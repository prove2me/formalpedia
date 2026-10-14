-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2572
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:06:19.166453+00:00
-- url     : https://prove2.me/submissions/18480648-178a-44f8-bc62-069ab27fd220

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 462410071 ≤ n < 462589928 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 462411321 1250 462410071 462410099
    0x1061101150f060e0d0807050c1e030c0907021905030a02070503030f04050409080d050406320a020d150305072c13060b03031201050a290c0111130f0f 66
    0x503000c004540301392807155144c90b24440700b40b0703401c04009030b1550312500d4070503911294600341c14020b44c000816064000210481c940c00d50400a015202201950040c0030f00050010310020841c4034411244e48200c00040340001d90314020230186545a1000c070000c0c0c6000c40d240c1c4610700036442008100340800400301a1001c5e01c40813900461600d0361401c007428180a03880707901070064034040521080101d168030840b5441c0010041d03012107032024201400f09051251038010f5804c60000054210540d68018402d401c5144000241c04400803003051003c0a5600112100c0e48114024460301980e00c009001d40c01c0c41d0344492000242141c03000025030740241028258000310500e8070100243c94000302220000502100e440391032861041102020a1240c14064490707480081a543c0200d03894200140901803003507030301140484941c10030303401841010469561030040d60203400a0600900080403070b003c1c002070365802e0810b0784e40c10300c1844e8421900c460400c01e00300009001c000c0d007 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 462412571 1250 462411321 462411329
    0x5070804051b030c132003060f0604120b0a060b0a03020d06090c090e060a050d06020d0f0e071202030a06020403081e0702010c2303031806060409030219150501061101150f 75
    0x810360b0b501442d40507003006400754000c0c500502000c1004641b8240360080594491502203580345542403048040c85440e12031405081041142e01c0c0c0b80c2c03004241040c2c0103d030020031858002826964070100b0a120b070300210700c400000394000400c0360b1103216a0241d5006444401010854410038940203811802180726409884601a00054483e44c0300a1070100420380a0001786c0f20304070b0303443c4c201c000f503007e20300c80f1100c0c515001114810f4600c81c855007550036448802082d0b0179040c041d14180b504900074003284d15204940c1558005600350001d44021803095110f640c0310540c14081514403000c0c09409140c05200b80584c001607a0f12942104c0360a801c42c040d8898602400303a1010003510013081d08010b4800001445850b0403005042003031b18410781c0c103540141c2c64500400c0180d8030106800b50041c1d02465105070490005100c0c008000d10540ca111a11074040d8007140c140c5000368403007c0401c030f85541c00d4000440038001c0d00c580ca201912300302070403401e020300c4010703401e82409 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 462413821 1250 462412571 462412579
    0x306040f05030910050a0f0306060806130207050a0305030129070809060d0603030e040b04050f0a020a02031c140702150c0a0c050601090c0e100e0d110405070804051b030c 75
    0x8244091241c24401c80303d209402030144d0311112011000640203500620503000091500c81c07221212078401e206800a50302181d86210581d240c100422140c08400c2c1e41950150f0360811a44000810410010024510170340300e45850758945105042c03035010144600c102460002c03181c0140d940e01c2021260402c0d80100080c0c2c586048902003022401180b00b290032444c50020044245908820b0034140a40206c5060040c902d0740014402507070030a4442d26502d100c00004100314088c190080e00f1034109a00c1100d0074061424031510320801d1807400e8021003991100041d9180d10540001c41d8001d40c9400140b0844454512010809400429243c280800841d5100c0c41e00c0c41500c400d100c903a00201281e203203507103a4000100504140c00c180b00420070075001482141803101404601285540b0707180d440810600500c2409118268112800013503411144803903600d074421940100036036a00c0300001e203818075260b40b034048003d8101100925201d5902c041d0703900001c41c885404003d82d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 462415071 1250 462413821 462413843
    0x708060a09061404140601050a0f1401020a170310060507030e0f130f021c0b0901030b0703020d0c02010b100206010807060c0f0c08030304050706080c070f11090c07020103060f05030604 81
    0x41000d000501040c480403030f10400d803006020038404202c501c07005800004042d1801a40e0f14002c00012081d2440344142c240b000400811454407030f01801d00d401c54041c01960911085542c0311200f204000e0b140306002070011003401941718603081d01201404207170410ba440c1c0501510040d00a513140c254030744c07140041c00c01c18511501c800210f04226180b1110501603030010f9642840650082d00c1c03552004e076880c0c800003005840c3da0007851652403010704201c403180d0070750700d40300d502d054024080402e054003044030080002c201d01c03805032a64030305da00010341c00c400704040002d003d0071100031a04541c0180018002c603030300410000d08031039060800038880c84003460031030140700078101e000d010445000030020f0a00310110055101c1c0b40300e402a5030076981c031120280e65a0001b61041d140caa5414442c103c0040c0715085164102802026000314185c1d000c0300160602104803154040444082164800c55800d4010407014104180340d8141e185d080c0404290355400040c0040c041c0000c40d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 462416321 1250 462415071 462415073
    0x2030103021804020f0301110918010302090106050a11070f230913020d02030d1112030709170c03011e18080a1b0606060203041502031e0d020c010f05040506090708060a09 75
    0x405c0e0288107140d0041e000380b2101012000441040d000b142545001d081182050700304008a101064180ea03401000103100fa400d0010032186500041036010a2082d20f907207400900d4070404ca490014401c0c2d071941400136051290a610401d0810210b00020610f0040c0b03504640d180345005274081d2400ea414241541240000341c0c3c1d107102c014000e500342c0200340307450302030b1540030b1003498008001204480c803022076150503e44034030085440c8000520310031024000529404941082c0002c00e0080b41c0204042e000041d08448401e19000b208a02d030707001c204e00e031611501490400b88664003c2c6003000251392100020b40c4517050007a000c0010306c4d421504d590f10224820303006241c010400b04445a00d0b6070380a07549034064064030180c01244401c203508240300008450200e211940041d80144407800b03103201c640c1185940c03042140d024081001000c4e000d100d1110011003643c40402e2a08150a006042110145c80500140c11010042c40013500000c2c3e47c2d40c00c241c1e0f1542c0080e1034011 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 462417571 1250 462416321 462416329
    0x503090c010e0a0308040b030f0108160603180602030f1b07150b010c08030a050a051302030a020d0311030c0307021201231506160204050f090706030f06092903010203010302180402 79
    0x650b0001400039a001c18040b46400c43d80d00610300c03801498040d08030300d9803542f15a40e5a8105280180b691044098041c40194421b03006024031070400a030212034803050795140e800780c1c0c20884890004910f0002044110007555461400580b0345d150654034022103a207800d0903004850055041c0151180640c0781d03507912521904090701d400110035910790505142900c094401038074080180d90070400031070828085940c40300c0d44c856004000b05424840c1c3d13428482204200d5805400b405030319810759002607810700080c01045c81880143d55201041c0c410080c41c0d5401c0e040c000030341d80c0f40500201041c1c200c034038003580c0400c0c0e13000c00b607555a44184122440e103c407072190507048080400c3c10f10031401044c8000c44401c4c4200c5040c4519030300d1a0302c000312404100c030060310541c85200c4c00c00c01a4001e81c45808030b103507110b6020506030345500d04001990b4482c1c0d420b80d10801c455280b02810910400820300200040703009510b59451600050a5540c000854650000300380c4007050856039 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 462418821 1250 462417571 462417589
    0xf0302130b0c060f060a050d1103010b062b06030506010e090f03070804050414042406050a08060402120613061119080a060e04021003180816030e010503090c010e 71
    0x4051841d10382d92802d009039181c031200191516401c00c0700ea0800301e9040d2038501c1b4005c09407100234101291091150701c806016800c03150b52a40c040d503844190030026103c00005000f07801d080218000344241802064035040e02461401105500e401c0044c0000b0f00080303059811550304203206296516403002d02420000c110070103802030f100000e210010444620080c20480704203d6041241541c42e020380d08490070300311002080c00380f00301b94201054103401c18840030004840c13400510242c6400120384c05c2511500801d1860b40726004100451404c03c003c1034001c195a00a0042d41c200074500d001d89074810900106115103620285220050034015034130007030751007000d054101072482000740a6601c182d982c0c00981c0c0c10300301c0110300c070000108110b000740d5010b459082d4000075600102d0040a55031000700e08541140104000700384114041c0c8403000244140750008d00285c60301400c1050700c0218281848001d2081120408011031243c404000030b00b0826261a170760300001c3d41c2e0803 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 462420071 1250 462418821 462418829
    0x807080a050c2b0312050106020d0c03030c0905060301120611040806040201050703052101081902010e09041e0803093f0c010f06030204050604151707170c030d09060f030213 76
    0x31000c030b010502130503800200c40000422074142040266200e200807620f810f41900309001046c82540b03030b0400288260300c8801380900524150145540702c100140e6198004c4c4c0c4201e4046901000400600c5007510443e00c0e141b10020781c5910700752130b10426a031102002000607040c4403000c42c4000601d802a4120313900000710182010302c000340d112420003000b00138025080d241c0b19061783c0d182c0c0010085600c010640d016150301000825541c104008000010310488010f090301d403d11550751030904031b000c801445000c4181e240e14013052158501309444c0803140140095041310001301c1403003404201e00c00a10181c0b0032042001404001c941d11682000010942c640152005503090a03032100040d81d2003100c0c284250340340c6104000036103850304140110911158400c0201840304683d40c11100410400e0351000c603683e07014000140001c14005402d608403d1503c0b07981d16007800303041026040e50411440080c10084001c0010b8100412081815800035110803080c010110060080c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 462421321 1250 462420071 462420139
    0x140a0812030a02120103120e10140f07020d05030307030b03060402060301060516051e010e030307020601060c03090305031305032109010e010c0506070915080601140a0309020a0e010807080a050c 85
    0x196524600550b00d170103820800800540340301d0414115240445500d15403240395503c600c10040102d5808099070b101c10490300040bc410000c402c01a105e8907100b850180c080c00155441b441c00b000041c0c240e48040d51103500c0398100404020042c2d80e4501070328155103480c501140c8854550001200c070658886014002d032060360b0121a0a060038100710005030400b00007400120280e560241c1d4900050f074440c40941c0000d030060102c60304c24042c0288075402880d280741240d0b0349031102c60640e446061079122200c07a20303000703201905042140b90406d0024032059a195a0000c0b070742c2d075050203050381f80c504000000035501081da10800808444603080815200c0d1800c0c0104090301424442c820b5845852003040c8032246180035000642c031484040e1100d282e864412603060343c0c3c175802881080141a507070341c0320b0070140c2c9420000300080c1c05140840006941006262031510440c1c0e84421100e5100301c1c11040094004140c10320342c01c1d8188e8070380c91550801106c43c017000c40075407101101 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 462422571 1250 462421321 462421357
    0x303140d0905010606030c03090b0103030e0d120c21200f030313020406061103040e0c0c0607020c091b1803010b13050403030b0d0b240307090204140a0812030a02 71
    0x2e01c034041d481030048034490b1314108100341c113860050701600c42140c40601000c0383c4100401c046805800380c0d50031342c000146025100700480d680e40b00c0f00c102e07d44966002071030140e10081041142c91403c4840c2180600b13000d640041804000c0c07003080b122002030185030300364801c4146010100406080700e0092010380e6201c0c41d000219410020300c55900b688100d00f084000100d05001d901c49410190780300f00554509810014150602180a040000000c40400c00c400414101307100082c0184541d502401c0b0040c01001002030a40b0f020b03049001c0d130980003840d108a207200c20201e4488038040f040e405040c1c4d0b04800000d0041c805031488a40001940e00d002e565004603901043c07265220352405c110720500102408010041d244008010300424000702d0030002002d0880d400c0650380040122240a110b40442e06100d2a90304c4100d40a40100e42030010a00701006200301d150305541c1c10302e0142ca4848441d90f5402c0c00c0d005000c84080000202c0c0b420b0005804555159244c1004862 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 462423821 1250 462422571 462422573
    0x22d0c070303120f020903060406021c060e0708071b060b0f040203040c0f082d0c0a09090c0936020a0b1b010c0801051e090903040510020708070303140d09 68
    0xf1040b4400b0502e5091545044079200c5400c4c4584240d030200c01c4054010551075030b55607070b0300b4000c2d4400580040d03284100c000c20001c910305c50080038081d007020b22081a0606011300003074484c000c040d14100a0082001c0c0ca40e800024510719501c0054101a01203103882c00b99010664407402c210949400500010070802808428120303942142c0e1540c0318413039000c1d900c81807181c0303800c00310309640084412032843e440e90140c07882829101500c0030303040d15240d00c8400700061644000394043d000301c1c1d88848840044c04449101e10008104140c014820400118040204c1c0c51000d002c21040c0b0300c824119001c421065000c040d901a40074288169540c0c07130321002645074111481903070002800005000c51038506000310641d4141e191a0301e92107900301400c0200c40e180340d00c004401c5a288a118040383c0c3c3c3e582401600400610b8003450703944e400d10003480340c040f035800341803401d540c01103a00700103040d030008040003100d030103160035540c00105240c075074114410825401700c41410010000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 462425071 1250 462423821 462423827
    0x81609090e07031403040b0d0e0c0a080f10110910020f10060e0c1812030d050c040305010c26060103020705010c020606010206150916050705160612022d0c070303 71
    0x300c152401022488119804d840704a6500d10036030042440316001031120040251164122a01c0c2081c540151859801001c01141200c00d45510140075a44417400c0000c680c14140801d00341204003600030311005400e01744035032480c414000c01c80e010b40c41c45032000400700e109200e60300c40041040c064074007a08894800d44c01410041c00740c441089440f00100c4c9460907034038121b4410f800541c041c0012404404104481020b08248114845c0002c020a60111260344940d0b40700d061420f003140d8031a42541009421907008030003200510140136400307440d035650040d0010b11b140070b500b04001540d840d503004030003034004d1032401041c1d50b0811107074018154012410070304c110000e0b80ac580e0300c1d0b40c0c0c20701c09900701c0da02c80203200d4000708a4800324041920b441003c03900030400d810801d00d4400039641e99498610740001d12104041104414404107a00a030314200000d8010700540c01d1001c90301c010790f031742c0005114140841480c0107480f59002e0b00d007015102415160704c161804550f40342405 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 462426321 1250 462425071 462425083
    0x3180f1801030f03080c030906060111030412140d0314040b0601022b0809010606140d020708160611030f060d1a10090501080a050307080d0f0204090e0607030606081609090e 76
    0x224041944000003034100c040c0703801520310408c00c0000a264540b6044015210b150104414016500041001041482e020f416000c020703803055210b00781000306c402e0040d00b08080039410004240c03d007140d400c00c43c490f0800403908183c01c8250041030752507100c01030380780a601c048403100a4001042206c18440418104143c10074107460f501803e980e150301a030300b221014003460000c9107103041445400d905910107401e50300352200f0018904002a294140c00d038002c80c0981c144590641550400c00516016440d000440c5140950a5051100000b0760b2054004c04840c020703c5c2400d4204140402d003020300c54412041c2e6004110384c104021607882420141c02014001401d1800004280c0400122a0301c0c103508940603508003c115900c610140e4400180210340760b884004032000b14041d0f10040c0300800c185000000c089000b000d0a50520000820100501d031078144100f10254000801907807100ca9590b03801d448800b131403000d13120300000b0b8120b190303d945010394040d1a04400201d07 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 462427571 1250 462426321 462426323
    0x501061115090d0f031e060305070b030f040f0303090b0f01060e0a03080d020307111b0906010c02241c0b0f0d12030b060702100207030c050303180f1801030f 69
    0x54820305005000840180741d030a98004400c0e60000901484840c480c43c41c030f8025214038074000c00d5a107901c00008601d400d501201003240317a51207500300100202008240300800702440211301703500d01300c2c041c400303001401031000d081248034883c441d007094866440640025403020a8a150741018802400f80c058240605c0c0c010031469034155401b440d1005655084941c82080c5604d49142800c0f40b4000e0340016041c40e0500410048005048105002c00800403114040f0781c86c45030b5441d800c00041e00c80241002d814072030928001000b588031040d00c0c1640404041c040e0080e01d2030801c64500b60310511144240c01d81c6010540c520700d40258110806000084403401c001c45404000c000311105c0c0340350020025540350048190860094020305c06842008000ea41000595000305082e102c510200c4001030308907603001e104001c03058075000081c1406070003c0d4101100c4040302d4008604822000d803040212803c2d10050f55504004c00c1441060207441010b6565a46010340e03405082e804 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 462428821 1250 462427571 462427573
    0xc030926071d0411120a210e060d0903120603080c01050c0c060f1302130c0305180a03030f0f1409010c0215040f022e120902030d050d0f05010611 64
    0x20000840000a411146101035110240646503c0f0b40d41c1d0405907240c400f54a940142d5003852502010b0345c28001e44042a0041d51640715002403803c406002d40c42000c4a1030034401c044010f4001e035103441090720101030f07036024000b8010b049414250b440310f604000355000c440c03c0000c04000c0040f0702c0043c0c001614600003c2c0107545844c10341d6009402001008810340d404200010f804070808549103802060850000507505d00c26000703d80c041d0300070000d88440070b03281d0b071001c01c04030351510425502000c03103040405404a504401512804200300150406407540c0b400b208039800c55005607440d0801880c00c02001080c100b00d225001d40850703071141c60754a456900042c007400070030812282602c80c4500c002c555510b6481040055441c1c0c81660401c0e200801d0445481000c0c42c2c25104140c8540818019010040000d2140d459429200e04103170802909400585000401e88040300003814010348448508105030020800d842580d8210b83c1000700000c1c215030801d4030302d03031000f143e10 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 462430071 1250 462428821 462428833
    0xc020106090203010311061c15050915060d1e0c0207060206010b070b0c0322060b0316080c12030c07092003060f04050c0c01050c0307090807150c030926 67
    0x1e45040202d00003440b010b0300200740d080800a0301e252581c001e00d02d1014600740c10202501c0e030394404045400a084406a01c0d040703480034015450319031a0300e5881040d01400076414001000422003a006119032011443e40300d9200e14600b07034881d00d81261050b084031003000f400500d448000e40d140410f06c81c520141c040c5000114440200c002115032940d000903102d1545c0e1a0342e0550b141941c001407a07c02038a500380781039582c003001280409042800f030440460000600400c1504101991950800c4189001c0003003080000104582c43c0c8420103e0300b48015a5035012000e0452207044035030071540c001d048000c00c503d4480e03449004104000380100505062000c9920140d210560308980d01400300c5042250030729140d00104c8d4440c0c0250403060401300148501825280141c8104425000220801800c80d90001c6001c0c0101803280c02460b040385011088410b0401440d0035104002c014035009080c180501003110003840d0641c40b880b1800c0c010715960351002c8980c5200103250241d8 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 462431321 1250 462430071 462430079
    0x1403090a030807050c0c010f030908030901090201110c1e0111101a011412060a050a031a0f01063c1d100f03050a090209090d030605090c03061011100c020106 69
    0x40d40964080385e124200a2003600140c40054a01d80a180030240030992607054090018190f100a54044d804100021940ea1010b1002401c43d10340d8651075071865129512440180ea2120703540c000302c0581e000c060411110001c0102c03a443c134034260004151041a00c1c07001700c1c88a540c000c0d01e03541d50b8809011200c0140c40011078140882d02c85802d5044820300403022403034284251250400c40041110210f82d0351303500850000095039205032000540036a030014481c400002056116001100c125010343c18144054120030302d0b01050300c0320788031110040464000750010204a1030040f60031261801034945d00500c0c0c08900300c6280780d000c4100888480c2030400400d220045116600e1f40180c454449604400805000b8814002c0a894904550158070327000003440c0100c4400000d00460496000090103070383c1c076984224007406544082060590409090320740040040700c08011100b0081400c07110440145594030580c001c4444204440c22281d0042589400a80090050300e41d1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 462432571 1250 462431321 462431327
    0xc0e0106080f01030b071e0c0201120509060c0d111306120c0210090804090908130b040b07170d0e030a030609060e07050702010207090c170108030a0e101403090a030807 74
    0x4141c4100c140602c0410040c00040d0503000500e52007800c0340b80000c000f00f20440480c0207200004040d501042000b0078020555034421050442400300840c10300041c14500d00c915a2044024091070b45884003080402c0000c5494100c41d039820800e540854031000038541d506031a441d541320700b8011031034103811904051032030f000e1014045060b070084c1404000392200c0e08080d056154044550704020400440d481d050703445006c02182c0904441516240141035084ca4110160807000001a090004020408801003103c2180d5401489070480700e6603400d5801450213a01403c070202801e04903a08a030703250010141c406001c4a5506000b1903541e8065002168124002c00c4030082001c80010001809840181209031044c4100c8010381d030380e8043c000440d4041d20074040058003d03038845025688001d001c0b80901198006540b52802d420006404900c0c1003400d24080c0c540c1d40b00d240c01c001d010b142c0180114030012101071703813031078000941c13615144425412070104010b8000b103424184 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 462433821 1250 462432571 462432587
    0x901030501090b241308100c0203131e0e04050604020306240f0d1b1e050907032007050f060106080c03010605030a02090607060b15090d0204050a060509040c0e0106 72
    0x150207800000c8035044180c0011900c0048032020040407805c011280258201c03402d51402010007402a00801410750303210016600707a420010110340c0141b06948590f9582d1884208907441c440c0303040c01e040707081c01d15401300480039404541482c3c0341d1410001400070200e0805e124034230031020382c1c032940c0e03c2c2c4107d01486d40c4405201c2c108841a40c0e240e43c40c0c0e09061400a00f41c400080100250051580e240000c0c458003d2000070018001d482c06c0050031034551105070070080c0304200d01c84031814030b000305042030750007007510b01003584030700820310f091030040006449242d4030764031f40d50b498034a418115910010107056503150b20070340c40001007892182488500400c80141e0440c41c1d0f03441c080c011140ca402c09030100d9461030b0301f0401e9810329590400200705043c0b150001141c443c2c9141c00304083d124002a0406006c0c8041050780010b0b542c40900203a00c90f41150005101c2d256414144020002034000300c0c3c2010300c0d4801e0105001d0040d004404071078900c40b803400c0907070300e414085400c0301c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 462435071 1250 462433821 462433841
    0x72d140f1614040b0f03010504140f0102070b0a020306150a20011407120b100e0301141012030e0a0e010e010f030503070209041a0f15271902030a02090103050109 71
    0x2924040308600d146015041903076049801005d480c1740d00303c420002402c5400a90f000c45080b81034004605041600748040d01002030302000841c03c0103108c0e01c6401e035040c4000d081d1040c50b036001001900079901c0803101d1000103104505a512003406a0001d00148030086490000d03003000a041003030030905002d0603000b44400d240c110420385a6500c291418026100c0c080603072600e51200b01c00640390740c2c4084a40c01d105507922007501c4280c1040c542111003400302842181c41d6002006044c0070880c400740110743e102e042d803540d40300032801c0403101c1000c0b1304030281d40951054070000d28042ca60b81d000781a42d4902d100c000099a136503d01d01c0a030a19848000c005030014445070001d4075000030103a51050050b0108106503681110f0780100c0c0104461aa420100380f6042c00700c5080110309481c0b50700c42c207442c070700c1d1005107208401013003401070300701001c804004000043c506207501d01011101a440402952203051a29000c000b0750461034210740041d00d41800003070154410b0207115403130 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 462436321 1250 462435071 462435089
    0x6191a0607020f060f0712110d02060408090102071a0306010e09130803041502030a1d070609150203090a0b0702130b0108041506050d0f060c0203072d140f16 69
    0x6810b60030b001c00c01e001640090392000c0107004010140c0f413068000d202e81849601021606140c002c0040c159542c114104440c070384c000142060303901c1d000030b07045401c030380c100c402e050700c0e43c4410340102e00c1e00b4440e8018080310000f03c1c40d80c0420300c0e128009140558400d803a03140309845940140104c9010403180d5800540c10b1140700c10102d403c1c03030011078003e401412a5103121003081071510aa138000e07541060195038810503081500d04204001d003d94007072402804245240400092072400c0ca80600c1808580c070010740c00155008200311030380d01c0d001038420b07003025650b041c2036441508960b1701030340211143c0c0c0469603002c49521485c7c080d020140c4904d0140c0d195610b40a030075a01d034450556810b6a03c0402240c250f0b142d409400c00188101c0c07449400c102945000819129239000040c1558024820f01c0001440113091103c00c40c04c010544d800c3ca680401c00d11a041c9285d100501864041e002040c171410020034104003240074841100e20f165046003003000c2d414036500c203400c6a = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 462437571 1250 462436321 462436327
    0xf04142e0b0703021018020405010510090b16020409050609010c02061003060b121e01140103030203091216030b01090e07080c06090a0b0309060621031602030a0506191a06 75
    0x8002a002401d40079000707204907000c440e85d407a440c1040750141c8607894002c1300c0c050011300440c50280100c0e07024180a03524001d00c40f040410107000c15415020b06524180c1c003140c8104400c040c0c0502c1155140c00400a12410a050401c143c444c01d065450790500e500740801031400c1d6000140190081005501045402e071940d22100002c100c094140c55105802406440c500c80c1c0821040040c40425810700e4504051500d00c2400c481503a40c494225020310300040000ca03402100b40da8186038207803540c4a40c0070700e21301075505104c885032600b080c2c1ca0644c207011060081000c20035040c0c5480a104000c4a000208915521411f5101d070103181e40c4101c03080c0c0c007a4240312014040c503c4000d13007241500d503210b074200e00781908115106640c1d030f030045040001d5441c00c03200c001130301c81203564400380e004c101c60340c00c5843e40b0600e40a071101e1181d000c450340071914100000d040c855005820340e01c1d64144800801180307500800b0070904281001c09030300c424840b000003048074910042c104da00e = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 462438821 1250 462437571 462437579
    0x20615060a0c050607090807050a0320060d05040501021c1523030111090103060501090609030b2502010b010305060f0612060105070c09091208160e0f04142e 69
    0x40d4441c00c01c075402c10681604000000e0400c1240134020942034480403055401c00d5195840c0c00c05960019204500040080021035a03100b070604800c1c05010070540f00e0310101c0045601d0348520703101c030f080071890081080b0500c0300c19800b402120704200398018035001e4160100c0140c5240c800356281058403401d08005014002521321403c1d003104d40040c0800c126900000c0c01c69183c8090350701043d000203550021980d0603c0f510018050034201045010b042500060083d80f01d400001e10840001011811030740083e00144002d00804024566010390954000c0c00313800e0700083c003800300e41010301003217444c036001c542041d0254001c0c0042e8108800414009030741d002c094205414404204101c030040b0b425524000c0c064010b400b0b022961071503e140810f95144148249000c0012003010b2040006290030f2005203200c252070b00b000040c1000380095480014007100942c0180780c00c105116040b401341d004c6216500f91400d21000024051000c40c1c07805581000440c26500321324180 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 462440071 1250 462438821 462438829
    0x906090106081302010e10090312080106020307061806020417010e072d05090c27060f0d0f0f09020315070f0c050c06040b031801090206030703021b0109061b020615 72
    0x50f040d00500d012a000c6094802191101071000d807454001107004400340240000803070040707001e01c0146400c00d43c41d854014000d45a000d4000f0060103191a914500002d6400410701c02040d45c0204007151b540d41d541c0101c000100341c2140c00c8400e5420040004455a40030401c03004444494482e2076011480c84242c080d42541e0000e003900b84d088200000c20140c0740c14010718801c0c292100010780d190181d014802c07080880000e420845074011450351b4480d00c2d4681550146051440c031310f074950071941c4c007074030190441025508074181760005c614078144082d005001018005d50a44a08038080441c800c00610f0444a0b2008a10025403a64500740b0030320304e200310315000320152030441e140b280020b40c5950280d80a104c2c248008001e1248a0080698114100b000781e4000c0004201640c0032688500008088000f4160f01042410310303007068000c0c000340c071701c4010003c11044215145c04801040c0f90101c1007200c9001e00e0142024500010384240109074024100c001075170303590100 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 462441321 1250 462440071 462440101
    0x304020f010c05030a4d1c05070303020d15090e030f031302121207020a05030d021e0c0310091106040e0c16060c0f0e0105070b0f06011b11090609010608 67
    0x1101c200c0c11210b00c5403001d695044143c0c56a01000b1650f400d0001d44400302c1b144c0e01007000c00505035000280b0520941d0910801c040c1e40520906100303841354070070306054000303018140340034402a00701840300c074069226414a600303540c52124100140345c000c0d07800650740e000302c1070401150030081001c035038241503c0d81d0710040988014071600e02c00c0f5401c45000d041c065211014802c0e1040400c0380411450500110b0026001c1034004158460301d040009668045651560100d02c014040048000304180f180d403000703401c064200d401002440b00f038013000b070a1001c01614180b800d140039102c0d0307103400000c582c01c41e418840e4128050f21801031208140c0e00200d40600c000314461b40913000141c0a0040224002c0c6079124601c8a10910304003800700100000f0050400c80c0c200403c000084000000d40d4002010040e0043c99943d414010780340340d030400c21096101020580841e08118034a50903440701117096910054948801c818492506001c2c0520000f00f40c030301c000242845030b98070203 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 462442571 1250 462441321 462441347
    0xc0203060a020f16021c0809040f0506010f0c0302120a08011a030103050706080901180f0303110c1506030703023106060f05090f060a1106060d0f02010c050709020a03020304020f010c05030a 83
    0x5031b20450030407103404101710f120042044444407008924980e040c50203201c0c3e0303006140344100601c40c0340341840000f032201641c00f01c08000c1c802079001c880305140c420030260201606050940b0340e10450124080c003444001d12030508003481c548802c0645071790007000d5034100c9600c000101511070810384169420007008081c2501e179903031000c50101d103205102c800803070701c1e009180d1200b1104d0281001010344940044c000b011030002c2020b4495220700045802040c034960442039520340301c201c0041d0030810780341c1c0041d612a107090f0800e01282800c10514500810143e01c0c1501d0071481200d030020741c0e902e03100e88000b1900c2c00d140c0094545c01580101038003a07000b0705c6080c21840383c0c40020040c0c0c002c00380e09000203880c440035415040b4200300031500584100c6416a44003a29910080c00500142c0b00074100324090301c86c83c04210702002100c01620b01050300795207940070420000e00070340040308d0582c425110840c500c070065000da5041419035401102079450858040301c00d4581c11a03600f2 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 462443821 1250 462442571 462442579
    0xa03091e02090f0c1312021c082d21070806011707030e16091404020a0311030a0501022b0e120f1e030a0615050a1b0f030c0203060a020f1602 62
    0xf02c031178401804200010007500d0400d0043c2901c10050050001001801c15601e8510310b280c00300c5c0010650800554400761100f1035400382d5844440307a5050300302c100c0c1007620700349040030401c128191058200159001d05030104c4c0382584d962403a044030766041c02e84031135000c01c880c808a030810400780ba01141c0e100300d05c0d0401045071807080f8070192514083c044041c200080c100c106010052141c05044842244826a1217090420f5000505110f5403840001d05403901007007200c5840d1070521001c4c6140d90000000c6480300741585840000341c000114100d68214a81c03403c45501c8014451440b10041410040c9160404c40441a1866000036200c041c0e25805115a80040558200d03070400707000540700403501c03401e241d80c0c0d142c01e442c03031608010b408480201e06403800c01c0d400029120522003519004050124034551090b40702c50007480600156200354a0307005042d00500c104c1030f61442a800c840841d1f0f10240d0000480c0a0381c007580c034085000b0403030840c801c0225810700c002a40010 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 462445071 1250 462443821 462443827
    0x30f04020f090403030905010c05040612150f080105160f0c110310020c030c100603121206031e0b061c140f010c121104030f020103020319020a03091e02090f0c 70
    0x1000107a181c2d08220b030110300194851a00fa82002020300840e5500c000c0341c03e00300d04040c01c101d8050004190440102011540c070200c01200c20f13480303d40300f0000c2000c0960b1801054031170150074082e0100300c0b00816505040366401c00d00d01d11130201f07e80031254540c4e420148041650f120701ca658a01c2c00300d65070512030410041c9041c0850720040080004070001148d03110380d5021601d060000b81c14404075180d11b0036004201080f220489a00303684000d14000580305140c444800040115810280c2240c140c3c001c0c003800c4082c26040c007081240542103201042d40c0e054100171104840314035074441c0501c204000800115034805040d0690a164196414000b25607221130071102c030b89480c03d0009004992070343c0c6552240c881d10300b211001ca05201c0c40d10b0b0540d2614020886141ca0090401d9030000029180125400d143c110411f01114150740c1c03844500310042c061302220301c0c147c400007401235140082c83c2d40001005003807a4098030f20540c590700e011142c5d48404005215030064a010 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 462446321 1250 462445071 462445099
    0x402061603170702030405120601120311010204410f01030b040207020418140105010308090d1110030510050303120138130918110402091801051002060c030f0402 71
    0x8005100d10806151380110f0310b485c60802000314000215108100c9a0032580044c0405070001da9050312098150a14021078600c8008441c0244070760740c4040365503200c180d02c0640899000000d80c6d0481c0340060000890381d808503c2e6014092042042039004045444500565000b50403110406100030b1006080c2441500031406a90381802d101030a58005142882081044c4000d1103009080e81c00822040d030442e56640c0d42032107680e071b078288108554100142000001400b0b940c00700d401a000c42908048208082d02410090b43c0c500041c2c2c808040200303950600000355040001e0303420a0b0040d03a440c000c10618102440715a920b2036514800100080f040190142c040c1144035184155a4030741401042843d500182c106644050611050b213125030696168100c0c00c1d600701900700300402c0140d000400910803107a03403941000f040e00424080e0010341d10300d04e0480b4030655441c0c581d0714598004036201d402c101c80191400b48280041009104501003056105101400c0705007600b0403 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 462447571 1250 462446321 462446357
    0xe04020d020d02030406061a030604051003060e06010630090f0c030b06130b0f01080c043501020403081b1e0c10020c1c0c0b0307120b01080402061603 66
    0x4100244402c040e000024001085018031460300281090022031100e00215101c0404a1101400c00d501c01c50725100802c40405141040c88000c2d9444003040003142d000b50303151a00c5510074411000441d100741d04d0741200011801810421080400008640114000d020001068003400c2617900d81d03030340b43c42d40001965060404010394040c030090803881c50900100070b00440002040072030541055410940e50300c45800ca021201400d09000c552907980c0c0c44142c000e800b85911400d0b00c5250707002c0c01089500d00c001c50440b811840f4200c000c684500381c550038203078400d0780300080140da000c002c80a20451010388880c00d0400b07080540d504624040140c101c0d10003081c0150310302d40c02184505015141030540e14a654406001504031005140000b03800282140002032203200c103050303041e0811403460b516030090140201e0940d141c1c00c0008001f07203022240004408054039003d000c1c0d00960140303d899100c0c59005180f1071400f83e02c0414500a100d07140c40803030900c10f21284281ca40d100e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 462448821 1250 462447571 462447577
    0x509030906072f10050d141008120a020706050d1401030c0e090c0f0d030e03070f0608010b04050a0302060906090a090203092e0b181905090f0a030e04020d02 69
    0x1008030703102d80c40c3d0350702c00b9840e0260640c0d244a103044000940c0002816484520040d2504840360421948a946244140001e4034030300000c40410801181000b00c1c04502001d202c0559102a040f5210171400c0d80300410648510703070110000d80d100003010883c86100780000d1281c0c0c040c0102c08601d10740f83c4000c203015154280c008446002d0104000d0000c010841d0f16654450031180090240d2006100480d926001781900c65000d1031b00b0201c0c2c1001d160168080d0721003d0030140071500191b0f03a940d907400110480e40680760014641d00d0000404d00100c2058a06440004208252161541d401c10486512003607030709400040511800645956600945004000c02840540c1d245800c404a50400b10300f01400d184a020009440013a042141189440104440d40001d158915100022500e010030841d824518000d00104440d41600269036000f0088500701805951240f0900a845a039554007940f581c0e8400700c0704001007842000e17150315116004d0001490b00061100c10b40690b4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 462450071 1250 462448821 462448823
    0x311030a0906121e0507050c1507260c0d09060f091b06080c0702041b02010f0c111515030d0c2a140303093303060a09050903090607 58
    0x4820800400c8500d403c218000c0301409005000c100108840302c080e156200c9103505200c800d0f5550740010315240c081c2c0c007159096240340d004c0b90901241d01c06280c001490440314540019480802d17a0741c014100300100c0716601510b040700b00356695490041203103801818940c65031030340b10b41100001c02d00c00d1040450024981d01c2c00300d4030301e2050901c54548860601e850752512048102001050390050040b034110348008036003a41c400e901c0c000100501700c083d2460701e50b004141102100d041d0150300c21a40300228440500c50100070050030782d040015981c03140c5c455003020782003c038000b114800840d80151940d0401c0341d01100c0e0030100b4540b0a604000c0c2012030030945140c1c0c184107241038550307120f074130000c07848003508070b030303658440c6102c0d041e1017040c1600e4406581c50035a50750174429240c0007800a051503806d81d0001d540d000c1c14500f038592400013042c217082007800307091441c4100c0c0c2c4101409004840302c90300c0c2c0400d0100901c002840390100e0b00003032006c00720390b81c1c4200082401c9 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 462451321 1250 462450071 462450077
    0x207021c03030c02060c0a091e0302150403170901090509060a0f080d020624010c0507031703010e0601080103051e0114040606080709020702030c010e010c06141506090a030f0311030a 80
    0xf00d05420103881c0020140c4103007080300c4140400781e02030b640010a2000c0d01d60301c09282e024800007100000e0020503581000750320503113551b100a03404c40580c0c041d01c21030340100d03524010324689400070380c082c0c411401c08030700245e40d10703400340b01d6403c00d10f03141e940020014011000140e5208030101130300c0259041032105811004121011550401c0a250040d40c40e0007000110a10707020494120b075581c0c10841e05005100303020405021041c480c030700095400c510030700c614800c06080c7d1016a4402d004100d5114001400b18606500c20902c2c0d5040c1c950100c014110144410705c0070041c1040904500129074989400b0346250881034038041c001d80c840e110110b005800c00a4807810f00829420950170300d403040c406500507070303000100f01090300030a00300241000041c0c40101d4a1000b5004003824803400c180140890481d020b451034400c14032140861560700c255800c03c400c0b072141900c880e900c8106010248085240c201c12807a606102c0e017052a12204c45413889803c61b044100c0701008 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 462452571 1250 462451321 462451331
    0x41a1504051005040815130507080604021c03020c04020d060b0f090f0d0f060f0f0518010b030a02150a020f19020316030803070e01030623040b0d0c03060207021c0303 73
    0x550b080c03070080c8a80302c04003420720b241003906200000360360719150b14510380401c01078804908030900001c031801c00981c0007415201c206884800c882c1e5604002e90342203000740d00e80002d2001d0600b00b10106a00c2a60540c090819071500400f000040d4200501c0001b01958032480041c080742e0781401000542c5618802503101d4108108100103060031041c0c0714000c070441c1d603440e4001040001a8001540d1181e000540126a081c1400040161910f49085545410103000d0030903603c5803001c88608040700248800c80740841030540760541654001d411921501035850b41542c480c024014a400300e1044400e01e283c1c03580c6091030080c9142c522040301e0070360604581541010301c074540e52040801c9544440d00e14559604c0325612006112500b08440c0818000d030316032003608128010400b40c136065400f5424800344a412940103040b051181d031428011030307030b07606044070b8552003960401c200800040c40d40d254207029521a90040341e00c5140d05040c0f4143c140040d0580500d20301030b0343c1c00a0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 462453821 1250 462452571 462452579
    0xf040606021608010504051011120106020c1002030f09013203011a040b070803072709051609050111030418020301061d090115020f1005070923041a1504 67
    0x240070790b40c5402100782641004200008114002080b501c82c40714040300050070003c40180010300d005000e41e2a4500c03420500004845900048000c0c145008440340e00c2d003445100300c141c0e624818188815403056050011000c4da600801c0a20003004421982e2481c0c24460034503440000e004460f00c080c00380c0301000521001495a8124049107103024180740f03003a0809200c1b802c5409442d02c003d110302000400221414419140051906508021041c48820a050101381d01c0624020420094900300019500c401d1200001d81c8460349074a8a403211401c0c1001103401807095144050203200070040011420755110070851113047c54400140c91b94100080149000c600036211803450900c085202c5040e51050802030440d141044031200c504010f5030164201401c0c003080d22072074080d541c20b4554114994010394898031496407240394960b1201c5004007180f1291041411810407050b00182900340b03980100c040155010540b101c1103c08000540c0984050103201100741c00494204 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 462455071 1250 462453821 462453853
    0x18012007120507030203090d08070507230a15080405030f0a05070b01091e0b0d060207080702180415050c0f0a0c11011b02060304031701060f0810230f04060602 70
    0x30700700501c41d00e000c40c90084142c5000b5600d019034500b151140031520f06142c2041120401c9420301980007040e2070300c2a680b00441c04064414462800f0651034500d1501c40d14640b203c04201603415513401aa9030a914010440340300344014001c640b6844104444248242500042d205040342e59903025916003813440d04900045060b842101450304080d00120501904100004054501c03000020900c2100e40001c08201500401030101840004d82e94240704c2c81c0001081081e009032441044030bc118000034030b030300c1801c650280c0108101c010300d4444a10981016403c4100711006130708011031040c03403400c50703480f0b00c000ea00072403c6a1a03035400c01691482030b150404090a0440c5c50000221f100701500044c07240003403040400000184c01c02d0302464002c3c900010344020310000d90b0310344102a081a00240c82d06000c1010b03000050701c07900ea42000302d400e54240844012070000301a0000c010b5101031620780340e00000300400040103880d01c1c41002d0083c1460342c020645590542881 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 462456321 1250 462455071 462455093
    0xb04050607030c0e060702040e010b0607030e040606020712060b0d0c06200c0105040e0408040e130c0504110a0c030e040c02010209040506030f0703080d0e0102120702011404030818012007 82
    0x300140f03c000615007406564941c1076035813454040d6008103804034003112083c01400c0314207401d0780c023340105d03198080c15844100da15518409840400641780c94503010f90740d824052003003408141c02d0041201c00a14690400002c8034409095090f1043e07540e07862100b0b41a264001d600040c50464400140b0711692803c0c084061103c0003400b6004085400280701b88202d000b400b030340f0790142012400f04413030042120001c01c240304500344031703040902c041c104106032202e0646d1301c88141e10001c24070386054803030000c0c0c0300e51401882b4a000d1143d00c0075112054501d406a00780544044941e89a89035402a012510195400180d0f11103010042004640380030b000b55019610904565162031000288070007620342100c625600ca0b84075032020f0000e819003003e01c0701c2d81d5002041c12002c44224001d454020070a03a0000d01950032841320b2030641640c1200e0240c00140304c1b00c00304000050110080446945280011070003219491040176080146844103c40d10000070303140060000b40603038 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 462457571 1250 462456321 462456341
    0x90310060305120c070504091a0a1503060519090501051602030c0d14040f03031d1f0f1b0f03090509250c0213050a110702010203071106070b0405060703 67
    0x200200c0d03046071180380c1c3c2c0e04030015a0a0101c2400500d41e410b00710100007940040100500600c0166000e252121095600030181036114074000302055105025002d2086540120788004c810f10b0701c0d58841d0702c081d05010b03142c4100c1480e5890a680d0030710b01400340e0010340d400707500041840d04203140801e84503d640540d600464200b800104040311021851118031551840d000401c00c21000107140301d1300c61503010110001c81e4103400400c15420041036070036504030480410003155460140040759a25030408150a0900804155281d019032068013081c0f0781031500f44090f070b028602c40310400100344010382d0b0041c8000054810550b115000802601c0261110240d908201c40392410701c02e05a414810402e0b9140020a0a140704800d00803040c0d400a2060070201b40540d01000100400c1d521442c40c507080103210340740e85944004458080380d040c0d00071072504d0305c0c1c2e0b254001040c2000c0071070b5a02040401000340400c03145100c860086000761702034a02401c180304098200c80c80025 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 462458821 1250 462457571 462457603
    0xd09061a060f0f0a020124030b0f13021e04090602041502030c210d050c1903022b18080a0824010e0d050f0102041811090d081309020903 60
    0x245036102c101c1d0030a9880070418080507a842d00000d030401e81c09408134248903414014000e0b209100d191481d10110308580c09861902050703121020a1040014102d40c0c1817510480a44c10700b0060030840948000c0102d0607143c20100e0007001c00141c2981e01c00c0d801918684e401140034003901640030301101d03941d41c5e01e000441c6000031a41c0000d8032040c1451034031002a85d01b103215446445500700719407464456001c10083c51828000554031030300100d400180d40951410103150440c00380c4212542c92840348403044880ca0b50410f151180e82c1901d150014154488140c00c40d850000c03690000340607c02d2100741c0d1104c088641c018034080c0020175040c4031624000c040466078410204041c3c0000c03080c41c0030480c1c0740c1e4010200f038003c000c0540080c01c42c400d03907160640480040d4094419a80100c40d0208910311022000040e07607130102d5400713450f00c010041840d203450924811444544610422402d01d1241d00c11b042901145907c01c80f159900017038920100e1805002c115081c4c0f200e04 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 462460071 1250 462458821 462458827
    0x201051e01030210030b13095001020412052118012105090d140d0b12010609091406191125030306170c0f060d09061a06 53
    0x464516090503041c0300281c080c1d15000700f084416072081c0c0100d43d2051002d04035140c0c4245c4200c00c3d0004185242d42617400038480d09002c200101c3d03a20710080f415504120100085d9041c45108131461445129042240450351070303410450340178000b074002001504850b182c18581800c00030704107807040f064130010a11140c4201d0032020000c0590b09105404000e200001d01c0b0740c4010395001400c025003044180780d042d01561146c2c5540c001c1407050f8001c400350b43d03007440b42e4101a80d103ea0032081c03030544107000b84042000c02c20164400c0e440c0d458014500d10790b480060001c0c0c2c0c00c480c1035812088106449850410034044950030025034011070100420f420300e0401c00075a020b0501001c400c100544800394144540341d00029114000203000e00c80480350038a203008211042244c02c110082420500300043c0e100c1e03070075420098480c0040c042c046401c00350080000780e804464640780d00c0300c401e01101d0921003c5204580669100c1e441c0005e84812100e9080044c0c3d030903011352403007010700b0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 462461321 1250 462460071 462460111
    0x180b100314101d0d0305070905090405100c0f080f04050a020907030c1806050909070302091002010e013903060b0a050d060506090117090f060c28050f070303060906080d020105 77
    0x84001c0c0704c03196450b0000301c0f510386038003c0303c000300e540c0e00103544103900605001c18004085021010000301000c00c112041c08020300391522091141c074131010441d89800214172400294446034414440c1068980300304070750b03000420109080d2103240010b5910203000d5032050f040740e0740804400404050000d0103281c0700f0018000d129014038036001d41098408501024025010740701b1041e0000e0a21045e400b1918009009001d007031704c407540540c00e05d8250a484044031140c0420200e8014000000030440044031842104183e02e100402d03507504400610088003801902d24540d083d41c8459580558000380f20a42722203412040c4902030400098000c4da811040703200e214859042108110380e960012036040045009070902540140c1d400c20151101c8074005000c0c9040c041450160203522a5540f40c1980a00c4502c0d40030940411540210440d007001800d5403034070a150104086440f203011105680c90343d804501c0c030b03a000d18034003845940c0a000c1c0710350058175112404035903d44 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 462462571 1250 462461321 462461323
    0x8060702071818060204060309021302130302010c2d11090c030a0e031c0603021302070f020f04090c0b0405031e061807030f0b010513180b100314101d 66
    0x15000c5481940d5945100850484640f2000c000701c2e000041152a40d6840758090003410030b00c03a00301d2107117807010311154500040d44240d0b1084003407040281c4903a81145c2c010744030514030500035200410804c2c9400c080d07a42071156021100d142e0f1850509400039894241480c91200413800d11507042c4804104080190200b503903440001114045200e01c0302e03450071400c61080050392492a2032555540c0c294820942040040f01d20131f483d201c030007514049064040b4043c000e0b00901341d01c0c0d4103813241c002d840c00301c05000b4900c0006000040c0a6100c1d43c0b01408880702e0303805001551401706007004903142c280504c8851040829186c4070000e000302c10151600d20080c9081941c1214030407044d0380755820058140a580d128130500302502d01402e042000c128248910340c42821031591a0304103034402d0151030b01d00344540380200000031066580c03c000d03500060400301c450020740400408102c0000c20713010b55035080030242104001151040065502c1c00c500001c4001501e444c0000c0920 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 462463821 1250 462462571 462462599
    0x5040e01090b1501140d0509070807030b0114060c0312060f040b030a0b040305040324150e04030806030f07140405011205030a050705032b0501081b060c070b030708010806070207 78
    0x50380d03c85441c1031446407001a50005680a0804582100810304210807200381d40304034001d0070110200d603a4180c2d111141070380c58045000003031602090780010008072306032030200c40e41510010403d60038511803000320751640c0c0084c24608801036078802030186508040452134186001980c2c207100b1440c040011036502d9100e4140100140c1c0c8582c0020103040c400d43c252000780d039001007a070340c3e00b0303854081e40445180305014002a162034100300c04800ba500d2051541201c400302c2e446c2413280d0307454409484904000700341d15050300881411800c1c508041c800701024010511590800311040024801180e105801420606948071034a102003007000003925107900d01c40c501f06640d414280351060031406400460241500c2c00218a8081d240c41e4100d11000042c0880400440c2e0366428481d136544d505c04a0001c80192002c0014042d05084009100844098003181c001075501c84103004568400c444407400600301c42c0051142840c244040b5400c00024402004035a08000d01900880c0f = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 462465071 1250 462463821 462463831
    0xb040303120b0d0b010e061f0302090114030703021b0f0c060307030b09040b0f070305010b1c06080d05040305120a1b030e150a02070f03050a03140d09060605040e01090b 74
    0x1c04084071005a441e0241c00c2040002809010400340002074a4055022402030050040700f0b0654070000c0c00c1c508140900820801d50b48a42c107440e00501c41e0150300940c894440e00b410030803404445181c0d4101003000758041c0c91543e07001030382d42505040071110199098500d111941014018654038500041c141c10103070b0007140c00541d41c0c2c4a03044180d0042c0148407040c1d802c68040c0f402c21085c8a40603075014400e101c50741c5440c20b641e030b650004a044420034003e00d03e1040f801d2000341950055802100398203010b00d50001549521280c0707480c0b8001ca075000640004000040520030810203000454949420450f441c1c06c040500801810380ca5125a071501c442110b0002c40040c5880792230031000380c04020b400410310b603880c4020021640d02008004000d4416454000b654585000303032203048980000c043c0001c0a410342e822510090051001a1110024403581503651000c1c821100d00310710070b010001e40c01c0e20304420300040c1e4005241d80d90599240410172404141c7c080c2e0210340c08 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 462466321 1250 462465071 462465077
    0x60b16030807050d0e0105040b150a030314131401030b090f0708060a0b0d0b01020d090b07021002031201090915060b090f03030d0906050105090c0c1b03031b0105040b060a0b040303 79
    0x6982d00e082c00c40342c50042c0861031240506002007030304c0300e000650105002d54080e40c450191b13a038038021607222914000c0e104a4001402e1802080801d00c9411401c10b0610704554607417030101c4904101c403481d030aa07081003101e1104078041d05420f68262107410030140003950340d91040e25001e1485004840010101018061110002225039070382c018030201074a1f01e108801e85800d94055442c000701024130754940588507070380f041101c2c14095500360003219201d500c641d1034450107a0a01011503090010041507100c03e02800030101d03c0d2042c454060302145000258070301c214184024003800d40460288034901c0c03c14180f08502d0604200c03000346109540750b404d24000385e40400d2452081c03c81d00d907030b803a181800d20000c01c111500000e04850303003181e060903c2d440b4400b40f81690f21030400301c00060351201c807074001e0440e9400d0800c480d882004003941d08000c3e8038a02005240800c0781d41500c2650750310100010010110312880e000101a2018014541003000c51812442240000307024 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 462467571 1250 462466321 462466337
    0x1090312110d0204080615040515041503050706050a03050c09100e0d0501050a060302090c0405030c090702010905070303050a02150c18030a081902071223030d050106050d060b1603 79
    0x41018440440d41c000c03002e2041159039550701d942481d00c0d0b400603a061400407040440e180c0603443c041c000c0f0390060291481c0360200e128074908110003040440d07200521101c18410001c0801c0c0140b003150b000301040d0700c50070356400801600400302c81e0000d06c03e08a40c0c1c0b0902c0000c10301c0c0c44201e03010707000300414101008612011000214003041120000f0003a60034036082200103689070300300d2412a48242c84503a800c0c0c0740c1400162250056014035601540501c85251591030002491a0440a00d00000410030303026121242130100030307001540416400900b51454a5040003540001008050074801034140328000d80d405109041050828080d44500c1c0c01503641c1c2408500400c82d0701c40c2406075540c8011b001d80001500071016079000d0300070310303400191a02d8040c28003012a6444048000180d410400d418110640e900d9038107110311081c040801446424860a4080c020320748803076880320040c1000704c00741d074032035042948103440601c80c0b29070504500c0c80140d007082d41410040b003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 462468821 1250 462467571 462467591
    0x103030f17180a0516050a080c0f09040c030501020a02010504020f010c0f0303050a11070507050a0807030b160c02130f05090d090902160f0b0103030f03060e27030705150901090312 79
    0x100c3c1042e100c40c040c009004049640381c01d13031355004201c01180c800384c450203070081d9203808468840404400c0e03203400c2608066221803902d0000b1507507920511a00a100e8120307200e0715103508980104030300c403000d40e6450041c0015450851001000a8400d2801d0174620906680c0e4414001d1100c500034141603c91005c01e120031441e401c8503551054401d00d458075000b0504102d42d03120401d2240300e014401c2c3c0035020809880c085002c90590713401c40004c410a0302c031150b444640c507a215140e80104585c21552034016a10101c0140c1c101468900104d4240c920032011021504050f1080031564050441c078101c140d009507000c2c0c2190200c040050f210000d0030100700383d200c05240010004540020101c0402019100c014140c900a9a80201d080c0d0081400c2c0e0417035015014540d82180d00b400000c1d000804611105042c4d09060080781824024140d42ca1941d00b0144085602c0c2d04401d04444074010703445d0a403039020103e80000d1001c0d0130707681c8000c1c002c0c030b9403044009143d070384036140d8113 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 462470071 1250 462468821 462468823
    0x123040f1209080d050d0c020606030a11011202040b0c0f0706020a0b1302091e0c03010308070206031911091c030c1b030b0411030618121e03010605030103030f1718 72
    0x2c0003040080c3c161000d000041d40020a142e11414a2103032607847c1c40034040d102c1c0c1c80003030040d200d00d10190080c0b440302480e850780612410071542250400c0700150b1443c51205550010f440240b110760f0049031641c0d040c5503a0b508001012003c40c0f159400318004000141d070001d42c8001e901c2e00041500544d4a03131840480c0401e0040c000650004004014020072030645500d012843d40112084056500c41c11842407240c0710a10000c0c00301c1c030050024002500d0304100442c5c216094089401942c0a9034981e102501c803400541c28010001140220443c20110421080e02407a0400c854121859540240070703c1d0f15000013400d0341d04005403002260408200e80c1010350341203184081c05181a2800180010041364a24003c0c000c03c4045001803111890030f170b0441d483e4101801c180200500ba200c0d0319002500e12046641c0c1182400e200540240001c43c0a0700e400d650340e9a0301d604504018121010200c600d10230050342d0951070600100d07a07011960000b400251610b00103140a1500f = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 462471321 1250 462470071 462470087
    0x306060d020c1c0912020609060319090c050f06040e13050703211d210c1e0f0105040e060112090501180201140c19021206010303020123040f12 63
    0x7003442ca1088207204038500100348042008122255183c0c000319031220b40d11010070501c0d880003500018144200e400c186012800303075030700c03840d181c03035200c1404480b01045d0281c03010114142c0d0000440c4c0c909104034180f011082035030140c1507417014078013440c0c104a8800340400404100e881e45c8800540070812000b40080e030000c50b044682001410200d080b1541100e1250391280040340400e0050301c0d20200400c4807100030724000380240107030200c1e1035000c1110720b040840c40e2411300840e21141090345e2425020300b80004040b0f08264980400e006200d60130b410052118140001070008006001e045080c05038800f0080c60917040c01d29200c40700340302902509000900c0c40d42004080000c840380c0501001c8014000d23030b2041d15403805007030440e00903c5903d200d0301c4207802518591a110840311240030718240b01034440b080d00300b000070f20079042c0070b801c2e0001c50050f511101c0c22140250102140810f030740b01038103003820300d0510340c2d10328042d50790b800401040113070410350051400d4010420 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 462472571 1250 462471321 462471337
    0x806040e15040308060307050a030302060a0e070b04030c0815091c0e1824011b02060403020301110406080a0c0903030c0c18020c1603020d0813080318041a03030306060d02 75
    0x181c4960b042c1480c010346140070440385240640b0a07000d0000741d626042598100b100e406401030452904d441400300d000d801603002ea01050b00c9620000244001103100510040d030107610000540e03820842c100b4100551101940b09807102c002c180f2102d184081410301180a03403000f10038a0110380030054a039038500c1c4281d103510400900b24134a1700201666102e100f5403d81040c4000d4003102c98a0000d11090782114074002a00c6203403c101004040b11601d8045000625443c189981c9a001900f510840c02c08003038505e10109081004030341000600b60400c40291781444031810003980240100c01034032018042028220004041c82155040b04000d05001201040c10500203000703040a9408580b207040903100d291940c100a0407224418400c0e25030003030045800092644984030a074110b000c42114034102e5035800100c0340000c0004080c201c07108422030660724065010001215a0034505400a110341e032410715466a010088940c0000c046805c41c0d01e610141c11280024050100 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 462473821 1250 462472571 462472603
    0x503060f070c0302010e071205010c020a150f0b040207060c090e0c0a120216060203064212040b0612010c0e04020f04030212030414150a0311091c02031006060806040e 73
    0x20301240100c035110010b424230340250000d000e10064080121381d0f6481c07000020b030050141c3da0341e81036141c0c1c5035000244038100e6060085829140d0b900000c040764407a04013190350075039483d04448034030b40003141403009000c80c080302480d40c81d04c051800d40f0362148048010401039075490881031601c096043e0350304c00c0c2450300407004a184a1418000941c02510744d0782c8240544040c450b240c1d8000c40044540023002d9081100c03d0200705846c00b10108941c0d228049440280a032541900760040c0c042c0c829030182d0030140d444e080660500c152064000b1202d1120703418007240c02580c6810400022503240d00340c03001690343d120b0f001c0da00401c3c00756400096100200d081481c00010000014000b515402a1904224a00d075000c00c020054181c5450b000610700b800f00c41f000070301950000c2c1e02900b8411120b0b10309a010740001382e0b15070100d02c90070101d044280ea60001e41c1010040280b54000000003040400c1c100f0201a2099034024103942c4520313180c0108040c4c40105000400c0b01c104004d07 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 462475071 1250 462473821 462473833
    0x803041b031b180608030d09031715010909140708041113050610020c010903080f040509240108070c11031005070f0f02010204050a050415081e070503060f070c0302010e 74
    0x2201005542d490ba100c3c24003449580c000c5a0001c0b005031280100321440140114a48104c1522030009420310100580511060595032423501c060710214611072144000350a859484140c0050f180e40d070260410700310540762040b07104540340003900b0306400118a0901d100f80783e2341c52414501441030b9100300e0703821100d5403040c044951056042180a0f40040750701140f1480e1001c0120780d40d012240701d0300d0005200701401c0010800002c010180034602c05480381c5429211004524030b0072050ba04070640420681c6000d0490084101e840700c1c094091a040d0f6044c104454010701044101c0070160544210b681540d407a598104080e66003052840710070300c100c1c640710074042c15103110071400314082a040e0340d090b0310461061007101c00f92507000302101c10b44c80c2044248001001514600300e9140d603544008103280c40100105001014566100640019106040c40c00c1c41d000d40d03c0f4034002e074045002c0c042d0b4160485100350307000c81c807450000c000320550305080303000d06003000140d811070040e4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 462476321 1250 462475071 462475103
    0xc09260d0509010311092103210601030b0f2407060f06210c09050624040f0b040803040302060715050405060a1407020a080d0905150a050f040803041b03 67
    0x401d014114030382090b00e00700850380c003100c5100898440c09410301d07031001c0c0421f142c2d506e5003020640c1416650340003040b01c1c10441545407a90502040110b1140c0c00101d502c1006031030341e414040c55011010907100f108541610030301141da0380030091440400c8900902c109014418800e080d203010350703000b2106000105158002900a002c98001c401d801000b045901804107000d18003035114581c4420500030741450300103a500201005070929920a440040f040c48000721034540e01800351005c2c0d0f0300c560340c1d850203005401220300c0b94021441018103110800c40f0306404000c0d58122a010382d1402d64820503032422200e18089507008620b403601c1c00e003d04c41403010004001b440340300c07404000c100308141208006280b5000321b40c0040168860078102002807542e20142a650480e07102c0401c54040f259500c1d810101c40d100c0842880040300100705d031640349800b4207600310750f41165540840c14241c0301d48100d4803005001071700080b800c0141114012013046007600643d04843c0c11400c1b2010 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 462477571 1250 462476321 462476327
    0xb04180f02040c080903030f060a05090901050906130309260d03060306050a052806080d020109110d032a0609050102031e0c0d050415020c030d0f0c09260d 68
    0x1918410782c0254034155500901d00d0003480c100b80100d260000450a541da42c03202c00d8840d447c0103140c03d401c640844400a41900d42c841e03418000e4a0311000440c251a08450030b42c54048000d044045000d950310711040403d070041c46090030740d0b4895201078682d001202907520740f2100002c2000c0944a00611200f10365071680c41501940e200e203e081c8010b80300c001002058607019101b610380d00505000590f00540c0303800d42c02d10444121100450320329641e01304141080c055030707000780c0541d44800b00c0c1000c0144155609800c804112580181030000e80c90040c00f020401d820384039801070424100141030385403030800c5045030740218103200d4003441e840c080307000c1d41040d1030003204145001d043c010700d49400b40c8440e2241a120000300d003400006c040070000f40c074001c1c1c000d03109140a103640e1546440d06d400203082e01e040311001103a4a142151144003200e1b4211800b000712843c1c15103047d112540310802c40200c4881c5c018592103407580542c2c03071900f40300710030408280340f0516205441c40c40d0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 462478821 1250 462477571 462477593
    0x61116030302030a020d0306270b03030c0703151104060c06060812040e09060705182e090b090303030402010f02010e062a07020303070f0c03050d020304170a0210030b0418 75
    0x200c83d070aa40c1911301c03504c0b00707a0694123140121031100407c040d4420a00c80704c5190082c2140303d0103000310707481d501310011a045922440c10b603001900410401c4c401d201d40f100040c54041032840301008031001c03c1d92203080c0f900482c09140d0800031101181d07010f000e5660080c00203880203400b501c0401403148080d8415a009100700340540711030400182d090325010031101d1050380340e511120302d040c0801101c0c40c1c650f1040c441180c5d100c40c4038064602000d81030103400c2d12a031078800c18403c0c0d4a841180c050403a21702e6a1210310700003c02c1090078203944020054a42081c1e082c02d00b40c020800c802e8041c0d0252400b0440c40e0014800c0008020b0480e5050f800d000158400030315548258040418100c80b91045440c041c0d0540d00400090001070481948002c01038043d03400030400c691a40c1d241401d00815000040043c0d20214040c4049413400e04101e4001403014002d0040603115408501f864031800495014960b484044100170707103440e00403003640c100c0804140c1d60388105282000c0804 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 462480071 1250 462478821 462478837
    0x70c0e0a051f03030f2604020405060d030903240e0c0a0801140c0c030c03191713031d04090309090c08010501090909020a03080c010209031b0a06111603030203 70
    0x1030800c00882c0b030301001d11078004030340c1c1c04503001c2420407030568400b1744022103009205802c10601d6000c0e24035280743c03031101d2040c021015030300c61118202030042000383d805c0a0301d5648681e2101c441500040e401a082c3c0c0c0881c2d5101060468001804100c11480707607a4403446c8070304c90f04080403640c0340d44000c6030188481004603110320302180c0302c42c607031401c0700e40c0b140c5600701104489022580000500014100d81101d030801c484c40c00d00002c0c2600e09540184d56110b03114800c604540c22015045a0746203512103100d01d132a11a450002c2e00c0d01440b44100b10054180300b100c0e81d07820b030b0b105000400020010340140c000e206840c07861800404066840c0f040901d45441e20748800403a0384501500341c100c41d016940c4c2c040c0d00e400c0003050340003401c24000481c0e10240c2d03400300000107000791001c0c0900740141400180c0704c271165800d050a200c83d4074a24104041d80c2a040c00c030030364032105142c0607965a4030301103040d090246011460314068203818200d40320b203108000101903000004084103 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 462481321 1250 462480071 462480091
    0x902060d05101e0b03091002071a0a02090a0603023406060b0c0d050d1404030804060b0109060f0f270618030c0e060310290f0604090b0105070c0e 64
    0x105599032034141c4854000d029100c004503140d10104030360b9107501e005e10341041007407040d100403c080c4074201c4200e90109a04407415604110b100b841540c403401c003a9440380b001c40041d0700d411340c4000042d1000ba40b42c06941c1c14143e0100300c1803d05102002e0307030b01015505882c0d41e4140c1c52040e8100411034030401c401c4852500740700002c10000c255500f620141c00380200101201c84164000745c84a4000d50b2519002a0f514801c0301130540b0700e280c2e21030159009840d45e041c80d0030941020400e40d611385400d50b060060f0380b10b0402c102070f8480200102c50f011480c0ca500c500031801d100702e42d29480750304901e0b8440d0885003020b400c10644200c840480c0c5450320b45445020001c0801c030b0b0302d00ca00d880b0240020b0000101000024480812070703911400c001c050f201c0c0c1c0f01c002107503c81140c403030030384403104098100881d1101d42d001d05220401603004584034400000c80300c0c000303034161045000b43c501c116100c00121040d83d000c2d10a6600c010fa02603883c06c0b00c140c4070600c00c030441c80308540720804 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 462482571 1250 462481321 462481351
    0x6150903073f0816080a03020a0906211a090c0a030c0f0509060f0f031006030b0d080d020702030a0212010c030b0d0f140309060c03040311060f1801030902060d05 71
    0x1c411032480c0c000c10503400b0101c200c40220095140c408054100704070138a65020409003882c00203c41e0f200a190000c1241c50043c1c58401c40030008045c4147e9130061402e12907500da1568510700c802c1c2d1b25039001484081c010406804000c02a102a0f20900003160000c011105000c3c004883d54050020400659001c0080711750781d43c412514034070786202c0803011440402043c038050410380000d110130040300416514100780c1501c514100da00849103125004c1501c402480030303d9041c05402c5140304112040c0148407055103441c40c0521880800d41c440c10340c00034240c41191010301c19008925001000d00910b804151506406070a903070100c0e03000130f0314010345141c1e2071a00c1200032008076044411440d10300e03615580d464050450078031041e094441070010003c140c0d100130091801c6503200d0081d5403183d14602c0d1a017081004114840d2044400340036aa4410003804151384e108501c4810a061040b60800140c00608202101941100380094044101c0c59560012409011180300d4006 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 462483821 1250 462482571 462482639
    0x51c0c1109010308070b040305091203030f10060e010302090a0509040f210f03150b041707080102040302010e0603070311070b06030d1707030b0a08010501081501060c0b0615090307 79
    0x5003078109010003004502e05022141c0842c40207440198020700c00d04280b403400a460001901c20818844418050b83c40081000074038104541459080414550100740d280e007400d5029003c0f02002d8589410194042000007550f51442e0081c2c000b884068980c0744503007072500f011f000c1e002c884403040c0e030311140140c1e1107074683d603004034403181c1d8294694544502140dc610200c020b80802000415540102c41d4042446000a0024801031441810180b800b010110200341002000d520455035644103100400151340c104550201c195000c840960741c076135880800342e0091081c07080c080c4203a0700200c1c0c030f0b000301701c481a09a400390000710300703c4000c902c50074022038072200300d81a024032107080d29010410039402038000101307088004084100c410f8a666005003140c2099022070802e03407003058001200e01002504038090186440d28014442c2c003a1951f680400018081c140500c00444000d600100004280c2c0c0420b10000c00b80c683c06a60341c0000f01a06100d0b540d075003040340c07100301d06031 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 462485071 1250 462483821 462483829
    0x1b043902060f07030e0c09190e0c13050903040906060507150b0d062c0105010911030403080115030f140f0106051c0507050f040611150702060a09051c0c11 68
    0x148036a910b4100461a40d58200d811409084042c820f034902c0c0c032503503201e007134582d441c084014450549405510b141c0a5180c260400780e40341000c1041554120012129047e22140d80c64414442200300128442c1c03514000300307107948225407141e8096880c2110102e84c066102000f0700700c40d40202d001c1c200510740301c40c07200c0031241003c00d099400099070201c07200180c1142c200c41c41009001c42c0f41419140c008a07400302c19000e01401d032800e80d40d500014411107285100d4003040300040d40b40c441c2180380c00d940142800c0c0c01801400e81e00d02d0b07100a010702c0c0510940007507043d020b9101c03082c40840364490800d14903120658483e034020144c4000030901d90701c01c01c00e9449500000c00702000308281e0755514002408050104010440c1c208181d16216202d0b10082004200075a200400d803a8a0600705007040410030031903a015031000140055103130b0014025070021541140000c40c00c03910314200380707807c0500c5485000c2c1c1d5040d4240c0c202e9507030010300c43c8a01600904214940080c042c00704 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 462486321 1250 462485071 462485083
    0x5040c081926031503030c030a0503060907031404080d060b04090e0c010e03030f03061504120c060e0609040e0a02190501030506040606050f030a02040306180210020a02031b043902 79
    0xb0b00c16909040c0000f5511500ea074100600b10300c0b000d015203140840720006c00382158040812500811030000c280700190800100e62640444149410028414070442d80600d114001d0006840400c010a450740c03299001c0d400340000384024290390340e41d5039a400b0000c0260050040908450140100300d18155002c0d580076000d03008000c001e0b40c40c00f80480352003041c81d0400f4000c9034128040d0403c250640c20044014000303440b07151041800300c02285003180341c0040c543c021784104000c03541c03003c0c800d80350241135800c1d088084501041c01402c0c0407401d40742c60480d00003e580300c1c010302003c07035000580400c6d41003a10000c0c0d078248055034491042c03006442d40c034450180051405c0002d52580b0425070061500014110005850940c0d60b4440505070ba490500c038006541030b522500045151900441c050400d15001a0000c800d80d900003d81310301c4881c500300c80722420390698010f55510359000c150028000d1024211541040345041e4170044003035802480000c091810b108024000140 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 462487571 1250 462486321 462486383
    0x15030703030207120302160906050306090c0a1a071502040503190525030606030602040501031a0306060105091801090e0c010c08040504020a050403080a0f08060a050303040905040c0819 81
    0x9100c020314180810314146030200f0164218044d47c20010200041e4800c1c5c034000300960203001c110181084205803d00030007070043c4019034440d020061041c3c95103075802c8121000305070284070700084641c0d414041d1042e80341c010040d140f00007805007144050b90150054500075000c03190440c0b4000440074928905130005002a4440140002040c1a032050074140300d006000c84134500e035686d52840b00b640c055400448185401140520055030315225101c2240001c10520100d2111100401e80750304000d4501e90410000040c44013050300c40c03881e00051101c505034000d1683d81d44214040040c80d050144200c58003841d03907142d4041d0b11a60111344150741001e4005c3c5001d07e000c1c204002540412008003c1c89418400080441d4106010b08030b042500d03118440d5140c0e440744001d095036001490a48130b800c00c0c50702807010752000401e0760b040c2c0302c841c100020a5210b50902c40c615505070b921090381132003003c121303000d41116204180d030183d11946000d146a585202020804185864 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 462488821 1250 462487571 462487573
    0x110a02030306040c0c02130203090d090b07060e120c0703020906090415050619080c090631060f06120b0f010f051e1317072607080312150307030302 65
    0x1040540c078241e408284d5040381814942107a400b694045030255842590920f005139012040045202c0c040c4480003251109140450301c0c64100266074280380178194004d8200781e47d82c04580b0405100300b1045042c0e200c0c590b4910340b40d8041d5010780c0ea841140303000c203e024844810214100c0d00f00b1506080c002da90203402a101150200d08220040c0700082032564405aa9103407440c00420300d021038006451890064042c0d92509410300ca405140640000d006080f03040c2d101100f0508042021109106403c0501c84840003032655009003803c0d0304000d1140030701c00d40000780641c0114083d2100026041f050152081e1007003000035001180b086503011610440491101910580080500d6841c028184804e05400308103201c803604021411480250b4040051000799a50704004d80e90381e9882009100c010305003494070800a018440c1d08030301c40185140c0c0c103040340040c4104c1002d004000d0449403142030303120683c5c800d08004c2e250b140302c40e404181d402032a03050201c0c4071000c7d0f13a0560 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 462490071 1250 462488821 462488827
    0x20a1406120405251d0408030a02090a09110415080402090402010e190314070e0c09060a120c0c02120a050c090907030501062904140d0303090b040605010306110a0203 73
    0x74900115040082003110507008100d007840764031024101c8940d4000042e04464a80c600b0308a800d43d09074015110311080d200c18004001c00101120100c0b540140860f03400b603200c903003d01c08141001e020b50405410107007401e0481a020030341c2070250040b509082604050740c0c1c1041401e5509000583e8080d400c031291000040255000d500521070311003020f0141d0343d100e00c1ca1010303014044030603003080383d0840d0310050010b124141000002c000d030058400c031440c5824100d5201c5924450310280d02d01071100443c04052580c0500303d072065a1120326001d21a288180d03900500354460f07480220700c520b08190f60904500380000f00f0340c10003a4841d00410381c0988107001c0105192b0000c200d99490f01c41c400c00400010420b029000003000d4000040b80150010040450b190000100140610400380b00800c40030315600c000d2034031200107503051484d40d040303400e0803000383c24480c0b406410010590300f840108100e40c1d1000d4100c074064541002426040000d42156208490442d00103030310034 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 462491321 1250 462490071 462490087
    0x13c0b0901050904151703180d0f1a070224071202090423060603040c0e04150c02061905010b07080c0a0204060617070e360c07020a1406 60
    0x9800144400c50050500c5400e003c554000201950407030440d040808146034003c03c101e900c0182800035003050b0034003031818a1b01141c012044200c5500005104450a01c103c01c18400900d040450780c5412164071f100480c110000610020703030980b80c0301e006214210004c1c0c0c804440f280c20b80c1c001300d000034921116866548048802d40014400d17800056400c1203150503076901c0780301d501462600c00520014603050710608142d0b0210042c60b07680103000c01c10070003000070380051015054030000300e140c00c820384550510500c681a407100c800b0342145818000c17000190000380451040302190a001105014548000151002031169050300b03842030010100043c00e020151141880076400c891200f81243c00142c20b807882d41d131121002c112548451000d50031071a0800394019614200905809002404500c0829901448691103a1001e42c0498032003140c1695400c030325080d000558107820085031098940c1d0204074200d101c6d039003009002460030300454020024040041c0203c1c104920 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 462492571 1250 462491321 462491339
    0x150106050706020c0c031603170301300618050c01140306100c0203011422020f040b03010207050607050a120b09040303180c090911041b180e013c 64
    0x400d02007548130b40141c010164980e1410841c0504001014980001d55842c1d400c11250540014520f06580f55040005000301020400d0710000d4405149000b4151310b0900c401440380d00103004010029410b00071414611140e54a40d0220340340a0381c2559074410a00006480740314006105282c1d81d02c0074000036900d80342c007451520505905007000884003086500203400c40d8884c0300305200100756901030000001058030150b500d544156140100e55945400041d004a07404043d06d20658843e400d031042170301c00f034064881c0c16611000302e074200e08050b500981140c00042c3d5110000f03041c00e0303604208507801c0c00b55401c0070901400203040d58890380c408a020340805070424002521025004001640b10f04c409402009c0c10840019501d466107400c1d02603000303000c283ca00c40c50502c12280001c442d0482008126442800d10040c07030350710740e541c4503403904aa80c4070100210408000052541c20740c138401c5100072113148100d204000c00a98003500c80444280c40d001c1c548907203801c1c803203490 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 462493821 1250 462492571 462492577
    0x70c020f041508011508070815060405060a0b030a050f0a0603170703020717070f0e0132040603060b0415030b04060c03020412151506050d0f0906020a02060915010605070602 76
    0x140240071902d00d0310746240c00e003511159461840c0211340f0003001c1000c45014010301c0082d001d114064080d200c48a907400e1442c1c5070207020380c1e10079550340c0041441c80d940c881030a00141801203a60380c681c640341c01888000c1104a41c14804e0800c101c2c0001c0c18111503210303400580b940074807480000b00042406a40c03a812040b0b0440c00d512904002045155528014030003070788002000348605810300d0340703415142c00d00d50300408001c0445001400b40d1114540320505030f800380d40034402f00f1000c048400768010f0407a002c42d50014076014001c030074014642c100c00d107001c80540d001c0c842030480902c00d491244007448040c092008800102e03000072101d420131b0032410440e28000d42441d0710748400480320422038900711602d5800b080000c9100380d141c007c5c81c13a1003100407069140c60b0314000007d0706501c9180040002155950048c1b80d0002d8540e01c00819207400040031512104d1800020b5924241a0386d070384040d11541c00128503a40100c610281612090364a581c1001d12aa0307519000e90 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 462495071 1250 462493821 462493841
    0xd090c09090215090d0f0807052509110d0506040f0e0d030506030307030801050913020312070b1e0601030e031611030f190609230303220203030a050c0a0812010608070c020f04 77
    0x31508000390317804601d04110700e08811892b8000ba06100c5030700c0802c41c82608055008815540c02d2140c0005140e80a1040e14400c081480380410b540d03954000003402000524040c807200d034039002d58030500200018059a081643d51410480c0351a040c0425035617004800e402800142e034000103201074141005c1d07064012030481041881010554000790508241010302c007100e0102040344824480c04405190304260710303080030758481f4560b0b0004005140d0041425051649841c0c0780d51044008008544000d2600c10044400f81c9203031910900d030400e40c071a414464460b00240300d0140b000415a50022580c0301120031660b0781030b035640c002400020b0415110721a60a5a2400e0140000a504000351000c805550390386008070344569440b200804500d2200303440c03149a00103071000411125050400c5c100329480703020510680e86440c1c0c3c1480b0040003034002103003501002205101e07403810794595407240d080d15500c0700e5080310100c100c1c4002030750080b0f944044109504103030707103e2203000c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 462496321 1250 462495071 462495083
    0x3020c21090103021b011a01030c1106040209090313080102041419060c02040605030102031306050106030b0310090c0506071a010902030402060910020c040908040e011a0f0d090c09090215090d0f 85
    0x204c06580020f90854591600c0041c801f00d210480340c6456034984500c0c100c51001d402c14948128040eaa01caa440c0d02c0100002d00031241c00d0b01003500100301f0020b50761b20003003c00d1301e041101e840f030202e14080e40051240803203664148243d203950703240c9042c0c85241640740c1200950007500c1d080040f110022181f8090744c20956070003000c20640c0b800c2c00214840c0103442c01d03102c184002031130080d0031100164003a1042502d41070700c056043c0d030f02160013500c0c0300450340003150688840c00c01c06202c5016511047c0e015a0009104041200d41d0505901000c0382c100c41c52110303a0307903001d51821303444121000ed52012013000003c45a20b070000045940340c1a6204859100c2c407420081030840d521180240c51140b404241009110810b014031400340041d019403111500008413441c0c1076000b0303003234000283d01010446105040e16035001014240e000100424066500c9903404010140680d090307029030b09002c910b41c0b0000002c1c0443d4890342000c1c010a4040d44217446600c0e000c48440c1d070031655 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 462497571 1250 462496321 462496357
    0x2040615020c1914130e162405040b0a03060806070918060312051815190c02011b0c03021810140a0e061f03020c2109010302 55
    0x3404040005040c040c54294004040c03041c000c41c02c00c1120005000000c0c0100b2280c00306212101c0c214056460722601035074221050120f1006040241c800452107804074403411828618003081000c0c000c0445200740025650000b8030f900300962003020380408230201e081000304220107010a002080b134a0124130f0005032540c4c0b03036070807581059029a945000110304007024031441c0c4066a1010a0034017042041143c54030316034480100782c2c5418080d0041c8403002c1030b10403047c54104d4941200000080089160501510804c81d0b65004070404d03c0e681510380744207a90a40c000e0929508040c0c050310341c68601c0100300460310a040509030100d600003145032000005803100b1041c0040c040d68070a107040907140c244e48001c10480c65501c0078500050402065a498656507a25070a50701a0144e07580c041d07803043c01290010340c0d00080100c0c40e0780421011002c42d541903020344090703203034a0103848201904517082445450f0902c50003022001c05c0001054940c0a90300400381201d1185080c10 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 462498821 1250 462497571 462497579
    0x1409100c021f020105060a080a0b01050402220b270a09020310081002040815220206071a0601030516170a15030305040602010b0a180c05220e1608070c020406 69
    0x61001800b041d02503074580c1c050102c5445c1c41d041e40000341c2000801400d0300d55643d21190030410041c07144034012607000440e107424015001400d4412240508a400401d07501c140f905202d031f015441505e8034021205c543c0c8481c50400d046140c484200800e0718000c11709200790303c802980b000d0218524000c0d0300c503001a814109003c0a50081d00105005032103030320b406d0180307003403070301882c056101044614104101700400c452000410040c008103c0441c048a10100305a0310445401a00d82a04162010341a0044440440c17140750203a80500054903025042031101030003040c1c4502282c00c100d002a01032480e500032507030000340303000c0c0031801c914580004e070118801d41d0829000180001814401c4503024003542c0c1010320f0658a86940030311f031141140692138030f01001c803c016121210300c240a0321410036988841c480300900060481d1280083e42c1d540700a12903040c0040c016000590b10340070600103280c1941e8035441e070384002e81d2000002c40385107040f06000c0340d0103661104045 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 462500071 1250 462498821 462498859
    0x612100b0a152705090a020706180b09070902040506161a100905060604030816061d07030303060801090203060601080c0c030d020a110708030f071502030c09011409100c02 75
    0x1103071003494070f507641c40381060700c18003801c21075108101503807010707030f11041055466041d03640da030010003000700584403d00d40c9454806010310b01480d5920044100c1d0b072809000401440c240134a05075804c031080b150b03654400c80242e000714420941e101005110f4001304598001c4054803581c0708620407000740540c04541230204405845d081605071541005106500341072080641080b02210035038101491603841403054424640140000003201c1c4c008000c00541c0d40002c40961030f41c1c8039445205c01001c101681d102c0e483d03c020b074002402c00c080000c442c0d0b010311a440d030a03a0090054985582c641c001507035004800b404a8504031020400001c00740014805400f481a0f180005a980d00621030001d042e081d451b01003501d280c100c003204002039200042201c4020144000c0302e5156a00b908050138a40d00700321890000030300000c1000303103505030117000f024086c07026201d030780300c00020703a81003040f90060012a40d004591617001100709030041c2048000300703100038244044d2140780e030070300 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 462501321 1250 462500071 462500099
    0x1b020706090605280e09070806030c1e0d2d0f0b19050702070609140109031202010f06080c03070b0c06070c14100c1e08010e10120b0402090612100b0a 66
    0x402c000500c074444171600d03840d164500e0741e00721045241c10181d50600d10002900c41a44072650703131091003044000310034200010103040d881c000080092611041c5420032620402d038116144e0f4008041c09500440b8500440c0d41e02181078100800c0c1030068091b6481480011001e40164401a41401003401c006440d0107468421113569018003291840d080b0043e110700110382090a4482d1130f040a451140da0050810007103a40242200b100d51406442c26401005800c000303000290401901080d0342200107910310041105a003181e286c0782d5244c800b1b1005021300b40204031990025404a09510300c50011400010700800e55000d460060701405883c26010550b41c11070542c490910326000ca07000f10212040d03031400201002b0005010342e000b82000700501500368002e9403000424801590145801e001e000c0d50030101d450150241800301e89140200c404030700c250310b03c500044082c1070000c508040700440e07100400f009480c0304034002c003a010709000f4507088007090000040302c9450f5603070 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 462502571 1250 462501321 462501397
    0x901090f0b120105100f030b28030b09010c050a0f0314040b18010203190504140a05071a07020a090f1509090201260402090a020d0204091b020706090605 67
    0x24242e907861078058032290080d0140d20841c440d030b680f800c404c400c1d140c0000840742c1d062050321340002c00d00c1103400099680a00a0002d41506904010780d401003c1d10044030015a80610354209032039031409601800e0303038540400c0d40009a01485104006030140e60346000b07501c00d50402051042e045440d400380c80b0001c5906884584a40d02400305000416011408071503c82c4000d41c51460700c5a412450781c0e1546091501c030380e81c2c45000909104260a60f0b8201c0801001036030150165070074101c0d035594150003912b034115400c40812548038039000858840580c09030071402250b10300b400d560000c0110284400103680c8582c070490001c0031001ea8900545404400081c4440c0303503000041c01e00c440c44e0042d000c5205103142d480ca444147c2c240c40d660007681100d40b210103903246000c400c068003941d8042001e80c1e0001c1404030744110250401b40400824000d19200c0900b520300c100c1c1d8850503072040304042a0307081c3e01440b1a0380300d00010a4000244240d480405052601d614281d2004d400 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 462503821 1250 462502571 462502589
    0x1207080604061415091f05030d0206011d010e01181506050d0c050705120715090b07080f040b0105010e0303090a0b04030b01050d03051204030c02030d0c1401060b030a020901090f 78
    0x2d610000d40e0a00d000b041e4101303942003030121204030300b035001c119800070292030148034591007030300740101c0c0d407013814500085e00c00941510050079910710040c7d5100030038011440c21800090160f0070041d03501c107000d4101c0300c0d410030f004040c0c0d00e02549001400c0c2011107070710440740c440365440003c3c08210304400041c68940d840c2079076600ca280124080744c48188288042010402c610f03070104a00062070385002174030301041e680e00e908030324151004444040e04800b10314100081c1c0410700c180c954400b4450010398403480c21643d02c8200541c3d580e0401c076402002e001d40d50005200da94865104500400300143c101d0f46054070000000705030760400d40c030100c0c0da4503000905108102018141c940140f03002d8604035485402550054018081c04565040b08840c61000409040c030400365401d034941c020b02624003171031401000811180d070100043e40c1d86020f0280004109105108a20072101c0d00505a415501c80c040c1c4100a5070040c002d0314100807580700d001c01d80c52044d0302c0010090207492 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 462505071 1250 462503821 462503831
    0x318050d03081906081b0307030b0c18060307021009080405060706020c070602030f07120309120305041a24040212010e0412210506030703060f020913090c05120708060406 75
    0x1101496050b5054051501404c0513810018058001040034801128842e028071004040011030718013900743d8406040380340d82c0002c3c1300e007800d41e0800603c4c446131180041134140c1407070010300005120541d042030040c4c1c4800c6d030341c50411442d9400044950300c6007102c1e0341f400d03a0f14800649540c2002c042503892550002e550341c0d80303800070042c51008000b2800514200010800c0d100d00d80d00900c5400b81900001040300c7c00840e01ca03920025503240d010044680030010710700006c000303040480e412200c0c03006002c861400c40c54900d0324684140b0a244000d403024803040500200c801d012101a0340140d001e1001a0315413030b407005200e0107090012a051340928250409100303e0050100403420700006402c0d00fa440e8080c45001c0d00110042c0c1400b080710340b135440200e480d00032240d10180081d881d110000c1c14018081e001402c1c880340c01c644290700c00501441c5641110a80d81004040141c401c0d002c00c110f0130300c1c0c3c1c5c1007181d22a00c07800b138401066a455441d418150101c5045403207958071 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 462506321 1250 462505071 462505081
    0x1170613020c0114100803070b09030d0218091e0c0f070b04030c0201090b0f030a05040302030705070608070315080d0c03090e010e040c1d180a020604090902030601120f0318050d0308 80
    0x5813258050842181c101725035180005051700e038400c0c0b081c060201da13500c40c005a4940c00030000c4489000800300c04550391a05100703090402a03481844030312410b400c5011483c4202c5803810a80d01d252040d4841c0d00984604d03420341c81070347c80044600540b08003448204085210140e03c58400c5029841d440700c500b41d40e1000600382c1f3340d1034018000b810340c1807000b40c0b1014904030a681e030142c110000010543c8031401c06915601800d040104680304a58010604540c0404d5640c014602911b00344440c0346101c413410400c80e0b140c014013000c7d45c071510020051910614100c0003050017810b001d40e010f43c49002c130a01440302604207042d0000d8841c2400b042080c3e000120006081e190b645031040c1031010032180c1c9100f401f529800c1d4658110b0014a40010f0900080d620654004e0642d50358555407000c003406030a291006a1090140c0000014454421120290220342c019400c01c10742c0c40c2ea41c3d0503145030000303000c4000c6913103109401040c03684502c0800051140a40c5440c2d03100e04d80 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 462507571 1250 462506321 462506351
    0x4090c030e0307080a0e010908030c10050108031c0c030902060d0b030d050a080f0403020304080304080709060501030209030607110102070b0114040b01020106060e3313050307030201170613020c01 86
    0x1007030400e2500341d4002c100784004500c04e0300594111400618111081400d01c2d001282d88020541003220940000241c0e11256040007401c400c1055030b0350300a0090381e90311704405880303000303840c501680c20030560380075050200c1c143d100003040c95542c100000e10701081d8021901c980c0103511216a400e42d20701145610345020001c0c00c2c20b442551810740e20380003044500422001002d822217034a8602040403908150080c4281e402801d150b000316502e03030f507032480d06550381c181030320508124a14004000c50154071074001c642016a014006003800d890f00703001102c644500400b02110741d5800d00030b40c400038504003012802014072142c42d4500e1400713a01080708442101422505580c98020304200c4240c1291001521010071180442031907e203422520f04c43d805082c0d00080080c5d01c505142d08a51380314003610012585400d0302003202e0301c0340140345d0760f065507003c0a4049103d0700c1100b40008852003000b40c1c01003025020301150704949407000d040e6000794000e520113945580c640c0280c403007 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 462508821 1250 462507571 462507581
    0x40216150605060f092e0e010e03070b090603180d0309021c0c050f0a120c030c14060318010e070f0510020601031106090a08030a0c1e12051e04090c03 66
    0xb4040710024a01200b56002c089203120304a00580078880048041e0351422100b0b140320946000984200340c0032612010080c509580180d41c0c6000c5042c1c00020807203410002006d10585400d00502d51400d07540004200700c5400003001c0d1100380c0200880605410f0050140070426403030780c3c8000c0b408410a00c104104030745964010ba20301c044551000c8049000c07404030f80d003126000c0d0b55150301e102c40784000c00c0e2001401e41068682c5064110350b8001c106800c2c0c40c0c00d048a008034040304c0d08580310800c0681d0f1300c1840340b800c1e90010060010070450340b4060080840c0820200c00080c1d883c040200550801186904c42008448050800c00107401c00141c008034202451010781110b605590310921083c3c1240c10046c0110310224280040303480c0d0101c00000303801c0a800310f075250540f07508005c2042c03c191400b1100c2d4516039003203140d030590201d08051000c4d4441c8a072210007100c202c088503e40c01441900d010803c15407038510703960f800940140081c213040d0b44085644409074801905840d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 462510071 1250 462508821 462508829
    0x15060102010c0806092205151f0302220c02010605040b03121206060702090a0e0106090515010f0311040306090203070b13090b0301060e07080901050f010f060e0402161506 75
    0xa4108502c1ca403005500000d1140c0c04541140c00c8182d68036a40240e0b034480b410292181803108003101c02005021000402c000e100c0c8400000a00c569548138107400440c45403145c00c0c129510120051005103482c1100b4450303816218424284c0120032118181950310407000100540d56410090009007020b02401e400710034142c0042c4032054150020107100d00c64481502200510031002c201c0c956950011508100d13001010300c41d80d800c1c400c460000810144050101540c41c208000900b00c049001d220700c0361420410200c00b0040320300064031202ca00c00054010181d0310010703d585028a6030203800654001c41d4000340c070070301d5441407500d4001107030003c0792402c405004800410840c818460140d499070000443c2c2c101d1b80001003030150031a604108202c000305c5081080310341d4090b940600c102c07500d00003400513488240300300215002c00e007d10f608680c2c01e810103001d900c1c0103c4d6800c04c4c0d070a0140006142c480a40c08010b6541d540c010100c540001c50310005041149a0240c00050 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 462511321 1250 462510071 462510073
    0x61302030c0d0b1903081209010b0604050607022b0303050c040503030f130f0308070224220b070305030403090902031320150406030c030e030403020d02060f040815060102 75
    0x606200c8801c40c1203005503415074040310340343c07500e10200741c444c0c8011000c0081181104800c00c1d0b16450a00d03400e42083d81e225404181d5100015140c2005008806907140c0250040303107400e0401e0300340210b0381c1c010281640c01c0031420900e10413840a00b00110409000e440c0004480449442c0c020191180a011811108005e20040c00307950340205c2291030f0464032444044d038a888120706c4c0d004500c1664003c0081b8400c1ca100003080c09030110003410018421a501e2076010071903600d802c3d403521000d0300080401801e1120406040b0307035284600509060840b41c415a41c0d5800203a425640419811000580301000b03101c201904080c2e03c2c1d02504201c0b40c15421850711903001b8458560602001e40018904120300034000e0b42203810f2066600041e101c0f00079070084400c01c00389540326201d60b5000030f2500783c40c00c100d14820310030000702242880185103401d10b180c01b0000501e1081c0d8059a0180c010005000507100d1a8010030060130460040c00804030412150001f800e0014111419 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 462512571 1250 462511321 462511327
    0x5120c03120901110f0c18070f050c071205030a03140f0402040207030509120d020c1009120203011103040309030501060b0703050a0827010209281203031e05061302 72
    0x20a5501050020051001801d0303203072070740c030310100403242da0202940e848203500824881550f5100042a4000368450542c0c0c11500c80340d4040c1743c0c02581c1c1044034100e00181005600d00c03c6030b4400c100400e05078003d00100c64480d5140d0b010b581010340c8258044038150b000140703800c1c480b50140100201100003c8060700035141c8001c0003010303160010710080c422640024000101402179090f50308030341c4050591030184407480d030395680da00e0031144e01402510846110103402d292171500b1808034401955440e40403071030030200002c950401032040740d0654a41d86089510765012003d544554000d51380c10b00da02e49036090060840d403090300040b000c00402c00c402c40200c3d03000012240b00700914a000c010035600d16103041c40b2501c03040c8501450108242e41c0c0d0034220310540140c840f09400329105001441e140d9403d1022004a400c0c0110804810350300b0801c4a60040c1ca10940d103010342408110304000c0c9181d5517001048246a0200380d5807201070294500f0001d910f903284030126201103113 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 462513821 1250 462512571 462512593
    0x2040509180102041d040318060c060b1c1a1014010507021210020705120a090314010b06040f14010315141903030327020d020d060e0d030203010512 65
    0x5004030092141200c0d2151980e81c401c10340c1c003541203030010805100c1802d61000c00064090304000300365001d40009034800201c9000c0c0500d004020100c0b000b0b600d80280c0901643d590502a003c4011000da105100b4214500b41e00d50908101841c2c921500d4061340645001180c10410a00540030107c030300d00f400c0d4240301a0100c11000b840040c0300b400c1058075071600d4400a1484080d1142c903d4180c02400e040240c0c4400d40d40140c01d0300e91041046d108150700018010046002c0c4d07490100025000c5031003080410805060341c1c0640044a001281c50000000455007550043d840240e18180b02241000b072914050002103075044246414003044800301c849d2266204540645908035606080102c8a039607218410f81c50041149844c180c10356490401400501105000c2a00c58240c40d610030400000c603802e0980169004100082107840b640030b1142c00c3ca050281141c04e0f036a60042c3c40f16500c3c0800241d00d0313141055a0259481d070601c0f061000c2180c4121090315140c1c040d40d0380803 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 462515071 1250 462513821 462513829
    0x503071403011509020d0c140a0810080106081c05030f041b030501050f1006020307030203030109180f260708160602090d050705090f0106120e070f0e1009020405 71
    0x1a04031140386100e030100c02001400240140b0401180c054003e010450014402c0007075006080103003c40002000030340750140c000c1d6102e100402d81141d10340c0040082d001014051410386400c0031007a940a071102e521401020300b103821036000050241e000500013944140f06e121802d02407040380c41e0060641c2480060303403160b0540a80014100b800010f001d054031000324580c00300a6030444005d000d42d040c0314001c000e5410703098900100c1d0f601012404500c01c1e000001300e48007190315034008c42c9903a00e0180360340c00500c41108120340003c4056814004101c403250640d800c40e0090841c4440c180203007039000c1d080454041c0381002e040042c41082e011079100700271b984406e41c1d14100f40f000391041e89003100080c80388072113003a4489010020030080c4500080d000c410354400f81c40711a1305450708189296214800d109403000103541d03c68030384c030380c4a140d000500c840d021001100e00310340e100e940f200001c8005800c03c0e088640303500100020844800ca256000f006a401c0442c03505003410041 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 462516321 1250 462515071 462515083
    0xf132c04021201060e04030519030b06370521071e1b060f270602030c0708070b0a050901050408191101061d0a02090a030f110603040309170c03280c06050306010906090503 75
    0x304504dc425403c44182c1e06200f103003a10344406052046907242e080d410f80291080d000003504518103001101203580c4c605007945d00702c2c0a00d1080d00d0352280070362180100b12820a03418004070802080c4040d0035070503407603c4c1c0501180e520840000c10301f00c100c01c440c941100c0007084031080c118101c40e035410346661008501c481040d000b00c40541d9a6a070084514034034810f90200030240c4100007120230922001007206805021a00400e12158030f946800728240c031001c1d41c1c0540499410031031110180d030f03000403602d00c2d89882e0a0044803c880980c8260031603a9980c08003130031a0408150700c1c56054540f06031a40000890001c509100e90540440d5500109000c02440038281244180c140081009a0320841a000344010750703e151a10b002855003c80748103018180d1403c42d099040c141c0c0104250038254000b1380180641d84c200d6100300f030003001c02da0386450b8000e920941c0c0c401041720030380090094085900c41540d03d04012000502e020240d034040c004000b0750000500242c0e41c04105 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 462517571 1250 462516321 462516337
    0x10b0703020d2d020102091512010914060f030a02042c0f15070c080c0c01030f02120402060f0706020d06030b0f0f0a0b060f132c04021201060e04030519030b06 70
    0xc1d58400c0038602060340240300d1860400d80c0411810600488c0889003c000c4c00c64040120350381d600341c0d90380c8503100c0c00c1d1000c000c0c100410180540001c1c0780342c208a55454601c030b400804886a0381c1603900480c04450110b031104002c0b021015980e82c0d40c0c4049011001500280e10042404085e800078442c3c03190000c00424140000c54404034600c6071151400c07500080d0080300c910307501d102e42001c1e10380c0d858105c00f00070702080c03c08901001e0304400f8401c0c0d6010084020080030740b541c0303950800815a120300480c0754030740c4013440f0220100d103081c4050304400c40200d20004e0510b003141030042244100400840701400a041044030b014401a42d0a4014040c030700c3c045036031800c10001170014044c03041a69254103011950005620381542d01c2000c440c641e440c41d80124144034543d002e5030031004203e504c1c01c5010301c0403400500342480d0040402043d10000500c0c41d45400b03a16605070004d4030280c1c0014408202c071640f500c1c220010b01c0450049040030040300b0400c1c0d011621078025908 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 462518821 1250 462517571 462517637
    0x140a0603020f0d031707030e06160801050f061c0f1a0f0603070917070504050702010b130614010e241b06040215160c12030207091a0d050102070b010b0703020d 70
    0x1000c41c4c030947c002d030861fa402034400419101c40c0e1a103180e44400000c1400501c00000b0708000c000142400c049201000c10350b005000c0610705408009101c1c94403d4600c4440e040d0740d0740d00035091541d00703a03218114602210041d603803841c1c481e100402c0090b6001148030780c0304c0c00c4100b090000081e001003000b022190850004050a41d00380340c203900f42100c6610041d001402c02042140c0e169041d8460b0520319001c0380c00440300703c5a100c0c1541210400d0144032224080106035649646c024605410342d1400100302042e0b40400d07042119005002c0c4404600140002c80c017815401220005641d05a00c000000c059a00d02500061129020317000f80100307103240000c101e102e180021408511098005818540080c0e503060480980102604141c0060203500b101181481c054052410304106429083d000d0b01800401c00088014041040385c40390342c20019000095030228096000f80006030754034bd02c8080508010b41031944d0826514100401072000d081606044000180b00708400e07a = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 462520071 1250 462518821 462518867
    0x1b100b010831060c0f080118020f09030d080105030d0c020d03030203090a0203070f0602070b07110f01090f0902030a060902070b0708070522031b0b0d0f140a0603020f0d03 75
    0x2060340c0442c070469000e4658000800007844003603003007181c181915075035021000700070f07010443d0082c000703004030117900c035242c120f0071440401c54010f030040f41ca030103610901d05100800024a4100400c42c02d0010411240040049180511034241c4030b00c05d5080c12940c3d90001e90008121125500004003459804004915800010401c01e4000c641c0a0100d0b81c11179218111115800418420a001482480e00100341360044130103942c48607500c42944c0301c000c541c510801401c0b82c03c0e90003540c1042003034140095800c0c051801c6c100144048540140d032410040b6150051341e030b2541007107003514010051100007450b040120742c2e0201c25441d2100e5981c440000844440c85000c5454101a44c80e04c010400c204100003924100ca00c40c000390f030170049181c05601d01002082c0302e01d01803020300307106a2041c1722440d0868402510080c000150840c0c655401d10544001500c1410030280d48600610850500400c0d4003103240045450458034040783d83d00624903500701c030000540354485 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 462521321 1250 462520071 462520111
    0x6020c06130e09060402030118030c02212b050703050316050d06091a010c0209040b0601030912020a03020d050c0307020f0f0909030c0606090601080c1e1b100b0108 72
    0x509450001d4503045a007030b00395003081c5121075074a80043c5d405912035441c102184040d64250340b5074804140c3e041c0c880fa400202c941e0200310084043e511070341070300540703900801c00350074090042c842c0403100c034a90501300054000150113a0490112444c1c24004200406004203420034217407503101642c0107952100784c1c000da404031030318000c108121030442e090110204410003290896016000300400480200783e0034801140c6d0a90340ba40007941100d424800309010503082c0b02c03907550100d81070501040780120b0b5610790100e91040c0303d420005802001240c0105503051108542c103116078a0440c0c00d0100e0708401c19102d1003020341c024400d03180c00c207007008141c503000e44085103884c00a003e88401e00d007121409489610040d0100e046000d204001029403410440703c902609040e50390040030354034942d100b900c0d9440250b0701901d01c128241192405200e0f00014950500e131841220003648a008050f807400d1080a851140e0a040c0140400d0341e0342d0164101703902c40e540c0f8a11011721081 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 462522571 1250 462521321 462521347
    0x6061c06050406120201141330140d0305160c06150e1b0406050a0309061407050c0f070b16031107060503040c05010f020a060b180f07030b0a06020c06 66
    0x8940c1c016a00b150074a4000103180d03a900d41100d4800703000380c960030540c81061000e80f80500c600034981d6078040310080280a410b0044198021088100c14200507100e44039451214500a41004403428a600c0f08041c0003682d0500004580d204103080c2801071341402004481c034060444160800c1000f0303500c2c1d00040c8016030700101c0c0102c2a4a04d06140f5a854130002140404215803184402218030400905800b40808440403240e19130355480c200345207000300b103010b00f20050301550780c1a1108480c81500003920100740c00b1b04401e4607416030f141d011180351401c1921103d01c1c0040e43d00000b001f0403101c508201155016600e189010b1140c426910b42900c01d6152000039028500c00c1040c080b440c039030801c00443c0624000d00222840503910001110040200210000140c01030f94101c000142c042e00019409400100580060f41c42640f200f110000100c403d41c0c55404410180004141c0521407001d00b15019507240d500c8a0402c00042c1d51340524903000d6005078000900c901e28011 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 462523821 1250 462522571 462522581
    0x12010b030d1b0209010f21080403030f0c1e020f04020a0207030809030721050c0d02100c02040209120c091303051b1911031c20190f05120306061c 64
    0x507005141301c00319616040001201ca05074080c0c0c43c4001001e2100f5900e40010b40b8602c4c550691022030740d49800e04558048501c0800d203200318040c400b0045981000492192504210100710f041d03051785282640104420f98011420b00b03070040e407040000440c031503130115200b4150390700031070f40b5580c03414440c010074603060781688500c0b0700307400220b0400b84c0c0c4e030034201078954030314019000c80d90080b02c040d0820401c1c05058000035485076542d00d00f40f103528044c046540509000406c01414050b00c0c2d0302290314031415202d000159044000964280d00d041004582c201d0140d8003181c002031001d44e030162a03840784030f0f004070130110704a2210f003d03140c08000d05030200d9101000c810310290503140c2409403d1b1003090782c9204c1d000312494940148801400c1c8140143c0c19942c0081d8000044081c220325034103c403402810340500400c0940488514140740d4883e03204030340014a403d100c0c00e0035070401060070b0744204006003c0041c42029952041a03d1509030b02d010100c0c803124102d0300c400000c0c5 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 462525071 1250 462523821 462523823
    0x1202060f070803090d12110a03050709050907200303070e0918070f180c08011202030f01020f031e04030804060c03090f080a02010f020408031209250512010b030d1b 72
    0x1010000400c82082c50100d803101000150740c48100c800c1c13685a0031403041d1100c142c1c4c1c8943c200414458912102e1007031b04200d400244600b8000c1403da00e4030085a0980c0c4122004400f1601d02c041430b01514060719010178007000803502075411420500f07801441ca0240590541c4074441075804129488920822030790140c1084003201c8804d940c03608104a0070003e8400d1000340740c40380617001c5286981e80607602010a450b91000b103282c0c00c10300210300c809414070050781c26104100580d040e2100c01d10040c40804000e820143d12450803403400c640080c0440c5d1642007900103d402d0000090b00164540e070416400803000c604240c52080450042c40c0c42c3e1805041008141c400c0004d00c85800c0040a003169150300078840e2600340f0b940b14048c0d2040d0302c01c5800603841003159504100030303200b090741c1010040d030580b0546007003e10041c1e410701c810074901c450b00c42c016004201c04d00d04440c0d201440c0540000034001008107500081d11001d01c0d540c11800c0c4040701900030a4814810a02e0703201ca = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 462526321 1250 462525071 462525083
    0x303021b01060305010b1c050706080a0f020f040302041104080309010302161a090607030b0607020904051c03020c0601060801030818030712050102030a0c020a050d0e012114010e011202060f07 84
    0xb80740c0d2420010b002c2c0c911020303403e004124500b5200c18080003010b0107101260040010b042545c076044080301c030740f00024240c003400c69652403059001c0d40e85000038420083d080002a45841c1540100000c4603601050500320200801c0204820310000c0160b490f201400d00b401600d605071014280e8403010100001400841130300301207038130090f08c80780c82401513051100f03c400c10f665406090b41140d20307200d500c2c1c0d400a400d11020005150141d105a4014410f100b951000000d03401103c03440107200c0100c4020030303008103c54400e11010000c0300c1c01045a440c1110f070a500d0342d2203182c00382c40351802c861104600c9064011041c0c40807c40d1100800383e2885c41d882001c0c460a00f10b00075001541d1091000c2c0c100250f98600c148002a280000340e04070000e40940e401c01d0b03c0540701c0c03120005006044c010745500c409200c10048420f20200c40006801280601080300850280d0105801c24034460032102d0046c44036640568450401c581d054174201e6641e84011b00b01034281c042c91300c00401c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 462527571 1250 462526321 462526331
    0x160219050102120a150314010204050a030b0109110307080a02090a051009081b0f060d060e18061311011b0f0501020a02070e0c12061c030306050126040303021b01 71
    0x4012055004120030b1400443d102401d8950040c143c007900c4030210404081801030609201283d03180c00e60a800d080300c100018502a920790200d02000016402590300107000344c01000108414007540e4941582084001e155241c0208041c00c3c5460103421a11400d5001c50012030035160121401c0c0a440b00501c580010800490700030410103071405000540c1c00390030a440d000c0e486032440e0802299000300781d40c0709030345c0d00d001f449010f0700710048481d607158036090300080605c842462a802440b001040222052034103d0a0703240010203005621400d0f0445e00000c04140710014940e815082442c001d80d00e0500082d41c5441c01c0c1415001820f02584000240200081540100480485034081d100704a82d1802c8d80c0c11080c500321034810140300c1c100003500d102e048003000b040e4012001006a0403001e1044402c0c0301e04059840114042565040c044c0829a0020402c0c0c481c21200b500908058000f40303504500002c010308014141034000c1601c02e00020003107241e0380d80010140082103 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 462528821 1250 462527571 462527573
    0x609030105041a0702031215040e2b021f0213090603050109060b09091c0908030f121b0d09170309160512100b0609030f0607080c1206091918050601090212160219 71
    0x40100c3c1e50304038400316410580301d01152f050004c03543e410b803a40c40c40741c09900410351190090181d4040c041007400e06010358000308403d4201d1056a0265009800004003c1200d107446800c6a01c40c6c0c0115118020003020406001000a107048103009040f960001580380c0d10000d44e07040034a50030000590202080448940c4500405401c011461800d81c400b652142240350924500075400300908100400ca24228100590011154140720f0f90310b000106070718920032091078200399000c40c029001072414000041200301004050b2008407000014900c007143c035560b88074000107001e668140c65070305001c01d171341c0c0e0f2805441c802c00d000b0381036900e860000a10203131102000c54241020aa003000465401c0d010740701620f40100174600540d105403600390400010304c00090a00070028030500400214010a00850f103440740107030081b040e00c000600d450742c1003040507040260010700c10700c0002041008100c3d9203800034000110b245084440b88012401e2000410810541044079070f0b00320 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 462530071 1250 462528821 462528853
    0x30914010e100507140a050a0e0d0b160509030a03110106050603090a12020a0f0204020913060902070b130309050d03050705070303120b040905030a05090609030105041a0702031215040e 81
    0x40c2e42000d1003004001c2a940c00d1020b0340c09100c0c540d0422600e44080c031409001900490052003d5002c034108540c1000d906000111030070108042160800001014443c911a02c0500c85091031103900f0b0450502450b080130a640d03854100c00502008040c01051410000c01c2d0702503c0540005400d496881c0f601010983d5036001601044961a1300c0220940d0038910200c0c6030168070f070b400390301c007102e40c2c50b184c00b0880a500810501c0d030f4813a00800e0303030100b0f80304036108100052041520260712002d040c184603c40c5c4c000140907400745010040c040002a600618001c10f94000301c42c200e0701400c0700d08084881d4014000010150320802c070011017815000074a101d03c511005c1c1051051000c2030052105031403181600504a90080c8291001c0301c0c02032000c2c10700424058a018104400080005d00b540c500381e40a80310311018621941640d50010503040d4001542d0000f1454070560101c1c0720340c0c103000144181024040510024070550b142e4008108000303e400c101da0503088046845 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 462531321 1250 462530071 462530083
    0x5061206090106020c0901061d030618010c0206011212200105042112050a09020307030f0201020c0603010b070f0201030209090702330f06041b0203090f0d02060a030914010e 76
    0x1051180c000070000050180c40060001c80c00e100251041c07040380d180000c01d8034880d40551980203440041e00109030a504c00b0803000d071181441c2c000c181a80c02128010f5421540217225000440d04010f0042c4010450726403d0210380340c3c448041004030528020460740001a05040c001e1420741501178503915505411035405035001d18443d10030880000d100d050f01c10840344181010800340c1000310540e11440c0d000e40d9011102200100d511b16543c0c7c006418031985400c204d541201d5200d904c0107550341044840701c003030310030384140e855541044039102c4140189600189102d400541d41806c59200e60152401e00780302518045035814882c030013948500003542e91800d40801c14006e800e4448071044070755070310b41c00c0041c0344040d9203514410102c5403034010085ca8010b5241c0c2003004200745140d210308804180f0364007541d1122306110800507400b00c44680340b80b00718008901103001d42d440d00121001e11026041c00686035115290071240c910364030016520350b5190101c5801526404544 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 462532571 1250 462531321 462531331
    0x50d1a0106031506030515090a110f070b0703050903070f08041d07030b06090112090c0f03030503010f06021516030f230f04030206180a1205071406040305180a050612 73
    0x259003958840200b242143c000301d5440c0f0100141e00210300b01c0741001c08823540c0101100b00c0c0840d941704222070041090f1f00c485041c0c02248000941407090190280205070003504a280c1802241001b58119a0702c0c0606507001c1c0c08404803107282420424504101c8006000168a901510317107a41c40c4030991030800c03603130103000c681070007082c0b4401c8c980f141c129000904140c460240610b400c00c980c500a02c02030404a0309440800408503105202c0b62013a802984030399a002e5480d0b0410300c0d005011350aa40c040e6042d980000c80c3c4004511020424035402540303a16410302080d240f200031400307008140ba4549480b07142806002c80715841e0195492410701400003c00c40b51102c0b00d07101e6400c00c0c1140c010b00143c0041010401408120551840600c0e9100849000c2c0c402500c9003048005c526124074042840001c075032041103107001d403010308800c04201038100303441c140c0c0300a0007900c156000c1551007800203005403e00c3c0e0f944030000004c1c00001d055240c40c0d12400710b900908000c1030790 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 462533821 1250 462532571 462532601
    0x20c09090102120106091d06130b0102010905030c2803021e030702043303080403081e0408150c07050706120213030f021c12030906090b1f060504050604050d1a010603 73
    0x6081100aa0140c7e5514016603001c4c002d0440030070307a0440300c1700030003194510504554135110480c0100b9030400140c039403000e100b00038000d02c00c03004000c1d0210078114440f481160b0351600380e041c003181d00413401704c0750204803108013030800035039a4020341544201c81d0000e40c010300e04400c20300c0c03404070070201c400f020085c0d02c92140d02500c01012a8a0f80f0700d0341c4002000051b0800062000a01803800b420001c103110320030380070700c12080111060581054100d0b80c800d9102c02c4440c190304096a1420fa000103004043e035207003c09640701e55441e4034450092400388480203540c005090816412260620b11120b160480c01c0e4403403070403a14410a55200343d00c51581d4280b216110440040d110720000e031304c90105410300d911494290040c281070390003503640640e0f50001c0c0004c40c00c0841c0075849280d4408040004d05002d48810520460035000a402c101c0140800c3c0040d031a203808039010381d0012902d201c3c5651440c5070804000c144200c00070451507680c0c000151145c1c040d080350307201e441c0b450303 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 462535071 1250 462533821 462533849
    0xa030b0a05103f14030705011a030c04090c05030a030e03120405100e010c0b04060b03100b101206081207060e0a20040e060c07020109080607020c0909010212010609 72
    0x29514141600001410f2810950f4180c0312070b05100707403100d207621410189000300c540c0c0c650301e445030607410400380f21608141d000040e002003000420b2103462120450581e10804074400c0c800420366440303a003c003650203282c0e22040c0c1d405100e110071098004140050840c0c0f400b0240b842e00410715801c50394014020710540c8014030a4100c07090503141940d001401c120780310003910070206c0742c035464515441d06202501000501151207074420301d10450059001140d103108031340034036140c000c649108820051070020120526901d800512002ca02c1500c0e103000707454059808400140641c0d88002c0107842074400e00c1c010314400d0805801000e001e61001c010340e030b5074a00400e40f00c951205005265203034628801e42c03d4140700c0000320341802d0103000054050b1980680d24a0403130180c4510003110790110b051701c02c5680c09000e040113032018901a2000d400c0544002e5520314104e00720620174000c1900180c0c01030000d6050718114042200313501c07034550759900d000d48988042c0c001d0904020000c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 462536321 1250 462535071 462535079
    0x21090106050f09061f090801020a0f120504051f0b040e0609060c03010806010b160f080405040b0303040503030f0f07050601350c060f090a03060f05070f02060a0b0a030b0a0510 77
    0x600501442008050040b01c4d40e0360301710441010b103090350a00c400510004020204242100340302501e4440040d4a50f03c04ea966130002c09080e00200c43c00701d9400301e082900b00b00000308080340c91069403a0301c40c05208860340004a4601403c403501c0b01c60341241c07030005610140c00000964500070401c04069130029110107178030f4011480240280c0200383c0c40b040040089c8800003008101c01441c004e040d05090310b850b034610308140c130000415558810042024011490940725454800d5405c0340110702c2e041c03421012945034020b28130311103c4404081541d035000712201c01101c0b00070381e00c4010b9403c03e60f109c58003241000e405004054a116000449002c02030000c4554880316040f00020003003a100d071401c020441e0700409409641181c2030110042c1503d074540c25101841c031942d80484c0310000702070703040c5c215040200020200111000c4080005802044098001a640300007040e51010b4502282008406500c010003402c9410300300102c811095001902500701c880b040030481da03803 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 462537571 1250 462536321 462536329
    0x40b0106020d1706010c0605190f02160b070318150b0a08150c0d0c020708011103040c03080d020403120305040b01053001060e040311070815010b21090106050f 70
    0x30424560020910881420140500a0110f141c0c40b01052610303000307441c1c15030ba48405660f02504c4860010050b804862111001c9000b200d6400d04009000c60411001b4801d00f26070700030984000d40507114290106245901c690003001c10405400d115100c402030f180703808030000c0341124190441b9442c00c1070590320307841c1c04450380c004c58128200a0540f8003410700b51150020000c0e0600403540d4040010350001c2416001d0030904c21210703006816030078a0b0100143c02d40c0c0c9015070f05101940200304100000c0e80501000c02520f80180e855500d503c2c090840c00004c1c42141c1002e41890100754004c2d0080d98990801c1788200d01c52a8007010b40d990700e40904c0b8206503d400d000140340612091042900f800440712180c00300c031a000072800c0b541e681c1c18514411800d54081d00000c801072014054001c08020a000400400b002802401e64141d08000d9201041c02016100000012004a0340046404014070820720303500075104c0d4200078190500070211449410300540c0201c3c021101032030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 462538821 1250 462537571 462537583
    0x180406031b050409150c030b031c090509040819020f01050a05040201170103020604090f0b120a0b1f060c111e0a08030309030a080405210a03060b070c060807090b0c06040b010602 78
    0x16000c6040c10300b94443c00c04400103040001002000c062360f0b200d100342075541c100910a240b81038485c43d4204803880b810300411100300e5401150040c803001044c0b00018010b6000c80b85040c0d8490103280824504410803414110703d181300c0d44c05076081005120305064541d100b507021303501c02d0f21442c0c8d90030030204521100a42c01d100c0a54094028002001703000d009400584039004414400940b42135480009402010305414030400c1e41d000d2040b02d020022804d111680100074180700f038180240d481c51300f003424400c41c001c101c2081040b00090f0b040040d46800d4502c0002c1c02000c0c000c0b0038400d40d10003007400302041c0f4401d02c527001041001440c420040b0459010f034103102c0c007840c0b603c0c1d0281405e690300f510161003220284244c2c1e0340c80000340f401c0030701a0f46d0014007c03a4a540c440c51424020261001a00260f4000008201d43d10008030650460340031036003142042c801d6640c1391501910301c0c5d580c9510401188a002802060301031001c14480c1c815440303906203e0350360362200310881c4d40700303 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 462540071 1250 462538821 462538823
    0x8090f040c021c0e04090521160213020d051f0909170306030f1b0a090e0c10110106171902090c031b0a05070b070e060f180406031b050409 61
    0x41c000745911881981180a0702540030034a01346880d2400c01c0d40d02080495034040d2058a081d00945421042c45108030044200f0250780c40c40e01741004d0f0701070280c000c85100400000e00c1a0b2500054185000007038061b0382500c0c0703c640b41000a894021803421010800c4900e50018a500040c04505410345109a4009030b0300180c841c0754540b64140030828552000d80029414819544505c607490420440082e50309400c1c04400ba031540c8850503c0b42c501da035500a014100d0070154503001100c0c0000b19041c44e984c04892401203016054416074070034042020000131542051400f048040554030801803000d00070084485d260108490bc00c141d60b0000c000a52098911003c070301842c1c0300740c000c0c40e00030748009a25081c0c40c80382c021514195000030301820200d00081114803c1c8403686070003030303840860307400c2000d40f210241c00040c15902c03d4218480030040003150b05e81340c6c000244003036003000e0720180c0100305540c2c90781010814031901c100701e001101e000d5034012070300b4149070103070080746 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 462541321 1250 462540071 462540073
    0x1106060a0f060c0203070509100e010509370513051b0901180209040c0324180207050c090106030501180b2b02130c030b0f090105150f040308090f040c02 67
    0x103079061a03411107052005402c2030340e1500c160f400208440e0380d0304040038000c052003031001e00424502a4040f8108d54141d1146120300400c034100001c3e0020b401130306103d0307440301010240360b0b00c5c150806d0314844c2d203004c2d982c4c0000d0320308003c211401090111003c0041d000c2c0044488129007002a40c889034541d0341d0540d0041150001009aa00d05c40c5102a1040e040d22002d410540810003007800c0710145c0009000198071400054800010070482d010601c4103815004019401d00c040c06152175003000100c181654006568001c0c410180190802c4010041403001d5559581d1001409082c080c0203601c49006000c0c10201010b000d485103043e0500050400c00040403065070030941c030100c02c0000311526551207962001a501e02c0100c40004d100e0641c00200e1903401c0d800203040f901c20040440c041c880c603480c1800180e407101202411601c04a41106030560018412481e0340a6030701d0440010364081400b004002c1d544000d13185042d4261508215000004100419980b020000c4805 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 462542571 1250 462541321 462541349
    0x1e0315041a0d0203070b0f0304110103051b130302130f060608010608061003020d0c02161208040909080909040503040614120414010e070e040b060409120302090d0804061106060a 78
    0x12505001d0600d02d0498001030549454903600d00010005500440e0031074507040c2c0c00401c000801105030804d054a24003860200103070315158040409170b01803030b01200c0c20241c0124021940104044603a009141d01804129400c0004450322019003507070781e42d294010342406808600702d84542c1c00c81e03040b113415540301011511200c003808007500c15002d410302016001c2190310b005141d68010074006150943c020401c800c0403080c003940500940d0881e47c050450016150040361980003554181c035080c610002c0e2041440c40c01070050311074240c160342c01c88081c00400050000110281c8219100764031040141408480c1000d07117840760900d2101500d8000000c82d010410b01a004c3c00c1c41a141000012800d08014a942c5089505d5125528000c18901084104020841c015402590036a820b01152145944024111b400c00c201c05c400c05901050380c0c80d05d60b0305c1560b418000381e086850030365203948981004281c40201c0345412018818000410860700b0811840c6045851900790b10103 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 462543821 1250 462542571 462542621
    0x1009060203100b16030e0102010212010e190e030d0e0a12080915072114010f06170702070513060f0e04030f020a0b011e050301111b030705071a1e031504 67
    0x40300c501b000340d40c604540d070130f114166503001501e4034680070304408a9804403a1502030701900901005900103816a42044807034000280000107507a0091503c02000c10360720711100c00540380c103050107009440ca00a11001507001508011480e0080114105484125810081c1d0140c0d82406440c00000540074035050a508110b007100204014940c1d01e000c1400003450301000304446082c1c005e01c284600b00e1108221080d04484504170800416070b002006c0c0c5017203107001c1e4a80c0318501c541c03401000c01d40d000f10080040f66010780c024201501c02a000d03251566090f01903007404440c104d0104520103141c8000c0e9000181116a950f840104024107a0038803002003d0340c000e2101d031024030b42034100046141da07420301500c400002c00812150700c1d5480f0581c01041401065500000307a0410803090001c41c4000c07515105840c1014022180c404081c04105601d12804001c00041c5014501e8880381200c0c0b107004500a920345801c50100e648444200405c8070040030300e0561640d01c016941c5 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 462545071 1250 462543821 462543827
    0x30702090a090f030807110705060a260915130b06100201020705060903030403170106050304030806010e030a030807030c03140a090305070516080d0c0506060904051009060203100b1603 81
    0x254090781c00100800c0030401c40e59080c1866050010403800f0500110070400c5440d8016101078031000b40e0741c001c2060510b4940804c0c5035202d80742c01e0004004000c01201d13050002c0e001e00142c41062610301d10000c2c5054184291241700241d0a030304107090150208142d00704140711641895082400c0c142180c4400081000407170b030540c100c03415550240030f00008500d0500207223100e80488005595640382a240c002e14421010b07044001c2e0190385801400480c1e88803060325442541350400b244c82d5100c0340c0c0180c9a0003031710b41c60f41e81d061003942d20035002c040c0d100b9a15801008562070907c45040940070a5003610300e0058030b100f00900c0cfd400000d05011064103d042040d00a0030410b01d45000d42c0c441c075040101c9650841d0142e1151201080034000c00c00000701644454903026400020f10b5807480e0300da0b072010300094030620610001c18240300082c40380700820420811304000d4041c031850084040d400881d02d030207400d040d2000c00500d4010710030444034582c1200d60300c10042041c954042e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 462546321 1250 462545071 462545089
    0x120501081f06050301180c0801050403120b011724030c0d0201032c0a0c060e09010608070207090213060305011a03060904080d020703110f010615120908160c0e04020102030702 77
    0x1e05003180c03541d0002aa42c0c8081c4220b140c03400f00321140d07402001603070510b0300c404c0040303900c1512248e24150400002c00e9106408800c100d200750070108414103607500483d80b030340001c2c031803d00504071030b0180003d07024900d5030303101410303c00c82202d48654280b0040503200d400403450300741c001e450325000c200190310a078030615980d1204080207400741202090344007150803031074084400d50b000740c14201c02d101e0311150440040c1102d2420785140701048001c541010010f214801c1800300207004038004a001340411000303408502c80071500e440404400f014200454441d000c04a481c0000119140040c0c250490303d11060103d000e25513225441444802c0c070000340196031644044c0203c4129001c180010000f0b02d0190740e07007100c1161000d06030390420002006500301c9a00d0074008010309030720f903181e00401c50700a0410f802034502250141000c0d14020340000e080940c00240c05000000c01c01d0707241c81c00d41c00790f101c1c00707005600c4403881132401e017007920045c4c05170380f00780464801031900c4440 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 462547571 1250 462546321 462546373
    0x2a0201110d020724090212010b0a05040c050c1615110a08030711010f0f05010e090705041d0105092d12130503010c030c08061005070b0406090b040b010612050108 71
    0x261071001d51200c07546400944004c0c45080032940c68004090552400b416a1b0048030420002003103d00806800107101c400640706a0340076944030301100040b03900810649000c0ca28010944601e06516a001c0c01500c030103000d80280442940b0181101d01e101e210729400174200703a802454031035140d80301c80d22540c200815003010401c0301003000004080a0040c2c4031070024041012482d01d90012010080d61016001150a092030b00708000c0286400036011084440a89000030fa488400b10307203242080007503461004e05c6d030901040c409030a40010348400c0d20388002c5440b040c0040310034098900070820007003400440d030011042c250403c0944000342042d1400115004020ba80d400110342500c01c7c00d002e5401103aa00d4018280700e9030022009c0e58007900454101c48080c41060000d4482d00402ca005025240d84500190070818961b1006611940000111495240c1403412802d0762909008030400034203400e0111840c00800d0181d68140d071082d60182405a642007440c06880300c0da0b803d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 462548821 1250 462547571 462547583
    0xb091506030f0405070f030c0602120304020102030d05060303040b0f090f06190e0f04050f0a0501060e0a0b07061d0609012906072a05040e071401140d2a0201110d0207 73
    0x10300c0300606d980c90740c021442aa9401d400c28038000019041c4030700c03c00d040d00ca0744010410400140e9002c0116501540d42c514000340541701e06012915501841c0c115080301440020040034a081042c09040241c10803141307809a07589080a0040c01d000e064a0300050b0030781c0c4408180c515000e04040442c405024020101c003110b1080082e050310825074841c581801c50340709006030071025002e5030f405003105040147d20304025501080e002d201c240b00d0382c10006002b248240802c8000d400103941c01007042c08803502c01c01c404054544440094451706c2056203080d151080c5107010240800c40590074090310603641d82500c0a0000c1e80d40b1108084901c01200c180004045d000e00d101020403085800350344408900301020300084a0040c030200d641030340054001c0050f1400c071211080e209400707180840390552250b21004e068000d0760061204107003400000360305090310380ca14407680490000c00c0e82c401c42c48090181c0c220b0b06101a0050100820071a0019040641d0020040a03100311 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 462550071 1250 462548821 462548833
    0xa0210051639030825050a050a0306050607080306090703060305060c09010c020a090c17010b0f1612020d08011502070e06010e0405180708060115121e0b091506030f0405 74
    0xd122080035401c01c1000b2400300704c61030144003003140c581400e40782c2604001d600c0907074000c00e5000504603004140d40d0f43e0800c040010b17010900c40c0711b0b401801c0201400340a25481d960309140987c41500200d5032203004404100005131140c0c428003c040490350408050070064030755410400c21a44031007100d60620040240f0080140c6547d0329603802401550400103d01d41006401456928407142030380e00e03083e124005000c0707004580c00700c6581d2100594807580e6040704032010202c0328544034015041e058000340d0f0000b000d8022554004400e01031761148416a00c030100a00c1d01c80c4502c2c0b0b05001607104d81c005001800b4003085482c1c00c00e0050415420851a071000207080d24801c6540e100168a070500d2031601c11002c01840c80507211035409401c4940c18007032916020140c100c2c0c20001c2102c060000041e1502c85e90001140d0303080308040340144c6100600e0f2502800c2c5c2e0f10b100e94021542000011018000001c00042d0640020703c050314680341c01c241b908100201402c02c0d81c01d40155 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 462551321 1250 462550071 462550157
    0x180e041a010b09061305131a1005030f1302130203010608161e03110c0f06090c100c1511090310110708030402040209030102040303200606090f0a0b060a02100516 71
    0x107c401c0b400484581d000700d0302d00800c80b8210784242d0110300c01070103696031f04201c029a540040580b980b00c84a61480d513a2540c1e01d550040d000031140002a4020100c190a004c80d217910350000d5043e02c0041d00c4155003529803c080c10b680c1800401c1000001d20200b0a1f11120944940394481c9040c6519010402c1110207008904030f5003c41e403400b0256200041210031030381d00b03100d5140c3c01210400941202c248078030104816104c0d08000700c003080140700700f40301001141c0341142600c0722881d03401c00041110740300905c681d500c40c5400314442d220300504e0303404a800e180110100008040806820003105954001c1c45400251040ba8426003d001801440e1003d1011304000c40c043c0e40c5501c016100007a0f45804000b080440f0500368000b0010081d00b91640d29445412286882e045d0740745980306580351004040d440c010039405440044c01c10ba03442da000405200260f880c071801c20168544030722a407411040280d0020201d058108401145030b1043d100010302070618254956040c10 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 462552571 1250 462551321 462551329
    0x1203011401020f160303270612111305011b110f03070b030403051309020a02071a0c0a050f2806020a02120a05070b062e180e041a010b09061305 63
    0x10b07900084c68050f0f10203000c1044c1640843c00701c1c40c0c4005c3c0e401c200400c0151210600d40c10354a0f0242102340401080c0c07008001c543c40e8410210240c143c2c41e09034480c802c007000d0324a51074480c8555030000c0c2c00c4120a40915a4080502048581c0b00b0140400041001c0074030081c1070f490210603a25006138032001501500d500300a601c9135100c0e50b115540c0d118a182c101081c8400c507008041d000d441445840502030b0001481c1003500c0ca18604c80a100c034059650800e2841040312050b001d001d00032805041000020312031441e88426416203244188040c0c2c0c10b410080c5041101e0f40b5103078594031040c04a030959008040f5640548140ca207158920081e11070031390b001210b0480001d50000b8110148503480c10040d40140c5c0490302d4520400c1c2c8000710786d0102014400a280902090220000c494002c83c1c0c10f280c144402414404c1e4186d031129951b14003032049a06403240318400c90582101d148a01c0d07400e050360380340380752941403c0c2c40405000840c0c0000300d501c600000312040104503561 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 462553821 1250 462552571 462552583
    0x2030f220b070e30030c100f021903290108060d03050f1c0b010906080f181014071b17040b270901060909051b03040b0702060106021203011401020f 65
    0x1d80701600d5814508841303400d4480320030300056103181c205228200b1030b1500070a025109146c940404282102c0c4d21082e030f07000740b151002700401040c450040d00d00303450b0560130445202140040003900c140300c08045c031480c05542004280025103c0e4001025450100d01c1158001d01030b1801508190b401140c14100380e02401c00c692030004900505405000c082c0514104d111080c603003042418541070380a048110040d124601c0c400d000c10000741308901c064508845948507804503030364214101d164500805904a008072100783d10000034403100d018008e420f03900150030b0341c6c0c0ca60312901521078003850703840031030f070304650a8042000048070000300025041070402c2c1c215001083c1c4603440c1a100040ca0030300464004c00100d00104001c50300200c0600c11030f12010404501550303084184624400c0e038101032400e01d6004018881031110958050388905415000c4032043d0742c0750b00e4140d80e504e07805030b10f180c0c40210400c01808400c0520095000c4900d040c01114800c0c00e607810a642082c3d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 462555071 1250 462553821 462553849
    0xe060d081c060618080a08030109020901020f1606030b0a050306010611010612030503090f010c090b0a170f06030f0c0f010c050115090f0c05130905090a0c0902030f220b070e 76
    0x340040d0f83c04c1c0c40e02c0400b0f41065006103031400041452110980d20901c9a0105204000c1869404116040d45900900c603c2c0b11908c1c000041d6090b0440003000100c0018841c02120300091801103415201d080800c1000140c40d4011300502180e0b281600071124190901313121035040d500c81400180100c410301d85d00e64200c2c406d442d296141d14014403103a1402e040f549076040c05a040172a0b103d0a560004514010340c0c001c50000c80d80e58210100544070700403074024002d03449020201b040582c620000007140642c0088090b50075801000740030301d80c0c3d24641d807071480e440380c0e01d00c40140c03c0c0d60042c007084207814820000030401c0a14074184880212145e07000c003c0640d10f8000840040c00709200d8051001a2814017900b0400c0f40c24000240c00c1e0907001d600d40c1d5550328030204603280000c004800000394440580d6904644404024019400c140e5998942c880404042040030b1004d5242200542c02d240d800c000c0d43c0090f4071039546d87c0002030f20000a00488080e090029181c00b22075040030 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 462556321 1250 462555071 462555077
    0x10203010302090a180803100314070614040602280203030703020606040509012d2009031c05181c0503070c051008070f1e020a06060e060d081c0606 65
    0xe40c0355005000ca281d20041508014500d400a030510b0a0742d10344014400075003103c4241d450fa030301e094101c00920f4081d040079244465202500d0600d65002031180203948881e62220010518945662030074060f500514000d0f800603030396103a240001d415113200ca80148036410742d84030002e4022900f168172010040d00141c00c48010020b281c01c2c5801015008032440008108000c0451030b003c86000f524251402100311601000c4000c910301c1e000f00081240820b12035003600c0500c6480031031540024006400b90103004a05241c07100f9030840d0507800c00e0315455891900b0392003203006154024104846600c4510402d009070380d5182016000e039200e21480045694107510304010b09801525400540304000b51440000340a0340715066a400c40e12034280402e908240d10415152032000c1d030181e8140c0d076804121160071a90000d04090040d014020422502e41c44501040004d1302c201c80075500004500c11080003d08280700410b210341c3c280d13042011603c01c0d04440e00980e06650311200c00 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 462557571 1250 462556321 462556327
    0x1605070215120f13080c100e030307021203010b09102304090e0a11100c0f030801060f0c03140703050906040e1b0307091710050f07030f0e030405040504230102 70
    0xb80014102950080702c4040040203625000400f000c109000100082039503d02140400c0820410006400180d400300e00600c070104461048503a00c3c0c100300c580800501c80c0320040305600070f41c030040b81d0680d01200030b800c1c5002c142405000905c100e41120302e08000d0401440d4000d110011028401081e120f41c0c0541c1e0340e840c0034620410380f90740c18032410302c42d0005103880d800100303218012602c00c142503511028004100380300340e0748410641c6c001381c42c02c04a85480020107034842119410b980040c1c030b620300d6030b040c03c1d00210303100c848559004020510302e20240b8821460761015040840c804c1c41c04910301880000841d441e0740141e4000220081d142042c003010351064a940340240e0340700386140c0e05501d0524402440006940325095080f44461140c2a600c001401a038001e2240c1e14414042c604102a500d82d40380000c4400400091805603410041030140c00b58964007040c1400460906040000300700082601034000c4880080304041040d0842000001032904a58800010b072 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 462558821 1250 462557571 462557587
    0x13050c090a14060405210a0305090108090d0f031521050c0102031318090209070c020a080d080a0b01030e0f0105011806030f0f05010e030408060417030408031605070215 74
    0x650321503402c5040304049520880030070352610020b50382118412101c1d020005030000560340000c00340c03100c5001c5070150b035204205241d0407030001e200442d000e9950600c41d540725001e41d0344460501c480c00340042e5440c440c19244601c43c1e004403400d100c4900c400b03610107958414940107182180c2c0b100210708031040038141400b00500142c000410b082c000f0754030700303020440503403022820341c0603048502103a281e484460074030b15031021001503030181c200e1602c0d040680c8064034550400b40201c0c42910b10080201d101d00011a008480103441e4603083c0c81900d91090f1a800741c2400ca0143d8105070b07031036024080500302000071a1900420328000a1154103113000351003050460f100444415003440010000640101c0040c42c00c560004021800e01105240407805004c8010000200c0d04c0b02107008201d2000200307000b401740b44a00720964191060b114410b449001c101c074080c0c25201c043c8009030080c0d1408401c00c030400294030b441c034035126030340d800250840c84d01d4440b403c0d41c910115500b0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 462560071 1250 462558821 462558829
    0x6111b070e070e060412080405060a170105010201180b181c0e04020f07030804020a05090a0f0b03011a1203120a050106020618031c020f030112050616020d050913050c09 74
    0x50b0040d02914001d54000e08070800700c2c4251290f881152038040440c040d031070038440c3c000c0569000c0e190040c22151350340000c0340d000303144d549840100201c02c105c1030b000141c0c5600501c113040313a0319810403a002000c940c40c1c403007060039030004010b07030082d207000030702010f403c002031144031003911030426071308480c600c4101c0c000d101070140b803c02e0780101d00c10031094075000403a034142c604071545450600380541e1180b0101b20034010a61007590090548070030701100c050542c0090320b80c818885001c000d1055010105820307990101d440b0b04a0301c0000390007000c06d0400c0c0150004008403441204e2034202c840b41c1c4c88000d96012504444a5903582e070050081c154140171868100d2900740d6046440c1441d00b414036200e114a021400250300601060b0950307001a4066400e03042ca442006c9440f50b03560307109158030120749207048030a4061480040d0341c003043c607008182013004580c010400050001c1c0b003542e407a41310051280d4880c03000181c001203200c80d401010712a1032542205611307502210144 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 462561321 1250 462560071 462560099
    0x17150109050106080105151303031119020a030b07170f06040b120714040e0a0803090c0915060307050f1303020a050604080c060d0b09160801090b060706111b07 70
    0x10346410303060100401207140e01c441403a040d20400c40303502c04a0104c94021510754450400e90b4410b44141840001c103050700401021071442018007034038003a40c001d24244d001c0403c9080001d5010000580901c041407030b10300d100ba40140d02d03003400f05064605450001d40f0300710854041c0042010314081000ba800c00703001d440c0d9030a0341a500c3d807201008180200f42c582c10680030303e0f002a08030740b10141c001e40c0c0700d070488504140300009841c6403015908000070076610403500c00f1030714440c3d15030342001420240c44803480b0740b61905c40000310040c5002000300ea5807029000004110b024407178592400b41c24001040f000c0303000c80c52815543c0c03644c810302400e0720300e81e80484e109603000d000c03c00610350081086646050122031180c0c0d2641c105100c04010550030102942100f9240f0800800640d8643d40700d90329032030f0b61030f241020780ea12082842924400c24032a034010200703000040008280c2e0300000310650030400382070b013072440244020382038040031502c50965600031941040000c00c243c200c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 462562571 1250 462561321 462561329
    0xa0e04020a15080a2d060e010e06100c0c0906140109050306160e0d0605040b0114060412030810030b070f081f030b07020f0d0f0e010c030206150406171501 68
    0x800608900c40b07040034180301e4000b4202000b41e61180a503501e00c5509414152404a2208070001d142002441e488000c1c080c0d402019070030001040041038141601d07080c6403140f5401000001c00c070900b80c4045459540146085942c441c0c14500401c1d00c2c003541c055080540700c044640490440400001400c080d06540400e021390403041c184001c4103070010f03542e10a4100d50405021807811840480d04c03440d803010000e444e00e0300d1720091204100c001c1800750704039221520b59680401c84402045801e2155204840501e2010701e0703020300007806507003100c0e4048101c04800c0d03696652038442000d07035002115080c0000e80e00d0300080c0081c1c0d8002c141640c2000281500d006043c80c15007548544a03014000a0400e4001400045031180700b040700800d040c3c003020070390700143e866260240071041840307020408a001007a0040e500d510441d10451400e805500134a10b54a0b01100208a000500d11b090f420940340c032400f055401580d0041c0569042c018000d10020704003141850100c08180c00c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 462563821 1250 462562571 462562589
    0x14090703090c120201050c013902030703030b03100f020409180209070309080f04080c0a050102031207030b010903021206011a2d04260607020102040501120b040b0a0e04020a 76
    0x65041c010030071000c03514003a01c1008149607409011400165070500032814200e40941c240500c4296260003102c009000c48160400000603130400c5012001240c004943d420041c0c0c030030700440c0e020034426001842e8078107000c0d05135824051004100310540390341050490034250001400c0101d0083e80c8545850500250800000013200b41d0019030700d80c0e00a00303841e0416403195880e9042c0074825003140c0d04042c01c0a10103680c0c40e9540724058803102e02401052180450800000300781d4004400c17518201720802179040aa95290429030040c00300b590f178203042140c03050000c401615140d00c0700c069940060010921985459841c0b954100d00000c812841142400341849000901195002d560f0503409280c2d2062010041c6012901a90740080221161800700e0242010400201e079403001800d42616042d40d41c2500990a0344503900c40c09000a021000c0b5000101ca00c2d400318003d960300400208140303000800140e8024140d03001000d82c45914003e000451410001e08801008088 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 462565071 1250 462563821 462563831
    0x705090d050a140f1204050603070201021c230c070b0711030a03140709031e060906142712091824090720070801290301090b04080d0609020414090703 66
    0x1e012000c21b00403441410f001d504080040303100c0b45e0003901541c41e00314500c04840000a00c0702e5125015198a82e0340d400000551010354100b80c0601210f01c0c42070541c81655440c010240e99400400d2100a10300c404001c6c2c500f5608240a105100500c540304040d80c0220b00501348082115906101030f0103c005e20442590400004058420303203401d81790700100d05010484641004406070480d4a0000c0c12203250100540d031b60f210892840d40240390f07044150014500601000b4000318a00c000c000c003e80c03005090340810280b010013000d4500c000f901000001d402511340c41503080707080d507201540c0941c10300310102c80801e5203000007486004868060242c2400c040240c848a0030f10301040ba0406801803030180380d81c00f003020000800e81e6100800803158080481902c030b208081c01d00c4035040d1607015000f02803505004114000d40c104d2400651a2510390341e08286078088d00d0304821544c2c03210f070000349071881c2c1c0c80a0001007030040c401030b100744000030400c01d852500030082d00500d0310304 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 462566321 1250 462565071 462565093
    0x1309050c031606050f090406090c020c0a0e0a091406090c01180303170c1308072d050103020304050f1903031d0a080918040606140a0b030705090d050a140f 68
    0xa44520b008a0700c039814015620200003840407200e02c034030030304140c0040c01c0280010f42070340b4640c46205841c2041e429a80c0310804a820811040320a1041c04414a510300104407905100e41c05041214840c3c025041a10024804c1d5401d1038412034012445070840c0c2207882440d60010556441c07005100c84040615045645c090007040c1038090540c3d940c2142c00000d0451600441102d042c80b0411404100d10f17030f61440e005541c3e82280c0148614440c142c00391848514030011040c2c100c6031510f0440100c00d0401004400941004000f59098403d01090071b81d50203042c803030760300c0511320761614214060ba43c1c2005029926207288191f070901e218044009200000703d408035403150300030505513a03429210005040d511408403460150086802031204100e21940040110381c0711001c1100911958820083c85404c513115041d04608200005103c06211714010007021000034040d04010141d82c6500c1c1ca400c0307003508102d520044101074401000380130000e150400144c0b000512900f076030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 462567571 1250 462566321 462566353
    0x50c060a0206070c020a050d200307050a050d06140a02030a110306030a11060f0f040503100b10080615031303030f0b1507050c030f0a0308060d0b060609030c1309050c03 74
    0x300903c00c008102d503103000b01c811559443c0c5064000c040c014588150701c502070405c440c07140d040016030a4600c0380d2017640075035410003107012000c50320b004198628031840c000038407440c584000f50441e5070790765400d818442d140340d007444c03140198041030005032a03251036801481207030340e07081050921400c140200080340e580010a00750040d84905610207142110b00401c0c11401200c0074110024800304445089100141c054012280202c08468005511108602c1240d52504170560408401461207070f426004e881b1982e00400c01030407010502081c60031440017500103554203500c148481000c501419410300a040c10749405440406c01c2240f60340014400301c01d900480314580d140491110140013090014221030500074003900c0d645071243d0a1941c6805400000710082a241008161541001c003c3c900c500380e440b0254030488e0329400c04105c0c103900401c0c0c80301d0740f51140a00c00c2c071894603401225020f08130521800b05000c4000d160140c140405058118025442303d000e082628107 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 462568821 1250 462567571 462567583
    0xa051f03051b030103150f05010801090b011a120c070203030a0e18070f0c03030603200907050a053c0d06060c0b06040b120d0f030e0a03020d03050a0f060f03050c060a02 74
    0x141c01030b016546d602418080700090810100b4800038a80b5020001401c8801074008202ca54411058841070780e80f20080d5074070034414040f000c0790848092000d80e1a00450144003504a07901d189a542021400d078000707031465104c075418100081d0200143d14490a014600d86100246100e46209078501554002d0002c040d0740404030410a16a18140034917000307074009005940c103d940000000c11303640c4402e002101a151103402100f144000450061051080d070b207090b4080d641e107070318008a056584603008032245d00640e0030700041c1d81c50070100c26402806501131105402c22034903100d022034481d003140e0031544080180300400503000e0000c0c242c10a403030340c004d50489000980c4c8840102140440b000c1c4141d403083d901c661415003040d660400401c000d1040700e560700344400880341403429201c03803020400401503804a1031221013a4007079084140c2c4203e1182e000501d482008042c1000d0381d04a41c00b8911090500c00240140041405a4542c440082c3e401ca450440f034204020760f119 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 462570071 1250 462568821 462568823
    0x409140a0c0c02040c05090d0804140604140907050c0f0a060b190302041a0603070c1b0506030f091c1701050103020a0c0b270105091513110a051f03051b030103 70
    0x341d900c44204520300d001c0c6d4143c8240c0103000d0050342e034284040c5000200741c0c0c8140640d485403c0c603404044690329000044409541e000e41c0b8030301c2c242100400748a800b01000d0001800e0003018000214130120401c15084c24004a000500c4c60f18089c1c102801150400555580110310360018400380303140b000015800c5a5051701c0c0090601d512000d080304c1222848010350b4445000010300a90382c2d4000b608100d00c078041c00210710a02040b2101207410501449407941200061000601c0d4100084030558000402001d03580200803a440c112610030744080d88001181821405030107031568210075902406007802d0441c40d1900c01c60019080300395240b0000c05511544000500406850061100c60404034100c104a400c00e480e03c03038041d01d006c4410b03081a115107146000b081c06402011800742c00f500d40111004070719510740002400390784040c3d50b04040303c56800a01034440f8108100c19083c00440f03288004c80c00000181505d030090607009001a01d1000c200d034000381141200e04403 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 462571321 1250 462570071 462570079
    0x1106090d0c15020307050a0e030d0f0507020a0807181a030325020306190b010201140a0f0e0d080717060a0608090c040609020a0f082a0408030409140a0c0c02 69
    0x11410761070030b582d0340802c0440001d03282d4000b009201d8501e0b0002c015044500f031310380b43c03602408282010301d903485401c1e645150000b420714a07460000f0b8060710007000f0b43c900160034403c8164643c8159450705009a01c441c2c0503012201e24a101d1218034810209020840c7c50b640d60b404540c0c030700090b0340b4022090140040b224a104000c441e0018460740188194050196101860520142071440b0b24040e00f2409050605000480315881886042c001511010442445440d02c1000d00700500d05141103801d072070380d16060000554401c2101e049003c4d41e560f240582c030b20704160024224204444442d20800304242480301ca5662407a0010035203099192905c1680d4842c042c95160a08031b80b0030b19005031400d0f1020441c440c640c7c000309040c0d250303500c40b290090003645086500b05801c4903504101e54140002c1d8902c5440001b50842400c0742400d41801c0640714488903040d07505c16403210060366518100307449201c0454500316400200039008200300440c40e100500800c400300c0c00244a = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 462572571 1250 462571321 462571337
    0x606030613050c030601090915260a0b06030d090602071503022506110406120f0e03120f16021b0a150c05070f050a1202010c120309031106090d 63
    0x40340d141c10201c5004250410000c2c44141004030307100000750300a6840600050800001084901842c094400181451003007290a10b00d45403494561503c0d05000c00c40411803104e506098000411a0b034040303902680c515091030602c0f00130580f91081500d4408280319100c0402c2200075004280070040311000d890603001d905100c0f008170001d00c50305140c8012203444124040242e49d420b44213149980c400c541c20041e2052038500c12384140154030a600010f42282c83da0549401903400c1980713462045100800c422403c800d0403070031b58100b040307036600301c05812003000311035282c0301d4082e9002894201810ba0446403844020f4550b45a90214142c4020707203019103407070b603e810b074041009000b07510017100c2d03581003000000c004400a150030740d0240300310700010400021103420703202203035401401008490300d0300e280740c240d12a80d548164184503041d8485c0d000f06000c00b01c94401c0400b642d0300043d13101402e00c0e000d4691800385030343c2000759020508000c2c41d1040004c151901081f14280164 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 462573821 1250 462572571 462572581
    0x1030b070c020901120201030e010b0a05010e030102130b130e061e150d020c060f0915070c0b04060204091407050a03110405030109140d05070309061b0609031e08040b060603 76
    0x50030a124000c000c0d0080f0805000094002510790401d4040d4800d90302400800c0e0081c6c078290a89e01c203409003940c4060a030508120360f60007040b18074041c020160005d0b040c0400d0b4843c4c101e1140c2c05920294203c00005040c1c01c2103400c5007a9000a09000000000582841d0000c00d404d6429207d000425108a2802c1030241e038409142c0000003120b5031159a940780828072600c0a0340028140c1810342c45420701041c002070302e619050748904c25102c01001180d002d603003100307030000000d4050014482d110004101003010380f0304841c802d9000b80c2d00540c0e40d5240026150494541e20460810403024030103000c561039201d000c98441d40c20515001c070f03107034412804800451041ea48a140c0c07540c40d0111004c00c1000f0700c85001c08031140707502900d5403000c24000960f40d922030701384000c00003410759034280303d9903024000400580b01c02d030380c4680d0700b440542d540408540403000b05402042d00003407004050148003e601414444030f28140085003016030b5104028080030304800c0c419200400003030 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 462575071 1250 462573821 462573827
    0x10b0708090307080f010606030e0d0807090f0803090109140f1207090f090204060602061b0d09080a030504050610030503030a1d0a03091a04320307060e0406080d020601030b07 77
    0x80420303400600781c40c44144d45500032903444401c0c1c440001d4a50030722800040d014060b00c00d03900ca0006400182594042c4680e0886000310010459802e22084040104030140b07480b9008015000c004021a0340c2c03102500050091022680300c1c005050f4000d0f5040480c4e100c8000088000105a40025112440c95485806e0204940140b0911450b04070342800341036940e0000c0076602d0080d02c0030003142c1d0319a01c040707071100e5045406a44110000c3c5c0903410103240c0000400a001c010a0b000074a0340a03a91240707841e81c00041b40038000b9031148103001c1841428000d541d002540c203c0c3e00c038400c6203543d84680d164040285402c81e2195120940e18903400c0d9505104048821001560245080c6241c094000e20550140c0400c814074080b80a61444104044905032140c10302d50304c0040d80351001d02514802341e0070910718044180604007810741c0303042002c0e4000c1c22203512548501c0070701400307000448441c1c5e4010030303060344020182e110194012034200d042d42e0b0800113510155403130081c00d03 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 462576321 1250 462575071 462575077
    0x50a0305090109210204151a18060306180a060e0403050c0c04150905090a0c1509060806210a0b0a0b0301053405070b071101051608010611010e060903070302070914010b0708 76
    0x15203d0310142c40c140c036441c1c0503030385c010200041001c4c96510304002c4070041c40ad2600080f80c116400c20b0401450000814008030b0542c1d01030000e40011446584506071205945d8090f9800c90103d080450700d444410020300c1746003078400096a0411090a200344410680704132441001505607454001c108101c209100040c0c030f05411901d1072510307964404103100b001002c00d00000002e03000600c0807880078861418907015a10003800040b0007041044550041e000d00400c0c82000c0c0b04000750000041c400061162194032038600004c0d042c00da603400e0509660000b0101e0354007103421b02c40c0c07032042100000380850b1030203500c02d00d207800c14a850b016215840f420002624001c1001d0401000651004220b02d5200307a82000f8029515456024880c0d0b00140121a003c00c5045005101c141d03ca007001800c0700c1203010021894a240101c0c0b00d04003901500c030250070340c000060310421326404001c04001000c07406010000948040c02a80d0510410702400201d90400101c640c18031110b003040d = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 462577571 1250 462576321 462576329
    0x90302060714090d14010c02070501080708131401291c0c290f04030210030e0706030c0302090612060f0907090608060d050609070f0f05090c0d020403050a030509010921020415 77
    0x4c000e506070200c0065608c0c9c41502c28640080d00306000101d071284650704d200d021300400e4800b81c4051140355280062084194190351041d980c4a4201c2050030742810500074032904070801c1c890500f410414400c00c81c14881c518080303500500c0c00400065a26118101100d007a80d14a600d1450f540303403290707180c030a2842d846108550216101c0390b40b01c030000080084030700c202c585a80310024818182c003511303110f2901080300e400c1403030204803035406a00014260a903d2400518014410002403016000600600300124800302000310b03908002d03a440210140440f03801c0018034040c140100640c00781e0190000b003200600116001361540000b06410580c040700ba15002d10b80b450056a54181500c59048a00800c400009402c00c400c01544250350018041d01c0d11036075000c4210300a6402007110240f211303400c000010110300103000c8200032500c203a54030380d920400140010300400060304000c1a01c0d5014040c42c0004900b4043c400d03441d0790568001c1003812a0304100c2c52011000e500c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 462578821 1250 462577571 462577573
    0xd0f03020708030403060507033c06050a03111005120a0903090e010303050a200a0305070f0602160303050618070e03010f050c0a03060806040506040b1305030a03090302060714090d14 80
    0x4d404020408503030080c9204a4407070381c0410001d0a01c0080001004401e44640b4211813560364a911306404140c3c0f18402841c107080110b501c0741d484010846104042d07000740c68000f66020446481c0c500303004600c1d40e0885030301d00340f42007402c800164507200002908820840395600c10307900425001d03455800081c10100c041d0301580d03940c1d09000e85154410b140c01c0000840468a08400706940c1140c40e0b101070364980104a015030603035040e07072994003e250a0702d80008440e4a40002003050000700925141d650320614020450303d0082e0507a6005403219105404031040c0c80342001e400b221055000400340303000075890103d0310200c0e006204031700e00c0103151810f040c01c0203c8500e1550045c00b014003030b81c0e810014131f6950307200039854080a4030001d0036504a10046404070780e4042603039820040c0e0303000007145880b160380c03914038560150001001289c0c407800e0090034180c05000d0a54041c040303051040401400044070300141c8140301a491013500d1440b041c0c824400310954002c1c804000074 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 462580071 1250 462578821 462578827
    0x90501020f030402010806090108060c0c1006061106070504120b0a15090c0909020c101d0d030c1101090224040815250507062714010608010b0d0f0302070803 69
    0x304075600359000325800e901240000001c90503504121740312504039031244025200c56240c7c042003070300640c0302001c1300c02c282c40703020007a40c000800741c07080b0030007030010b9210445220a0386054501b001320083c01d44003030081c2400304100c0120440e030440100c5a0090302d02c41a9070300c1c4448100100781c2d0740701e0b100c031040d10ba25010603070100c5a84601c0a0f16036944401051a60741c0d0403440c264498603104681035000000c443d003100d0300300e400200110b00d050404021822907400f2840c58465030300440c400080c2c64500100500e07400454004074564045c000384411407107900460032041980c500c5071410001800c6200c0a0508441a00c000d0400c1108ae50b000c0f0b140c00a0107032480e4010b0703801c20b0741e4200301c8180304466200344540c4c44514074070f42c40e040d00307100064480000070a01ca0b680401e10000c2350035890740b4980d096080d00021481840d01e5940c400c6c1554544e401c48049420071304141c0e01d44580d01429688030a41403031216440142c0c000c44039a1454120305001d49a4040d140502c004 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 462581321 1250 462580071 462580087
    0x90a110a180603110607080403020d0c0e0c0423031f11120402040c0201020703081501142709070903081b060c0a030e060601080a0507020c060f09030c06070309051309050102 76
    0xa0b04200308807401a03144840000458080028620840340000d0149604100402c0182481c4c1c0d181c803015070207201800c0c0e00c1d55640d8202400203400b140c01895076000043c080c001402414229402581ca101c6d50160b102c2c284004643c0c1d40343d00c224400100c10070903c0941000a09400020542071900c01590b15130010241441e00281c05032402ca1050b414880c01100c0180705109659109405607610750054803101e115546128081100f141044071101c03600c196072a2000050014081d000c400319011490900302c80f200000104030070b0300c900707004d500340502c1a5100c04203905982c1c000c000c2541e6811501074030001c18682d0160002c0c40d02645040000054202e40901441d0600340c03800c1c809070544007100c44d100c030004c0720401e01007444440450100d0703100303900195102c0940c1c012582603928400014140d5007007160f40421840c40040c00c02094101800582e0f03812105440b07060800c401960050091425400381c00d006400380d00000d00c0841498100c030b000c141c0c21200840d83d462007 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 462582571 1250 462581321 462581369
    0x141906020d0221090105071502031806070807092706030507050a1e060c0302010905011410060314040314041a03060a0509040b0601050903010b1203070b010509090a110a 74
    0x454400440980120744102c80d86484a90391441c030f24441c502c049240503426030055078550401c40064540c858140502202e0700b20768402580101c0d01c038248038044425640180c1d1a002c001085c582c10003143ca024000d64540100309901601c0c035003051303410700d00420030b580c440340a40081e1040c00142442000014014003051000031b407402621400c2203981ca40c2071400070064103144103820030000400401c005440703102c00380c800c98402d20000ca00512292100e600703592545801d100d400444001b400081c10221100070000e26180c03c00344840c000c07095032850002c9000b0009004d00120b24847c264400801c4101d9020b04180c94136644650318002600e202a0021a6014040c03e1915000300b01441c041094500c07955011180b40480d81d560300c01144d00342c00440d1120b405640390000280b00742d5030b095140590f000c02c00000d6448080310304185402050690016016400070310130710491750713800b003412400c1b00d4014074030341c2c000c6c044580410000c00c516442041c60080b200700b03052061030307 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 462583821 1250 462582571 462582583
    0x50c03120901240308030408210108010e2404050f0601140f09012105030f1602030613020105030c030705120a090c0806060607110303040b070c0f150914190602 70
    0xd41c40c80200581e40100700c001071000c0009001c58580c1c50540c008100244182005640c082d21504100c0c0c01c0a001e0008000e005143c600300044070b650340f000501c8607407000d200303018080d0100d4004014031552034070400042041c2407240c481d4501d01c6000102845010840e10700061a8107045036002c2da03545007004e842544161815101d000481a0f08507240390134600703503050b2102034000d4400e840724405415203c00021000725514002401810405000a400703484081100002d80c0c280d014030b841010b040030303030040c40c80b20048903480004002d42d03404010f4940c003404d254a0743c1d51305d4442c2e4509540340d000361040c00803000701030340400a1201060300042c480b288605101e09145031100451511900111006a08400c06200c0500461f980b00010040c1e02009010769141603161544101560300110050700e00c01e0a84004002100c40c3c4501d900040000e100ba60143c590386810080914010303110700c807860000c3d00b0000c0f255641e218410301c50340154035048054103648110103500c0702 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 462585071 1250 462583821 462583831
    0x2041103070908070909030906031a060a090e0903040e06090901150b0703020609060603061303110a0b161b020607061b1112040521030d06030804030c05030a050a1101050c0312 77
    0xc01103050001d056007450103034222087e45601c0f140012410480110020418283e030705c5002c0d103a500050110b5140c0030010b084035011580c0d04080542001d11070a02480068030160712940b0400040101d00c20403501c80c4e401a6048451240c240c82d00510303180507010001c58441030b01c022100024150b80d80d10001c2140030b12a0f000d407581c5540b140340d0141c07900383c100c1e141c41d090f070043c07400500040b44611201710418440d0500e43d4104881200d450b19100c04010100d074450042c2040c08282000440c00c0c2c054940d4a10304084e08031110f404804128440c068000d00640c400b0070101c00b00b2041b5002100031012040100403c1c004c01c0c00300a00390108484400028001c44101c24500240001118291040517003d05042e1034000c040c080e80210351817015003540000d004030401c81409000e144c0055000301c6c0b030950ac0d5070071818400382d054400d07403003948260300010100000804c0460706150094011688450040004006846c5c03841080c03000301445c0000602d075040581c030000424058 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 462586321 1250 462585071 462585073
    0xe0a120b06010c080a0c21020a0213090803010f09061208040302011d100c1202160302090a1e0c0e010504031104051503012322061a0d0803070e0915010c02041103070908 74
    0x1f8100a407410040340340c0c840440c00060f0008200c02c40176003804080c2d002034841800d4002408440c40d1900807880c1c01c2078102c039100758008a0100b0260455008150251451104c0e0004031115a61111200d104510000b8103211040f8820114244040341580a03030a001e403487d0ba074040650002004040843c0781102c848804488400c1524030001d00f00072104188a501c0303400c581141c0070130004550040a10584540300c40c0c00b40f0044c0040034141e01c1c002e0f500c20700854a91749051016094400c903200150401506100400100e003c500812005010030340340040c05449000c84014410000f0141540540c00c0075000c2c1c10f0520507000400340742c40303a1b49080145480d080382c5504c0801d002c034880742c90711944129170300c0428801d501c0580c861883d624400c0102e41c2400224060b03003182d003015200441e001c4200545650481c4014241140c101c805041a00d44900c900201e1281e900c40c06040010748000300c030464441c1d500112030300000c11030700c1c1e48a203402d00008003e03c2060091900c1 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 462587571 1250 462586321 462586343
    0x7030302070201031b1209050a1a040302060a02180402090310060b1b0a030c03261006080a0c120b0613030602070213021c0c0c0f03030c0e0a120b06010c080a0c 70
    0x6040503441c3c1300f0501710159544040c0c03044241d200e00041c21128009071690b021781101e100025401c12880d070b2200096140d100d2461420341006400d021000b04240d8140e0f0041100326007000c0390000640216104950050715151071030f000c00e1400e04a09031104410323280c0440032410100702009409200050321000b540014003800d001d843e07030b40c0010001d0211702510914000240201c5c50307134000000441342d0358106c0341c1418034480e00e070106580c40c591403049a40d05011190f401100310341c0c0250020300c2407021000300e0000413380003035500702c0b036012590342859414559a460407950007a001054980e400740d100d08049000790f10510b0100d100c0c10244800a00f690014000d0750700d0b5092840d1886ca41170340d004811400360469000c10b101f0003552540d20030002d0015010410700d40d0080c1c0d800a0092841e10010b0210f511b0110b03280d1096001c10ba04202c82c0141210100c0301c075500641145198503a0380c0166048909908000c0a82d4130114441045952180d002d0b00d005010b843d940807 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 462588821 1250 462587571 462587591
    0xc0e06030a140a47130c0302031005030d121508030309010e010e071206020304060b030d0c050607090b040b1608040e070306050d0b0612030c010f1a03030c100902010909020703030207020103 83
    0xb1410f054140a01c000244d502ca100e481510140001403c8100282008460880f13040c0000304031440c02d00d401001c40d50210900041c20814a00a0050f000a5006041c40b504c80d02003e00103407401030b101500943c4845040364607080f0310b1140d5008182e10400c694490070316072049400b803d19001d2280d0720350f1a20200c80641200010f22108a401d02010100840000d80300d060195000174000d81d1a1500c5441440c00d030f49040000c9509840c460f82d4410410700300386425428030328003402c50810464100d9007404000710580031541203d20b41c01c0f1183d640d4249526000c01200502c002502d070b94008a00050b000b036411a0140c0b1a1040d59010401d03941c44d041000070315481103001422540000707000950500380288600d07507031500170003100c1c20310885c1d1140b40e095407910b800380d00300d10751943c4655207080716900c5000541902100690708042114004540e21480300b40d21595503511441da05040d0790180c0f0f542c101920640b501595100d00608000d0b020f0340c01064101e000910307060030a0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 462589928 1107 462588821 462588881
    0x105010801031e080406170c09060f1e030403080109151401051602060313261e1207031a0301060e16030204080604050a0b09010c0e06030a140a 63
    0x4001500e030040c0e85c07211128050030215a0200a00c050102079980340709850440c419101e295840fa4814413034202c09507420533100303610030070000602c01416417120079a81692039216092100e0131300060742e00e188818911a400e41c1c1c003000c5640ba00a0340c8120000c240c6010658001104050a074001802c640e006840c1a0102c540050030390041000c44404a2140024106503446041c8000000802840b13010741c52442c041e90002c00c2c48074080083e0540d1090000c40c1440c4490b8a00302c18054007c1085160f410901c0b000030041c0034443c90140212000d503201210000507030740700c0b40342c00a81112883e50090074142c0074000468104010040103201c1c0340a0401040781c010b090a11501ca80e902901012180e41004041e61882c0e41042141a0101d0107540302681d03680c07a002d180c4000c050005900e44100a01030078010b048241d90043c2c42d032509041d089440221158201e0 = true := by decide +kernel

theorem cover : BRFrame.Cov 462410071 462589928 := by
  have h0 := BRFrame.cov_init 462410071
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 462410071 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 462410071 ≤ n) (h2 : n < 462589928) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
