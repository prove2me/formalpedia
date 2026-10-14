-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0905
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T23:40:30.294591+00:00
-- url     : https://prove2.me/submissions/8ef4e86b-f8d4-40c6-9090-808da9103450

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 162589928 ≤ n < 162769784 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 162591178 1250 162589928 162589961
    0x60b030412050c01060b04030f0b01050105070b040303020f0c06070f020601090e0304120302010e1009030e060c190203100c0c02040c090501051e190e0307090506010c140106210303050a 81
    0x500003190042c0c002c3e100381c2c1e210100000c0d0040d112400c0710029800b6401c260745100707448607203004202903008800e01400007031a003c0d0801805964090402d01c014000905154000c10710441d06041034083d60983e41080080314114140010081c1c40c0c2806402060b005014142c0041140b040300d029400940084030011480c1900e020195916081e4140040b03046540b0f5405607044031808000c8030160600080d03000465001c686800f80c004040306d4a800e00454052011075a48400490081e0040b4100c4601a07110442840040c1c200f039240f41081d04240d182401d160003403940100700305400c070301c20740c1d040003107840082d802c1e283c0100c2c510a080c00501e0410000c0c1a605c81c0b40780301c3e0082c20900780e0030303410192101195400c50110580480009407a1800e641c0607140070444080103010550007040b181c200000002e050390140d19020340201039078207481d4207248095200302d008200c480020301c0c001d00542d00ca40d03c140b40104c42038000900700004641c0c40b540e07a01c64403407100308901c0e5 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 162592428 1250 162591178 162591203
    0xe030307111305090607090510090501030209010c06150503060606030f13050307051b01030c030504050c12101b021b03060604050414060115090608060913050715050304020103060b0304 81
    0x35100e406516039203034103400c8841e4100c1c0a030b90001c41c1c080d99009149141c0508004c1ca000c66004120081030b9010b24881e801c03000c1c52000807500074400d0421f441081c60003584d00d40d034400060344c6040c02e04100a01907441c00070360050040107030742010260742d812002c0e200d0300e132201c404012460000b2ba6041141000c1000803c508070b0681c0c1d001046079105606890500c0015200d541c10001c07450810100070480c0000242c8640e0f00d0b00c240c240c0031007030f13060810081c101512826581e180600860740180c7c005000341c03a52010800108003048800181800181908541d6040041d4008540c0016120b000d01c089840324004070284051f20014008225943d14442000301400c00600240d81040d14162002440c00040c0010f038081c0c0090404a1120828030f0700081801306541e2000d000c000c02c0300c00740100c83e0344000c800c0e41c01500781c2594401041c050f04200c1e04216095022006140d01030095150035600311000c1e41c0309500036202000580d43e2140c1d5190584411076008000480c01e51 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 162593678 1250 162592428 162592433
    0xa0501030203220b040209010b071502031f0803120108190201030506040b1c0c08121c020c2a040207050327031f110403021003050903070209040807120e030307 70
    0xa01455124549403603c0d610700302601040d54400500f64400d0314100d1145003001700f541000420301c0e00402c0045200c503d0302e0460b4584501c250f20038412080c4081e000070108500c041c2e0348024030221110540b401038030700d0703403002459520740c0036800b07010410789200700004403041c010075003001013006903074964400e01855004500510000700000d510950b169855400303511a043d114122855132400309040480608100e03494030b002c0e5000103840d60141d800600c1c3c1e08502c00942e089034184d44d0404180305000c56540b000303801103c62403212803041a40b184407007000c442071480910100c00d420411140b811080c881a44501e54001d05a940100300341124112000311151100070040601000b4103866400281420105010300c1c64034a204c8241c022003074450310482c1c943c07041c103030220341c6020f181d54086130440c45c41d00380040501d5500e400190380c40c901482160407140e8020301041140c40c1c1481c250740c031500b00c0d18050313486904101c203103441e00d07000308182c00865900400a41c105409039 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 162594928 1250 162593678 162593681
    0x10060e0901090513060c0206070201050c160f022e0e030102090f01050c0c10120b040603030c2003010510150e0901121703070c141f050601021603050106061d0a050103 73
    0x81e242c04000418402244080b45c1340b84125044a0401d45c042c0c200f50a1640d002800e4400107040300a8041080101a028008071500350032426441182c0348103042e910300001d035011000000b0310701100000d400d12440380414007801c800980d896200c1c0c040003450101458203e000e01001650005407420895140f0343c0581c010f0001000e0a00c120b80c524004c150105840c201d415035480082514000050b60214040c000c03c01400400e940412070540b45803002807405007280300203440c2c00d0040c4040d460546900b030210020960280c02404281800394084144040e40c1c810100c2e2166444c42030071403a07210301c610152620340285034070703410390030b10b1705082040185183c22201e01c8000d501706040c03480e802d0051481180661640c4854034124100300784030640608241c03189401140c00040e005002c54190205104403500025681e610240140d14081809107603400d8606558000802c2000540100c01540c0442d030b20700c01550034113230050342941500340000354407905022051011354442d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 162596178 1250 162594928 162594931
    0x5030912090f13021804110d0203090709060b09090a05060d02100219061a090906040305160f060c02010f20070c0b03240f0f040b0a05120610060e09010905 68
    0x81000c1000c04010b00012400b80b0644181011550045010316128440580c004030041007950280032032a070315990184180700c1d661402c240740d03602001040140c0010048071000d0180e10100b08110303901c641c1801c02c21707000900f50510400000b40042d020f26098000ca9004500241c0140c4c07a05826030308000100708c07881d50460452003840b0301441c1104102800c459118051000000c20140003040c2050021340701c80c00e01e000381d15135020300c5080c20b00017403ea5440703501072038581c1e200c00304901c4003980400802c501605580044198500b841010b80c0581c1ca640c1c09030b0000c00582c150880e80e00255007441c01c848200340c1070310300c10410783c400180080030101e201f040d2907100113441e0418140c40c0e40013512606040766001000f9444002483c3c00b140d1030350340403652243c88078903944c00a414600b007407841034010340e100d0340076400139114900700802400c4024070b540c0bc071460b085002c540e0341d8030444440440007141e40300007920f10700542c003294040c88041e0940c1c2d0351368242003029019000 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 162597428 1250 162596178 162596197
    0x6190e0102030f1309060e0f0a0e07150809010c08130209100f18050105190527071d090c19020c03030706092603011203020a0b010602011b05030912 65
    0x800c1000e5281c00b08140010280b0189058004004c103052076040822122135801c0b00500140d00c01c144020040f5488045602210301040411003405041c50030b424114550701c0740d004a20860041401150440002c52090803950b0003085100004c040407619184240c4048414080f640f410304054140f8a558035030007151910b0440b40580e4841c2c07500c0d0142c0071503009000141e00451440c035074200301c1c00750500405085503210810084031540b1b428081451180740c0c0320340040c180000e1b0401c648500b007a6035500c0d951443e000340c90060805004200c6c070140e050303080e0034940b88000c66442c12020407802000d10fa01201d0a00504d10004200f42c81800c0204083d403294080380000c0b9a010401803140900c2080041610304440c078044c5c04040d1704a02c1c4c248030992445007560020a05000c0e00c3c11039a003070002452000d003a0806031f00b0144000b4010308140427400001c104180c0540156003c00f0325581d140e100d81079502002c42d40340c081a0b800203410340001c0440c01f10a0b80f21000341c001100c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 162598678 1250 162597428 162597433
    0x150702010302070507030c030311010b0604060f0e030109080c010e03040e06060915210f04030f18030605090d0807080705030f1803070302060a0e010b09010b0310030b01081b06190e0102 81
    0x10803513100c02d450405503a00440303d01d09040380c1030041503409020001c84540d048001e110b52001a000900907003c4e074042d180070800208001c3d0009803162244000a0001600170000d441407400d09112550081403040f10540c20305594118003e00041140c0880b40700d808003c06c01d8840308104110f56018442166000c00841c007030300b182141c0c43d0014945448210f00094603940303001401d1140160051483c06500034400410000ca900000c1900e0701c01c810b0300e0a2661041c039214030002915050b00083e141500d40b004020246800040380b912001a07604c6071760f6250349424045841450031942e60001a20500104240e002060b18003a04040c0175455031007041d43d4000c0140c0b4640000c0d405800582c040070034804148040d11800d419900814000e000c40c1a094000c2070001006104084102200000240300070720003003200401b035503202e442c000303655a448140a9840541c0000c001c000401c4441d0381c503a0f8034220080701c1c4004014003002e500201c0004c03091f6500002800501d0550 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 162599928 1250 162598678 162598687
    0x20607080c070b121806040213020d1a0a050f130c050d0c1e080c040311030a0203010e07140a180c030e0d260405030405061c0c0c06050f06150702010302 67
    0x100d6003405244050700080314859101c50000c50074000a1002038116072091038141d040c103d000c0e00104481f45d000340c05070b444201c80e0012500c0d0400170b218110110300000e14080340c140039490058100c000543c2e04495000b0310546075020007451140401800d42d008003094001d41041201c0d4200d103140e2602c506095003010001c950101c03d480c44821014000743e80d4040c00c0c03030007000d80503003001d940140785003140441c0350007403850860340b00309c0c000a400c141e500510320081e66001c00410032500d501800a020b14122051907075a80d444e03038001c880301d500c1d03114040d00043c1003003111041110007074505802c24941003a8a98002d060001c00340041540f2000d07a03012081c000c0006030040b030010b580350721b81805264028000002c0c107110354500b10054409200c049800081601c00b501d034204c1d402c0e65078215515840c0d504840e042c00210825044c42e280c00303140d6170030411030a034443c011501880185e41e042c130b5102d020102180c50590056180740b1940e0340750b503980b02a211b0280b06060040c40d0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 162601178 1250 162599928 162599947
    0x21302120403110d02011b1808030406020a0507061121090d150b010509210f0609011b020307050a08030c22170312010e060109170d1e090302060708 65
    0x1403502200c05501041c0344124200410030308002c243c100c500701d0b100800c01303064002d2026034900e01c0b4202c2c45007000300a0324101120344c003600e050401860300c54100c0340d030f40384c6d1a42d0180d107454081109840c1e90042ca01300248050042c0c03000c99a0003042d00281446040c0d82011026103040c00218a0244200740710200041d01c4580006000d98080d00c200ea00030025102014281ea00600300c040c10440305000c0f030346540d101d40b080c4413210050380c95010b0090144000f4589005e030711400c1c0000070722a550130300148440642c00ba03030080d002514550138075180d488069940f8401c50070002c1c4660b008000f1400414141806560401c9a104500c0e1402c0072440001c5100c9011851b0080300c0400301e903041107281c030485000750405171043e0145082c103a24010020100205100703040900d0081030003e13030580c0c403c05140c0060518185680500d01c044407600795106030107032420380420340c1d4074812043d140c00d00501440500c40c55841d040d0075030541e13007444102d4100190407a0380e8003050141114 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 162602428 1250 162601178 162601207
    0x30b06060307120507030f29060d0b060d020a020d08010503030d0f1803020c040507030b031504020105070f060c0e0901141509061626030106031508060c04030506090c0607021302 78
    0x505c05540c000c2010401c00d0140c0702280c0031104801c02104000080e2001c4080361104503020311411a55951034044129680000d80070080341c443d8001000070710300c80c12142c550b0107404544540e0303080703c280b28884001034441c1c01c030078040c00e94036900512100c0d8980c1e0300d0382c02503142c07550850b201280d250790007801d03401611400e8200b100540c00c0f880f0111100d040521909502c1030740c51400780440240b00022035203d0030100d086400050011000500303590040b0300316031078030350300116140103d1200e0030803100505031450041c002400540020315180f805880f45416919a040710309a1004d40000700410380524a10640c01a4014442c44001c0d50f02c103809881c0c0345000781c005c2d00c4100321618042c4511301040005040351010194482c0d8000a0f080603a8196400c80c1000100c000903144281c0142c1c09a90100c0700a1144400b040241c0010303201410440784203200310b4406440b0007114070340714151400f0580c2c0020303081c049580035282c01c041d4a0480c3c0c400b4000145081e454220005 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 162603678 1250 162602428 162602431
    0x6030a08040602010c2c06031e0a0903030c020a0203030301230a030b07301d06090c030c030a02030d0e2215090212070311040b0d0b040510030b060603071205 69
    0x3d41d40d50208440419000580080000c4294100e8081e03004040e0310f880100d07120080942c0609408400a104004001c0355481c0610464110300c00038600226284050004902c0843c0001d042c00c00c8000c1c09400000d80f1182e40754002c0140d42160b09141c1412020007160540710418998142c100b003040d29030391403100c0554000c090038441847c2c5000040c0818004100081035101492241c103082c00311998102c40030000c40c0c0c00400c4400a480d2280032900e40440c1780d480c8c50081d00203002c4201400140c00b051150150140c901000440c0105900c900c5c2d6848084d4043d0043c07500440d01038418000c0c40955030000340030708503400c4003071844485060010300102a1640e07406d83c101d08038060146200040841c0001581313010710341c8044222466020b0100c2042c1a207031211992420001400d0f1000b51181c55081d03515030f42d0000f0010040d11801424034010342c50301000c40c032208181c5205d10103032038012580810a0302c0384c005004145d44024030203001c00078401d203c51039003503081c0202e0703 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 162604928 1250 162603678 162603689
    0x405060c010203010509060319150207051614120a080c03160c030c05060f0a2313050a050907020a0b040501060e0403050c0105010609050a0303051e0304030504180903080a020306030a0804 82
    0x40c3c0300c1d0705010900c501c0b2240a070045202c1d03070010140404000d03801c1002042d0503030004803c4555041c16203110042d010320b0780001d04c54025410808452082410703200100e0f844103484001c041545420b100b850200340d19245482d0b040340d040316001c60800002001112040c800700c80c070b80105420401908010181e08840d03000c100b007820800d0084070044ca10240108880d03151818403e00f80d42ca80c0c511802080030305005400d8200000c0881d0400152000c03900032900c5aa900025241c5100000040c000d6034454408020f010072103040c00481d031403040c559500200320140d55922060a50306009208554039921148085a0301ca11114030394000c81c07103a220661a100451146429071318141c2064040110501040103540d603011a11411203070107060031039460411010090a8420701c00703a2820701800001480308056020005104950b2440500e138402d295200c104000d031000b400e4081c1c0007400c2c01003c20005440c5074000d5421500080413941d088006982e0246250442e5204 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 162606178 1250 162604928 162604931
    0xd0203100e01080309010f0e120303160305090109020604121707060504110f0307170703080f091002030903060a0b03010906060b09010e01111207031202040807090c02011a1003020405060c01 83
    0x20007041e00e80d0715a035800340902d0b2010b0f6003002c820800003031502d80c01c1411142040034181100c0d10030746883e090240c04800350410390f80d40e480c00c00043c98101780751240510000f440c000011764004010710401c40f00c140d004150502e02403408074040124850050280c038461071403100001040c940c4801426500d124030400700b102d1800d81880d0344144d41d101245401507100400e107030015580802c40c001550382ea44454400107000103e490300d00015600010080780f00000c0040a50181a010b0000c242c003c60711018100d00c0d00d40304a07107078000d02d24140d4166000c203000c80c05221142d0007000b040e00000c0e000090580c00c80d103840d01610410b5102c2c0303451800c001640042546d001080f42403c10b82800e20b400c0c0c00600201081d5103800c040b005040e4a803001ca45501054451502c0c02c0c0220203c510964a40392200309003a2285824443d100ca0070303152001c00802e4074010f0003108080745030b410001201d240b280c0103010718000d02d03403440c1e810580d00b00700104860b990700303029003e501c41e407200 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 162607428 1250 162606178 162606211
    0x190308040b0c120703020c25030c120507050d030e0301180b13020108010905041109010b0d0c030c020604021002010f020706090b061f0507020301061203020604060c090b0409050c0d0203 81
    0x2480740715550301030304401001000704100e8604000302d6401d580c00544074600140c0d911702e4042494148500c040e245a81c1c0f03024601c4d40c050700c82c1c005124030700b520b0082000e0180960381c0c40c1105a06000504010300c40e8000b41c070100450b2400750000e0319224000d0401e2081743c03024030000307800c4440514203135800b4185080300c4014061103503800b69025007110364000c481181a00064180401441030011035a01c404c0090100000c1c0840319050503405403203844030396103d04c01b40c81036400484c00c00740072624000f180b10929100f4000c155038038020740c001e404181c440e9002d00414542c0b04000109643d22040b001d6808041407001b000740c940200000143d40c40545880300c90201c2c00351400d8461000d0b40100945030044146181000025081060340d503841440031030b014100c550300402842030050080418180c01040c1d192045101b840c0400c103400c180c070000d5400c80c03518014842002c0c01400207006031035150744419000511469078906014042c0c01c08400d0340d20803511a000c4448040 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 162608678 1250 162607428 162607433
    0xe09190b0301022b020c0604030f02010507020303270106031502040614091813020d110f010f02060105040906060f060c0201110606010509040b040b040905010615020a0b01060e0319030804 82
    0xc5000300c00e000840096280c0000c007403081c10300c1c0c204000020201e4075200600511814541e0440b00d64445000c1542c0151034030b810080e20b071220000f0550003550030480081e034220310110440707101e6001205222204007050603641804c04184025040c01d65840e14080042180d006e480c525174503d5030405a903903424a1001022000300705d21619408034103200d60700d11a514000e102480d20204000340c24296200c20341c03100c100e019084042e40002c244a0030310180075034240502000441a2070881a1604003001100e054420303901000068001100600141c50300d5000140140c1c000e480101d01251201c5021040f0000c990010300841c900b12005400c650b08040071141545103140034010901c0c03d04000307800d40c4244a82031b4071955454500040c1c5985560101c400700c60058000c1000402e01c1c0f40c414024602c030b0058000d0f8400124040c01e001d88000346650626520007603d8650b640b07044001d40c0c44440c541e01c0749625000b00341c4180d02125140410014460282e0794141c081c1c10b1a0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 162609928 1250 162608678 162608681
    0x207320d08100909020612010306060518040201020703033506120f0303010513020d0f06080106090603031b03020c100c0c050406060c030e01020c040e10060e06010207060f0e0919 78
    0x44288041c03100c4102004030700d52045003040b0446541d0701d07000c94500313030a10014195200b40c1c00c0781c03011010784900100a01480388d11004c143c07181552500341c0d50380b41f4a40301203000d5084500a0050f40440e0044c03000074420f07840704070501000e80901000700800c00d07850940c00c0b0b825200b441c541000c20104507180c540705c0e8502e407903050342901802e208079200c2c6074152240320500525000d801301000340880000c4e00d5040b508560017034074003001a030b025005503502410881c86041c02542c2494808110060301d0f114840440b9415121004084c0c000321150110b100c04240603429070203045104150ba44420074444002c1c038807913540d01082c10151034403041c2e400c25908828026441c0490520815821690b200c0d0310f16054108400c00400400040b89400780f09502e040e003041c200384000c2120303c00014407044002c080038062115688030400049851412514540103030f000780c1c0300300a00750141c10704a00941035440c0c22103c0203078440110b0380c01f100580c1c90007180c201d134075509003071103a07603 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 162611178 1250 162609928 162609943
    0x11040f030b06030c0603040b0c220b0310080d0c0609061803200a0b0c0c160807030302010e030a051204081204030c110a051e010201020408010c02240c0a03020732 71
    0x4030340e170320304604140d2290410204000c000311405800000c0d02020040e05445554143e40b41c0369600c0c1d4481d0b11141d01d80e040d608140e85c80c40041c1c03000c0f9408209803a010806451080032956528011000c98885101401c1440070a5900310f0b87e40381556a070810100491082500036100e81c01c81603001038001c0a00104180070040a801c00402040080c61416003c0d400c4510300007425142d03030708018030300d0500a400d8100503065403031b1640003950702c8002c07a0050072079029030000c0001003a46c9451945034030403140d91100044c070401c420602040c41c11070311504140100100750815071740c1c000c40480700c03806032800c2e008074401c032060008104c0c00000c281c41090090320231382c011074900b01c042000404882011183e030000306540140e2a4800d605513030003000914024040c0741d8902c00c010b911580418521042e0022421a8603070522502c03101501881d0000c0150349041907410003200290003250007115203820b20040d40e10454000008090416607103c03105100707400080183d80340015 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 162612428 1250 162611178 162611203
    0xa0c08040e1303180f0501123c020f040302040e101505040c030207170c0f03040312030501080f150604091a0702010e0a020901090e2d062811040f030b0603 68
    0x13101d42c14416400030304c002804a4030282040c5061000780c2d03003d500a054002e1402280d03603168864003d00090032031601c50500a10b00114503002074000c0340320141c3c841d511800c072140000300010001400c0c01c2d481101d100c46545c083d1001c5110030000700c002c0d510040807400c04c0010140052000d8130700380c440d141149509080c210302c1e060456691007038010907a42407218890300450450b070300720b03002d12000305c0340301490050702c0d42c841d01d03803420250411040105100080c50440003059201000600fa0100c5444400405404800b80302c4240306020003490150083c7c0c403000c010000851030161280c1000304100812418585400024212001000041e8090b48100500350168903040c60311815203070105c02c0811500448142d01d4a00800c20310404e40d0426140030004c400c0c142032120603080c80b1140103842e0b0039112250042e0030954141c0040703600e0720050524008076403d43c0d201d603e0100c00d0720520b60a080c0d961a4036000358081e17520036201c0480740e03020407600745804d2102101e40700 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 162613678 1250 162612428 162612467
    0x4030f0c0b060118050d030206040525030f0302030418020a020d0219020d020312030405161203081611030d06030c0509011a03070302090a0f15090602030a0c08040e1303 74
    0xc006468640040310094041d5042c050550381e0b40a6841603040c140001d088080c090307440089051500035035884e01100e0580d0745015000e01c144041001508040400c0004400300d0380c2c450640d1941c05c00078a04803003c505600c000c00000902d0305030f69100d100301d100003050050301c038242d112020b0b041c0740d40036000d942150400582d070036001000180304054181c055603100d800d10b08074408a40360a082d200014910b01e400b1082104001c0300248030082c5840c04071003903030243e40d2a00110415484d404004004c0390002d80000c41026041004c1555081145404011305d601c080c01c440c1154002c400f4861866254802072082c0301e014040720009010586086000390300d840c40107858075410a0841c28a24000008210722130720a8040d00c0780500010145101650344520703015000482e8442c4820550b4840e08010001e4080d0140c801110060340245107009003c03070b0304850155030700d50708880440041c400450050700c3c4040a0b440b400003031a840356a9101424041c10203280d0816150742030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 162614928 1250 162613678 162613697
    0x105011707020709020901050c030723060f0c2101030602040f0506130e040309030c080309040b010519110f060a020a200a0b0402040618060314030720030f030c030304030f 75
    0x2580e00058040c21500313950001a200c00343c00300101d400c0c0c41103407081c01d01d5220114a030024000051480d50400d881e60000d550301d481059a00c41c0c0b1520220303070f200c110005000005106200c4c040c01010b00942d03444441c04c103030300d558003010800312003a00144c803002d901240c18008806c502200d00083c003412904141480c0640d410540d122045010780d800c410120000305003007502a00090001d10703803100404a40340d4072003508940d65040203641d244a641405061403155005000b00c50300040c60000c25200d1201003441514a2400100d0081c03c600c11030103011050941486007a008111013036000d651649400002403040d62200403104d90f070088204c4010400c600041e0740c01c1110380c05480844260b8842c0005801007400340d001110707900c25a601003501d042281c0c007040031b4a105a2607406500f90103084507a90f401200c2d001419041254400d1111548074010004d00c2c240040031500c140d20b1103102c00c1d0454102301950030b200e620100500007010b4116121004165003850040c004 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 162616178 1250 162614928 162614941
    0x42102100605220f0608100b01091208180a080d020a05010c0504120b1b07030e03060a0203060a030303021b010921143001080c01031a030c01180503060f01050117 71
    0x8421618140101541e130310716091494140a411560003080d4443c1940c4071248010549000b42041d10846800200d4086d400b20344101c4079044000c1c441c1e0800006400c0080cbc2500f4098000d003010b030f45580c0703d40b4031440051404001c111100005586074054180840305191140c296014400c8940900c20b003070005100541d2540c02c00c0b085503811002c0c2e0b44042d00e5a6101082c000c0721a1000280d4140000c2c04070b052607000074401d5910b030416021604166a03840341c5104a01060314425800040c06c102000841c1c46500900406000808606421703c243c4401500311401401c00329071540c0194080c0a100400010aa00420303036410a5030000d010a03610ba511889200101c4450244151000d00c00d074001003420100c0c599006000102561200c20703441c0d881c6035400881e1b00003400c3c0b15007040c513807241000d94000600b0150007840c0c0200303920019031f40e2600403103456040b071404102c0043c2e2668100005400b0ba4481c0b500308416505003000140000c140c070324610607107110102440b0303d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 162617428 1250 162616178 162616219
    0x210b0129190f0c0503030f0108060907080d030b060405041404022815020a050d050408070f050a2c070309061103060f0f01030e0102040905090c0d1a042102100605 71
    0x140001c50b841c05618180c01d0030401e03103200c0900716024026101c04010420344810100e2428140d84400e0220f1390a6030b81c1001c0e180d41c03050507015000c00e58211000548519009030441407800400034803880c201601c40300490115030682940142562049007030105500340344620019607182c40600034607006021108016a902601c6003120700844000c2800400b88240302d980f80256008040c0e0b161303000d2841004000360814000c5000b18001e18500290307440454001004464020380404000e40c40d04004910184070041500038100140460070a24080040e100f8070a8100b81c5000640c042142040011248290000c910740d1800b0810310403240c0d64046a0362b21070100f01d03103804507400e645004034064040c01010402541c004035000c9505603090300280d10507234003c022550410000c00030020381c841c4401010f0200400340c10714003009100005426401400f43c54112400c541c00c41c08184c1c02100c1c601b6407001a08610039031803c2039050f0044500404080302e06d0030801100c0d4a0300032 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 162618678 1250 162617428 162617467
    0x140c0702091003081201060801060c021e0102010e1c0e0f13050a0b030a0f020910030b0106050304020402090607030201020a030f1a01031a040615030f02040f210b0129 73
    0xa125400c504000740344005200b11000103598480041600c600d144500f0003d0741400303028403804540c03d0b10011500c103200d00000c400036038004044403400814003007001c0c5810303103130020b50b4115501e03441c07980d5500078100300108455820751114003030144a5031004202441d210481e600c20741081522400a40e01c40307418041c85061903400003900d854a0301c0020003011264140c41e014014642e2040c10721090380d844001c0503001f6139174220182e54a5007049040c4400b40001031070811000014002e0512801c0659030292010708014689851940042c0e420f800020040780143c0d000a4500003081c1c3c540699980c2408540023403007407040803604038a06c42e08200d002410148e44607244020300005580417440d000780178004000c42500c07075885030303c04c2c040c01e003031600402c3c14110b41508249140c0300322411074180740b07000004c03281032183c1440d8260818080d48400002c4408010104840b90040d90007458a140905181ca6080202ca4101c031003034680c14402c081c0a01c0380f00d08803c1e150107060b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 162619928 1250 162618678 162618683
    0x2060709060c0312231003050615180403020c06040e2215150b21131e032007050310050105030604030c0804090c121b02070603020a11030d090303140c07 67
    0x4680d501c043c51031000c040c4800c5d0502020050400184041c40c0b0700e804105040d039008a0643d8126500c45c216400305030401201c0030780000704002c0700d071340341034104c0c038030f03a4005200784141c4025185a0000403d076411542006200d60303901c83c288142110314444c80f2074904680080035941100c25100e081011588429001c4007a40b03c11a1806603000d010540029118900f504c6031200382243d0310441400751f80f035140343c013804800b02054100c0a00e1440148103503010382401107005074400703100800c02014400f00e0030310030b070101c80804d41c1c5007a0300c807600b24030600001005450714080800d40741a01d0a00380101e03492400c4010301c0b054401081c12030740280c050030f0016046100f490445983e21540d84203d900600e4814540096640b080d14603401800c0c20006102040500c6621480107004802072030142c0e001446c00c0160f140a07401402c00c1da41d0034280310901104408419017154030408800480c0c43e40c0d103c503402055014450f000018152a518225501e0701c4400b1450700d1003501e402 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 162621178 1250 162619928 162619931
    0x5120d05060f030d350702210301050f12030711030d0306080c060901090b030a06050f040204050306060d21170c030112030c060b060a050d06061b0206070c0b0a02060709060c0312 78
    0x1469583c1c07940700b1400d0301c040c0400680a0f075105c12032060401c1c2e44026151400180100e4442c0e80b444034545e501c012017600401d0032586180d2030441004006060440100d0700140e40c5a00402c80d000c00b84080c04207030f8003c00c46402401590010036082100b030940e14003e05182c00d0041c4900080040c403000046020b5800e0f503510a500e50050b50b43d004150710120070301c0e070008100078945d8401e41006003291070a43d101e030075000211f410001079020328003503550550701240010342da5190009803515418020000d0b0380313414002140d02c00038070503101c5c1400701040c40368950200c246000e40c1c149520441c5a1181ca0855061645418580e84440310103020444504015818407903d030b41b26109800b40240341c02c1e0344000c0d0f951301030040c2d00a541886985441c00c000050241d003d580c56821030324801803608080c5401780d0800c091600183d0040d42d01d440100710208045840e4030040060000b1a0004e110034507152400800007140742c2c02000401c16042d0141d0002034000d102c0d6403922410050 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 162622428 1250 162621178 162621197
    0x2120a12090c0302032a06120c090d020402031302120c0a03170c0d090314060106082a1210080111030a0905010e0d1206060206010f0e040206040305120d05060f030d 72
    0x1040e1100d10b6180d0400f035454024100b20003a52800305060107441c984241c04201000d88030820001766000b540b04d901c890140c03c0c800540c2000c2e61200030700041100038586040c6490540100b03080f60000c0b10081c01c0121800c1340c1e5001c1d482c0c81c0c10104c0b00c4181d540c00803e145040d0102203159003019100003440781a01d64030340c602d10034100c000c0c3c48400c0412400c680c80c0c1c000000d001001004244070070b4442d1210004107030700181c6c0100d94541a1a100d441c0e07401d0760f49404180b2074607510003d0003c040c0c1c0c81d6100b920018401c0c104028144449244041c6c0c0d000e0401e003000401e685081e0b4008403140e8940501c1e40c5500310308030262644107510340f8000508003054249903000d01a140c41000d058024460f4915102c3d4001c001c4d015941076800c5c04104544d12103200f640d94900a0144a000142104003004000c2403100708030b501500c040c080b54103060362030740c4240c580780c840602a8450351000c00c0c0500800550700c9590790050046485008001c4101e000ca40c4800381c082c4070104008000d0f2 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 162623678 1250 162622428 162622433
    0xf070b130302040245011805090a0b0303040e04020906030304030317040309080619150e04020607171b0d050a080402040906180813060503090d05132402120a1209 71
    0x1642e00c07015002e004840760444100d10400600300c10395a18240c183c440000305d203501c03801c00c80062a080204818a007801e0004011041034000d21511280e5264014000152400c0c0094001881c0303220180b1414103288c41000542c100040c031241c0030350300074402080031039408204241c5a201800142d034071a00d5600741260207110a0304020401e21039a0705106002024144031020416140ca04216034240241501c0700541144900c0000c1c1c410540454094a001d030001c0c05450303c601d014414000242c1c19075885608640c0f4902041d00341388207144441001802401071724080c51820a25241032104081e1442d03101a2000c0e0280f90394a9410042003087d600c4184400c0000c14914441e00f024507003001c180d031212160202081c900000082c0c034501450070b032802283c0752000303403141a04441080360a50010890088249110080003c12480c0b4201080000900500c81804510500000381c54891088030703011452000304801c210302d5500003055440c07024a650045030060060 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 162624928 1250 162623678 162623707
    0x120901112203020a06020c040e030405030c090903070606061d0303090109090f09050f010c17060109171603060f1505151b03030901020301050102190f0b060d0507080f070b1303020402 80
    0x50300020340040130101c0201d005500083d0307604081761b04032414844419204906034803401035200305c42c1c00d07500c9000d2501d058a8680c0015903c20400d200f282d05041080d19610b00356001b550060011841c9900e1440a4a5002000701c00100d001d40055242c40b1400340001d012024030710030000095610001c038401c0381c2a43d0415441203410008031000320801c0705156000300101d04128010500c251071048554800f20b100c10310541050315040e48061614010000d4110380907450100c5d802003450340003a8103c103031780090156010f1100010311007500805401200e885020000160608800170040d90342d80b2240c40520788114120140c81340b151901c0348517881901a04210303140008002c0100400055003e107041b80c500342c3c02c6450700700f0300c080c800104096010006e8040018209554042340c004084e036070300000c010342003241d0003000781c40706400d00c051500030700340701d40040c111440804010003003e409002c2d07100c45240340504002c10504184202c0c440240640c6d0041072005c40000d40 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 162626178 1250 162624928 162624997
    0x603020c01181101110601080703030503061207060e091e060f0d08030408070b0c0703020c012a050d020124030b0402060f13030201031a0f09100b04090212090111 71
    0x1c088074142d44042c0c928058201e0401d9000c400e00040350096420800b040c00548981210300f02c001500b99541551411a2240e200410890300174051003c4a10143c1c801c00121000349029501d0703c01c1100e1403c01c210150402511a000c01030085482044030b81d4403104154100c40111801701d1302c00001008100170840e03011001e4060200070040005002104000b000103038440d140003031443c1e40e008a40740407401003600240050b07000c41034900040d40540c50b00314070107a5000080701d402980d24011528580c03c80001c86842e080300300c0008405030240100c0742181400030243c18071200102030881c0038a81440041c164000a20108040d511000c044035101603144003010364440c100c03422140c0c200c11a01c0124006490010040c10322104611554410903000308096404141c4c141003054000300039102c0e20442c542940c0004103024580010001050100303009030700c0300d00d0f0298141240400602c2c3c8140c1d41d06122a08042030034500c1280e0402860200700e58420104100c0420913108 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 162627428 1250 162626178 162626201
    0xf030603031e140d1a0102010204030302070b090a09051f05040e0d03150b13060f02120d02030a060e15041406010507080f04050303040e04150615031e09030e10020a08040603020c01 79
    0x42c0094090f284d10840e40001140d01c0810344126078402c00e00004a080307111b14130003d00160000e41c41480400340150007030401a0004094420860300c4114030401c80d441602c082042c41484104460302d10605103650004150072241009065002805039480390180301484003015503d62065184e41240d440e424080d060070b81c1c040ea1110f0100e00040e00003141e0b805a4000701d004001e40141441c40091501414108809880d04042501c02c811000e900060028012907407200303000b1819807054880c1612403805c810b1516924211030007444100c03a0780715140030260faa00700821000ba608a003c582080c0d0344014960703641e0f50f4520a5416900581d000150702d4003000500040440003103500d60701450003030a5030b00b8510088403140044131918420012100d40341207500c04c0d10f502a0f48410401c0c0400c00d082106030704159880070484440490480105500b94914151703030070071f00e55061030030829000503d1100329544900c00749014500c5201c041680000d01041150700a4110032080003 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 162628678 1250 162627428 162627467
    0x9080a050f0d0c0206070206280c020a0f20010206060915031912030e0d0c060c020a0b040c150f09050d0f060519050a0603020d080d18060c0f030603031e 67
    0x244100e8005c0d1a5842650903e006204840c00301e642143c651400426141c5c210042d11004002461448080c0031078221040c154001c2031071800104884038002c2c0040c40c803038020f606a100308900e0740c0703803641d03406401e260440d07120b01c040004a072120040c0c40d80168484030042461202000000d2070501c216800260090220b410b000810504100001498245460a205035020610981d54488000c0303500800960320542490215805500007508040385205a4032078000540308c401c4000402d840031503801c10452410032640311000310601c01d040103450051110000740600402c0c00c589400f9007031041c03d0381da0100d41044260780001c400319a00507000c6c001403074a00004042c24405404036012a41440f0004140c48468462901680c1c0d00401800760000c03540c40d42003081c1c1000904984107030b81c2d581400ca03405c60510100000f644111008241001d003000010807600380c0c4400d110516091034000c0c40000d8211450190f00c2c0c0115800d91008014844210380a401800389183d648 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 162629928 1250 162628678 162628691
    0x60f02060112050106182306030c0111010b031207060605030613060e0109290c03101404060305071e050901051e03011407030b09010b0705150a0906050a1d0109080a050f0d 75
    0x240547c0d04a029000006000710309a0305110308008000d000071501c0641c56003103030395a9406580100e40c44040080500e000181c000100b1006c81d240a00c45100440003440110b9a40d0802503d13000312006000306034050505401c08462016600d4106d500c0101000d403a04014600036209600c2214070b203800180380705140740041e81c19020900481070710004c0301d201c900007a40d4000d020b0200d0b4001c2c18550322807051545005100c100007030041e0b003000d80c01610b456000012030410807040c0c0c054042c000e280380030b200c8001610304e554980d07640141d0140001d500104050755920714250ba99401c1d01980880f80003624002030300410f030071000c0c0e00100525400f80304086034594000d01001d4400c1d03400c0b00440e42c07111291207090142410040a43c0d005080c3c250002008403076441d0054015240466903100316075440082e40d07401c6501c010f11640d24001c0b076400c0e540049180081810f1580204240c0300ca0361601302c42842034140a105106d400a00044421283c0b4110340351220603002c2080300 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 162631178 1250 162629928 162629969
    0x15091315020a111005161107050a24020109020d06020306040f110a0f0311030601140409110a0f17150a03020a0b0d0c1e12020f030a050709060f02060112050106 70
    0x101075070012520a1084018020a250251003424000c480081e100f040d410700c0d0031030440c0c1f40100300c801d0031520f01401e54009066116a9000c0c4050309160050525003402554a4070525150743c40350402c6a040c0443c010158560352000c04a064100e40056a02e5403030001017006400c07901240c0400ca0b1030074802d001389a0641d0050500c1c0812030340e4a10745031451003012003e655000c9080d411040c801c0000c1881d540c041c00000100300406422a4106951017440000701c42e05544c4c1d440c1070890005543e0b1513980e018001400143c101d0130724901201c900200c508a00314010210100f04141d085d8804d159517824140800545d80200011546030300c07410101d081d81c00c40100d0313154140c10111003071251070081c1200702d401c1c4954025070100c8102090102d41d5031844e028082e0009908206000407803162400941c41040101000306140c2005940244400550307030003201004502e14400404ca980822003e0440349a08076040c030102640c2485401800d5580c171244144c0d02c0303401032500 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 162632428 1250 162631178 162631187
    0xa03020703050105161d010e0612010302040b062a0c03010e0309150301081908070c0806040308061203040513020d02040602071d060d0803090708060c07020915091315020a 75
    0x1070720711410007070015440382c192029440710580c034510302007200c5001810020511450551200c0341c149008401c8086007800300fa510390084600c0e640c601c861400501c00c0d81018003c4050400c0180c0d2040c1c900301c0508510030a0305400342000700120500362102030f0541007041410150f84005008000d924880da06190b070701d500c803028280c050340384074840803c01c03c01034081d64100d0f00300201401903951046080842d04004103030880c3d10010600448000c5003c46499002901552004080609140c1000b800795200144003c0c0300d2162201740a440c2c08000c015a421200140c81070401c001c40c82e00b8420181c041c803006214a0780c800302d4001051a40007403a0740032554804541c101c0311200c3c03a1071103140e071412926550400a02e6510764009070148008691010003001918886070300c0e00c0c149400c1980540e00358201c10000318840c0191302d814000300b504125012440d884c01183e42000c10003040c0005c10401864900ca804142401030354080414500741c5070208643d10381c1c01c21030262 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 162633678 1250 162632428 162632443
    0xd1a09010f0f0603030207290d0c120e030912031b03190e0d17130f0510051e09130501060302071101021902040b0303040803041503050f040f03030903110a0302 70
    0x56260b0401401d280c0c4500300303120721000d40b900355000c4c1c1101401c110b510031030201c2111001b4009100f00d54840c0c480c9000b140a0102c40901d0710010070100c049500040c512859040380040c002c0c508131921891440000441703480e6442640c0030141d40201c85011415030181c450301321682c6001d140301c0c0000e140080003e04056600a1040e0618841c690080714201c4030301d128030b078003d01c5090404001c140903e919244a00820043d070345810b07082c0f0b403120b202c85405c0c1c2c0040100ca43c48007041c03241d40341007030075680441ca152400d1400d0001c4c441d8980c441c924048090a5041000900f00100384c6815612556408483c80240480d5035240b00041c000d43c0107450540b0042d0070150000415880491921024401c0da0210340703440d5481c0d000c020003001804042c41d890304c03080000040750312090000e40b004024919800120905800018095540c014242621804c181003000002a4012040118035405140000c3c0e501851714054030745a1009030031886511401d509541016030004444 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 162634928 1250 162633678 162633701
    0x409050f060106080405060103031d0d1b09090203030f09011701031a060a06051207091205060a060e040305030703050406060302090411030d02030901020c0f030a1b032603060d1a0901 80
    0x101c01603a6074030402c030b8030303900c05450003400d6802210041002c00e100d403000110458100c000700600140c00b4000811690306081c0440d24140c180e026507a05c0c10145030f0240052201150500080e18140c1c00662280309034204110481d50225214207180d10074030364200c040028401d045000e58490804080703010001049210219003200044d00504029002108441c50b544800d400d0510301c1558201c22030000701040d0801840150004800303500d802030b000207a0044018040905000321001d0030fa800d01d070844010115400c0a21000a034800200c0341e00041e18a00003c50740c446162030805001550700195004880ba010700040c41040c048010a01d07004808560704446a080140c0c2c50307010714800319002da00140e0021b03c2500f00034010203a011801401e60351054041d980e550390102e4095480c840c1d014501d44140104071503050030f46d52010131041c6c008010428801c4461141c400201030501400002c001401040000712246c503000d1800d140c20340080c600b0102d400d00030900c500d41d0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 162636178 1250 162634928 162634933
    0x70f050105090d023102091504050607080d0612111804050c06090109090c030506100201090b070c11150306031e060106081e07020a0b06090f160e0409050f 68
    0x5100d40c001c0381112050b00c005008906680c07455000c01076012040400346002da145071885501001050340c8202003d9610440180c50752000701c207010035a00d1a48510a041c40200402d001c50798450003918082a44010b80503903030904403450002400c107585c404064020741041500411840300301c054100b017000d9400d42900302c540071107901204020f50b0080d1494000114451050410340001d1000030b00c10304006441c580d0b42c020020494480800c07083c002540e890500420b8a00b51694103503201061009100a02051700d1780c040311a0003030000701c28880e0b050140000c0081c030b40025100154002d001c401c02e41c88500003101c0030f40c011299503109000d91205001d100704100020400c02844200a1140385c0c2464416951400080c2c480000b2603490b0342c48c1400c581510b401107201c0d0459071301400203640180b503c04c41c0010090308040c4101240030810070404680c1c1c0f0402d5001104c4400c0140c0c49810308020341d0035800c6104180c1d00142802e0841c2c06001c00007401d0b0410843d031104 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 162637428 1250 162636178 162636209
    0x3080601170411030f0304090c110703030225091e1805060c0a031b02070f170a2a030f02030f0309090a05040627060e07080c090a0f060807 61
    0x112010340d0042102090541001d01203008542005110501c40502034211000746403110315041c556009540f142c11100c0d25522500304140d440f041da0f072905500c1000078030f00c490441d40c019440328519240c606485010303841d0001c5140b40b0191a00041c02258007c000003100901003406c1958064140040c290505103202c4205408004001ca160303000f40c05805243c840701d503290700c1c603484107004004040d00c4400c0b030745e0415207802181d07680d410144c0040882c2480d1902c281103250349a480b10000106122240d0001c0c2e5002c80e44140c0c540c0d021021019841d02000d20300c2078884418110810b03501207810120800c4180d10001548500840844e0340d4680300c01c03921582c038403980078881d41102182c1c0109512028130380046400070f1041401245886c0700c5000c0340310303510760802000f070005044c0f54803c040c815140314107800f00c0038000c007512a041c1401100c035658040d0b04030a5000b0364014000400c6a201ca5002c04084040c0c0d900a00c8407e0761044003a076508028003402486210700207 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 162638678 1250 162637428 162637441
    0x61207020c101119080c0f1c1805091305100b1203210a06050301050c030619050f0613080105040c0510030c120908070506070f030b12370b01030308 65
    0x81e0402c0c0e1510610b009000040f0440006040311a0b112000c6480143c24001002c200006002201f450a5580000c0015111070b0b048045d01948100320001444012400035840d100c40c21201c001380c1311b060f5003181e040d0311030207c030480c000b825280c0074015010300819200c0a0006801c80c02241000711812041170200380031681d228401e2000b00c400001002e468403a0740d02035001d02550020450b103002502541e6000400e00391036048074a1041c5a40000400405e0f00e401084e00405520b04c01c50f008100d824000420055408400342e20b11401c0c0114400c5008000b4203146005892010028400d609044c900440c84214500626118158252a00c51924424419610300300c500c1d507900d142803040c0300d2006009003072400d000d851449003045860082041081858003e10341c1d655025400b000e0840018226503c407406d45105540c0101e0102c01c0c8180055030a0005030080000b1a1040d04032008030310340850804041c2e0910090403000045c003000c1d40c0c4060407203010f40c582606e680da809 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 162639928 1250 162638678 162638687
    0xe0d0308070e0a1d04050f06011401080c03040b04080d0f0e0606280302010c0201050405061b12070803040b10081501060315050102032217030d0c180303030b061207020c10 75
    0x10300810039009080c0c88903c0c032140c2c1c0c07241031340e8000c1d000d00255802e20444040d51402d05100740c00141a0010f01044c000da1942e200c050070740c0c440d0020f100c4a040d41020707a9205d01000307000d00090510207000c240342840b01d8540c1e01c503006111400d201000103a441b524141d44030001112451710860005840310a0702400c005405010001c60440300c115504590054032490045107090b410403100b80300100f00c64032203c000b0f003101100b8585a0440c41c80c0d0f01d0949185c1b84406a000c11010070a000781e00c0041c0c046826281c00c264444185a4942d64105403402c0380030181c1d01500040c880c12a079001c000e074200742900d044c0d526035a014440b04c81001c22406031001c0d5403041c1c1d80141e008204001075a52040d80c850b500c4190700b001107080c69514044150079400054000c54190000074402140056910441d5140341a504060341c00c4860400444c841104510001c0c1c145511458904e5880e5a60b40494500b01d98158226002d41409400256036158402c0e0382401640403000c292a40e6014 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 162641178 1250 162639928 162639949
    0xf0a0903062a0804150501090f0b040614060d0905070b031f03022805041517010902090c0a11060403031d07080d140f0d0e070e0f040b04030e0d0308070e 67
    0x80300704800b481d1040b000d084541890080065940d50001040c208a2002502419008041c041004200300f81c024000500701c404089460340704031b14042c4104a240034121200c40240070403142142c403000300000741c2001d824000001042400f5008010a130300036081c01640c01144015120602640c449001c0440d28886000c0a9400001260030310700c0708006420300400728810380d5841c10b5070383e5210302080c1600c1544603449110340d490320040c00181c1d03912440850505141c0300078072495410382c000c943c00d5034000c1d220000f4198001001c00b0414001c450350b900107401801100d5030707840d05082c01001403e041006089030001d10001801e10200084e8010a664403100680106d1502c030009641480e079000f0080903083e418400007080340c7d0b0101c080c00a184049900bc60403042c2c0c0d104980c10710f0040d0300018500e9a11405012202d031040f55100d52180c0e0190108005881d035007000d4441208403c0d540d60b2040d99070704214101607200104d01d018030320316100c0304a000070400c2004003c0300e0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 162642428 1250 162641178 162641231
    0x501260106050a0902040e0c0915090112050405030316080c0406030e070b0708031005040e0c010509040e120d060803070305070f020d08071b0603140604050c07020603010f0501020c010c080a0807050f0a090306 91
    0x8ad1910a20324a4001d2401004030b038005040114443c917900303880c64260b45e03044800b83d44603003010042040ca4404580c0c0002611003615110042c0c1c0b0b0084182d6031940214002c26080650f038403000b60070480104103400c0079049242c80c003602e40720103150013261640221012001200c001400040d242001c0c09020100078600d0050007214060000441e000d421010030300380e1090310740300b034500d03101e109009204401c80c00216456441088500e0007041d200c50354801c2c0c030b0651082205e0707404203512500b0790303207810b9000403490700030401800092264018000003030042e82002403403c0c10000075440e0f42c03171401000c0d00101c49066840905a040b95000035000b4008140400090071516043d4400c95010994049250412740c00d500406c0355908260000d040341840040180229a01040002540d4400746400002107a40e40e99040c010701400070102d090111000100361090301840982c0c4800401d0b000c401c0d100d004441008003080010312003079407500d1030603509100305d07070b40944107140303448 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 162643678 1250 162642428 162642439
    0x20c031308121c1127280b0a050910030c030b010206011206110c120703020708070b0d15050301150603200405010f0e0a0e010e09010501260106050a0902040e0c09 71
    0x4510007680c1028101c100c0301c4c1c144088082154109504100ca00140d01040c42d2a0303040e14203c402d418006070310442c9462200e04072018a4805420701081e104405880c40303d15483d44500300d22000f52440d0203030b0340700a47e00a0030464610440c40d41607002507d51011030343c0078003d40300c001d001640c4851081c01030600d4521001d171a080410484d0b000409440d40542c10f80e031070f092215030450300b440500180744444c000b0000f03500c2c0605038104003090140840fa0050581c840c80c0c10721303107402c604c1050031000580d52502124900d0600c0c010702d05009150180c024402c44218003d803081003101400781d2000f09141042680806d1003101c110103130300f048440d481340351030300700030054a030360381040078880821401002034880d507228007101c60000c1003001c40030b94182d4101004942c0304070b4002c220408a80c90721b40100300051015001d103d4000c0039421041c0c10502060320700e4050040c40c3c00c0250401045080084d1301c0c1403d900030401c450b500301400c42e00c0d0320b499000307021900c1042d0b030b05030740031 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 162644928 1250 162643678 162643717
    0x12004060c03120c0c12030507020c0f01020c09010312170402060d0b15040f0e0603030a02060a0e03070f0506150a0e071b0f0f0203010c110a080706020c03130812 71
    0x21030040050390700c00340c0203050680440c070341c0741030364000d6460801c5054001a880001c1d2020410040b044c0e080b1000242014000c915040b04000d40c0d500040182d00e104444100e9044041c4e4000e1000e4614004083e01e4a0499078681c1021100c26005c0030a80b030004096035055038464034010011401164000e090b03515058210407042e010b002c54115a503030040840c042803211000c044001c20040491940c0b00c01c041e4504142082d0640d0020005030194100b00004514075a001c5055a400082588001100854041e200303145014400c40101302004011030328091040015140344500c9003000c2580e0ba8107080024007080d908035101e41c0311382081e00c001248005024a9418030200c0c040c501034146090142c0f11000001040305d000c0d5000100440c404044d82002c1c011000c60388818180031450402451101c0d5540303601e124040d01c2c020000c9078040420080e60100e03440c04a440c8200c80d115203480f0590384c400a0340344603202c84d922a0030707840d0402080d51345c00e40d1903d031076410092104 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 162646178 1250 162644928 162644939
    0xa031115090901060207030c060e0d150e032106010f0801030b0912070b0a06050103020903151308030702070806070804110d030c0203011803080108010b1f0306030b040807020102012004 81
    0xd4a503051041020000a00420700940c5404002038001c1c0380c19401000e03000d2071401c25141000042d0009400c21551441540301230311343c0030000c22101c0e441549800c2104240c0c840200070300030308079201040d010000300c002c00501f06802804540c0c3c180c80803480780342c48140c0103548903c2040110320124080700c004002080ca5024601e40c0008a0001c1e1040200400b000e088180c3c4480f10072210b04c082d00c0b06009402265110f000041c000c2030804600d407400704000290786a80b144000841c052017200018003528a510507444260381c05000141c072414006406520340c2c4c01030044120600c03c440001721014810120640140d8000103034002d0510542c09000a00481c03c0065091028011103000180c8003407042a2201e802c000324480c2c100010b00c1c00030102d11046e0b0107089241c2c1440d200701402c0ea28441401210740c03c1d0000840990007256041c2e0240c0b41c61307400a4403a100789003c020500880000078040b05100740d0003000701030308042c02113918996894140d4a85041444107010 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 162647428 1250 162646178 162646189
    0x20c0a0807031b140c040905100e07030204060b120c0f041511120a0212070b070e0d06090b0a051609031203021e0c0c060c03030703020f0c010c0c020f0a0311 69
    0x1a901e000f4a00400040e0040c2d02c02d000810980b40100c0e01c2020310000c4044401050140c04045d4208a07014000c200c41c83d1115a541d160090503059001d6480ca80c403100e8144c01c2220b80d00640d4007030001d0200e141d480380300c2442c0340c100442e8810034144034000643d8501d680130856454070724640c0d201d81083d051401c00480c600c00d000d07410b41440865180c13000921810440b00640440300109184e81c0c07049040300034101103144c12541c602d00030a0044030009048010600d90005080c60545c1c0c41c945c55900185120068800140455141034820414000100308652042d1200e01c000e0006403540a41c0c82d44580740c1d80381d007500045d00c103003041c000215082000c9452465628016003081420580c10b80340304441c45489064080000b0407940d401c1d8180400501d40d001205c140d800c102030700c54469100c2c4002042c00003050b1780099407118001550054400c03440d0408004c000001003040090004107a03032205904c40d445041000700c1c0b5203400044102079951010b20b490480303814500780702 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 162648678 1250 162647428 162647437
    0x3030c0b0a0902030f0c040c020708061b1e0c070509042310020c07031401020f030a0b0d1403030403080105091e1e040f170412080a02010b030102040f0e0604020c0a08 73
    0x7418151a04281000341e5400c2010f00e43c40020070010b04040d402840810044940c071401050564202150070000907901048a981c451140310a18511958440c1005036030312680c44050407800c1c20038030280038104850b0240014481d994204c030312041d1580c0400000190448000f80410301030181c0070700c00011038031803ca040132500300b00c2d10301010039298042660041c03014074401d6440304d4410411311081501c002003030502c1c00000c41c540002e8003900d5005200c01041c1b1a001d0341c540842443c03036190614204116600a801104996403280001d500c2c0d034015142900014082d40002c521890700900c160700810201c0e486c01c40400130074882e1030300a0b40080c0801e4102d0308504040c0c0001da610000c861185105614181101c0c1451600c40a070f0344802c031a1102c41d440500c0144100720141d8485071840750020b12560300c1d0004904104c2c050002160569010b500100303000079104000d80d2040181c035074260102c40342d41d0b9513009202c120b00490103604403960084c0d048902145a100040 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 162649928 1250 162648678 162648691
    0x804050d05070f080c040f020a02061b16030801050120031905070b0f1602060f180a05010606120605090402060f03100f1e06020d020d2106080a050c0105030103030c0b 73
    0x7a000c080d0b503164494070400d590f03032112031641c1003030517000450700d0181705443c007c1074803500031401c21054031802503403601c0061003650342800350f569444994001105481d10703201c10074040d0348001300d0740c5401400d1100a04c00d840c0802c211b040a404100c061420707800700404580700940c180200082101c030448404410a0b084c40300c1044840017040300c00b1541d610400e040c614441043c241101c80e6035500b0701920910045403c144207010300001168246a0030111105400c484018903c0c102404c0401d4118010030030f62810100250054110440f03001030080e40504102e0b8035a070f94284140b01204440081d0321403c20030010710aa0142400f03540c00140c80c02040c8030440e00d41c2d041c0300400406070816284014402c02030756000c0ca040e05074030042c10451015045a00d24504069502d82014040c0000d02108002060030f80300010343c40b20760020315000500c9075036642c07034045844003203010058900c0d00640070906010b5019030100e030b048a6055a6285244c500d944580c105d11401074101c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 162651178 1250 162649928 162649933
    0x110408030c030c06010e0f0c07030e060c06060f0d150207060e0d0e0405130302030702040902040b030714040c090f0b090d0209010905090f01060620010b060724090804050d05 76
    0x42a011400c001400c40034001d080110b54615030360421034940641680100c10110340301c01008100c25500c0c00e800c0d00000d020031166114400391505550501c80c1200d0960001e801080f03c0901c0800040c015005a00650388000f01050400500800ca600c8250207000750581c600d0a0402c803466070b00510103940110300005981285c3c2000e2818801c0c80b8508000140548500d05901d15140c41501d4000902d0000c05c451f40c84155006916400383c004060300c1940d59000240543d141c607001180d28a400505682000e41c8618400d800f6002d00c7d880d09010302c0c41c2103190040140150701d00e80c01da500320050850f04138980403120440f68002d14059401025000118005849606102d8043c00103d04045a01c1c42c025070128903000340c10312049000e03070410701c080024035001000d020070054000448040301f1049420180980f44046103941c01181c00901681804046071003900300c8604d0780c048004201d488120f5405455504001412940080208001c1031410000344d2000d80d00c02c809 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 162652428 1250 162651178 162651187
    0xc012007230405071d010e0f0d030c140f010b03010b0a0509090f010216050c09070f051b0307050d09060f02060a0c110f030d0c0201050114100c0803070302090901170a0611 75
    0x100d426030742e007990980041102000020140d4080c5d0f120042502420320785020100e104100080003403002d12220381c0541c4080024205251040c0b104952a81d00151010100c0d1902841d855a510207000189019480d10514107218a8180144403580381c005000c82c40140c01c00040243d25140a080003000c0e100d401c5c0080a140c0080c0064024031000e1720544a021485090842c1030021416402d0300c41c1d882a0704015450382c001d10600004069031500329101c200c1c0340c002030800d4146190140080c400031070400c080090019250f20215003540c2e500701c1140c0e0754101900c2c24019102c0800c0541c111800240c5242115444a10300352202e1030030245408032000ca043c00c1c20410a00960b45820000300d041826229000e8480444040e1001f00004e40c901300c0b00004017018000c58903c154290030060301c10601c118a01080d80c0c0d0003020700c41c0c0c0d900301840d019009520a42147d4010420700000240010b40f1429102c60b954003000030f030409a07020b544580041040034440c4083e02c50601 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 162653678 1250 162652428 162652499
    0x4020f010522050108070804120807020a020307030606091404150f060509090f0d020c1e190f030506060909060727090e060f01050105040e0601020106050603090c012007 74
    0x40030300c03100301c90454450300103e0800d00018001c040c014546018840c0900038000050400640c48940703451515200710a5103a00b0380490622303040d03003030103581485035480100038000c0560041044072250a810007020b10388003403103107000350111400751000c00e041d40380001c0360346550801520855aa40b0005030507464000250788504c0603030f0603000a034008221100c0d000720400a0765000c50050004019048452002842e486482030310594a150080d030102440e444204592010340c1005881d500701c2501c405a402e40e4109034402a80c4503c921400b080c142d092040d0024018101d81d030244c50340b5038a40409540d03c03140c00004198101040011000110945000d00050020410702048091031030849601e001009801c00c084a00d03104010442aa0421300300d80854211110280c4150b9941300180d0040c0f0395680510707041310001081049981c00401c00514101090300c13001046c500940000600c103010f140e070911154010002444540d000206c01caa0440052418003014042d11 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 162654928 1250 162653678 162653707
    0x5090402030f04020906010509150915040b07060c0801050d0305031803030a0b010306140a05012007060e12011e0902030106090c030204030212031608161202070513050f04020f0105 79
    0x302d0b200c4290400c504140030031840c0101c442500705800746020741c101405130000a103d1941a18400c406040002e44100181c5030380040d6088403951403001a240c40e51045d44421031360044400312202c0d03103003012602000e802f5201c640c1c1604c0b0054210725440c4c0031540c00355481d50003c0c1803140d409100b000d881c030700184100f004500c1011810b0021501411a00c0050300355030031504402410003100f40196500e0316114480c0e8200d8200b442c03c0400c83c5044010100321802040924509001d40d0202003802500080b40403010f510980d1031503c1130184514035400c0324a80001405001014542040480e800c1c1d007080c05d09500003000092001e0351400181c2c100c81c1030154000110f40c010404006528042415483c600207810143d403034502e1515802c25229108840100f00c03c201003905c0000504400c06584200ea0121545400d80c000c031070301a5070f40e50b036842064442c030701c40c1040b05404801c9000e0309024540044204071140c49580c2008516820444198108001801903203204003c8 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 162656178 1250 162654928 162654931
    0x1080c070c0303030c030608010b0d02191205161401022d0a0b010f0b211305030a1d032409031e04030b070f0c06092111060105030106180c0509040203 66
    0x90324000b0301e4060117900607003079a816521154560345040d102c03554039100c1040c605c1c82298120b45409100480603111036080c1000c0c2c200781c0141c0c403040325040c10448001410716a569440010208869446200c030000c03000d002c511a0040c2c000708110b0364103c400c00d640c110080440e100c528160814500d10901e030101041058640c2120030004101c0c1c208589080000352102c204640c0c40d10700e69040d03c04070038001c402c800c5500003200c4000b40c0c9080451180b1010031741c3c044217480e40c03001101c1009182440c5c1014503a000894009262100d10b0300140c841c420039141004c1a5403003142d05000c080c20403006064400602041111081003d1900705803a03010400700903294459046080100307020000070700c0b50092040d003c034003254664100d036000c070400d07500c5900415500c009241180c0c50840b201d00e0701072581d0f40031224080c065008489070741c1c12140e4070200c40140e81c0e500c0415003a40c40d1481030011400c00c0325200f51031a006c642105460b0011403c00900c2d04c203062002c10100e030700 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 162657428 1250 162656178 162656183
    0x11150c0d080a060e0c0304150f02041e0905011401030509161517040f080c0c1002070509090a020d2a030b01150c0209060d111c0506070c0c0501080c070c03 68
    0x80d400108400c0c4410b520a81c0c01070480080030300d0003844d0003030f40400e040c4005013018041002c3c541c2144030300c00040d000804040c00d0441c044d900c403030361152900e880040b40d0003d1555408030000109001c5041d1042d14101c547d0400030114842c04400158000c281c05890003055001d5042500d0b00b0a110602c144002d0206190041d050741203450001c003007114410300e140e00344114100b0320012800074040300300c405070050003240d41c81007070214003480c05000100042e048030100c0296032003580c021402404a480c103035000d0803166204540641c9489079140001d5020f85480320f084046280940421054190800c0348090b207594401c5807910f400e81c0754000c45079152540010320100e2012802c02040452500b0f0041107058254006031902600a00c100c1c003512200b202c3c84103000180c001d0343e02000d000391500c0440c03a410614483e51200b000b800340d51074402c000200c1c0381c903403050003200c0316190080a1340060f00d0405004403121722001d82402480c28044c425031006c0742954001c80001c51 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 162658678 1250 162657428 162657437
    0x9060409050c0a0908030405010503010303030c0c150b03010b0a03080a082a0a03060e13030305100b0c010606080c030408070b13061a0102010e07060e04050c1b030703140711150c0d 79
    0x20b01c1040040c1340c503000c0c0e00940c949420900081201d40d8208042e40c0c10340f503141c140860b000520400072140314a40e010081c000d0744480400840d40c41c40d80d80720340c03090081130b07000748460100350007400341c0740884d031000408240c0100711703040d0004d11400c400d5421481500c141400344180580c200340080740c449031f407039810600003545410280c15124000041208042d9580d06103081d0b0309042012041640180134142c6410014512800740e216086c0540054804141c582800c44000d40c02002c940c0511000b007642040401d00144483c003e0701c3c401c03070b8050261864081e80d40c2e103101c45c51801038110000c0b101c4031649400054540e0103030034010b0000325580d40510444070002401c2d1103001407034040c5c603001401c09005c0950b04c1501c2c1c4140c0c1c0429240400c241c1c4a89070354582c28410910700414580384101d1240e4500f4020000340758680c025994541d03411003031820081584203101c00286060358814240c885c2d41003d0240e801c00006c02c0e60141d090030611107103039040c200000707030050000703 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 162659928 1250 162658678 162658687
    0x60411040b03060711010605010f052a0d02030c0709020f0304200d20060408121803160305010f05010b0301060815030601080d110604080a050f04120c060314090c010509060409050c 79
    0x90305c00d10502c1700400f42441d00e801582400750303001d040c600ca80d0341032512060041c01c0026081d0000c00d190006200320034211102c60140010007920b90300822060a12130049020000d0300d01c1c0b1600a61340d101c046645c07034a00c0e50321981c0c2c035502a007507084008400c0c49000d512120042d07444100c121400b9004400403000140d60600003031401c9468000300744940411b0005105070440022102190300c406000c02c0e9075030a10445202d800d0310307064010756040c800c615094101520204813081228881c10090080400b96000c4d102030350401d0080d42c10555040c40100b181c41d2040710640c0c1c003e0000a0a01c4e41e001480001c0380c1080f60036001003a4079403001200805595026030701000c1441081d0180c2900c5c10b1035500d01126106401e948020481c0c003146003620f4000c59001c983c02481385280c40100d040051038407080030401da108900c0400c4c64000001c915150038a5070a10900405000d0084c24144c000151004d800210700c49400040a11012400480724460ac5004541d610942600c1e03 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 162661178 1250 162659928 162659957
    0x10f140105040c020604120e010c020a0807030302060a1b050d0930030207050c01140c011a01080a02090a090f02040308070c17030c07030b061302030f0402010917060411040b030607 79
    0x350354500080c43c0841d84a00c0c108008254000e00251007440d9503d021002e900410300100d42c5540c0c03822003c0d51100b403180340001c040310000340a4003241d101c1d07003e55070f403641c50540a4084980e8200183d02c1250590816030a2520603001070825031071107400040c05070465100c100c00a5400c40b0711441901c440104031079103d40c2d02c1c2d07020f075104800b0b1070194a009110760b06d081d2200700e840c4003a41409800e03541d00d02880c24041c1038404202410000700510301d803c070140b03520000a80850f0f408160341c4008030700549424001c031401f4400280c181000145040c400100038500b850f4801c070110780c20f1202200081d01e0400904006001d1000c0321103842c1011140800c9140c0899003c40304e6000b00010b52285a0104111040f0307030b0440b0601c5540c0c0d40700008610701c02460300341c85070180d10000c02c00039030081075400240154000e90318018002e486a00342c0104012020382c0c062941d10040c00240080c080b000c010310034040c090710100d5074941d00b001081c582201583e456002c1050301110041 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 162662428 1250 162661178 162661181
    0x30207060e1c080a020f090f0f090a09031d06030411040605100c050601050a030203070b03040213050106020d0f05030106021902040b03151b09060403021306150c05120306150705010f14010504 84
    0x40062401e43e08605e052241c0d40e1b54030b0180305c3d1624141c0186005a4040c019540e0364920030070a01c400351960301185402c0c141d40e8010310305d00c08101c000c5010a00c0820285007070f400c5103045640301030003080c50742e203581c0c0307451211109100d46281d0058580300045007c0d15410031071003888080303441d2104c00b102546085401d040050b0440c500880b4030040400160380c0004036441107480c0303002c2c055580d4841d030000c914003c07524007a40440314248000011201d41c00241407131100c5c4d00365200c004556030b2140486d100d100a115041c0180d0122420f000c07041c00c01c800300e80c881e9200074400030b80307102d0803804281040e03010252600020126020012442c2e45024511000f0b50070020042c540b14996000070120f0040d4003019024a60741600f1222000c40c0c2e620000103041c00c2040d0414076a4010401003030704003140d00440740f5009196005d00701c0501d10050700e000b441c1c01008050079000c4120202403d80003148141c50641d01c3c0c01c1665040801880380e800506000030f29520198101001d000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 162663678 1250 162662428 162662431
    0x7030302060121120203070f0821060109050f030a0b0f010f06050408030f07030e0a08011d010e0a0f0201091703030412080403090513020c031612091203030207060e1c08 74
    0x43d203c0900140d103d00c3c41d50300c41c0000380c41c90b80070445884514030110120b00e54050a0002000c82003100e202304144006440076000c004d50580c061003807803000f400c560350721034000c2e243c45002c240107000500007440d28584900c910070001d0f045582560042e25101c0c003208050700c0c1c08082c03600150040c004291080e2500b40a06042c0c1070041c0340500e044101d6903244182c00794000c088001103018001c0510070303642c080c0800740041210300360790313158000030780202241c02e100c0c1a00c940b602107012075141c1c10300034204040a001c014084022103500c60041398402d00e10106d0411045800114890303401e65500042400c01800035501c038500341c40c01f4034000d900440800700707125210040100090b484580601a60010fa91480222907102241c3c0040d000300c120869460202154805100d03007184556070a82d0b0040c401541c10060f41002524007140300e014001040d1040c00d4100d021034042c1d0010601a40308200001e510ba80032070b405410b26601c0c24818800e041d600c200c0f840c01e954010b0003035 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 162664928 1250 162663678 162663689
    0x20d0e0706020706020d050306040209030d0216051905040e011103090601050108130809010c05011104031b170a060c020705120d120e0a110f0405070512010f031101051605070602070303020601 84
    0x1482e81c50b01307000d030281d03659500f41d0710642003110010008140d030300c07039405071401924050215612148011006922280305481c103c2401480310700c00202c510b81b02a10a0f603071081482d41900480c107140074003000d0094072015481781d42d01c3c2d07081c003280740380007000a5214481c3d100191240e5410500010301c1050040c15840c50244170204403008155800121118200c090805810000071303072401e140940940b140c006200076003c200041888032807034081821400d890386020400d503c0d000e002010101c2003110b10796542c8280e0b000c4002500950000d40c01c000c4c20700440b071502d80d0f110002200b00a86040800c0d20340c100340031a05201d60480a40485031040303440c103114440319602da41b6503510f00101c000c0c1000d01d120380c1c071450945545488100c05280500180302c0c510346602c0140c96070380001103900c0b00d01c01d41000040c2291035080490142d9034000d01e0411052201d6004440503049102140d141c2000410344c200060820080e48009041a0300900038a40c0345040107410480141d01c00b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 162666178 1250 162664928 162664933
    0x106060804030f110c03032b0e06130809031911040543030209120705090403030906150314010e01110a03051b0d0f0605040903140306040f020d0e070602 67
    0x502000a800ca00c01031008030307007440c100007200105021300b032804036000d01540d05400000b4910f0300d140482498804604504101803008010840c900002c41d028007204010540100c00447c0c0341c7c180e080c05890805000da940b540c2000700c42c00000c0d0414450460344401c0300c0900e0300103410840d0411001c9252842244c00700712614180010210486005102800c4001300e1060780c440b84041408018007456000d0440d8030b44180e180002c4c000390300c100f04080c841d17070a000f0b201c0062440090003c05a43d80644444126200c56800703030054100301c441140c405440d40c00003080440141c0745c01004600610b04140c0f40d000c102c81c0d05007164244001100d481e41404540314018044108480da03844a0f40340000344c0d81e1325400106940079440600d01547d000010b50712164180315001510084c034014000c00501d59254200300440302c58190088c0456140c0710302c0b044181c1040c000c2d44e8094800350020034650002d01003e0103c2c0c1c40b44281e1000b5a40d102040e68032060101304460207071069000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 162667428 1250 162666178 162666181
    0x80d02030703050a1404080901020a06051815070f03050408040b0703030501030213060b1b010b0a0b1e030906190b040207030c0b0108030901020a08090a030c0312020d050f040603270b070201060608 86
    0x705c0c05622440284041e204c40000610508564030802c0004000c54103c2c1080100d42441d910a000d00c94644514400f140702e0110314110602ca1005018003920326070b140d02d540383d548001c2c140c0c0034040052094651001c02c0c80005940c0060b00018002c2c0d500caa940010990b0661040040000d520151004150b203400403d1090407484002c4810036030040d101084824601103000340500a505a15908120740c42d00000b04112008050106a00400c404a46880440e0f065804034002160509087d501c2040410145902580b45950b0311681840100d440215000407409136030000800700c0006501d520310009000041d1051800340040724055441c00c1410f00000795140191400079001140006500d1001d54a03000c64200666100480900407a56424403060210134280e00c90b015000708040000014490412079220040c070150081c24030781090300c03c50040c0080d01d04490007461030004848003414001e514561548618014585458a103c009080d14540c0d4001d0040c03181c480c0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 162668678 1250 162667428 162667451
    0x411060c10061a0d02030c0403020604030f0302010b0108040c0b07050708010e0706020c1207172109040e1617012c300702030a1202030a0212090607060216080d02030703050a 76
    0x311350044080348000750701c9403036406484426101e19400294840300c0000c000041150040c2185500c5000750000c03c0007541520054503041e1040390010590031100d90306002003070b004806800541e00130412242c4580d1100325090031142c4c1c886c0e84940b1070307118501c204a01c030b50410a0404102c02a039800d6103242035160015178515041c01066101544850460608001000810040400e607007039072000542184810680747d12400b03034240114200021a100c007000000c03802c42100b811407900000d24540312044070490102100b44680d035407905c025002003c45480c0401d1007482050418889901d141521440c2c101d001200b40d001780500741403004500c80c0170300360185041e441f910246d80c80850b440001e0900452403030007410701920800c8d859940b03038000301503c0340900a400300e0781000441001041d0f607000b02d45036254044000c11500780011213540241c500203a81c0c0c28018010b050990725030480341c210031a690b10b05540401041007940d45402555000074406c5003c100c02160741 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 162669928 1250 162668678 162668729
    0x90308030106110307060203040c050901090203060d0204180b151801060e13090b0f040b0108010b220e030c0a0b060f030c0904020109050406090204030501060503240411060c1006 78
    0x520881081c0a80b03007000400d20f94091044894480e441a4215941d03c3d0a1400c0b031482d41d15406031900a02000001069540c013601c2100d00a1200522980d83e0f02035075030030400500310041d607070003061402c81e4034a40015103104601d03009040c42c2c880c081031403440009000c0c0c60441113a818002c0c080290040240941202c40800e901200b52103200c03140740804561406031081000040c481d100003800c000c0000041464240658131801c2c101c00b05998410b010350907500e541d000726610031900110210b642014108200105941c81400300d450000c0400040c155006014490070b9604103c030f9107002c128060341d2403035000c001102c007a8100203840e40032076600e070084d803199402103100101013025680118507000c003e010003003040c0401600d400ca07100107500144402c890542c00c100020543c0e24001c80e104c3c41d0010032003003c440c400f040c2c2035907461078540a4800c4d651314684084160480e11003200406620307001ca40100700c04006144c0d0b040071036105910492071514003094a1141c0ea401 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 162671178 1250 162669928 162669931
    0x40509060105101b0b07030209041a0307090e01140702160602120a030515031e01150b0702090411040f020a2303012601090b06010807050f030604051512010e0d09030803 74
    0x41c2c1c0340c400300c03c8480c001c0c0600440e1130700b140039180034192002c102245605030020182d41e00c050301e003030100c06441d412020010108185290307050b04429818091913034554409019030f801c1100100d6200c4d01c00200e03205c02c5500390381c0100160409000b109904c043c000c1510010081d910081c00005112014181c1074016804002c0400d5100e40115030600c0525100103411407005040e40c2c80050382e01180214001c0d819183d58003942441940343e8110714100840085500340c03011a41b6000d002d5080104200000b1b1040324a80c600b400d01180d50b440e944612808035044107401644c6001300311014000300803001110801100b00403400801c01c0b245410f036030440f00002100300403d882c211500c00d840f44203403204412586020005d006010700c1b10301c814003a003420380311031441d511031500803075a0b8491080f02e04d034000c4040020400608050340f2456000781d400c4c05000c0030640410024803200c0462185054586d1600e01d442103040d0144000303000090035080441025295a440140341d000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 162672428 1250 162671178 162671209
    0x7030c060e060921030c07020f030f0105040813090e100c140d0c0318051c03020d0509070305060a0b0d0209061909060819050a1709041a040509060105 66
    0x18148a25400c105994001540d10002030040c2c500d1854021206a40d84c400885080384c50700300c039011032044040c003c04503401000140c0c902c600c0c1403159024002d44081058625030588104413800a040c0028418640100d1003030648681c3c450848418100340341d01034101c00600351a101c1004564000043e01f8480722044c260003040c9400050401e0f00d4200f104070524890030000907115590002c80d0380002052800741e1401c0286034018104036010210001009003140c0c0009078114080340c014031489000c00d03a51034058680464219182c00355a000d079074420541e8007100b001d200b00030041c032580b680010003603010000450700c00300241d0740c1c8020240103801410b003480410b0154232581074114001103130f060000c40f0075640c0c0003644000d2049100320b100398040d020300c5508001450b5003811f20550803600910242c005034580341c5452903c2e4000341d2407880104003c22558503a400f40710711141c50250980b64840d141000e000c03d840d801001850980c1200c001440190745452080340c0010 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 162673678 1250 162672428 162672437
    0x6030b012309030703050a14011b03050406020f1603030e062404020702122802090c0901090302040617060c030405071205100920091006030b04020f07030306060809120703 75
    0x1204028280401c0c490031500b203415014244020046c400001110314040344122129051034410190340360880f51181040e056408920a078602c0d171600c20f400c91600726014000c01440c2c505032000310b9509034031030710504481080c0600030900385a0540305030000c20b15283c018008070b19247d060f4420380701c41c41c0344901c0c0081d45452141d4151f01c899040e292115030142c01c5904c80c981d4650300c684d45101d541014040c1c141c242800e1802a145517030641900e5078058102a250749690041409940001034003070b040180d680780020169503903000780d100401807a8084461441c0402e452814104000e064140e10b83d0308005001c00118002060002c440c100441d50070110183e1400038100601c2140c020952418000c5035801d000004070002400020381d81f1007940700d07a00c40107200703082008032500d00940c03031803510401c10300e4001e40240300b681d07400500041c0313429101821000c1c56080701e882034000a80c2c0e0320050041c9500008050f42001c081c0004105511903035540c01101d1091410040400 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 162674928 1250 162673678 162673727
    0xf06030903112b0203090607080d09020a0603021306030605060d0c0203280801080109030207150909090501020d11250c0503010c020606010807090e0408032701020a030606030b01 78
    0x510516605a51030a114141d9441039000e0719410308085040c41002040703482010f18401d25070001040b940340e21006003146003131000907141c0c00140e0b04110809880743e0740300c034070010050341c855500f04064030762a140141c44220b1400c1049000101c3c5e00724400307062070240d052010390383e04000d42d216581085c6020070304103c503800c102d00710f00a420415001d000000380c1d00005000d0ba07444010b11203c29561030145aa0b0340700340d0b41c01e13900d08030409070141e080f0100501c20400d0701d042d0603540441604080c210395a8440d050310480b8002c0006403a10f0350701050300c034a5161075001e02450a4045e544080c1010714941041040d4400d48040e03180064805a01100300071100c403c0a0040030b00030000c2010030740c002c90207919504101c807a10b0020f0301180000301985e000d10422415100300c010030502303d0f078a9603100d18080d400a4010844075144035074030510b6404121940d045042d11500158444441c1c0501038255910f640118003414101000000281d03444000100c122081c216580300c0d2 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 162676178 1250 162674928 162674933
    0x204020f04080601090c02012d09020f10020a0b060d020108072304120203010506191701020c0a1a0601021c050318060703020a0e0301021e03040507050409030c020108100f060309 78
    0x3a403040758003444050256800005901c3c806500c212800f08603600248615551801203c4c058800c0c0b240220b2554049452101c04019503400712011038409000031045440500003d400040c030720085a00590200310268204603841020b503130440c2c4160790350a200750aa500181060744002d00071401c00400030444c2080c54882d240c01d1942e030384401c052554841c1c448a612800a500326000d034000c0d03080c900890308038149558031600b4210700c03d00c511410307800c0080e90494026045141e550540d0240801c0315181c5050005840c1c451281100304d01c100400c444403008084003c002906540290406842c41d503041c101391505881c540c50900d03a207645501074440b200001e000380103da0b20804c02007040c0f0319016070003406020308039143ea0901c510003004041c01e0f4400d02c0703013212110a1642059900c0340344003000d50342042c4180151038640c2d80f02c801103411110001020740000d07000303640000c15940c200c403480c0d40052001219001aa09101c41e09035a00c0e4103100e2507007010b40d1801140107 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 162677428 1250 162676178 162676207
    0x13140612040623070305130819030b040f0b01020f0109050c1c170406110a080702010806010c15090b1501140904091e0302190b19020706090b070305011d04020402 71
    0x9035500441ca2000c40301050640c040f5070b0640840300600801e1800020428520500540c2080b1035070001c199450059000c01c91180d15031131000c030100b45a2102e1050090395a24010f800031000002c50006d40006640e000a140c000d801c482301030349034035001800c3c0100ea004908040d0603401920130210034141c040d00312100ca600039201910400d9a03400180280040e0001003040f07890543c4c5044520301d00003c0b1685544601800a00074202040340c03000550040030115803001050411048920150f1240341d1043e103c0302c4010b403143c2c0c1e1020701c0d80030080c000c0103040d081580500c04c084504040e00010f0510791041800400b81040032078201c51950345e54003d41d00159106142080c204000c209070041080c92034421000f502a11241c160088610725041c041e8a03000802040f840d20cc5604034003013860044030840082c0d03020804034005c80c40364041c010141e841036440c0302c400c1c908203000a08840c0c1c181c1000310200c0b03201c60b140c030b845402c0c0c400050b0003039011240180d5230720002c1e4002c036 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 162678678 1250 162677428 162677441
    0x4020109090f050105100203040b0415020c0a1502060c07121d040c03090c0501050a080712020421020906030601050a03031b020a060215070302030f0103030c26131406120406 76
    0x380035050003540a06000c00d908420f040341c4051b100e207090481c01100c01c0c0d0b100e000e80c2c01600407082c001e020810080035541200250b8600701e0060340c4081ca98800803401c840c0031500004c006c0004a20310120599041040507445559818640c1c20058640d444282190ba200c0d070020400484c40f0901d41e003800308921a420030304004004000c400e240400c00b9001d00f407158025118603042c2a80017940d54056021214040b05990b6440f41540d1000c009488414610202d004156400d1002142202042e55900c0d1020014915401103420900c10080215030082c4a0340c003030f803c84401040390b5100d82c0301c0b84003038951600340221415601d40d00c440700f201c2c0d410400380d40329038400000540250042040141c03000e8000301c0c401941d9074890700740c00303902c0299440c0058140080c01000400c0c0700780c0c1550380a91040b081c44420103400e83c6a2518000e01200e40d9481c180005025414030000c1540324004003d20f0206e4080c00704d64000041403806017100300145064824000341c1002800d61051 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 162679928 1250 162678678 162678689
    0x1b060c0c050f01120c140c07030c0506121b0d0204030804050306070e06030c07030e18060111010e06061302120a0510050a0308070303020c1f020a260403050d020f0c010b01020606060a05070b04020109 87
    0x60f030302c89078044030440e81d5a01e10300c015100e6038038050f2b01140d141090402c584c0b0090480b414030745642c0700c0300c0c0c5101561200c441c1078031840c44140b040482c2e0011178001031004600400b04552600d08040c00c244c204100600103009000301020340169513103469081da41d200641100c42030b00c0d01c0403400d065900d00b01c0750f0583c80e13118612000c05001c090040d901113000c0c16081c1da8030256403807803d5800e42200ea4a01c41e002e59076018100085140c6422841a89c10b0562030001504000391000815940c1a040e0340801c4001e8032101000071001107007c600c0b00401c030032948074401601c0c5880d01601840360300f0f00030701015000a5140d10003102005030600d0780c40140c030030400440300c0c00c0007800250003165281300050090150301c50383e1024814007080c8900d40b10108203507921255401d40700d40d441103030302c1110740340c00b0302c030000b24514402c0280c20301807000c200102d50503002e07000090504100402443c070900d07091058800e550341c00300aa4204940c04003001c040d640322400165103074071441c0c0c4507 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 162681178 1250 162679928 162679967
    0xc0a12020a0c090509062406161a04110312040e130209040c090605040b010e090718060e03010f0e100903030b150d0e030a0c020d1b060c0c050f01120c 66
    0x3d1074409a0b800584111311850075a10182c5400140410500421452090340202c0c2040c1501c0e0f441c2507002800081c40340901038104554a540d040104041c09140c0d100b41d10130030041005100c0010702002251200b01c0140440c1c0f00c2c1c1400c0c19106014a0081d0301c2100654400543d0400058041e5004150000c20030007072842d003032901c212804950300944c0e41c01410207030000780758103050003405d80b91681610340040460031181408106803000306038108200e681c517004091400c18110020281407540ea8041c02640700340c06241c255083c0200080d0010324002c40040740c2e820215503031034040e0303003204046040105428202c0c054580c0c2002e0039407200c0d043d0315803016000c00382c2c000c14071110301d01d04c2030182c076180600d500e443c2d0046e14924008144500407940040c41c1480100e49268440c440d00b80c2c249030301002c1d48481042641041011442e0f504000e400e100b04a07a88400a20f0216805188410942c0000f42011041041220311a44407440000d046001d44601d0030131600702c458 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 162682428 1250 162681178 162681203
    0x3050708162715021002040303080105010f090302130207021207030b01050d0c030c090b100f0509120703080a03021b070302060405212b09050a0b1b0f030304170c0a12020a 75
    0x1000b5043e01c46841030305004d071007030142403440b0f42c685000740c2d0b080301e80540300e402c0c940c2e00c0d020065506101e40c142d26002c0284a82010006954510f00f000c814119000010b07295611441406505540922461400d034860202000060a00c201d031505542d03055442044070b400c03603c1d0403941555240c00c000d00c0600480c0001c2004003440c1c2c0101c503d250102c13135081410300c0d44c2d07209070391415411601307100180c003c10240c1d95900308406c1542d20314400c0740450301015926210780c2800d81000c140031002079000030f0500003120ac2007080361001042c0a0280a0107031450b800507409101d50300c0f03120300450198401848880324501040d0002014605440012044040700d1148a03088070702e908400b105c0e000700680c0c0c3d900c82c2081c1415268094001c03e0418180160404907400045003106900f0f00010040008c1e00240400c940d201c1e06000216180e007014600728107040d042d102c2d403103113044052201a2423850000740d01e80c180d03600b2201c0b00741802100ae50403401e00c111304034054400281c464 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 162683678 1250 162682428 162682439
    0x19120509060708180615010903020d0602030a061707090b0f091e01140109030602070c0503100911040207121d0303070c080606010302160312020409060b0307030507081627 75
    0x24800d80b00d00c1840d501c18072039603294000129202a24100c0801550084002a902413201c08401e21502014181890055500e0340040c03c80000d121301211007a4012003880408003090050201038401c1c4001820500c003415031540d138035525817040d4030025803540e034804072945034240c0d01140b4010160034001e80d4a091205600c0d40d400d102001c9000160200000a1446d40d80b035148001075016900c0d420790502d1070705c8a40c003035008480c05603108813602100040b00c0c0c0c1c00300040495401944d4010503103c94509140c120b0030740860700c46000d140108510000902e41040c882d20382011780c1030010700805800102c800b900401000380c0d805110015009043c4429104c400045400c0344084841a43e05c0307800440982c040c501ca403d610070410a94a00080e0040e1048110030000d120010306065688600e0426503c942d030021840d200d0020600c000c6070b0341070080d5644040641070035040b07410302d0603a14060182c850780e048100310710f9108044240c4a090500300d402c0c018071a00007100c58451 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 162684928 1250 162683678 162683683
    0x70b1e1b0c0312031b1e040602060a0c020c01051c090602040611010b0f0603010b0d020f030c07050c0a0e011a04030605090f0f0601060c03030c110a08040504140105030319120509 78
    0x2409035910903c240c644154207610060220781c41004240c03416030305103004032142d00e9160403070381620241640c0680407002c0c0100170400f0700001c0c0700d03d81c002d03c0c007410b000b03080d60101d448010400c0119033180240044990708001103601e210101c030300b1207490000d801c0c0f110b0f00070007010400501041c000500000e54680c004500f402c1030000c00003c005140c0b08000700701824036036080441c3c00c0030007400108284c2401e0806000740b420f01040151030020302d2000f10034a035000711080e0420f400c0203e000010312600300400c02e40d200d170a8400304101d038240002160789000c14810080d401c1c82080c0d0035610010348170150b44c01594004010f0200c1c8c01d040219030f8441907416001480341c4210002c803c1c4850b40054414100c0703100740c907036481e20351640c2c804401030071000b0340d01d13014880f0380080303140041e0041080d8540c060244090035215410002008155003183c0203035495004490010701044d0740200441742040c00010408401c3c1941560a0354200d112220110801d0301c1c0c42d042080380d0202 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 162686178 1250 162684928 162684943
    0x507060f050f07091e210b01151101140a0e030706020f04030b060303030106050a0804110d03030903030f0e0c0d05070b0301030f152a141812070b1e1b 66
    0x95203400b4009071702c4080710103e100a014000d070b403605280c42c04000607012003001d51101040341002001e800c450b601c86030381c2d01900380c1c445101701c410110980000e40e4001000c0a404000000a2007480d82e0007807400d10303420b8003808091600c0d41e00c5c004801d550030100100c880ca968010b2096449126911403150035401c01e101c15120191100d00052031450080100d0703059420035100c8609014146100b1070f45400b00400444e0320b090350b2020307001107507110710404160314400e50b004140440d451600505403130002d65945180d07400c1031003078164040041006142504142e440450b40141400d20a10340350b055444590580e00c000004000c0c070008090b403182281c010710440e0b003090101d840714000c8403000f0003000b142d40b00c10b0110039160400c20703206c000e4805541c03502c61407815110b620156680e0150401440c120030506602684e41020000342034807603c003a018050851610200e10204e104443c600c0b210001c090003100441280d0505580309100c050102e083e4005030807101079030310051b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 162687428 1250 162686178 162686191
    0xc0305272a040e06070c08090307090501090905070e06010f080c0f0c070e06030606091f08030a0c0303110a080f070309150509011a10050903012405091003050d0507060f050f 76
    0x10107907483e8006100080450144540b5520040d101d18a916698402d81008000c268140940800098000b62074000c0d14003a046080c80041d08043d28500342e4580307206a4803800304d4100e01801c2100603a0003060307500300203825061a09075a500c0c0c401e8000c0510680614098080021440c011f0106001505000340c42480702d100d2445d40750a42010340c1c0305c03000c844140e1700c6020b2031700207a290080c510200000010868051828a44031f81f4000d0868108100302000280900c070740c0c0c1c041c107505005a05103a0001140b030340c40c0ca00414402080e960004060391a01090300c03011942c514400c1e4449003080f80c008021403120004803804401034541540c07081410360030000400f40f921100c19501c0c940000c02055400074400d0301e00b00f0344444d0414003c07146d055580b01c0c0500f10740f030741405e04000b90000102b44109030509050400c00051000750034880c1c0f08400031010b00000300300103000401d074181800c0068440c2181c1c0740403006421f0203c124940070f828a01485105003207451013601540 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 162688678 1250 162687428 162687431
    0x6060804051b06070303020a050d0c23030103080906070f08030109150b09030715020709020f09040e030a05030f1003051c1b1703040318060e040c0305272a04 69
    0xb04041412001d1120b0214078552002040207004d0000e40203500174130050b06142041e07400d240300d1002c80070460b00503444010214206403038912110800c1f070513424071501080030040c19941141c6603540c044c0075000100d4040e04001407440140280d004540c88241e030b01409942c0c0d00c1da111034088014189840400c104200c4a031408910a040d40c400c1c1c1305608805402024118030380031524140d40031700440c0d0750950240d10000b0503003025600090031b52181100e80203540e1200c60080c081281c90074000205160001c0c0603100036507500c401203e400000c2c90000e40c0300d640b20000751220200080e031005020b4480d51a2240a034465422445400b080a49510003100d840c454005541c540342074005200300503590807844001b0a0340050340c1c115002c0d2400b034060711a20040c80190080700d4000d44080340100710a02010f01d01401003540000151400340540e00300300072546200d280102c130050201742c00c803a1071006020204154400007450034460a00003400b0003644001d100404560340c01503 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 162689928 1250 162688678 162688693
    0xd030c090e0405030d11040512070302030f03120f0a0216060b0405090d091e030210110c01090e010303051605190219060e060c010b09070815100806150d0606080405 72
    0x81aa01c05914425034000e0080c41c50900041c5104005202401244041850038880841d0640f038074600b100001c3c0c0c4103001424001d0460041610f44480407a0045c0d00d03500402a0241c1200300000d0b954004d01d5582000280c1d40310b961a120290041e00303c81c240146c0c500c41203105001d440c1d00083d540c3c00d8140e034108140c4c6c030f40d110040c2c5c80b074004020080101e1002ca401700a880016a0761402d103140540d00078000d503441c3d44c00503040c02d1440c407140001594008550340d5140d01801006805403007420505091031900518420a60301480302405210002c81c8402c4c04800b58081c082e0b40030f13403210030348000060741c005803084561a03203400d0f030041880e10141440800a02080b8040d2405622010702c03504124003081120f500803042c41c02d0654980003a44501c0d1038103482c2d94044c0c3d81a4070351201d0341c5415084000007110b80c0402c42c0c07007881d203000c9901040790090704883e041082603410074282124020b80c02542d21600d100700b084035143c4200012900c0c9d00101e030600031440303075040e548078 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 162691178 1250 162689928 162689939
    0x50907080108061617040807150902010207051509180106031410032d03020c011b0f060b040b030a050106030b0612120a200c03011b0504090216050d030c09 68
    0x4140309015207441c2c0c0e4040310203e0080a100c01d01406415a1031401c407100b40171a4a0400310480182c50403030742e09030040352240800500e4840b1940c0400c1003030f4200b10b5800d40d600003d50701c0b0150f119250140194205040e84106024221120f0090142c1f0180c01401c2c0d4a10201030039009208c1d510019241050481480d524000703003034010014840310240590440d240c0359004418104103141220107804414a4a561204c00509030f6001e50080c017502070020300003510b100103514543e0341da1681410b04d1000602c541680020070b80c0c10400c0080d03075911500102c1c3c0242851141c0c41d601d8441c400d64001000b4054000e0700075240310740d4585220781c540000f4401e00710741e004e000340c1c8117030090a080c0841001c0306010b460303400010719080006140412590314414a0707002088601d4004c074452000ea030800b401001e0340180c02420340c40c980c5591600041843c0264003030415060340000d0100e1200c030303a004244207201d030850107035100500c40100c090011301135100220081030b404c4000284 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 162692428 1250 162691178 162691187
    0x32402070311010c020d200304120c030c060c05060a0509070f0b04140a0e04030809010b0d0302060f0705030c1803120408150c0702090a05070903051c1e0f0c050705041104050907 78
    0x1039460070349404012861041704070010300301f03c1c02c1082c0c0501c07043c400081d499404030000c0100c14050482c6032a0f803400c50400c6501040d041d0080302c00d000d100303c40c0f040010310004049910000c4448006442e40300c0c2056641442025030182103012100107010401d1041d00b0000e00032102c4a00b10415403842c04000d001080c1424400da040c86611900040c004c00d0141130001c1e40148180c00000300103190200003503244040000030b40040e4029810040502c021751401c035048003180c1030080c21440c0036010030703940d0300c2804107185420092104240058a003009101601e44c454036806031a292240311017070380c130310748040c0f01c9000102c0000420702054408040ba200242c0240031451b1503641d808503d4054040604031070204181401c002011070800d000203420008000540501c208002400030041c075400c0c410501e0320f40700c110b500f0200301e400c80110841c1c1701c0c071420801203e02041c1030030340c01c2484a512842d0000d091884500c01c0328031180050083d01d804a03a0180140c035901c0040b503 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 162693678 1250 162692428 162692443
    0x60115050406111002040f031101020604050d0c14060108030c070f030203060c030408070b0702010221060d0b1f06020606120102130608090705040e0102030f0f070504032402070311010c02 82
    0x305100304400d0081c1ca01ca00d40f0002242c2c407100c200c4141844e0380c001c3c4801c80e80b09522084032480e50800505c2001004154484e42d81000d10052144e800c19885254170b40403000845018040e03121005410000c004080c2007004102e031098404a41e5200709190300e0350300990070183c0758002c030b020200d038090341d1182e440292038024004000310f954210042e00581e00103023080d03a030740c90140700401c0000c68008895128048590002d81c44440d0400030100c543c00c4410102c0c0c01c01c05003010412181ca40550706c4450300e801044100c095200c0040010300c442640800c02c00100c1d80030004078001c0d400056090150406440503164600000c062500f01d00030300a4248203a20441c03803c0254074452610769811180750020350b1800c2d9a00e42c009401c850030314011240594000c4104440501c20002655004030300c8200040285001d01c0c00500038032030303400000c01d8444035001801e9a07104020b140d50000502d11f508541c1d0301320300e0901500001c4507042010956007089000e4140030310100700ca8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 162694928 1250 162693678 162693719
    0xc03070305060c131212030501090b030a0210050f04030b1e0705091002010b0406090f05060a080706080403020c0909150106050906250503042403052e0f06020f0601 72
    0x3040e01d620f981408000590160f201c5041001d0142008600585003041d4078058600c5881110580150404060706a5805130f10044620b8504458810f241e14003144506820368103c943c0401500800360984072801500000c105180d008034000c000c00030130782ca0040c060614210901d00c50b500c0e441d0501d042d000c0445c0c141d40040c0042c0700300311290402590b80400c54034207000210303003040ea21012408852899010f00e4100d61926220001c00429200f604e41001c410b440744030205007003a41c847c2e030700d444510540042001c0c040015080c584207101d81c1000610040c41241c142c100380031003d1f1b0712117400c0610441c000d01d400000030403c0c050000c503401418090111802c210800a001c0b5600120003e91002511055070360360003e5170610040c00a0b102030441e0b080348202e108680c4944500100b0a001411714207002e000c401c8152440030083c0503610760004445401c40c10591700c0030791243e803007203054252801002ca030752900499001d9012070306004541d4182ea0381c076809001454010401c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 162696178 1250 162694928 162694933
    0x140a020a03111513090f0c0504050120011b0f0e010918020408030c03040f0902040b03041509050d030b010f0206011a0304140d120f0213141201020304060b030c03070305 74
    0x4000107550320004451040008040c03e00301d4040f180824070701c1d0b0164030020100d00300b021040c09000020f00c640502d02120003804c102d1060380710000340492165000301818040c9060082c0b0500c0d004010180d42843d80e0310003444260400d41c0d142154442801040d03010500030941405040d206000710384c007400301607441284442c40c0c05e0941103809100008110300c56020040411840c10400c020b00b0100600c078021036441e1f00c2c2c414014920a0150801d00e070640c01004200000ca03414000da03a0442d4000340d00d0141e055001c2501c3d4001e10032500b009210303000c1c0308111400e043d010740c070041c0c118000b038a0b5130705045000d54040361520746c01d0207a031030340c55040000c002090529070003030360b4810312507000310064400c0184110b00e0b000080100301c00144100000002d1003403070340507a60f0780c4100640e0943c103121200c156019075800500440380c480030014031851f119a030380c0303a600484c042404000c55480c01c107402c001c0c02600d0401201e60181c400e54880310b41c075040024144040b690010007 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 162697428 1250 162696178 162696199
    0xf03020f24032d010e07020f06010905191401090506030c13320103020a06050307022a060a200c010518211b03030a0f0c02061312140a02 60
    0x75a907a5810241032288050b10030088054881c44403403108400c0b444041c0074941c69131400081d0503268900034222000c41d0000341c1030380c611a1000411a05403a1481d1010403250350301d00724801c001100c405d000100906001a4004480000000c603040c0d500d082000d010035690b1905140d550500c111000da002206460000841c0200b035102a51110f60402d50002d00d045082c806031400c50311100d120b5400c9011401007045107040c104660042c501c40c14100e04500d84030300040d4607408841c101100b424038018007001708020402e0108401000206403035104d020310080207100800715a000000303a880a03400c595a08400503030420031803c16500d041c9000c44c42210320350400303107542c0310310340100c8121205081c03900801e1410983e4842d10004290715070840307400e02c0c80d1010190380b0354025041000762007100e55009007190004461410004582404c81c1b001c90241c0c401c8106690905003101004203240100380300740c18606002e54030081c0c1142c0000800c984400107424001d600501066 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 162698678 1250 162697428 162697489
    0x3051f050f060f030103151b09050904140106080a0203010b0a0e070c050313090c1d060301061805090705070b07080712110705060c090109061b03030e0a0501060f03020f 74
    0x40301c164180050314641c1031424800c1c8181480c1c01c04c0c0c1040300c0500b14980d42070b10301070341c910882c50842200c3e080d008002410500290943c15103000d45070080c02100001814003102240301401881d4401c001c21000b903490f0450358603080717174480c00c80c82542001007032a0b0780d00c0c00800040660390440e0043c03a8039210654207031404007220104441a000602c98560602901d803810001049940c0c40880c0d44920f200d80201300c1c2104400b280041c25060400030001c0d212b540640b41961090b0030101000f041c1c03103120410006659000316402800b80e010032590303980c0300010300640c51041c040303017000380c40e035102c1500c05440481d10840001c503895040c84d00041550454502c0107500b041c10b81c500181c0351078507401c000c8c003210b03d40b07400e4600240d05580c07540e10545002c014035039031a00040451800d070041080032803c3c0ca01070704068030b52800d0309103200b05101014515a0080007080403070303a03841d0055410f042921060344208030701c0d02280310f1801d058a0071001118104589a41e040c9540d = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 162699928 1250 162698678 162698689
    0x709061d04090507090908040302041d06150301020412050d03050c0a0c150e010f050f010503010b090c0304050c10031406040507300207050c031b01050a0c03020c04020f030703051f05 80
    0x200801e592500c190341d8005082803580c1700700c007086e034000e810300b0345e1321801d6006106c1a44c41000640f001e501c91103003c0e5841d8100401c00d25000480c00c94005444403080c00042d0190040303801000301441c01141e1103041003400500800a41d88544060159035070301c8440708600d004106065000c2101960b80000045800c8a4a481c03a50b0364100000d200b185144a2400c41e510500002d1402d82c4d0b072020721101002910031240100412002031002d10100004543d00320000703040c200c045040440810100442406800f100c0d1801501041d0341c142c4401006000c0c00c42010780c0402d0713041800100300c0304d040134024607201350550b840740c03404403a00000040301d880050b103002c0c0f80ca0031001c4903816440c0f064001000240d0180004102104100041600f04440d203500a060020101c1c401e032110303604101500e00031505403c0c14895580c103802e080e401c014801c3d1400e64080e10020321200c200041030041d5002d442103503010842d81e40d50b1140c0500c0c50340c440700402c000f00e41c411810409807409 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 162701178 1250 162699928 162699941
    0x3050603191a0a1a09070c17070210080f01091418070b040b0c122125110d09030203100b01020f10090b1510080603030c0a0303050709061d04 62
    0x580d08060740302e080304960180c5000140c401e00c1840707445600001c0c040300b840552083e0305100f00c0d031120050070101d0f4003402001c84800d00501900314100d03000518001001501d40c8250081c0842c14521a0840700922100089034450301a41c560400410100600d1180240110011103c60380607190b8042c02c521158038134841c0f49440c402d026000c5805541200604002c2001d080d070640c80d101905070b030500340706010914028002040c0b000c5081426030300090381503140101ca030b1035190b465405100c4050001d140f81042400740c1904001c080c680e0241d0300080d91540b010075200a04040d80c1c080b81e03400c2542c4400323076141e4002c0d220305190001c550710a101d8520140100d030049100303d4525400c00021800204081d030751078010354281701034815020751081852244580c5c11004030000350039035884040980400c4800700001d070154030104119814403061404507288900f09147c0140540b40032615140001e50104001030a14068603603030282d003004c07800e940d2183d81c0400901c0000c18a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 162702428 1250 162701178 162701183
    0x3061a03180a0b0c03181c0201201e0c0a1115090f040c0e03070e09060c1c0f0204030204091b09020a1d1906021c0c0809040f0209060a0504150305060319 67
    0x301c8001406d11002000541540c1e0319030501042e1020540c58080d08461030740c1d00003120000703044002e803008140082111401c080008d0302c090a0442201c800c4000d0182145003142885001803040c140036044c80d440c0414034044503180d068a0603100e01e0003081c060340c1080f43c0c00820030141514189016003010070300d00924030700005200e8940000929004255001d00242d500c0c0d4000d00c004003000340006a40802811495880d051501e0310842c82010b1014003121043c0c1d4030302c591111118250100c40085800a000340300c2e581107070401040c0161544034030f02d40e10100580c00243c8107a5402070b10301101543c1c03205101c56031403900140c410b8225044907944014051540c09591980f00440d2002d002658001c0030035030141c0ca030f02c1c422100501c1d80c5600340507504a188001030360980071a480c000d0156000300b1a4088820700034040c1c0110250254800c2020611112869001c0e0240040301c0740c402d041d04243d010020150700b15070342595a0354050300f11140611000001841c1709110320b1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 162703678 1250 162702428 162702451
    0x30402012304170c100c080304030e150a030f1a041515050409060f0b030a020912030a0c020112060806060607031101090f050d1701090c03061a03180a0b0c03 69
    0x3001c41d5030100403640250845580008040061900004104102c402c0c19400b92440d040c000340380880908108201c04006000f00030000000301054130800301c10411020140c80700501000c45a180b00c62900b100f641200000d142070040c18207802240105a100c850200134002c140900c03005220280c1340b1349449206e030031450100012040f5035800f100e040c01034280e603081e45860900e102075064030000d5001026041d08884140302c68161941142e410161103500143d9500c2d0601c0410002c841c03921141c4054080403641600040c1c01408071038070a8402d81c1d801350101d400c41036138012294903000700c91480d0f00050014225040c960001c1058500a083c5030442c00f4040760b0250075508184001c9501c003803502000400c0042c10401c2c24480031283c100b6540c1c494107050f00d054400b1051040c951800e0f241e04000075258007035030260014008850720002c900812000300d9030150300c107450103d90825225141540c00ca40450f02000b0640c4c0009800499203c0b050b11800c0c1c0e400261039040902e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 162704928 1250 162703678 162703727
    0x1706010e18071a090a0608040506060616020d0501060f0b1e030603031b0a020906010309050d14040f0306020406080c04080706050904020d0504060902030d020c09040803070c0b0f190b0603040201 85
    0x1e1040c542c0c10303080b00f484410380d11140601400043c05240d0b1000062126405c01d01001840108580c2c2d4041002d4901545554800c22110400032130000060340040700d558005c2c00740401074101c0e806903480c5220b80b030500d5554903100c091034032841e0704885180c4055952444994100300085800c048020308490800c2251000e0644942007508220005e41c054940c3c0f03000c41c180308000b141c0c44907003401d04201d100c5580d2030b210b0701d40890a0322a07003080040303021842d0310064802960054407031205c41c00e02c016100e00d09400254014012031010550820000d41010100d10440f0203690942e4080c0000c00d24102c1c040d2030640080520561194003409404a4050382d44103141c85036009003400700703034415140103140c00c2c84216105401150005500322001c0d4545020b06a00568008001c95072652210750071542a005c06400400340d40182c8240601d0740b0801081d039000e030b16804000d84407601c81c810b081044503003036160684c21000502c000b80256014030441c40859040c1710600110 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 162706178 1250 162704928 162704939
    0xe0f04080c0706120c030627180303050f0603030903030d020d0b060a0309170c07170f0105040302070303180315020c01060b0c070f090506240d05010f1706010e1807 72
    0x40c4010b0b03801c07260008000c001c5800d038200490103520208401c5080c10401e181c10300e01c4010036080302d40542c21303810348080c0e0403038845009603001d0000c41450b40301d080840d15451400030701034482a5100100c072405400031440307500d008000c0720f0103020300800541c0341c40301c409402c00180d08510040c40f110366032910300001139200c0b1030040c095003c084c0d80024580c1440d140c0000041e541d24a8603030049005e1191040d003040c009000401e5801701e12000c007032013465540f418600520010b00311103650a02c414402010f0700040c0100c2034038460f8407070301d039842004001034400314814840034010410140b01440748484c60b5006021906c2e030701e000031600e05c0e150000500d01d030703100a09051981d4000c00c0f0030802790203c0442107000e02450101440304e420641c001520311075010489800d03a0111540b019480c40e403441c112400007800303030014001907030740b60107044041c44184503034603070200c084020819106020400368169a06074800280c179440c3c00c140c091881c2040024141d2611852078040765 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 162707428 1250 162706178 162706183
    0x40b1315020309012f0904181208010e07020601060e0d14030d0e0c28090501080102030105010f0315060e06070b0c0a0906020d09060e060d0203040510150e0f04080c 72
    0x14918a61140560b40c0c0c2464440182110286441d800c80314001034260b10641c1e100058400804494544060b201c0d004040018014034040c0140c40381100b00302c0882080241d098481000f4009035295000c8580e42c0d00c801c2d4107a000226010001600410010f105a6003e02c821079000a00030b0300204103010240d8032500c0d002c1450054048d594008520007000390303010b02902004140207805801c00c01b1816010515500c5503403c900c5103118011103411141e80c0ca1040d41d8014030359845c0c10720940d60354848030740c001c2d8000c0c05506c1c0000d0030807424032800d60181c01580400c4071106011254140b034640304549200340c480da260381c403a504104501c003190031981700c180202400c0500558582040c40c024040280660148040d5040381e800c00d0f0007950030010100440c0c1182c24160341c42504600043c415204804100e1041d61010007400305100c400106a40011880361040042040500380052629014400c01140903001400619148408044140c0082c46520030b00d041800801500c0d0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 162708678 1250 162707428 162707453
    0x7050312040b070903050a110102121201180203041505040201050c0106170609070e0c0304030504030b04050109062004050103021303120c0b22030f09090507050c070f0e040b13 77
    0x1461200000500050000b101c0e00240c1008150500e401e21030b01c0d50381c480d915032031000805007084c3c112210f06880c6900030304c86000d404071000f18136681d80d01ca51000100c0c1100a000c1c90000c942c0c0215102c2d4015803d200322400303250840d034150800100105c00c0c07006080d0060080303042040a112500b200d40d0240104405896048414815120342c0b0318182e1070810010072040240e800004100300d445c4a00400c1c0c0c2d08242c02ea40d0495480d544c6040c141c626100719440181001004410482480010740c070031000c0522400b0140881030613007240700300c000c038001c0010301094405c000c01c00c0998040d900401c6001d00200520045564a03150300e100220ba080031180410899038600040202290396540e00a4044a0300c400c40b8212081031845003100702001414046c014009852640c0901c0440000b440100e80900151901000090458000d1200038906206543c408110351507414410401d039444d048000a4a0f6a2510b80314002e0002900410740c4030484500640450009107281d03 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 162709928 1250 162708678 162708697
    0x9060312030a020c060606090109050909161d070314150d060501080d0f0203040e06091e01090606021002030c030f0c0d020c03191b0318050607060b09010b0304030c08070305070503 79
    0x180c6585402e001c017801d01400401c654890071041000405a82c0c2145c01c00d415103200b580d01c0703449035859030b540358580702d1102c0000100c0c000454000810210303880102d0480c0c0c3e1010400d0400d40c60304c80c8107606032a03041da101c01000d00e45e0000a6283e030328501403044d81660051609444000a89030701c0308690080e042852645c12008000d51340301d03089030b1400542c0030184021442c1034548900c600e003054016040910465021011034180307101000440398401901440c1c42e40c5594507d20b100003420fa03841050054055207510041c2d4017040d1003501e2090054520f03283c50b6a0320070040401460f0300500130340c6005070610000600062500c040d140703120f01c3c02c2c01140c0d202142513184103100b5109280b00304001414400a9400c595104001001d9070716013850b58180030301101d11200402d141c0c00050708040041032031018051a80c0100d40070000559203585175980b102d40113030440c401220040d020400500d08200091002e00043c20218041c0c5800d030706107505c90391018150390103a860f0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 162711178 1250 162709928 162709931
    0x30709060902090405010506031905060d02030f010e190305030a090503040b040b0a0311180405041416051305010b070830040c14010e040b0d050a05030703080901051509060312030a 79
    0x40f0449080c141304003405003c08031a00390540c0361058507403e02c150350448480c00c5a8032080031501c039860b6070f6406100c43e03900406544028070503007890ba000380a0b00c82952102e03c0340506030f080850803100c442d072131260955641480c0d41e4070703e4642405040092401c440a1204000c0000e0302c10b0210081c20140c6001c55515555000101004068407030740a258060410b081101510403e90f01d6140c80300303544103850206080c3c0d038500701480c118543d40307c448580d000b141031814025900785c046100350b49003210304441109113003030410208c4409001e001e4071908208009404034180f5006000314400c40c455204c4e04540c2c03075460742546c401640144500b1428841404200640340300014003604600c0c400103411060113000900400c18490b400f40625501d0b129040c094480c075a04404d81500082103c41408043c038100356a9400004150005107412021505150341030003101d0240080b87c14a00301654034008018040074040c209030351500c125185428440440d601452103003032000350 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 162712428 1250 162711178 162711187
    0x30105042301060506070201031503170403030206090303010302030601030f0606080d03020901020f16050d020f0d0515070f170c130612060e1b1b0a1b050f010f0509030709060902 78
    0x5445680703861106801c5140d05150050110340c903401c050311446a02440c01103203a60103046008802e01d1076070809002d200c0a40007002c21f00e0300388002070086030b01c41da003265951b54800c20116184d000a010003507050300100010230101d01c0d80705844008030b0044100003006d42d0340b056002c0c50300a01c4500500030a0300420351142c15030701030003000c140c6541000605a494203081591100001a01841d403003144144c01e108103540392100f803041c141402400c00e212500c81c1d800d10503a034500c0102440985082800064601441003120171001c81564035010130ba944002d036040c50482c0018043e003040701040c400d0914140c40728002000501d1140c90710500c7c440e84001c800c0555000b40c01490017002603009105201901c04a1900341c04032090b02540c0b01c0461070090160241ca80c00c001c0c03031900c242d940c880c061146626404106410714402d01c40016036610510083c0c18140680c3c40c04502e1903800ca036480c0f4043c400034074458100400382d80314192551600804c035881c030340005400d198040b4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 162713678 1250 162712428 162712463
    0xc060809150108011e051501080703200409060b040f090c1b0c050102060703110306100c1a10050f031f110706060807050625060f02040305030309060a0e15060d0203010504 75
    0x1000c8030001420300d05c003440203241684094000f07282496015040000900004009a00c02c0c0d0220480e40c203031000300003000d102c548512030f10b504280180d0340f189150290014018065000b10b5048458113100490382c81c1c03030004c0e140010920882100c2c02e0180c80184008901481004140d0081c481c04150f0341060500000900c0c02000800784000e15113448100f80740c003842d6200356540300f5011a00010041c2802030101c605c0003050700001e0002210b4104001d1341e2503c0e124403403203603844403682c4002c01daa03003041103035200341a11031a42503084200c4200c8a4801c521601c01e00109000740480c2c40c150340d01011075180d00107102601c2e895a1003200f0700492105014485c01400304440660409004191003031080800802c446082c0c60400302e044204203454101443c3e180c00ba800464686075207050031341c0c9a41c0202c843c041c243c0900703000a184a1043d11803601c1c8015550b0040c1000581c2c1c4401412085000d8542680105541050070069409024061145104481ea50170300d12640 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 162714928 1250 162713678 162713711
    0x30b0406050c0301060e0d0c0e070818031204031b0209010801020c010f06050114181309050c0109031725230601032402090409030f090b070c06080915010801 69
    0x540700b110b0104041004000044d80505694850720381204c203640300841e40d240405481405601192003541d41d0b0013080b4126800414003031085c4d0b1662040c00d0940c91842d14540c491103003480404410203408041000319100e103201018801c00c034407407005c0c907041f5a00020315100090380b11041070b0f90001051700038030300c00703000c0e43d00d0b41360b0b46a0f028801c450130000080e040400c505e2b99003106040c0890303801d503403c021102c0c80d00c0701603004e80084040708214500c0c030040c00d5503400c1656544944103000d0070135445501c031441225044031010404400030005054183d009011840001ca4030030078488814214064403d44c092003010201904003030300e1040c00003c602e00071020b244c2d0f00103200400209003811507524044800404544140d9841003407600280a0046811740082c40d080c0414105034011450811640160304d42242c9a545c0d15102c518510800c0c10013403c04010100411015010b07800760394014818409584003001e05a00c1c0c20b8180324268420780303590303440754008151070408 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 162716178 1250 162714928 162714931
    0x6030518010509240603030d02030601180305060106030c050307020c0f01020c030102030a090c2324120702011107080d110412060605040606110d3501080c010c020307140f0901030b040605 82
    0x1001484c0b510351828000103900c80c01070007074030001142c00000064240c1e04c00c602a400c40c040f0054142d03242c03600c0b401c03c160313283c800340241408a490300d0b110302c62141c050340030750b4410442c0b5401000b1980b150070a200320800c00d4900d245c150321460010a003213503401e001942c410220f4500010f0040c1c1d0509180104413401d61008072404041103e55400c0072000702c800c5200141580c0751442d0302d0115039031540c40e41d1550007480c041c44021a51007000b41044110a004d1001030f4000d00c18201d5056481c1011b229001e0020521501001074400d40784507a04131490a2003800380c0340b170404e990345159030025031131340404407070440e9626014005450a8400e1902400d060f1400048041c0791200b542c5d0349490030010b050911071880e0800042481c000c0050600d0002c0c42040c0d1001107140f00380786002d0500703000760704107401230038054050395104401c00c040447e0000c00070112a49894101c414580c0311454135608050004034107413807611000b02040c000d61141c0d01000c040e1400d4240a41248e00 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 162717428 1250 162716178 162716233
    0xf0215040803190e0a0329130b01060206091e01110f0c07060c02090408090d080c030c0712030801031b05030a0308091504080d0b04090203060a1d03030103030906030518010509 77
    0x8900c444c2d1126a1100407402050340d0b030101c50030125806182d00300808101c40c8040a01c14540c10007049a05150540c44a140703070711a010f1204980d8036044140d80354141200c03e003940e60701c0f0f0940e600710103021050304100c1b1000903000064075070803a0203003180f41c1d102c644081e00c0500000b98600198001300803034801049030b450304e2542002c0c1c40d40024540d050240024000310f80208003099166500c50501300359a922000071581c030f07122030080307540f2038014410a9100e80151800000c01c29400706c3d6072241154141d50f940550781c00c590f61034083d21714905080c0c030f0000f800d20011825450801c5040300e03c03402512402c105182101c040303031a02291400c500a090300403818000090813070019500400306005010461a12500126004000520300a035161041c0020305c5482105503204072891919841c5481d20703450b4020440e9501d1000b0710005000800d03072001004668407070f62160b030f0000c651007108107006036040f00d12403d581c130a484400d03190700207005100c041078066082c80c41100 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 162718678 1250 162717428 162717437
    0x60e0f04021e01120f0e010507030f0f0e100e070e04060f0506030c010e1012090f02240409110c0109031d0a0b041208091306050103050f090a0f021504080319 69
    0x580440001e001e00216540c007807007180ca412440c403110200c3d0f04408580386d03548000300024038107114020050111074245080f4136181503507041c100e0348940104d06603c1192402000c81031a00181d140080c10780040c0c3c1d840a00034500c000c500080c40c141ca83d80500d01071440410050080303401d001c2214000343c0302c90b101e0b5021041c03500303043e6000002039070b000c0710803200c00c903a0a0b00a40c040d510868401c40e0404003d00c0e098a0808101c80307003501e101820300030313204040c04903a01000812401003201c08a03003101c0003403104100f640304c0754104000301c0d0076504289003018005000c490a59903502421008138200340c541c480e52203070844034020b9028003124480c00070351929000803018400d9000e02001a4603070b800101c24801210104c40200c840a00498403103114040200010550342c060640064101408aa10031203007012071800f039014000900209801e42e59060096004084105e800c0341c0001030703000601c61100c0140000304198001340d03680b50149c1084051107640c2088820a00 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 162719928 1250 162718678 162718729
    0x4060624121e0504050c060f04140d020616032c0111070b04090b030106050a0608070306140915010c120c050f0625020f03270411031603060e0f0402 65
    0x440000316488140b000c03180020356445078100103003003012090075142c1041c000a611165a00058010400c4070405c0f1850000d8070b5288007003000c0c0320f0503070502030342c0104180007403445480d81c14402200319100742029011142c006950303c0d206020b0301011441c21070403907400d54003940c22a1184441000c1840030306601402c14840504500680c002d41c0e03246a6aa00301c041187c8095005c9c0000d030200819142600f60b5800340101602c00440300000000c1c28240c3c00901410320348416016410000c2410405903600d650003a000d00c220045c0b181003000c55180c200106560200b0308103400312541c0c521901035001d0a089151a2580c842c02d80e0a0b84880c0c1045240300c0340309403444078128968590010303925581000c0b4034100e04500e2641c0a8080000c40103c4070300115510f030980260341110043d2002c45004100490341e00003040c814441040000820100545400581007619030400161403501d03401103044620040b01c004200600c02e0f000d00c01945403001c2c01140c01507001c1d126040c035 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 162721178 1250 162719928 162719951
    0x60d020603130203011d01090c060c050c04020a030906112a030301060c0302030d02030109050609061e01080703090c14030f060114010513081c110d0e06030406062412 73
    0x2034071004100c0c0340074240e580b0107501155003e401080d6030045490702000c61103507038200c490007407032686422640c4e01d4000c03000291040c00340c001e542e986a00701000e0a20348c0340000c2407002940c0096400d4080541d030340d507110300144452069140e11030400c80d8040d10784001101e02c0700d0322415041c180d00d11380460802c0c14480c9100000b281c0c10b484840c9010200400c42c0d00e426861408bc4010707144405002100109112240340c1c0300c544601011a841000c0d85c9504044c40745082d15040d103039400b020395611403d459409919840c0e00541341c1d00d000106868a501ea000502140d03030041d00a13424081510403480ca4100300c4c0e80c095105250150405515100040c90700c10000c658240c1889400319150345113020041c03407d00100300c14800d568030096840420000184d03a0400e88011411a100d42c070020300c8000358624030004151640c41e21181c2400400ca5217400042040b0350301a11288041410b50702415504524000d502e0740310319020042c180074041e9510010601354092400c0c1e606082e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 162722428 1250 162721178 162721189
    0x317100905010807270b090406050603011a060a110304080106120215041203030b130e01140c040609051203090411070b090c091302011e020d1e02060615071509020405060d02 76
    0x118810901707020131080712071911140501810001568410050b10402c410300c4001c1c1c001901c5400224000c03c940e044400f040c403200c0c6840d001054104d0310901081c01400d000315600d410491075401100c3c1804e40d1a0030140c00d49205030400c0c90301b01c021a2901003107041c51215a0680185160040c0c1881e0070010514014030a0110141c101510381c0c035416429100c949114030311041c5c020782401000c5001c4039890191000450f000091850140011501820002600c095401c3d581d100d036003a43c9802d08100c800602c90054205500003040001c03043da54a11075294028800c4200307948441050500c4020340200030919103007030304105e448411640d0b8503807440d903116100da80012a020f01d180012039480e0b400880344c1443c1e150b040e40150700550000341070b81401d40e85a48110708500744a244001c031510500e41080981e0111012075441e240080d1740c1550036004918a50070400b0381e80703a104a07185000d074103051142c0e81c1c0c0e2400055041c030b805405d0340140281c4510142c800307160b002c2034 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 162723678 1250 162722428 162722459
    0x103030509131103010b0414010e13110408031305100302090319030e0306010906090b01020a02030d052803090c120201020601030201031a12061e0405030f070317100905010807 77
    0x2480b030a5100300c0c504110819070302c020016501e03901d68035100d6840d41240030055005006d00e00702c00c00c0c58008a41d040d889510040003030140503040803000750780d81c1c5590015214803600300100c24818080810f000c0002c101400e075500d540b03040204440c0ca480c0901408140348000501014010010030f4450384000964a8021900582d40c440e17035142410304a0b034940001502c264580910400040c6a51050300682c082d54040d560070002c40500b28016a9078283d141c1d80290107821003117958007100d01480142c0b01c01039116031240c8203000d0000600115421f80068000425928040107003031000710f003040702c050400c0b44a0032014480c550000b0b952000144002410151100080291078506041000007188042c00d168804d409844040c0c0e00c9000481e091515019001e6481c2800740d05003000b01c0c0200c2d046400b5502c0d18109410a0303907143d03c0101c044c0c051008454101c503401c1d02e100f0460b445400a068030101083c01c10075140d045d99810b0384400795607480b06105100e074199000060 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 162724928 1250 162723678 162723697
    0xa0e0723010c02100f02060619050d02151b0c0a0315050c130905150405010302010804080322030203031b030c0919122418020904030924080f01030305 66
    0xc4042404080102d48420745514002c0d0002100321182880329003010201c0d00d800c15680a0701d1590317982d60103000c107013401100e000040f80c81104c0108043d00f00400c17080015800582042222039040e008068a42e00031101072280c8000704166125030103043c0130403100c403401101d1603c211880d40d11201e1001400600001016658001086603240c60204445545a0f00e0203100303801656410b8000003008122040d8081c043c2e450b112034124946445802d068a40c16116031324181c642d6203501c01140c000425800c191008000504a080c0a400a03051003a200342e0080d6030b00e140c036462641d20011070391101100501e042c018403072140e01d41c1058486180080c1d0324061001031119500750790707a178a42d02104014096800711818045440d55000707542c080e503000e2007440540e9401c00c1e42251140c1c2008a800c03418240350304018600f0f040c501e90030900920705020115141c0c0360045080c00c0e081000d110409280701c4250031140c100c00c00e95800920704098444940c95624041c20a1003010b000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 162726178 1250 162724928 162724979
    0x100305060117010b0a02100b1005031b030412020c0d021e0622050307060516060f020c010f1505030a050c060c1e0d09050904020a030b1305030c0102030a0e07 69
    0x82460740305640381d40781d0007400e010007802c03565910718880c0182d201400610041c010450903041903405030041c50401e60b030182130001c2e81c6200d00422101c64201400200b000d4084032502e40b00603500402940c0a180240140800c10740d04501c0a45081c445004180c0141c65030303036501001d6501c400804a2440034000c0306041e1004080000300f0502c5404044003055170001043d00440d8a056000c1056070b0741513088500f11034861006803014090850010101e40c00400700030000381168010040404c40c5440c00b500f80041440d03203d0950300c0181101240b603540f0300080200e9010054414014a02a005400c490700b10703032981a110780090000c540100710015000702100400c00000c3c44444030080380b0501c16040c592a291604998030700030340090101540401e5038074003000c2c8607004903402031062600e146183d40b11000820700804541440010342207003030104a050006200c0c0d4441c1c600016903915058400f142140c42e95941405903a202410074010300700c070300910340c081c15000f801 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 162727428 1250 162726178 162726181
    0x220b0105090603010b04062606150d030c080a0e01090f0503061b04030203060408040e0a11030610020c030102120a0e01090f0818060c0307052e0e0a0b100801060b09100305 75
    0x442d0140c10340d6071200d80c0281c82c22400140b62880072023010301031010f0212095545000981d2165103032410340e00b50180d600e11050f80c0ba020300d4a0000031082a20a003058040c0c200180c6417031466400c240f0100001c80c4054126818a60b404200398024098500e503071244a400d001c04a40c0d82d40c2d00030300c03915010303640c14070707081c0d07468000c10070740d401190b00504562141c945494100796540040c0300b100b024805001c040740c0c00d11604d0080039111400000c215080d0303a41e074001c103c0b01040140c40201075015502120450762000c0c002007508541e180308924880c2429141103003154104c14203102241d2401c44100001030b198401000035039000100c460310b600f20b4110005c040d104026149030b20010020341ca240c030035000b00181440f01e0040302622a030882d01410186115021240d400003140e41c01c805a140010b06c4d400703124942408402c076041c166180d41c640c8101c0c84160380350105440c4210080204000074001c1c1c802034201034518905214610740428a407a034010310402c00e1584800 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 162728678 1250 162727428 162727441
    0x80904020c0106032402070f02010f1116170105010302030303061e0d0b0708100501090513021303030905100207050109090e150c04050301150302090106030c09090e06220b010509 78
    0x8040d2031045103940020025107580b854044da5105400410501c2800808056500310503240301f51080581c1060803036a014103158011a41211054074032418028000348031351002004110b440c640c152040704a008090400307040808911013101c5030320791a810500107000613200481520b410030020384030303540740d03c4007051040700b19440d0300c1c5110782002100346644148807080003214041c1103541c07500e0000da01e070b070100942c0030340560140e1740c04504102c5041003035040403003c2110181385441c0040c2800e08060b52851618030f00e620039000980515414440c5140c2400c501042400d18001404643c0c6060000b03818212144503038074950f5900c11070345940b07410038444801c02070503041e00da480c545802c050400700c0d908240202d81c000c0d840d1086883c01042c050160000352600101a003c0302d0380703002c41c103c02400040e6030840800840000016418aa5004101c45003054002418541c0351040038003076242c406c82d807400803400e11481c4103000310700c1c0b1040082c1500d400b0f40e01c0c0d8101daa01c01 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 162729928 1250 162728678 162728681
    0xc150d110c0a0b040b0a0e0d0806030703020306010f1d1018090f0c030b07020a0308061201060810020309063601230411030a0b2202060c0d030609020412080904 70
    0x20781a45190b8001c4244000400060030240f61040b40310b0401078106031540ca0040c012a031604407081e0040d440f010001c10759500600b40720790f101c04e005044660840c1c0360342c003190615400780d20411000b8140752050004441c074054410702c1e1341c7c9000c44009140b41c00007803950b03071110070f20807100d00758400c400c5500c2402e500d40002051a42010200310384c14000d2400800740000c1c0d01c0b090314214901008100071510124a00015503013690303407200706403648001c20060b1140d414107a0203540d60348400060032801401407040b0040344140c010384910b801c41034541041c400401e00c5446684502c1515070b54007808952142a0308024480345c0035410901585004041240919040301c6148503150b00315649081604c0c4201e00c00c0d450141d4002482060650300d011841c0c1c000c150016000015203160110f9800603a14800d54440e1074000c081c80d000304015a01c60300000c0f003660071540200070055090f0040c40010407842c0d008516051500042c03c2004050381001042d03c0000122001030b0b5a60303 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 162731178 1250 162729928 162729937
    0xc0f0d0222061a0d0c140708160210020d031808030415060b030c0c0118020f150702090c09040e0f2508010e010204050108010603021e0901030e0601090e0c150d11 71
    0x60403910543c030151410004401c0c2c01034144c03401c40600700740389800858420014144120301409000307050400568680c43c07240c11400c040c98203103011503016400350340d420014600c858510f4020b000c4140b802d800040969440c81254082108485228000244110210f95000c1e0300200400c40c203c0949200f9005040d05030300014040700040b00f400442030300000109582d005000c002c01031842d240d00351034412060b001000e5840181c8000405840c1810010289804100e8844900c3d01d00c040c0e00007004a80305941002d0310030000314034884541014410380c1c2c4c0800301c04006204803088003120365501e6014a0340c00c3d142403800482190303141800050900940101802400308554410090303000f500103200d07a80c0080c0d9500c2c00016003074068421203031031342211032419031080c1d100303d20140703e40c2c8598181c1c0d04050340d0792001600c840d0180400c40c040d215803600410000040340c400384c90495240c080342d01c0703202e903946481500300b00e020442e0704101140d24049100c00c905486049180103 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 162732428 1250 162731178 162731189
    0x2030c01050f0a14060609042007030c0605010806090a11030703050f1024030201030207021305090105040c06031401031e0c0303082703071b12050c0f0d022206 70
    0x1c0c041031000d100110450a4440c20b0f07900c034100080f0f804003608140b0301c04250303195504210200210409400c1c2900480e641c20070f0304048064002c034602e44503031958031009003540000e00150f036032010840c09008841c01030618100408043c2001c840c190303111548030341c2c001c05501951889440c2034500f481030300300941c0c005094442c0d4000400749103403103e410070486203c41d840c00381c8101c10030100485804040304d50580501d1880e0031030340150001d50044030107a13813024201011410310f249030b01401d4415080d100001c00d2505103461300300b20700322154000005040c02c010780882214065820345044a0700205600320744085841e2484000c41042c10103460070542900100507d07801481c0035005944814101c400450110203c0d240180e0402c015442a0010010a07020848a200340c400700c1000c1003680c0300782c5a50715408100b90381407070f4040343c80f41c002c603039400c1c040d1030b180c038407a03410450584589030081c8181e40001c0c00c0460180009480d4a000c1800035070403000380d80718401401c1d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 162733678 1250 162732428 162732431
    0xb04150605131a030a050c0d0e0c0f01091202130e060c0a02060912040e150a090902130905120a03020702130617011104051011030d2a0c060c02030c01 66
    0x54461100a05507440682c02d00101246050b0008401d1041114142d41c02d6461545a095803164141c4001400014065107003070030082c8901c3c01e280031a48500c02807205480010000c4034203a10600c5401d40344400d0040c184400703c001080700c065250480d8030003641c100c5004c4c00d102c0d0740c03000f01c000414041e01201c0b018030401c2c1c1005001c1613100000c0500f030889800715507542c0e403001803855490315040e40040038600b06010822610341104080d40c1c020301c140503801040030707100000c070b01c81041c150b000d401e02a44858409d019410102400c030411460100c060004544039200e559484219441e4520502d80c0014080c0b03586200307605403102c0a80c020007181a2131407500c09040580254002d00514010105100302010414410038100c0c00b29440f0041c101490300382044140f8590701041030038407145044491818000740000c15542c000301000045181c107928440310007620060b00318901240c000300304691030340c0111401b100710380c1c840d00224900c0c004000032401c5000b91880c0c000344d507 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 162734928 1250 162733678 162733721
    0x203100207030e19050607060f0b030604150c11070509130b0405030a0305090105090604060b0607020301060305030d0b011106061c142a09061003091e030f090503100b04 74
    0xd82e108002081c1035904903481044441c415100d26499196441400c1c6d10201c00c210310300010f13500c0c1d00983c148605a00300001c01d03560348808241060000c807002ca42c3c00f215925402001c002034840ca907104155403628850065005404942c1c5001d40e00455100f0854a0300190401140c508030b0007030158401d401103628285450603590302c0e000b000e40500800d042400140b008081440f81c10b21800c0c000c401495951150789078540102261f0552a420141c100205005601c2c240615002948290000c5940329400e450001c04c480b120181a4100000d4016904410000003003031030b0040b0080796920350805d0380101c1c000e010303601410018503403081410882a44030340401c020403000c41c07081c01d089100144581c1a020050726680b0681c0c804900740100d00c1d11b0800300d10a011014250500013101c98650700c079203c80c42d210300402081c80e04450540010564460304440b551075490070003200d201d0410703001a0711424450315011000e691000e1540c0965540d41147c0c1d02c1001c04900404107 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 162736178 1250 162734928 162734933
    0xb0a02010f0507050a20100c050d0b2205090712030503041505091e1e060114060a050d0504020a0302040606090e06030d140c0703050d0503041a06030d0c0203100207 72
    0x40c01d9092000080145000002000c4034044c5045820192203943d4501280001420b040742d03400d0b203c00310310241d03c80d040348036005143c039105868406050307032503664440d820010721005490340c100ca000d0207001c021742a0344070700f0b28034035a07160250401d007004035442c0e95080340d05141031081e078411a00d0050180d00081815040130003036005900500b0400f486012031b401440c10340d14240c030320a46640c030900c2c0c1d0101058950070a080c401800e103054600740c0c00090b0f4000d4071039040544040c1e09803c44001080803c40d040d420b030315428000c3d1911418440c04c264050030500800c44030503031584d101e0300014115510b001c10800078642c010410060f180d15028014400925405443d40020500003c20401e24001501070007075529581c611100e40c005111080e03141d00b0040d80d00c400c62103403401c0480052414130070441c0c2094203566403501c038903040c1014800d01648410480c0c1030619801842039548000c19803100c0803d85041c03900109042c2d2012a261524220280354164401b04100c1c04 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 162737428 1250 162736178 162736181
    0x160308090a0b010905070e0a03210c02060c030a1b1203090201121a030706030b030c0f0604030c0303020d03050a02030f07110a20040c050307090513090818030f070b070204050405070b0a0201 83
    0x92816680c2d00044c1f40b41e09014480103010500002e012200c080d14650504041d600d1304c007454001c6480c1c100c074540440e0f40411940e410a0300c940e01c050300081400000150311004011110207050321400880c1e0b00c071b85460721500c0c11030996000305620740519074103690182d00c1503414104d000ca070401009101e640c0600300107482143c0c184c407e001c1c0d503500081d154481e0044130724066009006d0088009900b04000b0444c8001c0c00081d00200b041c0400800300e4043d048200040d0f010f034020b401c1030a0310160040c03c40300c1c01024094101d1061050041d0001200143e0f0382c0300700036082c50400c4025041074146400000e8400405240202c1c61070155808a0000c4640c190b1090b981441100040c0d4002e5502d800119584800110344080c100200c7c644030208000307815807003030002180c0700140c03216521544810507910741249a03030300012650804104080c0c0b013180b16405060705d0340c108100814140310b0308001911560716000400e05100d000d010410081404500e0300396140743d554000390 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 162738678 1250 162737428 162737431
    0x3160201090602210a0c02030d0903050601120b1b1b0708070f03031d011b11010e0402030c070206071a1807060305270705061602040b0303160308090a0b010905 70
    0x340001e40c040c03000a1410700014403c40c0030305000c10841e026498000f181203240d00100d4a4400304100060400b01688040c82400d01002e270703541c2c81e820313103a056081141c80d101060b07100d105400b0190040b0004105001d840703580280d0081c0800100c1c9030341d81ca042c01a4020441200c5001d84684400b10a10b0000200e4000300c88016094403241d5640708002200b9002911014001c50550b512005625142c080823103065041414880c0b20000301100030000802c44c40340880710034042d1803104885680001c000c5070017040469065145181c04c02407525980100341c0c00a0103210003250401c10040c10b492060580300d20010144501d01c2d00400c5501c0d0740740d01c180440d003140914003020900500c2800b800b44210240c011100440c860140030b2001192019101ca485014911001c07510380d44850050a0683d00404012140c04c424010042202c060601540c82640308110001030f0b03448142c04d2240c01d0f905802c0070704165941c000d400b070900841c00002450440000f00104080616031302a5 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 162739928 1250 162738678 162738683
    0x31e0209030106080606100c03020709020a03050f060a0302010e01030c1101020a08010e0f06011e2303011a12040303022d1818011a0909010f03050c0d15021b0316 71
    0x240f00341031340c681c06592506401d039006900a207601554400742805039080c1090a4401e1040301c5125030b0f1445400200d8102c84040000280c5490a05c4081c146086c00190400b0040321413070354036851540003070b00780444c5120881c1803544680c60b16003080d0250f2140d055020000c4000c0d583c0705094000200251424050a0044109034010445142590240512494043e168044c10491960328012001402c69154041008000300c00b441c240e52000c0300f07811071080083d2681c0f69410079548152a00d0351000c0c2a21103001400780030860710107024002c0d00641c0500b8016550500c28002c0e809060002e03446120348800030122440d07107100c5000602c814410402421011a604010400385ca070480c10a08201894040184802c5ca4180325655041110031a1949400c0003880460740d0b03101c00743e0242c40003080b640340420502409001c254461a0129013044110820ba0f441b100c20080c4103507101c6207140d010804011100403424a109a08102c00440303880b403000000c80d1071a1621000708 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 162741178 1250 162739928 162739931
    0x200f060108070605041a03130812070e0d173f0606070f11010201020408120702040e0f100c0302040f090e010b030f0d0c02030c0634030905060307031e02090301 70
    0x3d100d40308a0030744064448500c150b4079084c948070480031280d0000387c203d01c403e00700e0310328810002d15013400409000000300074089403407608800c0035200b1840a40c02034080e400c1030005200207100f401207002c847d620780f09002c2d02d03202c0702900e95801c0103100c07142d040810080c8043c0e000c1d80400d04414800354644030b00d0600f0f1035581c4024060f03d0300800b00c0081403800c8407019080041e451800c038404111040c40010300780781e50303001c2c120b25181c040307a00b100801c036000401000b9400c007401414880300c18a4000e040b40205c05442c40c1d66181c0c120172464401e03645908002304188a0b030104e5000b031201c1c10080d042c1c95110003a9070005c01c2402d17003211440d071030106010043d08020400c4046a02000060320100e080300200343c80c000b401c21000c1340d1602801c0c015611590303803140035207103c00725211950b4885019103460041c0a20000c1918120042500d05000007a803000c920806c0d00c0c41960016142c0e21504402e4014043c5010054680342c14003d0503000c180003503000d0002141d04900 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 162742428 1250 162741178 162741193
    0x1406160302120406020a0c05010f0207021306030302120a1101050f250e040207080f07030e090708060d0212010e010e030c010f050105061905190503060109080606010807200f060108 79
    0x101a4220300c1034001da0b030460000c40c0d002602260060740904140350103030603d1106a202c0e030780d6041c2100c01c208034444a082d40403c0c2031040d81000d1a40e2110f5a02d1410100082c1c3d0854901950b074400145034140106000142c88000511031103070b46100204400c020b0005040c55601d4101400089412026034007110301045480e1019400c07108800250380c0b0741d40000340c8401c00703200280d4464801075070001420040e41002c0301a0b0402044030700e0007a5107601c039080c000c02c20060050409481c0c9410001c1d90010300806175030355100300354803542c100c030080e04980c55064001d000d0551801ca008042d480e00c20b0740c010019010006007200d6000c44004c00c454509020400101c3e40c0c2030081d15080042480081940411b06484000324543c6007811402d1000c0380c2400464112140d2082001502c00b1050041c0303541c016941c1009010b0803409003034141f03401e500007050740c0801450f0707900f0005a07000d40e000807449520032000c6246803c06944a1081c0002d180c1e640f42003c4c1710f0042148203904 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 162743678 1250 162742428 162742471
    0x3060608070c20010302040b0304110114030c09060d0f090b07180e060d0203010207050a080c10060303320406081b0c0d0e0a12060905010506030105060315131406 71
    0x103802c1c100c480d400310444042403620038a2030b411007030000c1c030300341070580c03c010215040300907802842c4154468005900c2480c214000107205082d007200710700300c0e0481801800400301d0180d00fa070344003d10640c0d400e915810414031800c06011078009260102e4031300342e040018031005103a094440c05541d117504402c07403803100e00050001110320410000310040000324115141c5080c007040710314001000941001d44c1911801d0800c1200c48084a05d040000344a000700b80c01441031414510001700100a15840e648016240d80000002501d1481c030b5820420441005440c09480e580d8030359031117a480700e0311008003801c0604161105290482418007410402220030304481024071004050a25078140480c1980c40600385d003500313541300035012004980c0e4202c5040000d10b130750103420085141c01e241d04011b800c407070007d000c2c01e0199041204100640e01c1c00600c281c1c01840021001481da55003a400c0c80c188025084011301c0700034010070101304440300240319802540c00004600701d150020 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 162744928 1250 162743678 162743687
    0x801020d1515050c1e0715050f0a0c050a05061519080c10050c19030806040501050109151b0b2e03150e10020c010b040605090f090a0f030306060807 65
    0xd02c15011030380005181c075800144904060308581d0707401011900c81c4460b00942c54a1250214015005135010071b000700015980d064030100032032000e003010361a007005074036445207a1140c0194030041c0041081c0c410b0400604024941030103030404240c90141c244224003500306103050080c1032141e000d441114600400c20f104500032116460000c00441002d0810702c41d40c0221900d4100902109004d1405c407000c0620121044600d858240741e4010894540603102c1c8902034085401a45468014026643c1100036035044d1078040d24031030758107502c0e610304075103800b42c0380325031000071101d001124104000300142501580e1445040a15490020303070400c0c00720f10f90071690381000141c41d020008110041e0200125940c100d002080459040d401c882ca03103021038101d8103a0f654005012a150704081c4659954014111401c0c40154503080000b21101030140c0b003401c06041030404242c0c6140c1c00c102c045a95075200810403c90019420080c00030302d010301ca4000411404000a40382c01d105 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 162746178 1250 162744928 162744971
    0xb012603040b04140612090604030f030c0f0e0402161407050d030815210708010501050109030c170a0f060228020307031805060c0609100e03040306090602070803010801020d 76
    0x550348414141458202511211320503a031005800c14010481101c020103006215485204c1c100c00804190500d40760042c9110341d480030300c2c0200b51501c0d44000312207510000849905006260640e4510051400070340240714004100c01110301c900070309401c0002e0901c0a1700b012180405480c102552841408000c0c0215040140000c084500203005011003c1c040300b0502c0380900180c062a0004403442562010034101c1002c0d07601111041085901c01d0054038090042071070409509450343d606c0010005143c0120451748402135949245640e00f000411403060700226049407040301401d00c80000e6000746403401c0d86075000c0700301040100f03928803101c002640d2136005618040356900c0403185a00c42024140c86250291000641c664400c1d02521a5081880190035241481075503581741c8481140c40c40a1507041c0310266110a00c04070946007100d03000500130420111900d0b00380002e104490000786805004070001c03030103000541c054189101c41c3d0b0030030019401580e4030070090011 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 162747428 1250 162746178 162746189
    0x3070f122001120905030426010516020a0609080c0a0f03080c04061403180105072a05070312031b0c021e0603060d06020702040f0b090f0c0316020a0b01260304 70
    0xd103040070000c03015554013007030409000e40d05981c1401d49078451104101c002c00c10b606504061201200841c1e0000e00c201500070020b5110103400c201c001c40040d469010101c0c0280459686002920910080c1300494034810340d404162500c0181c985091041e034030803000b090700010b02100c001000c18051004071425140aa21000460f5544c0c40100c0202d030320003400c401400043c50202919403000340100d901500103519406403620314010601d00002c0c200400000303080c400c103080c40209601188030b0f02507940294014440c0210300b80c0680c00703420017004c07081c0d507000c1d00c041d241c40f0a0350205661420910889018078261841112140f4069049580540c400010008200c0c2e0313240c108013501055200e0540541050740c20340001d0f04071081c41c2e00e052000f0740c50303102e44c1c41d5510b811403500d1350000340c12000d280c280c145080c49009500004010000c0d45200f10704071524203000b040b00c2d0040307542c410b44000b0250f03140c16000c407442c040c5291010245513805002540d901d400700913201900c8 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 162748678 1250 162747428 162747437
    0x50304032c0d06020c0a03120b0103050115111228080403020d1805120706030e0a050303010501031104080303091605030106060824090a02030403020d08010311010c0203070f122001 79
    0x1400c181009546611008201d80f1154200200181c3c0c6509025421a40c0e0080d00e60003030600c800c941500a543c8000550380c1054540001407101c460010b200960020151401400d80d40000d01500d1030090038211907100d005022940000500954004d038150091101421009c83c040c244140c1e030000083d24000c0145e0400c203942c40e1180c1c4250f04142c1c100b040840a661082d54070b0021820403102c052a0304859042410280a081d415008142c04212410014015070721642c0b40d080e140e00040c007803a410540c45440008a892a18003590003a0801d80184c9659081100b4100c2d40c40207040c41e140d020175103e04001510b4a01031280508554283d211481290307103403900c00c081e07d000205002140f00d00d80c516002c6035290f241445220b00238003880140e4031f0615040203481c001c02000e1540811400700010f00c0024803ca00c8485154020300701041007208900c0082d04005031a042420008106039000810340035108a82102ca4041d080700d410200341003017070003c130000d0440345030f0124 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 162749928 1250 162748678 162748757
    0x60b1e0108040305040f090b1e0105030103080d020403060c170c040803070303050c0d060b04030b1323010e0d0e1306080309090405100203010e010e0a06060e01050a17010605030403 79
    0x154020101164010f100f071801c140303803584a103600d4981c41082c0d0801c2d400340c2c2c0c0d1201c4002d00b508155106020034172103c03907000392105030200000c019101c14003008100c5600030a291180340c10980640f4051548034601340400c8001060003455042e9600250b5405003a400200c0c0d0410f4862040300c0940782c40c44051460400c00307450076000b515000d4102c41c3c05440c20412002d01d46034078032562001d0540c500341155540e02e9800c02c92441c1c00e003d040440b502506040c1600040c9501514907103224100341841011031740f8010350390040c50b441d070b2442414050a441d065020307070700c034000da6102442111584402060701c60300d00112100790080b92950f6008100f11017061428034100c543c0b2a10800455507980e00050609080e6002a030050008152503401800558203101a159128072401c0003000341501c0c2c40070007010f4980301c80e006c40c180080021252202446403142d80d01034884c00c0340c0034003a07507501c1400500b190b1044400b82c00141158020416008079401c1e004000c2d0f90514a40812 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 162751178 1250 162749928 162749989
    0x71a180c10020a022715060a0e03031b0705011202070c050f060c010c050d0506010c030207061404050a0e31080904020705061504180b010909060b0d0609060b 69
    0x9a072402000e41c46040a5200140e4507550050140c0203c4074001c006020036100307940055101606101c04000348200d01c9043e5142c1c0d100350f49807500180703062441100b041d8003083c25480b521120410a1081349250801c2910020701c00003250720aa8030084490484034160b0203d0140500081c1111404c500070010b5241a02ca03589a000008240710710f0103200c100264219030300e407001c480c04a0000306008484c801c02d4810b480d88842c0070300304000d4003100b81e54025116441809000144034094500192038254001642d010700006011521441e031100710a000350281150940b2005800c811403040318040480146c107807420400461000e10b0841d0340754001c1d81c0103d00015080766087c8454008a903040183c0c901540315480565a1041601e060005580c0311440a0580104503043c3c580010754500c034050468504400008421b0780e145000f002038002c900042d644010240e590000b84219540400b214600c0345208204003480801481003140e01d0848452800c0c4400c07600100 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 162752428 1250 162751178 162751189
    0x20f060a0603030518120f010504030e010503040b28110d1808030115020309060414012c0603040c03020d05030a0305010504050f07050901031409030a090807050303040312030204050402071a180c 85
    0x1351700000f048029103040d4070200901e00400170282c50141e0791503105000503d41c2116036150509400e00e4140e2941c07901e80c0707490404c654050a80e28405031020b03000b000604c50a000790203040402c200601a800f41c401102d9800e40002c2c8682c0201c40ca4401c09204540c07450f6060041c1030303404002d070341c11a03103040259a0174408005003a0158003042103c601599a03010040003d800804883e428440d140750004040a000288508040280c17010f02d0542401428044411500071610030741c1d640c1c0c41e0314010b920140c3c150300c001e400c6030910740000b040100c04805001100007554080240703030b0b130720020002a5034041d01d0203498000d0700004200040e03c01c0004048407401810007080214444503a041c20034001c03510400d645e0000301d00804203030b6000305010000c014000c010310000341007000198591080344401482c0b803101910180c00b440c0283c055400604c0b000b40f0854480005040002e82c45015408041e13120300d10500140d510f0820151a0803404413440043c0040e0501205110 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 162753678 1250 162752428 162752467
    0x106050114180d06020403030f020604050303130809040609050f07051330080408010c09032003070906090213080d0c030806060702060f0c0d0f020a0803040809040c020f060a06030305 80
    0xb9014008108002e0041c1ca880740c00105040c460600141e55500e1824001e00c3c00c0368407224442190804810301002c500f0000a50f6045003169844200030116850401440c1c8144400d1a4201e82480000035494100750310003440750000e0036404060b5076584004076124440c5540c1494031314020301c800d12025401a17004140104000d5000c816400d0105900d0803900c16460125040100001c050020700828058a03100301d070b04d070500401d403e04594920002032017003c0b07078141a00020004020390b41c2d00f0880c0e00024864280c08210040c1c03074141c043c0c0654010000302da90b000d0030000014054030b00140e01e00010559543e100703190305590342e04540084c8054078581c0d1001d42030000802603518040200b665a42030b00b811955540801c12160a0070705000b40f80c002e0004403030780251450380200c0c002040560181185903031b95601e00d003440072401440411608113185c00c805108541d00000e142e82d40802c0481101c0540e0340e06000081074841500006001500a019464a0800460301e00 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 162754928 1250 162753678 162753697
    0x40303110703080720041e060506040f0306020d0216050a0b16120b04060b1305090f060117070315030827030c0402070503041a0d06080705010804080c0a0203060c0c0c030106050114 79
    0x2c00b251210840040c040d200100c1010340841d0001c4c1e180b00303c0500c1423050000800d81074481c0380c01e081c030704200d1903440411444050081d5800090f050100441641240c80a09000d42982d010074002d007812684c91009000807100d9080340004500456203a43e8011407400c40c50b903030f85c0304040480c00d80d800540040410380ba002070700e0710008034030040b084001c1c0c540f25600c0910b408400e4036107020420001c2000d811940c816444006105090340e000301e400d61a5082c807081400310361103200c0d00b103008051410104048000720440030041100890080031170031404041c24510039840002d16040740400303441641d05920662075203c203403c054014044c503d000310140d90400c1c4d503c0d4007105144071800400e00200c01c0c009011402100284155009043c1f450000c0c011103040800281451102030400ba0040c80e02180585110b503007003107007250720b5502400351140c50030010010308058200d801d07e013501c4e005a02d2180c65509051041404446059640c0700c50300b921141442c800b684108103a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 162756178 1250 162754928 162754973
    0x907030b090615041b030c140c01360b04030e180601031401080c130f020a02060405100209030d0503041b060e010e0906030606061b01060b090a0603140a021615020403031107030807 79
    0x23850b51502140140102d0300c2c005002055803004031440d0407543c1c4881000c495a0368843c40480000d001d6075294244444d400084406103440b141020703118500103400943d801034490781b8170740e603c00b0b0702106c4070300070102a00c0a004003420f0864a40410509000340c1d551540048401d9680d80342c000e0b40c2d02407003075080400280503000c1c49041030aa0b400f248411003d64441020700003000410442030141c0301000404605010f5a02c000a0700c41c280c0c0c02c1024100040880030906029900211483d4910101061030a2558460b4090104e100031503000d404141110090710a5080ca09891072041000401400d0980d480204104240e0480d012602d200305000e64204e102e08403d214940260140b8200b00740c544110f0020020104c00302c0d00700c81d0805041240995061100900c2c1d5500f210365504056200c0300c0300c0c540e081b0100601c02e00644400d80060700d24400381c00c1980200240e9009644113075454607846500c0380c1e582d03c03900c0300500c2207104000c0100031401304a5070140d06901c4122 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 162757428 1250 162756178 162756197
    0x181b09030f01091a0c03010608040606080d0903020901050301110706021602120c030d0f020307020d052802190e0403080601140301082d03040e0907030b090615041b030c 74
    0x2080c9000c6241c49a16407580d03550710381c44148500c0340d154000c4c0b44071003c0c40d02d000d8981a01c15011501043c49020103100c2c002d8040350410400342c2010000c1e003482011102882106400104920040e101c203a000f00c6e501c000129060030103010354254100c8501404c1c0ca03144071a40d8920007580049650703007840040012408c0140c0e20804011982e41c0008000d00305603440030105420004480c68820500070380303003845801a034021040d95010354049518402d030034020b00b8841d042074240104500604e09040042c0c4280320a0755920300107500a5410310902d2200d0419400e06013414020b001c08144000005030020344140d550950140d410700d002e0030101c12510455115410030380051010f9004042050a4070b126085015404a4001400c00c20803101e8000c1540341c0c0f1403401f6800340322040d440002c07a0134408004a200030740c0d000114034240c0ca00340d0300264503003501303030381145180701c0880044481c2c3c40e080c06110f91588503045610f4412030f0f000c00c160000c101204a0341c050154200 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 162758678 1250 162757428 162757447
    0x106150513091103090114130f0c170a03020f0102090607080c0304080319020105100605030c07050c10020c01080108010203060a0504050a0f0f0501060e06070818120f0c040605181b 79
    0x102000300c3c40f86030510703449082c025991429a49122824254003000d441044000c01410303407041002e940042030308504021900304601107840c0b580045020740140703103094a00c0c0c000000c2c58501e80340203500303450000c107084a80340c0c242d1081d40a46d643c04103041c00100049a10040200150504002101c1c0703001e588000250568025a111045201c282150079030790079020300410358404004a0030118481c00c0c04405410b038040540341200e03044000c0b03021820418104940460702e540109038141810055038025640c920b4861028001003112000298040d01402902d00480c001030010644074146001d100c000d160080424221580350f00d00c844110001d84103121109030180404034441d8103140010b4460041910560b00070882008208040b5001c0c40a5a1100c003c005505481158010003d0495021600350342d095000d0076204001d060f100060800038104166001d101c50303580c500c01c000e9096010040940306d038000c003000421405000304041c0041d45408070319070a01720a070 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 162759928 1250 162758678 162758681
    0x101e0e040510060e0f150f09040803060109060807020304031e0609031205060a2102040b1002061909021c03022d060109020c03070605070c020402070602030f09010615051309 76
    0x240c4003500e054112015003a24030086000b00c2c0007034071043e2141d04c040d0400c0804800d440b2401050480030b02c90560380d200c0e066403215480681003000420b84800c2c3e0400f41402e48040e4070540e04107000c110410000144203001d4980f892096466802440c1494a152076480700a4450a03420041149010300d41000070450311030000c225000e66108000d81c000442100101c2e4000f0300300e1441000c45000030000c07102c142060040004440d001e07220f080b80d03e0b1001c100584251000141c2c0001d03092001c6020941c0001c82c00d100c1d503c41c0c104441400c14408010003114850b03800a50400d0030003082070000c1195240400803644223104465000c080705c0800c00c3d40d02583c0d0f4000c400e515040c1c0808004a80070440e0a0242c4007082c030440c83d000e220401d499980c03160740001090151504001803600c8d0060b0000403401d80c01500540d65402e0a1030103c00940c8200c60458200b940d02c0003090407000140310380f03400c1d1100c000c94541c0d4003007507900070b6400d42c0102c54045003001e0701c0752010030081c026 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 162761178 1250 162759928 162759931
    0x903120c1107031b150518060c0d0c020d0602040b030a0f090b0f091e01020909010905070503061011100207061b020709020c07050402040f180b090c210f010f0608101e0e 74
    0x106d540b140d0f25032031000c81680307541084900c1ca601c200418000e0f02501d100110f0580d01c280841e0a119103c0425403000c51941080248050282031010400140807200500111300c41d031005542008000b008031403002c111060500060442c1c481000040c035180a07401c07036245c2101c001c40c1110084248032121000c480105109201c1c1e603500800c68520504003201c00901401d0b90003828030607464070a00042c101d000042c00d0350b01c01ca4003101205203a50107960005140300311a010f4580c0d08102d8100c4030040d50207006c0846507c0d10300011030703d2200c2c0403000500c1681459001d410490320380155079001c1e4100c4403250080c0d00800e01c0028280c2d07943d20081c030081141c20412607480c5d1802e40c2001d441c082524002000b1350415070009000c0d03880105080d849a26440b2040c0c55148000240c404150440114404a5047d0003803100c44511045200c0c12200c8008500e00c03801d40b140021540400241c400c000080a80b06007400007a8441421940425516101039401503803103103600b184890 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 162762428 1250 162761178 162761219
    0x2130305030d0c05040506090d02010c0812041403070302100f0b09090f01050702190213060e1e1e01090e030c07090f05250807050c010903120c1107031b 67
    0x4000b40020018030309014840031400b00d81450307418540b43c003001c03681d2031080203482403285401d4000c0200b1a130103003046120780e0b40c00460301c6450f4818002021404c2d4010f840c15500040c4a0b96000f050b080000110b1740700545c540d025010860407003d90001500c00c070080c007540591555858042900c0c1d48600300d1140b4211001410b1080d101c800e000d007110f0000d440b1208541090448251200d400011241400d0307061b074103610b03100c1030103c400b4002c200e42d4002102c22031107070007408015500c481030640d00c101072005140d12500c1c2c00d4441d0000c02c8001c540074540c2400180108010030300c990143c440c08800714140c0f850991300c040ca060621030f0716009000a15650380c91504004024490a41d00803400700c0f8020007040117400445010141c3e002c80f00801421708002018103100b641aa03214001800003401808501d250240418020b0094180d0142ca41103580219511488044c08928000380c0903160b95415902d441aa4080d1315003201048018041300280345000c400c0c10302040032 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 162763678 1250 162762428 162762433
    0x8030a0201090b060a08071e0b042301081005060702042a090f120b0604092013020f04030803041e060b12010c27090c020309120a0b07030203040602130305 68
    0x352985020070003c00050405070081807085418890317841d00103010015207900300f0895402060404161172690815000499545030200700058150b2a0042c01c006e41c121a801000c8112100307801164400c604560003520710034650f008000e0b40c00c01c5002005031a00140000c5405d041040c007580050300460100c040c0b161101401c1501c607076000c4511009415001c200403240380c034080356030101707545400000c0d14881c034550106074503079141d9012580d002d03402000343e0103400c02641c60182c04a0b810300d034580508140071170650b1180d0544200c5034009100d141c01814181540c58088807a00002c02c1100e41d4106044400c50000319240640f10b8144940004100906000148a08000322403481422070717040900503001076400c01e00030700c1c030341c030400c0742107860030038107240c5200041d1b150350081e041e9a00d04a512003186501000405a41500791080082040b5807103019a4900c859400a020308002e503000c54a140c2c402e4000b507400a00811000d0305003240581e500c400343e0a507a004a804e039 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 162764928 1250 162763678 162763691
    0x20f040305061005180c0a111c0302040f050303031006080c120112110603040f02091b0705060105030f1b04051e0a050a0c020703050703110d120c030207090b01050a0e03010608030a0201 81
    0xd1a00d01280726034001e506001c0da5003802c280d06030701c002c0e010b285c2060062088c400b4072101c0d20380c82009004801d00d40c541c4840e1050b07141e0b030405402988680252105494400400724184c10000b0480303003d5000b40d9240c0340c0c2d40b4034000c0201e81e190009400c4000e1108208605c8034140003034a01c00340a01034460003c002a49030303203003020400440e41003090040e48140204408980041032040513030f501620401d88640c2c40311400300c5180c40500003030041035408903d00043c0540010441c2c16110254100c89808014000300b941d01c1081003580300b808460072148513010300300b5030030658000700c00f415920805000882d5001029008440c02040d2540d01c504014109007240180110030400c1d002800b04d450550715510f440754018003000c3d001c02c40c6441c0d129815111a061070601a400450b00b00340d040d00407100410000c08800c060300140305601020174507411512031410704083c144c407060300d07000707148406540740c2c1d420080c03040d43f5550718540080d6125051005000c8240300d07900000c3c07035 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 162766178 1250 162764928 162764939
    0x51e040e01061d0f0616200312030c0d1e0905070608100501230a0903030e0102071805090a0206030106020c0103060b090127080d0917010b0f04020f0403050610 70
    0x5030816402001000004403c1440c0900741ca0b86480d919582a111070034500300c2c82e40424003a124041e41056502e40a071014028800421561042030a030720859250045a50b81090f9840a002060002e5420104041035004903002c0080c85240c4007110045890310700d4800c0e00c40f9032200500e03042d50040d03c1300200c1003040bc2c1031080c50040c0c40c1c142407440c80d5080250150f20325841c0c034000c0c1410b1104c0085000e0003400030300d444201c401c0049242c1940c400241a00800d40a041c0c8403ca021403840e404800751980081555025200408000c003105003402c10107401400ac081e20301501c500480c1c01c00c50150311910b0046001c0e2049070001c0050300d82e540700040885446c0d6001086014080c800c685580c0c0e84410001d80c0801d880e044200c3e40f0900e01c041c0c880600300c3d41d0111185100700d610180a040d00300643d203040703d50401c080e062084038400b855007038a98111049034011020b0081483d545010390180c026070030954031440c03c01d0740343e5a84910f0000183c41c1d0b0803260b02c0e080c13401c121 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 162767428 1250 162766178 162766199
    0x17210408030f06150904110d09050c0109080d0e01081e0c030105030c060705060a0902060d0f05071409031c02160801020304020f12030405041802061902011508070b0703051e04 77
    0x8002d80b060b81c0f42400c162501000c44d03454040c000c080351199403540840d540b05c40c0103c0681e40c00d0561070104121035000303407a00950300c2c007451020070302255410600180040c004034440081d24410388404001c2200a4011034903c0001003019902488803082401e04010718103403184a01c160f80211a41ea50500d0300701440d201c07070081054802d000420007000012004100350f5000201c1d04404960b010380e6100003111809038141145020385086202400c6035410340043d400b9441e10f450381484075074170b240810000d101c0d1402d0160543d014104440340b40c141d00404041c640d07001d2040d00c5c400012286040318140c41a848808169000710900c401d502c1e003140301c3c0138403c0007116890b20244100e6056510307802240320b618801c55031601c4400e13580004240300ca82e02c2d81d00502c6141e03103064002c0300c2990101c0011500c0019880c01c402070f04039810354950382c07080d070300d16800a0030220300d0320062554940c0507550803410072000380896003c142c201d8440b0801d4007c040b9000d41c84506106042a = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 162768678 1250 162767428 162767431
    0x120c030603140a2d0b0a0e0a06060504060906270b0d030e12060403021b0102030d05130b01080c011403040204180c06030e060c04151e0302040e0c0717210408030f 71
    0x8002060b800401160f19030702e041145442d5501174882002995028407490041c40e613140c95507102e0195041c00c13801c2281c80e03408003060b10300c00c441c00c1008070707100c50711071040351042c0c0260703821200200343c995210522440410b4000501c0d200205442161401043c1c0a240c80c0c8000c031f001c200340d004145c0040c5070641c0e9403180307411420014130941c642610000c1d80c401c00940242102c607200d0748030f2004e591003842165030341416901d00340000d081c58040384002e626240001d550007002030300003054401002c6a403c4224005035101420440c80030008481c0e81c1c0701800881c5c1c02540c0300f03a4226500d00348100c10203100c1c010041d05510a140c00340c040c0580712048183d15864000f10100444940c0d20390031746040c0c9203980781c07540f03111200b5001034415100d904001d40c4c904000850100c802c41c0d0580040040c0c9415604001481d03c441301c28902900a91300700410740e03e02c42d0f85c00440e0841242c003a08941804401d8803405d0b2070046024542c40f0420b030750035a0100d030000108404416100580ba = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 162769784 1106 162768678 162768713
    0x2060406090608060a0503101512050a120305090615190b03071209050c040e0312070e09010501020a0b04080d0b0301051608010f06120c030603140a 65
    0x50400c1c40c19114980018a0007400a2994104118802d007240e001600520300c4901022a07400a040340a8845036217040080000540720b888001ea044001e01071400380056013414203008c041d00b40075075000c0c07007414103000a11a481c400020790307a40c030600740c0e400070002000309000507404150380705c180070b034030300c00b4040c08201070b2036040c010340c00748100f9254041c140c034064203444280c1c1d00484001e03055400c088180d07813503802c00350404807411101c4002e032454100503007440100345e41d041c0d40b40c0e40021002049505242000c0b19410301526007400100f01141456846008800340180300410500300811801115030250b040003440000040007407081d440c000e880c41201900002c0c80d80c0000f89a0310000404409000c2050140d41e800c0e540c3c007000d21424035909000e8100081b100e0200365a0b00000004614034204510703a035403080001d02185229030610100b4466100c251 = true := by decide +kernel

theorem cover : BRFrame.Cov 162589928 162769784 := by
  have h0 := BRFrame.cov_init 162589928
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 162589928 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 162589928 ≤ n) (h2 : n < 162769784) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
