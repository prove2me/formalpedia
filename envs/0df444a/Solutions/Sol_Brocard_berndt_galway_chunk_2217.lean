-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2217
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:01:44.674317+00:00
-- url     : https://prove2.me/submissions/1fc44f67-36eb-4a9c-957c-ffe5ce72a4e8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 398561151 ≤ n < 398741007 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 398562401 1250 398561151 398561159
    0xd0e011d0d02012f070512030a090314120d3201050108060d0501020307030509010609090503160602091210060e0f06120f0109030309120504060915050d020d0905162106090804 77
    0x140782091b100111400005403030006121582c82c440d41100c600807525221701040411440500c08400d4004c00069907005091850b036103000341c0c40844040f4842d40d030384200159154416140741d0403108030135400351601800a00403015060144520307410018440002003241e00d0b0328200c0340c41d440e8420025034682c180040c002e40035103001c950b05500b961910f070000132545810700660048640003005140341800c854103400c0c0080c00342c1026200380782c00b00038004d010b41740c0c07a20a414403081c02d80a44901040b0240280c141c0b41964000d00b22494068184138940300e56503c40e075000f000032116500103034038800b03079035007000c81e0070035014015440d1a2200c0c06140e050b030802c01e01e05109600400c408103118138241c03558000c500403000010103032030091161900443d9022413440039030500c00e041c50b044035107090a0340e1100012126082e03e800c0d160003007040420504030022031000c0324651103810108800c1d184d0088520b41008816080380301d4080c04450f6000510703c903089110b90b540c0d00d4603 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 398563651 1250 398562401 398562403
    0x3030f0301030b060f0f18040804030203070e0a060911190918020c06060d030e0607030c0b0a2f0a0c030e0411070203060a0216020d140d0e011d0d02012f 67
    0xca607514045c1a54410410082c58898035041800e480104151030905020506851640004208940480c0200030110140c0e030100807500040050307032004091850040e840d6070668a05a003e10409420107844020241d03134941a00c070070030ba05040480c1d603071500c14800c0340da00400750b0101642d041841d44104102514ac1c000305038007004c400c01c4800c2610b600c0240114108060800b80000c1e11094900e500742c58194005c1516034028500180c141280380c840b030742151020b0b1a41119541c0d292000607848885021080e482e81283c0c5038440b2035170000d50303802406e01ca0902d14008000c54204041c08241c042d82c0841701180d07000d1305c2000b07650341d514185802580b201d20140c1c401d00c141030000b4414603090003124002080340f90009925941a1309011412030102030845205185c1c0c0701c03202213120100211040920582d0382c45086c01c68800c005170003001c2071038103070060036030340441101d80b526429480d0144036030a2030b0562541c0b00100092221440b20100040d00156200d440412000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 398564901 1250 398563651 398563673
    0x60d090b070f0f3609290904030e04051806011805010b25030e0303190306060f02061b041d040b0a0203010e0f15211c120b03030f030103 60
    0x440c1e203c0f07042000202805880d0400039412200000c4c10b842400058040102907110704c0d1101c4411070010162074506000070749a0030b040800410203c010241207200c21a882a401104107a400780014246618000c0803a408000c07410700031030701d41c0c000c54101006070302ea0002c0600da40d01543c4095855542803500100001402001e00307003041d0001c40c800e19140211070241c0340c04031402288144521a840c21030303900c000194140700880c5185407035a10140b0061404003550007010b045001190005011186140c110354100050781c0188140143c0000d5150341080e00007208442c011024403581c00984180d821007904484018062900b55031042401c6010701d01c6403420003444e90350048140200e0000f407140180d900b81a03008201420880040142c0210f46240c0c0d0b00d001e0703014070340030510441150451407407640d1504102003a650042c80541e40c0c00044460f030300c035600705401006014074503100d081041035980fa101104156010401c48119900802c482034482da941d041000030340c2 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 398566151 1250 398564901 398564927
    0x8070908120c2107031209080f12090c1e15070320010903140d14090708060a2313120e01020d020705010f0c020a0302040e032a0c060d090b07 62
    0x1108400383c020081d842d5900e6100600b041d455904e0411951340c030101e42a00313a02c1941e10850b607454021002003030280c4000e26410840e001c2807699543d0b50b40843c03c1510004007090a1900484000e210540c2c50100501800040b40d01e50700900b00784200003022101c40c1c403d0030300302c90030000c0c41c00e042540080040307030b184487c0414551102e00003e05a0b003640c02c0d13124010b0000744000c94441d1803a0140c40034001d5031000500010300c04260b02000e03a00c408094070b0002903540041810083d80808100c0316501165101d0140444080e1018103018800b00c8440420040400400141185610000d01148a81010085448a10312240502100c000d003144c0c0b40140120301e20241680c1c000140304003158010f82d140001403c81000840b0007140b518001c90380210341c4800040035945d180913018909558001940e9102d9072001c4000810040440604181d820364000502d0540007091031445440252810b0b65204d0440c100702e00103148103c03000306014400e00c20300011560141e4401904 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 398567401 1250 398566151 398566153
    0x3050c0a080c030a03030c0509031b040b010201091a0606070506040b0a1b140307090906091a0a080d050304060914070f05061815070c03050d0305180d08070908120c 72
    0x219480c0c1c80700d0364503800e1040b403094169019262500000707100fa0301800c0908882d140041c02c1c408000c00013410003189005407091306a0584c1d0452051406115005080f0340c2400200700060441d070316074070420049200c1c580c1c00007942d40040c0c425281e0030202e0340b2481e8080c0603618940780614144554040c1035070010304840c601444440030154040d00d51083d000703141c403107860450140307001f0310700c2ea40010404000c02034903500000c0c2d9540180145005001c40000200c5e4044d0110386541c6940c2c4104d1075584142c001440402c810100481e00362b01c58030b10340ca4a5681da942d282807080c00b604459600400c00401c20301c03410405000407074940b080d0394418200a44555440c802c200d494000c0414417244070b441906069514a41800b01350000c012200c142800c100180e280c101548019610640d202d0308140c1d500c414140d4148150f40d48116100e956042d6180750080c015910075007400054184214080807e6a5070f00490708031006000e598100c0c1c9218072010503c4400d500116460401 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 398568651 1250 398567401 398567419
    0x50316060f05010302011e1e020304080c0f060d050a020f0705100e0303070f0806030a0503030f0a0605060703050304030c150501081e0c030c0d260301050f030c060301060e04021303050c 81
    0x80c40c1003602078141281c1d0142c0d90407042c0000170000401c2814404405030502c10324041c44800100c8c80484100c10a01c4c54025503212840c0c9040d003800e280d1034020561240181d0004040c440e0303200010b60741440501c0600107981c1c1d5807014000002d210340e0548407800e01d0046200410414002005204404d1700e400070b2040318080b01c09141c3d280000d844940105010440e0300c820310f407107100030540c000c1c1c008044580c040301c40d88442e0304546c8180c8084d4410480c000c2008084a030f01d002d000001c02050302e01510f008000e86005180303000c040e000600300188002101e040c40301c000c0c0d01070031900282c9010400342d41d444810603943c1c40040362071015124080ca90f004400c0001c10a8103882801070017070001300c0400420000802e08058088445844e143c4400b282d10b044405c1d203003084107040c28516541c3d4144010802d010f00000343d010301c264081c2c19040490303110502668111501c40c101030510000050000f8040d020350503103140c0c1244108ca00100340600080c82c01d042d0403098900d040b07 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 398569901 1250 398568651 398568671
    0x7022808030c0d24240806040c121508060c0c0d05090d062d020c0a021c1a01051305040c0504020a02030c0307060525020c0f040e0604031808070e010b0d0905031606 72
    0x30404110003180340103d00c081c40051040d00340340c3c101d40d0f44c130f03602c9c0d1a22480a20b1701801d020100e072941003c540960304c000c1e000b03201002007002001e401c880d00140c1c5608007030140140c283d80f801a10010300030803001143e2001c0c1c546482c0740b0031019a81c410014080c100c0840e80817010010301c1d002c0348100d0442d00d510506400554404c4480185240740a418094495001d020014a03100d040c00e05820310413240b28041940c1c48851030a1a40c412204034855152100700444040c1441c6054252880c0009000000e588101c15808490007070b540035842e030102031400d9003140280640e6502e00c1c00b0021310401000015400b403440b07002d9819240b206441560080c0245000c00d40c942009684440f10303071041c43ca022a110265000020030200b49002104a864140003003507400701e001c41e00040100550440d54230701040a82581c07001448014580700111449070b0040c840c2d000d80748000a001d80c0000702c150042d08143c0d130004110b0f6a1590b291484000648651401b40c441d42d1074070500030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 398571151 1250 398569901 398569949
    0xc02130906240504020304110a081b0907120e1c020c030f030c030f09040207020409150b0402031005010c15150906050f01080408180907022808030c0d24 67
    0x40d148880c002c0d80c032800350074601800000d5002400c29115080d07159881e01443e92940e80303007c003400402d40a45119402c140400e1038482400c22024402c008603010440041e500480c3c1c41e42076528028040340a0401245030b6003420300f61030102c060907940c00040040c5079000a10079041d68004d034101d85150000022941c0c507801010380503001c940003004284482e501203009003100701e40c000d100501d807401650001c1c04440306450200c4815003a01c1003428404c141c0e00c01c03986005001e940542ca18a4118031b0301d0b412019074050076061042043d805810311014441c4242e9410350000104602d4007800c500f500c2c00030f624414241090304048011406083c10750440b0b080300c40c10307190b001007a142c6640d650021703044440190564209941c2ea00415a558031350b290003441d2036005003161081c6004186030b00c0d10300240440e41000c207103269a00250031181100d9100000108580d21041412040c0700644151688035180c40405c0d1810000364003251580001c42e000f030210560110748011401c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 398572401 1250 398571151 398571191
    0x7081203040c030b071439190611070c080f030403030912110307060923130c120e070f06020610030206130e1914010b09010c030c02130906 61
    0x801c2c041c00400304000190400c00c0c156000300d1700d0305002e40c6034000400d900b00f07503811021071540c500541841204081210070000f0f100030752201c2030300c5509001c05460356501d0840013203148184c54040c04450a102c0203602420f540c40710300c582d442c0d641c1c4440c204030720000f5907406036008900455130112080341002045804903641901c2c1c40d44210700d0002c0d03090080c1c06443d001e41c1d10900500d0401103903038003400f81c03e002d0926600c803080041d0608056034040004402c0307003014101000c4460302d49a50f20b42103102c066421010215030b0351421001210210088c80d0300c00d105606109200e002c904000c0740d00c0080e5102142103881856803010f089a4813074040e1080d003000d007902c0e0001d001500f403800007000704417000b0f0082c40100da0349074031110072030500300c4d49445421010148180c0c222070390f010320203406000d40303110841541058014a03840c0b25095826052001910030601058054111704480c0f54004141d980e1403e5010302400161644660442e00c19240041c0d41e14444400c48d11 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 398573651 1250 398572401 398572403
    0x21e040f0e1005010806011101090c1707060504092a0905010f05030721110d0e070807030308012108281e180e1807050109030b0a0f0608010e0708120304 67
    0x700c0b02e140c9031030019201054043c0c59503040103201060380010030f400340940141148140702d080300181c600301e0070712440714020301e00da040364010b01d030f041004940c0721082d6401d9030014240020b0481110b520085205415000144400e000480480509030044802021114283c0307840d50091f0010800300c2c0d040c40111a49008100050b40c0300640b80d0700400505880343c1c40450000321140700c03100e0180603070096040c5680740c40d145c801400d1070100c1405031100610b00701000341449070440e13401814400050142c0655003014541d542102d0040d01c018146043d00f21042035550b03284d40030206480c1c20314140030000c0703c8850307002803144dc0c0700794020200e020320110880d9a0058089040300e061100c5281604900c40010000c203013114030340310090240b0700a5103d800c0780440340440c0c03410103c0716444281800002030007000450307004c040ea2030b4800200d42000441811201c246402400d15402c5046550300e00800200c01490004e40007054541c001d00702c980144520b0b070f40014a00c030480e8 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 398574901 1250 398573651 398573671
    0x703020f1603020a060f06081207170310030c060f030515130c021c020705090901111c09051605041107050d030b0111060c13080d020a080904021e040f0e 67
    0x94414082003000c0000c41d154803c0c4169000b440d040d0700c0321400d441c0407281c4441529550481008111001c2044c203801e40340400700c945c2400d1150b145c1350140c4c0c04502d95944e0030400000010892041d1320304100145500940180c040764607400c004000d10045181140841d2400022440d6021407502404c1411001042161105c901260200c003900b481000c840c04c0d442031910300c0c6140341c4c80301c071100c1400603180d0080c484a4a070204100c10900080e003140000e034034101c40c00c681705014104498a8620f403200c1018110510f02111000303060000015200f0302905042504080d484030100084a0048600b8851000d50044400c0b45104a6400501a5002d000340d043c000f03000b42c009100c406c8050410f00030030781c0760b4440c03542040400c0340c001441c0d8034001a803165280c80f911941001e802c090005005c110144400030b0350300c1380b03100406446108045907910a44d0740e140c0480b0080840301d0944419a00c540b81400d07120f80007801080e031240e0202c00e010414034403141c034561240d03401035 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 398576151 1250 398574901 398574907
    0xb12040201030c05090402040e1e101e08030c010911030d0c0f020f130b03010609050603060a1a040c090e0c03040f0b060301090602071b060e061c0617030a080703020f 73
    0x98015001481400c501c41e0a002040c0424403046c2d94a1025000502000316440c01c0381c0fa01d0300e20008a80000c0302040f900510520510200101340c0c00c4240548621804507422601b03c0c081c4240241c000b43e000d80e60503c400522000000d0040d04032a41e0184110108001c49a00b0401c00d074503030048680c13031800a0101401000410300c0382d003c9043c4980040c010180c0001142c010810b038407106c2d100413880c1a190302461100b0b047c04d100c0c0344014034000c0010016410020006601c0e44006441804025110743e840c0b5142c015000e1a00d0f0300034002001007101d401019000382c8149540c1c42004050115000010350145400007200d200740e0340840c100307854890b99507400b03c4207030300a00419003565aa00301400060f0700c901c01440600e000b0103502040d0200c00c5d15200700c954164000d4002c1003000145441c0544500d8140c4040b2a8060b0020703103200c1449035107500820003a80103c0480038100b0400304010710100003031052069035503d01113240d64a040036004d038400c03000c0209040c9820 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 398577401 1250 398576151 398576153
    0x711151501030b0628110c0907050a032403033905031207050912010b0102330403030501060f1b1403070b010b0306130e07030210120e15010b1204 64
    0x20f07800310b0044600200400c0c100b101051400190080d00e0455061150035035044120964000343c48050264040005000000c01e1901141a403040a0400d409100300483c940c801e2501036000480e400440d208440050107103844e00140e0005240300540214003010150a00111080904800c68040c0c0001007280c50100344800720406203000180d03500d003c24030455030b0000e40e40340541d0140708141d843d2519420080100010702050180c8191a40c1c941045160f580e600415084806490408000010f0301d10709803001e503124200851400700c20740a030411003010740660109040c0d480c5c80e42d0f01e00c0d09140a03035007641c0100b078032280c1d02001420b4800300000154004a585924032017002030300d00707080300c556980780c00c90000c0c0c201000b405004010418a42045650700f041003030354080a110007540700302c1042d201c481d5030001030b000310031104048542c02c0c001d01c02d01d0f01170350f02204104903800c95642000e845608600e00e49c07180640ca01e0000441c40689420381c4c810080c10318803041241c50b1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 398578651 1250 398577401 398577407
    0xb0601050c0709021303030e030d0215090a0812070f11031210080a030207030302160506070b040f1e030f08060303120709120f0605060105041a03040203010f02030711151501 76
    0x34607100602071148000108200340c0ea40054048841103410342543d075401e500d0b01400010389014014001d038001860185465800119130881503500070b040703002501d881d01d045051404503840500280300000e20722500c0c41465800c0d51250700035503981c02c0911203142084031005190204407005510920a041c024882160080d4000050955179290140d4620502d402c1116071075007030b000758100174820000e1540500c0040c48407074031121044160b071300703000008000380a0200041c01c074086910004040110000f0002c03036140d003080048142c030014941ca1300d0448a400310843c0040c1105004105c02c03401843c05a0141000402450822410b4458040321040c004d100b001005003a14002030741070813095002130003a02803024030f1044003e42c10000c098590280c65141005020003007005035040c0005500710341c1000580490383c1e0340721800020302600070391907010109840001072160080d003014042c0100c40f2800309071401c45a00800020500790304031103507018900b05100031281d41d84 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 398579901 1250 398578651 398578657
    0x612050702070f03080d3804020c07182a0f030603080f0d150321030207061505010e040908040611070321020601090b010e090402041e0203011401030203040b060105 72
    0x3031548101d5142540d100300c02c1c858841941c3c030582d01c0300c000151820300e0090b580182d8180d5240300807a502c115082d8080c400d02c5210070340380c10741c04010a03c5804555612901280e9031106414101c90116450302400310848654111003099686402c101511764030b00c070021b55200402c906e005160b059101c0341e042d2866840f1308100001c06035912008800a00c0c0c0d400a40500e00c600c4500d103803200c8481c191031085850040e441500c10b50342c08010400240c2442c2429242e100f00ca413090126150360b281600079006403d00181074078203001101030709070f075030f85106011210700b41d81e841c0300070b0340003010f10084641100e00642511801c000901c94031f402074100a64154030300085800943c0d594032400d01c80d5020805c070352010282054000052030b4100041400b624940d402008400040300002c0c102101110b00540078840040005065664691114a0303200824040d151030605400101d402036209001d8118500c20700202800c403540700b4400d1301c1c444d680c4254020b080d62901001035469030 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 398581151 1250 398579901 398579911
    0xa03081b010c021b1207050d050f301201140f03010e030301090b060a02060a1812020709050a090807020d0807021305100b0a12110f04060c1b061205 65
    0x803540c8040030380002442011954011940904541d492884041c000e410302000540d22071501183c410400000c0404d98908850f401c860004c0c0001c1180380280c100142a007019899028503d00079025210016450307004104150540b10080031142800b406406209801000c40c0107203001400101e6803015080d07480c10b00144403590403024180040d00703580d065400000150004001003207201c000340185881e101c000c485440c144440d12000a507208402000c007649581c8640a0b012a0a414414103071101d130449902c3c100c444c20840701940d10121440b4a404040c60440014400751040c410891002d5101c0c4c0c9062911030242c0801040d40020a02514919000c100040050f541d413040d5400c02414001e000c20603207030004d9026482441d96000c0007100d2000c0000d111100d51007502c028602d80b449400054100000c20846a00c0c011a0301d600207000c80041d0100700f480e0820340100559115801c1d90480818004441c0081364040c490007010654100b00c4007141029a0003643e408 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 398582401 1250 398581151 398581177
    0x60e010c150216020a0605032e0e0a0510050a05030d0e0a0b0c07030303051b0a031802041d0c040c0801030f0809061602030607320403080d0c0f020c0a0308 68
    0xc41d10314440040b640101c080744140d01c1e010540c0300460401c006001300030400c0741001425850308200d250b006020b5004501d141044009248842c465001c0440d00540b464040000d11450506010781c014078042d110289841e903000b1000a26207801518001682e20280c09824041206c2000395030000c0c9000b29642c1c0800e0200001c21407a08800190000d03646000c01805510f241d8100039040301c0303002e0800309941c0306d946200300d5005504000c031580700c0182d1900041e00090110307101d580a0007848000e60240c02c010074500c2d1081520030014119049106449100391200308004c21540c424011001003001480100080b680c1c109409110902640b031480c50900000001840c1e580300400e410102a001020700065040c1000b004d0f502882c641400140101030440040d2410314032582611001280f8880c580d005070304906490056521410b155201e02c110803261000d41407440700c00000840072246184503e200081903520f080c8080d01d15610641191500e550301d0307025000450709 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 398583651 1250 398582401 398582423
    0x6041518060b07060c08070c08120c070212061e010e0103060e031309022502030c0f040b18060111070f0902160209090606010e06070b0112050118030203090901090204060e010c 77
    0x8010240c2d80180141442824002810700c48040b0145c4181e802030014820025988006800900d207001190550381c1a44402c0d2030329030f1040ca001216201d080c000940000801c0b16103141c070280061103078014410201090141e4000307a0004207224006d102d1007100101100042010600590005042490300410390b80f408503c0e804d4550a060580d10070b80c3c0e0710340d00181d01d1100c003441c41610300b43e9507290b202c000403404064000a03540d8801c910628880c0c080d084100109554035404020400c1e0043c0103200307590340c0505030103088601201c90300c0c0030802c41032110b012a82d012400c1c02c03e980c41c14602807040ca04052601c03001b50083c0030341e009454054180d140c0542d54000301280705801e41c0c4020102c51910900041c0b8414899500a00818040c415040000c0c0e80a5042d41900c0044980c01c003041061309015014008400007a41c0765940c0c001d00d5001d05901000515141400741e400c0c051590340c5403407072422440b85118a80000d0740414a004583d03104281003a0141c0c0241c46483d5 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 398584901 1250 398583651 398583659
    0x1020c1e0f101e030605210709180b0f240102030f04140316050112180611030702010e1513050a0c170f0106060504120f0b010e040b0604151806 63
    0x1c2c11600c509590003c21000ca02c0403000b852101d09620b60740640d45018070680307140401203211016035000f00940d2078114100c1c0703034000e40200080740c0244a034000504c07255400120110388006c4c140c0c0240d8170701c15240c0020340d41514840000d13002e1000c0e0b040080355011402e65140304118400500c03030460004000d0103110800ca9000b42c005880d5000203071003e07401003020145809a007201c220120141e90f081081030b40c2e0001c007141142e01c25102c020444080c8281c075412071291a0348014042d80c50081c42000d0700d2100c801440c4500e620b034000f000880c030003600e0155076404a02040001c0c4801c0800602020701180264000328070070002ca0780c103d802c81ea81c0180480964001c026a03100c88041d880054604012131a001e00403000200b04407070600100402e988224000c40400e14036aa002c03034100011511032000054100d103c1501550711402443c4c2902010743d0182d409258440225429141c28070032100d1600c2842c1c1c03071003107040c5040d008170104002c4103040346d200c0380d90f40c000003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 398586151 1250 398584901 398584909
    0x30e0d06020f0a0f0305060d15020c2404021c02030309040b010c020a060815060c0303070807050f21010803031003060c03180f02040c0203040810020f0403050a06150501020c1e0f 78
    0x4024103105413251103c916116800608807080144414400d144250003503021681e800390304403540c280c3c4600940d42d61604041180381003100c0d1250340b20700d004070344201082c282e810911400785200b240c21034071843d001c50b0b501d6281c01c00c2d814043d5041c0c0080282e01a01d01e85584140b07110341c01030500c07002d0841107400040c0000000d82c054404500c0020030000008040c01040b40e04072811148142041811002c1131366a0000421500900c50024042010300e0302940075910031114404442e5a14142c4030f01d800400c2c04802c00f0048480310103400442e01d1100402542c2c490b003520310002d0041465915000d0141c80b59100d03410506643d02d05a01416007901c0d203400d5841d0048485661601c220b03c1800100c60300301e20294115081800300b8060008003161641d162891414056225900124048824403441e4070007400d6105800544080210b507400c101038540807000c03418111580d0b02c0040e13850f003807504010b82d48602100601c80f40c0a51000320b544110034007a00e807020501041d8081 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 398587401 1250 398586151 398586157
    0x61e0d0618050105090702030f3c120105010903150c12060806090c090106090303051c05012c011511070b1b06010819150e0d05071707030e0d06020f 65
    0x210068540b8018003d40c11300e0801c1c0d540022040c8001c500d0107100304400b0485000710790304000340719912140c00c0b402c0d0840030020103c01d0b1910300440900340103004124120b600411310800216921400050958054083d0704210303038000e074800c1140702080341c00000500800c5440418021000e0b04e008804406100e0304024080a20003170003a410003202d441c2c0b4155254601c14462078501c4014410b076030380301c100e40088035450305210703880760b1021285114078201200a007509500d030400009011280502c600d4607050b15441031b01142140400c6001d4011003405184c4c500c00241040c0c480451003a5610414050b41d00180e591064440c20f644410382e11180c07030035070014030840107810b10010a00c4240c0c01080d01d28028111304100350b204c881d030b0610641014001041c82000100c4110302e54001c0401c480e020b10941c1d00c0d01c2d56065000d0040d4000300019503401c40c1c026010349042c034285c07049440340750301a00d408410701000004c00004001d81801102d000d502401901d034402401406 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 398588651 1250 398587401 398587439
    0x8030a02010f0b0d11010c05010f2306040e0718061a1e0a0804020f0402070f08040906091e0b0307080d05090906032a121005090c061e0d06 61
    0x204440a00c030b0003800030740c0c402040749486410006880000554111603101e103a60007800d026080c002d00b420901d00418005480c0303841907082058650040301c1c048691a01720a0b041c4604e00c95440d40001e01c030446034280c0d913503400c3d03030b00030700080c41140c4101060b20080b41102c840450041d46070100300c0c0c090311014003910711107140800e1060540028442a5212120f1150018107245811800410140c009040a402403081c0f0742d40005a490f6034044820203134001103103c1d1060b100b440c20360b1959105200c0c0401c220302d800004207001965001d24107591148140d8082d00b20503023181c04009180061046074140310322040003681c2132041c00115070461b0710ba1030305a144d0300a1028042c40c090018803041c440e4008594070421240700802c1001100e003100d108004102c1c86e100450540d0700c0d06e0342e1103007680c492010f0048480d0559044940f02d24101e0043e2686800c800c41800003500a00e0703825452a000b00c1003450041d410040500740c0258200c00108401c0d6940340ca100c090080119 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 398589901 1250 398588651 398588653
    0xb10090f0b0f01020d2a02060a0804110a06020a0b07210501091a0618030102090a121103010e0601090e0118030f0908030306060d0504020a0806190605060a050307030f0608030a02 78
    0x2040902070302d82444040c41c50b48080c0080e061903203224074024560301020076503032038000c020b0302c01c1c0032030742d03845807180c0400da501400096030740401e603070007815010049804503100707842d2000c111071904049200c401110300d641c0081c0520010740d60303079041040c0d0080c002010041000010308000d8035810900c0c6c1c5d6805484000503003075040603d40e400740c0707034400400854450014001c035055203c1204860341780811850b4400c44840c0308002902a20504071425441044c200d4081101c00b0740c110030602080c82240407807261b1010030305260980f1400d02d104240e80e0010401000081c005411080d0943d060000006004a0083c0c06901c0380450f10806da00042040303107080d40c4150018850f20182007280004c60440c035101001944070321504400542441d141c1021804548445488001401424043e60704a00d00380e60008540d19801d0038100029092043c00107a0303080c584111044005c00e507950619650381e00500f0b81c0a0983c0b0500d00e10441d698090010b00d110052000d08003583e8244c0c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 398591151 1250 398589901 398589911
    0xa06050103140c0102070308030105010804020f0907050a0809190201121413030f140f071b14030706090302060901030e1c02011b020303060d03081f0b03041205090d0b10090f 76
    0x2c14451415071040c40b1941035600000040c00415005030645e41110801d00e00f10396590f0716840845e240d114030b1201e10381c1000400d021702c2030040d04a000351106a0182c1d0780d1350425612032070020380c2d41c04044805aa44d02c0c404804ca805540305508800d90444014000304c0c40f0218007103400c451401c00c80d681114100145c070750310100340d48003071610801da00502e00880d1240407444000c01038401e58800003445500083d0440800401d4020440c0d03e04052032a2100c01d40d8a030030203000052800c0f0424420f004640001c5220b50003003160400f40da4001c0c025034101210080154002d1440c0301c031020080c8100307a000740b1404145100495000e0480d400880c44070b1100c03d81e41007038100b01c907082e02990000c4c010000140c071024540898070b50549420101074444111400004040c0d03403244205c1c658020004c60307181e003100c1c02103001e544103110000c5280c600100803120740c0519640710340e008040110030400f084240145580040510301054040c541e944c03064000c498080340800b070300c84d80350 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 398592401 1250 398591151 398591183
    0x1b07120905011d0a150309051e0f06130813050913020a120302100c050405030d031a0603040308040620130f24030c0c060c020a060606031b0c02030a06050103 69
    0x2c40c400f004144505481e41036184810000160b04164500415030a418004c03c02c0c001c0a21940040c003106030040240d44080b2003c00001d050b01c03503915046d507500c0c42100c02c2d040304001c00081e40b03481446514110752080c1344558410f0240d9200303603e5140c1c0d480705240f02042681d2010f8800380140b41d904140080c0641c2032052058420055000c420700c0c81403800060042a00410340c807040503620000015aa00481400d884500882e000250903205299241c80780c1ca415510101c01c0800038919042400e02e03c008012a511081b24004e000520100200c0c00003a502d0304000b42c1800b40d003070b9213012544c1d03207407280c4081c3d0490346500000500b0700c6010418030220a11b800080c150f0140101400d08043c0e414000c8411540703201010142e0f208400c0802a01c10311210080e1503100c130007030100e01948000255604240c0400355900d030b14110700015801d02034460201c02035058a10980034010503101a03490302031050080c0c0e0035000d08102c1c040060500c0c40f80ca400b8610810286116541c5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 398593651 1250 398592401 398592407
    0x2060a0203030601090b04060c0209040f0b0103080301090f0501063507230405280b16060e06010501020c0f010306030206030a09031403070e0f032406150f031b0712090501 75
    0x15586c4001c02d03104003000b0a0159603400200e141c21980c041e180144c20341c80c1c901e440c03d441454100301400c89940440040100056100114125004900e083c0020700e0030398204401c0394801c2c4208400706007442d504200d03911202071140c001085440745000d003440c1d01034207150300101c00c0303404600141103901c001d84a6203a4100d03e00c148030045a900e41003078201804280107514250310445400b103a864901c8482c96000110000390264403d8179403501080e040050040c8a8510300315941d07800c1c185000740d11500006d640703041750310580c0100b40303581084043c40f01580380b40b914281016100d2001002503182d2130002c42c000c201805001840e082142001030907c41440e2080505000030000e1054041c1d00c003800d201e845038100e81415141600d5000285460020316900d240907000b0a1002203860503881c885120b45015900c9205400804840a81c00e200b905110040203074140b02040f0310303880100c040899119140c8402d0b1510a1648031030300c540764110b0b003a00001d00c1e018000d0110703580c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 398594901 1250 398593651 398593667
    0x3050c10020912121b0f01060909030806040c08040215090405041109010b0435060a1b1110020d02040f080105011d04050a14030d0f0509060714220302060a0203030601 73
    0x1c9102d011345039022800403204a284501c880020542600a514111220f010301546030581c101d81c00800c1081d940c0c440010103844080829000b28044000203a86402c0500404801c0c00b0640d665403031945d0b0b030340d007000509915100740783c080b0303c0f0500c4281c02d00e8070307036100c0c041c0154020903180126020030010080003100507003100c2048003003803208200d0070b440b004420000c98926000c42105561200c01c0347d0b41c9004283c45a1500e01c1850240500a02654010303001580100b40a00340f450751240165903c000c502090a000d6200144c0c400a1a50541c060010101c1e5030030050b00e0150340d0019480043d42d1398000c1040d5075034038030040254103071402c0d0070b401c0d0100803022030301e1a2170300c0e0301c07069141c41d140000a03001444145403404c5d03181d4280121101e44404c01c42c2044500d800c54141e40041c4401c9a901c101403068030041012a805008561380140c0442e103064980b1028a60400351726400150b580c2900788105008070061b91342102400701214542d004540701e1030000001054a0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 398596151 1250 398594901 398594929
    0x90510050f1002072d090204081b040908041e08121815071406090109120c020406090f02040e09060907063f1d0714061209030703080a15050d03050c100209 68
    0x380c1f0401c420003044d200481ea1902e80000c80704100750b0b4200d81d43c04a0040c000004009180c400700040124103141e040a508018025020b612500075846104403592508000d030070b1018405c0502202c1084511880b80000114000c2c00420307699110140c60111030b0065601100d407452000e1909003045000c005440d4080c004030002d02c5170311115240c14003503002000114040140f5002840195241d80d045000240160a000c10000802c00b012400a41007802540c40f10204440070840e020800a4401e004040350030203005001d1420f0302c143c0e005207012422040e541c4000207141c212504600145541c80d010843e41510030021584070002c548404250b140380e449405600303043c500001414006554246808071000c844680020b8100d005039081c0725160610394040114456000c030203405118800c1c0c90302d0001c0c0c0c40b072290702c00039580d05040344c01e0000842c14042105240022500e0710150203401c0281c0b8003000302680a0405400a9240010340d030002042ca01604006a4040040c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 398597401 1250 398596151 398596169
    0x60a0503160c240b09011403010b090c0301120c0e0a091e0510020d0207050102040f0305010b01140304120e090f060a060504030c090905070803040609090510050f1002072d 75
    0x1200b19070b5a110030301088444000314010b0003c4000400599503000381c00465000300441000d6035214032158507100525440d40c007a5003003504000725820012009030003450000c1d0b9650650307082540382038030016003e50070383c0c7d001c2d00b01100013202c00e000c2ca40d081c010403560b0004a00c182031424200d00095500c2094111705100c000e205012a60109035105c0104043c2c101581d510314181c6030350040d024210b0044c095510005000501e88225500c14044034401d5000b03202d0f045e0300c0740055809a50506030110b03486410400940000c01802182c0c10424503803d003001d28190070004901c00440c1140c0440c252600e000c00c0c4103142c50800041c10041c049490b2080c030b042e0070350351118407105492103802a1303192207040340790800900b808104064a0b081040b49e407a00c3d5900c60041c40c401c45032164458a07450310011440c2d42d0010304a401c15a100a8000c40308400c03404c0a00800b1411340f18483c085008488001c00d4034038220410b02d1588114407000c400c006280b41e440c0c582d10005500680344 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 398598651 1250 398597401 398597417
    0x9130209150322060b0a08070905070507081801200a020405090c0f040e07052205061e060901120608010b01020c030705360a0203160c1e050705060a050316 68
    0x4681c40000a4448071014080d42c040240c09140c60005170050426250b40049080300100d00b0b031500003825401c96414980034031039901c40045c190707801d105141014001103001c001c600102c080e5080c05004c2d4040604d82002341d4041d83c0000035000e02601c10001da560008503c3d2015807030329015064010307044a0103031a9080f81d9800141f03c240300c03085814051038580d030051103041c400340042c100500d400303415110450034190955064400e41c44030380c4650351400001c40c0450030684100301e000805001c9284441601030200180368001a6806040100e800401c4000e03001c0390050100801543c0d001140340201d5074000b90501c12500c01107070103607100d003008000c1d41e90f41404021191002c030080c000c0310210703800a104100c0181207c0c81c10f803002c0b40d05001707001d8110342c0258407600748401d810340c054402c0c0f041110150440b410207800c000700750000210041c0502c03140c42d8581c1c441c0c81143d07070301c5d5a41c101080c0540c000010074000310f4000700401618080c030050352006507080b8030305060 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 398599901 1250 398598651 398598661
    0x708061006111f0c020a0203031204020108011a040303050c10060801020c01060902120a2007030906110607090504320103031b05120d0f1407030c05090901090c05091302091503 77
    0x510b030400c981c40c00d42d0136210307019034158a000340a038244058001d8203580c0d0b034010f68456a0030041d800e540881c0041e070964000615110001020f910b0821510041441c0500d0b6031003caa560700401418405030084071002c0d03203181850f01c19a801014544009611012449241800c6541603440b245500303004020544180c0c20b0f984000382d100c51100400aa5262000f05090998079010903185142070009240340915402c10704000071145c5a07034030340b0349160081105a0326010290341007004600c0e012414002d600d4075410400c00d088801c02d03070703141d14030401e00d034081c000c40407e4041c2501d004200c018814564060015000c200441412044811943c0c0c2d59541c1c0e0740140d00032200700319011a8414899036150170841c0400d410403001e200d03200d001c0b40d85000c0078909a400b18042460b06407010950380c005c4003954a070a01c000e0802d10280c0c41c0010110203441c688504000f0010100102241a0307101d51205a00c00076100740107071581448400e201c000031004900602d895802d00c00c101e = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 398601151 1250 398599901 398599933
    0x6030510021312050c0d0516150c0f150c030b13020a0c0609031b0809010e0f01021f1b05040f0f0b1c06080123011d040311070806100611 60
    0x41240c0c50303001c0e803650f800d4842c00c04034101900c003030200b0b034406441c5806c80144000000c04010703050803c2d181441c40e0341e54001c10415400d131040060007203556541c41070086412a00c0304e4126a02400540701e01e1015110b0301c2003254195810303500842d81e07640c11044582401a1070f0b00428040000c1145041380d12803018004c403200f0000240010317191200c810405200d0b51a8003865014102c0324841c9040360316088500343c001c0021b407400030b40c2c20044002580751445040081b1681a009480443c5c9885d4803078501800b0322060002c415241d2440d0810981e2089104000e58066950715480d541426810240401d4503800f6103038402018400b400710782040702c112074181d1401a8022401d181040e15203001d040c0b0703a8801200c07035107494030b1a01c0c1d000074449051540300c100f91079500b82e81c4e2910701801c60281e10400d641c07044018203001900180c09100c0b540038900c110b074100d03440d05540744041450b04d503048034800850056807204000058120040c12025203040c1d0190400041c409000c03 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 398602401 1250 398601151 398601187
    0x71b050a030b0c09030a290f0c0a03090c0305010c080f10060e011115150904110607051903120c030e0a120302040f03060b240a0e0f0d03030603051002 66
    0x78005555401c0402e0f4410020003c852142c0e1014050380e00780421420030b01c5190803014079904c4d545084c0081c80140c038014020007072050120000c02d00b242e4039000780c03030072a50300082040e506040c2e40c1c410074004240c07603884120044d84900e00228083c041060300411a4402a150401c2c1c504c944040c044154128200041620381c107241160404918070012141000040d0401c4528003826080c0340300e00ca60011038911030212503500c505109800024440c00c0603003220b01804017462080404140d290800c018403681d40030b041164204010441c0005411240410031001300f00b011410519000c013070300071590010114202000818001000191941400c101c028480c181c0c05c201d0f24032032806641901c2c06003184201c603a254640b80d1410400900724082c0c0d25100340031000168610100c000d88544a122a41c0031441c104400d0700c4054422864070321034140d02c2407003140803003410b0f00c0d20300361341240c0c034066030303021443c2440c600b0300605044080d5441d00140d4010420f04241821040e08 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 398603651 1250 398602401 398602403
    0x50c0c040e06010609081c032c0d02010b03030a080a090201271806030b070e131814070f120c05090a0507031b09030b0910050718080712060207020f03010e03071b050a03 74
    0x10208040d1000940300f00340c0c248400d0201100700c21280141204040080c141001c1041c40cbc00030030101d5106003c06a0b207010b1a0441000103860f40d0010745161a0740d0040403c031881030500c000b500745010008460b00030040b032591621151000b0400c0100d07004004498500c1408004204a604549400b428544020301580038004141240f1b003d544038002048040c80030600c04100d941c403503441031103652503505000d40700081000741c00f1282c000082041011281c407a0502c0c88207918204544405000040e4207444100d9060b10019a03511842c0c610340c468180b5500c0025986000b100107002c48003c0a600009140ca20380103d00e404d407c24040410781e6080b010300d0b107490340c131400c0807440c00d100684c81030701150500c400e0050840c2c120551409450b03620001110094403005040d580d25030501c04d50000c0310710140c007140802c0156008180a50001c0e006040c00030004c404a800e480010401d0a4183e20025210050120703100100044001e0800c1d1051a6031406d000603242e0805400 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 398604901 1250 398603651 398603657
    0x30105060919090e070e011412010e2e0c080712272307140105070606061d04051e07090e010b0403030e06070210050c0c040e06010609081c 61
    0x30704001d2991220041d608040c10b1002d211a195125031004018007500c900341038a6108100001c1030941c140d910f518140d4031444080e0048200d11410040c0c155144054030b4400d550b10700d466922107400313201c0c582c8003440e5001403440303407400480d0500d01000d4104880782c0c4603281440e511219a40701e136100c1c0d04005075181501ca03916415107044018240911942c40000d0315000742c20000241d5090203400c60b02603070052000c0c84000c203240c0000140f104d010440c60b0040e86c003d01c0036080382050f4944d1450185041801c00c0d005941d1001100c046030414004903064054905a4441c510a10740007074006880c20300c81ca043c10340ea4a008000801c1845000644d0040000c00080c420303e00c0e00001c0426001400071565160724085c1c5a90142c0070136000554043c80810301c504000040b55845a4040d003d10403078544002e003143d40e0b40101080b041b05001c0c104018096a40b20700840b26280300040252046500d0400b01070171082056101d404545c00c54165440c100c1141c82800d180d070032a9007 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 398606151 1250 398604901 398604907
    0x7020f06180a03060e010c020703050c0d0303110a080103150b09040b0a020f040e16090e0609041b0308040e07030902150c030d020c0c041d071e0801110316080c03010506 74
    0x1c0382541c0c81c021000344503074004491200010622035290418408000068000c001e2106281c0c4200e894024900029040e070340103041180c1207007042c0642008090107490b00080d00801d410960017564002900301000070244170050044c00820700303010a400350744090401040040030b001c90314000b001003010380401d08010001c0c1140d01035804403003620304110401d5a0311616601c0043c0c4100c0c041e640ca08500c180c044000725000c0c000c001c50000d580d030403030f1140e031295100782c20416080d00050040f100030a51041112114409048c40340146118104051721141401800205014002e115800b050305200c0c0580c0940c66201010301c02c0a8081c40d03855403020700d408554650f100340070850303144510000e421446940081640f43c074105040f0f80511090b1200640e484250119010985207900507420400520b4018142e180074002e1058281900c0c40d80c580c0c0842c02c450000d189079084010000403c002221000d07607214265000b41000805400e013004442c1d511301050180d540150800 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 398607401 1250 398606151 398606167
    0xb0a20090a050306010b13091e090317130b09010209060415030204030b0f1f05090a0903180807080d050c030d09050109020901080d1101020c0a0b07120501030803070e01020307020f06 80
    0x81d074840c4040e0601400b11601969941030306034071540000503150301200e9100c40071981020710300801e0041c3c08800100581040c01d00740c120020031018100310b0901c564110001071649003541c840381324420001c54030b280c00115040c400081880104a101c5a9204000d001e1455884402b81c070251079401c01403000040d0005010b9009204540000e004200700c4820407110b0f07070205050701c1c030800b008558400d40c0b01c0a09140c00036401c45008095200d4040c0c000540844500e0340705010090291820294040c403644810190428a03000801c1c107800c501000e01400b0303001c220070340310030720986443e07450103180c09501512800350411007445a501c076400841400805d402c10806180c0050611300d595a54a0010b5a62404003803401c012998201c007084000380c040c401e8400302c4554001030442c05410b941c804040440c000d202206000040c1200309204000d480750a010b9807046c0066070b580d041c5104060b1840c07000303045141c1154410001140140c985509070f00383ea14050300c20f26100c40718 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 398608651 1250 398607401 398607409
    0x91b150306130e030304030e010c0c05120a0b0408070209010509090c06130b0c010c02120a0c0206030907080a060c08100641030a0f0e21160f0b0a2009 66
    0x3070603100d500c003c0c100707401e003820350502200450045110343c4031481c2002c40c0c0c000546804443d5400a44011030a980801041c1040014040c031800da05c01a1001220b140c1e4038910f582d0f6095505503107610000c100c2c101141400c0f01200e003d800100c8000611340f6265800359542c05001450b5409018007062402504030904060000740492201c0e05403181c0c140c0010758003c0c039102502000504c10007807482c0003011014200e840409569848925080305a024001903500180601e80140708505001071440303000c0c442c03a5a081e101d090045240c14600100400c1090080c2482c19000282042003009070381080114860380182c2141c81e582031880300703190070002c1c000c50103085074014a11200c0921030480000b0342c07058003545000c101c81c001002e81001100c20b290210620383e44a032030100400e4007000032094915052603503480c50a6081540444409240b40040703500c840700e0600d94041142e0340502940c0a206041308000700d000c3c1c483d10030f003680740480c5210b80b5504000340224098070303 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 398609901 1250 398608651 398608669
    0x503120714010f05011d0a0506010c080c03090d1b08061e0402010c021908061501141c0f05071b05030901031508010e0f1c08040201120f0f05091b150306 67
    0x510b203c100200e41c3d40d00303802d0010707013003000001c0d829000318800541000118440c4502405042e074427450046000c0d44d8444182e808401414a10b20040c010249107070350b1055241541072144541000303000c6103807840610b0418942000c2000d402c40c3e03041001d20200040c0c42401320007031000d1010b0307640b254001610740509030b250194200700c4e00c07051101a6141602c2c628201c625600c21038103d65102070030b12800102e220300c02c50010789a040e0310344141c0b0600c0050290f26810b841d07040020001519102c040300d40f191069080103440707500f00205660843c0b0421f0000140141040b0387c16405e54503161a44661500141850380c0da8001b40c0380500c0640704034000d040548020028001d80c21419640c940e6101e14150080c03180c091928440f407240a4849034281440d11003041e41d49541d801511814550642841c84a60307804100300049154003071600064a01c540c0000c0f942408040141444201c410b0b000d80c91141017501a0f8640390310840d0706450030b43c04021620f1341c0314840003d103045 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 398611151 1250 398609901 398609921
    0xc1a010e0f041505160f0207031112151302090105041515020307080c0105090c0111030706110702040207060f18020604090b010216230a0e2a1204020a050312071401 72
    0xf901d08800c000030b40308130b954200c010070036075220110800440e0b88100e039915a1400300820300070108100c4a000d04255070790b4544807106105881d0300042c540c0100a9143c011500b032284100e8009171142941098a501030140c581a20b003448143c07002001840b1103009441525481c485400194038101d10920a541000340c0c0038094583c0c0e1b10703807000154064a0291910203460040400b40078196000d1030414903c5220f06029500302440d90300c800e80140040c03200841d207a00200000300c01aa203500c003c11402e4468000020b20042e400249400c80304035419010020100c1d0586201603900d000c1514115220b100c004111606c2400040b42807004c2028500e11009580001080000d200c5202c1402c805003140681096040407081010140d02441800d10010000c004154000d00c04e0341c01d4103d29181d560701052400785810243c584e07501c80303001544440b003000d051104514003000c02e00c00906048000300340300c14407254070a08511805800400a0b51a5510210320760801e4014031111 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 398612401 1250 398611151 398611193
    0x301060b07030c06050a02070201020a06020327060f061e0904050309061201031a0c1602030a020307080d020106090c02030306130b040f0c02010b1002060112020604080d0c1a010e0f04 80
    0xc0c201d18a070152140420320340488182d41000001060180544261400650164010302071002d0039110761000354806814003000c0c0807100080b0107080100d400d000c54100d10b40c07000b8061343c500707089a8580c031040035061030b105004440707030f080c0244529402c440c1821801c40d0030800030344852800710f140d032203507003207041d0070610108044041c401e06038040340c100d0b03018820302030f110741084050b21030081044130b200a0f12502400414401c804511201c0b005920182c211130110350f803600024500041c42e4030030007071940a8824040b0f110b50a0050100420203040140401011448042c0d00c03800001c08041c0150640c3d0012058100c00350081c400d4104081d0040085540f101c0c1480003a0280000d43c1e00950b003401e03640075440c100440d40d40c0075000340f5409000e245e401d10048041c80c8400300c00030390703001405000110b13540106001c0e202d8994280c0e11480030704101440d02d801c900001d02000b0041c3d030404801000080303118041030f9400061582200303581c2c0d03214a03198580340c111020440c51 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 398613651 1250 398612401 398612407
    0xa020c150a1b0c08031b0d0504060b040b010903050312100f030b0403030c110604110f1903050f0d0e010e0d050d090f0b0c0a020f030a1e03080c04230301060b 69
    0xd070349a008040020b00c0c10040d940314030b0440001d46002c2105040100b42c0c0c00200300003903e5007103c401d500071003011010b0041ca00038000410704280d4400350740c02d581095076030240d003c1620b004c0c0300c0c1001c491401e08007400407034650b1f00ca0a88070702440d401080b40b6880c010002d16540c06400044005d08402c01340101403507117900f48100c40c20740840d401c8000c81d1030120082030960080d10300480e00d040b14401007005030740c0e0340c1d100c07034408015288403508285030402460f180d596100940b501c14102c5141079144500e141002031401d4219040c80c40d0a8010380000c42c155903000c0b03000712a610003820408031409140300800c0c2d00d108240700251a07400380c02044094154003007440d404980c0e0070382440740d06640b541c25810a600c030324850400c107a032007400d1540050030800d0660f10a440c0c01070585108105a441d03030340c1c580c3c403015100302182e40800b154408040e0400300e295000540341c82c08500f001c2c20718080d1101e04400030710120940b44d440380303402602d64094200d0300142418801e643d072 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 398614901 1250 398613651 398613661
    0x21906020d02160510110304050d05060f010506030705070627120801090c0c02040b270f0a051302010804051e070501020c0607020a031707060c0e1806090a020c15 71
    0x900c81141141c00030050041e031101c000e01030321021840061322802001448642545041175070008004012000c5500051000040d60703501c025008081c00e000d1805003860303281c1108802c4050005070045481510f082c000e00c00f080d81c1c4801a6550b09a0095000803808082d45017030071400008140b00340320000740e0f4042c20401a07c881905100002034079882880c0e62241d81800584441c10311040c00203402c50889005440d060b04103040d4590050205010030040c100e6030b101c0d8aa00031603004030b03404034900380840500100304443d07001c3c055100403c401d007003085490814070044100030341082460800300d4144507090000580d500075440302c6104019001c54115103d0055101345c5025000391040791140e8100f03501114542c540c0108298a950b055a9403400108000c01c0414000e20042c01a000000d609119031120800942c484805101045040181154013003400c055403407104828030100e616001d00c03140c2c02025100002da00c812040740700350316007034103404103492800030346c811b1113 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 398616151 1250 398614901 398614903
    0x1005030109080904050603060613240605220503070b03250819200f0c0304030c05041a09010303080a02070b0c04051801080604030f09180509160b030a050402190602 72
    0x19243c42910203000642c0e0301000c05484203422107045800c40382005414020711001c0d404812569020b000c2c274240c0c5175890b00e01044401c1c0517000b00c0301080c000201c01e07071081800c02c89603500a2180407a8103080e410940843c1c0c80f4031540c400e04051000220119003040d40400d03801004c0400508250800141024001c10b042e000b03a820012080446502101400260103001d4200c019a1510900580c0c1c403941e07815254400c44062081610911151801000501c02400218018000300c842076040504000c100c80c9130440307400d20800480e000b00c0c00d6490309039038181146d4050030042420f66400c014503000e841080d0006000b20141000c0118041e2000090015202c05482d84014013110014003404040203025280484c1d0051b40042c0000344a0394001009602d240b52501a16680700c200d145002d45644040c1d400720b0700d410812046040401c2913207620284400184005490203045120320711010782104001c0341c44078005801c1d0340b03403609010111520981c100381442d079281c50003 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 398617401 1250 398616151 398616157
    0x6240f0c06021303140f0714010c0b01030b0f0c0c100f02160303020304050609070f030b04061b020a2f12010b09070f090e0601050a03020703030f0c050c07051801030b100503010908 79
    0x883d030540b0201c42005e16141d002842c12010380d010401820150b08040f11440e20a4402d140b050400c034403000003a00007020035081500031440b034940520340741804884192106001400c10100c54401d0002041610700010211103d182d160b00c0094048480c908400182c0b040d14801030450300c0c0d10413201e042540c554001c51046002d0004c1d54041d03201d200c18680c45154511551004100206c018070200e405000440c0e04030788120300004900905a1403141070341400d41900340035801404088040c426004841a510141d030288c03000f000c0307415060030b40468030070043c850041c0c480031045802d144096025609101000313000103c5450325000003403070903020807545000101407910004035540304001e10341c01490161101400c01641310801c40094011403000d0b4100747d02e40310040803041e150700c100c0e9204801982c1303240d9075040c21219a03285c248541c0c049401106002046c0410034200020203055030740c45002c004458a4148250f00a000750f0342005501d5482c04000c04c08024800c402 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 398618651 1250 398617401 398617403
    0x120c09191e090e150c16030c0213063b0903040611010501080a120c020d0c061d0f0d051f060e0708060d0201030b041d1006240f0c06021303 61
    0x1e04030205880328030200684003e801d03407100c5039100e2100c11040d0303108805013982c018107405026041c4509894442074010b0364990540124519105801c19801c2c0360008a280e000861010301c4814644030202d00c140280c0706c40e900c0b440f2904140c5144c110b80128490544042e500103901085c184115003580303c0e4010701c02c4001044175400e0810560a040c02428121101c09000d001e6125154941450303000c00142c95804022004a80800607990305080d210a20f001e82400f6489508126001e405d0303104400f0b001c41c1200b10402d841c030580d030301c02035401c0b01c0304000e480c2c00e80000303564581140391128401034007250305400c45024180342401e0717101d9170413604c04c507200d850b040d1158202560400d41c00c3d150300c0e4100d01110117910140d4020b8120641040000e0800104007445c00694200130012082c10065504103550700c000c020350501401010b0914800103040400400e04001c404e815941d801c0802d00c1408104600568016030403880c40c01e401007015550f03280090018651582c00b808 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 398619901 1250 398618651 398618699
    0x60712080606070804170105090d0f0c0309170a03110307261b0105070905010518091f1202031e060714040902280f0923030d020d0311120c0919 63
    0x1c005270300c1c11000601c1e02c4078990a500d502d246000c50308030440b0410414001582846954040000c00c0f441c80c40500240e0700d10780000d404030025618004008240002d030005040e0700034070040b004540707185800c6101c511182d0303041c480d1080c600400c8185004401e0b1a00c1e445a02a2600d902040123400c0644601c0040e9100381e115500d03040107444600620105c5850f100c2d4440d03050842d810480b05180d0040150702070818521848a509900d01c645c0c4d0b0801100f02d1414800f038030440c10208102d00d850020307000d1468490144d600601e56a2400804080030424100c2003d0041a46041160060540a6420356407000c0c003010665414200d6002005848402c8130035200c2144240303141c20078480da558801124624098440c01001c51000c0480340c60038031010042213503681080001800e686d641c014040c42a541c1c48054211060404501c1d01c035402000510061007140702c60350380c4004a6144a5121400724000c80d0540061514400d5158000394022448680000c55503c0e5195101 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 398621151 1250 398619901 398619911
    0x60d0e0f0105040b18010515040203060a08100c140a0f26010f030201020d0809030406051308010507080115030c05120702150c18120a120c1a010e060607120806060708041701 76
    0x21001764201d91040b0b9134114240324819010703030289056001541c002d44024103e0740c003692104401d5041428418802041c2c46d60303040c451850740d8110804009201c3e5101c0d01e0783c00d040e040d80001d440a920b0424510030003505217070b41c5034504c05100c0c1c0d1821111a6020407091581c4940007005d280c0304600060740948a03003400d024005108040541c805d41501000e14105854500241d03403a030050068103107082c01d03c401c0400e1046003441032a00c00c0e101c5640f04c500b21752400240c0d0514211500400041500303000305030380c82d40c2e04041111806410a0201001c665078a0000c0b410840002c0d08020418100020f00ca08d524039107000e400c0d0341101086110441c1800003c009140c040e0512002c120b8100000f4031020402d0f0550480c5072130f032a0305002c651b10101d0364810696808040901d10741ca006a0010b104008440d88a103501901c10f4501070716000058440c075903030b000b41668860030012003800090b0143c0b10700d000c0d98100c50340300b60030644036602c0d600c406201446c66a0001003540c680 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 398622401 1250 398621151 398621191
    0xf050105101d040c0303080a0e010219030b030a030804260c0c010e030106050a0b0c030903120d201804021620091308090a0b0a05130b09060d0e0f0105040b 68
    0x1e80b524500a076444007001003680e2669805071407641008259075082e40d5200105c1c8444c103001c0c0010504001c6100c42e0344628041980007400721803120b42128041e6103d00721007400203802400903a00140c01c07440301c8010030124040020503240c40e4083c07142403000891070401c0d016000500000000c001d80359250400c0f801002c2c5800c95102e4800d2a41c088031340d036401c01c030440740c0b0401808400003c10a0704e02d805c070f640000ca894001d042180040e540c2c0001010301c1800d005100342e070f5554900e11052580700c403009150310000c3c05179030020f512107803508020302c044c0da81d10f0b41200d5000581d0640040320b605d20f410003810030080b582100b01c2c40076054084040c14584090118800c4e48640102e4075051420f440780300032900b00d2500c180d045000c4035404900300340d042c4058901c1241d541e807403a039524218606488000410b50042201d61420b0100d00c00c980c1d00c0fa4181c2d20420051080000d46550b1400a985405a002d407401440d51804080c002845482000144101e03142c408034100c541507 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 398623651 1250 398622401 398622449
    0x20717070f0c0b0f0405040902040b030d05040f06050f0f09011806030f0e0a030c0b0a0b0603010b0d1803020d0315030c080604050d02060f0708070203072307210f0f05010510 76
    0x3c0c0740c513005802e4404000502841ca07080c0d0141c188540080d01c002120395056004c01e161a0b400c451040c0850004602048560b0301518064090b00c0d141c80e145042c012401c0c0d6040980c050601d0361950107a01044096150748540c0c50510000e0005020740d4410790b45441c064018900030850182a03400c1004404641c0800980000a645e0503074810415004945a247d5506406092810741a441d090801226a40d00b4043c0d400303810207d1900d41c0e91040d00c0058802c0300d546a4403a51000e40050b952404a600845c001030007551608010540500030f15400800c44c4058000826a03a40c045c03000c900700b400010290310883c400c4040b243c0c912031011007a6a2000b0444810304007020b02d800049201d44104422038208109004176030034075016a0703071402e8011954804410301c0d6111011011800b00c2007010400034001440c00214285d00c0101403840c861011001808101a51480c1c0080002d074040d62070083d43c009008000600703101ccc0c11180082c205208807071291400226584054031 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 398624901 1250 398623651 398623657
    0x30b06030405030702040b030f03070803190b180702150c040602070b0f070f020402040803030f04120f1706010905060706020301060f0e0f0904030201020c10050402180712020717070f0c0b 82
    0x5041070043d81001c84aa0811010b040841d5450b5018016801e10003110700303081014100551003241625283d142240600060801001040c0316803400c05ca544c80083c0c440b040008110328240c8103c09240d9a00201a0700c1c203544c18100750700b00ba052104100c0200c002c00081e0043c1c81007607003500c0c2d83c580da441100c03400d401038810688011004010000000d20306400c0c101c1744c51b01c0544054101507840b8030160031a0404c0f40c0580070040200104000c12200d0340715000c040d40f403410020301f980c071444001019803102c2e00700c02d4913003004c060100e005a070180348448000c18009215943d0b4290b1031030704c800a50802c1c400c3c0c6001c181000008051640240e401404000000c0d09000c03005c00c01c03000304900320b4800b43c815019550b0800c900c0d0103243c01400362081d00b40d030648000c41c890802d403041c0b15000e440f480514100da6034000c01c0c409050b5204130864060302803040c003d40c44600c0c606008070300e014443c100c403100300f200103014405c208107041c070001090702a004100b843d943e03d811a20540c4 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 398626151 1250 398624901 398624903
    0x418060f06030c0903020d14010e2d150c070c06020a0f020402031504020c070503150c091207080105070806040515030309100903050102210a0606020606010c0f120f030b060304 77
    0x10603186028400c040c800d40c40006100450310f041c0c103000359283c0200740c5450fa03800040d02c8000c0303845121000041c0034001c0f103280c103650900404c103036140050352a403000c40048040442568041c141104e01c0001c1080d80070710900b107100c00c01181480314480100d87d11468040310382110145c0c000a0342800410380e484126008030031600403618650810009520080900c6402c940c4104021110740302c40c400f62108000c400b009140040c00d1508042c904840c180c00504002088010401001035050a44200c00005c0c0d80c0c07003081d804102046401c000040e0020882c5c0d41c0f9001c01c1009040d80004031902803401030b41c04110540341c840c0800352841d00d04030706641650082205000c14189544600c0105455242c107a1240c0d03100d9a61909a9004000c505600242403c03c0300c0102c142170092500700d181084200441880c00d1400b0b03403100c80c014038107410310440340468410b00144140c0300401d0b80d404140100041c6c00e4440c040c20f505101c030f0400d0000703444c01d40050f1050400c0000c50f0b00603 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 398627401 1250 398626151 398626169
    0x50f060117090c090c121812030c0f090109081009030906020f0d1404050a0326030f1513020a031506020d0210020309010618061d010b03040605180d05041806 69
    0x88030f0080c2403107015038015100001e003450402280802c0c04c01d485251b8010300e10000e5804d101c03000c0c0c00c0c00c00d2030301c0803c0c0030303050480c5402c00c24000350740c2c4104101c0c1c000001800c050394a82258000507a03403a24903078071000c11070143c106107035000d80040e802f1910851280c0c40b44100141c5406040f41c4d511300c3c071a003007031b065400343d00c2d820400b500a002c2d05582c01d40503500c1c1e600c0c040d12080441d001021a41c01210400351800a4607462510040c101a6a55110b030b002800c6250010241d941702c00054282e0740314450409112200384c40d1800800011407000000b07541e564911a8014001c000482e030792400355944000215180b8804512520007000c140d004000712100506010000d51000d0140e440b10340da80c0c40e000910505110414240341c085000c0094201c1c41d11840140b01d058201c20b980f0719001d0340e001884807010b00000c0d682c10070f401c41c400140e80e41e41d45003000d02000300004410040c1c41016401c420384c3c0e5010000f842590301085210214054000f5884261034441c028101e403 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 398628651 1250 398627401 398627413
    0x919110c1905010b12060a050c0a1b060f090807021509060d27030203040f060e0a0b07030903080d092001020d1103070b181c051813050f06011709 64
    0x9409241d48498074490b020300000104160204000b4031a80c804004014054011404128001c00b0511409078041840481c451505002501c01001000504400d4810000c0c20080009004280c3e0090403d512844000c010700c03c4182040e5401750400b4408a205602003c0000107000078001541c0680001400040c10190718001050150907011503035180e80ca41c0d6101d003d00901e416002c6c0403002c3c0660080c2d690740e400c0c0914401c888010b5005030091181d4503048101d1a101c00903e0350465071a5910b03261178140b5407404903402c595035840a4a011004610b44101c20f0469000229907480780e5100d1240c02100326001031107c448206c00780c0541c10840703547c04901c5c0a404a480c0300780c90308c0180c910388034041d981d100f03030760b0b805544040f0207628100e10700365080d0041142254000041c4800c01c10380c0744072038009040384941404060550108004e024207a1244c615042c000ea013424800d000502d881c0004812801c070441d41c2e2030000b10302d00c900e0400d808600c103155014444407006884 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 398629901 1250 398628651 398628673
    0x3010b0417161a0909070e0910030803160203090a0311011701030f02091806010905040b070c0c0b0f0706141e16030216140708060121020f010c020919110c 68
    0x2450b1880b4440307000d100441004034040313a503140d00d0891310a0020340c50b9183e0409184c02406480c0d24020b003012038102900d2801e0010595400c10f60b64000803d10b80c0b6049000d00303190480c194043c0031149a04090340c48004810055a11300c10380b105a000c0c0e90703219006d071501c820340d81000d0080c480603105010380401e0001504010541036444080912400b810760f4000546500d0328a00768081691641d0791340a01081020110381c1c0b40d0002900d141c600a4a1003079103407585038000501c44c00a104c6000140c0c5181a01c0e01000d43e040540c020408028118200021640c541812265000b80315000c130f0328040da5180902180b0300440498064174075013050601c0131303002984000609094a23095003110400641040450415801c0c1c0c1c501400c0321034074280f000340c030348001030700500346d00c020031000c000c0c11000344500342ca42d0a80484034900918007900041c0d400c601440c030040e4004840a040120f1181e4071440c1c0d008c6440e440208001441d030011055600340a141c105108239003000b0f807064 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 398631151 1250 398629901 398629919
    0xa06060f02010204181a06070c03020f0d1101031d0a03080907090c090311011407050109031101020a0e0d0f0606150e03010504030e04051504020d0c0801080a0f080c070b03010b041716 80
    0xa8224038180002e506c2c0e2900c2e140081c0c81500000300440d000310240805004600f05030705490142072007510f043c2006c3d1140c0c0d44001c200101100c1090400d07654200319085c410b42c0c652504c0700d60b04418152107205109044c02003001004960f00c0c001032040c48000540c3d40158031a280c0c1700700c8595180010300703085650b1400f9100c4810b02136410003249801c0d8070302c2c5010240042510a00c42e000004103000309107000b51140c4815807500d50164814446100c00580083d1941c3c030070442281c8034185140c1503d0b104c4a090004400600603510b001404588000d50340405a240c0c502c03600c4600018000108242c01d9880c2214018000b4414581c4040da50a0a80149400200ea040420f00c0d550134140402c080785c001704101040c00e6107810415010030b410082d079501500502014003080049a21642131180b0880002040c881000403004908001409500040e00018030050350b00d59541c1c48002c00d5400c40e0086d0520f46441ca017100b9049900020310045040012a003640740318500442c0b4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 398632401 1250 398631151 398631161
    0x40620031b010905120301030303050601030e0705040b06130f0e1f0515070b07090f05180103080705100e070303080f1b18061605010b01020d0c0f03030608060a06060f0201020418 78
    0x1041e0640d20f44060b680041d04c1400030100c2c0c1600100070395100d40c9103080c0213041c3e8074090b12003410705140030801a580701c408540f9000b5204240e401280d14004100420700324480c80c84114620406200e01290428840c01c843c41100c2d03103404a000311f500e43c122500e0010200e01c020340322045545c0e508006509203020071000011301c00740c0d468184072040d01c0b0680e901ca011500000082c580030814020980d0803200c1d40040d090582d8018880e00d644040240220010301014203150b801041100c2040f8040203800050359a00100b40007080d440300500f5964141400104e002c0360001000800e003e6400302d9891003540409401546509240307207070380860b030008898a64015a140c0e0020a42d25003000900801400740300c842c86030140c07810003608641c0c621400c141150003603860002c00981c040c106a074555001400804420f5403803034140e00070203203a88a0801402400d040001e8602d40b6800074080f5442c9840311600082003c40407400c034415401140000720381101d0b87d9089468907440 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 398633651 1250 398632401 398632447
    0x518010504091508061806011208070c060e040b01030903020d11160806090f0a020a14030703121d010f0504120c0506191706090a0e1e0304062003 64
    0x803152901d502c2e03101071010f4400340480001c1c072140311034080114070802c0000c5940b000b580c11404002c4200014400c0d265034040c0700302200c0c5201a254601440032000c2282e0849a02400400b801540d50b1006869151041c0015100c1c914020a0b0728882d4000e000f1401c81c140d140e40504060540c158007901c61000e12410740c02d840c03140b00715260000c1480030105014100c8d08008200a150190400e8a8105c803801c090308a034001d8407201c030050f11111068410b5030362002d1025555000e080100e451300d0401d0b40040c0401c600801c0b1032030382e0b9030481c2c128448407880c141082e40b0006903c0055030588900802e03c400100200720400201818041c205030943c480d14146140e2540e42c0001500c1e80c101c140c04041e00d50348080f030440c203540c201070750901c039480c82800c5010314a000310000d00c40310740013401924002d40380c0080499050013480300710000d01c580384103c010701c450340214643d030303400a00403680461102500d840c50b61240011807185e5550301c40081d45004058071441080418003c0f03 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 398634901 1250 398633651 398633657
    0x141011280c05030a12120212010e01051f09091d0d05120906190b01020c0d0809210c01031d0d050d270212070b130305060610051801 58
    0x544258000110001480440400c0160028920040c01c201140d0401d581c00b2038400da00c02c19019002865028040c600040070341030000a80b55021aa03401a220300c042c80500040600c0000c1043c030400b10015050300c409842d424250400d410311030b01c03140702c0c9a04c08400700c0d0854000704003812582d04003010104030025440300c4000450245031505210725180c0003c1703200429000000558801d0190380306c0c648400078550b50403c5440140180c0740514104a502e890f00b0f040703036499008020ba00001726000d40301c8100c520310b40c102280c1d980c01c4020603a1185030081e058000000d9525a000c3c20004180c2c090400c85c03c0c4030006500819000e5102c12802e6001c2c00100345402c410720441c0300d100d00503294103640700b203c00c40c03e00498000c1d51030969103c24540d41195a05000213048800c550705488002503075100d0b41145e860241181c1c0708480d54100010000c00314480a0a003c00322803041040b035059440d0001008201e114089050700081c006014204442c900414659481003040c1 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 398636151 1250 398634901 398634913
    0x80f0a020904060b0a0212070f0b04080c250504020408070b1b070602010e06010f1511100e101a06120a0f020304030e0a0e0106200115120b01141011 65
    0x21002c42c0c02d603619a0b21000342d1050104100b01c0c166014010b84059000c04440c0130b14001256441156840310700e0f0700600101000360008040140007401ca0784020318100480d441d100301e403500030100c0d41041403250405440b40da800a000e003003d0095800b51000080601091070500419107059045500c07581e200e03105030a0900c1a56405010003005040340c1c3e4000704119000042040c902081a4007612a00c80030f92401c12100a60b000844030f280b240f0300d8166048110940001d1600b00001c02c28000240b50024801000030b000800041d10070040d403040c0a0508a00043c1c20341d08400400c064101c5000c00c00c18054404500910350b0040354a400003601c3c160354072440049801c21101240800c4e620550f4018603c0c0010400d0001d08415100142640c10510000c08c110b00e1901e500d4030000d50241300c50368202d1300b034000118151600780c445240503566441071300100c01e40401641c840d0a81000460124002c1103040884171000e40301403801d5024034000c41d030004e580441410507002e0b03d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 398637401 1250 398636151 398636167
    0xc010c0206130b03011e030213020912010e1f0b0a0b0d11030f0406151401050c0a12200723030a0b040b09190f060b1306080714030a03080f0a02 63
    0x20941210162015551540e00c2e5030401c80000c1624940114440300100104407c01c0160b944100c4c030104018442c5000d600c03502060082401380901c0000640d0310350800808036041000081c0a0500c0c034a1411103e804000d40030140088940b07900e14250072a00d42d41c0180003544599009200040040d100000c0c01400740382403410325041a00c01e4214040441c05100900050b402145460140c2c408101405440d1100d4040a02012120981882030106114003d43c3e01444161002900b01e400c1c00b0000344081070003020000b0301c1d5180c02c516412007808030800800050001c082d6281440564203899403d0506005299083c0d01194036114150b000e00010781d032901268021441080141024208200030710f003002403201c02c140c03405200107004e40100d2401d04820308000c0e0044000141400c042001c0384465050380c0400900700e05120380004c4804001544400b242c4082d00c1c94202c1c244c04000b0107131541112a0058001083d40c00407858180e00000c1c01c5070004038145c03006181210b0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 398638651 1250 398637401 398637427
    0x10e06010507080a08070908010213030b06030a0503040902070b0f1005040f0b030a060605090105030a0f0b0a021b0303061801032f22060e0903120403020c0406090c0e0405090c010c0206 81
    0x20201ca102c00142601050101b06a080041c050140c95880d0083d4140040341142a0520784d01d840080c1009142802207000ca840c14807120420b030383c000055075070342e98640c039600c000b81d1702c5014200c0788199110001004030481041d054004c0b0704029200c590300c4e140130100301c0900620b503d064030095403004400d0080d40e04002100150b885400301207070962902040001c45401640024005d030000d440150004000c003400e000e10f298011040c448507213607045860000e014507000c0c40301d4045c040300c0d4001f03802c00010296200b484203ca042002034108140321100c0c4c042840028480c1d13600028050842c14a40c0400030036015074451100030402c03280000315030f8607040390341100340083c01000f031074110094050800031f40640e0055000d03a08060f15215603d1085044c049554540040031a003018820300815200f600014814801142c44d2108000202121035101c404915003007003400c1c09041034010507100e600c0e102c000d0040c0c42e604000540c2d00802e021005ca074000b03020418015081c0e9 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 398639901 1250 398638651 398638657
    0xf061401030f12080907121106040b0304061a06030402010f140d150803090d12030b04050c0a02010f0902130b01110105090309090106020a050706030209060c0105070302180a0e010e0601050708 84
    0x402562242c1c20207885003000d4200da440710491004104001c400c0096194000803400119855805074000c03544942c18140c99a503040c1540e940d03c5900000c001070032041c00000355000b40d0040b602008681d41d81e450444c442582c4c400c1d055003140080c40010059809910340d500a0b000d2401e100c2a5100c00321040c91850b8040c142d007024599651820300c1c071013800011450041d01c4410300451521802c0c80002e907e0000d442c000400180c90b14002c01e6019120707400608020201034818061400c00510f22102908251110001503190850b180d48582c40e50060801d00b030340281c501701c0d40e28141007001010300301803c000f50500c0103000c10400c60600910501d0312404080002d16100c0b401101000380d01c8206a1022045500c10800700d03001c1100130400f1001c072100b03800d00503039500c02c5801181c3c96024914610541c0d51a260400c126180c05400400800c40c0e40c0c0fa500c0b032a242002d0811402c00d800c7d02581b804400140014880341c0100050f20b03800c84014100b00d4204200d039511901d81d58 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 398641151 1250 398639901 398639903
    0x90e03070b07031a04060e010308031909050709050903090d08090a080a080a020706080f010902031005060703090306050c0403051203060d12020706120204060806130b04020a0203130f030506040f06140103 89
    0x3c0c0c2d54a00b2004404509544a69032010032102405114540009440800ca060002910501e800404100c15120002003840000703440396050046070141e01300203440c0c2c0100d00c80c144200b0f042500044400e04d02004907006040005d0450744040d900c2d4440c680c080c0c2040d04c0039900010240f4001c10001810030000302280e21170405d560341c0b03079000c4400030b0501ca410f0b0701c000305210824060000e00030041681c0b505458140c2030041e101c1d42c40c4803a13012100803d5201ca5044131000540e1418503601c040100c090724007611080c0541d840302c0000c4c041c644a2440054103581044040b07040f0240040f0040d030b0842401494106403140d1600c039800100c16455840f00076074031098013000125013002c48100c008a068104500b01403805402a0001200810207885403034007034140b4440396501d0f4010201c0742c0004d481107403a00c103000806581c90b402266046031481b150071001582c442000107a201b502e601502424217a25951b64040c1c00d80400d8804840c41c54580327419034042c0140c600e4281c021 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 398642401 1250 398641151 398641157
    0x20310020d0905070b03011d04030c081c0c0e151e030f0a0b0f0f010f141c2f07030e1009030201080f0709060e030109060e01050103050f01060807090e03070b07 70
    0xb04410f03150862415055170320460080e6000c2c0010400242e00c5882943c5080310300010400302e550314981211012018031000308a20300210310183d00c802c10b0741c130301c1c0801450110200308602c030300c42c815501403100e1113910313911500d201040e9250102c21800392040401d9072200c001c0c4150208900082604212009141c5420740c0c000c00091104c03902a100000b20180c0f0441c04c0784100b640810403406200c00c0707050602001000503020144991104010280300c9201c007030316003645000e03096019508458005207a0b0504100300b03c1c0348a11240141c500100346c580c4d281d101e500244000b070351380102a0075803e01c0102e0707290503a19121081502101203881d503841c90780034118070005d0720b000d4018018400340680c1c00100110180c03c45021400c3d0768250404030b052080c034100103400751018020051040d41880f0501c42c0041c0d05400907070603a4812000e44040c0c4281d02200c3c1c0c201d0311103114129269001e804104621416a800005080400c000b564608036854665220148060b1010303000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 398643651 1250 398642401 398642411
    0x2f090403020a17070c1a120703020408010605010203090a090c050d020a080f07111209040e070e04030e030a030e0609061b0a0b0109230901060e090f2b0309020310020d 73
    0xc1200100800411000183c01c907410041c09440354130303100496020ba0316000911010300504510360806a03034140d20011a045020b00d0403100c01000782d000f45c8580c520641c20711030085025800881681e650f074070040c1914280600c0c100306040a003000c40c030f11506110040114082c0403c560000b0b142c051201e0310340e4880e6007030080c00000261402401101000fa09540080d0b5541001c510a0a50018003040d191034001100015000304031300300b42104107201c2c02800140d54880300e0901e600c69802038076401c1144111070181a00c400300d6000c01000a40a014551060714002015000d4000c1c0036005c84d0800b450134040d01102500310034140710a50009c0581010007a007110f00d140074207144501401441031342e4080027615400315101000c0000a000000c024000c01d61004005001d10030000b00700e81400050143c50724800b110403041805900550040c0303111b581c0680c1420180810400d0304941e030007104500408081c00c007244c1c580145003000b026201940007600c0440c00c44940055 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 398644901 1250 398643651 398643653
    0x603040c050303040914010e071d06160c03050d020c01052b020c0f120c0a080d1b080115020118120315140a1d130f0f0b09010c03092f090403020a 64
    0x905d40c016444034100b44140000c0201042d8019021219410680707040001440742c20300046581c01041d01c1924840c005024133828005508095800c40e4091810b6030281401e10804a0b02ca180049090780401c1040152484520360340e101d205513803541e02c000d00401000600a14260f900140084805611606022544c1d14040c0301c1c805000c003581c10041e1400d07960294140d20b96000020140c015000810b010002c030105401055540304110440c0b402c422119002405540007170240d0080344812265045046005100d2003600315041914a000300003a0b41d42c2e4100c2c920038090303240816403940d0301145240049660340700641095905e4010070f06440b8107002d01d4440503030116000c2e0340000070421f4407184c1580540c2d04800350340054004400315040004481c3d40c00c200040c400341098101e50244500300d00c1040c040e00c251002880000070041040b400e440d440700c1c02605d07101c0d420402255100c040c403004540c0300d02c3e544009200d074285900161185034125403c1c1d0141c0c00c0042d000b0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 398646151 1250 398644901 398644931
    0x20a0504090c02070513110c07061112160f030512011710090b0a090507030f03050403020103050105060304050c10200f060c0414040b01170403111c0804020603040c0503030409 77
    0x100c1c0c44403580b0080c5242172500300010001c02c9200350b2544100e0761078024080b0000d40704216180b650052007120512950791800500a80207200d4080580c00354041ca40c0da0343c81070b081100c0c0c5990303a900043c04000025221203c80d00ea07001c01c1201880000c014440381c6c030500b00d41c00c600030460300321292851511010780505080264458507003d51902603c017000800f0424000e800814020303000480d040d842c0f80042c50582c0c00d810252045213000311003810954401d00800949100783ea050220707998400070720000f400191350040441d0400d0402c00c2c01401c04458008641d03c07549004c0c06003a0320104494080800c00c1000002038000c0102008981c00c1041000d4001200302c04041c5007500c1d0803c1008030291008907a44200e0310350101d600365a104081c074112201105051344a01e0410703203400b42c01e2440d090384c00812030041841c842841031202d1604101505140c84905003603480307a003042805d9000600c1150b1a000c0024049010346080001d070019210580001030802c0c3d00034004 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 398647401 1250 398646151 398646161
    0x10e070f3b0a09110711150f03100b0405010512041502040b0405040b24030a09120e0a0608010501051608070b010803030709081f0f1e1a0409020619050d020a050409 72
    0x5514160130300400010f410a40e0046400341da8010030145080640d00b00004c1c40c1d04680b0300e0f000c4a03070001043d0110503442c0c060096000c0c1c007107050000c0300f03156200044002d40c0502d1040502160b003e2041d220f2000c0707a4051141c0c000d10403030108040c1c80312503400c6812608a604283c09180000c10280700e1810680f0440f106048200c07611401d0514040e03414142500c1f0941040c03604002002280050325143c00224030203a20001c1040c11004e0071100070090300319134400510510078180300040341c030301544200e411303642c040e501c561415000c1e80c103652009400305000ca480d1441000820046401e40d1102c5010f0000b28016640e40e0900906c01003015075903400000007508060880041d0030052070543d001c0c60440000403840c0714081600c8001032050380aa004050031102401e00c1010040d4001510320040c800303035540034070904040c041101c448010003500480d04000000284900c04550401c043d15450a03038074060210b584039040c1d03040000b003e80400c1001c6401d01810b00280030b2 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 398648651 1250 398647401 398647409
    0x30b010c02150a0201391407030c120804030f1103041a030106350402061b03030603070801021306180b0a17010503011b0e010212031e010e070f3b0a 65
    0x1441c008400e10f1044e011140d010311b58a020407030100c0755800c414003410034000c030344041180503a10ba0304141005041d041d040302c411262004800c0100c842c0c0e40c001e001e041d000d2a003542d2030200c4013103455002d07110101c000740c00f00e8251000b80800250100c0c100c1c650280d4101f1582a1500ea52424101600d48100000d01603454041c84440c02221354840088c00e640082d070302d24040c8a40c03958004a103451040303e001c8444400d8402c103445400d40c00000039030003400d098080381c51540d0b0721140c8a08034000c1d41e07131500969080450401180c0d00c21007100300d04100503268004d0043d5181c81c40440c1c3c0d030210b05080302040f50400320b003849002c03120109004103408c1e4000d004480740f1040c1c030600300220501d50f00c140240d02d80c600c50241d20070003030780c13102054105665682e81030091810440e00401500250742d80b515800105980360142903160140d50aa161f804c3c5144890009850781c0451030760f10841589100e41e945002c00641c2081c0100240e198079443c11410000d0900c0014001504 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 398649901 1250 398648651 398648681
    0x3041505120a0b010306150804030e01020f0a11010201060b0a0906030b010f0c1407050d05060a0c031503060e0c0d14010c180314010209030d020616170403030b010c02150a0201 77
    0x850141c9660001d090354003400144002882c0e0000000603401024184c211040e01100342e644461040d41009845010f18004c3c1c44484400c0c04010049039201d00d622103890310f60304480401e82c001002c03034400184001c4c0500010842036129007a0400c5a004903e010000681c454401c0101d1900751081548410003843c080c88078811520018118180c1d007003004040740c403001500c0314422410b014020207400c008101c198440c0150400c142d640c10181c90040c001d601d081d40620002c1e009200c0c0c0d9164060582d00d45004902d96141c540040ca51844040064001c0040f086481d640d0b0034880301b2007621a0000c213011315803280e040303402c6400890b028020700c9462210003c1980c42509400704490340b05c503111901c01e401c42d008501a01904110030f40502c10303e85050425500815003501c111410a0901c2030500311110440d1003800b108664951104020701040c0880d109800101e10308006041c145419040c036801b20707454960071a003040c582c0381c0c0400d44d010450b9080c019074410030301c0f0346 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 398651151 1250 398649901 398649907
    0xb1b0304031b030e031002040509090106060926070e09010e0105010b03061c020402070804080d0c1502182e1d01030509120c01020702010806011d04110903070803041505 74
    0x140c0d02800e01c2594148014078541003120b010201441868810442c036000b90a0f280b03000e103400d07180006500140612480744042d130000950070141441080c0072100c2681d00c54540901e00204246405c1850781d0000000c7c00150646001501c2008045d0050804000f000040c0c5040c200b01400c40d100610701e01d00076410600102b000880030360640750409001c580c003038035503051081d000201c4542608020340045c000b00f080010b204a64000d402180d41c2c86040d61201100c0381070440703052001880040124140c3d007000b2400d03820325405011603170a4001c11740c4950385014006585801c8040c810307019080a28080e018020b40700c5240030354424281402040d032040c2104002803092000100c83c10191789400058107200200140c088181141e000c10b40d03205e1070496524080e60081c2800e0b0b0110344ec001c0410795075445105222138810080c220045d03664180d800300005010b1440b19000b09402c1070151303e055036020303c903120013000e090000350360720b0b490700c4c8552419803482c94448003405424 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 398652401 1250 398651151 398651153
    0x70605062d1c021f03090501050c0c160b03041b030609150e07060c0b070e1c060507090b0d1e110d1d070b0d06170109020901050f030309091506070b1b0304 68
    0x24004181c1a10304c1841d440c03034a010300d0b2402c074018900444060010340c00c05042c003000403036202c0142441c118850503150201c14900325030004400a00c2140000030003040000d01103180b8585c550000310003c21000500769481d200e00080c1c84002005492001c83c02d40c0040820101d840ba0400803a40600648a118546180544007600541000d403440d4212800640743c00d200b00c0a046041c08010501107a440c00c000f4208030800441f07204403600341c81c04001c246103d000d005c0c000221032403800b0007072510301e41c01d000001802810070314400b5600700105124000e04540180c000e103140c12001a07132290f400d240c00c0c00903983c240038901e20701c0005500449841d40d01062601c142e0f1030305142d15a4440200c0b05100c000c0400750312080180004000c0c10201d514107400c561040b600031903009035a80d803254100720b0022110481c45501d6807040019140d1420040451a40000112020b00d911085600495190f612420040b1030036005031040002516403000c120703000e660700720390250440c502 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 398653651 1250 398652401 398652409
    0x11d060112020103020903030409050f1006050301260c090a090c05040204030203030712020c190305060f071d040207020904050f0d02030702030304060c0219060e24070605062d1c02 79
    0x841c101a042580014462042e07407400c0048800500c1417000401c07591a108205040c02d10055072103d14584540000041c224410800d0300d059075510141814101c8440b030f802605821641d070884404d0040c0180c500b150740d03070215150300c00c4040940200b19441d062400400c600402d82019119901c140300074405600c0c00030680d40e55aa11108268020705910000c0e0301c0c110400518560025002244a1140030030800080c203c0740704200b10f60036511144d03a2040004421141000040d41002002c907101d007010b81e0215841c540944018941042500410916901142c00b03445a42c4015441c81c082c610812000220b030700300d8070146042a075103034000782d00d0703208500c01c0d90108007080840105641e0341d140414680c0d081034030a10f030155600d560241c1461403c0391081c2c0b00f0400712380342e80c103020034024200d481c01c1c1c007006a00b850300f00e85903101c400a08001e0400d81c1c210000b51002520f4440b1451801090130f01c2e07441e04542034003c40100502c011000e1200586980f50029400060315 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 398654901 1250 398653651 398653679
    0x1090b07050903030d09050a020a1d06191e15050f0f0d060e0a1409070806040b070302160302300901080403020f0d0e09010504050c0307030911060309011d0601 70
    0x11880c503003581d8801000c0d00080c075500411013285c1c1003d14200410007041800101407034202d10a03200e504440740c0d030341005070690b204c01064224012074000040c1007480c0074440d084440c01503e680c1c1280644511840710031022101ca001c0d0b404040a10600c903000400310380c6e801d16940c901d001d92070181c8c107000f0342409004001e128003500402084007040d0104a4108101501c1040c41d045414500084a040641b0500c8a5811401440401f05404a0303010641c04140c5000800600d8151240d541c1c030316540318000d0641d010140c0c240700f9900042c10308022095404c1c02640105201310b800e9422030304003920b0110302a0048401010940b541401c58196582001c090038074008582e91420260704001c8000c181c48002e01401003080d11090b0800b280184d03802c801d481d2aa4103030307250b41c1032100b10381c02600c000c480c2e690140300040280d4466080703101c00c40d100e41c0303141d10b0105c04003020a50f9508150703031949042e51a41c1240200364900781034a001800300a0042030154503003c0c401704400 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 398656151 1250 398654901 398654911
    0x90f09020310171903030506181506220f081005160f09030c1502060a090b040f0503090a060801140117070e04150801061517060603070c1a1005010201090b 68
    0x60051901003c80c1d440500180d00034540d043c1c03905481440c1440c00800500c0c048070210b2065080084242c0c6d402c101d0f400780d0748540c403d45c3d0010400f100c01f10400055410541054124104041c0d0100b04141805401c000510003041c0d410021418980018184400560144d104510300001c010044001d040005040746441c2028030390500500c008680b15034007500041c140140310b0400141015051404224001e032a46c02e8840a88804c01002d0070303a4066400507102c82c00090208011842149100c45407500c143c0803203282c6043d0201241946000364031800c08241100010040c1702031040000b00708400c2480c002c04444641c0c041c100360b440c4050402d000700000344200c02c09644817680511080707041441c01c0080e0540c0e8400241c0a0032141c000c0841500c500d1040c0c45501d801500c01c04506099510303502082c2da140002d202c610780009049608105465000c000452200100c131045100790606101c0c0c9881d00803025400402da5134002411685410007103c00b098400c0c000a4200c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 398657401 1250 398656151 398656169
    0x70f0e06030c090a0b09040b01080105150f0d0f0911060c0604060b120f0303090d0504080a02010813080a030b10050a17061f211b0804060219090f09020310 68
    0xa40714044180e09a008007443c043e0070281081d4049802c0c20864060540140c00315030a100340c0c0120001106c1c050303001e02c206500840070440c840380c406101c601800d018041d0898140c01c0c0110024003005590109444440966540d6400d009100703010440c440508419501030740707000010b6250a070f55200007803002d4103855551070a5074140e40c40308848069010f030402140c14060784580300c02c0c3c0b40e503c251280c1c095031240040341071200380604195000c0724840c00103428074032465001074403500e2008041c54042c000c00d2140030009406503024013100d411640d000509641c02109100f6203022441001041c0b2006010340402580d114052410b030340907000442c00c080d180c0c40b01040d03401214188825071a00e0842031042e0095011400c5019110b0080000c60802c1c03035140701c0400c540c4c10f102403a006542481c10740e50b040c0c3c0142082608540b082000518018820b1504002441400e1142000641050081100344111907945019120a00046165052240752220800c40c14481c4401c4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 398658651 1250 398657401 398657407
    0x206031504180501140609040201090608040203010b12030903010c0816030b03030903030703080a11070b2410050702040518072c0a24052206090c08070206070f0e06 72
    0x15584070740e000202103024101000c481100c90380342041c003030f00281a103603c200c00740c200040d0b064a41103a00c0e500135170b0107840e8114582d061150440d0709820040042c1d0b010364071042c0001054031998000000160404d02454998410300101825540312040c1081003220002c1800761180030100c94802c0000315013800501a9101c20100341035005401800e6414000851745100f45908441214480c0c00c0000d010040d410541d03c903500f45028982025050b03407101d10000f001c4d1000c150718942801c07030602250403070380c0300740000507402c0b504101c0301d400044003c6201c600b181000d00403d034000381001c2c00040da02c1c5041148507030700e00c0381d48521811207c1008900103001240d0703502c0c0030100c2803402d03001c00902c0c0c50034044014001070008080204204c0001c1c203920346034940403a0540d2802001158410010160051141d0304030720440c3c0000d668a9000036000454822440d001c6082d480b0442d4034941190003a0401c00020511401d0001076030491068a901111540765102c0c21526561 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 398659901 1250 398658651 398658691
    0xc1e080c09031504030305040b0705030403020a0b070e1201020409061d0a021b100b091311010818070f030606080304030809010503100e0405150a0b0105030109090813060509030712020603 82
    0x2103040c1e010349090040c3c00007201444103242d0f05401c0b5038440c3d4001c036901ca440c1c0d29000c408848501c0b0407140940180c0008480c100000c14078200503800c0502c0703103044110000d42c40001203842012041038a40d40c0c0d070004040040013200d00901c00200b40d04840d0f4076014a4124001c040b480c0c00400f44810b0503400a18001020004600310400007443c0040fa0301d401c074210350b0701c0020101920100d225049840018120420a100c0301a10f02c0d4000c54091260b507074900107484141001e803a1840103164054101000c0004001500042c45800c480120071480c508142c002c485443d008180c3c207400030031007400820203110071682e0518080ca0415501e603200c0004071496103050b000800c900c0f15282c00d00c070074040001140d89481520054902c00d6444d40703c640c1003111092a80d65020070401e20040241640326405400c81c01d01a18403c0d01d05408a03040240c001003d821580c00300d07101140080c41400c082103504060182e80e2000c01441102e600050032038003005001d100c2e0041c010400e00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 398661151 1250 398659901 398659903
    0x150f040f030c03030206060609010f03091115030a0b0d030504140402120c071b060906080a0e010e0303090d0e0a030f1730010b07080c010204180c1e080c0903 69
    0x800401010152110050722490046140c0380544402c1c0d0061140e0f0300450402c0c174144007100e0344580c0585a000302000310082c1075002d81080c01058030391103a80c4100e00c9451311a00340500d520700000d04001d070380b403901441001c100d4400b12005401286c4148042001a811100f207406a0f204414103050400c3c001c0300080c083e05c0340507040144084c2480621204803a403002a181d410301c2084071500e80038036403851240da007441e440382a0001e001d070703c010004030703018503002900203408100108407010414903547c203580d1300d405403440c10741c400010455041e40911040c0c11103800d03803500c554004120b40018004100c0380c00040d0511480c1000002085103480c46903003400c40c1381070703020b4485080d240c665000201030003107035050683c01c00c10704200d119a48207181c180d60350a2071160800002c0c2e00c1d001c405400884e0414507640d82040046518612081c05d600c45e0075503d140401c4000188034020b003120304400d20b03428424141110340d20b64681083d01c01d50b00c070308000781c02500d40c1c2d03800c000a = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 398662401 1250 398661151 398661157
    0x1119170d02031b0a1205040509070c02030c01030b0d0b01030f0b0106080903030610113003040c06030903051209060610030c0c020f0102100204170601051002330703091205040302150f 80
    0x60281d5001007038170a0356a004009841283d404841c2c3e0300345a5501e500a81303040304030a400940c15004005003002a6000f548150700c4d103040a0304d01d0f10841d01d20341e205104000300fa0016903107030b54212200020000009049405440350f441c16010508040008075680e002c058031517445040042000e01070300d44545486040e100d07841007101d145800c188203916010800241d801c50f903007504004800c810f031030041120b000341e0780322400c082064603052045000b846920230031810020b042000320400c40c90038480b54010008540a8030b860b00300701080220300c0c42d8804a0300c0a01d820144400886500004500e40060301500c0b5220501c000900403400e000c0780c210140e02c40c5101080c00318400d103c1e141c02c9d003032840c2442c049600990300d440c10070007810554042c010040e80221207011007004c4000306058405140380b030603418803110304031454581104442d5100029501e12901d02880030f1440004048c07901800c110381340a0454000c0b5011003c0d0000b20502903000040040c4440003030411 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 398663651 1250 398662401 398662403
    0x10507140a23180102071a070f02011107060e01020114060f151306030905010608150c070501020f030c07020f1504050402070c051507060c1d0d1119170d02031b0a 71
    0xfa074483c0c8000c1500710115070320200c5030040c414501d0114003001c3c0301002c4d0060401da2002582040c241c0e81c1c61034140c590b480d00490410041c0b03d20040c281e1400c00c07144014080715101c044c00e050400000900b1203559030070a01c024500501403003072580740c01c1c26802c2101400d0398074140584d007103100e541852240300e19111802c8020f00c0001900c55069015004c0148110002d1005032f40e5a4241e0756950701c1c03007030255480f461200201e03a83d101690001c00501c1d10031400581031082640170314600d03400031030f080608014001880411450000c12480c0c0f16041110b02058035118001c5040c8a40190301803240603560004e081d0041c04400015035008100043c8510340340b100d04110102c5075041510101c50044c00c01658064860003240450242c001020040605501c00030810000391000d0906a902e612890100f207103645404541244000c1441413001c219858489810b8640100403400426034000d1412071300c449074040200e17030156202110400024000c11070480c241603c1c454 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 398664901 1250 398663651 398663717
    0x602090d05160317040602070618030203060f011805011a07030e030115051806030a02010c142d0109050307021009171b0405040c0504050a0f0f0b03010507140a 70
    0x1194082c0c01103a05501c03400d49101d5064400300a109020714680c40c01140034050258000400c14000c6907c40d003520900b81c078030b0011180b01360b6506d40129052220640301072401d11008001070028107079807400042e0703141c101001001070b503140c070503c8003c065100b0541201894006040c0080c58408c520b60011000028000c002504240103040c0702d0104910400340a200d0080148440340b1080c0c3c16240f0581000d4050540e07809198011141c804c9011001c49000400b0840300b51002c004000824142c02c0c031165160103114030440701a000d80442d584910181c0c100051070000400c0401520b00f4240c0c10f03129424510802c6000f65180c40c0d5640044108280c140340c0440c24810000d1316410145000020701486040d00080c071054960456002e00940040e48003000f581c1026400561b006405c1d00c0000307140c118140e030701c0d02aa2414500201003136100c0d50419850301c0c081c89244d030003090034108080019007003170000165008481000060080020348a4000340502c002e46170355000d448 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 398666151 1250 398664901 398664913
    0xb01061d130204051801032406030b070c060e19020402090d080a081509010602030a0f050d150302090a150e190905030c150c04180b03070312120203130602090d05 71
    0x40020741c029000b44c440c1c20f104440c04140020303c1030311800241d068a03000014000e281d0fa80e10383c0008100c4200030014590303035a6150004c0030a400080e201d0082106a5803010300b1031090a118090711300d440c0b000c0045400c81040e849111003805480140240c2c10785025846000c0240020403212001d003000d000040005113100d151503025070154810000b246500780c21550340810300603a003109020364030260344200b2280203000e0040b000541c0423502c914195180200741082c10080c0c03140108220300c59800c0f20414421407a00034290b50740883745030410005180700e1100009034201610031107030500000808900c0c40d0b2501c4071146040316000c9024030900c44140f4050380e4960040c01008034500540c241e200c420654071711418090100c0003103081c11309090004100003246842c0e00451071a60340c245248440e203050280c68000c5010f054550000114000c01900c0d104200081c244402c0c81041088854000d00481e4030009810510040c0c8445060001c503c0d2200007007400380c00c500ca13003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 398667401 1250 398666151 398666179
    0x90a030302161e0e0a06050a060f1106070804030f0201140c04030b0a0e0309101e0302030702070e040c1a4311010c08040902040603270b01061d 63
    0x80348850301010140810740c0c995581c3c0d020b02ea404064031543d43c199000c1c10208100105110b0854000150103c0060142d94880009898541c2a884040420746207842c0c2000250070160000b00d803558031026100a180c5050010800d280050006040c4589481c0b0784503604e20035405424804240c80446242d403d02c0d140030103c5403c144811210400c4c02d1001400403a41c1d40100760000c03140700c0007142411140c00400c042130a0300c606040c00c000000003040e0034420415880101c0c151203890043c0c0c1c0342046440241018407a42242c44101058014000080c10320604942110042c002100940c5003c00001903544664524090b40e000c8a11303804c0d0004501c102c0c9000c44980250071008180b0f00022405240e0844c0302011700040600b0004240ca54054041113207010701c0f84500b03920b86501c5000500c101e8000390000300000b81e560381c03400d08403060780d004492062590410f1202d190315070340c0c5565403204140070302410095101204888100405c04450080c00c00a101c801c000d024 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 398668651 1250 398667401 398667403
    0x507051020031b210306121912080c0412060f0203160201060501020703020906060901050f0d05150f030a0312020408010f050a0c0806090f0c070b070c0213111608090a030302 76
    0x494215507003070f1100c00c40c5100c201c0001c00520780c0c140c045400321038071010541d841c202d400041c1351607044102c0c4c1d007510300b00d0340c41402400700140550700c80000301d07040da042400303450101f01d00d044244000c10f07062207004445a82a24120750300d9060641c20702c0c206e032a040018041d1000c1c07800c007030f600100500075003081070003404003485000d41c001c011042ea034000480c0d850542e44000394015103007070041405428108020106580306040c850715210086040030800d134801c0001001040c2d0314000d200c00701041244649440348121480c0c001141c103034000a0b250041000c008080c042841c00b020741e80c610640655000b007000000030012100c0c88510f1b60050301d07045a4001c10340e4a84081070b00001e01490b1428003d0102401a0140d0b0350b03500c0001805004c080c10440400000b0300440000400341e00e1154896038541d81e0341c044070f8000e841448030402a0040b08a40380303040042144030b0700300e00d00c16558400d1450445001c60b080300d0078110803034421031f280303641c008082c80d202009240d0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 398669901 1250 398668651 398668657
    0x204030c0b0307080a051b090a030506180115060e0f1f0207030308010504020a090614301302060910050c100b19051005030402060c01090308090d0804050705102003 72
    0x100c2e84c60314034040d43c030310400034100c94084850315240780203060b054494408981c09400544030241c10b5011058603500d6442c45d004044030b444508200165000c00000402c0c02003204692035900341103141400c054000c9c3c81d4000c00041c040c040c480812481c3d00e41c4d0b44180c40e0140d5209615584000343e15850802510780070780340410343c0030868010000509040c42d200f252a603c2c0e041d912002800c0c1071420403100e80c04c3c0054280382c041820304c111040d45040846048030a030340d06103041c901c40320b60445050341040041854100c0080c2002000c0543c481104455802030111a42c00584015107815200c0340140e002c2161140b05003009200404902d0740318885410044030491105004c0c00741000c400b04a038000e45030052a48403403a29001e02030b00c044c5d1b411910003071055041840c645880da084807079410003038000030700000910810910074010301d95589104d14200250b45015100c0a43e100314500c9000d00810f03d0032054856180308803452407904a1041d11020a03000a43c9034a07501c1d0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 398671151 1250 398669901 398669911
    0x2060603010e070b0702060a090e1303030b27070302070f060c080c03040309140621070e0d020612040212030705010e0d05030f0622090c030b0f010b030f0702010204030c0b03 76
    0x5880c04115001c2c0120000d0604210741a503204185032416690a02c100c07504000320900501c0800013009c02c001c002d080b1011710130103078646800d581d55044c2c01d00034265800c0c43d10182c014800c5030700d070a01459441c0501034a198244150700c030305444242040b0020700c01d501c4c0181804041310010010046ca83c1c2161444c01680d5403004c00540380d40c0c07010b1105100548001b0040f0383c015004120b440c68001c01030120090080c003031802c0c00700107c81c051415003c001c400c03816042280412200d0364120705180d0002c40142c41c03070115042c00d503000c15080d1044c0620840520b1040c4005002c56a03044140d2691a910001382e94640709a441d1190103050380740c02e50600d03030090481717071400c0c039101e01d05903440346c0350340c2c20004569126403007032019110520b1308009a409440c128110319100314000c400089200d9407403c5000b030720b142400139401c40051300d04d42c0a08504401001042000d4040d40c2e0440080301c40b282c0280c851080683c0244100d90005101501d604000105500c40c0c0c40998464 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 398672401 1250 398671151 398671153
    0xb01021906060e0f0c1c06030f2603150603041e0c081506092409150a0b04080303040b070e15030105130c0906050703021015170a020102060106032a02060603 69
    0x2d8582d13240c444c940700300407900d00e008030307405000114a807400c50801c400308503040c80000490030b4503070b22461041046c0c00015220241d42e49252102c0780ca140f044004407080c8100c005003141050707003216002e0641c19225620406020000c00d06201c40072840c00003401c008150311000010525210549940074814000c89020740305010b1101040503540710b200720701c005c260031125034035440130807004880c000070b02c520f00c600000185c0c01d503240c48140c2030145000031807160540ca0841d040003900905034010a090700b030f041c031041148000c0001603a402c158400124021980c1c0c000d0700705d4002080306c400561000c010742503d50701c0c0000348000d40c1a214103546c0c682502c8000d4440d81c0603146040441d50008059050800640741700c1c00191180c039104c0e00c151041800900303604015206580f105c9092000550320400521a02c03086480541c5203100140c50b01100980020313466010500c07a008c00d01d5115902115421400520304185070b103004d621008c1c40440e000d0007540c2c2c3c44115001030007 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 398673651 1250 398672401 398672429
    0x317011d10030209040605090a17031602030c06160507060c0e0f010c111509040516020613050729070309140f2d03060c09041a01080601030b0102190606 67
    0x18488941c03031040c00e80760054903085841e191566080000c2200421003440c901070005d60000055201044101c5c1c62071601c0c00035140e04151510030f4155448543c5001958002c201e8141c0307400e030200e1340c194490414070b0030b000c4000d0440c030195100e1040f000000c004034a130660304000c103904800150103048065031a40d0b0340e15200001521402145000602410b40350041035890b450032800c11800002ea8010320f40c1005e6803200400d0a82d0300c159808000105c2c0400e03002400c0d50304021159000c2043c01f501c011115094840644603d83c602507100c00d0610003003910586081aa100780320a034500d540d1954610440c1001844001c0c140110000e69807131000a82c03562812199210004030000e081c441e4907020f009000340450380803840c0f0105003010106802140da01440340318800c9080c151502c2d512851a8100000c645c00440300715162000848081c03a640d910141c400c2c0e00c480b003802e0000d10480d080005030b00e40b04400a0503603080a41ca481c1000f0030600e0740240003103843e10501444 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 398674901 1250 398673651 398673661
    0x12070f1a0f060103021c0f0f0f1b1b0308060102030f0307030c0f0e03072105030a0c03020f03390706030906141618150305070215220317011d 62
    0x1007a8030036500d045c4100c3d525001b62514408240d8418062043ca603071000410790b44140742d00301270b140320382049101c1076610111100031104a601c083c600717005920b131550801e0314150006040300714000b8023400304505035002503180e034001c00417030343c0310070a00998a44078903000e40000c0180080982e41c1e00002c8070860901e0390a400742b01c0d4200c413201d005002d00300040c03c040c0d0f041d8044101302e40402040c0c1d82c03e00441d0204600748000c00880c142581c6e0000c18862a08001c0c1c5010702d000480140d5500402108500701107100c03c0707800e0070064016071030090405010440d2148954681000c050144d9400054a140c05510100981384a031406210302c00050480310803d09003213400b40703607001115507021000c42c81081000700e016819540b0b11071440d2a81111520340c1401860038020030381d16401d03c80b02e42e40402403102225850810600540b0701004d91000040d241800080c0c5900c01d4a8010101409900142e402d5450207007003050359a955081000300d0445041e03814031118411011070 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 398676151 1250 398674901 398674907
    0x2012161b030b010b0a0e060408031201060801031a060d0b0a0e0c030f2d150a060e0601021002131d01030308180a020607080c010f0b09090d0212070f1a0f0601 69
    0x203044940040508681e40e18080e0b20103100e520004082040209003d401400303551424058005055458020740d01e038885e2400106640c14180c00c0301c010b200c4c4000041000400c2d20482820044000c01c074418540c5400700490030034084a00020038449081040110300c00466100480d540040d00031190708020704000e141c0c83d40381c17424040740290003c002c0c04e03240205040340c010780c0301d050321840101503c1da20002c1c2d0912a86454070840b008442d024403a1548182c000c1c0d07000703000c030038402c200181070120003c4d541b1840172604105403500400c0d00341038107400c424803170010040714003103450340340444c10140d030041801d0001b21701043d07044003c14075813204084094004501030f402040785441c541c081042c00d03040b17044212490b075002c101c5848900001e0250006808c401880491510201010032041081c02002c10040760b200480c42801c1660000b118510500541103e41e56134a05042c403840d40e140248016200d1001c0f0346201c01c1107040049294401c13840040d40400319290f0f40011 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 398677401 1250 398676151 398676203
    0x50a0605010b130e0c1903140a0c0f1416050105010815130f050a0c080f010e030309120310030204020c0f0c10210e0d0e030c0d03201216 60
    0x103501ca01c04034141400b03c19081d13140103030440700c240071860a08042c50000030952985404a8000949410800c0007504411078800d07084003c2c04000d0101d220341d803600504002c4034036035403010442c003c15100c10140c1c0c5001202c0701b108581e100e41560f0555401c0c074502921080c8600b480380c1c4900e03020490341c101e10310380c024041e000310f087d44000300f20243c46810480b0504401134405020f80080d03031000550641081000301810300c05040100d021209040c2190b03003c000740000f81e00104100041b022022484040c80303a0b40c0c568158407500c42580d010881200c039000250014800584800f603008005070030b0b00309000001c100d80b90002c84805000400f21950a040045480c1c010341e400314000d0088101c03070000d0b120000040c22034828841070326108113401c0c1d480100d00c50500d49025424148014001e80d20145c5106a0900c01660020031287c5d41d11010302d89101021120030b0009000d1020a101400c52104c00e07880321080c031821119401e0b4410110341c0d4442c4a05010319031030300030180d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 398678651 1250 398677401 398677417
    0xa0b07080a090204180c140a06050a02010e03030a05040b09010c02060714090d230c030a06090204090516061d13020c03070c1e08011b08060a050621090601270b0d050a0605010b 77
    0x7807458230320700c1e10509a80300d4101c0420b005c1595200d0b071401e4003018007080a548140322126000c070300c42c02e050818032003120002c3c1414006034107080e01201c2c802d4000681540002403840c1001100103940322011140c01b032405243c0d80110003071100c1c000d1100100507640418081c42000b201d03941100c1895a0b034181ca10a050b405070000b041d04004191f403503102c01e6260b03002410108521042d0f90715681088440001d1200c3d1006008040c415940d1008485010350301500c0300b2244880341000042c4620000d001e081516a00018280502c11303062007925040c0d580400c0090703410740c9400726240ca503c2c3c148603425024940d0313a0000781180d01400f4004030004050251286110011021030300940c00400e500d0b0000143d450000340c5071100c400070809890803010020030682c1c04403a05a0aa00103001a1b080f540684018010f40113000300840f02c00b40042e40a903c52416450080d028003841e180c2550701c0380400c1e14071420310030f020895201c030f18401d00c030800c03160381c0701d11100c6828040c60030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 398679901 1250 398678651 398678659
    0xc030d020f0d050703111501080c18010b0705120a0801061407030c030e19060215160512070306090f0209031204180e120c07080f0a0b07080a090204180c14 68
    0xc102c001140c020340051401c40e000b46800c42000d820001c07210300d49440ba800810043d1541d20040050240a11010b00ba0040c2161801c1c840000021040ca01d500180105c1071424000241070040010401265414100c16603820361903100d00503016100d424241b14000c086800c0b09160746035005440d00b2249030942c1922541080786c02c42c0c03011200300040e02c00580e00301d01c40d40707c0d0789090049102000000d04056000341118000e4599484038804041c1011228002c03403980c24003201e4010007030701c50304031f0410131054050343c030008110003500c0b07154856180c0d83d18208000806c200c441c1c004100044055007100c0000002c810440328503c958460b066404a640c5924540c004050300320841d01c40390b00080703488016001540c010503070310610000d000c690024504202283c000d1240c4a071150610024010801054076220360400e40104800c0400c4140310005220328020b40c030040c2c00d1034000d031040000c0c002c0036035002e5030061904020760b42007000d003a00007403500c80c030f03100380b11041400f078 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 398681151 1250 398679901 398679913
    0x110a0f060302130806100302011d030a150f050f07180b18060c10020316030c14070f17030106120b0f060f0409020f04150203121609080f0c030d020f 65
    0xa00100c009400c4124030078120f604042d0005103107103080159078001d000c02c0c85c100440c0c0340740d8400035001c6810410079081e02d0310345c540140b00b60789d0086026141e10340c002840b80d6031a4400010a00244241d50900003150300d41405d0004210400034a07034403e400c80d40716076010064101c4070521400d2140316102821070104045242c40c13418548407612180040c210600b00901100810706291010180c820581e602204004215210307641c0b80c651084141410041c222503098000c3c01c0f90803070490b1411200300041c2c04800c0007004200060b100350003c80119107403207031581c01c1b24654400e01c00c450000e022407a0203401100c0070300c82d605500c180142606d0300704401c0c0342032109540080d200c0e01500740b8280000030301c1c1c040b1400200141d080c101c00c1140d84904007034859004294070325040f0119030050003d040c0900f603240c200743d00403803c00103184030900300410031140c5440b04e4008280501640d05521b00404c400121115809402c9064404050014030f00b240c0d900750003040e05425600c21 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 398682401 1250 398681151 398681159
    0xc140409201908030a031401030803061e180a0509070501020309090c090d030e040f111204051c05090301060509070f080907031217060436120c110a0f 66
    0x74108007803890a000c1d0982e440114008074600000c1d034560300129940d08002020500103a00d03109103d0341d600c141030102000d5045464406041c0001407c0b90300454165200d2101f00d41d610f04c3d14428801c00070610030510240c0c04d20710009550685103042240d003088049a802c0742c0205140d0b00742e50040c0e0046007007a40303900400c01818809401035590440401c034046a80e1074105c94010090300a8981741030540c50402800102d58180d4000006a45454845084118000202e0b10246533240f03080c592505c032801c006d07080002c00107490001c0116081c600c170300c454104c4041c141e0104110003c000481c1d0311810300c00300c03940841d410800100324030600344501340182e4409821814900498151036200e959103600ca414990950000c5000030190125107144440b4944c2e002c1c0d003d96040c0641880c810320f00303443c1305e407440c0001c4032040d9544a81c200c055100c41100c1174181c1140103100844003d140250a000758488142c034032a9114030850801d003040c11640c41182c000c40410000b032454 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 398683651 1250 398682401 398682443
    0x2c01090c14090321070c03030917011406011808070603060e010b180d24020c01050a0603031d0d02060301171902030705100c0b18210a030c0504030804030c140409 71
    0x4081c000511440c0901400000c00c44861b0080080c5101e0f84030150b100d07013083c650810880312011103051070ba04001c0000000c0e00c10541a60b0002d0080c240084441e415408400117401c1540140c0380c24400c2034030008015600d80c00c04400c07a12555450286030741c0f41c20b10f00a036841408840c0c0202140e5824030020717810720294025281e070083c02c1c8211111407080840b0143e0101c000304606075900426411642d840a205554111551404c1084080d2444e0340c0586110482c000c1607407603c440704162040f54491f50351103034205a0040c00203030b0b07035a1595940c031110089029800840d104407035028514008000d0410031449e0024001c7c00c1244c541810000003d0b81900c1e00c40821078481c018100042d81c408100d40602c2600d4038020440080c0107440e0328080a004125072804000f80320712042c907400c7e40488100401619001c0341d14442d448054950f40b0030390b40700030241d00c00040c0000620080b03e41c0c000540e100300c0f4101d4540e40002c41008103840704102c01030102c01c4e0b001ca007423a00c409 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 398684901 1250 398683651 398683693
    0x70510080f0601050708070c0b120112020109051201020d050a0f0b01020303130605070e030312010302040b0d15050727080d170a0515040c091502030c072c01090c140903 74
    0x48034106d400d24000e41d642c0c2d0004802032903402985003c90105946d94104005c1080d58050300c152864802c0d030f006203070002418040c40740300f0240aa4050350807030450150070b4046503055182e03ca400e100e41d04100780400c00030244d090b00401076514040407503045620110803603000394050a5500d00942543e01c9807802004050720060500480a160030750544041c000f428030b01c8001c901d5031050750b240d030041c00280c50224101e41e00c501d4a0384411000a81c17503010403031080e50755010000e081c0da1215000d0304c00380082c2d0144012211000f0190b4201c108100080c4c040c0c0b00200203403507206154082c240c556005441d001d07400d043c00303a00064032030800d6a000e99404200ca002030404a1149804a000c66001c407000c900003410300c0e03a0612030a00d00200030840600188000c500d003a1100032943e4607012035000c0d072a400e000d02010000751002c40040070318206580302c0c124119507582c04224004254001d0400080b60003c10091402d92044042e210f1110019002e0215104a2804242585 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 398686151 1250 398684901 398684903
    0x2120609030d0c0e0a031a0702010e0a08031506031018020f0f09040b0a08010204063c0c080a03020c010c0309050d140408010207050a05060a06080a110d050f070510080f06010507 78
    0x800007544c3c015550f621802c01c00002e50040c20031201a40100c800101c01140040c120b20541e81080380310050b9100008550380c60303d4010038503603100c2e2907400340030380002c80d48480c942d4411400b000384000500c020103580300b11100205860703180740e50421844e040e8021206040f4000100740001c035010300102c0c00030045600014400a0700710034140c006504245250488626690f0228040c444290400040c40c15450140000d50543c4e001c0c80039241961890400300040790ba986528010440c00307807048000c12070b44001125100c0e103600300020300940000020340c8907036080012018969009119100c601034000014052141035880150b0344903400c01e8038040b0350f0600300b0000034501800e101802207184500c2c06003e6444a5040440c90000081e000e0003c20389405400c20203020009070580e045648039aa00034613804010004115021004000c1e106003e855151000380e000800d885c02590021514489058000481241c0c110001c50b00020f2449000001c40c110350300803000b03803940d2 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 398687401 1250 398686151 398686157
    0x307090e150f0c0f0d0501090b01110114150a0e09010b09070f020d03020a050403050a0f062901081e04030e12030f1209070b0a0c151e0b0f040c050702120609030d0c 72
    0x10340d408441740b00b00d841c240d012120560351440964803d682c03000c1280022114a0002e10544c2c83c0480d80100042e17000e030540405119208451007103403284442400100038100c0a9201450003400940c045c0c40f5080d1141d05c100c550200150346203018100600304d10000d5401401600c01002d0103400a502c420080303024000f06200001c00240c041083e00c20051161003a86002c0c1c8140c94850140c8000703101c941c40c400d154000c01e6000c040c44010850710300703c003440d294200c6d4840c01d022508451799400d490141002c104100310074140c00a882010810080e2950030f22818800101606e0740900c6089010030b00c0d040144551102201c0303403503500112644284c895195654021407030300d6106404180c0803e440c130718450705002e00b0210409644803544014080c00081c0d079049100d5211100f40074070740c1d075580e103050f0f482c5464080c03011540d5003010f0810045441c9c00f00010304250003600c4100c0c421040c510307441c0500c40000c6002801140c8101c019400c1040c1d450744500076001c054440810 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 398688651 1250 398687401 398687407
    0x3060c092103020c06040603151715040309030b150f0105030c070b0c120f0702011104050d0807060b04061d090102040501140307021f020408010b101b020307050307090e150f0c0f 78
    0x140d0f43c5d491000b00010b10752600c00142510300540440d005142d2503002d1900c07410b000c01c521620b0b00c00899410050000101c007500e00342d5a52600b90f0380c500060300003405a110440800c1925078600c03400001142003100d41c103003039a04035001101c091200702e52080d00f000c07041c468100059120140c4e55040514a075800342410f8148a50164445080300c002c4000103410080c0000c1c160288564040318a07251000c61415041c180850380d01181201d00401d0000c0000328401846070a52060840714801001400703919541d0301103035906060240d407600012211000b04805901c14404c03107080b034406848841d4040317903601c0c3c42d5860350001030840003940a0242e4880c02c942ca0100440d01510701c002c00180c4503420710304100d003185c0c0c1d001c0c035180c014144d0070f0318201c10301c1d0809402c0208013822029074607480b41900c042400d1007015800207415124909021a6042032070700034481005001341141e039a80300d6002c021a81490556151035000c0704900400d5840703c05800800c0700e0705520030340c81c0c6 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 398689901 1250 398688651 398688673
    0xa0908091302071704060f0503010506040e0a42030b0402091e010e1b03090c0f01030b03070b18030d0906030506040204031406090d090810091403030a0603060c09210302 74
    0x4140d4600913031452207100000c2c14040030390040741448003109145007071411507040c01c010a40c1c0e4481e074000c1d040309800c0e0100142d00d52160382c00291036807003410a0840d00701c1040d645c1d0070400741c030310b00d40308050407410019044180076100301c002100c0d0400795a101a484540902c8060400940b000700d030101007807400c00402000105450080c6030910071070700e5501e0111120003e011181c40d2131001e48404006011788a080000c05621519080320405420000c4d81c0c01a0018000c800da80da03054094003100113050b510500241c64450441c5511000c810b091404040e00c460f0340c103070480c01094038402c06120680c0310394807455011401820040c034182d02d94172850102c1400f200745901980c484820007010110603c00c0c20744070162410f1924160741001d031038985500e0a4044010080d43d00c040e0802405041100d041c0032800c00300603a0b42e24103000390590003404507404166551810001d145400c54403480449040341c017050b00740b00680c4002c000d5160203160028042d0210300ca0020400 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 398691151 1250 398689901 398689913
    0xb040b090a1505070512091c050f070308370c020106030201020d0f090e04210905010912050a121e0806060f03060409060608010e0f0a051c110102040605120a090809130207 75
    0xa0043d00340307c000300441030381302e0a0301c0785c5141241c0001041001c1401014150803051051b201c00d1980f5040040d40b40d0358160f0300281d4118035004409085022140c41504401010300051114000c900f01b413107580c2c58500281c0c02d031856031000a00603401072290400040c407441021940a456281804001e03603100d506001410060b981610000265003400d01c4450403012102c813041e40c5800c041c030019290900203000074a0300c0c8100301d90007100c80c513403000300442171244485607507100c0e0b00d00020804005c001001034030241003110200c0b0304040b08036051070240307800c40d204101c010003c61414040241172101c0c0d41010b440c0c40d4100f5181e400b44000550a40a42405051148000070714036840d40a09480c16450303009074260390b0401c44005c000314602107804003400ca54070b884040c1d40c40480d2801c9402c0c480c14103500241c5e500c0860003113071050b440801000014001582c0071801e80b9144000030031125041401400ea03602006008001d05040c1500484240d041900506000068640c4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 398692401 1250 398691151 398691187
    0x106030501021809060f0a1217040617090a0c0504090201020f1c030b120c1215010308030f010605030f04060b0d06061404200306061b0a0b040b090a15050705 69
    0x20440c0600c20300c5031a191800c0019020341c1c031172070480c1d2103202c01e0b04030340c04588262418014100780051a014040902c0750740c4200c3d9160724405c0e40101c2d555560f401e4020720044501481c00c030744441d808017080700204001810341c4411b4010103684900d520b0081003000a080c034130412070642c0140d0313510b00081842480100c2001d2040c1c91660200b409207480201110001c0140a02ca07812490b4000302c000e10001e400e41000ea010750300f0a0352003840c004032130700d020703100543e04019104080001c41000085800740d8000e2900602840403662509029601400708a403081481c41c44c0d94001008100990401070040c02d010309045151101034660b201500e4054114120002d44a104001d0741d040c07501c245050301d900c072150070069945e80400400540703c0982910f20072100455801240d03a4100b150b6401078542604450701c41000b494060708800c402c94094418520120001d4916035005ca0183d055560081200403482c070800a80030003054050100c5c01000750a00030240842c48075525 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 398693651 1250 398692401 398692417
    0x8040c180c020f1902090606041a09040f050f1f0b040608090d02060c0d0203060a23010e0109050604090e0c030607180609180b030f01110901030b03030f1b010603050102 74
    0x81420308845002910344003800f040c8050642c80641040107013a12030320b5044c20b5a604480c03070441900d40600150007406107170800c0f141c011036251014051080000101850002a1024003d5181901801e0200c61080312508202c0c2d0843c000078481442e503020822600c000340c82c024800039190301c0d00340c0d0036401030340006002c2280b180500c0316504040000913405150313032005140c24078100a14007010300407800300c4181c8540200102c1c043c1d0b80c03218285d10140c418252041e100c400c04148076185202ca419003e4045074140210344025403103840a801550006001141340500c1c0c0009140107061425580c1501d0082d10225612a6002e00056014814540c1d46051540f600c0e41140901a840e600210a1000c03c9204002e00c1c003c10b088061a0180404001281210071010a0805e250f81a94000551034980b040300c04005c610054400c4190030b03a410048031000c1030900d6a00c0c4104102003a01850074000c1001c440b984821900005000340c1c00421143d640b645e4541c00c2ea041001 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 398694901 1250 398693651 398693699
    0x902010c060e0a02011b0809120c0d0b0601030b0a061d040219020f160807030303020c1501030615140618010c05070603020d050703091203050705090d0605100b07050d08040c 76
    0x4104084d0360788407040d081e9001d0b004240b0703030725284141c0d40c00080d4843c0d005541e0241511101e6001031031001c1c000e01d06c042c100075014080c440d2443c0741101082d142250b4080c0824030b00302200005041c00c401d86030664405488100071449119404451080d2503000a42e00c1502006081c942e07158640e207840c844005500240700080f08511414100320801448180409d544041085250400103022040380d4050400594034910141128108074003140140210a89a8000400c00c000d40d0702640c3d01c01101503028182e81d4841801e10720402078000d0b25680700c1d90a03c0401c1c41c4616481c405012200141044070280c0300030755034036040814540c01040400d41c04110520b100005005442e80000c40c2d103810031008185503620039900c6c082080d1b0030700301aa99000200985e02070b404540d103800c8002c1a0b440017000038505600a441c045845815070b414241b000a255140b000a6941e0706520030082c001580388404226003003400140151040624810002040c664865841840c01d52400d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 398696151 1250 398694901 398694913
    0x1350402040c05030912071403190207060e0915040207150f0501060f020604201504050a0506071509021804050313050f0d0b060d020a0f0f12020d02040902010c060e 72
    0x10041104464000c40803000f480000c10820031094004a034110800b06514507a9855480a05012201c4c0718000e00d00555407000040d551f030307164208030b0b010f91a108030b43e084070000c0d9154a82122542d030035440007504640108040358008a032040501c411141c0a0001400c1c00e20316128103901c034070000c0c0c1030a403055841c1001480000303103010399805044103040c42070356030744d131240003d607107840091010f01015913078034440002c0c070150400c0c0d61081c50300800e180c862002c619480c001d243e05ca40700f400d1084a03101d40004003414004203131038103d6004000e1083c01d080144551014003059902241c1c88841025030301f81a0401c01c0c03005000302d014000840e280c0d4202c6015908076030b5a40c00440c0b080b10b1302c840c003104541e21a1049100da90f4007000381c2910361a1180405ca56070000c0c2002540072018400102c1d64602111104080f20b4080c0300b040c2c21159214000310a02d030408101a4021401d03225010150500d5004000020710600d001244548161504000c03120f03040304021a641141c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 398697401 1250 398696151 398696153
    0x20d060b030f091209010e030c0307061814011e050702042a02012d06050a0e040b070906050d0e10060f060e011d010f020f0f030a030c0c020a05013504 66
    0x100700c00c503a2001d0480018055802600c40818180c02801d84e17031410802e02141281d10f90301c007480169000703180a4111103d5686908014041001629104855a08000c000240c140c11007504458802e4103031540142da125007400519580844402881444003c20600c00161910706c03a20342000398034421000e086401200309001c00300c0b00700043d011613040021007202501208c2100203507a980503461017000030a0517111000d840142c1c045ca500102c00000003460721160b00038644158813403e0a08829a1503881c161048130039030107075800040f41441805452030282e40001055401481181c448046514600e000c0d03520bea04500c03248000000c0800950b82c000200003c4040242003911031007901c01e11503d031b6903003840042c41c10010807404000e01c0d21b0083c040740c202040c454040e18840100d00100d1980e80d48000c0c5600d0000785881c908442c0680300c0c00407231060030b9004200c0b00c0c101c3d1078440112500070020966001c118450080700c1c0b0030344005002c8159040401c201143c2624003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 398698651 1250 398697401 398697421
    0x15070b0f07270e06040e01020409090309050d0b0a020f0408011d010507032d02160f0c0b040503030307031d030a08150901032103020702120f101a040e01020d060b03 72
    0x1603803044a05503901001544102e1400d1181d00c42036400c15081c00c41c181e80c404002030b0181210044040080d480040c001c0360320041d07504402c103003501a4807000100ea5a03002400405507074000043c0040d0088404204140c101d03800070031200c0e600002c460b06098452814500719583d4500c010181d40da81d04040600030420b015265128100b030a023000405e4650390300f444c01c502c03003480b5035107424051a954000e0340c005505940c00400741e200042c0098500b0300d00154080300c1c100043d942141c282c030000a01c4800801220305444018003c1c50568841140a50140040210080310044911008070b00c40200700b0141c017008110755a20301d02c0381032084603000040e01101129025408090040c004285500940d40130034494848900d0314601c00c01e0110020b01441000035404154503040001030080001c00500720409007040c0c0b014001d040d00518215500c03001280708800320400e01a1030751910354459000307440207100140c078220701400c04004645c81600580d0760b40b100030081c0910710030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 398699901 1250 398698651 398698667
    0x2010e04061503111812071a1201050301050103020d080a1106070513210f031418090f061f0e0603041a01060c150203061206090c191415070b0f07 64
    0x802681d46a160110318500c001e003070f00c4039a0031a401500f03e403040d08051042040587c00811a1010324444c540411006000c540e02028541100c000d400002151910301813240b076048903401040440052525902c141c415084171180406110000183c90280001402201e1040d011566803a40d90001071030741c554003040e10f400104104a409030400314111801c030f40440d02d55001030200114204e40d1808542001e502141c07801031500101c0d441c0c9103099040e21010480004a5031884141d40d8090b240c0080801200c209501068040403103c031411000c1c0400350904032880c1401c0e0401c030207030105695603c2590104d8200c41501c60120b01c088050329a54094111441e201c5594042516078120001200c01c4045441d54000003041007035850a082000300d04031802601c9040c43c0180582d41c5444203102014001e010007070312441e1031000c551149007902d0400801520000c1c000301800410120400240c2400e24200300d080c0200e100641000e05c60010740325282c00900c0c151b000286403c03 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 398701151 1250 398699901 398699921
    0x130903020f300f040b0a1e0f140a09050d050d02010b01080f04080306060702040f0b0a0914010b0c010e0613150603052e090b0406050c0f1602010e04061503 68
    0x82c0e100e0340b035001c012404a18248108522210540d140d025012100005110b01d40c409481c80700009071000b072031500050190300100c03c409a00b18a250208010350b01e180d2140b01e500e0000d1190041001550000005404010080d1070300a45250301c8102088880903034603801d88042e803283c108404c040d5424045c00380083c00c20f10f804280c0b4103050b190040c0c441e001a000616900c00400062940d481e000c003642d000c0c54000304140100102c0b4a540001040004222400766508200201d01d8840b18020600300c50310382207506810381c0c40d0540035009500140d440400e503540303401040181b01d4080000a01a180c0080041140d0601d0318102e10121a03042c00340030028140300041000c10004038544003c600c0781c88030062560181a81e0888070090115951403c40c5005180c405000880310031501c903600ca99003c114076155002c1c0b505450094404039514a081046070402003a018040c0403160761041c1000504c000c012030004098500c40c0c5c0000c0c6d240c110780e0b40065080350703060064107031030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 398702401 1250 398701151 398701183
    0x180f0b0603070e07030902030a08040603090c1a0406030911180a05090d090603240f090e03040e01030201211406010e0a0e160903230f070602030711130903020f 70
    0x480e2400c40f840d4440d510080804040c166510066015500c0601140c01d0040e070064a00c0d540c0c40d2104000340082c61442c1d0280d45400740b1030004203000b50008440383d520072007070b0b4100d030070700340380000840140c80c910170203c5040018244482650320351020401040c4c45600110310145449000350044540090a14141c2d41c0004c21850300550000d6404059034114070f400f082142d00c0c00c00800e0900840a401e42134203500b1900000c80b030b064240d00c001a00c499907424445070012002442e982d0203540503960760101c803035004200541c01880081443d0072401c11016038000d4440c0454200c2c0c000781d00c0300c400040d4081c1000282c1d03900c150369000c45070007200c018500d00c4c100402010300e820003d2140c00703503203034074025461407901455a00c002540c0c8a0416507403c610b80c42e108540451152100541340b0030721300c100e0b100c280c0c00718a24007960340e964021402d104041d20740c0032404038002d400d507070031410442035001a524640620311025002c0d030018505060b600c0c1c0d1030303031030000300044c0700400d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 398703651 1250 398702401 398702413
    0x1090602120703180f3009080304080d20010c081e1303120b0d05071706160503100b1201050901090c0813110a120210030627180f0b0603 60
    0x1820307070f0840702130040d0444001d48421803941b07004074884800e051108906400c403ca4071a00c100134041c04420b20b10300d583c0d18101a6514080030f80c2d207005d5402010025040100204c6542e84901904035610307c04d10100c00da0030904060307a07070840d0300740020300740012040410048000c51440a58001c2e40140f89004010314181c0481910300c601319000504000303514484408503146508011840e550050011464046620b0302582c1c4001070721480003407840b8001152551580070a80c0c0d84035a80d02d641c0d854508e80c40460480f030341d603c02408200c82407540d180c04202141190098206020541500034065040c0b00405c40c11140c16032243c018076040040b404812680041120307000320070b103421191042d95501c0d000e0418000680e0081c0c02c40c0c0c030707600c000075101c01c00301c840395803140284c0b811711400015041c1182038400f5070041da910400f0022091202020858518a015090800014080704003040c05029810b0710407013902c22912000c410790074019000b1460340c1102e011002404 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 398704901 1250 398703651 398703671
    0x40c141c020103050c0d1d06070c03050a110307081209070803270f04090b150402090a050d020420090a050625080c0a03050a020f1506040f020c01090602120703 70
    0xd0180300c100c00090400d80c41c2e8001c201012041c2007600c0c0700c00580c00080c000c2c1604140440c44d100c001e9066000711b44501000714525900840d48403a2160f0185d5965180442d20702c0159801c2c0d021501d02c0c1e0a0b48802c00c0400c022038541d002802c442008074603400c656003880e0000c0ae14004d8940c00000c103982040041c3c0c41c010301801c2580c84083d01601d20448a0700d6804001800f0992510125802c81c0c1489040d000304100780c1c060a2140c15184948040c80220500740412802400c1c82641c100f160034030280528500019003441051000f00080b0b1000c098009100011400103c105203408001c40d02d804039203041d03103d40b4003510098601038104800d0454600910120120401207003244440b00e205200305003080700c9162400c0002c88903503029902d4014000d0788114002030041c094050054210b0740003007415042003454149541d815240c80e001c102c01003011640050b6a1642040721001c10780307003030085403a001c2c0180b40051f165165403064007040304000b002142094a0070b04815 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 398706151 1250 398704901 398704939
    0x81224030c01050a030e0f0d052a060604020f0702030a03030b01091e0b031017060103030e090f0402150912030a1e090b18041515020703020d0b0915040c14 68
    0x20184a65031901040f0703c1081401182006c41f151016005070050b2084084400d801c08000c00d4281c1620f420070450b211400144400b0703a103001c41c0354007d50001d402217a0f082c50282c02600100b51205403940c606015940001c1c90010520800c42c04a619410300c41220f41e040341904e0002c00c44102014400c800d20094000040c540d0b00440310104001710104420034290803142001d41180310340c42407040c418241895480e0024803080b000901302c88074148143c10030242c5180a84803035907500340c1c82c1d126a0708100e003200070a21038070340b50001807140103200d54441c10a0070103034000d00e002d1541c640f1070a4000300720851100046100c20403a1030503d4520344d001241d0811181d0502c200c58035406500c41115404011115041e80a82403a080340b02643c5004003c03800c841075048404904081c00c141070303031220304500c0301a40c01040e094401010581c4805016440352044042c0c0301c185523181f9010400000948003940d132000801b00c2480f4480e401c03101d150081d6001c481650300b4041c400000 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 398707401 1250 398706151 398706157
    0x10803070816050c03030418060504020901050306210102121e010303020604030c02030102040902030a1d010605100c1e0f0302010c0311070f1b090c08010b030f010b07081224030c0105 80
    0x10810042d01c000c14018403100b0b2100c8012a04018140ca41d0344c0e076289089021a40720341240d0091500d840c6000034649068400c80300c0c00342044e11005e0643ea12001000740707600c00306a408004034400c500044040b8028401401000c11080724105181065041104c0f212840699154104206001400800e40000d495a07000e9030520b0b21030041d086d00e02c04203001e8003c90307100200b0701c2d0010081c090034610980203100c1001003488001032540b80240c240b820f8902903c1029000400c50050310383d120311030070304103a4880c0a1400058075403400c4940401c0034103c2202071f13820f89402a19170b41016420b0182d03144103407013031078280251300601891040910400341d004007a400d88840c000308003d00c486601019290b40035003404850780d1503c581001d040f03c0b80c11000081c0040002103180c007100400c0e07074005d904100c11242e26a080000140c1c0c1907101e104191082001031150b0740c81f40c082035542e04c0c4900c0c1718100d029001d42030382c001e1101066076403d01c4d9100340c00261036281d103a40d2140903 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 398708651 1250 398707401 398707417
    0xe030a02071202221401090603050d02150c0c070302360c0f03040201030f050708011d011211030f10140702010203040b0a230c0a0e0a080712171206090108030708 71
    0x31a681091120840d8004e00d0318030740e8401400c82005c00050320321130543c0074000312070143c1c0c151400300702c5290089172101c5184d0101042c80351610045507031a590307100071309107180c27401048a560b99220b80016494226804208100784003e42510f64046d540c40344291554041d00c080f4041810010f8981907640107a070503c22a100000c00044c0642e0700c030350803070024601500420002801e0140b002044200e0134000c2c050b8607038070034000c80c084400039020a41241c440170a0b003400d0882076510b011860409194407075044c0710f16030305000042001c3c0706d9152000e140d03520014010141c441e043c070b20440014422815a44144104404200c0300c000566005081d80d0f4000380350740460003648440701205541e807420b0003003032040140b80b8000758018000300b115511040c07000701039981001401d0405006601c415048420100110300d00c1e141c600300c60360700c140365003209420074407184807050f0070007050f0601c00c000e00d40c240602410165001405000450007540c0351010756200e000d500d11950711 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 398709901 1250 398708651 398708689
    0x90e0d08010b0d09120801080d020f1f021e0c0d0c020d06111c0203180601030807080304032109170412080c0f06070c0506070c0b0718090e030a02071202 67
    0x200c510229549034041342501d5808803840d005440c040c000140070010134025440749105103650007003054000107909080360010401003800000d41c440d5885150082c201c1142788070380a02103440a40d100032504900e0f465104901e684030303e00405454a001c024a4188040c40703107111402e03026860382d841000f1300c0768004c8000f280c0c25110020303050342885041855402008414102d4501c60120340041d070180b090041003a880e00c0280c00c1080c0c50386030a100007861200c0070808100080c1121014651180c040e040110221b44000706041e40e18200900c03528100340c0c0e5500110400c155808940d055428020905003040d062542c8142c050a2002001c1c04100b00814101c00d250f0b4104009001c2c82007140079540710f410008400303001c50791030f500110b41501a410016025030b00c1090400382580d002282c50825403a1000c05459080c00783d042c0030b60381d6259403c08241500316024050402084500941d590000d40c0d100034209099900411000d160100142d000350740d5a000e4241a00720040c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 398711151 1250 398709901 398709907
    0x100902090f06040e2d0f04031e02070e09070b07020d06090204091203050702010605060a11030c0d050309060919020d1109100602100203040f02040509071e0306050a02131502030c070807090e0d08010b 87
    0x1080540c9c13038695440d44903042201c281c4c4080080c56011490b10102c5584c250036400c40c1c2c4030180c02ca42c8030045c1c0d0003402c1c010a01404240c0c090724000c44e480125034000c00c1d0000d5404c1440d0040b13402e568502d0002d40b886a4442890144a0f41c98403c4650040091000304071007414100055050f1040740130800170401600b16040140c0703002d10440350601c620340200c490300034900001a080c0d410131546080e2030301a220000e01103d601042e800b004201180b10805409156420001d81014a6605030749911580c800c0e41e001b920b44104060080310860007000180789404802850020760a04070071020740144148000101c04180c0181e5165041754040340942e5801240d614080442d4483e00031281100c2d4101c005603005900c0741d042c0e9002e001c0c144a20341e00c0791020030a902c505c12101d0561108118108001b60000e5526002038800b441600d00d050b030210101458041660403e03030080e002071a041005913858030aa4003000b4900010304007008001101a2402c9414131441014403000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 398712401 1250 398711151 398711153
    0x304023f01110315011412010621020309150a18060e0c0d1103010501050901030f0b040203070b0a08061e0d0809010219030507060b09100902090f06040e2d0f04 70
    0x29048803455808082c5010303100d140900142000c42d41c80040c3e05d01007444480d40c410242e55400c12209007105050790400d2503441d082c42184ea03170302840303241069141c1c50580500f104c4c4a03400114000c51050008014112641400900a40c0c003d4400c628041ca030049160078141640c5046401607008040001c0712180380c10028104000721682c1513108107070149160400031680d1503002d40b0007040d00200650b0780c80d4024000070030001e02014241d09880d03484070001605d0740c1300d2580d01c244050305440302d4698480d00742049070030171100d241c041443c20707003081118282a01580d49500801340751007030404c00b440101e415076013000e0f0702400952001480110030b034020015012109094110b0170f00c0b00c0f20718280104a80c000c44401c444070340c1069400000c40c54090912400307500710100e011465072400d03101c24000d600c100003544d04242545454000e559605000e00010640b200309440b0501e010380d034043c0c1c2c8010000e58107100b500c01d0480d00000316003000d2007031b50140351315076900203d0300c0e1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 398713651 1250 398712401 398712403
    0x30314101e0551070302010603080d0204080f01050c0712140304030c050d080105031b010201180c050102060a050708150d121806050403050c06070c0e09030304023f 72
    0x29030032031900800c100003d4525005102019084070450300302c800400d030f5a00740500c1c400100d61504105401505521409014480d401480c90a10070b000025001c0c1d030f207680d060415045501154800e80c0c1c003103000c21103c0b00a204040c118020b0400801c41450700046a520354050651302600001058840c001014000d80d101d0440c485004c50302a01c07880d00b440e0003004845008011140c0d4011540c600c44035501840801e4141c582c010054030364022404c46141c2c49140070007030306046640b100c405001c8a0514601e1701540c43c02030455980c010704100c0060b140c55400742c0401c001c6481d040400a410754170059031500050a40b60181e6030740c0350000042c02029000201508a0740c0f400c5214200e2a00f00c0440c901d015038010030151099660581903480f400b071444050700b2600b0811540c0c4803032502d60000e0401601c40c3c074040044540300c4a503c0d14142084849903669800003003400250714055030741c001d804c0e021018054541d003020019a60549140c111203442c118008510656010 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 398714901 1250 398713651 398713709
    0xd0206060a09020306060d060806041101170a05090106121a0601050301063014010f0f08031b010e0708010f15080a0f170c01140705070b0c280c03031410 67
    0x14401f00900003a80c41d090904e44034882982c08a40c2c04404d030780210305e90350240030400c0038807070021034801d010741c1d80604040c081d04d40181920740c00e558804012603010466180d03803a07101d01800c80e07085a001c3c85c070304c046c1c10400c020301154144482400104815580182030052802c00407208003510160403608000c0a114961080030060400340e003407241802c0324004a040f9400c030102d000d00c459562611280c80f13240c0f4020490a0307001040400e00b000001e8242050784d000301c20000401314851080d1600342000c40c0c00c04942782c0d46502038072021446d41c2c01580750f40e0320b44107000038641d4a0241320300d9442c280302d60000c05040c401d503451b40c2403204041c1100b10301c40d04048030781d039504811502d0340d0003803401c16141c182e54031900b00410000ea208500380c40c1d0042c1d001000180584810504921982041d0125000181c0310040400c02031030f60b62603c41c0c005180d8648000030f024900e006000c1e55103412082214031101e00c10440d51500c29400c03401283c0e1161400a026240d500300c0f412144 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 398716151 1250 398714901 398714917
    0x615030209130606080a0f050c390607020c060a210f0f020702120606091803040f06110c0d0b01050409060b03011416020a0209070e180f090d0206060a0902030606 71
    0x61404030002401d903006108544140d104200801c269000f5000020413500240d0344070241540038041404044003004450210203080ac0b0400480d02c074420000305015140f00303d1600b15040301c014400c102c1d030100b0605a40170000c5075124103110342e00800070420000b96400d48035150070a50507402c00b91403584800005403084230f0501c414211004014060b620a510490003850207800306031041e40045035250068000401859081c2c90369010840d89145003090ba184c1400304000000740d608501315940300400b019200c0f001c1d15108145d80318103041900f0350841c00341c81c1c07091111000501d2224410305450044400040001e400d08107800213100004d050f0760550310b08800030b91034280c0c02550912500c141a03401c0358146208004a0700e400200d24002e41040008001c140c145004008511103054041c18802d200303046c046418141000a413804e500507028201030200407041881002c18500d4640003d02e02c1b420004085401d031640e9204ac2c0030940c0d404004500c55a4903441158410 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 398717401 1250 398716151 398716189
    0x70302190e0310050c04030f0314130302211002181306090b0a080c060a0e04020a030e0609030703020c0d060b03030406020d09090515011812030e03100615030209 71
    0x35040315400a00326071039001d1500d00c41d104000c1c0ca40f503600030700d0141610582001903a01e042c0340c90340d0307100d008101002d0340403800d228829070115810b24101c0042c007800c48400380e03141e10281c654010b21006280b912702d02aa510289241200030b04c1c0c0000e41c11540000041005a5a15058468000703011640e0750b48d551140d8000d1a003190122150022001d842c082c044c200072030500c400801010f02e95034883d25056412007641e81c40e20307151181c040c0010350b00c1410805000000c2c41c001400b2a408400c1c1d01011076500c000014510008000c0c0765800003203080194507000454401a548980000c04c481c4100c82c0912102c040203100c1c0c0090080b140c0140480703450b2134a881c406925854003107410400160000b00020704030200b806aa401005600411300c10f40c1008801180c00020142c6804600c800005000403000ca0014100d40986d000755a0b96a4a80e0a0000c041c1410600103a0711411070030588107000d00342980c21442c00821260030300680d01c00f20000440d00c0301c1c0719a11200a4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 398718651 1250 398717401 398717437
    0x807091512050106020607210f0207050102070c060302090625080408030c0c0103020a0e0f190b180d23071a03011814010504090804030602160506150d0b070302 70
    0x40c840c0c001d0103041e004510140180040d0780c0714082203030758400850708200001c3c603a0300c070201030703c21860764201600491940484c103010340c11000707401c1c0d905c5040115020b82d40001c00c00140000c20940030050800d61805615000c145400281d030790061485001c000c807021201440760b001038100d21070070369900074038840e01d540d900c0c07060a48940080a031b06141c0d00071a030599403250b1180c400c854000c021a190034400403000402d0049100740c1d05a09600102d800142040604e400b084441c014001c1e0301c80da59031410240101c40700401c0d4200c040b801144100305400000342420030f0301c00340700c03550800741003041c2e0101c01a0780340c20000d0f030003020350580b00318140c0c01c101100300003507043c0d0707113100d1400f085211000911412500d0400820000000682c018030a507c0c0030f07000b042e10180203c03c2039040940b69281d500490340841d59140c5022040d019140c100441071003541e60129004601c003450080800215030400c07800b01004080c3c6101d60005183c260280e81039030a03002c03000b009220 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 398719901 1250 398718651 398718689
    0x40b030a0506010f0803040812090111010912020c0f030304090905030f0a030b09010519051003021c0605120d1b0317040f0203070f060e06130b07060b15040b0901080709 74
    0xd19842c0c00c0c06003965000c3c0e44100030910000000440d41210210401000d1400140d081d17002c2d9500a46030680c1000324034140c40c103007004240a001c10307880c0200308410700140c40035006864a01001c3d00c0502500c0c2c1c43c2a0120380c1d03070f008800d90701159581c0c0400714000f24a440c01c141988205000e060b051000803903070080c500d50550128104075810707180c124107641c03904100000c411109604400c1c54414070024440c40c1040c411084280d201c81c01d0240c20034400481000a05900d800b11140b810f546220400041c640201c100d00030041c07031006071006901c0b180340142200c05104105104402c55030b99502054401c48201c01d04042ca41401c4071103040c540741191840442c408240d100b03114070000071600a000752182c0007150400d84891358003814000901c015600031240c180c942007101107000420104690041c6090780c460040000d10032410380c02c02000ba10b440d81c8500c5c410a00303002c04e00c41070340b0101c1115044c00090810503100e0b9074542013100d0001464000c0b0fa240908105414 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 398721151 1250 398719901 398719903
    0x9061a18010224040605180a020111030d0c030b03010b04110412020a0b07050a120e03150a0f02040e250c0f1103010c020a0203010b10140318030a0903060506090f0a0b040b030a05 78
    0xd004174440e82003405140c541c003000d00000950380c880c5420f5904140d14400040d07005071131141c1d030200d84070f065a040000d4075440c002251002107204004c240c69410b8008981f40a200707030288001c04403410004581960070700c0b4045e00031809202030312004000110199030342c038440000245404100c00303075505c102d8a8840d45644e60b0302d108403420300c40046071403102405a0780d504110000a40244000705070000e018000010107400d0604182c1d40d11059100804ca0f4001400500220000e08190341003080d100d8481a40c0552100440180c44840724596a441500320ba13500703800c440c0c0c0b449030030154240f0114041a88111a078550702e00f100384641c40da0085a201d07115030089000300449508503083c86045c5107411900000100e50031032203e0050811400f0319044001c1a16410f6041040c12003c1e24540c00b00441c41c1c041070800d10200100215402196170000042d40c442040303041c43c0301c070100c0b080d40240c64090601d483d003d050b407154595600c259040e62000301100c00c012800c0c1049 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 398722401 1250 398721151 398721223
    0x71209111c050d121107050a050d05040b0d0506120f060a111216021507051201061e0f05120109050103110d171e1309061a180102 57
    0x60701a0161048000c0314004000e00081099085000f510381c075007035076000b00c070075000a074080e00105560705180c0032000d0740580a40005407141c80140010030841c00c0403843d004d03042c1c481d01c003041003c10003485009440303000d5600d08000c20381c0202d899107400700001d03041c10000c0005041882803503c05440c401000600600459002070200110400c94018290b18480c00240078046a90f647c04540010049148550000010320584115103264441110703030030800d8585400141000c1400050345142002460040070b450034400490881a192120000c110820000034000c1c078480e0300700b455004004407103d502d14040700c02c4c0590784460850004010a00050b074092141501c4002e0600f0040100c1d080c0360703005041017100042124181030b06500440d100d42c0300c055413190101d00700980d4006021802c6900f4002d02010307061040c6075046440c2d9502070000c0103900002e204058003040101c81c20440340d2451382c1002c185820060703280a004060b40d06258002c2d01c0e40b80e410100d040d8007 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 398723651 1250 398722401 398722433
    0x2030d08150f061603050f040b070b0a090b0411060417010204032006040e040602070b0f070815181b0403141c0503060f0d060e03090301051f060503071209 68
    0x1203000002112402d00450700106030710150404000c0101000300e25081c010900414400e00d4110f141404017a040d103802d4020390300482c0c01c1640130604030100480721040540c040b803000c0c01007011040d5915001324001d40070740050407105800d00b064070652520b01c120307405060501041100c415005000500030342c03088c13205440100701d1a00d06c26031643e040070850050880140342c50b007480c2c281213100c1000c0c8005042100d0791a801c00140c3e00248040b000c41c1e00c1900c2500c80c01400c0d1400f00005040840018000d0200c0214a08071001a07a03030a444500b100150b101a0180380c0c2c1c8025400c0c041c000c007512805030307001c0e01050020401c04032035590030007a42e041c0c09075090322090f0b4455000a12220795400302042091000a1403070514503020503ea0400a050398000c04068445000711a40f400b0030000c0d54000060555140c01c00340aa56001f1848030700c80d242012146010a205011502500c0100280040451410f0384120000c081071285658208618001454204102104190 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 398724901 1250 398723651 398723671
    0x10f02031e131a0703020d0504080a0e030705060414060c0f0a0212010b1003090302010b0d060608070e040b040206031f0f151d0f13090c050a051e040b0d02030d08 71
    0x400190342d0100c8400168480780e0040d00a8404845000540e200c49070081c00e0000f003603400e11400d01407604e5809802c1c0558001c52940d0340c0c2d2807a80400400910310001c0031800b80d071090341c040150ba2508421103003200c100c440300300824680ea20001e0001d01c134240307900540e1f10400c0c0d50360b88010404185510103501c201e4030541140308001c074440c2a80c1b11402e038aa030240c1040031280781a4080c0e080701800e02d20030310000807624030401c0000d81408c94042c091b1152513584400f4440d0302d40c10400c0c1005454201c842c0042d6150695807180380003001080203008401c08401b040d000348140c4003009d114442d14504920b1203031240e400c810040c1852290f004201e598001c40070590740142c003002810030307140c000348100d4941c035010320810648080a00c3c3d0460325420303136070340300242d01e20491940c0c0f8491024070140038946800c01240b0380542e003006204001c082484414004607c46511400c00c0541d0080303002841c450009400740344d04c9601039014041e80002031103495200c1c10203807040840381 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 398726151 1250 398724901 398724961
    0x905010e06160801050d150c02060a0e0a05030403080711100f12110d05100807060201240e130809040c0e0102070e01151809021201140411040512010f0203 68
    0x1c1c004114000602e0402c008540900e005100c14240091241492030040f0000030b034044e400440a01294070024150380103810100610209030700030700070b4049496526004281c0300c10301d52105502c9220724840102607000020718841040364807510200c420b0001403480800804089024181c0c1d40219a10300002da4a20710200300d80040c0e2140358001c18194070250b0038040f0b503a000380010400a0708464441f0008140040d44890800c60140600060390000c2000c0b20b8403685012100503504880442c203140c40b1003400030114030341c5a113a20020415a240405206080c0002144116481c0b00c3e005030601c200c000e24250006407080b055030080e400c03241c0c0181d0304d600c1840034800038062424600c10713060040450b20b104031802c0690044000007031100310303961601c9000b02d13841151001c8112920800402c00c41e28030421041904d48142c605104084441c0f140341a244200c0c003405102c0c0a0084a4107040d003001d512010500300310040c219503d04000004e90074403003011018408140040e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 398727401 1250 398726151 398726161
    0xa031407030801030212010b2205090c060702130207052b032c0705030a0f140703030f08040f060914210403030305061305010902090a05120606010305060d060905010e06 74
    0x20446a90641558550320380c2c0e42542e082141900101e000c0c14055900c3d0300764684595500907007041908101250954000c0d0300d039500d002501c90017042907034181c10174100c1c1078050b140e08040340c08107a81199280d03160038290001030001e0152030310203860761040c0c40d1100d101c18406040181c800f1402c2d044019030020740c190441c01d6a030420b025251484500c2c0c140708280241010000603c60300c5d000b5504c2c05c0e920380001c245050b0f00a10140d500005101001081c0711116501660040a18002d081c5031070641d00c000c1c060200842c0760004003c1d00000007018040190300b41540237500c000b041c0046034850822600210106900c3c84960182d56070740000c80c08600c046003103494040408a007020300d10340b000d900602004150302d4210091130105c22000c5445d20549000c4c0980800040e140c1402c032043c03150088ae66080140070f4080030038456400c19000a1180c0d0182c0b007443c5c0403440340c0c0d804010400300c80b98580010082818401c0340e008110040d0801780c6114800d000f00d60240d562 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 398728651 1250 398727401 398727437
    0x16030b030307021e04060b03130c0f060e0d230106030c051801090e0a050f0715050903150a02040503100e250905090c21070803130b090f120a03 63
    0x14001001303512180c1180600740d04040300c4004a10348100a0000880b9503503103110300b550b503104031154812020130329105810410b8182a8074042d01c4800d074000002d13403c1900185c0003000c81e240c3c8071701c50460f900020040028542c060543c6082000c80c0710307084040c51103840d0280070300c1d000840d11340d40064408101410441c034082c1000c1c10302c0e81641c00607407a220418005002e0b400c1440d025006050f071071008a0310070002d41200c40380010040c91541c0c584410044840314800065040000400045099a8000502d5241101c0701204043c0391380391106010020b00c2203a1080b505400b0b4844400003181c1e2940c001c1c5400201c0d401920030035881d00300c0d50340356410b41941c203200002500d43d040c0000c0000b940216405140c4808807200e00102c0030020f859007031005181a00612245a10701d40b01c142840b05c1c4e8002d0128900450a10039901e601003048190b5010720f001d01100410f00603400d9482030600b911a850150541c0d240d170100d880c42c2a15450081802da02103400507001c40f140c555 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 398729901 1250 398728651 398728657
    0x81206040f0c020a140c01020a080c011b2102040b0d020306010e1003230601021c020703020901090911030604050601210c24020708072606090d031802090412110616030b0303 76
    0x50b4098010027030155241d4460740c000454603c0f05641c1c81c1540c035160034406640e5009030640703440312911413400d54611020400b1090300000318a006110402c00c11030f2800a580200040d00700160b143da452000403183d8014814100380c0c0440740403503a1701c95542560014000740d00324104030502c1b100c400400d540d140025600c0d0b038016889401c00200d907880024240c840c440040c07040d220095520740015040d0002a00b02c40016503a1301c80c040e042050304120b0004031001540504075030310305521040c3d110344c03052145a0303c1d20013006255249000c491056072280d03510100c12042e8a40b6002d094412104182c04102c0200e0017450214415000280302402c0f1000344008203501801e15082c50794036050800315420030400005400202c1106200c002d105151040003081e5101d0102c800405581c0d45094610844480340018005a15800300160703002c0d41080c030200440a500d034040394501e08803180100d0b280103180a02400c401020b4101c40314560390781d410301c11209008100340c1c40788 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 398731151 1250 398729901 398729923
    0x9090711100504051903090b130609080606130507110609160b131a0705010915060506040f050915030613020f01030e1e030405060d0603020909030403081206040f0c020a14 75
    0x544100c0300e0040945245d040703510000d1003403030803c0c449030b691400c0101e07540003d511114403c804040900001d58415015402441c140000340204d08018001c110300804003580e101220b520362001031300076030107003039010100f01601040321141e02c0c00d121440d4540760301000c900c030303500110300e0000740380b81041d010764510810092051070410b113480c030700d90300b602000f503075a901041c0c040c01b056011520a00c1200503850060600d000000017a0b400f00d0103c504070b0304594400c400901081c000851b04504a1080d1102507903414055154208001c02d40400348400360b5044c8a41c104114140c003152b044000414800d544020403080720000540954000e640350810507480702440841e4420f00320594200c0749418020740b860b1686a0780440c910758841d8006503441d0380c40ba070081003181072080795542c1c0301e454030700558285030540d83c87c01410711401c20800f9405d041040840c01036520341d0301400c7e181090041c200041c008010021f500e50181d1807047da103900c6c002ca10918a83c5010884410038 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 398732401 1250 398731151 398731153
    0x20315060303191709032101180b0a030b161b020915010e030f070806010f080a080a0504050901090e0c030d091a070b0a0b03120c030901140909071110050405 69
    0x2d41c410714901000105000c0031003c0140c22400f04e00e10000c81c00b801c9014242c4140610307603483c0300b020000303680076040c0d0408080a400000400c44101021504461180129000320365482624005581c10039280c102400058030380c000d200d1309401200301c894490f013071900c6081c51604041a90b01c00c00903c49006508065070b0b0300040c11204490707100400384c0c2c105051090700000c180b00400e2400e403800502c12216440300e6000d000c040c40402000e401001c2c000f03841101c590411041980b00e086458004200c4400410806800d80c0903606607400b801d0003400c0003125603520410310000e440209012000c5004888008a45040c080741405003400b4584500c4112454811020b4103903c0115000d052141c1c14018000003c02d88100180034a001440102c1c0d01429281010308100000c0c15058642d1010171010541450200c00e4901210003420201080310111582e102030344280c2e40c0003503000618100304074280f5003052110351001c1c002e0084a420040c10280340d02141c50980300a0b140d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 398733651 1250 398732401 398732407
    0x9050115080322270e0f010b010908120f2508030a0501060c0c0506030612010f0501330e0f0d050105041e020906100302120106020604060c05031501140f1303020315060303 75
    0x100743c1301114048503e8002d14000b5188001e581c001e42040c407991549001c0d81d440d11005041c2e503034407980c0b0720301038110b0700054506107400f0010700d5014032400540500710071703012441d40081036800c10f009002c0c5500d4006100103000a140c1030b4640c0d1f10032214050410300d0f0800100d0901e01c5510002810b90f4845480388000d41898200800e58000428140c1c0c0603018980980404000380249a500c0e840081c02003299414072404500c250314441e541a69916500c482c561842030b000c40000210300c460401d80b4070b80b052680454071403066210040d4011400300c00404c10454154071452085002d07968480002d43d04400004000c1456240a540502804089055883c14102c0008010f1140c01d006241076508507130180c0e1000240d0111001d6003040c4100028811540140200084c082c038050b883e519044192804060344132407450b04005c5014080101121f43c60102d40140241151580d00c8914940810f0301c20180703400128001e000c3c02000303401c00840e0890407130013804000d0195007 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 398734901 1250 398733651 398733689
    0x3060c0503131104020d020d0e0d050a02190201020709110310050123250317060f0918161401090515030714073008070504060309050115080322 63
    0x2e401d6014032501913200d90b08000c40203554001d44001e21800c500b880012a00c07902c0b041070306090a0103001a24184001004910885680454290510001e8615016140c8c0c1c607400102d2400300203070403003c1c425282c00e50342a143c40c40d8201540c072820920b40c40c1100c0700c0c1c4076001150b858020780440b83d200300c4402150b0035600d19910151500b00000440d0030418103040c5d5207606081e498444c00c1e00410b241d04030490720404941140c0703078040c20135202950200f88110200321001700041241907000701f81807141a405005010b813141808040d103400e2100b981710301104d07003d039500255441c0410700ca400000352038101100b102d880640715280142c01c594484a064966181c40c83d020140194100b00060020300116503003513610a009885541d000000c82106031410500c1142406000032403040144907a844000c075000d0394083e20b80861046154a00f450241c4030f40036110b5100300040d1408070310728500202821840c2c04d0f0b42e1000501d040178000340c180c0030790309010b0711001051038284a0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 398736151 1250 398734901 398734913
    0x10510051017011502010e070f030209071403130302030c0a2003301c020d0e151b040509090c09010e010807030206130b031e070509012106080d03050103060c050313 72
    0x240c413200300d400085240500342c0440c90a240032900725001d0786c462030310248150304207070003031035445402340c1016200026510f0b000e4100340002407008a000d0b119000c1101014800e2042c2c8518080b00c008032410f010307035807501d07a08423031100071100851025880320684900d00014885111414139142d6008499034444070380c454450402c0f554900b00e4200320081c0070300345030002034148000a4100580b21040e8030803c2e8103844131200c0150199000038107510b00a00780b201c440b50420300c0c81014000003030b0824203c0300d85d07000d2035208643c801810380422031302103c00720740d01409000403600c42407c0d80c3c88100200b0142c1c400c3c0102c45a43c1e0040409100504205004201c242810211408240d0b43c42c840f03000a80d00c2216032110441c8100941680154024469070300000c107414042e040c10908000280080d190b801920400c502d06100300c03003371640e29400380002c0c0070036030140d8007280d5899801402420080c032007120f81a00d8000c2c04005548104144c030b0160030b2401c1078040e2442552110 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 398737401 1250 398736151 398736179
    0x190e1e12160c170606030d110606012d050415030912121d1b0406120201120603080a0203121f0506030403031d010b0103060e1e150301051005101701 65
    0x8942c0901c5026001c00e2611048480e11950260840200320300d00d0038905050034030600f01e001a003030120f140c83c8817100c903c020401c0d035403161080c80c00a46035120301c0000c01d9070380c404d101404150104440d0304061182d1107001030050358a154441a80a8602082103040394030703c1e00050411402c0150072110b461062607044042d100b4043e01080004041100010f01c1d000c055000c46158020001c0b141d4000b41482c140305007090031101004054030700a001d05129004a40c02410010000c1c00b802c1e840b0915401200030b59000008a80c450611a038080d6884d80520200e4401501420014044036290212440150220480c0d40e131021b103000b0620029800144c0100d05040e100d02d00c60255040c440d6040207a440104000b150038a880ca00160468055070000d0690300c006030200214030710342d102454414403000340000c035996900341d2004103644601c41c14507030650812003404520710000800b0001c0c1c440480d00c43c041c0780d01070726040d42d0b07440d41d80481001ca0b0203c11b0041022214400b80 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 398738651 1250 398737401 398737403
    0x1315050a270905060a0b0108090a110f01051e040f0902030106140d0b120d090617070c0807060504030801030213020901080f0711150901180c0905190e1e1216 69
    0x412031034002c3e07032550704101003103d18418240d0b8420b098140c079a44079402c142c100c5400c130050003000c800c0c3c0c0c4602503e030003040004c501900412181c0ca5280c0d10410488200594021581c551002000401075040e406480344882c3d148081c1c1011881c0c10281c4201d0f412188640c442e400324440740321000b0750b590040034007090b1841d42c82d42d85540585038241c2c46101110340c01701070808078000500190540c42c1680215080200282d2070b800302da07074500c04a03600615a420849d1807084945850700c8144110030b0700030300d400e0030242400109a000300109060b41e108641c80e4041005802c0c80a08070701866107020300040328031000c25035112407502f0707540d08003040e403030003001e45c0300c004154500e031016400d03000b600302c12031008200d01032400b0302c5440b090400103688550034540c1031700c07104041c01d40d50045031005c41d40c0b00302007040910265a00d0000000f8000144041c8480060f92a1100783d070311020000c210b00100e424081182c0401c0909a02010101ea60700305445107003031195204400c00 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 398739901 1250 398738651 398738729
    0x80d08010e060120010c110c150c03040f17210304060b0f03010e06060f090610110309042406020d091206110c061803041203030506010e1315050a 64
    0x214030302808010313041800e5000d01d038001140e501004a0010001a507409178050a5082052032841994981e0340c14049040d020041c603441d5038445c0c3c483c600318441e0303078000480180e182030001419040c10398ae021a01c030a25040e52641041d044041445038640611003010510410000e00002da030f0ba1701c02d224a0f0710142a01441c2100310020900715a80d0004618113507000404010301072412100c0d00340707605419120302100d03081110100d851032105041541c01e200041c07074800207140041065503030781000140b042c0b201180c2641107640e02c0000402d4000354a20003c000300b02a1b00014800f512070342142c4c0e0300c0032400d01e0440d001a0307046010004940154992460310300c2c1c001c002000c1c016440302240030744100c0c2803500444181c0300c0805540d1031942c01c1880208190350607120b60703002154060402090603691100121802c61104091a900c42c140005074031032001d031580401e581c004c00ca00d01c6001c95494804010301480c0714821102211001d205126144000d0a521008215505 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 398741007 1106 398739901 398739917
    0x50114091303051b0114130501050702150601030213090c050408070f08151807030302010f0b010509030a0210120203041b0e130b19021801020106080d08010e0601 71
    0x241941c000c0b1402c18402203540c10007904001c10380c1b800070071007045a142c05609054181205503040d54150f1030800020000c1d4000210803003200c8070980184203994440300114007030740c0002800480085040300020701d00320b46014492001100341c68854641e810202081c0ca001c071107900040d540058280104214280401d040d40c0305e00305490b49094582d1204030704007214582e54021070003031140c600000701f4541d041d80020b801c48a410300c1403144071a00c070011070301e900400302170b190302d038019401403401880d0280b02e0900e05841c0e414200400442802c04c0002c03604101c42c02c0e110269100081c942c101c0c0c03080004009081101300306500ca04080201038226419140010203032903140e0003003100d0b603200322541500e48848103400e540e0f404251000c0c1400500f803814441c09903007801030210340741101246c4024400c43e07950760914540e10b40210001a20405000719042c807a0f49 = true := by decide +kernel

theorem cover : BRFrame.Cov 398561151 398741007 := by
  have h0 := BRFrame.cov_init 398561151
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 398561151 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 398561151 ≤ n) (h2 : n < 398741007) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
