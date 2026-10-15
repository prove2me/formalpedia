-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5279
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:20:33.234196+00:00
-- url     : https://prove2.me/submissions/09665ab5-8eb3-4e8c-bde8-eb69a2660cbe

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 949280575 ≤ n < 949460431 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 949281825 1250 949280575 949280581
    0x21005010302060d050601020c1915210c0509040e0c01081008030f030a0912090816150302030615030907050915060901080a02250b0f0702071502010e07061115010e 72
    0x810024100078221604600401090b0301040da1841449810100318ac613452081a19003282403034504500c030040428452031104001c1e01c0360941c0d1a001294011100100e80b44408900c101c071300d48102c41750b4541c41450711803810080b0a00141d110300c001c2c401c2e00c58036066102c0e004c4440d8900c00074422034296030700807c0030042d09a00a009507400c444180703008a80c4072019650040d1142d60090003c0020300b100c10704100599003005090480704059000600e52030500c000c800b030700055522003070f050580000c080340040e110580301070100b1160300070356a1603003800e180301c90b00ca501c030340f00d0681318090880104849880600d10801070f1480101503519201044c40151001080100100d441c80e90a0111192101d81200c0e000700d009400c034220301e00c01d000c5150480c0040340c0034013120b0040a030b0300f0070010a43d400003121000c1d2850041e43c40f04414401c0c0c1c04034054181c040ca901201d0040c03810001344a81c00580882c50300f003820302515403444481e140003000c0c10091207140320210b1140d003c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 949283075 1250 949281825 949281847
    0x40b1b041a071e020a1202030606040e0c12030a030f11030403140f0c01050115030e2e060b0702030f0316170d0e280201082e120302100501030206 64
    0x800081014005100e003440c9850300e8501d43c039000c440200d040040880e00920440c45d003410100040c5c0f1000c1c681c41148102c0e5008aa9900c500901d101d00556440c41500504038080040b0708080d00020026203040d41c10480392910381e0422901c003800310741800e079040c0030042540210403680c070207103601c10300b0342e030351520111180c0e61811601c0d441954100302c075902a100340401099248614000031886500d0440d8108054180441040400d072410041010400d070100e2103007010f010346801d00c1d10880c1f42011a91418040851000041c0d151000018680c6040806400518001c80a07105d0342c5282d15402c1d07889200c0c42480600200b010006100018100581c0c54905002c007500300d418081c0005112080b200f5812148495501c2030003040a10f010040656034031004014000000749410750020b8000780001d000351003160030900e0702d203406030014509600541c024451420781259035141800d4120002981500180604804c00a43c8500c601a0f0b9040740c0d400340c141450145180d80c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 949284325 1250 949283075 949283099
    0x50f03160315151202030f0414010f06090b15071505130206040b0711030f03250c3209130212120d06080d02032d03010608040b1b04 58
    0x414601419035504454244120611550001c3c00301c0203124012440e4200b405460354810106a0074030500400800442c015003108007074120b9844961480901c1244031401c0c05450005014009103182c5000043d10340c11a4000034a0018140d4850205034889a19001d15105070a009412a00181d0100c00c4c0e1400740d900c8a036001607600b0068080c0040d82d030000c0d07829031245d4400341400c600483d1060501150b00c800859158088000f0821241c034102842d4803401240004a0359105525440000400302028080010b600c1203510900315102d0410340d020000c810070f08541200d01448034a40400e1050171104238250080040340c6030b607101051483c40b1240c0b10012038001c00320150b800c13400c9408100030079a1101200f0860744541141075403200702c400f80d03400100d541d88000340502c60240c002c800c69030002c954003041108110340d9990840a002d0310441301002100c000000100d503a03005401034002d40c4140e005480707907181d007a5400782e011001c840d80780100108000812640d00a04 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 949285575 1250 949284325 949284361
    0x8070c05120301090c180e06060913020708032205070512100f0614040612020f030304030b0a05070e030c150307090915050a0e070e0405040c151e050f03 67
    0x5049450a04603000c1c0d08070141c000380e0240082c10b844990f15100a0f0300030102561141d40ca00541d0007a500d80380340d82c800a040900f07407030300503000003a00e030320f141e190340b1103d10380c801c2918000d555815541c075042080f94021500d84e000082501d003081e00c43d65a60394a14070790754000001304003075818481041030300c160001c1d002c0d00600c80c54003c54600122405442280e4400407000684da40c0382c10018000503c007010034034030940c50034000f8000d010980000d070101d943c041d150395026074000c0c00824036512803508003904070010038080004212075a00b00078820b0a00c0c1c0c0d5000d0440c44034a081c90340e03543e48408038a42c803a0340442504641500680038640c09096487c0944145682e8200341040301c0c0440042c0f22000c46101302031040b410b012040034000e1400112481407031a0a0f040103114400c0101090300c11078582000c01e00380310352122603038040c00c280d41c44000c100d000000041c1000e08042c04038004142d280c071204480501840564400110036009a0b00c0c603900d03010985245c01e110 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 949286825 1250 949285575 949285583
    0x11070b180301140f06041e090201020a0803150f060c0c090406060504061205011109130c0509060a031a090c30040b09010b041a01050702041d03090a1508070c 69
    0x38018005450740c00b400303a4044080d03401803886480c10041110108841c1c0200041e0045007403103880d42001e00481d50000071188441c0d0001002442440101c8c1805088580540b40d0380012081c003130581c01c80c60305103158050448143c01d600c520041840414001d4100c3c05086030000c2040c8070313031414540121a8001d01c0341800007020368590703001400701e9016412841d004c5841c0c07030100041110074401c0600c20994295070a0030b20302d6100008000e01c03180342078144801e8036000c255040c64040c8041e6480464024a456200c3c5e4144c0801001441c682401110031120300c40700c1c000c1420b010050740d0084d400901c2c20352a001c607110000e40182c1039007407c1c0c004141f981d00c03c1c04090704040c5c4800c1c0100d12590000103d0304204d09102c0c00d48100c105101c0c030480c03501c4400850001e4208508031800740078204030352101000d000141c000d20314400014840086070900880d00400800100300c0e03d10304403241c41040d030300c07001484039140c81e0003030035008200032402042c0414028550b0000c0244a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 949288075 1250 949286825 949286857
    0x100504120606320402030f061c082b050903030721050c070203060f0124050c0714010f020307022b05030a020c040501061e051309020c03090a0611070b 66
    0x80c480030b609200c2e0003140480d0008200c60903000e90f0005a40700b40507580c80c100e600b941142042c80c4c0000c5d111340d018008504c12106000540b4040650182c10510781e81c1004000b6240d403007031407102c022459049001d0b01201c0708140d400d1079108403131090718081e00d0304000950869491140546260058202c40e141c101c06096001440351220b0043c2807240c01c0380d03024a07455031860300c140b52800c040078040b04070400003080144a03000075810030240f9807484869600d41d017001c0b075509841d1445203c0503040c0311b000711180442d038851603011881c05041c003aa00e441101c002d180b0304903124061424001d500c0b440b02d59141040c16030013007205083c81022400062070350301035980c040c07035540801c5a500c003503000800004078070728080c0304150040846003015104000c225000840030754603040c0250601101007030020080e0f0030b12900314003620100038110354558500031280d6503500500d540a22071041c40d6400708410b41708159440d0358410b03020040040a0030160245281d40105001c0508000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 949289325 1250 949288075 949288079
    0x315010f0908061e0c16060b011e090810060609051203220f060804030f0c1410051603060609030305090f1509040c1b1b0b19020606100504120606 64
    0xa8103002030303809218003600d40454640b0546128403601c0e00240048107000e02030002440340c65240c3c08041b1015440040080c1003096940165024400d5404224036501810282040706d0342140f6014151462101214032081a40c9100000d441c2130303010304000503000701030070841070170607801541085e0041401d903820600f21b402840c040c0c10301b0070048128440360300da0420900c180003a0080280440b4580501c107490680c8010789148045810b500800ca0f04805a02c10320060740c1000c0d102400010170345401084a42400703000c1d200c2035811013a40501c002400014a0091264000311001e9490f103640b00d41c6151425696600002034158016140c1038680d100d950324241e10002e80c400314956031707448040d0b0070103000898024001800c1403001c1408402c540400c25030390508000e0b8005040c1213909c454030b00030210041d45502c107034450368010550903100038100440f01085404d913421100d2564400702009490b100020b82c110204004000a000b003940d0b004039854454060b00001c21700c1c80d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 949290575 1250 949289325 949289339
    0x3071d01140f120c03041205132d1805150109050904060209090709140d3f020304080f19030e030102090a080c040b091b0c101a0f060315010f09 63
    0x7001300d900c2c1c02d95020000070003040180c0b240d181103072002c3da03280141c204107050300903c0c2900e10a019180b085e031600d986003450110410792400c40c4040c4007134940c0c0c00300c0e910507090412159004400600310b0030170000600e0404001124480010140d4408503a185820203200e5a01d0018109403a000d1f002c015050301ca446042806000740320b03507270311800030520b400c0401c5140f90070404444d1144585403411408140301c42c8113000c0c04104888140c4040c004c118080c0344070140500c007030488001c030282d541091074020029008031259541038801d461250038529882e03003982c0100f054001a000c05e00004a40703c0c0c2e00c0004c0c4e2440280c0010b113004401d20000d00c181038264808000d907401407000004a04290207210594001035500c00494241240701c0f1400d1407081600b40d05442010480e10b9810404100000c5d1100c83ca0204010100502c940c1c540455910600c09008a02c00c0008109600f09801200d1154010b100340e030001d100403c00444590040e201110100501841c0c0880c03c8 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 949291825 1250 949290575 949290607
    0x307090504030507120315090b030304080a06060e010e040f11180406050a0c0c0f02130b120127021f050409060e0a0612030f0503270303071d01140f 65
    0xc1d0b40a9107803141c88002c2441d0080c002d50b0f82c01c26100400d400d07c3c104507814146503150006603090342201003108040c14000c0b9183d8003599206520b1803254600e1401400308581c003460582d044d49000f0030182e80ca601103442d002a0035100203112505400c69100414031f66842c011001030024031030041e22550740200350b00342100703807015298155200c1c01e000300c2642520030000601c18a05141010000039110f02c000b04070240000303405101d10010040910000d603006890440c00207290840c0c07007030200b0806000307201800366810b90314080d0718075011060840d80c0111361203500800c0400c4140311480760343c03016680b03141c910042c00400e100100ea6182c40d0b01441c00a06031480350f410303151620181840036500c059019407980180c3d80307100303c003095020805504491041c1816035a07503d52021040800024140c00c01620040c0703034448c580c5030070110046008490690b100c0c01640740810001001441c04006180410780342c040300140ac2c440840036112080c100c01c07499003040d014844540c00 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 949293075 1250 949291825 949291831
    0xc0724020301091406030d0905040e01060503011b180e040204020d140c0c0114011d10030203100b0906120601150c050607080f09030309070e040206090d030f030b12070303080603070905 81
    0x110700d8a40d15101130843c02c1100342ca40c4440120020151414182030150183c603080c00f4040c0140c4d00d40f1030401c01103e094005100814014008100e840805040d0759041610342181c100000d4882c0fa06952429411756080203460916101100c1031b02c031542004001d5104002c40350303142d5103581e004003a8400f0304070020b00c1058021099561860058106c41c00c491030070b03550b00700c2082502c3c01403000074a10400c0391450b49214940c00c0ea113490780d6100d034428458907440294180300d46594003100001e290445403100788250f65206464036803100f0004090f0903011003501d194000c070010041640303890203140949031242028118041c064840f18204001203134907e0100e0000c01c02e118400c601c060245078808040d03800355065040c04110161204040d114003503801d00302401050640d501d007001c6070f00300c40004015240c01102464003802c020000d0a03c1c0002c640341100ba8061030034040505810806424080c0100c83d055a038143c0e0300070000752525801d03100c0d500010400340741922500380 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 949294325 1250 949293075 949293089
    0x603060b030c07260c1e06070804170313031407030c02041a06030a050f07080c07110f1809060612030715150b4603110a1808060c0724020301 62
    0x1551783c50f42d00e0701c540303006040c460b10740310010b0250780509410307030224a0030b800c80f81620707062000d52210704012a0341ea1000048503901c0400106004241c51480144490745121740c0700d0b2018a03001d520410401c5c0101c040250204c1c0c0014007000061405034058080c1c458903a50140004030000040b810350342046039003940042c0c1e03810500039040310202145912690500e4005560303d031072251080c05000314a00144064000520a0b200b65905486008044c1e0041c00405812141c2440c0c54040e00d019111102103004600210725142044a000010501c02c04011840d2455a64951130301000e0b015038681d980e661055101525400013010301e00501e061403401c2c1d100d491000900d44514481024800d00c10b2807410140c026180700c03901201203d20138412100c02a107403c2c7c068001d80350340301d410500204002071180e01c4a0300401501182d6100d030940c021b803142c0710744505644440540e04051806001d20030702c400569903104c1c10004c14140c035907094031208127540722816a002070700a11 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 949295575 1250 949294325 949294327
    0xb0a0806072f0a0b0c0a211404030302190807050a0e1201060303080a14100e06010c1b06021e0309090a0618020703081501080a0b06070f12090603060b030c0726 70
    0x4000d00000c06449174100e1003001c10140b034046482e0025141030703400f11056131415030f000110004000300c0d9003d42c001620003401003a07140741c00d2400500a503c24050350080441e2890340e282664829440c15110344113030380741d152408c1d01c41581510450a05526998031100c507662291012200b8000d00c1c000350320030348500e041d0f0709214803400c090f0390305252242618100c2c0c80403c055480300c8244042120308000c41d419140e2039402c0101c402c41c0240e40040c0100528600c141c20016929400d0380844542c0d600341d424040f0035503000f9555010215a8000e142e106215081d003602d484041e1a400c030031030f90400245141c2d84c100720100184000d020660303055000c18100185904101001c0d071008541075008400880000040c0c000c60018091003803142c0c1c0d81c130851005807102021904003070b810440c004003541451034010745010510149000140c202e0310b00181289c040c1c01031303030207440c04842051305560f2000c442c150280c011a906407507480c051031080740404801110202e01801c010802 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 949296825 1250 949295575 949295593
    0x6050a0c050f030a20060402030d080408120f060f04050606070219080a0303050f0c160b0a021201030b011a1602060a122a110a0f0f0c0b0d0b0a0806072f 67
    0x5c1d0701d42c00ba401d0b455035590046010440140e9000c00c00481c00001c1b818040c50340e0b20b40c1c1c10401c119001d86c01100100d6880c00007803103285403024202a00c03407403044a90f442807206202c1400140d50782076030025000842448443e0041c0741003810500c1c02101c022803040801c0d914245645009013520080d0f01080c0d49505212204200110196206a6840c03d0754906a01c03450720400524001c1c2001d007941040c00c0100310001903030380488081030410040d03104c1c1d65840e030078101030a60b0280705900c07032101100428028611400180c8400c42c544c104240ca5802c440d80038020340303034080a00d0004022491016981d41ca903103200314043c00c00000c0d0359042a1144c40c403002c4d000c00c1007100800500003d2603140d0070715440010080d0b6455841807100b2000c03140c529040304207048400f4010003003480786030b0100d1400600e2001c1e0082820f00c0e5800d02c4100701c1c079030a00c008844c0b540513074100c13070b0081c400107080d06000340a0b0003240a40300da02041c18031042003006500501d204203400300c6070421250 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 949298075 1250 949296825 949296857
    0xb100302130b0906190e10120b01091a03270a1202010e0c0f1f0c061812180e090a05152503060324050a0606050a0c050f030a 55
    0x1a501030000c00b030b180b91401c1c101c031000071130a0080c94100e1217842c442c00c00303805013144181480c01c800d61020307148429410740b02202504d40104141901c41161405982e21955071080200508451a100c0000d0041102c889071040591008142e0300e070100d15004410300e40b42410034a60042c100320000b8041ca544a40317018183d15246142c4201168145804140710b1400032402c0714550b40111440600070b002e02c0f001c6070321140034a144210b26000813400558940d0054100010107218040400c0b01c4000d04c0c10448030240c0c5110007404c02041183c0d082f0505005460707a80310801c101207050245641c601a181c11810229403681143d00140399010802c001003002c81d10542c121103a50a580c6801d69092402e849082941080c9541d4480c40d0351606020783e00c00b40c041c54012030301540038180d00a800c010301d18a01c298020692600000a0403c5120700c04cac0815103600340e80b000d19250b0511003c0702c81881190043d5141e01400c00da80c1400310003080207016940450b2030f02941c800101d10 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 949299325 1250 949298075 949298107
    0x306050f04030e040923010605120a0305030a0c030e1e1014160c20101e050903010209040e0d09060f0e010c2102010902120a02180601030b100302 64
    0x21614030600980144000070307400410a2001d52415500010300d1013490500d291a2042c1c1d502140c00c2c202a490050603020041d04090305607141a030300c05030b511a140004507610214050064002078040c40070a40c41304441e0808900082a460081141e906c8607001d0350400d402000344c00700d0744800c4241c98000c402c050041601034505002c0c06c004106c80301c0006210650024624400c0140d0741c1ca20f42e081c98019817090a100c0e801903040110a801761940303417006108030360b015200d52030f0408205201885510b440c0001c140707000441c5444140000107440b2500714001070ac0d4955020301550649846603c10742c1d0b11100414000c10014151034000740c810480780d006035003001070034900d502c6e00d0b41c0c1181c2203200d182000e10300880400d02509049801c500f0749105441754010030100f141c5d0f0f0382c0d0705404c41004a402181c030b031404100d100c01c549581d2072401c00c00075000070b10213800c400d2801c10100490303802031040c100841d032500d1070000140700038143c24000e80402d50114941ca03044100103 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 949300575 1250 949299325 949299331
    0x908190c090204050904120c08030906040302120f0d050402060c01090308100504050601090e0901021e03060306090d0e0f040e0a031d0a0b07060209010e1201091106040303090b131a04030605 83
    0x15001c6142038103010101c0d801d40380c020805044a481c81e07c00e0308560744643c40b040c1490340c0020f40a9180d01f8003440480c0c80300022f0300c1c154018402c0030507144145141344c044070303041045400f030345107001449030b50b04c006044020401d03684441c05122074080210207000d130b000000d03c0380d600d0070307128603003c031030f004a007405038202c14003c5181200b000742e180d0300319445c54280c0b180d0941b803400380d030b0300d5040b0140a4484c1e0500c0007506810f91803000103445141c4003441c02440c0403410f4680c0c2ba0790f403024807075581d0f2104007807400043d1014450240d034100400b6100d55804d003d4404550101854882c92800c0c456403421000a04000d401120441b515400590b203418101c61a40903149400183d01c3c09002e81d00c0c01400861340003542c00341c103038000c16076406500400341541d05629440c041541c001c200c144000c1d01c00307042080381195036190030001c0310706583d0300d80c43c0d81d09000d09058a907422a000108003200d8220148230200369801c16103800f10301c0b10b281900315a87d403821450a801510406 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 949301825 1250 949300575 949300589
    0x10f0e1902061305031203190c0e0613030b0711071a07030e0607020301060810060e16050a050c0f100f3309090503030115090308030a0b010908190c 65
    0x10300405194040a00008060386030115150341e1680340901001510105a51185074540b04840003164811901006144036030180d000f00309581661381031000654024404050006042d020041505c3c41d14001070030342101001c2074000801c1e2030b83d88050210500b602c003413000c00da805262412841080082c0300192200d482a05c1d1070340e0200c076041499000c2c07400001c0c14002d00403035003810364551000380d480c200d070020001d005032503444106a8486c103010305114000d5041280109030190005195400381081c4800c240c40c0c0301c9000c20440780c9411031035045080000410515240500c10410b0140302d543d284090011440700072140422503019100350145282444d144c11074030410780e012610709070f042c80020248040c80b165101c03203540180d00300c1000d1070725201d100380500100002440c143c0e09010214085c40645401c15a035051551100520103282003001401c200780c20780003070780b44203818140704c030f0174580f074030005820500302902e8410a00d03901e601480c144001c0107241c1c0010420 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 949303075 1250 949301825 949301833
    0x1801020d0b0a080f03190516060b04050a06050307050603040f210909061410050f070c080c0102010608030a0e0f06040326030c0403020d110d0804060314070e0d031808010f0e 76
    0x588451329200e0080c200070781400d441e0185011401c90182003100c03129452034600642d83c400034904603000302550020340e401207182000050401646204802c19210002d005001d060b00d0072080100e2540003c104844070580d4614601c0050606500500c45074a00d0300307149110f508423030000304803555543c840180b2900301001000a00360a400130010840191110041243c1e0500150b4251040d004807140c04800005e8460034060002002c10030340e40b00030250340c5045c04600c0128242d40d490b00036111207410400c40420810701801d4200d0104da0060840c04c03000940f04c0004289800950042d20003801d26102da040f1743d0341500058010600500c03005046040c082d00020440c042d5000081c025403940100e0b4081c040c0c0c4c001d40200b013070300003800e451400d0b0032807600080b80d410521400c0b010070b09200350a14a061810003ca126046641d1215860310b8094100480503916142c00e8040c404101c0c010007440c181030312030390040d001c1c0d180045a84000c1605050440300c0010600700c1c1508 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 949304325 1250 949303075 949303093
    0x30a110909041103211e040e0f13020607120215070f030f0e01061203090b031b09131a0111030301030209011512060602160504050f06091801020d0b0a08 67
    0x15039020303402c1d00541c0145018640b1416040030178604404007203203254109000b04001c05504814004020301c42550300c4108444c24841c52031544c9002d2800340320044041c0600083c40c0740c0003141c0441e0322420030081e810441400d600452500e5200007000d17112848104208000250104501c002002001020085500d8845401485407403080500820542c681d0300314502c10035540c00c0020318440041c020403034250740d880c0d24070401c0820030040300401d03208000000d1105002003034922482100e03807201c0c000508201e000c0d019a0140700d4036580400312010b0481130481c0b61040120070755220800c4400d40200400141154086819811065100708014001a2280c0f111681100d05031056094403100485045d10620440d206042c91a443c20301c00041a0707a00141403d0061711048083c2e001c02c1c3c6601c00e005c281d03641201c558400345007800100324682007410750150311541d4005003010301c1e40b44203481800c0e41c0c40380300301c0090315444070704000d4149081150000100740b404000c0241034 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 949305575 1250 949304325 949304329
    0xc01021c020705090108060402120d1b0f05060a09050f0106060210052706070315120215130801090c08030c100b01020a02042406031e052208030a1109 66
    0x980c1400c400c800e605660825129101e00030000d2101424004180002d15030b100c0c140c081d5a48412030b01a4825206030101d06846540404c1030000c00155598031040700441d100104a48103001e9812100c0d00c40230300ca001c0204e08280b04840c002c82c804000880d51503c1402c00a182104200c0311303503456407407d841040821f40018124040341c4030488003003a1a5a0700c60b2404030340c9001140d03011010b400fa00c1407500c003603010448522842860310704100c954140c01942c00106201d005040c414600d80c10b1039005403412044040c03031010120105450881181280104001c403540f2480c496910758201404102200d50391002038141800250f00300f0b442409640c0c0e641480c03900300e582c0e1a90f9031600b010642d2082c05104001d607005041400013000503180095015221044000c0406450401140711442401642852112070891f02039416400002c000209805040030003070801ea403101c0c0c045110003004ea48043c50042c0076042d1203141a40d40c1e1025181581d0321082d850300b08000c03128540e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 949306825 1250 949305575 949305583
    0x604060f020a200c03010c080709060815041a0a0f061b0201050319021e04060e2e020f01090b01030201081e0703020a113408030d0b03161e080c0102 65
    0x200f080f094444600c1c4201080042c00c0c5001d07010020b80550900c480000c0e01504254107500a000070341d1317030b03810103559071104a560b5001038500c010554000c0343e44806500c0c3c00e8108801010b160300c00e5851000142c0000303100c07a8580d90000b00c0841c8000030401086822450320b00c9041034400f00914041c219500081140c800182260b903a0642a03e02d984440342540c150f4110920203821007c0060000c071280c001a0003c1c4140700020700c226800c200315042202c81d0702020b01d5440b065142c08000d00c0c0801e0300d106094410041144031f491404a41340c10240110301c03100e80200312036241541980001000458014030144006800c1d010f0029540000d58820760f01a07014500182c44402d0104c0c00c0744d59045100c07034444c03641b00fa10b010244d440d403501501c1c078080851b0b1003c542c84001c51b1000c072060810070710840d2a250020b110301c1c5903121498010741d0410310024291445554040c1c200314031020141c01c801030307007240078501402d00d0f01120411000b420020004180d801e5448000030341d1 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 949308075 1250 949306825 949306847
    0xe182d09030322081201090b04141909080403060e010605011115041e1a06030c06030a0b060f1308010b04020c0a12090f06081f03030219020102100e0604060f020a 71
    0x701d1021000400040707015524110081d44c4450211350fa80384a4005045814007030080c10b041c580b4021141c012458944141d802d1000c1b21a0055101d580b150340d450b19140800709054406501c030761500c40001c1c0ca00000b03002552080d140000c00c22040e43c1043d084034181d822050503c003502803a08030740f85000030446c104d4084e25070002803a0347d641ca0300c0e40102074030700c10510b4589102c0440c1d00421108600b9401700441100180c3d19036a5140100350307032840d2840d0496007001c410404921600d6864001c407002201c054503c900e4030a0510000e445640710003105e92004521103000e0111602c2030180f04220a400c60341542450718000c0e180351a00100e42c8000e20751781c500201c00c00c2c07940c00b44110000404d00019a801c0c52507503000064102c640c101c5802c02c403180044c0a020058001801d880d0079250554024000c1d844000e0391100d003c030003510140c0c154031490f10364218514090040580f03414505018100328105441c1800c1955100c9117141c2c441401881010000e42c0d00c0f20703592207 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 949309325 1250 949308075 949308091
    0x1605010e150c040b03070207270e01020a0518030a020603040b071b032c030106060507060b0a030c050607030c06022704060608150a09230c0403030c030e182d090303 72
    0xa41d1b40c0710200280d103000c00e07a5024152520039501d00c0c10049032864000c0b80d1991805000744100b00c500c0307103000c2c02c074429905000c0200f401030041e01044414540310100b104005003c0f209154203640018080742c000320f034216a2005041700304521281c1c0a50740742c0701041826604061202c00e980c02070b000e1134100441910004441c042e1a107000f0316145100d03016803020b002000010385031702c4000d26580c04038000741c0b540340c1001c540004a0801240c5401265004450252128140010002113a104c54000d408004001c43c242021074820310040c4509140d00f04c90800701060101603000d10006000d000740f00c1d5140c28030802c4110342081c103407a40000d58184003072941500d1400504602c03019041101c0543c035008082460094074592504680c1310056a42199500c15960b80024483c41c0402800550710f4103c00000034042c0b802c480140600400c1010b41d80510900003c1c079070307002c85a007130f65030030b2a0240400c11003110365a10308414541860f04081e14007120202ea42c2c0c070001d01901c0c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 949310575 1250 949309325 949309327
    0x60d0906180b3c1f03060203070212030402060d02220801020a030c052d1c0f0b0d1208040f020d050c040b010e031b240415090e06040e031605010e150c040b 68
    0x113120a5102e80c02460180c84812400410a890f03040400094108071442c5d80540f162000000c4065291002d580c4103d50080500d4500884194010b0103504490300503000c05000100e11040482c1c0700c036501c5c01810300c1a00051b2144031a140090a0703031003c040d41c40611204200c1c0181c40b981c49000c0d04142810403813224600340800240800912035005100e824911a648240b1800c600340c200c204014207110061185021040070860110700c8580c000f460410400810001c0318020380b58543d005004058031542c55000b41c011441010340c950080362a0b0300456809007041c542845204c4007040203203451804881880040307559072002c440c2c2c15480f080301c0311204805a4030f2800c03410220000c240c0c00c510340008680380100c075401502071401070b01200710110070410310402c40302c02118032900760030307595442d11420b0000502071000350303c0701c40c041006803d18543e915041c0b0040b880c402e034000203240c13050b44001d90600000184d0900807901000505c8100000203040da02501d00f034020503 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 949311825 1250 949310575 949310581
    0x105010c140708030a090e010509010e0103120e15070303061a0d0207060b0a0602070f06052107031407120f02210c0d1d0d0e060d0906180b3c 62
    0x1e20b251140c20f40c0401e140d40320008001c000d1030b61003505202210f260009840e0781d41d80f9203081000d900000d00460143c20044130041000c1424801c1d00712580b00c16092901a189159001c11500311100a03000f100b01c10015800d0304040e03140c441c0c1e6004003a182107064481c1c14058002e07086101e600e24640040d6004103410003407055a074003080210600030034051540e562142c3c06911801c83d0710920340d03d00140f9200081c2e190280080b500302c500f402c01c0c46184c0c884800840700c51450050180f4041541e00c48001103001e00000d0001d0107040240c89421034481c000715602c9c20760300414140070320075006022031040780e03e110f980780c491884c0c9110426203564648500c4502405011010483c00b07081c8906124100103182010320b0b141c80c4281030b64850913030310340c007510b041d40503020141e0009010444200c00c4840f551292038900e105000218003d008004090508901d00d603003039036000040b4081c003444c03803041c8000c6044141e9680300b8207030038005a281d04400a041e514481c11340300b000400 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 949313075 1250 949311825 949311863
    0x8030d0b01140c060f070c0231060605030109110408060408070f050615010e010810350f0c01140301060c1703040b0603060a0608030d0207050717030909070302030105010c 75
    0x4411110254140c090381c5030b002c07482e107a540e203500036500e00d1840040c80006ca40c0d42842905c00031102c980280113111015000792944000d00d60151050f44185000e2144440e08038540c003440005103000d0307441644079410a0040811150f03030401d841c440c030b9000c020070800700d40c011880c0e5500c550000f4000d61030305507600b41039044804801e801441400740b5030410032060300005890032603110030780e54540e0308107000c40103644c2030700280c991841418458600304807009031a50f08880c0302541072007084d40300104411b1583c075100b20411020b002d030040820380095030000c1100388400c0d902407801840300d00c1903942146040c8018096001006091092507003400501a015241c000d0072040469491402d070030642c0814a0649610b40b1a0280d200030a0703405403e401904183c8207000c0207586021940d94084000390f00c1050100d410b401960000241c800725040e06240c99040c8101450780c9112100070004c3c0c40301c00410b540c0600d441440148101d0b6400f1503241045640600f29285105031244 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 949314325 1250 949313075 949313087
    0xb07080c012f0a02102d0e070e130209071b0c1d010303080c0c120408030304020a0b0f040603180c06020604121b140c040501060302040906171f110a110c0a08030d0b01 73
    0x703e01281d6810b49403002201b21140d8000c002540d2101c040e164a141c94840d0060a000c003030750043d503202c62400303050700545010500160800c8190611584054004000e00c0c55003110200544844452070f8080044007a08084d151302405c1071140e1040d00d40c11641d0160080102420340d811851000c00d4258113a40c0410015106c24960340d0754944442e6600003442c0d4990040ba000c81c082c0d8101500014040c03410815169030310f031110341d1681010b082040850003020804c1c4400d040e8500250820f01052841001001411007540605080d1601d4142000700d03d400701c0401d4108141c200e150304c01900d0b24161281010f91140b1081440d03810402c107680f50200005000c0d500c58600400060042d802d903004008580301c2c00001d000040d030b24202c8040d4001b0b40312039459103400800405280380074040803074407501d0190400141e0160200081080381d0401c040010209298140c1240345000030001008407500450301c9840d0346c1d007051070250301e03401001c3e00702e1020303600c0702c942a00302ea000345 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 949315575 1250 949314325 949314371
    0xa030b0411070b1e0c1b010b0108070c031206090507110d020c100302190915050301030f020f130207120e121e011413021008100b07080c012f0a0210 65
    0x200400030600b864140d107031851b40b010402001c20541140c0602e0710240c11700030398240101c161581103441c0e4400005803003502403450704038100300b403128000d52070451030b01ca6007015064517407001482d03141c940001f41409002c0036410b40d00e13030300041107840d01035030002c0d80c0480304c84241d940c401c0d0401d90450a03800303401106111482480a441c4070340301564441402c4003101d0b000000f2001ca054034082c180d0f00c3d80b10a00000e085000300300b030040c0c09801c1401c183c010040e005056410301104000a4004a0b0080c0e001140e6500481c0072a90036580d010205031900b20044034104100c102c0700058a50305d40c10740d80c000500d0407003d101111240c00a511520003039221031094184c91410b803c00c2c40042e890210100e1107040d80c4181d03041d905128101c0e851241d112012400d01403800d058034100250017a403402c5400440401142d40300351350a000f140110b03402c1481d01c051050030543c150461406200c1ea598406d50180800e41800d9030010309024002100d1100007611402040c0e02d03480710400c5 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 949316825 1250 949315575 949315621
    0x1110111209120f2b020712030905060403060501051516030f1214060a09050f01030305090d06022a030a0e06030a09020a0303081603022a010603170a030b0411070b 71
    0x10800c621260000c68031444040326884d41405107401c201100c440c00e50070080700340050b40102403d0080b07119543e40c03004a18040d0911110b1260b0362030000d901c6a00c10381040390380c0380c1c8030001005142405800c010854281c02c0509080030241c0c0390715246120b04440260401c08004001d0744618020b00c5041c42d040901e00007480100b040914100000da42661160701441d0004000222103841d849414050915000000026440c40e01c085490750401321446030f10802c58420007001542903c000d100140e10b84030316240c001c05a40b0030101070018013903988115001000350102481d40000ba0403800f000444001e0b8898039250f55210091803011002500080c003090007005164101c561240326107000c5090708404141c207417085003640100c865502c0c0c10f1182c0c03020340303080145004d15011001921000050040e9881d00e51205544c9445c000310807500001441d04440e640c18000c541040d0420f4505008a031103c100204091241c500003412400505000c2454410307003002c01d8280bc0e0310 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 949318075 1250 949316825 949316833
    0x1202130b0f04150317210a1b031d0703120c0f0503040602330f07030209040603060f0606050f04031101020304030b0709141f05030a0b0d111011120912 66
    0x80049290f5040c2c603a8042a581021302c051034203038401031174044405900003180515000030b840c10903c80703820405446900c0440c0ca465a084041008280548542c1c80380d640200f40710880e032200f03c40f540c0e40568800c256400c000024030114000c000022004861031a1143c102e14075404c2052004c10380e07c10050150000241c00103a581d400a1100c0f05403072000e02144c0c1d0306e0300441d52074a40c022881c08c0740c06c2c03055160000695403046903140b41d50000c1d030381c01c002d1301d0309204200007000c80e155600121103c56076443e00c917a220100d403003400041c1005081861400800c400d00c810135000d070303110081031701809040004480e4400d1082d00e00450307014901d4030b07250070000c0d000351a034445401061800c0000c514980190729200301950b0b560f80c000d01104143c2488494112801d50008112803000d0703480300e10144031901e5410b003c0e0381b0280a0291000c0c40030342e1508010b40b0540841d0108100034200c01202c3d501000441d0b16880e0850701a0b0a50f0340d400107102051144c0d00c80759490b43c51f409 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 949319325 1250 949318075 949318091
    0x50603010b07060b060715020901030905061e090705130b0f0316090506010302091e030f0a1a0105010302040302060a030c0212031314010c0f110f071e1202130b0f04 72
    0x100c1c98000d010000c0c0709800601006040ca4207100c07543c002c40d003001c1d2003800d2403076865403204403c2d801060402010301d80492034101c140c5078940383c0701d000d941cae00000d60400f202c0086130350603a41ca010f400000b8140a0b00e0b0316031801c0e00140c204019214134000403a500c80800526a960b45100c1d0031030000075042c2c4051034020b0002c0c0d41c3d500350038403544040a0402000500700c0d0b10920131034610080042103040310102c281014400340181d4007250343c240c401d2500b07100e0030020410418078881e109015450b07031060240d404140f10481a40050305043c01070005000503035801080d41c45100180c600080c225020a41c22890700c00c0d4500d1000791030300004244005038904600c40b00c00c1c28001c0010481507640340803514200c3d80494051400520a0258421021700c074400c000b44601c02c2d00d080380c2c08201801c809908040c1c8a601c131020b130201e40192882400107104c03406006144905819228245c0e41e0040740c45035822503121074141780c2c0c5100e2040690345d094032010031110007620403c2051 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 949320575 1250 949319325 949319339
    0x31b2806020c06040501140d060317072001020a032a030915080709050d08040801020a0203091c03140a0c0f03030522050304150c050f1e060f0105060f0405060301 71
    0x42080c0100c0c40140940510300c0704a041400890702158010b079119007071069491005080394000b805140005502d6030030000210346180c29010403280801c1405544007114582002110009000e00c0c482030010078050700f0340d1380c011500307404140c0c146c209580040c19103010402141404035a0ba0f480c0c0741c002d00034000781984800c6610031780d0820207140b00c4201c440841601d0b82d0408848480005010341c40c24425410704803503502005120b03181e52820b2035155400380e03007680c1046411100690004c0341100c490702c2c0880c4075448070100380002c815841c02545004002075803804003440f540e00c0001d110290b0f503109a58945031242c0050104090001520300140a08415641d103440b032900220720400386100745441c0750600340e01ca40210310305441c0c11007401040c1c1309182c90606100140c208000892414003030000b0368214440540821240c14141c4004080d150446282a6200104001c50304504603005815a0411504c0917200e048041161103140f00ea50041c039000070300400001484 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 949321825 1250 949320575 949320649
    0x1401062d0903030f02030313140a060f0e0c010c12030525020a05121629010f0e0c091e28260a0605100e130b090606031b 53
    0x241e482035a44c0c400e0181d014404a84d00c1c0401d449184021521510040000702c030210f4000c0d049a01000b503840c170181e241c0b0382e840ac40f807520002d090040c0d2942c8410421403c02e0201c070211b40000d0a01800ba0a9240c9486106410b0010036406040d0b80710301003804c48480d01c584d59014051000d4105548a001d98000c1d103a1000b0001100d45112720100740a40c0c8601c4410350352903820340000c0d120f070612030f40c845500e00c50300d403602e07855a007207010072640c6040c1201d4452806440c0c40c40c00b00c00803cac07404000b040011001800c041100078240003035510703036803a01d91240b5100000d8503071050944410000418007161000c180e4030002c089454590070500000e8298200d0340200701601d4041021000c0c0c900d0f00e04414001c861a40141c0301a038002242c0e584800e4010000e41640b10010703480d4054026080b9003583e20050702a0b0420303066003001003054001c1c0d40200000d000e081c41d4200000402c0c4e44241c00b0600c00c26001d005000c0200603200c0c40703982c80b80c80b07100060311020000c000b1550802 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 949323075 1250 949321825 949321829
    0x91e0204140a0e07050d02180d050d0905030d050f1b0105150a050d02241c021818011a090301020307030b13020c0d030504030509090103050c0f03011401062d09 70
    0x251642c1d070000184052481e031403e105403019181d041c500101c0c190124003c0d841080c407400307503d2884c010341d03460f500c5000d210a45580306e04001c018440b00c0c441d01401610059115500c60b0b0700c0b444100c10035503071007802c1e0b44941e01025111600c0c0d10215030068480b000c1d03e210702e002c542c0781c4820040c0740d20341039951921658040e0b40300e0345041e841710203105c004201008040e4000d018a8ec2e50b140c20b614404940d4425202c3c807083c80d083c01a4425000c6107150464080c80c0324036004103400c1e00d15941503520303d501000444024440452002107042c0708a0148100902c05c900360101070502c07016403084544600c0002c0c0210743d00d280c84100500100303030020030180908038402c201583c1240034070848501c00a40c6000b0300c58a001020110050400104110204901030000140303d444030a10140070718803e001074072000e0320007401c0c011014401c1000310320a03030512000b000760708600d201c038905407055840d2103400004103412500f00000c031080e4604030866251514459030340d110383c1c0441 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 949324325 1250 949323075 949323079
    0x715111905120f09070f0806100b090a0302060a0203160633150c0f06050a0c090303050d0203061c05010f0510030b06010e04110d1b0315091e020414 65
    0x10000c1140c0c0031a5030340603042c40b45403882078202c040340c041000301c020107034040190001c40345403075281d0b88010001c5601d5807092003154000c000b0300c101144880c284030b01810302c480d10541004401d800081d1b82000610010b03000703810000748903080c50f10a00844038841c0d4507122513520740500e454540014000007003100d54801e02c00410a2810564034904000b5034081c1682e503504034204581d903122a07005140322018084403105110006048003d072501c03ca0103040009800c0c500400744c081610300100c00e8038104100303200e003400000d03041015610b510070890b000680b40e80d141804552003c0404503010f6072030241d03200340400c1103015042058591140e81007444261213050040300440340c1c502004104007114800124294404c0381c1c28040365200501c08074900c5040b05040805900240c40c2e0100e103a00c44901c680502000076000d1407010084c54100b080c0450404540312200d80780c00703450700704c90f00c4801c005080310800d100301411027243c0a046554070b0b0381e108218100c2c164850f441d8 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 949325575 1250 949324325 949324357
    0x103050618071809150f09050106140c070510020a11100c03120b06041710020313020111150108010903020c0a0602151305100507110c010f112505030f030a05040902071511 75
    0x704410350503008d00e40c106d03801500d408003080300c568199142504072a10003207942c414840001415070341c2102c050030440c8143c01400d100c403124100443c0c140322200016008444210480300456403100385108456090701d003038000100d4070850100500350f28160a5401030000c50082180c80c11100c6d4284104955001c64444d804181c000c90282c1c0411a109010350100c0d140841c0554003648a0188440080d4286d0b44840c403ca6041c52407000f003038100f01d50f90785d0b4801e000300825404000d0500c3e513078400c907001000d05141c4030b0029540c4003075040c1b8542e55446440860f20004c14407038400c0080741c3c407406a0f076200ca0620b91150040c01c0c201c0340c030030020f919190300c1e09040d580490b18104515060395040421100230030107442c141d041d090010000d1140c1c0c0f044040008200c144c0a0741c130f2550a985c15140c503d44000c0500d03011040e04480000c2d041000f8500d00e50740c00c902141d0460301d410f031003d13032142002e0619401924440803e00d41c05400c100d040842c0c002c54500600d03d82c038001c1c90603 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 949326825 1250 949325575 949325579
    0x7060f1e0347030a0b18210d020711090c031933030b0702032701020c1509090405010212060315060f121f0c0e0109050909070510030203060103050618071809150f 71
    0x86100c4907c0d001d0401c0c40c1200800022640700d0542d0000c08105019480b995503c82c01c00307010400c07501007101c20808404021041c0100e42d484012514404075101c04284a681c10701008005808000b680f90380f0b00445003418904071004002c0c4403802140c00c210314880e140ba100c1c134080d4030ba51107007202c078864410740c89215130040c0958a40b06440301c01079009107901c000440501c481c190070707038800400c420401e00480809982d100c5403640708a00c103500241e114808040110180340001d802c007446900425072040c41c032000002c15a40c0400300300c5240d503051a0040201e082c828140900c00c00d00d008003280d042c510804c002c0302d00c11900d140c050030001190b44120817101035807140d512900041e0704640030800c40c5840800c00d81c000e1b49140c180d5180035910030000340580103440c00c07100480e4001c82041000c0d0f0701845000c0d4071610603100c40c007501000305000006850f005010209200102031640c141c03005480140740945214030003008180c9034520040400036413441a038900c00640240 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 949328075 1250 949326825 949326853
    0x9050d1e0308100501050c1b03100914010b06071e06090606030b0f060604060203180a15021e010b090109090c05270c0a0207060f1e0347030a0b18 64
    0x89609030340c499800b41c05c01e070040048140c2092301344082280d140c0316400c5400304d200140c2c840c0103145482000808811407035421000d003917070440013140d441400203200c031101003603404d540c011008441d07090249014a081c5004c000400e04940064606031400704040200660140c06500401600c2c1d0540c40c242c0e181e008124281c416402080010703081401106010390104480c80b00040c0002c00341c6180903240c002042d680d101c0c800c4080016030003100360140c0301c50b450945a50002c807900092001b0018000840d00350041031081040c180c0d5504240014014800310040183c400205134501035107400500c0300004004000c0030195148031000300718040f000004481c01c010094000e08091803a01d6070540781030810040c284e0600804901c80c070b21044581d0450b84070450705072000624403a00303d12203410680364000070210706000d100b01c841898804804020210a080c103030519180b400d81c003103814900c3d80c01000300881c66400070b001c1c1c00490201d0780c01d180703201c03203048a01908400c18 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 949329325 1250 949328075 949328077
    0x51503010f2a050706020a0e0a09020901211b0906020c0102011407050a09150503040303061e090b031006080d02240a0c030b0306161407020109050d1e030810050105 72
    0x1e5101291081e61032061a030011000d0000d5070b2412034203000d42401841c3c1ca910f0160f0b4003001c0d0b0040080c510780b44003801442c0031003980d00545059042181041c00c2d0308006401081c00700700710180c0c60300702080060014840c0e0000b0a04000403a01058408059400500250b010340541d0340035011b1800d00380c420754814864a03a40000510301c4142c1c0c0d40394030006a07200c0d408200003c080180c20301c00030030340e05104640410214010b03500c0b55524074041c24000c045400a0b004100701070201c403400030100d81c074041000261007400742c00040c40d02000e800240b40000c08203900381003505101c80044d981c0c90200741c152000105800303503090303002c0c400441d030340c1c0e00040d290038001e140442000c552010a150b000030126440c41c20005642c2d0003090003e450810701b191010070080724408440341d210b500024407840300c8a11440c0b1030500810740d00281108a281c0180741c068002d0351004010701c010320840320503400004000d034601d0240d5040040512000301d46425001d10103190000c1d041d4441c1e4 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 949330575 1250 949329325 949329341
    0x151d060d0f0c020d0c1703130203031603090f35010e010b0a150203030109090816080318010203070e01180f1e050d170c010e030324030d0f0f12051503010f 68
    0x10b00403c90a9442006c580000e404003c18003d0704044100589080005000f4006030400300c804000d40c40c80d0082003d81070b500400c261940042040001d1040c021020541c00c0030009481041c0b010b40c4800300601c0e00c22081210340c4c1d820290603494000c01984400402001a00c2840301d00c0e40b9104980501d034040c00019005038820001004107200c1a80480f44a41c481d4581d2840c10b00000d24241941c480c41d40c5c16110204000180440c0c40145000502c0010ba075000035070451620a00c05400807004086071410b00c0082c1c1c02c1e0f0084440c1c0360624501800355070400004007901c0e2400070f10301401c0458408041c3c0c840090101e95490150f800c031a445500c20000514840c910a00c664150071584100b00c1540d00e41880c0c440c0302400740f000e18031880740909030714040c2940044034200382880d511024041e03004040c401040d1b503401385881d8210b0000342040661300c0e904a400300c4591550030398405031140342c9003d000502c0340d410755022070120210000c0c8002c4030b100b0a40803c40e40380ea = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 949331825 1250 949330575 949330583
    0x90311031305270c071104060905070f0807090b07051e06011802030f010306241710090507090507050c0a05030901120c080a0b010504080109051501151d060d0f0c020d0c 74
    0x1d8000102d406040c40c3c0204032640c8161b1100c010072510101003415500b50303400400c01d59480703408000480790320101c142c0c9002171038134020202d0304003400302500b050094061780c00140d50005002040c040100001caa207840c010200a6146142c01c9800d921008280600c2c03440d103486070401e40d6546803a0080c0c034018040c160200007540d18550b0780100a100007200110440c80b080e602c01400c00c48145c0e100018038002400c66223240d03a2055403030a00c1395a03c40360099034600b0f42c4034008646c000405105890b129000004e0503101d4440540e1140146030004c0424070808000c0030401601001500e4880c1003030321105901c100c1d184d810402c0d1b9810f04843e0001a00d20b10011b401c01000c0c0d04011021881030404501d0113450301446400d4941e2004181c82031307480700600c0301d50f040c1c0900c3c41c28014402914420400644240001c00b810342d6400d07070048000e140c000515031640e4200441d043e0343c02d0000100300c2000c40c2d510440c0901078100c055400b6000d500c104802d400d000f00500008c0ba540 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 949333075 1250 949331825 949331899
    0x31008070e010810230f06040e010618020d0209091801050c0903030a030b04020f1303020a0608060102190c050d120305010603020a02030703030f020d020c070e010522090311031305 79
    0x8580100c0001c004c001124103848400b01103200403540e0580000707000b41818802c110091520b501480140c2740b10030b003079201503072600c00e082003084c0b0340c1e1aa441e0424245c0c1405640c801124048002030b004080225520100c004c040c41000c16069140c440c0f4100ba0340003d00035941c03041d0715a54980038000255806820822000c14020700c240d004540160001b00014100082c03001040842e8000415401058821200510545c0340c10084040241403e1404c0c002034075001c00000c2d12001c03060041038105c024016031000f0800400c40f850007070300c0050070b40250041c1605182200f06056400800440d145c003002140d41d500ca13008072101d64200d50001c1d45000380a035012401090024610852141d080c0044e190004540c0020202100c03003000514020b404d00c00302e0380c168172069001c54803440c41c904444007180d540c070f0794000040d00c0300c2500058070010f5080070746132469181b9012405010004003020042501645801a6003007034803044031600714210203050802d4050195820150 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 949334325 1250 949333075 949333093
    0x907090b07110f060a270f03080304020d0819030f0c02030a260f1f141e060a2a020a05120f011b030c140742111e0901050f031008070e0108 61
    0x49d404e001560090710103462000171218545840e226a000040c0030740403a007440702d00119a0794540146a01c58001d020200111041524003956034803a12407140180044d075030742c040c0c0c0d201014015107040c80600e640480c080c645207a006000420071600200807185410f1140c6019070010141c0050300e80d5407407500c145551000400010350b540c1c00c0da5035007014001c3d5850946450384c0002e001ea42ea20341d2241c0040e0454070646895014a0804400b80040d5000260001d03079210241101114010783c2d9006803111402800ca0405003203c0125181e582005401001900274008006901c841623408110a200005048900103440d2990036614442404480c01007036010956400c078804440c0103e8140c10010134a5283da03400021101c9144081444000040070602410210303400c80c001e1145049061004d41d0342140705000d8051211502068100890340250b04441d8804c03030240e0000c0c1c4915007013244100310803032800795811500481400140c0c40c14089400d0b81a5070100e006025444 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 949335575 1250 949334325 949334333
    0x3070b0705031f0e0f0c1903020702040b03250801091106031e0106050408061b1206131e110a0203031506040e04060b0907090b07110f060a270f03 64
    0x703000500325460074502010080030f280089a81c100041103842404511807600c00407001400030010140900c55108124211502c0c00241003201d160b0b90078240140c43c0c051500100d402484850740311364061244401d41101d08205000450b0002182d008074510191503031f078014284c0b2100a001004da404d0900070389060310741580a1039014107031510160343c120300c81002d81a42042a40120003142c8009001e200104003403004540c440c1c101c0001500b0074040304244541842075010422065600c240440c0d41982d48411002c03103481c1305101445200c007030100003040d1100c109249109030b4608558007040001c040241e80c10703400e030b58004e50306594910003543ca250b040c1c1510039a1003501007001141403000c500340d460066000c0c0c04002102c0c441202442255000a8056400e104d0a68400c10000c0c91030030403201201e42c0030600b80d0fa40d22509000c91800001802e20719404807020440c0001c540e8415060744600318840c0e00301d0034182c254500d452419601c0e01a282c00d5026110040c400300b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 949336825 1250 949335575 949335577
    0x2030d090809090f090d090b04060305070e03010f020a02010e0705060909040c08030d2f03360a030206010902070f0803070c0204091101091e0e070207080d080604060803070b0705 78
    0x350107100c41d1858000e5220008080280858580c0030300c0000720144490484204414a2041c501d8109650b50605003050070071140514450b10b0101516140000c001c2846164095501d80001c0c0c000d1002c1070300c00f9001400384d00100c18040041d031809503c141a50f1000030107000303c4001034081341c60085000c05105c00c0e48030080080e2407240302e030382000401e05020001401140700b404000214107030319040e004501005a92605074603c0e13440c130b919506201050403240c00c600c3e0520802d2100b541003a240340c02d500d40040502d01c4140e4080180c1c600400030031a613003254030036401c1e0341e0180c1e00c0e503256038100d000b41440a000880307040d03000000104080010b6400401c181085044010303140d00090550700c0090341290323002462034003c01107507007050b401000f0303004903180c400160000b400c00c000c0b00d4145208940b022100e035400305121324000d100c0c84e80030380307104070503102c0c05100601c002e029545d017991a18016841d043c8005610710006c0207072081d0540c8503403c103185848803402110380d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 949338075 1250 949336825 949336841
    0x9050d0f1d010c050f0303100311010e0102061603090218100e1005060d0b1e0102010518151e010303050a12060305060601080c0c010216050607030902150a0210021204060b010f02030d 80
    0x305120700d0100c1d1410681c10001f0390b11800f0442c003a40a820b040d494144019a080700d08607041c01902001c1da04581c0c1c0215a041e44103482d511501078410f180e0380100c2c0a01101403010390048400902c2040402c0c82e00307071092054039a55218103a003503541120343c052807011901c0f03007007903480008203200718600103000f404040301c02d40001c100604000000750000444580031200003a4030004040e00d56028018250f0194100e4202070300c480d1154103d03074880341e918403211640003515001a030500c0d07046144003040107540d44406400e41e1a40350181403544805810400700e42c0c00460000c1f000050b005481c1626440400341003203449141c01900c4072000030748040d200c2c03101401000b041010905c06000c103203501c8c82800e284601035060650810310041c19400030141020f000e000513841c0c0b030081130600c1c5084400c00c0d564440c4410104d0402d030300107499414107400001c1480364054103845d8a4059030140c04100400c1c6480e2006540c1c448024801c0300c0913070424010b6207044807440d40800c031 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 949339325 1250 949338075 949338083
    0x23010503120f0d060b0702030c010203130306050c0d0c020a0521070b070306051f140408030f0f130e0603061e0a09080717030118021309050a0207050109050d0f1d010c 73
    0x10070201900503e4040d6081c43c0c00142600340c000c90001c044d450200300d00a08210b00f800a1480d02c00352107240e890004840c00054101602c41c00812400d04541003100c040c079000110803c485004104000c0d1100c00c5510241c0d0790703203d1382c03580720305200962510f00c1c41c03400b000b18024a042850742d210f01d4041c2004140ca810f1540c2e54800003010749650a50a0120803110f41e4500340c6a4031003805004614030070100701d00031a0031711051101c1d220010803a103401c2c140321942900c503034000c1020f80b200d10035840c248c042c0b0910460000b030a101c120704150302548003102980c4a640c2c1d1085071a451400100200050008040c04030b01d281c59a98452805c0902403032815250075080d0300c2c0d826520941d80c0c1d2030b01b00c1c1c4000000401000644424461103581641029403804400441c2e21003580501e0103110001e550341c0f408607401000540c112800f141d030100c000e01680b105800c010391102020002c902c04650320060502c03500e403044806400b050110b40d01d400024000c200111010309001104036 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 949340575 1250 949339325 949339327
    0x50108250506030c03011e0605181210060f06050306030a0201030b03120d0f0b100f0f1b0c0501110a05030706110c011a090601030e060c090a0e013201080406050c04050604060323010503120f 83
    0x14110881030002c801003d0154330081110341c1740180f82000c0001c2c541c070000401c282403061007501d603004103c80010790380900e408908283d02d88006070601016004000102000003a0501105106d80048400c0007006030200002c0400302c2c00d000e410301c40d03000c0d1480002c50b0f0107401e0490901900c00d5030340145144c40c0048050b0159000302d401c514501c174054401540650741000380e5039010550020214400c80944450340c0a40e0b5003542d0b0b400344442c001e245544880145010040701c5080d50501d04681000b40010001452000542c080001c5490300604414001948a501a00604820099180013400f207556004465960f9802c0101801d5010122040004030502d03100401c40c0130381710406072103d40d841c030415500c2c0030400c0c2004900080011002c0b0132050303a0490601c0358020342040300800c0513039494103800c23400e20590300170a51004001c01c2c00715a040d416400701000d902204039070010054a1550178010792000d2040c0341e4550f02c890003103041201c1d00c2014240c9045d00030711b01d0b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 949341825 1250 949340575 949340599
    0xb04060621050c0c030f0405030601051203030f0601030906020d0504050607110a0807020d3201060e01170f2d0a0503091302090d0b0910050108250506030c03011e060518 74
    0x1c0d17003903521110b64024000404181400a440c09011360703801040c08a5480c0300e040d08501e02c1d19124000180034154a42c10000041c2859005e900004102070b4080c1046503078084040b18180108010b640c20380e03252103480c0004990b0b40c01042c1851218030ad0384020202e40c1c0c4140c0c0d070306809600c81401240c10800740910000000c0c00607007510781d40b03600a213030307008290906282e440b02800c01120b688070b00e0f03052213000c01100340d50b203e00c24151401910f2901507d113220310745510b4141d6034016000c00e0b10600128003851106d50309a1144814048801d502400803c003005544061020000d003413500304100404852034616101d41d10613035041005404d10f100704c0002030041c03003000c40036a180ea8820b010025425402c0c002040c1d40d045070f200800095043c001015560348802c110f00100800d4034450036400e0703640c92000c4000b04001000300b80e90385006040035407107410038443c00103945242c400080017116001d00314420f80d41503540311400c04485440e102500081c510100350015020b01c60 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 949343075 1250 949341825 949341847
    0x150f04090807150b030607030903050d0902030313080c0a2c070c0501091a130c15091a0a0221030a090c03050a03020d0e0d050606040e19060b04060621050c 68
    0x100001140ca048000b03000300b04c1400341401c1c450b00804003000c05241c55941c200280d0024282c0340402140350000803241820310109141d480f5032561310380302c5041e40c1c100141103100018116042c54007a02d030140c1c607136603e100c1030a080e84200020400e0741c1000e0a01d9180e104501c2800d42d100f145403910404055290f107a283c210f8a0550007507409400950740c051040c5a45490349030000f407201c1c6850104945500c035048080032600466140b407143c0038160941912410f1081c0c080c0044040d901d40f81d0b00b160683c24030750f80c03003500d4103c0940074258101070718030780080503c656011541502d500e181d603610712500060043c04002c40c1d20851401c000f00100e80100040f1404074403940061108241255020304440116400f442c402d000345401c2e0400078201090940d08010141e4001c10f600050030340e20b508042040740396a09a0400c00810302c01d2100c01d0f000018500310507201040f01c161100411284403418104100c002114007500c444003003480e501050f80004030000042c01c103512140 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 949344325 1250 949343075 949343093
    0xa0f06030f050f06011202180702030d060e1006030c080c0c070911030a050903041401081e040f0c0902120c0a090801020a031d06010614130f060c0b150f04090807 71
    0xd4166683d070300c404801d00c0b201c0c404004050242150140100c9000156800240100b0101e803003904c00c83c00e15004280e00c14020400c2e50a04030046c80c4c04d2241540fa5180d41103007101c115451203020890410004056000e40724010300f030000d507508d01c0071655980041090380d6000025074651841400c0303001912410a101d810a0384070703c40e00c41640d07402d0038030349a0144c40002c1c0003407055810400c020401c805d04003d014140010030b0078100303000d0b500d046d100b240d6803040080c900c3c2d0700c00401c2d0401c4104210712402d04c540c1d41c800c0d041180d80b80e4913520401c04902070703500b1401100c0710b80c40200c1c4440d81500c0241a0303445c050311380310b049592070300c0c14207099070040301416010079114030341c058442d48500125222011890000c0074151314180c0010102030300c402e4121000c1d040000c2e003d80013503811b001c560145c4a4254020401aa100801411003000c804191000024000420105d000d03200d03485104100003004c612110f541141004000c010400041701e0000d0100700c65000507808131 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 949345575 1250 949344325 949344353
    0x212041403070818090a0b06031612020a03140a0e060408030901023c03060a0506030c04090c120c02060402010e091909080c06010e040c030b0a0b1306031b0e0a0f0603 73
    0x2084c0c0c01d50781e41003081402400e0710b000e031080a009041000c0008151100400d423a40107880c4940d6141d802c80c030704816039102004064141315180001034003114160990400142d4500c0620b00a01e207a9030b00d64454103c41207188002150b030064000305000c980440050f40d0801c0c107842c001841c05207841036907201c0c1103038284898205115a5074071001e84030b5242c1c80001840180d68ac080c51441c0c801c000800700001d81c091103104a4000c40400e0502425400b618080e03c1c0052040000d14131000b009010101420354461455040c102c00c1d0240720b1000c02e5041c01503a041c1c65103542070540300100190264014500c141c0000c2c4207146003c041600d020340b880240c0688985a96145a64081400c0c014142c0250380030b8218103003400002584180282d04603a080700501e0070649414042801074244440103903030005c3c2d506820110301e4031a6100c401200d201e204941092541005c0750000e005c3d09210745d582074000200041c2503c0d065800030344900d41c4c8100c000403110741300e03912008031003510 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 949346825 1250 949345575 949345597
    0x2070201141303081b100e1002070b0a0203090114040b1b0a052a16170601050a0b0702041103010315050603011a1c0512041a040311010309050c151c02120414030708 72
    0xc7d07403030301c00d01c48003d10108000740101c1c001507151114588441d5030030a806450b64511960000000381086d03400c1d0720405070403c81203400c08560819041c00383c40e030300c0241c890350b40b200804103581c90442c0d03810b0111382208585444640c2001d1460001101d0030070005114031b090103881e5000449400144034003074400c0d444040e100e92031030514034076400f14042661701804a0b4016001070001e0b5440100c16000c03502d400c02d1096580c0d40610204010304111509112082d10200003c001c000181404480c51015603138104074681c0c540d810142a5400b4200360071815400744940f8405040ca51003152003403800c0652030202ca840c580d03d05141040f1454000a260000b1400b4020520740492a0740b8554110300024101030540e250b138000281e46200b681d041c1961131070500308114042c04041c840010040c00f06108400485d40c4038070a81c4642d440c40329400f102c0c1003041da00015442174034006014070000d1f80305955159101c04242c0101b0309000c555200c180400000124041c0051449902c5 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 949348075 1250 949346825 949346831
    0x3122304061107080c100207091d10050115030f0204051f0f1404060c03020c03120408010b030102070c120804080a120e0913080a03110d02070201141303081b10 70
    0x15000c401010b003019050007035501d4000450400c040940056502903020040b0340a50981c000305000740d14119955100c03039005400c107501c03c80079100d1012403204030035444083d64400c0d03c80481c41c82c2100d209000fa0022004020300500c8201d200394400d60440c404414014a07083c0c0303400002d14007269420840c0500010b0030170410205034058011414040c1a04041c56551100d0070a500d583c081c90080d00104540402c0c10401d05108021b140050b09001c0c00f40c0f1000080c2580402040d401405910405d40c01d0044120803400c05100302ca01607a0030901c0030500301e003083c21207403c0e100505c1007608d0480b01803101250200e414050000c41c175203d0a1142034032004004090040d104a00400d48201c03507100c104400800c4881c03100c1c0700c50b50b000c2d452a55885040f4006d400400d020000700954020204019807040380e240d00401c03105000b41c0360340c405c100c000d40e1081003a22860521f0a2200e040134420400500070b0400741000e01c0036114091180a610ba1245180419181c8072855080d1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 949349325 1250 949348075 949348079
    0x10e090f1e07020a0308060d060903021c0e13150b120103050d0306030f020f0a210c0b030601021c020c04020f0910050a0c03081503031c0b060a080103122304 69
    0x50420501401c0d00d242400300456407600000c041c1d00c03245080700280a0001040010324103546200040307007040e0340b180041007041e10a041c001e64a10092141000044109002c0307a00705003c0d061460b451000140700729503189861580b4009045654003008035242c010a000c40c030a10060042d000c0040d038107622003010740c9182090b07460412403445060902d1b01d801c2c0300f40082000001001d542540680c1c03120007010081020446091440d400900c8004000d41d0000010840c0116801854012100ca1000a49036501d10032503120584110340564851182002104902d900d6141c07011107600503640701c0003181004c50b00f07aa01100100004540016000030309107851010f030391308901d42c1d180550501010140103450064009805401d000d40c002c00121041400d4400a0b8540300107030560707031a0000341030340200c84403270001140c83c01e03410000707030014506004060321404019507844114503482c688030030b00c0540356144070504110101001900c4140040f000c0000481440401c0355168 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 949350575 1250 949349325 949349341
    0xc150c190c0501170a0509120301150801092304050304080607030f1808090d0618080712080f0a0c0302071a010504060509040809040e1e06071704050d0e010e090f 71
    0x9603070b402c45410700c80f00b042140b244450506495500184c520340009180d00e903105603a1030111601100b0745070080001c004259500c05006117110a5a40e4a64003016601c4040745002e403017850b6100000111400340d60303c40c0d4135049203455001401403040ea403501c0d0300c0d40001400c001c1c0440303540000c43e480301100100345400d84202801c7c40c414040e0110800c2903039446071b8451041c0238115105500740c15042c001d00005922040c4a036501100b048241f55140c94204101d03080524143c0d0011034564140d80014087d201285c4a401c2034a903240a5541c3e09841100a204a0052038205036090010030b0000d40003141c55125580d224805005a6141c013041100740d510710b421050140c1201824000065203d000380c6501d804c007250041607203100f100d20f10380707050030034580b031041c003410036a0784428554041040e40c040d002d16900ca5051400316134100140560070b40b001410fa901a0030342070415440b407402d2078011201494501181d40c12200001c0441030b060300c08503c0c125110b8207200e100 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 949351825 1250 949350575 949350593
    0xa09090b09274606110918101208030c1b0d1709010204030f080706180803250509280b1909081513170702010f0905030c150c19 56
    0x40300d03e0340c641099400c0d00c080c1c00007500c054080001d01842d02d031444e42c84085401c038190381036140041d00380740045c04114040d45a0b208103841100c200c004040c0702180d00c4001c4c6068501d01a0410110b501d55184d0b0511040b0355807054000c03080c45400e52820b000703044c205103d8260402055a80e00354004989418190140c030060161411688104010400140018581d07418581c1100034603403160003a0401e44007404091040702c0c000552130317180408102e10180618000d504124800341c017a1075201100804014009542000c41c8081c46038080b185048044c0d16002d5219001c40c490424118415103412845078021451001d4003003040d819200c980c114403a1100a40d14000b59404d141c040710300e448460070b0b18442264404c0c200020103035200b1090811003141e01200314400081d00b00709141c9141c002410407400101c0b9540c0c6246540c0c401c0440405a0b01c0c000e0203001002d2005080152100d03a1280119031950184500042c00f50280042c1407000e04541ca074500c0070301c0e245016074030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 949353075 1250 949351825 949351903
    0x601050406080d050f042c090105040c0b03190509030c0c100503011502010905150105030c01180611010b1201090203160305060f0a020c0a03050a09090b0927 69
    0x140d15050381009030240006016000c50840c0c10310540e907440c03542407a28180f150390845014640342c0e68240704001400d003408000d0b0503107410787c00ca4036101c0c031240d5400e81d041600c0142808a05041c140308400000000b180c0000501c51100f012090b019949016039004994003409a0408541e8a540395404d101c40c20440302d040341c50307960b03078210707044c5c041d002e400180643d10740a08002e408000b124003d42c455540c45802c40c0c2202d010ba0281e8850b049003030024020b150090191001c131140d1540107244005c0d20700d01854200c141d0030300700b140440e4a070100004403241c540d02d4440c2c06500e62900440b10044140100c00031075401d202d40141854903903d6640100e244901c49c408002260000c149681c01c4202241100b13129240d00d4042c4029018020007200c241c001c2d008a1003c040d0481c0082541c0391050300d4440744aa03840491074111080c15000c9500261a0000140e0a0902c01204c40102c9202c0b820b061a1f001a07086203403503d040d00140b06207001881c403840002d100d0076076903140 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 949354325 1250 949353075 949353079
    0xb18010203271f060603110a1205091203010e010302040501081207170712120f201e04060507050c090105311107060f02070b0708060d0c0303030e060105 67
    0x120714144a00003000041d0450b90800305141e00d1120280d070000280240380c24403400710107845440c1003c1c80207600a05051042c0300101c0e2a00000201d405602000d0755410007694503848000c103448844071000d070800402c1482c040c0903c0d42c0c002c0400161202442c044d080241681000d0360451040c0310840d40180c01a0609a1000102e00c09200c100c000300e4642942c4400c140c1c00107401881ea150681c051000c006180101e100078441d045a441110108a0266180c0622a941246094100304e85040c1502000640034050401e0920b0b4a00e0046c0000c9000c0010410031410507440018223401c181c005200181d80000c1c01420b12004001130f03100c48600300c072072440d507500d040000b5400703640072140107506000c0c034018600141003404006544440d40030040c0805002104d4100c0b46078080e02080340c86e10700d008440a1264071510079600e6159001c5441d1942d1749030341c0410b035440d40c00140065440b1660a810100090102d4820b100940c0b01c1c1c1c5010544000d00441c840c01c049058100038 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 949355575 1250 949354325 949354327
    0x13060206010f15021e0604030801051005180f0d03080108012009040f0e160303020609030a0f11120f0a23030c070206090a06050a021c051c0906090b180102 68
    0x11241c480c0020010040703c000c0384140200c50b00c0c3c040d05a0902400104e8a440c4200e00c5020103903c020100307420380700740c0c0b007540c40e190785a03250002c1180c01092146402d0000c1c10078021000311146000c4c070030040020080c0382003c0b054424000a410380d451180c00c074000b40c000001004151424003400301c2c014241008100e0708400071045042c40c1c05024030191080782c4031400c1c42ca00420650201030780d000514141c0d0b1480c506880c0b08104c0044511044005214020028401e10808400d95008082c01d40d00c595443c0d0440d00115034542d0000e81118042c0511003000071100c0149005000c5403071440b80180e2610b200700c00203024603c4d18442014a40218130000e40110b500d00708403a441000042c0c480d403a0007c034000b0500700c2c00380e01e190640081104001113503294118003d40010b0507694211010150904000400000c6104041003c14818003030120100701e1500b40d5400460100000150400c454a405c0306640081905617480402c00090000da849103504010708269860029 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 949356825 1250 949355575 949355579
    0x207031401060b09010c062004060906022406031c120b010509090604020d18060f0c051215040e0615030c010e150306030a02180a0b010c030c0f08090a09021306020601 73
    0x8141c2920a441c0d1303c90410030300481c040208400ca030f02030074224108038002c8008102d90070a0000c598402c0c010345010401c074010000c4d101b8030010b03840c4c99022000800b80b0030800290b0843c1d10a02000e41595454001c0c901d207412001c0c0c07c580391030340032020ba03900c40b20740c0c2c3c003074850f4282200c0b000e080e10390401c142040080c1d159210a451650061016100180c4d100350008400e00103141020010007a00c0d415405203052152a0300700060854941c01c0401000e0405030080d00d040c801d001c41c0c1d09010b42454001600741031490000c1c1a5064040d1004c01c881802445260526004560320f05094401410388082820f01b0801046804400c1c01c2208001e002400014080307031054035a842000b9000000802548040c80451800c0c0d9024001c0c803a0210240d00980c08410101c1c0c070b2600f600e20f0103110980b150f03c20010132010a8254071030141192040d141c41845c001e4905098441d20030070000d8810a841c0d401c3e00000400340078200585401d0328808101410082d9444501107500000c01 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 949358075 1250 949356825 949356839
    0x903060c11061911070f020915030a080a020c10020114060301060821040b1c1404020603150a030c180e030307020d0c2405162309010e0303040303020703140106 70
    0x30054105445180036001011542c030300c040600104481000e00640c0490801e08101030190480b460b14422110030580d56110714481651981d003e01040c1c0c0356011202f0003000c641e003c0d0040c019004948181c40d0508100400304100c010b4030420440180e40d10481950702c04800891660009000c5000f84071903460008450340d2451480380c050104940312078490204100c41048078001c02100d07094940711800c2e61a00043c881e114001480110304201c0354a00040903210003600c07460b8010300003402c544074500107e2072441004c0200c1d820100d814000300c041500948a600108105968044400c2c085d00000c420f5130403c000c60001540b092080c051202e40100e504a0b180d1111702d031183d000300003410030740001c80400f00d03041e68542216220b0b1021410580200303106000c078490640c41e0324902c040458001803144801950408403800c6005110400e80041030345010500d00741c045500742c2400281503134050b50085000da40a0a010010001040030041e1410104d00013004800c0c90816 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 949359325 1250 949358075 949358083
    0xd0c03170f010306230714040e010e0f011406030f070e04140603010f02070203150402150c0d091205070e0a0209040618181e03050d0f090c050f1c0812070903060c11 72
    0x206d40c40610185009100340e010381c5e403098400030210320307070303011210f50b5501825104d040096406410020b050300000c034624421061081c420fa40c0505214a035903030320f406880040c20040e1041d4100000109803603c0b42d07803503004448500d00d280e40030040b1030038804101030840d084a0b154644043c0140245409a6408107070501807242c2d0300041c29043e038652000a1500d10318181c0000c0c484004181c9105000e0002907014407060b207a00e03018550381e120402507010042480d40105164807100c01442900a0045844d400840b4650058101421a030004080c0c5840b0b0b00040c00e2024840d211800b521a14021151110742c10144d010701490942c40303410000c414614031801240100800d00300b018400d00460340c22202003501003254407030700040700019150340c1005403010485645d0101d0f40e0f1415801c40544510000d1420074071180008542818014014064562a50238055400e942c100320722600c2c460726895440091035400c41c0751880803100f00e90000c00402040b07140c080042d840c005 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 949360575 1250 949359325 949359331
    0x10501170a05061f0206150411030a0b030c03030f030609060901030804140102210d050f0112060b03120406090e01090902130b031c030603030206090109050d0c03170f01030623 77
    0x404080303080e558000c08100c4c0340c0440304001c1c100940200852002940c0402c219004072114102802403c035140b04000940340704082040704103c041020400d2140f10341c0c0801c94004020302520920380c4404000f0741160403010f07a554902500200f0041245801d140302503000c441155401c0b541d50542e180c031401402980254401d030440c50072642c1d05a8001c1258034601802c00d031415466655215201c4860f80002d00010b0000c0d00f400c010079514482a0072150581d0221a428400d9240c1520388101500d0003041c155003600918240311100e030140b4000300007400c5113440f0300f4202403400742c01001c4008140d110b480140d10b0458030000683d5003a20340f64410200000c08111000c04800103428a131345500118200d103030840e01084481e4142d002802100c0c0a9002e5403003030b90f140c210f501c0c2640c131401e000070400d401528005614138040c1401c008181d0103441c06040708003408119640708030055840d607948426003401001004594003c000080c41021a4048545600b0031040d180d50805 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 949361825 1250 949360575 949360591
    0x9060f0b0f07030e0a0605190804050616050d0c03023007120b0a06110708010e03160302033007020a1122050a090b07020a0503180a0b0703110601050117 67
    0x2081c2c8185031140d10307650b802c0c2800400141c1c080342d440401601c0b1354440131045002c55041c2c510610858099010035100c0ea4011000c0d01c082e640d4840c1e540b40d04000c0062035401d00405010024148150340725900e04121203442c01039490314444008056030000b014810700d201048090080803032130080c1503070780005a40c00c0900803c07424402c0e24015040d03002e94240c01c50400000001d210f64041d041004040c40b400540d040651121281da090720200c0c500186607a0041040464400b40103c03d407004034007030f04c1580e0410501006c003c1c104442c1d200d8070100e0350398403151000b034841c8403012a43c00c0344031800100320b0791090396a030215000490514500c0760042a42400d107419800392100b2203040102001c000b5131406221941c001d0508030816914001c080002411142c00050008061070b0404011414101041d050f42041c04400b0000f5400c0304010348000303103070728000002e4400280f00c1e0b19221000f43c3c04482180c54094164015410044202ca241607100070440c0480d40140744 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 949363075 1250 949361825 949361827
    0x90507300c110102030f010905100b0702100201201e09010f180906060507060c0305010e150103060b040e070e060913150e01120302010c0e100807020f070f09060f0b0f 73
    0x80e9140603501d442d500354507000a5400002049080400f0f050442e0680d2280d610810480e100c105030540076002c0c601808500020802481d005490410004130491003d032002280d090002d0b4010305c540e0300920081416240007051070341110707202d05c861a1000c00085115401e000103480001e1500348110012014448000341080030350380e07a0400b2202074902080c01748441540c40c0030041c046d5000313040c15140c2034641a41448214030030302440c0e040b1140c09085040316150700060080e00c2c00001c085a0601d5520f1600103110360a040c003820003030042c54000301451400c000c01038154804035803010701c84c5400b00495071807540d641220b00025460302100088481d4003c01200350300c42d00d50800608900c111000040800400d01e903216814413a60082c000404c90300800e6403011450801540c0c414092180006514421500f141d4001300600c1181c407100c0562810600746090781c0c1000601900c4100300b40664801030003020003e02880e0080400c403450000e80740c1d981d0084d141c06010407030b4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 949364325 1250 949363075 949363091
    0x3020d021c08100806070e1c02030c1302130308070605063c15091207062a170307021b06030417040906090f0b04021804020c0f060109050730 62
    0x82a49011000c4c04d0720f0800c07211142003409010301503c4d2913a69444c0300780810070489070103c14000019a2040c0d01400802c1e143c0b00e404104807008045101c100e900710360900403400000c1016201000642c05100700d155600c000e0b04020341a81c40041041d4013a1140c1e2103840d104451840801840c483e0080c035076080308443e0810400c61520700a1369551200c1c1000d00e50400b0391900000344144001240d0010751904e140e181941c0310b810030b1003000b021503030705030307527001c4015041031921403c082104542e103041c00c0d03641e60020b40080030111802455004010083d031030790108a51503520f8400c001c030b5404001207000203800780c8030042004060341600b41200a019140c4410b4a010344401c0000384000c58640300d030540107001e44000965001c0c20865a801c480c1450710894a02c0440c0309041a880c046a605000203988034070a50900d9124000411402c1c5506112560182c40e00d4032004c40c540c06e02c40d00003801038039811003280460600d024408100c0f00c1c8c0c0d40780100f00004400011031002c07 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 949365575 1250 949364325 949364341
    0x319050705192d0314121906060f0509010e010e06031f090207081b010e0a2a080c0906060d0207051b010e030703061119030c092102060702040204120f03020d021c08 72
    0x1000d03400510701541d0580052104803851f4604e0120110010796080025640c1c0312011035650310800301803404a00d0030041071310b81c0d5200341200305180906040041c281389944011890542c021034412034070101c0c0c00d1140d903140560302601001010004401e608050031615491541d11030314441c043d80400721034140c11079020a42203080b001c3d08140c25a40010b0a6082001410003003e401c0d05c600030f490940140908045c050840580e084240204108080441070040300140035080e00d0b03110405000b041d04601e44d80c00107020140c402c0c40504404c141580c09002e4241220003513078103011030405884c4441c1c0300010b40d041143d410000100d1000000d0510003c0c6200340c4c2226440c1812204405105a8050700f0100c2000300070750310004016918030aa01b8403003440c6054101c0503804101680240c50404003a1458900080c401490f2a03034076062601c01411100301100c0010754125500c06054050207005d180c40404d00160250980d80300074450b074020090090b01c10300c47c02c0380101d00c42c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 949366825 1250 949365575 949365577
    0xf071a0c07080105180610030b0c0307120c020c040506150f03040c180c020d0206090303150307090f09121407060915051005100309050319050705192d0314 68
    0xc0411400070481030410b417454840074042a0f13007880c040d1142c400819240301c03d607041e038002c907a003000340314149445107056850a07501c017810000800c420071165240d40b030795034401d403e40b02c035843e001000300c1c0b0301c103005000c00c0d98002420503101d203000400d401081301e950320485800c0510660501da8a41d0745291182c50b034801e0b60050080c10902586a0141d104103901494400107140c00715140665903580c01c80e610402262803a11980092000c1807000101810540282800500340e941c1d60340c403141b0702011152680500442c2d151115000300130b2040907108007010004a190040070340710070440b0070501d489810f00080c00b02d941c5000c05c900340325000f008400760300810b44c0c0038855030501a01c030701541243c50244501c40d8004540440c051800380c0705217016030794828040d501b098810210f01c034501521840742c4050100c1000f054002400502ca1140c01c0f036014035416801c84041c1c1050340400305094500c000395000032103140c1c81d0390100910050b169515140144000b0110b50180001e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 949368075 1250 949366825 949366829
    0x21018060b01180b130e15120c0303191b050703170d020d0c020f030a0815010c12020601080105161b0227010e060603040b040807060212180f071a0c07 66
    0x110b83d2220000302c1c0d22101c18008000d0150b008280810032500d64041d0403441da0b047d80e0900036a0385038100d85100c0e040459039580d45008a0041d1000c102c1844003084c15607000e20040104140c7d2124418145030b00403500078180d01100c80382122417040c82e07a80306d40e22038560001800703508580201d03c4150008100310303043c0808030360040d9101e00508006002510709562620058061010040d042c201c00005492480e04159684486500d51207401070f0310858400c480c5040210440182001c81d002490450124205600a000a62410140c0380c21540b01410303c81d481b5000841d48000d00e60300011465030481c5040101180b4800c5100042061300343c03003078a00c604008074000601180c4845203250488030b5081134941c00769940c000b000b0171031004171002400c171500e0601007070214620308042c159031840b4401c01071500c543c3e9050041aa0011106101c51108214001203240f205000d801c0000082c4002064240d040c50050703001090042e2002e0002e1001041d1118044400c1044c840 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 949369325 1250 949368075 949368107
    0x80601081305030904091a0603010c170a0207081c0b091003080a21140a0501050d031101020708072a03150b0a050607080403020a080c01050f18091006021018060b01 72
    0x3d406c4040c54051914120300050310340d4031041c24001050741c2818055000050b805550b00282030f003410310590f1440b03202510300201e0075800c0c007521001406a0000b03141954006102c00c001d00d21011600f0146c503480008540148544000d02c000310082001c0311041d01e13031140c1640d89480c0c6104003102c800d915031105000c10020041d9030000c040b0700760f1010f402105803a40700f038440d070307a8101d000e001d071a000c0c0310301500450b0401e16000401e224448a64203500c190002502c0c0460719150f40a050700111815a10007151003a0b4403c0c011082c003460060001d05000c00c0c00540c41c5807100450300c071078000c090903015100c150b0f10f00d00ea940c0240b5140505402080e10351982110f081c0b603000b68209010032070040750040d4020840c0c00c0006819a800c10050351100e260a00c0120180307525000055010403404002c05d88444c0c56032000140d41c4a03480711045495650701c0c4c028001c0ca043d81d08201c510146140c00352440c0840c28425800144135084000801e6495081c0012070f102012882162 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 949370575 1250 949369325 949369331
    0x1a100b092701171002070f0618171215030a0318080307060b0f06180112110309060610031505060a0c050d030c030c1719060902040e0402030d080601081305030904 71
    0x8203021008214502043c0070510841c0c24101401d84404100e2080450142c800c41028050400040c103580024103e0f51030440d0751a0204520f658507110400c0e05040443c00807400711744050783c0003210036207030360202401504280741c108074004680c41c0c1003115070241c2005140c030a07002c1951080c10441000385803c0781100d61325030b21824254014400320f030800b40308400d0303110b180209141c90801d1b01c42c2c040f0a4541c01807400f1241c0015940c19841c07007030769000d454031a0244044800319401031803181c00c2c494003030300c51444c20300100a4041d0b044145d4400781480c1c41c0008000340003a01e03c04081e64406e480803aa07548090b00207a030381c040c0b240c41c024118403038049400390079035040d0080c10005165441c14045203d0700941034580c401150030729001a04443c001400700c0d085851104840d0300491800610f00c7d4850040380c01f80d80c01038101040781e0040c6018001141403c0000c162400e0591034284c00310b041c007100003421940050041c003440d81e07042205405206003481142c00c0090024010 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 949371825 1250 949370575 949370579
    0x618150d1407080c0102070b0d090f060e0d0504231507030c170304150b150d0c09081207080d02040504140402040e061504150906031a100b092701 64
    0x3208400c03890704514505000c0e1403000900003c0c002458614048140c015000391340c1848403081d1141c110500d050b01191301d84031140301144000e4281131301107010301000300b85081c488680d9440c10908810a0f0100101008200b1100c80201100ca10482030406064a010010000a80d4101c050014282408000a0741104258010514400c90740c07080e418130b903044080650001240c041103401900c1d0036400f45100700c0c41c011a901a42440100400b14080c040d801000b019040d0400c00411a80701d568825440704a03400030b141c1e0000b4007044d001840c82910401111600b4068000c004000090105a80100d900d40c0e405032006008013030001c010048a64000c3e903805041580c00740d020301d180c81c0300070040e0303100842d01070b04c18603038006041c41070303070036081400000c0603000c41610900103c1003000c110350651b0301884008500641032030080b60b0851103c00107240020340b400711610030070642045491488810b0390040c10040300e5076030000c500320b064840c000218001c400300302c01d150400 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 949373075 1250 949371825 949371833
    0x906030c1e0307020c100210091412282102030411010f080601050d09050712060608030a080712060506073804150e0f0a0302010506090618150d 63
    0x90150340000040301c018001c0100545001c40c402525a840143c0107030401c4869400c3c100d54990b84182c031032044646441e40070f4248001c03206200b100f00d598000034000b404100348104210404403040c0a04140b5255810b42c074580f1702c00008500b40e80405181c3ea41ba180f05000318105006501e0354108004051808540400294011141107030320042420f0344111551045101c45540500ca403070710850742d1240302c01544c960300f141c41140c0400d62900e91f05d20000e003050180c0801030060000d01c0d9541440d91030f000c01950166001074005510500c10610800c0d03203d41c000f0380006181c240b00b1000022409070b40040c120b039401c4140c214200007845800c01002080d03070240200410f00c1c6140071052441c0c0001022030031440d00340503107100070114021568241d10b00c1d4011000030400140b2707450304403030b40341819068a50084250400003240062540a01a80f42d2284040311130500310302e00400052550341701d9100940b43d0250280c00201e0311b51507110741166004c2d00810301c01c400001858 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 949374325 1250 949373075 949373077
    0x30627050601081006030b1803160f0b0c0f04141801120c0e010b0706020d1808041a0f0711030f01050a022d090d0f0f060903020d0c1709060906030c 65
    0x10840f400d40c404c295214207030507507034880c00d420749034400b0714a0f0740354031480000c024400000c418032425000403c4040145c0384046450101c0a2280511848158140c200518031300c90040030840080020003080c0c00041910302124140c0719039960790f0706001426404501c2c0403501c1040404008408400410790b4a030007803071500c10602c01c00200807002d842d5918a140300f2801c2c4100b05002c1d9090181c480000d540760040e0003099903032400003403811030700c13241c1c1018900080da003a1103801d8001402d1000c80d0900210003401c46403a0149403608504100b008014481d00b18040c100b60908085000c003598244400c4504041c1d1500074411403e000040d84000e40c0900450b114545503989141d00103210b0108030b032204030841c0a01c1341051310000c2449079240007003c0448103004205000070009030000b11903c001402580006030800042c42c010f0b107410b19090006060214003211440003c0107890030b00040c0701d8201c24280c03250540b60100b040d40c0110501d06e0760103800801040303110002c900c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 949375575 1250 949374325 949374329
    0x501060b09030607090b2703070e0f0906090a1103150c030709080c0d020f0a0e0108060f070e0901061416050d0201060b1222140a0210020d0504030627050601 69
    0x1c0948800307498104c1c0c152903284852240f20401801804074441c141420000c03182401101840114039003400c50000782491840c0d00840c60a08251080c010481484010203030b000050350300030082d074103254420303e544005400f0010000b4040800c4440151001c1c80020541e04216490384c0840c1030050046032990403c5414100042c0c40b0f00c4000f0700c40c100040c480c2000d200142101d08440400d4003031005410421000c01e0b0042959440081c01d0620504a01d0003028000050036190414034000580c160000c0d201c00c1c03c1090b0b46104404554902c1c0c12141100c81340d00b8010a06512002800018000e008400d074525401c09550000d00502080b03416503905540c1c005c21045803207110f1581180030340c087c01c0d107210448000142c000122000540181c226003201c80e44041c080395200813201070644490310450f00640c5607a03046007000ca91035207000860b40081c2000d0790250b08001c000e801b9502c80907100d10781303d0104134130b0150035081201d00420208118110b5142c1820b00039502c0c1428 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 949376825 1250 949375575 949375579
    0x110d0b040b06011b11090606040b0a0c0611040302060d0c020f1203180105010e0a0f0b09130b010f0b0906130e1e1f0909111e030601050301150e10030501060b09 70
    0x15102c620013400415a8001200c0d134899000d01890b00040c05100c40c2e07000060866030007041c20040442d020020780b015010380c0340355503540306400c40585050021703210103805880e000f90b002d020900040e5140307010381d0368440c420381c40042c50042400040703142444c596010302d158001c0060644104002c00d000314070802c0b480d050f5080f00c2000d611200d080714001d20414030107007420004070344041c6046c1c121200c44559a040070440050110008500c01c1041e07030303100015143c43d08840708220507131070030a004220742e10000100a28018983d0b0303d40c40b07082d081078401c403000200448420134003d40c1a000d4001c628101ca00762800e690303403102402d044464041d420751882c0c00588109070102c8414a802420300440410a180c448454040e12001100715039072011100607083c0b0fa210b031503440284600054080d00c0b5515000107150500c20180c10560090b41007080f0280c0050a01411a04540b801020810301d80e49182c1c41640c0400381d904002c1040d400c0000015000d00100c025122031801 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 949378075 1250 949376825 949376837
    0xc0603091e050601050d031101150611010903081b1c05100801180210031e1d01050c070b07170f0a050c032707050301020f0d27110d0b040b0601 63
    0x3807081d20705407a035032400005006600400052000d41404a008039440d07100e810550642c0ca00d4615550a440c101c190942c00040c405c1810485035900080c18400c5d0840903000300072195898030000c22140d00101064202c903c04243c024041412100711000d40038043d284003071038038516005801514003910700c1e5142e1405c41d030700441c1f61041032060321140e01250102e0080c107482542841380d01c1d00807110410a06a484d80070400c4a00c025500000c0443c000f40000f81429100034180952450070810361b00685c5010704004e421b231541c034111100c544e000540004142d17180c54080b608a0f01c0b10840102e019158401c0c807104c5d01440013540d005900186092001d03650350514030200e400101c1c1c4410840700803c0212410803010307146060007213005419101810b80790710210342a603026000020a411002030100000c5c0300b51b200300107002c2240004904007242c40c2c0342116001e01c2408010740f4026465070340c0c189aa07118501006d0a580c4603582c405103160905082a500c40c04542e8035003c241 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 949379325 1250 949378075 949378103
    0x11061609031707021203190e120105040f030305070f05070f0c180e0601060c0b0f15030703080c060703020910030b0102150c09030f0309010c060902030f0303010320060f0a030f090c060309 82
    0x4c0c08000d44d054a881d400f82e450b008485004c040341d0502003460324527000240d941e07240300c0380c907000e004680c425801544006121621450020200c0e80c000300818100025448803da085922004a50300c19801c4140180e06040a003050541da50856121800702d404001c1e00550350650b5410103006950800143c40d120780c3d03030340c0040da4400c103a45401401041a01d00040240400007015604894a24640c904000d458001b0924221013908290792412011841003c0a1010428039a000501d0300d008d6040c4800880400d201e000c3c0d048901083c1915400c1050140e48200441e41488041c90f030303041c22500f081d28030900141d1148109601034010000e0f040400c80c800070031035150180603514204070704030503100c41e4010703d09500120303418000d14452071140c0300c0c1040558041c50080d070107001c0350801502244001c541000c202c60007040140040c2c142110f0450540d0b00c4d0110310b00780450000103546c00e00303005203030340c060003011440c1c000e03004103041d64998403c0e00fa20f032250213120b18045d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 949380575 1250 949379325 949379359
    0x100f14010801050d0609050609031315020601180e010203161b020f12030d0207050d23030406050c0c250e0112080a1206060c0c061106160903170702 65
    0x898641405020440880042100d0304000310141c8560380268000100981d00f61340b41401d000081d6071803e8964008034004003600c7d40d4840138001489280340e8208024031039417010f515060140b142000e41020108542009120b90300500d4083c0506402155240b5200d03a003130425010645860000400e03508145141c004550301e004001c0e40c00600201d4010742c06810021140c103c1c0c240b800a40c0018808940b042c1602d00240612921800150a45400c00c12004000d0146050040c0c001d0340321742a801e401940d21021a5049604040040b402e0381c1d071000c0c08001403180c006081d800780b08a04080d82d030007000100c2c1c0c1d1070300307010344d07400307180c90b40d84d9010710128000c0a02074000d4805051440c0300010f081403004011000317450922680303003070301a80020f0403030319240d00178408961400b03440400c210251728000040c191a0800303000d071f501e46025103a510b01005100194000c2e28036204024035028025401c001e681c04084a100403070340c003c0c4950130307801000d0100c0c058521001c103e40c2c05 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 949381825 1250 949380575 949380599
    0x1060909050f0a0e0102160c0e0705040b1204030e090a050103030e0111150417070807151814070f0b27060a050f0f0c010915020301050f0904080d05100f 67
    0x1e4a030a0740e07210300a80f9104602d82c014041c00c0401c6420750b6007041440310501c429081220307244c2c001c04548001d5840c01040524a10004001d1030812004210a20030a0040c0007901c0703031002c83c41800103059545103410b44071b07000703444041d9a2103080b00041088548082c0c010505030380c0b081c2d407501d1164000c0e00040d0303007407264032a12078860f0300711242d0280402d02d00e140d113170760250040e0342c415903040304a60308441e59400100244c0301100d0025408040c8210b468004480003042c880130408803003a0b00440d000e5074105034008210101001007894400c2c030800c69140a403d0380450050015552100c030700841d4010f600551405030000079164001c6050814081d1881018240518100003004115440d1340301040449036a107050110881c03a01c4220b0290041d0710811000082e06003d60a0070120452421100410b0303600401c014425500c1d007c01e02d82c003100e801c4c3d42c000c1154890f03160401c068000d160441e00420300d40420010703840c1014025100316440c4884142c1c0b0341da00d4850310340704 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 949383075 1250 949381825 949381831
    0xf031f06210911040507021e070f120c0905130b09210d090f030809150613020904291903030f051b0708010b0f060319052d0106090905 59
    0x181c007180344401e5a15900d401040401c1d215242d006461110140060200c4009641140042c0d108030b03400300d0302003040e42c000c03540c030154100180016840c260a58603410a5405640410b901d0455007000708850000c06d18060303c030440c81404186828003200032030385d1600c1400d94040701d1000200d5564040415002d01c20030060003003c0c5103440d100e2621042c0d034040c0c405100f0305580e40e821403011400d00e0003281241c41c400ea5422809040c1049110314204c0100e081c06481c03000481880301c6651091072010404042400140c0c603030381b150000900a1604401e4088403441d030503820001d02040510007c4a0300b000c40d120105580781c41a1125807a103e400018041280d1990402000d40070f031010b04010281c0484c001d0b2610010150b079818000e05603c03860761a91a0007100107a85010301d12051281000e40c0e0303c030704616144200c8030000c3c500c40d81d40d00f00c0a81d070700086070742001820140c0c0d56810941c442c10b64500c90540d020502c5070000d10446002689440d004074014405024240c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 949384325 1250 949383075 949383107
    0x607120302031923060a03050303070206100e07020a02090a090f2105070b06091009090506180d0e06030c0f16060f0506011706030708070f05040b0303120c09060f031f06 74
    0x8040140502030184c1d11409030025a1108a02c0c07400000103108000845c440c0c0b80c80d9010384401c2c00c4c0b20f88500314015540e007140d510319034010b0401c001d259000a03240019501210f06203070944407954000014044858040e0120086151040a1003500714400c1300301019122541154020750350126520301824200030110000000402c00724505140381c183c000c10850f055007501980d07400482c080b50090303030003115150000810400411020003040000c07214001c0500208005c08900904110480c194680704410210100d090301104e80280c0d40011408610240e03540892424208003c4040008640582c01c3c80701075080e903841409214020354041c0c6554001c034650740207001c81150001d10081d018400c030701000520798810000200101140204594040d0902c4140320640e59854041c5009602c100200c000b14012008050391007078a811029403960b0504000500c94810008068445040071040c880b00746040c541c0168141624500310301d03104d42e1001d054031800c0d41030580354 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 949385575 1250 949384325 949384361
    0x50307081b062802151815010621062d09062301020f070609080609030406170a0b0a0612050a09150b01091d1006090e060f06071203020319 61
    0x8048503410405012050f4070b01c0c0141d803440070fa0304060405041045442a0f880c1104c80715064a0030400c0c44002c40e03010b03507200d0b1000950b0411001070720000c240e5118510901ca0185605240082e542c44040a07001c001801d00320404800c0c5a400581c42000090341c0e145070240c40003c011a091058800301e81a104080100b0054107a0825503404030480d618154020759220443c4144244131032000703081991507003550a400c01012501c0e001000304400c2e2664000c010a200755a040780002d0000c10703100d090003a15503034031a000d401034078450084582000d140000801c4254014004000c21200c19a042005c6e59440000b28203441b515940a024480c440100300582c2c40590040d600455040c10242c440c2c95942c0c24000f200b00741840845140d402e0841032004450b0307110a01c40045c1214986480014100003c01c80b4142000e84801e1044920b80070300c1c641512082e040c1d501c07460b0440d941c2c10701d034150024058040d50080728454031400c00c401035000380d82594880e00c040d0141c5400303e2 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 949386825 1250 949385575 949385617
    0xb090907030c080703051902010c06150f090e1c050c100b0906031b1905030f1c1107181d0d0207050d0804091a1519030902010203071704050307081b06 66
    0x40141f4141d035160503410405440c0b60300b40403818034001c20b802c810b110208204014641000007081e02d00f150003416903076040203185060544002007164040002e00003060095100e0b039010341d20782c811080e0b00c810394010400c0d4611180e5082c0d20444000740e0503a502031140d0b03910020561604800d220350401c1c0c1caa4074101c0c0805d8101125040549034460070000c4906071140002440c1c440744910030100307641310900c04824180101080340c140e8042c0d01f031600c82e41c2e0b101e42c20540c550002d409410300c0540c100302050000d011981000c20040c00c03561000d844117551000b129110420307a8504805803056040c0000c6c54108091038030030710740c1c1200000e070502c3e05000020000d0b094640e0600d217400d070300c454406240d0f550801d1041034440000d4440355559800010089088008010310341407518010070035002d81d80100071180303450751040c1c0f602d090030f0f00660688610f00613030b00070940611444102003058040041c0d4032040507400c01c1c210001911020030804248250913000c10009070465070 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 949388075 1250 949386825 949386853
    0x1050d08070b180a2d050604081c0c020f07060504060f0c050703020a27050717060111010c0c0201110607020c010c030302091005030f0901091709040b090907030c08070305 75
    0x18030f80c0209080010340d8281c15550211840c114511206440c2020b1406007918203c0942c45070301c82c0707000d0324600c80640d428161111512104014000f9110040c0081c8218103d11a002030140405541804122080e0000c000941d103c210404941c030b2842200c50108100340114155000c58a4555a00c41e020358130031000c480e88440c60208070340c280304615001c8016070742c24190401500d80b074064001e04600444030050090100b4910401851812091001d12507002e41c941418010a072019041a01d4081c012101891b0195003810154070701284d403940c203a813008191160078000d98a1a440e80c51140c1202e4030380c941560030101680c0480b600f800507502494880c2c01c01c6001c0d003130041c1010707042000700702c098880c0d103900b40008800008106c40342c0b43c44070360780f0f8001507a0710013000601c40c140e44010080d08802501940c840c800f190408590f6215000036250020103004465641040c1e03c1ca0b070790302c0006000880b4890891103010035403040c0001c0f040d0440382c0000040c2070145030140 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 949389325 1250 949388075 949388093
    0xc080412030b180703020309120711060a0e10091a1305010f0918062c0103061109030703050312090d05090d230a0c050a0b250b160801050d0807 63
    0x400070380c028980e070820122003608100f2840c4a10b0380c980300540d40346002c0199500f000d0420741c001603203080c240402d0010038240b048025500740300f0f41c0c84e00d13903610b50130310152035101107008007a5101d0f0840380462112544030b8001c1040b5049411504040000d205801d1228014071007210700401c0021410002584100cbc103c078181411400c0c5101c0207034461030090001482860031980c2d10f61500301c00c02c203031b038a0801e040e10f034140600350600b18110040aa0043c041040c400a0492900c0b54004595070181e44100c030000d0034001c00f260301079540d9142090302c030b80141b150440c202d50b203100050400760340862402080304955648030301c0c0012a000700328003803034040782c2a615260b0940f01440541c05c029000c8588142e880000c00c1e104c0801c0c40d01128495071a04000e00480d0010310802ca00c5100000342c4a6040fa60032403812449003007100203000e0724202c0d6024020317035018130030311106001d041e0070191076121a56a442250ba200d0050000e00c064044000b0701d54081045203001040f4420 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 949390575 1250 949389325 949389341
    0x6120e031801080606041406180330180d14070e1909050a031b0b040503120108190618050d0c0c0504020322140d181208040b03040303060308040b030106030c08041203 73
    0x8100f007080c0410020200749080c604030340f146505003010980e0710204680344100500502c0be510320600e401041008050303c0d085060240340501c801d49025004c0009107824600300c100305c0c3c8101c566540e60340c0303043d00450500340d802c17a8804624119051a1100030700800d01400c3e045001020741d002d403554110384006082d402c0740b801000342e90714240020041d03540b09000318040c0707000795104c601d14000156800c1069100c1170442c5d01001030101c028031440041d09035030b500400009803c2195078080c036814111803000400d05e004030001020300640100354900518010488200051f40b61018041280310681e024401030501286d1450010420302c5806807043c45491fa21806406540542e40340000b00c07582c000200741041503150510002c04036500042424110b0080803110359240d40b00c0324403481c0103081141b0f03130001c001010305000740c100100542d40302d5002c55560340d8500c11001290420b01800b0006070810f212000524403c1000a01480c1c0000b200c00b60080c0f13258040c0c3c000c00ea20 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 949391825 1250 949390575 949390597
    0x3060c03190603080909090c030d180305010c0305040510110d051305070306051911040506130e0702161202090a0b010c050a150e070602030406120e031801080606041406 74
    0x310032070422580300c1c01000000c610402440780c4640b403003000c1243c203880c0149100f1041e4413503807101c2119603000400c02c40510143c14090131503884e18a15410404017900003420035070070b14010140466140c0d112606c12030282091f100891411182c00c0c0540d1a580401c03517080700c0038402d0b40113840881e40101d4020707102d0040d0720007003220b035a512414412940d02c150380c110382d1481080b1700c680c410089003200d22501c420811618029900e02e242c1d6015a009a40c02004041a6080c1d0340f95403d01120192030b00c81176403100d506d00034000965507444501c18921590b144000010341889600c1490403441d03008051030000d541c3c600c2a00e0046c4400c094003410082003441d00004503d090004002c03071802110300606e500ca4001c002825940743d240c0442b800c0d4800c440421030301d036010042d81e058440d42d10300b520741001c4181c1c0320b00140a603600c00d24854000001d135240c10020b05108140340c0c0c003081e283d03842c0941e110002c202c020300445c410462250100c445141407031500d9001001e50000f2 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 949393075 1250 949391825 949391851
    0x150c06010e10092f0a090b09060c0a050c03010c050901020a02010c03020120041a120c030901060b040b071a1e220f030210050402010917120327070503060c03 69
    0x160f000c9140c29601e41d43c144450780031060346003c03c4940c9581d0000c44460310703100d0301450003c0f548002440050f40744102d42980388041070001da19960281210841d452080c1240c0c5000c00360b083c110389a15858072560300ca5842c198800442d1409541560a8140c050700641511001d80d00151035040210030210300715541c844040ca0a40b1129003100156410382c139400c0c1e141c0d81441c070500d01207006084900d000650600c008a0b55008010005a0002c106402103450342c9a426101c0d01600c1c070703a0401c0d4100c00700800c01051015100006e0828540103c000040c510664000d00e400f90750159a003456000a134091080000d4107100040d401021a500003810b40c2c005200310264035801c4281201e00442484e40c110034558100301654403491400010440d030f0a0507030005c0e1103040c0a204410407098401c0128440c1c42c2c080c00303c600c80c4071070000820741d01d142499140d071352489619200100042004c00c40604808006948415140050b00820154a40c0800240c40c0c2c0c10080c00c940900038 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 949394325 1250 949393075 949393079
    0x41a120405061504230709080d05090111010b0904260403060209180702071214010507091e061205130b04060203091b10030203090a05030a0f120b130e01141005150c06010e10 76
    0x110809c10300c0050b00d0030fa42d907591601c0e1000c000528403c0150003c46280c1e04140c03020001e84d69040f25150810b030300070340c0f40142c003480101c032808031244260482452503002c24000309001041c0c0081c4400702003240c085206801c92902c501841009503502030043e4400742c4d003840b000901d00d0300300040a0046a581a0820301400180c1c01d44008503501000641c2c8170340d040029286c010301c110a40e003a290300320000d00781017240c010074140b00c0310070031950643c5540120709194420503841d0300154019001407074903e09810844e01a500c01d80781100d0501c2214400710080d01e03413204040c0c20b550b00034504003003441e000c0d008034041d401c09404071141d80150b40c0c1080c002007040006096512260b10b03909030200c0d41000140c907480b01c0b46000c150160604010302c00540d6038100c1d00780e8486040100046c5064601c2e0300c40c5c01054100c08421011000c0005e100c2d070ba902030301800c4200c0d0320889410860002010f9020310038018101c0c5140207900c46c0c4014000e04040041c1305074400b00d41c01040500c19 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 949395575 1250 949394325 949394339
    0x50c0102070c170717061617042307050108130303060b0d0e0c0f01050a0c1106040803090a060e0a2c0c0c010b0301060b041a120405061504230709 64
    0xb8103907500800c100e202442864524150500025000780710740310481c8a11185580030170f440c3c0d80c000300f00f041e0805181030000407003802225010215503642c5a06502ca1420b454060110b000c41d0002c2d48600c6000100b580740400300150078020703244181c1da811183e0f00c480440f0341c02c10310b113a00300718145a140c00c0c010844144000113885075401d10306000c141104929041c84c240702d040360583d03002d054001700c05c80d03850f40c110007251030a842c13a16190080e4041400c0c2505103d4402d0210750307002600140001c0e41220010140c03d072011304440e0b402c600c81c0e0b104019580304458840c17072074118401c40c034200b040480c06d05003921811100c1003214a1900204030040c22001d0032030b000e030500302001c0b0301040240024800c86180e000258003c000c0f1500340009020b46020314850a849814207003004c504201501040c2c0b10a0000c240c020080c508161070855203485044400e501055050304401c1050b140900401c1c0390900d500e56180450100000b40050034140109800144500c41720000342d41 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 949396825 1250 949395575 949395593
    0x1014031c0215060f060f1e0d0f0615140a140a03060801140702070b1e0a030e06100b09010503060102030c0a0516050a0e130c03060e0105070e040e060403050c010207 72
    0xc118981c0600408101d4030300502072500d0141482d80925520a140f0038a501c80d6800c41d110412010082078490040d40c11041507034141c084480d60345000402c1c1c0c420382d160f054200c07403050f20251400340032070358903040c031888160342e09040d03140080c43c20040c0740d6441c2d450300010031100a041c54401d00c14407488100309040d501c000305000009035140010032841c0f40138841d084250350303420030450b200d0411000081da81d0b44203020784408000c0005100f007041c500c3c4080c8000c1e40c00c030803890586441e04a1005801031084003260400d5000300d00004d41542406160842a84c03410302119080854401c01114a50002407850b070662004001004a9040c02c214120041c0e00c103134020400786010034034001c990002075200c1c5015400c0b1071030501c00c014201d91310652298060365040030000e800d0030618040301803544060301d481d00d02445040341810641245202c0c500c10344503580c0c2850308405020440c0c18500349420703650001e60210300020f115000500c4003501c1f40c0300241c20701845071540514 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 949398075 1250 949396825 949396873
    0x60403120509040f020304032f0604080706060b0705031e070f1209080a0807020d03181d160804020915060a020105010312021c110703060f0b040e06101403 68
    0x4120701049048040c0b800f40603040c21004690010f600b541819500541040c0030788107504036402e081c003141d007006003100da0300b1034100d1501800c43d081403d082c10821a03d500804d019500b080c2801d00c042040142d8004a81c501903000006600d044c10303000c83d02d6080c00c9056507001049204000d01d0001c950a6541242c03420700136400350108050405000d4001c140e41da00403071464002d03400d104040340d0240c040d500c0064043d600d40d085045e1503c1c0403521030720f583c1300e220220090f6a10128154000e0170750703240b2940049a02d01d5140d110f0359824807008174081c08140024034404001170043c1840258150000c1403441005d10204070400001c42d113420519011006030340d5103004000344882d0030842001c44106001620030071144803461a4000c442010030000c1c429000c100d482080d8003040b8030001150011020484000c642e14680050041d040c80306129a0802c81525080c0714042001400b50004000c0512100d15121070b400076841c013441c055525028500400040c07030040804151 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 949399325 1250 949398075 949398077
    0xf0b03091e101a0114090f090c04031205090a14040603050d0c030206180a2303030a0b090a1a130e0d021f090201090b07060b0d030f172406040312 64
    0x80d40102440d1031030210f685045080078100c0c0750a42d400c100d0f903002500d10841540b40c2089560b180035400100e0f04810160403800d400200d003100700b00c11111000050002c0c2c0e03121b4020019411302039001100e490058001141c0d0080041c1c030104401c00d001c12810758003c2c00540003084072556500e40b03500b0105c2c08491100411433400d058401c160b03051010b00c0d0301601011540715491a12100b5594405000c200100f2010704403910404000b80c0403415400c45203140d0480341d03a03180075844000608541800c0d9070094030b000c00403401c00710345030151281042d9280c080100c0c5e0241c00081015625000ca0325062007032340e48482010245061103132a01d00071140d00180b01c1c02c11114503402c50300c04c114508125051416800c40d0041c0e900c050344808403036a042a840d1228403a040071401400c2c00e0220507030001c0c09241c03e404151300b202909140100a8642001807100d039000046007182c201c6005180105c031020010491030010940c0140c100c0151490b030810b0740301d9842204d40d59a5489580c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 949400575 1250 949399325 949399333
    0x190309060b22060501050c0d03020f130305010906060801020a021b010918020a0e1002150601030e0a0f02010f090e130311030c0c190311010e060d06140a0509010f0b03091e 75
    0x40c207542e085005442c001c100a02e070292400000395100d54580340c003c828842015000582500c0001403142501e001143e0100544031480d62842d0090080042020840b103050034103000040541061081e00c4140286030050050701c0b14072001e40f2600001c8000740313410f01c03e0401011482095180f03040080910080f0016510010300c10040e1402e61821361441c0f20341458100c02020035804503440707500410062405260341c40300c0c03006178043c081a03c3c420000e489203405c20000c1c0142d143c469403040d8000e89603150390400e14042202c0c020401c3c0950a034543c001408905c48580c0070360003424040c080e00d084004d403842d100c0f165007035900111400105501007600c80d141c1e40f40030b43e85110542c08202c822039903645159101b80803501003480c1c16050028032204030101c1d0719558201c4a101d551900d042003c66105d1210200242070100300d00d00174903060700042040d09190f81ca4906031800315107001c1c6c134141b0300418054543c0c00105041c1240c095210000258a14071402e5030b110f00c8200098 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 949401825 1250 949400575 949400629
    0x803190e1f0501082e06150302031501051e03190c0f17040b0a05070e040f06170610050d08211602070b0901030c02010e1b0312190309060b 61
    0x650141d0340b042c1c200b18044d401644034844106119401e6211108804051101ea0352228441c0d04c01000c050348a181d04140034456080071580c150700844c8603210304a01c00c807c20043c4401111107014495842701481c10300361144044110941c003460380280000c200f091114148403c52041d10010803c0308040340d55110400306c21500b00f0840c1c1090b11008008420b20328240c1c1740c9141c9000003508440800f40e807000841c040c0c91185403411445000070f0400e011a40001d11603500500361ba1140f148909002c0010100d02d0f200440c0050290032400031604256003070204200c0001c040710801c8400071001c020f4902801c0101131150588440040355407603d24145690034090f06914180200315004814140321000920301a2081d07500300b031a00048640900c541640146940007040c1c013644a0105c400b10004504400049201030036000d9840001b04441d13002114001d01c010b45107080e03035211403c0c40c200d100e60311440016000c1e84c0041201950440400c5000d40044001d2049507132005074 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 949403075 1250 949401825 949401883
    0x40f0b0c0d05030709050d03200c12070806010302010503270c040f0c08010e06032121040c0501030b06072316080a06050414100605011403040803190e 66
    0x34030768a045082141c07a61910150040c1814111300549105004050310803040c0362003170008000d10f4000c9044c002c2e13120f85010045903941c0b100326590b841015a045440100c202c0450f000080b01c40c3d0304024811642554015505504024035107005e840c140c0c0d0560501960124032002185448806050411024810301003560301e0304010403801814a101e80b00d280b82d000b044141120f00034241a000c6848460001e82050030100d404182c0b03030400b1a242e850320510000600744075942c03c0785030f038007030001c131a041e120b0820032940034002000da03030381c1007005500039003281d011001c0040201d0303d0000c4a5941c810361040c0c040c000441034400040a2010110030000d4a0620021103014800146004100b03941c41c024a2402003001d522040898200200402e507480314103550403d89540e03040074100900142114410280081c81c00d242c0f03130000380012002c0b01c0c051504202c3d85031440d624108096040006000141d401c640c3d1800c64800f071800c01d1144090b004500c4609001030051464 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 949404325 1250 949403075 949403083
    0xc090302131a151e0412120e0d0302010615210203090a12020a060b1914030102090301091a0708070e04091103030409143105121902060907180e03040f0b0c 68
    0x907011103400307080200b03010031b0360700d680c3c1d51a400754001400b451710300e80c1603c222081038602e001150489400702d4031800300741c4c040d0003000c1500c0440f0300c42d401c0060500030031150034039000c034032507041d0350540892814540990000c3da80003148200304c0e01054000c0e510b5020800c10400303000c006030000e034118010070000d801117840020b812526026504010f4410700c3e22140c3d54030070309034101894a100747c00c0d51821740680d07100e040c00074020818003c0c9402c003d0002c0100109100300034200340c0002e8641406495060300480c800d5841030241d0176008140801041040307000c0c2ca07810510719801c1d015580806c010005040e65603404102030f03a0086c070032140500060f100c202e0f584a0140d00c0329100302d05542082000741e0740c00b850000c00b45103082107801c00c41c00b00d841c185004000202032070381ca12600040c0340c1c00700440d404c6544030340e036480d111620340b02e4602407000d403440380881480d0164503d410092105c12044180c1e4945965001030016040807980b01c03c046040c0402c00c2c1c01040380c184 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 949405575 1250 949404325 949404367
    0x7080f070306050a1e0e09150a0513020f061318060602030f0f25030203030f01061110021c0501030c0603050718051c050d120c090302131a15 62
    0x400e0600480d030a000014500301401d0143e01780044212445030b04480a446a060040c2110405c882c9170703080c910f41c45030b00d50a14852250907403e000c00070075200b0b0240d2290030f104210707031201c08001003455804c1002c219068054030b58800746c148144e41404605200d404000d00f0400700c001c0e074500b10009094281ca0856100c01c080d500700303024039402c12140400302c0d024401103e620b0341c1d4800c5031800380303040020103035191b001511101c2c595800701a0004000c6004030502c50300034415a0340d030681280e43d4503007403141d80c9168100000804010196801520885941d58501c008000e0210410402c4170700c00d130f1041d110900c01a004101c8190035200f4070303070044030310318100303403030510100c0005007040040c4a40740c003407180c00d103000c41c0401e000c820500550750f1090a5410500d00c404000706082640c1d030001d442c90f8a0302085c006910700030300312881180d030701609071082d80c4061880d150007400070441d007451007660300c948500650342d0b5290390786400d107100307800e04e40b80c801003c6031002841c422 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 949406825 1250 949405575 949405577
    0x7210e120d0e1201062c0c070305271002061801050f13050c1c02030f01020a12021b030406020a0b011505040e061302030a020924040608040f05030307080f07 69
    0x820000c1c0036800503036207811010035620720b078400301c12000150050240382c0c0501d410380d28001c0f00c00d00780c80d21441d0b29001c246807010f0003004c0ba100d1145e054064801d2900040c040b900402690250100c0311300318500b98009081d00c2c202d1082210007107001440c82c08600380042e04420108181d034082d01d002d040518114500030452440c180344600c002840140a02ca00d41142c4944802040810000c1d03841c465805001c0ba1400f81c0b003002101101400400124440d004403c01c00303c0c0c080341403007511040c44039540c1d428414070000900b10000c3d8810100c1d24101c002110a400c2226001c000410092845074001d041c0c021241c10030517185131301038109007040040d004c150b4040682c42421b8800341c0c3c03a03910b0b050410f0b840d00000104060b1b04a003254505e61300101c2000550030496020b08440b00098501c0001455010441442101010b40d41401f0340000c0c8414082d9074441d844d4654000e00c01c1500c58540d02c400d03203c082c80d40c2c1049070000001348a4008102204801010b800c2d007100305 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 949408075 1250 949406825 949406833
    0x1e060303020a0b10031b03140f1207020a05040207080c07080705010c03030e030c1e07081f0c05160c03030e09270705180105040b01080f0103060207210e12 68
    0x255500291200d0141002800c20200280400c03031800d51040d000c0025503001916400720480e005c0c0703201c0c01103051311040e54200720b10381c1104091600030074407541c18003000001c2c0480049028108809800064050760030150002020403540c80d1032005108250041c1000340e02c074821500a0b9141c000d00c0c0c1c0100c652038100c81010000740c6d070000866180103506080210f080044007c413180f4500a402a11b08107124881c040c3c015941c130001c3c0c48445500f040c00f0b0710121074444003002e50310000b401c80c1c28250044403040039843c8500b68414514400c0c0c03450440d20b422055819400507003412902038941c01c00d40c0c94104101a00400700c82e880c00b0742940c90051910b4083d0416411362a500341c1072550b0803440d6010301d010b040611004001c0d10005180500c10f44801c40301d9075402c0c0090084a0080d4580901810658020b40615100b00801c5030901096030071652040b001c0c0d08040380403240c415201c00f1070020010707005101d0b04203018035079840c03001000d1801040300c1c2e04007001b500c0203142c06c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 949409325 1250 949408075 949408079
    0x915060d0314071e12020d0f09031e080417060609060102100b0a081515030304151b0b0f070306050f06090114070605040c2405030601030c031e1e06 65
    0x2d0842c245941c0704114900ba262240540e0514004103c00c001041020211400a20b01004000b6005252407142603003200c00019030510240c40801481c0c403440301186025904100150311582454480c80004840c01d540d8451036468090380e4025802008031000300024130605c1840030050725034071180c2103400248600344100082c0d16041ca40451103c01500c4011a404c01d0b112400e09a004169a408a42500e000c0e031000c0d040003882954101c518000e41c2c3c062040c00e18001050b0380c103980d444004010210820042a0707094818105882003400d5440400008141c0781407955104050000a50b0118648050001c044881d941c000c42e1158804564502c410349540e019103690600c00e0900c1180d080070342c101a5480d01401034010480c5007800100710412181c0901481110801000350301c001743d04200e19070b480d45400000100040d014400a407856100750840a0040700c1410300241c4000302d07030402110440c041c032141015940f0b40400f5072400c820a152904031204080c020001d981c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 949410575 1250 949409325 949409327
    0x1060f0507150203060d15090c14090c0c0709020703090305060906010311040e0c03190506100501020d031e0c02010515060f09040509122109011406040507030605090915060d03 77
    0x20102e045149019038003100150281c0c8900c9400141560031600e543e00445012003101c2c050855101c085508622001700080e00c1e02e00680c206100400040c4000d0607a9103c1c4031080d01504941e60701c4603036101d40701001030105507a100812116029a031100342c11400e60520500c1c00c4409071204170180d01c044010804503014801050f840d190444003ca40e08186014040c500030003844469418000d0380650300102550030901c501c0c07540b01d04180d0b03c50350780300459144440b1061080c0d5001d038000c1d40d00401105d110742d00510034034501d091600004110400170904803282c1c0c505520250307546200340401c403601c680c3d84d144040d4040390038a15082c039504820200740144075106001d0340d01e07a40070400c1600c0600150410000801145483b0000540a80f020718402d048003c07444002c6804a0034010042c080c10850101a000c41301c0b03e034480303105000003010010030400806544041c04035090b039600072158040d0004000800c0c3c81203048101d035070301501c00b9110b288541d408240e080c0c002 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 949411825 1250 949410575 949410593
    0x9080a031a2404030c0e090c120d12090807031809090206040317091e01120e0618120a0207140402070c0308071104020301090e010c0203090f06030604110f0301060f0507 74
    0x100d03000c07070410b1101d00d18001d000014041c6402c0201400048103006c1903180c50640e02c2c2c0e1050700414100c446019903c1d00b44003140340341c620080d003550008800d400d4603a0241041c160044084100000e007801543c80d480c0e902c1e00002802c030300041010458418041c04030f2041c00290504c100708100d184c0c01c650004107d0300ca00d10004160612181c6188508124001074816a4102620f07079110a035041003061504c612805145002c54140c03050449000907611807403602c0c1c094000202081d464080001860030300e2005015014420a5004904039610300090420740803250028031040c0c0c10036040d000f141001a420780d01481c418003c841c04203a202942c1e03400c07070b904103018035552038841c01c2c0301200348801c0100d690840e0001000240385800b03179000e00c00e450600c000030040541c94000c102e8681c440d031065158018032031404495249407040080d0b4100030014070015121250b207034101059001100c03100036407030b00440108182c0703400090140040031350345061841d14089131358035100 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 949413075 1250 949411825 949411849
    0x206090a03080a1b0c1b0b07140c03010c020c01080c0910080a1b050a030b012c060c0105010f031a010b19021e060a0f0209030a0f08070609080a031a 65
    0x2002861004101032440303c1c0d00c9049141000d10f10b088000c55103820145c4010411001111074022600150000e100442c003030742c0599003c0400d8a141102d41e4035150030012140444101a014400041082d07907400d00c00c0140703901c91500640044424003001400f081c5005003403c680d11010450048240d071240329900c22029030b030506000944135148410002e02c688820800c0d1700030300300760400005402c4009003011765001e640c1481040e030340c400111140800203400c0340e000c005201d0b41e00840100c000c1100617411000c0c001c5410220701d00070090940c3c0c0c0a0b0300c002d802d0007603e0002d209029601e90031080c83c40040300e054919501d4a10641014468000846c1c901046890b500421610038070412590b841c48008694010300f099010341d8454905449a003d62840c000f00320b408041d00c0d009807140f580004001d4505c1e0b08140c2c0740c00c2c1e8441880310b42220b094004010343c03400100503204908601c0c3c013584802e40c41d41e40c40b28010341112565400391225004500c000001c40d5501e4100900c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 949414325 1250 949413075 949413077
    0x5012304062d0f0b1305030c0d1113021605010615080406051803070308010501110109050a0219050907050315040b100c210e041d030f090d0c0b0310060206090a03 71
    0x2008484014a08001043d422a124072140c0d4203000034a08050005440900c2a00c450000240c1d0f85030209641e448405100e035400407102141c03a804118800c422003006480948450a917020000c4240101d900050980305601d42492001c0c0500009100380d80141c24031850300b0003800b144c007401900b41d150041004280c141c46800044c00c0c80c040760001e140c5840b90000301d0f0f4807240c2c0381c03070042e10001c404d0080314001810183c40705c0003207905001d0050540c3d0080050001450389400344046400d04030407ca1160703480880010b010744405510500c1066656209500c0381000604020074010360484d0070b00c203034203052100010740e48280b042e4085d00d907541018800340d03c45180a851081c0048000f0340300c1152030304038820040e004040d4000502040b242040010303904041c0c01711920740c40c50303100010390082c020900e8400c4c0f410028900300c0c10041034505c110340540e44001000c0380e150440f110908001c810302071408038006413000640f81d0342c00505400d281c4450500c0e0b03540034054000d8 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 949415575 1250 949414325 949414379
    0xe0c010816020705130c03050c0301050a14030c03070b250b180f01020324240703180605210c0d090602070506090604050f0102180111100501230406 65
    0x41c003242c1c020045880101805414000b03c540c0049001c2d000b8456061000702203810301c8001420030480c0000c60341607031001440c40c1e1186085c80c4200300c0074041c40305a00e805101e00e0f50245400c0c0d404014000080140c207080030380d2219211144110680c4c1d642e9105908542080140d0001d409621101d60100d808a80c0d000001105800149000110200c0d00304951000080c020304003815070003103080014040c0e90300e10458112040c011321810407035084c0c8103024200359aa00c0d21060700010800d0a0007481d10f240303201070b0000540d841040903031118001c910700007900101d64026200203595906a10035001103842c01040c0c0c038940e44610500760582564946444003080031310b41c103031207a540e00003040340c09910304030346e245640703a005a80030386480c4110710001c05502414003c030745007100e41c02400460b840c400300c010740303c0c030614007031071151409070681c1c01500f8016481010f008015404540e00d0204c00006828400c2455408940c021400c1000501c810160540c50607400d610a003a22 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 949416825 1250 949415575 949415611
    0x1d01180204270524060306010303030b130c05040e1509010303030203100e1006140c1207062a030f0905061504141501090609060e1e0a03050304090e0c0108 68
    0x104568620b0390241201c0c40402c1040740060140c0000d140030090f140c00742804204140c0d0160460003c001c5990503410745c01a0010300000c0e1183e08000912000030348a8946507103410f400c941070311051900c0a000a102013001c106040541c100c00c0c0c2c114803003000309620841180f0201d0300700c640502000c0c080c1600000840d01049010606400030501071070081c11a0031f020207c1301d41d28000e80308540c00a4001d00d0301000c11040b5404032200000341030010a944656035a00010b150007010098402035502c2901100c034482c0c00c144403a902d496a0f2041d031002520780307000f0307044507501200ba00b100c40c41c00100c100010f900162040c1c10820745030002c046009050000b0340940b00c40c111640a80ca005400c0c802c42c8401d00d4a82d85060b0400d803201c50100362903102c2214000b105100358000151255140c0300b05050020381c49900c2541411910003c2c010040400c10140301984212815480054108042d03c860300c933035072244112501074011181c4500c0001c0c50907a01510154000b41c0074028 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 949418075 1250 949416825 949416851
    0x90c09060d1e020d0603021315180f0504320c2404030b01090e0a111c02030f0c030601150f050a1806080108150403050f0d0605090108011d01180204 65
    0x80e50700c401c5440b01d01550f41e0142c0284250280c0240c2c03000700d0150407246211a00e49105000c0c1c00b10b039811283c400e040103840c00c007c48614001e092900c5214a0350b9020000d004029400350502c203a0044a0703002654000c9403449400d400c0d01d050421321448850700c00010601e0201e040c410030b5004480114546144a4082414a0011281c08420380002070300104101d016062141281d410090401880d1041c4d1882c0341c5481c502000203044800c3c2c5400103820b843c049181d007071043c15800e80c42400b00d44541c0030a140060b180c54582d40c5da40144407160711031030100003d03805081c10b141008022011000041d08600d00303641041d052040100c0e080f101540b29a000480cae0388101000500700302d07951134021b0000c600038011000180a0542d11450380b50409403954085c90b410313502c0e5447c00b840303507840340441d0f0000c2c10340380c6109858880c000f48540e54801c400340608004000042c7d081c44900521105903103444800c0304a13410311802c2a414180d4403810b0509540544002c654141e102d06 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 949419325 1250 949418075 949418111
    0x9060f020c06190210090b0402040f0b130f0c170105010c020d1515060507050d1d040f0f05090a0c06050a09050319050106140a03060c090b0304030e090c09060d 70
    0x2000c80d41200e40030903152105001640307044050f003103d030280c501e20f4080c011030300107840c100907010b815603c4501c0420010706040d403001d00301c0c0704541c40c0006d50403804d4000404400c1062000552243c4540d14007041640c0c52182c82d5080359103061448076428410034980da080414880d060501c0700704170280c030642d143c521041040f1613000700341d001d500c03022210f00b2004151819000065200f1060086840c0380160101c540080d0008010500e4011501045516140da544043000c070303040c10b000d040f459071618043ea80c0450040c400100b4141000324419044a0008095403c241c7c456680840812880501e02342a1039803842e0a60b5101043c203025a6003034180d0740002c3d011701c128024101c0001d6080102900503100707000a0000681d906018000011104019980300b0881981080000c0080c0d2000f84d4003043ea00304041c0650b90340d08600156081228203402243c0200044000d505c0d1041d10301340d01600b070609440c10034089102090b110f016007442d4070380e4155291080b10602803400f07 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 949420575 1250 949419325 949419343
    0x60306030309060d0c020607090b031609150305150f011e0e09041a0c0309070611010e0105042312030f060103201b0d0e06180a090504150b0109060f02 66
    0xa0f19031a40d451407800359100520708a407035400180602e0000c120501d114603140d03008c40d500c200c283c07419070302d820840b0342c0d2800003401298180401e00000140c2c00a04440001305020700da200000c441c5400d00d103c030740041207081864820850704102010503a040019900450a006102a842080403109075440d10124030300d6607011040384100320422400401c50f13040a840a900d109480d100c0d1895802e9602042d640305103581c211035014000d242c400c6000f030750300b401d01c0c0001158a92348000d01500310740c4203580071355201c0f14124403555800071008144005a207508002d0248582c0020511418080a00000720300041540440c203660f01c01d070091503600c2040c0d04950b0b0385413003444920351035a01c030860070340c040d00f805042e000c5000000f00716003140e40ca668840d032250444035810040c8690010880d2540da0040c1c900b036a403581c07100c46906010b003070790043c0043c00e07040c03d0400600510116603030b05c0d01c0300c0c02c00300242081c1e644070b980c981c00c0b64010704081c103801092140903400c001c0c4c40 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 949421825 1250 949420575 949420579
    0xb092205060a0c0f02060405120c120f0415050306030d0c02060903070b09011107030209040303020a1803050307020f100903110111030d0603060510061d010c05010c03060510031a060306030309 84
    0x207a8180301c10707a0b956502080101c3d4043c0c03190221452607103820303030300c4100844000d0800d400c100030803040e0740201e10040c00b0300c03050082502d480506c9900403886e607400c9490481100280490300703014030800100d00045040706402c0681c00d40c40c01c580004da94140c0c0034006001c10200140071421925180d007601c01d06507008059441150b190241c031049608071102450014403038400113114890b0118078001a03c0d0083d00500040c2e0302c0b030300d06034069030201c803048042051001200c49050440d0481e080510f21403000307165036880900400c051040c404110612607055691450180f941015058003240e0744401c054000c0300d44200140c4991410110603031407800005012506034906610100c16244903c070200a2a01c0300c590b120f080c1d6006006c0c034000b20b4110f03598950b0081d10008080d10404051514100c94451596500e0a44102003000700110341c860109004900e8100e9200c0c100c00150b24040041e203600850010700d4180340003480380a902c0000c04200180ca0600032030b0002000 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 949423075 1250 949421825 949421833
    0x40917070609020f040b090f2a09030d0f0e12030405220609020406120e010b130516030c120b0307050402070b0403080105060906070605090a0209150901090b092205 72
    0x4500344507029051100080384500e03516510b1900618041c4150314403000080c21515455449500c841c0d41040e0140c4404005030032810b14581003400e4001107a041822400c04030b840f07217048001e25240409084c01030741072000d001c1c0e0b03c45849500201440c0f0045085401c07000740c1006828607400c40c82150002070300440000380c00d030720b010441d40c03203c07101c000350280c1004107a079a150302c40224005c2d409990000340310070a6aa1128080e5003280002e4200b0500002d603580c01040081c07000400c440584102584600410114400c929070700040035032281030500c161440c40c00f005042c002c4651000220b9540e414824459440c00c10024003d0300703028008560340c00341410501036658040b1800c50005115000100e410304110301680d0321b4040260905d0304022702503031100090f040c010094400d51099400f9040903a07107000341140200454500c130000c1c02942402d200f10810160070000c47c49040c900c484e101d40d22103020340e50b44400d0501a1040301103030f40a044100c000e1001001e00207101d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 949424325 1250 949423075 949423087
    0x915020a050c060f0703120b21100b0a09021c0606050405030f01090206030a050606090310020d060e04151d0a150c23031801140615030411040917 64
    0x14000911030401030099007140c101c0c042801c20410035100d046165400b4034014041140000c0c042d412034210103a074004041111680600424500707074130140b4035500c2003001d100307528001c00c0601c48402c40c10341c011001d212074500c0d000415201030340c9200b14503509a0000e040d2020002910b540d103035400040100303002ca19956034005119401c68011144680100d0020410300141441400c00150740a04000e003907984506000004140091155421803c01c01c0300034500c3c0c2d000d010b0050344218504005032905540411340044415607040904280701c41421301010a00d100741c0420b0b08a81c1d40300c0460800400c9803994442e0030340c1000c40102d44500709e1840c0811140441c4400444001702040184500c2000120b030329000380b90340c55401c0180103946210400000700259880307034210305500c039000051101c480c01c41d00200003029007400080280b0000d40f80030102e441c0c18000d029506419810152581d11812104002051060303603a00b018804203c035501e40c1e1942440000c8030552601 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 949425575 1250 949424325 949424327
    0xb0d0b0a140a08191e0b0708040b06040917030901150312080703090809010e030102131d06010513090c0c08030106020c03010f0c2715050706050603150c0a0915 70
    0x92a44918140b1540359a040071541c6900062980d40b44c00146400f154050141d85403424a09800c034130100e8214004503c00e4042810031001c140500c00d80d0380c0300910b5203414203016800382005020648034a0400400f00c001c5141c203080b040d5401c0000c03904a989882d1034080300c0c010600954041194030740450000244844080205100c090546414046540c0c0c6a01102150340340000100828018812043c1d01d5200c0c0750040d00612000e00014500003104117204c59111090b07010410120001d2200b071044040c084601d5044442800c1503818103a00c0144512200b001e03001d40c1808903130f031701401c040e224441c02c002e00311307950031400041e80d950316250000d40304d507081240140030390b0800503201d2001c0042c0c850300b4449541aa00d403002c40003200481c110142800c1cac0c081076441c1a0301d00c0403801c117041c043c00c01c004031a00c5d242c05d40d9488061030054190b0700001c00062090300804642e03a010040c6040e4035a01824101d041542d42e080480c06454151807034000803034500c01650b81d1034840b = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 949426825 1250 949425575 949425599
    0x6020d120902060d05041703090c040b1005031305100903120e07060f0f051b01020301030c0f03080406030b042408070e240607060c0504090e0105100b0d0b0a 69
    0xa0245903880400c01009001290140c4000304002504003104100d12403800815620164101d8031503200c1000001c40c00c0501c0085400c00d031080307030141d00141c2001065281a02c01c2803242c01081d150b180b0a00c2e800c00e8042d080b8080141500c00400c075160311002040781c03e01402401c030b00180401c2140901c00d0500504800045041c54601c0307107030002061901600003181c2d02110344a940724140000709103070480e250b84900f141d5500b0702c0820b20a84100355078249540e03c00e407810038001601c0f9803460411619525036a03005c01403154003c0d80900100724880100c1d016540c0506020440b440307440003041c01400341e8039403101e030880001d00800070018086510800c540c6020210342e51161110054025240140d80c0704820681c9100070b10403a150a01241c84c2d2803d00810007401c2c400b50f5290402612220301d4030a00142340010184034502c040e02c00c4040142c0d003013001304a945040400d09940001c603005022410238086000d0030103c5040d0420b03006400042c28804801340ea40d0204071170 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 949428075 1250 949426825 949426843
    0x213090303022515360302010c08010b073f020609030901081807080d0801261515040e06240114211f240503060d0c0602 53
    0x82c1c0035445403100418088101c809640c01d0b0410501e030707060030b0014042c1c0010410b85004d207418064280e0780c103490500d0780c040c08160b88172118403841c0c0a0550b1800a0840b07410300b0300001400f00040051040440c08011744144562190100014881340d0302e00c455100d01200c80b0711f001c4202440b10342107108241e0640d00c071021441d002c0350400d4a801d402c01d5100d000d87c4206900082c1000b0004510b04140340501380c8003104a8180c4181c242c403210000c0c01e004032803941101080c1c40c0c1c00100185035001c2c081d074580a21010724030030244110b1445644800000b0ba161000003101400324003450140c0c800c05404940040c000c003c040000e00308c240d00c800c1c08a40300100e925460101c1e03004170b00d00c100000070303000c0141e6500203c0348a240c40c03015240c2264000b1840100d00090200448008000a80c080c0c1510001d180c11130001c20700a4510741a1504203080c68843c5801c6121160b4a04131500e240d61a00d04082e0740300e958240c0131401105501c01c016150742d03124003001410903000300740804 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 949429325 1250 949428075 949428097
    0x33a05040b280e07270f051b071a0c0c0d090f0b0a09051207090b0402090a05210102030103030914030a1524060512010b04050906010507061401060908160e04030309021309030302 78
    0x170045046c1071745c4a0842c0c41c201c500d503410208000c40a00720300000801003508134414080c0880000701e0180c480c500c60780468141d034441c1000651460580010017820050105c1803400c1041c40d0b08040019140d84100c0c403030b20b191150f0120303100044070b00500303041026002c06400e20940b15034801441740c1d2400c041c49190491403400c035074400c2c581031a008807919030201801c1640b11a2401c0705020710700e10110f08407030720040002101401e1100c00e00046000714003a5540346585030070a0041c50900c65540e6516120354480c170401400610740610941024001050010360440320320506400c000702201900044500788001007101ea1302b0501401052a220a0401c2d4507a00d1f020b402d0810300c01c82c0500c550000700f1000088a941c8507000400c1003510450010601424486401014071402e81140020403941c110500c500402009418141104103042510052400c90b1500083e480a40040c04158445003084155110103900721104110180200001121410014001e411040c1d00031 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 949430575 1250 949429325 949429331
    0xb07021c0b280207110d0302150103150501140904020918010603050d021e0c040f0e06131514040f03030222050a060f02033a05040b280e0727 62
    0xc00d440d0114420341d030a0300d500c00011a4141111317000c002c0700c480c03464011000c5108050000c09020b840444081c021413151081c074181d03a0300700b0054001c0d104160809149007031022802c030303480c6d40c880716143e412540680d03500c12039031070b840d07610002d400600c1040d050030740c02c0820020030003031300141c11515060a43e080e14007181d0041c4911440845580d06201541d20202e0540014906a4084034500503c0c103000120038445030652820040c0440703582606a00c2a00c1300024401078030310001c28a034018004110100030300c2c91035507101e01d0207000601404201480001054080da044607203045110f0b01c1c10b03440b004264034200c503034895401018019403c0701300c00180c2d0360285420717409499041d0042c5007841c03d100c40d10744042420103200c094030b5104c0206114500341c88400e0020095010102003440c0c41c0505142030300c080064030059296002807107418600c0c2c010078445e11080c0b0544030115001015030005847c1c03407440c0d00a40f101c95201d4051414050207403007d11013510b07151a0038 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 949431825 1250 949430575 949430641
    0x41a2d0912030f01030803090304050a0e0a14090d110c041514010203030f0a2a020a02040b1503040213061a1207030b030705040207080c0105010f031a010b07021c0b 72
    0x28610780000d0f500c5190111103c0014400109030401443c2d0180401c001c503030419940714001317060000c1f2540701e540e41040030414031a002c1c10901582d038041c1c8103408144407609121a009a850702050881000c0202d101c1d00319810440031721079070540f40c10013081031010580c04050b00302d250f12a4407422070b003420500c4170320445500210689120303081d00110801180d83c0e944118024010b036a00c40300701441c03800c942030344564064400f904004103a40c01032220b8051803040c0000c44a4032030110744035a40d008907002640b84807400302e9a003e603065580307007050300055680c54090140c1d504031039101031000401192403408400644103001814200d07070840d4803441340580403159845509074050700a007000340320030b0400b40c0003020712034446e848207450300050a080320f0031a0360a810125108203061010000d200001c00d182d006251400340074559945440407403981d40c071030030b10002d008101510001c40c1141c584e80c1000c940540041d1001000c0ca403410050500100e070081030202881000e01c2 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 949433075 1250 949431825 949431853
    0x90803010f0e0f0705160f02090c040801060b1e091306140906090601080705090d0c0f0317181e06070b04060617030423130b09010e041a2d09 62
    0x90130b0080840741c4441e4039201c00c6500c11a031180803030900351250035010307501a00603120030020521500c0c0d07031010540c5660420041c6c0d400d40700380d82e0104400480c20f004168611220303120140c03500740d5155010b0354580601c40812070041c0d807080f410101c07a00c2c101c2c0c0040c400350f21111110700080100c4036580702c0da440303034100050380c20207689050010f4030040001e4440e078014001442d001d00b0060000c28008500c0d82c550b0b40021311174001900c0004040010010044070f0b55030300d144000c0c074103005400d0812148400d51801200d03403203603114015002e10362030b802c0d0841c008142d02c01d81c0a0161652400c0c00c1c1040a081c4100b9203003100d0b11854154002000d011581d4100345101189000c1c524107443e111800c003030a44291035602803000c0c51400e0303c083d9500d822690000a000d2940410241801003c02280b15016030064203515034540401000403a15100d0302c0044055420146050310303021211140c40c0a0340308411400c080590700c14a8540c041300041e841a1300d244215003a2020380e140c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 949434325 1250 949433075 949433101
    0x18050604090f24020703030e060108070e1306321f2d03030f0f03140105010f0207051009092703110f1603030329040207030201090803010f0e 62
    0xa00030b0079042c00c51101000181c1050840314820f40301e400c0e4140307040b0300c400d02d40c400c0703130f120890480c086aa100007070680c120003884a07030b005000c820060300010f85402c1d80303070310009001090501c070300000326855001c00145501c203402031071510401c80b0306c0346d09009040b070b2031040819560b059011a100021a06403070701c20034454103050013041d001641e1520b200c64881c8410010103118483c00900040c4100340d008a013180210302964410500b0060340002400b4400640c06000803d4140f056a1036050300ca8a103d604541003864260782003004560202d00f00403a5820059110954203c5141841c0d030000e495015a0008002048001d8030003100c20041da0b80c1101d420000c1c01541a21404030380680f0505c580d401e1134605441c044d07101c0004960604003411103180c03440719814014020316502d8810a032a02d4818080010310801e540c52000d8030f4902911064819034000944104151003074008905650380040751503200c0d40c482e02c1c3c1c0d0381ca01e1414040c1c449044945800a09500d559074 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 949435575 1250 949434325 949434341
    0x240417010b1905041a0904080301030317070903030e01020a05070f1701021e090315091c0c0c0527011217040b0304021003060b0d0605010e010e06030a0e070f18050604 73
    0x2c81003041a880c140030f00c4060040280203000081801c41514629210400c0c40c2c0d00c074521446090390742c0e42c1103280c0542500d5003080d0003010351000324100300045421023400002d40e9010b0400b500c01c02041c1c00101e1a002000c41c00030802d0050500000d59035101e0904c0d50241c541e072007030458440d44488107136402c0b40900300001c456890300c2c4080940300000c0900800316100040d0540e400c13041030000004a01c00b00fa5603007600390340990903c8640310b002144011114001d0b10341600340506644030405c0d00002802064400d80b0b8000c0281034001129040f803411000d00345c440050340d81c1d210030682c04642c0b031481c00da030000190f000c203040108041003103c0a0f2a4226403042c15034807103409101d000b99150403090309050340e64002041118244c070152222442907031020031001d0a00c00014155803002e01e071503041c012045180905030303a41800b40c0764030407640c290008540101980d00c0349019180e6002851240c1d0031b48021401130300c056404141444400d80c2071049850301000d00048420032 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 949436825 1250 949435575 949435609
    0x3050405100e220f0501060e0f0105190507060c02070803030c0a03020421150b030d0e0d291501050a030b0d1b090b03030702030309240417010b 63
    0x8100602062922101151030305240e45440c42e03010315401d02160318800d40c908020160094030700d410b600c0841d103000fa4054900c03000c1c0b060044d54500140035143c0b0800d403048030b11600d1045901413060f40328106454444461585900e0b2180d503141028009078054070050755850700b05074070181a03900008401c1c0480350024000d521f19a0f611902c254560001c4500f04101074080100080807030030740400c082c2a1041251a0045030b00d14680492050f81280f81d00c05440e04101540704190f4002c03030100e03660010341c01c5c001107411545001428030310303a184000300903070141e61822440f0140d400c45c80d2075101940c0505a10390300c64002c0c800b210050301298500150040110711103a40c0319400c00c0e030700c9603405428540421021f640f140c038021030861407002240d5407030b04100440e1780c0500804030743c0f07081034010310302e001401c1e008241c0b2031143d011414015890b00b60340b06961424a4903409041c1c480c04c00180d180d81e16080c103454031001d040d81d03100c420760a040d480b0009141a4884404004031 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 949438075 1250 949436825 949436827
    0xa0b13050103230f060c04090c03050903091509040c0201050711010b0d141f0b0a060903020a05102601030201031a03060a0e07030c030803060120030a0c0f05010e0a0b130305 76
    0x2240e842c441c094540165042410301819134102d038550f40c1000f80c54000e80040f0314140d252400d0800e95021101503a105e00100750501c0144551200d000c802c40e20458402c2c1d603103100000c000c0148402c54450311400b65003062416052190940d419031226000d0840c0303503580c40c2c401030019a40e87c2a1180140c449601100710145000000c080081c2110b0b200210340548910140b41c00011502c4014041c204107800d0b201d100d03401c02c034070b451070480002e40760b41d00b0b0800c405030075900441d440d0282c034001c042c011444080062015400760b078503104c00444a040c807d51003039031140a49500340080c80200d021034181802c01014284001120650f840060700034030f2550f030f400396050003403c1820034285650240104c0800800c9a001a10020394022102140d80f81040303400100364514500d6103007546c2868524054070180e002c021100d040b13101d17145c405d81c1e122150038404c04034000514024402c0d807924900c0c1c4481000820f02609440c058006803c40e80e035100e9002207035100d245802000910 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 949439325 1250 949438075 949438103
    0x1a0406052802091309050a0c0b1602060d0b0303040611010b040c12090204180c030b070503070c031107211101031b180504090302030c12120103030f11060a0b13050103 73
    0x75281d016001040008010b6400c45066240c80d400715040c6481c151002d40002c0c0402040c0224100004010400c1078840782c5001078a10840c1c10318061908002d204010018000c16006100d410864400400030305503540c44da5581000381030b0a1340d100f805003255003010707541e4140e03141a11855002d001380380c844050701100b402002c002440f80e10000c9038020794500c110948019590403e1400314031941003041110b0440c00c21400b8010000c0c0000c0400c60101308014041d0b9000d80c0d80c101c0c070703641400d1081004802648850806240f40c11000c0840d550315042115944400e840a0101d40551400b0296040b10303c011025244008400b040300810312090090302c034412549450301d250346640c103403075041d11000046c00362010740301c0039001070340045650440020140a50070001200002403442c040c6102c0100240e07181c140300c080c0a2040c4a1070410145000d00c000740403c00d40740f01521810b207014076124000300500031b20035000e40120301d15a00c4681603413103598141c0350004d0702003a842d1 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 949440575 1250 949439325 949439401
    0x10804020111100203010b2d0403170f131e050f0f0a120803010303090e01050a03060507122409020408030f090102030f0c06070809010c090608131a040605 68
    0x71028200504103206603c14103100500764030286000c2e1982030000c507519040303002000c8584041e105504000381c0b4500103080184442e00403035007100c4c0d01050344e03114980d040f100c0003282d005030803001d28040310000300d100390301007040d003418255620300801109440058a000c50040b03042d004094100d4000180c0d0103245c034060400c54030f100c5c4001d00300030203284c99041031144041c8400080380d00100110044c070070590030150050240c030191000900d598034050014804059600c0050071840d41c880201d682c452141400c91120b180c541428040600c640c01c900e01760308101501e03001e03542004540407800d801309008540858140600450403c498213801c0c1c5101d0344185e00311819403108012403266107043c2c03806010140c4d010006841127141880c80a00241001018020b05914081e620801150000f205a003542c1051401c00220381c0e0340d4000c41030013400d40a01501c280c01440d0707031000150040d4034072032045210782001d0000c0e032a006040481c05080f4160ba0700504001e8a49420702c0e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 949441825 1250 949440575 949440587
    0x61b1b0c010306082d16090515100e041d0303071805060c03220e0f10170d21020714070b0a0801030b1f0801230601020c120f031c0e0307020108040201 66
    0x1171324000301625122032802ca072140307510340380d50700c401101d0b51502c04104106421082e030010b451010b880384454030720240307001400c81c03480b0503082c1d12075541d03003805503188207050308004144100c403c01c9075030b20b0410140140c000403c064002d000c0c603442000200740e90403c00140e5510800c0200218104441c40c801414902050290b00304a0342c81707440b0000300080c1e058000b82c011202e81c00300805a080900340026141d45c2130b044815929500d0840605101d800510414426501d00d014003108010403505d0701d4108035000e0541000b4004075200d01802020000003404000100485022a80d60002110207010380312500012411b00b10040001c00c600b0303201c00d544010364492a50f00104000317002c9030780b112150000341c017981d0340c3c507a5442e40c82c2050122904c10b05281d2041225441e041c00000d503510f00f8101c1142c000c0010a010201401040140a01254100c016241c407030180c0301012000510050341c0b901090b00f0818402c842880200486900340d0301a5503056040d95950019202 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 949443075 1250 949441825 949441903
    0x18060a170136320105060304080412170307030f06171c0210060308030f060f060409020c0f010606020c090a0c050f0304050a020301050103050318030f061b1b0c01030608 74
    0xc0039154601800040070420021140c80a441800000c0f440c0c141040c1040003016000540121010014807000c69000303c00d407800c482c05051415100101454155083c60038407007000c0c1c02d0302c0080305000301c2940640140e01daa580d06402044031f0366540400644108071310749021002e070414400d204920030140107010501c0c0c3d060048131150f8030312070039400c100c2d04a50b000341c0d9100c00210601545150540c80785030007800c112a4100c80040002c00211644100e11803492141d5001902540656080c00008031150880008002d034a640d10006510740c400710407160b108800760f40000b0a0781c505413186200208056840781e0500c0710711101044a5400a130041e503091003041007000041e5024000c503400b843c4030b400171b9a210080350381181c1ea00320707503c02800d02c650848041d0f8605400002207003580310500c4038011070318101d10481022a0702c00c000442e50b4180c1515401d80790b000c2c0008007232140c00000e81e001c0000b0bd80c0e600034a03448441e1030b561400c060090540050240c0100840422 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 949444325 1250 949443075 949443179
    0x140402090711070f03080301060905091905060102150408040306060b160201212a0203070b0402130204050d080301081207051c02030c031308010e0f03070818060a1701 73
    0xf41094503a8641850714442e980100c400840010041c401c0030b52018012001b40015102110681012030301510020f08810a02c0340c0a50741c1d90000b01c0c180c2c82045491185010480304010f90f00705410901c001c0c2d40980010388100d800c0039000602e248085044903819180d1f8400d05801201d2640111081c1003400d00c500500700480e40c2c0000340884520424401100030107100d84442038040d22040101d082e4130904055401c24000000410000440264441d5045440b825019540400744000b4051900581e0b081058030840c40200090b0b200154107031400242106d050500b10208003071036104401d0000d155401c2100c005141c0e000219181c0c0e0036004034011f0745c2c140420740c209540b842c0c00400700c501c152001d2030341c200901c400c28411b4900841005001d881d0810402003069664403c0d11402000b0500004907114800d58a14044034a40c0c802400180d4401c1d1640004242d100c3c0d11000350082e02c1e000d40002403294203000c2140488148207040014070140442060070041c155032011 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 949445575 1250 949444325 949444333
    0x21091a10181b02010207020103060b0412030e0409050d08041a01120f1112070509010b03100b0f0906210a09030914010c0b1e0f13060c18031401140402090711 69
    0x2015240c4040780c000c0b51810f500050300c51106d80001004d944591307000080d0a44100014444089040a00c090b0310341c060902c241514805d1000c41c0c020840b00310090f10502403214105041d661120300e140c0100d00a01d615840c9608040c00381014100030300c101280e03e5111840d140010741c0a03801040c123203018902d0090703d1211400401c100d501074a0043c9020780001d0014086840c0001d88d15003d0840d07000c0e0241036142040c0c2d0303203e1040141c0188401213030040750000300321a110085a01402014101c1e40e120788114620341d1045010301c550102180c200e500080ca24029482403200417030309903a500d6504d0b4640421807650800300c0c0c214504011060202c140400e99500d100b601401080c2d044010000b070008881c80c511002802d03007201003000340c00b800300c403c0041c0c0c00c200005130070400c0050440c000c40703c240e60b0074419507084e9000c4150755000000b480680e0140c50f00c0e84540b1402808060911104480d03101070499000754005a8a004603040301d205101c1c000b00f52042ca401c075 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 949446825 1250 949445575 949445591
    0x61706100f210519050c070b09030f07060b040c02010b0f0f041409032101060f080604020c060901150f0b07060b061303050d0905180402010f21091a1018 67
    0x2003011800c007400b034103a602da50520400c3c082422641c2c40c1400195000c200b90f0518245050f034510032014007404c442c07401804141110000d2044a016002990702941e403143d0f00d241210140c00340d04942c03803003a171401442c052414011b00441c4140c00e0010701d4030300000300040130482a2015101142d070080c1d903500c09103074940c2401017071340d0050000300e00968440320000700031440304004842c1c0703460180404004110268010030003100b402560300b441d00c030559460001c1002805035141c0504d00d48100802d00c09200810360015914160820030f8810300e60300c41c0d05641c04420342d032155109400c000c00c81e400210300c280c2e10036944420002c044a15141d50014601100c0b0701036001134800c3d4105520420100b1741209407540201419642d80d20310030301400040719110390080c4041d0501403a8003129400900c07500a2000102901042c1030850440300c004800612002c20704861403400c000e98214920440070040303110740d000060301740e20903090514203032210b80783c0781c8002d001a07116000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 949448075 1250 949446825 949446857
    0x4060c090b0c010911150a050d1803080405150c0d050a060503070315050f060904110307030b1305010e0c03070303200102070f020321030c090a08030310061706100f 72
    0x8104000c00d0718000304116605041028101c408400c0d014411b44001c1e2031602150a03280a44450511505000c0e03164002d50090301c9c06000000c0201705980101c007450004c0580000740300c1d0055005008550b050000042c4017135002d40c00791041e440e80300d410300c0600d8030200365420059001d82135980110313180c0e070b4030070100e4130b00039441d0400c58000103400100b03100039440c2d228480c0c0c084817000c8941f000c0c0c201000031840407032000d04090100f01c003040380d54019032030401c1040000c0d90312000755402850310350040719400b0051001104e0f254240340c19206108400918180d4807000180501501c40c44d41d50b041c1e581d80d600c40b180043e2800c03100505221103c0a1010b000314a00032500c1b2220945644109820070b01200c9081c00c1c1c081640900c0740321103040100340c03640303c20541e001d00d59510f00c1d80006000e10001d0b43c00010f05100000400c031205801c035070035008464064503940102c0c01e0850058202600848115401c0204450340541e41841280b00030710900c218100902c0e60092080 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 949449325 1250 949448075 949448077
    0x40503031609030c090507110c090a1119020d0f0306140f0d08030c03250e120102070c17061006020316060b19080d051305090405012306030c150304060c090b 69
    0x100c100360300c5d943c480c00c118185400050761000002a0f0b809041d8200d80031002030f03210b03c8090041c0710300641c0c1d0032140c01c280042c842100c04840d03000c0192024098040740c001c0d690650313066220009000c500c04203a819020740141c00075039444e009012490104c0b00c09000c01884c01e00303038040c0d00400c039104500101d80b9800c0210300a612842402c1e6030381ca00204084034207510446640c0c4d1103101030030204280c5a0110f0b88000c0310b1000c4540040100314400c1c03050181c001e0900103013075501caa400001e100031404005c664045031510640b00e07150784a643c0e81480c2c8100e03202d0b0902680040080c5200d9a030f40d4101d120f00e9901c0b5200000741310328040c0205416404c0484482402c2801503405d000c0301c1020441d9540720b00c142d207000c41c83d0144c21001d06034090b8030b503c9214007038000e8030b01050800c4020b400410140784a000024101040f00007800503080c802c1e42d21600034002c025900445081c59211046054907105001d4550340726076803000010300c1c00351612020010350443c08074420607918 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 949450575 1250 949449325 949449329
    0x70302070b090705360414071413021204030804020402042312010c0203040b07020f062a0703410d110102030618100b12160206040503031609030c 64
    0x3801003040904000600210440b86100e50000483c17607448040008082120407118448518210030070781c6851400501c6880140c24a540e00d000754000840e4a02841620768070030581100c82c96040c012072107014080b03104402800514140c40400240840e0184003c07a410503c09080189015510002d600d030520b059000701a141a40141e85000c518041407283e040701710b0540200203145132024080e50320710503442074510f410000700e901001e544d5103110300d10822074083c041569032114036821400000f9016111140702002d00e0198092410010307040007a280e0101d0b00c1c7c01d19107803d640e84103845d0306100b110741d030b00010800a4020400750040382003249007644001c040000c8030a002401c03502503400c0c150b107243c0c418000c0207401d9640b03c0d8401810307426400110010b4070307003000407409072000b0b822403101a10005191140c400a2400e4207200700495000e0200340030307004208a84a020548029000307074002d202080700b1201206070244501840d0602a46059882c0d44620b00d200c40c50f = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 949451825 1250 949450575 949450591
    0x607140114060f03010525090b0a0e01090806010303020c09041104060b03060a091103070c084e0114030309090a1d0a080315010903060e0610061403010509070302070b 73
    0x105109843c10003541c142d400480840090000349003141e0100b29402c00030000b56001130f01200103614150041d4241409025642440d5607075006078280a003807074a02510444c00610403c03000914800c0109030b103070581303506a020b00400540d0300f080011101010384261180003100100040540e114440c50700200348226a2949901e411010003090188540c0a1101d150600c844055160100030840e07030311254030708010403030498074148403400b401080041548903510b0b5041580c10154410a8041c03c45190185030a010344d400a00900c4810722002c2103c41c0c40e214014800340c800d42c039003141c44410281c2101e04011200c00051007204003034544008040d1381e00e40c580b0301100e4040d1513059812240c00108072210b01a5034140451200500800001d070803000d041440c0e0703100e24003001c0119004002400a00101c01178180c44d00c1060301c283c4101c0c0e0160200043d00c600912604d841e0001103031103e41141e19103400e03c00c00c0440109405e00705a0308010307190014001881c024061215 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 949453075 1250 949451825 949451861
    0x90c030f06050d0803010e0c040f1202100e01021e030910090512010e0303150a0312020f060f1303080408040e0108030c120f030721020d150b040303020c06071401 71
    0x290300c004500700c80e4142c002c1030250301ca4495040201d0301c2c0c13a08403411980340c00041a042c1da100007120142e800350f6000000b0010788082e000452100115817030010034000c6900062043c4c0030001a2080e00c4c0344898240036800071800040d010041e0040d0b0b1070750f441460250307840c00c013103100000c0c50420a61910008514503070818041800c2040111000310419030080000101e0381240d5540c13070000070704000030600c85180d14040703030f10742900c03c80007182d1060061485102d11b4002039182e503810305120400e8840c80d00003c1c08105102140350060030b5001102e01c2c0c0d000d0944045035020300080c0156080c003010000002c101c405042082d000340205005541c4544c9103040041c01d051003000006001e2005100c0144040003110403290010120305215007040d01900c130030b0f0700d02320720320186030340e0584041205441030350203030040303d0703042488282543da103030301e0b9000702a06001e24000540140e01c4002000400d040c04c034001e1495078090180d03410b002c241289094291a6240c01003154404 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 949454325 1250 949453075 949453091
    0x6030222090b0702011d011a060f04031e030807020d120e071503060e07030207031d0d0f03200a0c0306020a02031e0405010f11120a030902120f07050a0617040804090c03 74
    0x102d0506e20801075054400034019210704c0784028500a40281400e03100d4007000a010203100f0143e001c84009503400000c1c0104144510380800101003060402c2d408918211300051440e0720224481d005407400d44c852039500e04070740c11180010800400503541c40c1c0b00751140442c80440303d45807100c0043c2d0f16a0f0200d541410045100c008900290009003071500500540d0b00180d08064010360300c41782d9018064400303252000003801e00034030714000342034641d00701170303000501d940314100d80c1d142000c854070500903446004509907220708540c4080c2ca407d402d190140300013100d603001130140074242e2040300d0600130106402e4440402280d20407684140004040151b1358100c0104c0200001700e0801c0320780d4040c0c000c0300c907448011044120000071070015400040c58040d51241100540180c030340800d4821340c1507403e507144030040601c081d07403083c0c0400048a240100600741628440e41d105806a100c1042c0c20428541c0a003080b50141c10601010030981d19500c12080c41114559022a11032 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 949455575 1250 949454325 949454351
    0xa02131e240f0503163015050603010b0a030812041b080d03060b430b240d06050705040e04080307120b010203090105160503040e040302010f06030222090b070201 71
    0x45a0b180302020450401042044404520702a103105011210201c0d40b401420811025000c0800138005042c00b11f14100541d82408903884903114200c190000c11880841c04108908086540f000500c0b044041103100795800819503415002845003140b42c428041c940c40b41e940000c65504141f6240d4450a8181c0304c041d41070282d034004000c1c040d0420314040f502440740100b0401440c075000b4040042c880144c40c0b104690807148015400320b03a01c0390203429460700e444003200c20b881041d603a00450040c0500d044c000c0d2154180f40c9070003000b003004040b19948000182000410f41410320209000000c3c098903030291b040d10903032017555030310340c1d901d894035003d42801800c42c9000350701481c1038a84002640c00108845261030242051340d25281c2c0b02c408a1a010480e10f0300900d940400305002403042000c0020320301035442a002401502c2d4580740c01d908880c09480301075840f480040c400c400d01d42901c1815800d0000090000c1100403044c1c9030480c0c030290030f0b2000c00040c0c1d50b86201484003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 949456825 1250 949455575 949455583
    0x3150b0d150b04330f15030b0301050106050417031219051609060e03190303020306010914090f06030f15150405011428080a02131e240f0503 62
    0x100c54112400c1140c0b45400f0520641c0742040c401030003e074914005826941504a40a0001495203146404d0415101d0301b04480c83c0140c000401c0200b030510b00c682400c1d01c0c0600030203050f24640da469900b02860410b00280090940d045400d440c0410012900140b032070405103072042e2928001110307009514020315045440c010006400c126150480c80e0320190301141c0001140c945142940c1803016407400217007002026003600c030310461a5207242d000c050709900034601c611801d882340800295240d0b0130a400d252500301e03040c1e01101081c0040c414504e0713011b44030b400039009000c48101400d01036955140c28500861501101070000c03c000741d01c0c8803090008407118043d0707800c1c059949410044040c02d960003100612644414030b024406ca4001c4030f01040c480f400328880003200307681302002621040c070b407a0247d00035010160100d00c00009405004c1016400c080041c01c074000d082c04103001002c9540b0016000300920343e000600c0e4185106d4040545500f4010034402845c042c101460 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 949458075 1250 949456825 949456841
    0x80111041a030403211107060f0612121d0d0510111c050403020a0f03110d300f06060504050310050105030a1203021b01020d0c1803150b0d15 62
    0x1414030030403c10000a40c08250010399180c59400300080c4d603590380a103000350030b80d509aa154008085881003e03c403607030f000b0321200d00007160100030980d16000b2501d0744c47e0400c000600207211492807002007078440d180001075004011155051150580c0001d010340e105001c0940e034903031103180b2031850451580f18030f5400c1840c80d00490718104542d03080d20342d0341a0010328007880550711800141414020702804804660000200061078080d2601901710700407038440c0c01041c03162000c5203103224000d030a04001c0c07100b410502c0400d00c4080c01e601c01c000e4a00c20654000d01c0d159818581184507501424028000355100c003629207060070217040c54500c44685800341c480c00c0c0310041025490200c0d86000322504000118a0009500302c01da0292103030040060b0780c00e4020310000c1c660b82c01075020709283e060b1103000b40100e50221004071840d180b004403d1302100b82d0380c1000c10004540d41810900f40401901c081461000d0300002180e40c0030801040d18484280d00308150741d288203104581c4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 949459325 1250 949458075 949458119
    0x603130507060801050d060510030506070503010602010e0303240a051005180f090606070f1203050403120e061305010e0105040507052e0e0d02030a080a11010b15070c08011104 77
    0x241c40d42c50140001c000350b8076800087d0865070742d040850f43c040489004000a10b42005c111001c0303041c1440c009045620903c503010055183c2400902c00c010f021080360b002c1c0003580555020304201e80d07245461540654441940001130520001e020b45400007807203034014840e1209615a8030014280003000d0811058510501c18115400d42c036a40300c548068104005540b1561950302c0740c54071204140b2003883c040d0501d45402034100c8956490f41007248514860ba40300c03004000c0c4642d1040954225061035002a08180b00007044000300c82c080189082c02072002280380d02120801c203003107c2094030262070302d400c28441881181081e000302001041c078003a91002070440c0d86100c07a00c00000a482600300a07d1007030907000340d602c24401100064008040d43c81400c3d03207183c4008680c0c40071540034040740720300d50320b40d080c4041845107130f000c00c101400c04200441136858003246980b22440c00c94000c900b0030f50129088030244034a6542540a2503582c0d41d039400d1a0001c800d0135481d140d182 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 949460431 1106 949459325 949459337
    0xd050a18030f1110081b090a080102030a0c14040303030510090c020f1b18100312050706060515071112100b0a060c0b24060313050706 59
    0x10a200384540300058044052105006541a04513804404240a50001141c0a507140040c0101100810b80030703103000800c20019a00c4626904414141ea601004000c81c41c002c51003507008030809402d008002d03001d0044285aa4441c3d400014205500c3d40041018000003031a1000a440018800c2c8059031031004004d59a000b9070186826a1003000b40f8008213100882c1111036102000d40403070070210b002c880e252089040500958070480342008000086a940740181c01078101994a0f20360390039043c2840c0c019940c142d08018480c180051802d002d50554000300c0d60105c0d03002c01024445a45000003402402403141030310f0281c01842d000c3ea42a100c294050f040b00035040b114000c400c0e440704400c5078070080e00c0e5402400fa4684001141c4841d0b0f5503d420110341358100703c1038561003048004240d02da00192903400183c611000c44404100b001d102904c0a002c1c10700c1c2c00 = true := by decide +kernel

theorem cover : BRFrame.Cov 949280575 949460431 := by
  have h0 := BRFrame.cov_init 949280575
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 949280575 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 949280575 ≤ n) (h2 : n < 949460431) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
