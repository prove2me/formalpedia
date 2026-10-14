-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0272
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:53:01.247337+00:00
-- url     : https://prove2.me/submissions/56b5e13f-e0f3-4a22-b527-e60565b1f334

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 48741011 ≤ n < 48920867 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 48742261 1250 48741011 48741019
    0x15140307020c130c050702090627011d090a03050c1e03121005061b0c060703020a03020c030304060e09100b0a0216050d0f02060c0a05011d160b0f0a0201020408100506 73
    0x100d030020200b0702d40b00e04c050300c005580d14245010342c1c03134090041d4800c4c003514041c0c1090004004018a8400a181028008800b01c0702d803400e51400c0300420010289000394803a003c150340900035030140c0042c2e881d0301c00e54141003c0f91140441d007111400c2c6504030740400521f00241d603107600c1142000c00102700c1072180b61102c040780d4a81700444103064016014041e00104200f10000840790f45610300041301001404440148154901080e081c1e0802142240580d205071002020150180321290fa4024290006d50800c0d252031401031403925541a114002e50b5628003142241d040300140c41c02071315a24020359501c0c0c40d0008002e55a0082d00d040000c80c0e042010f01285c5c51401c010303d0f69442d41c102203591910b0105e40c081101c1503201e1508000240302d80303401c0c240020f03000c3c0210120003511640406e42c000c5812185410450175040805d415443c00b071090080350320326402e8071180c868494030340d40ca5030102182640280b0442d00810b107640709103000d944003610036400c403d00c14102030f1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 48743511 1250 48742261 48742279
    0x3010e1501020c0409020a050d0602040f090504080405040507110703030216090e0a0605180d020d1b2103060905010b04030c0e041e11060a0e0108100e0115140307020c 73
    0x1100340100d4420421266005803c41e402d003020030314060b0800b1190b240010015a006d507610f20001c0c4407080125411900b46030003250812800003414130680042400072801d00843c0b81580d9201014410f5000f044e00c100c0d40c41004c41e1020b03220309862284004503408441c8203545a05029503241010380800c1c01e11200c550700400d048942d8040c2441c0303030310703e0402000000550340e1140041d280041c0034515500708500004400c802c01c00c42e400e4100211340250440240c0c50000406a84146840e4150640b046621100080030340b411403084404441034544c2c1c500507604101d0142c1801d074404030016050000214000072840d006000703d07032003202d184080c20703582c0c17158030124501224003034101d1940b202c131000180c20302080111514803520242d400c00d040c46000800d2604119041c100242c20b80e01414031950b08803900782d030801c0440900d0a0302515040c04055100d0050041e0110702000d10030248070a402014601e90054104e03140c25200c0c0f030320382c6000b0340d01e0601c1045944500400 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 48744761 1250 48743511 48743521
    0x27060b0319061403070306111c050604050f04080315010e03030a02010e0d260403051306030207030329060c0a0b041401060b040513240909060b030312041509020303030c03010e 77
    0x4008040a43c3c06800380015903e036032200d000502010103640c42d00b020421041e00045140d030003032140428807170b2000650381000e00c02d00080b10001000e00e80d40903813090500012902c21b405072a0f0003e4400b014144125984004030349842c50075100d26058400407580590154064100051034280c2e5002c642d07010040302012944442f41307240e0000c15048007038034100e940740b1458045a10a0103424418580850b41b03000c00a40142544007000099004c00d010b0100f6625005070820710348004007040302170550a02807003a03084002da141d4881c000c0003682001240d418010007840303a401c90840c0c0020f140904019045156092080400754a00040071072201c1c4d941c0180c5050320809044190011a080898002006104804074801460421882060002d41c0301240503001041010612040f18901002510750402e80148650000e201d800425031400c240e0741e40c0250409804540840d01e403001c00024184c2030f01c080d405010020400000654000013103040754a42e441810490350b803 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 48746011 1250 48744761 48744779
    0x20c04060f170d0f08041a0138040605090109080d02030705150106020604141f0b01030b010c02030c1504090513020a0503011416140403061b02060127060b031906 71
    0x800c0c2000013042c03a101c2c4c03689020740324042095001c0d20038080214104140301c10707460804026444513401f42c0c9243ea10100690150f45644006c0b44840001250000107e04140d0789004a000b603000300840401c0004d4160722421540d001021600c1c10781c0d034400c40e1841d000b918ac1c2d000c00400e4800b4801c0c00a00c64035034032003035070341c42c100c40e02e41e405011107407144d0340c3c0e45030b101c50010441c41d050302c00c82202c003c00100e2504400c0159494120010382103080f080007506854220100e1814440100e1540c00541c501240d0700010f00c0084035486443c07008620342c0001405160015810946000d00300152881d004c0c1c0c031415024022619030208542c2d8000701402c0e40d0f11603183c4d5840c00c1c0380502080b4240c0651880152451440c2880c80b5206000a12902c007600254420380b1556141c3da03076030105404040000c65610203a00c0544007542c101101d5036003940301c203812038044a5110b0359401490003550b0201002e050303c0317a00306a6034240461480705079004165030b59980f62800d07000092404e1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 48747261 1250 48746011 48746023
    0x606170408090f040e062a0703021c03020f0a020312131101030902040605030d0c0204060e1303120212010303170a1a010c0204060302060f0309070b0f04050907020c04060f17 76
    0x6480942285010068818004aa0f81405599800949560744c0240d800c3e07041c8502403003142e00305000d95010071082007041e49440c00c81c1c5c2c0241d40040411041022070b5003c82e001e4140882e803140341a807141040e9080b8024403070744000030070f02e070300100d00e1210183d408001041c2c101c0304070000c0c80054498041140300d0902011006010290b0307900c019510b54042d410105c3d04a0005000080007076980c40401c1c28440b000f112000040c00d00c01c006011490f1a2003510040c100c4071300783c01d45914010704000b151504140000d42405a804003c2c0e482903040d8044070692080c4000d110a503517503030700d806410310011280208000c1d84500000e1001003003072080302e01c01402d200c010141561401c00540b0304400c8079209a811036240c3d00301002503100d2400403c0314400420f41142c0d80c0c80c2400c00c503406c10380250030040d680d8804010140d41d200141082c0d8068440c100d4110340350303803030780c1c1d809031b10781023007070410f0303508a42410000100c803800380c0144011980103542100c80e89550f050076980f144 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 48748511 1250 48747261 48747263
    0x303021e1527061801290603040c0f0b040611011a010e030708010204080c01081014130f0905010b0a060302031e0702210405010e030a0b041403070206070606061704 72
    0x1001400008165410954000c607035610801d41000c00300d003030146210f0400d03004032000414189034003160000b0a00074820611543c49800c12030103400e0b190906621071101c1c03001c2d602e2180c01c1c0400031400384000060300030010b209400c01075126941d61680010785030010310603100810300043c0c10b0111500107001e8a410f07c04422541c007c0300480310019941c507218420210b4043c851180d0100c0d07140c5003480103201428003a4002d06c41012444001000740030001c02040000801d50810082448005590620741c00c048440803c03120f040d14040c001041c44c052102c5445040160482c1842019403020030511020360319040c800391600421760030b91000b902d003012500182e0340c0c0d1890340f10381d4908080e0091138500c103a07015003030201c800d03000ea003460042d070741d080b5000000d04011668020796000c4c1450700540141154084d56240c0d22610b840050001e420b540c0049100f107802001401180c2401c0e9000b0070081c1c43d6445814084010140d6000c0c0001044040ca40d001240c08210b036203605c51 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 48749761 1250 48748511 48748543
    0xf1502070e07020c041103061203040807030807060b100905031c080103060213080a0b0105040501090c080a05060f030a03030608060a1e020706022104020102071a07031107030b010303021e 82
    0xd10718140040c00680c50040803001180260401440d00f540c079801203d00158165a1940c0c59051000c10000b034400d001d4403140d4154810441007001d2400400c0243c103d9400c07100040d12080707a0f0078420080c20300414a81c2d4010076015060301d8503134000f2141c0060b26420340840d5a40e8990001082a40c070001e11181c0116a00000400014101d90014902d08059500c603a16641e924400d1520300a00c0d1941140c54008400040c013141c14039104035030050500c0d0205000140345c120020304907902c0903003680003807600c0b040003412540320042d0300e002d42c82028040341d6043c0c8103030a00600070510350180620034002e8001181d403036804c80c09a0000400d14801011403450040c055070000d42c0141c20032110765400740648803810581d03030030400e40000008040002c514051000a00f0320140d0b800038519100c8110907590103c01c0710050314034941c7d06051410812000070304662410809600050000300d80314004400c055000ca90b610084c02e48122483e40c60b21007040d0140c640c07a03000b80ca5540 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 48751011 1250 48749761 48749773
    0x42a020102041d090304170604140106030b01180605100309030305090703030e0d15110a0f0306030c180603080a0203043003050a0e031605010e090c07020d0218010608010f1502 77
    0x10b984580500f02c0e0012400380c12a8071741070b954101c4518604100c49200340359084907080100344007414001d12000c07121b4200801c000c40c2113560381c0b0b0100c0418065002502d400c4803000701240111f078040c00190600070140c07180080324500003409001b41c150124002410300e0081101c0f040001050002d895040d00c030642c0e600703d8001448400450448240d41450340b014119218004a10030781864620300b2001c25a81c0503548005015500e00e4000017040514000c010004102080300c9001035800e0248032007000711590582c2c01c081c00260b00041d0480500040d050703070464000000b8401c541c201a4103c03412014151012240c3c442140c4c481d0a2118107003504000a100e0402801010140e0030a14112400d03d00401d19160380d081f0040301070040c0704014806036030000d403a880c040c0001c584102861a000d08505040e00451600a008160b808000c1c0115900c0c420700b1042e680e00c1c0c40d044855503039101e03030041130002c0a206d6120143d040c03d201007a003a0321f076000c0403e41902c903001080 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 48752261 1250 48751011 48751049
    0xd030b18011a0d050108030a2006011502010902040f0501051c050c06070201030e0a050105070305130206120405010b121c030504030c0f021507050c03010e010603020102071211042a02010204 83
    0x2d400d0000712040c64051800b0419451001298444c0c140070b0060b10b401143ca410721103a0103042c1082c46440301100d600002d0031401303609800903006043d030b8465076090840c22051841030303015041d030020081d41701d070400c00d828078600c0d440d41c031107412220100c13042403500100c2c0d400c100d08c0009824014040e034004503c00200707401d0480041040c6071041c50300007002d0b2082c542d400d00f00405c17000100c4169445505010700250b00d401441e0300b0510310004e142c42c20340c540d400110325100342600c0e038050754140c600040c00d1010079440320780300c0c2c0310160a0348500c41c0e018100d20307200c52039641c200040000c124030300803421307120388521449254181c58444a01c0c80380e40713035181410841c040813680a0031004254020044d40070141106500c10f000070071441c641c1400301400c0d58103c00c0045000e83c034204040000d44e0340084c945048900b0286403095504080c204881c0f0200c06200190b00541008050080e2490003440700074080031071288400c0e071605024040b403d03481284203003a07000300b918800302 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 48753511 1250 48752261 48752279
    0x10804030c052e2009010305090f0d0c0308070c020f042d02090324010e07090b04060c030f09030503042d0e22150f0213080d030b1801 59
    0x780c0078901907000c456001820442015030350480010001880307280101d6600d44108a010340d0040848041d1406040c01c007110b809200e500402813554101601c90001c2910180c0a00c40c100205c0c0310b440540f00c0d0944a083d01401f040c1c0703108411000035500000040f0780340d105e4801500c00c3c683c000c0a10101c0b01c801400c0102500e03070803001c51808250000c42000500040481d5030040740c500c440980c0301d4580d0341c2011300b00150700444c1051501c2c4540f01400030018050894152991075040c0440c44e190070f072044074807141d15001000e010100003400f040c0150800464880e452080e5125111240070040071200800300b840000e0041e8030502060080d0080445c15a40b081900f41400050541c5480300c2501c95544d98001012000f807241802813035800d03064280c00050000300e1381103c1010950340c1d51241265000d4000ca40d40d518516001071003565011220040303511000544200e803201c1c241078a138052843d030342e00800e1500b00315589034101454072520b461240c07003070340d2460782ca000c50389 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 48754761 1250 48753511 48753527
    0x71406220327050a05010305060f0409050a0c0803030a1b0212090d1a09010b030a03020307020f0f0904060b040507110307060b06073e0d11120f0a0c05040b01080403 72
    0x100c0921250329250340b14040d5410300032612800001894400a24010602407454810f070800341c101030501d001c01540d900c0f005a6148005002d450000d54001c25043c42810080304000081840550010005a071000040a1405130b002c903141000007000c4d03502001303014042e044040000d0780082942c0150701c0001405091211000740c100c1b081c86100d66101030b000c1c00001c2c9021021841c01c011301c414658244500004808141d000f015040c440d900c01951300e00401d00700a214102402205c1100d49600850030304100c0003404840c02400c0520304000031b0018004260300031458440000e040c64422101c03041043c0e2140e014501d4500c1d281c8074800540204450590021010001e0340000b444140b403110800400760396004090100d8040702c038401e6030314018403131103a80d4409940d105a4400f0b041261082e070215800001000240100b8110300b080c3c02d44520601584010001414010a0300104a88a004e08883c0780e61184100003c0790040d082c860b00003010000000e000a01400384 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 48756011 1250 48754761 48754763
    0x20a020405101703040e09030906040b0d02070f03020a030e010f0504090b0a03020607030206090705041e020c0f030307200307081614010507030b0f0306150d0c030f050307140622 78
    0x2040002c2d50712842c110315500100c0030142c12952000a00b00100040c8006150700544904040e61030104080c0c0000d89901880c022000c2041c03001820003080d00056040f0340119034090310584261000d0704001e5112400c42d0003c0d80480c5d03007091244955841000400300a40d441c0c0c9030281407a0070480340e0746c02010840705258000b024403c0c04000f50b902d15000d0840c10340301307500501c0b0380d2810726000360611000758002e501440c100b9002580c080e00d41c4040805a850a0740e00503110074440c40594500302042c030052086010010600076880c5d400a0040110241031822410524070703c0d88551303a074402c03020003415098050103001e07145040c071803090b801c090240040740318683c00f00112508489007550840f021079640d2003c0340b031605110a060340d854808034060240c2d0701c0c4c403a85000d42c40b2030199034240300d00580013160342000034000c03004024640180302c0b4207400800c1d10b046a582d60055800303403401c142c402c840d070703600040c0012071500c200c8000d0890300440c0b442c04402421101280e43c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 48757261 1250 48756011 48756031
    0x105011d0a030c030b0103150902150705010f06031202010c050711010f05040b03101502150103030f18030602030a111905090604090c020705040605040212062b030509100c03020a020405 81
    0x40e0010110794151401806503004004561a9500d50700d8050445210109403108240c10427540c600560f4848003514800356041d0610b0360b03940c4d05880c042d0b004010640c040340b00f82c0d14150000c000d020041100007800c0e5281d030002c100480c2d01c103105031041d01403840010003940c2d07140301ca55038652140b00c1048612045041150030035840c0c0c41b0391000c42e001200c002c0c60212400c6001c1114a2100c80009090b4045001400101114100061440e20140805009d110150f0201716a070341c4202a12041e080300c600c00121002d4483c46c104c0003a6009a408807580da0a011000001d9a1050225202c40303111811107046d00f100818140c130a90001d01d54682d20050a000000f080c1d20f40d4018102c00703807010b601501e440c504000800c011039500e070700114000d92050003202a003448040c1840e030005d80c12240c903818800340c0403800a50000b00003c4070b6004690280c11010140c111011f000c14920446149109541d280c20032103d04c10312020140041e48201c02010160425610050b0888101c075 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 48758511 1250 48757261 48757279
    0x904020f03070503040c0b0304032c030102071b05061617160b04230304060518040618061a030f0405010608010e030a09080303010506040302190312050408010b090105011d 75
    0x6211035609070821190726010030f100004202c00c000c15190440c1c01f0748204080c032030450510703450051110714909840050b11480e0b0303590759a01d600ca08441d600c8403074018001d560f52015450010700c0540005092a48103069580206251500c08252040b5096a6861030b8102c11241c0360b00007d160b0071440c12040c036a081140c0c100115030b0030894050507004130319800d054100751170038540348043c804021292103503141c020130705000d001c4220f07800c441b22440c000c3d4480411030440e0f07443c200032500031070b40103240510004818a02c220121041c014030801040801d0383c40000909500c008011085407017400c100041c4114004845150031601070000000d06035281d800541c2101c014074558851039101140701c0c81d103154400554405400c2d6040514150f501d05404074000e070299000091246100420842943e001c00d601c003001190000b40c0c0a50b03074603040b40d01810b99403142c062010207500344462003859003403000007141240c0040e95803107941a500001c21003003001c0000011350050707140c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 48759761 1250 48758511 48758527
    0x10c05091c020904110117040b070e0307090f0b030613020105040b03180106030804051c1208072105010f0e04030e0103050a0b030a11010206010806040506010302090a0b030f010905010c03061208090402 88
    0x1190740140315512170b1201c04000d10801d030000d41074004103c0071000c10603203841003100040052850940001c0785007444103040d00d0080010741045103e40294540a20700001a0b8800c4403607000a80c0d43c1c0419000d40d42591a00030010a00505000700640415801c020030008183c01800031039002c00e9000c160440c0da040760380d05070f00351415076005507003800000c00d003840240f42030b0180e111008140c10302454505120342e145500307500326020003824841c4610001c0c0400d070207081200b4410740d0001a04048043e034030406801404203000c5e12840407078080c07003c190100c5d81d9071000d0240d0340513221103a40d8003d035401140500030082c9801c203016110700c00e00202c0d4408001588144d48a50510b4401d174103240002450100140d1280350300c0e50051741444042000400d0a80c1501c1d010f580e0b16055545044540d006082c1103100660148180d0300c100703001c4a4194031040c00107124200030710018001100c21402d031180360281180d41191395240030000340c4d41c81d000307042c0c00781c01810240c180030354 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 48761011 1250 48759761 48759769
    0x6080408191e1d06091f03020c0a06150e0405060a050405030d0218090f100902090402190809010c110d0e040b03060705040f091b050309010e030c0d020708010c05091c02 74
    0x100c00c14120224500548a1402018501400c607070315105592117400e100e55040042c91078900c04442e00c1d0302d03401d00035041001d07a1081d0102d83c600401101121a619036a00d0400003c205084103003052155004000c940903400c0c06011340226003000081480c5c0e111102144000c040142c0b08861510003006417030440000342c005008480c0901c0b0075400000340384030500c5545280200a50b41010b454010403030080d024640070302c140c0381e2801c40161580c02c02c03000714009110340004682c2a80020701030601107940540e405124820340e90080c001034002c008151500c03145d01c801941150842409040c0503403203050549401030000704041204091000401d04005007541e4440c001040050140903400425442000a01d40c0b440101300c520714415544644c2541c000c0e45204000002012803030001c42500000501d80c14141666035030011240e00c555207000c1c04507014050700498000041a050611604401c0c05444c7c50356460541001d0810000300d4541c01e200203441001c0c2103100140c4c41e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 48762261 1250 48761011 48761057
    0x70b090f060c09040b10092c01030f05010c030501051c0314030705030403110706020d030e010207020a140a0806090d030e07170106030b0a0b18270c0a0608040819 71
    0x304000d4156444403d00140000d964a050105004900042d56140c055a00280301000c41d00380904c41030b8286082c00070100143e0320010810001140b800000c81800002e4010521701440342000300403000d0785032429030640e8000d21039280c1c002120800c0400c2a4041b442d55268a8481d14015284c200b042114280641007580c813500041c5000c800c002c20907801200d00b0340c0388592140200013092803d04021340d218140d189920402d03072076090f1464419025010b03103c4050b401000450072540360075468654108207101c480c4194000e00c00011714850108545001e80b80540182081101e211429005066a00780d485058070940b0742c00104c1f035581042c1c0c1d162105a200001c6051451418556494a000f90010303c01c0d91400c02240003a61ba26402445002e140140000080e80c445080100c440442c0000f1325140c00e4600c103c905800002c1703805641094122062064251a20750403a01150b040b02d009000c19000c02501100c80c003a103050111051242c07400030100e21112586a070080 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 48763511 1250 48762261 48762271
    0x2160609060516020a0503030601180905040f150207020a030b04050a021c060c0504050f01030c03021905091008061008040f0c081b01140703080a11030c0c0105010b03040305070b090f06 81
    0x150780c1c2d20500540b910005090000000c003840280540324441d280e140c1c691002422072814003040722051128403194410b040002e1048100802441c0781a041010003410800310803110403080c000c078010f80b22464400e60f5442500036186000340b40c290340c1c482d18501c13809801035500b40705003440302c07006a40d5a501e1000048070100403400503000c40c81e1100c01e54411185440901100313210034806a1102c48107000764400c2481c02007581140c00c40700313500a11034025106a030002e40709903005041e030000014400c910041c0c030815041000440100c800c808180d41099100420b007080e00d030194458051140c1090258041040480e495652030120b114181d0200d0030302c1e0040c4100e4138480f00100c401c269011001e00302131842e18210313a02000603124000c001030a001c041d01c0070030801070050b400018030190012004c0c1c0d0728180041441a00e400559403d605982858000300b0100c100c107050b64091036143d25481d0a00c035490342d03064800f1400610360000c900c12443e0003d0144002c1041e14094 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 48764761 1250 48763511 48763523
    0x9110702190315091a070903080c0f0c060f1b0c03030301090b01020c01080603070b070305040e040f0b070219080f1c0605030c240a120f050a0f1404020402160609 71
    0x7030703103946010105003800d590710202c0b03e80b908542c00082120021804001c6680100410041d501c0140c181e650b001d003500003910404000c1a42c0c0d0356400c0000303d00c1742c400d51444c122800401000200721480c40360303035040e08450382d05010b50401e10300051904082c14942205991351a10000c01081c61502300342c1c0f104403801d4031506920810758040c0b203c000d0401e42860542d01600d4130702c01007555808180306417501503d00290311014148a0700560b4003400351b41e01216040d0405003042e02c192062014156400150700340499411070001600d640103d103122000c0140519030741301c0705510b4210611820084104020309540c2501c035005130f0000241d902c0c00098250704150038980380c0144640d030680110620010045180310b072074a4030315581045a2496612240c40c01c007142d580d045414280c4030941003010b681c005180d5a0070251003404203c00c100107071035602500300c0681d041c680e040440426024041800740c02e00d50000c1040b9070100b0ba0001c0843c0e82c0b80e9460f030481d11201c4042d40c2c1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 48766011 1250 48764761 48764809
    0x9010605040e030304030f0f1803080a080f0f012105060406061e05150a020f0f06010602060f040305090405060312070807060507020d020601090b0a09060801020a0908031309110702 79
    0x894900340c03082c40340c2038803104003c50031450155030162400603540b14005c1408850151514aa442100c44140c0d0500003000d42d0070700e0b0b81d80e1405081c07a40110444034007281c0d880d000a0000e02c20151898410420f116006502ea440c01d1742011219410b60750748003040b9861100800858800c21449004034882c800008000d8a0f000080b10400008407650320942c4886104002c50340c0c842d500d003200c2d81b02140c00a560380c804140207926000418801006078000d007005007a8604000c617441d41203071015002c0d52106da5440e00d5090300650210340041c0412018000c50401e070030950f02140c1d11103400f8041351007038172551541903200d4006010448001c000080c40c1010070001d80101500f02c4100e000a1803889200e48020b07455007414012402e80c603581314142000f6542c0c18140350000c003043e0204000c1d0b562591907880c044c5d0302220210002c81c507525030001d1740010010449645201100c1d441d050340d1b0520500d40083d0481e46814410140c007407088101607650500d09041c4039881d4125819 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 48767261 1250 48766011 48766019
    0x20706020309160b09060405090604020c0d050a030b01020a030903081b0601080307020f0406054522030f0f02070308040605040e2d09011b0206060f0406140f030304030506090106 78
    0x1503c01e00c2c0c2d0700920314110091100c032045480c0c2c03806640681e8422500c0f00c1c9a43c0d10100410000d00401d44540307034911891083d94511a0004000c221120441e40c051104041110040e45d464450100080008052010070404030303045801400d60b08042d140c44002c40c094011a046c9454802e800402c0107410000f0140214501001500d04c44041941e05211031850032000803141555407032000406940c60309403040000095200101c54a01800d01c1140030709110270403000c00d90308541034403500c15401407008031072660f181c80914155040e96100f821902d6494210343c074480880c4e0007025842000c50100001d81c0d82e40c05000036001c50756030303552180d1034030131161640717000034010004003003008140c00c808004109503440048500c100c40015912040107442c01880860583c042564201f032030858401d6010400c540100001c1340d0020814291504120458441d03100b682c00e4014540207207542030a00c000502d900100040580b418281d0b43d445060400000b10f40e0038007a6555507030248 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 48768511 1250 48767261 48767293
    0x20609091810050c030103030c050f06130c080303040f12030e0303041202070b04060c0b0601090302060c070315020a02100902061e1201090c210b060c1b0105090108010315020706020309 81
    0x102c40e45080107424072850505407a0030b4124030040c003025040140c5444603c041c0a01001000e0f01088a40d04941040c0741c100980c502c1a80b41c850211050451301c04002040c0c100001500e0146030404411072318150140e4503039210070f06040412003455210300008880c9241800039500ca20700031410005c0e10001c254000741842c25030780140007a50360070310081c07040d03541c8100070b410286d40c040c1034429540c0710107005030b480c17619030b0340020b501c0100060f10751407001011413424116845400403411840c0b0b92035120302a0300904007a0001688125006c00025040d0b4019020341c03400a0180e80c40c01201d103410f80009580e12200e000d0069000808441c01c3c40491080c40c01422341d1a410404000101c0000344208001900c04a41644c001101030704142c140d4000c0104420061000c0e0796030301d01c1c0300320985076005070f00c102002a91850b4840c0165001b101114042d28050750342c00b40d16030940c1d440c41d000080307490300d08840715428400305001840c5031000754090007140b00280047c2490085007 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 48769761 1250 48768511 48768523
    0x603030215090f0109200a0806011a0409020721050906070803130b130b010b07020603041b0f060e011206030b011a070c0f0e07110607050c0c0a03081b0a030801120206090918 76
    0x146008a6003847d04100304070700499410f064500000240f03560f090300c09410840c41c040c1d50001002c2c00d10001d150410015140101c03000010180c3e1200501100000c2c25500c80c010040d5141d0040300802060002440000c0295800003101401002200e03003912071030340507601216000034240943c40f00c84244a031008a40d801070452703010051801d000c1d540400c246000c0504024403860071440f180841c0c0340070081d83e0703001e05004903034000d4032591400020881400c542c1064045200c800b4401210609130140d0001d40c4e821001c04d0605901c0c15054940f14007448009881844c400e002032400142c20f400040000c0a80c80381c80d400c01401c107034030303000583c40c00f9003190140a6104003440c00c210001c102d84d0740c8448d00d4200f01b61501c0118403101c3c10b0007004103e595102240180100802245201071b01065200d0038040713050f00c0020307400c0d5584078120000540807840c000c00400c5102c20240d2070145440c405490390342010b48100c00300c1c55441042d0350100f4145105c54605403071000401c85 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 48771011 1250 48769761 48769823
    0x11070605310305070515040c090e0321090a0c090c0e01020105131e0f0812060a0602150c0d090b0603011a012102040308041203120603030215090f0109 66
    0x200140c2881445401e90048220040007014001d003c2501024014107104150f404c020404d039000c1980780c9450000400f1410740955074072686400407100303241c0000010350f0b00080c0d00031035108510b40155030805441100408489032482245031010010314a0140320005044170180030949080700c90700274190070031485490303045a16140400043c103603d03400c00c5803801c3d0401c1d0301c01041906030740f50180302d85805002411440c11100f0340000c200d60b8500070701190180048080b031540740c0104021440303400e8800e10005a004a05c4440c4030480910050b400400741851107150000a0080500782c3d000c04030281d894120020400c0b80300e04080c0240c072218003042d2100e000548201d000a400e5003035180c0241c00b0204004026180021180c0c1150051034125041649580c3c0d030754048980d82481c01c500f00c000a5030004000d20343c00d0039001c0c071000c0c2c0340d064018000790b0031a200d10081149004001088920072810314180c0c00c007080c415580154000c00c80f5200100c03140c00a12040c14404003 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 48772261 1250 48771011 48771061
    0x71b09050f04020f01050c030f04080d080105010f0e0103021e090a05040b18060d0209270d12020a02011d0106030b01080a030504050607050102040906140102010509060108030a030c0311070605 84
    0x1046820a1070038000c540c400e07412600b8441c40c51013640125401e00814940300c4007440001100e05c50f00d00c0e080041d2045800a200f1240b0080100350200e42080081c4078441c045200d440031320740030300d003c0c03204000070b42d40c18500103043c10324203003a0300210350f01e03040024100e501c001000043d0b418169010f5021302001e4805000304082035006c00d041584140c3d500192206040c0031900c507a03616880495000d400425010480c10013544504812007440e910508000c0385040c1618080c40210b00424440780c1520780294902250360302c54003a600c8500301800b107560301c9581444e401d50b40003000416621400000402c07a0642c17511719078001040e0410034040e80031000c0200041c0c0c0c01400c40b03065400503500b603a00ca09d8580b80042c0a40556045114a80e081410204810450700d01803100804268002d1081d61211807020752504401c1c041e4081c1038104000704030403d800390308031b0b10701d18000f07180004180b102c042505c44941c00c191406c840c0142c642d0180040c07001d00d50401441000da400c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 48773511 1250 48772261 48772271
    0x403080118111c0908070804150e010509010e060d0903090f080a0506060607030909020a12050604020307090e0c0d060b0c2b18081504050601080708030717040b071b09 73
    0x742c48500324040e2804020780300140c89000c821140e095005064003a61280400381c0384c03d05450000815000b0b40514407000095041c1000b0030b42c8648652048418182c46052812113500300440b401d1036040c800c1604608104140d52280f001840b814007154003ea840c00c0f00c080c24440d41c22100354640c0c0c01307048198418090710004c02d00224180360401800c0302c00a40d40d1582d0300c1d09842d05011503105511562010406c0c0a40c0307038200c841d080c08452140010405039440f0709c00c1004902050724440005010f0b19802c2c0b022082d00c0c8805a0003484205550781010105100427003550401c2e002101104008201c040c000c031420000311aaa079440b58804080c1d040817103d1029000001c40b80300c081068200e83e100840300d410020754090b2025509466462004502000110344180c400b25254810240009458200411041c06848000340514640340e5180c491192000c984030800405002c10080001c9003408000141400c5210b010600361031100745520340c120450315844286018240 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 48774761 1250 48773511 48773531
    0x20115080312062101020306040507090e070e010513030615090203041709010302070f03030506090901060612020c070503010c0c05060f070f0c05010b2205010503150606030a0e060403080118 83
    0x1009840c68001d54500c1d1882c0356a8100010303982c0c0c850000d441c0007410203071181100151064000398412a401e440622075602c0d090002c0702c42d41503034800c0010200710f610120307201d148030740900f000200051400606009000c44520710428103603004480c85544c1e020540c0031107a8282d002e5000303085003074086055181c01d40f582000f0000c1104185102c0b80c0009580610768041d0b0b0540c0c40f85030300034200165a013103130b180180080c40141d41151107402410002405a00c050085a059440300d40c4e0300c2c8000c407120080d600107500261110807a03030050f81400310701b03501c0900c5103100700000c5503219500c2c00050f060850030b0806c0a825140e640b01d9090402c06001d4109030700e6813816005143c02503407004503040c45030050184041036a481104421110011144103481d800602c06a0108006590341c0d0000c256584411004100d14203002c500040c00500c6e00c0406107038440030420b070210381e1048501940b41022005caa0480204900d10010300080b4030b01010b203490b204403204200800304003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 48776011 1250 48774761 48774763
    0x9030705030a080916090f0b0409050c010509040e06090303041208010f0e06060c01050702010c020709060302181b0301081b0117040b18060a09020f01180e040606120b0702011508 78
    0x5016000e0301403001c83d10204094080420000c156000148020307540c05844104210103805544071050146040c01001c0c41d036403800d8801c0b220782e243d01100030b00207451008015107154104051003076100f80c9d40c02444454001c1801990f104000010141d0760b00d18040c9000611110f14070500c00422482340014800041d0009101c015242d6a0403402441e56803080082d01c6031050340e044407040d50800050068581d01508245420071003502510300c0c0d0f03500c0d008001e08a60103480081e40c0a0003000e01a408207242c1200280c00070700701704050820003940640c185a551081c0d02c51001c681c40042c00c40700042800850003c00c40f02440d040d400e401000b1a09411f00c14082d101030302045250021841c001c0c68241d204942c81c8911301505c40d2072411001041c0100601071091307000315410b5204030141d45c802c0d0400d01c01e5a07203c50100d0b64403420906201c00700d0800030001c6800a603181404203200c1201c000400280d8451800d0a81034a000c460013801c1d90000300c8e444900d168220018481004 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 48777261 1250 48776011 48776017
    0x9060507080403151d060103050f152703040b040e06060a020a1101020309030d0806040c0302040e04110d0602030a09060b12100b040b09010303050406030c02030306062508030c0706050903070503 85
    0x240103458903480646400030403001340203407044501002c038040000d2120050106e40d2504a0380524107a810303141010810944a80c0202c0c010840006107400048001c90007059413400284900841040000029409072441e4855040818004008182081244841c01d071280c0e104034180d0380c65007822608100655a92445030307004200c000c1070401400d06910800c00d9a2400c40d00508603484e90404010107804200191441c0340611b081c0310104410b01c2c001e000b143c040b6150144e0f000415541d07605c800c0031040400780034a62020400001c40702041d02030000d58000c500d600c40006001c045464248126001c014040c0c1c041e581d604444a20103001040c800c0800b20341ea0000328070750035984000380050042080d400e60006140e800070041c5540440544241c43c460f8804000ca40c0240c001a82d490008441c19944640704000001d010f04200c09507101d601c440c42055461a2615900d403074507504104c0718044c84000118441003403040b0341c012030b600120300c0f80107103103400b81d00c0e03c1e500c1e140c0c4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 48778511 1250 48777261 48777263
    0x206070803060d02040f0617030c15100b03070e040c090303022e020c011e05010b0301350d0f080c030f040503041d06010e0f0a14041d0105060109060507080403 70
    0x14404000074085407030f41d41c40c0c003001d01d500400400c0400b50074061070004021302c1c02105008a0720b461010103907003000084607141c5c071408009140482d219103130101e1003d001454042646116140000c00440f01000f071070140c811a150151030a200c1d8040c081115286031180301080345645041000c00c0c2c02159030240c3c50042101d21301d10280340c0c084e0b420f500040c808040e050724800613084100d2003066008588a00490300003102e6040248812000d03100e0a0241c3c000c101d0080004205200405203c044140c01a244200002d10380c000c102003e0500c0a40c0580d05401c40703240030000341d5021b55005800d1141d0304040c40142424286070340b440c00010410345400010401040c1444000c0081c0d80c01005601d00c144400303070782940c0107140b42c98143d4006000c6000001322a10034502900b240c0c001c02000f070315509000f4070749610074246040e000c403140d82040e9a80c0480c0c1c1070b11400c01c0c100540002c6c03940042568244034000400e08038595000a04100e0240860400141c0c0a0111803c42e = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 48779761 1250 48778511 48778523
    0xf050a030b0a03050309010801050901030308071b02030604050a02011101020c07050402070503040e18010501140603070e1c0b040b0609060a0303030f0b2206050603060a0909080909011805090a020607 87
    0x6004099400e500a142a403401e982c404001c503000801c0040020040104c200280c3c2c4854050745d8610920071a04c0b002c0c00001d0105408400160301c0611170061040b03828503140e0014502c04898011904221003034406645a4101000e40c0703003556000706281c4e4084007424000c515004060640c50f0311004a0b01450f441940c0005050084c0001003003078030003a00025044214034204100007807104280e084a6090039401c0c00000580c100f00001000d84a0700050256465551038000441e00e402017030890710780c0030000800210b41d0b034442c45030b6082640d00c1015a14020b040c02d003480b401200e0010142c0c0d01c0303032140b902085002c0c1c0b01c207035050003220723414140859004990000f00010b00080c1007010340081402c96651034004c421000c00d45040e03484481000101d4448040c4640c510044071419000180032200b08640c9003190301c4212014042c80505003495002400102904030a900852080324000580003079281244595900f1003c07410080260450660124545001e080005480 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 48781011 1250 48779761 48779767
    0xc0c0e04050f0606100c020d081306050315030c130e15010b07110a030203071203020c03030a0504180605090c070201020f060c03100b030601021209041803030519152108070606061b030f05 82
    0x102704507031007030340c030700c0c9000c0902045144e441e0200140b0030340089030312415074451041c400d80a402d01040091601401a241e10002c190f8500508043c00100f804000c20f4441c200418911100602c2140e01800d0a500c103996100820705018030703446000b03402580b050326a544100014cd4000500e8802ca0350f0082d0740d0710314a081c41c2400e1b818540c0d8480c540790180400220503240300d6000b0b00400c00d80c0e100c1281d005e004000c0c3c0401303000b03d80050103401d81000000d408035020a0800000e00703c003500c144100e40001e136000c01d40ca070a00c541681c0004c14440b010040c42989540e4a4101001e0b0468501c61804d5203482d5000030f50324150744900d005060701c000303907641441c2c5654100c0110a00c02c642895100c0000d131400030020182190203032080343d5026904d00e14101c0d18024500c7d0050310080400c400390800c5054118444132003c0906001c030b0080d0340200107103481c0060540680166000074506c2e26080019002c203500d40303201004050700d00b0200000079000884641000d81500e44551 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 48782261 1250 48781011 48781013
    0x350402060c06010e1009020307021e030403080d050f060904030f050315030a0c080c0607020f0436020102010609050601050304030c0c050409060b190e070c0c0e04050f0606100c020d 79
    0x280d14490400e070700c2001d0055800104030404d0b0301e5102405088560040241e00e680c40381032200b203000603640140144c001480260191113000c0c04200d084840100b034a1505607a0b60700c81e02d10394001c40545800c55191001c01402d0080700382101d40c428000d035500121031030203603801490005c00c0c44031340d820321101001194840c481c50301c11154a00f4058215081000f49052103c4030043d05c0c402c080d00c80c480c9540c505e0301428403501b9165000c0c0e01510b500b004101010801000e04803403203c0181080d07040641d01d002a40301d8201505224102a040f00c0710740c054000207003524000c0d004908818103240910205036404000c407540702e600f41c43c21021040b418503040c600d00140d548156401400c0140d0f0740284461980702c1c10916004442d41031482400302d10088240d11300303126040144440600094100b402074503803640040c8950b02c1154103603203548191614540981c0e00f40c038268403c0d040310030034600400081c0d81103603085401c03440743c10380704a0041c0500700039040207008031a0074200070 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 48783511 1250 48782261 48782269
    0x605010516080712020c12070f230307030f050f030403210c050303090c1f0f050a0504050303040b030708070c0b1314030307030b0306130b0a05041a01030303020901350402 75
    0x180300ca9511004511016201110086d96409107006640c0300303041590309510502c0000806800300c03441d0004c4500c0c11850b00380f0040380d5480070016030001038202c250030207003568140400809107109442030f807442005c03401c10924188900c108404076900401051004c2480d10400d0512800034051700c0c000d105d2070f503508480392a15000c0081140c070010090003000080491040c50400060b640c0c41224610400d460100011100340c0e03001080d403c8501c0360945200794001d00071000141009890300c0c0d5107801080c50b5070b0065100300c007440030100501408a80c02000d10f80c1185051070020380e5a48140c540154108000c1d083e8014000b411001d00b040041140012a41c6c1c0600015030780c0302d2501c40c10144c0070305002c0003170354032034021100050360007259a0b14080c01c01d50000e415072031554442d52440300408001c0c00659115100411016a0600403075600d400707144298ad000d6203c8a0540c0050401140d9400004109041c864030444d0092680c10500c0200c01003014205580c41c0d0740041 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 48784761 1250 48783511 48783517
    0x70302060a211b0504050904060b030703120504060801090b01020d030b03070e0108070303020c120d03110d020711090705120c0304021203030103081c020702211e06041203060501051608 81
    0x12a0392480400c52599403400b994098440c3c0000e83c64240f1250f0f015420482d1184141c2c003645900a0703e14000c213011030039981c89121109805400c95040549944444802018800f100c0c0002030300004c080c441943d020b92524010007406a05109000c030000000c1e403902c4006014508241e074801090110380d07010080b1500402c5004c104541030b5840304001c6403203522500058002d88a448140c615501b0a01c000f42807a11118003d010942c800b2a0124040c1c2680400340460710814001c061084c0028401002100d103d0010b00801c48501e0050100c0c202d40100b000301846001d01c40b40c26000c7c510a40c456015000d80d50907940c030343d200e20028011000b00d0005040354400800040204514803005000c682048601c08800d400b03842001010780c860304c0002074100340300010440990035580c002650310048c00c03045d01c0701c43c0b00c0d004606454800001c664100c17580120280002d0141c80d0b400684074040f1403800307012103410500043c1c502e100c0c50100c0d094000458040384c3c144030001c030036 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 48786011 1250 48784761 48784787
    0x1809060303091d060d080c010603020603130308060102030306131d0d08010f050402040f09020a1101050702070f0b070c120f050105070c03080609071d06190521010602070302060a 78
    0x410005031241002040300b1414011045880e070f4200302110882d42404203c3d1068600801041001d030301035607400311079007003140806070f07540d01c0b11800310059032100e024502c1241c8046003502d2000d01c5042c0200b00c881c000d8960342c19900100140300741c5e03488800106000325017800c00410607244054036409030685081d5000f042d401900f2080500543c0044107504840e1441050713408562144204412445603100e030600c1c06141500400400c51945c0181c00c007420310341000b2524032203605101d42943d6040360540d00580000344144003d070b1105503100085c0098100643c14a207040d543c0704140c10b0180100c0541000742d10b0600c041019040c9603030301256012000703000f43c1c100240007030a1504030240480200380500c001806034100b550550348960300b0b07582c0d48003c0f4450300800e8410359016018058001c40c0c00c01c550703a41a6410315500c0c884503255a54150790b00111303014810511142030080220710f65280042040703980c0015003209482d01150950740e241c00c0c0c0e09040d07a19541c8110 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 48787261 1250 48786011 48786029
    0x60e06010c051203090a12020d09030b0601030f0e0105101a0306040e1903050a0f17040303020307050903060c03040204050f040506060f060d0e060925030f110303070b061c0f020118 79
    0xf003000080d05d030100d5035070401441428040700c440844c4034183d80f282202c41203000050400c0c0800c0000c01e801d81009504801c06040c001803449200140c0c00c02e607500199515240da440343d080c00402d109112040b4010654003100e0401c19060108048079032001800f000c0c45183c454031458560401448030480c4a4220b09405550095034a0081c1c0b06811080c10000400c2c003101c24601000c0c0110b01d80d0a64000c40c4202001598031a901035000350000b40200b4100841032004107a103480401c02d650045006048132034036890710b441008240c0e07000070b21084107884401d0038400021400901603822080032210440e500200801140890041118141d841c1e0304240310b4295225022410500521484040e601a4007283c51150340d0031300d0248562084030280d00042011469060f04100303040d203d031190b0b4948a01010000b451500b011009032070081040342030010526004500001d4051681203030811401e141c1c031423042100d2443d1002e4140840c0c4007004650041240084020f804059 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 48788511 1250 48787261 48787267
    0x60e0406051510020d02190f12050d0c091404090b0103080906070204060303030b0a0807060509011803060207050d0908011406190905011202090109020f0301030206071b030602030613060e06010c0512 87
    0x100c001d45d5503891703155040150040c5002071403844091001e1700c032016007007142c1c0c550040180d074501c843e0f0052440404101b1009006049400f05a0701505c00399800b5596010b43c6182401d0030742c5010044821207901c030360318001d0000001182041d0460459070018011911f0b40100400700318bc4d4400c01c40c000794042d03d0078402008068055101c0c44000750b0a0b6420b1080c2511a80b880c1c1c7c0e11540c6004910209030700344a0908a0740c0701c1c4140c460008103090801c1031061340c81d51684240c0e0801807040703ca0b81c0242400b840e00c1c07640551400028440a8028818400480d41110712124080c064500501540303408d408206144242d14000b0200360a023081a907075254421840d00144080c2203106442e103d00001e8035000a00030307540031141d50003985256034a582d0800220390301c040000c407034580100c0360f1039058403125800311005501400e00580e40f8a884400c2045c16002c020300c50910501c0d0240501c021415840ac0030b501400a08140e411040107043c11803505400c400c80c864042000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 48789761 1250 48788511 48788539
    0xf030e0d0803040308090a0803011a0903010c020c030d090b030112020f0d05010608010b06030402030d080907030b0c090f0904050a0605090f0708011401050d050a02010c060b060a03150504060e04060515 88
    0x140005603ca94040e0b40c03030140c3c0e9200c40f60440e403600e021000190001605100511034140b92202170b1441140407005d1600e0080b040f40441d003903e100441d91405600410740c140740a0400b40619400c1110070329148281504110101d0210b000600030750721400c9101c0801001c40d25080082c80c00041c0c0204210240b0141f0300c0d0160207082d081c01010240d50802c042101d240c101141568055540203001d01210064028102c6504800411031402d0f4802c1c14800404034000b104a80c0c003910402c070300d0b07540e00ca0700c4000303010000003583c0d41a0f000c3c400d56000c00021842c081690548103601080205a507203d040c0400d10b082a00c0c1c0d2210400e0090423000900032805501c040c5000d01e840754010710381c0e0f985404110302d0f07400d00c0c0c0c00541190400d0181d10010761240105141745841500d001801c242010082400c9800030582c2d00082655501e0100511240c8585a402010102c03000c0c0501406c05455000503840600300414440e00d490228001600314020000c14030000f4264030b05000310 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 48791011 1250 48789761 48789773
    0xc02040e07051003060803070807060b0901090c0221031f05040c020303040221060711070e0f09010e03040b09120f0a0c140f010c02100311160501050901060303020a0f030e0d 76
    0x11482820f00c2410703c80e19507850503000b4000e001c21117410380017443c10000e494544090540c0f0041c421210b969032040b0f16400c0755244c0203003501030b24401c0b8002818a142c000040c2c80e00403075403402d01c00d9240da03002c141d04803401001220350001c4410030002001e81c0c00c0c400e4101041103a007005900a0410150340c914950000166200e94022545041c0c42548503040c02500a484504806185c20000c00224064007581441d40c0c20891303481290407a80c1c0e80c124a611007103099a0140c04000e0140600010303d00900450a003508120081d40ca090304d81070180b881c9103d000e8404d030040c0d940ca42e5132070442c0c400b03000ca020000c00c00d030141c030343c601003500d0700c1200b911a1b8001c5007405004541404005e05244580711902c5070181c4a2682c010f146030204070036145a824440c0405465050b041100d080d03141c05480030f4440c0003071070321111540346450f5003544c030010400703a1560301d040420404a80d002403148841c0d900010036000e0144a420204c51301580020420381015810700d0f0b503010026 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 48792261 1250 48791011 48791023
    0xa1401120614091b041a04030f030c0b180d0c020a031b060f03020c03040909061803030b03010c0e060904021b06010815070305070c061d0a05030409051602060f070c02040e 75
    0x40221012481aa07407103003003152110413003941c0d5802010034031082c01007449826151950146508130f0a0409a8035900c0901e0510f04140407400101c06410b000704100e400185240c11550100b9000c074071513811189242daa0002000c844200540131090b5400d648070b2502c5800515009000d0380140c042c885a00d0f031083c8002d104103000a84000c0d0824600f502c01d00c2a180d007502c103400038602d4589484da031100503243c03203030058032066913480344102d548244183c000041c6111351004206402d4103001c150858001c809a6000c4c003052034030754801a80c408044070b064907821600140c540211130001441c0c407000300f0745100340703100d140000310b0700307031000030700080508025034103d1103580e42c1d018210151102a100940407800302c2c5800800500a50030401c0e1480003182d1102e05414000c0000703160038040942036a031034200040c28444c18101e8065207500c40c0318610070780c01186189800a44d61140146101e03621903000c004910814801d01d920710045130014818410840503602c4103884007 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 48793511 1250 48792261 48792299
    0x120e040f06060905030f0309010f0e03010e070603061208071407120510050709080604060b12030414030c090708040818060a171f0306020c0304171005010b03060a14011206 75
    0x7902d5143c002458034000900007503028a00014504084401006450084001100905118890310081d01d2601c0034031071940700c1595400101043d9140640c054100c9107580c01030030606010381c000c0004a0300e25022a4400b0303070701034462a00c0145240a4600740b550682200759035606c044940da05200000981030700000005504108544581105aa00407128030852080340c20007000600840c500380e02502407a071010b0b0515100703038240c20103203046034402d8200784001c0d0642c1039000c450f418104603100f01001d05131038182c0c16051841c4090303c403c0000b030000f465410006554600352101901c030b0601404080d0010343c0307910001c0800341c100d4044441f0100000180d100003401701080c2d0f4000150190f1102c5401510b5003181c039101d000e9400074034181594803082200040404a224001c03e007082040040c103011b201d008042d00580324183d220300c003c88828024440e141d0380c0c0ba45441c003100c940b8803442c101e0b84541e00060381c2d80440e008021100a181001c0000c0d50a8081800d038814 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 48794761 1250 48793511 48793517
    0xc0c0717010507090e06010507020a080d180801090807200904080c010e070303080c0a09050a0305031306080c0f0d0b03061503010b0303190503130c080a0309050f0d120e040f0606 78
    0xa5460510490f2071101510581071750349419404281194010002002c2a900282035404040d80390031030340b85040c803102d00341c0c000900d40490705002e002c09010884040d00d000070007400380c00c0603a10380c107149000340c1001401161170210328000203918402880780720702010b000804a40752608101c0c1d0681c106044020455081070380b0128024004918441030743e0f40b44e02c40080b00d4955480c000407507040745041809020700c42c280401c01e40c2e2074199500086201d10011551104112068488100b4580c01902400312a00c144024850305100340c44551240106007912041000e8a50024081030210b660305802820284414000c5c20030214500c0d00050b4000c1c0240c3e046070b0245540c2e44101860725020038040c40c040000c09120300000c1d90013080d00d40c2800c1200b0502c0c0c840d0105c80025174040c040039404185407504042c2c011003585d00800c1d0071980745040f012003c01080200d0544403004001c9034200603202030190055801d00e020303240180c4100107904465208600800f0540501004 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 48796011 1250 48794761 48794771
    0x2040501030e0a020108150402090a0803070c0f0f0501030c050706090303090203070b0a3e15060604060509040906020412050309130e1e120307020c0a0504060803120c0c071701 77
    0xb00c0d140011003064881e03040e51401300650310052813074802080080e299510a800f0400710b00140d031000c41020107041e00e08041d590300c03001458411610b10b5158414262502d01141c20007286403010080c00444000782000300c0d01c0840f1910407166403240b028020300c03081c0b51100c102e003896410b41c04403e800e0b10030781c1214003594480a41c0320550080007040300006100601c4901045d4800846110a01c1d19025610900c0c8000d10080c0841c0740308000d110f00380d130240c0c60451000075200700c91904040251031982c0313445d0a045000380507114480a040c015034550301aa41080310f00e41c129001404641040c8005400d9031400c6600d95110b41c0d020b611a02c8042c04800320703812584541c44015403008002c0c11076410580e10a0281d10070005165050302454100164442c172020040d842902250302820070520188104102c558890b00141e009514016050284090000407030309031501198006495544041101c0440d00c5440350502490060b9040080c10280100b01120104400307002800 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 48797261 1250 48796011 48796031
    0x8161b0b151003051005010509030f01021207030f090305121005060a0302120105030c09060909010603061d01050906010810020f0f1201030b01090209030601120812010303080106020f120d1116060204050103 90
    0x402e42d0310075540c2000301401071030308101b070b9030050004002c020806029240c80c007408030416402ca0b0001c04050451840c400104280c05505105d00d0780b13280d6214504004a407500d0300c0c01041400307840413407030a0241c40c0e00801c000542003200040280802014144c2c0c3c0d10781c4000040203500306900403015041d00c0f1002040500d00410040c54222000d8141d042940d900b008101070400050b001c464a07542e00c1c02c01001040007400f94098035210a40c140c1d580c81e580684842c01c680c2c0081c52500c09400070030062102a0b00420300f140340e0450500050f071112483c462540d010f00c580c40b80c4200f41d0400054003071140003880b80e001c2c1280d0244c43c40c2e5284e40e998000394000e82c4550042c0e0307507040d0081401805800040c4040908080c02035408500345840d08200f41c690080a03001030700072907418401006000d07130401090701b43c0040c0b000640140c504c0c03001c0480340b0307000c1e001441c40d81703a0301ea04112081403001400c3d91505601c681d2406069000c4d13041c0301009500074000c0c1c0d030000e401c1182d5a6 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 48798511 1250 48797261 48797267
    0x4090b010605091e0907050f0d0203070e1c1220100501090501080a050a031b0206030901090b1302010207030b180303040602030702070b04061e05040f06120c08161b0b1510 75
    0x21341d1a000035086030295600c000084030907030300400c0b048480c00000e01110741d00c0102c41c405148120000d0303c40e126403101240c200680309441c0e040c0c0c2e001c06610840f2100c00240039091104031030085090a20b18024051480f038003522000e102140302c0c1c401d5a080800d444030075003001b41240c10401040101e641c9801c1c002d40c0b10050004060610703880005844c000034890303000340781c40e0040c00b096401c8500142d030008a1755402624802c003160f440305c010106001e03004460b01c4d000f0340301541c4200c100c4215030020b0f441d03007814800030341a400d4040000e40d00300300c030900c41c003da000c0140c142c030f96a14103890300301e001b50802d5a0400c0148035884021498500c3c450484040e5562600c400d0307013940e44e80c103030090782005c50507407403007040001c1c000056690b041101c0321002e822203880c8c550b100340c924007481040711190045401042500b03028021255040c0c440c0300b840f0002840c2050060410146441c0007265108004040400f01d00403c80c00c558030b0610300b41c009a0071551611403005084c422 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 48799761 1250 48798511 48798559
    0x2205030129010c0305041802091c030207060516020d05010216050a05060f011d060d0519030201200a1103090d0f11030f0303010603021303020607060204030209011703120604090b01060509 82
    0x103021440412042c0286012094245c15806007c04050f00c0c2074600f4000ca410f44412400303604107040c04010400070142c051116001400d11458101e080074004810411040241c1c20003a000f2602030b0444024001c1c00c1d0101d407a40ea8200c180284001c425140c02d640e9840c02d030b4002d032007600658010079045200950340c1c03412654000b01c120180303107030704150444415018050707a0b80050b001081000080b01409140700340c0b814402031504c100e5660034007034295040d45e014981c00140d205007101070189880d081d00d10392020b5182080b1a00301e00080c407483c48c8584c402c2107910840304a40c0300c0405c107860564420552160703100300c18030b00c1c0d040103042c1d07503000d42289010300340c1081c0300500c011482503001c0e120380c10300c03c2111002079680b80c0106003560312a10095810035000030f020300550405403040c81c01018112400300042600e4000c4039205d008012148001382e003072401058070341c0d480b40c211922170b98100407000c61550355890046c28640c8411550350047c1d040b500b22a524452501d84 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 48801011 1250 48799761 48799763
    0x7030503031015020109050319020a050a0c0906090203011503091b26010e060109050c09090a062105060a020a140d1b030b01140d090b070306060207090c052205030129010c 75
    0x1141031080309030009500f841d8509d80d9004500c600094800464001c10007061039a02400c810203005007000c0d222420381d80560401d04900340100700400c044001805c5000c0490307501d1030001240c40031480c0c07190900708140c0c0c40c440600e2080e20081140c0f01c14225050f10b200d10515403d10400c13004840c1800d90720102000c2c1e20540204004226040c0c5580140e50b003ca00c4465803817402e19484005404001c05030b4603007141903540d18090080040200650070120001911940179504e03030380e5401c5d40d8110041031858460780219110040d5401039140c0703c0341c0b19480840540300e948444a500081c40c8460007040061700c0c0300142c01c40349000344100350650b281a528184520104610b8445560010b8406034036030f66522002d0020030b9050803081e009003c2d9541c082140791a005c0002c2c5050038a4000c40307001407600e401c980703265070080200c0304844180f200885e8401c00480d0f0402090313107035510094043d42008240044040e03104a90040c2c09400c014130810a40140c1c011140e41c3c0f40301c0d00c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 48802261 1250 48801011 48801013
    0x91103040b0702030408100203010305060f010b071106130305010e0606040204050609010c02030a060204150f051305090a0605060316090e0906040b2d0603100c0915020703050303101502010905 84
    0xc00c02044607018116444811401168034080d52817121901e030039000c107a13810030720754080010300070000d041c00640d4114444078404034840d4100011411180300b140002030a0601036540f100700358031000156407001c00c3c1d001e551501c90b503a13802c241d406031090407414041c5000301c4000500614052096400340c81001e000c480c18602010700548440000781f42c160782c07601c0741180340d0300015054001000540351000074000032101041c405048113117040120014410140308c06030b00602c91285c10412118225101c03c0710761624800c3e140203115a070401c80d0891000020800c400504031100c050340186951602c280655900d010758170400140c55070501600044045070105116204a98201100e400460036001c080b20040c0f100b84074000c1d404038490046000c00510b480c062100a00403007190400344079013101800004d010b0354aa000e1000351000c0300d1136460105108015002c0610340c00b03c1103943d203052610410b00031a1a602c00c1e01880401a250400031901c180035100c0c2055202c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 48803511 1250 48802261 48802267
    0x30b0114040603020904061e05010801081902010324080304060e010504030f060518060a050414030a0806090c1e0c0c0a0e040b04022e0f021209090406060b0f12010911 73
    0x140c2c040300658045503800380c0c80f5444201c0466030041416400b00e80801500f01c16682d44e14010016100030ba0580c41050640c10125000b40807240b20080c074052aa03091030001502130302c1442040008034141017800f081c200756100415080c1c0000018404d413039180d101c0300f803100043c000440b0140704600005007010050450880002c013181c00098002d00300840c10840c0303561141060303180183c100c44081b045900c1b03c0503c010b1084821100304c1c48100500994503010790488040d10030140981000c2c001c0190320001a00072049105640b2001c00d004007540c810220510100803540080c43c5101d6240514011004a0b260903080042110a40600c000c1c80360386a4880440c44040104180c1e00142c0e141d4125101c00079145040d240c05060b98a001c4150352135880051034250040104d00555100107a000d070325070b043c6d8059401c204001c0318804501d60711840e0190103440e1960104d012964042140c2d42c90324400c502400b0400707003040081c0d01581c1c0c0e4000700170079180d22807081c6d04000810 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 48804761 1250 48803511 48803519
    0x70305070e0703200702130203010506070f0510020408010518030415050a021002210a0b01020a0f06180b0106110304050d020d050106051e040b04060503031210051807030b011404 78
    0x207008007607110241c1c0c100081c0d2103180104ca000d010310101c9201da0200c01c0010321400f10315103a6160b013186a5000c04c11810f6604040c04150240300380b28010780310346500c020280c00c102041110035120200c0001c10f54446581c0c0482c14003804054440503082d68044c840014034050003c00c0c1d5080b034885031071a601c04400600c1c1540d1030b0344403268400450041c01150304c41d07084140018480741560500c6040500e0301070030790010590001d00080300d01d505140c116540317aa40080e0301e9004982101c41c6202900c09854140000c100b81140381400c60344032403850007802030384040c09040705c496407112004442807004c01c6882e84581c0c040c5a5101d98041401009418094078419507070344124000540b0b680c07a04001840b600f883d00c410000e526091003c1246800c150044100203441a2010301015081200107034590044240b6032016451010005030808440716183c0010003005d0250b80179064828644940c20b24211440300200e030800d4014082941701d440707031aa180c0200f0348000c2c209810 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 48806011 1250 48804761 48804779
    0x111c0207050d181509090c03060602060c160605070305070f0801030218090f060109020408010f020c0a02090919121d0109051002070801020c0a02040501080a0308040215041e0906050307030507 84
    0x4000000381020200f50000b00305414003c000300f583d10002c0d110f2011041c5414184d80a541c0701c02814020507003007050800c0425000211250084820351a540d1901c5d5011000030f070103044a040a04594104402d2186264150380f00b036010754116900c165070341c0b20020081c1e07041c0c8400c1c4802900b0203d8644080701d5140b41c428800c1c0c00440d89025a50740000ba07059441c5000c00a030000b80710f084c0d00217020000c4203024850b05071706d140c40c240154100440350b900940c66000107070b0041d0142400100040304480c052050441406000b4689004c480345070070449c660b04410728101c4085028401c8628130811141d03024110a0816074500316500e09050601801d0401c030008e03081540301d00c00d008a1103030020b0001c0c2142c001e07000c1c014000901c01c0d004000c20b50304180d10003c800d400502102c00800d500c404030f180d00c9038054030044061045801c1c0c0341e5003071189500002000d48140b8141240b40c01c2e488001089a094400520106032500e0400d43c075500188001409544610820400b00030 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 48807261 1250 48806011 48806027
    0x307060f0207080318060108161503020909040606140a03020f040903020304050a0605031006050309060106031a090a090b0901050705270d050303070305130c05010c0203070504111c0207050d 83
    0x491400301504103200b60b91410307a6074001790703003014007039441607031085450504104150040890000601c5a000707980842d9400038400d0140103813403400710310030f0b00009000381c04540b484500500140ca5500d42030409100810250040c1c12502140001d184054903100d00b103101903e80043c039849200e114041000028429002c040f003c1d80824040017555980d070405400040c8040e4865550700d1400c01d07404100702c0019003050b01448011300a000d0110400600241524444d00b40040c1c0c0410001c035250b044a03124283ca40e0002101c420094440199041806142e03c98100368020740c0315010300034207940c41100c240001074410303c902050600c440e4132149040084500c1d034101c91030f00300042222000ba05905a441d0360001040c086826410700c259a48440f540001e800c92100701c0c0e542c015140b03851300c0340904010241c101101595401d000d90002050024420001c03a00c0c201c20074642c035007140c103088030600b01d04c111080042640303008030b5003165840030240903060070200003500c100c1c2c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 48808511 1250 48807261 48807281
    0xa0503011e03020916020f0601060e010c0302030408120c010f0509030a0302070204020c01060e072a080705100608010c030e070e0133030225150b01020109060204030f0c0611030706 79
    0x3a410400000981c450340e260f503024200140c01701844451050300a46402d110007003090700d40e480840108403041d48251803542c000c10900c0d0648503040d140c1422491401a500b25030f0060113601990342d000703501c500c010000080444000d00101c03101850080031203500b119a0320050700b0411400b01c08030702ca40c0c010025584010401420704a1890740302c3e084502c59004034006989490070f11600c95044038598202d0060b2411448007005407c6520307901754480c00c4010a0307880086208010000e00344042e851070440c000e400c100c0c00c1e075101c4581e0301030005850481c0119142010b280c1c501800851720100340c900009041c2201d07440c00c005000064000481d4910680c18544c00040c0d4900d860324000d0141d400791382c0541c446130a03444c00c58280c5124001303402071081600b4501d000a0769184080d80600a04400041403401800184c1c003404001000030005840000d0200130450100d0440124034055441c0328060782d20780c101036641c00d40b4461224020f0f030051050100049054015003528 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 48809761 1250 48808511 48808559
    0x90307030e01050a090314030d0e0d09030821090a0c15140d0e0a0c050307120302060708060a0f0303020609010605010503090709050a021b030307030c0305060f1c020907050a080105060a050301 84
    0x411b54075150b9a50400e00781d5080031080d0030019541503401c205000d800f44000701040600703124861f204002d4001030703842c44003d203086d20200710446003900401285840004083c21002e070381c9444c0c5030b40341d200c080091086400b42d04564010400012403400c4001015494692002c01800a88842159000365000035025501c40d011010040400d112284d681c0d0f1040941d404440d042c10304150800440741c110031481d03000721501402099000030f005420185034101400113480e18800b0030f6003281035402110ba00c02d0203910000c1050f40c00144c00780f1490351503000b00601601c070801120b4902c400c0e1140c211981c010141440400c1131540840d800c600301000041c54010410088954100c004941301e00940020007004034068040c00340041c11075152604200d02d140000c002400122216070403401040d03141c00d00482e0301d11540c0c21328443d81d0010030181c102c0c5001c400080640d03004211800016483c000005030a007804000d441c000d41e420348030366003140c0c06c0c14903c000203401010702d5088 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 48811011 1250 48809761 48809777
    0xd0f0807080f070c09141906030b0106021f0b0607080c0313090902180417070204060512060106021501030c03080901020a0c03051b1c0212030705070603060608090307030e01050a 78
    0x40c44007004140e0981a50101d030380360007607410a129942415030000c0506401d00340a4140b83c0540404075034008411380000c0e01040840307501c14010107460304020b040340540d50000c200f1540024000200303641c0300000b401560001410801038410300701005400c06400d1012200190090010341000307446c0303208a9050405045004224504c540c5c810449240e481c090781040d42049104510300c1d0740703c1e495940b4181890b50b079030011713510202498403189034041161821503076a40c110034000c00d0003d00211000c01c0d10b9522035180c850070f00c903600c054414a1903140d010030b041100e440c1202d0300296850080c9296403a91003180e8000290b0f64114081d200101d40065100600080514000d074010b04408458400c0100102001c9560381e01c1502e00c074140c089602a025450f00d0300741d45c1a84c0380c00400c44158000361541c0104d0310018040c1c051920041102d40c1d0650080080301d40c1030b6911001e41e150484031940742d1240e0800500014410b584c0406554010002020038542078584015 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 48812261 1250 48811011 48811013
    0x19030809010f1e050a1101020a0801090c03021623060408030f07200a030e0109030203030904090507030c030501050a060e0613110408010606020f0c060c03030103060906060308030403020c010f020304050d0f0807 92
    0x540c42d420380d00d0510110328003184000201d68840786c0c02d500000c4000c021890210140320252600b40c0520941040545410307003024024400e405844030403540d408240300c00c03d258274020038102800440b295010f40107800710010020005031560145401900da00c0c91b6440704060744190900042c441c10178049442080c0c4129408040c03c14a0811088041c1c0341c011000d14000788030701081303107802d410801d0700d41081c40943e50200032100708032800c440020b00c102c2e1038503141c1c3c1031003119440500a011245400000d2084c1074001900c95018464204000398484001020042e400d8940d0364221108407441c0d00d0400b070a510041c5c2040c103512010341003a549204207800d42d0056002040181c00140c4c8602207480c0810141442000403221070b0f0410100c0d01509079240414070000d00b0381a1100001010f0001c160300c40d5018640080b203103a540d00e8a41400303940c4208803040e4600254124082e01c180ca803021090b24107407040103214a4158001d512a14802c90b00c808080d40c101000301301c140 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 48813511 1250 48812261 48812297
    0x60301110403030302090301060f080d210509030c06060103090308010e0a09080f04050306090304060525060f0b090612060a0209011101240e01030302060a0504110a1419030809010f 79
    0x72008510951300565600b40300002e06094820b940d00100340700c18001002c3c80340c04004202c115080541d450b00d06000c1122101007288640d0241080c0541403801091109071000032004004020011088400c01d4a031140110b00308c2e248c2d03c4000e8009030f18600144048080c0c41d07101500440c1c640404581e000090b21000c0503680a507841682a244c001001c0007542014002e0903808101080070b14101441d1940181951140e110058100c448000d0321005271092100c00c100c0540d000f05080120030408000d4600801202024a108880a0001a0091611700d0303030b11501d5240c040c044c0c09540c40b070961441c082d4001600c01d5060103000d00650395010024451203046000c0c00b284850798445010300700700f102c00190402c00010070702030010710200750005185500448070050004c1c1690322800e082c100c030005550807540c0105140c1c000501124030006640e4141360840c0c0045d1481401502540300310424800201030301810720111707030b81c1d40c01078505a41c0c000f13140c28200d0340824912001 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 48814761 1250 48813511 48813517
    0x306040e0c03150a0b04050405030a0809120c0d0e030c10030c09030b040b011d0c120403090b030703050f16020a08090103020405030307050f0d0905030c090a150e0a201206030111 78
    0x4240034611a00400458041354007800c0c035110303025101000355061507105e064581c403c0703541d0082030240c2c510225084000400425100344c01072607090380c80b400482841c03526000805240d100007060344450014518021804000c1620000c02c000d41c4c1c0901e0720410f80107010703d4990801801340741140000400c000751b95a40c41035204a903401c1540d03060505003418081003a41c40301ca0791f8400790400040300101c104540700a0401c0c101c01845070b880b440d0881d08103c0c0384e040303241410804418810426055002a2b00603254510348a056033740d0682002c0f60004400031070401a844020b0310004106000007d2401071030614000d0b1600d5141e5001c0f0340745030301c2030900716247c0d88403424106a200c002c0c0075503804250b20f407901000b03440c41c000001c4d0703071004005940c0d8452803541010a594095540c04415007410070301c1c0307820003566180003000321500122001d0400b5810011001c06186092240030191920410b41d6814081282c41201c0da90030002c0c2000d030590f5a5414442d1019014405 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 48816011 1250 48814761 48814783
    0x1303050f010606050304030912050709090501090302060601050c1b0a030c0b0304031202090a180e0601080d0206010f08030a050f0d090606090b0906090105011b0b070203040303080702030f0306040e0c03 88
    0x400103180d400c100c06007180c038039901c0003041060034018400000e500150a00488a00241c103a040340c40504042d402c002042d8842441a0301d08038410707080080c19040b50300818000d03001d0350302035901c02e001501c0c00e220303081c1d203110180c00203164075918092600c4103070200c00c800b41034403001d581c0b070740d8a80500e11410b0b00084c0c0784c0c0501100b04410151312221020300c804280b40154100600c41e4082851452035002d1500c91070701c590500a6016180da109041200c54101141c0e21960b4900203030b5118068448801c0050203000008500441c81440060031030312884000c6180610791034045a0903042007400020050b002c10800400c0c5990340144c1c483c95010300000110704d1700d4a40e0340002c980100510900030040d12040100710350b200c1e20080c0c1140e1083c240704a103000d448028082a01c50344130005c0130070003042c0511644503400005041500c0c07083d160100c417919600d006903541c0c000c20030b040c0d500010400004806040c182c000098820034034007203c3c8031190210005c1c3c180348401c91 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 48817261 1250 48816011 48816013
    0x3070308010e010f0302060708070f0c0b03060f0315011403030d090303060501030e2a060702061305030105070c0c0b090109030503190909060e0103020d1403041206060504051501030f02130305 84
    0x4018081044404160b07401800d25040351003ca6141d5400308020b4000e411010301381d000301158840522103030040155165078000000401c080c1c0780c09416092760410340b0a503018003c40d40c03500c8442d00f030015480c0c2040701d003095007030301e941e107005a4a2a01828100c401d030b0075000c1400000d603030703030b21600417001c805209460204d0100d04000004007101c122500560b255804650f81c0c44020341c580101892030403003c60b00e0956464a034010a10500c00c5041c000d4020304005074a1a000490700c12007030940c0c0c0118000d00c60b03510342e004100c0f0032010180011340070384240304003007110400c040d004210010040c140303510030541d65181c450840c0c106065041558940319000b9a481e41d02000e200060a6001010001c0a0410300c2100402005002c002d015040d543e00701001c0c011b9a9406400c0a22030354126030b9910b80320701040710303003075a04442211180c0c1040780101d010718290266512580360701041780110f0144100460142c440450489150341d130801c55000c00040007010040a940108 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 48818511 1250 48817261 48817277
    0x31006030b090f07080703020f0a030603060605040e031603031409150f010b0a0509041b09030303200904150503060705040611070f03030507030e090f060316060e060a11030703 77
    0x140014065400384070106110341e0b6200e041104092910b4000c40d00814545425080383e500c404040d0b00034801e130074041007000c101040206143e43d15820140076603110314800c0c02559620000d1005440031540d1a1550ba0024010070360301e400301c04180c0e40410b000c0d1401151411440f100103040c6c040a5450369455041249500c40501507840919004010300c0c15440030f81d8901b00c00303110325009526051007004000117403071010350355542102c151400031940303019000c3c084000103018400c451000b200400e003448107008102c1900d911800c40da401007c50039203410700030000c01c001090b0900c5520a94443c058001c16a0f440400c022889505181c840c16629400c000d0302904103020123840c403001b944070043c140300030425003c90741c2c202c941c103042c01c0b80c07a02241c3c0307420f07a0703180d454880003900001d0100401c15100b030000c000720701034101036041e03030310349001d2809040110882c2d02440300031808041008a081c1818001131503d44228a02a00e280c02205002411a44030381401d9001030251 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 48819761 1250 48818511 48818519
    0xb1b030c0301080c011706010c02010903020907020606090702030a0c020607060f0f05091e070e0c0d18060c0305090705090a02160506060406060f080403080a06080f0a06050603011503120504030203030310 89
    0x101315008119409091200b0800c0003414032410368040108000d04000c44102c8000841e40140d03003000266500500034461440c044070020750300d017001c82d0303024031500c0201c0c0880d00c42c1c6d001000300d5039001c031559120105040343e50207029442d440358604a41041d074440015181e04042c2c0b01e96001c20903296804501803c20307166461600595601d40c981ba03000620002c1000200000c401f02204c01c02450b42280e59100c16802d28140103810401c00028204170503a44d40c103801080c000d0781584602e60030840c3d400351500440032240101da80391000d03400f141e0305011f41d1816040296100300c0301d4101618020110845c40c01c0708140ca0021140c2d6880304c02031160907c1c16020f481d014020b6894406100c0412400003003221201070009810702100030003042041240390081c0b03024040d45811207540c054032504250f80d03000e142000b903407130074030b050046400ca20381801142c2011b405401c0401809045481e03108071560700480c564140b0004010010050300c05101951189400300c031041105460 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 48821011 1250 48819761 48819763
    0x10e0c03010501051206130f0212010606021203040b0609041110031409060c03010b0906130b030601020f071401110106090908030f0a0b06030a1d03131d070504030b1b030c030108 78
    0x1130300102d10031078203050250749400b070016041e50321201c1100b015210b99202c0c103005c04c0c000c04e07440d0080c0d000544c144d0040c5044c0710540060702140c0880e0b01b00d075100750f00c3d40107117421808281e42c000c04020b01400424101c1c90028275542d04513005420320840c075480180026844500c40c1c0040c80840d4071410300660400014030200c0d4003816045c007800140c9440b85c0700106600c01402110100e80700426055140d494000a4640420710000c1420341c4a4891701c8034002600112911030062040e00355400c030001c0040760b00c0c0200e4109400081c940180c603c0192007031003440340c0a05044d903a500780086c043e03030303140108000340d40102c041f070783d44c6e040041d1030105038400140f600800c00c2c242064200c00d6241c0c1d804581e0b1042000d880064403852028282010400c1c1c049124100e200115841002c1c04821a540d42103d103046018006180d00304060001c8010441d499000b207041403004001086803010442e50056144641441f131000ca501c0401041c0c1003591003180e400701c04401880749140c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 48822261 1250 48821011 48821021
    0x3070b190801090204030c05010513050402040e0f0702010903020d260a050103030f050306090105040f09020a09021b0c031002210403090302040b01052701020c0303070b0a0c0f020d03021308010e0c0301 88
    0x90380d5404d40c034081c15a141c4900c40c207500d20881d0b04104000481d01c0c2c0808051072180c0142100500641d921503032031124150300343c000d0f50f03551228801100030441d114014400c0c0c4090640c150041d003480d440d24802030300d1400300036203002040b10082d01400700c0150500071452040c51483ca0000e059419424010000c4081b100c00303005220301042132000681d10600b81d1750440354122804510303051200c0702c000144c2400c500081d004030301c801d030101e0641816005414040025152480c5902d41a03209694890100c40340c075030150800c1000300c1244541790000c1c591101c446013501040c0100c4044040151000c1b24241d0000c0c90202d414001c519150244a04455007441c2c007500344240c520b01c40c50700c03444441c210382104020003030621059000b44501030802c400101a0307031700d825103400c2000220380200c4500290914241c00784000d1802401c421030010740a40c000c00c02d0003c2404150001d510201007490380c18007184c0d00017100c0303009000714030600030400060082d0a50070014076003521 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 48823511 1250 48822261 48822269
    0x5090612010525170a090201050903010903170c090d0809030307050a08210601021902031606030b130c02120d06030206030405010905011a03030d020310030b0108150f06090402090603070b190801 85
    0x34004810b07214a0501c1c44c41c0c660403132580c3e140044c42c280e4510040c1c0e054412014100d42550810354410b040c160407084034640f40c40c039540030798582d90710318502441602c102c02c1202e03803044503911010f001c21101e00140442440c050116840c1200c00e44501d89002104201180d0312003000840c80b5110390680e100b000070b846160b42c840c0550900400207134980d0f0742d003c3c1840301c0641d01c412003403e540e020801e404080b084202006a900c1d01c0741001006000d248440340c2c010f080c2c1a061041400300b0344071b0307049521120342c05000002313078800c82e000445d40603441c510880ea031600c0c030100242c0c0e90b440045010304e114000001e0042c030345160240c255115007100d108030b10a91190a405514040200c0c2c03200c038510701e401656507403510b10201816481c0e420241600d0304200011581840000b4a091424200c0051548a0399481501c3c000c0d000c0460b03941d500003001c40d0105005040510715507410036001004d4038030391510752022412a0b0001110000c60103280700e49407070000d802c151041e0140c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 48824761 1250 48823511 48823517
    0x90f060403090b0901091e210302060403140705120306040f0504110d030516120801080102070c120201050702090708070f09032a030804030807120509030705090612010525 75
    0x34034154030042e001e9040e512494082040000d002040c9a1140304060003409a407102804185d00030304201d5515076160103600050500404006001c4101100d0102070503810b90060280d07a0303503940e00301d0311030001200c100140c4105001400005405101109408001000701c40d01c0303140060400041c0d40e1401e00800c01c0d0352503c010b00c0007250700100391040010301070f101c4900400c1c80d4901103c1901c14164030010b419107090711402000b00041d19044400c201d035442c08980e98031621014201d1240a5009040b841741083c100719140c0300f99200403c0a005040050803d0041c1d0040307206481c08642110000340e105080090300c507001003103421028800c0c40c00752401e5003156615244182d40501d00c82810341c00c00140f800c0d0306400c1c903012010310b521403896926283e4a00e00034200b508403082c1115494800359420248a11400540d564108007c0041c5412850f04007805203201c00a041c25400c00019941210342020034040c00b4040c9842c002031813031040d07002c0402c4072b140c20801d440c5820 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 48826011 1250 48824761 48824773
    0x3020c1c030c02040209010903051f0c2c01030e010c03060801180f110d080a0804150e03070321091a060103110712020313080f010f0c09030b040f1a090f 67
    0x1107940300c41c070200410342c107660040e40c1b12401c00050f1140180c65000800d244190b003001105a400c1c1c1d1403003aa04403000e0070a11003041d0380c000903228903004082c1c100d0013502c9404190140c45c035240f041490b03180f06040000d006112080024252003128825030080f03070702e0b01c0040040c1182441510760a80c061303490742e41d40c0e078404d954210b000c0c8090080a004020031264848840d910b07211600d40042d48040400d90b51520701d58040c0c4081000c039005e0b622007410381054004041140115444c203641c44000c3c40c6805c88a43e070603541140310381d142070300f400c168429200c56203200c0e12803a60f05902500809565071709200380603024440040145040608100c0010b02d80760103c0e06894a103a44144060040c558006d01246140a10321030050300543c040d00c000b400c0c90000c00c902c42074105e4403000b8880780d0100e140e10019a10050083d0000952201040002c03035011000c00790403921800050300036413415140d42c1d0050800c4402a940c1c8148002800309003002080f10b184010100005411 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 48827261 1250 48826011 48826013
    0x60501241803020603101203020d020601090501030f020405090c060c010b0f0411190c02060d050609100506040b09010c02041d0610030503030c03060402090a09060f05010201050c0f0a090f0303020c1c 87
    0x15001e0030344070081c01440040003158403591300c100c1407400750481d00351451000420303050081d52450f9400004001d40a4000040303400c0c505801424160ba03001000201051090740c2804010320b40244801901c0c000c000003003400e0b6072100014520070841c00004206130130000108130300f007210003014500c43d52030070001003a00c40f0344e00141d503141140b10010090440e10f070384003a6507084d82d05030000c0d48a40001509001c0c3c0340303503611540c021102510403035410303a10640801d0800045010701a0720400522080142c101107000410507800185000034107000181e01240940700813150308183c07050782141d5a19002c80c00c00c049680b20000a0102e00b041d440c517221551217100103032154280602c00400500d80e52079580407a00c060300080e01102c1c25030790340c0001a004000d540034159280c81a0200062203600c14098280110702c60381c2c00d03d20305594140301e80401c0c1d0040c00349006010700340a0000e8950100c5115000650094000e0282248a04101b0001c8001c4074002c1401c220003000c504 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 48828511 1250 48827261 48827297
    0x40b01050a08060f07030902010504080d0305010905010e130206090f060403080304050c0d030e0d030302160507030501050a141609050a08010f0f0608060f06060d06060509030d0507020d110d06050124 87
    0x5421900c17508000502d840240012161741c03003a0340150500b0300c528a000e030310740d40d030591025040700c0e51540300300450390321042148044070341698003c0300d0300c250106031400342c0f42c558001d10303618100810314944041080003082482d0090352081e24205004010001440400d012415045404441242d18580c40c3c0d50064a82c01e00000c1d414025081040d0400c10540281e04441001c0c50410030240050307c40e15001e56180700500040381c8650904021a89519050142c19481042800d100b1040d58401c1c0740c104a902e4a2140d140030029104000100d94071680780f1100540780010002c00c0000c0031407a00d00c01e5454801c2094030407403500c0030030403030800082840c5070461a00d84090f0f803036465040002c0e0b080d020b180d284220b0a49490400100540c20000a0814100075015192140364440c0141d42d18051880045d4001340c41410307190008201c000b6089100400608854240002c0d40310101150402d030094064000069580210f2011503100081038640038600142c21410a0381c2207 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 48829761 1250 48828511 48828541
    0x60309120c02220b0a0b07050d1409060d02090603090d0f02070b032403031b060a140414250302010e03010e0c06090102010605040e010c1409011d0414040b01050a0806 73
    0x40c981803042100c40c03821411160810401c0700d00080003a910686c0310440d4016a5000c520200c0d814400e50b00141c000901138130003861760000020156040c0308107402409403a070302064600c21910f500b00b03c0c0400540e51200514010401880102044c4042940142801c04031003440000d6603c00e07803080141c83c612408076a40710002c01c0ca45a9400022a0710b41a4000504002ca80c54040810016108001d99016001c051165003c9440301d4a901030400c3c101e901111040300580c29800025000c24401102c00c014240070000300d070201d61064001e40082c0c214003942c0343d00502000c4041080d0340e03102401480800003103000f0003401d43d900d540555103c0450040c1340c0221008250310200d60700139804038004200103072042c441400400000384c001d102d21214a0045401039020441c2424610283c41c441441030311071400b000d0302e4400d21601c200c40c1349103040d440340d124190010901e8150080724002c0717206884d40407442d41040104111380c2542c3c0c200302241d6100b1001c0000b909c40d00341907 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 48831011 1250 48829761 48829789
    0xf07030c2303030a060b1612090f14100206061003050702030915040f120803040201050310031a010602060a1512020a030c0806061003020301320307060309120c02 71
    0x40500c185410385000469418074519030402120407084541400101000840c81120b0501040001c541c503940d4064850140c40400b400d81403280e00c0c0040055082c4900c107034030948505019015640da00109464440e107500100480c520855a84c0100d0400071039441041c09580090b01c0203240001c0400c0000490701038550826803a4400b18a100e07009100301c17451414040c08180013259a00803401e42a400707032158014000b0a90b5000880252003500b010303280c2c0d88020900e203540c8a640044610381c001a08282020821420005c0001e081c0700f0b0001821041940d100c0c1c196140540190814500500402400741000205070590102e42184001d4031a2509594580e484034004605207190f0380e00001c0c0028440000400d8240d40012928405c4001710350681002c041642d0480c241d01083c031503550520028404010583c503038148090302034101c1400d601c0f2116107500024904402c07680040040780d903440000d0103014070700c0014041241070f420140e14421860b404114031100100e0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 48832261 1250 48831011 48831017
    0xb041b080f030406080f01060518360105010206040302060403030203060a0504020403120807080c0906030417070b09160311010c0203010b03060114040e01020a0e060304050a060c0f1101110a20010f0b03060703020f0703 95
    0x41590352b155114030580b031080010040045584420141d00c030b088900502c10101a03e4080000042e19032000910500c00d0368590b01822144d2210b590940280d0009003540b0340c0044600e5000c01d8941340c91000e480210b002d0340c0d02890020200f01c003e071080303070094820800c2100c0501001040021041200c00b201d8043e07a406a5030394541c203244101d01e0b0a0185001c0542c0300240e400309008410f00000c0c02a8000001d0740c0100c48410644583e101e641d200003040c10b110364803c1c0310603600941c0d9038a007490005d00042203031010b00300000c0c00c10b131098000303101d00c0c1c071004400b07003031800c0510890b4210038580000b107141900d11000038080c8802c0103049132041d08000001010030205100b08440b441d8801c405025400c20b212001c0c00c00d05e0594075440004081d61000c1486034014001c180d80040c90030300851501c0c0110070104c030342c82d08820001401002d13605034000112800d1060400c1007440c0e104c005610a0480300301360401318050580c4040500520400400340d054034101e614041c3d040c2 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 48833511 1250 48832261 48832297
    0xc0903030e1e0402030108070810050601020d08190c02060a0606030605061602062701030b0f0109031502070c170f0a0309050f040e0102160204180b041b080f030406080f010605 77
    0x8000503008000b05941a80190000c000060340d04000a804419101c80900340c0e100b044403082d9903002c03034600701d0391a40140e00104a46031400d00400c081d80e0841018001d801e003100e500300d120420380384602d55000050f4018010044a00c03d580705050291040b45001d00c1494901000542c060154100004045078000003120840d41c40c0c40c111055140d400c2107005290000b502e8042ca21400b4500842c0407904005025031785260400700ca0403854016168440254215201d00e00c881c540c00e0040e07084c15508010754004544003005900082c00d00400c05044c54507000380550401e0783c1c100034685981c0c42407013454006038000c030b40d06042e11070a903510003150903028001070150503d000c1f4600d01e075100040451003403814200c1065064002d4509020182030048c286e203005410302c502518003e80366002c00c001401480d05810300c1d13500342d0790407902c03d80c4414941e42031006a100f40c4040740d000160800509801452055000c0d40070070700340308158507204010302035119180b1301c0311001c2518 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 48834761 1250 48833511 48833539
    0x70e0303040b040b0310150503061e0d2a081c02120a0305060402040e0408090f0a0b090f0a030b070504180b100f02150106090503010f06030f0209071704080307030c0903030e 76
    0x8080c1b00c0006c14140f1946140401e41c0c98002d480b6600030b8030315901a400c00c0560180d41c04000405190980b005810b02e5800c502c01c2d2241851100361302648600c0006400166202c040f030020740790003038070440010300354180c100310650780a095001464010754004048406c032002801040e0341003549903050104596039504000b400a00c21030300a004c081b489074007071106100c0300101078020480c06440144000080d80208010714083d4072500e034800b0010081e031415400c2446070410024400b0300040700040c0c41c0e41c1c2e041d1017250200c1e03a4200144000c01c01b004004c9007c410406040c084003805c02829503a140412802c1d008001c845046c0a501e45425000d50b01c01c1040c54840800780c0c0f00030740c844d45c40b40d80c010800000351045500c05d40c00c040c800d12220700203129500841e41c0c05441d1041582c9c42c1e509000150300010302d4030083c059142100101c00c0b0700004003921a47c07099003112b075686003842d03020381124140b122050402450050502c0000d421403e41050f084c5d08550004601d111 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 48836011 1250 48834761 48834781
    0xf0a021009120809030d02072403060b0c01050403021b0f060901020a1203020c07080606100c020310020d0c1b0201020c09190204031103010b03060709141f08070e0303040b040b03 78
    0x1c2079104544066800d0305610600c1119405061440b02c101c0585540c100045400c17030340ca0880b8000d524240801d07104a40c1c4003c05c2c2100f6503801d11241c1000b20700180c1d16482d108003500080280c10440e5103030b108000800da414012940c01d440071044041000d01002c001c07d0351040c0711001c0070f0150500150300041d0ba8020000c40c1070300359220380d18038140014060002d01135005042c01c0744140c440c0c03c10101b83d842d0701040d683d11a42c4003800c7c1900745940900100c50300c0302da00030180d030103000d00794600001002500085c00c0354003066801291001c10100020b02442c0c026021504454a0740903100050307a0108110203600f000302c0305000c80340c55180301042c03001200d1001c2d103402840024008100508803034000d2803200101e000708918140081410b407540300031a11140061203498003440769021b0080741188070440600a40c00c0c0c6005802c402802d082c1509040380070070700c04410080a41d60050040d640d030030007078000c0c40c145480d19403149124061402081d80003580800000e109902c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 48837261 1250 48836011 48836027
    0x10501080712051f06030207150504060207050d020601050a0e0c03160504121b06020303070c140118060504060c030b01021002090f030d0908010605040c090311280e06030f0a0210 78
    0x4044010455070070708640c1c846401c0418810004001c40070300c4c2c0060030768021320a07200c040f508060807170340c2e10f082241904000e0a000b0001c0301c00075400e00220b004140100f01107111415150014101541000200a90008543e1100c103140e039482c020044115100000d40746c0204040c0041082101d13a5030007501c85010741c2d00040f000d07415540e0740360f0520038040c5c44503039036020180540c80070070748402007241c8901c0120303691f6010503160101080020a601944050108030b5400000c039800e8030701c44201d0b020090101540c081e9104d4060009200782031182c080442d805007403c005407039407007001035164800c4454130003c090303011a0080030b50b01ea6000e0410600c1008081d0703100c0c2c400046001c6c1a50000380034240c5c956103040c02c0455141845d129030b52092845848004a40d03145981c1c03c40c42855000e0101d40000220030340304200048404c104181034815411214418101103001d0a4014001d010398460b60100d101c00482d0500816081000c0e5019501042c0300340c0c2580701600d000c0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 48838511 1250 48837261 48837287
    0x402070606081204030605060d030c030507050a06060f0513090507060e040f0608010912111002030702030c1b10020a1104090218190605010f0f050a0c08070c0617010e0105010807 78
    0x30140d50340700260f40d4032500007441620320455042085499031824031103001080c40c00100441c44080100001c05e008501907c09280708108a071300c050301c0780d9665402c2c0d5403698404024054001401c1c07000b494680e4030001412042101080f141745c050322103e643d80401e1003040f042c40311003c54603841761916001001c0d2000508802c0c0402a521000c440c020008108142c54242d00110701c8a2503c2c80f0340c0454845c0513514004140030001094408020b50019000109511080100c000c5240050161400d256500420741081090240500c903809580703214030021500408078840002d00003034400c900e08075081c0e03000280748401c0c0c40070a200c00160403070981c0401202d405c205070f44881081d80300c4622001c4c0020b100040d030316401510000d101103104400b160310190b100c0b252501c1003019085c1c0345c1d01c1e4540300210440c01c4d216a2903030352045800359010013200e0402d003d016000800c0030b4039500b58401c03a419940c9040c01c481240345040c02118104a20340000c5050300e449900403050b07070 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 48839761 1250 48838511 48838513
    0xe1b0a0e010f030b090405160b0c15060604090912020601080115140609060d0506030c0409030203030f040501180f0507080601030f03030c02100e0a120e0a0e0405030f040e090f120405040207060608 86
    0x2d05050402d1503440a40041c186c4024208c0d1402050303400b03240056503060081c2d58010003ca245404200310705c01f10040005821000603c4005401e04050240e02015405016448001003100c00003d0820b40142c00039129a030516251082400c134a20441e012205401072803000c40d4940400180c591054401c0103034040000300700c0c10601d1105c0d900850080360101d0440308180710382428042a140c001402401503007003440040c1c44200c1c0c1c503200d20780c0140710f240001a05401d658807021400300ca04016102502c2415141c1d041000c01c201210240118074000c000d0344d85142d80d6040b5224148100a080689820b01c0e0002c0500800c031280e00c40280d0030042c0841e0240300043c503620000200705440e40d1b02c900c9100c000190003440741d4003ea48014200d0000d0b103081a041c0624000087c00c121014801048a0341c040c0d15207001400260154541d006030705e00300340060b18540300e500d0860f42ca03544c0203010043c441030450011201203510a4401580f00c281901703020f0010039182e4480c0b801c03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 48841011 1250 48839761 48839779
    0x3010e0708030a0f0e06090603040c09020c030a0207050d02090402060d1103130201030c0c02060409020f07020612010303020f0c130e0f0a121d130b060c01060e1b0a0e010f030b 77
    0x40c1c0030040301038084a0301941c1c8500c11514042003c481c1050358144858101e40700b084a03803440d04060000f503610074064046c1c562965a80c06512040340e0000700946059000803504081c1558140324400c0140300032222400c6600743d90f00002c9281d040944028403c000020300100b5140041c0c01610006245031300d05034aa1411101800e41d0303d5015404a0009142c14a2450128054280494401d4010f46042d0810f0300380704440009502a05851011080034881000140d40e45d40003031900040d2410703125078551540c500a40782c09444250400e69030001c40d041061621040066455200c0d4020040f504c070304070500840c02c144650004248034040c090260003031002096200303424542c503944040d51a1407100010301440c0f48402841d034020441030712400315038400c0c0c00920038100700810313691402002c0b0032190308540d000c0d400780c4020404101080b900c00e5004540446004c15208428a4040c507000001e00031904100b001d0705000303018002d0388490707119174400c82056001514001d0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 48842261 1250 48841011 48841019
    0x17210a260a060b030f06100e060708040f05010801032a080a050105071202071505040204150312020c0f0916050d0c0801080f010b0d1514040303050604051f06080603010e07 75
    0x18000411201c01d1541c03801c01500040c0c141c2d003081140e20420800511450989845040005810303d40c142141004a15007012949030b894070014500540f003010899555850700170400c4c2e00b01c680c0e500c1503043c400b48000400100d8102e02503031610408229910381c11041482d09844244040d4011200f0f81c42500c5200c1d080240550005014416907101ca10a01c941168141c0c140c0c070501400501c1030301c001070907904105623074004c0c6400c54402040410ba0480031a070f0710190041e11707401614141254103610700b145405201c1b42e02d0801e410798030f21143d90003050100380c54000c0034180011a0b00b1a0203d00c40d1948140d0603101e202d00c400c1c2090040c60501c04004001e001d0070300401c43c1c603000d85091186203c00500c02c018102402501c4412407243d9904c4a01e03481c1c0c201004400e802d0b4480403801115595001e016205134030030b45000030a070902c001400203c40c0d00a14000e1000e04885031b0100347c2c00c509410204840706454400b600b503592801103400342403a0501d11444e0f01c9020741c085 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 48843511 1250 48842261 48842327
    0x51612060e010507050703081008060403090f0605040b0708071a0c07020108060604060f080903160308010e070305041e060b0607060506030f071401030c111617210a 72
    0x844480d00941080c03007a150210031207800c8401c19280b903404a40304004004c002030044004a6000162181d200d645e1031f030790080c0c0c9042503400c580480000b400303000c00340815041c0f43c5501004e0100e610b0094200390a24082c02881e00ca0000090001d9201040e503008000d050448080c0f00c0c045011103045506200d00d82d07040341c1d00040c404034003203804480040e50703604205042d2030841d2003c1da50a030780301900e050706880c81c0001610440c882d000c10461060030803801040400070f075100c0d1b6552040ca614262036200d016401504001c2018181018031000c078803a6800412403840b03820720660041000e240030b90080003440300d5582c1014020604d442032200720f5000c02c2c4902c0054060340c8107546030f0800e1030b882d41c2d40da0040b88021100c00314a14055407003903011400c0600b42d4100030008003042c01641d0b02d010b00030030300d4046c01c440c400c1c0140010b903040806801d00700e81e01801040c5141c21120380c56045641c0b0b1581c8401c8003000f0441030040341c401c007481414000215100d07141001d4402c10a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 48844761 1250 48843511 48843539
    0x1e0c02060c0a20130e121e070c0e09010504051510090f09030306050303030420150304060506120c09010509040c0b0a021510080619060914060a080d09120516 69
    0x1182c461a044c540075140440b46026100506400e5005040c2c1c1401564151000350028402c00c4202208080210301c51034800c0c000b401d0046c003a1a034030703400c0340c6040c0c0341c6e01a2590090004060ba4142000c1c040000d600094940004c03100c4004003e407603840c0704015102103070744e0740001d000509001c0c029494200d00e0b0f020368a040d0080e54140041a254028999244400e8034000c04103618030305020f0308120007400c4403e2190303008219600c035114034045c5072059001680c040d030362559110709000c2e80d494454803825462507071201500c1da00c100200081c2074074105118090141c640c4d08001020000d070b03a42c2120161034148410741c2c40d0703440144020b40e5841c50402c0482500c00c840c002c616017042c241801012600070074001c0100b650344d50004d48080c1123003180c009402c2d498407008174040a0b1405100050503005c0b5940c49103241c030f14200031614125074032100702c0b50085001500c6080e801000c02d4280c0d0031410784100307a015076280c590718161003481e080000d04190040440c1c8030910040e1 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 48846011 1250 48844761 48844823
    0x30c0305010b0307031505151026010f0603020d0b03120409050c0f0307050a0c0203010f0b1302180108090c0d0305030403180b04090b0402040e01060f1e0c02060c0a 72
    0xb0002181c00c8000e1683e1600240000b420760a507041aa401c01141c2d50040c590201801c2c1c4036400840b207000c00320703186010110404021911510108071040320005405081240d031401c070f0347e181d52601d103035010248403501078881010340006910001c03403000c0c0c12401000c3c001a00301d800010b0014048100c0780c219006032003d0300e00f0500801e135802c2c0d42109941c04c2c000901c04940c610f841c0c4034800c1d40c1580c0401c10100a00c40b1000010f005a0740070b109504446003412400714000d00d42a0401c0160744600c0d40d485072503031060000d9074902101d1100c0500c58282803c05035a6901c0d46450207180424106805920030070f8020303000304141d4000041c502a522944030202c0c0c4801c1e0700440a80c00030140680314007104140310400c80034441e50031180c8a8800580018603043c2c5415030740c04044000d0b0000b1010800ba8841415040e80c0111141d040c00810807101c105103030980c00c0203082c80008180a44100c2d000b203090829030790140200c01d04c0640c40401d0301d00d41041c0c50281032030b07a000d9140c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 48847261 1250 48846011 48846013
    0xc210b01060807090902180a17010e0f030a030c0c0803040501020a080604091101050a09030b090d0e1807050708210105030106120b1819030309020f10020309100e030304030c0305 78
    0x1074003034010012207010388555125841480d041210b10002508000301106040103a041191215101c5401e003802601100d0411109202400c101c142921022440b291565120703441c6842e1511001c0b081d2401204145004a941850600100d803402136259024007281c80000502081140560040800d0715043e280c7c50a41d540721420801140c240c2c05001d452a450603070b60b91500d61143c2c0007007040c3c030100e050242a0341d03120340311000111811549a00982d1240030b0004c410381d000104104071003000c542c0e5100b001003c502145640780c000d00101c09006010034450200650700040c1d400891454081c10303c0c8103040c4000c022840000e21649009528046001c10302000c80d2000a64035a0017800c48811925110b400c0324040022920444440c058204001c00749030880c50ad03452502d01036500890025a03030300401c0080c0180201d203901c5203556210041c0583d4010096601140c811100a0100e094400303044e12034030b00f00d89620340d16000c00640070081001e84d41e45101540e010300 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 48848511 1250 48847261 48847283
    0x3030f060315070f0e0102100212010306050a020405060406050a030f0504230319050912060712150509060904020f151314030303010b130305011404050c040908090402070c21 76
    0x600d0b800260481510040002040c3c4036203001030034020180308102100c10320403036103109101342d1500201e8000902c4050781c003000030010403d001070f6000d03a07504000381203011460245800005403041c405c1d485500c0c18002c020072044030850095112942d288c455a109000074076040c038203001410003d8294101074070201845203062540001640e040d00203400701c07260741d00000c100954250304144490395001d840c10110440c1c003c000d12995005042030380320441c080050039a08002e403074034400c00506c4080d811508001c684e80c1c0003907564104406850b0303245103842d01d0008c40c104500380014950442c141803400c00d04d40c041c0000800800c010f4521000c1e5150701c0395030440207090103c104503410b40c01800144000198080100000d828400710400b80564a0b030750f050a40f0805514401c1b0600d0510400040c400c051020320801034044500300840c0d201c5603621101c50107181040c50080c3d2380400d041c41080701961403c0c01620780122001c1d00d1078580c650040d401400244219801071030700c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 48849761 1250 48848511 48848533
    0x2071e031b0305011a0f04110903010e01060f1409040807020d020301051503010e070f05061b0f0a2108040303050c04090908090f1002030915090619020c030304050d0209071103030f0603 81
    0x305c555484410401060a420030580008100250070050aa9000d1000402281909030303424896100850b0030300002050403440c2a03607014604c10190f00220043c0c60344841148a540c80d005001c0e0302940c45100350b80c0340c140b1030000c900318010350903000f9059841e140c02e10000481c459400400300c44114028420303034040c0699103440310a0303032050206080065074140b00d6441c008000c2d01012030b01500c00c000441829180515000712103241e8412074008444110503c0300c401c0841c0c44103000c0c52103c5141114400c0000c15a0000500c090101980c60010494085110007101c0051004c00c209002000701c0d1706010f01c2541c01a881e0602c1340e5841c0080e40ca607810480000d1912407101d801560a0000f0f803014480100c64a00540220060402c460703003542ea69940a803d01011035030760240c00302d140c020082d280900310701101c5c0c800c0e441440100020b60390400303001c101590684000382c03c0d07103480c50199051898110910134034000030040180d00c00080303018502c6500103e003111403560038 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 48851011 1250 48849761 48849791
    0x30109030e090105011409040e0a020303030a060303090e010308090111031309060e060405060303030a0c030b04180201080a05010503100b0d0b04080d0c26060f060c07080105061002071e031b030501 86
    0x210000318001b00700140920592407030960700001342e480ca8002079030300001c1940d00090540c2e104a406045107503440100703009041d0700c08030010162003800c03105490380d4115242e05500707000e68402e560400c20340503903800040205005030b80301c14945501c7c540005407940d0b00e09010380858060b03070300602c80c1300e800904a46401e00400f4001d440140180d07246440d035001c4400a031000822030700525855081e81c0101740c90343d02c42c070082c0c85c0100c1c442c1c5113103031b100d88001041010003402004000741044010f001d181d401140b070b83c00c0940c0e041030000d00342110708003003102925031080203000c0021070700401091110940050401d421100c4041014541c00f24094500c1c00c0d03d070661214100d080c400420381c1240c801841030308244000c00005200d4681d40c00681254440d0812000f1500101d000304058a000d019040c0c0026080314800f60b48000703071400955a40c1da911031688500121030a094080414171030940103503400113556818890040c1000c001e08049200441d402e6180c40b00080704915 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 48852261 1250 48851011 48851027
    0x10e0613111824220f03020102060a09020306010605070c080f030403021008070f050306040b0d050d020d0311031f0807091a01030b090f1005040f0626060f0a0902030109030e09010501 80
    0x2050746480c0352440b038100c2d60075038580040200981310400c40c0e610f072015444007035200005101c070712150b46a0078150720009061400252000c034480782400d2071800140c6d00402ca1505603a500d14140e41c03251940c1c01c00c180d0b14107140d40400301e01c0c000c000f20030b07000810102c01001500d00a46401020b041c0c04041101e28075811500400040d0005070280e0040344154011508404001d0005c19003055840c0059100020300f801220681c0c0124180d80c42c030740e010b02c0407900c4190507040030042c4280e02251001c01d0300c0000e200c40c0b10341000803264040348080103c102c0280807800d0480e4401c9440d5607000d0006d25070611001c620310041010420258828000d45800301c401901c50101520341212403c0c0d0f82501402d2030f10780c1055000c002c40d09031601d00c184903410010850100b0900c0c41c0c141c0445004085c1440d207104141141c552036614100040d07030700c1c1c0180314140c4081c2076650740c40c8800014174070f008000b507155081c50102d80500d2b911415181070100c003100c0014260342c0ea4401950750352 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 48853511 1250 48852261 48852289
    0x30307080109020a050706020313030306050a06140901020f06040b010501030510080d0c1514151c080903071701050709080f070303030207051501030c17010212010e06131118 76
    0x140803800501804090341c01500c0703d0482030070002c0c00d12110b55103000c1642c0003113071a1255002c0c82c110a03400c2c0340d41030107600700510059030350703203500d6081040c0101200c0c00c114013200720341c80000d181c14059208000500c07400603000152001d07400c2c035284c01c0940790000e00c10180002e00301000b1a0b2040c0c0e80c2a81c0c41300301c800d0700f00180203140901e86c042e10755800c1414182e41e01d003114143e080e282199400f81600002060900c1c1c80385152288603013000700d0140c02194000d00c2ca4800308548071542d14100315585401069441d183d205031000a45040b20342e81110a054002c1d00d5510300180054012500903050303616146500c549410b8229680c00005541c1d202e01da00c4810f081000c80d010307900400c000c41c003840a5500742c44a2401d403030158002a40201d44492000d0001c0110440000d00511000b92100007949070180303c0d48020260f01042c02030352807180c40c2902140c0b0700d5907070300c1500218004000c001d100e011201c4019004541051010b5610029081440f43d810320701800f0000b42c034 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 48854761 1250 48853511 48853517
    0x60c030b0f0904140f070302031506180406060911030f070c120c0302072402160f03020f0f0301050c0306030d0c21020307140109061a0d03050a02030f0d0903090503030307 75
    0x407003184410854a184040d10543d92800058081c99942c0411300001e2549034064000780a070b14914414145010040c4120141c512066002d015542d60799150706400c40d242d012032644140c071181080070040041e81d1150003400c0ca010030003000160508080c0d803150221143d45034417135492103c2511070300e08020b401060713441800c20300120030340580180d10780305000f407040710440c6403030f6131034000b1301031407501b80180d81c10400c500d551005904100c4100c455801081d82082c00c0d140c120740c0c0d8141c81c85400b0091055480e129402c58549600450074000c0c000200244164203010351001c070b841d8000e480f02c2c0d0183c01001141b4004038050004c804103903522010b9405a10b11090000300080070b00c005102c210f0104020100200e4211201601c0b9110001c00004403c2c0743c5103480306c201c0340600006011415080400005070356000c0d001c0610607051f0034443ea4400803458201d040d0711861511442d0303001c2c046a45a400125944115603030b92098442c001c0240d20f50041680e03e000481d452400 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 48856011 1250 48854761 48854779
    0x2040f0903020a1704050406170f03120a0b010c0f0c0e06010207030b060d03110d021f05040f02040f110c030c07080109052505090a0c0e01030c020703061119020a060c030b 75
    0x600410b000c003e0070401d13901590300b05501d0382d002400781d88465008a89100c0b8040740e4184e8807406009925a070409840110b24020210a03458400d0b0b00c01000100d150350b90790010005a4000c2c1e1114215039880f02c882a840410340c030b0044000c05080c0101c0d0328110303a42000601d15400040d0389000c6d030750085025130711940d03260200140020072050880c2000090316040412010420034002c204445401070110f0044459131102000d140c01d01d4000c2050800d0284408606a40d210340e54558041c0c03800300b85e80f03890021103800751034140264040444001030140c055000800a42402c0480005680455a403030b00703243c1c26910021000b40264000c050084501c840c0ca9040180c48d11120b420304200f907680700001224008115180b803001a2644146000203a00c1003e4240ca20400d08041120080000c8020740d28506800000e210664500f400603007058480b054030b60000d02c0220b010f5503c14003203802512203d9a00048414905000c0302d000484e0103400380081a1030b002d003102e50 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 48857261 1250 48856011 48856013
    0xc0f020102032404090803070804050c0913080318060c070203010e0604020f12070b0f0a020c1002100b01020a0609060c081005060d1a03010606030b0a0b131502031b0105010302040f0903020a 83
    0x1519008050304690300c1035940030138000041b5000051841445e15403074625182c03a1a082840c03e1001040d0b100340300740383d03038000c1001460840741c44550b101c2d0859452038480d038544404100c0721084070700001a40c800c0800300032a0240d450014000e07541300794003e0100c0b0b54110f400580d01d6206480095120314100c5a0701418203100c3e03850355902142000704da00c0c16076100002c21960380513444114540074000b4815203c40d40411100040080c01da903042c0c0b0300921280300039160b110034014038040703c1d101e0805612980c42000800b241c2030300080f00f00402e5040e454400002d041504080001ca03000100142c3d00c1d521029a0740112900540143d190950701c58841d001041d850720210802c01c070403076031075100c1c0d202440303440041c00c81501e00081c00442c0208211120085034003441038158204401c85081004200701c9080301c2005404000540b81c43d1416800c50142c5d40888540d4071001407009182c2805400050480e8000e8401300f181d050941455015200007040140240c1d0150500310 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 48858511 1250 48857261 48857311
    0x60503060c07030c061a1c0b0a020c21030403080105062704020d05040b0a053d05060c1b06090d1203020c0a050708011a0d030804030909020d0c0f02010203 68
    0xd07507240f192819880b010b4140d50707070a0440f9130a000342c2000000c0220300c900d25081102c0b01d4440c40d40c0c0da18a00c400b880c40d5965441c08420000c02c0c803188260085581c0c50300329010000c0760700e142002c5000b109102d440b02d00c120013540084a05070005160a00000394605280086441060380c0c0c0d503040f1000d00c0081c21a4404005001c5200c0d04141e0800542112a20a1080c0b5008074450001d141e8541010b00d15041601c1c0003510410403606e450112440c040c8000c00c122681c41d1010314003428100d80301c1d1029070100c150307034400c5400801c00941494203a00100c0d80441c601c0005208a500107401000e00c02c1a00030300710890f0304100315802e40323004503502d41d4105a8250061401500d040800740c3d150307041c6886590f00301c8103540801c1c0305004248003801240010050130015400d14092500065088805082e024090210b450042010f15114542a1000e06290041550b48147c4400154010408010f042c00000c803440c58071011544180212405110801000d600c0e4440694102c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 48859761 1250 48858511 48858517
    0x6061d0402240d0903170112110a06090e0c0d11030a060602030901050304110a1a0c0c150405010c0501020706050403270b0a120b0a080312010902030105010206010611010905120c0f01060503060c 85
    0x16814040d041d1440144041c00340006e0303001c0c1c000d04520091409041c1f4250004400c40a103003440707960800024030266500c00c2000d81110b0511107941c809032203401066415110302a1901d2206042804ca10104c080520017940610f036180300030008103640d1a4204e84a0041451042c0098030810218000c2002400d0190040030010010b0380000d07550750120003940b12a80710150300240c041039000c0514020721140000000c261418004520b01c143c0c4991030340726602a0701c2c10311036034075030040070312409505403443c01d0b034404130402c10b030305042c00c0240038816001144d900078050822006010581410308108642e8220700352400c10744491410b40c0c00003160b1030001c0030b1030b90350020300545a880c020741c04014200c84c4051a0b85c0c40f80141380d5510305034160003030801d2500400c0104100d981c00159a0f044940521341801020796080005001d0044000c0c081c180344610300c00d0a0001d04024024007815002404450a200c00c1342403207400d9407118440e6951642201e07002590a502c0c640003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 48861011 1250 48859761 48859763
    0xd0e0f12010e0a03021c020705180405030f0409060504050c07020108040b090c09040c05011b1221020a02060601020105060d0b06060904020c060f0601030b06070f060906061d0402240d09 81
    0xb107505611802041d1403c01400c0741030b001a0700c41900800300d418600300c2244015494405041001c0c100000704010641517001c00214141c81c0c0300240501c20140280c4010b400450038042c0e5031541c2c1c0408201501150003024455498807000c00c6008065500b2600e0196040e102c94403203540c3e80d00e0305000d0030030083c41c2091502500f004040c0c580d49442c06a0300c194030944017140000c0c2007034001042c1c4003e4401118a61200440031808030780b500154040c104854079040072000d000160747c00c2c400c0710340340f200e5103500e00100d41040c0464011590510403002a802000341e0b503144402c02c40410308196028000700540000b14170750342009030081c00c0303140001e07101500e844c0c000d440c00e929050003200c40d00145002c2e00c050060541e07040c0240c10740d11000f16805410201769813910301d075070460381600070011f0750703604452010407810340c00180003040d04442040c01079a1008070919248070032582240b042c194000d1903140c03031003184011101c4507a40d5074103900313003020b001c0c802c0300810341244 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 48862261 1250 48861011 48861013
    0xe0906010e0d29010303091a07151a0a0f061407021c0308091c05030402030705030f030717040311061602040507050406120b090a0906090501050708090d0e0f12 70
    0x19151074907280d81d90422280c41c8200d07a01c00d400341d4410b401c01c10703c01042110406044445004101003588070804800f83c8000e1010840000c150304020b00300c511440f94002d0840c0b0424a104a03059941d40c01404c0121254400c1004070070000200f020701001c1b03001780030380000d0f081000d2102c1c41c410b01c1d040d191840e9040f03070345252523742c0c1c00140784969044c1d5086942d04982d0000c9041503800021140c00612400c010034018040915041c071001d00385201c00c007040340100010b002d6683c2081004001d01000d81507900384150f03035000e107031a90b220304810303a01d1000d401034402070056280708881c101c079040020007440c3c01803c4200030150340023001085400da0f1000ba20000369989204042c05414551141661241380c60005010090404940350b03500789401444012a02c0e5410610b1303112881d400001406180351401c80b004255080303000d0701562803d001c1162594220701c1c0c1c40d015103195002c891a00b12000003c030b074081d40c01c000c0f02d500314460310708162442c1401c90790341407802c0f00d1034 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 48863511 1250 48862261 48862277
    0x50702040612080a090602011802010e010e120606030f071a09060d061d090c090103121202030109020702010917070302040908160312060f03020616050114090f011406010e090601 78
    0x6201501d84500c140b000d035501c2e08000b50080d4000d800810820052409000030320401d00c42052600d01d82841c2c01029041c001d880311106441c0e8446c036140701490000030404515030310140c01c426034840e4125025400307440745003450700d401400014840d046840c04010040709040720a290500bc2d00700004554200380b09102104040c2902d000c0e0001038640c203a40040ba1511068079034009400c00780807a58150011015200180c80e1104c40f6410760360854500500840301c0e40e000c8400786660200a80c860b0b1020001080802850b001414154001d0b620303001031585401d0300ca001d030440ca802c00c0c076059008500c1040113003410341040c828a4081c0c40200c0c10710f07410914085002400c0e00782240015240b00161a01d0789103886820081c010340700c03414a400d400e41e408a800741c419150041c040303011072241c0200304038003500400342101c800303011120710741000a411592420300b200051100c4d400d011407860304014081e045442064160344120b282c114200030700c500190003410160400c4070038 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 48864761 1250 48863511 48863519
    0xe01020405030d021501091a0906030c030102070f02031005090303011401090f0603140f090a080705030c010908040f060806010c0303092607051504121b05060a091509080a0507020406 80
    0x18006003e111500d0703005070000c1e260900c0c484242540580101e5081845d003030a01c1c0a99440f0500e0074400300003070f5020105610b40000103032a1100700d90110361305600020b603043c1003024110000c03400c00d100360102d030001c1c80401c5000040c0c40e800c0390f034080781307510620042181c40da02c0103022880d048107040641c1c4880d11403010b0411074400ba041000488c0d161601c020102e80130107001a4001c1e0940020710481c1041d01e40151111504e000c090321564010070b02201780081401151006280351008200325045447e000f20244c03c14464001340b600da914000030814016410036100f0039050351070700c00d5100b0513175041d4001c080b1001d041c0d9a450190f40000b540b8040700d9402120090b24031f000580300c00540c5015490048806010071141c4c1c020310500c8001002d250915150b510305041c184a50818030300f0a64440703400f80301c0038080b40308030018400002c51552105401c0390088100110550006a004050f1000000001c5c881c10040011040d020b100b400904a0144020720110302c569032 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 48866011 1250 48864761 48864763
    0x30203010c091e050303090f1206011203080f0105031203040f0501050709090e070e070305090a06060b0304110102010c0210020a120908040603060f03030819090803090d1404030203030304060e0102040503 89
    0x50300d001d404201c100c1c1c81848162200b420080e42c1c4032540c440c1011040c10540869180c1c020380d007402d401040900d8800c1c0c02503942c040700e00c500300c0b941001c4032a20340e55002828211890a0000c0c0d005c02c001c42c01003103060045d0208181030b42d0b400380040519010140d841401130307000131310540380c1601d4000c0780700000b0300a00955001c0c0d2070320f81e282070482c7e0130034100900300c0d02c040070116040d44c00000d003042083e03d00e1441542c0500f4070300700000c5035078030003030500c3c141542548010703d02890301c00e0200d002c4003000090340c0118001d00c03075604507003058801a400c8500b412070f0440503a01c080c140c08a40311540e0002e05140302c4920b8544081900c0c5907051054409a810448510030042020b00410790706200d0040206800004c4269052454a010f030841d000500380403030480845810b060302d00a030b50440100e40d42d1060455541c0e00d0b203c4030741611a21004034560014841c030301540c89040011007a03a080c0c3c0d030001c0145143d52619501d40c00101412010400c07203540078040080c05030f41c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 48867261 1250 48866011 48866021
    0x30a0902190f05030d0e041104051207030c0b0f09040903020f0a030c060e03030601081f03080a0503090607050427090b1014030105010b0901110c04020309030705100e0c100903020301 80
    0x6034a2035540e40c01802c2c180e00080c240074581245000360300c0550081e00a0740c1c800100c621081096074001080070112240050031b1182e6001640c001032001510b2400c0c03a4009003000440380100b010f2550951940441305c1c0501c5105100d540503441403100e100c603403400390300216109200f801200c0c045079046003e0360902d040b030201540412a0340011209001c1c1901030304c0300b04c1a50002562a5241410007e4278001001d460f070708034465a01c824403c07030000ea040c81c0003d1034202e01c4103900c0d5008810002c115034000c581c0c000c018091640072030b0040303028000361825503521002500781458541c6a004420a410303061443d400d4540c100e00700407500f8000702e02d00410004040960f40c4e4200140c000a01c103a10549500984c942401049140c0c80002941c40110302440c08411404940035110301e82924002c0c0c241e0b10520020612011000006c002c200c140e20541c1a0741500c115101d000045602101440c280341c1c10007284000b051400040682e0001440d00b48070040d10b4403900030a013160303 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 48868511 1250 48867261 48867289
    0xe0d05040602010b06130618090f0603060e1204170102040e1509010e091011090907021006090b090a090c0e04060603170712050d0b030a050109030806061e030a0902 72
    0x8000180034003a10342d0a02628080103402c1e1440b500e0321002e00c00c543d180503060710030700007000404504861030f055200034542c020000d68a0500111a2462002c001860f551104685903450710850030301c06000416200c1004031217000c0d181c14140b6081d0107008105602228000c0c0355802c02010504500c8140541d02881d401c10844001c24145000e102c00ca2078180c001090310104101001481c100004110f41d0003c00400c011807070888002044109010b42104150300c000400c2c20000d14075070005910a4130380304480148a2290754500d408121809103140540242d03070b80e40041c40418032034000340200c40c80b0f910013410349a075400c2900d0700b840058404880c40d1307031189810010300c48150301c0d540da002c00a0a006180401076071f14018400702c1528020240507010980e950440c256900c99081075101805a4007401900d2a0007402001002d030304401140d5000045000c0382054000d46248100d00c02501c1c000d901c0d4180443c0709504010071110803640c5590f0440010f07103444a984980c1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 48869761 1250 48868511 48868517
    0x2030a060902091003050309060a0302070f030f02060c0a0c140705030a08090a06080f0a05060103110d0501091a03070e0903040b041202010e010e0612060303070501110d0b100804030f030e0d 83
    0x1c00e02a2040188500000d0440ba40314150710700140b002c60004011104140300840d0303200d035100c1e51200d00350064000c07158050810003000e90200103041e0010440f000220903076090f140c51f03a5821640b01c500340540f01e03464002035070060722600000c0000e2040c0304040780081c21507068503507880c0080c0c03501403190000c4820751000304070901641001e61502000c0d2039141080c41161030700404c85c1a410400801c5003000540350000300350719034001d43c4102108043c2c00142942d43e4988000d05000c0d0400b807241400045c070340b004a1112440d100c1d1904140d0070700078040c2001c7c40ca4070181000e040f10151401c501c5000400001803030280c03c0009100900300101070030701b03840082c00050316030019002220b060000c030040368251659004115017140aa107050083e00e611048042842c500825000911541c43d004c0008103500f540c0b800741881140c100304c01d0060b00108010300500c0701103015440c02003043c28011030000781c06840503c0008115243c0010ba00701c103125141d1030700c000d815949000c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 48871011 1250 48869761 48869771
    0x10804021f0504030c0b0702100e1203040b130801060605121f140102060604050f0a020708210103050d0903120531090b01030e03090108070c0501060305070e070f1e030902030a06 78
    0x10040c4a9150000428850090504042c101e4009c00c0c131416000115a0410402e8850031150381d4581094503405540081265101c1c1d80354203240c3c44035448045201c841328400071002440260501940c4188c510503a82e482c108120200082c005902c09003203400c800c0c00e22502441c01601024490004101c4015031060b102401ea0019003040304c042e080b85d020307034102000c204010b0000680950058050500141e440e1054103100c01d8900409a054103d001b000b070000070038620440b50281030703078042c80545241d02c5048a040c1c40c100080d21000b0041510b8200071400c46014101801c10400c0301d40c540034010f64030400101c2d414011150700420007046203c1404035215a101c1c4000b041d400b030070300700135181089500c2d03503580c09440507007410000d40400148030340d0702c90303100c803044643c0c885c0c000d0000c0e039100e140c45500c800c03280c0200d5001103c040c000440c10b0340314100c01c0407540020f88801b025595a1201602d10f80c05402c0540c0506031129014801078038200806c01c40240507040c0012 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 48872261 1250 48871011 48871013
    0x1802031e06060d1a131a01050d020409140405010b100c02040b010e130903020d0504030213090201020a08070501020405031002250c050d05010b040e0a0201120c181d060405090c010804021f050403 85
    0x314a94401d0380b40320444d490842002003004200058900b10002402c24a8451074003400303001c0032f8407480c2c108620140c2001e114802244000b404140120312030310007400600030705c0f02070042d440440344007200040c100d1110800541082e91040c20103d4042c9403070400481c1c4079020030701203006040300151241c0e480c41107205242e03041c0482000004e0030300d04545010b145400103103191500c0001d400020b42d99056480031a0b000300200840f29074032027411600c80c601400d055000390464071a0900034020742143e110000514403c03203000200e1540e10801c11030408010501ea0800e540c8120345030110500c1c041059a00c3c60a9407006c030f4401c0c000030503108040000c1c441070300d25091000f2065805000c0040c0140c0e000b40ca00020b05411070701c002401c1c81c508404840d00c284a5440030034020081c8004030302c501006a094565040382750064840391607038424441151411a89001d05070010028a486503120701000d40d0003500003440010484000e914148103c0c034030032450404034100083c104 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 48873511 1250 48872261 48872269
    0x706090b0906011707030b0a060e0123010509010504140a03020402030a02040503011103010608160315060806090601171303050d020408010506030723100302070f0b011802031e06060d1a 81
    0x43c0940130b110700c6003801080910f400c0d0354564807400014000f01d44040000c40040d030603404400144808041080355595400e112a1401c240c00081c0e2000030f0030983d8251194060303022a01581010395600c9c1c5000d10b0140d075004808010310085078072081460000015907110300195000d0201028010382d0b480c80c0c6010542107900b0454498115181840100152038000070a99402588849120394450030b100c812401003480310360003015800443e80c040749103a801400148221000d0310701003490f41b5804015a10001e606c0c2d1025051003500002490f0250712204004c1c404d0300c82d0500b1420b1107092000031003643c020b50081482d582d514001c0040e5443c041000c0b4000308105d809400103480000e20b106030022030b96040c0c4d4011243c84e000036030f0244c400d6049880868210440100e030070aa4541146e000400780304420340d00e10f02c401c8001d41041c807442183d001e9580251140c41d07444407a00c07143e0080c1c400608030356004005021000c054441c0b400b9003031403812500d5604256038807910400c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 48874761 1250 48873511 48873523
    0x60510060201090203031b1f061401020c0a06050901020a0213050603240703151805010510031112041a0901091509050a03080603011506080a0b06070302030406140706090b09 76
    0xe9045a041080b00340158030080220385401207143c08810b4007940103022140303010a10410582c10b14040c200444072490503600c8030040d24000250328640094002c0120b036510086260b0a91021104e402044128016001000141010f0041c2c8a0010032600000d00712901d0111607140c0030348034420004a0728040c41807a076130101c902501411610100c1e00d040b002100180a90181566a4000307590301c00b0740d00315030008102110080084083c0744030082c015160a00c078403409501c03410000705c5418003d0140c00c101215004455041c28003200b0a4509484090415950022408001708554108042043c1305840c0b050003c40c08044510f404a541c00102d04012002450599668002080483c06c0c4400070380529107001d49413a0b0303000080c014132180098080c00c0d4012200001c0e04c5400c0903e02e403141c400b07000104030b10070403182445000d1050b000020300603001040144042c42c003d001c0122090b008001d868100260f0340c0d80c9108403007488a00381c5d00007842004021447c00d007045030b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 48876011 1250 48874761 48874769
    0x30403050f0705180a020306060d09080702011404081218031207031202070c06083d0806010e0c03040629130b0105181224010602120409110702030109060510 69
    0xc00b00c8481c01304180002c09a901902e0400f0317061700017010a410b0307500c50060300c19845218104001c242070529000116920100049000c28040c080c0d03440f060244405031811540040b001d0442a01140b020f9001d070307070140f60110700724428603942d10a90745040200c2c0030f00d40c2c10b01400c15901c1e0664213002d01744040f248030341d9400d50300421180700007491f8001e26400f101c8181c02c040307810b52500d2640b00200d084440d4110110b009002142c011000a00703072030030340038418510008084e07132501c4400340c48801c2400750792840110381020441c0c21102000031a4040d0060b0b0000841c07202c080030501184e0000308041c4070041800d0007140f40340c07524124030100380e210890200000e90030100007a00034050481c4905003006002c12010a548483c1d4074100a50700200544503161a80c3c4245010f114010b107004442802d200c001149490000500142c60600c0008884c1032a1400c10048007824144140011070311003402a040103841c240114055144200c802181501e0800c1d00c18902c0103150344 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 48877261 1250 48876011 48876019
    0x20403050f010b030709050601211b030e030405010c05030706090510110a080c0d06030c030515130b010b0702010903120c0302010b01050403020109030f021203030906060a14010f030c0e03030403050f0705 89
    0x242c3d840300c0d03500044034001c841c595800030a5079a62000182c50160404051640c50000c07044003000d503464650106510440c10a606246003000d11000c60880d151b0961f8183c10307a01c200300c01e000c80e40c000e0a8003150b0500c2201100d01d08241c5542700000c0d9880360b1422290307907000d0a601c0d04441d1460049803010030034800401d00f01060058000c05c1d1910141c03400c0e0521a0000c1c2c0310807948138680086000c1d54210706200c581c150380e440c000d81c6c3c2d0082d03c0d50200660010303801054681c1007130f4800420b00c5400c01c03032660303081e4207056002d07000d903200c081c0c2241402008840040000c400440351050100309448011400b1024240a429076080c041c81c941082420802440181e8110401800b9250000d45040c0c1030701c0140b011039800c0304c480515a01074032011003000401c0600044c800d100e0103080d5403075082107543d4a00010464040c0b02440d020a104400c0100220720175400300d90200c21901d030640004e00200b0101e803c0d0b50054000b03661a40084010003190310f010480c240041c28159 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 48878511 1250 48877261 48877271
    0x2070609050f060601200a03030f0b0a060e030c0d0210050c010f061212020607091403030d020f03010311030d090b0a02160612110307020304120c030204061212080402011407021503010603020403050f01 88
    0x1031a1587c461b616840000c0c00d00da9991110301c4400b030746500086e05160041c0040198a88900e00903003400174070940140b00b031055078010405400c0078441c1658503940503160b000c0c201180c0c0c4003900c02c0d03009158500880c3d0351340c59a10440040e18061203004103941e01d0400302c4051241422038110f00c10034008820340d440308040c441c4140d4003004140488481c45075480c041a20a0f000030300b94030541042d075a10900124881800703110724030040d4102c0b80301d0300d45441c041c1400b1081c9a10b40e021280a000400e0765041e00300b101811000040400e84c0051040d600311400c0045031108215141c0c10050004400003e000f6280303115100b440c00c0c6440362a586411480d104c2e0009580b44218041c2c50fa0010307000c103e0740104000e00190001444e8001c200340b01598a07000d00ba0710900c2d80c81c2055403515001c815000b1014083d0310954091501079503030031003070408101044480d0f03111120498000c0c0b000c10701c80350a200a400507501034000c50f0307030240c1e4962850410a00d010000305c920540c6034504 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 48879761 1250 48878511 48878567
    0xe0601020f0c09060d11030f06180106150305070e09010b0a0f09030c0302060702010504030b090a1505091b03070305011a0307080708150a0b0910090609020906070602070609050f060601 81
    0x310326051344600102c5800300c5910492500a0503030388040c0d01c5582500c81c4483c03000d90303548080342d018070440c00c20504d0340e43c60070710040329402e0b284144221042d4400b07401c0d00d4103069109802082e800381c0386041c040040c080407000318044103030903840710307521402c0421004c64043e40800243d00108482c139260750b140d41503448030400d20030144002482040005680021a4003d4087c0c0c2c0041d40c0121a520b414942007410548030748010400704d8040d009030300c14003130080e040e200c2d00e40115115802002450040c20407d41140b01041c0316990500c18860000005102405500c0640c030070841010f19442e20481450300d011000e0b041480a034110174014003083e0000184040950741e4643c4804c04d0351100400231001b4144a403405030090764200404c03c810700c255080c0011130b101d2417000c010266032484a0000c90203201c00c40c0742e20039001c000380c0002c110310342c010b0030f03456003c1d44000500745495a00c0e03601d000c42b441c0c9400c0064210000f0403182d982c02616595080d41c407007040d500301c8419 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 48881011 1250 48879761 48879769
    0x1203060503061909080703090e01120b0a050601020111300103120302030402011701121203020c030f09030c042c06010302010f0c03021501080f070909020102030f0d150e0601020f0c 79
    0x4000c09020b1103100c60341c1c8030228100142c1000101542005c9a40e03601c05090500034100c0501d8011134041030101c60000079601c48000e452021240c000c080400300780c54030f1505002401019042504564a40b9200c1d10f0444202d4001c0c5007502103200c01800c524044001c0384400340900440325014a10100104041a914105111002e0123860016500c2e5075910050b00d89c9000184002c0c4a07040c14400800d0416855041c01d074598064008410004020102241030b40f00700b45442070560810301c086804403c814018080524008090f0b0391840020720108048032109201044000d45042c80d0041c0340d84955207844d40c4440030f070043d056560450b000030302580e800d03080400400c90106e03952810b03d071090100400c1407040b9004101c055949100070390303480c2558451260b1340c0c016400c00082090746445200c84165042c0c02031410507080c00910150394002c03541c050078003a155186141d154484040000141404d54661003550038101c000a01d0100801c2181c18254029140400c480e51 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 48882261 1250 48881011 48881023
    0x115060c080a0c0c1d061002120a050706020a030501030c06020102091008061903030206060414040c05120313060201200a090b0c0708030d0606030e070e010b091f0801031203060503 79
    0x2401001150b515510741104992034040c1c41c0d405018030705482d5020452009000002442288114152000361608010400420401901c00c0c001d0703440030a000205600e148050a1605030341c3c1040c508009094843c4004c0c1d91045041400295076080103004125180300381c40003400561000314240107002003c21001004019442c00340880c84c00001c9179941c0b65003021f410152803c0d584c4405956031726002e5030324102035507103078400e604002c1e15041001c80207880d148a65080031a01c8441031610041c00310141c26041d076400b407800108a2400c0d40ca00042a51005000f00c1d40000303a00084911070038030102c1071500030701c0c45120800c000c2d13070b01c00c0c0d00c17000384003d544a01d00d0b21035a417014481e102d4a80801030b800f15405010204403080d10070380d030f680003100301c64403514107200700481040803c1e2605c4503030054120340780210300107010280c2900c01500d80440c0260000c0c0e01c8070f1408600c40190800d485181c070015075030341c0c0107104101410301d10140c0711407281005e01100d400c0500081d100c003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 48883511 1250 48882261 48882263
    0x91f050402090409060906050403030609090c050d0302071208030f0a02030105010203181207180f020705100e0c091f080613060f020f1204060e06060906090907030209010f0501020115060c 82
    0x98011800c0c081c2c60b6516400030000070791081c1c0c1040482c10a01d00312016040445095000c00e00d400e00004859600f4050313a103030b840c0d00040c04242c8500b090100003a81c07800d918140e003144107441c0c0114031801d00510307025006000b400140d441c1e01c9d012400080a10008120b00342d101e0060004000f6a47c0000544040300c40176056104200c1410012038100747d1100005101480745800000344600180030094841003501d000340311070207002c4404003c0c0c2c0314904005209901408c0d00c02844ca40d00d03030003014010890000e80300140340c203e000845c030041c1a90b06014030540441841000f03606c0032a0300d8010b22a19018017a03c0c600341c10341d06000e1403042c00203441036486800c0042102965170480d0024241c50491329168042c0e0410080900340485048030310600d018203d0955420004010340300302002002c001c0780d5070340c1d9001e1064100c4003800507813042c03041080101c01a038a08401a01a2041c50380c0d104415140c030000a09485046800309202410804280300031a800b0303454000346 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 48884761 1250 48883511 48883519
    0x6040e0f04050a0c150e0406060e01140403060906050702010b010c0203100c0504090c05070201170c03060d080c0a030806040b12070b030c070c030501020a031a0f010809010e03031302091f05 83
    0x2079480341000303428000a4440205640701d60100407a901da200101150910b41c4e6688003464600c100d000d0100312440ba000c0d10010403954450030415610401c02803600001d01012030307003002d80d203586036000d466840e0b604130740d9940c0b540c0801c444582c3c24403506c0000e070400d2030031560120300c90b004a600c40c00c4908042c605c11303031100038140c81c06010310200c070000c10701c0d100c0c100146951007500800c1e94002c850100d0014003540c01101ca0301c2d1400d90258000d03207441100703031704c1c43e02c0d007008102e095020351008036001c0380203100c00300030100240a4051043e0081e2280c094070300d0502c0400040f1804158414410502c03103844542c40000000e64500781d485116040da540c2d180d14040c60b0307050003005401041c1c0c01c20003001100300401074014090351006601d040c0b2140110800d2001103000203e00650450b080c55110b825942c401d00411740c0083c0584000a046500000340d43c0c1180c0c4100c0750b20485c01c1083c2c080e1011400c00c40800b41e841a450360b980c1e1a808044d0031403000e4040203200380351003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 48886011 1250 48884761 48884791
    0x106080a0209030a0c030539120610051f02060408030703140c0d0b0604050607150b060708180f030601030b040215190201110901210612030207031106040e 68
    0x4015a0341c100c50000030010221030404009260401040c6103d002c111180e000302c405082c00440c001c0c6c00080902e80c100004600c400340c80301040d030303041001d1711402c0d030002904c515290449001c3c81020f00420080c51403150b40c505200a10650100c1440041d95007071041100240c00c6a0105a8a42055005002c240d9907207401c0000c601500000e10702c0c4801007611024400c0e48032408006040c035598021003402000a09820001c0e50701551096a0f003101c41041202c002603504900140c0300200715600050945800c1e0204070f107904044070032120300400040b0a8405684000303081c142d404100c1d000a00c82c07501402007510b401040c4002000500300b90b010800315512a8094086034034004030b080c2d00d0703040c1e2840c1440400b05090080e00907518000d220301e94848154200c5050180603155964101411020740c0c410300c44540c00c8900b4580d030340f0700c04a40031b2811003a9141c01c0c4e003e0f0380202003186c207500b0003640e11400035a00c98810380040204001c907100041100c1c0e070201061a5100f1 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 48887261 1250 48886011 48886021
    0x50405090a0b030d02030a0801090b010504050405041b06030e070504050103080412050a02030102070b010509100602031c09050f06100b1801050a05070b090d02070e01080c0409150f140a14010608 85
    0x40980329848030075600d805090103c060980d0700102608280e47e144d5114881d50342d0302c010304011070f05094034403400100200300a2047d030906400a40d00507201d802d0840140c016207900c148041c40e40c1d040100000d44641c0c01c0385e072851040210380c2c00342404a9081015500d50350f40c1e40d900d80700c0e0748107042600d01c00343d80c1d46007401003c1c0108000d0345e0700907000350758601071461301e00400f1809000c0c03140318601000100705550340c0f0840900666000d5001540303024051142e5002c0140c44414802a03c3c0d15030043d8000500180034078444202c2c3c41004000300c0c10088003012180246801c00560640c0900c9106100200b84000d034002d080b0a00b0000c0c0d40f545002c900721614800c024016001240e804140074888a00003005c2c4801e0040361b095580c0640c81c0c1159039400c500c28800e101ea81d902440d0300b03000c1031a05a0028104500c101c0402da0200e8088140c001940d103009015a00c15a4402e10320341c02104000c14554882d4080b98100041301070090f4440c004031040c09110204565400016 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 48888511 1250 48887261 48887281
    0x4141507060204030b0406050c0705060a05150d080403050c06030c0702061c050411030106120203060a15030506040507080d0c02030604060507090506040308091921080d0f0213060207050105040509 86
    0x120265045107040d96125202d003443c090581d82503408844461400b4009080e0060748002e644582c2c0e80700015051946810326160040c00340580115a1003240c071020100d1340c1d0f00c1c01002c482c0184551403c40d02c1c0e600d0360802c0c40c2010102003905024100130400c029004c1c412904644481d64101c075455240d6024034622207520030b200300140d04540ca0b110611007401070b070210813200e480b0110028050b05894103132030b100d01c202e545002901688203201040c07070482c8540045040c031070b4190200704e00b90360340c0d100d05151041c160b8041d24982c02802e030a2002007011310003070080c02207a081440c40380c10580c0c00b01e551580000c101901e10750f915008038842e188500312400c02440c0061040e9210380d12400c1030401540000e0506118241c8145044002034404280104880c2c2c201c1040409903410014611282c40742c41c400c0700c4e00601040f01103a01000b52050345046d01c038080c4016114144140e040c1c209103060740080040d5403100c0020001aa80b1804450a07241e003614480140d0721929200c0c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 48889761 1250 48888511 48888517
    0x409050903040e0a20090a18090206070c030605090c010807081b04060201060603270201110c2106060d150c05040b0a0c0b0114031e0307050706050a14041415 69
    0x843d4080e01e9201842114411a0003d488044d07907610400080e941d0070404000c14443c52442907004000703034034204400d0141c011028088030081001017042000d0354002041640450300448003a001c480040c014440144215076214842c940185100602c0e50000303042000e0082c14082005040c5001031001e03001e1040000f1484000c240150301d40b51105c2c0c2c0a8040c0c510b900030310380041e02c2c0003030780c1e0f4114a20704510281c0100c20102c81070344e100e042e0011600582542050300c03052080d06e2424059480c3c180e40b040303565035040389281108103429891402c00c200070b0483ca01c26208000724001149242c0e640850850140700c0c00141307190000c41c143c440d400390303030301000000c2000f082c8001e0382c9030800c00000340244107810280782687c8400303500104005091520760550300c03022030030007142035a092144511900e4030407641004280e568080c5800c51030340090002a9000c142d0000703164100c415464190790340040b00d42086d0500f8484208038801d03040452260643d00c0c040304070742c542c1e4811 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 48891011 1250 48889761 48889769
    0x501020a111f1e0315060f021504150501051228240c05041a070602040302040e0c0f100e0d03050f0d060f05010512040f0c080f060f0912040905090304 66
    0x8102e29201c00006000800030080c0e001501c0c1400c00d220420510a104001ea0900d03456444100541000c030116140b41c0c10001a200358451003c02d816500082d209840c86544200038100501101c002c071001a1030707060740701c140a83d0701180100c04503100071400811039038410b00a038143c50200005e6605043e0402c001404d1502c1c0c541840d00385d1583c40060b140380d99000b00091000c4030100318115503a00c80c41c4130380809040d60410148410b0091070003030814901420003d030801e40c0f0394002804480001c406c09000d44d100e9400000b46052800c2c00c605040380842d81d00d890340307000c0300024007440411405180302e12522002e0705e0405010710141c03804000c0a142ca9500d80042d241e03004e00510560041000241c0ca214000039650b120744111807ca40024180600c01d84950782c0c0d075040c847c1003c10850317054008402c08601d02808200034051114000700800543c14151036a504603c4060010402c60300807110215070b004c1910116011260603050019031692529009070450043d500 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 48892261 1250 48891011 48891049
    0xc060504051f020d050108070302010807030b01021c11010f200f0712170a050106050d0509070302040e010c120209060306010809071a1c1a01050a020f060106030509070905010501020a11 81
    0x2e5194001c24164064840312880070700400003030741c96410040d660000d6201c02170024048100082e2603901c00e410200d801c07001030040300d456042ca91301982c2c400710100446d0000501d80c2c1001c0040e14024040d8095039000c060013040401c540d0403024480d8044040e5649030200c0000301082c0c8140c6e824100c510051700003070445a903d080d02d50080c5905518803a0080740c41300f08011843c1e66aa031700ca942d049588c0c2f600d4441c0f810180841d00006408014070305c661500440c036000025807142e001e0840121000300001400d1541241c000d0440300f140300607001c0d4144180000503992703d40004481c2c00ca2404d00300401c445c1c1d60001030034907005490704949045030031560b04d008810f614070080c149040c21400c450160003011a0b100003265041c04000b07a040d150a0840c0d8041e5010b4401441070b031902e48103907462002088086ca01d0135a081c7e00000020fa660410040e4484045c000c030310250a4400c1c0c18441545030000007540d80ca0400005030500801e0003405109a40380da0880b01c102102c00 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 48893511 1250 48892261 48892303
    0x14030a0203040b07080c04060305041401050a0516090510052b0903030b0907081602070e010e0907050105070b06040f020c0d031506020106030515040602121303030605060304030c06050405 82
    0x512000060340003540c0468150704001c1c041180107010b80c1c01c562240c000f41c000d45007000c0c42d1807000c0380903000180042d104101c180140002c020002e0054078407d2144010114070742c286220031125080c14003100c0e00070003070440003d010b00d9980b8035500071a03007664903000380c41d4007400c05585510b43c42e901003c0b00c0016010072086d001340c0e843e0488102a030090720200984001c000c00d2080b51007003181e02c040041c213a40d0000726038081950000c0700c00f580a02c11140815202c040f407510502080c1c001041d84030321001002101c034030030440000500740a1070410b0401481e5a01c461650502800e200d10454840e2680103d0344850b5060740d021106c91400c0f0b443d00b070845a0040c0042036030700321002c21200e54020100d4600e0050040c04112684440202048001401041000013010708105c40a940802c03040c2d0122030f000c065680606c100780c1e00c610160310286000b0b8101c8515902041c082c50b014010000401d41002020b0020303a007090006c100d60750303585800c80c10040380042018519041e5 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 48894761 1250 48893511 48893521
    0x211b0c06070506011401050306090a05040809031506090703091e03030f050c0711031b060f04050901060207080d0305012709080301170c0406080a02010f0c020303030123010804020a0b09011403 84
    0x35414100c5e91060003da030b6040312003004441c0c2d44021910242c00003495404030f0030200040e032105070301c10f004864560921400400290410490111101c1c0940c400c60500c40c040c58000e0f0841d07001700700c6050402482ca81c2e659480503101104494119080b40d170851001414041c1e04108825090361500300204d01c3c042c00003411540000105980f84650380540c8100f508001072008401c840e00e0341040d103603590300030070840b841d0700410400145450900c00055203803074074aa03130740c003800359074020b0300d015400c20540e5490465000043c0f400c1504000c01086642c0f0020308010904080d9103414070554240c10f2000c5c0948901c02e002440e0f140c000000007550140400b54103110b00702181520308001020040000782c806e680a40700180d080004010300542c003e04e5480d244150311f0420302e42d500c1180e00040d040d0f41090b40074081120700940021105c0b24841070799016101c090901c080141466004504e00040e54021101c2000d000a443e10440e0700892201d2120002e00444951701c0c640 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 48896011 1250 48894761 48894763
    0x13170408070b03250e0f06070212010b120105070e010e121501051212090103020903280b090d08010524030c1b031804180503070c0305211b0c060705 65
    0x100c5000000300810380c00c82080515044400074029000e036170b000381d4800000100034014a0466030b01d54850310030040e0b900103885040481811000d50b41c00012088101410b010031100ca504401d85aa407411040084c070b550011120700c4071002c01e1078480410700050011400d030b40601d0704240c40512034140c000406c40102c41c05035040c0c0310140e442e40c4030480c1c003003625503448101114030602c1c440180725081c01948242e0140c030280100404848981180c08019030f040d01c4022118002c03400b01009280901c039584065a4204411000402c0d0310050400020412941130145520601295401014001c0000e9940000c1e10100141e1a540e06001103540840d0b8403201c0c00c20038070341c860742c102c0b0700642c1c010058a04841d08480000191b10688040000508100e240706100000006007000800d0040000c0c000c2c2178460158404203604506005140480505011110358a410208020b0100f0700c403d40b1030446c40317001c03100a5607034200c04d028203014100d05150740018021034000e0078804 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 48897261 1250 48896011 48896017
    0x1302031003150e03090609040b1309030305060a0302030d080a0204170703050708030301081e1c120506031c030b030a020d12030507020307080a08040c0b0f1803030313170408070b 78
    0xc81000105206854524980240c800f80302e01000d09800030700080c029405c2041c010600301704028030006000100030002410254103040e601083e03556411f41000b010341612889420400c101d070b90418003440c41d070002e5130300c441082409080047e40008542d00d415030b41c05a6000d0015544111514a21108107035607440c1d85200c107642903c5410300024200c6000704c00c86c0c1c103807070201c0054820307250781c01455039000099002101041c03240c25801d1001018240140d54030b03c960380d8401c0b110320a240380742c5050710006440240700e070b00a0006861112000d110004810f00141400305003c200c1c00700281c14030900c0c8001079040802c096010042080460b14003011800c503880422013510307071300c1c4100d07030b00c0c01459002441014200290400076024490007030744148620303000c0c4d940649412002400760004006116940c80100b2880c84208411a0340c5d00c42c01400d50046086181c607020030628071100000180100c0000340c1e62610140007101220003030103129041361030b030075034503941c605241e4 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 48898511 1250 48897261 48897263
    0x170106030b01021e3003070e030c090c0307030e0c0d050d1803050613110406060e030c040203040206070803060d0501050f070f02060708070f020102070f0b090c06040b07030804021302031003 83
    0x13006140c40d0344240d01120010f80c0070b0409483c01400c049030507801d08400340b030020300300c1200e0f00703082c21046100c01030010007144600d035240c0e02c8a01c81304030a800d0614264a2a8045125000034020005601002c0040c2c1c0d034407140b00d2402252644204500c07904004c0d1200304150880000d004960a2140004450841a01c0359170746c40011314030034070128180d1170780d07000040140e0060070100740c00d40340b0044009113541c01000500c030b0280e1582d00007412a0499840100807a0a05180e00c0302441c0c2130100c074500d100161020b41c03843c5080e50005049104010f0000c0110002101282d0035032201e1500300d000380e80c020000c00c520300705840b10021505c002ca41c02400a00d0302e0b0b0b80ea5906510120720310303015078030b15107030b4140584138150241e85e154190200101199400c1c0302e10300c04141e0200604c48042e00440c0702c0c0e10281070201c02603040a10600740070340200d900300010403c003048403080301c8a554140c64004515100d610004036074110b0a007061000340e0003c414021401c895117400d030b00305d03 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 48899761 1250 48898511 48898513
    0x418050703060203181c080a14040c0303080c1305130e06040b04060b0a030312200a09030b070207030503040b0913050414060919020d150c17060315040204020a170106030b0102 77
    0x421741e0154043e0b44141d4040d00c08031104482a01d55515802404c40d1500001c0d0b491010940b01d6140c4840c1c40c890340200d90596080ea0140400c00902d50810955600200030100080c6044c0e5004600e9441159500c02d1500900e60404030881c10078540c4d001030f24040c0d0101c240c2d0300505040c10a52a481e20644068071100d10b400c2c02c1d8252482c000c40b265080f2640340d128120451601c014a100410103444034020000c1d03141c0a10841302c035024010034403220300703031501007a103405d5042c890f040c841e0007480e8006550040c0024400705400006a80480700140c5e1400c1d582c3e043e0b54085241c030314207050368814044c00c04040c002040180c0480c0c5c3c008030850307421641144c0c1d500003103d5943e048080c1000300b14000038580c1015050820510310388500034001860a400c0320980c403001ca070384031100d00c000a10241079003160f0300704c1c180751075400000450003000c11039500025844801c0024200920860f800076041510078001c020b600c50b91611191021150b6030741c1c56014006e0f260305c801280c01 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 48901011 1250 48899761 48899791
    0x7020601090c0804030c020402070c080303160801050906010c0215040b0a1110050f0a2003041b08030405060406030203090a02040f060f0f08030307050703201c050c06060418050703060203 82
    0x190b6128900140c03003141c05595401c032886103502480001d5014400c2a900681c003800c0124407202c080000314001c4161081d981801c000d0090020100f440603003140f8440c00d65202800002c0ea4041e2501e1509c50701121243d413405103001d0109080d00c03481c0d20883d2503c8000c504c0305a01703030f00001810003080c940801c0e52845200117808e6011075078211482e048103c40c48010900841c0c040d03000001c0030b16140a1644817004010044060740c0089400301c80c2c0d5016031054024801e51500e098005240c00001103040904200005003a80150b001c0c01c401c1550200000d00b400380c04201003060359802410810002c40c1000050b00030b03040c01d01a81c0c02e0f46000b80e41c001062010b03c0101130440d61028007450458881c400100c40c1507208000079400c0090700741d100c20b074640d150a81d6020509420004000d07004621213510780e144040c0502c902809001d0169441e2170b00089141a4080000c503800518520340710501010481161005880c2c1e00c2a07040110410000d60b00a5001e03860440464003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 48902261 1250 48901011 48901031
    0x20f07110604270606030e0a1101030213090221010b070308060d0206120405061602070b03071808060a18030206042a030b1005060403020319020a0b07051c020f071205150702060109 79
    0xb1f0703890003c0820002d030b02440094010910301d203c654084401450003500d01802c040b02c514000800e6080882600e5000806c0c0d410302a01508813100d502d400205120b09616190100440d4094000003070140560100050f880d40d9171039081460090b8010841515840303080000c0d2007414040340c0480f02441405e004c9443c5841c00804940641800da00500f0003604050284205402c0580b850b001d200700b0f200e980d0680c80c0708040e96000740c14610000e0410345840100302e400e0b10800904000e07070844110064011036804545e03d68000c3c0c102e1000300a0880c1c0455880c075054400138610140d4084582c04420810103484840c016500501c0c041c2d10309443c6c0040202501c1117210088d419841510003400c82d030345481046840350700017461181110b0340d40d000c00c0d105d54890003044555810000d40c80d46280c0002c83c0320341c40030703001d44010a402e1140741c1d1429507a40c05800350185040080001c903082020030021400c40d00c030b6404c80020f15007480d14010359500801e0055005180c1041f44401e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 48903511 1250 48902261 48902267
    0x203010f0b0609060706060801180309050103060b07080c10022a06100e09030702040207080c100501050901120206070c030f0c0b0a1704030e0a030804050f04020f07110604270606 78
    0x241c400300010b000c1880e021070282002425402038604440f19a116200000c95000030b20903003000f640c06e400d91030301c03a80043c5802403001c3d0154020714113151408405000f802c0c9140c080e5035030340c2c0d4040946607031035282109940c500303a8a10300300341c2c0260000403c89460051910035444c00380a03481c0c5039040b060007807862a100d642c1290006e1006d00c2002d0100407000511588907049600c40d001d9a191a03090340100f0280e900040e01038a02c1c40001810000c004010000b071804030303003a80d200300301c1c55040c08000382c40354074180300d80710285000100703450655544404840140d603001d03c64000103a80d0b464081c0750079580810a41350241c00c0880000d40c018000100c0d14034000a650305442807101c00c90724509180b0190040e000c0005101c1d2504880d210400c0c21809140164289030b1035924001c10411440005100180154010701c0b440c803034a10082c0030303034500390390104040300f41b2000000490000d009030350026105940e0900d900710450b6180f03800b40c0c10a041d0402c1400b1440e10340d0401c0d = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 48904761 1250 48903511 48903521
    0x9050a08090a080625110312070e0603090a03080603150a06051203030c07032d2003040f1401110a0305040303260403181502010222060203040b03090703140105040203010f 75
    0xd103103202110380c1c076a00c0c00030304404451020f0660341484111102d00303a500b41d14540241c1c2300620705041860500652982281007105802812609540386280c01101c41d030311342c19401d10041c14011400d001c21650380d01480040d43ca8650030305805880c0c0341544520010b01038500c40c8502400e5101c0407044c4001c0b0201c00c581c41030320020740703091502c0d0580e034040380d808030050a400c501d00d98014507c85040e070404e11b802d00300070803235070760181e04183c0d000c8114044c0859004690640c0c8100b1003007040700100b03400311702145c0300c8400c0050511055001a1060a0500031020303d600503000c02d1010990014003510540b4001c0d5183c0e0032454180010340d038003142e0070182c0d0022089401c0044c00091040605460310304215036000c6996990f8548040006418209030000d40d4000c070300340100e4040420b00e100b108101e020f510400f10700d0722a02a40301d210f540a001020103001000942c1c1640c01c0080400a540c002c880b010001e14204265000b0201075800728480c0d4203020365000240c4540c010 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 48906011 1250 48904761 48904771
    0x1d0304031e02030102070215030405060c0a12051902040e01150c021806040f06090608061006080f09030405030706050406110c1509010c02040504031e1704020f0409050a08090a0806 79
    0x8a0801410020881400c8500c81e00c0803070341590200071590040c0c0b190a061101d01c000544280e459040911b4681d0800c44000c2c0410610f180921011f0b5030355501280d412818104480c001899885d44050641d400d40c05444600003a400004c4c0041c0c50f941a442c018100d608141ca92643c80d260a0301c110b50080f100000650b01c0030550300f6000000800140da40e4010b10014000070b80c080700f0015030340540f031036030b0b220b01c1d0707410782d01c0d01c2c100140c8405224090740000d1035050698180e04000f400b40400c5000350000e4980d0a001000444d0f0020800488001d403034010b044842e55640c4c0c41c4c00510319409030044a0004060a032407002c50701001a140c103280d0300091181c900303403012811200b41031300031640080c100420b070348103080942c0317451050034090740c00703980e4a00c089441032450401e405071001d07041d000c110700b514610b10007100115046400035030454416a02282080c00640641102d540c050403d000311100c2c00c040150000041c0010304061f1452404540c0d295000350b154102214 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 48907261 1250 48906011 48906023
    0xa05060f060a0b031e162709110403060204140a05041505040c1205010f05041b020606102601032904060e07081e070509010305030a030c02031c1d030403 67
    0x380502031498020059030f03119843c03051861105e04400c100c5801c10b501070b141c0b5a441018a081d02842c03d601c8441182420203441c04d460080180f0000e20000b080e01d4402c00c03521550f2041a01541812401110010f40d00480300750749171520307020000405000014460301c607000600c0005003604190240c4010726903001005aa11441d010501000d82401401c02e002c201078086080c500000034410365000c0c18801e1207988409003041c05010880e41c064400b928001400341c01c28402c5980007a1032544081c0940d01031007018030030034050310000b6040322007081100c1d60700210600080c101c103089040305e000385480c403240c0d030110080c9402c58140400105100900c03d000501260440c0c1018017580a0700c0104d41c145940d940080d42050452088019007010082c22140868410401c88005e01804c540040b078552440e0b1341e10b6035a22812422009254664441d09602802401500e4180410b5402d035406140b0120601c40101014081084404114100050303405000825501500d621a03 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 48908511 1250 48907261 48907279
    0x2030a1505031b280503010c03110d020a0203120103120905090c09010507080d02030907060e04020307050405010e012d02100605060915090612011502011b05070f0c080a05060f06 78
    0x402a52180c01c280c3c9800d4221628803c036920401c2e083c0c44050020486040011019081200301420b440250105400309030901145079044c2d00031a048518203052030a0050391180300e2134007a411170144890754000c0c02c0c0c060000006100ca0b800d00620f21442d2a41c0c1c0d02142030700e03081003280c6d482e03090365007100e00c071024810704002d5402070004141481c041d00d14541000a859200d0041e03074070440d00101c1d0358000110400c02c2c5900b003610500c40c9502110254110f2a00a100400501481c07007558100002c40d0401807040c4d0140161403034002c00e41d0091002184603c1c0c810051400020600c0700611a01c81c440c00b90b42186c4c03164030181d59004014500e80340c2a8810081040c07074141680c0c1030101c04010513900780e61120010043c40082c0d00c4242e03070703070761600f02020985000804028103590400e014440844901c6060a90452113414030607142ca075a41000c5101088121000304015034503140070541c400002008504075220b68211000780d0740c2e8004003a001c1c0410303149560007d10314 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 48909761 1250 48908511 48908533
    0x302030415020304080609300d0b0409060c021e070312050306010203040e130221121c0e0606040c110703030309030512070e0103051609030b040201020c06070602030a150503 76
    0x1007000404040c9078030440c0c2c202030f203685d64036040c6541520301c0034841e40f0280080d10186026103001c1841082d40c40031301c402e51071400d082d030304602c00e00e4a04d04099070b4a0300302414580d5158001030b80309030040420441840201d0001e035850324905010019003400c0300c08900750041c00034066040c0c03075000c4071301405425840001e42d03a58001428040c1540818007000ca903160100c80c5403841840f5039180c1c0140c40c0c146006000303081031310b910800e00c00d10901e40010405d000c0024901068400e40780d03010ba9503950503a50030a02c4044030042482c95050500703585010340b00103242405141d040710700304244414a0000e94401200d04030185941d000202d0400c04a03010780d204201841c06810654540b0040d0711060001e994129060004211500300e81c005950340351080701d43c4605071004a880d0001401c0015058448a1100900080c803c000040459100f40452401701101800d4191140258034010010b900102c40003a10a403404400310500c44550440d0022500d000c0c0240c920b070403034 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 48911011 1250 48909761 48909779
    0x809040203091203040303091a0702061501110304081b0d030915030209090412120209030a061a0301110705061012060207060908040603020c010f0213060804030306030204060f090c020a03020304 85
    0xc100108034041c0c1c05603c405041d80c00c000714802c5110340d4001482c024a49842000e05544846080c0469a440100703c4800d4002a5498021010031074820600128600403980f0035112481b212107800041000264000006040a062540c403008900c44071946814011003494640e03025000444d044802c12901c8182d0005020f000c0252034003519104082c008240c030b40206950407a041380c404807d080d00d05032300c0054501140304840096141c9042e4800107503541e6464403000d420690380b00c0b03034070649100c0a10210341042001d002031019001384030002d000360b003000e0300603201402868002101d2254203901d840c142c6041c0c178030b802510201501ea010080d007009008407502c80d030351800340740480d003241c0140c401082a60380250360b4100d44010242510150f0f00c1d0f02042074010f2120b40c0080303900c0489003041e40c1444ca0040701503074642c20102c0192090354406508a8030b0715201041d01c4c1500d030003207016a0a4200c041c401e1301214041260340c3c038828800980142c1052006110f4026 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 48912261 1250 48911011 48911017
    0x1090317070c020a0e060111012906040f121203050c0f0318010e060618060607030f1403090703170901140901090302040f0203040b070203040608010905070306090c020f06100308090402 81
    0x288a18101a0b401c40380c3e0b01080860f016600140c140c00c00360030400c441c940e8072098010203507170703180e0003442144112000e1000040310525441c84400d1000c3d801d900d107440380c0060301d0013040070088a071145a80c419182c044e95164400540307584100000c1d541e00340e0301a0041390f0062206112035031130540394035a007043c541c001a0584807002118158032045140900800200d6800c14004e05040c2c28030303004100e40d9104404449001c80105c07070810400759145000c3d54107150b054201180802c44a07141240c1891855101c66291070001c8180b00420a0000d44c80003501d11480b50741d200d160050644041c58020008014001030a80e08620f514400440140000c5130040c1052030b4860749a0303000505845840158180341da40c04810002481070b040407690300078485001030351800307042450040c101c20f41409449181a00da0010a4100e8070035846003004103001c1d6000c100e40c0c042648001c1d1203050158140036507210b1840410703889511000904210f95000c50024600340c41c0c4030038000650 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 48913511 1250 48912261 48912271
    0x603010f050d0f0609050601060810080303010905060117041101020d030203060306060f04060510081012050a0308060a0f0b030906070906020318040f090804210c030204150302060a0f090801090317 86
    0x3c120035000c200003c105001e80d1003180d20410251a141d810030384018140034008040e564146100c54042003100c0011041b01d0550303203c604041080da854500588800d00c20700c45c036403800e1400b20100000d00c04a00c55182c40b820090782a18107003078205808a00b07034002038031700c90b5140c6c0101d030110300c403481c10740030340e40b45048041c2020980a03a5000002c0812103101000c42c0400c8a1400b000703804007401550300d014215a9146036a0b001a6851381582c0f80c041c40e400500384205500071503501d58810064800502d000d2180d00d1a807a29214101600c2d001175515211070b22078107010840c0765000b0401c550a0703906690003542082c10301c901c8181d03400015403420307401a503030346400f03050018180100400b03c0e010b8800b25680710301c1d06e440c007a5014070707400a60100004409004c1c00090305100030004981e0102c4000c9200502b12103841601d00107548001e510602c005200c80920380c00034003005002c0819218810007503600d0302110300b03a5240101c0140000c8058554416a020310f8840603040 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 48914761 1250 48913511 48913523
    0xd05010905030c0c0f0402070b0117030403051014070207050312130b04060306050915010e10020327010e060c030a0f020f010f020702090124030b060705030301030b01060e0603010f050d 81
    0x2101607448030382c1541d02101046a03250405541c42070703075050540110b0a80c5000340c6045280405d15142c0005e1884103014291000c100d04001c4030348131804109690240d1380240a0b100802850040040204100304d4100800d03007000d800150b0860010411710700315100a001b03040c50a05481e100c0240c1c2e0f200300301d40e050500030403401040f09403070a4040c001504880d10001001070508040240254008001b032040500351424038940740d0348407034030b02e40005050310b0622010440307110903030640c0154040d0070603180b10240c0d800f03c801c1a581c418000e4110a8960700104100c00050050034428541e21400582c1300300851082c681c450f12000344041e41601c1a102c0c01c1c401c180c0da80b030a641031420340c5040d0b01e80100380c04055240c07000c0b07140c0c01403c2c0f13095002d01526000c0e00c440c80f2a1101c48800b400d040d40c4000c44130264803118212190150700a099035980d6071a4034068400f1202801038100140d5981c0721074115040c0601100c0c16100c1083d02c00104524082c1002484000fa01c002c50308 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 48916011 1250 48914761 48914771
    0x61205102c0f01060e0903040302060a0909050a0917040302010c0b04020f090f010303020c120d110123040b070e06070b15040e06240f01031104051203190c0309050d0501 74
    0x1c5141e21a201c080c00354205010303040340b0101c800d200c2d003964420703000604d11104020038840d420000100312822250706a400340c3d00e41411070781c20b80c1d007400c566004034070850800003081a8841b0550180d49094031411940103071401e0403140c024103002e03501000380071400028021000c940b41590084c1c0c403a200506c0e84400f100303010086a0034031820354407020615078640050080503018803d100d81c00ca0151210500104016042ca65072881c0c0e22a00d000d1220820300381e560700c0c85c2074000c10b0549036015078060340391441c91003602d40320000301c805a8010a01c2008582001d101d800800800c11009125508015854403252000e150140682c2900e00316079010346400e4031503006040138013907020f0180200e0f20742709401c051205110400c69008441803a00c460003662114000007070300000b032800041c9074805407001120b621454000c01e510840440701d02c120303000004000e000d22232910324406009001428103503002c0750003400080c007045400f5020310440c113104800080e0a40100c0010070 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 48917261 1250 48916011 48916061
    0xd111906050a0b0406030f0c05031b0409140102130f050603010b07082d07050606030706080a0209030c0a08031903060305060606160c0603050106021e060106180e070302070606120510 80
    0x11590b0306d51007181d450100a44410900284a149200034035054018049031102200111032401110316054800c41d0f6071115001031002c090300441c0202c00700c400031541c441032880d101d086a1494811003203401e11420f000701e41410120240e0341211a13031a601c81c10b03d80d00f80d65560103900078580302c0088519000060844a14900c0d2658904004905043c1d0340e080b1403c1c0f050426400420680c06548400000c02482e03030b100210f1580b0182110005854018180c002410b0000060745241d210030151030100e40d13400c000c00100342c1c1c40402c0100d00002c18035610160140c13965844003819a0308240001551070418000800720000f080780c0b00c0f01886081e559401120f005034000f800041d41d10700050100980400032548640d001c0031404800c3c08007450709540c0d44c40140588010420152070640d00304819921240c050a4a103114000070314220340c00400a4000d618151491404d190f030000354400306900c0c00381442d03000809090700c24803115200780036002c0d50006400b2940005100b407 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 48918511 1250 48917261 48917269
    0x414030f0a050403111c140a02060f04090e0f0a0210050909040501060311040212160e090405010e0616020c090711031314030601060c0308040c09020c0d111906050a0b 73
    0x14841c1d4507200c1544440c25030528540803001000c2890043c82e0b5a8140c00101481c100c41080c0740d60b108044000f524946800a4101100600b00940124000c01d00e9200092240054410f4980c0c09808004041d60052050b903075020001d48070160390080d0b01c4a02c0941046501c4507200c40c3c16041840c80e02880401160024030f00b01d40a4560380d545010500400400720814104000c1c02c4a0540c1080700c5215801c2da1f4400c09010b0002c10322280030003d2009000781745900500d04000c000100c50700d0031742011406845454031010080c015140001c6d01d114084545035210b510b10350050110062400600400210140046040c810b40f20541e444c202030401c010075100d405070214040f00c5150030107035049880ca85003a41e1080e00400010720025600000c00507013641c151404c4003071611541000360000c00707150401c030241070001078200320841000500221003a22941c0314a0407240a9400a84681006c0c42c032000b0f621207101642c000c110260812a003100d1703580000200111020005 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 48919761 1250 48918511 48918517
    0xa051201080129060f070c050603250903120809010603230c06030f061512071e0c0b070c05010204090c0c03080a0b030a020418020901081606030e03030414030f 70
    0x707035070142c0d1903444607118600c1d104010740a121110b5000c46003801c1e001c0008805002d00c5803080081c40001c903140d014440c0c0900b28400030880504440e960b0704001000c0c1d40002d00d00411840b015080940806100e03100b01c801400316500000903146500451400b15002c140161420300340d0742d250000807004c618050000000184041c80d580c5c4800800003000303080c0300e014104a44225000e00c1001502103042c1d410681c03042c000c50f540b00c4d03445004101f0100318003460030f441e100c400340c0804001203281c002c807202c40000e0b60002481c440c21403203501107507088044a0020001c04540780460880d0340200c1c580c4900b02c0c030410016040c81d85440c5040100e5030307041e0000c0c00268940d1448002d0580090000e60454040c0905000c0c004100c00482d17600c031003500c0000e000b15a610049401079050300540001c42e94014804401c03941c1d00d81c0c0c00707580c4d41c40b800a0444d1100d0412000101d05000b0704c21502046030102c042c40c20740d516603d500c4050b49843d511031401e804100212444003421b1001 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 48920867 1106 48919761 48919769
    0x109080a0f020312040e0105090901020a120b0f0d060203060f0316030f080403051c030506040c1b051507050304061b0c060b0301020412031106150a0b0a051201 70
    0x3c00c2c6880710310310311211103810104002c00d441e0244201c5504981d4100e40c00c001c00d4540b1540d1600300c1c82002600400b013800b0782184800d03a20075030031005400c90020881750509440002140c5000a02102181c6d00c0b0740c004104070b440d01c0c00c2c02816200120640051804031f440f00d05105114519020203000400111992400c0014402c1154046c5610000361009455441000f25126501412280c0443c3c100703c000380103030515110703450042d243c07591500c8920551010b42000b0a10455094a0300e00420b05a038600c0303442110300c0307070082c011640e5241c4d40c0e16217400c00c0400c64000300c15602e444c0f1280c0c0000141154045a4440300503002000011000c2812000a009125a81c00b00b01c141440e00c1c2410141a0000c2d060040703c410074056038116a2101151b100362504030f07050a030b02c40c5008106100d101d4681d8040c00d407800a07420700f1883c0140350000084045001d0388 = true := by decide +kernel

theorem cover : BRFrame.Cov 48741011 48920867 := by
  have h0 := BRFrame.cov_init 48741011
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 48741011 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 48741011 ≤ n) (h2 : n < 48920867) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
