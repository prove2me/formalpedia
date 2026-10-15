-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5510
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:06:10.167291+00:00
-- url     : https://prove2.me/submissions/5f39aaa9-f046-4c22-b757-bbb90b81d559

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 990827338 ≤ n < 991007194 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 990828588 1250 990827338 990827389
    0x302010c05071a07150e030316030615080f1501020c090910052508060319020a03080c0606010e030109110139060533130509070315020c03040302 64
    0x95030a200908035003c9400b81d01c00138044080020002c420900030900300ca0401c110300d040c40200d9030340e2001800c415040c0038803a00c0001b4003440b0350041809482d100300c20103086a00002c029002e01e80540300107051002d0400011038000c6110070600121034164000d240d042420310034007a00c4030018106c41d101c4d006081c9680006110740c0503040c02050007a00180c0d01194054200109a000c05105c504010241091021a90300040d003010544105010100404010710008035407010903440142403080c0494444001100400c0003445041c082c2c0700c280d5159406d6007010300302c415018000b81551054003c000030382d48143e440d950640b0701070070300c10494400d00c0080e9454254100d84481e01c1076100394043c2c03c1080602829400100c070200d40c03004030110300f141c072055120b1031061860300e1640d0034221600e80e484400c03146071030700c81410800613414042c00716070301d4a0541c081960207203000e181071035048002c1d10813107150101c01005141040d0a59080010b00c00f940d90508100a21415 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 990829838 1250 990828588 990828599
    0x1b090103112214011b06020c011e0504020103050f06060307030b03010204270b01082418040609050d020d2c0a060f030f0603020d0b0a09051204030302061501090302010c0507 76
    0x8010000d148041000002843c58a825840f801c004070072014108105c1c00c0000d0b42454440d800c0035242948040f0141c0c031889a281d2090042203040d00520b039085004020306408400ea51000e40254000e985c140101e82d0f60385500c07400d040c0103543c0581c001138200001002c03a0301c244d20462007084010001f43c03405a98008208a059401f25041c10300702c5600c0b040074140b00c451003500341184082c00d0603003140c82d14494612a8418100e400710648868002d2880715555107030580120320519510b00c4114205030070301c0030080544c01c0c411072700c5d84103481100000340e00000384924081c0079a51030b51082c20900c660701c41003071035400c00c1348080300c0040305084450303a038481841c002d0a000d6031143c1d0100c408045c0101a92004001208224036000080c40580c0710085081146a0440e61030096522250b0a8030010805860050514010641e2090040c000c40009100326400b0742d0842d01e40c0e84a40340100210481e80140300e0201e0480c000400055010701d1118040a00860640c0d20f4160b03203c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 990831088 1250 990829838 990829867
    0x21e03010b0a120501032a0302150c06091209040e07050d060209030d0c020a0306090212061005010233040807241d060720010f0b091b09010311 63
    0x1c0e0003800d003140700842d61900311507115101c0b0284400c1c07218103101d40c0d451a10341500d209082840d0114a01d002d107240a62032001e011a0f07001164050074440c980005026440425003082003001c07400d010726004a88812400605480700811080313031503203003181d86400c10008005a03000308060b80204500000d9580d203503001071407441e0142101682d10b800352002c05040c400f40c4031030001441096802100540c0302c401d84001503c1d4031200c0051344400c917000140d4890741d107103501140c40c410b01080ac910486880d00e81c200b03c0d00700780c08440c0450180201002d00034074081c24486881b203e00c0c01820b2080071214a103030440d001d80b5003d450030b130301911188030807003081c2404100300f0300140c2c0b840e49080703540c0b28040f840705465580031a000c030504411a12030201915107410852030790707000d01344c541c03400c055001c030814658001c101481030007160b04094501000320380d100d25006e00001301c81d0681c0c0362100404002202d1298982000d0000650040c07070002180a051601407003003da204110 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 990832338 1250 990831088 990831091
    0x5040e070315020403020108070908030414060708131e030b16110a060c0207060c052a03031812030c030412110907110f0106060230070818010804080d021e03 69
    0x2c0c2000940e031941103000160407c0701c00b614130010000c56160070000320b8008001e83c1c0c1030340d0194480854a800740800a4020300a094018200d2080000c8040c1c40c6030b0204680c038200d504140c00803080d59101d00044504008510000c0d002c0340340a00000c401c15131210b1802d015992504000034a10213000e1180d240c01c100c00350032682c855807040300c0781c1d0300c0e501001b141000b01410315040c4004005591a40d03114908074618144550010550040c6002c500703818180400d00030301200e481c0c0300c00b50104042ca8034a0040d05024025625114108850101c2115444103c0c5c80c0211700e090710b0700c002d20700f400013020342c15150358415514808840d0380d1140510b015600d1551910398150341e000c0b6050801174014410110ba0703141c090308100040e00814251210100510490025030303014140a4002c1911901c0040441002036070104008400000d03082c1290350690350100014a400152258107050303801620200303003407002518550340d50b002800c06000b8109074894160a00c0a034465070f420 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 990833588 1250 990832338 990832373
    0x61d10021e040f1404050c4e160801150c02041a041811010e0a030c080619050c03010308160b010902251509081306030f230105040e0703 60
    0x8038101081302c0080b401c800001d10780c040700d01300880e041c404420300c01842044010041588656480302d001445103803490412548058824011f80100f02200360602d0286054030707013403c01002081e824103064030b5500c05002d0b1502c0702d900507401d0107068000c40f000100d80304100b003610040310703006843e24000c080d0006080d40d03281030a0490181040140c4203050004424144007032a0348001c5400f080c08003d810000b802c045000c0d00380080070400c0d500654001900740b004100380094140000030f4114480c0e1580600e5084420740000c04a042e10020348901d0b054440500041c000303d880c8100030490032070704504540400641d6954002603203000d90041079815408141c600c4608040724410b0084204004c0b480e401c007549640f00c100780303080641807405003503961030b12000700100802142d046040c01e0b8a402001641c0c0d5500502610880848503c1c080c00c1482621010071803628110100c1e01607410300e8016803d020030300009081030500f0650500c01c440d800000729800682c814508038 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 990834838 1250 990833588 990833609
    0x3090a1a04081b0406170606090702010f180b0106170106030b0a03050607081014180402060c0a080d060b0301080307030311131d09030a05190921061d10021e04 70
    0x3c10f0f8040004990083c4e015502051413a6110001c078032000c20115172190f4121a44450742d00c0d20501240107203e503d41740075000b45440c1418901c03a03002d07010300030094420b00e03020700c2e141e889a1045030300c0b00d503083e2100481c60303010b0010300039240a40c0140c0115031014000e5807405039039841d01031810400380d07900800b20f91100244031905813840341c100050000030044078640000000494084082ca400d0000081c003000042021503640d28216400d4100383c804680010500381051481940300b10301c840b5001d403601100050b128060400e882c101c40c084005541050125242503026142c100c1d604014050704008981c1018002a0264081e12280814200070107580000e1500c401000d04001e49540c0240440f034200399000701100c000d103040581403907c1464200003a00c1c80c48064202483e00114001c01160304894070884034460741c05564140024040c41e6002130303032800c3c540c03100145070300140400e0904054035002400002d42c5000706820b07a41f404501d0f00b513650481d4200a1944 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 990836088 1250 990834838 990834883
    0x1902040308030f0c0f2d0c0f0c01030501050907120608060c07021801150518030105010e0a051b0a180e010b190305071e030f090809040e03090a1a0408 66
    0x1090041165480790407140001d1512405c144818001c1c06102c0b03000f80c82e42110300c1c035044820b203004448108014494a055140ea074a10031b0750781c903403044044ca40d4180c451003a00e070041e580f00380201e904803000504001d54944601400f162440b007045481e8500c40c0d1a0300c40080d404800f00b00651280c4941c2c00740c1903d6000b20700c10005100c0041c02810742c2e0070480001800006480c200e100440e000d6400d060703a40c5c1182c110702d03089442d1018001e5526502c0c0500000b1801c80b141c14a030300ca520107280400203070342c559840706280c0b0900103110f414280c0910104903914020f121805d0701d15024080340001d580d8500d5580c007904800d8104039810f44011070320706035001b6000e03960440d16501d802d040c046403805500080c43c1f05d82c1583c81010345980860890f60301401b940c8050180d0b103005405003e9101c417410001d0442c1c0c8201e0240340500c1c94648444040c81c008020340d803001c1c40c020301c0308044030310304004105902041e12802900f540104070005012908001041c00705000c28022141d1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 990837338 1250 990836088 990836101
    0xf060415030b0907081204061b0503040902041809030e01120204050d0f02041b020a020f12030706060f08150406020915040e10170c1012110403200315190204030803 72
    0x1304409070f0310100440e40f01800302d0f41c010301400152403e50304a450021007014401d84241c0500c41a8107014055000002d030205440069800500540b41034554450005803125000c1c0119180110040c00042d00c00d12098019072141d9881e0141041d80c400c05410309032640c00080c6201c000c0002101c0b1401a0880ca5045040502450005440c1c82404541120f400e8202035200c8041b500024400c01e040304043c0c03199601e01d030080d40c40001e00307022a900c0342d41c240360490080110780120209068800380c0040c00d41c0c0c0c000307a04190f00d09403003003400c030030380722541c50310301070f401c2081d010303500c0002404550a43c0300703804082d000900b1240a001d0f8181458002540303015040c0c0c011100b09020040d40c400c11140000e020400c4520036a86115070380c1c403078841116003800142c005403246052090400c00501c0800c0900196405100400c145a414803140180741c00c01006581d05908001c0a080d1840d0480a10343c1d403141541a49600050780a100f0300c040380d20540080b1040c601c0481800072 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 990838588 1250 990837338 990837343
    0x60206130201050904181b0302100c060603060e0d230a0e0a030204091203150b0412140f030409050a02131802041a03070f02060127060f0f060f170f060415030b09 71
    0x407d0002c00680010b21400d5402043d400d030340f201d9100050000d0108504200401d80e80200002c50300880104602081c4800300ca84454500c007161000a540402d181005901400d5513202e211030031112900d0f00d10f0310708041d564025200c40300c03984800c00d00b50000142c1c60b00d00131808468070a501e00e8400e082e040341e0107411100c40c040c02c08000e01d542d51041c8084500d070703401c4400b5903034080120400c0360310504c0d2100c1d201e01c000f1b582104501819243c06409000080074105884480c1000d02c00c0347d4500400500701e0240c0d02054601600000702080a00e10070300203442c95410701030740940b41c240c030f90001090103102c0d841804840c100c00004c200d82194090301c8520204498400317000154581003014040300310402036606480640c0503030f0b07100d05032594001c200420f00082c41c158215601e0104070b208101912070800461016140c552000d032086082c46487e500c804040c00c0561a20b0100c000110703801465180c102e030f5034807801080b074091039056000943c4a51510300e602e10305100020b0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 990839838 1250 990838588 990838613
    0x90e06010e090303060a05012a15200714030717031008060402012c0d0510060b0307090b0f1204050601080d0f080103140c0a0b03070e010906020613020105090418 71
    0x2da0a410a0050003001d990340c980080c00c4a909103040c01107072110320f5803910301d904484600c040303130110201c14104228003400c1200c1104e4801344208001402600003215248105001410300e0004001386c600144141c111810349106940072242402c80c0340d6900d5500e03210150003050340d542e02108014510b0000340d04500905948000390030942440d50000c0e00300d900460f1000c031004501d0280c100514441d101000b1042d800804c00c480e50400390030050f0312944250040c08084e420302034081450010201203900031031181d958588801e1502d10f0781405074000c44d031703003440c080e44c10004400d440440c042440e0003140148044c100d154980058030385421081d1030203c0078041561580300f0405e41041900d070450360000c4d0610700c01c00e01c25241c50f04041c1403a00c0954050450300c00030800007080f0380514411200c58880d901400c02001c015150002c0f14800c07940141d00c51070004000c0000c0d903544507100c81c4103042c118141140c5000150944060303403070300d0030803002402880060050f14031242 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 990841088 1250 990839838 990839851
    0x50d0609080a390308060f0d0b04110d030819060b0d140f13060b031c09061706151804020c010e101103010e04140d0e010e0a0b160c090e06010e 63
    0xc0d00c403411959144903c440c5070f00c018040c1303c000720001e4140d80701c01310110044070000701402070515107807074401c000c02820baa05440f4101d40314207848c0c0900740f0071388040d14140c164452200560301c11000c11380c22901070304048462501e502000a8402c6148050550607040e01170119a074100b0394402c50400d00010241021a42800184145040c1d0011840c0f600c0d038102e000800c140d038402001c03921b0030100700960f80000144010302c80700c075544140340409641c400e40d6440301d80c018400c100310700c60006a41850340070340503ea034141942d10740c01c000c4c85113803010a406008985070320f0009049801210b40014140d444900100a242c010700041900b42c0a5840c10092060030b0320b2141c0084c0014000e500c04107905a0104003808141ca001c41014100c41c0b048950850302c04000a00142030000d0f81408a5902c0c0301c07190041c42e120031400d0039281c01e4802c15007095140c1c0d0707060b00d50300f183c80e40c2640c80e0803c021011039080030f580a140c1084c10070000404a5500d03180b882c000300d440003001d1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 990842338 1250 990841088 990841157
    0x51c27050609120d1109030303270109080901030504060e060709060e120c0909070308030c07060b0f1003150f080106080f1506241606110c07050d0609080a 68
    0x266204000203c15100a044110700000d9085d004100d5801280300b041d130714590622000c01000007a80442c1d481c00d41d585d202c041d85c51003079018214464240c0c3c1150300010500c4d4414042c003e590b502c06c1d804580c1c442e000b01404100ea0054200b80c138100b040548560740020320100c0c040c05065080010300c10b59850580d802404602e801d503050b40c03585143c40107148035416100c082065104204190b0000e1030b004982e0b0341d980c1c245401040005d50004008845250812520301e0070383c03500b1140154204805421403001100d441822001000720070b146410700c00821001243c040600170301140546100e10000030704500b820419850b00425403000d148a034008100c420381c60300c51010858100c1800d454400032416010a4142c68041d26003440320300e000003082400c07061910180381880140161010041010620b5580030184116101c4645507404210208800d0425444000c080e0f4001e03440010040d11995a0114540c403c60f5883d001450740c6910034601c080302c03900d0010303180603c1e21 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 990843588 1250 990842338 990842353
    0x406050105010f271e06171513020f0a050310080c1003050c070f06021201090b22270c120c05041a03060c2701051c27050609 55
    0x2802403640385040210304c0c0600d007040940c00c0c0042d464032a80c0141020300101079820480c000240244d00d1140310f040009003406e2410a1810010700d9201c5c05460540700402c4d40080c200b043c410b00464990a04044950810040c4082c0c003502c00902284006559135540d00e0500c1c1d00401b59400040d0042d5906c0e4006040810030766076100710300c50a6401c1814041550382d40c9248000442c040c2490203000581e01031002030402c20160f000b1312004190342c088401990b25004980210741c41d03802c1c0340750494145040c1d03281d5654031203d400782c00c5442060124491203220030145481890720400c1c03034109490346e5054200701d054841800a0420220702c82582d9010351134690030324102c1c4c8900c500075030b0384840d1188c00e00170308a0420154180501100c0c07040c10308100e041c1d42607101d00c8100c910025400d42c502080390174850b1445144a0582d595410001e240d142031080803142c20070312212564a10590310f40d425070418408141034400c0055000c0101403e1490070040001d04186c1c0301e401418 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 990844838 1250 990843588 990843617
    0x105103b13020d060e1b030d030b0a120f120201150909020d0b1f1202030a060b06040f151103070f1401020f0d05071b0b01050d0206040504020a08040605010501 70
    0x5200344a101a108916030403500d50400007011581c140300080e40050320b81c40c02c101409050b4212409501412040302c11209904038844000110210314552540155405011591294200b1898458000c0454081c5952043c00b90b018640100080302c0400a004c1d4900c2484285001c2a6020791103000038040403c10f1001c12010502a00904603650390b524040001e41d1a0681e103003411a0b4081d0812042c2c2c00c25a024022001400d030344100c442c0d0401d030340032591100c9107c484131221390142c010003548140b55500300c090441c0c1400307160045401d01000600c044c003646100000c00c482010401d04102c1460000c140b80c504d20501711459104005160011340140f0040701241d4205810b903100e09282c201503030181c410307100e070240505004201403580d03040560189000f00e0407910b41e03030400d902c10151501c05894006001e0110380c0c1e03140c01000745080103a5800c0d10a4802014241f41907100d0700024120382005c81d01d900024004410401040864803919001d800b09091079010b242904 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 990846088 1250 990844838 990844919
    0x61703070b0112030c050a0516360e10051b12180c032b0915050706110c0c0a050319080d061d0f0f010f060e0a0503010510 54
    0x6120303c404102c00107500c2424180700c2d240020500e40e05c80182c0c3c3c0701c101030b403c14a90314039109001c0542201c902a00103000d01d50b8002010800303002c048030304010a400c900d607241d5126041241008a51038444200b0704a0b005c3c491310740e00107400400000e1900344031441e280704020b5421211140785041262400c8805407400b04c9601c25118403940b0a04810f040da028103215240c14915058401d0180c41c10040444e62803001569072080d0342c03849031407151003044408108a1241c04034499900c90303030b00080c0303228500601805003d240c01240c00c50300b002080c2106e0f40800c072001110307000626180050b01c1c00a203c0c400a003011001000c10b0f44441e4070280c41e0110b05407004200510008000c060301c401c6402c0800200340b40da084d0b030308800006071401050001100e0007618298803030000340c000d9811203050b9050b2280440e0340e00200341020800e403003038003d10002d035034846500780001403e5a030034000c1c11300c80e0503c408054025072400e030204414018003510342040c090380541c102d0790407021 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 990847338 1250 990846088 990846091
    0x90303040902030f0a2a1d031f3c1104140301180f02100c0f03052d040b16020a0305030a0206160e09060d0606230102010908030c03040f06020430052518061703070b 72
    0x1015103805901090f4ac006030080450043c0e082100b04003007170008246140e00850b00b421a019402030209141020071080324146a00005101a1a1150040241c1048001e02a40103404e091100004803640c8991410031441d000c200c1c0003540c000381c81051403942d8600c041069a200700c802c00b00408807014807490380164010702800640109072280010071180d840b14855030090070502400d0b441c0e003402a243c0d408900c03079401501c1044082000340000440b0404a081c4580e2040c0441950108002c41940040c0000d40d110314540c8100001c00c030079224000003000e804031544803107003042c04500c40340022940d649042d645001404808601900b003120b50010791100003d560340c3d81c0e443c107c1d022110720107026003410b2010a002c181d10b064024841c0c088400754130b644c0c2d00c02c1580810100741582c10030f40284982c205041c2c090f02d050140e070080070180546000950110f031100d01110700003a035504940b8015480300d90800c100e00380e0860300d4400f1501d610240d49080515124a26031020 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 990848588 1250 990847338 990847421
    0x60203070302071a0409090507030501060501170402010c020f03030d1e0c1403040317100f09090201020c040f200405040c03050105010c08090303040902030f0a2a1d031f 74
    0x40e403088403802500b201c8100e034003a2114000800c094409410700303e0740c691180c00200ca081d031070370380302023000d6004070482085c0b440c640744242c1e11960340d03900449001d0740c0c845089800080015054a12b030342d041c400307080140341580001420700000c0c0020040c0803404a030181c00b42e4900aa00c0754030662080ca0302103501c1450003030540d20385851804880c070a801003c2c5540103e0010188503228030000305100840d40c3c4052210915034813540c3ca8412a85818402400340e40b1000703549400b41410f40207131510300c1d140c4a00240681c1001941008207004000d69080c1c180002414440380c64075100c0c1d0300300500d20f40b508008543c100000030b000304030465005890144041190031281ea4204203c45c0680b4008900b0340d120f0506448210401000b42c8290850b141840d0078400001d81c01000e0b0000011749070301302c2540c400280b0b0241d60b0062801484c00c0100c02c40c0c0c4400383e098a0400c034800c140d0100300741c0700105408051151088034071851a8490f040c0f24142c1d800032545091a90307901415 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 990849838 1250 990848588 990848609
    0xc050a02030a0c111906020d020714010f0c0210030e06241302130e0103030f03050f0105060d18050a020a090902150f1605010c0e0f09010312091802070c06020307030207 74
    0x304503040c80000100501c0025038445c0e80c4d01030520200c00201956000c40d0255000c031009465071840583c1c68806d14040c180103040c803201029429886080410307540130840c1081010b00340250045103881100316500b40219480e280031014054003000010352204099041480600d000080900110f440a0229200d9241c175000e04450344510360481d0130b5000002494921656a80700245540304244016004213903401508010540640111445a00020050701160723081008108081c1c020710085400140e403441c44c034124442ca4540907042c28001c0f4024204d5a0181c810804e0341111030308920501da0138032100c1c0b03005840d24010720100024810744540c68008401d4044200d01480d90141c00302c00840507054144103040d807004400c10170f10f40d2030300403000940092040e002400c08050760444c41c0ca4004101203200d0383d01d00c407981161494810407065a07005c9880482a0034146c20381e09650005201c402c1022000d1248001d201d24005542030481949000e51201c449101c0d090115 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 990851088 1250 990849838 990849857
    0x100e10051215120105070c03080c030f0109110d0908072102190201120516020d03020a050403060209041506031401050d0f03031508030406180e042103110d0f0c050a02030a 75
    0x99907a00030103060f07001c0040080205107018200240580c40c03180c0250045179030310000c80c0d44809220200c920a1a1510700700000d41d10303001204000748485954103210340d2061004220311180c42c011440c020380581c030200c0d200e4403282001150300c18100c40025030622462320320b028468022814103c050041201c100000c2000c0c0010780c0c000038204d5a80c040280303046c04000340083e4101808005204c1e039401c0351904100f6160a50482c0709000c5004040340c2c0501007003001540c40e0700140007034031000d40086000003540780d070480034102380e030031410110b9142d2180a60644000c0800c60042500702d074008440070b40307034490201048000101504140d11204803000010f90200040c0c024450314003104e41e03c40d5203000003052254995060441c035415000e00149419070103291074004c03074104840521801ca1003480c511101d80449214090640340c1540b503000c030a028000d010709421451b0045207001c030720010704088a08441c03040050000a100c00c20340580c0c00016070750110900d06100781c00d03 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 990852338 1250 990851088 990851131
    0xd0c0f080c010e060c04061b05010e1204061202031009051513020a081e0c13050a140405060d0c09091515030c0e060627100e100512 58
    0x1050490440640551400100303824204415030180340310030000001e40e030702c2d9154205000410b100d01d00c2203500085140400543c0340f010300b603400e20400e2103a40000b07460b00448440e142803106082e83c02856000c04642080310075001036003514400101e6070110f00d14500394000c001b070403049020b615502551100001c0e0042e500300180f82c41c914000304045c1b03c01079500881406940b002d0388180000d40c0d15008500041e0080070302040c00507411010100d03a9641c038011480703941103410b104c20200084040000c184e22030109c4c03003024182c0320100c600814002c1003440b080e220080c040502407404641c40c43c0c0411038100610701591030b0490041242085800c0800085c001d82250706070341d43c0b401441918032410403001000301c6e4400d0400c0c92016607140040c443d80380b400c684840d0440010440c202e5100c41c00c1c0044069815610300407010040070b0008a00e45d246012280c1c404501c0a0b04d02158529041c0b820080b050350501c0c1c440c1c605400c0502d6103041010141000700d6008403002100390 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 990853588 1250 990852338 990852353
    0xd020a0e03011518090f12050d0606050307032f210c130509090c13060b13061b0c05040c030b060c07090c11031803030906180f060a020d0c 61
    0x4142034014000d0011110418045007034502c54454001c01d007440d00b03205429180240941101030f9000500c03080940d1203a1103122280e10705007401802c0100c2085100c1900ca131030311410015100a0351480d44a15040f40c0160484d02c0411203040402c0c4488031040e030090290701d4140842c005580c00b1500d46c50100c0c62040300d24100d20301482c0c1c84082c5420001e00d1210507016040840007040f440d44400d40c0c80c0180400d50320b00b0342d000132054100650301d00481c00c2c2041c080100c1900260005289542d0f00c141d2440382d0440305a44003800b00d008000c000c001d50100c01c0d8040c1c07484031400307844180480d035a07805900c420b500c281c0340074a848e820f00c2c00045d8040e074008200c0310f1018007999521407002c24490b8950240e400303020004c901e003400414a0794495415043c101c109940210f145c00402c408103203018840d00105036142c402000688100d0701c4075009403142103490416030f40100982c3c4100300358060301111aa000b14000c0c020b941d0354036800201c0341901d60403400c15001c030120b5410203c2c07 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 990854838 1250 990853588 990853607
    0x103020f010e0a1a0919060206010e0903190e0102060610050702040906060b0714120403030504053c24030103031b0804060f0e040603020906040f0213081c020609030d020a 75
    0x8221002c500000c080c07113000050070009801c40ba400d0607000d12090307a0b0349060a0307000304030050307205c0c000500a1001c01c44041c3d801218060850b4203042003030b0f13159420709500942c56030000720908005845960100003664000b03c08076080c0c120350380314034001080e03400b500c040603110f9515650a141842080d43c0b023000030340a880900e660b583c41c60305140303001c038007610703100300c10741c412643d80303058904099042d03906899140d078401d407400749042c0400051281607540141034011854510340402c0d450b680f480d00c41d0000380c24410194101d4801c10078180d04541c2c003201e03e99401c251b603100f0900b1030402c4a041d6545801d002040c2c13050f124012004a8245000070b05c402400600440c461340c000d80c0c40700c6c0450072a510101603001200600c010359440780710003074100814001041c5503150540003a487c0c51a20350b001410144900b040074024504c40e84114024ac2111300d0450f205001300b410b02c984401a0300041400d41440c60416582e4440c904441c500140e02061500c8550710480e00003 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 990856088 1250 990854838 990854849
    0x201050d14040311030a09173c030702280b03040c090c020c031c0e0d0c0f051207120816061401080d05040302091003150203090d03050103020f010e0a 66
    0x81241e950101c0500d003040000781c2e410b03000310f00c0324091100d294030000201d5005c5c84c2e4569504008900d03080c17650300440840704951055000d90a80400c00c400041c003d00250303605841c10141780000d070660007210441e181142000d0b07030001c0010304013584956682c0160704190300c4a200c1c5091100c8580144000f0a41003400142800010b2005016109621900391030940200300151080404141c0c0e96001502d03600d50580c01c2030400404440309019400d90400e501c0c20b00302c2c010340e29100001d10540c1c02500407030740032102c800c0c00c1c0020b502040c1d202014280070b41c2d8002c0b8411038400349a581e22501d01c00e2058011492031b0718020800e14002369030301318505e102c00004030f1083e40782c20b4001c0c00c1025010030074026503c0c0002860000001c0300c0000340309507100e044ca0a8110740034413910b02402081040c442c00b52040c00030000381904110020065080c2005031203003070400006050680c01c00b80303901010304000050016a503030085040419000b400e1a2781d82030801004a200f45074540d002 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 990857338 1250 990856088 990856091
    0x330070b040c060327031101020a0507110105040609090c0507061a180610050c0c030a05030c010b01140906090f03010218030c040e03030f100504090c0501080f070203030a090201050d 80
    0x266820858011940c0707008900c00e60344520003e031a080c1c1103044075482c0e551402808000c41e03114003103001e0003046003025030003490184483e405403000d59003a40c1c002d00c18034001030300005d803a00a00403210720004141400b440c28038a01403130860002c1110303105006061105030f80d4101d0803102c5014108441120350310040500007150740790458450500c21040e054024004181d17070744400d02d82e031300c0540e200d414000d0240c00101c000c401c2c2200d003500200640d0340c0e20f2040c0072903910b084e0f42c1003024014040c460030055550340300c1038488a09540002018074180035414004003100440101600e41075601034031190b440b000c10200060a00487c0c195182e05540300142014400c0804060703c800113000340c0c103d640b0780d42110f09200c1161505483d0f80f25540060002c62100341d010f10303040307401003804030401c1c588585407000074003103a59000d02103a51004040081100356000800941ccc0080344c1d14000700a440e200d81c0184d26880000c0c142085280d98241003011a8007a0b015220454a40d100 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 990858588 1250 990857338 990857347
    0x9030601171624020118080c0f0703020a03060b030102070b092103040c0501030c1829071106030c13120204110705070b210907030606140330 62
    0x70080003a081c0418100c0c035000325030742c0b020004078034a41103046034041c0070032071003c00c0388090002d40703502c6850394842113540b2048030080c04c144103580c003403071580a60700300703507840e8a07007545070b45010314491995400d504466820070140e981c0384d0108003120381140001c281005040300207802842901d00c000d00b101810320501c40002d900184821440c0380c000e00340303404c4443e54019408240070803180249a042045070a2186520a41114a54442c1402c112020301c6c04070150340054801c1713400480c2c0009038811404060311b52955005401c18070150524070f41049030301c600c40700000c64101280620400400318200c010450111032036901030300421f0207078030b0310740d11031485803a181101a481181000f98086a0180d100c0c102c882442c1d1200082c21020300c2c0092480042c1c0010341054445421044203242c68045286041d00c1080140c0181c01341904614003a07003107503081e8000c0c50b0b00c2d284e01c0046d4600d989000a00c1c2001e0800303c44514000240c18105900100224440401002c00401c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 990859838 1250 990858588 990858599
    0x61e07030f0305070504050f0f0a08060c0702010906050a08042018010e060402040f18020f1b1002030c0909100305160e010803120c0d0608071e080c03120a02010209030601 75
    0x14110030802841c2d0341c00d110715140e00e070301207611b8003c40c003a90341d0080040c075000765a403030000000f892071132025004044407640c0700301d06402c03e54210307000000c200000032102c0441d83c1c0130910001070802030030f00d07030f083c10703010030004199010045c00145151003948d03861558020901103c000590300070880d01c804e00d801b81001c000744400b8800d01d00c041c8101404a03c40780307024001e940941e41d0003c140e0b45e01e01d00d0303c0c1d00b91001c16000b0400e40f500c0795081040080240780d2800a203514240303407138002403d0304d8061515140ca0f5140e264078118038414428466a854071000301d510b042821121103061342c64517003102284540f594401040f40c4212044a01144181401034003146c0036140500040e0faa100c40e902d803130340b003140400511041c20200017200d40c50310502500214010000c0000c1d5241c40f582c4513071074132810b6000101203240d00d58094602a08070300c602c201a2905501605071030030a440820b556280c40b03085102e940c940850020410b0b4802d5050b98180d41c40102141d9095942e070 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 990861088 1250 990859838 990859847
    0x2190b0a0207140301020c0c061318060302010e150d0902150309011515121a09040c230a030210020a150209100806010c1e1403030a140403050306061e0703 68
    0x140b00740c0360030f100c2c2902c0488081c41d062080e160483c24440103040c1e1801c030300c02007180d140d200c0361344580382919103400854280c0b560041402c46038444003000030094198000903220a0360500028801d4854a00401800b0182c0c8290b800b156080f442c04107021800384005080c841444404050440b030220070000b00c58015040350b5001703c200d80500f074416495032070b40c02560311440440e03004214140e030817803184e2035107034041101b50740001a0a500f018110000804103041074605507810b001c5288188000000c8400da0b103086624541400141c81500c07000c98580e076840c1c800039120711200424003c0d42ca00a0041554403944550b4603100740074000344c074000a40140000302c0c001c400d601d6203101b00c18059001d1502441050f1164200800e13941e840c042064a512024055005032403c1c0c03000080309058442c4050215401454492508400d81d904440301541514082d501c1402404003094104007103e802c404140d4001c1d54510100ba10043d40b00c00e1075209802c0c80340300061020502d80d22 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 990862338 1250 990861088 990861103
    0x702120706171003030e150a1d0a080c101e03060e06061812011503051f0213210c060804030f0305090d1b0209010608040b090a0f02190b0a02 62
    0x2515540b40d407503111111601c1d101021110341490000b01841030003c00e00031080d480c1007100080ca01c94240f00b200014a825030401a002c001042111600006040d0341080c010034451051f2250404149041405c0f5502d50910343d45c3e50240b912030f03c1c020051340c07081084903050510200d100003407540c03141008004002c944980864030300304030003085035403600d803080364005030a07298a2008107049204100c41c100c0075031800c2e12150f41c0d44e1070f103079150002c3c6c86401004501a80140240c25000c441c4543e03401d0090f6440e9941c188100710045940c01d185040f541905c02000707200454180d840243c610140d420140070f0309490300741364000f8019602c9070b80c0c1031207548640d54141040c030710540c082d803d8a0701501e0b0101d141e004101c01d004007602ca002808904000d1304000080e040791038011880201081c0c0000000a80d5181048140050702d0a90b80d0040161401007900c05003d03240d003200c00c941f00c10000c0c4500c410010100f0700c1000301c0803420190110b00881c86da030765495a000f03569141d1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 990863588 1250 990862338 990862349
    0x90a09060b1308060402010f0f0207051005090a0b04060f0c080d11030103031205040c061b1b1a04080c0103050a02120903130f050604060302030403201605040b010c060c0507021207 79
    0x1402e00010840000100b01c1c04c0c0500e034181c40342800d18145030010f65414140b28001000c6204900c000a4655107520805c04580f020380c41d0341d0741ea02440c8041c0042c18a90341c01c040e00c02c107010030082007019486286201c000c80c0501e0964400541860000440e10030801d0b10241d4509080c00e402c10360080b4801036040700d00c00c0e00c1d030180400b0505111410707620304560140090281030030405c402402580d580c4000444920042caa08400c0e554407501c841200c20b04101c00441d10005010b08190951004c0341f007500803044074101840c00c412a03a60349001c48a06042688490120b0b450021940585007a00000801013003145808010160340f034000d60041441c8004003d000151107102038901e0040d540050314a6140908200c1c09401940c409070040b010030a030031090131000c01003d41744001051843c40500043d01c48a4501c80c1c04c02c180386c1065102d40c3c80c00a081c0a140c0e08441048403640d0b0001d00400c080005140643e41d1340650200079400a140c5082d00c05142000b140601c04d964 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 990864838 1250 990863588 990863617
    0x1a06010c0c03051b1e0f0d0209040506040c08070b0306010e060f0705012405060d05070e0d0b011511030a030e010608070b090a0801061d09160603230912090a09060b 72
    0x18041d0412550811045c11480c0c2c0404291000f80a4148801c900020359005042c0b002004140c1e80480c9080100f110103032901e070410414082003282e04540d0b18010030a29005142d11420102808818440034000c603062101260800103943c450f103055a0030340c403942c0401500d42c122420814041c0104c008903481540070208019905c0c0725521090742030306c401401c1c240c10b01000a621000604000e4a1001800100da1803603c180d940d403c0200c2c18139100700340c40509545010b05030450000074100c2001071205081d10802208800016201c4040640c13a01180c0d0b22003188000d0f005102c1d03034008010a0007006000f08981700f0510061525204c1941d410040c240e45d5640c0314220b030458007a454850318040398044540421680c9c2c56009458003050b10502e05082c010342400413980e40c0081c010940381c4000c0304098000305410a24041c040e1006a07081ca4003403070880e04c0c0c41e0000e112010300c6c000810600641c0e1240c9900d0000340c44445802c109058032100d4000321a0002c441d00100301 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 990866088 1250 990864838 990864883
    0x70f030501150503190f020d02030f0d0f0203031605030a061e06020f030c211c05160206060f010c0501020d090f0c120f08180d03050c0d09031a06010c0c0305 69
    0x1414001171004130011a806468519652540c0e509402d030702404041e40d208169201c640003684d0300740506095011901c00800c5003e911010203018214020b05950554109008105d104070122001d44800201850165641d42d0750310306031401400c0d5900080d10034003c800d0301e440c03503242d202c150209581494084031007881c410640d440c0c4c0d0b4402c034100742c2084c1d0851341d008045a5a603031a00e440010003045014141594000d4555541c0c0240403803802141d1100e090080700c24803103880c0d070469210341c40600b08600d88a80440c4084003500c4549042000340c0a440d030510100798191448241d468200b4080000c19044c03110180036009001d07101d256080c4c60010f0bd1014004040003025804408248105c0d015144c4108542080c4601815100103802031507140e41d4580600e00307810321a446240d101c0d0000714a40740352008981000040c80500314080c000710781e005003014403400240f229080740e95108001216110a00c5000421001b1740780b0380402000404240d40c007810f0250903807843e94 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 990867338 1250 990866088 990866099
    0x21911070b0c2a0a091116020a080a0609021206060901050114070605010e070917060406091703041b0605090312070201030b1f0e010c0f030e0f0d0b101d0a090203070f03050115 77
    0x201c0e401000460b007246ca0403c00800d07000102002c05465a00007420101d840c0d90710240d403400c00e00380e440d045604070b82c0d500007401146001a404103050b0b82d040c0090040d071600302e003c1800d484060042c41e0621044014400c01c0a80304402c40306020352051003403705595820079204c00c200c0660b46440443d5103508040740038591005920720803c0307894004e040c552582e4407440d0040400700c3c403d60707018045040122012410344010344c0100d106101008000701e01c070b001e030782ca64405a00803c00704401005000c907140d60019081001d0341030040e050f951081c0c50310040c0d0050403d4140d9581190580c001c024004034613990600503645291511141e8405600c0116100124030b00010b0100301081d43d45404071703103c0d02c03410040d0725028060a420000324000284001c00300041150070040c042c040004440300302c80148004c3c44030a4840781074410030201c0340400200200311022042d520a803407404c0d582c00f08200401002018010205c40313449041050284c100307102c0112a4a401c80c40000d031 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 990868588 1250 990867338 990867341
    0x406150902071110090312021e03031b03090c0922030c0c06031407050309012c0709050408090d0f060c0302030105091e0c0c120d021911070b0c2a0a09 66
    0xe004c205030b69aa1101401c541e02c4c80c0300000e040c01c015046102d65140b001100c803d90700c1e00801c810200e80196181e00c0c000d04503810245041001b000842d9003441800b9850301c00299018451710211003031411685c541d03000144003001c0c046c1d070700fa200c044950706a0516420504031111113015104070300c100383d00c1d028280c00703540d884110040c0b41a8400c0004d811207202d8401b5542004403d40003292040703030104510408040c20300065004038024150404658040140c50000d00d248035041c8224a4243c84401444c040c824640c0e001c1c500e603007215030400401100f802d900c254400801c00246d0400c10300200203400034082c0501414058002c01c002c00c0c1200e0040400c00f401030300c4110150380e204101a500d42016040d08050301c1910105180d00e800300380940490005580d0058131146200f109002c408201c3d0185000e2004095210074540c0d408601001034400301c241031643c540303072085070030714040440100d0b40c116620164424003808900c0c2144418540403a55641401d44805a000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 990869838 1250 990868588 990868609
    0x711030403080417160305070f0807121209080d08040212010e0a08090d0206031603060f080a0b04030e0603040f05011b1d011709151302100804061509020711 69
    0x1418850103020810130000c00e0b2000d11011140d0070305540141c0000c025401540405800842e45a040344d5414040c0c484107020080003005400003d000c440d00d00036407640c50201c982c50103071815019400d02800d5500070381095000301128021640c0b81190240c004010a0055900301c3c410740348881503500c001d07814001e800340b105140002c0e04200c0d400365680c225543c0030140072900a400c1010440250362404085c0d442a001ea007089070321242001001000c0314071541100c0e01c0b08400080511144800007084c1c080c2c980d01182c4030546841c2c40c24180e0701604500d2556501203030001c00c000422040004110180307218070003d025450044401c43c0c84500f0b1a03100d00b0020b0005074600d20240c0102d181070b40c010030103050140d511000c8001c140e08400040b42d0051031944803051294201c1c004c91003441d0f01c840659411880a8200d5000502e0a12607000d05000c01c021a0089824080d240e0300c0050100801c14200040703c0ea900e0100020350001c04056905c1a0300802903c16802c2814240 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 990871088 1250 990869838 990869843
    0x7020d091409062110051e0912071104050406020a020f030f090913020414070206010b070f0803060a05130b090a06080607050c01020c01061d07031b0f0507021302030711030403 77
    0x103152036443d01d0901002090307107003000342d854980d509110b2070500e003448581224070b0464004642c624040d1040c0091140b140120103511580004100800300701044001010041c000c14a9482403d4103040c080e0424041034698020b21702000e000400030980c1c020182e01e055a029203100c1010f85168684900402819030140ca004024101c25860810150750748520b003100351016400554003c00c4c110b505c10740e500055101c600040c070107400d8040002c1401403200d00313000e6240ca2510358603800d84000d0490024195103020010407520713034840c1030b940050030020b0702d0484030b282042c1442024200c03044003203014035030fa4404600241014020001a24205e20041500392201a012101580440320b8280c00355070074041c2910014080c0904001082050701242c0c025500506c1055446409000401890700c0d10350b00b00c61000c00680780c805484020f06048a1907240c81c00f043e10140b04040b8002c3d40100d0740070444d55512003a071f0282d80600720540e40c0340300c80c094a41c1869942c8c490b50001 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 990872338 1250 990871088 990871099
    0x60604060c1e0606030213061202091e091f0e0309090405100204030809010906021606030c050c03040306050708100f030b04020a26010f140412050c030307020d0914 72
    0x2806194041e00019200c41d120301540d41c06030401d511844848007842104442c1540c59400420030752a21100c1a44043c01c480d90030054680f5051480d011401450700c000c2c002c0700c0c2d44001880320203080d50341d441140b030004820b00440c58414843c40d154211a83c54515101c1025550405445ca92045141240e58240110316012182040141614008000b11790502c42c1c51045c01d8520024000342005502c00e1080a46804180002500b4070780d45820940440d0300c0700001401100801104a01300c40150400046e0741802c10750031159441003d0f80604d162100050020030002e0950020b48100d04641ea1012140c0703610020385070881c1c13280714444034221084800c0c00440c609000c60b540081c0700501c01d214180d900d40342c40400b03610300046000a00765080341581d0a510a005101810380c50721000c01001c10070082c0c0324000071014001800016001d00030100160146c0112880000e290085070348a143c6920000e5079004c090b40c80c0740004407200c8000500c0c400b040304a02411303000818 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 990873588 1250 990872338 990872347
    0x1506020109152a050c0601050f06030a0c14130f0b0c15090a020d0f0b0114061c091a090d0206070e06030702070b0c010906051303020c060705030721020f060606 70
    0x92018041d021140c1c4142d0303107011401c80c440340c44048000f620038800c0e2501600d030b1402500701810300c2016070129000b101a1003009056545e10011264000c40c0c2202c001015071042c2411141c154080360361455007400001c00121010b041400d40c1d0072542d001150340111a03d4050082c0d4501412003108116840510100d041c120180e20742daa109600c1d5081340c00400c0030303400141e96041611070564800068240000522080300c0d400c90161101c44200e0000d240c007200400d02074440c100e04890811400165041d440b5600c1d0064840603402c994400361407296010558440441502e00c03030a140b140c101030b090742d80c3c00440c1181c4903400640310544044101d10900c00c0c81d0740300402071004c41c0034900010554500050182641c00518000041c50440d146003240c100d41005d880490000d02c940da0400c0040c5c0d000602000300d03402904c896860324258a4900d285000b80e204c020605004e0380d01e0085038208007541350200c1c80b404d90031621801a0880ea5130388070001500c030190004410030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 990874838 1250 990873588 990873623
    0xb0901080402010f032c0f07081906060e0411010f1b0b04020126070e010302040311041d031c05130b0708060102032101030201140c030d1d0f011506020109 68
    0x100080c2c40b030101d090100322041c80642805002c12806d50641d182c0d02d006401100d45001000303e0080c2021038001404141d083c0640c2a599000c40c03011607130741c0031540310742000b00007607900068010400b140100a85040c50324112640d128148645800981040c111009440c4075880041d881c000e03030040715107240b03e1500c0302c6006c3c0c032004206074141312540400c0034401148052100006400c868030350440e0900c1c404c010000d008500071581010b006010074000700c0c18000480122600031200061046548048001d0051500107012007500000c2040d0200c0041401503a500000c00b40040010342d9562850700310745410b40c2c41c00f4281c0421035002851040c000c070107158002d90140102d07410041c5c0c3c02004a02c0d5404038100b00c00581c00d41c4c00400031560080c016991642455102c14200072400d0030300d5a80b8011f1543c1003440585901d61304000306201c05a20b46030300c034600c080c0c50a050103109620b004e0507041c1c014150780a0005c1c00080c1482c03061042121103548158800f0b40c1c0305400 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 990876088 1250 990874838 990874847
    0x1003062706020a0507080a0206061c0b0a0f0914060a230403212f04062307021f120b060a050c190f031d0a06030c031410050a0b090108040201 62
    0xc0005001388941001040003040654010700340038121680100303514035211007801003295034000d16401d0507400125030000038004003002070703000c00101000617910f400c45071088064100c090003c0d0007030364001d110140c03c10002ca6128400c04c000b01041c070240c1700308943c502c0140a40900c48000074010808140041d202e5601621082051585003008240440c60401140c1c0c40c2803259000d070b46601e492441860507540e44a40c40c49540d070015013054500000603100f41003184904c5846808040708444000c1842c0a4441c0d994000c1c20841b01d80c24580f4a92410107180e0540e98003240312290641100002d034028000000c1003c0c01090400642420a88480d004102c800c645801000d8440d030303e01d0f04d000900d902e180e026030070f10356440140c0c0c180900b01042504808108182c000c82c151241d45902048404451080c64002508096542c00310010f121000b01079034452402005d01103c01c062090000580300304030b4000b1040c65890400d01c1c024881d20500b18041299140001c003d903015 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 990877338 1250 990876088 990876097
    0x825030f110d020a0f08061303020319170403030b030610080d05160506150907110a0308060d0b0a061401082a07050102040312030f0b010e040509070b03100306270602 73
    0x64161207804442d41d001a80342da5894000c001036114802080200c504d00700045e03500580007140000c2c024095450081d200e21460351070b491540c0c40300c50405a22841076a02e2030b072114650900348498101450300030050800c07032080c1c3c1c2c860700c10200450303408011000305c02c0454102c08003c040f25490520705580e1500140403500102562800000c0851000e0142c18840c402c075078003d0010921080400c20031800207082e0740300b0828103074200180300d01d000841d84215905401c00500b02c0d6165000981e6002042100404c40d0002d501440000300d00c3c0e41001050302d0402a20312003a000d20001124421422110181505585812419107804101c0b01d03802c0c003140803011501d80f1603940ca8403820b9a00c198806c0300e210030744da03a400c3d0949a05109165040707000081c00e003c0d06a1000000f0170380c10041007002c4c0f00b196148086121b0441c100071b9400189020b408207a01e81c41c4c0440700c1100e174035942c881960b00d05d00f09040b00b4100082542c00d0510911000d40400c1d00609039201c0000a401 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 990878588 1250 990877338 990877373
    0x6030c1e04021b01050a050f0f01091a030f1c020d091707080a1a010b0408210c12030402101107090e010b0d11030c09011505030a09020a0825030f 64
    0x2820070810500583d20744000b40040070031000420a4103004050708115000104160683e2180509016a044041c40140d0440e600f05001094a0300c402d83e04a0280014502003981441040ae18005000000c45c42c0314078072041d20781114012491003810303a11403860b83c0b170942c001400a8000c1c01408800891004400c10120484071110b86034001c0a18116600704142e40d420b901035202c200c21068494407034050000030007800e061514089140355103d88003406682c99441060000f00c0c4400b2540641c5d060030301c0a400c9072096901c0c03011082e03035907005030380a0780100000190403041c140200080d40803400c4100040035028a030183c82c0c4000c040c07a9501d0100d5540f00e0b44280003079620440501146402282c00c0c01d00780e0b407510105072a02c0e005010440c01032408400402c042c1c45011404e0007600d4031400e116549a0707070304c4243c4005010404009500c1010b0a002180d001d6000812640c3c490f502c3d41d55440c024040724100100e80002e11004100880c001c0000000078280c8102c0081601d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 990879838 1250 990878588 990878591
    0x2090c04050301150f06090612050a0b04050a0c0e06040614130803040f080f071a07050f07030809090f09061918061b17040b131a010e06030c1e04 64
    0x1e466500283c290f6140c44114944840711000900c1007092200a110082069003050008945030802c041c0c540440708040500490743e0384009203c1c03d1b0541c20119a480004200b0020390ad0070020150017080305808900001d80031f07501040031414507004403800e07640c0b00c6c4c031045114a9280c500c0003403a804242c00504c1d9880071200001c0c016010070141026014079010502c44130704282c203107440c110710304001d000070354000c0c0010080f090076031418036000071100d2903c5942d614a410494900622103c20701014030174010000f0034000000047d0001640848a600e03281e2034401d265510100152001009600440e0104040303c0b140e1810b420b4150043c440491030303508602c9543e21050300c02c081603034410b449001d00100341c40b0729001894030340868145403641c180740e55209001c040d00240001c2800601c0004111078900b90031110490030b074412920000f40440b240c2d03c0c1007000b020b2082500c107070011000304420340ba01045400d00c01c0c0015051210b403200e200803001040101c0c00c281c2d500103 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 990881088 1250 990879838 990879847
    0xe10051305090f1305190c031101081b0d0b060310090b030601080d1b051e061f12050c0303031009060e0c03070309031110140606030705120c0409061203020d0305060d02090c 76
    0x1001d4001b400b8410b68083c54108040e245503060050f08c0213881d0703034103504100e919810026804802d031803119894403180701c90740d100c005505002c0700030044004d00c0c13a84548044200941a0b1400345a0801c0c1d079403120301407101a250780300b4181da40c0700a0042c5140d0b40c0007501d4512206215900301c1a040c030080660341c042c000c00362a840d05100003003620b0201480e040204190507602041a5604030603185d066100500e03281c811001c4070101c6000e680c03104c0c1c0c4012207030700074800304001036440c4407402020f507039403030401c0c01c2d8003040d440e181e1140038910303418074400280a40344c42107018070400314002c4242ca5030383c909030120000d00200d2030842c24030420040f0099044003c00208040d049640c100003141c00012a402d40b50780c0e401407004c0e106880070401c00003034961140a032815041140120106034451007040c0d82180155000b000d05a40b9181002403d2849042d1040e4064000d402351101071101c0d01046003520b00c211403054002c00e24016070303c0181070000c402a40251846407160030b0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 990882338 1250 990881088 990881113
    0x30915130e0408070b0f1012060608011d120313111302041d010f0803070b100b030c0d0c080f060f0d0203011d071202030d03020a0e10051305090f1305 66
    0x41d4841038074195920f03100860702c00104000c0307030342e0b49801c80c0c4005401400742c546640c6804c2d0250080c0101c9980c499030500c07403030070011181c0000c000390503007400134810110809024180b18000115807071007440350031200e50350301814504882c002c004c803002000c00c001540c0c8441005492000750342d6008440341204032a45646880580003400c0d09054000018041e15240080f100060704142400304000804110b50103001040b51802c90303101c00c516a0a0792039680c14409031540f6407190f00c441d07100004020b034078100d24004040900164004101000405004a44100e01220f58009101b0032002007002450142c450040c100d00041058541405940c042800c3d511640112200c07200e0b81208801018002c1c0401c0c009041c0039074101e21000056000070740c0c0c030001600300406040c0d0000d4040d0f80d1500c0b80034014000c480152001c4003d004407600144141e0255998001c05110044045081d00d00520868068444040040c100341c4a5000303460307907201003034804ca4444c400d01c0d0140c40c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 990883588 1250 990882338 990882359
    0x506010203091005030604140105100c0804080a230c0d0201030e0f01111e2803090f0f05010510030f1e150209010e0409150506132c03091513 62
    0x1803c0304e0f6a21030300c0b81404010b00007070f59244400c800001a4140040c00152110203036590750350300d14034044100346c000e0b080940091107107410003980e40c02640400002d00c0303241c072403203134503803020b000e0403400c89a2401c000ca4030341e40d1003088107521103c0e801010700036611030b4205000911207502030303400324400d1500960031621075840703104d00d107000400c4010400180101d044002841500701c1461309480e1780e000c2a41004404c2c8a0700984c0d007150208651038400e03030240d024207134072032a451050611800c0031030400125417800c6440e0342c00d002c0041c1c08124501c0b1600100e07540f283d00b8611071411a0369070070b006000040748003c4081109034010100700349807004c0b400503131003500042c0d813800882c1c00102440762045115000c0c03418480a500069000e2891403444a27500f5400926511440000303181c0f41040042d00d0030b624201800e2410700310740c2445000d0500301e964510000c002c0000081c3d41c507805880042c0e0750024903150381c0d111403c0d040d40148010040d06113881d0310f160311210202e6 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 990884838 1250 990883588 990883609
    0x270702030c0318120c011b0c031a1602161815060f1814121c0e040b270a020415050a080f0c04090903210506010206071106010603050601020309 63
    0x1c500312540c001c5030a040c102400034134400101d880140605200b4940083c010990512011030040020074200040c440000041c07405154898079100c0c0106400c0301a9000711025a10304c4140102d00e214a50700b00e00028180c091303014440c180301c035550b01e800484880c09507108140e924968891b00248004445c0300d003600c4c00781c049500d4400d00c4007420b010013401410064074085d01d0300d803100d10500003d13050a44001d01820100c0e40d1421440c151401c0c217080892145102d00000b0721008030300300c0150081a03510f600c02e015201080000758010400080010401c142000e8124015400c3c85841c4601e81141e48040c643c1e0015152a0341e0301010101510b5122100d00000c9c070100b42c01b0200340d88091040d8100c21412951800d908144000c042c02d44107a00c01c055110f0b07a911040e608140c040c020070700000082203280c21000c01c2408443c80a00012111680140200c00010700d41c0e0b0702448060900285110013440142e080840c20350080202a101c141584400d101482482c3c1d1a00b0154 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 990886088 1250 990884838 990884857
    0x11011106040224070b1609090213090f09060606030519180f1a0702161e06030b0409080c010507020118050d08040c050d060f390507050a0605060f270702030c03 70
    0x1103a4090700c6d14001424206190044405240100b0034000103602d10110f450039904034440004020420b010b41ca0014004100c008110a080290005032160540e0142e0f2240302d001c07a0150b080c12003c800b4004480107801c1e064a52404050001c001c0b898120042d02c100d44186280880c10845407400c3c0e00030070040310600d0041c0d00200c220090307690030748007641c02072000c5501c04089480e609000400742d21680228810140d841c0c0d00c00f1200d5849400140c4040c0d04010270594400561282c640a01011114000958285034a82c903520f003003006942410794104010782000383c5001070449041002410a54005111034000308443d80e8110803d4900c910034280025103880c032400c404180c0300722111a6801208140207842281000640e268050380c0120010542040e008020f5455008044000c6c100f80b055600c4942001100d503c807d0007007000300d0b400b03200d00c2d540c4420001d15a0b10444411407003500d00a1901c65240c054610503003110250055074141120300071030074610340104000d07 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 990887338 1250 990886088 990886111
    0x30c030303150a12050a031103090415051e0a090504150e01020c010515030a08031308040f0906052b11120d090e010e071808060411011106040224070b 66
    0x42c1d1205240481c03a41c0c00400313045880b020001c030700361692501c1d500000000b030140610801c800140840c10300403030b00e203480001c2c0104002059880b49071b103102058003030716009116818482c55486c807000543c01503480d0041c103500380141000741c51406010080c004a034013140c030f81307004d800002306070003042c699030906000140c03035038101640c55007990307005420340c01e0719008180d900200e44c4012800c542101d400811090742c0f42c940c422940720743c541c1c070400a0802c00006c1004292003c41041b0f0100719411244240302031901da204001c24120820860301c4048045040c0b04c0e0707400c00300260401014010a801c03807500d43d8510101c1c40b0301c0b48160106035660032a825079500c40760400261000b90070201c02c4410030350b05103c0403e08104000d0441800e22910a41c148070314006054110003406650007074607800c1c20140b41040e01000710f642c21501150200030440814440000e032544aa90002d044040303040c441c0210950000c801c85109008020401500c00031804030700c1442d0250105506 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 990888588 1250 990887338 990887371
    0xa03121103300610050c0712030c03090602010c021f0b1801060f0e030c041805030f04060305060f01020601030209060111031c0b120a02190e0703090215040f030f02030c030303 77
    0x10802d00341d29000c000071219602c2c1d60140025500d81e0003505244075070030b09050795600c0418400514061240d40f0455010503145082000c05a0013080d844c032107882601d504006503100ca034142d0a030fa0000a000f40140c0c0041008028138480d06035000300e008145000080d5100c0090200307181010080e40014142c201e90300400a85500000100b000702ca06d24099020410090001e621084c1c081d42031403145488840e4074031801400c18040c0110350707008080706c1d07890021a4507102507401c2442502c011a1a100000d112414000802107603c10705901400c2143c1c2180d00300181700902500701c60401480d01c0c45c3c0c80503203004000800100001401c4550140e10388030550050f91541c00b5402d000746e01d20510164580000140361000680c1114400c1c00c05d40404003035618803120b41e0180c95141e00780000d00944a805510040c201c900944503894004c0030341c42c1e4840640b00d00c0c441c0d01041c2801450820224000e802c1c035160592000741981c1c910640f0000107440c68000762500c0000840500 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 990889838 1250 990888588 990888637
    0x120604031b11030a110f0109050906040203091c08060a050a151202040906090213060c020d0b060d0209040b0f0109050108030f030606070c0b0d14040809190e1303080903090a03121103 80
    0x204560031b44800f40303048080c150401e030100715003650141946001c0d64000c004a22042002e101d0000d856044c04004040201c020303000400d080f8040c0c5503a40641d00003a0301003400d00b0030301b00e0a000c1c1c0703500314a0b4260340021210200c2d000d02c81101035862081d4240400300e00030f03400780503903001880398040c056110b003003031105501c4407040c640c04001032020f81e005000058480320b00a410b4a03800042c08490fa5803060082a2100b101980c003d5000d210f5000f044100030400d140300f8024900c2454201081ea02c0d03c4040c0c085403401c0c0220036071a03200b480704400c400f40c072341c000350b61103000940b80c54241841d613560403a03c180940c2202c0110741c2c010031800c0401e00d961044800640c680b0841c5c3c0c2e004c3c1400d4481a4441c406d4280c0c29000b20b80110a0120201700240c10f0030003403034141d101400034034089607840445459070408900254130031001c20f01c2c000001069495000c0e00504003100585035aa4088000e80c0e01241007091000d02850103504030002d0001d00250710004846001ca2107241d13 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 990891088 1250 990889838 990889849
    0xd050f071211040203060a3f03080901090804141306090524060f0a031b020d03140f01060c0510020a2006070f0e060c0f0c120604031b11030a11 63
    0x41002c1e80c003407441803040280c150b543c0144041202e829403400000100c696407940114404c400009080d8503503040b45400d03076510f1301043c500c0035005c0c0e603420078240c990114060a07206a0500546540c800f40421300804044108006651074000c081100319601e4081c00720a0300c0c0d181d07128a00d030903035420402281c14200d42400c4100c0b942201e54180790420640040c0c0c041c029200f001c070014501152401001c0d00a0307004d25a10041c80c44240c9010030300000003543d515041e241c0d0b2f8002030620000c0305800480081c20303070041c16880c0c0300d4030141e82044c80c11140f079250031009490300c1c4603005510580d04c01910040c00c0d00c403d139644045000c040c40020341d129800b00450643c00b64411800c001c4085d50190351700520454500d81110000d00d0000010304601602403088141e004008003041501c01c0010321240b02c010903107110420302c1315003000c1c1d61141d4085401401041c01e00015510b481d09030008815050321070718900c1100440c51011914211003071074100c60740000c00c441d2a0031481c04 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 990892338 1250 990891088 990891113
    0xa02030106060206010b12071412070f0309020609090714070f0201020c0603010305100b0a050414061201020703020a0f030c1a1f050d032006040f0c080a110d050f0712 73
    0x30b5000402c544d5140540c00c950920520f0b01d078418a002810200f940d2512643c1405881e01c2510701e03142e00c0d4007951680c00f240660650340c03c0c01049120480c10705e40e80c068015400d007550014a0b0b10709002a81051050210000342407004000b02203140383c00d04014040940402170080310300360400720700c0f88006440c2030314880d4101d20402c0f044c001013000600005216102883c18140460310007006400b2881d60182c6030405903100d03090008000180030180440e0340300d03e00c111002c1c4625904581e04508038454841d0140050704030340c0a402c040341d480301c802e10b4603910130301e0b244c02400c080341c0302d04050500b14544032141c0500d10003840315003000c0c48101e14a00c0c15042903042d42e1071405e8005090011a10401428007403040140c24107220708900f0b1003540d10b416029650f20745000c3c6014007107031041000441d0241d94034100880c0c0d20400090202c00103500090b4000340002080400240000060007295244241314104a0000701409200c00a110008403445441d1041c80d242540d07001 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 990893588 1250 990892338 990892349
    0xb04080d14030610020c040509010c0e1014161502040905060102010c082a1201050315040201020a03120e011a040b091003020d080d09030207091103060a05060901020f0105090a02030106 81
    0x144025072100d41040422240c00c182e0480d0080b1380c0d0b1542040503070a11069809055101d480c010401c00315003819001a42c0d805650b565207003031842510100080d0002608040c4001806100010340401070580148190743d415100454003c1003036841d221240d0f50250040032041d00442c007003200c030314540102500028240000d100703140e40c030706004028074801040400080030781007039420506040d0060300480044298003699a040f000080c0031110310a21501e0700a1140101e444d0000f081e4403405801258140e0144c0a24485904c046070b20001050510f80070f16a26048808006400d204000c80c01400440100b9590406401c200848114040144c0600c962108114001319104a0321040d03a40c103c0e500404000780c1d0401e1541c83c01041ea101150074500f0403040300f4907400180c0c60341210580407051214400700e02031811580415582c094000e20702d808144050301c2d103040649511141841190125481c0001c218203499040d51140d88a41000c550b2106505080c09440081c00 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 990894838 1250 990893588 990893597
    0xe2703091003140a05180a050106060807090b0f070c0503060403020115081f0c02010b0d0f30031e110d050c03041a0406150303180801110405011d0a0b04080d 69
    0x2c441c81003c8280c2c100080c40600c070140d0b2240041c45580b07000643c2506206644115901c221451070840e008124074050a004a00018002000340c0c0c400c11a0905035a200c10415040c10403001c07000381160010f02003219101425031010609880800045105d54041c0c0c1c008034140484529012820540303802449094128882a9080762140083c1c50000f0580c1a00081c1d299107100f0200c0c01803d9880030310390f0104180d001c550038030216101202c5114010b14400040940c0d10100c00b00040d90000614032010310704000ca850b0320b001e9400148100d200c00f010004190911584804031000c007000101c8410002c0f030611841c446ca171240a82c002c0c2c09044151030741c01c090b100d000d2440c0440c245030703401c02c4010001804000c0c003500010308a1159000d0301c21450b81300c0c80c010303055101c60f40c440c1e802c001c4010b074001009030f014011304004420140100d8038150526004592400c00124180308075002c00784001c651f44c968040005c01070508009072500c42d0305080b6240d0030881c50000850810 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 990896088 1250 990894838 990894851
    0x2102160b130b0904060801061205010b010305041e0c090e030a090e011d0405010e0a120f0c0209181f060501110d1407060b031c0311030c040e2703091003 67
    0x1801286002070b00c801c1206030740c48106020000c0d020701060340002c441d6508054000500f0250f54400d124100d00c140f00034840e0000b070303000441c00c88100311805031400d181c420108455102d40c0701d030740780080d00918001e80c11540740c0c0030b91000d071211440010301c08d600000c0c0b03038804d6a6109107418041d10400403610001d51518034041e80d0f9140b00f00617a002903a59201040c2044000d60000f80104c2e500d0301551103040031414145100d81d80708103000f01045011303c4a6450a04c5400850820399004240741e0054030381c0160440340c1484410b94010318443d20165400002003629048065265041c02089440c01e1100041105502003022101075000c0c0c20620012a044179518504040c180769294607001281004400790800f0380444d905801445007480703448000d0700c52141498010340701400540094440c80725188004c0311406a004014802031218404080f1401d40160004540b0030718075424070710301440d00076130f2110020a540005013610040c00d040000d500c2511803030a081180 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 990897338 1250 990896088 990896107
    0x20f09071d03121209070306060e190e1e070f0315141003060b06070f0b01170d0e0f010c05070608040c050d110d02031f0e01111908042102160b 63
    0x440c040d90004c916082c0c0c0a00010b101d904081060000464004c20240500b5965400d028003120069a00701c0c80103904c0500d802c0341144502480484d482803400410309601041e5200d04070000c262040c0d034081c045d01c0000500c9070000070001c00554080d50007041c078540c161240710200c40081c486c00880b0100c010801c04280a0380c203c40c2c08690700048045041d82c902c0001590901c80c01d00000d00d041180c80000091100420259060343c48505285103030f501b400040540c1d82c0c1d0341600350030010f601260302111608101c00d604141003010704040c0c0b0031074501da440c5414044590802000614090200b00900a1181d0a03900030003042d80c1c03640f00c042c030310340b10140d614414030120341c0071300419420041191810401d6504000307152841240182209081201a200385c540c00c56040d0b0805407070502d5154030408545a124140d40c5100d43d0240700324003900e607140014800c1d04d034600440e0740b40d400710180c404028550040c5a0152a041020044801c100c0f0525001a2040c90f01400072500 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 990898588 1250 990897338 990897373
    0x42720040f1a0102010c2a140619060b0414040612051f05060a0303200304090c0201050f0f040b0403020a02030a0b0708090f0709020f1306020a0218040b040204020304020f09071d03 79
    0x41000444282d10f54107075417070006030880500860002e0aa040c0e180001400110118849001c3c82e14540b4ac5e21100c1c0c03e40880038241d400d6406491644141004100941909500004c0f4038000140012030302c40d50b105455035044080a2094429400404885400d28500c9803803055510f0781100c100900e08202c001304100100d140001010b1007005801200159140c4402401e9110088200c075500d42e100e101150151030b41003c08000342d030034800401d0f00050340500303051007050740115000380f40c0d4803500da1141e446009403013074042d030144882081c0036072400e200741c440560291480003114201900c0c01048824001c01240480c0c1242103070100c40240440d202c2c040302e01080700580c0b102c400c10f0420440344039000e886142c0c1c4040c064005205034002c100003000e140220ba6000c0c801c01291480c60302080e048034020802040100081d0040c03a16074040d541150000c0d00c00381c000280900401d802d400240c901c000802d07104010442400b824120821400d003060f0080c0603085070f4800078a0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 990899838 1250 990898588 990898607
    0x10e1e04050a080702061308100e010509060610110105070519020609060406150e040606030c05100509040c0311070f050c1c060c051303060209042720040f1a0102010c 73
    0x603c0180005400c1e01903580722002e440c581d207040d41100f2040e545e1a6440c0d90b6444d00141c421094600300f800381e8640c0038062103154840c60082d005445c813a5038560400c48299000100003050002a0002e0000440c00740f00c0e1510a801c1603c1d00b0f6510701102501e08018a030b440504411548030004028800401060f125001944041d003c00d04552004d0480308400c07054000302108900071041005101d542c5d00b01004a0380150703100030304507442c1e506202003040c541c1c00840c041041041002541c0c14582d1110600661615002480d0704009401609541c4800340030346407503004404100a1140501c001040d0007000c441c00010410852200241034001c2880640425a6074004c036005a01580440c0c4154124000e180000d41c3c03240b82180c02508812540c90040b40b40c5842d40c08007081d204281e03e504e1101400c245102c0c0600d985280c0c0803415401ca4450707015203600ea503191034440340955059031040307201c00314a00e914803541c5954028954035550440e8103101500a00540164641 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 990901088 1250 990899838 990899843
    0x1f060c02150d0e0c0f10050a050c010204050d12021006060903290405070e0c09011d030106170f1002120103030807210b0306061206060607020a03060203010e1e04050a 73
    0xc441c1200c162100350160b0042002d8400c159041c00142156034901051001c080d4004540d640d01c2c07543c1007001d000410240c0500356000c070300e080150340700700350141000e0880011210009480c040c0c940c07020501002c1f406108035640201a0700440d14a601440340380307113010318140100441460010000c3c40c070011444060f00c40409001040d4036034046214034100c80ca50041d420100e81071030301d40705a46040b00d100d040f4401c00d41102158034800804100d64130b2120594903120f11403070116064400290740c12480d989507503103e07400034622081d03400314180d80c42c16901410110703e00e200c48500f403502c1106185041441003103a03000700616081c0340c9042d02c4d018580036003540d50384e002c2a44d0788584c1c880c0d4100d4510720441c00d0098041503802c40320100c0b50030f6007500d20302c0d125902801095000720246d480760750804000038890742000d02c003824103e8001040188295500e850360801ca0b8002e03006001c24420603401c100d4085d695120303828208158821103141890039440f510780f0b0ba5080d4100 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 990902338 1250 990901088 990901099
    0x301050103020a141209100b0102060712090b09010e011505030d2303040503042301021015030c03140c0d08070605070e270901180b0714030109051f060c02 68
    0x40501203441035a0142c130340d212418082c0d41e41c0041d4810036064040417580284584240750708403e28142c140590380ca28401a001006141c856000a0307a500ea004801043c944d0355aa43c11008140303050b10700b038091550940002a02c0d070209170700d41c5c25100d140b0802a03c00c2d40c0031b207040289480003c2c5142d440d00d528600b004110b008444081c3c5c0010b4040416003010f0008014807007401000301c0180300311901e0440350260036850313103803c1040c0340400074010b0158120341c1203003206001c0364100c030584040b080e4989549940300e0f60703110246907050f0820390f40804100d0800130350780c108105216000300c0031180301204424960742c1c48072501c19204024112500c2d40c011401050060f0113030b17224598010141590420901d0341c03440b41515252910358151403481c040340c41040b062151a00021043c8a01040850b103900c8000c9031900180c05070080180c1c001c13040300070b24519006940600450b650100341c0341804e0492242c65019101d207980340e100c4645040101d140c0003c80b040c49191305445 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 990903588 1250 990902338 990902347
    0xa090c0203120a0e0c09040b0f040c080109080301091a100e01031d0c011d030307172104031e050a120e160f080a120c060e1c03140c030105010302 64
    0x2012415800303000c1c507400c02284102c0a00c91229595040380c264502d10804590009104004000780414140d80107848407200c400400c03010400b051500d54800e00419000d280d1564580e032480c21640110426640041e0120050180c41c2003070142d607031203000380c0c5c06101c42c01c0c0302400003441c00c401801d000c1080c040460784141e0140d0103500803110300705041c5404046024034001d41c0740c5070069500c2031400580030f20b0f00104002c420300100c86170110060002d5042000c10b07035484209500d00f041e000c003428802e10025161540d4041488590b00310341400c40e01c242054034001c4e11041019402c03441902d01c403040d9007071659200041e1070042040f854036a5050078005100d00040c46d06184002960041c40c3c004484200840311402c215428154815542c5036155807a544031880c0c0724008281c6029503640e90060307442451002806801034000144004400c14124070f000b400300703000c10111009481004441c1e400d441640406040c441140c2c030705180130f413030000345440705015881c185a408079 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 990904838 1250 990903588 990903611
    0x81509010b030a29090c060702030c060c0708060c0a0c0f11040f02041401031b0305041a10060f03050405120c011d061501050a020a08030c0c0a11010906020c0a09 71
    0x400516900340054191001d5030b44034140200c144507142009222003403020701d0300c401c0344010006244100d074100d020744101c06d00c46040040e16408004260b901d44100702e000301840e90750400406040b1002030080800c585418144c50801000a20703502403c0c00c2441001c1107150818100c4c00603d40c0401c5000c080340b16031400c4442c3d031140100c0b040e000703882d00a0b81551010341d0750061090b24a000189500d01482d01e00440640380c18042007581d07209800c500e150040d0081d0041c5402610400142c2d0b003200e085510469021740450b8000b80d12012510708110076900400641012011450107001034030705038440c247e4505011801c80003001c000140307140914000e5100750408a0b65500343c0280346600c103e803d0381e64105840c24403954041139190080e640c002e5040700d03241061354016201040c11516200e070756030070003004040c8074041000201e884040c2403000001040c4510f55250580003a80b000521542c4d09800110a550288081511907a1000b0140d070407583c1d0501e000c1625080074 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 990906088 1250 990904838 990904841
    0x2115180f150402160510050630120d020a0801052b03031805071401030203010e0c0306010e100534060504080918011805070504060c03020109080a030b04050a0608150901 74
    0x1050b22880a9105184004c00c120300843c028000100b550424042500e8180c1080381c0c1c000614400b424030074071660104228403007140555840140d00c000e4074420084821004915401010300d0f0300c1240d4001504c254050b004a00c1d1800342c281a00c00210500c01940d0010721450a4041c1c036100724052000c54040510a42020701400c08110036000314060f1071038001d1f62a034041c000da40032681800302c1c141c1039501c640300340d0341250017000b801c2d2402e8442101c030f086141d001a120604120101800c0e2804c1e89498243d64202d0410f03640f510307030710710509280c200040840c901d0070701015038851507101124451200c101c24103405c001c0001c3c039500d5500d01010b00e0303c9090300f015001000c0611482c1d003032104040080c12640b42c0710103040700088601d140405c40d20222003c2004c01c00c01d000502005208658100e0305c54030070700001501c2d100715101d00400b50420024100000d40314295107846013030501600350002c1103008148007441c20300c450740c0e072075600381d11043e541c03207504034005071404409 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 990907338 1250 990906088 990906097
    0x1508042d0b1f081501080d050729010f0e060d020f010e0d1401020408061302010c11210c03010b03010212010e0c1603021e0a12052115180f150402 64
    0x202c0107880c06a565029903640721a0030b01c0c00d400f60240310b50300000e0b00290110300c60a9400301c07903407407500c0c200700340d5100076122949581c43d00204030b108410300b142100d10b00c00036010f410191176901010b8a0302611381940700e001080c00d03000705d44c01010302d07006880c2c030b08042e0100b400c2403c00003040e00390711011490207140341d0780c040c104010340101c030260b23070b1810340c010000d903404102660056940d00610301500307259070900a00281601080d980441d040510765410000700038407003d40d292040340b03103101d0611000c0030300740a500300c504104490300e002d00c10511958000d400075410100050245210200f05201c0d9805020343c2400083d03d400c0c074003003100c5551030540f0600b00100200c3c103000390744503400b502c43c01b04100700f000203580c51940007510100741540543d08204c0000310840c00c40340351b04426020701c1a541e1491712148145880010544904801c6d18904c4480c1c00c1001007080d900400c2c5d2099503070003840b0041c00219015600c00e075601c083d07041c000110780c00d2481c0129000780b25 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 990908588 1250 990907338 990907381
    0x1802010f030b131b0e1e1005091f021e0616020a02030d030603020a050604140f060415080910050f0a0b030a0c03150b0405012303071508042d0b 63
    0x2034103280b508148404800300c00c49034510365a0b0b1455000c144c060082d50080020300a46c0d918540d00810324510780034008442400452030854200700c07002001c10ba1207902e20b0101c1e02101c80190455075810780c100300c0e01c461401d030700c00c11101d000401218503032115005440001c400f1140c03480040924000c10408038696800303022180c5182515800400170840b6000480c810503058000081d10f1404100392001e548400c5003007a203c2c45d0040130020ba115034031210300c2d00407030244800a207003103460583c081c4e45006a1200c1c48a0300d40b080d00d0702e0502c003802d00c22160181c42d1030144802202100c134141d50096820400103164903d2000003450400081001086d22003400b5010080141c4e000500c43c459200007418001440c260b800c020983d5024081c064004044d2040070820088407420301d00c05a5014059038503480c0c07148004441d42c12482031842c04110807106000c10408011800f0503000e06004034030f01110400c14070545141e40840c4e01400c42801c40340819411410b2000c5c010301c884 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 990909838 1250 990908588 990908591
    0xc060a0318080a050a03050c0a1b0f0b1005120601030b0c0a02010608030a031b020105190b0a0302130203070f0809030f0a0e0301060f0518190c020712050a061802010f030b13 76
    0xf0010402091035004506500000c0d091002280041c84042c00f95460b1501070340f90b2211441b90780b80700d00da43c807107811410f80d14100c200b003680010452015540b07002d15800c0c0c080034041c0b803c1030107205555903c540340501c41d03400000100f002c21051811036400400c5000b10b15540c08014100324003400458102000c9800b00085400303000e60940c2c04888810080241c00354140107816041e1308a80d0100da4500d03180000d1024004001c0080e0312003450700c08014511660691030350045290949842c2808200307540c00410302c20030940000c0404410b424038589600149401d144054490240c100880b600140204030408414020009402d100c10061f00820910741c1e1501d030744004200c1403081030300406100e102d60480d035403d00101c0344114a241110360070801e0001e0001e006012860340c820450003440400326200c21a244416a254006d000510306402181000801c840350030102c103404c0d04051000f200140d800001c03042c2050b4003420001000d035404030204800c2c0c00544200200d46 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 990911088 1250 990909838 990909847
    0x30304030f051c031a1f140c1002040302011e0507020103020d0207050f390609010203040f0611010f0614091803070503131203021011070b010320030c060a031808 71
    0x144e505030702a020f03414a0701c141c02c0f81041010203004c1c106944d9101c60071140c10440030107601600901d0501000b600065001d480e0810301c200043c00c000c0300e00000034140e50006401c20542d030b80000b0b014154a0360202e00440840f80380e00c00303017841c862014001c5c1410340200300d44e6041c1e403060b410b448150360440c066822041c40031003100d4a5203031880320680400a1901d06c19501b264031140c51301c041d04c007100c040e006c0310b03c1c040820031650008104203045100400c00400d601800070a0f80c002040507843e81c1d5014030403d20902c1c2901c100110303030300c1c88620380002001840b03401d1032a40c41d101801d590428a071f455011800355102c40007003589072680700c00143d444c10032000200078484030952001e0008039503103c200081d0040750394203010340141c0c400d020300340001c070b00f40e80801403501e2407d6260b8a0700501d60f4403050580d000b6802544c1d0f00c151030740d440700315142c8850180100740040303016000f10101400007270014040c4020102c1050380d02d01c00c0344040b02d006a000340c18240c1100340a80c84 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 990912338 1250 990911088 990911143
    0x103030c17091e040f021308010b091b0c070b18010206011e03120e030109060f151a0702010c0f0f0302121c0b1f0306081b030304030f05 60
    0x800c031000504480716204041c4032011540c90074107030703041490020100b58a80b07011040316080c8501c24842c040d4042d075140300c040d0039060548000c00d09000c2c45605403080310315101c0c159007107604c00d2400b00d0258400c1410018212880002e4401d0000852070043d01e0307014030b14500d4600503a50300308007080200021210000014a042000550400d07800c440a580c1c80d0f0b000724907001250a401640411002c00910000d1031001d00e04001c4480b903e400600091210002400e40d004000d00f0389106641d54032580da100302a020b05c440b03043c00785182420141c075200500c00300302a0300b1960300e20400c001c03403520110ba01c601d010b00b4480d070300146482461f60540c1002150540203040440c058451487c006410102550aa4803444404c44d6507a402d00c10031040c101c0500759507401954840398403101a082400070002c440040092039400094040c10030b14414544141c41d1240c50b05040c211403030520541d00001201c06595100141038000c8401d07180491411440d0511001d0480c0030b000d1090700b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 990913588 1250 990912338 990912347
    0xa0b0a0e01090f0204080c06030c0d140711060708041106040b0f121b0a0e0406082508010209030a060c05160f050c04050c0909040221160609060207151403010303 71
    0x165599102d00f040f4035849081100104d1190f48109440354104859a24052501502a550120b5030384042440c2107100c1d00c4ac02e0485031100d007150707100b00c10807003404007a0394041c241c0c03d00608000010715440c100031710090220400100300802e0401d5a400c065180d03181c02e01500c00414510319041d444503004542081950401c50003003a0b021507100025543d0007201694041480d042c0107018a003040410b021a081050030f0b1455030002c0e1588000900d5800804c281c869459416041c4040caa17400041c99151002a41c0900140c2c0c0c010f21056132070342c0e0f02190001010341c1c420340001d003010074912b00741c441d40251a9810b4888840031030346c006006007030f40da180c4c4030380c4500c0c103660365407481600b00400c0780c00c25a404103031803206020140c1c80b0304001c0c03440380c2c10a0004000c2e21111501c01450b01f402c45d0800f1503c003d0380c02c620b00e020718510112914001500b028141140424241040251398903c64031070003203403201030740115200c640204030b108407403200304120300ea80b50f1b141d08020b030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 990914838 1250 990913588 990913591
    0xe2b0c0f0b0c1b011b02162c01030b040302010b040b03030a080919050307050708060c0405040b04090803070507020f0a0302240f0f0c0d03062138010b0304080904050a0b0a0e 76
    0x21107026140900800b01781c4089200c400c1c0400a4078503c0901e800d00f980300c00c4104403512230710303049280d03c0c640c41a20300000301110300a6100d07000c0c006e08c80c5054a40203003507480181c540781c061403c2011f4034080f55404016110b0601e5186000072103030b6600c20f089840c00c840c0e950340903031107212040510180308011005040e594001c1c412143c0300e0b80d0f00c01070709643e484211151140c004c01408284005d00d02a042140c3c0010010804a86a0103035120103005910030b40d1400f0100d900080d901d001c6042445010b8804481140c1c0d2001c40ca1958002c2072080c0107000350b107101c242441440001080410082d02c1c204001d0302d03200f527114501c1201606080c2d10144d4290020710031910088610781c881d01400c0e080e83e200a000c0450780000d10048040240b80b00c2044640a02d0b01011040000c555010102510050204101610b81d003c0d41701a0f0000c041e040812815410000c01010508402c122840c0500584001a00d070341e07074140f00002880101003269002d046d1580004000501c0c00285 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 990916088 1250 990914838 990914861
    0x2090c0c06011d1303032310050f060706020901020a05300913020a021f05010311031c30060602010b040603020a050f040e2b0c0f0b0c1b01 61
    0x25000c03640c0fa28000e440d20341e4009000c00701100120002440140d800108010040c0310f400c021400d0741803842c5550030030103111110910f00c41c541d4104600504218103101c018581038584501c4042c0c0640410310b10700c160b85000c0c1005c1c2e00001d2486441e4800c103c44510700c0e8101060368411022418500f0380140b1400340911031000c0900c400c1c0c1c410b10900111240d500e4000c0598800800401c1400c0c0607400258580e030960141c13880c0b032030006880e1300001a4006100d1030000e8a5030441c40c4c0000780003031381c85602e0701a5004c0d060b100f117001c008540d02c2c4041031007801c080d0030092405002c1410b10004400001d101c0000508901a4480640040041d120303d60020b0018181d0081403004540700c510004c1d61241ca0001c00304103500302244400c1480c50040c00c0415903440741403806207003009007417030140560600a000e070305181c00e5034070204e400b425078509007154100300c4e100c4604042d040c4c034010300600441004158601d40360000c50f401428401c200611107500b00c030400e8024000310b0b810 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 990917338 1250 990916088 990916093
    0x120c181f08010e0f1603110c10060f0303080f090106030f050606040b030d020a03050f071b03030f0302030105060a120902041514031203010e040309030501090c0603140c04051002070302090c0c 84
    0x200b1103c540390341280c4650a444580c22003503403200c1c820170241000000050905540f1016500c512441030010101348003070b40f0080032611078044c04e250446101d6403062415084684003400000d6100c14402e0700040d010700d14044039241c50785010300404507503000404207a0900e084100300800030503140e201342d404407401c00c401d020b154107058640c44130018410040e0000c04481000900501c060101d04103041078503424038515695400001c0410380c00200c18074000c18003082015446005000c802150307240a605551402002c500b05004c1c250208051020006018450344450791216103c0c907002001809032081c5100342013100c0300540100504004480c4800060341030001c0c48486403006a020285140c0c40e100e48101c000002520407020440300010001c08135409000c0d0006203800b8031200b100d01c1d450070341c0103070441e0303000007085801c80c40c3c00b001c0028040e001d00680d0100c50041c1c1d044c94078021229000c80c200001c0790402548628006d041c0605c601101000e032205901c420b04 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 990918588 1250 990917338 990917341
    0x1806050a051e0c0c0703020d050604170717030604180b10061704020108100905010f141002060114010522140a0e011206020403120206060312120c181f08 67
    0x4a44110b0088440c205440c80000c00c04601c01100700d0005003410f00700041a42e1401e51240e00240f8000c032141010348041d80304406010502508100c1d0201a1a101520310300c1c110460340c0c2c0d0f03e07064008601c058940f201c013100086503a01c40e5080600c1d00041d0090b103101c240380504c3e01900d0000191160072040c0f4003850041082c600070f082c107000904850007004026900c0354011541440010000d4000340380d61540000d0b40310b0580500340c06004c0c0b00030004803160070020449201598501d949100d4200c9038074844400380c01142c0c050540e2480320f8503440440d101c00061314140b0809031401307214503164010445050502000d0b005550061110f40c449000100c10450000b13503500420310003812400041018200c14c403849003000780b02d07410143c10542d0769121200841510f032042c0000d07811103400c003d0245802c5c403050340c40010b035007a501e04000f103000c59000205001410702080f80700010b10700c81c0c0c0c80e2044441980850300142844d86003010030880403041c0745c0d00188440030442010 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 990919838 1250 990918588 990918601
    0x51903170d291801030204020307030e0a0c092d050705090303041e0915060c420c09061d03030304082115010806040b04050108070302011d010e010f031806050a05 71
    0x45008101e0340e088403e10781e9003076800700802940054030020606544030941580c40c841400503040c0640544d102a07a240d00d000760380d0007940d0302d1400c4052250348095084500051240500c50402c4140da030004069030342041c1030301c1500c2028102c584c90700c4041800610031400c90107025802e0303041804508116070361442131040d2000360204000c02d07080c0203418020288103041d00070611b409481c81a40300705c55000c80c1400341c0d40d1071404021901c0c0c020641845c04034143c000b9040ca005000702003251040b0b0240051004a090003900e0801260700525400c40d82600c3e104140500000c007aa9500d041515080c1410b50007040b6902004d000001e00741903800b201c1e20014880e0b40c1420f40307600288a220011145048010411540141c0d03038680e503540c640f914030600b4044d1040b000201030041c25800050702034a5840aa8189a00521005127299034000307510144004e007030a142c003610003504401d0f000b504490032030540d440301011150b8148000740c2c00c0303140260031200c0d0401150b2140d0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 990921088 1250 990919838 990919849
    0x1a180f06040804050108040303090803011d06100504050415090c020105090f1c0f05070f05030c120717090109091e06080102120718030822051903170d29 67
    0x11140034160b0601480104559400344901c190303c58440d00e0001800c424a68031000c55030000c5e000740d40c122185000300c00400c0e0501e002250000403c69144039008220f510080c00c92046000300c030700450f00c0700b2160075201d082d500240040c109002c0d003070102007104880240204012074a40740d6503c0b0710700342b0103004000410280c502034a1400c48500d100c40e40d02c01526125042061710007000360070041c90f40418a81403144140038802c1003d07640c0c840c00490014a810038600006401580400034200014a96150310340d4000180c15202d444141e00720050307900c50350540c403640507141031880c9a0342084003540408409440e40c2d1003004540d031501d00183c00c0b401400c420801000701c03603010803801070003041d07a148818182c01c0c281d004c2c280c4036928425242c02c040c0c0c025801e14094a64144000c0c013841c072800c00340c034060790a64450080780c4541c803085102840050407100080b030325902051f0380001262070512003e0024805689450320300080b1054501e03034440d1100c1c004103070b107001d03140c203 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 990922338 1250 990921088 990921091
    0x80c061308030106031503120c032303180c0901330e12030913020301030b01090c090b0a03140702030304032c0f0402040905070c11010311070f1a180f06 67
    0x1c1d0307290541c2e0900c80150003d0012030045860024008000000118000e46d140d012301260754460050002c0c504d0701030800c0350b10114480c1c2c041c1e0b108100203041000041520303400748160082e144c09001ca00d030103070b0611040f0344079640c1125030b140001c5221400807032220900e0510210a4031070b50031550900d081000e41000031030020f684ca5100345103529000c183d4110200c00c0c10162441e0504500020b41d117140072484440ea01e0b80c010004006104814208500600c15000c050122a15450000305583c505010300b115200001c505101804e1081e441407410f4603030300d480c031342c80b5041070103001c1d64039001184c040300040c1c04450001030106ea882c0b182c2c07016001c002d10322500c640001c01041942d402007203085801075400e0000080d2004140500c5000342c0c0e2036200d036080b1a60504040006100b160301e10750616003415070708240384150008a0f0002604035100020f41051494401c80b501e6a50540701c40c007000711424019403d5000008010011010003100c0d03600224059aa0701d5610 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 990923588 1250 990922338 990922343
    0x70f030b1309210e031212010e0c0d0603030e0f03010b100c0317100f0803030c090d151a030d0809070e040804090e1006050d230a020d080c0613 63
    0x3075003a9160303a80ca035400c0195002c0c801c40105141c03048000c808125064007051080024640303c1c2c2201e1346007818000f01554014109a8a2402d4414141d9415940c0184201002500c00c840000c100d20f01000030b54080c01f41d507140c240170050f582d050040c02c070304484052500c14031015000c0c60031403405203e03010030641c0140c540340000e100650291075419038443c090f0240b001c80c5003030f0382080d5032940c40d5902c1004260300c0040002d060407007400d000e101c3d60b0000c00965208106001580c00c100c01070b555014030446801b10215400d2412101c1c1850402640303410381c1c1006142105040c8514400e000c002c815411680e198468180485582000f40c41d00e08051b0003020f800e11202901c0d9011031b6005001e0b6004620745039503800800211040c8a10350609070700128581c01010800f80180001403034103c40710054800d170fa8031042001c1d8a10a81c65918a03050000143c1000050040c2c10354140c0040c00c540b1007030028140000300c0e91004114a03850b010300000100d45c0d070025288100d010b40c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 990924838 1250 990923588 990923599
    0xf08070f090e12160212060f090303010806011e0315050f09030a120525110d080708070f02071e05040b040c020a06050a15080307060506010e0f0d0606050a0e070f030b 73
    0x5503400701c0e100f003a50200b45400400308254011001503102c00648001c0c801c01c802c014005440c054103a11855000640f85540071b400400c010404400c00180e1281034501424410a00219044154620341d8455000400611407584481a41c1180b5801035105280304035602e4440d40d2644403140d00c80c4a106481c001040340c540680500011592004d40e010566141c60b81001c280e0702d1030034503240c4071a20840c0c000380c550030f505100c0c0c000520542c004006182885001c6007012039000d0698000141001c040150305120b8074200c520802c01c410040c40d403001005d42c00b071040f452000c0015040e00500740514201940d0b500c1074281071003500f1000129a000d00380e8500ca035601c0b040a07141c00313402c0c4004141c40c0c8500401d07d90301d40d41c0480081826100443da0b4403414075281007510801000306e030500c2401042e83c2d840340c0b594600c003280e000c821955014010355500d8204002c0c5a16004140c2001e00c115000c20b8043c50440d02900940f540e80702e4500009401d44120169900303407007030030f4011 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 990926088 1250 990924838 990924853
    0x108061f08060d0605040c03030e043c02040b0d0608060c0a05030c1e0306010f1107090f02040b181903030509100c0f08091c0b07050a090f08070f090e 66
    0x65104107551a04a28000c2000d2014401c0e03403038500c180c600c141c50039918480203907070400c10560444654804c41e8810342e0244443d600300e04c400b071081503510440900c0015100d0360b003108848011000480c05907148011900d503903c0c0c10860303129800204448043c0c41ca486000314030600009959882a500b00071424500200008c0c200e44580010b40040d0b801e140c02e20140041c02440130f8101d0072007184489564a9140c10000108401940c546c1c0d43c05103d4110f090320f9060101085071010f480b0719803804214900d80224100091080380c5c06407901c0500400c42c8000d01d40b556980804807001168007c030b00000301400d00400c600e25102c002c01055041102810701e091810a0301030761081402d00101c0c41d580351311040c10b06e110111084403189800204007540707140c04d014001c8201040301172801c204005541c0ca001c4528050302900600001007103186040740700780d8101c1c001d4158040f034030440e59a80c0c0c3e40d0569a60781405084140015400086460200ca2003200c2e4005564801040346 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 990927338 1250 990926088 990926149
    0xc140102162601020d05041a0402030604030e0324010501030606021c032d0603020a0602121617070c030c060e010f0c06381f03230114010806 62
    0x2c0c080168103041c184180d4400100254081c8043c01205428000c00b092502d0306107030811b00c80d08106104a4094244410720000d03031400183d25611540c0350418080c50841c420000c0d180900c032410743c0641c022080c1e292030460f8002a00c060484800b80c80034804a80c440304103a0300d0702c5501e20f1507407095111484031420a40f00342c02923005880e02203510b40403411031120002583e81c5482460001644444c41002141802c854100c02403203d88003901d0401c8000c240c90800e4480d803144a038050f100720300303042c003800780c00401c03c0c2c401c181e0b103002c16964404525081c8080c070320301c0c07200356040c00c03c2100c0000e900380503090003480b144059442c00c040103450344003038649509510781501c0f0243e54440b0048a082100c03d48038a420b004410768802c00004258100c00768035610707550740562801d210461801e20310604075200384000c0c0c2070200b0341e0b40e00030340940c00004802e0b85a40c40028800000038442c44201c85080c400102a42c60500ba40e50350300500208900413100e080070188101e544101 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 990928588 1250 990927338 990927359
    0x203060c13030c24080c0a05030c040906030b24010e10030b09090a1106070f080a110d080a0c090e1b04090c090815060d02060a1205040c14010216 64
    0x10341001c400d103900307000340d00d80d2140d6100b20342540020032440d12503c0107407812036030300c00055560282450140e600b89880c2d04602050302480e0303071110500ca00400414100141e400c241c80160000c0c120400103641e8900b480103614034261100c540840001c240c4104110a44051441703c07401a1105406601d002c000d1056200b08a991403040560b900d0071290b035607031041026401f40c4007080090011a80368100001c5010109074141e1182c641045441c0001b401c600070b500d00c0f83c4c3c00c0403085442e01c0c1011410340f81d00090030b00043d082d0060250280b00181c000101c5401a40e900404004641c2440d80c1515056a41c1c01040070b004211030016802c032074010000e028402510b0440c50520b542c03403101c0806c1d10f0340882c040e00452005082403003058002c1081c0d501e480703644c0c0000c40c90750a040011601c4542c055001030b005100028621151302e01641d0010041c035501c0c1c408000034a85418104009060f42c0680c50180e036003510000e440c2d6100043c411607010441c02682c452a180804a00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 990929838 1250 990928588 990928597
    0x5090702010e07030302030d060b1c20040915050906150903010e1c0e15070b040c2403110c07140d0f0b0a0b1c0b06040609060801090b0601020a0203060c 67
    0x14210340d00c1e0b40b580305000d40c040c000c42c4000c5209400442d00d0304003c401c910191001d60704100030280061051035030307a00d03080e9407400c801c2410301000100d50301c104080c1c036401c00c002120b00d042d4a1002800280c4e1301e21075413040c80208075440070a401e1a8842c01000644e0744140c501c640d000c4e0841c441c0e030f00c10f5041da100408034030f400100001068503d012506040203051141284012011000c1c844410703048668604640030494038852941c000d00107403511801490030181c441c101c10340000303007080112809140500b440304001c8000a4003030483d01d2008240d1171420f0002030405003000c007215801c0c0c1c20b071521080c000001c1c00626082490341d003d41150828441c6c1d01810052045011901c8149901403050003010312003030500d8541c3e00003056880c808642e0740140b50075041d40f039140c1d0f881006110713004d511854118541d150500080d0103490243c01c8132409900e0403c0000380d1420552204508512804503040300703551b42801640c4403032003180f0203034241d009617002a148003400c80080 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 990931088 1250 990929838 990929851
    0x3030509041a0301230604050702030d0c090b0d0903020124050d050a0b0c0a26010608100f1403211b030c0601170c0301092d080708070b010f050a0509 66
    0x6000c0055003000107405d490307040c02110030699642500260001030060f60561055013582c052019080c2000001d607203104055100d410a40c0d04c11400080b40d11902ca0b4030014040501c08645031135900f0200301c01085000011009980f80c068104020044007030001c403055014034175080d0451030070781401040002ca100c111082e0296084120025202078413944c01641040006601c4104130003010b400600c0d00b070141403001c0b003501300000315861b045501c0c07815100280740c202141d450701c81d140da54441840d0004c0d0861104400e0105548000310303015000700300c0407802c450715101071514102d45500018003100d0700010030012204580700f8800140d5140901070b007140d1030210310214003030808900381c000c1001d10803030140200c215003082000490781d0400b20000c03c070004540e50342d260650310380a040401078040e141c40d05840280440e04080840d0015110343c1e4036102c034540741415606c662411203d052080d03002164070351440f20020240d41c0041c003214074207804c00040040c0d20100070300e003 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 990932338 1250 990931088 990931121
    0x50a061209051203011806050f012a29010f0603050606040902070507090e030a0e1e030709050703150609180b0d0b07021c090e0702071d071202040303050904 69
    0xc00e8002030b0204140c00e44140003401d060740b60350401200021110300c0b0444101c038141844028030041c0e84001513451040001d0070034a181c1111480c101e540e4144400205221007050141007090009043c2190001391104d2403003140c030b40c0c400f1520419a0f00a01442859000d8410300303006c1c05005e039000e545c00c500c00505440c02e00ea034400c0c0c1d45040e60b05c0b010b0200d400b900409020485036460f4003a0915011074100030b10b041010084004004414500d0030900c0b0390702c214803008400350850381e0001684400b030155106141ca4135100c0c0c014003c19540c440020b850711110714001000304085400350350255440403040c1d4504101c103180c1c002c1c500c002685055490030f50505030354490501e001c180b4031510b0200c140346003c4101909110307442c690b107007040c000074140003480c680c044107038000d072003040411a0383c90719144001c03460910740b41c02070714844100111444031042e00c82d001d64031a04c0240c0c1c401c103800c80d60035820000ea000e2888010041082800203039414582504481020007280b02c5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 990933588 1250 990932338 990932351
    0x20d021903031b0507063603110d030605090106080915060609100201090b01050415030224040e1b04060e0913120306091b0906110a06060608070f09050a0612 69
    0x200100f2500451201201068000803c8010000c05024500307a03240d00000e0780d014004010841c608021140c1c0c40111240d0610040200b09030042c0718540510382200105c2d03460b144c010310045c009082901400e88a00201400000e590744169a5540b00b00041009003042a0101c142040e50070310213440386034009028081c00030b02e5210174100d55010b9070280c1c000f2501c14a103040c200d01144040c1c001501450800080c1003101010b45080c00c126030b419240441000c11211214060507013250156100035000500001da405060084500905094045601c1c2c0315000e00c624005108600c0380c0c00200f02620701c00640303860010b82c0c0543c0820707100b421200c4802c1564035044004102e04c4444046a41d480040c06415042d2050a4040c1500d10726020180340416000d0a2030708507124060801808060b4961107403014010054400d50085090103941d444410290100008542400000311084440004240b0070002c1c01c044880140442c0d480070304181089407414010100e07802c44035110030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 990934838 1250 990933588 990933611
    0xb15160f03080f132301060302060d0507120b100c0201110d052d0d0c120f0c11031812121b120f03010e060d0803040605070906020d02190303 62
    0x803401851090b07458400e24079156458030034034000a04410f010020803e2a180015403406600c01708140e000d003100705462003007036a43e014008640000f500481701040ea42240c0d400c64001070300403a000d0302c492111203c030b50350a40468402e4000b195000c0202200e0036591405142c00454043c01850a10340b01201c21144500e01038030a1405000070354000390018640c4201408250042c202e480300c406032444112541c1d202e8000c4104441101c3c1d602c460000d50b035402502ca1032920001c0400c20301c0380301110030040006040302040040404ca85500400c3c40b540e0200480da440c000c18580c2e5415490740e90144240500065a0841148180d40d4143c01441180c80500305860001e94041c074140500b4a00038180000c0c1940707016070020500200c9a01d0310404103480c1503800380ea043c0010342ea19072001612800060f0400740160740d0010170301c010b000300c0e604800d1040c40075440311901295100012603480912247d000010f802c226480000034159008000c01203019240200c0c4121115 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 990936088 1250 990934838 990934853
    0xb0f01020d050f1c2a0c05150709080d08010e010e0603101a041406031501030b010b07020604090507080717090a030503040c05040e24132604090608010b040b1516 71
    0x20040c90105c2049101c81444055003001c042c10b00b04403a00c0c0030b0305000c90640d40c890766a540e40744000c03140185200060615440b5102d500010418074084440841d2000303800b0381168000c0c050310815100d0b50001040024070150450b015510140c014207000441c0140e21004051381280c1028414060303a226915075114014100d100305076245070b00090415808140c600f2454030700d0448218490001000440d0321841018112006892035a0307803400c003803001681ca44103c0d00406001d514003000d000e80705611031219440341c0c400e5116601c00740d1800e0b103040c1501c80200c0303540c41e00f54000350651000a100e880990b401c01e1103071102404090302d400000d8207032002042c448000e41d01c0000c2d0b0307101640e41e00b96140118910078003029042d051500c40d03800501507010f40030700807040002200000003100d0508441c1e0122a00c1c031a900c454a550071203000e0401c600c62000590300b421401009442d041c400d0302d1401e400140040301360000c01b4a06000341d00304900c40c0c18907480c104040f00120380705 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 990937338 1250 990936088 990936101
    0x3040203120c0c1807080f07170403120b1f0c0c05030316120f0c0326010f05041103010f03020118030c09020d06082103090c0307090b0f01020d050f1c 66
    0x202c4014054420490003031044200e000008010580d09500a1042003504428495000341c0d0800010304680c0d28070105440b00c01c100200006000700f84010001410f40c045000304514111540a0101158050130030900f03086003003101801c150110034082e4544d0251184040703640c82107000780b8000e6900c0c030010b400c6411886901425840c0540c903002040f110404460000400d800d141421070100c1c00700506440c041400101032111031400700c51007120300c2d01007602c01c5440100c2040ea540c2c55110014204245115180c055800c1c0b85460035000c81c1030702070b28180c80c1a084ea07170301c0107031468004542451004502200c010044600800071070f2040707007040054003015001581c0c460f814076508080311950b40c82802660022001654460400e1040ba041c00300150702c610345948a042c0c042d0704025021803190b60510421500040b03145c050b0700b003001ea100d070868204190525000c01a078441038140302100000b0402c11420131038407040f8000d400c100c90121038010709031410201c0c5c1400c4070740 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 990938588 1250 990937338 990937357
    0xb0a02090f0d08180117010509071b030c0b1315050402010c0206070b040308061f03150801180b0108070b070f03120507030b04050a0b0d06050a0e061305060114150304020312 76
    0x5000440d01c840d91484040d5003407a41c800c0c84c0120016100a44211b1414810b000b01c40c4610640404144858801c0034181000c518101045c061545c0d640b4001d44041c481d640c0c01c40b0410343c144001124000d0810003095600d030402c6482030f111400c800400010440140304905014404c08814090380fa0700010305542c61240c150000d080c100f40c20054212070008281d00d10690103006107030070384245820007481c0b041030f5050204140c035104101c001c115247c3d40100c8010362038000800010b07507200381042c014600a14a2548590700d42c40c1d411b446076202e014a201103402002681c0000f03001e030b4150f46006000b481d020600c3c862a0307603010140c44003507030b41c500000e440740d18281c0380385000e00c2100d801c0304a80b501084640f5154000c20350001c0d00034030103408a070360342c40040c0d0010030b9a00098210740e20300042e034455250100307441d420360307404103420386407032007120004140a81c11088617502e039000104002c0c2c404465420024055000800890700b602451000f00c00185621000e440d0008 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 990939838 1250 990938588 990938603
    0x90e061305040c090b0402160609020a03021338010f1427040501050907030209030c060703171501080406020f0d2a03111801091a130605070b0a02090f0d 67
    0xa180030b04440964505c456200d10a51041007450150020032103500d0744103901a002065481c040e00024000c1c806d194000380d048007008241440005480c6e1203200096121013052040005450040c03006002d19202002c801040c5400100da0350300502032801c2d40390141c03030286090980301e05c0b480355079007012050b00214040d440039850640761400000924917010f4030204070035071400d0002021040c1c0070780010b040c580e0018a84c082514144000350f003120020700340030b82c0c4404070b03c3c004018110034029041c0781c08126006c01c440132418281c0c81c81142c0140d40c0c4ac078035a2a25241c000096100214044128508203d440440c4e64140108075121898140c6004130001504680c01910381d100070060030513117002c259124000c4058192100f680300300d0801c07203804589100582e0009120303088612035441084c0f40c4900030203404000c2c4082b0135810380c0030514542d80e4209a904c0d010740b1200600c0082401c00141751705515902032300d20a14000e180b02060150306020540116078580299101c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 990941088 1250 990939838 990939863
    0x603121920061602070506161713090c0327170a05070602071b03060905240a0c030b1201060f0b0f04031b03080d1e020307090e06130504 60
    0x180e00039158401d0090450300204000850000c41d58541e040101010f00e8103c503c0c910040c920b10030030108000d4400902555940d00305104d02c0034000000020403115414503004649860400703000b071390103216101c801ca020b96410701c0c2c8008050078100000808059030f40d03141e40d03203804417810307000690b080c90724626080c100f0b2410308201d8070500c8000d40ca00d0355000c1110f05e0406606c001190301898200b000140c84184030b10f040d42c42c0740d416a04070001b1000400e4007106111103a4080b00039103216030112080b2607000f0307480911140100701c80c51810310f0b211000481d5040c064108100207502c0c0d00e40005c1031480c40b40000c1071a031084410301ca0580d51101d0610030345014581040107401801f002e50b0034618419501a4180320ba404020b000030b00060350040351341c28030134036000995407094045880701c8061550710010300700c0180d140c0c290b00f010340503410313012580d01c00c80e400741e9000c2d81d4400540342000414910000090b10203070b0414801c030b0240d208410144a540e003d14800e48a14101 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 990942338 1250 990941088 990941137
    0x11040f0308310e07231222230708030a0f1d041d060705090405060f03062710021213080f1602090c0406091d1b190e0103140c030609060312 61
    0x34440007451400051042d80e248218150201900e03100d541e03011560107640b10304800400b002101d05101c14855109d24400800c200c10b010002d8000b000480da900080f81c40c01c414116985000510382d45410b42c4401101d1599003080c0d000700c1c41038101d07102c040c41e600e81116065450050100c1c0d07400001000812070640f103240c98000c0c140c02200445070820340641030300001341c40e070300054451b02c2071010042a81d01c0c62000f60741400b0700003a81000b03031059504034004109c040d40c4010021241141001c0001e04403941040c50210026003181c1ca42c5c0c1030000c40984040c2551002140d152424040e4100000698400012510900104840984691408001030215000c0d034101041440c665109030b01d851038040e0b6800d42c40343c5628071403800404800c0803800d451140f50302d1410022103403091500d20035023211402120620a036410048241d01a80c02c0c101c006044d6158030503003100f000410b90b03515114140c0c0360403101c01004d032102003d0f00601d00766260b00c102883c850175440804417025 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 990943588 1250 990942338 990942367
    0x40b1822020a090b070c05010305040311070e0429040822090b0301060b0c2512050106060f0309020619090f030515071d010311040f0308310e0723 64
    0x10514080e5050030001d00351b90385040429180a2141015a2100006e081c14426814003c1070b482c1c1100707460401d511303049143c107140c0b822903040e10f41c1e80800c840209a1420152200301104400328108401d48480c1c2d1104c01640c004401c014030715001d41c0d0f407145080c0301d0304200c0b80100b504500004050886009042c00d6030b0361a488180740c2c20042c4640b4601080c04140a0107200d220360013105203600d00714020544100300e0f0041c1d24604a01070303004080000544c443c0c0300b907030019210000d04056404085013564000c4c00b000790450f1050040c2011500110300740070b920301460400d003048035240d61500c0c0e1005010f0f4425140c9504c552a010721040300389a0710340e08003000d4a003800b50700c468400441401509801c0290401d0b544210b100b0030250b02c48213450207029550181030000c0d56908000003aa00503644c884012030f640e00d590b40c0d40000d550b58140704840c0c100c10801d28203142c0990820052300060510090000856460001000045006803101d0740300c04815198001c031041041d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 990944838 1250 990943588 990943607
    0x3040c0512070311030109060c0e04050906011a21070c03170606090d0f02090a09031107151101110703090312080411040b03031b060402031002040b1822020a 69
    0x81c09001ca0081c9140e071110040349810681c1e401c090400d6072410200082030040049402c0904001c0c6004091042250300405040170103400701d0b03041c4604d450329072000b40c0715402841040340907820b00e0a070085242c944000b40610380c0c0504403815401d86003003007410b400712086a140c400103590541c900d040541040005080c500204108030552405601041c814480e6220b240d00c90103080740700504005a00e50580c011580c00b42c036140d11030601c890488058110701c40202e000c54550190034484150028010003121840c440c0180c0e1005626015078940001101d540819522a80c41a40c0c1600b403600401e4440c4c1301e50b40d24482d203031940c144085000b00d0804078408000640e014480840c0d581c46803030000002c12031300000e003041140c000900d03500c10201c04842840441d4a00c5440c40b402003400d604c180d000381d00b43c1d0781e00c10a01c6141c000300c1c0308600034610400000c0c0044212a040030000070712002010f0020201000c00c41d40902c1c0962a01c0d091225454000031031601c803641c01030921 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 990946088 1250 990944838 990944849
    0x1e0d1a09010f0b091201090f081b1b2403070207140105070c05060a020307020a1403070509160305061513090b0d02030c1302090907080106020d0903031d150d0203040c 73
    0xd850b480d080100c01c480d644103100c44c442c404c03900444081d100220a50007144499408001222001e030280f4003000c0d103400a0700409400303441c80d10764020711803001c1254040b500402a0f0801030005003800c01850401614601d1070440c010560340d01051001c40c010760182c01543c0081100034500001c0f03000c15803920600c18100941440004000b0b00301107002025508100c541c2ca4484071000d030304a165008062000e90b200d00429000100c180310212520500d103030650540304940d844e44180b08601c88150b40614805400c01002030000e80300703502035070b00300c90000c2121100c92128008081d01e500510f80d840b000d200c1c03005041081d0101c901c200320300504150f405160b00300a03600007039166945c036a000348c060300c000e0014400f0001c40390f0459032240d0005200408600340018010b00415090050030054807480706440300082c01511500d0442e81d25a985214a00c10716501c1c1151104d03414090b500540081d00c1d140c20004a4406841641120000141c0301c0c40c250815220f00388050340030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 990947338 1250 990946088 990946109
    0x12011e0e0c04231506130504050609040b1f0512011b18091806090521040308040303050d0908160318031a2a0d201e0d1a0901 55
    0x221030151916140078940c041c0f11000c2071020b942d400e8401c0070380450b0b160700140c0c04400051001c0345120001c24030f20035204140e80c10000350fa14681480100300094030f01501d103682c2140056082c0202c8680d0815031071403400000c0b61280c2e914045a030501046591000c140d46464081d000c0c540c44400035100c03d060b51a2501c1d4200c584454176840c00414002c110481d600d8600410f40100c1504240704200d074000410024801c071070030300c1a103d40d4030101d00c0140d80d1841c98820040e034513600c155803d84c2e81242a403840d003451540d0640d51580107050174503026403514030702404184050050701a070300110b4442d100e001500c3c03900800f060005100c0340d498a0300d00b4800e00109501304510901090031207000c0c0d22544805001504829424a51920804101540c41d40011010780a800340e9140c04609100040280c42d200203469011800e284be201001d016100040c400301c41420f03611111440140d14081c00b83d4a4081558204001c40720000c141c0d60040c50382e400c0500d1102d005083c3e189a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 990948588 1250 990947338 990947351
    0x120a060c1d15030a090201090503030d090302070806040c06050307022506020f16060e220c0f05090d020f06040e0c0702031504030c0b04020402280f091412011e0e0c04 73
    0x6200150002801c4d150145030750315a0b070001c59005581b140c4c09441d0090803070341c440d880582d0351801b90009200c100d005014210f400554440001911030082d644207842d0343e0380d04d040040845458000410060442c401e8480b03940c0b81c102907000c03500c0300024503c0c000c04560b0412402914084c03600424000f0750740101450f129141100310360b04156102c0d80f8014000c400602e0018084440304803030b01445828a132350f044400d02881c1d005c0402400c291b1540360021400600c1a03400e4065a03540b2608001d4403c4520010314042d031585500141c010151418561504400040d81d00b04407400c500d0042e0019902c42540780400c031040c50101d0124480c24a8a8503a41c004d00c941d8100c880100482c0e41140440c0031540c80e80c0596003030082d42180071075240342c040726141b090b511002c2c440c00810000c009916210b403040e103041d41601c0d0040754007030320b100c81c10301800404881c030ba8030b100481d545d4010104c4249040c5090f00c8000030701c00070200e20000c80710314990500711140d811030702c124509403 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 990949838 1250 990948588 990948619
    0x90302060304060902150307031b1b0311070b040e040203100e0a0611190c0c061d0d061b091403010216030e0333091b120a060c1d 57
    0x4101c0b40d200e584150007140c0c600991000c241640400012500ea09001001700b1002d10780c56030007400880e61083c2244c841400900043d40caa07041c40000c41800307200c1c5032032140403a001c1c042c5040c038150f04038229617010341c2e200852003158000e90800c511806018041c001546420440c0741210b28105904002c102c0c540480a95125415000201b665480b90020710740c83d00440c058921019851042e01c980c00710404d40140f01381048103080718004581c1d03401007220340c4150b031011004402515403040342500c00c0100030072440100030445805440701011101203201a01024010b03170241c071407044290a01d00d50004e515032080825000c1c0c0e1050022018810a010520b03c015402d8100b240d04c00c00400c0209084c41c440156115008503400b0030300ca00c00c0c10031034140c4a1007009118a4210b03445a400c0c0d01e0310f802b0501c001440d000c084c0024002c0c81d1800c00446609140100c04580e0005202d40c0c4100580308550100c1e0301050400300703c0c03510035681141180345800225042480b0002d8031 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 990951088 1250 990949838 990949849
    0xc03270f0608061917010b0604140418020604051c02030a03090e0a0e0703060b060d06080f01110c15060316081b0d030f052101080102130f0605030708041e050c03060601090302 77
    0x10f00c6215911742035007500000030300b000e40c0404041c110103081a41e5680d1621960a0001100c0801501847c0b030b127200e50f8145004c071a003112009a000301528a0203140004001c00b0719003480c520200440d10380d4214005036003c000c494000c503c01d0712a42e80041c81d1003a9501445001400b4458003410050034800312500441c0003000d0700c0c1d0025000800381502c502048540c0660701c0c200c003207603150a101043c04100003070040780d040c1401c4020321200c0c2c507048000c1094040c0041d564460340c05210002c51791003a2204003580090302031304480902c9074823b9492500825507001016035000050800e103015000c40c24150107242c182d0740700810b0640d0f03a4005204908220040c01003000104d04c0c207403608100e10300d607000068680710740019541c40d006428000d50003400140da08007000d940000d4541c1c8812542021106280c07a46429640d0f00e0f6425518840010001c850058541c0c0da000b00d0300708800c0800c400e6501030b100070011f20303080c1c009241c81c004000d04494180102a101000141e444 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 990952338 1250 990951088 990951139
    0x52806170a1805250603181e120f021608030d0b01030204080a050c040e010c021009020105040f080d08070815011101060f0308030a0b010f0c03270f060806 68
    0xa40042c0c1c0b51514041e4042e010300c1500001c000d8040c240b03c3d00c0000c80000c0b8448000d244400e1010882030b520402501110b401c0c10f52540b00001034a80107001c9444c040c051307070b1140420025120380f00210340c0c44010348822400c2000c00710f000d548a000700c2030307810000203100340d000d440000756441c2403404056507030041c5600d28181d01d07100c814040c4282d119070140e6000340701680480703284a80514140d0344503013811001c140a0703403401044034502c140500034142103560b103801030019030701420403140c042c0030420000c1e410304c00e08100020b540c00142c0c0340302000380401c6024080d034198540340103043c1407000e4240d004002c0c0c48028400d90801e0300c5042c044018003404d14110101c850321145001d0b0040d9807010001d030300d121500000b03007c2e901008521640070b050080264500250065030000c1d204002c420000e43d9214154001a0061121aa850f0310303080c080ca075410300110300c52020040d141c20006030700c4e0030b031442000741030f40150f0709a4014400322800c03e0b0800c102400c903000300b0031 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 990953588 1250 990952338 990952351
    0x1501050f0604090515060c030c0c1801030803040c0510080105120a02150a032007021311040e1504060303031b02060c2a0d170a090b04021905280617 65
    0x613910301050100c07440c8079607103000314009850301e92a010020400ca480360000710001c0c001e4001c04a01c5241c5282009002d800241ca60740c005825900b10346401100da00300030002c5075044805040821159145c0041d448002107580d03c602c0c0e258180360a200341c60100354603805c0b030f650003000c013407005960352744140f64500b20110720262a000c41d20400c501404464540c00754504d8a5414a900b001b020001410050b00a50f5544007840c10316071460126142c5060030740344074006000a000d030720350b5800820380100071940624858581e0724000780440e41c4562045003c42d603242d401c41140d520b58060b90103121843e00144c2554074241c12082401d100320604001e085605002c1031000f52480b035400d40540800000711441c0440e022300241200000d41c1c03913004420000b100040d040601802a0240698400401c0140ba215035080c04a02204074041411602d024400820320703071201e8a000c0c00c0d221241d440840c01000740d20004c4840c04c0141c20040820a8210203102c90884c50341d801c0307404c482d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 990954838 1250 990953588 990953591
    0xc0c02030c0906010e12241605030c070b0a0c0801080a02150c031b03070b010e070c03110705040903080411010203041d040615150305091603111503091501050f060409 73
    0x1035500004858855104c0b11051b031180c3c030f100d5400750840c1c001424050840403081a02d040031f10120607100d9808046580d070640100c07076540058414450009950410b03044840541040016907640704280400c0b07070055482070355080c0c1c090701140e10031a1280146150000b4020500c00f503004140c0d00000b0814500303030424009469421070b2030800c129100000307000560403030080c2d842d152944a40c0406002e503880710180740049600312000720614050f044588404880c421199010b8030900a4206960000e014034603000589848501035241c090748a5038800b003452915203418040c004c107150b4040e045600503c03080c4405185a1402d40c000c40740c18a0449a5980d03030300d03140340941205c2000159020040500064010380b0340c40358440d4108584040c066590380072016552008110001c100700700e0700103400c0011420f01034482d4440388002d810f03080c1003402c070400607003594030036100c01c0103541c86214140c40140310b9250460151404654a05440030400006000f0b400350340140c42186 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 990956088 1250 990954838 990954841
    0xa11180415050d05061504060e070f1e021f051005190506072f09130302010212070c0210230307110a110f090903070303150f0312030c0c02030c09 64
    0x1101001071160007080020a502c0101510f407070040c0d1990390070b8a025000c20b055083c100101d14041c0100401d8400800400400355134000c801c84415008c4070703500d000c1c1702022000650186401604808031100e640091030004188001c1201d941c40902110300800e02d01b5050000385d0316400d1800003122021107414082c08420400c2c0c84201190368400b40e4000e0b0005004000c001c00e241c9c0016005070184840d01c4021242ca001011000301c0c02510342d80490f032000060f114003031a01e1603088544c000e200040c10308003141c981d802d007240c041e6000b401003022a0407080844c0750504449030301c41c8042ca00b00c0e42c00030365041d0030000180b0746000580c20000c0400010f0041d03100b00c2600200000c2401106d00010007070800300030800001601d0390240d80071240c0c01e92181050801140556a0300b00254500b10a949003140244061100080300a5885d100040d0346c411900c6424051401005100b0f900c0382010400303011154902100700621030300406d14005650040352003456103a0a982000c803a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 990957338 1250 990956088 990956111
    0x14040b03030d021603080f0403080a05070203120112210815011214010e070c230f070303020609010c08010803090904080f07060510080a021011190b0a111804 69
    0x450040a10b180e090510200c4c444c09101d54078851840c0d9107020f07844000301500c50a1050000c500100d40c040d010820701c40200e103841d02c8551015234095100d1040d00e007041d8bc0c445062410200070303440702400500d80d81000003400404070064649044842482429000100015113040350051201c203990f4000208840030b40d01031003810440940c44482001603103400d20105400e01000c5c0140302c1d501042e44000350340180685400011240c0000c68540c1010350405e6841a400780003001103c28040e0b00c0c000d446000f005c104409c0078502c280c0291002e843d28045d140d00f100c89001c0b04404110071040100404c1101200300d40003154180c41d400300d00c0d621410008510b00c21005450a035140c002020014084194405030042c041034501c424000c0d5280401e640d1004a0704010354013a42d1b04402540d0315004080103502d407075004d016182c0309050034a0352001041c00d080103580c203161450401030542c14a1140b00d000c202c0c040c03841401d040e448400480c920098580b51402a552000c46905 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 990958588 1250 990957338 990957343
    0x111c15020724152603040810020c21220303080f0414120403020109080c01051b070503011b030b01090f1505091002010912080103080307080c130e010f08030414040b03 73
    0x3c2c40191000d490700103950342d42c2c542600c01e102e52006201c4c05141c0108104252020045800300c862443c010600c0019681c034141c02503201140441c1213210b01048180310249400f1764040ca0400103403602e84400c4130050030701c080c426080752801c2c0044d882000740002034010210036007002c0c06040848031a42ca80ca40304005155129000d221880780050080b0301c480e0403001041640d100780e17070703544402e43d4a040440c0e599007401b2405001c9503090140c0f034960b2005a070007280c1d0f8240e4400719284681c0c3c0c0d101090840300c1523681c05002c2c1d168014203000c2c15425005217a1600c070b0a20348561107514020303110050610a010705000030a000e14810546c604c40e00030b45969840041c082003040c040f403030000c1d00030200c8840480b801640f154000303c002e406040c03c1412240c00c418030711b1850b52a4801254800390080070403102e02030902c070200c41c40c0101501c642c0500360a0100a50b103505000710204d0342e507680d500c4851107070310800080c040b16024502c042c4100c1819100450401d2091000070f0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 990959838 1250 990958588 990958601
    0x303020616031d0c01140c28080d0b120303040201020c0f03070b0301150212030405030703080c120426180d0503040e0405010c08151804111c15020724 66
    0xf0040d0b041c401840d00c640710120701819041e00980f51035540380301d01d55000003d40101d501c0046250000d5010004100c40c3d0100c49001c901c4003031400003c0404e50382ca0300d001c1d0300250f8812780c280b81c3c1e541007442181000300015a4110000b00194103614150b40000c1d91031490388049070050015400c0d012650b01c04016880147c40b0750020340b9100d44c0c4800030180c9043c100242503006200e0030071464105034808044a00454000020b5450b0010310b85043d20303540703c00380611044a00800011a0000128844a000300d101d4090070191071402c80d0030036000c54440032541d2039030000300007250140ca100309101c014550145c80802a104c0035060003030640c00b5a500c011140d900030300800c400c200d410352289601a055403110780098440001d400d110b20b280e60320340350300600d01e0490001a88011400b00340d021b485040c3c1000e045813814040784001440c0035100c8482d01c8544281c108010b00d0994884c010780711501c0071820000c241d210b110b80340c00d4240074140d0341c003030110400c5519011a000318 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 990961088 1250 990959838 990959861
    0x20d030b210c1e03210406050307021207050c030d320903031b12070b07110f01110c060c09030303070f0c1a06010e0915060d0603020907080619030302061603 69
    0x1401550280f401510704169280081e100b4021020f0000c595030742c000410810400c000d03071180c03c0505101c402d03107050f40050705d940c1c01c1d4440c58074840c9845600c0c0c2d00404200348140003820f00300025406151800d460b190b84a4240b040c00010f0f1403004699581c43c80c45c52440805030b20007004807104d84007007072181d0520190140000105040002a0490206200300700314080381e022140c2414139010310301400400800744030441d000b09009509c20040407484005810175214215149401c3e03900f1034030702d07050514542c01d020079038020100007031082c0c0c0c0d03100e07000c03407100c030320701904140003035280d20005010318103020f20710081e0444144118680c2041c0c95000d4004e03400381140c0900c100a0210486410380014601195042d00382032489549004504600000b401402503204000c4190001c002c5501c03180d81d509000130260391211030840c061072280d142c041841c20100140030b12403c04c46002d807600c03401401c082001035400240b031070f8400c4074138444035100d50007120b00f1030180040d600007 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 990962338 1250 990961088 990961099
    0x102100b01090305100506030d03140f061801091b0327080f03040c0302122b0c021801061b0c0b0d020910030506010e0d0f080906071a010303020d030b210c 68
    0x8101d480b80280c6e00050050b80101c044954468040708100d0545240e0b00b000a031a80c44000400c10034400c803240181c025000904412401840c80c507846003605007680b00d0410a6201c00c2e90081c2c604040c10b64000c5941039140c24468a00485c00c100c005410a0402c81c018103446000c05040c4804002507481400604c901e566503810681044448542140002d9103d040300008a105c0c4090003c1e104030440030f03a1190100d03d281721042200340f030b0180b01d404018004201c00c1d81c401651061010350142c101d0b14040e03c01035041103c0100040700b40c140300304154080b1000031011400708410300c4101d91403540c0a0355105440a00c020190007180d2540750084404d558030300c0301c103030103810085c1324541c2030740d5081095500404000740b801c0361540190a40c400520040c0116400e0002000c5c9000c0c058402c92a22102c0d654243c0403407400540c001d0312800340d4005204056040c000c0488003da00c0c5000d0250400c2900020750407848940c65541011303400058442c40a014009500d40010007410b = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 990963588 1250 990962338 990962353
    0x10b03100807180b0409031220070c1406070206121902040306020d27020d06020c070806040506010e0709230312070c1d041203020d05040c080f010b0102100b01090305 73
    0x51900903903401e0f03c0c00450550401240b40b0349420176111b030041c01509070307460f941000050080d00c070007440c0c4540354860081c811810243c680345d01c84000c1203154803805400c1d000b240350240f001c4a4000d030300d1086102d035404002c0314015989090541c1c08014406480c070385030b0b03111140d1118003000020b08042c0d030380e030000c28000300b031200030780c080c3c0308508000d1024002002000345044505c94032085035800c00214425000141c01d1441420840f9446054010b14103c0c0105d03400d45442500d40c070000c0c5580c041c0c400c101c02c004d004c0c4050307401041c5680030101a400e102030040c041020600070075844158200c00f61181d16031140741c007400310398050150394059208031220300160788000300980f42d0b03240d074031400900d07005203111078040540c070346040c212a82c49903681c198041080140300720806400348004040c40300a8420a80a148035489210301c1c40c0c030301001d190800d243c60180c3e00b010f9141602c18643c59801081d4071130100f004880000d800080000140e0b14182580c00150052141d4034 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 990964838 1250 990963588 990963599
    0x182809020d0b0406030314091503090a050d0c02030a0201030c05070b010902040620030f031e09030301050f042a020703051b151608030406110c0a060b0f01020303010b03100807 77
    0x5004050008001c0000d0105100078810b01c025600d0038400103001030140000b401815280c24060070001c3d41c0244080050488440340d103c40742c009880d0300ea0f0b190024112401040410400b1542080322400d151540082070740001c0d031107814544001c1d040c142c4480c0d4180025103d0700403640c205e80e019a081d401f40d61034044600081d08640220004140d40e24501d1403802020401c002030a41403c0086d8940345282252000720780000d041185691000045084d050148403005482600c500000795180c0d80341c0320030041602d8032542294000ca02d04603001000110346042c074652143e00c1b9100c5023002000c154100e1038080a5400078040c4c0c0213142001804c038040804101c03400500722a800342c5202c044101811610603520840c01d9002c8003401ca0f4005104000956407103030180000165261440036260460340c811552040242c00615a6004000003403180c94805241075464001411103840080d650b444180681d809115000c00040d5003207401e49070307000c042e00c40300041d41d41c1c490341c50 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 990966088 1250 990964838 990964841
    0xe07020a0c050a080703080d0b0d03030c0201050106050f03060409050f030d05040c0906150f050f04060c0b101a030a0b100216230d260c1002182809 65
    0x34104450a1038500c10014081c6014240c1e2020f4910700c1001c4c03c02545035036101c001e10340c071008280c104141c94600701030700759841c101300501090180d01e01003000302c18800d00a084401c140c107e40c0034840148000914505080300392507214905031400500d10003203051041c41c2440300035800040b4403002074a040006040d0300300c14001c51050018450003500c4809201c00c1d180d0034000d4644552105c11403800f418131031100405140351a0803c203107031000f00b0850b215298810f81060000c80c241110007410028000c01a56114407203480640e0890b0428040e1900c61100880c43c0040c0500403001c145007505981c020a40e000380101030401c200016100a5190002110300e10021804403600288103079072a00d180c0d07a0301145003240c0690320069070402000d502025000e803641402000e81820b0030111401da284230f01c0000302d03000d846104481880d0300d440d10500400a58600500c130540c140d40104507d01c010607001c070b80080303441c4140030341c11a0f0007680c5031440711011682580090303168080d = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 990967338 1250 990966088 990966103
    0x308190f1406090903031f1d1f060203090120010501030b011805070c03050d24050406121101032f0a0801080d080703050a06050306160810030b010504150e0702 70
    0x30304000c4881c0381c0e1901c0400c00700440031070740000d00b0703001080002d24480c103007480c0580402d60141a000c0c1943c4440c0400c5801e00e6480c81c280008007080305011451045001e0400420845089002d00300d0821400945900680880347d0510580403080404948240606211203200c44020031696075a42414550709000384120164007030303100301c52110400e65016080c8640840e07106c2c40003800d1660340403207940e0720000103c00415612202000390801084401d00c103846843c40e142c660300d0905c3c00700001ca45099209050510788101c0c140000f4100c409168410345003424001000030503c12139030403484112200445030340208040000071158000a0101c0100a64400203070380c0e21484851341e101801c80041020460b40c80008a50030303c66004950310035100d4001180f85e40c0d031540803d2a08000b42c2d20b130326150300c503500701d8022143e00092080d403201d58141100919461511103094003c07042c05564011502d07240000c00070800d400392840200f5445003140138031310b0401c50003502d0300203 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 990968588 1250 990967338 990967361
    0xf0e010210180b060604080318010e040504120e0303070525030f03050307030b15090f0307080f0c091e0c070201020312130204060e1b03041407170105130309030308190f 74
    0x91000843c81311705200064505803290203004518201b481c0000110f2520b2004103a41000404110200641c4030741c000c990083c0d20422590040c01141c14000e486915202041d9019900c05d1148101050000071b02c881b01440120013910540034800c1101c0a0b0703030312a08081c2902c40504508810940d001c0002c0d8491000743d030b0101701c000c6000301004100703e00d1201443c80c6d030000344540c1025190041c6002c01c0100300034200e07540a40d070b540c0640c1c18802d009505841c05d40100501c2038082c00c001d00c406030700c944900c4c44407100c0002e005403203260060140036826040c001080c0f2404590007001140c51310b0340c0e4503541c2c0881d0b02d0881e901005e2050149400c03070089040500014100606019040c01540b4111101c3e200041c1450904100d40008000303403075088540200c0d8036000360074080c240180c400074065500e10f03400707000c10a00350348010b040d245070035aa80c0508000700e40e012140300c0030359606160000381600c424032a03030300382501c604840c0b40d000d15012444c0c4040109a2141e0b44403038 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 990969838 1250 990968588 990968603
    0x30a150b0a050d020f1f210212010b031008160612110d02070c0f06080609011205100c0e1002010c030b06160803062809110306010f0e01021018 63
    0x156190240800d0020750b01c540c82d00a0124642c0000614160b64803248411000d00205a012400c0c40c1820700c054034a800a80810f80890340804400e410390500501e128400a056181100380300c1d0400000301705100f0013048a40200104040700c0b440110312008189281c01c039003403500101180c0598030761170310030b07000458008855843c004000d405002416105104901e0a2400012141000c1c1d4090728080310031003440701c0046071200c106010040600b20703e50701d00480f45020700c148010b40006030040000d54410003040d40003c0c900090300054400e1a01c004203510a0400b0241e40b03002c002c030703589540f25080541c1400c5603603056005ca41c0182c040d5a09100140184051216074800c400c0c0b8040450101c0d29a01301140b1101c00468200c240a0103540c0e04480b0100000759050f03c0c1004440e2900c62418108466505800b81c44000c440c078402c4a80346d400d1440010340921302c001002d409014000c2042c5103240c1c001d000c5003011001800b402d11840300b40104103c02c458100340e0854004 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 990971088 1250 990969838 990969851
    0x70501110d0225090203090d030522060c0509040e0a0213020406080a0c05070b01030c090516021905161d070e10030209031e01051608090705040504050309030a15 71
    0x50300300040c00c07400d04a05401401420a06920300341c018075044034001080f9584080020303600701d180c8000e42c810100070014010071031a8100041c182c480162a001c0d4141c8240004010360311416640241d096011074001a0310820b0034040d1040c0c080c01c0c1206d41c3c8a40340003100c00003070038003040c83c240c21031084403e0304201070400304840480c0210b00030500002c000d000041c2c68a04c96074049410b115031418001d00b461102d64035011009401d0308129560000ba89040100c0b011601880750082800310302c65402091040000396034001050f06c40c02060030284504003440001d000c0480044d020174450510780da00d03890041c2d14000340300c040e52210350440f00012074407031254104203940078004148051810211008402039000014110350502424441031421702c2c40a40f0390306840c20544c00400c69241c220304607140000420410001d01010a081040310340001c200a42603c0c0102c0b00010580c65a0405900e10301882c4299601445002142c0007405084103c500d00307861703025400c1c00003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 990972338 1250 990971088 990971117
    0x80402180403081e1e0a0917040f05040524130f0b010e1c030c0c091a0f03010b09011503021603200703171c09030503091912051e0c070501 61
    0x204c0e007007218034441d10740d1110030745400700d20b204925640007000300c0300100b0540700341d40b590303036000c5401c0c0c2c985550310b0300c0002c080040280e60b42d2618020f11040314100454949090b25202c0d02441c070080b6424400a00e00745009962181101124035148540802880ea007407078901008103030111800d40072030051854819145490703264a02c08400c24004004200e440f50f6003610070000d0448202da17041741c00344003c2000c21151003000004440ea202200c007074400390742840b158408001c442c85c000c4c0d05001200101da10303403908060446400d400f66151082002500720000d004111408084002008007042455405043d4113416285645094240c0a007403034480c1d1b035031400f2300c030003080b5000f000300c15a280351030100682203108103440d80407955205510307050212408070790110042007021003031000200303041020002295182280366040305403900c0d034040c00403e100f80c0208014001501019410311400c005030079001c01d501c074640340c1003510b54240d1141c245001e045d00065180444d03410 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 990973588 1250 990972338 990972391
    0x10608100b03090c010305070c0f03020307020a0605180f030106030b0a06050910120b040f0f0c14040e070b090411030a050108190f0303110c0307051b10020d08040218040308 76
    0x5034107054014581280303c2130040d80038040080014060142010440700451001112900c0c414840d0340903503514920752041005030b0401d40c200c1c50822809005608206000c46801051301d4411038041d031000390000700003409050b090300b0041c444a00c8800b40b00388200a5000407040e200b046410326465665560744601124107880b50503072600c80e4202d0440440d04280c01aa0003034000c04e448101210703213841c0d10300d42280d03080341200c518101000402024016104d81d2000310b80c221014800c012031a21a03e949001714010000d62910000d000800ca960701d0740030134141030301000740d96180d203000d00608008240921038103c40d8040c007100d111314601a80c02500b01582d02c65072104030466652400c80041c00034038591000007001700814503000400304090b01106204074001c0001c184041710007140c42803080d01040c01400080003600e801900420400002c07201c614020405640300e0002a419000707014403840c01140c40420320080c554001007051150071105584004c50300d00c01442030 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 990974838 1250 990973588 990973591
    0xb09041203050c0d0606080f0108061b1c09050a05070b0a140a090305100f060e062409040213150c2012070f0e0a0e06151305010608100b03 61
    0x1030100305254400d1884074026800326410120141045040c003108420702c0301283e14503080540400c2d81380341040740305d41c69410454094082e403400b91a0368140814a0140303848000c11207007006001003880030100841002e07007844005120000c0c064a041070400f1500c8442101d4143c40500954401041e0948400e08403900c8241e180d0300c4200403901a100c00105421010410040002064000010400402c100006601c0c6d060340041c9503501031140004540486e80060000f000c607808103c195943c20303d0001c040e0000242c1c5000d00c07a000703200a02c036031241780d088030345c824804210109801c8130345409009503034000d01ca91350444843c0c042507031000201d140080c880c0e03100d0070517048800f0b14820510030040028250341070411060301e0003410003901d03400030160003d58000400074a8401c43e500343d008020b0042c1048001e03041c680385619440c0c001c000c0540070004000c0d150300c1d0f8441c4581650f598034000d47c00c0107203586800b0020714004094480d1068005036040225910b50300c0d000300c0703 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 990976088 1250 990974838 990974843
    0xb031504210203090d030518030109350a03360309060503090a021c0609050309010f17012903071206170601090b0109030c030b041506030f02011101020c070e09010b0904 74
    0x50240f80303040c0d0703000c40340c48c3e00000144004c5454501070803081d4400740901e4210a105401c038106002c0303070502c252502040501a8030480c0da40c0010a5544590382085070030410b52854085019143d02c40d421064644140d20504a10a003440000d40050525007641c89644a41d07202240c1e2640d0305400c507428081620b1020b869044501c40c100145003400c840e140c0d00c85140c0e4015414181c03502c4503400c0b181a503606440c00d03040001e4166003580c1c442c000c0179410003541403450203140c112841c0c040c040c1c014000c10342a00b5003500d00034407190303804040e04109908404e4182c0c0d03914110304010010003c05180da1400d60503d10301141e40101300500d03452a51151f8010040703a0320302102640903201c0402e5060501c491020080301044554403520090750164554000c42e04251074000c01d41c540441e41c64034418a00039047c0002071100414010442c4c0920b00101d2851288107020700a01c03404428540c588100c04e000030396846070540c050301c40e010b024000c220000b4140140705003440f00b00e500 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 990977338 1250 990976088 990976099
    0xf080c09040905210d050109110318030409020c03070c380705010e150c093003130302090f1021050102390d030b03150421020309 57
    0x65403101d0038554801e00d101c9000c0d0048980886440781c0050500034041499203050340000b8040d00801c4042c000c0500411101c10208024052404001070700e0001900e43ca00881900c95000e04441c000c20035980074010b100303030865071031413600082660303540900d4088400400e4a240010b1400800061a080440f01000620400c41d03410545280b0250030084500c5400184081c1010034424400c1d09440b1801d50010303c61007100d134028410002c001800f00c032008404101240c100d4072a12600302281c4000d000941e0000b112241040b41c801503114682c5180c4030106006010f21580104482101c0c02503824034210703100d400c052040035004131103d11126a049034104041c008240c0d0414090a80c0050b1046900c800da5400d400c0e42c2c44000740401c07010b40c040036211070340c815188914807201c070650200c90102c40d200300da0341c460400341240014140d43d00c280304003944040c4000300060450380e2524002d450546041d6001d19503543c081050240c6408009400d5400001254040b1100910 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 990978588 1250 990977338 990977347
    0x405031b0306060d0303060f090e161d04020f120d091d010e0403110a0506060901063207051204140901030302190305121611010c050919050603090606010f080c 70
    0x18451041d1302a03c084040566070384000804450600380d58000d443c034002c02150f010101e402491411940c0d2444030007500340d1130820464540030f8410002c000003e0002c51019603620300016142c0084000354640141c2c449084141000000c25407400c500c00c0d680381e10003a00c0c1c42d002e40c0e1401d02c440b04581284010721800612500b4241e1000c250701a1091074400300070f11006080d00e00780120301c5011034096200100380001741c5401c000d2280941a113140c50902042c060031200811000891440b40100c030504240d92000c0440c4202d9490300c0e0040202c401e0046115500421a800351298a000f005012421412072506000c2035048a40550050681c100c2c28880388040c201240c10480c14040304000e4280e51903003e00c20b041c400c1c5e603804052035180c82162800391040c01205002017403079141c00c0c4440c01c000e40140588030305030800d540001c050b03d081861402c030786803c1c1d003016500080c00703c1004803420000601a00c030300820707070343e0b1281003140e150300340c840d110306441098480c9001c0c40f = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 990979838 1250 990978588 990978601
    0x60a0e07090b30030f030103110f031c030f0608150c04030b0403050c011e050f0903190c1a09100b090c09010c0c0e090708060c0a0804080f07080f0405031b0306 70
    0x5041c02c0b000c4a07015400c5078148550f40349510356408450180c0c4c28501c040010000e020740910301195202c000d41d0810705c810b0040300000d03200d03c030034103442c51407110070507480d2010751081d80400142c0420302002c003c2c1300d850b100b4990391040b000f1240c84018002800044500c01c0c40c509581c04c8aa108400710810b442e40d64040c0c8058004454607101e940d81c2d8103c10b5507581101141120711800c2ca14002a6414000e0f03041c072034404002e04000150b442003040548010550202c2824011070f860000180515881c000700c6070540c0b1241c1c5900700385030700c0a02c44070280c0490300102c3c0d2140240c003040010245014400f19000480b0010f504000900c400d03076040d40036040c14285039110b0102d0640560321172010503588401694010781035031000d00305101c120410480c4a0304400e00145560a2422101c0000d04258000744020414031001c915540b00c000c00b101903409050b03009031134688035000e02c100510175412600c03c140c030900ca06d45a031840d10a8503050200d107400090003410b002e1392020b = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 990981088 1250 990979838 990979879
    0x6020a0210050f0708090414070e011b23060702070602070330120b061206060a050409050a02130611101d0f0604121e180503060a0e07090b 61
    0x107810a00104003d0760301c030b41c24000002d01145205030010380c0c4500d045000c0c0401c44880c1210b54104c101d0403024004415004050100b14510074601000390505403a81c850b140b2011032401000601c8802c494018501d20b8101015010341c00c008030703001544e681748226510001031080e000960400c2c1001d102041490100b0200d40c10748140c81e044044403180050702c0c50603103c1c0d555002030081c0382d488581021074061800540e004580341428103c01c00440401d200e00075101ca031050f1000160468514040d1050394001c0190701070401451030f1003902000a503021050170380600c0d80307440d000714043c2e0080d00034015041d020310060585403250760800e40102450344d402c1c054141c4085010344a080200440381c180c2074020040c1034142020702c0c11034508064548a107060040d089061030218075400d0309503103068050301d09444d41007802404011502c0180c0c000d56010b001e098104022240da942122034000b0b1400f048038447e0b44c0ea01c800714203c4402510999112100070710074805003550 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 990982338 1250 990981088 990981109
    0x190f09020114430f020f0a0513020313050d030608060604090b130c081605041107051b0409020409031709010b0609060708160b0405010b03060c0f0c0109050f0709050a0606020a02 78
    0x801403414100341d21a0251016144420001c13641180d98030201d5003103003440083c101b0551015540001070390304140004403400c6520f08044d400300e60100000d070f03142181c00c0c41161050b03000030a07180429490702005010305014050348a0380c0c420140420003a003000c0c411580305070307008425a0040e840781c80032004202c01000c02902c4075400307010080380e40c4a0a12943ca04140781d0018444076034508009d00c01520130a0107040100c410511500010a40110b01d0303803400440c0c2640c1c0e248541c5410700142c010844004080c1d00700f45072051140030103030800800d02c0d250045074010345a0b40c3e15407822500303030b80c0e55400c42ca420a8052048c10240c2c1402e41c080c084d0396108450180c24500b805404410000c040013043d50303150800020700060040a03c116001414182c01401c000d1405008900c5540300f0b4104c555030303220001401d900404400e612407640554400c2c00e880490800c4003c1c0c0c1e0365010b8500500307000901d042e001c41c10503d110310403031088860741d070040e1265148a03020041c074100c0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 990983588 1250 990982338 990982417
    0x8060906011418030f010209031c0513030f02120d0f0507142509020414060c0f0a0302061909150903090f06030606030e01050403090e190f09020114 65
    0x1e004552202c120b560001606800410011030303000c015000c0b04245c0762440c4000f540c01076900c10460003200d034401048030030a03018041103000070034952070741c2100c4612039407030030506d00c1d0440000403003001081c640c3e1390700083c022a83c9c0901c200700103402d546c0741c07903c0c40040740228102c1904241407071300400181102d107004011030754900605245403810038510701503240481440340000228094221030100c040d26000f002141058180345041c2451510302030040d215090205002041d0f86c4c00700725206102c0001015100088558a0041d5603640140c1b2501d011354041030320f901c10b161140c0300c1d50031a25044080001c6565480a0b00001070284107800d900b00840307414003160340b4172100f611800510680d900020b28524000b401022905134200302c02d560790401080c8004203900c02284420b0f2a5083c8001c000e548504400c1803510030740c45984160701e400c3c0800301000d001c0303650185020706e0003030300e40304e40c41c0c0c8084a15200610070445d1400860303038846c460801804c032219101201c440d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 990984838 1250 990983588 990983597
    0x212306010e0a14041b0608090c092e09110f0f0702010c0c08030403051c050a03110d0911041a0d12020721170a020d0309230a05010605060a0806090601 66
    0x5000e11803000c0300c1000b240c00b503512140e9001090f031703a401043c0385a03008186c03616211100342020644aa16090000c201d507100355820000718010801e01130103408003102a4030180b80e10141c0c40328001128420f0f01c01d44402078900110703102181c0002c802c552044042002e40d03032a080014603000d1103500641c2c400d03410404041081c00c0000c50880a6030054040c050086440340d185280c264070b0141d11500101200000c40c58907030340745810105950f0098658103001c41c400245008036911406804d5031409802e05001a003000e10004040c890403100058809110203241e0320303426580c1d04001c1150b190064100e028510108561403110f82104041b48103030b4a510307030f9800344001141c2e22800b5181d074034100708154404020f10340c2c44140c3c03020202080346082c003815071f8010b0b4035030041c05602e5041c1501c0c1d42d204000c1000690388003d03205014850103921480c03050302c0554a0141810840d4150301c0c00c600818985000b0044c2c1d0551080f5039500d02955039180280b2501c1080540000d0501 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 990986088 1250 990984838 990984851
    0x71d060405151201290a0c020105031e10050f040b01020307150906020703030f050601030b01140a090b0d20160807020f10020f07050109030525212306010e0a 69
    0x43c0c004041c42d40203099400d031601003114504400300300d400f00c11345c0b0745c1025202000508155500f000c014106103070242030564030b03607035294481d02040309402509035194032050304110075034a0382403a0030245c48003076075140303c5942c6450511088485070070440d03025034410702c611700c0010607074210807000c0c00210700003003070007001680c038070003070360010740c4218042610765103400400e5035244aa190f1040e030920701032090703610b800000780c00090000c100c0c1e46200c1c0d00141c00e04015010f0401c5600414010254503070710319250404c20300428120f1011740464025080026284020340240e0723b20000c1e4400e0350b074050406586035080d6610a850813038010521100b003807000d9940510402e04148541c0140219882c01c0c9100d5040444c035412450520511590a1010440000b0310794004003103a000107400f6488146080100801e550003c140c0880441e03035016209050f2417888140b5124403010385007800f8110009010300c4400810070305c0d560000004202c5001c03003000c50303500284941c1c00011003 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 990987338 1250 990986088 990986107
    0x2280201021f050105040506030a030f14040f0f050411181e0402030a0501080d1706090a0b03061807090203150f040b0a120212010c08130201091508071d06040515 71
    0x418080030b2441c285542d5a400400143c00c0c1390240680c8890124003404030810666400360410350300c003080f0f00030402c2e42814440c8402d4a142118041c3c10404080c2c02d445654184e4404401d6642c05501d010701c1c1008000f186003111442034448014104580104081e42c40062186074008107214441da2103610407103031200d89580c40214082c6102540210351581483c031070301c0c03070050101404000c05c035040741d24212100110000035041030302119490b80c81c2e2075000c100005090340041c00e5615004801c10700a06100e840b9103024202076a909491600e0b5450f50510100d0100f00c54000c4d00c4000301354654031600e8149415542010700420000e20a12000081122080281c100035144144400a00c0c254640814030111155210009202d4402e0350318005080354005080200010b010340045003c582c014030b031700c10140c0075007004030125181007580100508001c0d40c14001142c65000208a241c1d034042901007d6540604207e14040c54201440100703900f0044501082800f032040000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 990988588 1250 990987338 990987373
    0x3020d020301060f0e010e030705120c04050f040302010b0a031505071103040909060e16031b080d051206010801030b19020712020f12090f060309010b040e010e0d0228020102 76
    0x82e200e1035440025013544007001420443d8802001030500c40807940c0d00300c0554001558109070f610030b548a0065804a5908030b2a0844165000d030348142030030104412442d141c08400d01c41c0d07000354001e00111020106104404403580005002c0b00d41601e500300761400701d6000729030808041d03d0940116a0b011000c0c03402d40e00190130002d03045803140481001e01000b8001d02500302652000ba25610820311296a101041c9201c020200410f0900e0b499150b20402e81c00390080072000d094a6108440780c0004203170790f02c0501421240403090340070504030b5124240760703410b0704d81c0a00e601c00c0e41c0e214986110107101b400c20102a207907400b00100800581d0f0350803044692007003600146400005a440b107402c0280241c05e180415034240182c840a95940008080ba00f000380c1d9003558035207503030140c50b000d0f00082038000d0f0418140158502202015405498041081c9090318010b0354030840c2240c90700755050315404039001d90842d0f459400800d240c600c04081c8140120b8200c002c510f100d140307 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 990989838 1250 990988588 990988591
    0x102072d050c3d200601121703100302130e0a1b0305031216080903070b04020609120c040b0d02011e09230a0b04061707180b030a0b0108070207140103020d0203 70
    0x3402c081c08143c10300041c0e0031402000c0e680400ca9584a110203003034030420760f160014030519040301c1442502030300340f010421150701e480c21310030308182e500c0c908121681d580d29035510003280a4082041c4450407150301d40719107181c1c80200c8014141d200c0ca1500c900064075003a070001101c0c03040219001002440070001032400c0c01040e0405009460a0140402e00c40c102c110700e2418440c0d100c080000700807010084070391442d80403120301041e8681b400800e606004280d1116000b03003104c0151200e200000032555180142110280712404258090003041d2170112002400700351007076006c031100c11b4072400b00e24844041c1d20b80f5144140d5100c2803088041e40c030700c10349421100411fa00340c1540c106040181e0140c40c5090300185000d242580c0144058881d072000e50304445031202040c2080d208181d0058003080740e0141741c506d291901010119503200351070811065243c12001070781175001e104560b00c0b50b5143d801501c512880c01400d49030281d100903082d030400da0308103c048101c001e00d01c06103 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 990991088 1250 990989838 990989929
    0x9021f0c02040506040605060a0c0614040311010c030b1302090d020913170702010507060b040e0708010e01182607023a0c0b0a020f0102072d050c 64
    0x14200c04003401400111500508294025410440e0500c21078a4050413941c48410a140c0594055034904000e8000c01d002121003005001c07032010300c018950310060102101182c48000c2009030001c101c01d90842d50403540b02500411803440300d91030414954081e1920782d01c05420501120300e1a40010301c10042212440941201440d8050920214002c8003841c441c580308002d1421340e440d00060081e02900c0802021140c550045400503100c51700148070f84c1c00a0811124450346940149002e02070b05490a58158600b072038200500465082d00d6002c690480d8066605450b040d03d2030071030a40043d5002d01440d010088140182c503044511384002c0e840700c1032aa89c031442410100b4542e00000d69106003402e800140802007800302201d0001c4039507051941e42e0791b01280d40e00342d0500c074400d00d4402c050352000c00ca50040c0b11540f408901c0c00952451010130041c1c050700100d1002e031030740350050625801916506d0301420040340c2d25400510091400b011188403480c00350004013155010b = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 990992338 1250 990991088 990991097
    0x11e030b09041a010602030301050f100e03100608010c050405060a0c052107150c020d1b08040305060f060109030302061f05060d0606020111090f0f0d0503030a091a04051009021f 78
    0x1240782c0c00d01582d03e24058401d910242d841e5502d05000030342180307a40d4500b98440c8080e084207034001409a40003800b400383c054261000492241508002080e1621800400303508050390650040d204000307c0d003e6600040a082c10034404120032100409021800c460920502e920101c800407905c19091a828110901c55501c000d6803600010411808070441e00990401c90700000682c2c01090780302504076a407030060840441001004ca022080e40d40180140b200050040b0a00102081080c41105094404c00c4191540c2004452106880c44040c0068126201141d0560304c44000b00c1c02048100b124850221385527000a0f2071130b40324510408100b6541c2e4803c00500da02806000398150026103aa400c02c0354807008907141d0041d01200078840c02190403000305903550803903c158000d8000003200c0c1c6902e080d040060090005220540d03503021100c5401034012420030300d007882542d0010161069030100a401c8003d0078615500b2030788841c244900c08402c0b520b004035001501d02a07a01c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 990993588 1250 990992338 990992363
    0x150e03092206062d05160302061501020f0706080603070b0c03090f0109051008130c060825090b0c01060801020a180e06030d0f05040e0f091b011e030b0904 68
    0x1084000c0340e8241c1c1c400c900340702c0740000400b80300c07020104c1e0b404107002d59181c165030f03c402070310220b9013440f80d40c00d6404100720086141050507400218981f00f0040101000408a800401641e0740c03128802c182800da4020b80051020a101d1003a0907001080034048031843c1c2d40b504410300144e04040c4030004140c1c0046440d6101c1d00d003c0e5600301850780b0038240750440c0c6080201045200480040b0712080c44a83c00104004a403152400c44c80682c00010a10b80c461301c8800007401800d007542c08440442c1e0304c04440041030410150b4550000741503e43c6110646480c6c4c401e43d103500300715952141c0e9540d4480002c1d85510a000400408441e41d40d0888185c0c15035069500345185c80d0072207075150007941c080000b9a20000b644220340e1496041c4031000b52142c0c070342114a031103150040ba4000409205200044111300c0707038103003d15281c4c0141c03800c61400e8031651400d240d000c401180002d204092100703282c0ba40034074100c0c0030b0a075442d000c5951400c0c03401207081924190390440c0e81000001 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 990994838 1250 990993588 990993649
    0x31306050604150918080309010e0d05090603071b02130e0d0c111c0c060c03110a03090302090c0c030408030a0e0307080a0308060d0519050f0a150e0309 67
    0x410154001c9045600304030510b8480014141d24445018404a09680f0900c1c6100c0c003c8003002d901800d86e00a150640d240361040701a4013810442c429a503e41c8078896a1036803680c010015a01001d102a2642d803c580d298101102c4c0202d44111255880c113901e0003a401603140c40b10114240c481d001400314026031410301301460114040d103620108901210240b001501c1030100e003150a03012100100c02101d5807069201490340c10900801c46c9658140000d82c481e0000400c20225020381c13252588007030415042510b410480000034001007081c179051005180c54040310390000c00004503a41004040c155052440e4484c5d0052800d50f44007080300541564020700e00e100f101e0703090b800340030391a203051540d6070b0f1a40306030001024080004000b400d1502c03010540c007195900030040741c01450b2075041020300c44480080603140e5010340da403642ca00340340000c1c542125590050b4889414005094428014080c0c010503e00c07501041059803065591230480001c000e484242e403070f001750300d1030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 990996088 1250 990994838 990994841
    0x408030c12161e140309010605060a080406050708041a0a11040303230f120c090a0b0306120c030c06030907080619050106020115170a08040b070b0901060302280b031306 74
    0x40341800011206410f1444010350702c900701082202100080685a8840406942c05059290065500000d006c01e0060394136900c0841c65001e42d01440741000075850300c03a02190042d604540250103c0340e0001c80046841e0030310740c1c0c26400a002d40c0c00244d0500c0d8440449040d6101754825800240d108881480c0c003000301c9002e608212018030f11501c4d06241070a00791032030080c0c0640b0b01031020040c00051001555008889940c0e00091200042a403035000381c0c280d540065440d1030240f000b0b54102c950320800018150035503040140140704055580d410850fa40d0b100404600c083c1c0155103000403500c13800c2100c9400b40382d14000a943c00d00c40b940c03c2004079001640543d08581c14880d0381ca6652101080c071f40181c41c01f84524115200e401c151592410040f440300411010300040e001a1140c2d003003000c1c1030781520442c0b07400d85585425100d1801d861ba036010295010501901040e0503940100441090000300181080b00030340d50150400940c20495901002c402480c92840801403036 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 990997338 1250 990996088 990996107
    0x30f030f0601083120030708010522080403020303130603150b190c0b010b09010216030c060e0402070b0c0c070501030204030c06180e01032d05060115110106030501021914030408030c1216 82
    0x10300e0001c02040c5040412f1810000403003201d08400c0740d500d0350704424850032000300c602a43d005411241d0f50140300340521001c0c02680f05150010303143c024200c00d100d040b500d0b01d40454a880da445408c0880440c651042014011200010b0001c1ca00e10781000909098015000b401c06107049a1280c6402001a0920a011b004215180007451003800000c04502442c000d442d81480d24141101c516000719000344202d4070040e040c12501c1c000c0010031b000d680b0043c0319040030641951034a039610070040d0181d0080303010041030040715150034040c07944280b03081d20002a101c480110074a9550301155001c842c280c0090b10010800354140d410480c030807002652074202d445881818001d151203080e110391060190020754100704200038846031140b80c1904070b492121000308840c035a43c0c80c09a0003580542160312600300c2c40051141e44a010f0b0f0b250b01750a59050440341d28568966a440702581c0c0f000702030805a840c00d00036031154020042650340310f0003c05003284000c09040c400602086030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 990998588 1250 990997338 990997349
    0x5090a180c02070e1006080604241404110d020d14341e0207080d111e0304091e021602090f090309090612030f030f06010831200307 58
    0x800061250185e0241c4460007191217500e054110368481c44000b401801c850319206a610041c0300c0030b4070b4000c0c0c0c940213000440c0e4148800c603680c0d10a00e01400181e90403550403020306101404426582c1c00290009c00c020340141c200081c200e074842c801e43d4070f034940540d00d0401b002d4810124080001c1c012000e10104502807286008480412100905605002c0c03c207144110005040500307881c000c010782c901170180740059406844221a00030203d03480b804091801d881113541d203104001200105a03064002100903500d840c1c28010000d01030203031100540e120489402c111911030b2010300c040c0116000c80c40010010603024010089120340107403074220040e00000500200907000000c54440300800d80e4041c24981d41e0030001503d0410585004040d400000f070301e01240c2004034015441102181c0181455403600c100441c7c082c4001c9400704184544d4480a00d50344510301c0c3c40744074001c2110503001241d0340c40e07130318005210720a0300301070303081031f041c140c010820303c1c0510408000d001e = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 990999838 1250 990998588 990998609
    0x633040e03131a090d0f080c030901120c0e0d050f07150f0f0206011406040506070308071b0c1703090411040f0803070807060c090e0c0909010e0403020a0305090a180c0207 75
    0x25864014440c0c1d128056130603214003074041d8560704200f0b1519500e5940760708102d0070794450030451030558036980700c03603a080d00245c040360074000c0d15401071055242c43c0001d5955119000840b50601c0304014031000192024420640952490740381009914007401c00d62880319a024807404020b01403442444118061000c43c140d20391150358001212411142507044841c000180311000c03035000d100d140c11041c5c000c1400680c0000307040d04007900c2c5010398030701d41e03031103030580001c10065400804c1f0a400a001c9407c520041050f5514590144040584c0c40150303032520ba170940004040b2a6600101e0909040101d81002210000c101c840018007030040654030380115a0342d07030106481401c8000b0205a0b0b6a84000e400e58400c404003000350003006245201d60070101344800b0550456210184105030f81c1001044414a89503e00d0080342c0c5a00200602c141c1560142c4058122034070300c0b6008000d80400044605450551112000340b0300720004038005e070003000a0403c18036030003116444 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 991001088 1250 990999838 990999869
    0x190912050d08060f06070b15090705070f062405130e0304170a151b0915030e0c060a1d0f03070b09011701030b06010e030633040e0313 59
    0x10004500d440742981e01e45000c1c00142d40d040c002401c40c12440c3c540b03981000c4080303820003c001342c14841074001c04c40403e0314040d00d104c05042007414601101c0700c20000c0d00a0244100080c10541c40340c80c05441440c011400c214003c18825164180c000703040b441c00008441000b070f038101400c904030040c0704030364248400525001082c2c0e03a4819481134582001700c0141c4401e02010903c448103841c1d0748400c5d100d0070018440742d90800b030204900346900c050740c02100c007002c0f540a003035240111405680c0b43d06640500c24001d4008040040b440005405480700344c1c2c8050750391100801400085445021940213603424103102c0d0300e80802180e000b400030a21182d1565400110780c0c04a800128440d65035a40203401203c01041c0d200f440080700c0c0c00840044100300344030105a220300001e036198a0110104400c0581d41c91069034100103420079100c14100b0401c0d040340c03d04e144121045103a41400788078001c203040751a4284581c040f600046502000480c1c1104c603600285404e1005c0b0400 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 991002338 1250 991001088 991001093
    0x14070b07141305011107080d08070219020d06050a06090e010903020f06040209060d0618030f0e0a050a090e011107050105040c061e0809010e100f060501030614010c02060f190912 78
    0x1c0124062541403180a0300c3e003081703440c0e0400a05000d04609030070780e003c00194007070142405a05980401c054007403400f40c0b941070420f50364081842c40c3c0040020342150f0180c2c54101c0180b2001c3d18915038651030384008143c046685c00b580ca05c00040400000d0003159a090090801d624807401c0c5c2000d0700300304284005a0307070306142103821010445040b2400105860100000e201d101888800a204400f44a09054120400000030700054441450751411f00c1e0170030100ba08036010f5594400030101003031041d0030140d4000341a050120000203149058036038070b0206a00b0604084416030f4403003003000104203166100d04010005410008446000c0345180502070015812240401594400269070180b00b5001110074051f00015104080303003252000024040c2002c00c02d6085040032000034082d446445000100ea0b55403519030210f41548004407039401007000141d920800030304c01200d61003c0e503401420f6484100030300310703a010b15540c005044104150f0200110310b0100800c80003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 991003588 1250 991002338 991002367
    0x70b03060f0f0904110109090908191b0303020d1e051b0307020325020d0f0605090d0c11010302040e0c0415031b0c03120614030708030702011403060114070b0714 71
    0xb04903a014501e400c3d41c45c611001201d51070656070008450310308200358081840004001000082404040801c000302c070b2443c1502d0800e898008004102214030300c1c000428840c0e40074003154942c2400119200b6103041480c000c0c140c1c2809105800e40e0341d1010f010081c518000810613141c400d2070160f046250114010b0349a0056180316842e2a2142c414130305006000041c601007070780e0040451110044a091185c006144c064045030f18501c3c00012802400740098240c2030102559142c4c03140d0300f00380d41d801145160181e00c080c1450b40900c008107000e2110800300b03104d503610481b19602c40740750525000010b14118047d4090524218003c80304900150311020441c4044c1080260708000b8941101e8075241d85458004107840e00314080b030000c859490303640d0030103801c030100e860315501c5100c03ca03224464020001e0200304600c004180416550b0007543d88030005041c400d98400e140414051298008a41111000d40d170100b00800c250f0090041140752000c851060700f00801a407414030b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 991004838 1250 991003588 991003591
    0x30a03020a0b0a020f03071106100f27050412080c030f010b0a350c0c03070b15031c0210060521121308070b07080d020912070b03060f0f09 61
    0x24001442c010001e800038820307030129000c2504140aa95030b0b494255402401115010b00e120014040c2c0c002044942080c0c4074020700703542d54000005046890100c44424041c0003000d504600a2449004d02c2101100c0c40340c0c0c1d219502610040480100002005111034402000c41c55104000c0c400c1c072001e420407114542c151824042c54a80c1e800e140c030015a00b4805561030014600b504000350308d01c0c1e041480c40e940d6170101121012007691142034000c0ca05000d008030b5107030543e000b071000c000410090050590005089d031103200d414800800071a04000d95880b84441c070b0034120f901183c5107641040b60b124440072144082041c11704000015608104404603580818403091050704150010301500700400104c1503d241e445400c140f1040301d84400344601c2c4c003540940400061100c45840884c0c5400f0340c010001403404c42c0714460700b0000d4000c4d25803d43c1203a5061811442c1a000300144005450007032000f94480c07410701c0400c00c1541241903494002c3d2150135040f89a0703104c01d121507 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 991006088 1250 991004838 991004843
    0x180803071401020316050906070533010503060703022d040f090b10031e1401060f020a111c120e03010b01050f030c1b030a030f0f0b030a021009260c030a03020a 70
    0x32583c640c03051f8001100c3e8010b096000d80103010304e10101410070324194000d01580ca1032900c107003002c102115480c000400c24807a49405403c0f150005030854805e40c014400d520200320b6a01111981e00c00950140f000706112032a640c500041c14491000500c0f200b0006059011090214481c600046161482c004c61443c003455202c4a1441c5500311070b88c0e40c44802d00c694034040050500ca100c104a0b130800038400c1c540492500040c000d0028804980303d0300c82600b100c100d000c081030120500a000072407030070b44007a41d1001d04d901e10010718014a206c1d841013050340c1c3c0190035296032040500b141c4092a002e4103024080001c00301c6d80041da000c0e80d5100800c0210341c0d445214400c142040c61340413801c564200d010004503805103d400d64041c03080400b003c58100084048003010000702d9034125040c0da810b5020041c00c400501d092840180e010071036142c04030b031a540c1c1c1d420480300b082215080c40006c00c019944403000c17030400c0000001141044008000440403510042c3d110f40b80454003 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 991007194 1106 991006088 991006097
    0xe01092306060117040203030702040203072d2f030a0809150f010b0a03141812070c120317010311040b04090c06050a180803071401020316 61
    0x710388101010b844030594403d01c3c02d4001c03003503c001003017241d06210804c10740c0b0040c1c5a0340051401407485032148800280c075a076200c00ca20400f0101071441e116a445031400450b0300400003140c44048162150f403000f0702e41c0c421360554449001c06982da1200064210f40c181c0e0100f20280711300031240540c1c0d20006a0090045010300540760300e11815101c0c4010f0084031100c200818041400d418001030541040003441d81c9154222210800f9140c01600e041101406000d0032001800c0080ca0901c0c11140d6600d13610441c116004151465174110003660030903006140b95200211440780d0400f0075a034034500520207060301039915001d5405c1080140060809005035080c0320392100b00c0400240c02d1440c11103403504054003403020000e82d07088104c07040f031700d44070900b000c0d010f031030003440c0d440d0624207210b811071241d580345207802da2040040059031030b180c65041110070040e213007 = true := by decide +kernel

theorem cover : BRFrame.Cov 990827338 991007194 := by
  have h0 := BRFrame.cov_init 990827338
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990827338 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 990827338 ≤ n) (h2 : n < 991007194) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
