-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0700
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T21:13:18.932171+00:00
-- url     : https://prove2.me/submissions/061cfe9a-0d67-4204-b805-ed190e22f918

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 125719424 ≤ n < 125899280 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 125720674 1250 125719424 125719457
    0x403031a060328060b0c0a060b060415030e030d0915050106020c01020a140309030102070c060915080604020d060b1b01051308220801020d0c0e0d02030616110109060903 74
    0x2c0700c1c03140031140c09640c201c001821071504030351040e030240c007805036443c0000320320703003003900000c03e04980d840c4000c01841d601401c1c08811180c5142255100307c108201c20000c01008540690740c08416040000d82030725a55032460862040103c01401180340134403400800c21500d5030715400c0c0c4a80f50081145a80710b60050b0b83c1c580d400c0001e580035130710801e10580000c62845405101621541c183c0b800c02e12460082400c0e600020b9084170394000c154020310400c0c0d80b20840328020441c1481c140e08000b001c010242c5218405810303a8069500000c10601e00700c07250b00498010b08081511036542d0540d1001c540343e149079030000351419400c1c1808074400c0047d00681d00b8216400a48803441d00c201c03002c0308ca685980b44d0960074a0b41035000d00000b0850402e20281c901d4408908000c183c200e40303c00000d0412403041c8690f44103400849042016886c000750b03180c2e02c40c20700d0022100d40800c0325029905030391016141c400b1582458404403c0006d503410a0740010b2203078407004241111000c5 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 125721924 1250 125720674 125720677
    0x6020d0f09111002070801050c0301030201170f060f0f0a0303050315010302040e0f09070b0307020106450207020d0c03170304031704030e0d030305101508010e040201090b030403031a06 81
    0x6003980412202c12191803030407160101c08040e050040300c540315924480301d800d440c3c085032440e0300c40703201200400655800410712002c400012528050900e0f1800a44144407009000c80340a03045611040d85203841e0b04030208440c59004001002c07480d900d19000301250300032141c51004401d0031018400d6035010b030090740d00b580d010758a404225610310340000d420790b800500e0100d02e80b1406030009030450302035000310300400d0598000b20701c05084c64044050008141e161410b020450416102035800d800a0003541f452814130301300c1518021801c5101034000d100010754001400000d1400300207403808001e04072482181c1004038080c0b000603001c41c6000c1141c0c007a0100718005004c030104400070082070380c0701c0e1003030503c3c40f42c6a44220119003030600003481100440d6480041c8103c2c81c0080401c1d500800e8680000c0721402d640035001031038a4010300c0b03541d4942d0074610200b400c6a0140c3c1c800009000700f1183c598803442d003070030000e028100722103c400100351700b1044035003582000070 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 125723174 1250 125721924 125721941
    0x40e0a05060a0e160308090f010e0306070809010b100e03010c0806060d0b031009060b150903070e06031c1d010903020a050d050f01020c010c0801090614240706020d0f 73
    0x20081d00d0959075101040b0081c003065141c4001c00c0c0204a130019101c2c0c1010f070030300003039801070214940b074809038018040100b2a001d24503041c400d0a4000403950303500051200d41c080301c1e80c5000301a0361129018503004d02214405103a0100040c0384103401d56a20820744104031071f046000344010101a1340c00d90f50030000703880581c0c006100b0041d5603106407958010388083d80029080b0744c142d41c4140c0082003100d0f030744074048880b01d07110701405040e0f03d007000c004001402e00e03500c032902e480030503c0061780d0303024948111154840840002415031342c05105a0010180360030000c0c10100c0c03420780c01428888140c0d0591200041724103428001e5200303504101c160307603000d000c005080d41440200702c41510416011903039841007091201c4100028009005103c0b141c00010174120701c0803501a10182c01600600d0980f403510360704018006042c0341180e90030109603002026400141c08001c0503480c0740007030400c0004002554010005543c1c000c0c04c9040c0d0032802004048181110402600d1161 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 125724424 1250 125723174 125723183
    0x111210105031207050a05010606050702090612060a0f0608070b19020703032003130e06030f0a02060732031e070b16051c0207060b03060708040f020a080303090c040e0a 74
    0x1012034049002000080c144d4030300071001c0340c44180c1103036241401e540240c3c20000c00100003140702001c5080c075003040794001400715030021140301c100c91482d075112030042265002a40b42c2028072040d01c0181c2c4240b020300015000d40b40240e07201d002c100b44651001140c00940c24450b0400d101c510320100e00c0c0d41c2030300c3d410b80d54a080e80b2402c20401b20143d007844110030040c00104410905072070503c95036802032a01140504003498944209414051f51024a404c980c12401240c1c00594400b0210b0f141281c0c400700030980040d600e14030b905040a2044140302c0d503140010346a40144002014250841e400c0a680d00c60850082110989020f1500002c01c07588901c4041647c2d040d04421a10b5004928503141d4246641c510312686107840b4561010316096001403190284141030050103100d40c1c0640003440356080c40c0400130142000140058000c1201c000b07018210342d50120391100800700c55040701d0712400d000b9146034680d40100045889507150032803910646c0c10204200c0040c5820 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 125725674 1250 125724424 125724433
    0x110d0f02060d0b120c03010609090f02090c1b03040302100e01050703080901021c06081020030702100501090507020d090f0909020f060301030804090614060a030b01020708011121010503 81
    0x594244079441e0400d295442c40162558070b200740c25115001c040d24060620002003071031641ca0000d260840c0c5403600242c9906003000182000300ba420019031113641d90544a50328182e41d20746003481c02e40501052000c030125461404c81c585040000a04143d0f030080300d524000f14107681066512206821440d800305c0c1c1c09100d642d0200c0c0c010642d02e0b5100c1e8501c400907203480c0c076600c0e4203000c4007402051410001d55070741c0240564141084215803009003044100200d81501450303412422000d03034800303c114000000231b50024400c1c001401103000c0310300203014658640d102e100c060034085452100500c10058002034043c80360301c82c1011914030081c040a50303800c01c0003040c090700008000340d07041450307260704c0d42c201c2d216000150b0085016000068449041040705000c2d42c420f640200b0300700543c4d101406050342e80300107d1350840d000c3e040004d08441414010b03424107109034004843da505e08034203482c0d1890040c004105d0014500782d0740704168080e034042d0300c2c501e40a008080d0903a00 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 125726924 1250 125725674 125725703
    0x1181a011709010912030f1103040f0b130f060b1f093005010b0102070602011406041a130209040b010302040f03080a022806060b03040b04020603060d0501020d09110d 73
    0x4a8402280d082815040085a03840d085d850304100607565403900f00010390b4074a0340039000c4041d4030601c50900340c2c4901c0c07585903041039103c2210891070380101902c141003c2e00415000c00c000c1001d5603940750312000c1d003032042d40300c0c0c00d006009000481c2c550340030f04054080c0555952607a1400801721200c0d0321825111818180b0200346c9240d95640b0381484d080d420500300385402c000282e0321a45104000200310b15107a100020700f0311100d42d0244040d03a04025455a5211100c0700d480c1d44501c0a0314000b61b1132200800c202614404080440d401841c1d1244c1003010442580003880d8601081e107080c4500000b01004400302c1c845c601c50240d040228020600004403e030f0014941e42502c5d2046445409440c1030b0096049184034221280c140c00c01303001020040c15018210041941006c032905502e043d44070400f00c10f10082000b0f124010000000c1c2e6665100c904085030140c01c20001c646602e095261107000303215812007910902c50b01c0101c001c0f1480c10300e0101140039400741030103400c1070 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 125728174 1250 125726924 125726957
    0x60a080c0c0309060c0d03060b040806151302121b0702090c0a0e060316120504150914070b0301090605040b01020a030e010c0b041a0a050709030206070204060306020301181a01 77
    0x200050490a000d010400a0319269a140406005100c9a410150101c5141040c01070208e0b0425805280b0069050104003e880400b0554940c0070664881030000d24884d800041c10b0822401c145100c2c941c804180071a2001c0c8a8191a00c0b13410002941500c9109c80c0c1050a0381d405075060007036003d0203a000281002c0d0b6038802070100845207013000c041c240300303100004520ba00100d8006056104280311446280d6014040c8089201c861070104003504042d1100c07010b903604201c1849505132600304a4080041c02c6510b2506c900c0400c042d10541c50711590100b6642d8000e205414400b41840340208540c03810f84902184000144c00034400c00c040b581c1c064070fa61120410943c144640e0b002680c02151010010038072817407003003503003030054100342d8800c0369601d101a2081049a00e8a82000940341c0c000110105581d01122200e4594400d8070000f0040d150903003000b40114004000000c01405c0017980c84004d0740000000e0052248641003194003145e81c88095001aa80f40c108800d40c5 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 125729424 1250 125728174 125728177
    0x50414011b0212030c060609070c030305060a0b211b030601080c070b0c03041e050634020105061e013009050319110706050a050c0601060e040506060a080c 68
    0x814121914038481950006480e402c0100031210560f080000c81c90740180d000d026143d40701c0008c40d8504942c0c14001e40c000d149a01510f00101414cd859001c0b612b9039503042e000380010b15a80940a6031842c0c80e00c0c84210500e071410a003080200d0341000728a114485842c45890207110609035030860f500c0400464452202924a851601082000e10003150604041600ca0382c0c00e48030403035503410140740040c40f1055084000d0200c1484400c500005030b0003141c00764024a014a40f034110030751100d2000341c026030300703020810340851350a072481c141341d010b401030fa203d41400c4540c09007050159100c0703c07488041c070041c04d000a003101090624010040031422013662103500340d1004007001115142111540d4105640031742c00400c41111880352141508006111460800042001d50803900da64038030600910b030504c0000300e40c0080c03081c4640c05854a6142407011a410b5503510040603020098003100700340514204400944030303040100880384000059680e040701540c61405c1a8020b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 125730674 1250 125729424 125729447
    0x1101090806010b0d0209010c0c06090e0c0c0604031d0301021902060702241302040c02010b040e010e031c022a0d081510052208010b0a050102100b0f091807050105041401 74
    0x500120800588c08150041c0603030b00504400d44500c0102400c044c2d140f06005070040c04a80e6021003040800f140c601c000c1036040e089949030400c1103220180c00c00706040601040c0c19903070590320104080e00d000070b00c0100b50000700401c1d000d4030107503111400d0807611803000d80c032080c002902200c544440020101c0040f94410600b00000f01e0400d0705900190540308060300110050391a0003a0b0b020a01c3c01e80705070540203100600801840022150054407402000302200302c100800000348100c51441d0102c44541028090941d4020400360318000748880340c07003090800348100e02038190000d014080c61400340010518450742340f020101007180455800381100d040210038070a4555946203600c48080c4208031000c034052a0381416007882c21218012011440380d40c80d1402001580d8001c41d20041c403d00c016804030381c6d50220000f1520320200c0c008981e801907007130000c105038040d41d06080b02d400c40302d6109854040303656800440320ad000710701601e0100c6440c1d4081a2456010701040d001 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 125731924 1250 125730674 125730677
    0x90e07060f0c0c0e1f1a0f040b03010b1c0501051e042702012303010e13080301090504021918150b0f040608070c080d050a0f05041101090806010b0d020901 68
    0x59036003040e6601c0f0320410569001901e4100800b040c0310350a010301102805000c90030f800d01140354940140203952072402c0980c00c3c5160b00015541d6115555134040318050865201019034075692420020344d580d220803c4045040f2003c1d420003401812401081d040b50b00003040d04880c008842005914107641c0c1c00c0c403e90143d510b982e0300300c041501e1200c01c44000480100c04000042900024220940216003852030f1010078042225215500d8182c038151101e40800c800d0658076a04445000419104054106440030000040b08966900014410380c0300355181c01c2d12904412803c101400f281c0100c4e103145508180c5c51681d08400d510a186010082020300d0725181e581a8401160307206403050024088000790900a041e003140d00c0640180240c81c0055450651f600c0c1c0004500465601c0b250040d12000031407501500c1b074110b00083d80780d601040100d17091900d03000311080d080301c00305408544401c6001610210100781d8504803201809410718000c0c1c501e40201c003e501142c1400d0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 125733174 1250 125731924 125731937
    0xd08090f0a0b07020c010216090216080c060109060b03040f021903020406030503030a0c02060f1512061009050a0207020d06180f15050c090d061e020f13090e07060f 72
    0x301002041101248841c040d144030045070408400c024141071517420300e14150742c0104d282c0340031007002224031001c82c3c200c51401a1940010459091f04101c44138000e020b0031f001081d0701802c8403010500301d048030984c01040180b07640c1c4920b019442c6c00300315405000183c01302044809811b00502c0e289403260101d089a1115841c3d6001408485280d08145c6040c0e00100800c9206000c92141c5010100903000500c0140390007920b88004003030040001d54444000c006041050700e41d11002000c0d062034000388e50b000e1410040c40f02c1c600001d44900700324103041101068805d21180300b15a400c54019012540000003900c807800a052207545c030141c2c82c40c2c01e5074503002046a0304814a1300034480c040340090060031000d900290b44c406006140108010864402c071681c4403a00c4e0741d0005d610800120742451015075062110f40040c42101c0628000035001101c450746000070004041e45c0c4525200041e29840c2940c11600b413807a9003c039543c41900203101040c0a4251154040034525052 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 125734424 1250 125733174 125733193
    0x310c0902070c03061103091903020109080a0c0c050402090303090103050408070f1202010c02010b0604050907020709050703090b012115060b070c03030239060f2115030d0809 76
    0x1400ca91004800b6156480354100070f00c10040c16006460340032840907010344c158186001c40b2600c8024140040100f150700d1154581014002e402c680700c800d8000c074440d03407a038080880203850a5051030044942140302d5201082c1450103209070f541210303010b00214140a41900103400070700000d00107031000c5005011800000f41040740c0c6200c07040c45410000345418040001a0071348020900791015079040100f550306c15103c1805650807504226401031042d00c0780c003000c0e03080003026040256458100000c0242e400c0d09600f0142140d0b21616042080b0380c3d072134800804009000306040c5103001e0010102c0041003141e040f890f0405004000000e4103aa10004d210302d5030f002060446680c90b08140420a068040c800c03101c808500084903841045587c42201c412580e0800700c01c3e030312403800007040b0152640c0003603a003002d920f460741607502e00c01c0700803400c0c0d4480d00c1e0340c0c10314140e892075001642054010305102c070200030160040c03c401880c60820340d1100401007501c895842580380d003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 125735674 1250 125734424 125734439
    0x7060f02070305011802090112031b061d031c0506090103030509010908010507030605040f0207050c011b0b04050a260f0304061e0e010f0207230304030218010e310c 72
    0xc00a42c0402c103981c403030000f172a80c0705108000205900c000308415554122002090b000048148030851005120424840c1c62900000402c160f0985420000086055994900b40000100101a101400c10903103006201601c0140c0e0012601d49800001c1c00c001000000e0083d0060007030300805040c07503546103440d81021800c488044842000013a242c030b01c20480b50510348100729a03008120000d40c54041c05444403955400c580c901181003001100d14014071110f5088100401c550141c101a03072405c041c10019590650340d5825144c11034002d500020038036034500d4000403c0d913481040780c244000c419800c401c80d00003d00a84810340c80342c910b1942c1121000d41413a900084840000f0640c400340c02071400c5548164190a20310301c1001010007185902595504903a0400850701500a845549030f041d409180e01c004d4110403414041024280c2a01505d030580d010a594104280d40c0e809000070044200e004e21030851054075141e40c5101841c0709454001d41c000d10016400c103031b44e803d0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 125736924 1250 125735674 125735681
    0x607020a0b030a020304030f09030305070b09160608061008130b070210020a0c03030b0f0a0306110f0c0304090b090106080103060203130c0906050301140402030d050705010b100306031b060207060f0207030501 91
    0x3000d0f20355603400002c100030507800c0322031601025a2440c042c1c181a055a801801e03c2c032440c40c002e0300c00b503403660009030005001c1101103040b01c18414082c081d19902c081c058804042a201c0c0340c03044407048240c203c007501c03070f2124a12414541002504514054403068850500a04a0350440c092400064041108c42c0010074103001c041e034819101003c20b0078003c0880d406000300c18455682c40c1c0040036207641d20309a04040d00c1d0000400039228500c4240e00d9600d01c50403800c18002c610105207002034450100127001211922002841000c0b1110200901c1003000d0082001240080c4014804a0b4450380959480402c120201012101039150034034008019440b001e9680e4882c41c046c131413400c083c001e00b80440e403400c440d107000d41040d41c006071300c80010907c98410040c02195150520100b500011030366000540881400307000e480780200a0807a9020a44842e107564850302c080c40100c00100302180c0303041e405040c005081481c200d07428440c58806030114800d4140210201d0740a20 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 125738174 1250 125736924 125736931
    0x10e03060f01211b060f1e030e0304080a0c0e090f0d030b0f120601090f0501180c1403090307030801050102060f010509060105120c18031c0e010504180c08180c0607020a0b03 76
    0x140d031032141d5403034084000c200c505900030400402000c1402415018004072000c1f26130b02640c20041400185a5403c0c0d00d14001d6600c03031001c41c4034100c0c040052080b032201c07550640700350068a01d11651108080303541c41c6540e1606005540c03107035915110303c6119034005900c11000a1860780e06802c00e00000e040805071500880103504618010014035030340c1e00c140111441214804d20056141a080501c4490801c85031440141c580003051030407445418000200c200341a2820340700c4c10720b203608681d82c0e0031560080740490310703000c00403e0a40c000202a03100f440e020b445a00310760309102c14800c02c040081e02403414440c1c14884c5591503074244115900c644029101c0c40e4507003001024079420180341c128450f0280d0801000c146000340707007000100340d40c1d016040c0189484841b40c0129010b114907800658040303080c100c0681da0a94a0304141c201c1001e030390303074030308640c41d407c414541d0105070002d4030580d5840003404400e40d0400c1e01c040c01180b40010800f1800955030081e1908690045 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 125739424 1250 125738174 125738213
    0x50d0f0b1e01021e0c150c030f1908130210050c0328050f340602030f250806030f0609060f01060302030c0d09060603061505010e03060f0121 62
    0xa6071011465904001615510440c600c003c2024040940819200c3c9803811140d4003450280d586048601c405004580c0d00c0740c011400ca17992400e030041c0205044c0c200c8440c40c0c0d4006030300d01c2c5a40322544540742c0340d0302910302d40002e08200110b6900b0071201d8a804042a02840b9050000390069641403024002e004984281380c1a101d104c0c401d410038002802c0261420710200344042491400c00009580f039038202c2001110008224805546440d84800c07a40c41c801c58803000c0c40d204010494001e50301450400d0300803041c079200c02104200e01565001c00003d648881c0251000651144030b20942004003c1d058405036031745002c05030700340042224020600d6014000381710003c5c0e100080c07a80103010354a07046083d42802511401d0602c04c900700d50154549444030002030082aa00440003075031321040401c02d14800740c030b03002c40b4403844e44203c50214a81c0c11201c0e0700b50402054007881030a103e59510042d80c01c2c8444503074420300c80440a1101c2c01c014001200280103c1120020031104 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 125740674 1250 125739424 125739469
    0x70c02030c03060915090f0a0309152a061103010806061e0117041e1b0803090d030804140a0b061f0207140111010f0501031103060106050d0f0b 63
    0x5401410301c1c11441c821824002e070710540800000042c0429407604990046003035090945410710b030146000d0705104290100d01454200c0400c1640240001d021521058105808045a01000e44030410540740300c0450611000c1c40d01103001d10001c2a08409129020001e04401c41035424501c6402c00d0300003800b107a100b070382440807600d85007504686c102c201c0c0d182d0200c3c04440000003802910000c01210309669104041303400c220b44484510f4003405503100310703e0182e10504054074070340c0003009001c1c0044442c5802080c40071020040720f012060240032400c0c4003046a408850a01005000799890b40d04044608141007062010340c0304140124074035119410914104075583d00c0005d10010100c0c00e042e10400481e8000c5040380c1264480d4141c0c01c2d4003d455070042c0c8080030101ca512116510b00040e0b008131031001c0d03010307505890082414681c5c045900b002c5c0340e55900c1c00c1c080d0781c001c00c801b48aa2803241001d60080d170b042e02d19000e0081040f002420110300c1541c0b00400b400c480914 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 125741924 1250 125740674 125740697
    0x60406090903140a142d03011802130305160302010906020708061f031505010603060f0819020f0303040801050910050c180409020409030807030f0203010506120606040e01030309080d0f05040b0a0903080307 90
    0x2a41c9409a1b61005190807151446d450444000d0640c24032000c1130b071456401081000000808880810007150031006803620307044c0340155413014a50f14001240030451185020071028400a600b5090b101c80200a14a5441e20303641003041c0821120124420040304801000081d4091014036012030303000004641035040405c0941541c2a030340250343c552200490402c5036000018034684030030010082c0140b40b840500118004081c0066503a405100c001000560640154840c6100f00000c2c402d885200f200342080e1406d81d102a00e9124200c1d00c144040445e50005500c03074084a10001c00000303141c04141d01041c03d480780041c1c150041a05041045482505030080c0ea5100c2c03070800e8114a1503041200080ca00d000f904452044160128000340040d221001200d002d80310141d080b403a90f603500c0c50014050b42c860701a0f01e030503018021020340003a000368002e090419441e03e401d81007c0c00e041109020b90801401c1d030301044143c90000000c0786011009501804882d55902c04506 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 125743174 1250 125741924 125741977
    0xa0f0801050f04031d030106051e030105061806011b050703032001270f0206040806010302100e010f050c0109060608210c06010509040203150f060406090903140a14 72
    0x501c010045030300b00d1904003c110001c1c1d03211007400b85180c0e085000603031107003842002ca40103181a4100540200310300984a030112982d948100d41144210000c0c031032503036000c041c4042034180e1103500e0320311108040454600d40c0103500010111106007444408001c881c1c41301031030081c4560055000c105003900d100900ca11488071261030380e114900900040d18a00c08015203000309051320b041e00100461140200651040300e500c0258009028503216515208071580b10704080c40200c2c0b042c290200043c1c1c0d110f000351814241a01d058461a40c1b44220312005d8800e6840715070b602046558594007240000c1d40c2d8030402000e46104d00c0109280784d01a90303040d0f444000d05425034190001030051f00820580012007505503a000e0360115965115031021170700e854228241082985481c0d010070280e500401136541c81000102c60500009594085e01021104004405000100c18454081d24007481600410740e007001440c3c01c0441408000c0f0140f030300e4105c1d0401d41c483c0146c5e00c103106c100c02c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 125744424 1250 125743174 125743181
    0x307030f0305010b0c060c0c01060b1206010f08040c0e0403120c03060806060a26030f270d21110109030801050301050a06060f0e0a090f05060a060302160b150a0f0801 73
    0x1070503115041362418141c800c485540d510010100e007201c01000610b0504038200b034008a00418941200c10f44071541400720a80002d001c450040c00146d0b0007043c01c00b42d502c41c03034105020720b4014400c080303090704240f80c080100324000c100b0360500005081c40300900308107101b03082080b00160790000f0078a052220280c24010081d00c514864003994009000031402270780c1208500d00c80c001c9551104280c2c041c1d01d4198000c0030302c0040a007002048921b1800c08882001421840e4100100809500941085481841341d10084e00c100301c0c81c0c00761001440d20160300301142e512400c0c1002c000054401113401d6074050300c022800942c2c42c5c0010041e6040901803207810100401083c8111410018010040c1007440c001d8030420426070118800d54a40b0a8014090301c078420080c0703e00c20422542030050042a103009001d46080040041d2280c82703442503c070000b4058010203190403e540300d450000d50f024140160760400d004010040d0340c0c03400c039000c0013401c1c140304920146180c846040c0c00c5 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 125745674 1250 125744424 125744429
    0x90b13020406140612190510060e010903110105030a0603020a060908010b0405041110090806010f05120606030303130501020c100c0914030618030c120c010c18050f030f0307030f030501 81
    0x40154a2440400d6540c898065036403004094250b031704155240c0000f984c4000b03800c500004100e140006106604205116803415241540c50300142e0307480043c011200407000d403001916519480d41c00f40020741c450001190040003039480030640c00d4880c1c0006601d08580c1e030207040030034180b10040103040001c4c09000d41104046604019525203500c90954814048050501c1614100c141011031401488208090220a02203880170340c0c43d01c50507800c280c058082d103071240b45518403104c04404001038041c460480500510f040d6241c1c2081c2042d0583c42c00c0c0109d8044d502030008142c540b40801c90040c0ca0080b035031011481d41b1030311001400302203003034203c440c41d00070046041c8019100051441d41045500c10304240c214030700038280d402c5014a1502814a00030394030078074910581c4a000c0d1010907000402003052842c004010745e1a010342c1e218920a05c2e807611030401003480c284990005420004e030640f0160521040e403e810741d0300243d81100420101b80401c188280d05104a030f01 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 125746924 1250 125745674 125745689
    0x2031b040b0d05150603031c140f101a040b0708030708060a03030203040303080a09050604050c031006060e0f010e181006050a0c0605070905060a030615030203061f0201090b13020406 80
    0x2000703003507165242c58241d1080004d2152160030049685ea4404104807424495004021032440c4643c0d00b0160203003100c500050009145200071404011110310b60174050000b80a102c0c528520301a10684404801d6028407220b0200340030001c3c440f050400180350143c490100d0650700e03c0e10000c054480507000d48040d0040d001902c0901c0003c4d0004111401d40741c050400b104180d0f505001000900b80d00721004006015190a00007040b8002801d603500810890660348460701c140701c1c0c141180d030742e44554000156060701440d010305100d844018040c0043c5420700700c20702d510021070911403200d1098401e491009003000610703466011468090451842c1003480e10214613401000e000c400c02014040940d20008521850300520035103000f08006860543c0b114020900540184154401e00007203048980315840502e00c60310031240319110003003020030045040b40b2803c41d000d120072220070540d9a01c03680300c008134500d05040c52088a0750700401e00d0829440c810304c001d458481d480703250f = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 125748174 1250 125746924 125746939
    0x30a060b07020a0b0d09120f0e0405070c080702040e0601060f03061e03081810050a03050109050c042739091404020919081b090a0209040902031b040b 66
    0x60340c8a83d00d05040302d400b031800b2602c0c2c1412038401e50003005009801801c2410340c504000220350081340135045000036803030f84490010720400303010583c3c0307045a0881c00258648030b01000190103901604119002520004484e00780c0c0048601e415020381005020640c00740d03100c28201d40c140a201c001d8001425141c0504080c1038031010051181e000060400c2da010410642d03050307501e01c95207c4083c004155441810005d40064003d80c0302490010000f82044d0012036010b403079000b014024409034a04600d00b0785030400790f850b0842220115000c007820740c0d090054940b210301840701ca5403c1d01221041020b41500354000d9116451201580c0c1011545500041500080e0907802c444440d5400000c1582d0354001900921515407000e03401050703080c40900140c1c84000303076020380d692441240da800a40500e50701d05200810100d6600450350710014954000030b80107020341342005480400c0342e14182d40041d04040d61059640c501c220300419440e81480c1502400812043c1a09d040 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 125749424 1250 125748174 125748187
    0x130305040b0307020c0301060b220302030a0605060a081f140712020c03040b070c1502030301080c0103090606080609010510170a33021305060a02060f04140f03030a060b 74
    0x140240c020361040e149040804000100000d00901c103085501900a00030070506880c0e2001005a41050395003080d00d03c4010244075407440340f400d2410642c7c0e00200200403c0f20a56941c02c05000002d00d002e40191a1003000030300400c00f001480c4201281c4440078840c400f1300e241c40c03000c0705c07401100ca80207203004106020040da004046010b101841400c003595a49228249a01d1413040b0b50040381c00c0d0300c00285040038000200742850a076007604d8103660100303003d2002240d1380c3c0020300640741e1075000352450195035800303a4000d01c00720380b14031000f0410954641025082000032119903045d80d4480b000c004441e00000c04420280c200044140d59034210f084020307548202900009048240f080180302c5589a5100c44010820000f01b0f48007100112809075006500060a140d5010680c4e0740041380ba0703e00030041e41c2040031190300514965a40c5d00300845e01c810064826507082020400300400c0e0401840001040c8640d0402103560b414883c4071002200c0d030341d9003c08824001403044 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 125750674 1250 125749424 125749427
    0x60807030f09120e01050c03040f260601210f080910080705070605370f02090105030f07090e0718140607120201320711030a1103120106030b03061303 66
    0xd0912141c4e18042c030f8402407000042c0c0e00c1e80300e100c2e103400041c407000c5000a04000c4000d0140e05551081110b8600f29080012038400c5c0400280001005c2d0086001481040700300ca460040e0f40303101300d000002d501030f20380f10030307109115450083d24010780000b84203401c1e052600c0d13104440080b0340351500840c0713000c000c000c11601445600800c150340300c8020070301080280084a10382e580303c1520f00c10080340381042000405500d840f8015103400d007440e000c0d00403c0c41c804c2d6017040c003060b15154a1a070302c451b0074568003e0700800b01400c0c40380000700450300403011007030b151107014140c8403c203082c0101032a40c805115564891a00b00b407440c407a564842d11054240c448642e4009001c2010503241e21040e405000c1111401c0201c094401d2550403000c1c421240001c9008141d0840420f911840e2046402c1c4541c038070014425801081404e400c18030840c95007080c03400c0c240583c3d0911005d100980513640c0c0a9104c0341c0000e40310002c81e041c52405220030354001d402d4540b8807010030102c1c0c0e0b0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 125751924 1250 125750674 125750693
    0x170a0203071a04080d080402120102090604031205070f060204050f0303090607080703170406060311031902100c08030f06090702030304030207051e030f0d020c03030405090a0506040b0a060807030f09 87
    0x20182d682c515590b42035101c045540070382e406000c10301c0035242507180044008001a1040310181d00c21385004110030400b10042c4200e034441c074005444903151600b0343c0c0760200e070809480c1800301004800c2014030040f0301d0000f0b22004c103901c10000941d94030f03d820108280034603291041486030b0010441e0b02420755880e4101d501003548051180c0d214102400e00b0303103001c01c1d41d035005c4144c0100d00c000c010412800c0d85c05503090324410b0071080e95007104e05051596034040f9281d440d0041c0c0c0401c00c005d000d45002d4502e24034000e01403a1412298000342d1310700519030000e80d00503004007062003e0003090325200d80d101e0350260061000390308510309620300940da0501441054081e4401a201c003c00c102d40700610409000082e044036882c42d10310082c03959504007100c668005005601442410b85008003c41e81140d03000ac22071105500c96820b40c134028103010302100d41c1700740d584040640d251516846400184004d03142c42c9002e10708014090160369101105440d02031508d007900c0f0020704440f8 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 125753174 1250 125751924 125751929
    0x90c09050d020f06090a08150f040506180c060406020a110306060d0b1b0703121407050a1b0501090f06151206090203010e030310030312021305060a140a0306170a020307 74
    0x1d607050395282d0814085113882c4240240d564114640c8003000c5500c010000d0080c00f440c00c060140f01195032091040c042c0e03884103441c000e007070341c01c40d038040b4000383d58a1021403200000c0c0700540d9210145e013400100c00e64440d0780030310096040720711070304107000302d05c40c0c032410041c8207034040c040b14944200028418800c0003402483c0044c1400803500c020b00c00342d4102810002c009a15645284030705014080c140134176128181c141c00c202d11710452412003020140188040d4490906207a52050309a42c21003040c81c0002242d80900490404201300b405441e61003401684401035601103800c20741c059400403665200d42419a000404c00018440f04806d11a03801c2080041c20800741d2000a01411f80b0302004105448040b00780061201000030650859200e0b0f100c4001d140c0e1a07225803009c2e4010605101c91000400c6003c1115080010007010880028a044049480000121902c03504030084150000742d982c1c00c1481042280e4000f0b0015044140041550070311642c0000e65407601390 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 125754424 1250 125753174 125753179
    0x20705010507060e0115080c15090409110a0b070b01090207050a02060a021603050102030a0c170402090c04030803010f05040e0a170d1d010c0e09130f0309150801090c09050d02 77
    0x1280820f00c501603015144180820307000340304840315003103002c000400750300800d46640030700d406103200c528100511a01c0c84c40300c03590480c01e1407c2d404c00c0200030102004155003021b00400d015001d60b56200c645000340014002058849016003002002d44005030800c0704003510410148000c151300166001030550f048484a5807100c81d2402203003003000102084444900d018004000c03c001074018500c6916019020008215002c0c1c04907803503201d04c03188005020416011030058100f00740b01c1588540000c503440d18190f82da98035200194000d900011820605400600c02840c080c09001c00c0d58040d02c0040c52040300e20740381c1e84024080b607102c41c00e5120b800101c3d0f001c10800c0d0b03080f40950280503041603042c029448d05180c0a03085900003500001c043c4001c41800b8a003001d8040d00400c0120f031940f06400032170781c4003d070f0503013950000d0b400e01a28110000c2d16002040030a00c1c01081503540d070149502d804c05800507110011150010302151060074070003500c0b1003e5480256804 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 125755674 1250 125754424 125754427
    0x60306130f03050d02190212042402030c120c0d080c0a080601110304080a0605010f0e0f0703090206210106050a0e010518030a03050a0e0a0302010c03032a020703020a0f060207050105 80
    0x303502e0191024810304440e5941c490000c03a0b05408202000048a4500a41d0b0240d03401c81181d80c516402c0c40c8154000d00707515038641980e117040c0c201141d514541c0c4d0410341c01100d1400c284500c00314a810030b400584280d0760710019030807108041c140145110b80d0180c2c02c000300c4c1400e02100e000340b28020b000c000020003521200240480e0310883d14400813941d40d6090702da4860710b5070400c80e1105107400c2c4c15036055040a0001a1460003402180c0844002692542058541e4204180c03070311400b9001104050b07d850300c0c0b0002da03860350010b00c172003001d14012840c591170158010801d42c5e81607201d0000e02105011140c2d00540014910f100e00109103070455641140d101c4030342d000522200300e50b0b01407241a94800401d50000c0044c49070405030345400307550340d00c4841000000d0905002c000c0c0040e161040c0c0d980064002c0e04403041d043c01f030140c40d090306281403074807c008003d507416480040c0c1c0160010020b42c200740d04424040c02a003407040e03040e0350074184069038484842c46201d040210 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 125756924 1250 125755674 125755703
    0x6030a020d0902102a030918021324020105071e0221030601080112080d0b120607020607182402070306020c03280807081504060e040b06030613 63
    0xd65500c20114a80d0050190a403c4060b88008180c0405c0c010031148251548607441e04c04500080c0c410050b6a040da68061024200400103841455002c040c0b80c4070781e001d00c152640a03202014120140990303040070500605e4540d150620070501c18203440940e4581011300c034280c1d0f4020780340b10f96001c11a0003d50b510380716000480c0742140569001d10f500380a481074501c0c0c4001c3e000110700891003640c41f50303040e0741c070381441c0390403421040c070010090300080110f50850040c540100c588428000c10038045100e6040c02641001c80440c0d004c1d0058000c07070108580c6e15008008120309100000d990415542040340022240d030420070340070b60f02480b000780d0310a4248204144000780d81e2003e1709544490394664000c1c3e4a8100d02c0c00203030320b8118444001a12100c800a0b02c48684a50b5030b04302c119168160195002040500f907809001b07100c080b03116083d1540e004a02c010000d0038650741c403a18041c10318400e20380004d00030310300c60780141003803003000402c0704483d007c0c07690006d0034202c4140 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 125758174 1250 125756924 125756947
    0x2040b0303120c0409050c03090709050a0e1b1905090402040203090c0a060f020c0405070e150904150504050603010c0801061107170a06060b0901020d110a080721020105010506030a02 80
    0x9441d2842d85164050b00410024403050300c00351080310f000e201c0600c002c0d00c8007011441c1a0004440012099101403410012030341c06822854022542c0500040d2800000091505200c1c00315286600e40d00880300220860401d110740003940030b01060350b40d0f900780c01d08002420001e0f0282011b03115580102c04525440002d001e04c0e0390007100101060300b02075840d5005850402d5031150140940181627024500d820107000d030a01c1202d250340c0f0240341d8800340c401c2204001007012040c1d2208028081e200302c0c0d40321445034001e04809200540e645038a00300401081d20402003a80c0d0080c2d06100700c42010036000500c1c80c2c151100c5042c4400000e01501d20a032600b183c2d82d10072203940754512241d940781c00000c40c2c0500c0b0280101424802c240c0ca81c1c510368200c1c0700341d83e11640180c0c081c41d40c91440c54450ac4852207124000c00c01d41d1080d041640700c594035504044029107002d080c00f8010211fa18280302d100c125440113000038400e541c58940050001c0c0401410801c4940d0006080d40030718 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 125759424 1250 125758174 125758177
    0x7020d06061d16020a020a0306180503031801050a090c0501140f0f030601081503210c070b090a060e011704060b120c01090503011a04240303030902150a0c02040b0303 73
    0x520540031240541c0c0200090031116020541c0d0981a4a20010030201d20900c08200144511b0700134018024546c519030b6040020903211913110a401100e419000c00258140300550044220424040103044541c010740d00b140c001812410055140410440004000904010407a5824240030260a800110f004054807524803003480421001509019440d210b82c0610701a00c0203903a0b02003159201300015035900c208074260359048d804404c55603040841a0111054102c000140d00c1c20490003207000e510b414074030b402a04104c8004100d0180900b400d603207100042c0180d1520f0683d074003140d4006011b07800c841e000344200c0e01e0480c0000e4140600d41c1c2250801d68005810b51602c650707032541035600c503000b2a0120b03000a1480c50300042500c2c050245020101401200784012880c00c020440185103041101020440c503401d550480e920340c40c03219001358041e46011034540110b20400406901010701e5084412060114050346640900580e0040e9816a4001015256400040e240d03 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 125760674 1250 125759424 125759429
    0x5030606040906060207030c061107050603060409050303090703020f010906080a050604020705032a240a150b030703050109050f040f0c120804030203010b0301090210030203070e060c0d08010503030f07020d0606 92
    0x40c00c1c03d00c1d03400500b4507030006002c01240d0140846481964031031104440c084015100b1040d0341d80072000a0049280000086400c803000420000d907000c1e8039900e50741160011510400a50031000c2c081081d809c00450041c200e40092801480080c28101c000d04000800ba007594549651a40000c07121303200e940c116260940c0050403071b500c0e500d1809107581c00c040720079808025200d4050342c0d20140b007000607080b45900ba142e4000c0c07800606c04c0c80354025a08004242214644e21049440f4410405400d100003400c501d4800a030f4902c0c00600c046d05480b01a4001280c0074540300420015072195546240c2041c1d101800000c030311014204483d2490158001c1d040c1400e074090303404100440b5400420031284240c00078051070407440e0405080f01c201040c045d40142481c0750581350b00d80b190340256404050341c18101d40440c091800304c0c055410405e00c202140d072080080060468021303e00900500085008501d0f0480d0318080803018094104003c5c0108030b80360a0b50108126500040c01 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 125761924 1250 125760674 125760689
    0x51e0309130506030f030414040504062c1501060806010f0c08040f050114030403050301060c0c09020a0507050609060411011107090f1d07030209180c04050f150604030507060503060604 81
    0x32055440702488000700400d0301c4580c8248184100458080c80200a55084600c0c1d4226a00942061300501c405040014011900641d40d0425800800700300c005006018840032406680a00080350b11440c00c3c003c0d0911240341c101c40c400400405500030f141d554072540070720b803498151101a809403034100442d90000e00d040300c040390200b140ca0500d03401504841090b40c03a9510050b24418001d010311041d0b50140004e40208018001c04d4003c5151020840c07107800643c4009a4070f4260204980240f04041c00168000811806000301048882e4000c2e41e14000392400c1e052582d0f422001310b48200103e0b0501054803290120800240500e100504520400f8408041100241d100500070620385a1400226203e100828400002d200d01500d5000e8280401030b1140f0504440c583e030075116014092144407820f15494803603005542c024100038000d00814200451503402c003c032a0080b03d0b010307200900040011450001d0008100c80c418100141d036500c6180c0403c4491207517400071207 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 125763174 1250 125761924 125761939
    0xa09081303030f021002070803060f0109030501020409020304030305010530010605030708030c01050907060813020a0503011d0c0114180d02030d0507120306061709010216060504020f0409051e0309 86
    0xd064100e4000b2141d42203039800c0e114a85ca403031802d02d049005076040900042014400200581010014140d070b413001418190f00340c1c0c2d542e03501c0c542641c1c4990070428050b5000b00c1070008043c1c142c0122070140504441d40c440800c9070744210f4050a9401903002c102d030790307840e00400d1000c02c2944104007421003e0180c2344529103d280c401e542c0d50020b051030101e980381c02c0000f00c02100202e889070960b21140d4420750252140c2040002c0f0240c980700503030307201035481000500c0766402d00c110300c0d80d6180c0703208490144000c10802c03420b20356003454031030500100708080fa80c401114011a03c80e14040046840c04124101c041102101c8518000350140300b08001c0d110b405070010060310080307104100600403450494030440544025104e82404518030150885c08607080000203075200c50040001420844e90a0b000b11900d80c6c540c40c00d4910555490500c000e40c103101c0c4005180310010f881c1409540320594990b0360392a20584103420810000442a441c00e4050013192001c0d81c0080010 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 125764424 1250 125763174 125763179
    0xa150b0c010b030618060c0a022a0a08070807030b220b090706031509020a18060504080f01060b0f03040510020708181504140604050a0326070203060a090813 69
    0x128020080551403034400c0c8600c400184041701440c1c1d041090b42c0014002c0c041c02e40b215006503c007500010402c10070b50140e100d100f250541c800c1c1041e030274070b04403c1544020108174814014003088a40001c1d40c5500700340018408910002185170850740d020070700700c000f0355412000d440000c07036607510030602081524a0006000b105440700e405100e482081c0d4a1490791007501380d04a9008000c4c043d03410403041001c0184054540c003602c0881002d00f4941003c0000700c80b41d030003844081e04200003044002c1002e00041e0780401401a5800485008000322800d0842e0f080050040718005400c25200200080420105010341c0e1100408102c0a64585007580780480c4a40c006c0d03150590218540d8901c0a01498507150303004001051602252615090009442e4100070b5210500d8000c40d04100005250303c0d10004000110f002c2d0798540800303072140c1c581c4d082515401021104250b02800907802680d00840c016402204211002415032081e140c5400103005d48941c5100c00030540100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 125765674 1250 125764424 125764447
    0x10b0a091d0a02010e01120b10080115110307020f1c0309031109070e01050c0a0b13030201050c071e0c030204090506040b0c0a05070f0807020307080309012003030a150b 74
    0x2203041001e0038285060600490055561402103402a000480306110304013294050100e506c0440e08140d0042192440340e404a1080ca46050588002038a220010030020180c103d940035048010b10703041062041e0008125a03074001c04601078410701c11043c0e10795941c5c2e039030000d07040801c20902003031408618a003400740003021030f0710064800383c00c021804140d910f440214148210456110014062502401181c81d5048500781610030712500742c611002c2200345541500c605072420b003a00304042180b074003d09490020b412040804410702500740080c80402d640e103801d140940d02c00381c50040c1ea0414840c00402c40d40086e410070310780417409080c00404100b9501c21401001d0003070868803507201c0845d40c0d02c610780b000b40001d5000d011120002d0301c2048400052802813417000e060041c90b80010307050a0700c65108140d1070b400006d60302415604403c00b0540c40401c003800c4042d090300252096124030004154090301555030700c1c166407500c80e002516014005125504ea25141c89084 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 125766924 1250 125765674 125765681
    0x20d15090b0a060302030d301805030910020607170a060504022101050108060607080702030a05121306020a1a0a0905010c020a030801120206120c220e0a110417010b0a09 74
    0x2042c1c0c007034042c90040c1074419020700b4001c804400700412004030780c865070b18213030340d1aa008d0300014032032511204c0d8451804801c1521245150003840696a98284082001044050704407060190b401003804c000700d03240c12028103002d2440541519910b60745800805c0b004041e5900032a90092000c180d00100c41c00e81c0307207454034815189206540d07590b00ca03001034402c19030490b40568020010080c100001d910703203015040b524030103800c0300c091744041c0da10b1508003400d0703402c1c0040320640404d91060b0b507410351040700700501041c0003401c0943c9142e1118103c1c050001c11802480c4224000b00300500007950055070155000700082018a1443d032000717403504c41700201900014854400442c8100d0700320700c8044115801007205181014800202e0803116004058422480041c03081c0c0f131941c102a41c04c1c0d5160700c54840350488030742c1484404d070b0b45500c0c0a4040c20314149030001a0804110560031601078459540e02009081000c85406000d0b000710303c40f0075040383c0081c40010b82943c3c03580 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 125768174 1250 125766924 125766929
    0x30c06050a050c0d0e1002040308031609080a02010806030f072c0c0703030b0102030d09050102090a090506210309190602011b0503060915100c020102010c0507020d15090b0a06 77
    0x244248460303140c100e0010203403001601da5108011041090b803407003600d0740e8000202c100c000d101752040c001c90004100201c0c1c229901c207481c1020008101f003000d088480e100d0940401c2c90400c2115a41406800c0360f444400540003810b0120f00c1c2d0108a0030340e01044840c8000c01524100c902581d00c3c2d00303c10725145002e04490340071512402030030007000c0d05010755921030382c00e981100e4100b9105131402c6001e422170b0701020707043d07010410407218940018082c0d402c4060180c0b001599030031005c07042c0196207440360b00c51f40880c0d1802c0103125080d17540c081e6100d14a4200c0d080e070030140c034103003002600354850300c00c0d40b9610600e0305070300b100000c0030740140c0c10458203560020803804400070a06003080080308a108000380b000c20004d02d0310320740a4056608224071580301011142c442011170480400c01038010081740f10802000215a4240502c41c988030203890018188640c55010807012030440000400640c3e07142039180b444c009640c81130150b01d4210aa0881c0b80c2420070b4003900621260 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 125769424 1250 125768174 125768183
    0x15030405011422080f0405060a0e030c010c031709100c030f05250f1b06090b01050a1202010c051002070c240e0906031e0102040e1b040509070219030c 66
    0xc41c001068a041100f032450004071030510031000c0001d681d1581e546a00c00c80c1c0000940ca0244030120705502c405002c3c2c14009240d84034902104d03920810903103408030b4642e0007410000c400070b0050003c0c0d031040009486e507110b5140300585458100100e4140f01146001e10500c9142c403007000151641030300448a01c02e02c207201000a0303190190f5980c600703090940012a01c414803215804074034894480b41840360268680310081450064141c090000341503030903144551603000607428030640c1740b001d07070040c01c0840380813403518038204520464903009080a4140020500c3d80404d101e820310031801c0281500703000b1560742841d071410380070b400094010300c540c0100790b079001a094031f6101c221154203209500c031486040100000c1080b2000c0c01440b5039018000c0690074080a007039140c04038094600c0500140e19503040280ca0104040028680783e019101c001110301c0106413101100d00340c4070181c80d00c0b4010740d00d02c1d03002c0c0d00c0c1c40900c9a8109423003000c81819030506601c0303210f50171098401d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 125770674 1250 125769424 125769461
    0x90218010e04090b27070509060d110901030c06021009052107060501121a04030203030f0402060d060906091112010b13080304090204090b0118060f02070305060c030601020724030b1503040501 84
    0x2d90b200160b403121b40c2e0180f160020a40c4000c1000c0d880d111440c00c071000d1141d00d620341810711100c0400c0810600383d00844c3c40c490390b11028425141c05005502c2c41c1c601191041086005c50f480d021340c0c0300340654640700319869410f1420309a502c0074044540d100d402100500c450359542806901070384140030281d8046161040c00051140f83c4d20742d0a0165815600031421a01c0314103200340c40e944083d00481c5e0110040100440c0c00496019810007861307171941c002100e81c036100c00101601d24060b4108280302d410803215402d0014bc00c03040e03054074090f2040c0b40d110342c02c100100c4d081003d940c018a40911011030000b40003e02c94000b0025958a034005002c1d5010300c00040d104400100f8510103010141074047c44800e00c62a200c0351540d00381c1c4111000329540e6164241000c8050b140c0f503021190002c2049441c0d40c04214440040003000d465000e21603080700d5410220519600c100100347d00c42d030f02840c2540d240b40301d45426800b001503840d520708081c50854002d10091282c003205220 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 125771924 1250 125770674 125770741
    0x7050c040e06040308150105040e0f1506040308040b1e0d090302011505060913020d020a02010501031101020a0c0e040206070602030a0b0405010b0903151e041506090218010e04090b 79
    0x100402c21500440d030507100e5000030740f0780c0b060f150340a0303c510310a141080401c3c04002650032455034601d000d0000703913030801c9082c1404001c4000c042226100107000d500d04000800008040204039030445800102c100d403143d03000228078030140c440c0201060182c4011500249403c40c030751140c100284130350020800c0c9040318000b9480007445c0d00c00e0301e074410f200f13104c1c60441c0c0c00d0540c2c0e80c038a01c0e4a40d00c0014a070500d20b1301c0c180102d8000c41c1c80400103039907800051081010707a44050203400400d00051050581330341e64a035030380b581405040640d01c11400820708644951040c1c0b9440d6610079419500c900e012501000100040b803146440b0364201780000401c03000c44c8040321751b00c00300503010300030b640390030380d0341b120400c80c0030b0318a60303c0d240300300c6090042403503610142d405540301d00c03851007065601d14086405d40340d094000e03210043c810050036400d10141140b0b506000000e00b0445140d4000400280041002070005003d241000c403c01011046001081040c8803400038110203d22 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 125773174 1250 125771924 125771951
    0x7080c030c0604050405151306091d0304031e05030a11010b0d08090d02010c05030a050405011106090c0f120d091a13030609051c02060f01140906041a0607050c04 71
    0x441590729250049010401031000d0304198001a600c13580110031000d600e01c804010a50966605503002d480030703510801801415002c2c06005480d90388410300790400c406218480f5200d12441c4030041104848101080300d40000201c2c01c00065042015651500c41206018181841e081c80c907050715460f040461103107291445900f446c40c0d80050f40c040c1440020b0b8188000d04025040a03414814000052000140104010480d5030f21564a5a8845c4e150900150004150301d85021060300008200724001900154540350410100d0303541800c1c004620200d8203040200111420b54003803418503c2e6426042071001c41101d40500340402c185010250500282c01804c00c030b101e05081c3c022041003c200250001300f1964020020381d000f0b52004444000500b050107071042c0540c1106c1c00b0040200c10f12045103004018600700020780c8403c010000d20070700d500070b0140c2d100c0ca40e01d070501072aa50341180340210300540a00290f0b0384441c207042c203a03a5504100c03182c0c0d04c654240244031103c407 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 125774424 1250 125773174 125773183
    0xb03100504052404170d060306020c010c0206100b1912022206020a05071701060e070804030905041802090901060f0b09040507030c050708070312021b060c0a050a12090f0507080c03 79
    0x45030480e405d94070780c001c12440e04603a41e21030900120f009403121008404180c103032000304012582440000780b180c01c1414040d0600900030610103185412260402c54843c10b0022500c080c0760703107400c50705051080c4800b0791318011501c005120107072000c900100003c200709580131060702a0f69206407001d66400040341d940d80741c00310040c1103400100040080010101060211800000000c41c905407503200080c0c00c1d840440c0c807400090600c0044c08103154004005a010b0203060301c00388400d841c0326840b151104000c040c02806070342114001204000291710000240016521010076250340384580511508500903ca201da894131012588680c00717842040c00520003a15041d04242e25030300c48108075000139000b50288803c02a10f42d001e440c25100820303a0310780c840b94580d0f8803030140f00c88501c2c0c110000d0901c507001008120342d42d95950460241c071a440213074508420b1a4550700601d101400720541e0081280015a030304404014010407503500381c81540c0100c8003020031781810941d44 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 125775674 1250 125774424 125774431
    0x10c0b0c0901080a0c0f031512080d060503030f09010e0f030f0f010b030a0c0b0706020d020f030108010c020109110621010b070510061503050a0b0907180504050c0405040b031005040524 81
    0xc142010301d41c1900c2c500a0f00300c0111360404c020384448181d5150040581003011040880d1007400000f8203070102c070660710330f28010344006c0d0700450500d40000d000781c0c154490a80d40a050200c0600410307201c0c0d50303021600820030320190582d0003a07610b96000070355842c8000d503601d20550034080982d046040010b2032418858000205115061500d070148403154000c0a080e20a90b0b020072052481a02500080c0701c46400c5284495581d0f00d400c07034140c02c4883ca1760780c001c11a4100328440b000f2580590720341e50209003c0750441d68503031094000034100180d0714140010341c0307014400090460501c5020b84500390040d07090b82c40b5076241c021060215030307c500800407202151103c3e0610760b44a94082c0e82d0002c613802001a11a101d82c00090900d4003c0318032000103025112807848041d00200b000e401008161410b0100b0304010441411900490045600031035031104220071a541c200158006202002800c0000d410541003054440c5c0001111021a0b030018010500500b80382041030720 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 125776924 1250 125775674 125775677
    0xe150607050606090601020f0319080601210c02010209040e03040303260a02070c23040c0e0f040f1b0504030c050a060203070f0321021206060a0914010c0b0c0901080a0c 74
    0x40d03a83c481e410040d4071341014240604502c5460440f040d208003c01c0100300d52160141c2300c0b07880aa194900030500300006107450704115011030304003140800003842c00c07404014150081007945c52103500700d0090054401c1154040d00b4800c0241d00c0800c040000c100360b81c000e5942c2281d0020400040180754081c03010051810b00c01d500040d6010b0b0198013621040d44108651034009d079032040501e400e15400826009807a0b5999202e0060b40792511800d111002d00303041c82c81100c606c1400043c144184103000502682e201c000004480500381e0203130300c156680801c0c004400d06080c0000f000740e00306003c1112061807401c400f050a11380202500205d0300b165005602d000b1460b540c8801c1c444c1100b200f101401109070071414504040c2c0c01086424140003401030b207401d03103031641080004020749190b014407401c01c418054241d200c0c100307400350b803200412000b10504500048035808102080078149906407011320072071090b10320060818450903620a00da03a10b540b6280400c80e10100b09480 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 125778174 1250 125776924 125776933
    0xe0c09061207051201030501140f06010c0b042111010c0201020f030a0902150309010209040609061a0703020304050916030c170610021e01020306120a23160e15060705 73
    0x12141c020100d04075806195458001c4c00c3c0ba6921281072403406082e081110782d40d444585a1660242103941164400404011202c5905083c800a0b11001c14003201804070305100700000c041c0b208183c1e10300211200340808130101c140342074000381240c14000d014541c95091000000c9080d105000b9583c4000c1d00e991160314644031108044010308070340d04101c0e00b1410201c015012441242e01552056105000150b0f4801440c03007044101d0309285c00c05207207540303010b1091000c00040d00707806c0c65441e840741c11541d641c991420182d2075409545c1c8425030003a2003000b0440c0401c000702034074091881c581c4041c840c44400c000c050b58414203140fa11b08042c00d0840001e8294500b0080e905c000c1507050066620002d88200040154482c0e443c2e00c40b49030b034001050003a24246448020018880100603010903040c0c0c0e0b4440309400d4040250081d080010542c0c00040d2100b48200303640010384124051a09a41d04110b50000f0342c1140d200344007130204024a51a400c16104458270160b00c0382c00761 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 125779424 1250 125778174 125778187
    0x601060f05091f08191e0504020d1712090613120507060612050c150d09061b0c0c05010203040609090507200c09070c03080f0c1905040e0c0906 63
    0x4039050b0300100441d50303000090070001e0f10140400368552440c103445580e02802d518001d94184202240d0400c00b140390340ca404007496405a01041b491009154114041a00e8a59000041d0441401c55000e040064404032940c100c4442c0402450b03800045a03a0340c0c159900d0518040c1c4440040750070388141c24003c00c1d04400106407003102130103140d003810310a051240039203034003049170541d030072080111a08076608020f1003c2003011008040342268a810030050b50404801c583c081c4c0980030012075110b107203081c10803403680c200c10f428540003407000d001450700341001003000b1b0680c102580ca0b130b000e240011559501c00b204440c150790054640c0a1000e00d003081c0340004020041c448000c1150724405160100003c01503010a8044800180035104510f4200602458041c040c00244001644030600094002e4800e40e401480c122040380c142d940c00c0030b0548184140c000440d0144104002c0281141d00030b40a0401c0e51049840640d06c0ea4031707064104040e2103a280c50310350090f0140002e = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 125780674 1250 125779424 125779427
    0x604030e310f020c030c0709050112031110050a0506040b01030e0a02011103040b04060f030b09060d0b040c03050f1e0309011709011e0c030525110c0306090a140601060f 74
    0x7524600728900e0400a03025048840e194101d0300449404210781d040001c00020f080c1301009048003070000c0000812540d454840140c0900942480050900c600300510a00c590000c1c419003150480d0301d442070181d841c2140015000740400c494181c8a00d03d0182044001c1d440303849030300c0002440d80e008198002e07164006440c0c940042c541500d0501c070030003011604280f200013038401851181c9410b0842450714401600380c450350340e4041d00824803a0200401070703403024105910f080d0441324100450310744e414400d0728400d0070303000035209104510703080102000000c1c0d0820a89000001c6441494601d0030498503031144510f064001401d000090f00c0c03c0c0c4c0700308100754000070b0100000608082c000c0345880404540b1050144003a5110002c0d032149030075019840d40004524126840342c01e1a800000780c41c68117000c81001c02018a909688141080004101010005046410b2458140c10303a903600d028588080314661095211780032055400505581a10003a44401c40082d4110300c0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 125781924 1250 125780674 125780749
    0x30106110601060e0111160311090703050c090f01020f06010e01050a0602060c09010e190308030a0b010203031b0306010318060203010302040b120d030c0507020d050d020c010203250f05030c0604030e 87
    0x200c03010303000d200b030304d00c2003041c102451500940c40341c90007050108203036040146644005002f64245030030007041003040c0d00e004040341d24a01c01240d075800f1403000040105e10b07216405101d10014840c003400030650f5148a0150307812a40102d90242215031503a0040b42c881c401a0b800040107803051042401d95801402018581c410142c50030f1310b15400400c3c072415024a41e40260b030754240000600c0745000a601403825850790a0004502d541040308050101e0b041c0b409501307038140c1002c070120b019a07200750400900028604c200301c2e483c0c0303c5801d142000b94800c0c4001c0f0b108514001d6100e80c0c0b0b00707106107081c407003880e0840682000e0040d580164050504005841c00304002000780da001646d800485004041c010380041c4000031140001038030780b1300c0000806041d5802407280c039080000c02c1400743c05040700c00341e61604581070b514010b40e1074032090400800c0340c000896804400030000804c0361185000c0c0d0342d070034501e0766000140004000ca01a003c80341040c91114610900c0740480c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 125783174 1250 125781924 125781947
    0x2d05191104050406020f030a09030327030f020f100f200409020901030b0d050d0306050105040b07080f2a060604021c02071a0901140c0f0316030e03040b030106110601060e01 76
    0x100003506d4007110301801c0d0780a0b0300882d61f0700c01c0c056652441c00e05050303040c81181e08900c5d506010310006801c226109219109400d03000301000003d4843c071007424800d00c02009088091030448600c5c00304e206210300a060490b405818a51a02e110001d00c3c041041d1510031003400c6001544c034260505e820240650b202319802414035803603a024440c143c680701c0400c5da440b4051000742c4141518010003c0640f2a1740d840541005000d120a000704044001100c1185500c110a503a8035403103c03d1445860160000d170b224001040c40580820010b03088010021510701c5065403480c5e136500c0c2c10002203015803c20300c4036032000c90721280c0506180380c0c01805c0560065074650100d20000c40d408820420842c0d2200c101d0351101501c40c070010031584550781192140074007c2c1010210084100b15000081a0400d0310108070303d1001d44a000f50b100b00400c003040d0f81580da40d103450700c1d00c0343c130160310a100c5e02d80001d45400b034060030200041145810f8a802d030b80c6000203000d204004551001019 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 125784424 1250 125783174 125783183
    0x1a100c0303060317180d0312021605060702030301080f010606050409050a09060e010608190209060f010c050a030f0e01110a06020f04120b0106030522030c2d051911040504 75
    0x104030102c04507003005035900c42c40203520316107a175410300d50300c2d490782015444c14410700503114001800c001070b402c4403080d0b4041d2500100140c0311050b2038007040323a00d601c1000250a501a01e414007890a07804001141a01e003200d00302c60032000010b40c0399003283c1c2903125420004406100c203020203500345d0480f5401502c42d240c0032402c0e4419865020407207100b602e41e1034850f991104108034116051101c8082400f42d4600a0307554811b03078020503420500148440d100b40070750300b504641d86e8011b0400700030b016000021901e040e80310745005001d85d03282c006110049900f000715a500796200c1c1040c404c4ca485008054101c13040c481c1c0d42d901c069041344d807694100b010b09100c0410006030b1520542c0002d80540c0c134000711945032000190496101038058400c1142c5092214844005980750405196240c5480340340449035090070201d101e5581c0200c0e8072403085c00c6000700400f12081403170300300501803002e59400103403940c901020038250ac07138000d0480654030652400d510742035114a5115014 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 125785674 1250 125784424 125784431
    0x10513090c0903111503041214121005060c15250e04060b03091507120f0e0d050a120207020d020312070c050904020a15030b030105070c03031a100c0303 67
    0x1114110025941d54007158000140210820400c0c441e11101c01568910151403486880c00071800c654800d1100600103003000400510b4013070b403184a592101144200c4900007600c45105076280c500032641600d40d071000080d030b244003080d189404003c60700030407074031030050100d507520b04071441c2103444c000c003606030011002d070000d61080c0c1c1a03031034031344090010760703d560611116000b04011202039821840794008d0910810501e064002650011b0711907459059800303545405046541e0440c0c61240b1a11608001c00c0c0201d42c00b140e000144081d845105684c4410b503031181c21a1a400340c00511400140b00e40600c0c7c0c5540c2c9283d005241042c005820b80013201d031242c0200c0d1034802d8103244103c1c2c15100003031100c18085680300100c0a0b05048446841904103a00000c00340d0207980580042d2034000312011005038041d9200c00622240036000348954a000c0d98041c1401e000b080040e8042801d2102c11440120f8104040740442c100030900c0c0c41c1003651036011a18407407c000d0480078143d9 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 125786924 1250 125785674 125785679
    0xc090609040212071203090b0a050a27031a06100815030a020307060503060102061b07060b0d0204060b09120102070c1203020f060c030714070b07050d140f0a0c021b010513 75
    0x2031101101030b043c1e0303585c02948061a0300d402040e498095100311010340d000d10500e0314080d4400200d84444003a8a8082c4c0e507041c04110740c4010440d2340000c050790703005803200001044480220340940300c132044525507440d5101c00600c2845014004100009403040d00000c0483c000640d012141d90400f508580031020b550380420303e090307107036040700000c40c81c0803080188a43e410003c0d5503006010749251850f0003140d2042a10b64010740070000e10064845040006070340b6806107403088260000c00501031681c0e1001142010b50145482070300440c03048228184400e814000c60f14070b258414014850b09117440240c0b0720019240c0c00c1242140540c00c811654074104001090240941c00e410583d6801c1c00030000e00550300c60000e00111103000d001c01c1010614400300203901900d203080180d640c23030460b10100020485230b1101d104040e00c0c501840001000b028110f4071030242d5510400c87d07a054090241ea0320044c100d1b441c480d59550b020581c2403548108007621840002c3d015000b101c54 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 125788174 1250 125786924 125786959
    0x9070306090504050c120d02150703020f071110031e090503090306010f0e131509050705062101091e230106020a02040c0305060a0306020f07080703120c020c0906090402 74
    0x860583d801d407850f50055401144c0c9140c0b6642030224900d51790002c0040d00580400070313440d000740414441d8010062000145014026012036600c40020140b4503074481ca035107407070a0107041e12107000380602800100d140b1034900a20a42201862905025020014210303400c0040e1850f41d0040340c07103000038440c00a06440821080d8080c0c403040800110070390814900ca210400018062051030880390b0040021070f61a0300f5401c40304058a40c045841459400c00b00e14000c0180d2099030000c000003140b0304c80d01c844074100b1400401d0416030b0b200301c0e41c0c0c40800341c05491281900410304103120155030a0b41a0344e502044520189682d04075131540706404120542c0c01c00d80c0241e0140c1c00001d0301508500c0c140c42607100310300140c00c041050303092500100d14110400c1c00024000740d030018000070500c00f480c0950344600c0e40300e0b040e1559001245070007820001c480b1648d01c2c0041c00d090303060384518000302c0c10505030100500042031a0b5a513108106024802410582e0462500900c11902c0e0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 125789424 1250 125788174 125788181
    0xc070e040f0b060d0803040b07021509031b01090201021203070306090204062703050d11030408010c030c090806040503070803060f030109031806020105060603010b0715020a020a0309090c0e0907030609 88
    0x2240610610032180700142082c0c551400020403a920940c003c0f0814800100040c09507a00583c1100008070300c0d07600e2040a0b0310f001d08907121410903840781d00401a031142c0000003044002c07410280038503644900c0014a00b039a0487e00300074090303001543c1c50328018040d2006180e0210140c5000306a003562070810000b01d9010350442000103078441c400c041c00d07050a2400180ca07200151440d03074440c1c40c5456003074440e180c0345151810048940c0c0240d079200c0c01042900c0280c500c4000800161403c3c201c0a0014081d1014034130220f4006480082d0480c0045601e5201e01e400c20051440c02400e9547c0c030031103030b00041820f640300090101204190310244540c6500501c80c0c0c03555900038007421b1103061040480e0f400f0300116810882000801d0b110340703050342e044424420040791588a0b919041c1194804a1101c0c0c503110310110749000015400901a008103002c2d40b1003510407500c0c0c0303c0400c241c4603207003a103d022440d910305501c0e403414594855944045545000a00b01e5103d0640c032054 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 125790674 1250 125789424 125789431
    0x51303060c0e010c020f1c1a0402031603050d0c0218100302040608030a0c1202010902120303190b09160918020c010b03010204150e0a050a06031a04050c09060c070e 72
    0x85644441c84100c4540096401030265000d081c006414505a40010203201070040443d010712001d5400d5520866860700071b40d40d15622404041c07840c1881a62285110411a4140d00c86d1040d507540e41070054031401744c0c0d010350fa00000030301a003c410701e00a0b6120501c00c7c0c4102e0308141c001e07000c0c142035074400e20424090560680510141c5143d40100021341e280c9800a05085d08204200d106054011102e010131580c400300d43c10110402032401c2c2e00511001001035000056902c21040c80c180c00b100542c440d002c0000c0c3e4000302880303034140b4000c0303c10600c8810782100481c000304003506030290070500010705614001040b240c0b03468149840c04003d81c01c1c0141d5980201c0d00000301c100a020701ea0034848140c0085042920748402e15440500520b101010f212800d0b41d0001181c40305d80b0510003800e400380031171880035075034203005000f000f08155803040c020100e0040c01d00340c50a8015140126440d005d01410480c60008001c80303680450420764a91190980010b4040b0342c03954031a12 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 125791924 1250 125790674 125790683
    0x90206040302130f06060504150309060b030303040c031205030417030615040b1c09020102070b070c09021207031a0102060601031e0507090f120b0f060609150901030c02160605030601051303 83
    0x104c100c4046025802e8608980020302403160900043c059280103143d640b2500303c0e00d28000c204008642000c2004140e142041e03600740c00000308001c2406003000d01e400440380b280d0000d090200e00c81604440310300003901c004000c40c00038440a002c50b035402e8082c680000c5c00800080b5070000c00300c40185250712aa000402d60040440e4900b14030704141060040503c50a0060007901c0582d40000d442d02c2c15401180e0022101141e101c09001c441d01c0d0200181a612004546e030324044080d4292074841200c1d24400241080e049525441302d5102c42102c612040e0000c2410340c07110801500600150780700900007080b041c0441016035114040d1038041c6480d900c0710f40c0c5c9a07003882640d000150032900304174214110214501c0004003810240e90784480030078500440e03510364400141140c440c002943c1e51010454140002c114801d070010419201c0c2624100046039207440c0036a12032084c442c400007440e41c1407500b0401f1030301847c01558010300524145240500421203195801001c0d0001e0340c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 125793174 1250 125791924 125791931
    0x313030605061005030411060f040906060e130e0a02040b010513031407060f09060f03090b0414010606141602010908060405100c0e030c300a050601060507030503040609020604030213 80
    0x41a04207000b1115001d0f105144c614990314140e1120f0304440c5a40340690f000b081300141c6401d40f916681c040d100a8444203d00740481d07076031480000c014000340120680314421910341d100c54046188101c2545249a07070107004000810b03000c2000606d124400e2030706001c010845181d1550108120502544c1304003e002e140d218811000d51034401260460810b0011002642d2925500711180e54103c3d0818034015001407540e680031006001c100d90004c0400381b101c801d020400c0501c2203000030b0030800800030041c081c1e0340c100407540b140c80e0b1041c040200900f08402070484c207690b8091002c160042c100102010780c0c54100c541b60501c01c40c1d05980039005442114103c14150040103012401882d00702c442600c0c40740080c2c0c44040103907401d485000301c89408004820301001c0282c200070448400888140c3c040b4045882e901c8400e0200c51900544002180250041d4252619a509a99a281540d84583c3c8a0008110b11101079922140604c4008010382d15180d0f10309007440301c4080170 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 125794424 1250 125793174 125793181
    0x3060810090b06010305072003040f060c030e04110a0309022e0905010c120804140706020a0c120c03200301020f090315190c030609020c2107080315030313030605 71
    0x614460000f5086904140c184404d1114055000030502e640e48180301035425150070400c00701d4514415980309203101a440000003444580000c01c0c9400103000e40c540d0400d401c0400e0400080f5407442c88070201451003485031081d124800c1d030103115000d2000e0147d0035280d5512850200c03850382201d010028030700d1480d1082c0007030b9200c11a400145401c0c00c058030b003614181d41c0c80c02c10100c1c003110902041201400202804032031070000a40d0201c0c0d1054441994a6034402500c40404903401d4844003404940025607240381d0341c034034030040d41100c14010130f80e00b03660342d04000c89900b01010107660f04101d007200c034139038003807000b00404c0210703046490741d95072410185820031407400341c1070091003840c0c002c10006402c0f0032100c1c00b1108107040e0028076881e451400790300401b01500030740101440482c66070160080080c90040031502540038400c030044121310070b0164442c90400600d03010342407002c00c044203030b101182c58040c1c6000b41070b40e0404042c64498269140283e009907901500c81c402d0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 125795674 1250 125794424 125794433
    0x17040f02010908030a14030712060b030603010e0303150d031202030f041e030c030806010c08041805010b04061e05040306150e090c061812100c0905060405130c0306081009 75
    0x20b4009100d804041c1d420b14840c280d024143c0700f90b01000d03d4031040700000286546204107540d00718120151310400499458103c0c146480d04101c0d9443d000e90f280c001852542c11000007940d115448840c0040d0f03241011070240304080c509864101c1c1801141c40312402202c656002442c454001590079030240e2805040c0303107162010a10b6440544841c4c00c803100042a442610306001940500700005a03481703807801200d0900c0c060718040e19100c4d022802142803a09204181c0d001e901c110400c3c040c5903250701441322a80300d24824035000c03e03415003200c503450230b0f0f4111142c2d44802a04100303042c40e903203444101c04d8690b181083c0d402050094400d214424034042c02d1034000c11100300902c0e482c0c2018010610502c03680032054001c42003210720310701d107540c0d444003102040b003240b0030b461031079803607030300ac00094055140707003401044840e5004036803414030800b910102c5d08001c264404031800c44012030f0080007188016010103803228000300748648104001d1703443d107481d07620000d07200e03800e03041 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 125796924 1250 125795674 125795687
    0xc360c020c0105030108060604090222020d1401050d0611040e04080703020106060201060f031e0f0c06020c0f060f0c010603050708030d1107050303010302120c030a060b010f0c05061617040f0201 85
    0x20325061140031300051280da140080d52541c082815070700091851780c02e00008044c0700c0c9001d42c00200c0d100848e40c16801c5405a0050440d0107201030081c044040388160041652100b402080d8205d40b84132200000f052860708001100902400050310f49502d4800301e084003d0212010b0b600442c0001740d05040640c24880c65004158030300c02080502d061100c1012203c8480c0320150038a584020050890440d010b510340c0502da010f003c891b0450010700c1c015021124610801c40980a420350603042c900341034803802c29500e0f00600d864941400007210301c00c40c2d004042200031ba596900030110006038100318480140440c80300a640300c246801c4075006652006000d040c42040612030740e40003400010a0f41e06407a030489109401100e0841001c0c81c0241d14600e141e458030840c2c1e080018081c1d43c1c0d2000c070100c03000780d03074030345010078a08401d49000d914814010035035400000007811801c4484200040c1607090b02d000710055084540919443c0310a0310191400c400b020f1140c41103603007001 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 125798174 1250 125796924 125796943
    0x100c150b060301151202070c030209070503061309030e090108010510090e0a030503070c0c0909030801060305040210030e120c0d0315030c06050313050105070e03060c070c360c02 78
    0x9200348500000c05001c100c450206103e149280405041a12402401580e2070a450a001d40e000c544030b446d207091112800d4010702c4280e0041d641c0300c0108686070302c980304403881118060120300c5030707101c0c07041c449000300401c11040c2c00b04004043d4014450b40c42c00b07511070090400c10700100e03d83c00c106040c0007a0740000e43c40211290f140c10708041d0034005c0481c20090a51b0036050030f076181c0d44d81c400c09a41d07400190300001c0003c7c1e8824030228043c09a544500c4074a03000c1d41d111001c580c1c80b40c1c401c0d4104c8800f070b40c000c0d41c040302d00c514003425284243c100c55402d60ba0742c1d0580c1da0032030001e60510700c140c200d032908050305d40007456210600f41e810b108100001c04401042e240e020b00d103403203034044d14007603005080403c000000060200301e01c3c0c98529001c41e60160003000545465400100a2600121102d101303001e844045550f0101c0e420aa4803007681250003031303a400d4604101d2000140d01c0f1b1703c00048802013840c20f40d01d070807c11185001102c440b040017041580f01c440000b400c00c240340 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 125799424 1250 125798174 125798213
    0x6050f0112020306061e0306010305010e01050105060a0c0f0809040c020c03011a060418020f04080a1209080c1e0301060e15030312190b03032106090402010f0c11100c 73
    0x15814a005a50300044c0c20f40c100c501616101c0c0ca050518865011824030041d0054041c841c100000040083c15030064110402c8071008020a90302e40c0d00b08035591240c800307000c000540b00d01624000c41e190380199840903210700e6030300e031800050758041400d07100f002d0114409038001482149082c00d0a00840301c000e101100d0301c94042c20804000ba4060080380203001c030489290030031602c050b81c1765040718a9118284101034a50b6505c42031955103108070786003110000c04d070080006d4100d0050a0ba68169007014020380b160000380c0045c06a4003514000c45c446020411519107583d8400b03100701c1c0c0180403030400007440c1e86443d5a00100c61000d4400650183e0f004000308035030050b40b00129a04400342c861500784000c510345d5544040c0c000c000c0225454040040c2c0410b000140d095615880203410010300322030f03650b000c200003582100303e07000f80c0403502c030009280c0c0c070350b20545220f0246403103031001420740803446000c26100c80d00d00c1400e41c04503c604144e00c1c180400b055076051881c041 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 125800674 1250 125799424 125799449
    0x2390111041d0406060f0306020735070201020c091e07051303020418140f190503040e0c0c070602011d010509120306030304030813090b0105130b03040c1206050f01 72
    0xb001001400408003401030b418040403000800d040100d40d80205000b8000c103441d99904903120700b0320200950000700201c80101406071000000c0400c04480340d8408c00c1900401c00f0689030810007040c035840110101d0450040401100d425600c42c5042030141d44804c140b403c680f00d104d109600f0450016004000748041480f61130120148402c09509895044c1c50215824880326407500d4410081e043c001c2103000d80a5503d0b400382c1700040c00c28690205081240d400000d11078210ba008400302274090f2141d0400c20051040301000740d0940d1f000030303140340c103985001c030100c400500307040075500a1030040c1d4551040440c40000c0300c8c074a003d04c00141c4001c00840c2800701115070781324680314106081c0400400018526541802070360020354100c1c4000d41e0f10b40d10304000c086814454040e8002d00e9180101007126075100c1c0017901e01010314503105c408543d080c0a00000c4940008004540900b1980d5001c50029098907076078a03828810f850104907130400c1c900340844242c0c140c110010302c516 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 125801924 1250 125800674 125800679
    0x21e01020703091d130320010504020306061c1713060e0103060e010e0703050c250b130305120604060f06050702121b040b031516140306090a0239011104 67
    0x3618100e054111714500a0503102503458a0143c58203480082c00e0044080d0310031600151000c1034008078801c0d03101302c003038907003680c5d0f1603040040c07076003580581c42c901d641028888400143c0300003518104503070402d0312605014203102000d80111082c0c1121000507641d440d54209940c16001e01c001800015428880c998140420034019080081c99581056241d101003480c807940c07401240d960b1542d4541d462032a0b611103400704a072840040c82281c9801c034203400103c820300044004d00b5404d0b41b541c3c9003481e190384034084400e024809000d0590042c0c0e5410005910720b45501940010074503600c0d0303036480d207141d401001010b158129161125804c021140d0b6074001541510000c0e88004560002e10b0203842c07004240b0305000d00e196200c105030f0b1403003445803104060303401d104074200b59070f230700740201c045000004803500003039421540280401e0041a500f000603009000307140140c82045c90210407401800d0400410601da007500c05030f82c203886641c208000c0c047c1c1640100b80102c001e14092 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 125803174 1250 125801924 125801969
    0xf02030f160306063c0b030901060501020615010903020121061502100608030405060a090806070c12020102040e010501120e0105160905120d0c050f0106030809010908060402011e021e0102070309 85
    0x5000a881556a900c045080480d01012604c014003402011a01b15100d29140b0551402410396000d4280035202e0074001403c0b0780b01c09201e50910450607075528120901d1035005541c070035035502170081000921082401c8001d602d01c02c1d01d0003010000030f007a0201c1f103140d01c06801d02e0080044038102d0f500b00324051065007000400c80e0111403054491503070b50b040c4550121030060b40d80c0c00c0749900d4001e02041c00142c07075000e80c901a03404c3c003500c0c201088180100c4140d02700d204911405c03900c0d4106c00d004004541c090702071941c60100080300810b045e0840646103084034030890703007454842041a68002c4450f44203451002504042e0744020f29524581c5800d40e940303072040030000c20015003a4a4908101060142c00c0301c00c50302600034000705480e450001c040d40c0140440d28005203c030400000d10060008000303015507010303111f8031244090006002c61701040c089542c400c0d813054060500581120300211011625240b00040e00d41046180007000c44c00143d22512404403584403030034140 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 125804424 1250 125803174 125803229
    0x314030a0207030b1b0c03040509010f0e0708040305070615030c09020a0207050402071407140108160e04050406060f0f090c02070b0307031e0f020c0c120a0f02030f16030606 76
    0xd0740c2082c401e140c4e0760b41d10306141508407950300000109840105504080500c00406001542c0040311501516a210300102c550300e10140300d08084008440d0215400d14050150a6001070080c600b4a00c0d100490700c036801510090350392105c0401d4206000c10522410b0310440003e003003007030300640c6496000c0d007000350340304401d0003600e00c6a50300041e000200201400094003c5e0341d9541075402d0680d4404d0a4148038130303416540c0f4003042d842b000041d090301000d01046140302c000d4a60319040101c04090000a080040c01250202d686042c08140c06e801c4601c420010303c911510f98038481e04216080702034070a0314460000350342c0008400c0c02040400e03025240c0c4190a0f02d00043d42e204886500c0380701150011049000910b050201c081c6054a40c000344000c0741500110f519500d031302420302000f045421286045504049800300004065503d88039030980014100c580106c04c0d0183c0c40e052244010403280c503052100c908004209240c0100c20060003100055085100016000c4501 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 125805674 1250 125804424 125804429
    0x30b0604060e0a0503060c0a08061008041e0b0901200301080601030807060f02030c0d1401051e030102070c08012c0705010f031b0f0e031b0f01050d150314030a0207 72
    0x5011090300226003c0d240c18802e42c00502004044405509040d81c1d5584140c0c482220b03240050201400900c690800b47c107407103501a40303565000350a070b40d0780c2c0700c07082910107200a10000301040342050012401800380d2078003408509000190000e109141c0d5000c11a2014000001d80c0080c0010441003a002c54003c2c1144c0c0c00403a80b540d0340074240740c81401001d40c3d2400c04c24091010040c0101c10350303200040c00c20200918405c0040307203511010000002000d00c2041c0d40944644004400c0c006818000c0005250140016007001010f03619081c0a10258000c903105079034442486003c0c08a407203851501c1e9989640007003407003160403030b081d48446140c0070700d5043c4400790703c60411191095201203034044407030b0303003402807440e9042e401010b140c8a0100007002402c0601c0c0c10303c407854007003110660345010403501414660054184000c0000d000c0ba0641401002e000b841040041406001c40e44459005440c82040c11450010781d20913a4020805682d4010f0160340b0181d40c0000d07402c000e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 125806924 1250 125805674 125805677
    0xd030612060209030f01020301030b160c0b0117070801050903120c030709060e0117090c032505040906021c0905010f0b010206191104030b01030b060d050a0609110603041101090501030b060406 84
    0x2070303d9450a010078500340d41c000380e80c1810b41c4004000030900400e221614000c00e0995080790a501d4a104100d807c000036081c090303c2507007500010008507070b001e010041850b0b100401c0d60040b5545440e800c0c02c40f03008540e80e0600c4c0c4c2002800a000d040d14803081640308400080b00f9055080140c4000d02024441c012035003404200180c2c08500e80c041d20105140d0391100d541919140783c0844940e455401c11520b81d40207100b4a40713140ea010741c02050300710f44001d5040304207108514200c00c00c0080c2805207000e540c819420002e80510408001c401441051808404141d1000303500e40b260844002421656401e40ba15180189036a4003045c4039400c4440f8100f0b0858081d1a01ca4400041608900008280303400007000001c101408560504884c0201d451406595421040c031080412060000b4026001707248441c002031020713884216098001ca160346460005100813414a40c4180c90964509a00030784594180d80e12010b018050300c0d0a280501801100d034022400901440c0194170 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 125808174 1250 125806924 125806927
    0x1180303050d0216080702030f0d0e0904022e020c0306040c030b0a060b04060c051006030506040321050403031a0307050105090f030111030a0209091302090103080a031e0e0d0306120602 81
    0x340902e8036501900c0e154a41c5a100d24500b01481c582511039030720642d0300301e000c0e02030181d08032202c2c0300100301621620240d4880701603002501003003164406004000726448285045185d220410007401038400700781c080c0d0b1412188a503424064a00070302840244c0c80396200b0001c000001e1440360044007143d62000341901c02d5100c0804800240400ea00403d0b004440420300158151b881058102c4850051040e07610403201d144074002075800c2070001074034a0740700c0804200020310034402d441b0040ca200780d40801c1e18100501c610161001076a00740c000940b41d05039012002094449410450400c034010b0541d1031400002a0560184880e0b40d03104039200c0c00c003110035031002e42000c81141400c1164550302d10713200d100300000307401215a00d8000c1014200243d0103089800c0da06000940091560302968607541e00c121099014a66a0081585983c0308100907030615450743c1951480c480041000c207261440701d4600341c80845000c041500b003003010002c1581621010b00610742140015 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 125809424 1250 125808174 125808187
    0x606011e050a0c030c0204051014031501050d08041a1b0303061f0c0203011d01270206090d0b040507080c0109051309030302160b0a1d0303070c051c050310050118030305 74
    0x5d591030800305401940140c00c02e02002000704c4001c031803c080e99800c00102c1c4201d00507005040e590014207010f86003525408005100c1860030514000c6500c1c801e416982c0740c151a2420089803001000b01043e47c440042444c07041155002000c2c891002a070f8021030079454078200042c00d801100030f44050360380501c401440e441d0b01c25030b1a403660070307000342c020303c404581e04007614106441445001110751030541c0d01d1030440c0509006240d0034540c5640d050002d98141c0802c8101c0d4001d4400c103a0000070150440b0008102d000f065100301e02400241801a02d011180c0d41425441000c90781000444c00041c002075680c030100e441c02081000d8002403400c406d00c0c00740c0c0280310b6000c2608541e0b044c04d0000781002442190720b8424100c0c107809000d4a5040c0d0725030340c20740021500881041d041800000d8002e4410303003c9026150080c800c0780c00102d02d66050008034103d103a1610002040002001406040c032401200240400c1c680203000c071034145418a24119035010040030004005402c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 125810674 1250 125809424 125809427
    0x1030b0103092a15020c030c0306041203150312020102030f070305010609091109030105010305070f0f1212120e0a031808060c18060d0b0415050306070c14030c0606011e050a0c03 78
    0x90f41c003500480440c14130400104002a56464050705064440c0c0b203a807100c504507040c040f80c2140200e0717108551045040368030005401506007149102d414a15004000011034403189608035120059000181d5a051404a11040c18030080c411000d150800004100c0303940c0c0482c170b210840780101c000040d08004100102c00318032502174070550540c28400084280540850f03854200e0785001000d81c181c1c0d0344c2d2021181074036507038030414020580c032203a110081401001022580100351400840c030f01c41c07484101040754101400090640d11a00d1920201030700001c07405008000240d003030654610f043d80c4241d5800e0024041d0000c3d13000491813a6440c0044035038440718107401003029442d4420b01c500f41c402000b400000d40c3c03081d03051a00c2900d516100001600c103860001c1c0207032406668010050b18104030a140496421607009405032682000740040c1506101000c060801030138901d000415550740020f000f150680c41840354401e81c0e4112342200c40d40640c40c2400260022103090 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 125811924 1250 125810674 125810753
    0x2e150b07020423060a0e070e0105070809040606200c091317030708070306050405070c080903100e07051f050702091512010f0c020d05030402240d02030601030b010309 73
    0x14180030000d6100111030f00c01c5064000d41c403504003601c5410001d980c4a201521411042d19150040703111441c0c520101d51140000702100c600585006103003181c0704000c6011980960b1080e0300055038010300041084200b071040b401c0940920040221040b40000507101510103041400c400141000f83d2041101c80a0840300280340340c100961a89003c20020340301d84811102540001d1a0940104980c6411300c69140100d0442e0303580c0f94001c0d2141d4950b041c903441850003980c0b5101d80304040316210300c035004440e2010080c001401100d03240c03c0c02c0c465404c4441401c800540702443c4220322044c0e11009070360a04c2e404030f60441c0c150f00d42419007070100300c001e03499a4101484c0f5000b54513948054000700c40e0100750541c01c0004080c0301c002283c03034590744401c2c0d0f0006401000403074058076001d490040480c0d012003039244960050f5200f941190720502481d05a140c020003000010f6801d4443c88012410a080c14003105405503038100e00c4201c072102c00d40c000700858a4841031001240da = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 125813174 1250 125811924 125811941
    0x609160e01181b080910050415050907080106180b010302030c0f091305070f0801050603070c1106090d0b0411040510060305130501020a0216090c050a0807020109052e150b070204 78
    0x3a0f442d811048a2800140082c5044504510610031300d801104038180c584150352085400201002d1120842c0318010040c1c5000b405240d214814030001103800c9400b8030134400104020f00c884604000e040302e843c007c0d92403047c202818144144204460b8240c40c0044400f12140007001c65a60052000041e40d0704c540940807044e0f0510f45010008555004900300d85c51107441d854800c00b580e42d40040101e01e01c4210b0342840040d07501c00c43d0000040300e410b0b82ca9103416004103560304092a00b400b261250355006401c1c0d4030a100c09040c80107004c2c1603590b6848413001071b1403c2c41039107020b01c0300300c2d02c0c80304500c0345170f0030165220006a641003a805101c0d004690000081d5178408900100a603a0049400000f02d00b484541e000900c081c3c082c03283d600c944005450310303401e2000843c801d490415004090405654803414100001003052051718201c3c03521101c03005076440c412844509003444028881c12142c82d00511801c044001d42c08202151981c031022035460401d403012401801500 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 125814424 1250 125813174 125813201
    0x100e150106050c03070f0606050f0a0303050901180305060c0a090807120b0a0216061506030510050108040812070203030106090801141906090e010e0606101407030c140609160e0118 79
    0x840d1b442c003003014a410060855504540700414800c4503410049a10564400240840c40400000102c1d5002d03205030090322001c00f03a0f11541581c5c03070301c4032814942e00301ea41c14010342c000140c449540350003004801c040d0140070001c02c5c58500380145241d9203800d001d000352400a07401c0003c2d0211191b601101e491044e10380350500c81c01c0c0d0500d80400901a14060301710f0304001d0180c0030403083d20a01c00c0520694508100e540d01c5868100107451164003d0f00940309120304128010002c144c1840083c001c4e40d0382d1780110380e00d42c50444010a60300c10b54000c0c10b11039041c812681000d14802010907004890581c604034003001312140200103240f254072210031203007403005101000c1419407000300031b00045004c1d119166600302c01c1000d0300c02040810700100760041700d0500c013460042c001e0704125100e41000d555072903907030726030000401d162822000140e001d01e00300011444144810341541d1090301020403007a044c55500c52241105019484c5100300c00c1120a03101000d80d0051950782180 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 125815674 1250 125814424 125814443
    0xc170a02130b07030903060605061c020304020321030a050c040305030711030705130501050f010503060a061d0901030f02011413050603040f021225030b0106030902120f100e150106050c0307 83
    0x3e860054600c56081c40152291444c141c40011141800003c0361074100790085c69015880c24035151600942001d44141d030144940500020b14200b402c0b40500d02d82c1780104226103d02d400b036103460541707100905540010724284420800914000141c1d10159030010380411281160342c0480c0c40c1541550200e07506c403d02081c1d00302451050350096041c2d41d000e0b0b804008802c07181005681910059800580050f01401c0800c4160710510304c208007107898034081011041c20000103411107000f070700240c4907004000c4541c411980c00801c413080c80100400080e04080c54694080701d504000d10400e8050080000081c080106000b6110f070b080d50300030700c8410003000d407040c01c03651104c00a450300c0302001c04400040b860304030b01004204495000c60305481d503a080071070480283c03e003010200e1b0012600f50148854080a10903805003202003001071581c080045201c1007070350804400c490f1580c004202c490450303402e60101c40e05544190900a50701c040303d0150520b50310541300083c160201 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 125816924 1250 125815674 125815687
    0x2060a200106150507030504050603010b0c0105070809030a0f09030503030115090801060e01030201030f090b090f100b03060f0c041a3004020f0303040308040b0901030c170a02130b 79
    0x400c00c0c4416081195048411604500032021500702c1d0500d004407008100210302e020790039885640103118040c03203803814600302a60f50000c500d5a81080c0c00541c101d190100358801a84e009200d41984200341d440e044045040000f2400e4491041c5407040003000f10401000043c5400380e22900000d42d40801142d65035030b0f4440c41c2c0b508000340640c0110001741890307000180d0480500413941901d44400c200b902c1d40c0d05c0c503401503001b40952000740300e0127520342070a00d0102e00301e803640d144556640320103060310500d00407030710b414000424241d500207403030503d20b2800c81d00c000800d903901c100580310845a944070905c80e80400d000b164080301864a03410a10301c0060032110103808000640c110640d07010b02040713594600180549015520240402e0004015282071030344154281c00150131f803403609031030303880390304441d03020703421602610320005028085035a0505c102d40503e80585803820f50107800d0414810001405001c184803a42c01081c20f60070303403007142d8005e0021700b070b9480103554035003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 125818174 1250 125816924 125816927
    0xb0d021c03030c08041203200a020d03051b0904050c070c090c08061f120204050604080c09180a0b04150e0607080708150d0f020d031d062b0902060a 65
    0xd81003001200040e0516500c090054090920356014642c402024210341c800d4450071402001702d69007a0400780c0e9000c445071007030300071340c0000c140c02c40580c0d024065178001544061b0031307100060050b6441101800002c0c1e0005c000c14280da02660b012180403905071070300c00b140104c90082c0403005d040d03141503e01c00590041d641e4010b4400010340d0301c5034902603503600701704000c888116041006a010449010191300e1080e41e00c2c9141c1101d5000050411391668007140054001c0d4000c100036500c07104440f00b10b0f1810a0120340d00a16200502c07601803810b44500d1303155216000d0040640001d64041030420041070709802c042c003102c2c5010022420146841941d41030144c410b0808115020049480f2a00c40c4a40034425040d1850704174103010360805000b01c41d10f614006030780f0350640d40c40b12401030340c0c0e980c000c00041e80642e03a5030103800d002010351040301904500c01846a0020048042c00461084041c04182e2110a00c43c066100c03900c003800140c13034090b000942c0950001669003095 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 125819424 1250 125818174 125818219
    0x9040518010e01152c0106090609051c080a09091503021008010302030705060d020c01020d06030210210b0607060609020c0f060408091002030d09050715020a030c02040b0d02 76
    0x661600030300603042d02a81039402c0302d120540d0400c407140d0030308003402040f61a503e00151400c400840243c01c1d01000c1150381d0100e800e800c0500000d201400410065a102c040c20000e0442124441c071002c2c4e0080501c1040352072028000c00554000c611622100c1c01b50f40003070028481c40c1001c2c0241915050180c90440143c04201d110701c50550741c023201d652082142605903075000e80103100450800c0200030302604003d0152100580811024040520a0000c0c0c000b1005908011416904520400c00e0301c87c4841065020440302c100d403101c513004200c600381c3c0c0c0800e070780c240014802640b0740071908a1040c8000906214140203000406e0041a4014510f16500c10141c1d1410913080c9210341e2600402d45000d0404a010702c1740700400e04d002c40b801c16498101c0c0c01100d1500407100e40c03110644101d28801d88194000e00c03000c11850b0b0030807400c1c200c2c541c0c040c8064001310352150340c041c1402252640103806542c2c1c500e900c84140d22032541c400300c0703c1c1d0028040051000746c7c50710000035 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 125820674 1250 125819424 125819461
    0x308040803031b0306090a110702030a050d2309090a1404111504030206030a0c020106031415010b0c1c120204090e0c0906091311090403030c03140903040b03040503090405 75
    0x640d0f40c1010740c16003840e6108141d078000c40004020400f142c070b4100300c2c90b020301495500e504e8102c504100681c01660300b00907021803a07104001800414140c07100280c00c03059501d0314858600054540c10541070103403000c9075881d036002c0f2492003641d100c04182e0b8000303001500c1d0b4601d00c0340001003884203008282400c101e1520080303804000104a8640380d107054011484000c2d0060341c1400450769642c1c0540206003403550904c00003810356907a45840058000540003089a0381004240c00c0640140604150160044200d0a031601c8210441941c0d61030080d400030903104944015014a14428642038211008040c0c05540300da4840302c10308018a884180c0070441c0c0b00750007032510030b42814058288103080003042e29203a651481944100003164400840b040c540310f40d502201a130351888680d001e00d000c0da900046900600b40f01908a4403d84000000b0000030820070148480000c2100d094171144a03030982c680d20b4619140b46103000340c02e01036038824240000c0222052042c64003689 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 125821924 1250 125820674 125820691
    0x9030e0906030706090608180a0c090e0309090c07050a0b0a0b0a05151b01020706020d0518070e0117010f020309031903060b070618140c190806010618030804080303 72
    0x9a90700c4440070550f80d0080c6101e900003082c0d841070100030080c0116440c50b40b207064107010740d0b400d4900c174030303141d040c903800c28000c444900e000c0070240000d075031f144106405840524021450003144c440011800c140040c0811070b803100014481040003c01d001000c9130a50040c0704104509003444600040c100080c4001c0c09004040710003e094985034095984c1c40c54503003e480d10348000b0400d500d01d280d8411507451803640d000c00003517002523020703c014422502c0749200050241000b150b460120505105004d64580c0410414013180c01404003503030441c0e190b031000085518110342d805014010030746c11407010034404800c114035180048000d0078902d1b11490300340683d11a0160680495a02d8043c0302c490502c2405040c0028051354800c400c803031152408004065260360b60f11341e1101403020003003072640054000c1c0005090080c03030705400300428135040e44001c6c1410b40107903a0b00414400d1208010900d011035401500e1303200d01401640d00102a1513445403501045507803684251941c1c0c9 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 125823174 1250 125821924 125821939
    0x807020f011a1009080a05070314030309061f0f030506013f020a080d030902090105010c020f0d11030a08070308011211090603100207150605091006080702030d09030e 73
    0x1840366106206401c0506094036a003040c1075000c1c1c0c24000c2c4414034a0a110030300040c00804110b007681048481e404e640f01d08020721016003145045205500c846c408030741c180d8414814403804e40300201d9116880a011502412142000c0310440d54400460f44201c45000940070048184000803d1a40c1a101d1041c848a0954110305806a02c43c40750101d90191181094640a4038100c10034120305160008140b8903c003521405054145400302da151000b082c1c0c0c1c0c41240c0211708008030124010202420200303500000ca402040c00902c200d25692311a80186130190104021009000202d41000d0211a02c1e102145400000e0390f00100054012904003000090200c2c1032560105410754002c18a0750040122002d1154008000d486181d01d07000d0f000d0310350750320317a05031001e0b00d09680600d81901c03070408010410005c480094100a0182e01074408100b061010b03072992404940b43d510b020001d41d03072125400c80c1580586403244030103504000022041c0b6900c1046d501a000c0200c1c0c1c0c86 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 125824424 1250 125823174 125823193
    0x1d0108011401050102190620030402010e090c0717040e040f050708010911060c01060b190e0f09060d0804031a04030e010c050d050f04051203070b100b040510031b080702 74
    0x10705444030912a4500583c0031503074180c00d21007840c0801d5482c502c5a6404109040411880b09800c541b21680e14610722005c02000150360340300d03607990411541a0780250080c1000350840265118404024004846450406031150f0041e011240242207030000c1d002e0b141000c0ca80a90b00c28075000d0140d03901d114101000c01c00c010107206a0201640c00070f1000300b20310039482806840d03000024101c0c40c55596071000690b503030610f030003090060303c203000b41d004881c030f030300c0c0701801071940c18100f24040c16055541e4941d0381c4481c202103030002401c4501005c1c44515141031003c03442950002802c1d40c0300c0d207401001d114220b07203116001d40e1180d203503a1030640c1c01d00300450701d034804050054841e61091080b40f4200340104024040e6041c0d10810f1881c182d16440030074991a0b03605c400c003c280d400025800c00784105222400c0d00841c0e41428410401c1c80d101c020003907805180035180c031854801c9030700e624543c0654042e00c400d0f001410100406991818040d08254040351014007500500c0e007203 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 125825674 1250 125824424 125824451
    0x5181009061403060f0d020d05070b0a090603061206020c1908071707030804030806030703290105030a240204030615080f010c05042903090f0d0509031903091d010801 73
    0x3d5030b124000c007600d058040301d6080304020a84041000a9810026560b041c5003c1001802001c025003010030441d80d0300c1c40e000b240180b01c01742a40c481e0b4109450f014040c445004042f800354042e940101001d61200303601c0d07041c9410400c5802480214a0345501840100a2058007425480d40250000500c210100c0c110740e100f4424214001c0c0081c40c0d0f0320000b00040e005070341e2030390094806800c0381c0da0380e82c0760b9680011400e8030140303c0303c01035089107070703a0701c54030031007035041d02410094001d03140d00d0071250f64065900700f5004d803218005c02c605010a0400526605031001950820814019600303102044040c6070381e5401404003600070302824a0b80b0400501403800305060596070a40307450b10300111401f4150380072900703030280d01007074842461500d0000c1c082d50145c02551b014116945100204500c1c0c9951992200c0901c1400d008000c001d580104080c0b046209150303402185041619003115400d80582250703c1020346801c481c803038516020161410f88080000070131421040228 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 125826924 1250 125825674 125825677
    0x81606140a020307021e04020d0906060f08070b0f12040305122d0405011103090601140f060d1505031006060e0d02030703140c090103030f08100e0106051810090614 72
    0x1c244016910800a11005050002c101900b90710300c10014150090b0724400641030b40c1c0140310320442c90361a4250a003c0c80742c03522841e00113203450100b1901c101e10b00428143c84404900c284581840d002c24100c61100f07480f001c6544290b90020124082c0c9481e14015185400c80f0001041c9190684000358040c0301c3c109020501002c2c40000c03004040304401c01913103c076002042140d0039525084484808000d80020718026030610010341076541c104403504000403640c1070f550340f0540c085000301409480303004c105c440340120b1000115190150345100005a426035103e160144038181c0001d40d800110341c02081902e04554801440000754420450104a40300d0041c0d810307001654204002418a07900c80b400404040c140c4035800d00500c00554020700076481907022400c40c0800024081d480441554001020360080404504000703240054410501038601800000a4400400d078020507400e600000000c215480001659100030f00f03008042c45140b0100c1c07070b00c00c403c03102c4624140 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 125828174 1250 125826924 125826937
    0x11010c050723060109020c160311100305010b091002011d010c02070e0402031203060d060204090204170607080a11040905010815060a0e0601030b0103021b011d0a0209061908160614 79
    0x400030702041e405c2070b0340040251300100246056100d1000900e0800c50407600580045002c6d02140702c0945000c0103000e0107e8100c1c980d070040515000c018000c4108181c281c5612060036101d2008038091010182e00610189060200d0925040c884440884054000410b040d0180d800d40d05220380e125903500e81110280c0d00258540c0060040740c91140741c1001441d40804018031040302c81c4525103560040780e005400820f2060f400003001e01c20030741c004402904035004900209114600454000d00d016409003080c40110b0700c5900320b103040d0300054181c038040c0c51407040402407965a0824590380340c40b000214400104001b0001c1d04600d094900e4030202d80440680005542c2c61000443c01418120303100c43c1411350034000303030104140c00308120b0112107141c0000168456007840711031080c000910300c1107642d8404103101c1e0040e00c40a20440d00120706652045000361120014401c007285c98000a41074466480010781810010000740d08803590b949852520150030359464000d0710900 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 125829424 1250 125828174 125828243
    0xb10051c0c050a0e0a050a0b090c1e040e04150b12070801061a0a030c021009050d080a05010b0409050901140403090e0c180f191e0f05010801050d0311010c0507 70
    0x1130001942c150b501781c2106038812011040050030210400000d50100c00959000e02103020100390402481203958041a500f6408060b59080c07915103082e40301c59240051004040b85000c054036503901c140f45d0841002082e009141c01901c88441d0b05843c0e4a020510548007a5800e1620005010221002e00c403c5904008550313480c0c418140780036409004541c030100300314459030b0291044019a0701c030340c030b944a20407270240881e401d516400402da82c101800c040001da10701001005964080c00407902101d03406140860203583e07400d00f00c2c0c0108080e00000d06d00c0101401004101540100718809580b03400e400384400340c0f21401a51054081e940030b000304084407142401d040c1c0340a880d40040c2000050400c1144880f2304010a20406180d202c04102ca90241901160784040d1460368050080c1000c40b807455442e05000819012042c8200f90291500caa1800241440341e000500360000e41002070101c0c1a1030000282203501c4103a00340d40000c1015000d0207000e22107021900e50030001c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 125830674 1250 125829424 125829449
    0x40803091009030b0a05091c0905270a0c0f08060303030f09030712030e0c030f060735010509090307050601060f0203120a020c0d18030b10051c0c050a 66
    0x204240a09021030501c41010301205102c0000002c2c0ea0141c464401d846094012882c0d04000241030701c2c0501015050b00305035285080d107454540d2003003d0f0781c00c88100b00d407800300f0358003401c1445011050080304210190f0145d800c12100381c04a40108194550f40e694a4455034840c81040307450140035a012030b49034004101045000005d0141d10b40c105000c0d1064904c2e003c03995403049059403581d141c0c100400d4460b00e82d003980700800e100c2000105010b034043c1041044001c07181c0d869600003000941400302c050a9000407001041d0800a1407920200d80582144200c00d000f4145109104252040c2e51100014401c2c003408000e079800554800020b03c016401c00105403030012052040500b1880f00b071114060707142141c41f246004041103000103030fa80c042d4541c0b0a00f8400d45900f08018000c1e0f000345183e0214243c9444400c40c0d070840228074403502c03100340c0c1d4240d43c080360b40800da02000103808249084070386070101100034843c100c06201c60390ba0b082441480758543c803844045941 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 125831924 1250 125830674 125830687
    0x816090207060b040905160b13090c02010207080a05030f0114060304111207120212030c060a0b060d0c0e040e0f2104080a0b010303091406090f01020f030f0904050c040803 75
    0x2a009030400900c0b030880426011035250200301150b08095041d601d43d40081200c820050b0f424102801419420301c64502d4082c0c03e8103038504181d076038411100300560301d20040c5c001600c00e5040d101107951001c20b5658600f0707140001409a04152461560390f0506030000802e1000580c066507500c01c00741c401340c02c2d80d86d16100c040d009010444055009088100038407411201401800080c103c035080806d4090991300600c1811301d502c100d2003801c0e600c20001c0a00503900019a039520a48680001c81d120b088440071134200c3c09010f21243c6400e0034034200002c0141c107d090f00c81184000e032000c11100240014040d9900080580c807101c640005140040c030f41c141c190702079070700e140801403607250541c0c3c0c503881850145402c000781c48031a1490014010554000308500c002c1080f080709803a0b8451140005905100b84800c0381d11480308820b0325100340c0d0003448111010307101403040e2500c0f512540c40980e8141c0c040f440940c0f06038541000520181c6602040c2e0b002c1e608100d00550400d003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 125833174 1250 125831924 125831939
    0x303070f1d0a09060e01050904023001020d0c081501140f070203030c0d0810140d23010209040b0103060e0103060905100c021006060c0b042a030503130816 68
    0x4030080341e05142511000d98041040d21106141d00080c418500002143e91a05608100100040c0c10251041c5865024400944d0f0b400c41c58190707201da84c0c400c8110110020940c1c2301c414002c000076080950010503011030844050f4000c0842e81c1c0356031070f400916079a00c4a800302d1001801070860110f084000c2c2d10981111300e40c041c0445449050001d0710b04007094000a103142c0000c00e030803031141d11590005a0155200600036000f40b0704041c588911801d04144c000c010380c030503405030702410324140007906004902c59a00c40d40c0d1a240100c4600041040030b15020354415079031540154101f0740c0c0b8400651192180c44c0844642ca00c032090542d003169100409800390140c1607d4900c074600301400c0d5030105128455105420343c004003000010f00c100e18040c0e82240d404802130003100310158010501c801c0045600c6035204803600c190500da2038150701340040008120f00b1310984494080100310000004000c102400c0c1541c04d9017555500b0500d0396032a03803040040ca408103076a400c00206 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 125834424 1250 125833174 125833187
    0xc0114030603120c160f0317090f1002010606021c2f0d03050403090e04080a08040507120c08010621061125120f0f080402030c2206080303070f 63
    0x41c401001c0e50149040c0d40240011030300240381004054001c10b40000c80c2c040301090010090600d12000a102403845e04e030035221000750100314036040b0000422008a40d54001c0340d56860704000d2101d40c0e00445010001d00030000c6001c0c03600548038810703104000254035002c003013189016075500203c061700d1b0b204071070f40702c2e0b100c904902040d03821510042410308107000030031102140742d030005800d141c182401884061103600c00800002040d06000c00700351030f50100c81051402d8100000c02e0f071180d103480d17841d00102e41e00070f20074500f035a01c5282c10051a030b080e010444d4034240c0240259900d940311310f2400c6911140c00d04038240b011151400185464020b0114490749040301e03804c02e1a6044c0310324019400f04a040c0d1000c0703c9807500b0f0204840d00440d00b01c03055071442c06107991740840001911008809207007034140101040060115078041000e010601030280c0f031384801c441100d0b004400040342c41c43e001e04003410040042a180c00c0042664840d24040da0340c2e4000b54075080c0c2c2600c51 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 125835674 1250 125834424 125834431
    0x20c0d030e0a0f0303050c0705040603030c0807020111031b01050a0b0f1003060e010e09010e120f0912010603030309030f170f0a02090d080417030702060306060a020712150e0c011403 80
    0xb0660980c0003542c40d251000c460b00441c004d40750300c0c2e0768401420065003030041e13a030052440303546401d60500201c2da00c0001d540d07855038800d1003580d880d0514001030f544004207048902d4a8800013400080212031007401c6003584007a60000e00154581c01c42050a80307041c0d00c42c25030005921004181c0d80e1400500d070038001d1030300303040008400f5241e5100b1540c3e81c0d4260026016100100e007401061030091044503800c2c40004040e02d101e016006183c00a4030821000c2002440b01180c182102d9a0b0b0502c02800d03014042c00030042c142c1e880c600075001d8400801e050700030072450180b040c0154064200b0220042c41203607e08016524030302d14804544010700341880003070303082c8134a80042e100c075526803420034000c00e40143c64605c2c0606054034191166200203050300144115001038440d5819613800031307822210507454403079043c022850441c0c02d9004421803c2d4110240040c040c0700d50301803019444143c0207104e01601031404540d514000e0104a00058103d081d20038010f40c02d1005c0c40c0c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 125836924 1250 125835674 125835679
    0x20f0906090112140105010e0108090d0302090102100905010f1d071223060402120c0a0b0706110a030506090f0106020616090f081c02060402130207020316080f0d020c0d030e 76
    0x8550343c620284102c1d54400e006545246903100144115a04240e50180713400c42442d00503801e06e000200181c941a0000e43e88041c19004940d000c1d844c1c3c000d000700344007041c035032100700480c00c900e00701980602500d1410f00d400c84e251517a1401a038182c800c42d104900001d10081c5000c2d458808545002c0b103e04106031001254291444a15495588030580d2040c260001b0140e608040c010010b00a6907004840c41e2940310300816880ba032101100b040480300d50015050b1141442c5c01d2134000740a410301e240201c0c010000d1a5a81c0c280c040d4040c90144200780c861020395568020002941e8a080c0900d2015a00c000b0009540d602c000328210b000000e945050309400765204d80c50344145120303400004860700503448020400e4806216640501241e20051100781006c2c0c0104002c5115030a034070030203580010b001010754034104085411162001c0d50b18003942c0d51050601e40300c0301220004235503030040d82c01d031080180c800941b4811454004041c0340b00142d166a050724000c042007089078 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 125838174 1250 125836924 125836937
    0x106180905090a02010212090d0b0c0708040b070c080102070201140d060509010602030a1b0c03030c030e060307051909140d031704030504030c06020708030f0c030705100605040c03020f09060901 85
    0x165244540c001c060041c500880204102e16840c800a400c1a0120300d02c0210301d070091212a85c00d41d54481d201000c960403064040b00307a2640012140d0b24401e00d02c3c0035113a0180054000b0b04422064014925940104900460507850b46080c81c213074801c045c000381c009500c00010381c0c0c0801001000703141c00103040c000018469503410228210400076031014016030004070f07204001d150884200c0002d80b10f0300d03500101801195542c007580c03008600001d02004141c0240004060003100d84090451000b03000c00e84900e8080e40c010034030340c00301d44540604206c120180081038040e0001c0300c15030b036002071903103d5403850328244840c102d0004000c4d401c07c4030300323142400c031420101c3e0150b003c1d038040d907141d03581d071421820079510b22a03c580c840b508550110f0401c10001001005540e00d41d81d850715800d0b91100c680103014518011000040c03c1c600400b01601b2100c9100d9101800725102524180203840c0b00041c01d03012805010420007030075004000e14407441ca4a04c0c01054504414104103 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 125839424 1250 125838174 125838179
    0x41203150603180c0306061e0305030703141e090a2103030c09180207020a0e010b0a03051e0a0606021b06041202010c0b0a0e010f020307050d090212010903021b0612010618 75
    0x1003101603109440e06ca0341e0700f200344008082914001c80b1000c04011a904070351a503500d0035647d00c40c2c098040d007044100003800003480355840c1100c603101035111032a414401404040b00300c075031003001c0651013010b802800103000580c80c00001e01c280d901c006914000031143e2005d601500d001c0d00f0507000c2080081d400714101480c4800c1c03088030005003100503112140c40c130611621490a0300100381d89009640108132140c0001c0440325046254074001c83c40d07440d102100d200b62003654808021030b0000c9001c115071044c21740c2c40401200c61550880f4425800101c4050303d907003c488c1540d800a000308014441016955002f0305980e02c1890410288401901c84d100920700503544c01c1c64040c1c4409203c0c072402c0003401929285580c50108514608081c44064118401c1c0c105442019445032290300940d07880c80090000615084000c3c8588907541c1b40082d1608a501d24080011164580040007400c00c43d0903900301c0c09954103003480b01d9003400ca050302e02a8075400d8225100541c0d01c4003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 125840674 1250 125839424 125839433
    0x1d1f11030d0501031205030c0304030e1f0e040605090606040603051b0f0703020d1704020d03030906020c030903010e0303100e0a150303090e0a0504120c0f1a04120315060318 76
    0x1c00100d01c00140000d9154110310b407845d03100e034106401808000007031042c41803400c040011a500541e01d420b004d5103d003190300204040005501e40149121101e8920218068129401900800c0100c604004c5192104100328000e141aa202900040300303100500146c0d00a038481d82c0c00c620380c200020300b0090794411907a2107601c20802a0403034580460401d04154042040072061001810840f00c15084101c04115030040100060700c1003019904d042d0904d4004d40c003201d80c451f000a8159900d075400a0050350380d0b40211081030180d0b103400f4211644003004401c3c0c0b0301034500380c5102c800091510340c0d041030f440b001600002006580f2403016820900b00d4048800444c4a1340b2184092864644d421b101490000c184100142c00d1504100c0041c24200a0518844071420403030000b1255040004880300c41c60001402c0421842c400915540242c0d030a034421449500300410b80701600c08200d05403241200035959408801809212444c0640c000003000c080e810942151450310343c69 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 125841924 1250 125840674 125840677
    0x207020a030503041503060810020a0c050604140c040209091503070e010f032114180a091b050c0a0b060d05030a081504020403020a090b0f0a090b011d1f1103 69
    0x801c890b603500c005400c0040034801c075000804400315040410003a1314007820a6112890065611409a800988103107801e0080b01d000741e1403504038088130134a140525040036492003009140800e449034056800316490700340211150607401034000303500390300e646644548030350b1100d420720351500440c03101040300d0020b0081c80e03000300030441a054203a80343d0f06190303841d4841040303400007802010342051400394020450340c048500010303089903070740b540c1c15008101d024200b108680c041900c44000400440d80e030010502c0c3c6d500300094002c010740018042c0c9162162880240403078020b90490300210b010250815030002010302006c81d06403030f07a138a00d4110307030080e07004501045161061208000c25a44c0b4582c1030740c005c0e034003103241c6400c43d0001824506584a070f070030050307242d000d003d80d00e8036108400645040041c24408109032180c4210001d0604284010300240040100050600542c090082a81000380c048901c1341341d41e034091400a00043e030711005000d0100d00000300c5200800 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 125843174 1250 125841924 125841929
    0x120607020105040218070e0d1104020a0201090510060f090203130f080a0801050a0503030f0f1b0a0b07050304080304020103020309011e060602070f030b010519030204060605091c0b01180207020a 85
    0x3400000c09150a1041000d0356542540030700440003248108104030b03070030201e01240e0321030031220150140368500d050f44010340d54202c5560040e0011404106498054020712145441402565480c0d00c3c50721940080301c030148aa80c01c010f02070034003080030751302640c01150807402c40f42404801c0210341d140d40c50110700d400c8003292070010001d07031034588680c0161140e015181c12241541c0083c9804000303582c07802031030301400801c01d0000b40c2600103905a41196154002e240c54813106030300c3c1c0c00c800e603124014410b0540303001200c0c05c0080d40c16841002185e11490307000d5207103415500e6030b400440094100070250030071036513128503400e000d51b01064201030000f024179010a80a08140000b400c2040503404114150340441003030002500140d40300c1d064030020350b000ca0a40b0140c148c071210b400c0d010390000c1d40283c580080891404d91002c02008000c1060b21142c42800354640a03040b504141d1001500f07401291b40180404280a170600e00002c005038000350805440b500045d8102426a = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 125844424 1250 125843174 125843177
    0xc09110c0f03181002012d0c0e0105271f080703150314010906050c031504020c15060112020703021c020f0715050f04120501271e120801030309050d0302071202120607 73
    0x1f00f240f5140e05a960040880910051074281c0c058600d410019000d401204c0240f41c1c0b40703844002100b50250141e1003c0d41c06900200825200c068096624040541140c2d50900140140c400102460701070300801e944200c942c42602d821600d907172500380c0062403402c102031040d505c501c2c03200040b500900509000e10710034032015640b030414010102d442c0c224030090038080c42c0184000083c110000c1014a503a1086640d041c3c00e5665600040316081c02400c14080000d102044030710a06da400103216032046034a19800f45024003104069a6a21035215203142c940d00c1081d050000310355458204040710124188142400c0b004403611803507070042d41026824034440d40c1401d0511a003401342c85000320740469801e03100340c0b5046503d00e5007081144003804107880c03284020314900c1140d264048954100140d03a08a034510480103045079020b04c000d400051071403101054920b40007100c1071286034141c005007a400d1520112084000e40010103036440010004840c2086000707004441c07042c13400c0d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 125845674 1250 125844424 125844491
    0x120b09090d020105060f09060409060b100207050301060f031515121401052a090609060301140f0a080304180207050304060909050a02030709050d0c09110c0f0318100201 74
    0x840083c02c5600052041780300300d0034510002c80039101d110701030342c1115041e04e0125500d880ca0600394090401d10140c40d800c00d5109001800d515404511041a01c00c214002d2181c00d640e2441c071984140c4a0102816075080441600300301c0866500050b02070568030b030004030080d40c895a803106241c02020543d05050700705441b01c0c0c03d08003803081360361200c00c0d00d0010f4010000c0345040c1412000868148000b0ba00000d40440107039100ca055404405001301760756620760b1100c4a00c2000110f1014050240e50354078108200c0e031a00001d00401d45e0034440007141450314002c51454240092403511110359400c012030404100140020405002c054490240e13441ca81030072001114402420542501c1c818030501246a0344013014500700d03030084031040d2031885a8200706028110aa0020791028985a200c10820031050007809200d010102519003200d9030030b200ca900c0384a55034560308000b03000e512401d51480d01e90b24040c2410b84074030000508208190352314488608120001310030804 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 125846924 1250 125845674 125845693
    0xd020111030d0e1005070905190302090115031815090c0905012603090907030b040e070806012d050d050703060e0a170a0e1215010e100e07080601120b0909 68
    0x204000404c4030350010b03071040000786800000100650554043d01d03120700f00c070701e50601d04a4040380308200516001080c0224950703440c0103400c4449d1184100c000404d040c0300303d0710a101401d044106503079404c510340d945148460541d900081807103440c100c80800c1c031410003007060143c0b44152406042580300344c921142450241c000d050780d80c003030340c03070354503801000303d10314544440980d03680100f4a420081401c90301d400000b000341010b4031008405124101c1d00042c7c0000001d80c41303048038140c10001501c00c042e00394401002c40754a0510010005c01041040305080418017503205070b02803000d5411440d143c0d030700c12050741c4480d400759155a20498001d42400300540c0c515942540c08011390b171500c507000d4009013a2004d801d00303030340c4145030106401003120b10510140c049110200001805580c5030a00c01011410546080860301c01c1c118010441c1820f003d440c60113100c1d1511a0911035480000440b0350700003004023000410f440e01d0050f81503032103444d640b601448000024010350803 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 125848174 1250 125846924 125846951
    0x5060a03050115081504080414011b030e010e060c0a0b0402010201021911060a23070207080109060f060801050705040b0309070e0f0601140412030c020f060a0c0c081b0d020111030d 79
    0xf18090b4210145d40200c5090100040502c000c07030741110720074945410034511100069405985410169135414020f03032440040682c0280220342d000403d0b20b40e0180b4030542000c1c00702c18020f458440189501030020300d4042450107902c1070f4032030310520000d40b9041d04407031040004841c4040c8407001c500c1c10340d11400d5286d424040c2035440120b0b6401081010302e900396403000d1044d00b100a81140f0450400700d84041d10910401c0003400643c40244180b108a1525030001c0801e8040101841e04c0c0c1040802c43d40c4043c0138107402650303680d0701c040c105400d041100000c0d40c005008142144102180011503100d804e02c0301d071203410a6103200e0180e00d841c60001d80342040d0b0b030203100e058400400c002d01510341285080452150107107030409000c41c85101085260720141c00b003951100d00480da41c1d44490f805080445c0b031603c54125140003540c3c4002e0b290341c440c1c05d095204041c0f031a1400d0752130a800c0042c034421880380149081401c1c040503141007400d69208020020a036910f6001504d03030075 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 125849424 1250 125848174 125848183
    0x809210c100b090f090a0b010602030a0201060504020a05250c0b030a1802150a02011514030d020105040b04141603060c18082d1006140108060f0405060a0305011508 72
    0x1c1c039550000d10003805440006920414024485001070139184007050f2502010805580c0076544504420b00a5071903040c0607680fa04610f280d06d0040d030070404d000c94541410b000f96480b54503241c4410341010400b107801101c202040c05800303003682c51138241e0804154402c0c0100300408480e900b060f80c0c1d04040020b4020742d107a001c0c0c00c0c4c04010002c641a001a1900028000e29190412240e500c0d46052a0102c0c050710310030030201e0b0300c041064000325100c40c0242d0070b60f00010f0103e040b5942800d034a40113a0a030740e01198003500140d81600060041110300501c000740990100c15181103480124010804d44000d40080c0c4940b84e40e041941c00041d00144040108a03c40380f07882d44162503c0180d40d07035418809000e02001759041c24105007064500b1140c480d02240c0d1050b81c0c41822010340000080c1010301c030318480c400d200f000d41000e95000b0360074140180f001814145520084006000140c0300140640307400c40807052001001c18070a1040c40b000c01c2450b80d146000e41e00e0440caa503d070 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 125850674 1250 125849424 125849443
    0x3020a050d02070b0613022a03090d230d0e15160606050108090a020306040219050a08100f0c050912030d060605030f09010b0303160c0f0306140a0513030809210c 71
    0x84e8410001c000d4200284640c238a03540205136a1000c010b0b080c4086613056004010714250441a491075a004200c0070030070746880349a0f82da100701d44002e00d2200e9196603c02c0321a4000100c2d04181268036035043c10721010702d04280c91207803a4a01459900e800f620f41808003010f40b02c10b0b650700020700c05503030b20441d0150400f01031801460011030b076800103503e83c0c4003c0d100911481e919080201102002d0a1050082070014450b100c0c0a548030710b030b5078840f40c42d503c80411082c6048042200c80300c00c0d01c104003464145a96139414018071100744010391000303070710710605440144540300000102c1c1c010b20014040fa03984031503d80c00e001c24440c60401d405041c608469042c00d14100c0326480c00025107409080401c001d10004002d4181203040074400c0d003001194051840010040c86115002101e99054030701b50b01840d6039500016900719881507486000c400c0050070502c0c00b00e48030303c2d4074a400803800030640301620031213503070418410815012102085000715011032030341000d0001088 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 125851924 1250 125850674 125850709
    0x11071716050102011e0506120d02060f0604021201120303091b030c0b031605030c1303060b010206091b0d0c0807030f020109080102090a0e04080d0e010f0c051903020a050d02070b06 79
    0xe40c62460307010900c41256017180f4500e41e0f4a000403003507510041d1500480035140c098481003000440003d442d000d040b1441480001e440340420001e0505100701d03030b004840301200d10762903428401340b1419103001030420350400d42c80740c00c4e902c041825a480031840075800340c0705d0703020186145820300c65440c1540c00f04082010038004c01c28140c4015805101e581c11500d0800c3c2c1d25078038400005039074050010b024011201ca8000803040055641c000000c5001c00d0b02285d115541c1c400c01c0039601c000d00b040f103440844103240902c4550400a50458405102e54910300016840b03101e0145003003115402644d14601c004000c405550304800901c0190404000940c030f4940040c0c00302e00341004520800c100090f102d00080e061180795030540b10008551034050180064002d1694081c0000c2c580c1e0300d440514028010420030701640460701001106981030b858840c0701c50341680250017010040040c44410842c180001c9524402012034900c40d9401280380d08290b418080001480d40f2500c5 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 125853174 1250 125851924 125851931
    0xd0c0b07030f1b0e1c051e030c06010609240e060307030b0d050a030314010b0301050607021f11070f0303020c0913020d05061902030705070f0606090f050103060c0c0803071107171605010201 83
    0xa001c40c4021401f006a4280e05d1160782803d501d80e03140b54030754400d0b0400c0380c000780213400c008107810f9440100c5804803407030500e4580b07501c80008189403411070014892008a91905030ba0041402c20743e0107035274455030714180041e111070040085079046142032011641908110081001c064041c801c218540350310503986e4a956041140219043c4018010faa00c2420301041910840d6900404200d4500d40d0021490380d10381151000f41c60244414107540042c00368003030100340320420341000c80450350140d00800c0641d8030101480040134028201041c1c154003520040c0160b1190303100c003240d407807040000708400d1400001189140018a0b41806614010400d012580e0341c414240d030031a40c1c00c0700060305036501506c1d10718020180d9510a030381d110b050499095100083e5408241241d016510501c40d80c41044070484088107200d80041c8122418401b240c0c01d280b10704814400312102c80211a082e0b902d940c910b51403500c201c0030403201c60303000142c0c450312460743d0301d002c0004040c20b00007072 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 125854424 1250 125853174 125853229
    0x40209070e13060e090709020306010903140c03120a02010c0207030c062f0c040b040504080f030a02040302060304140c0a0b040b1606060b09030d0c0b07030f1b0e 71
    0x25141800900104100000d1908080c610350350b20618105045007407404200c250f41d603040740c1c0c075100c004032240707201400390341c00c0000c84170b4031070003264803800050b9214039a06003940e450003100e426a0500925500c950000d50b503040c0c80806c543c542c0d081c0801883e64441420314030090945100e2845c0303e08540000c1800c000007006c00303100c0d000b40c4034142000b41a81c0724041d21180e00f100c981381c13201260400b03402942d003e00c1d4003080ca40314050381030741d0034015404c4000c140400c2d5142603a0040041d40100311040080703104202035904600d544c000907282c40e03502e40016a0741c0c1c209850071340d46a295031040940c1100c5c20018400b40c0101510303102600c81c60a20482110302541c414452002c400241c5031419804c0046012110b40c0d009800b002525266588807629801000c0c02d18042c0c1705800070018814003030795000e082d442c0c6c01b54907050719680d41d400407000742c820020054902c5803129116558650038030030003c0d500e801941c03102c0340001703400b04010324503082c24900039100e84000b540 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 125855674 1250 125854424 125854429
    0x1a01080c0a03140c0405012402010203010f090c090b03070306261b01090f030c080606060f0d0b04020702120105070201050112110d0503070506010e0712020f0a0804061b031b05030402 80
    0x1003200700c80d0481030710f00d0781d0303400f0304a51800c21300d0380861641e01074940000442e210002c1507a20182c0b880c5003803006605c11407090183c1c206d100c2070051205040d809981009100034035007000322141c5492900400b450340d5485d0300891a0810341d0b41c032011036240c240910060f0f28403800c18400380c4081000d1030048280b0100551900702407600c5840c6c440259140350b2207640503833400c0c40205645818010425540c0c01d2105c84592540502d101a0090384089032551a103807082e41d101d99080d981091070150b03c0c5132420001c21041d000c498001c1e4090140d0b80141c0d503400c0c50910001c40810010074a440c10030170080c01c40d0f00c160090b042c103500d000180d1000c1120340300004107005051360b54012404803424405d10f107004150b001001441040c0010407013410010a141c000c1e03004c0d842d40100c2914141a40b020b0380070300350035a0089070091003001c003401d11034581c5c81d402502403800080d0011200e10002c410441580d04603000c6900c41c042c0c00150380003004424002065881c1080c00c40c03e241e0300 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 125856924 1250 125855674 125855689
    0xc0f300b090309180405011b05040b03070e040501080d02070f06090b16062c070e0a0c030b10020703030e0604030203030a0c060e031b06060d1e08040f031a01080c 71
    0x180a000e058180303000500800080003100c05030b0380c000b484036604080000f001c1928140845080f59554200042120036110a6525502c0b019850325a542845c0c102007692107190001407580d0100b2021034114105a00d40d4841c41340138200c0303100902580700003031402034681940b55225100f41240403070100411548010000183d43c0c10f007980e0fa03516010761840101e0b0088522010b80124a00048003042a5a40391600140d0985020081d00102d44050050700c44c19076105c2c261075015400c3c0041d50b91b40c8550f01c148140e82a500380011020a0100807840c0c1d04442400344d0056403120320b092003415007049040001840c104c400030311782415503012945034014400d0380c01c140040c00f50f00b04208501900300000711041c05044a480d00c0008500d02c01910b50305c3d1401685000380030101c1c4082c103090341d84050a1b034021401100c0c4070504000044041849441518180c000340400b1513460b201500110045000c2c404907020a00401e00001a20f40180c0c41a0000d80c001c01b160340a03030300d0780030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 125858174 1250 125856924 125857019
    0x80304051606050f09040f0f021b0303010305101d060702070906050301090206040909050a1e0c0603090f0b060a080f100c1d090a0207080c060103031206030515060d0c0f 74
    0x9132a40340c081c80004940500080c0c1443c804c0141055480784d591101136010300350700304016030407003c80862001e80c16241d00c028000079049404c0f2454400e0581c2107a00030398075000329249004880c40b030114042d03003401c105a0f50390005030028641008502e10034080c100241408400070844030f4030b280d0018806200318400c0d14400c1e40c90742c5510083c0401404205d40c01504010042030703020902d07500040500c0000f50440c1d28100071503001c945503101e07200704451160b028610108620a49e140c2c541043d400a24035030348100d00d0280420b203e803007840301040308041d00c1c00030088060894100760580f960700f40e8003410040181524a046880c200e40c403a00c02400b55014081e40d00d5101111019105d104805020200006050f0304102c000060b842d0480f80071341d441d1000d00c002c1468840903100e113440041c000e40d0007031920b40a41d200f481a2160464001414220f003070109984120031405540c0c40440380034441081080f10705190312580301c2441040705603404c011400e03e8130345c1480e40b80c0c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 125859424 1250 125858174 125858197
    0x2071212090509010b09180408030a0b0402091201020415210b01030906020c0c090a0605031e030c0604050a14070e0703020702030c0307080109030e04020307080103140c040908030405160605 83
    0x6586141089009039a01c201902d00a000c02e0183c1d138403807000c2e54041e48518446402446042e01c440041020300d000c25010701e60080305540366407500c110304030240c694202c1c0541d005070f003000488255518070040b61040f04d9007200250301c0d40e1400e0608100322007600042c00510001040e01801d5504141e00855183c0d002c01c0005180410080120020407064000404891000540e54807003507002401c00383e4070303108030f4800c0455514811804161440c40c89000d81550018020f542250400031140d4080d603110b40480e41041407046413a8500803040c0c2d419140758105820540a00c128400075444140241c0b0090007a107103051070510840c130300207115104150340420808215501031003a103244150007001c5615058560412500a18602c3e60880205030396901c1840070741464003c2d01c0c440d90b100d0300c610b02642c5c61500c0e00d20320081001d00c00011401140116100e03a91144140400d442c001d900c50783c0c40303180a25240346402c0180d079100c7d0351400f040608000c501d0340072046850050304c5 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 125860674 1250 125859424 125859443
    0x6030f0d080912030a05150d030905010e0103140c03010302180c03011203020a0615050a1e030816080f0a0f030b03060c0a05040b0c03030714040806060108151806010f020712 76
    0x41020843c180030350480442d4030b00c03200005210145030190401070081c000311050b0030324825101e00300402e040d61600b0080101d051900d04124a41c0605050b0030340307031418100840d0706042c10501ca15035460440701001c400d84e000c0b00600540c02c10903025101400d07112405ca800d42070940311030840f404144690684d82c26140e0070041098804e11034a8225030b03002206102040c881000b1041c02c640f2070013281d0103070805c42c40008000c07681c002102c2c88421403000b1004d2070703400c548507174609511a10f64004041c03210407150740001d0b40072000780701030444001c3d040c0d1541440e0500034044d00a042001d810182071103000c21265a01082c0d00b500b102c031a07141d55584940420040c0e07114000c46d8090400c140c40410704080c1e106020000310300c41c20155444008400c07442c0030750f0400d4010350240f0415035100c46d00190295003c0c1c1001a0840501c042200c0b1200030381c0002400340e80c4518241070022500014402c003542c01c100c07880d010022030700140860a003010240a1600b44800c0d01900c02210b = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 125861924 1250 125860674 125860681
    0x3080105030d0c060b150d0b010f0c02150a0e030a0f05010b0109051e03010f0c09050315070807050c0709020408030a2a08131d0906090712020f0a15030902040506030f0d08 75
    0x1035400c5d00768406c020503107038030b40c8401095450354010b045103040741d80820001c10b0284034640c8140054401513a0040c040c0c040c0c4001d0f0700000ca45904010a00000d000b40c0d490008100d550030402a00083d100f00c2c40500313542c000d40f9201c0d080d104102003c506204c44103500f8070039551203907003520540886000c004d030400c0410f00006d01402103480404181441c05800c2100d20340d0081484007521001c0e82241c440c84034885407074284640480e040d100181d4a01c0102c2c1e04540300c0c40041021120b110f040300c00745030f1980d6101c4120b0b07101d80e000c070f14181d000140044129401c0031924840d9142c0244d200d410400320f800110030100c0000d4010038031640020f804003081c00030603007000a0820182c4515121900c43d582107040001070300d03c84090700c641e00000d00900b0001900e002601c42100044040c480e00e035092044002000c5c8540358090320140c000f2070b403940031140c14442000b107a40c001c00c0c040010300620081f1007000d007502d406034000c143e00d10300310000001c80b100f20400e140b904000303566 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 125863174 1250 125861924 125861929
    0x3010f171002040b091c2f04050f01090e07080709020702011809090512090f010e0607061109100201091e0f0803150111010b150d06080307060903080105030d0c060b 72
    0x3160100e0901c80c0901c003140c0402c5444131400a04501981030b82c8840903440300f040c0380d0600c4d10a150004000301c1c0c02040100c2c0103244400001c451840301000d040c0944100c0c2d0002d07040d10720407103260640800d118010860040c090080211440b42d220181003464104042c0c25103a0015001b14901660002480340841e44514149940c050f0030500441c0d0b1a0784450351701028000e0075a0581e00e5115a05104010036150000c031031540200a0400340c51800d10f200540704a1045810140d101c0e400340541400301f0254014030306001c0c9054044c59482d499481041a403c0c0811200c104580c54200340d803000900d40044071049541140404940311860f1074a08211105500d000702000400300602001218a41a01c4450142621810800c0011040e060300321550391200c00c0d4804040c103d04585460100000c001c400c000400100d0919110001146036601458044a000707030b0782c0101ca000e0603480640503015000403000340c030070b41101d07800c01005100c054401501c400c0c2d0340e640c0090a82d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 125864424 1250 125863174 125863183
    0xc0b03090718020408280b13050d0305010e0a1518020f0c0a060506060906030a0f0e0106031127010315140a05040210090506070f14120c010e0303010f17 67
    0x4151582c9a030072818207200140c0069041440340b11480c0c4900344d81004169000c5002c1640070200304107203403203610307280c48880c0f600c48003505010320280001c0c21100032560500c00c0b80c2013042141c4012803a9450000e411220036130003000548194a426048102c0c51444c142240071584440b04100320403403029602c40c000e100391411461f01c2603000400b15100c1c400898074461036070240c18100030682e00c5d02c09102e1641714451400c1d92100d0100009204800c0951041d142c4082220001400c0319400c980799084407455041a15416371244080030b0781d16007642881c8028041034000e9501c2c5640090078070803824180002060007180c100064005142580110211399000703a00c1c0c407003800d012407818018042a6001c1e8018980b1086080c0e1050042c0c400c141140c9025240614101d9907880754580fa6141200454a20030028100110303050101b00302220300003000c0c0016a1804c003024003500311511081d0b641d0050b0018801081003441c2030340001c00b00d43d0401c61803902c1100c0348084a080 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 125865674 1250 125864424 125864429
    0x907050a180b030403020d0e03010902060f0a14130801180f030c061e06060e0901142b081b19031409030a050f0c060f0714030712050a08130c0b030907 66
    0x406000f10812040c15800658680d00500a07154244005c40d14000d16003607030394081010350020410410791042410000c01000c04221030310340554114000401c04450354421004441407401404d4103006040c8284903e4040240000e11581455226584c0700d842c00207222001d4241310640e1081c0040c050a078001c030701c0e01e9840440c42e13441c20120f02d0260b002404240603170300008103c0d04140f40107050111100d41a03501c010f40e800070312a06c000c10000010120301d001814560760303010121000e6440203401406510400c0c0031902c070000e1000303090140c80b5480351002d007035105410030040504114569012030350140f43c030100000000d8181c1d950384c07041840141c0c05204120328803052210108500c145108a402a560345071080ae08000d000c0c0182c82803440c40c140c00b003101c000010404d12044040b135503c2c200341c0303082000549540203282408070544000c105d0014040d42216800079840c3e500038400b00c0041d00c03050240c0ca0706200c4400c80e0080031452600000070400200081040100 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 125866924 1250 125865674 125865689
    0x51005070b0a06060f05120a020d0e150703050c040e0601030207022b0210140f0a030603050313030c050103021206041d160e0117190609080304050a0b060907050a18 72
    0x200c0c100b806489008144901c520300004045c0d101603088241301e80b00b1280c01102080110403d40c0b1280905002503005840781c0842e142d4883c407002c0901020711104603c1007510030150700b646050300000e0280d40004103049000d00c010041844544c601c0b200b1107070450b00a185c0140c40301085e1000c0380541040394440c031400c40c41d4010a040d907401d0b140e0605102ca10a075840caa031030030310a80070b541d584004030440303680b0340c020300000090400c400d010f000501490301e004140b00381d0325183c3c01d0550b4400300003041061881c49003032080c0920b20800d400200700a103011841c2c0414041001b00d541e80192080348540d4858000240c0d0b090b512010010540602060f0b40801c90107a40100c0c1f090514801d980c1c1020390707070303000082c47e0307900007922075803480c5500160010310385404582d40300c0800c0326022280e0130356448445012440e020043c5101e41d1081c8002d014081240c1441508090300404841c81030000e0001c106100d5030150598a1040042c00c14021000c0c021002403a40303001d5400058 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 125868174 1250 125866924 125866943
    0x2010c02150a030b1f0507080d020c06041e030504050f120102040b0a0e040e070b030403050f070606080c101209020a080105070203271e01020f07030b15090f0105100507 74
    0x50160800e60001e06a16070151404c104402c814014000401d103d02c103211924404440d1781d180d098011401402c0c074510800b0494603000b40f0401080132071304900300d040f085074808070401c01000258182c004410341c04400c42c0a0844803950010210b00c03641c05541e0080f115603030003042980301c17090b03d51034a500200017952104e0322007018401981140d8222000146142d044960504084c8a09003590784a04060495035061030301a941c00d40c00940202e0421001304048103420b0100400343c00342c1c6119040c0884c4041c40c0042580c6028030090ba624414180d695801e1009070300301c443c5c0c080840d0010b1011070802000d00005007200c0684d80800d01c9542403008000d502a404002440703400103103a041c1100400640590018151040700182c201c0c202000c0541284205203014501e45414070480d4035060410b100c1a007071103441c0e442214082d82d41401c0c081ea80c100c544140700c502c4c80035604508140b6190715041c0c160348042c403c0901813401078060203500e034420011600810b81105800 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 125869424 1250 125868174 125868199
    0x20702030d020d090512030717071208070f08130212072315040303140d0605060d0f05090307030207170102070b04050a06050112020d03081012060209030d050a080403080402010c02 79
    0x81d480343c03802c000d07000000c0d0100070081004d1400a80c540e24107450b5000650504c4a2952600c800741552520030101b001c1c18043c1d0790001c0c80d207024164141419076982282400c2004014140c402803841c128180010303030003000440444d000982d4201501115036540300c8000103040ca042024075008500b802000540d003110801ca20004142c0ca900b082c0c40915050301c215861a0340350059010050000369007083c402000c410031006000340c0c0c200c501002504a6603000000e00e076a101e00c0e001d210690b00c4401d1a250004188182079202c880c90029519200303623650003c2d21013040340503210a00f008046034000010302541560a060f0b40580076001900742810a0750780d1300403041080719220300300400890244e0380d41c2d003c480e07a00e50181c0400440a030668003920b80070001044031981000703000b00020113225241d43d084c012070260000680d500300310340c00d00d4107002100a80d24140041040454030300d607844000b040d0711a8040c9008101600c4a200403900d0b4800c448010390300480305c00c0c02 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 125870674 1250 125869424 125869427
    0x15060807090203040c080304030302150618040609061506050f070804050306040c0305060105150d0509010905030f0909060901080703140c03030a1d01140a0f030e061501080a020c07051003020702030d 87
    0xf5030056028001d001c4685070b54161040c0c2d070348206c1c040100160003540c0c0b120728981d0f480452035040000100744405001d90038518180c13500d01142c080d0303956605c0b0007119060184134440c000401c0a6080103080d0141840406800c0b8418072900202c02c680018004090003001c40985025080040550380c085c20182400c4020010740e000540700d0740a000000a803c2c581510f00030100c02c1500045420114118011401000014241c1c0c030a13549448190000482c1400202500204459440d48551303541c8244020b1000040481d070280301034100602000900050070710807240e0003442c280d81c502c845042a8144441d440589800d440049140d000c02da400804d907980d041a03001e40c2d01140000300004540a400b0340704035600301201041290111403103195520403801c2981404141603552102c00351800c1c40403a02505111202840758604d5a80301c102c80f41c000d0090503042d030a05904030180c940b2041e41c1e1084911505000b03900c04001030003034042c0c802c015002000d60301c9451000c40c0 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 125871924 1250 125870674 125870677
    0x1c0804050f0312060f061909080d0203040e04020405091501060f0e03031c051b03010b03060f090708072016090609020a0c020904020a080307060b010f1b150608070902 73
    0x101118680915519800078090020903520a951000c2e00b500960f00c9850900801e50302c020304144e00604104201c0301440d460f005020300c0012960707102d80c0c070603240c5042a420081420000000c40d0800c02c41000040002507507035070400c0e01140c0000c0c0c00d03103038504028070381000f1010059000c5000000003074125006000d04000b641c0d6074071012010141d070410540c41c0d2040401004480301440442d1142554a0b4001d95002c442e0905081c20811024800409a00241d01946801c1c500004002e02070500c2013010385490b0041c2c070142c42c1800e0082025011100c0200b0b2082004070101b1094810095114030303042d040d11040507112010782c3d060068a82c3c15150051a0009003490710003d00f503a01da00c00c480c1009c03a00d61b118003041c900c941c00c00400040141c000c1e03a029402c4413001c1841d2205000806105d07200346070014a882c0c21100142402040d03a1400b000d0016440410056800c0e11143c841e0584d0300c900240e8144a4805407003006000700d42021103070703100b804070101e01d1895990 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 125873174 1250 125871924 125871931
    0x10b13051e040602070308480f0702040606030510090b030102120a0507020d05030c0d05060307080d08151e04021c0527070602070510021216020910061b03021c08 71
    0x58581a00d551140323000e0700b0400618440c0c0003107990401540c03034a440485481c00360a01c404007203408003201d044000d040740d00305841210307200d030000400a0440c42c0c01e02c514001002e25003400d20640c60071444540c0e0f50041d078480c403440a52074201d0746000f41c0c0c0a604582a0140800f00307030030981000740c00d07140102412241c000241c40740000c4541114003440c1503d2040802691003442c00e034041408002420025217200d80600c03880c0c40c00310700003105201c03c01c0604c8061707541c402e0034031307051501d4005c0706000c0f90814010b400c40b4618034040013426164110b00c0304192005a61113408201d800704211400410280039450310301840701d040300300309000590884081509541500d06480281c483c401846000c016a01c8aa8100311905022030085d01c04040d6005550800692030b003184841e912149034034003000c01c514041c100b10324202c2841900300084915009480c0d080c0600a81200c1140d022030070035419881586081610070040482c03141940c001101011886000140500c40d094 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 125874424 1250 125873174 125873177
    0x60903030209031911121203040501150902090d0f023c01080903030a0c0c050a0b0703060b0a0c0204020f130306020d0509062503020706020a0f030b03010b13051e0406020703 76
    0x55482c4103164080561410813182c2101400001100540800c2241c4140c0040e09205d40a4200400062030740d45000d50f20840c011400443c0703e01c02c8091441c002810790304240c0381584107200c0d007a030b25141c0b030010398400c0358000700f580c0810190740005903810811210b680c8030208103d510050004001428030365903185030040c2480b03400e0980054030800d40c1152410003aa0090002505d191204e8200481038252070420034080c0d81a0703100d4034100341a210098500a400038180310a1640c948100801001d25039000c40c10111400b500400c40c030000030010b4826900800e4a11066a0043c2112000c540315040b0f40e11440e5a480c0c2007000e90085d030102d400d0a0300d050b00040214070f022486d1403040c9100e042144010018082c40381a91103800c02210400d0344c240b0911000800300c0c1300501c080c038101c0d11034952440305548011f056480d0210504d00170f9050001c08030107510384404c6002004558200402c16541d00e8682c031301c0740d159021154030f05040110901c82801415401081054040d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 125875674 1250 125874424 125874433
    0x2010c0305010f0e04060f020708070605010305060f01150f02100903030b03100504050601030303020c0c130e070501020f07090209060c060f010609080601120305030603010f051503160506160305040306090303020903 94
    0x340d00348003103d5822407080d10030841850000030001040c0d0350144420201c0480e0050030a0f0700c07a2500141500300305001c80704541d44600500a000e02005242d03803202a04505112560504418a0f202c0d8584642c08045c4100ca01c01040f186009001d06c2a40f0f03680760004010340c0b05182002030103040d10b800b0302d078002c0c02191410402c200c560301480c1d200359004030013814aa403031603038200d00035805504d071303458540540100400700756520401245020200d410209a440d03249180da404d203156640001d0540d800650010458140895100304555581e0300c0140c4603483d42000c980c80c0c0c03060030361184050017020308208604024401e154143c07166035503098211038990692940d141b20a0051107441005044500002845603005541c0200e018001003005041440607074140e54094500300951081004804554101081120403880c20380c00b0601d42d40d03150001194451050350391602c1000c000c2030521007494000d00803200159400002040040010304008009401601e5814030034001d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 125876924 1250 125875674 125875679
    0x81006180510051509210105071706010c110d06060e0702030c0a15020c0604050601140414061011060705090103110304110f1207030503071b1d0414010c02010c030501 73
    0x10354801d8500c80d19004a4a208503420070707003000b00800301a510b004030340c6020411010307180c0322480c40c44070303400e40c6552588800899054103801d40304028404410002800313a044800800d0a050300c1d0088020300380202402c0250a0103101000240e181d1a08803c0000c2020108041940b2a204030758244040700000d450340d540c02c9860707105250003100994030240424000c6a03422500400105030703d4001440c000030400040e060000031502a10f241e0406001002074030490244500140000c4808001c2d1036800818180000805802c1034041c0d281e41c00013070b074881c0c0100e481140910b000003c450302884d00080c01806c5d030784100d4003940060304102000904007002c600352809079600c80b0000310100326250a012480174140c1400f80e21011008080b01c41300403d105000c0914040ca02035a07842a81c1c2c20926079410340c141c02117140d8072100750100107140c00480808074401020030703024640c2d101d0782449409a0b0705e8a85095141d481e10200f142080c3d0154800c00c4091a651024080c0740ea = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 125878174 1250 125876924 125876969
    0x4050606060f030103060506041b090801061703032d040f020a060302031e10150302030a060806010e070f0203040302041a090a0c05162918030403110118081006 70
    0x641240710600c2c2c8014001400010400c0d0030981c0e000f107020740f000415090203003800f4028240c190070351011454210041c0302855081c00349102428084940301c40340b03200c018095a803480010100b006281d120107440e5990103403400e90743c4008070920304035400307814182030000089001520491042a00050003d1160b0290094034840e8210f002c02c65100289140d000001850052165401038000305021a200d074031300c1d0001c00c0480840c1d0b00142c0b0fa00e010f191090440322507800a07400c0c0d52100c001004190702004440f0390098003481c10010420b9100b409920b14043c94100a40c442d050810845820a02030480718080300d00701d83c42c281a0f02c403400300c1c00860319041c100100045040007501410303001e200c011040b1602c25a0041107000d01900c50189418044d9442c1010700400707130a21215039410544680600c103e64041d600e0070f482c40d03070ba40740c0704990200702c1c2c0d05024241c800c0d002c407481c10141e000b00500500c002d48041d410824511001026036008a00c07840c07680c01031110002 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 125879424 1250 125878174 125878177
    0x903041a0c0c1c03030b030a021e0112060302090601050a0e0607030503060108180613081207020303180d02030301180920010906030e031b1c020d090801141503010207020312030405060606 82
    0x228484403603d105040c0394804030090201d83c11398540500c180007402c401a12543c0c2a8608010607840b007066040020000400401c2c0c545100700013641840824000759441c500e1503500f01ca07090800d980c0d40c4900c0141590701c40090b9030307000d1344040301103050000e05030400019407199a09a13680b03080380e41c0d151740f043c5070f0460748034201000341c0c8044d0000d00e045603000d16048880e40908141410300c40000300d20841d0362412100b180042e0404001c1c004149841c1c01d902445031100e8000e88912010303110001e5a038081442000752911003080303400020309143c0c1c4008000794001600c120008030300500c0c403110604148885002034504000018800d22034802c0003030404415010b1454010401683c668001e180c0c41010b0090244c0e1486a151003d00c0c0800708a98560b90054070704000071078009081c9428a074480402d0307904080b509008181785201d142d60000c04105030b1092400f040021a009000f4541c1c025054454424480b07200c0c40e046014600c201d204900f125415601c6400788000c0d03 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 125880674 1250 125879424 125879449
    0x602040e15011d0418060609140f040305031501120509011d1b090a1b0e01020d030501060c03181d04060605040c0203030c0c12040902030702010501050105031005090903041a0c0c 78
    0x40c0f202d181a912481c80c00790080c0c0c0c0122200c84200d40100f41c140c40da00100c61603544910252a41d800b0300e0f0014058281c2038590043c003506512009150070740780036149110081c11441d400c3e2441c8050403840c0c3c0104c03440d0a086c40c0e00d0404001d249000c5074800d0003810134000803000b2a1fa00303404c00181110005070840020b1000c54500c01d034010305002d211070a00080c11a100389522144502d101d02c0c01c0c880300c0d000081407030356040146c00c1e80c0303000a41000c070344613894401c0504150050002e00d400ca440e80002c4d661510f0001d403e61041411004c0120058118103035800002500c01c400d41c0d074504c8094080d60140c541084001d030f031713002007202715100f0011200141c0c00a20001d07081e40324600160603030038070102c160b4003000c0c50002c14801550298020714441d40c0c1c04810300840c9682486154054007082c03c1684c554100f070604d00d446a44984110b511030f070416000103860840c00d0050b600140f01d0117580200d0b1004d500700c58040c1c0d4200c0e54480d1050310510010810a01e00142031081 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 125881924 1250 125880674 125880707
    0x140f0616050405010305060409050a0302072301090308070c030804090608250e090a021302030a1805060a1109040e0708121e0d0209090f01050a060503040215030709030602040e1501 79
    0xa820310f0500190041d0000420300390f40241d07202e083d000410010300c0101901d80c0b0a5000c1c00125050084002d1941c810480503030000c0b50246c4181110f0340c001c0054820341c2e4008180645403081d40c0341c2018241c14942005000b45004100080d180b8505e400182c180d40704038007500d417100320905cad500040d140e00740010409608010b00811580002d9060b564000703800500f903441c42413654002c1141c44031740604002006500104001c3c104044c2d1154541003410314a0480760342e003454a500c0e80d00d0401428480e803c40e5107454040782c00c24010100c40c0c0c0c200c0050001d10183ca03c18a4a80d2107000750300c5200ca182c09003409448001701c14000306c43c0c0c010729035110340c0450041c5140c144080c0c1c1000e610b002c04181d081040d020b540c2c0d900b0307088a1195203541c80c651055070412062003400701d610f600c0481809418000d020040e0342c0d454a152403c441c03100c7c001c5c0c69988040c0f04650004265001400703440c0300007804140c100d0039603c41c03031240342c003c007a500c485040c2c0401128610001c04400b01c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 125883174 1250 125881924 125881927
    0x3121b0c1502030d050405150603030c0d032f0307090b0a050304060b010c020415150c050c090709050d210903030c030806041112101502030a030e0a140f061605 70
    0x300300000540700600854071031040302c4c01c00c840d80100c403045030342c00d54080c0c42c26485070311144e0500800e414460342c4800150059410a100c0c030b101190b40319284050242410380b6400c011000c3c0d10781c04080da0402143c04800600c00384410b25000090344243c54a0300021008400031828031401c008481c01c00c00169100c074071315079507a00d405000f0a41024068100b041d08802c01d03000da83e850003902c4010003020741101d500c601d45140014290060f036110300902c203c8402c2440031500200740c40c0c81e4900250741c8802d90b503071740b408211120007103a00202e901907a028429014068401a10410b2116411030703190f481c200c048080d5106401840002d0015070081c3c8d424002a118103c41c1380c2102c0060404151040015086500c41d08001c404100c02c10841701048540c1608604501c01085402101000d100754145d0003522881181c50000074540c40f048070048688003004020003841d005949901f03284c8054505c591580d500f2064010346100364800b141407160007550b010702940c0d5640361035 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 125884424 1250 125883174 125883179
    0xa05060c0c030d05280c0e011b020301050702030a08010f050918070b0a020f0111090904021903080f0912070f140103020f0d06030c0e1003030e130603121b0c 69
    0x10003a40c072003030340440c0714002801800100a40c0c0c0c080e80d805400c1c00ea05400c40da0b00c500c10310b400010f01c0b500100080909100e20306846507080b001501c5541001e18000112500d0342e8141038100101c58002500341d841d00c000c00c001d81e680800070b860441400c0c2d81c1d070070f085e990b101400118034200380541a4080441c4000c500642d40d9500741000144c10301c41a10016552140e40480c10342101e02c0003030158100e2800c800e4881028480c124081c44810001c60404034107401203040c0c01070080c0001d0080016800c0b0b5040c90140810108c01160b114050b10b5a404200a1080321504645100b5000d101002c855000100d00801c650f8260750300301d00241076542c81c10381c003009964805112641403642c01c0005061400b91318000b86000c004101c1c01003500d43c91441c001c2c648031800d6101c09903000c803070030510030000d000d40019803c90380c1500d48030848005030350000740380c1c000c00c000c41925285065400008c0007035550314580c0c3c003c00394403601805940e0f603030084c2000d02c514000030600465a0000d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 125885674 1250 125884424 125884441
    0x901050a0813050d020c1003050c07030c020303070503030c0d05060904030f12060f29040312080423011e0c05190509090f0108010f1103063714030a0506 67
    0x10307030310002018141c00011450f8a41c40d091040407800d440060300305000210460030a04a0f51402c9040c601e0b04021615240707049101d03a02586100600b00a882d880d41000d6640400a9070800e40e00310040d07984e22f05158008000d190702801c94602501d041c040040e1303151074200c140034800c0e41c06444030946200301c1d00049400041805071f04111a5450700049017034040c4031281009401d507400311041c0c004000e020141e8003030000b294107402181c10002400000c41411384511110607134241400162928682480c0b4001402e51010018000031000030303e0001c150080c00110150660378003004e0200c40c02c180c00c2d50820384090340414020086e20740c2644842900b1484d114262801500b0700d044000052881d5078217035285c80c0310642800040c098410284120103a0701c00400c010040100751458104190100500342441000082c414000ca100003080040e507890001d80890380780c0c1c3c40d1900903448038616004001401d09000304407a0141130002d40c04810980000080c0f180f076032600326 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 125886924 1250 125885674 125885687
    0xc0d02060d06060c05060f01030c0905100b0c0102090a0f0515030a0906050c0c0c19090507020f0d030c0207092f1621080709120f0804060503071101020901050a 70
    0x102240c10550402030000c881c9954411003020b030a499a5810445502d42481454001c014000c05041d40c18400100000780580401c10100d4136002008542d940c2c40440c41c1c1e6621103582e0002140c0040011002d80c1c804065000300100c8004847c005102511924107080110681c040c440e000503400380c017086441c03592009954860080700c030104c4c1142e450350b540c0d825100261941041c0c1035011400c1f003c0164188604442c008056400040c1d020030107a000031810402d102e2549440c1c1e882000c070320a94400e216000c015600344045440901459100900405452544c0340043c0106000030545113a240140031005c2604002960440c10760484030000e69104401c0c1c40b00301d10100280e030140c56280700104502030240178134281c80521106481e40c3c015202000c20200952242000407482d080495501624942120002c0041c21407511140e1200d50040240c420350020500184259128001710f21400055582c0c0484585030300c0b00e18242d002d03041e502ea010800c148a442100c4c0c1c030440 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 125888174 1250 125886924 125886949
    0x80f06090c011b02031b0a06030b0d1101021e0303011409010503122208031305040207020d03030c0207030f0b07030e03040305030301140d120309062f0f040b040e01080d05070201020c 80
    0x300c4200f0701001e81c00680780c10248410a0054008240b20f0100e910b024900c04008158a0805004c2101d8002c0014101c07448504014007180466106082c0760740308010440e005054a150034409510b02c00c41e4942e44c0d0070034491091107601c031601724001414085803007030403108040d00421004100c0807002c0c0542d0082090720200d007040d04c01603600c110705206010000d2003030401460303071803806c6a0303288860049500f10034090380c010440a40140c50380c0c0c00d1801025050700e00005c60a240b90000c034101481a40081c01c403c1c451a828001d00c40b14000f0a402485a9107080182044010000341c0700d008030320000c3c115400c2070004104405602c01c20189803800107040100c0f07600380d40e81e2400044211084a00020750300c2d5200010441103106498402070b20481059020840700c0201d91118420f5500010841c00810715044c50301070442502c01070018107a02c1c0d0340340d90702c03007d00c006070350030910a403801c40c071030b54161000704d900035002c0f2100260180d0150035000b03079110500035142d501c071 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 125889424 1250 125888174 125888207
    0xc0a030b0a020f030a09021c030503041203180303060518040506041205040b0c03090406060302030603071809080703020d14030f15010207090c0302280503041e0c0f080f06090c01 78
    0x8010300c10b43c00e58000000c51042030310307040020b9202c4040c0103000c0490440544c002401c2508400c07034001c2a08442541e40c0aa4010800703c200190001c0440c0070300110202c64100b103a10410102c05c05405400907000c1c0c0344140c442070f10891102103120304444007a10081c00603040480031601082150024070349010841c1003291034180c0c3c4298580c403d61214007900c00726000841d0301c005600c0c05005800040c4040d18080d0300b10b052201c0020b407200380038460315241d2040c1d00d00c440340c2c07810f90380c108140494028030025126412800c000c1d4032940503400200003c0e0703200c248180168003000c01e40380a021000350801081c0e8400c0c8000050001208100c0d06501c18a80e00207104142405100c800d50920f0768056120b0094202428038007110180c400e00d102d0642071b9141549922005a90f84507401c0070b001e0561803c04620540b1103004c4d1388026008040041c0d01103500c5200300740c4403045400e81c8084a605d030035031550b243d40304c110550303030b084c044d030440307400ca8030f042d0310940d4000d0304002d00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 125890674 1250 125889424 125889427
    0xa140711090103061d012d090605040807020a0e0408090907020313060f2a0303051f0308070b0a0506010815190f210305030105090c040302030604140606030c0a030b0a02 74
    0x1180000d1070a00007640102d501136180e8607040e10303255451a22014405940f002488030f245040f81c0c1a4100f40c3c0e481d011100039240e554121981c60355a041102003940040c410030081c286410006140d603c18242640990300c883c40001d54155820369031845a90840e0b1000e080c28140780800104080c043c0511045100c280010018000c0344241c0c44003c251079201c0c00b41c4031040000207060031a40d050456920341100782002c4600c0b0781449042030007503051074000340564803440703070039091180803081170908840000080104081c6900034001103014041505c1c90340d8030b4200401c181c4008551290020f23000e0b40c040340d16220401349403490b05000400b002019172030f00c42090034281141d40095400c01c5208000c1044620840c560100e110503c005e28003070701c50944018296100c18400c3d540600d1f104c1000a2100c1000001e031006154000c3c25100d1505041c24540b1302c0a554040c0002140180700200703041303240004a03881e0306080030740700c92071241c0b454494469a02e4001c0c2041e50b01d540 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 125891924 1250 125890674 125890703
    0x4050405040c081603140d090b030705130305150f190c0e0612040b010807080706110a0b270723060c06040804060306080102031005130e010f0e01050a020a1407 70
    0xc144907105520f0f01320720103441d0951840c10034488058041c01e000d1000d40010400041041d8042c2d102c3c425104880c1c1c4407541c94030b4600003114240314940e080e4160303520740c0c00c022082001c08a0109028000030101c01c645440305481d00703045c00d105551180625614000c00c0d405001150403242020240b820428030341840000481c010342c0c400d04d079034140018010300700002c000611202c01e015014035030080c40120b0900b610566260418022071083c042c14143c0c4140070007013080b490581541c4004205124101a12510040030f0040c0c940c01d03e4003200b4041d10070642c0c0c002807050071200489a07190154104004003070031180501451074100f441080240023450f010008240214441c4400795076071031800b440101242ca0716086080705074010070601005011032102802a40c0040b0b441c4030b50300305600d0a100003469220f0038603a640d42450008181d001082e8411030030234582c14002d0241daa83c0c290160101d2050428080224503006a4000700c103149034040c29a481c8a1400720345084c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 125893174 1250 125891924 125891939
    0x903020a090c020f01150e0405030d0c050c010f0b030d12020f03010f03021906080114120105010608100617040605090a08040b0a120b0d021905060706020c0c0108010b04050405040c 79
    0x151541c21100d8031a44460a00000543c100484900c07114200d00030803c910403a2105c2125810500c10388013522041d40202d02400000d0084404514101c60201b1104038507800142c9150008803502e440c5500e0101c007a0100041c40c05200d49101307008015000c40b0b06041340958209030301d5007502625a03404c0c046034110755691030055001e800d4092604626502d5441005084a000400402d20381d055039800c10140e40c2040c140c80c15101650303149000308011001154140140c009a04103541c01d18000040301c4d600144030130301a10f5548030b00d200366074582300155525000d440450340504800341c0003401003109640103581013054401900ca1211440c0c0b20903c00740c1290300001c2d500c11000034000704140d0402d6600501c006408402d000c03a4400030005580781d41000b0020f8001c1b2140c5102d501d84000300307400c0701c01402009240d41d45682050500600030f400c0484042d40c0c8d0720401c070707586140d5800f4400c040e04a8038680c1c5001c1c91b090510046c030014000280085030301d400b03c0710740425500c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 125894424 1250 125893174 125893189
    0x15010905090f241e010905060418140f0d02100504060204030c090b0405010911090d020621010e0c0c07030f050c06030f09010623011b170c01060504180605040201090302 74
    0x10340080d940094480003c0d1800840f65001a0101c00100042e48000040001120310300b411110300801c00952030342ea040100d006000d0380e00701c0e208200303944d0743d051003008000040e0004c490840811200000d40c103c4829940f00da403800c00c03102503071001c00e820580c0305035900100e5116220b11000750800303581f40d0b204c0812002c01d40001c50200e4032a80c07508800d050520815004141d9a4414030640e500008085524400c1002c0c60703010f4000b0034815400d544403a402c44c0c0c070041392201102803180c001e9403541c1140c4003e01500f00c080508038041020295600c0076201540d0201001d483c4070352441e5505004104152012500c5020b181258501c2743c0d00d00000e5445a110404440900d10740b5074102030841e141d0703810240d0250301c2c000403049200e1003140a4079000742c0130300340802e401000c00380b481d403a500e00810041c150b00e40042c4039200d5510000103004445c0101009010541c0c80754104002e84003c001c5940200c000f41c0070b07000202e1401c1d00402e800c01c1c018100b10100d26101d0b00401c0d82c4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 125895674 1250 125894424 125894443
    0x71e051c080403080a1202070218100305030f0a030e06040302070605280801080c09010e070309060b04020c150708040f0f030e10020304060f0203030105130c050f0d0b0f0315010905090f 81
    0x241c4c1c401059200741c03107030800e076054181c1507101000c5140c242d55900043c10110700e1740040c80806031500009890342c0202a00601854001040b03d0320744070819000c3d0890b601c00206680041d041c4401c2804048000a501d401154075402410280381428402c5802e504030b21104a208026280064a08000081810b00900103a40c68500d198108a4074604d4610743d902aa4065031055004100c0e5a41c01d01e8540c1d04207486150100d85030351141000b1001d05100100e196006e44006102601e1030030014482400a0003541c0421841d900c0c0c51080d60b0b0320004642c060030350240300703001c08005040c003180c0c102c000c1d00c0ba09000e4100401c4001250032a049006084050f900003d07043c405148c01c10501030b1903402c0c920003103140d981003d0114404010600c030760351b05203442c0c1e089230800c54000c44c00e84148003200c440d07172a00c40d02101a1007024040401e031241c042e052090b1400c149040100304903c4e450364880c00d4500316440c0c444104001c110091594505001d003110b102d11005003400031048 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 125896924 1250 125895674 125895683
    0xa050309100906090209070206190c09030c08010b12070608151c03090305011a01020a080a03090828030e06060108060102071a0304050606060a0c060506030a14030a02071e051c080403 80
    0xc4ca80894410711044031801f900380400d552000c010000711b1704d000c40800800402244010800f00d841150a842035070f201e420042003140c4118010503011f8055100020310201211484215404400d01c241c60304907d001c2c1000154050000501d00b0609070440180c0c40030150042e0354140c0701489070010032580c09000c0700000c003d0801042405824003030102d441a00540c104d481e00307450300002c1d40c0e44c8403a0200501c802d0011903000780a0740130b54410b414141d0400005a0b0f114003104100c05404098a9400c030040110031010304c52900c00d114004000c00c5900003010107881e4000107581c4041c0003030583d41184628080482d81d941c40c03401180c00f03080018200c507181e04081c90324904000d0020700980c02082c080c403260142c50350040024824a0704140000f40701e8aa51010a040c43c101040150240d50001003104d4030550000007041035035015800d80f08c02944480310b5100003003580b4602d0078010b2000b003060045e03140110751041407540300c0e00300c050340408540d60080c058206600c1600c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 125898174 1250 125896924 125896931
    0x206091008040b09061005090415050702031b0c01090303032c0a060e0105040203070b072f03060906041115120f06180105010c0330020309070f0b0a050309100906 71
    0x208010400750f205403ca1140300107088076103051070010791a81480d204162158600a010a060129441c0b66510b140c1d9000030a0000c3d04d441d40e4003965a40c48181908010700d184005440d96203008110b05200183c16554040090b14649045025101803020103091140d00d001d50341c910040290450300403074043c030181c040b4032860309041c022075404000c01c54403a41440e08020050b84d0110b090015a03c1043c61113858003410300702a52541d0716220001d03403e90008010f9080c01d503081c0e010501e1806c045044411580d02c20542c0d039220708095800a00c138141c000f89042c00c1d4503102104a549640141072241444032081108070385007810355076003094042d5201486903c1c10052040014085424400d0580d5450600001c6c00036104000c064204644001176030140c00322000c00000e065502c1c40901c400c0c0050101100083d48181d564801501c40e66000298440790400ca0740e00b16500841e2150520040030390946040c1c0c0001c00300ca1550040c105102032001c1d03184a41d0100c10300409000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 125899280 1106 125898174 125898181
    0x40c03230f0a06061401091a1c050907060206040b0a02070c0302090f01090c0201060506190302070209090303060f01050f09040e0f010e1018020a060c0206091008 71
    0x2000d10700a0201035440d81c08000340100c0c0c0e4501079001080490350f56000b0b000a20b1421160902003005075900300f00c0c000008001088001d6200880c0380350161005c03a66404400002d000e64044e071342c1e9030a01841000c10080b41c0c0243c4150b0005040717608050f143d203500b4120043c070740308019030001498000c02482c05604402540e02030416100c500b00001000f000000c24001c1d00002ea14252001c60322030b205001341801c07600c0241041f8580003000e040405250140b0888500b4146c00300503070b10050316148170707080c42014a00040c5d40c40b07080c503c00f0000452046d01c3c13414100700040c41103c0c40513104104950a2003001c9800181072010151540d080c040e44e00c4400550703502c6c100303400390729100221b00300b102d00e180188108203d00d101ca06500c1c10112000780039402508502c400d1003040c0c042c52101c81000d000810050030182c02d2000506217885080c0c82d04e00044039001803 = true := by decide +kernel

theorem cover : BRFrame.Cov 125719424 125899280 := by
  have h0 := BRFrame.cov_init 125719424
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 125719424 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 125719424 ≤ n) (h2 : n < 125899280) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
