-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3296
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:14:16.653053+00:00
-- url     : https://prove2.me/submissions/c1b50e94-322a-4b35-b77a-ee1d898b4e02

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 592625899 ≤ n < 592805755 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 592627149 1250 592625899 592625923
    0x30203060a020405180c041805061f09030b090c1518011115040c17030a0f0e0f061303060e0d02190807080a050d090b0f0f10150c060c02 60
    0x421000c1241c00281c1e0003207500351000500b2030240e10b40e65802102580c400100a1550110f05101c0880e080d08601f10034401da0200d00b00216881c140b54081201003100c0c040e400031141840d11403002e0007500700c0541070031240c015200c107085a88008116042c15400940541d110382c0150041c02841400805000c0380f4a500741c010426006460054828500c1045040b003954000800c0c295041c200c106e945034447e10550b0b11801e280e40d06c16a001c0284840c0704070803400c1e0000301d03000c1d60075588040d4901c6041000d180c1010b10348032040205211409142c2440d004010000d2100031654402e05450700840d4000404c2110000d82042141c4800140e0075038001401303024141d80d00091602c1030002441d4000c810070340380101680e100301c0254410003144c01803000600461204614600c252034105000301000c3e200c500d8049141c00f02010b0007800b030355014081005200c45c60241c0045035090300e000e05141071105880210644075550b100b100103003500e05092030445d4042d808190051410 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 592628399 1250 592627149 592627153
    0x302010b0409030306030b060d030207170c03010603051e070e010501030903050c150a060501050309060c0309070807080d030c1e0311090a08031801210b0d0605090610090903021906060b070b01030203 87
    0x9182c2030204049c0990020016006a0022800707010506d00c070a0319084d0380501c481221a0740d005078002c60302b03540c0c45500507181c0d5000700c0341810480f948003100b00300c107005000107010450705110001e03001050601840f810903545003078600c101070084080300c4401d80741404586075007481e80071034000c1d0711045682e0300d08582004800a010b5000e002070300e01500c03110000d0b0025556415034000320303070001000c1c003141d80f05804000074514800c0c85080d0141407454082e00960b00fa40e0320140540b019140101d0410070514082da0b4080e021095050120b40b1310700e0b0200c1c1300d500400884c10340b40101c000d40c56010140c488009841e8a00100510b10760b9010f0107414003420080c401034030300980098000c13400c14924556507448103e6540900170009000b07007089080340064891904440081310043e5042e44900240b0601020085040300203003000d80d0180a0341e10207640084d05e6407090040da51021914844440402c00f607600040094410104040d4484c1d02c0b07030900001c5c846081c40164024 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 592629649 1250 592628399 592628401
    0x3806040f0c0801030809030313080a0515060d030c06020f0a0203040e06030109150513140c0a270b0409021f0f05120117100c030b15250302010b0409030306030b 70
    0x1408031800380c49106070158407618403507840c54540c0807466009501903941400100448036121306d1109070301c03018050303940c02000890354502e03200c0c2c43c010304802c000706c3c4c1c00002070401800e81d030758117580c000d105c0d4540f4145007402c2c0185080340c0603004840f1483c44107a004640103401e1903001001e44100c4a085160b81c1c0f15454001c20f0508850310f540015201600382c511507a211042d603002190450302d0b94489001c03018158640c0c0034995844144400342e900b12b502c0c8891207191102c09180900824003510b49081d40c1201050f007044440160a081c00c2d444480c1c0b050f9030398507070b4458400c2d260050907440e940c0302c0307005901c0c1c0d411034011840e0f40410b00700701120210b68828019070f80112600c00007414607900b4151450b00202d01300070303105041e12074042c1c50380c11078205001e1a541c0080c03507107010448800c200c0c00c01801410210742460100802e120380740d1141c0022203030840e50303c1da44000924222a0f8101280074021142d82544c1280c10000041c0402d0350641c4090100d0303000304c0112200e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 592630899 1250 592629649 592629671
    0xa031806052e06050316050f070b150a051c020a050a0b190207050a0608090109150506040617060a18060e0c120c030c060a0903210f1704380604 63
    0x1011040e000701d0000413820b10010301c500307249440708224510142000c9040c202c80b2a00408240d02604048076103080035000d03c503108411400d00c50682d40125840401c0b0350420010400340c01000c80d0140e1003040410100040d0744500102070023418000d080503025648900c048201c6501c00050b42600702804038000020a101017040c00903100001c2031042044d1422074102c440402c06082c81150b03560340c030b2450340000c0d421203640105040c032400100740c0b854108208000c0300c22070384c00000b52018004140d10040804540d5035880a541e0740c0028103480c220414110382d484803c0c00401c82842e243c99025190f200154001001508035036501461003043d8003075032600018076035950036070f0020300011703040d203066000f90440c00c03541d00c1e010030540c2c3c0d0380e181c0182d9480100340140e0048801c650f03d8003401e9020024a5100c1440d0400302070340880810b0380102c07018000c1c800b404060281201e500c0c0d000700d80b0b50390783c0391300840d042d80c4c030325100c182c11210000d100c01e440e11803045103004141c00e1 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 592632149 1250 592630899 592630981
    0x10e04030203040621020c0a020405011211060f0f0a0203090a450c0e0301150803070303090f020d03030b130510060c08130b04090e010902060a03180605 67
    0x8899941540910b0030146486800e03280b200ba5404411103a07500d5130700101d41850284050b200d2000540b000702481d002c0c60060100302c480607002034001d481d030301d0480b0021500e18001e4401641041c0d955503560039844017204114040c0c0710320003080c1c410001c0d0b001c5007150b00102400440344100c9098010320b54414a5807411840401440742645545203001c0541c0c40380b80e941c2000302464043c4101641100519600f00c6e010102c290000c62140e01c448001801c00b44a492903800b50403411400c0c0c607082422a980d01e005004000302059218540c590030402009049075083c1d1740a060400480034900e0060054a45100f00c5402181103a01c0301403551074901540c0d001d41001c50111603c0d5003002002c4034039900950050380c02050402244100f84200e0040500600c5030b00140c549a07818402500107484010043c9001a070500b0107080145e6501c0c2c013101c9031301800d42400104405ea00010a0b200000c03d140508914a01420005211006022041c687d40c000b5007200701600620010b45d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 592633399 1250 592632149 592632151
    0xf030103240612260d091502030403050726040e010611010b06090f1c0506060a080102180409030c020a14181e130c09091202150606090a08061e010e 65
    0x55501c0c02215a40e20200f05030f00310403a1845111300fa000350501c0c10801c030011561145030100074407562044501c06001c454000401c1c00c0b80709500c19803560410b51801003031406080c0c005411041c0803210a54107080d005100200c048600300c03440d03101c0750341e200c950350285024482c10001c107440c40c0c4480c2c030303041c010310540704a284010004ca06100103c01448048014911541d03005880801c41400004ae66030400c10041d110703c0c0203002078a4045e06011880c0301e6039020402e20703070040c00503001d1194400c90080c021030040c0d0700010303921124102101d580c801104040d422062180380030401c0040032071118009c2c9415211022111702c0c404580c1c5044c6011240b08000c0e054040204443e0410401165040f05600d1040c410662007901e03040c0c0040415488502266903840c5c10b0800c20404480c00c42c090440d50019044080c0c407044021801c02d0028807140c0724035800280000d4503a20030300401d000d000d00504031182d511f0102c0424840c130711012003410403810100f00000b04070024988031 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 592634649 1250 592633399 592633409
    0x81f06030c260a0c0201090b0f090d0809060109020a1b05010501030c05010504140405070507080c0609160e060d15020c060a11040f0306050a0b0904080304140c060a11030f0301032406 80
    0x11007526501c05524000904e6070380d11020440d5220022000812192211036020300d1503090800c800d401d240c150785160000030030444092041900410a04c0c3c00c0c0401c9a6045078074011002da9115080c450495002603070050418400100c0d034034001c1401415407100d03040c0c91041d4140c08150343c440c0010349540c0254410303207071101002c400b441d41c24100354001e00c1d04405281400350408030696190308460300b0a44c0d0009140d40100e040200564003044220000841d02c43c0c9000000d0912000c1110541c2c000c12b03060045107548400d000b081503680120710700d00613814045454551582c032458a402c0c0542b54400500d0902900c2e60008841ca0b048030119441803c14040d6940f45540340c0014140061030000c0c00d42d95040ca802e41c0761155226a44210b105400fa644d40b40340078500304204501d00c0380042d0325580400075550b01926910b04441c1ca0610b6800d04808282000050520b1445103400a41c074400011000004108a24a60144861700d030f92286070035581c5903c0b00b504a951a00c55 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 592635899 1250 592634649 592634717
    0x1c0308070e09090d0c111f0206010b071e14010f021201080d02060609130b040c1806030c1e03150204030c06030c09030204020c0316050c041503050d081f06030c 70
    0x204e1400140078400801110384a0a0010a9070781207000042459158121030390044174400c029200311613040c40344901414100d00d20382c0c01e015654130307041e80407500c45c5000003c4123580c1c40542e06002d422240c08150882041c0280101001c1d52180303000794015122146200340c5800012868510100341c0032803400050f80103040704c0c0d64174170401200a2020700810750b81c643e800e5024000c125190203040c411401010780340627941c9440c0305100c43c2c2100a083d040c1c400c0c9081c07810302c009014261440100c0701240521581440751065845c941e50050b0f00081000003070641d842155221074010b00101d0b07002d440c0700405940c0d5a42c1c103800340d4070340b5403800b40044c000000074001890f2550107041801146022a81003e10350032070900c6410807103100b956a0b510208600031249440d01070784000725a0502d498020310301d1a524141c0c0c40201d8100341080c000381c2000100300e5400004561045003044101080c215501d850140c02010b59003024400100d03c2d501c0300e40882060b088000c0c245181c0c0c04 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 592637149 1250 592635899 592635913
    0x30b01050705210d1103011d0402030a023c0109080a08040b0d020405042f070b011802090910051005091e0a0909030e0307050a231c0308070e0909 64
    0x420781114083d100d0300c150a1201c140040c1c010030301c3d90302c00d8110002030840c0d000d41c0e80d414040c50a5a1220032020036065001844c1040016240815504411031b03040c0e03400303a041d400c031000b0002d51841c64000008515000031501180f00c4c000841c08107980b00a0700c64208a03616031140790b0300c600710658050f000c01030070042004102d4170351004001007801e4a030f00508103500c98001400b40c0d200b9035140c4d550b50f00724030b807290b40f03020342c0000004a5402c0503164501d1b0206a42d20300510305014464a0071044100c0c41000242c01c413501120302e0614000d1811010f490138012103c8882e0b151b009071406000d03884220740c60705004e98115500840024806070381c52400000d5840e101010701a074540000039421b0000c2c18600721302580240f0b52180e06c2e0340348240280401e06242c21001d0b40998850000004200200140744807085032146044c09041c2a0080c08008201001c644800d5000b07802c1d59450aa0305041d80328140600542e407903901e40e000a4000d10800845d01d005032041681e03500601 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 592638399 1250 592637149 592637173
    0x50604020f062a121809070318081b0d0809060627361b01090501052b0b100c050319110106090b031207080d1d01050405030a030b01050705 61
    0x40641c1408600315022030703002542624550340321303800c000390402071340007285c442d513100b031500026441d4082d03054501044100d6440040001038000141c0140c0106d0002451014150080402c0c1030103030725102c00c03160709500d207541c0140002800c507041c04181c020240400c80c030745040103041c0d00400c490301005014803110544078888a5021b01305448021080034a02d000c1d400411080619004410000c0c00d0070070070310a81800d0001c0f1410900702c07009417401280060780c0207040102034580a203419070b201d503040f400b02000304900d02031001020b61a0182c0c6405840e85801143d10f0400c01c1d9851080842e01000c1034074200002c4d240284a0b070010301180180e01d0304406603c4d506122807500c1c4440380c01c00154242114001c4c2c00003103640340c80346503140050504003c0d07240701d5004240b50518200060b140c0109a0043c000c030424010b4860a805100302c4140303a42e40e41d03800c20b0740006c00950a040c6403060342c1e58031000d841c0703010a0901440141940c0240c05403688103030000b015041e40c038501 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 592639649 1250 592638399 592638457
    0xd03140a020a020a021002010c0906021f0504020a09020f0a090e130b0a0b0423090d0c15110d0e16050f0f010c050a030503040b06150a0e011209050604020f06 69
    0x2501c00c07070046105100c4c0301409130792a61840c8070940400d80000403110141080200010642e402010665003d8010302d011117860044c031030048807940000141d42c1d20b036840040c1041429602c080b0300c1c2030001c90b59815540140d40108210090380c3c40d0030120769036034134a104441908903105440040b1011490000c09c0b4205600c5a01241c40000001c00c0c005100004040390f038008902030714000f400700d410382d41504240e01160402844001480e68651080c4018204c40e039960300101407010b0114001c01040013138100c000041c0294802c0c0791121400500b0f00f0040c1601c0c40402103612914a103003182d1440003400c40241ea0016102c420428a05c5062044c8040e401d21424101310702c8010030f8010030414807100d01058460307030b1001d41e2400c040c04c16503020303003010f06180d22130a200c404940d54108011f007103806885c8a810b10155032003142c80140c40b00c0d2080340354140c0560510b600d8004202002c15141c3c4100d00c04c4030b241006210000520486002e02810401c165200b46076a000840f69 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 592640899 1250 592639649 592639657
    0xe040b041401060f15050c0607210509060403020d030216021504080106150f0327052b02060109060b03010302150f0a0503010306200a18080d0c02030d03140a02 70
    0xd8081c40e5040703410118520b0071a07500e5405841c1040c840c26040c0915400c210398222001d4451034520704004080c00002e844102c0a40280140081850000c04841c000c1100c8050802c004e2402c001619003207100d25100c8804884c11001030060f0410901c3e450f00070b200f5502602c1c03490098003560000755090144860360300d1080e101d810010301c00050001c00902520003e040d1010b10303544010f150140240c001900c1120800906050106002c1c9a0b080000c0701500c81407418045c8180c884203040250800010b00b910f500700f40c0002c160000140c51000d010741402c1d07415030072990300e03a99950003c4102c940501a88010f10340400040025140c80340784405854501140b45161580c0b03814a1001a4000c60240010400210040080c0710007881a55010303003510b0601595420105941041440352180901c02c3c40894040700324001e4100354690003a001002c222010310502900c05040e58040343c104030700c070b44940cae6226207415129004140d044480709030004c075152030740c055440103500 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 592642149 1250 592640899 592640903
    0x6070f02060121050601120209150f150717040510021f0b011407030329030607050318030d06030b130c15030f05041226040f140a15150e040b04 63
    0x21880301041041c0056402000201f10b05c0344c3c0361aa510510010850040403056094120b00680a56455021f1400b03040d6008030303100000d02c0001480c4000314005c060b80500311001180c0030304c030703200e5251004005a81049850102082055604030f95031540c200071b101190454141e240a510850303040700e0000c040505095a240c949200c0c10285074000c1c120960000b03803100040c4480d070403e8030b1440403541e00c0c0f1810a5035141d840000c640e17074001c0986028104040003001401d1070b041518440108101705050741d94a040c0404494042e044c07501080e110304a088010540320101c506211060f154413000380e040051070503903001e00043c0840201d200303150b10794802805451192190610a911422801c07607c0d001c403400090140c9a404c0c004028424240c3d0025541c0e41c251049591099108040c420341181600d4542001708111201403810300c10000b05008010948802d4a90025003030410401c5030b030007240d40410040d042c8944c0c105213481101017800308048060f8681d01034 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 592643399 1250 592642149 592642199
    0x608130f0b07051209030a0905040e210f0c100614010909051e040f11040b01091427010e130209010603020c0a0c0605041e05150304140a120206070f020601 68
    0x113080c10070743c10042404544440c025000021181c0c1000d130054480c9014190654040200800c0005400c0e0f640021420b02960318441008904801c006442118074ad0314507600d101e43c5a50400801c1540d45401c41802c1034050b081c10f81c045403001e9404004414000143e44001c50545844d001800512001d03002d02e0b0f58081ca80441d0458100201d180340c03b9512a5186c403481c10700c9424482d1204140d01c0c43d192141d03041406070b004a03a4001c007548141c0b10040c52800034040c10384c00051411880c0b002c0311080003030b107000d482414401c1d192028120780c80050508059511102c90074821001603c00039404020711006103d5188203a011f850b903000d10303e0840d644601c403621614001c2c501580950001940020148942c802034001004100c1280f545048824141000900400201c6c080030044050110001e014849054600f442e9500c000c426142800740ca03003480c0c200241c500e03800078054819500071580c500e100c3c14020004465650241c00c80380d0810111050203c0c450002da0504c0c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 592644649 1250 592643399 592643407
    0x3010b0a0c060617011b08011a040e010b1b03030c16050a0b10090b0d0f0210020312010b070b010b09010c1e02030f030a031d060406050726010608130f0b0705 69
    0x142c841d21039500a08003d4042c98452440a00b43c1400d54401050154015a091920100d400c1c3c10210940c192040b20101c442d507000c03005103600032030107541c2c045401048040000920904800c005200c0c102a450f020f10304070222002440c2d0300c2c40240ca4550003514204212040705050079284014a407254065802c2c00d0721585800329540e070180d52200e004148400f00700900402c500c10106051000d4036034407013400c410f072100c819150381e100d0041d00410703c1600300c0d40214424170031201550400030b030840b0503507140c100c0c1240c25081884211071042c0c2c0c10001080c604410010b540d5402e205969840b401d075095910f041003094404201c2c106100d05502e0f00006a03410b120302d02e4003440e19070044d07854900c4841c0007000e48040201400c02c91002e00840300859002141d100d0b400b45d0429004940c54848883c122030070010382040010880071003440041100d0040e4045040303641d41e030b175000201c4e15031141c10b45814440d00c0000340b90030700c0d40e42c0a8002030136110840d54002c010f41803040c10 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 592645899 1250 592644649 592644653
    0x60415080f0c19030302060f0907120303020408060a18320c09060a0b041403030409020d0e070915050103110c0609070824130c0801020409060f150503010b0a0c 70
    0xd0300d0710a00c0484055044002e4400c2d6504100982034980703807662006a01c02ca00d141c4000e51901c3d4064207046482900c1c2000075200d20b010050365008101140788050030f20030034100100250058003c2d4a6a4042e801c0401d88505143c0500c031104c0b1010303441d006040c010b036030365000c1c1140410b640c0000c42d203189107001003445400f840c038800c2d0070750a030140c02158420401c104000c03d0040c00c0c3c610400e03a15600784006c84a100a8030155940c1c0c91801042c4040000000d25500a940c4024000e80c000225401942101e0304503200d0305855400300c40e19541c551034414156003900c82c03411045403d070030341002258031a41240c0d021200c845440341c60090240003076400d00070100c40e003c1035a4072904007044003010422401d400c21350301542c3d0a192800d0500445980030012788003c1c01c2c1540c0210103001d00031940040e600078109030008554a580d2900781d40c0c058807203403003800c2810403c440c000804c41d010001c03003040d0580396070351140386a090040c5c400c240d03041038101c042086007401e10200 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 592647149 1250 592645899 592645903
    0x280b09010c051b2a040b1203070b10030507091d28020f1f09120206030112111e030106141c26030a0c0f020a0209070507050303190b03070b0306041508 66
    0x40202880007641e690080030105005c2a550003554003405814810000c0c8003429010083d41e40046c0d1116415080340c4690040000d10007040c1c00c050302c1c600413084006050001c41e40000310b410101c0e0f036900540d816101c8043e07100c0f821a02200a00f8900c0ba11000c0d2815034150102a00c2e840108444c104900c410045107064101c0144210241401d14035240b605402500703620003006c001140084401c141da010618501040c0f2030f01515030b81051105081000f14a9400321828024005842800c003c1c84403d20b141510170106005e5403074100042400481207070040605800a4003004114400c02040101d0070030100e0309a465295604044000003444444100e10b0300608908075105d06140c8880b80c2103c50200c81041403024204500e56004e40204609818a404890130f168668030254280d40318401c64030002c01c240400001c0001100f0340c1c0e03102d6080b420a03808101b200030703018418145c0d206d0703a078010000c2d520014000140b1502d09500f06440b2032840d03d4003a0718684d603c880b094 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 592648399 1250 592647149 592647193
    0x9070e180c0408060108010e120a140310030501020c0c0a0609050303041505070f031206051210050a0e0723091b0307020c06030109050a140105010e0d05280b09010c051b 74
    0x1000d48d44031030306e07140f0750202003068820400f4200700c010701c0c1c0700d01c10b24058896000c0800c4d4010b28400032001902510000d600500196041802503543d8005501e02c540c648000340c0f07409208045580000c1080d41c0308808400a48030050011481c03c4d041ca0345c2e2001c40441001640200441040040c00081e6564084850184680c0310a03c2c107088220b60842612500d0f00320310b018008460080c0e80c00140010700b101450199500042c06880c0e1410003005420b12410300600e0b0f2113030b0540011030031000307130300e140b480b00e910100b5070045031100003044140c01084c3c403031204031517100c0310002c0b00340c142c04015500005c45004940002c2c0c00d0001090240d0004d91028110035540d0013000641091030041000010b10119030050301e42c10040042c000c10222203030540140e11421329101080002c2181030810504d403024410841850300c040000038181045c201c5205c0500710100b40010014041d82984c05403503200d00c0d0030115440c0e00200d4910528540e02c032680b242d481510848680311100d4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 592649649 1250 592648399 592648409
    0x60108061932220c090b13020c070e010b1204021516110102012406030207060204120c06140c0a02121501080304050109050a1d04080c010501120209070e180c04080601 73
    0x2449140f0f0034901156403c1034104032a603103120186920400204503401c0842510001600020540c00490100c1d442c8580c0b401e101000d82d100103400303041c00f04000740a03411a040561145406d03030704e4046201950080020740c050503099903003c1001807a00002d4501007086001c01d150030154513200208600c008500d003501c4103600d0701c000c00c12a50307080c01007001c014032880c40e0002d10304103c041c4140034230440c46410200b550200d0300360b0401201da0100c2e0018000e42807450725018190030300c10a2040e01c3d00c94000401c15540c0502c0c0403220407803d954104e0740c1c4074050100303034110750288003204241f07980c1003910b0700441c00190341e5035050345071041c081e1901d24001c540b02d90800c0b0014104414580056100d40c0c0c413070f03104220303e54140c1001c00290301e00790042c2100d52a20303d00004c590140483c05c805035400d01002081841d00401d00800c054001c940b2050707151905403064580c41c030340c00710140e0040c058400c020428101050965009401c0c65842442c0070365416415003031010a8000c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 592650899 1250 592649649 592649741
    0x2718080a0f0f1b0605090c060d050703063311030c070302030d02010e0601150c0506071706220c021c0e0909070b04120302100f0b030601080619 63
    0x40705038401d50042030055115041d0409000d06844540a14110001110018040d0b03450b0800030711a079074140b10078200707080060202901c406012040c5005080102c0701c0c100028238207200012030740545185941d03a4115207441580042903140d031070500c011642940e8003070002c40b40001001c000d0400091070344071020130207081721909510415061081d90001c1400b1a8144502e00c465944080781c82030440e40040b4940182140010042d5000d0b041070002801070300a080030003e5158010360419421480301c5249607071607a40c070003000500d0103c1c0d11a078080e02c8642d01e13603542030421f80d44401c000740e040b401100c80428468148200f08461680c20000050b00d0700c18005a034201089907076000309070b11003e850183c1c20005035140c00c0c0200e00c6403840d10160b0011500905000380300300184100307109024049000c0029030400a0704072107010b107000740309100001648002c08601345018102000c8031441d050046550000500110002c2c56407105444070f8480311800b140302d00b801d44105081b0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 592652149 1250 592650899 592650917
    0x40c0302060309031c020a2f0a0302060a0f0c0c0201050a20010914010b1c0c080d030507020c0301110306010c0c050402040e0717010806040305070501150f050a2718080a 74
    0x503107501c00c041782e40e403c50fa181e4010300100e00c01039004810101c64254800102c1c2034045081c0000e91032803c1e100d44611140641680b1900741035010a1a42c032508440c0410702409030718040342d80450b0a0102c0740070000307c3e01000000190b21800040c013546a0b1841c1440108403140300030704c25640c01900c0301e01c0e145c0d510090300b030400c611086c0e4203007003c9103007008220094401010828644518180b072128040072a600010003254a142c1f402a000940c00c4400341310440308c014000f0441039030540054402d0485ca5400ea150500514142080c4a8062421500d0758801941c15200000c801c0390b0385c603203115000c03506450306d2010340010b00c0006462015414a2600901900d40e03052142138605851360042c4913201d4002184e039006030349850f1140d52427515041c11801030a00480c2012904404007000900b444250001c5003030340d8088460740c20096a9004050621b40082c0380e0440c1d850344640c003a10304440d10b87c0001a8031440c2c280d484000c0310284e40b14641c95102c8480301001ca22428 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 592653399 1250 592652149 592652167
    0xa03021c0f1505090603060103080f120103030905010905030d09090203100801110a09080f120a0e0d0f021002010b0306060609030c22050c0a0804020f0a0f0608190605010f030203040c030206030903 86
    0xb030030100400b01074a00c200e43e8100200482c0e00c40d40c0501020b03008100008841c1c05010341c0314102e492900400f213101d0300c2540c59140003091382941d84505400101000008a42c0b85400b04001c1003510031074070780f01101e901e0a40c40e0400303500024030030300c0040403400300040d04050070301130f500c0290313070200704603980d00d1070100040c3c07020010740c02101650780405038102c40280300050032400f400c468020180c83c0c0c03080c041e0407a90f50000003607250308040400c1311402000b500130141a04984202d52205010f949490224201d89280118503810b80c4840041411400c100d001008200405029144420040004145103030312500170740b102800b440000e41c00340c00b024440d69410081c2444000d142c02610300000b0001040940701170f108400000c4035501c0381d503074451810010006101140200350740c942003d803e00c60304840c603d0010322601100800308201e0310412050314016120200f907001c0d03080048009401c018412501013400003004005070761100059885400d03050b00450f602d110328 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 592654649 1250 592653399 592653431
    0x160309030e2715091f03121d12071206060b030711010609021e161e0b010e010b0412320c0f090105040903050708070b04030f05030108030a03021c0f 65
    0x1d00b07030030100043c2a408110ba0b0349400803a43c01408038105100313056440400380980f0707441640020003402510190f2050030b5000811441c0003840328012000c5040c181703003030203420280c0b07848800e111707005a803044c4030034404e8260404440d40174500010b151900e80c0283d220691054403508085844280c0e4a1001d280034024200030340701094040d401c0c00300e8248040e440404d41404600240d0740486d0407030b14200e400e0b442c41e1509400c07003507950320b0314031098001048500d00c850584030130303000c03a0020031035600c2c0c12190ba04848120301c9892902d86041d15825098140c0803044403030402c080b05030026078003603c40180c5000140d50f070a00071003c084404030f02e0300400410840c0282410a2046982e688230300d00c0c1811503105888c00304412950b072074102c41d9031240013002044a4000704142043c44070701c507500c40c0f0903446a00d901411020381841941e02c1c1c082442000c1c40365004124030021184681c015249044441007010454540000004180e4168040510703e4682d0780102c000f00b2560 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 592655899 1250 592654649 592654651
    0x32e030b16090b03010501050d090b040b0105041404080403110d0c0f090f05151c06090809030f030430140a05010606030c1403100b0c0a06050a0203160309030e27 71
    0x2103402c0291041d0300e41034041006001c148500ba0501c00302145600c3d486400d500120700d60760f07101303003c210b81c1c1c0380600e0064039109003800b0303040c0030350f14055410f1a40b0380901c5500340950707040154603041c2440e43c0d640d15070b0301c451030210941103424159110000382c1130515403400380000300c101c010006c1c28000b501d0101e60210798400d200c5400e00e0180712000c2c0301d1119000081806841c011100c410310340590b201c0000c4000c1c0203200b1894000a90705101101010b402d030301c141113042c0c4961152442c501c0382c0e40e029031f0088500600c86505d00340c1d00d01442c585441050391125585c00c1e81a1080e40b58a40780d81ca0404205007079410040c51003007080020311844001d03080394102082407171000d8100520030742203200d900300080d42c0040400c41d010084280c050040005200207991405401122921001c5003407044440034100350108498078054000e17680f240c01c1e9003100c14032031034054100b18090540823405405100d510764a815142d220786080d5000e12a03000b002c40c034038190392104000c1c1c2c804 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 592657149 1250 592655899 592655941
    0x717040e010603180f0312110409150b040f4208061e0909101d0f010603110402030411090a0b09090708033a0b1e06032e030b 55
    0x4451452180081c81c619040076105d6011b01c1c00450f40e118440600300105800c00441c02d0200c8041000110b1007516040304901d000414054603c2d41d0341d03a519000140280d000300784960b00040c0d02800309c1d012100c03400d0000f0498800040425522040d4000da0000c54030342006a103405104114805410100482d0041c01c2030750403c0500240c411502c5030000041c0c0314910641e407000c02b2401580c0200318140a500c1c00102c00c02031000400d010071944d07248070a040c1e07068041c41c0d100c940713039102c1841020211b0342c000071048000c00c021401c02c0000d6200507c100d4100002101c542500e031281081b20b0f100d0811118001590401e000c100200d4110050001c4520b03448910b0030304c10031101106607800340a0107281d0a6003000030030907003104840100006940200a401e9000e0518401e400c44031326108162103100b1010360203120700c02c04042030130095400c520204041641c0a0348112041412003a8104402c90520f100312903440c28055544265144e02190061102002c07141159580200c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 592658399 1250 592657149 592657181
    0x402010314150d020f0411030f0c0a02063c271b0a0b2709101715010902120f0723120901060602190b0c0717040e010603 53
    0xc540400d2400b0b5070500b4052041c02042004454821500c1e00c908a14100c98002c0041c04031080040f494505500b0417174030003419030145404a03500016200881c0c050240d00c1d1701500d001c1e40c1e00700403000c05454064100d9010610180304454681c0c4240a0f4140026118902441400d10b441605041d0380914000c0700c3e24161844a581c10344400542c1c0d800100d200740d061300b1500c24680c001035003c5c426070b00840f41060005030758801041107495504e50054003034240440e503022401070180117202120391005020800008ac8a003058551743d409038410482c00311241c1c00085186d240c141f03402030340001c00c0a600410740060a442c6481b40350761111040300203250302e1900b6071005100c0b640c0038402180412605000c1d0324032940706400c0780e01500240c1030580d45401d0040b00640208205d100341740042c09810500c07440310714000c1302c1c2070a090300070044840d1525000280c403900e5010324012100fa504480315230781441106c5010344010000784203040c2c4070303603d80f030f001a065406000b140380c118 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 592659649 1250 592658399 592658401
    0x20d36090c050f070215070b010602010203040528030305040501060f030302010902130c05120a02040504110c06070906090e15030712050606040216060f0b12011d0f0c10020c0402030f0402010314 85
    0x41641a00f9100c4c5260119046103901c80f206040c02c00c1c80c8111030014086651190020405c650150005c6015034407500444005c02c14042030204a02a040103031045a40500102004688241c1002e900140034a0000070266070750704040c0c0070345089500890240c0d4582101005500c0e000c4400540c0001c801014450820102001007030b511640681d5074603180f908000c1406c46c0a02c3c0d040c4c5c7d0140c1070150007001840204070444965400000d100f505601c20314000400e802c1c491180c070402c4480544400c0081d904044000c8414a0024000c2d0840c0c540400b50301da45540800000c03005002c000c1e059904840d650074420b00307000d80100018011401008910740d40f28407501d0f03004500d43c101c4800202d04419840f040c016003480030f8101e0f8841000014100d035080194414542e480103000f081ca985000b000c845901c9070f40c40341c2c5064840d0000d195801150030561101103d042561040c2e40c00404c0c100c00007802c0343c20a450564501110408100c11960144100d5000c0c0c040d008160100f = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 592660899 1250 592659649 592659667
    0x80a02041d071703070b0f0411150a0e0f031c020d05041809081201170708011e1503060603030f11031c180c08011406060406020d36090c05 61
    0x900d031054401c207040d0518801502203c1d80050065800481d0702c407001e00110705180d0320254401c1d0040d40c042e0b448000a511071f11091400c03022443d020b11a6041250508121380d4081e150310f201007509940200a01c980040d01d55418000c0078296218804030025040b01c01400030b141400c0c000c2c00c0c07001c0c008108424881d4000030440c10784480800c41c3c2c08500c0321154030b480c02d21409140c4c08684020001030020850702c9401c000c411524440300b084034070480e43c2e00b8070035081c0e445038800800b140c4020150340c214a10144c100c0064214030349040c0c050255241e9a00307040720444d074000d07400511007a04500c1c5140d880301702c046000201074010341c00e000c103101c4c0803202e15a103845403c0cec556540700d9108003d28420900d540485411102160344582d860701c0340c50103401c1240040304109900c10000345c840c0743c060709480540d1810340c01801c0400001809540c0404100b21000d03490a680c03031030f081c0010381ca5140901c1081401d03100c000f4640b412021a0030350301c50001c200d0a001040c022114 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 592662149 1250 592660899 592660903
    0x90605040e0c0c010c020a0506090c0d1b031709011407033f05090c01050c100b062503090b0c10020904060e10031401020f0301060c0615080a02041d 65
    0x20503514041d200003540e48507560319003468860070503503501c69402c207040d110089801044031038102d0b000c0c07829110302d40d94480816888000003d000c0d64008942403d80001c0703403039840314907082c6003184152540d1503100d4540490481070031401c2010079000003240324555038004c504455480503540510b0800c100703598081e12503c114907040005040f04400f24045240c0040003c006d2025403150f03803d5a84000041c40c0904000c8500715101d10802cac0000c7d04030751292081301c0d48442000041c2256006072114a40035115144041da0b100b001405200d0a80e100c074400c860200c0200c0c82021030144241c580640300030490f07440800d903c0360910000b1522040410042c213a140d14100040c1c0e9280000005002000e894100100b034103024000c00441c3c00b8111003000039a8003d20071407600400e11001d807400d038030034a14290305003501440104840c43c000c4e2101c181c458481c40c80860000c81e00825200c0701c100355400b5003140e0b4004000e000079424248241f1505a041824103403004010312101a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 592663399 1250 592662149 592662157
    0x1503061b0c0b0604140c040303080606040303020c010f05040b120402030d031a0f030a0b07080f25080c09040e011b0203130e040203070b04090207060e0c0a05041a041803030b01090605 80
    0x1d0705031542c050014045940b541d2040038140e442165610903414200340389981c513005804214040384540e4080750443c0340c05c0040e46d040f04d40c542c2c020302107582c0b000d0044450030b500e9003008007484814407000c903c0b5a5407038090609031040842c820b003280b6041c0101171412030313039465041c180740c500345120615050150a10044180542e5030b211050325070408a4070b400c81c0e1a1014046110007002d1291140c0c2c080d0180d8020900100900019203802d10019503034000e115101003a202c0084078020364500030700e0340d83c1d8400c0c44c10080c01d040c0784014020070255201c0d03020070425655074401b0714500843c0300c40340c142031441c01d100460809280384d60398421041d450198150541c0d581c0d000804540d010050ac00181c18100380050301c0303680d1028074201139000380c5811541a03080520f542e104a0002a480c100004020621180c091805060000030180710904d200d07040c10404e02254952214000c15680300a0b2010f6103c2e03568150030700404690b4500c1e40141040100c500411070300c0e501405035 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 592664649 1250 592663399 592663403
    0x180204060b12010e1012120207061403010e06120a060507020709020906041703300105010f0210050a150810110909010905270307032d05070f061503061b0c 68
    0x707411944c85600c084071701e100b410350101020326400341251040020328001070f22954072a400b1614441d448410548103981c2c0701401c010703145001d2004025942c11032016517000039000c0e0148012212500e4054203281d1202000d8030b03820380725010302034007583c1004000c3c010302c0203520031418441c450000644c244504c3c810780c21b600840001c80c18004905208480481032001401030f98101a585590340200844400c1003241c42c4547c00048e85501880e00200548403540c082c0ca40555803021803030041401510004036565190010b94010f08030302662005000f03a000244012440301c4900000c0d00e4101403440e00d46001809180d4240e140c09030094152000034501007801c2d5a030070b44410812016000200718a2005031030000c01400220007802e03002e000e1740d1040e0302d1500e8600315001801198450040c42120841c40a005d0b5110b40e020b003101c58030520101d00100015210350058941440c00444000185001001023048503c02d4954400100750028141000560080c042000d0b4440c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 592665899 1250 592664649 592664669
    0x10f030f0c050a08100c0e0f010c050708031b0618151b030408040329010b0d0f02030a06061707020c1e040f0e0708060603030a110f01180204060b1201 66
    0x51030080004071600d81000d0711014081d540e034555210f07004c56440d82e08049601a5510308903103420424810010b020700325901902c0c100c2c0402d04031004481c00705603058240d816000356a00031580410900007401c042d40284200e448803110845624103040c0c019080013245a050104681e0008002c0740d416442c5045424403d2507070758021000225480d00d0300503034182d03080001003004104141c400f0300240d03401088aa01c40460942210880d80f880d0030151201d415114010042c0e0000d40f0000c20300c114001c0b00200d4940480f01000e001e9810603650303a0b803115114403062101d158055400c6501142442c3c041c840350410030b1010b521031401e019900d000d4030700c85485502038004100c40c8540884064410020b524a144a6100420020548a41f0f078012100f0010303000703030000313007840c01450300802a40c40e02900391400d071079400c3d000e06411958012420003804420080c82034661402202803c3c07030040034648100411256140c000500041c0103014118845c030710040c850b4191880f00758 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 592667149 1250 592665899 592665923
    0xa0e0f060a090603080706140411120a0f0501090311150c0a2109110a03020102060a05070c0c1e0f06020a03030b011202071514040314070c1d040c0608010f03 69
    0x403503108212900100c40303143c00c1100c000108400180141481d600524040000a24489544c00c940806940c00b030300340382618000d1b100504d0711484a0b030110b010f4004546007803126980e49030510740c3c200c1003a601079554602c8001410f07007005150242101c40d40c0a0701c1c001d102c82e5100aa5900d0142800d00c4a041c003190f0349104901401c021101c20015400000141030004c0d01080034110700b07401101c40b105a0030103102c4504102c8004000d880d4160090035080d907500010034000c140c010680390400c15040c1490002c0b07100c51200d403000e421041e809000c04180009078801d5913680790301c5001186144082080312030707404a5901e8000358186008501c051403078004171066410745031140d090302d100090341401c0101c00c1c2011220f400c0900f60a00182e00315018441140c0401c64010300400d11007926902c4640f41b800040100906c80d90031002e80756161440c01000d40003081000e003c4440354010b020170f01005008080040500346002c0c42071790f050281e035078018162480b0081075804921 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 592668399 1250 592667149 592667161
    0x80a0305041109090c10032013030b1003030219020d030f110607050a090902130b0c03120c0901021e19080f0a02010902330c1c03060f050a0e0f 63
    0x803442c00300c40c44008001c10f12501380000394640b20030007622018424902c4103458100d07507000c0c0c0190b0f403849130301c9003081c3c156441030420001e641d40007034610300080d0045003020001a14410b40e01d40612a80c1e01c803001c0440c00c52401a00c0c1442e4550041c07901c06a185506006a8900c02d41d0405554503240510b490910100143c5414500c215542154014a400c2101450707220000c0c00c031000007540d03903000160750f41e07841d0b9040b40324401d542c00d20203649030410700040d03080800810b42e0404881c00c50340b800352101c2c0400c1c281d1000303aa14030340c180030000e51407280c1c0d039040204c013100c0c5000403130402c8804440304400b4ae803454081485440b80d08500c2c040014000c019065842c00354000240564074003c6200081c000c1118150491003040f100c400c4040b8500c090414154620580d051501c1c01d00512601c1d0405800c01002c402d01c0d441210785103030798034a600d0000743c0642880d4401060396420702c403410b54814101e80009000c0d190314041042442442d0007a160071104140d0804e05c1074442c2 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 592669649 1250 592668399 592668413
    0x50307240e01030f2a0305010305030d0c1806120f020c07090c0210090b0702120a080408090a05030114040b01080a050c04090f021801031106040312210f020c0c040504080a030504 78
    0x107210340c00c085032a001d40f41c00f8543c181d841d1020101417114141000c103854560540c00c842080c00050420791080c00040d003465040e0380204c020705014200500519001c2460480509880e0404000140903560481d000781e494018040c0540d00e000055040072203450070039039184000d01ca0030152980321442c1111a600900022180b0151075205100104c110f0034110500c1c0f00a03900c0f00014031502645807450343e01c4800b901e210000355500c04146880d5a2100c4420390811250349501c0075841740c00041303a60f424441d22a0540c8007400d88201450f05081c80a29840140d212000f20b03080040c195001800102da43d56100e04200c6000402c0080ea00b0400100360304d415000b5040345403600e000d00d0000c0a0054039040300c0c810942c616a50315000c0070f01c1a0b5000b9440020b0070200c980d9651700c00c460003840c80130314804040707079881c100360900b146c0d03041610100452007154641c0000c01c6800003c0034031a03440c01c400d050f607041c8070a0400d0350780c412251140c03d01d28820169100c010404100030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 592670899 1250 592669649 592669661
    0x51e0411041d04050d03020307090b0703051b0616090612050a0609020403050f2103010b1b01050a090209060f09190207060c110613020108160507020301060f050307240e0103 76
    0x111805051200407400c1440e070b9108042c0e80c00ea501e03219040c000442d5a2083c000c4901c150702960b1030300a0145803a0301c050311904110400c03818014240440c101040d10b5808426016101c0801040142404418000342001e28540081040b641d01781c1400b0301504074080c0c568200c1a1400043c155541340f25440040005821500441d800018000b06020700050320241d4041c202044e2410340701c541e420100c00103505121070000c010240010403030580c07004054003160100e102800c50600a505c40305e4212a422100710842076966103215082d811300c5c1074010f80c0440103039140b940218140c0002041d40384c0080040048005c04401a1950301c0181c0584c0c040e00d903c42030a200b1030300384c0c480c045d292218001c0d0020092060a00003100c40c98424403880007a038068540b122151a05140030307403080e88000840085c0901080803c0058400f48620b100406800f403d120041741080101130600c00507900c102c6100324040003e0003400b10281c95090000074500b0701c0c020400903440180c1c0035083e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 592672149 1250 592670899 592670909
    0x3281d0f0d05030c010618060807060f1710061112300403080105120c09040b070903021504030c06080106021207150e0609010606021b120f0a060b0307051e041104 71
    0xc5400310b0144c0054000c401600e545c0741800d88251003010780f28085400520aa441030741c0820720403c4680d000385c145907410b02140c601498011031022121110b103c2c155103511013602d12060820429a00c903104010580c003000c091304100800c01003a01c501d000718014180c1c14907450541082e54192180c2d48603a10000c0f4018401e185030030b00300a0300c1a0b00921406000d4600c00e24500301951001c6422401114000d21000da0345d25103451b00c0c030b41c800c8010002c000340030308410f001c00980c1e81c494100c410071300c1d0035480799a41c1c2d00314030f40350800c14204c0d41f1500c1442504801486201e0300841e400007520004d05120b500c40c1014100b41e0120000428101b09552030301403080a003900111b00d5600c10020b0000a00603280d9480c405c0340e5a003d48480011201c0f000840103440746005100e10459042c0702080760703104800505038034113224555104840c0b80e552084054038508062103080000d2000b103400d0300e01201484203034241d84400d00b02c0c1a00c1650b0340d10343c00104c07150703803421395010300 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 592673399 1250 592672149 592672153
    0x415050334060201470a0b0708071104091a1e180f03031e18011e06080a0b07030e1609020909010905010515180303281d0f0d05 56
    0xe40e4485000c1e00a0610110400b8002064402d54103c0081407900c030f40444e00c98605c6500c20107520049050905e0140b4544d40d21240840000030603070401c001810400307026441c080d907541e000d460600b030800c0003002c44500560607c031048011031180d0000382d8203aa102a003680b82d50780e0710401000c00003aa101c190080000c20420721001102180103181d01070141001c07100140703840700201d82e590100b210408a220112000301c0440c00141d0506900050f1007552004405001880a0b0a5500203403510311050041e0803200c0140d9440d01035000140300d030304060074003100207807507000420b00c00070140c4040c5a1a500842007403d010002581d00d056040400c69005445a541c24040c0d0300a14404d803054006070300105034150346115807412528010075407810401c01c407441ca0120741152441c01d070b4411860b60f040c0c1c1191000d00040c4500804190b546010010040c0403d10461556038182d00b00080c195401042c800311058000320703000101d40321003080c6010030015401d40d0003004010014 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 592674649 1250 592673399 592673503
    0xc030e09010b0c15010e1602120a050903070f120308070c02030a03020303070f05090d030c0804030f0f021509031e120c010204210f0602030a020c0a03090504150503 72
    0x14000500c0070301005840c030b009482155244c6083d24510f408280106001d1700000c001041514081d000074428040160059503485a141c0c82070341140d40106e000103000c1000002c18082a1400303108083c0078000601c150102e06041c45030700750f4125142d2400405204148000c900c407140104840281d02d40c1c000d0460b80344800da80b41c000e4598006403a58004640c1c003004405171240a1415281c0701c403c058103820300e10245071000c0b134007007528140079030707a01c101040088041800425803090045c0a40d01240c02038016205001d0030303100907040ca0b00820000d12006c00c5036540410180e001030034250300d8200c030f1510040c071242450300038942000c03010400141001c1c0d00006402500131a08200c8000e01204505084986122181d51000b0b03e20051040c2403000211154059900b10294a00060401e0020352440e8508443c140007030b8045480420100000e2419009000040c0600520000064a4000803d645141d0701410201217807003c1c400515450350110543c1902242c41000c3c401 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 592675899 1250 592674649 592674659
    0x3090f120c0b06031912050919050a1418090c040c03060311030705010819020415030506030106091107080d1803080f09030403110f03070509010602010f2306010c030e0901 75
    0x18000758070000c54500ea21036001450910b800320740c0f14400b0720140980340341129941d40310500411980900d0701485010301c01a4429103078045882c148840c1d203650791440d2400c01c070030804410080e038803000d52281d10980c039002e0b0703403190305a1184946580c5401e44494854499041c1403002094909400901d040d544541e603503455048541143c1c040c00d14800b40c01c01c0f440030305403540c1043c000c840c046003140c0c01041c044150507860030304010300701c2401420b042c0c07180365121900301c4644540c40080e841c0d5080c0318080c40d00b03104980c01030481d03240402c5810300c0c05040c881d20707014a1034050307e6501d000c140021041100c2d0000001100d080407111184405883c5c007038141841603805883c000c480d00c00013070b500030002046034140e070b800464500386d0001840403c51205000710509806000e0004001601d03115406864041d06480d0004681c0c0f01500304a4001c641842c00d04440e9658821240c03000c85800c424829005036013031910820030502400c0644500d05203401c401e400040e82000010 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 592677149 1250 592675899 592675907
    0x50f0f03120d06120f030c1a1015020d020c010509030118081312031b03110d081503030405060306040c05070b1006120b010806190b0327030412020103090f12 69
    0x1240010980d82045496140d0140c01081032000200519025000c4035845c0800d008469420080d0f100c2d403078101c2c00e03802d0107280a400400c140d03122800640904c40602080c0042c10000740917400328402007845202c168402503039255800c0006042c003000040c5015143c800390000f10020017107071907002442a0514040700d0b40d500000c0c28071120304d402840400c804164034041880c00e0f4040c1c4c0c61141040d42a180c1d04035400c4000c104800f0301995a072950390b46d40c02880078000c04402078a900f46d00307140c9034030218031110030b200c40340d03100750410032080c451a560001a07035040201518001000301e105402503078680300300000606000014410001e81d041001164800c1d82d02560301c200100d40f83d43c2038079058448a0010b5070102d020f00000441c0b40c00c0c00c040400724216604241303190544d4401c203400c0c040d441a2980000d40c103041200f9050106802e4400b640c8150b0540111700c0c1a02c0c1180b0042d00c144d401100a04041d111242c1005029001d0324411015404c04006d400c24444580050 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 592678399 1250 592677149 592677157
    0x903062003100611030315090a14040501061a0f0d0203090708070e06040c0302070807020f060d0e061f2306040b0a0806040e030a020d05030619080f1005060604050f0f0312 75
    0x3500003920f003649801c540c007005c0f09807801404021040c6048040c9170040080d00e60000b010041019512146102c040b9549464140203034003402c000140f0301e003081000d0402c0301c24078003c091101804c001810541c41e00d4000c9400c01501c2c1c000060300ca0302c5920f01c19040141560003400c2c14400c080d40400c543c000111000d010350000c95082000d403884040030380070703800354403009003d03040309124034405411314140c4a1181100181302501e0118508014400c0300e0b103030169801c3d5a8808410040002500d0707840d0310f02d04414201040b00f00d480d0004c40d403260b5038102d0080c07408140c4c003200045c1d241c4030001903d0141c940c14105a0b00e5a0341400b0050071404225001d44c400d6040c8803400d00e0500d0040222100e15040c0c3d800342c00c07a1181c40d0300945d03031a4000707441e0343c0e00300c81511201c0c0304000c54002c040f805021250060420140c0440c0003034541280c0d049442e0b03020f4038000038010282d032405c0441e411200d051310032403d035a149100240402000c03901d016050b014200055441d00c44010080c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 592679649 1250 592678399 592678409
    0x1090b01141b0a1b08210d0603021c0c050409021f0203040b030408250b0c1810020102040302030d0305010501020d0f11060108010c02010f110306010e06070f0602030708060f01090306200310 83
    0x100541e2000c0b411b07540c812403c200140c00c100300740c42c3d00e0ba960303100006000680c260003011844a90740d80c0800d0f8244c0c0340c0300e0350b1041101200061f038204124070009000400007120180070411480e000500c1c4410300090f03880980461140d1300c8001402803050310000c140700105551645810309045540c0da0008003c403c2d0a94010034600b540e1461080d00b140590700300c0c07844096551000c49001440c2d00c404548a031940c440b502d00d03d810703510801c0d10300c0c00ba11075034005030b112461441410b00d001c0140c0104001e040c144001881300d664001000fa00032040c525101c3d003140d06004003920035000c21002202c2034001c12001149101c415004400c5815160f030003008013140d0200c00508a611030f46682e84c4112041010520541c8114401030200300014011850100300e81e40d021042508580708540d40354001c0108803441d50005a0b81c2d80c060810f651200441c50740307400080070701200d80001040d190b60f80021002034900d01241c0c0e01d503090401c2c14291f40342030240750b0207000c130554810 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 592680899 1250 592679649 592679693
    0xd05030c07050a06230903010207140a0204050705040e06090604020702030a1101090803070b06100306050a0305150c03060d17040f120c08030406050a110a0b07080f01090b01141b0a 79
    0x40051005e00c01d103100a0407440003030340c124860303440d16007001041e40201c1c81c45516640900a00011604a041c2d041400485100400c8000e060780305000990f14003c16070002d00c841488100000000c480c1d441e50f03c8201181c4149450b980d010001c1c000380103007071000c1d41502c02c2c68925803c10803681d0039269074110988910b10403d58031000a9030740d200d121002002c51096030046406400c0c02c42c1001c0c051105801c000c13900644403c0031030030b40c0781d00c1c1d481074525501c80312800284001c802111a0006040c180c924074600d005000f282c2d9018011400410b00100c0d20311aa0504030400143c4002d071914040581c0003d50341c20074001c1400c1c4490040c1c482322150200010f007690000b088804070340a90715a2800c000c0764901c02c1da17014005c400d55030340c18099a011903000540106260384244c2030394450801c941040d0618a0346d8120581185040c0c40c0740420400140e0f80280d440d0402d4051040344540c4c0322440c4250340b104090921a55500340f0601000c07108000d46540308017144565508 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 592682149 1250 592680899 592680919
    0x1e13051614030903040e04051504030206070806060a090e060d050f2422030203040801060905041119091107021e12060c070201052a1006051503010902090d05030c0705 73
    0x800141c18031040d9a4020903a1040100300081c031581c584159000d80214180e070900503903410b0411b61041b040300c4c11001a000303030301001802d41e0041d42070358000c04144d6002e81020100d00e40600b2000d0903008200828488500054855079841e62401c0b14a0b40001954405400d4001e400d540b400c619207000711088031124046058074032407800c94422150421040000d102800e03107224004000c040642c00c5000400c008601c2040034007440004103c500c800141510b41401c1114a107010000c440388200300c030111340c02d1542035001442050390681d000004c0d08045c2c0450b403501502c150b51009410078280f0105882804d040c10841403600400d9940b1642c40e900c00010a80703500080701c4030759020100740452409544628007a1009000c040c104880002204150901c40321266011007416440809605005500c90141900910064440002c0c0703169040c00110203000502551020590100300c005150b80e440c843c00c041140c0080a6a648400410780c5a445840c0307401007030301506001d4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 592683399 1250 592682149 592682177
    0x70803091314060d1a0108070e010801020310150201020d0f060306060f06021b010309020915010f050c06041401020909040c09050106050309100b03010b1c060c0e1e130516 75
    0x801100c030600b03064240b80c0032a94400b001c128104003a440d00740c50500c6080c100c581d204080303d5480780a0314601008010452801114074624030050700300c0c0116234018420b20444a003124035000541e074070143c5940e0303409a04034040380240580c00014161504251001045009c10b90000064a00910b414098151164441c3d0f020060798454480164006190811754034070f40c80c400424000d0500d00402c0307180b91600050b10780e18040d1028400350458034030b080044e68000c0e00440c01d0388174074203241d81040c0400002c2500c03110018006040040402c2e49194031203001e5040b1480040001c00c29441400c0c02c0c1002100c0700d0f9940580812249800e002144a90094041e01d2150300c06900800b00b02d6110325529003d80f40c8140e10642564030382503012019a290b01c2402882214803d039403241070450b0070140107443d400c4102105200500c2c20404054446940400f00341040071281c3c0c860306004400f0034050700320f02104a200624040a114a0030889208901202e00c42c0d1303160504070380d1417 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 592684649 1250 592683399 592683401
    0x30c14010e0a0b1c0c030e0606040c090308070501090b0f160e090103031808030a030e060a090507060804111509131413030905061614060f190e0708030913 68
    0x401d81e541c0c8415245020049618207000901540a1300010b41c000034411200080a69181408060120f1303100e0b82e181e520408204640303640614100d50503c40346080c401c000d401106d05010140c822107002500c4414003400b5004283c0050303200c0381e41c2000e0300c0c002c81032200c042c0d03040c2d5680c00e480e01d0885c202014a44070345200314400000420300002a440c0d17a4054a0451212040040c401000e07140021038010901c042c1c10900d8254401060070360307404001c1d42c1800350041002500600e041501c2010a20029640043d0ac0c9c95040103007a584607401c009211260201030b981d0300c0300390710a04000e010012000303004060300650709401241248a0410160b40d164001100b0480b00440045c02544013810713880c0d038443c024203040d603000703444101040c00e5600c0308000f14030356001c0c50b80c01c40c10803010b00355400416a800d07010b0b05160605480c00d800304c50300500409080b07104103c0310400620694861030441c00f4010403210110f941e02107903500d0b0380102e90094452003075200011100c00c49 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 592685899 1250 592684649 592684667
    0x1060909020703120504060f091101030b0d0c120219060f0305070e0d03140f0708030603070803030c070807031e03050f0a020a12020310030c0e091c080628030c1401 72
    0x3c15103640d40c0540000603000010b1a00800956070f55440e8000b02d001d010081c414880d000380502d810001041c0504005029101809101c41c0603904003c00788010440103855041902e039130220f0301c2c018603918000203401062141042c100503116000c009100754204000d00d00084458500780305ca80d070f9141c019200d82100c1c1c540150014450900c500c0064802c1089003c000c0030080341c80d082a000c10a200700c4c3c3c2e000000304540118000003404807a1030104a158010000e01b4001c51443c90000c5408001340070704040100b924038040761540030580528443d400800c003075920001940d214031401005407005844c240c9100801002045003404903008480746d0302c03415220980c480e002310b0000e400a600003400802c65400740d080202c001281844014001c10481443c40c5440c241118541d09055050b45d00d00c80d010131814254140c980c01512141c4e01a004440807004c1140c20481c2000180d00841c15080c003122051021040080b03524500c81514115070b102504444054019034080e28 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 592687149 1250 592685899 592685903
    0xc010c0f0806090a0213080c03070f0b0f0d0204090f050a0b150702060d020d1e05010e01030c150207031203020c010b0f0619030902031e0c2b0611030f010609090207 72
    0x540c1c0c40005000d400c00c003289507002035052100616141c1d0b044100c05074082d050b04060f890750041c600701d880c41d2a04008080c09011040100703242c00d45000c44152203440b4401400c00d00d075001260041c0075102d26815140144021742003801190091002140100001c442644055252040001450801508410400000704043e6103000b4a940800060384c002c140380d0040c01c0d8081101c00030b076880314080c0b034548032000d1800e031507101e00403038050081da2070581104100490200042010030a0412005e044500d0000a070700c4c2240003881c22410800c0940010b48080740c0b4006614020b6410b6000b000e618158000070858241e1090801032802076444403d5031090092110302c11503080d210140d10304403098100085c410fa40ca0f40480d042151101c0c6000710380c0e0031103c103030300072690500c6566200341c0308417544103003c80c00d410350300d481c41c12501d04003002c015112183c0c8108007140c0c2c00521019580c00e640c60300d071b10380312061082002003402240002000450300040c0391487d4025581420307 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 592688399 1250 592687149 592687157
    0xb041b0302010e040b030c190317090f040b0d1b170105010b0d0e0f060109051b0307090e1f03050705040e03030c0412031e02100501050a0e0a020d140703020c010c0f 72
    0x8a200c0c1000040e0490717400c1c9a40c1401180d4001041c0d544404458045022080503400054514201900000403280c08a00c1c4a81c040103400415502c090003903982c6201241c0000b03804c2429808642c513044580c40c000e01c1810b0011566000841c110032a0080720318800421001000e00b0025a00b600d000b0301c5400291a81400101e205d0001c82c1c200e14106580c040032102022031200c102850001c080c0d01000c0c01960703580611609641e40c03048402c0100303c03410381c14070f582800725008025921620581c0090a02480410078030030b41103420281e0041070240940d0440e480c1d0070901e85600d8140304542c404d070320306480c00d8040e00020083c3da100d0451540c005081c98940a406011081e0bd180c0441c100310594644220300f980e45d030340125840115500501c8022413084e254811038030107030882d510641040e1420001d0000c460f1000f80d00c540e4000300582c8071075802c2d001601414041d01006003510345031040041c01c1c0c1c0e00d507000e403d422420308000c2c062401c44150988544074100d020000203 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 592689649 1250 592688399 592688417
    0x60f07030e0f101506090330031a04090510090c08030f090307080115030609031704050a05060903090a0b1605030406020f1005010f05040203060120010c02070f0e011505070b040b041b030201 83
    0x10561503035003005d4804c4000340d510000b10343d0f000090681074550501c40044ad6a40b0304180c0c042d44d460400c00386000060300c08010742505511076a5540c40901005050f2a0b26400c0c850b04010629402c04014504881140d03182c0f413002689a00319042082030a000388518030f00010a020b05004d50b42e48484154405c054160031130311000c000d00102c001c107809020b0803002c1100000200c1e40d40c648118069406044881c45515100d070034414007810781315455006104403401556228001d004844881503110f9232440c901606c50801d684031007000d481070201083c0000c2940d00843d0a29445950340c066450810043c1d60410450707000780107113068801401c5080c400c2d408c1a60046801940c141050080d02e00421202100701001100d41070403a5103580308804066010006a00075240000000c1d03030b200d042c85140003110105100d80d030007500e00c003c0500c505074000e0040314400c50700a881c0104524050034000040c0d24250b5040b20b0700d08002484813004500d118240f000d59505035107a000b0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 592690899 1250 592689649 592689653
    0x50711011a0a0510140d0b040b010e060910020705090403050301240203070638213a091401050702030a0605060406080303040c26060f07030e0f1015060903 68
    0x50841085590828450400484200e00c05c020003e0082c003520000045800c1e021a814001034072043d11040e410300082c80107001e1903981344000e48175890016184501c95822a11040f0318103541540075640200c50389003172005150340440218180e030051203000701c01c10a0100c003140440c0980c10340e240103070410321060f0006440d0f81c200e03c07034007000f100c0e40c2c1e61006d502034112000613040001c814840704030000300201508295403000141c8000c45000d04108201d849201d8441440c0129985048045907441c640251108015501034500c18408801c40566000c0507280a40c00c1c010040d00c0c0071502034095a03980300d07408580e44242e01174090400701100d6a40e00c009001e0213401558042c0d2503200c0403903203a02c02c0020307522640c016000c50b10702501c0d14002124114641d41080c01c0c82e20b544010240c0340b4800607101c0d802840400b1341c8146940d42d00021002003190880c101054001c038441030110b0140000d02415665000c181009192594481d11014400521601c8081901a541040 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 592692149 1250 592690899 592690909
    0x25080a021b010f14090d0503060d08070f080a09121a0c0c240106030e060414030d050906041104050114010c050304050603070801061b030509061c050711011a0a05 71
    0x81c1c035607022000d8807410300180d0281401d40361004880340d030865a0f1407903070036060348040c2c055411002d5800031b04100841204001c0c402d10009060707a02410401308000c0c1040301002c00c41d0042600031480e45440d0215160107c43c42d8050350ba20070006445100c007240f4941c03c000422802940410303000c102507844541030070039035002050110344100901101414070010b025012040c1c00c8500c0c1f220110300840c1c8040340f10081a04400101482d00c0c484000404001801d50b4100f900050340c0741042d0000010b1070b1540c410840e28850700ca083c030044c400002d00005026005c0c40c403038159040c030191364005002c1110700900c1781d92020308652a50483c60f501414a1080c1d241c000e000b600d02d4251240c0104e94154002d54526000800040041105030ba004c803036540b11080041001c14490a142c0f0020840e000340c43c1d90f42c0c41100c00050000504804140301d815620f41c5150038402441c04075006031085411812100165003810b00714408030440440c20240703004021f00150382d6034100002e03c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 592693399 1250 592692149 592692157
    0xf0d09021f03020406031103010f12060b0604030b01080c0111031801050403061b140702010203121f180b03160b09031501081f151a0d0f0525080a02 65
    0x2903003100319007a034401010110701e5404407640c0961400b507510391401500604075010311441010800050005011041000c8039400840d0340494240100c0d0540e8109480149150114141c0c40000040c0000400c080c90b050103041303a084a05941800c03984c0401074a4007030700810105000d40040251180e280c5003441251940d100c1850f00c01e080c1070f2a5a40c180403503c44e02d07165003003200044514441d02d64401c0020035640d00401f9524141407150340041d40d02d01407424460380c03002c3c504000445802c401d41441c22030070b0b042a04000c0150b61a080300a40d01750b600c1d2180419810181c58000c10305000030800800700d50303409103400703943c90804480002c0d00229180c070746c14028071002c140c8101c4420070803800f0700302100c05442d01040c00d4244803218074000c040300c0c01c003030309002d030348210418544101412218541c0c0905600403001040094522a4945160368549444c0071740711500102d60040d0703c950011200f030740c0344006071080e90348200040c01c06c100020700120001280004550050 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 592694649 1250 592693399 592693403
    0x3050f070e10090305010906020d0b030a260d0f1a0402130e090f060f100f060512060316030f021801051f0203040906060f120b011b080f1c0506060f0d09 67
    0x740440ca44c0729964142919113941054581c80e401060524882c00117104020008800f240103000c1d000341c0b41d950044034036909080300c1940c21500408818403a1107c112000001c220a003000016882c0342d040c0020703e42070303400d074248900380c03030078040182003620803601510070a91500782081d20f0142c40003042e00d002488007690f40150045582441780401c03195014810000400d41d151405210180361031045038490b07c400d01c010801045042c0d0404100e6903000101501c91041d99a800c001c031740380040710802000450f0b48a580003003840588603043d0400b520032a0744015042d0a09243c1d14190300a005155000030b207968840c0300b02041058001c82d052050064a04007942c48213904200c071440d52119012808508541055603849000e00200041c0003c04124013403410f400280001d02c60104c003003144032028200b809009500050b0742c401c46140301c01942e14610450420301c00003a0911718004030f4100030105000349090415035054108901e6200c0c18031005a00010180c11846d1007 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 592695899 1250 592694649 592694657
    0x405040602090d120e03030f070605150a08101a0a0501050d0b091501030c0c110609060d020307210504030e1513030506060a17030405211c03050f070e10 67
    0x41c0105a80300c520f00f40508a00a2000c0700900864000103808000e00c2601079200750004c12108207181c002a055a407641d030000c400182e00e40d9021042d020400799400380382c0d401790001030001082e81d00003801e940241c4152409200c41c1d44100784082100560030303c940d5201540d07031000d011035449800600300c18450000c020400003030308030200d1401d0405031810114074114200d40c0c002560107004546600c03c02d491700600c3c13003080c1d86411103901d0103402c00c58807a0000040c0c0c020039950b014150390840001c0c0d2011513803820107020141441c180040002048144224001e800003150701c0344520541e0503850354602e41a0b0302003080300302d4030a44c80c0085080d9043c000602104078030340307400300a94481c1c00100400d090020030880203031055807094003510311811070f5210004020040d1811200c00703813500c0c00702035441c45480401a441800100d01c078401d503c8010443e051030600318040701c0d52a20b0801554441045061240340112345850205046421070b2800d41827080c25102446003030300d0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 592697149 1250 592695899 592695907
    0xf011e0302030717330106180303030f020909010f0305070f080706050a0903150c200304091503050613030801141c06180f05060711120306150c15011a090405040602 72
    0x4400c05c40500d0302c140c2c0d03138402900c04000007200120031141d01400c464208803458200311f20340c0e4121003445010007001c141d1100c42c200198a0b9130f03010b44c2d9050301c0003000000150303101c480344809100640310564961051260029a81e194803c9001c280c4070b40394082d03c410b13030420710203032401d42c0018900020800c0303201c0008041800c0c0b2810000043e0022004501d0030b1009034000d00301140ea0b500c051006840c103802001c4090004121030844e034003040d0110b400e132034140a561403001ba41c0e0015007280158420000e10480064200c3c9609100c1d031110800381e40c880c92000c0d0040302100203507070022201001c0c01e014450220380826031034030401c000b0509982d0004070200040d1140422901d15804000da03004028083c00025844145480d006040c59070441e00503903542018905802c10080000c0803d6081d1500c1454100f18112459001e03510042d2401d00c5644030b1010940380200b80c003110010410110409007440039984900c40903080c2602e2100b088002d01d0050011a07030345500304 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 592698399 1250 592697149 592697173
    0x6033003010303080709150f08041a0c0c0610060806061c020a111902180421260f0c0a170a0204030b0901060506030c0a020a02090f011e0302030717 65
    0x200056020310301c41c0d610b10016060400028018051541007005818400690100165400f00d0603400310441403420401507100c0342480307a83c104000d001c0d03200c1c995a002c100946003c540e030003009503a0758542101c12607501c946143c1c841e03200c54018a80060785c980042840740c541000a007200e4054030040505c00380070020044100e0340705040b180082083e2044580a00506212684800714040f000001180940e070004248115499000c40c40c0c00c03c0c0c8000c2818400d40c102c1c05189031001000f4074018500d800800382c20606c103e954072800e400403049400d90a01a0107805004140640c4804d40c0c9d40c0710800c03001901d8204050680c20084078406040c80421004812801450f1000300160b6a905604141c124594010300c41f14880c0c1c1880c004103e030792244011603074040d400407402e0342c885491040c205c2c2844803106005c1c0d88003500704280070402000981180c12615920207585400c8403c001643c400c65081c40f0181d4181c1019008004c3c0d440e9180b030554a0207409030958014248076 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 592699649 1250 592698399 592698493
    0xf0909060b2d1f05160c0b090a29030730050903030108030703180506180a050307030510020a030e100603050d0815010c11040906020706140603 63
    0x2c034105051402484003001c1e290528a450400b82c01aa066114641c060020b8000329010b042c81c40100b0400088054030140d02d40040100c4503440f003072120a80ea81d0f04c3e416081170b04a02c0003c0d00c191001c00e00051030b60035031245100d041080c6004040340c0304d04081d0721021508014410b500f0f1140f0321a2000e030140303603140601c280360900784010113003095140c1070fa012110003c000360388c50791041005001070b00c400010303915156854038000b0003010b400c00c0090380745001c962106030400c0780480c0b186440603148414030400358064490a02855542d41003544e500014800076106401064441c800c6201c40c0c0c0090001c0341050401044002c1c1d0325600c1c510f40400c0000081c142a0749100501c1045014000000b906d00c2902d000d080905141c15001521007115644e50f041c06503941c1140c003001007420100b40d41400080c0100b01c1010581003d030040d500604046400d607240080e03200c2034501c240d2103140120030103001849054042e84941c010b00a195420700c0c0c010402caa4140310744460 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 592700899 1250 592699649 592699669
    0xb040204090e03121f030b0a06091404030e01031b030e0102090d080c010f06050a090509010e0607231326100c0f092301050903010c03091208010f0909060b 68
    0x200085543c2c103450424018003600c06025013503070624400a1051100c8881d85e020207407070b0410f04d6040151150007002c0001d2103541d000b0b00700c29051081c0b041226049404040c41140680c035030300f0b5110b50100045040319a030302d03020b80e001c40350b42c5065150140301c1d90004410140701400186003054a200103401441d0700b19088488030400a00310108640c01e0242c01c507144113140c002e200c524103050016940c00502c0c01401d449558410010f41403410035007000240799402000e070740d501e00303264200500051880c5042418015443c44090100102000300e40c2000f8000c07030100825800c0403900340d907141030340c01c1e464401340280c480e0444e070000a000401c50310100c440001581100108080c09038440e0300060828003130706580c1007140241f90440c0d40004021350503d080881c0c5040d0041c1d070030b4000d07400803541541c0307005509a0001d0b0190310007100e01d07005060043c241c0e140b0b0941110780e801309025014010502000070070814006802000d85680729200c0031428015040205200ca68 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 592702149 1250 592700899 592700921
    0x1e0e0307050616021801031104180c03030203030601030c0504050a0b0c0a0c061205070309030e060d0905100213050925090b13090b040e061b0c122505100b04020409 72
    0x20041e041100310300c0c245c1d00a030322a03051508003681c150300d180c40300c4090080d250740180c0030302d40ba040720600708840b80807803441c610f0b401400380394103548a041c0207682c1e4000b20784290104c0d2402d0300101c0514054015982114002400e413400035081c15a000041d81200c600905580310300381284001603401090440a0051961002c4640c1030402e10748041c0c0d00040c01400c02e041c5400d00c0c0c6400b1036882201840c0c0c042c030564540707503074a2440b416900200743c202c0d400b078014002c910720740c1d40f0780301c89400429440140481e501c00d2641c40340108030340c1240643e07802c0800140c0840c2c030519842090310b42c000845071030610410039540c0350040011540311240750713a214105440300f400a2046841402112402520b007000000b501103003459071008c0c05028413420070b5070041d500380d1a0340c0c440c080326481c005013000c1d15400c49500403e0100c0d40c000714503c84402c01c051881c80031a170070110310b400c507081d0080020f002142c0115142401804d4400215800079020080442c40c07800c80d01488100038 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 592703399 1250 592702149 592702177
    0x110d0c03170f0d090302011b08060f1311030405010b041119020106150c0210030515040e0a050d0801080c01080601050403260a0908070b040806010302060f120709060e011e0e03070506 80
    0x541c2c4c40c6802401c44c2d154282c0c02c104101c00000c02041607500120072684004140d4103c17000824640c0050b024040c203075030514515050111764494814100301440c00349110740002e00401c40b503001000252010703620f010904003412721002f90020708992110140903900c1c000012115224403100c8d103c80321801e02a408034100c17a00c04011802c04803840101d180187c03400700f0490800c00f2821020418041d40184a1916602010a81c1009120121a56030322104842d00c000c4a00e0003d01070321000d20402d009409584182a11540204070503846030078169200c034a07003411a07840420302200d000188416141c1c4050001d240c1d50158010b207a040501c0e145d0b1b0314181d2501c1007851412081e40c1204c0e039400c0003403000b0451210000f1380c5605480e412100d0f16241d00d41004401024041c08404d5508800400b0a02080030b402410324029036030b0a56555440d54420801074411114504180c00c00f0200c42c122081c501e0720503400b111140100806865203540d13070f01d000403415000322a44010304 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 592704649 1250 592703399 592703411
    0xf090f02092d0115030e1209010e101107080d0f110a02090a06150306030c2106092006191d060c0c01031d030403020d0305190c110d0c03170f0d 63
    0x451070351221240400013a04c3c040c44520310441d01c0b00c0e11000c00180c50b0740306c41c5010604c00c40c140e02030888140800400781240c010450030780001402c402e807020108403c0d00805c04003007124040031030b0100400303105458046103800c0c03000301201d640344c0b5442a410300b80928a008001aa6002d20b468004e12107400e010503a40c0c01e00a4003260181804410400e15250010400004400040c1401115106000500d0b604011031a6941c1c038440c9480c0140401d180088a800704003040742c0342241c10131801080e004284180c0c007440003070701c80d64051042d0803196401c1401003034070400c0900c075001e052000c4406110b0070740010448540005600150a03003004c1a421902c1d40e05214a80762021f008030040c1080d480348008544910a13400045d0203541c0d00018001898040c00c1141d84e04101e09440d2a40040c0c10354004100318a010400c0f254039a05001da5172546c905916100c104a40151107140e400b1b145945100d4003540104852514040a00809510300b184401034480c059500c2008180703 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 592705899 1250 592704649 592704659
    0x201052a0f0709060e06150f0715180f020d11030312090d05030f0705180a080609060c1305041a190311090403050a050d090204150302040f090f02092d01 67
    0x300111034010f41042c510700701080088084040712542c000c0300940781d4a000103091030540701103100c0c4021001088000040c90010004040103212018400d035904200341414000702904000700444041e28803600301c0c0707040025292001071072206501c40c0128405400c0800e01190a681204204440e00c600220821680800c14000406507141c1450700900d586002c01c0310800707112014002404101e40440c952040b0038940d0024403004074001c1400865a075075141003556030100301c50703058880c0201c4010402c0200640c060b500102c0e42140c0d00c00e030392402d203001c0c440209408800109480d00f13004807a8a561181325045c401140200031080c6411b0031814029001d24202d9401030107680d6500400012950041c2660110809450601e0380c0f80d620700100b102510040c40060346c01860121039030034122140449100b124403c0d6010700ca810f00da20f0440003101d404c882c01078000d5100b60403800040c030304456001d0340084141c00607003040030400b101e000020300786804240704201400c01402 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 592707149 1250 592705899 592705903
    0xf14010f090f06030515150901260604020f121609270809010807050714071a040e0609040309090905030406141305091306021801180b070201052a0f 65
    0x184042c60905005141ca5551600e0341c801c00b0380708048540c2c124001280140a410030f09588901c0000d111300c02035610303051455072130002c00c04c107042690452005194210004184288500e0f0028a41e41c001c3d902c140038082c01307586c8800c2c2000d060248400440906191071418030252155400000d944c02c04d0f1320841c00803019003400c00080000b0700118100040c3c83d1011208141e00a10348084180c4651800340c6d000c0c01051340007400303c4490342890030210320001d119802c4400070000300b01c0c0c1582480c000d45c540e100d14090001082011400600755040411300d582d00726100e4507250540075524800384007240c040d600308030344503040054100b281030b07030040440c1c1c550240070310594075050144e4071200071211188a954001c484a5001600c42c20840c03006016079a0080002d564600b00c0c1d0003003402c44e0206c07500382c9001c00c080c042c1240c0c858807020721000565400c0302a0364903103d1960015241d03a0800c0e84100d00d000d40709003401608034200c12161184070b00502c010310490b800004014 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 592708399 1250 592707149 592707161
    0x312030c02070b0708090409051005061c031d220212060103060b0d0504020402091207030c09061a07050a12020d17060319020402070b010e07020f010506090a0f14010f09 74
    0x60215804100c0c03e00a006a8104660b41c5581c0484081d035121001d40105001d03110340c88000c0d002d405003e4a498a45049800a0784114008c0380c1c4103009410400141c080500070202c05000213030800400034821081d914034041400c0010304103d4080b003e942e00001c6140d01c0040b200e00d0b10303000310703000745070100b01101d032604a0742c24241800290700701400d43c62a8080c81600181503504c80c40406c0554803035504451662001400b003004000704c00700c410355141d11a20040310840c260490016616405224180076103003d0f070b0114012600e8000c00d602d4607003161000340c640d809a080b010000940694110124070410780241c001000302070f001800001c604049802601001c208100a681d00032030724540340411240c440f0b0358040a800418000d000b03c0724003d041459000c00811080a05002a03100c2c403400d900300e43c00424001280b50a031a170649140b5046500f820203d002e45506420410200744000310000390484030b040e00341c5107410285d001424514469000f03020000c1140111 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 592709649 1250 592708399 592708421
    0x2150f0c070f15120906230906040218040305120f0a050a0b1507030912140f0c0306070c031107150f0e0303030103110a0f0e161d011413031203 63
    0x203542e40ba0614656603550220442010400201803882c080d0f0f0300c075032010100907003000c000c0001c61100d00d0301194214268400501d40111000082c4502d480000c0c1240304560103044004923400800c40808414406001101440003d1242e0119080d82d007005a201d1501d030b10400403a42001040340c0122000900554502c90030302e20b0103189a19030004507035440d4800b0035030b1551000c00b41000c41c1c82c0e100c690014a011040b24182000740204200705211f03052068081d602051b00d82d00490780d46403074456095070107800400000300d580d4012945080d1160003804c6c03880340c216030340c0c4003141081c056402c144002c220160550140035400002000440d1060030501e000c41c5000c0006507407408141710040008a105030168860f8585414820041491f0f00e2441c3e00e032a00c4035645409000204e60202101b00c43d43c040c1d00d202441170b1070007002c112a0042c1105107142440044030410544115039004030000c002030340708100d02d0381908009500600c00c3e561840e5034240020300356002400e030 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 592710899 1250 592709649 592709669
    0x703020115120f0b07050d060312140403051005041103060414120c101a10050d14010b03040b040606051005040315110a0e0d0b070815101b02150f0c07 66
    0x1101000591501d4403450b20781d00040e400d56245e82c0c96504480511a42c544100002d0502000008220365451880c00380b690540704d0740303501c5410803041840340c0500d01c40900b485d070208254480714031480e8001360700140240e201100b40c13807102c00480d24080741070b24215520b00c1840c51801f80c804050180309107101903100724928081d401a030f0340350340b6140c40401c0c0008a41d120308100d040b220241c4150103404015007900c1003441c0f0440054000d42155407420101c50403e4480d00566420100b12416280f000030303081d04649581c3c0760349010100c02817017101e000d0b41d00c01010070290340c0c1201d5070420b01c3e402e40d82c5907551411864000d64845002c4144083c29003400070041035900b100c000e680c40d41c030851404e44030510680001901050700220f01902400801060000083d444600d852041b4081205085031038205000d1054000d0070603044000161488160034940d000d0074103441c0b6541c001804039003c0c50001d18000380302c2d031082c2c1110a1014000440617144001030104400a11103641 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 592712149 1250 592710899 592710929
    0x170a1119142d1b070e0702010b10032c0109020f030c0a0b0705071d04050118080405010e0303120c0304020310110a030f1b03060f0b0f041401020f030703020115 70
    0x155074071406180032031501250b0014481034005902ca4060320340301c4042c01c14054090920b0020303981c5078400c901401c04004120000101428014018000710103000791492440794641c000c04c50013008903c1c8095030251200004500354020011400c800014107400000d081c0081e01c1000703c2c0c0200c40300200d0003608101041c4800340e03a120f40c8402251012859030b951400c407850081d041c20215000b450700c83d00700865071051125050300081c4070301d22400080221101d90b1917042050503540f42e004018407402c010030f10583d403203032244080401001c0c003100d08010640741000c2d0740e43d400300c8040800410100400040d49805c2020340d0313203aa1811410800700340e040007111242e00c24aa515402d0580b24003000e8400c25942d40900b400b131901c03104000e9048200040100078054521401051040312440802e9505195003140c804e089130802081c5420f1620150f03950440c2803210103419801240344050717046170300340000e1038010311070307030002881d480541844290092140c110382d001ca0340140f = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 592713399 1250 592712149 592712167
    0xc04050402030a032102070c05271506120c0703170403050a0302090a0905040510050703020c0318030a0b0109060e010f082515020a05060109050403170a111914 70
    0x11031020fa600e900743c60b00c41c4422021503550103051071701c100f40200680c4000784040601080d000241c0a5400403142c5030204501d4500b608000001649807541c0c00b80800c0204d40000040801da60705100068003050500004001c005c00c0c000c012a022402c4000000e120401c06078840d002c043c1c1c00c90394120f019900d007041d403001005802400d80b0481810b90004801c4010b030b4030b45250000520098030103008a02d01451315076140c03038480c01c40012590400004c140800e029009540031103200800844c20301c00c00c3c1c00b0801682c1d105495081d01402031007203001c0410744442149000e0242d0b18008600c2f54900032080c055140141e0100c0100d8200f1901032100d0f01d004240400d01d010140513050b01406200780e1814580b02d2540701c1e52002c40840101035a41e900800d011240a0013035080e50360320f80e078036140941a00c208507401000070b0803a47c4d0b180c0548104101c1c00c0e4110f10400c80c0040c5000b1010302500780c80d40421100d82c00c00114038481500942e120780046800c035400100e103800d1a020b0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 592714649 1250 592713399 592713403
    0xa030608060c041a1602060703121109031f06080304060c03020706030b0d0b06030c0627090103050c060c0f1209030c0d02010503060d060f0f1b020604050723030a0605090c0405040203 80
    0x1c0305641c07562400640006400e885c2d07200c01d0011500103140c165102011b00e0060560b031102051030b55820704008601c500c00052006550001001130003800c030b6800010080c0042502415640b22150703914100440d00003400c10181003c1c10998440140c19107950401a151801075032100003010308003120702130541c40c0d900d401c00b10260301905d000340c6500d070500001c1c107114501d103880340c01c14008642c10560200020840c0d03218942e070240c581041c51044140038002c0803d0001800d294002d10941400b41011030003451b500d07200d1000c0d5009625410300140c1401c40500250100400c00b0481d041145002d11103c0c01c0c0c600222407401e18090f20ba40081c144d8000185403900c18078150449909105040c0c0000200d9460b08004200f1a4660040c2c01c000301095400414040c01d40d07803458102600000e500b0b0b001d603402074000c0070b603180790084842d0200d035002c070310300d2084c0d00714824503400c0c0e00c0410000000a01c00c0502148900e000c12000e458040c5c00d80036984101d0800c002d010141e240 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 592715899 1250 592714649 592714679
    0x603090b0a0c02071208070614010603110705031e1201030f0b010e062206030c120b010501020a030503060d03090b030f0a0506030123040302190c030204050f06030319140a030608060c04 81
    0x1242034a00340d488035080c886c41d00d00610b103020708240c0c14040c007e041c1c200300440c400d0580340d01d0740b4104801e800340b43c141800e0340914074000b04554410888030358007198544e002c642c480041c4141c4ca14003036045625520003c000c0e44101c8207036500c2d603d540c040001d80074556001d004064514109840d2400c002824000140001349900b0304481411180c00c1c03554000e04091900300311074081c0b032131340d03403000d0040b420b140381040c1c0b950210349002090745d600c0410040c034165010340d2058250307180e43d410000d03261040b202c103c0c00c2c00360444000030090a2400a5407080718800c4250102c0e241c0030080c0c0702529401412113200307915041c0d0310800071300600240c030300760380c11011842d540380d442c0c0c0382c184c1ca03005071807011281601c000c40c0c0d40401c11011401c0441502d00c00d940a008a440d0b850215448950541e2460740c187c00c01e01c609180d0b0004d51b41c2400c1d080b03407e03140445175a07104041c0741080b0340c0700c4030000001948440050040f081704000750303a0040b11000c6920300d402e141403074080c0c40300c078 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 592717149 1250 592715899 592715909
    0x120207031703130f14010606091508090601090f0b04050c030f0a0c0c260c031b07031e0f0b1503011103010609150e03010c08091006081209040e01060603090b0a0c0207 73
    0x4c0e210502d4007032110040b10140500d0000e002085130a840d0b5034041d1800072280314400c030040c1d006440c03560541c852070816000c0c1008000030b0a287c1d08006084000e00200800100150794802c95590641d4945c02464084c1d2501d80d40c0554038208803000800281d4014080c01e402400e2036a08980d0b154844001c5d20032230341004041c110f0315002e04000000d007000b026484046c95001c03685420013403000c0001d000c0911441095080a420100340b2900d031141e910018007000880b20241035400b03404220642d0452280141c3ea0211180d96204080018180e41594010a14261303031516420248114152000c84040d071a045600d0004010600c1d415030040964103910002902145070180000e12001c2400400a100162007420002c4c061034044801c803100b4403e03040e00307090706090f51054400741e400c5003001e864852520074082c032056100c52105a0020b6440003102842d04d020305c5404090505940e010408a2440c01c0000c402c10000d00b58a801c0d40c90509200b044a8001a011301290 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 592718399 1250 592717149 592717163
    0xb0f0613090503090a030c08160f030f02030f0a11030721020d020a03051f0606030507020c0613050d0b0708061c0605130501021b010609060308070b04020d12020703170313 75
    0x500703140b90480c114094809040d4010850b41408070400032210f80c1842512281021209140c0168111084800c3d85104585444140c8507040c40880d1014549481d113500160444804a0301801c40e01d25003014143e00303032103a1195013880300c1c0515041c404d150081250403404000840942a001030345140d008000340304001e6002504215107a0108080045411206445d00083c2c1240c14126008110345c14000451801e04c021440038000d00ca25406600c013940203104520030312050010580c04502004003d00403010005843ea40d04400c400002d03108104034402d904010001801010020380f00030b00c06d454646c0040c0304034441214181e189070300b04001141940f1001400101202c400c90058801d500005265420368050364020540d1158a030080100d541da83d0000f0b82115854003006000300b0b420403144002c601c5010010b0340040c00240000d484440555455407086200311024005d60803007041003040c0050319102c040194000141a40f0398900a020040c21042c02c060080c031030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 592719649 1250 592718399 592718411
    0x1061b03200a0b1303020c01170f04080d0c05040801140c030f07030207080f0a0806030601080a1b0807181406151b01060909050610080d080411030d0c0b0f0613 70
    0x690710401c804402d4540121160700c45080c02003004030b042d25481c1081d005445004d4154550394803034419050200d01141e40d030022921a0200008940c1001c0d00030765600c8801e104000541d03515200f108101c0b9441d0f00e456a0b250702c0e2450b9036003075551402c180c01e01042044100726443e10740343d00b1030341e000b080c05000d00c4c0180c0d907108003500240200700c00941a10004140c115264001000030041107405440748802c50b5920002c042d03a4600900580c102a0400082c0300002669849860303045c800d420b44110096447d00f01462a04085a010b01e009009440114a20303c4462254408500404000c0810341c41c102e0049408604007203428036007a0000543c811280310880161081d46081c000240825603440e005038024004004090761980a9000824113400c603482000c82181e81c010080d102c04151124260f454002c0148155859140e8120030821560284103112816a5a440d800303240c41440c00c090241c07500081504200745a00c5007448401d0741d400c0e540702c4040710410320103d80 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 592720899 1250 592719649 592719707
    0x20126061c05030711091015030b030a02151b0a030207061101150905061215010603150b040905010e010504231503030408011a0118061b080c0601061b03 67
    0xc00750001c44040c0150001068038820000c0c1e0b11102084158100c501c83c031a91a1100380c00342d601324034460b17102c04070488915089603c0c00f81c2c015840031180202a541c0584560300400d041382c0f0186000c44c43c9590010b01c1a240510003400c108c8441d94401c010049940165406503840c5100c3c0100410301c01c00f09802c0d0b401150940001150000d0001914a000c5d900c00d08540903042c1179802d207105844920100b030304084000b070b031606000c010008120a9920b032042c140d000b401e12271038401590f05044004a68400b40c00c6c000c10080445d0000012250b140001c81e0030b0845068100e170344614207014000017119003108000364000d0200140020076142d003070302c103205031a00000d00c94050001040002c0c501c072066100d541100b00035034005144500c10801103401068141c0e184146c0c00c482c4106020701446088200e003a04000c9200e0f5030303000415141d00c0407581100903c00c969910220041c0460740c1d124071203428100c0030b03555040a0f0310280d94040c0010100c0e4503540c0c0842050040148 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 592722149 1250 592720899 592720939
    0x17010e01290c0f060109022502010912050313050a05061c0b190e010909020a1809060216052e0515040c0206010f08060f06060a110105100302012606 65
    0x2110010314681e5280c480c800380b980c03101d24103c8103a685000d400c0000414108900845000c505178110300044402004810255940d6000303080c0c3c10094030304000300e2403d080d00d414041d180e002d140155192080b212100c040512550003444c0513103007040082095456510a8407050010868140c0204141c000014000c00d007010b038070b542c401c00031120400500720940e1494151100051a129079a0320f032429482a504030100003500555402020441030030001d0b1042c1c05100d1042000c0b07055285600e0701c00690b0040c21081024801000c0f100c3c00700300040101041076030b0452a0760100c0304070221803401012407000c0e009002e98803880090009040b00600d90390046006008100782110088020740e00d140900a10002200d1000c0c0802c504500003100b91140c503038100b00981c0c0741e40b04014019180c2005401e8000e00080303002c940680303c42030140a2148054545806980d880c500005205129400c040b50701c6150705420514966502800c003540b041d4255036202800c922942c96035 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 592723399 1250 592722149 592722209
    0x71101030f0902281202010509120c04020304060b09240d08090a0f05100309050c061b34050904120203040b040b0406030e1c140904110a17010e01 64
    0x35030144404c500302c840300140700703880c4600251403c000b010035502c0d6161403c0b040c110b0080640031400c00c0c41043c5152900b8400d10104032941001c2d01c1c41028403030041000d0303800548044036004d07281c001d00d0481b4200750b540300d81e009044014100e00e0700641e6051191801e0038036030ba0340c02480c07040b1407502880032803400c4400300000603040c1c110700d6689489074404121103025917031245c4015607008003820f100b03009609510703030017002801042a548003042890791000490100c4a140781d5812608084244010300e034152003c0c1c2d0b280c94504010190b9081550100302614002440c450280301d07030f03118a1001d03640b1580c00081444a4054084280d1441c016a40030b083c41260007d00442e10b048040054411140107031411b00541c4c0c12080c110340c581c46000080b1070f01e000d0b10013840380481e04c5a20450000960241c54a00d000086800b040560307850403103031946100000f540d02c0003150312940b01b121010101000c01925410080b10281001c03061045000722145c10900b120340000c010640 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 592724649 1250 592723399 592723403
    0xf050a0c0b060102030c06091501050a06051206010309061802150711060901020c0d050a050c010819050a021b01021309110a08070201231602160302061308150912071101030f09 77
    0xa1fa2503281c0301050356601c1c04007844250303201000c3ca000086a0511030740840c1554000c0d110a400c18000400ea0704a00300c005141c00e0406855007401c0c00450b41ca8820964100000015049000f00b1401400030344410101246403280c02045840e01189600c4400c1411074411203041b607a4141d1000100e01e00440501d260f503000d04e0740b05039942000400920201514800c1040d941ca10f01000010b450814085800401c1d107100030040c0c018801640d441142d2140c400c00005003040c540c1d028036040b8186017010078240342e5000a40c2d0900e0004416407500a041a0170300303100d000d100e101c3c425010b0107289139043c1446141c801041c2054004e42001c1417206c80c1c02c01400c50003901880e1503088800c15660405400104150801800d10206615040051011908480c24134640c28040654003074100c80091035400381380401c01c054103210000c60182c4444a031992030511519076400d01c02211141504070008104942c002404c110a85551040908000440c0100c1504040c0641140400 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 592725899 1250 592724649 592724653
    0x50a0b13030306080c06040302100212310f050112090204050c04030b0a0501051f02070b220b0901090b0c010209030607030507020c091e040c240f050a0c0b060102030c 73
    0x8000c1608410030620800c54020382d01800311039900d42e21561100c00180100b500540c08110a10250030b0240b01042d040b001441120799865402c03905062607001640a42c2040b40607440c003900070342c800f441a2149444084071009034034640055544401200c0c4101814020b90360b0105000341e1440c0e00240106030041c0c0103002da442c181d28000840c0e441804222001d1f25404080b0307000106a100303050689402030104c4048126503d40030140d051117030b41c0741045100e4200f022884410500c00746c001c00a503146045070640151000406002880c0c0180c01e00035003d102d01c5407507aa115460300d04680180c4985a03446850b100b8980c060310804040541510035641844061541075100910484041c0d007603c0c1d00940c881c0030400b6525058030b94421500c4003440002200c608119866001482003030f4000711503541c1e10100d2214203540e00c00c1c0c4040902911440030468120902d20344c00107961030102d140c00d54806000c2e20740602d090010b02484c403100009880c0707034000c1044403003e61070481 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 592727149 1250 592725899 592725901
    0x70308040b041805240d060911030d050315060d0605040207050a0215181e030f0601061d01080718080a1119150e041d0a0309060e010912050a0b 63
    0xc07101c902580144160540c40b40180149003030301c0e00c507114081c01000750041059040030ba110388804026802c041045e0311810811410001034080d21840b0600d62040041200c42c88848003058101424590490f00788501002080340456007421201141d5204546144d00c405040c10307100c0003031200340c000b6a00140300142e008140440003480d418602d03c00c641707100f07542c8000c07441008a1b018540948100b180c00072042a840c1c074141c24103144001c2000b001d00c6813401c500c2c00003403030030310300c40350b80740c41600803100500080b94002801480d54412403009032085224500003400150014084010420528241c030300e051044400c800052039440221030b00b40100c0d090038442004101c030b1235845100340c00600003080615100b2101165584809041510030300101070340c2401241c849503900c1a07461034071206016a80d80a0840c039520301004000365090352801801c0c4141e250008010302000c48550b108680e0710400d00411703582c0a900c07016401c0c0461074000e10f01203080c0001030001c1c2d84030b0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 592728399 1250 592727149 592727159
    0x1030c0203040618051e0a21020f13060f060813030f120f02040902250b0423010507031d010506030619110412030912020a03020f0102030d0c0905190b030a0e07030804 73
    0x20f1b00000000c008603520070045945001f41004000780006034040e1036141810302c030140c035040c1001000d001d40507090055a590b80785400044800d15040f03d00c85103580401405041d078008034040d84188000c4540300c04034407a44000d46014451208002001030a100014403402c43c0d41241c0e4620f96418403d48d240d541f1552108082d40050003042644a8020650755034a401c542c040c40d070782c81d04200c0600f0f25071180c0d02c4078681c18050f01c9000d45030703101200c0240408202481020710130002ca41e40001d14000010042081c40c0004090304500da042409019050b074003c520039030401c000d128095003103403400007610041e0005c50070b1640e00c180041030020340f00d012405c421940c1d51281d40d0340412036480d9407031901d025144e920b010703401051901e4140300500301200001085101401128100180381c804035042e1020701001e0070000f00300450820250401c03040b0446003040c2004020f20b0300d8104041881035010042c0740705000e40d2100e51300d2440820a100342009540c20420682d5995215 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 592729649 1250 592728399 592728439
    0xb03062d0307081c08040b0c07020d05061009050a020705280203120a020105010b030f04020d02120a0609060c030c170402040b2715102304090b09010501030c020304061805 75
    0x484c20035031000da906815032643d00d1007507409500c40d652054042c03000b82c84104424611340c02a00e0101d8206001c2c0d20031002043d420400e051240d401e01d443c0000c01c43c2410302820035100d014020810403401845014001340c0042050100041c207480072000c0c40500385440e501c007403842c00300070707406010700002ea903c0c0f00ba10400524890b11903070000e00c2266030b42c3d01e050041c0d100843d001c244a03180100840c0c010300e082d1005d50314942c002030124840c1004103544d6810701c130301c01300101c030010707541d4420f1010022180070303004d24070890303090811055001301d030081c1040c541c210400c42155007481c0003030115511a0301922030a003015008071080c401c4503100422500d00b00b0100c1000e42c80c1100007a2152014880350400481d010303086562136076000c00305a904240064000491111410901c0a0b02001c2d60250000b452031010210b088202030050241c62903042c0c014504041c201501604500c1d00001100c0490340c2078644403060201001240c0600340417030300001d611003241e0180e640f0060304 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 592730899 1250 592729649 592729663
    0x40b0709090204170c01020d0c11060d0609090203100209010c08070218040825170c070905130c05030105010e040209070912080705010c08040c1e1707030302070b03062d030708 77
    0x82042107170760341c0c001d4900680e40c40c0705220b030700f00028508003030000006401e4190010142805004182041d043d410b02c14190b4186800031022990790b9400501540b50411800141000c115803c610b880c2c0180002000c2e4503941c2c8000c1d0416800261090854542412161041c5d0303840e01004140c0c101b6141c0f0a80550041d1840502085602480b011a20f02c01c3c0e08420f001d5440781c65007051600700032001c4610342009505500306d019080d80002e0084060180620070525126580940302d05c610308050920140c2d0800c60085c0c0c58000140192070300841e1240d0040d8040314103007003e550b00c2c00c0c00c6804450540101d10702041003000c05c0108a0303428003500ca0706101d00001e0001e030001440407200b000d42200d0140c0800c2c0103103810001c1e008207400d0310847e080f07840480140203071a1480300a0316001034a80b0340807680484010030a056050003c0e0740036240100542c1d103982841c400041c44094040d500d8170040212642e1880081c41030b5441a40900300075040c3c0f002240d94000c8103803940e80e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 592732149 1250 592730899 592730939
    0xe030a0b15090c030105010f0809010b030d090801060605090906012a06050f0603190b0907030c08100501050d120305061809074103031303060606020c040c0503040b0709090204 77
    0x2024000c039000190341c0f010349050340e0781a500c01c0c1c81070340c20f80000c0302c207a080a0f02d00006c9560340c541c0f180031a101400300c803164003056110511584c2c9400078503400c4410a031701031401c02105001203985a95800109508028246040e480e5a984007244903501103040d43d6a14200380111100400c106060f04035a02c242000e0761301c108075644403800d143d140c400032481880c441d540200074100107000da4840c0b90704040500d003208c0c4402c0d129070714082c1030072264100c1003196211428002109110340545800b404e41501c0e49501c3d800707141d403003d000b504c151030590103042d1107600003120350300c0d88510f42488514200c18422a401c10290701034a5165500440b120420119050b210310b88041034001c406030005403894801d02aa001d601918907034184041d581070008208080400c040c00c502c03040554000d100c001812890036401034900141400c41501490400c484545c00d2500f00007601e44c000e0700152948010ba648050844000c401c0c0c0e080820000d102240100b010003900c8141a80c7c55 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 592733399 1250 592732149 592732159
    0x1404060905030d0306080a061d070902070605130b0406021e030109020a0305010e10090f0b0d150c0207051003051308130609090b0603071b0c030303090b0a0504120e030a0b15 76
    0x241c03420f030110141c0e0104d01640e2000c4e48111141400100581d00c0703888003146000c1e2464100e100c20580341d00344501548211201e0340c0124120043c03148510032a03820450400c00c0d5071094405949415900c40e0090000c0c015560100310384244030044d1451902048420f400741d5540e42e1185910402034100c03228200000b858500086030030071004400501a91200c98a0307284a03140441201c0900401025000199218070f200c1031107403155508050340070304ca14005032010030b1049081d0225010320540c5400c40d0f00c1f219040100da150081a0b640340362062170b000c40c0c241c0e505403802c6003092011000600b0140c00181d1541c0030006807010307205440d0603544040c2035507076071820356054032400c00000313503c03810030402318240502480155940b01c040c0703030854403c440302d92564003611286070f0080c1c000c65100e01442c020012804403440d4411520b42c410819814207444480702c4104c2d0b13010b904240451014101c03000d07a01040480501ca90007006081c840c03615105c600c480c0186103200500071303 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 592734649 1250 592733399 592733413
    0x1060f030b01090b0c0a080d0e0f06010e04020906010c0203060405100f1116030c0b0c09101106040b1f1401031503170307050f121f081903140406090503 67
    0x4920034010001a00c81c16500c20311120f09000f492051903004a07090314152040300100d0000642100c080e003414120ba150020b401001001c0b035606115420784003004035000310f00107000402000c1c841c180c2040e01510005203540d40d080040c0c4034515001307006940340c03080d10300704070800800107410541c50010310030034811102107107524820348083d5001034544000601c00003662007482d8003903425850180c542440b01c183d25807902c21b141e403000ea4400684a00c0000c12059a09082202c40301102c040e182c01c07042c18446403040c90711044003030401010300360080081130808000420448c525031500c0c00c542d41c060ba644500c041d071110b1100780d1501107801c2c02441142541c0701c403d5001201e81004804506c00008604621a940011b09146c14010306000400c6c3d8051084098584848829222003e81c1070940b905c041048200d03e101409006010041c00701a00118040c5034885040038606c07035104861906864105681d00d19020020000c50000741c805c0d40200b014048643c16000d41c0c0d80 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 592735899 1250 592734649 592734677
    0x1309030e010c0203030306120c0a030c0306050601050301030f14010b061b0c1c03030c050f0d0b0f0a120b1306181101031a012d020c09060301050105030d11150403080106 74
    0x100c2d244000080c4d403640041c000202d16040400c44e00340140454030a44111040d000d00160700629150410303030b840c03440c1d404103004000c120702c591a00001c090801908640c55030740d5040701204440d100030001c90300100e15880c10003003500420131000e030082c400e6880301d01c910402043d02c080903d208840f0300c143c2c01c01355124182104402c1c0c4a0001d24981442c002d86601c0640c050102030100201704002013291819142d48400a03282c90ba07900c3c200172811900030b5080258151035019624803410b401e000420003c0c000d51810f5143e03035400585034161b03980350b402c8814400300e81400a80707100d061504036080c6064440c21807141a10681b1010032030f100513801101214090400c0d900105100288101150f026074260401c812840a812410f240d00e18007548039082089280c20250b807010007104050728041c0da44940c00801030b8000c2100b90301d040b002135510b00924007902e0512182407103c00c80810140501010540109044085400e0520340240312000901c140000500c80600d0265 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 592737149 1250 592735899 592735907
    0x61a180d12050c1605010503060d050708030a0906031d03180f06030108030702011b02010e012f060a11090303041a0c0a0515070201140106120f1104080f19150b1309030e01 75
    0x185e44069450f0350031952100140144148140702c180d40a114551001031511000c100070040d40740b031a40d03144011883e20384050709859200800419070b102d010005044100000140c41702c0c148014803100c2280d0401020401050a40c1030503500324100000215100d2000001403012500c02c0c0e8400700c2212550000f00c0c180859114002d002402070010b0202540c861400b142d21720b0705c10340d180302200d49030780803d035200c8040c2c24020720320380c0100c001c001c07024103035128019080400f6000740e494100e80100094a0784114016016042c42c03008840c2c103168984c0b0151100c040c1000f007112402140c2d82045035880c48404101a000d1401e02e00280c91640b041c080d4203000c0051410200007a404c200003640c0c4041030f940d10b104c0c040d9071481c2564081011f40150182142284100c0b6070b114100070a1509041c0020a5020285d00601e1394403140d5200716440480c0c980c00c03050a09602111045010240805c41845170340300b035050703032a030141c4240d5170b100c080388034866141c4885407a44080155 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 592738399 1250 592737149 592737193
    0x90d0819080c070206030a0f02071407050a0803030a0c111204030b130b070f02030f12040c06080f13210819061401050319061503061a180d12050c 64
    0x542c90300014080300e401410306401a50f041042410049482215280d01004a804c034903010399070f003030401d5580c0480e8082030102801414041d5a48e500d0103013007190850303407807102814003001140c0d40c402428856202c0d180b404d0b0500b2800083d00c001e0010040709098580243c0000d54000345040f01064901c80f0880c006100b183e84046400b009a99000c000d44039442c01e01c0305182503000810203150b5070411400200b68202105200d00041c0c2011309040c3e08a503040d40120041c0030300e200611850204503c50a540072221404041000c1201d152100401d09c110340fa0481c050340c00a146a00242c201960b14403600012203c0c2c1025600300e01c24a081d034025101b00f6400d990604003130841540f0480042da40148602121581400981c401700210345040d407068a2101080c40e40351a0b0a5040c002e040c000d200c211007140001240d0000e0791020b1040800840304002080a03900c00c03501d030f01c0200001d440d0000c0100c1400e8200410140c000d522503665070f0f04c0b6005001881c800094200840 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 592739649 1250 592738399 592738411
    0x71b05100f030f090b09011d0102250c0317180328030302041701020304030810080d0c21052113060509030403080d0f05061f080705090d081908 63
    0x14440c1c041019200b03400801d00304a440e20301c25202c60350080480c603c0c0603000d004e00d86110000491b540b9107003806150080840c100710389640108020700348c800800e40c180d100040b00e001c0120480781075103004240460203900c001c080c00f034582c820740030310102c2e607000c0c10320300e90b414410045ea40a0401050340707403441c46141002a48802c56a8112206e002c828400324510a04005161580720310b0080031807048840c8110031783e90008100410158866241c0e900804031007840109541007000c140d03101d4460140207000c00c0b078991400c10900500340c0144650340d584060002944406041c02001640f0040012208440011a80000b084400c80107440f070500000c00350014031503551800041d007405030101381180300903c8048042034194004003215804040002401d0b1040064801921001082c0700e205106070f848208204520100c10320507905140303098403c564070003100761060302032001002e4100c40d016002c0d00c1007001c05c4c4000d0007111503481859a44021409044074104011645 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 592740899 1250 592739649 592739657
    0x3020312010b0a230408151f0e06060304031b0b060a06020a030512060105071509030905040501051e041506170c160312060b0d1a0103050606090d050f03071b0510 71
    0x7030b840300752482c042c070200030f140d0800b04c0c0d51409583d040400e00c1c041100c2442d00032940110140002040382000c01c2025190a4160b40315051520b01c0c0c08070004030040400c0e014503c000b000070b04040c4518401d100f00c0c00003200d150004072190800412a41040316143d00a01c60a0404600d241c00080c0c1d04400c00d9150f650385140c0500c80300968000c0001601087c140a0184110300000e00342c200389450307140031810002070101040c1002050140c0c1603100c140a0752a08006000a880300c1501c46400b50301c8080c0840c5101d4200c0221300284440000744050a6241a0100b01c1c00c1d4440d005c202179428540d00790000740c544007003000e010300c900c59542501d10018900785000074040d0f1000c41c3d50110700d92000510560303400a4400b20b500c500003141803903540d00200f03c0c404281290382050480207117800c0180d440c0003000703e056849407005545c0300c3c6903440c1d07071127041042c204403a06001c0300c404190703900d50300945032130304111080043c941c2001032038143c081808d083c10581c1026050555507 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 592742149 1250 592740899 592740917
    0xf08100605040203130609050f011e0506061903051e0106050424080f0907181e050910090f0c0b090a06030504030c0311340f0b04050f1c03020312010b0a 67
    0xe40d00c001003501f02004c41303460180e210601003405080c030411180c41d00041e101201040801005012034400504040c0300d10f03801d0021891040c03c024038510384140c035090008054454981303002034011072083e0300700061030410000c103c3c03c0d030280c050300846040903007602d6500b900361290701d03402d4100b10756103001488500010301010784014846420030300c8482902c02150300c07000c080020351701c181c0940c0754940d107030800c40c50401103e4114400094a030038003000710703003070103503070b05454200703c0c0c100482403a20b9078074803018004101880c0d24066480302c00d035075100b07680d4102c1e0f07082030304100d465500c124080c800c0095141d020380580351086074103a0310000740d0100e81d5030079070341c8152030101220bc030300c29031524854015480540d400b407510f0142204c280d1844956400354000e226401604588240c04820000b0503060f10954050310401c07281c0d0f5807130001507004220494000c040c1c100085421009950506801100425130703400c120701c46408681e00c2c3c0034908007501c0360041180010755184 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 592743399 1250 592742149 592742153
    0x2104080703050a120501060e1003140f060f0d050606010e0907050703141213120203040f05151c050f131211010b0a1818080406080606040f0810060504020313 69
    0x20003480706038628208403100c04e007110280000c440003604a0b201203038010708006130030300d0034282407030350420a0b1a05005980600c81e2103000600043d01d01c0c51003403007107800701c1c85c80c0d503403015148082c01003d400b442031503a090411596901c0c09803030407400709046903010070180c103203500e490b03104083ca80c40d080c2c40e2404076902104c889501d5007410740d890720f05000c0b11586610082d010b500603062190600f600070060705084c03441c03e071442d41c51019507101300000c01c44031400c8000c2c5c0c402ca44040300d00c6018030864500e00b2030f10344038a100c5528580c40090040c4034200d119805180581001001c0d5600c1e42e8403d0800c440d4100c80080c003901100980706506895485000c840d80e540b00c2510000ca003c5060030003003164568590006e003c540b0340d0002e05400d0b141c1718450620642840d100b81d03010b00d103844d150300c1003030300c50740c010401002260340004040b07480c1c40040700e0042c038102d1243c910031591004403a886062003c84901070070f0601400160602c0c0074001d8900075519544101c0b030001580e = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 592744649 1250 592743399 592743407
    0x80c011e0c0c0f08031e090c01080601020c0102070e0612120705010e281704060203070302061302010e06180619030b010206061c0203010906020c070f0b19110102070f082104080703 79
    0x81000342c031b91040e0080d0741407580700142e410380900b40d0301c0c001b46103c801c080005040031400038449411076114100c940f043e680d00081c903004540c1b080c4400c0300076441d4040402c0484545212403141c5200305000080011401001410302c5405030000700017810800d50501c0d11128581e906041038100d061140181c02d00c03209948080ba441202032144000c02c00d00443c040d50002d60040e000360308046814810f2580600500d5440901c0c0010480e40307915a03400600880c2c01d1840c02400744d440840c902003480314100c000044008001c2a030b94540d01d030384485900312100310080100007030130100201c03141e500001d201030103420000c04030100d0702807941600c1d1040180e00416a4959202d20526012443c0c41c4018419102000080d10b0058148840c1d08004802c5500403041101c0400906c00030a5280101d6400da49062500800f81c002c2ca51000b03000e8010100701400c0c0d40a8610000100445034005040030640d81c0c440789081c40c081107881c0ba0030f20089a0282c11a82c0030030040b4006845 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 592745899 1250 592744649 592744651
    0xc0706081f1403011535072d0f09110a0927020f12090a082a1501060e0f0f130621061a100c080c011e0c0c0f0803 50
    0x102074000903500100309107848000525500881d0741030b100348041c07040c214410155404071b1604c2c101d40704030340319201a05961404a4418190700881d074108260032100714841c908245030080c2e000515194540000041c0400544200a1401d29000c0d902d20201c400c0003e83d8451105178460340b517030700c0ca01540107000e25401010140c00c0c4085000c103d00c04001361001d40600128407000b40c0e100c2c100c000010a42c664083c209040c15409202e070300700021a000300312810800d41844000c00e04d45601c4120251107031303160265a0f50300590043c03040d4000034100e0742c3d0480d0001e5035000c0c040031140c82131110304400350301403680001d650b101041c4d150800300750606002c5001c0c24001220b07030392060801040e200401c168201c00b0003102c02c0c0000d03c031840c050400a807016038060350f02114008000b440f1501c0324074200d8240610000c51100b8405504145c43d03100c0b001100a2050f8290404d501915078929045006078605e0000d25030000da00c214004102903911080e0380540359519211000c440d00 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 592747149 1250 592745899 592745939
    0x9030616120b031908040b0f030604060e090307110a0f0315060f0609170c030a0c030512030709091a06031801110c1e070b0708040302010e0108060f10140c0706081f 72
    0x10100000a507d0005c40c0081c031a26100700074903512401c0c60400c0005680310b0b035112848a004150500181100100448000a6208020b08811003204001c0b41c40c4040390b502c0003045d01d080c40300000c1840720b00085020300d0310300d2003c20085280c4486000c1d2156445014003000242504402d1007114440d500030000f901c00202103d8840f003038800028640a901d940440741880342d00420000c0100030482c102041c0410080e20b411886d004000904410051190802d02902c80b001c040c1d0030360600d41c050031b100d18043d000c3c960320b152100750501811550181d400c0b041d868001c59041010390842a1903a24071950007910091380103022045c0c3d11118020b554146024580700080c130f60402400800c0c5103885a402a0307140d61440c0000340a00d031032541034606206001e4100686580d0312450b0b0740401008480000c17842600c40400c40d802c0300384603110403602c0000a440440341900054404c00c0314403c0c0e0700e000c213580ea25641c2e0031440d100d00b50f501c18407010300ca8007404ac07504502201c4105d14 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 592748399 1250 592747149 592747163
    0x903140702030f01091101090905060f0f0103150303110c010e060d09020a0b070f060c030e0d030c0e04060b0301050a0b1602100e190e010906030203030304060b010509030616120b0319 80
    0x841c0301c3c9192421100041012110030b44482c030f26a5040d40c01c012031750300400da04c5000700014a07180e0041850310500507925031003a80ea01b0b114400d41ea010360300540841d51042e94031700302c494480c0307800780526a0b2001d05407a035102e0030424620b01d601c140030701a1206405010203081007002d200360405854084801c0368842014030b030104192121902500549020360700302141300c282820704608840c560030080c810541059581035841c1000074400404004030b1400151441c0d80042c12034504d00243e0595910505141c000611400e24030042c5060740c90440f40c2000342030b5214a00b220a114400c024151003004201c000003518040b002103140088904055261150400014818040703200007030032402c282500a11a5203024440a0f000d0f00f001d01c03040054504540019030b0701d00001304000d01075a21150340c0c3d44264800e1043e2207200c2c030042c0850380b035820b003140700c04209255038550030005510b080c90030b40441014002c8082040010b0041c0030100c20214904001d4403c80f0780644201d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 592749649 1250 592748399 592748413
    0x5150603011d010f0f1404020114161b0501080103030c0803040309090504032006010b041403010204050d1202190b0c160503031602060a05041101051c05010f031104090314070203 78
    0x2041c0202840b81e0500140001100e00300441c10000700c40d0700300120704002e0710344019907543d004203100c1183c01c0f0b50242000074031051400002c0b100c910a02400340411941600a40c0c10044ca41e1075895690000580303448806844100440310203000b40f1014001403034901d07120011505030f40080d504140a40340100b101501c1c0d14114081d5041038804030005505603081514502589940e04034100d003400103007a86524014841c0303803900450080c20000013202e0390142c0c2c2075a00b54102d43c002c00d006030400189059908007410400c0c15a007500015000b292001c11a40c0d4451001c1410298410151191620ba038030109001c2d230011071042d02c41c441d5184481d8041a000c001075403141d180c0f03034034510703003001031402c000d080040281426001341c2c01c190901000641c2c41c8610001000300b0318000d520f407180d419816040043d100307000d60201d032502c00045802003030541d402c420b4078010a410800c01c0c210030b00b400304956002c2000740016104810f1040c600c070411b0000c0c07103001d000904859003 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 592750899 1250 592749649 592749671
    0xa020705040c05030411151b07031401090312110a050f1b07080727050907030b0106080703060b09030a0201050901110619051f050105030406060b0c07210515060301 72
    0xc590306030001c0c0c2d02051001c001c003c20002c00307007014204003005403104c0d0a0150b440036100d504d03020f005240b072031a403070b201c458200386242081100c0085030094042d00105079901d919174000c0c100110182c00081e544804810310b06400e000360300920041c107034071074036101c80d003c3c04403002c0d0030000305440d0041040144000c041c09444408070202420006014840c0c94041300350320304a4030340e101c1c0303081d54281000e840c0700d100050440200600030040100703465584004007418141076400040000203103100102e9416400038945100301106c0e203040001c142c4804034018240a240c2e485075156200c41030309401540310351702a02c11030b441810815000300b0300b0500c1c5400c100e400c0ba24048000d00014480c52407005a006140c2c2048003001c820380c248a070b04214404080315406410f0502034004041b030200415584101b000748400000141c842d0b16100026448101034460104481e1070103d9000495000b8901400311079071050051a8a5440300c54103101104010501603143d540d5020440ea = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 592752149 1250 592750899 592750901
    0x30c06121107240b06030609060a050306040302030c01110435010906200304051c26070e06040b0412060905030a050703030501080105060105090d020307170c04050c030c07080a02070504 81
    0xd00b540c03103090314070b0702c2d18000d86141c9900580010084a402c1c2008903084140e1520f4085a80208040d03950418a03501c10011400c4410301758003a035011b104074400c100c240341e4040050300701c20030351034002d00840380d0340740b41c01104d8000c038015828034004082c24040f260029800d040f075044030045d030070401071040302d4402c0c3c03c5460384030381039071440d49401680d05c041d2100340d07036000000c125480b118118109501c410b6034451000703c52034414001c400d000960140900c15504861030b0040695100d00c1d82140312000e036000a580300720200c1c4482c8042c25445c42c100083e40c040c2c507868000300b4103040c074220101184074020075003076440c47d54074003800000c150103000600303c04c0d200792103866840c90306142c010103c0390140d0140446074501018044c0c0daa9002c001c59803411011115103d1001d00d0340002810103100394401406100c2d012419040c0e0072000c0f414141c000e004039400c02083d43ca95220707000c144011605285d1586d41000508001600c3c03801426a2800b2841207502941d180c0b40410 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 592753399 1250 592752149 592752157
    0x2010e03101401080303040c1203140d0905150f150604080a06020415140306063001090f09020f06071b080a060c030207030906080903120a0903090f030c061211 70
    0x600c100742c440149400034040c5031402030042900d04000d510b1480e042d218003100315401c0c000d03501803c3e0380f0713a03160007407501c80d40c58282c042c1c01031041155910f503902c02d074500501c981c180031602c40c003c0d82d0030084c0e601034141c04c070f84c4580c0f18484504090ba0300c2074284503504148280c002c0d481f4206200204520104100384c4c03644512418005940d01c2c20802d562042001c0d401103d01040f02800040304108000c20907a0b4000000352000f0b82c803405e034140f002c841111031040c2e500310300c0b003104403298070f04900ca190b090494480c450108030950007036040c0f80590390145006034000e803809030762080c1c908056000307004070341c0120100000548054501408000d0545c0595507560180c50543e003800800e00c0360724030700b1030070f4181140346c00307442d640242245c462031044600b4090200001030103a103052044810b85584207841c081070b0314000ca51540144a0034a00b0340000c1d40c80900440e96141007000b00040d05e4100040d0b10fa031600d4080c00311a603c00388006183e005480d00c81000e00124a08050 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 592754649 1250 592753399 592753423
    0x4021e0402160c09110304030914040f0c02070905060a05031906090f0303060501092304050411060703030603171612051b0d02060f060d060906110f133002010e03 71
    0x3c4100d10301c1d0000c028255050706460210881c000c000b4400041c0c0c1050401c4212000003142d1011201c1c0c04002400900c1005403590085040c80042c9a280e80d0218551064942d154401c0045440e95400c2c800c02d0b084a004650b05607100301c03090b02214100004554081e0700c903a03004141e20748141c0e81c1c0d01044406601c00c40c003217500c40b60207200f1907030401000005020039040c01e40c030a08604111860500307036800081d00803959035003c50140581101101e5000001031710031541c880c2e85140050040a45100c2512034008400710290340030112022078085c03001103480001800c1745130700d44a100301800304954060117401c0081e80104031114850700340444401018000f0702c6113645001e07092800040102d20740c21540401c1100c183e942d8190709000d1794108074001800b401901c2c2000c0204100c0210a0a042e0b01003601410100d030003000306100410f11b4160440c4542c1e03a040711301602000040341202406800140e9040c0b140901540700040c01450301d0506039803400f0205c0c1c2000010004 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 592755899 1250 592754649 592754663
    0x80d14041707141801030f14071e05060403030e1c05061005040c090305060712060803040b0901020f010605030312061906050a0f020a110907111b040c030504021e040216 74
    0x304110000f641c9941a400300075103100503070900318030f101c80caa030b00b050000070003c40c003004c0e0200911040f8480313207140503032140c02c983c00030703413500c8419000b07154000c04055040f0750301c1f2001c12a810040155400c0382d1b0b040d1a03581500755540200048409512019480240c10000c4900858020003a8502030780034030298284040c2000103000a86100350000401d01484542c200002040003c17520f52010a41c601308082950895a84024126a0b48508841c2c030011802085000b0110014150700000360200c8242d60100228035090b6902403159940c5a0414441c03400802d41c5060182e52050300204031000160040b40340000f5012150003d80c0003407070105144410982120701d50380514110300040c6005422030750303840b07948800300f03074210301850b41071001c1070100d4010303090040404808419a42490300a00d44080c143e142d100307860b44140e05100c04184880d010340301e85030007550042c0c4085481000d03054506e604243c001c9500350066401c0003211000c0510741c120030040307441090 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 592757149 1250 592755899 592755913
    0xb0405012c12100f0605102d051209010501030b09070e1b04050a08030901030f020408030922060306230609040609020d1202060403090f080d140417 65
    0x4001441e10600300640800d0110208410082a0309003a4803403220404441c0000000c84110002d0305040e0325001400c0c0035418600d84e0070700701c039058026800f03840054800080d601a0351034100c58000b4841c60031080d07181c85804a608030b0603980310b001101951801e00510b00304100e005506e02101c116002203450b5502c80c0144100044042095000002c120041034082d040004000310400040c1c00d01c038041009041070006031800ca41a5001028010110102141c0d544c43d40340c0c59602c00810140080d16094a075185d00c134182c401e5506680158000f18103150a60041c00300583c0b0007040985500e080c0b88890911403061f00962019503c51840450200300e4102d2900088084030740403010082440c0030000d45403100108140d210b0b400c80c20110b4400c135140080b6540b1420740c0c40180550306a80c1106a409400191650040784a60b44000519644511a21001d282c5024070081900065070609000d4400c80500881c4100c00708a24039155075012484036501da00c01084031140c011310 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 592758399 1250 592757149 592757159
    0x30f190c0209190b030721140a081b031201030312200a03060b04060f140c0d1e020f030d0903020709150608010b03072114190b01140a050901180b04 65
    0x20007160302c0030400717030f0007070014074106404491044a000c44803204002c0700110b03031092062000301d41c005235041405407100c201e0641040c0c0742e564400c0e040454902c3e8038810401407104004222809007400505200882c0d00395a4112540b000c5062110300081c0c480085c0b80c8810001110880c00040ba5110107507a96484c0c02c025041e5803041c0d1028800040c01d110401002c3e4220743c000c503080040b864480c0001554a100e806e00f4000d255104116219081d2407000680c0c228014441c2d01d41c1840f10000d0814000c0c1c1c04a07039820454256036001d800900204400e410140c120000c03440c401e0060b108a561260341c0d03a41181c6640050004010340c1c60001c200c0741d50051205d6015000d490b820624603e4254005041140044584616500442e650500c614010b0f440032810000070280d200b0981408000302145078071240941d00020b02d048500e68a5600130b0101c4540c40c161440054248400503009a503540c1094600303905101c0c0341e5140c4444480b03400140030203003210000640d1178038100 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 592759649 1250 592758399 592758401
    0x2d041b150e12030d020a02070e040302030310080f0c21010e0c21031903060e07030e01110408060c0306010e101107060c02010c0b06150d061502030f190c020919 70
    0x1942014050700342c0c1e8502e00c030500030100c1242c1c0c003421415805139545a070008103d2521416500c81d248680f0000184010140d001c0300441c0a030488000381090030781c48042c0640c80d0b5141d22000c03406944000035030402e80c1060718000000c0700d10b4111200020555000050a403810584504400e82200128041a11300000304100c404107240d2090180040c04a500d540d130f1207980301c102e503401c02d04c06281050381d100c0d0304058050080103480061a0a00180280151211464100040d4201040079034520612400e4908960594004100e01d07100c6002d0022554406026a170402c1105030803c036040d2241108404801100c0c0da84441c4044400525401d001042d0042c0003000000780b00140542e03800950340e05c0043d0000c8554030b2644500d8005031042100c08802080d80c0c1c000f0542c007880808a83c00b03202110320508144e1088241c14100700d849114014588010740f0040c40410140310a07103130070014001060401c044195559000521080030071039a40303a49400300c1881890b002c1170b07 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 592760899 1250 592759649 592759667
    0x180f0b070206090712061e0504030f080c0901110f19110f0108010b0c0c0405150901121a09010209030114041b06021b0a09150e2d041b15 60
    0x14501c05000d01c1d00389a40b031680c03561450f20882c002c0e0041d80f40319400740013855101000001120580b440c140da0900300c140d02600d13080740c0960100321a54005d041150041081f02d12901c4400051450040c0ca2001580d0003890313400c00d02d4140c8611112201c0e0070364100452103140000c00c10300781c070b10105440c0c156501031407152018042c1544010b40740050340c01c4903840b07054a852610041e1911701a40308036142800c11460603500504100c140500031ba00300711168034401003074a4500840c0e0305d40714106c0744030000c0031000b0031600103005203c50224541031101d0700068800700161510310044000307400e594007090b40c0705103110044103000c100503075811448030558041e645c1c00b9810740707440c40213901e07111240422400c007004501c0f110703101d90700d0340d0410000c2d11041070708108400402034100ca03030f40101e00a0180c3d0881c2c42001c40c0e40c002c0300d600740e150507601040740441c451440828100c0500800f5000301c691081d0041d09484001c0c110f042403001c1c21140c050310b102102d030380c50000c0c11000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 592762149 1250 592760899 592760911
    0x10906150f0e060105181504061805060f0a020a08070b150306190b030703020619090605270607020612040605060f030a06230702010213050f100e04180f0b 68
    0x10165004200c2802200c11050344034400f405c00d02d0b2544001101c1a4211179009000c0b42d008500361804040c5000d400c0c00780003511000d40e541035254414204085c14003072180901948a441480614281d0301103c6c010a000205441a0342500c1d810795a4800c081c1c000c0d02003201c03540701a80812030164a2148008458601140144500e0800d07050805441065000100e815078444450b80300d907407410040300700295806800c081e6034091013343c00a061400d20710000000d451604005101c4e4400c0083c1c0d04c80d010103001c040e0314a081d103a8071203400c00c4000611030300814180040c4001da80c407034000d00342c2000803800001d400d2405145c02e40031100f009203454451403d040c003e12807034a0000d011035115074050000596150f01c04c4400200d5040c00d5403030401c0b41e00400c2046185030b8190060300180c0c0321301d2104420207444000b0443e0000d07003084940c1e040a410109891f10900c6011068800c0c02c020f00002102c20a61a150907000c002600c1039580e45025001c131780c1041354000665500c24 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 592763399 1250 592762149 592762169
    0xf03020a0b0705030406150e150301020f0406030e011a21010609061d0f070c08070204020f28050307050a05090409020a1d0f040b0612010e0a200102060403050d091401090615 76
    0x1078140452a0580c5502521090303c2d11741c010482c0c42709407000d604541c1d00034141c407225070300e40ea6910030040181c5074a02c0404180d50a04160b45c45994090810142c607503030042040032340020240010075441002030038400c047d0348410001405898a10800e03000c0e004580309000580154880c00c0003401c00075040d0416140c8030f000300124264406c0d143e00701168000041580d40f00c85000040190184011904c1c9203800041c03106985800b103400140c1c4507040c001c400e04100d51500f01a01c25020480c0c1c0580032420400c02c003103802d03105d5001481c800070010400142040d0750740102d4000650354000102d00c40518043c0c01c030512001d04056803161042142e00020702d09540c03144500200507110900801541031102d01c182000e4200079000a114022907125041c2400d02007140c004041c1041c03400d04c6800c1180c003040d480804c41d20711a03038142d26014a080d650048036401804089825039468194110f00707256a1828040c10b80130394003552000c0ba00a415801018060f11f41e82e02a02d245 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 592764649 1250 592763399 592763441
    0xc020c030304061409090a060f0611060604020a020a12030e0106090204180e030409180309080d081b0903010905010e0f1920040c0c2a030f03020a0b0705030406 70
    0x256800104841c103407102c9180014080c1050001d846031401160001d941c0040b110301007000300601e90b403001c0c00320b0301243d0080400b183d4903241554444c5403071100d1a01504808002031483c20150010320040d440d510454040c0c07412620780800c078a462802c2400000d840d80301c0100b2941090150784081c024091046261628180c205544581d0000c1052400c53b15010b0706180103030140250303402040d0165081c03010030031307840070500b81d540d070640d049011440d000404030b402d1000254406881e255a1174801d804d40f10f40303030303c040145d0310368103a01303815042000010010b4030203014003d0224800c04c00071400c5804900b000f0b0400030710408800c0c040e440035141c4c07464400144408100160004007004072040b404c8852003961108403685500f1500b03120240c0f0707000c1d034090204010b440c003582d0010340401c030418010100460b003441100c49022201000e00104541c00003411286100380111009802c1950f200c90184000300d07401d070042000842080148109c074050680e1800d0810448901c3c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 592765899 1250 592764649 592764673
    0x120604150b04060c0f021f1d0603190212090a1e030509040e0304080f060a06060206060d12050708040312180b0d0b06070204060e0f06030a08220801020f0414041404020d03051207090303030c02 84
    0xc0d9000080140190041541c12f0003030050781c950446d01d460b411140c40c0707219864041440359546c030003c0c0c0708441c9206136595119489101114800781b50f64150341d901d1500b0f0703807101080060700c6603650541903804200310025131110100721561052880710041c003010b10f03011914404440d100d601080940d0019000c01c0f50b555100c4090b44140c940c07040503440b407402440d20403134541c052107800800365107002801000340140b1815508440c41540c0c0c0358104008001810040398080d0b100381d450202003030102c0521540e180d00079002018000d0001414107030b841d000241074034090fa004890f5485142c003404030f42c40c08552007552152090700100526941580c80c01e06c60311410091180001d45482e144525084a680b03140080402400954440c417802d80d0034990307a030181c82a905040c14141245860b400c00d80103802000790b0302d4800200c1503560b03400f48080e01c140900c1c11001c115042080c140741008ca016010300074ae00a503901c0b0181e42c10f507d40a800ca640040e807031019580001c0d68084 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 592767149 1250 592765899 592765909
    0xf06030515041106071a0c0309010c090f0501140904020304060902090703021602040e190525120204090c030501060806040b0c0c0c0609040f02120604150b04060c0f021f1d 75
    0x10a00c5410b4544580c2c0f00c2090501c0405200000c0106c00c0a030042c00502c6046a500c5001d5809070481100070040812484070a646e021440d03c81c040701c0800d0b14008020b03660041d1024010f003500d01c40c2080c98059100000344c100c0e40211000c072162550b0311992419030400200c01c99002c0c0e000e040851810f82d80300c107031540b02800d07101c0091050740c49000003518144184124031200c0e4a0b605090800481403805507142c0c03041803a454603943c00c2060b00781d80407020110480c1120001e4400420f000c840d5028440900081c1750151035090320900000b0001d0800d204901c01402924064101400d00345000900c0e41c00c00b8201d412040010700581300070200c0442c155001480843e0032a41d06d08032803001c10054030071552010b0030340e8808a50103052444c0c07084181c1c404e003c05c440804c0300c0d911900303540b00310b83c24030b016140a110302400140030300ea00851081d80614090944000030402a41c0090000400c0840c4040081102004808015003182a003450317112703840301c0c1010803c071020202d0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 592768399 1250 592767149 592767173
    0x151201060306200f0904020d0921211802061b1002120703240303090f0906230102210915030702100f15060c030221030114030c040f0603051504 63
    0x100020701c00041d450f0860b40d450f412158101c034008e0707092003603035107a05081840d0b20400402c00100204600a500614400c00780245240c0c0150030681e06056100c046000505443c002c000c0803880b046c4069015a985030080d080c41b24181c8407015546000080c40740c202071601c0204110303d801440040b600e00d18125038076a002034030b803400107080c001d0302c0da807854a03000b0180e0700b14070300c2102c403030120034103910807405401c0d182c08a0038484a640e45031340f19400c4070342c0362180580703201d101881c0400c40a42548a21801c03141441120781000100390303010103003050550794508500b400103541a0a080102020340036510049006042d4030340040c01070f480c0d900b000c0000001c10340d14004415003c1e415400300d250026000c480c40d0f240c80c2c41e0b6101030f0018592560550141c40f44d9000c4600485040341d0703035005500002100e40c20740c0d1800f0401c040100c134040ea05a454040c480d8119001e4940d40f1035140003140041c0701040c61403031810805d003014011684100b600e0348407410400400d184000c40 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 592769649 1250 592768399 592768417
    0x30b0a0c081b0310090218030c06090d1e08030c18010201061a074209020319050102120903030105100305040c0b07080c01050109140f15010815120106030620 69
    0x21030303583da01d10b00c0204e883c5500380c01c80e407209031000c0b50b205030600182e9014070314128284e08460324080c030403041040718010403544540c0311040002c401d00292103451900711100e048030720382c072051199580c4c1d5000c6820803520000041004140b080ca0a80d1305202814081800e00007004600e0801540526001d0f00c0704403c8002c0e20001014810001c525280c045200c00d001030b941c101c1003074606024507040c000cbc800c0034569000303980010580c20891041e1031034a64000c00400d29200e045140d150710f00c03007896064840355030030700c034100c0e14106c03c00c060f40c814040c00001d143d81c0c0d810f000030030214070003007907006040502e0301d810880041c020000d81b40640c0c600d910815140c203140e2410b0f080c1881181d02409075942400000a018203c503040390840100200440c25299100340d00c14009950444000c2410150407000800d65400748844503007140050f24084114000d490209900860b001c0e02e9802c03d070741d22002001800100e21602038010141807170541c400100e50000b0318640501308035 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 592770899 1250 592769649 592769701
    0x1106030f0f1b04120204150f03030e0f1c0b09070e0a0f1d03070605011202010503060108190e0604050d031103040303020d0b04181205030705121f030b0a0c08 69
    0x300b5011408442900b61001c00b4421455440303807500311820008250040c100c0c01182080c1a59074220300c940f0020003507502107004943c00502d03549040b50500509450705130450b00c101101395680c1c8a859940701140010003854003180400d2402c1c0303011207402804c0e070f45a900100030030300803404204e51781d513040840c0c4500802d8400e411100c401c010134040d9080000c803c0d0360361407880380b00c0021001e0b0040c0ca003d104100126a610001c2c20700441005d04000e001880810024003158080e1418581140c04c0020004041c0080c1c61350008035201803102c00041e9122904120800c41d007000040c0ca204e01e10324003440140d105427404c51080c00044d100809254021607a42081c00c09030303004e5014030038010000c1c03008100e1069480c1d02c01004e12801e450130b203404040102c180b40601c04407030040c2002d0381c490346485402400c10300246005003128030f841207000c0d0558030800c0d08080d100c000d903004480000550604013080c1d030464143e400c400003171040340001c200340d00401e219203c001800c01c0380 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 592772149 1250 592770899 592770901
    0x1005070f360e070306050a09021605120408010b04141308210105041407020c040228050c070801050907060302180307060f020f0a2d1e1106030f0f 64
    0x800d01000c03801005542a1000042860410207401040c4020498600304911489510741c41011004d8a1490042d103800c404004c208011071801d95000f4000308851902405940c0f61580d41c0c3e44c20010b0303000350071708034000c01b140501c030b110400e124010701010116401c106011403403140052540d0010400b120018600c0d14010a100124040b60f881000c0c0c01c110810180c1c0d1400250464903083c09001d014610b8070301601c0303000a1120056010750744540080141e94010401c100c00313584542841c8079956002030080306660400d9218240380182c075100c0b01d4560b01100c400700c0c94122a03601801c100d0781403100307000381e038407012420380d081d50214a00503980d200b50840c0150070843c5540655094400c0c0400082c4480d480b01c08075102c042154203680c030f03a0301142a4159075409140000d80a00c045403e04d0b5024856007030500191300c20705441d5168400c040d101c1c1c0310400301c00000c00d0803c1002c050f8020401040a0300045450400c80e1002e096081c103480700e56221500070850252a00100 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 592773399 1250 592772149 592772177
    0xb031005060d210f080708011707050a090f050916030f03110a03020a020406090c05031303030e07060c120c0b040b04020109080a05070f0602030a0f0302070305041809051005070f 78
    0x4012440b8150052090305603861000384449400189036100e4001032541c0c9285400e507032288000a0040e0140e83c0d4050082e400c0078283d031090310603050f003c5860300c41c2100005980d250135800400900f60060001070300072403126a04291400105141651703041413084524801581c422642607e40010300380403154100d180075564042030f4100841d20384640b0068030b04040d80002c54401442c401c0c1e50500500b5640d80300745d020703900104480000700c0c8080c00040c154182e503107501c481d214000d00e13000c10282080c110403410907010b0f40003000040e0100c2007500a0024613055112100700b40e2a19011051031611008007091016100134072103451540824150b81c8142078100140c0900c0c42680c1107200545803040e5107008510500d9011000c01c24005100c5002109550750500c5d641c550441c81c445401b4218001e5100c200c0803030500c14240404546200c0310120011540032030b0a000852000b80e051003031508549036210030085040500304000b55504c900d80004003600360a080700851059 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 592774649 1250 592773399 592773409
    0x30a06151224121703060a03020f150424080f0c1b120702030c0a05010e130612031d0415090c0903050a050303010303082a0a030207060c030f0f0b03100506 68
    0x406600241d1140e2110101c0da44604035030b070204003442010742c1c030713841030145420342e486000403111541d000401420410240c100020382c071050440007410440e9191440d448070040381c2281c1c0120020445603a0200003065112504030052505403e00159510b000103c45c0140200144016182c80001c01c40d032b940c1c00001c450040d612039030002514081011000c048100790000c010a92092151441d40d202c40c1c00d00300350701b509940b0107139904003180c0c3c501003d00003580f404031444800b05556040c00a4044050f00c04c1c100c800c1d00ca03681d42101040c0900410800203150124030f48124501005c0c0c2c1d0041c1540d0007100704490400760017140b503054402c1f00b5500f508031640064181e0107940408020440c001c00214141c81c03203901e40740404c0c1c58070380d03d05507507200d101d0f203146078102d02d0710610101c0080c600140024800e186400741c50004a40c0e203c2d01600c070f0060130349011a0b21160110000801c5004a0383d0103041564200810000400066076130480385246016140d039400c0420115110 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 592775899 1250 592774649 592774691
    0x80f06131a010915050d0f06050402181513020c06160203040e191409120304110315010303030c020a08071403040b070b07080112050d1103041a030a061512 68
    0x8a9004841036944405002c09403008402c41100d01c114000b0201701403500041106031642c200700e514024040f1a5182002000091b0040e40d11808003034201a240e104c0b60500d52080d00c3c0108007000100c0820240103805da80801c8a0a00701d005100c604580d21000988540c01403400c100054183e0942c202642140b0558104001600500701044100c0088609090020462501c100449051500c141456a0041d2000800d80c0c00403031100d0704081400d009190000e000301001a04241301b071000074a0f10b00c01898401c00300803080010014190141300f0080e501d0142c1c009424a0032040c3c1d90a60548100100200004100c00990035001d0341042501c02424040e40c036070b55112542d050458210400300d420300c00081c103400000c603610600403501c800041d1301400410041480c031314269058202c2c12001d080c1444144000030701112544503410145500c048140d0f641d041000703400080d20341a41018800c1c801d8503544841707041e44030b1403810760301d40d15010005603500c01ca0749000d03a03058 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 592777149 1250 592775899 592775933
    0x40c08031303020a121203020f041502100e0c0a0e040c09020a05120114130903030e01050c1e0403081e040305150601022b030b040b0306040b04020109080f0613 70
    0x12011a445001c50001216a425640219800d101c40395032040284002c1c108a03038010000c5180c00c5804600314065005002901c09032041c00e030506844c0c030300c05007034009244024001684690000c034006a100d2044c010f13007443c104041c0c60001c1100d8040f0782e0b0203e80388900321a44009600180030300c00b03a10500c07805401d80304420341d520310051000400c035410140e44150380f050040d00001e6640407482415190700409010041c01c00d603d224081c0040103409001c0d0141350700ca900100c000c0800703110361803244000741101903c9000b00c112038182d140c401010351142c141304201c20700201e007000c0166520344220b5840c290031030307403203580c1d83c3c020703009640c07004166110704c1d41c400106500c0d45445921411080e0f00711028240d4881001650600340d10000e580e60001c19401c590440c820382140c54078810190004c9032030301112020a1a0000845d1b041d40e500c03071140240021581d0021098000b4840c00380206803007804031400a0f03c0cbc1a0140000304d00c2006a01e001c01005044400204228 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 592778399 1250 592777149 592777153
    0xd02010e0d02040f0c08040c06110a020f04090501110c0f030909060f120a1212051303110304120f020907080717040c092301080d080f06040e060c250515040c08 70
    0x212040e017000d003003880c0c1070b101201e4942030b40e100030a4041c4148990408261541c0080650705c81036000c0c02650846200150f410507254a02d02000c540709000b100720b114004129a903450918200283c2810b0760b55039104a290001c002070072251350b402901d240c003d0030445407003880c407111400050100101c4140e00b010340c0207039680c01c003e000384800b140d45903500384c1e1a01c03e4207035080441c820813181c080b1200e111200b8104c4030718000c80d2241c009145400d01c11011240740a0301ca007804008120700c0c06089500058219038903046007441055603411800d0307403d00035010305044d44040d007036550511034002820008070004061040b0241e0701c10003820903a13800c10480e50300ca4200540700008003042c902d1800120000030309280000b1b240380c101e24030340d520811141c503040b440e01414000900300e641e0080d00d0301403000d518101806004d000d810015035859039800d00d00d41107103030250703240d001103d44440300c443c110101d0400b05041d0240050300007521410b0b80c407403510240644041e0020302f0f641c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 592779649 1250 592778399 592778411
    0xc06050c0c190b0601080402060d1a0a1212080621010914010509011505130228170f0c04062708240705190e09130605060d02010e0d02040f 61
    0x10401c8030701040d140b14003c0180240035070b108030042d5044901510000e40054040000c0f030380034881d075070083c804000148490784144841d040000e0510207190400c101c0c100b01ca403101e13010031801281003880981542090f0307503649080710006e01540c115809603400007001c1481d403080da51081d03111070700e0030390320000424845800340601d90007400c049403065000d6180019181c52080c41100c50022100c005001c1007218250404a401a4201131640a5002103040d038401444206c1080c2c45078408546da00d03100341c1d803000200400e160702e014010001c550401d5060284800e030b56012034080c0d80342c078103180d00070f00700035805225504c000c1e00c2c0180254140c844040f99007040800c03220b91649035421103030280200d051049190794002d5070b03500042542001008440c030420f40302641d0070107803400d100743ca08003e4004606052030407101001040e20403c0800c0400080d0320405030400019210008042c4195002030000f82030500c81a206098111540003191380f250042e03203070104a000c041c405 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 592780899 1250 592779649 592779673
    0x140f0c010510050906040e0c0103150f03050610060804080a0f0e1f02010f021206090907080105040803250c080f070f05010525020705011412190c020109030c06050c0c 73
    0x12901030b003d024802c40380071012841a00e80f0780181c41c600185d40000d0b107009220300e4010b500503c80d03800820502d0200e031038005405000d40380d80030021809034000d80345c186400030000340d200c0d400750024820720120700300340808503400e00155818810241805211407640b4801600ea01042174001940040c05441150395001d0007011110305130410b80003800350148094614043e40180c003c0d0f81035451804001403d42d242c2040c0d0180c1000300c05054a459035110446a400d54034201d406582c01d010000500200b03542e42081020035140988118126210040006001c00382d851400f42c4410800300b08a0700801e0f40c001200e01407940a400c1c0314010a0300c0c68214044c2030704442201074142c00d210018060b00c03948802c24540c0081d58080d0201c2824100150341961240c070300390700f04400c107000e2003034500c0c0500720031801518035407060181c0403801d1000c001a1040c5034250802c42e41040b03d118000798200515403852980210b010070f150381c0f1054010154010302c142c107050b5210350020703000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 592782149 1250 592780899 592780921
    0x8040311010c120c0201061a070201090e04080a0e060403150c02011503051506061c1a060414030c060a020d051b01050c030a051f0e0619060905011e140f0c0105 70
    0x100684032031009110113070074860160b00300c03030040c0f03e07501024550003015402080d0701350060032214414101811469290130141c0203540080f034040b41c492500180401c055500841442003034441202d4a929240c15543c569201c440044200301e0300e00d0711844001c080e00e0003074008080b45c02e00329160741e0502c0e5485c180165035681d212610078480388010042060390802c07004554030540d8111400010310300445c1100d0090000c241200354482642403105820350303400005000500c6180070720381d240d45403d0105402e11a0303440c00548290401c0103100401a00446d0420289070a41411034440c0e001e10361034039182842100f003d00d154030b003504002c000c0d48001c000d503004000540c4201714640c3da450b07403003100205039a2707200c0407000254010409560340c8116294003e6028000305e0860080d012268005d521940254000c0b4004100600035541d00034444042030b140704000300c0d15141020b1016180d40d00d012460000000001140058440700b0400c0381c1c01114440001c01031071508000004d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 592783399 1250 592782149 592782167
    0xc060f04170714310504030f030e100b150408010c020706050a020a0b0406180606090b010203030112031b0b101802030f0c031b0403060903080108120a08040311010c 72
    0x404810740c20111414014400140d400a4503401c020400791030107103008014038121540100d00c10700f150208000e00007280908480301c09500041e003c80c0780e06061801a12007d2510140300406103044c80d118601c100000d45642400c1011a00180441c5103c021a400c0380300710750750b8a22081c000800152010056014a9180c80241c0c01d0305e400c1074079690100e0b100e00c0303801c4034000141d1041e00b2440100d101d80c3d1400750403600c582400901d20340d154860b0800d0b11803612042e660306607511010404e000443c000c08412620920280d8910360400185101000c4a0103000d820803191020611141d00e03880550075000703400881c04c901e40c1c5814501e0350703264800b9000b00314010001d40c4c0d404100c280c1074003d4901481c040c82c0c07030b0f60a96481c141d41d4011500010022041c400320384446004521007080240f000d14082c03600405c0c1c00c03000e41000740c0340c000b041c0d00c100c20f5944a17140c40201c0d0340840c01558904074040c41d2144890703c480c1021602c03910110403150095180070607400e49540c00000d84 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 592784649 1250 592783399 592783409
    0x8070c030501230a0c12151e0b030c0705030702032a011d010e0102190516120503040308071115130f1811070b07050301360e0c060f04 59
    0x922103003e400310042c10700c1540030140711421118002080954100c0e42000041c0c040034034040b640901401c0001060b0340403d41801148030380d1910a11000c48503015001112403c00107040001d031030078500d100541710017041e081d1140800f040303081c104070080c0102c2303001540080807940320b5480040303d041c0107600c808140480d18448800904a940680706020042490440305185503203090015650300e1100300406045006108007000b55141008110440d80e0041008110384541c0040c0591216580e8100103020344401c4941d40c00594000100c900380c0307600202c82515910f0a1804d6064002e010070641e9000d00360002049403c205040588404280721142c1501d0b40d6a8114807034840c0058003502c6072509284a01d003490420b99044002400900382c502d61030400341e601e0f501585441624400c0c006000040100300420384528002d00410072194003080c03110800014034008a0703824100c7c0d40064440a481c1c14002051040b9101400007a10185c0d6540e01e1800311310682d4854015 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 592785899 1250 592784649 592784651
    0x3230405100b0904030804020108091c05040603051803040515090a03060509060f060f010c080705010f02090315010f030609020619080703180c0303180807062313031e08070c030501 79
    0x300c032114980243c682e0301454150721441e043e500c0b580c0045a641c074000f401e03100580b044403101150240001618007440c000c540d2007548030f40c1403100050603288080c00e035404180101060304200d01001c0203c0d811100200c5080c070091414080a80c9180681071040358020400400041071224540200e882008000203403183c90380c4005030980c070408191040c40d0040d14540380802c50354098910358218034044c01038142405215a0b1740c0b400d5454a1100d0f0452903004a2074221508041080e842003c00027070200c4550340c18194a15a90320191002500058581d80d445082d51a000110b5002071045175000c0100c6104c0740000e020200107550b0070001a00e0184020218a8860074448440303a00080b5a01014a1602d08482045650102101e810082d01c00040d0180013000040c0050040b0b031038610001b003c01c00810302010044070f0401a0791030800c0b813500282d82072000e00d80fc7e13076448a03800030500310f1030380113282d40545850018190701c3c0014100d000d2081d6088180200c0741b180f00 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 592787149 1250 592785899 592785911
    0xd0b010c1505191a01080c16050a0302162d0306290d030903060b011707091a18010f0e04020a05030a0c0504050312071e061e050709060323040510 64
    0x81c0b10b004943c0c0c03400b451a01089084000da81c4c56104504c50b0707401001842c402802c2682d4001d070090305140510007107881d40d00400c800001c240e014010174203104217600e00604260b181c00b400d5540710f50080341650310b08455101d4141c030202c545004501031a0899070400c0317620400e500047c8641d0b440c280c0c02924004200a803407180ca404208604899819a1203900492660317803490042d04000800d541440b0070030783c02e240388107000c041592245460f1399885010328941020001040014030200c40c2c0c0d000204050310140790a2100819091003c1ca808000400d08940441d6100c1c0040031103503010380006180085154007002850150744046070400a080480400b41c805109d20704c140c58254000042d07000f040104003010f00a00c6005481d80e250703062644140d00000340d1410000c4522554034034147e441011040b042c44040048441c040100341403100c00a00210311070f120340706c20152140c100d2807540c01c08a000100083c0704492001c02400c2500d000c81c2c407902c8a40d036020300545001c1c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 592788399 1250 592787149 592787191
    0x1120f0b09092103061c030f031b200f071202030715090302060c01090c06120b09060918100c0203190c020105040302210604210c02060d0b010c1505 65
    0x220b8180801c800c00d541c9000703220001d4a041016030401800c450748801076a40c110b0116146c226828945c600c00d6680c02a403544150000c1d044410f01c0b00303585283d403001c00d114000d99410031000f41c81000d210089151020380c64011520b0400e00c450440600e0181c0240010b4003040d0f0190712040903c21010b07200469103c3c4502100202c008000400040002c40100003601f0450024041d00b00c03280300100389003031161a2490382d80425840180014400d0844044904251041c041e81200c1110400d40a09020002998103030002d40040829140120700c0110345e6801c20090030b200c3e1084200380245460100060740329040340d9250fa40480004000503003a0307200c0d102c100001b9034141c4030203042a04640910200c0704240382c40d0300d10000b18159403521090100111407140c0e104000540005503000800480010503004003002d00420b46000f20060740c88500b610820740c00b0080000d894064400101c946003d100c00103001003619040d80245042c0607040707144125000c04499443c14409 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 592789649 1250 592788399 592788403
    0x1b0a08150c030408210106030b09040210080604060504090f14070b0f09010e03030d06051e0d081806041502070b030c0a0c030e061c0c020303190b01120f0b0909 70
    0x14090665000c0110030000c0c00941c244006140c20601581d40e4900b0183c04401143e07182002189808101911000400c052580760081c0780d12031030262440c80c01d0303080942c0400c0601c1e000050503000d010210b400940d040c1c95070f070300c5031005090051050140248500708406e0784001040c082d01c2007561803844a085010009500c000c40d499460050b1034041c40d820300303a5140c0c0100040f40d0400481c40035032070180d40c0c100f02621001c0d040c40300002e219883c06080202081c9580d5603480c004030010400da285596114141404030340010505603980300942d111945101d00400c0e25034030080c08a0302054586c0410a90303100301c03c02d50221994203480d0000c41d00140030844602c0005242007050036202c0e8811000c0081042c031a09061601d2121040061a1a00304000d20a0612030601c4800301c6002140114080340d0440c3c00a14a1401c2810150b019112004400446c0b82e8232000880c006901c102151011140764140802c107420070110b11001500b031003040b0500c20703031703100700454000080 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 592790899 1250 592789649 592789663
    0xa2a031e0e1e0a1e0b070519020706050a12060312080f09060c0703050a11120706060e070816050c060a0204241d010219080903060a05010b090603040f051b0a08 70
    0x60790004110450b02a41d80b0021302c5014100100002040b03600715002a0301009118045d40e2251605c54684640f581a00700585001c4004001c5500894003005060740080807a00382c0d01e07243c949424182c0c0074907004809004242d00c020107100f01c103a401c600326a84940454020700d0a818001d1164a507a0200c51ba940400c0e2040c1c04072000c100101d80000740a60018805402e69007425410007101c0b0020500344042c04a001c440c2280002d4a00200310040c81020007410501c03200600d24102010018018800140301c8950700c125036000c680342d5401001070b150140081000c84e4198505800d00a0280d0001c0c8160055034aa48400341140d0140c2e240401c0c040c29144d032040c0b410758540e42d5126185602500a50642c0105645514079a1000550b405802c0c01000c0459940c1644401e00d8034059000f8020700324a8a0b100c0180000344400b4115400e03a00111400c0b900d90b2541e00300740f241d03105023180040c2248228410409502c003100842d01ea500e42c1215038024490340c0726001904c03000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 592792149 1250 592790899 592790953
    0x3070305040b1602040c090501020d0504080a1b0b130e0a0c0f080a0e0a080301150903030c02041a060705100f090506010306051f0806010e0a2a031e0e 66
    0x8001d200038024000280b01038500502000d840910401654000c9002c0340c0100350440c0016048840034441c95804020780007209110340f40c190f240500d0060150748600769440b005041640700b1a000c2500319224070382c040030742040607409030359009511b18203441681521881c500525000000b0707201c21b0705441244603072a180c3d01d8480504215207004c0fa4441001004620b2082c1c1c2c52007100c1800c0420041e00f04c00764170446210b9a25410310001c01c0031908003c0b2074000304104200140b001a52001c0a0820150b0582d0301081c003070031319880401c2d03a100d14800c80f03406c01c0001c40e00009112000403180daa41100394000c0055100440b1288251998501c028285a01050040002604552000307034050809920880600d52204001103d20302c02d07072050070690720010050260001c107200c60b40d04521040403c2040000d40007284804c00900303a1182da2104001e000504001e0007500a4842c004910148650350b910702402c000c0103190003135030400c8602c11444044080d0105500c203403120f003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 592793399 1250 592792149 592792157
    0x160225080f0303061c02090604090203011506170109060612111209010f0e0d090b1c110a02010c02030702010914130c0203120c09030705090702030904060e040326160504030f06050711030703 83
    0x580c450027804050502904126010341da08c40031221042490b824040260089a0b0f074103618008140c0c000c4c05403c4103070000300d0024600f91003006071a800019010b50101c00c682c000c92a10101101800b141c09420002c50140e4100c1c002c11440501c107500541c518400c50908201d02642c114201c0d96500c0a4906d140101e6080d00043c0b20548600003c2c000b01910100340310540004a865241920100e0302d0222110f040442c107100381980a0042c41440c00710fa20085040c5030443c0c000030300540c00d51281c43d80703080300c0001c68000ea448104050004081e1040107200940c44034400a540358030071040c0041000740e100109070100e110f13000701c4244140040080040c5414102000070041001d046041940700812848049803168066140140348080806030f0907e40750a01404040b0200c0103400c2d102d1180b45a00c11203662171040c1500090454a0301c4505082d401090301d5603c582d8001800d0340310100301c2041006103d07040031348940d1450f5242e05000003006003140d507d01030440024041 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 592794649 1250 592793399 592793401
    0x8070e09010e21130b040e1b09030c090429070f090305030a3606030f020307021b0a0801090605060103110c0a0201050a0c06140906160225080f0303061c0209 69
    0x3040840f00079141c010242078480f000c09036914003800140c1d100e6800201c0f00301006007000312044850088820010381c101055180164100000740c441c002080b586110300c80443c049000c1c07010a081005c0b031031040041c20402501c0c0740b4019040244101c50b04d4001441101480c1c1c1d90a01c182c80da002240c1d8408000c505186100000b9103c11804030901031200401c3c03403103414011042030403010602013000c0364009241c109580241500c0c244071012140c1801042406000c40e400500111400800d4429800d2084080000b450004c1c55502c06c3e200c56082090b02c03c140002c681c0654000c2609880403c004c4180d554591103600446c8580c1525401942c111400b65000e48000c060182e00e074501407201c440c031a980c01e8100c035012070000114600ca1010480000001c1080c144c11907122070303288c1c1d10714541c40c1000b0340d035800c3e46c20414020a0050a41c050300400c0c03503141c2c80503244007415a07100c18058490355540303400c1210303460b01c0b0318000b0003c1c0313840401074014404469000b419480392 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 592795899 1250 592794649 592794703
    0x11a0402030a0228020111040b0d1a0d05010b180103150213030f0f02100302041202010302091915020c010305010e060f0d0204051306060504051006080702030408070e09010e 76
    0x35000140950001602040034812291030410350700713a00340b91120107071101d100f040c0000742103480c0c01c52030010b42202080148030840c0038006540210303030b0306140803c48000c1a0001130003205002c100581004d4000d00c65000c00030190040c005201003622109122014481c910205880a10025244503803444884680810300c3e0014008165035240080a00d0b03030307076034400b00040c013400000e980050728545044114640030620b0b640b0712015280c00d40c18036084c8415101d0542c40c00000038145913002684101d0741c0c646005007003145072500e069240311955a5030482e13805c101d20303d041c4018014146a5007076903009100d4503041c0c984402c0051074503654031003031220052405580c0795020b10040c2560005175660b0040511600d0140c81d0b0034410000340c640074050320034542125108506100400c000201c603540740200302c421034602401daa80351020b081e41980700b15003200c0e05034018176401081c1a0580b04100703024050b820020030802c03458400840e00e0704040081113040c0e030403031140216 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 592797149 1250 592795899 592795901
    0x4050904021018181109061207020a0f060c0e090124020c0a080a05120f0d0c0e130b031e03030f04030c0b010f14010c021807050c013908060d151d0f011a04 68
    0xd2712150300c0c0102e84080b06162074a00c1c4a100c0040c3c00c0ba003a80d180d0440044490f131151440d04ea0100c1a40c0c03460b959410306103503800300c40407900c03d84a00e462011a82c020035100b0401381d00b52010240121350110740307440c0c40540303d0911040580c0c0074410740806410003000503080750030556094510f42d04100e42c4424000c043c001d151510320400101c29400c003015518a010466283c01600c000621410000c090504046a081280c98900c4941c0791b8001e010030040200c0e540407105480c1200076507036a2034140d504451032100078290b4449170740081004040e20506005440711118114017990040380116540e01407040c000750442200c44440160407602c07034065401001c5070030040e0900b034211118270308503000503601c403054010b2000700600d0b01115045440400300b50400154101c0c020f9480503100c40d10152440e070065107000c03a03460901044401491401c5030080d03086c410101c0c00c1c540040f001140c0c65205001d4016400320482000c01441010050a0590200003803080c0351003c00c4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 592798399 1250 592797149 592797151
    0x60c15130c090518010510080d0f0206010b1e1917130209190207050c1f171b0a0806010e030102041a030a0204080106030804150302040509040210181811090612 70
    0x1561950005503086420380301b8043c41c0d2040c0219001c1c0c4201c20b2400e564640340c800c00d081c0030810f01c050b503801e181c0030903404200e2078191006056500c0e0f8901c00700d080140602c01e10039072a191140b000ca10400740ba00000380550100303030b007030799603d290303410190440150b5581520840c118103004900d5800505000540c140d00c20030003594a11284040e207180c81c10781c0e000000446540e04801c481c0c160b6858a16400c01036000b0b8812420303000c6811110180c03c580d851000c90010082c80b0303001543c1d03000900101000c0c149040d101980b160a041c40c0072740300b054145c8201c0e0200d140c1100403151414140309440454183c05034141c442d11043c104042158000760003101071640030000810314003024010710004501c036413441d42c0d41e28a0210035040d000c0034641c2c01020140100020015613071810ba1b0150020b1b011180d100c0000c00310b60b41598004649000520500301c14200080d08044050f1803100c89005131a042c8440860112050308610541d0023840c0d2155041c0035004034a42190748907 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 592799649 1250 592798399 592798411
    0x106170402031513062a140415030501150c080904020f040f06050a120c140c0a0b011502010c051204111504080303061309050a03120209060c15130c0905 67
    0x142c1c000f19a800c0da218004103084554038a060480c500303601c1002094820b00404200030a6415000b0f01100c461102603005a2a0707502005103c5802980b00d42c503d03012603004000b221a5205c0c1e1840c1040090003500c0c007486140355025580034016000c0d80034130442034005900210703c500c1e009040301000000c0d0000c800c2c0c40b00603002030101003401101c0d01c24503009880203448050322102c45510040002841c2001d031a403003400c0010040529800c010764807050a1191030f10b07500e90500f01c21300381c5482a5850054481d070301c3c0d40c0c0001611051f01d00b80505001481c1e0080c800400918015221031007100140544c2c80e44c2e440024001c101840e00324015094010300000e142d242c0000c145110f900301d43c1010f40290400000e0002d14509520b40700b030000e8814806015490b040c0e01c2d02d903110010140302405101e2440840f890040070740e81150300310034000340303410703142c42c2c0321180e8650700c10030b078903131001c040e10b0b05004601d450060703289848480303500511841e442410103600c1c0c80540030103041 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 592800899 1250 592799649 592799653
    0x60306010b130b120f060d051005040f02100327080f030601140c070501081b0d05040305040f0e16050906072409140706050306031b0f0901030f11030303010617040203 73
    0x10108001e09114000c4c183c1e003502c80c1c652007442c00c202039440c0003003502070704441c4903841c2401d01900042c4045040100001418400a856941d0307080100500c10352403402544105034007845140e19405503c030603010140c1d08202c004040300740b550080c9011103008080d01041050180c1c40251080d400215840b80040c5006c2c1110112032561480c550003400300000d0a07001840c082c0895680714031f603030b0ba100400c06004031030703443c00c0c600c401164851343e0703005c41d4400d07150304c001030074580900c040394024070010410340c414555468844000f198241c83d800d0400c0186000c3d90038082c814810341e80510130040031280340040030782d44c050440480b1303403244c015584080000c0e0366043c514802e4070302541c01014140c404180356000b0908000140c1c00013014484240184249500c00140103003c04ca9031108681900c1d00190000e061014080b4005c0d9110315850004010803558030a50b01e034061007501c0500060b40c122080540341e01090003180002580c0820a10200920780d449035002400501 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 592802149 1250 592800899 592800937
    0xe030c070b0c1204240905100509180601090b07060e0601150f0815040b040608010f29030c01201b10020304210804090e010b0f0603060306010b 63
    0x2121410064240e10514a1200100ba040c1000704103200070201d03000f01850080c03900d410189041c5840109110764002105140042c0c2c40260240f200d41024120040000b03000d05140c0304000c007a43e021403052801210707001032100c0e08401920410340a08016111000f0481c241201450b21b03030414101a83c1960322202503842084c42030085e00c0c080c00c200030000903100c1240401621082402c14280200641a0100300610803911940384140320200d42c003085a80789a40010081c1400ba004407899528041000011002c1a885200030448100403c3c240600340404c84500d003820303600d21a01a00800145059903204100300160302c81c82d029114904003e6104407440e0410643c1c80194203510f15010640500e02200201c10170740040c80214075040c00c0c00c2110380404030094104032100c01c042c2402c010000880c06a4001e420303c80e0082202002030a00355004c0c1a50107840c0c0d0184140d5444c01c12941050b00807284140005002031110340d00c4c00d01c1495140e8800501d144190342510 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 592803399 1250 592802149 592802167
    0x201080417030103031701170c010e04020c0f030d0501050904120f0c1202101b0507020f06070213020306210c090901060b040608192d1103011e0e06010207090e03 71
    0x107805140a03600a0b51103509408104413940c54541040e04035100b01d00e0258400c03900f84200144d6404441c20030f2a1920013400d4010200f03029029100c0550614058820041d840103000805030a070440c4010007802131740d0740c403001d00075984020755003c0e051002c8540c1e041003581c0520550012849986450580d200098481100d0440b100041a0043e00312032990441864107025807030081890300000c090b400400c003009440d80c8078803c4024011600182d441c500350f5103030700990b203035560064007400d1501105d0283d4402076204030b40c2c151150f07854041051486803c1240e04120440301c00080c1030920703554040007008200180031212079903d40501080400040002e407004011a40340c40f141410041d0388080c0d00c400c100702c03406607146480c40d41071415400c80600b0084090b0f000100c80f0300d901d40c01002d4007400c45800820080d00c0c000000043c81c02c1a500c2d6120320908452141079015150050302215a8003a144c050040c0d1103228107204050a41c0d01c5190800d0100301105c1c5003903084 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 592804649 1250 592803399 592803443
    0x31c200a0624051302040f080a05070f0605040603052a09030f1c05030403030e03070f0b0702010b06180a030203100b1002060c030f0a090204060b03061801050d02010804 74
    0x5120408056001500d00000700050750181090340c1d94280031410340e104605484454062a034420a445541c0340d10031140d40e09100c0e811140644007802ca440c600c0c2c0c0c0c0f100442e43d036600c001c82e400c88240c4100300300054090700031301d6184191401595290700d1715140000450141c8409001000c4202503030503901c2440047c60624410545518010340d16032030a03101301401e003550303528144010b0f04048110703d104801030740d0040c05420641030154591b11181401c0f0018002c11840e107156100004d00f00d801c2c88000800c0c08411841401180141d0392600780407402c1c1d4224010b8140c01500910244494090b00c00140c1d8000d000940440e425543d2034000900c2d1103001500b000d2040c0e071314007180125040000d041101201940014460707428008036000c0c1c07501c001481d01809000c040c0c0441c09641c41504000a0150001e005001080d02e52090044680c001e07203107188039400c800e000403030043c2c107044000c0c100e9400800d400c80c400e00030340040d204400020000c907000c0480b50440d02d200c07003403 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 592805755 1106 592804649 592804697
    0xf19050121050304030605011e090b09060f01031e06090c08010602250b21060f060d090c0e04060204090f020702060313030e0a1e050d02031c 62
    0x101c1d06060b4150702032030308014810f90410000241e40080f0072002e0111101c0904010300450b640c8190204541c0d45a00050b04010404c0001d00396240c43c0c04980450541810040307100d02d00035407080d00074071040031142c0c111aa128014000c02c030651140301e01e07990382c50070038089950600c200691b5481c4100d02504505412f50b407905d08903400764402d08010034424050076200e0007500b80c4141c4040c0007001c0c0c079409400703c4001a0311480c0610030b089000c1030140078207207480c100d42000c00240801150a4456803810207000442c032810b130081c9840b0314003841c0c0050300d81d810902048251a11a001e0940040c01404941c002d030340c65000f103d40088801e03104050380707406407034165401e4000100460344001c444e000000e0300560108001d540c03007402e1100850311506c4100304410003018000181d00b562101d511104410b8642e4400306590309507060296000b946108100641c0b01 = true := by decide +kernel

theorem cover : BRFrame.Cov 592625899 592805755 := by
  have h0 := BRFrame.cov_init 592625899
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 592625899 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 592625899 ≤ n) (h2 : n < 592805755) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
