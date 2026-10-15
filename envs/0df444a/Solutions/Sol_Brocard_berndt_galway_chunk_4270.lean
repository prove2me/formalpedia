-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4270
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:04:11.08693+00:00
-- url     : https://prove2.me/submissions/44e7d9d0-10bc-470b-8934-0efeacea9199

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 767805755 ≤ n < 767985611 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 767807005 1250 767805755 767805809
    0xb0c25111c0f15020c0106030503130f080c010c03180902071205030615090f1c06150311040c0302090d0b01050405180a0b060105070203070b0405011d011e050c010204080304 76
    0x80c154402d0018200700245001c03160000c104108200982416042080d2908441c8207910403070702e65000103461848a00b0890401006085141c940e10303c0514103040c2030303101c1038107c042c01d0400c0301c410202420103024085880080c0412100e03032845a48400c0460b000303512880c8191500c00400e00d42182d403911840860b80300e414084c082d1b030700c1000301c1c000c2c489041e00807000341c682c090518405d020319a1900c00c03603a4005440900450b0040d2000d09095084814400200a103425091418804240c0c2c605d9101c0303107000c00b6640040c4610019404500a00a140040c0e0740300c02c40309840001d00c01500b03441c074103071441200c3c100401d8686000c10b828404510000c02c40d10b40140c0f42040c042500c00b000142e0100c010704000e45442c0d040c1d40000e06186442d0086a140d4001040a00c060b503030094903580c183e032108000803045150100041e10f4041042d50044d070184402c58400c524502c0f8105960307600b5031100081d900c40e0b80342d50000e80c603904180109548004801c406100c4190051 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 767808255 1250 767807005 767807059
    0x1e040519061d0303090319060b040c0c15020d0615270306020c0a0b27030307050708031306150302150f12130506100305060f040b0c2511 60
    0x1e01e0b40c0100000100e08105100442c02d441c50345400705100d4805140c030140583e01038000082020494503c1904e0060300719110403001c42d0240340750450036008250010b03022101150050840075400156200110203031003410402d115075410a6000114617513031116070200310019449440a148624250b0901d0035000c03841c40e2423074400403004101203000d85d401425200400000d42d54902455281c80159078006c0c0c0780c00812103003c0d04001007004607144401c511260160240d40b5500300b0307a030010a075001d80c0801812150000010491f21b0707020314004040320380c2c014014041d4000d00712505042ca43c841c84227a005490002d02c0d1809c06401c03034100c0340c81a00244146003840328581b266048200020b00c80580914918101c0002c02c0040001c10b12403003c0c0c0300c00c00d82060451500f14103020380170300a000c2c070100320310070b210010b445802402d510001c0301240c41c0c0c5136000704c0410b600184a00c4602424203018240800901c039001020010051041c0c82154143c00819100070b00c0c89020 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 767809505 1250 767808255 767808257
    0x6031112010c0525020901061110050408121e04121407020303070b0405030d1811060a080f092415120a0209130615080c03010b010c02090c1e04051906 66
    0x803c4400f0781003100340c0d04201310f13140b4591006440c0c03000382e010402202081c4c001c900480c1403800c0042e00000108500e955807420908140024141680d5209550150034000d03251070100000041304400364200402e0910380000120601d42442d040c0369815403521981100022024200c80b9003090344541201c190680c0030f4010f6151800310f4980c0c81c05000041c108580d0741c001004020006080c5025807484082580c00c1c0050708241460711410078065a0031041c0106810f00c640080150007450705684918842c0c06020f41e0340e03601e140c140c1030030900001c140e0139086203401e00b1100e01c02d10448510600604108400b211805005c121443e54841090110746d442202a4001820080c0710345401407204070002c102c2116a659003015140c0c0ca803070300300c4220200d10341000380e50420410303849604400c0c0c0007080100d0103c000280f0f685840400a03004080c420b02041060104804840c502429015154000d45100a00e101315507c14461180328140c1e10a0000c0d0b02041503030790808603045 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 767810755 1250 767809505 767809507
    0x60c03081b400614210103030306090f1112060a15080a15030f030509040b0a1205060a020903190212030301150f0302040e0127020328110f0c010f06031112010c05 71
    0x4130950358038a5441400d111800c1d0350b42c5031120020000b0800312034040c504c20b85020030001d080084241c110b404d4258000c1c07900c1e00b4155000d008003040320841d90180400c613000e400e1642c079400412060b0015a01c100c004c01f4189030840300701507104885e24020812118180251748080c100d807108104540005003071000608c14010000e8041d070020100380c00f02610104104641e440020a03601c227550010f0844413540c03d5010401c90700740b00741c940c442c001107411400c085105001c20b03502e8548001c500e002c40011203607502959200410790300d0121102d001c81e5aa5078480c0e40c100b40a20b500014100031034208050034000e54003a009450039a40c503d0560211070703181100c000c00c0c0c001c8017491201644c1800c1c0320000074003014002103101d0754a5403060340c1c8050342c07290f0007030540c6080425103003400c3c40e290300315030303004c601000b00c0e00b4000749100d4442e241c0214408580c0100031582c8222020743c64081c0c00410000980c00f11482c21004030780030804a0000c001090903038813103504420014170 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 767812005 1250 767810755 767810777
    0x201110a030b1f0e1e0a031a070903151e05011205070e040305090906010c02120706020f0708070b030403090806070201090b0f0601080106141e090a060c03081b4006 72
    0x2c000480c0fa80c030001175070900b5444180c4001090092440c0d030425030703140c03007044504c1da030f00204148000e401c00110b02d45000c1c05c52854072212500300021400410003a140c1034040d5040c3d259242c80b150210750b0a804001704d5039542031050194040341d40890325800b9502c0002003620000e5403c41c031554254440d18039049003c01080501c610050807503051110744456000540c803110303095003419109030010105c9031708100002c0d14200703088610b002c140d40300e48420f0100c0c0c14041b480c0300c1200c5103208029202d440718070301038641d40221b070800312441c403d0b4410420710a5054000280759030044403904100e4540440e00114010210751480c00b0a085100410240d0700c100d080006080403000b07420706004516040d0031190302d40f05107445d43d541000c00c1143c201e160000c48000104050f0619012202003941c016012420050407481d161801002c403090310103042c011604220351070800d08402c0010188a015140b0242c4400069008090f0180c40e5106910508106507081e075101c003200c840c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 767813255 1250 767812005 767812009
    0x80306041509090f03080606090307210812100609031110020f031605071d1503031c0c230d02030a0239030310060c030201110a030b1f0e 60
    0x314040e14410a000304005000881c0d0515200f260103003849015428003851403410000c1030954090301040c4104020000940e299400050b084101c508010043c42282d030102c104103480e07002c10074003520103031b00014101e4591a9201509114520501101c01001d03101c0d081110710712030070b000081280784001c1c107040141c42c0595226200c80c0d683d2044684002c101c81c28a400e41c0c005140ca900150341100382d0504204080c00100f001c0d02044240d0005058400511460101c002d443e0819006441001301020f460034402c4641c0c402c46922140c0064402901c024018015210240d000810908030321818103000e00100320a603004040e0a42400307070042c100301c025400039140303141d102d5003080040545498044a88141202d5080b0305800e403078400440c03404103003c0e10050410390130400030030061900b0281000140c801500c1c024450003110b14040e401011100200c0e0000e000200e05011010341c181c01211200c42305403510f0022081d40e10384080000400c0740c100004c100b034400c00503c3e41c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 767814505 1250 767813255 767813261
    0x703120209150d15150c030f021005010608010e18070911040302040c020c18010806010e04050a0b090105100b0c070e060613080637021305150406090e0408030604 71
    0x1004020041c0000d03203080d5032105041d0f8802604900c0311600c840844201c00d210156901c0106040c0c44d03040480244040020101c407075804008045c40f50360025054290b208000da0201405090010001135844a4014240d01401d01c81c1180c00c0302e0700d000051280fa076200280005900d88401001101c7c20203800401074a03034141c01c2403605c8014000080580da5034040d62083c400949c02414000c01594140300035910411030648071018040f004010f162000500f50f411685000104201a16585015400e0a100c00ca01620a9020400384010f420040d1302403402946130301d10725518079070b0b00c140b06100e07401802850286500004420060b4020000155a00180041800e4035043c1d003c0701c0380000400c0d0360080302c281e5100d441000503d1040d20811076603445100300015600c400c522254034641c0941d19500f80d42c0707401050b01003100300d08900300406014011315030304441c07a0640e9400c9030740e080b5204150005825100001e01c011084010500481e0040310300c074550341d143c100340409 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 767815755 1250 767814505 767814517
    0x118060f03150e04060b06030c04050d110925021b0909011805010519020906070f020102010e070803030f0115090317041a091e01171302100503010603060b07031202 72
    0x41c076840e001c103419040d41901a0b040a8514140020140e0030039051040407100002040c0c0d000d80d0081081c402d1540c4446c3c1030f82c0842c2c2c0100c42c4003080a407a85041001101e0800d8600e40240c5800180b00c90361028034490301038030b03503002051307601042e41400481c0c0e24200c503208404508a07031011101103042c60b9107500d41c4144114000310750001c1d20860440711104504040d900c59558200303001001c1654002d00d10140e440103021b505000140f00041c0071885031640083c0300000c071403000d90071a4002c3d08a4011401e016050b110740940e2014419100e0380b00b241c02c00c040d11030503400840c03034400404002041d400c07140e90f40c5208505540d00c2a10803003408200c03c6c910300050100140d10021003545500603404640e445403500848001e101c06081e4580c080242034031240b58a5480c0d0741d0098500c584800c2d10b040c90480360b10343c41002c0c11310009040c00070350000d54408034014540e0f00034008504a815a95080007103a5607518802058051038000800050088500031030407803154000d000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 767817005 1250 767815755 767815757
    0x2030f1b15010803030a06080a02010f0521280204030b0402010c0309030606060302190833060c01050405161a0304030203310819080313080a080103060b0118060f 71
    0x95003030740c440901d81201c0243c3c46400c0c0350740000200980c003a11809881c1c0100408001800302c001c2c164000f03820900c581c030800c400c006c2c001c10481080e9102086003c60820890400190750034066030500e01c8070f2000900401010310480c0c3c01c125400e4520031603048980015034407210781c40b5540110391030340007041d056041041001010001c6a124482c1100130107154400581c1c038044040a801d1400a21086100748101041081101d00740d5404c4420150015203800ea01140c00034400c54000410700e9001c0c0e0014808a0042403840055114600880c003803421185200240b03082c903103040c801c80c02040c081d6042d0310307180420310007010080c42c1c005201c1e005982c1048049168030700c0041c680d180171803044070b03801e420400c403030701038810100542150806812081203280c010400c81205203001400004c3c000005181004000e003511105540500415610401c0c81402401d80c2d000303000c142c602c03a00d4500310004542c052461441118144500c24005610b08103040c1d5041c030581070a40 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 767818255 1250 767817005 767817013
    0x20408190503070f1703010e0708060d1205030a0e03030907050918030a05030a0b1215010b0a05090607030c150b091e2406071416030201050f0304060b090103080c0c0102030f1b 77
    0x700f2a50001700c09180600005000d02440d4902400010b0981c0000341c5014002d204a06064000c89c0001c204c0303101907034403070078440e6a81c2c86480b135000090400f10380d240391500021042c85441807012034000100c0744121086107507600e03035804e030140155000040c001d0a81c8100044081030b4014006103520100b103000000302880c913140407514103504d01e03281c4000c03504155840c03000450103501c22809844400c00d076900300300101501401c248150b413403880c0f0481001c0b49160825109078404008550302201d00c0c0c0c058070071480d00b20050854001600e120b1950000082c40b01c02c20b6401c010b99141c0d840032207501035140c01e02c0c51404003507104066541080070b5038a200194035550018a80180305214540c4200601d00702542040900e1004600162840d0010000360780c0c80026900202100c0180903926200c1c0e14261004115444100d41c21400b40c900010500034290301803c00c031005c2806683c4040316190049880b882000d078980d107001e000707218000d6400c19000303a620f0f5505840c0b08036 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 767819505 1250 767818255 767818283
    0x30705031902010509061204051c0c0201110a21020106062105190513020102011407020c10031506113009040605060d0c0908070315050606160501020408190503070f 72
    0x1241b400e80c0401401c121040c500380c1031004000c810840701e0003044425030081c80392404c0343e60080c40405402c00103410404000030065600350240420b00c8210740c000c41a031825003602681034480107080d03c00308090b52070b02c2000075010f0300a90345180c0c403103051900e040078a40c040d8000e10081802034030000d1503000d101c4600c401c0b03040c54403d01d8090300300b130b1205040c3c0c0c1e40e66200090030346900c00c0613080007001503414081d0254000401030403e80040310031030448840702404500404540c4200c949001000d0000900140c202c10340702444c001c42000d440182030070030062040301140140003038100750701030011008421104054507004030010000b054040d40c2c0c8002811981118054078600b9a03910101080e44c0d4200b22890010704109005d04000703403075138031107411085c00c4043c040021901c0d02c00103980c580c0d40e8021607400c007078a0051203641d5001410094000d41003801440741d41d100320311803107921861440566209603440303801186418542d0b030302e1602e2441d2088007110808411036803 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 767820755 1250 767819505 767819509
    0xc1b08060a1a1302040504060f0b09040c02031905070204060e070c080919090b100903050a0807031e0305090c01021f0e0c060d0b040b220504050c13021206030705031902010509 77
    0x1c8900c090f1407030100541c50324113007070411040300c01d40d901010a480b114201040401c08070010303502141421500040c0054a0780000e90440c40b85042502c4144180750001100342e42250151002d54002c0d601002240e40300d1550000112044e100c0c240840d103503094000010390220020304100e04041c01c6205415903802a10000803150703000310641c184c8580d080045401d004114800c03070f0081d4a0300e60750203840e6803651500c03045070007400b0f8400388001501c8028503009064906010a2411000c5107200d50403034001e00922040e550300d581801390b91155201e962002075074800d00c1c1d0301000c100a503001c0000c4090004d04221a5890245c00741c44040c03400c56540d0b1016240001c0610b802140160201c0100f00441c0d04018a40f4450b589a40b443d0003a10f000d50111190b25104003070004041c0c840d810a646446510588650701035800301d145200c00006401405109420400f01c10054a403c1c0030592503800c0c500409400d0380c032885005200344c0c1145c620004080c01810a44e01d0240f00c440 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 767822005 1250 767820755 767820769
    0x7110d03120e1c02030a1b0c1d160207060f260106020f0f011e1503080c07030b150105070b0c0904022110030c260307030c1b08060a1a 59
    0xb0412141e60090045041da14182d480d454444440601c040d626040701b030b05010300740d44100c00b14244802080605841000a14a419001b40101250391607655814402040f4004002c80d00405c00f10201c11100032003c2c000500031042d00c0250b01e40400303140355001d0848400e164006103942102980200c10340d402800c03400140a091254040c0202c00c102459007071030b003000c0c4800306003580e00d800c41c1d0b08012104c1c034810510b8000740d50b50100d0300c202c3c0781c0d0080302800ea95408c0a0a00c0d41e000403501c018a800003240f408491040040c020382d40e1301c0c1104068640c800800c00d502240c8100f104900049440300c8066001e101225101d04010050000c6000ca070404c00c41d013402d5901c5032140c1f100d0101d00e002c1099202d03201c0448600701a0450341c0d0030075442075510580c0c00178600c85164485500a06d0f2034100d064030544200da0326011542801032417541c191000790703000305648501c4017642004140b40710666665034001c1c8001d0b2200382a40000740072060262100007d0007680710000d90300e0103 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 767823255 1250 767822005 767822021
    0x11120c150a020703060c0c0b070f0c080a0c0b070e0307050418020607140307060c11060405070902030a0b04050c03040204050906070206072102030406060501020105060409031b24050a0506040207110d0312 89
    0x47d48500155030949001c10b400100941803005110104503403a980da40d2140a40800d01e40c407a0482d0b4603040152001e0314407440d0034500514032500c0d1010000e041c0e9000441c0d100380e2904504407600c02d603a8006110850740040f010a0010a082c003005015040c544003c1c4040c0d84030320420511001c50800050458001030002c681c05925021082c1070243e000d860b10780c00c1c40301007020341030781e0a166232000c1d80d8259a2140041d031640110014490103050b5000001c0c1e408060300c18802d07441e01c510107410300e40c0121000c074440c030728010110b1000f49000611034400c55094005100544071060196046c004501420021250348115102070440900245000700d21500b40803800e9818500060b080d52001032005028515112025001ca5807000c40710040c3c0f003c030945e0820003255410199840d403910012240001c4940c0c0800101203041d50140d442800384402c20041a1142c904000903403280641c06401140d0425244585203003c2c9146120036219051241c114a036401e00941528040 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 767824505 1250 767823255 767823257
    0x14270d080307030509060f09060a050709090612050d02030f030c0c07031e200d0605060406090e0601141f050912010c110f06160c030306080a11120c150a020703060c 72
    0x1030300520010710001c001064104041c0d04004080346844086149d641c107005095171800c0743c883c804a41d8060240c040c1802802d02a6001d1095a4071000b4008c0e2034040d0410450362481020401c82c1d0003417011007560051421400c0c41441d58030340042c7c110458000102da500980075032200000041c0c182002c4005ca4981e00440c41252401d50400310001300750484000c602c41c0709414030240654440001d0071440341d120f00d00154640f1180042001005d81d41c2246e0b07102883c0a10981155000043c42030498001035103140c0c05008010074069044502052140f115041c03034000504c0e0b5029601400d511391029194078513600d0600710b11400e66040810300004900c041035003c800c544140402d100010b030100c020421428403003c5540c0003e441160300c0100000395001c4000c15109402641c0100382d10401c8404503505424400c00150212007000c3c03140c40185003518446a000ca0400211540200b8003005081d081c5008079503039001c0c200f0001107014140001c000140301d4031605284681c1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 767825755 1250 767824505 767824511
    0xe030711031e0d0c03020705090106051209031e18330c070611070b07081801110723090a051b040807030206130b0d0b0114270d08030703 60
    0x4030340c0070305041c080d011001407208110705261030030035034000600400107489440d0109085103c0d040803401e0444940200d0b9101218030000502e140e48103010388041042507070001001c0e00c075040c403581d40c1d10403002e4002d000f410540524150485a50240c540700300010303081118041c0ea00b00207001c2101c00c150088103904c8045000c1c480d41c2000d8510280e001880761002d14201050788032941e07604041c03141c031040000c85600c441c05aa0b0600c101802400700b03903840e50711244c5502d0580003a4001030350320035007015104000412507201d15070b020507500c4140007500c0741c181000d00c50581030b040c8400e8901400054507400c562601d4080c0d20718459040d01c400003c031400e201d00d5465000700743e6000c0c03051009040c0700911011202043c12070459504031030065440641c0742070014502001d60040c080f8900c0841d50f00038510300798000c001150402d07a120069049800d00c0880b850003401011100102c4003400c428104280034145620340310010f0103000050000d65401e8800d61003110940f0000391 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 767827005 1250 767825755 767825783
    0xd0b13020a080736080604030207140a0b0f09030a051608280b07050c0a03110c060309061302010210020d1a12100e010e010204030c06090e04110603070e09070e120d0807120e0307 78
    0x20501d1490752504a40cc03108861070320004400e980140e803030704026200000340c201255501040108a09540501561640c28003403c0900300340d602441070100c0c5000314087c0e001110412086000062080810720316106056242c4102c40e01c001000007007071050030401044a82010468800100d01c690f60308580e5500c200000e40c00d124002a665000c2d41e000c0c000d0100a0b8008140e482d4402042d4030080c00f00622400100d103060084080c5200c181d100041810100705141c10220980160154500500340203409001c2581502413649040d0340000c540c01410481d82c3d0080f2020700314130000451013001e00d00149089030f00c203070700841c2c095001f810100300b659041841c48004003410f10180d58035240944490714103046480c5524811040000040c00d220f01900e0b1010902e0b1001e0140051072a105101034201e10390026070900c18541003001c51700001000a51082940050340c0b04441615080400eaa45c103075a004106000c680782c0ea50562641c0040001d0800f15000d081d44a100c8a = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 767828255 1250 767827005 767827019
    0x1090c02010e06091c121d011406010509150d0e071a0f120406020d1e141b0309030708030c0703140903070302060d0b13020a080736080604030207 64
    0xa00342c100104a280c01070010001d0704030000c00c0b529210741e081d2000e804a419840d1044800c0020300c00455000d6140c001a8100071005502024000040c20001c0248a400c150310f6980e4500848801d070002c0d10821031100a0708000f5100c403814030b190004203013840c05d01941c035402d484001c074000542d540404802c200040e0f1100b400e40300c0310f060141083c03900c1d05040402c0c0d038074440c84502c1140c1b40c02c18804501008140e60445030108c001c00383c2000030042d1030300440c620305003414080805a050220101c4c1100400401c01c1c09041449803003c80807152280304c640c136420040510400780801e02c40d0308041600040114410807542c02c42690f114014503020741030003040c8600150f802000e0010102c15100016075109030703601111215103a0b81c4011701d000180100040b03044d000716280000c40c1192201c1c0e0040c09100c1080d84412003e03a503034440449200001e641e4880b00500c0100a0180c100c41400408451643c440e01042042e911f0301241d914150068030114010792116400700500 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 767829505 1250 767828255 767828261
    0x5070201050606072f0d0302070e10080705210706030b01121a090405010f0c09030c1a033408070908070506040302060d0b041d060604050c030708061801090c0201 71
    0x3c4440909104864459584011550303440283c00c04a60042c2100880c0c0020304003107100004060024800a40c9002502c07500d1510130300c041044410301103106a04c044403030000365540c1c0b200030048149480c1c2080746140f0040144641e40d840581c40c01351104051042c900a00a10749020621403011000188209010520890300c2440c00d240d00d0b0510b80c10800c242005a01203400c84001e8556050a0f4018114a0440ea801d5854205400b541540100303000c0300f140c0c041c0c032044862540d220150400050145604a8501c00c1000041c15940000006c03000b094100740400a40c84643c0c3e03000e48640c0960045040400d2254080004503039125000e040604408805481e0f46031412000c62841e01a42c04024030034140403403001503040107035018100902c0003e01c10b005501d20341c0054205000d1101e141d07d00341c01a440040c0c0035007040d01800d80102d101801d00c07031855030b45141c11508a0000f0f01299408030107000540745071130300c18040c54041d00381000c00280c1031a00040190031 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 767830755 1250 767829505 767829511
    0xb031806040b1522060e0109060f060c0804030c06030218182e171506030304030204050432011a0a03060c050d060b0901080903092d0d060507020105 65
    0x980d00040030000015a50400b242d082404059220070400c0540002444000300442141464102558035194681d070b80d0400c00c1110007194140c003080c0d03260704c02402544c001d800b0b0f0004c1c0d00410f00e4200400d80c0318070501211540203814107406c0c184c80781d0303031280c8010040e8401d10003e03030082603038401c03191107074a114104401190207450442e6070101030990200f0080031341c41d124054030001050000265142220410003858102115841d080003c00c1011901c1c0d9024440c855004040d0070f908415040754022a4020021414145590f00300f202411004008960b00c1000014032000b0042d45560b42038034a950028122064100c00a0751b03003118070189010791b0305001d402640743c4a4454080340c5065079081200880c030200180015103180c400c081525100a152a0000030030b038100401810b1010700c00d07a04d14849032a8104002d51780c1c0243e40c0020782c0900211081405502101448402c403900440c200544468480004400200b80802503604907100e030100200168207114040e4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 767832005 1250 767830755 767830801
    0x503071101050c0d05031f080d08100806190b0303031e0c1c0903030e0f07090606080906130302212505060c03040203120412120f120b040f060b03 64
    0x403d040d81c4100711030307581c90641d0407403051003c0040801d4503e4003004420f00d812641103114036000795500c44c581c0d503a054044021001408582c086025041000004c808691300070004254941301e06c154054800d400030400100306a0701c03031000100c1d071014006948510440c2c101441038210000403200c84c504000c0807041003c00030070003c45000f59118651140703811001c0002210595031a05900402181400109504c03e0300c054030b200500015440701070301c506038014044c140c1c2d00c00081e01c0b076200a4802803444c0c0c00090005014400000740c20b01401e01038411560a5881403492000450011485238440d5800080c1804079100003002001610002003000602c030615440d101c0e00c4000240c010521010004080303000e5540400080c500c2c2a04241c0b100c0c0e1b0303255585d040152200144804980c84101d40c2c5110452030f00468140b00d2103135441d21100141040b803070040d0024035204400326449a550512400342071a2440b034100174010703480b00b295482c1040c0382c121440c00c2e95416451 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 767833255 1250 767832005 767832007
    0xd02030a0c03030902150c071701020403020d2a15090b0c0316052409061503071217040609081b0d15020d090302061005180403050306011407050307110105 68
    0x940c1940d00140d800c04054151400041881ca14130000d005084601d03500fa400309400300e0500f80c007407004076030070044503052030782907100c1183c0850b003500380d000340d08c40a1b601c0b040c521500c030089a426521101c82c01d801000303e540d00d04074440e94121010180c2c012002142ca40403071000c020360003600c0d150184c082c03c0440d600f002c202d0104540c0d40d2180340f07400008201c00046610802104008012041540ba48048445102c1507990b078404802150000060310410021840001120340c200b04504805000f40100c1070511000c4003e0444201040b40e206840d82c2c10341714420800300c00303072015000c00e43e1031710001d6182141c103620f800c04000040102c0501003030525030580e20160003240890b880110200e03101140c00000c0300a00a5081d02241c490920b02031a08246d40400c1e680d110780900b9489001d00b07a01d413814490b88a1440d100d15074907082d010040f50200c0d0041c406568002c105140ca42c0091aa02d2101505034108002c203c030954404111a4101300c01c840e0b005a04200c00e103046 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 767834505 1250 767833255 767833267
    0x3020d2301051504350d080f0604020307201518010c0216030201200d11010e030426010914060a050c0702030c09070210110702040e01110414010e10110d0203 69
    0x3c204011400e64104040705c0c190300c5400030f298000326513000000c2c180300c1610b10460351002c014151503402c4920361030180980b000900245041d109980c0549455591001282400c004109040505000003203843c0700740c0400c044044202990329115410f5860300d800c01500c002c0c1e60300d0a403401e0003140720940d0805000c201d04011000c0084007201d40918024601c1400070b00c626070071448a0049200500070380d1080c2c0c0800f03800c89400054840c0d60740003088103000c4884c0c196102c5c00340c1c2c040c1c5207007401c55225001c04041801030020a008140e000011104041d07031700d481c03c4490303420700503030b56030402003c00140c40785900c1019031106000c822700b071400d030301070f8006501c400340044090b1150a41c03c0105000d54401c11034415880b80744802008180170418038a103203a081440100e00c5039003891038801c031601042c000e809100c0c00a0101905080c01c011505845201c280c0c0043d0410105401d80101c075510081c1d0700342e502c1d8041e116416140c080c0115030f410b00c22911802800d40d80b0070420 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 767835755 1250 767834505 767834519
    0xc2a1a070c0b060a0b1204051507050904150503030406080921070b09010b060c0318060922020c030304030c0302013c020c0f160906080d03020d2301051504 68
    0x1c0100c220303408a02024035903a2100000c1e1010850f8101403558940461120000012205114001d500031011500c400b50644040140c098080f100c00001443c10720450300d41e0300305070f00048400701c000b80046014a8403080482d1454100b50301c0791002507400020302c007030360380d09000440e80c1c51907800300c0381038900d110354890741284554403009003680d012500060143e08290300144c00c000b401003a19030b640000700c1111790350350012540c400081404866100759450400c08644001001a140ca14a1141035100303108501d000c9001d41c0380550200b04c0d030080032a00340019846035219845d415036a08440c04d00031300b10307005051890382020300c0c50754281d0000c0b403c0c0010240f5000140350507101c01c070f0104110001c0d00802400c2c14140c851815802602c010102d401c2200600d40e00204030b28594651221066031054455821a41c106c000d44102d098070940040c6443c01d03410f80c0203d6080c0310700b8055131080f0f4407a0002e0360f60580a600500c2940740a2784a4a940340c144d4071854200b90800c01 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 767837005 1250 767835755 767835767
    0x4180c05040612020d0e030901030e032d0705030301120c080102030f04120c05030c1b1f03020708090d06140901110414180a0501150306180c2a1a07 65
    0x61002402842e5a0a043c0841c0130780485160724000c02041c0061081420403690300d401101006010908210060b001000e0020540340d0203410b20740003810ad9900300700c508095850b0f44a482000c81c508016510200b03404000440c000d11f01100b45401a02c11b9040489180049070401c001c2a4010014080c0507410b041803507800a40280e10300503249046802a08e5401c50400002e00a000c0811400c0f581c2101280741d4240103115102443c1075000355040004850b461034200c5010702d41b00041080c224402ea001e03002081c400c007104c40c0340441d684000346e41c0f103c0005088074104e803901d000503862446030042e03642103210100240040d26080c4103504c0300e4000c40c01544a45c10002d246400b959980f01009107281d103814000c018103007811101000908000d00900408014100d03022014034801d1140c6401c071494000301036651034150007400c01828410520b4800c105003444d6240702400042d00d40c4c0c1100c0700410f000c00a008040ca00340d000b2891629526003c1c2416508001000c2c0e0001 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 767838255 1250 767837005 767837009
    0x30302150f0417130905060f100824120f01060e010b0d0908040e0c0d180c0b0c010905071401021612080c12040f24050a030e0a0203030a0504180c0504 66
    0x200207004041048a01c0b007056020f500810325401d5410f01000420a6240d80114060036050f1123003c40400c2038424060103600d0300c211000028206000121400c1103401500303441180010305005041d45400003030201c42211041001e290030040101d480e81e0000d2244d01d00400751507080307409942c0351410b0025240244450f0f410b026480e4400f610030000342c1404c46015000f549448103d6040c54203c3c010302d0341084102d9140c3c1440d06045044541540542d80c404e264040703213000084e420446060200d03002448440e0035592622000320000b4001d00002e00501050700c08903038143c0c07996000a2a0031003d001d265000003ca18042c0002c0203812a800003990300400001d6480f0aa42556440c5c81c001d1070907891040000b0901003420302070065000c0407a0311240580c458890300d02c2e200f106860700c0301c2020300401c0c0d041004000d07a50007600088c10030045101a170344454025000f190565009080690005000042c02d00c041042007402000c80405402c0800c040c0c0407030900544240700e54 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 767839505 1250 767838255 767838263
    0x1106090d050418060e07030203062b02040f090b091b0a0807060305060a0f0e01050406062609070306060801020904052a0906041203030603061a0102070b070c03120801030302150f04 79
    0xf02d200380b01c29640701d4016400a006107191508a0710308410014000e402c00e890252040c100000700000d440d081d142c0c1d0103d00c0740125000d24007119164208401444886880100c654a843c096008a980c1d00e020910503500d80307001d800001c0403c00c40044013500c0030342c41403141241e003506101019000441074141d5095042c00074160702c07158001651985654080c405000f042480402c1c1021000040ca0407642c054a0a01a8945902d01910030701c2c200c03600b07074001c42d640c01c00b41030840c4041c00c1d1458220700f840c1c086c0c0b10312544944446050b60302581252203903079000102081b1508061103283c2d800316900d00800601d9424050800350124083d806a05201700855090001c0d07481c9021280240039060355450700319403a280190280c040c1d0702c015a006864040d554030020136a486840c02c4000c140e02400441c0e09001c04241690004401500e1100026401100040382c00400c0c0c194081c1036101c044c1990316501c1c3c000d02d05451b0f034410300900b003806030078480010701650940ea00a0b41c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 767840755 1250 767839505 767839529
    0xd0e011b030e0409171305090a021c0f0f0e010509060601080412050315060d0c022a06160218160c031d01121802090f0f01050108040c05101106090d0504 67
    0x40b45c20030081c409400c0c1c000c440b40c1140000e00c031500005a0021500300d5805132026240d541d1030003120320880c050800780c0c1141c00380101c01000d030030b016540204202c49061200180d403442c20a034160845083c00400300050703540c0c1c01030080e044001c00c51558031000910f050701c1145030599400f01482030403200700d010300901001046950380441c4551501c02d201900d581d840f508220342600152540070b544c1e030054019120396031080303002241b106540d1807240082200c0380c040030302801850360182d40e4a0300f441d5005505040160707a80035403107807244000c0964140301d080440c80c00803070080c3c5461100901a80c2e103d00800a0742102044802402100d1b00607014014440161000410205605011480e00300c0c60066804031030342d2040200d00a5540c81c0c0940c3d50070b410b0703414106c0250345c801020f000700b00040006601c942105580b00c0d1040802c980c00f2540c070404502c032184a60b1314000801d0300e0021050300804104001c0340d01041100041071031034a201c0300038041d131023280508103c00315 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 767842005 1250 767840755 767840771
    0xe04110705120315061306081003030e0f04060b0301030609120c0309090b0f09011e0503010228171003030e01030216030e041104080304050a0b36030d0e011b030e04 72
    0x800045005140b41c0501406d40d00c240b21060700c104003100f406248040790081c400b0a04003210340c010501602d905446005402141d038040113082085221440c1d40300c2d03111100881c002c1001c0018600071441040701056803a141d2a20305030124120041000300070508800d4400700740e10105100407614400c4001600e1086d00c80810300001d44240c06a81100d4100c000040c0040800c19a20514540e008c0c0001810b413681d00b050f00307034401ca030310001c2201d8601001d121403c1c90440f1080c0c85c1c3c411400c3c0103c8038540e00b25008070050007155000040c058920003001450741081001d10044424a41140350001448a0010b5080000000740c01c100520500300e07010748039980b040d01031541d0f0070310756a1101d6890250f07640d07d038420300880d80151030003140006c058246005989201543d0200702505503000032004240d00580521382d501c0480001a01640c0e45040c0040206d80c80b0350b5076001002c08404002401c81444081c45000302c0e0000300e502c5010990005032030096440407203000ca0039074 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 767843255 1250 767842005 767842021
    0x9140f06090a0902040c0810060e010801030b070c17090f090402130e24101e0e2505120907050a21240509060f01120606150e041107051203 61
    0x52800f1000b90894903101e0b10ba0703c3e0700d80240300103100340c4d45002941c64082d1038400898820540000c050302044425005100140030044101d03840045490010707a100441d0701d03810816000142081484440003c5481160600741c000800840d03041da1003400e541005c3e0f0201e140301103801c0c00000c00c941e032a12810b0500c01d00340f0012212680c4800184040c450418590a40517420385244c0f0700501c881c0c0c0300007034081f106000c20888203005051807190720710701284501e004000625404a4541e5917117014a0b42d1201c5020b201c040e5143d69805849505070040d55907160b9010340704880c0f50340001d07010803443d50390b40c40e2a07095581802c0610664804110450f000e1000324500600300d48030410640c0c1d5014114491000e403428402c13007031181ea02d4203464643c13074181c19134480b258550b008005105130206100c0c0000c0d5288101d4000a01c181e841921402060b50100400c1c00503811840b262400e11301806a0f9480081c24000c051400300c1c2a0b403140e545081c1000440200038020002819103 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 767844505 1250 767843255 767843261
    0x2060c0d02370306051f08102301030b04290402040803040602061609030512030603100e0133061107170d091509030201031d0106080709140f06090a 65
    0x21048541450350900c0d64030b126a4241c20380d1460303000080c03030140001001d1401182c0090003030448a500781c41c1d2038002c2412600700c0d0004200e2100004074180000310f20005400900140e0aa0300e100440d040749000018242c42038601a0b0b44110f00700b091a01c0d82846000840c000c854002050716018803246010401038000c1da030182034540800701e400195503030089046445008020081c405400d05004c0540c0c0280c880c0c000034040d6402090401c03411104a8011a00440001c00725480315a0480382d100940740190070041c400c2c9d4480c1d01354810001580314007048200c8a105030306410b0b00c090440400001144118001c000c0a2641054081c83c107004080152611084da4090749503101e6040d0703503521000c610b84d400190410703400a900b240b0102008191005541d03024891851600110050458201484481000280b489510050911036100141f46910103054001c0c544615003086a50040320030300c146840303004011b9440c101120361f513030091044480e4451521114010402 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 767845755 1250 767844505 767844547
    0x150908030f07050111070c0b070f050f0a03080a020a12111c0b0108130f02010c050c031f0f1521120810080f03070b0a0908040f03050c0102060c0d02 65
    0xe000001d460008460200020004103000310000d20005d444e0002c062010300c14000003501c040102c040900040080c2d030020000d0724012400840d5200d002e84920f400c026480b01d918890b64000383c0c200c41095040548140c0c0600c441100b14240102c0040180c800844035400400c5295100c0041f03400c2c1d6120b00a54882c0d940c5c0804408080c07000603000030051888804180c04100c0030400286034418015a038440d00f94040f03d5100403007040e50040d100c86101d0f01007107074507010301c00c02c00038552810814080d03180c41c13040c0d10b4a01403070801920002c580c801c600d4001c005003411501d0f04213090708580d07182261b0341d800441c1c00402005111044500f01042d000384601d041000292000e40c0c041103250041a0761009407145568519041d03581d5240c0600a43c4140c10a110500c08220b00104d56540700c1001c8901081c1c032601c558402000341e01507000b0581d814902c0005005003e4100480c1d280e221083c001030180b0708120380b0112540c000d8412941c01507400140c08000b0010030100300107 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 767847005 1250 767845755 767845769
    0x70f0903020f19030b010603050a11040e0624040608090a0302330a0203060f01080106120209060c03300405030910020c041506120b3a0b070f020a0b011509 68
    0xf0764a03101c1c9029451030400780304401c0007904020100f4032004881c803c8402220002c0e039014a05454207440640650b402004560310504a00c501c070b84104075591600e8410380500109035590b400c180d409000d0305c001401c01429a80000c180000194000442d80d44190b0180042040780c0701c10462082d19403200c245940c1284158000c1c00042e4400750040c40c0103c01c01c49802400395908070044030130180c00d101389000910101107010400c50241e008003078811014007868500b4400d42d800a1459204482c480c8030a41c82c04021580e440c0800c0709000a42c15001c1000b050b4100b9071243e5950b4025490654498205e1031711496841c0d000300491031b1008800f810500008501400c403e04440040c482e4001280341495000c035003072224815543c0309200104411400c20064410051481d0340c18908002c0c078940c090541c3c031060404540d8180944518020200341c60403d0009042210391241142590301c0100c0340c01c0001d2103015441e0544200024404860a8052045a41d00140d40c4881d0b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 767848255 1250 767847005 767847049
    0x60803090111100f06050a0605031605090a080313050a08060c0409150306090308040b0c0405011d03070b1c0b06190c020f06040b0301032d0609050c1e030105070f0903020f 75
    0xb070441501341d08180111802102c1c42d18405507100c2094440e440102c519076100081100011841401940036119402d4090b103581c0c010b076240c1107001e2856121302440101031240300310410040ca40f40d5000e50140c05880f01034a02ea081503941d12059000701c1c060400c070142c0319201c507101e03204080e550100964100702c3c1407068044e6420040c0c001a0242ca040e101e01c0f11000005400c1d1400d44c003250101c41042e51100942c40c1c54090101d40d010240342d155a05024002d03001801c3c0c0310b04000780c882081e44a0080035006c803c031070508121400b01c92003600441042c42505080d2554544411102d00541003030900407038a4070008820300c102a82c81a44804080f50110700142e07882d01a41c1030382d2040c0c401000032040e158000c500002560300c0320100d10328206419000030042d800c1f0484080c0b2900482c1c003d10902000a617002181c42071039855141e4145240d40c05103003d0003503e401020a04201c1524201d504004240207801c0c00007034003a010a01c3c070038807540c8070b4043c03941c000c0c807414101e1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 767849505 1250 767848255 767848271
    0xb03060c07060b0d140c09010f030b13060507050a11071401030e01150b0715090b0415140a020a0f08250509032433060702120d1206080309011110 64
    0x1481c014603007118202a131046c462244c100741001070459041c0c4645401000700b15203503a644c1c14451a005148460b1141c01240080c0010340901615004901c29100c0300d0310b81041d010020161402c41416100719401a0b03020807288110301c009040d044020b28020403000f40f85100180980315045e132000e980e1890b1400058032801d6130f40a000041d12a040100c40704039034045200a883c10160042c00603400d101c00700d00000e442500c00440003000b03c0b004600b47c0000c000c1d1400d104811107040700030a400255904003151700014020032040541004201410840c0c00010240c1d840c50401c0034550284003902e00035409030040d01c0310488004c00302d03504102c40c4e9a03501e140410070700010401e07c44010201d030795030a8454039041d800064480f810b020300e44011521144880785146240c009004102040245c1c9516034411003c00c2c0303034401048030541d50440200704c003818508414515181000038850b6480100c100c6181c07400900c1c041c0310f100d418007801414143d14660703040c8458500b4060f = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 767850755 1250 767849505 767849513
    0xb1b161110051819060302030718181b020601090b030a0b130c0b0f030601180806090a0302070501020d02031608040f08060108010c030507020a020d080405040f02040e07030b03060c07060b0d 83
    0xa0183c099010b0112020051000c1403103020013002003040e000100000080c08824801c0d40516404030252a102403003010401c140f00d0690607e03000080403030101d81401c41c000200380140100f6980d40c054040c0c21604072900291111810b01541030902d840d000303452459a420032040b0315080d00402c0c02c061505041c29905d540d030603090300851b40038a064a00042486556095812847c12040705500d940c0d0b8510046a84800051410766a48480100030520280801425115003074500c01000002400e041c040d2401259500483c1150302c10a1544032107a80032007503071a40f18103c0f0504500c0c1415190500043c0604d801c000c010b1000c000e8002840f00000600314101c07111100200510b101d5110211300b83c5404a5410b400340c0d00c0f86c4e02e01c40050804070074115045000303400440c100350b2140300081c25545241003681019030045002e001004010007280d0300302c403c034102000001007982c0866100e820003003c07401002004a5960705220240c6c01a5844140052107100c1c03400c1c1c1c03850 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 767852005 1250 767850755 767850757
    0x30e061c0504051e150c04030c090f050901060501050a140f07030c060e0307030e12010f05070c0c053007081006031a09100e030c0601030309030b1b16111005 69
    0x50300b80c030b0910541c03042d5000643c5131402412550382e098003030304500401c0d401d42c01c45504003800d001e0070f1905c20040080030072496003c510141c000170030041030f403043c085841c800b540c101030025a6542d240080401860f078011040310301660850a1581d801c450811241e5024000c0001644520038009020401c0507445802d04e14075522914040020301401c1030055641c0c01507120040c0412691708180d556442e04507100c0740078909100020034119a04d18144003910010340c0c501c00031403400200b035400c1040307840c103110142c0010790b40140d4051a00d010006620307040007a600000d0134050700e1100d0b0300d0003485410b000d02203000444105c8540e19948600803c40c900c0252143d1005101444410681080e00c1c0e01500600000b40f849400c81007404c4c00802c41a05507041601c001c20442004181c02c0c004940214080c3d144d5641c02d40c40d5007070041d440c50000300b60100810211015000c041c854900b59400301c1c0c1d00100c01102406185000c0d031141e6002000c4581c010017212030301c04002c0e4044 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 767853255 1250 767852005 767852011
    0x907020718020a050f091306230111031218060f0a0b19210c030803010905072a020f090f07110a0b0c2a060f0c070f030e061c05 56
    0x140c03091044070300e603a4012080f40a1100c01c600080c0c01084403500744030302d440141000401c0140886490071149002d4421510150b1040b15414050b0080841c0d104000f0b0000d00007540a08040d680725498008117900c03481402100103c0b8880b41011407034100c05203440040112485e4216207085c108a001d241031140100d40541c0058241440c0c035205003841c1101121113411085c15210340c074280b0700d52503c141a0200460410043e600c10080442d06c4000e40c900194054844281e9950602c242042943d81c010450018801c092540045407803014107900e01d100800052000c080003988009208840440ba00c50fa000e075849041c0300441700c2e54031229010700069201d23072036018074183c442522850341c0c010141c0b85c442890005184034811034010601205440c0c0c00f4900700749045448c96105a010709810381320351140013000b8050b44c496100940184217082083d0815210fa540c1010240f00d819004041100c1418404d00c0360311100150380300100300c0d8003040c1b81d03001d101020500401d012 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 767854505 1250 767853255 767853269
    0x602070512162006070b1b0406170112031b210201050a27200409050d0207060509060a0f022a190b040b030c0702090a0911041a0f030a0209070207 64
    0x10741c1200006080e2820032280c9443d0103040207040c00c1c01c644981403450401044c0e01c00c40d201c122294900c01c0320481c0100b0203002c160b100d011340e020480b4091404440141c002d0b481d4044030200400209411000342680301c4820800c4801c081150300e025100c01d29030080c41154402c000700e9840007141c040d00254443c0d02c8a0034200314180c0303140100804441035215a80b506c200d400c0185010801c1c02c10384400c40d07c1c64178200c10400000b03901241c110b8504030710513070791500010001c00f91143e050224034010202da00c1c1c1203040c0f019500005002e0b10405419609100d04504030b040303a14000e0000080d401403080416150043c0015003d05110115030359502c60358000161034900d81500c09002c007a6108000940c0c00cbc135050120380388455002030a04030a041c2d0603c034600040c1d403940380862180728582c0c1c000c102a2028a8681e080c03d000c0840700380302d03030304003024040c2d000e80b1201a004041e03002c64280710344d0340c3c441e230100e82400d141c1071020790044113031000c0000350350300000d6403022200c0d0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 767855755 1250 767854505 767854523
    0x15270f010e090105010e0612071a030717010f061b02041508011d0601060e031c020d030f022d070501020301030c140a060e0f01110d0207061d010c060207051216 70
    0x484910908842090088407035000e40c1e00e001ca105c0d42008a03423030507020860001c81c0d0354191640f60841c81038440c20080c290103400081045486544501a01480803920f5900362032941031018240c003600d5140240f40410150300040a1515901403110000071340141c410013144c0c1e007403030312010300d04600d00440c0e8443d0308010b000040b511000c861507514074810000b808841c0d09014044940800524015a0611562909a001c4030282a9201c1a141190010218000d606901600756003a0b07101249540e4414002d02c81e43d46100e854650700c0d41e443c900390840d040181c200c40e0000b4015140042d00962001c400402000aa01c08020940305180d040129a80401d070801040c10142d001d0440081c48200d068000f5040210020710344000506001148041c4004001c0c5051012032003500143c1c400c0710f003040350540168611807011030702030010840e0480500060048851306400a01e43d40d8005110002d020f0140490070440340b01204250340c91001440d031543c64800d07404196a0018 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 767857005 1250 767855755 767855761
    0x30b06190b0a11010c2c03010b0303030c030601140307270f080309040f200d0b060d0c0f020105150d060906090b07080105030105150904050c0a1d090615270f010e 71
    0x300501c06c01e0700c00f0591402c4203000e200343c0c41ca114011034080c00c0b200d03010b40d20b42800101c1940d05002440c8600c8046040a86074540400010302c40c503e24021020801e81c10401d01c1440c5034010010156800484414000104080030b80c81288415a001c2010740c10080c101081c0c5540200042507000d4085030240082e1012200c07490881e10300c039040c541c24075214804074440141c144050700700349451040009a82e203100f00410482d030702c040110800345030f9510307c9a01b855000300548001d03001d1403000300506c0c9800c00860004c2002c1d0020103101c1c1e039910307480104014541c0c000043c0d6a900140a100100aa1401d851031007004c2e5800004240268004581420140300c1d4034071030b40030500d15030070914100302440368030900a88142c03580e004d10021141079880752400c01c1c1c003c2402ca441c1c2d4407030f1010b0200813016104003815000003a000081440750020250003030343e03503059045560070300108003120740e0a80c0304002d4102c604402c08420410502c441c0c41c60321103040700c11403003040603295 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 767858255 1250 767857005 767857007
    0x602010e0f0d230d02160201121a041509020d02040611011107020d0305090a0311010f0e09010621110d0605100c060506030a0822050a030b06190b0a11010c 68
    0xa201c6401603800155400383c01080382154000a9400c9807100703440d14500300a11003240b0130781c0e21681c2961080300d0710f80058021564007149201340820407507020030030b030040c1c0425002401c8540040c5445191a000b81fa201810310a42280091259a104543d00c03c0745030441c00182d0454444c0102040c800c26245030f0241040c024a20591000c0500d1881c12038180c1c00c0100c00ba07050b0b5800d80403c1000d104419503034a4404540000e18010241c00d080c01b4450310004040000e01203415040010f41e0007150015150004011b0549200e4249501044404900b00000d5040b1611841e04035040c080c1c42800c1209000c01040fa400c4108014402580ca0320309005403603040103440760002d82c0e459541d01c0070035152f40c441a0840d800500f540c2c0a002c640e03d40d403610350440d051244081c40f91801380100030705a160b0400c000c0006480001c40b60340b568503200040280182024008c4a0191484504080150402c005060f0404600c1d4031031038229401801c1640b150300e1101c580d03283c80600e045031 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 767859505 1250 767858255 767858263
    0x1030b062805040e0406021b030d0603060c180312032304020112090515040606080a030e0a050a0f150e0a0e18061504110c0a0813090203061503060f09010602010e0f 72
    0x2913400c00721200c9880d1640da440074000e40c000e81c140d1807903845011a4500100e07060005001d0950801008900607046003020b82c11074808890410a029001c40c204103082d5000312048101d82d0080d004040f001200c0100780c02504502047c0300f8180d0b101343c0382d0450350180c9101d03103008034000c0c0e84a584800c1c03903491440131a644110042c2169010030b006801324101c03129131030790040c07080c0c002140890f83c0e40101842c01c0c607001c10807800f09094282d001c1e0b49050449015005210440c2d20070340680c9084122440d410040c0652910b001c02c0c5603110141c0f5000d02c0d84011071030b902610f001c0d0083d60b03070306450300a01d03c1550314042c80c800c44020070f0007541000400c00d0091071480303200102c1c1d122010800c0010100003c075101588001d00a0010580d010702900e003803940038420142d66841040d032103080107942c90300140d4455205100740001ca0301d59205403007546c00c01c40300c000c0c0d0340c1d01c8440028204054584405600c00d1200001150450707041d0040f5000c445520102d40c9100b841010740c3e40c40e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 767860755 1250 767859505 767859509
    0xf1d03030106080f040c1502161404050c0f0f0d061e08010c020d0e30030702010f050406090b03150301050114040b120c04020f121e0906130b0601030b06280504 70
    0x15484c1d404c047c003400400340034000c00888940116042c11503a15100441e04080d40d00900c00d64403681400381041c14940102640075168200107803601c11242d01c010598040c0d801c524000c12804100b0342514500b036444807000c2c0c0f0b401e458440703c40495031071088504038140a6800319508001403900054000180d0120609003916020020607484051204003445482064490b200c0c408220504041c02c20348442c20305c0c03802010f0355a40c2d44a0001428040408001c14100201000b04221082d84003a210066900140c216035803911000c10070451500241e44a41d40f6505c0c0c9000003c0000d000052000c0c102000d48040c048005800c08006140b038040307030050704130b0300318050305103041c07030301d94020a40070103002e400c2401c1035003440d103582294000b21200c086c40102c9809546084a04428250b44500403d000f45480c0c500750304032a011043e0f01c07200803e030264240200e9900da02a0300031481080001d4a450b4543d01c5401b0902d0340d024103d4900010602c0c001d04501c1802d1040c011074007 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 767862005 1250 767860755 767860763
    0x1a0a0e0a09140a0f0b101227051e0705040507051b0c01080c0f04050603060301021603050d141519080a030504140d0f0308090a08070614091f0f1d03030106080f04 71
    0x2007070300848050f80e6111f11915080c00540c0e031888038410074440d4159201d0903003202c240b0b181c0601130b20f2500f1031030b041d243c50901103101d10700e9040c0d04405e14000f4909090320781c10f850101e083d464030102644c541c0079550015000c8121140c00085403c80041c0c02e551048099aa44d045525240c400c079030f5500c514503100c00301c0001003000780400e040c00030055030040b002030300051030f05ca18680320051075942040b00300c1c000341c0c0020f07500d01000301c0341c021500c000183c14a10250790401d40d540390b83d04140c414116010714140030140f8490030080a940c2c0041c240401a10303400003d929004209034042e001d4a924000b9020440d251350510300e071902d0300141d00c801829110907085e1003c2c0d03010035004024006a10035010440001000200585480d903c11000403946c06240d04400c424080b009203010040e034400302c8040840c9007030031115403a0351002e94000440c1c1c54818204000781401c075003040504440a000c1d0220004000002c504a4589a480000d40d4540e0f080e00e600500c0b080d500a0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 767863255 1250 767862005 767862019
    0x60204171204061d0d14100c09050f0d05010e030427050402030a150204081002030711010e0c13021909030c0b09011202250302010509071a0a0e0a09140a0f0b 69
    0x4141c500a44d241216a000d00a2109502c0a0303d56100e010303000541c24454034a402c00000f03580d00d9802c50103000700a040c1030415400c0c40d0704000c00728070900090103a1034400e2026061010500c4002c0d07210380343c0e00085105490340c590302d611742010139041c0c002c0a0603035a84403480d00c00341c2000b1489070f01d00559004000e080409403075100c610400304403011440d6501d40c00c000020342c00030104002a02001c1ca28000f50302d03440c1c083c1011781f003a81d1298a01d010359041682e64548814049018001500c2c11281102550f04504a4400038000c80c00c01010760651f10036003004240d048441c050849108581c4041c41586645204403030340900298036011800d14008110740e5100d94001d4966024000140045003012085d51400b092100300203a000d42d40d90410f2007491a41840000085c02d0040380f0758000c2917103096400000e1059401c003504200c524401150b0b1550b4074136105000708007002003413090b0501d41d20300c81c1c8e1200c402d031401c0e15518a0704051030303000046130046032b0001c00010484 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 767864505 1250 767863255 767863277
    0x3050615181512010906170105060306180a0609110405071b020d030c0b0a1d030c030910020f1c0e0a0b0715060902130906060503040804090e070306020417120406 71
    0xb00401e4141c907a245802001c090207020b40c40d24655007102d008050440001c298030740760500280d400e541a811038400f9034108010401952800542680c03c070910014081081445403981e40c100304610304001c201c20b05240c022418400c0f0340c4242d244868007146c0810180c0c4408009440e922640e01c80503246540b02103105001d0320b422440c0c140020b0284c2005c11a0721403642d182d0b4200c8504071071203c1c0040e900d1040701d5500880f00707180c1e580001e0400040d49005c0848010302d60324054601400c2c0303d68600079052000c40d10034001d0601b0000c0c11421100d00035490340e110480038070411200c50004075004440b10191609024400845240d0002c903481e0041640f200c07030f00c0e03025061060800315218400010303000700910007851007503078508218101a091074103c000346c0310341c0d902c80e0007000340a00500c404150640c04a6040701e030b01e41000103211600c2c00c50141895225440941130328030218002401c0001d0039006012002410141c42c0c2c00004000707d4a1280928051000020302e12101 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 767865755 1250 767864505 767864509
    0x7123f0c0f08060102031e0a0f0f0e09041a0403020d1d13020a03140a06080c04110301051905060d0b010e0a0305100b030c0d32060a0f1b0305061518 65
    0x700c580014045c07042c1c034500f400400541038822200c40c00f050b004400041c43d22171059200e29000f0440c01c1d64030384600e126201e500b000302103d04d0511034a104032891404941040581f2031041110105840d68074240c0c613080c103000e900c42865003519000b08048107042c0881d05c2c419601004e131104024955220f80580421440c0250030004e0002e003817540d201c0701246100e0010301000c2c4074a541c0d0402003207250401a503a4101000880e08600807818112408568400c2c0c1d020382e41518401c1d289018401514403220512220982c4002e400410011f80c443c0b1030302c0603400c1000c1491003a210140740e24680c0b403c4c40161000c501c0007070440d03048140301e200680580c2c2c114102058005003103600c80c016050014400d010390b488121200140e903d0b580e1103030f1050303c41c10700464420303026003d1014180415642c940d64018201c69041740e645407070800320310240d8401d065401d608200002c03000240c1070094010700003510345901c00d40ca4010300911228608040b500d420000c5e980c1030803280c6407a01 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 767867005 1250 767865755 767865767
    0xb0a090c0503130807060e06010501091a0d0e19060f0606020a030c03030b010e03031b0606120318010507060e0706020609011503060c090e0406140601050f07123f0c0f 73
    0xf1045440103c2004440c012900324013400841504000242049514100001d8106203c0340e102d11000290300f040300280e030107070b1015100c04c3d2500c40c20120b04041d55801c2d8504001040c84690301d08200c0c0409481400075a51012490001e4040104601515454141d9503140c4c1581c000700024080d51210002900c41e40081c1d0b1003c1c0d045c1081e4404001180000e400c1d41c216500b205d400070504019480781103404c104060308403d0a4030314a4408a0000d1040d0f124882e8410018508102c4039800343c00364070440485401c56040002085681d84040c042a190031a900c00c800042c4641d00c08038100e588107102d6500550f01a0415000307107172841d9613040107415080c10290510841d008005142c2a1141d0014490340c416400041c1401020141c003081c540080d1600381002403e1110f0011140140c04481c1990b07049000d2009600c980041100c0102030112040002c0383d1000d800320003070388031a400c43d003084003480d9155407005d01607408074100c6690b4042d420004407032070740309240540926 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 767868255 1250 767867005 767867041
    0x50f040e0d0c05030d020403030806040c0c030503011a040b0c0a020f01090f17070b03040506010305011401180b040f020a0f080c0309060402060c10021611030d05030c16050f010b0a090c0503 83
    0x1004c0d40d080620050b20070040342c1065000b41c010820150030441145010710441461755050308060403d26003a45008000d4001409024170030f8404d060f010815203200010782d801040514552596807080e0ac43c6140c0300c40d50007401301d000340948121800d6540c00307889510262000c01c05100c505524011003529074141901d111900f600a41c1e501148490000008611a82c020401800f1075455454401d00310f80c0070324101c1006d581c81c040103000083c54000003849075180b50340040794002d2407000250007004040310f0906051b200041810040c1d4200b41c0109100f1150303120310040b42e66180d0181e449200844d654650b41d00300100003001480c04001034960b0f6103100c0200c4440c100c451309224100c0e841403000500c0030300504801401c0210020400a46407820f4010386002c10290034058802c3c0009080078505140101d030129507c194110948002074200080f1101c0803032000840c0d0080000700c0c0901d025101e40440850030350440d000742070300e0000642d02c041c5180e03030380b11010901e013101c1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 767869505 1250 767868255 767868263
    0x5031606050d0207031b2108060906060c190605010f080105090a060213090906023601030b0102030f2205180f15060c0601050405070c050c1c051204050f040e0d0c 71
    0xc807039411b54a01d04990404440c402e4014030130408995020250303000c1c43e85208020050740401b0403081d03407502420303146c100d8000d540329034440c241c4040f21410314180380c00e2040c0320001441914180080781d040381d8122900115240350840d00d800c202820383d031040703400d040c0356444000f00b00c00282c6031781d004000801c52010300421103500c0b80714860588040c140280c130101d4022450003c84010f400c0400a07960208091201e683c0d20484c40040310280036406605155a50070b02400c240d0007407044a0b52802c1c0030300d450b50b407601040c101d40c500711258205020761b1188801d02066034140381c0d071205011102c902c4030300307520742c3c8d144400e0030080030040603013900094180018245448540207005100a40302c050328403581044280021110000c004104100440e000540030910101d0310413040b00c01502c0c003001c1c90b0600c40d80341c0e030b0416000d00700420a10401074501d0304010100080c00580c0e400300d03603509244e0001001c020544502614000f41900100010182e0078082d010b108000c40c81 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 767870755 1250 767869505 767869517
    0x50a060b1903020c0a0c06020c0a0518042d050606060304031e05090d0506040b061e0103092109080d0201090b0a09020406030512090108010f1d04030507050601030c05031606050d020703 81
    0x130b112a01c904001c40d11308100c0e00396800396000c2c4a410340504c8030100031081952a401d2031440c1000054202e22403900b03106020703047c20049802d1282801000810720000300740069400c40b076086a001c0c201d0bd1102c19111806410080f0b2010700d080800c0720300594040c1d50701114044040c0d0110001c52204042905002d010040b12000c2e8640c00c08100e440ca0143c2c002c1c0c0308178074050800c25410744000b002c46102d9034015940c1981c0000c440d90051085000f03190001c0c1523602d13494441d0900002c2444040e01c84240c106000e4500e60000210042e20130744001c0d0b4005030801e1605074207940b4000401004401480006040b04c0403940c80240a580018030110700943e40740c581c80d007800160311040441d8000081c4203959545c0252106006280c00c2c21100c015903d0700f2003462403210701c034416604d0b0012944c007203001c0c50300c942c0c26101c800e0340050980ea2996540d1819150300f900e54030403180603002d16000703580c14881d080e1140c01124900d0312500e14100d00240c00c44000e500c0402d040f810b01003 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 767872005 1250 767870755 767870767
    0x1215060616150e061008120c0a02060301081e010e0303010306051f03052a1302030601110d08190b09010605030703240815010b0418060306020307020d03050a060b190302 74
    0x401400d08141a8119007000407101c41d0112440d007400e200404500100c5c004280c200826500060b59810b0072101c0b0110715100d5120720030603801c00d0741c0b00c100a5808900800041640d210105402c40c1050030b61007190704032034040b03220500b078a054280340840d0340c10910041020400c40e070040c81c1e0200200120700042104500c20200101c240c2e04103440951141d8811a4000050140c030f04450005421034004010b241e40042d5200d141c8070030500700703a5004004103000341d00580f925207aa840703030420303104051903000000b024040104c543d1035a05103a000400845443e901c00c80d804140040d00c1c154080c0e00b0040282d8140e880038108004040e61240100003030024411070340e0140428040101c05c07070349494003c03803502c207100c001da00381d403c0d0f820010840b00b25413604913421102304000507200308207140c400c02e00800203540060149030002040020042d80406c02d2083c406590b01d0070001ca4a0f00c05204084030114011080050010480c03441003800e940a24038401c026483e0140c80c02c6 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 767873255 1250 767872005 767872013
    0x39060408160c210b01050f0d060e03131e060c0206030f090c0613051203210c1215012a0b15030f0d090815160c1b03021215060616 57
    0x101c4040000ba515611040030f2008202c8000800e0b40100801c481e12401040c0356000641d24403a8880d00400b201e23640d0345885181031040c03013600c20741907415a401313031140e43c1ca21244640000b06903280c940c10149940109200c1c1c000c14228600c41d4011341640e045941c0c600380e02c4401400581280c542d80f10b500403907003880d07803014010140503c500184112043c581800c0c0404285a131034442c10940051010308601640c4e103111030345a0140002c046016128211401d486106452980311210030381010060f108207102e45184040c94281c1c0e400c84c21201081c415017400c400e248604a2001240c031441020410401155422a021221401840030702100281c42e00f4031081a040040d0080b10124140035080300c1c40c038000b0700c60803000c0c001c1030600340d4509000c03e200601c2400080010100001901d11614480602d150700903509088849400c1c2c00d0411001c2510040788030301c10010365104003800c0400c034131440c584100184000c40c1c0710141001101d80080c0c00071502076030840030800200f = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 767874505 1250 767873255 767873279
    0x702030106051c050111030405032a0307081b0d080105060a0908070611060f0906072f160b070503030c0c0a05100207060b0d03020d120239060408160c 66
    0x1c05403580341240f030342d8181c5007060948400c00c10031000c0041c10b008000c00302c0e5012044604c400e0304860084150451080000101c640f50020589a440007003a8423003040765030b900402d4000030010400e21141d6030440709540e24145420010005400c00c0010845414090060300000c5050300705035041e540c0350100281b07030520340c5d848100001d0b0050300a0420790001c1c44043d0700841040800c002c5403410a00241d5283c801030701c59410040707540f000949030551107000484211540b0500d90f0b4801542515035a1058024800c080f0f03000207120014403945034a0444545943c04000355003981d550910b400000d81000c510412140a840c40140016209210b032441c14140c015006803100306d40c2c28600110391440750b640380140c142c441c10310046500060451501005441e00c240c4e0010b116418202a0003081d203140c01d4011130642c14440303103000100b41c0b041446008011115406603c0c1c0700c56480405440c050212075003000f24100d58801c160301390f2803650085002c0c4144230b079540b086d2500 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 767875755 1250 767874505 767874529
    0xc050d0e0106050906010810061b1a25080c160b090303071d0d022b080306030d030b1507020303190833040e012004090507020105070f05070203010605 66
    0x1a42d545160070b102070300d010101550060340a107080d003031618120344003104002d00c5d8050380d003d016403498a01100059070031854070155100382c4028000c4103030f200c000074a01c1d065803100b884166030390444020144125802c4440b0099990310380c0d04c1c1d258041004c11300d6003d1007450a002c80c00c41d52105c0803807503081802d4050703954580150b03540e150224004201a015208807442d0404411000207207585035030781c402d61650100d60205000c00d0040400d0b550701400015030012501f4216110140002080510700c01c400a9003541c6490a0284040342142e4a8084480d40090025840c1c44240055000f8080341d078405411a460018213840d410003090f5100d00c3d4000280d0f41e2403c00403d0039000d403054000e8002c2d454103100c10156440c0c040642910340800324080c80e6a4400c0c103000c00800d400003859005003082c81d1049802d800040855a8060701407511620300305008102414030520030300323125241300d03501c55510100b0030340225100c3e171200406980c90341d228040802c0e42d950358404941 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 767877005 1250 767875755 767875781
    0x90c101805150c010f06030b040b070e2215081914100b0f1504060c050111030a020702030f0a020d0303020a120617010c09120b07020f1005060a080a0201120c050d 71
    0x522812640d1800c1c4c01d550740b5250a5031060308000c0c007040021030501499401991207104a031443d52210422075000021140c065881003881c40d0b20608030381c4250190740945a030050a210250025003a4a64807105220b9000d20394014424061941090451800007621554010441f0201110700900e44012030306006440c4c1d86d41e284010052800074040c1c1050a810b66085512080340301800082e402540300740d0041c0400c071807140e41040401e620444148404005c1c071a06e0f401c0000b2002c00035000100120300901c541044524144000280500400d500404c003d1f0184507554044001e500441c84407818803940c24600000f403800c6000313038405809190501c64115946604160950307614a2072a000e104030b40c0002d106c002c584000e0000ca40d9080046c3c140c06441d80c0c2802c902e4122802c02c101e50034007403c10715090340d60b001e810560007076200316030401c50340d510f80744420b44a4404610003030114844103140b02020115804c0081c440d0060f0401d282040200f00c0c0300401d4440c0003a00803 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 767878255 1250 767877005 767877007
    0x41b0f0e090a0c050111120403110f1c0807020409060518070f050a0911070f0807020a05040c08060f011b080d0c02010207080f0f0403080f070b090c10180515 69
    0x110006800d03030001907120318001d0051990401d5501c401503d10724601685041009120003080c40403c1000810044e5241c0301109a40b03582d0790800c40780308a0781c400781e135128800941c100703000d516004880f0017564050741d1b0aa2046499a6180300305a80980002c0f604a0303140c01d00c04001c01c010b4480c1c540f00d50490400529240010304c070342810704620b07030460040c040c1000011b100946802c14a0350a85803002c50004408581140400f200d0240c600c0003030084d15080c02440030481000060b01000f48240d601084ca06d454504010545604010000010700380000241c00d178906039251900c40401810407902c0d080748200088142c0d004600d0a4506100010340c82480c1070251245c1c03045190b040c0700843c201809a03840c60f00902c51030341c04007440c00d00490039902070301d41d0b94226001140c0c070690310380e6245003103000b180c03550b045224181d4000b1140c20020b2500030f408107858045100042c650030316180b624070b003969201003001000b07103401c030f60303141c04035050319031b00c14840d0103441c2a40d502d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 767879505 1250 767878255 767878259
    0x103050f010e07141504080313080f0d08061c050f031c060f031401140411011101060605040b1e0a030e160303091502010b1018090501030503070308041b0f 68
    0x210382503a0900102c1d42d207950084100f00580884880c0c0c0b603d040f6012200496041d1074038200302d0950207550803100071400005034011041d85031440400031100480300307a5040005a080c200c0e104c24503c184071001c0740300c03440003a01a190042900c1c509001c0e480d9410070a0039152555031414a00c141200300c950710003c1c2e1001100c0487c442880b2500015500388803260400428601049540c4002483c000c0b9000090000140a400c1001d038940e09241d0804a89041d042c480302c1c40022841e26804034011400d403840d10181801080c00f5900e554594070b213490300c2d01c409007089511402000c00300e6111445c00c01d5080c1c00890041030001210b603800300c1c030000007030301c00c6050007102007510700b40308808501000025000058001191349050071050700c580c030140280c3c050140c806081c0e07404007512085c1d507900341d045074114113800c52046c00781d400541c44120b02c03021200280400b80c03441c0d0013803051400181c40b403c1c805600512960380410340b445003504d42d0f2040b620540125130003800136042 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 767880755 1250 767879505 767879533
    0x152003190504090e031c1107050609031b06151903060f0603050c241e070f06060504021e090a0b03041a060103092a15081503030903120a0c0209010305 66
    0x58810f04013a21029600e000d51100c0740b51401c06410178485191511241c0110705200100240e031005074025042d10364a00e0310034640368a99001c1183e400c0f4410001c0c034101101038002902e01d100316029420640041008010004444605010081092006a400f00000c1c59501540d1540c3c030100da00494031a0551406c03e003031250411170075001c1d00840c42c11608410410050b00c3c00031680b08034890b52075000300c407200240440ca40080c0c00f0600001001400c10107500e48084040d800364108010281e168000c01c0142e10aa610080032108040c51a00940c4064001007a0380c1c000201944403482c0d0710020740c000c5070020bd50940d4600240d8104050b00032840d1407840e031048003460104181c004a50f1a242a2580d80641e80c41003200d0040061081101841c214054612020000035038108010010801d850888131514040740c1d46082c5a01c6040c00429541c201c58002d029042c0d0340d003144000c400e1604111a0315081101d0800b800d000350f01c0b034450480c00b0b9402074020346540007482c21 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 767882005 1250 767880755 767880761
    0x30207060b1807050d150305030c15060630130b010605071502070c17010207031d0108010e0c0d1103010816032003010b0301230115200319050409 64
    0x1054022001501c0750081c01d6080c0c2c01540d44190681016034446661007440001403440680d0105100c0c0d418001205102d400009042c1409081d000c80d0180005100c440c00000f200f40c3d017a44d04007d00307014070003c9000504145120381581c114a01499092a82d9944401c0082d62101800c400d04480d03002032003102c0384818003508140c10041c4c1381071465610f103100340d01040c0305060b980e0b5001c20030408115034a51000000c00d08203581000702410454018001e620640003100130401841000080200c0c080c504900d1443c145c4031154180e1030943d030264001c0300248503c00b015010800007211645e40d00c600310341c031251032036069101d60511841600c0c019203409600b00700c50a102003000000e104c005465210b1a101088114040b14040464094070004c40801da040d403c00280c0c121421240505414000c030309003d0500c00c1c0d07030380e408004240303100e01809070003e40c0c2140c0c410461414108540d04000e203001c21a4503003c207110b0b810380b10004040c1541300103540014100240c803c0c0780 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 767883255 1250 767882005 767882021
    0x7051005150f0a091d01093903030507061e020903010609090803040303020903070b0a1812150c02100f0f05180d0e060904050f0108010c0201140a0513050a0305040e1006020606010e060c010c03020706 87
    0x12110102c0c0211000e43d00382644c8daa200040802c4400101141002403c1e00036001c841110b90200620784403052200b13000e90010918103010750710700200010840240c0c01000c01c0150481d2085165442d00c0c0c82c00c50107540800388554141c0308003c4000f03a13810100006102101155840e5007000b02003a0220041c50f80720341c421000560f030f025803003004c1690f6401d00e07585400d4418000030007000c080c10a90602941c80350f0318060524100d00038070b00700d45a41200307042d64041c0300200724964681e458407044014a840c0b600580e84440710585806014183c2e00f0303c89480104014200700c00240020280c0da0100d407560070402c0d490740100203c1c0c0090140403e810440c0c002803007560452540140b00c0c0700010089450315803901c001c01c505060b101030404c0b40c15004425510805000e0030040d02540c007521641c3c070302001c18000102c8000095800345c040c1c41e415400b40c51143c5400004482c00c51f65881001d90005040041c1800121300b485171051444035920301580340c0b442401e202085903604 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 767884505 1250 767883255 767883323
    0x803180a0f0503100903121104030507060224040809060a030b123c010c020313090b0d2901090c080606031e040807051005150f0a091d0109 61
    0x2400c1844641d0f000314281040b4410440300044c1c444071030a049588002026899035a00e2802c5942407104d60300000a00680b8003500480f0a101d5030303800e0480e40c808040c113401d85a072003d6003002d4000c1203200301c0c560300a4021141c1d182411100400507130507501c00201c81e40403a5440500c0c48090410322025902035280a0180040080050a0f03e0000030f0024040c10900d44100720780300201c85d0b404002c044008a280204a0701d480840080d5483d070043d03401d1505030800000000d628203d0b8014440d030f1b61006032824400c1d41705a501d50164080c40c03407440c45114116034112040070b1071121668001d01c0035900118040c2c10031180038050140c00b42c0000e010782c07030400c2044040410980180201c1071004c3c210192a40c40c1e0500c81c2240c00f03904001440350090512001d1040e20581050f4050040034803c900007400031f80c2000b4148076500041754100d0f13130400042000a0803076204c9410386443d80400c151780e20031280c501c2d00711440c00000b00c8141d00884e01e41c80952500600050a902e20 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 767885755 1250 767884505 767884529
    0x60309140f28050303040602070b0c07031205090a020d0b07030621030818032a1b13090602040305030a030c0215011208120f010501120903080c030a02040803180a 71
    0x101100241c6985031001c842c044942410440c5440c0c418180c1d000402e56000b400f80c0341c590620703103000e00c0079501c000019038410070303e03602207540074066400721510b09600d80c0700c03030b54101d000ca04210040c000040010f240741c084c4181200258444056010b41d55116404201c454074101c0b00140c1110700c40c1c0c012082c50000d1406c01e82c619400314104240103038050600182e9075031020a001504851304000c40c040b4003000c01c0203502c0484e141c0e00d00e034040703603801c448a180f01980e4181d2660782c00207d1441c0361017040c240141030f05003880c0fa42d00c0d0390f01220f41d101080c04042a260b507826a48240c0c01118642e00010b40e88041035811f11441d01d81c0e102c20720161910101200140c504c46030180241c090182009888a00300b103d410212004094801032070381d054605261a00704d0680700740f240c0c074041030180510200001c80c9102d00c81d407295050b00e5664807911380f8000c50201e6000200300c1003c0315402c00011070f80c11b104101804074403002d0014198140c80301024003010300c035154000c4a2104d0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 767887005 1250 767885755 767885773
    0x50a0b0306071404030b1008030a02060105090c07240e070b1806031b2203030c0201020d02060702030d110408120a121a0d02130501080a0506011d040201050d0608030406030914 77
    0x100030f00445040300d1b00b1904001a0791102401611401c80d240c0c480303001480300041e014001a0013050355030480382c003140d040410340d45004400605101c0c00341d00030303c802651944203540181402c01d541a00c002c00c500040e8202c20003249a1900805801c1110214404184100c925014102203040c1400c140d400a00310b0420400c0842081d0030b480034800340e10004140c0311010307020820443d802d00c0c045144c1e007020607a0703030801804181500310140e00500403d805001d031540000740040c00307590710b81d008501d0000d03440c0c40403005141813071150304030700010400062400c07000c1100b425840d03041d03110349980f20344e02034014103c220100380400c1c089041140c43c1d61030203440000d41781c256206803400d0101c00b1052001603078190f411030941c804549405d00110301c0010002c2c4a00c0110710a40440b0040e90303d980d0030040d90352902c1d248904d03075005080040c0040d4070078009810360203541d5002003a0191126a503034190341140d003003400042c4e074072000351083c421f155565802d51580c00c00a014804 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 767888255 1250 767887005 767887037
    0x518030d0203090d111309060e15070e031212010f140d020907051603030516180b070804090c0c29041106040b0711120f0a1b0504050a0b030607 63
    0x400349040315449035070444d0b076100c24031824440b5052043d4006044074292911042d100005100081003660814070b0300711500c1c2c44100015070140700043d10702c00f64107036540b200412102c1d808520002600350141c441c41240354900380020b441c1005050300a00842e6050110316000e680c002d030b101400401e00407021a500e074550100b071441440d015602c0c0070545d41c03208403d403030500c1204c103c150340741002480301e403c3c51760561000e80201070340000b14040c00c2004000301c4c3c5810b10703a40030300c120804406c010000c0d428202c004280240c0304680183c2850358420703900781200c60300b4403440e000c6000d40e07005d5400c000c3d2042c0301e6906444040001c682d054044600c01304080c0c0d0003000100448403800081555079244c8050b100142114142c441e40d80100e440d0408802844100d81030017124201000ca03202a000705075031140190070401440d9001035612146410706444034a221115400c48000c50707540c0307950085500c02d080907080811451038650a0504d0b215004248200700401c2d410a01c48030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 767889505 1250 767888255 767888257
    0x606090105130f1b2304090507030207050d020d080105040603021807110d0207051008150d0203070b0a18090207020102031603170103030c031e0203090d0602130e04060608030913050a090b01060518030d0203 90
    0x7c1c403816880001d4035614010f05500910032040c0140107171007079404034422254009640700704c003c000d42e00c00105076651010701c403c0d40c403e400000d50000120b0800380b0b07500e61040c01ba070741c0419240340c4052a65032944013181042c000c00096001a0401d071000d200a0500c00040c42da00d07485442c1414080ca040000c5244d4030240e460420321030100d000d940700555804001c2c0a01030308100003000d43d1032004c0c02c000317000031218114440340c800619900180e001124820b40304aa03406030040c500e880c00110000d5042101e0800071000c0c01100800025401910400d07640a503110303880b881c1c078010704ca0401030959120411041460f145111035420350300d80c0401a9100500c0640d80d00115400903d88039010b809800026002c3c02089500003c40c0c601002200b40910300400c810080c2645452280d51a03216091015800000c90300d000b038060445640f25540c00004090b0000700418150b94503034400c542a4024000600042a0864800301c605024501c12000310024010000140b801070740ba = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 767890755 1250 767889505 767889509
    0xc0f08210702060412030e0a0f05030c060702151c020301030309090e060412050703021c03020304170a081305100c0513060206190207140105010b07030807020606090105130f1b2304 79
    0xe17401c500e80e8010980184001020a8001080a02010744580481012501e01e21031640b10b44541c000f811628102038003101d9843d80c000c0d1040c00b9011801c1c60640c40340c1e10012400d42e42c2620340d0060180e11500348041c5000e1446640c2c1c91012a2424801105641c6030000d10003841d003180c802c2c040060202441c402e00c0d04200e06119480d14010300741a07003080c401d1184000588140880c1c100156030590040d40310301e109482d6041c402c2d00c03070031800c0150b000303500c09100071500eaa0003240308500c4400104010601c0341f000c495991450081c20401d031403407181248085034010401003031016a1110200c0a01031501c002c15203464864150180360340c144480043c141d90000d0354002b80914400d100c02c100110758001d002d070396559a503900003070348180c1c2d041d0001404c3c680803c121910104100b402217400501c0000c46134240410801317202c4825004408041c1e0f1451500c80f03c0700303030b40a00e003d0502030f1104600c2040f8940d0024128400100210810b1024007603900100f003810b006a8003 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 767892005 1250 767890755 767890769
    0xc031a130902030102030145021303021905120102071e0303090212030309070b0a020307060e0309041508070f051c030306210c0e0910090c0f082107020604 68
    0x10301100e080141100a140400d006501540004004504902e4039003000f914414070303c24080d491061032544808c00094244034075801c0580741402a031548158000d070055a44100821400983d07a9002451810051101d810001d011150400951400380807000300c42504600035454112169541e840d00651008014142caa00461a80c1458425403007840301982c0607015402514000d40030b20340d40c1d00111640ca6403442200008603143c3c44400075104140c100b41c00079402d000480d034452010380741b4a0380030441480107000c8000c0507588c60241040031183c0c1a81d83c00803d06183d03155003051070f03070b03000b4002852103039a0412998850500118000000c0c216200d8150040e1a046024100795484039000e4070910800740c0c00071003030460a03c159131181210b40320071540d0304ac86007400e1904035078035192078100a1308056402959000142250310810380c50b60a10346840c10001807104a80001c5e6a44d8010700006403c1c6020301d00c030100240080e03d01900307180041c0e00152151289009280d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 767893255 1250 767892005 767892019
    0x10111603030519060b031f12021c170a1214010e1305150613060f09110906030403050405030d030506060322050105090105090706080105031b06070c080607030c031a 72
    0x49126140404984250050302d10070b100d01170351001081300e290415140b072070b40299074040003100b081d102c21903902141c048801a09182c03050741c0810088500040343c0c9051140751220003c0018108080303086d002c48003422190315850301c000c00400700d0200e414124045840c1000f0000300003207608000741156403d2807940c605965102005020b040100c2005107644100740c83d1002c6c080c411000c00b4801d0000761080700e0381286502a8005840e0b0303031b10829105c0310303540b402444180429002402c211400744c10252030100e154020801b150300031501600054808902032020740f50500000c1c114408915050119040c030b038000036454030020f0620903120702610104948812103500410015400034020850b42ca840660346000c2c01d0100c070360b0b0302103001c1d203080031030001d0048140354180c55010b00100868000f904804120742d4901d50600d92015080c4080c200240f07d02240300f000d4242e0b00b01070b000c0c0c1e0601c1000a800d4230202c0c1c030603105160074040140c2d807502c80111090303103110ac102d80322 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 767894505 1250 767893255 767893261
    0x130e0c01050c2112070305010302011115011703090901030b0a05090d0e0103092d1118040f03110601030c03030201060e0c1e13080c0f040219030b01051209101116030305 74
    0x901144940e08050201c4d2442c4020000d002c0e030903900986c1200c1c003e03201c400812003003c8040da1511148030404103982e020500500210b00030001c1a9012800c180441c0d180c1510400040c985d100240e0084490858900800c1a400c0d001d00815410910b680001c1100f01c0c0140030103015001d03e03010460426030740700b07405418800049400d005182d1300c0900404034a01e0510f02c0700d03800d03e03501c1090340e1400d50440030303460606091070050b80e41102c0b0410300781c40d03848590340c00703000320841e14003901044131144802c1e0203c80148101030003503205414541103c6d103140b5000e42581d8446e4804400030013440100920f11146100702ca03020018a41500003442c2d1100659006014503403520f58220304802c1c010420100000f412008807100b00d13040309031840074030200703c00c1c2c0c440c80d20518043c0800c00112100c440c080d400805c5002c005061150a04c4000c03c0c803000c90007000c903000045544454072040700c009861140c6d131100c0b507560140c0780c601200741d03101404060f0b0742d010040070150780d8000 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 767895755 1250 767894505 767894563
    0x510030b060a1d09011508070e10051203030907080a1703091f1e0501050609060d090602030c071b030302071703160f050d0804200f130e0c01050c 64
    0x2280c4043c103041c0c1009030b000d2407080314601036240112040c0740107611780380300c42000c0f9612175103000031201e200000701400340c1041a00d03001c20b4405801c80c0b507048100c00b404a0300c0d44e6442c1c0540d846450004c002c5480345840280f5526200503684041900d410800124000ca4140a10808074104406401d5070780d44541995500d01051030190141660400ea0702ea80c0d0700e07e607500b0082001c0d041c89400c003402c8e040d0552600889000f0300c543c0758081401c10200103d420b004014000218076480c0c00500080c0136290310050307034412900132940c07070740001d0604200800c0d615a50241041c80704011450360540d03401a650314240c1c0511a6042c42500b00754a03140c0c0308000321381e0b2041c0c8041307440c45040014603007084800702c0c4000403a9039004039030214409a1160821a1003244c00410b005804041c5004801d507802c28500385940012174580280302d1521001804100c07081c2419002a49118041109041400501c11141081010000c0d0301041100152103481913212204810f4a8000000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 767897005 1250 767895755 767895769
    0x5011e0c0206010501053703150b030a0915020a05090907020318120109050708010c02060f100302010c030c08120906160503150f09090606101e080403110a140d030510030b06 76
    0x5000f8422841c1443c0300e241394034040520790307842041900d05000c00c122004100401009c10b00580c07110354404d0001500d444003d4001200090041400c00310001c26400d020003030743d101070078400101b1000900d0000c0b50a01c8045030303a00400600c0134600b8030f41c15030b200340000030050610703030b10034a0140c06080300c0034407c0d804030768840e03800011104141c0d502c1103254060b19007a011000035010710070016200841e03503041203100e50524090007000904690056a83c1d013803c00c0f064040068601e040350000354804024075014840f280106941d250100d001858840b0007000240740c01101500400410b0708403081e00d0308500030b08441c5280c8558140801c2d099505501815032161f020024031601e410081681ca002c0d03072054800024100c0341c031074242da800e0403001503010103000c05403d048120303119095050f0414420300d011001414050140c900e42000c40d071003512000d4418041d205200390421400125050f035003070901179490141c2020180403454171010f4211078100001600d944c2d6158 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 767898255 1250 767897005 767897047
    0xc050d03060302091b0f0c0a020316060f0c06020909010602010e010e0d0c02130906050f070f020703030c08090a0519090b0d021c1e120e040908040510140705011e0c020601050105 78
    0xc00c1503201d440383d10050341e85225041003a13009004100d8bd08000b82100c220300410b90340d0907192801d66010010044903102940502a603249500307104804003981c800e0485802414207900108295081101081c2103c455646558440d4811401d2603038140c1c1110315604e82c02d404441000b00061030304c40d0400074000281c4010700c031a181c40d0802040750000700106004a15942d26107000c0c60000a050341d48085c03902028001c943c0d10841c800c0040e0130795000780704c030fa01c01030300c01503034241e641011030411895042c400d954206003031000d00003030070b4520800c050084100c8480c0f43c0308850f5008140300e4150a034802050000b40c0d4500d9080c000b001c0f0604d880031703503109007070b440c00c0340e181c10030080c0d80031209202d1000617003201e400c00c19441d041c064441c50075003240409140601d8a8104540074190381d40810602c03019140e4070110b0081400030f40119805100040362415850704241c0e6480c00044044000510b0480c10016007540064445d06540e001e0801d00d55030841c20312013243e040110 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 767899505 1250 767898255 767898277
    0xc020c1e0913051b0102190609020d05030d0e0601050f010c0f1415070f080a0b030a080301140901060908060a0903030b130c030b062b14070c050d03060302091b 70
    0x10a00384040c0e0b01c0c8840a0740407207030280f8242c07141e0b04220040300c070310f1515038100f082c010b901000c1400443c482014141020910504001561041603804103821160f403050980d0290000304415150048030700520701020400d2026001c1503040000040e41e60295004403030400015000321010001030b00000001c0c02e40080700407541001800c401581e80c039030a10300c00c01d0b0104103070100b07401c240201c80e048506c03034180e21456040d981e1030380e58500404028031002e5051191100d000e01080c600c50045010705a038004001000f441342c0c05000c040c0b00c043e131140c4100041408108529803000c1450741c1c00149815000c241451141000ca014119a500855001003009042e5a8010340e5074000c102c1005161800c5c001528030f4010448103001d40a0b089070440c55020b507100035070700303183d44140c0c3c414680d0304001840f06607824181e02c0e003c822500340f40070902103020300c001c1c80010801000034a45510b0203100c00e90542c0e01081518502074640c2c01010202c1d41d000c1e180001d0b02c1c080e12004040 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 767900755 1250 767899505 767899519
    0x3040f03021e03093f190302030904051305030a080604020d061806060306051e150318100c0e010c051c0909180201140a030905010c080f07030c020c1e 66
    0x882c03000a440398410982c0f181700700c1c0c1c0c0c420390f5803090180304501494800c8982c08a0286240800d0040100070001c262416034050100b00402120118164025950213607004646239800101803001f20b0b0806442d240b1100c042c1950500040c800004550900c40e580c5846000c50b119900807a010303005414044403804d060006c040b4004001c407403050f01c8040f408034103000c031a0361070500fa0101c511034020786820030301c01015600d101842c2c2c0070307414022201810142201680c070310700f032901342c2081d20b42041007805200c0f00e42c5119420807202e12903030860a410811800300f00c1020317003900307107851650b4140720f000f0500d5014040148a6581c04840e5458128032449440e00d000300180800d000740c106052800c6d00105100c00080c10206840f603040e11100c6001c0504141241706400042c420820144c84424003400140280030703100310103081c1c0e1107030102800e10031188864180020103600c201490450705090551b4000f03070081c0f0710201912012040d103400f20405141c0400b120b0281e4200c54 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 767902005 1250 767900755 767900803
    0xa260403120c0e10030b0f0a0305010204081b09010603050402120709061a0909010e1003061415010305100608090708030c031b060f06041e0504030c02010305090d0503040f0302 77
    0x80c004a030020058001c040c10003000d00720210550f83d801400721481c2e04400b110040190250180e4001841e0060040400c0d582030740a00c0090030040c2c2c0c1c2c3e00102c8a60b5004101001040c50402c6071100d5a000004548420002daa01103210803030148107400070541c403a80030509645850549071a800140000c0d601501c1c2c403241804013509961207040d6260150f013403414070319007150301682c05003074006101120503442d005ea100380380c0901426540e4400b540503070000001c0c07034600c034a102106802100c013000d0b280c0100c1174001000407034901810f1506080810101030f54507820482625070078140300341b081d02d5150480e841c01803a50421041c5100009200700850303400406000e4000d0290440d41120b8000990b00352201d50942c0c00442c00d501090110b040ca28058101c1c039840ca69650251203001424400101518401c0d10250045408500c0b8075084d544d042c054242d0102e140e0703005191900306031100400c0d5101c001e002414080300c07180301c10201842403005240a414070146412244 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 767903255 1250 767902005 767902007
    0x1030209031b0307360b030f010c030606090e2a2703010e030f0c0c061207090b0a0f08130605011d0708071407020a05060d14090606060a260403 63
    0x30982c07200900c00d1084070400150611078001e00c0c40600c00d5891021180304010306418a03005da04009114003507112101031419440422010528141540021a4039204d4000140c21550340c0d400c540b0030491105001d10140300200c00f40380d0042d5860840c0d007100e140044004a44a107080c800010490340000ca00c03003107540000d004208000119445140f10076030303100b0075080311410540b8411f10303082407112800700c11021018144805101c000d80b080c510204000078070f40c0d4812990012490402403d110009610908403000340102903035151520201010243c09031887c0c0c5d0094040001d41c00014101d070400781c40315144190721000622141d40c403070544030310301c1d0030240340c0c5070303820b542000081c1d6064818540c0f03074050195901c1c0c1800202c1224440d061562000400b6a0459440e020015980e180c0314014600d21909010008840c0001c5800319600b03000500180341d150300000c188080c5641e03c0b001c5880e00350803030030044441d1401019031882c40da04800c05000784211182000141 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 767904505 1250 767903255 767903293
    0x150204050301060927140102040f090f060b0f090a0312030c080a0612030e03031c0501091518020913060905071b2105040b03011d010e130602090103020903 68
    0x140310128024421140c0301e0890f43e048514045607503190280c5450042000c20341c00b85500300b600d000c0d12915103054801011142aa441030f03001c4820021881030401c111080e900c900281c0c2c000c07101060004603d00415102c140c05603210115548900041c110301c29610070200c6001140c3c00030b412981d0040068001e0002c10400341c041004c282a1400140b8548e060f1048005941e4104812820039903a0340301221a8410100e2940c5c06104c10030000589900c140303800e29a101d04000049078560400400c141034035081c1110084842e02c40ca4103014403658034031000a1000580c00041e02e689102001405914215000282c040e00d44503010424906d0754128903c10385841d00d8445200140f000700305c8076114001c10203001c4030f0260070103c07000c41189a005060044c280348c00ca0404cae0f00c82580000d241d03c00e030b000440c0301d030b4031148080b40c0b64141a4803600400e0801c0d00e019291030040c4404c0e140100c11600180416800521000300d80c0c0240d0642d1000440502141d160300c1300001031001b5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 767905755 1250 767904505 767904509
    0xd06090c02062220030102070b04020f060f0d0b0105190512011a1c02300702030f1b100204031a0a05090c01030504140a1505070e0f060a0309150204 65
    0x5000e001c001854001c1841e03c100050400004034509200058132644801d40c00203200c9603040840f08aa0105030b5024000760800340e00983c982c0169017000e20400005000701c13200365005107414400c40009080d14002d881c0000c0d1b03015000315003103800c800100c5240c40b036030012050050f00d54030410300030303a4000003820070255150b0a0f03400d5640c8a0003140b000e0b5061444022030002c0402c903c0010a0744240c0c4451a5142c012002d800c00484940d150451990341c0300080360754024041c90606060206149500503186002461a01a41a4101c0f00c240710780d0309001590000c240001c1c4c005403041004500380c02d0300341011510b403a281c2c03074220300d045210700e50704031003001110102d0110340c554401c0740d000301d008500801d26810081c0c015400342100130000e54486000c0c5400e103159580610501d51002c2c441d0103426045007151004400f1120003820400030007500c1c1250841e50b407201040a00a003004541d590b0f198001504100e000d0189a1802005480b0340145044500c10315005001 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 767907005 1250 767905755 767905757
    0x30906090c010504030209041514070203090103050c04050306010b0705100227040c1b02040b03011103160908191401090312061a030406151a0909010b031014060d06090c 74
    0x11403a01e20001100e060140740000b80d480312012011500290340c0d510014001c0c0c00c554401300c0e1100e14134240c0a494442150741202580002038401429a45403042580c0001000c4c591400c007410a0042550b410050042331148400018448203201e002c020035504860701400a643d284800109081e082c1d0322084001247d10390091032450038a442e002d0341041e0300e102c1ea649141c5d10700818102d040c0c00203940c407da801c16510307000784845803001e011701c8040c10504c50342d959580c141480360560324150000e0800401240703104c03d01080380040782c95803d41c10b110300d190000d9040f506000c07146520030000303403106602e8410460f0425802c03c061100f400701d550000c02c58a9922900740700d90010416055010b0042000001c0000350b241d0310900d1203042c0c540305d0b8103079191160b07109100101d4003d82d1080441001c40c807102c4074904948800d015081704104c80d8114103014102e800c1c410024011907041e40703411030451209449000642e004c00f5019070b0305008090b80d075a01c0c013005000c80d210400c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 767908255 1250 767907005 767907013
    0x60a110d0306030c1502060c1c090c031e030504050907030b04090b010f1707051c02090415201606180615080d0f1223101e120f020603090609 62
    0x401601c41702c801c040300907a58001c0e10160752492400c04040c0d00c04000301f50710502c00103000b103462400384100440c40d88150310b081811030860910030640c141400701040701403100c4401d41700003503101090b0341c00c031201036511100d991141e04c000d802801503040d04941151403c082c01c414080d54445a9048030542210400c6c2140c0301c000c0058001e10081d1303000c110317900c03211003003046081442c4004c030b43c00408418071714400310302d500146511009071801d13200c41007101d054180391455481240042c40e00c05500903c5401525030815407806401100d129100c80c01c02204203000710703504203044443c101003402c0855040d83c03400c603000f441c02035140402c100307000320f004c205244001100c890148560701c2e0501c1c42010702c03d080741c0101c03010080d550000c0e00d07802110803000c0710800001180c1d0b4041e0307000d5800d00e0146d03001c203030700d1450742d0180102c80c0038540841075800040d00036506036590243c110b9458951030404402e0110b815800075003103d0000100b204910001c107060340207440c000300751 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 767909505 1250 767908255 767908259
    0x60a1202271504140d050f060108030d1103010302010e1311220503070509010e04080c0a030c030f02060601050313050c030a0507051f020303340801080c0103060b09060a110d0306030c 80
    0xb001c0ea004900030f002001480d0707500c0080914084155004103803248046034003c00c420000181080c5081e0310a500310351011904c0003403059640a1041052110ba12403801e541c0365400003001101135203282c0780291695804403852031015042440c04000350b943e21690780c0d54035442040700c0c7c401001040e4165014400100302c510700484d54404071140109108126400e00015080c0288082e0084940f01001c114100544d1824003000c070081e0301a0312500780b1000035080c0a807508056880744821034000d041007110700da8225050300d03000000c075004000c3c884010300e0024509038203100207507414824036031641c040000001d500810307120103882c412240036080a08103c04423405041d0b9000d40c006200241440c00c1c64174a0400e224905005101d40320b8400c0782c080120604914240000f80302e550050103481c4c4100010003800e1800c1c80e00300a4035141c903040d00314034058081c0707591042c1e0000030320581c403034451300c6025078084150054896003c01484058010085440101d07840c02202e580 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 767910755 1250 767909505 767909539
    0x20d3203071d0a0504020901020304121a0a0b010c1401021e0310060c030206241807140403471006080606030f0709152c060a120227 58
    0x1500b08004002d04103040243c108401c00c030183d001321000ba8114071041c0000a0981490344590354417074041d21840d592050950b06010056a0041031003180c00d041028100d03e0341d0380400302c058916000f0240b00304031014110314502a100300d0040a44000004e0003000c16505008011070050650b80079010b84190348180aa0f41c1220303480001d030142c2c019400107200466608407459074280d15a509400922413040024030302a40c0301070221b18a982c0307208200b450344d040204603000d412003c5030ba9003020f2440d41d594149400c0820340d42138442c0b444038440d451840f80c44400708a140584242d081c11003458100b140746480c119100522200312103400655076004101503800703000080c00b1a8950390703800140310020003000d40b50408002aa035000034200ca03000303101c60346561103544c45007070f96541905801c0045000100f8210681c6010300303c80c203183e55140c2160410025410442d007501000c0c02244000d0050348801841406500c4016048041650f9242d00380c4001700c606a01030030309106 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 767912005 1250 767910755 767910797
    0x30d0305100308030c13060804060e19151d0d080c07080f0a02071e081c080711030408070905061e03030306130b0d0302010c0801090c020d320307 64
    0x25200440070340d542401e001003100580290b034496103035115079141c010010304040c650f040550003107000805580521041026a016820088500d1402001c8504041416000d4140a0720006000c413215030300c2d42c0e00c0780c000703500200c40003440e003281d00031801c100b1055a600e480c001d10320f41000407820400079491031080800c3c1d84400c1d8000c0d01942c1001d140c0314140185034000c460040a500c207001c0700240d2640c158900752920654000b0002c1e55030324010a032468001c0e9603041065a8184204007111150f100c450302c0e501c00300910b0034588010f1009021400c0d0301c41d0f03030045075481c00b07402808290400542c00c214064170041d2521031031203c041408071b1034016004070580e07050304104040b52040c80e202e00d216034048084400001c60440c0d50001030804403c0f03403001c40150f51035020608009400054050043c03803060824050500100c50081d1a40c04c3c2c44034a20510502c038402e44c502d02d0048090a4034403010100c0000e03182c40500c500c3c040d9410440350f80c00006e0700400d4030700c90301c81000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 767913255 1250 767912005 767912011
    0x90306050c13080304121104290a1211062b14090a051c12050a051812030402090c04170c030106050301150e1305070603050a0b090402010c122c030d0305 67
    0x907001943c0c001b2180c0e24803018941e000c4425a01585070300403008004180c0c04803003412210414050900c8030450140521000320354004603260240500c03001c0031880241c40301c1e00e00c410446145903138290140c0c02090261080c0c031041955410012030780d8840130319130b10001c2c2001c0210800810b5a40e03540000350f0703486042000415681140710300c00d0303a2841100e0025881c4240c2c7c189132041c854640b002c0006c60f40126035450ba01910b070700038041c50418140c0641081c55244000c1c04050b0b02e00705c910b00c0d180c44041d1009029640c40b90008001b1211001a034011b001c51100841d048901104800c1c1d03101d54980449120703500e000b00c000b0341032505228003003520000010040c00c0e58503200303165000d040c005144c41003d0480555400014609111403000352038643c50001d0281420160002100c543c2d042c0103005030402018000541c0c1c200b07155500c0954040e216054041107080c00310703525849290380030241000044400d031090302d0340c52240581e1206070200c030a101c2107448100c040d00c5050b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 767914505 1250 767913255 767913269
    0x2004080c032e0e012913060303080c090d0f11041401080706052d03090114040804050d03110304081e0303100b030414060103080d1a010509010c03090306050c13080304 73
    0x184024001e80b4400c0e00f0503100071003280000142c0c00700c566211030910100071141c58070307085200e9554400d441d00c103480c901d8800d0550801c004103411980c001d410600c000d0500060390201117189000c681d29048194411544603400200340e01d0780703107480048645c002c507000384941d042280b4060883c12803400c5604851805c0c00a007856840c1c80d0054900d0741c800888044545c4076440142c00003440322006243c9400043d5076569a81b92404401e421204200d101d4146000d0307072810712010039442c4c019a42516403c807103100281c120f5203029a440040200d02682601011900003003281002c280802c80040011040814400d0f4451580c1c4a12048a0004100c0d0314094180f141000c1b0758060b50f4000d10581462451490349403a962a1a00076401100c51403c00036010030b28800718000c1c2201c4e0126003207000d00e01e900307010000c3c1060244141c0c00381000603200109060502c02d00f901401107800950401090070070101d0341006900020f9407a0a040ca0a13400003402c400c004202d404913049 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 767915755 1250 767914505 767914573
    0x603010c1e110a081303120504150f1704050708070b0910030509030c0a05010236042c010e010b0604061421100305120a020a02042004080c03 62
    0x506040e40c0c0100d040e0240c0c0c040b0300c43c210f80900000e84240003842400314000581c1466891490070b085104c540100303080411105020402c00f1401c82c0300045d1081030581000802e80300c40c0c40b022039104801600c040b2100685030700344005e00c103021641400f52640101900d9903140c4410403804035101c1d000c44260000d030310f1300a0b02c060300d100342e00a42d00701114909991500070340320f80d5903141070300da18408d4038642d5000a003510f041b685142c01c120682c482641c000314144c0b038410040e0003004401d080c03d00650300c4031409042e07201d9400d9803c02160710384602d080f41d11880f401140c02404000032880c00c42d032820403011281c0c500703182a00c0c102c0b41c132907803410381030740001c000540c940c0c100d0b003074a206a4417000010320199240400d503a104d440070f202a8041e0920303500701189051002140440d103034034100003001403198040749060b0403e40581d400716800700c203000d0100c00d1011502140c0c1090201160128061b0004207003010480b508408039841501035115485010600480502201c08 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 767917005 1250 767915755 767915807
    0x30210060f0e0a090803041406011502030a030c02160306063f0f02060415080105040516030908120f040c081207060506010c170c0f060106080c180a030303050603010c 73
    0x10b0039891030b076100c0c0840b9804107034811140d032a21400e070010340d4100c0b40350300b0302030841d964140c0c00c02c04c080c0100709440b4081a01c4c048064041d4691148824050030141c60700c8480c001e0a00030400c0c40444200c01802031101552420b112008000c18054054ed1070030304c0001a01d07c052091141d40000c2180e020360051500c00c0300240c10030420200304035044c2541380314220250b65200c02910080c04440c81e4140102800032005001c82416045280300c1d138580028006144200d800c0c0da1041702c00d6040001e10307a8801c0c20f040e50117005030352420204103150420041c0c4182c1d0900410702940c810107a04841a84418030b00d0b4036031503504001f070110007040c081d078008074031103800c0035030030070b106060032070303c01c1c4594503400110062018407a01c90030300020070005504080040e01d0658150101521082d4182080181808000341030012070280204054142c0c0c103130300607401603030b484c024150000560342e494060701402e0105c400510a501e040d548440c8503000d461584040340000d0b0820303000203 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 767918255 1250 767917005 767917019
    0xe0706141e030c040303030b1206060f0a0f06030629190309060c030b031002040305151f0e01180b0328020d0506040209011d0f041a0a09030210060f 65
    0x500152074400c44161420151034941941c1c000a41c0581c0310b502e00140c2d51402d40c1801360690741a106d00311301541000f20007010782e44d00401c10b950028401c0300c903088089142c0001840904a5811110f88c055100000280c8244c00d40d000800310394082210603c0c3c01c100e003016040341c110b41d44001c403000d0010868114201d07422a64141c2128003810001010001520360604486135009414082aa2400a0340035231404201d0345040d440d0fa04419450710b4215960207454020b0865000000c02c20040801c28550f4014002c900d0252550025000d880e81d0f0764002c40c4402c1c0038480c80346000801e0740507118031512801801c90610000c1c004041a00d00140044028041102c3c040c280d200314015600050b0349020036500c0607401030380100341c40d06144c010402c0340c0006074030003e0102008517541c04240402030201c0d070722000c0b1500c0024280d0b0346041015020b03524016844000004500700044141d103944a8215a40241d08559149419400040445200740101d021043d03100804020f42 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 767919505 1250 767918255 767918257
    0x30703051612030c1b1502070503160c0311010906020c0904030e060a08040c120f0624080a050f01020301060c0809060c0d4d07051504030302010e070614 67
    0x4409242044a1080242e01c407525030019482140300082c1d1540500c01c0242d40c09103115041c0c0079140c110004c071894507522803494419807246600400e8000c158081841410700a5801401d2101e2246100c015a4134200941c40c200d03000032541c03075010091010655204007141810341e40650005d2103138695010411442c60b200802c12030400c14600090403494803500042c204000d425180c848445c101381c504108000710a400c000603201086440030080b81d03e12070003040c2140c22131382c001001c010000c034983c1040c222000c52050840100f01c00103e2070740001c0c11103030403030262056400020294001900380d110078481c01c1c1c00030340700304c2c20b0401049484c8000c01c2c0c1507000070400e074a0105210640c50601004052850110b0404c0c0800381105203a81494411030300b8100700710f8041d82c05100b81d042130342d0b40e112080d40e2070720340401d0740c58450b00100802000740030010644405064070841403842c3c9d500c240002c8005500340485507168540004580040d100c0584420030050828520400e40e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 767920755 1250 767919505 767919517
    0x8040c1221080f280c0306090f02121b07020910060e0904050d0f02030d05010f030201091706070c020301090c0803130501030501030803040b33040b091306020f0403051e010506011103070305 83
    0x5209020002851113600e40704100e5050000d8a000c145240342c038140c0e8080740e04003440784031294010801030f010485a084056880b00c4a00c80c0c617510540080e00fa91007500070410b0081d0803171030b0703481401030080085036a0b901300d81c41c6a45140d485138614040c00701c000d0081d10014040c0c0c1c850b0600c00c0010b800b614a20105964a20481c3d04040000801c90250f0360b082e444400781000b411424425035030301c403501c14003415004900c404107000b0780002c1a03450350000c102204020407170503003c046580a412208045030400649484c560b00c1e80b21640e00c9070b0008000048004888034001099406401102d0480740c011000c1400c5645a40711050503010041058901c8002c4550074034803942000c5035001500125000c21104c152084144030450300003d05041c840d01240040100b01e085110000340c1c0158000c80c090b858003001c1000317003c0c034022508014894010800e81d0200254041e10f00890040444001e00039516441c0054852040904000016810411403030b408280250000c0403 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 767922005 1250 767920755 767920801
    0x509060c07090504031b030504050f060405041406091003080d0209010201090b15011d0609010e010306050409031d15070605040f020a03230c0105090108040c1221080f 73
    0x22419520300291800c0c0352440d08001d080c1a6200240418140d100c0d202e02d05a025a000002c030b035030200c0d240501503009a201d5103106584440c00c045407a1200d03026940182800b030810712044e51112860f02403080b040311030b07078011040e0400240302001c0081c960341c11241c004450b107160950034200074000c2d520110f40b1505541d01c6200450004c1c4440c41020700c1011700b406041811220040018111f41e6145c005030b0007803030203e01d141d901c1e54820085170701c843c4003428001c08201701100168050265a445164450702e800f0720390083c19003020a00d4070b41100403d148402400303078070030014204601040610000300038040c40300028415480142c112f4011707034852000818aa00141080280f50001c9a008410384c040e904100c1e02100840c0030120010042c10451548a000820b1401800020b42c104000c01010501380f0a50050480241c491120160000074207414404000300c40c1a50071421000c0c9517142520721480340542034041d1100d40040355254840000da0b1000443c0e002c1102 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 767923255 1250 767922005 767922007
    0x1803020618030304060c030e040203100b030603150a0905070905091f0216080c0105070206012405161103151017010e1518030702210a171305060c0607050906 69
    0x70800ea5081010300020301e22507851203c4403100b4640140400c0600b0b8000c0d00071030060080c85044005014140c041c2d4502040460b200e41c1c03500e0000f031400100a645a0303100c0c040d541840980b5905420a6800d1401001210b2079a0790b28089901140c40488400c11507800c1602806002d400303103040c20705070601d088130250801101c02818910f1210703c503400c907945d9500007950342d50785a003802070301e5105c40180044c056640c501000010105102d02084003041d0090100074003240c0244140d6103840e040d40001584030314149420103400f80f4941910380700b03100d003030003417030aa445072440f007445800d000035103244451400d00807400c0200d40d449080e8595403940701c0c4e000240010080c0c51007500c0509286015814000a40c2c04140d10390005003203281c104002c2d44000d80c80c1c1c61070942d50320448021501c00c00003080f11190a0855021005210701a084191108011845c0103001903445110484030820707610030800c685407080183c4800640c10078000201d00341d0040024107840e010180110b = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 767924505 1250 767923255 767923297
    0x60221031b120a0e0102090901030204110409060b0703031b020c1c0602121f0b120a06030206070506010e0a02091f0e060d06080c100c260c061618030206 67
    0x8080c880d08840b4640d80004044400c0209001c81401441d5085280b40000c51915200c03102041c2105014040a8012074503001c10072020140c0c0300071100141026030082010b0f40c1c840d110080381d81d00c25081078001a0030309640803908600d89000c410903c00320340042c001e44030044203000c41d82a201041280c121603001d80540411560b00080201031040d5800304414a800c03060020390301c0c0f16101480f1000e103654003d0002110f20300440340c548160006080d80d95882e0300b581c50140049400c001d40000020554104011000510301d058a80b02c0304005c0c0182d89000ca0441280580e404082d0b01c028000d090301c844040069010304107001d10700c0c0542403001200081869503002c0c5454034001586d50408000409d1b05122030904003508481c4003140c01c101a20050a0815131a8090500c4885084041889480100d00390000006180c00c5407111200c0e405e15450301022039101080560040080e040346114668181c140540704081000150070340d0280f005c0d42c1c2082030076481d445110001 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 767925755 1250 767924505 767924551
    0x120d17070c12020c1206070203180a09110a020c1906110c21120405150307020a15020306010221030a1508010e010e071406040302040902010c0c061806022103 69
    0xe440b01c02403881d001450f410090409000000d280700c10103400541165062100d05680802160520140d000c2c0540f440121040055080d1007140c0c09040b00e10320f8900b0401d408100c000203020780c1c024580a80e0045840001405000d0304402c05015203100c0744a01031140c6d80c090107c9180e880084001c5450400842c4c000c202000940508000e100c8903449400a0101042050081c000c01c2d030490142014035001c089540c41040c4804800c0640012002070704c0e2602c00c01100d00002c1d00800b03503034194501051508000c0d0701c20343d41c090050140b1521007002c00407500337200190100504440d807a69a8100c4520300410740220001170402461f5000a1700740f000340600410183c0c40000080d4003205402c5591410703440368015105d502803554012125950b0009950031a60160341c0800d02414610040340d480110b00f000401c2d01e81e0b0344c1d6002c646164461101e10149000e2030803101695140c00040e40c0e16203030540401d0032000303980712010451144502944d0051844407404198403d9604 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 767927005 1250 767925755 767925773
    0xc03010504051011040f03020609150f07060b011704060510032a05091e060409060f0b09010501020a1e05071205030a08061806100e0604080309120d17070c 68
    0x1c06030b410781d010610701500c140d924402c0841010004030300c80d2900740750803030154040a1310701c1f01034030900300401c03056403517100c014030308081400c40080e1f1982da402039070f000840c40e044507205842251504010103006d50041e421300c00b54544000030004c0d20759856a40380068640182000d0140080042c000000342a1044004003411040300394004004408404058a001ca60000384101c00ba00c0c140f04803e4010541d02054a2404600d2000e035540d03100820060200700000a1215242c11140f080c01000c9902880d142c4408803030241c16031366100012a52850440000f41c16003005148021188126288581c40c940c400c400313403140a96112807002210480d40b1082c5d036950000520100d100c1d91089686500c42011a0482441480148000400c500050680c2e0142c0026170480032858043c2000b003200f0035004000f40e2759152150105502e81d00040c40d845d00900080103401041d06000c80c40d4070900703416a482014100075020070404000703024040c50280410502d07505d0200d60118 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 767928255 1250 767927005 767927011
    0x150e0304090c03050a0c080402090f0703110c01021803071d041406070206100605031605030a11160215040b120727140a140118170601031b080607030903020c030105 72
    0x24038001344500d00f0b0003e40c0b060301c0c0b001d00b0807000c2214100400006a486507211030300f0150b0550b001d07103280d884e1082500149100041100c80b000c001c5010224018150020200c1e24002d10000851500c03800070315903200c0060090813503250413403039050002c0445004031035119004d9540d804c1000014256036003003c06c01d031148401070308081e08100f844008030034000000e02c01850110b24518251042c01d00b01003400c003805080004c00008151a11819007016960030f00b0070418582d41c542243c2006945210010101e000c3c0c2d030f4421922801d4185501030b1001c442d407142e0014984001e880c203481680b03100815039018410003c82070b81466407202e403414046104a110041c01130308240c40b41040e0313003a0b070301e0481c41443c07126014010704200c4d000c910144c020a0074041d4044034240c15040907009241c10208090700501d40d4243c0b28500000c5080c1224002c2d020200e606005400502e900250350150460380c0d445040420700e603034400d03405009224000d105441540d10031000281c2500d44c15 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 767929505 1250 767928255 767928257
    0xf0e0102031204080417070515090d052b0804081e070c030506010501140c1b0d170d0c110705013b090601030c0801030b0903070b070306091107150e0304090c 69
    0x4102401074481900ca500c0c80e10040341b000b010024079000c0010312460400741c0003010048041415040d5440d54500c01d4011a4060140c4165400e000d030807070100c9100c2c8403042000904c2c51060100d541c0502c840a0003617411a041c58501b0b1142441e10200010704581744a000c581001008003045072082c004020314403940141c402075240ca40010441c1c2081d404060b10300008000340b1000a00c00603404100300c4041c569080302d291b0400020345480340c1c284000c5c140c046104a1140701e0400d0b04000c04202d2a025001c0040741c50340320301220890380c42091501240c0c00842c0038482e41d80520038420501da02e0150556441995810034041b0022248070708a4601c1c00c1140e881d80380c07408070441039005400307280c101b00801104000500c410018030002e800462598041804614184100c5589540040101515050104006004100c40c1c1b280c6600b1710704c1c00f681940c00151500c00c4500603070700b1001280801c02d4401d6008000d010345d004c03924091000300400642a091805250109449 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 767930755 1250 767929505 767929507
    0x201080105330a0e01050406051207020705040c0503011703130603050c16061a01030b061617030f010608091b0f1801120201140a090e100801050f091c0f0e010203120408 74
    0x3d410400380c01501c15003a8241800000d10050009951003000d5803030381d003806512000c60340c85aa40980c00c1a2054011942081c00c03d108500e10ba40c00900840c1202e034148800952444280c0800740c8900418803c10103000c015a003c1080500c00d412698000c4c0070b401002d464a182402d0100040e00d080e00110b0305903448184100224200040d03500e6111828241449000840c0e0000799041c800d500b003003c088200c00c401c04080c0301204c2051081d80c1010801e95603a418a58a40208003409108840c0010281c03000200303000004201c041c3c40141112240395400600e0b41000120000254000d803c22081c0c41801003c07141ca4401500914016584100615a6000041404030303020000c03609080c1c02c0002d4403041d42d0008000c404c036160030a12519035141c8451010710400b96070b014034100d40c00c140602403611800742c03219004500e940112501070050f030380100c00c021111b04102d0041000d0702001034103180200340404140c001441a00d01d005401404144561020b075410360700040 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 767932005 1250 767930755 767930767
    0x15020a0210090b030708250522090603060e0712080702092d06120c03060a052508070f0806030718140108211207182c13020108010533 59
    0x1401f5503000d14242c00c0082c40e20221044c065028180340b051110184008202504030b2030440b4442440e08050700c0010814400c17540e0302d0400201818603001c402c1c80a00405000044403040c0044000c10f5590011005091010f1602000a0510000c0c8241c03080008200a880c800d080e0710b08171b00c85030001144600103400c2c1326050200b407014444041102d5800410240d8881c3d40010b80103030b00102c07112000c6100d40d104040071006143d41d944200b000101c1c2c1d1038840507640c210031094802d00042c1e55800041701d000c40c3c100e94082c4140d40c1c3d150542c00c083c07400c0c0140c5001c000f1001c51b0300b1003407201260a403c0c0f100100362003002680406419001200d020b030401054107655044a00101505410002c1107100f030642881c02504070070034842ca100d402c203210100c02900100a0000e003043e00c410341c0c9981c0300d0030300c507440c0c2844115401c104203000901c1030211080c05030140b5010380d6080466824001404503903c0062100c1c1101c0302420720802c1c400d090b00c400c085040e80e010b05801d0b1158 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 767933255 1250 767932005 767932021
    0x721090b0705070b150d080d020c060c070b1801020c191707030915020a0204050a0c03200403020103020c010209090112030f0e0d02100314130c15020a0210090b030708 73
    0xa20141c840000c10408100c40c00214944042007038015064185005100019a00141c0080f0607810b00500c90039001c1398019828031076a000c2c0c4203018200301038890310756410038403104c0ca22555200501580758100412501e215401e600c0e00d40e0458540010714103046590321514103050882c404d0710781006910320000f00b10150a811b03805461006005040c940c1c0341d41c000c2c1000d60a4012185220300c0c920103040c415208000011003c0d8014000300401e040a41005003c1d040c1d2146800200382085821079000308584181d401c110542011541007600b194011030180d40034031400085c0c1d6400780b00c4209950b80c1c0c1d181980c000c210410301482c48034100e02e0060305440790b82e200d8009200100e40d83ca1660f0702d8020301ea0141c3c0303a04440062604000003419002800c45000c040306840c0000308001622403101c21400000c0c1c043c118036400b565035407802c0e00380340012160490040c0c20a040690050800601d4444101c2603424104407103900d50246808503002125410006140c020074080f40d4 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 767934505 1250 767933255 767933273
    0x1c0c0b0423040203070c14030405130e06070e030607030b010e0306070206060108090c030d0c061d03180603061516080705011d010e07051e030102031501020609071409072109 76
    0x5050705403403c1d4210301c0e20850242905070708400140041201d00610700c600b034001e00864010f08001803c6801a0015500c0c01c0010032002ca070040d520300c80c1c4408141054040c0040b4504004014000d00c000e0380c40d01002c0780502500c04405041c0306040b01d2010484c2d40910010b171140540354001e124914050000620340100600a580705402c004014456620041040c400a0310f81d8108041c40e10124039044005004000001c59030b4580791038040421403000c0010b2041244030307207030304460000240400c038140c0f00584030f0981c084d041861820034203110300c02a20700a103d541b00000296650f0b19994840d03030100e50300b1601d6941d2072050b1045422242c0740301d0303040710500008008c0c40081280341556405a4000c50b44514400d00c10303000c01001400500c02441c1029000795128108039000c81d51070000d00b00031601600500340021004000010718104898020701c5074081742e102c51b010f10400c0c030000b6040c64100040c0343e80302041301e02c0d8642121a0803452040c00a001d40b0182040310356 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 767935755 1250 767934505 767934569
    0xa030e031006090e161514070b07030605090601170f0c040302031507080f010302090f18011107170f040b180603070e0f040203070f050c0a0b0403021b0a03021c0c0b04 73
    0x44c2820305c4100344800590107900309401041801e000094172070140c0340751298015120010240710714007041101319941904140f04840055560315660b44a4800541351503401c0c0701201e803000c5054001441000d0704001541d001038030191300510f0140c50f90040390074404035030030703000100c42004103100480744d2158480354000018401c1c2403c030b5040d5030018031000b002804506030f028100d00803682012a0790103c540c1a202c1d8002040004081e07221820203400000003902e07030004c0312002c81d14010401003202c0c201400004154580760500d00000e01c0340e04034014462804500104030102600c7e508011400740c040350b29065842e00c0c1c0042008030305e00d903019201e030040e8014820300c0b010036004020401d00900311300741551100803181465240001d2110b000d84100c100c07105200615401043d1500c0308a0141e0f0300003060114142031100514062000035080701e0154100003020000c2e1a180411610401c1c942d4011035543c00800c6207174005400c52200359000000759005444000c0d80801 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 767937005 1250 767935755 767935783
    0xf0e03030f04090f0605041817040602061303051306031a0a03121d0618091b0415050c010507030e10051512070306020c0d030e0a050a030e031006090e 66
    0x200d08a0720304285042030282d449002d2055413207040081c5003030744682001000c0d16000d00108188a060b01c503840e00c80451000070744402c2c80030401c51540c40305980407034056900b16002000e2549840c00d2a16500303a1130039051f800c1101c1409a6188070054610950007400e580d0ba0124008c5d03003012240d2101148840c801c0c0c41450412800c0002034510b1380510200d0009003002c0c0e950340c420884509103410b442880750382c001000207941c2d01100c5000400d0401e0351040d11700141503624540c0600411140145440800700244410000c9030900021400e0000d1140fa01d9410f050345040e51500752a8151000c1020030b032260070030901e1901c1001100e183c030060003018005401d1001c4440004c20141000c00d0048018082d0554800d40c02c2060500941d07004008554034074850080b2500c480102403403800203230603c0c21142c061500095054969078210000d0181d001040d5002c1e07a10503002c8564580500a000d03203803400c22424403d40000b001285070101c0c002c001210184c1c04c0c0407405400384 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 767938255 1250 767937005 767937007
    0x40b0603063117040e0f040506151314250804020f06070f03051903020405030319030e07180c0306260c12010e0f010209060a1412070f0e0303 62
    0x12484541481c0b0807801403041071603101900810701035080340074541000150000d1001c9008508010030400103104644860452400d1900d802c0b00c00400d594060f10003a02641c400700c0891803000100d001540c05880042c2041050300c191290389040d1106000c014040766144410800c240340030a04401c2e50a645084a0741e0458004402030101031000d00040e002d0703141211850203c0c0c9a0104a0b0b00881c1c0091100030413101618008007035501840c04855001e40300c1c0d816082c1c0601034000c0e9419543c1c0203000d541410400e1ba4404c4002d0341d010500d004040d2928003e9034409014401c0d20050030b00d45031103c04150040f219001a2501d1804020405151400401404903d10082119480c007549501420300c2000f81084c034114111034480e51009001c03071802c8d40c84005500154222400e101a22280304400d0038082c200c0c0a250200d030f42248041000c10b114038420300740301000c2203800ca442401d1150f03605c00010403c408685a9002c00e500e00c0e81130f1401c0b40c00410010307002008030011 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 767939505 1250 767938255 767938261
    0x1104020406020a0830010617070c030302090d0804080309041d0303010e09150a0b2701120c03080c0309030601120201091809021504050f0406080c09190c08040b060306 73
    0x9607600b1481ca000703845804003141c00810300d172034140b0341042440e0070142d0040740c045501d03100344907903000c1c0702d03000208176032411121841c03490600141c41248251211020300080f524160041c0d40900410381e80010040704010014440d5406840507151584c015602e03520042c080c08220f422200745c4102ca080440e66159a41e08000b00b203a056403215040040c1ca034072188031b9140740c82c0442c0980c0386140381035800c000d112241603202c6952240e045401070814000c03103025100b031148400c00c410300f503020400180000060303884030756042841020403a5490341c1d25101c03101c00b50012a50180590000a40540a80340400100380034249001c94110380c0407072580080d00086040c482e1061018440c03500580c101c0d030a9101002c03164011788000740865506042c080e01380e003e401550312a40342c0c000c84803051700f41486020103580260000300001c0c90024204601800c00528100e0403202ca4400c0070344140303080c019a4114843c603120604075042c5494036212074040281f1b030a0099010b5410 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 767940755 1250 767939505 767939507
    0xf19091109030703060e031612030f02030907170c06070602030105180915060f091806160c020409020a05060c0601080c010305070c02010c0804050a032d05100213050901030308041104020406 83
    0x70f0001140d5001c9000242d8081c0000034504501030210003528078a8010100d0003030008110030300004107105c1c2e40070817020910b000800300303d01041e58031000c5544540c10500043d0f06500361000003150035000c03100c002a540c8005a40ba5106c1002141e2681c1c0100042001f0f007491820800324404641c01e543c01482c1080e200380d0389804d01e030480b80001c0c000301d000ca2555192640f640488c00c2020341508024038000d00c42c81a2074001c3c4600c200188200303c0046c9440e65440d12400386910b80360340c0d04603488155001c01018142005041e41d010919080006150303440500030605402014060300d16580f5000c0d40a0605c220a00464107240c1070000300981030350303c0020b034591240c1c2400c0040c502c25040c00c0c8003480f4002c980286070480010200842884107549030880600b900b10718604510603801c01c1c06c440000446002040365000518040714071007079030013501080081a4141032150b03a02e20000d00210804e03881980443d1100c0240000c1c8400c05a4021000c072065606600d0285002c030 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 767942005 1250 767940755 767940763
    0x160302150702030d030f1d150703110a050708090307120c080a0b0414100e0f0f16060818100b03060604051009020703020a0f05011b02010c120207020f1909110903 71
    0x107404010503030386c0d104210905816902c0380244500d00c2010400200d4482c404a540b010070b032000c1b00031200d0400001c1c40c514480c3c000d0587d00b404000310541800041c2c407064a594000c043c044403151b0081c000c50b86e1645041040c200141851400c40d512a10030742080c1403500881c0c0c02903011904100011404181c0c0760285e689c00c940d00401703032000500b803002141d00f4003006410441c404d40c00e0085940c0b0980e0002904442101f603001501c20030f80424901513a40c5032010190003084e00d110004200c114010003485521500125810100240b0081141d0500c8580142c2036440c691320400446207003002c01c00307154042426a8104014145500101d507204140d100d0009810340009007102014424040c0e00c5115a00c8001002d03e8081d030701d0010701900443c2c0012038a4103551210f000510b1050007580b908080503241c02440c2440c0c50009400f0303601007841603801000000e07890310b0903102d08107066039090b608240c0a60a9081403c1d01e81035502d043d252003488002030001143c9a6030200e = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 767943255 1250 767942005 767942023
    0xe10150e0d080d14070513170a03050a020a12080f070c030210020c010204090908030405060f070e040c091d0106021e070e100b040306090201020c0105040815061216030215070203 78
    0x550483c1d1188403c1400c400034055a1005450004040e000d00810a4210014001c800ca46122407101c041d00c07580b108818051801d054801e80e800720f4441c1d004280100028000c8840358415030b81e81445d59203695070600d58150340701000071940b6003004800108890041e0b005946880c28202841040d02c0007561283c50610b0118000e60004060403c0502581154010a80c2e240107001400103818103200a400c02c84058885000d4000002c5090895030485840b0384a6925060750007000c140a010041840411000501c10104000b0864143c0403000002c038007060400080c8660415000a0812803213030b0700500316020340341d000401418086400700170f44000801045c901c3c3d45403007101101245d507611031000440d00080200038080c5540015080368001c4e021a0004103842004440034800d900c112103d0360041c240711185045418000c0e900404000d01030203a00441c01c01d0607040a000fd0054000a68001030400850400a40e00b103036074242d05005500b00b072406d40210362680000 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 767944505 1250 767943255 767943263
    0x90405030d0609230c1902070806090a020a030807020a0302040f0507090e090a03030f0605041d1204141c02040c02011d011109060a030905010204090b0f0409081e040e10150e0d 77
    0x4c0000604285940700c00d940d0000018400005440f020710300194403001755000306000d07401114005880e0007000111080480e40c0070388040040c5103035840d02161500198400c0b82d229044510000140e0350301d001e9000050140b443c0001e403805d080d0005004107150741d111041e035403000341c02c102100d40c01007142e090a0b40c05040c00b0030311020081d401402441150030165115107000d40144d4000140c414014480801804030782c1800b0940500c01000d0049205a00211018544956032800e080a101c1c170654a6a88841c1e0070a555a00240030313201400b0740100141c0d550070041c24030030084541d051000300024020480900c42104001b0b061042c120082e000300000601e290201c1d00c00c4e031141545039006002151980e840e104120003401d8041c4400b440740c1030107411440710340b81c18451301032900d41c811b401c04d1030120392010811080c20030040342544030030144800100910b400102c0f42c45038481d15500e20f0940d013003030950309000114241e004200300c10300c8041501910750f0f000303500d0842e401c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 767945755 1250 767944505 767944571
    0x2060f0a0902010e06040f030c080a08090d030e0409120e0f0603060405100905012301050a0e130e030c07030b0f040b060f060f16020f151c0b090405030d0609 69
    0x403500061313941c40e01942200303801c00350000e0b0002d41240c42c0c01111064078480d11040101580c0c640b0074503500d040310307400540490000c019500c1c0d580382c240030002550f8402c1c2007401d820901440000c0450b280410140d508980d842c0403406459031140216240e101c04a0302d4103420105070001c51110701005241e90f0190f90b0310004030711070302e18030341c0e02d50002e09203547d051100c0c1d03031a01d68040c88089034482d440da45400d085c509112540c0a075050b0780003013140da9501d207800e468040c1040464102032062250880c0d40344103440302c6070720500c02040c21a100e6001040800e19528040d680807030002d000c0c140c08191001800300044081710038503001381e03084170600061000310002900c1e5101d40c02c03008071800320000390202c03500c0d0110308408005c0c2c001c0300d615640d14401d000f0311952083c0a1520a44d0400030801c948268014219658505000500020314240b4001c0880e100c041c065401f60742552000c60447c02e580c8407802148003820724040c3c00d000c48584442005010100e094100300074502d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 767947005 1250 767945755 767945771
    0x708071e09020c15090c1801080a1518030c05100b030604170f070b060a060206011401120e0a030504030b1b0a0309050c09010f060909020a05030c0c07260d02060f0a 72
    0x420008000902c03038503004c012650a0141c00344da521b840800d80170b405440a071100401003012010110704130740c008006040e8184540c0d41301031001d0107000d07100390f005070348842011003d44580c400403007044c420b44900103400b005051031880e08000c07c1c20344104d40c0c20420900c0c80c40d213000c1103490b04190301a40e12400090101c18800c4a40203c07001e25168940c0883c1c05410307c9000100f00d13000303800c2980c01100c02d03911400126103c240034010310785e0781903102070b4812095228416415921286403030010b81c0c1c542100c0308a0508013000429000210085410f0040c80421070300340da00f00380c1052055442c52003540f48003d20b03016452029007072603540d905c1f4070305000080c005040520b50040880240b50707161003120f502e5070711900410002902c1c071035000c5440c103014400c494182645450701030865480201c280015404130458010340e004001000445481d0b688956005a00c01c0c1c4602030440010010180b03008071210300841158002c2050000195004990940100030740303101007000e40e = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 767948255 1250 767947005 767947027
    0x1a0f0d030809010f0216020f030606011e050f03010f0f15080112030e0a0603051915030b091c030605011b0201080a05090a0b010b0a020c240d0f09050708071e0902 71
    0x100100b1001c000b14000901b00764103402070040b00f180c11717100700d030b4464080c103003081810743d41e4a040719000c1c0421844446000c450100c01c191221030f034600e01e800351415004440761006500700f03034403081755982d03050000e12401205d180c0b1840a401c490f42c541448921100d8003c218070010b00c50404031052038140c850074180b00e1080c6007012480641411b24440d0354000040050208903045d0f02c141030f0141e45003c2c0c0b80100d00074800c10948416034052201d0070761301c138408096005054641a4803c403400489000a00000100f10120070b48000901620308000901076030414480b80210f06d000756218030050386c00c402004e400441b40304001520740d50762200c1601c1d02c600d54602910b030320300800000601100100050445500560035641354207200b10030b000918400248600d191300d510640707444e401423000054080103074850804140404803031040021107405a0048d2982d0300b2480c41444941010000c940003803190584040d08045070b03610100b285183c0d8040c2c013009640004190320f9903 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 767949505 1250 767948255 767948261
    0xf0b0711150c09210d080a0204081c0c0f14070e041e0302010605060705250305060a0e0c04060b071704080a02120321010311040c0804020d0303110a02011a0f0d03080901 74
    0x482520082c4c84101c4540c0783c0c07807a40d42c1c00c50524480002e440c0d00000307403040d0110b000781c03001c965071230006203000d014404650420441003080c01c0c0811004a81c1c81c400300c2d00b80a4090384980c000c1001c545554901d250850070300085070010b4a56203501c10038000001e07003a044c0440780000f0245c1e00c141905a070305e0200d000d404a5444242d11140200343c2c4030a005c1c0202d401858800341103000c04000d40c42e515551141f031842e110141c010b0704140009aa114803076040740702c10800c000f00340e5542c03200b00e600050860302103410646e1003a00115180701008141a55040b200c042da0309541e040c18a48050b596485c0038600c0000d000708080340c000c0e035107507500f001075500e0035041d10343e032221072500c0040c000d614846c01d100aa4000c1201c0c4219210350815104545403007440c1c2da107074950381e07071681c09205e405032207041c0407030400d0358445c04c9220965030a4050f00300300450fa40045140c0c0b030040402616a82d50911040c4145e00c810005400c0385e4070a440014166410305001e03149941b000c03561401 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 767950755 1250 767949505 767949529
    0x206090409140d090509130305070b0c04180507030c0c0c0513020f040b070302100207020a03080306031501030b1801180303110f0c07180221130f0b0711150c09 70
    0x4901c01c0d010003c0000c0d801c2040c507401d44034240d40400c2540e8918080c0002110101c2c0f014021500400012000c01c4296040d160f00c144004402c91800396111500c440a6810521001085681d2030a0100650389800384101c01545841d198550014685030f551503201680705480c41118046208415900c19805072050300d0180da450688403680c07040c07107150a40c0841c5e401c130010b018011341207030024004e109981200e40c0185c103621003035095a440590561001e0034650340b500c201c000c2052082c809002c058080c40c0725109003401414500540744810741040f24444040c0d0504501f00345403507880c500d04107071580500d0041110307410b401d2001e40b1440342c103d040032103000005200120660003d6403c1c1111219007200c802c8081246001c0100d01801c3e4a580c0200700c01c2040c46004183c0b03102242d0402c003c0800220a04010b542e26404510400022903034441c40d04c0400120903001000c2800d405125409081240c2034030601c0c0b07141d21f00050251040c034101154440054a482241c00c0c0c6c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 767952005 1250 767950755 767950793
    0x3260a050a0b04050f06010212070803010b031b0a0917070810020919171c0203091e03010c080f0c0702010f050a180b130503070f05010509150f031e040206090409 71
    0x550520301c4030b0030303144c0e481210047e002d40b1824180c65240c03d440c0044500c42c50708070301e03041c1c256401d200c0007480a0f40003405c2443d00500c00499015140c00d07610041080703003400c2d12012541c9150130610303c610281c40022030310716000807800304050034000c81c0d1002480046900103988000550006035004408912042c40c3d101c800c002103080310a04101290448001d002c64134103060301a8580001e07034002030464010380083c000d850721030034407040c41c010801c4581a15140007040c03601007801c443e0081c800c40f0010358401c06000454150b980070b82d8200103078070640740c03420320130760000707403483c4030090b00c10040020006543c1d20451103001d040700703481010a0f00c00e20480c1d5a8408040c26040380c1c03004651040c5107500080d82d45000501c80080385d031219001384a552800c40151040e4002640da41c0d04500280300f440ca07034088200c0241041200c008800c0d44a042005112804241d441521242040c0780c50030301c4090381c0d42d041583d00042c421200480c5081542c41c02919106410388098 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 767953255 1250 767952005 767952011
    0x5070c030b0108030c0f01060621060801020a0e180106230f030103240606020601180212090d080a0207020f0d2f0f0118090c0513080a03260a050a0b04 66
    0x410f90240c00300c0100403041c1010111007107040841c00d542e088400911640c00400c5004c00003a4504001c2c2001c40c2903010500c1d4005481540d031000f0717a003660b100ca001c0d180040e0700010781020602d80180b4102003411400365160720303903040c01c0014000002181224010390080d403046640300480e00202c0b1041341c0c0010b196916540d4a1400e00001c9506140ba8484a0021f4203014021096841160300f11040d41d0300a292992030100400c12955100c0b43ea407000307603001c0250102a56422000c40c1c0030340d0302c0d40020017240781000f800900c04480900480d40305801044907801582d128240059102d0040b10710200c00c86c13071894000c80c1500e11101c481e45042c040700024a08803441d000c810040d4200791080c02c180940100111111065844245042c0c62291002d000b010201e607c8001c0c20000c03820001d02d00400e240301d1840c510703501c1c0c0c01800c442d88001007210806901c03450401d110000d10f410000c5424070218554400500107000b1000655901b00280a8940c250807403890302c04064020 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 767954505 1250 767953255 767953259
    0x20f07090e03131d0f07170c0c01060f060807091206020f0903060a0624050d090c12080307090501030b130f020d0e15010e0712090203150a0203060a0b0a090605070c030b01 75
    0x44c10750300d841d20401d2a1981800a40180280714016114401980e00e64610002c414940c0592030b1001c0d01074084900203000e4083c1a00c002d20800c0050190703c0503e900680c50308c2c4009141d400d00504050800101c05410030450001007400d0000c50350004026031070b8110004151900d0181414081e450310404003070209900259000c0015120841100401e51450406079104520800e209200040c420080d14400c00c0d4107500000d8080d10518281909581c0c1c0d00c103118500c00381440c144d455172400000c2c07100280e007001d104002020282001d0200346035140000300c500c4000303c2c4241105456419840004c201c40e81142c0d0300c08201c2c01c08019140f40f115080b5690004030b003d0007407440c481000810044401c10030684644615550701c1404840f804c910340240034a203200302d826201c2d5280c6a80e0040d200301c0c080e403142039100030050302e910b4040e040001d482c0310380e4031021004d03030100102d1502c03e0740b00c1030202c242d41072410180e64440840c540304411030000d500c0940010001800 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 767955755 1250 767954505 767954519
    0x30507080f030711011b091e0312020f010f0501050f0105031f090207060e1912091d150f0a150e04020d1509020301050604092a081006020f07090e0313 66
    0x5900c04d4a074680e802040080c18030781c00c40c0070b000c0e01241d00b00e020a040c40c0741040200c3c02000001c1840e1050000b554407281ea0355200d803040c03003440c4406800740c0c000350707204c04c91001c0034407035169041e440b404244515403600000c100c034544060b400c0e50400c540080044e103419500b450010b402182103003404503156852001380d000b500501c804440403800c00510021500340000c4007040f400d144822524a0b6640d550380c100c5a00e8001c10030b5040c031907240400503526160251000c040340c00041603c80528003182c0a010051072a02c2142c800c80d0041d048030240c3d20340c0b41c0b40000b40c509c810f040c00744032071031034200b550f281212600300c3e6400b900008a00209081c6034000c0320f40b28030203d00106840e40c072081424180d0100b406019081401803104101c5106c0030b420a800f41548042e501d801d80d0800044005220180030340d00b00891880d00030705c0041000c42c54010000d00c02031011700074a00702e100420b500d441003489114503030768035900310791540e40082c400c4443c5924984081c028a13551000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 767957005 1250 767955755 767955767
    0x70503012105161a0c0d0e03120d020d0507031a0f0f0a0801020a08010506030c0d02072d0311030f040e1b18010801050a050d0b10092c0307050703030507080f0307 71
    0x400715a45041c440c05a81c83c0c42113016a15068115000b51170a0395500400b2115242018011903040c82085102d00d40159101c0041c40c80d0011040c0c0580d0700c0d4910f600e00c40503254041c000700300309468480080a42070440b91182c100a000311140d204400818001820740d2100c411b105502500c802c43c0003900000550050041805c0c42d101d540f10b036070740e81042006074001206c00403000380e01000440301e016010f900400c405440740741d41c468001354400c0c10490103030308052014410510f2124103828160084104810082120002d502d0301401c408100c1c0580030300c7c07190351590040c100114040c4140f02aa06400326402050a074682c5010070507024036401b01c00000b4041009680082420308110201c80166100504485d901c0f4005070f0781c2e04400b0b14020004503c00d1207240000c102c0c05414040c0d01d00070f080242e000200c40480d10359004818412046020711684100a240700140c00824001d04498040c00c029840780300f00e0820710300c81d00ca4800d20b403015110010130086d500390008 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 767958255 1250 767957005 767957009
    0x13060e04110108070909022101080309010201050a0204061b0203030c03070305040608060904080711010c020a0f060315050a060503130f061b090612020d02070507080604020909010507050301210516 86
    0x4074580e80c00142140192860f180c15110400002d410501c24080c00741071b5001046046c1120080c0780c0020011800b04140031800e8020b00b070300e5080003d03035021035a0709000741d9402c81c010b0442185403502d4403030040e00d00e514412030f8032070880042c4041015594140103032401c81400a00703072a510107041c03800420b59405409800e0202d1040720210343d40782014100c4900c1079500c071419900e0b004040d101c1074000244501e04030704000308586050010303262041d140c4000c3c4200707c3c0c1c14580303501308400030301580d11848074400f221f0450390080007030740c1d03810b10f4a400726200c6040055598440196008403c075034440c01505c0310070055402020050307283e01c1105000703100600081004188807040b1000c0340b50f481949d00246140c107010300c01c4245a40181600180c00b100149031100c103503645400c0000e035600030820754204c90f0400040d030900d4861640d0104460000300068540840d010b1b000b030006000380314048a00186040103d40d19002485a0a030005d003105e80c4201040c3c01c50700d01c10701d54 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 767959505 1250 767958255 767958263
    0x130c03060b18120102030f0604020c0f150108010b011d09060303040e0f070f2c0f04050c04090605101707030e0615010311091c0807080a0302180109060e0108040213060e04 75
    0x2c030143e40e0000c41842520700881e891b0f15100ca007500c8801c10840a0741210f0246120f82c01282000204900108040c0101000403010480c417036242140c100d00316600c01c1040ea051061401d0030ba00d6601218041000b0480304503800318060700e803500405e01e1402241c00c03041201030007000748000c0070816043c031441802165036101d00301c41030b43c1080750440c02c000d00016410103e144050030180009801d6000c454000d0030341080c00c0c0414000070142c0d070701520041d104000014060001c0707150f90260f00060b00d0259850500d0085030040100404100c040d02507091009034040741d001c40c820b8109200d80c1300250112590360a000c20b07001c0341241c041c040700e40403d00c0d1000d10f2441a516005460300541d0003843c1110035600d4981100110281302c070125038034401005500c0003d410003000c0c1c0100c1429982c016250a207507507290014160321840541070011070001041150303440441000002020329204200c0e88aa1000c11110007400c0043c070302c01810901d010a1811444000750700c0303036000f = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 767960755 1250 767959505 767959519
    0x60124030c1b081e0d0b0a08030d0c09030f080a030507180b0304050c0a08060403090e1506070c05100c031b080a0c0507050a03030c05010c0806130c03060b18 69
    0x14110680844580505460100ba46198188840481a462200c80314020b40800340b4040b801511031138003034041699032003000404100304200d00b00c140710f03902d0400002d8844a090300c1c10103060603928021546903401c49500c441501d08410310400803000113507445403a4000c01c940030f141ca03c185401041e12040000d20f130400140c403e40c4100192100300100c10041d60866051400800441e40700070b0054403184a200b59503111500c66010250080107900050440c60400f0f00e0000c0c52024554861100381b00400140b0038500c841502003090103004440c1a0786d0f0f00b900b85014001c40e600c56000b00d90040c0030000300e0b080c4580002100c1d00749813091392140704040303104070800810030301c603000a00610810310815242c28041c80008060b6030040b02100c1c030050b42d90340056811205508110700180001502508010090240801e4030314182020348007483c000021800d811a051100056940c80304000350140340039903c5140541140210f595507100d03040000001940ba80e6060742c01042 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 767962005 1250 767960755 767960819
    0x1306080115050a0b090402160615060503090705091f0303020705030709090b0a0908070f05030901122306210606120a030c03050325080402190501090902030c04080601 73
    0x628001c0209850b00200181c440034100401012980c20449000340c2140c0e00700141c140203810556480b0b541d62149001051040208003840e0340e0550304d40c06102401424021700406820220349942a98030642e01c20380b0540d90380044159030001c0d41400d4103d40d0107881c0110916501040c00340503603400703600f142c00240da42c0700300704111000110043c101c92100d20100d500ea484940100c0740003401501c28a003054103949448030400242d8004131100d91001400c031049503000302600b000c0b08040e0204100014a01d003007240000702c849400001e00074008006151551183c80590b0714403030b2100a2880d60310400c00442d510103051b03c03198070070031041d84c1441c1e26a50004042c4001c80e4145d0301c108000b440e0380d0342035809401c05071041400745401415800309101ea070a00300780800350340c1e40c0d4000c141414014051083c43c40103590902517014801400380ba60408006030843e000c0300401640c079a9200f1101c20705014680000074140541c60000540b9a8915103100440e0310b10303001548450 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 767963255 1250 767962005 767962031
    0x20403081201031e0f06020c030c1f060b0c0d030e100e0f0705121e151e0a0510030b190c0f081f0b0901030902030d091701050408161113060801 63
    0x811360307180c02401050741321400c0300010016005000400c1038a02160304041401c14000d05100704400c110803142860103000311030b1041d500030325000302880f2600516020400e800c10b0f031565840b2642c0c83c141902c90042802c0c40c00c08100c107850301603036040104244000c0d0030308103403580490703d036604240c0b0903035901003424900300e14000c404056030402056514082800000c10404410041801c4d01a000b500c9840682c10210584201c0000405510b800002170040c03403404400380038008a10b180104003c10202c9260860b01038a421070038021880c1d482241d650303d0010300d801e100d080c0381c4c03c00b2a000903d0390441041018120591540203d9a45050204504440c080340196540100d8082040040402802480d0a0354185404101c00c50315402203841e0845141c80350002038945030003044403050442e0712541c1014001c0c004c0c09281000c0e1101c60350f034002d1a400c010300d201001d411030200090b0303544440100301c0103411140c081008034040f000414691080031055401c1086d150420 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 767964505 1250 767963255 767963303
    0x80d11010b040c4a240a180b0706020307080a060b09011d041401030213090308040b0702100c11010e0a05030909060d0c030809040b030a150f0e0a0c0623120a02040308120103 76
    0x203c17020a404074148031001400301d40d0701c002e00045844184240d2004500b001440b0010710100740103540140e500c9c10f003044002c1c80b5080080c0302c000d52524040044c400b030490f420032202425024070382a11041220308003080714051488415034864a440c01103140b64111404040c1240d0086400b00300d000211882101502c550303183c000d00042203003000030006022441000c1d0401d00910449400c0d100d02c444003000c6a1341c402c82c000201c1d120000481000a09018115003580a40060f1207595030a90343c50781e8a00072038490760300c075981440000e0070b42c2d201d50800107038490300244014200c99407400c0c01d0070242c0c400f400c1140902d09040e080c0d00c0d1f034200011500c6909501c032410103595003400740c9113401082c0240079109a50389944218690070000c1145030101070180c000c06070100e1400030054442c214001d400070100c14441200d070b1141030344800361455036171940540200c84c2c0d24058543c000784101d40006100b24400700d100803240441d154103d0590740316003410342c44c02207454000000c03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 767965755 1250 767964505 767964559
    0xa0605061306200d1812080f180603010e0a06050604050f0f0418081201150503040f030c08160b091f15080d11010b040c4a 54
    0x5400d2000c40c0402001c0d102e0b6091080b240e40ca07203000441090b41d0fa4409050101d02c050f200c00284420101c0000030461096580040081441045d0142d0341640c2d0b5220501401280740204207000c56954645003021111301c05021b4020500c070358a41c2c42e59010305c0c0300001a034180ca1428603040d03000c601820b0000403601516001007000b100003054000700640c1c00300d100340702034202d0b4803194081d42805c401b240d42941c852295580b6501c1d25225002c03600b403290160302030700300c00c0c100e1014030060710380240889401c0350b04621010402d204604060f40d004588040040408800084040540c45d041c1c003c185198440e403d016110f07200d8079000742d5a041941105041000c01c08150003500c1c0107a4081d020110042c607100380c0f0296690002810140c0b2a001003003ca4285241c00c094500280704403421010122800c01a8928201000b042001e01d03041b55440c4070110000d41c104019145c00007100804080c560b030200010406240c0700840700c04005601070309031010484003000785140c2587c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 767967005 1250 767965755 767965777
    0x3020a050313210e03010f021206090c0717041e0f050d1110081f060e0919110c010c0314040f020d05030c1b0603090601140402210a060506 61
    0x30440c2c96071002142c0c0707801003000031540c260440310082440060b514500d80b8504032501c07902081c140d00c07028542928140705011505500c1008521540e4200c1041d6a40088003034607002074541c0c441411407100e104d001b10103400c101014040c050420244c2000304143c510314900b00c18003200341001c43c2510080d0b07006103000450080e00900050600c1c0c07080d0400d10380038030b0414181340c926002154456030094550800180003204021140a402c0f100110320008240d11003a0140340c88002002c0c00c0036004014810084080410224140300869106051000004001a54043c180d0140310f601842e115901da50801d102c072240f481c00307449101d840e90741e1080c00450940c1c2d155102c0c4590821048103d0703003c52607820301d60204400304080c060782c039a0303140207001e80c002d2019071040e1802c00d00c1c030080c484c000400400c200c07520003149082c1120000c03155900168100c400080190140c100010071000c020100700d854984042400c502400c2054410003c0c03d0303ca0302840000c1c890420a08 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 767968255 1250 767967005 767967007
    0x1005160c0c06030506030a15020301090b031504081c14040b0711061302010512010b0706110712120e0a06140a090c14191824030f0c09050702060a0c03020a05 69
    0xb00c1c001d411582e032203030004080c0d5107045217030381d612004d01d200100c060702015130103c0180f104040c140b060050b40c0c0c0b000c170001c0c852a010002500c541001c0180000d090741d5010901641c400c1507010140a41030300503000f0700c034402a00c09004071521007190207a80b40070090380860344550140d02d1400f02c0240c0000981900d98940d0b000c0b014001c0d80000c1241000410000c420200002902490180001e00745060f44d448403804d003003090303071030101203501c40010030000c41002401090700c88a14007207604058402541130000302d801081034ac0c0c2100d60b28010781c0b4403d010446180d04c01d8030715010941940c01251202e02d0000d04641c1c220b08010127840c1018030074003548000f00c20340021960300a0112002c0c9500d44410100014141c2c000c50341550003030540504400c290069140b41c08545040003041031038108094243c0001d0721000c1e08440c80b00c120b5406000742004680041c0c61110018801030400090080d030300d50044030101200362800082403a002e1090003110703075a0b03890343e881c6 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 767969505 1250 767968255 767968259
    0x4080a08030912032403161404090b0c07151a13020d020f070302061f05061602030a030f080907241b03020123250c051005160c0c 57
    0x110200e5880034000c0000c51003034100410b81d88020384001c500c160800401882c0203200e02c42202510064009a14440e8011785c1040c580c8000c048804c1d8102c4200d400e07080c03284c90710b54001c40e00800c5224009072440c9000020031040402036001400007500c5003850b9440040c1c0e02d4504000c030342c030390540c2500d42c00004200c1c10441c071742860108180001751000518104085402c40101d80c0411044490350102151500c281074051000c0fa80c0185212003212020b07168a81d40c440b6032049000e440d125650120f4110079a20320048500c41e0a6805012600391082d1828040d2005890034400c000081c0e00c0c10000300c1941004c01c0a400701c51240131849158843d1002c6042281d03c0c0c040d0ba8020030090040c0d144410314195803003051940240c00015441c01005589040b0350560074114014005103030901900c2c240401048017010000000704100b142d29090840ba8a000c41101910900c9204a005820707030032948250300a80613840804c585010f004400e80d00070041c0e07036000d00803c03039030841 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 767970755 1250 767969505 767969513
    0x40b03030f071416030c06170a0c020f07031416030308060405151305041202010903120c0e090108060a1406030a020d02010e030f010501140f10030902040b0405010801020c1204080a 79
    0x581400792162207540e502c80c2c4a244041c4c58003c1c80f00c1500c0030003c0c4080100141b100d5080550007401c82890314107107402d1710003000042002d0142103131200580c0c8005080e0003600c02d000354500000140103482001760b49050600c007074250701010314081e0083e084003100c00c05501c60105c045943c0f544448459079100703070800c401000018030924500001d00040101c80d13a13400000560000d40190003d0b290805003001c10303529114008100030b6a15040301c86c80401c0d0880e0500c42881000399000c035a6600350030381160b901d0b4100440d1034001d0b9080700045012400443d641d84103a00c41c0b1400c1115048a0300140c8050301c050741e41c85d405d504411842409420b204c10010714080c01810900c6481450030003103494200f5912104000d030355510018025a05c07428580e00c0322803012a01014522034620009031281c01c0e0294007401e06646010070021926150403545100300001c00800c84c0703603940c00000307010b5807001d000400180610700f10b40c03848120710010f8602392894600108190380d45170762 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 767972005 1250 767970755 767970757
    0x1208090d0c02061201081029060c21041403012a020f161d04210207030501090c0311240f070c06091505030c0a0806040902031005060a05040b03030f 65
    0x800743d030440703400c00190010030120755845000341114001002c1102d1003100d0710048840e1200c0c001d0111810301007600594241d9242211b011408460166860845000c410300e0103040540780b4180988011a10031068144005001125620a90664003c1103442010300721036000c070f08000c50341146182008414422640d4400c61904c0380102d1b40814803901c50035190000120030a1500c0649402c03c1c4644c17411011f241004694083c180c03502418150f0f2409070015040c43c03400203108100c0c15142d2308910070450b2000568100000700401102c0b818103100d41c0c55140000d4503055019a086030083c10004150340d05c96400c00070342480040382c5904151960301580b840b000280080c00300d0000310349002a450020156a101c854907a13141101400c0c101d249013206000707000b014020130000c20307a1344003242d0420078280341c0040d02e9a9020009801051681e0340650148900001944a80441e82c0514020202210481500350f519010001036a00e02c007a890b4040e0010711000704585030f280 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 767973255 1250 767972005 767972027
    0x6050306131407140a0905010b0d15030b0708100503060712022d0706062102010309080c03030708062d130e0a0b062d0f031c09031208090d 61
    0x50389007541c0320a2001024a003900981184c00e00d100c40340c0700780102d85041c41d40600100a09002407001c0d6160040d0a40203002d025600142c1917110302c1294030300401c60b0511409554040c07402c4149007031180c3d000300250030071200001c944080801c007003038910f8002810352240f100f655038500010900e140c800040c0d041400580d0300c5040c0d12036032081c01c10200454100410902030810740b10103a9080400603158240d00894074541c00580b07004500307851070011b61a141d0203003404a528252450404100d00c6100300700c850381c0c000841030202c4a0b510101d8580a52070071680d42c0241c40e022881b80100c1d504030781c0250010a81c941a018184c1481e686500d501300211800150a4501030003490400c211a4411a07655201c682000481d00d0305090604030070202d4044000c400140c101205c00c6001c80401481c803499030490202040c0d0f9040141f030109483d03502d0003031140149010058a548080d010803150381c50352019a01c9030328070586003540301e000010001c0001482400c402e469202c070003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 767974505 1250 767973255 767973263
    0x50918010e1810020406030e2808090f180406060b0c10110d0903080a0f0204140d02030c0604080c1c08040b0f040b19110c01120e0c03010e060601120605030613 70
    0x2200e03440f00c0d12912031026000400d03580d1004035503000c04000300d0b03080c04000c8042a80c481601c6042d0380c01c003076421014000b1203500c4100700c1e03983e40741c0e0b0001945800031081c0143c1e02c2440d03407000802304104110a20f014621030001409460703161035036110580102d200c2558170b5800000e40b4001826036810802140b80100401458607902c0e500d40382c00d4030391512042c0c01240700078050000050071440707080c203003850b088800c5051900b0302d0310306400d002c0d0b800c0d4458400c241c01c00e0780c8400d540e03082c000b00b0314100005188946d600c0e0b4401003140c40ea10301c2d085441c40350320074410000c014180501c8200d040380e884403080e850325082403080b00c110340141c003030003088150074440802d070200044010815182440800ea460300300b010b4000300b9500400c00012034a4100006200d4240d81282c0c40291000b019400400d582200c8204d4070319040125585582c15800d04210050100b4040303400c03401130a081c0c1c6c0310500044418104c0b03050300c65601c20341e90154400c0700042c1d241c203002e100c401901d900c5 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 767975755 1250 767974505 767974513
    0xf06070e0112090c06020304360b011205090601050f030a080306041806050a0510060c050709020318070f060f02190809040e1e011506080f040c15050918010e18 70
    0x3e074a1350003c201e4140c200c00090390000505001869078890b40d404207240d15080d02c61860320400c8101030040c05129204511600c888a20500742e01500000b481c02d0800038041005140c074a1342c02e0390311302c403c0c4109402040607d02e005000c2c02e0203d6940710054000c060980f654482d0303024007006042c072034005d5160a12020403900015440e0085038007595034101c022480b81030000807600e08011907404002072041d9058164005200451207100300d56101100507240c1e529014050a64450941c00c81941c0c01400004500440d404064009903405503440203101c4140e071400f642e560f81e03107508880d00032480d007407403d000a21100040c880004040d001103895000c0001301850445c40003600081c1c2009106a280142d03400d100d80c0d04180d1a501c0c0d01d0301c00525005000d081c5401c0a070088945161071000682800145a6150024030000803402d050603888038004016801c1209203a109040c1c1014504112194288143c16181d01c0701c203040071307a120108000d09080c030505e400300076801 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 767977005 1250 767975755 767975771
    0x10312030e06040501060302090709031a10050301061217030609011a07210f030c05040e0a0e03040b071703010312030203060103060503070b09040608060121060207061d0f06070e0112 80
    0x1c000d00140340290700c21000854220304610402c000c4e000018282001c01060f604100302180704d1076900c2003031407800821300440d80c8424104140040356600b1181e0150708000b00059041c251001c1d084800340544180c00703074001d41040d207020621081c2d88281d4400104e1005100322100a0295039422004440c05031601c0d070590b54a0142140f480200441c110542215104040d00201040902e014902c2c082011a841e05009040c5000364040c80024141d8400091071010040e4000f090048184044985460351481080b5465004030001c607030101e85202030007001c559010541c1c0c16282c0c441041000c500007c4011402900300601d050304068540c400020561000c0c40250060b0240300440c40e40c0d002d0b40c00c14001030350441c0c3d1056086610042c01080301451404038008030201002c107044c00c202d80390504802a000b48800605194034044480c884949074a00c0000c0103115102624002d10b5a083d8980c0c4076101120039401042100d5060551503200c0c03141030019181c2a100016901c0d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 767978255 1250 767977005 767977031
    0x52202070b10090513050304061812060e0f1219031b022109090105150706060e040c0801020304110405060d0c0308090f1002070510030e19030f02010c0801031203 71
    0xe4820b039440c0074082400b90052040621038080c417a40000600e08006940384140d0f185503491050f03100308002c1010380c10909420518881d01d400c001c003100300b041e50a21082d42041402041181c0514410744100301100701910404200840c1e40161100e095003403102103001d0449584074240c6450425035110302100a407184003918040700707021070740105080350150010b00c2c0256205a0540c2c1c0e2008103114a503403907903402e568581554400c1d80c0442d0b09515010342c08105005075071000f0141d070308241c030109035405941c00403441640200c003c18074007513680010908074072040d03602501c038038101010f0303481c6810079402080c2c03c0f0720081c04c1900c40c1c2d44552503110380040c1e1504110b44501000030704280918244008140101d4100c0d82200007403c1000060f650702600d00c0349900402c5c03052001c510690199001c4081c80001401340e030541d00f09642d8010999440c0310b02103000c106001c2c21095a0380c41403242d888401465154002d0b1079083d0740b6503038400c995002905080503200c0820500207 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 767979505 1250 767978255 767978273
    0x240302070f030e090c0403080f0703020c03030403121e02190519110f06030915040501140711060106050a0f030b030304080a03050322030e0f0a0503030c070801060f05220207 76
    0x940c080c1d43c4269044580c8010003c5040d030180403603004074010b201c00c0c00490042c0c412035140c00c0300105020345e03c4401c2e00d000e03030800103014840307035060101042c00000d000402007503200002e02c642da0150b070400e14030a440c02100e8402e4001d40183d200306054100030907a00c00c840c1145002d003080354002c00381e807188401481101c0f90110740546491080800305c0c240a0031905034404100c4905055241c100002d0359142c003e9141c400c03d0800c08404203082c000c0a43c00001d845d0756038002200c8602e001a0081c1c45603044102c4c101d03c0340f2501c000007600a01c1801601c030601c00710f40d946201d280038494101c0261640c00d103040d602d40000c01c0005200b0804101501ca414403d48032542c691500176001f05401410f001a1018860500e1800b000203500116400f45810100c940914040351480070960200c0c02d0b4220176054440041d4498000e000003072010100d0302400002c0c4031390b41d29a03000ca842458584101e941042074081c042001310b5141022280040c00040d00605205454031b4030440 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 767980755 1250 767979505 767979533
    0x31b0b1008010509190f0321060509070216062f0c180c0318161e1406070210021c0c02010f020118020909010b130e1624030207 56
    0x10424a608040290074000c1c001c20394040d1105003d0036207903058074000a418000d1110003440404004178842c00c143c01012501c0381c401881c0e50700000420403080b55030003410240280c0c1e101d14449000a01402d100045050105500f100c0b001e03d850314005040d159003255214540c2c0200b40003680035202d6540071211075149500e40024659044140705002c0a140500c1d0005a1b905440c0301f0440d00c3c10028041740d0300704084080b072801c070200a6440b1414195200546150341968520018100c01c1e02c0c0e00914140000c5000c61801564940091071940c0107500080c0c3c000c41e0502c004009450030104596408244d8019600810400505c40c007a941c6002400f602103140d0382111340c19540d02c04140c1c003c04980d40020444481d1050380044581c103080002403003444c0703941c006603201ca029000301c0071701103001e04040141d0018000030405820303a8484201c207445032100c5030f0400381c080d82c250001ca03101d040d00e404d0301103102410702d2050880c210704581415020480440060240b0302d450003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 767982005 1250 767980755 767980771
    0x102070b0f010545040506180c1c020a050a08031c02040b0304061508010f020d0c090501140c01150611010c0207060e06092413060305070c031b0b 64
    0x400e03240c8429180d19894040c0c005074000c118080450802d0808240a011212500b222500c0002c6070400000d55501d019035003007403540110070500042000c0010714030f014460381d0501056140410150581d0b580313007110710780e41c030030620007829012303070125403a490545001031700554400b510782d004500408500d41c84010280c0c00011800f100e2403c044d054003440b9110102545014500210410741f0301000c2e101410b4559221980b03100704901500400042c01c0c6440240b041d05d0030006000c3c02174101072004110603007041044072803148140310342019244141c5414000d034912001c02e07107440e0840d401c005442d66860f80c4140200d29401c000700003c01250761081c950300d1601100ca425204294081b0056500100d41070000681080c80b01c5900281610b429480e4030818001901c1884080a50340b010f207c0b180c040c004158100004200310205c0200119640b541c03803900b101103900484119001500a000c03207000280704884080401d90f14619280741d03201aa00e400d80000c00c2600d00035 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 767983255 1250 767982005 767982023
    0x60605030f060604060c1104090b0a06061403270705031c0201140c03012c090304060809031305060711040f0e010c0207030b01090b01140f1312020d080f0c010207 71
    0x68070203000840c0c0c030340c000019219603080c54a04000504a94010100100f0700e840b054051007440d140c66010180b21900480803c00d14100030030300000414003805004002208440076500501d042001c8074010102000c100a06151180c25015002d030300750b0649019024035500025265403c02c09a003a031440e0f506980066205403801900f151000c1804d40c010707200060811800c0038804050728111740d10502c422082c4807aa0250b1903002495603440a5140d4909040c014030540000c09032050f6800c5882e180480d403a900300d4a50384e4010800c0e48044061071910034051402c05102401c6040d02c00e00c466011b9821910006041c0c0c0c008908580c4070b2559000c001c4200d9009014601140f0002d002419005046860381100113405001d800c01003a150303000c85000307034441e2410a0500a424500742d8981e1041d040b20b039410b0307205510b0311108118990300440e200052600a150b0280c0c006d00756912100e495035441c0f140d0f000f00c1c15820050505209096003800d00380001c00b081440345102e1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 767984505 1250 767983255 767983261
    0xc06020d0204141e130e150f01170d180902030f0f0601090e132109080d0305160c0816060f05090d020d0e0a230301050c130909020604050406060503 65
    0x1120f079000100d02c158400c00c8001d29003c060b6005811030800d40c43c0541d0b015450018000401d0083c001071558011684220014518030701c0709403440758000c58a802c48141c85903aa1002c3c007610100300c140340701003500711506940340c5501402049000d9400c001d0050100d540d900042000c98004503058012605208100206203007440c00f095800072003400c003000c0c241d04280a048201c1c00003031481c81c5000c00078900700c051150041411210440008e03582441f24840040201524082d12402486200b04030388680020b0080c01614412015807042800c81c200f0b500c41210b5140d40d00c00c0582d01d41d03034104002c3c010600c510342d21000c100d0240074003007001450007000c2c40464074004c0100c544c0b900400c60341000700e5404078041451450616168141e002c5600002c0c100b85100e83c440c2c590401101d00744510003080609180750748200b10b00801c400d130b6608418003403610490100c440c1203040c03a02c0503c41034586a10030304d406030000c3c01240c04d20b61200007041c2228150727001003005c0781000c410 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 767985611 1106 767984505 767984519
    0x1b0f030519020d0b1c12031406010c030905040204080c0118060509120c03010c030507030c080601141b0d020303010305100608061801020919052e08070c06020d0204 72
    0x41d45000b40032849400095190021085610000b14406c03140400c0c020f100301300840c2102c101c1c0000950300c0740b00448000d600c800084050080360b25020401c0e403118800b81024003044001010a10260b100140c186849080b800a005204200c1404150350000030385210724010356010500003034040c800e40c24070410520312030f01513203132a1586002c03580c5500005d00503911038a041000c488000f02c12180e00d0310880d1a2401300300004501079120340d10000900c020601c25100c40e40a0012009207130601c01c5520202005910110051090020601174145604c9a0403800c000e2240381a042a0710307600d0041880c01e070b003600039250f100c45103829012981c854030001c000407406001c4800103c44130303986014040c061400f10b01803000d02c01c0d0010301d50907224803046002e900c51142c42400c4505000007071060040110903085000000c490780090407044007210009600c60f401d00c10 = true := by decide +kernel

theorem cover : BRFrame.Cov 767805755 767985611 := by
  have h0 := BRFrame.cov_init 767805755
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 767805755 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 767805755 ≤ n) (h2 : n < 767985611) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
