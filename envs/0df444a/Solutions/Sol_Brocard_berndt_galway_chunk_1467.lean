-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1467
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:07:43.32901+00:00
-- url     : https://prove2.me/submissions/b6da1af7-f8ee-4cc5-bb91-157e27700a70

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 263669064 ≤ n < 263848920 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 263670314 1250 263669064 263669069
    0x1b0804120302060f0f070f050307020a0506010b0d0c14030406020f160303020711040902010f03110c120901080115081504090501090b01091a03060103150b120303060901091a1011100b0a 81
    0x40c0703443c400411000d10f401c0307081c80c50187c50610b0144da84c0c1d074590034101d003400c0030307010004c20300e019181c00080c0500c1c0c106e01411420846407810494058010b4058643e0700550070b0039000d2290500000300840c000d9805050354480308400b0615000d00407480d2403018030301541c1100400e0340404e13684140f00c200320401c45071403001e0390108140001c0340c00181148510080c90410551a60360b04614203e08400b9201031030030040c12146210b412243c09510b64014280c1da0b030000c0c501100004e18131103a00c011154203515502d51101d1a168500180c400070f07412011503400c43d403940351000004400348100401280541c55000b9154113020b002c00507a00291002030800030040c40181903560042150303030442c1d0340480409070341d00c0f008014401621368500207aa0044544c2c902a0011714080010f620a00003180c9400c2243c0c1c0b80c401101c1291045580c403c0c2900700c510807001c44d03082c2040300b412107000030b080000d00381c02101d901600e0f00c0501c00000e00c0507030300c1c3d42e104a801e0401c560900007 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 263671564 1250 263670314 263670331
    0x40e040501091b0803120702010209220510050a12050102120103060e0d05180f0d0c060c030f0810090f140c0a02070506090d030f141201050f0409031b0804120302060f 73
    0x281c42d803130f24000654a009910110400b05a000d000c50003c40c000d43c11070b03441c40f101801e80c0c0303411004030490300c20038503500d00081403840c24000054411940c00c12581c007614001000c2007611400d01c4460309182044010813110366500b0010510110f51540c81c0900852041c90041490310008040c41d051074582e24504003801800e00c403003500c00a262000340703010001503900c6c40c01c14074245d002a030124294a80500211032040c03003c00c083d40d0110b480b400960003902c40441c80c04170514101c0302513400701d0700a80343c00030100e8140b1142c1d0f42600000201401c00d4000b00b01220803420034610307000c3c02e9804403c104800140210095018423088c4000c2c0380460340d66040001d1800170407a144440d0300d0090030044c0898403003a50901400d18070030a64014649152105150445907136a41000c0c0100c0d031040f442e03281c0e409820300d00750140c5420035600da50f9554800803650004540144d4211080f00d04100030310010910102101e0300c1452079000f54018107003400c260911070030100010b0321001 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 263672814 1250 263671564 263671613
    0x390d03050402010806010c0501060302060f0903160f030f08130b090a0902070809040213122d0f11011112070b0105120d0e0d14010c02100606020c0f06040e04050109 72
    0x70160383c0010041d5408a820308010703500068500d04503004203c01d4000a6000d00d01040c80c60460f06080068242c89109404580d034030802020200b0a103000e5124401c00610300600c10300008001071344103100c02d07218812660502c0303a801070701c1c4120740c1a40c116940f0001c02003404d42503413500f4020b01c002815008011450f14020b516180781c2c910902c40814040e40e00020044468003081c103080d40100810024107111002d103141c10780c07441c004a201500e8003010900c0a0302071505240051800d40d0f4004692000d90a0642c1c8001880c0c216211560600600d008049501c4005120642e12106500041c1e59960114903004020300c03010b80141e400b1b250114006680d20b5070000c0e400105e54514100510718080c5030000410308121900000e08981400c45050072540b4150001c1117510200d40036541e000324004483c0c03003211250f100311030041e4030082000ca03131030912218414101101620fa0303854551038006090704100c0c00c1d5000c0314030b80c0d5910441420b0200b00c010b08800144101c0262 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 263674064 1250 263672814 263672821
    0x9060f050f04211b030c0c03030801140405010e0411030705031f0c02061e04020f0402070503070204111c1d07151803020f0609010309151e05041205390d0305 69
    0x400031200102c020401c601120313000c20078580118506108a64000e0141c42100c1d101e1030000c0440e40c0c00e2040c1c0101d80014903440340710b45418004d160603940069906e0106650b00d481c0c108119840c2706541c0c0d010700441c100443e1381d0f282170000d41d4440001e88105800e12411f40904000c03030781c0003a000300440d0015020f1041d541c080c00245540c1d01c00030010100ba644541c00010001142441c2c1365a0207407000070403904008000c400f0380710283c000c5800b00a02c02d100741105080f0720840c8151409030b04400b03442140680c49903c6100300b005e10818001d00e4600301d6824901d8403c443d080f2104a401000400500d107a201d0114480c101248012501151071039001c034592624010764a40b0454010803031601c2644030f0750060324803a41103038200320b45a040514040052084542c05040060035503000283d40c0c0c543c0c040c10b405268800819a03100700c6071a070450b50703a001408008e050a110040514101d400d4451040440e4808884c1014282009a05900e840c0802014005260421042 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 263675314 1250 263674064 263674067
    0x31d06090a020108070201022802061b0301091e020a111b06040e280f0c080c040b0903030c01051513051504050711030708040f050603010807050409060f050f0421 71
    0x207600419030a09048203161600c2d01c099019010b100c6103446244440780d00a0005205d0a0041c0c0301c80324aa000e8840c552075001e00030003002041c0e44000d121510400040200440036480300128441c0c043c221021b1009a46043c030130380c0c0c000c510120000701d800d134206035503074401e0180d2010240717100c0d103030500d05a580d00404d005001e0f9120b1102c0104c080700000c0c06451500300c020b51104480c1e2000d2419810000085005064840c0da0000403403414a141d64100c2c01028440c2c01541c0b500111810517140c240440e201da0700c841212038041c0818007015010b0b12007400340c640158261003501035003080d41810f000b04015000000078119041c8000e00c05c844850040540a218040d240451965500174003641e0005c00ca00e81c80f5607a1100060040900c80100c2c00f410507a4207003400c400342940d4860130402c243c082070241c01402d4105d008100007a02e8150300941f8010302c208004200600d06400e1103044a00c00c0300d0703040c11620100c040108008600201034280300030001c8280c4690800e510 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 263676564 1250 263675314 263675323
    0xe2b08040f122d020315011a040501140307140403080c0c010503060915010e0612060307090b09190f0603030507141903051c050108030717160204200a031d0609 70
    0x414143c0528501205440c509450806505a80c0c01070708480c0f0444224890140001c1e09100c4e13a00c07100c42c0744110000000d0008112011142c05a6031072510b11134100a0200d20741c005811101400030082865940c0031100000d080218002e60044e0b40743c41402503020f0804400315020b90401400300208546030b55101001904500a281d031b00e24410b4001d00140d4103030030714040c419441103010a412200381610701303a0300d2040005409035200c441d07403a0b15003030980b2984022207500c81c403003200280a41d495042613410080c0890701c040b40e2443c56084480440e00c450b0010340004100040328818442000b06082541308400c00400008804080d590b01c080c414060090420000180d0050f40c401d04945002050745d00d001d0400c441d5a40b411069903030b40c80700800702c554810071029625012807200070744c0d44581b50b80c41c26a11823005582003000030b21110601d0421140c030b10b43e0041c802d16a603009040152441d403070000d880c40007804182080742c8100c204a02c00e0340840100640403a0225 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 263677814 1250 263676564 263676593
    0x2030a03050619030f0201020f100c02010b030a0b04031209120302070303180507060309020609090f0718060801090902032118031c050f040e040b010f06020d0e2b08040f12 75
    0x780e175001e4148403440101d060035800001c00040344100140544a001d07961b00c00d1581032004d07002000300110f4401815101c00c030244000c0e104060240c00075000c00c2c040d0056050141c41040005007080b503541d20130310725410304500c900c0041c0d0b001c40c18000f01501849950001030410811881800c420740d155542c0f0403190146004151b200d0b07480b6000c644a107416030701e8208000340f8110480c034041071413148022080318140000ba10300012614030300c6001e041c00c4191491075851401c268200030070324020340a0351404a82612502e100d9a22a50f000c3e4410130015001005d41c1d550740851600010740b50385085801c501c240c0014140380c190b4581d1040038600125a400c1c095200e64055029202038002d0342d10400602801c1001c01040000e00d14005060381d900410302450540c840200b01da450041030005408154003042d10030661a051405046c4005003900c0401c0d9482118015500310440010880f0382650103d070520135088030140550203004001e0881a14035103d842d41c40b1961040d4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 263679064 1250 263677814 263677823
    0x30524040c1802070b0a050a06150c060c0c060e011406010315090c05073503070804110613140301110a080a020d090605070e040e01050601050a050f130602030a0305061903 75
    0xb52030308803101d041ca4041d10f08494001c5d01d0f4030000d14150900c3d030003906007282e04880051070002e0100d80280c0d40440c22003a03101039a10b00162004941d1a14002c200c184540000d000c44950b80e100001c08034098881d40400300380010590501640b43d140318400003402c0c1c0381c1814104030707080900e400300e4141081107500c07110f03020541450342c603000d4806101e8000080d020140082d08600f0020403420707203070491070007005000c95102a032180b54905010582d01100000c0c0241e0100e40420702ca641ca45000c86002031051b8503102055004001d40d40c019400444808148022080c907403400307100b21450359107900d402c0d0340b8103003800d10001d00d48840100316101c4568041005c1060416503841051190740c0b14004015030305020401801c0a90800111845541420a5101100810300446001c1da6042c1c4490b400c01c00f1000017611180c01070080d8902c075000521034400718040c2c1c07000d10750043c8110340107144e40311381d00800101514002802180240c3d60140741141c40e415030114501142d821 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 263680314 1250 263679064 263679089
    0x90b060739180f06050a080303011a04180b01030b0907030b121203160c06050406050f1308041202060d0c0507120e0109150e0a0608010815090d0f0207030c030524040c 73
    0x1070b40f080003050315421450300300100b184003180100c400002103050381c1124900508003145040c200980744254017031000d141006250341503001d10b06801009441d04141408a00c510b01c2c03a02241002404558940001351501c224488905000c00c1c01400107240c100074002082c10680c0c014201d10010740052540545a4031004501d0301c50700407044059480340e004c0c849070034181000005403200b510040007c601510100d0600c13569442200a81e0b540a0401070401e403411005041c07454176010141d800140800ca82401d000c003c6c0b241c890074869544619450788510304000144880990841082c8800619480c0b00b0b03a0300150b01a0445034029400c01080d0f910302c070212141d100100140741c20080c0c01402050303040c0c024030000d050701c8004040b41d0b8014102ea035040c0d00c000c0191040714482d000f010200d510740d80f085210807580c440c2d13801103600141d90383d1b032580c12840a503031040d5042d800202c2c1054503042e20304d401c00340c1100070202461590406480f0900004803510415600610 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 263681564 1250 263680314 263680331
    0xc060320180a0902030405030415050702010806010503061201020705100510030b0105060703121d28020d02030a021314072a0c0f08010902030105070207030c090b06073918 75
    0x102d603100003010f498401c1c010354903405c1514280b070341ca81050042c183d074007004500c5000d049114200b0b5901c43e540503519100340303407034482c01980d495001600c59500042031403008050140300340003c0500902c104001d2401c440075202c100216035028000f0421980144c0040002c2003841000ca41903800864016950302c40ea450144c0c0e184074900320a050305402c003e00403014800c1c5540300c5170b001c0d003094141c885040904a8003100500441242015240b202c510040581050f4101940c080d03c0902110041d001c690001605000c80d48a04003009454007001d403280301c410074500d0f801c8031103414800c3e01410824104501d02c003120104d010b0b07641400c2001003d01c10444000c100500444081e5074036140c07900da000d4060004003034141d00035801c10010841c0c4030310019904041781c2e00501003541c55828100b445024106646040382d0000f41400000041031400034070070058410b580e40240d200c0a030f0400b895040d40511003140543c28444401c2000a0321611071140766241d04000240307521 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 263682814 1250 263681564 263681569
    0x910030203070e1c0c06030204080d03020d09080c060124051b070317121e0408070c180b040f050c22030b040302060f01080111040501030b03190c06032018 68
    0x240f14944d0b00181c00e10345a000c3c076901d030042c0318080d4002c05074451845e40b5040180e080c1c0c401d500c50140c059000124000c103183c8030794064401e84c0c0f48458080741000003030700c5400c0c0030b0b0000f0b540c5da01c443e00300311b004003c5203080314072103a102c2d10b02c005e40101c041618803000d4800e018400408410700104d54808411400c00c2c00150055648901c00c00400d962a14606865410402e03507400c1204d4184081385a00d80d40000c024001c00c11000c43e4181551640d542c0340954200c1c200858619010040101f044140740365024600000c0440004c0c00c3d015410821041e10081250010407074506814071400304250400c503010201c000140032000e410009820781186e4141d80064043e035207000600c810194040346003400780001001c401c82e01d03600c0e060124202c9481c0c1154145010307041000308050b50294000b1007036400010b080d00e6181403e0058180100340c080c00442c1c181d11801800d0111640510508100c00c800480c141035130069055412078501c02c044005141c600000380e01c18107503 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 263684064 1250 263682814 263682827
    0x1d0105030c0d0c030501050f030105040f0f0507030606060815010f080103080f130902030f01080706090608150d030210380d1202060720030d0f0f021308070506091003020307 76
    0x102c01d00b107010007101c150810300070b009042c28004c1c00c1c410b54907029130314101c2c07405020365401142c12018035812200d00b507441415021301c2c0e0318111410702070402e0000100c0c60310f01c20351008240e652151022850300c0b2009101c100159620107041c0007440521b42e02c2503a00c0039100d0b066070383c0a0003403692901d0440105d00c40e0f000b0004403901581d80250302042244041d009180034040c800c80c100c00b0380c3d0b00c58080980722045401182c0004440110400400c0e104420b01c0e0b4205402382d2945100004410115001c6c4008100c140c016900034181200302404502c0f809813500350724081042c42d0040388000031a0650342c2c3e04020b0344141100c0c0c0305140c50b0707620200042c450b42c0c030a444010801031303000060b4480300d041f50400e0110300320a40403051190440089100041c540020758a404110b04102c0c005102400120090654520743c0b81211701071403005140c407100f0492041b00781468900d07030900d0050381c0d41280780118000d0103001880c0d120304080100c03003840380c00c016132a50f4a04d182207440 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 263685314 1250 263684064 263684077
    0x30a1d0a03060204050a09060305031c061a13080303101202030330011202010c0204020705120a050c0c0a0609050909031c0507030b01170a151a0909071d0105030c 71
    0x1000c0e00c0001042144950092003100c0302911280d038420f13921f2500c841110924440039001e604104528500031610002e00544184880300c0064444d880d110012404030140c0740364440d0f200300082e0001410000e024400c010001e00303004524515155031283d00038041881070540030703200c403115081156000d000340c42146211101c220702c02e24150030500360810460303242150311464a0700114541030319034080200540c06844442c1c025541c0c1d402d0000940c07002c00300f078940d40101000c030b012651f1000d000341400c000641e212900d0f40d201000f15814008440003881c0b042c890b840040100070b170400410b200f2600300707d40c541c03070030f0b030340c0400b030609501c600414181d0410727140418080011071070307026901903135050760200700c08440c0c1e100660700e562403140315050288a660000304459016086802d00b29805c0541c0704800369036a1404c040780200c8803400300024004a010705603410803583d2103074008081c2c6001444000b0b501458407540c64403030b50203030400600000080c2d03283d030302c1400c8450 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 263686564 1250 263685314 263685319
    0xa050d050a060507020c12010207020d150f0f0203240d080a1710060e030c0918030909100501172401050408100605240301090b0f0a1413020c030a1d 65
    0x43c600d40454025100c41c010380361240718200d0221062080c0310144203564100d94003603d81031600441783c031800440c19224816009041d03c650300d00e40c22402e103000b64804c1e51180c0b0030241c1c80742031001d00c00c42a59030790102074402c2d00707204000161981e80d080a8003241500f003845280e40c1c1000000444076024040c0f03010f800211108244444180084540e008a03140c0340d4959003200740d920100760f01d4000101d407a070341c03001024020a660860784e21940c0e148820f1041148e2802030b01310041000c1c0041100c46a92030444101c08000d0b550b048288542d500200d91849646881e18810030500e00442030001d42440c030748000187c26030303402101110041c013549021203160350014400c06002d403010380038503070080907601c6a00b40c0e680d1030300040b400340390b21210034142160300b4641420024254548995403041c40081e107072065445a240c00c0010b130144400c02c1010340361000610042454848840c00781e02c6c03040010140030f801c0032040e04d00405641c0780a80e0266065118800c14010302c0741c2c42c41c1e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 263687814 1250 263686564 263686571
    0x711042304020103110c0a1b09090f02031507022808070b04050c040509030703110a0c0b210708070e0f0301240503030412020904031e03090201030b0f0a050d050a06 72
    0xc58440d19910a10641c07013641c00780106502c0400c0d00605000e80d0715004880d074800551400000c0100410346924100d4101c25103050f955030054030242c4100807000ea4101200082102c2541014448845069207115141c9900d0420050081d41e540e410b40000485410440e070507038401003150f0b014500c4c5a004000c2940f20300d010b040c10402010152001c032a20302c42c04090115a04160069500c80e8600001031810040e09880c1555640903d45000c1c26034012140c51000081ca1b084820010308921030420b61259414142524042c01c0341083e02d01c00d40a65007008051540080000d5204480d4540300300000c40c090080f600c4049049109503140d404e0121840500341500031044124209480c0340c0e0703489a0b1202450345a1040340100c0c00e109400110142c0541070540c02c86402520a00d4415038040f030445000000809080d556070009817602481015580d050041c0034082c00308903400080c4039a41c5001600780c90303541c8140f90148001c48200010301c2070502c04009070701d8001e0000e1 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 263689064 1250 263687814 263687861
    0x30203070e1504050610050705010b0a030c05010210050c1621021c0903020907030c0203070f0309060e0915010311090a0f0e091204050415031e0b0a0c05071104 70
    0x450341d00c401181d440749545990307800c0c030000d0700c3c003405201e0103001c1c050311341019081034001c211255030107542c0503101592a64180f01c002d85845000f8401940034062160a05042000086c01c02d803941c1458590700b81801d041c02003a50f050000c0b240c040400368403540300c207116443c0041095400192402d800180705028001080d00070403a1040380224801717028490007800000ea0b004070301400040d4101704070b030340042c06850107540048030004950040703038284081652044100c10305130004070700103591030302c00f04007040c1c0020102880210840b40320f40d00380f5007510b01c2c0043d16058503070541015250102c1c0780307080040078111201140060411300741c0c55264402c0520740c40c400c1c404c85020464a4000940740900030411502502c401c0b80032034a098680403c002c0600340d600c2c800b1440395142d807400000110086c0600c0b030154002c0e0b0001d0144502401d00c880c01d40801081031521030304040700c1e0701e005540901107444040d03221b09001442481d2601080c005d0549246400c9590802c103400c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 263690314 1250 263689064 263689079
    0x1b0307060f060609180504050106080607090914010302010507112b021f120b010e0907120606020c0d06110d140406180209070e030a0503030a02040614090102030307051303020307 78
    0x100e000c03510840041c031002d641c541040f1540101482102c00312619002c41082c00b41e242c0e0491504180284004034200c2c1e126650542441800d035900d40200e5000300080001200e9030040c8061840640c05565113585140c0000c2d0440c401ca02d0b0050110140b90082449a0344550041040000e142c1a039401c5d10307000c032040b40c040b0440c1d01050344241e000340124080320f10040610502250079a403212080018050068042e0004c000107078144601d0404400c0182c9a01c1c0700c0d184196100d5850040141c00c030b10400d411a0714907004502103400140c002007081c0c6a210001c441568021030014402d9242082c0c1c60250140d50380300d072401c9040c01940791240202c041c07031900075801100e04010325240404c214440030414100250403030211800111094001e000c0c00540d00406019101000b01d01d03a04c1c40c0c01d5500450342a00300c1030b80441c09005150744000d81d03d58869060443d82d00e0400c0010004c2d58900000f401c42d0b0422600141642501d280d007a2408002c540c09000c030303030071652550032 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 263691564 1250 263690314 263690321
    0x306010f020715090513051519031a070806010c051e010609110a02152503180308100f0b0d021b010207260306012a050615040c080106090b1b030706 65
    0x4075840f5403600d071031502d13901d44248031f154005d00a180100182841d800c0a0001000b091124900c2800840c240000820800c92413010784d1959003a40c15228034207214043c00c0140e02600c1c040c1000000c00e074038000201c0c0020401c81c911000022810b481100340511400351006d9080610102d0802d080c032411800310b44080c2200b051360f0340a8a1246003814080035905070100c0d501010710309504006500000b001c54040c000038a03524000c01c240d00940005d0314070710030204048000030842c1c3c003040703200001940b10b4000340c00c50364549e40c031851620350012024054004440580740c0e002030f03030f4a04d40c600e841400c400418a14001e54481d07130036081610340700c0132104012500d54281340500d40d05450901c1117a01c50003050711844501c94051200342d1004d00d440c046240640d031103090100101d80f041002030320440c0100a071480303544488007480f040d01d001440c144140014200184031140c0c001a110342510740b1903009584480030a500010000450342c10500140030004030941400036641 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 263692814 1250 263691564 263691569
    0xf2006160c0b13030f081b0c0a050607030c060b0303090307060306051903031e0302090d05030304020f060301050d030f050f0309010b03011406010e01050c01060504240602010504080306010f02071509 87
    0x100d841101580e41c841c803203803602c0340302d0f4000a5503522450030300000c2d803401d0014540c0390084c48482d0074040e100745c511403c0d15202d28901c029620030620035045103440031101002c0d0505071461811701c0fa13103a170b0140c10755814107801010280c035584140c58644080003540c519000050031030f02c1c03003a62440d0240050140380240c40c012030030f618030880e030401c40d032081c2d40849900d540ca004900020384881d1001d801469940c101701902081154000c0e42d40307800c0940c501d03000d0006103a07281810310401c4852410741240c140504806d000412071685c1d1071360911400ca07018240040f404a40d031314200c0b12403003001409180d040010080c440d842c24158070511030020280c0003080164a002407038981040700726a05800194070034440c01065124001400100800c040007051154856000406503412a101e00e202040810003401e0220101c6440030010000382c0000c11150800d51202c1c5094070000f444c0314144003918280c1c04100d07108010800003040c414018404031469004020408a12803 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 263694064 1250 263692814 263692823
    0x2404110603071107140d120c1401150906030503031b120709080c03011b05071b0305160f030b04030f0e0301060e0115021b040b0d1e1403070f200616 65
    0x80801050a990310805d00c03002c00d10040411a9014103170346ca0000040100c1c030000c0030072030001e98010001c0da0f001c88c6001c02c60b80d44030012440c3c2c2400da035200d1301030590713601110005e820030004101145003c011282c0042c2d403888207a448aa900b24054000d00c82d020003038007a0380d003030000c2000007a880740b08181074990b120203803001e40040004150a8079031408052102d40f20113103032110f01780e010701c1c0281041032140366103a16010420003580001328045d03000b41c81c250820416034441180724508280900440108005c599045855006410100400060500440003081c50f1480e0050702c100400003c010020702c0401d031141d01d19107500d8420b10507000205000c46003041590300115542c4200c0c1c22451030101018030b104204409404842041c0350028180b0700007101044800003403a00c1d51084500403881c1c04854544148084014024502e55070420f00940d00040d1000c145c440c2d43c241c00c11000c05d41402c01c2c08204240c00b07107024019500042c0007404501e604c18680842600d540103 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 263695314 1250 263694064 263694073
    0x14040f14120303070807030b0112060b04150c05121c09030e01030b040c0c020613080f07080c090c030a11130e0a0501060c02150a02010b12010209040e24041106030711 73
    0x100705071641ca00081d0703035910120348150000390080e48264096000c0d008145043d508504900c0042401c840040c0c200060f4020002402d005900c401c030fa688038801c07898036151403804000d803503150700d40c43d145000c1e07107040744006443d8080c0c000d00b0451024030498030001700402c15079454050b00e014007403054113002ca428070303480304454030f02441040c141c40c06580700c61703c1d0135070240d003000b031117500c910885e00d6043d0000d100410302c29020445448840f07501001090700d51700704084980751008840e0807a1245580d503003004900d000e03c0e41038036004607401001007000311058110030307898050702c40301504c403404004001403802c1c04581d0190240c2c541c0201000280d0b241c6034115503078900c0b480081d4100d500400f004100203091001002c0010843c400041c60100c48000101034042600c003c01061b9008a28604103161a00c03511b05e00a48000083c07035242444075000c0b403804001c1c5000494504848001001d110007203441d41440900207002c16501c0c50481800f400442d01012021080c4c0704 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 263696564 1250 263695314 263695339
    0x90c0509060303041a0c030c15010e0c1902120a0c1401150e0c040302030d110f0105090d12020f070b1b031302060711090405010e010e1b0114040f14 65
    0x500c2551a4040c4074050003542c50b090900e001400c511411503c6604c5820040101d444603020a04c003402c078200300780000d45003040014960640f10401a048060042121001d001e441803100b022101c48481000030841540311400701641880801540409080710009050080c19440380e4101740c0380c0d200341b442010301c5c1b01c007240082c01c075101c0c0d454040741021400c0040c0b010301900e541c6564001405a1024035081d2030340d002ca410010800c0039200400c05030000b01039175290502105080b9800c10f0003c102519204000c103641d02104107240e07007845000400341c03046c41003580455442c5015000e440d40d543c04146071565089008490005a13030036021155a60041e44108890241102140304190b00b4001d400700402076010810868142c0940014800c1640310100d0f0030344658001e20001441e0503a10381c0003030135240010140b1080b0303044901160030941051384480c030303514002c0c42c2680300845076084050852060350415170840e00302c600000b91803440c06045001e06182071718107420201 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 263697814 1250 263696564 263696569
    0x4080a1101060308031314071202010e0405070e06160b130623010504050a0b0315040201030c0c02090a020a11120d0b060405010c020d170f0c1b01050724020d090c05 72
    0x1ca40f4040104040700c2000440c40c1006010310780c6500c5030055030121151086030031030900d010102d9100080c0c64030304110490540d03810960004a244013990180300174a0304690040850600ca420ba030311440012030669504842000c080b5407940e4001408000d90070141e2409032000b110f21021224941040220b01803501c080c0000100620904a8007449900b0042040050b00c401020b0030201541d07040107030380d1990304000c51709004030b0498504003182054000141600c4bd02101e50040c400c1d040502c0c2c0040c0c40d0380c4c1c00a40d220390f00c15001a1201d000401c2110b550008040310000c6110b44100400d81c1503c0400403d5051000c880c100000b4160030700344003960145128142c007040b104131403c40503042c04c240b00c400d018491a140d005411251140c514560001c0701070b1b280d01e03200411003c103c3d400030007ca01001a02208250110481d000020100c2c07282c0b0b1402003d42c0b00741d1100c018103944402c4443c421102703520f03041d51509007440407a0020a0651410b031145021904001040d0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 263699064 1250 263697814 263697821
    0x3080f0112120305070e060a031a04152715081506010503070c0203100c050c01050108010608031c060b040306050f0a0b03210723100e0712030e03010504080a1101 71
    0x7540c45600200700d2540c1040960007040010035450600c10740042010750b5603a5040180f00c1c1142a40b40010a000c0c0a914001840068a2a0303801541341809403001c924500070a58229418900c501c06280004d00c0c2100c0012130041a255505080007100c0c0d281404900241c419180c2d0481281c001c00c1c1503410107040621706aa02502042007000481c031002c0c899a404120903002408840c000400f440d03040e400c8824580c0c006000400c0490079034004203003801464010700d2058002e015890801f0b00b0980c6070322540400ca1300340c000859060000e50031130b811080080070340861540c6c480e552800c0800c0a48002c0b2140404040c00720000344c0c24417154415103050b614082c1c028550034981c6003420b0224a013103001b221409800b8441540050300c41c040d05103010388000002c08404c080e9502e050b1030f0861038015010040c0c240640ca0111f010002990001c442188400c450110114102a14140e0b1074004054255092030b0402084c4444c00e4014459000a0303074079840032464509004e4200d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 263700314 1250 263699064 263699099
    0x1807060e0904051c0504181a0405180f0309010f0206281d0705011e050708070f050a06090507080c0a09050a1104030501060e070e0916180303080f01 65
    0x3003004800e824000d07080030003026a10038810411503004041385036213041114104d0040710b002a000040a02c04d000c032002d44031608000582062001010742e100c004070a0b980c030310380240074503500d500050008100841d044012502e03a820360700344071001c2e45040d48030360110361401e000c11641240748200c03520005009200d1900550042c4da80c0c00341000a003181920001031081080e03ea640f0864440e02c0015502000340324080102500c6151000242c101104210280c4414101142001c001900701c03040301c03061a8003066441d91403110345040b41c9100c079002d2000c0c00c28440c01300c0140c10481158000701140340a5030485421a0392003107410766440b0044113943d00b01c0034414040141c0000e079000b06410944280c804a00100204d80040740f83d00954416a11030703455140c108070194501c042250001c0b82d41c41c00100c03185004010507450300000d000000c02500c543c410040c003910a19a070f001c2ca52441c81880b03c1c880d5a4100103020403000d42c4c6041c00d01810500018825454900e858003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 263701564 1250 263700314 263700317
    0x305160e0402220e0d0206060a06030b0306070e18130213020408190f0b0906040c051e0603130b24030f0a021504050603010b0d0c0c0302100b180906180706 68
    0x400c212400c030707488510903070066880c091138139424131001c48002446195400341c0a41d004102a103004810850000c926510080c245440c00000c01c1241c0c41c042903490340122542891050088400d01141c4082560b007543c51800304c80ca028080340e9101c030f440f02c403041402101c007085080c030744107010402c92083e4441c41e12607a1110003142a4042c0039044444400c1c0120005c1803070825544490341d50304402ca0754164190030079800c2000f00229401a403002e810f0941e02141340c944410210072202d007080303a24038403442002c0000380700102489089030070f03d076000b1045101810302c841c5c03101e14440f0401c50415a031000754480215820006000d46c1e415105c1d00080005400c540c0900178411070b0340e200700c1c080180421000c07407651a43c20065000341135400d069540d4400241030401115075034014442000136110503c40030950020740d042d4109680840056224040000504548503041000307449894941c1044900e030001300703000b48a1600c5070a1900740d200031600f819291501802100c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 263702814 1250 263701564 263701579
    0x601110c100e030a020405072105044404050a0b0f090607080721031109031203090106030c0b04050f0a0e0106030c14130f0f060e040b030111040305160e0402 69
    0xaa50300c039004040e0407610180130f603068102d0390f4000c00c003036420460300340020904c5a205441c0d1050740c1c01203e2402401581c040005040542d101030110000c10710381d00e61904c01707000c10300541ca501a0f0b0051807124130b66090003145140c1c0c800b40096045032050130711a10000400003001900d40b401c644544d130904020519100644080202540001c04103031040741060204000044a203403c152035903140c082031389004103429a000b425240380c500640da2121090021010649001690b120b10104c404941a141e0390707000344150044c441a0b00191211a100c4000275180e6603030b03030083c020381d1000c3d100e580c1454075a506100041e507580c410303c034400c2c1404e0010031286200307a200c0319100038140381181c07802ca100141404603800c445400512522141c00030004801000c00302c1c001040000c103140e031214074200300500302d43c2d1850810350080f600c41c107464602d50740a5101510050644450b55121500c03410129a40c528409036141c6000311118045800090b402c40d2070f10a980c01082d02 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 263704064 1250 263702814 263702839
    0x50a020c12070c03081c06090b030606041a1008090105060619080709090501081b010206060a0e150a240c08070f031103041811070c030b040302030c010f050601110c 72
    0x801050380b1168080c0d0710030368410400700c001248803008090191441040c845801c0003180e00c401241c40c0365200b02003091038080c0400c01500e0101d407213603000e1000c0310001000d0002d0750300000c4e001c140f002016440313882750500b038105d00d410011080c001c0898000800443c0da03040140200c40c461000020000d44800d052840c1c0a440744504960101c05c0b858031006041d0385201c12400e840342070304800340380c0c0c10151014074100320070500020908024401064030b81081c001041c602c030745034010a84010b0b5a0b100242800c2c007140c4030380f01e028034042c00c01c21440b40e59403488003003460000030078041c00190384485822548143d5241807001c1d040091640350403491f9030307140810300d1426001c80034016400140a200c02e014405000208400301e103203402e1400307581c4050201d440340700c90f200002406000080200e681f00100809a82e80200c1c140001d40b25400e0580c914064071100e009103608140340030301841095003156024050a80700e10101c9610310302441c2d1140100c0115540001095154 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 263705314 1250 263704064 263704093
    0x50303010e04060213141315050f01020307021e0a060c0309150e03100e1203100b070807050610030c0504020a0806010318060e06040b100602150c040509041203050a020c 74
    0x2142d0b0800d200d00001032030440709101e0340159080035404400c80075041d101c1c0b02243c5c1800400386105440d44a002c20a4825000c2030740900142400b4007400741c101c0d00489880c5034000c004480c000c0e50000c006503a40e0000e090003100d681031903a5220300518803010002240d80c012004e4080c0e86900d41c845c5d424840c14001c2c41001c2240c9004514208030808200ea410f0351014020100220152180803079000b084a0030b01e45800c100040708002654200200903e0112000c0590141ca1070104400c3c5c2d41c00c1d184c2440c05c0b2a004140024025025200a01c01c02c04039070000001181c0c40b03168036100c1a90f55004100880c0600e511050100315404002600c82d03202e0745c006848894106c01c000c042500c0fa4aa003412160280300b80c40103503205c84140802d0180401d403c43d8072405820040400d5400d00c80025105c0c15500824600c2500c05808a1041b1a081041d41d028140250200b03240e8641414003c000a045041d50300c0800e140101048075080c0b103000f251010400800104814901c0042 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 263706564 1250 263705314 263705339
    0x21207210c030c0f0c1508010e09030403050705090705090604090c0909050412030b030f03070b0a200d05060612041101080f06010c080708040b0c160803090f0402090d060e0a0302150405030301 84
    0x5088501d0742c0d145c20301154400d80010b10640700300d4a40d0b11031b401581400d0082c0010780014003003c0e000e5000740020000a1400588602521010f031242c400a460b860700c150b42900615801c1a4070841c041004201c51080b80c0c0515071014255407440e00301665900c03040704030340041c0e030301410b5001c1c83e1502c404850300030303001400c1d030300009000c54199610400040781940c0186c0c1c2d00729030720030303c00c0d091040c5030b2940d000751680b010000300940c5880300a6090b081d21132041c40c910020040d25100007400a0792403a081e14840340205424620303d2405203000050784200404c10b5010422203404500c03080f00180115101d0300301a16109840300e8981c03107110440d0800701e4203c1d50380300d041001080429114015201d4601254010000c2c240118240d55011242d03800046d03c40d40240981d100070f03592848410104801a600165034111903000700d884400c4954000e480281480c4402480c100c00084c1848030a00a07800c3c3d03400400b21440e1014940e10035103000c0d10341e40c402d00041c014a1504074 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 263707814 1250 263706564 263706593
    0x1030305030406022d09010314010b1e0d020f0705150c0417010e0307050a0b130b06010e030f010603031d06030c0d0e03160521090108010306020a021207210c030c 71
    0x41c05c00e00c00e0811541d82a481c00d02000d900c000e000340407800040c60358060203900005080004120055810119021203500882d4086a442c80d02441c04071500407008044408034001c0c18415951490720381c0e844000c4d5480700804450500c589840700e9148200003040314000c9800466891406151101845146a11240780e40d02956110980508010700f00f0080c400e0a210b900034216520960605206240c401031014500c0b400141c1310f200050402c031103e55010000b4240b44901d008078401003031400201d0440551290f1815078003105050f04840c854003217a0b480d01b880301c1e2784400303075090204901050300d003a44084401c5c070955007030400c0c507007061711849014002c82b418450307101e40c2030602071811582035540d6000281d031000c0c030201382c000d44880083d030000c05510b02101a80000c1215a0521014003030341e0f4041a100041031081c000b00c401c404112080d02c8c0ca898040c100003080200301070420301c0c800c0314041c0301a10103001e88803070ba00080d015140d060350005540c403000c11005111 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 263709064 1250 263707814 263707837
    0xc0806100e191706070e0108040b06012d0806030c040605030c0f060c060103060c02120301060804020904150e0318030105060a1211090103080a020f06010b04090f02040510180e0103030503040602 85
    0x3440890021400e12103c01c640820b00c00410b99800d02ea60701810303071380c8030300d0890341048503100801c40403854000c030081d0050310a281a04121400d07030750006851051581c94030020710b0080007400c41c80d50007170b8918050542241945c1440c0030031410842252403e20a241c0c040c0c0041c00c210049141180f9001401007014100760315001c0c8080002d800d0103000d0300300701c901540c0c03114800c100342d07410414040041e154182692465060a60141900000501c004d1043c40f12030300280400002040c4d440032130900c08014001c145e51280b00360788940010400c00480c0100c0e40301050149014000d9600a00000d030408160304d080c500141d1407042400000d690140b602c1c203150b5034688400c0c00143c000c50068210548035040c140c0c0083c00c203c03030041549910740c880e500520400d54507034103c40880305000300028001c0b80f02d120a0000c3e019075440300c0d610007e08141a040c0640100040000701d171000d1900c060383ea110822070326480c8003804080c0c00038000380001000584079600511102800 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 263710314 1250 263709064 263709109
    0xa0911090a030305130f030f06050402030f100603110d030f2307061e09080a05181002030a0206011a030c0f070b010303030f1104030209070c1e05010c0806100e 70
    0x4600201c0c0c03001d48140d00840c00224005204101c4e400301d10640400b8120758071080007401d246403225514800141000340400740e860b000b02e8210340e02042108180c1954034181d42c58107030381c031250200515451000340e44480510540c403000d4546a004200042e40c0f5443e07540014203244003c55a41c08900d14207a031640c51040144c62851501d005090594401c01001c14000c103103c13400c05e840005924400e2003141000c074144005012803056803800c0000d03240c016200c0700d0300d04c15000300c510001d605030b41040c1080340d50401c03140d0100013071560003038640840c0c0140c0d90302d00c10703081c0038800030185d002004c00900126000e054103c005050f0b01e96404103a6040006039110700400001c203a000303d0110384e465408075090135071800350386000380c800c001032410145550085401e452004010201300680c00b0b280c04c040003401010f00d2188600d07083d060a00c7c40b03071854058002c03c28030680744085480c00c2c001030218505000c43d11101c174000e0365203120001840b03080c08241c100c01350084815a10 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 263711564 1250 263710314 263710327
    0x50601150903080f0301170c010e130603020409111915050a030e032d07020a0509040501020c0d0203070615050303070204050702010e1212070e010516020d1e0605010e060a0911 77
    0xc02e040070300015044ca401c440ea0341d52400780c1c00c00c1241d4151040ea8490b0300504031040d00c5a800c44ca61030020030042c0d070610040f89007519040014102508000d43c850b00d00480e10b42402a02104c1c14008681a10301c070482e004040d0300c8402c2104907211301e4082580034808421600e200b18054002080c036400d0100d40f00b00006d40d040d0a68000c0040d90000c0307a45058603010200b0325481c40a10580f070981010f160080c1900400c6000b8042d00030a0301400b9000082820418250b044401c10745401041e02c04156101e0b03402034030f80d03010f0b503c182c0e5418140001144000c25008030345045500c020b0042d0b180004035401d101c090180140b98100350756868a040029a20900c000203d2215417101160b64070f0300c0f15403210a984001c0c050104120401c40c03400c0381079801108464107400d04250045110840d4400203480c4c2c9032440c4000c040b0b0000411075000029046a0300101e039202d0001408a41e0b00c8018010036040d04031101580320b032403001e04000c0b00d6401c1c1d0120031001c205048251034070741d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 263712814 1250 263711564 263711573
    0x30a0b03150403020d020601052d060c061006080f06130e0c0312340f08090303040905010e07032a031b020d02060703050403121109040e010209100804050601150903 72
    0x7001218140d0160300001094a81241d05204250240a04644190041d404500c00840b20720054121464840324800910142e50302d10042d907000302610003c6400511b06004444001c0c0490311038840821036101c00308540140c05a80c152003040c014020400780d034210b40002006d48003011814469008900440e403182d103007405020a0404400b18117030342c480448910003032207252503418080f0101c244013400540415542141e045540240c010301d4501c1090030040c40c2881500d03001549440006000a00c41505421982c1201c241d486028810b17580d00f1410380c00c2d01d039800707a40c2010005104110b140b6034488072083c0102ea03078525001443c5000c9001c00d8500103090102c60001d42d0061010404181c3c0c10050680c2c040718500e0180168102590040d140b400318a803440c80b031a4a03400c03005002c09451007507408030080100b0500440d1140000c0c503000350b003c01e5000340554210030003400428010548580500c2e405001054160308c0c0c80c0d8214101030074041c00600b0090045400000304 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 263714064 1250 263712814 263712853
    0x7021903060b0117040507271401060e03031804020c010204050405010305100b030f0703061e09030e0a141c021507150b120303240a0308030415060b030a0b03 69
    0x46201c1c07480060200014000500384541540000900040705020007001a1003c51901c1c119034000005c0a004464820403600c070420001c20207003005d20f05580107020311415640a41282c11548980030921080000c1c141c80c2d114801010a014210341aa4103440c1003580c0182807014020000500380b40c1c6550004040d6102a801030399030b6032010007440c050000c1882900c511100484c02001d528050301850f40d102c0f800d921018084d5130390340c01140c0300000340300d040c41e074280c0b40b00d0030400c00e162240c40d0240c040c08001406502950904c440031601400d01800361507140b2004014502c501d00920000101034241801281c11100600400c100202000e01624103c1c0c4600b00103540e40c0c08140710b801c11601e280c45044c2c410744040e10045442900401220780240d00c0c4250028030311241010045000e400d50086600b00304044c03000828002508042c43c09580f151046071150085298581d05440300c80c000c0c010380000030400b0501000c101e40c00600707014005025a664000380610b0607019 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 263715314 1250 263714064 263714069
    0x1090504020d090213020c0706112e050f010513020702030a2f03030a1d041b020106031b05010f0f020a080f0405040507020a0507050f01050d0204080114010906120305070219 76
    0x100c0d03480b0fa044400714601aa02e012100c44100000c60600c04040c0300700790b039920a44a10014045c98031104640e188003442907041c01000040d042011900800c404013004420000102c50b0502d840f012448598400e01070314100d410062030503980b40c1d20082c49400941c45664100d0f40342c4a41c50600300019008584120b102400d04070130500c48000849443d000300c804d40500b4031a07002041030b01103503034003d86014540d2210110100c00a1002004940140b5982d07880c140307500d050b070502807031b4558150420000d40344a000790302c009010817200599281030030f00540d4042200b0201d42d40340b181c826215900c0600b081c1c8112000d40b20b56803111404c0d544425507e00f01d40c080058240320307a0070f150003255081800d903c010460403000c2d854040d101d50040c000d0038480c145016800409a116078151032440052810466641e555545294000e008941c00c05902c4171802d0000260040319114140803108503001c59400407095030b070111080d500010b8107d07400000c480c07010161100038281c4401 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 263716564 1250 263715314 263715337
    0x6010513170f0f0d05032404060b0d0b0102120405190b0f0a110a02090a020307050903031315140304032d08012d1214060406090c0501030504051b0109050402 69
    0x245861500b90070076000903400c0000f58032100c8071240e5507a00008036944201082000c800314170b0903089005402d1520544140e110b410b0074800300b80d8004140c000c2c080d1840d00e650400c008559040160313168204c143c800007110710184401c002c40c0c200384000c8903028000803420902c01d40c682c0c080c03a517240c1151410690480740030070314106482c0c00c608110300c3e0301c41c540003c2000f0031555000400c1160002c122850f5a030700071011822141c041ca0640d440410000d080c2c0307490799164403a210407a54148070700131100444001d42040a405124120fa14510401d0401e1031944d03107840958802d0343c928820582c3d00c0d00c15803598218000c0180541c003915640d0b50f099400e501d002c8441110381d0709504c46a03881128807411881a0301d00d924100201c0d0311900f084240b0320b2841c03c15010b080807111952102c0c0c02800b01300300c00c208003640104103483c8100d00100c0e4590700ea8004404894080703c0007080f41e80400040002e000040c0c10314400340c030301490314540300c54036034000c41c06a0700111030802 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 263717814 1250 263716564 263716573
    0xf22030309140916031506030902030c060c060705031b030c070c080d090311040b040e07060f0203091c02031e030a02070b07020d08030c07060603030c0203190302060601051317 77
    0x810158441a0a070050040110745045004440002184035401410a44030484801c582805850007030f000361501d9003189001e00031256440402a02030174400100700d109000e403900341c40491a1603070035241c0300f1300144000d06040e0784215060b20158000b411840c128000001030705a0101c4104c020f51051020612558032181076140401e8612020381040040d50440302e1b141445592007101c02d01107941040020702003c552401040007005100840740e0417905200d400c1081000024101048601d01d6880c2401861003100172614ac0c011303103a5955103c20b01e4802c8804e49800b83d501d00d19141d0005007a5001c50b40c9400030158810391410710312002d42c00100c0c0880c401501406040e0042928458031407809040e5170000e0215004241e0051800c60007102040c080c5104c00107945440c1c0e8844000c105803500c07410042d022640a0500324800c2c0b00d50300204c0c000c40315541f6a00b04165050b00100000e44802d4010b4905400c40c545480c03003c00202c100051000e0f20300b00030305c0720001800c00340 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 263719064 1250 263717814 263717819
    0x4060906020313031e021c110703050c120105010605090d050f0f060610090b030403080c0706060e06130b15090d060f0507020f0a050706030c1704060605090612070306020f22 76
    0x303440001e500c411121719624802c1e0512005402217015140c88822040340b2298494013030058550551811104806109402000c010032000191030504840e048895040c59070b1010441800da4500340100307000280103200c5420903090001488840520038819600c000b0f03420201140780c440403c40080700307540b00406000c2a410316124032020502c003454170074500703414807400c1c4541c3d20028100608100c8034100180b03400e02120182c0c0c90080d800300c0140b10280c1e454904130103900c400d1310ba00d8401c012280c0c2c1013003c80000d00c00c9442d440300141c4919051148070703200000a42056900300e41100b0910f42440c0091854841c410380324004003c00203540c10144e030000c3ca00490800720b454180e12042402c0c0110704001081350440c0c1c4070f881c01040c000540e400455041440c0c64405140c00e59181c180402c2004a80204080d81c109860018855559108100391040c03280c0e40c440454008544c10b00226821b60001c0c8001201803241900e46600213015140302c0180100c214000c034043c0506 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 263720314 1250 263719064 263719067
    0x151d0d0c0f060f08060d03230403030e010804150b030c0612010f05010f050d0e03040909060203060306091c052d03010801050708041109100801020a12110309030901080406090602031303 81
    0xe41c0a0241440c01400d10314204402400c00700c070242c500c40c0300e0301000c400a030070148070f00b545480a4a000590b2120122410b544a245805c2800103d01244020354290300c5035202c0e10145c2e00c0ba542010a5401c4d0700c041021000c0103250b000e05264250042105010064a03502c000704048100941803200e15850300340300b5103200c42141c100a0400420003d2004502d07800026620031407064040081c403201160703c06451841580d01070004039040034000410302c5901d5014501c01c802c00e07010382c0c245aa40d5590503171640c00c4101200141e00074007040312041485107025111542c1b0612143c40c41052410074505248074203480400901d03400801881006000c1c004c607a0410340d281003090f01f03800c080d55480840403039108140e0180a81c040014030b074054030500345004088040086580b400c401100400c4519120700104650f030070101c00c1000c2c05a900d04480c8543c1c28103001d50304102c484801120320840203042640e200b520344d1200e1011070581c2c40218001e0741200780c02d052210f10362a0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 263721564 1250 263720314 263720339
    0x20c03060a0506090c180907050a0f0f09180b06160201200c0d020616030f0e010221030601020312092d0c090901140108030405011701151d0d0c 63
    0x4841c8030181010300b4071809888808075076402c01c005440300e54580844000d0340701000580340c0352540c000c0181c0b0038810f0701500f11006040c0a4055541c10301c20300c10801c41a40d0130002e4a10480006804142c00c0003443c910040d801c0550144d54004503c41d10140700040035504440c0f203003082130000000340b00442da000784801100184400c0c2d0040004c448144040e2549904090075004030000c45041085607114801c807501c041000d44502120000341c00d0082c0021403a201e03c501186030801e13003109039800080c15820020030a55000501d405030031032841c56400c0605118198802400f03003500301c03c01e0a0103140300c0c0070b110009040215019411816206490800200402503e0b1480405040100d4a120400c505480641c0151110340b862401880100700031a04115100008201c0805c040018011660240d80c4c155000e03201c0c2c0b8900000100a2040030b00f548041307150001828018110f10341145944601d140540d600f084c0800e01d0030b0030301042100c600322015820b0041071010780 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 263722814 1250 263721564 263721571
    0xa02010608070f0302060d06090e0105060102060615250c0b0c070b09010516030915020708100b09041106040f0e04030314090a0807050309060412030905030613030f020709020307020c0306 82
    0x1050720b545019400c50781a20342c0e002c0070740112000500c0e041c15400701d800100003010740c0710341000349482d00e4408500900701690014014040c1e400400c0152400780341d812280700903c420304e442c044083c811107601d24102000049070b584642941004654950644002081ca8000700c90b5a4403942885c0380c00e100e40741d001405001c20a00c10391005036400340595004101c442551150000903050644840420358849000400709071040c0c414146c1c04107401084650260031100806401d841c0d00c07040e2a1000032954001b902d4000081c0484da00ca2442048030304003500d61880c00e9264401d11090700b41541081103101c1d03c81d81400700b01030703045c8140400050b002880c6c4100e800c080c1142170b282d0071504005080fa420104120b414850140704072060075500504442c3d880d903880c00103208462208809070f01080554100045504022490500c038245842d01da8440c0748451390141c0d01e2401b0901114118801c54001140000040c4019030145202d90020700f5944248400c1501d02403004 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 263724064 1250 263722814 263722829
    0x30206040c080a0f03030203090f030f09030c04091a04031206030605010e070206010b09010507050705180f1f03060509010f050f090d14090d05031c021e0316050a090509040501020a020106 82
    0x422601d01041e52003560820707a0345e0500d03001d84c0c0c0340c444601080c507010000801c601640400614140c3c00d260f1400144441d22098040d41c1340030801504001c1280c01a08024000b0200e6021501164421100142c1c0c0948241400380074102c1001e2140e0451b1801c0d0400c86085540381d0040c0720440080030460b40c4950144011700f00703981001074911140c001c400c11181401070100701c0204002c001e008200c0502000f4002095040300e260740641400c600742e4580c480c00080d1404501d110940071144198a0030400701c00501501d90760314040189001001c10240d9542c0f0003288655505034051070780502c042c03000107400e074100101d00b0781c100b41e078070000b40302031150507511862000c030b0000544002090481307039074400351194145241144a03400b503901025004840682800f031050307001d01400f0180d07008402d210628180314070807a02c0240e50250f5070b20517036440c80110510610082c49104507038506022400d540c0c1002c80c1d200002900c044036039075004100904800e509114450050004 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 263725314 1250 263724064 263724073
    0x603150b04151d0a031704050607061b02070b09190503010f0f0e0102120c0307020a05030427020a1d1203430303090302030f2215140322030206040c08 66
    0x1c00000c60107107282c48001d2002a240c045d06c0031450300f5000f51801400080c084580e90b10480c68001c0052503201e03500c2e07128854030103184001c2d920000f170300300c00d072a032200300d0303620b0907107404200b00c10300881e243c012008403021036021503991000e00410340812546440480c0309074440503001d05031095080050070310f80c4103214400781c0315866001c864200e00001c03942036403034032551402c074100804e08078040c10302d110010700046c899030700000354a2000c0c440c188040c1401c8100d0130303000c181d205c1c504103103002035240d29070582030700d4200b8500202100000c117070302c1445041002aa040d60480d022103105600402c1480c07082801c9002c15800100e80405400c00c81c0291a0f5650700610921030003030201035543c0035082c205402003003141d48001400c0762140d00e5401070f00b62691131a1500212003041031200b20005550b8140100001c1088410340310441401009100d600702900010b02e004900c0c240038004d440000c4510201000f0b6a000ba40038208900d490b00b4240000c4a15600551a9501 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 263726564 1250 263725314 263725367
    0x203010b0913060b040f02040f0f09140f13200f030a030c0b0406061211030d09050901090c0203070c0f0e01150c03030f0b03070f0f0503010504020a0603150b0415 71
    0x1a019050682c2d90b401080081c40c414030401107070080c49901404590644001008200c01302012000c0301194919400031061603101d03103150050302c1240e00c11000d4408070700042005e2180c401daa071584241201c5005070000ca480d00c5014030003407044014854004110805416414034401c0d03040011401d50040c00a10415a002041070b640440d026046040740c00c0807504009168005100a145c0800b0401c80f0701110b007001d4000104010b68bc5101e031103203003105506980a220050222400100342401e2a031900d0040720160503c030241d4000c41c0410083d80700000e0016081030058044030041c008107506111a04500000c1038003d0501b45000c0040110910740c814107000c640e0390303d40760214001d08008070381400340c07800c604070381d51500651502003003c860408041e01101c502d202004100356031142130600703c80c0150f902a402044002c3c06000d0705000b500058036141358071010014040d941c84805185030000d400003034080c08040390286a031507108004903001070741b00e44602807015 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 263727814 1250 263726564 263726581
    0x2040503160510051e040303030c0318030c1403071502130f0305030d1d19030201051815100e011e050105040605091002010e010c0207051801050105030406021c020f070203010b09 78
    0x491005140300b00400082c01c17001da200f01c40c0c043e0f134007001042d240c0d5848544038035000e8080c03c0c08080c0c0f040028507081004031b13221800001590000d0705074559403c01c070701a8980e4801a0400351440415101c2003021a000640c07448124111078042100141c80c0c132013518042d1100e00c560b900c0804548e8490700148082032003c0308860840c07510440000e011480117407800c1e012604e086030004980141e00c484c40c02c032030b021880000c5061080e4001c004540c0c404409031100b0024610b140f05650100c5a0380e600c1c0e41804407041e4002c0e00d0100c4200d4155640c03448108245001d8001c00d07102040300b686c144881c190321402d2400f400c001d0900504050070410000c01da0b0003140c4916126800780c49002c00994002e5004d40d03880d0901e80c0007806143c03943c044c040e548201ca88541802600703842d9040684c2642031580c41e040c4c0e00140d44642c84e649440e260b28002c1d400084c0c3c00c150300403540c40341d114100150b00c014800416a24016a20390105004141c2100c1240403840d0103003202404101c80305 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 263729064 1250 263727814 263727829
    0xc0304121209060f03090203010f05011d060a12020904020d0f08070302070801140a0f0b06030a150e0601050a0809010b0315040614060f0103020d0204030b0a060326041502031903020405031605 84
    0xc04d900c1c900080c4200407400081d01500721070307a00c0020b140c94480003056080580700c6c00c0600003404a4a540103071146000c0c41000e400307520401c00998900301c40080145000150f5540090000b000b82861201039100e0094541681e00c04807200c882c002008001c058042c400b48004155001c02009107029668485156550040c20489010381d2a04010590002944000d070340400140007103440749462600d0303d0041c000c500e80c1c1c1e15801c403241c0000031b000c442c02880511546041e541e080c241020340b4000d0310a40c0f4058144c4a45540350b00020300103440030003031030035100d5190000c4030407401c10303082c0142121103030044503692600842c200f06c000d840700c0241c000c0d00c680a180069840c140c1200c050700900803038000521620698041c400c181e03420350021800e4038015560a01503104026440c0310002c200455104144828001001460070810303908002900364019285020059030700101ea0701c281c440721001003980460140800c2c1000c01c5240c000c402d5400d06128054140f20008182 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 263730314 1250 263729064 263729087
    0xb04230904080a050c1b18040507270c030507080702010902030a030f0e030307140106150c110402090306190b0d080f030c0720181e0c0c030412120906 66
    0x90100004050b0f002600c10344c00c684801c4a08001d4403001e082c40c01c01e4550140700850218403c4003041015011102c003103864900550384280205100d03460080f0300146100e880701248007081c0800e000004080d9140503001071503580d50b0300090b140c034201c0030140a82002801d5201113a2414050000503280058660301041d0181001100098682c0c4200c8005030382c1c0c0000ca81500000c5038410400850950000b81c1c048190003d104c61610340c4407082d00c02003080c890780001050b0500d12400314400c0090340014010240c1302501d45120711020078a001000e0b00d03030f500e4000c40361074592824004c1703101d40b05045400b2250000710320b5007078a40310313558050440401c0c803240380000490083c0000e1800c940499a0183c0301c2230103100d03000a43e9891101d850b00302800303400012171864440d540b00410314800c0c6c09031109916858603505041401d6180103101c115004001c1140030000601080030388014604204400007003001031400721007201c24848441d09103c0d1002080c000c041c1c0190800d41e2 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 263731564 1250 263730314 263730323
    0xb03041113060f030506063d03090c1214010c0e2e050301060201060501091511070e0903040512010510032006030c03060f0a0e0c1e03010b04230904 65
    0xc04805810900e07004000340e40c050f61009080d02ca0020070814040742c0c841c89800101d4145c07000c5078640d91451007101c196401a51440c40140b807540d40c0321010380340c09903414011b142c0050021520798600410325072542058109e080310090220401c06001ca02400b404c1101c0001c0c014188901b1015007200b09080e9054820844883c0044840c44030f4850086955442610010a50458103024049078800e01450b001075082c000041390039401001e034034085400358500c00340e40c1202400c00715200704c51803d8075884c0340507084000074025240100b1902407801c60016599a81c031785010410803072107119041f55141d050000b0048001c0303442c1010740840e9040a107050b8070304500005541440d01c6c207030007a0b611017008801c0c0124107c5010241d8880c01d01074960085202c02c0c40f003001a0b4150354480c05542108070702c0052088010790010340400c8864107030044042851070450074403508240c000301ca4814002c02c0070001c0c0c0100441d865100030140120440001c0d0031800300340d4210000300040c2 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 263732814 1250 263731564 263731579
    0x19230715020d09020909010903050a050f0c1c0306050301050402090f06010c050d030f1a2b0f0f0b1b030708060f031501050108071103190306120804050a0b030411 71
    0x1400d0040380000000300082140c4110358808196078403070000c002c40d10003030340182c81c0c11001840146051113412000341e050f449a80c04c1200b0288100c520741d00580101c0354400d010700842d1072000301002140e41c000c2e80070851100700380c490307034008003120001d41c413070b51081c0c0c14501400056103078900b40c1c0f070708070504030b2103644c15542c1d62005a60030000e60344000c003a441211040c10300c1c03980c11b900c910a452080442031110b00d074550488291386120baa60035502001c3c03c001442060381c0f1407203034041c08085a4000c2e1640d403042e15a51011840c00074143c130040001c0d0740e00340030460080b00031130388140784100d0101644000c00600743c050200601140a0112980110301180d888084282c2041d00080c1110fa900154003500c0030701d0f080c20320426010a0740c40003c5007805024060840d40b00307140800543c24410b104440410714980c450301d10b400d042d42d5200109804a041844010b054010b070729159465107820184200e4200650050400c0030303051042c000010b90b0100c02d40c0b080e00d000c480d0503 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 263734064 1250 263732814 263732827
    0x50406090b0c030f030a15050a030209070f110703050a050c06030903180a17100c0e0d022209030f0210090c0e0601090503101d03090a05090a090c0b1923 67
    0x180c1c5035100b02860707136800039008000c2189035035003034001d001502e1900709a400f405568000b0700c0141115804004d60208500000880301445003c82c55851916441c0416403040d0202540d030901500d904142c2d0300d6004240c4100078040204580f00302c02c40c1c1610f0603407440c0f0302044007540303034000c00c98600c0750610460b40c051440e0360303400144c4d0044c00e100801d082e44010000351050b80c86811420000300319007000e403c146c0c101c0c041ca4114050340c03000381c206e420f4446c40f5420051000b0680707861426011006000c001000400d1051007502446502e41c440080341d2400c019103400d0074241501075540c03e200341741000544451512040300d0014100b80c80d1501c40c140103030340d900ac03650001340d0940319800301200401c0c06900700100049000603084042c1c00b00d070b08502d84a2080070b21203504000014002c104504040e40c0703095015008103030005051506a5030844024490740c410114000c02048403111403001c02c0186e82d110781c09061100c4400030414000501404000d81c41c52012808500c4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 263735314 1250 263734064 263734087
    0x30f090c060a110624061b010c0c060506090606040b070302010f0504050102030907080c1e131401140f0d080304020111030c06390f070609080315060a090306020702040609090c15050406090b 83
    0x4903c4d544220030001e0003090070449c002801d0444081050700d0441c03c02001c140107041c2041918003618014000918082c00c1c0303849140310b50302101c0110110b42da600c0141c2e4440d5024800e10340554841c03070000d03075241007002000e8a0510302d5001031915030410380c01079900303540704000c0c0b26140c10340496a03844124490b0010742c83c0351203074119995050070f08009007480031800b40010706940c1582c100c805203a0a207003d00868017910206540c002030714080844c003050101000c1c5070311078170500d04024544045e089507030460704050815103041e8040c905000d59181b01c5007a881920720702903141000d0b00d60304028080c0c104900b0a501070100000520080c400c1e00c00021100f15030b40100052000742d01d64a0100b4495100700d44000035444a02c1c0500740e1072030600211480300c3d0080d510805050b0664481e0b800035030240c0812030344280d6031140024541c04a020700d1400f03500925041e41c203185002ca0842c0140017442451003008420441401419040803003001621160a0020703152103c0f03020 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 263736564 1250 263735314 263735347
    0x204030b250e09040c032a060309021806031212010608010605030f06040903021c1817030712120e0309100e030d080603120313110301020f030f090c060a11062406 71
    0x2400c034070404110b00c1c100d500640d041da0b20413190b1f14400307a96269076801c00c80481344050342c002d60050380700c080c071b20b416144004003079004407008003500c040400c07080d04100c40354080b0048450782010200108040d070b800504060041607103040a0b40f5600c2c003440c4a43d0001070040116101e0381e520070b80202403510030000002411902c504100741180241340141910b44100d401d5075036038400101c00b150200801121180b15141c500084d42440303039556070300e1441d142c0080030804114468100c0300b84c40d540d90203441221301011f0051550342e4802818003810054111321001405120b200400c025100018140c14810310341c941541140c0364000040e0500c2c0790403200051009000c4284070842030081d01c095041c0d4410b00703642a44c0c102d4501130600740d018601030305254020a00006441d002000c5c00721760300c02108026200c071400340000040d03c5400c41541d21000800b0b07811039a0700c1542c10803c0719042000c00044003c880c0c031001440c20280075030841c1c50b02400000c100d10004521451 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 263737814 1250 263736564 263736569
    0x80a031d03280f06110d111315110109121205061309060f0e0f070e040b0a020f1b010f0e1c050a0c12050706050c1216090302040204030b250e09040c 65
    0x38180405c25080320b2900043c1c0000552003412460242140c2e26200e01c1002ca4500c0c1a07406482451949442c2d00a080110103105040034419420461402c1a02c00e1040d0485144144906030040c0b00000004204014240290280c6490328003840034a07920307500004001c160140c4046000302480c90000301610441d5600030030b003400e02d08034410480002c1503140c00c3c2002e60040701c5c1c5480c0d440b1081c103001c0800f5240680303035074000c5010580c81515074000300700d903d80f1083c1d400d103814014140144070075203421001c0745d00e942d1424002d4401040303001d078040b10110314006140300c480c06c84185030720007402c0d01d210051010002d03040d01c455001c4e200300011281c02000000710300c0411a030180155002c8070044820030310b0070380011005a100d105940a00c44541c0c5510601c0d60703940900b03600b031310580c0385c0f200500c400c05078000010780c0d990002700041c40c410200c044407418401c07540300708070305240903045a43e400320783c40101c481d0380b020040305800011558081c1e55140d034106582146580d8 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 263739064 1250 263737814 263737823
    0x70311010c0b0f01170d05030406051308031015030b030c040903140d0c0206060a03030e010f02030c0f030d060801050c070813090c08060a050102070f05060f04080a031d03280f 77
    0x10780411804181c603d1000381280d90320060040191000540f46803210382910300a404a1000e20105011420f55803200c1da01880034004012908d103036484408084c0c0085941000203105050148500044000060500340440c00c1c03d01545004c240000d807581c0351080700c03230302460b80e4040c0c5c4014548a105c209a01c2001c0c00780702e5660348540000c170406812084801c00152140e030b00410082d08000c0c600704c1c101da405a0ba130001c01203055004480c0b00a00780503010440c40b0500081c01c03001003e0010340c00616841000715620030f100034000c400d03200c03190b120100c00e03454101000080d13428101100c0e850f5a01030700041d6125500581182c038000d02c1c0c0c00400a092414030701410041c0c01c41d0201f4010a0100c54881a880d40c400049030b65180f117008000d800c1754851f030700704020700b80100508058820017501a0030103031149000f80c9881c1038114140e00081d81d100e9190b40424440c0310000c0280f8098014003030301224424414403644d0309000c044e60006482c0303014824000b01218012020344d00 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 263740314 1250 263739064 263739083
    0x8030429040609060906080121060908031e06180601050319050112020f03010903020316061b0536100215040c050f09040f08030601110d17070e03070311010c 69
    0x40b01c0000700114603034004c070800301c0c5c0c4110380810818010785009040303903900c0450214444404400b81a201301d2014221a040c1c2c071a9414000100b805016501c10112030100050918100c0410107000c1c101030b00041c0280c075a0304000d00190826951030798040380c02c0c04c0c456038940700c81803480c00009485a0621a0b2840e001c00404c0c002041c0007601c00c1c0c18000c5401d28090b1043c0c2c1c0805003207409841c001009644204000f0748203001000050b05040d00030030703000410442c3c610301243d50280c034010f40400180005054544480541c07046d1125002d55400c0003806400007214022001e14000c40520403240f1515621030507108110a418401e00065150120b042902c0c1c43e00c41ca041c03a000c0e052160000d5800c0c000e01e400c00c12b110038800c6030030024114158507d030700c580c21070340d20203055a4104042d4034800800c0000402494140070955956a01c41c00d0400341d04c0e525508010709150100031488041c41120b81d4001208800e40340c20a6400009196950043c9d940305003682000300041030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 263741564 1250 263740314 263740319
    0x303060d0804091b0e030d0804031409120c030f1501030305161b030203070503011e0f1401080a0b011d0a0e16090e0f01060b070f0501060909060c17010803042904 71
    0x20141070313454001d405840e481c1108190b0810146c950340414443c00c0011083c40009010900c40e805a403c030240404005180105040201d01c900c0d440b1004001213070700c50910014a0705003000b801540290358805401044214044294010700610000d000c201000c1400c052904840b5441801254051841c50103d14623010f0038100d01c202d480164828040c0c10000503440c1018007648a05c118416000604000007810300e0000b0b0018000035541306603a103903402001011000d1719401781c405080140644540e600d082d10816005030440f410280c08800205019100c0d841000c0e0808884200812884030500045280102c4107000091070302560000040320394069008906e0221101d060721420541c140000d42a90090300ca513140d0060b0410921000c40e039a0316888101510441c00416015039036a09003003624441380050303c44598401c582c0200c150042d11103407c0c8001140e00160942c5000c0e01c01d0340301d000394815141210b8811030001c844c507000719a0a899201c1580b4030750744854 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 263742814 1250 263741564 263741591
    0x30d0f0f0c0f020d02030a17040606031a040b0112020a0909210c05010e070605091509100809011401270b190305060c03131e200a050d050303060d080409 67
    0xa070b005082c000b40c01500350a9080c54030200454065501c036440c1c64012a41c91700030f0348060040200142c2d80c003541c911001c00041d01000d17800800400300b42d4800401e08050801c100c0c1c0303c2040e0302c0790a0388024151150016200c440901c0125800908005801c01e000e081202c0301d484643c6005030707002d01d002e903e004c4650300440b03001141c40c0600300810110214401c03059031600b00e80540c00c04244140032540c1c40c0d2a01ca69030081140d1a800214240010040031480c180144000b02c001300c1c040c901080a90102403080701e10a000c8440c0801d02945064100714810b0031500340050080708427003100ea05807500e03401c1107421a0024042d100a2054403204900c0d001060200300d610307014680210b2003190900c41640e00646480c050000b00750010307900c581e80c0c1889054208501804500b1030b80100b80912440036a110346401c001902191200400c56403001c1500280c0c420303602e248800c0302040c40081076a40c010350075200709483c00924100345c24603014540c41307041c200d82008207490304070 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 263744064 1250 263742814 263742827
    0x32514032a0a0314090a1b080105010b0702040e0a020f040e01020421030806090702061f080a1b09150312020309101116031a1005030a0602130506030603030d0f0f0c 72
    0x210b030b950300300300d41c1c030405502100700b030400d0f90145502d030700510031b00c0c0101e108007a241560100c40c640005a5a40d01c00880b420755409034800c0310b00c1c0c0300c042114020750425000e0201c00c0c0810300301500c442517480d80040e0540300d0803000c0300d020726030b81c1c13036624a509402d5044401030400c8080200389680050303a1210901036052080b4000780418010641c5070900b003030a0340c0640e68580140c5015582d00320b4103c00c1c41280947c040d80841c046200180c1401c051011080c014001c5540342d508214544e40d92240d405a6440280703e41e03c0d001c0035454a070302c04d8038282d055a03444840c40b9243e000183c8102d14601500b10500e600490518602101d180c000c902080e0f92160755055843e000c51084605610010510004c1d202e0000c0646281d0f00c00d8908896a90244013074605586d100e40387d402203807405010303c404541d0281d00190540342021440100c07002410103c5040d0701d14688580400d440380a82d89407002c0c8141c40b10344400060100d40c101e00200c0141c10010400c9041c4044002e048 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 263745314 1250 263744064 263744077
    0x403080a0506060f070f14070602120703020a06060b030402150c0c0105181804050105091207080c0f03030a0c1205070917030702190905070f0e1203071403032514032a 73
    0x1000380c7d101001024641c0030840204840707150700544122080d816007001203600c007440460446c001c0d0104500001c20b070f8030a031400341041da0318064403407a10340b0502c84003201001d00041c80300c3d418409035401001c0041d0450007007000703180c11500c0d000100c44140d4601c0d546c1c048a80d01c416262995043c58041000c071500c504d003e0340080c0520380320100740c44c1d2110140d200500d0043c5040040300c01041003c4000c04050380e02500700e400070511142900c2c00e5410a0b03c1c9548007544816500055550040501490040c0391a0420041c101a58083c011200511503182245a21120858403c901380250380b09c103600034180c1245004601c0c0b40e0102405c8600071403080d0b515140125402900c6800c0320002a42d490300c400303091201480070460410b42103900906244010890f050003c0c0100c00601000c202c20300041d5100d040400303d0715400f0350403100100c400940209259100b80d4820449010003c0700504695a5140e40c912a403501d5841e18800c0200035400d030071142030f00d48041c002d154 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 263746564 1250 263745314 263745323
    0xa08030a090317060a060e030f0601080c010e0405060d0b1b04030c0504060b030f06060c070506070c051002120406050306120109050c1c0213020f09090906010e060402030403080a0506060f070f 84
    0x1208080c0031080800c0c2c22080d28019001045c0020600c5a0360180f284444281c500070202d0751681420283c3e1468407000740c00c8204590400b0307070016090b5820101c105003242d400c43d800d00c2075140140c041402044030b05406403105032000042240825a110b020900f000200a1107603129160b007495543c041061183e240140d1504400213008041c0c1d0080c7d9000398243c14060400713480704400c01c00365401945007402c1500800c10009415a25003004040340d610038143d814083d442c101c1004202009d45503242c3c1550403020307070032094007030a00403241914501e0403d44d4403500d034000425999210040d4a0105610300501003050000c0003a000c0a420011150f120a4254007400c141403025000d40003508065110702980b54440c4030b40250615040065005081110307500004600b030000366803004403900034030014000301c51901c492591018064409528500702540c000305800d0f4020110002140d40380003240c07281d5030f20310448840700709151034640c8440050a1150142c00d605108a4 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 263747814 1250 263746564 263746577
    0x203040e0a0501061b0c15033e03041e203c041b140304020907180515040609150504180b03120406030b01110615030a08030a0903 57
    0x1ca60a20030300406042e00c039141d40d2502d25200701e905070500c503064500c085411118165002c900b9079010307a03014016451070f50b00442c0c145041c030100a5225210340400e1040c9a5010800d03c0740c201289140080300002100103580350380398101075590700c11030795141d03001c10b09107090726040c0f03c8101c5032104003d0141c980b110401e1120010411016909070600500c45a2030080045900604110f0721311034015203504020420f594000404072081c00c008440298100703c18038070b1143d44007404150900b1008038280ca141000d070002405008020011006c1043d500601c890b29a02070740404020304015020f07225040303c0500da06182d401600610000900c03460001415070b00c014140380c4d41020540300c0500c2c05040c541c848036061550264482000c0e120700914201c0d0310100054154010740020994907541054001800d954a80c904941045014018034403001d402007074054100d8080c1800c0141c51007004082410641100c0b0060b042a0001c01000031003a401c0d04002c11a0b071003651240c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 263749064 1250 263747814 263747821
    0x5031e0a0207020306060316090c1809141f090207020303070204050c0a260a020f1306020102180f09011514071b0503070f0501050304030915030f0b150909060406030506070203040e 79
    0x140d40d8843e01c0300b0303260904a4039104004603201340e2b000710f01c1c581d440d00c1c008940003d0340f0050401010700c0d5014003c101da0f20320b1030f0640c20b00213038116030300f1240400040c0d1050486405124000c00300b13010750001d6580c00034088045503410404c46004541c0500180640c0c41d040c106024107030049070074213001c01c0c00c0f54580030400003000c15910324080c42d0105151903407105501080250840041c461091108105c0110b41401d813a60090003006190300240e07032001400f11320ba070700c03240804405c0d000d64101101c151640d0b40c6c0003100ca064500c041c0d413584440e500004200d85510310400001c0c1c01d03200000ea03460a10200017152186a880100c10300301c001e40c2c0d00d0606903220610301c500c0554480e02001841251711071401150090b0203450910310380c9403141450000b1041c50360b0500003081c1e0320f48400190a119020b404c0c1050001c450410740d00c0000508450755104000e0858402d081c4000000d9090b40e459100c400650741100440e800782c1342604011b59294400c2c0101204c0c0304440002 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 263750314 1250 263749064 263749069
    0x3201081002040602150a0b030a05030d0606052503030b0409080903010c0509030613020d081209120a09050f0411030708090f06101e080d0320030106080705031e0a020702030606 77
    0x200d50403101c030b0384e000300000042c00319145445e40c03014000210581d02c4260081e02540c04000840740d42d4000c0014607030fa04c4051784a40c0403031720554400400d1000c148880c15800d0424807840f00d1a0b4907038100b1043e5a402c5203821001000700350002984540350100310014414074a002d0414200154000c101d000030118058611380108018030398140d001d81d0003d080742c41c5100e920020b0303510151127209048581da44083c0d05402c2641005001c40e54181004803a90041102107125036002e42041c0c40c101e40c0740c0c0000c100301c9503800307000d020f01403642c4800501d0310303680d0007515510162000c064480c03c180b076004107490800d42d8802014400c40c60030140542d80440c02d0ba016801c003844110f1a01d18089000010303070191030315008420b004400c0050560001e10a4813181e0304541c0d00098508240c143d02d60380044502044508a481070006000494201c100d058008600341003840d201c3c0d94091500441800132051801810a110240403540d6095000303054094400c4007528480e541c0c9900307 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 263751564 1250 263750314 263750317
    0x1080a020a0f14060a0203070807062301030201052a0706030b180c0904050a020c0a03081807141908010e0606040b0405070f03050a060e100501030c050a020a063201081002 75
    0x10700f62003030500c0010003085180c00002080e0722a83c0740141c9007009030300c0e15030324503d8204803401ea59840c4c94030014000c600c401c41c00c3c0307010481810006503243d41541c0000b80103004541140401c00c511540100140c2c400110780d007400d0b502c20045803150307900c2d0300740107001e40300800c0d156014049401c000f0442c3e07685124240e226031800d2200d10b040400725010403000c0c0c103024085c0d0000a50800181c02c1c000c2c000d10003200100e0107500d84a910b401c040c0c0c01060050b0041c04c00000c2d85d0000c4500340050008501c43d071009280458040c81138010101040040fa2a60b40c0507800e15031820003002802d0380c01080b4248180130446040040c90303824400c0c04241c40c1308507031120009804494001025000b5440a40c00001510000a030b284c0c0b141c0c400030308550192441103030b81c0c00c64102080190b80c14010748008041514110303080108040c4065950100f44900900c51703912078101060001881d05081580101c0380340c1c0d40811348091048a040c520300313005000c8140101e40c07040d24105010700 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 263752814 1250 263751564 263751569
    0x10e0d02190201030207020607060e010608480607050c0301050604020a080403081f0e040b07050403020d03080a091e0302100e030d1d030309060919080f0304031701080a020a0f 77
    0x4498003400e00702d500440080d80300c61000c0b030b8231100500500e008105240300b224441c842e0708000146850504c5006458602c00c952402d0030161400c8900e158a148402d40040b04003925500c4401c2d06529820701011342c0c5401201500820041604800c1c4100001c000182000913030080105485020500050b48280b8414401040900020a001910a8a606610009021717a941413401c150202c1a82e1000682c8a0b0540b044180d09010900082240c0e01c2e400c1405404c003d03240625507800701e04004107101024090140085c00540a0001c40d000303071070516801a000c01810b12500d0040d021076100d01002e84c01445132a0111110391501d215103207c545100c2d004604006010a000010303000c10b1b8910103034100c44080d0030600180800141d0300801c0100090085440c218000c1440d00004031912030060f42c2c04480c01c8089400300c0c04a421034000b1272030003581c03541c0e41c0c101510032900901c400e000400368503000183d042c501044003d0b01d00d200301c607980203070350b40d90510150200060 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 263754064 1250 263752814 263752843
    0x5180f01050307060c03181806080c06030108070e0711060709060e0307080c0d0303110d0209090a0506090705091f020606010201141506130306020414210d0503100512010e0d02 77
    0x103085c8000881e001c0d140c955408070110060113800d549910103296684a2000c1c8009010340711607050190f400280300c001e10403181600c44605540c541085035641e14880d1142c01c410012707070008942428420001c5811200c5d4601c120303865070408040c010001c101e1803150701e0028144080d640c40a1030045811011200800010a00c240321603003088141300103a40214140756486c903400c4000d00e00e483c05042d020b5540040142c9983c550380600120900c018048040103250004002d80c81d0358043c0155000849880c08585032071a40c00810541c403101170100c0000e03404141c0c00c0640c96400101c052042c0c0007a4000d01004000c50f9404291081c02d8510600604c00c1e1000c840144c1050005006010514180e1180d1180d490312080c08a0b40903401010307d040d0000003400b480e05201c0003c2c450045071411001502c5010390b111a195145e0b5081241000000400b190172401500ca400d00074240080000c61403114560644e4020002040094101d000d01c0c00380c5a03c42e4004107418424080c0c9 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 263755314 1250 263754064 263754077
    0x20030109050a020f0a030506010e0f1608190906091419020a0b09191220030a0615050312030a0b04060308030f0903040b0c0d08060a21050705180f0105030706 69
    0x3d030308102410b1380c00c420b040e40210b0080c00c0000400d1040202e070340240003068801029050608070515880c100401a44014003d5134002921030b07030100405601001d12440e085000c180d02ea00c00d030240c501c41101a14650401e50164140401040000300f804007031011a0058100302465141400030711501a41c08144000c003040301c28150002010030010060502e14840c01d610040c001c03d481c603400c00101380700004004005c20502c505400c2061079800404140c5c7d0310b1020000350b81e0030301650010280d5072a141c41001600c0e072200e45001800d0b006050320400040104402400e810444080c803255041514481c1d0508180c0328a1096a8004207810722790b55640c00118074903000a850b4207502e120800c00001e0105580300a004541080c02c05007440700c0b51480c1c010030007140500454400e1003291810040302d06040400d912803802c01c201c03540e144005082140c01d085c100e6003d1a041080c00111040c00d0b614440c580f48540c1070545440711603601c0b070003070540d42c0c0200e02840022819 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 263756564 1250 263755314 263755333
    0xa031a0f030c060715060609080d0513051e04060803070606050402030f240a0e04060c0305010f050d03020307021503060306070804050d080a2409060501031a0f010c0b042003010905 79
    0x4029004001c4117015921817040541d81080c640104ca10540c490340024190540911000c02c1c24070404052400603e400d03402c1c00403502145a1103c1039214884c40f9800c25150501d43c0000328941c000c0c0d100d0020010001c46913a56211a00c9500030141200c5142c40c04102060380c3c6401c0c03003641c1c090510184011190350300d0300040445481d01000c034010b1001007081c07400c55940c8420025014003a00720300c030012410185401419106860002801d150a05005102850802500004031582154031514514280c181682540725184003c2e41101010505248810600000b0b50041c00c0503021242d00ea6241041118400300981d070003003150304541c103d815000d11034440d803034001c03103c0b0100181c0c108030002c1d012020780c0e8518080b44103840071a010010ba145038486c4000801003800e0502c5180740f041c0560320001d10a22a41d44180c04825145c00182d01c6401d484c3e4009501c00c400c8115410107040c021a5000003450342c19203400d148a0012980c03c041c007450444a034400300800360501e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 263757814 1250 263756564 263756569
    0x71a0f03040206120a020d053d0b041e0b030f06210109060f050901060f090c030b03060a0605090601140d050901023601022d0309060a031a0f030c 64
    0x240098410307079000f0340521039240301103500001d41c0d015691002005030b560541c000000183c07040200701c15084825414003d241e04c0c2918405003208221202e4031488808004020303185201070307001140403a50109000c1170103003180e800d40340320b400441224100d0743e030f0f5078580042d2407008440107100951841d000c0348690500b000c42005000380441d61070140c15000c40c4150840e485104140c444588408400c00241d403184900ea0b00224408024008907052139090384203085070f8070074824666603800040c0701e018403e60122030103840040681e201401c00812003006001c05010b618858015030b4003040866001d4118a060f101d21994450301300650515014000c004c000e20f02c0145540030090024003021000d200b8026901c940c1840f054620030311070005585400c468071034155808040d101b0b15029000c400c4552080c81d005911601e80a448215411400750200054100c3d00c00b2414a8600d0380540000107803c54172001a02d8131400c1008211542e4091400e042c4c15400c503608003070560 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 263759064 1250 263757814 263757817
    0xc1c0507021207030201051014060414120d05030910020a0c020103020a090b03101e03020315040606030807082d1603031d0607020f0604050d08090f0d0e03071a0f 71
    0x100d5940192450700c0565005640d403940800401c81c01030350f4030403c121201041c015000c0c0a032180d03045030000201d04401082483c8584c0c050558503440300401d2050a5840d80c4060800b1011041030343c120001c9100c002c0c1c0560025500c003042d5004160400c010440700c0d1090f43d40c7c13070382140e17100e50404803240c00540095010103025070411a1004c1b011a1132020807004600440c81c0e680c10186040c6824291680f003d6a5009420009000c0800f040507a600044500740c0b41d184030380c40e101c5529646040001800c540d400180500000300d5200c0c02e0001500181110b80b603500f45c040e04841c840d02154008118a0030300103501c00d02030040b80064500040110300b864442d00b00065a004074030480d000300b41c0507400096580c0d114100304030b0115030500c140c0c02100c804200070f0003030b030a095850b44c1d02e5204401c180804c03c0900300015a28072800c00101c00e48240c40015200381d203a540d94010206210301c10f40900070f108030040056001e40110348012034044800c3c02601b0596600e0050b8100e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 263760314 1250 263759064 263759071
    0x6010302010e0d1a0a0c0912061104170c0907020a05060403031a040203090102040f0e04150b0f1009080d17041b05031e06060d021e040f020c01060302090c1c05 70
    0x112002c081c4000010720a21603020400c4d02441d401a03031454808a204251b403881c520820401410300010002c00480c0704001d400f0315031006d004201809003020340d2100340910741c000c2e00c98020400c0710051905000c00d841010050995401d42c140e61855801c1e42e5aa0510310000e01a501060010740030034441c2e404841c45002c003110b801c1450007684001020390300309844290403a54001000c00c0003807009d480710740c018945800d407000c00d494a602d0b0880054410803140f46410345941e079095266407040003241d8446401083e500313900d1b400e054000c20304045401790314618400c00d0000503840d0301421843c5401640500e101c617844d82c880d6501070328a03414600d4400301d10881c260108080d41c043c07201e2030103c0540800320400040740010540f030814064001405040e00c0c072100170141e1a020003d000000b00c008503110b85600720b03c040381c02020450000d0b45e4071031011515040d14107041d084041120300031100c42e45151900c3d00c0c1c0d03142c0ca00c074a40c40b404103800f142c2c8030401c0c0011544c000e980d0 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 263761564 1250 263760314 263760319
    0x411040603120f12060311040c02010b0904030c02010504030623090c0609120c0a0b0a0f210507020a140a0b0a11070f03050c06041a09010c0203030a021e0408070611060906010302010e 80
    0x2015098040c20350640300246c0040310110071500700c0024505151081c40c0c2c22050520091012603048004140441c10107440542000170a901100943e40904111001180c0c40700e807c105050219401202c541c994810110700a1802404128800070005003100441001420b0501c0c181400013000310304110030807101c00600481e0301e01d004542c0e840080000a20101d001c9a80d1880784141c0101120418804442071200100608070900603829030002083c0d07000d0384c0000d883d140c1d544243e00d80b4000200003480c07851480c41420a449002c180c150441e03128174040700c45a15401d1410007500e0300c0c40b00007110360109025507804036608ad40700e400c1c240c0c0213040251621100c00021420314400302e4055a940d80031148501c1003500c000c03507490340100c82e84000c1100143c0b01000035128880601480c090a80108a03a852030318500080d80201681d101c075266501d9071041d040303440365260311800c00030030120b04c0080b004040100315503106100840c06004a0703801c56006440d005040c6a5064 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 263762814 1250 263761564 263761577
    0x506070606050a03030f090f06080f0a0f0e0102040f0609030206032a0307050405090105090f0414030405031f14040c0506071a15030601050a06080c070311070b030411040603120f 78
    0xd1a0b0700c0d001d8401004e94002c1e59451083d00a00c2c402a0540d801d030b6104030781c0d21031000010414558444c8001e500450b241014440989954a042001e00b04021200e800d0300d14144070400301801c158001c20403108a444000113244da200c40a8a0106151001a42003802000091a403c464000713400e00307205a040c0740000c0c110002080666500203e80c1d5101048000400380a24074058145030700500040320441e116207070050702d041e42d0a20142000f01024010964003500c04001d00c140c4003c1c0c40003800701c94044900565041c00b45501410907002d01d403a140500d050000308100f0300307210304e40103000060a03178500024002c1903445400156902c502035405014404015035009020b02210240c00781080d0034201054280031040c0d10080c800e03070790440100300440d00100303403640c496441e0150f0303503d440b81c42c1416522011009000c00e6540a00c84011681950620186000f43e01400000c0719000101e014081201d441e400090110501d100c3c0c261420b43c071a2500b12454025440d005 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 263764064 1250 263762814 263762819
    0x3080f070506180705150702010305040507151d010305070212130e0c09010e0105251509150b0f01090b03060409120314090703121103210106020f0d090506070606 71
    0x82c14107006440c008003680308452560340300b07001004980041e210855101e018606840f4140710305104080d0000c0c1855280c0b000a42402000d0140900400040313880000040c000758004005880c1c8100010006181d0503a20078194400d1180510410b416002000c01c0c0c0d282601800c119042002a041e5080f40383c000070821048a245503805643d010404940b2a403040002404480e080405641049400d02c80b441c2d01091000892107003864001d140c60014066040a00c0398074249110010b580f41030000d91000c001c0750504c5101840d880c10804c00244101f00100002a03502112083c001802a8010b21641035450f00540c2c100300024030024860b0b080d40e8408012280282d51080881d941e001c4150b0b02005c030844040d0310003080b2003d0058641107030345012198603032643c4a000c0040c01500c52010060800c00c07603000540c83c0038082d4000240040851160b2002d0046c080180901c400800f802400010704101e561099250180898104402d0220940020000ba141c094640900 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 263765314 1250 263764064 263764073
    0xf0402090c0d0204030303020c010f0507050409020f04090e0c0a06020a02031e031b06100501030b100507030212030f070e010503090615030102070b0c0706180c0317220303080a06080703080f07 84
    0x80004500c00d88008d070700c1c0c0e1103100056003182c0d071041052105600b01001c0208086d8050f04075401d81c2c1243c040141c0f1611088002611405160004040e09241c082c1171441c9400c00911488420401c980f00214503403600c208a840e400200070003500755005101c90314603003104488051021402c3c2c42182d080c15004ca0049440d41c80900d00d11025812030010b0041004049180c034000d00400e007810304c40d814030380c00400c00c1c4078800c0404600f0040041020b20405100b80420303040000482c0c505900d9040c030740b1090141400030341d90b01000c203003140b000c04600e50040c0c054a2040010340d0140c600d80c0c1d80d1100e002c1c404216070308820b5155600b0010200000c448102103402100100141034540305030780780103c21100a506081000c3e120100d0007070015900000f0082a40d0707201603528000c100f42c0b514071619000b014180680700c14954034096800c2d184000300001c41e40240c0d074851140d01e030303181501c048070524041c1c02d40c0d640060f541400407078091401003040d071055540c110720f407290b0b03601c4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 263766564 1250 263765314 263765317
    0xd0c0e030a030f020d090302010c06050604060b03010e010906050d320d0201020306090703060e01060c0606090f0b0907080601140306060f0c03041719022e20060f0402090c0d02 77
    0xe048021074040b0b0700d42003420fa4100414030040704c45d81401d5801c181160000380408800c0e003002010305484000085642e156600800c005100380c0c0009030726540c4401c80400c42da03009000724003e00d443d0000c0050035152403a2152841900968421440300d20100514104008843c82c106a035904011140c1c5111081108181c2a1082e500040e12070a200c42080248200a0000c8003018180780d414404078529190450450301c4608050144901618107070f0040d20031907115500007464089017041e50000c43d044011503050440322000e0503641ca0b4000e4641940581e640d07030001d450419611000c010000055030400c2d030007400743c1d06100400e41c03c0109640800f4074102140c102040c20041d8041c00c120311a02c0307009040283c03054034640341c0c00912030244850068850f844092611524149010b042e0410031464600c031147d045080401400d40c1385100700b8500d450b01002c60f070081010b000b2880c0ca000314000b4124450540711502000344100f00a420004c0612080003001c2140000d0720 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 263767814 1250 263766564 263766583
    0x30b0c090f06160b061002120c0a022d090408090d03021005041a10080309040b130903030b0f0307050f09060303160f0308010e06011e020c04020d061401050a050d0c0e03 74
    0x801c405440f01480c0b400035603840014008500480441c50703042070640c0c0101e09661034400c1a68901d4440704d2150a0758a001c65024001c1e40148c1c90b002c070040f104007001c112200d142142c51152405081d91800d1000d0f8280449000e03000711014801e40d52589485941241464083d10403a0400034200c035281080700c80c1910110743c203e14602c2032031050018800f006610a01200d460003002d0b03d050802030301c0744a00d0001c50322a5036540701c0d2020a40e21030550480ae01d0b0041401c201300c80700c40c40c01800070812403402d18452040a21000c0c000d19001540105545000d030400c5030043c900c0052000520b0003610003541804280014070004030300c811150001801480200c0091250341406000c2e042e06802483c241c2d921941006000e98000c1364000d159081114003080070403c0300401c900b00005054050b602500004026030090f000350004429108401700e4008800030000040d142d5118001409011590a008890038040c2d542d01404100c0b841c0d0030600700c0061143d00103401c080140 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 263769064 1250 263767814 263767837
    0x70f02120a030b04020c03182b080403150b0f060a05040b070804050d03050301030314030402091302030102040b0c160506070203061317120a0606030c1b1a0907030b060406030b0c090f06 81
    0x8180b05606032402d80c000f4023075080c1501d00c880c0c1c42c0384100940400c130314030b03516aa11012081603402c04100705407080760700464000600b03003643c484100310311003c3c0c03420343c000a21402c0d103c0360b4100306192074030480705000c69584030945054034000c0c40090641081d80d0a40d9904030a00c00010030341c071145622138a45200c3ea84a9a4940c110301c3c2c050040701c0c0202240b000304000344200300c0141c68035081c940e0001c1d088100c0c00b805200c10700c00240640f14075000a00048000303d03a80400140004095036204a400020b8a11544034024441c0500032900065410f601c22008031b9149003981040a40300d03400749176000300340000710507000590780c4900e0200c04985000c1c400c100c40e2007180c0c8900000b9001c035240074007406080b402d005003940c008510303050805010318240e07400c1181c04041000c0d440c50452039000d1a15102c145c03a03403120854442542c3e03003da00c0c00010014a071500c100c0040daa40640c1007030243c1c481c2d070610840c42d00010310141d0410080c0030414929074034000917212560380c5 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 263770314 1250 263769064 263769067
    0x2c09071107143d090806070302120112020d152007030807050c0705090c0a0305090705010210020c0708150f09010606121113090e1b0607030e0d0f05060708070f02120a030b04020c03 79
    0x280b174201803520800414050401d0b106120448040040d09891411100f03130101c01200c500003800042c400d02240c040c020120805200307488901c40c0300e5004a6048521159261080020440320010b03500c5280ca008000800050000740303110301960103032100001070f90881d050700ea2a0008114031000a9601e03020003d4040340c04e8900507030500865a2040902010f011490718010010b95162280303d6652450358000c0707192501030004010403c020003c1e101107030100010741c40e11200c101c4042c0c0f040b035000b89040b00014500c4005014010403100c280e69054400890741282c40000d0401c00440381c3c255030104500e5a006101e403c0100c064000302c01c00046151050402c1460041c480c03040310b0700d628004145003444d50f902d1094510740398040c1400e0000d042d581002605200e43c4410040c0000c50450f950000c0c003500003000b5108112584904082d601d45030815545d240011090200580c04455502003440001d80600b0001c3c04900300442c0b001c4905001034123982080303032420801e510 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 263771564 1250 263770314 263770319
    0x111504151706030313051e03070320060408120a0c050f0f010f0e0703060b04020c060c0a02010612150f02040504021611102c09071107143d09 62
    0x580c071080340e4100703104400452601c6a2000c00120b9401c0d50301c44e1a03c207a0752806104821200f01100f0943c00200405940101da145c2c90880c03000f203551801c101400c1840744c4212000d00f030400884054440c18001080301070b041c02c40c0302c1c1045d44150000030420950349640f0000400070004a03c10305d00110141c00428980e401690844101c54000c40c40c050030085003901703c140124440d030540e500060b0200b8489640c00106000c0d22410100740c03206d1040308200503800c4030600203806c201c0e180c0e60007404510703680c00115003030031110350015140000a02220380d42d4142a8000c20701d0007072501026080c1565078000400701d8110420000308000004214000c203d000700c0502000c090072075412030507550b00310b401402c459001000800180b00804103036100c504c004205207100030000c5c8111b9051521110003401c02c1c02c01c400c001428071030f0020114075034045001c00c8108070400f03800f5001410300920b00c10820b8152400f03041407800900700402817502a841c0590080350036803500d000e22071 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 263772814 1250 263771564 263771597
    0xb010e07031d1507080c041205340e011a0304060b0301110a27061112130302090f040b061c150903080a0203060310090302031b01062111150415 63
    0x280c018100010045000204101c018165081d681a140321459610b1105200c9c9006451300c0c0c0c0146840c20746000a103141e018502d5206280012940c2c00d40710b2503105961026025039a40c0d003802588a03117400d90b580784810394412409194030030301440010810000311000300342141e504880c000031030000060920302203500007510381041940c03084c0300c6040503200c031440c0908801601480040183d00142403a064408101c034420301c403854041c0f44c1c0d450039041e9208030707181400c1c4803c0740100940340000d0465490070342c1482c03140382c200310600e82e2590307420104030003030000050300c080140c0c904e08400702050088041204400a5120000700d8110600700546076140007003003404139074010400c2100a440115803203408101444010400021618060342540114030004000140c8500c00b60881e07101504072504079040b00c030b840450701e330884515507540c070502c0034060000404103000301c11a040038030307103000c130350f6030301c07800a420700d034032040c2d8100d145240160031000035000b241d100c2c4000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 263774064 1250 263772814 263772853
    0x90302060105010e091b030702070906090c090509070206010e1e09060601020c0904050a0f08121003030e010c0308060f120d051201060801060f030e0c0d080705070906030b010e07031d 80
    0x904103c690400525100c400711000195494a06c5d42c106000710100d80d00c1402040614050048000180304c4d40b0340741c1004500030249140040c3c0045d03034065000800b42080007c0a0184a80b80c2c09064070340e00f010500720031400c1c040e040024001c07001c0018560b444008d0701e44d034028004040a0001824110002403500561302e140d18800c0d5104d03c1803000050000400d0760006600261060340082581071160b024040c840030048900c000108008000b6564268013054074829141c040803246104011120110b5900d00100402c100601064039864018001d00860b0270041600788000007400c40907080c1039000441c1004a07e01284205582c04811201809000c461900100b00c0d0b1410030014006440300d403441080c142d80d00c501c034010600503c400800200d014020092880c01031400b03000d207030310035081600d1a001c0c05170003142c94801c0b07000342e80803240c2150951005074203100110185a04c054004010305503501140d814038140480050302040b038200160148545545250184 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 263775314 1250 263774064 263774087
    0xc03030423220c03020702040c08090105090f0304030f020303040503030403150501061b0b0a060e090a03030e061006050307020a0204090605060915011b0212030f190f0903170d09030206010501 84
    0x949842c0c912507107148200701111454041d02501069940c481d02e4190000c0c8100800070750000d0502400340062900102000c1c042d034100070007002640d90300d540c415100d16104840e01c8440d0010001000495510b00d06803107040c0c001000d60b45040d0342c2d0741c0000e1950380554800c0300e41540300e00c500d002d24107241c414180186050304241140304c0d401d014000a2000922008000c1e00c2c55001282120381554003000c0034000c0c080410b515401c1070300704195101000d042c1140041d04000000090031800715417240208840c41a0185044c10b1030810384d80c130f80000f48a8800c5204141d800c50142c0e54034064106240d004510015507414048180b00451714001c0ca5040c5200303c1404052999034000d040440d80091100741c6c030034405030b07440001c0c02e01c01c552403c0360940c440414031001d00044100180041211015601031889040c03900380e40600a403404400440c440580800100320703401080890403441b4001103140c400c0b111310a01c1150403050094005900c07113401030206582007800c5004c03 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 263776564 1250 263775314 263775319
    0x10e100603080901110309030708010b0301061211010f020f12180f0901090c050405030303100602011508060a050c07050313050102010f1109060d02070f0f0320030901110c03030423 79
    0x20306800c580720308607948a180361450400caa502030003a07026501344160703215841c0083c00d444e201c030358840440b8085e02900110620a5284c00e10004500306c1c41c4205c582000d038081c2035a01c41c00e80030310040d94180302c120100029801a00b01046007c0001d004428030301c407464503c41e40724860400311011070118211818000c982041d848007041d5100403e81e411508507000105060f800789408440320300642d405540c0501c004020b0003050203103880040d06075038456008004071440541c0c2c243e030b940c4851080c408550005000310700d082850742c00140e8408810300d80d40c1e241c10400d0752a246154860500103800388816201442903607420300031303000c011800c59018010042c203c030b411050352003958105445020005501012038150b9015601c91640003010b020150721541002c511000302440708400160b00d00900c01100c443c00001d140b0340c0c4040400450030040020010b4642c040c544803603482520542c19005040d54003040100050483c855818600c04007004608007501c1240b01200d2 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 263777814 1250 263776564 263776571
    0x10207051c031b091a040501021b030309030a0b0912161214070807060e0105071b0c0f080325030504061d04020c01060501090f030302030a0f0507120c0b090703030e0d020120010e10 79
    0x7c941d03a40001c599200700201c4d01041c805c0c80040c0c000a20f0761040e0801c4c2505409040031103401d010703240c0403061060010006880358420700f9048014540708250003140501c82500e82031010580e1004080003034030003400c0c140c1200c1941c6010300e03025004900e08450310200018405d080250034000d0250f00181d0b10300174072071801d00a8016003081c1094040c0410b141036103000209210350b41c480031008003c290929422161202146a107a03440500d1418074032400226102e480c00c4400e0900c11a1174156944a080070b041c0351003120788180000d00390340410603542c0c51100550381d030f200034104258624000180b0701e1600c4000740c401c154a0b4001110381004c1c0e042000440d03004400c94020300c811303280146040c007000200f603071a4011000c001c3c07c00d4289074201c801003a000491102202e016145001c15a40d48850550780c03004103000080004610703412002d041d00381908100c081c81c0c4141400720682d030118020070b80c0101070f00c0f806010f41e0b4440b112405484010710084114007540790052 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 263779064 1250 263777814 263777819
    0x21213060f0b100c031403011706070504050604090c03020928060203090604030816080d0c032a030c1106041a09160506030a020d0c09050a0503010207051c031b091a04 73
    0x400107150701e00c0740401c3c0a40421030740100b602c940c42c00034290268546e45902d0303584030204652400001040e030729a911903580841c80742d030b004005a07801c43d64001c020320703e4617040404070f4029140300d00d441c90038035400380640e04407907890101c02181050019900060203025888801e4205000c5c2e001a095400030064000251111130481e0705880d048920a5668444c000da668815402c004010300228004a0701c0407410b41c240d001800e44801c0d0f55000d102c034030405480c2030080d101d199500c0110280c06042400c40318080c0d08260460111800d000d0401d0040c10700050030201b081f60211001148413150b200d0100c403103203945811504160080c1952251000310742d01e01c00c414042c1a04c101d001000007030034002c640e01100c2c94800c4180003401035a18000c400740c5141c9050040038454481c103180030941341814400d40b00016044002003001c80e0710743c60300c4200019085145000c154440c4a07222154046811780f03c03a103003880e035400b070106240800d4040c500550500078107030300c0400c1008 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 263780314 1250 263779064 263779069
    0x112090f060b0307090e0a11030a1205031b0a05070f050c2106130210081003140f0c040e0c04090204020f07050304030302010b0303180112060f060903110301020703050a12021213060f0b 81
    0x401f0310380e122021803144151000064540a0320b081e0007044901901c0c17000328010b41c0000554042c80c8100b8842a05001c81c5007503010b503018180700080021814131610780490710b00c04001400038001c40a81d0042c5624401107400300e018821100b440744580070701100350000401c5003540c40544c2080d0146080f83e1540041c0345400c00060100030440d00300f01261036200740e442d80760700442d4418030040d64610018501610f41120b00c01280d0340d40500c14203074003642040e010f00e6202a4014018240d490022401c00000300044282aa00b250b400d0000c000c2c584000304c0203107403442c000d400030b646581c40c510303009082d1520044068000d80062125448200741003e50b04588502420004d2468016004101c0144041d40c014210007541b04400500710340c001c80c1e22001d480c010a44800c3c842451340515090307100707200e40140065410003d582c1e800e4410044c2c00040c0100328005442c1007818114004540c005442200040707607001501010800c40e80714907607901240c441c083c055803110100 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 263781564 1250 263780314 263780323
    0x1c2f0306010c020d03031103070c0614040201090b16200a1a0403080702060c071e06020312010e0606040f0e0a0e0a0b060402220b090a1a0304020112090f060b0307090e 73
    0x4009000e100420070190806001f90010074071a9080d190382622807801103c01821020610000e44409107454000050300359041212885290107031038003030201d403400e4041d03d41e0fa4446050810503141750303040e040000310800440294200b1903144121024500c108204000c41103a2000140d403410141569400303100d80242c0f001c50341c00c0091180c0b100d0503400410720a110700c4040a1040c000c0e40380109a03e04642841c01c248504180034843c0a0b8880c501640e50b4401c0754016030b010310300c04004102e8208601c04e501d0f409200a0041c5040564400c100d140781205500300031f00d42580b00d41000b900306440e10401245000b030000034400707070720151141401c03810003400c8c06014a400090030320062644204004400392240040c4401c1caa44620007105508202a8144104500c40002500d4800d02602c110940c001008241c910384443d40192240303480c01c42000509a21155035030049249001c03e207400d90301170500030441c844568205401c018264100304a05450300c2d80000252a0000c0d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 263782814 1250 263781564 263781587
    0x2060906091c0302071506060e010e090a0c090314100b0628090b070305030a0f02070b0c09010216080313080105010f03030c050c22050f0601080406021c2f030601 71
    0x10300c1c102c000c40010110041e00c68888050100b5045158000742081540c2c0701504813420340c0d5400c0844025540110b85480031001c1d0240e110741103202050404203180d20811342d500e92400c5c0043c1f016681c0e40c8020002d85881d6425103a03402110361404458043e001d02c0e01e074480d040380d884d803410b1b0b45a5004a4483c2620307038030b101200d9511030900c1140d0300511000d80503015844056859401d035203070060030f60b4001c8601d140070b5070034555000703c240d4550080d80d04030380d4050100c2d4401e6640503e1580c0c00d40160303520724118480c5c4003541304002c0441014401504a03d000346a41e140714100d0b00d44803045030b500c0000c0d40d070f05d400010081f90b00c0012080c01a07a40c549000010a044e50a0403441c2c601d04280050b400605010341000001c0c140c17442d82c0c0d1202c072440d01442566110100001034036401c465080c0440c04480000b00040e0599004210b440450b0078020841c5007080000c004590101c1030310300c241a00b01c0c000c44000c1e090808921881e400c00c0e2049841c515004000811010440c0c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 263784064 1250 263782814 263782843
    0x9281110050a03200c0106030c0e0103050c09040f1203091109090607050708040b04140108130503030408030402190e0a0e06090309040b0a120b06040b03010b1f18150206090609 77
    0x81380004006403a040b1112490342d48030100f15207032103c80038064003e0985110440300036101c5000060781c0d01283c0701d0581240e81002c00b41044034000002d1044011004008071140111101c9000c005040c19010a002036038603500012400114980300300401e642000c603921800c0440c042140c0d03406d0020b10280c1c003103003a2038901e03258072492901030f2040c090f0f50404d64004e1004200412424100b00c0e2544810400345e8801c2e240e511141c40c2c40c89400c40b0b071440901181c00400015001c60307242e40045400c81d00c0a02900782c0310b60f8407911110443c1c0103802c0b204601240100784610801940549a034458040010302060b0500c041c0c2c1c0707903032440341104140c00341d07071681c10700c0403d695083e40490050181482f100c4000e0120710b060004050101c41c064495494207051441c20704051261840042010f080e0000c1042017184881280c02801002c0042005004101000d544d030b0b0201c54006001040f40290441ca4504021781002c40050405140e5172003001080030b11140052036180d4035018 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 263785314 1250 263784064 263784071
    0x5120a0605100503160e060c01050a0b0307170d0518030604060903110d080f092a0a0902040303080a1d0a0f0209011205030403060e07051012050702031c0509281110050a03 75
    0x214400301c1c0c00c500560741c08d1901c0e0352070070040111900c034a41110002020481c20345044649800380d907410586085130002c9190300403440c03e580b4034000d00040441c130043e24070540082d0042c1c0e0010386407030300440341107500b9600c03a02c50000b01504075a8400602d00d5200c01b5100d0f141000100a01d0f2070402403d42487e141c8103404920719942c10301c1060a100c02c0c103554060000a07503059203e014044003002801201c00f540002403d0280f482035800380e9a1503511000d480d110303035214001410408604501020071000b00410304403081042800c078511079200e00d00506814010071440c04016484414003840b81d04080d000982c020044605032607001100140e489220341c2812700d04642908402e8100a09528009419400031050074180d061210300748001c1c0d50300e05003245c99028803804555080c2d80008400300d51490f42c1c100943c001100012980144902c4d0050000400130b80468403205141c04090070500c00e03e500954480c5034192106503d20051080040c414810002500105a0b8 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 263786564 1250 263785314 263785337
    0x60e06060a03090609060c090e0a1406190902191e0203040b131a04080f07080601150509090705030f01080303010e040303020705150c13050f0d0f0305120a060510050316 74
    0x101390344205000d58005100304081d03005824064403620360f5018048082301000c000401c2d111007402031958800008000c044c140d2036410a01410f22215081c0d4003c802c03074000c000c10840f07181d1016040e40b4000141d428003101d00e00601030820220031481220340c020103144e2400858000084404450045103511350b6809681e100c0d0f142c10f800d0380c101c000440c450025000000c1c04400c003070f1054a03101402e444c10185807a00d8141e443d07005101d400c201303411010040210130801c6c0d0781040c0c101e50a05050b8078000e0200f00203202c00308101c0710b00011400210501010001d2101d4242c05496110b00031413641d41080c0720ba51001000070030043c00c02d600082d11000f0040e007407014030214880c102c52040a820000b00248180e0002144411010380c0044006490f20f040f03890b4a809820252090b070a000382c94503150b82c07010102c4420350030301c9010031101800850408007580709081011000a07540e050004205d400c5181420100410106109000002103c0b962100b800451810704240d48031 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 263787814 1250 263786564 263786573
    0x3020d230429070c0308150108040b090106030605091e070f210203010e010f150308040506030a020c060103060f29190803070305030405010608120301230a06030b0301060e06060a0309 80
    0x1d864003a800c000c0d01c00c40b0600202507000501c41c154a0320039104c540d540d680380a01005003408032003400340050f52010215010503512040b01e03400100315000407690380c0d01c907141c0030140c600c103507007a200d51b03444000c0e1400e9000e100380803885d0001c54100900442e074504440000390850740d011799170380004159100d646038058840074441442d40503009008482d86004000d0082020b0000520054103280903299060301c0d0800500540c3d03072003030a180c00c103406d200034003540d50030042108200319800c0040300c00d5854100b0850f07008500c1540041505010040c03024241c803003020311200e0315001d0801c0803501d52400058402c08a13825070380404101800e00b0302e09290b028079032041149000c005009018590b0000040d4802c0d40524000e200c0c4984d5100381a9440c922000c425080d500140b00510184070300805140c041c540c4007007181070604200001456148403948454080ba2381d401c00c2820904007802101c0084c241640c221425290102c04201c6500c54008800d00b010b648031824410030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 263789064 1250 263787814 263787863
    0xf200a140327010329041a0315060a1d0714090a0513150603060e060a080c090a0e0601060309060e0c0105041701201b1b01030504031e03020d2304 64
    0x136041703074101400a03c1031501c01640c00c0300725003074021410310030040c0001d11206089080c42502400406825401e45042c031550100604000c2c0c0c05104004006a54080741c001c09080c030342c2e4090390b900241403514020f000517a24408841c1c0c200d10a00010006540f00e49184080300c0042d141882c0320f90880000200400362645440520010404003041890b41a84004180c46020346c90040740d031904010400580030900c200b940941c42074000d02d0043c00d1586515810522140000c14002c010004060424030241c005500180c3e030744d036003d0107100c04c41c0524640508840060545503240c500000d201d449a4000c00800049804180b0000c1c04254402000000d03a5a100503600c80b2102c2902034503441000f4001441c01c41040c8042c1501020500545000c0c401d07221600581c080307401034019010080c4282d0522a0200c4d41c2140300e00000c42d22150105255801a0b845900001c0d00342208c0714801c05500c000020701c8050796048520814540142c0c0100145803808425003015108 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 263790314 1250 263789064 263789081
    0x90d030507020703151d0c191809050307050d021609050f0402060f0c0a0804030339020f1f02070f05010507170c031206090105010305160f200a1403270103 68
    0x100b1626408103003051b4808106040d15940440d1000c01c03c5501100461000b004c03800307801007a4010040da004202100e5200504080c887c0c2c00341e1b41403145684900781881000030306000540c212401d121030382165049000061301c0604c004014905052205214402c00200001c2c001e81c0009800d0003a002e200040e181021011030468048040c2e500d020030071a0010300c400c8000c00c240d0345560007507001c014a003111052030590040c07811204440042000e880c01003059820122900c080002501d4030052202d88540c4907600c40703003458803000001e19152007a0f1016075507000800090080d81e03400f070101d8400b503421640c0c580c1c00e900c0d034411018007442110906060703403000103011010b12009074203652003180106d402c080326a90301c0c0d0042d003e032b8208035241d0b1046c0c0c806c1c05900c40b03498080c1c8051107214000d49040580d80c0c0000551014a4450140a03500d60340b1005040301006602400c6103062007502c1d0145050003009480e080038403688411b85400c003013102c140d05100d40d1180e40420f0701c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 263791564 1250 263790314 263790341
    0xa080a050403120b2d1306061d060409050c130906060f0e1203032401030504022b14030d060b07030507140c03030301060825020309060d0f0e06090d03050702070315 72
    0x1000d580003070380b4050f081e85c1405a0180021011286040d00584501070496000783c981c8080020b82e036202244111181e4070007588a42e05000c049030108451040c90b20900c1c02d800c030507607585400140e0030500304c0d49a0004100710305200c4280895030f402070100581c1c061604103d081180d40000243c5800061001420380c2d00c4048204403001e0001108004801d000c6c2e1105812101e8000c0110299401203401079001003a840d4a8401000002464000d02200300000c01c04c0d0740b80c41d40c0c1c80e1440030f13520b944c40115910200e4400f8031901c0c644603d4000f0320002504518000b0310b0741c0c02034a280901c04c2c2c05440702d5100e401c0400c809000f1310001e21000307802400d899030b035a15801d001c2e00e2440240d958544540520040648040c00b0480c00c45024045030002c6040103c240104600c030781c806203100c10070755101c2200400400c000e020300000074003940098001c51030312440262504080b083e00c1401c042c102024042c0d00303a00402c050080e40c0c0c02034903180071000030100003c051301c1c94820460 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 263792814 1250 263791564 263791609
    0x210151e15030c0f030b2d0904030315060201151202030f160609061b060b06090604090501060807050313080d090f0f02011107140913020310020a080a050403120b 71
    0x2080d96034141e020380400300c0b040e201c903138903150309110032022100d0312445207802c03000f11031900e0200940d80c1301c01070780102501c0074440005480004143c94806c00d40e0b0413008241c03500685000d217030250880340b0241455200800032100584a4100c44034200d2007040800301031218280155181070000c201807200d007208548461700304c4500b12070b40741040c2c411070000a10446002c100c1c64820902400018400c1c051005d42014507110314000700ba80c55403155024104009100ba40d0b2103c1028000400c42400001490761401602401d5564002c12420070040d0401c2040769254511080c410415080f41c2034503240c0c40206160b00081500717090141c0001c203a0001042048500803084900301d10030790340d113605d4103084240c3c103554401a000b0660081c1302036801164038181481d0a44c0c0c01210564500c00e91603880c2c01190902e0f42003103100f910b064000824486039034000514603040b0540032420401c078901383d01d0050840b4101508608250b460b22020122551411080010170000c200481e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 263794064 1250 263792814 263792849
    0x1515030b0603042a0608100509010321090807060c0c0510021e0c1e01031103070c0f0503130b030a05010501021504020d0f0542071b1a04030210151e 65
    0x14200200841c0c10030310007114588003148c10308240c40348a040b20750058000501040f201410700c2e0500102021004003d80001c1c0001d801808001140044c0001c0d110785088cc0c0503810551412001504454056100040e0300b000f0350307038001000c400081406004078500a80c80810505126a809213241c0c0840c1d012414030401c801c1d4003d40e58041001d803130401850b0b15400031518940402c64600307001c00c81c4100a800466400f000d41c4aa06103c0d0003038138540301c0091864a01454143c00034100b111022040101c03041a43c0300d403601420090004000c1c1a012550b0000340c0400108001d0044a040e0705d12000c00c240307030503240c1005e548001901c491f040042051140613684c0390b505804109640407071900c04010208000b241c0c0044001c6013465038542d4001c0c0c4514202040745140d0100c000a0400801c0384001240d06100044504032860b041c42e08000703282107805041c41c042c4d03601d401d0b424412184600150340c11035282e0444002d109a000d00201d094154952008d0244156941c12 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 263795314 1250 263794064 263794067
    0x1902070606140102070f0b0906040e0403080106020d0206091e011e0c02010c0e090601051c05010806010302122a03070503100504170a020a06021c1515030b0603042a06 73
    0x10609480080c400e02c07035204480c100490355001c540c403401c589200001d10074000810b00c0e2000703050b0350344050b0030700d46000e036645910890641c0451307081d00001d40d0a00184041c0c0d90500c403203201626188018070050a08a000c6521083c003210030100c2001e16440caa40800740039084800d00014103040c11038040c141c4662440a000041e081c10015448c0804414200340204101a1540009410380038140d440000640b070540c00032008085148810001041c1304031203005030b6002e824071001800c0a0352441c4184044001c03100e66841d502d40040141c00b5403041305a60501c00110180c079074a0070304d8140700109082c103075a034003ca60103000d55821200e40e10240c3d0001401a0300c158005400c5410140c1c44100c3c6000b103204200040e04440807400118080d034010f05100a0b480091840c11a907000d15402150710300803000d908145c03200e00401c080b40c0e0404050b0940d8400781814480b113078003600003405038840104002d100101c02840c0090310307025511418004a84040c0d07490300b0a07201c503030 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 263796564 1250 263795314 263795321
    0xb031f08030a110d0302070c0b03090a0c140f060313062406090e01171c0e09040f020301141506070c0e0718051f080406090206030a0c081b0403020919020706 69
    0x40b10200da10518120740e603135610900c22200a2030f00a103010b41140c1c10003114100d29030004d001c2c0c0b00c15108111050000c54030310b0044200030240814040c50012195050144071060711600910a8006204201d03402641c450303034002c0d1a62000c1e0016502085100c8905107920f5a04950140424250701042d020742080c142c1c402e84200380c0280320240c0c0c0e00c0704810031045030034888411540000301d444908035214074000c40e1244c598103215401782c4600300411034103c3c04503400c0d210b162451074084c040d41428444e60920700540c0c03200d0b590702c1c50400403c0c1030342241e141d2918000c0c00700080d0501400701c49100200a418054691046402d100000804221a4206e803210800c182240018580b03094044201403611500d00c14034500c840a40030f41c0c40e40c0004000351502030321060040c00580e02e40700114400c0d042e51100007000c105140c2c2c0109400740c01494108905100000c003203011030351a046d43c0c110380d412a286d800c0b5944209001000030051040d640d4658004101e042c10880e07980c0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 263797814 1250 263796564 263796587
    0x11b0f150f060b030103030906080714070b04020f0d0809100302090d0b19020705100207030e03061609140f150403050708030a030e030a1202090d0507120b0c040b031f08030a 76
    0x40051200c00d0f120489461284420304c0010042140b1440c100440341c007440326164000341c1400c0542e41603101d400303890001d0344a9882201c0c1029400204811440c1c4022844012581074039207040014003035440c1c24841c0b04212036144140080714801d604244240c0480d4045040500620856031042c907006602c00340945200e4400c81200d03408a820500d0340c82075032861500440100b504c40d1000007040029403000c0300c142c040007188521510662002c10610740500b11640038448084400440146008601d070040306250070284000c009960b5852914641d06004030317510103000455408091462155610050181c042e1070800640c002c0c0220280041c25006d03201800a0b441c030002440e00c03031084142180101c1c0360340442e0f01d6540600d078003420f05180080d002c01c200c2100303520344a290400507402000e03104054103c2404120301002e100341c1244811161030b08181c01c0980d40f10b21400001c00540c110840040801086503000d031103032006000710010b89681e0b08030302000905004800 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 263799064 1250 263797814 263797841
    0x905010f1407050d110f0703021c0c0302060406020906070209010305030301151b2411070c09020418050901150308130519050909010b04061d010f05011b0f15 69
    0xa411965122100624144500160354403a8984526403000800030140f074210a00841402d01c01460072400c071400031f140b014003d80040ca0010543d194852440190418076020010317010b118100203074000031a56009540680d000d6180d075070000100d951406661000b81d84012800000424030002000031816100758a07044280b850841c2000c0c0d4550319400c42d28200030490300c140c0703004a0500354800010b500584001c090051340009400160380703211445403c2c4640010f200410407c040d076952000f0a40318006506140c500003082e01c8114049074120505500e860029940090a500800c0100304500341d501c1c07070366246d0170007141d00e030440354502a03070350342e40d81c030124032482c003490b224280e0080c41c40e1502101d0305003018006004005803140c4481d41d255404800c0b140c0d00e40c0a020040c06039503d0030748014003010201303441ca03074040c0d2190402124509007441381d030340c4c002d00524008c40348103803894103143ca5152010000c41c1d06440a4038001c50314004002c100c2a5400c03100c1c0c0036803031 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 263800314 1250 263799064 263799071
    0xa240516051212070804020d02040506010c20011b050322030c09090308180304090e01020c0f0d080f091c1b0606050f1e190f060215010803090a05060f09040905010f 72
    0x182002170b10301c0b8000740d5000e50300900c1d0300742c918018076080d00016442001032428244194075aa00c0801d00c2c0310f03420f203400780c0151a5265a40a503485410102202c42c00707540700c1002c46071034803983d40307138803800744040000171807289600c00c035503003075104540116403159010301c601e030765462101d0007800310071411030020b401e00c004180c0300107030504500710029001000d1454645016a080d008000c0d20016292a5400307100c1c5080d100014015081c8079040040540b0100a518000503c80c140c000c0400500c600c40200740000d034400043c1000c4407240c00e10a042100f000c2039402d0700d40c6043c40941e00c1d030f1400c0005102080261541042d8125403040c1c0d4100d210040d00e1081081654841c060540444586c2c5400c1c245440c04800c80080316400000002d400c0c0d07102c0305d440300150340b0380c5c0052000d603024003420040040d491040342d0062150602441c1040580000114844001d01c00c0b148110808545a0b034042aa041220700310840104200319012030307442d245000e0000303145412a154038 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 263801564 1250 263800314 263800321
    0x1b01050f0a02130501031e150510050705120a03060806090a0204060f08061b04031e050709060e060409080c010614030d0c0305030f070203040b03040f020a240516051212 74
    0x8500985250359400181e100c10f00d4144001100140000d000c0c1d1007032040c0300380d640344282c07165104211001152420868001d400c0c0301c1031180c1c0441255001040020802854011481c0403c407100c01280c0900120784d43c00f0b0509046018125030b400c10000d0303020701c5051105039030307001a100d40718610958062094a80d2078558100005061141c3da0701d64002a0000c8d0f01185268092522202d1660f00700d81499203a840320740d10300e403800080d03458810240840f00305003c0d04010440c0100b41c1040248240f07410b025030554600005418203004a0700c98240d01e040000c41c03000d940150380400001c11503e5504e06055005400c0100858003c5c001c600b4210041c0d4410340402d00d44c5501919078610b161a88a002c2401507030013040801140000e020204d1507030310003170046006500581028a100b1814010400d50f181d0581c44420988802c080c42c075003541741c1c0d4a00440c4905141441a1294000a03103010015103008004120740201d05e0205280040d01029014500103112022210b94 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 263802814 1250 263801564 263801581
    0xc08041406070906030506190e0118060b0d0507020c1504050a0e1302151218010b04050405060612010603020a03080408120c0a08160f080912060c160302031b01050f 72
    0x108240c821100003071440c041408118000e4005a412180c00361070141c2c00b00003e9840592a030b0103800c50407c9c1d49440c4010001030f085000c05035035024580d102003200da0700c0c100d14900b8510440a001c6401e6840f0341c005043c1900038080c0c07108a0601600c0300180e407050440d001202d501c02d0140c588200a20741020604064001446102d40c01e00c5400042940c00b0740c00300100300070b0070071f41f08440b010100f18165507542014100790046981818001110700360f42c141c1825103501d1054240900c1c46c04c003c200104800044080c0c0051050314043c2d08038035505401c4e40500641d81002c1d4000003428000020003800400a00441e4460410f0340c8410b8034880c88801107103d0351800c0c140741d1784450222404030320311100410750704250280001a4a481d5034a078120040c03440815546500d0101d805c403050308240d0512030b810840f11014040c3c0b49003a1100b200305005134040510b000002621640030980208122035a584400101c55001c081212419010b410102d884101e0008428046290314 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 263804064 1250 263802814 263802823
    0x180105130311031b010606030b03030304020a1403030d1d062409151908010608030a0512040201020f030d06090c1b0b070e0a03030306050f0105090a091e0c080414 71
    0x800a25410810411058a0440b40d403401d1505904880c041009103074800c00080c0c0c058520b0b00001c80c004a0400d2400c1c001600311110300441c00d009810070810840140e544880d07081c1034501072600040300080d03540c08245980102d610b1071100e207140c44000501e405d43c0440800e0000c18042c00c584a030b9072002c2140c884900c443c800b002c01141107012a022901d0161559a40200c507131909581321044a80001c0100d2241c1056070100c80301c448041c01100428080c0c1c1b0082c10045008500d09440181c00411a02c190a428152000c0440128003168170034003201c0c1d190100750040342e80742d000000030003000704104d03c50081154908105550340c20300801c84080000c42084140418044546034481140c03002040001003080c005288005503031002805400786010741d0b0300180050402003803000321200400d000381400410321801500790b840340001403d948848a020a1504000700c1300501c140c282580082214104214a000702c2d60000c0000e00c128042c0350324075000040411071030b444 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 263805314 1250 263804064 263804071
    0x60e01050d030504030303020702040b09130209010902040b0418110301180e010c0816090e07030c0806030102070f170906031302030c0d03090522020c1c0518090a0f060e180105 77
    0x410004d0008002190180d400790038194009800440e01400c03503000184800d44c11608203c180d942c0403d24401e608124505034003500c240001103150600340f81106000e4041da106003800e040100042401011150300055001741d001c1705000d03141e5071070710300d2626100858652905901d00c1c0654048040c0c0050242040b54002901c0d11100c0703440e0400c448040825010480c0140311000000080140d1400c0c0306520034240d0703507400950036211020003480c4038005002680300303030300502c5800085007203080003a01070350340415045040c0816440002c4180035180840e98400c802008100f00c004041401c80d606901c00c906641d902d4001e8010000030786c0140344058002100c0701c03414401400c0c504146203034060720443c6180002100344003441680d0142245401e55008000008a44400313080280f41401850405d44e090010b2050186000c401c0c655003103108087e404089140c0c21b03070031341c82030348501c0200409001080e210343c4450071100090303c11402e1a503014801044031107041c8900d901 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 263806564 1250 263805314 263805317
    0x1021204140705060d050a1808090118050a0e0426070309090c14090d1b05120d020a03030b01090302040c03050103020306150a14180f091908030610140d060e01050d03 73
    0x91031300f141400802020028514401c0d180d0b08c441c2c00403042085054401124400c00d007041d03445a40000040c4206500000c1440d8200c8030441840740d035540c40080003d40d00990700020032076485082540c243c003030314059218002d142105070f078500300e01c010040200074081c0d2103d80300d482e541c002080031660307420310b0307040010601c1072078107103200d07a1100610403540c0c001c080490305149074030341482110284079011014203403564100694101800030341001c07581c6102a1102c0c500014019440c0c0041c14002020580d565421000d1a07000d1901c09001c2e5401910030020385596020140c0108001c1c00182c4c480d10420b8009084966001d5441010a5000d05040e9080345040120b034011807411130800d40c0b1590342e6541811685c002c902607841640b2804104130035003840384c074a505204030740a141c4142e03c402a0b11801150700801100d0300300b00309681800ba42e0b00e0000b0122200e165590111184c420005202c039038858060b0080b00030344038400420342d0181d0b070701c0c3c0401640f60b900c1c900080 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 263807814 1250 263806564 263806567
    0x61d071713300c111806130501030312020a020106031401051b1303140a02120604110102030921100507090509060613061b05060a060306140f0c0d0e0102120414070506 73
    0x84818403503610f2095030b81c400c903401182d546210f80015820030340c02c4c812044001003641085207600e0f221200c04820f0590401c200511b5066407002400c01c400c82041481042d000542c0590030b038401d5006000a50300125010b07250860100d4a60282100b540c512001103480209003114110382801c89411528034034005442902d15a03c107100c0380402152007140b0700440e0034890150b120f000c10440c00076010b070003070081860286400d0740300c2801e00c9586c5d81107600c00e00c101000c68407046c07540c401c1c07003001d1102406245c90a904d09450005000080c0d4001400c20003441400c540107040441580d8080391103035200d82c0d0394014811240606500c01103154881c000400c2844d005150b0f41c0f4800c48565150300d0300015a813195440c0900540781821140d03559441001405460711441e010711000088000c0d0701c0c141074581c0000540082e0074541c0804000170200c0b00c2c0d40140e4800a40000c80c0f03402552134500311480011210411201502c400e06c0c032050030241503074042402c805844c00203001a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 263809064 1250 263807814 263807903
    0x30d020d02030a030e01110430170702030a020d050102090328110a030501020c070608071b0b090a020a080a0203060f190c0c0b040b01060e0301061d071713 68
    0x13140948006102c00240e9542e5440100e45203000c0d80043c07014218000703005150541001076845102e25030b07032a02c408840584510400900f042a000c81803c800030100c68842c6000e0000908084203802c000b54840c22248618041140c19005419960700171815104035540c1c0b0412070300401040703c08244800740c01000c40000a01041c1c04800011015003102c1004e80c8031b556450032644070112800d4a40d01848080109550048400364407601510380149803800000c85083e00c074040447c010001c0c14540001110341c4410441d45580d180c00511740e50340d0303a9a41004984581c00460142d00a02450000a180d03c01046c1e9042c02020404584c7d41016014004503000b84040f41c04030082100d0b00b1072007000324541404050003503000300104100d40d4500040070f00100c40c000c048501a9040030800c00002989103100b07285071b0b59041001140707a03140c15040f9000381c03201840e078026200001c244030284600701d1626000d40e1207000100540e403880e01d0b503403142442400044080c5c14901400 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 263810314 1250 263809064 263809067
    0xc02030d0c020a05030406090e01050604080a120e04060e01051f080a0c0e06030106050901080a0615080c0403050a0c030501050a051506091914030c060901140711060403060b030d020d02030a 83
    0x5401c0700c03003403042d1455121103650300c82c1541c0c0a544004009440f01c2c1c01404080c03000c40d1818018a4111030703584ca01454082d2140c1ca804003250701401030b9403260325064406004068441d031681000300200255901c072030980d1109802800345501805595940024075449001c0c260016402911110820794a52442c80d02411900044104004040502c2042601d07a6000355018103010f0701d0321a22100004001404820014a1032a1a44c1880e9003040307007030038510600ca034240140c07910140c19039805050210301d1045610007400c0d441185001d0b0140404a141d10065a208100a0000e52158100c45040d1070054071040c2c400101c0182d00d011619000c0c00420313030034201801f130341104c550283c400d100c0c41d45507a124491284081000400c03c1c6400d100a038180481241d81c5401c2102c10310009000360810080003150803030005081083c020f91011011014400409055407581c076803a005001e062080001402481a907401c3d4502c28008110403250007401d40c011814800e07403110 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 263811564 1250 263810314 263810321
    0xe0d02090c070302010b1005030402010314010e150f0307090212010b0f09040b0d15050115020109050601090b030f06100f0b0909061009030204060b21010f09150519180c02030d 77
    0x10843c1559a605408000e43e00e4440c0d0508521665803200750700c1c0e140c0b500014040d41c41d044200d403100a0386a005000408441c80b07d250080042034002c5c03d45061200840c903c20718101ca456498410b8140018003a01c4940003050b100d0b42c510072400c402c0e40c0c3d8804418040c09076100010300b5510502c030500103418240c0c0500a034010051003407448070a141c071030117201d500440380042c00d15100c100501c03481c039a5054200300340ca41c0d44000c104c2c400c080e4803001e40302c0e00180580c1042c6921100c6540080e9820004186254030034400da4101e0f00382294280e0070300031a0b00c00c1d081841c030848000204088404280c030100207000d0080c103410744e24901080021b00f04048028180503039442d0100140e252486440c1c0903180d02c45680d9661030034900d41c0746000030170066a2110107120801407001c103014010030011203680c20804240c00c10090f5040030720681c1608801c0e000403602c100c400300515210701340001c840d04400c41040b00f65008115a0658520351030070800b41e401000540c007916542c0d0b0 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 263812814 1250 263811564 263811577
    0x31b0f0e0a09060e0a0303061406031605040f23040905060f100f030f1a0402031902061207050d0c02030301050303070b090115081c03061a0d0608030c010c0e0d02090c 73
    0x10800500710b0060f40d2210100d4603411803e400590001e0608010950148540c41c06821060036402d10312001c1d0001441c80e210041c594101c0b1558803020581140c0980181c0e805020418500308940e07880d0100c0d034209100d110f8803902c2d9000b8101c14540b003070909100d42000d007504003000c0c0c412a910b407030560307441074800307080c02c078100ba0101400564004d003090450059482142e503082482003504181294820310001c98020f00c01d00703020b00006035800100c1907501c4044218104514003d8000181d80e030180074103c00c6c609941e001040702d003a51240041203811030310300d0100991000200100c0e034901003401000d81640c0100612000304220910640c1d00c420300c980007145201d0500805205080d4076800522180c0c014005607003100020a260040c1001c10329040101d686044881c810040320262207042a400004000310101c00030b0300207501a1581200b104e5540c40c5c1510041d00a1a20001c00400503855001d180341ca07240032516180900c0e00100300000c0c0f501d40050420165001c070 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 263814064 1250 263812814 263812831
    0x5040b090d14010b03061e0f04050102070501060e0610081b09030c03010c0c02011b021f020f0601060e0102070915050f13060e010510020f25030b01080304031b0f0e 72
    0x4000c00e40096501e40c030b0b106000940000215103240d0780c409240c60404040c00714440c050340314110b01c2030040d460b64059804091403484074003030349031410300c14024032803510081e0095092210108154601035031003401603205030703103141c2c21755403050084540c00c10580c2c0444002c1d44442d90a0715445503000505100c070310040556200140e01030009086606c000140c5010a995103e0481550f82040100c2040e200303e003403900c412600e942c000751400e0300c040e0b0401c030b10b0007140d512161054420450807200c0c000b80c0d401c03204956140d9002912211030003913400d0040c0b040d10004248040c0344d00402102025402484802c5030420f400c0042c05c0c0c010307915264110a65992940303100c151401510001c2c146c640304000203504050501030140d1440a07070b0b00540d4403405861080d6200000c3c04c4416060a100340f11a09009100800344a1115407028107004418000810700780004001803084900c0341c5403118280c01c0c0e01880300340c200d84a1040101d94550b0070002c2080383c2140c0342096000b03156 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 263815314 1250 263814064 263814079
    0xa0b061e09150a0e0105120a031e0c0609050604020411070b04080708071a010f05011403070e060903010e060a141303030c02010b06030c0d1a0f0607020301060909081801080705040b09 80
    0x301000f24004440a900484010318594010001820b0103d500c03550210a4400f80544070038a031009081c20000d800591404004241320542081c4524882180f00764094002d00c007981301801c08030740e551807e4405911651402141000391403001048030840c40e40b02e400c400301a0740e903803114109a003000109941404d410086d10300040c0c1004007003500038078a140c8007200b031350400ba1140307e0710000d60496818040032100d120541c40280d41540e5200c0c6403031a0246000e8803000c0421402d000c0d0307100c1e481d015800d054629000c0403020600e140301c0e03140c0d03100070803003c1c1c0c1e000d141d012640304c182c070000038542070400a400800d10a0700001d10800302400045002104d507000714201c0c2d4011a0400886280802c01c01d41c440103a00850b035028009090000c030842d02c0c0300c0010740900300781d611148140c0700010400110f48082d00908020f2529100402080d2894200042c042d03000603035104402c011207000c48942e6000d50b407418081c50f960f13960340313040606040f80b80f45c407648022805a4007140 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 263816564 1250 263815314 263815351
    0x2a01050121032604050a030f080708060f19180f0204060804021c050d0c0b10061e03060f0905011e03080d020901111204150c080a050703120204080a0b061e09 69
    0x243c1e4508a014034401d00041a13030000e5070900800409003003507180c0c20451140b00b0301080325480600b075500070a0894401170321003460000255190303943ea0240c40e81c4280040e00096000078504005140382840d07a0038802000e003010400c080784290b01401c40031a0025002c21b025042c010614007540c40d40084410368608540c464914142a20800a0008220414540c20041250030b034503003296188d80303402a410305100f8050310000a0300c50786501d08168889404015100350464401020300705d0205800545944219020308024011010120f01010288a1000c00c025262048a4120041908140004034208081d52204044a040003810307031408009540c24484220010808900107035202d11f400d08000c443e511004506051200070b5400318040b4296000b211101e443d1458010341ea40c4040c076040e1042c40d030404221070a148085000b2034198000683d213400c0e02c0c007400c1500240e689910800c8221542400350740c0e0032400c1110352554a08000d05210b80000003481c240b60801d1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 263817814 1250 263816564 263816627
    0x50a0e130f0606051e031b03121204110312070807060e030a0e030c0301110405090c040b180108010b090d020d02060c03220503240703022a0105012103 66
    0xd5048250b0749a540e400f030800c403918082200038800c01c001e110105000300000c00180d01c9035a051082004005040801e291907981441001650449000c0007031b1203520303007410703104421001c4034111070750703c405540319119180000e440030880c030300e11010501d0003a483d0b464600310703003007040110745158540007031406042d02800036042d419401d0b951508140c0c01d4070201031030403403006045402649805c03480c107025000c900842d81a41d005070307a03540c256289e0308111506482790354016100350f407010800c109401c080c83c500c600c03062000d80c0c1d10502a41c17030341560041486503c1c011688829030f0955070300142000c01095082074001030926080101c03c07034042d42954040c0c04440d8100400da601d15800c110709603a007070086c04d0107400502250403403500c0d07400041c034482c402000c020344803000504c100c0d2007a0125207026008407601401c240031550420002c00c0d002c3c100d40a294200701c004140c003a40b4088518040b042138585150b071046940b019507205002c10340f1045001c02c107a0442141c0c4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 263819064 1250 263817814 263817833
    0xc070b07050a020108160504050913060606050304050111090a05040f060509070e1212090d050f03190305160e0d05100e030a0807051218030705100b0f010504050a0e13 73
    0x2900400241403480e03000d10004116603070003400c41861b00d80040340040d41c140d0100c107035001d40320300b070b05c2208480d147e104c65481c1245c00220010041030412401140b42ea0384071001e14003662040c0000d0280030100e140341c40607805484030540d002060444200700714940398000145943c80c90000140042d11903010a14001d01221000042194401a8001d038141404c181c8141c03280d18000d00311110721090b081030284140c08001d0b100320b090400d070005000080c081072090003021021a6964481111200021045080381001280c9000c00142007106020032800314003c26684200c4620034480c10030900f441c504105076410711800101010048052259401260541b0000c64440a141c440100441e42c000c1c00e00040000c28040b40880c02107030813070181c10030a8080006490f40d1540c801d1482c60044072005440c9200d50304420800400d00e13481104800c0041c3d800f90f81840044006540c0743c0b05520a69400c80d0034510204030040320700e0140d5070020565106c1c0c9031b030b0181035210304144 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 263820314 1250 263819064 263819077
    0x14090a0e010c031509060b040603090812070e130504020907032c0c03010e07030803040b072105180a0302060406020a051911070f0803070f06021303051e01150b0c070b 73
    0x403070307600e405a00c1141c145180034402004840006c0c00b2260604811441b14083ca115813800d0644a521a204014021050300c00c49070400d8404000d41c6000b07500100018681c2c1e09050103201d40c07600b40e03842a2007500515100d90380140429216440b10b0b1011001820f444e010300400c1c841c071641d4281c0a034030000c8145550800720307001307060402c0d07442d04250071186450303040580740c0e0080702c00f0000604018162a40b264120560b015642d80e810000d0b58100c2540ca12000c6e070700041810700064801d00d0740858003d8000b01c0081c0e071407010100d412a5995441c0c01d000c3c02590010380081e0000b1a282c0013001d104005252035424440340040003201c88240142500224480002d0702444640c100441001407113808204900146007101c555100c2c4218400135218060300411803081c448c013501111811000b10342d401030b4140e581c0c103000751140c080240620300c40949101d5050014014050242c2c45141c50401d40c0f145072070031000741580da02659901120f03000c2c1c0f00d0001030700d9000c040a0143c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 263821564 1250 263820314 263820317
    0x503010c0225080604031404051302120714120417041706070806061b0a020a0906030b06030a08120702070e0a0b040c02070e01090b0f0a0306020a0809010614090a0e010c 74
    0x34000211101c00300710079160003450545114440070400410002913194105805040005400031070b51007540143c0f0941c1c201c25004000d41c0c0019008080700e41c02080196600c901c1d2040e41d40306d8182c01c03a04940c003094070841a803001d00c0858910140d0f6130b0060b4211340300390b08100e413242c8404c40428180e00507030701652001c804e14940d41c0c01948140b00480d0321031198030b850038180c505800002c0d2a4003603403602e244010b21454800c1c0c0041c0c0104030858580b42c00514507907480e540e5a2400001c0d01e2207010484121541c400421481c1c01c0000d442ea09103984424428248003445640015030100100840c086204a180001c0c0c604860300246010310300365080440c05012290911090300d074201c481c1821940084802c10403041d00032049815034244100209456800c1000140d038010a46001c80d840611904000200595540101490801034680080c265200010300303080310384900c02c400000c003444d03101d02c1c002c1c500307281704591100c4081320005089000325121030850303455029000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 263822814 1250 263821564 263821573
    0xf0307050307032d020a06050703122a02071a0306310b01111507022a040c09030803130f080c0d09090603210509090c12010f0501021903090503010c02 66
    0x1070001041d514200905440b00d19804c13680140340e001c00c04500342c0c0d211340030400c0008907110042505c11406400c100310240c0c0103010080c4803c40c0c1b9440a08855100e804640542c0751400e41180081140c9044500e2003000144012482d298616240d000030012a441001200c40482038101914140034220032089400081a140c0444004448801c01d081d41030000c14248404415400a501c1081c41c41703040a4107050340321420241d00e40004068416440420300d03120740b8420044045102443d101194284012103034400c003552229003500024040c400c0420028440c2900c003511850b040b407190120720315040c5507856215080d0810804454982c012031400c0c00900d034800d0742a80901088031707081254074650383c2c076000b25180d498004248102c0005200e01d4090040040d14024072014110201c180b40456840c1c0007a44400702c15101070300c828001080e1800082c0046080d1031042c0c004000c0f00d821400649407626403e8821400c000000c0300c0441c20303440c00e0003104c180c0c5103250001e2 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 263824064 1250 263822814 263822843
    0xc2103120103110f060304081b1c0809010b04060803070326090303160305091e0c090702280c14040f02040f080f06090c1c052e0603020f0f030705030703 67
    0x40c082000141d461043d0018000d00006c00d40c980b04a80e004030400b100549c0c0394400041880c28841100090703801c0303540c0843d202c00c0c0c2c2500300c0c0b202403003095000000c20111106c0000c0104540d56070140c0e00e500c1d8414008400002e0180e540340c0c0000b00b80180c41d080b0800a141c84078244c5408456194060704080140459800600c1d04080206900d05060005240031201143c1d241e112041c200c480e140d1003503411000480070301105c205218060f040104510300020069030350102074412254584d01c1ca148061480c3c0816102c002042d408050900b40e14079200740101c40030399183c01d25510950382d1800c0080c1041034030081c0000c00a440c070f16200b4920703207942c44c0d081018681c400c0440f078220100b000320310280411034a020b1a400c40c0c0740c010441c540d028031103002590303400080c12403048058180103c40c1e02c0d601000031094a44601015041111107502582d41c2c500c0003c0d002192540c2c0003400745402304040145003405402c5401903691600001c0c50201144c0c0184c4140d00c400515 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 263825314 1250 263824064 263824069
    0x905180f01090b061905210706020a08040312030209030a050f01110c10050c1201061701060309031403061c080a08100b460206090c210312010311 64
    0x5020000006000070086a03559480c0c01d00d910600900c0544112103107501c101c0c240705081107440c041e0002601c00d603001010407960900d02800e11447c0344207440740d040006040b62001800f502a203900c9089141001d2079652550340d110490301702c003011f00d40c092050002c01d4404006030000c0d10f01402c001d000c010603203007119003180c0440100f0820340c0b02c108a9003400ba2030000d44040007040c10000081c95685480840855029402d11000480d01e01000001c0b03050307001c000c800526140d0101064180da951703030250122024070a0090206090b0000c082c0f21102c2c56004d15403015001d4189101964600420015a418010110340e41c10f0041403203801d250f407024005900000c10002c1d9880d260800386508a00d00a0301e1030340c1c0002030b101506c02c204040b14120602c000345400d0454602d604010b4424a1820081540308014452030000480c1c0c12800a2088000713200074204509000201d0180080845030b0413184a00b4070003040441c034540000414140254001c145030101d45945031304 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 263826564 1250 263825314 263825323
    0x30f030c0609050a061a04150e040c1a0a080f0603061f090e030c0c27040201090302060406030203071101060617040606030812010f0506093628050405060606070507090518 75
    0xb0254007c5242c08041c0100584002c04401641c41800d6a6110b941c0c0e0380c40c11440122640c1c000741e980740d03206100d51290340e15901c040d04140102c0d4490760a5560703104000c8121000072641d880d41540040049560400d4060718042c020390b40b40c07001c00d03016071508401e01c1682e40100d07042e03039540d200041a0b80320381c1d024801c1c407035003c0c1c085907410303049c24560801c14106c8904202d030480e144110804642168007550100d402107074041c240e2916a507071142c02500030b41085a030007020500c0201b0016820030b042c850070382030359450b4072202d0b0f80c85070003804602d0b440c1e002041110100d1f0782e14400b0000c0380c00b03c8040e01d03181142680904456050581013218070349070340d02c42c03405a01e041c000880240d4403c01d40c01c408444038141c400500030102c820b0079126141881044144180c5018442c600c0d111031000f040940b032440c034034907605c0c03c0010204100c81003210050800c0d0091000728040340391290041801d24091411142ca054955010501700e520a95161456524030f4500c41001c0c6424807 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 263827814 1250 263826564 263826611
    0xc03031804060803030402030d080a020d14041b150507080f0d0902030d08070203160f060608030d110306030c010503092a0907050c12090420030108060f01030f030c0609050a06 77
    0xb035030546c1429030100303990346103004041041c001000300081001407150f05441514844120078483d20086450109039402b0a07601a1040e8040c105044024003c084000c0304039482c1060458110043d00c10845582e04400e8084905150400001c1d46d4801c1110103841d821030303503a100184404603841018601290030000005000d0754004201e415a0080b09031181c0c00d641044a1062006910f8040c0300740d40038400c020440c80ca41000490000c0002000d00707440104000f00300040301d0a0804482c041c0411295a54140d00202c0084003c1d4814005940c100c5004d0080366201c4580b154112130850031755031f21090050b4407000c25540c034540f906000d9000049800d01900d0300c688019907645039140d0120178401c041c000a22030703503a9141e03a400810301950714414031342e08007801414081103074428400c0701c1c2d55224001c081140ea022525496040343c0e03009000e80b40c901c960380c4c1c041c0c4a61461941c10740c0c0c40c1d036440e000c96022400620080d01003a10502c070004d0f00340000d40303c03246002c00c0d00 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 263829064 1250 263827814 263827829
    0x50c0108090f0d0f090b21100f150e031005093327010e070504050603031608041203020a0201080a0b030a02151e130504020708040909050c0303180406 66
    0x80e40e052850b40b602080720340605040d071a1003049103003821015500040e0b144e11401100310300144080c02e8400c0d400c0c06000d5080c1908004840740c860350f40810b08c4090707a025410122914807410000d9120407102c0b40065010707030911020724004603000a0078070352202512294280c45a0070805c000d403051181d10182da03070b0002598283c1c58164a20656072200d14194070301c00d0607032400b0a01d01541851020151107071450301c400c07482e80c44001e2502030081c601c2c8000ca02c0c45041e10205491606005062051802900550412103011810860602007001c00e8030150400c000100d184003220600c0b07691540a60010000f08109100040030607030020169030681d0304d804d40000240c4e40c00301d050481140c0458003890110081101d003d040e106400c24a00303d600c0920861a04402c480301800400c2c641c00d0354640301c295180c042c031069124103000203001c82c01c1000300b4820b205540e408050790502842c11030743d04149010110745550300c40c008003111521514000011490180145c40280c50b81 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 263830314 1250 263829064 263829073
    0x7050610050915060a1202040807030b0c0301060219030c080406090611070302030d0c02010323071d06071e020307030b18010209061b16060504090f0b031002090607020a03050c010809 80
    0x3c183c0c1084a07a03000e90345110b0400002e101d00c14510440c8214407982286104558681da00d00b404c0d55980c495110403282800c0c05030015880e83c802c4420b8034101d6200746c0285c10034411180c220095440c052104a0900044100e80c1012500350000b4001030982d03500c6048402e4140b2001500d181e00c8114550240e61104c0803e00041c0c0380800c44005550050a0214010050b44016070141164011400030000300c14104a2064030300301009000728400d444210028601c601800308100f404c0ca6050b404c00410807071000000c8042100380d0b041403403000b0030b03060034001e40c1c000703070030240c60340d1040c1d0358aa481360610010202000c4460040c03000305000f145081382140105010307000e000030300c0070b20b000068051950007109008142017641d1000c44a0059074a401300036240c0c2d0000e0040400b041d203401403802c1e000320148500c1008540040040001d03041402c00c1c40040c1d0b101e00c6600f41c0103401805001c005031645061400035500c98000342c034034401e40750b0005042032002880300c20300b90301 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 263831564 1250 263830314 263830321
    0xa050601030506032407091e050415030b06150c0f06010302031207020f12280605061206040b0403051606140f0708180c1302070501060501020304050612060301090503070506100509 79
    0x35107620101c00c04a1917003600ca80d120b10040d40c013000c85030320801501042e280c4036940c1a51030302400080d00d108880070061162500c100302c107100c0c0c181c00002c0c840c1c100840418520f150410403c08528502c0060310720380961048504c1c00c11540c0d0030710803020343c4440018021442d0900c19584d0b40f141400c209402c0c03101580009a0313182107000254001c225010020134030a8051182d0b80e0030303000c400641c0401e05040701e084079001d0906079007510010b1030000801c030035250081282600701d40150041405807169116140c00c8070300034100320140901040340e440e9400c01c181c81005200d0140c1350000f0703201e480150348a1102001055000d048007000204107100d504041c5458100c807525006140c4051000d000c103284c51100744072a070303003d02c403e4031030b10018107113400030210385103d8002031010315980c1c0c00590b82c9001d40e004503036200c201030006061400d002080c01c0d5210388001e0000c5806c0d4030b6901c0f2141107900c103210070303516508040b081060041010301100024901507640ea09c40d0b19 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 263832814 1250 263831564 263831593
    0x161704080a05060a0e0c01030902030f0a080a030e010501060c02060d06170a0b010e0c070f0f0537050607230706060f0f05100f02010b1e0102070602011e0c0207030602030a05060103050603 82
    0x441081a180c1419640c049c85020354800b040b507144c2c2281000300325090180300d0704021101c0d401c60041c010010382840c040750780040c0c040c00390b207048070056203c2941405081d03080040c1c80e00000c9460032035990742c1c800020254061100500c440e034030603010740f1f510246424070090303228058108200d05040d8a0601003800c1c071050403070700b2064100103002421141850500650811480d028046100b0302007000d07002e180c511b038140310300703552080300c0c2281c1d044494005440e009440009071054101e40c0c00111160701481c4070a040d02040091380c1401540c00d41c0b03a00850300405019140c80da610034040c0014084240d05601500f43e04410120301413916000410080d900d202590070070194028000c9414000d400400403468002d06a6010b00d19180c009215103d00680a50040c41002e1000030f61038018429400a549511003200b001160781a42802510600140004601c03c1410000100e01c6500c082c5005030f040504c04a40c0d814048001003e030b9038081d001c980301e0707004123a108200301c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 263834064 1250 263832814 263832823
    0x110d0215010509061504151b170903031c0534030911060d0c09090b09010312020c03100504110108060d060b0f0402070303051614161704080a05060a0e 66
    0x464003200c040d05aa9643c0c004280c0030042c00d00c044401e442c000c20040761f8032032840e03052102c142840e91044070343c03a054080b03400c5900400740050702d0001c043c1c4041880da221b01c3d0003011042c0001c0c00b143d1414030f0060480000b820341044e21081180e0302d4041c05101c0b40605103280039500030003881d91656281215280d000040400003030141540d460302c00e020826034a20f441c81c2c582c402007041e901d13150b52a100501421140802d400000c505800200d0201d101b840382c0400b4140141004650340e0a41d81c64604d20060001a0000d6214060140c0d02e01d80e4200704403041d019079600003103220305141ca0a0100716004059140c1400900f00400c061500c510420404082e00606c0102d0300070750000116a682c14810841a0464000600e16082c1601341d0050303030080d0540d0076002c2c215181c908086840300c1e440da039540d080030400c000610f484584802203400c2c41307008036400c0802001d00c481352140e59101da40461a01d801000c2c3c0001480014410140c0c0140c20303840510001da042d102c4141ca4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 263835314 1250 263834064 263834069
    0x303200a120e03070e010b190305010602071e0803070f17070f08090111070602011401080c010c12020709020d050402010e03151609051005190509031b0d0f03110d021501 74
    0xb0890640d0914007140c0e01041040002c050699410459513182e0034080042d5002919900a00f44001b104c3c201c000c0c442c0c4240750499001d60b0140031503500b0035100e155a11445240500c902c050300030003055620040c03004242086c8a421680c0d190609890405c501c50703000d00c10000080801d12075040401ca00184111ba51940b1501d40ca540b075800c4401625001c0c400030b2020200e21900b071003c520305405512115550311890f000c0003841e03a0710076541d80d485170340714003581c0024039096904002400307185281104021a0055a120b0b50f02c42c0c460804a8010544091210342c42d4000d000565800907801d400e1070340281e010380002400808a4024014050110450480e1550902c903440d849020400080c100040900e40d9915103040000c1407500041e030949440841079001c040b07171b14010000c6541805001c2c001e407c4502907a0a686800e03a500c1e144c1c0b5400a000030039041c0006c0b0481c0203c100c16200e0788a101b981301e01460b64520f0480340044080c04d551040c09000746407120180c00a04 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 263836564 1250 263835314 263835317
    0xa09020301050a181b020610090e0d03020304080d05040807021f0918090501020f040303031b0909050a0912081005040e030706051506031302010f0f080a051f0303200a12 74
    0x4103507184c1031811005048004500c1244070740040c400074034030380c0070550038000c102088121003916121600801160380113030002c44164010304060221601940103140c0c003d002d00291410444490805410f0b100126403c03160f9190000709070b0110300e4111107410a19a0340442802140002600a00007460500860b045040808545110040940c000003021b50b44035009640716150120004040e4103c0e001c1100464142400081d001000040b404c941e0181680d03035020452520241c1c400400000d0704070740400751600100e0300415002d42e01c83c0709000b035a549440d04c52400142c4241101682d40000340b0943c1030207460640203c002064910094001e40006812788130542e81001022807124200c0c3c1104000c0200f10f00c1d02e15507007036030b20310300e0003a01c601000300400c400480f090b61425404902040201c40880c000a076140c2c089980070804440354501a4601104c8015589850340201c001800b01d035100340c1c1840381c9002d5030b180d604445008107007018080d540c40710800d021400c07260 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 263837814 1250 263836564 263836589
    0x80402120c04231803030f061c0503030403021011070602180919060e040206040306090c03143906030a090b0a05041407061d010903050d0e0a09020301050a 68
    0xd1903060a02514800d41e1000300308000941a031842c000f85042c3c1e1000c031051003c0711000251004110709048801420700c00b001d5451642c40c07044200305c00102070001a008002c00d8090740d25038828450640c070842c0180020b548074174061a0003850710101d0040310100380c6c240201030055030b20500590300010761202d00962110000c1d030010100b0045c40c0ca0b4203a0004098007400640200207900c102c1208407860240010798a4440388204d0302026a0300075000359042008002040007680b1902039944124054072200c2e541c0c0c0c0711501c40f000428500c2e40690000348c5440c0c8801d02000c0c0f05002c10008070048500700d9140303403001000c0d0b40c1100b00e15005400c000009178400045038480e40165038020b0304000c0c1d42c14100c00c03060041004413011181c20041e10100d10ba50100051540100c0e00c0c03550700d090001c41d00008544500841c140201e0512074140d50101c00600d0502c41e0303043e051001c0c0d07200900c52031031400b00b000052035036003c820880d2041006010340d485116000c0203456042c000d07007 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 263839064 1250 263837814 263837839
    0x40e120c010b10030b090a021e090409020d030906020f06010312030c02070f032009060a1503090b1501080105100503010605070f060903080a0b040e0c0906010e150306010210020a080402 81
    0x490150110040d400c3d480200d079142120700716016400b460640d075007a150a40f1541e90111890220f116030301812030680d185019a01018114100030840c181d400b0b81302040711015a408180000507000d0f04601080d10b850040c800c3c20340c100100302d0402e42c140d0003060350354590344035071024010b030304842d6040544031580d450b02c243c001c00c1080000c046245070071180a6407401c03c0f420392030410044030703620401010030138a039280000c505805410000e000140551900404140c8907103007007040b81c1416210b40040d40480c251621262080c01c0300030504412070307030190006200001c140c00c840e12561000281c00b001036480010f0b41d0659540d400c0041e40c42c00701d400c01c04890032110b00e00a1600c0d0401510700b0400d54040c0301c960041c2d500303140602070341c6003460800040d81ca544071005015440320002d0702040c9070134004a03400c04410304148110b8020380b800708541024600302011500ba00009003c130a5a04001890040c14454001c505106007104014103007040076201a1003541071100c0d6 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 263840314 1250 263839064 263839087
    0xc270311040f0b0d050706091212031a06040305060604050a09030215100b0c150a110a0309080408120406080703050121240e010b090112080310080105150f040e12 71
    0x80f2800d001c001c000d401240300303600d40965100d1640c040e501c00120031800009082000102c003d03040303907116107481010b2141d41c2e1308400401c45a010100920700036200600ca540f0350000410145000d04054030b0780c4c3c6000020311041e108054511001a4604800703100842d5011800f00b59001daa000103988a880703146070305d1065400c80d00205105040000d83e03002c45400002c89d00d218000040c14080c481d03032080052400c8460000c001c400c00c800130030845100611130f611a00803184501c0b50103091640b00d0010a240005040020700300440c006404d0048039049003c1d145c0c000d050746020b0005605002101d600b013061029500090304400c0400020421851940000c48031014980fa100c252408044400750400c8400b001055180c00310804e0309040c5091042c1c144c426a100c461242851581d985405e035000404200400706403100200307801100303008041c0141c1280020908104001c000c01004032100d42d2800c1c4590b10780746130381d40400008218010003516000c2c2140c1c4031100c8154 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 263841564 1250 263840314 263840321
    0x303010620030d110c19021e0a0f0306091e050706050d0207120e100c0b0c03070212030a05150d0c051302040905090609160b0315040905010c270311040f 67
    0x504103d0604222003400103801d600040e1811915440440c5c0081c9070903100c1c00d0081c0b4440034043d4020301c0c5030303040070313850b400c0300f01c4000c0c4255020300950031641c0d995000c0540600b140d0000c50308592100c1a030414056215841c0d6000000003100290248030b07907032003a03907500300c81c400d103000d204000c240c20005401c503605452072190400b002c0e8010760b070f44d40002040440b078051801c1c410030940d40e500408a10400c1d180340341d00e910507284c000544804c004156990001000700c81140724480c55800000c032514080d602070035000c83c2c04612824142941400d060100345400d01610041d94000e010031a1401d07030800310744080c0d601031024510224900c0203880b0365045003203140c0c248010b11140d1100024207a104042050035200d0300420100c4441e20800345100341c901c28141400070902c902c61f001030010f041c000003040001da56a0300e50300c00c4c0c2928500b000000202e0032810032036448000001e91082d0b4004505112a141400c5035550204801101c0c2068000c40d03070b174481c5c01e10444d00d40c3d0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 263842814 1250 263841564 263841577
    0x40f050d0f06180b1602060a181203050108071715061212030a1505152113121107030618021f030b09010f0603020c0c040c05040602010608030301062003 67
    0x110034090003c52207442524608805021100c00100d500012000c80c481c1104000301507107607014141ca80c480102182c09445401808502c0b40301c180c08490000e02121012031b107003080d0751408107031903150003180c0b1f04100095005021820001ca50440c0c0540d0102d2003c581551000120ba456121040810308590321400110b48a1051401110361503100c00702443c840d41c905107090000380d20805c8000002c403103500c82c440d0011710140302822520060f0001d8441000100c88000250b01e01c040009a0100155200c654040c041c0310440c042c0a00c08640343c03c5203170a0b041080b4122220104c035070f6108094480600741c00d0790380c00310204030402040d40c0c00711107800901110300640c3c0c039203601c0384180d244013481c000310f0714005400902c2d0030700b01d564504803458100e0202c803003032500100f41c0180d801043c00d407405010300b004010341030780e45110358100748810f41c0e183c6d9140e5050100285c2110790b00d820182e030030390090004001d504d80c4010310300049441e5007440c881078104085600d185002d5407 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 263844064 1250 263842814 263842823
    0x608010b1b100e03090a14090112080909042102060c04061413060206010e0a05090a030318171b01050f010b1b120315010507050a030f170f0114010203040f050d0f 71
    0x704003409030103800070244c609560111500780500781e5400440b07c1901c1da60b508541c20103110030040200d20010941e942c151400703500d00602d070218500002e02142000c03035003200c003020080311004105034501b0b80e81c101d0306d0441c002050641030005842040b40164407030401006040745001d0401041a02900c09079080c40300c00740020794451601035200c041c240100280f070f10011001500e181110302031395000b05e000d000909078403d00b9442c21005045115508441c80c845c2c2c138448000180c1c0c2c9412100d0703000c160015641c50f4a540d548000644c0d4689100791260780c1080c081c00304643d00e8440e83c03411620100b02295441c1c404007542c0041c182d012014400a02840d007031900604010b8000b50b104095140c0c00500600030700340151141d0240710030160003035001f0b003851070011380281801c0d82c009185090240b2544044184250f4419007120140c281014800040003950f5060403040401d039024009035042c03908101d010b6400b403005101e007600c41c41500a16209102c4103040001806412 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 263845314 1250 263844064 263844071
    0x1d0f04060b191403010e0a080409050403051209010c0f18120f0b010b07020f010f300f02180a0501050304060507090e0406090512030c0706050603120307020d0206010608010b1b10 78
    0x1c0f03007140f03540b900003a50074a009500b0581c418030b0810300803e070101190340c024201d0b4203050801c40c2000050400a000300c041c4082001190100f11052412074403034800e240000c0354050511600900c484400e89903513007808075860810b11241184a040d00a41d4600c0010032202400d905100000e010821700c0600404407180011402c440f096004001341ca00036070380300c407401e0021401151080031083d000c80000d0303c2d9010307079802c1c1000d203031a81c00d855103104491485228003600c5003040380e00c0c01c0014291658000f40380010718903861044810400b0844a600d0390710b1501c4006021444000c00040c0042d42c0c0308001641e0500139420400038007106000c3c10042d00c0e05147c410000c00b2540300a652074440e800103945644507900481c0e02c08c0a081c1c501b60300b00358075582c0322006004040c00e841e03450f000e0f48142136402100000510710540c240c1d030040070308c2c96152101034103043c410f80000781004104801440900d040c9130403665100c00c500780b46080842038401081c1004014002d42c082a0b05 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 263846564 1250 263845314 263845319
    0x3030b030102190c1103120306010e2103120a05060108010b030c12010e0105011d130e0f0a1a010819150b0a0b0c0c0102030313060c0c0f08041d0f04060b19 68
    0x500404c024600c83c8100c0a0766409505002050b80d00d141582c05031050304070400c0054250752141c92400c1011101130328600c6c011019010345130320221685030484042c0e0001c11856004880320b000d00b500003181c074000300024204a0b0000304000014000c02940d9135001000c54050b40e0038901320740e5100340394000c000300ca50312010392400c881d6007171103042e0000d161103a02c0460380441c40340c00d14828030014808488211015100300283c02203c03994100d07402101c684241c009000d0001403185d503c10072060501c0d00d00401c01c0c05003654103800c00011075001c8400309103000744410b601080c498100313441c9600f40d801c035040940544440d1400a400403103a071000200c1620354005008042e00e018151005489000c004a90302e020460b4405a08085980c20b10045526035218804a8500d07141000d000301440c0c41d41260b8850420044460b040300280030050f601039044060008171480c440881d480c2803a100c1583c250f60083c001510159031503e2081e4150b032001c210403141440008159003079076 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 263847814 1250 263846564 263846567
    0x408030d0506090c12010e0603012007050f1506040f1d16080f070b130e0903040806070306121407270b01020604030c081c060915060e03030703030b03010219 69
    0x7060703490394050a07001003c00c404400301025600304182003e003414041c0e00c2e04048101454000c0c2c230440d059580c4000040b441c00c460441500e00310540080541e42d0080c51a2040c508602c14803185da194001e800c101c0c00150340d035541746401c0402280c0100320042000f00c0701004004105e22654002d9900d03078500182ca10109100c0101207101c061040c240c0c0e030b21006076840e40ca4844802c4402c0d08014000d000c20807003203000d030003440350040402d81c40580380c510721000110260750700e9804e03510200342000104001c0000d02c4d4040c40610302404110324107104440c108071004001401074042e0307209026190000c2020070000c0510701c003131011041001084120f2405802d41c0d16101c0e5041900345500703940005006402507915984007800101c003501c2c2c91149400c1f0b410f2010607009881629840030741103000b001c0142c03040c0d060000703a484008182810400d0207501c18014040d6040300c083c1360303540100685605940504000c687e0254070800640280b2854040500c8030600207001074030309 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 263848920 1106 263847814 263847821
    0xb0f030415090f06050c0414210709090b060f010f0c061b050307020c01020a0c05040b060f07080a020607020105090a0f080c0f0102030a0b0604051003050c0408030d 72
    0x240540784020241c545001040c0c03040d1800b120701200f4440144107860b0040f140f00845481c3c2481c100101a060000c040e0051250344200550b003401000701400005120303010301550390290f00c50f500d800040c55600819103051440d0400107202c0d04050f4902450400c058640350b58101c01d110b0222800080c005003114030b43e4482d28a5108003004240104003060140c48185d124030302103200038941040d40c00c3e4141158060304022021036202c802c00420384e0300075200030456500b450041240c1d44a041020002c007603001030804140030002001d441c00c1c203941da003038841c591a080422402e0b01c5042e214414250448004000001c3d44000060102d910030070906003800740c5e00c424a400c03c1c0030400d144500b6500041084201044c43c413400c858880d0440b4010704007400c11f030100360071082070109103092540d07427008101105001010340b002064100c0c21260743c0e0709080c4854014 = true := by decide +kernel

theorem cover : BRFrame.Cov 263669064 263848920 := by
  have h0 := BRFrame.cov_init 263669064
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 263669064 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 263669064 ≤ n) (h2 : n < 263848920) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
