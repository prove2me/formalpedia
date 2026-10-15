-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3897
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:59:49.432534+00:00
-- url     : https://prove2.me/submissions/3774a17b-abd7-4b96-923c-d116a93c7fa6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 700719424 ≤ n < 700899280 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 700720674 1250 700719424 700719427
    0xc01020c0303010806160507030509010e0a15121104230901090614090108030906091f0309170a02120c0f070806090d020c09070c020303071205071a160806040b15 71
    0x1000103a914110b40201222100080030303031b8000c40d6540190640302c0165050420648501c444c50040380d0b0305182003280c69000d14884400a500c0705040705094001c8100e80c2d4400c103245601000500b90707030700c100c50913072015010401080015103080744480540109144c84070045042000105416000c2c0c02c8002c00070740e520070400c01d030f068a40c039003100c503e02511040f66540c5860f0203e9181d0140002d10303070040e0f000140d00800d0741d86108007442001c0d01121607001c11442190018010039103e4011507580c4c0c079041114041000301c5050b980d800c10300307a004107032041e83d00c4a224901c4d00070701c1c058201842200c0a010480b80c060003414003900c5640000c0003107144c90310f4902c0c03400440c20412000c0d504421510a900c1d11102040b80e408125810520701a00c8a40302003440c42c452305002814130112200610703401e0fa407290092031054003d01000010141121040688142c10fa82100c00062003801000000d8001e40c940ca520443c01000091a256000d010030351280c10043c0c0049100c50 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 700721924 1250 700720674 700720679
    0x105030a0219094206110312090f07060c0b0402010302090d020324220b040807050f1b01080f240303072d031704061d0115080610031103030c01020c030301 68
    0xa0007608000d21603040204c28080c816484804130406060303009110421080e0507040104100400443e01c8003000d110b00c0746042d10f00b283c8816120448640d512826014410000600c1407207603001c000310a0308801c10740300d03a0b20346500540c020b60108000d5a003148070021660b0244c5d409110270114484900c2c002c000c035810b070340d0340c42469070300051441d070a03040d0000c00103520340c500c0102c090307100d40d201b003c5404070748035414210b0345401100310061007842002c105500350307880402c400c0f8255000030207940010701020b0064500c00c3c01190074445002c604400104642d5031508104020703800403d80e04540c02c168400b0038295801044169007601003114448409843c3c504981e6003d00c10f9503a2402c41ca8035554010610144100050700c100b45031408a424410617910000c035010b1462103582c0c5449410300a18080c0008003860007a10040303d100250001010845074443c850100740102002e00755550404000d140384007140c0c141c4014042020342e030a0910040544c004081e004689035031 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 700723174 1250 700721924 700721981
    0xc090601030213090509100c110f0102040e0c0d0f060b1b010228052a010f060f05010507140307030c0c0b0702030c100c05100501090f02030105030a021909 68
    0x1404140c1014410090800280d0505043d2829200344040110305910b807650060b1814070f400c030001d00040c1c40d000d01079141c06c0d000001d40100e04403500076240300c140550304036401c0380035074400e00c01c00c0d008034000540d40300d218500404003110b5174980064100d01502001c003ca42c10b03500810462000041c00345444600c0024039103840880c80c1c001d41c03070800040c03103002c0d0702c3c0402441c0100c581391030282c4c0701081e4010070a4401e03110000e0b8075004400101c107404075a0903401c420149041d4602546030301244894001c00c815508400132102c0c0c07680c64a001141c6681c00003609807000c1c0400222420303083c4041c002041c05500a41c0d0741e40d6a240141010744096515501c01901c0180c104011801030710081001d20f598101150024042c0c2411201a00c0c1001038410081603405078100600c0341c4002d590010303040c2d8070054001c00411000d0201141240300a0240070b6269001420040061800781d50400b1030428408460310780c0f40d90342c420304098418490744850161360290001c0e8418 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 700724424 1250 700723174 700723189
    0x630040506071b0c050f1210050a05060402190513080f010c0e010809060106540803070807060b09151914130618090c060806010503070305090a0f050c 66
    0x54030341120701520700410303a80c5541c0c8905600c030b068015a05034162107103a540e80c0540c031b25262042400c0e10300841c23088981c60014201110400d060510344000b20355030b03041903c2950b048030840558808140003012054509400c5000704401c0c0e051b03400004101c00b28180241d0201c59040400800e2000e0101c030068581105c03808185d0400c07841b10104440c3c4500095207a0450b095400e11a00d1401051400800310701c1303090315100420803101c1d0700030101018070304203d03010120814403031002c032848083c09030710101c6110b0a14981d00a1160710f02103010007004007002c42c801e890002e0401110804203400c208c044503180d800c240803601b61002420800c0c0d2900000d690703c1c00202030b03103050184842d80c0f114000a614010b0400740c10700d503c54100c41d4440000340a0405009840c0c0c800207414101608142200b22001d0700c038070000181050086400034000c410507101d560440da1404801c4005240040c203003522882001d001030086070145c0c0e1082c418902640c0a070070082c99502c140b1000 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 700725674 1250 700724424 700724447
    0x1a070201051909030c0614040c05040606020c1c0b040c08010e1218041113050a09020901050a0c03020109020904030906080f0412030c02010605090f04050615063004050607 75
    0xa5905000c100b041140007108520000e0402030000180140355003011151202440401000d142c504038408031544a044400b620039803149180f8140b0b19115428003040e1030080c4100c8001d6030100c480110305140c50000341c0c5111004000203240a800f60f192007110074001d59080c2c90b100017480c02809100c41c280900100c0301c03c10350050080d000c01c05004121031062059041030114418001c0e2855603e9401280416058442e010b48803071940304045400c05541c461580b140300c41d00d4001031610030718000d585c4100e034161521811b003c140e2070140d81e00341100504404556984140e0030060f03440c004e103613001b02d000350b58aca60614248500a000701d50081e003035541c1c2c01d103410100320010300c004440c0600c90302c0078076000c42e00d283c051109a01500d0641c0100764082086001c2000841100101c0761282e80110101c0300c041e103030300c1200740401c103402000790342040e400c001c3c1e01110701d010351141d07660780c084a4070004100c1c61141004d81a90703040e83d00329845e801480611520640c03103110a1103 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 700726924 1250 700725674 700725677
    0x1803050a0215100608040201030e16180e19080d0501030303020901030608060906011502150c130e0708060409020604090e0f1e250317030a0c030207050628091a07 71
    0xa02d402c0004a0b2030740390100b03101e024104000380b40001c00b1a4071035080714202e00d0040045850042c9800b000117a00f244a00864452400800342c6404205080c02104c40c03028140000e004010042c40700c54410041c02801603540010801c0309114080d194828a80214025a0016125940040018240c40710b59100d068075038080801c0c8440d00c180031a015045442054203c0301c551000a4183e04144201101902000c80c4030200030200e04000010120301c00d1404260007415180d060311a8254000d9640c2000940380400042c1e0300d041950052030030500041102d42816640d05100d001c1d1a005050f094143e008641410030f082c0c020850040c170b005000101821080f2841122075940300602c551035072410003150b9000d04d41001814000180d50800c04200e59501c804c01505180d40c0b007924801442840c0040c1c03041e0881c800e00c217440b91180e20101030407170741d103580c090351b000c007107030a811132540800c1244468803111552084980c2c1c54841e80c040c50350076079051440e14910600030807060 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 700728174 1250 700726924 700726963
    0x3090a0b04150b060906120603010b10080618010f030312020d2f042111060f031005010318020f0a0e15010e060307020a020d0507031709030607020a02060d0f1803050a02 74
    0x200740740e941c02d050320500e07c10040b00c4000d5035140800a0b000d441d00115054005046583c0160b003941d000704540d01c00c00e41600c610034142c444a400e10050b01017441851408145608140000f0740b040780700d4850034980403030160402c01402040e5003200c034440f4000041030102c07903031002c02a4007a216964052082e5640500781890b000e021f1070510002d800400e03038400300e200d070182084000d142e002c20100d000b82441d0f032241c810032022166035000303464400c21002681c1000400e9842805035240c81d00003400040d584174600d030b092091100c01d048ca039039802409150301090b98103100c1c040a125544c50405940365850304000501011070200e0a240100020403c102c903250300090b880d1310700383d810742e40105040003d05000381802c0032608002c2800e010300c3d15190118210202601512004509464440d19071040a0340c0d14059a074000350090b0f0103009542c1720310810350001d035444240b100e01203440c40e4042c0e02100c0200700302c20101c001c04d40200c0c60702100c960407c00c901013070310001d5194 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 700729424 1250 700728174 700728187
    0xa0519020f030901030f1d0a02011b02062a060a1b030218090c0c0f06040209090c031c02070503010609021317030f030c0f1812030708040b03090a0b04150b06 69
    0x40d516440368003c1e6505060720b5088058429000c0d501040c00d170303060038064021500b4100512a04c1e03601009003a400515100740c41070103030800c40c405204065004141030305c1e12010401c40c1c0150010112080c42e66a040c004c03200403e0390030b1010394400e00d868a030028081c00c40d1600c5803030041d401c422a40802d407050100030310200c036101280c401c40c141291180758680d03501d036407500d5904c51480c007541240035458000e06d20b10000509a80994821210280030b60380355010036945034811034015030305030302102483c150201c0040c400c02500c0e0040c419038003050b403240c3c007007404e45c1e0740c5a0104d040b45a00041440710007010b0400c50b000380c2180f00a0390351003055030902c0b59890241c2d6400640a54000000c5403000990400712480ba400102c5c003d40c0764030009000c1075103010b90400d2a80a840416124074403079030048100d41c000c030b0340858a54102400e00b402c1e0a00c0342c00c024521003003031080d1542d0902082240c50400d100e40e21444a0384000d18031030a03180305076801d14141501503942808203 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 700730674 1250 700729424 700729453
    0x61906080a020f130306020c2e09020a05060f030114010309020a23040f050901050a0b0a03110f060c030c010606170c0702010923030c1008060d030309080a051902 71
    0xda80d00005420805625032003600c407100d2803403203201a00d901c40203811000204015058026000207110f0205448030100b50f24038007188540c202c0c0c0d003545d4042000c002070b010000c0036030040407000d00240401000b1501c580105030b072680882c0ba174901e2128044010401313144a81c240c00c50041c428a0240440c600070342c080f9040440c903016211020072945048643c3c00c10000741d001c00888000e000b032060003501070340b1074020711094030040c4d465400c080010303000c220180a80340c20058054907040119117103403915080202000006603209001680301940c0750b8030a4044d0950700c4400001d0741c0c1d1440800361240c2101d140c2c0c2c1c000030034803481d0440e45c151400310007242c41e071020744c0601581e0703181d030036100480d4050301a8010392519a044550a0320055641c20101000c0c8070903022510502c40d01410011280315950040001030b00c241c002942d14240b500010302c3c4140309040c00b00340a2103e9480640c540c200340c0182c1e000500120360054a071038031204000400189001814889120703000c0d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 700731924 1250 700730674 700730687
    0xf01050a14061003020c160303030b01080105011b060b031c17010e04140c1009090f0504170c030d090b04021507050c09070909060902031e160c020a0914061906 70
    0x50303d200d404102c0781500355a00a404548210f840007050303540003c2101286074a801d02e03400164002840e16602000c10350044541d18142c420503169001320240005030502000381d8004102d41c0d8645520140f0b0f40c80e141000482e90074520145007030440c1d103288100030000d04501400c0ea60f1944203200400106441d620002d401c01d800294401020802000741450440310040c42504401c02c0d18000c0c24580e80501c45000b51110b1100510030108440c2403030099440958000e0a00744a501d64200c1560403000200003181040060b02c0c20800300a80c1c0b0300c00c458402e4000c0e41c0d20032445041100b1403505103a61440145280203860070002a525a2a07076207620203103030341c020400d003000b04a03014007420159008ac09854828400c1c5034803120711034069001070314400c080750210076051041c0400035510a00ca04413000c501586002500004c486404180d00d0585e0420315000020941400768011004404100d5900c5000d81c10a607082c00402c4140302d14404440719070003018011140d0065 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 700733174 1250 700731924 700731931
    0x1a031f0c0914042016031e140a0323070f110c010f02100617070f050102062409160806042007020307150c0606290c0a0203030c0f01050a14 61
    0x200c3c00076a03444039210032254142d6060001c0740d10030b004030702100d2443c404c80b00d0f4450703c0d210380d40e022140c404007100d90082c0c4240d070010401052070340c1e1604103401c1002000e00b221292600d40490700b4016903441c81c0914560201a49858010200b00409907070800e50030700c1d2450301c0749040c024841d0101070003601e03140850112810000400705074074055100300034201100c00b08100400280b80c0d2140e03c001e038409120050f407514090140001050208242414116001038018150340da8a2800540c00c0e280c0d005a100c0e005461181c61690700e4540c2642270b031040203d0360f001004801e20b040003038162007000303200c24400c50030082c0c40b00d0003003800e6042d021707641000f80c01c02c2e0700c898007840000e08140007038001e169840e40818000c610681d0081c640c2d41810f004800400c2210f4170303035002c000c05250303654452490002c50041000c50081d50740040c0040c9400000365034044585600003800e541c40103024071000c1d80302c1171050031307904020f106054002c4260102000355070514140810070b00c0e8000c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 700734424 1250 700733174 700733179
    0x3060402070213020307030c0e18190f0911031905100e0c09040515070c0b1305150c0912010b0a050907170103030c0c06020615041a031f0c0914 63
    0x1140141c2191640410301d8030104001105546a2410203802001000d00d40d0000d0002010000e0144540c2884681024400301d010008481c43c0d483c0030001c2c100403000c4d040d6501d1070f82d64204580354507410b0720480320000d101e0300b100c4031441d0b04501014645100c12100510150110300a6400200002040da0308403071001070200b840e00c0b485103d142060200c08100782c101a40900f0081001b4005c652420a00000303a069006a11000d000319543d0051400081504110700c0101c0c01c41d014090386402a60b21038411030300c8028003502c481d4043c41d000d60b040c02000301c02061258040c9041c01c04c140354265080d000300034800401c0d0001c0c890f8241813040e14040c0d860800400c3c0c80310301c030301d084c0b0070000045002c405255a481c0b4008120ba0f000c141c0a03a0310b64040c40c2e000c25110b20108200b40601e0a00c9001c0c40a0001d44040000a00205510248145000d01d032402c854038280020340740100040b807000c1202040b0a11101583c00c651007141c00c000028900b4802c0081c030440f4080d01403000e = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 700735674 1250 700734424 700734427
    0x16050910030b0a02090604180e0d0c0f020d120314060f0102030712051b060103021e01021f021308030409060906120308061518010f08011206050c1b07031b0b03060402 73
    0x5583c41c8100a100e82c900307284d045000040c001c54026400c0700c1124030b04036210342c2044117030341100321651135048095a0b04001121042400302081490000010050004001d0390707441c0051343d501d5800303200b00c83e40c0c280442d440b181404144040300c1840c5a00401c01e8400d52101c0c10300500003900c0c0c2c400c0380c000500840040555141075489041681d40c2c24400030b00c01c543c1c40120514144d500c0381c00b4030049115140e1103080c8600ca041100c0d403c89090810303001030101c000d06ca000a03500340d20b420000b0040550a0241149400d403a241c100c00511003000a0740c0e540703040000a800b40c490741e030452051582486810015000025001403103a500b501e0603e000341c07903a000141c0062103903210b01c51031500110307090020000c50700b55441d0f60a0240c0b0ba00060070b90125091781e000d5400d1050380c511008220203c80843c41541100750b026800c400b00d03902e03101100400200d40d0822a481104503800900c00340100050200c041c00e1807104940c0002005182c004101d100307100081006d0b0007145c0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 700736924 1250 700735674 700735681
    0x70b0601090b2d0c0d1d1912030e1f020f0703030e06030714040b04050924120a02120f0d02010b060d0c0c050a140c011e03200403030216050910030b 65
    0x100300d425104910b441c44241c1d65441c1020b0f2001b800c0c04141345800c00d19400281075400380c1d280c5024000d070851700001220301a246040c481144402411000b9814090400995480e50b6951415400002d840e000ca80c036081c400c1240091810200e2643c96080d0303804031600f8000700c0d401c04101c884681c2c048030101c5da60b9840070380c1102d83d2030000415180c0148041404510301c0c4204020b40183c840030b8600940030b6403006c5070300075030383d10720315414040c8010811610b02c64280200d4050140f80d03107004868080c055903000c04c00700010881c00620300d4100380b4140c1c401110900c602035118480d48024002c081d50500054086d20490030703051003455032900c0000071a0f01502c021440300d42c000c42515a403950906004503501400e0b9080c0b0050b00075000060100c0d805114440301a8025401d406041c4c421074409500810040c20340b54910345865034100542c04070500148040d600c0f9a000d0f0000c00c844000c0010112096040f8600c41c0091804200b0b102034100d1350700e03044940060b191000c544 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 700738174 1250 700736924 700737007
    0xc060a0c0c060608030316020c010e01140403080c03030403020105060307030c050f010c0b0f060109050d08040308031f060201090c09060b0306041a03102a05030414010f02070b0601090b 81
    0x70345084008001608055000480b800048099403241051489030105d500354100102d80300c0300e40420050205400b1500c2c82c945520986100c100541c02c1010180713400d4503904e8542c0d65800c500164003803680700108100800d98280a11908840c080e802041d040f41580c0d10007102001600925000d20003c1c484a201c603841b40c0b151121013a040501c04089052015038111040740440e071b01404100040e0700000c043c2850045008215002500e9508150a503540c0903440c2d400544200802d660b4060388030b40c401d43c4040c0300001000130350000240941d140c03600918140725688108001d40c03414204102c01e864000c12070b03512100460380065040c22109000b000b10301c0700009140c140c40360b02c0721030039000550b922240400c0d40030f5a02184c00090455020450385140d40000005901031012600181c145000e01320310300022800400c02c10418110f82c0d0032030b00042000c0c0c0f000c250210500201d940c00c81c44020241c030480d031400d8642094541c0842060214464036800c3d00e665000210249 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 700739424 1250 700738174 700738187
    0x60708090a02100f02071703120a061523090a050d060608070b0406170112080a0e030a0305120f240d0c0e010618141315030b0106090503030c060a0c 65
    0x20780d402040f600c0c100c440610028408000d41c4080b0300503100707140010800b0395503040c3d107683c1828207200441c03409034507254000340243c01802081c1495103500000c610b84074141c920f900704282691b110651010072425000410701c0601c0755900c0d00b20200240d110307580300c0345a41c40070348509035141c81d01e219251810314020720090340401d81900402e4408a070800b601c1005100b2a0780640c0d03044031210200040d400d0303050081c070480c84c1890348840c94100081c9014046d2020208900303001440040d107902017424070b4001c40c070807000540e00040d42010705940c1460b5980113414101c80501519006244085070012001140c0d038030401c44030b200c203e0750799a0504000a0750b102d0302c590f52290f95112400300b000428025640451b210a0f2498280600303110a08100e941d018034402e000d48041d0248801840103020a0a00646540700f0a1000c940070300044003c51160700c92080710b61400ae00200700302060b4024610a070410460002860800941e40c0d40200801c40e0016105000000a07100f1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 700740674 1250 700739424 700739443
    0x100305151503100203150319120513090501034206030c170d140a03150e040f020907020a17090f0306130309050d211112072306070809 59
    0x41c418540740303000c3d01216401841c09648581414a8100e4140741016103c0400020405018140152050109541c2003e10b5928101c0703080c028540000184901344002c03044e0081050940c403640100b04000311201d0b14103445500b00c001441e0302440042c1450000c806c0401c441803049100f000e001c0e00d80b900e520010003140c0c000321020b14142d0354202c0c4154401d02c0380c0300e900c25008d0700040b903000c140035088810a141140900b140381841c800c005400402c1d200500c410302c241950404540009140009401f490003542403c02d98505441003104543d0000c0c5404115003003440d26900150345041c2d4005050801c03c01113803184120008034008012140140c0d44c03602c44e41043c0100703001c515450320000c601075540c80c81000e4030b80d0188880c1d042d075203030b00a04003040103482a41c4003601d0300308006913403041d1070418512a1800300d4280b80a481c6900744402d4040082c00408000411000c000000001079180d0000c0c99007200203512044d0042540061041440001b400d800040c4005c010 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 700741924 1250 700740674 700740679
    0x100b090d0201051b011a0a0b030c0a0e100509040e031c090614040f1101031a010834020f0f031606180605010e060d02030d03090f05061e1003051515 65
    0x2814040607401340d02034040240780c440342d541d4054000420307083c031030002001d4800324051103195031076007240400d09500200101c0108a104400882c440c1d0b5800440d00b4060303515510252140c00d41c90400046503c2800300c0d0700c00d507104000010503403404120700042c400b0503050005149256003010780c0a4032900021006035554076082208005188003c0420140540d84a030000003580f030040d4111101c21050429003000d102c090136082d8844d0000c00e84c070150343c0300f6010f0903a0a10344041407070880c00502c0f40020440510103040643e041000420902d000c0b0010700c203981c11a40e003e600ca1042d100300140581100384510144043c179080f00300b8040d481a06865403070080d0400343d000b06000c2c007501a0501851003c0303012443d00300d036840c03000f940050280006000401c0d00360010a5004c00c12100740000c5c008482c041001400b60313a100d40ca03a09505001c0c014101e01c0e02e94104001003126044282e002e10620200d9000147c0907e5081d040859600d651144401e80c4d80341000a04a6603 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 700743174 1250 700741924 700741957
    0x8061f020319090303110102070b15040e0f011a0103140f04050f06040c0e01060203030609370902040e070803040308090109080d020c09282c070e100b090d020105 71
    0x6005903c5828007040b02d000b41d5403500004150001c1d1402d030310610201620400c1d000300030a104032481140d8011421008100048101c1100340c0c690400c1c010083c401241d0b5510b02e4158000814605040d2410000340f0f000c2281e52541c6811041c041800782081004a00601c001810401c0c10460243c01d1010308080b5203031841c092808071f5041100c0d002e1106a29000000050100d000200340c81c044d440c0100000745543e503038010b80c424030052064100c8868036503902d09141c80601454503c68240004010036054270038010701080d200b0ac800c5150080d8002c0208010103800442078406496000b0100c0381d03240b101100403940c01000342c0003e00340c3d0188400c4c82d14001e800140c0e03048070b03101c1a11f811001cbe40d505038100107150a00350250818580c140078032040000c40d035000031034000607850341d882010030303002c0310045000d000b040581039a031103031100b4448540300c00703141380d40f00d0807103100001c90608261400e4064040c0707001890244080e440640e04584c00380c0d003074440b4003c1510356038 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 700744424 1250 700743174 700743217
    0x807021203040f091103070f0e270610051c060312030c0314011a0f04120f1e082d030907090b0411040303050d14100e0708061f0203 58
    0x36840360b001c0c0c030a000350810031080002c2c01001c0b90140c02288040d00701401c1c00c50b559103100741c40c1e131508503006e48100000c0d0000b04003140d80e815015a1071550314000d038646803910301c10002c070544014280a1040400d00031901c0c4450f8890115203914201c124440030684140b0100b01c090a06c60300001c01140340782d40011001d0341d055118400c0014039560034020b000c0340180c1c514800c0028040c203040009141030209405d01e024008003c010701c0c1d1241e591410ba551514200070300f032104402c66480c07031010840000c1c441c03000e1490316100040c1821400d007105503600c54040b0300c5040013a41c5034501070042092074043c244940702c1e000100510070b0355685042143c55480310f08a005480c6090700e441c041d1001d03400d05105504964442040003071809003551016a0642c002a810740180d60b214812003000f501c0c000586405050724602c00c41d006030904030105000030006004800b00f0038544204102c2e56a0348850040500380521034846e51040d100e012070441c401c40d031090b04912014200d0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 700745674 1250 700744424 700744459
    0x7050703061415010801090911030d050726120c0c0f0106051002070b040e06060d020a0203030109050703200309150f1008060103110609040608060f010f050f011b080702 74
    0x740ca0b4000c40001c50181d5a54070080c0540381d801419280028000b80c0140505c0a10f50b01c54905c85000d10a0401021024400139280291081d1a0000100003051070020010303100d4044580b5102e607c080740c242481e0400b240f0303079400b400c07202e990045d414002107000c0c0b2a10404449801c0611400da40000d811000b00d103000c1c091500c2880c3c0612013aa542c004468070100e00d0034151000040710a203454544140d101d0142c8000d0282a40004104030820640120344000e0440f40005c0d005542c0f0381d0f240c08229030071110000d040d14245030030410108071050310440000701030350840800d50f4403601d68003034180c41c054404038110340103031140f024091000c0022444a2045c0c52608a90110607120840a61103040a100080810100d40c83c400094034200c00076140c0040301034000540b0a07664040e240c500740080d100300c1811441a40180600711034100070790090a0144c0b01404e0850600300003d140e0042c0303c0d0390021594041240c2420002a20f0441e10720a40040100d240885034010 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 700746924 1250 700745674 700745681
    0x150a031505010f1209020111160906140d06050403020c042405030c010915170a0e0f010213090207060603061112090703120804050114010b07050c0d02030606150705070306 75
    0xc6490400454050010700c039031290b03071107158210083d950340d1a1031404041c0f440283c45803107401c80c14051141030700e10710311400b0030082e03100001c004130350406903140c06c031103004943c07158002021821a00e200b066260312040c005245d84c6034007440000b02940c1d1400c041f4145505c40d041183d0060034070350201890703c0740c00303524a24100381140c9800c40968030004c15541d54012008540480c50350030040080200c0d12100c0019404c07603003400d4141c50a04c881d00c00021600700d034242706080c0c3e1410b20720007040e4100000040e8580080003103182001c10540c04910044a202e941c28143d0002681410000181c00110055170301100c1400b4543d141c0d000508950070802a84c210640d400000481c4800009540011640c010040c1d110400c0c15280403589420005c0050722550b403110160030300900a00030050080c2040c400c80c54944406103880f50600c0030500321240f00d5500000b81001580d4041502c0f90012421520800e4000c8410100d144074020780381d0141450188600000601483c0c1c1c1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 700748174 1250 700746924 700746941
    0x903050105010b03010501090e0705040b03040c09231f080d020607020d082202010c050a0c0510090807120c0e04080405042702060d020c07030507030311030f18150a03 73
    0x20700c180d80c1c940c0000c0c2480d002c24030030213000410981003000300c03c00745520140c000050340340c1030f4030f40354440c000c11078548d205981c101c4940340c645108101710500e910500c01d5806011340c40b0003078807c0600090030034480c09802e4410300c44543e00180f0301c4928108110000313008050070307a0342e280f2220002a40795901220164050302404055400c40d41c0b01e4600ca82c0305410141001d5141046243c000541014161040f81031080a01c454000305404100b036216a40c0318503110200181001c0a101c00909141041428450b110400b80301c0d0000100301d0500781d403418407170442d1425035810032244110b0300354460300d43c40b40098103200510103181c00810070340b038043e107051003440c80628070300c07600b000c0c0740040c6070001b90520040ba00514085004000c0254807180250402415861031800c03c41c065100710740300d900a900030000c141c1c02615481e030313181d981d8020303504003856240c00022500c1180b49958840b034803051800103070754a03200c0641e194000610b0403504c41055042c041d00400200 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 700749424 1250 700748174 700748183
    0x2060d06080f160602061e040f06021308010f0209010504031403070c0914060a0b09011d270f09060114131107020a1413052203020a11010f050714120301060903 70
    0x10f01040103800056054040c1c0300d2400b01d091848171412098135214401380003214800c0c801d00c010300c081540b60000c0c00048448045540c04c06144c03446250841c1c00c9850082581801840742186607a00b04054904a036000030078081c0556a460742c8a085210f980c2e07004200d180301250109602d0950fa1200b40d890b400941071a034951102401c00489040f0351103641c010309420007020701554800c0f504451648441004550144608400285c911000c10300c50404803101801030031000e040307090703019088000c03111217150f5414880d20a940740c00c01401105075001800b1011812501d40f03082d100390303900055004100341c0400240350450744d07002803816807159094800115601d205540a40024900100788100203100d507007841003d000010300c08100c0f624200781c01c5e4441c0c800740001d501098400e6025103034921840c501a08002c0c0c401030554108040030350800d001c943c010b0101d501d85500300c04040030100201e1621032511010032086082804003200001d080c40c1c0200d452800d69205 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 700750674 1250 700749424 700749463
    0x5210403030908120a11070302150c0c040b06030601140d020d0b010206281d010e01090b25050c030c071401230306120307120c120507030c02060d06080f 67
    0xf50303a80e06540c1d00e10b10344030000c000b400300030703500c0010f008601c00b8050400301819a05415603d800007405c441c2840404084034800095200000e0028001e42c80003203400c48041202d41d5180c804a40c01d800003d150606210103445000400280e40c0c00303450b04495441819552244508144000fa2446807070312400741c030442001c20001130003076648640382c000d0f100080c0e07000c0c01c80e40c00310b10107070182e00c5212645554900e100008200700380a49141c0800440004c24210a1450a10310000008142d00e502c070b520010b003107840c1035110701c0044d0000f4807840c20350303120740803400070740d0070351180b1120081d0306c3c03061007000038010225802001012400340c8800c80340c45821811610118a03106c180c1070001d1080000543c0c034500760b05942d601690b41812a07061032466520b00c2164000d42c5203010200b0051100c0c5010008042000402c0c4017582c5401420105183d0307014012044640c0b0003440b943c804911105004c50709c4c0c0c8280c00500c1d118007103030b2011101a40039600c501c40a908990f01400 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 700751924 1250 700750674 700750679
    0x30605091b2713050109060203150618010309031403040c17070620010914011b0306061d060c1207021921050c04060303020c09010503061e04052104030309 68
    0x904140d01c000100c107a80d0007400d90303240e074000310349007520052078400d241d0090100d83c80403503400d129a003030062160000694a0904c0c07010715610a5007002c04c280704c2c040c1082030750040c2114160411400c5000e0030041104492403900b40d03910032191450b04804ac1c008030810007802101d05048089030318100d4401d441500390740a090f1101500e0103482c0200355000b00782c60096040f50520300140ba041c030000100c411941d91145000c40000030030301c3c4644e44640e0480d410801c2d444002056084504041040a240c1500507080641d5654016030b07000711040560455207a0000f00d416440c40c40040d10480c1d001c0040b00300042c1c1048100b40e0080101a0741a0106000a0b08040540d5008402035001ca03000c01c80960240c4100781088660307004404100307200742c5503401000d018501c03c0d000f502810354403000744019802c059204034480e41c0004280400e249100c43c521010405018264106d135407613040140c1380c08a0240e803070002141004080316410900e602420582c0c5c0b203985d80d0080540e = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 700753174 1250 700751924 700751929
    0x16030e0a1215020c03032401021b0108070201140702010f1109060301120c0305011e0c141e090d2301060b0909090a021818160b13030605091b 62
    0x400900441c025444603525080100741021948214941c40010252904d0f68500d1124210340007560034000724900d4010100c500c400d60300340c000c40c4807000c1c40140381040d842a000d05580d200040110f05000d131841c00f040303180d0b100303400c500008189002c2401540c100721034024003c0282426070035049261111040d0060f04440c125041350310020201c6003103909040c44006000d00b4280c1c100ca21600700c800000000d482130045401381c142e01880d03d11000e05410189041d2008a0014010002c0d1302100360324103000c0d0400e0b03c1840004100b040038208000d90840c0d080e210782ca401c1a80324000c158107404004e1050b0500d10520101140c0121002d001400d23a82652124098900b024800b80204645070400d000e0669002024800b110410062074000c01c0005801c0f0040b400810a0003041040c40380e04540b9080401c21920700521030030700300e1900038002c3c26040c05246500c0b0b20000307498202181c000705840140d90072101c01c11503820483d15060396400a242c0320301600802400c28185072 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 700754424 1250 700753174 700753189
    0xd05030406140405090a0c090e1015020a030815040e010f05090d050c10050402040f02030906150a08060a090503091f02010f06210321050402150306030a06110702040216030e 76
    0x7107202425050329500d9290024011f03000641e0007408000e240000007691508865110340209135019000f02503a040c07020485482529440140030755002c00d45030070021358031221095100301d00000380800550f5060009000e0507007400302088641c200342c0840e4000080d5480315014540b000d00701c030fa41004541080d5000d0050303008600c1541c000301c01c01c0310601c00c180c00c0542c0c098802000003915500400c1c00c801240c1003602d504c081548480d0811105550386031500d181c661080707402d852034510b04080681d075600c0044ca03140b030440c1c940d0300c40c2080003010010745200d813000400d40c11150048242048151024160b220019820440201d209092070710901c0141c42c007044810f850300103980b104d15072207401c2c2c40d000ca041102221641000d00079032024040c50945844000c60a81058010402d03091700e080b01c51102030000304140f040c40c0e0360000d00d2a6490340d2003000419404010340503c003640c0540d81000e90024000030349031309516004005c41304840d101e51580d5090000900070300004 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 700755674 1250 700754424 700754429
    0x105120312060604090e010b181308070c050405041511040f0302040b0a08061512190b07020a081c050a05011a0d1113030201021903120c05090d050304061404 69
    0xa400800641000c07410440714280c0c08a40600b40c0c51509039100c2d4000e040351650001415245d640d00001c1181d442c00804880820703800031012840c0d402c0000043c140103a10442c020080c843c005109420070014031150b000a0000810412481c501401c00c0c60070000c1c5a1804800f051500030004102052031040d40d0945c3d00c800c6242c4800c5003140c2c280300003030010210080c1d0200441d4000510000b00304211032281704291029000c00c2403101c1880304403440411190510342103450f0940b034984400100041c0c0d141c1001d1118101c3c5c072448820b030704268415202806589000a032411112041c6140003081076503070008120540d0b0f02044242128420700882d504c000e25003561941c65038040c009444100307070003280090200a031061045040c0c0c00520150f00180c07007107000308255a018030000250041c0640880c4181819a80040100e80814584480c00d0faa91000d0a0002d21a405840172200301a01c0c4e80d451043c58200141e030381d0001e10070200000c0d4030000324030803031003d031003900d08 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 700756924 1250 700755674 700755709
    0x70306051305040506070f021c0f18050d170d140f16080601050c0309130906050c030f010b0708071a010e090a0512180319020907030e0a30080f0105 65
    0x4030340ca81700303011240107c00c40c21a1045105000941d0170405e1003d00c200c80307540b9252100201420341c0c0030041c1003c0801d0408840c02003141c2010400380d1180c50030035403801d620000001003012400b9103150b0340e014040c04070010a10f41120343c50260740003134440d03000d23441d84210796042ea501d00b603405081600001c031a2002813100d4001c2007803540120007500c0108000400e0340e00700074200020403601022100741d038918685805005050002900c02c80d500082c0300c4415038510b00c1d00d080e2000000b9010b00c070300c084110000841105204110301640c54060380409031007010344400202c19030b010000e02900d15154003000c042062030b80c002030805843c076480301c0640091390001032605070a400c07400f50780e154410300c1900095196414098000c4441d01e0343d409400103030303031801804800d480050070502894170b80b0240e04035803440000c0e00024640d11001007541000001000b2075031326000003001a0326400b2007254040d03290800c0b00039100d1080d12211b500c587c1e0742c3c1d4041090442120030b02c0d05 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 700758174 1250 700756924 700756933
    0x801050a0e060127120b040b090705030d05090303091503040606080714041d06010e15030d050427051003020f0f0d0b090a020a0b090f030d052d030703060513050405 72
    0x40d402c0d80304124551500d944d44025010540d0310188001c0c0c80715880c404880842d003c00400c0b003000402d00010ba0002c60f00c0b001010b65505020110b40d9409031900d0210a1000c00318148003260740c2041161500000600300b00000700100042c100c05800030741c1d045031071900b45240403642000005100d8201d03101d0000c0d0300440c43c8508280301c01800030864400d800761041c1620410400104051402841e14100c00000c5281988811100c1d01c0400000382c46600510013a05070326a1110648041e212003e0041100c0d012010001a0764003015100320b00303d606050412510240700d00e0118212070007a1f8408031492031000c1007008400d82c0c002069404211170000703070042070346402c08641c00800e2500300c46076038145400040c0c8905283d40024003d40c0b0000700000c041c200380e2002c0c940c1c00e805400400482c010504050b0203402200c25042c6103006514046801c21038111a5001d011124402035545e07041059009010b800301f40660750085003e50700210144845225980c85140c1000141 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 700759424 1250 700758174 700758197
    0x20030c06130302040203070206070206100f0b03090f0d180e060604090209210705041407021209031f050a05073902100305060a0503070803370801050a0e0601 69
    0x24841d00088900c0d07107000c0040d81d0110050b11588015400f42d070243d0007c00d880d250000009250500003040200d6580c1000020056406006900802e946003070041c1522941c6561080b032030028003e03803034019442900c000301241500002d4991412950141341c000032600d8107008070b4440c0c0d05451868211500f0001001541e045502030a81e00744020502c8030b1901400d011010080540c581d1a84590021001000302d4902440354120f40f042c071a004807003501d0300490281d00c0750804040c0e1030300b011000402c0e080c1664184034695400c0034449110141040f08680f4000504040794160812403421010030480390088040d02603449914001441142e5140c50110007105141c4c2c0703691444600481401c01070b910240b58815082069500040c1440c1607400c0100c6800320342d00080c06074001031400d01907100c1c007000b16180c4104010462001d0b40c160030070400c1c0008010a6a042c11550700c0e1829200d9902c03110180c120f55040311091000c03078960f891071070355541c150340442c00b14001040c42c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 700760674 1250 700759424 700759429
    0x3030521150312040b070807030e030706080105030c01030504050604060b01090b040b0409060b0316120b060c1006150c0b090313321305061f050703031503030906051c0c0503010320030c 81
    0x3402321610905d0000000000c0402092800380203800060108805100501c5203003004c210085000b0000d290611050606071121a21180080c00103802da0340c450440c2c5101c0d034003807281800180210341201c0e5455550300030802c0d40e60414010004020f04050000810000100030b03640214030950100415002d42c02081e62010151415031401c1525178845c0a0356503a510040d050010070380002e0102e1840d105009000c50b8a15001404c40c11800185044900e0b030100b0134030b008030707031000c2941700325111280a28170f94040d803000c841003504051000b06880402ca031100b4007801805c41e05240c80410200d41042c0c03400e40340340981e04403100c03103680070b002001500410f401c1140038000d485c4c3d103104d150500310350030380e0605040045500043c07000205503062203850240b81e211300c4400c86180c1503990042c00048944200d10801ca40400c18030030401d0759003c603181940c448007081100d22007910000d82070b074009100548407a041c04810b000b01e07000c1403c201c450001c0040290440040e541c08 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 700761924 1250 700760674 700760677
    0x10e06031c111e0c19090f0f092a06053103060614060403050304090b06220314030a080123060d0204170307050703030521150312040b0708 61
    0x18004104a07070701c42e50031880c1400344200b14452007501100a5420421a0018a84032803004240c0c0252032200c180201e04d42c010b461002035400001020074441000750b443c1d80078201706c80400c0a26440c0c1380384241000301540d041041072000981e404039009404190391310128080c814131021410405c82c00009442c00c2901440c82841075a106801c000540c000c1c1286003502c1c3c004807a10755640d41e00b84549114004c03014170900e0b04444280c5030034116615241c59000b14400e1480542d10f45248a0a583c0e5950684800780c0c030800c0c0da034600300c150300000c0c003d1815610007510a4901d07030100c1429414003104071401d1000c40e031201e01c2d1320b911380885400d1544121300e101140c0c141000d42c5803102c1da221001072a904901241c0503840701d003415002c2034180c000142c00d0032168420004070000032004928241240e405040280e00c684180d1140380e4020101040b1032441050b180800c640c48408a82000c070700e450940c115030801c8603008400380e143c03255025040074494180200f00001d9080e00 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 700763174 1250 700761924 700761973
    0x4151202010309021c0f210e04020706180b060103060b0c0a021504080a110a06030e070b180405070203070501052214010e010204081c0e090408130e07020c030105010e0603 75
    0x51a0070020205c80d9015442046071031402c0b550045446015014030165000d0082c503140b50906050400300001805003142000c1c20005000300d4012620034240305280e030000c034421252244c2d4200c241c01c2460480c034030000c1229954003082c9840c4020035200c55030001e40c5c40ba41c40007001094850116020400c20142d412034001000c42c0130071020542490078040039494903c144a0500c4101c030303100803c050035869800c4182018030b4007001c0010810001400f0b82166001703c1714555540b01840c0c0d050140000b50901d5170014140014050b1281d400030082480798090070080040d6102e00481e000348100004900000c005001e5103000031850b0040e9102c03414155000016040e510100b00500f0ba030002d41c449445600080000308500464841040a0908a00d883e1244040d244009042041c0280021b82a4140800c0c19620184040f822074041e02e40c00c0c4503034000b031801d81c000035a0383c012540603034003a508003800040c0d520050442c0c00e0080000502a1100c0c0480c2c262024101c1e1011 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 700764424 1250 700763174 700763179
    0xd060f060317040614031b030c0f0715050a0e0706051b070f1a03070203040e040201020c1f1b020d02040c021e101a01090306020d09051002090415120201030902 70
    0x180400000034200c0b0b0030010b0340094540d45151640e10380840a01150b030110601c40801208004104000f2400d0f03500300c090840d60541a5241d88800501014600601d4920a10311800003419401d12442e55106081c541402c8002d01a42e80c3c0e11078640241d4039242c00b141301035030201d50b0902981707008202911480750100520507079480d078541034070700e01429076202101c0152110740520100b01c0e0a6580c245544812641d00d20710f040516000f0340c1c17881284078038540d4039511000706045a00c280401c84d1001001403001701012138040c0300d030f04446851111000800c80034070f6005200b81c0c00c4426a10182c0e0010401200d50308039400f80406020300000050446c024680340c00c03403000541d003422071904042402000d00ea01c800e21312030216901c0015030140301c480301d020011160303407101c1400c09903035000c007000d80c4a5068818100c05046100402082409007030305c1c00c4c01c04103080c1c2c00b41c402c40300c0840f814010b400c1c941000e000481c10b03d008000c19106141b074600055400382c0c0103602c445101 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 700765674 1250 700764424 700764431
    0x1140f060901031806020904140f0609190c030501060e0f03060a050a0b0904050f010c050306030d0c020102010f02270f0d0624061808190311070504020c030c07060e0d060f 75
    0x2d10741c0b043c0f040702600c01304460150740494210a5814180702c0c103100445843c00f840c0e03850a00544201600d07000400703e500c14014400003960108222091405062a20006001003011888090042c007130900650000a26a480561052401c80c40c00d085800024000d03240944464040c1e20107002c009081c501455100d41d151202c40e04c43d0350300d43c1d01c80c502400c00f03064214107112126082d1216280b0250800106005000f40e554000c43e07184d00c4000c1c142005241107446c1e10050740540304245080510a00c0459070020304e00d440010300c902042c181868019100d81801003003007290b000d1901c0c0d9007111141c00880e001551690058281e4961601c01900e11001d480351244c501c0c2054204200080e01e003001c645234a0080d03020f840c0503204900281c6000c40703412801c04480d04130710402800b0400d0502a921540b0001d1040c0310103040301500a42d5984061080941c0d6039208000c1104188918400090801d02c1404000c4c5841c8008040700d210000a032070b85d10240043c0300100041554 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 700766924 1250 700765674 700765691
    0x1503011208090312040b0a020d0504180c1817160b040b07050a150f0524040c09080601080307022103090f130507080109060e0121140a081201140f06090103 68
    0x1100d002078401800719072003d47c5d0390036121030024201985030746405c0500c03c2c01c8c04148541c41640303072894000303a4140400a41240070010850303162070541204100d2002c400b0f030115820700c2c11000d0014a0541708116071961502446402c1e11080920807403000c01c9041c072047c81158070802c0202416070040e4112a00d501682c2c80d10b201d5546002c04880516544001d1781d00d60f0030240c00340c150b120a0950841055804032520740307400c845410f448500c0780d6500c000f900f48950140c94084007500390b1500320f400941e141c4c000d40d5a0b0340c1c40180c00307a11403941414132910000c0075100d040f030885c170404040c50500c4910410304c049140035500184d0702603100c10180704640010300c070325481180d03c0d075940c85065240c2903124040340c4080e00600400c2d000c4c1d40c0180320250580e54082d00704688021003001d103015904000d0710807000c904ac1c4600768002c4010351414080d0200c007900c1d524908440c000001c6c1da070b85048a4107060041441a08150400d5084c0501d01d883c80140c010620181008100c0c0e00 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 700768174 1250 700766924 700766953
    0x7052403091c110c061605070f031406090a2603100603110a2007180506010e040c020d0f031803030e070e0402090a0c02210915030112080903 62
    0x410440300e811169001c480188402019840d0824084006080100903143d1010240303460700319500800e402084002000311038989009400d541081d004000e0322040c507101c03044e024a07005640701c1995100d0040003095440140030656038018030fa00c0c0d000b442142d206030398000782c04400c0000059642813000040340b60540540003907100d51640310001d0341a908085010b01203548075400c0103076450050082d40010354111134001c0701f06580307202404115032081b48062800b00300c0c1d00008200340d41c10500304100c1000b81c201901480f82621403440c4000440d052004072107081ba075482c0168018280d04502c40c0c0129424100b0480c203140200d03c49259000f849401c0f0354105045002990f00c4002001180781404080c02601e500c8040e038115042ca130300043c0d02ea28010f04510515079442d00310107540c5000300603072249045541b001040030444442945025048041c1d0a401810380c5c00a00708000161400caa041e64400c41c070540001690f40ca03450490303008813502c1501482110f418501c0309 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 700769424 1250 700768174 700768177
    0x311040317071a091005101211040c0f120510030605040204091202030702040608030f03010b0d14011d090f0303180a0b0a0921140d0b09010f0807050d05070524 70
    0x21058028200724074100b0100d06490015042c81d8100c21790b2030541440015290103209908680940a210b110429507041c03a20b581034200c0f192513070240c50103c0c2000680c0d0080b420142400c0b0540340c0001d1881c3e00000041560f03411a4001242c548642e014000600b40360322550700240054800200b0000719507034200496807000c008000f6a001041040840c40d150003404040c2030503902a50502c400704130411840c3c001030040030780c880c101003007200300070010364000140100d9845451006582d224a060b500d048080049003100d414a0002900034000103000004226503000951940e81c3d80355900e201070081c01e206074014045e0100c4880410240840c0f903000f940c84010000d00800c0d5860403002c0341e084801c9910803e69841c0102150381c0e0007902482103020b00360340b0150758584049030b14000f0b21442681c980d1210750b80c800802c00ea80f984520703106541030702007102d052039201c808004400324203132001030803a40440d000b032049040c50751040900380401c80300c0800c4c0c150107142e121880e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 700770674 1250 700769424 700769453
    0xb0403121d0d11030c1801030f0f050d080106030e0a05330a1b020d050a261512070b1926040209010f0e0f07120c11010c031104031707 59
    0x441e0507288507601e43d840d05105e16040c815003102c00700c841c040b00001144c86883c2c1480080c041d498220305401c20302032500d29840c1c44540c800150380c20105024000f8005210038020b41e400039107051f8103030b1140000042c4108416401000030134403200c0b1b40f07100d43e940340440d010001c243c0191348620030320801e414090901a00258001061803000c01d005902c084110f0084081194808580d03071140d584c1220468400c004140303004011108480b44180000400880040c6400c400104005550500b4100010a00003c944411034a549851020b5860100e030140c0e0461354001c200280941070800940c1807a00083c0c140a2103961412420482e150100d55089850180c00c0080004500e449003659014140a8054900050070000c81800742c40005003130255203881c41d0041104103002e9805007828056174141441450803201004045400c4800c2c0707420250b00700080c0080044c00ba002c0c1c41a010442603100d800d261550319002c50045020041c00c6110904002c40004a41c05d200d0689a = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 700771924 1250 700770674 700770683
    0x509130219030f050606040b04140103060302180412020318013e011b08070305060d0b0709090605060711150f070c03110103050c16020613090c02070b0403121d0d 71
    0x83c0101c1000100c016540020712907842400c080005025440c14036041c1da084d100c4060710408102010001a002420301c1d07007029600514035030550516520340e803c10b0380b049106903880010802d901ca0140d84e203006a00888080d0700600c2c408247d43d501c10b01c1c1c6402a581c03a01109e0783c030100c00f0302068181c4009040b80b94450b982c4030052042440090183d012486c450000540030844035070001403840f000a800300c410942c540010480a075202d0031301710b0792180c10168041007801e00d9000501000800c0c481e03444800c4c00c040c00040d481c6031103c1540e6101c1d030404580c0d04050713020010001c01140800148181c044c0620600003911131076400380107078510a41002c484503046040c41901001a070310000d0425040c00100300003800b04000359009480410040c00316403090b0300c00202180604d142c003810b900c480d00300c009000192500106241c0c5603540030380340c00b1500e48004c02e0b41841140005000300643d00010410584906003003d65013500321648048100c0905c00141c0800381904103a4 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 700773174 1250 700771924 700771931
    0x60b030a06081501030206040303030e0c09010803090a0807030f02120f0a1131021b1204170d0503070f140c07090606090305060414030c03130e1303050913021903 71
    0x10142c4100500794203480300f0040785580750700d1580011554880c50000504268070340100040e0150208a0040303030050042c035000300c641e180d49041d0394135040f42c203c1500ca401c4007200041c5250003c210007003501e40240b5440001401e68090020011f41c1131012111813151120800c031006e828010303240030500c1107242d040004141000c02c50091409100000d50a2010001d03100d44440c08030710201d00b00c10075001503260024480841c2c209080c0c400c02030064010304c052061040c0b1108024030075985200d08a041c2002d100c00780035500c1c3c0c0201c8400000c101c0c1080072511403800707007801907500c81080c81e20740381d4180e020000e0703401c41d0044054082c042d40802000d000302400e5009040152456103442c03046107245844081da60714018201900040080203002e8030b1090500450700710301c950000b22a034855044c2911400505184640482040c0b21404501e1042242d09800c8030715815544030743c20b12400601b0440c5030080b0b4640740c1c900c60741c208a01c0000c00020003051002a1080c2c4001 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 700774424 1250 700773174 700773179
    0x1036060c05011406031e030910050705150c180d0c080a0c080d20030403020a08060103030816080a0b0f130b1c1208070903150b10020a02150c01060b030a06 68
    0x5003910541100e501040320000100706145c0c03070005d034003801600254410b0803500c0e0391004250651181581c1d454010401000034071540341c00200802e401c074415000c44a200741c54080b00c1c800c1a00560305000514070030480120002c1c02c0a14550113084010485d190100d903950325801004241c2d400404660403510280040c4510140484001c000c80400f13810340c1e00c40060010040c078103100d055969a5001641102440020015540610303070240c99640c24030b0321000c03c20b030341e00d0091000324001000a0001a840721500310001e25904546d00d50070f400d0f032104103000015005ca01c002c290030410401c1440d0f0240c0d2001883c15180d111240c000a003c540e50301801030444442407101d400c00085510240000c0c001500d5401c1d101c030300d01e000300841e220364000300e484003407580c009130288816040003650b5881640c0036110f0403104071074000e000c0d100c0741d03c1640c403203a08040203581700450486075900700c1660001000d81051107400010490707282c1c41064868ac0041d14510303250303035440703030305 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 700775674 1250 700774424 700774433
    0xc24120a0b0a0b09041d010204260c010507020d02030a020310020310170304170f0f071503291507050d0e0303180f0f040207060f0501051036060c 64
    0xd14101c810207640280c402c606046039603000e40b1840840310b000e141c0c0c40e0022440c544010606c0f44003a00c0c960000d559540e0784400044803002140007403170290801c600030154046000400c0003202d40107031526800c00e0410307002c004c47c0781c500810598240c01450120b00042e0340c14032180083d03040e000c80040c3ca81c1084100360400c11540d82140c495440c120000c038203c62030003c144e80c103da07290001070000450039241c041c00c00030100c640911038030550041c6031000c000458100e0a0790300d0800f49130360014003407a044050324080e070080e0300039000c0704080e650640c5810b800001c2c00f00300904001103800b13811124021541c419a41034603036070442075062110350f91000c41e02d50b4622b811001181007204020b4840f28914550b043c0385c2c451440d1403441c108588134801062051400208115181c459904100004c3e04601c60b445241070318100011609150400f09001070380426668000e02050380484050703855030300b50300c00205201c006205500c41d8036044444025007110b40c0e4665403040c06142 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 700776924 1250 700775674 700775681
    0xd050414040b1813150902030a0b0901090c0801051b03060f1014040e0906091c0f0e040c0305160306120b0a1508071d15061c0213031a06030c24120a 65
    0x541405c15400c0001c810050b9400050410140b40c100c00002e04603118641031500416403010020b004000600d13001403100300651019100391f11600750b003441d190307111510703034042e11048904a502202c40a100100e50801c91140d00d4081403904240c0c8550b10f0303480c2600301540159202110f00c92600042111081e010b0044035048403c10000f840c5131301d040c1d070000048612405d89802004803080d24000203511584840a0181c0c0190040140004a210090180800700c41d40984400d02c0c000c00740c94180300e8410501220114031b16a440000541d84149541501500306940562036030002c041d00010f40180e43d00918844000f403025508e8290944410b05284690040f07445100c0104003c000c10500154640c0030222100c1d44e0f90b914101706030742c00d902d03031195102c0301600c08110108804040c80c0380c0c0054070700a008001030400d80c030503e0060302c07600301e80700c58050300004d01d03402d028140f08031181006017427001d501d5101407204a1207009a040a1010110034002d1800c3c00900da84503c03 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 700778174 1250 700776924 700776953
    0x70915090c0905060328020a0809070602060c0d020d0f0606080c0708030106050a0513080f070e0115051b1002090f1804110a030b0c0c0d050414040b1813 67
    0x80c000704107001000380410b20a8071800d0300030400040080d0000c0340d19000704851510f049480c0104c00555003000c4025040840b1401c0403c1d41103021410315a00002d0b00342c2118255401410240d90700c1c4800d401c1a08803807020103200e60280700512500783d0501400706c42c5c07209640300081091409900400d4048050a42e11410008111400c089006c40303045a047d5002418039a40d18441d4100c1150184a4050031100d00200c41d08040b4502c2c0303010407030095515003503045a08080c2c503000b550130207800a104039440d1115803043d0080a40c0140701078020802840001150446140c0c04141050005926850300d15400160343c00c40d40742058507244542401d941110008450b003042481ca07480140c000345c1102c0545495044c95074070640001c01440e800106101e050074005280300451300040080b0880340204500110a1885901a60102c511071612500c500108409100c010322003004a00d82046420f407003046003030000714129024503e6041c40704000c089504101c00c8039420b00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 700779424 1250 700778174 700778189
    0x60b041205070b21070c060e100507140306040b0111070b0a14040305060a0906060503030c0616031503030c031416030906050405130e0c030a1a0f040f12030e070915 72
    0x780714508400c613404404402c4134140d44602c82042d2a060340a90b120041c039403008040a040490384916840d001c60a4280e07202e11407014012600c0307940c0156903100105c40031054441c814000100c0d1031420b6048401c0156040c10641c40940d4040011428031903590006a10a440020740311101c0c1c0d8440300b90080329203881065810700342540c0d1400e0b244d62014260303540a0b0345520039001441102c1e03025200900c2c0080c11a82c0d40d00c480304426840c1c80040302c001d0a2201c4001044094900030f0148000c4c44910840e01e001d420b0075507806944070394901303206400f00041c2c3c0401c2c9503036203141c00040a2420500203509240c0d0152718000b4030f00c0383c10790070481c1000310a00040000f0f45644030710941c0504810004101a4509110989446038226506e681403003010824070a01401030340c881c0c03079071a007401c0e10100c130303a0b071141c1303035107001c4000c0c2c0e0000c00c150711101403d0049088051190081c0600389004280301300a00b8049180101d01d4100700740c655501d0b104025034042a0700010300600c980d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 700780674 1250 700779424 700779427
    0x303010e1b07060b031c022802092a04120203100e030f25032001020f2703330105090402040c121107060b010c020906011101060b041205070b 62
    0x49070050307581e0082002c000e19054880c030020303071039035000e118021540115480524045041c484000c1d940d503050700142c600444040ba01a0b0340c02040004220680d401070b0150300d490719820f80b804010b88910568006000c1c1541d060a00800d10740000d2008000030040800c407032a5600415003840500c040b0705072407038506098416803010210945151051400a113a2143c00000d42c60000550803ca46071102154030314030700070160000c40c081c1c0681ea00d840b0740400f40007402241d40c200e2003450390811840c00d084c031940000d600c2d8496030040042c607118405d03c4001c000004a4a0f06811041d48406607800e2003140164034401c00d00c4402c0243d0b87c0190b2501c0b0752400012910204010340082d006586503d0788802c0f050003001282c204010b01007042101c4d0001c40c0c085000303a08010701c1251828140804100c01c3d601c200010180203800425240140d2514401510a00c5008070ba0700b07010754960340c0008000d81940041c02c004c00e4810347c25614040310349441da00f400360540040d54140d00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 700781924 1250 700780674 700780711
    0x7150545011d01090305010f0c08072607031b020c0301051302010e2701060807021b060a03050a1104030303090b060103150317120705070b070206011d1510020303010e 73
    0x9100801d2800b0508196140007441e815000486a003600c5805c050880c1d800e0510051074081d550f8080c0c0345044041e42c50144903110028101e54034400240c1e0700e1030000305452a00c1e4001003e5100507000101418001000c50601c201c0c440000c1c8080d0f0020056009802400340c2d07401e0a019080d448103d0003c1d040c482c08003940013030f20010701485a940504001d101407914644801c00b5942c14030918122014035607500d030001800464100c42d103000501a2030801c0a218101a800e00d854980041070701c0d040c0f0700382000450040c100107041d443c81585403522000344920000080c40a140030340d8000c100d0011394109403c1c4144098400e40c101031500c0c4d40c1030404030310140040e0070b40c0d0340920902d001300c0070704900c038019014894118900034042c8051140003600b00c4001e120b03251140000000954448030103a8130f43c0381c01d100702040e24030f403910580f01d40b84c4280c120580c440782c402058440540040049a5000090110603015a02c0000144000380d02c00d0051640320300c0307002c2a41c09812 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 700783174 1250 700781924 700781927
    0x3060315090312090a060510180606200a02040e070501030b1839030403110106060f030b03191103070f120f030e130f0f0e0715054501 59
    0x3c100c030741d440030006800300403800a64003402030b6101c60f074110038184403900b807030007a40295440c1407081c4082d90803442420310142d4524003d060484003c5c4e00c98105a5501031204d411410b00c0c0348044810340240381ca0000140c0d903074400d0b0200c003144100100032090a220016045030b207990450340c480d1140049040b401041c0400182d07014001101000404450b6000000c0c0000c0c3c0485449126441c01149080d42d40e20070701951086000381c2e078000d641d4074400e19803400c84010b80180c4001891410001114074080d4201d90389502d80034080b1602c3c40100e5a0310045a18280c0f421680300c55103100076501c6140070046500940503c1621a02452030f1400b01c012100710341100030560407001d000d013000c0c103018014022100720050010038000c8140c00c0804014012041541d8549150030404520314209214841002220300300800d0203e0a0007602c2c1c0c00c01c05c909100c002080010011411a8188015074103c940000e044100c0e0511601c3d480141010120700350701c030520964246160107a = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 700784424 1250 700783174 700783177
    0x70503010e01091205070f0c06020607030b010302070b040b090307060e01060f0501090f06181d04060c0905060304081b0d0207091a091f05040c081b04061e0c021203030603150903 78
    0x800c141030040c1d0302c1101f803130301c1034100031006406011403400d00d0001444a8002c106035201d04100d540400a580c1c00c82c0c015012130003107075006807003101441d0000f00010118980aa000088601180d040c83e040da40c84200b03a82a00300341101a946440c0104000789601002c400940002d0910144207414100e261094034540e00c1403504012059007051450880100c401e006084c000e07a0ba00b04030094420300380340201d02647c007100c07071a28140781041464814198001a5130008200c2e600d0340d00c8503218000340d90004c21810403440748006180034036140400843c0407039001c64010700051490000514129901220413074003040d82c08216151b1035468000307403640100100c450340c403611888c0c10306002407581c681106070040e141c009104502500044181e115000c110350044d84481c1c5d14052408500440c400c000c0800d07102c1120300c0c880c400743c400d034285401107882c01c0151855117400040d01140c0b00070464030705400000600081d41014841d102c0a555003000d00311203818040d6429650317 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 700785674 1250 700784424 700784453
    0xc0f01200406020d1413080109021807050f070602040906120b0708010f0b1b010213050a05030d020d0807110a0803240109150905131d0a0b070815030708070503010e0109 74
    0xc010178107141078051070b0021305071400c0c00040049a07103407a48541d840c074024450700c6403e9202d464001c1906149140c181c580d244904042d6842c44e0900c140091003003242c1c1c1111004403442030b000e2002040440e21446150020300110300414481541402c00c0d202184016184400b08402880184584e100e01e180c0c0e00c04541982c519550f403481403110b802d1824402828000c16540009501008551712070ba0702c0b8160b0380201d0303200007203d96406c10165516a100c4a180140e007000c50042c1d0140c1c01588040e40c0454030703040801280b04c4c554259400c2000440c02100c0101c408424403020349180501e0b20343d41c1405004580c81304042c04000385c0060410710803c15145c2030011400d06042c403130001e4a0041801602105000d0700c131001103c060400980d00124010104500602801d0006035a2511507000809115030761601e01c003c446540009090440300328401c0c030f80d403003da1805c10861000704a054094042c841c00c000070542542c41c03143c00c12840b82e0419440c0e0b4040765010600104 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 700786924 1250 700785674 700785677
    0x213050f01181506030b0a0b1312050307050102040b0a0e01030c270503030c07210f06230901050108061f09050a0603020d0807020103060e01081f020c0f01200406020d 73
    0x1400c2e141c550000340c20f6101c51840c402c00000c100007403c0e605904100300402c0101d0b25003440a480715001112409211a2a200f0b0380c2e02c407d0070081d0303c1d110404d0a00c40c0340900c042d02e00d05a295281c00e800d90b40301d1380c0000341c40d090005880246540c40103506440d00c10929090101c8008000000c00b030f102001e003c0070040d05010303154055400301551101c010720010b01941c0e00c1c0d003801d41c09580c403000140b250403010b41c000b210765441207490107070525690303034000c0100024102c0d1383c88840080c21552401c034000c60001a41803450b0a4440c041c0d4172414101d000444d0640c142100941800740281c4030006201040000c2c40190088032031842c181c40f004c8500050a83d00e25242c400541010313400030350490074604520081c42103160007485024001e0b00c1c01e1000702d0780e42010070092070092040140c0c682080b0241010b40c4064003a541c0c0195200502606000451034800c0c103044924401c200142c1d9600300708840d608540700a203060f0740c0c2407180e280c20280b60030390194540b02505074050 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 700788174 1250 700786924 700786949
    0xc050a12020f0102071d060918072106020301121106191b0803070207140307031721090a0203010b040507200a08070602121b04050d0c080a0f0213050f01 67
    0x500c607034420440c03400204044140121b62002040071032080d003009454050295540c58005101000d800c00b00c6280360044e240100781c45858802100c5000d05102d0f110408180071610300d0010a52500145010705000b00b4059840030382464054121418103100314058501400707004001c51001d440c000b800c201c0380c18410b4a4817031100c0a803000440d040c2d1700400d00f800c04410f000c0b64541c00600d500c01e8455411000312040c004004159841100c1c0c8002030407122290110540840ca07000500030360b00b80d0490300110b14603409520000c04400311911101a4480621081585001d008071109814159810059400c1c40040202240c0b41c004990b07414400c8416010b0104001704103d01c03106400040c00c03a01c4506a152110103903100c1010384510b0582d5078085900c0e1501101105000e1100e4220103252500c2c00081c0403200310000c00603a0f180c02d144200158540041c48494000e82c071543c81c03404003220300c4c810820b00b02d1141e46065080c52520080008000120903918113445084101d074 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 700789424 1250 700788174 700788199
    0xe03010b1f1209051c020d02010e07032d060c03060b030c12061302210705190f020102040b04080303060102010c0c052a032a240c03070215070c050a1202 67
    0x102034055504010581c2c8200a042c943c510305ca00c0120416400940c25170b4038850980304200d081c2c54011402501301e800141c2c2c10000070701d03140c3c828450349003440f84003031310381100188454001c0094a07044d241c00c0d840300084580e0030f500d449518040c02035000f0305411070400c522168058080c0c80d10604a2802c1c20010034a40d070368036000740100d20100c0c0030655985007180c8803503980340d40012850703824011910125003807a0065094821a041d10085041000c103100f000725030416a03001c511080d550708120111728000d00000038009071003814001d59880c10400c0c0024216803590392400e04101c0d01c1d201d0000040c1c030104198400301d204c51640f80540b03110403110005801c4202c040c0d50716104007501c04540c09201c40c0300441081c800001501c5082444080c42055416602e150601c40c5004040d0a5100c141001500541079480c088034280041640030038002106a103a0718a1100d0202c0e040341040301030248140074000588968030264a0300c0011003c88041c20f00c003c1c403622481401 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 700790674 1250 700789424 700789457
    0xe010305090d0c200303180405130f060c09050a08070812030c0a0507051002071406070503150913020d0b19020f03011809060204150e060403021c060e010c0e03010b1f 73
    0x26105013460050903030359141036201003410000c0b205061540a142070900003021580000d04902c0d82c00d030008101a01e600c1a59608030041031403800f88014040c4c001800f00e400d49403c800342c2d02806c1840c0040540604142c0713800d25109900700c418440030010020820b04080741001d41d603079861103090841d141c81007850322030708000c10303004091515407000c154082400104c4000042e5844000e080c1d84954a0700701d0202d54510088031400528501d040317140001d8102907180503449144140503150140050340010307000d20240e04141d85114196040c001c071044008003070960300d40d80e41411868103a00703a407988404d0005128562030801d14040e840310400e040d402c5484010b50080045544903110074032019044080c4491400280e42088145000d081c20740c100c409aa03001003c0da401503c0b8440ca40c0428804604111001a2640e5800101e06000d014503800340d0386c3c0b0340750142d5054100041c1400c550303003c64240d20545200d03481190f80101550f06009250052801032005070b2890507 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 700791924 1250 700790674 700790723
    0x30903100605060a140c0d17061818030421030f080402010c080c010b0409050d0906030b030303060603182a0409150c030222030204050c040f14010e030109030e010305090d0c 76
    0x801540070b0060081fa07011155120b150500c04c4051345d1803902054803800148640700b00d582c03180d0451070290a020604520016501340c07080802941164500703602e91400343c1980040e00e40d1288295007808121082580104140c4a00251843d180c0e00c82d103001c1e0002061002401c8014019110000d98503a00c07000039044041100d501030000d0191007410b24000740c0d105c6500c20584001924420003180c420b20a00500e801020000c00450941d05c1d03040c2003183e15030014091000046c1808980e1801034024000d0703580407800300089402c8458132201a14810b280204094031491802c104100000c0101c06103080008145100040b00360704560b0981c000d1040307984000501c2c0c078650f031000076100e500c1e0218094900c02e4134240400d44407041002e5070742c042c1e400385012100c030f000030900004006017008800403805142c80d0000d501003a01103400c49829100940010b0880030014030b065805024407900030381d0481c020000040d0f80c4000408100000d84010f045187c3c110030034100e0812000d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 700793174 1250 700791924 700791937
    0x8041103030c0a060f06030507381e09010503071d18010f0b1c110f19081501020a0b2d0a0605031515040905060702030903100605060a14 60
    0x2011607a0710680700216640d10501c1e00c03c202e9420303003084400300181d10300380212130840342d102d4020026a81402d00294076188000100485d2242c000910514422040542c158454110f6105941c40c84c80c01b01c071241c800d4116070b12440500082140c1107060764804101c9500c004945003642d00506050034204000349820401a8400e001c11181038407908007000641c101c030b4006442e2000541d660360b03900f0b0b440c0121170f008903080078000c541054208041d00500100c00e0010801480c04804030304042481c0c210560f000500302d060911104215040600c00d60020f0a6426550848401c007000035950140f04000030030701901d500200b10444c502c0554051402d412224004198080707003002d0901c200c0031682030881c1800c00324000390600300402c925070003c80c0c840d649500765444403902462000f42c000c0d00e6800c02d5840c0f42c1070300480ea0600045010350101e501465807442c1c0081050714180070f4001002d0b8140c58070404100720f9845004881c0445120300702401c20076486583c202d4180500d5 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 700794424 1250 700793174 700793179
    0x507060b0a0e0c0a030e0607050307180803040914060103271704030b10150816051201080304291603050408060c2107091802040f1d13080703080411 65
    0x107005100d80450050074804c0c003940d60030414054001401035407881c044d10440c020850130004510060310030b064450400d00c00648408102d5a6142506d24560040d40324a03200365649a1175550004da0f101c031541c11500901c1e09205803140251800c520032410800311019806018880003007101c503101d00c0d508240140880f5403510354a0038400d010440403201d2501141c0300400c08140800c03c691084c0700802d107940c508505070b032800a4409440c0c3e500034200c00380306080c000c40c0000c6144008d4a8040c200ca000a961154a0440703240f000304550903910401c1c8401410045078400b0000c20740341c10054500340c090100e40b407402c05036864030840c0c01456060041a00b005501da4035074001300069218246034921929050301e011031042410b84a0000140c3c0da03040801140000c18081611a01425030051410341d0703404000e02c511000c1e0307001d40e19002e5240c1c2d0f070912422098040030b40c004000100e80d280c0038446e0344c1c0e1380f18070321541c0c40060610041c030b0702040c00e0102e00d40c82d81c003050001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 700795674 1250 700794424 700794449
    0xa260103030e27071b060c080c0324060d09030908100c02030702091003050f01090302060c03010303020c0d0203030d18170f03010b1c06061e090f0317120403110606040b010507060b0a 80
    0x742451b030050003650103208007143c8900c010603402c0c1101011a80300d1740d401e40b18498000c45851610070001c403180c80d403d40c4140700f4890612136440c40c1c440c0400c0c1e41c0c480d860360100707980703400c21030350400b00625444143c2510b0700d14504121a000310032103d45690495505140b5076074121007000c03169140c0c0001d03220303100d510210851888150b1000421324025000c0701d031140d50f0304072241c0e414802408001c0c010303040344030980c0c3c450a04e101c100000c42e05c0282580e040c50510070045003101d001500e490380401c11078100009000c9192111201803103c1c2003805d1401028501c08060b40c841032141501c03074880014082070248900c0240c04200d44c0140003402040c0d07690500418112210300003a8406a41080d03a89225015044007012a00b52140d41c0070460328540711408020007044035180301060170004045132410300c0060511440c0303e1b40300c0920103000040541d180c0807001b011180540e18115014404c0d81e0820150340500b58401d801044004a85000c20318075034495100c017948111 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 700796924 1250 700795674 700795727
    0x111306080a06060e01050d02010309032016170c0d08040b040906090f0506011e02010b0a0305160803030907030807050f06040803060f03031801050a260103030e2707 72
    0x4941c00801500581c07092042544504030181000401e01c58203a02600354444280154025003003000710600905060025000c550740c7c0506246c41c5010040d010b81000240c241040801c08401002c0e100f040d20030b482503240c1034a6240d489a445242600c101100f4035100c0400c03034808115400740c80700e240340640341c80e40d40a17100090070650054450003070030020240102921b6110722845400d050f502e004459880740d8a086240307140084900865494180e1007540752120070300b0b40c00440c8580000e00c81e14440d03e1031a81420101e402c0540c140d0810800d02103841c00000303615054a4010240c280c1c1c8032a00c0c500300b0300c3e00039a110590325038082c24040100b80405680598030421081d00d0741c484da038441c403082640380c1c4200130a8103018011000c010246510801c09409240041d003080301e203400105c8203d07042005007241c3c40007003444283c01031040542c4180b00c01d205c542e050303c0c580f07003000e5500c101080401881440c094940d1002c00000c904a20039020682600c0c1110801c0c00c0145 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 700798174 1250 700796924 700796939
    0x507170f3702090c160605090c04050c030114010f17090c0a1409270f0a0507090c1b0c0911040e090d050304111516140d0903111306 58
    0x80e420030034200622070414014209050310030000348a40c0103000c003030350740e80301c0040a055400028010844058035600f0344002405441401d00800170b14004200d0b0b40c1804003000140e07a03000b00380c001520014030040100d44041c803c4021215030900300340355090203401d0101da00c0034881c1e800d140b52242c3d0405000c190380d0049008080c00b101501c04907080d5488410030380342c201000d491240c00c80300c101d000480400540d24504d411140ea121104002d503c403c000702d260001c641c01c0e040d8683c00c08003030101085820001000144030110051104030481c58020342035000e110041800302c0109250300f400c01401e41c2002001d03101820b803c000ca07105030b403103a5500d0303001070250b400c418a030000441c0c4550000034603040000c0c040d548652459490340c0c4c41b500c41c104061500307a0051055220420f6120800300500f030700b600c4201c1040d014441c0c900b010304100e070f501d0f492400039410281603042c82c50341c0940f11a00762500a2035002688480601140e1011000d44802c0e0072503107810f40104121 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 700799424 1250 700798174 700798213
    0x80309010b060a0f0f08010621090503070b07090e010b0a0f0c12180e0f1b190806040c0905090606090f19030c06110d030b0102030706051612090507170f 67
    0x124015500c0c80400c0c03613041020b0706d02c440700b80507800210703071004000c825a6031030035041c0040b1540c90b80040790f034070300303598134140765030400c900490740e0034158820000502d9000070f021000b040d207440700c516203501d03003641001d061040f920450b00300308a501410320f00c0340c0280303480f440c0c565211080c0034070100130f080c0041c6000300140c1c034030b6426000d1a000060f14102c18441d940034805121100380f02c0d454051201c0f10f541d20b00d501d40559200d09002c600400004600d5600700340a9580b225846460440104011189031310919030500095a07028001c1d034586411342da90040c0290b859998680d22107000490504100c2170a65010101030381ca103034030384840b20703081c1c040780d02c11015004030325140c000680c0d007945464101c8501d5840194070030341092082c1c01c103212815040c0140d900e80b00840d115075050f41c500b1070341ea5a000500700d040740c4078603600140815102c80b1122080151401e41e6031a82e072651240e10031006e19800c00041040800f80134800c020b910f9040300e0032a5907144107a844940b50 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 700800674 1250 700799424 700799447
    0x10209040c0e1f020a0501020a02030304030905010305090c121005040f060513080306191e0f0b04050120030c0a06050106030b060703021e0c060d091b050d080309010b060a 75
    0x294280600c440304540245000848503070010042c0382085643e400074140300c00c0583c5407404500c205840c02c0c010400a10050005d8840b580c080c654914180c10007600c4003059501c10360405141c10108445198080384084084134115010300c051034414004501d031000c49210006400e251905201c1003182c00301c80c5200941c468003050041e59588840380510080c441e20143c8444030400c0028008e10340550407510002e13120a071814015200e072500d0241e08400000c51800c3d0104a50510041610010318002045c241c074200e85807505150008001e03010712403c00807500702808090380501c0060085e90a200c0c5900308030380303240d282c50500102a007002c0c410140481e05d0f001516000e81044000c07608060f815400905158104000c131100c82c03e0142d41c164601e020380402a0079a40e03900004203810010726001207801080c5080c803c5d103481c0e14044094010301d4a00307042000d5101c0114520b0060b4204103145d459a40302e801c00c80c0504800201c0c180d0041000481034040d0741c0085400c8034 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 700801924 1250 700800674 700800679
    0x90603020901090c02060103080c150408031b1e07050712150608010207080a1b05030c150a0203131502070807150e06040c052e02061f0501082412010209 67
    0x601d40d03696418481212100544400160041c5d001400444c803004000c0c40e140c0e4201301200c41c664004200640d81d40c0b01941c04a4a40d071000007441005402002c5d10216540b120081c0e41c548840da5071481d2020002c4207401c1203a88003c41d0900a010301400400020691480502d0100352a450110590807111490941e5286040400f04042405102b50340850b54802105841e0264140c029580f549800d404100c01d030787c034000e40fa4009841030014190144503980180a1840c9030446444ca4000042c407480d0310501c1030040145080700b42d00c080300c14a4001d00250500c003180b0070340001912440300058a0203a00042d410100440c0b503418842e07904090b4001c105500e003884845441e4502903e000d001c042400d0018071981c508581075020f8142c0406c0307082003589807504d0040080c5070b00f0b038201c1d0158000c401000b00b018486000200310701101c0d07100000d40c50030000040d06c102e10280c110f001c800200170f0309800300f0038a030070b020404050060440300c0703002485206902030b60200c00c4c13150 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 700803174 1250 700801924 700801939
    0x91a040507090509030904050a0e0a05060709120506010b0307052205090c07030c12020106051e090c0a022a1e011814060705031303050a052407030506061309060302 72
    0x1c00d82e25600c42c450160400c0d501940c40d1003148010840502005400c0c80c052030f584240640002000704114003a103132090015112520708000084c00548c45503102c8400c0000d494196400198007095450654081c910025165182d800048580740140c150704100c3c00c01040b1500302c04150360070102e0444408a03116109581d13442040300703e6009002c0700601148080a1034000200c0e04286101d00c0e00d040c2c400000c1c4151b4400008600e100074044041d4901e02e4201c0c10b80e098201a645c00b90700404c201109860004402c1b8020342d11452003c40460640341425840410200f40c03c013050781c4000100b01e41c00c0a003140c1c1d60b1480c0501801207950101d0020185140b90b002c00310160404c440f12054912000a64181800420b500055044801d4081044209084285060004c000e140220300400072540c09160440c078060181580744091901c044680040305540c580e040c0c2e1150003446c011038680c90780b10208015015580306c0e10480510b030030f0041107070501035001c541240d00803103204 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 700804424 1250 700803174 700803179
    0x318060c120906020307120201021303060902090a060b0a0507030e090a0e010c08010b0d150b160302060f13030c020a05091608011a041e0506040f0302031b031f091a040507 75
    0x15520401107200700f8001d40c000b44500800302d094034400c80480100d90002515000e41c2c45402007203203d07035400480d00380f640c405284003036040040382c05602c0100d01000304106170400020240e04c0c09a80040801c00400085540c10103204503070585070580040c1c600070250410a0001c1c004c1c2008488211042d0304e800b103141e2105106420b10350480d1407007010a8900050300c001003001c1c01035548000c42e480f01c00c1c00f00051030b020301340003030503102e140c510b039030744103a00c1880c2c020308020000e04913400301c41c04007003800080b44d040c504000c0004e40c90f0030030385043c100314408100302102c42d60001c0e620030a00002c110f1b100202d90010310400010381e0340d042a03607890f420100751071402402940c41c0e154050100348440f40011002c803003147c3c0c080ca00281c001e41d440b40086d020b9840343d00f0441e01704002003003c00460a040250f5510821241d103c86407410900300442da0713610b43c1c1c2c0380000403140d41c0359500b02c0c1c00181e81d00c038010f2143c100c41e210403411864046540e01042c15242243d1510485000 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 700805674 1250 700804424 700804427
    0x102010902010906050c0f0a03020a3302181221040305101805010f0209090c030402032d07080a030f0801030c05090408090603040b04031404030203030d090318060c12 73
    0x81100e0340e503050b1030f410b001c281048000c45482d000a20600a00d02ca564180c0c56031840c20400300321654402e60003005501741c1d520f814150030703006c01c0500780e60403030b44007082c0c211000300c48a2109042040c0c0d00180c44080c0c440482e8500c40d43c411407560000200b035443d084c4901e01087d05400e51208400740d0f00f407180202e00069151182d448013506541100c0700b0341070081e510781c009400804071041030000c6410241c4501c1e007154680314a481c0d83d19030014840c046030502e031395119440809002e1882c03e518140d00400c0d1034a0505488040f01c01441c0c16810244141e0342e150701c81d52802c00111110f49484075055a51425042019004150340c004440c21040c4035502e06810384e640203504c440804d151400744030782d0702c2d4040c000701e9402205100301595911001d01441c4202c0c0125003e1489041904001e40700d5420b8841c42085144201310510140e10008100d504141a0b030000264030300c0d0340e00b801c44d0501600007400c20902c3e00300707500065007680040f010042034017035995500e003038846480 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 700806924 1250 700805674 700805681
    0x50105060903030706020306040605150c010f0e0a020d08041208031b07021c030e040f0b01090f050105180a09020705031e03130803130c0b2d09130b1e0f010201 70
    0x100e0a0340355004011311000625142c01850300000c002e0800b003070258803640080c0230118400d8a4550300180450141e508a00074002c000c2c203141800f404206d804800c031080c60b190744200101070301456090004001b041091030403035004140d044c1032001c100850345001c408a51082c0c81180f86505034150f40b596402101048500a541c01080500c110700f1141c0b40c0300b1554840b90b400c0c0c06003c0040710090301511507008d90000b40c40318a00004404983c080054200c48181e04405429207490380b0511103a6002012950f88090f0381c02045640350f031007070000300b00b041d0a1b08024200c3d40045020303420000000050030a00055818584030420b402e070254019000407a1181e10200f400004440822245001150000e042000d1100341c103600f9116402502c101e80d00103519124005158a200696400c11080c04001c0c2104249003509005d01ca4040707028800f45140b14185002400011008940c03000c41c0801020f0414001d036000320b48800405c14061095038015480740d0443c08045d1710620 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 700808174 1250 700806924 700806937
    0x7030e040507050412080d050c0d050f062b060911310b040f0e1c17010e1801050702071d0f0f0601021509030703140f0706090305121905010506 63
    0x30f80340d0f41400e103804e0041d09184070100066841303010420449a1100440c01054070580004800c0c3d650f48940a100b201101c000800da00c0055030000c090040680d9140c0002c03101d1403c024900640c01a000000d0341c4104a00390001d1070b041c07802e2022410427a418a40b43d0a800048503542c0342c00c6401405c1c0d0012402c8032150030b00704107120114403038440c030691000c0401e05000e8000201c0040c00d0000d1710843e000304821146540c041001c2c2d14142c15800b035444440c1c00b061400c00d902d0004034440b840103280600440341401410030004907600c11f01c0c85031301d4888040000900c29418003003c0a5240c004500500820709940b820042c0f011031600320860003029a42880140350381c809006000c0c400000d0161411030065004900c08100d5000f0300d036020700000409141e41d0180d503c3c0103002d030000030103004095081840440c4444412009a5500c5034000c0e0011802000500e4115114810000c1ea8040380444600340507008241c00440c105c09500c492040001e0307601c880c01c10909010340c0 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 700809424 1250 700808174 700808177
    0xd0b0711030418050a0209130603050f01020f0304021c080703171b070210140d050109150806010b030703060b19090e010f23030601061d09070c0209070905040c0507030e040507 77
    0x32034500554000394000f942c0030b14105001030807c2c102c0720010740002c829641c0810210707280c07a810310070b00c80c091141c030407081c910400861514503003460b5484107001c0100068421b50003a00caa07801c0e50f50740f06401d00304a612010071a540e440780d1a0280c840c03245482c4540c200c0c40b60300700182d0710003140841e1726180c41e820f0344c640341040190381c00c00402c06110310b04041040b1011589500b04140c03a0050240505075590200b010760402c4d40031011525000b03c04001c44515240030800d06101142d41415900340c01903243d44c2c1c0d540c007002980036044035884002406070010f408a1004803080c091000802c9959807040d000d56100050300c1c1c614428007848a0140031707082c0400c00e07421718416406c1a080d00d800c03590704c1c0c59032000000f800c01009a02c20800f140c0e0718622104e000c444002206400c2c10101c1c0c504030641002ca100504500340124000c0c00741e07603a03002013591103001e0f4a0b481e0040c04002c10a104035050a4001400d941158004401040003001c00b0b12151809020700f91141005 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 700810674 1250 700809424 700809449
    0x703050a09141f030902130608060c09150307110313142d0111010c1709160509060d12180b03130f0f15090b0702030a020d0509030c0d0b07110304 64
    0x1940100f0501c0003640e80400b06050342e480300040181ca40702c580380b4021495101c000780c580d01d01000a030410304010199211000d0400c103d0129039203040d0319001c10b014680c3c10036180d039600d900544040308007030b0048086100108a80d104040000e03154002c1d1040d2468184000003990103120300d40c08d40c41c88900303240032288001050005c14061035020901c0c145813505884215a82c600d00b15820704111400103240b1000001c0603141c0b4014280d0888041001008007401070208a0328070b50860180c0703842560f40c3c10100d0480d54583c2030301d805064000d03008801c000882d40c0302415808802000100c801d0121f080064160200010f40307124118190100752000c18542d600c0045035025003044440c8042d000e80440400c40300721860210074010440007035001000d0420842035200201b414003154003c00c80050440d5000c0754443d070741909410450388400d203800010f03007485a04036040d50001d01c000c02e40014805403216860054441d500d441290404011540d51a0b00c55400b855104c60a03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 700811924 1250 700810674 700810699
    0x1202040e030c0a1e0b04050606030f0d020606090406091202100b12060c0c070b0d06180b0f0f040b04020a03090b07080903030117030d0504050a05010b0a27020405060703050a0914 78
    0x1100340d00122800c004c00003504404410f6030310740780e42c0034040e5426106540300c3c000304119410200012510941e40000500000c00650b01c020364490000702014040d403080b0003c542001007a4101c1c030502e60388418400503000425000035660300c000c2e410a00f02c80e061074050041424000e1100c4020300a03c4060300c6a55502c0300319100a90100c51025003504c141c00000810021103c094851146024404103282d407500441140600302e428003e14803624040d01d0058a50310200d081d402500181c801011500c1c008001a00802c1c03001c40b02d0360080d000180130103c03568160300105d1298800c1144000544440c0d4044540e00002c5a80e2400c03036000300018086141c2c0000b00d600c141d048041124030b4600e075007a0180954909807400c44166100719140c1041200030b00813210114015609130441c640781450b40c0342003080c0741418600e00d03007074001c2070409443d240d0125009808081c01881d5102c2c01442c1c018425401140b480c000a1140744010405507240e68001070400b5006244050701c40 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 700813174 1250 700811924 700811933
    0x6030c06050702190f090504080909091f020f030f150907030b040f060312050f13240206060303310e060a09050402031c02191415010f1401181202040e030c0a 69
    0x18042c8c410b40f400c6005200c1100160b5881c0f0007188103010000c0a40303050301514130b00c1d858001c00120190507050050002924050710241682d40c00300480b0000e41180e12041c41040c404051104002d40042e904010070242603010f170010b885018055400300406d010402c0d2980481700c841c0402440c440e100c12140001d01c0c412400381402c02c004100040c41c2503420240c00303e00340c505030301200c0590000c4828900d207030f03403411404484000c140003414180c130f040000661280f04a07414080c002c0006025030701b4030701e040a4403151218001d021191301e1501e40301c108050000855a1a10600918401040723503a1140070f028040d9501070000e1038003209140310798070503101760340300c0000318800e9241c10403480e034032a4a8104014040c00039408012a000d85141c1000c3c480c000b01d0007902002e20040161005419014044544c0c01700e0f9400100380071030041369403000281d48030b45202518000840d0001088000242c51341c401c840c100030440c400070300e15450f402a410303a0a003540145a01c0b40c0440c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 700814424 1250 700813174 700813181
    0x3100b0d0807020a080a03030b01140a08011503020c03030901050405240403080604090203010c170106020a03021911061b1b012c030d0309020405011a1b0106030c06050702190f09 78
    0x8503c010f03c110909a20b078810303103150001d001e034190f0000392100340c143c20725600005409050704445443c10306d480f14040e1302078040f070010710800c088070000e124819030480c402d605071044400e0340400e0f0795490612064150207094192025150f90041c1030710088001c13110340c41200b18812403003128086541c0e98500b03680380341d07000b003203990443c0d100d0010600694080c429101e10036100d0f104d047c04011070702c540c40c40580c416000076003950700010101021075000103c00038004501703c94501407040301d150034400d06482e8005250081404140c00c2e4401110140512600504030210741101c442054140a202c1800d545940403540118055507860000d84d0003410f100c001c003148100301d47d01d042c00700703103840202285000029076440c580301c01c40c07400340581801010b02c1202a0000b00100380711040700d2080700c01411024420b41524034150000390040c400941c0c109108140269550b200039245a2241c00224420184964000c00110300d019905042c1e03003050a62640f80790600d200b0300000c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 700815674 1250 700814424 700814437
    0x4060f0c05191505060316050607140d091d010e010501050c070503030a090509060618060c0f03030f04111005041701021308160905090a0609080c01050a020903100b0d08 74
    0x714080c80340e040003180704200c82401c800d03204203a403650140c031043e1002d08540d00503240034400c1d00200d6403103401c0155200254140c4d2070449407107541d202685840d83c440350700f194844071140580700146204d581c0002024040300c0c94070314001080c1d081c0c0340d07190f11134a40901a10f4000c1440100601c910751080c00500200b40415007180c80b00c1d511500040d28542103030a82c0400102484810320403030501094440d0031003016104641030411140e80c0c8008074000c206400e00515000c50210b00801c01005240301e8604c2c04820350750b403828813080f0401d13031860495081c1d034254250420400c42e414010132210007820726039038890034982041540e019036030381040c4807135540d90240662060b0256031070500c0010844140140917207404950b0500f030f105803e500003e0a0351400e01008407e6201141d81c40d2042da004a00145c00e54840c901880c0901456000c004291710344000c1003127805281e03004280007074084080300c50303d600a001d9001580c004601c400c0c4c11028201c080300000320b2401c00b4144 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 700816924 1250 700815674 700815683
    0x507140102120f2a180108010b0301030602210a05071106130209270703030207050a0e0c0a0c0b100807170319030e0a03090e01090605221104031a0a0204060f0c 70
    0x400d1950080c94840f541c0c44d0044100f01e84000140300640d51048803e12001401c0c04c0c244030140c0c1d1301d003a4002002d404144800b03802d0a0700040c0c5004d00c020920307465604498241001d480345c0c20702e000824000c0204580250104401c4940b5107811040043c205101e0030b02020307101c6805800e0313400d109110401a20041420100001d00849844164800c1103030000010040c040c03e851400c009140c0105940160b0154480c00c80034403204405886451340018096260f0760f45496a00c0e0444203180105030192190109605124214801101420032150800c085a01e0309888549281c1c10b030013820000313001c503801000011549104035803d0041c11a02d41000109508650f1203541045255041200080c220510601110403070f40e0300507000d000e400100700505402e0401056030416000082c200d0003442c40d902500041044d00215940502c1c42405070f11555039103080d9141540c61714502040c09a070394006070703810216109135005c81e05159240710000b032816006440c5c0b1140000d0581c0c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 700818174 1250 700816924 700816951
    0x4060314151e0f1e18060625080d1407090510031508030412031e0f0804063209010239030712020d020a0507060e1f0507140102120f 58
    0x100d89990740c203080d810b00b02014070f14403500744d5100b0401c012520b04000c4003008020200500055480d454141d42d035415030021003c50701c0c150280a91003032001c0920082c00744038002590403000301c09800912094103520300450b41a2503d903000d88005d0b1f03243c0a81900903e0f020118030442c1d01c01d41110315440c1d00036800c4041151600c89281c2154420782115580b40b01d40401d51040543c00440c851550000404024000003005001882102c3c641201c500f082246808a0140425503004504203c0c400c58030180305101e040c94004000e0003488480703891404240090502c803418001c598404a111240b215140e8a040010800180c1614402041c20542072003200e01c0000300010a140c038010b18042030301039100540280392210140d00c20003150000088c0c88001900010350301d06842050520141411080c0081540314071012800107600c88a21000ea05807500203000300301c0316018841c90100c004d41500102c1c241e110711407d10b0780ba140542c00142d04114000440340d00400c04880c1003 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 700819424 1250 700818174 700818199
    0x150a030602030405010e1501050612180a03031b030b060726031906062f0a0203070b0c0105131a1803030f0f0a14011401020304030804060314151e 64
    0x303049820403107040b03400780e5440141411840f03080201030660020300310040d40640c1054040340003030040d08400a038091225020696012001c80c4110400340000c044412400c4142002400781044244142f00c001613020310002c05486401800e00022000c1c0581e072424030030f9a6455801401008030020001d0503115284007403030070000460160707104102e0300a54a400100090841e00154044014011084070074841e65803102c00b201081c03245c1042085000380e503002040d08150440500030341c980500300d0046003480c3c4103405072603c440640000c001d2a070354103d83c03d0041b49249005442c50056100955820f0001408130368032030700190155101c0000350816603c0c50304161141d80403040614208801c2c0c04210543c0da41c081a10340c81481400d81000c0041c0500380103014501c50404c1103840c0003e81d9000300210780040d0343c4040c1e01941c41c0d075079110040013445541120a00c20f280900480c1900b01d03465101040301c000202003111200c030304000411202c2c070150719181c1104d42c0c600803 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 700820674 1250 700819424 700819433
    0x1081308130906050a050609091501030e240603010612170409050c0901020606031603030e031507050c070b070321110d0903110d021207050304030b07091418150a03 72
    0x4200081240700000f00300ba40c00c120800008085503004070340100310074000d20950340c0d5a0503a203900702c070345144012002034040c0c0049000c1d103151111400144038503007240400311a036400c2c000009100c3c0000d01d4075074440804060a0b80e0f618400c076203010300460241404141140c035441030b00084040f119240965800d8031906450302100c41124410020a441c1c078039580601c1001c1d4400002c138003034602c685020025812000c03450001804002050180c0e646945040015855009000c5021002882d150000414035401802820701c0c600500c2e000090001c1d115040c0d505542d03140d15400e907482041e80c1c42c520080401b05512051070f0702d40741c2c00d00030004070320000c1c040c9402000c000b1a840c15642005001821000c80145080d80f282c204000d240780d01051807030320003259403103044d9610040e05281d0300e18040ca410150079039140d0018020141c1c2c00c40d0707002044803a20303008242039241040821415051107014180b803000c001c000034041c0515540c02445481000300610b82e56078980d150b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 700821924 1250 700820674 700820707
    0x8120405130b3a02060d0b01030209090a05100803040e0a0203090a0f15060e0c0a20030a0309020a06020a03021015121a06030303040309060804030e031504170901081308 74
    0x11071045550040d103c1010450401070b00c0c04a24031801c86a050003800e6010520314800c0c07482201545643e07040c6084545c0c4660111403440600411141e914100b01c5001002042c0940340a18103081c00c000c00070b038110011003540c04851510b040755102d0395a40d50290041e50004002119030f00076038010345c0004030500402c4180900170341c10902d100407203000f21401c4601e90b4001e500d44540d105c0820071000c2d5040c003207561051091400d103110301c440c6080c5021003d488000c041c030901001c16640c1006905901000400303000f100c482403002c0e920501030b42c0310141e0a1002d00103802a071001a0100010b4004000b40e0904021900d01686e0702c45048200c2100410101d034912030941040003540c4e811003c00382c0001c01103000d1032560400380d402514995151060005204c0410009002e1500844180c07240c18005170581e4100054123050880b400d038101d400310390300c14004805844021810065582001041e1030700e040d1a140c0c003010a011011004040320340590810100380100c1c0707140c8 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 700823174 1250 700821924 700821949
    0x70509071b030c050a0b040c0f0f050609010203040e16020111090d0b0402030f100f1508100f06030803070c020103110c0d14040306150305070e0420030f010203130c08120405130b 78
    0x91100400e060510b040d188d81902c5a11980244401c0d81007413000c844106821402c943c4101c4026940300f01d0140145d05500441c0e100d20f03412480003081011100a200f4034442a502c0740d0b0003040f2103500200d040300f450103507060440d0040700244000c8009220280d0f02600300b030004080b0789410b140d40c00410320348401d207050500c042e6141d0991203031005150081c00118421032108034005030403c03902580d2071101c214118034190711500800500c1400d9400130014540101d00b10b50740e0710300003101602d400c108003030807800680350041091004500e0b80070340c0c9020940303102030940690300c468100c0e403200729035242007030600c401c20000001981071310500903200e21400030032600070303c0d605050b41824000c1c1e02901541c000c0004010001e5001400355103a01d808041100402d035100c00481d01e003550300403800703a0b03d41c4004141320308204000c0c0d41c181001d1280f07042840180d1500380c12070300d0714070171555016800d000340b1060129282c1403198143d106441c1e200021340006400004103003050740d4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 700824424 1250 700823174 700823183
    0x5010f051801050114030a03120b0d0c050f0a031e0302100e010b09010e0712020a0512070320040b04050105090d060c121b1e03061206020309070509071b030c050a 71
    0x1007189440c0400e0198a00402580000440c0280b41a000c2622003851400050800400195546900255a02540440d0400352861000222038070b0f100141e15454040c56100c0e0805440400080c03912040e814240c0343d00504603400c0c091700d6400c100c10700e0481042203055010720b024081c1c0500f294880d400b1808092000410001021010b01c03044100c1a0400500309102104100e03080ea000703111041c0020b00345500582d203910040c01240d041c0100340d4000780741d01901090046c002c1d419013001030392000d042c40b840003803503a207240c04030180324503c070740702343c1072340a201c104425070140e400340c038440d074001d0300d43c0240100700d0361100211103103080a01e001c0303102aa15200103500c54481c402500b03414800303082c10f84a0200d40513141d80e07445041440c440c070240c2c02e079500d40c0b4840c0c0c21800042c09400c1c0c0e1a40e0b40107880c90030002a40045030050714910807034200065a181a5a4080c01403c0d26203d0900c250009e03643d1850307041c8500000e80600c5041b50603500026001c1041d4003035039026 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 700825674 1250 700824424 700824451
    0x20409050a1106070b131a070206070206010f0e16050f120403080601090320040e07080f0c0402190c020402090a1404050105010e030c0103020c0705370f1205010f05 72
    0x2510300720b002c1eaa024400c1d40c2c0180c806000c0b20001034800c18003107802800640300361071a41da151401e190385010611541d0319031603804c0c040c000501d0700020f410303001c1c448039000e55050b44c0e218038180c0c0c054000c52040030380504e4100301245a07a120b10481c11883c00c83d925000e0302d8408551500f2145a00c280c01c15140f503407200d0b00700404c0c10f03030150145030010b20034a1318a07696031441c0c89441b07950b140d0030703029510000304504000041c3d8440d8411151040c540089d0740a07640d80c0c041d000e440c3c08850043c0515030080c0448140240382c0381c8200c1c0d0000c851000350f9940c900b840701007141d0b044800c1304201d8009908000444e42a42d440c1403202c0100174822042d0403c0f1410010b000541e601a40614144926400d2070041e0b580e001c681019075540030701e001600c03020800340d680d1402c9069846250002c2054003414440c5800c0d07000001c5820740904450003c003100403280342c6003000c520441041c0d041015043c01002006141c02100a02950000c85c000c038001484100b1a00240c43c90350001d4003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 700826924 1250 700825674 700825693
    0x150c040b1b060a0510090b03010e0706180e01030c061101090501110d0f151e05040e0c010207080609030f09040b1009090b0301050408120417071b090c0c03031802040905 74
    0x2400c211065200d4007401040c03049060211403c4805c10041c05010801d40d103561550303909803802d510501c5044080c0701111a0f040d44c03004040e000c0382d0300304480486280034420100d40c441ea050704130341c106da0340710b448006100d1410004807164440500240303129501c07590347e640481c03802d0165205209842e940d2603601c0d00c0b9480c503002291601e4088083c0320341040312110b0310131100c40710f40701180c1ca4150f61940d05003060402c0948a4015001540e00038500031101c0e1a14a0000d031000788000c4c280c08a4583c181c1351500d4994444040341c840e1515881003004c402c0058450001d044c070150082c0c808200d50319504006843c52404402041c0021076a600030840c0100c10b0140f8440c440040d0000c02550409445a052520a1300c20100300240c1d91800704e0f007040a204690007041410800558540c0d265260003040201c0e440140d400742200640c0101d0380041622032003003911011380b50000040f06c195003d40280807940011028440c91150070000740c0c446005030240a40b284016049901 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 700828174 1250 700826924 700826977
    0x2190e071d01020109031706060409020d0b1801030c2c0702100f02070c0311030f1f06270914012a081306020c010f020703030e010507050a02150c040b 66
    0x10481c0418116070500c0e91010220b9000540c605140a01002c2c05a50303954010110395244105d40c06200b40500c0020003801c282500e80c441d0340482c1c81181d0314600c129241b06102c182c41400e000260684401c170360200401e08240c03d4200c5244402040c1c0802c04d2a227100004c03842c0001c03680c210150300003c0078807036194410f1144c2c0c41010400c100840c01d00c00030703450f450001d0441d40001020007020490780c40301c59a0030044418982c5601084500c0b10303030800100d40f56a88040c1805010505001c0049a1b24000004034282c210701c00e910001581819658807010f4034041405940390726020502c1c4103600c800380aa200040d481080040c5100034003402e0044015511071910200403440003031010007440000b106501c10380041c005a12030100b030104500400c522882c6039245880007582504060701608100d40d035082c594000c210300c0c1c3d5140c0d0280c480f48181c1040000503000072640340203000c50030000541000201344501c2c1070541721f4440303e140c1d03840202d49502c0c400ca00d03900c2c0c0d81c0c00c6 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 700829424 1250 700828174 700828217
    0x3020c03070602120f130506031006090f0e0601030f0b030601171006060530040f12030905100c140406020304081b0d110621060a06030e0a02190e07 65
    0x108581d00c0100703804c95942c000750703d26008500104150790700000d86035070b8480c0440e00b618060300d401040c40341c1d00e0401c1052155115014821000458035464000a50440c0c00c0801011191007102d14220399565000460050084106815100390761703181002d1192010410b540c00b0302074480ac01100d40b0003403c200c502e0301034610744c3c0014250500c002031100e41d0740402130721000300c01c0580c070440b10f9031040c4848444040c51039425010608a0301040240098400c00d00d040038001c501d20404030305c1c030050803400e4954595010380741e0380c0a044061a600c0241d03208544603009494205c05050711546903003510ba12a500a0005a04c00716080c041441c09100e01341c6403c1d13010740c3e03652400707040b200460f00720b0380800f0780580070925007103846600b92183c60031590751144504155a000c2c001112082280340152341640c0103400d40c03c004502280640314807842c560302c0d28000c00700014940d01b0400c00c00c0721241c091903042d414507030010b111034400b4401c0d80910040c1c0c0f40d51441c0142c2e05e1040014 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 700830674 1250 700829424 700829429
    0x9020928060e033c01050f10060201200f04030b090a0b0f090c01050d020c030d1b021204122301050a140408070605180f031903090203030417011803020c0307 69
    0x41e400460348416030524501314071581101c550b202c2e40d1004035150f40d0016008502c0e858000d02d5081804111215002102c801e10610381064111852a25960100d089450b61802c0301c0d20303d40b03a810206c02107050310003d41000b2034164240d0345800e849580d9843c00c0341054840120b0396006102560810100c1d4000c03990065000c8240c0d0141d140c80c00e407107079039005040300340c50500c040040d4080f52443d403601128211080642140d545256102e011001005c10700200c510145201c0250401c0d0352002c1411001c150180505c41e0070a0b08003501ca031510b811503402142c0c80642c0031125640a03800701802e0b62a003110000025080c904118000182c4585507101856420386608200002d0308001c16511010b810640c0000c4960320180c41c50b0b0509074510540c0b900e441840b8105103481c500000030200c00f11185105900070f580341406500f60f50b484900258190814801400700784000d80000448040480021130a096208840d030101c5000803001d400581261444104e00e00b01008190300 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 700831924 1250 700830674 700830679
    0x10181505030f030d0e190b09011b05041424070b07020307170c01111c1109010e01110109080d0f0b0d051c050d140f130c09020928060e 59
    0x34880b600e0680103032203125400c01c03592916642d001c24810300300c003001051180458410210040c20b030b2400d201002c07a104441c40700d815820080300c20b125000294042c0c2e00c050381a101d9a0605082420300310300304200014164020411681420b4403410780d40c96904003040a14000b950342115050130110580c0c02480ca60540d4002c10060307001440303c410400902c50141560f81d12b540640440501400540c0b4194034100342c04a040c2080b00034948251008140c505d00c100a20003420031494114010070142c103002c6032051151500c41d501807190000615400c01c000a4000550342e01d452131600301061a0028660314003094060a0942c030074107425207400c0760701e808020707044d0b903c182e03407035050710300c450700000514089542031405141590410a03840005100c1c03499041c0001103994400c44560502d581c040021983e070074a003814504126401144c107402490620703c80304c01941c0600010354003d5004c030003050001c010589140d00c0c124071a01800c01032494100002c1401c20981c1c1c0d21407 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 700833174 1250 700831924 700831933
    0x50705030f07050a02030d0509030c0301060e060103051f121707020904080a02031b03071b12061107050d020709050a0e03160206070c08010e10020a0203121018150503 73
    0x4046200002074420071030200200035035540580c075089040030b80e9440000e4051141c070f018007401c280c21030060440b083c02a8210764083c2c3c007990401d030030b0782c8040c42100c0480000c88045025944280c11a9501c1616035061704001d000c4050301c0e036001c0550b503100352202c2c1e903100640c0041105010102d1140d0840c41005130400300c061300064041034020b80028500b84000801c46007050081c401c0e60000c0c0302e4a803e0b94264030b41c0f00d901c65140d0b800900e08580c0080840e803400392048031548681d0990310308007422901c6100e00d59801004000c1d080c40e03030b41e0004040c003040000620030800c120412403658081c124861408094200b0380341c0140042c2e040301d061100100c1020300020075142060b000000c185102c15190010440034811020060102d49518a020410b40415008180d982c0c11100881d100c4074018500340080740194034120300180c20400c07020603040c2c14246400e4012103130b40c170802142c59443d035a6004501c07100407440c0fa403035241c00c202c2900a000d041848001c2c40d0680140c07 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 700834424 1250 700833174 700833187
    0xb0414041704030f0f05060f22050709090605040b01091b030b1c0f151b08041502030c0309060109051509040c090614030615010203091e0913120e0a141314061005 71
    0x96000410810701019540142e149c481801010030144008001c000d0003000881c200d41005000b40c107045405445140042c00000707101c824601c1050000001c0e042c10302c5510007184c1e0228043d0400304905680102071441e011390000303010065044c024400c039110600711240d850728408010760b80241d00c2c20325203404019200c0002e2580e003407008a4151a09004030354907407070700b028030005032040100082e10100803c00440c0e40c3c0c2e40154000c030043d00c02c032121a0398950390358040d501c0071160701c80002440c1800304801c0c10500c0d03546800078811140b400ca80340d252a003090840300079600c0303040038440307007040307026641410b000340c6400918554400c16441d5034040003130b50303e118170381c7c2d224040c2d83c1a170700046c4200c1100700d0904c02900b00414884450600c54040164512114425515102e21101011a80e4011000c40714030b618003502e00c0049c0d502e00186000c00e80442000103400c1800c511528004c403505108251000311074407852020303414540180400c4244900611080c484100302a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 700835674 1250 700834424 700834441
    0x20607090807090c0512010602150c18060a0320040f080303061818010c0c0201030506011106060f03030d02031e0903120f0711010207030801090b0414041704030f0f05060f 75
    0x22030640398a0203000c070313050648050890b6140704074200300141c204804c0c001b240341c660101d142814940303201c0c10401c140e02c540701986600d215041c00f6061250042c000015a0f0420a0140a40c000f150030f0004a480c2480201001500321024040162100103814081d5280f80c100443c00350103050000e60561828130003003500300352071600d8141c42111030400a12860244245006c40310440d0009104c00c80c800304000c0c201282451089001c00d080000080547d48541d10b00500e00031211f00030901070729140203001d082d05400c1185a0503010070440a000c8060600055005070380d130508590b00f4140081032001d100c0c80184c8000200c1e081000380701c2c8000006548590046402400c1e80c00c20b4a41c804181c491a1452440c3d485c6035002003036001c14581c00980d80760498200b008180442e28070a000c00040f031345031182a0345000403034800301d40400e04414a10010001d20341c0b11034901034076071715a01d5014840e100100d070064040352100b42004030911071a81c001003614075194444c102050b4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 700836924 1250 700835674 700835683
    0x130b0117060d021c060c11030d05100f0b0d0b01080f150a03150c0f1b0f0c030605010b0a12090b0106181e1e1a13030b15010206070908 59
    0x3542101906280c049a21035840320402d24100380d00a01c5800c0c10728298808140c0b8242818081d07451900c0c00303528107441405815185441e0500c0c8001c0c5246c0242c01051038001c05025103004514425200f0100701240515a844040e000450002d40c0718064422a034061780c003522001d40c1041b81a405008401e031003d607040350030140009201510031040c1011400340f2200d0341c40580301900c11014000c404d05654461081e500081c4e6410b40e10700241001070b40c41c0202888c0f0440054050018180810140c0a000c0c2e2007a11440405040a58030b0300c0e08000d0328020380041c0c0303103101e000032001040c45d0095507520040748400c00a2040031183e84482c070411b20140314001c14002c620f0300030b00e9a03940100b01c09020b480502e51081c0b004108400d0720501c4003250003004252a246e41780814a9000030414a0445c0c0340d0000c0b801d64003080444940e010b801542c2c00c1540140e41030b07400710000d290b104041d4442c0d26480740d91040080a01c00091808002800710001d2005181043c0103c013004503 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 700838174 1250 700836924 700836947
    0x911120c040608270a03050a0e0907080c090604031202070819020603010302060d0207060501030b011e210804150c0614061f050c250f0e01062615130b01 67
    0x11800e4440e044c001141d070441c0c0c156032a81e01c0f5000c0c00e8150b80800d0382000c054994040300356500242040b00a09001244600b550900040740721280090000d00b21440103003490503005d814182882d80d20f5a031003122450300543d11707001da00301180a01025600700940c4100d60340702001d1007209900ca8001c5040d500c8180170180c014400050389581d42585601103818180d44544100100d60352070030112403180307007030041c61191482088200d40b201b409410407001d54421021107801088180100c0e40448104501259103c0f810b00c0005140020411000705444540c0c444d49144020703840d2440459654811040c0e4510707411041c451551660409020212040c0480c00800380641500343d8240c02440d105100c140300b51081c00788842070703840c88100c3d100c15070303035011039405c0e1100d0002d814039815014404c0c03800300401c01001507510900041510780b60404c004a41070036220100c912002085030240e001d09040c0904aa01f41000c07460440e10303400c203a108100510b001c0000030701e50300411 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 700839424 1250 700838174 700838191
    0x30c0b090402120a0902030d020f1510030b1501080601050f03060907050d0216060e010203010501022104090f0c110c0102100b040b0a0303081009060506070305130911120c040608 78
    0x11516009907203655044941800301c8200c05242c901d00700a4034405032141d00804c034002d014140e1481c1401e80006484105031058070042d01c0482103081d010a0a503000400d03140c840c1071910400004070f841d803100356001300d8a010740348664083c610005000710a014180314100007041010840c1c0507000400d80c0e400400c111810761a54554490881c1c080c050b00140300c1c2d41e1440042d0880c1310b41c0107941c8106000d48528000d00240248101e01400c07400244602405600442601c2d403400c3c904040c03044184414009403800c040c2c58400c408200d40d800c00c0d0000200d40d40303104207000c00f5084289100145280d03401802110319a20001f9110707030015808100141d00ca101b44951a80c403500b0581c08600042d0503d1600d5903a804c0080c000d0303509654808040c000d5900126054129000b418262a0301603d21407420a20750340446a40e400305003410150803044101041120090290300003140c038100d1082c1e10350741095201c400c021006042405450700802c0204115508810184e0f8400d210 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 700840674 1250 700839424 700839427
    0xa0b070815031212060609030616211a0307140103020a030f111209010207030206060105070201110f0606150316140d1404110d0f1401180605010801110301030c0b 71
    0x66100c110200304120340480c1c0d06004900d00002e02c048100b025080410b603030040c04e00300f038841d0003e1207414070542d40740a030140c0225000134104420420f202c00c80c85958900801c0d40d03c94400400c5601503050800340d1010344818407036900399460081d4402401040300a003040da441e201045910000b6030b045070381410f03004503000a505000e039100440f03401000c1300510400030061903410990740326100d140400740018000c42c4068605200b45d5280c19890740060095868280054500d50071040c001c90400c10740c44c0c002210240d05000010080c070304003000b8140c504018013040840e00c1e00d20442140c1c16028010807d54890003d030007070710307035415040c4400102c416101c0580184030712100f81c0a09402c1006082c5240149419648180d019080d429003101d5080c08200e00000c1c0c0080151041c1121900d00c030200f00705071020311141d03100100008040f4104c0300340d41030404a6400a980315580e80004120407442801850405094903103502d29560441d0b50b86841c02c45680110007800c00b0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 700841924 1250 700840674 700840681
    0x10306051306060905010812071e1509050109020f0d0c050f0a1d0406150e0604151d0f0615071b260d08010b1806070204090b180a0b0708 60
    0x7401600414903a04620706011460b110b0300342d000a40000c1c42103a1842c40b98092065951100d201036400881c1d00ca9409079182480521110303040940707040503151aa030080a010740071586115411990303101e500080340780d902038010005d0162040c9409809007001c1209400006d50708104401950001c684100072018000e011400604440e005141d41400d142210802d44aa9500162207248201c0049c80b5204201c0150320300140e00b4071901240545040c0407403100c1c40c254000d203031420300c02d00e5608070365580c1354070503081d804031403200050607001c4e0380c28040c41140c4002d02c140c1c81034083d100d031800341c0c081e440303201000d00c0b405030007034119420b1003182814011140000402001600446011074203040c105c564490740c4004001c010f40f150041e00201c2c0d07030103051024120b80712840028200004151075402000d4410107959000c0c00403c0080c00603900d070b224040c120b0307004950580d164170700000000115201040034400d254461071072400054001d1352920b030300c40c0c44d51400300d400e0385 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 700843174 1250 700841924 700841941
    0xa0f0e10091515150c081605160b040f0e0708010e130c060908240a020706020f030c0702030d0219030302070302190501020a1821020613080102040603060e0f01030605 73
    0x1103080b450191908020b540031600c00111914000e40d80002c6040c24807107000351081e188140b90403001091085c09101c4401815144110742d042c8a018406599100c004034104841106540d0030031b00d02c514000c1000d0207080360035040c49014180e280c01d01100e07420080c00250148405116081038004070b000018800701a0075009034180764003041c0750400a869040160002456001d0358585102d05618003056410700003000c0494901c0e40b01a0880ba1034044209001c0d6014480c2680c80f15000c0000c02903e110a1005510400703911241e142c43d130801e44101802c0040c100b60310411540903184c4804004580360301001155490300b0010703501d0361585401d90400c0c01a00e000070b0325994001010045c80419001000740200540c0e54007001c003c20103d40010103c1d0b406540d6140007603842040c03600003c152800103050004043c58203046034480715610704000c0340c1044c1f5469401180401c0001d030035000310b502034482c410300041189060715800203511030501c000b03000c0b03a403141c001c01d0554 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 700844424 1250 700843174 700843193
    0xc120405030a170f0d0203161b14150a05040c0b03010602032a01141501090b091002010b09040309031209031e0c1a180111060c09061306080a0f0e1009 66
    0x7010010380c3c2511091031290500003500108d51104a0b0740301c4614a480d6244a00c003200340c2c8180c0c044044400c3c205170b4490540340000866441c2c0544904840b413046070302e544240a10400c40148045014900703031526141c4d540040e407124500c3d040034401803201c1354000c010341c2e60492682c0c01d611490032100c446002e90441003980c2211551a00480c0c00c96400030440305486840032282c4003030544074110044540d121144103402200034103014100485c9070100380009964228070011402c480010000303000d540c41070320200c02081004508004008020507100c0410401b410800c540034519110040380e1a030300b1440310f2001e6070098884040059a00301800980400071a02050107068040480964050030807021400d000060890b1150b10509a01c12035103400c0014161039295080a044140c0040351104c1c2d100000748014043c0f900c000c10014000c0c280760b510340741c0ba404c010200d40200d92a007a11a202c1d00e05060000d011540c0000d1243c040340a81100005c00c01e240b810407103100d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 700845674 1250 700844424 700844437
    0x3010b040e010c110c060d0f020d1404060c0201060f090b0d06060b090306060a0302100809250918030905010f0c0c0e01030b1e07030921050c120405030a17 68
    0x11901d45000c0c86814801544100a082e0807030303c50445100340301c0465555a112121841d502100c200070302000d59485070010b031100c400c0c40b0005400c2414400400382039a140070880481c02d0070600400007404241d02500340b011100b80001c0069030300780801c1c0c81139800e480c000c0d0340001d41c44a07410011611360324406520750b5048101004069200c422044450340601c001071f100b44100000316046203006a4540f089941c000c0c1550f0804444c2001560340d43c0e80202001001d0296469541e001c0e0b040700c404111032001b00c506401603c0c20007440307108070781e503411003050101500504280041c1e001000e190a03504242003813072401c001580c0032510756206000050142031106400140031012100c2d0768140c9100e0b004460302035881c980d856415101c0d06209100c244059408262410b001e64400c8a5040c020181540b03041005462985c0483e50b20345030000290001800d030b1083c070b006201c8840341c1160548a20302d0030303251500180e034550398658060080d108030045081004140e41c01c0700d04 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 700846924 1250 700845674 700845679
    0x6010801171623010207050f0d080415030209120f060a0f02090d120806091e04030504030503030412030e120706022217010c08040f0b0619090603140601031e0203010b 73
    0x41c040e00e8050b504015401a11040c3e42c29980810321400c0398004a542000c1c0c50026002e0045000b0769402c006a100c60b844065807581007c20003c624912a40c1201c2600f0016403005607458020340140b12006d1b20200741408070f40c000c4505140907040100e1225002030030100c001c62650f040c050f20704001d1144e070f10400d5101c0f0040c041c01c410400d080d100412604190f44036403c1c075964035800e000c4d8001089560300042a4402030004441220501d1984c000b400380c54034504154499541c540740d540700380d50948aa1100d0003550585503030600881d02d038021400084c06058030211080f04050044d00401000719401080c81c1e085901e01c90017004140d2501003003030750300d80d680d4103044100f10a007510b0f0896550800c0140e41d5010b001b1341c0303d58081c543c03246100040382c1890f25013101c1d041d4080c0096034441502a0340307014041c1031002d0303040078107000d85002620626614224071000e00004c504121900814010000328003001c09116492506101c065000d0764103100003401402a0f40d406035 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 700848174 1250 700846924 700846963
    0x303150303020a0b01090c080403050f16030e0406081c1214011205010b010318061e02030109020d0b0d050d0f140a080106021e0d05071104020f0715050601080117 71
    0x81407580c0003030548041e83c0207044480d41a40c80e480448183c901400d00f000c045141c61003c100000d200da0002c00c1c281036040b00f42c034144001203000094a08421700c0640002d90a8039040e01d0f01d150030701c6008004c2100c0c0000b01300405084c190021004030441c02075051000c030103c5c40081d01001d402800d0080c049a44003205580c59a80c0c0a018070324102054a0750340c1313814501200c5501032300c901c8400c01003440742950820016624080540041d0010b0708039204c0c0381d070248184124a001860103044550405600c2d200c065002e00d0885580c0b05502d0310940d80b46000102207a000302d1211801a100c0c5081132102c102c01c02c0580b4100c005d075400403a41c80c0001a048015035004c20032606807240356081d1121088041c035441c83c03400407404520003982007503201051300e90080c0001e1450a205580d00c1c4000070707405001408030f0304280341036a040600011031a0400121407102e040b03c0303000344003c001c2d030304149000070322100703050150100700400520040b0408404005043d0040c00005a20 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 700849424 1250 700848174 700848179
    0xc0c04050c031f0302180405160803091311040e090708030d0605120d3f060306050f1303081b0a020d0206181203100b030c032202030c0d030315 63
    0x36850366104442c3ca0001d51001402114200c4040003d64200c2e82c005000500d102001244403a40e0740740507100312500d104030282a246078145c1c5030040010f010900245d40c0360b9440c2400e004540d14410b0350000558540000c40c800d40c40c40e04180d030151850440c032000b1581d560341001e441c01415401400c4a0301c404914003c500c41c0e1a00300c2825a20141e03540d500e9180000e9500d940c0e02c840070605008204950412004034112580881e100010310104000303240e0754000380d42d10105080700100240740c56044c00e0003031281d83d0081c140c0181060581b440c552408080384207140201c0c00c80101088034100110354185c54075105113087c000900d241d16a591005070000e0742d650704201001026000303400c000303000c03408499040c0085007400301c0501082c550403207088401e2742c0001c05e0035140c51400000414103481c518090b601c03601c0441030301d50b0740e801c010a04802c841011042000d00148440c01600140c42c0420039066580080d51200f0540b84c0c145029000b402044080000c1c140900100 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 700850674 1250 700849424 700849441
    0x130305120d060902040e0703090c05060d20040b12060d02040f05090c1c0623040312050615160201031e0c120504050606060304050f0303190b010207030213020c0c0405 73
    0x1c0c003441c00030500c1080819540d04000003a8004d03813113101080800d030400030740202e0003138010b0f0034420700c62004101d5050300c4600184070b07a004140304c2c0301031955810035100207107105940000f000000c0c2c00b500c1d06040ca050b54040c4240307d02d0240180c542c1d81640441c030151111100742d800607034003c00c18000041809180c0c5c0042c58100c0d03214150380b15840180341d02e8102100c1000e01c600c2603403403c0d070200c1d10b542c6406029007400e44100e0b0265604c0c401c61650038881200c0310340290300c40d50f80c819a14416000800940c1e6014000610403c50080e041864000c100c08644103068107142c5007100190720b000580c000c2003035044a054107040e4041e00428050300703a22010150310745884010b640b034a081c1001003191070850b0010919804400490401c7c60818050b50f401032050086920320403030090528110780003030703c0ca24000c0e4501e0100740780b003000601484081d22020310041005901d5500000c12107110b5410400c1001c1d4000b9100907065000e0207188081c88001e801441181458042c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 700851924 1250 700850674 700850677
    0xa12020d0912030507050d1505031b100503060303040e0c07020312030a0606050705030703051b01060e15090702060f07030b09090a111206011503090f0c0305070602030405031213030512 81
    0x1e044480e1402040324a81d5180030f80724990080d0003a941c5c050501d1b021980460003407401029041c4071a1880c8000290340d50300300f1103054080c0308051881c40e8444400706010a0744517000904007400014010001903440000559003160081e80005905445888034440c4622a030400603416014201d16003441070f80103002103010340144d0104021031941d0f12002c503860700400070014141d402c00c00180020174440c130041e04601e03000c0301d030248071340d01d00c19042401c543d2580c0c084a0031440110800040342c5030000c9d005115903090b200e41009140100e0000c0d220f61000702003140d0079010002003062117100358040c0c4030310301014000d20400d0828000c03060303840341040c00440c0c6600b10706ca11803815003002d104180080f0840b10052800c2e9090240040e8640030184204082598615006000c14030100401c43c0701c60160003004002411030400b1400d01d42103400c00c40c2954420041003055445c00a28080e8038011400f1090300d5080030342c90b0b03d51404a03030b030010301584a00714102860050000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 700853174 1250 700851924 700851941
    0x4180b160509060702060d0b0a1503052401200307030206180703020109061d100f0809160e0903130b1c09081602040b0406060e24030403050a12020d 65
    0x8400c40040000320003115207204140409070420340600400005003007800240250300c504c4040031030400f00b240c010908690842c0d0259901c409602200004550180300d55038218440c4500c003001000076010780440c9401102c411070400802c406580202006075009084403610718081d02d9039080303c0e090095030744505881e03603442818410070140d00c41d000044d201080301da042c0c40385142c0ca807510205981c1c002c0d0800003402d40c00038000402070b00d669032840d40e42c0c1011141e100c1132107103104e24000034411503000b0400c000e1030f44517502c01441912000150b01c1140c108024240c040d990341640ca6040d4014030200a400c4494018003244101040d0080c0c05180c0b04c4000d242c041180da25542810742c0d0510b0400360500d00104020141c1c4025240c2d030440183c00078001003852010030012501302c5445038400340001d04030a207a40c1d0b15280140180800c141903840c00c1e101c81d40c00041024031480054001028400d0000710004114001e190503110030101850854407000c0342c00342607000d000103c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 700854424 1250 700853174 700853191
    0x203010509070302030a20031c180f122108160f0813080702030d0918050408090d03090305010501081501090e060a02090301092414041a0604180b 64
    0x210026901c0c80c4000754180480340c0040090210b080680c6901d203040c50950a2440e440b07603520708800d1b46807410410811510351001e44038180300d00c00600200300c010f148103402d100c00001c0f1010801c251507446142c1c01e8135400c5034020b015504516140d080c0b144e000404070751068600202455841d08030016074440c3c49c42010025920040e8041119034220144030b40300840d0098012540d031810460405210503c9020741074039240107034000928100400ca20324000540c0000d0910070580002d0b580c402e40465008184910700701540e500c6030b1030044802c018001c400203502402898414100b2100840c1c221008201558441c2042510340c0c4030340300c0701019081418000107000cc40c0e80308800e85c807480d200103012603840c0c1e100c60300042d41c08016038035819074072141307410b02013032800c2d00c281d00c075171050314184039007841c0800c41000341d0710010030150201d410001040041840d00c42603001c0c3c614084c2004886a5031040002c0081075035503802060000214640c408010061401d40d0085120 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 700855674 1250 700854424 700854431
    0x40e13061b050a0e060c01020d0c0e0a081011090a03050307050c01080717040c18020306030106090207030212090414150a050a05030309060d0b040905030d0c020a032109080a0c020301 80
    0x70760720003803016031a044800000070002c102081d00b41d44121022070452100800080c030300540310b13220750f080e80c01c50400041c06e681e85445101d4403580043c0801031040055400d450040c0c039007083c0645131720103030b03a4000c0001d84070030300c1d040d5071540c0508039400c1010091404200981700c1c01e016a49801280040343d151007101c06034045903014100399841441769a80f0740e01010341a00d44805194000f0748116607c120602022070070a00c0300e0186002d1804d00c410041c0c981c80e00b60300309400d680d20303a884005401c0c0b040201002083e4045414140c14030403580c8940e42d50789030b50200300100070440d00440c0441034603050000d401408100d688900000700c0d0300c0d0070131035119010800c104a01c0c1c400c05a26038010000d00d07026003010405002e0b482c5404800141180d10b15011a042c5d918481040b1007c0d08005601c0542c40d1603403040682d407030503520080030a11100d66000d000309070310b440302c001200001c14007800315038101d400ca0320300c0982c80320055468140e4a03801804010034840220310a50a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 700856924 1250 700855674 700855691
    0x207140703060501140603040231090c2405030c1201030803070e0306010e06102307032d11010b0a0f09140906040305220617061e060f040e1306 63
    0x80c00d0502e80170460010001851030b112607080151250a03183d84044d11701d103070308515103420780c494890115134403119400701e403c1c1402c0c54000321210640e0000c01d0814034180f018040354800a404990310226070415942c1ca0b110380c568005240960b8182801ca02c0d00c103800032041007140380107180a00c487d601e4060b44901100101610b900003405061001007104000410030f02d09204400c2c50142c603410404075503118040e40300d00102c0602244408a030001a4440c10198051030340315052510f02c603c0b410384d40c0c11070140300000c04603030800410171007044165400481d080d888040104401080d007001c2c40e64495050402411500c191180c89103400b00d884070560307800003080c2c8181c2d000070180213180e640340d5007916190480c00d68442e94020013840200382c140c20800c1a80980710945500048130016000d5185100300184900d010b01180a1076a05200000c8a41f801c106001c50316036032a00e06c41c00d00e0040074000c40d0300c40740d906003421050000540241d03440f081e03030a00880041c003104d00d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 700858174 1250 700856924 700856939
    0x5040b04320f04110903070312141206130f050a0603030f020c0d1401060e0a02070501050a0603050c041a030d12060614040b0a03180302010c02070512030a080a0207140703060501 78
    0x70a0907400540004070600360181078a02030340f21501d59004124030604164170440032030f1500c402d07a041103c05445680a540101750001010b220721a00300c0c402c6460480020107883d50b40700080d052502514035859100b203a89016000500740301e40705c2c402000030b072805010440c050700488c84182c02050100c00c60380445071000ca800600540042d03d90301c0a07440584e26a8108084250820140d559819000c01c02102c540c600c540602c50484002d1b07110100b41c1042ea0840c0c1c0702400e0340e002c9520700300c0100700080000c5110000b1240803100014004000c50954210b4011980e0103070f0f042c00b8628800040c1508048a2031850b5011242001420344072401522210502411201c2d115002d0000300308401d01200103040003c0c0c280340c045440b40309001340d407000001004044015175100c0416103149503040210900414003240d07000e400d1030300b28001580324400c02d100002000041c000060550348107070101c44403541d0140c01c6d402c8200751503107e151104882d0004940544c00d1000009009 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 700859424 1250 700858174 700858259
    0x1c0c0c021f0e09101e0e091b0a1202130e010e0a1b050102060c0c0a05120c010524040b01030e0f06010e0903090a0608040501140f090d110601090b0105040b04 69
    0x458116040400b41c42c00c00c0740c5a564004685c0174900c1146005030b020a00c000d02c01c070070380c0c0140804070082843d41c51280030074055000a402550242e4865601040a2503103909490010381e01503071030741a07080c000c3c1d5125001d0030241050807059801c044500d04091400280700c0f030010700545000706040060040806855911300c60680180d00c4a03021a20384100c80f802456064192030464141201179610581003c0a007892003541c0840032501d040101828001d00354400010004e42c655030940b4007030070361860711092100b0b005a658054180b2181d01a91001e81043d4100084031600403080310005e1742c03200d003400381c02c0c00e880e403040200740c81c0c03000041910b0200c01c0003851100c00d035003002c01c100c40811004000ba41e4545d203810a20315600d115940040c028a4200b003899024a44180380514003401c01c803084041092802c1070f601d00c1170300801c045041d1658000c000c035000c820180103c80074000c640144811090002c4d0010300f2900700702c0f00c3c1980d004001803101a8405128000880 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 700860674 1250 700859424 700859431
    0x5040b041b050c2a01030c031401030b1b030a02091f120911060304060606020f030a09140102010207050303090c0f09070507030e010315060815061c0c0c021f0e09 71
    0x50340800100200700e03001e04050002880300e01d040f5001141054400300c68045150b010f503820b1403e0880003001d55038103004050040600341010700c0264200070f8007840c030389014880905000880300110b803a844002e610342c1ea03a00700e48040c0395141d00b8400c000700c0007548a01c90241c03180b2000c1c448150b2000307103030303000c040e906450341c840000d64001c02c070002020704078102c0300325545411070b9842040da030744140c0a075000300d0040b80002009030400350040d01c0e01c3c000084841c0349074001e22541e0600c96001e44102c0a07259865841d040c1c03460320300c005074060b001c0e1500080c16400044108080290009109450380f001181c0c5031800c40c0c11442400881c102c25170b6020700150040090001007400740c11091441c000614002810752080340181d106000030740c010780c00040702e07841400001c1c401815050400b8138121480c0e450000c8081003501814081c8000f0890340e41c540441122081c011fa00c14088942c0150184545500704281140031a05c04001030307001c1104c0c4880e20b4410304121696620 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 700861924 1250 700860674 700860701
    0x6120a1502030c0702040606020c12011526010212040512041805060a0e011203110102040605090d050a0602040f080d140301051207170304062003040302010c02040b120705040b04 78
    0x82488610669002941c40208070f41541c203000c201110041c1c41da41703d0315000b48400d038042c0503800c015038104241d1040088922030941e05001d0340446000e549021541114150101c4410341000e4074000d40d0301490111101c0c50039440800c00e1005141a104070b288131303034482d80c15035100c50f80a9101c0000740c040e60241d451074160300c02c0c800c071240c4c006034401c03500101d004055007030f9a81ea030703030f15039500001c241c02894203184c00740103c8007015008603252840c2030005000b941468144074000b0907a001c1ca14140d4030070409030f0084010f000d0240702c0028511741084066544685070b400c2c01d41d00448510541205101c0d2814842400384a41c4540b0042d107a07038500c8620310f929107030400c1b102606040d0a00150f014005c0c0c0042e4854016082c40d0000294201843e01c0d98504900606048240781020754174081d4849242d4030ba400100466050780da090074170000c0d2404600210700103010f000050350b0000468480340400360000100f100840e50222000d0103002d203544144000e44101071034080703 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 700863174 1250 700861924 700861943
    0x3070e0112021c140d1b02092e08030a08090a030c080a020724020d0906020607140d0f06050310021c0903020f031207120c050919050a030b06120a 64
    0x801840c00da0201c51490304107001c02591014641c42d000b802544124600c4d83d01d5014040e071000840e0420071340310301c420540e0026945801c20f42c0208004420041110303544040d080c40f114203125441000e4070f902004031400e0146152140c40c0c5a5490b1301240c0800081000d0800207444054002020461070740d01d070f980c00c1c48081c00b40c3c0c0d415070305410000c1e4000550191038404540500c02031607000051a0f0380210040d80900c80f6406030034034004c100d03442c0c10015403e03010312109400084445d000308403450204148030742d501185410340038040000c614036042c65141c4800940c0d50300041c0035aa0114182d4500100000c113110032442005520750001d40c3c10380044060500e65401544403900030b0042c2c45003061300c03011550441d444a4030649912680405204030650b01c81c010111003448200100060300e44010094960300500c140c440c411b9000404907014061240c4134078004000147c00020000e0b102c0c942004444000c41312240540400100d1700071801d0002034140d0010b800c81c1108 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 700864424 1250 700863174 700863209
    0x200301110c032b110d0c0206010b1605070302120609070501030203091905010f050c071707031d0a15030e2515050c030d0e060603060f06010c03230903070e01 69
    0x20b500c080e02483c141c1c1d115003525049281e030303540c0b070090f0510140d125803401c0d6202a1811000103ca40034501c1c841154440307401030010411560486812071400c014110f101903980c03030030340e1030088160402508407100d0180c0d49200d05000403114000c02c83d0405403201c150703c440c011001c07070004481e03044182e4442007811100e40c50b1b41c000321200e6406040041284030023481c002c1c05440040d5040d4845a40006200e4103011a83c503203616901c40d40d4507030b189407a4041d203008101400b142040c0140e00c1051000103000d68640392082c004111079030003101250f0817480d015004003041601050117000300340500c1b800e810052201c080d913524a4007082d4943c2e0405510060f8001011740003c18002c08000300c0c0400003003080031b1300d20105030b0f0b040403800c61450105d003403c1aa020b040140250b00003030a2020722201d07007a04940c040801c1ca07100101590f2030404036a01040c1c00720340700b00828a049101c1203045110001c120204055040302c09490f07803035251a207020800d2046001c01d5120f101c11 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 700865674 1250 700864424 700864447
    0xe07030c0c02220e03160c060507020a0b0315030d0302130b03010b0409020c07091a18062101020909040507060f020a120e040b04020a022505090109050c07200301110c03 74
    0x1420405803e41c1000640a212884094039503445000000c15032180e1a02c4c1000300105100c1d85c502a04140c5001c5041c03454507408180380899a01030402c642802000080526601f0180707210403400c01000c0324403c3c0c40e4002d0141c02544025038030040b803180500042070740c400c000c0031641243d05004403145400c1c07604100307070000d402c004400041c80c0664a4005030305107190040c00f401042c41c03014440c00d60004400c00c1800701c5c00c03480294004d44070340304015560361900343e050f940c031444100e1440b00e10001c01e1054024801ca0003010b030f004055409000901900140d05415220039440301c02c005c0405050503a50b8aa11000c01040c60070061280444148101e1041e01c51100242002c00e8a00c50a070000c2c4c1607800c4584140b0040c0c3c000302c00008011102c0d1aa10181d85200f01403980c1d0a0401c00460500e41050080c1078800391a0004119000ba59400301c40da45078010351030245918907100c1c0c41184d000c091080c14441c2d03003000d60303000d400040c04046543d1424814001d500d000c8442c5003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 700866924 1250 700865674 700865719
    0xe03010b1e0609120703050d0f03060b07020f13060305010f0f0b030a060e070308040b0307030b01110a06020f070506070c15050f01120204240503011109030a1707020a0e07030c0c02 79
    0x50581c100070204c1c0e02c9a500001080500050341c401c10262100d01401a0014070800d41c1c1c9040408060901408004400c1c00001f05d4402076019503d82c081940000b000c2068041a1020244c0132458003100005100c03040d4031070083c80312000c009100940b1a00501010f0390b982c0a0100d62580041814000040341e07a40f00340c4a00515009480103180e480d2180c141541007503100c82481540041040210359061241046140702401e0218407118200140c9594011011000b403040707900241c03080c108036454060781d0540d40e11204954152904c48001424000407640484081000750f60800e00e0304800c0c0980e0740f08100503003108400340e02c3c00ca1103a0034403480c43d0081c0d030000d507a030448040f814040401a00181c55141e24450114070700000d040c2101c40100785100700d00000c0c13143c60320302c0e40d01144a805043d085040603000c0018120040c5c0c1034482c00c180294010456030b00012001403800e985440b03892207850402007420901030541f14a00c003d10b00940c800150604290741009810 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 700868174 1250 700866924 700866937
    0xf010b030c28090f02072604290a170c03061027030b190e0d140c03030703060311060c0d081801060f0306060602030a020601030f02040e0109030e03010b1e06 69
    0x4a0700b03040d0748031000000c44103038a40100e400c640006034482070103014082c028451030b0080c010300011000003003103d100e0140e40104e2a90196603907050740303500d0110311400c01c0640c0d0030840341d5803422260400b0f080c0c0341c1d40b0b158241c148a82c0c080012540400101500c1c40303044050480b00b403020410320125940000640242c40e4045510b0018070200f07003004040024600c11503c0144900b020105000e0454980000300c040905058511f402c0c1c0d080482d00440000c8075050034201058a86960b080c50702070401508450711010041020036a070540003070342128040d880302580481c140c0c00b481030703c0c441d83d50340b040ca81c0d0042d440b2010040c2304e05000b40e400502c1942c1845c865220300703441030075592140e01509440c03e044c50300344213002c60303442503100406090000307514240703015002039260181440003901d0b15542100c10300c21340d1520340006411150080017044000070700e14010f00019505507130f00d80070b9032801b1200c2049041c28103070720824088542d10700d42e4000a400401800b940800c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 700869424 1250 700868174 700868239
    0x50a0203040e130f3c0f020102070312021f060509190e0d050d0b0f090f0c211608071b08090603040503031f1401030e07170f010b030c 59
    0x60750340c0003181c0700214210781e003440384001c00170107204010b41d00012000c43c82290402080b80c0002841c0003803091004542c980e02000c6400340460900040c0e0422040750310260440c016011801c00043d404648401502c00b103003035032400090000302110480c1d160f0701499070400e61800c080340400001600003083d41c880e290000c64400d42405405050906248960340460000f04a4111484690044104425040e502c1040320307109180020707010140540070180100e0b20b400800c0740305c80400c00b02e0311030426001c0780301d4041140a01c42440103804840c5485081490010440882e1040d002d0600902c0ea0381c0c4d070324105524140740218018001e0f541124884010001d241141d25088080d46c4124000c801a5803240350000c0310a0300007458005d6400020000c6006102c010342c0001911041407080c030b400501a03601010b418907110160308803003c1101c0320b0010414202001803000d8101316440003d02c004005003050640c1e4040c00032080d540111006003104c60a41809402c50895192 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 700870674 1250 700869424 700869451
    0x30b0901090c08070801230601080903190c0201110106080706110304090e030702150301060203161b1e1d010306020f040e04030c02100c0f1b051c06050601050a0203040e 74
    0x50b5079444011041507110142a0704040010490035000f071150301500024010340640081880801454180004203010b05122040020918114040080d107510b5801000d42c4184140702c0300019008006981c0b0490024450724004404600180141d00c1123900200c020501603003824001d48442e20242508089032001b0701002901d80480d0041e0506046108007840e43c40c0b0303143c0140508041c810782ea804501c2d40410040182c03c1d8000308581001400c1e008807000e1080a141000c03440344c01240030041c1c0c4022000c04100402e07160340ca2903190300361560030307403100d51f4074000303400786203503a0fa02c41c51103150001c010001315440c0d070020451042c001c0c5546250907180c200350074078050299001d5001904070015a0110304040c2080a001d08080c103140310011581d965003c0d500d011034000400546115001d05c03c2c081080708146c001c3d0100800c0d01411b01c0b252000d0800000b0007031303020340e0102e0920700802c030340d0350042084640c102c203180e02030341c81c06044c40d131013404003600940f02d603602c3d000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 700871924 1250 700870674 700870691
    0x370c050c010f180902031803041212030605090405250e011802040305030a0f030b0a150e0a050616060b10050d02071a04060f0501060f0e040f021b03030f0916030b0901 73
    0x10f01c032058029100d001001070322400d0120700840c035116407246002c401d520030041801014030120a44044503030100980d403864070920000c03400380070190f024540250f00310b002c1c0300400c4804560300745c0e400d0720281c0d50903e0110300c050040f812100d070f20135200038203400c00040c032864580b40e0800500d2285c0c00d401518055503942c801e0324507401514418001008802101d040036418000e20b00044002c6910320512414415a462040300701031402c424802407082c0803004e520b1f10b04242006140060400344c445c80c0c62440340b040150400c4040310b450345441440082858448102c49290141e030369840e0400c81d100144200a40c080c120a9410702400a480c060103000c0c5090244a24072642011071103900c0c4600601c00c0c0c81068009200388400c2c0075900e8101540400480c4101c1c404590200d04005110480402842413402000394444201e050790710320b2a00200440c0140800c400340e427950361311661b000c1e40b2007240800c1c40c0482d145010007000490000c0440503001507181000268200 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 700873174 1250 700871924 700871957
    0x306070306291b160504110d0209040b130618020a0207060c050f0105040f1208010608160e03030307050403020a06050405090708150a080d0f111011370c050c010f 71
    0x50001048070030503400740101e0034404c0d8803040000d004000503581403041c5000610030385000e02400d040116407650100d40d101c16943c1e180c000c140101e402a07c500440e90302181102c002d09424000e440103070f02100c50f4405010b1b503c0c0308440d550821a40a02000d41c1405012120395034501d9081d1040d0ac504030401e10004421721503107001e24819604617000c0c002d41d10f4060680c25900e00b1100601001e54010020a9040511190300011251501c100c07000760b4a001e82e500040d0324841a0548004010041c00940140042007900c0c000c49002c128259070b00c2341200d1610490186d250003a020002065203940500301903600300200c3c20300001000107020202d1180e84460b400300801e41e00ca43c0c0000110b0b0742284150b103001c40940b61200c42d001a541896540d00404a00340da00950380342c610005c0101c20b102541e4151107808040302c3c02c00c0c405290040003107400745c440e20600e1607016407011041d0040b9900340320541e000f4040c004960031800152070820480440030140030a034405d4503403a1303 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 700874424 1250 700873174 700873207
    0x20f24040905150303032502150c030a060503160302041a030d02012708070818150904051e0f0a0204090f0510120203031e16060b030607030629 63
    0x801d800d18000400340350248941c08404501d05103240a5001002032181c110707080200088400305024680c1c21490504c40c0c100c0c94070a000400e40c4040c01c0c0d0f401880711404031940114010b480706001488170b21744440c00c0540320240c43c055080401c541c840e0410050803d0b4001e044824010f40e04e1804043d09900801e00340020b4001000043c0d54600e0f03200d681da03011030340186844040c5404803000764101c0e62050034901c074000c000342c601180840c031803641a00b60030904043c4140507101024103d141c0c500c190f147d800401000d4421400d00c0e001a00e0100c128010ba40d506059a0003070142c0d854208003440043c03405002c84020580230400803130328040602402c02001000c140005052a140d00b4556071118190000e8440e124034155100c050303078002064590503038151000c401d4150591100300a1807040708030f01c1404003114202d00d0240708282e4030039810f0078801c0d015200b075960340303c404500b180c110b402400c0314041d10042c00d03c590030a189004518120124000c0c0ca000c8200c0d1072000d21 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 700875674 1250 700874424 700874429
    0x5190f02030913050414010516110109050f0d02010c0e010518011e050903070503010501121e150608012f0702030106120b011514030a110706090b06030c0d020f2404 72
    0x9a0b2a10b0500041294280548043c8546e54008004604146940454000305000c0c0a01084200c0c8603c1c60212401e6002c05d001c82c1e4020201c0710313940300d02c01d555511303902c1c44002e00001d5403808450841d513902440c0d0007070740e00005944241c03070134200810521022031020202e03810052010182d4501c8005c11010040200041d00d9071070306d890140302094030300401604054041d90508004009040e01c0103501d810039a030202042d440100e012030005005652903402034003110804803107180c0c6016561142050354050320086c400c110384200c140381d003081a58621034808841c0e6082ca52034659100281c90040e20050001c00c840303945501001c01c8081c50a801e0710314400c1803004018041e40505550f45c03100e02d07810001c4000d200c8801c003240b1400000c00c0124051740307401d140340e108904641194001c80d84038100b0071000142c4d092000001c01c00301e402c14042c1c426281c101c95140740100080b001c4903402004200c1040c0714005110001d8a4013803030150040142d10f2150340900703424081c102 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 700876924 1250 700875674 700875709
    0x1c0b0103021c060e01150807050f040e1204090b100f0905120f030301170f070e040b07210504060605031203041509021002010905010c090b1b0c041406090705190f020309 74
    0x181c01d0702e00d46d5040e0189946611501083c2d02c0f9480c1040036803100d45560b00b00030340c1201c001520190582103103040990401400140b180d00140110703a00340107a00c804040e8005036a00610720910b04400c0c1c1d034448414500b500450390448040001d0b1404031340703d041d80c103070701c03001c1d00e0030100c44000c414a103400130313045441d4031000a007440c201c640040100c00d800294400041c0400352603c0440d0056420242010748440f006c1d10020344018050301d107034140346007400c030080c0001450303030440d4000301410f4070102d030520b0801c0800911460002515500d000b01080781503d591255610003c03450104400400c449440c1c5143c80c02590390b06c40d01d80d407840400e80002c00e11500030728060742183ea03030712440001d12144540500c0080ba0301c6007a101c2940e903503000700100d801d40940f06440c082c001e2110503441030034424041d400f00c2c01c109149000d0750040d10100c44030384400c1d100b82da43d40070b0044210482080b42d408004960300c1403081c3e54400440e070041d60301e4400984085182810380911414 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 700878174 1250 700876924 700876931
    0x80a051e1f06090315050c180102070b070f11030303061e15070506040b0f131509170d0608011a010f0903050106090e0d030b010e0103022203030206061c0b0103021c060e01 75
    0x41884440c103205c04903500030803810025440c120490540f01e0152001c50038520715aa20070b054680d00800030300000c0c013800000240c447c0703080c1c54003145908507450212505003450740710b25841d050000903280580c90040901c00c1828031071103000c19207203070300981540c000d00300c12903400721401800007000784074000c401414280c41c2c941080500c2000180030200490840010404250030100462001d2a881039004000300998986200544181d13480601815805588001d02d6407041c401403410310341502003841401e80c0c9028640c03c8956181500a02554140114405611038003a1102c01a5141054051181c903606c40500311140f9801070610755580301000310030420300b045858002c02f1940303020701031400036500080400b0089a4040d06042c0c010501c00300100005c410200c5601104074030100380782da203080c029960b040c00c1e00c81601420881030111149810122000d038a543c12941146241c1d03c1c1d0740c05c1c061071901c07481c04000f4000c00c100b0290001900303800382e1840f1603881030020 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 700879424 1250 700878174 700878179
    0x915181208090307020603042604051503100b070c09021c050c091e030106170307020a12110d08300702010c090b0c150a050106080a051e1f0609 63
    0x11050402001aa0300c14081e45034108051882e0010031665080c0d8141c03402603c0752103a14001410b01d6207030215240c0c0880c50340500301242e5805000e0b00490b0000c42e035151800d060210004110301c41a00e85520604500078103010030314585d001022200e21a03902020090b41c0c5112000c202e0300425849915011f200a15218603845170081c55013002d00f41c00c85a15010105001614141808480442c0480d01710304280d01030798294001d1004082010b00d500f0900404d1070038030b8030f962010104034441e00101d1004160403003403a810101040c0e011102c40d40c6c050309601004000f0605010444400d2801c00c0300c0c03003c001c1081800c1608180003e48141a00440141840c8400c0c00a0140007103a01d0413400300c28141d407200040342146c0c0408100c50380e52609140c1641000c6010291750810089002030003100d841c10383c0a14100c2d18160341d101655283c0765400029210261500c101d20060361b07286280403951070203150b8000903150501d50f107040700c42d82e01c0000100242d2080c0041440d04004 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 700880674 1250 700879424 700879433
    0x3040303021801110303162a05060106020c220b060d1517030d05090c0d03080a11162a180b040c0c15111b010b01031509091518 56
    0x81c1000c00424203000c44541c44e209180d55484c04010420361800b041e40c0c40b00305103540107034543c220b03000d217042d105d441c2080b0b5000b5907101c4d40c0001c0030403569885a0070000038850b10203e41030540034801440b64074000b48400d08411110341103d11403810711355899240e5510b07a0790324003c00f5190360b00180401c80b01801484481c462946500404070654241c0d8154032104011003110410081c1d041d00140948541241c0c41c5022030101c51280c100b14000c40d15400e0541246e07980f4824041440d0074000038502c001d042e040e40c00741016644a43e40e86c6242d00000901d56020300c00f050014100c600d030810007900200074100410b6000320b100d0211a28202c810385c1542c002c909860b0306c10354048c090440c48400041c1200c48401002d881402102044c146c00b0b07506030402403400111850742900c0b41c1452000d22210320a03c4c00d541003561070015010059402070291142a004c40c0012281a0749400d2441000e40000b1800325000c500242e0340408a2891384100160100421204040382032940b42 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 700881924 1250 700880674 700880707
    0x302120a0314130c0504021309151e05061b0f0703120914130c0216030b071106100b09010504030c2607030512090f09070f021006060503060d170304030302 68
    0x30f11440c00544607100116403010a101c044810039600140d0b114207039440b441d080b0070940c11010703105003420702a40140081c402d224090342e05070400d00b0400c1c40c00c4034018807034850328032038140c00c00c0c0e081c0071070210841801110b08901c80d0074800d1310001604112001d081007002c3d00225a80c2c8503040800312510781c022041d0016101004068956103680b500051501000000c6820b5440d10b800128800e107100b481800c0303802e42070260760a001d5880e843d00840c007150840d10480000c0c58444807814040740092654064215140401d24890030240c0b640002e40c44041000c4c18803408010010016107202c40000040c000d030f0760f03080030241501d50300503800503483c0d5000340c481c1e01408003400032400100c0d425600000e548820783d90707100390001040e060100030600719803000c0840d08000030786401400900809050340d094134004c00032610f01004480040c0149000500103000041c0c0324101140030030301d10781c040c1100000401c0d9900103141340354000c8808900013600454085d460714901c0d035 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 700883174 1250 700881924 700881931
    0x10303030b0a180c170408070515040206120c0f0429091507061b02060a0509030a020d120e1e150103120516060606020309090f0f040305070302120a0314 67
    0x4402e0030070a89048800f02c0c562500159514141c0d0381ca540c05009140149258406002200038802e202d1910b41480e4900e034024500548040c00350741c582400284d800c10310035100c1c0b0b40c01409a428564244261703082c0c02001089280c1d032180c200500301c600344500015000a040d0000921003203032a6100c000c040c8030b003417000c2c5083c12005000440160b6030381d030a071680c51a50a2000e546403003980c20003a01030284c40c1c1003000080041c40112074150340c0415494030030040c00606002039107440c52840d07aa482249108001030304000038a0b1401032040903818a040b40890011076107501c1120f0f40e5081c02034030703290090141c810f01c5c0445600e0005206180302800c0c1d06000038425851a01c1d05480310343c40320805c50800c0800a140d8441c80c0518600746011a00500100b086948520f00a5500c1c0d1105441a00c00c074061000680d001d040c0f0705a503807080038130202042e903949643d9800d0340c403a0404542142540a0f402030340e48058500005040d66011030b54010410b40b21020301c0f00708141024 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 700884424 1250 700883174 700883179
    0x2012010603030e060408070b0309032203021e03060a020d090b0a0605030706020a051c121514040207020d02060906041d1815010506090d0c0b07050628090c1508010303030b 75
    0xe01c410051b04a01040481c2200d180c40032940c0e481e0b407503000460031842070b40b060f16a68031006c410303112803000f480d010100b900d200352a001d000001e10542e500203100311104096141e40a0b00000c0d0315034010f500602031207c034820b404a00c5074032a0352686403a02044904800f0f190380e4040030099407404211050060105001a00040403d615500c1e200c3c1740c1882180a01c480c490040030034140300310f01140f9071444400081014002d0014054a0904144180a00c10b03251048800035803038140300319801281e004110b130314405020f5080c8444d83e0130003e4916800001440006484800300c1c10100030f1030b030748030403da400f441c0410b00c0b034a10820400c581c11043d4001d00b518125a01207644050655108840440d210002040000c40c01c440c0098010b045404011300040c1200503200a06440c5100f4419122166100d41003e03803c1c10001101c0e04205040042a60f03403001241d000000280c0101d91503001c0a40390785080080c898011400800502c2520040003856418410702c00f00c09002c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 700885674 1250 700884424 700884427
    0xf03091401020c370206090607140c04020a170703140406020306040f0203070e010c02060c0d08150906150d021207020c04050a11041a130609030b0a0204060c2012010603030e06 77
    0xe0840d01c0540c2052804006a10364103580c13003d05641d01c2400b510500040200400e0362113400e4501a58900441e0260201c11312403515400c0305850580299020542540c2d2070b4005500c080180002951010741304205260740c41c0e03500608208080400d601c600e000d90700240e030f00d060141c1031208560340c4000c51001c4600c184103000c070840d4806131105014400b481c1401301c5800c140001091442554070100003445011090902190030620051144101a42c0c01e10484112024441c030f4807030444201e0b502808100d05003010402d05d0015047c0c2c0d9204200c01030030041a0281710303448980c25550140543d000d00c03850411840c2070b00070558841da100005020f0b151030000b0400290295024076510342140f299041e00d114125402c0d1900a4031f21100043c0b1180d803a0405441d081c00d5010a840840d040750016100fa5014000c45044a402e5500d043d04030120303480306010b15003c8100044103103800310055445568404e001d20341180c1d0100002400e9185140241c41130b00c5507405580100030 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 700886924 1250 700885674 700885723
    0x7081309020301120210030f0c1d03010203071b0f02030102070b0a15050f01050706021608030709080c130c120c2a0803161103030906190207020a060f03091401020c 72
    0x1601d04e000325401d80c140c5040700c20300030038482a406017115001608006260030084006151b0001007800820b0500c64140c49415100d001e040c242d1004480c4100410f41602c5582007401c10184412422030003000b0141042225500007803e90b400408140d511010140c144906050fa920481d54154004642942c8591038140130450003c2050301241c11b014001c9850030a1045a40459681301c0411803a161601440d1070080c25a0300203a641c60b000689000d000314881c1d01c000b8070300c00d80c047c005100ca40c48000451440000e032080b030ba405000c000044484002001981c01410b40520854a40c9a1441c4007018001d5908802c41c2d869404103082940c4007002c54085000c5036040007402c24400110507841c0c030103803002c00440d0052042417200108000d1070b807801040d414001c6000702d10100144201607129000d0740076821029600c00074204041004030b001d008580c1d003403c030320300340491080c2035500c03440394030a015000001e00365000210300c00003210070308c16205c003556074045061b00d120 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 700888174 1250 700886924 700886939
    0x30c120e10020f0607210e0604051e1b130f050405010e07050a14030109140d0216030b1810090503040806010b130306020a030b090705090a08071512090807081309020301 74
    0xf5005d0200c0040c041100210411185080e56281c0000a442001c0c0440d1985456a65070b5842c11a01961180150003a001030440d140b11048406840000100194802c0307180280000c0e240750303002e0340d01820300711f0f0522400e4824051180c1804080c000010140f8113401c01e0b60943d401e200d1030b10703c41e40207543c0500665030740340f82c800c0607501090708111900514401003801490100b0016113000710b0760b0f18803900904002074226841e442c5900f80d8401020100884005c0d00d12404010034503e26640001c02600603a0010307101188820200c60781001c054911004481240800741c0d1650000141407107070b01d0082003010300601020700050300c5d2908014461840c0c0c6290f001c01080e4540000b03c031040c0500c00e402200841d0760041c40e03110b030303400e1040703000d011940318195850155042081c0000c50450224840f0212210700305651a480d8240700101c0d110420400c3c038204159603140c011011030003060260003200c8c81048031603a1403440c82d0b1506200502c80c0e00641c2c40500400040c82001e = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 700889424 1250 700888174 700888183
    0x601091e0b0a0302091321050706050601090e01120506010b090604031511030c071202060103081801140f030708010807030f1403160b060f03030f0412030c120e10020f 73
    0x3400c1080000540300a6480058640491a48080d40c001001d0041c440041c404403007400d8054401c0701100c10040f180111b9401070490a0100d0010076001c2c84500301041c02034000980c4941c0c14580a030080e502c4070310a80075070800303810146040041d0040441048010003c0354050100c0c50116820410300e000000c01d14411030000a143c2c020a6a80d21000421600848100f14401010f2512803614580d0341805030061131040d1a18036942d82c01140043c004600c60781601d030800c01302840c24841401e00a541412010401d04004078410080721351117003200544440a4215403160782c03820860070081c058481a0480d00250b000102d0810026407a001103c901560003080310300e0705040301281074114028041d505954070042e218003420064400081c0748245412544904030720341d244149503132401005020402d0244c03c0100340110f5401041c910f514a110345000158090195113401026006941c2d403030110744500300100da9458450180000228903100600465034500702c8640d54 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 700890674 1250 700889424 700889471
    0x30105120106080622300c17360f10050307030c09050303030403120612030e150405030a0b06040b0d0201050d110d0e1f021c0507030f0e010e060109 65
    0x102c1c540600886417400c030107000c1e5a04141c006000407250120220303e0320402144994181140401c1c400d40d0100034001c819280d20342d908a902c14450710b0500355072520940c8140c0e04600011b0060000c070311112201080c2124101020030800c540d4070170841880444040c90101c0342c8100d15948c80c0b61196640082942d41c0015949804900091682d205880710365440d0081500745c00300008000a154101031030180d80c070980030b4104a540d50b0b41c0c110000d030604c14500100004e142c00860945840c2200400140308034941c0d03550b18242c0e562000a107407503402401287c6403034401081050034502841b407a01342120580d07070f04481590541c0001d002d441050010340b96550380b01b5241c51244d110034142e400300300c07062780c04001401e034504000b80d940f4a20142c4051501404e01400c803100c40c0c60080d5103c45010340c004444a42d6040d04100c0a86001802c0c1010142d460b000c4000c041c00e640900c0c0d4182c00b8810000441e106400045402c0910580080c0076031820000240d40c883d03a00ca001105 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 700891924 1250 700890674 700890691
    0xf06030822030305120c04030c0303170a05090a02041a210d020304030b04140a0b190e070609030803190504230606010f110a020306150907091d0a02070f03050301051201060806 77
    0x117654400444024500454001600220344004003104064101004615441403030000031555a90600e220040d5141264980d40d190804441100181050b410045889102101080d4440c1000000c5180d42d0000c0085d8450420020f118080005041c0003c1042d08410700c00b9518060440e280d101c40e0b0307000940020312403160000800c002500500c90300700002e500070340480040c14200500c80d01149040f404585071460142669030880c4001480c40c110351054548201503032a50300da4034002d4000421800260456031080840c00c1d18a02c01e003032240e803192141127036840ca48a9907941c0c41034285180c0e9401d52080090240903030304400044c444400d2858012107a0010400302403c200748940001e4261090400380141c094650250a102c00c8042c1c03000205d6a807144070455440d910b0380300e651091a09a0038005c03100c0026101c0940c00f008844000d071a10b0b0141e03030344002414040800f40d0000b900840103003c18a1311850700005400d1000007403100360306014520f919460042c21480 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 700893174 1250 700891924 700891957
    0x100b031012060912020c190503060403080c040e04061505190905060414100617161805190306110c030d0c1403010609030c052209060f06030822030305 66
    0x4110b032581004044a900000340b0401940c8203c02a40d2100031621992080b403100c00049104c000c441480d004950700200104030b552180d4806a410300000383c100e1034011802c100c04602200c5100b41a4040c510521000941c440c0c0c0005150250055402c203a1044031403204482c1502504201ca1003a00c101890003c3d46d80c032007070000b50040c0228034220075002200b404000720f01110700d00c140211003043d2240c408008070309141303c08114040390000d091404221030240318510440d03560300d0209100411680c06c81e168030000b01110810a03c5c00407881201d80b0620800a440c010304540c1503040c840309007072150340700406489004401c40300800540c0c40039400c001c144100c24144050100040f030302d5607541c491000030224103440c0002c0c0c03400c104440c80001c40e41402c1c1c254190742151000d2083c0120750501d00325016080401d4141c68603912119024520344480c07140d00c0c01948500c0c1c0355503668841079403a42030302d80c5806e21500f042c0401101040442c1e00042103450080e80c81e400306 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 700894424 1250 700893174 700893209
    0x10501080a0c030e010908220602030f031003020d060525090b13050909070f080309010801061d040c0906090b090609062d0304030305160207060e210303100b0310 71
    0x31002421030420a081c10340c06c14140c20240304107840140408104a2503115490b05000c1c04020464001d200d507200507441048441400713400030021350b0b0401c0c6078203004018256681c0000b0b80b20000324400b40c0d8401c0d47c940038040040b5401c0d00b41c14588180f500100c641030541c0034007402c0000d1602c00c60b44100b0002660300d81105007030017110098403000b460710f147e900b000c41031240e9400c0303103010b58100c81c940c400000c5002140001910942003050392416800c3e0f003001803c07201c26584038030048030110660b44c0381c0c0071951603000e21010510349070b0740c1400c490b03d0a03400400030342043c4c0c06241190010440c4d90b1554640303000712040c40b04140c80c613581d204500b4800b001c008420840d48030b00720541042c0004400e108000542c05203010b03540030705c407940303130140400d400d00700e1011000d001d40d024402c02c10800d802001e6608101c0e800030503520b543d64030011130b1183c0c0c00c1c3c00b0806140b035030000001c01904507819072908015121b20042c40d815480c08220080020b050f90081c0a08500600c030384 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 700895674 1250 700894424 700894427
    0xe190c060f0216060201060303081308031306090609030807020c0114071b08070b071205120106121107050609060c0a050d021308151005030a0f060b010c020d0c090f05010501080a0c 79
    0x20b181e010182d04400c5166603450400034001c0a07107010480000d0400b00110302c084004075490441585c010f4483351641d210305000703030064101000120b540b1521000e0007800304210780f00d118100c601940383d03001c00e8682410028245074041045030305000050100d540c44200407410f80d00421760110051803c018a01e080d4403900003184d0008130f10744100480841c4500c080d0000c0c01540344100a1103000c0c906011054515028002da00195600c6d00401044842e115001368036a8404010001030400c48088a512155010060a864692242d81482610b04080210581c0880382070711403030030042041c07002050741c814190b003842801d80125030204400c2e05000103500805082e0125402d0201d403005017800e0250480d003400158550240002c4c03241404a501421564130a00d504549080d0381d454100400300e80341c0050421004248000c01030322021100e0188601820520841c00d06d40b03c03400c8182c950040ca05190207052400410050f6004071240ea04140c25080100f103034000c6907030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 700896924 1250 700895674 700895683
    0x31f050303030112150524150c070311030303090d0305041b032003010e51150f0d0512030112050106050a080c011404180e190c060f02 59
    0x82180d040c0030000000900c807122980c0ca03160039106040c52549800c3c1c00c90010200e810840f20307005205004d09007910540704000c0280c0e50ba410040c200695500300c04421800e60b08410b00400f40d0354000300050050050003442e244141c40200c005528504d810411035844020142c000341c103240c0c8039400320701001805d41110307a4201410940b4a2080c0e078034100301d01c2e01c043e50f4181e40003421000041003002d04060085040700404070004107905a241801080c41441c0741c0010104100020401c1503070704100600c0b1a058012054403d150300c0e0710849001d6482409081d00c000c0f801c01102502540d11541d000a107120002c603184070b0b118009003809030412140000469409400000228030380100b8600480c100780076a00030419a03031602c00f40800d5101d1409115407a6000c440302d40f05a610441405d20350119445040f0300f02540e030398102c10600030100030a070301d994507282402240c0f038040005118440b42480450026030180c1c64510340c43c1e009000d04020010040b8644003814000c00c0b = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 700898174 1250 700896924 700896929
    0x313030806030705010903240513020f100212090f0301020705010c090e090a020f0f10180812030606091302130501030e0c010818031e19230a030e01050f0114010c0305031f 75
    0x4409c0c040c91070001c0184440c1210004100d1054100d003158060900300311180071a080e07402d8000b44213840d4031450701829500402c0080744d1102c0b90b907025444a480c20700184c40c0d803038454000480d2228280e41c014026612a4002910381c8503040104440c0d03900c0012607005054042e41ca40b00030000743d0005c03a4000442a4405410082604584181d00d5008442c286e50300e8050480b80b4482c2d81340e2046175111043d40c00c1d504546002440418402c0c60000010f0200d0310004000003c03542001c40104241d030031a2112054a9003840810095635030140101d0b0f00c6000c03004090040a0b50000028002d4940030b801d52070301c1c0d01171001e0703090050402c004071864240a8000407280144654024103198007101e460302032a080f80c450780d42d806000340c800e10b44005e5006a11440c90350b4042d2b061a16410101c0f0380380400d52502e54605a0442c20f01c901c2d07008a9a00ca0282055810032440c0d1096200078201d09041004103040c81340840d500c42d00790303501701400340e28a6804125005110041c5003894 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 700899280 1106 700898174 700898243
    0x11030a051c0203070c0602030408010f0c08130221060103020414011203082706150f1503060d08120f2206050910020313030806030705010903 62
    0x1041c0426075100680b04407420b1a20035110801e00b8205640610050b0300009003d0002141c00c2c01041d458846000090084420f0380d0001131040307400904040d101043d2400d01002c664506041010040007204a040000045000143c0304c1c0e80c01c0c40100e210b28a41051201c0021520641e40d0480d5000381000040b40926182a0307000c9800600c0f0080b0280542d248a08410f528030020410b046040000c00c1c4902d81080c40b800c042403603182d1940b040c10b907200c1d101825030311041c43c120510000c101d45503d03616582e0208032415190080141011000300300d002c80d00741c0b50031203644940a10f80c8000401d45901c10784107042d40031800403401042801c0e49181c0480d007140c01154200304c2080c112010f080c202d80101c0c040340c005495031510103080f00c01e4081070581c84088a50420011000f40c0001460f1000180441c000c6210060051300d40c8a56401040882d20620046040342c = true := by decide +kernel

theorem cover : BRFrame.Cov 700719424 700899280 := by
  have h0 := BRFrame.cov_init 700719424
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 700719424 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 700719424 ≤ n) (h2 : n < 700899280) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
