-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1585
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:42:49.605947+00:00
-- url     : https://prove2.me/submissions/b53b486c-1dd7-4929-bc2a-37f626c6fb15

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 284892086 ≤ n < 285071942 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 284893336 1250 284892086 284892109
    0x209060103050105091305120409021306030b03070611010b2115061810090204080c01030608060c0403230607050a020c01020a0203030d0f0608030a02160f080c01050304030c02030f0c 80
    0xe1070180038940c10080800c01c901405004204140010000001070003030030b00014542458007140300c0c2c0d50740d94030120100607400c4010341c00e43e0090780c46c2000640790301174483c3d0384000b200603014042503840d20342c1c00d440b884400030030070300031307540b41e000341c220b959100140824a511a5800740780038298500380d45151021110425908c01041c01c14004035a0f540d401c920b445001f12030300c18005548500a89840001079030040d1019800443c000c948500007281c4401d0004080ea0200300d160394511000e075560b8820381e00b21203250000c0000b80045010344071042480070590502c10344040141030054038201c0200c4240c5c000540104400c90804c3e418403d100000c1c0d006d100034840c0c0c003160f400082e16881041c1402c0d5082d0b90325161941402115080000200004001d580d1617003249840a500c80b40c41c0082c80e908250060004a54060048400000d0b10074a00082199000050040d501a1b2000d4019414030980b000f28030016982008840420300c95200984140980729090061080c01c8 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 284894586 1250 284893336 284893339
    0x215030711030307021c1e0e0429040b030a1209140904021f0315090504030305010b03150103050c0409090c0626040b28020a0e01050a08040201030510080a0f020906 72
    0x100240408140d001841070501c580b006c071aa02d100b800c03484180e130403000360720100e0500a40359001152080e000180b80c500780a054030709014414280d8001801283d42d2680d049849810740c00c1c590f140d003059840209102c00241c00c403107111500c0d17150702c107920700507103040c00001d81001c1c400c1c00700003910240c0010050007654141e40500305640080d00402c0c0010109401813008600c002d489803281e0030001500410102d4140d9088d01ea00040d006054102d4090300803074140000020101008005c80317200d2241c100014400003140c100440180c070010380011024201448042500100c034400c8540051089002251a030b241c6140580f040891036025900140e4013048851040040000c0b0341d4025805820717500d007075413400d140d5900070b0060480540559015102441991540d60081c400c2c848281c90303000200051000444051260f0071781000058001c1d40400c0c010350282c0c0020f170300202080c000b50381040e250f100b002d181407030310541500d05c1c20708101d9981c00d40c00c0010101c0e0b00b1200 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 284895836 1250 284894586 284894593
    0x8060c031b07030e190b0c01020316020c1309051204080d02010e0d09030b0402060c030a0203030106080603070308040e090106030212030d1505060f1608030f01171b010e0307030215030711 82
    0xa840c0a050200c103143c906000d80c0012017440140740324031081e038000d4a80c11040c1c0d030300d840181c00458000d420441d40c0c900c0280602c24090002c900002d6044440d4000600800500b8907080201e0050000007408580500c61a1120051008105e0180c8081c01c1c0050040c10030015400d00242560159902c0092680200602040b8241d009100c5820380350440403030000d903120391011810301e202d0100120305900000c5607503250a64040001c5049407802d544a640075101d010400d911954a448001c5c20030741c00300700420080790741d648190360100c041d000004400790340c0d4010800701007810359030780341e99040003070741e407108130003500c150341c2c41d0850f03c81307442d5001c2d04100214465100e00008451908008100d0080702d03403444101b010000c1d84031115503140c0c2040c0b00c49802400d400e00030842d10b03080116201604000028038414440c03441405074002401e50b01c01502c03001c000c010480e07054010300e41d010000d612082d4007908110b04028189030740c0e140550300246050084100c0016582 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 284897086 1250 284895836 284895847
    0x40c0e041d060705090a09050703050928030e010c1b08070e1003020d1707150c0203030f060f010c0b04150606090f031502090310050123011e0908060c031b 68
    0x5000a05661011044c1422641c800015000503d00d490a90103d41c03050b050804000c0d803960706410650003103101034111203c0c6040500c115098004400c0740b82d603400307000703405038020a20500e41c1d4545554181080c284c1580b064030ba450300307405100700c120740c442d814520401c0071712401c21059006001400e15540b04ac140280007200b201e9017840060311654402d80020b044c0707c0e0380e18042d8403404500d8800b41c0d55444601e48032460600c04d10400d03401900d801d4003501183d0021049034400c0071311803466104c40e503a21042003012a0280300722070420902c410a4000900400308031070269006020905452080307a80e90800d80381c82d60454401c02c07215a5040004201407070100e010340340d200c60406030303603605412880024011200190f030702d8801d041071030480f103a107a072020741601c2c540d956080c2031100754440e0131040b020000e01d290000364241074150100e8078000701107456400b43d19003149134a5032130110343d11304101a154010030076000014401035410034850516101e10011505080c030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 284898336 1250 284897086 284897141
    0x90c010c0309090c0215010609031e02060910120c0203070606050303090102060f0702010f1103040303060f0f050103020702040b030f0d09090c050a0804050708060108031b06040f0206070c0302040c0e04 88
    0x5210b40c450406031940354100085418002d00820280c62611101a035603503a403490010003441952100752500c0e10707a90401a00c1200c41c2100e040c07601d03000342c50300346002c600740244003800c03410070449030030800e2001141505240718000d016a02c038165000f151640500c0c05d117202251003580c0010311070342c820880301c0320a0340c01007100d9510112260744d0001030358034003c050b8050a429140c40c0f10bc035140c0f206245102c0e625801840c0128040c2e9000c1102c0c9480726003040c802c00b6140a400b025500302c02d402c0000d913109800078000340d4400b42c800b0a4500108000c41d1408000d5000c400850308400f49640070150300c41801740040c025541c080c01902d151a002802901c80c8100400800c2440400602800b0040242d8002031180c5821a0003e40c0c1d00d0040382d4690b008081e110500030345404c59844240d900080250044d60407500043c0300940755400c004090f400448101c8a40c06050000805617032144120300f003000302e075200c0204282140c0100411500b409807143d02c0c2480516042c0d540 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 284899586 1250 284898336 284898347
    0x131509050a080601060f1b0f141507120c1709010203190c050d0c0512010807080f03040b19090315050f06090f04260c0d02010b0603130312091a090c010c03 68
    0x902c003103800c0c029440c4005034603074900805d15070401340c0964005088c0004114107080205c540748181c5d0300340c0d072051001c43d0f51208514800d54000002840069070142e0b600c00c60b40c0030b003100191604020120034005200b002e6115400ca03403d9015940c04010014003034050403c40d1221141c0e5113003013101c5101070001410b035001e0141e2440c02d45680b0310710440c5d0340740140c00312001109800741d903a13907039a91242e5007640c90f0040d002c2d41400d40500d01801003a41400001e84042e04c480c2c13404641401002c2801d400c48501e61840740c010005071040000120302a8181c400c440303014408040340b68039105041c5082e504010382518041d082d03d6081020014001c64070030341259110380910740c240e4003919040ca4050140400b11413000c2c00083c41e014050000510380080100d81c0c000703001d04108002000440e02088802c51118243e10f10b410000038840c1aa003800b00d0102c450018485142c0d842e03a0180d84825000c00140540640501808080422408030070703090928001c0012906598002c25 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 284900836 1250 284899586 284899607
    0x8070c0311031e0d1b32070f021f02100c0201061505042102030c040504110303040f08070b0f0d02070519080307080c0c030a20010513030306140105070206131509050a08060106 77
    0x16490142d40b10703441d8404415040c00d450b003104a210340301d107c603051200307a1080002c000c0340701d0300308600e02c4251441d809520300d404038216006001030900404155010306a40c5181b0740c210b56039450045031120501900e880c038807002d03075100d585590808030800103030440c0b88405a50041071200600c01641c2c00650b00501140a07038010640340c03118039003001c5c0c0ea100005110b625000c080f03000725802c01d20f00c100030104c84c600c03001c6502040d614650043c01b44902d00611a40a03010800c800c80d5010940040491522031000c441040c48901140f0440e50260303601120b018100005002c0d41540c4440b045800c40d44070321740c440c80c003062314a07210303983c0c0300382441d101c00d02001c411910000e002c1808000302880140c0d0080c0305130728010928201c2403182d10000c901092070402e022522807040d0355100c0c0394400c10b85805d0724007000380d000c000658210040c2d02003000521100440e421031a0028150040015110303400300d80d042000300021800d698024449980c0321100401003070303900907005003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 284902086 1250 284900836 284900867
    0xf1c030f0522020f060418060e04020d14030c010903030231050d02040f020a0201021207081005011220030601090e100b0c03130305060a060608070c0311031e0d1b 71
    0xc2d03054001d10204812100008040b0b502c41c1000c90000b070282c540091a5070307103140005c010055141c8440c4101d15102d801e0f14017940001903074003040300050005642d40540c5c00c0840440341000c400c80101801d48111b000b04a00194010034400c41c0c40700c61030881182c1d050790000301a007030612680010f20301d890303078803810340310fa103a48040c1d405540717490344085440c1e02c10720810f541ea212100000790103548495030080003042400c0000b00c002d80f150403604e0082c5440000000300910f01001111a00440801d01074800d03980c1050080208071900f101c0c2400000c035034015202c0c50000005461448194070480024402c00c0800c114040039058180c00e40ba01009071b1a10341000740101031071401030440724104000c1c0e004010081c031000140261043c502c21406008898840800701c800850944164010480404443e000030740100030742d071180d41c00203049900300345030301100e0400c0e14000c41e00700c603114030b0004038406042a540201c901e0110b0308840e0741c0285200120003045820480c4002 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 284903336 1250 284902086 284902141
    0x8070807021c5111070503190c0809090703020903031305010e06040806061315081b0406030f12030221010e0c03090327040507110d0912060b030f1c030f05 68
    0x940020714a0344c40081650980b0b03010b1030f19000c0d145020303507076903000700d140401c01c1c1000841b00c00c03018810840010642d500804c120304003440c9200f4031480e050042c09020070b140c0c007400307003200396203041001e4643c240d4145880240e480c0b0300303800504040705d2103444a000c4c1604110502c90880d0000d5900d410840545088404e52a044000c1d4000c01401c07100b617402c00b00c10400000c3d1010000350150880c0c541c4540000035550f41020001120b8280c840140500c000c1865500450700a007a06501d2003403c7c180940b1748501c0c401c0500003100c0b000603140d101005c0e80018400307000080d18041c3d0294020510f545142401030100b9500e00420300482000c0110752940c10212503200381c00030007514060000e1190741004640501100c001066404461081c20000c0030b24030300c1000c041080b510541551185100c41d0384410020345603500c10240c040c031601d084040b0940082084079004810741d950300c0703800d81004500405942095182e003508904010501c50024803010a10110700381d11400b0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 284904586 1250 284903336 284903483
    0x12080906091e1e03031602031206010305060406091806111e0c0a080d0e0c0f0a060c05150f06180f010626010f08071208070807021c 58
    0x4581c0703060034450301c081040b0840079a0390030348100080918016903018041c40100821b4900490743c0340030300001d080042c0300520200b01a54000c1d444250803110161000c83c045031104012000d803401141607484401d00e10140714203009840c841c5d101c00c0000741100904c0c00101725070000c924080c00c230011000502c0081c1c4440c04040800c80c29608541c044201500c1e07401c4540d05500500c08020a94918011003000c01040c0c90030b0b4084210400d030060840340c1150400d9401c0700c90020015048a440c0b0881880000d107920b05030f2168071411070740341d101d455443c25009010001282c1107a0075038805203e028080010000007040c0d0642e02c45140421175580340d8000d1003c211030714611907040042c1030dc00420450104500c4105841404040b00d01140d40e4500b0107500042c400c1024040030740a002e0400060444001091054001440c001d0502c0000b08400700c81204003904039203250040801081401c110344a00b06003038000c4442c01061582c43d021100c030b0601418607031403d41c480800 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 284905836 1250 284904586 284904643
    0x10e07031d010e0c0f01031b0e01020a0203060f04022e030b0625050d0e0a230a09050a0b0904030c06090204110a051b07060f03020a02191208090609 65
    0x85400da800401c0c0091080403868000349032108402c2d078040e80500042c02d105143d0b540240201840c204001225510002c10040308450242c58115601e046000d10f000c40009aa02040074070300460fa80000e42401703062610400c29844a41c44400368250b2103080703050410454205241101c81040c207010440c00000d5001a038182b103159021003802c80000068100300c2044804810b400e4442c0c42115110000c1c05015203e0301814650591f00080c4803200b03201c4100403d2101507044070f0040d1040310882100300181400015820079000079690754100b02201c962400380d5102050300340c43d2881c0760700701620010045400202c1c050540d54440914800310f480d0b0b64000103100503502030a03610707074461850003001540850278000701e483d4910404002a000415040d040765656250024014511141600a500203000000543c0140c4507940700a104001d07000e140144a4290410f428000e51405048600041c0051089901c201c003040203690380059581c540d20900811940104448075 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 284907086 1250 284905836 284905871
    0x224061c39080a1a101406070602040e041a0c0a110c04111809160c060b04020315100305060604050415090c09030b090a08030109050c1902030a0e0603010e0703 70
    0x2040e9840040340d074400016003250208002036500d124016000c8010b4041c42c108450303110983d210307121540c60203400c20031524200441d41c4880b078060111424501c00d502d03450100d810a6008084c4071079402d0800c0100000c80d502c0c100d50048a9200542ea07080c5124103c0650040001310003c2c0a81401d102e0720700780d0f04008080c0e40e454000d1007404042c41ca400f01c0e62550308420940502c00c4494801d03800e4916041c0b0001e8032682e20a120302c80003041500c801c03904004407001c155141c40d95982c408201c0d80720f900055118210a80c0da1201b580030b54414800440c0c011081c00c410140342000717205541c1c1d80d08040f902120b800304c40205013400401000c2507911300d16170200c090b4600e0005114120b581082144081300c1c0224401c0e42581d40385c43c02552680c5124000507c620010030050141b0b0180740d11072604510021801818428104c02e4882c40d03050710b9a4035005640b0128142c0a001c2d840206046000810344159065500d0460004c80e010b4000d03203104140f503194140d1040e40c00104 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 284908336 1250 284907086 284907173
    0xf02210f0a0302130b0901030e03070506040b07050d11090907052a070f14040b0312030403050d0612050105040b0a0b0109030206030901090b010b09030601061409010804030224061c 79
    0x149802144e159078441c41001c5900c150115400311f400d01c04900c910400100699280e103400030041c02c03007652b83e80d64003003500100418680600109201031904100310344180388820a01c400c40564032140e420400c408c03020014004003c10000b000003540e0413030711203480904044040f122600d1420340040441c1003280c5030700240000c02d0200300c0010440080d00d0040003124081c0c4003000000e0050003455201c0190b480340990000080003c01e0009224900801d81c1040da02c0001541503110608100e040c2c1c80500c0c1035602c0d030b4407407003404180301e0348140e4903401c0400b054041155502c103c00207402809a4440a4804c21002c00041c404000a400a440b01c81d40803000c18410340e15082c1080c030a400040702c4070702070b102d0f100c00401c00a000c1c016010313109901c115110b0812403800d00440d801d440c02401103046015500c219403a4101c0c6c0010780d0700c40844076061001510308501405066102c1120084500a0442d07425010800858618010b5090a002c5081c0086048456011490742 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 284909586 1250 284908336 284908357
    0x3030c071110211b02030d06090203010806040f02031905160e0702070911090d03110c010509011418130603030201051506070b0705090307060c1a0105030709020d1104060f02210f0a0302 81
    0xc0714182004ca03a0f01100501d407103070b80e08404020098a070703804801240424000e000c082c0e4800004070340450340d54064405201d1001742210180f10280c00e540791041c00c0c1740740840c0d80303602c01c0703c13074601e589034400c0031700d0203481c1400c1d0007065450f0210000f9a901d25501c140c0144603510780310f240381034401e0f6007151080700019007442d0903210280b8005220940750200725117603014003040c100c0a584214121440008140e440c00d02c2503144203103045040c2c0c0480e8040190000f80e122103207058030b400d01d00b0f640030304541d90001202480e508001c1c0c03c0d510003c10036400c0c6540d1286103100765440d001a2180150800380d46001a03a07005000e6504d0b04c50a202c00360b02d440352030400128203501101070210b440c802d440c03440300628004100000c804080c0606589074111403814000e1a4ac954041d0040b5044420007003844000d07001130f202c00d5402500b0000c0001e82c0303c2c0c5d95202e0300303030100a03c442a44460745440388002c4880607050301800307490b00c001c0c030306c810002d5041e0f0307000d1081c0c0648411404 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 284910836 1250 284909586 284909621
    0x3405130f0617160f0e030c040f020306030c04232d1005010e012c0a0f08121809070e03012f040605090d0f0503030c07111021 55
    0x4071034001401001c07440901d554032410800c0003851002800c0c10042d40304815031510413a410b201361003036598201940c012a054400c02034841020360746c41c080c4481144800000507600c0c104481418242000306164600030741c241110b8000302c41c20804080400008001000d05a03180d0380c464a1204280344108940d15034038080036041c00000131030700c40c05850010308140483e5565401075810000e1030440c1c07404118400074141000c03155060007022400c0200d0580c0a05440300c00280070900d5a401030071b2050704680081c030040c1d000b00040c502c1c04a111000c3d03030907c0c0d81d4103110032901c844003405500824601000c140424011103413070b100d011008000f803110800b00041440050504600128421033803075201d00080c10070400c89003520b801c1c0e0b549501d0101c84000748204100880c2e07081300c41007045000240421014000b8500407503800122540e22905030a00c200382c55034030909980b06505083e0602c1c101604450301e0384054886085008585807000845030003001d055941410445 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 284912086 1250 284910836 284910839
    0x250903170c0616090807050a0e060d170306130c0f0c05010b030703060b0f06040b031303020304150804050c0901060c1b0506042d0e0103060f0e060721050106020601050114070206123405130f 83
    0xc0f1103400de144110815101421504610030018061f0781c02c40d0303910350100300e40d481d03010780075407080010760707000e900810012400000b0000131915203602540140d40c800d543e2402810300d440c11902d142c40340c09003100c9450600d8100759403210301d0b1002411345084003100d026a0000c0500a01c140c40013031011031128050341540400c094050b05003290211614003030a1014619443c090103418140c964603a1600008200d541c0c074800e5a02102d8007000022405010000d46aa034100051000d4032804600070f0441280144141e09100e0701011010b40903108141444078044075115a0b0440340c104501003001230324200280014465505118118000d0600308503003590000306041c8244410014040c1600c4c20103602411a4401c0c001c06005800c503400401c81da6202c2d42c81486d4507a1351025251600a155000584507804a880e02c0382c15034104081216003104441160050818110249954440c00200124005a03044100f090010115800d01c0c440c5041e0038110240c82c0f08a05051200d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 284913336 1250 284912086 284912123
    0x1e06050d140f011e0806060d02030705030a050f06070e1c0f060603140708030f0a030905120a020d03050105120d050d02040b12250903170c0616090807050a0e060d 71
    0x440b090280c050003a0900383c020080c00a4541c00700c0880384c1080c080c01c003940f81c1104000c450070401f44140d900d41300b9003001240565050100180c031501c100010502c01000004080c1803640045c040f50500c40718001c42c038a6611218824410011412503420800c1640e00d400a0b9080f80c07280080c0c003840c0340030004000c0050040100040c11150012140c0d00c0e5130f1200c20396520f1140f500344542c2c841c0c1c14000400744034001c0c0c0180003000d21900681d40413050695003800350b90403542414005078845a02581e000b9054410940500003d896515012104001c01d6a0754000f2000360420403c00149103141c0751103d074142c1d406008600403140d41d615040a80c1042c1c4403050311072224915035112040344c564107140181c00002602d80b01d22203031074078544880e0b4044500ca100304e80b180c00c0c00c001d1004039041c288990342c4100078200070421750010080004040c00e045420100490703200c01000c0c0150341e240b60101c41120800b0070100e4036035854130085540841d80384002480c1d80b203601c0c3c0980d010b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 284914586 1250 284913336 284913361
    0x1303030f1a03280f08040b0706051b03040515101206090203010b0603061e06070b0a0c0f0f020712050703060501062303010b09010309060603021c06061e06050d14 71
    0xd061003181151810403031140e9401401d038400c0c16801c00d02400440080c000313921004c403402618000ca01041c2410355070f40d120a915488544c04540c107556480800c5004400729600c00c104000e500307440ca0441c9000e07540c880d61069100c00b0307032498446d00400180d881082600344000f40c10741c0c506001061095203084000b803e03d1081c102d109509045030340400b810803e040e80c1c1f0a0748010810304100b03007048410301180950201960304858104180d41c04034880c041841d0060315040740004412401c010020064880588190104404010190245d40e40010340704140c035501c00510810480504d400c42c58582581c3c00101102d041c0000055415000b10180b20207106520b40f5055401138510b1291280c402405034038210b800038000104294420ba0284004521130a00000c5040e103039000240403010503500c02c030320355105242860810005d402180f00520345500340d000d01c24400802840135044078000c4004100010600414202143d0000700d00c0c0740d41a071904450b07041003c00c0160 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 284915836 1250 284914586 284914631
    0xf06052d03030a09030b04030507200f040516030b1c030e0109090c12050414151b1303030813080c0733050c0a060f0c020606010908061303030f 63
    0x90340000c5010842640c00d0201c12150960440d965103603040c4d0039551030319400c050150060f020400244411130024004c050100e201c07240c400700020840c00d0030000c100ea815602c3d100980901d050074180204040b1034040c2425070030003410003082d4803650720081110701c85051040b002501e8902145000d16800500d4101240c0c4281c1c0c440c0c121584803d0720b442070b00d02030035400000030061185c41040342141c0e80000c4e045446603602a2010003000070381441d10242402064187c0c0d050300901c500c00054050711708001500000341030030503824015072603a062040c0f0000c1e007444a104009201c5013031041541c2410b0703500403606c685030210042010f55507007a030300076401c0d00e0032086032034800041c03001868006924054a07485604654100482d050b4000c500c0c0c005141c070681d0400c3c070014140380244815003c00c0720001070741e00d0140c2802803500401070a060b05006500c80c06129100c00800d03ca03510585140341518504414942200103140784c444c002c0c081031801400d5403603003410300610360 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 284917086 1250 284915836 284915899
    0x16060209040b0901030b011401030b03010f0609051e01090506010c050f070311060f0a0c0201030f061e05060a020d030c0512041109010b0306011d0f03010501180c090302060d0f0605 79
    0x200948000d414440f85207000e00010b400300d030300180100f2481c0c80c01702c14941901010300d804254242c07004046030035901c01c03c01146070542c58420038442ca00b100d114440e480656104c030340d034070300c6c004481e4203042413010b02038410011f880c1c0c40011310b1039000d01c00d0303003080e07550080440c0d03000c03403a49242d01c2d2285514002100d0242c80800e10150619101c0b003511b00070f040c11200076143c002c0100054900d04034040040303051507100c4500114070b2250744601c0c40100310b010f00708228140711042002025640b50042407148009200004943d5800101e0014540385800d00150740c104445007607800c0c0c000d000e0360700810039a540400040010700510315011403410b80e000e15881c0d8940d180811180011510a400103910013103114605143c100344002528018100103001000d80e404242944c2c800d0b0031001d030b9030110011107940c62078948100c000945044c5440500301d403c66001034450b104040e500900c00c1c0d101d80f031056909a056003d2401000000d00e0007542d0090840000d0a080e148800c90 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 284918336 1250 284917086 284917091
    0x120c0602010b01050919080106080106091104080307080304030e273d0b0c0c01090801050c0f090f03060414070e0c040b07080d05100f1203080a020f1606020904 70
    0x200940140036990405070140c403600c1c1014171207130034006c0f031510f050a903000100f004840040d240a0030f1003014080d00540d80085075103400c0250b094240c5070150381412000700704203c200305103000441a103010961180c0c220340d49441d1400c0445031f03800e1100080b54041001e541c049021001010019124856450b08111a41d1401440b0300c41240392070242a42d500c482d1011400042804070640c00c030805401e01d40c0c1c4d4907458100c0610350342c011030b040324001c0d80314203420030903580c0080c041c10091100f50002c3c0001c2c9898155040c040c050f13a04000121803011400740c02c0d42ea00c03400340c00304c40440502102d84500d81800d00e001ca506903954500540d001d00300000c41e20440c04900c007481500380070714951070b0a20f000860411756022080030b41340003400b8050344010302c00074018640500c0b01030b080e00e61700c40d04062103401040200d238000d68481490010307590000340c100d0041d9034400110b980040c1c59860249034854503100d1004640c10100c0035040650402502d64040e001d05101903804 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 284919586 1250 284918336 284918339
    0xc1014070f08090705150f0c0a0b010f080d080612060a0b0405010510090b0f04051203040e011d06010c24090b0a0b03060f06041803020a03180614030903040f120c 71
    0x15210b540d0b003a1031440c420b4214030b0042c03150341000282010b80300c07000c031681c51402c1a850400035140e007041c011519181c2007110f40c0c3c42442a07010909026001f40761030300c03410510f448030305541c407544440b015050011410002ea41543c801172020341d1f60f4045070a550061030f0203c4500e0050120683d2075100f07901c1c0c10000304d0b1070700344011000560310765602c9005000742000881241e5400444c0340030101c00d401c000c0400e041e107a810700c095030840001e0055445030b041240103016010140c200902d100c5013a901c0030800070b01584040d1300002e080c2000400d0110030708000c1e4400300d03155101280d007981d103481a08a4003060703000b020327018080c16a4280e5a1541b0340c035101920340052000ba403603070112010502da500001852600124010800180e10702d04070300d940d4041650307480070f5000da04400911818140c1240030005c03004900c1c0c244107402c9040403000340c941e996890364013041207004000075002c1c07601001180c000d00410002c5860484d50f8100117031510184000445078410301200 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 284920836 1250 284919586 284919617
    0x306070c08070803010b12011406180609060c030a082412070e0907080c030a02010905012a08091206010f0b0f040b070f050706021212040206070f111e0d080c101407 72
    0x24090403c00c00142b41b149400104918000c0c600b2203040c2c9240d0011040007507440c241c1d00c920007400001c3c06030380610385602c2200340240005000410009904500e141c1031000e4000ba007a0400040c2e00c2164003100c440e1042c10128a41102900700c14031403442c58051003280704001460108071380004088900c0420703800c09064840503a08030080c0460410720051100350f000e04031044540e0207020b2074a07800c00c41c252880312603442842c0207803070700e040c00184200a0f0502e1016891960004002490b4952404620041d160f8092003900403d07000800c080c10318a031031000b110001d144c50000c0548440050900e0290100c3c8040b0484003441083c1000900e0382c0046083c403000d400194641e403c08010b40e00350b1200b08030080003264003030f000b08800000203030340710700f0b03e01d0040c00340501c01407a007030704000e200a20407100202000ca411030321a01010f652080000c44081394401c5c3e0407503c0700004e10b0380515101d41943e0300c10300700703003000a9809040070700b1820610402081d0381b00301d4000010302 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 284922086 1250 284920836 284920859
    0x103031d040e070510050c01020403080406110c0d1101020c0306010b0301090c2c04091b0f0906051c02030a080c0f1603020d0f080906070c090b0f0306070c08070803010b1201 76
    0x2c00255000b9110400040c940001521503020302d5040c42444c00b4041034142e42203a0264100f11680c0001180a0107080d5000c19207120581e0100d00402c00d4480d15000036410070315207100240700d401080301c00403459201707128030809903502804896aa50f154502062650000d019440039945031003d075507061845102500c0d140c41043c1c0d1181002a01c9004812821000c070400301d4105072107070b4060000074154000ca0707002c201e02c641150400d41c149070340b15505441070b0b40041401c0d8200f100038000c0e503580c0b10016032159400000d1007604c1d4514800f0a041c08864030014055200104414a0140000c9240c042146200c820380d2100180d02d4080f000c80242804042d42025403140c0c458000790220407a41c404038041e00c6164205441180001c01552200340100c0d40300813440c2040044022130f000d40800f00108035207030b22581120340082540ca1400400d00d8081040d449050010f0010b81d904944031a9008040e86569686030b40a2120642c00904000ea2110200000150500896 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 284923336 1250 284922086 284922101
    0xd0309050906010e090114041514010306050102010c02070608041110020a060b0d0f02060307030f0606030b03060105031203040215040918030e1008070e01121a180118180204050103031d04 82
    0x511703880440e403c0040e240080c2103000f0f100c0350000d0303854040c81d00c049440001c1400801c441c100c4a040c115601000609503951a88140e041d03a0600e00144441900804c10100751001c52406160b2644e444c00c2c518600740300100140c0c2c200b00d81a048202450b40410075040290046909200c03e110f1082800392404c01d0000c003412000c504101e807001890110000c5400100d18030300880c40404100e0507000b20360480d4006808641d0340c07a0262058142808031a0050000f1000b0301100d480042c008403803440000e01c003d100c0c079400340131115030b0001c910541e0003500b901c030800c00030348859907038020301403010400940105030010122401c80c5055801030300741262aa5070110f054540c1442610400d03810160756042c403142a16413036803043c05101e000c12a003002c540004290240ca4141b281c0005058070b60221190804010b00c60030324003c0c02025040744801c0001080e00c1c0511904550303580e0040300035842410b040c0000281980105c9100140c462103010300c0e62401d10200b040121880b4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 284924586 1250 284923336 284923339
    0x201170705090409081908090d02010b06030601051c05010306061a0a020a060e01060b0c01090309060c031b11040f05060f030a0c14060913020a0807030b090411040204050d0309050906010e 82
    0x20002e016940c00c054001c1074100784100d1907142068022100501d4404c91440c2c2c1c100062040c03000c02181707007c1041000714441c0349000030000c0c864000f0210b01039120081000b41841030000d8881401601c815884002c404450390400c59075031249044c1015000e18071989650505107080903000c03541070800c0300c45004498000b80711601c0036658540140c006000f22035010b560303604000030860b00e5500101001c00d00840001120701840c60060324004060f0003110030800c8a004030307000250005410a2404070100d15520418403900e040542e502040607001c0c2c10504299425071001c8582c1c11890060f2000c070741e0103100d0403a460034140e40d040b8020000c1e10103a09103104000c8035940040012030114060b000c00d103000d104601140812880c441c400da005a0700140d0300e010340741d00c0f820b110b400a02625040c8145004503000030103500000c1d01c09400c98800590550082d0355941c100da00408001d080c10003049402d0401400014161090a00a051540005603658801e078914402480b0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 284925836 1250 284924586 284924597
    0x702061515070204050a020d0c020a1203060522180f150c0c02090c12040308010305011407050f0d0603050f03090112022503021009060e0f01060f0923070c02011707 72
    0x20079020000941700c060081d80e0150703403c004210340c1c0b040301c0c0070b40d0502d0020350300100070802d02403a124001c010100101c000f0985044028000c642d28818001c3e441d64601e005025080c0004c0c10b6a0b00a028000b040c201c02031035000c01c40c08209084170410f18060240f100900b01c16162141a802c0c1c8200c3c0008100081c40d40650341d00500d0104005904004d01c401b0300c500308a0040138a052113481560240c0c0842d000341d0041041000c24000d0441212400701d00e642107050040b40905180547c018140301401c000ca40050f41d045c896106c0001941c0290490301c001090580e860380f25408a54818001380180e440c0b906038135460b008640d007941415048205241880800ca46203020641e821801c40c05190400c1e00707042d2183c06103404c82405850f000441c00710b41c50015180407100100a515641443c404101101103401050101c500005000c9008149440083c1c0b0b81442c00c0804100d001072a03003440200c0d0340c045402d009c403910070b88075039140741e0042250342040481111a480041c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 284927086 1250 284925836 284925847
    0x20111210a030e060a0b0a0602010e150901090b25030b1f050d14011d090c01140708130e0606163206151206010b030702070e0702061515 60
    0x109400000c1c8040155407a000801c203488869541c1018429203000300c181e52900d00104451030306040d010000d0860780000c02c442e4607588003007501d803200d00d03401c4240e101d00600003644407007082d00305080c0c2c680d1141240d40e007480c0401e0180103068049916014041070840f68514440c024425824400700041c800c40c00e148a401e0a20361241000c80c0840800c902881118403410403400b4442c03013804810b4a040080d810402e800c80901d504222040080d0109070500510450218140b81e2034213007840c010765150031044001c203091003001c0000740041c0d00064039520045140300200282e81e0b0b2200d110780c41d900c881341080102d01a2400301c4180070795100c1203100040c1d071828811a44068250755900f841c8030b80d0b191400c00952042100140c0e00b04108000300318242c04403580c0e04940846000c070040d00c2806240e555850f0501600400c260000041403146008006800003081585484803541c9040c01000f91280d41c155140d035800c4201040054941c90a11600700c05000007035200350401 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 284928336 1250 284927086 284927143
    0x1141909290d1107050f0d020a1e03050c0a050102040603110304030e040923070f0506070534090b012c0d05010b040c0207060e030a0803071b0b090c01080a02070c03020907020115030f020111 83
    0x2b04615403044090100401c0301101800040c40b000c0c2c08035004500040e00c80c0d140c0080035041e5000c032000030440c080100100000245c020500760300d4160191400510954640391500585507440c035900c21140480039840c030324081c00a01a0706490300c500501c600e0550b02c2c414842d4500504000615542085044e42c5542421401904000504100c2c02141250442c0f44c024032860503040444465100d84030003c655800803006d0220080c0115001d03040448054060020850702010f42d204110200300c400901100350042008003500400400400300c0c2807002a640380000c0c416078000c24610740c000c440c645004202d01810580180000d46513a0710a03a0031908120010403681900842e032000c0b401280c4900c1046201700911030040c02131010001c00900301407030042144c06954010046040040c1292540c00100c96050310f11110640700c0c41c50603405042c6030301010b400480d6881000050046004208038040d0003030b25019121031031200b100e5200c1c4501c2122060a9610480e0284070b07 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 284929586 1250 284928336 284928383
    0x9130e15090712080a020d11030d0e120f07020a0602030a05030f13060e0c0f0a050d0f0804030501020d140601030213060e01141909290d1107050f0d020a 67
    0x900201c0c2a584207685800e03200e041c40c85000c00607104050003180c41d1408a40400850b400c04440342440c4102400340340c00c103030b600d2150240c00f00c041c507251240c4407041c00042044102d4241d50703000581d160712400301801c0316500844010717403007602c50721000980c2ea80080215240e004d26580c8051855440c01504088541c014255a0a00d440b00c2a1500072409612a03425080c0c1c400010f452504004020000407191184d0810310803030145004000030b5840e52002c00415902040e00808007074141400c4149010b641c0c800303070442d4000100021440e0441e0710003a000c2c4a200210841c030740310100110b01320301130080341028071403803203105004040c020f142c40c00c5440e405140441214400e0503500d05540c000b143c0401d04183c500400c9040c407a088040039015155040c10035040c00c00308044242e44010303032484c0755884200042c410041c101c00e0303085542c00320110b41c0707400d0740c808140c60119510640c84100a00d6409625850b81da41440400e035819031642010816150424074901e0041 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 284930836 1250 284929586 284929591
    0x40c050405040317070207050a0518150d080a030603030825110f1e120a02030a0509180403020d030b09270a0c06050403031403060901090e010902031209130e15 70
    0x18000c140d50080f54001a4000d103c2c03148103d5401f8009441c0b0302000c0c0410809a80c022078806d03920300c08807840b03140c031020303800f40d124a1810150070181e0595000c104684031000f801b42c052100043e0070b80440341c140d080041268030070799070303006150741d542c12401a030a2207480c070440c82ca000e00d0f60070000f2407090306491a905034900984400c1c2c0d00c0020020316120307040b25203460700241d020907800305030428003105c0038110120354407900e814590380e0000e41b00d100e090000400e1100105200103a61194000c009400e860380428408038201414040d40d143d0814034100f00107401c0c202070b4001420300b401c40c1c40c0240a607031008580c003000c1c10906040394500c8201c0300113622800305000302040050500c0c2c00241950703140e0955075400d50070000c1c100440341500c05c14000c0c04000b840856120700c0c5881d811135030304401c0001c440110412013409804460006503042c8950760102d1440e100c01c2e8010007095404858408800d000e071759415081d90300404485006802c03002c0e5504120340104030099 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 284932086 1250 284930836 284930843
    0x11509080d0c15110d0e0f240c090301141501230f0c150103030f09030201021b040207060f0b040c170105150d06060203180405040506061509060d091a040c05040504 72
    0x9400f000c60000141d41c5c2c02c84010000e14940314441d0716106003060100d40b0340300c0c4081018080800f01c8100100a818010b2a85001541040001080c0c1c456030029030b2000880103001f400402009042d440d00e4031402d465100c80c02160341d0542d5110342c01009100504039006442600101074000340701c2894002014016006004000104250b40c042c0081c21340c22204580d2050a5415070400600903500c441c0d5107010b1103030180003440540c4e00003521000c808016030618001d400c02001290182c00b400100400c00ca0502d40561440a045e401031110401c0958041011f1202406d04460580210740d080c05002e8400b801402182480c000c0303288880c5089041c43d240c00040140c040072500a980b2000050f0000305000b4501005000030b04c1c0c90203021030f0705006500f0f06447e40c0c0c0c4c039007030090308642c400c006440c040c0204600d030070140d0b050280003c00068072901032400300e001400c80d50908544518400800c01c0e030303003410b140700c9a005a801500300300d4094200f00a0000405010300b069 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 284933336 1250 284932086 284932091
    0x60f0a0303210608030301090c090e0c0315030f010606020d051201050402030603190b040c0f06020d030545061b0a050d060b07060c030b0102030909060a080303011509080d0c15 77
    0x30a03541c5403e000f044014901c46004503641c0d0300d0850f0f02d0b02181c051240403020000140400c00c030201030003404c9900559000c050135920307140c81c00c034007010b291900c0b002c540501400280e406504819804070080320000d4094810f6400c0c100000c51303040c82000c124250b000c40102c014030450405601869000002600316842d824141da04ca0038841003044003158803420110403c010040700102e010000c00300107540607502800c11101a4542a03c54900e500301b5540720001042d1414a20107580d4000c810107056411807552811500f00412036020710b0f203c10b5010501d00ea100d040064143d00c220307440c0780c07420820081b02441d0b1201c1c2e401660120b0800805000b5104040300301c0c82030308000d210300d441f1540c1d12240e03403406c0019909560204003d1510f04a0035209598010003219464402102c5079217541c4c0d1031000141c840c0d404c0d60841c00c021710010001041c1c107901e00ca2949030306205a10f42d0b00180340e030313040030540d641440c0008200044c1810711050005d452002c07003601014491102 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 284934586 1250 284933336 284933387
    0x60d020c0f0706050f0405011206090c020703050f0f0706050d06030c140f03011103070c0615030602210103110904050c0909010b010f02153409030b060f0a0303 70
    0x1016a08500014051900101010070004200b00103440003801c00781042d600301090750030720901074056489100c2c1405100382040202003142c1e0b1080003d480c51400801c40c0ba915040001d5403803513240000ca415214624054075180d00c0010004070b4007101c00000c0906500381036085807207402c1141d400405070384400e03000c800103440c00041009001011039840d0700440160801440450803502a40681d140c07071800013024000200b2681c1c051a2803d2500640a007848c0200080400314424503201e070030000044104034140e0021716118130350681d0031b0210306165014205848003844000c00140721030044030200e00344032109070742c014080c5003550390346101a40813031802d81c0100d540358103c0e5500c407070640040d0f030001c82a2206000d00d00c0242007003c144104030100e00000b40903210725803046605032540c1031130041d0342c0090b0080400071303480e040580701c0c0281183c1c07002d010840300c0541381c00014440e030400407580082c440000f812040d00602d5501d05442d100040e00c00802c035200b01141 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 284935836 1250 284934586 284934607
    0x518060d02060c06041a16140310050d0b040314040602070e0c07023003132105030708030103021807080f27100c03150b0a020a0209160e0306070c0b0606 67
    0x2a84918040c4141c000c0030180c404002020308030042ca035842d000d075454071707c00c4001d80c0a52031f0344550b056440610782d2500e404140c080044c2c0954846030740880f401d51240100045500d41034040c510944a210442000180f16000c50003940245001a4403000080140c0c02690709083d03003010b2080b1140b403a03c015030b00401e8a00554641161085001800191503c03001c00d0400d0f420f90310f10000f440c00c0120181c800328041810f8459031829a04d401103640c0740d00958904440083da00134101c90345e920443c0f4007034003160800d1000b40e01c41c0c1010030007841e2004140e05d604d84200d420b565884225621051907070500dc0014010044045000ca1a00181003101d1488103200c10079600034401000c00c0285001503844807c500c03030405040a015014080d1a100b2200035150010b0394a525101650b100f01c0c9454034040c40039500c4900c02050001c03031800490000e416000c91703611844c0350002c680a2695984e4252055800190100103e0001c0707202040250b41112005061a18000314040e = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 284937086 1250 284935836 284935843
    0x2070f030c0f21110f060f0c0f03090f06030907150c03020c010f05070b09070305010606020f061b04030201050d020f1902010b01020d0e13060312020d08070f020a03030b060c0114060a0518060d02060c 87
    0x807003029151b000a004041c08030308000100c0b49250181c00ac5241c641d403040070650120403601b2150095002002254440c8024003260700508501a2a65124020900010004840c0c6103058004d40149815a01203511403941e10075464900d40701d00345070900c40d82d00c91410800052070f04041d40500c07400840011828080c0c00c2c001c15260b40100013282e140098907051600c0508941140d4000c030001c07100d5601360f441500c0c201d0382c090809503207a101010703090029104104d1b521160b01070001e214880e103e00782c00300c142d1003038450340208080c030524001640c0d22100202c3d00b0f00405d48502c03000c85540362400c0748010700c80c1d0389840400c000da520340e20103988000100081016030050903079195600d034000c0e403466200c081071816003141c403c0b0800182d01c5080150300035040544543c0039a005449035001c41d00401507041c020403070280005420006002d007038490328414020140e00241501c0e1078680100c25200011190351192aa40100880d480ca04035080341c2100381440380070358038071051 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 284938336 1250 284937086 284937097
    0x230d050f0109060e09100b0102190c03031205090a080a030204052d0306130b0402010c0203061006030e1216020a0b07201f0309020102070f030c0f21110f06 68
    0x84000d8255050002200541d1216003203032000500e110100030034142c002030300b004a00004c02c4002140044080101d050004150000c1c0240c480003500c00200500001d0810482c1c2c06a0b0700c44ca00500a00f0f0340c0c0d42a50000d6070b11004c10313800b0b2903410000c54000030040040f981e050800500d040e940720080f0f03805070940d000520460500742410000c1d02c40c0c0c0000c202c4d54950486c040c00c09440d04010200340d00001c0e4001606401c00700f00000c0440e40175100341c101240c0c004040351981d1401e10a900c2d0409014010040060b040400d0300304404000508100c5000740e5040341402e01000308429003044401003016079002800c0080059464444401409000d0045a014008000700941507862082c0c5540351370103001c6600c04021110041e810b034000a1740540b030302040140e000d000403403400400e0380022404a241d00c00010402c0b412045a4040700c11550701c98998580d104d1786020b00b505c0c0121070f0151280408070703950001c5c401802101a5a900401320440c2c0700301540400d0094000 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 284939586 1250 284938336 284938351
    0x10807110d031e02040f120507030f150c110a020909010b0405070f17010509040b102102040e12030c0a031b171513090222050103140d230d05 62
    0x8940b032941e2112980c000e182d480e100d400fa003d619142c50301d013403217080d1219842503111100300c95200d28100001402034400641d004000d00700122418100484104482542e04c0d03106071800c9072149030f046c000e550380c1c001014a040a0910103009030284041d845004105521955850b40600860340d2544101030040e4600c1d601e200c1b10003804100580440090038025800c0300c4180c0040000307940d1070003401d60150f408525612951030350a019681052642c1049003410b41007070340c0d40c030803030400304803c0c4503603008a030284914114000c40319100d0100c141ca40041e0403041000030030345c440542c001e040c040c90b980340001b030b12800a11541010342c403c00e9035000251702002490004c400e149507107504502d802030050750117215003000400044c1181040d280c0c0545885016082d56100402e4a050810380103405d100e10003100c42100c001c2c9402d00046821201a00b4000c0c4141400102840740f80180c2d00c03694014048440d1065445109140d000d410340820881c40040d0402401040d014110 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 284940836 1250 284939586 284939591
    0xa03140f090a0b090312040e0a020f0c0703030509130501120609290a050f15040506010c02090406020903060c070f0618060905010f050603030901050306090c0c0604081c0b0f010807110d03 82
    0x8044c1c3c10141052120840c1e05a1050709000c2030080300c100c8040560002d04801005940342c20003c544a5a4056409002114090f01d2400024107402000910a80e00101c4100814240801201013152800e0241ca441e20b400104203100141c920ba001c01121405003030704002c80520009030381c400e40324140c440b445d034503800010300c50100400d006468101c500480203980510b01184894458039407400000d01c1b5903140c0000c101076901411000341c0868025114003035520303281c14144040c0d4006104240244940c0d80040c4000010b0707420344542d1507100c101c034446900c054454001030302c0b00500c12803100c5c1441c0302d8940040c59602c00d403400188030304008221695921408070458900500c02d6000f9001000001850707a40b0800b1207a0005085800480585802071886142d01030550001c02034450103042c4414002e0740e0000d8030710702c1917001f441d10500c02555080001d442654060b5508018070b40700b51209503005190003070340f0028618200103090408401d8a141c900f9200e480385c08640e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 284942086 1250 284940836 284940847
    0x30d02010e1f152d0605030402010f03110c010e0f06010302130c020c04020a0315050303210a0b0402070309030c1d0c280c110915090403090b04090b0f030a03140f090a0b 74
    0x303041500c00c6081c1c4c07031004c0c042860302d840c00402406600c001440241000a407071a40800345000b0340c48803080104018003d0749841054a10900802c41c407070507803e1610034500b80b1005520001050b50680398048c1008120786840102d0724041d14482d59081c0942c05500c144255941300c1d440a80494001a075012586400f00104a034005200d40c001600035007042000c46052582501c41c41d41040c03018245034403a40d28407440d00c009100701100250b2080c0002030708800d00d90300100a005580c083d4000f040c1082d50707851824154107400d149848003241800c0060142d000c0e010251420010b818060b050221074041c01c0c42c820103038500c221021458844040e41446580250030600541c1a120460182410301d0344141002440e4440c80c410b480300d100103002c1600c50503507840100b5048014903140d90304d80030601b0245c86080c0c0e5490043c58034200c26400742c64002500c0d902c0b943c05446803000b0b10010a00503460f0b03070200080380c0c0d501c58108004140c44e128030309540c00601c020007110b520b45 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 284943336 1250 284942086 284942129
    0x1b0e1f231c1e0c08070e24071e020a052b0c06030609090804120c0306020a05190c031202031e010306020405040c0804051c092102030d02010e1f15 64
    0x38440d030a40c400283d18007030f000e922143d00911880d03040341e41410a003140d45010342c0050110802000541c5a480c58000d841444480c240050100709100d0600043d402510307240b000120a149000030303600c2500c074035082060b418080401645000f001c05003025614941a4281075011001e40849030702541d118200442c035494421800540040c076424003440701703039031901b40345070080e4040d00314020208001c400130461078415900c021035024030255203400701d0340c0380906030750868200301a9440d4408803512080e4480d20070341c0009030749500c44d242117507032100c001c400079040100700c48080c100a204c00103c045103000d085000b10700c9850050380d143d01701001c0c8819140800030100070302a0040500c8001040490415842034001c01c1454419030155012280100700398840d80581e19007110103106181c3c1900c1a4030300600036400c03940c503141005007c9003200c1da400102400ca8100c00c2d00342042d0450750b056071814014040000c910301c20b0312481c00c9020308460303000405110351346500000d403 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 284944586 1250 284943336 284943371
    0x18020103110f0708091804050f0c060c0a0b07120905030306190b1806070606090902010908120a180e0f1509060a050d061b0e1f231c 58
    0x540c16401e0707456003025501c0098002d107001d03841d401001c004000c01c80310b010381c45040013080c071641e00000d50000303410300c4e0074480d844110aa010032001c0c001c040c2915502d0801c60102c41e80c40c50350800078011002503883c2e001100c0d4018100c4401c002c05141079142581081c05116055805403010750b40d2410b1500800c0000e92003500c42404251100804000c4551100c2c00e07101c0381908003101d5451401e12400085551281140091515150410100780e40b55560b01a0110901c03e895105015485450b540d60350351504100b00e0500e40100024459244904201c0b2079091070220303c40d240a032944c00050b180d41c0b0481c1c1006c2100340c10810403000c42a40c0356005043d070001c1d200001981044000300f04070700c1c0c480c02614018003100c12b010081102c2540403881200380030a4030403c0003045000100820799009410348a07402c124401541041c40306500c0c1d007121456140c2c43c4000c032414030541c0103140b882c8141c0060400c1805600701d80060390f0b2940001c0712555000140d00c042e52001c60b101c = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 284945836 1250 284944586 284944601
    0xa020120040f120503070b0403031523030f0c121f0507080703020f0301030f08120c0405030c2b03020f0f1e1f02031305070306050402120d02031909050418020103 71
    0x242d08030303c40d12080c0401c1000c8200e03a1040c0d0401e0003119907994509040e8041c1c0300c1d8407a0380d543c1600e2800f0000d00e0317120440d400951800c031641600d004070200360030980d4400301c40c4440e0041c0c2e040420b04d00e003186807070f9205e44000588074003a1650b1541c1c0e96882218034042070741d2401201c0c0c81e03404100586034080180742d4400e1071030508500706401074000c05014041400000d0100760121035403c02e0068240940d03100b07076140140842245400580b00c040d6412500c2094028030a184a500481c40c081544202c13101410008600145c0324615040720440d440b0740540c10b5001c1c1d901d1200d46104203119484840903d0030041070000c002c1c0310001900e2080e0f8210380307020380140143c040d4007601d041d040791511200800142c1c4a48541416200e41094000c000b0300c24418407900004000160308006e10070740c000c80d41d500398082035001441d04d5217020150b00300142c00402c2442074016403108281503842c42d0b8981050055250008101200e0b40810341380500c40f00707003102c14119030341400f1300f00 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 284947086 1250 284945836 284945849
    0x9150f13020628090621060b0c0714040b09040204020a030207020909160f060807030c090f0303020c040525121506080405010509070f2106092303090f04020a020120040f 74
    0x1035080b850450006e25031207040c0b062110400740031040e60020340d07107504808003801d5110043c070380c0c443c14980305c80c0c1c3d120300500c55004040882c8021030341d185060320607080e2036031001e880880d4564866007004002e60018040700103261b428001000980c4902150600c100c40240040407156038150100f03c2e110071a07880001203110045c2c1c1800b07081c2d4003c142d0b076040307002c42c1800f191070a50b8460643d80b210f981d4004114003900d2200020030b055000030304113003954083c0d81c10089a15a1070180d24a518480c41580e290b030000e10a2030100d0b84902d40d26090700c07081c400c00080b9030800f50306803008640036501460000d54520188800e0000030f00c00c80f500104544024210a031a103070044402d8405881904204c614440100e091149505c4161006a9011004100e403584c54680101c0b2407128100b0000c140c0d42c0058012410b00d40002208c0340c4040080001d00c41696581c01c02020394090780c00c0e10119500c9500c0c25400b544080c0c1d40001c01542c0c0c0f070030b0036155810003900f07044241c00d961080 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 284948336 1250 284947086 284947097
    0x609050601050406030b0d05030d0b01090f030314030a0b040501121e0302061302061213140a0f0f05010e07060f0e030604080405010c05190305070b09150f13020628 72
    0x2240c41d0ba000300480741240c0d440d003400700d900d168420004107142c11680001c0c0c03480c000042c18042c0f581c002e503c40d10041009807901600c0c2515800f800c030184601307010013404a2502c0c980390000e20f1081d0042c65200b1004900455030000071800314003a0b4001317a10456800080304191800c001010800c9a4503180c0065009801c403140c0e140295640d401034185010050b0017110035040d51a1441150400c4003c1010340c503a505104510134100c1c80203d1041d01d48450040e01094048404103100f0005c3d9000405401094000d80300c46030110f43c038100c00c440c0d941d607841c010b0303103030000900544008000d2078644040c00076007108050044041d01c801a8484d4105404000000c1c03010b10946064030020b203001c07a8074000034038005e4030b05440440c1c0080701141c86946d01041550100040c4540ca100d0260a152900c5052172159944031040c440000c020580c000104d25100015409070b100c50b21040d40007405416802007000b6a100d40c80c90310a0207407035040d1640c00000060b50040914017071501 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 284949586 1250 284948336 284948341
    0x913020d0f0f1a061c020c0706080117030f0f07061802090c1606020a0309020a0b0a0f0912110a15080a0c050304050d0f301103060303071b0f030f06060905 68
    0xc518000143c1e01055205420226290701c03070200c602c580351031103025000215510703c54904050303940d140600c1030000041c034031400802c00701980304070040c001803800011803d05107150003200140e0004204804a00300501c101c4c00880e85a014841c86980f440e041002c0c0c070142c0b40144444140014403111040d00c081044500c00407542290300316654100c00d0050301c3c2c210000d4110301074405184040c2d8000c0342c0c21800f04185803140024009006580c50303183d400e0300c8207101a26218440c1c070614036441c01032003020380825880c82d0b1a40414000034691060a626501c511104101080c215000900b86030300300602d0504601ca02d0544522506119003145401d40c0d0f8242e5890b01c0030860010090300c0e0307006a00b050b00520711a1461525070f043e1151040151011100381d424080340e136001c10381010030582d0040a0401140e0207282c000c0c000d54030704009922442c2a15094014041f054483c2801c00540e016444804d10302861042039114141002410104180c0b051600501a141d180c07805 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 284950836 1250 284949586 284949611
    0x6050609010c0809041103090f0123070306090606020a05070e1302060705011509021206010801080d030c17070324060503010509091905100c0809070b0913020d0f0f 72
    0x564100d40d1091030103002450036840e00d00300901410401a0f009804e2010342c0c00b14100d070300c01440c820140001100d0b080d00348240d07407600341c80d19607452030b036504891060a03961040c1c0107416503102c4400d0030f0128504da900c2808904944040c0d00110052700801d40d020100501400403a008000c0c02c8006182400e045400500c0b440d00c840c40203100b0200012500d04200c429000605400b00707859145501541c0e03800c0f450003a5004500401c1543d00c5400001d9040d8040d801e018146c5001000070003402000c4035040e00180b1040c80c40109000044401e441d000145184080c4650b4055801040800300e002084d448001601d1650503407400d540340901800740d1180540e030449000f00c1c1d1441558a6220070603040c03105441402030214031034901d0300f0500c0700000e0480d40302c0080c5901048003c0707007171508a03215001610b4607000d80c0c00140e0708001200107000031740310710040140070742c2ca145d010100307042c105d901102d08600c41c1d0b41c0b04e040c00f26500c8214814050302c60342c038210610401c4205803 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 284952086 1250 284950836 284950849
    0x3010b040603050402031504050105040303062405130e01170d0503070519120f0b121506060c0f0a1202010f0501030807060903050f28170a05092b0806040605 69
    0x5140c0400d43c1d00c800081c2075640c01c100710003a0f0f151751445500d640c180383c108940a4042100d040d0f01103420400d00086540c111002e0580321525a1069000110641d504485640c00f448440781d0407103c000d800b18070094140341c01c50090190b402c0b03c09222100c0844103042040c0c401d980000d200080c020050000d402104481d0610103c511102d00310466000544410341c01c0d0f40c0005040385440441101d82c01140d01440114508590304c882030b1f804414440e9480b10403c0804419000b100080b4030303581030000213031485901100070784980d0000c80031180e01c4c194160000340c4907d820721038454071050b020f110f0b003000d41c19200024022517045450340e0100b0300c41d03541c000f0300107a034440b41075085c18440d000b990100c0703075911350706d65891598074000790310710400c0020829481e202a48491a540c0105200c42001c00351078110001070780c612138503400400000304428014080e140c0c508840c0e45111320b0090f0200c444d4500c590290004200062121000800d807601592510070b00703000903039882 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 284953336 1250 284952086 284952089
    0xc06090d0c030206160302041d040c05030609070504090807062c1c05030405010e0304180f090b0c07050c0306070c0b06191401210606021b060708250c080d0503010b04 73
    0x845e608280100b2401c1c02c400921550380140014040e28030440908240d0b042954007070ba000e0b00c0c09081040d241c008140d1a06000e444409040e80708140400c480c0c04c003600030b001c030036010305c54460030034801e034035070b1820784180400c601d0351034010740096030341001c1c89402d403400e8060020080a2292100b10300b0f03803624181e06e007110184400800060104482500500303071040148040c0ca44856030340074880c0c103c1400d4058518100c0c20000103a0360f00351182300707400c04c10b82c01801c04900798442c4060070f8482e0b07100c04025280d60044070340580d00781d1030410006005211a07990b030484004e180c1400d05099201800b0b182c8911100d120031506104011038441c11b5401520808070480603040041c0c55511554900c0141940c0b88821060304c0000f960256040310702e20307026103c90f00d1203600038003600a01d0484450b8800c100740b156501041842024000ca5100c0c44841060741d503e80501c0340aa0707005800494080e183d0b01e106000c1048184680e1540f03090310f003065411941091001000e41c01a0f = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 284954586 1250 284953336 284953351
    0x150a0501080607030e0309040e03030105130213140a03080a0512090d120e0a0b04060501080613080f25050a05010c050a02030403060506011b06050610090510080a0b060c06090d0c030206 81
    0x20b175055620321a40030300450b0405400244200502009800d086889030800d104040c440c500e040b00d00c3da460b480c0c5000325042e80d1004901007401c0c6050000e080c01e109600b14071190080c442000c04000110300c1001803001240c15221680c0701c0c0b0304401804001c1030003d01402403500b155103044545034000d41da29503040d10010b40402c025240481d1a8585802e4000c090164840360701440140100380d80320314180d413180c00076500c159803904450304e00d9641d5030750001c0c20b501080250034880c1039194050000032010f00d041e0f40d0000c400100114581410002c29a00c68001d0024202084024851280a41a60b080c1181013803070780c1c1d5029481e4022840080c0420745c031400020f0a50313106c0d1404e0b0480f00302008405a0303010140c20000000e2000700c845a0151164008104103980200c012204440b401480043d800c000d00e40c0c119001785c000342c00c8220050b1107904420680d0340d014003408203550420000d0100b454000c0f08103280c0182c0480b09801c1c080404000d90100380e011030f1845c0e20240 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 284955836 1250 284954586 284954591
    0x912030509030c010c03091202010506010512100e010602010b0906030105060f04111909030b010b04030f031d040c170105060403021c050a0803070c0308060a14040b030f0f150a050108060703 83
    0x9907481c1850030362141c50b442c1100c5500c4c008001c0700d503d0700341d4840303e00c01c0d0140e82c01c507030101d40c0c50100343c2c03c0b55010381d0110702140e401d1010720051b0646240b02c0d0341c011581d4220b025000d44c4c80040e01c40e00e860a80201000d40d4640b1081c86490070145280d40e88071604070028421030801ca80410030036a006041140119142c81c030f0071b00074021584c102c1c0c0415030f940603000300e41200c10310001e0051001c0c0c001224001d80e030500000b4045060819a0305490308a008011800d0759aa01540d4a01c2c01d41030038880c105000450503265661440b80c000500401d841340c0a0b030b00014407080ca90703032030141c110a1007882c09010500243e10b5604158000103500400302c4880d84003030a22900c1c102c840080100402000401c00103d80c2c3d203d108414428466100d880164845604102200b800d901a4800c100c00c8079107480300f41e242c02d804c19140d015000c4d091b03500c090111200390f030410bc411003002000f5401010030f00d141e00d11015440703502c0b54041030108125418918441e46441010701810304040c1c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 284957086 1250 284955836 284955841
    0x1703061e0a0b160c06030b090c0901021002070317040b01060909060f09021e07050304061101020307080403030b0609030102070503090f03030a0c02061804140108010c030c2f030f1305010309120305 86
    0x70343e2200001180ea400c4800340c400c00d5038035407004016240d280c0c001d038052009000403801104078070042d12144141600070f0609401c04000035030081d08015001e034100a2408021000100300e0108d0301c0c062405034858a400303604255014194211a0780182d03070552804100300310642d0003142c283d0030740d6400200565500c0100e045094422103540151070300180014000d001c200002001b04100c074119103540a1b103d40c0d4110040c00c0340000c80707918010442410004000034803a610a4044120042059060020401c003290890700040d07011655035000141807640d51401c6104c54490001c02c5008502e44480054000d0410001c20741c000d004050102c0c2c1c810800d02900840100c00b40c002e4001c00c950944402d0803450100c081c490f5609a52800e4034020759203201e8010182044200d440e0204801d440b00c5502045840750281c2c5140c0f490410403d80c00c181c400c0c0010314402d00d4100d05151101100c4c6002401400c1c3c5600c81814946880c40d07020000703500c8026151664480d040006466 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 284958336 1250 284957086 284957107
    0x30406110d020c100603031d120a14190309140607022d01090f0e0901091a1504051b0a0908030a0504260a08161703061e0a0b 55
    0x28024090960804603010851803070315070040d80a40000c42e500380845030110396070b0703552408179104c41c00080c00080e10280f00842c1d081c00ca2840d401212800b402040b8841c83c03d080704c0f4240700d41003000701c030301c0201c1009190000c9410002c40c0f05242031403507401560740241d540079050240074460f20900441898040340355980785820340741115006011403a030061501c0000c07a151024503003040182c1c001c0399036007049510910201d81500c00002c5407030b4000341041032120300050010030000c515900c03002c0c071a0004070003040f804c103001c0740700509603054180295001c00038a5070011180c0100e1501c1c0810000c120b1070f40c880715401100d00b9165a441e80350810171200f4034860740080040780700000b100c196450340701d0000c00c01ca400c4031180c2d583c10b070003241c80d030620001d1b03c081c1d00700c036940240b444c0c4010403d514001c103801960500c60305503241066031507a501f00d00341101e0f42030100307000c010028141447e6200101866002003098015036800c4002505030b0294003e0040f41840442e551508 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 284959586 1250 284958336 284958341
    0x61d0609040f02061207180b0a03090501060f03080c060901020a1b02010512160f020f0a060528020a0e0d0f0b0622090201180e0606090409060f0b011803030c08030406 73
    0x30b16005480b02d56030b4009800880582c0000344c034a02d0010380d0448203c10745428010211090301ca0a0030028030341451304c0700c1100074019121003a5429543d4000028500c01c11159100007540309000d40d6450380c05008400d0301308a4014100d0085900400803c403400740c0c002904112200d11842900c0c0c1c442c030500040392580142080711100c0c103902d0b0244940d41d510300c002c500c00880c41c3e03641c14440e000f080004a032101c84030a24103065500c03120148001a00c15000703590301c80d034030920911a032034404100866604944404c02d0004e41c2c0010f46840b21a80802c0041e0f0100b8103881c6203810340d40556400c4401c00c84c2c0344005c0c01e02800400412043d5a40c10031000c50600000320f80452605800990340040500031404c0f0b000c10760113221000160f00c50b070319810444210484801e0142d071010300340700e060b500040e1105e070702c10380c1d03402160000b954620901804541014001441040140000d04030011012078400c40060391842000041d52141e0203243c8598803020751078407900c0c0c03450000301 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 284960836 1250 284959586 284959613
    0x10e25120218100c051c020a02030703030c0309050d050c040b0f030a0b15030d050a030207081b100614030c06070602120c0a120b09070f0e030d1101061d060904 70
    0x140315000041c6080515840e00710304501c07100480d04090420111076003551600d8082c5002009a00000a8022034034604c0f983d0001511042c01592005a02940040c0c01e11140760811400f1860062121062540c070030891800340000f580c0c03e29120036a0f889242d0746041407110203101d540c07075031850601e6850f00012541004000303001c0700d40c02c040920b080c0d80b40207170450381e0b15080c40203d00c0040c854600040c0c044004001038880500d030214a0b203049019510071041564091810002d50012101c007414080700b0000b104050f00c50b901c440000c0b0000c6da82240e0244075031000d00d5400d070105690108051401c01400c07120140d469040e0329145004c0e0040025400442008030700304250340762000c008001035000e030394500900305200400303c000c86044400c944c0d08a00d04400183c03d540c040d0500104c402d44506000ac0c8849041c40060710f086a540002000034540c00200d100450090040c140940107400b0400d076900851820401d084000030b10ba00d10509400f00810140028a5107110 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 284962086 1250 284960836 284960867
    0x5090615040b010c0816030e03010c0801060c0813030b0115020f0c0f0109080607050712020102031005010c060f050a0608010b0604030f02150f030106050315010c0c090c0e040906060e010e25 83
    0x45d00c5d007117030302c82206d4144540c2d44140e020490008090300707640781c18840c080840c0540d8649400590904104481d20514802c080b42c40040c100300003c04a060351101c04000c6104280407001e541c180001c144210310901c0b00c0c1070541d4448003002000c0b5502050f0000c0c4d00c203050782d19a46400902c00101e40c41660b0358040400d0b4000c100622a8807544071008202c403500aa200b0300091162000403803c0303202c2160711f821035080c04441841550322510306018002e00400022590643c1d81c0115011a0016100c0002c100e541c2c802c1001460400e00850882000c12502c239410580356484203034402c008003000901c2008100c4450183d03c07061030075200044164518561603685501c0041c6c050b80c0190741d00700d01c00d070206244201c550b00c20718a0500c03903940b0550001e0058580680007020b004814102002d0044140e595002502e95114090f413113070141e0808501d1a1420a50300300c03110060300305815040c0ba1a007044003001d03801c83c844540407911071aa0107400118a4222021003c810500 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 284963336 1250 284962086 284962103
    0xd03150b0f0a2304031220010501030c0603060b04090c09120f02150c15090f1501150f0f0e03070f090e060c03160507210c0605090615040b010c 63
    0x26007046007490080c2081400a40341d0780680401d622040c1007684001c00002a070382c0b0100020301c00a4001904100c40007514240f41c0700344503141503000b18507088143c669504e6952580100244180c1c030080700c0041c05503082c2000301d1810070135119800d200754028180f005803150000d40366680f181c0c1c203030f00c02030030030003141c040109192a2040b550304002c00180e101c1d8205800c4c181d181880c107011558000c0c02940106000d00305180c00d03140c440d0b00202b0341801c0340100b6070405041c2c182440101c008200c0307145101e41c0c660504a1800b549401a407240c81000a82c55009070115040084004500b0a03801c100b410001d40d0400079280c448260402412150070031070000d40b48065801003449180c000d016243c2548e41c001c070b610b2142c001101c0f400000034080c05281074080c0070f00005d25103070f40130750f40c2c0c0d040000c030744016240c4540210466000003849400310005100052142d1a00520030f10060500350809242c25003140e140c81c3e04540c40f0f5540c490101885a004110520701580c0c011141d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 284964586 1250 284963336 284963347
    0xa0311150705151005012708010c020c180402010206071209051903020d020109020102060c0904020702060403050604020a060e0603070f020c040903120b0f060f0a050d050a0b150c0d03150b 82
    0x4549460643c1c3e00320303001455002c081000701c09441903801c103139007043e0344508041044480058850441c51040030090384510001f0030803404c2030045000c030f408143c0003040150101030901c800101c0d007041200000303071100244030050380d02141540d000301c8240f401c11651120000004024241500c008100d4032580d41e1241c0719031664a03420313031024029001da42d0b51380c00001c81a4281c400d260382c0240160040030000d40c1034001c00000d0082d06601420041c1840d5803603000c82e503503070300c560001d03281a4041e10404c01140b030500709480240c2410f20b440b2104116240108450b8080588180c0c14030a4003004050107501c06c011003200000300a006201010940c100a0b22540315a24400d000b5414406d0241040c20600603041c0c061070090101ca20701005c1026265103500316254082c03c1000030400c03001d10b0f0a450007028019406294002206442c40c2c04000c5041e0440c1d034440f440d50303800d200310a0800300101d0b000203202c03098140490420b90400005142a42d5a00810425000403c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 284965836 1250 284964586 284964593
    0x15151209050d0c051e0d080c0304240b0303030109150503120703050a0e1809120c070902220e01140909030324060a031a0303090a0308130f090b01020d0e0a03111507 72
    0x201d91624074080e858058041c0c56646223004144400c48001d010303055400c010032107907a200791013070000003114600000c2d184c040500007821580300780c1c03084104a4603501182d00840c840c0310300758001d0a0480c010015410b0309103024015000b091740180600001240f50a2114003540d940701c286000103125000d0415102c0f45190b840d001600c0c401820311410780d40b06002f50340d40c4101c1e445281c141d8010801e1510b0204101c0c080d5008440201a413100c08003012021030b082c07817501e005410600951b035100e43c108203c2040c142002c203644c6204111450601500c03c0e0003008880d04000c1c18184d14501d51000e6181c8441008081102a000313540086d00c0030b8455030580c0522051080c41c1800a906801181096580d00508064a600070744032141080002c1d1980f00800004005da1640b074411540e56250440245a075804003800503250810440d4541c0d041c0b025040703880d554140054600f0448010804442d00c9002c0100039a102540c40708040c0d45092003060901d0341440d01c5684d81e0741614 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 284967086 1250 284965836 284965843
    0xe0f0405091c02031602120f070b0d0f0b0d020418081803061308300a020408060603010c090b0702060c03030421080405120d15151209050d0c051e 64
    0x1014044002c10541511101d0791002c800c882403a2071194412050031401c0e020400c0ea083c584103c00000d1040c801240f0402c0824890f0303100805943c55400d4480101c0301c0c00780140d40021508151071840d212941d03085503a0300010103031507501a6000120260700d8030030b0072105119000c010342542c4002c104a10014840905520500da0a50945205444e6280341e22164080e0b0340b0001d11a02060002201c0a480001b044002ca983c1c4203a5881c1000c20500640d0460020b0343c4442020340c00003014040d402e410403103142c0100003500200449855200001c0c0b0081c5140101c1150ba000001d80005551307441041d00e2202641a040c0c3e03940b800c3c2480d207008100d0903250101440c0a500484180443c02003409601c526000b038083d000c0e07014600d001c102294400c0c6011120950b940800c6c50f80612110803039005044e108141005910131508007138000e1486145800305a41481842c42c0011400314106541c0240360910340c401d0f1250b4a42181029170701c03160011007004154003a440108000f = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 284968336 1250 284967086 284967103
    0xa02190b10090e060a091b0e2502070501140c011a030105010b0403050d0f202a01050403170928090903021509030f041409010b040e04030e0f040509 65
    0x5000a4004a60325000c141c03d03640064107007455508007900261036014113410204465114000402000b4101c034401034044806411410751403c407070f000c11070f00e08011002c50705424080d1411401039103d0483c020758950b1140140d41c1004140d6408030b18442221040e10f00740b201c144002d1112920002d103413402e407101a60250311075824107000146200c01e150865050b41e4100d80900480c405070341c42901e00b44c5459504600b0082c0b030042003444600090000b0b400c202404002e420060105440c40c0d5080c100391404120419800000d241c250b0307044411903048a03400a001c0d03102c020700404651f498000c05403403a0308041c0110682c5a000107400170700b076560074800211800b59440340780c903500711851880010096400f0311004410080d1458080b940302c1c40100071286012080076404240c2d07001540204403000c606440c10803e8034107420402d014109441d000342c145450000c640b8422080070304007606003d914003403000e06459143d001031070408013400c14801802c104840c6c03560340319070 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 284969586 1250 284968336 284968351
    0x11805010f0501051309170a030509010b011107030b09030d180606120209040b1003081309272a0b1215090106050f070b0129070510020a02190b 63
    0x82010301c404126581c4a000c0c16608042c10004401000c20000c0340101075084081d10390201c24841003012440303000040c40c442400d5503010901c0c1c103180c000c1c41d003528050300143d814807000e6a01c10f00018800070f020b00460360403956103c40c5488401c9001c0c251b100343c00400301444e0424080c104102c004800c00d05030688600c20030410b01c0e0713550b00c00103100140c100340258410892804140415401c586440c2c04c0f03950484a94007050b0b50741d0710080641c0c4900c01c3c104480681410810580c46e0501c03a0302805002a058080823a80e600c1c00d8680311031240200403d8003588041c1e44001d80041c040701c6800c1d040e03d07100f19020320b803100c2c0032610f590007514048543d2400301001072003070b0705610722203203e214016010070f03116400d046054840e03400c2407104286552080c84028089501500300900804006030301784c092940803036100c00001c0e00c400301c981c000202001100e001400000782903604151100c001038450b000448201c0c108000c1c079080c10120480104031304103102106002e0b60007501d0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 284970836 1250 284969586 284969591
    0x3050c0a112b0f0201050903011410050d050d030905070b0c0601090c110c10051e0d14090d0f17150f040c052205090403020109121d0111010e01180501 66
    0x1454810340d405190b03140c40360a400b10340a00740e080003c2d20788102c00c0900b40b050412600f0101214082821a450039032400d042001030020701901d08240c200a1010b4901525132168080c1c1d82d4a0700e55560b4406240c2804243d80c40c00c40768148403091002c5400b40600c40c0140c0c0e03854041d1150142c0e1755400f80100c40c2e01520781142c601001d801001c8100038414075102929040500c0300c2040083c0101009810034424100507001407815185c54250f10202c1c0c103201940c07112040c5800204981140c09600f51000264052090384c4030001021007000c0d4075864a9503082c440010110fa20500580049a4100e85201407282c40321131110f4403554240d0030345004051000070b41c2040280d82001d804540810703010070a01e00f8907459500f03038104e009504082a09090381e12001305000b40000c4a080e40186d40d10319481080102c000d80b450280340c050f00d030411489841c40c0c03e103044a04041e031510305224010640000c1c0078420b40100304550070550080150081100d21440301d05c101d40400c841d01e52 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 284972086 1250 284970836 284970859
    0x1206060b0307021c03061212140f0c0f0c01140307120c0e030d0f1709030405030706080907060311040608060d080a11060f04030203250818040b0d0201051603050c0a11 73
    0x521a11a0400b2034141c40074480c2140240c1d11020140c482000e200000c1214410032400f80b0341c6908014860820110340c18bd54a61071003101a00703015240f904081103410164000125a0f4000002115400030b0b003800c030707620307182c0c108140d40c000e0352000c44444850820314030086080d0440015a03000c501030701580d89403081200115202d442140b8010045100482030500d801d25000426610080314800c40c0c3ca010307151400249018215400500020800c408001c0c10110600c884c8008182508045c480e400300f03060604460300990040a0400030040005200c079916500f0080c015070b04011025a100c25440004103202d0a0100c205d12511942020980b200c070103100c000c4c441d03034059009d1400d200d40b088042e20001da0500c05401c00343c0c02e4241c100c01180149008050000c4a42110b1000709000000c0c03100b9a4040c030fa04a03c115892241a00580d0300707e030866104c1450002c02c804c400c60185003e803641d00861020a10510600c4201410881d103200c0c04441004112550320100 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 284973336 1250 284972086 284972143
    0x110a02030a2f01020303070302070501140f0106020d0807120203071206080309030f0a1e08130f1403030a2307050f010501081c0f0507080c010e0705120309010503011206060b030702 79
    0xa11401203543c016442000000d2a003171003a400b40c000b15102d40c0021401030b4080c100440498000d07121000080d52000040002d80e070100b00c01d11882401e420103400a1404420151441d2011402c50300210b03000800101850322643e80440c504020300800c202e100d44601083d13a5036008942254000d114080354010f58070310005e54405c03159400240b400010b0341035050070301040e00071030040300c01040034003c1c0c290030034203c0300000c06440b0007003403001c9032498482c51503604041c4100d500c4c001d400c10801c0c0c400c20b560100560310450700181d140c13940213003d84640c0186209035040540740b4091802d0000b1915030641209048030364100440d034642810807100c0404145031110203010070300499091400034060009040f000d0b005400302030400c41001c20181c01d66a148826010300d030002c41052006142c4014000e03501c1110f07600642c20310000c0d0700081c01c640303c1802030301c1084031102c5014042081d00d4008a018041da404182c0c1caa00b000748019548140c5e0064203810912150b0070001d0781c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 284974586 1250 284973336 284973413
    0x150c02031605130e030417100c09080d0e150c0a0c0905061e040207060e0a0302060f101a041508070908060408030a021309051603060906050d03110a02030a 68
    0x380c0d0070042100000460300c60503e4001c02c0010341121300da01080c440060680b4407400e5811000b46aa009000d4100c203001e03051b800c90301a003003038000303000c402d500c140424040051802042942030030450001d22040c0001030360100440c50140007250700080c80c00c001c040200d600301e01030f4805d0340700034556515198068181c92044480b0b03500903280f5080c7c0303d0140070780c80d0a040084005070006180004c41e44445044c0c4880342614189507000c1c603076003410158100801940003080400000c25400d081e042100504403a1042c1c2d4282c2c10507401040c0d4109515044800030084075181020802c1004e030013614400f02140d15001241e04040c0c0090200001b00e0090712566116041e18655500c404484000390408c40c0f80700081e010402000c00c0705006072141c5805400740c0082060651001c100003000d485443d0000c0002c2810030008210a40381ca001c2d10b4600d80d40350402caa545042503489a140002c1804041d42c940700d21441c65040c8202441280030301e0015071349100018002c5d004a05d0b0b03 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 284975836 1250 284974586 284974589
    0x70302100e0c06030a02210402030c0d1112030409020301080c0a0611060703050a090506010803180415050906031609050105131808160b09010e01050105090915040309150c020316 78
    0x1102c0d005030b101c01c520351408030011984402d00e072000505260200ca640d0490f43c140340484218420044140421345c80d04020f04040c0c00703c100c803405450251551894202d070742041956000b07104102148441e2041070040d0740180c0102e20301151a9a91942d00301e940340c0351441218020762040390046590380c420351480291111401c01004180c4070130400320010310b00241180d02850f91050307454005001840b1280c024200500110340f01d90074060079580e40c0032441c00840c407541c500507141a03402d42d01e07060141201c200b1260380e00c60f0b90719940402c0c1001900c82c1c51042c1710082c03090200b001d040303c0d80f04030705842d020740382508802c07864a400c4c021515007024401112840050400c00208000c00400a4014100310b040400c0d00d81d540c1c1c1030000e94169106501039454402810b40348800b4801c560050008507061100c6042a41080752142540800f40c200d101d0400009006c3c1030103116940020000d5a154514203a00b000303005150081c0075504910074081d00005c1e1843d00142580c050 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 284977086 1250 284975836 284975861
    0xa0506190c090e370506101701030b0c071505010807050d03021009030210090c051e150d18030509041118012d08010f120f3507030210 59
    0x901134031294260134041315000404660078049990038200301d080c00d1861011a6221031000ca2036003801c0d41040291626200100b04010245a0401c0e0100c02c80814504580e00502c0142c003d80360031080c60b0140c0304200c009800601d040241d0311548460742d1080b03048036030b001c0076190181e840320100800070341c0c0f1200c090010ba104285d10040320340c1542c0510341c203602c01d00440b450030300d060b000300d01510030001d42a1045500608204450f0600600d540740e000414100d061096891000145007001801c4004007000c0300482c4803450300e1001e82c45002c1d45100624500d00108281c85c0c01881944120000b5003e1814050108542580007054800e60705408041422200e409c800454003030007200d41191a081604042401e08024254080d813148010703907620380250705080c4101e0034400340e41d0042d0301050b400490200411030030000000c80d41c0d803040980460904c442c609000540340c1e0400e4a05084040a41c0c94004d440c0c28000e18010b8466020344007248102050841240e60144081 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 284978336 1250 284977086 284977109
    0x6120c06080c12180f03040f050a270905010615031803020d05090411032a04080304090b062b060603060e0a09051c0e0405240906030a0506190c09 64
    0x1402c0c04a03018140903800021040c00510320130200c0031142c60030542a04003456908000303818040300d4001d00071074001d0b2000351108011980b518821a00c4c0b0000d41c541001809014080313007042c00480d0301b2092100f60030800038015039441303d1030b00b21725001d05501040440e01d031084030404000500483d45607250160090450340c1103c0b042540c65070b0041a040c0d901990314504044000c50304030185004540c0c24a581d4803000c804901c4103905480d03058135040d03400c4240401c000c204000011078050320700e000c40101d885017882000c80c1e201d000d10900030540c0000c207109114080e03a01c0c000f03050404510142803014990341d0b2400d4045a13a140901e20644141c140043c51080039500260300c04d42c031890480d4403080d55081161208440300c0960400118121503002c2c05252a02403540c01500000c2d90011560291018840044921110600455020000881541e0248201d48181d50410151030840c0783c0351a200351200c2c000e0300c7c418044ca141107010409123201e140040709030303064a10741 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 284979586 1250 284978336 284978347
    0xa030c23030705120405061618050d020d020d030315050409110f062502011206050603040201030c0e030313090c1403070c050a210f1b0f051006120c06080c 68
    0x1800d125900041444040c0001040030300086520014014440d60007907001c0c185600b030030f089942c88a00416501002c0084400e60080d0b80740d4007046640450b101150420f880d440244003161101c2002c82002c1c2d070004590320681c09054143e0030444d2803000080c007864400784c541d01000f0488410307450107025101e40d6820074469080c002908013030181d00818860030100c1d801d80160200040060242d403100c03102910600b1035800c041c0f4441e10800c8501c09202c10381c101408180203000051010b8109034136501c000d2132044c00b840744c42c0029140034081d20317a0350300560704125040540340b207004443d900c0c010002101c1d504c520302100e0003016406803a840d584808404480040d10348005446900a8104880000300144025008613040c88c44244080c900c48402401c200e24500742602072007044190040e2003840c0004d00f410240c0d002140c0d000c550303003074140070f8513080014400c90355032440c060b0003007a1101d0704500203058910656400d04015116141107503400d505585808501401303219 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 284980836 1250 284979586 284979647
    0x40509071202011d06040312082d180f0d120b030c1509180621070513060e07020106030c080307020901050603090c0312030a1a060a050901091502030a030c 68
    0x1107004113803240b00d4507003041d248000010398981c41a80100d5a43c10130a01c50102690002c49196000980e490031025020240050f61350605c0d440c0e01d0245070340500300c0010030f4010503c42100c2c4041030082100d8070303075034000500740d520700f6200c0c034800c0032640c00f01500442003501d014098103408080c5c05040b095062000f48203418001c00f40380b101c1044140800c082903282c400d2018040c4401c2281d825141c1083c5080c01034001c41002d071910860103c113800ca614410002d83d00003200c0003685e00001c0021101321910050469400842410140c1c1d03080c481034541c15006070b0151ba000320b1703540548560364042c5958a02c00d503a0001d40050714400104030501c1d007070000e994003c00d07240c282c0b0f4503e000d074400242028003540708484448000302c10300284413068410400e072010031250200c020b0b150400021614040d081000c0100300c0c0000b415440c82e4441c611000050003418044039201d4001c45001e502c036000007650100080c6410000308140e803041d03c480c1c4180c61084441f0203580000f01 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 284982086 1250 284980836 284980847
    0x81e070e090703060c020c0108060d0507150c0203120c010606050c10150504020721140f0c12070501021c050408070620160c0602121902070308070302030904050907120201 75
    0x2407100c1654041c8800000c081807072030040103080c0780e1550240c14024240d1002500d006c1c000313400d13240134882f1b138aa0b51000850000e0b072142594042c50701c0700792094000034101e520b0085110020b4041c0561450381f00101d545030040d10308080108000c3c4612a1039140403149800340f005081c1042d40010300500d65050700b60310281d01038800100c070340d4443d41c9800216040e6481100c0448060007214410a00d0b043c4019090382007246d60b240207034504080e0300c1c40410034060700444d01d015010001e2500c4442c0d0040000b0b0240040d80071115465055500740300c3e000b504440e00c82c4800340202304406030386031006d100b814403680e841050039040c80d28941319131005000380c414164000c0c0c403c00398a0205e00c01140038044010008030703140385501040c0b0f4070b0458801c0c10381c01607055601c407440d0b128144007800c0540d941440c4190700e41000034443d04080740303010f031580d102510180d000241c0e082415400704c02062135000c15242405103440300803801e681c80d55a48603c4881515040c40c4000641c0f080 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 284983336 1250 284982086 284982091
    0x61609060806060f1603030b120307020f03030d06080d0e0406030314310302190e0412030f11031512101a041401080d0912021302070b040302010501081e070e 69
    0x50003680c1000711076010002c4c55800341e07084003c070305600f030014010140d0501900c4034051007a252a41c201c0851002d03c1d03a640503c004c0203214404010800006441c10420340305100720b159018070104d5941c01003a512108040144000581d4043e00300c40182410300603002180d078181d031071070f0907005030900800f11504034420704003000061400c0420349500c2035105000c81d100050039110083d181d4410800ca600c16400b036840e0b0950080000c00c115054070014aa00507040128401100e034000412402850003a05203441d1910748a0805403814606000d51321800c01d013400f000c40407622004103d4401c0e50080c1c0c40a4583c081c5011b200309840e036801c403020207165244a400e17040f440704005801d0310802c020741300340e9003c00801000ba65804010a58104d00d40341003a46209052000d9200b19103203403c406400348001a03200703440c289465040f01c681540101d4205540d040c9850000d01a103020b109110b42e42c402c0642c2e84031056900e04801040382d10740c1000b000d20501d440a84000304200 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 284984586 1250 284983336 284983339
    0xa03110102030d1a0a0e0603030921031c05070314040813050303041205210d050403090b0304061a030d1d010207050307060302090a0609031e06020f0a020f061609060806 74
    0x7072142840024030340c0a04601540902801d140d04035513a0140030307a0001540c030102911030407030b0600c6a10344010046559203c4240d84188031440814001901e401502d00c03401114400018481c1440c0c2144503001a000c9504070140400d07285c5500490070fa0754986c6529001d00d6508001c0303030001d00f001d0000c0c881c60964210f000c10b25170740c441c00a41190015400400300000c8960740004100040c00007017190300d02034040c6e50b03808180c40e801c6501c5020310f9420040166840000c0740515000744440303001403c01c041c07900d64a25051404d10060001d1024940040d801c40c00304e285985030204035040302d2100b039940d4084096003800c918400c040c000c0d241d14150301a204001c10787d600c0070300020015012a0701e000d80d070344201d0f4040c01880002c81e4403840802464101c1070000404442c054050300c0e400d406084200324980c01d00000034811891240c0800c0000152454415004648514049a904161070320340d038550414500c40f10b1204079440c00900648414442180250303503042c2c20090 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 284985836 1250 284984586 284984593
    0xf01210f0b060406030203090d02160303230403050d0f090515070609120f020d050a050307050a032706060506030103081b03071a0105090702071809030c0606151704020a03110102 78
    0x7110114002d40d1090b081071000070703000020402544420000e0400d41000c0344000c0c200407014140041003c102030000604102010800e641079a0f50101c00c5010000000c4960b5655945d914002d6a038811040a0501061408090100c194010040d80049a5001d031417600c0914583c000165198440d000c01c4945135a21900c0030042528580c0071211054152501000746603940e2010b840c04018030004820008100320711101c5951103001c0d25001622810001e403510441d00003a0050b1454105001c01c0c080c4054403044010010b00c041514240242c50400c109501c81051000038802400050840802040720450303090310040307040c3c81c180e44081a00d00341304080d55110049070b0340c43d07225044010b1100052142d0729224031440e800103258002490150300c0e140c04550840e000f08502c2654075aa201d0b40024140030301d00082c45030394080803c110b0385403200007010311058052118800654200011a01c02080c5c03e440380c0550740003810b0201080c919135860b12002c2e003840040f4110f00 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 284987086 1250 284985836 284985851
    0x108060a1808040e060915061207031e1d0f1209130f06050405090a0f0204180f06050a271e08030702060603061003210207080601140f01210f 62
    0x4048a0180019144d4440d1603405030400340200807031540040c00c091b4a100200c1d025007485d0361900b0072200b4204d0b2507003041406507038101c402d900415070f000815144100c0b940c6104000c0c8140d5201c0140310003250222100e41b24142c48540c3c3d58050350300c0000c0903a201b01d500714422044c3c180a0304290314002e0480810010441c801401d60340e1a01a2001407038407094148858985030142690003119040203100a41c2c03107448501031400c04c076001900480d940c0500c480d0303101d14241154103a54100740ca136000c0c900d907480d025000b0642290010303040b83ca0070300c21402080855180c010549120600481901c1d141d880c0c1591502c41301d03081c50b0041200391128030014403100080c500c00c00141d000b5200f14906901850b0805000400050413080c0040b01480080c101a4079056248cc0c0540141840451148240e107061200e420002c01031050400010783c4210f000003d20140e081070b1110100c01c501d90005444041003202c51004000d20030140004403003996002c041d010090000208954 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 284988336 1250 284987086 284987093
    0x607060e0d0903060605010e06070b062b0203060f0609010e1f1701050c0405060a120207020a080d0e030a0803060108041505130201180303090308030411040c0504090e060108060a18 79
    0x1c40c451481030081520444100300703020a5106040c01000282000400f07039405c480000c41521500100070031603209000400c0b1540c0394a00c0c0300300041c002401d5000903400000780301249402003e42207100b0320584000070504048a071140e4050a0040d03c82880c40c0d0030500030b900d461070001c01c4d414001c0103810b003a0881c495901d00c800014601d52400405100c80c0d1410303542515070081042ca19454204010889611000c08464801c2d04074070780407800801451011020384101900a58000b0801d280450515000710b4040110411901c1e0840126a001d0506888580100010b081100140700182595000e0300d200342c1e01511031200c55003c00b07a056110800c840055800710300050700181c0c014110f5070031107045400540c074990601103152850394001c10581d030300d0000510101000c00860104002210b00b0625018010414000d196050038000e04c207802510501c100e184c180000020b8407180850b181c0e0503039240300c019026507503540249d88040c0104181c0c141c1c40411604040011 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 284989586 1250 284988336 284988343
    0xe0907030816171303050d0819090f020d0c05030d0c020604050d050f0d0503060429040225080a120e06011e0306110918090303040f11181f140607060e 66
    0x2056014038103011403a04504203285072062030407669084c000d48c1c1c3c00703006110080c1c1c074036182c2d50041d4003408100c80c241c034600700e001c0200104000750885000c901500c20000c0e880301035010b0f10001e030101e448a041c0700c0400c45200c804008042d4200300200700a11450402046d000c0505000e0003c80d1f00c3d6000b00c240807450800395030780100000341d01205101461809014004003140c06c40c50200d00c00c418148006d0b241d100c002c100c03500c11640007885441510703084500710000940041890680c94560402d034040fa840352140c6e10004002c080c0100d4504d07824072a44c002c0010f0b8070010880390f824802402d408070b0101b0000c035041c50340d00000000003035080c06165100400c0000103901e5106402c203104c40e1005c001c0351441c1d00001c80e020008581c40000640b54020f070404450340b030703c050030308002c41c1003c80112040d4010301e0301d4215401c06100180c005000d000c0284910f0f4084000c1c0b04142e18508040c090008840c840148641e00c5141490260000f0b6000385000201480d0071a0098074 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 284990836 1250 284989586 284989597
    0x6060e09010501060e03031e03270105010f21030804021504090603020f010309050d0c020616050604020f03010501180203101508090d02120d020a0201060308030705040e090703081617 80
    0x25982d169801800301d158402080700c684032050300210305080790486d4000003901040045500d510010000030402046540042040c08840e1101e03a1580d0303241f55482d010f00740034000d4260311024200d000a034407011000285a0394260212441ca076417a50b80e04448203038000c4c205030392020b24130050030500307803946006200400c1a80c200140251552040c08151150142c10390b0604d40b410600d14040303000403407d40180c070b42e070307190078095040d05200007191801060607284c25103d00318803001c100100010000e0145000b12110201200c26000301401c0e80c409004000306d0348008200d0112450b035507000355410007815920940d060b500c441c005c1c40032440c0c0c019980001001d480500005010610201660710703401e1014101c1e03c109004481602e100b10120200103641c0010303200d184a20039400280656441150550742c2e050610b001026504079004075a0a00042004280d0036000082d151080301d621011503800c00c20510004414900802e6003a68000854403101b00c030070391668018a13 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 284992086 1250 284990836 284990851
    0x1a06010909061d0108011406010c15020d06090510180b01030605040c081b0304120f02030d05010902130602070f061103130909030e0f010806090c0d0203011409071d0d06060e 76
    0x11a40300405030f14040080060b4803030011030745402c8440264900b0300308010762084080c00d103222250514580001d00003c0d6941c00004544082004440a1169003203c2c0840d050b0107010311668550b500b42e119043c0b818030420000c881024001d040302c4080f604124040d0005050004115030b569002c90f00f80c030340100300d85000804036003c0110804544600c07064044402c2d241c00d0440c074203503450f102140c210046640034460b5081500981c40d01c200212955030b41950402d00ca1540c0d50404200a5002a904483c0366a03030707100d000c03640342e200081c04004c683c80c031402c01d68124a007d80c16103a030100d88101d14211302007085541401041c20000000a02112100281c084c081e410010064507404800600c16004071703540c02c10f03580c6c0c4519169085001114151419160f40d0881ca07443c0c0304424507e1260350020000044059203047d01002104045c0c404110560f03410344211140d40c484580102c10080c2c1c0f45580406040c03464403c0e0240b441071000203141612603081038843c280842d03149 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 284993336 1250 284992086 284992109
    0x2070b01050109170709050408160f050715051801020102040305030c150f01030f1101030608070308031906050901090c05070b190b031b040e1203070807020c0108041a0601090906 78
    0x10041943d001400b4030052010744402941400c511844944800941c0f18a400d83d82c0c80740b0128003032003102821640485601e0a454241c81071034644612910200c010039582405041d0001868103e0114842400300113a5200d03460a81d079201e807200c00844480c5071904540d401c1c0700220000e0401c00041c01080714400080078080c4030566840700501c0c000f855048030a06020040000a00c007802003400300790f0001c5443c0740f0b001c11200490003028a540100d01a208411001090000b01c400070b50140103208c11070f8480c0125184807405444951040d150003403c04d000400080a9582c020f02d07002150740b408501d040c0603921100c140c031a007592004070410b0320301c1d050090b00e04035102e00364001e2010307400f524450814607038680c9500c8aa4040502440d262002728146403000e0228103100490b0051240e26810913800003400040200c0b0000094807900e011080c0365070140480612483d03100507880e1010700c800c2d242c3e20310950040c1c9880d046c03115900d8040307a015a24040e2001400489059 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 284994586 1250 284993336 284993339
    0x7030308132a05030703020d0b06190906030512041406030a090605271605011d0406120b0a060b0712110106090e010b0d200604030602030903040f2705091002070b01 72
    0x10b20503960503a44440d100e540015000c0005854404915064a40100d0304a00070b0f0340d040c011403240b0030b40c0a0400406100034801042802c1107034056025680914201c8030140403081c80a5442d00c614000c000aaa80c0e0782100725451a250008590003080707000049210307005540e81c0414bc1d10300781c9405109521120040003068a8680314a007400c8101c00241405480304250140440c200e004c1c1c0b504005039000c0c1b9080310700800101d0844020060701c1040303200e0351507281000e889402081292074030711000c04180182881d0140c2c0c01510a0342c0d660600c1c103152a0344805400e8507280401303043c13002d03045d200d014042c030a10415004110189000c0b9030848045c00450071600c40ca691144030b0803044120f0340100c1c44800304a040001010a801d045901c401c0020303c55028036400103081a00000c1040114413010001e0000c5560110503000344544400d00c8001440c8107842144c2c40d00b24100d419048840c2a412140d0012200343c11b440100c4031100218041e64070200c0c0a80e0f024007590f00 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 284995836 1250 284994586 284994653
    0x50c060f09240103020f01020114150a03210305010b0304170901030b040c090e07031404020d06091209080106090b1f030b060703051b03040b0d02030405030423210703030813 76
    0x141503c0301704244001c000c12407200011051020b2b0240402c041c80200c09007100f12a2602ea07075a1003d0f41e0484001020307045520801040ca280e214032420000c1c0c1410700000c5c02e0404801a030340a076038441000402050195603030300c0e02e44c00c84c91800381015100c08440142392214840e46080c80c3e00c1e0340c1e40c9407421b818401c8186c1e150344050440010103240c6560f1081d004c80501d030341500568102d8002c1005060390070420041c081e02080600410408451000703020340184402d0100e551010090001d20340d54010101181c00c001d445e182c0181a1203865032407220b01b507203002d800380040c1c10300050381d0030f80501148540d08410411008940002080c0e00e55504100340804c10200b9400150728003414446400750f14003404040c0c0384002e4020010504005003130080d603001e8408e20400350303c13a01e40503006000071740e040c418081c0180b00d0700f0008428104c80027401e4034403007000e00040140514640d0b00301d456450041c00520780b075049000b4500001c50940c07480003482081001b003400e0b404070b0130 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 284997086 1250 284995836 284995849
    0x6020a0302010506100e09100906150e0a060c030302031003051002070c090513080c070e0709051305010f120606090e0a05070815040809010c060e031306050c060f0924010302 76
    0x8203085e02c1900482483c04860354400365440f1703502410703290304a96403503450344006076111941080c1402410040c011403050031000d5a02059a1156500200031000034240103c003c80d074040c0000080c40d00e60b0480100b8005c0e00110740080c3c1c03200f0074074200c69680c0c448c03606010325204c001078055000038401050043d00799031003000e404540c03c02c000303074107114072247c0401c0300128004100380c2000c120203000b03101c00d200c40c2c401480021001c85103840e01e050300500c1320300c8900409205500586114106400c18810141a1589218000e05660030508119482c10320100c3c100d030010345480b00482c04808074000c0200301010b000c01072103d45100d1400500b440b0fa15004880300383d0242183d60081380c400b01c840c2d070304240c20031401e558400025004840d50454103c1c080c0059050124081c03d28400000406445500e0031040c0c03a0251141802c40d110f102d07001c20344001b64084d0f408120000d00103403034180c0204200c0c048603400300d41100040b440c6013144800170b4000801d000104150708114 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 284998336 1250 284997086 284997091
    0x31e0a200c07051210180b010902090d0611040801021209150906040b060117040c0306050105150711062107030b120615130f27030f0305130c06020a03020105 69
    0x100950404107100d505540d60425803280a215902c5041907100320101400428070120004400381b02e0b00b852000384440e0b82e101c80c03004076030f48007010000040c071112500c01c0c2e40d680c410040403007843c1c1c021903d8000181c1000c1040090010b41000002540402403000701803480f4600604901c40c038140380100d080c0b4000b0b400100c1c032207403507404201d00d840f0007080e225400381c3d20070030b80d071525120301e0300488282082c111100704640460040c80188500241c1e8002103074401c2a05120701c0ea01c50007031018840d0840e203105559141441031400044283c801c825035448068241c2d82081410715811445440d28103a07842501038080900c94001d40c18010401c1e03a070341c2500c5500e80380c0b2016590950b078601c000e00d200003c04803840001c0c031644d03901c195400000744042080c007250911a42c898000e06174850007680400011140200b100c5040b1042c050198040c0c84529802c061500141d010344402440800c14880451010000440c1150004080d18141c0e0051448501615020342140c101 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 284999586 1250 284998336 284998391
    0xd02041514040f061505031009110c06060102071406030901020f031006031a0906041a03010f020a0305090604020102030406110304030f060c02010f0e0c01051e180108070f050f031e0a 80
    0x40138024404c50803180d00c00e200003441c030b2410950b60750ba001c51806c00041c00e0b0300311040c0c40c0d0a005051407201050405090090916003d49219455003001a03a98040c0703031060b45116620358001420f10314140010b0b560010365200094908614116003203116403046a500c14031020502c814040300b50715203d210180304640e0108622003894400180c183e500003000d04d841140c403051900401c580750180340f002681d001e002072005000c41000400607400c40030114000900c1c04001901d8402d001032410300894068000d07500d01820500d04545049040d041400103100c02c00c40040007c45145068202c94022080003407401d68440f0000d0079240f1145002d1402800c2440c0f03511030810126591282e5003090030010ba95080d6080a844200c9030f2200caa05420300104590b2808151442585e0101009076a083c1150340d8204064031010091040c0d200004c1c03041c0605080c11380031400640d0484c0e81903104c1d240301c2000740f003000c0090708111031780e080b819200d842d00c0d0782e4009c131002e960203040d00 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 285000836 1250 284999586 284999591
    0x801120c08070b030f0a0b13020d090f150b0a0537060206100e0402150c01140108030c0d0507080910050435070303080c03040309030f0818010507020f0d02041514040f 73
    0x10703050025483d0241801075800700343c9d000940415080351075001019855000307100005044e0642000745040c000210300c018001c1c241100c01403107140006811098490062002c0c0d40c3d2007114803c0b0190f41441c0c50300304200c0001c203103a1003080c40d44440c41c034014000c56000302208c0c0b41141c031861020300c0a500501419809909120050751440050551140c0c04000c0325218811800f990b030140c031804042e0f0031101e038a10004200c5c0355000c40200a0051084201c0c0d08141d00380408452031702c11b00b44050b00400e4241b190208628140701502c2c00686645441400e00b5103418a00d451041c10000411560740800c0300007990268545603c103003000205c001e41607082c0b03107490103841a100107105200c5540c00000003802c260007442180061a0401548035001070179281120942e4010301070005040c41e80400307842558810700807124141d901170b0558051088000500c82001003055080745e11648400005404d158204050b000400e403580034048580034000c103200803a107018528440060 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 285002086 1250 285000836 285000851
    0x30d0209030106060942030b04050601020619150302041103040b16020a0809120d020a051501050a090b1f032007030806060307090803070c06110109030801120c08070b030f0a 76
    0xc6c000395000b01e80d009540e0183c0c103292001c1170081e50320903a4480c404c4d905284140e121400741d070301d0b03813103111881d6003624100110703204c8030700683c1c0c2c50307008035000d914141340e41e004801e58610907004130028032100111031a11036140c0d0b000400703841c040c00c1c003812544004000c00051205007010942c02000c2c6550f40c407002403da5030300940714448503201406410001400b1001070315401004440801a6400c4c1c4803282c4000f800203458010750841550107101c0c54044d000d614130442c40d0305040711402480020034502e003403412400b41103a0740c503055118025540c2203840070405803403001c0000042e0740000d80c4c8034040104000b00002c518403602408001d1149200103508900e5841d00000c04643d402c0d142d680707402c4201e0300491140c2080703010b800045900000c00c0581c078480825a000c5850316080c0a000681c22401c8894892014000a07100c500400c50207141d030441ca1103035400340075804134541d120f01d02c4500d440007a0b0f01200c1c00e503100008000052003400c100c1600260030680900040 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 285003336 1250 285002086 285002099
    0x30c0a05090a23011203090b0a05090d03030902090f01050a090203060607020d141b04060902070c030312060902040f03111c02010f0306090c0309120c08041412030d02090301060609 79
    0x444009100405039991200580c0c05440e200c00740a00f44580e0000b1010fa0f507840d040341703505064880c070007100400c03d40d440201d403908041054400300a582c0d40c1e8541889070b44001c200c0c1140031070009900341603640b103e4001503102c40ca50a44240703c0034404c1c4400c1e500d000d0600180b40004ea0001440c18814024082c6903980c16084a0341940c0440344050084042d0421404204040c1c03039107003c5104203012a14403c22200004900c03601c02c031001c0005903a14030a1005a10a8140042000808a10a10000c0c2c0a00c403100b961020700480040c1c00c50b10b80207008100d034000c0d0080c01e03241420302d80c00c00802021888498411030190741c50040400d243c1e0f0207400b1941080c00c024140015100d400d1519403096002d0070041440314800e01c42d0018200d009001408860410380b05064403145890405000e150601d01d01c0c1e900c8600341e40380500d00812405405a134296145e0700c180d4a4050403a400c1c0300300043e2800107403000005070394885c03100c101421107115600070002d001c00c42d0010001c5 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 285004586 1250 285003336 285003349
    0x10080313140a030807080304050f0616021516030f0b0d030207030b150303030103060c1407030305061206090706030b0310020c03030f3709050106180e0111042610050402030c0a05 78
    0x100e03401b072031290300c075103032031a00074100170402c9030f6000b80f4810181003100c0024944031007001d600c246c2d003e588a400d44882c09042d2031004803544260790400180c201c6800784a40d014040180f0300038400210340168400282c28405121015401688416000d2060004104c070581e006807e0760a05040c401c28000869105e000510019241c40e540d0302140b45001d00401c0c0c00c50036807640320745540e625542840c02030000c2c101038955900407900c40c05420041180003400a00800d403031001490880e140c07000850240c042403103260703058002d00030544500710032400030b0a00c0701c400310301440d1a0701d807910900300800070041070702d001401d400d803100c1440040015003017030344010060080b1665100405503809131000c268000c0583d8030f406030000e81c1900c12002c1c00f4403442e0051091001e1240140c10350700340e49400c86084c0310810300700400c000c0c850f954800042c2c42c04034119608510038040f42000d09100e9191084010b0300d4070f9504000452900b40140813440d0022a440c000082c10300380403070032 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 285005836 1250 285004586 285004597
    0x40204050f010810050603010306020406020606030606061905160c081b0d08030a2901020c041a010f02070806090304062c040f0b031218030a150510080313140a0308 72
    0x60043c1c4201065a40d820307070800c1d201810000e040d1654070750352813401d14025071180c840c02005000d0b40010817102d01d804600d0a018000c014002c6043c00c3d485c8012085402c4990001c005004040220b001c2c120700c484100b201b881e005a400482961030040401c1c280720100384810f42e070b04141d409040e80c503650720030b0f420b4206802c50070b020f03129520808000f00a10014210350340400416201d4100880310f025003403250307442a03003994035500d0721405220a03102284105450800d00f658882c500d03500ca242140500b1095104598216640724920713800d15200b911152001d0700f0018040c400c2580101080345c420114503442c02e410020711078928a40104a4130480c45a03440718655100304045401844080c50003c05684003c0f03050007510340701d42c1c40030598171030030342c58221045420b140201c0e40c0700180d508050080f8035403100308001c00c0102802003200008941c00040440c0c407034400c00240c4004074541030801005410b001e18500307850f001800032441303001c0c03030801030000401d82426100d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 285007086 1250 285005836 285005839
    0x80601120302030a0e12100f060b040b09060a05070206070b150109240e060a0e1e0108190204030c0305060a0f150501050c01060905100e01050411070b06030a05030c0d02010b040204050f 81
    0x176150a07409000030404aa2004600b000d4403030304a62480f040a258841c002103090b02008100c0c069442c9240c221a0096115a8110305418052000790f41044002040603403100d240643c5444043c2d03000490750b400060059500707414420410a00100740350000c40361000c00d080c02910384d071601d6006145400000429042e03d1030340942505190f010f01410449204020090340d1030703a0039458000c0c000380480d01084c0c4503548120401c2c50380c0c0d030348120f010760001c81039543c4035a80d40e03041c0302200c2003504001c001801903800c010003c003056004c0c03000000355100c0c1c0d0203040ba904101e032070714060f194000d0080091500e4041078801079030350103498070201c4a00782800c940720b00c60065040d0042c2a01d900c1152510f040404100d9880440101d6a007038a0145c05070b01c52698030b641c280300441d25005c0c104407800804004040224804810169020100900b01d0764010704075a155030942c1c1000c010084103030f0290500c03215264087c002c0800c00042503a0840c28149042c00162944107012070b641d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 285008336 1250 285007086 285007097
    0x70b0a1a01110715020d02070b0a050304020603042423010e011a1b030406110307050c130e070b090f0312030105040203040c15170703050609040b060402091504080601120302030a 78
    0x641c401c0b0320030b011a40080030700d508200f04028035260040d4480c40001150401400342c040c1c041210701c915019140c0e24941607940d0341c00c1d0359690b0700b1320401c3c2d40701070810380d05000f0a034140f90342e44908482c0300040b11a0800045007054414001c04a0410103071a0400c4041c910f070014891800340c04040f5044a21034002e0700428807600e00841110301c640e40010301c500f103a020150940f0f0000000510464445507200c09a24511000d4a074883c01030b024020042d811403c000e06c02031501d400d18088011542e00700041d01c40d42c0080030b030700c0c0c01c50382e070701c0040c1c880008144421180340c020304400e42210f00b6005400c501000000c4420319100c1400345038460341d0f02001090600c0281d045080150820410503000c03101184000307065105000d40c515035031038104c400102681e219000d0f240c02030401902540b5240c656030707166003081000800d040c1c5c1146d070070700c0369600c903548941910b0b155185240c4800c0d0754038113198200e410188c058002e481d4554240c1c030702c1800242c0c00001ca828507070191034513 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 285009586 1250 285008336 285008357
    0x906130f090b0907030218091002130b0a02070608060f0105030a050c12010806100911070f030210090804050406090603030f050a03060b0d1401080f070902090f0a0308070b0a1a01 78
    0x3008020000a00e02900c0c4500035410032800d00c40010302c0909407402201c108455038600900c0d071030080011180810039400c480306600c402c0741d040d00a0800780701d48903c4209895203034a621005a000881c40344010b0740b09007020405a03030044141600224251040c00303001007600c0018100d840301502e09910140c0e035000141c2d201c0341500949441c0701206092050035607640c4a180e6030703408180c404c0107064030000000a0304203111301c0f580d0540c2c901907060380d0034030030a030310340300c506098400d400d4040d03014440c00380c0e0700c6000034420041118420004162500d08010621049030340b690801c0c4480751801c8404e01c0841e030071000c0400d862103a403038125034408150508401400940d17104241280c004549000c5084050304500445625407501281680e6101c0c51355560341000810041c89402500040c482480b0f20340003401000400b9041100c140340c580040b49058160fa442601e590101041c01d0040281c2c1d5143c0c0d0350401740075501800070b05a900c031584003859804c84180e0500c800300c00d1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 285010836 1250 285009586 285009611
    0x905060a1803020a0303020d110a0b061c05030a021e070509220215070510090305030c0a02010b0901030309030b0c0301260f1c0314010308030106050f0d06180b090613 73
    0x1c111000e19400350921000c1ca5491401a584003004407010740890010a01d00044241c00901c1d00d000079040710511069844680034410404900310541e041000c02c4500e0801050041000300458043ca5000b0208141c2400030200c2820310500f020740140c00082c1c04110581c3c0f10100c281c0c004400d03150030442c40035021419085071940300d074004c1d0401c40e5030341c5040344041154082c141300383c0a4000e60700170440038040d103070403140740c40f81c024045070092002c01c20065259001e004182d510b07000004121551400295a44000340d1007240090111102802007120401c10740ea00007202040d803604550514200406004c05c1c00540d030742443c64000c41c000c1303101d403c100c40c0b01d80959080560f01c00440c00c418040d40500b105842030302203810a580b540c010f14050000358100c98200081d6030460342850011a1503900003004980034002c14041c44100c00c1c00c0c0e10841c002000600358000001d144041210181c81031640c14600c120f4811080209039183c00d00d031429010b0320b6140004046680d0103 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 285012086 1250 285010836 285010877
    0xf0e040c0509070c06140403030e0c0a2105120706060b0a09060507020d02100e030d0525050a080c0f100e0d030b2107080f0f1903050708030403080f0105010905060a 72
    0x5c3c0055081c048100a0002c0650f405d40c092402550b00380460102c290010340d848a000459981107160710303004018420ba80305200c9680e24000a080c408051552112464611440716a6006e072500180d41c8003040380e0b07481840001d0402540311810b00e80340c007101505002d000d10616050120001e820011541c40079682011664020441205034110b14002072414000c4041c190180c480c3c41c81010960b030260040d118100c030720325002d402074025035500300781486190034111240d2003404030b04000906603902900160f00c020b001400032060f0380180c10718242e80003000350b400d40d01d8900c0112132154041145100034409040119040c64660041194210258801d40f203401c04101403c019030070101740710b0100c802c034800700e841c80e172030404a03552212100305010f1859800038030320251002c2180a100e0700c20b4040e092160503d03e594a0300d80c1c0541c42102c0440c0001c002c0020070464510702c20006014080a10b0422140c506040202e50b580c03080c04004020f1010345042000b4809414 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 285013336 1250 285012086 285012107
    0x606030706121b0203030a0b0604050a0611030d020309030307030f0b090103060c0e04020c0c0103060b031e07030623010815010504170a021302031902070203070b1b010501030506010f0e040c050907 86
    0x900808041185100000b5102d400075200340d40407900740a08e8844626005007540c0503904000c184900d19072900c1001ea0f41000d1108160b005030100303002090b00c09030144050b511488544005d503a0fa40381981009048413900108000e480d03103840555080b6484520506054a91040303000a04010f00001622640249411554020b00018480700c400c0b1020507034040306c501c2078a05101c41c68450340300c489103000031980b03c02c161001b00b0350704a030000708001683d0010010b080000360142c44426000400482010482c00000031155441c110b5074041107503940030000704c43e40f0b06805038240c0000c01c24803031407194442404007802d9103012640140040003d9507801040044c1f41c001081c481d4029410450b02d0120b503000040c00780c0300031555030084a0241394000c001d00521802c00800b24002c1d0003c600850220f42052076811030a1070074483c2c42e028600a0000304115858481c1070b50344c504054104030382c2e4155040510000420300e0940c20203a85040781d00b8003580e46d8800f01207410040d00d = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 285014586 1250 285013336 285013361
    0x90911220c021014061c030c06050c04151b150b0a030f0507050a0f0b0f0409141501020a150c0e060406050c011104030b060f01090504111902060603070612 68
    0x1030610260310070350009000a480300070600c05101c24400c200c603c40e682c070310445246802040e407034086050703d01480c1680030091301c6802d01451800c42030315030004680c002c03504c0c150303410740c0040e05102d0405c40c0c101c5941300304040e140071110f4900d14000c00b200e9188001c001031a090002214980e4015103421450b442035004d00840c80d43c556a003440303070620440203c15610b41c040d0240110b8242480c04940b000d50b400b04c0c006450092034040e500e0b5140d400340e814508490014040030440a170b01d030044402181350a110b401c0e00d82001c1c13507400e0700201d100e0398260555001d810b50800081c0351000c400b4014404810000301d2001d5001d06554001092a0301035001100040100d80d4640241c05401d4108003080200100c507500f0f803c1003420f1107280005030003901c164001400b14074114040c080302c008185031001c0e2b42548c0340c010800384c50810502a4509001080040b4a00703510034081d03840c008244000c05c041d09224022a8803004140102410071410300d1a001c2d80143c590401d0441030785 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 285015836 1250 285014586 285014591
    0x60604050d05030304062316020313080a0302070b0306010e041a0d0c03050c010219062f0405180609041709060301090c0f2f01060f030c0f09091122 65
    0x100b898903948950003154100c440302d00c0c080075075001e51148440a0085000041aaa0251980d0b108903c03200041481c6608504c420802c40c0400098141400004d041000007003910b5031043c07502a0410300d02d60403070500c1e8101402000404d030780c8800804902882540c0005001241c1e6800191220000070141c1d0000c03031042e0214200300e11424841c2c00c80f401801692440062400126240d42079a5041c821620440308a440801c41590007200034618080848005402010130a100d0916096203810170590108041009003004042d4811654081f4498105490440004bc00d001d0025001800f9841c2000e820340481440c1d500711508900004c01003610380da9030b80b00442c060210260800c0c001500340711030180050191941c80c02d40340403512407540c00d0300b07040d0140e001c0c0e02c410004440150340347e0500044502082c85050051401104443d46c4207040000074010030545a2201300d5480c130340100180030801e40c1c1208400003104440c840f106180c1d0310b051581e01c0c500c0028001c075251 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 285017086 1250 285015836 285015859
    0x150b010519021005250801030201020a150b030706020d17040c030605100308180109050102060f01090c0903020901170601080d09060309062408010c050901020c06090402130b070606090c0f0806060405 87
    0x128010b00407514051074250420100c049001704440d601e20030310000f070150307000e14070000000d40e025944105400c41800d0005103d070411000038a4004194030403005600840484085c0e01d604c001c281c1c401010480c0e4480c801c1c00c0c00d9440f2008010248000360107a036484012800800c0a0400f00c002190440720440d2504004403684c41c0000144540074041a0300c170100203a503500200311135210b018040c1142000d80e19110403c40603041c04902c0008112404078040010394540c00c007140a480b0000b00240d5542d85c00188514041060f008543c4680c0704c0400723a80e481c0c0d8440711200c00d075640c52a0114002640f40b41c4000600340c0c40d06090344000304100002c000780501c4152900716006c100080c40110f60300309041d03a0520903542c64a005810081881caa6402c200000b0600010060401403404410301c50038405c451060308001d0700c004001400d01e0a100303507409008042e00b4043e804108408076140c010706081d602c40c4601050080c4100001c101c0d82c0c50ba400d980042202801c5a030b18507 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 285018336 1250 285017086 285017101
    0x2041d060c2a011b0f0e10030f020a030e07050a05060403110d1401050702060c0306030d081b0712020c031b0906240405120c10080a180f150b010519021005 68
    0x2880d00d0201800d03100d45032130716036290074440c0d0358003002088191107a905007071000050045080e42912003c0505440b45000c91f000c0f0000d1000341454540da070f50000b046108601031070300703103003441d440300f03104041d0300006103c1030f035030001100d04480d13000c400b03981494402d5000c0350041840c1c002c0900194000790110340c1051040d00103c1c4501d00e5582603c0040d40da928650000d40419207040b03826a00294540000a01900103603410401403100b46240904d00b000c03250140d8400e401c101c59500e025030170888400d4041110038060f60b030403809410350f036044030114800d03400c0d0412000d220300c40f84000308103251a9a1058071821000c030f000d07070340c06000f5058004040d41c0035201e110f025100082c20f801003810085011003804400605004164103420421500f2190151200480700c2c0c0d0755148680002551142d8450b140c41550250f0401e202c6003050104405070001c0a0b00c03041c103181410b1001c0c1ea00408950b080c0411125186000d28403e0040789004100c400c40600189480103100c1074 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 285019586 1250 285018336 285018341
    0x11b080901150605160201050909010801020a09080c09041e0b0403020c030c040b090406050402012606012a023616051204151e0902041d060c2a01 64
    0xe10030200090107400c00501c1004601c005034450b4000040040c000e08018804003400c44c00e09600505d800b50070100820300003042d0043c2a0b0028401c3e82d80012003c4449821203440c200411014018080300600c490200b07064200c0204000c010070b04081c0076511050b40d01800102c0d2030341040c1d9241e224a030601e0080e58500300642e110b40700e441038071140b14040c0b500740a01186c0c080c0c040c0030341490343c4403541c61101425010300100c6c140711140140b2a0850703900001da40071410420040005401c0443c005021318141715219a203d40e0700f044008100840d180458100e1a030542c3ca80c01c4600600000c000b01a585100c00901c0001000e10340c07001c5003001540710301481000e011003e040c40c50f0b00c0251040d01c910f4544480b01080540081c0201d001507d1094046985c1c2e800416006e04002000c0d0480d0842c84004124680c0ca500b020290704103849010341070b0780c4070080484444403890b0150f42e07461006054024000300000c40c1c0c3c0c42503110000980802c505001404c910020f440441c901 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 285020836 1250 285019586 285019591
    0x304080f03030103212705090c0a0c1202011119080c04211523010b030403090909020f150310050910030b18010e030a110102040b1c110327010e120c011b08 68
    0x45450300c800270a40807250b50301141d00f15040c644509143d00e08640d200c4004209040c65042035569910b06000380d503107041c0c01800d8441d010030420101740c9103128050514000030f0b025100a0400340414003c5000b040895812500c805203120441c0466107807450034480e200c04401003180c100103072941c4c242c0f8960b12000e054003525511a407940c2e00d9030244040e50004aa0243c0059840b00c810000000030f0303445078070802c0c0064900c01b0541c1800c3d01051f941d003030f045084603081e43c0000401407034017205910723000606000c070392007140d90525158012f4400702902014040c1507401c00481c0d4445012940c0384162040c80c4000e2001c8a00141d10580341d42010003010041016a01d0740d0b001c510b410301c21107054480d00b0101314185074000c030076900b4414841c0d415801d213990300c1007114030307003610400035603c41ca00d00d060040401c41180e00307a00c03001d15400d80d40301d910380c10500c01c004000c0011079882030030404c0b98601501c03a50041e07007483c050040042c2004000c0d8010303491401543d031104c119031 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 285022086 1250 285020836 285020839
    0x50406080c1c050d0f110a0b091606020c01180806040c0e4507091b1b02010e2407021c020a05090a0e0f0304080f03030103212705 57
    0xb08481c8030903842040210000d0254000300410080c0b01d00480c40b41e20284118a00007045900e591142c0d8540141882c00b5942440803508000c0054010402030113020743c00303a1003081251a1060103551109490340003410320140034100b0241c0781c0c0001c0e40320024080c1c001180e0441c02c0905000e8001485030040307a10031070b83c0500003600340ac001c01c1800311000390342c0d403000d2804511426a19481400845002c0e040e80c5074036200c070305410b042164002514803101c0c005804542d041401e1001818103040e0004c1c0040327a030030701158140f01a5a11445502800d001c5803081d1210002601e00c105007a00c41340c0c0c8030040004e6800c1c1c000c000003500301140700f5100200b81030204c9982114003100c410000394080c0141c40d0034001c07414040003c50308040540004a082d4144040c410300340403c00d03211001a600110b01001034040821001311101c4070f84010390b01e07550443d00d0301c010100313510b1601d039102010500e01c0c4083d644291280103000a80000300004910481070740b0403400594410036 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 285023336 1250 285022086 285022099
    0x9030a0206160203061b0409020306060d05150a0602300913090318080a02010309062d150510050f0906040b09030d020d0219020d0b160305130c031b050406080c 70
    0x14a03c5010b03c2c0c3d1b212080013426081d50520b842c2140702006540b0007041035070009001e014003008540103008060060400d4517225460302c1481c0c0c00d10240e0951580b01c0401c541c05140108400360041164084940010402c0e099aa80d1080d5181e00c9103e11511190401c0f0031180480740003d4a41c844491180300c2c4d0754000b005132480c4090305910445014400301da8011140d80d10056000b50700940000b403041d200403130603090a1042003440d0701d02d41e207a054810224805403110803428417907040c2038179032280300215040c20800428189080e02d40480280007002450040c00c0408034246d0f114104000d1005942d192156141000c82d04030b401c01c04e010b4400c003007159088900128080d18407220b81d500170303c0e82c2c202e0180c1005031802211020ba80000034810600049601140e446104000e1880c0d00d4080102001c40201101c100404d09168160074003840c10005000d00e2032141100c2d0062032030000c80c01c0181228041c3e080540c04140c1c41b900d800000101000049144130100900b116003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 285024586 1250 285023336 285023341
    0x6030e01090215130e070207090b060414130213120339060e060a05040b15060307081801090c05130b06090d0f05060406090b090c010801030809030a020616020306 71
    0x12401d070358000303000039846001c5400c00c1001004000103807101d01c1e4640000840c190b0382c1c550100000344156113000c01038014140034000303007840e8056284040f00640e456450189404840c0b21820f1280c6c80e218414a101c13810340008080035010344000c01521001e038034200d583c0b980d070898010b004072812008203202800d81b04499940010031011200094a4991345414684000141c82403120381164001c1c1e882ca410b28210004001c0c0381d1003078004000026041c100360909070780c0380030010140c0003010213642d85880151111016603402c8400d0303040590303440d05c1d004902d40441c0010305a1001d10341c604500c1e0030520405104e40412a1010f484102e41d88885203801e0702550041100e4542081040141c440c0354144080c140940c40d0051101400c45203050741c03541d04001064600307958403a145c104403428814403a6100360004070010051415130001c07000071b4800d40c2d0500c0003619401002c078802c4010307101803083c9046c003540200318a03030705c00c5290a0b003aa5a81130340f40507030192092000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 285025836 1250 285024586 285024611
    0x3100525021b0105030a0f0603060c030e0304030c06052a0a150c0503161e110111070f06051b130f0608071e09030c080f010f0227060f0a05040603 64
    0x1503000d250b120010502d48418203038801543c46910103031100c02d120759210004180d0032014030404000c0e51081d0800310f074145526000074181d840003118002c0c0c1e41c004100420000d000c6e80d003440102c443d5030038117684540c01116007500440301079030080b1720840e964140000422003c40c1d80c801982c4280842440190030143e00d504590b54032030b0403004a10104003140314802c1c9110000a0b590b070a140c80e1a8800406100c1c22401c12086a140042a03c0c441c01c1605c4035028014240034007211001c1b1402c05515444082c0171041072003018081c2d65448000c04c040c5c0c00048121300c0c003860601001643c1380300b134814900d8840424880e41c80305010074580881c285121741015800344071036903141d1100032001590401903100d44585035050200f80040040000c0c2c07040c0c00440100702d240060160b00780f8821280f4290b660801c44814150301c1040301c4008036440610f014022200c491003c84002031010110703d05204000c4400c03c3c0b000c01241029142d5840401030003a0b485130340d020b10101c144c01c0c1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 285027086 1250 285025836 285025843
    0xf03070810180f1b02460c05090f0c1308070b0703021504050d0810090c09090b0108190c0e04020d06031b03200105070c06030b100504080c09060310052502 68
    0x1d002c140140c011070300403040700b201d0f1000c541c01b0014480014603ca43d40d650800309001100f1803001400c141c04844d02c0070b00101d24114802030105852044007403034001e07106000c0030300003425004205000301c0e02e0b1810714080b91400015201d410200c581d003644603002450030360401f0504500501c00c81450119007000b618010340620b5001c0d0040421107481a015184408010103200107480c012000264074a41800b030021f03280702580341c00e10407600342645c0c2010f64103860b203010305200201080c443d441024084c0381c003c034512607000140900012000b11502c00c9842c61143d8000e0004c540d44201c0e41090380074908480c45120f5600d169245c0114422012100b44000b6180190562a01c0b0045501c0e42c03880c4100c42c014988903152803c1030396560000711861300700400081d0764003514a603a04180703003081c4001c00941030260800346040c00c40e40d500c3c040880c02c0c5010301c05580114055880c100b0401c28035101c49a000e11403450100c80303580042d001c407203202d0301c91030034524a580c0103030010 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 285028336 1250 285027086 285027131
    0x1517010801051b2827030204060b0307080105100e030303041406090d02030a0503180303041b050a140607030504031a160e10030c050903010e0708060c0f03070810180f 73
    0x30102c0f419100050f40c070302d01364810720303619010500410f00098600311040044c1d002c1c1140e101400c2c0c0d81c0007030443c010320084407a81d403c440b811100810038403c50b50703000040141102d0b41111080401c4028203001c446100000e0403007a0948400b20600003003110302c40110901d80c00050440748269640100140da4034444400d000150300700b040210380d1503200314020b40d800199044000340241e0f042200320b01c0e6510456060b1100384c05c5070151410004011030080090904468003901079042c02a07400d8814003454903180b05060015a410400d030083c015600107640000c0f84503140d00d0050310940050702d086a2800d8801043c05409921900a44001010742d10142000c0c003018051401a03004060000306001848420300c08100103070380901030200d44c0784044001c0d00405c0d103450300f524074110380035200c3c213100c40c0b0034041a92a90801e4054944c492094074290315180c84204424041d074207150010b1440c0502540301c2d8650308034540001d020211158020001c50584210b59010480750 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 285029586 1250 285028336 285028357
    0x9181c031a03120a050c0a0212010905101112040c0e040503070606120b040803102318010602030304081b0a08030f061801090e0c1e0108010905070203041517010801051b 74
    0x134401014480d200b10098140d101640307089031031034005600003500c00a0b90030f400d10240c4e034548201d0010801d0070301c40780caa0180c1c8190140180c001151108180d801052a80c88128480f600010207200e204110f43c001418035000407481c0742003a0510544a50204030140c800c1820500001030403400c28000451054004006450341d4584d0ba44d81422640081d1030a01c005620140200399000c2c446014400d44107000084401503c00f2014000000122014501161a030400420236550007204607940305500c40020f070364030210000e005042609541c0e00c00360b14440d00850000300304030200118060320500180001d031396900c00c10132031034601143c03418405548550042041c1500c5070059511241910700795800d210000020918114080068561721050000d000416580201c0000d016000c0d004090010f031401e404040d56910582c460b407015201120444804070b40301c6d030740078541038501e803c000146503502d40c8464060101a24100383c2d441c0c807107a61001a02d01c06040f5521a00c1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 285030836 1250 285029586 285029623
    0x15050a0e0609010b0d0b090703150b090916140301060801030309080d02120306011b110906011814060c0f06060406060c0507260d030f0b04060509181c031a03 69
    0x1c1c4100e10400790450031018041a0329001e40006e603a4625440903c2920030343d4000403040000c01d08101c00c1c0690340d019910302082040201101d48510403060780c418082c00481c0d1030140101e50803a038501d080d1400342807070780000c400404c5d96a40240c2c0320b8106c901a40d14500302d5078131104015241c54440340200e002da07110705070b0041c03450707220405107a2024050400112560100c2028904135500d4034046860704e5884c003040c540d614040221580041081c83d00301d444036035a004550304058079000c0d00384020f580d940c42ca40ca96072118115142521140103441c0544141450241d442d01d06a031041d03c102d08280020660354441c402c0780d24031a81020050040c2460710409075035030403010b1411040030006604030078481004110044d88880c940d0340c00134070320111102010885480e21b003410311680c206102004155910a01281c02100c1c0f9a142c4140800c03450590340f03406880c02e5440d03000007180711610b0a4079095805a0304290408540c0c01090f1640c00804d0b45039544541d58120451 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 285032086 1250 285030836 285030839
    0xb0303030f190c0e0910291c050a0c0f09091503050a050a0501050a290f12070609051002120d020706020d0c030e07050109090b01030f15050a0e060901 66
    0x9400d0402600401808048070309940b1400d0b422066403003c0303080c1c0011481884c0e071008141000381d401c80c0c1c494904a1b080c0425401c0400303000c0080150041c030b00503a0240340800c00782240c40b45c2105c10360700a503001c0251100b0181811400b901003100d03020211864020703044002401541903021207021655104c000b60708103804800140342a0508801401c04440b000c80024010822110501e00600003003462900c2ca18055003504c0d001049681240d04003c0d44204070031030a150700c000c20381002043c102c1d9902090200d180c400140c540745901c08408034540c0c000d04008036940301540c60315901c05040c50346610900c58100803130888400180d0004e1041502041c0711000741240501c06c180242c03800080f6210402a0f0b08080c003003503045669403400400c1c1c9501440b554040c0707140c10700074100d82440d100000e882c0c60854450040105c1d00c07102d502c10240c5c42a80501404500f0030b07000c12291249082412031200580241c0e401055000004100d00000095182c41082e0080114040340e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 285033336 1250 285032086 285032101
    0xf0a060806100e12030304051006030804090e15010e070f080402060d091e0c0905150306010e06150304080a020d090f030f020105040b030723070b0a090503040503030301080609010501090b030303 85
    0x10840003a04408010f000c2d007030036000d0703a15030448a450b01d04d844002c548904003030801781e0401e034548402d0f100381c03803810700300700001000e240035074003118800c4c8030001d001c4003800c09507801d10154140c4221807421a10022940c40140c00455004240654a0405084425400b600c41c0303101610007a500c888184000910101103402034056a03124240001160090200c0b04919030760b445000c0350b810304580400c2c0712407202c500c6250791058100c525403400c01d0804c00031984900d410700640c405c148001b00064036031780700c0c9100003024829043c000e07543d0345004d0410381c4c0035130090003a50300103016940000b140da61188080070140d07001c20403124991881e5a49034260003044940c12070501030300380700004480030b815000d90712074981a02c40b88641c0ca09484681d41c416000903002c88400d03000d000141c0031641c00d0a4032036200c0c403080d400140c0d030451820800d2950089512403a41480000000b19032403501040346805044440300074030031130741c88000400035214241d40c00b40e0950300c180300041d01c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 285034586 1250 285033336 285033349
    0x4140103060c110f010603020315041218050607150b01080c0f0315181801020c0714030304030c030f0614070c03050703170c07050609150402101404060804020f0a060806 74
    0x180074a0511901510f40003400c0c90402103210b074410032595480c0000c005505007801500810008070810070788920702640e50081c0c05481d11030100030030a80662090000320394440380c2c0e0180200420090301c907000c521f48210200030fa01c04a0300d589040400b040115402021110f007d040041400b030304003c03090f60402c01035000103003031a10301c1c14560003019290701d6088500b802034144095180c03040c0b40c1014501c081a4000381025450f038410064103c0400000c243c002c141e80c1900a204102071100340040d2550056030400741100d000980d000040010141c81d600340c152041c1c0007401000d01c251016121a0411036040780815100c441150000e4400c400420200c0d1103030400400140801e0103031010800c0c101c8011a034201c00042d2502480001c03c205a40009504000c0041095035a46482140400f0300004d0080036a03039250307940c0c2401010390000e6545050101520b8540d1420010079203031007a103060380910445440c0c40c2845c1040138590080c0c4405440d4180c0c4c6840c0c1e0424020f8 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 285035836 1250 285034586 285034601
    0x121a0903090607060f02191e1e0e0a0905091c050910052109192a03080a0c200d03080a0b060c0313060c1509060b0316090b0414010306 59
    0xc03c1e5507261042640708a86101600e81c7d4245803040061141e445407001d800c69400003009038441c41000c0e6046440c5622445090300051941225840b10700f020b803040e80d08001ca0001307035500c0041861302084180041c0e2102c0e10540b8a4030481300c082000c00307195581e0101c000c9252000880400c90f4026a0514046021000c101440c1241c0340c240000305000401c0748030030a141c01c2d00b511100388400003804010110400074045845140320501e80c1c1d036504411300580c01802441c0d10341d100203012040b449080780041d81c000c0d0300d986e0f4510096a0082444000e08800c99000c03642600d00301890023204410f02c0d15460107010b84101603030986040c3c4003007400400f0402c0d1941c40c0c010801e1103880d110701130b100d00030b0000002c41d01c80e072016031010141081508202d003081035400c4007001041806225503c0c46110000004104ca040e00300000a08804209150144207081e00f2850180b10003a110044454404080024407050001c1005031030b0b100e042541460001030041c030100314558010070 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 285037086 1250 285035836 285035843
    0x927020f0c01020a0c1709090114010e0a03060b0901061106070309050319170c070302121305040507020604030206161d03070905010f0824040b1b0301121a0903090607 73
    0x60408200c001402d0070fa9224005000001e140c15102004001445400341c00485045220a00301071001c03000c140314600510401803040300c6002c1c200a1359024484440e84510082d01403400c0f0f030b07100d0924002902148182c980568404800010010b00c928100d0001c1000c1901a148603144e8034401c802415920f10181c0c3d841c0001c000407504000d0140341d80d00c50340078a80b60031401380d0000151511044008284100c3c2043c204901b00c0080c1d40818810710384280c00240c01e4a40701003140c03880507150341c2d0b040360b42c00c01c1c580014030200035000104030f84540d10950031581250b030f4442c454405410300308619004a52030f42c102446112180120000c0039001074101d42806981c0c0c40c512059480a80c44920150b8507014248000c0d001407104004103070040709100034541108001420380040100040c2c010306401c004604d1131305140300290241ca001d94402074895844613440c1034a400c0c1e42d1412141c41008164290494009a00091140640d00003460030310310030307006007c95544540400c8 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 285038336 1250 285037086 285037117
    0x4030e030c060a030606090f030309050d0305070602030c120603070302030d1b0c15020d020d0906050702040e1005270a0b070908060411040e1f0b03010b1c03092702 72
    0x6606600c2d02d101074241054140d501142c1c2a01d860000781c00990143c01010b207840003101e0900109810030401c40444005035600200b402680c00d040315103000390750004100500000074800d803103402c08064060380600802174100394851404055483c0000c1c48001d40542108440004c5030780141000041071000c0d0000c040708800e15595000c0440c4240c1207900d01c4065842c03c40d401300d40c10090a4cc540c00c940c001400d14a100f000c000c0c200040502c1030104002c0005a005d08549440c2c01000d01c080d00c0e1411110305940f440d29810240c2422213200d83c40c0200b141c441d900301154040308010318014500984072020040c3c5802070031007001407800c018400005400120110200041031180e80185100404c3d40410010402600e24140807000caa03407212480c0d4542d00c1740407a104400411700d071800100700614a001c00c1c050500c07401d040fa40008002840e40340d861014680b0003181d44299101021540c1b10452274a01c41c51801c0006207201500400c80b02104043c0d000740100785000182 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 285039586 1250 285038336 285038353
    0x30307020904062003012106090813211a090c09130b0f24011b060203041106030c1204030c0c12030f0e0d06090c0506161203110304030e03 61
    0x410390160082d0703002c407500380c0d42c1d0b00c240282c07406200c090032818445514092665142c81504610042c03c88108608031013211661410021140d012410451744443d44c07a031108500243e0b07aa0000c000c0c42030352104c0c00020034203603d20300101c600c2201701e603003c514882802180c90410000701401009106030340b245140b120225074507005440d100d0340441c18003a180c448645000b006900b0b000c3c000d03c000070320903814000f20241ca11200a0b00f40910088014500c0c0442e00490b4024030210f0305860700c10010341da08080c48120f80042d03200700c0c060388407481000b1480003881201d01c400c072110310394420244410742d40c2c00d0f8240320041c1c01601900e0b003141e580055031980d000c0c0c00c0055118280f00b9084004003001c050304001540c03141501810940240203026010440004103c90001d05c0503a940c51244100503d0700307491400b400b005051580c44d078100c103051070b500080c803c00c240c1d0800c14a850168085121780100c0000c08404403040c2e00316201c640d030a80755000a00a16075040c0104500d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 285040836 1250 285039586 285039589
    0x11e0908090307030803070f050910050d09060501090603030e09010608040b04210f080a050c0306040c09080f0f100207030c060b04091202070504060b042313020f03190e0601050f03030702 82
    0xc00000c2c600803d040c1d40c1d039003801c7d80060b0008103030144c4041808000d0200102c0c1e5a244100040084071500744035a46260350241a40200290380c0010b04191a000002c10085000e51011050324801d44981c00411050b0302041382c6950f02f4171803000080c14520006001440c2001e58540051148801c030303107a407942140050740b51030b40001c014001030201201088082c1d11145560b088089a1802c1000b406c2402c2c0003611b5110040030a40076503200c160715040584121549802405008181e810b02d62041c0c401d240c03194a406000d001c41d205144e81120b00c0046803089481b525415168a0350903241d940d01c001c09801c50f045259840341c0c1c0c07404800041184848900528980c590180a003a03060604010072618141c00c1004840420b000510051042000301c840100700f09200344c004584401c00141c4903002181028403040c0041800d8090800c0800034501030f5400300100500141c00ca00002d0460701c2c2003143c00400c0e40071704010091424071948190031004040c082d40d02d403004680 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 285042086 1250 285040836 285040843
    0x90d0c05070810050f060402090112020c28230604060902060d15150c05030d05040204061502010608481206060906010503060105030711071a0c010b03011e09080903 72
    0x301c3c00c0101c0c80d200c1d410450455a00f1503960ba100c10100e90031818401402d000034004c2c215240c964410a5001440066110003003017100401014260100e02022210300e85000c140d221a8040b51000380007500044103419407649074882c800504001c1ca15985c45842d520054000044103980001c020000100702040600861030080c40c4d0725018030246142040174000c1c402c04001180c10060054603540000d2400f204542c0103018643c004242ca8845000041c0181019400303c1080a0500e404044c0340d5010f4100c441182c1c07107001514100b0b84c480194000048501030900d403d03030303080ca10800403480d4070301c2c5a103503440c0035480a862415005000c102d01100c0658030070740c503030b00c204200095807510030720141e8042e0b000e107016811030070040f0001e005c600018040030140f0410001070310968500f00711000042a00056005d140700c40300062046036841032801044035400c10550b280036083c1402a04c0d030081161826900c0224002c03c0040248422403048800090800c00d4030002e0381c1c03c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 285043336 1250 285042086 285042103
    0x90905180c03061603020c01020d0e0a0b070e010804141218090c130b07210509010314040c090b06040503100516030b030c0909011b08090f0303090d0c050708 69
    0x880305203040100168100d8906039901c18410311070380c002c404102c6415850701c40341900c13401c182005a101c48140091a0280c043d2000c03a00704a8505282004403d000003455081d0b1400b0f0a0815081d4071000403c032100150240e10300e010480b0080442d000403c0d50300d00001a00743c8009036041c00a00c48516280359005413420903260301010a690030318640300c0401a00129140e0340c0c0d9241181440780f20181d101d1070b10982901d80000300d0550180011103058815a41449a040940101850000d000c50f0002960b00380020716100b0040203070200d8900150260303401440c150082468200d8410282ca80e92541c00e8001d03a00f0712001070140c41c20441c480383c00340c22080119644c0340185071740303035404051a00c001c105070400410104c0d64402103190690b40c141070320b01c1c0f00c0c2d07580c442709940d0140c610a440c8904441c01440c050004030b52002c41c0314000c105410a40782d00d9100350200564034041a1144c4031290415006204101c0c02070400340d030b09520801c2036a001554401d840790a00205 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 285044586 1250 285043336 285043351
    0x7030b070e0a24031b0c0212060f011409090a0809121c110307081c06170a02010206010603020f0409180c0b0a02061b030703050a15090b0906030a030f0807090905 71
    0x1400c3d803104901100c44080c190101d0a032504008000e0901080404101514410414003801c114800300355111901c082091011b40c400315526401c100301181da03541424421181c0032050721440028515001d1411405111450010a8a00e00711789038a41603500005015a102c6850305440500001c14400501d000c001c0301da80030040d800261015080f07002600500d0040d42040101800140d2240162001c0c0200071900c040d12007030b1001090b000f025103800c01c05014041c258604000000080c000b200d1034401e80c240c130640e903070b65101901039000d071005c0105000700c144824800c441e001c0d440170030f0200e00764210f020502d80d103403500c0e1230012481d0007881e8030990000721010360b0350301000000d801c500000400b00e50940c00500243e1a404050100340805440d540407c00101d2150040c032205520750405200385070381c41240f84000d241052149000f031050400050380c40c42e0208600200da44c140d16071308480002c00c0e0040341d8a600040040b07092140303440000c5140b0076144540c600c82c01d01c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 285045836 1250 285044586 285044609
    0x2a04050a0f0606020606030c01020c03030307030e151320060f0915030c03011e0501090e07140c0106140d020d24290405010b04090b040603081306080c03040507030b070e0a 75
    0x81c001c0c181808c10000820300d42c1590b0000700702c001542c030008100c0744c3c40122494001130449103c10900d060045003805030b4098440d131800d0212941031140c2d03000c403641c800c1064070810400500030302c004086940b6059800300c000d000f440c030303aa5102c00040840681c010714028055401a03036010680e0010b48801591040c040018008240c04905000c903181c94503900b103120f01d2410f80024010b105a0003031115070b20242c0d0101c1c4526000d00b0900050a00010607141c54840d10f01c02d4900074400752180c0000c1c0c0d0500788000c88941005201d6110554014102807034201c220746941c421607104026211b8080b04000e856904509207100e41c1031020030303005a104086070501c001c0c508403035404209900c074510b0640100b0241401004440880f0000c00010801200c01c40001e002400554400762142d0b000040710710f841d003840341d00202610b41d15101c0c0d0d202070700d800644156a00003154014110790000c542800031a4a0202c0241d218015281444180700c100020685409540e40181003912 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 285047086 1250 285045836 285045841
    0x302070b0a060308090103180b0109022a03041203051201080102040f0b03090d030b060c0114090118110105070f0819110a0b04020f01090e07050c2a04050a0f06060206 73
    0x4000452580140554000b40300283c115140c00710f5a00c2240c109905041d500d80300840c0c420440d80b0b4a0001c0c581011005103551b83d0b485407240a13510039091001c003d0106883c0702503030880522541c585164060065040a00307004030003120a10020b019800c0c45000d000c2c1d04040c8200c02800ca008c0c00c2c5250016072180e18040c00110000c49039005900e03c10014400c00080410001d403004090010307180201e600c03902100890b00c54803421490403500d5007843c60300e0401c0b83c4c100710564094110a80200405034205950025000303481c3c00003040400d509007080465032054011f048840d0042c00382000c070480c969a5500310b5030192408010f56180740c907070403140c0d0341c22000081e29016040e0107410200b40769614580060002007009129864610488445911600f8a40080c2184200c0710750b8600304030350090141e0b002601e54010313620408006010206420188810200340c000500204000d400e00300005414011f01604090740c0d00e4600052151a80c09030600400070390f006843d2a0 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 285048336 1250 285047086 285047093
    0x304030e03070e061c020112020f040512031c0c090b0c0606030105070503060a030201030e01090206130e0c130506030703151203030b040c050702010c05071211100f05091201020f0a030207 82
    0x1c0ba41c4490f804100c82000c1200307603217450701c2c41000920700c0f41810b40000d08a01c0141c5103503a0f03e20036105410b202152561a41007504024070a88804691185405480344400d40d600d01c102944101c0200105030b601082c8981504200d10304607140c1825665161914105e041c2c9400117810301010303601101c03d101c4603041c20720505801030768526002e0b00d189440e20104080c81d503113100007810543d4900403c001c50400390b02031001958004c1c140c560752250b294040115030100e00400748015040004560b141241800f00d41c104c1c400358290301c80b0980360008008407504010030580925840d0182481c00c81c100341c1181e005084036106020210f041030500904440008061500035490951101151a004000d603895290b0918249511341c5051400b10308280241d800480e2031400180c00d002041442010128506003e4521060503031003031508803505024030101c0c40106004010340521424a201510080301c0c5150026252200314002d8a000d44e110102c1c0d900041d5001c240700301003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 285049586 1250 285048336 285048343
    0x1b0b07030b01080402031e0307081303140105061f11010e0718060f0524040e070e0d02091824070311070b19090b0403030c0906030c02100504050c03030304030e03 71
    0x19201c2880d00602038640f130760101e0740d07445213420013117080300c00742089101c07581040017110400b50b0f0052805071105144030780400c5450702c5000866159061030a444032900c814071640d071003604000c00780114041c90462807407003034480d031000d01c04000c1e00e00310319800080240a101d00f01841200100445403400780364a0348250202681c94a0508140040040b0041d03801d42c0d0f019030720100c80d1100012800300751900c100114015113034220f070012400007038110f1100d40461080d05141c0301c14445086050030003404150180c4025404014580030645407001400c6017550801840308541d58400a5130032183c45281c0c0b0f403040f03c075a003506420455500c9d031600504003040c04103a02c071403c154a42c0e489000941008041d0903600a05905080e43c1c0403543d04008081c682000446281e41800d0070000c006d800380215035808201a0400002c1c00381c801e00c41c1e005e1001565010b0540f21001940c10805410050026a11885072002c8004590384c10b0000f14000d0740700380c8804107900868410300d0706 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 285050836 1250 285049586 285049601
    0x302040b01020d02070b032206060509010f080d030b03010e070f080f01060602100b040f0603200a150c05030c0d11011104140f0409050105011d0a020901050f0a1b0b0703 74
    0x1150424000841e0254001075140c05031b440c4c10360700d541c0b00e81c3c5400d04088000f13444410144140044081a014400541e0008007540c00c19500c440980c1e8036012030111400c6c02d40302c3d03c00242e004000200e5154426807050f4065940100042407441840c042d03540b800c003540c0c1042e80400d06c00c40c01041402d104021a4207400710800080c4465454000040d4980700e0480207440000c1c0c0b50607041c2d485a9403a4005e52901c0d1181c1000c200b0340d51603003000019111a41e450f042d1800003801d00b001140303003003050b0104546001d0488501c0709100401101c40074040c0d2001c40d414030003444001c5041c9414050848140000e5482d0920207e0340c0b8280c5007521040b0401c03d045040800c030a2254403880c80e0482c0d0000300584403090306005250105000b060702002c05001d0354640030011550345d0305000864210301a85400306519110781700e14900f203105809ca901e01041c0d0410449004440318806040710030028180600c0042481f00d02503044510110200c8107880354100b04a0f0b4580c06125001 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 285052086 1250 285050836 285050839
    0x4140c0c0601090c020622020904030305180f030406031a13090203161a0a02030c01060b0a021218041e0e161d011e0506190807050a080a050402010c1b0302040b 70
    0x250101040000c1e407207007005021f07035072201c03107014010301c840c13513801000c0400e960b01600c070007130618044c240140200310558054482a0b034801c009407200000084882c20188410061441e0504d860010780050004688407054084416480c01c490742c0d45840130001d09401500c003084003103c62040606081c920440c00c01d400300e032035509014200c0c60000107030b04c401c03000e0241035840045e054241d1450052180e0550150f0070039401244501034403018205504080d02100c0e401001d071401d1007054014a00d018490745135480c2440071518190300301031681d502c584032000036502c4540040d410340e00c04050211043d40031032920400403d1400110006000843c10554030912643c04010103d906210359601540300084502c0042c07030025200e00240030040c403013907403100702061800c041c010514541d40030480300d0000035110360040045405041a943c1e07404100e030f4a9070b0340b281c0240b201620590400246c5012080010344132a12100c0b01542c0010822803185140b0410003545c41020146 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 285053336 1250 285052086 285052091
    0x3050c010e060c03120612010f0605010207060306060e06031e0721020705190c050a140a1d01030618021005030f0a0209010f0e0f0d03110714060a030b04140c0c060109 73
    0x103420341c100200c251585c4100b519140c000584540b000030791444c180c141d02640c2d9518012900e49481810751181048031001c0c0c0a841e14150f4520f4190116440c0c0d116840110701e6517050385240b0300d4040d00030f5600000100c100100e45400da680c400100e901200c034200882c0c092100da9841884002280c1b0a00242c03e000b9460140715954054980f6a04880c0d40e031900f8800030450f040190030105c1c1006017402070214640b0a03510614603060702c0d0389542a80c040c154165010030001f12103405000d0f15080a9001b041c66486c6607144002403661a080c2e0b1a070000c81d404a0380140d80d0b101c1c2d0f40115007201c0c1d5600c0d03224140180b1403103015001900000c0d10910411070400980d80081c4121702c60703241814090b80d0041e4642c040388100880d050300550001d4454000c90415400440d901d00c821740c484102d0344000d885580904020180140866004009100e9030103264030a400c0714940035009880485c4044046446142d0600141e9080070320714400310300405104404c1019600501d200d4509 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 285054586 1250 285053336 285053347
    0x2112081b0403120804020d05010e0a03030b0d0506070c1703131e05070b0c01020c0105090a0c0e0108030d0f020909040c0911040b1608040803030f1e0f0106050d060f03050c010e06 78
    0x5150708040f10141d9030342481282000542550b40300c01c600110341d81c103e80244001142c6070852030704c82c03012134021404240b030301c0582c000030308005042c2d4030590341c4080284055101c40c40141d908e50181c810850f11511120680b8140124a001840c003ca45101e0b0301c0e0181711952900c401c0ca011354001410603460303404546004504001143c100310342034086a00d070b8440c2c1c0c0724817a50180c498400b660b5034541c00c01081c803d00c11000210742100704c0c0035090108006403100c10004020400b032084006690041c06002c480c445564000200c084811500603e450f034007001180c218131044a00b0f541020107910200804d035800e0103011808840520414641810840c625005000303a401d915040d5000b05c1b5944100080720007110040d0440104403522864140b410350707141882103da14160350220030080100c4103600c0c40c424000c080b41345407031429a0800d4000c0722580c001010b0511a113444000001c3e2500451181d1406140640e0140001c0030f0484000b401c004104c000843c06504100b00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 285055836 1250 285054586 285054593
    0x120213140618040c15110102030903120105032a060723010c14040911070b0406150b0306010c0308061f02030414030f0d0305090a0602040b0a03060806060105042112081b0403 76
    0x78800305541245c651440c0c00382541c2800c8400c0d0b4001410844158400414019107410000240c44072018072004010141e0b00d0717a05164480240c982c0c681030000300d08001000d5480650903000d10000060403031800d141a40d02d4488180007011800c00220780d105460800c094401e0080008484c01400d140c0501c01240025000380d22547c03042c0b06465540b0302c0c404964603050b5003110411b580004007802a401d00c3d00b0160000e0241c500034890120a500c1d00141121548040d031340300b180161030f11003036840c2544095842174401801c40d54850252085407800340c002d41c5603407001c010554019601c5504051801040384034500c3c0107031180d801800780c0380401c0c4001500c88400c0c0f0041c6804a0389884920903e07150484d0518000d010900100d00403920b0031000740a013070445c50a580601001d56990300441d16543e0950b001070002c0c40401042c0003a00403040701900300081c507880c0501080f003580394041e203080c2d01b4514000141c6040c1c1840b9402c6094513042c1e62804294075254a401c0c51940d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 285057086 1250 285055836 285055853
    0x607030f120c1b0c09050928240608011e060e010f1208040801050c070203010c08040b0c07080903060a0209011709071403010f1b090e06090112021314061804 69
    0xf012440b50040000500401410455880003010300c1d480510540c02c0c905101078890341101508d03121041c0d8040740c8000c5080b02c036124032100e50400e0040071800701d01c00c45a02da080710b00a010040503214000090118024810151288508080702e00104030422511042c1c401d0740d17005401a400d00b500500015039811000b9040381c084c64900030312080c49242182c01c5000d65402501d255103000c0410922a042c0e100400006100301c0003003001b564036400c1034034507803c00e95011b07000b0b4070035500141c06210004000c01c5900d0192010341d0030048140c0000c0c0c07030003c0440e100700c202500444d400f02d955810001c240305c0c1ca612144007000c540703130414529985140b988140120001c80c0e110005d4035450030360100c1035000c81c0d0380c800d1011005000340d0321802050381d040e000000e4110315000407900414004035024030b0f0000c05103402646010424040f001300c0f104180d9000001c0d5500315910003030740c03003040607440461021300841d01d041410843c285090500701d007402c030060300400001401c2c00 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 285058336 1250 285057086 285057107
    0x405060906040513120e120105070f1107050406090614030f0a11041b200109020f10090b0c010501030309060804030c0210050919090b060901080a0b01030b0607030f120c 74
    0x60b1070016595888191080c103c2d41c0b2a01c01800503010b89910389007080d0311001051500a041d50084296100f04288a08951080720394400094114141c00b64083c030074500410305241500455085540344c0b0006012202c0952111151031340d100010000015541100e00c50301c00110003900502000b48040b0f612681030f803c00414400c4000d51108082e6a580d000410980070084204450f0050400282c07058407084004100c024141c200300004c2c10303050140100d250340c007510100d1040c800100784410031041107258003d01030700e10710226182101070050142d41e1034030f20001c581d651460800bc2c101c2d41054108004101c0010100000329410503800408194140c0c0d174030702e0042c00030307000300c4660040455880e4402000c503111292820150202d100740c464645081106c0c9031a03404100b00e501c50151001d01040c8001e00040b00340300c00e40d218072422181810081242e0309000e0001d03e85902108088010440000701d400f600d551228184201c2c400b1050300b00400580040080e0407035501 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 285059586 1250 285058336 285058339
    0x3060b0d0803071202041a1b1b130f02070f15020301060801180e1b01020f061003140102160b010e06010903020f060a030b1c0506070503040b0f0601031b021b0405060906 74
    0x707040f1031048013140d8120f03401000000c20918020f2541401c60f48180e004100541001140351100401101c3c0461031022040251300f100c184566210306004800340340d031401100b00ba590300c1c48210280014001003007540d00ca800c4010300d881c9146801249541443c1e02c0078503051050006224088d002240b113030541d80444854a4900f12000a80015000740c2c410415203004004010b0b0102c50715840c840d01c800c609030240d5216030b5440000603601c0000b1100c4440603c0000c5017080441c04620500101c101082d00251a18882000c04107450180920440d00d82d442100100300301c0484001090300650700b4604001c019186400180039041701000652241d140040c03900038040c041d034041141910090030700541e02004441601140ca10007009850700c1c000e05000802551045080340d10035940b00c1102ea1564541068000e86810001c1109040c181e0761120420012680e062201002c1070302c2d4010100782030070a40841540340740d00c121074012820441404180c1d03460460280d8099030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 285060836 1250 285059586 285059597
    0x1060504081b0f03010c0e210c0d02120703030c0b070201180809130908180907020715050c01050906090c04020f0f09010314010f0905070c03021903051b03030103060b0d080307 77
    0x2000000145032040129030f243c1d140d8071b030413441025690001d41648215400f01d5500b0341c240251445040307144002c0741381c0c107015002803009000b41d24195918610141c0045d0500c80c1d007120039052240352075002c5d0010340104500a1b0344200f08a1142c22056101b8500d00c001d1003985202d0403c0502ca9001040003061342001048800c0303181c407510748141c55142000c40030f2000e0317500ca041403106075101c2c0904c00600760700c0c0441d50621341003241e40140140d842e94002c0105c1454410072000d202502000b40f000c2001c100031034200c0080900546e0f0040d020786000c2c0155080c00301e8402e24100c0d14107285030107140184034041a440d2004240d07210303c55120002a90f503480800100d0040c01030188440711941580000700300c3c0111100c2c0182510750318502000161a0b0500549429200150090050780580d041c0d00c01041c85a5000c0303030982c0301c2c0c200319003020344150480ba9804a0f0300d010401d1688044010410320409002e28920820280c03140c803080c2c1c82c40e4039503405603c4014032080500a = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 285062086 1250 285060836 285060883
    0xc01061d060114090a060e0406080a0f060b0406090c02011a09160305104b0302040207020f0402031305120c030316170703020301030209060f2206090905030408060106050408 76
    0x6240f0300301ca440000091680070103e0700c1d0a4090100c120510308039001e20300d00301000c10b180d01c000407002e0601d0303003002c030811003503c4a5862801030030044000c07540040d10340c140011042e819010f005c400382016000130840502d4030800c8400305a018020301d20440d540428000c2c054001d410740342202c0c880d45004151551400d4001d0a0f084c100c2d4009090104d43c021014101c00c002d2001d840000d84203c01c44082901d00e071401074440468990071490906100d500300018502a070060040178405000c6810303d4101c040001c041f0f80003115080f520781410b03c2c15100700102030091706013040e50070f00414103050f12580d240c5c2e500e0100412501000c040080326810a40c00360060f40c60380604040903010b1482c050100402940007803004034040c5071590082112442e141500341c0c8030910150201807112558880cad4641d011103480e1101e00c05984c4c03800882d10032207a005440d0058080d2300110b94607854003c00c5890300b01e0581c418410400b00744404d00c1500750110701d035001c8000c0444150380b2030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 285063336 1250 285062086 285062117
    0x60108010509071107081608060907150c020d2f09040807060915050a02090a1721070515040506090f06070804020127030507080a0302030d050901060e0403050c01061d0601 75
    0x22005d034021034207502c01c500c450800e50560f0440001540c1a440a880b40c640380e00c220582e440410740590b42000b4020a0b448035290702c175030b0504d07801600040440445003001c1d114111888812241c00e001082c0e00003860182d1850031650011200e010f8912061034a09501d5802c81805254401005a51140c000006102001d0407400364003030b01d60005c019900788600804000d5018145c01400741641080000d1076045210910f600a14000080c00303400618204440800300006400c2c0500c080520042c40490b01c1004030914800c0656503c02d624205800d1480c034010700100700350210381c403816842074070f44008030b406c41d00709106040c001811384031407005a032050b282008000740192400154005800942a0401182e004101740e07404e0503160030345282c65083d01c0380c015025a1007009026100b075200d0344040e500c20509000008c48945607400a0220401034400742c001500c003080303c401c0314000388220001409241485d0905450f04031051a000070024101414007040c0b500002c01c2 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 285064586 1250 285063336 285063343
    0x1012060e01061505190507050d140c100e06151005070302120d050601090504022704090206030c07140102070309120317090a0302060c0f1905040815040b0601080105090711 75
    0x82c0442000303d0b24082e04a0750000c0064000090a810000380741443c2d03010359000e1022102c0d400e80000c0602020407030b10303800f610751088000500c3c0c260303002042462051581401000c80140b8220808103d04d034000911615000b0094480a242c001c00480075103140d540305c80c6900003907020300700251500030609042c0c0c24207002d03120f0300b498442c00142075516a80658006481140240c031820703c00e5864009020403409002c206501422010044114003001200350402d05800240003244001c01ca90101d40c03141c1007941c080308644408100e08040000311010f8403c0a0800da00031030420f2890b0320001c00724142849940e204610040703900c001d061050f9501d04001202c102181903904209802990b00c40450a0590050044501162051050b141250360440c00705246c142000350707010300001205800185502800010000080c0d2104148001010703103d4000b100e130103034a07250405c102c0740840100028104805900144040c2c0c1e1103643c2d15410100e2850880e107007402c0808924074 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 285065836 1250 285064586 285064589
    0x7050a0e07030b1e011707081302030a0c08030a080112030c080315150a030c0512060f03100c0c020418051209030109061406010906110703171605151012060e0106 71
    0x4105a132484c080c14a10041d40d410564180282c0c0c840201000350903120743c81c10025144000011141004203240c0c0c01e0107160200c5841c0010306072813000b00c4a5448400c3e11200d544900c20681012850601080c0c08c204c0050040c1018001c0d0a1502101d5500401510840c1001006e0000c04001f0821540116100210032200501001d08100c07000841150941002607010000703804e0003107884055110f003096414038403840d910400c003a21a40b04000c510829008126018030800b100107503249001d00522550302d002e134a074a03104c0f002034014442501d103151a000720034202c146162001078000600760107001c003144052600d410844000034003401c1a1000900381c0ea080002007012000504503180c0182c209032a11607840c0d9883c0c03025101005103002c103400c03a4108110030408030340c109518000d95881c0e1b5100c03520317000d10010343c2104288244001c1e0380507804602c0e00e25440310f542403025000b18440d894501042c0c074029022141c200100402082161070740f502c1d420104094204c0320 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 285067086 1250 285065836 285065839
    0x2032701021b061b191827150b030103110d02090703050f0c0a020606240f03060901090e07060c0213050c0903061b0706090627050c180f130503030a020d0e07050a0e07030b 75
    0x114030104580d0307060420351f807504c8640080d151510420580302d104070142e04030790104103000d081d40c0c41d54699248080502080030b0f004440001d083c4011b035102c2942c144103039050344002a030360400000c4d400e40050300400340c1c600d400007048200c80c0c803074000400d81c1d0302400890368440010b0003650400f4511100380d9040d000c0b0400402c52204984032a000303588030710400e8030810490382e65200c08405850305541c9080b82c0b50010a8103024003407107401a4840540041d204448880c0080103210031524100c2c0ca4502d030072070101d0203003074520301404a41e40142c0030345c2040c4004009903189010620444000400c0c103683e9480c14030400003240c104c00305492942100240305951254480d40303200381c0032401c592031f0041404000440c5010401022240c0c03d00b14100c1c0305546d84042c0404108024224410040e07400c284000090000c02c000c510440c402c1c0c6000d600c1d81c3c100e2116400341c55050003010029000740c907061015844094802d01195916124001c0030703100c245041d0000d15030030301c295 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 285068336 1250 285067086 285067109
    0xc1e0c15300b0d0b090124060c02130b0a0b09040506040516051c060902030106020709060f05130b12030a02070609053f0a020f030102032701021b061b1918 68
    0x90b9403c41075008885100050302d81541f40780a46520a108030300f68040c0c003020843d070901c140b0250170981804003a0307a40707114000910303a01c0704000800050140c0d01c840800000000c0650311800c15004158002c01c054600b4811030030060501642c0d2181c660401003000404900b010001c540e140c14058040c618100c2001115103800212020358402d006034005403090780c20000f41e200240c400c6e48116079129441c4144541050b04210300c1031402c42401d410a0740b91400042d0030b6443c030202c001c80d810104015695456001c202909100c8a98444410b22000400030413154580585031740320110104040e00c055040310300e903c88a140c01081d0488a00c20000013056003110028031030071041d000b1103100e1850f094503c2014240d2008440100940f000741c442550010412a0310001190b280d034005820302030351160100806039040c0d00c07148207034010000c1c880010002514507008031031800d4803a00d41980d0102c92000300c42010416810458070802c95940c003035850031884090408003450 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 285069586 1250 285068336 285068341
    0x2030906190905010915030504020109150210061d041401090b09030703181404110409150e01150813110a060f0f0e010c1e0c15300b0d0b 60
    0x1003101c01d41032851014081400c0c50008607079580210b00450840d07007010304004c0c40c0884104c1c210060440600103e040c054035090101c3d00b06d00d00040081103911540c0104000c41c9544050401d80341141e1102101c0140300c440e1a864031401c401e11a400340d00401050349200c24034034007a0041055280203407030050400240f01500030040010015a03000340c2d904c0c449184511004400200c1a200f48035403490a044030304050305098120048805507002172070b041550f60906c4038250346008050300c60794400c102080c84103102c0a03035051b0242070703556400c9440e6490010082c0107108041c1808a405d40000210820000c1c28001508502c4010b005460302540d90300c00501540c16429401d40403520240500b07030081d200300075164004405a44280c050305c0c0988405100013054503881d05200a86c43c0700d50046042001e091009110302c00d604d503c00e1000000003012544081c04803010300300000812031080230004068012500243c000040d4219408001401480c004000a084e409030a04 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 285070836 1250 285069586 285069607
    0x150d0603150507030209010c0f0c03080f04030c080f060402240a12050708060f010309030203040509090c011202040b0304120215090309181b0306060c0a2f1005090102030906 76
    0x3500d401c1c0300340310031060165441d1420182c099015040b8090b00144a030759800e40403c81c00c050210405000d0000710841c0c075204d803650241a031001200e10100500000c08004100c038114840e8000e00091010308100b50006400301d0b120301010744041d11403242c44040030102c00c11b54003141d45000d41014019529020b2481c0944000404040c180c0c6c480d1602000481c42402240c40074403c4c1030040400d18900a4800154000c041469003a411032000b8440420b180e01c034112080d0003451180300418600903210001071410f4003418528812074010300003000b003002c3c01026a500f080e40846d0b004108008504201d180ca820b00120080307100148003886000038010006100805094480c50b2a40c80045001e81d20690b0a5803120300501c444030703030385003144a140055030f00100c004101601e45003a2124051803c0131904c400e48240b010505481340505822001c14083e05880305010341400819000600050000c2011000d1140000d00c886240e0300c06d001b00c604001d8000c11940d00c4000528 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 285071942 1106 285070836 285070853
    0x60f0b010e01051c1a031606021f09080d0605130204060516060b100215070f051206130f05040b0901050c04140a12030e04110901020c150d0603 63
    0x240c1844509104e4000c03a840e0a8800c1c082c000812406020541450300f4034010b8a0803d9a0220810445801140054a00190b00d5040d50030046491104001d8402d6076402010100001031500113003a40c0d600400942c3d90546801c1d060041d00c00400089200d140070b00c0000c14000d100303111044022605031100c0d24400e0fa8049440288500071815034141d03589080c2c0560084940c4005080701c142c00d9992103070b185d2402c4070800e00503ca0213015482180c005100e43c005600010703142d500e07901c034407804009684400300200c0c01e004000000410095800f00d0f10b880022010510801050241c01e008000001005103401e1074558618210700100981c2c5400803006000002c002c00084203101d240b80c026100c1c618040d000c54200021120904c00c00c49030142e0074010840580d0780040c4d8000340910542c0d902c186074001015030301c1240100401c44030511700303018000c41000f030b801 = true := by decide +kernel

theorem cover : BRFrame.Cov 284892086 285071942 := by
  have h0 := BRFrame.cov_init 284892086
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 284892086 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 284892086 ≤ n) (h2 : n < 285071942) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
