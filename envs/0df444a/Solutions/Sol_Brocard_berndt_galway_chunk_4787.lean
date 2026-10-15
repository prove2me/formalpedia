-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4787
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:43:47.951112+00:00
-- url     : https://prove2.me/submissions/ef13e44b-3fe1-43d8-b4f8-578fd148ddd4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 860791366 ≤ n < 860971223 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 860792616 1250 860791366 860791381
    0x91c051b0102101416170a0203130605010305060402030c0402030105010f110307051e0723090612191103061303051e0318061f170a060c1701060207120308 68
    0x6040d016003400f401d850080503a0105000080030b912601c4444000e0705410f040d0350090702c2044e219500c5080040740c15000600c8001c29a004507089034014600f40482c250541d110810360320240c0048132a40c011500b40002c50900704144003005808540645c1958144000288020102c00d0540c0c02c00c86005100d840e003080a2040700d400305c2d0451700740e80d4200d100c2d026620180460310701d844281d100b5400005041e0140b081040302058880142e0b6541840d48010815a5403000d4400c2c0c0c0d00004000f48d000c040d1030308100510140503500c1401084036020304005000410490310640a0f400210800c00c944203d09a45985e00f541428101d4484401c4681da2040c201c40b50400d8207809000810710400040300070041d00030581c000f00303e03a1745503034100c41d0400030300c0c04002c040c0380c00882850511640c480d80d14040d00076030b5040c0494500000030746800d801d0351041c039031100104000102140b903112040200c240034144c80c0c0000c0545500e001943c40c00080c0000d005400c0200c2e050200300c01c1c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 860793866 1250 860792616 860792623
    0x100209011814150c06010b07022e121b080403091a09120f060a020901140f1810080708040309032108090d0e0d051f02091c051b0102 58
    0x30403181c05072140035541c0340c03901e4400c041c52030031485214a9408111103928a061422268010261000352140f40d00c2c004509101ea08654000ca92242402c3c80f081001003148240c07404e4000240445150f808050b20081c002c04a00c04030301c41d405d4100340e140201c1c1d040303015008900344040d01c1c02950070f40d950300f800c42e8010080c1d004480360b030001d0022140b102c0c0c05003001d001310001c111030036000300400c54600f9641c0d03a180c1c80030300110307005140042d01028155028140280040c1412001c007058808480e071030390712078903580b40080c402054400c001880340c0b10080c460300b13054070840552004054080c0c9408001410038003004501c200041c20103209044030001154003a2039210310b030000024201451508007280e0000440b017070b00181160700300086180d6400000d8a46604450140091105400c0c031a0780c1914184101ca5420354a4140c4003150400f000c450b0f4001030321001200100120050203096618841d90038214101c00300d030b0702044c00e80526080f102120ba0800251005030f04 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 860795116 1250 860793866 860793887
    0x302090703020f040608061c051c0201022215030212191508010509061506070308100509070c2616022b03261b0c0a210801050310020901 60
    0x410f0300003050006030741c1e400c4032400d401030b0001c44a45410f8001500a4072030b4002202001d401d0f075102c003a0040a00c1d484041d0a00d01916501c0054030309945000f00c194010402c043c400b0294031309070300400610941c1d603031200817045146019890701e44198085940504050032485503002e1843c40c542c1004000d5200c410b43c50b50010051105a0f0382c2c00040303000f0142142ca012090080c0700000d400c1c5500d4881010b800800107022500340021914121400301c001000c03905501d00c2807a02180c25075078100c21034800c2d0040d0347e601c1c200058900d000b2291807100e4107104035030366a99100006068004054070942001405070000409440c00020044102c1c0440008002d0340207420700000441001c1c00c0345d4031402903c40d90840002a2410018007818400c8440c0d002d1003540440d007421a000903010711503445a036060f003042c500c0351042d0b0802c40202022140035282201950208850504604240c071031401d100c05a50b15001c046501e80c02c8007840705011580c0029010426801200000c0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 860796366 1250 860795116 860795137
    0x30f010b0f0712081f03020a1e260d0e03190302010b0d0602180306060906210706031a040e070603150f080102090418052815060e070216030209070302 66
    0x602000f103060041d104410540d00e1401e4000d22103420151120b001095000716503010700980380252900ca000000b045401c245140030b00d98901000404004034404d954540c220503054070242d980e5485da041c942484e560500c020b200c7e041001d44143e0782c0100703c45170b0368000028591440c8140745001c074010040d101d41e90781d0041c08043c03100c0034170400c1d601400301d00354500d0786d40811003403000416940d0b2000725001c030b41c09002080000d00d981010590052009007035844600c1802c03505200e1418a04681c004100080e92103880c044c0c081004454443c09103007c0c0e50030400e400c00204c1d80341e01c0d014240910818140c44110404241e0071540003074006081c02036a05200300d44400d02e941c00f0b5488007108900c03440c244441d0782c03228940040a207003519401001402809001c1c890080d024904902c48c3c051200d1040090000c12161918285481d001e6807001402d2400d080002c00c0c04000a4048811944a2100201c2485401110f10150f0790101e81e00a0340780e961050440182c419541840c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 860797616 1250 860796366 860796383
    0x706091a0106020d09050607080c070803030a0209040f05010510030c120e1606020111070b070507080f0706060f05030a0818030307120e01030b06120a2c1002030f010b0f07 75
    0x40001440380c80215059031001c0c0d090f5401440c003031004030398001c1d4030300a241d03001c24100050800282c0c0b030401485030100f420152400c042d80c440405003143c1086603c01081c640002c0c0b074240c24909032043c10501003400c081000030794100004900c4600c011180d4009040e0303164041c3e940140140c104080b4042034000500c2041188031525490740284002c04000109040740401e041c2d0040c01081c098120b0030400c40d04080d81d80d16442a100009041c880601c442001960b001c146c040005040341d25426854603030314442c600c1c16a00300d6115501c4050481c5500505204907a000304180d80c04540000d4010785810000300350740b00034841c0388281507040c0300001e038280800c11281d403c0c1c0c1603190b054480b0802070f21084019410358404280300c580c41344003041035144210075540e40c1380d000b6081c0310000580c80994003055003100c46105644a42c2c00000100c00c400403010000340d81d10030a104819030840c241500000076410040c040c22514403004504011035182d28000e440342c0c160031106a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 860798866 1250 860797616 860797643
    0x503060d0209150103110f1903090501050703050f0702060402060906220603050103210903080c15100f06110303060d0302120715060b0a090e060f040e0106090c02061b070609 76
    0x1c5000c00100381c0d00c9113012038140114040f40130502015681c410f050324182d58030b00007002d90380090071001002c00900741071f60fa40c801070100784248551441004161400601420204145004180010702000855000700104401078850606480300001d096541030b4841242c040303007a14859103030214002d0780105000005800f0b5054110f58103d0303004100e00518603904402c62a00540381000840210b000410100001080d90000f021104042ca098440d10b828206e0f2044003a602903c104014945441c0103021000c0410b0950000b8034141c2006000f007070041c40803585134040108807034840c44000d190b1005150092005000b043c081c1f125403139880481d1700e0800b204810204600c50414500b22001c545020701c0011218240d526440c1c5003c014500440d07c010104001d003056000380500341201d0a50322a80900c20300c40d84883d00200385030b41002d4011045900c42090001198091014404102c0e000441d04080c1000c200c000c994403800f5003459805041e00703200003170994846051 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 860800116 1250 860798866 860798881
    0xc030403150b1011191110080c0313111c030e0a050d35070512490509150c0a0309030e1011070b03070e0105071a090321040f030503060d0209 62
    0xf0106d0100c802160700300c2141904d550304613120030048078003140b11102000482c43d09010170340e1040105101e410f03821364015000e07010130780c580e16040e8620001a220178030141015007007074550940180030b84207064158585400034221510080020740700711a400102d0f0928840d5280b10071507408150303802003000e4510310380917080da4807988045d2010700402614403800071a0100b15031000c0b080104403450720207041d00d05c507880c000c0001d541080c0d0300000f0300c0051000c05072100c114118000d4000082c2480c064ec2d08508142401030b18064842a0400300000c81c03003d0030588074091030500c1c00090b03040040c0303425580b140f4101002e40d40000bc4440d94428141d014002e480c99502d10382c240e880060fa1400c4d000114041a07075080c1c0410300c0c1484000b865449107010385030040c091400880c808040380f004440c0c02e10207039070205242d000010501080031400c0b444c000c0202030a5100001454940c40e001003400e13851400404008001003c80c6055070b0341c24518180c11b80082c00010b89d81030111 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 860801366 1250 860800116 860800133
    0x91403030106080109060e040213021b0d2105040f15060b030124020a0209181e0102030708010b0711091305100218010306140d170c030403150b101119 66
    0x101d4200382500703000c0b0203c3da0900341031039140030315400341c0040c030341c07420b60101d400180d08045c2d1040b800400c1507a4cc000b0b0103c0030081c01444201701d40780c012401e618800c050709101030807015548011308060520001501502812001c203801480c4100c00e070040d101c040015103415485104100004030000c11048103159400746900c114800010303419020b03184c1a41c0314068080c01a42c0801d201c4000b0310000152081007003800102010707501d000d89000044004118014501c4482c3d079070100410500e00c0e005201c1c68054524048d003103040c003510303550305000486008461030240c11240c022032524552592801107080e0b10506407402d03280039140c4a002074100f01e645001801c140d01501410754041c0c440c0c442565040079102c80045259030070300941c103600c15000c85134a00c6c00e110786103000e890760000c1d00304400742c01c0241d9941c903e14240303107070146200d00d02041051b1070035900c400b841c6d075124107401803c1100d0038981000030a4043d25814100c140712072842010300c0c2c9240b50300700081d05 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 860802616 1250 860801366 860801369
    0x30512070c09092010200705060d0b040c090807090209120a11011d0906150c06011e09270804120303140906040506070809010b0406030f1203020901120914030301060801 74
    0x542c0200c44280c0410051100c1700640e0400116807030410202d520500d81c0020b1681c0c40915045406d120358940c04207030a94003010400c98020307581d0310410510300d040d000320b07100d020740d0f8a44200150704dc1004103483c6c111070300c19441d036958001400080c1d52601d41d00c456064180105448940e070250030200422050860303203d00003244200030f0380740c4911056908032284800f40404200303664038414440e180c403501100017001c4405201c0819103181c20484a8003901c04061490040e204910289000302c1040c1c116082071400c00d0882c011040c0c014186101300302c512207000521070340c54140210760b4480c5400040200c2c581e281d020050641580100b0340c0c0000c240041522a5500d030b86454070bd080560780146a40c10a50120304414803074040982c0010220000207a1480004001008c951840c1c0c000c8422070010140700d0144040043c550131921618103040d480c1808180c0000c045803100905403d00980d40c074850010302400d10405114000e2280481c2e65950710388001401a5209 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 860803866 1250 860802616 860802653
    0x180302100b0909030f03150603041b0e040206070201030c090e010b0a0801050409030c03050706021201060e030d0927020f0a020102040f090207150203060d050703110f0109030512070c0909 82
    0x1410001c0c51141403800c0300b42d1284004401560400b00034008240742030344003405000c1581c8400042594541c2e560000794000d42c45401940d0036a02000e41c48064a0780c0c542c440080415103900300405070b1100b004840380c0d198246000160242c54560503507000100fa040103141402c0c00c800401c00c541c000000b0800407185817211030440c2c9c2c4e654200425501c440724010001103500c440480000d025001800c1c50b071384580e03000b6007040a4a150f03040c01410903401034002950000140c0c00c1802e09102c10701608000b480e080394924100b80002d15041d81d0f5406020924840c03542500010b074050f170684440c81c1300910001d5444802d507100074040c2d003040c000c40003e50300c550800113245003c0d108450300c00da40100e4641da1020b030415060001c0d04001d100f141c106841c00608000500c007804028091849050155669200041440b100090403484d10703052101170030040c4007003600080c0d61449503102400240c1d0314441c3e4a804208002540c0c019030b2498280000c01c02000035072032243d10750024 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 860805116 1250 860803866 860803871
    0x105070215090a0605060111010c0c03270b03090a051501030b060d111e040f1a0a0303050d1d0d09180b0f010c02061909080106050301020c060f04030318030210 70
    0x41600218249000690705000b0b6540101c90090001d4510340117030b81d0081c0e0504001982c01d484031421820b541e902c007010f00c00282e00820316410980c001d000c0c540c0c00343c0048400c0c540c1092981c1d000402c0d240700d01460b201042c0c048001072407040d0810102404541c4201030f03500d06100c83c844040c4001c000c0c0070440344000c01c040002c00900740000a00c1c3c2240c1c010701c0c08051404014148030b42160042c00040c01c19026110341242c41d211070041202c4080390300c03000500d90198842d442500560602603c2c451102c0c0c440400109900c40c042d9030807040f070306100103460b00b84c0d400b401e01e1911034040d00124034007400b07004640d450340001c468011543c00990034071a23402a41a000100c507400e550095001d019151014607a51103001601941ca00c051f00c905e181c40c1c0d4001a110070944812510400100000030610000b03800780903880050000742c000703604282901220945640d401402118075560a400090500d03210340c1001c4016002c1c400004410580b508009403a0a103581c0c02c0c032440350 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 860806366 1250 860805116 860805133
    0xf030108210304110102073c1a0918070f021b090c03060d06020c030405030c09010312050c01150306020903150601120903110304091d0a0b18100c0201050702 69
    0x707090442000c80e04803103002440c50340d5603074842c1007141441590604510500001180d88100b45222880d584107819030550344203041e03540003403801c0b0031102c441e04508110104220842c28041007150695983c00e0301d940f05d8903190041001591002d22914a990170300050002c042d4000000c862070f18510750130798196001500c0307182c0301d8400740304855070030403640d000003500c1c94201d0025540240d401403129803060026211101a60080920101241c1001034108001d24040249a140005c20340b0480c0760b41d8034503203a489030010942030081c00c0c0000006c400f04025800c1d0710a401103e0888445180107440f03050150007900041c041900910035904c01e08030094500781c06900c6520141d4844903642c0000320a50041e101a408c22800e000810310141c0e000380703090018001030842407074001034030340c459491000390248030003178001c0c240c100407600e4000c12000d004880e8000e030382403101c40084400040c2d90303142c100707042640680c4a180403a1020340940c103400260140440d90708070f90208 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 860807616 1250 860806366 860806393
    0xf0a0219050a14030d06090b013e07120312240506090d0605011e060f0207270c03140c0c0a0605040302011103040c091512060504020f060f030108 64
    0x280d000310000c0c0407544a9604440042c02c2403610079028a00c00c0140c1e410409042c54510a40f650368000038400364130b801c03d540740d9503031040c011403d40b5400d10801c5804440424000c1c0014202c00b5903014040081c0c1105058000c00c1000a00921a0482c4914401800d00380100301c81c80409140c42083c0c1072020600d450028250302484003100c00c48038414280c0f0309410402c1d5688403683c1c0b550002c510710561404a000b6200d8240240001806030407001004ca1114541007800e4010303600f40911085c10383c240703981c00170311002134030618038514654890000f1080a04403003090140304550500c3c444a54556158000f10680341d0309003906050382d151381c5240f000340d000d0785550b0b40f49607010079400c0380411071035002a80c010b8043d000003e1303c001161091142540100e60a0310182d961140800284406205204c000341c00350346444002401d2003400d0700303e2000000c0280c5101d40710004a400c0d50b8070340b0300e1a1501d640c002d00d038950350100740c10b0000058100f40311b404401c0c000e84451000305c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 860808866 1250 860807616 860807653
    0x100507020d0905010e300c030c042d021b0c011806050f16120807020d080103020117041a0108011e060f1a09061c15061e0203070203030f0a02 62
    0x20f81c0da05854494201804800380008030900b501d0401e258501c4001800082c201d80820700000080340024040174124201803500d800500e00318640140c1c0391804140c29011003d856607407840c1c0f8003071034101100250003070710060302952401c0401840004107030f05031101d00003400720307808100380c960a641002d960070340030111013988180d50124204000e0b0070080ca010f500101404c3e20450300078500c0190340d4482d410000100e003a09404164a4010b200085070100580c1c98410440c1c9415416903045a0000340796411420302d4104a00045010508002c50015491410340b4408940c43c4e8030340c0d4468549020703142041140f2f06003047d107524540c00c080c0d603010703900651f0092144030408500d0a40c6410396030312540f044483c02c000c184440c2e02e40d55140300040c0a20400c101e030506840724040340c000116540c240940e41000906141000b00941040c0f125405005070b01200381e4081c400311081e03085110f2003400030740c54000080e11070980c107180000b401d08043d165007100d546210b4292003155 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 860810116 1250 860808866 860808869
    0x30c06282610150c05010903080402150f0412080d0c0e101b021203040b03010306140a02090102060f1b03041a100311041a090a06030204050a020f030621100507020d09 73
    0x201c084180006100b0400c4890f2250fa40440c00c0c50000c07040c1805445060071100d441c1030843c0003d507901c003030200b90318200d09110624a001d400e820310702042d4207080f00b81c40c0b24030b01c07650846100d0817101009019800068461a02d02600c0178005003243d102c00811b9401d00034501783c40f84030702c1880c81081c603100321500140880788081da0310909806800b0440f603c0d00e0324845070a10300c41008007160301e00400001d0360007541300714004101685e46041d55201c1142c014105080c00744107102040550703030f00088194014031402c004c5081c5803108005028001740d2550782041906002040c0002c00c0700342202c41413810181007a1b1600381d140c01005005103103072840301030121240e05440410340d1070f0540c0044004811805140281d21848011641c00241203030342a9840b59219801c0003903061034003807182d11540f5180114502104101880190302014040d50301603043c1c0342e40241681c03164092507070001c1c00f1400f191002d00c900b92040d4050a001c8074000300500030404002d1031503001d0340c2d1400 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 860811366 1250 860810116 860810131
    0x4150905090a1a0a061a0307030609020c0a0311010f06030302240c120a0b0a03030c03030c0206060a030f0606030203061603150303320d0b1806030c062826 68
    0x10f02c0c00e00d40d102c08041a600140c103408400d5038500c000540038010b520a11034129007412000e4580c41c20500280c02c0310607580c0a921064010020201181400300f1007004a650500b01401c1121502e0412401010208407114181d403038400f0110606800040b10201d0b000f01024041301207513a0a01c440e400b0b0000d444103c010601484400103950101c00100d43c040c6445400091800300400000c1004200c0d03401a00401c458005280c24950b00d070203110321004a07400240780c90309043c400319141e60f880b84006400242c20802d0002004102d40185008540060484406081100205040c0008410340001003490500b40d00007494607440000708882e00f40e111000c4080130084528026040181c5181c234203541d042c10294007a0b4080054090200c1403040040c1041c91602880580d140c02d45021460f400d9410070066683d40c00039035a683c460040d1480d94481c02802c0303010340c00c000c12562000104400202003c00c40f50f0040c003281c244078040c03501084820300d112034035240d01e1091700c822 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 860812616 1250 860811366 860811383
    0x91b10020616110601060e01020d02010b091501110102181f05030c070204150320040603020a2106022b0207050604061508060c13050a1202011d04150905090a 69
    0x400c80510300084041c680306909040c3e104120b01d0b0038513814101e09801a0b03000c034203100d144550650b4108490303d4000c43d180020003010700351100140d0040390040c011060040c0c400c4004249910900000b8044500305000303545520302d104c01c21444001ca20005c80c0518500000448501181152405100d0290b00c4251a68035108101c0c7c4041d0701c80c41e82660810b440b0340c41c605441030280741d070000550003211002035026803500c2d6042115805103c1d18070071800d040050015035100c0900008a4181601d00042001d0b800341248074070703071105005088c40313101052003001840301c1e01210541c0002607032464a400700b50a418412400703400000303005540490700160010303449601c5580c003418010b450030711045d5258180303864018125044c4400c01d101050b88200c3c581d0240d0140003800b8222071400d80386041c0005020202d641c94070281c100007018501c40c051414440e9842039030000900140118404078a0030b004400641c4500c2070042e01e00000524082e001080c951900f60744414074 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 860813866 1250 860812616 860812621
    0x40e03280f140d02072406120b060d03020f100218181501050c01110408060f070518040605040e03070b06061309050c12070207150215071d0603091b100206 68
    0x5a282c1d5005070500b40c3d5240d90801211000c41c0c5100c0351480d158001030804102c440758200c92505962032a4400300d0303a04070542003600000e03040981c19a04c444103440c2c2030844816410f0481c6010441c0c01c0d60040c41c0510b0040d06c81d416103540061400066034190320305400c2d0b0410500002e03098824600b4103000c6242c0100ea0284202c8001c815541c505141071420301c84c0c805403450845d010603034216880c2c00001001c100601003404a00e80c002402d180755440352402180150584c41041800000c0090146c000c28a90780c3d5a44000090000a4000c201c6003140740f0303ca0303603254040a8240c44a0040100040c0700d8540706003160301d200f507403801c006811072038003602c0c1d80600720180c900704211409020950950001c8100c1511450803503004084c10391a16400010682c1440031010443d00103600087d0009040303420190002031501d810b442c1c2d203907103c0c03080000410b0a500d55a004800105000b00548006004151f0a801614920805940354200020070288029000c0540c012000 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 860815116 1250 860813866 860813897
    0x305061e10260102130e0a0506011e02120703090e060906030c040e010609020f1b0f0a110607020a03050601080c190b071e0309031e02150306040e03280f 67
    0x596158001c00750030307400c06000202ca00c00c0d0030390300508004181e0056201c8208540404510001c1d0021200d2904010178240080020400646040000c500410f0502c0d041c1015208100929100d2030003503815458021500d0b00411404041c0704151807801e21101056062818054aa0180c00020000d180d032001c05014030014090f600903004c201d56840340c0c00502c40d00c041c0002c10b1040c100c5000305507100c02c02c1358080d04450044080c440c0c40d6110900403811000009042d8038a11f0700201580a610561b10009409215108000f1f4001d1468000081080000074969040e10314074070643e0b849500c0c140070310039024111a4211000c100c102400c0049a40480041180500401c0d801c06640d07600c002400411060710003c5000910281041003844511a0810381d05402c0d1580984062015000128030803d8101e01c0350710084008082003c42c0c0c0c2c2c2e03074050601d85640d00c080d01d803607417894141c030604680410740c1e00d88120b09006510190900c2001c82e002c040f4625169903000c403900d0b04 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 860816366 1250 860815116 860815139
    0x92b02040c030b06222304051306020712141303110d080403080304021305040203030d1a1201050402120109080318031e0702011206060e0409020612010305061e10 71
    0x81c00a0a050351100f40f031029440d007000600e040c190825040c101d100a0004911140000342c0c010030611007201640c20b00c5100c07200b81d00d201c0c090100d4001c500e0f51141240709007500c542c12401003051748005a14820840d114441c1c505030780182d00d80500000140710400003a02c10340400c80d814058a00c0103100040c0c507c011400414000780880c0820b28440d60b80807047d80c0700703400550310320310003004000c1149440005820005001e54040c801810b1a80c0425501c1c001c240381c4288064850000181d01039980211440c0c51400a058058581c04075500900810044d01d06a000e01400c40c1c125150410500414041c0d580c040c04a9156565600c40d07548500f010b8203e4007040d0008122042107041c65898a03902c070300ca0000800c3c0d480d0520b10000d44540c0304180c9000c445401c0ca801080165080000c0e444680030607180404d14100510000d00903220b030b401031440d031440403400030040c041c000400d14411302d0102c40e8030f21500c41280100b02503a2085a2442200f08024018001089100d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 860817616 1250 860816366 860816381
    0x503042a0e250e12151e0c1309180c0b0c010e06150d0512070c05100201200f040807080102041509080c010c0f0b190b04060806150d0501050a02092b0204 67
    0x2401a552401c603a00f0305458600c0d0181c42803250881c031b107801203502c4a180c6010b00e412070600c4c4005894140302c081c0448001380c0030b01c42c05000f15500c80d4002c2441e900159154040365010001d8200709807103e041d4500d90b00180c80b074041c82e61034800c8102d10f80c13100044140c012140321040c000383c0d8403054100166080c1d884c9044480d40100e034988500c400700b4070041d100780c40c85408841c200a04020500c1110300724170541d54110ba044c19400000791214a50b103215240114081780d6646807802c4810750715200d2036000405900c6031318800955000103501900c00e99403440c444094421410030704550040540c010200250010b00600c0c810350700503175204082d903108c0c40c038060030090307d03856505131810304840c03200d00001c403145614005040f5104407543d00302e003140c08001080c102610180d440c600205990007540072181501c2c0c103030b5908000c2440e00c0e54008000c2c0990310340002e46401a421002c0240e00442d041c1403040c0303070100c03241c06c086240b05180a091403806c1c4079408000180012 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 860818866 1250 860817616 860817649
    0xd0e03090d0602033301031a0a150201060b1333120b1305010f06050c061f080d02070e0f0106020a0f081b0705100503070503042a0e250e 60
    0x59203000038441050080000717404418508004002c42d400c00141c10f80b0220302184007603a04c2401e002039241d98080c040001d83e07042003445c8420001840081c0d00600c45a0080d5003e241702250710f9034010444031442003034480d0724600303001406846104502060324602c10102d8000c40d8050850320601c103800141c80b044480070041214003000000c10304483c841c41c1c0800c091500d420040c0107854840c1c18200042080b480c25074a03144101c1040b6858030400f0b414007581c00000e880c88508011248840b2015000f0201502d000300c0e4030b41c202941c3c81d00d407803140b1001400620b0005412501c0f40408504a90054015040310982a6501641c40180e00401c41c0e2124040c07002009642d041400349030b12803d600c004003916801c100400c10140c3e40d821101c000c0103000c004020300564010180ca1300b051f4051811a0301c0c0300c224015000c42d13400090181d1035101c5407030380001e02c03840d2010b07403601403104007841c14120322524644942c2208004c030241c004c0b0703100800c2601241400c0042c680040c28 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 860820116 1250 860818866 860818891
    0x1e030f0b0c041a0c06090c0612041b08061b0702062a0708030a110703022115240904020102030306060f0d060305060403020d0804050d110c0a03080d0e03090d060203 72
    0x1c031218685002d0205443c035280304800400d1150010504200d025044400a001844001540c03000141035100304000b00101051010101b0100080882c41c0c104505107198144c0d5071071344030061540d540e40b0032190900c42000a982400f882240d00c0101c44505401400e000d14202101f4100200791100a03402d010f1410307016482d05020f1130070300141740613004140207107070742300701c440380040c810100f50110420030f0300304110030030050751228040b1000711151001003441c040717040d2441d81801400520b403400d58242c1c0040011501d250408004002c40c010b80c11480c1c0d0301c10f0400e1203084401200e000380903074820408605a0319145003d0040e29000200052030540040e020304140c90296000b2141c503402107050200301501448003484000e40d510740100285481e894440e038422903051144d05005d046500e001e281c031005c3c00b41a4050704040d0900d003ca0340c0d03030f15240001e68020980031003820714015041d00b80e00310100071251035030001480c4401c514100d40740c1030300032350014003007915111 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 860821366 1250 860820116 860820119
    0x90b0913050619060305100902040f060e0118031209061805060915130504140f0c070204091a09060c040b22030c091406100807110115030503041e030f0b0c04 69
    0x44260000c0240c1805e82d004500c0b414544c40041d000380e8150410300f0458018041070020308050010002118440d14282104c02c0f070140c01038a04203414810040b68494843d0302000b809840d0504144085084c2d40301031210342e1304c2008071015403252404803c0300c614290308110510f030510140c00c080000a22280030800191900b005075032100f0841c601644080303c0410035407a2900c81d038403090303514404141e0240350180001e0b0b8107040041c46c484e50041d010a01001755210b6034070500020768400001001c1e400c03480e90800d00707440101c500402038030403140000c98180468040d5001c56055008072070500514269186d44120301210300b201800280500202240780c00d4440001050410701c00143e9440616802c40084801000c0e640250321004203030700495404a41c050f405013551038030183d002030040d9a02d01429002c21400c04140007142c0100c1480701c007000800c11204007410700180d5403080038611406070518030024101c0351001841d48040b42c034407100d00381e001419101c0103140c00d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 860822616 1250 860821366 860821399
    0x91c05090415080601080309090a02070312050406051803041406092709010b0d020109173309010b0d0803040303020c1c0e010e090a0e07031e0201090b09130506 70
    0x242d420210300300702110501010040c8001c02e02840340540008009503150540c20300205285c4540a0b1001464031760008070201814031441a02441040f01e2800b0300c0b440c10715003020009410103607100e050750122701400300e40d1b0446c000100e9044500e00d400c202660712001c81000801e802003110301c3e401032900b00c00c9540d105c11080c28480c0030313055699640e405040c002c030510708403680c40d802c3c140a802c0d190303000e10150303030400c852a0403240303000e2950035541ca0320310b0780c2da08284e01c190f88810100e440d4400402860a040001d494655a0360810115541c0d008001400d85804122450300442c40c003100d480400c0c5480001c5504c14001d080c09482c02d00343c4244e0f180f4018440708500451407050255010032584199100601c080902c1d10708106100000000e01d4000d02801c94800310390343c4d02641c107943c001400400c0c0103640007651102d184c00c07154285103034140c1c103080481c0080c0710300d00c01041a05c0210141d501201000c1c0079034405440c9191900002c11001d4070255000f6008556006035 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 860823866 1250 860822616 860822621
    0x306270b090403032007050304051203070b0f060f03070b030402060a051308150a0c0e040b010e040914070e040b071209140f21070b070c081602030c040203091c050904 73
    0x1aa10075940010414075170b41841030440e032421a4203040d0340781008050b01140001080d24156034088030404000c941c940a100d00d54880c900d002030103100900208421801c1e03000e800c510074202515200004a1240e081584883d080d0190b019030945c18804540541890009001e908a413420241d150a074a100072890301c64181c3e0100d04a0f5200401d0580840e151514140d0490b030300360b02c14400c188060300083c041500042969000e035a80345403d0109038418100400030348070151040003680c5040c107201c16094120001060f40780705410303002980b04890604240b0840c2c0040700c142441d210507000311a024040910103080e251101d0800c00031800b1540d004a5083d500030080081d0002c04207a0390070400c681c4000c4941c1410740c5880d4001d4404217003111100381d80141004c5940d5119003069130382190f0303030f0f101912410740402c250704020700502241d000240202c04950b410503900c8100000c4e40300c1110450740603003000480500b960001c41c00c1825038a42805e01030700302030314000420308 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 860825116 1250 860823866 860823871
    0x100f0209120109050c010f0206190609140901060f05011b0602091f08160f030908120405100f061206091401020d150b04030f030809031606020406020105070306270b09 73
    0x4942e55030310f0410301004410003003e80da4010a081600b60700304410406925207100814013403000b0405032050800c0f5145600c048003600c003180003004180c0c0d0190000c044203000b05d903099969841c4c5880880c0d80d4104104030380c100c5005942e030750f20095000c8204101090745910071140140c0a0110310040e598058034a00801100380e0f410011401416008001103000340c0400b01d941c440c0306a01c03440f1507010040301e45040c80e608012a075039299140c41c015a115604092290501c1d00060004000d40403400c0724443d010302409000c0345503101c44810407210035105503404500800446000107030aa00950b9120740a5900829101d41c0250210701760b1348856500700d6032990b190320a0640c0a1a00c5485014140062560b07013000c1c207640e2040b446191171039014052184100c005403040340200103c41174a0521065020010824905040a9009400b40c5000341d400c120001706454801d00c01e00045800c005190054590b1100c0b078281e410818110819410303817940d40d036800a071a1011800d0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 860826366 1250 860825116 860825149
    0x7080c0d210c20090c1809070c0b151e0d0b041b0920130b0a02031e1c050606071709101b17040302090709080717100f0209 54
    0x2110b2a030310300003c0c28440310300320083d0500440b04000c0c207034490b8501c90780e00c00c0c16241400c1d51039400800c400f075245a080003041d030120107201040740c0307030754816000801c1c17911034840400c943e112035050f11692601e82040341d0300000d52009013240605008030282d0084000361010b2413100b0140c40751480944215815240450078481070f584110a011340b150042c003c80108202a0704040306040003c0c0400b00f0701c02c03c011001c00c0b4004150801d822010041c2581a0210341e244101c4030302a485e03401040051084802480495064040e000308550410a404062140720014488038030001c0101604ca1904400280803610004003402035040040c0510008551a4a0450704020180103c85141810401500c01c04c01b9004109040c1d5170509d90f02160304000c80545410304100c178041d96001960040201c424031200f00c0d007141d01d003020384081109a80b511911a00c104200c00e154840108047c1c1c0080081c5000b1115948040b1103e0316614000d03141c90441c10014444d02d94001c10300c0e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 860827616 1250 860826366 860826377
    0x9070f0f08070c0b180d0c05100b0a0b030108010e061605090424030602041404090803010e0a0f020d0b03071401051c090606060f0813021807020115170f07080c0d21 72
    0x10f58408410000010a1031b032500d424000882241d88050303c454000c8400710b139440d100d040c08980b82c3d03100c03448c03280a03040103491245c0300d683d2104480c0c040c0505c541600b40c00e01820300845d89030400c80054460581e13071a02c8407403030700c4c60b5042840010035003c0c2c05000c0007010f034104d580c8070f00d00340c0d03850100450007004003584603030803c400204020300400d03215224a07d0071100100280062095a0440d00d0200740d5000702e82c0c52031f60600241409201e20314a0501c00103100c0f69030340f140d81c004059580260116107002e0f860b0356170794540307010540388180803600601c0500c210305104401000110106000424403080c545c0c1c0351800e0319100c2c0c20010204400031b1445900c00c0c1d103c00c0943e404031070802d0303d081a0409401144c0740101c0d00d89000d4070500c20703c00040c8400c7c001d4102604c0300f000d941c07403004055543c00d6096405001c00301d9503901070043d0700c0f03500c40c0d0003800249101070b01c41d144060000401c5c00000c1080b20f118a6000710f072852110800698203410490704100c2c130a100f52281c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 860828866 1250 860827616 860827651
    0x31e020a0f06091e0618030f21030b03100905010905101d0c0a1502010209091005030c010e0a210b0c090103060b120f07031808070209070f0f08070c0b 66
    0x904400e4064000c05003005029448040080c6032410309001c4400606000304900d29500c03905148000b47e42014210502840c00602001000103805c02d02840003401103000310001d440840c103446042041640c95800401f40c114683c1b4154400c0c040f03c0e02c00c0e80002130400240e40e42d40c0c240020256540b540b2542c4d2203090000100450001c41103d001c05c01030072140444c0e00c001000700f4554040c0644080350b4244000d000c038000d604030b44041d0700061004c4c00e0f9140c04800c9440e00b003030500810f8064010011103911550080300001540140103010030700b442d081c1032049200028860140640301250070468000c100c010100f00e001b0b1000500d40c0d0380e182031003800582610035603884004c82c4403040010034083e03000102426000304501e850007040d0f0302c44801c202d020782a905410080180e14441c1e0380301300041d11000f0280e440c4241c0308014a681d1f08101591410300604a45000c9189900b20320205841003c20030ba2101c0319080400c07003200c03036440b0b04101941c2103d1128070fa200c009030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 860830116 1250 860828866 860828879
    0x90103050601091206090c0b16060b0613050d0602040b0a08090d0804050d031a0a0b0304060b0f03070b1e04150e04060b0406031a151c02030c04031e020a0f 68
    0x903090380301400382401c0c6030aa260901e02c0304024006000a48040c0c2e852075090100f12950004d10001d01d0030300085c0e81c9580b000c1d003c2e0401101010021a4803c0c940540400c42d8180b080540e103803404080c1d52000e1040c0740000740514a00780c0441100c90036030030400810000407020140c103041c07500e43c0e9200c2580c5400c0306007c0c03910b82d203041080144543c20781004002031001802c01511600703807902050602844032007035041307401c0b04000341d4044040d0340701280406a12001d18404c6004031014082c805a840074402c1040154101c240c26030810b11042c0b040c003030480002d00000818076900422650032412030142c0d50040c0e00302c0e000c40e940200340d403c502a030049101c1c1c0340b804102e404004480c90404640b00c01d103c3d40c804e04027407586981c6c101001c260100420101c9190103004611085690074100003640c0c030907000c4410070b015441b105401c80c0460720a40f481182280c801d14609425900c44041c6101c01203502c0ca440451041c4001c01070300c3d910010b8004060041541120760700b0200d = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 860831366 1250 860830116 860830121
    0x60213140406031205090d0b0a020a02060f0103030c0209091207080304020906121015090608010606121a0d08090a170114130305131e060f080601090315090f0602090103 74
    0x39480d10490a2442c203201281c6120352014a03a04c1d01d06240d96151407a2021411260383e820340501071300c15400c100300c3c646605e9002410aa4529030a03180f040d81c8000076101014000c2c000940052410002d40c001402c1501960b80c000c5403402c12900c2c082d130009400f8001c4e034407080381100d1001c4040207010860074549207003500300c50101c40d490b00c062200200319594003406d00c40b0811a80d02d03150040c140540b04100c40e40034001003e0248000780d00c501485000e48440d1013141c00051788907000c2200400720344035401c00344000c2c0e5035805001d4414030030400ca1810702c00381511000010099030080c0d540b5010808000c0015004007043c03812039020050845040813406076021168208110001d20b60b01c2220080c00e0381810450740780e120300030708d0565500340e0f50090400034200600e481d203c030080003114411101d0300e41d1110351541010408684040043e00c844c0d01181c216102440051041038114801100d12413001590785c1c00d80e218a0058200c0c990306482e40340e800281e8840035689030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 860832616 1250 860831366 860831399
    0xc0f120207091a0406050132040e130219060c030818030705010510060c02090c0d09050a11090c0a0e150903160e06030a03120e1603050c0102070e10061b060213 70
    0x242028480e01240348a0104942c07607520f4481d40380d114400400328401c00c0230301038501610707041c400442c0c2841c3c420348203200348403501c07001c0e40b143d04941c00c1c1c0c0001031a0a94888141c95060340c076010004440c0c0c2d0144d81c2d414000c2c1004004409801c03000030851010405003440c18060030011503941031031100401040318981103c4c007000740030111500980c91f140800d68002000c0003080b03a42c4c4254508030801071003d41d070010218041e180c901310034000d4804422045180403a165019030f11165a11032a921410621401184d003c441d488082d180580300540a18004913505240a203900000303402c105000209d94540703510000306010032007169801a50110043e0020704d0f400079503480140441d0214503a9840e4984c403010503001c1102c061181686400c410050424145d44915210f41c07500351a1441364010b11804ca0b0024041000005c407a0103089003040c007103000381c24020200c072410780d5500c1c1103560320265465000022000e1004280c0c2c0234202101102d8142004002c00c00300045 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 860833866 1250 860832616 860832619
    0x80d0e01060803041202042c072c04030c020603181b01080f220b090f01062106020408030c0105041403030c0d0f0b040c02010c0f0c0f120207091a040605 67
    0x4048040c002c100c00002210107039241d842662030512040d200081c0030706809400c4208140c000410080450145c3d02e031000200c1802092351246921030a440c04a071401008a41d40426600280c0c03610040384010b46070014041d140002c965040e540202d08142d0080d40c0c2e03801d101c204000070078007820080c080015540c442d1f2600011204003000001c1485001900b201410302841d0086440d414000d504004080a48034203c01040200d0034584000342e4100d40780002801107200700c0340c11810620130075081e40c00040700301c00031188a03041c0204035600b4a2044501e1a0300700b001051040040000c0e007503808075080040781c503140902d052a484504481d08005540c01481401001013030700f010f0700c8002600320700000380c0348000006500940f401020b12030f0020b01e8100c0e20460b071641034200e540c0514117078a450002d4180700c6021100a90b000401808104110711610002000e40b811401140c005204590a60b521030605004903543c000000703c1e540d0405c046140581003a0048a008160 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 860835116 1250 860833866 860833871
    0x20703290402060a1b0b0106262809050309040f0513080a210c0e0102030c03090415090f1505030f10020d0e0f2524030f11070b1003050d110a0807080d0e01 68
    0x40b04800409c04140c0500f52018020402c001e059007196000c02e58510701c04c2c0c4c5070003031200c50000d0800580360b90001d91021301442c1003d40d114081340c541d00406020f00d442a0701e801051030b1316150708a40d40c121810403000c01441e00c0340c482c0344010601c01c5d050040920700d40000d501e02d541c00c3c05000c4e820071110480c159007003440301c824100c4010055814600c029140030556458046000d81030042c2030b001207030441d19080d4140903050095016410043e01d05104d40941d60310b0f4820140d86e444102c61111640d44007100304900c1514903000703008130940d007140c0441d40c403d020100908100340d218400311240d100070700c4240c202c425034100449840c08400a9080e481c00c12217a120f481010038109078560b03c00917401d100e1a8482c0d0f200700c203840d40c1418100301c8403025440c060403e5210000c103650464841021808422017009140c040300c0c1d010340201044010304c08251901005a255a0b1050180103100030101d60590010980c0c5441100c8940e540c80b9182106811a0401e900c0307074136903a1 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 860836366 1250 860835116 860835167
    0x92901081608150607031d06130302043c11091e0d0c08070311090c0a1d030d05032a1605011b020703290402060a1b0b0106 54
    0x1d1041801401c0348080d03140c4010142e44101d9042d048440b42d4803590f8000c040001c4074028103a1210354001000c0d400026101d85400e20b008001550241140144204030040c008000510b8143e016448d00c602d0600071f021030384a01807049c5011008210344c200150305181881148007010701c9a400c030840d807003201500308403800700407552540ea03500e51074039030160003100c10000f0b58524441900c400c3e0300401c822070140e1114155511800e640c0302c11a907200d03440182864520300070064510400803402420f044ca200301800300d03034030f011220801c0cac1e034408003201d90080c0392428040c00d40410350301d40b40d05560713003000400400e041c81c184040041184440314500b5809100508070750046414a95030b010f68211402c100d0700601c80000c0c030f03c206004460352016015000700700c0b002242d004011000c02104170f0f4a641a1040d8140781d0080b10784242800100140341034005460030030005d1610b2081c44481c042d0148010018002c107450000600004000f20b960011561764161072602d0202c1b0280b = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 860837616 1250 860836366 860836381
    0x1306030b0a02090303090301051021080a0503180d021501090507022505040912020d0503070503010501030c05160c0515070803150f060f070b0132010909290108 70
    0x3a00180444105580010b500301141c0d4042094929108000303008000905104007081890000c6200300340c21030170452100d6041d403000d510704000d0990450f407800d02d400c00c0c0101c1241c0d117a06c01001d0841039602c91030940c0e074400b0200580d440842031600100300e03c00003514990507416050340031414084c00c1c081003002c5658013054000700b246081d09400c20403854040705c1141c4d0001e40d00555002490003100c1001d10185d0344508454580c260242c80d4507002c0c210084815110440369800400d404200400c601e502c01c1d40400808486450468200581d000200e40d11540100082d900340402d014140401d00e0100d0103020104050401355280441568401c411800010000100c4826021041d0019100c40c0254001c0c1e0000406982d41c903048001a03450740e03007180d85c056408900000020407508881c603860000c45101d80012113403ca40455200000500500c810341041420440065508640c3c064072100d21024142500d914000c2e1010700d802080c15406181040070400078004035 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 860838866 1250 860837616 860837633
    0x105060f1807031b020105011d01030f0f030201061701020d141003020603060315070f18060512091e030913020a0c02100207030f0b06090f0702060a0c032405130603 72
    0x80304050008414903980e02c00c1c042e03009003184100340c881421518041c952281c0d041d13004030705981004010100c80003140f4415640d002c801d0100800382c1401601e41c10129003186190758082e842071001247c9caa40310040b1441850542100b04000c0c0e4010900c002d0582c1c02d805285500b55032403045800c2440c080043c0032142c51207110107401401d0000c08240c0d02d0318140322020705814500084505410704500003800009109452400100340c0134020340115050080b550454110742d64290800b01200ca00480442d0090598003151203091241e280000354031301d0300c0d012116084060358840750400244650240740c1c3c140d04c0740e0b551040012070300164015610b5010390750103507080d925002c440c1d4400e034508042a0400741070b80c2c074816444003c000e01140c51a10490301034800003903d80742d5100c2501002d80940f80d600241c1c200000041800c0f10503404496864a00c1c030707000c95a0343c0304907030a59100804000e0b000303440c107a004052100782019000e484060104281c10000c0901d59241c1084 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 860840116 1250 860838866 860838889
    0x50106110609030f070f060216170a1d0f031c0908010615050c03070816120e10050a170a0f0b010f050f070c030b0a0506030705060a2312010906080105060f 68
    0x4070f600170608409000c540403840081030b0740035104544d00ca8603003866100c910944d40044600200e5041d0883d00a400703030f01591040c0c0450b4890b209005c81024150300222038220007250040303c00304002025503410001040350116a0966002d85103003100018074004407604a443c09a040002c00c008880b5612040da903c0d001c54582241c581c165102d14500718420464090044040820074041c2044d1614403040054450300025144404401e003c1d42c4013820394040d07a600903a8040400902c6000e44000c0c41c0c54225031a0111000e50780360350340c480410060722000f174925a01c1412b00d5140b2854450700030100c0007420001180340c81e0100c02400c51050188038046070001052280c100041c1c104864043c540c040080b05192900350300c00d00090074100e40052292044490003d101c0c18400111400c90076a541c60601c1c040c00c0303c00051200d021901500c90703121080202080d840109513509020301000385000c140d0500e0041a20300b075450140203e407081e0140109841740b913030340c00404c10 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 860841366 1250 860840116 860840137
    0x609050607092108070b07051804090203210f0c2a0307180b0d050c0910120206130b121005010e10030f330b0f03060d050c0a0905010611060903 63
    0x2030f45000207161205850103200d0340100741c0719811051014040d00720000d40084010500400c4401c040c0c0340420003903410340701c0040d4158001020700c49003c1c05060700303070f004131a140d07010b513282285941030702e0069802002058080d400505400508900c0090304100c880034040d009080614100c00080d1200114450580807480f12040b8541012058201e084580030003040b081c0c040b0782500301941c032400c69240c8a849422000c00244007188080c03112030980d0400490341c0c413010314030341c01c0c402d517580803552000c20a6000c0c03000290743c100840c018001c603007940ba460380b411b08022901450390822038000c103040c0b100203881040c0075200d08484002c0c060f2285004110408000080b9008040c456041400c131101d000c80e43c03085e070b000356064410070310003082d01c1000d01c0da030340b10400c0c1503000e0b1a070454007075801000070400d603290540d60840400d005106035040d1007020000600c80c030300c6a5101d101503170380318001088115001384c623058900c0d440e00c0281603640791a02c03d8a4a0b4032807040c0e0903 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 860842616 1250 860841366 860841419
    0xe1606080a0b0a05270708010801050708070212090f040c0908070b030c0d0b120f0f070608010f030204050601091d0f060306151203070206040e060307052e120207060905060709 77
    0x9a284401c17624000c0b680c071010a04003036090800b04002070000000340900182e960030040440e0203903200d010b4082c0300d85504c1e130280840710001800c4900c154070046110303501090311848000103031303618418003580480c01d0b01c805225500e01080d0909000156102002a1000b4400c01c400709100385c040301c2008140c8a00015080d8540c000980307d4105190300030321034840e46a10311858400002e401c46000080e404680d42c06a542a08444005d4240070f4101a80c0c8000c1042006007481c0d0052500260141441d130485c80c2c45007030b0346400400b064045147c280d150340a1014030805403002a8001e00c0c1030b0041d00e0070b803900405003404071080b100d82e1800b1f16005600c441c2003150600a0342c3d2816402001290f80d25503540c0740401b94070042d500f0301d01c40e025042001075145000c1108a11010f03009108a030340c8081d01580e0050884481280704c1030110203200d00d507000115100900509100e10303000030302800e260400c14600500209600b051140d5510b007442034407540d51141c240d041085910 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 860843866 1250 860842616 860842639
    0x20414040302190f200405010f030c0314070503160603050c04050d110f030f0312181c0e04020c030c21041a070f140c04150510030e1606080a0b0a05 65
    0x58030100d00060042c3c0240f00e00381700000c0c5080d041c1c91103c84600308a800740700d541d03251030728400400b455201c010700341580b000d006c000154440c001c0810401d00d49c0e003030b16401c81c3d540d40440c0c01c00d1000284c042d9035103403001d01408290f0b00341c0304031a04503c2610029080078104408501e0305103900720701410204200c506803000c0e603600a0403054825010f0700761604200310b0088240c0e0b030341008440310a0300b010140010300107842d24601e0034400080d0001046490f43e90b610726183c0c0c24003035030f405041280c003107464030154846000404003410520020760b502c0f13110b0040e060030302c2d840c055804041c004006a12001c0070f40142520103a910004110170f403240741400074111803048420041c501c46850003160305003c501c0034408202c4005d5000d6500310000b4400b003000b2145240b076001c240443d140000d0040d801c0c400c00321400401d1074240011959401c0c03a10501c0c0c070200c0c85100d016221044014041c141d030160b0070a800001914040c03002d5020b41c400500c0d403003118050315001d000040320 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 860845116 1250 860843866 860843873
    0xb07020f36060319031d101119030f03020a170a0605010801060e060423030a060203070912080f07030c080f0403110105070b071809020408070302041404030219 70
    0x1007080039400d1904031000900e051507450810a60400041c005a10560000500c2410041074901d990109150b100c00121182c0e07405580060303500443c200c03200000401c0ea02503440744401254010f22a4598103510380e214520140780400c01130f459100c4203144554040000c0e040003858052480c1414056128002004200c030343d03140d000c06c901101c0000c074003402241c2d00c0a5119038169070f400c0c1e07039203d0240e0b00c840003a10383e41c0c0c00405294100340c0820082010600071001c5000c8003850501c180c0f645c07141c02c0000391402078944016150345a0001c01c0c0105160450940002000d941c180b8803043d1346a5142d80c030144c00381e6440b506120341c00003148410984a0480c40c083c440d0702c00009078036140f045001a180d504540003c4400344806541081c0740c0d80510305560b0b00a90210100840b40d5650300c0403902c24100d862002c6c2038038008440458441a280050310180c0714210040160b14558010041910903043c6412004446d003803d000100340e020800c0b143c8954000c004c0703000040c00d4036 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 860846366 1250 860845116 860845129
    0x9181f14132612040c0311010918090618150506010f02060115200303041104021c090503190315060302121b0d18031d0109090e030d06060804060f060b07020f 69
    0x1c2843c0804081c03182044100b0441c0b544038400d4034016407580b010502500c005480d440b609025240c801e0a1b0002100512203241d0404c0380c102c3c0c0300302401f05401680156040e203014921500b102c01000e0403c0306100903a607441b905501c980c09203400040710f001c445d80a51124018000d40c00c0100c01103100902c854081c0940b4492800c3c4402001d40340035401c1d01094980c1c100340c2d805c640b2180300100b03840044c6454026900b901c080c01644d1626a520213a20394010109050119040c2c0801e00c100403002e219061840b24100c555180419542e0304250b4160070341186410400034580306122003410f112489080c190b01c11190101204440d00e00d000e011601e0003098140c404141c04c211000c0d0101000403044403a051003500c410b040140714400b100a02e0384554a014000f40041c20100300710751181c0c010307001d0001c00344262480c0c001d01d915210281c9001d46c210340c001c030b0703031640901c810001c1620400d02810001e005c1088400c2c01c003041a0007500c9114406803080b03802d440c0d07071040750b942c22 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 860847616 1250 860846366 860846377
    0x609020603010315060f031101030906090c080109020901050d0b040f0c030602030106050a020118030f0e0619031b030e0d050307120e07150e09181f141326 68
    0x14480c0341c903907a4a2800c0c00e11024800d40b0f0714541030031701e1400202d80b5000d9005109072940070810000742c0c070140e00110010081d42c1ea05440440d15001c40b107001c1100f0081c0e4001405800c000400c240456006001a201d01a4000390207403111168400c0468800c21410b90000d50048002d0304214003030070102198000343e040076000c00d1000000003040c6030000f006140948890b0002e105910f9440b221007034243e000c442c00b402042040c800107218520803070a880c03400702c1c000d14030350030014074280c2501d50300051409600030a61b942c91a140101400c85c0803809030909207001e110205408080d0b82d02c91074074207114028000040301003840d482c0118560702c060076450004001d168543d0300c40581e03e007481e01c98603a000700c520b8440781e003041c46101585140702014050f80c10544401604284068420b1601c0ea00d50003880c81310005607040c180107041100000c0008219581c0d010380d0328410304000381640c0000c0860052650002d100100820089034a090f40701c1004840d0b0b0b815648a880b0302c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 860848866 1250 860847616 860847619
    0x30a11150412480b0c04170c0310020306130603050c0127090203041104180c050a030308060609041103070906170412080a0608570409060c030f1103071209060902 71
    0x40204200441c1828001b410807034541c850001c41c0803550310095516000301403290754050f0071201030001001707450340003190485406040f4140c0b00004401c514120307030b01900b0803500343c0c124034014201c0e50703404101c00200c582803000000301510302c002440c0c0b0440e0075209004402d40c000c80007809000b403585024080c50404be1061101d219580c61014803200c14010031658403244460204860608469010941c0d9240c6c031103c0c05502d80c03100b000380c076400025003680d01035181c01c0103144450505001d9805590581c88180c4007a05014002d094400c82e104810200351201042001181010340e421003403070898100001c040e1520690000500b01507000f03086c2c0c0d40304059a011410401b20408448810f0f03480035004c074001d40c0800b40c6d07115945414401a0441080210395540b0200044000240c40040c0000740e8000141d480f24103030786506c0d8048012a0b542e40000108451901590180400c207007601c0b460f41c58509005000c00c401c0c04e60455913540e54080200802580d0390005032040d40 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 860850116 1250 860848866 860848883
    0x50f0307060c110628030c020a110a0f060513050118030602030402010908010c051b0c011e02010e190203100c05031b04030f080318010608030a1115041248 68
    0x110410004980d85080f6008046003030f241d403817007a14610a02c200c05c84403102d60302a001c20f02164445c920031080c005081d40e40301014100c00203040c28607000c0760008211580707031241c85000d00c160540402c11558440c50500101c1440704000740030058403a0207495012400584a44642c001200c0e40700032600001c40079842d02c4c22040e0721a07081406025034100b2019152810a00d5940340707500e8040f07101216000c18004624036014840c1041c4541d41e010252000149202018150030f281c08034036100d44003c40091201101542401d20000800e44086a0240041400c501000f0032030310004010b03401407104062800c40c0c8d0484901160025078000c2e0b0640c0b0300c4802418028400d500c00d0300c0070345980c1880d02030500d02000602407541180c2d88940a5800c0041d20362050300c4004196904c0000c6014070b200300c0c0d050003420030b02c0d58021802000e0b030759140318a001014101014802030401c040801c0c01c081c0c4000c10741415003040c848840e80025001d8404030929890b904070180c0700500414 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 860851366 1250 860850116 860850127
    0xe1f02120306150f1b100f110307080c070602070308070f031a0105030a06030b101e0f03080f0c1507110304080a300512071409040b120d05070507050f0307060c1106 72
    0x100002004001e01c40d14000800688101040745008c860116130004c18084c0306000080000b401450315507803081060a00c14913080b03c95903520101e030b1101c441180400c0401007448102c0d6403151000c9103040413428100940d10404410b051641440c20030103041010000c001451010b07540c1049000310b42c03180804045007040b442c00c501407040c038010850000c2001c0000300c50060102402421950340f08080d01781e140c11a103d03101c0c1d40d0300099000b45d4a0b4010018000c952100300140747d400105085044c0d4241000d010080469144030384210b240c3d413003400240000ca03800700340340e07a40f1540082c00241400c3c002c2c48501c1e01c0000500b85d035a401c051080b4040c2107603041401800b0a4805c0d25015080b030740c50b400180c0710b0200c03248807000030080030300150b5580e0070076a010390044040182014003c010914031740d480c00f02c10030302500008402080c540b0803c20204650400f40400311011011000040003082d60386080e0700c030b0301e4100068046203005101d0300340e43c1082544005401d195850 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 860852616 1250 860851366 860851417
    0x190b0f180708010b0f10050438030403080c19050d0f1d0c030a030c03030203090a120c0204050a0b01020316080c060a02190201060b190e1f02120306150f 67
    0x4c0c080c5a94003801582941d85040492400041d4600c0041d4181c503941e081c00d0030183c20501100c1e210049074103004d84440307024107160032041118803805850390745950702d1400b031900410007500030740234003540c5000307104114894104442c0055901400c0c54500c0d260110040541c0c00381c41545040c8140360700d00408500703000000009010a160110300f00e40000451006055540801c10300181c005008602041c4c0024440c1e0000c640040d0080100c0b0f81c0a005900c1c0c0b92401181201018049007440c01c1c8031742103003000c2c09050303404890036030100b11740121000040e44a01c40e070b0f440040880c008945600070003009030b0940e90468219003c83d0900d241103407511000358400f5038110800084000a1109144140640d0b41500c203240340c66030504025010402c1000d91440c200c0c014030049482c4481561284090038817205c03203101000c01d02400c202c40c0a8204401c0c1100e24540c18010010001c4944808000d05c10404c0b004645c0c540d00c0600c0103002620740070f41c0202190000718840c4040d0305 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 860853866 1250 860852616 860852621
    0x181e120a1e020118060909050403050c16090b06130e0702070801090f021806030d1809020d0501090e19080a030b0303070308013f0204060302130e190b0f18070801 71
    0x61003130302e505013065103038200302504045500c141c0000400f00748081c00011701c6600615009403080c01c0283c240400e8080d200d00342100d690090220402802d01044030050900030422200c2c0266012071400d450000c00440d02000c034002c00da20400c0c0c00c80400d16180c401c0186a00a0100300c000b00401e40305850100e001e400303c0c0e001070b4421802440300c0303c0a04601e0000500880c0014000c0c036440790b6a44064648580c1e0294801ca0466688400200394009000601c8299220000050550f0512006000320760202041a4460307024100c0400c1d145a201355890380c00f9007010f44a91101c2168034203c0140400c0b034030a6816000204051007010740040410341690302c1452041944020354010001c451040b1074034100644003c0403200c011108a01d500c03a5040c000750000c03d0b09501c0b031f00480d41d117030720010f24800d17a10380d99102c1e00c5e003000b81400301c24501580c42604060841068581103101e00d0040c0c840c1d80d0003201c010110300c600750000030481da040100b41c265242c0ea07076a511160f00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 860855116 1250 860853866 860853923
    0x7090e01080307050d17060d020a08070801061d040201050d020f0d18021e010203090415050402070c060f05090f12010e011d1212010314010b060f181e120a 68
    0x4840c400d03c0e01c040c82c2e850041b180302181c0b00b5644031071603e5944407010441030754104101aa0088164140851076000611a81d0050041d00e80045456440c0c035a41ca0b44002c10742992000d0304c001d001c02d000043c0e900c401202da400000b1880980c45042460007240036100300705400c03030a40d20f46410851100300762410182c1581c000c80c0c10344120026129000c4101160101460040c1c00c00c104201c45483c20780c1c00032545c04a000c5800340503d440d8000300c1c04030380c04203078141d900000904040158542c0007245043d00403261034610706200610b030108407002040c03003819108400c1d220715817520180943c00f80d034981c040c140090000300c5a0181d01041d06c0b01083d0003000c64041c0500702178045030b51204a600280c00110f4201c450380c40c0d911441c2e40290341c0e0304400815501c8100701d0480d0740d1070501400060f407000c01c075590f680c01102084107800320b1101d0309a00074610500e00c4280d4600c00c03000000c440303805441e054890104100c3d1b0504103e10020018005415240200f018842102c10f90300d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 860856366 1250 860855116 860855123
    0x1081015170603010908300103320a170d0c05131406030403030c0c0b042103090c0504180209040b060a050607110d0201050f0c2b0203090907090e01080307 68
    0x510b0b101c1c501454260350b049000a8880c5208022031141c02052801454001c9002241140070710b110120f452031140c003e030b00603030ba82e400341e985c0303503100311300a0350426800c0e084100c910740030115580406403a083c41c440041d01c1c00400d40841d181c43c85a0074215002c0006242d41000718041303240380648950400481985010300c01e44000c0740c00411341c03250030202400202701a06641d22075800320054146000355908000d1071200d4080010424560745e801244a413407016048125030b030401c01d40d401c0c40902c4a0800d800d11072000042a240070030305050320400e842c0403e8041c2c4a084001d42c001035204001c1d08801a1001c02080c04a112440c5002d060122001820b01c8d9950040100310300a610000c3d100c440e6918010810b0714000038050030f5544181041400d06d001c403a1450000e8112280c00b41e55a0088282c903491055640032422101c80b1180042c42e12010130300000390b8a015068425000d8621040440e05080c02002c3c4040207108072000c02802d07603100c00c0038584940090000310b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 860857616 1250 860856366 860856407
    0xc030e070801091a0406140a0c0f170a1d0a05010e2e0903020705060f03100503190b0c09060f0a0306060504031a06120601082107030e01081015 63
    0x1240200741800b0300301d40c80d50841e14483d0341d0114048074482c00440030b44200e81e110b9449242692a50411140c54030a0342000f80c001a200604400a000030a01003d8103040058000c0d41907045007031351540507003056031400300160015158070007903848450f9017868400c621407400104108103054005541c24403024040e0ba0f030060445a0f1010304120b902600a40c0303a40d0040c1210080c0b41903844400918040d10481c3d4100c1d5030f82c0049075855021503580c004010002080043c2064840c1c00400209802e6000703013661580c3c41c281e80d0440c1c1c0c207408010950084180400c0b2084040e800361069502c00078100c4d60b0300c1c00b00c40c0c60301c070044c0c0c0900d04480200e8208034000030040d010300c054508036604040280d540341c1240c413031014132800c020000f95203c0c950003044004103e0403c40382d030281a58000415044c01e20400446000c0403d046003452103c04100000000e5400405600036039404e0801e0304568455441c0d0320014a055048180f0100a061110350543d92000140c008003034040802d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 860858866 1250 860857616 860857619
    0x60914030d0608070b1b120304031d0a032001140c06091b1003050403031409030d0b040203060d030c020d060905010548070503030c042607140607060c030e07 69
    0x103d0362560203034491000c2084050180e4400c500b0251620307040d9a4013001130742d22060040f00c2e521a1a00145c07826000600d04041e01c1c0004445100780350a0bc020840302d24860038a99601d5816a9204815010000a400400e144c5990181c210104c2c0d5008070ba0300745031580e41d40c8281320380c2d0f2001203030002c1e10313445880c13140d001c442206580c0d5001e040003e072070140170482c1a00254054075014204600309580c40c104d20700182d105000e068003441010010f10b81d20145c0d4007a2000340e4501820440c0b1a03841002444a25070300c0c00600d006580d41410140c287c01e059000107449528489400f0301040d041103200810081c06512091040d5460280c61f0111760ba1006082c4014000c07500c12841c1e1069007481c2040c2c00c4901d07900c044000c94405541d8506901607845030b01710f810555050400043c04601480042c02004c0d0181492822158910303040490816195649560384610f039160b420f502402c580c143c49190448074155080017007448185820f0f000180204041c20030340c03c090241000 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 860860116 1250 860858866 860858879
    0x9010801052a0904051b0a0e0a0609180b0303090d03020703170306060a0810120b0603010b01141801030212090f1e100e031b03030a0605060406050313060914030d06 72
    0x80b07210141e401580302400d1042400a20005080180c46a00703500325401000c002c2c5c0c1d030044010042c0b10403542e100401400d5035400e004000915400403800c2c0840101c3c1808503200044803040302989101020400d0091480401d0861281c1c40d5040d81005014088a00341500010750301d00b200d2192281c07c0c0c00b07413503c45290520f80070a680c5150300040400c07086c5082417041c10b1181d0030903a0b0b0350740c0d0f8192940c1c401008000c2e980914085030016140020803405207000e00c21801440c0007130801c000f140301084008042403183c8006080010100000c00ca0664400c0d4144c03103054041c6c071010911790400d11a0155590400d500c41c400a1013214044c9100d14403541c800e040b402c01c2c1c2d200511000c3c2c500c0394514090320384550040103e200c140000f044181c40380c2d4048020805460145560f4100421810141e80b100d42001d80103003c1080308112b980d074017404036540020201d40c09950042e0a06c0c00034098040742c800541402103440c2c680a8800c4040001c01050035907142c02c00009690700c1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 860861366 1250 860860116 860860171
    0xf0e03130312020a3f0315050301020906070f05071802070210030b03060a0b12030301150f021b01030216020307030b010501020c03072312060a0504301b020901080105 73
    0x18802406992030402c135085140c41780100c62102800d11900c15150240500d60b00315030f6461a80e0840081d844100a2160003414000c0384003a00d07055000b0340ca07003050640801d689108600c00108060f12109000c424000c05101c00e00c05085192043c0840307950007000c0c4c0c2c0207500110026403203050080c03012071119009103d604c1c0c0700400a80036000d01d50b40c02542100400c4400202a0402c2d022080000c120790f0900065000c0c0a10008801000d603005c0401001142c240b25910159440b0301a45910905e100c138408030010802d190140c0c0d5041458201006036145100c004d405214079540030041142c0c500c00203050b94030030f034200c44880c40c6400030507a55034007922515440d015022996980c030070a07054010300c058000741102c1d034a18810010301d031408901b12083d003002d03541c910500c000c10481c0404000c1400f0b04a00b50703800016030003400d42c180260000401c041c40400482c410768000346400d2030040e150020190319043da900d16449001e080100d440b40e0001d9140314904600c1d80d4400c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 860862616 1250 860861366 860861383
    0x140f090f0a020313050115150507031e200d0e0117010e040f02030a0b07180b0910030f0903081009020a1e020a06092a060e040f0e0313031202 62
    0x10480c03410151100341d00180258405803e00e05030076050300600c0c1c0454024040d00340c2c03280d118560740204900d4500b541e85811014140001040810048800426417050340056220500341600c41080d4079510261750b00c04080421451084080d005001c4659010440001129007074454446109001c0011500268103504ca041c46144080040c4101483c0340c40340c035440707440350041030620344842d00020300d001d02a0350704644280700041000220365000320a8024503c009a40203695130902c46070600700d0052600d0355001c1c07605003e00a10445c032940014800c0b10242c14100440849400c2c000c000744001c5039131a03040f0312408400111100184201d40703c0070050359543d03e030264110340841203140094102c000310b10440c1080d4001c2042445440c0c10789100e45120b48401c22054034266820310007a8410300c0103010340c00c0800001e60010580880c1540441e00041c000c07594004480082180c80140303012884049421820307103402c030243d0030a490182a04e806400c00c0c91608907540d0310072 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 860863866 1250 860862616 860862631
    0x41803230418090215130f0509040320120c0c15130317070506070e0102060a0506010e010c060f0f020714010c0509090a201308060c040509100f140f09 66
    0x403180c2c1072001e00d1a99200c4440c062005085a41c040c0c1c1104c040c040300d411501041900c002a014100841c09000b46940010001910162950b24007514003a00c05010041c40e1304915050410380000342c0c0090151024102e04038000c161141000031007142d51320481c0e070203a1b024400c01f6803486185800d50b0162b0f00c2038040b208941d01b80074250b60303400c56440001c1c0b01d41d000501d0184130a800203041801701d00d200d0341316aa00c1c51442032500000a19048018200e00010b40c5040240072491342d0285801ea140082801c207841c0581c42850b11400030307d6184914906240341084507a011503464000700b0311a8011520f118114a401031102c1c22150241038040103c2d07010808811a0300300a1001c1e50b010703410b1100000c0c4107008103004884007a2054240d484200c0004401c00b21780c01c00311016018002620007000309242c5881c00030003510a40c040e6034400c07450786001414070007070404c2320300192403400d141e200c0d402d503501d2540d1000080c5040583c170488480c2e40301ca049043c1072625601c113054 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 860865116 1250 860863866 860863889
    0x30e0a0b0a0e10020a0519080f0a0b0f0603130c0e010e130303060308070507030204051503030d0203040503070f0b0a11120a09080f04062706020a060203060418032304 73
    0x110645808010080d25001d82c440d4003614141180300401403014000900507602c507035a07903101010289000c210a00c0d084001d1114090038403103001d0030038110542c80b2603090320014070710481c0b000003840ca041029605a04c200000f0800440c00b02c11414118072511925400e03000c40d495040d140c034440002d01500c40301e01d881c0d40020b0001442600f00040d03450180c140050520340301c1e01c800c01203900c0010295442e510102082045041c40d00c1190391044100003030786000d00050b00001d880f44110080c0a041c0f0350040f001c138050040900460b41d1440e4050008100300c0c41501c2c0c9460078a0b01142c10300d1000c0c0c41c0460006041c9007445c01c60710641e402c40c031711024980e41c0503035500c010050b461040d02c0103881030000452603a400320041002c0c005507101d10050b007115800c00c061902c102d803804c0c44140c51604040201f5038001801490003640208091307100d64810003c0780041c1440180301d400d580c0c40032148414150840a4030715803050440d1010303068500300e00f0210036072143e8480e0401e8030300b = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 860866366 1250 860865116 860865121
    0xf041a06180414070b040f0501200d08091204260a0b15041107030503010302090a0f06090506030c01030506031f0b030313170111030a180204140106030e0a0b 69
    0x1a0049000d034003038002880d51000161015680702500c070212012102082184000d14007070100700000001405080c070b400389480d04004035000c02c660240f1440e41803054016808404041103418005e807101c1e24802c881052045800051a644003a0340f80000f60203000c04200040c51260200c60544059103908551654400403114480d81c8005500780d1501410f440400020301d918070550064041c50416019444500200070171034081805544414004026800010fa00304040d00c0c11650115038501d4140c1d11314400c0406001082e00a400440c40c100000c100c80e05546c0c080350280c0382c10b07000c50702c035004080019421113900382c40f07541e8950300004000314040c1865820302030900d40f845010580784040f40129185400c400003541030b150303000c80c042c0242040442901e891a8000c00280441503000c40142c800c0c0c800a08070f008025100c0b1141e44041460382820414242c1c01b40c010001c24a0303400205400d54400e0081e58002070411200176035480000444100c0c1030f40190045a0a4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 860867616 1250 860866366 860866403
    0x3010803070201120b121c05031e0702030f0a18050d0201080610050702041a0301050f0f070f050c0d0e21151005060a030c021612030f032c060f04 64
    0x1540904c10741c407829115228010386451b1030040241c00c440a10062815803a202000c0500107183c81480c02004000d000300404003104010011402c260b01d20700345001d81310010228118429508490420714000aa150046501810140000310700c89601c004540e165010018891038140f00a800940303013002064840c98003014580f5a84460f05040d0b240c02c1d50760b03002ca4191000d1922a0890340d02e404041d03000c60500b030103030315440000c0d211039444900cad0240c041c05200303c01a02403010441c100f00116036983c0207600f101c6801186100b01c81540480e644020312200852003003038003c04000c60b104c400c51031600b0510303000400d58006464030660808042c41066801002011004c0b121600029141c907001d00803d4003140342d65012803517000881000e803510110060240480c41c0e070343d4080044800d0b94244118066040c81e1042c84402103079011005401d40021120a41c40b06034403c5030743c079411040c08403609042c001552240e03500c0410b80c00041d0800c46010f05020b2402e540c22484 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 860868866 1250 860867616 860867627
    0x1080c040507110a061a120618010603021c0602130803071527050a0209070203030412080f0406020a020c04020c160f060516140a201f1110090605011a03010803070201 73
    0x4116038005100441141800035080006e5110190825004503062001c1c0305c01c0c00c2014512788240270001d104140c9103501280e050034840d030028081e10822028001003280c19011140b400c07038009503249200fa15000c40940302d612540701101c09034100c0c1e03c03004841d5101e00912000f410001450081c614501e0b1580041d040d0040b02102c1c94050100e00000507591a18214080c1d4220342c001c5850f80342a103444034200852405603404d0150710400c001e1080022440d1a83c0540c0c40724002d0307191150030000f43c0c9020b0030581e41a07445800454075690307400c40040c2035034003040c500084030f42c0680e446004030913104090280a00040c000c20810a5044190440030304a500c10602c200150720764a901504145542c0022203840070b5058141a2200080340c4909041600302c2c0e56110090001005040e203a4990103000305102466070014410310701400f803c0a090207140741401410464035280e00207180034090380160304480c0060600d00491042582e050702d1522000710714241c850303001502d0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 860870116 1250 860868866 860868881
    0x30a0c023a09152105010305100b030a24060e13020609030f030715051501020a0201080a11030a0c1710030b0c041205010e010e0c010905040c1701080c040507110a06 72
    0x10b01c0210300300080c00114510400c60034055680d501c5030040040c041034944001c1d541c030304d449010300f044010300c0402c0e0041101c14901020200002d104090a00800d00744449002d000d0014006ca10f0b0340206512402001c0301d1404155004001c42902d41c4940340c039405080d03400203400103105170b0349070050504030010140700d140102102c5000101082c540d10b16441800c084a003042c002070103440040b0203019054102051155012482e841c41c40000e5503080d8504e0040d04024010780440c0440c0410790220f4407606503c14500d56078648140c004020701b000c03100581c0000c45803006580c400340c0343c003402c5005002030205a41000c1ca9a121985400405007650800950820001500500c0b01c8840086248500004a2100800701001d421618000c4000000c0c0d04866038904941e030b0700c603111405a0f8000c03180010b4004040da0122210b2200b0f00c00002100e49150010a00500c001100200400d0032a0103200c1540e852808581c0d4000e203e508010340d502031444000007854070b400624 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 860871366 1250 860870116 860870233
    0x302070b01090608010f0504110d06020f07030e0a0501090609060c030e040203011d100b091302091002060f06010215161107170c0d110d1502030a0c02 66
    0x50a0140503290000620800c0c1c0c841c54030903554080030802c07070b5070a008a50400d0158082040540340940f24164203880c81c10005202d1502100d1040c100482941914145498903410f542c85070740032300d0f000e05520b4840d0340c0e2501c1000d84210002d899132186580d401030b101d1030750341e070100c0d64a801e03030030764002000107004c9051042e40e14a00c0d0303240d142c3d44081e50013001321465062042800343c0c0384c100c41441c048c0c035485410503c00b4051115074080c80072035981c2d6800341ea02ca0f924190303642140000b40a0403181c164041c00004400301c1d2550300040c0c0354040c070030b2118254161b0b259100166510f8a540c55a11101d804400c000b981d40c1a01c01c42e821401c003424108204444400030040382051030680101c994099440401090030382d0800031040c0b02c800c1583d500b46442d0080d02c034000089001e4540c0d030b10880e18075040c8000c1010603d02c103050505120419500d03800c1112000c40500301c210403420061013900074451260b10540302c042c2d10101442c00d00c2c4410541c001c40740f84214030070803208 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 860872616 1250 860871366 860871371
    0x3310060f03061a03041b0602061f03020411090a09020a08040303020a031b02010e10020c28060e01060302101701091d0a060b0a0b0a0f050a0917070501020c03010e1c03 73
    0x50b40540f48500402a44482c0b00b0403a941e142c6440c00c01e58a045241c0d40c00042c207004401840700b1074001529503080b00208180241c1a8560b60280d5260481030700700a4115041141502260344c00c0d4002d070441140803102d404d07038280c96254542c100d0140045a00c00a90744c00041808030b0301913401455807901525011502c5c1c00c1e55220440324010305405800140c4d0741e0b403994584000b0501c08800e442c000400c0662414900169542d51116031112680c0d50182c070051041c240484d10740c180d01050ba00140501c000d00032407904c58000c0455100aa00440c000d4080c18481440788001ca0100c504241d07582c5082c2c0d0034850000c0041000c000003100d000320701078010119100c10802c428889104040110380c909480702809040e00700d96000120280040c03140c03108690304a20540081c0e6200e180c110348601071460101d4064000e0f9100c0400101541c0110460100c0071074070006681c02a0200d4038405806d006140c22240e151040341c8c489c1d04103551403148800211103110300704101d45000b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 860873866 1250 860872616 860872619
    0x14070b010603050a1b020c120c09061302040f0801231e09190605090d050703081602030405040e0c01080c1801050d270b060d0309090902040e3310060f0306 68
    0x19150150030b1711513904050307803044944490a141c024401d140100000004d4a65594000c010036903035040508014441e80c1100380e01800c0c170751240e050303038010510301d4085504180d90300034407402404242c0d50b41e050141480d80d0411903200041261f80915a40784024002d0404003840c00340080d8041c0a03100e10b400390707200e10081c0008070400210102d000d104001458141180140d240602101851090110601200c4d010940200713010740d1190328003082050750740c002c0004a0075841160031241c0e11500e0820003883d82000002e0000d6114020307240c000182d10342840c400c8503030203400d034240c040716803548011030390754840e41c042d25410304205804601821802071412018500e140303c0c0b119511035907144000e12140301c1000d0740191080c0c800507243e540d5928010702c05c0c01a402280001a00c1d420060300310740351070b40300d01140110b100540f54030005e50080321040c203c0003015500524a035170134009504e1a5410058001c640401100d90700c0d520f852010b440342d0050320103040034035503118070 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 860875116 1250 860873866 860873891
    0x150509070f09050a0906050f030609030a0c1704180e010b0a050f03011503050c03061303020703320303180c0a03020907090b040e160f09141212030714070b010603050a 73
    0x1051300602000c04020580608200c140030000410050300b40c030030382c004000e020b40761a01004503112401e152504499416183c205404c18515180c0484010100060000f84095400301402c1d40000c04400a026000c001c007809801e88501c038202c0c81c1e001100102c100954606401e4580d502da00103800841d00c510864035125a0180780e60041d1015000032001740d0040c5010704c0b000f940109118070007802d519850f100255624082d000050800c03030f2000f00c20980003d40ca07203038a05202035581514904c11000009501d0360402d071607031042d410503c44055400c05022840c131652441c042c018802d40b41c03454003000408100a03101505020b00d642001c144c281c03c030b030000d00c01740a01c80683e01c001e00b0071a42010000d0802c2c0e08080c02c05c207081c446418243c0d0701103404411034000d0119103126405010001e444040c2414100d030052040c071007080c2842080802541c42000d0640740e002000300c0322000300425201e1700100400060840005001c5503029070f1089800030f01d41c1e00e00240d040801c00 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 860876366 1250 860875116 860875129
    0xe0f070b030a0f240b0a0813060b0301051005090601090b0322150605090a1116050f03130e09030301060f0305040f202d010e040f1509150509070f0905 66
    0x3c40d0280080100c4d0200c00101c1e2010802c0c0003068102d00003482d09000c604000d02000c0c010f050707800680035001c0240d0500109420598141c0e0340140204240d04040c8464034104d0380344e01c1214000c0e4017450018074198010500d00c01191980200030740780d5509c40c0c1703400407007a84d02c032410300c012805281c00c0c00101e0303080c01d2103003030702002c003075002480d0b41c145820480d6410b0b0091250300c04d1800c0080d110010343c10001600c1b00019440b0544104034407904e482418080e9650f00c0ca2800c0c031003c1514a00421042d500904550310f401d1240c4181d00d604110b59200c1c0300034080c40c00820b124448125099100e0703481642e00030b00443e500088902e095030303542c0803076240440d4040b61302c2c0d103580110f003d8a401c4003401884010038250f00800c85200244105011801003a00d0501000c50801a400d4440b038108620540340e0080406c20901c0341182c0c2c0c006c512260203140d50315881d190310140700003c0107400d1025220010301180c140e036280c0c04c044801101c3c803000c20301003140c804d200103825100c90 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 860877616 1250 860876366 860876381
    0xa020a230a050601090f0209010c080702040906110a0305160507240c030e0c0307080601060509360703050f01051021020301052e051b0a050c040e0f070b030a0f 70
    0x3070010f88029454091440e0070307074861348200c0300194810050f4a00076a0000814004150b00075450350b1510a1400050b00410030b65001a0882e42002c164031203040003800102123924154404019946a8900d000c22000f80c1c5c0c82c0c00e90104804000c4100800c0516584e65071090900c869000791808260800080e6801401c0550200703454809440c1980000d1141c8025a1004c0c0c00034040c051810411944d90401841440b00f44500040c102d44a52030f0101059070046208c0340815103401034561241310004c1c0740c0d1450500901e04000b080c00303107229000305401103041d8143e030b0501380d0038807017004402c00410285800340060030070080788498801172286000b44850070016200d40c505018403840740e401004032581114100d1203011038002c8441030561244d403d181c4240c8584000702080340203605491010650f1094440b403008010000401c0ba140701d0058800307216058107001640e0381d0780c104a000101c540c000c0306040c03289540b4407014591100007994041944100070354000100c80381c1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 860878866 1250 860877616 860877623
    0x3220602090909061b090307030c03050c01030b19050105031302330705070b130b0414010314070c03030e0c10020f070f120807061b230a020a230a 64
    0x118041c0107074a0865980c2d544045080080c095914003c8400505000264000c9807454801715201201e620204100e0000d55886079400c00200d1b1241007a40c1d450481c2403049002901304034110f009400d1404140c0242c1510a4407d00381605010055442e608000c0031003148030b0100ca03e12000d1703078540c1c6d030075001002101180040d1741d2560b04801c41d023060710b52064400040410034800020750000c0e0250803501c2401c04d986e10380c0720071940003185070703c03d6000e25052a40818040780440440c084503540c003900b6201000b440740034901e44000742000b22600004a2201c81400010a020f5045000911040c405903108089414005520b0b40c4201c07034400c0050348040b420740690305013041044003410659445081280c41c020040381000742c42d0000900303855020404100300a49600102c01e1400d0a900380d40c000314400400500c0501e1800218961401c9443c070a558440210100c400402550f40034089603052526029035100e41c0455124074840c5807004658048018800c4044840c030 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 860880116 1250 860878866 860878871
    0x2101101231504050702070302040b06070b010303052203120804141603030809030c06060d0512161b0f060521010b0304030206100e040311011e020d0c0212030c032206 73
    0x40209042c00c24103514aa040d02031032410040c000300ca600001e5090031240e0444011448011030000709075a8060304400a0082c13420314000320070190002c018017013094400d550486d030010540f4050103c00e086210180511072010040d009151181da07d0b41d5000303026400107420390764042a65813a195003060210b00c1005c0394203041c000c1542c01410950000d030400010340c1418964102c03a074584d030018100a05c28602400040b0800c6400d00c8031844d8894a001001d03110001d051403211560b80c451000c0f50f0f8109901d0141c40229a4004181d080c0c8102a0007003010a0410f0820b50f559844480d280d2203002d0000f070f0204100d800d2000030b50207044401040d68136403c25140103072410802905410314051014024070036644010b00142c0c0c03190305880e00450200d100c4481034018401d00c0040c2d0540c2c44140d1144d01d01082c650001c00030226103140800c500c44031504120385a40c103411005c4003208081012a100d16080000386401c005090a007050300f000032100c5002000380b25008451054 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 860881366 1250 860880116 860880121
    0x90507090b0f011403010b0309152a070309090b040b04020f07020f060f0d020307050d090516150203071403090a0f081204032406050a080610060c0210110123 69
    0x414500d00000c2c10340a0800c82113010100ba103040450205000d9218413000100008800044c20041e40303a0302c074405000c80f0704d5800c20903c8000460155a15148810702d110b03c11060007502500f01c540b903a80583d1046076590402c0a4440a0f0440502d142c0d801511250390700000e9a907480100120b81c400742c020341e6a072019206000740e081400c013480d07210b00d00511401e20407486080440d00c0c540d00034140140d5a503180e03041520700c0d00807100c003148028a00b601c040108000001c40711107954040500c003402a96a044550300c2030103d100c21401a001032103401c0000e2041c1407010381d03071481181a2410801224041143c04080e0f40c00040603060014003013024a40a2000b421901c5101007441d181c182140c0b28043c050303000d90134400d0389610496070006c03901400d13400703400034050040c4066a0756a617078000c581d0304e8100391141c5a41032400d00780014054001c0300c401021030b50140421400c40003029003550401907030f91501c2030329500c49448141c8820035000c54000ca09420701d0485550 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 860882616 1250 860881366 860881369
    0x108010506030106081b0103020d02041805090321060a031e0c080309010804020d15020307050d050609070c12030f05010303110d020615040c1b0b06012d12090507090b 73
    0x100c80140c40300d80a0307458003005114040b00070520500f07100f00688114600d0b40320f000124000e10400030035040132071000c075004c1410200c034160a8030710f100c0c0345018807403521095402da07268803660b910807549003461848203039074551082e091984442d000b440e1003e5103135680c44094400ca010500740070f84032810781d5004104008481e018000d070610000450420342d07904000b8010080262002c3c1c4201103207a03180c41007010100c8901a8000c901100b07541f40d0500701c001030641d4000a03080d150603820100064810f051100600d072084c405542d650f4072590050b10744a418015812010040584074500040701800f503004650007903100b43c0d6902c51003402c50681c80d007408400a10070007150095018041c520440111819080c04100e44c002601e401a01c02503a106505400078a5140204402c082c00d000a020146120790002c0c2c0f02c007409010840d011180080d1102c4070207000d05504000646054491303074180f46858422000007035000c8035611105d180c603d562303118140d080d45030300d616110f5 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 860883866 1250 860882616 860882621
    0x6090b150307240e04090f200d0510090c080a050303011703032809051b03010c1b0b0a110d06030c1208040308131d040c050108040f02120f010f05010801 67
    0x518281050750089a11240203840d42015200741c0320030042a00c0f80a00e06586550040146d035034080c40203002c0401c40e00d007000c4240c000c011400c0080c11100c0890a45003040410f40210317aa0000203861046660100c420081c12041d1080d10301848650012031018001c210407800103000344010341c0c417585001d02c032500741c1801204a1005070409d209018000f4003031192014503200e151030002d5041182c1c01c80c10000e20301044041c3c164802d104a0f02c000138280021818108400c0d00240140014184240e0707800010403520190400b60b40a050301040c1e00c00100d580142c2400c00101d0f60ba81c501c4100c480a0300300702820390f081c03a03641c281041003100e4911803070300420420cc10080221010b4403210510b0140c1d20011300b001600141ea91414246100c02901074541000c0d03c140402e0450701446039100308036802c0b07503480407031000130803958012036002c0e01c1964018090881040c059003400b40092114814200354031814114902040c1d081c02000345944500c1d00008030780d89070680701801e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 860885116 1250 860883866 860883869
    0xa05010f1503020d1101020f030d0501050a0512060c090d0b04030e03010c1e0503100512070e0603011406100201420b1b120d242106090b150307 63
    0x220704072020790030001a102c0c000038410303c640140005e0b8000607400b0050781011a500c80d2401c250100103180e18075552280d101505843e420f40d070184c10300e501e41007440003400350842c2180455008400203010306561800401e01c002c0f001d800004000140e5448607602c0e00c05032412008601d81c90001c3c51103050911864045100920f0101f00c510301c1d0f8002e0036803010101c0d02034400c10000000140302200100b000320002d00c4040d110b4441840c12000b000d1300d841e498050040020849404182e1603e03050044000c403030080030600c019a2559020003005c85008040c1e80159521112042003940700c0c000c1044802c0502214404980c10004450b440d0380041c80e41c1800504071a0014800c0303125107403e0300c0340c0c05003038030112104040740316215180010300502d122050078001110002c5000e02c0d0400308080c480300352480124480300740340250032100c0b0b0040038061a440c408032100d194041030492007040c06580300140c0c1d01940c2d2940e440801c000c96000c020b0014241240d02c0380d080c1040b4500 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 860886366 1250 860885116 860885141
    0x51e040311180106031a090708040c06050c0318010210151e0b031f0e100e0c16020420040306020307020607021606030b010e0d1103011b0210021b0a05010f 68
    0x400010304034890044c001c0c503007015a24000807151b0007402140d01000c0b00300a001042c9031405080082030804102c900b20303201d01003014005022800707542a00c1c01030100402840c01c0c0820ba65a00d0818481480000c2c1103110713642c1180304160f1184101e001541900031a2201d19040096100541c036501c03000c1803d18141c407008100008003c020740e50031078501160340602d104040b04a181b0810369421034900d410105080c07110918100c4118412900032218081040c5e032000c4009006000b10700a12080050cc0c0b0040e03401450690b11988005c0e50070440145448000c800d10801c0d900720740c00480e0595400020b026520342c04122065000c41180700a0503841c0005005c11000742044c4030340703004d05449120016440e8041e201010010002030200d0325141202e080410b45151600c441c01d0080d460605001400c40d00f403008500010043d400a000c841400030f002030095008141e50ba800e05030303100036844007060902000c5001d42c01040081104489484c052003206c01c014141c4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 860887616 1250 860886366 860886379
    0xc0215190e10050c150901060302060406020105060103050a060305060708042316140d060b0f0d20090903041809020d080c0105220213090615031104051015051e040311 73
    0x2d468441c0002a80d808000ea10940b0001750740729813460b03d02600035600020340c01240803c020444a030305500c4071b13200d901c00b681c0c284500c0c1c50354880c6404881d0703107000c05840b940082c400500c040e0700551105400520076061281d40c46c000316607030800c010140030080070903003065114001c4014a442c005025140f4900e40f1880d42c14800009581c03810311001c014019529200514100d6403511a425a016000b509068110352140b8204840020001010011030301c0303201c0c00b940e9070404030884d80c070400406004515103414074149070b00503060001348804860b1a0441000183c40e0200704021540c07180b40b5890711150700d49602070968200400d24040d11542c104042c1056200d25441c040386501694179601e4030005c189003d0117000403100107002d1701d0500c0e01810f00110300c2640401201c0c0110362500140c0b981c3c00422054034030035103000740c298004401c180502e403007100e10f040d1352064505102d03103170000c038014000d60148001403401c56242c0101d010002c0c08070340e8410b24103820045481 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 860888866 1250 860887616 860887627
    0x1712090904031d0d080904051e191107140607180e04031205010305060a11070b071b0b0403050901081609141201050c04031109070c0215190e1005 64
    0x42040c8100c020009420450301c00c80c00c00d81841000444465000c02400900c41030295007466443e59000c1d000720341c0140d16000015807440641280220f1200a5800382c002d80d8841000300600510401d10f103109580e5101491a800285070b00100141c501c61007454016018001e0b2143c1440340040000c824094002d596050003103441c485003055444200c4451000d89642c20100d0340c1c08160042c105040d840d2000200511400180e07061289203050300c00c0c095114600c090050764000c040005100d00705c1b0101181c4441d02411903000302030501d01a00310248141d454100501e502984c0c03d8000ca100020464819644403030901c2c1c1c0b10a1100300ea10210030b00c1c401c02415245544640921908034080740501641c41d0142140300c50341540c02417055041c00f485180c6664020701c01201c15900f40e5191000e1410b0070704074584900c00315150b50361400b26a80a020340d4000445d103140c206c032001c0000034070b0784404141400c41015030303699100c0c0c0040000103201c00003940084240500406112 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 860890116 1250 860888866 860888869
    0x6010608060d0303062c010b091c0311060c070203120c10050a150305071517010603050915040b040213151a09060403300504050d020a090501171209 65
    0xc001c1e08124180c4403442c0207046030904500074070b100e0f04254512a600c0c05d09044103004840310074071056030250320f22400d036664542906a07100322858503030003d800d118100201c038104946a001e65000b4100034030710708503090003031341030000450700c20440903004107280003542000c000201c2d10194aa038101c2c600341e00542c0c22903848d200000c1c030008031611207000600c10001138100b00c03422045000100d2002c0c1e26403a116842e400c031402a400302c050182c00320480035209803c5403103050b05000b5250441d90801070110041c0400070300c46e90303503881850f021030f0741601283c040900c500d00405c0001d1950415104200342c4480714001c014010b410017400c20f01e011802c078049021210f803a4018a1861310b0190904500d0180080050348024040740000600c20140384c083e44007021880d1881460036841d0400c81d103040c1c0b1105050020314144018480c5017841d0601e40320300f80c0000c260410b007030759402c4110141d8600340c01041420981310000c1584410810541240c3d240b20541035050021400 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 860891366 1250 860890116 860890127
    0x3103050615181e010b042405070f0f15050604050a0c0516050a06020327030c0a06020901051207030b0f0105042d08010203100f050303070f02090a020909090d11060106 73
    0x266441c00c0911480105500b601c84042e030741c81d00010007500e0310f02507079248059041a04148160128605038012689001540c41e401d5802114903031206400d0404544400c81101c0d82428101ca001c16603d0303891022481039442030075810007142000ca2103281100500040c0d5102030546c0707403c60b0502c0300070254581c100c0c050390200c0050b100d04006c030009030300f0481d2038500d060101500c1a1b10010500c071401d07840c1105600d00002d54141c84100d8102086500c0c2d9a02c100100808217820109045c000158150014118002c05140650034000020425541d540040e02d012000c40d685800c445442c1c2440208802084800d00f00310f82080e1034003503406081e009000d071003106084025403117540c40701003021507405041007000864a80c0340c61f007400c00f0407440034020030041c41c0c03800e400007446140000c04c03128a0381d8410408a04000701d41d00303000e8244000750080c5411030b002e2280c4542601c82c0520241f00e02d000600030052080ca27010050400641c04100080941105005010386500007 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 860892616 1250 860891366 860891389
    0xf0203090f060c120c0607030501121716060f0c09090b2413060f1407050309040e030418020d0f0c02150a150e04030906091a3103050615 60
    0x540b01150b8485412041034240702011802c90407030380300031600c00c070014070010352140700b07202c1c54404110503600d170b200380024070402d610002c00c0c0904078000b0706003103007401e800b609881005284a8403125031641e942001e030750042d0080f000250b070781c10036501c002e03901a0f0050300030150b02d0b0b0b04200c56007151b130100d12101600088a955000260008003100d882d0300e045581524510301d015a200751602802880c01500b10b00d50350002e01040032100310a069807044a04580e4884020341c43c00d4090030602014008030074101205020a00001822082142c0003100601d6100b40c0142e540800d20381c0441203a03202602080c40510746541d0300c00d016000504400044819490184641d44030740c1004058002d1001114903003800b118009042c4455001c098051882525404003081d164401219040c001d03110705d508444690b1410302610310b1900040c200104c58150b80706a91082c0080c038590075041d0328081c101417000d00c408106106060101d47e4120311080140ca00200d040f07400034681c080384 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 860893866 1250 860892616 860892619
    0x7060506100507060e0703240b03060601120b0f0a0603020a021b0d02011805060706020909132303040f0b0723070612020c0a050c040b0103090203060115090b070c060f0203090f 77
    0xd07000c504100000406c0038070019030703011208654844030f181062076034800010600b481103050941d500a0b9140c003080c8140704580680d42c1800c0c404080784044040c00c4e03039604e8540c002840f00b041c0301c5940c07504004000540782a460142c1d8a101801c8000d140c01d048120f01c504072850302000d0b42c1030faaa113200c05291a6024a0151642c46084580c0034403858244c0c021580841c0003e500701c200b06860b00a00341c0148100d522408681c0c030382d0072618840c80603034030081546544e801c81d03201d400000c030b5220228032030f26000c8a0405880e03103442607140f2210b030130080f40980c3c0030400e0707820050f03809070f00c506400e0200c51012050500002840d0f441300c480c0107407000c0c07180c04c0b40180c0c0c01c502c095050b00c0e90060080704071201100c05060240d1646844500d2034056404c1031440b01055000307008980380254090001c2a450303203030031015114040c40b50241e900b0800c082c0f600140d48002c582c00b42c04003501440a0074442460000064921241d0520040943d0000e00c8250348581d6844c240c403040d000c0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 860895116 1250 860893866 860893871
    0x1506170f0601050d020703031a191a090603040506040b01050a080d0f0e030a0b061302090303071101020a0b070206330f010905030703150c020606151e0f0706050610050706 75
    0x3114070050750907004003104a004107101007001c50506916421154580c040600032654903040300003031002405255042c1c0e014a42002810004008001d0039001c080c07602d000494106058030000880303d40c030aa405490640c01740c018001800340c0c9820040c01080c089413109601443e000805880c2e01900b80b4040500c000300c1842d242030b601810010104083c02020345a0300003c92070402c0407a8400e603040c134015080c4141582c20ba01142c42298a81d000081c0190b05142d21550750000e20040229118114060280088001101401c07414024a1035401802d00344c40c205000f02600c2c0080600a5180d64281012640306640522040c25901007039a2190f196a4204010b9440f030517a54000e517094818010300000344102d0b900320f10085482141c00703001140c182c40040382d07100c50945007664442448850b002540d4542030007443c4480000c00e6032a246000344181212581256014881400001460780f040102c0b5200d142e900010444400c4520404500010014000c600d4000c040a6 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 860896366 1250 860895116 860895121
    0xd0209070e030a020d03030f050a0c0c080d060f0f08060c1905092101020403020114040b0a080a0e07180c03050106050901030e0c090405010903022a09040809131506170f 74
    0x40b81400442d01594001d130564001041c03a140080040120404d87c070581403410020440414080c000d941401c07040355960340403d0141d03100c040890b4410300406134001d50b01e0100244000d0705046000c000d00044070b80b400d05920b480c210b0703410044020b243c5600300808000090f49a492600c01c0b41702070215260040d2108182c0c008540c1034020142000002d510300d50343d0079040c481c1500144156031003030361100100c085c0340d84c0e241954000e80c014011040014400004118802e00c100e0781e016418800205a91101c4440c5506000c1c031a045290f01c43c09002c054030b042612802149800381052804005a40c90301c08020054000c90280c2410136031100321780d44410008005580000800401d0900503041c2450a20b0081404480490241c0210510001001550350080040e85044e01403480359082000070050183c030020001c60b040c1905020703200c129124401801001d0041c0000060409102c074658418007a03a40d0002080011110848045409035180e164001c58080c0d4151501e8 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 860897616 1250 860896366 860896369
    0x260d020d0207060503040b010e04140f0f070906030b16021f0209010306170604031103070c0f030501050c0c03042601090f060b03030708071b0b0a230a1b020f060d0f0b0d0209070e 78
    0x100c0640c1c1d070220f814332800200681c41d07400031541d000c55036585c00884047d41c2c0e5564000c02512414400544600700318000100b5071a191070b07269400b2405441541c005d0320555004201c801f40034003003240c0c00c60307012488911958162144d08080c04446098000c90f511201c042a512580100000c04201382c0040e000b005c420100184c030010382d4005081c01d06241ca4080240000a5a02c002e40f076560900d00481d0140010008490610640c00c02962605003085003481c64040100d9a420000c0401c00100b0b040440a2052040261041c1207000344107805050000c142c030390101750701d0300c240c104100c0503002038000c0044a41d0694441d20410000c0c44100440144a00c07a600c03c1c1030401e000144003060355806194090701c6401c0e0030034034207940680140980540a88148200410f1310162204840e555400d41c5401e1184000c08503848020070801251035030b08002d40641001703480e0032000c12100e0b000c1c014a518038009a441888601441d00001c2c00c40d070000d0903820501105003e401e025 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 860898866 1250 860897616 860897633
    0xf05030c0d050f1c021e07060c03021e090d201e06040306050402030319110d0f0903240f15090209090f0a1116021e01020304260d020d0207060503040b010e04 69
    0x4140006c0001c011001c0c81c09080100e6510550b01160014a008001081e0354080d209840c15451115004604880039000d0b1504a41c0409581940140c110740c8240010b104021006090840d1114005180c90780005000704580140784020b032040e44911100440e84981c01a03504803034008101142d03545a90012a0031803140b00700c0120354142d0a025400034039084000240c1ca12a00003c44140e001e00000c1110090107560b010300000b402040100003040e4400c851020303a4050f851f4101c1e50040070b42035801100c5442ca603103417000352500540502690071a012000801e4051000e51804c074245001840781d05004002400d43d54041003c540c1d0300c0d149911003171442e00307803084455a41c0d5601013022540f0301d0145080b88182801c4e48041002080c1601190a149068004505050a01010600c0d8040d000d02c402c40c45404004403000c0904100b151050a00460300545800300c51520024140803013604890f041c05000c10030300c0001032148560328111400706c4400407154850307203001500c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 860900116 1250 860898866 860898877
    0x5120d2d20340f151d030c01030f1401030c050102010f050603072c010e0a23041416030602070606050a030c03080f041e05030706021b1009030f05030c0d050f1c02 71
    0x1c043c90b8140e0108184056800c4c444828103180c461100000016100050851904002c2d5400d500000f0720381d407da50003030700610380000c01c5000105080c114403040b00c071540b000364815900380e842000104010358081c820480320020b0048180080e1512401003a132b55100d9104070040942e60124541803081078444041c01ea420300d0504195659556544144056050b5444281c00d4039001c0c10320b508007028403500503c0303042c0d0040c0c11499526130b16007841c0f015111145402c81e005800029440c108010001c1020f103200d40782c01a00c91341c0d141809070458125070000c500039107280e2014000f140c0c032500c207213048070742c40f4032280d650311400070041c071603401070b03500c030450004544400c0340c03105001d241208191042682111011581c3c1c0744200d0ba140c100c0c1601106a0036a50541c1d8698101001c0141c06048507040c003082050381e80c0d66100c5510b2401074283c885810103e0500c0303207001c2c18070402d8401c08180c9001c6061664a410b4480507120700d0320008030010500c111520501c80da40c040d1303a03 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 860901366 1250 860900116 860900129
    0x10f020601052e0807090905060907110c040c1106060405062d04061508090c010c15020c03030f0703051609090b01020f2505120d2d2034 60
    0x10380c40c2d40f5910b0068140341050b201200400c0c26608003252500c4030b032107820700c103440091604499440d00c240949140b40b0300c10100206005030a1895074039155806414001d420a40d2036090210491010504103140a0714030b912480c24007081c082c4d0307513403130403610f1030701c41103c080b080b040c906807880d0340c03400c4038030380003081d800c035040a000188400a00310382c03040180c015281d1091680d200302080da1615494110940420841e01e18030000c00d400003821a111004540d0041c5021094000c1c01d14681040740c0705410707000c0310300c100030b5455414051035400c04e0402603030680741c88000c0d501500c4002d140c02003420540e40c030002e480d0035a01c02c000c4176a800d0340c944180c1e21041d81806200c43c0b050844100a407420003010400a40790824007001006400d0000180c9519240d40108460070800501d5805081c001c08c0c2c240030b034002581002186d521540d40b58050fa8841040d4111009d40040072001000d41010703a4042e00e003055480300404807221003000f613542c00c0d121148860603900302c2d000031 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 860902616 1250 860901366 860901439
    0x105030d02070b310806070f05030114150403081e040303021b040912030507020c03120409020a090b0c0703110f0315090f010203010803030f0c0a0207030210030912030f0b010f02060105 81
    0x54000e04e800381c040760039a01c01d40261901561703412001e031100c50030780c0d8810001820400041007450f48400c00240d0b0000000c0c14942040307401c00f0a04001e4000381c009855640b0000b44621400500d14280210810302c8192142041d1658330040d44402152070081c10240394144801070726a1541d01c0104203942c00f4440c50308500f81d12000800030071040b10000054803444080c843c03a4580003510320440d80000400c545000d0a00e1031000207500200c0522040c41034039080440c0c80407071000035018207841c542c000d00301145541003c01c85401a981380c4c0340a010f480a510704103460105100700b625485941a0015440d001c03821850301c91018a440d50551000c4004540c45401200070341c0100c3c001607404905482d4600d40e4a01441035241c54409a888408204018100001e403459407000078100000c0808881d120b0352000302618486000181d5038440d886166022446881880e042c20710384090b401801c13842c080d680303038018000c65129200b082d061a0862030117440541c030303411000910 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 860903866 1250 860902616 860902687
    0x2040e010203041113060522020f0319050a02030c0316140a050403050601053012040603090b070914090916150207150806010c020d02030f10050105030d02070b 70
    0x13a0402e11902d1150034810094662000742c080c1c0d550050300c040d2000200b6410700003c8500509001d880c0d180c0401c40466000d00804509884440c080e6101d41d0407048030000e44030340318140c03a0458000401c0c1614061052090003060303100d400035213502280d40c007a8200c0c1c10200c0c0e00b00742c0702084480818000740b04000740710411035522002600440c1c0c43f61044409503603c81c01040010341c0b414880d0b01403d141c12500803190700c0a8000503244540000640324444203142c90214940e12940050000c01d484100c0e0200304002120b606078400034614100140c50304203042c009042c2c0c0740101d101e10944500000c21603600c000d0084503c054000c810401c0d03050358607401c510201500130396400240c02541d400081c40385040c80030030b03518813084d40c42c1c80301580c1c5d000065410b5a041c840030ba80265400d0b40d020300585080011030500d901d500c000344680d82c442d04485060fa60140c03c040d000307801ca40323141e1500325000240d0300165044450100d0302d0303017044642080340c90340118000f11030784024000c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 860905116 1250 860903866 860903873
    0x40e15150a03020c0606090c07020613120c15110c1311031305070605092b06111305010203070c062019060b010e0f0108060315090105090d0207080d03050402040e01020304 75
    0xc24160031368030140c13a03d41e603c620402402c510200d0f0300218600d000c2110000625028008100b0380d00700d403401c1d40c00035803180403a162011000804881d41d80d4500024000060005002d21b01c2030071a15048003200c014030b003120b4a07000b056212038018040d024010300c56060541000d500070f04003022468172071a1500d29100780200d2460156014021408081501c5229070121040000c018007006810400050748e400080003000350090004258503500780003921a00900781a4180480e505859001030080f82c0a18049503201ca810b42d841000202c1c0002c25040c0e5404c03c5030407900746040c4804a00720784480d00c80c00340c5d4400613203029501500601c01400165092854000c060800c80801840010348032940d8080c244c0340e00c0440507250400540c41031820356482a03003c1c2c1a81c815240c0071800c03c0800c2001d41d50401c80d6511082041101c00c410020340c2405e914034030040071168606544652280001c4802d10b04154403100000c00350b4a803a040360540d50b071640c000b1580c0e49001c1c05e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 860906366 1250 860905116 860905121
    0xc0603020c2b09050109061407080d0906060311010504060804060e1f0e0d030915110f04031a16050301120305070c06170609070e01030b030c03060f010905010803040e15150a03 77
    0x42c500c40828203211004c01c1c1548140086802d41d0361300e031951801080c1d40c581c0c017003c1742c0180800702c03200282000b1410601081d03000340346400740316001c04540c5508503d4503c0306000c6850307016041250501c003c011803984031907116085a000a030000c2c591043e003031400d05240030038203541d245000040e201c1e204000690b10142055960a00b9101600100d10b812070903140e01d800c0c007500e284610780713030400c00034402c6d0b100c0900f00c20110b801c2881c1c05501d074241443c42d085a44141c51146003900c500c0c050541c204200da0348202484490020a941e00d080549a80010301483c41d802400d60808410540120112a1a140c100300040740303241d03807007800a0105c024010b40300d00c0082508003042f00742c18007208082c01521542ca8901c5062449001100100038609000b545841360041a5900781c41c18040e81e400345000100e106850340c1400c00100c00c0d90010303840001e4a0b44200800c002c1e00f00e4844409030000b0007100c1240759142c0c0c1d54005202071240b005c1c1c0d400151000100c0d9903400b03400d035 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 860907616 1250 860906366 860906443
    0x30406030c0203041802210109060611010209101b0206040f06032d0c090f0312110a0302070e0601020f0f061005010c0f0b1305070905040b0906040c0603020c 69
    0x15a001d200030100403000300d84a014900ca4448440e14680007900710481d5074019101000740071600341040400501c280107520820307444184459501e54090241603030081d1b0407031040030098000d518059802c0081500c00040d503148804001c004500e4400d18802c080c01d01d0300c5030382c00a102c3ca407030b0390300c454400c031907060948030300004240307480c0440d40c4607a80040300203001c2d00051028440e000d404604034018100ca1080c5c1010408031a5000c2034410540c60b00801070b60294410f0300d100390802d10060400407240e0702600c00c6a010360b48103c0020781c00560081554143c04c150061915481c005134a003145600080d49180914004031000c1840004c0041c8200d02c507808401c0c59a9843c801518042501d00340900100a01615607011604038030b41e00741c010080c00c45da0f0a2865054550341d04142e0386410482030030343c80340107100621590308040750700004035101803c035900340380d035509101441610420f000d040e00401c10955014040c8280c2c0c505e4000e10654550310300c80107035207c0004620 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 860908866 1250 860907616 860907629
    0x22d09060c1e010b1f081501120212040b0f04050c04090809030a0f0c09090305040509070504030b09060402090a0c08060d1b0b070c09020903060408070204201905160b04050a020607050304 82
    0x400c07179a02c0c0424480ca135184960040d540715844141c64248840c140c80d1511807455052144444a184002015100401d03003919002c610303900c94289442c0122554070042d04003440d00d8124410321010074030100701c14040329022a0300003840c2e41c452400946500590700c60a0707042c05031202d110700f0300400f4400c016a003842144941030890300ca03030b80c01044800b03500c0c028002032018041840a81800414135800444904003282801c1e602c0e034076082c51000445c3c03845184c0e00000300707000840c1004141c06030415800c007810300c201044444c0003017030a4001410203100b86203205611060010007516010803038148100d928409494605486183c1c1c0a405c04581d014517509000400a41d98800c1e100784070305c004d01a24190712540c07211070040d0861042030b81d00c255a44c40c80c0c00c448003612501002443e00030030f05900c8100c01402c0c01808418001400240b200410100021005410380302c03013415440b1401c05400d0700c40b410054689108290001e40100c0005031300700a010000010704120b51741c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 860910116 1250 860908866 860908879
    0x20616050f011b08040c0b0a090e0a090f020613240215100b0d0f0c080105040b0a141219031701090902010f0c1a0a022d09060c1e010b 59
    0xc0304802500f21100404030507210140b8145807801c25118150349901303d400b030081d000c1007130f4407652000400e07032040ca0304401043ca03401d4104054a1250203513540009054810400b10700c481d22002e04245000b000240704040c0060000e0031264900790542c09030566003100d4102071203003401189a1781e01c6030714410140c85085074101c6041d90612441384a0a1080442c0b41180d14207507800810746c0107a6004da00954449c52400c11500161181e2250551680d440881952401d02404102c0700301c3d1501502500c0207038402c2c03124000d0141151801a000e0312070401c04126061034504007480760508401c50007403803c004042c95800f0182e0301300070320100500209a6600e2111100b01c07854204001d01292050010103040f6004d0b0b80300400c294015442d0012000c0700100c200002c48080f60000946903010420a030014105400001c0300d070105c1d0050b41856034000c1c0c0203100342c040c0500e8a48607940c00039400901150620094040c40080380b0204411064016007502918040e50740502500c0b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 860911366 1250 860910116 860910133
    0x31632040801060e0108030a0e12150610081512030702040204120b0c210a060302090f040525140d020904060e0624040e0106050d030201020d110309120a030902061605 73
    0x48080300d05e0407900c9140046d4075001c2c010f06c007a0f40300341c1c9800c0b441c0c0e8130040c01c400c0e0130144e000c00e204081d5040302c0008254082e1500104120305030003401044010407600c03100b040135100400c1940180354004803440c3d6030000081a0691440c86400e80094102e80007040001d82d145c11070212a00c01c911910b4903640c0c560314602c1c6551280a0000c4048084041c81d2100711509261004d4035000600d400c9d01180c52510b0382c0101c2c181071000e46a40d5459103c05040206014040c845025148151601c45141c92400c0d0f4885030300070414000c0310111800111500300c5a030b07800c241d480049a024101c0001c4c0e04d081e040440040c450500d082e00e1601444d00002c0d81307a01100b40364000c0e0146040c42000b81c2c0301010603c001081520081d02d4190740e5410086510b40d1a07101400c0384034469400560b64030701c52101082903070003207154084954014400d01003404008200c01c117518046100070741e1991042c0e4811009030210110280d0040b4000507580d1081c1e10107483d000d00c1500803c02c448400 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 860912616 1250 860911366 860911379
    0x41215050c091503040c031a06042f0309010e010c050703020c03030f030f0402040b040203090c0f0a080d05130f0609232101240e010b03163204080106 66
    0x10301c80c1001c0a42d100c40400140041944518051034116011b100c030252600c0d2241d030340ca00660842c2c080b40d401040e2840812166180c980a09501002c00c0032542080490070500a0f00c00f1200450211034241d0100c006000e0001c254403061581c14207400138800e0240c805805070082d800b20300290014041c904a010b01ca08000085030b00c10211010145d19564491851a05001024104aa00c00d4581408000d20f071340d01d0001d0340c00b480f2910003070030348400d10008003c02446d4100085008000e120800c200c51a80030805002465103410070a546e0f182070500e0300ca6604550f04601015024a600400d00c00c1e40280100240c0e0711009141d0803402c92600385802d8041e02021090f844410080321b07034810a0840c1c070009007032000c0b10010070300723500d80180c143c2c48402e001801310414906101c20002d100c4070510803070041104000e8145107080c103114480c04030030701500c0348041c408151b00d44035648180000848000441e80c440b0320b4500340300c802ca0000703980701b8480c0c00f05940c00c1c18800f0515 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 860913866 1250 860912616 860912641
    0xc0f1036061b110108250203030a060905010f031416060806010323060f01120609051609150c2901171b13060b040801020306031b09061504121505 64
    0x142d81c3c02441c840320720072811004441c0680c006140100c0075004100024031405203558040f40443c042c0c01031034032498519001002c8904550044942900740001006200d410b000203100381ca401c200c1b8410030034402c02049140041d480002d85003800d114000084c915407011007540101c0d001d9a041c04443d01d912028081c0d40108829442300c02510804251b03180761002d10b81054020605140c1141201a07814038211003042e07020070000c5032140108250200050030012a40005003840054241410b20105204540003064030520240c043c40f41c05001001580d4100110030b00078010f800031445201e03042820080c85512808016032582200c41c0c0f0011070040340c02d07510342da5810301c546000010440401804506c44680540d150790214000244000a00141203900c00260340c90a100c001d240c504440c3c88a41c6500c192405103040055462540e01038000710101d804e4030500c107a042101c8030610a9078400a01c8841c060310f1303401081245000200071424440d0100855a9035542e000103 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 860915116 1250 860913866 860913917
    0x10f09061b0302011104170706030908121b03090a02030607142b06170d0203120a020307032a020609032d04030c0905090c0f103606 58
    0x12030034841001a405841141c01c4000780c1c06480085030361184280000c0659116030855045000c3d044805184410300f040840014042c0340b80400400440e601e45c3c030100e02520120005001d41e080c0400c3d1407120b403200c00403942c0c68140e065175071380c20100011555840151800ca00901481001442c190b0150201300712100178001c41905d401c0940c588010f6040001010050844003440e004424a003030748103803c085d25207180323011421015000e86620b8001c00400c14400c560082000341e2491660810454200d03000c4000507803a03494140c0154044c041e14802c1d80d0902c1c41412807039a0040c07120740144500c4c1010f40a407903e0f030711102000754503407040007400c44c7c1d101c084042c0c0845800b80305504010415034080c45c02d00341502c0e645c81807140e442990043c81b00540b0364003031001d005018030246802e030504413846444041540d000c580ea234a4494408018410483e01d8203c40c201212102d28802e000c4044140580c1c4103840c080a81c09114091617000820044000c00d91002c001c40320030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 860916366 1250 860915116 860915129
    0x207081204141e1003090b01060c1502030105060a0f122406030204120201050c0f10090c080615040b06250c06050c03120408072004180209060d030c20010f09 69
    0x503554018007060042c03071915024800d082554500c00003007c03800c6801c3c220302030700e501d42d18803031000e0040c10015512840f010310450101d204100400903a95040100d0312650541c1c107103280d40c0702d50144140c130700d952401c00454699040c01c02c400a400380c000401401c208039003002c4d143c03258031042c08030b0480c040ca01410803550050509003000d58001c0d405000d403280c1c2c8008807503c41d0708410340b150500700d2102d0440c0c4d640c1c5d00d03140b1440c09c00065015290180c4246070092605182c4680909000811003540f00d0245588114000140e1201001c5442d51070390100300d900015a910b0b0310007002416408187c400c41e40500d40800c9143c401c5040b01c0800750220011070500702102e104820031900503004031800711041001c0c1002465601003000c0c003034109420b000324410010240000d86480100d055400c40d1050944401a691620250340010701601d03885030b0305003146010f440d03141c0c0c9190081c1c014072560050899010f45514900034143d000c4c0d07510032810284020039200b07d207040c003c41 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 860917616 1250 860916366 860916409
    0xe0d20040c0302040b04090b061c0e011803230c01021c0501270e0a060c080708090601080a032001060b0c0d0311180f1306031b0e0601050307020708120414 68
    0x104810f07c20b54100411009000301901c4c50440c00c2941c01d44d0080c1000510309103035403601458100c1401c00c0c402c41541c40030441e03900c4009806564018041c1d0b0000d84101c00400f00403401910b00d48220041d1181035410f03100855803004540d00541c0b0810002001200356420117001084c4114100032001c0d8410703010310450800814042c1000190064580c050814418400c6400100e00310740034400d103404050310780c81034504002000034040c14004101e4004c561000004015207400080c10400c22501882d00c9482c1c40e000061b412440700d40e010080c0b0780b541c00c2c0400837510300b106500504801c448a400c851480003400e905070261404058807a4408030180700c0f054550211190081c141d560003811002d050400c4000a50072016040501c1d1081d541c40c1f4080c800c00620032061041712031081a86801c10340b0b008076003d49800000c21090420030007001281502b03008000c220080d110702d80580b00354105109110445800c944280c690101c2100410723080c0d410300c1341c00588a000d084000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 860918866 1250 860917616 860917619
    0x1507050c0a122d1205070204020304060f0b03071520101d1f09031704080d0b1206150105161101030b010e0109030605060d20030105180d0e0d20040c0302040b04 70
    0x3c0c0d40201c04c20080100a00c0f2007040709000617640c0b40300440c46079102d030000145985064404408a030f001c00840c50103a400184d0901c44498404424146800c5a1030801c52021090340b0304d41501c0c1e610751408441c2d1041403140d162880290b0003070f59100c8012008408501026401039680e03c070492200800d10f001e050849d42100644e411065505009082031304912400341c030040c404100454058990710408110081c0c80c21150041d90252642241d0340c0c5818620116102e46170180580440c032002c400318003030246030740a5020768807200301919440d141e0190509100310b0342994a000e041c00a441c00004810541c018154142d8541c2d040e550303a203c107410340d80c80340020b050152220b544044803100b440c000a24141580300b03600170002c3ea0312407a9032524103041c29510040e000c40d1005c4080b0002007580c020000c0e41d00030b0082c951a0240014200002003410703015500e0000c0c1c54000c103186c0001d950700c04011095460b0405035020403045003064030032130880c00780e4001d451900b1000c000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 860920116 1250 860918866 860918873
    0xf040308090a21050f0a1d0d03050412020a0b07151416030506030118030221090d080d141602060a0e0c1e031515040b1507050c0a122d 59
    0x4443e1031403a1241840c3c1d280048911a03034000f0340010f01408002042584500c000140c0701d20f030fa40c220708040e902a0001502075502803d0b0307000724001c5401041d90710f801d4605540d507100a12005101d110005540d071f000d00d041050800c0000b809034240c0906040c4800712a600c048100e5119403c0b88580c82c0b00b18145d000200c0250001500903903056403505184151102c50b0307610800c189100f500201740b202c1d0000102c044405030b420350381e80300000c00c1c03140009a80b80c01b03403411001c0b45d0240c501595503420b155060010a62000d80c0344060402d041042036980710240b400000740314076000c807500c60381c170b00042005a596880a9180b5a0005034080b0b510741058450010402c001040b40041000054082850111020701070703400c2c800c5a20070700441800384031085036005400d41e4203016402c1282c0110300303c1441c1c40d41105042c1400124001400414803c6a40504000300485a03840e510000c00e5081501e070309081c0c0d501c09002003c0143c2442d208030303070441c13641806070200606802c0d0703c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 860921366 1250 860920116 860920163
    0xe130f03050a02010b09010b2508121905040f0605090615010c26041a07021c23030405040c0302040f0e06010210050a06090b01110c150702090f040308090a 68
    0x2c660074155900c9945031940360f510608250701078140110616100d084040d8041c10740300d05031004c500c40821054804000c03607810421503c00307461036001c100c0720752910007000301c0c0d43c0041d0401018a510701414401040120701442d990203000d801e050049460303c0104a4540e2001e80d400c0d00000d00b0202e00b02e001354040c0440c816450b00400f0044d2080c0c41104441080c0510503003011000d920002d0140001031002c89400f1030380103100d0846041c00002d1740801c0c2013110340314503044209200c810200402c03981a8090b0400001030361500548801c000829517240c1150003024412414110300c441024401d109850440b141e1725403414015103040240e5004283c06030026045014100700e143d51400385000d5140590383c28075001400341d1400d002c0d64200c4802c4070301e147c10401581541c43d0030140002d9400021141140c0081038101c0001c510710080c030900304029000b1000904000081d0310705410184241d0083e00c2e0f0342e24a544a07610f01c0c2e210030000100070710b440c000b2100e0903445032040303 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 860922616 1250 860921366 860921377
    0x21803010b28030203010e0a0605130807110f030a120306061416060e0303070903050c1e01030f061a120a0902030d050f13031401060f060221070c0f0e130f0305 70
    0x240c00c60b01156449402103425601c40d0703002c048455004240b00d00800005111700d580c8040f10100d05148801c2c1c99071000355501ca0340601414646220b07451642c150354a461b60035042d1002421214445640d25090209411007014080031a1421900241c590b02801d04101444555002d561030405035201034040f08031551000e0301e00b507540e4407160f400d13a2001c10045000e00c24689401245078910f00d0310718a051160800f49004a920309059128800c02c65031b120203900090030041905030006200340f00500c03155000780843d54000842039034012116000700243d120344036003540141e840d8806d600584080f054000c3d01176010000250800344079001a00d128a06c00203801d182c00040701e42d00f81000400d03002500c0ca00b8141200343c00c002400d1107540014a608400614007915041003c2c2d00d44200d045800441916940d85600405103075045a006a5115013a0900c0d192a10400040407200c0d001e0700c0310503440300000c9080709045a030800001e0f94003942d65030503d030b8582d4040700c00d0b0700071 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 860923866 1250 860922616 860922679
    0x70f080f0c030c0d060e0102040509041a16050301170a050303010f05130e061308090603010e19090506061009080706020715021b060c010b0901080d030f0e030301050603100b0d021803010b 82
    0x900c404912b940e2903c08007400340d03010301140c41025036150000c3c8504640504014140c0440c220120052a044001c0c1e038112455400b80804811a410b0307068145030791428000c001303001c00400030604640d88a07104003034400980751840b096515850400841f042c010b00c401c0664025000507014620390200008028412140c0724248410b031004242c0580080c0c011036181c1303101030304021040008902260070418100014060030b000b40c3c485680f10300028048500802601800305006402920201e0081000d0003c490440c0d83c0c0e20402034031010a0f00034400c0c0c07501503109a0280501c00920055554150782880c08296400c6082084a90002c181c1c59259501da442c85200f075038072121401d000f400c090002d0f1420a0380c410307005046138103422498240b586444001d40d14540b001054a0548030305440140e0740c0c0e1911904c10345205143e6110b80303500c820024088610389401e80140c41c1c0308000c00d00009102001008150030b03615041d0101d0341102d02400711b1883d00341c801c0c440d56158651f = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 860925116 1250 860923866 860923871
    0x260c030d0c140406020c01080c1315020c0a170705090405070506031902031e01080f07051507140f1c0f0e040b0301060905180304120602070203070f080f0c030c0d060e01 74
    0x10003010b1414140c006500c05005078002c030080141e0303540c0046441d40e01000000c81c85203082c04090300030b032501c00e090113500b04c045001c00810f98850700810103400c1500c0b00904100119503140c3e8141080c4081d03c80000035030184d4000040d80f170030034404241c01903a002002c3d21180d810841480783c40e4100a005504947c02881c01610f440b04a1000f18054020151658010030881032040c1c006401a407010850754012007100f07507184004074038501070340d100b1a004858201081c80c0703600d46010720303000503218804000c130030301d07490300001454420034102c1001c1c3c1d450b10f0f00511603011110380e40d9a2030030115002d6040f200f070343d038403c845403d0081401880010040a100046409c40312187c10007081e182d560b030700703001010300c0707091301c1c0200706088200544c505801c1050400207403185010080001da004501c190444d0713001d00c500005020001034400c1507a6582220b659076401d01d40580a282c010204222198100420b6604003220003814200b200089955454014922101480419503 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 860926366 1250 860925116 860925137
    0x30b040f0602030423030a02030f030a0e0706110c030d0f05030612010f0c03110313031112030f190c020303061203040519050a0603150909031704260c030d0c 69
    0x207041d032000d075005a005143c3c48440c0d0110b44650b40494001850b140782d55482171248414031580042190b00c5240d000400c2c40c0c40c4c1c0c0750492844082c000c0021098414020410b002c9500c44d44800c0100240b9000012140c07442d01c110203040e1511546480c490009d03c55240c103211071802400207503003264000e040320700032514400311503086808200c0c264503856203500c0319802081d49401500302111180903480c1c603500344011030f4106901a040018281710040e800c04004030402e02c40c1345169040b003000103a40c0e10f002e8008952101c8211444c80d0200c600ba84c2040f600c2400341710f031024442e2241c0044d4a075844401c01c00141c51004a00081c05110070040490070762500d0000d19550400000074900041c1001c0c10020b181690360041d201f00b42c41c0842580309413130180018000c540b11101c0005d800340180c241151420003c03460750b03490440c840244400c112051410340061240010356100c440912440000203218403c42452035600c14400506041980c0d40050707a417010604142c008403 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 860927616 1250 860926366 860926373
    0x4150c0c06060f051002060915130f0f0c081b01120e07080304150809030a050a030f0203100504050105010c0305030c03060d020d08130909031d03160324090309030b040f 74
    0x102c0c01604080000c0a00c50b80421107420150b42281e480c03400c0e40041c0c2a585040d01d40c660f5900c04070150b1014055050000c00c140783c02000130104842d8100a4401c0703034124606202e00807030203460040300c01c1554002d00040d480c0780401d0010343d1418164038060107403d0031004441c03c4515084604000d40d4851020342c1840c1c01300036080040007000003454680e46450890381400c50502c0300581808021000c10206507400310803110f02c01e1003030404a45464881108400618040290a081c1880001402070a00b5502410000c031801110244020380c1c8038070044402c8462002c004001c504148041032800c180380c00a981d114202500300b103d10003942d00011905503801d2810f0b03c0049002404004004422203c03101400e190b04040c0569521a507000b007040e40040e2140c1c00f40208560b1000803580e0503c240e995a04d081d8048455454490501c07000424810500301140c0c1401001d0207a4003c541c00f40b1301d0042e4160b1036003a015880d503111400d2020004100b02d40d01c01d90482c051000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 860928866 1250 860927616 860927621
    0x1030e03070311010e03031006181d04050f030a020a0602160602120901050703090804170705040c03141609030f030302090d0f02010813081c0b03030d14010e04150c0c06 74
    0x5082c040eaa40c0c148145600740f410303003140c015000a04490f00100101b09850f25100581d2003214003500d00743c2c0045441900061010806400120a0041c0300454000c008200114a400f0314090000d07a660350012100c0e603aa0303032140b0500040580c2020030520081189680a09443c5540f040c003a0b00400d03156441c08202c3c2d0107840c09180900c804401d21440400034400c0b60761082e0310b030030204002c00494540031918000e5114130383c0060b201e00d034149894402800301000420000d0000c0c81048140701000d005010034040e043c10f2000150005070045181d0401034044c51800d4442ea26940d040d0740325001106951041501899001c10005840d42ca40c1c01d01c0529840c0140c01c4850010b00310b10005116840c00b0f8540341101c3c2c00380540a001c10340002c1142c0c04c14802c10910721180b9800c0103080c0203030400c14507907945404045049203011030f040e0001080d070600c8013000761061f030301c44042c0f888119007038401420324030f414019038a0036441640301c0700031910b560402c198031002d103680c0d4105 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 860930116 1250 860928866 860928877
    0x200a0305030304032001051b031e070801090c0e1302071b0e04020a050907080c030603010608070902030a14070903031b0b0a0e0c062110080303041a0c042301030e03 72
    0x8041a105c18901961422401c02284114000384414180b21300700040e4441d504c0c019038040000000460800e03017608070a1103208100a140704000d191462015041800c01d11824010905140030078000c648604281e00501200038007031a51200e490041800941040d442101c15034110080581880d035605030500c0145540f04905403a0300d024030510001060f15802107025200000030301210391780000c8803a071f100441c20f43c50b58a0342e0702c80000a015084a40c410456402480008a08203c1a0b00214410328a10109000901c080100b030508142c0c211582400668240c0f8140002842421625140e641070001200f00f1501c507101e000996100341d8403200003596036000810201c0e0107101540410b0401c560590602900329481c0c00003041e10400c1c2455043c2201c001100c0d07003400b0403e0b0000d40529411281c80385041d1419414148440e481c580c1c510a0b010000703003003422540c00300c50070790f40007180c8084000c01000c0c2d40008848120304070b5061648a19034090010010000b0700b0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 860931366 1250 860930116 860930123
    0x141e0c07081905010617030a0c02060405150304060e150a0504050c1201020703030b0114040311030a0b07170f071403061323060a1505030c0904060608090607020a200a0305030304 78
    0x42c10078030700e801800c44030182d00c00c0d02580001c2c1d81004c5096808010b5820010176410b11000c203501a100090542c0b040d5081a688440342c0c141a1282c01580c0e03015508c0385101c0e0508000103504000000d9880c140400032031000d012020001c0c01c0b158044c1c01c0b803600305100744100c801c2c1080e280c0010710311241d039080c10f2126a41c00305040003415418007821081311b000b030030f181200700a042c0c4d441101344201d0101600704290f00290181e180ca041102c00751030b43d04071400300c1d02410459802850b032281c0c0342803880c03000c511002042a860f181342e44c0038041c64064541c4900ba02c00401030080340e030402811642c1c800070244080c4410311050044035039203c100300e0b88170300c0d01030105080c2001d00f0000e01094050b04990340d041c046041228000701c40311510f42405c5450b9641c000f114484c9108051038117800c503090031800500c1d80e400040c0c0324054100541614456550030320100d9070340c444040d01a03c0d451b501c241150038011000444012554040c0844100c1900c0e80c50741c3c0c2ca194015101203 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 860932616 1250 860931366 860931403
    0x51009050d11031506060306060a0c050102070c051e011205460213060e060f0d1e020702010f031104050405090c030105090307050706080a0b040e010c141e0c0708 71
    0x70180780604c81141203c000c5074080d455400c165010403440d00000b86114000d1100040c584c1807070340140c544412041c1e0000c025540c850a5191001c45403c6504c1041e0040e00924820104164071713006d6aa0300030780c1a90751f0351040d4803000ca4070019003001b8115002c2005c0c0501c059143d0701c842c0b0107040d00d0b201d4581c581c40c802142a18941d0f40c9600e26428808080d00c1402440700c84044e40c0c3d00c04044030203524080514400c0a4000b503032512600e4039400c0240400982040031100316005064400c030424424035900306000340d254240c3c803c00ca8002c2c00641c0130030000c0c403c82e00941c407a100400100141a00306602c880104040710b0040d51400c070964072103800d14103285424010503034081c00040140d820504e0681e41c45591f001c003800766805100c5a1000102d203911690302900c1c4020004005104039004480894020502c0070740381000a5844456025401c1c038100490b5032007050080c03200c1e81c04400c4511076859822503180b4507010701402000040405c003c00c0a05550501d40116 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 860933866 1250 860932616 860932643
    0x406171f06051008061c0f0b0907080f0d02011406060904050a0b06070c0f0501170f090c0616020328080702060904061d060411090103020711040501090c17040804051009050d 76
    0x800034162000c501c240c03115a00d213503001b0300146400d040060311540c004000201500c0b180c0e0036504200090300708503030b5032140340c0c0d070100312070800280800300c0105a0000c0096045040144103006011110319402c004100b12403503440c20310360300140c0e010422040010705507080384c000400315400000240d075101c0171800e050013040740041005000345402d00341400003c00700c06046222000c018099441c0c2030400d00000c04440044c41226007420005003019500c4036800340340800402409001c0c0c0c004e114808001030065203961103d0401c9600401400174804a80d551855a5120020072031f00440148102d081d0342d10f6501840c406800000c841c084511649000c0712204500144400c0c400c604100314100650201411200080401e180259440c0003604040340c000ca005614960000d123480c00000d41e9a185501c4a10794003401d545003940890010340300d1020005c191400341c200501000b0810981c80c00324100000b0300843c2c00e00c403804690752030010340f025070540025076040191202 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 860935116 1250 860933866 860933869
    0x10b04150e19120b010e07142d0301030b07090f05100207090603060203161b02120a1209080d0c0b060120070603061401021c11100216020406171f0605100806 69
    0x710380c0989602410741d4060315043c00000c00343c8c00d014041302821a400a00302c40f42c200c0501c15541525004e980840c000c0210788040301032540300748070030740d102c0c05110301017175101e8410034807603088a4114840d101c03000d05141c204403460a40a80010541c4601c090000d40c254450203801c0065018200068480c81d000d402402001a103041c3c2400f00041d00108a140b024480c03d00d00c03a1070b4050f94200302400c00d60117031130f14000060401030009881110300302d00c8654444000010345524105484d455128960141c80e1042c404100910035880d0000140003940304240c404d104000c10207800000701e012585090034201144c00840001381c84034401e003c040c0440307c109180e01001e100805c541050441c076803055500d0b24400c0001c012a507800f481c01e42a04002860400088060440d80d480d00d1846003074841d00c214404074041c2e418110001401c642c2c5410f16411840d1a40160448002589800300c2d00781c00b20254002d019a42c12000c07030701d40c690750241506c611407030b169007495050000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 860936366 1250 860935116 860935133
    0x181202010e01050c0d15031505072a140c1e0301021e042306030a0902223309050430030e0c0102030a050c150915010b04150e1912 57
    0x2c20a140342d0709800082000450094208d0507214021000140c180c6030900c0490710b031340d4408013031000f0804d04507405602041e9040412403103803013001441c01c1c107050040701c00e880b040380d100c4042c0d01400c0e801441200300300020041100c0c40c0d0040c0014605030041404102c000042850744800b028046428480b040011254400200d010100e1660001d14480001c640b80320045c5041d12003034640c0901c0c0c00f1919840b10203140d0001ea611000e01c00c0440d640e40340001e12118004d02c642c651000030508202c0602282592340032000b102c00200315090800b00340140c030018004075403101302c600c0524250300480706542401e0305903103140c1a4924104000600355101960412025049100080c6e85607800008035001c549042c03c100d52102006155030741000350480c2e02c0550840d044040051401d4081409889514070311740003040e0344d813100119171903806540035a5015610000d203400140740a48071104003000c00030048410610121040345003441c141d400880c0510340c0244040c104071091 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 860937616 1250 860936366 860936381
    0x120506060f060405060d06090608030a080a0209010215100305030d1a100522050604090b1e0913080c070e1b03150d0813080c011101181202010e01050c0d 67
    0x100c070514111414407002611910843c85564410702c4001001e0050041641000c0010022584c040100ca540d17002c1c1c0f00d07181e0348440820000120b0310300014081805500c20303101d4a5034103a004207001001215030796100c1c100505003242c0903401d24000030004204000402c2c0c085d01840780400e4070020119038013501c00b024940b881c41880340425801d80e03a54030400f65004094041502c0c240d4482801c80c018119415412180c2c00071000200403541d80c5181d004030004103400c0c0c0d00b0f190049121290400002482c1403250b0384080e0369030100b400b80d1000104010200c3c01035440c1850300444203030ba00c0c03400d80c480c0e000c101c210a0007800c001501c048041000812200440992b280d0320b014850107440b00442c44c440307031048020340b512001784a000b80a8071003882509107144402c139250380c44d695445040d94001400100100f184020400041c042c101c145c000c4c00882c901c81600070f5039865140100d100e01001150359991240707038504024000c1c640625110f11400b551000f400d081c2d81d0594006 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 860938866 1250 860937616 860937619
    0xa03020a080f04120503180f010203010302030c061e2a01090312140a05040305070c030c141e040b1c03050c0f0c1e0a0e040317010501080114010804051612050606 71
    0xb00000c020202e4102a400e5800c035496203440ca0740d90781c0380102e140c12100601c40e04142441107501038540f540301580118107984c021400ca030300e0f0007140c0041101c644150301d100e4811003000c0050040761004000541510007020780799405515400d000301c420025152244180d6a4445110000b07154100d58000300b15040810148905000d241e00246d039140d01506950040d680d600c00103090611030000d4400d86680407400480440e0b480c2408100c3c00d14502880c000c1489a240c80041032800b54110031a864540d000c1c020158401410040182442d06100d0f410001240c000300c00c585035600c41c0841c8034425242c0c192100c44401e000ca00e03041c1400359021140d405910713607078001e0351200100c4004800b1079145a58112018010500e1041c141c0c0c0444011541d0005100405030040034001d04000340b00018113044c0c3cad0701c1c0011a00c1070002c0c4107038444685813001301e4403107512902505511502880c111002e51440c44400b03d80310030140c2c85034800a0122a0702410400d09002c4207802160 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 860940116 1250 860938866 860938891
    0xb0a21050406021903020315010e0315010e07020c0607021e1f0504030302100212061c06020310060e030606300304171509030a0f180b0417071809080f0a03020a08 71
    0xb45840e5548c1c0f01080b0004081c18040100945095981c08129040c0d126042c58400c0701c06507900c0d04041203a103001d03220b09001d4001d0741c0c0c5000d0075041a00658403d0340c4c0040c84550031a03200d07410500801a001c0800e81c115a40f04070b11200d076100000c1d52003038049169201d65481d1300e10304000741032048000d500c10a550040044034482c0031010f14064000c4401c0754488060028034142c030318005e00140c401840c650003c010080c4c100b550340c42443c11545281c440d0f51031302e6043c00400d034031008100c608030351180349049255030b09040c41900710308603152000b038205410040d24440780356800075401080340019103440c01050203000c0c08002c00d032401c5850030b10801c1c1000900191030380104050701c810001d82c40002d0700981c0c07094042d110516080031442d51910b48a4104400325842409060071070004400340c040103802c0000c0c100100d81c4400001c01d030444078001c00c0c0001d400d00000070f0300d50b514140084004c1002240041500b0a07184e01c005031790342d1040c200900014030040000c0500302 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 860941366 1250 860940116 860940121
    0xe01090906150e060c301306030b0a0e040602041a03040302030a2a0b0f01060e1f03140c070204110c1c030e1e160b0a210504060219030203 61
    0x100c141411030384040074186100c0b54060000456403d0081c50340e03440035485030241c0c11032982c030004083c1803868441820b0694009070306c1a15103e1348500d40019a0150745444100640c600c41e82c82102c8203080101120007003562040d016000c01030543d01039541c0c03540041d0421107241403162046094003840151411441d10b6140a03499018240c2c0120910010040c000460b4403c2228000d00ca00f400c41c0d50310b0768025a0402806445044901c29803c41d1030600100310b040c01107444c00d502400091134009100807440d2001c00480980a00005154441041191141c07040d00601c1c40b40118580c0c19440701b400703004210a5804c0c04c00080c04c403070401c1189488280c8086450b015008164801c05100301c0b400208500a1001c00c941d40c0d124000c641340c200405074110420082c015041040361412103c1d066810b01d180d0040c03190703540800041060194560040c0001d4000131195241d01c4c06051450b0142c4082d990300b1603080360030507400650744145440440e030040c2c3c03101240c0390460562 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 860942616 1250 860941366 860941379
    0x18060f05060a050f0405060a020f0606030c0a031103010212011e050d0206040306200f0703030b03010e030301050d24020703182306041e030b070203070b18100c0e01090906 75
    0x500c59582c00e001044000102d4141c042c4000003202c000301406008156251450400207403104a40108091140a03d001048582c5000503903d001103800401f46688646140d80380c1c450045c4107034046802d0754080c4080c1392001d02e404190b07802040c800c1c0686a101c06606103c0001e8070103500b03d5841001840250000341e166082601d0940b41d00030000540e00c104146081c0a442c803040e80001c15400010b40c1e9500203a2050150200c0d5104e520140615090002018241c521200244010703a1080c0010440c902d082c1411400803400307000300c5028034110440d040d88850398150700003079403038001410004055000d0151401ca54a80d00c00d124403d05041900520286005500721006139001e6140c0141d620f50048400034804808000100d60301600012400481e43c802500c02007074100000c2d60441c0040125001943e0103540480c140e80c40d8030929060369032551902a19100f4218894072601040c450081400941d44031400020340c0100010304100c059003024034414201041003140c1c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 860943866 1250 860942616 860942629
    0x60f09060a051e040219081b030a08070204090f0b0702210a0c14011815180b0c03070c02060319050a180b0619030b0103030906110303040b1b0418060f05 67
    0x1070f590984403010740340e100c2d40002041310380d0340620360701540c840c0080041c5501c0d0009082074200b041c0c44007452408110802c140d00c804d090395014090040410074800140b500e5401000c0451148034030b624401c416498920110401311210360259101c012030800f00203961540c1281c816620303121501c0d0007811107004107617130b40c5410014141440c903461401000c000b90810141c002107a000840004a181456107401944c0e1050440d40d03807811054429140c54490554405030300241c5401003a281d2008401e980d44c801132040d02000307081030b664001641c0b500001c502580d800303c4010740c40107228000c107003101d0000e84105807117840c20700030182a0b079450310070841c40768200506021542c0c0340e0300817940315500f02181c58481500c2420100070410b9401d2418180c9010f0303600c04003038644941c000c1d204008a0581c0b40441e0f401480010000b415450310150302c20700101d4030b07048140260411100c29000350700703c004c551004c200801c030410715900c9548014150810220109490040440c04 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 860945116 1250 860943866 860943901
    0x10206060d0f12021c0203041805060d14010212010602160501030c020a08130905040c1a040302090f0402040914031806040f180603120c12080114010c050f060f09060a05 74
    0x4003c4503141c2120307a103000b40b10000e00c10401c40d540d8641c050549034001d40700c0d40a1302401981100c25030300c205100c48144521403281d00060401c01e1000010b0700c80c07500d65030392014540c8071903401300103800c00c10a07002581070007020950001d01012004510700805486070343c00030341c1010324221700010b01990000b01d0724155600580d01035600c1c401010614456803c07500140c601a04003c18481080b6030103444c0021110204e003c01c00d07007002010f444505124610000e54800c2c3c0240220b0310348007040140c03640243c030051002814041c150341c5c0140c04100b00801400c250800f242c40c044120f01d0b04035002e1503000885000e0318090802c090008d908140d0302550009803a1034004650074900313640130310003854210078000c120103280c14004102c030070025000c46425041e131906c10b0100d40034489240c10f0740d041d841d04280c0710000070011540350072902d03800d54061003802a030707202007001031041a001e10b08404100c4420724065405a261002c00341003503104500d80000c000511203400d401c100d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 860946366 1250 860945116 860945123
    0x607050904020a0e0301060e0f1501091a0c070f090b0913080a0c0f051b24090d0606080c0906011403011401110d0e04150f0315090b0c030402010206060d0f 68
    0x1600d40f002c8440c00c6405080d580308958040d072034a0b4010031120b4510407254498402d45441d40000d42c2c481d0015410032002d48030791804281c0c81401401503520b40c43c0f0f8008042c0c9408050307418031076500843d9140036180d61080c000c892100310140180c0f00300303004008403480140ca0389903a80c1131403090f80c00c620b00101d0001d00030f11800300c1d00c814580d104280348204640c0204142846001d1410041d44610075904034030038114a00442a4803420100400c05030905603a6040a0230114800c5611190340f00542c010360102080010100203000c0303100302c0008d003035010002c00c0c00000d244140090104d001d0003d5060210034104103072620422000c80303040d1000201689200c01e403110043e20540f0040403040864043c0c0c0000c1d03a14103502400340380c061642291b01b4498004100c80080c1d48181501440c424400c01d01d07014800301e0007016101401c0102c5000000b0b851041d070721411581003041c0d6404d003444400006110540d030341001050380101045030290710304103850307a480351032070680031004 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 860947616 1250 860946366 860946371
    0xa11040905030702060a050d05010e090c010c05070506160c09060b031b040b0c010905070f0513050c04052214010e1305010e0601060918060b12091609050114030607050904 75
    0x30000c2103000e0099030301e0194041d24103a200d09205901800c0354000c0c42a00040d5880c00c0000100b124505030540d0003805048040c0c13100480d80c07001107603d1000820140c0341842400f100052685900c0024442e610ba600704802c40440d0501c9d10b44584140c41e07001500309802d00b030b420302220180c1d104498201100e040c00c2420340340042d015505074015580b224000e640c0125284840c510107402185505101d00e041d200940c1d1550340c002a42c120794003542e0b420604200340c4e0003001c9082d510580e004481c02d000f542c2466910b00001e4610381c04c80440400307598030301340d00d58000411030043e041880955446141650306020007861032040090158a10380c0f00c20012070f0502c03c0c294458103003442808140c036a25070b1900300151407000389208000300540340c20000c0c20154000e1040c5001e80e102c501160b407520281c41085000b0190190121010b0700070048202d08914a040140005014010300403906600d0242c24090741c11440320311a000f034001c07000f00310200758440c080340c0e130b0f000c001c6500 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 860948866 1250 860947616 860947631
    0x21206010f2c040f0b09010c02030a05090a0e010b040e16050a03110904090b060a1a1225020607120c0c1b03020303040b09030606060a1428110f0a1104 66
    0x140342d9180848241034065480900502061158030016060201d02645e403010541d00d40b04856422980c002c2884001a04207001c140f103014032600040c580e40d90010048110241c44a0a07030394800402e9010000396000064200002c0c4440011141e00c01c402c1a000100c01e510305c5170242c00c9100d0611800704142c0d81e240080c07505840181a02c1079840040c0c030030040c25000d454201004602a1440c43c07150340400c000203510481c0301c1c901e14040d0082c0d13410300e0030004025650005044081d10034000c0c4c46d540c400c81c900005281981e41c2e0518000c4d401010a800d20120103083c01010340098000349003480540c17604903800059000c0e01540c000200307205401c081845903115035040c3c00080d454000000c0000e1280350b601c000d4050064100c0542d0302c107460701003c0020b14071502c0c0c14600401c01e034217040c411171000b501c09090703100c602e8504100903280c45100302c071070128840908004100510f0002088000812113010f166030084002d10202030a41c50b0ba402039030035820440d200d41d403683e10 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 860950116 1250 860948866 860948909
    0xa0c08210d060e090705040f2304020a0b031e100b12180106080a0506070c0b0103060f09020d1b050a2d05060703090303030b03030f0706020331021206010f 68
    0x2c03800c000e0050b400e0188031410060302181c1c591055201c0c5510442c10079520600c020040e10403074410b4001d02168181201c0ca01e8202c004007880108180d9000f554144001a252030003030003180b0a0000e4002c0c05003204528202120741000038040580f0f928488a0604c01d4000400442d10407032601a00403066a035800310907403a601e20110a08000d5003000c40014240c000002c04125051041c801c0d80c10f02e98900b0002c0352841040704c0081c004440080040002c524150701c848416501c00c00302103280305e000e0700440e07030321100c0d014115204a070000540070b1640d4103101c1c1c00c014000480c3d940440da460407102021101c1003210020032119000409400341001a00360402000d01514103915188241409031280f01244401d8010a052001e00e548518021049a21040c040e204450400c117040c0c07a03a500030f40000707245089030400c1c503da892844445c1e94050740c8645540b03044440350715061041c09410034600303003e0f04559000c10300600003410502c40a4060703452051202406012010 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 860951366 1250 860950116 860950121
    0x80a05010602070e190902060a030207060e0f071502010b0402040f14030a200607060e0102120c120423100e0c0603010312142817040b0c03060d020306090a0c08210d 72
    0x200088d4043d8000038180807a41d0140c014240300c0c0e000324010403040010401c2262540b02900160b40381d80c0055406100c4e0104100a07078210b24045e1000240c0c42040f0008203041364003a410406480080380e008002c05e00c9207410031000c40e24180e01030030f24204c155541e030b40b40c0c44240f1145883e000c100c010291040e226001078480300b030741202c0144040051048064004e5110b0341c1132103011309a41e400108014110800c441200e04040007600790307580c8079202c07400398450050020205246400b03040c05280700802844032000301086000400c441c1c1c40c2c080d20f160901c0c008a140c05082d050004101007201c9075084504640c0310309100308a4818201100d040c0c3c0b141107400f04040d15100c20344640d480c01d21602280c0c42080d5100c0012100d18840f054646980c126001450400c0d680d0005120f40b401300090760f000400609640300c21038140d80060b0034180300301d59100550740011880c000b402002c00c440002404880d02816500c48080c0180d555102c08222000c516500011102c200e4079066 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 860952616 1250 860951366 860951381
    0x2010c09090b180a050601180b07031404031b0602061e0f060402190305071803150c110d050310050a080a06020732060c032202040b090106080a05010602070e19 70
    0x141800304451130442c000740028801a204140060500203445c030030080101c8100d000c3d80ea1002c2c6450a00c101d0b594121103420548000c1e10010200b484000001808420100c44083c0b4144600803c241007000007860400024441c0e201450850b1600081d00f22201c059a08a4a0003001440c40d03901c03000846c02900c07a6140c00300b03800b00402c048080c29036041d8001b600500705a83c42c10b6810300c569100310203403919400040c04400180b01a07000c0030300c56a01c424070460b10350411803400303204102800d0400c2c00d040c0351200401da001042096028401010030080c0200301c494210050411102d90755410314136a0041c0301a6000940b04240081100c6000c1c2901000c02d151800080903c0c00291083d12224528028450b40c000300d01c4061320b05060f00c5c07141420982c44d014170000304145c2040ca502d00c1100ba60001d58840b10f1104a45443d07221f14064089038035480c40c581844042e0004580b0164041011508801d8040c084148008605500b040c020311000743c240d12600e44510040042 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 860953866 1250 860952616 860952649
    0x918040203121b010b01390b091b0d1e0f050a030e010f0e0f010f11010f060f060e0d08030603030d060e0a0e07050d141f06030204060602010c09090b 65
    0x40f450300c8018007824002074140522000030300070805004019201520300303050140d41c00d0100c80e2460340800e80c0350610301e06030001641c04846004107803102440c00344141d52900c0d898005521400491803007455200091806998007503503c80c072a00c4091451404000800200c014195120180070b640036410003925001000d5807003e56140c940a0103180440c82028007190032030340c114800034000d14500c5022075004d040c001403001c01078011500a01362050b1803007032224408084411080074070070510a00c09260303002030100d08059100c04103440710381c4110304100b400c048075240d9460f041440034003258401c10342c5440f5140c080010f4254003d0b0780880c2d40d0702d4580303440001c901c18030b06100390180c640c1c035100300300d0150b5101d0f0b60f0780c660380a8040c8030340107040105894002040200030006004800701541d00e81d00c0041d80d0010310211421140c01c2540d00e503101402503282910501c00202410b0008003c002035044024013201207501c241420659204500140c43e103c080344545015039 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 860955116 1250 860953866 860953903
    0x12060d05030406030504030e09190c1704121806020c10140310050f04020c03070209090a14150a0e0a021908030f071a0609130606050907020d12020918040203 69
    0x11590f00060003043e04841c10b50008880030b0300c0003000c1c18a600241e000d50324404668001c40502c002c082c014104203040b20b401c0040304810440544428030740280a1845a000441c640c1c1c88440c006084040a0000d40d05219071410104422034000032050302540003074598079081d5000c5203081d61903003070030304168042500000410030050a0400141d064800444000c5203a99070324007448200c5c000d203912840550b2041044c8005807600700c564503406114801100c50142607075465502c00300c010101060603502c03004804008504400c195540407420700c0f0200011140c0c103811075555074050b00c1c040e000f041080d2058110050b0501004090030850044994031092980c01c031207154486601500e2550300320b581251090310740c8648500030140141140070070b032240181c00c0e0103a03010140441d04183e0340c0741d0000b110381341c1c48030151190886401074a06d55400001c040c00480012900f00c0c40306104102e010807030b5540414124458139842c031180100c0d03881c0c0c40802e2912a424490301843c48 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 860956366 1250 860955116 860955119
    0x216140a021f030e011505061b1e060f060a05090a0f1d070821160f1101020d02060c0301120501020904020c01021c0b0a050d0320010606021204080312060d050304 71
    0xb607440d030420301c40c0180340d504010b0458950f030a103080b140000303031005852603100d170304100600c2d009020f001c4004100d490b0400340e111520b15a4645031a1610448020f0390070302ca0a84809410300030541e00c8482c0305000d5100749000f40009040c60941e000b484d20902c04d840120b0341d121030a510912482c80c1301c00007001200040b504603501481380c5404032126104202c00480c0058000c5a07002e420761510328220310301c00c152440e1900700e0300408141c0601e40b100032844400f0880101ea00c89002d40568180581940b51200090411030000602c80555000d102400009504141140d046a59070b54040202420514084d030180c802c010030640d03c43d0000c07842e0540920194014000c0078805580a1100c00c444029001075134041542c0c039900c010142c108000600780703c1e0003001c00e41e20902c0c129442c0720400010100c0300c0c42c050b45030880c986d961074081c0042e580402410030340340455482c850809152102075070f0742e40324076285804d00d8000100840c0c41030f11818116650240d006013071300d441d103 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 860957616 1250 860956366 860956399
    0x5090109060507110c0402040315020306060c12040f0b031b0d0b090103150e0d020703060b0609192619060b10050c060117150705090411040f090216140a02 68
    0x4201d20b041340d8001e401002d40c20724403840c0c0b0b0700c00c440440358000b074803c045546240c80702c1c0003900000c0203a030304010f00300071001942006100c959200100c001a042c0c84604240b103510b900700c01900b00e0140b9588c03c105000448580916910840f0102c040c0d05640c0d0320310011380f0340580400c04255801406040000c020043c02c4140710002c01140141040412800c440203039450004258250258100b4802403020a00c2500601006180030f0300081c60000074401003002c0c101e042170f00310b0b50f06519034002d115850a040d442c92410341640039503150744c5418400d81742c8806101d00420504500c2c1c40c0c0c0c501c2042650b40098040d140000c0c2030204000223004090000d6010400300e07101405030034008981c524000e448000e00c0c1180e9401062015221100c440e00c4040c06000002403203000c2c0170340b070740c5583e80d4050210003d154120154a40e4a0801100d04030325194210380b00b55401400302010b00300550710310098143c0c0008801c081e5020880007a400c00000100194001d00528440c50740f0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 860958866 1250 860957616 860957627
    0x60504021f0e030609030313030c0c180914010209060d24180e060103080919050901230907170406020c16150215070f110f0708120408030702010305090109060507 71
    0x90000b43d0a660030350fa03420355a00d40340d110841da0360162040030768546011900ca201118091072040e208120120b80f00d125a600c02100000d100c14403a44803000e0b0001c02032880d03000365009515070002c2d802e01c07000324001822800f0b1400c2450003166508010118030181c03a544400041c003210961501e16160000800c0c40b00803010a003e8060602c6045e043d10703000040c4040c100c0303400c5050309003000400c00800c803a03111503056901749218031400204847c1c2d505201d44e4000c100f0340500c4807101c07458541c24861100e01502080c421a01c010410802c150801840300380801040d0710904503580394078269000b4010082c040d4010b10500c041284020510391803031083c2d0b40202c0c1010340d01748410200700e070381c0c02d9580500703281108800081214140a00c90542012500d4145500c4142d03150000d185008901000a0070360350205004104c0c0700b02c180720221091401e00c410624041c24184403d56901c034510000703040550754800903180480c00c1d0f004643d55075004400340918100300000410 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 860960116 1250 860958866 860958887
    0x220e01091a180a0210030209041b05030612030f0301060e03030c010501030c05040e010515040b0301110304051c090308220e090a150902030703110d0c062c0607060504021f 75
    0x5120b1801181007414100242d540000c550050801c1840288003804030007941040d51440c0e046500c074940740b1404030180d0300c0c1d01d6011411b40e44040c0c80c4c0c64902e0800c20094001446882190030400c046040c3d00b81d50801c13a419101c40b802c003100d4010314180424a184039426055019500c0c010010040201c0310300350900300c83d8100c03418004200f6507a00349088034403d5440c400040c507038484ca42400e003800c1d0406049200010b00000303a1103114131020015500071a011502034100d503915402030048001c1c5000034540350716102c03102d5403c0d80d40d4103070113100e2100400d00310000703024a910705c40200c1d4008406480c044074007441c0d0741001c2401d01d40c1c0c5c50102a00716580c0b03c0d48000c0088070009480f5600d100d5400070000e0201a18540b50020105201e81580b07402414105040d00843c40c2c0e80c900034001d00003550f40e4020014008040b44101c2100594032844140c00660307100d03203946441c00d03a00036a400080014507034a662000070b009040f80802c0011030300745180c0c44903525801450100 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 860961366 1250 860960116 860960131
    0x203010602010605100e04090809210106080a0c030f21020f0606090709120606170618030703141303201c05191103030412030e220e01091a 61
    0x240580b00c8040000300085030300350900141d10041042420f2600e50007238021140940320403450400644042408004440719a0220300042408019152402d1294030014021500035000111069032000b81c0e1903010304c00600344400c01c1c8403c20900c0030118100c0040c40f91403c83c0c010044a48402039160b1612390413145450043c0700004000c0d04003800b1041c800d002c2c6540c1d56058900b064000500c105080d1020355610f5030b0392401040301303011100c0280580341c40e40c2c01850707035240030b19201c01031410081140d03104c0d070028010440081c1d000009121101c002030700c2c071602c41081491003c1060042e030b0001d051000e6100001119100c0e0701803000c1c2c488010707550ba03480180c2402e14035070200e69040c0000c000b648a07a0120038000408002c13200700700e20569a40d11449040e0001a2464029811400d01100340e18410350803d03820440388030300c540c010742e0200003a0214002c8005081d00c060b00316110715454100d0000c00400a42c0302c00c0c0c60700e40c42500c5252002d04840604c030070341c4e4111060f5 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 860962616 1250 860961366 860961371
    0x5071b0303080f151f020309030a0605060310090b160c05100510050102030c0a02090621010501090e060f06120a080c030301050a06050403080a030c09080312061f090b1615020301060201 81
    0x1140c4001007010700318495406002080510310905d2017451100c40340701608114001404100841c0d581030083e2000d00d800744c03a02142908002003018103000c07000c4002d48115140101c0440002c50400c405903200244030342d9030449803d04803050700c540100d490010407130300a01c42e001d514a00c440e84400c1c0688800d04c1e290402503140c10042e42c0c0c3c1e102c0e01c40070249a5215428200040c030304800511e80c4164050302840e00e210300344082c4d1042c1c003008045055039944031070040c41700e00c0c4075210340010590507030300a183ea41807501851041010240c0004d0280241091520f010701007003090180c5c40f03902444803542c4051440c1100d0700c0741c00078000d12388986001240040e22500c94015102039030b4224810516150010038290000c28491009500b0f0000b00038001607a64410300c0506440c0142c801007440f24980a020424111082444690b08508001c548070319a544071030301c5800d0311184c2107070b03980e00d40c54000a0106c000b410303440204500800010b000d0181c1882e000f65040702d8054000303 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 860963866 1250 860962616 860962621
    0x2070302060412090f18150603020c061006050909060f120c100206251e03020903010b010809070603020c250807050301060303120203060a0315060e060a120305071b0303080f 76
    0x11294107489200c0d02e44200b5038607000b405204c40c4861861100816200000b41d1f01000d1204040500c21640c0403501181e1f000c1002d40b115901440340d95480007110550702070a5080c440003030314900460302018003540c2c0640000f11191102401c0380c2001200034a564050008031001c4c0d0340e42c8241004460290031041f80107040c00e8000981039014000344541e2400d00c42c0f00181c40600806441c00c05420810328550802c9880c01d4604584101d803429503015070b50f89003d000303050940300c189034040d04104115040080c0c500c0086418010b0740c8c45850003503511451501c1103031810220101440d00300f0b102a9400d080303141d600c400401101c8019080e1031849585408241c200ca01611025001c1102e4120780600c3c85003950086500c64401896091481d850740c40c1c40c003828210340c80c1e08110345c2d42e07003034184030340c5040802c10b9600c1441201d00303580c810b040c00e40c108041c0b180d01000405011010a030314041000c450840d043c0910150800154181c0d03d040003001401c05451940684440001 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 860965116 1250 860963866 860963903
    0x4020d0209120d0f0c030e060a09061707020d030c02010204051e01020d0512040308130b0103140708030c0d0c23010902130b0108010b1605010f0903090503070f0b07060609020703020604 81
    0x105022501082e4998201021031138905440d0410036002c2141040480034a00d11305076110006015450300940c0c0e030000d02d40c20060042d00300382030050701c403092445660400146590001d215009020b241c83c000c03030404c1d0440416070180c080d6400c021360290780511548030014518080c4070440c2000da00300c0e440036031200000d403041d1164040510898100000050209005600c543e402c80810311b030088189038a034440c00810700080c0c0048070300411034000001c405004220510190098030301843c6000c1c0764141d00380c0c0d52002080154244400308603010305000300c40c1024004c11561f000b000d903e4241d0010014020000d441d0102d00c502c084041c40d56480c0340a01c1214640710040c0c4030710071107908140c001542500841100280d221000321203000041080c000c03484900c0c0c00000c00309000c03101b442c2c081c1c48502560402070081c0d101480420040a1f07200c017180480b60a0385a09a507000181486005003c184d04100c0039980009000c000301680051100d2141d4000c0c04410ba12484210 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 860966366 1250 860965116 860965123
    0x11031819032f030a05340905070c020613090c0e3d0305040203060106030203071704021c08090a090c02030405120309030717060109140705090f04020d020912 69
    0x74005209001641d03880c50707052a802140050b290714080145a0700500091624054800454860308039864400400316644031130b0303408555200d11803014036000546080c500f1043d100e07403c15a500c0740c002ca00e000703002e030303034030b0011550050b10300c0f03603a020354420070004034041d4800d1301a11460048810340700c41c070865180b070400000070118545a0000da030700052000701080f4100003800010f003862003490309100c2921600711b45031408681c03880c00d4010107041003416802a424540100100aa22640500c1040400328200c1c6903041d10348850020644100151904540c0800c0c650206000d00003250080c0c41c2d11041140d015200b542c8421120080c0c44841c40a800540e00034002407000389807000215003202401e0045900f09264040003a25010b0305030300092034a50501a4041e484d6421b000309400b40640035800d00c0b130041540940854408024494810801c001c692000c2981e0f0303203810702070540001081591225488403224009602040915201c1d1700030394002d000d56032010 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 860967616 1250 860966366 860966369
    0x80703020c061c0b031005010801150b07020a05151303080c0f070311040f24260606060c0307150b0f0108040c0608090304090c0e0418050d0f11031819 66
    0x201d402a0b450341410f0b110300007a00c43c0d8528aa414050401c2441480803036119460091840e070001003400600d1002620719a481340e045800d4500d402c000c6400540c542e0054401107600c2581c0c020b0211210050b440c4d4107000c2c00e04802c0c102581c1d00303000018003d081c00038140d10b04401040d91005400415403961765800f51000074109100f68114031458505503001444603c0c1540c004203424403013089451000d100c0c240d140c5064800700b01c091040090700340c42c0d040c80c0b00113a50510f000500c002201e81e80c1d4070009040501c51940040d50303d41d0040f041c03080c0c48640b68080944200e8608404680e0040e00390411103600072200041001d00c150301c40e09140f07000300d40100aa55900f400c0a00031280d41000400945851000f0040001c54218510a48100074815903c1c2c41c406188441004180c40c1d900b041e400c071324114480c1100100e100898010501c13a19401d003980c060301203610540d000701000c0c142101a00020420071071902c01e80002031b0180004403100700244c3c00140503541400183d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 860968866 1250 860967616 860967637
    0x303110a020d0311030c1f14153007031502040b03011401030221060f040b03031207030f06140a06020303010b03010303050a0302070b040f05060a05091009170304080703020c06 77
    0x141d00944021a01584c120b800c00c20440342a80d16050540d02c44a1030078055415502c03201000d01ca9070506902c0c02c0c4926020032030203900300616420404034403a03001c142500036901c1090380341e410b08441043d0210240305400301d20940b28900e410b0441e180d0300d81d5001c0c40f056034040c0c0a00591051907440d44200c4040c0d0b150050180e00f16400c20952290440b6a942c141c2d052580c00c00144403020440170340f110503031a54011142c6245424000e01c9814064800414040e85c204404010140d6000c01604d0703140d05204e00d49000c41d80c034600110007030400740444100146c608031002c20a603040c1d1040c04408102a100c00d01b03c284d44000c12681d0784403d100e038180c1a0010f20050000134030580081911b21528500542083d0180d180d901090b281501c0c01c840d11a1084d006404020042c0903040d03225030400d00410040c50003512103a02d5005007603401c3d1400b030783c4000c04010010708e140d0100d0041c001b0710340103880b40741c940303011112940440b205130090321034803203040c1c09460080e040340c524405 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 860970116 1250 860968866 860968879
    0x6022a0a0605100306110a09080c18070320211509070203040306020f090102011d0601180f110c0f0c01090b1b0a0804090606080103020913081908010303110a02 70
    0x885072034020040c20003514080200f682c01100002054040c0141c45480700200d01050707a45894140c082d2481805600c4100260070800400b82c07166103041e40724030010195841068140d0307030350b00105d00038459a40c034410f841140c84540c226490448020382941c0c000001820002c0300c800c03562220304a02220000c1c02e4000300d080415041c28078481058020a003801101d08103510384c0d981e1010303130f00100e02c505000d49000c08d48102c150790902940c0342c840c2d400704180b032000490f42c40315500c60405002e170054070780d840d500044441c04503900c5004080205041003000680039903460f0000d600c240300c41101442003a06100320058042015080840d050f1180a49a4036084d0f82d00340d10382080d08040b500c11547c40c03401c81400310030300c0300180240c070480d25107648074208000c420440d042d43c4c10000401c009840140010303181c1c1c01403103400070a9a081026902110307c2c01046510902c01503074040480490b114464507007080041d816640719840c0e4615201d03041c4d20499540204000c040d51224 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 860971223 1107 860970116 860970133
    0x3070b15010c1115090a15030b09161224050102070b0f04120804031a010e011505091e03070303020703050c010e1e040603060906022a 59
    0x3424006100902070301d48091034483d480c0360360f0054602e9003000f10080d0b10f0400b902c518040c024000e0140c2034a6500000c0d41d02d040c403074a9404070b410003060402919003100401c0c8560032110060240740d41583d01240e0038207081427007100c51583d510100c01d44461241c2000f0321000000c1c0e81d40b42d0b0304c0c585000240350041e103a100d4520030304140305840003114071104603002c9a09107203401020000b507051a80c102c0c4078aa000070100084e0208480914403607808127812036841a641145aa980741004498032021510640c0016001c000003089880d120920100300340b080b1194090050034140031900e0045eaa80095004d030f4000c081c2001046010000b95003425000e10f089000c00c26100b0100b81461180603e4164100c4540c11070a0942c0fa140e01400040d600f00780103114540490621030025400100241c440c500c1a8a55100c10f11b450b1043d440c0303100046006004a0 = true := by decide +kernel

theorem cover : BRFrame.Cov 860791366 860971223 := by
  have h0 := BRFrame.cov_init 860791366
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 860791366 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 860791366 ≤ n) (h2 : n < 860971223) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
