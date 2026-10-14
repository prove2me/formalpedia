-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0570
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:30:12.3023+00:00
-- url     : https://prove2.me/submissions/1415e544-4826-4e0d-aa54-d524e0f73a56

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 102338129 ≤ n < 102517985 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 102339379 1250 102338129 102338141
    0x6091f050a030b040201030e06090307120909090f020f060a020c0f011e0906020c01050a02100506040f0204090501050f1f0c030e040207030e0a050a0b07060203060f041e0b040504020108060d06 84
    0x4060040306503551039007000f0404039003c82d000c0c2d0100341070140500c00010300141355441482c07481c01540c00e091140d5521011340544000140c20040610fa0105c1c0c00240c5210340203070746200300590040d450a52061090845003080c2c500d100320814001c800b0102d80104607040c00c002e04a84074046040d00d440180da80e4002d408840c5007000d031980281d070000703410804440a440442d02202d15000f003010045580b4403404a1810040e08080881003045003942c0140345c20000c0200082692450201c9507022604143c0c4a0190507840300300400c200d050524202c114440b003950682d100e540105500c0518500c041204000c0040045128050502c21107900c040014014000c0d95101240d0800034010b0b480001003620134440d080c3c00240620f05040000c2c210740f0034215550074900c00ea16802c009410003024190441c0340c0c00049102556a03214800d13110541c065000c3c0201e080401031402c072121501c107203000720729210034400583e810416445c3d000d4011034150401c6c103035614003038010b051 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 102340629 1250 102339379 102339389
    0x3080301030b15032b1202190306050907140703050d050c03040614010608071101060305070801050f07030204030f02100e03010e06060f040213060c0c08030a02010218060306091f 78
    0x220011080111200b0603a000b400341c203101c441c1d188249003c05032580d981c0c11700c902c044810003500c2d01112400c005007200d442c02c05c0c141101031b0003841440000780e80c4102e009030500d61881d05c002001c1c0d6054417520002e00700c213844070b005525110b80068645000d084503484440390101b444000c2620a504890701c48043c00300a0010f800e10310800581508141c604490345410840d10050a14003000140c2c100d85195039482c83c191141c1805890f107103081d0401c04055501c444000c00495803c0000c00c006107030100c00040c841c075051030700c6901100c0c0139280d201010f00400c0b04001040c892402d600c203141c2c040b03840800c10003400009039020b03c0c0b40c03820640c01d03500703022829490b6000414020f00c1800c0a440f0400c0e00010382007084100e200b0342c00645601c05100c28140251803142c804828094803503480003440503200c402003480c64101e00003441c0181c0d000104010b03030034540414960349107025107495007035080000028010610041031004102038006c066170308101c5103290080104 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 102341879 1250 102340629 102340643
    0x105150f1306030312050c0306010206070503220b090606010f050a050a17131101020c0a090e07050d050606100c050d0e0609100306080d05090109180f020d0504020a060203090f0607060603 82
    0x95036484d01a00e04001d40a61080351840c18001800c204484811244115416805081255503500e42550b203a04040d00c11305036900b6440800300d030420000b2140300558022141c041075850504181c51400030000c2c220b81c108480200c2626042e60000142c03080b100d12810032a445486811048446107640035400c5102e1242e14180000018009801c00c210390140c4003402d0000c1c3e04000690341c2e404800051074201c55124410003195669500401039112103400381c2d412075503104001411980000001c0d101a000030044c05024541034a21070394000e84c0e420202c20580d142d841d96603d407092403800800348009090808c000e80d481004a40a4100003003424102080000d03000f40200254020070590380302d8240901c00c4640034a0541e0031010b01607440110b40c81c20304c400c450860300003408030400f107500e40c54050004c2c5007900181c0859200700f14005154130b4140108010790342c0603401481035400400c00c0001030788035030341c66004013107040d906290ba640c0b0341e00c1c01200824161740090041 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 102343129 1250 102341879 102341891
    0x20307120516030506060a1b02040908130608010519170a020a0b09010201111305060a0216060c030216031e1a04061508030a08040f05030c07260105150f13 68
    0x611802c2c0d0040070009071542d0100580d50700e08051042500c070700c00c264408145180350300b07500350428000c60712440b0310141c00880c0c040c103107642d6180c42d41c211450b00c13044034180c1c0134240304150f44401124010101107030b0104046400c41e40012080c031481c01246000c0300c4d48003590999140401005030855030103058054120744d10301d0319903050b4209001103401542018051425402c803d4191024408952002491149440304000d0182d0002403010158020740407800d014004d001c1c0c613940246000c0e02c4804540d406850001c3c144141100350082c2e00340b05500a0000c2100107065100c990300b804001608085c850508540d00c040d01c00c00c80181e845103404110400c142038201c03440700b28248154910040d11000d14507141d001d014070b880000796242c80001c010898803950084030600602c20780f40703010701180e50711341408100c3d0400304403d86038000400f4038a82014011044064a0300200194189012640141049501190b214100414a0144564584d40001c140028600d020058 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 102344379 1250 102343129 102343141
    0x11030f030a020c0d05030904050415021801030b060a08060114070605100806010f060e10030609020d0b01080603010213030f02040e06010905010f050d0302150c04080f060907050a05090403030203071205 88
    0x2481d03101c00141d000600500c1040e9000341000c00c0012a40e0354400f02550501c240030081c0001403900030b20507180107180494100003018503100074440304c0c240c0b64056005a1100780054150391340d61103e58092001040139402495101a40c01c0c0c20610074a84017580d41c80c5c0d21210140c41c05802c60103031041c0e14000c10b10200c803003000700000846003480251042c507039881c0c08103a1000302c2c61044201103a120307080146135107042011151440e0017130a00140e060348819100e0126081828800b166503559010f8007015a044107205a21602c101c000b549007002000702640751840900c00280f0074011040c4410855445400c980d070314500090864056681d80c1c0104400b81c9001c0c03181c0c01880c892110701059606050002d01c04464040e0010599184d203508800da180d02c008280a2030340b074040c8808200e041d0b0900070b4441c42c041c0b840c01070081c3c1c10005422401e00c0e0345a0300851052007142c0080080d5290300e41000e40c0160103040c0140c9a5481d50000d5031700d240c40b0807013140a2803600c800c00c00 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 102345629 1250 102344379 102344383
    0x6040204080124080a0b0c0c1905010c0314060609090a24140a06050a0806031e011d060f040f0f02030114250207090c0203040810021b0a0b040b0411030f 67
    0x46110381d0b24030110715135245a0941c40324410350300540800700e07074400100c00c10b00300b030010040702100340200d840350151420443c6008864070310807a016519040358403215541406542e00c0c1d4002c0da00c44440a051510014640d4810500e205000300300030340004170950540c0d84001040700c4291204031032030b201410021a041094052a00300d42c0001d0041e00c02810800c42c40c009403480c2d0344401e460910408410741c4e4010006191070362500c6100d407100d190344481080104030140000c00032800768180740050706001450001d100382e50717010f0010403d6801080045a8005800181c2513035440030900708204601c0351034034069015801c110f815240a01c0c0300a12034400c17101d0030f0740080c0c644480c8e083d100b08650598010700c01640a410700348407084140e072104403000b07070500489241c03555480049040c8000b401d03070303485600d6005c2620a02e90440300a0301d2000d0b4040c40151160311055940c59803400e00107800a0319105044000401b00900c50042500084004044450200c89109516 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 102346879 1250 102345629 102345671
    0x16080909090a0f021203090307060509040b120d05160804060f0f030203060907050a120f0e0111030c04090f0b061909060e0d062403030c020123030f060402040801 71
    0x2a00035200304001603850100410a4060280d220202d0300306001c098003045824101140c01c1030307140c042000740c2007855804120540c01000d41e52100e54841e40702e002008122421002c006016480f07540303004442400c00728014a10001d50b082042d150b0aa81c0c400c01500c0c0141d01009056880000e0701082c80390b00b203c8248048180780d83e07003202c1d25982d0003089060f0f000030759220360880388235401300d445180500301410000c61103191117004a4081d00f8802c058031150028100c0c0c0c181d8a03180c000d056542800740752245904060541d00e103041401c8400f034544102e108103000150b0326180814600000d80040489100051129403034141b118980320259402c03080e1080861014040003070114001c03c03a00c48207000c002c12558410010b505c548004d41507810003200c04003146991124004151040c88010f1402541c40e0700d401342d6a48005415030034400c8500012500b0106c003502400203840c110795020380740324506012030f21008045030190049802440d115424486040c2d07046440c0e03444a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 102348129 1250 102346879 102346897
    0xe0d0605060a09022503110304032301061a0a05090a08100b041a060c0106080604080c010e070b160c030c140a050411030c0c1203100617090309040b0301021608 70
    0x420a465a443c0744004034416081d289038040e030700c0c48030361400f000d0b4103400c0c4030383ca4000d051403c4038803007450800f130556009030000c4070300d001c400e02107036242070305e0000050100540d08000c102c00c07410303e040440801ca003000d0b51101d030f6400254000301c440c0709405543c0140d00c09459100301c00e482d1a50551500140c64180c0d0341c252905800c4c214515050003070042c40d48441c00721800010400f030034004550f00903203001005640f01c4000140c000c4082011360300c00da002c0e200d15512240741c00c21140c00c0d9602c4100d03d841d40e91000c903060164410910480c0d0902c115600703040d40c100c0151600407032030070360382d4005001940f400300c00088400e203030601440d500c2000c07258050060340f40d07000c0008451020070b091070b40c118284005503171303030300a00020300684181ca42141d5601c004042c402103140d0046490300c024444402c0100a01a009042d02c005130414080d00e071410b1424030840307903684c001d101c0c00610490304c40309558520380b0300398121004512612001260103640d0b00741041a5480f910013 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 102349379 1250 102348129 102348139
    0xd090e07210c0e2d0409080403051509011505060309161403010e121b100507030b010e010c0f02090a0e07080f06070c0b1303050408030a0206010e07170a05070e0d060506 74
    0x840c0c10030301e0000f003201000c07112114001c054209044c0f210400c030400d454010f40040c3d90f441e1050114011401030f00003544158024001d24404080011001d1000f800085c3d00b070381841410450945480a081c0a444003030300c1d07035910380c2e5503401e05500d004096080804400d81d86030000c54030300030300d15201d044daa1054009001000600c880d5540d920650003440c08130b00414060740e02104105822005505600c03c01c0360b005411500e51031040317410560f220340c0030036035516202d15956003083c402c02c81d00109003040201d010058859001da081107403002445600c010307000414100c40c0c0d90202c0010014042101c01e01516040742c20741c1c03080c080d50090503511508000450091280a0520100340e010925005644480d140c14030740c0b90000e07408400f400401d0201180d00001080a05094405540280110352408083c03228403240030b8140b0341002480340e2841d0007001c071501d841c1e800600358200002c035070359507103011a42c050410b05100e42c400030b411208418841c141c1c03c40c0c5d01889003210 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 102350629 1250 102349379 102349397
    0x7060e010510060c0506060904020f03060708070e060c030a031d07170708011503060902031c08040b15030312040f080301030c180501060f030903090905010b04060e030d090e07210c 79
    0x28240c03000d40000c00018091b600002c00241d2505010400b16001440a400c1c611070440c088006410081c084800a00046a032020000f21036403040d810000d41c042500c40518007103051680a4684c0300310b641c0c2c41e003490f0310b5404840c40484c2e80c4101c020402c11500584403040e813552900b106e40820002a2140c074801e180000c6074a540610810081848481d01450003038a0356940c800035124110341a80d16000d51079034600e140110f41205a0300e085283e0b5044528030341031070325820003800500b110020800302c0c410300e80552000011645a000c03140300850041d6120714041d60340a00e80c0130002c041300340120000080120009000058030b171400b4148a0711104007141d031044581c244220000199a401d210100038000d0303002d410524000e2a00c0f610703a548500b05001a2a000c0e40110b00c011030002c2d041003910b500c078200b00700260044003d0560301541070001044c0c2076507402154240303151507010a0302103000340e04400c400600180500341041c1030030602c0000f89056140d01c4049242d002c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 102351879 1250 102350629 102350639
    0x6060f051f0c020907020109080301060905011106010e190605120109050f0c03060406020a17040c181509020a0908010905030403020a1409070302090307080a050307030f08090a0f0807060e010510 85
    0x9518003078070190903a100e4084400c40e80800000c0302d000f4202e031041d950313603040d150b000c101e00d40c0007503003e01802e032500000c0d0b914003000104003c0c640448502d9a0b00a10018030840d55076a00a50300000d031848660010080848007100801c1150f108992101c400803030155407500642011601700d0142c0180ca0380d40c610810030301d0316003005000207903041c1c10450001d40010b11030360103020014901d2410164414411401d0700b030085003914281c511402402080060b220b4000e01c0410300e8040e00402d02404e41002064107d030000c030b002c0e040403250082283c0b15041d1084541c4001802d101000344a08156070800d540c5031b03030060200740d02443c080c240100d030549109200004054000d00307031007078590310074504070b00035003104800540c10302444000180e1980c08210314020380b4000e001941d5a0302c018070b00680400e24620040c802d02010000304004400d01240d100a001e4000b00032003040c040900d0040000e111f00480180755034640144000035a505520080c8107111005003030044544030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 102353129 1250 102351879 102351919
    0x100f05030706080601210504110901090c0518011404090219030c08040311160305060108010513020a0b09131803020d2c03030706020f180d030507031b06060f05 70
    0x14010301001c03a20000109130380f54442c0d18061001c5c80404250079448075900581ca042d1801543c0503209101c0c0c030442130010f0700d40381300083c2c01044c03c001d08002c50040448003401e01e000e000c426441c1e00400001120460f406000301e00303803245004680384d036a1900c95071207034000d4118194081d4589480b550002c5028000e124030369829000362030310035040d42c0c0c9980848003210300304481c0007913000b0f01c50031001c41e01c00101c400025500c00c40103400305605041e040360843d90000c150400c110300b40e058500250b01c6030110b80342070390000e80d910380d95125100b000c565000d000c1e941c84c207251403900c4008250306004100c0c40440f60b00c00e81c20340f05806401f1004540c8071030103400c418240004001c5505601000210301c250101018094a00341020b9442c0c4c002280c0043d005441c62502c00203100c2c0e41440030300c100b0315504030100d482d5590b111039030324000d0140c014008018148503a400501d1061510406000011350b03000100b42312040c1c40d800807040380c045a1103520b00500020b0b000b0717440e024007 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 102354379 1250 102353129 102353143
    0xc18060602120d0e070b0316020105060301050f0105190b0f0901020606040b0604050f0d0203010911010f081b0a0302070f060e0c010327080c06070c020909061006200105100f0503 78
    0x4040b285a00f491511510240240b0700c3d1180c081c55803180d01000903580d544400a9803207052003090b8889a41d4040c0340282c29034100a001343d02c6649000c042110210204201505642c010b41b00009a05c860041101c002d0310030380c2084a10500c0480c1c941400c4a025000742802e000c2a805d0b00c02d02d441c0d0400307100c1a114401d00ca183e10440601c030620aa080403004d484103410f00502c41c080c120700b541c0110703084030b035400d005403440c002d07420180207903581010003000e5510840c176040555140071041039544213050820441c164078001440c89581d4801e4058960613034104049200d07014003494050300410880c0030300d001038001e66a004800b0340c02403060740e44a42045014a114807017001c240060b2039400041220b1444040c4a41501e44404002d068414803140d1541e8440c11a1801040496034004241072038a9024004100d504a5001600c4041790190b08004200840d00f01c0c4181a110000f80601c1240d0700e84020010340c1e900c1c0780b06140841b01c070b901d107070a459074440007030540b6641 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 102355629 1250 102354379 102354403
    0xa05011407110d14130302060d02190507050a020d030c0206030a15060e0102150603012a1403060310150b070308150102280c0b0406050307120605030a1704030c18060602 74
    0x2000440d0030f130400c445800400029905140301141c50f601c0e507002a000c0d400021071103d000d0390100d41c020385d0000608194038242c41030f06046040c8103107962210f940d83d030702c000c1c020701580c0d640c20403104150080790b00e65442980280010303200c4c9000903042000303244a20b03030a1a0020841000280f55008604080100c04107a000d42070200303030000d01c4490305a014203040c0c4c141d90703101405e43c1000040500d5041000800c096240c08001c4028001e10403088115000340f6030004000748803055500207401c0c20900100e641c08101400500009000488184c1c02000088800600381d820141c0c0410202e1140c6441981400e1558484004a0381d610301d0080c414108842408241080e240d18441040340e58445d04040380344070f4441244150680081d440400490400b00600c419a81c014091039035003080a0341c200b120751301d8900041d649241d00b440107040114007174961034565078500c080b64080c640080d03800486a17901c0d004110200035210242d0348152501d0004202d4610200326421004 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 102356879 1250 102355629 102355637
    0x2060711030a080c120108070f0602060708040f031707030204030c0e01030b18010f0f09050c12030306012703050c010f0302040305060601210c0503190e030406030c020a05011407110d 80
    0x4400b654250756803d400f6241160b00001801801607003400008518007a1141c0c10113024143e1521044003603291840d000345080d500940e041204403079100180035032094028404041c1880e96040594102004845400d0341c141c03103604011344c1a80580042c011640b14108040100e541e0361a82804101c0a0000505a92002003c2442c035030421003000c01021040000054030605010000110b03400011803201468584072900c040c800140084031600609982b0120254001f0030900c0d02c030311004240e5414004942d40390500104200181150347c2c4c200c1580210450f241d0428640d1a06c05840c6140041e60b003004484000f40f190003910100c82d80080105400c0d1295001941c4101000d940240d0700c82107191050150011401800b075480c1d100d032105a5a8100b01c2c2c0c0031036801801003000588941801d8002140040c004211401c907078071445c001480c0091944200d0800c0e00d040006031056081c5115001e1444108034118000d1075203844101c5442c00c1c240103584c84c0c0540b045548049 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 102358129 1250 102356879 102356887
    0x908120309100e070f080a140105041110030902060c011416050d09030c08030406140702070503060f0709080a050c0f09130f020a17010618020702030a030c06060e070f0206071103 78
    0x24145820010039403241901343e42c0410b0700c0b45180ba105418075480918650b20441a000500110a075100024800d03e4000c1c0103524103500c2d10b4041486c0521258000c1c4800c2c580c0c8142d0300c2c400c0d8080740d00c0c194010591540e038155445914042c011070000a0700305c40c1e00c00045041840d41004e0840a4132064940360300307041854400200801d140101175041c005070002c8000041d88020046106034458000018004404160030a82880c01010740f015944860340500c4680c3e0001885039110715039079000c00c03184e5204d02c800c50380c0388896403001d46030b8461a00c0d050200040400c0d10300792550300f640d0030461741c1c018400b00881101e0a890700040c2010311091040820355021000c5551070025260201c103c0d039a000c070520785000c0301d601c20042c0c0d64401c424004111417642070025411003003015810034440340c0000351901303281c4000a0600c02c1d006409820070102d6004080140342210301e80e58a841c00c10009407590511542134001402021b0000f1003c90181d6a03007540900c1c200015810 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 102359379 1250 102358129 102358153
    0x180b0f300a1e051f0503070b0d0b040f09030809010b04050f040303090516080c09010816050d030207030203010c050a03180510020901030209040504032d120c0c0c060908120309 77
    0x244250b0402110203400c52103082c810034075a025444c041c021041030509401001400048641110341002e842a001000100868440e00301030301c40c409605080010f42480c2000020014080c468680481c182800840b02c00d0507040860a803044800c07030002d010b240c4040c0e0400c021600101ca00790314250780c2d4030100300442d00c2a400814401c0c8220100d42e00c800e8810031080035070f52250700031020369102940c019158201800302030300404100e03008026803031444070492104003203809928000d0340c101841d00b083c184200032401c001c6030040e00030040c40204110050880c0c2c0032114210210303051501c2500a50081c03c805841181c01c80082c05040c0003200407a4041c0d07000204581c1059000d0001050981c0c1c0d911a060145129466980c0c0d041d9001c4200007110501c42a0050409244181c03003400ca500504140c0f9540710540c80083c218068072030554440c2d401d49006850801d81040101b1520340203c80c45054407038050440e030703c483d4040030f9405603200442c1c01405179040349a41142d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 102360629 1250 102359379 102359381
    0xf05190503070e0a0306020d0f1a12030f040612050105010c170306060706020c010207030305092404060204030501020a030e1606090512030c0d020a110a15180b0f300a 73
    0x60042ea4614241d007052200703800003203031501c59800a45d2540c1c1e002031000c6a407255441001c680e801c00140c01d02480303001801002c1c0050b60401201d000f02d281c1c10100325964014000c8440440c10b4091454640b91264802030905071814501a2224070340700000c180ca600441c03460800c1d5900c103561100100c01c131b605410070307500081d02481c0c11200501205000800a002410f10038114000058590500303040041c2614409000c4904642088458100e00c10302001100c511058801d541c0340d0300e44451804100906c2aa071024180d548041070503080700c0da1640002c60000c444204440d00030b8407656013041c0c626024030409001c00e11207181008141850140010541811f070b06590804c4c031000714050500c3d2814800740c00503040004010100440d402201d000381c10709440d4070400c24200710a103280b1009440c01c40b003c0c040311900010342010600000b40107000d0b109241502c46000d450011410303000200301004000450030340340041e01d2104009442d80c180c008001425444000d9810 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 102361879 1250 102360629 102360631
    0x10b030714060d111e0d05010605040308030f0601020c0402070b04030906050a1b05030c07121a06090f06030c1011071a03070c050106030204020310050306340c0b0a0c0f05190503 78
    0x34003290784c01d00011128458000210301405940740f2885d503501c180d180302c03a003150416009203003807000c01c1c0014000328040700e05681e4811038640185a09445144c010303403420b400350711011f602c5800094103204211581ea2002c0c000c031b201b40c5590f07190a0300c9003070030b448502410310f0910004110b00c0650103214403102a400707000b0b01a00c1a80c0c64000070b0340b100e0341003001e00d4000c144005d8520742000d0402c56852011014408845540c1c0c07907509011b00045c1da8002c02420003840e9100300008511745503000d00810308441e800404c0307015400e400e04030180216004504940c1c45000d0b50305c0c009803590303a410321101500500421f20303107540c1d40c000d400d803604482510207444030341d81c80070302100588540c4002c601980c3c642c150315840929000070540b40000042040c604602c0e020403000d1241e140c1a4540c40c00102488092480c0d401240704035904280b0040c0a02081424001d00651042551000e100707200c440e520181c040601d00e006880c20311412002e0042800070250303082c501c1d841031001d5 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 102363129 1250 102361879 102361901
    0x6060307031a060c060105190302060702041d01060f1401020604170304080f040602030d2307080a02090402040b09010305090d05042303010914070f0612020f0c030705010b030714060d 80
    0x403400950070b5804500d00e50401e2400c444079a0015005102629143c069803d145920084a4921a0640e80460014080c00b00004d00440d04d403410440481c0c00c0c1d141e1150b0350b6815a008101c1030f03681d640787c0c0701c0c25031081c0700d4110f130076040304c10321682c952022510512650300701c100c03801d10700348004103074180f580010300585841a0600104144c085504000c0c0010000c40d4000c5489584050605d8110340803003800d44c1c10b10b0480c00001015000e00c50406078000802d0409520701d9135902140da02074810f088440d9807103480001c010401e111088094104c2110a0b68104695a242c044180d40c800c00e040d03840c000300b40203000070840303d0341110000d080d004010031900c41088a140109003900d80c002c904a6079a00b0102c4e80c05100702c002c00041008000e11404406190701e4141c0c0a4070400e80d022040c0c0d002a00080e80f181c3c2c4110020858202480c0041101d6680400c7d041050092040c201424824010302038005010103650081107491080145a6482d00000c402c080c17000b80000c10766 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 102364379 1250 102363129 102363161
    0xb06010c05030a02070302010807110d03270309030b01050603092a0a0e04020312031506160503070b01030b0c04050f01050921070e0108070f030b09072403140606030703 74
    0x903500003038051000d803108856940003810214110300c009031821000820313200c01c2200c102c0100030070800c0024600c080a265040005500000040380740e5528240c40910125502c0000c0d1b21040560003444002128010150240580d0b219010420300f8401604c02d03003559030200c00308010041440481115004498824020360086003003c01c182c58040c0d441042c12085080802c03084d13007820f02010760250002c06c800c4c0d2461401001c2c0014864400d02c049004401c04140c040003510210f003500c441a8100044a8a45a0603d840d841592090104030b602d401044003203803c0030003581c01d0701c060301d000a0294049481003c01124a03400c270154155014144210000810111091181d600d2000c40050000300e401c100c03c19040d40c0040e40a68080e601100040044e901e0820701901030ba41d01c58070b408180d80383c08161a150200c20b410002e80d2140030001c8030110004100ccc0c01821403c1c6490920510680c02500d2800c820308030b500b00d0b0441c208000055140b442540410307042e2a001c40 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 102365629 1250 102364379 102364397
    0xf0403020d060204033c081b0303040302100c08062803060506010917060403050c071707091a0109030b07120e07030c050a031502030a09120320160b0601 67
    0x2107404210200642d20583d0000b824000e001c070141c000180c841d15040b4400508a00303c0e541c4414204486a4204032a42600304108200014045031490010403248544005001c021aa00d075441030310300310058414062a22010b00c5940140c5a044a0a44070640c842c0d841c0c1003417000851890300315049c0e050603042007804401c0c484040d1b8028601a040c001a1803034500000740203202ca50300003129610300030712411002c940000d4090343c8103034117190503501e456103d641c840c581101d13508150032500041c10a401c100c1800074041d000c40d19401814000030740400007003030080c954513040500041e2140d4062000c21041c10f590342d08110760707290407100c0d066400c40610459120580da080d2540103003500b04203200c080086070018110881d80391114500c0d5a441101e41c1e03061450031801c0d83c0d00400004c0045800380c5c0514541900407204200d01596100010f0080020352403804140c510010041c804103540402c3d120180050078190700d04403090b849170710110000610980c10080c01d00 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 102366879 1250 102365629 102365633
    0x309080105040b1b0403080301050409080712051c06050d0210120906050603070621090c170a0516052d06040b030a0f02030c0a0c030e090c0909011703040b0f0403 71
    0x12040c0380c4520302808440f00700b400c000d04c0f00c24012180244c0f1100301e003418071050000c100d4400c1164110340085a00103404425442c000000d806031000142c480c03250b0700143e80e9000c2d0040e0042040030f031205648402c4a00043c2c480c01201d0030f07409100d40128a001c86000103042058864003043d8690400c20002c50f0242200803d580c191b50303013183c1340c940b11014441d0b141400c00c1200c5c060003050608036661824200307940107031810f0428402a254469104000340700c0d4011030000078220005041c0d6089961003180c07503a414006000701e415100380b82c0c065407014620300b4070109075030000b840c040041041c104d44c610101699030754980021080071006840355030780d000074802881000a910740301c1c6004c10713080003211041e4004460781801001003000c100c0903041244c4800791103041c4602891800d0400b12081c800c0c82d04603030b81060380318043c003107134040300d0015060700f580449030703690941e89407000c403c2030135000d2444960a6005010500c52144030001070810a01c2c0c200c0c5160800c0e03030369 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 102368129 1250 102366879 102366881
    0x2040f0204060c0201020f01050c0708030a020c07170d030905030d020a051606060501020d08040807020405041505090f0d0512070e1f0f1d0a03060c030902030f060906101d0403090801 80
    0x20b030710400124500842c02411540c06010103c000c211600003080b451078140c540d0500c0c0e10a81c0e200030305e03030360002000601641c01c3e941611041c42d01c580817581e4003500ca00108020005050b00c002892003600360010760300d0301c81d01070441e0300c95010000d9808d20f18090b58a02c043c0d04504a441700f84030051200300d01600d85000707a010003502030030000c50254600b0001a0410421800710030030014190b0070000459046001c580c074655040c0ca0002c0c0070340d103038180505950302807040e8448550030042808201c03680091201a410b0f070503000d0f00c51242000c0003e940900c075109002c0c5a41c80101c00042c0a00e001d41540f9101c800050008285006098419201140c01c0c282c3c01011034490030b0390680055006e820b418009149103c0c400b040c101810010703070010702c2032100a2145444006010086100307401080c040c80c2d026084074409168a40000c1d100c80088071445180c2c49071b040000d00d9508084d02840031555040c1e04c0344c503500da606403621210280208117405200f40188005010030007 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 102369379 1250 102368129 102368137
    0x7200d05010e0c10080f0402061e070b060a0602070608061c02220c0302030103051506210318090f01150507021002010e0f0304080c0d02211b0307120f02040f02 70
    0x10388405014152010b0040081c220000241c034130400c4994410000545c0c42031020a80003501102c00310b44803042c440e00e401c1c004840381c1302c1c1d0a80c1580840e025042000350344581e405a907040740d0302c4a0454032000100d80e545c42912030403000510303c00204510f400c000c1710b469008950395028107035044c800d0300400c0078188401461030f0042032000410030250300c18460f6623420320461905520355451a100c440d0f0321007010f4a50794940d050f080c0825600e66031458181e01110464018803151019030040c0d58480e003140b41080816030100080d04c01d117141003032425110b21010940d4891907401c240c110300c81310190001300300900004101d0100581d07034603030392611050100e138004200085080a0641004001201d4440541c07050006124104001c03c0d80461240280c40e01d40720003400c0c3c0005032275a00b1004480340501c1711188064003100020500c0f61143c515918064011841c0d4414140c2d01c41c41485007200300b01b00144134000044d214452391015a00003000410344000a810350700c103d0780 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 102370629 1250 102369379 102369401
    0x3020402070b0f060405070e01111f0905150c03040f050a02041104060e100503150118030f05060708060a05060d0b040f151d01120213060807050a080307200d0501 71
    0x40100302180f210b51051690081058400380101d061071400900411041140d00341409200d214840d58404100424220210f481440300200da4036016040010902440c094031640560f10003440a001490b403c64050051422594910741e00c07a120600b0713a41584000304d4880c01000903010241e80c0302c3c000d5280035a40c1d100e50b25510340c9841d401070300b805800c402c4140184001105d40548580010513607034410301c4410643c0c4000b4040004031881c00110b1403901e05a0f214090200c18032008030320061102e407040044840310b8440c580706841c1d0080803105540d001d0000e4006012034180903000e03003861500c4030b40c040380001c003900006095030f0074044252000d90780c84d41c40d420048420004500140429404204d140440300704601c91100140200c0d402c0900602201085444d0200f4448400c1a890b1040041c0758039100e4150303d9a2946c861301d0701c101c00c50340d404500c0c8940402201c509650040308078144580080802c3d038020440407820b580700454921080c0400c07420b01071102500 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 102371879 1250 102370629 102370643
    0x12060703020301140121020d060b0301080d141606090809130e010b0609130b0604080a1103010b0609030a020103151a0304050607080f010b0d09170903010614010c080c01060302040207 80
    0x240c140715240400000441c1040d04002d0b5001e040c040c40013010f044060211b011880141c0d5485015070070b02c01600d5254040c0c403410741d00000010b81c1840200b01e00c80f01000e1a0f0701c0c00b802100300e0700b08a015000394061482c0005a007041203002903540d0b4001040f0070700c030300c481504200c00311b00003070944062003840d09140d5460344103620451400f8402c1d000e07050300447c0c2e05400e01c49241c0c04501c811080f84024624140c1d5214607018564803c001e58001b00845011600514010325058154500c2028132502035800c2c41041c801c24503081707058414440d00030b002014064403a0300114040e12203420b00d5540e58100b0704002c50707160b226940541c1c0740368003407175003d5690030300c0e191180c070303100c4000d20f41410005060140b02030001680d07085070442d04500d042e5500c03a500c45007000002d00c1c0f180f60090000605400701d050070904940a0450030300e0480c0200252651019042181200d4501d031500080d16140702c2c40000340c16601400c4401020000041d0181c1ca0341d0106d4102c1e40084815100c075 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 102373129 1250 102371879 102371881
    0xe0703021c0f021c062d0905160305131a1f09020403020f040501050a0e041106190e120c040207050f0709020301050a0f08030a030e162c010f0311120607030203 70
    0x404d08015002608142a000400249151100c40415100e88190442800c602c407480d0f0070312005040c2001000e0300419a08101500300320010a42d2010119408800b00381008005020b0036409054819040c3c0c01401200b40d151250030380c0429001c0050090458400e6400e20300d0161018120641c040e0141c2040184d495086004000c0b24414085c0d420388114200401030241e40c0301d42107440b0440304400304401082d1500d11b80040a8014108041e030003071b1001c104941d0807400c041480c0405441500c500b08040c1550044c007040c0c026520044041d81d1000002e002c0c00d08180e401802b02e14003600513158000c00302000e03203003054419444202241e40100040c00780e0310f4200c800400410070007141d030840e03624240340e95840b8042d01506100345991040c0900104000f4807003e40c01d207582c000c182c0110340d121018507000c1d852052481450751803060a202e4040802c001282c1a500c21441c2180f91514680d03ca01011000702c0b001900489148030619007071000b0003145016004580303026840b = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 102374379 1250 102373129 102373147
    0x40603150b09030a122f0c03010209060403060c051b07050108160206180c0a030803010e060316050402030c04031209080d171801060e090106030302100b0f0906030316080d0b04060e0703021c0f02 85
    0x280004847d10640309910400170400306a0b203a0b400c90b81100e90060f404141850b5425050301c0398083e44044801028002c1c28020340480080303807000c26690b00b40c031010255150741800c00000901400d101001d64442c002140e071072040740d80000c14055800040302c0100b00d803000071071417104c6c050f0700445400714044010303c03501a8110b0344a51011041e0028402c8126000c101d154460603032241c28003035a400404034441c1010074046030041d680200440c0302c0400c2e11032000300404440e1203088100d010700c5031905105403241c0d400c256010300c0a4000740040e11940c05200c12580f081032121507541d40d80100041e03a400390810240b040704120000903080c0d00e103042c080d09040d0800345000140385402c5418045958180e54401c04071703001d5405035a56580d10011a02d1882107940d1070f04050700c0003070a4400c1100d42c000030300701c4a0299805004100545081c4400e0750a503024010142814200040c1034503c00c0d400b500f0311039030000c0c4550a0303802c03c80703100080700c00311003415896540015020710 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 102375629 1250 102374379 102374383
    0x20601090507050307050a030b0301090f0b0a05060909070918050106080d0207050102060708011401020a080c3f070614010e04020103150503030906070501020f040603150b09030a122f 80
    0x16210030701d810804d24524019400030000c1c450620b2290525550b007030059141c0c3c03000d41c04100046d50080c00380c09039441605040340640c0f400c0303030923144450030700340001c1c0a420038404190056800d80001c11165051927040000b9101000030304400c0c440034510f0002240c024000d1074003d200401c0541000303400d00703000a003041c0d00354002605540c040000d1006055001140904659105060303013000c820080040f4207109074114003400c0d003240854440010600826040700c4081c06251401c040040325048200a03080c41200240f00400300840301e01303280c000c90040c00301d00c0c42032400241042007030403603010921003a00404e180c1e5203c4010402107580500c180341484100c080010422868000081da807446900c5805015200204a00041090940548160754608002c19840760744405e001802401f8144003a40302d00e40e5100300150812103c1e00302c41000001401401c04025203450710081911401c44410412142542e45564003070705e0301140c2501854400c03209441d50240070024 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 102376879 1250 102375629 102375631
    0x30d021605150f011214070e19060503030406050a0c0816020f011706150c01050a020901091203021005130b040b15331c0204090501091e0b040605100206010905 70
    0x310b6030400b6009000c462415a0001c50442c2c100c201d83c5a904101860294020344040303402d0240c0c0c0c800e003200414502001d00b0001d00c5200d0a00d0301c0c00341c02480d10122410303104140b00f110b401d904200320a001c814031940041c11205001d040243d1a0380c103d030f44084166201e414a15800ca41c10801c00045140c01c03920701c009480c091901446503c9039164408107000042c0c01c0320321490b0701d19844890500c5002c1a290340c0003114008000510f045010027001c2e5200442050006440705004101c2c04c02c03084864012940550044c45004120450403000300400703000001801c000016003000501c44c201890710a500c14415400d81d07040c03501d181642800c0b1581268490840100013003000802030b460017030464a04000d03040b036201e00051400345841021080700001c1e10035002203803222055002002205c00c0100c003001f036030ba600d051710720488084a0700303003e215030f079403440c5220b10a03550400100a44024000540306545800103400c1c1e100012019003d80c100700010056081c00e44501 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 102378129 1250 102376879 102376903
    0x70b1306141c0e100c0e0f10080f0408071e0c0806010b0a03180c0f061e050a030b0a09050a0906051e06100306030506070504140d03020d0c05030d021605 67
    0x5070704009a2007040c0c40e044008110b5488015540d0003145034840040124045005901070708000c402c8040d2001031079801c02d40101409416007100d0449075041200c5c0020b600410fa03038a8021035200c2004000c68440c000c0c00649041781c0c24000c2a001c1051110703041c4c00c442014198003d105070703900e04060240225400051903801c0800100404a04c410490b5040a2140340015800400102c00c41c01c035409928094804141010017282003017481000f5020781d0a19228a0142d00e80041d419000080c03d584140014205002c900c0d81a030083d000005400d4000700b060700d40c1c030342710390000b011240c00b00c2e07a0f00c030556110104002401071510505400103122861695100c20f40d048100c96a10090816805211134041c101c2da4244243c0c0194003950b0b01c0810703511141801c0030000d010350414002c0c184501951040301505150041c4c3d000e0445500d0b4018041c11030510109171000d05007a24103980d2800204150104004c5501c02450380b0304012800b2403c081c1607061551620b1060248 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 102379379 1250 102378129 102378167
    0x1b0b0c190207051f051e0a021203010602070323060901020a12020405090705070503040306020a050703080601030b090a050907050d060e0c09070e0405040f05010c092412020a02070b1306 81
    0x240501d496040064030f20042890451304140c00003441102c980c4100710703100390716000c2c2c0d0484861400000008042c00c0f0a25401c4807601d044480220030350307100a11881700540d009440800004200004540f0034a0f80c4c440303410907500191501c3e90078604100c0d540c0c066a58000394011007240c020032500c1c0f03030b000781c13130400c504044c1000003058039001c000c0c1100050210105a00301040401c20441c1c0185038856015502e60300d1002d002f0b00030341c1000c8012004505600002081d551080c840da0003281c40080c1401070030303150f04840b80000c11024005c501c1600484402043d642c482054445070a44140b0380041d410b4040c9100d1070404aa00d00c0051040310184180a85158800311000701003104a400040b65121440c0421480d90303401c6001f002c0c0c0d400c10040b00070480c0c0154011080301d0680c00f080c07115048403011880007641080e8004003143c5d2011044980c0c0c42c50381d024145007d5540121541c0030b403120050099500210b410307400110480d1024003900350300104d80d036601c07490049 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 102380629 1250 102379379 102379393
    0x2070510090e010b1614030711060702031506061b0c040e010c0c0305090d0606030602030604060b04060c080d090203030309031e0702101d0604080a0b15060a1b0b0c1902 74
    0x10000070400b038180301e001c50380e100c00700d00789a52100d0300c0b011001040c0d01541608446070341e001540e44a401c03070081500d130100c02a125500500f000422500f0031503009001e0541d1850f04102c1c0711100101038500c0381c2044080c409803050800245504841140321001032402040700000c00040c1e81002001c00c801c0e90501c40b888007080d40004c803081c00c90b039060070300644a03901180414003190343c4840281071a41040c0c00081404902d50066014810a4030207009254031004c0c0d004941c03086104050000300c0305160340c004200400b008c0d141e04a5201008282d00c41c0540000e45150015a1010b2042d000021034503200e6140c00000202180f40c880341c1d0381840300903000110401e2206114070148080d400084020a00c06003040c801c20340c0c024440c0380c80d0ba45408a940da1080c900c0800c94150003d100400c034052600c54903070307070000c4004148510b0029410400c903000380e81c20704c402017a1580301c82c5100006007141000d92180c000d2a11003511000c0310703180081801100440c84c0259007000b8 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 102381879 1250 102380629 102380639
    0x70201020703020d0303020c010f060503011503030801090b24030601091a041511010603061d06190207030915020615060703020604060e07030206131e1404050712020a0207051009 78
    0x1041e1201241d8044811080720001e40c201135000e8418050050143d5181c941c40b00c51560090b030252007900c0064000b0840240302842c00c00002030503020240c0401d4150b001000750060740d40141044003c0500540181f9201415040c1300411514400f6814613021040140f9540c0c4500d9001c02003203500340c840640c614048800029126601804000000018000c42d050727002e03000c100e2102e01c4610081208956a0504000400081d42e5584640440112541c24048001400340c050001c50301da02010400101030b4a009601400c0220140900c131003001562440380a880201030020347c01803c01c915124034100d0004919840480c8224004d221640200340e0005059600650003c1c000511307041801e035140c5400c2c1c040c0d00007540103100065598031180f100c2d080100302c0382406002004d06401078000101d0003003500503000b66921000c9035801c140381c42e42000c2e0300103009080070811512024404c03000ea900c4440c0c3c450150384035040c01c10184c148081c201c44468940d04d040e0120904003 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 102383129 1250 102381879 102381883
    0x614011203080402010c0506090705090114030613020d08130e01120503030a0b01031b051801030501080a0803070921140616030b0619171e01150905040f020705060c07020102 76
    0x800e03000d001c10941e0b00014046901031408001ca240c1c2180850b1a2842e10750070190f5240294000c2c140503000010002404041e04a14040c001c00002c1c041c103c0f594560b012a2110f0030448000c1c0da00030b0f140e40032040480d50440041042002c5810b910345040d0801c1030000c0c3c0060181e00c8085000301450325040800d0020050765041018448041009200d4a0040b4043c00b0b64040303210314814046441c100143e005030081009000b0000000c9034184c0c10f0005404481091007050340341d0301300c400000d000820081c000c582c441c06034100318100c0c1e512564012468480d202c6072540250213115001c0612211000301c01c0000d03402001440c02d8a01410f00c1c1e2109030708040d00100303260b1a50b41e28000b41d962101502d824415a01d030000c00201c50b45c0e00103102c419807504110703000ca400d00c082440f81801450110b41c0d0405040510b80d140d1800c3e0403040c031040301500040030007405107004245550f40b4001c2c001d0382e00040e400544ca82400d030500301c0c10600d0280c20700600c0202000340d60010317600 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 102384379 1250 102383129 102383159
    0x50909010302061303050105010909140105010b070b0901060902040605071e110d050c09070302031006050901090303110a120e01031404110607020105160c030c05090403080a1104050607050a061401 86
    0x8140c070303500e8131001822500c100129498200801c5542050004100c030840303a40000c44050007201c0c1d1810300c981d980c43d414225030080c02602452002084614049450112066004506000000f41041d51060400100d0f00315801c40b40004800290b0282408820101c224030180900d194440d0b041603940d40c0d0b650059019105400340d501d5058a906002c02481910f0703081c000584024210301d080b5400400a41c42142e600c0d08401e00c010000c507026114105840f8a5031060b100d5400090540e06c0640b690b0070f045200145500c1010b401030300051202c90710304110401911000d040f0141c10340003405841e41c110903020481c000d802000301081a2150701d02440740140c030001e95070400b07800120707640d104180300c11040604170b0b01c4150400454200e00e40c100c034000d10244002c2034458040107213040301079402400090248011844a1b8055804a443c2c440c1c641d50b06460159200b010a2a64100381d0090700c2c1604480094001d01260740140715040e104031031034520315170400c81010101a0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 102385629 1250 102384379 102384383
    0x7051303052415010903110102070b030a0509120403120c061e0c020714150c03120103050a1509020f0f03030c0706051902010606020a0f03050909040803060411041208030a020403080a0f030c0509090103 88
    0x420b004940c901f41c1d00078032010340603000b040c3d491a568034215484c5400707000203440142e890300c50617186500504004040c0c0702a42d9012000340507003810304000315802d00c20100d080e55076035a60b108407800c0c058806503505200c80390610200300e070202020007901707105d11f6034010420081000b518088590705d018812840415208207107440c1c00104108174a540118180f50032000820700021050103c0094080c07800d61248410384440c0301c1090354081030742c80310800290400110f03d000911858005165a006140901140e0801d00c030100c0b001d207400c081d544107002060002411030f000902413a0408038aa00a0000707100703691610400035914099504081c1800709504181410035101d8070450315911401041c0042c2803c06041c010b200d9401610410720941c030785a410011240405c00760f4003200e8036888101c41d00d0300c041d1521001a8001400f01e1502c40d42008040000f030b1821002d0701d01400907986d070a41c0c44c40790100140c1110440008201840814003d480346507480034501410340e6 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 102386879 1250 102385629 102385643
    0x160c051e03040807050f150304060e011b0809030c070b0a0c05010c0807080a0e0601090c0e03010504060606080f010311010309061e1a1807051303052415010903 70
    0x154508085040014099004500d05055844035881000010152090301d098400b601c025982d5001005100142850300c280c000500300c1c124809200b040c005994443e0081602042420402002d2800c540c00c03c0c0c280b2000c00b10b0b414000d00d2050f4403009041d40854440d004603d4000e01100340c2c1d1b40c42240e40700b0034409002c00602529414465081c03030440320f61180080c407500c4e001c074801405d4030600f100e42500261200c000203d015065014075581c2481607005448581d007464450b401030060761009030300317014a54007183c66940707091041901c90303030185400262035802c2c07000040c081000504100c00f410305000043c00460300d00020201fa074802400c0002303416005d1300d003401c0030b0a291480752408411a01c46c824800c40d054105a1011041184c0c5040d450041070030861849000035031200c0404500002500c21070003500282002007a0348014005203a0340c0d81c2c2c080c03030302d00c0c80790140c0b0b008189403406951b02e1040013030158002c01801030328215800701c0000200700314194440034000b8 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 102388129 1250 102386879 102386897
    0x615031e05060a0e0109050124090e0a15031a0601020f0714120a0501050a0b040207030e0402030621010c020d0c02010806010c021f110c1002150406110d0903030605040516 75
    0x640e036040c04490007020703a0113540780c1030f6a40c3d0ba003000003004244100b1250b00c00d41048802a00c10740700ea0070b41c403400d4a0310b0700740020b800e100408464200080050103001d40d0b030517111070709000c4581480000c0d48103a00c1441c00320620300c2c0002d440103010300090305550004140341401c079004510041514005680440d00700b5842000514040e10074030402054040c002804091110640200d407240c2d114900c280000111042404103e101c0c0d0540a4000780350440700c0c41081c68250015500031100070507040748800f4003810280004080d14094200b81e40d5051070a0000740c040c041030701c151a440c02c0059000e1820380000e07101d4030008050714100511900610110340d14047d5030b1420004030300c10661852044640980264090440c0100340e10402e030a5261610f04514044a140b4159020340940341610103201d540c80001343c0215076240d260940406d80d000c00070064082040e4911000c6903c44aa00f406070803a05030b900719600650a100c10801d036014000080b10b904a4186020350305 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 102389379 1250 102388129 102388141
    0x503011208190c03140306011403090a06150305070b0403080706020714070623040f05010807030207050a0b06010e0406140d1110050306030d0503090705010c050309030607030615031e05 81
    0x401d20035450103003440c2c0c11411030255a10707400801565507512035107a1030fa90500580c000740f01d9000840f4410700003100d90661800030300410000d16040101c0c603044499540302c03996003c00340c88041344400c0d400c0d5003d038400c206000302000200000c0012025461405043d034030b0381549481007480c0504080d8000800e9000c100e04581000c647c0c400c402d060b110901d0300c80d40c00070603003000154000c2e801030300c03a161403425040c2030044604462450080745a9940303018015a20504004c02c00d42c01c1c10b0b070034003000001c00c1050064482e501e22490100c500d510306000050b00302c50010000d41e005500d0032400344403100441071140740212003120343d9207a03900e00b0700d8440c2e0000d83c5018410f412600150760b40b80000e40001c0514050a011000c1d00e498100e002c030201c4960100f01c0c0c8641d00ca82c802d11040000b1b50194540200540c09001620b01d0401c3c2039010915004050755204002a078030ba400700300100308190800c0001d50140703424010400707000b0301360f600b460b207640f200410180d54101140c1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 102390629 1250 102389379 102389393
    0x506011710020403052116050c0f0102060f010905100305010603080a111c0513030204020720180106051b03030f040606050103020a02100b0a18020703030513081b0c0607050309041b05030112 83
    0x1002d0126847d0400026441c1741c4240c032024a030321800d0296240d144003400943c0045807140c8a0360200350112216032030000c0801c090300340941440300e18201c600c40480030030400c0c005da1002c1c60044103500e55944d04034000038403542d10341606804941102c42c994018000f803500c0b8404141092405a40703400c006c5050040c014916880203520910005c0e1a508010800596072004c00e8a1282d00c1c9202400500384140c4c1c9000c031200020402007000180201e41c000c20103440c0103c2400210440020075400441c5141c4c01581c1040081000c0d604102c00c00c22140944d2010700020302c0c042d4100f4280c00d2000e9580c041404803803c41035140c003444054ad403200366002008004500c80020a980f02c4a20301e0000e52042c2410307000207081c4800601070700303048000300030070350b074801e200750305d031501941040d02c202c0a2500c01d02400d010301580c4114036650320014100b1300b80504061580d8420f00010001100d44500f20301e410880c120f444501d400750818142ca04580030b041d03400c61480d0852134811 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 102391879 1250 102390629 102390637
    0x8040819180602070302040c0c05030f0c160806041502040b0406051b1c0905030c0d110a0305010c12060f050d0305130506030403260603031b0a05060117100204030521 73
    0x71281c021003000410590024884084a009560420443c1c1034944100d0b070005074440040c0c926801001030034511018000184810a10107096a440e20420846011030300641e80c00105903030300210500050200502d410110b80e401020218a040d1602c8015099801240302d91030503c10003182c2d00312404d9003582c0220b414440d89050340c142c40101c048001d842410740507210001032090310701048030300700019903034140c840007071501e81c1008450f039031300b034100c40070321861074003c42011000400100c00340180103c281c401c0e141c090000b1442803074042107910b0340d4040c43d51895000020003142d1911031660301d07081d40524065580c1e55038030303130030380e0303100340564407480d00034400008010516612007021107518a40c0c803842c14401b2098403000012030000c2c0c40c003da168004202800148600f41d1842801da00340c44180d8005043c1c80e01c0341801c21800345e00404640001c40080d9001c3c3c1824407010b0100d05c150780302141041d00f0b5440392940e8810b50400340703001c030300900c0320301c064000320f181a1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 102393129 1250 102391879 102391907
    0x9030102031006080702010e03070f020f0306091b0618010e0d15060f080c2d090109020c190b040f061b02010f18080313060219020105060a050108040819 67
    0x9650300e0505141a0344030354082d00c200f000240f001e40104010500c11f004419003204c4000055090042d140c4441d0b40403108804102d80c0000800d0040000d6102805602c1c0f042c0c0b00a4007400c1c4580c4184610b02c048244015128400c100800c0b011200003201a0007030001c0e442841d22030440040c60012135006101c0d0079010b03100d114158041c03078400c507198100005480300c40414070a2170350383c1d22141e991000c202903003aa20070026030b0442004034500c0c0180c08595a98083c90100004403030200700c61001c20f03048400210b400042811030a0740811103640303400340107650140900060b4a45503044200508010151080c241342c40003803011581144e06603024504090151900080002c0c2c000c0000c0032404100a0414000e00e990f41c00d24050310f28400e400c002c81c5c6207584d5828808650b1404280407c54000390709115045940f4210801d040b42c506503900005254101042000203810030b07a40042e0400c400d031410000003900c400c040c3c07100c00c03980502044420000c40e02c01c1d6504500702c100 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 102394379 1250 102393129 102393131
    0x6132d1103012d061710050604030606050406151b0c050a08060601020f0c060708070204090c0b0d1b050d020a0201061a130510050901080a14040b09010b09041e0305090301 75
    0x108000002990090050100004046101510310f00c561200342c203d21074100030801a83c0d01e0021201060b80c801e50000c0c03001016003035117071a000000c8803500a60016100d4035a140b0050100d41820301c00d001c0a40b40c2040010070221112030010300b030402c0002d80c840310000c118082010040990343c3e580188c08000d24140810f500c82d1039840d030390341d4200c403000d00611441c5054000540040307103240c0d0340340c00900580d1034a00b40ba2101522903129100880c0c000ba6540f40a001107640e090042d0003a04130320420550700c2c02c807508a8019640c3c5842d07204040686402e0045240d500801100c00b11200c066002d80c50791501c031400d038014040d030b611549084940c03a140e90542c911800041014203138105090008945900900054464080359140032a50070418004598064450143d00c4a51141d002c210031020b800c00b03903a407100a8400f00c90308030404007804003d40c42070203400c40d4242d041da00c1c0291841d00d40c86031460500e060b06a2110302e10451152401d140c03140048942c403180281c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 102395629 1250 102394379 102394381
    0x2070f0303140f06010c0302030d15080f032502040209040504080903010f110a180b0f0406080601180e180a0c0905070c26040801090b06132d1103 64
    0x10442a188044802100020702c1d040c55481c1c0c881101180c1802044011008955a5268001035980030080301060701076100a00c07005d105030405000700c41200811071989041e983c40c1005151810814110301400c5400511440d103080540c01c1189038410000e58034606541c0650010400900c100080315811505200130031041c4007040303004000310107082c1c000b0008000da40889000711000f840f0070305440c0d80100301d9060312a11401c0ca4551940510842040d220b0360340001c2c4200380c2c04040c074004000d801160400400d508692290b82c0040c00707091007003802c4402c004e03c0c28a0400e0f4002c0701250644c0da0045005011306001e41c0340365100d58001c4600401160800a4100000388560b081860038000000c0e40709101d52080007400342d02112500d02c003041003076000c444800c01d100360000e040c411301000884807000d0284900c40c07801000c2500242c140001840072050031140d40200481c102618242c12454001c10072419a00f40e402121031a11400060005020000183c450641001c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 102396879 1250 102395629 102395633
    0x8040c031b030b060402090306040210031d0a0606090204120f06060f060306090507050f0d02160218041a0112020904020301061d0a050f040f030804110406090e06010503210d02040503010207 83
    0x1d507201580d00400e8050b500f5901c803c03c1005074410400035a401d608950082001801e0906080482075005c3c10302284401c44811420071a80103c8891503032580448100c13000c3c030045110b5880a40655001540707410f00309140d000b44050b815900410000307620921005010807070b0b0010000d488250448420f1a55540d0003c0181401b800303070300f42d8145800c0119110a004204889254010050385070810054071000c800139080741c1150300640c03030b5214103000142e49010b185032003c01056000c49450030141000072403400c0d04103111100140350030062044856001150240c0c42c0e04440a8002d90b5943c800700e40980980c2d4088030240c154020302483e1640c00206840c45510182c5081195a407108103d03042a270701a18080c0107078076485605d0000c41d116102c0740da801401500d0100046c222100444c0403600740d40e01c01c000282c0e41e04140781240380240b069500400048004160201695000504000781d12040a500b900f00040c034947d40032898056038000c0c40c0040c000c42d141c22281c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 102398129 1250 102396879 102396923
    0x30c030c08030c090319020f0607051204031a1503032b1b021519020c01021614070602070503030f0306010c05010e010504020f06131401021204090e0f0a050d08040c03 73
    0xb04d0b100b4001d400803100d0884200040c58a2150000c000501c885650014031089500c980f200352b82501030000402c0500342400d005200139803180070000140e002c501050070390a038002d03103400009015140b408041e81e030300100361500315566010454029022600201e2590701e044152010706060080110144264205e62942400c090702951032050850340107890340301007218408540482064500c4260303840da4050305050050314001131400c50900704d8110f0081041c01c040b240ca0070f032074501504001051054500808542c002402e6440c28603001941300d001e941d244942000380440091140c1c0c1c480c0b80101100d40d0040001c00403c00c0d000104c038040c01040301c05900840403c601201d15041c8042190082000d207101c0c0310083d420300d5003a00b511040000c409046200381c0e407201c00c544800c0c3d80104024900e10300d0000e13948a2614160741801001c84028400b50040d01c000c0700840c001203080c001102061405a4081d0350341c2c503102005c050b04d6000600340d48512000c052442c506 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 102399379 1250 102398129 102398137
    0x1050c0a0227010806010b0315041e06030c050a08030f09010c0b040f0b0c0922061a030415021201030b070507060218030f0705030d08040809090709150509010c030c030c08030c 77
    0x36011014950380c0e02c03901680e03918a4284201107c83c1c20800014a00740007031900c030b9045603030050022940103001004090181041824689515a9440200100031400380e04000420701039a1680c500f51070105072a80760f000309105c01c86070207800a4103d110b82e2050154080c0607500c040d036011582014200b040450b54858800c8400b1004800030451170203d4805440c00040004e220200c0f1070302040300181c0750701311000c00358a02502c40c00d0200b00803090101a010404501c0308003070303d0b440c0030704015a074000c03c2812505244e1040020801150740621400d041d01e401c0100002d107500c503c1e601712090310403140050300c021310100d00704480c2d1641c64182d4201000482c219043e40c00c4841d0165201d03142846560b41c5680000211004039000e510f03081c0d4405c2c080c0641c142014410b401103801d040c4112890b50024981d84404d2102d00c0c80c0c45000c1400d0b0310541b90480c18160088006868045101300c0036080c40031985032542018840d0202e400407980c0710300d10700d880f414005085002c03508 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 102400629 1250 102399379 102399439
    0x90607030f0513020409111c03140403021c030c061506021e101a13050403091703030708090309100e0a270c14030403090515160201050c0a02 62
    0x410a03203528040c024038010349003d04400f00030344410b64529820000103050071601103884030f2020102d54440c0d915044034440840c0e140d01c40c40031180f414a001420a181020f02c1c00000f0000e010500c05a00e4001c805942c01e05240709061000d00030781025203820f44175200081603e420320360f0404000d60800041000c540c010f400301d548131159500445003441020155030200d07403006080d01001ea05a80285203d000d0f280b2410001e58007045c08107001e82051a4170b40c00d00307919001070108241e484501d400041c8901c104000b444003120140c00e480340700182c00881003160000c0481d595030014070803543c408000a22901060314104405840f0f41c505280d030f244034a06c01a40020301c0d04001c5c013902c0c441c0b10340442d13609100788403501c40001021450401003c00003800403190390f440d400002580214080e45807604071914140c10040394041c2100b81070701112045c04848094800741c841c1545c40d81d42400c110752034030881030600e45001d01260010f9441310784070001001c1502910780ba0443c1c90 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 102401879 1250 102400629 102400631
    0x1b03040605040504050708062d1f02070b070f02010c0309050d0b0603010e0c0a15110714030c0a030809040c1101110304050607020601050904170403060204090f0c03060b07061805030309060703 84
    0x1d910304c002074444d47c200f00c8800303030071040d1740031061102c2c40907000840508a6640540c1c005405407000b186000d05034040c8403084100c000152048203030100000741c010202c0315105c6103080701d66907901c1000386540500030305105c0c0d05481442018081c00403c400f420014193b03140381a194141804010019506c041c029480d0a000418002e0045032580c0030500141250b02018500894030f003a8a251080900c204400c82c1c1411103180b400703100364402452596034003400101c00e0820142008500290a03200304500700c01000000c1d943c100b51422000211000120807680d04419a540c1c0d052a091b00460f502c1c005d2641003403144503018500a0b0302400845a49540304041640d0b035642c03c0c06403680c000c4800000400050000d424105040650319440341015a030707580382e1003a608036030002143d03e500d94054046510440c0b04070700d1050901d1409002061030141e64460b203100344040071782510b403260480d2400051110003900b03100c1d40b04017141d589142400411383c4814003a500d4038006 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 102403129 1250 102401879 102401881
    0x120a11010801120b041e0305180603010f09020d0608030c03040f0b03010b070206070809041b0215100501050f070f061e0c17092104050109170a06021b0304060504050405 74
    0x80c0d4810340409040c1d40d818141d070391984240303403111000180c0c000c01c101c1d0781409032009034540c03044800c0c41001d650720984480d80c81d00604400000d101e808501858001c070030900041045070102440b00b0115060703094010303074441c07150140d40040c000f1a08011024480082e0720707400000000000c1003214a22003000c4030322a10b441b000e00d440d00c001c3c42001c488100500900d40507160820013004100d100c1e100c007501d005d03140c10205c1c055600b00c03680d40c440d0f424520006003180340c0501000d20700c400b2a1801003c18501005079058168880c05034a04010000c40d40b00011b031120b604884140342c00810340a8152800d03e02500900f1034040c0b03004811515100354030051015002c0c00c0c124a0894032002c20002d0705010044141c013004090302524403c10081d10b00414811011403150302540d54050350b00d03414100050042c1940341c0c0402e6903042c030840385013254140442c40442d01917100178051b94807003400c0c1c00058010404e08c91240540000030300015039a4005c0d00170030460303d0a84060001d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 102404379 1250 102403129 102403163
    0xc020106030c0b0a05120a051503010920010e04050a05010f0b0f04050915060307021011040503070e0a1d060114180403030504050f030a0c0605090f0304060f030b120a 73
    0x240e03101444000c1840318005000d02000f05800094021000c1c6440c107281040e0f000844101d041c0c40075240500580c0e65903061004040340160266a0207009800a0101250a60b100b00d036408007030301d15010b81d1030080070001813688a130b80c05c076140e000002c100f440203080a10201c03004101c01c0c89507000c07800541720001740c40c41c03804081e103012598500105080500d41024400c581c24024094011403045c1d0131407402c41d559032409076006074a145e0042c0700461500c0e25007400c540040d000008825400c1c0030401c620750f0001360280640300c0c1c9040c030046684904291030090602200310b0894000d100c5c0000c047c00300e0000d100d40c1281c1911302e441950000380b1003030000201104500500390704030a00010f000c01e020b5003103242c1151040e07045610000e003e926180c20b64001c400d4039000161160301080500056008290b00302050401900d101c0c1e402540302603070303803007617214000600c071b60b0201c1d102c8428080d030300101d10741d00c001c0c00d11012005c120a5080c0c4070740403201e041700d14010342904088 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 102405629 1250 102404379 102404381
    0x201240302090a050702070902120405070506130501030207050c040c02062d1501020a05030a02010b1f08220b07090306200301060c0f05030406212304110d080d0c0201 73
    0x44075005403815916494070200a000380030004c02e90030540c41140c800045d118810310080032058200c005450349402c1c24039010b0300307102c240d40c000c0e885154140070b400003c0c582040020100c132002d007001a59202145450b0703040040c0c0140e07035984a032800b03202a90031a004501a807150028031030303010460000d41459018100740c40d00c02c841c0603100c0d400242c960340d01034030440e88404050041b03c2492000c2e64034140303503500010b1160300507511000c05c01b000303042c0f0701000030103481000c0413100d2048030100020129040148900e00c01c4006141e281290b032101e48480d0301c41c0340c11048082c004c1c40c0c48500503160b503545100c115032051900c240a500c0c00c14140c1805c42545d00e02441d286540d180007021650340748455001d881005d6044500c000103101007000384020304464840b000c0c280ca100d110140c40900c1c140c1c2c028905801c1c100c2c00c500e00c40303d800290038034550b605c141e03130b425859a003070258040e084500f5040d001203104030402c0a110038800903061504a45006000301e941c480000c038 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 102406879 1250 102405629 102405701
    0x91e1802101103090f030f07060f0914130917070b180610030212031c050907120335040b040209100605090d06020f04030f06050109020f0d0f06090c0201 67
    0xa0b00358000b48008281850a000480c802d014024200c42d0300044a038446030070b0640542c01900407403a856424180c05070051050b40041200c840f11030f0350000e09a0200b00b240c0d9001c0100112503039241e6410013002a0074102c40c1510b83c68000c000e46039130790752034042141c410030303140410b0b030031081141d249140400286140c401d0092049080289107564240b100440304030b40000014003050008074400b001c00d20207801c52490040b004503aa0405200311801c040c03840e0022044003400080400100b0f400c881e10004a054030310902c0203c00341a01c0000d5a003030584104070400e080403013404140040d2080c45802075008403034040481d120304000c0c07680990140720344008124148555034040c685101200c005500071070016241140609001016030301c660011138003060b5078842c1d5030a10407030b48a850302520300e081d0210700d0078043c0c415036a001c2c0920343e140030503180c4816182c101c9401070f4210310001c0031854401e00c0301024594010b406000c81042690b0300011182d1107524039091503c080c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 102408129 1250 102406879 102406907
    0x80607090906140f2106100812040b0d020f0f1b011b0e04180b01062604020f03100c230307080c16150501090c0216091e180210 56
    0x1c078499a5140500003003501d41380803103a11000c014445090152100a0403c01e200c4490241802e86840c80c61003512800d107800c61009079001490240400c1c1000048400b42d840c2e138000c2948a004039614a00640720b2203500480b60400800e5800d41c0c0c050761000b03003140d0094201d0141c6448602491203080f20440001420303500e205014000c202030160312100d1046502400c041540046420424241840c00c2c6e01140e81058003130042100780c3d0300c0341c1103048031240204068480700007004840e02400d80500040d104040f80314000c00d80c0d5a00704902d50003444244c40038000e881720340d000540091002e11a144000c510340c08015a0b00c40844103c034840c0403a610f4900454580c1d0500d5440c80d00540321891044440803170440203e01300014090380517111580100310341d8100000c1c4402c1e140e00d5224941558002e15207042086400a540800c2e900350910004210462228a070109907071554860b80d01d5141001c0000707400726107c281035007140291011140c0044400007201c540d8841c0d915 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 102409379 1250 102408129 102408149
    0x4170606150904020d0612030e012601030201050901020f070f05030c0405040203030d020304020a0906091b0e0f0909010b12010b1005130e0406022205040b010c05060a05070c0c080607090906 83
    0x40e24071103140c02c2d4050002c5592170000020919144d454000700280610001d90101c0c200c000c500351650f03401040c500c003090042200d402241244101407000d0001801b00070b060010106080b0881e034030822907140c8503d21032003260340c0c1c82c0c1e6411010f011001c05024540c0030f406401d01511071402e081c020140030340d6000c1e005514229410021400a42000c1c00c100c0e070182e0780400002e04d400f460b01502c800f50510a10005100328555462a44005800f01c01d4042c001841c000003d25a01c040c1142990b82c019901c03001c103580d030708607450300503d000380781c16502c21180ca068036018501580140c0c08480c045c1e43c080d050203513101c2c1c10344560241140c0001d04402030202030081d8074121141c66001803044d4809070414010000741000482c045144000707021040d9000c110b00d260502510403124400c0c2010000a009070311280d859202c000e0004101684841c00310350703c58030410080300c00a4101c8032409a09407260035640c2c59200a6900c240054041c4402060401051048100315035030004 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 102410629 1250 102409379 102409387
    0x110f12030a0902060403031d10020a02010c02030120030405072103030b01140d05040b010e0610230a0f020c010203161e0b0901140c07020306010e040503040b0417060615 74
    0x160150140e10042016000c69155400742c0010384400380540003440c425210f481d41400c0111812509201c3d03100042d200300804400014425008601040301c2602840d0420452034180080303405040d00d454007141c00011001100c0000954402030b5015a00c50400c3e40d540640e6a9190302d00c01c003083c80c050b81c55090b0380d91100300080c000d0b031000312080f2040c18240fa80d0103031205c0003246a0003001c944c8070341503211020081080b103820191805081c4003140000d85041080114000c03000f1460270200307100342108a2a40c91041e080e101d600da00c40e2921482c0e5038266854000d040305624125a03000d0301c03c11044803020740c0040203a41c546030310280389000100107501c2d0300c030316900d5981c0d000315194100c980e800042450040410320446140d400410100f0840e4246909404001c01c2004400ca051118400607030300804c5042c11142d50b88035040391903d0758204070342541b00700e030b0000d07550300300028001540103100304d00b907141c0411010a840540e52880103005281070905621051030344108 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 102411879 1250 102410629 102410653
    0x30206010e070306030b0f0105040c080106020309060c0a050601080c0907030905030904020d020d05090f0f28081b010b0a08190b071b080702040b0a18020a0302190906110f 75
    0xc000719900c40442d140200f40f096603a2a0000c00d400300340d80703003c00a01031034014003950030036010700421001d0a00d014500b42d854104002d44030b002d508031217031050341d0029002075508410000c081701180c01000750f903080e5a603003840e280d481001c2c0e161280103c1c0b00d4000161590300034803403000c2d41074005018510b420703c0c00c400c0100030f40c40307161002086a403d10060601c402540308540c4581d18110080c007804ac00c091407140307403a04501c501281c550200701c8a4041140c004146440400c2250060b15004000c1c81c1000103401020f00c651248520780d004880300c410150000e0000d807009455030328501e1b8442604507190044401d804105181e08010100012100e11146034803502c503182021743c0d10015120351389909040c0c00d06848480012515000754505803141104444003243d5240b840c0c0c0c40d00c0600307450207c4440c02c10103074a60125003071304880d002e038044481486a4001041790024142409001c88049005060000c1d1542d190042c003404000703407201502c0710350002805021808 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 102413129 1250 102411879 102411899
    0x201080a060905130203070902090d0212010207080d0605180601020604020d1106070309210210050304081308010c0306080f1b13020c030c0105060a1212030603080415030e0a03020601 80
    0x605544440e541d240703400180e0b45010700c20700d4002d080308500790b4080600b60042500e0008150828800c052042051714016a280003180ca201030b815501c0040120070380450074024082e40300042c106640010301d5203c00d207816400041601c204941c05080d500c09041d100428003012506140943e2000000c20702600d400c1043c040241c4c072900d03da02100c07030303240e001c295203401030402100130502c00d0205001804030300c030b0001488041c2400c6122580255000140e50090342a6401c0030f105000001c41c0c04d0044100841304401000704000011a40e1511703018000c01200c40e00390f0000c1c1c5031040c00316641801141c50440c41051600800310201c0b140010070303000d941c0300c085c00c0d40300001c02d55800350214980003510807001c00801854a032030030000d4036400d6540061099208400014042c80702030224120f04240c1d60300007440050a43c41110700b41d0041c00150800381000c0000f2a0000b08905818442000d0307000a50342071149510141c070b11541c1b1480044020003582146005000301190 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 102414379 1250 102413129 102413131
    0x10c031101111603080a050903072003010203011401080906060a09020d0b030109030509090106020d02060a0b0f040e0f1902090a0e0307060204030c2402060604020f1e22060c020108 79
    0x5000002a00340000b04003000e8507400704401403280c11600d07800798141504124401c0d40112903060900080c60309114545d228418104001d0040440300e000f541c041042e02c00201040201800855076541c5504c0b190194500d21281c560020300000b0014009007004122980100c030060126646141828540c0000e500550044c900e03140d511703000001c02c0d9509001c0c0c2c07001e0303d0098840681e00c501c10b07003d0041d00007050300700f4010756000c5400703002071320750020702d0700c1d400310814600050041c0140c0c00500d008080d0081c1319070103800c046d07448402e503c021421104940c0c2c4441200d500100300c110981810b60f6000c801ba40c0304440b400000c1080500e500900c0c0f00c1c1500c2c2d01940d180c800c4907560f09080341c1040c0c20030354440580070420312294004072031080700030180c003ca103542480c000500a5235410000c0c03c941c021038020a0703a4801d000210190340303015100c49a0464a14103a080c0710190350030010a060500401a0100780c5200b81e445450054800d90340d4ad210f0a805140c0043d512030b10 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 102415629 1250 102414379 102414407
    0x61113060e01020a0809180f1611030a050d1b0f030606110c0415050a030b06180c0306040902031c080a0501060509090a050705160807060c08090718020403050d12060602010605010c03 80
    0x7d581880c120590303030341c0b0410307072007003518251301605418084408400220003000d5501444110114001c5010b800002d9407181c154918050740c0d100c1c4800003480207048504d5000d5103400707414000401e4603070450010410a44e856a08000c5d69549200880704101d00801104843e00700c0c410010b45030400b03412070003904501c0c0340040c0d58a0b5032080401c0304905c183c1e01c15603c8000400074407802e443d00006102c0b103e0041c0040103941d05100000080c0c1d440007500462140c1d507585180011500c0034814017000201c070300c034000d030012081c10000e803440e1811580b415246103800c002196a038001d0003525000e86020300000c18556400c065a0300034031028082030300f07010051110824203010046003044880c410480c803501d40c803907441c0c070b08151820034156400303000f0a58200011420009510000c45032009000140d41d042e1100c0c0310024400c07500701500b14080ca450700c2078004d42081e281d92a00607842c07010131089640d540304a00b22582e48c01000c0c00603411060342d8001c644201c41c40318180d0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 102416879 1250 102415629 102415639
    0x40306090804080708031803030304020108130609060e0705090112030c1506080a120e0f10050912010c03090b010f1406030c1611150309030a110703061113060e01020a0809 75
    0x40c1c0c480c030f4424600500c1da4071288081d880054020f450420140b01c0d0780341c604043e0700460940c00e0641c000b030030000d801025200c541c00c850b0308030000e219003500078540941d001603042010440101b001c42d220403507401203a0144051000006500c55a0b1840701c0b551901b40d0380340c020b020440d9903600c1c1f110103074040c0592903076203e00002c0b0301c859090018415040c0328102441c22041d0004010b0005e0f04001030040c07084400e0f0510034841e1325400304100d94031449280407a55180c808000644406428252160b150318100121400c60b0b0160302c003144041c021001940d06a81c4c4140720403414040740500704802d4503c8591141d00d0409202864020000b40840c07414000c80310503010313441034948030649580c0c2c25441b1003030741410507215a91001c0c00c00c54116103186054810ba07a542d104d200c250310204202c50080c0051480180b107108059075100100707000700c5811a580c00d9164104280107406100c0c0054005502c3d0301038020140301d410182c0160085211030346400c5c0894000084080e005 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 102418129 1250 102416879 102416887
    0x806040f03050304170a020a0312051006030b04060e0a06031406040c0e041106030a05061014220e0a020405040506010906080f0601021c0c20060f03041b030f0b090105010b0403060908 80
    0x12032900c5c02400c2e11070090350090030316140340d02300103080e0b00750a2640c044c0c01d490b200902014041c000c10120644070181404104d52180c1008100208210303400f12240141c04800d01864200136004882160302960080e0304003265043c580b40c40d450f06a40060802e03224100c05c01a07255a081480d80c02400790780890401100480071800c540e008031141c0294580c2c0b0801c004241c0707840c0301e80b45060b103054680f2440c89015003401c086e05124042640e001401005100007004461583c040c002c0c1c05110300b01c103003505251070303503201079007280c010280305a00300b00c0081c9141d441003498400b1102c6680c0e07042c610344c075500000c00c441240513002c1411405000da54590a203038090124084110658035045110381038140300000d610007000c1100080366a01d4800032a5036420305885d4a4000a0180343e03903915a4905003400c008101070604c0241015080003041c480010030055059001e0414000251740d020000c50882d2424098030b054803000f0b00007070010916503400000850b1041c07201c5458 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 102419379 1250 102418129 102418163
    0x20f031305011112070206010608011a0904020f0a020703050c010e060d0504050a0506070207030c05151b030c06010b071406010e0a09060608070b03070908030901090512031c0e01060806040f03050304 87
    0xf41d036100300c900c3c18401000200303020090703a040000c0303801003c1900c0c7c400c4c041d504044c980722990704000c20781da60070360000c203d2030026580c50781160340d141c070f1900c0c1d46991205d0711b140c080c2d203c0400b848240c5035409149202e0b005540a03114010407224010304042c6480044e00c00d44008050250041e1803612950560000188042212a008180e41d4001b020480e285242c090702d4003880d5002940a4810b10007081c424018260a4540310908003414030000c03042c2907441d03461170040d40c07181c917100d1150340000240d8048150040c28114080c41201d8406823544203100c6d5503500a1003005421880f44001030092101980301ea51b03042d00c2010f0220b00e0998410701c0e245424172076008604220000001d1150700d60300040e203600207280800c051030808080100117400d04c10b052240c44d00882424090b40f1700039900340100d0340d00b909050a050b01850046440f82c3c000c10a41094920543ca0703c28085120000050180d100e0381e4008a1650035102e90755045901d42c0000e002260246c1d503800c0601e035 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 102420629 1250 102419379 102419411
    0x10504030605090c0409061b110606040c0c0f03090608060d02150d0603020603090705010206070207150825030501030302100e07050f030106030c0303030b0901140f1210020414090a020f03130501 85
    0x1d541d83c022040822040388680020f20923032052078201061021042c64030001e01d40102e0703000d40c1708904603000284403246050540718581c80c03003401840060041088410903401c1014442550748541e0703180119a6040117010198140f0310001e90f1100e91040c6904c10004030348000d0101780b2107400040342aa690394089a03180d0004c4e5600700b00c64000d000c0c00d1040d940d040120350f902030081c0c40204116032400c03811504040502e1501c000b0440d0f5280003402c4500200c0045040c01510343da041b65072030544000400030304082c00b04030018012150190001c4c2d0440c011900c0d009a21402f80821601d013104003c8459444c64a10381c00d952610130000c0030503403030907800300114042c8d20041078540d0450100024144140c01c24003600c0540354203465603031500360b480c03440c0200031b0780c218901a4170800282e181140ca2104a40386a00000300070601d02d13144016428a00001d603000c0c0a1610b504400c0016030050250841c000340091000844500300b52a42c41106409100001024000712039950 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 102421879 1250 102420629 102420641
    0x32404020d060503190b04030e1f020d0f02070812030a060e091509150109180b0c070b010807050d1b0902040306061707060e0f040b0324090705010504030605090c04 72
    0x2078100d41d900c01c4100018102441503609203126058260041444e981c0c8849007070300e0140c0040c0401c4640000642d441d1101c003000001c50582064402ea0040c010b00b00a40d5185100c400200081d1644c103160307542d50000540102b03075901c40d005880c4100c40390f0385440d15070308000c191701040c03a00d0f4017000030700b003980c144000d000b08940005003c00b8015100381010800000c1c182c0b8115601070360842441700003850005055944104001c00e40c841014158120a4109907025114011510500a02031a12001044070b203119072010302c1242e030382d2030000740c440340309100e96500311072614160b1000840d03039005818040301640001712082c0d101c02c2141d0890b00290001c03242030f561200c2c00e2103a020700d440d003010860b84000003807440e1030070000002c2c80c0000c411502800381c0c0c00c1110400a40d65240c201405c808005022504e401c181010342500c42c1100404640801060001081c19160702240d0300d010341e003041c0c440c54a00351039a90b4020041000070b020461034010151511280d540700d016071 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 102423129 1250 102421879 102421897
    0x8120403050307091a04032004050901050627150604030b0f0703240b180d050303100f030f080d0b0607060c080a02091e060f0310030314070803240402 66
    0x1680b2072400b00c5024003071660f00c1d00500d8080340310050f8080384c20320800440f0b003500d5108040303d90701002c0c0442c1ca95001c010710740941d0711a003884200700500c501540301c1c0380b064908031058070784100300f140381c400f0444505110108415001c00003e1190401d0500001d10000241c110f9107800c2d0f0320348401644003020303920f28109d15801c100303125200f507140c06031810352006030810180c1c60441c3c0d01207410b500704038803c0d401c10a0010640780302d940d04015600100c5600504084405200d82c80c110740c50354411101286e44040b082c0e000300e40704002140c0c0741d080e40d40c0100c000c0d030340084a0b00c801e038ad55001045040c0360152580c000041c01d840d20f0018019080c400d0101140a00744039030080c02491000781a0034840d407050244000c61340d00c3c840904c2500c04080c00c9030050b0140100030540520032040d403148075200c000180000c1c03003007681403c002c4274000e07518501c4001c210340800401d4480d512000d030000c8000e10209000640f014100c40007814441c031804c010400540c00b080a80e0031601c04 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 102424379 1250 102423129 102423137
    0x302031b0a030215010b0d05100803040603060302180f0c03090703060c050c0d08090c0d020a0b0a1d0409080d0b040905060106030903020c03070b070f030203070f0804032102061308120403 82
    0x41d803810180c040201401c1482e40001900035581882d8444c0341600a003295104282d4554000c0b88114001a4000c0d000e4003200040c4c07913581e0385905016003d043d0340d10040340110a0028003039003851700f6000c5a40640c4107a0140c0029446c4c0c1e003074501d041d40000e0f001403054010381d031000001407414850b494542c1005e03100c50341c951400e0f44400d4145480d40c03444205000480040044800001c1054420810101e550700c1c1200c000d0700124029400d1a00000800c41001130951071468224131319030000803070315089012041d04201803105031041c2c410700418094041c042081845e015420070b10869101802c0003550403516102c451030200d00380d1205011990382c0100c81d040c954144014002d0b110240d0051810750f00d041d131110901d2198000160000c0c2d0745540350000c00d4400c0c0b003203520003a0048001864450380e400d010781c0c950310510048400f003d10004c1a401040c241030702104010294000c0d0446544c1c800c1110340c00c02030407200711401801000004441710038255424010f90203552 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 102425629 1250 102424379 102424393
    0x2a120108010507110c010f0c0501181b14040f140406020a09060e060307050f1204060c0807020a020f0f030106260d0c260c0a05062d010e040302031b 65
    0x12150848801030302c44010054400c4e01d00403821070018032108003050a06e0004240800444115402c0d00c09900052465080100103441440d01801a40c0400d000340d51075400c4050003184400140d2140c031a8500d11106850440400e02d056404a401c0d200c00c00340100d0701d11044a6000d00e01141203408035406a80030503c2c8148652122401c0003410752400c040c1a10984000094840d0100170300e117a08101340081d2507612410540300342c07098088000250401c1c1c0c00c141c5410000780114124144c0054055070002d0507a901c0018240f952540140c0fa00925407040c100b0300812100c130aa0b0340390150349460380000d130018070030900c180051680c040307080d080c8070b0f101710542001608440007040140d000300b080c0125012a040281100c00c4000c11040301d04d0b60b018140d640d01402020348410702600200105006001c81c80328441c2d4041002107145405008a8111040c03402c112000003100e4600184001d141b44040160024007034011241450490305000071603404d2103035540100c1d00522 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 102426879 1250 102425629 102425639
    0x8010e16030f02030901050f0a02090d0b100e0f01090f050c0304020d140d0806040c08040b1915060f020c09010807090905070506160606090504020603040609030e190609050301090b2a1201 82
    0xc030327000340003e42c06600d008800d000086061003854005090139030b940010881c502d0113003250b08014940b030b011807036a80c074020009414003002441560405814601c510568664600c5070a10400760200c1e03880c04d6890320340912911204400d0211601c9045d500903440388441002802c1803070146503101c036800c1c03500e4018401a201f0190207241404000000d0000085d003a101195101000140040a4051030104032001d00305001c1d800e421400f0031080803c80d645d02104030025400503400f1129100f2140c41400003c031000d209100e01a04000418002d1b044a900400519409102140c040703d45400014043d544450070b007401d10666549444100007890207818010041c1040400840c0343c140c0216406100040004000c20b0780c40800c58105800b540c504261024003401540b000e220014100c10200d20314015040862a1058005011b203414022001000d03806025041d8030b48a18240542e108440a45580c800041d04200002c4504060240c5100090480c00d401654980 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 102428129 1250 102426879 102426901
    0x1a071202190306052407240e06090a0b070c060b062215090918050d2307080a030e100c08010e0106050c1b010219051c08010e16030f0203090105 63
    0x90b6200074010540d402211034441d44200a40c11700100300f000301e0b581d441303152410f4540c500c040e0b00b032040421502001603000f51802e41c007068103410300c901202e9560f11401c0c0416602c1d80404001408442c420000410040c401c3c0d901003010351150302d000c82c1701866000011516081a160072410b40720700072206514078031018211000b0003410b840b09111702a010001041400b0034010340c0021900d4200c001d8900c03403124500c9400c26040003c0e9030110a242034000d200e003204101000716644030000d070300101d900c45002c89007040d90000e1006d15000d02404c1c1070f0302800c0c01c26820700c402d0017072400c0c101c1c44200c54040c841c50040d40e6518040c0d50b43c140850044003000c1a000b60082000034000d5404455000030482c2803500d00000000e0844003100040b80783c44078031199656003ca40c07592010801c1400900d100c0070300348014410a0020940070120380c402401d1013454401c164590200780500b0980c0060424900c041c540481e002d0110601e80007a60700a0703c000070180c1d035443c10051440c0117 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 102429379 1250 102428129 102428141
    0x3070605010b0a02060105060a0903050d0c1115070b10080d03061e0803070f020a12060e06010501080606070b041a04050c01030b03010b030a02040f0b03070303110105090a1a0712021903 81
    0xb9641038181150000001d42d101c1050042d176002d00e5001418141080c060404d803c001c1d54020200c5e81e1f200c40344007004000d03c0505a003120b0017007921100030014074048010303101940840000d1420485251203201d90124050014181c849412001103803a81c2c06000503129014541c8012861900d00174052a07030345030f4400c03149000034940d01305110f01c1d0000f20846400c2030304100d03080000f0a560000680000c5d01da070000e041c08404492407420171600703411030000c1e040450159401f07607a0344d400660303207440120b850a602c03000400c1807900045d990480690000e020f64030302d260414600203034514020302610b0030b8409501c150380181066038540551548144160000d22010300c142c0040b81e603842401000034443e984909118401065a9120700300c088801030807110604e50b01d08001d0b040902484000c1c000e5400d20001440146001485012507640110101800e028000c10018020300180c07814040001301001503d420200d800a4641805070340000c079421810ba4802030f049405c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 102430629 1250 102429379 102429389
    0xd020105040803060405070e0a060306050405010f05150d020904020703030f1b02120901020c06180102070f05090a110c01050405160e040b1b070b010b0304151407110a050106080307060501 82
    0xc105020480010408000da0f600510151008507017034890ba1400d031240c02802c8075843e0800c417090800212907500d90011030882b40140c504001f107980310b84510510f600c1ca4020950410482c22a0303494040607840203025290740e0b07440040c1406008e03000142a68460b800640c000303612041c218480034000d120303170079040b2042e68044003c000d107410701a45811044040544481c8081031008959009104040520000401c12a0b441502d0000c0c1004e590311020a02d0051140700700108003414021903500540340000c04188181c0d850110440152040100c0c8a082d02c20034807500e42082001d000d0745005501c200042e0400703824841c50644042c0059204440c0d44440d20705010214003d1982c007904135200702070210910400c044000034511412000078800003402000080089804008c3d50103544100703410030b014001c1c01d00380f00990324402d100864a8015001090982c0c3c01204101d00c9080310750705981c21031000ea01c40e01c4c01c40d401540600d0303060304002424410000c0314412180500 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 102431879 1250 102430629 102430631
    0xb010605180907020f070b0309070e1015140d090b0c0a05090405070903021002060702010b0109240e0a030602030610020d02071e0e240a0b070314070606030506090d0201 74
    0x70412045400003030328000d40c5203002d103202c40007040969100744890358249116034201d441041c0d42d440c540c1226401251911894094800c010944c0c009084c40316010701e81000c103e800840c24080040900d900c0040c0d49014007103680d4100702c0c0d009130000582258044180d000503200b440c1c1c14100d406030f50040c000403141d001001480100b070b40010a0314603e680a48000855540e504800d550900c401e82001c1d40c81015241c28240c1c00350700040d860701c541e48a8ec000e02c48242c08000655500e41240145001c048034560b0a40c00101c468801031044645403408100e60085803000c42d00001c03a541007669841e03000820041e090038103440d00e080076240e80c0300400c0d4650200d9002034560845028945424010f42d05800d41118282682400742c15150641c20039400c0c02c2a0621080303417802e212280055500c2c4038005146008000c200881c1e03000400705180034850b80d8220b0360b499100d01c0c1c540d1210f40602464010840c43d120703100280d803140000b0000d81c10200a110f14110000480b03c0440e = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 102433129 1250 102431879 102431887
    0x6060105030c070b1812031e070c200a1715090601060c17030a060302010e0301060b0a11070305030406020c0901080106081b0607050d0e210c060a05041509030b010605 73
    0x42d5210a00300c40320b060304985542210307251040262501c203c0d025150f079042c0329910704040f01a800500450151503100b40f0004140400301114540101c11201031b03000c45c8100c04050041901c4424003680d12540102e488000340142e000140101c1260300546031184080c00c09210028041104407500221880569083d01c1c000d00041e82d1002c1c14040c0108201c0c0b420100b2041060741c6161780c98007085440b560b6200d14228010000800c01e5104c00d900060415040040a00b01071240744203039421000c1e0075180030591032041e20240c4120700710203100d1040402c0000821828000b07080603080a902500040c2c8142c01040400c090607004a07403107915001c800c100310000010020340600c0c007600e031142040811800175000d800b5980e8054101e00444c242a00f030603a0044105211690440e04911502840c4500048801d8000b8003403c0550000d8040c1c0245e240c0310010384030310388003450000c0c035040e1036296040c41d0a505440f44404038480030028010003203a40783c10750150159181240c10 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 102434379 1250 102433129 102433141
    0x130f0f051b03030c250e040b151c0b071202030406021206060406020309010f0e100f1209050c09180d030b010914330715060503010b0105030a020a02100515030606010503 74
    0x81c1c804141c02c401c101403036080360300d5504058a0b003440007010754a4004071b461401d4200900b100034100c0e0760020f0980310b51811901460484111540d21034542d00c00c8182100c940d5542c04524002743c600d6088c8000303194032a8004036540015841580710780d0026071946c1642d040840103280252000344100740a00c420f004081e03000050350816207013460b05140d810642c440a4805401e20045684c110f03074010130169070982c2041294001e0040c43d55081c0740c030002801103000702c1d9900c4000400603040b641360406a807500e003040642222000d40e0500310344900c0c1407024681928941420042512584c0042d525a00250030130000d25546031024042400a00004e0308011005845030041c1065204005110b81c01600a42000b034030001d400c0d86c41078141011418a00381080f040fa0660500c10b010840d42818012003000c14010703119142581c0b11020344070301075000081007100310311030581252204d161074054036005803542c501510f8901c24142c1454100340c1d004000c0b9050150410900ca0 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 102435629 1250 102434379 102434383
    0x5070506030903120c0d06060f020d030509030a08041509050a05150103171e04060201060306150609030b090c030a080c010f140105010509060c0a0b061207080303130f0f051b03030c 79
    0xb5400840625200907640e401600e288031b00a80800000c01d41c6440c2c00440c03a0b0341c002e04030b42940b0510742c00b103544001c4080412805c0d94411104c00b0495002446610b06290169123415000b81c41040380c4001c0b241826060400c59005040954081e484603640105128081c441403540e99000c105c0c2851035811600c1c0c2c6038050a882c5442d1315042c000040c0d00d6000506001806145250020910b07600d039901e190090103481180002d0310a0340c64506241808401c0914203c01c881103074460403a041c1c6180c8611080c4400140041ca4500500015503041d81e420301051001d584581e40c505c2d1201030202440b802c44103900001301c1074070314051000244142e4451a541112002d20740303c0e13074451300d2101144c0c8900824000e405603102c1c908801041008054403144950300546900d4611031030090202e80c0c40702284034180445d0410000300b000304045101c81795080e401041c0010f807501d06e0381d0f04c44500d51980e100549007a00007610000e003640c10091120540c90003100114140039170703142d1042d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 102436879 1250 102435629 102435637
    0x4080310150504060c0f050105010b1c0603110f060c070905040b06011704021002030705071511060f010513110c0f0d090308090d06060e01030602040302090a14150103110a02010905070506030903 85
    0x4061140d03031358000781041013030a4401041ca40c1f1200a0000c0c0d40d46010404040e0000080741d0352082803824080b0444009110300320460b500b0800388020b901103070313080c8003c043d1492803042e0843c2082002c4001800100b001500800346010000b84038581401d0113410780b00003514150400800c0c04d4081c580028804582d60003580445407003194800191007a403862248400041c5103024030b0710000703086105400d000760032003e151070781d94074005250340c081c5d10341740200c0342d0560703250025006222070b08100c1a0307450304441201000907124207141340c015094106a030580c20710b62100c0031204040f1014003840c211002c240c00c20b45d1550781140c0e5814403501404008078090202d0001c080240213058005900a110141000c080c1d56104d0900703c1c040d5009000603401940013102095100344907100350068100381400408981d25031161040d0025040103a040c10181c0f114174903040170680300000c003036000868000023040400c52074090304024940d0b0055204a44c14001c100d4400c0000c4119 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 102438129 1250 102436879 102436889
    0x80c0d03050f04141006061701050604230102070911130504111c060302150d1b050a0e010c06050a060504060f05180403030905120304050606030a020f040b0607060504080310150504 79
    0x1380c041d00441d03a100030b240c0030326041e148500c1c40c14180c3c000703211500520581d0920403e000c4040700ca81c0c0310410700906100300e10a040c0c40c015500c0c0000c08400c1400000003070800144181c40380c255645510900341c070001840d034041800001031000f00c403900f035508100200010f40702070002d84c05084204003140580840c1410743c0a88600816000006501000103194020302e05c01181c400150310304120b0300107000c1103400f145404500d035080309a108502e580041b0b1562114a0400c10401c200c40e2000110303002414880e041405000203240c0740181841110040c4002403201c3c0b40004200954216074401d15071a408031034144195119a100c090030304001490740c9002e902c0714501280104203040c009040f40c0075002005e034810102c00300841c0540d00074070894003251628030801d0748560040b140250b1140031418901c8007401c003908400c2440c14000c0c030711801c02420f501c54005503802200d0840d40020004208444104034029400280c141114800610a942c45014010344154003130 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 102439379 1250 102438129 102438143
    0xa110321030a0209150406080708090613080a03140109020d0b0108010b09060322060b180702060601080a02130b090405091207111203120105090105010203070506180c030a080c0d03050f04 82
    0x1134540d03640300c0307040e214040304a10049541d69a41e8800c024083c0c00181d0700b0000191a03900441c0c00399a00145140c0a1610f00f00d282400d0030040d070b900301807035110440c80c0060580364800701d40c4000303001c1011402091014409a035480c40007a848040320030108545043c07205401c01445040d800c482502c59640d02a41c0132952130b00c3d00d0640c41e1083e4007450410701d00a008950781c00400903203801c10381c58280c05a80104050240c80f90040ca52003040f1402401a40b04200050856105802c0241c00880b20180186070051500640c90060941e8003d003c40020000e54041241414842e055100d801c21003e0900064499204410392040940182035070b01c02c81200c0349981e440210002d42d07561168100c9941d00c1f20350000342100402446110f129450a2000043e2540040100c0b070035980d20002900543e52392110360002134040005600e61031080905206090300c0400c00c24404900510440d529600300b14001482c0000c1d0001f00b00826040000740418a4a036101c09500030ba0301c514 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 102440629 1250 102439379 102439387
    0x503010504050c070203060a090312090203150c130609080f030f0a03020a030609140f0f01180f150b03040b160903030c02011202130810020f070b0c0c0a110321030a02 73
    0x7014070014002e4404c040d6150280c1401d0000c140441c0d882079541903c2611000da041c480344520b0021502c0e4081c1c0a505604035283d0080155003c000d281d6005c160034212505005211280444221103904a000401e4456070305120f07a030700801942440c0d01c000c0008614080030780c03503110418000c82c0c180c0d000349900031480015042c000d401c00d6015101d9020100042e204188418406983c00c0e918201c1202c018004500541041041705050307c040b4094031280c078181d17128410052021003090341c00c5980c2c0d41400d403282180d031642d4000400c800c01c841351703c07402c143c1495281164080c001c404010b03031101455110079004003800044a42500303080340d0001013400141c9401c2001404031103c64400a02004c00f1440d0306000c10a07216400c040320b08101c0304a800500300d200e400100034640000340038200018400901e9690301c12641080e081c188910902582d1502c00d002e0f4007114000d007203c80002250408005403c10341d98107c170800c150300b0707400400c0d414511003c2c02041003da0005 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 102441879 1250 102440629 102440641
    0x601060207032405070903120c05060105010c0f0210030b03190b0406020c012a0905010c1e02010909090b0a1b140d021308071d09070b03060f031c090503070303050301050405 76
    0x1600c416072001008428059482c085c94010b0844209000072134010740040382018400b44145100464554401c0003032080740d0030000199030059003180c003260b010071064030240041e01d80d1910311421400a4901041150b020710030103062429a61a110b020504020800d0125444003500794005401c00c00040c0d44070720000c292400340c2210a03030101501205d0300100b10805150400340308020705640d40c4121292544011074142d0040a000780c121540c0c0444140e0041e214156000c016205040012007507981d00a054203840d00a2400d64032a44100c08010300c274142801a014110314400c1140c00035589164041c1c03014110140f8001c2020b0089020101c250700355044880c1c80070750600c003c581e1643c0340c078032075030b9014140911144018561103081c0c44282103115035001d448400c0c0a49542814051400080d0300014000c9510455045d0013114a45050010380301002c001810b0385c1d0181501d0324050821417007940002d001e41d110f000c0c1000880ea200d0b06490540300708450100c3c1e691551 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 102443129 1250 102441879 102441923
    0x7080a12060305010504140f010606090b0a090302091503060a0203040b072304030b150402030714090103200901021b010e121c1706060a050a0c020111010e07031103060106020703 78
    0x7503007009050b58a414244070a00c14a40c440c5164040404100c4402d6442020000e00b0703a140f5100707203c0802c2d440001400800d610700094070140300b06103071a480e15541c0f0b4000036400541511403c078010310000148000d0f0a05004040d4400103021040d0301d941403d68940d440c0200080112003003109411403103801410340c000c0203d44242e1540740c180c44507282e0034100401c0400f40c607605805d4054041003800c81c1818000e0306c0c443c03215619103e80700d0390f80002020150b845005401d040640c0e82d51501ea151035109803030b00340b15820048058841d00101c00280c902487e20212203507241515460002c0b5a92000303000e5000c52041e0354840c14126490101d0b450080b020721100f4500300b00040c400d05444e1f203d8050300711780c0d0016000c0a007030384540d81880350503c694941c4070000340041101d0011a80281404400301d813046c9000c2022410703030340c40d560854042107551041c6402045081042c04400c4001c0d004c0c40354101e002c2c0c00c0342c0d407401c1c0002c0d66501052000900c0030103d9455402a0040 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 102444379 1250 102443129 102443141
    0x270f0603090a050f01020d060e060603010b0a03060e0109020a0314010e0a0207060603060c020309010f0503130b093901030b131d06010f060f02060f060f030a0f0b070306050607080a12 80
    0x801000c84d2410305020020038080d4000d56441c044003031402c0400074010240d202c043d03000b90405080e0514507401c05110400c40c1e404540400103160320b0b03180001d2510441c0e13213200d0091120a10060b1070f07826001d8010251820306401c6400c40c0c1c50326006202402d96001081e400002405006a0b40e665904d80ba20140140d0361001e8003940c03070143d41d000241d40100c001c003400d5100740d03185401440058800c0c0d030305000684916a04e80441c003081800550f44406050304030002ca400c0702c000f140b03040d203250446950380c41050406840a144400401e00d2001603800303540d4242420b02001d4822808200040c070070680d10840503031501c20b8100c041030300300310b00c04041180e078080c1ca940f5a103481000c03058407030501c10301c8006000c0300142c06100740301180c058003c1c1c1c09000007d1443d1600400c008280388409641c1c3d0b4940a2100e82d000062410125400070300e12a459030501c40c40c1424016003220b41c60b0780401d0207900d08110800004480030b085494081d001c1c103010111035041b190540042c00 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 102445629 1250 102444379 102444383
    0x302d0f0e0402040e01080601060207030317130510060303030b0f031009020a1d04110103090807020f060f0c06061906020d03020f09090901020d0f02090d14010e0111270f0603090a 78
    0x1c40060013140c801004907106043e0742d403002c111507480e41d0303a02c0300f207070340361124480a00000c4160f03190b0882d4100c440d2880c2d4120f600d490880b0b100243c41d0b111142001102d035004104c90f9a40c0c202007040582601508401020403296042e41c0300854011a0702c2d03085010040d40501d036594103000841da2031281171006080f07030b407041400c2218840804258000161020740e10b9103034403004c003140ca42c420b000f80106950300802507801d1000d168203014504044e40000c9a0082c010700249204652080c003a040030b041c074100406040c1403100901c4240001d9200c1e108101c018a10244500c1d60005155007403c8814680141d0f039031290300002c0340c1401041a01c03980200100107002814005401904000048002c10030035020032070802412449070ba44d440e90041980341041d004698414240003c4e40355060021039811183e0201ca400c450006040688802c800702d410148802940d9500c080c0b03204020520f442000d80bc0c00142405c0881c44403144200ca00200081c21030a080c050140030503 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 102446879 1250 102445629 102445631
    0x204150e01021c2a03210603020a0b03060102011b18170717030f1c0f090210030e030702030105070305090d03050108071a0c0109030305060f1f0507302d0f0e04 70
    0x1c1c69a1070b00401c06d03c19400c502011318800050b00031940010b1007100d040741c1c0d004040201e11498507003026030a41004040a055560780c1040c41031540b501c2104000d8004296079540b502039518042e031450070056041a0301003039142d0794002002e41c00240060030341381d0586900c00700300a01c0500c0340c654416050207020484010415450703d001c3d00d003441c0da0505501500b4040103540480042c00c803420800080e6000f004c40d19541c4029010740d120040104528096030b280040a40200e4251902540c03000b000039039850801c445880309004074804d859091030140000e514001c0c84581d0303040140204000c0311204d0105124011011044820443c440340c0203100d003080b039040241c01881d0444066000303100d00e12019520b481c1241da040c502c02d01c500500504040030303400c11503c40d004040100c440c50303603c800b25652652400c0b6031350795101d101d02c4a01c04442401000030405540a8140c00c0c420129075031200c820000e21111006d056801d02e010481c00300081012581ca4103000c002c16001 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 102448129 1250 102446879 102446957
    0x308070b090a0c0902030a0e0a210e06040b0705060c031003110f0d0302010b03010b0613090c03060e090a060b0604120209040305040f08062502060403030e07090204150e01021c 77
    0x304c1490700954461810000e0801c1681e05461810340c44000d204c0006240c0b86c1241c044040c00384082075665042c07907540c03400810b852190404a8034951044d000406031000225442e0200300c410050303c0c1d03009584e920001e0560030030119040d9584401e002c01022010591030103215a200c5210406107814000c208000b203034110b00300a802080590102802035091200f600064100300c400c03200703284e104d006900966464502c100f070003890514400c2d0b003003507112000003e1400f0042c019602a107481e0018002101340b0749003140c220b44000c001c46005101c1400100b104c50001205488110740644041400780d655141c00c40301842550018a480301100a0102e100040018060300c9140462001c204030b05201441c003289400c0c0c4903003480143d2101000400280c444e400103849168800121907020791903402800590700603401c109002c0c0107204041c40406e6200e40c221107a04420b0000d05a0f40c00d0110302805039455145002c005c0c007401c48061201141c141c3c03540c0742101008032a030307020 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 102449379 1250 102448129 102448139
    0x504051219020c1f030e0304031406100e040b01030f031814090f0408090607050309062b060e0601031d011a090108011104230a0f08070b03010308070b090a0c 69
    0x1007103081401c980184100400b421190502c0c000710354001c05200601c0800e0031000340110080d040c104104055400180070010002d18050448507509000d90068841464194452450030f503d541c440d4a1145107401400040740c0d840704940d040d00d42004200e20103000c40d090070b81d00c2e401d8000d504000c05000c40c80c00100c11180d15584070b109101140c40490a455903203105002d010190707005002c040c41001115000d1618200a02c0c48a02c01d805a900700192940001d020fa008915180600c80005045500b42c02a4a80444c8401c1c00810104021420840101c400d4840200311505050366503502211415003404050b4451900400074041a0700c400960201c2c110071001c480d00030a08013002150000c0180140c4150f081c2125505083c9440d00d22049200d14080440e0000c0d80b00555550f2915242c1103c0d09000d464144450f50750286003c0c00e103413034150550f0240c5003600b020b00061000641c0c81c070407241e0b0260420300702c050039181c03861014181140043e000780905000030340003603 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 102450629 1250 102449379 102449407
    0x2b200328020106050301020906160203072301080a140a11040902030103110103051e0c090a030b070f0207050d0c030f061404150605010305040201020d030f020f070302070806070f0c0605040512 84
    0x1806160581c000e01c0141d0f81c880034076081c2d0188910890703004009019009500c00d4070041c20301e44c6030000302200e540603030324500100204604404d03910300301d203514031042c02c3c2c2d40c002031a5900000904820001204110303207001c03140c41c000d00080180742e118900d14903242030320f80c151009841491070440d070309d50303403403410030b10054020400d076002c43d04003400070b1900342c50500c00501460800f13034041015610029042c0c416800341d00e01c203034000b25120010012a4007000100d2103001c4545400c443c03820111400b92600c1d030329034401c03031241180d4000303440081d4000030f46004413136106000710b00001480c070740040a403120616a1108081c900100002d0009102c0680e051100c10300040240c9621840118141d80c0c080300c3c0039015902508480155a03c664408a84100c1c4210014184081051402043c0c2e0000206a005030b00000e410311071400d05006807a08040d0905104203c03c01c2c884004e007103402d4200002e001c00d03136540c0004043c045c041c0806520810707844180e03595515046000b40d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 102451879 1250 102450629 102450697
    0x7090f0906090b06070b070806061215030708030408151003080a0f080606030f011814010602030703110f0c100201090501060308030a0c0e010e060d0603020d052b2003 73
    0xa54100e040c5450860a070400c602254402504004600c1ba2507840070804e94100c407000d4070003900f001040080c64250306003160303070714060800c440c18071601c4c4061320300f0949070a505411040303d98008010130060100001404c92881000084034500c7c0e0303450103e41d07400310060b82d00c003411025000601d02c501075808400b01040c443e1030744509a06441c1c480c01e1002c40d010444605000d100c0290050010440c0162005620300341b00d800070a407034010070104587c9000a170b00c140056800418030030101900100e0000355820f05200525203c0000c043d46680c559141ca8807500820491204000d032074400c2d000340c000c0a802c10000d002907a604d250400709a40116101e4004a141150803000d0921914440340700700d40c160f5407050646e031008200070042d030008903401c00c0b40b6a95580040140c449040440722a802003014001c480030040f04001214020741d031000307105c4801d4028084003500321741c0107081442100c1c000345924615241c0d0503c1c5211b0a549202080003400361002d528a2042e240 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 102453129 1250 102451879 102451889
    0x70605190e01081b071704060e1c0201051608040f05040b04021204170d09050604060507090f03080322050106230607060e150a02180d0b04060507090f0906 68
    0x55004440910045a140007090031181c00101c012001c1802070f49410340103550303045508626403070301c201079844000f000d256210050755800b0110b41005026008005040b690b842a00c0d20009403d07420356141c0ca072804940001d0500801142c080628080042090f00c425802004d243c0e660f91644000c07030049801c0c4c030609105a040450f10b144509040c02610320310200201c2180040d2510790720500075030083da5900141034002d00c09000000b0300360007000c444500030800b41c552030900342440d000b91003000b0112030500201280420003031007445540030843e504900700c44d4880e160390341400d56103202c56041c40c1400029a90301400e012065115104079004d95400d04c0503403561019040b08540400001030340110140030f89004241240c105c100100c00307040640c1d144503081070b08a1740756281540e40d110a04d40c04200b00840c2c0b260311000d00c465a000300c0765031020b50002d0b0740d0010702c40b00040000301155100e8010820f45402031044101405446c0340f8034110540340c10a00d0000c090f10704c10 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 102454379 1250 102453129 102453157
    0x1090c090b1c1203090201031112010f05030d02030301030b060303190806040f05060a030204020906090901060903050606041107061d0609010c03060b070c0302090c07020a0b0304060b040c0518060408070605 90
    0x3403001e500c80a0280c202c605035000d40524444210668140c004000c0e500b810380c14180c803480303a940a000080c00810341130f0358941d1011250350400d086001241195006227019500001850b0515a00001513038112913000410001d15a01c0d0008203085000d881000410001c01c0b40408200580000085110701d0b000d8408121070b41048000c04140d450545070030307030001c61101c0c0c18405030816030000c2c0904031010701014501080e04d0085481b0b50300903401040040c1e81802e0600c100602031182e581c01900441d400d12070006d81490481003846101c2c40101865682c24100446810440c170000b00c0d88084c07000d40720145402e15665000c0c00300894080006807605c00045450f1040e01c09403485160824400800141103130300340b10b418103003c1e02d40754148000784020b10050b503e892681001e4500f042c141c1d616070078289040d02c10399451041a6116078200824096041d0380807054644803d8541c03c5099420031100101b44a88240e4000185070700505070049040c42e00318006200d2294501c40c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 102455629 1250 102454379 102454399
    0xb0703080f09060114060a020a050706020105190207031b05010f091b0e010b070b1905040f121b1b0504020d091101082e0b1801181809030201090c090b 66
    0x11482d07856003001d004035a60301904034070107580c50900001420280301c490040750f801130025181c451928034240e000a006030344580400c0031480381d050012410166010041d03060420654010b0090f140e500f541c8103d20301c00218020610009401c0a080911070240400c0074081509000002d250301d0641c0c001507214603640068000035502186040360502e01707009041c01210354034890740403030140135840c010440210304207041d500c0c0e21403180164810070043c410011280360400b80e40030302c180d0003404c2c04903000c03e00e4100301c00c4800c1803400d1640a00016180000d41800761685c140742e8001c00e401c503102150212101c131030303603200394a60f900400444802202c5a001180e0301d040403211034034503810035040c0c14604d42041028070800104084040c5495440d01600e06180c0c1001e2400d114102c0d04e504920305039604403022080100e81e1240c42c80c41e050500f482100118010907034950340c40c0d994521078040c103100f980320560103588581010001540d070521640034054800b0b03a184507041c061 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 102456879 1250 102455629 102455641
    0x804020a081908180901140405010b090913030212040620010b060703050705010612050102030a0c0503011505031f080303090d030b090402040e070f060203040816060819060b0703080f 80
    0x10010340072048040090315003400c940c1c03510400d13000620a41c1908041484822482c0e07141484640a00018045c0c03080020f1103008000c04d0b100103070701c40280340c10208605000c80d141da103070450744003084603500b50f0100050300d0102c0c0390505001c0000a810000b040214205601c40003154500e102d200c1600700140001801d00e08840c201100d00c1c1e4081d00c01c01000f000240240081d000e5980640c0000030703055070342c03520710915070784001c2c0481d00c5035070020030003120031000c1c42101901200c0e440c020382998108200d5281840c00c4c5003802c0705010300840018034a101c24040c140c80b010001c1280b03070015613a1003130036a4030303002038179540c0700d0b400362122601851f407080c4242e40031080020404e25980d2141e4080c407008141c0301203a40c01c1070044600109026404074004d80c0240440c0d0b00650b6114030f8000031500b40192902002d0b0a42e00c62041003151030392140c105500003c070280b9809512070080d00182c01080143e010f8020588017280c1802030540001215220b40313140151425a940e0701 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 102458129 1250 102456879 102456883
    0x7030602221a0a1407060501030b04020103050a0606020d0507050304080706030608060a090b0604090323041508060a030611160c03030e01052704090b041110170a020f0f03070804020a08 81
    0x400c00920042060004401d402d00c03840181c802d074111200704500c0e00c017080c0c5481d4140e0f0801d0f001a1a03401c0307680144011540d0511496a0040b003100c010801c05007842c20007501d4000e5201c840b802c000d030121744075003442403d200f150010030900e0110340c50706580d00000b4010703081c2d510541c2c107603004190010b0a0b014050091030802c6500c0710050209603030b1081003000408150700d0503003c001d446550410303140c441030140710800c082d40302d04075100e40c078001e4080100c11400c5246020488c3c0e40c1d080c4615600c1e0440c5601c01d49a00038008a400030300500204401d001c1c43c81c11802016602181c00d090208100c410320a8034060703581d0480348011600155500c0c85840b00084220804000410349081c11184160003600700910118010b00c02e92140d8113504001d4070265548009003080320341350703e4842d404621441c4281444031a001e45805498040b00004203034000a9400007131001005900c031044071940c080401c015520390614100042c82d003501101c003240a2203051708042401100 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 102459379 1250 102458129 102458159
    0x1140a050406050a0c1515120203030702060c0c0d200a1202040c1b1407060c02010f0f120509030d050a02131e1203050a1d0a15020703060222 62
    0x194540c0c500e01440e10008403025849260301e0010002c3c0c00070100006070074001c0c03511000301031400101e000c50f0071060300c40b4501081d500140424120f81407420068401106075500641c04941040d15030390001c0400781064003600681d50310100036003540b0704204d820500f215404042e060b002c1c1e110a0814180907144a6902071030803007280000c00d18006207056003000e40a10b07122700d044c1007070200c07100d0241001800d161080395001c0681c141e07552148010000e840040001e440c001c10754542c00c0d00040c00b255101400e04080000c80c0c4421301001d8050500d4003071000d001c01c010009ca20788800425101d812882021544504042c04610500c48034000c0e2842014000c100e11000c5280128102e807014181010301d100c2d2181c80800100e0400c46001c203510342d40282c41d9240e0b1150132200003460400d900704450001c9942c40041c090513202c02c01c241c403d0740c4450030400d0b00103031a158142e20300034032944001c1c1020b000107400b40e9445844a4140d80301010035489880840d02d4080030301d100b842c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 102460629 1250 102459379 102459397
    0xe0904030905040c0221041d010f0b07031707110607020f0601170c060d02030405161505090415030606080d030509030a0503100305070b0405090f1014040204050901140114 75
    0x28071240c1c140150714050744040400d14481c0100d905a1110302581e41d0102a210890386800e100410200710028151811303101c109030381c484000c01c81d0304004c0841d110b04c07198012200301c0c0d0300106a0004148c01540584500a0056100540e40c640351000512050548024100901860000c58145400061040c2807040c16101920f8545c0c02d0145000031007100d03a0740c1200600c111300b251841c0c1e46400006007000500c6201c0035030f0701e01d0603040207031038a44003051044081c29891010050300c804c4100104000180b450520780e030300104400280504904032005407100b04940d400010001140d02c608111003504041d201e40740c1c501070098084903800c9603210700ba6041041401000c41c8198021948141103054544d0030740d40708e0301c0341850681c4503003041490010000e424019403410444481c0d200700d202e002d0f01d0f050b00d01512000103051340c51240022003103e510070b18801d683c6039010790b4081c02000e0564a80341da03480341d210a010104c1c00d0720901040e405140603060981100454030740c41 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 102461879 1250 102460629 102460637
    0xf100909020102060a021e03040f05060105030d0203090d03051b0703021f0801260616020c0604151809180b090a020d0b07140307111c020a03080c0405030d0c030e090403 74
    0xd900c0c4aa174001944c448a03c40d0380041c140910605940d05403400f440c01180198820a00300205142c404e140c40c0c41a08031074801c7d404109241441c550002c12588801001d41c1d603002820403610382510140200e450301d0300741c100340c1103500c000c1ca00000f07002da0807640212080c60144188600d01c0b00c52071801c04034003000402d0480103000d0000110100e0107162802141051005041814507061501c10b54507a410320342030b054841d101590401601c800c809089526070700d42403500a40c000c4113100c51044c03006101c40c100d1644069162200a28004c2901884c1448605c83e110303011102100081130071540e05558501140d4400c6000441911140e40503114103402001625803011a810080c030b000100300003461600301c103004080103140581d03c02d8840107030110004841134104a8041448540300f42c5040015205a078001101884680c260804006944a0034844511441150001909403040b081d0741803001d548081600705003402075488401072030f00c440070882d500e202a54050001 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 102463129 1250 102461879 102461881
    0x150609050906150a200c010807081b0d020705100509060601120f0603030806270c0913090b010f0801050402030703110102012003100e090a110109080102030f10090902010206 76
    0x15090403501a500008000c0162a201040360f901140640c4510542400180d04400e5080e40b4031120b101c180400c011400940038502c1d809000800000c1c00902a000300650000400d242664500311b25820100c030701417483d0740300e2144500101030362096104541a105a5621070401030711841078a0250020601401d030326120b1000440d4014040100700040c3c40d950380442201e000184078450082d0b01c45d8407100c0079072402034100714000c1e0407826080d24409203101c0d0350711460643c8881039030014240108503141d24600c4003080090101c210f480380c2c95450420000d00f80b004c107548a0b81201e030042c3e0000c69603a1614042c60a0b02e0042c0c800035050f5002076030a2002503c0340085002d0340d041032000003146502c9074134408445004908040110710b00105200c041c5601d1449103001e0103030640d072006030b03041802c041903642001da000501001c1440506502603841901d40d0002046450020742d01c9043c00c64079107000ca81d0075503810f150340030800000181401a800f41c810500e405030080d080c1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 102464379 1250 102463129 102463139
    0x5060a03090305040f09090c082d0703020a0b090307080d050a0806180f0105030c120705090603120a020309040b0411090f040b040f0506090901090c170c090403030c03150609 76
    0x40c008150707045082c880f05010110f540040864100c0c000c0c241c0c1100401c1152050410b09000c0100780c01040e042c1d003141180420401175515034180895041c200000e80c1c0803003142071070409540da000254040580c2c0d02c0001c2c007408020142c90703c01401ca00356401c01d0350f42d03070401c0c0d9544403d1961002040062040343c1c1c40e24010103400b070384110054034044c01e0f0ba400c45402000c44004a44041855640303032700600c41303030804001c0d2240102007510018002d008244441e076540c0401d200e850320030142880083c4003901c041c00100360254a442c010b540f9144c00c9075003e034594004030070450249103000c116103050310b00381c01040880889600c5040c0742c070400c41c09000d1000c28035a010f50304a5202c516452040e11184114907619011050002d01c03428220200301c03807500d001c0d00c5072541d40e041c48012808103905030303285070486000c40c000c51568000e0652150800c0e540905850740010000f00304801e042e01504407042400c1161303401c011981c480000006a8550b500600000400301d035020700c0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 102465629 1250 102464379 102464381
    0x5101806020c010c061509060b031b0c120f070515010806060406060f03051005090a09030e0303030601050f0703020106030b01170d08090606010c05070302090c070c0f03050606011d0a15090503030405060a03 90
    0x1d09841042c0c030941b401c81d01c1c1c000200a0f140d0582c0700c41f0381c50f07900008016401403104d100c060451030b11040e503032600074058602c1c0e5540322800d42c04c1000d41400036000d03000c003996000710740c46198000250b500c0e401a08120b404061401d204202c001c2c0580400103030603103007605c10b807000d0326100c2e02c03400a02c104101088006010080200815200301d01000c281c2e9610010082e2003000c142801054401d03c40c03074010040f07282c40d0309141c0264414401d01000340e800805541c101907906840a8a80c501c80c1422409002c0303640c405456003104000108091a40d00d00300d0300b000c1342060440345c84800f60030086800200032038468120380c1100e00401d01941c440d414165805015904890426031681c0002e000c410041e81c0b101d8000e100000c001c4200078629628030000c081030049c0148107851522190380ba050010011410410904800304080d840348085140c00d14000d480110850303110f010504800a00b008100b0100355900000200c900c1c00200b10b80075100050007840c1000e01c039400581c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 102466879 1250 102465629 102465641
    0x609030307031a03011506030c030207110108190c02030403031427040207080408010501080d02060403090915150806090a0b0604121410140a06060c02100905101806020c010c06 77
    0x140040b480d14440300b191340c0c00d00911481c101403605c171061003864140f024040754030782d00e42a0140341c018001800420b0500c01202400074003030a140d203195032001040040001c907010100445440c1c04a0621069400000340c030980e84a40c81e08202003188204211203406a006100180c4451000980f02e48140311010b20117080f000d040542011810340c3c0b85505500a500304142c169074603c01080895410050000031076141c1c00645454205901c00802c0300c11240214140140c6a400f10107055a10202c8180104070702615003001c8505a0002440400250781203481440100d000c5a02d9034a20703c280003031146c0c0280403030301d0f0078a07062a840c0d02000d000e0f0195292071403a401c690750017106000f1551400d060004c001064800c20004131002000608101503541c0740c2441800582d80240000b41038030340444000544503000da100f1a000340054102c182c000766003400118010b500140300c0440d0307130140022041d40a0311481f04030b03a50503044405c0d13030016030b2101c214004143e0981c444 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 102468129 1250 102466879 102466901
    0x7030f020c0a031413060c0c050a1a03090a080a08040b0612031209010f05010b070510060b040936020f0603040f02010503090c0307151704080d0b1306031112060903030703 75
    0xc0c50504083c3c4840c8031001c5c056a004a0118110049031403c1148030202c00b0040c0108881301100c16013022040c108a001d1030b10254810440000440c841c403104014402d00c850340207441e180e56009107000105030010943d800c41e41d0700c1c1a080414020701d070040142115507440c3e8015410010410b02c0e0710842c490140c05d014045d541c6a0381710050008500540707010341029041036980e0303040c1d440d001e450810010720165610385000800e019000d550ba007142d045601148000c03502226106030001c030540105492900050352150845103070000740780303036002a40200e609840c40004001400f503030340b01c1203500070070390301025840c0b034015805680555000310041c012911000b040402107071615005800510744445000031140d007603684103803450349400d42400051603600302955201e007240200110441c03625103800b1200f003143c0382c1c5801c986203a01c1601e400d1084a0b86c0f4109032017101c0a0301803640c05440049040c0401190002c3d038240103814602c001e61559550b02000c034010700c0c1022003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 102469379 1250 102468129 102468167
    0xb030d0c17030405030304030f1d060306040213091b091d0c0d0507020313090c080c0f0d1a010f18230603270f0604120309140607030f020c0a03 63
    0x8462034541030980550b1143d44603100a40d0341e03080ca810040c0012a2244e003000800019007800d400c0113030400350513110100150b4141d501d03038844200107400703806443c8034030308040c030b22010000341c010454120a00354611318204441e15220160f00b29a40112405216910000440c0c04000282001c40031a07101d0020310b0a1820130100450a1083d14000c0c1c800d1801a84085961401034914900c280e0041890304020001c58030114400f03000110002c250345003074840828803030851f00450044070035a414408081046103000703602c021001c00d00310101400281604040a00d050166a1914441000c032a080d0125441c0c603441203140c24003041c0600e00d05900c240404a00d850703e20285000b15a900001c0d80d0350b411244482612500701c4000400550003031008480095021401582041c1c00c1300300300b021440e030303400c00750302030300c1d0300341000f081101891506407585d440400c41c503010f614903540c20300030280003101110990082407500c541c103400640d000400680102e052101410705e43d15 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 102470629 1250 102469379 102469403
    0x80a02040b0319061d150d050a0605040212010603150c17040f060603060f020c0c01091a0c07030b01060f08100612020d060b040f0906050907091a09030102130510030b030d0c 76
    0x1d900712001c1d411700c2031a900b800d124024004407017028110076980700410f0754603902d000882e0710340c0c81da030b6407403041d0107085241d4442c0401c3c1991500c5000c859100314840081c4165607480c41d00290804070320314039007406464074a0550205100da0607840913003a00c4020b5085580390350b26508213002d50800700719400e0f6943e880000008040303001300540094007520058540a0380a2220b052200c4164540d04100d650901884062005604029041414401140c0303a400280d07482e031600c05541c00140c14041303101f0000aa4039440641d80e8204402a62010740b00d40301d425032071100b100f241c007680001c43e40106081c5030140c0030f07901900361481c6440011641c44e0766058240100e078040c7d0050f10f000202464240202c0340caa00a800040006960317203940c500d0805402080c0700040d0092594240c104a0b44105075001d050507074010980044c001c554030101c0b0700030200c0401c80307403140c6801101d800d0410024140203105800d88440040c02611907a02d0600f421140b0342249038081302c6011881c9 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 102471879 1250 102470629 102470639
    0xb070f030615110c12071e031502091801050a06111c02010b030c03160512101404030306050303070f12110102041401020c060c15040f080a020d080a02040b031906 71
    0x42110b40c0c0103512501c507920400741c40d100c02400d280c00300030b90f44d01480d88030030126640750b0b0000312074046130012102c03998600300001078074000e41e56603400680105001201d0707a28640c00c13540240344020b01240c1ea11400300301420301102c02042481074642c80958030000b0042e142c040c501b1072079085041800e440c0180c0c030740c201d078100600310401c240c001030b903440181d201706083c00c2006000842c2c1c200d0052a001c00404180181c590304c50180780c0c092101118074110f03102c0204040600030003414408d0001d40c00c1070110740f5801008032401c2e80020304100f40001c0300c0c00d001c030440c1d1405400110b4410040c60645440105440380059801040341c9040c40e101e00e44000c1c4081c2c000b5000038100004000d503030400091505032025000d910858040103924100c1a0001c0e41e424500490105c0151a13a01c82c18400c0d40182e0221010b400c036800022000201c6501103a64540c6222a458542090b129281040c040340200d00a4202a44080022546208401ca410012840043c00100701c0c0c0c0d0300c3d0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 102473129 1250 102471879 102471899
    0x180b0a090c080a0507031812020c0a060302030907090603150b0f1c0606080609070e0a1404150e01050c1e0f040f0f0b0906030402040216050d02030706050a090b070f0306 74
    0x4100d848001040d15041c09119040d074080c44d60000c00c01d01d828011240039407046055013042c2ea81c001c0405401102e14010780b4000d03c1012020306005200c1e40500795100409000f030742c022940306819000b0b000000c100081280300e44d03030540b50070a0200304500c0d1000e045034002e044a41005070300800001103c01580d6a0b40505c00c0e01c3c01c800055000c00281074a0980c095508a82084081f60421403c0150324440090100c04480c141c0703040310030300d40b40d1505410040a1100104000f00401e00402040c040904444031410b003913440108603c0d011107698a0803030b807045d1003058102d03604100400c0c01c00000c5003451665540d14000c5450301074007101801040d0321541c02822508111501005900b400203071450041000000d00307460040d441002541c0c1c2c0c480280700a00c100d40c0410b88225103c2d45c01013214106600034101d400d100e10340350b0b001c0c0d80d0381c004274400c6400c0d03400c000005401640502600c1c0701c1c16031140015980e91034007101900d04603941040b1108040c2c3d110800502c0e40c0751 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 102474379 1250 102473129 102473141
    0x120204090210051309060e07051b0106030305040303080604060f140a0e090106210512220608091011041401050c010c080402090a0c120f06051203090415180b0a09 71
    0x1078030f840e5924603ca410740f4402481c1c0345d0100012910f09801040b050340c6034071415030f000c01240791099a50303107126904040a20320301d42c8a11650f1078140301204168201c001001a030340203840b84e042038ad40d20000c1005941d41405200f1101c071a18200300b003100540d01c40151000401804d000c08280c0b02c040941c9504801c803050f401d00c2e9110001081418003a9505064004401c0c20036040c2010700d44400c0d64540004400c0b12800078002a241e40704402240995029540e41c07a5806031203640700320040242d0010344561019001e00c1039200f12440c000d12a0085a6004130703004d0741003518201c005088440310420090500108000f82d49e0401c0e000c0c13244000300d06041d06d504200f810320f801071054015001740074072411868200c0500c0c8003078000300d129100b0012a900401c14040d0422410040c0c00103901103500300b012101c07108421000031015001d200e4060710300704044081e0441d0700251108a101c0c1c460040c40100e2114043c1e500f40c1c028401540c03002c0c000c100041d90b10744404044480d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 102475629 1250 102474379 102474409
    0xd05090d05010f06030b090304080d0e0a15020f010e0708100e03070b1006081b03040f11030a03030605030d14031501090b0f030603010b040203060f060705010f0c051806070c1202040902 81
    0x7948140174010030a042e588580c002c44528004c5041a04141801d907840743c020f04200c2c180032100e1104a981d650f01e040302400b815a0551080c018084140080d54039004d040014405500b41441183c0c03068000540c603080715411002044000030550a9400400c0420b400c6075050000700107180c04601c0c0c0001f102d01822106034003403501c41c03401d20010991400a003003541d10712105c90032450301c0303450001502e42254000c003200140c40ba0324a007443e6001084000d0540500440b8680d409043d01984008102c80c02a4141c807141d2103404001c9401e4014650312414820040c804604900c082901000240da01814055036417034840152900c1c6801100144111b041d0010070070800382401e020700e413581c0d2000e48043d030460821500144042204c850001e000b088003140c8407040c0b000c2504880100c1e246c6100c10800312071000e1000300154024036007008481005070007103106040200445a00c42d801200c7c50a946051669100d4030004481d010f030b92007901d414049016a641218a03c02c950f = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 102476879 1250 102475629 102475631
    0x612090309040e03120a050105061c1d0c0406080705030319020f070b0a0f170115140c06040507060c081219050c03180a02130203070c14060a0f05090d05090d05010f 72
    0x80c200841c4d4180c00f000281b05400541c20040100080d840300810340d040c1c1990701c156003042240303c480220040c44940e070010f260000380045a6029000441c403011222001d4805010458940c45804ea854451344550b070340580c03040100100f500c1800b5050045001c039441601c07403404181080070710b030042a07042004003110000c0c030b0318101900300801002c0b94050b42400400003c4401c1030081c0018144647c080d01018400c052414a10070002000540168040141c81d1703a00d0f840300650724501258104d070a4403c862020901034003130b14944080710b92203908180f40499140c162004e07041c0c043e006240c10b00005007000d250705194000c85104240d103440d81f80e106c0c5400100c203110342d40d0b1030b0714400850300030b91900c40c00b58445200004080c10b81c07860141c0d590301c07003000032607140303280070409040d034540c14003413004000c800708040f40910403d5a00340111140780245008881041c3c80e100c080da0b102c280345034a1107002e0000780000c08001015201e40d9141070b29081d096035500300b00340b00c00d1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 102478129 1250 102476879 102476887
    0x3190318031203050906060d060b210703020a080615040b01050906120a05010b070f080702010903020d0503190816140d021c0c02010209130209060d14041a060612090309040e03 77
    0xd603606101c4d40b0342c4054054010000c83c10658040313180c810042401506440d01c2e2800c00070191030320241183c000c0406454980c48600018005441c1e001c5800100d101d5081d00b00c001800307540004520740501c100b0300c1d0783c01000b018201000010705001c2000381c14070005202d9000241d9481024201003c500e540740c000c0d5207040580d000807140140c00698500009108100c041100d04003003c081c1980a1020781d62680030340010b86035803001e5400294002d444400e4542005000701c0501411001884400541e201d0024103a4100c24210382c1d0441c04103200390340f00c625500c200d04a114442d80d8041d0035140c031404460000070ba034400c480c0c101165861314001c444059107803064503158102d900c000c506082c1960700090411200d00b0024540e1900440e040019566503000c884c56210206010031400605070310f4103075000011a41910310500b9540780f806904441d40200e40306031130042c0344501e001380750701900c4140e15018002d003500b03100501040e03c0c07680381d9220b01500e10410100540e11 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 102479379 1250 102478129 102478163
    0x304050a021908070303030b0604090213030302010c0e09150f030d030b0f040e03030c0304140a0c0320060318070314070312210209030a12030e0f010203060319031803 73
    0x402d042000520b01c618554100c00c108a80000c42c150301503e41c1460080ba42c0540340000030010300894010b4100d0502c0020b1280400c00c0c4041044100c9120750024070084212200989281e2000302c5510f0f0000f01c18000623404041600c240b901006000301150203494041d40440d2528080784960404240e8520071a0014070307003240c8001d0400d00440701801490096040c10781c4900024151492019020010070204489269040d19004200041390300c0655641800b1a03002c03400d00c420f0340c1c1c4980080d800520343d07405000044800d20081c02d501d02e540c440000d81009444454440307100ca0140240210000e0040d80b0f001520a802e42c004160441c110300340f254074107030450002d1090005154040825041c141264007000c5500703080142c54501d15400300c3e090844205000780107041050341010202d0300f41d0300c01090514010704a07080b2802ca200011700300d120641d41140e240d40310682001d034061003660304e04000d41c0700f0700d0008aa8030301050409543d145940049070508030180c11851 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 102480629 1250 102479379 102479389
    0x4050a09090507060809030c03070305040e070513030b0c040314070e0f04171303080c010e0c01090302090a050c16050d02100908120a0b0312041706040201050f0c0109080304050a02 79
    0x40c0c490444100102001582e459a5a00c243d11507038060040050004541c52010b01c01d03251030401c071b0415655100900d2500903c81c5c2e02038001c41c0040d480040109034020f11a038295800703800209005081c2a0954581d11240103009041c000000350030400031000641c1c504030107100a05041c010100d0508188807031f041e02c4c01c01008110100d0101c010440400d020803462261400c484450780d60365440d080100c028000c00b900301901211000450818491055101884164480b0b050b1003076203440000440345411b030741c0b201070f40c4010410082a1850016404181c000f84070202d032a20b40b80e4101d06600c43c0b1303401c520003a56507420151455118940600c83d81c03240c2000d8800801c2801400e50341c000103800b80038440074010078000005101c41e4401e600064a60b038006084131898824524850380c1907015009420f4504901080c0c03030300c48100000c030140219070585405050031603001d10401203030000c1002456a43d01c031450b010102d100c1d4402140201e0007103010f0075214481d801809 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 102481879 1250 102480629 102480649
    0x140f0d031509022701020c040203070c030806030607020c06090d0605010e04060f050103020603010612060512030d0e030408190c050418060506030706080604020904090c060903030801060e0f12010f0e030405 90
    0x30342c21a00400c13a282c030b5440400080d855a01e40002204d03180c8107002c00403840c001d0310600c21504144000b0a20501c560070107110f4002c1842a5034096031641d4034070905031201c0059030b0200140e8040700502000c1e1034400c0c041c14040350041d1088000600c1c81c0c841106441d400e81c41480860100010b00c400d100381c500070081c500b044070302d0501880d499a80800d00a00c8140315010821050020000e11400d07550000c00042c1802040c2c0c080301d0f10401d43d465200d03400036043d021a0b41c0303400c018040302800481501c08684041c0e0207400000c1d00f140001904d04105003040300c01626500020850355128441c2d10000700c1d0544010b01060040e240010880708060803d510130f82c000d910401c1f446034409140d03648240b007580c000d1b88603e0718801107005807100c864000d05580141c0d00206400707510030f0040c000c40e4000d80e034995159a03252015140a5880079030346401c4000340040369464280800c110f40c1e0459260000949055000c1140b402c072540010303640000e4100003010000b524150080d6 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 102483129 1250 102481879 102481889
    0x10c081605070803130f0b0f16020705150c100213060e19050411040806040f05071a0304020d0309080a0309090c02190f02010207030b0a0501090c050a050304140f0d0315 74
    0x581c0c900415501c401c0201c0c00010325903810b03e81d840e8000710410141900240025a00051607c01030511400c0000e20070000c60b14006d10840e4210b08400c2244002501c504980000d024105280ca60500b80c0b19640d0100b140c0351030300e01c1009400e8414031100d10051002c00d41c00071404800e5400e00f54000c0601c404084058802c2c1c84980c0c0250728609110070040c01c640045800244050240001c80e499010b15402544c440c0502410002402069030f00b00319002e00c10420740380000d40b10803d540560030310f01002c902504051001400504007501200c004038000c0c113000101c15510602103182c00380c24a403c400040140808120b05031441c050b8469041081c0054130384022042a800305621002e070f00a0500c0410000d007800350b90082c80300f03001a580213001100a0314151710800c0c0585001e118003020075260141e2a10214403c50503605485981d0381c4440c616203d0361254002030b81d800041030300754082c080701d640c98240e0402421050384490745000c40d05a43d0300f012181d5a05003a80300c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 102484379 1250 102483129 102483137
    0x12010e01030209060d03200f0f0102040e13120e040b100c0209070e01020c0402070f0803040305031920030601092c01080c06120c07060513050c0103090b010501030914010c0816 77
    0x10b42170000ba0042019440b0703108422a181208802c506030b20329041502c3e00600443c0681c0360b000c828240103400500030395010a8680c4255107450300c0030312041c00140d5002c1e018203120001858060b100d24091100000c0060012890084540c0052420000380000401066035401801c0840c00d190340b1950344403105040c00c01c0201201c00002c0d403203180c2000f455200319070004040041120002e060001c032038000030001d0b124946442d000e4501d5005480109d10950b91a02554503450280a14078004081c032000e4440e0004c00c0d1000e0b03520f5003026201a05001c00705c940450080f140324040300074200005503140002c090070800e000d407084180c204210a4000301c603c4541c58990008079000070749450040041c0d580c80800402c60703400340c024020b2803d4141024070101c0b0701d2000c484814540218151520f0300d400c1c1005404903101c0c1d0070300802d000144801004503601950080c1a000d0040401103400100b500c0328508480d000500e4001240d030b001c040c00301c60423040b404902c5004841c20 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 102485629 1250 102484379 102484399
    0xf02010902090c070206040306060f03020a090207050a0303020c0f01050411040e0c030706050307050d0c0203180303090a03021e0301140702160b0d0216050f0f100204031a0603010212010e0103020906 87
    0xb003002c0e000001c01c012900b42c0300085400031500c0d0070040f2001580c01c841c0401c0f60795100e01a01c2071300b40e0707544001e91281c6e1401d107000c11a000c16100b1521201e90000040c1209411070307030b095000c2d40000f041100c080c006c2c4801c51486107001c0c040d442c030492188a03070f040c98071204800c11080710007458480649a01044000d0035035100015020180c1d140d42c1485a101d40d54030900b1500781c07044a0034480301ca0708207000f440103190004042d20054a0f013801d410b100300c0c514024180e1f00c0c01402c40a5a00002981041001d420b10360100003090f000c0b042c00310a400c00e45000b20742910403c2407200b80fa070a00798204103016905110078920340700c4081240b148545004045155070180030540030300f480d80010840302d490610720749401c003d80d120058807110100021803d442d4139602c107401c01203000e001300742481039000380f0031507043e6a48141c080740c059210100e0b94580134070040125405642c00c022500044070b81080690007400c494902512641c1180305129500c0030250480f4028580c0325 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 102486879 1250 102485629 102485633
    0xd06090818041b090504090c050d050f1002030f04030c05032101031209240c0c08060702010b060c070603051302090f010303110a020d060c020a0212150114101202041e03030f020109 79
    0x84446000c0f900d086401154250103420181c41d08d65899200c558030018078001c5104100d008188889203242103015200600e0840707055030203a01c011622410403910210001e1b0010b0b0050000380c80c0c2901400c110707410009090381180041c100d0380c13034100034040610010010021580c0e03c403240c50b0b0b800e00d0304003c15031a00205200400f010700a18038184060b480050440c0d101e4811250306075000081e07010381d990f5842072651943c4040d80c810006500703001d08001e19007420b40850300c100403250024140d403443d00030f0131402040054001d90948a01c150782c5801340c2e403000c03411401402d000045134aa54918070f400340c5400702501d40c20065411811094000d69212040c81c40f806811400214404a28a104034104011108029030040d000c01084140321800507500b04010541c0031403041e2640c813036500c2030f5064510841c507030303000e4040c00340007004920400140310f00c4928000b000d03080c240c55102c4402d001b55034441d000c2420246100c10828913500103181c3c800003186000800c9024669 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 102488129 1250 102486879 102486887
    0x22805100627090b07030e0d030c020c150424080702160506070302030c0105150301180f060b030a080a17070c020307030209090a02090f100806090601050d06090818041b 74
    0x300c0642d00c0d20744030003645015040c2581c0290080d80d80c000c864138501d1900d864060024500e044106181c0d1094041d030034070960003845600c2950101f40c00521040385501d0400c070111981e180d6203a21407106110000d02d00302540503509880d07103000c4000e40f4900c0342450042401c100280f5400071580b00845180c12600b141031040107841040d2840f51f990403a0b0b05084c0d24501c10504080389a42c078000400c00001c1e8200b044520300c0104800a00480c4040300080c00060100b038000b400c4090100f5030040020341d00d40c0148401d44001d0190343c80309040303845880c155044540131101090a1410946d0428003803015981d000c20141840d0b40301e000c441c0c010aa50b4801070100134010110100400c030f82c0b800030010042c3c5150700801503401480d00136039a801c0c583c015291011400a0b0b00c0c404101c59002107a11886840c040006140580c41c00c4108491101c00200c280e8102355107a10342e0340440e030700302c0081246000407a6411045403003007041c001240d680750b1280c09088100340d011040d160b48 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 102489379 1250 102488129 102488159
    0x3140705070f080909040b15180c07030903150203070305060d120c0501020d020c030702181303140702040509150903040f030303050606130806150603040f030f0228051006 75
    0x100c0710507110b1440c500402103119101c5540d60200d000c508000421070040c24031071080c584501c0e0b43c0031400500c0e061182c0c3e4000703440309032034480720702c0d001803000c603204406000d825010749051031a1b15901d031141800013113054844203841e500081000290f58143c040c0603041481685c1c990418001511480b02d96008454003604006100003103070700b484002d406407560700520140865803581c0c620000b079070701d92001908034001d04461500c0710301031190032000f45c416000e00d01d110844502c559012101c0b00088010b81040c010144070400241e111442010300c0381c00b0010081621400e41e10994010700b1380184044147c2d4402c010501046003019070840840b80e25040100d069103904000410030700428900301c0c061040c2400006200e080090601c1c011504008055503641d250000d01509100c00c803005080c1d0003c1d548924006403040a107681803a11610680e81c14541c201c6d151514056480809050110401301c0c0f4800d000003070050743c85170402d2070001c02500785000f2116a24650f = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 102490629 1250 102489379 102489383
    0x1020070204051008060c07030201180b0621030703050a030515150c030903011112010e010302100e0d021201050106090503070f12030219050102030708280f0902031c0314070507 77
    0x14607900410b10310030903840c03204090300c003020945d0858904100d145c00e85800c410000d40c015800c0c007c0d80500320a400240c242c0540d0000c034081c8850340c1d07040c00e0002c1851030f08035800001c030710b8841d50040c0000500290070303000d100eaa102d43d558500c081b001419201c002e468903d80005030b40074000c10740d4401c484401d2078a0820200c58031009281d4415085015543d041c0e0341550070645000481d0071504003d1402c005034048801c11640c8414100920300002d00000f504040c0c11612401036038001c10f1084000b20004146440d26110395010800c0b04054001d60f0070303030740c2d1107038014891150409850300181c00150014103215240c810307100c0d000820782c407803288014600c201810a0510074803040c880c0909075000d501c5400340c0d03450403500070360040301c2c4400011080404034080305820310308903d90303445c10f13441c45240c000d0200c06c0c600101244c0110701c4400780d07110319400058400b401001030380401c030a04c010029940000150070303076081000008110980204000a994004068400d03403a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 102491879 1250 102490629 102490631
    0x507030516030b010e30030a170c041205060402040f0e030711190806060123030406050c040515070605060117070c0309030b010803031608010f1403010b040903021020070204 76
    0x41416401030300e0790f03148468501c2e0040a03048131180150700da41e80b4924060300c00c6e0641444640c0344080d541d00e074000c928081001508411b40203003400c20802c0c41603000304040c08400c3c44d081c1d94020242081002c1c49046a00d0b4000c0800c1000f9482c0910641c00c0c04000c140d03041c4221464007800c07503141d100e40400209108200d071000b03081515148000019905480c004401550300d6040150303a80708d0071200d050000b80144601078040301d076081d0700301c641001000454110380726aa5441c0141038001d200c1e01c03020009200000e00366131108945100e42c0061031070580d45800a0629400340c2c2c400a2925042c051500c2040302604240490f0300d900c8010342c03510012000d00e619046030b5042d9103a1000e0103031159000041a41c0d00b01200550007807102c0412020311070718440066510800134450100300440401f070410000040340343d080c06c1540000c00010f080044007000804441858100798016840b4500c20120561244a0308100b40004515990140c1440250382914810144024019 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 102493129 1250 102491879 102491891
    0xf09050a020d0509150601020d050711010c020604060e03060a0e0613050f070314060604090c050d1a01030309030b010b0c0703030f020c030a05030904060b04120807020109090f050604050703051603 86
    0x18140e55056031104440508140410b081c481c00d81603030340f9000032102d140070442c003022a441d580002074403403100e50184c9403141480c27100e48400f54418100c80c1001c0c180100760841c50016900c00d401070000e01708039115440c0c102c840c2c0e4140740c600200100b005c042c05240086100020700000341166004c54600300c543e0400c0b401c3c0c513029042071500201d1140da4460b080780441003001951307407100300a0141c03086402d01d41c1c50740c082006444901c0300c0034006c4603144200740f21a003440d0342c0400382c1d035000d90030b080d01cac419000c034644002240c01d0f03200350000f03808541c040c41004000c5400c00c2c01403918081e41ca0806008401d17454645001e484002c0c28018106030041001d4002d0000003018000141614400441070a04545030303171000041e0b0348245d02d41007000c10036101c4941502c060b0781c01342000d0300c805807090f0303582c07d6240e20441c82a410700813018000545200755002d00710f01c01c5110100440c0030b003400070a01c41504c00140170001414181401c00c0001821a402c00c540030206107004910 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 102494379 1250 102493129 102493141
    0x160618080109050703081e070b1902071a10080714030f1204091503230105060402041a0a0908030309010c12090206070303110408032206032c07180b01020607090f0905 73
    0x100a55040c5411140070042200410700c4001c142c01c078481c0e40d403a440b14440c04007a804002c100d100e402001898448901010781c503004030748140c55440b11480c3b0341591015180e0700703c40e14104103907018107084e1740c040c001060b00e0b00f001e100d442014640d0400a0481c000c1ca92820f550383d0060b401459540d50303032901a001003031900d41035080151b03004001c00034042c28040290310031820b40d07074260149609001c0450070908151007194220f400f82001c00d104c862503040b080605920450b00d031410809481404141d5070700c28030084d40200350700000004c030300c48540380c098401000d030003400030f1031460500480096102d1001321980c3c950306140c00110b00c07001a030001030030f000302d800800c0148004228902410140302c9010807031415801c41400c0c0a035110300c1141a211071030035000528106007845281a06110139848008030b9260540c2c01003134072552422030088480980b0b401780b544130450b0742ca841d601807090342d802002c40e1405503038440c10038080f013810400324800c184044d551000001e04c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 102495629 1250 102494379 102494407
    0x3030a05030411010527030706090b0406050f0d0e0a050c0603010b03131b0b0a090f050f010f05120c0714010506060301050f0a05090f06100c20010216061808010905070308 75
    0xc403120302c01301c5a00c0c0040b042d01d00c1220f130481c140c3d485007c1c0c45080e0300405d50900800d030010803160003c486500c0c01c0e060036012101504090149003907980240110704081d806401114400c0c2e001d18000e01c450720080c1042854020740390641c1c0d010300030400060184d00c10441c100c0ba0b102c0f105406058040c00fa500d4101c1c003600b40003412402c1121000d03c040340054085005000c0300d0000c0c0c1d10b5190207a00e407100f8014001c0d4a2017496804052440c1c04005540200c848115420940c01e189081a1101d402c50b84501400c488a02c11603500140354402c00a85062440d03944020f10002c018600d00403001c075850340b00c18001c0e184540d1200380a061156904406400607190103001e201281c1404c21a80070806415100b0fa41328100d01211141c0240c8038407250f10b19590060700820441d00f4482010740b2000d1510f514504501036252414450301940c0c41d04c03001054243c2d5030005e84800c58141d05d1080d600c541100105904010120011810020315402030741d8000c00040d03074869080180d05 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 102496879 1250 102495629 102495637
    0x1061703070302070b0702100c020d0203010c090f09020435010c090501030e2406040914160501050a02070509040602120f0603010501050420030a150609030201020c1804140c040e010e0c03030a050304110105 90
    0xd614ed800e0540491341d00d584151030030200c0301d21340c40a0030043d8803100c900080e030007103010b4111070f10b04c0301d00c100f841c50b868002d00c008250703014448100184031760840603094035004406000820b286031401c0040703581c54070600c68480b0345240075103040c00004450003c42c090485a00c1d03480720240002c900290703503030b601c1b07043e640ba442131041c41c480041d04415030f12100d800400407030444101c80009072650088044032130041080d80074011050601e020841c04c2a4003038000d988055007030001312155000c0c1c1a4185c01101405071003001840c04904040c00e48105030803c41c06541850f240824031845010003214481e034910503e516980c034881c10000500700000c90240c14809040e000030722581212400f000e5078000e07402e440081c00c8000901a60f492500c5c07840790b40180420020300460406540707184e00c100c034601a6645000d004001800b60742c40c4413501512030b55a0307168244010410441254911070a90185050450441c0050b00030300004201418402490741b864009a21440c121 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 102498129 1250 102496879 102496883
    0x5060a140d0f03031b090509090303090607081308070813081f24030803070207080303060a05010302070606080607050903060a050405120309010603020d060c0e040b0307061101061703070302070b0702100c020d 91
    0x4614901170018103102d003034803840b8002d41802c0c0204800b6940441228450a605402042203444620003100d00d0b040003401d100302c521044191400080b842e500501016000786c42d40368444409004a45422400c2e50104609921031498505a04480c821524500b0010040003d64010303900347e8408405201c070040d001c0c40740f90080881000800000ba41c040d04041d400c0b901d00a0f00d56080075560b00c41a1142680104140d02c100700031341c40b9400808510f4071403440070030001d41c1e49006500c0c0075000c3da03581020a60110700c40c0c4071410200100c90b803020028006000504094031850b460305400e0340d612100c40300005c00590a014250046002168040d0048c046d200781d42c01c1c410010301ea1b1100100000b010015401443d00d01780c0070351181c03414028090810b4515151042c0c8a810300f102c3c6400c0517549400000901d68268000e40310110340400146540e0a084e1074000d05180071500105402d450030700009000d0b8a41c0403024014070083e042c0680809400d00010b02d404002841c0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 102499379 1250 102498129 102498161
    0xa0224090a1710050402011b020d0c06050c0111070f1707050601080604061d060a020d0f050411090c120402060306060705010c18050f0105190e060d05060a140d0f0303 73
    0x40002c210802c80042ca40009200d4250349075440c407081258151401658040c4c001806044044449407405004200302d03440103100100c214000d235980419080c03243c5c420b20100d0340101d03038502818028000c80104c40c1c4d40d0212a894404103035104510016000c1000d41215031042140342c040b08803c044600440d00305044440541e59803120030350f1400121030440710385041022100c02d0703103024040c80003920810006091580d40750f00e0364000070f40240344030b00403807900d0300c0d00c10058900a06c1103a0256004d120b01000b1941c03000184045a00041c29144011000700009009800c40c501c1454019034100e981035542d840e07100004015000d4500d0240c06546480740245417280c0150140202d0780f65500300b0b0082d565a01c0c100500182ca44001501041c010000a903007101998044d142d8250107003001c071000801c880100d031841d0000c90801c01c00940d148107010f4a840c1c445401c2004024080400715038900500c003243c10541450300080140d80415011020580070350483c0085c0000482c1c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 102500629 1250 102499379 102499399
    0x30708032101060c0b0910090b0406051f15020a0804060c05060601050f0a051b07080a03020118031202030601020a02091003020405010e09150705040803040914090a022409 75
    0x804151a680020300102944162100c110075407814002aa412189162130300601c0c8015500c41c03041080c0300920141c194040d41c141400b9100a5110f40051a07006440300010303494186002011150040c0209a000303000c194400901e51440d01c0d6034050310100b0b03180e00c40e0140c0d02c03d01a45080324001d801010301c2d00100700410800c0d4010407600d00e0f18010811154291920b100556041c400c008a201003100c042103c0e80d8040c0c085c400030001c03010030002d03281c08a500032900d1800c10f1440e400802898006040ca1014103a0901aa00c042452040c405400da009541d018001c00301d480345039040260003000080070f42c1e0003130002510641e0060002c503510300c1c00c05400c00c440d5070b850208038403480c50000045401103624018a00ca00310b0000201004244506901d417030420050081c001c002c000c00011030700d00c1d400d00c090300013098014404911024050144902c04030f00034018940c2d94001ea00c84030162303840c09078a40ca8841030460702e00c92046845900c2d03090384079485031a504003107401d03 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 102501879 1250 102500629 102500639
    0x1b0a3210050603011406030607050903120325030b010e130b09090c010908060f0f040c0b0706020403020f010203070c090e0c030f0a030206100b030c09040b1f080a090510020d0b0307 79
    0x381000340b092004800070410444244a1020b00030700984495426a02143c0042d115900590043c20b14a0006044450000d9803261020556004861003070360060403018100503030010300582c440c1000c0300d0a007400594520f5000800c52404240640c0c814620b0400f02400b0b20700c9a0703c8001440c1018100005d00e19040c0f4590340d43e000341c6421280011960708000800c1c45000c00d41034014034042034800303100e45542062101803480940140c80801d41d010b0f001a03807000c0d48008000c0141f00345030260b01c984c6980100a030110b440308146041d0f4208100c040000b900021544003501d45861000959090b024a140d14043d0700d0b0740900d07003600c1000002000e82d0000030707002d41c40502c01d90884125070307a1002d42c0111500d480c8100914540140041448980d09101030140c0d150003420015580590a0005404013a000e8840c1c01c900c1004410b40001907208e0f09042c3d02000c180814810030304141d8541c0e540d58996020400d0181e0701040540300c0440350f401000d03079814028121a070280d291 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 102503129 1250 102501879 102501881
    0x406060806040b040314040501141b070e19020301060c0f03020120070507090903120e1011090301110c0a1407150906030e0c010915120203010b1b0a3210 67
    0xb038800f5400300344400e18948001b84880c08882c1600c0b8107039140c658041000c2a14a115085004210007c2001080304044044104001c0000f0482030309a4413040c14040c06c00c1e043c1504160713604074510b00410040c0112504414a400c90581c400c1d01d03c0c1140696060490041845864100355811b20b403600c00001301d41d0001500c0c0c901e0252091313446c07103560303084040210341035800c0c018040f40c0000008810607000b036010f000c4600000301030b5030300c55900f402c0c241c0444820700984800007031301050720340d00360500f4172600041c8c800171400740386055003034012143d486104050060821000000700000e1110a024002c01080400e03078034903c00003c5a0003800890240c00b0301000030340f1b0f210700c2072030341c241c0000d1403809881c06131910700c881420031031002100400c180f85401481800d000385103401307009100450092004040094aa00e0038803030480250700302d03a1010b11541d10000720107000c501e035444a02c01246401000400c4075580c008425503d5001810b100c600d40264a04040300d40c4607 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 102504379 1250 102503129 102503131
    0xc0901030b0a030b0c0703030605090c04060215010e060d0302010b060c01140f16030209030c12010219091d0402121005010f0519090f0e191a011208030406060806040b 73
    0xd8034107205400e040014001000c0c2c580c800a0104a40745002c00c08200400004101490280c84d01007940398465001c100140750030350303842c000c121000404108042c2d05001115900f100407804103019494081d040c0000c14015201d180300d41c4000104404240c000d5220050b00e000151003180c80d060608007803402403108440240e010194000020004504014458466806061010f4a0005480085000350416522250144242104203030583d07500749000010b04469400586c0d118906401140000618107200e81440b1040d0b2081c00f061001d203032114055201d18080348078580e501d000140aa008240702d8031640e024503025401c03142c0241d041241601d16800070003211a948005020103141c10303100ca8805000186070074007031003c00d50012195940004408580300749940030140c14241e2155110014800080707a03c810030138038028030544000103040c04a45580741600800d400c50710340301c00406038000000000d0030001164081405801070b0f0040352224030b820301d071101013840 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 102505629 1250 102504379 102504397
    0x201020c16030c0e0903070303020304020f0d06091203090203030d0f1e0204052119140106090209100f09031502040906030b09100b010e091915060e01020703030806011b08030c 77
    0xc10380c40c0c003258204e00019580e00480407180250b242ca4285c1d04d00720020b400180040364051082c00301c0c003c55136501010302c0c800c80d0003007034009188890391038002d040c150047d022005040c03c00d03c1007005a540401030b01c600c985400c0000c00c494a940e42c10100411428a8500315180120981c3e01085d140c1d42c02380042d01d4045e40c003400110201003038105c00c020905a8a2001d5200d07030b81081d41d0141641c4000308a51240036001004642c000b00c1c142540c0c540e40203849499070200b1560040d10f00003c00103201d1085051000b01103d40350002040c05005000140560181c034032803544106495040300d00601805504120b043e4403464041390440042d01e10801c140b046204c80349000015218621400c0e005031640d17601310100006000611100600c050107001034445520b28440c0c2c18081c86203001006c1c400c0e420b44034100b1201400f12103007452606d0440d841124180700003500620380503041642400c3c0900009004288902841090031006010b200b004c410300c4642243c441c00381642d40 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 102506879 1250 102505629 102505643
    0x50106050105040b070212070b1c0614030715120c05040e0a1103150103090507140112050106020d080603030705013803031e0d0c080403030501091e0c0201020c1603 72
    0x1565840111150300483c05542d04e82c001c104084030061818203e02400c1111a07010f039810141e48400c65026500b0422004009600419410100a115214070805403019803120020f0781b0744813002c240d0b1408180036500e02842c0000100f940d80703018499840ea020310902d824030a44071488001002ea400a2062105519101c004107451242074083c071011408261490b074190341d0382c1003400e214050902d00340d5052603629101500852418896007018220314002101c1030364006000401d24a441091040158034240049c0262030303002c18803aa80c0409460900101e8030b4400000781180300710b0034000c2c0203601c0d0101d0302506551402c260f82e50aa140c0e621503180000b018040c074605c1410014280e4180c008000c84603081100f024000c1e23a1020701904541000e44072031058044400c07a125650225000d801000201503241c040c940c0903100da020f080c0302451502c030491404c41c11280c1c0f80107800c1e80715010300351024401d60658400c805094100c80240d481c101a034103c503c45400291150 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 102508129 1250 102506879 102506891
    0x1203030506030616030506010e0603150f1e010f140a0315060309030801031e0203030c060919260d0c0c060b030c0a0905091203090f0d0809030406051806030c070501 72
    0x185000b00d4007500c11144da8103810b81201403500200c0041100a152905106000901c90910707125900514031945a4404100140d04c084040000e05805075982c5446410103812040f40440503180d818901e0744203081400140020384d4040d24590150503084803811404541a080c49505800c9103054a000c0380401040c5c6850319022800d60b10003c4000e004140040010000918018204e1f0802020044001c400020701c1d070009003981c0c422500503c0b6035205400b40034207910144544250320303030140700924080203140d8544400308400c00c0c0760101000d205921444070f180e80c400f1900425840f8904000e1116441c070007612064241c10261034840c40c0030f40c0040c1038100000d1400c0c0c00d03100200401200c92030103500301c000e08030003082c0030f009010f040c010400d100f941601641c02044050701510328284103007182c034900717810280030380100840c40c03043c000da445000c803c075410381e07080b4900f50b580c46245c00f80030300c404c03140c2180e4185c00050020800c0101541c000c00b805081d80705800900503 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 102509379 1250 102508129 102508141
    0x20d080316020c0117060312040b0a0914180402010e03010e0a050c04050106091a04050a06030606080a1406010c0f0203070312170c09041d100605041103010b03070804140712030305 79
    0x3e18507041400601180183c1c00c044804000c1e010301c0c503440031004003100d0041c0c055410582182d002584100f0459002188030725905401503a280003500a140b082d184050000c000a800184070001d03c04800502d00042019a40b08007926002d050015000744040c52184501d40c3c0d8800025805035014010401d0300d42c0546410302401e0b0403504aa0b551040c1e187c10603280040607810040000ca81c010b0170000001c268a41d0183c200040c001078a0000d076031440c100d03000c0c000490007046580e04c2450700601d4848003000c00512500480c0030718004403c03a840341340002c0780b203a101d8000395040c400c4200000400100040b009450038242d034403040c2c01381480c48120325000b07003135458110140d41801940180e0804c2d5101d5a500b0076018403100b000c40301d00c09034508256076a040300c2d00d084c0e2103002c14001420140503c02e904000402100d00e10362400302c862100c1d001c050580400c01072200b020405105408102c40c12501654047d9502c0d141e40e108480000f500c00801180172030f08280000d51 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 102510629 1250 102509379 102509383
    0x90f01080c04090807030f0504080a0813080d020a060b1507050102030115050a020c0f130c08041e1703060312040e070909090b0601032a03060302030c15070807060603020d08031602 79
    0x1d0f0503404003146040c0003456030f090307801c0040ca00c000e808100040c0710002d005103080010b80c0c2454011282180d5480071025075403ca5082500810a940d00c813a55010b1a90703800900c6840e11a0042e0b40001c0c0c1d140c10000158101c108000b042d030340c2183c04580001171050640c0110704031580381488030380c10000500d05a40b60f000c4c06054002580120402003900d05210144011000c0b00905e26900c46503640e038890102c0303d6003000c480004076940108010401c48e401c03a000727903103000500a1524481a40c44640d020ba0004085a020704040045120360302c04000c12120003c07081c41441c2c803542c9501e01c1c0ba001d50401c0321100c001171442d51001a100d829881a0848660032030072480d541da403400c0064000c1d042000171000541c01d07107151001c00e1000d030110514007001913900403441919600402d490102090581841800c2502c2c001800729001c0044604031903000701d1040d25035540d810904000c119507800030750007569054041c803c009049001714070603070501c4820b40400c810315404903 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 102511879 1250 102510629 102510641
    0x6060306080c0f1f02011404050606010f0302030c0f0f040302060c060f010f050f060a110d09060201110f03010513020c03070f0614060306130c050a06180e06010c03030515090f01080c04 81
    0x3c0c0c0c010a800c080d00c05a580900c0a01d00f0001480c00003166401c0010401030050104940580e43c507040503040c010340d9a4031108500300045640341c10b42c01c41c2420320300c1c01801d01c1801c0c80c0d10710107440011600e0320340c038940c6c0c10f940003150014032040d120520f808a850301e0301030855821850801e00c80c00400c03416510412182520800f500c40c1c2d1820880109100e5203601c1040d402c8103214842c9081c42050301cac01c000d00341d80d994450f80c422040501c3c02c600039094070960b40810440e1a0184100940e0703400c100107032070444030210b0f40354000300650745411009220340c41e8540c030b443c000080d00200b40000c10342ca1a003a548684e03010401c002103114400f00041c42a945598141c01c4080441d4100040c071950a030b6090144810114503603031203001890101059004d103020541c040d0f10701c3c10742001c0001103c01031803144e01d810020301e4480002403404400b00002014160794202140c0c050300a0000e428030000b000d03002c01c0850501b0307664025001000d02c40d02c0e07400d02c113810750b10401e824140155 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 102513129 1250 102511879 102511909
    0x30b07020d0c120305150d150c1707050a050d0c020c1f02060624030a090b0105150d20031005040615050318010b090f16050304240b0406060306080c 65
    0x24148402142a0483c003030217000d46060341c030340103e071000316039565954102c4403854481e0351704a181d172045070a00000d55903101c00250610030ad44540d00e0041500c1d407e12a0f000099262085c1da46101c036400340d03014050b02d00d030210403500d4007114101440d000108000985070498460842040c0c0d8429003c2c003a4030080403000581280d0301040c00350412184054840d42d007941a0300c00c00f00581c3e100746050300115120b0318402e8407180703a0f50621802180d49809410306036486001c00441e002c03400c0c09440b64000640e00c2c070b03941e510b00700001c003032083d654600e01c8080d1002690341c1c1440221090252840d0240512492910303100090140c4142d196070345941e46a16071500b1955110021045c0c1c6058150100c06952100840b480980d0761125182c8074076000c6000c0341c02c40c10224540c00d071507815040380ca0288441002403201085000203004000d0781011556039486d0100c0382c00001070302c0c40e2002541c1041c01c12002040301750b01900140191540c400807a1503011200c1c0c204070400074205c1d92 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 102514379 1250 102513129 102513143
    0x1501120b0a0c051206040204120b010e0c0903070605090d0b01060f020d03050610140f030f0109060803040303120c11030a030903020c040c140d0b0a0311030d1d011b02030601030b07020d0c 82
    0xc40c80a80c4c481c00d1000f6400f0000a10050900d03584500104c0180310b130b04c5d0221110a400ca00511200c20012605504045540403c5050000c00408240e071400c05024440501c0408a05031800307994456003240283c0d07100c02444035a50303540d80c02418030038040750a20003500443c60740d0310520f0300c24401e00d8841c01c001005901e00c150200d00603141442051600341960004124890420750a000114010049010f9210341589000000d000f22002c0e50800421500100002c20100394480c0300f180086024003400110300b00440b40503904000300d014903407010300010a182441582503481940502c0c026003c0d101d20700e030f0f024100710885000b244102c0101c0c81030b424821900c0c0041c006458102e085030400038205100c0c0300000c26603c0e96a02c12134444103104100d00d81070509101c2d889800c0d0840c03c060f1038145500c010544101c1200103030f40c1c100200003c8030302c000d4002e5052240b0080d0080d0a441c4956140c0c20400787c81c04044490a01501c920700c00541c00078410b8054240664100ca4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 102515629 1250 102514379 102514387
    0xb06040e27071203140c0703050d03020705100e010b030a030e012604060914030c10140709091a041508010c050c0a110f0319020a05150301050f031501120b0a0c05 71
    0x9503c00807001c040066040148082c0ca403220301c0c03402802428141e1010340181101842c41c54924902190088100d08040c0140314940008800080c0311942d201c203000082581203807080700d54010310404260503418400c0e01280c006142e0004205e658080d03003a41c909140d0b91148903c01d50805040341c01d0112071503418001000300c0c0c402c0c0e21891149110f541008024681c0d07115943c6181c002c0d212a40303140d00600144442c19000b031140803460b13850040c105005192081010742206120b1189079000340c3c96140301c20b01c14500312041300d01c0060003031080080d81503d1113030050b000703110b026854556207450303c80801c1a01507000d90704519005002040c01c1c240b03d541c0c24003a6070010003515045000302d0500c0f1500d80d814481c0380c414176101258036280d042140100552007440354071040c001c20740500d4403424140303590b04403815501e06640c400003e07010940803a1525482101010525100e00008038103c042000e102e20418050741128031151690041c180454409039005404240b00300 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 102516879 1250 102515629 102515639
    0x80109021809040c0e040507080d0e21070b0d060305010f02040e180109080304030215010609050a030b0912040b04031a0c0702040b030c03070b0c060a06050d02010c060b06040e2707 79
    0x15445980c054032413000d248060741e644000c0743d9058001c0d0740440302504980760074040305000b003000c044007290600e0503050a00801010074a03900c2100000304a9802d4907509121b0b607903003040540d008006081016a03a4000c409280c13008000c207020840d0070354200b00700078203c101d05000341c90130344803e0135a40c2420b8440c071954141005011101d0b0982c4d5480d4804400441c4091001c0d5104074000c3e000341100034144500f000d01c0700340581001c024064a20024019911038000d00300031317281e002800044a171140401140b40c401246012480314400140c0407a50901c1c1401400440307108219030078011007002120009080c086a03180c84030003042c0460303002740c03500e03400c0040c0407003000c0c080e05e2000c10014040703820b01d2000d40000e15071020025144050003410000701c4e40c0700044107410803125042400143ca03140c00e250010b0304011241406d1001d0100e640c0c4070100310741c00105401e6507160340fa248003605c464215108107841e145409130300f01d40c420034400402c1e5490100b01400000d8146 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 102517985 1106 102516879 102516889
    0x50904050f090304290403050c01090b0a142b02040501020d02030306030d080601090803180405010e060a050103020a050702030a051509070f0e041e0b070801090218 72
    0x140302000420800030090300d040d00d2400c3c41600420b8440c0c1040b010240000145149001740000c00104005d0005090502d025080c1c8410001503a1503030803030403034000c403e51640802c000070b44948000b510760008042d0295101640001c580909066800c1d1840c1c00744070a071000c0c1d00103800d101a680401409011003c0391006500e50310380300740440d1700d4a2001c183d9005114242d0003280007a07014140d40b00103001d034003040780d4a404513050008501c00d85071040038001d901e010004900e001658840750710502000d080401d40c240340c0f44c0114029409042000d08000c410300c20b00006035824054402118020390040903403c0c500d6200700c40701302d0054885440c41d032143c40e040151010a040185c2148c641c40440c610365078460900c50341d284006021b40d6110381a41040e44100480c582d00e0f0750203548940d07a2101b1380d03070302c50007010224458140c0d40000c40c1250301000c1d00a14003 = true := by decide +kernel

theorem cover : BRFrame.Cov 102338129 102517985 := by
  have h0 := BRFrame.cov_init 102338129
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 102338129 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 102338129 ≤ n) (h2 : n < 102517985) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
