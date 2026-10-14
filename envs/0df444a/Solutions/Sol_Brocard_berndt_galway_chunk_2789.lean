-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2789
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:44:48.809363+00:00
-- url     : https://prove2.me/submissions/1a21438b-ff23-405d-95a3-f008d9604b21

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 501438848 ≤ n < 501618705 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 501440098 1250 501438848 501438869
    0x7090f0f0f0603060e241f060302030108010c05070b0708060f030102070c090f15060509041517010e010c0f030209030c0d121b0c09020705100501060905120c01140a140f04 75
    0x24841d8017140400e00c4035001c0d2994000710f628040c911079a104e00c1c200074091800d050010b00303042c3c0c0ca605074003a826000f441d0780d45003d80c483d07142c4031280342150080c5070404280f00c420052000000c030389030101d0b544801c3c1c0d4180307601c95460704004550554a90704410f901907100081d201c00b403003139020810007180c420540070311061070000c0420007580c0c10091070038501d010800050081d280070f18041c0c600d0f243c001e000010342204800e16140c40c407002d64013050130318980002c401c12100080c040c28040c125200002d00c41d200018500801402c55a0a01820194041030900c038980e001e110140e420100100b002c5500182828005d8a10303821806a50200700b03030b0b00945030002101e0314038600786500481c244640500d030080880180d400060201c82e00d0140c0b039500190052544129800f901103540c0724610b060602e420b100300f6201d031002c941d07160fa10009007024140c1c0c0c41040341c800b5490a00074603071102e5200c641514820707400b24003408160300209180c44c1c4083e410000d4000c6446074030340c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 501441348 1250 501440098 501440111
    0xc030f130c35150703020c010515100f081512160f0e060d0f050a02030f030904110c030d090203030d050a200a0c08161b030b0106020f07090f0f0f060306 67
    0x80e440e000c9105074071014102d403c03510408498440242c0c00942c000c0007410301502e0304c40c2e02e101c16802c6410854000a41d903221202d804a541002154400d10b60b00c00e05003031100001001c000782c000600241b031024850000703400401241c4500021300094842401160303100159050100c000f003015005040b40348003c0c2c1400115400b4204c450390013404c0140c0510081d41f0f03261504d00240210400c255214401c18244100507101003007460504201c0c0006161288050700422007a5501089566100e60041c000400522004000c5500c3c03c00100703000901218030380b020900394068040c1219040c0cbc54113041001100b10f42c2c0180710400354591144038500061000520385010312403201c000034040030100000100d04c20000c010f40140403040c100001040e694081051889500821300804140002c00401c060308440300d01602d07841c0040d014030b5001e03103c00c9544644034403444102c10b447ea0280007004e0b0441d8018403400040400071301001403101d401c0c0300a01001c0c881118080e19000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 501442598 1250 501441348 501441419
    0x614060a14240a110a110f0103062327010e090106031b090b0d030f14091210060e070507030c03031512050601080607120504140604050d020d080c030f130c 68
    0x1e02c05048643c0004000174510f00c1706c0c00d006d0011445083d25050641d0b40703a003c074504030340103840c0c403e60024003075a854243c44101844120003c10081039040c22850400c079002605c2c0b2158039040d5562a400e078406076030380600311382c0500901d500c050940b0000f81840007009100540350303000d03580701900902454a44d24140071607001d500c40d000d030000d143c454031024101e10a8030000c0190343c210078541d09007480c0c080000c1040c0c001449440c00781c1e000c0741c0408000d0f0441e0003040020b080b050503201c1d01d031a080d0b6000d852489120f000400300f26121114408242c0260b104920344e005075081c0f81011600c0780d51a0140c01140c100542e0184600c10001505200014581e4030607205075580c0c1d1421291480341501400c8040c0c012502c0440d11050329549c3c0c2810085c06220b14002c1c0000e000d640d04000300641020460b0030400c042024030000c10210300030400450750020b82c003c1d10503400d659009032400c0100c80c00400140244c0c00d0030320014143c12046a41d0306031024941c8600303c00035002 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 501443848 1250 501442598 501442603
    0x6040b090319050304020112022106040504020f1002190f140601080c040b0105120408131d06330a0207050307080c0603270102070614060a14240a11 65
    0x88802c1c14441d540c1c81891005807040000e540c0040c411305180e00c0c200c081d02144130590700180c000011315964a0314000d041592040c4854210001351801c2205007080c1e000314010843c0584824007a014044090440c2482080304019034440ea1012102c108000e00d8622245141803501780c802c07643c1010401044000856010b040300c071603100404e0360042e4041444058006180c085040c41000c1c040c41d14007221945a07544164460303c3d0440d5070384440c41e0510205103c54001881e075850701804404c1940008501d1034202c40200d0740341c94003000345030380520070110b820503031065052140108107600031450007030b101091440d0207607440c0c6030b224014035035a5101840b41e02c2c402d0b4072440342501c0e98200b034002075401441440207045000300128520000c800802032030038050394001000024091540700d0040c601e04c50740c13180031090034030740d0018454480c0d0380103000701b4011100d5021502d581e40e0700f00010701c04a20070f40030350b0210120240d80700342e00b00c0740400d00852043c500c2c800707144201 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 501445098 1250 501443848 501443857
    0xf031103151c060203010b03010f060918051b0c010c0f17191407020d090b090d021201020415020c04062112050403020a090b0109090e30040806040b0903 67
    0x200d0344034001d0314a00000c00074051001c140d0100c510852a151101140c02d40c0002d41c00b07803004040e0159294940f030b001c030b840401f2030b6205104110800000748a881c102403508030040c10304604c04240c646542100410451400c5582c10301c40d4000a413408500030107401c04a201403481c5c82c0e0f80c01c0b41c0d8911030191001c0c00c0b4000c2051003003890100240444d00c2100900b184040d12640009001c000100f0010300d420003910301c140540c1c402d0101110907903004003018082d01c0341883c500e003030014220100c0c120782e0003590000c0c0315402d10201101800303025415034000b80a1030900c60707220b103c038039000317511100c600400c0707802035040440101d0180c060705e45181e0903080c001140d10b4502119107410409030960b021507402c2060802000015039641c110b1480034014111001900303218180c000b40c0400c000c0e46c44003a22504210000001c000e01280502c21040c114690013079010411140c810445150b5a005150910114010401050004140744640d00c49e1911103034589807010386030380c0d034001d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 501446348 1250 501445098 501445111
    0xa171e06161103130f030c0f0609150215070302040302031b0102030702101107030312051303121a040921171323030c010f060e0a020f04150f031103 65
    0x928900c07000c10544221441001c10300400103580c01c1c40c14409040c0700c0311141e42e02150f0708140140003801400300c4604020001d020608600b20700601d480c001a2800d0214400d0100400361880240d40050082c8200b0315185120760702060549050600034009420901017a4000d204545d07290080c02401c0224448a03030050b0021401c040c0c040d420485610215980c2408111740b64090a01d11401042a000a0340c03281d211401d142c89410620001c0302c100400289500d25001030b0341d4040b0b50409881541038181441c0498451210910304d0b4201e074400c240560400c3c0740003824000d0082504034200c11403008080707000c1405810038220341401d0768021103109860644089480e42207200411511030340f040c6084182c0708510382c0c689000103070011040c1d45a40000810400c884400e10804842440e0b0300404c0203c9403c0524410085500808076080241e00042056680103a40c054a000386209140c82040c17564404004291a084e481c190001c2410301c41680c82c1101d410742524403030074 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 501447598 1250 501446348 501446371
    0x9060b0d150b040305010f05160e060310050901171504080d09060f090f11010f0914030f030c070614070f0210050c03070c050a0b040308030c07020a171e06 68
    0x800d80c034006001486a500304403001d40903440005000c2e19044082d0000754082c200004240c02d016040f402948c500900003183e4056017651012a160460380c51440e403a01034890b1341d12035a4514031140e010101e03811081c0d0001f040c0d00002441c00b100d1078010104001e040986000200340310170b1408580050b05c004100302d0f824490300d0a24040d80d8848000d00d40038a00102d5909954140d0100312100d10905440402060303810100740300b082e03059240201700a00e450700040c4d0061000401380282030040e4452032566107004c500710f81d01005030b4000104c99005a076030b181c040a030700baa51415148101e03004035205400c0380303085880013802d4500464020a880ca240b100c03070340c01c220301e40403668071080078405e044c880007913801c601b00013400b0014855401c85031124103120410215a0480c0d200101c2d8507002c200500c0011212020380e0b0308024016131036030b03c61a051002840100d125000a444140040c107000e051110028105240c20302c2071020107540e0b042c2c039900c980c4442040300c1512a41 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 501448848 1250 501447598 501447607
    0x80124080c090a182406050907020c0108040f0c080a060b150a0302030403090b040f14040213230405160f020c011d0a120501020306030607020a0f0201080603010207052509060b 77
    0x16881d400071400c001560900c400c07282c184d65601303480749240100c02c51011181c0d01c2c0c40e020480e114801c4c24040c2800300ca07c00241c3c41c0142000b552082541d84150400000f5030100b0108a520701a2040e05644000d00031202e64680b4001541c545c041c1e170b01910300906100c084131307507420f06225200c000140603580c949040c0d4241e600342c0203075001400450070041000780002d14040b101c0c0107000900001401d003d11b0500d4442e0450180c413044c81c410b0b201c2c61041000810702405c0179480b004036422281c1d5841c4c2d001d6640c0380e001c20441d4400715a41c125081108000c49920041c1b101103403500d26403114102c6141c4034104a13501e0000b0400c0300d01040142c1c5003412050b03450780540075600c1000f8268076040341c45004800945960840444050f034001c002e1015600e002c1c8185640110035100a111212142d2285104410030b010003030f0502c01c00c0800b040300750b1021b40449000d260000100c0766001050b514002081c0d40301c4005c45007102e2190070205504005001c1c003803c03100408401c0c1d080 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 501450098 1250 501448848 501448861
    0x903030503390a0201111804090c150509040507020c0a06080a0207050a0b010510140d05060111150411010302040e0105120f0a0303020d0f0207080316020106080124080c09 75
    0x6103050204140e184032540c8511020031010880001c008640d030704070b041c0c0b00e0100040190944500c40d004001c5442c0c1444003285c60395003404508035101d01210040b80107140f600740400103141c10f801c5008251035400c0c00c0c42d0455005001405002c4045e6000c10031a520410100c0c1c864007501011a0702c03043e8454100105841154025004a07030000018a0810140e8803d46040c1c2c400c081180c0100c2400c004200c2c0d490189902d040c203a2039070820f5014448010140c505520800340b40740362560343c901c0031803106d920440d10b000010001c18203e840c50b0003010304180d44681c046a08891400a110011006501c2802503604542d10211500d40c66420b00e01000000c40f4603400803500b500c40c192225142500400903c44c40e10f009403801603a0b1400340320890240d507090414210600d00400200b40000c5000c2c040341e6000f414240c5290802880000480c09002554403003009903080038002c82d4541154003130a01450140c14240750001d03030351544903480305c891021680c0c0c0f102041000400 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 501451348 1250 501450098 501450121
    0xa05090d030e032a0f01060305010606020c0612101d06040f021809090f2a1c02220e0f0f0708190312060b09010219111e03070b0901020d0903030503 65
    0x5a008442502000d80c0d500403481c203180000d45c0c0c0c41c030390fa0380c1e45030304003013003802401e104141c003400052014040394010b84011903002c0c81f8420703001d40c46203000c1d000110194201d60142019255422000005000203808d85c11012000e40d00c1c18840c81c503001e1804be03000301520131a10b1070030448a8842d000300c40b403020802d0940b40140056458003c10505001c80001481000252842c018205941070511000301c001446446645400b4900c02040c0d0100205141030600c1e60a0b41200c00b985045080d00030001c18412241556400c43d0a0141100c5200c0c408a9035040c14138400003210711860100700c0495481c02c0312300c180b46c030603000500c1c4a010070b01d00301030081c02c0c17a02a040034454409280307281d8046031039950182c0030b640c9010a800d6669079040c42068030100c416104c03140e40725900c1c2c6072092101d0f111408103214502c82054a070444003504190312040c48014251400180c0e24100c0c802242d03c01ca07851801070046400940985005406040540717406d65101c50460740c2d00c01c441d06 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 501452598 1250 501451348 501451387
    0xf2410061e020f010e2508060f2211011b080904180b090a1a09060708070306030602130f0e01060801030f0201051902100c1407060c09030203060a05090d030e03 70
    0xc21406a0384041c50b0f150400d01984501d040681d004003c00c1150089400d17070600300403a1032203004100402000519000544980c020180d80b00d9641d040d00c4100502000811000b07480d00c14609044608040c010400d802036a034900030307240c4805000c0c0340c50303000c508803a91181c0102000d4003400980600c0c1815444080c40c00c4201c09684000200b644030000511000c40e00300303030303030380d001030f9844040228202d03000c1d5504550107006801030034161401078458030010142c104000901000030301c1c4620a4015030b00558015070115619000303400c1440b600c056500418519048444c0006112802000403504965081d51070380007036421030355a01e52020205406030704201081c40100ea02074440308044030034190a800400c0d00c05082c01a100564040180402c10b01a200701c4100e0049501e60865851741d602a10005074030b54000c03000e40d440445508041c0d0507101306801c00c1a030b810250301c01801151414211210260b940c68110241c0301559a80c0609800c103020282d000a1940d14a2 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 501453848 1250 501452598 501452657
    0xf01151701240612020a050a030c091214061302010c11190806070f02010b030d12021902060711070b0d0e0c03121201150e060c0f241006 60
    0x10518251250619088a242e101c00c20304080100c0c10412000343c010000700a042e200302e40660030814140c801414a000d208000b90074507880b54101751200d0f11582403240a80403040001e080030840303042c2420a000c165407104018415507001c0381000f0b507200c00e00320445605035078403440c14020344c0c0c1d0b429003820740241076a0405601d500070300f562039901d821100a48a0303003004046900d8400001004c1511030408101564909003210404d41c5010038001038a00c03483c00e0801e00100b038090800700a1150f5805002c049200c0c0c4008131400c1e502161780e81c050007050341c8525080018001c0ba9865000340e115180d49650200408629109690055002942140140c4140180000100c2c1c101080a981c140c8607400c0043c980c01804280c0c4401e9001d4192420001e8008004540103881c0000d40c40c0d005211384000300f0315500c2c082d0b0401c2650b44d82da01c880140d821127407041d035502804200c01b00310117030010620310002d03046020f402d00342002c036110b59507602609040d051400c1d10089498140 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 501455098 1250 501453848 501453851
    0x1201b010b03010914010f05090d05090f03061302030d03050720150403080703060e04020922050d050301060801090506030c01350604060806070f0302390f01151701 72
    0x9807034594007886407042c0180100c0b203080c4100680d0544a00711030201c000103d510789010140031041000091107031410342103040481d542c45d01f46000a110801080d150781d40b41c42240d08000207511140840c0301c4c030034402c0e8111120031001000503029510f003121084009075481d500041e40282905440803240c0c012029210618005058444840702c00c0701c00382c010554403c203106000768540b00d03120040407e080080c4150600d940040e0890744007903d0701c01c1d190100384071607850b6a0030845402400c3c3e03000088805c10107480a0107402600244105008200041d00008900c1c0c0c2c14011300b4400c20004014001c80d80d01c00e801500d502031485066414050008400e01810183d07810901c00342e544046070410f50703d001c00810080e980036420607582ca410507814011415004940301b942c80b00703642000f607219095402c017416002040052000d03070384411011802c0c1d00984012030b0603081d48840070790f014007991150180c241cac2d00310000c0300c1c05420300303c60401c000c00c4030098526180542100 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 501456348 1250 501455098 501455111
    0x919090c080a06060509070e0a0b0306011806021f0606020c0d03180801020403020f01020703080a0c060b041e06050108010b0a050d060b03012d060c0206090d06110a0201201b01 77
    0x41c0a442d00b4030244046460682d10202486140340200000d5800312580c80c0c04c1c54480032102c00700c1e04141f19480b0700380b0086004404034000ea801110154110081c581e05411520307034500000b5a41c0030340d404070075140582c4a000108524190080100343c2760f50380c00407c02c4800810500c1240e0340003190070b40800010300c81d60303076000680080020060585400158545080d801040b410300c3c50308400905551014030100002140320303003a201c500e0707d0360414800350101401d10340081c001448560354010b141c007451190300b0780f1400b1036a91005044008021081d250001968030b03040a000f81c0002000500c003005170350303100d480182480d0b0384044000c9049641c03100d0b2604180c0082e0030015560500e030308010b0000c0b1038a00c840058100c8501c546180c00d150040107000302600e4407020f8007410000800e19001d480c1c01600d13800c07050740f1002c100803d031101d81514000340c0080000030015400c1505c90b1080403501102c40080b9114030001c030346840407021540b0006103001c038528029540f1040c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 501457598 1250 501456348 501456359
    0x506180306090f1614060a090302040609050a15030506060f0d06060305060f090c0907030f0b0d030e032a040e070b0d020a0e030d09090f1103040606050f0919090c 71
    0x11146010b080c0382e0b8001c00d4001007048030765042900307016221030300801c041c40c1000b01c0003018900560480f41501c1e41503960030215001c0342c0c15080c90304007a400600b4000000342c60005640414070034004e410302008a180d001999015100e400d100240c00c50b40000b011484524100e5080142140b00400c01d42c02441d81e50394010a43d18543d1003170312180c04c81c908001c050124007040c2640041d440c4083c00c800c404002c00601401d0014048c0030401d0b54a85c0301e024030b1419640f1030307024094024480d07007401255240c0100b0000e0714048081c0240940509085600c0c050189580c00110712030a440c03403521007030180001001d1417208401c141c81070130000113414014070020100721030000805a80e4209006e00500200007010b4400e009a002c0036100c10a0350b84441d040c001e07074082550200d070329040a071307000c00900f0f00d0b00c04000d01c4000000c00e000030091242d1095080340c00946542e402d0301e115400300031030403c044032000e045000300b00e46802079058507402003206900c0b55801d825916243c5 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 501458848 1250 501457598 501457603
    0x3030a0801060f09052d010503070f080601051b07140a0f120203160314060f060102100f150f14060f12040206120c0306011808100218060f1201051905061803 69
    0x10360300188070300403401451400e40c11400d10340c1ea00c6d1428203001346903052600000b04007071100710b801c1c410400341781c001c94000d0b8801c40c00c49000803038840c89647c070b410b014401d4940300c264070300c25059814100b01e000c0802d400c15030903880484c0c642c1d502244000d440d008c01c04604040c050401c03a854065901e0302c0f4152809400300300d004d54050390800c90028100c0c07911516000700540300584442888040200a030390014030003144a044c0c50000c50b204098080c0c21003d03001130441074032408070a80000c541400090340f14011210507289403d020381c03d00003442600d201e5103566294400007085030f180385140b0309003056001440a0100c0d07241c1405601d0700404081d09583d102c40018002062213031569100c0e1005c00781640c085d0341464001d02c2d040800f50ba808412001204032600443c400c1d00d030340c1074841c5074000101c019102e5a40d4039242d1038210074a41c400b40c07070441400c009800115203414074000395070301a038240144c51036841c1840c0c1000079540220590f0440e480400c0084203c5841c02d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 501460098 1250 501458848 501458869
    0x310030605070c11040603080304020f030a020432010e130c0306020706020d0c030e030d0c03060509040b04050d030903051608070f05070f0e0402060702010f1103040807060e03030a0801060f0905 85
    0x941e202c11100d0518a40040c01d10001e004c081d201e40d050580c01d1000c01c4c039520449400650440d285095200880c1c08281464504000039501c02d2516501030080220605074000e90040c040d50110010881e0140c88003a800030b00400007103040400c002010301c001e011194981600901d102001980d60b580d951080e648503080c12924103801090201c20500c03a030140c0c01402c603180c101886001041c18007180c0d00d0090001ca11441c5484084c9656454042d9014001500019041400a250900309400700c044140c40c110303034030b200d0200015800c80c4244105201d40d541965164a41808020410352040e0301c08001c3e100710303001308030303500004801000c800080c501c91380c05440c009151182c001003814043e409560400400010440180d44607001c6420700c907824200600b910071060411140c0300d40300c80340c4007010700c0002404101729000094840840380950317600d055003001101450740700d0041001020110b081c0304010f022847c000c00d04400304945a00c2c202440c9641d4000041c90b81c00c0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 501461348 1250 501460098 501460111
    0x3020904051e07090e0307031205061c1a061801050103270f050d1b02090919030c02041a03150c0d0f06030c09020c0a080c2d060901050c0d020310030605 67
    0x943c508022819280c0160012105220082c4d03003070900340e860241440302d00400740d41890303039160300040460303a030340c01d0040305c3c0303030015404034141900d629196101480d0705141040709000080001d120b49010b012080c0e1440703034100e119410380d28140054014001d81611200c01c25800b41e4034081941590702d02d0003c0a01811601320101c00394103000d400d110391806e116041091885950010000703840c2200b001c694180c4501005554010002e810191701c05030407000c600003c50302e41c080c03540c44000c40c400503008850410020b1a0383c420303020032071070507256103406070000101043c190081d038160341d9002c29081191458480360f49160811166000b00941034596100018028403603001c8252002e410f122138214a0006a0b8040aa4904440000521000d8001410381c4a0502070041d04a0090f042c00ca9180380341074030800c1d90346178440310203500c40b40c46480006069050140602405607424940c1d252508084012850196000920a0300b05001111000000608500c40c0900c10750 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 501462598 1250 501461348 501461353
    0x1061d0604051807030206090312040b1b0a0b1303020a171c0204050d0b040302030d020706020904140601050d15051306170f0304090207030309051506010f02010204030c03020904051e 80
    0xa0004100022250064100201480d0183d030684440000094440c1640d80480700152110301e0708000a03d0311000700b000543d940d0011600040d800c0107032010303000400d20a0644410300c0c111548040c1e56002050000d88080648808502d40c5400a51600180ca01910541c0d080781ca450b1580c480c1c0600842841101310700004801c8242e50690340081c2045010200644c5820300e800006969105859801380c01036400c280801d00b090300801c111843c014143c501903403600040d0501d10002c0d049090441d01071420108000c041e0b500340d2704403a11455058680600b40408440e0f4400100408405102e0482c0e1400c004203040e80c501d0034130b0007803005180c80892000c1c10400c00d2002c0d0f5100c00e100058a80c0030900340000004080700b03480540300d041e64010b0303d4404508084019041c03464000d01107014441104090210450980d4423aa0081c1c88030440c80c101c0712000c07400c034450340c4000385c44075020040a10040c5800204160014042c0046a168850070701e007920b0040100120b050003603 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 501463848 1250 501462598 501462601
    0x30f0118240c0519090806010303050c03040816150c15050a1e050106020d020307030507030f03060504020d0c020d050909010306021605030d0e0c0a152d0216210305090301061d 77
    0x240001c8804d0051105160803156146045a0140d0701e0f801800010107010700400e1020380c8041c10820382d80203000031000c90b04002c25010031440d145400b4010340301c4ca800005803651050b405070078001c4c00303160b00013817006803140c5850461000380030240031031765155280e00f0400504040c0b103202c1200d600195400040d29490140c0c081c1ca40f0f09400c85000a40d042481418042500b102c141e8414540504143c0c00602584c00c088008000741d82003103074040d00c04600c080140c0003075808010310f40c50356000c0743c0083d6540e001c01d9230640208100503910800180041c03001501c00c1e00900399036015400700e4500c00c182c6544440c10f40d044808103003129030b42d685203280c122000f08820f025525058035028503160130000c00544518244103800140041c441500002402c900c80c020001410254000521114114000d45400030000e50344c81500720103038007003642c410f02c2850b80b0034182800100001091030380c0d82520945c01442d08203505558444002070300c01061483d24002c1c103d1020070490a = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 501465098 1250 501463848 501463867
    0x5040603080c0d0c02010f050d060e0106020615010504080d0e06093d0c110f041b091703090904030e1509030f0a0c06140f0a0e030f0118240c05 63
    0x101543c400025081005804d45040503036006001600407511605c0c0040c0d8501b01c20410300e02500c0507030311200c100403400b8000110aa1701061b214000d6201074808002402c688004442500880c0205400f5421101c3d142e402280155059a02c501d030142c00c90b07090281e02000203274212810390148249400300d4040710002094200d14429903609183c03040307140220342d01c00505c10151108000c0c05c1f40009420170341030b640c554203c21422440188244580d424408003003a0a486609540001c110b80c04008520b00d010f8003904807030a16072000845c01d2040c500200a481c0320060001d4051120f42e04440d48a0344501c880c00310035554034010030303130341d203108105051818180702010b1116401c01e100400018440c0780800d0101c1d011031606145c405040d0480c070404d0f2140d2f03a10b01c13102445c0041d0144aaa8201c15050303031040045054811000d410461503090f102d000520807651203000b43c01c40000744082105000c140c90081c20110360050f20b540000443d100c10a4030320104501090b103884 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 501466348 1250 501465098 501465103
    0x40f080708011e02070302030c011a1528110f03070c1e05150d180c1719031205040c0306150807030b0703150314070603111c0605040603080c 62
    0x512403040200141c03030120ba10a95480d0f500810100600c1c0c000449a0a052081041c0c4400c403c1f010000c11a07840b154560001100c65943c01a020300c181201c242007000c0351400781e4041c0301c080702d0f141c001c110329000c942400f03804441c0b5400600407111407084034564200904c03da180c0c81d03072009668845c41030402e07800e280119071161002502c0c00c0201400500114030280c1101c40c00e8814103080890224030746d030b1070302591042d02c410170303d40703c81c008404804201005010b805500342108a45c0c40d031072031352074410b136008a2901c01c0e401030a101c18540404c40e00080703180e00034030b03101c1c0c06504003010b2541074850603501030340d194510102c14021304c0340318411107045040f00340403881c1d070901d00902c064a49049100180c03130840580005120700b4003079048441405511509868031940740d05d040c400f6601e00c84c610600921441e00081601406032280042010720035075202d040c0f440703846601c1005010f1a0a900429465141c00500342c1c8a5002c0e0102030b61280c0d61551b19080712208151 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 501467598 1250 501466348 501466363
    0x110d1407140a05130b150c1b0d1a04030203040e0702010e120a1b080c0304260105060d080307020a050327062d070c06050a021b06030109020a030e03040f08 68
    0x20300c600e441503003c003c1c40d41d404142180e1015641c4012800703981010020300d013200302c0d000d10b0102080000f0381c89080d03080442c03004c0d5a40c4a007000c860120b509881846400030303c01d08010000074402c0e40c88120701d81070b14250350740940b0030302c1100d242c40d449041d443c21039682581c40f9000340c1e4440d00c0340380c41c0650503c80f0300c0a030003000c0200e6050554158004100610085966050f04514030816050001c1c51007154908000c80b402c681d5100d03034418256001c0034402035603c0e400c0c00076074500c100640f4180590b0b8001c4400030605900d1925544441c2e1550b48064100310940c814041c5002c0041c8083c400361800c021100114400710341d410903100001c6d44040f0000380300301d10400108042c08000300c0c00c8040003042c2c6004542c03201035840201d0782c51050220140c0380c060700060000c2d4665010005000c400350590968008180485400203d2103100702c6c072952000d03062005005207a4903901070041c5650b03500c1d02003114164841d010f41503501a403c10511142d2620017409100300400185 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 501468848 1250 501467598 501467639
    0x319050c010e21010603060207080403050d05040f03032a06050106090e01030b01090c1701090203011a03130303020310051c05150702191109070e040b010f0c110d1407 73
    0x106a401207080007030910500108540c40840b822a00b0f81156202507100c80099070348013204540d5024942000500c1e504140300440311803003140c0002e85503d02c22030544c0d04445084001411080c19640c0548000b0010351200d0400c1c0c00e00c01a00421104003807641c1d01c10360182400140c2c6504003a00101604d200b0b81200c0700c01c1c2d56043c010400500f1000005046607a1040e0002d01c4072880601214030080321340082a13002d09903400420702d50580c0c1d0046041f42c410b00c0000300036403d05c0d0149401070104651030000c4041c045450384c04280250000c603400354913202200c0d002d03a16900040d9404a20191001c44003003414400c100300103080000c0015032048444000c00c0327190104000356101316a0b60542034081d00c002c0d0b0b00c1304011040840320860b41000300307803501501c1c104030000c00341742c294998241f20301d081416200ca03070750050b004207004180580d50ba6036031b5034094840380e0014650944203034000c0760b200014004502243d4100c1c2c0e00c4c0700464050588149000125900d200d00444130 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 501470098 1250 501468848 501468857
    0x20319061a0d09030c05030a020303060102160b090f0a120606170a02280b0c0109050d031505010c050328030f0605090106120b1002030a080c09210c0319050c01 70
    0x1504185903201054592102c90644081030003081c42c6401c0300e42850003400180944008552450b006030080080c610544080e800c0f10a4a09800c8002d4910702903482082c44402007048281c1542c20005403074184094050f02d10088241c0d1000d9810f40078001502c1501c40a989032418403000c828003030f41590002496005259441060300080e03c2e502040d1000e032181852a003940c4d5000700c0070500355006101030703e0b1090b1291403107100d150203041c41d003204840c00d00890490141281c040e00c00e400c0e03413100556060a030300f800c001c010342d0541000d50703040d61a4030090000030006505c0b41080c0b8030782c0c04120840800880101405825100801041c50384181400001d01ca180c4583c0c40d51411a0311500d4082a1200d135441c04800070804a032425801a2011142c01d403090b80002c0140020b801c43c1c1d45041965a50743c6020820380205030000f640039421581d00d52400c5003000c100305501659001360b418101c43d42002a00d40001d48540f0b20410014034800024002c05000b4a42d260b5000e080 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 501471348 1250 501470098 501470129
    0x611060f0c0301181404030801080d181401143c0702010806040b032b0e090103062003040c090c032315030703060f050601051c0504020f0402031906 65
    0x102001d400140902c1c41e20040420410861000f5500144480b404603000d543d40b500345814000c0c4040400d000310146032140c403105d220010b10844005001980f41c007803440115061241120102146d00142410411030041c030b81820000307200280800d05640f40078190841c0c004c414100c42010f60b0703840c4480b103001c0e041040f0050304071004542803154246405c1c480340d5200800940105500480c003500351140f00043c003080c0d045000b000d0f03030181c0d503040354001203115580c023200c840c0c2030446400d411072007000c0100001201900030400362417582c0c2514200c1d100c5540c0000d41c07030b001140c0607240400080d0f0700f00003000321440340403e68101072405204c180c601124003424a1642500300e54180b4030f08000036002a5175801c0900340320740040a07500042d0791707410800c0280c0000a88103030352070724002c0843d00540c050320803544240c103981e500c550200d41c40201000285001482a038101818600f40e05159941d44000c5110300304078001c0d091080da107902850212032130750b000728201ca8030501307 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 501472598 1250 501471348 501471361
    0x2040608061009090506040228030e0d021917161205040803120406020d0212060f010c0f0308150a0306020a021005100b030402040612051005070804150507180611060f 73
    0x704480548039407240c0403495443c0c2c0c001003002445101216084c1140641c140c10010315030300d441c1c1027080115a01804880d0482002e02c0d180e03030100e0201009a0b001ca0400882600600200b505060003203800d1902038030180000c0e203565204481d0054500c200203041d000304a95580005c1c0c00c1211844c14030f061a00303040b000e60303580c4550002031960408890010702003002c16011030766440001c01040d174607035003040035003001514192002c51180186040c0980554400c1248001980c0c01c0341705c0c0c0c10756202c16201941d0036480601002412a040c50241407151180007110000b144542d10042c4d0310010802d00a06040705202c49a28140c02c04050014136108981c0600654846044071556500c80d840040c2c000d0800381d0244105401d504461814043d000c54100c01070708508a0501255039007180841d007a03082254000c100c201194007211040035940d02107940314020f810641c1001903400400c0b9000e20041d44110001048640200030140d0300780003440d041014100d2030240307400c204 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 501473848 1250 501472598 501472607
    0xf15051b07020a0f080a060b0609061c0b19060f08010501080a020904140c03190c021903032003070908010204140103090312091a060f03071e030b0a020406080610 71
    0x11000d500444501281c1003056648400105005003c91015141502d0703640d452a625019401010756015240c511440150f0034075508030b500f0100c005107298504481a031890794182060b20020b805c0380da680c41d52500381d460348c20803603140050003000038601624000703006200000348030605041100341c20042100b039800640c0c1c0d81d080355081d02c002d42c0b2180c00ca40418014081c2401c089680040340e010300c0310701e04031200114001c00032001126900c0c4400b000f44804d80d541c2d0703a11076005a200421641c0d074a210390703011081d040d00c03900d00402c48860366040985000028900c03031504910000a20001a0300200c24034014941900254141490508107000400c003400340e1a0515441c0e1239a402007510890008820748030b0314108103c206035a0905441c1a10f24189103603203c034004010803074500e80f0030a0720070800700040081c9001410f045c22a02c071440005c203540d100765000e08001c0005181c10040314071648511400588803490034400400c894009410240510304102c1c03070340001e581c0b1 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 501475098 1250 501473848 501473881
    0x3120215010b21150301150f090b040b09090f0d0e0105030606030705194d03190302030907060e0d080313020a06080601120203010f0e090f03070f1505 66
    0x361003009031141c00a00010f07000300c11180c002c85420800302c042209001040e000307140b603004107400800450080402407401d440b52070040c82c0221441150420003200c140c0c120018800001c1c0000c00c0d480c0d40c000120320440d00a65603040160000c0c041c2d00c4400d0000c022900c003003201e03071602180e2000b025002920500c40038010364007070b50001000818643c010300c219603401102e080001c215841c0d00e040280344d58005603110744003100c1d54042c2041280c0e240c101a81058641e64a2121102e0004c0c048010107404456071049010038084480c0d000c00f1041d41d03080c0040e590b1009640c2c1c2c5080a00d19040074001c4e0009014003c0c1e0380440c2d0416299541d44282196001010075a6515400314100201e6040c800c025480010800c0c04507a1651014401d030007200d007a2182e0310146240901c5106a010034000c80007501c26011041190b00c440c000c00d2600310060078151071030450f1214130b5a0940c1e03c804401e031140d44c20081d0120803c814255100341c0300306200300801032801c10400340c1210410 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 501476348 1250 501475098 501475109
    0xb07080a061404090809030d020706020105150a061808031b01050f0f040f0303060b160302010b120d0c020604050901090506030d0c05151e010e06190e0a09031103040f0312021501 78
    0x1131324500130082007000411203a906800908660341902c040100030b642c0c1c09603008460041d420440468522842d99000000c115130082c084010642070440483e28215401800800c0314004400060114028070080400f86e4401c40c4c11842225004129400e5a0000d403845940e00e0300c00c4200b01f00840920355042d0040d5000711500c90100e49401c040340075103540c0c0c00a80c1030b400c000482d03445c080c81c0032000c07241480c400d0b0000c0c0904107000701004103c5055400e8259150410760040c40d143e4482c40e00c0080e418401044981065210004030791810000d0b00003208030f41d034480030712855280800a40030400400e26040103070b0074541d80c07095212a0701828408038000500046a040c81d61240210070000803119018103540c0e40b5088890045c000340d900300e0240b064003149604140c02e1951340c8090f106c41400754826601c4900c04070000702611942641040030682d100d140c41041031008100800e01d6506c20b407a15421410a5403004543c207004800b990f206400880c184010150703000c1c115403 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 501477598 1250 501476348 501476351
    0x50301080717061f1a031008210d0e030705030a02072c13050105090a0b1003030c1203060503070801050708060616060f0b03100911100210050c160b07080a061404 71
    0x405a4039955000c4c9103070843c20030b036400d0b00c1030b0004030b0421101461150401850131100140c4d1610f40503240d9120060103500c0500d88410318095030000c200030442d05007090710005400d030010400e10f041d2f40000d4401c8030750f40c00006406810070340c1004403c0c003a01c101e40060f411000001d1900e401d007100c0003000b002500700b6500140d844055151140c0b00b050700032000340124501030034510744500c04c6d440122144860b6601080340e403c0403036101015603034180c4981c420002d481e1298400d03842c520b03400400700744c0c030f500c00401c580c0c0301400401c00a005078000441c00381007841e0701400c0540300510041c0905c5042c07000d66641501c010390a8609a0404000241244040d8014000d84000381803550148940b42c4120100c5c10207602c011340310360003003407030502035030900041099180c0b00c0300c00240141e001d070f0340e0582008895032190b134100038445002882e00020703000845244490382d00940e003a001c0741e8200182d00d60080e801507031000056104000203414000c1ca0751503458926021070245 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 501478848 1250 501477598 501477631
    0x30512030709061b0f03110d0f02122a0609100902010c0b060d0c0b0a08090d0206011502030403060c0302030601021912030b1305090102030405120307090b0703031b05030108071706 79
    0x4814444607220205d400c240484c044003c54200588841454524405144071380129032854a11036540c001c4440001e501a04500003a03142c01d01050b0480d05a904030040c0c0035902c00007060907246410300d41d00650002d17010601c4d000c5002801d00c00080e14074541103080072740c41d00c0182c0e84810614030099019840c000c260700c50700e011912704101442c00800c0c0408041001c1900741c4503a02502085e200b9584940390781d40c40c0444280c030341c0c0d280c03424600580c3c4210014841c0c22100310130214200c441d80704981c2066506d89501064521814014020076400070a1000c1c6581c18000c0c02c4480070303840000d801d5011075036076240c40c11220810079000c0582d282d106e00c0071aa20540f03000c5501845140910603030800c60903280c001d600c01c2d202240c16105200c069003031680740c00c040d648646815100e10207800c0c0b4005541c0714660118408a00f0503956480ca2500515040110b11680e455a659262650304003c1164a08255078104842e52143c2404001c04003000080e05a8010034841658064 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 501480098 1250 501478848 501478877
    0x305090c15091201020c1b0d0807020d080a0521130b090a080714060708090d05030a0915050f0604151703040e09060a0506060301051818010608060103051203070906 72
    0x790041d40e29195010121006490b0f90f44030540291818404403c251654446080a414208400146102d41145e07142a805c4003040240e00903280d0940091b0050015071011360b81c0c0012644110040d0303021600c0401d0704403e008000060100c100102c0d024503201d410056448010f04102220080204940600180c68110700348414481c0542c050142510740c056441c3c0f1002d0015900e9900d2110b00c94a03000661540c031030150b240c0250503440140c0003049024004a445a000034900000350b520748103a500007440b2000c16082e580c5040c50005618101070b00c011040d51005800300e40b05904005420303840401c03003000700d0704481c0b44c44134a071840081c00c8480c5095004070760151400b0342e4148100b102520340410598410f0751410f42c2040700d9518001000310340d0000380100c5030801d422040c040b02c0301e5000082c10341c000151411032900421440fa0707090030340c1c040b60490101504030400400400070200081d030164046030f8011401c41c54056002042046244274a0007000700311428080c1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 501481348 1250 501480098 501480139
    0x5180a0617100c020304030c0608070c0c0e06010233060d0b09031b01140f040c03080a11010b0406030b040f17041211010305070206011806080706021c0305090c 70
    0x40a44021880010400c40d07031036038076150403540c007416450512901c01c80c083e1001c000c950940f50304c021914803480c1030001c01c5410481c01011642804000040741003c00c0a21941c40000c1a500203d000603147c1b142c002802c103c40d0b041200700b402240710661031344542d40003500507510340841002045541e294001010072030b4020b00500000c4501c0f0034020b00e110044010241d0207040404920001d20006d105801ca031007449180ca020503064000c2450000d4481a66070000e00070016124207035141d03195400140d01801c05500860904100d00054010a00881c034000808907410085a850b6448202c6500301c000c00c0108840102c7d030b600010440d5440c6c05020201c143c480b4140c80325150f02c8590100090301c9130590301280003060041081d8442c0c010340303200b20040c2d07000d080f035a4a0500140a80b0b00c241038114591a22800c021500c94410842200180059401081c2e80405140d500c10180e40072007950702054284000c000e101032000450300103103c015540310418190a200b07024 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 501482598 1250 501481348 501481361
    0x60905043201061b0c1815080d02010b18010b090111010c030b09060324091002030a0903031d0c06091201050708010305100b030a2a0f1d0105180a 64
    0x11400c1078012540e8a0381c407007020341541654001e88416010708602c0015405402c510701d03008008011000c418002042d51036280321444e11008030100d01c0104091403030b00200d01ca908040c00903484a9460500c4079424050b0604250742a101c0314001070800c90356100314241405401c1e2001d000241008160b40700d40b94480c42c0c034900708001c0100f1045444004d014103045403000d032156035204046041841c0119000407000b406c85204170b80c605802d6000039204000070641d040714090305004906031540d90005510070041c040340080e21030028a4080c04680350504034100c07044042c250f40300b41400000f600100300d1000c0798001e84070700b0240b0029015901c0c10030b5403d500e5080c0800d00030030769003060b0858141c0e84500107036502d00b03041c00300420880d8010091140e00d070307214030a00d20102c0c1480d0140e11b416020030226620440416458860864156002c2022440b2034002041040c004118401c0c208014000702c0384a54542070024114009908440c4841003105021501140b299070201 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 501483848 1250 501482598 501482651
    0x30b0903034f1b060e120c090c04060f110d08100510030f05010603230a09120f0314071b080408030a020a11010503070f2d110f0601061e12090c150906090504 69
    0x82d10203192102c58001c4035041031141c1c0011070701d330201c0201c12a00601c501651500010002c2008100f000c2c0125802540130b001007a02d21401400450306880c3c1d0801110940e03d5034901181202e610003020080b2a01644070000709844c0142c002d012007114841c030b603044002910103910301e03119015980003d040842008040781a5410f02000e580d8100b88007400d02070305502c0801c002e40c0b0a43c64040810740849501e40040c1444900b8008010000c900c06034181c01110014242034580c01550b103158084507510016a212018400411090081480b0324140a180103415400c01881c094060400c3c6015141403003110f00311911152100419200d084501c0111301070000d4880c6405080d81d03501d01c011000724001d01c1b6491801010000d85641262469a115490360444003001c4c4c03818008030400d6001c108202c0254801100385015181010f40944202030b19240307041e172003080d41400040e1000900c020b80504000711500013419034212401aa00403c1c03c00001c2852100c090703c00d503d9 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 501485098 1250 501483848 501483859
    0x3020901120c0b1c140a14010b0a0f020a02040501081e0a0b01210c0b1b060c0702100519020c0a0602010509071824030b0903034f1b060e120c 62
    0xd01c10310920345c815401060880010003580c1500358804444940c240500600392500f0000150658422048084104a144150703a100c0b10207034006420b4604c281d10401542d03008881008841c804101d2161842d91b490703000700700d001c000355900c02c1d1481c414071400c88402c0412102c1894090501710198410b640254846815034541109007541d402c41c500520404000340300c200085e0100144903800f4691001c640d5040c030900b9030820141200d000a00c0081010500510b040840d003c540411180d485401030b11003c01810140001400c4981c003800c21a03040605004e510100802c0540c00d60303a1411410b4000540030030804003805912034070004000a245460840c1c0140e0494039040d00c1c81201c024065885070a02e055a0b40400d41c1c0c110a400b01016411031103001c800b4421001100c008a5840700180b0b4000e80000700f21000310303101c282900c800319001040f018205902108034a00d0110380e450381880c00080049261900c0d103401400c0c869903c540344034040101d0052203070000d02e03 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 501486348 1250 501485098 501485111
    0x50903030d050708090a020109051507080301030b07120501241806021006050607051b0f09090a02100f14030c040e19050723090409060f020403020901120c0b1c 70
    0x4050000e14080b50107a00040c5000041791900001290f00401243c059442001c00c41c107003405c02009011280324603048030410030403500016070540c040d500035030141180d01024034007900040d241480c0086074500c7c0754030f004018040e4600390302480c0f001840401c00c154440da618581035075031040311410003031651020700001a1046c0c1c0020911034076031200c0803d2241d665070310f0030300c1414000d0120040594200c940200c03078040d0303008651590700340c00030a103840d0f0f1102ca10108511308810f0381d04078540d41250030780d00e0030340c2003074a40e40c04846814034003204a200400d030300401c0d20640003400c6d4078070310002020440070090f039400e907809840c6c58410343d01a424205440d0b03030000c0b142c9002c002c480e8100340020340711902401c8101140780031360035201c142648503550206294407400c00e590348140d8511140c0040f880600c2182000500c02c1001a920390443c010409500d00c141d106442500f440300c0b8000000c0c000750034640841d80404075081e01d80d200c406004150b03103003400c55200958500b0a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 501487598 1250 501486348 501486367
    0x629030c07121427120c1201060915060305180712020301020705190b070905060a0318050d031505040605031216051603170a20010908030c070201090b0c1c05090303 72
    0xc909400001d098411440a42540052090201401701d070b019854000c0d51590b50349040001080501a81c400300000b030040d1640e0680d421a80e500c40c0488a03481a0b000501005030948102c54100d4800700d040c1c10144008683d10b0760328038030b03801100c4814014003000811074609405807403803280e1040c1034400c502e1680d841e03507900c18403e04060f94056120b001041045000728121001e0355805840c42e03140c90201c04054011f8560700c1d45082e9035608078255003000c00c10522080c4000ca0030795401042441200081c0f15900c9200d80149104e240351040c200601ea800003031a604411541104588030f40c02552030302d401400a800240c9540200d51003403800001246100c0b0549101e04030f01f01d1143d04542e15a2824001c2002035808a5091122401400c0701a1054120000c003000041170701c502c10740c0c6401c415041650002001d0780c010801008660300250410050305540c0905400c000c003c0069940c0d03076450303c0480c40002030001040540c83d1152044405048000d000c50341c0e10401d03036 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 501488848 1250 501487598 501487627
    0x601030503071209030c050d080403050f0a020f04140604051b0703030506270f0a18082106180a02040e0c0903010c08070f03050c0702040629030c071214 67
    0xa202c110350740e41e60358910303070100b500914900c4141c039008009090320b6824481400404401c050054500800c10f11001000400c01c0004a0000b2143c0c005820503004174414026840c941c1901070f031249081c0000d11303841e076481d40c8045030b10200868020446031038555003d20a40c010844007021008002100c105050701904124001c1ca002e0350040810402607007070722180407680740c2d42040300580001042014081922042e006030307100341d00281c1e81c0d0040010f161080d00302c05080b1494030703011600400064454070725a105120131a2503103090324000c000540700c4062120038188200010011800c80c10b8140c0c10788001d402404182009818030701001c40c0c468100c007250521035801c022510070110312800c58140a0174a03078603501c0010341c0c1058203078040c0c03000401401103100c0034006200941e64500070500203008920240400c103980854200786103d040c07030412082c0b03200b00280080120a50308943d83c0903049040c40102d82c1c0801d0702215084564890001c00705400719880c00e00341b850 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 501490098 1250 501488848 501488857
    0x714091c080717030118020a0215070c02010315051c06020d1404020906031b0103090215041508090303041505070507020a08011a12031b071a130501030b0904150e0601030503 76
    0x14074110b001c500b619072a0f00028402409212401c0000403803070101052180c000e03003010415401038034802d010410510b640502c1c1200d494001485100d0310805650701072107401d020103505000310076160b0030030010070101c1204039800c0101c41c04d040d80c21428031101303074145d581a40710380c1d20a101580781c02c2c541080c100381c107a400b40c0c410802a000300d081c43c6400101120039040c0c101c5241000c0d01c01200640c02014400350036030b006040c1c16030719011b00b14900c00030009040c82901800001d058588010071010303000303002001030b6100700b081c00045641402144403184843d8404034090341c0d90a0700302c40f42d0094050007900230b6020000032550102c103401440d0031340d108030001c1414030f0070034007003241d02840c80e1110400ca400420204500359400000c04803000b41e4401111412503071002d200c00c640103012002226541c02044801c0076007180d00b045001040e091a0510280c5042800508521005400140303800181d8080c080125280e40041c078001401c0030030303200035681d20706050391a90b00 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 501491348 1250 501490098 501490103
    0x307080c0705130209090408030a0e0a0b0412080106051606020d0f0f0e010b010503060405060f03030703020303060a0b28030f060f360903140a0e0f03060714091c0807 73
    0x800c0f4000ca8168100d0710a84100700e000034084059501c450300c880301d0319030002d0b000000440e25003000c600720090400030b000740d40d1311401c1c5910042ca06802e055681001d02650001005031450040080f603a201068460000b010388044211101d01d141040c0288145e040d0320020b03a080c200400045070407035000300c030b629002c28800d10441000649040c04c9581c0440000d003c00c3d000d10104109040907030005500102c00b03030801d24100250700001c0d02d5900541422070059200004115841c148900380704014240c0d810b600d410000c10140801d85403104600c0e0121002c21150440c01c464400d8201505e1035903025000c001c2103443d07050004200c3c20502404c910600021007044d106d101805582c907410102041d02c9942462400c208030141c25200d2080e410000d0207046055919138010003043c1d8070041d030700c600c803d40c000d0340140f14105140e00c80c054800c0e00f082040002d074907009102c0520f1108080c03074540e03842078004006503468454140d2240c0845900c4124001c00c400f1000a112890 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 501492598 1250 501491348 501491359
    0x270f060106021603030e030f010203010f14010c030e040c0306031403071e170a21050109050906040506070c05120a0305100f0308040510120507050301050f0306040210050c0307080c0705 81
    0x3a252074099940c0c050655101405280c4000200046880742020030340840000302030310302c10060b008035242a070308283c00c407940c402c0e840c500401c1400007c20b41504801c1003801c00c0d541d403240700e440c0a0029420080c80c18022502c81505c2422180b090f88054060350b40300558004980300b041f040c594030b8120202c1181e10396111011007099010002100100a0303100e10f030f9008c0c1c000000001c0c142c2d034005001d0b11040c0000154102e0b091080800b006004800030036000450f585030901c610261400134003403005603084003040c0b002280c008a02c09038010501d00304030f5204201490b2017440e2242140c4041921000031801c40c0c0d00c41c0d415000140540c1c00501b0505c030740d035107074100c100e00181144401800000d04001c20070040c109050442c2100606051540000c040000700500380da60403030303c5400280c400001070250f41340c5001030072024442900281800d00e45540030460400c00d0740c41c0c0b1824094003085040d03403014108100c44165a20028250300d80d010740e07849541d124100d015092058 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 501493848 1250 501492598 501492601
    0x140c030712050a14031603030c0f0c170307120e010603030206010e100e06041d0c1306030215030a091e0312021812030c2a03010b09010e270f06 63
    0x80d224070301c0111001d40c0000c041c2c807100b01c00360385410302c00b54100440d880f907000070b0018400c0a8802120900294000d80740482c180990782d0300182881828400305046c0130400c070b10f05000ca62455064950302c800d006d000c80d44c81d1150301c010344280c00314103641c0e2516403d020144120200640204040f280300e5021195240d0b243d100c042c200c05c0c800c95800d0b150b101c6152007005448000300e00e0302d8100201170400580c444003600105082c4c5c420038071101e95503005400c0010181800c0c0c0c1c0c1d1100b4004802020041079003581c1c000340c121100c60800421310340e400300204100f10269400b0761000c0350f00205804541701d46001d80403200701180025804507062001359200c1400d0790013240c056080b0f5244500c11030300c9030404c200c108243e1071107019030f80c80b061081c45181d820400600141c210820411000c1e107a2007074102c200b0391515404503020781d06008004010f5100c480001e41551400d015030030455403411207200940181c103014000c044440c82c0e4503030790450301140702000b0002490035074925 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 501495098 1250 501493848 501493859
    0x40c210e070b1c05040f022d0102030910030e0106091b1409090601180801051e0606070305120c160b0601021902100f02030f030a02190e010206070806030a140c0307 72
    0x1a0081951400d00ca800f2201c100011064a44c41194884d210360303c1d0304609280754000c01c81c1c00000d015129000b603801400c2c90980c2c0d2504071181480242480118940b924503000f048001400d802a10300307164881e035075008152029044070010701074000b82001201e05220f40000e059282d2a4008082022034854440140c000700c1151044032000e40759445941f640750045410701c02801900781c1800303600c40c02250304c076070a0090380d0190100500e4400800c4110702481c40000002d80b442d48035003001c020160000350001c0a460a07a81e00c984d4400003603940341c06050040c031420f1990020340200c491410200000311001e180940400e0b4215013009403042c00c070080c1c0514107403020754002143c650000100d407045841d80040c0e4031038810380e818501541201d034000e81060b00d04001003500401c030200c1508401402c29080030b40351805420f40001c00b40040e480e0040981940200858000010340230348042008176102540140410340001e4100c1c1001e4070b940052221718428000d03007038000703003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 501496348 1250 501495098 501495119
    0x10e0102070b09010207080301230d1401240605032802030f0703050f180a020d110306061503060108100b0c070f0b070321090c030f0210050307080402040c210e07 71
    0x10303111f40c00a107091650342010030170407411031130700003079001940100100e032010744038907030300c0c00a0a10070b920b020b400410300c0d42e00ca4252060741081d580140b5202860511606c991041402180c40d20f05005599440d60308070030741e44280c110304000c540c010720005010124055401540700303148000c50ba4a6549a49070300f00d0564034140d42c29000c4040035808110111001441249600240c0080b20140d02080e404200400d00540081e144003402404900c06410148003180c0c1c026030803580f000700c04600f0100082c070350101611813810040710360f002801e440c5441d8040030140a42e2600f0319211410154010360766440e5029418403161a004001b503440e13491801d60340e00e141c0c1501c41040002450050004241240450840d0251101c5c8000301040740340000201440c024100260178840c40d006100c40903c018410b0800c00108008005205520120b1140c200750b040701c02191840c0c4070902200c21500551820700d006129104400000400364000504480000c060f40c00441c0d50f503946c103c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 501497598 1250 501496348 501496357
    0x1009060e090c072a03060501030203010608010b0a0909030c020a0b03070e0a082512120305060904030905100c080301060207170105010608071206080319080f1909080903010e0102070b090102 83
    0x140c0001844141c0003d010750000045980c544e00c08000c502c0c06540300100b040f2481e07402503079070076038503401441581020700030742025001364030080c0f00e1081c0c408c3c003040e00d0402610845c03556640d5420f0120805100b401902d01142d0020b141b41c05082c0c8441c1703101082d034030558400d00030038906060301c503980c28603958582c11a05840041d12411500c2820000741d0542c0e041c42d240c80c51584400400c2c43d00c001a02115030501440348226030107007401d409401c545010300000d2145810310b0070000020350189009081c1c96080d15107041ea55000001a26250300e9100010f01c3c5081c04000801c001e54002201c1c41155425607102060305498517955088520a010f8038000442d8600010b03c814002e58240b02240c40c3c1880004a966031940c146017550800d00e00707448a989007003e07481003607502c64803050700808050115a0303181014110003020050210074051303455112044a0f06001c18070003511102c007400b900a0003d242c0b140f980134001c0d41b0040701181d4040380e18010a00741e400c148283da = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 501498848 1250 501497598 501497611
    0xb04140106021c031e05061e0f04020d0e1b0f01030e0c0405130807080406031d0a02010e03030903070f0e01060f02032208030706060e421009060e09 65
    0x925a10104043d0742c1c0c8810700c26403107102450f4807107100401d91030101682c040060381048001401d07007850b10401055085403400424001014120141980d84040212501d41012200180c2c0c6681082130030303018005c4070031107040314024038481c4902c001301790700e100c031042c401140d100070317088410310065048031059070702030110758404040e40030603007041c5d405a034100e610b80d5486134400b034056459803001d0b070107801d080f61202c0300440e0800400d07406006014484140320100122400752117040c81d580c041000c0c0107410460700161228050f00d080c811a0000d500107010f881c000d82d03c8440750b41da0140c081c80340c038511429540000500380d00c0358104c494400c450f6030246241c118000e0305501c69220341041e40c030404e060710100040f016010002050520310411021444d1450000800400e80c0010030f250a40001c0d900c6002d02000048038202005801c2d03040380304002900c0b0100500100030b080d1168000c00b500c414a500f4035000356400003200c00a5980289000d2507609114160300240c030304 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 501500098 1250 501498848 501498853
    0x908030604050403021c0e090703110a14090a03260c060412120e0c120105070e011103070203030403030c1b0501050d05091203011508220206070f02040f0b0414010602 73
    0x8280c40e850305401c0903801500900c1241d43c150080400e1400541030840c1d8030340801c03113503040800f41c1e041061010358820b0542c1810410045000c41404062040c20108400c0000b203918443e8023001890581c4c0038200040c00c0c10710510344a1400e01103c0000800700c0c1c0000d5480200207000032444012149040c041c407010f401d55480b82e0791803110b1141c00c22112810700401c1c01c0c040c81c02c00b01600c901050042010010489140d000090201d56044840340c0d443e82d0b414001003109041e0006903040e2104000c0c42e0000070039410050680c150700481c035000b0740c58000041d00101741076000c190151010300a9021003044181d07400054402c0406200c2c07680421828442c8800000e80395100d2980140c6600903a0b000100602120078103a200740c000b400c1540c0303400c2c160502507500c0f402d410f40c00f40d211b06102c404801e1401018450b4001031030001d01c902c00c005940401c002c10032f0042200d01c2c0e400b81040c881c007003080c1f81000150807108000c5005610301180344900140c1c0c8048130341200c0b2650013 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 501501348 1250 501500098 501500101
    0x110309070b0717190e12030a0f0c470406050705190513140d11060d0203010b0d0e060402010c0308090c0a09020409051b0a050d0b060d05011404090803 66
    0x9114485410050003682e0407203072052450305089402c0002d1411342e9003003680e0340000012190240034242d02c1441d150003106120000419140000100c3ea907408060070418058084503404681070b0a40d00801030031100306a003ea6108402455442d42d8510040941810310300256a2001481d030442c40f02480c030000440410041412988519081010380c500145041030103c550501082c1c0c89600034000360300040c900c051000e801d403445e00a046800c0650300707039890700e60000d03505001080010700744c16070056200c940c42d5142022105032810b42c41041d9104c0d80e4584c0c1c030101c6030700200c40c001e24240c01c00d29030304042c180c0420b02e5032007564140c542c0c414000894030300321103045008060b05c20a01c200103a211190b61840586402000c40f514090303995420005400f09490000d002024a8449071131201004400007042d40c8c4459070b585050303501c5080c110b41c0c0c81c000c0d01040f0301d1103400c1400020404403000b1140c00c074505075104040da03000d511010300284030841c0c150b9400640814410300 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 501502598 1250 501501348 501501359
    0x1020c071a0a17041e0f020f0a140609010c1a07120203040201020d080a02040801060e040614040201021e120d09020405011e0519090c120506061c18060c0504030611030907 75
    0x2480c3c160050702900040c0c05001104003e6424104030301c1e41a00e000f01d5980c624021854940e05101e0107500644040385124540344e00382070800040c426803441220042402607041c1d21800550b245290031920654819541e407402e25180c0300700b941e0100008000904211440c002c1d402241d00995060f802040c41d40c030b0504085804410103045031012680030400040c0c440024010040500b444a4003041c80381031900d85074007142d04410400c601041060104400b5170303000328080f80740c02c48012549449102401c451070900c0c400b2041c0403500c100102e040c4114503415403040318828426281004583d803181618907524584403600c161a000e019014030150809240002008036840d501000050b01c3d00036000c191484111800000b070002801c09031030751aa8014140c10960035943e0b103140014165100c9007001d80c804044000f65100c454608600600703218848460303801c03010070801c11908030001403e680c814801500e4280c1440c4498040100034412030b070142030762000400d412483e14 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 501503848 1250 501502598 501502637
    0xa0c3003080601081306061d0603060f13050a050a08190e0f01110a02040501121e081824040f06080907051002030409020705211c0e0c0301020c071a0a 66
    0x203003410301419250604c05e001800394010180034040c500761180625004e1041040382c03a600400861080d480041841501c01050000c030b9000b0b80c001d080d402d104a0f9900b440382c5002c08042c0c0003401482440071040c140100c0c80003801030040050782d88517101000f1901140c0a407464003449600624a0803120314540c003d8000188241e0340505580f20b074030305070300000d00f241c400760321100d0a50840c0c004141041840c000e80f902801e101030b020340c40f405154480441a02482c12031011032502c1c61030407002039403241e68501c450301c10500e52801008807c078042880360002e01c11454040381c41c1001240c21401341000b03512801903800103000141c40d0900300300030900c243d0040741c1580420000854480680e00040240601541c0102031290f02c00c01a0001e2002c5d003454030940d20400e100321040e2f00e129100643c0e0360782d45040081140e81160a07501d00340006d81c03141d140d06610006858401e0720000c241c3c03408030703a078094000901340740c42c000c4021244a15048900001e04c00b803c20520f83c0c03110f = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 501505098 1250 501503848 501503851
    0xa05010e0a090f0911151206040612050d02061506031b0903161a0304030c020d03020f0102281803080307090f060203030f06010e0a0e090a0c300308060108 68
    0x203041c0c0c540d060307803602800e084982245035001c842e038455185406200c040c000c45070740f10a0994030100c019040b40c0344031006008801c1000c401d4540741d408030702281d9640e08800050107110031000c03001080c9140c10307643d50000b080c14030b02501455001540c80b90040304103070305d00c040142c40a0b181d5a41c003100f5000c0b124480400d007141c0b081c14403940b110f54030100a103802800c14691040045801c2c1307010300e1045290032400000ca06420810000060350020342004101c0c0c0c182c031381900d0f40ca1039240a03810700c3c242050001e22588089104000079207001d0261000010304a00c110064141142c00c03102c554043e82c001c1c41c2880508403c0001170000002150f01803440d160035017250f61a0040c10805640c5d0b940060016440881449844048807001035046031003424060000d007403903004200d00503107603c900b003500014800010300340c01040c40b103801134076404500f150000707445400d902c03041d040e0311f01803070303000d00314601a911801f681d5001d20b0304030f0750180c0b14049540e5500c801181cac0d1000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 501506348 1250 501505098 501505127
    0x203010e1f05180901181211010b010e0d0309030b0a09020415050612040309031e031701082e0612030207060809151503060f0601110106030c060309080f0d050f0903090a0501 76
    0x103851000c001d190341d81d100f01100b9144a202c0201401c4202c440003054081084e40e100c25034ad26214803d605aa081149040800416120300c05d20305e000e0308043c0e07000007160f400a4102000042080060f8100f0341c01100340c0c41c0b0858040245207a01e0412141c906031030302a06030408401c003d06076441e40040b071140d40c424480d14045031241d4403966201d4403003840d81c240c0c2e0a14403403851000d08250b00490300b0340c5070740380b8844800d56561510381400d50b00c1e00b0744854500c850725442d10700c0c64520303561000008803103da04000d005032580d44641580140660000b60014000d1050100f10b061007003180501402d0104028910f040302449120070401014002d940812460920105aa1418030171140700d107003c0500144189450b00014102000c110701806050b49055002e00000c4e154501c0b800c2925828070340040c0c500c0300da10340f010356031003101020304100c2e801140d003c203800880d40002e0f1250281d140b807100030740c413010401541d0380102a0b0003070340300303121480c01c0c04507500c104600e281401 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 501507598 1250 501506348 501506351
    0x1b09080d1b030c022412060d0f0206030a0204081e0c03031612050d09060906050709031a060d02130b0a14090f07030f02161118010611100203010e1f05180901 69
    0x40c0d03020f500b01074804000305c03030600554003180d03210a80000e003501640c000d606452440050b4042e643e0705501c41c0b26400003d03c110800f1001c04c040010983c10386000d050210100d60032105030b41c20f110726070300450070940000e01c00c0b0306000390f482c100070043d94220b180c0d82104120034581e80d540c03c0482081c0e50f22400030410140b2100754262280d0040503200c50003404001640b00f00d40c107013041502c0000f0410018041c542d0400c000140e80540ea03e8000c150b0300d0043c070100d45030030340080c0040c0800c0c0300180d800041d501d283c5408600d10742c820b1980250803950010502d5440301030041c90171410802c03540c003003c10000542d55000449106501540d80d160000b0b0f8250f41907014400ca80081d44586400d1b050840c810041100115040e04d92007402c030307882120190300103500407080340140903a101708084004810510f800800c540071600100000940d140e40e1601861241c1e0312040b0b07a40c05442c3c944010403c550700c07098008070195140a010f404074400107891320684c6810291022100d903 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 501508848 1250 501507598 501507619
    0x1c02060f03010603201614010908270102010603020604062609010606200d0c140a12020c040b0603070302090d02060a050406020d021c080a1b09080d1b030c02 69
    0x2090030045000e4422038800181000703401004036130130300b000120510707240740400100000000c10310022040030382c03110402584454108807180034000d0424008e26000001c0740c241001c10f040548040d1000c40100300d182c3c8107503103100480c265102440702941040c820041841954400c00c2c280c500c81425850140b0031b034402a0f020002424200d405c0e0314981d6586005110f90b130303404286804070821003402d0000108800514944483c858011a001d0180c505401c0d410040c884940070f686c42a0300040ea084a0101e050031404070348050f040000500503008152150320745403180c0c0c7d0b07240d000a01058156550041e00790000d5118400082d405205410024016611107000702902056540c415403658580400a490a41c141540500395007000b20024540300183c20007003070000e02450800381c1130f220413004070002d00049956151050508140d91004ca810070203007801c07900c0d00c0c0708884510041c094120f81c403c82070300c00361002d8682d107405940401d20927403a02c00c400340028a90800f0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 501510098 1250 501508848 501508867
    0x12160509180a1401060501050304171b01020a020d031404030212181e0102012d05040221071a07032106050901080706030b0a03030e090702190b0f09010b1c0206 70
    0x3494080e42c01110101c91102032071070404800e0140800600c800c1c00d1460940c00e040d03a07280781800c041c0070401c100b0200860441000e075030450842914040300c800840d92542c034035400070b44500c810307070001020038140200111403507a480030962141d034140d070240400100d500144071003944822806401002515145c010070342d00e0a00740046e502c809203440420500c80b80019082d910a09170001204520381035041c2003141c0e1011011098102442c0014141d07120710005040e40d0076144855207001d110081c03000c4400300090100d043e200f003600d1082c2e186ca80c502604002d0720440c0ca0083c00036101460b190250341030003240500103a8105804100142c50f80b011441c495026409203d103944281c400f00403aa401d441164882070042d20380794181425030310050903c15150380c485006481c3e100c000751115109104100300d00940340480e0418200604009000c0c08041d25504a040100800714060010510a503864268080d064521480761900852400e603a22402683c0001040024412 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 501511348 1250 501510098 501510103
    0x3200d02061b0301030c061b0b0f090124090506060415050a140a0e0f0d0516140406120206070512040b030103260405041104030f111216050918 63
    0x114900164010712103072801e01080700d5002c001c2000c000c2c0702c000c200014804141e680509109440003828840d4403407801c0180d20380f01d65a54a0090704c003082c50014402d03d0702400712041e0058401400a2280d03102c520030407000e1300c101c854200e080c418851000c000303a00e803541225034030200c0140301e07909043e5512403001d1909415060701c0005080040e4066030a40c010380001c002503a50003030b4a04200301c03480054401c0e0020b542ca28805c107802580340d40030340c0e600c0750300d103040302c0c2c1c81801d03103c5d42100d1901e140009240e6024480c01c01201404081041c1400c1c8034141c100c4240c0d060b459200403d54081c0711030340d400010140c440380151502160070040a10081009003c014009540c3e50305d14202120041309021824a036180c141e80d086140c0207031001070382c0c20340b1030840e03000030442d04410710b10303000f03200d0395000900c8002421303d10000e00c0b03000707040c00d0384145050360b500d007151000301c002c10303225005450b030829480c103800c009005904242e20a1940225603ca030500310f500010180c52 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 501512598 1250 501511348 501511363
    0xe070e040503040e01171f1b0503071d0f01030e031204030c15090b0718091109040b09090327120a060e01020f0304080901051c0b040b010c030c0320 65
    0xd440c2e50002508004c20b15081d1300a50051101007216072070741d91076403072036612030040c85d2255005001554100d00303114020f5000441d0064041c0c040540c0040c0181c02502607042203609074085607202415101420700d0018020b02c0b2070004043e400c208a80078019402020700240a801a22044c011046e03900c09401c0620701a07070103502d580150241c2450300800c10545070b20b00000303603401c1c60a80760010395413041958001200d810411345145003c2401d00300710010380e20019103d800c00c41030044c00403040d402800c1d02c800956050201c00d03050424807940e12000d5480003074030740c0100712040c4400122101e03402200aa00464119a00341d40c00040310010408004201a0000c0520404001c51842680800b80c000d1000b503003002e007803c1041e1054000140b000d480a10009090340346030303200750f0441d0b0484461643d2042c074208140c00040040ca1450051030045182c500841410340c0110501d850503036060760381c08d6401622b5034044651b140b041c404201e10120710002310221314018040d41d0f = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 501513848 1250 501512598 501512603
    0xc120a1b0605012309150102030d020711040b0d03120b01030f0c02030a110115060818060c07030f090b180d0605070201020d14010501050405010c0309080703080424120e070e04 77
    0x3090b25410040643d851003500c07607015490b1881ca07900074006840d9406801c2c0e200211244d040072807420b202c0140e003980304003224040c1c41840040c0040c100704200507400d400ca0015101000003008000074001c50540f058400340100c2c4940840081860068201c0d249280c01850302040408c14007070b840d0152815801c0f2640580c0010401d0010140e101d1100d41c94840703160000e2003d62483d03c0c0581c0041c0e0540200d20401100342c1c00038001241d5114030803403c0d90054101e4a44d0300d0f01d0074003000d540d000324500720f000403001d46505598502c245840e40594040c0c014070362511400f89402180c240d120741e4038941042d0f4105d40310011520b03520403141300704265000503a540c00b00d2201081103640d5103010f41404820400180203030390b8440241c9050381c1007800c0280000342581415100c0341200d0b0f210360341c1486001030200410469a0180c4100c80b45085444441020340c000d00d03a0310400c00d00f42c94001260900081c07400780e00c64000c10411480701c416100e400307031560300345c0341071041c00c8409 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 501515098 1250 501513848 501513851
    0x2100f0c080609162a03020109020111030c0705010e030c18060a0b19030b030304091a04050901050f0a0b0f1302032d0402041a060703180602030c120a1b06 68
    0x240d0086401c00301c140c0d4020012200c98205203000a02c04600350481c8510404020942c1ca103c4071401c088081040849003900320502c0005c030b00c0c58000d000c0c0210003c100e002a0500f00c801500602c0041070790440c0f0080e0000d000e00c1d81c18280115059a015200300360f051044801c0f04d111a10f07452203002180850044035001890001c1c14048114215402014440c1080282e4442c3d007002c0200351403640030a18000c25820450000207245003d02d42003080028a0030b031804103802610b12012942000546050040d603503a03015417400c0300e02c02c03a00380c10941e00000018121003001d9001214026006064180d10350015001c5802c08400071615104d865001042c03050a000200451081e401c2d00d01107410100000e2030645854600500000d0040da00c0340c0304100c010418124411640c05e019140b04d40fa0b200700d0600a1650310100ca01103020710400c00c01050041c80401195118480c48005140e0342001c1d044401c400e174042e64801b000c01c01855040d82034012040c01d0811420b000c2d800 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 501516348 1250 501515098 501515111
    0xc080f030717070504290903033004020f100203040f09020d060911071b0306230601030e070b030a110a09240c0b09070302120f0f0303071e02100f 64
    0x711840c0c0b5480588000140181400b04101c900100054203c414444000100103025064007031403841c01203104190b0702d400007194244c850b12100036121000182c2c2c10560200b240010410041800159000307500084948040409400c041c015203041c40c40c20300c1280d150070b030b0341c82c10781541c440d068006608094000800c0224240d441c001c450140900000802c460070b078079000520030388240d00700144200210010700804081c2260f0a00045800040c28030000f0b00d6002c00b070311141c9030b0030b9a015003504200049102035106c0e01c141103100d41c2140040141341c1c01c1c20b0002c903d40e0001000740841c181c81700c9407610a01c00110244c000d080107a2034007a0740500f40040307079409804034154000c0c00b400048144010760784c8250703003014458104000c2c0709107440d00307011507041120319040a90400c140503042d07460404005514441d00f00000280ea00210008030f1003510f031700c0300340d81010004000030101504e081c41c01090481c00800350041b220400d5811402c0810360703400410503004542d640a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 501517598 1250 501516348 501516377
    0x40c06230c0a0302060c0a021f060308130528050d05030d090f1203020c0316080c060106120c03021216110a08030403080702010c020a1704030c0305030a090519060c080f0307 76
    0x11926401c0600421b100d8101010480002d64606841e42c1031039000c2083e408113864026503a000101441d003044105070b80e04803540d00d401c80c42009202e1a80600d108980b403840071005401d0700003201104124060305c0600d82000c000c0030b043c82e03980a54450108001041090840c1d202d02c540030b51290000c45210502c5041c4200c10b000e080030484141030040051614007407000c07040741c1e841103400c410022401d11138141014240181c0342040018451074001203241500010341034080c624204090120141c511070071001da0241c00800c60034910f00310046001204414840440c0448a03d000c01c2d00c2c60f0107441e210b140c01004202541c2290000040c84245640400703416406450340c0000c1c8155181510002e42d142215480603001c81c510301c0d40d80d08801a42070860b00155008100d006000f6103030704001e0389075030188521b103012032140d1800040500300181d12801840040450345556460b0541c251440745560704201c621a80030008030005000303450145001e080030b40c0d100581141c0c085e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 501518848 1250 501517598 501517603
    0x4081b0a060608010b1918060b12010513090201120902150a0e0316050d060f1e0e060108151b040506070b090c01090f09020c07030203070b21040c06230c0a0302 70
    0x7080310034001c1131030103d0340c51480d2894911900300c1f40d08980c10842c006041c0c040400429943d0450015240c001803915204040c40d070156040e51002c603404281c2e000303c00c01500446150400090100b00800140d050082c12a444035020314009425020100d80700300824000341d10480b0070741c002c61034915201e800d604003041080741e96160300041408a504150005658915501c0014071a540f5a0313600d090300c00c0c00f508960000102c04130340900ea020200004405403034140b10301d1300300c0d01c1100000204075000240629a103c02c500040c0c4c0a03440d2820480122004d1242c041d80c1c80e00c0400000401d40c0341c0d40300031301c42c044c00350b8001007090800c2c5030614104182d144106c0e0400c403001d6030620071070388403450a80407544024401662043c511a07206d0070a503840d171002e5814010303c040001d5510b0500000e0680310385036681922501b080704502c1c94624410350780500b44034419441402000c0c060042480821a1460b0a0042100c0c001c981c1007140c2c045881071903290804401c507070406404 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 501520098 1250 501518848 501518861
    0xb04290c070602300d02070507030605010803040e250c03051c021b06040809060c0f15090d030e030901030e1923060408030f180601030302010c0e011704081b0a06060801 74
    0x8154030742c400044040c003004103078042c400d48245400d80c0006c0f1fa8080100800107003008540c841e50a100302c1da500c0401b5600d0350082c7c4108030304d0100e600000b462090881000e2656a94240708407170024000079400c48800900d4103084080c07010030440301c490881c0c070025041c4004002712000d030b40c40709483d182150001c0754131800c0719203501c0b04d0140b0001032112420f0318140a82540d0f11512003041d54205441d00300d00c6442c90405000d11210031000503480d4504901c80d065100032614503060580d401c408890203502d040319a904244220151907201e60468a140500391044680150024000c4044001e1a51040f01c041c552035034a0016500749000d0350341d600400c0d60281041e841c0907201c4140c0d51000030001c0c0c40c034441602c0044e900880c0382c0300340240c002660044599942e16864088c0c0244000410b58001c01c04043d07080ca0950701ca04141d00f0250703c003204042183c0c0300c50ba1411440d03013200c0d4990340b242072020960b041d581401c100d54450b05002e1080420307102c2c50500c650f42150031 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 501521348 1250 501520098 501520153
    0x30403030c0e030a031805120a030905120606040507090e0a0c09060306050a090b01020f03120f0c0f0711060d0f0f140c030103200d0515010b04290c070602 68
    0xb00450b08695039010454001003a011300308116140c9007040c10032055031142e00403942c080049015a40c0b000030029200422921940310490100e8a8000b0000d000c5143c2c52010b03059441f8000080441c00c080c3c012540203000740c10314017030305030316980315595a010440c3e01e00007a40c0c1c3c0d0b48a401e00c0d6640070320070300020a9182030402c9050704080220b18076509900601c1d036200e031503540c0044664801c0181ca80704501e40001e4a440d00640345240100c1802914803100740f4500c1d401081c0050200400c49810614140f10717546091842c0d55403140c044080d800c00c41d44960306008000701103e41c1e01a01103030881e0304000007a58410f90b24214121400c1220100341510707600d0411141402c190100c80c1925000000e5101800c000e002c60501c101380350004a8000007140000c4080010004002c0102100d40b00721040c03681e2540024140c0d8000c40c400c6000d94080b1420200303498201c50010001c58140e00a000d1a00c041102141d00d844001d0b0b1102d00141c0c00040720721a035041c0148181750125 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 501522598 1250 501521348 501521357
    0x3603170106051b070305160306050a0216020d0c031b0611030304021804110402040b09310c02100903022a01140d0f0e030c10020c191b0902030403030c 66
    0x504100c07008285006240003490000304401e007846260b0350410541c002550311008807000f103281040c100084260350300c0221401c601b0100401c0c200c00b90b0b80241c50034651048215001911550200140286444810b80340241e00a40c040f0115454243c070000403004201406811807800c0001040e80003140746030110754000740300380001650b403040295642612a45a0390683d03d0b2401c129090708039142205034010b1000600241e040c0d243d801810fa500f004075011807843c00922150a0501c000d160b4190140101c00400309800c00300e544010b1610381e43d40b04640702a01220b603500c044401612082d00543d11800f2941810801c4006601c40c2c200785132600f80600c2e0929002800303811310192102c00c1d0320000b082e0414803c00036800500000e044e824180680162071100d0f94883e03106403e0301200e809045855002c80400e402100c1440c6001d8000301030b000c21b00003c250f418080040129078402080c0301c2240c3c6401480280005040300e4640140d032030406207130103022a42c0b1a4401c901f4003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 501523848 1250 501522598 501522601
    0x10b1c0e0a1b09020703020a1203090b180a0f08181c0602091203120114010309020901140d08040807140109060512191404060b0f1003360317 62
    0xc15000c11010307855688401c5100003401803202003401c1500c6608440c0041d40b0100361103050684c0040c06400030381c003d82c81e080c2d445161610840075507401402c00f802e00c0d030b4110080354214105034048120b1440050940f601401240e80d18452610030507000c0d00c10032000310b1002101501d65104502120041b10222029507101520b42070034001c8030000b5200580c0403984140d90340b03400d80000c11080e08603099039a20f141070149011030500078004d859807a1500c02541069500911848258607002081c86007541e10309481d0300c1e034510003049a00c0c3c200c032001100500003045000a40041c102241c0504442c50030461603189002c1000c500700c2c1004000382d41040032a400c40300310384900e14000d140650303580c0c60002e904080d41c41c0c5203540c400d5514100501d12410008100715018a10a0f601884128000e108010b9074408517a1450f40c0420fa00320300141c403e01070760050240740c00a4118082201d500402504201c208100c1c0c84080d000b203603148002c0692200140100001e01001170085 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 501525098 1250 501523848 501523871
    0x51914010207060f03150515030f06060a05071509060203161101090308040320060901060501020708010e030a200a0c14010804111009030b0c0417070e06010c0f0b010b1c 74
    0x28041360b401e91014150b50b00629848525101891400381c007001d4418680060460302092076944111030b1000d007803d40fa00412103c0c40e19904440b01c10034640e45443c141013464443d0703501c40d18030342217a440da0f40d40c80b84204d0008200b03001862040030480c4400818060001c3c0140810f0122150202c080c0d150401c0d400010b40c102c00b200f604180c040c40c240d003040250703100b942c100c1118402030000b40e2240d9000c008940318150440d0043d00d00a0b0700769800603a540c2c40b040c0c2a108448000159900203115588072107100c0d42c1c840580c8400790440e0a80800d95050403420100d070501c0c1591280c1051005100590051071001c1d004002807800b14400d1910f521103a11449507503200e01d00c04d005802e0502e1100c4e102c2c1c1070300c401031078110621441070f05240c01ca0400e1a07100380301d45054115400d40c030070f84590000c95504111011756610421580e01c44004560007d01841c089910051412a00000c1460814081d010b000302a00c17042d41d428403040b10308001c12016581034041410030024050 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 501526348 1250 501525098 501525107
    0x7030c091505121b161e0c080705030303010515090102121c0c11060106051b071e080d270e2403190f301d0607020d0c05191401020706 59
    0x200107412403814070b000d815450701c6040100e080898080c6c84200840c81d50034040d207a80d02c4812902150225000c1c141d41e2424035490f0b01007482030390340c0064031403004031001e01c4403c010400420140b041e1a680307034450f1001341d52500007008502d113004062a8442984000307209180a40c03016041c40e0050001c00240703203554a505009440c20440e0209815180e54141c0320304070900c4003004142d410207511440009204052820708881042c10341c2000580d00e0404181c0f05940d100d540d075050102c1d4142201c7c0400f0740f08961170700b00112001c4c5000240010b0344611180541c0a0103441d00c201c02c101180c0d02001806c01001d144a50004a101006091540031046130b0f5030340041c00718201c1506060008462801d400d1420700d070300d18007811100c852141c14002c01c0410443d100c0011010542802d43c40c8142ca1202c141e410103401c2042c3c4005d49813014080000a20510108800f640c4440c04103c100403030b60089803000000190074000d28030107c903072810b030311401e100500c030180c9810700040 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 501527598 1250 501526348 501526357
    0x2011d0a030c03140c0604050606040506060d0c050405090f09010b031b04050c070b07080106021b0904030e12010f090c080d2106031e0b0f07020607030c091505121b 72
    0x3002e00080380c1141080600510041102026500c001519801c440f121962122400c66044645014820016017070345080d2080902445018040b9802d00380894450710080c4821800d070000c0c0a418800090700742d0b10a00c2a41c85030001440e684050700f0008002e40c296001c00300664800d402c0307400203c46040e0300149490700c9403000c50b80801c01d9111710000403050300c00c022001c2d090140c8002040074464011158170304881c4a642224400440142e8050070038200144240e071001558012401003845400300b1161003000038101c80680025491060840f10718015400322551625580e009114616101c01c0080005e01c001e007070340c0b03948220001d01c80905544501c0b200110740d420101c150034580d00038405035601040d1045e00004546050241c0d00c543c03902107562284200c0000d510500071031030f060090695070000d00b40f50f182c860b4113902800181a1003000c0100c05100007800308044035989241400c2900d540c0c0e030720041d0008203072102000500300341090000641c2d00d003c1c4003020080301d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 501528848 1250 501527598 501527603
    0x1915060f05090a03020604060801032a050105071407092c15090a1502030105040506030c010f050a050c06010b09310f02040b031e0a090b0c09010201090b0405060702011d0a 75
    0x4650702ca20601c002416031200350000b94000e200850080781d03079600400405e050328020b400c00c0400080760055440d459101e603070320200d052005c41007080b065001d103028086a030310030200104120101100e4070328005403a4492045943c031a4002e941142106245407404100540048003200035481840e070b8407002c11600b01160750412002038984103007400104801c40d400020004036601409140001c0e4001333001e8180702d0f501d080041480c6280c00a8040f0030580107031180c814001101801760f400d90407812441c810310804104034210800d01b032104501038894916203e44031840c541c02d10098080101074411250003c13850344080741c4841e24104c0d0071140041021400050f0111880042d00445e0301001c07240c2008000e000860200388134200110107085a050740796036401c180b50055a1200300701030010340e83d410110304100704200040c41c1c280418000403401d05090350390501136200441d07080d96582c01a0040c03140003582030280034440d4911403c4c242900040021040d22503400d800c00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 501530098 1250 501528848 501528857
    0x5030115120305041215050106050903061f05060f0d0506060c061503030f120403030c0f0905041a060a050c010e01090c0b0a110105090705091f15030905061915060f 72
    0x141c02054820011070340a0035103202001405920752800d004414821410150514200800441d2891254085c1c440010000b0000c0540713440355400703418110b202c601c282081e07229146d000f0a06490340e400800243d03c114a2640e0b407910107050b40300440c0c070042c0440d07110b01c03c01c0010000310340d0b00103a03564101a600c40c0040c00890366000180c17651003800c00140498002081c10a0188036151a2a100303a02946040c08407042c9494201d42c0d40c14058080760100e040d460081c4124201503201441d00200d014021035082d081d4000903009420211011000031400100740154180a00480c0c40c2c00c40e4075802881402d600d40e07100456210140500303941c402c80800d007014401d00c61240c1004081c1c03020000c020f10700b0b000c80020b498079445d0040d10700502c41342d00400c0c880049514030080ca150b0318000d000e5818248181c080040c0d460100000c101501c0d4a0b9000c0450007c0c00f20f1400782c00380e51040388119400c1e402c034400740c071410340460f0010805003608002003a0003100001c4080d07104d241 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 501531348 1250 501530098 501530129
    0x909080901050a031404060b090a0e0303011401090e04050307140d051206040216150c18170a050d08010f090b031002030604090c030f030318030c0807060b12011505030115 75
    0x404c500038008085032502d5400088140010306c0010740c810442d964040d620b403d2541c0d41e04c810b2809031800384240929030f6000b0030041095800107110440c0d41201490003001082c2d803504040c003940320642e0107440e15040044c0700c10401020001c002c00003260300001d04079503001c402c80074006001c1c1d841e15015503042c620000e042035880d40c0c101e0b14083c0720190b001d9146102030402c280058050010024402c2c42c000750403d41d98001c0541ea030080c2e50840510b205d9509000c0303a15000c2e90f44090a210340d100d05808400092000c2c0607180300c84803e43d48040b5250b241441052507000ca07540489180c42ca0102d4907800d81d2804100c2d00c0262030444805130341c030b8481002050042903000c00142580c01d10700b40100401000c410001050384c0282c0d414070865100501c3c245504448100060108070482540400681c65802134402680603a50002c0d100b030192000c0b80d03024401000c5c84149035580c40b000341100a003080d102025203800d600810010703d04c5085030a14101c90300a49082030403015 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 501532598 1250 501531348 501531367
    0x60c011130131110020c030105060a0320031e012408031b0708070602030304050d17040b040c090203090109020406091122091b02190b0f181207020406090908090105 72
    0x104070f103000180103000c08200c8810600c0c025218154002414800d5090002240d0945081c10901d41540d1700300314403d000c031400d21a4824035400e03030102c5503014090007000c459030303c95450a1400d142000c200100c1c0c0907030041d071401410310b0815034100200020582c2400f01ca4400001d66805e200f10720340211954082d03103001c40c5050015402501980f00782400810a03541c0031000c0d40c0a58450002c6030180c00f000001a140034105140b4150750039150400940840c1c4410503458020307000d00c801a11040c0c940340c0600507a03100300d030300000070b81d100c60581085042920644005000842041195030340c0c800380080309114461441c104121a014103c1743c08a45e2000f0320300030304200070f0400c0001e0488031105411030f860007046c00076000b0301300c00034001c2d0502110101029440003190743c00780c0e168203286a15032000307081468403d070300043d4841c00ca001041182d540d2124501c0d516103800140c41003000f52906604282016810f1004540002c0c40308406d0b140c4c102000d00308281c50700501d4 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 501533848 1250 501532598 501532613
    0x50402040e1f030503040f03170403050a12030e0604120807021623033a0215040f4107060f02031315090503010c0914060c01113013 58
    0x80c1c10241140c0000100040c1807120447e05c81c00310f074031640a46010040d0381010080034010b41c4809001600500b680d800052408802c0301c1c101400350070002560000001070500e403000844c1c049805060806910781180e400c1485994420004d1000b01414140600d000080260a101c0c1e40c69011400c1448444005108a43e080c0c0e01d030050101d64896a0700842c52030010710981c64080501190549031020343c0064100f035004216507002402c1d21842180c2d000071820b8014002e0310b507040780503408000281c144081e08000080c80c50604a6641c10040f40c612803031080c174080c00e003032540300d1604856220100b0803000703c4009082c111408000301409034154452006080d0990003002c801040d030710030042c3c140c004c0344ca2a5075000b46507600da50a1608079100c41c0b1a100101d050b035001040b110f9017050342807a0401001c0c10513400c085034908114259101c400703600c06982004500300e420303500b449130861150041441100e0321505200c02d0360422441c083c0440b04101701c1d03141e440c801d00101 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 501535098 1250 501533848 501533911
    0x231e060a092901090b07020105130b030702011506090f121e05010207120507020d1b0b0c071502060f0f2a0a0e1e062101030c060801050402040e 63
    0x350140110b80c070944161800c000281d04400c1d01102a00ca40c07001d651003009000103032203d1a03d13107483e0100a03001502e040e00311501101404030300d00f102145002100d0080c2d4015440340d00027282d02d1a03008051207100c500e581082c130030070000140130058030104000c48030880c0d0710304680820800d401c0c10500c0c00c0c0c41201560032901d40360021090704000056004010642c011103c1e4405001b049070100c0d918030415901030341c0b0400d00e5130324101040303a90b0340008111003040021103419988000c030030182e4020301144e00c0703250072401c0b04021003903c2c0c05400e03040c0302891000c0e00c444e203805e094595184001070508842c0d0b00741c010000f00e08a420140c06500c207182c03102d40e0000b07540c06000300980d03503009401d040b0005a407058500340508005071151880384900d202c003440d80d0b00c107005000c440d8200c2d20003c0d0101944e10700541404034041c03401070286005000c011286414090081c21204060f401a800b031803040008002da6000c07211b9083d0072810b0f080648894040d0309140c00b410445 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 501536348 1250 501535098 501535109
    0x504030f230601090507050427090b10050a050904170c0c220c210b030c09010f0e1303080402090c09040510090e0f0703060b060f0301030303231e060a 66
    0x25218600c041c0d5100002d50b0504a82503c0d10030300c4607507200c02d41211180070700d1185000c05051908000000c01e06103000c0d0000d8410b1100024104156469000e41c020055450032a100c8200405010380d003450319248020302800c1e91034491500302543c0c0d0781000746400c55807044540e00450040666003040c404601203000042c2078518010800b46010342c980c1b140c80905120320300d4070710304039401c034094595010307080303440b002440b00886e990040c0d0740906142c0c42c209905029050322840da9642e0b90782002d01918222080710314550400002481c25200a490500b1b0140d000c1904c4000a82c008480c5500c2541034a000c00309449820002c402c902801d403e0540c01800e000c00c100450001500d81c504031000600240099501c0c207203096200d0219403800c02050700302584c1840070034401d811850761140b014012070716100c21540f413607505403c01c2e0801c41c0003d40300c1210409032603042a03103c4021034003580b45062810240c540c0c4c103030441c0d5080e0094464a0a0000481c2941da000d0882e00401c0c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 501537598 1250 501536348 501536393
    0x30c0607260420030d02121b010501080106080111030f130303060801020705060708010f23011b080903060601030b0619020c0d0b1909080d0e070312030f05160504030f 73
    0x2028905001e1403242c006428080020300f2409400500d400180540d64900c1c58014180505450b0306d491560342c80441000f80d415042c160040031680248500381c000d0071540000074990b8285519282902d106400c0340001680070320134440c424041010031030300100d4148072803600c449d00c0d29007034000e400a0360180480c2e510100d5620240f00011515078441c60641d52844803da0721071082c00c0641200f8000c8500c0312103002010f160a126841c0c1c40c551041c1c050409180c0c2e1060701041d80784036003003020111074107000400c082c400c03810104910b503001042420288541800c52021807514003400703641404001c0c0003483c1c00c10042c000d0100710700007440506803c091300160f0a0040d0440c20036909400510000d00751085480d12034070544c0e130030b50752240c492417030b1846030640040a00f10010070303481c15004240c800800102005001404104241c40110781844201e22200c22a20018155200f081c03084c0800c02c034207507001040f00c0030f880e80f1080c41d00c80301c4214202200d020380038580111498 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 501538848 1250 501537598 501537601
    0x1120c020115260111070209061804030c05011415090403090902180a0b030402010c02240703080708090d0909020a030605030105010306060305161a07080723010b03030c060726 77
    0x31009802504a005035004910f80505024030818220f80403c3c000d551030703a4080c00b50b4001403520000301034002a00400303800000042c1092454800e1040e641100030501207442901000002e02440c01110404142c8004601d41200340058030800c1080e154456000c1800040415018400c0320014000401045407200503007440340c60031036000c21850b481a100ca50000a00451540032a4421b5906139545110b0110036400d1141d0703a007100d00d4003034014000c4801281543c1001e405005e400d80207a40b1070b41d150414000182240c0c2d0702509001da0360b00014500c515041e009140d0408541c0c1c1c81c0b400582e113080750301086008098076000b555241d400c12000000307100e27040d044081a280a00291040e042d03940200001e104028410208205c8404580c10300403004907002d40344080c01040d0341407a0100310f07691624141c4403024101080f040c2070001c440408402d07c6510782900c4160011850047d80031501540c404009050008100a86011928011203030301c18484040f008488409035 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 501540098 1250 501538848 501538859
    0x303110114011502190f0204020f190203030f01060e030a0305180d0501090b0c03010e0610030b03030c0717030a120509030c070608010612050106050307030510050d08030907060e01120c020115 84
    0x94803400f01d10f820051041c00c40c40b418040c0c0c001a010b4105503c00c0080d421088242c0c00d000107900700e106001c44071403040c404200100c0c0101d0f8861326200302507001c4c40c0e0701d00c1c000b040c4a40c246410380000302001a01008000591030000c2c03011071141d01800d03c5034403004198440084030610720341081c0c11240c4114070004101c015041443d030310307104a00700f16a585e81c2d040908690300003403007520318003030b1080003284840c18100000c42100c1d44030300d4003060088c1c400010a02c1d50340304000b42030047d4400b42007009040c40c0101d488070301c0d480502c043c41ca09101c0c0b01c001014600440c0c440c5000319524404105201020021240c45420304000c0d22820796a03148080e04c6598248070b00e00103d80c0708610a03003891240d11445040e07400c191141400c540320141c040b401042d008101380d0031202044030100d0243d8400ea90011068460400b055413403400d0003c850902200d903000c00d06000d212404042039030b811810840c0d10341c0c14164001645160725104a000d450070600021500c1d0b0410000b162 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 501541348 1250 501540098 501540119
    0xc19080f150711120d06030212060412030227060c0f0607030b0f0109060818031911150103030804060609050112020103140106080a0e01020910020105040308070201090c030311011401 80
    0x10021641d00100000b0b60b1202c90950300207418940081840e0007244040070107580c004003401d0001d440300400142d0a4880c0d01042c82e50580c1c5d603425415600220400007004031154411032035030303c00d2400354188241c00c0c0070503010041c02032034903000d1101005650000d40721035040c1c80700d849020044824800c50505655181d4000b900d000d030009052081440444c2080c0e00084503015040c0d4901e007600b0318180e42214003c0c0c001d4802841841c1402e00035110560410240115030322201070f440440042c404058103202c4440c0c030b0142180c11907070802403000000e1480f60304403a003504201009176150326061000f04400d400c10840c0a1500f000801c90440c60016903543d03d10030788081140207080146105402030900c500b03400200080001200700380c41e60040030241201100260400c0000702c0041c3c03092a1145003040103079940c2c0104800e0640c0020b13190f800c00b089000070040c20800d600d401c40c156406020203403d010000c80f0850307405c08254411003411409268030328080d6190030708040d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 501542598 1250 501541348 501541363
    0x210d0e12070f02011b051e01091a01050f0409150519020a0905211002090a0e010902120c0c0d1b050d020a0204110f040333090614090c19080f 62
    0xa00184401206255031a007250f140f1017510f4200e03004000010503000605000070f0003000c1e005140d500d685c8900009061800200505036505280300890760400b41400481044210301d0b0348500d042c00c900c0400305100000700080c052507420086202c2e030b603903c1070f061140640000d0250903840003900b0000d4540c80406901550710883c1d0040d941c100c03414903c0c59405826450719030a81242c1d0340c0c425295081d44c01041d040101030910700c502580e031002032399240b0f800d9005521842c2c000031070402c00e001c103184107540414110140c50412117007030b901c2a941c0402d1070303e210611400380c0494221001e04200c001c1c05950041c100c0d400822005402902c0d8000401d08078001c0c0c3c00d00150030400200c031003d460304014012400707820b1519585176542da0101403881001c0c03195600803210304084100c0c80c40904081d00b0040400c004c5000e24201080301c00d802c400300c0e001501502131044000e80803d901d1042c07201254401070980841c0e1030346042c80c980f40d05c86400c40c4070311498104042c00c0403540a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 501543848 1250 501542598 501542603
    0x6030a14060103050c0103091211120a0509030d021c0f0306090f0212070f0e060919060f0e040606080c091f03140f0f04121b030908210d0e12070f 64
    0x49170080b01c464015000e980002030700a001c0c186085184241c03d2080c1c150604003801c4804443c0000490401c20040381d000210703003800075100084000d5035090822401400d06040d200030207040305410700c1d4081000a0781c0e40d04040080c1207107041159842500040c0c00745c40c0f690009c028a001088400c002903102030920100100340d503000900031806100e415a4600d050381300e00c06560312120805ca142d50000c2c0403039901007044400e0100403c1c0c0c03881e042d00901741a8a50000c10585403d0107055501003408261081d030810703000780203a036071090500e6044800c10350807980303480e00360300010454072998001d050016040810007040300d82c075070406003664002c1d1080c001c044d1181c000011200408540300c40429110402290000b8982907040310104501d01e800501000c80d41000c241c0d440c076016054001605101052101c0302040c0301e00c03200f0403034140742036210300c9912050340050702a00302a60005982c0b070300102d16100e07082c09001d10681200c003400396251410714109100d450000c805 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 501545098 1250 501543848 501543853
    0x3030739050127050d0f0b01140a080a080d09150510140a0e0103141c0903140313090c020a021305040b0906011410110f0708060a060b0d020306030a1406010305 70
    0x2018282000b5100005000c0c0f2005207180005040005200c00105841c00480300c00d440c084212010442d0200340501030f046210020b0281c40c1418200203081c0000e4018100750b403c000590340005100c242158840084018082100803050921100ca8600a0f80c90034400b8200000c0001000b4100c0c0d1510a0782c040b0142044004511020300400c041ea5016040b20108200c0c0148041034031030a0040380500c40d030040f501d00f10468440c100a0a01c07480c900000f0605080003441003020700d02c42e581401021800039801d02e001003000c4900ba10561007030000c0d0a0751a0004403100c3d1080c0101c5959a40140445260003015442040101412070301594136510304000325040403c0411428120f81d49024a0200040c443d003c0003000d90580903180144009200ba417245441c1c10702c1481c144440303c00203010401d01d00030b030450030315000514405106d0b140810500c85004d0000c00d81390003d2401c0c5005840e0741e10a00800d05d000d006210180100b460000c038400c0324180095243d040c1c910413820b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 501546348 1250 501545098 501545117
    0x933020f12070c03021e130203190c2f0114060f0901082802090910061509030627080c0120030f191109010914030307390501 55
    0x100509540107040b401040146030140420151030004214032004105252488884900ca000151805001986104c0b42ca40120800c08642000802c002d10011070640034000010304500080115000b01044000300030040b0080d140c55907000d160714012010345000b0805001c82114600e11440211071251181c00e410180010718180700300e1040c1215120302c001c202408030342100070301490001ca0001900383d240e00c0004090399404103140d000b10441c0000e41a20314044001d00e080d1500b54001c01082c4110b1303d02580016400110801160740099002500000e200c0e0f010b03800340350080c0048e1817030119035402e0042c04601001428005507101c003c00030f407030f26264980c1d000032031f07081d081c00706100610001d610381c11401540d980c445c0780b104440c400840c1407035900040303c030488403000310000007007600c09032540c00c40046005000d40e44552790115501c500083e540b0f20403940300421491450bc0e88072460042c2c2d204801e111a08080c29070285480013141c5000b001c0244980d0340012400303139 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 501547598 1250 501546348 501546373
    0x409061712120903120703090b0a05060109051e0d0b0106020615030304061103090405070302030a0b0f1f0c0b0708370b13090b070207150933020f 64
    0x34030350200d003809010342418012040c0800e600d110b4020925a603034001000006000b40101c01d499118190f82e84000a840d105404d0890603a24010207441480d0325103801c0c02241ea810501000032280d04481486d00c0c1004c0521007201c813941c0904080e048070584881004001201d090141a9502d40d800c803801961a9030908030005610f020058040d001008180202c522070644100b5040740f0100f203c0c503029540c0042000c9440480c3e0140c0005da0100c20320100c00072034050302e5030303141d400c0314880a1048541c00141c080d46000444c460242562751004590b83d0080d0b03c03041c80c2c103400c41101c1c020343c940094080c3c071218040700c1c0781304414400c141c40300b404910948440503520103002001465041a01d420f401025840102c95011420001c239284040c8140201c0c03403405d2007084464400c1c2030851021b49400307040e4101443d48100d03502da180c0c1c4543d10290701d43c215501c60000d02d8000c9001d00450262500d00b0758207400907038a4075a1603408503000214003446521140c22102d1f0b00305581c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 501548848 1250 501547598 501547603
    0x1050304030806092701090c12020f09040c0312020312010f080c1509121f02030112060f0209060c030a0e0109050a0315060b0c0607080604060506090d0f0804090617 72
    0x4540040105000b1030100c0d041d0b080c1001d1a540c41150100e00c00090815001c03040400800641104a1a0b448003039900800060040410080900200300403a401e016800603120552616059000b452000300103401e01c100f480c1002c000b150812200f4140e41e280d218001d407240e0101c4040e880380c440040c00000c58254410341c9800f119040d41c0640030104101c0e041000890000308000c415040c03e000110083c2d4a8810210941001200030070441032041071445206098003010300702d5610500040040e01c081a08882d000d03540141c1c0001d08540c2d50f040080240507412865811120110b01400076040000080100b01c160703480701c00c0e0202402e0011190747c5120b004454101031000d1007000007480b02c40001c007085000c404045809521103070810516000300d070900c0e145d58400300078030901642000200390410303400d41d41070013141d0410010a42030711820311801c2c0100301003502d03101480060100c41c18582d0744a612719a0f5169520368810260810f80104550031b085d04000b0074050702c00 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 501550098 1250 501548848 501548851
    0x3091409040308010506091201060b09120606060f0f07080301260d050a03020d0e061e0a05160507110a08060a060914010e1012060f0f0c0e06090d0f20010503 69
    0x155950042e26801c0170305029481c1c00170a0401c2e04113208280710328030641d080c0108400341c810140e98030749524400080207802c03035a40c5c0109006401190a1040580300d00048482118280c01215078859444402d5200c074468540c018051900100000c525151b101107015607403c0610b500d07001901100032000c0d240c202610041c030118100b00b0010748080d0180d00607000740c00740c0d004006800307001900f4a50600c1d50440f0224908240702e500380c0301c0302c0b05032410113810100404040000b417400460348140d00c05900c40c003030305205001c41e042d410443c40601045030b40a020f00004582039440e14502ea558009071800102c441c1801808218078885100300c00b5400901e8041c000c06074038050824071070941c0580185200e02d0030f52404903802c140c1000d030a0f14144030b80c1d00052102d03054941d200132030b500d0001054a950405d524012515849002c06038002001c507502503a8000c508000340031103800a82c004e207c0180fa1002006100c240500310a00f00c5100c2c1c228444c00c2c0c00e072401141c41e44070 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 501551348 1250 501550098 501550103
    0xf03090a0c140a1a070c080f060906010f30230c0109090c170711150c07061e110904140405100203090a0609120e10050f09030c04090309140904 63
    0xc403c01c10010f4010501240c1c0d13004030300c001164509483d6480351098219550442941940051a910360040e0b04004241c0c0c04170341c0e5005090107504011200b00b595803140b0400a0081203400200c120100c075940c004401e902070121000e01e600760b0314040d80d0151503e0a080440885650700c10003c00022a01000c03845050307548220302414200d03a240201030000b80c086c01c2045d0b459400c2e0156001400c0305000c0c1c0000e88445109800145130f6138034244040c455108418140c00034040320010f0101a82c95299110b14082041c01c0f03058107111071b203030309002e800c05140e0610803500d01c04440e18004008404081c0c506005058114030f60b14030011054400030156840031000250903929540550b40040d900300588490841503251002a2070b104041600c00c0742015101059450b0450070360001c03a801961580c0b5031200d4140701800e41e00a40549186000300001d00084655081c0310705004181e000f8410020510310b410300414412590013418505c03800d184e01070301245485a001072140360f = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 501552598 1250 501551348 501551359
    0x6090f0c010c0f0203030f1b12180d02030d0c0c2301053a05061509040903050f0f032410030b13050a050a110327030f03090a0c14 57
    0x580c40d100444490600c42d10554201c2e0040800d080160750a200401c1c0c0180000160740d00ca004c581e401c03d0f998003c034848048079610004512030101038007029a09121401c080d80900314a4140100300c01c41c1c2c440340001d606019005220320003036000074588540700d00500c0d0740f0201c1a1252010744601d495101c241c869040c042040100b150700c0340303009280d039682d5003140d10380d4004020712105401c00d140b44108011245a004440d06000318816039620910071161405004d105c410303075211a1040c02d85983c0119264608041070501032011203581103241d21005984039540c1c00030058a40095842810711480390000c10380b1404450008400040b0041c5a040a010309480a4000708400e0040c2600300360010840c28596207030740714042c401c025541002c112864822600030849440d0f82200c00d01000c144244901b00c0648040c03400d034500c1e000307100c0031003100400a1500d54010f0420b00b0000020001c100910b844020541c9038103140311305c05180b0071940b164520f0f40e0801a00c2c1d901c54000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 501553848 1250 501552598 501552613
    0x10b030601050d06240909061107110609030708240c0a0504060305060a031208010608130c05090705160c03110d030e010309080910020604170306010804060906060e07020c010206090f 80
    0xe1074660040c05142d24a2900624895201000072a000d40380d50000c406c040d0380c2c0e040f0005105a60044a03495a1614500c2d440c0644950325201c2c05203c40e01018000d10300440c000135151030802c9400082d10640c4201c5003002000010040b00701d080c5c28543e2210001203002c02e125000c8181550b60003180c0b911214103090810604800818000f003010740d01c5100c1c588000081007201404410950407903452411560401001820340d10000e0080345a00c0441620f10001c6186101c4180644200711500c2d415030700c4010044a4a020300081d0390301d20742802c0c181002b0070400c0a2184101e900c03502141c2182c2036040304018008410b807101070003258005c1da60040c2907110794040c10240307200f81100c07800d0101e02d40c0414004280d6451401c00b580c0418180014062120020088030415a44080c61031801d800000c00e00e801c040c10017018603807984040001c018080e08680c028100000d01400359140c913240c02942d503691462000e0250041e000421207008010030b100a04008840080c05078 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 501555098 1250 501553848 501553853
    0x90c05072001031409010218150405060d090206041811250201020a140c0913020f01050a031103071707020109241e1d0705031005090f10020a02010b030601050d 70
    0x41c480e640340308904041d074032800b001d4074007048080d1074099200c4000058aa107001c281e000c501c500c5041c5d80504c51000e03500c0440780c12224030219426108283c4a4540f1500540d0500300a00034554001b5072251002c00c0125446030a42c6020314040803040e024851100080d41d00800d0744582030b440224002e45c41c41d0311050349a00b0705080100b03807042c41203030401500b0f034503440041c0c998040403007101d40205c08d011002d86042c0540a40048901d9992031004042d40c3c0003400b000065003d040c14040c0105200d41864021760108203080303011142e0994920300454020810b002c000d142e80e908022650204125510510500c0000d651002c45031901d01c20829140d04404520210341c42d009491b000030350213036800d100c0c2c0c42945c23074008c00b00804c2103855480761180717202034040c445103664840001080181d50000711025000b50b5400300198a44401840900300300c60400c0080c001c0c0300706800c41802c00d00541c000d0080c2d2410303500800005102c0c00815894075420320459030f11001c00c4014802 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 501556348 1250 501555098 501555143
    0x40209060607051002032a0421080d050402270c091324080a050c01080403030209040507231806030a02120c070b01090e2d01020d0501090c0507 63
    0x204800c00400c240c0c1003030440d070b941c0742c80c10b4100e0514807072264011003481344405107100b84040c0e00344000c04807501e18a6103500703244280902c0c4161420034600004504404011180c40d103000382e0030480855803140c0110540001d008250380803402809003c600b00d0484081e085040d00d5000640d0a00400e41c8441b40740d02041d4110504150340306181d000e1740d000000080c85420078120342e10004403004500841403034824185503202d042c0e10f4000315046000903c010507076075241042401c048030142ca5030304085009001c0c40aa264200d440d0a05004100f60001c003554a51019072286225415034984101054001c000c02000c241e07100c075044850b41d2401001940e0b110450500050034003d2940e811101c0d4001503c030040c59110008107401446018100d01d0302404a954050004d4007070800469906c20b2140454602c01000791004081001407110200210b5070500c02991038084952029000b403c0a119142449191041d08044c0038003410a9405550b04040c0f18004961800301c80791 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 501557598 1250 501556348 501556351
    0xf01020d121107061505060a091e0302061b060a150603021803070e040b0703021306050903100509100b0f0f09100305010903030b0102060708040203061f0506071103120909040209 78
    0x40035120b124030003552404001811100f0300032603000c900040340c40c00080f15440160042e40c007a02082107002d84142d00a0340b4101115040110150b0344c0a00075090b401c0700601d5040254031800024869044400b01940f004e110807859082d29400d4a0f090f0940045860300f24003e440200020000c020440c040d0707016060b58661038050f00c45a68604001078106034240e000903c03210045030a100c14020300c044202e901640c0390500318a8182c40c0c13020722801130560b1003100708100c0005203660306501c06008252208241180038040c506040b068261225001900e107401c29281c0340c03001010b4504552400c000041c054102c6124503080b000340301d6030000080c608015000030500c004000340c024858460010b000b03550000c0c4030b0301c018000a00b007442c05000b49041026031403d22004da90041202034010940b40050700450f1200201c04e40c0d20300d001d620040d44aa00411980c040c48135105003803000840490035281444262402c0c0c0d01d15014a144039500f081c44840060010304141c00450b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 501558848 1250 501557598 501557627
    0xe1e0a0b0d060c0906020d08062d03101a090f0a022218111c020a030603050a0b060a17060c090d0b0406090507083f040609080601050f01020d 62
    0x84908201c1d00e42409440d420001d11001400d4104c00308a500e5061000e0041c0806920302a19a400c040000421154100300c0010110a5042c65425030240300c04040f14444005001d0b00e5400380303000c0c0f003800100000281143c01e0701226544001511344414201d10078001e80c01002c4450315140c00c010002d41041701001504454800100b00ba080d02d400d07280010300c00025064501c58103c4014025110b00290040c1c254006100c00a04140d07103080c2d1411000c00c9200041c0c039001110300490140880da800034089029842001c024026007011841c401c90050350585125940c960b00d0f2061341240c030703140901540028001c00c0c80c040d03c10008105920300105103003600e1100b903c0b10005010181c9049403500e030350341008410000e0900c8502e00414002000c4c0101400c240d4080c5488080c9007030120901c00301c5030a1b05401c0b403c0e507004030080c2c00481c200a071280e8a884000e0507200003400340140c05c5c850040001420714002d01d00201c040410303406031032992841030058503541e8004204 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 501560098 1250 501558848 501558859
    0x60103140c03071e050a182d020d1a0904081e0d02092103070f02120f0a060e010603021f110327030106060503061002010212100e1e0a0b 60
    0x8000c210380d02003048101900044000482400584000d410001945e83c400340c068100d07038200b0003110346601403002026012117004100c60102c0c0c1c036080d4402c80d070944500112185c4054912a042199001c2d022441e500e2404100e540300844120024940c408403980c1c1c44107500c4001000105070001806103071201583c0041401c0f0110480c00c1d4039042041030a0384103038003103200f910030718248090261601900c058412001000c0c03109a841c2d00c19020080c0c03c120220b82058115111042602c90075000c110682d94240001840103450700503508064902508200c920a80414188540b000300da5006001c0045140140704801002c00310303a1500c414480083d1583c0f2040c20180024495085011320464000d050242051410704034030f5104c600a0b03242c40d2081c412180c0010440360002c008403240181d2030341c0b40748100d000e445040750361820030903a4801d0107503000c08415082c080d00ca880d220300c00c459595042c601e41c03410a10703160b243c0c05000180402c0307a90303e4a40c00110300c0c03c8090003 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 501561348 1250 501560098 501560113
    0x30612051903034208120901020307020301020c06010302150f090d060f06260714061630080f06090a0b060c0d08070504120b0c12090d0e030f06010314 66
    0xd151801300c15090384081141c3d0400a00400300c07500400382080c10000c0303500e062203d08184001e503a0744d044408a0b02d44150004d4515100c0e03008000b600d015590040003955140c003240615a19040c0070300c4100d01400820f00417540a203808001d4410f5141d50010041c00c24038514100301d11041505001e82d551a641c2074900c51000d40d5014020103003508040350398000620004611603e628400c00342d1041d0030400007800071600c0d210340070800b034030222000c5440c0c8415540c400034480703d15000421210441c01c0c0c01c0f59460717048440304420300701c02414180403c2d82400030b07100c090303080343c0542601001100240300d519082c80029000043c00c0800a803000e070300004a61107901c05010322510b50300a0804013001548250f00c503901024901d013231341c03c1610304114809224100070000740f62000d048005241410510150f5030181080649031000741400030023141c540300d101c000240001c0c45c580d10404c0b52f06002601d50f4120760300301c000b407016a1954948082058224003d12402e004010703 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 501562598 1250 501561348 501561371
    0x90d03030f020706050105190302031b041b09090605060c060a090507180506030d0207151101020f0f09010f0807090b03090f0a0c1706061f1e0f03061205190303 70
    0x1000c3c00c00a40b00d0701e0700140c5941000c003042151903000b626081030441c445d43c14030060b20301045810003c28420140d0091050720303070000e4040c0c1020010741000c5d1402201c00859954066000300480740d1102c07081103041c5d155130a008152003241c0070620680d012101281e41e8041542c89045103900410a444026858410348005003c4801d40324900d25117880602811307140900903200020042c2c001410345c1d5191041c40b0391800c0d5580500fa040c80102d01d0030b041c0300d5401f1b40450750b80c541c0408a40d5a160340f100b00b1000c07030b9040511007500145107100e01450701c900410f0003500480e2035481d001c0895250415060555200600042880c060072020100850302040301c00303003152054105411460400104082d440d11499000603554444010721019494403481c0200400d0080c240c1d044038403041400b81c0f4031104035a88002040c0702d60032201c0410782d0080400785d19440e01d603018441d40740d071148884a19024800b01402d00d03003040100a41c200c070414607090540d482070601140400350303030 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 501563848 1250 501562598 501562601
    0x1e0c0a14010c18060f051809070c05010f2903010e030a080609100302151602030f0d12050103050c0409031b050703060c020616110f12090a05010f05090d03030f 70
    0x180402002691180240b074200d5820104080ca50a044907880b1070716031400c0c81c01044500740c454004284200020345880000c100080e00e428900e02500781c0c2113505086900604605901341d040c0c0f02e551034a8040c1051840500506001c81200c01503000c0b01c1c014072118107a1114801422a8159658618440507460901c050401c1581c20b07210900e1310314060060002e032290003403643c038000c5003d1000f030005a40d0b24040003948001400315a4070b8a80d06c3e0810003e281c0e481c00040d505101d03511030700c00500800144400400003603500c4141620800c01c3e013074281d50003800002d1103a0080d1019400900700703680308240240c040d03e8808031440c0151780314010542038aa003075941da08484424000c0c0714003409608144440341c8010096454944c403541c0028451503845020040700904216524500308070f240703c110010380c1a41c0c1a04180e0a000d0065801540c506015240d60000014658010440090448040c0e11400e00c3c0440c18001c02264601c0d041c422000c0c0742d620202e890201907103 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 501565098 1250 501563848 501563873
    0xe0105040806010f05010e0a150309020f03060916060f12200c0a020102121c110d0c0306080705060408153102130e0d0c1a0403020607141e0c0a 63
    0x204c2c1300001415081400051a0742d21444909010b610b101f2010004042c6d6200c4000c010012480c00043d45030080c400181d00019900c01d4540c180f00c0c941c2480440c4002184500401300d0503580e2074005656180f040d190842e845081e0300c0480c00440b0313260111003050b040f00c1c3c5803600c291101d040525490300c4c040b0b01c40d00042c04407400c42d40078546001c1196010400943c90b01c01d4444035a040c41e4240d1000d01c02480d207a0f080300d102c90b40310440280240e850106440080c100e441080c130840942000040081189109101e040d1242480000d03160610b00d0440302500c4115001d00000880c001d2850042640070f4100060030100303c2081c0c07810561005100c02041001d12000c6400c0014010003a100316159880d00e282803810340c903121080c100149004101589040004400c40f1a0800e03400c0c480c3c0c030102200103402c003103040004165004c90f01510881e12501e031030304030803003205d003580ca14000c07942c0d03451000140000014101540702c2c041c001c0484041c04640049440c4c0c1e41d0880c503040d1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 501566348 1250 501565098 501565109
    0x30901052d0307020f01060e0a09052e0b0d0201081816090207030e010e0303190215041b0b031302040905030d0c03060501020d021603120c120e1e0109060e010504080601 74
    0x1c0c04010b010000381c0c1400307010184c0b00440002d1200600f00b802c0c0201c42240581058138a03682da903082e60801009001d226511408941e11b0117050030611801621040d0700c1003406400f902c1c11111448901d0b00208032050b80d50107a640b80555a200c2070010100302c000340d1040c1d41c5100c0c0700300304070302c040400403124064007245a0260719003001d458003034820010442003034140200c07505a9050b6440000546400d010100e070f00c05450b01c41500d050381000000f401e0181c13104019010002440218021400c0b40c01038034140c0c103c120b660b8455400c2c00e00003903414424989026440501501e001c0d00f00000c46030040301900c0c544140811000d040391100300c148000b0a894640c2044039680600010042001600240040075195416031100802c0c40c000207244055210b08024803510540c6c02c449401d070712001c85480190079030400f07055000000d604920807151800280d00026900c0042c040d0f400040c0c5602503094185581a10510070000001c6d04000f01800000381c00c0f5010883c2d68000e10 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 501567598 1250 501566348 501566437
    0x60603020703030e1c08190603050102190206010b0d020d020c0a0f110a08070b0307020106050d032f0606090603011b110d02010e0303010b0304060603020907050306130c0203090105 79
    0x1006150180c1034801040450415400025407034103c40603018030b690103a02c980c03034450842d0f40c4114400100c0c8410490303203000c1901d0b0088c04020000e05500420a0b079140d10038008000900c07071812a5160000d0080c6040340300113000281c2d04c17101c0c035000b0303000c3c0f040068805030034401e00205052500805944c20b40b49520201490014070a41440d48040c07080f00b600e405501d40d05290991b07a0320341c00c500c24420b4006002000070302c0580b003940914090480141102803125050070300034141e08030740d08034200303003c03d8581a15550310815581110319140401a182a5590400304100c400c00101900c2d015503e94101601907a041c000313103401e00108e074035182c03c0001900105894801c0004005c015685450384482c032082001081d207044400001c441e50356030b60340d031901002034042daa00c002e400070f155400748a040c0b500080070394800e840039120b46480151811804c01a600124060760260304100141c02c020351146005010408030044034540c030740d408c0e01c10b010468081c10f1070324017000d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 501568848 1250 501567598 501567607
    0x2070816030e0a09020a0c0228030b1e0411010e03011e060807050d03080412020a05010203011508090a08401511061611010c0e12120901180906060302 66
    0x34074281070103c001c0d102035002141000501100038285100e8100d000c1d109204104c000c0048410760401142d84605502800c81403603920306d00424111426113109001403007080e4920707214043c07101729503c2980c000009020040c0b0303030340c01980d074a5070010007190155241d03061143c0c83e4424180d1880314844800300000c1a41c54440d007942060010303003016125140004240c00800c3c0e003d0b00d040c0d0000d1300600c102ca25641d410303400780e00c0d00c40048801800c5500110002071440c15a0081d10388055480e01c03148165501d003001c1175112416050700500b1524180070031403800c45410074018144000c03c0d60848446040c00c262108074a9006851100d824024814041c01c100c0e00700341e0b88810700c00e0424088012680920903140c0f00020451500480c0c08140005c1c138901c12014a443c02802ca8000c2000c400386070030041c0250380210301c040c0603844441c8648141800014201d406501e00380c440c03400d01103040e0044810048204035001c49c94201d50021820032403d2003101700401d4561401682c0d07 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 501570098 1250 501568848 501568877
    0x4060e010905160803120606131a12060607050a12260402190b160312020c1501050d031b141002120a0501030b06040504150627020408030a030207081603 67
    0x103100581c10005440e041442640c21601c1108045500080101c50f070350303289d0005d171aa25401d00d010f640403403c1091151b468546541210005100c100d00c6000320b0051a5035207414000030748183c1c00010102c4e407081c1c41c058080f4240004601d02504245800e0f0703d200c141e4560b002d203081050b1040101505038030144011460011504002c0d0810f803414080b0304c929144c0503201a00034000655180002d81c070522040600c0741d540c1c03001d205841c850840d203840a5500c040ea40380002d41c0215250356070380d400468246000c42c55820000d40c0359480055055803039116491421560f641220303c01110b0400881018052103c820f07528450440142c480e6202c40e405c0c5080a000b901d0285071900d010010b01c042260501c0c0194080c0c819200031400742c4581c64006803180b00d800c2c10450b00d5103484c00c00300303407010051400c0d032000040414030110030540c1524101280302d80c4c442d0030b145920810011214070300940140415501480751a418541c00403261441ca4600100440019000f500f40100 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 501571348 1250 501570098 501570133
    0x30a030323010503100203060a0f091a03030f1806040308070b071b020901090504030e060d060810020a02060610030905011406010f03050f010501050c0106030f08030601090909020d0b04060e010905 86
    0xc0c01a907124508590b07514210210303850340b41000741507000c81d13000000180c95460700d0310503500400c0743c00f0041032019a0b40142d500200b46070518142400301501c284011864000140c41b810105139481c1841c22040b04c01030a41c0c01c24031803000350001d00c2444000081060000506501d5000b680c491000d40784c1000010056140c1c039407030481103056500f980d800341c3c07a07101e0000d0659070300e2840061503407034030300301030320040050440150300c002c2c0012401000d24464100304100c40c5280708507295014420200c0003039028074a62400103a00130b0303000400503e00f941d00f20344640c0d800e0800003010096603c407142520305510050000c000c4c040140f0030f16503848158440c464243d0301c1c040029080125920761501c1040c880d103410004082581c81702c9400c298485c030700440e4041e546e07984084180c9400c4019401c00c45000707003c604a85000a0304001a01400880713560042c145503c035001e41c0d4a281281ea030103003003580c416a444800311002d14091146403280c5000745c0041c01e607403404a85a85 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 501572598 1250 501571348 501571391
    0x106030b040f290705030c070203071502010b01030209060307140706180c2306030c041e050a050d0c0e181605120c01120902030a120c02090703050106020a0b060a05030a0303 76
    0x102d50f42044040070403650f00500c07019803c600c0d90300d040ca580742c0300c0003030300e90840c00741043c069414003400f24002500c1018441045415900742c0003804840d00c01001541240998021950000310030030018241c544941e500d201c4081e00c1d284042e04102868803024100d0785e074403d0703ca07540d01d050102d81d0203101184440200808407800200c2c0da4114a1a44500d500c07040791902d80034807030110102d001810000c0980d4080c000b00180d80001c624201c1600309007421a1090314052141002c0108040c00c02c020740b503000c00d0b00180740710340035440e0980c0d0b540c5d180d80040450800594070f0340c803010355201c18000340801c1e03050102c0c020b40380760502007000014480b015502c08568440040300b01503981050030081c072076140c06800203a8981500100c0d00308200041c0040886002c04a40351065402c4021403804e940287c0d0300c1d5007607a070b8140050302110000c0c041c400c090f07804054420000ba0340f44a80584c05100980001c05051707448001c6454035028080032000309484405021503550800c5024 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 501573848 1250 501572598 501572633
    0x13061a031e070c0f0311030705010605040e0d091505040e0f0901050a0c0e210f0601060311130519051c030206240111070e040f030f081b0703020106030b040f 69
    0x60910b0500b6400500b941450500c02810780a00e82c0054092500648031240d0805403031098030350b22121460928024000f50142c14403540c0783c4109400c0a080c0040d95004c0604075481d0707140078a08004440f0700c075003c000145403c11500304000700710a141100d0450007558010f0030b131a100c0c20210358032802e42d0350042a2103400b5150400302c81085078000700e404581481030340d03058621302003001d044041000142c400c01641c801d038001c8407040d800014203030303040f1005560100089046020414198031031400140d20b0840011024096482c04036801303020308150100000b50103a0ba18045020250030045180c0840d004107065000c0c140c0511030990321038000c64051440a5903101c090503180684100c03241045201051030a01080030002400542407002c401c888514052130850452441c203c0101e001800c10302841001c9801904828010400c0700c40400d081408103086200035040303801c041d81199215640040800c0980d0020b5000700e01840309000350420504004420b0703441c08440 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 501575098 1250 501573848 501573901
    0x20117180a060906051b0d02160203010905060106020d0207030b0a020c0a1b0f08070b04090b241c05100501050c0a1a01090c0507030c0f0221010f0f09020109030213061a03 75
    0x11410100c0401f00d0301c40040301c502c01621142e40300e441008070005000025055882d00d08100140200001c80340e0403994076600301d410b91003025204a8460b121403100400440c07581c400701c0c40c88115900905107465410341200c0b520101c3e51175100640803070820511210003201d40500510381c084202d030010f410b06000400d0158500b064029552041c2d00c81c0c001e04a80c0c0d0180024030b542e0722014802418121071440d80a1940105030b50000e070f00540c00d18800400150402c0c100e80c00314055984612901c641c440380b06450a8010365407507201d1102c00302035000e0710b81190006000035650302c3e800e00006017200c0980d17040c2034170001191a42e210810500505100c5100082c2e44600300a442c00e90200700b4043c5078803a4404103c0c50b94034440c07040e00c06400c0302d5458501d040c0550010008140c000001e114800080c0190000c40720704440103030010b4011340c0f05001504101d528014950701c02c210000710303a0396490b650700c04180b13018620303400d100700003082c00204d98142003e5071620b9055040c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 501576348 1250 501575098 501575131
    0xf0c051504300b070f12060503061602030423040e030f03040602160206120708010e07170910021b071d240603100801110403020117180a06090605 64
    0x41d001210440300c00c122021400b07003500380041039508802c80700c1c5540c01100c01c0070380d050682016100e01e1595204800141c2c3c0300481d0b540c43c0410b800f80782c00315480580a0810ba880e603030b40e4101c1d9030f54840400c02c00c0d071204000015a040401d221404c01d8004d0142080101d581d120800c4140ca280f1302910a160b80300780220000c840c030040807a034201b0780c843d40c01a6603003030785410348d03008405044002c0c2d0702420110361003504000c031940c807074402d501c5580e030311045a03200d109521400780c066802400290700061380391a607140d070061594201b11080c0031a032815035540d0300842664082240000d201d4200c50021200c4003082042401400350505180b030480483c245c2c003807884900810018120711015a00c0c00c0e0707851900d107041d250110282025569140802d41c4440c801044e1103003040c00d43c41c00d54144034400c4040b0941c0c040d00c0c2c1c16540c13000340e070355111025003a5450144c03008480740c2d010030031401415000c10207a40624407030040800c0300fa406090100848000424500c12086d20b000d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 501577598 1250 501576348 501576359
    0x6080f011a010c03030612030c02120a050318010e10020304231c06090512090a060e030303131a040b04110102010513150b0604080304030b091902090c070f0c051504 72
    0x80d07090480c1002c3c07030304070300b00702c054101100178003442d61100c88122145c07101c00050584c4070840e2021780d03009803401c00f600c1d02e0a001c0d09070350b00c118070409003181c0c000b0301c00703100e5203140040d0b4114120030514244452900701d0340024a00361025a80e00e015034800181000120400d80b00001020424030281d4801c5044501041d01141d440c1594403030505038100080030003ca644c0071808464110089880c805140d042c0c1b002a5070004006a2040c5581d210000c2c49a214901110f880030000d0040c508644440d0789200450000300d0301180c036441d15217030002c01c014104441521990040c1002c5000c3c0c10982810b20b09003120580b0740b41164101420405803ca035540e2103604958410000301980000301c442800034000c00311a00d50003600010009480a000000380003541c3c0103412003c50398444c201529a680848848403081c8500702d2400000346c0780101740c866001640c0c1194038a080d80075a954502c00706d42d00000c41c2e0080605800b8046400c12a070002004410310f4a918641030400 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 501578848 1250 501577598 501577631
    0x30303010e16140a020105040312020c0a14070302151207092d1703041e061e0903060f0c082223010606050319021903051509070306080f01 61
    0x40400c52002e4a0207441d07140c003440b9141103010300c80706070708a80d104c0440e498003d02918003541c00380d0006120203d1400750000901c00c0350716040e4000300030314001070613640c1e10007044800c4448422602a403140080540c0f1040b410b0541a040262840c0d1b8070301041310122101140030b0001c1c4100000501c044c041060701e0498022403d0001904000c1c07072080b0361044038006d105400c400d0343e0300c90b481841420342d00c0000180c0252502c551424030801481c0030000b901c508580b0078000010058000450314810413039100c0c00c000c48a24000a4294594030303824103840c032480740b400318540d4036111030600c030b0790000c90b040d0481ea40000b07408219440c2c0803200380d103c4e28004080c1c00179401002d40c0c01c84000210b003140032039000758000e02c0920754803500640710303820854241108010700c859840350218a4400c49400c0c81e1125030701ca501086101044008090081c100464060f40b560001803565814840302c2c400d0810382d40c08200ca43c1040c501c58100f0000301c980340003aa06080c02001880040c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 501580098 1250 501578848 501578851
    0x160515100f0b0f2221051e06010b16020307061101150b0a050d090b0103050d02120c0706050d0915020d0c03021303020f060f0a0305160203070b04380108010b030303010e 74
    0x7102200701181c0e62400e403e0310450060380c00140025110345c40c080002c0907035503c100b4214001c100391040d407840850044003038030080407181090303000b810040c0b0080b010103000c0c101b03070b0054109480d4108102c2e40030a191203995001480814580c50302841070103801d000b1049428804107215680300d1606100250f03a0141003401028040080303804201c452465100784281d50b00205071820b5941e49040294a4031300c02d101c0340740140100103a1940034451582101c550600904c001c08000c0d04e81081100d8030380207242c2e180c0c24a5260450b001c0807a004842d0901c0f60340000301c0041c1d6030380b503912000013143c4d0900150014580140105040c103411854803c01b180d8041c5d0380b040810201c80300160003031141030006150290080b8070303800320552591040c0d20880d045180405600e5205209076682d0186050003003c107107405000800040020b071102c1c0c84880049800c1c14180000c1c4944441c2114010300300c44151590801000310480c00d004a01d860f48098015620f1035042c90301000320340c1d10 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 501581348 1250 501580098 501580117
    0x6060114090904060c1b0302060c0310180f23190e1009061a060307030c050405040207050f1005041e05030904050a1509050903160515100f0b0f 63
    0x9290500c242614880c408a03800c81030020480c90007850a032502c04001e06001010034001404020b54030100c005000c058501c40e41c15400408040c0d80d0603103071612076032004282400030840c02100151400c442a0403142e0410072800c04142d450f14048540c04542c80340c1c8640b507081403e11a019120700920100039004010307004020019205141000050705080c41413510500c10707107184502e018030075404064001c1c42a1300074852900c00906100700200c442c038100c0c4c0d100d074080010400f8507000754001c030301c40e115505001d818039946c1c3c80050102d810030241a60b0030b4001c42c10200c0c4d240b6041c405042c018a80310010801810a502c8880c000c2a0103049048240300545140c0188282003094804c20340340203105202e1403034503a81d00c00182411a005c0040c4e01540c20020802e283e09010301446201c00700000c44c2070000820032002e2500007058251694010461030300c0016029038221403142400f0006808114607044010303288a0030b91f030001d00300400a02010034400101803c40c2c00310078 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 501582598 1250 501581348 501581357
    0x170601090b0d0b1c05060604020909060d0c0308130e16051219060308090f0103090b1f0e15030d0c0c03030e06160308011805060d0201050703050d060e0a06090b03060601 74
    0x40c2e400b00300200420070740810550051202c9484c1c204541d5a070040400d0901c20025a469511940305110a0340101c12a840d0300a90384400a8414189a68015605805140e4180d0341964030f441e1810b541d8000a9851641810707a5001c2c8034080d0038402c8280c0207031066038822100c404e001d80081c041c0c000e411300b9150000f1401c0204a0380000303161055841040103e040042541e2480c2c21100759010b0603c1d00c2c0100490b4010454944c043c0c0f01c1d0220041d00b20b1607104980d070b5214100d40c04400f155200180d00600100e01264411240352550303c26003124126500312030005041515001d0014070070400c202c4200b4100001031031420720708084a0741400c020020114810004609004803d03858110380217000186060560001310541228140d018601c40413011145440903950211055a0000c01317030030407480154490002007429502910b011420030031400c460314256034143c7e2003501e8100c01582445070108e40342c070070f9400034503943c00b003000369210003004640c42e818000c00460502 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 501583848 1250 501582598 501582607
    0xf09010b0405040915361a060301180f1a04120e010908160e0a0605030a082203050a030e01210b04110a03091707031b020109050a0308030403170601090b 67
    0x80905c0b40440050403c00d4028081c0380c440718643d50004004607182c0500035440c124100101111030b0305091120307040700700e000148503941240340c1c0852003c0d24440d055940d420010801c2e142021000c2d4070349115000c5003440600504000030706069001848032401503c3c0d00788000140003001c191406102401c1c4220148441801030300c410000380d010003200d0107480b84078400c4000b11040f41c070a582c41841960f40c00d4980b0030381102150321501075203800d94010b0b00c0350004160340c0b60240060072400ba0441c2e0780c413010340d240300c465a181540200d80950042011008040c2c006100d101d44500030f01c0d1081c4080c0f02c1c9802030419080e07040c00c6100050b80c030b40161855451720340000b0807030b01c10041c80b26501c0001c403600030010084400c040d2821082000c3c130604401c5000102d072811509503071a06d514481103e858501c4c40a1040124140508039a0002d055110015500001c6002d092100d899183c9414050101c103c42d0200309410050a01004007076a04003190005950b054004245c58 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 501585098 1250 501583848 501583853
    0x8060108040b130c12061a060a050706061a030a050108010902010503071805030105150f030705150d02070203010c0c110109240c05031204021908030d0f290f09010b04050409 76
    0x905214201510f8074031312000101d8640118004c0b0b010083c17050404204698541040c0c01c985580e0303a40701544400f0412010442e0f511903000f4004c0c1c54054140041c3c481e0761000040e8070f0800c02800103071300d007c0200c200400d0345036600c1002c0c01851100300070300465071150300013419884001e0010040c800c00f4407060829890404c0d409015000141c007c0105040c08807070701d220302001d00402440351415020401f001d01b0302082800856101034110300504015007580c0860740c00000480c0d4455500b44041d4016030340c24010b9035402c540036140d50b4450b403410708086440e50307450341815040c002168010040c0c640c138040c51541603541e50441c04044241d1791401c1380c4020b00c0d0704000e401071001292900b803154046030018002c0d031088800318800300e400d01c0c80c403454280a201d2411960014802510003680ea0307089412000f007841070000c0e0809402460407030f0100b03d2484d03140e0f461200c4a200c0000d00b4007000c0040410411280204550700d410503414980c0304600400740a1501c56015008 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 501586348 1250 501585098 501585121
    0x4020a05040e191b0503070e0c0c0a05010609060509010506120115111005090708060c0301090515090a06140d0c0302191205060601020d0e060304260a11060708060108040b 75
    0x40d800070303149500d80341c040c00d41409031002d01c030f1028114540004c400c1c00500c6180000e000b0046400459583c8484c3c6e446481440c0140c0000c21840400c3c0140b40400002a5003031141d20040c1090710400141c4604001c240080e010058100500a03581001614610110030305220304441c0407012003026041622011100307034204400d048110320855103561022002030300b0032442100000c0c121904d603940c0c2e02000750340b030f541070b80d01288005003000103211615680d0841907004000c141c46544814a100104000d074000312402207200341c1d01d400c10322010f01c1c1071003c50a4800212040e0100a429842d0365004100c03500c8001e00c10f100c40c180c21f030080300d480040100144485100c903401040b283c1082601c880040340e405005004400781348008a0242110310b1b42d000c8007902460175903803955101c00560034154010000e9031864051405e081c010080240610313401c0e640c48000b00d40102410034031f000c60141106050011517000c01030a41d9010046646c0590060710f1601145c03102c0400d0303007 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 501587598 1250 501586348 501586363
    0x111507120920040f02181309080a0c1b180b0312220b0a0c03020d0203040e1f03050601060203041d0601080c030c0f03010e041202060f18010b06030a090b0c0304020a05040e 75
    0x511070380040707402a1b80b032030180d83c2c10318440350655004c5580045101070004407502c80c034000701940c01c10300c0312a10581c403036840c0641c82c07889042d040428a409090061740001a5449940d03007004450052600d41c10303600918170802c02c190020300aa14a400841c1000d0044600885240301c817003c1601600c042980101c005207850032103103503260352900b802001e04082203810f038098030032005086000c4d440002110300b120929020400c654035048000003030b250303050f4007083e00a1034842022002c22000c1c0110b174002e05c4550021603440b8601b404a400c4040901d07803c0c01071030b40c10310400000380d03085034809500214100205a8075620030440440c507010703106800154100103c00030404031403110900e80518007580c5000d022402d2200101d99500d0f040303c00c0c0b107a5001d000b01080030b40c840307540100300e2800c80d1000031403565003900c0030031926002100c19000700ca0b2aa4402c2c0b0910800401d0550040e880c0120700c0d10350f00e0160040fa100200c24400c1601403a591455014155018001d44 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 501588848 1250 501587598 501587621
    0x2210a0302130b07031d0d06110d240914010905180a030203120c090d0209090c1807030e0d0203190309020d03030f06090b0f040c11150712092004 64
    0x11030b46076200c00070030440750090310307040f0003117240180240c0301400c10000e07203a0011801010130040070030a40d140c1c409841c3c40100075612903024084d10b21440094080d5407400031202e40b10203003600c0394903501c00040310540d000c980d01e2481c10701c2e03050700543c0400c091815954080d20115140e1669088076543d00030058020a0320b0003160101c804255010004083c1e221440169044c0d80e01d0f00c80000030244a1010065031144440c0c03203c400504140122940c0001e522098851190710040441c102801180c4003250102020042010440e01440b400b032a001c0c5450040040080070389001e56644100e040c000701e0b500c001084d20b502a80b00b03400a0001c20740c0980701140003401480c000c0c0141a80c5245d210b00740e800c0600128024070544241e0715141c500030301042d60304084405000c0100441040c5004200c0d22441040000004214001c40001c44032a212a00d1800d00801424815100450b81455040c50803400104060035503204154080400746148248040c00040c010304101e100c0c0c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 501590098 1250 501588848 501588877
    0x6090402240405010216060c0f0602040506160506070c12140d0614010e0301050c09151e03041a1b031806070306031401050601050f0c031e071202210a0302 68
    0x1001000350820020308111042030b02101c03507031804c684581200503807d0003000c0000b8008030b45c1d0fa000c50600100c020015002e40301c01494140c03103001058040c1c1c0711100029030340800711489410000100265a4001c20303034641140c00107000d689140a000305042181d04100320502400083c02d19a170131034404075403001e010041c9554403d01405c2c0014a000d155011901c18040b00d4441d080600070240320b1102468805d1828050342e0412080b0701c9412280c851a03071040c07024050040001c46004005200c00c0ca12680300c0c0341514040758450b82c003400342648940ca100a010b008003980611110410100c0019920307550380c8940000e0031801c102c07058082d88030f600248134443e5019031201d029207014410614015400155603407e94100b034800a00041c4208141140261402c0107032410000c0d40041d42c7c90509050391248070010b4045641c00009000140001040f1101030078040e504024000341c00b100c9180d2040d20598102d6910300c400d500c01c00118030103000d04c65030454599101d03001d01f = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 501591348 1250 501590098 501590149
    0x20c0717060604091713122406080c0126070f09081506011110050718050f030a0210020c130606080f010b0a0e0d08030f040507051806090402 62
    0x3102400d6290428110140034800c00700e640c1c0c1c2044d0061010007600720b2010100010184481c80311503002940100450981c1c0b440422910108299003100b680074003101d0104071080311025580c511203014801c4c80e00d11b03200040003030410104180b180442d09003000d1241885203001c254441c11800481d19260b0300d184204004260000501d0303803003840a5642e0600d41e03483c1c0e4401c654510100078407101c00b440340e0000454641c4103203400e242c040144401c0d1880d4100d1114908240c45065802c0d40c082001000c250041c0781d0f04181e000014541110100c1d26840f281011a0300c0c2c500350b14000c1d000d03070f02c840300c090380f824000c010204c15608080c0428100c5a800c84214006000a00450000825000200d1541c4144982e4981a0340e105420107160a1a95030103545898400c035040342c200300c00101000c045150341000c1e61043d81c02194040302c03072500740707031143c1804015041944150350404004040d0350845e240c06030f2021042e5205503c0d5140d900000e40c1d075000385806505015009130 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 501592598 1250 501591348 501591359
    0x2070b0f011701020a080f061809010e0d0305061e0f030706050d0b0a06120906060f030305480703020405091b09060d12090513060614031b0a03020c07 66
    0x41a0341281c84140828a804200b28401420b030f10400e0102400552040045484113201d620443d40014004000c017480c01d0f03600b031142401030401c861a00c0580d5403002001a10601404800701c4c0b01110f180030006440c02d400081d40710421014000b00c0060a182600450748852102108800717009080794102ca07500c132001480c0b603000403109035040d030a0402d40031a41c240140080140d640540b201808408200083e070014018914142c6034103444007000180300c0382404185010358000c1c1d417550350b5400b0039140c0c0d0060401c0403481d06074070b400c16142c002080e44882481c2089038101081401c54480b0811060301d410041e4001a501c10314000c2848880900060170080e00c811440e00e10801141d507804011f0500c0044480542181c82c10ba412000524a000508040556030500d040115122008512288200c0340a100713043d0b9510001d100240c0c01c0001c401408400140b01451842c02145910b402c00500c0e801c440102000315408104034001c5e01076428524104040354816503460 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 501593848 1250 501592598 501592621
    0x9050310060f08011b050f0904110424120b030f01110415020c090a02032a1c020f07020d020307030f05100b0d050c1002240906160c0b0a02070b 63
    0x140b1403035410615803400000c0034078041c0100c04621505001d00c400740c4901c0c050550b1103038012180705080207001c111100c2e2036600d0348074200001c078040030781a44880c18004018002d401644159651010000d600ba5000b0752001c0c0f10b1007403004e452000b0414044410200e0714205c03003217200c440c00e5400c000c250380f04040c07610060411111760011082030490103d400341c0e00c2d50300c55040c2642003c42c00c0e000070504e030003d030019500860200b043c1e51401e07643d01c210805c413001149000c003a021000444209a01c3d454440070b000c400d070f110f011031400941142d40c42c1d091144400080c001e4154020901c20f642d010f200b51002181c02090840c1c060001b45811910b59928180c111480b51030320b03000e0390090400401001c15254001e00800303940c505042001408442c1207521021031043c0641c0d0920400100c480a0007002c50342c1c0311806a0410000b01402c12000928180d091055030b03c01094a07540034101e2040340390042138013074543c0c4070741d41c52901911404070003030140e040c0c0005000c1d969444 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 501595098 1250 501593848 501593861
    0xb07110721440a14160312060807140d0602040803031906090203070c0609140d090f060f02030d0e0703140d020709020408030d0209040b0d05070e01080313120309050310 74
    0x200100c2c00700712102c1c41c4210014800751050100c200405005010490b8010a4101c00002d0541d40c0e06051001c48400e010000c41d60303007001c500103149001401b011484a0044001401c0c023600600122424102c6d01d80b82411001e114511860307101d01c150b1309000032541110050714400f01a81d6503480c1c121a40c28000f4140040c078003016150510028000c00c0500c00c1d00e0156002c0d990b2908060080e4403200007508003007805980703c50034616003100541b4100100c00410b501500e4900103030303240420301d04c01904103602100a01220240b80312a060b4003100320741c440d1542e0040001c545843c8910b882c41c001040c1c00041291101104c030708100c903400202c40258040716030880e074451391070788848000c3e40600d00c10303504217510034410106d100141e034004e8010b03000003400015070b49162000207007800c9055081607440f500011018404000020b40103030250058000442c0782004074054540082c52a21941c0c09142000408100301441404c1d400018140241111303122410115030344002d251 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 501596348 1250 501595098 501595163
    0x8030702061303171b0105060607020f0312040906030b100b0306270103080c2a010507110411070b160206160c020d03020106052d0f0a080312040b07110721 68
    0x52140381741000e90014040e50344945805844a411b0400907401e02140e0041d404801d41e1600585440301c2d45420369034041c00080100550210300c00345142098600c0b4600507222a490001011080c8100d17230b03414048a8100c0300c02d540c0e00c01300040030150100081040a00c0b1000c01a0000000050000b41e00142c001c0c03100c0081a648562503e404130840c0d414407000ca00811100381d41424881e40c050000b407d452801011003540d428860400207044904c0005040d00302000031401e00309000c0680c5840b5031200000364201160304117000060f659004c02001ca00684010614407100640b0070900098070650150810f4106806442c0181c043d101c03a00859000d5520500d80130340040224803000d90b03031809110a81032a591403010302006540a4620741d4000e103880380001400c100c02c01c0103001c10040d0440b07114a50500b03140020001201400d560304025240b20070410409010429108a440b040807400100d000b0380080403402d0381c8014083d01c03c4800c0f01202d8001002003106450b61030 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 501597598 1250 501596348 501596377
    0x309040605040c020a17040b0c01090614150d0303020d0f0b120c06040902030903040f03050105010602010b061c09211d0301110406080601020c04020406050a180803070206130317 78
    0x26200e50500c41101c0108402c50300503401075520b41701050300300040c4034204a010052618041d159011404c2c507500000c812500b0343e550b01e85600034040c0b184107000c03801401d4404200541851341484404d21107240320030380300b8110340a4000c2014020360486210101c1c58409000d802241000c0b0002013021700c40e079038050304401000815000010420081110004102908041c24004000000e410082c41e49a25100403c40400d010204c0c1c02000000c41c8900e00110305981014402829211a51a0f050051109000d0b0010030840c2640100302c400f18140b00140040160600340b00c1e14408030310340c280201140c000301c3d4034140d110034070106402c410400d10142e42d42c0d4006143c200d4006001d4000d02c0700d4184402e000c3e03544208103040c0c12502c14030465481c000c1031030000b4101e0703100b40d0068010035800540229100e4000d58410349202103803032429069441c00c1c4ad244e0700c074403070100024031804000808502d80f01c19040014061504000d41c0002840d4084600b4801c2d4840e009901803113 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 501598848 1250 501597598 501597611
    0x4060f0e0a2408090a0b04171201031209050f01081e150405150d020d03020a06050114120a02130b04060b0408010608060901090f030804020303070b100f0501090e072a05030904 77
    0x40c080e1043c0c034041c2c3e000740020100013440351100503400c1c1000d070007110500070540c940080304030f501d0007421035200e50329410365540d490351410852102c0c003c03501101703100b54101300300300959450702804501c8c2028204000f4989c3e503000c2c140809044c174000ea802c11058441070dc034206410007075181c80340d1400d031010011f584820880324011002e070041a68810007078482c100c010705046c05080c0d4090b2181c0100ca000c0641552118182d410982042d20701c80c800a0158820307142c010100c1003118049070241c8406100358000c90191010001c40741005c0351140070f10300c81e41e2516070002004104605456803229182c0396600d01a104070310a80c1124419039002c80d0360300d107042c42070149079540403a600c0c42908450350f064a88010042c01603926010a100150115881040346031150507a10380f0140b030181860b06030030608409030030075410000c0340c0400344004810783d1401a0007035490b0034000040030400340c0c2d60600216499100c2000c0d900703100c04400300034000010b445407250844050054 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 501600098 1250 501598848 501598919
    0xe040e0102120612150702030901081302130515120106030209100b030a2a0e0102070f080c060903030f0d020304200105070b09071d090d1404060f0e0a 66
    0x341d001e01202c10b000580800080340c0d252520400c2c00c0000d07081c41090b25aa101099580441c3c21400c4640c5030151b04005038440305980e21010b03c5030300c408640c0203076641c0301d1f0136008109895400080d4070740a5990380d0100d1101d900c0500304100f054402003080541020501d00c042c042c2610781300403400364049602098040300c9a40c200030995228035450380c1107076181c40358000a0700b40340c3c0c0c2c900460307008122440720f480306c580400d06c22034406031509a81d05000200091410b551f03640311050b035444124084c0440c400106540052983c101c4815450f41319003000a811842801d9445100540000c0c0410510103030340c020394420b9015418900d1307006040700b0444801c02c030641041e07000400802464000440401d030064202c103508045a01560702e4851240340300c2d04088108107500142410012000b904000b510b01c41091407405800b56480d50b610f2180a014502a00c400e003c11410007103485c511903003886200700b900400c00d6203403950b03030242407201c01d055860755990760b00941640600c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 501601348 1250 501600098 501600101
    0x204201b120f0a0305040201230903060a0509030a0c1b0f0f0602030a0909020a0915050c01051f1a0f0d0204030311070f1403010f0f1d07030305190302190e040e01 71
    0x800801e070050261034060f900c40100c00902008000302e048c003200c00d80c8180c22800107041c0260041c46a002c1c20740e2050010304241c175208004100034070840c10101000001c032804416075141e0502c0e0b0a00c03150201c03181c90425400741d00c0881e481c0070b01e20660400224805901c803800c044130150b0207403202494440c0c5049849104586546c00403d00c4050200701c00f1700f40c0d0f070040c91421800e02c1c081092a03100c0d50b140c840390550320001000900081900880503000f841425088015106013045803000003089102801052203a84080405440461600c24451045a600c03600c501d9000e90340c0d022001e20720300250000e000541c0026421a040703d42d40c80002051800d03911006901020300f840c00340d2200903218141600c54040d5210200c103000c1e5440c5000d4507818550148000c2030b004801413010442006d1010f15a22540c003500b000c0010a82150803621418801c0d03c00865000252606501910501e054080004884005511003d50104c00c803015a0800c80d400c2c022648601091070 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 501602598 1250 501601348 501601357
    0x150902030a0c090602160b09030f0d2304031e0311150103031e081801020c1605011715010302250f0201030507030c0503012c0c120a020301030305070204201b12 70
    0xb9030585040d801f4420030b500d40018043e001c0004040340d07040c1200a040d207040c20250504e54000c28400300030003104501044041c001c000c01611010b050516503155283d050130f4400441c6030462907508ca550515114204618030340c411901250302c00440d000171290030201c00d1006600003021920340f0a0341d1070701200c4580300300c600c603501e84d0f0355500c40c000c820341541110384440041e50b50170058561005420302c003007101d405258007003000b003514203000581b102d44040c0801000040c0301c0208000701c49a0140b0100302002840d00584605004499070341e1461007c0401c03459040e03601a100412010351503109440e80700faa428030440d100d814003031341a601481070740000301b4820720052051440ba080a88a280b0b0b00c2011070f4201d9101d0401d07282003c00030b4440b04908080041c8405840604940b410740002410034110724640c95500d00800b40d024451000307203c0c2e500e034842103241085110180c3d541c000d60b820403e81d45e8500e100e0f100d1758842c030200080a64001c458102c00c030b1081580680307 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 501603848 1250 501602598 501602623
    0x406020c06030f04060c09080d052d07030c08090904060b041103090705010c020d06060e15030304032a08010e0a021801060905121906020d051303050409150902030a0c090602 76
    0x11600f5499a58408000d0404030007000100400d035a00090885005c01002142507420b449a940d1356403982c3c2160200030001c2c0468071981a5450708644800c9402e08039000781d601490202c0c005a5989042c215070f00c620400070b41c0c401c5009080c001030005d030350700c4080e280303204032020040c600c40078400048034041181c000d1200e070000320302004554015011f0001c254401825103100c0343d156681d074411929690400c55a01d40c1c0d0300100255102c070742ca407049590004900071410b003480e6030f603000301d40c4100039896840c0101141401042003000c1d5015806130070900b00a10407609444252a079030421103001740e104e6041c0c9000c1d1520b40c0300d201c100754143d991030364030054400d003001c003131000480b4000700c214118424442180e0150760542403032658070b0b201360005603841c0b80c5c40d0a032600381e8030080d0aa460400c03100c03060900080d04202260125a90201c0110319003001822804581202c1d5205542c4140000204407446005602c810100c1d40151120070f20f841c0c42e144201c0e075030040c14515 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 501605098 1250 501603848 501603871
    0x2310305061501020102070f050606240f0d20180405061806010c210801060f0f030b030c1c0c0605041401081b13090506030d0207031203090206040b0406020c0603 71
    0x105900c2c1c207040200d400104010b000152801090380e40720004100032500580d06608003c0c240180380c40c000b07072a9110040003003e400c1c980c418410300480203100d03c24035041402e82c0000d00415003c469042003031400c1d441c000c8054803550441170202c9540c82404400003a0440c0c6039140318078074282c8103071030003000c0190a82c00da2000c840c00000346101e015104506001400003094001508081d0220203220460764070b4980300001d02c4058a280010b03003090007488004817150071050350244a100c244101032030041b07424091503000c2401c1284182000b0340148040c070003103500300b074111309440d50a0b210b101c20301c4103540e903010115035034012801090320740b0405003c4040c00303601c180c45481d0850304044102c0c000b48004007030a089680141c1b000c4000b440000010040032445202c2d4a0303002400303a01070400c885011400948550080c000200b031201e04001c2c030100c0034841c2c1d102000d82c5a01030a940d6455132121a40d590f150003500c581d00c010312500c22005503500385202540e0195403440c0c2c9 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 501606348 1250 501605098 501605101
    0x1107020d0303021210060318051c090b042c01030201080a050402180a09050708010e0706031d010222121110020f0118060b0f03060c1605010231030506 66
    0x30040c014a0304142038007019000c2c01400b0060b041c8101c400e0152020720f8140a0780c0e450454003034290764500900110300765181c048200400c0c0c01091a02212000d009103a44902d09400c1c19140c181e002c0d0084007804201240120748c690715115082c00e841d8003079103a8205600d0508480708031600901000b0b0006800c90f01150090005820154200740b00030700183c034070f943c110002c030101d90f0100e80012605840351610018020244482d502a01440300280042c0600c0e01c0d4880d510780c024407515003015942c9003520700842880c601c51540c00041802556148a0518880e50b031041800c03039042d81d0030904a001908800940d0700e00c119991009011043e201c06600f04150ba4800c285400254001c890104032411020700c540b0000704644040780d10840c0b45821301d9802c0340c002c003207064010421040c000c005a0350010782d20ba8404d00c0d206446c2c1c1d0700c200240e0104d600341c803442c0008182d58008100d040500044545000c490150354171088006681032a40010001092201600300e400020 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 501607598 1250 501606348 501606353
    0x37060e1c11120309040207120e041407050a0302070c0b04031203020a020c040c020f060f180102041805040f0b01080703030e1f030c051c0e0c01140405010f0c02031006181107 76
    0x10b0a10703a204036081c041d60b0074070040402180c2641e020681c04c03501c42440200720f0036050b8200c0c462010241059504000f01c0041c10808205100c0141c9044140040401c07001c02561007901103841e51507110b1000200d04c3c0d0364140c1e0010035007040c002215091014060224464428401d4401c00700940e401404030300380325030521008203401030324081103002d40c0720b0300440000708000e61800340c031003003140000919003550104020902c8a81d400c81c1c0d80d0040000308022852290b007015000350380d00c1d00050649480c03038403549084c0151001880032002c8000010604408503610044038003070b41340c02c3c0011203920108007441d080c50700703401c154200e10510614003a1103a4400700b100407460610b00c0ca0968016140c035002e00b000c0c10100405610b07503a10010407102802003d01882d4207080102c040017824083c4070141c026030007014100098001f07815442407180410050725078000e800e840000146454082c09048103001c0d801e1940010001d810014600b4414400481c0c8042c00060500016030b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 501608848 1250 501607598 501607609
    0x3151002070b09061b06090708011104030b060a051005070326040611040f14130b3f0105040210050a0c47010501080637060e1c11 57
    0x8a401e40c4c0204061010b83d60304220b05031072000c0e250b000001007405240200c0d585107050801e400914545e4106203100071549901c03010b031400d407070b401084900f265540d880400d81100081e48400e03030000d5a0444441050381080041034282e01075941c0035052040d2000380ca000c041c04a400000304801c1100040106a41c2d03440000c090300055007041ca803a5480d00d085241e010941c0010030a0103000344188542e02e003000740b000b20180006020f000c0d14050f08002a41c3c81da03090450000020340c21103083c5805100b403c0300424268245040f002e0381d81c00d034819402003900f241e0490140d880c5012007070141d400390040c0c1d440015241d4946410340300507990402801c900341686d8484401d000050400080e15610b030021500e0240b049040d2100c01c441542c0303001c00c043c0e11181c1409501c3c03043c08a02d0b19400c0007013040030800d9010f80b00e10109480c44c4200307042c0f022900b1100c502484804518540c2c443e0070504042001c0b01c8000243c03e40f2410b00c0e08806e0798141c01032450001da08100d2560500 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 501610098 1250 501608848 501608857
    0x80105091b03070306050a0621181707150e0d03050c031302010915020a0b010e093d151a03010521030f040f230112090f050303151002070b 61
    0x480c5804038000741c6c1c82020508107800c0f034200c64041040d1010b401100885041c080c1603004580d0303000e1040303405250049582c0c43c110480500b40d01c400e110080c0ba6019040103e454007a445421050580c1c419481d0100030403c0e01011040c0380100662803000034402c1c09407d000308040424941f1395159204078003880380883c04102c1c14888003020006a0300455030280c00040466000f500011880d0301d040254194160000400503018509000304420300080c041003e003c06192203128503044890003886600d00000e000900d0350601011040910b40d4102050005056516540c2c468451402d12901c00c120032205000400c14001003141d03142c038104083c1481004055200c08480011b8030703034203582c0610f21011300000c00003000c1014142826600c0002c102c3e584608246402e020040240010b0350007206041042c0100c104030500541c5c2c0c011406250702c400d803401c01d9000c030b24017a0707120703002118003081e0421408907544543c100210380111440709607018000990400e002c04809400 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 501611348 1250 501610098 501610111
    0x60506031b0c0c0306010b030603160f091112090a02090903040308030c0306150a170601050f0d050c1303050a0203010c030e0a140a0b0702010e07051f080c0708070f03080105091b03 79
    0x9100c419010f40c1d01c3c2809443d01074400e20000390741d2032403c2800d261826010408410003240310709003c000e01000300ca44242691190300d000704d414020300c800d080702405071181d15242082d405081c4440c06800207594031604d0300c290f40395500750fa122202c40c1e4903405180f00240c648101007002410f42203d400040d41c0c8810001d0411000309440740f003110158010503070700360110700d036040d080310b0700003d110300150700420929100b4940000c1c02c0406503503004640c3d20f0210a0740b1000072503a458185070030740b11150b80e030780f0210a5203a96410403070b0740c500c08528242e000b5440c000c12600014031900236500351180e60001840c10040e0f5984400d219060094214103500408010800240c004500503008010681c00442d0300403003028400d00f000140d0740701500c100c0d583d03441f840b1480014800b00c010f600032070918400c90744c0c400f1030450882c41050b01c010700d2000c1c0000c100040007420780151071007a01954400925030380f5070f028410b81c0d440c25201d904007000340c000105015031101c0300442d40441d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 501612598 1250 501611348 501611353
    0xf020f0904020d02070b040803010f0509011503020d0b091e1003050705100516060603141b0d032708100b0a0b03040614070914180408131e0603060506031b0c 69
    0x140e558540c1101b18034262000c5503041c0303001004000201035405582c025290440c0c010703c40f545410704009000c00141e00040130b25801081041040d2034544c85030454401c05804010203280c241c010502c1a4040000440506142c0003c00c1d442040019044d09036036012008209282c200381c00c01c804210003a03103200030030208005216501d0540c010107c51141300300d0300801c0d00780c05c40c0b8100500e050424861100345d48035034004180e5030541c90b580507080200307988844410104e400e044454040780300041d0b540d00c1215240101201c0b103011001c0481d01c030034041c0c078002c04010607400103442030410b4181e40328000000c10700000001d02c00458000d80304020000f07414849210400303842c84111283e00109400300820048403411011485440750111052a00f0403040f035a507800c41c034406400030b08509004519501c01c55907403c24100984009132074940321010501c010394100c00e203809460f00203414080001082d0400900b43da00800a00308103054801140010a0f8580c21a5940a4130361 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 501613848 1250 501612598 501612607
    0x32010e0106091803200304030c061706010c06020c070305030309031206060c0304180f0c350121050304080c1f1e090504020f25020a0b0a0207031a04060f020f0904020d02 74
    0x140c17130410081c40114410768090841518200001d80320400034000b100001d0742440400c00941e920441c400d000903408480141c54100c4941c9191a15440d070b000106280700c00070600503da41c0020180c0b40002c41c00340701701882d035200c80900c07145000301c1482c006103034814071040c0043e254940c0c44800c80c2038500790008004d40c1d8003800c0000e6422088a010102c0c0707400d003001000212062104021072200031a01203000304c44100c20741400302c14450741100c134222500b008038601500c000c1c00419a0054103d0f503c1e2078646040c0342c0c5946420203521302c105040706032890b1088948508030f42882d01034850000c0045e12041c3c0650401420001c8010810340360004109540c5520181110b9502d140301a6102c500d0155010103003940d50080c3c8031402c642403400b038010f03540e100079041036803d0312071040c4d102c00051105a2400d881604014501c0c0c107400303448080a80f03d004d6551003235000d0b0b074007401920b42544002c0c1c224413a43c00d0128501d54104900780850410b0703001009401c0c00300e080145071 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 501615098 1250 501613848 501613907
    0x1a030a0f141204030311010b040c0203070f06020d0510081b0d03030b030f06270705090415060305010908030403030b19050d0309030b01080f0f0706050732010e0106091803 75
    0x450f802600120042861b00b01d400d030500c00e0921a091030705a040c1d9042005c0c5903040c6020395203029040b0001c14003082c80b00c0403010841641c05442024200203010300890a0200c0520401903041c00303102c286e2320804515958424000c180c0c1c01e802c103000740c5007648607025030700d00301d014100680145400d481040300101d80c0d40310070055648180ca00410014940032800d11090b1312020b83d2002201d01d40c01608140a80d595544110b41c00ca0741c0030f030035084200c3c501c0441c0800b070401c2e07a0011b0965403030400f00d2803d20065400640c4118400e82c7c00308010300c808000c01c800708021104008405050045c2441241400c80b0075818043c001c1c181502c0741a5241d540301017035007090300640c1c3c094000c02003061040008000c100d51140640001e032200724100035004249008041014090742c8036160394103440b000c3d403d0510341e00000d84140324400d4468002d400d006c0c110b10004e00c0629840d0001c00900003105100c0d03090b202c11500e281c19014105618116030204004054082c030b10401c0320540c08 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 501616348 1250 501615098 501615133
    0x60d09110904140f0f0607111006090c080f040b04060e010b0918070b0315130e0616120e06040809030115120b01091b0f11030a031a030a0f14 62
    0x1040c1d2180340c0c0800601d42c11280f081c2010070702c01003062641e110406415940f00e0100750980d10078607900d42a01c0c0c0d203518000d220b20348106000604400d51404202040100d4203400010021505442d04510754840b400d481a499008440140071180c00d900802c000500300d070818115808100004140e940c0c8042c00031340c40c41c000b524058030300910301e224941d01740014031840d0001c0c516801c556096240045099407145010208140b0894001c001b200c0200b4296211302c040281d14821140203151680d15031107084400c00d010380105510403101c40d2001d03014010b0f032007080fa50304090714003501c941d9100162608420005640b40d500c4842d4041c002ca8600c800d00000c5c1008406070980f510f150408000500040e000a601c4504100c1c2c1507100314030141b0303c0c0c01058480c1c58000c61800840404032501500302c0011060350200144e800c03100756050f04401c1642094401e1f04c60000300c00d0003055624256024000c00d04040c1e10503210214105504280d003241340a0260344400d06840000c64 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 501617598 1250 501616348 501616351
    0x1103031308060f011203021b0a0b070b0603071e060e060c03030f1e01060c080a020106030803010b0406110304060e13090501050103080d0f1505060f0405090403090302190302060d091109 81
    0x940d40b000c0308001d540f80306030944500509040c083e000400c102504e000f91100500d92072513141c2c176280742c1c0c0c6020644990791494010a4000031045c1c5032200c52501c2002d2580070b90304203210f0b200d4038001050709401c100c4035004481c050303020302801d280b5122003601c120342c2040d003480e4026030603c8080006102880154429640042d8220803443c00e10480011580302c0d640000c9408203460041c4102900101d191802c690030007081c2d51910300384030782203015101315000103101c00e00100c0005048115100a4010399000741c031845032207184036401541d240940c0c403c680c0011610404002d40c0d0512205010f507524800c02c0101e4100300c01d85985080d25020b07070044541e240700007900c5c280d550070751081c07000e0b00303604070b000f0b120800072440407201da18400d018440c46903000240449000610004560042030040c1c00c11a15103003904014010380d21500c426400b0b0035800f03c1c0c40a0642803100c945041d82e0f401400350381003004142404d0300815100f0001c40343e40740664145c205641c1c802a0a5 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 501618705 1107 501617598 501617609
    0x4120e060306011209060c0e0a0501050327120a050a08010527062e02121c0f0e01150f06020106031109090705150a02150105060711030313 61
    0x1131070081039440c000802c07143c5003098003603500c0d8000e012a0705a8004407401000749665000540302440b0440b0020918080d00140c0b90320a0503002030040514074102c2212070b030700c3c800469858a54411080e610116101203203159045920000b4603000d80707000e80b40708440301140031100b0424a1282c0080300640380840016a090300e92800344200d1404500c80310034002040c2600008441c28406100c0c0107000341074000080301c0344d402c00c0710840010035980c180d984030b40d02c84c0345009007640b041668842d40c84012807a4684424040e00d03061a0a848800e10110f103810b407010248184c5500020a41e410408204003150030315000c05000c40c410b81d607120141e44c0301c4040394285002c9406c07607039115010000c0b0344210354001f00500344c02c00c8140c00325589492820b401d4030bc510403d1155503032200c0b0401c8107100155400b40403070034242015084034145602494081040308180c0c014 = true := by decide +kernel

theorem cover : BRFrame.Cov 501438848 501618705 := by
  have h0 := BRFrame.cov_init 501438848
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 501438848 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 501438848 ≤ n) (h2 : n < 501618705) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
