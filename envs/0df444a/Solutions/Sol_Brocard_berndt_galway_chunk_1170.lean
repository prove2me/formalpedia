-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1170
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:34:52.392196+00:00
-- url     : https://prove2.me/submissions/c3563105-1d86-4eb4-aa5f-4b26d4ff8b23

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 210251798 ≤ n < 210431654 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 210253048 1250 210251798 210251807
    0xf0402010c05031b0d0f0219031803050309040606110c09070e03150f0610090308070305070f0b0612010c1d030322091103060d08090a0504020a030c03150f0611120301060f 75
    0x5d9045406004001502040094011454400c1c800a040c00c0a09403034080c5411903000345840d18034001d50f107034680c0104c01c1c050b00102418603c8000d40b4104071481e03c451094419903d11450342d0000d610009000341d41e4104070408641106d00e90411410800c0e07480e00007400d051710344110503460b40c540c004005040340c60162490f080501a180d5080c1e4070000340c401030600d1041c1c0405050058001030840800d03201d00115001030740c118802c606081c02c1c518100140701000d81d60244240c21095811141c03c1040c4284d00c072200ca140c4a041789049940143c58501101960302913040c0810f0014991170402140f0315080d490750010b0a041a07130070b0045107001c039520f00101c180b080d2003c6c420042e0989500c0812050799420000720ba0700c8a001c40f000601c84c204640105812078008250700d080560150000d0800b10303400e03103084c0304401540d0b04006025605108003c0300280139481004214000d02d902d004264144040e903901d101034115008107a0300c00e034021400500010120541142d10 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 210254298 1250 210253048 210253063
    0xc0c01090b03071e02030f040311090708151302091f02060a0c0e0111031605031806160f151806050c0901120b010504050d0f1202030a080f0402010c05031b 68
    0x920481078118105201c0013003141600007010440c1c2000801081e1886000b0010f4600706040b582e05181da80352646010443c00b07405152540c080c01200d00817688241c00358490520514010a0716100c07500f04604200e0031000d484034100b1007076403c1001c500140c84140728044034000d058001c0023416845a0000e2801e170005042402003882c26480c202800d0f40186000b10301002441c007039103807410a00215065118891065105c881c03550040c4042190110240c03a4100c1c060b038201041c02480710500505100e55010b94168103084d0155900164040024010b080e003d0b480802c0602444000681152508a4040340d20000d1814000c00c000040c0510307540314a0b124002d60811003480000b82858501e65034200409844005120301c0364400c0e400d8800802009065815496180c20100552904d0a40a07680d404010340382c003a584d80000125404408181d41b1102c540d17071105c0490300312036000340040741044580b0320000c1c08220100081c0440c1c0e80396441c800d0032000e0312003800b0302d06840c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 210255548 1250 210254298 210254309
    0x10312110a2a0803070b0613060501080c070813030b0f06010e090f1f06030e0106091107080306030a02040203010b0c070623071103011503050d0c0c050d050f030c0c0109 74
    0x81400741000a20071520b45003004101036080b890420b0358005020901c41c2500031000702d20010840206001034205128012281601c01c0c80d01d9400b0900b0030426150365000710b80c007160504000c0341d20541c5240007032403c14080c04100e824901003020104200209034409d031021040c58080c401c2d424420742032590407180908007042d40c0b56034180460f00c81a401041e02c41c3c03c1f00d00f240040e0004045100d03055402d4405e6050b9064107483e00342c060010201c0d0000d5000641c0703441d0002c82c902c1e1151140561715000c42e60801c0c200ba40c540d5854805910040c40a900350244c0140030b001a01e49002541c0030701000040180c541d03c484250b10718000c195488501003000800a8018100c0503203e010041c1888402241d51240c1c10304001000b40c1c1350000480d0190700c2d04c0a001c0c0c802d001031102c0c00a4a00c030341c0039501c1e4041c64400c100c5044600c181c01601c5030282071404c11061510f500700000c10f07481041540c1000011084090031a0041103000c034940d000314003800c9130b0b5031380000300c14050701 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 210256798 1250 210255548 210255553
    0x50f03101509030326040204050603120a03090b010b03101511010603031205060a140f04150e10080714120a171803060405060c03091c050409110304172101031211 71
    0x40040c0100100085c0181006e806241e8410118410340c030140440f1a083c00400c075138683c2d0315521308009009008400c420b0f80d40090501c0041010300021003141d0007840c00c0050b150480b81010044056041d00001241c18409485a0401d500340f0030f0145200943c007031b80310703103805041c4e07480b401e010f03101d0050500e48500305240b0144511190070000581000f8280d5000d498001d60001140c002c00740b00480c0260ba06801800140d9404c00d01080d0340b040310044044180d607580c0c1d0351403569410b07050164407408948030b1101a0242400c05000a195400c0012252120301c20307242c10152680f0940e4031010781500180e200d02011000140320861481640100b800e0b103025240e0640780c0e403015103d664451000804601ca2410170402c112110310f1040281d81c02c6405a50040c015521a01c2002e003085c2c100200c07040d80c81180b0058a01c07890b0001021b01d00502c12000301006584121580741480500300b52004015000080d014040c511a600c501394040c190300b00a0010751000034061a46c0c0d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 210258048 1250 210256798 210256847
    0x80a0308190207121d0916030e070e06060a0909020c060103020109060c0507180603080c24060d0308091009110405100302060d020702010509101701080d050f031015090303 75
    0x10703008903d0341135900c03441d14209580c1840c4058030017480001c2c680c2107a0061100c010301c00b1028003140960054003094030100168130b0104000c40c0c4601c10b51003210114504800040e003241088001044001481e1622044558990160074202d80061611160550180c2c0041c011035811035020805403403035080c0b1018208082d6540e0f41e0b68241c2d4002d4980b41381000500c10703084011170308608040d6610104068480d480c441d0911399801107410072016031001c50004c1401c1070040d95541d4000c40e00a041c01d00a0b00050310306a4150304041d01403180d40c41031391070780740c0c0b840054440c039501c0c6442105404080c0c0041c2003008107942c4040c04482c0341400e405020001030342ea074800c0b1801a107100d1000350300c920503800140d40a000300e41c0e0381c50300015803440c1c800441da80040c03222036810302c03405c01c24801d90300c601da104d5031211303e2046030010840401807204030030700031409154024480c0385110080d588031040b4031005032120fa010004501039003000e20400d6008103080800e00030a02c41000311 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 210259298 1250 210258048 210258053
    0x16050a151104051e091e1501140a020a061d21090112090b180d0f05160c030c09060f0e090a03210504051606020c0a1e080a0308190207 59
    0x480c46284074a82c03280b815035080b50780381e50700c400441c04c0c0c0c1030700240043c2c21480c06034001d500c0c003c030741c5c01812048401b640008003089200b050701010300382c060751050500303000211051159449040f030034040d84a006a0400012618014841515049800004554100d1380d00701c0c034103100150400c101d248891000d0a04500004c241c2e60000024a001d0706ca030003202c0180001040d4a09002c0d041d00d014108000300320354002e03a16054900018112909100310341c604443e100910b04100001840070451445054160304480400354060081041020750340e039555242100d1903406110306c292200b00402442501e0884000140100c6c1c4540c0224039004840540714040d814006050002c084080981c1c20210fa41160107205044000c00442c14071341000c6654429080b850b800c0c2c15110400498114404144490f10100140444d840795042100010b1819141049240410348040000400e0002085500c08081c02521050000c3c02d052444170101110071a0b00c404450040010400 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 210260548 1250 210259298 210259331
    0x3050112030e1503010608060a060c11120102090301021b0f0607120c0e0303030403030e010b0102190f030c08070305071704050d031809020f0301050301050708040c060c020616050a15 80
    0x30003503070520b02501030780d42c6a0300040015412aa20380c00b4410080000700700ca0f9040040c29003e6607003100c1a025850303948504032920051000c0061040500c180030344c0082c1815481c603008a80c4480000d4145002600400d00b240c000105600c210343e40c3c0c01645c400401b00340000e20000c1c800c100a8003080c500103001800341d400746002c6112071982c135003110003007502c1404040c0d0038072002001e0b2503a90810f8240140034140904014016518080000c4036a600005803441c41410814101c0c17140000e41d100d10a031a098090160184820099a000000c240700003d141040c403a0b04c4084d00c0d8401402d10382944108034101d02c200b040104000c6c0590b0b45c0f16102450480d6052418207243c803054125450305c429182e01040e40c250012501c1000725902a000d181a02c1c015002002a41d81c1e501c808c86600340140d03005481d0002c0750f032092152a12884095034001d0002d4030003807500000505004140c094604e0540381601f082c207100041141d10501030030071030b400ca081030040d11074807290504c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 210261798 1250 210260548 210260579
    0x2a10180806010e131b060c020310021813060f0e0f09011802190b0415140a09050d030201060e0a0501031a100501180e0a0203180f0d0c150f0606020c01030501 69
    0x450391080d40118010040c00c000880001d6000d0705c800841d085c3d98100103054603144400891090084260585500b000762095564500300c0c410351102c0034035140300348020410351407042c0380440c0d1035100c00314102400700d5114005040130b400c0400c2c6c034500b040c1c0381c010500000e002520a40d0420041091080c1d42058520555404540003400a40e030301a0281108840c1e60180080240c00705001548540500d43c100c0040d41c00e440d03c51190070b0048400d00c962003018100d102040452000b4409070408008170444644070b40000140c198840091801030078080b1202800eaa86500060040000c860201c3c01c4aa0066880449030f0600c65410030f02c1840074001c1c1c80c1002072036419402000c1c055171514000303140152442d402c1d401c0c80e03141d0070069441254014101c407407480e00c503401030100044244020b001b19028103004403c101b0100c034000d030b0000040c0c9407a01d801f065150000d0071071048565040d541031000911502d4088080e050080203c6214185841d0100410881d400c0d0003081 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 210263048 1250 210261798 210261811
    0x40311040506180403120c080c0d02030c0409060803180102160b0313080c0a051606050403110105070204020a0201050f0601031a040504030c0506070306051309052a10180806010e 78
    0x1248a81e10715000c83c00c083c0e00003041c0b80b0280503040034441459045052200350030013603001401802d1464409440512041e0ba40e84206502042000c11085071607018507003100380240b09510342903803281c140d420b5940e55081060260400101d511543c2d2a111080305202000c0c0081c00c4126580ca1070107811009501c10b400d00c003040000050f5070184210b40d4044402d501162541d113403031007050300c0d075524003284008903414404c01700401d2000c03180e44901400c8485aa5485d4035007421070b9901c110000c140080e450500c0b030107000c21070060ba80e03400a0310503800c80d9800012580ba200500160b07450300503101394181032a01400d202104001c81d0100d800701350a1303d010070503444a1a0446000c00d5450003d00340d4090803050000c0944c0c5500300108940c82292400b024201c0e5040746000c9802d8148010400e50250382d091250305107072188100483c00080b0000301400d00300300891035809000d08603900041042d00c010140246072074038080070300500401400c140d0305082d5441e10409025000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 210264298 1250 210263048 210263051
    0x2010f05061f020f100209100e1e010309300806010f05090d020613030b061507140c0907030c09080309090c0d0f0c0507060f09022103070c0f1a04031104 67
    0x5a12200780200700c4148118003e404a500344445c040b901d00080d0000384203a44184d0f600d81d02d05550503c600c03000040381c03d0040580401801d042d20808080004800c41410b2680703850a0308c2c007007604443d00c40000d14418503c1803083c0b05402190308171125004644042c403c02c2810f1181e41d9030b0007501e81030f070341125041096450000600080700030f01c0800000354400800540306440301c01c07000905e01268814154a40300d510303018104500014203001e004c40d0103a080c040705c004200d000780175040140c490025141c1404484020070b0060000302e807002e01098075250308cd086141d009032504014100d0401542c14240c109001400340f060191204541c101c0205070b0301c60300340b015404600258010141008880c3d217040016003150002c1c8400e0752464036191240d048410b40e40141d0366001e900400e00c80c0c20680d6003403122405004480c695105100a226250000c1c08098900014201140d00c0194551500020b80c1d000d401140f440c80302a80c0a03c0300b000055440e5802d5440e04104480 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 210265548 1250 210264298 210264349
    0x601082a0d05010b0907050a0509041a03010c0e01180530010c02070608010e040f080d02090405010e060a0506180f0f130c030f020a080a0c030219020303010602010f0506 74
    0x1a8460141018001e910900c5030a1140810005500100346440e017503032500708903a6460303010b0390a402403c0896000c035a00f0003c9070131902c0d03c0c2e40062402d008072818034802100c0640070030b0031038000c9001c01e0003180300000e81c0766180d03800c035442c1500d1140d00b1401c105040e0400300814010b052401c0c1c0c0c03d1004c000841c224000d41002c00d03405a81c0300e40d04000300092a07200c0002551000648116004901f000300040384d14070054000a01c1560000100c01021200e503a030001580d00204490781c44590900c840c1000740e64038080d884c004c003105d4515001500341081001007880c640e0b8007517403140300c0406c094020520085017658000c40304490021612250300302040220f01d10502c06035100750f17081b0510100001c150b02c4034040820301e540411071240c149240100302d20480080c0004a10340500142580344581c0243c03400c0d4407030345005800c0084180302e040007007440e13079500400f40c0c03c04001070101c0790b070910440c4211401281d052101d81400300120780030501680010980c402d0800 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 210266798 1250 210265548 210265603
    0x20906091e031903080106030606050a0809030d060311031c170402060f040305061b0c0c091b0301080616020601150807090305030c0325030215041a070e01030c02060108 74
    0x6800c0d0491038070150680b40382c00000028100c04911942c0c0c22400b00b0502400416118420b105000684100d030b228503203805040b090689817598024604001072100b00724402d50280380c0d00440c0c0080d885909001e030b031b9110301c208050800561040003000d08400840c0b00e9651a8000d0070b18000d02c219085070705298480b8008110184901d040184091364006000001c005c0c0c0040e201e48900d0000c00c2a091209048410f0076552245150048441d4080e0710700800c585808020a5080400c0c40c4080b604100500f0703071444075400036440707200c6c20f40051003002112150f456030a00c00d242588090b00f07240d81020f0100c040107811100000400c6840000a040140551068400344d504001126100c02500e0f0301503039a548203800b80381c6036080c3c4940ca40343c07004410380c50b000c00729455005003d5014455090710b4802c0002403082d00d100f2040408a0600d904039100e850181c2d40d00da48054071128140000342c26100c402c2030450455004400400014401090790310410028290030341c00f964598 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 210268048 1250 210266798 210266839
    0x90103200418050c030a051209010203090a090605010207090e070314151807060c0b07050a12112106010e010302030702010b0a170f0d140d091a040c0902090609 70
    0x541038250094a45039804401c04541404512880c1c0314008485055a61038141900c601c400b001c0100680c2c41107441540d00c40f20080a441c6089041c8101c0b8108a0300e80d000480f01e50050b23204c0c2c084541e40f20000c1c0465641402800301805100d10141321003219003c100fa600c101902c40a8a586007110181c20f80b440d00b8001c141000d148402142c060381000c0c3d4499010300410110080c861048050029645004510b1107215907008802d44001c3d6a0f504003c1d24140d100000e00400c00c20380c0000540744031000d2049102c3c10002c0680191200a141c1021011a1214000301541007a88003044416a4000c052111611082c80c001d40c49803610002a405088007000702c0d5807190105001081c03d40d104a201840820703040101d0342e4403000c032181a9182c0c4d050103001d9000806600c400420880c440d030007040460341042001500480e507490ba940002c2740d0540d240c0d00003a010382800180000c4214240261143e0780c0d045242c460004d00041c01e42c4900c4500c00d020301d0702d01c40029007801e02d030b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 210269298 1250 210268048 210268103
    0x204030204020c1507021b0d11060a030c090b090d1104020408030f030a0b060901171b0a050c010c030c0c0209090106081f140105010507020d0c05130f05010e06090103 73
    0x14000b55295800d40400980302c95400c441801341e04841000079195501c0047d081c108141c6203298030b41000d01d800280400c2d800750000c00e0f05c0384003110301d44244a4590100400010340b0a03940001e81014941d402084641c0541c00001406400d0042c40c0460307585000b4480000e6009840084000605000c140680500d600885581c04081030b00459202040011403140c0c0290604001e14000b10381000124016850624002404007403400102040c0c10709036030b0003030710002d80c28080000b101d21490450740002c0020300050ac0c003184404c400b113402d000da0385071198141014810390f481450000d10801c41240003034487d40c020401314039048002e501c0780b406405010180c40f1700d8940c044d04006004448180d8021140ca4440064003c400c843d06142c103845e0141d445625150322602040030007480800c3c01d440c21028210000748559540d00a0003a000504102090101256054000b1038405905c469040d0b1240c0d01082516666114141e0540b0f81c49000c4102002510100c00e04c24210f = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 210270548 1250 210269298 210269303
    0x10513021b0f0f07051903020d050a02031603151406040c051b0c180108030a1124190b0d080f1213210c0b06010c0209010b120c0a0504090f020403 64
    0x10811482e0742141d01103840b0b8896581d080c101d616442ea21400d0040d5040010f445105d0620598400d01c01840c0810807451902c7c0200f040b01d01d039005c81d400003810030300141280048182d01d403004004001043e00c86084810310184104440b00c13045004400b0701c0c60041c0031900c04ca50380c030b18503004a40110141c400300303032460801029000c07050311802d80d00d5802c8448036108044042c034034250542c085100c5c9040c1c0300028051410101e401c0400c3c0c420134a030701411241401050f0781c528602c80321201c44d08820b001c0001171200d42c01e100c0c0641f1408c9600300040b8641d1400d002600001da25034107008180541d11a00160b540ea104007a465640e000c0c509224980c038004005000c3c01d203228550410101e80030301401c0d155000301035180601150081c0c80c030800300c0d02c4000080e01003040c03040000d510800c18104904042003550010f181103100742c01c04070f09054007141108800706550304455110848041c000c0c946041e59030085c00c0d83c01307944189a200c030b07240c980141100515030151002150f = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 210271798 1250 210270548 210270553
    0x7080121050303100920042601090609110612010e04030c0b07020703031202030906040f060b03030408011b020a0503041518240201110d20070c0303080f010513021b 72
    0x41400c000b0200320030360f10a689109003460041075000b140e040080f070706c808414203070501c0d040c6030001084081b00b40f8212a00014542040e01e05844428001c0040d5140705140000318102a460500c024000e904d10b40c6029020600c0212480c0841c0c00038641502c1880c4100d11542d0782d503145c104da0f01d003000103004215115500500034001d40004024081e41d200c1e0702c079000d9a81341002d0a400f24081103405204c941e200101045c042045841400eaa2a015080228482d010040824138503446a403060078561b40d1414012681a0303104219403080e000c52010340311106d40c03900c41035668012401181103a1000c6a54140603034014100403071040b03d01d9007c00c42065444483d851300c1d40d10402c001824040710340b032000c40d0b00d00c180700d02c00e060a1079158560030300c001c0ca5040c20042205104034581e02c200007d0000d903c007030b04030284c507840b1711600010902c5415840e00401490b0060300c1000c2d203004040040c043e940e12440c804000310880100141c4800b181e4050220b000b605074000300c2c050 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 210273048 1250 210271798 210271801
    0x1803010c0207080c0612060f030106090507020d03060b0a020705090703200c0d03060b030c0f0403081315030203040305030604090302190327140402091512040c0503030307080121050303 81
    0x6a00802c0d4002220782c898241c480952110007440040e100f95103181004a42d0781c0300141e061714050441c0403500790090000102a500c070070303d250884d10241e500d00050f9101603500b290f09076050091001038800b0980c568203100345244041d40c3c510480c002c03e8401c9002000160740301c0c0c4640e20940140054003c140d4804000c0222192280d01061028001d4020182142d1109029000303000c1164012001c107032450b91398044001080d080781c1c00708805100f00700800804902100050041d0890b07010110348410324049030100180c826403969002c2c54018402c11010076080400d8a40c0044152004a0240704e0745c6012420118000e01d14006d0401c03484140d41450350103292700c0c2412030400c0304245030340862030b42c00361640100c0c0700780c1030010b240c60000107090419402500441c83d0240c00c0303009800b00a65000d2a0780c201858042c1c058400d0b204000c01d10022103544c0e0000c0205401030340c030f98100a1401080481c0501507140c0b8002000e202047c03400500f50400400381d041016282c59 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 210274298 1250 210273048 210273071
    0x420040b03040b060111120d0e06090c270106050d11190809010e0c060f090a030821010e130816030903020f01360b0d090b0a06050a060302180301 64
    0xc5800581d0103680070011200041d0b25540a1a5801c2e051000c1200402000900000000083c1d11600c01900025221441900c100b01d081207420f001d03414030b401501d005503240040c40425401604080c40751030b03003200802c03100c0b402500100c0c1920000e18049a54410b00201c11010f88400244c14101e007200190f071070b80c14011001640044405075072160103540314610b099083e02c500200380300440e049805140b10915211004200a04520703907581e050084000010342c46030400d40c001e80392220002400182d000004a00c02080e5560600d075603540c0d4140010074285100c01040b0304e50501d000f8182100b84204841a20513808441e81e0009801d0326526004158104502c8101c0c014855604440304a40c0102822601c000c0240f1074400319480c3c6815011042c0000c5d5404115240d1061010031800d02060003041105c020500c041403100e01d914001302d83d5400180700c001071510b0001d00340075555501d03c05d4400c484c00b03440c0244e114410300c0c0d054860080100d40e0319a040d80b8140a4090 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 210275548 1250 210274298 210274319
    0x2103060e0a020a200316020f0405090a05060a0c09120c0504050c0414030106210f05100207140c1f02070f0305060402010807030c1b15050c0c0f0703050705042004 71
    0xa1080c1941c4105501512800030800901030a1010741070b900b00340142c000340520001c01d1035015000424181640c08d850703000c1303811a44103031150360141d000f1035a41070500c0020080f132034004e20040d40c108903140044d20002d000c0d40060103411184c45100001d01e0500c400c03c050f02028040c014410000c6003881040d0306400d910910800c1844c0e002c0c03829800f100c0c50184140c0c0114ac0c00d41100c44924041394070b541e00824000c01e41190101901d15800010035020004065615401a40103a54420a041c0b14034403004450004100e58001d2810114a80700c080e141c5045098102101400300340408003a82080c04d035800c0784020068509001062240000380f5a015174000e8950714201d4403002e05c00c5003614480695103010601101402e0a0300c48207414140100d801881403c0485600c1c1107520162001510070170303500040442c410ba00c0200500151262808034401000440e18654540c0d0700c407100d511804d445940e40d0700041c03541d003503070342c0301240c40c02d100041490340c4d551510b01014 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 210276798 1250 210275548 210275557
    0x2105070b0901120b0d06051e04030203030604050f040302070501050c1e0d03060803040e15010c060903030f180515060a050a0603060911070206031b0f0a0c1403072103060e0a02 77
    0x3030004402e0600f2902100c0c2c14820a0326030540034002c201411004d4031001c0c05030102410000c0c0d4896400c01d03410040e42c0c036040b054021840303940a142e6a00b8002c0401c015208080e202c040d16070100c405020020b600000c420003114020300708252140d1600e020541000c04043e04010381641c800080320f41c2e1407020a6001e541003080d2420010310f500e80402d00d54074011409084280b901042c08580101403014005048020500d4400d983c800281da520085d26000c0d10f046020030b481c0c0044c075030010342c14002c014509140e030b0340c40b901c100e6281e00c5456480d861120111a43e505c450081221501c0e00c080315806050080c0a455031a80c0d10840100244103a110b4400340c1c1d460420580c15100f4038008a1302c6041c2c00414443c00c40d00c071804043e4411841449480a4000c1000800308004100010f09842440741c1c541aa0000c69410f0800584902c0390002e600c0350030400c283d00000715407410100800003004040c405540c45d210302036004180581104041c41e164404018405081e6001007 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 210278048 1250 210276798 210276817
    0x100804021002070510051c0c0c0b071b030c02030109020604030b09120f040b03070207031415010b07030c0308071116090e070b0a0509060714070e09070501092105070b 73
    0x81c48144071007401203031a0641070081c19400740007103000c40f22180c41034002e402a4000355076800d00c0301f02401c1242c4111a004440760001c079071080c9941c014840e540192507030002c0913042250103102c0c521075120607142480700047c01e0000d08420342c800c0d91400d500001210b680602215505d6440741403d080070801203800d001503200f42e022a002550f84030003500d400c000100102800c144c20845840000d401c0144403104600c1405000404101110f4800246e030840c000a003080d120720442c4c00d001b4143c160405000483c2c02c0146200290384000512510350301450401401d44818008503462074007901843d002e4403881c40240050f02412200e88225115000c3c204034040d4500c50300c58540c0e0f06840391818066050090009082c02600146050384005140c0c52900c0d05a030f8990000d41e030a1405841a507000b0700c8240300075504a40626007085a6100810499240c4400203010388654001c20150009800004035110b1203c0c51101d0f0040d8404141c40220b6211007034a0895000784824 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 210279298 1250 210278048 210278059
    0xd0204120807051902090403030509010f05011419210206071703100806060a03060f0b060c0303040c062a02040908030a090201020706030e070e0603030f0a09030b15090f040503040510080402 83
    0x31000e07040944090703000607601911b181c0e0259640e440c150001e020062051a007952110780300c102e000c00a02c10b0354040c203403902c0c02e0056000104140030054022207600c0503401030000c0140f0840ca0205000e440000c4c07a0031903c021454541702241d5140600c0200405510030807691800102100c0051445248281070325481036595500d1590340710000c0c9c80d901d81100c1150710620114150f50420a290541c103c00420245101e101180f41c952045072800c0907604003100340002c0100101c80b0900034451840d0102842c03010020b210b40000201480c0b442d03001e40c0701121011034595402c0720f210396401c511416142c0c64001c0c81040540003046d4200d0041c0124040407500500038494480300c81c071014010044d01e810400300c1f030600c05001e0103155051009111888462041d5001000c901c810703603596081d07041c594074207101c0258015154040e07052075000040c031a42c8402c4213696204100420301d50154560f41404c81c1588142d81003540c001da1311000100482d600070174814011403003540c8 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 210280548 1250 210279298 210279313
    0x2030712031e090302010503060f0a1e0e0601020703080d09050106050a0e0a05060402031e040206070501240909020627040c02030703020c030303010f052202040f091b02060109020d020412080705 85
    0x1e04889043c014080240800c5040c00452040c3c11b005440d400148006003140c02e00350748403212114962801002414804950401440710703108501d85030b80c00c0402800100441415a134800e01c02d40580310403e1540c581c5c912480d802d002c025044640100006820b00e0341d02511a4030155681d4001c80c4c0b0000c0302810f085c0814280e0030540308591003504400c05181c01c4620943d21040312800140003640d0020f0140078030b0700810028410003055400c011006050121190401c52640c1013070b034000c510700b030b213000260300250b01c945048600c402c4803201d40c0b46030300400c4940c080f03041155a421170741191821940c2d00d0155000002080d01c01d0007034084640480000007003503903070b11090051080ca00000a01000f0341d007014921986501228200c111b0071840c004961000c80e00598010702d141c8507a00f0f020012080b06118030340036281c80000414641d0168a00695901ca0600c1100712241e03000031320709451155941543e000d00b01031a208840d00c1c9036410081001e8201c0e02c01941c0600880c0d0 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 210281798 1250 210280548 210280607
    0x3020102060609070e19051e01082a0a1803060f0b0609150906071a06090609100b09060c070b0403060e0607122309060115110304030f0203071203 64
    0x2040f00f0b10400c96a5035021407814560240110020b8006060310b00d144640c102041d1980c4404d0401c0054003603410316080d004204000400d008405401c1000b40000a5001644040c400c54820b0344403100c90456a550000210100c4d00b5518800060080080d848030100030410346401111500e0b500320000d000d0382580d4000c0115030b00c1014080e80d4840c036181d064414000684018042500c401482c0300d007072003a10340340c109e565040c100881c8646c80c00c0e40d00b085580d182c086070440c1c0000c000d0340c1044691801d1507081ca9050201d0140010507800440c100c400e80e640c6000b1205804801825100d80740e540e810352950b42e4015010446070582800005130f0600341c0000d450b4811003642d07031034003600020044900e009003542480c1035001101411080c08454002681c2030007822844000d00056141c4404400b02940c0a4000010406040302c2e9104410380001541d0540e034100c180b5244c00c030001d01c0007031310700251503001020400c503514100701415000a058031000382d090045a00400086 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 210283048 1250 210281798 210281809
    0x906030c020c09070302120115090b270a05040f0b0a060c02090403141902030c0114011211062809050d0215071a1303090801051e071403010609030201020606 69
    0x32415005070311520948102d490001d202d180c20500d581001843c220500c40052400603003600221020001040d80c40149a8001010b400406041040394144035281d49400c0c0000e400c1c280318140a1000d00e4a20300b80d0390f904141400400c001807081200b00c0404c10080e0260190800052141e5a260400101c080c0658490040254010308503180e03540c8541d4141d07116944016101d8440303000b8090400007030042e100b00e03180510346800035612000d1100e251420b5a04602c0c0c1d05940b0541c45004004540500080000c0700f5441125054070365034003004a0b003140140e1840300d08224103050070105240048850089084031581c1e803201c215180d4040c40000713190110000e401540520380f40c240d4402c0350000d05003061051103281c0f484d201d0f00c001040041c0b420303078410341c802144000600405070020020030050411200921182c5014400012a40070360200c1d612100d03020000500303501e106d109201c11102c40c00c81f089440b035844420041801d001800200e000d84160360108980b403421 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 210284298 1250 210283048 210283061
    0x415110115031e0305031f0f030803060310090b0703020d0905010903030b01260c03090c0d08030121050703020609060c070b0901080901050f0114040b09011403061810020a0c05100c090603 82
    0x1a26902c4ca0f51b00c076074101107070701844000c00c0001f4607002c03c1c01140303038000d407443c0000550003028240e4072420440c08050070f0800d5403c00060491810003170000061014541c0b550258403401e0060b00e81b2100c0b0400c60152041d2203004159504e07000689080503019402a04149001c1e40e0304a41129000d0710042e00c07280401c0b100511610702d200055808040c02e004642c003140650035203a60013400008611841003d180403240c4c03910200050000440c90071030740c2200c5641450b800e03506092070310740580360183e5000207402070f00005102044c03a15030300c0417200003005e410110307400b0540d514400d80481d0401525140061103070301c040741d40e4040c14050540030f08424030b500060f503464034508060b188080407459400c640c983d241d0614640e6100081070090030005008090b0700003c40230182807100003410204010540748965061740c0001455903504c0f40c1e807034801030782c0344002d50041e00e00501d0068010176034850490098588000ca4000c00180ca0702d41d250011013584811342603042c0c0c2c09 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 210285548 1250 210284298 210284303
    0x906021303110603070c0b0c210108010507030b010512070e060a0e13020403030f11010e07090912020a0b0a050901090b01030809031b01141b030c03070b100b0415110115031e 76
    0x402042c0f10740850881f0143d260000c5401500d18038004102042d505020740343d40c484407408000310010020030100303005965003d040c0380f400b001502809000602a03004809142ca41c6d010001f0016250900590121a8200c40100501c2e01d400b15454010320a00e200348099001c1c0e40380c001a03520700711050090350152645615100d040000500c02100c0842c010060882d040d03403502c05c4c500e191201800b803100908405640480d40f08160700300f1422503400808c00320215030051441e1004203209030102d5800c0340b2601008a1607454000c0201d014004e80300300540346007882800041000680d03c002c1018200c15400e40780c07a4610703c240c211084044001c0341c0d01040001204c91300c0da484000040060510340c0c0000710b921281c446a440c41c64005e000b1401041c1d100082d41d10502004444072940680c44100e440200b600305503813820940260b20400c0e5200300e14000c51146240202c1040000300c80c500002c01c035490700d60040b202c9006003441b0513900400754a20501d0895406402c03120600e4 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 210286798 1250 210285548 210285557
    0xd0c030207150f1104060f0e03060c04051203040302030d052203021e04240608090606130c05070b07050d0e0102030c09270703090c121a070201090602130311060307 72
    0x82c002991a006004650940040155900401e01c00c25505102500c0541300d56500c5410713400c96a840981310109100d0305911a0b4400410026004214801c56040e11000c0d0b80d92489054103244c4640340d070140d034000961500501154602c8140e0200c060210b110300d031800c1410f07803000b08000690b610202c0c00003079007005c03d80b00010a0210400c105010180b80035100090213501e80105102c2025899030b401400c41d517220082140340da00c40380c8140c101c40c52a0107010700d4204407002403070001880401403039144e01d610610703007014020345c00c0e145866002121082140361800c80103005920214100403401d00d89034004e400000c0c14400d607441030740c180b0000c070b1500108900300980810038071312130510001c0c00f03446a020420b00c285114080c1d20b0035200400ca9000901c1c147d2581c040c030b500010501034130782a001020403000d4600d00e08000441050300c1e180c0d210440c04a0150000f00006071415000040b21401045985034420850340543c5090416030880d104216076440151064070014 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 210288048 1250 210286798 210286823
    0x20a030f053409050c0409050103060b01030c17040f080423040f0209090402040f23040b0f062d370f1806090e01022701020d0e04090f05030d0c030207 66
    0x3003d035200b5034200080c0001c4c86d00b040d903148200350541c2c800740c00071100300d61101840d10041d6018000e00d8030341d444c80d0070040c05900180408100c0c4541c0180f0103014816040e6404052002420407039000d0490024106080310300304556803428001000014029031030550031034003083c80d501c00c1d03e6084000600d201100d803500d4082101504250f500c0341d0159075500c0348203014034104410300c005084600d100040030314040c200f1f01c001c220024003041050741c400303041000c666500c8488a00d8046500c01c0420990404c14101107900100fa4541d504100304460b00760369046e5480d02603c507011003201d00020143c0c6001400740208261246072034040d4010400d00c901240e4001d03681c00708100b0740c80000c845c1e80e0b90b00310030140c030001d80e1429826540000c11010740002000385070302400741e11050021510354000001c1d03030f40c084d4040708420009003d07641c1e9079950b0f69403c0000400c1e003059190303108420302e0130305980701c0e4003803014038034014074110408503030340c1c021300030340e800a6003041c021042c0e07 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 210289298 1250 210288048 210288059
    0x30e1c170c0c0f030f0d090321050706021614070801110c0303040314090a0b0315040506030316050708160f0e01060207090207030c0b090c120102030f01030f020a030f0534 75
    0x407039041081d40c4c0c1806215042c1a040208201d000c0d0a904203940b0b40d9a002d01e982440c1201c4410b0285031151070209448006000f50803c08071480d403540001c006a0360700b8108440501e2201c040780080804c900d450848030305400005801003961116402080f604a0001c1c0f4803106110b05403080d800780d00140002400300b0301984148841581d0013a1091408101360700007884005541c11101b6151000b00c1400031000d0104c0503195456010317202080a07042ca000003a54900a000c01444030300c00300b500e02c40c10050280000700081242104880031590100001c5054240501400c600b200c0303d140001151000c0c404000d040303039820340207002087d0410703141002070750104000740c050280b020384010000b0035070b040191281919078040d001000301c1000300088014000c030103068aa0050007480440d1001c4480603045039400140b0031240b00303540c03000c01c0e040011940b01038016000d400701c400c24404082003100d883c4101c2221204100c011102c1248204598020400c00c001c040d03005101 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 210290548 1250 210289298 210289309
    0x141201020408060f091606051309090209010e0c0c070b0712080412030207030306051c030212180d061d01060519060f030e070f0b040806010501030e19030e1c170c0c 72
    0x2040214002910718200c0c401e1406c048010032a880000041c0c000245080500802c203603220107840d5641003400b220140e90000b130380c030b002e0602410000014590109804010b00c001b144c0c1d4102d40403040d00e41d04c0c0e5484003050364030340011105482c0207000d400031549543c404c1c81e60034410f40e40200310520034080064101c0c0250440c0b0b80032000c0c15511100854556184072141040101403242501d15125a1900074284920884503103084401401303001508524500100794085056540382486002c905085010f000b9591080350050740c44401d4590801d810b4011005840781a1040c103926100c1c0078054603248032612513440022f18500203400424420381000004100a41c2110012034551901000c110444d910041c81c60070001000c2140c20000c3c4a1140188000d080400c910800182016140c900c03409040e081c0d0302d8100c0c0030b41d04140c056224a030103984040c0002c3c00f0b00f450307903440041e05400e4080c04c2d20708034080350303c40da02400c501040794030107a051006880b05080c4441400b4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 210291798 1250 210290548 210290551
    0xf030106050d06090203071a2101080d05071505040b04110312070201030203060f09181902030a080f040906090c110a20030a050604030216060504060c02010503070c0c141201020408060f 81
    0x80e818000d010380043c02d01c2400c4500c042c684154051380d03030798271030b02100c5020000340d00180b8291010724000400000d6000b0a40c0390003a000d41c00e050360b46a10518001d004010b8401075160514502001d1100703110300071654a200710b200c0d10904922001e0740701050b580d8900003000941449081004d940154440d401441c3c00000180015142d40080070004020960441d0601810001e82c8520881c02d0000c02c40d41c40c08442d140b902c01c020300160340200b80c0350106150080d040100000e203078820101020110750060081003c01c0080a4071280c03002c000c0c022500101c4009003c1c800700300443c400114034992100d83c80ba90070b494040196030014a100b001e1141194075016807200c0d24040b0703505000252240384254098000ca00c1e142d0015006103106402c0402081402e00c4188842d50300840110540c5809090a9440750b40c3d1070000c4032407580c000c8004082c0f20040b48001040071140381c0800f2000e0084602100c03aa1800141a0807070050b0310032030040c1c0e0310000100700316810704200c45 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 210293048 1250 210291798 210291803
    0x12080c04270c0305091509030403030810090e010902121603110d0b13060518060a0f02040b0a08150f0a1202120f060f01320103020d09030801050f030106050d0609 71
    0x40c0d5550800107420340c1151020242800030a48030020400e54660501c42d003141600d50010545040c1444c061483c1d0724019404010f080c809400f020401e5501880c21480060694040a11010101c005c805002e000d2000c8228060b080350002904029000f05a02c1d403403409504c45117a4262646c0c594403c00003603c84100e810018442000012a0b08040300521034851340030b42e4401c01c2024940b007000c64400801e02c4a4005005031048410080401c080d5000b818960340400ca44002c0600c000c0203200b942e101030303e0000d0004040c1000d0b03810101e1184902540c280d00b000b0b10f00e060040c0f0850300010f0401c241c0c0302c5003040081c04a00041503000681c60b00140c00107800145031003190b4a480c58000302c0c3d030300c264401d104000313a070082a04014098094044521254001080c24410394111402001100203042c1e0000809911a505071580503c40c00c405004103009403d0241402c40c0a0080601420302d4201e8006075080500449003250405000b44d2035040890f11460000c04610004 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 210294298 1250 210293048 210293099
    0xc090c021f110706050609070305010812210103031107050a0f05040f0b04020c1c020a030e09070c170405120706050a20010908030f06030105070e13061502010912080c04 74
    0xb20b14400050805420000d10600000a0b030b82000f1041003220000200014200b60a00005100e0a0000b01d121110b5280c0b41030341e01e80380c220390703c00030b1402c00e1040643c50400144000002c00e055208100e210b800080381d06841c2259210f001303200c0212481d0295190300182520b0130003507818150b008041c0d0088000c1e0000b0b08010040018050340d002c00c0344040c07240c1c07011464424a00710b090180561803500e00003000d408106940140c003415030305000303e12a42c02d85002401e05030140522038001c2c2c0c0e05c10b00c0080842c00b00391200d50507070410301419001d5010700c021038082d01c0e00003842000f42c03a035540761181001c008010440306070802c0038001002c0002025504000b520901440380860310031002c50781c072464607400c0710084042c028071081c8640e0520050145031500100c1c508120101507880c51000e0503503aa4103005016990301080c5170340c420103030790555150306611012885100e006000781702101780004585045090768807003d11002004104061080e1004000101110014 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 210295548 1250 210294298 210294311
    0x3030b040c0507020a08030a0c06020a120906050a1d10020307210504110f090f1e0906091207170a0c0f11011e080402090907030516030c090c021f 64
    0xc1001d03103015040c08408140003040c48011481c10032072200c040e001e02c100550400c600040024459000907102600050780012140400c501c5401c02060180c4100001d000881d020320b080c40050104840c0d911815141c00e4a00c00761400c4071250503503c46401c801814111000035070007000b5031000c4c00c1e03002403142e403194403001611100c0c201c02c6901c04807800061107140904059401c456a106414402c090384c030880fa03900c0d942c1e03241244e000301d6541c074015410340d5084840440002c0c0d01442d81c000e04884010400c000c44000740c07491203030030b04005840403d510302411850900403218024124500488000651215000036004020461a0071100c0c0c0394640c07140089194086401c1c0d03440d84030004e520ba25541c002e426052030150400c1c0403020000c190b58014003042010304001e2040e45c0c860013182c5805020007a8001031030304070703055901010315544141d80503095032204503003030070ba0018002410580c07485009507201c200c1d0064844480c4000c445090030684025400450b6a00c15 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 210296798 1250 210295548 210295571
    0xb0c0c0705130609140108031c060512030711061303060c02030d0603030e010206010b0903150a0b0604060801090b0603040201200a050106091a031606050c030f1218070501090605070303 81
    0x40d40c4190300e002c031440000300c20b418004800144ea2038141507411120f02d250041205000c00021100c8204e140d1466200e40e6452003603501c0540501c0c1d00c2194400179107500c4400000022008200c03091241841d585040640030071301540740201031311485003a07a08542080801c5072a00050080c0c031161042d0392500c0081c002d0b86007100c080350420b42c0011030f010242d1005580402580b4050500d03039074000e0070460030b0b030700203544c620268410741141e940001c00300d450302c2e4164018002000c0003c000c507845a1300c55800038000903003442404140c41c1071078005183ca05150382200d0007240c069440311540c0452042c00d04076002c10740c0012a9134883c0400810105000780f0814000c0c0c201104d0100d400304000d2021103140e903a00c140c00e0b03c80d400030315800101043c040c2c1c080d01114940d08141da102c2450000c51420b500030134000418446000600c2d02048100700601031042c0d00c6070003160451003400c100f05035107040d103014160108841d003d05120150081d8080c01d9060b109140209401d20440c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 210298048 1250 210296798 210296809
    0xc0f10020a0506040602040914010510030e07030507080d0206011418091603061a03070b0316050c01020301030609020411190302033102041d0303040609080f03041b05010203070b0c0c0705 82
    0x11181075038501d41c041012301031840790303001d0b20031410f0400c8480442941010009040115611901c206141c8d070780781400884842401040d0056800905035806160303191940e607259001924014014043c1100118070015a0ba0030700c4018280900061943c00132080c11008113240509034000621500d400d8641c408002c1800d0405940700d00b0020580601701400d4051600320041c91500c01e030131596040c00002c040c03005880d841804441d20280e6000e16100680700c070300c544039100f000c45d40000004802e100007600700e81003d03032081d1010402c1e40184010340c52039004001d40046021ba260030710007605442034000d1508450483da0ba260411120079040211928448442900342c8800d80d441003985820310a1502c00304210500d000d40d0508214102d4480c400103000401c203d070313683d0594081c081480180d41102055018050f62400c19050100100c1c4d04442c40505600400b54003040d203501c084180c0e80c4040e800a5114a26207450403494001d0704945060050752040000004507551030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 210299298 1250 210298048 210298051
    0xd020309070602011118040506060f0304061a060f16060b0a08010b040b0d1707210c120201150608040f060204180b0f06040e09100c09170c0f10020a0506 67
    0x84800912a00b840e0500190a5036000180501e084078180007008415201c2e021010340003908503000540d50ba070b0640065042e028800d030290080c034000c020082040341a9224565000f081d00c030706890340700d900040128610803104840e40e01e40381030242c0307020710240900b806049842800042203030004a00817603c082501e074081942c40e91565803181d0141854800c41d0350f034407400e0300c5070071601240b612018411904c80065400394140014440c05000c0308207880c0000c04540340c81482107500d400001807102000e42002c0e644003070900700c520038550052145845a08100e0861400d003441c01d901610761030340040040e070781e0072088d0302c01c01d0015420344000c001400c41318101c05500881a901da4048480040030240a800002c4d03914907559504410369085803d225811541669812582402d00141042007001c640c1040d142281064004c00311000341c40d8002d160701111950f4182541c0e41e901c1150b02540c0001e0058004482c604000703101c441844a1030045038172101090f035607540340a60 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 210300548 1250 210299298 210299311
    0x27040e070302010e0d0b07050a0c1a0711060103052505151b07030f08070201030905121b01060e01062006010906050a080f06150a0f0b0315060c0a08070204020d0203 72
    0x1003202841190382080c1d0000111000780c44040707401045688102d5802c3d000f40c07220051050210300b070b8200900c1407101409460740400d445003103941c0d10503504400c40d000e8940c0b801040428590f15500d1000040e11380c1280d404c20000c046008071005410001031415080e00c0c1d0505001c07101007450f855110300003100404020075160345580041c05180001c0e0000c1508140d6001000c0c10004900201200d05049400c1031a8955509062005030018841a54005d00314022801400c0a12100101405900b40141c0c21402e117280d0072098503080356203600a1586074101e1800500c1214072403009190050f2a48410a020407102c080146ca0880c003640011440360300c60714180503a06152200130028105440100103151110188903140c0b813008046120b541c903030f502d21104070b60340c45051400403c46ca01442d00c09549a806222181c0c2c0103d44e166018541c3c1101403803941810403c84440c5d80b0b210000c8c0085400c15602c40300650300c101000d07a0310503000c0c00004208e00d03161000794003404 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 210301798 1250 210300548 210300553
    0x50108031303031404170c090106020a0305070206032701090b0c070302061621050907060804020f0121020c0c041401060207030b0c0405060408030c0c0a0b1c0212040c1d070527040e 79
    0x306102c04002000c23405800c00c3c0c0454010341c20350710000c1e4010007556099641182c00076104c1d6a2441300e035580c2d84c40600d01c075011074012009502c0202065001c0c410f828051507030800159158040d05005228206004005a00050000c2d85081540044004a0302685002c2c1501e040c07240d407000c0b00e10050180702088a94071418000c2c40441049401e00609080c180b0400c1481c107500050f00e200c00401c0e0846c140190200c400382400c1d0314481f900120180604215200c0031421900ba940b0a002c4480307a004a1411000782c0b091800c906202d812501184e0041482d0b50450782e80402c0c940c40546a4105410203000103e040d640708005400034044050003562102080c0441904e8000300d000e05500403072594ad401c0c8808250b901c111854000c2c00100020481903078507079080244102146107241d164440140810450002000001c486450208030103990700700603a1000403105590000105404011018003010750f101a8003d0400b50314800707824106c400045401c1d00c10280e0401001d4 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 210303048 1250 210301798 210301813
    0x50d080f12070e03241905011415120117010b04060605030f160e0402071e0309030c06080f04030c03110d03020d0c09050a05120304030f0b010905010803130303140417 73
    0x583c0724011140702041140206001403000b00304030b106049180a0011300368440000455076a091080034030604080402048190b075103890540d054118030031014810f410600f44801d143c140641170768910680181144861b9280c007503100d5090100000080d1255200c2011842e255034912601004013055250565a89444104002070040007014910b1542d11545200300c04c0d5880f4000c00003a400c1500e00503a900b2083c28411010b40051900d02c50002e6a409584105075000c8400021a4481d40a4940694441d141512442d000301d8008284824000006010910a0b98a030303090070301034100401c000c40f0100303403a030920345030030064030200383c0000f44001c80312040d00c0380b0404840d00380341c1070000354105000a00c448420340700302880313001d1400715030340200310900890340196441207403100411a2464000c0c8407038424484c0304402c070314150002981e41e801004840c170321032041f000da0500b2800e42d581914090000c4000704d0613000c00b1b01010038010085000d82000303903004401007010 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 210304298 1250 210303048 210303061
    0x12051605160504051602061801110f0d0615021207020a031a070915120504050309030a0609051009150f0216141c0c03030203130206120901050c03090304050d080f12 72
    0xf514009408805e040e500c2c0804142080c0e408a80c1c80d40000c5000000d9001401e01c6074000e01400c40030714400095840040e80c1d20301001e00f0002450300c1a83c00e00c007030001070f03510480121840403000f44840580c0041ca801d0082c10001c0c40140203062000301407060603500ca4444e22031f112048100391201062800a0010305900030840c1c02c01002e180e400311025a400c00002000e0441004a002205449001003801c01000f84180d594840000e800c44007003259a0a001c00130b0300b2299000c1d01c15000d501640c0607983d10f1070107000d5281c0d800c1201004000f84050341c1500401840d42c420715030503824070400704400060310a041145014035003401c544c50015102c0e505000c0030915604082180d02041a2229000032a03682c3c800d0b01401c0050310303941d071290510214150742d48000e5111301d001034402041c000c1c11050714003500c01d0380004c018a644600d07454910344000c0e00e00321581e50061200708550300e880d1003000c0300f0512071001e1174101091400340150a400400041440f0802035080024 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 210305548 1250 210304298 210304301
    0xc02090a111b030d09050312010603110a050d110d0b0301180f0209040c05180906100609051003090f08030610050a053c09040b0d12051605160504 64
    0x400202610081041806401e4108101c0c45041c0d1580c180100c00c080d4403519800a03c103a0300c0d2182c00d054140300403c00751070510b4582e4800e81401070954410380011a42520900ca41d00c0d4008006001a01e050800502a035083e00900d0301c2d9a601d9803900c0000c0d02850018002d02103030f8903501400b081d0350856500709400d5940f410a8005910039103803206000c50117020b00300f40a507406031081411502c079070918403440c42c141d0300090307005407410300f4440708170441014162240c0075040580f10b0503118544d48040d6884140304450000b031030f51005101c11300d410049059503030b0180c02d0000f1000441d0ba101c05030100d01002c20b0b1401400801080124140b2020701486200070380b60652525981c6000505039001d84000443ca00100b280f4011f40324442c8090300941090502e038602c44060007240b101c403140d10240410f400f40382807012104007410070002245031749901c01c282000c000c50144041358150040c00121070034071541e0b0007400c0410400c0c09801d5525500c155620301a070300381000d010 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 210306798 1250 210305548 210305551
    0x3370821070e180403050937090509120f0d18050105010e19090602121006030b062b23040201020d050f070b04050c1003050609070309032a080a0c0209 66
    0x9004442003c3c05104840c45840340742e610603403600305a03444040301c00200701d810403003440d8800240c0d03510803c002d5881880e082101e10803007041c0349808940d140c1c5d01202c2614001d60b00d2051550215000c2c2450003d2070010f0100c00180744541810485550302d40300076107815000c1c9030b0000d4001c180003001c1c000700f800703240d0241890820f04241400c2040609807550504d8080c0c030385c003654502d80c2c101003040c2034040f610840c520040001207401c00c1d50704040011141d2143e900400c0c5403480248030f030700f4603200380e403600c4840300c451115040740340c45046185001c03091001503295403080ea00c61290070b0303230b400043d0706003415000060f0b0b40341920000e407a005100d010401884414404800a0800c000c119054030f1307480114120191158a856441c0c42d0240208a90200c0b952107401c2082d54543c0c0845c0c0b060008075a40d040c940c940c80c5054044826610014000441050b103064a05800c0801c203d00142c0390144000c41d00d005407141c15454000b00009000034011a0400c0150319040f41d40d035 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 210308048 1250 210306798 210306827
    0x61b080603070603140a32090105010609180b120a0507030b060306010b0f13090501090207030e0409030507020d0309030506040b01091a0a060c0204020d09060204050337082107 77
    0xc00c2403905100c140451208001c1c2142c00d9940c4628940c10306800c00480040010107c0d40d201c010082e248041c0300300b105084500400703d41c613003800050701030b100301c81e00802c0f100c091203000d0078990300d000b5103030103824039141d01038024009002c20390000c0801c010f80424a400307032000e450744a06501c0d00048100c40500130728840c0d0311a0f4018422601020b049441c02440e1380445a6282101d07103803480460481e80c4029080c5190200000d8020021b400406a142c82a510400d4000d80c00c42040304940c9901000f0740051002d000a0300142840381202e8074403400382c181004441d40c2d03070340d82d6031514000f180c041b203481003140c004100401c01e5005825009044000c070000008082c0301080f2070500904c07d000c2040b560241d600e040d0340f99075044920040d000e03030f0140010512070501d00702a500c40d20403d8017920400c1c0c012140101340301e02c403441100070b440280d240943c0180b4401c0301d01820740e5054912403000c2012011130900c015810b42141d08400c041c510f40d10b44242d002e0282e907407403402d2 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 210309298 1250 210308048 210308051
    0x6140c0705150309160f0e191b020d05070b01090506150d0204060801080a0f060b04060f1e05010918020d0f0c08010f12050303012c0910050606091c061b080603070603 73
    0x74005204408800300960301c00c2c24036442c40d40c4c3c0f104150607200c02c030900c08c05191407800c0c2000001d00403c09840c40004220303000c8954001c23214030100d80d94071510034040c0c40740381901d00501100741181c102a07000034008017428210400501d0221440d40610401e000103940007500b0004c264200007524010503610340940310030181519103011200c01840018240c40d0350b501c0c51840ca41c0c0c1c5a00100182582d40e084110071911080180c007070364081088071604085036a00000c0b5036100d105860103a503c00060280303034410f070011040103504421218007525445224041020007140b0800451000b10342d51710086501d004041d0141c881d142d080b00d5284070741c0c1002030020500000c1242d04540700312311307500494100941d41c0300480c0107400c042c2c08500f9166051003100f080c0040d02c02c1d1071f1340001d1800c01140e203442d0108845d5218641c1c1541d00440c00310102c2c40c1050390b14030140d006034010302012410440b0401c80305402130300359421501044d9001c050102d98101046070802401b21400d0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 210310548 1250 210309298 210309343
    0x6050a0503070e03070f08160506030903160302030f0d0902010f1b020114040b12101e030f031403010f0810051302060309160b070302010e0706140c0705150309 70
    0x1004285110003000b600c00d10482c0402803155450800c50341c0d0040c000d03200c3d0b804c5010b844040054842c80142c095640ca10700ca080e004c02c1d18600340c801c4901600c0744000031841c08047c0307144083c21602a500c241c0550100f4800c075603101d0441e000400d0301c041260800203030203c0510014003001c2c90240303000100481c4075080e840404c0300344403506045409003409520100700c030001c01828070035030308101141000480c0250b041100c0e10702031401014038104030504c69807202e080c12104110b2200d1085400c4245c1800c00106440714612b2440c1ea0180c03402040b03490540700003c03032690003a0b010014000700c10201300051582070229860b903080c1031200b07000a00342221030040b031456980020b8454240040495141c007000c0103000d01c0300629100c0301262a07a0ba04280005400c14007055016508020b01d80713103001000b02d500000d8802540f51130400c3c3d8448030300c0c030741e49402c400c2e080c14180c442c541c0003040d9030f80c6022504500c40a080300465492401148e064280f0212a00f4207144606012 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 210311798 1250 210310548 210310567
    0x50601090b09130212060307080c01120c1206290c0303070e180f370209010e1207060306080f03090405060a0509070807030608071a0d14070e0a0605 65
    0x3204142200c029100c0551944910000101c8102182d00c103500321500c00240c0c0e10305503506201d100c0c8215022400d440b601555000360303035100c43c00381c43e00fa030014080313032150103d50140ba4064914a0701e2458000442d0b001026a04101da00300d03001092011040c0701c5050628040186031008524074042c0d081c18008212091a940d010290907042440f10780c1c441b41029851b02c5510310b0000c0d403403444d988458207000c2c94800640c5400d1300c480610310f0b0416400340348a10451440c00c0440000030b048105208100d040741c0007500008101410490450320102d8181c0d02c0c040300c810104005405801c880d45070042c0582102e03400e03807060b58141c0090f4405e9900000210907103803035100c00e81d80400ca80c1d48010006950a0503500044d9201501005001c14141e002c0c60561051b4a280c400f006615140c4d5101e554035401d61040520391844a225040c0b40a2034001904146036120400706040c10540796400300a40704613184000105203511034038031480c15803401c030010001d50528915045444 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 210313048 1250 210311798 210311807
    0xb04050607113f06040f0507090c03060503010c030e0307110406030803090604110a0f03020d05120a020f010b01080103020108010306150503010f1409010c09030f050f072601050601 79
    0x184162481008081254410300201c0c00341c0c800d0901c8024203030701c50f0302071440c0d54040910039200d101c1c148443c12040c240014050300e50b40303840700c0ea202c0e0040415030340b165206440c8950000b401c0740e0b5401030031400680310300340d4020000d402d0130680313012400504280c00e060071981e8000e5000101400c0c0b50f55840d14140200071105002d410080d4111000c0b80d40e00481c000d448150710080c03007043d00108220205101048841c000c034410740c101100202071303104015060402d40204540e41c00340c1d85040006203002500e442529204006603202000e140038440e1940d04503002039030160300145880600d50030f00b8404e00d0348a1742e09003005105035041d80c000905603403050000a0880b0f40c2c5010b104420312507000c4140080000030001c3c0543d80b900c03100403010300b0680200050f44142c00002c1514610180030b18941412240d841c411402e00d15140d03102c0c0f41403941c4055400e400340490b40100420240617980c00307014a1a078400412981c0c1c2034502e6102548841ca030000d0b4076100504c0403da900 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 210314298 1250 210313048 210313057
    0x8011109090103140c030a031d0a0e0c0c160806011701020304080a0e03010e100c0917031608040914040b0f090a080a05090a03063e130302030a0c1802040b 68
    0xc0841d400300d10503204404d40c505400c810149a141c403403101c8a20405910102800c1c120f04a5180054070f01c03070312018000650864021240408034510001d1140141c20000c0c0c003c0148002c01c913144401032800400e080c41c0e1135000080300e504214010700201507503441c0f01d4141c001260003180303545040c0d10340320740741c1c042c1c0c085140402909005c0e0301c00c070341c1d0250048035241e5510707000e480f06204141044402844020f0388003022400b030920002d42089106002200085168080c51600050725800c0740c8002ca013400441d2900000e100100b900300c1d0500c1841202050182c500c0341609040c117144081034402000d80501200800400c0020040130030340709140c0d50312810385502c1d00c19404041d6090b0181140840d0060559a4004280616034006114031403503240481041c03156004620603480d4544815a46c001502c4204140c0103038038002441e14440c3c3e00c0c069107199440b0750003342810722805050342c903011388041c10b00c42050490340d01c40956899003021403a00d80f400c86468864080d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 210315548 1250 210314298 210314303
    0x3c180b1807020d0c0c0503010c020f06090102070209060405040201050408070b040303021b10080c0d1802100905060a08060a05040f140f070c02132a020606040b0112050604060305030a030608011109090103 89
    0x1103044c0360004001460007400e002c1d04008000344080075103520001e5950720001c01e442c1d454801c01000c80c0100b03006100300d0341019000f40c4a890140d88090900020380000f41c8203e040100400c000201c0310002c2c00041d01401201c00300303554451443c2002440c003500c0942e420420185410007000660714001c41c210b500d8000d00701410540d840140c0800c4a000d0003c1f400a101e0900040c4a00400c130001102c540510890740d00314032a9004004131020070b503078090542c100104100c080c0c40c003801a90300701d5100000404002c461600c403070205040d02c01d441c00c0c10514545500c01448000c3c8a90200d50b4071000303c200c13031002c524202c3d40003001d008002801034000c1d40c6c020300341c80e14201e80b500040f181841010203a00b1a000e241c0c91180c250222015150040c000c0074041f40c4107103000d001c0c000252805a40311083d40c3d400702ea07400c00403e005000540d1280da1a000000000c0302407000d4441090141c0780041c855103040f01c1c1d2820348421030301586000a0400841c40a5034402c81d0702410b44e81c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 210316798 1250 210315548 210315557
    0xe010e01121416080f0304060f0507050f0d050306010e04090b010b0f120907060909020901020c100302070c0b0306030705121b011106010308133c180b1807020d 70
    0x15060b080c1040c0c1c0d40c414041c51074150007000069202000b0b0360070020200e4a2150803104218102015140ca82c01075001e12030000e1200c40d900031000b407040c0040d02005010300309590141c0c0242724040e150914001c0a140822808402c10401d5a002201d070f15211800b51000d011564660b9203407400b030001409040d880d02c0f0003141030b03a41040b004041c0c1c0d42150b003e1003140c8107810032500c8035543c0c80584c0304900000341041c1d004516649140290703004510306030001d224900c032020420800300090781e421020140d00307000140c0801c0d08400303000300074002041c0302907503401d11800f41420900b00d504032600035200801c510070301042c0011106a08002100134800b20540100100c8541105960014030392086100100038007020a004240800c64aa000260305664052603400c2d100b14900707605098403000061512081c0f0801084030550380c0b4415104455102c003a69111042505100b11000d507540103a150b07107080c049120000400001c214940520f8074050003503a50710300414180800 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 210318048 1250 210316798 210316829
    0x703090501030f060e091506030304080d0806061918050f060708160c03050105060a06111510050303072301061815120501140f060d030311070c0815010e010e01 70
    0x88000e5400240a007400290303071704040c244a581c042c0c0c1c51140d9800e1180b04944800440c0b0306141c0001202c0403641058068180202104004d0303e02c00002480980c01400c1040641c041c1c090b41d2002c04030b030602c951204540c20101e458140071340c50072030708280d0107800350f486078042c83e5460380305803000c699024501d5642e0744641942c4c402c28049148000340a0904184080200541034001c1403150805030f641c010915a104c8044038480d036125084070298100500c2c00120030001c801d0a54411100300c0b201d201d155079840030070b18580c80a0380c1502e42c1d640000108400080c911001424100d003040207001c000d040064a0302d01e00e814291150380c1c4c0e0345d14602c41c12446d00202d006001004501001c1440d000345081c8140a0302c074a60410103402580000110311810f61f04446004040190103d42c212034180e4003903006002c1d050003405d140c84103100800004141c01200d402800140b0054a89981e0001040c07680d40c006802c4400d04516850040c01603194010712141118600c3c11061004d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 210319298 1250 210318048 210318071
    0xa0827030f13050301230a050408071b05090c09010212040602121303020d0605090c04050411010c0609080f04030506090c10032c07150e10111501060201050a0c0203070309050103 78
    0xb4446194081500b42d4241204494400c00ca03a00040c416191005907a80710b07503c640610085070000c440042051805000040201c2c40060754501030840b80c40c0300030401a11080050500407040b40e201d003419000054090903540c2c180200c222110701c440301c1e80e0426082c608041c3d11518186003000c400b110125085051000e44440f0600468010340301c030340c0049150400b800604800c07100e6149600c90090700075107a0510380300b000d228a4004c041d031070525900304011a1038080000c01519210345522080021800f13080c01858419081411980d4032407035440c0c03a605088000741684401c0e08a41c2d80d840060729040140d1031002400e20b4002040801d0020000d0070004401c2003840c41e4020714225045241c0000e60306095425a8601000d0f4088402d4115074152001e0401604411422031072020180074030f0340703400d4030310354082070b500584e40c1521a01c0c081d1209a10190050391107005000d000c41080c82075003481046c03071004e107251031040e44000e40070b05943d204013410540e0707800d00c1d6840d = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 210320548 1250 210319298 210319327
    0x70e0913020d021503070906170609071b05031803060f010b0409051816090e160306090203010b1e090105011407032d02060609010e0108060103120e04020a0827030f 72
    0x112181a004107a221b08103000024030f520b11900074200803c070240541d0030304201d011004c503c00d8400401020780d9580d003100c21030b60025000b0b800d500320306010441c0000200c0a2000c0c5c001d03035200004464404070030400b050300c0e000d4054150400702000d04010702a86503640704640c2628140e130760104042e11800d001c48011440701c001403406008079181800418401c0100d4411205100360503c003d00840c0c05183d190314110721065810404c02104000042c0c6580003801e80b240010000140042010040752071310719582e9541f104106201d40350302c1d2901d8400a0345014050a1030b11119404420003002080d10038064090b0911040f4065540340d04003018681b0960400c0035165181e0048456010f59200801c2d80e140e072150000c00c0c008a1070740340f1f02520784c1c100c1d1550703c0188210303461500c908140c003c4288100082002e2704200c41e100c1c0d00c0328002040e0b10119552032114034a842c0d41c00c60030320761960b03041111010a541c1400c2c883c87d80001030307603601d100d0b600d18aa682c2c02c51502ca100d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 210321798 1250 210320548 210320569
    0x714060d0c11070e240301090f0804090c0203030f040f060b060c010e100b01050f0d06050a12060509010902061b10090812010f0b0403030509010e120105070e0913020d02 74
    0x945250404007806200e6a01110000d8803941e004115003055480358070b12000d09208603a083c20030b1090240d170704181e0400f0710f05030665a4000d070000644c2ca100e07480390440d034100380c0010b0310a040b00040801020311503118603101801e10b41701440c15418500e4038629040702c090805020817942043e0001400002c3e80b10601a0f8070092000f942e903030034090b1087c0031780041c2c1151401400740a000d42c0d568000c60103a00301c50807059481c0780c0707007061000d03000441c0c1d004291900304149c0c2e140400f04103a00d9640e11103000d0100389000341143e169a2078610b060b203200901d01002c50741032541500041e111a0207649011008103850b03900c040d804440340c0c0c98030101a100c80060750a22400e001401030007030007403140c2d50540d00380c0709190b81c0f2002081c42c1003c0500c00c441c441c4000300020000310b032080c009483d00e1401494443e190320001c600082c802c0407214000070300b42c1d6585003803100c4942c1107030034400480300c26180d800d080d00d01b5081800070503c54020207400f5039681805142190f44410142c2d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 210323048 1250 210321798 210321817
    0x3061219060f1401141309020a050d080d05190c0309110918030313030206010501111209040608160f050f0a05090702030c030301030f1703040b0a110c0f1605060c071406 74
    0x200a03603561605c0c9000107284044c864016445006c0c40709a000c0c2d180500d0f2015074001e424081c607075181a0070b125540900e101e05031856001030001c031425844501a450084468007a92900c082003070340d081045070030b0f0030409000c0c0b626054aa0001030035244010882e074004442d103020603a20400800aa550b0040b91030040e4040081000020010b119011100c140282c0c2156042c1c1e890740d005403000c5542c4002c0c401c240d4080142e40c14032820150007400115030191021031156658819640362100c0d480001c09000003d00c0c0c240000943e0300f200d00c0003058200d682c03e54a102c4035000c1690001c181c01040d001d181034200042800c1d0081045072440c03404030b8200c0b5600c3d80e590900e010030f403000140c01c07a1411000044540d034446c211f003c0c0e0740600c3e0000000c0303c954840062003401030292b44003501d0300200603c261441c0c6c55003030040118024400001c0c010504500454604c00c00b03241d04403510410062080712071603003001800100780d83e50b20728030082444610f03002849601a0814070b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 210324298 1250 210323048 210323081
    0xe031f0e01090803040c0b0405011b02030a0c060f0305060f0a0302120a083c03011401090806100e060a06090612020405040614010f021c1b0c08010203061219060f 71
    0xb040010400045100f540944540d0740090340b41d080c00b0a0520451003900e0004811581d4002504900c000082c08284000c2c2202c2c02400c80382c2d074906034600340780d104d0380104100201001c1c0c0d490f0580506684407000310740030070004615100044000d1514040039000d030101c0e08145507400c1003048890511074110a055444022142403607661080b150b80404010040341144d00302013400300e000b100c1c8500c0d4840e1040c11a820088402c40e0030051401080c10403000c1d070000510b0352010700545000c0e54600c0300200d05141000aa00e1765808084c2040740142c03613004007004506e42c0b1501207030070f07166907180c00d50840400c0d00c07500000e800303180c0246600c40d2a000c2d00289009034070341601d04195080c2c036a07150700840303040266103503c101042404000360184c4911442c0d8441d82810301d0b000074240e204060780846807030304080e0b0496904441c0044c3c1d400001e2002c0c5140c010400c00925103050010700204109015a48643ca0b0505004142c980c44060040145d80c241d0405c44071015003d0a = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 210325548 1250 210324298 210324311
    0x20607080a020f160501091506060503150d02090a0501090e0309030703060e0a060e0a061805060a0519240807210804030812061e0d0b040618030507020109060e031f0e01 74
    0x402d03500070020007100300e800b800c249070008d440490368050750003100d0305074650380e003165500d54111020300d015070301040e4044400d0380e01500503641c002404c2d0150070300c0c010016080d81814282c1040f02c1c119050b103070442d40140811103d42d9000180001940d50101003c110700a01c071f9503091070320042581c010081c81c240718990454a40002d545c51170103006000500c54604031a20400b000a000c00c1e014025400050004480500f190401a00f005591401d11031010714040708200f154a401d1203001061030041c200241c08070a81c2d40180646509000340c080207107011590b811400344002c000007016a81d480041c10310413648141c40c01150020040d0396220040d1382c184100b20310844e62184129000b01004988852030340d0910b400304005480c11215040c1616010b5408078014000c81e5115110315040c0032420300f08640d10b061510949980b40c6031503440c030024240b2a50343d01f0040c2001080715005040d50350016004219140c24152004001d0720a2400c030b01030654801790000c19030800341e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 210326798 1250 210325548 210325553
    0x106150804050d031a0d020a0506040305010203060a0509070207090509030d020309210c070303081b12040b0601030b010c0f06141005030708060f0f0903130b0d0b01020607080a020f16 80
    0x30403500c518400c0080d50a2000d81c001d00b501103503900c01040d040d80300e0344200c845070342c10680c0c5508078050004010514042e0b41d0740018000364426007044a81c1c0e5004014007525040c040707042405040101d81264042c60030391002556032074107114200b0b0303003a114400b0039034101c02841210064002c003002035517285000800155501403201d14154100f240a807448141c000d40030170707990300c0400c04029041152541d1400c4804590190894001c5072030b00142d2034410345420000c0071849000c5601d0044c0d841d1500b00b003020304000900c010306042c1070008010705a80d000b540c00313444991044815100200c1c504280c0c0c001c3c6908912607030b05030b10520502c030081800320511400c444003102181d03040d41e100c0c246070351a42c900352120300206800002007044103545068041d844496802200c1c1800d004ca5040640307040c0d980e104280140c030001306d84a000300b15006030b0700d07403007404c0c0000d0046007800903000340316100051a500500d03901054401615007140304840f4904000709041ca101e881d1030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 210328048 1250 210326798 210326807
    0xf0d030324240906050d020408010c03150e0105130e0a0606230d08030a0e100c0302030f060405130308070c021203030702010c140405010e040209040218030f031218010615 75
    0x90080141d2014001400440030760250000c0140b103090707a43d203000a80c64180c09903071640008281420994080c0404528a8404d1144003481e0341c040d5004550100c0250b010b41c0584165040300440103555801804691035003100019040b43d158030018030441e840d01086c3c2064011a8000c0000303080048c0010146402d100302c80e00c0d25025900b640c060740d01c102c2040110506000d00070300303401e01440002c0358a0b145a0002004460b4103058940b000900c201b002d0851344003200740800b280e40031050041d412000302c0010b51001c0155801c101909040c0a260906a0340c40d0f0020200700c1140002054144035102d00d4a0481c0d02500304041e0340c0c3d02d10031481e16500308455040c010761904100005a520840580c0941c8810034941c902e40f0f41058011141d0b5107540c1101178006400f002035400b80d0f219880200001000450091030340d12401040506102c3c0005036040103600600020b001074014000c5282c10040c0c80d00c2e400512143d440c07001c0d0140a4960000d210309516001d0081d0b415080f = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 210329298 1250 210328048 210328121
    0x105040c030902031507020a020603010f060305130201020a060906060803040b2701320c0604020f030609030405010518040504030f081e0103060f1506090603050c07020f0d0303 77
    0x899040c8500300003000c044045a10203038000e54164002d02c2002d440116401c88541c021704a071058a42c01080f64010840c81c1d032083e403050f0b1407200602c41c00c01030940d041c401c15400100290030258030800c03540000b9680c0290301000f9080a0b503c08400040101e81c5c1d20a20080050301c0590380ca540c0d80c0c403000009500480e18842c0c00911404008650880600b980c12a0381016140c0004800c14120b2100303003910400c550040064541c00b2440702081094050440c0110b104002d02a62425105000c440c100e1401100e0023039200b02c09102c0c0100c03022095800740ca03400c0c0b0301592036070410f8050a940d03c1e01c842529800a01d010203100c14503a0044043c11155620380f0741c04116250b03160581c0310f8600c1c41c6882c40d4081615401800064016085032806400b00e030310219041c607511100a00803000c0da4003c03404610300c0c2c403080246d190103028641c0c1c45100114228101032a54010036a51040c0d420200e21a00040402504041c0264410f80d00744036840c4642000e144021840b0b03810640 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 210330548 1250 210329298 210329309
    0x2e030201080606120118020706061401200c2b0b010e010b0307080c181908010e0303060a05060c21072d060c0309080712110703120c06020d0e0601 64
    0x1c18400201c90382410001c8455140030030035845216071a05042c03005800d005040c0d02da00c1070b02000948041003181c002c1e00040d05060031a8500700e820880003600c0c42c003646640116100d074414907140b00d1480403c2e408044c03a408c0d603450044024504284489180030100021961020144042800001d4155034142d8400c0104200716907207138240000c4502023101d00b40002808080014004055200034043c8040003508190548809030b0018080c50042000320050551203102009080e400f4000c508103080040c0145103941041c2001c030300004070340d01445004400008009001490801c0000f1200d2540c261280350f040d80a0460b00345036202e1319040e500c200e802c2c0c2c0d6103040e104280c00c0580b0159030907040301207030030070700c0e0b9034000078209140c2010149170352075030300c80c01107a820707001481d2035132150350700d40c102907602203001d8241c4400452040e0f542c0d0084c034084c00040c4c00d108410002c0d003c6400d1210000401c6d00e04000a8407030340114124141c100f90b20b0714020b120004d801c505849 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 210331798 1250 210330548 210330557
    0x602010b030f0304120c0504050a200702011b140f060601031a01020604170d1d0f0606060406030906020f04030f02030c01052a0a0f03050a030c09030f08032e030201 72
    0xd00d00420955100c40c880c500d00304030b40041108010101c01c0140c4416040d02c1401140d03d9140c0d03d90006045842c01c6980740390141c0ca826a4410340801d56041400c00211610490704011140d00028003d804074142210350094a144e0070741032260142980c0d0030f0400f072100f101c0300300d032508031001d860b40c10964006022900384034a5500b41c1503100f001450708941a4001d006a07510340c1c076a0b211080281111034001e080c01c1142d58a4030440d070141044808043c0350903481380c4407040c0098945041040001c04541261b800e1101d556180c400321000c440702c030300d800304014070380b410440300034400c00b941401c242d200010004100300d80081e16000060085054070a0032141c0001900e8a02c68100c0300c42d01000f4000604d100c079040a14606014003400c02180c408141503038885000035200f1a050f4041000851a0307803100d60b01d4042c07401010320320710f41a0031451456079002514007c107600103103980404000103900c80000002117042c0010b030a82e96004e10b0b00005034100c0c0000b180800d90005 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 210333048 1250 210331798 210331811
    0x3070f0305150c030a090c0312052805030705250b070f0206010503030d0c020703170c101b03050603010e0d0809070801230c070c0306021215010c03181e060201 70
    0x150342d2166080d20a8503020075080c42c50703540e0315516000b04510700040307a11210307189010001c503c1003c8040c800303100e191241aa0344c00c2c5840d140101505591000c825a011803514265580d03024050b41d80080c002e040450300c44c20303100b5042100001035006101038001040b10074060045901c141030003800e5a868080080d1200542282c07140d01c00d00a039501544200044001c40e0781ca68016418188103106445002d40c0b01c0d510034a80c0721084140403002c800200e03a44141c03200a024401c1c10f2440600100448414a1820305000180e0039002080c15034800c002590343c3c4083d0400300d9100c801d18203036000319510311400381c20b0240948483c8402e100e04040410406814820182c9222381c10b1001a809088201141320104004001c041041024040f54000911015298024500c074181c09600c0708003c004d01c5002c18001040380c4814071008484007074698100610030103058046ca4000003400079054041c0c0c0507452030b4030540c0494a04403603403c00c00b01d038030698000d4408a90091009 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 210334298 1250 210333048 210333073
    0x506040203070c02010806030a0b09160b041203120e0d020a0b06180a0510080303010b070b0703090818060f0708090a0b07171303020604030f0501060605180402030a0b03070f0305 78
    0x407404120307003410206442c101d00c00c000d58042e40c880e540c0050000c0840e980c0120760380c0c1714002c4080a50384029940d003c03503555401594002101000303481e20000640c00c00b4641440003080d070000500107020302002d1080c10010bd442c0d5040750160030006411907a445d80c000c90025900d4020890640b503605035080440e29514181503021100c2e8003105141c0b50685841703490340014000034107030118030394000d00005075110051000e11f00800f2060001034035810281801c054000300203141d102018540580000003851050076190080d03854454402200c0086003c240140f240c1044000c0020022641c0c0c0200070700031005104008080d44c41d50038496a4207443c031864080c0c414001c5c00740305a02e064840240c4d502014207005849140610181e5a9a802040082c0d000c3d4109454081018a0100502c403090003450014080c51400500d0150750350309294064038604826446a50008082046030520b5040054001801429210342d41d50302c9049501068861000300c1d603601038000d100d5071 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 210335548 1250 210334298 210334301
    0x70309110d03260106020a0303020f09030a0f050709150603020a0c050601090b1903110607110604030c0e071110090809040f0903111b010e010c0f060501182702060403060e10050604 79
    0x101d5840b50014611f0401c030b40e03420350107500112080036124009006c004070b595410044028960700401040c80c40340654181142400d0481d0440b184250030480d4004600c07000300011030445009290040e16070414103030031101400500405000d81c41a0340010900d107d20758840340000c0702c03c6443d400c80941c0c0c0343c1c803080c181200c3e100103001c03100c0425100507141040d00060000034440c2c00b654882e81184000183c141d00503400c1070b81c00d00c440c50320031722400003486da11981000c2c02e4103160f604005030342d00c2c40d60340d101c00c02c2e01c00c9015a120a804003c02030303810140c4041c01e20050090068140c2685040000d00d94184160005001e410700c1d2000100007203038100380031145545000e01e00c0d4800006403414212800c40a04102c041070210022a42414440c52174601c80c0c640401c0a5140c85105135040b8810300320f840200c1c2c0b42c0588071510100401e00c2510300700300030000c1c42e03102f140c6000154950244d940054901810003045407418400441d040c2c0c03e43c50038040801c025100c1d10280310 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 210336798 1250 210335548 210335551
    0xc15040203030702060313080a02010903090519090221090a060b010f0c0b072c010311040501020a061d03040603060e0705040806040204050903161109010501031103070309110d0326 79
    0x1c0d0940c208000000242c1002030055074050141044152282c101d944c4001c42640000d00141c0182d5407114480300b00340d030003e0404000c02c401c0750042d285220f007118030100d6105900ca181880e036800240d640549052844100700303200e074100c018000e0b1400c854141c0d01d50450080c225100c5103800c0032103d9541c06503180e1a0002a00c8d80c0b5803844202554a50784080000f504000921204c0c1c166803080d1030550b0080c0340510403103111031000c6040e10001506840d444005004040d00900c414031546e6400516122010b0700004081000060b084450588440013249030020740400900401d005425402c14000c90f0084490703800e00766120b001c111103038080ca01400755260000000319015103040d03001180c010b80b4100603a440c000030507485a1500030251400c0750244041400b8000c54a0800d07501801441e003803c062101e1000c0701d030440210301c002801101890b66031000b59040c42100e100c0b0100688014042e214811114207010f0010890122165040700c0c4e0724440030418250016074a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 210338048 1250 210336798 210336803
    0x1208090c0d03090504050912030414031207030f0b030f0a020d02190605133c09050907060207090c020303130f06020703050405130c02030d0b010e04020d0534110a0605070201020c1504 80
    0x10f0071612b075540d800c541c41c52a9141d400c5c091006204886805615141190003925240c80c00584140302c28406000c0d50124524280300303400034142c0f821040c0002c942c440f02558103c80c5440701c0801c900c0041c5114040b01090440341d4600d51021a0854204005040c0c0303600c00c40d08405055900ca941210080042414000700c0402d036044803426141c1440c4903c5240a44090100302c640b11143c840c02c9030011500e0710031940c803102d010041c0030307014441c1c60301500400b801409112b1044202a50364840a09400342801e064119081844a0600d2024000f40d00c20b01c2590354800a0800030960303042800740390b2041040c000907903034182c141c0c0300340c500d214180d8000c1c5040808011140e4010528400d01c54140315a483c09201d1341d0740c0c1c1c0c0c40203140309102da460006407801c240720407542c3c2d404412034681c48051605e60070320701007649000c0d502044031549400351030010107240311070814181c00b1000706a01d0401c42070082c0c0b9034041d00900703044400c0800310307100c00d2206051380c5417588096801 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 210339298 1250 210338048 210338083
    0x515130302060a1523030105040507051003020f180a080a0620070512030601090504110309010b1e0609060d0e07151d15120c090f0d1208090c0d030905040509 69
    0x4014060245c0c680741d04040403070700855a100341000c0440d080d210102c40031101508055400d03c140e1400c42003880c952880d5203000c43c200342842c20100c2040c451034172100340040000900c0e00450351115484000b401c0107205841c60001c452030810040c194851034120070210780883d441c1c40c924500c0649544581160003444c0f4815285c80d03d001561000c0c0240341000796000c0049103a0310380f03001d0032046c009e20110546c1c0d40e00e04603140908641607010080d00c02d8180050501250200484400c01c1c180201c49090392000220001000f502c10103a10018150410004030070484010849901300c850481d417010450142e010100d814400e81c000700440c0744845000d0031028103050794603061203a44101c089182945140c40c1040e4040100c07110300e8090000207400089051100200344868826501c454000c8101d50740c0c00c01c10f20038481c00d4003c10142c000000d0140d48200512004000041c105804020842c20000c00031559801514051400c02d0702243c8070241c002510340e0110700e402d11 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 210340548 1250 210339298 210339341
    0x10f0c080f15030d050d060501090b0f16061d0f0c300102040b130803040315050411060d09110907081605040f0b21010308160515130302060a 62
    0x1958a0110042c0404400d149248685030072070f1070801030181d265a040d20340ca501d802c54074034035005640e100d411090401c80d000c2c4041101e40c18502c15901d060801c808415154040404294051440e034000503000d1420010601440c107008616507040d82410800da400851041c0c114641d20300700342c0900c1d60440c04900300003000f181c9440c01a1000c04032070b101854000109040c640c00c1e07070030503009130b482c000000641c040d412404020030802010010082c6092620710b40f146141143ca0f00000410a600c46000404100039000000a0083c000300b805888080c800c981500030300c40f8400032104c08071480c00d5041c10b8580304401d54840c502541d603042d0b0590341d24114881030048160404140942803001213890701718080c0d100c0141079070444407030311034910005040a0400304440785d10603031401030060010612400807602504041b4580c801040c04a00d4100e1401c0c402a40078010300144500b80021000080c00300c8030720034001e038225801c80e00c1e4450b4403000c84900341f0062028441d00750 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 210341798 1250 210340548 210340561
    0x6121104050409050a060f06170f030f180a0303020f1e03030105011112070b10170d030b06070b040c0501230909040305070515090d0f08040204090606081e010f0c08 72
    0x1000746154a00c908180c41c00800c4555070030060360089000f85815070788038034049c001c900202d820519541d0061700200088400207402940324030134400c41031240320001414100c8615400b5482000d2100a8401c0007119501c0c00c1c02901d440e5030520604050060100094000b44143e060740c1842d030703444c0040c503c5c40c1d00e480c0041d20b4909210044880c00e0084452000b0041001030107008418054003681c011881c0483c462141c501e643d412125110642c08840340c2c114000040c110079401580c01e0016034480c4200c001000d50140160080c01034030b00f10100030820098061303110480f03000303032519190000b403c14003501c04003054640350303811842441006c84600c0c00d124080d401900a08200345098590340314181059000901e01e14200080d2040c01030342d182c07c0180a00e036120710301c0c00c0b002c40b07000300200402c03000000c0c0c4043e01c16600c1b242d100d41840f69580c4414024010f040850301d682d5400c42218594140814202d4000c0d460310b103440000011a020b52000075060360f40b0600a541c401 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 210343048 1250 210341798 210341801
    0xa020c090907120c031203093908030c0c01050a0c030c03090512010b01021002182202031003030f03050c04090504051c030f1b020a0821040804061211040504 69
    0x20405500c1d031040c0c0000041164a400c46445814041c51000c1c55850a50800400d9055100e6240d01014a001c46400c04201c1c103140307005004100d4036070391600540742d0030111000392010b07148103c4160391b54400120040008010140042408181c441043d0048010340301401820344140116024506490020b84110080c0c14001d100382000c49406803140e011070101c1c0340ca6028103480369550700d01c00c2460368040003412940b808180d015032070074071003110b16201c0098010038140104424140540003d1009010160b40b2840d600c04640320b01d002c40190620061a21040d401300300100c22140019200b801103500c100002d022992800b0714291100c1c0040c040140241d0b014001caa4062a80c000c13a03111001450840341d4003c41c039107a0205007041110f0b03803010411145000416042800b54000c5801030559402062450b200d0480e2040300010b00c015120380300c52030060504110400000001400648003103648401c5c08000301207081044030290f11140d00000340c00d01040225240a = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 210344298 1250 210343048 210343051
    0x10605030c100207210c03031718030f071103010905060601090b03040c0e040809030a060209040b040605031c0507050616080f070c110103060b0d05041202121602041112160201020a020c09 82
    0x4001070720f5001c85e50711500341e60341141d08100e0000d151841d00090380e207a16804a504000902d401801211402c4070803a83ca120b0004003010000e4042202802e0240702800710000b410042c000f0312034022107140290f2903107000c0319190301050001801050070040301040d05d2086900103040c4002e6030511500700c07404100200120303443c0c601004286070360740701401681b04072480f510003d41c44502580412013a50b4011407140d0050386803017800c001d561350014503402800c070500d400308080c09c142c0508550a200d00700d07007e05584150b105000030307115034038074922800519076a021a42d0f1980c00346e2034100507080d1011750001c0c00d100c00100c045402804003480c440710504000441640d10791420b000c40e006005d0010445a641003080140130742e088083d030041403d0300c0076008105602c03c00e0348440c02042450804199060640d004540391580034200c800070b00f001c4a03848072502c0b4004034803003000311313102c2920000142c603000340755005000303030744e4146040c0c1c028002c404c03010010b10046600 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 210345548 1250 210344298 210344339
    0x20a09120b1b1c0e0105130803010b070303060b040b0301090506060403030c030809100e010506130203091528020705010e0705060f0c0709180525031401090204020a02010605030c100207 81
    0x2c0401881d03d8485050200d9800d02141600220384803101d18901821500020302c0c1d03000c090b101e2000440000d1902e002c0381d066400285000340c0322207860804400605141e04022241100003c01041192441c03000c3c6048800380c41050059039201c0c004d001207800313988402804101c1c00c1c800710b07001a000c1e05c0c000e603001c2000401c880c102d840a0082c0310030303100c0401c402d1100c0d95443c8207011450810140c3d007101600712130015807841c10b00030909941c502d048800d072190ac80400c40820742802e441960391070b0204645400301d05604940b5601e00c005d501c00074003110158601580400d500b00c0101e405011920010131150400400c800a40b259610400840c00d0a011f542004a082c0713010f440307808103080e054091401c058070589002ea02d8410b0307000e00703000e440303410207082d070b03080c021850050003030b203030301c079001e50012010000c40d9800760403203a50096001d400480c00e01e042070390560140c0c040380c2c0102c04461480e940103090020b611002000c80b40181c1200c24140b04646816100148400 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 210346798 1250 210345548 210345601
    0x7050f0a0e0f1c0b010e1509040602120708150405012601060806010b070c080f030406030c0215040318120206030406050702070b04060801060807020c0d02040b22020a09120b 76
    0x4101da000600074080c3c42c00701d181420441d4828410b100d82e028105000d000c120300380140600300044410002816076203402e11502d09440040c08100e0550143c1e2101d030304500c01141d00b800c10300d001401c042e600319840a03d6200c14800c80b542c6140c1405003d04881c00c0b03403850341d10b000751007140c1041c034100f200318503480790340305c0d8000a04810b04221145c001c0458902040d1500c0003482d012420180c240d0041e85268006d051424005001004840031038080c0c1c10001800a00880e0a0303081ca1030303003511040d0305003151080006054209000a0f1581614000384c0d00240e112034010155a80050000e50055000c1c40021b000031000d5002d02d401101c18011200c1040e56404000c805521a40007200022005001041025040201c550304003102d4009820f0002901c004548080240e000c06071059450f00800382003620341d60400141c1e0400300c103c0c0d4403482074003000400a507000c005960b000a030469000210310512020000c02690300c540d4034141c0340c0320752a4004180c80313022004480038 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 210348048 1250 210346798 210346819
    0x171303080c130b0c01141f0b09010c080d0b01030e0a0c03110d020306010303020f10060e1618060309020a0e04020109121514070305010b19031d0102040308030a0507050f0a0e 76
    0xf41100050404240180e00120303031000300440301c040412002c2d19404140c242e03040d02c0c0b50b00744036040104041d41c1c00b148046e51100483c50049a250182d0040600404030010341180c0c001e410f42c102070315205003070304c0a000d400c526003071250f500d000c20700780070b0305840d030781201071000a998801c0d031550702c040227000000006036500000d09041003070f40214050b074000141075900080500c40b18210010a038000c025407480d051600f0382c3c1450081c600803400300070540d081541e600070030860801c103101c42c1c01050340b40c1c0c881d14060010305609030182d00c42c1745104400100c0240301301c41c4511440d81a910210030034502002c00140401005044800a581d240d00004010031446020b180700705005924195003071001000c2c04950040c0c2080540710000c1200c2c040030a060000c0403031041c04d0b4a000182c0c1030494011400c140c1514600d0071840d4000100001480082ca010314001c10f40c0302c8040020f6100c0440a83d40c40c4a0540180c010400600c80300364044d010b0554003107900009070411040 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 210349298 1250 210348048 210348059
    0xd05130c0b2a0c100206180307030e0f18150909120f0c01020c0a200a0e0c0a11060115110106080c0f0d0212010204140409050303010e06011806171303080c13 69
    0x242c0c04404c00801644000c0810501e040546c0140354a000d203030000c0c1d80b034524113850041481000a819038001e58100c91012029140e4440c000040c202001500445007099510b80849090141740c01e40324580801c082031144902103981c550120501303c0c4146425141d142008580d00041c0781606c82c3d540c24020009040c3c418440d00741401e01c100240c5072070702e0350903505003083c088c0340741d9850140100306824050260000086504651410080b580360300107010704696406405d0b20350308507070190200004d292071995602050700d04660b2501d80341d66841580301d6003207a80d04c0c411586c440d802464280354904100420840c0e42c0e4024100b402170340f26a40100f481c00704d0a00c41040c1aa40c001010031a2101003a55114080c01c1290103100f410082e0b241c4517500c0c001809490707130846001c3c000c12603030380c003d0360404110070442c3d054650260b0347e228003400b15810041c1041c0c46010082c0010328440c0610420001d21b645900c500340f0a888002d901380c1d281c1c0040d82e10005482d10180003041 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 210350548 1250 210349298 210349309
    0x1009150e13020426030307020604020f0312040801020a17090d030504030509040c0c0b0606040b04090f0b0d0303020a02150124030b0a2c0603030307030b01050d05130c0b2a0c 76
    0x18056884d1004640540042d10507030b100303401c1d41e040003d90414800d11450750b0340880c08681241d01101c2c56403c500c000f03000a401c0002040303080d50392000000f0001030880c1e064019080c40c090546660921100406024007580c0d4115030340445900001b00100095000f544440e800134000e24140e82007090040c08201210801405000800c0484029404111028040d154016415038071141810324001120805000b81c0c0204e00f045c6445078044c0c01c0502081d032050080d64401000d00f9880c211500f0b0140096225040700030050240c29001000e010314817105c1d41c12502c0e46107983c0c4103c5003d90a02545030700400c03241040580300e04802d140351f912403002001a044030701081c500c4a010b940c0ea005d801c0803c034020610603029000700081c079500032060f60b070b01004074200880c80034485001202c04d03118004003001421314010500007000c2d002c003494003646102c0c1d07400320388580d15500310040303c0c0600301985190401444550202405a082410b018250102142c8034890920000741 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 210351798 1250 210350548 210350557
    0x1090c050421020a0609150c1401060b040801140105090601050a0201060503071d0a050405120d200a030509011104151205040b0603250506280e1009150e1302 69
    0x900c5040020900b019840c11070040001030045007080c4c440d03649008481c681c9010310506c001c0c28810000a03150601450a0290900300380306d000030080d00b511109402c0a94101d4040c101d001c0d0b03c0c24031060a010040d98449060340c100400040780780d640e03480115019070103a400a011552200c80005094908010110150221103541d6007181c0792000210950791009000c0814282842c0a00000c10404030700000c0100c071544000d95100c050214010240c04d5840341d400305407484c04c43c40215030f079100c0050405d86160360341c207019640f50107042c9170990b9640c6120340c8260500f080704110202450a00400390209402c054842c540100f842c0f40403110202c82c199a00d40c0910304000c2c07503190501c04111a0a90514a44612844a403124041840301e019090142c0710000d440611062601e5180c55100c00090030004902c0c1484001840f002070060410702071100c140c0c9026a80780100b00b17000a40c0c0c400d200b401880080b00504440b1203203058080b036000a611014041018120700090 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 210353048 1250 210351798 210351839
    0x111e070c2402060c2a03070606090e0d080606030726010302010e10080115090b0c0f070f030b0f070c0519110103090305031803091e0906030a030801090c0504 69
    0x2203000301820218a01d918191080700300b150004001c0000c0c564002d0103888074a041405007448000600d20034036980f178070030310020440e4403001c510340080148903000807042e07404011040c0802c400304d5900d665250111907400d0085030b1040f0005505040c403002540e4041014982040100040c284201c112401e4030300884040710000c0060041d560402c1000e08074400989104500060b40300e0001c10320031040c003a03144291030f8441c43c44c0714a441045800090710181141580e01c14401e103c4a580b040031050408040c01054000641c81300d46184070400c880c2c0100c2c1000c42070743d4410b80590103c3d0028291000e00c0030905096001c1801000f044000d03d10410380112890310505204c01d20180040780b075410035041c10f0840c000a40e00c48140ca420607000072020708401901c0e41118118040c407a4456080f25446981e40340d2004281846510001d0a443c100c205844132400e142c1c0305c109030140500814820030040100c1400c5911920881602d450044d0034103172280481c181600595140c1c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 210354298 1250 210353048 210353069
    0x6090a09170f0415050405010203030f090a29011406070213200a03050a02090609010e01020f010e0c0a05120312040602040b03130b07020d080c0f040f090e070603111e070c 75
    0x103000d00e00f005042c0000f0702e500b5040c21760a2624150000750740344030040c0301c60005004000400c0c2111802c006022445a100140c1c0440902c1420b1807030b007200102c0d02c504000a03c002c0001605640900c80f6450301001038540343c40c0c00e81075002c0c8003241407109426a1020b0b40c40c1c100c1c0c200e1419030b01c0001c2c5801108040f81e99251007902000f070075144040c1c0b542640398410400607500e9552081105c1c4c0240c0700b801c01c0d0442c3c14071080141d007801402219401e1035420210b402021000c04a200c2c40310000032554031101649441c184440280c18240300c00141c0d2040002e10003140501101c1a4054860b000151400c0d80302d104850146c0c00660b016024169111258000c1020310b407501940891541300502d04043c085100501034000a82980b40e07900c00014a100515018002c85000e403880a004d1001c055803044600d00034001001c4404043c094528003046092007802841038510341000da040c1403d02d110301035148c4ca03090100004000e001048001d000900e51440100100183c040c03 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 210355548 1250 210354298 210354307
    0x201020a090807060905040e0118051e0606031b060403150212010b090d0b070507080318120a020616030b0d150e01090206041511060c1c020306090a09170f 68
    0xe018058034016006115990440c100521400d540140904219a42180c1c00318500d008958464010580030b02c040a805014442c09410305c0000200c03010488500503900159012240440381c48000507238805038140c10100034018111103190203e550342900501682c80e0582d2560b0360111041941d14803a651600801c0d20426403400c00201401850440300c4249051904000104081c880c0d9000800a0074040301003070b40148100c080c4e9080c00e5108101d40c0c0e503800c0c001c5150f000d04a00c00140b8a56200700709081c8802c04c03d80041d1901034000350000c041a444101001d40d550b14050113541c00c040e070717030f81a0320500e40d12201d103248298001c803500038814644085080985403030303420441c0c4680c140b40e401d40050311444d00f10381c01c1310401300c815690805155422241d542507100b101d021445a501400138440200b0b00a0940c44600300014100e01600d0801e01e080c1c0c0000c480b229407056021001074990103040d0841d0300304503c58100515450403815441800340c1110510b01c451120102c0c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 210356798 1250 210355548 210355567
    0xe030301030302061e040302030a030507030b131d0f07090c2309190f090207060f0603080301090f20030711011a0307080304030f080f1603120507080403080c0f1603020102 75
    0x890700507022841d250034174480d00d060707200a503691282c1d114034800c0695500026003180c0c8a81c3c481240180d00034407034104041c46020312009001c0400d03070f407455101e1600101c0702240340011981882c80149015119003840c0c0400d1000420f81074125138140318800d40660310401780080168130850035100e550742c96040d048280040d0040d1140c1602400e000400c0900418440e61f46c0441101d4601d2009641c40c80c82c5d18000d00a030500469441c1003d0404030003001f004048000340d4142c549103402000340900851070001540d030400100410f0300f01002c94894000400401564488843e04290400c0100302c1c00040c216004640100c00300785a17030b904a0b40c140380c09c1c81894003c140481c001c600309425500c032050b0481750359070000d00320000020720784c170628104000c0d42d0011001a901079031150707a41c200a0a107200c00d6a25103900380c0f401c0b0000781d02602400940d8041ea42650720505242d603100d142042e0b940c0b142d03641104103882071100c014840300803003480391010310036030005d43c9a08101 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 210358048 1250 210356798 210356821
    0x301060f0e210304030c0303081b18040903021e161a090607020a0e101d070207050906030f0f0705090f090a0201230a0c0b090304050102060f06040e03030103030206 72
    0x9800450400c020515105202e40c0c84030355506251081c030b00e00b41d010048916a5929600c1541e0006100700101d81c000030505400129a07445103a20f0307001c03100c60001d1842c480f03465200c0d510342c030542403504c0d0800603403074205a44805166442401111501c1080541071b00e8014072075004405d4036804603a80c3c820315403820008100600b0307800714004003191081c041e407050303001d1105454012840030a402065541e0300c01510010144c006904a250a01301052040601140034464055070120780c94011503001e411103074820603583c4d020344100c60130101001000c400245c05151b040c86402003d030020481070041041007070300200140500d504d00700501c035041c80010005001d20f491601003003542030001c0b40c0055015824609009143c6000c081d007950324541c4003180381124004601c5074040c54001d1030411080d805001020226540d001946641388190b000d0710740140c01010103c0d103c9190508143d42140c00108042104804095030710710f1a0000da10650041e400700c000c2c000628002d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 210359298 1250 210358048 210358067
    0x60305010b0411090409110a0b0c072103032d05041209030507060e030a0c08030c0709020406140705070815071106061005180603010603020c060901230a021608030106 73
    0x42e1820310800400420a1900c1e006420142d80900d0325000c08904001300709001e42e0b45003200800c942c207a10f440312080345658020403100225807189560100da05101140c0c2440c500d000c0076101c245800480d5000c4001d8010301c038502046801c4003058902060000c0340c986100c2040d400001040e1030b02d070030070343c21801d0065100030500c030318201d003170000c41c0001c909075081d0b0358107041c9001c0740204040480d1602a002001038415801c60001150b1464040300400030060341d20221038043e0340300c15040e803ca10840c8542e90103c2c0003805c00d01d04107002035014140040c018425102c400d951044101d0400c110848000810b80200040001d2150000c010304107000e031002c010710319403420358041407050f48150b103458203002c0d020407000d4800c0040c41032961180e40260046449582d18800a00039422050303240c5800d009110005003121014807408102c5c89040125000580c82a0648d502070440986184a15502081042040980d580c20308001600c5525036680c2c2e07614200e401000c0e03041 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 210360548 1250 210359298 210359321
    0xc0309050708010b0f0f090f04031b0f020321031b04080d0905090a061a0c010e011515053c030114090f0f2716030606050604060c030309020a05120106030501 69
    0x4048103004100c1d12141d007503230382c07010705644501140d448608040c0d1380c030070726864540c64031074002881c541040032102d403000f800c43c4260100e80680304007451801120484440e5803c2d040c4061000494014072184d0040982d0010f59885107070540b10010f16042c4002203000350082411540200841c0c180f45444c143d2001c5107039410000982400249200d40740a400704482c1c4500210780c00005682c2903101d10720200c501b6008000c1c070300405102608105180c030a408086503a04105040c180c011401c42c0c90340305007050038072407010211654200e0300d42c20818180089d4041d0011000c60640f240c011400b070300d80400002500e1540c0c90800c040748a0080c40b44002c085104148242a5600c1201a80140c5224111030403c1c00400c40c4425036160380103688104d1040002d1240365084200b03803102030742d00031541401059191403e1003524880e030b20549000408680c80c01000c28800c1d07002d480384070b100400c0c141c8120741d0f5000192840325a00c0c03a21609075910107041007004000d10880d900030301c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 210361798 1250 210360548 210360559
    0x708010c090f0b0f0904140709030311070e06060310030804120c06050c03120a2306040b040b06220b0c1e010b0607061107050a03080f0112020907030c0309050708010b0f 74
    0x3403c045410400703024100e10400844008110a85203030b0705d6410940009038040350b00030707031803500303260003808141c040c0300c181c0128a1802034058140c6010408005807010100071003402e44442085c80601d0340000d2440c1c03034503040c4003070100020380441c000b00010150008041048e449a04100c075440c40594001e40234400204000e54005101000f038680711a405500708149645622003440900640070001d00c0d00f48410ba03000740401c403e84590360052030295402c1001891000600044468607403056078040400c0c492074604a0034100f40004500a02c5018484a6600c90f810791a40c0c0110210740341e590420f02a10b0100c91008131414800c0041c000288903c14000c000710702c0314803960001901c4961650403c0701c00401400407900400da00004440848115040c010300c0c1e4a0240c80c0702c5944660350700000b811210b18a0010869a0000e0041305161a806800d074001c00c07403404c2460a2540360001e25001c12818042d0000030300c0c1103000030403800c2566040001300100041154441c1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 210363048 1250 210361798 210361829
    0xe0106140a120c0905040f090b1e060d051501060c02010f02010c050301181b0c1401090b0a0f0b030708030c16030c094101080307020108070f110708010c09 68
    0x9540040d103400041e030b041c4000240f03030728001c10443d15200503400035074025040c07040e6060301c40510740c440d401480c06940003600d80d480d00c0585035601d1080c1420300b4041e00c290404101e031440c0640800320b40c54410401c9601c0e031440003000b41c0c0049001d911074004113401803119019541c110085001d90f41072880200040c841c40c3c0005080c500040c040e01d400050320791134104c11b5204a5001c0c40381150003111401900c2c101c400d0060610003183e408590341c106c030040340d00300c0303440500031203512a5200801e102d550f50703800380c000001c00d0340b00c030218001c68940072684c3c0b03242c0307040c0200d40140855101843c0e8a000c008901490180300c015422041e00c070300c00080012400c1c48440100b076030490031000c19440a00c1c131103d40c41c01c0014100d200c104040d1203a1034004452019a000007004010b2001641d0b070341e400003a1b40702d008025000c2e02181114000400151090241031041c0302d1070301f00b00f180203481c9502e0303e241042d02d820840160b07564040903042c43d0b8200c030381c61004003880801410407 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 210364298 1250 210363048 210363067
    0x6090604021005270a0b0c0a0c0b0a0903061515020607080601020a11101106010b1908040206070f03050f0c030301080106050904120f02010f020c06040b0a020f09011211040e010614 79
    0x3180c640c0d4660480d4040354000b88205a48040008001b00b14410440f40c5800304041c0441d201c100d50042150130702c000c040f002442454580a8420521854840100c007a25540310200a05110310141003028100075002c03d400758031910030100d00c640d40d8000c06c1146480c060240014101078506419903001c51042400110b500c4000e01a101054503448410420341d41c0c2566115101510302c0c04500500001240d102c1d4100090a2625250418989500e06070700e030554000e802070707401941041c8100002c00c04502405c1c0544480c82c4240780070340c50304c4404203130702566401c40c050702d1075180c00c000010060032009000304c8029100407904000345052079034401c0800e11014030028180f0201c0400e44640a00039030181300ca81c0c207001e04c20740d80d039122000d040382c60b000300311000c441101c1d0380d50108040c900b842c401d5851507404a00070300c1c503200c00350006680006162543c0b200103500d44010601c201e0108000e007000f003280e50909a03840d41011005031005040300062100e6a00c280802200d = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 210365548 1250 210364298 210364327
    0x170a050603030702010e130608030705100501060504150c0803010605090406053106030b0f01330c0203010f060806010317030c09010e030c220b01031109012006090604021005 76
    0x71030984c242098490000c0c540040780341c1da40340c0c084000d00c0c0c500d0110f00185001f400300003800042c2c46801075810311388401301480d08599081c004c0303e001540c140401c2c40710080752012828901c4d00c5003000c11300322445a0714002c06500c242c001c4c40c001480070401c0c0f4040d00746805900050302e07040b80c03401d0b0528400a5903038401c0e07001a620401c07101e02c0f4056a00d5884c3d45030301c10800795401100b0b0075410715000c0c4060300085028880d01a140139644016444034035444039200740c84a040d4414003030121828011102011f8080c0144d17230556940003041200d481ca44034880040080c500904510340c0f45084c50140b03402041200b00340f54108008024100703111000712a0f00e034000342031010070b48003140003081c6850b500b81142d54001341c1d6140050007080d00310031a902a54205441804807910a900440503a10344c903902c0e21312640d05110200b05036018100b4410380200c1d2400700300a80712400701c50380c81d1850594541045420a001b44015410910a041007041c40ca04040e440d010308410b6140 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 210366798 1250 210365548 210365557
    0x2060306060304020604080f0c01080604091203020c0c0913050c01020304030c2c0a0605120f030d2a0f0f03050103020d060509010b03070609050910080d080601050712170a05060303 79
    0x20712031040000050b085541d5002a600500080e204998648110304001550380543e582041d0202e0038110016000345030078051141050b9015008881442180703405802941010190100c0390103000b40c030711026210543d100c0e120b48250102004071a43c1ca040150a0612030102c250441d0810001803000c503d5510075003046500d02026907401e0380c0300b120321002d6540c0b888200c0030040350b2079040c031090010304e401050540b50102c4154a001c0d031030070f401580d0380d8044000c0b01d815030003d214080e004159071344601c00c1d0384d6504100b101c5582d10940d130f1250b0030707c01020410100b514401c0421030703191f0101400c00e246005090421295046800141e240f100d400e20051059841c2c500003a814503080d08a0741500c2000340440c0c07015503c0301d80142c04840c0f103006450048468400090310910103000d45401c03612242d02a06111135500403c54a600c030040c40369041c02420040000006e9181d1f000d580e801c05259110003002482c241d4460555130003a1000c03d082c0e051006100155034044100d4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 210368048 1250 210366798 210366811
    0xe09030a0915020304230316140405090106080604150c050a0504090e0a021c2a120302030418020a030b1f050d0e060103030302030412020a050715020a051e010608010207020603 77
    0x40e004000b10000807440c501c2a80c112031200007010040e5800b80000c40c490103201e0200b1819100a0a0054030314005101907200b040340062410000c0034003420b0951006401c00c0c000f00000c02c1e00e40d1110039951811200f0303a03046078160000700401d036840b10f0510400301d04c1340d414038040e85040484203000707159000f140504d20026039202c0f0440c261000030091b601c11154082e0081e0b540c040c0b440004240341c6040380c0c0507104002d56851885415003c0c1413001e0302908440d01031880a0f0501250110b00c01400304202c1c290b200402c0b0100c0c4082d94000c000304000202d840142c0c2d5207003201c10007402c2c2e4042c05010780c09103c903800c0c07210401a00c4200c1552036201c03483c056440c2e40940749203001601c4050038042c2d0502400300040141941600190300c2180110142004010756a42c120b0ba516103001c0c003e40340e40c1003400c042c09061690000ac814007161441210b90b60204e43d1030300c900308035200407845481c16034201c5406d00e01e0700a008100042c0b42e00d10086052200c150082500ca00c8018030b030 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 210369298 1250 210368048 210368069
    0x6080a1505040506012313290d1b0b18040c11060c0901120e0a050d0c0803221416080d020c04020307030e0a0503040311100e011808160e09030a09 64
    0x201e1b458a00b5602a4240d4900c0007803503000c81403a01c081003802011080394403060740104854008035004000360b02045040044d02c441e90111082e200d452a204580352020840b46400600042a6400c840a0201c4001ea0030260b0000d0300f030541040111342d0705100c26000d101c0414105000018007061071503000d60a0540d46a88000010040f91050b261415010140b480c00450104000c400241c0c00b064a1146d0105c0c1c1150780e0b4150107850f02510540001e050b8801000000c03081c000b8104e8808404000203080a10310035580e44004840304000f80c01803e560106091800503601080440024010140a00040c5003503240017521107001c181c080d03000700c0d0000003251102d0720030382c04140805042020745141d41e0851902948a40c0036102c182c8255854042030795051500310001c000c262507684131212421440e4006407484c0c03860403e140308980024400045041d401c2c0001c6001d40b10b902151160a41040c1c030f5181c3c588000ba114841c5d0307038018405046a41c0d04202048262100d199a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 210370548 1250 210369298 210369329
    0x308040b150a080a0b010b071e020d060204170705010305100608040f052a01030606080a051017030903010e0f0c01120f1104080d02010e2104050406080a150504050601 73
    0x10303110450030101501503041100500000f421642c01304602003503510400035004540d0b6900340015860003010800b5000580040810950307442031800d100d440c620182c61283c07601020b0300c480003207070015441842a0302d142034080301e2000742805140041c160034281003040741850b81306810000b0f018041c00003030142904c0402c05024100715855003503039114044816102c1d80d81c04020354001c0030661002c000700d900c54000345c0da40c0a13000b404140c854683d1090481e546e4498000f0141038054030005480106203800700310340301000304400580c82d00000540e51004c40000303060031250718000c101c025070881c1c00d49156141001c21090242642440c11318000068101c0d06070051802c0c072808040d00e442d100106207104180720240c01155050016203128142c00e1006a080c1c400310000521240c20400c42000307084036001040c164450855078007410184c841c40031904445c415001032116600c4140402c0c104000c40916440c15501c0b80d40600550a10795030701c680da2541030090241704085c405 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 210371798 1250 210370548 210370561
    0x504090201030e030a031d0708060a0b0d0609080c0705040213050d0317090a02010801050414191d010609051317070206161a010b0901120c03020405091e130308040b 72
    0x300f10310001884042035a0792802c420101074000d200440800c00c20f4490310120012496000c80c01400301c90141014003519a56405502c00a280d0b030b09403180c0c0202d11b04891004030b40c1034440d140c2881d1292401d2540ea40b54108083d151810700c1d402544914010048022003c01068412084032401e81e2100c51240035803900707845455020512000c42480c5008012401e080004c0048809000782c8a13400140d88034030901003aaa12145c0c094200602403000c22254800e00c46d04000004000c2d90014040032a03240700c0400d40b114000c2a20ba580d100d44080c0b14140c0103118542c0c00c1214411076544460043c5d498400c03181c2e05124540b41c054010800c6015074031040f00721101d1540c0d15081c203021460b10f1500c1460000003004155040602400100b000c5070361604448400320142c483c0380c540c5002034000c40c050700070300e9070003010541c003800002030549480ba03806025403034002c15548015503041c0458103800000b844071041c0510100e00e0f1010a0704200320981040d009201d00801c0c0e0b8400 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 210373048 1250 210371798 210371801
    0x11030109020d0f0b070e090f060109082d0c0a0e100302060d021b010e0a1b090524100e04050a0615050c0c0901030203031c0b06040311012601050409020103 68
    0x340c0c010350401c160680c00c0c003c000c0552049410980b00e00c13004525a20b41131030460300317040403e00458101081c82c02052444910240c0c09512080525004d036606480e02c03561410300e5444061070040e5080c075240c140c1c51211814612440406400c0141800f00e204030010301c200743c5030b101b00380e40c0038520030200d43c80d0041d0006a1000d103070094071140e554407402030a040254005401036449500b080c038400c1a000060281500500b03e4800030282140180c40f50740c08000003941100c01c00d00310840006907083c40f405441c0c4150640561800040c201c0c0040c000e05003801c01805120300c80005401c0c00c05500460380054281d02500c0010783d03603030342070409401001550094444000025020000f265101c1c00422404240350242c0700c007003020005200b0004001c0c00001c0d8107401c140b10441603024819105000d140070140c000c2650508030012a4180c2e0094006503124610144104001d5800100301294214039a118401e481c1d031641c040c01000b541030003a2881182c5950b105801c0d07a10a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 210374298 1250 210373048 210373061
    0x1b0a140a0b0f0d0219081509070311090301050403030c2303010608040620090a081c05030c040e090a0b0919020f04090204050a020702090c0412031b120c0506060d0f110301 75
    0xc0004551300d294024920b0011842e081401c40090701ca0300010381f06504048000001c5080904480c225032122503040c0d000c0c042c8116800034003070040c0407502e5599401d026013400350340a918001001310340e8260051a0311032aa00e644040c40004420f80520102c51040302c2c1101e19a20f087c0019841c3c525001015142e1016100210040150010010951000100b01185046401070f0b107240e501e1041d2510380900c00c8030540c0010f032203000e900314280110029503000b040104201d10b03090301c4000003004510241c0b143c9406521000304a0300304003450901c10780256044005214400088040354660340b451710000340102c42096840c1c1c1261940d030040c806081d0f0042c010700880c94150300c048025004040c0c00d911031907400d008a070042400e20112402d0b50002811407420b1f0901c2c1e101a40c1c006035420a4000b402c0106e500b24010801c1000010b24003a1250345007010090181801403401c44040c01d03151160501c840700748000364544101d0b1180320b912400e05030400e80d000d030011303004051 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 210375548 1250 210374298 210374317
    0x305040305030c1510080604020409020406050a09090303050601050304110d030519050316030905070303111509010e060603160909080c0f0d09090b09010b0d0b031b0a140a0b0f 77
    0x404515079210f40780201e5484c0340f007401c00d520302485903200c1008082c98004c5200d00b5400b0742001c1c0204016003804c1c0c1080d82024000741012454a90302e9001c03a981c0102c6500c04030606584004100815038180601c40c1c002c00309203841030442c1070940310364141403103000d900d40c8210703400000c090406000d5003e9a00707009400d03610003046500000c007c0d000307a208480844d01e01d007050842c030718000d0080c410384a1032a001801044000c0c203590f4140c1d0f840d15120035810280c0700f0302c08400c00310b41d0f0303600200c1d103d81c00c404004a5142c0d0310229042c0f078070710301403d42e83c400d03040020750b41d10344d984c0d682a1804681018001141d80c4519080c040c1c8107206860041320342c0d015103400780006040004a201c0c0c0b50403240d44500545964424000440340c10302d5000d0380c0040e12000400c0304091903009480c40c020380c1200003420a182c40002441c05007140301c05089000d100410349032528001d900d00c002031800c0080154400c40440005080305403501504400d240081255088a0020401d0b5100c820 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 210376798 1250 210375548 210375553
    0x40302100f140406110f06090607081503060c07060b0906030615040e0115080d03020c0304060c0303180320010218091f0902130b07020114030901181b050105030f040308040305040305 80
    0xd0711350b00010b0460300d6555800c034441c8580b001000c803c000000701c0e503204901c41c0014107883e8854000c00c480b0b8103405070103103508040f50710303500e4640c0c1d80501060b4041c40311100d085a44104600d0044103403040f07000e40074480e0011500308041c1d070300c02150007075000202041e6110001000350029004059540320000b41d9031070907020800000c219001c09083d180e0b81811a0f9442e010f07203508406078071a03078a018010b0740090000f0001c02c1e0092222030b1345188a400c001c2508000e80e5460700444080c13030400d40024062000b446c109010440c51510341001d118000d42c90441d0308807214401c42149045103008201e94000920031803c80303c004040406140c000c038400d5a695070144002e5041000c1100c02401e103498005200c1500d01c04445203694107844030040406840c60030203240d00000c003568925501d80c0406031552002140c0ca05002e4418048808901c4a003800842800160340004e41032110800c10700041d100e0b1724000d607521550614000c05203503550318045a00f07000300d500003049031 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 210378048 1250 210376798 210376807
    0xe010311030408031806040c0605030a060b030f070e06070b0f0c1308010f0b040507230d0e100606030203040314090f120f010e210309011d070305060705040302100f14 73
    0x901c86000f180610036400b082c0391010081c1076095186c02c81920001d04101640c003003002528010b1000d90341c0207088440c002040e9640e01001c10080d4821035030410f20300d29000410100ca83c01031081500e01d48207541150426085076030f514140e13540070702400e5507c1780c40c00004207204628070484141c0c1d095010310001c500d5607455807070301a1683e0b00908610b1410942d903654113050510503544a4079141d84c92000c5141c04580f881c940c03010954180310241820441146400c0305401000e5402c1081d10003400c1d580d0107a10f41208454440d0812030801d4010414407001c02e030302c80e000c0c0400a010020383c646c1c820a600014000c9010703410301e01d8100d290000e030401e125401080140c0000242c40080c40001020034409884401082c030b4a891094042c1408011491110240d07a02100d80800041c3d1034585c5400c00c60028400c80c02c48000c1d03880000c080c020030006001180d0000309034209542880c1c00c4d5800142480c0121118a0030404d031b41c521110340e640f240850186080d084081c0c950746c0d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 210379298 1250 210378048 210378053
    0x230618160b0c0c040c120b030613020d140106080c0a14061902010207170309100c1d0f031020090d1101120e0102041a030906180a08180906030309100e0103110304 71
    0x20720b850640c1b24800d0914094841000d401c022548601c07601c1d024029805000f919420051018814081950500b0406814455401d400d1041401510001d0003c0020710003417001c0121005003038020a1001d0300b042c054021307640321603060f902c10103210b294103441503100c540224028002c560000e841442c042101040d07100303031080114096070011050740e00d5030445030748190581d5115001d4000080c1c120181c0c1100d10030350f086500e942c000c000c0602500d410844006841c0241c1e8022402a00d95980035842d036903184120809601034460b807105003000040d00000e4000901500302400c200bc08103810701d40e41c0c2c031416010745075071441e407010040113046e081c405000b0341190044000200c491600c1003880d070b030a001074078031608440004060950318811001d8040d542c860700c2c0075040c400e40301400001011310014080b4070102c09081e0105046103c10000806005010030740a500f08108003082c544131090208103030301c4942000c04804a002004a0003007a002400d00ca1480c40441400308 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 210380548 1250 210379298 210379307
    0x408120703050117010213050108130f0809031608071e08162306030a090201030b060d0b0103060e010e1f05040c17010b0c030301030f230618160b0c0c040c 68
    0x50304c8003204080080d07880c04031094201c2c410740030250721484d03c3c10001c108d40d61046041660000304156a515221480d076115440e240f10031100316590200420340420304d0a080040006070001403c031000841d24043c1c14945231640c0d0b0155020104200c0780040820803142e9202c001481904111203140200e0f82d0000640c0880b4042c1c2031000b00c0c11b10345001104408403142c0030011000b84042c1c9107440350710a800c002c04581c00d00324107158960381400718642e11400a0300e2555101100401e040c00200001411135005403c207a510010480042c4001d03000059407552100300018001e220401c20000641502520fa000da0b520a00700141e035130b509503000c0d00e003144560040b45400720603600c46544800500440034040c155034405d200410100c3c1c034400c00784070030502401c40303031007049920072000300764628072030160f03856500440600200074a400a09500b0428100251441103140c0c01d0311a60030b4a43d00c640b201c00080819902070168003802103030782000c0024800c001d0418800000740 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 210381798 1250 210380548 210380551
    0xb19020712031101050a0b0a0501180306020406050408370302010b15040f0b0a0e010f0309020918060f071d060f0409060e220201080c0714010e011d0c09040812070305 73
    0x3c159401c100c0803882110440c0240300c940d01008111800c140d040100441e001e0341c0300d0307000d2005c2c03410110f40040410042c0c402040541403503600d5541d03550418100b246803c001c0c100b040e03610740c40d022004032840c07091603a40138005200b0414061b840c10b507040c02c9000d040d0544156911500070b0103001e0192207113200030310440b02852908403110343d4030b585002840c001c00304a0f401140d0010304014041d0f00c01c070441080c1e80c0700307410b00080704074641d0046554076000721011105a240c0c0989010b11810411003580e11003c4994000c0c51494802d0000700b0f031081071102001c030050846c0100c9400d40c3e800c01036521a504c00441380d03403559a07400000010300000d10030f58520000d4403001c80c05000702142c440301d02c4c820300324499500d13010b01e134011920401d0040100300c0da190184610360024000c680750042104080c40013042202c0d1414140d800c40d07031084410303c0107041041d0340c0c14560001040e0020030711411108912907a0355810025014411500300c140890312030000c00001d6a007680c040e5 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 210383048 1250 210381798 210381827
    0x5030702101401050d03050c0106080304030b06060703120b03010b040e0102090a0b03010b070809010327120e0a03020f060f032a07150903050f040305010f0e0303010b1902071203 78
    0x321154291005400d085502070a02e0141101004005101c50304040307a420042c81d10926003d0310740414003ca003800c54130590404005608001002c00130f0156204020b6004503040311254075181c1650740180201402d8062402480d8a07000600c40b181c0d820341c003410702da02d0054028000b0700018802a4003d5200165140c402c01004c0404110320000605882c1600c44007140140b40070240c0e21001c1407070700020070150405881d401d01a0317414007000c40c1e841310040d5051172000e2106851508000d071003c0380b400ba00400520181902807655038055007011243c050310800808101c183c081203051040c1801180400d1000040c00400c00069440f5101050101744280a0070450007945030b10b8800c0d4100508002e07901c602086060001d64000d0310341c98442d0400500e0207605c420100b125402030f9006aa0f030365952801e44040c81042e0146010080c421005145190b041c11b422050b1800f48600c0c20104c095102ca0101c0007500030440140503206440400010450702d2a00600c6000c00c13800d107 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 210384298 1250 210383048 210383053
    0x190c0306050708011d040c0b07030c0302010c030c0c02190314150a1a09060f0a060306051302070302031204030c0602040b0306040f1b0507061e051b09010806150c01060605030702 78
    0x40d071024451044141a40c40c641d0415081c25130b1704c60022070411026000b03548205251034002003800c40d00e0010503509100f5140c01600ea000307818041d00311429911000d0034182404840c880791a0301c8a5034101c0540c9c11110900c01c41c034120400c101c49c8425800003450031004940740c0810600010b0201502d9100e00b461070919550b8022820a030741c42d0040940c890103080c0c403008018500700c05d09540c404d4014080541210b0000b002a0901e102a442000400d50b40c0d401440ba508142c403506254021400007985804066607000b5500e01c2054401c2444d4603000c0b002c5400c0500c1285c0c544512504068103648540e00e5030010140b551083c0c0b4268411031900c0d05121100d0341e280214144141001140500c4038081541a54154000310040324002d65444001ba040342555282204002c2c0c120000180b600d0003412018000b00d05489018420109100d088004daa00081040c0d0025040d90542d8011512030540502400b8a41c2d900d2090350030170b00c01043c1e0703590000140d4891020b6508 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 210385548 1250 210384298 210384301
    0x40501092906030406020703051204030909061706010e0c040306060b131e05040b03010f09060603030f0507050c0402070f02031005040605060a050108060402250308190515010e03190c030605 83
    0x15072803480400850107a0040c0c000e000090218060307501828080e4040e0070480c0c5840d900c0505442c500c003044408402041e000382e003d0243c030701617114240140400701d0404202002c0080850360390f900500c9003c021840441c0001c10945004059500445d4050014082e841d141c500c60400c0790094a06002c10740e0601c0400138908400d0403940104031082200040000c1c10039050101400c0b8000309c2d503416640703503140307400b5000c1c01d48112401039001311000540e160452070014020a501d4600c40e0401005001920100d4400710348985001e070308070707401640c50b503591400540f001c0c00800d0182d418029152008088481c54006078861480385104006643d50702c820000c0f000c085000d03660004070700b400000e60f1414030b80d0042c08041404540c0c58031188903003220050791005035204600007140c1c0c0051055070301454828045c0c49400303aa050041d031504810281002502840305130400400310980d1880da20107004108403106a48101d441c625128107207904829040d00c021500d440c9440e0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 210386798 1250 210385548 210385601
    0x120313030e0f01170606130e1603110a03090c09090b0907080d021009060204050402030903120702032503031e020406090f052103040506070f020f010801050303030c0a090504050109 79
    0x11828101058480b1060250000c8000c21a0100240020b0701b0003420400031640503d8040c080b40100420190381d1007a2030100c401840e0010540c0c1010241401c003140e0a40800001d0161000e401c55880c00250142950800315201c0005520003481c251400201300184000030342c24620421011045541c420350f80c241c4103554034840e86000005801112601455007010741105550038050400035090076140c4000a00300e030f106a40103503c69000092006290141010540d400041800a141030650261104c03107030440400d00d0000500e2540758203002c0501a501c480f01c1a0750504800d1150030310500104000c0d4858000c05000c100840d20000380c0340040c810031320070f940000c2c4c1451401680800e0b0460907403021803185c3c40c240002d000c00302e030780c1d00d9078000b070500d8500500c0f00c14040f580d54010700c07082c0b10311000e940c0e0401041800502a54600004890304244088901aa40c40e811303502190352486a80003203502c60b051000001e016100307070f004032000f05040342d0150301520201 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 210388048 1250 210386798 210386809
    0xe1026151b0a05040801060b0a1b0b04020108040602071b080f014505070302271f0509250816030f06080d110d050c060606070203120313030e 62
    0x1154070041c0611500140001542a40d000d400c282e070b0b850800a040940301daa46900303448254200c4005d4000100f1800c1ca6590308c000035800e0080801c18203882c0c000b103900e40c1c6801900040c0b010f414002034502140400480d0350485903520f804c12008107a1480c1c01601541e5200144200040381c420004094503a5806202e404000d43d542a00c00c1340014500070081002c1c07048054600510418200542c4021940c107100508980704030050700116003544104902c0340c000c821105034034050400b0000280c2c0e180c00121742c100841c0e0408406005c03144000e001c60040941007140c00007103034028029261300c000d4240003140c1c503601022440080801e42168004022034404050052429003425928080d60003110102c00c2a40c0100b492908c814001c0d2800d403001c084580050840e01400110b0b42d010321000d43c2401c070524241d450064510b0742190b40f4007000e84058892540001c800e02155420440901c4411004c00c4050301c9241083c941a900c0c110004294080307440b04400c650f4900d000c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 210389298 1250 210388048 210388051
    0x10b0616020d03020a020a080f062503050c041205060a050f040c0b0903010204030c0e18030c150c0909010303020604061505010903151d010903021b06040e102615 71
    0x800203a003000c05141e001c200071440d07032400641c1035004410706100583c40b0f140c424006040081c1c01815040c000074605450004002c0032038092a2084408410106000003d00054103075442c0101e002d4a60441d072501078400e59010709040010044c1d40f03410080301160581c40748483c1c240420117a5510740b181205010100c8008110880b80da90a001c0c0100e02c0c00a062184c1000d0001400e15840795a4810001d020b90041021968030600700208400c2c040a0001e24007400300242d42000300303000a6580d16090007101500714606080001c0403c001081682c1e40c0b17610040c40014076503500d040203500d80303c0a03038050b1541c0382031903201d80d400410701c03034020700f260010b81d0398008040c0f840d00c0f41d119040701d000305144d03019110b141d8100102c0740400880d000704486000017a85000e9494040c1c5000c164002203000540b45076000c44403039403204161002c4489282255000780e851000703044944031306400084c44040000f1014400c000c8a03051501000400c5048a400b1080b0780144606101e0 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 210390548 1250 210389298 210389317
    0x170c012607050a02010b031902090a09110f1504090204030221031605011b050d0e070e040206161b090f1a01050a030e070b0a1e1b020f060d050603010b06 67
    0x401068925200b0300c0104800c08040c4000901c01b401007000a0401c01000305000a5480c0c1d484080c00f0741c9070038018207400085910040011000b60707616020f80e02c3c0b942c1c0700d04c0d124101015140b0459183c1020180c1c403460031051060b41d0340e0312216054000c1d001404103038000e00d21351145400a8648200c55101c084201e00150b0803c2c2148280f024208524082141c40e552242034085401c00011100581140640c130340ca500d031345003085c12408a82000e003a04d04198800541000100094400d0b41d421a4040d1190b40c5e8a4042410a005650318034000900310b03980288e2540c6445103024442e81540c2030580d0602000c0450340d1100147c940c00c210010700442101c40f090f0007580200001c00044005040101b4062090b5401d1800c1108903406250b00d4100003980b0340345194007061005c0e0700e8007004211080200785d40300007040d0325244206804100100710030b410640da907901d0100400d0320002c08031592072021602c07000140c841034460601940c02c1416180c46803400d08140d900050 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 210391798 1250 210390548 210390617
    0x509070e01030b040206090d030918090c0b0708071401020c0c0409051f0f0606020105091903080a0c1e0302070b070201180b040213021201080705010f080a020c07170c01 74
    0x74295180c2c0042110f01400c120392080041020314881d40719903003030700034680c0230751101803100c2d182141c6844c008441042159459141604050000e2001d070000310951300c19031030f4161104d0043c64601801d02c16110040c240701134a000001e547c8030150000c05100d102c16040c0c0380f1564100c3c1c180700c10303540c100d0801400d54005c400502d0f039142164030f500d20300078603200001c10034498140d540c1c42250815004680140d4454040040034041003151070710802c00d555503118041110380300140800009802d00a955490302140501030388202c92810245000b0a5510a40c51103014094000d521002d81100d60925450000d0784150040c401c04c0b510714036501e1501003648890f40c4420700d068000300200d90160310300014010311010b6202501d1004140400901c076941889940d030318000705907106604100450740c107046200c0e030081483c0e40049200c82c0250303c6800141c1c00301e060110390341101815445014250544078000203c8620203c001e8890114946c403480351254071110300e18403d04c507030 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 210393048 1250 210391798 210391801
    0xc0603110405010e04111c050c07050c01050714120403140d050a0302070c0f0e0405070e07120506010e1807031a06090f06040e13060c081e1314010507030509070e 71
    0xb9401044e2407010084014000a880c01c0001410203450b08080e104290b2464442d03500c80c1820b055100302d542080400c40c000d810040555102555408a190755034104440400d40380c08114000304601c00c41c000c60000da411601c0384180c5a940b40c1c10610041c0c900d182800003030341000101040c1907014004547d1518a0308401507402d8001e0352000f4400c64001298000000d0481a64212000901410013020505080909100b03240100d503812074a411b603461000d0000698102c071081c040041c2da01400714140e550600140d0b510443c1101098115811401c645105640000c0b214452821520304000500300d007944601020034103591550452020448004207240c110146201820010305091406407542450505407000741e403214800f0342c030040f001081010700d001301a00c4486524100116143c00300301d8150650444e02c10203c40c140b8880030413182c2d5041c03000030a600e90400c148003100c0c00c100001c00d00070607007103401000103882c040104001c0b8201045000890303080c5010f06803103 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 210394298 1250 210393048 210393059
    0x1a0402150306120f070602010c05040e1315180309060c0c03060908040513020903071d16020c03010e070305010506010e0d0b150a0306150608010f0611010e01060807030c06031104 78
    0x300c0d400540ba06074090500e00100010040c01c01a9040442c4440050804a8035200b0080d080d2399000644506000c4184070902c9460003c03517100b41e0000e01d181d0f003803041c42e8560400e410001c454880003100389041c2019520300c00c0040108800c018443e0b80e4090000c3c0c1e0790203003155107840703004004024812000c8208042071264003e40003246c05485228502540c410010304410351543c01c02111603004641154603260032b2243c07000400e00d410640c0444040c0001c54404050001c0801c0c0128a24a18017a83c181c03080101c644a804050020480c4003181465035559180510044401c0c0d803c140010349694801ca1132036a07a440042e20200c0040015030b120b0500000080040321241031540000075540d943d090007000450040000080807044d003841414110342c40d130000e40030300001d9001049000c0242400208680c42450413005201c12040018003605200f400e09020750f00700748000c10342c030f203020400000b124410384164486554515040d000d640705483d142d1034000003071004204 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 210395548 1250 210394298 210394339
    0x509090c0703110316200d050706020709060f12050f0111070c0b0f071e02030d03090b070201150b0d15270b060d050711060403020c030c0a03020a38071a0402 69
    0xc1140300c6c0484079200d80301100070400052038000c00340c996131301c000410010716405100003030251040c201d00b03101d0035007000000000e88406114144c9802c110703e00f09418448144040e03994444d254009100c4200b800e03105141980016606550803440c00b4000215802c001003141c00d0b00b06003184c1c0c0c5003404400d854402038070750380d080d20035040d00c1c0d0565120010783d17007401203202c0311080f500c0001d01e0201c0f6050200d0b5040004042200f0b5a00d03242000c10394410ba0410b08049070801002c2d01d95640f8010041c902401c0c9403203040e610000480800704140220700c50381e0b50f02c034040c003554155101a01c2218010b443d00e0700710254000000f003214110180f459044664824500d05042848400d050111490014125015070042c3c00c143c0110320145018803030810115400c03203480200b2400c50300040c0c4c4100c202d00c0ba68002d0045061b282d260101c030300c0381054020f881624001d05c403508881c0b080c00c40f903000000848200310030100300d400f88804442031a01a41e00a4002101c00640b9000c2e184c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 210396798 1250 210395548 210395573
    0x1415031603060e120a02240708010509090304050409060c0320070816050a03030e0607090509010902130b07050604020a0e1311130603060b0f0406150f0509090c0703110316 75
    0x143c60082c2100300d04240c00c3c21000b80450391042e8014000c0e668407401d100e81c010b000201391416406072500f44081240d0043c00c20b03040d00d00494428400d0b89030400d5640c0f40d0b20440c1c0c06142c0103424201c14005000c1298040e80c89032855032014019480e5070704024030840301100d80c44038482000d122403000328a50801a244a10104184d500d841d026512642d2900324800f008800203511600d50201ba12014010300e0303005125805c00c1c5444601f0100000c059910500840d0110307a404944011410130503a0300c2c1e03004005030403400b940c6864a052054a42000325030030b901840e910b540c00262841c240096922515202e025101340000d46e41c0ca07040000180d80400f50300c0000c4d06905520aa00c80c8244002103224810000300c54a0348000d120918030039440851185103008010401413000501c1200c03940e549252819020394061029074040c0a0381c0c800070b40120591040081c241d10080052203910700a4903515500c1c54000000e030b0750703403183c1c50781c0c12150014500110000341d0d05110b6035 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 210398048 1250 210396798 210396821
    0x50c15010f061b0c0e10090b030c060d060b0304051606081003020621090309010306050909151e0f07030b040c09060c1401091a0c0a140f0706141503160306 68
    0x28810f1140300c2c0c54060300301d205604144408882c40c0c080c0090040b4404106004080e80c07802482004a01800251200d0300c102d03800b07004400000700480901095804440a8100580c400b40c030390800741041a83c844c240715840c4c42c030441142010a44500405100381300f5006042000c0b40c0505584c04d200036a049034a14900740500c90060951011a4410240c4190101c0c1d0080d52900001d01c001025500c035603010a00030400e039000e119010038040b45240314031192481e4001c1c0d0707849000d0440d0000d019200703005451200744051007004000000c0443c081c0942c1e9400f400500d0b1701c0020030044a00300c903512408606078203420401e0900400704904041c0c060ba90390741c10225203d140c0d60956030440c100301e506101c0070307141240c1c690000c0340c2d09400031041c8142c0d07404c040752928040d100b078851580088595101040650490880d00100c1c1d41035540035501b8040d0116110301b854020009503407007203004070075081031402c0b400c0015111a859800c030000144a81c519200c01d00100010500e1 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 210399298 1250 210398048 210398087
    0x60103052a090108030a1b0c120f0f03050702090c093a060c0f0c0c061409040e0c330d1107050304060e0a05010804140715050c15010f06 60
    0x30304000ba038403241807900810043d0003a40c4d5501685000410f290b07000003001e4114416000d00c08041110350703081d001592031006600b12112200c2c10031407010031010310000d00c4031134824056810141d00c0000303060390301c0c400c0c0c6821850f0707101d61005044a001d088030243c2c00c540412142900031101d030f42d40300380307408034500300c0c03140694150720001910680d410150742c0c1644514060114035404190150358641d1071600d090300d0060f55584141d1000b5074411700d000c00c81c403280300d840510301000440760300c580020400c202450001c4d42441c1c80c0c0c3c0c0070740404c5210f00f642c100080e203411824880900e500461183c0f0085c03c00e400301b001220340d0009102201c0c0682c1c1c0b103030340780042909078008000c66801031b00159116403400c60000d01d44206440c002d80600c991203810000c41c1d07000700000703401592200740c0100500c800e1a695140c9242588130805108032003404901060700710004140300c0d0314200540c1c8150542080a150b8031400307101d480411644804200503440c41000c1313202d2a022030140 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 210400548 1250 210399298 210399373
    0x10e0103180b0412030204050105040311030705180405060f06010e01031d06071805040911040504020409081308160e01030b090708060a050a0b030f0601121a0703020309070806010305 80
    0x10750000520322084111000700c0c1e008140b006000c0390b00d1100c031001c0c081c3d24007945458140000204a802144001003c80ba03203411003410740d6500b4031603007000e03007009404031826280e20300e00c03481038a0b0145c0741980d01d030150401191f01c2d54048074078035100d01411b8484c01c0d0400d00700c400440003041d60826500c1025080c400441f104a4140500341c045c0100d9500d00714049000d6050541c01601e07507206520032443c049030000001c2c0d00e0080454549000c480000c8c4076525400424050049894000d14501c00069903105072410441500251041c1c81d048a9461044801c54240340d40c060180112441c4480010070009110120041e8449112401c0d41c6261703603260000c514001c0140e6200031480c3d00d410400072841d0b1507106500042d1001c07002005e5072040c003e0705544401040c0900710350300250040c030f4414024050702c1802034004a00c2d4089503841e10b01001002908165104000c0303004803d00080caa10b40060024160f0b5000000b4154140004660800107180c8003054a4540c50454 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 210401798 1250 210400548 210400571
    0x72d110d020106030b0717011404090c060305100f0537030b010e07030207030f08060a030203070b0315030604081c09020d0b180106210501020c070609080106050618010e0103 76
    0xa414240e4a50004a800c0382145040920000020519410059032403006148007220701c00181c112400084d14130b10001010010a01520001402901141c4a4100000c0586e17042c1d00a91060600f600c48070003450b101c410b03404040704a03200701c6500c005104200c2e04d91541c1800d13407a11040c886110200c261407140d10400c42d82d805980251401c0700884010400600b4420f00164401840d25045240c403140f030754080c210206085d40b400410000783d00003051034031040181800785400808031903101c1e90729180204168000c5030442d001c3d4000f580c4400719403c002510602a07076101d10b5190400780c16006513944003220a04400c441d603124419100541c4550391803110281c020f400b441001d18090801072898598021040210381c509a4100b050207509150201c081c1030902c6041d80048080c180705019000340310001070a40611700340000c0180d004088034040b251010028850745948004100700e900481102881c00c1000c0080d100343c6610507203848115034014100014590100c2 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 210403048 1250 210401798 210401803
    0x2090123090d0f060606031112070203040f0806180d02060109110702040501080d02011401140f03281101030606050405040905150703090614060f012102031005010305072d11 76
    0x181042e20000343c590007180030b0010a0065601a101e10f00b81480b000c2034000000403a40304555045602e0068100401c41c034078402c0c0100c1e402800c0d8010003081e510745400314a5103820090321076401e034010740c01c0c0d03200c51130030081a020642c0b83b098001c0c00150f86003d01c0385000d40070000c0c20821500c800c10a000059a0f648240f602070402c0380c0061000d00944071010342100c11740d490810015003500010840c0104031942070b00000c3c0f0036140d42e0600144200031903d02500c212070301351400f4410110342c59400100c40d0712200706006481102e09010311800540868131a8060b000024400300701c00c2c007443c14640c1044449074410780c00c5a01c0d104908142d501c00f18416160400065242d400b20310a0100502031064482c3e19141c10920b142403610016005c0711010951905100b01ca80b2464034101c4070714121102000040d04c10742d600d01c0c0c001e43c0c01d08940711030b0150601203440c1c00c002c501042d104200001050351290040b0700103202c004000718079402d401d41c800b810041d480c0245041d40300103 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 210404298 1250 210403048 210403069
    0x111070c0303030b04060b032701020c060403080c04030305030105120309040c03050709080313060804050712080901090617041106070c090929070e12060910060503010209012309 78
    0x3400214812504501c1c0040654100c1c00c1c29512036030504100740900d40c484e000b200e070410003104d0080205158003429038103e40d4080c0745240b0035403000c626001c0119001c04e0140c8100c1c80391b41c810017113a9907188000c1140c06103020180004006000601c038908120094048446141088900707018a21300050f00340c4050040c01c0c4002502c6800344103000e6088080240548243c402450030140c0300414020000d9061180c0c00c20004040041001d100043c4408005007004a8040610050300e0400301ca06074480b654080c006901214005095485400703512000c2c0c042e54800324841d1607c0d04d501403007584a18803a0380c05081001444001452411540003c15404e140420300e80d2560a04804504a1000d003a2000b8070b040000784402041c42005640003102d0704058141b00820382c04074072003524900c0751040911403078017030001c0311600244a0401c07503180801404425101e00915003070323004901445010510752285c1380500005141002544400034040a007000c0e1031500080c020800c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 210405548 1250 210404298 210404303
    0x503040603110f0310090b0a060c17130801020315040e060f09100e0a1709061c2909090f03040324110a11070f031101140d0608150705040611011107 65
    0x80010810003c002030050447c110012070328501d085107020000741c50741e40d04203c02011103060855000401140c0c2c802d48601c202c3c0c8850021505444111f40c81c000d42c030550f03007106c01c140d000e04030032114035090040c02c0c05101208040d15180c0c5078143d50703440c4a00302801305540d80c00f03000000d0b80384001500c565010060380700018800300c2c10307508040244540c6020301a8824404018183e202c1c1c58080072101010805544084c1001c082003c44c0c00500380c0758401c5040c103072100c001c10483c4000100315040c1c50800c45008509071100c9010580d51040b400401c20b15801c240010804181280001004000007038804000f5490481002d4101c4501c00d2200c41c0100010070181041503205040d040c0c05c1d11000010f0903210304000541169406d11320004050100e80e18455040380d228400302c2d503074035121401154030b4044000c81a009007029019000ca584103049481407000180b1964a00503910341e01d41350b1034141802400c41d0340ca01d40107081b036000e40d2079094920b50030300280010306c4481d0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 210406798 1250 210405548 210405571
    0x1b021207050906060a05090904030507050604061a030106050a14030c1504031a071d03010f2d060e07111204030b0403030f0213060503330102060609040503040603110f03 74
    0x1400e003001c00241c0ba80c040c14250080368244428005c482d00700007240d54910b0122080462543e45140c200c0e103d12801c2c0000b030003030043d00248810000907402203000320310340b01050524103012005140c00c89200e44500c0c0e81c4101c46070780c00c004150100c0655041e4a80140c2620b801400180c041610b181c91400142160200080c0410500000300303c44520004212090180c03805c0032040102345070150402c480c1c0d10410201e0107100ca640960068220025000003401030035000116441c40925154605501422205407003034280701d0740c0710348402e854868225080903107401e0710442c1d0241d10a22110824820405504401e41802c0040e2008510425040c8201d1415150080907102540c0407074955600500038403204080402103072091307926a240550322640c0316200100340c1d51240c1801d499084807285100b004011394940f14500320002c0e0201e4903142c6a5409011201008640240058000740000c2c020b15119402a0b9400508030004505008206807034254a40c010703a034011220 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 210408048 1250 210406798 210406813
    0x9050402160c170c030724091508060301110c0a1509050a20010e091311060c03070c1a0715021c0c0e030c0a180204080d020a061a060a1b0212 62
    0x10300401081070944c00980161080901d04601c4050450462a0780c5901581d02c020389001a4803038810040181100c5000e01500030206d007001c0c202d81402e41e141c5002e5401c0030210070400c1d0468045900b0a190080100401006a1198a5143c502650503440d06845041c10000306104100b000a1940501c11010018030f110020046001e0b10081b0981800040c0035284003e41c0e80005450b4400e16000360380c0381000385032420f03100c003900030040795601c014045110307086040e0010141c03d269204180000e46582c0343c51034454054000956150241c808106640015022508550300c600c0d401c0b501606040c8402410342d9000740c3c0840c0c405c9070543e076025081a960303010010b0090310000b40c001e00758400d66000441d8500380d07540140e20004210036444881d28010358120b80c0204080c20944808002d10308000307444058a003001c0d640141130411001d254441e4400058a100c070040500b490494010340075596460344400300d058098040307281c440580c4500c0c032640d03480954003003d00a40c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 210409298 1250 210408048 210408089
    0x70b0f0a0e0d08040803190c09030c08030f19050d0c0e0306070e0f06070201180b0408060f06060a0e04090b010801050105010306090b09060d0f0515070801120309050402160c 76
    0x49070741001880d400740d4442180000c00980052155030800e070001c00701a03499448084900d4580c1120354045506840e01c00f1a03028140d02c07140304001c2d00d1141d458282800c1d92241001e07030307c0c041c5102a01c6259802c20103a1070000307120048206070403035806c0086c100702c4042e55080031a00c096083c203000c0343e0102d048024a00c3c1c180700803980701c0c4503400c100c0708052840c40421011250b80712428040c200010345c0d54196801140d2269481c0d080c800300070400d81c2c031f5a035022402d0304103200c0c40b040d0340300d81008a0303c880f564000c4c4030302c5418043e250600b810914102141c1c00c201c07411400350071660700c14032400410124141c2078040c005140010819501d44000102200e0540e0300c034840142c41e000c809142d070340d946075500ba080303e03003180c10300c40c0c01c6000d052240500480c203500904503c54100c48010039455242403610070700d25601d03484010380e80d40a100080e4804540002c00044000e0380900c020300c0c5c581c4c041c0c100c15400280b8004154075990310b004095249412484058400c42610034a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 210410548 1250 210409298 210409301
    0x301381807031e290301020c0a1103070806040f0303110405030a030e03070f0b0909040201031409010b0117010312140f070303020717190309020105070c0e09060702010c050d11070b0f0a 81
    0x78001200504011091000902e011001013044a0020860140030006442e030303025016140745045007401d45000103024a13050490381c01702d4041c54000e0041250020322000007140643c0302e42e400544001000081daa0120001c010442e49480c00301c2c0706000110b0340341c40407c181102c1c0c41c840c0e140c2101140310f96040524011041d40309401c440c0e682ea0080c0040303032a481c19520801020340341036409850b280700503005050b803054074500c004000c03000c001c1d442d9815041108001c10030b0301ca002d680100d071034108613040c0c000d00001e00030004503030510283d940702d080140d0750124804c0105040c070b0444200c90302c0944c480d83c0c00b42c00294021500805004111001c0da0074051450701c1145000140003410b55403120401d20403090661303400303141c420359005d40f0868098a43c00034024644d19150404501801001c0d00c000c007030b1384100000a800c0e58014030904240d00000c0e01c81d0307410003448501c0a009001d05011106506900b03002e41c0d00058144510140111000e0588086030701e040d951000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 210411798 1250 210410548 210410591
    0xf03080903010e1f0b060c06040c092012090c0307060903030e040606020a02060706110301120311010e33010608070f030c05070b04030e0909010506030138180703 71
    0x1403260440c4600f030181d4035008040300004580c4050100d440a441170018106020b1094031070154002ca100304400c0040410703203034060b100c2d600e00c02c01c21071400070141d162155400c0420159002c040280c45d1510884202c0300f83d201081c2c400311044010054003107410702d0001c1d03201c5004111002024410140c000000b00c00c1e04c2000c0d1420401107140220081d51600a8440a401040c000030a5424003040d500b101e0745007041340b80540d903a965110450380308846801c2c41540082c203001040c184140043c007038190310030111801070809041c16443c071b04020740032a02c0420004140041d4101030010396080301c4c002c01701500c480c0b819140601e00502516442d032065020185011207002c8400c2d007007000d0300c003025085001b500c501d40d15450f0544821140c18903845e070105034841040324280341508014403904007a4028000c1041c4408502124104000384404075800c0d021203c0740100302003c0c640060030024030f03044480b0062105000c9044081c0c603140d0000762100341c08100603502c0301407003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 210413048 1250 210411798 210411821
    0x5160806040515070908011a1f0905090a06090e0304080c010203120103060f02040305010222090e060117120d09110a06050315061b06010e13030c08070203070f0308090301 75
    0x18181881d042e55101d0316142c03d503075402551102040442c41c15803040401002400d0700d4030080000b9a03030409a242c180340d0690025104050303081c205070408191403e2a45041c51030340b1144841410030007040b81e100030040c405510280d407810005081d1202c2e0080303100031090ac8003e135649a0900303e005060800b00154207043d50720401001c0c190714a40e01d01141101c1e00008000340001840c070255020f40300307660000c0e11660010484074445070701098280034600c0203c252200d101c0d56140d01c02e050350666039400010340c00c250010081600383da00c40b00768240c540c0f4146c40e400c041107a8111140e4101038101d0740c0c12603030380e440c2508000c08184903410300c4a08840240d030051401c800145948002040e4022152848403c1451510f4090544415400c03c20698202c100006140342d502d034400d101c0c000d060103c99020400c40c0e03203448030010b039003034040e038900c8005419601c0d054490f038012502280c01d4803400c0c41c002540401c5041580103144540d5541c0d0780c9140180401d400d440389004c01 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 210414298 1250 210413048 210413053
    0x30f0d08010513060503030a080402030c090702010c0f0f0207091a060c0a0b060616060c020f06011502070b040f0303081503030a0e03162306070602030702030406090e070f05090616051608 82
    0x5c2c4080c0c0e030b00000b03075420b40794280380c0440c03035507182c1c03012a0501c0400700740036400c000a20306000a554040d00b0825000e00c1694030040156080c61040780d68403c00500e010141c3c1003488140000e10740c0d0f80111440042040012008100315000b0454640c0043e494200c650407007801041000780e0300c031b0f01e036400c040200d8689040100c17610140003ca035481c0301c02402c40e55607000407141a030003171000380814241c00017a04c007607603520706211100031500b5518000600404101051140c0c1c00d42c20344054907204590140034078150b40d810303660844040c14607503c0c0910100f41c4501550208020000d17800c2503503400c032501c855103041c1803610b8900c5000d4655945524006c0c4502d41e40709800200c060400390180003000c0c0880c000c036910344680c0001810341d500000801c040d1030f0b0000b00810481e44103030345880b046944d80500c040148416101d160010b50340090304041148907102804032400001c0c5030501e0403444140d180c203e0420240c007110741d9080541804094080324031894000c2060801 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 210415548 1250 210414298 210414311
    0x41518120201170603100c1d030601083708041a0903060a020307030e0105040c0501020d020f15060103020d0e010b0f0307030534060809010507030605060306040b030f0d08010513 78
    0x41c00080d1410801c0c00b401181c00c0001d0140c0d03404020384c06c541080c4c07210801c03150400310030040402241c0740005e00c1008512004c42d80740c3c10005040c1b8100c03500e02000d04145070090344070300034003503821201600f1b40c07038400c10380c4581080103462040d89511848403250340e01d2a0003d242c1801d000b4111416140c48280249406901d01040203540411110320060b505ea0398000c080e001000031515840c0c6562802c0204001c0050035100c54090f100c090302290028040080100d82d9000c02c0d04184a03981c02c0414040c0e500103d240002d03800040504003d0306182190200e2003c80f84400d8084a00780e44a48d8001c00508280046500082e001d0b00a40100b0f420764135465030b586225040c00c00118510700c1c40c2000c076218070000403150070123078401d071803d030b9a6854028600c5100740c1d1543d81652034400419001da0080c46448101c030f1780038001e207045a031090100001413502d440c146415009840324180010300510408406030b60700e846070301c000d5041a051080ba503881501881540b894001c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 210416798 1250 210415548 210415553
    0xa031205011512060f08012003160e03031c0b0f010302041202011803240c051e090a03062c01050c1b100204090f0c09180207060204151812 61
    0x10390004884803908104400100c0b01003114028102c0380e01840300c202039103030041001b40041d00005160b01da028283c01814100c0e0442c0a0b56200a9502c19491b203090383c11048014080c2c0b0081c80042801415242000050300740e005d00440d006051400c1035540c3c41c03007020302d0f2030607860140303002600303180440c103160500e031020b6550b801c4120007a0501404020664030b0b1240020034601a6521001a250140c604a807605d1509030a14a000c0c146040944050007544104180c0380c00c80001800c642c804000381c11071102651003c0440d98000c095048040041101c602801d20980c60390070325040c070400d50080d004200388620501100f00e034180f03018403e4448021066440402000140c0d00c006400703159254505004062038071001400071178000f0340d4101641c80100c2c224850390040c04640d10001c0110f40440450051081380f00c132043e401985078259501410b10584111070041c901916519440b041c0e80c0000d0710000090340101c010482d010707002d0100b00080100f0074075000090a2507 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 210418048 1250 210416798 210416819
    0x102160623070e120a0303020304030f0810060c03020c0d0c0807081f020c07030c090501030b010905071403070e0a0b0a03060602030c0a020d020a051009030c12020d020603070e0a06020a03120501 85
    0x82d01d01010804000c00440c120b94413984c488200791094011650000340034a40500a07420466041e40443c001c03002401c207007030042074218410050600e04d40c100508084041d68a03c401300c1e01607007140700d000304104658480c2d10140c080f1902400f83c01921500d030521a03072034507171103812555580d00600f0300d1421002001c88030203a10303250400c015890303180d12141285000c07115172016140c032846541c002010384a07548650b05aa00070011948070342e0b2620347e840f050b50f030b00b81c0d0150b0000c0d82c900c518109604110002d190442d041e0f00e4020300e03035000e00b000540202c1007504000700038100011200708280e05441140000d02c030030300285040201c403d1045441d02c3d40d043c4068001c440e0341290f10119600c144070107025050013080c01000723000b82c1200030150209400100c1d90140d84400c080356020070152603100f8980d0051240c0d250a03066424000d03240c001070401418010700480c0c945050b500d60013800064080e40d80104800c80c01814010800c43d49820007641a074544801404949500c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 210419298 1250 210418048 210418051
    0x703051c05253603060501062d08060a05030a03030f0e0703030206130222051501051c020711090103050607080f060108070809123007200c030102160623 67
    0xc0348942d20322a191102c3c1c0c524502042c41420031004034002008105d91644840e060382c100c0d40e1161610050100c0b422844500c4442440400e46903201c0c40da03500d03204006096009901074042e401007a0780d400481c1c84e01c030007034404501083d140e401c0c29020600701e120f52350107484110001c1c010300d440c0d0745000c2c0d07c071000a07003500d14200c00d1003460f5055440f0341007030480c40e481d0132035640c0c5580d41040c44c1c00000e03c01540c150304950311181c1d80c5142507129030262a04810541e4020398000c0641210300000c1d8400076080700c0c90740e005440c19a250307031041c02c118020b500980c068402441c240e4002030018000400c008a2480e030344060140a9a01c01c441c558002c409060a55441d220b220a0350700c0c0401200c1901e100400c00219034945010f03140b245003a840900400b41c41000c02440f05000880f0221240400951840710485540c0020301550060002004c16903411204110109007039902c03c00c151911511079615050070404203100b102a8401c103082c11041c8040c400c045003059540 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 210420548 1250 210419298 210419327
    0x1b0b0f04031704061d0d05040b0903070506130e010b03010f14030307060501030804090e010e03071e06060308040e06030109050c0103020904060f1e06230703051c0525 73
    0x50040014101409031120a140c000107402d48112458545062800382c6200c2d43d440a401ca5115409007090360005180080070406494460410341031a41e0012130b5000014070580c0b42c1701e0481d0002e0281ca591000300391440329040014482414200502d5240d101039015121520040004014982c0d500c0c0307510b02074034807560140b1000c207940300000b4514000d500028041e98580070001007000030b040010012100d45034010b01c9010201c02800d0301700d44100035600d825400401c0410000303141032200074240d27500c0c0562000888075035110081120341982044a80c44170003d81802070031281d40c07015500c050101d0003801102c43c0c5583c4d154407905034600c1641850b401080590355a81d50380c0280e00a8081d42c403214140765541c01c00c070202c0b10351381700181d0080741c58400082040d5220740450b41541080c02c0850301c0304901c41140040079840128280c007044024806101001d20081080104030816580454242011803060980e81d0040b4502c02c01000030f85040e051280c1c00c031058a18210 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 210421798 1250 210420548 210420571
    0x60c030f030c1e0c060506030a02030a0b0603012c1501030203031b1f0f05160206040f06270b010506130324090b0106030c081e1b191b0b 60
    0x141d41020b5a01d0000082c10f0007850b6250075058030320962146112800d82d00480040c480b6403160f800749038988090860182d055000140c00034013161502324002e4018201034000600301600c2540c4a8868200a40d078250035082c4101c4003002c00000c0000c9034004801c80752000403549507900082c3e5034070803070441e034151039036020000e102040700384991549401c80c1c10305c5070341ca80c051000f56002021a050b9804111380f802c40402e005801412003070000b0541a0010a059110768440c51368011444004542440d200c510104d002031103002e2810902c10b1046c07641c50f0561040c60b11043c0d50205030403d6000d0001804542520640b00100808880d04066a800e0a400c0c2d005030540441d0790701c40d00490396081c02014810444411750490407595140d90400240070201000c5440c0700050701c580740101100b0100100b81c0101507041c0c3d42200310321000400443c009490714090340c10240c0c540303a044480d00c40d44100180c0001c0703142060a540c3c400d002c1d841c0000d070b03203207144040058801c01845 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 210423048 1250 210421798 210421811
    0x1a0105042307030e030a0c15020a02030708070804050312040602100c020309010f02070e070e0a090b060306061b06070305010f050a0b0a05070c031b05011101090209040611090622060c030f03 83
    0x10b5011358804680182c810301502d50320000b901001c1d02199001c04c00b100e000010004440856180b8404d0700d543c2c8501d80d010703510702503c644400140d1b400984054070100402c02000481d643c0402c070602c02c0301804c82079243c5844c03a03c0c6001c4d052802c40105468044e05010041f07880c95808006c4482861007400c01052059000c0800c0303142c41140d40001c0aa00044410f01030017613041b00074810248021034801100540307510255003074400e102c0c4501c1e0807902c1880854040d241031300241c003c0705028115012100000c002c0140303880815540200469a0340c8018000580e00075921409440d0550f982d40b4528540f007410280e40c40b078032020074100003002c600f1104000d0310b010364100071900301303002102e42c207000d44031080c220304d0300c0c400d403404280700a0100764007130b03018060308440307580003806101c06a1304c07600d4130b00c003070301031601c42c0700300b030b0604103c8000e03d50f54500190400700714500e00007a50041040c000c00f1081c156030068414058034084400c00207510240d051081031543c940450b00 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 210424298 1250 210423048 210423061
    0x14010f0b122b020f120301030c0f06170a0f0c0806030714010e190f0602010f0506041817042c07110d030e160308130918060e030c06041a01050423 64
    0x134480000c24a000a00454541002030704590018605880c080c200303810040c3c0d0b0791032202030f10b12010704c52180460000d0202e015a03045441440354404210a00800d80b0005100400216526902d00c440410820028001a03090401c9a41c0103042d802c481e40f01c1a03a40080060080c215590465100d80601549181150381448034080107110382c2c0e4a140c0016110b800190103859001004241d082c5484000350701850180140c50a40407040c12800c4084515104c048031052900300a010300c0b90200000210020301e142c00d1645860a880c65400580100e090300c146010302810130b008020741400f013a4441e4401090440740444982400203440301c0340e41000382003000300b000c4040c00c41690040002803000d190000c1c42000034080324000c6813511980448100c030460302051407480305400348140094110360190610a40120480c3e00b09070711640c4441c0342031412a0708813544002c110041c60103d4040d062103002d84003c0741c062241d0482900c1040351408103100d01c0306803520120101c5d94 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 210425548 1250 210424298 210424303
    0xb18060319090521120a061503020a0c0c0906090b0406030519030207080d08011509150e0622030b07020114160e030a0b09120c0606040914010f0b122b02 67
    0x1414104413922505140d9441c40c4102600665030b0310654003a07541c00611300000e035201d500140c1d004152801408000d00314110000d401c00140301d13040c404d201c4400703000300d40041c3c1c2c1d42d0003c141c011341c045600c0e418035044074240c440d812a100d01403030070b01e002070002590214808001401001c0048245001c5007400ca02d0843c542d44224218000c0c2070700c45021f20ba211660905035600e0f03003d04010200300520444a458080c403a102644400707500c0c2c144000d1290002d240d00d03d03001080c950800142000c03410b8881152558412040507000c2d003001001106c5121a500c10380500081224281c10f8070028100a401069802c4800d2010b88210035940582078101124030050200e60700c14505142c40c03038004005841005c058454025101c511440d404100d0b00149080c0010707045c291501c130180805010385000403104000e04204c0d20300d94800c24428000e02c08a031400c042140703000202880248000f840300d10520340c00a4103251408409034000e41807023540760040f8486045003590490 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 210426798 1250 210425548 210425563
    0xc0d05090d030c0201060b09190b0309030306010e0d05100e0106080f01021e0a08060d0c08030a0e1207030201201207061406090906041113020d0504120203070b010e10050a0b180603190905 82
    0xd202b030302c0100c00c1c8441804000003461107100d003030301e43d60040e1080781c040004010392a41c006080b03611694034281161903a803c211234440300d050001c65503c4e01c40d101e007414940d8050002500d41e501181d002c14411204e10700c100780d0b60882014628045e142c2c0401481000c0040c403440c003030031004108004211481c0c0c091002001002d055036103481581c04010000c2400c5480240f03d005d852030701c4c064415001c64840308480c0c0c1612003003c0d40f0b802042080002c011000660350500544490520040f190070042c03070880d220b00b400141b25214104030366000403002e000300c0d02070104c00b0100030742070f040040c0039074106030005840c00050203108005000504403041c5000854004540341031905001d40149000e20f10801c00c204d00461003401c2283d0340c0c01041805811b03401e08400400100400d101c200780c0000e214802d10071065220781c04600c0c0d00e0110381c0800e81202e00003e10300d418543c2c1c00300140040c0002c48000349141031121488003000290000c0c40ea0030341e03031041c201f400c2180411880 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 210428048 1250 210426798 210426809
    0x3180305300402030609030f0714120c1011040303122013051f080106080c040302040903050c06130507091d0714030f0105070212030c0d05090d030c0201060b0919 71
    0x207404204501c03160901032055a0403406403043e80301092540c1004400c0d200b400c0c044a82203800d00d07800c1d46400c0911b1008000d03000541c01420390440790021070704028180210030800070521841c40501d07080454906070741000c9456814441070000a901501b5444424181c0a01085c4401c40c616180c6103120040254080c07020006036076100300510320009005c5800c11101140c2d5400c00d00c42d0b000d180107440b80e80304005800800140700782030180c0110b640100c400c00c059030405489601060890300e040500303501080000c24903114008080114a40c41141380c05650101000307aa5035543d141a079000d40011640c0341c00c0c050400d106524610a46183e00c00115020b0300c0e40d0390101c041800000c070a0900901405041c0010300005001751402104107078010700110041c07014015013500060304800000100b00000c1001c0201800344900441001020f421700c1c0e82c80940c080c1c1296600300c0084c05590604c1c000b00254000002580c1142c50107899001c000e98003803c525200345801d4009 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 210429298 1250 210428048 210428107
    0x11202070320073210090e0c070605130f2301020d1a06070b06041107050105090f1603080d0c0314091605042702010e1008090105010603180305 63
    0x61079180d000011110100c035200b0010404c101d07220050b1444480c00981d00c080862804030740d0310882c1c10401096600c2e22080d141150005488203031084d03c00c01c00ba141c0405c031000100d0720358140025880f541c0d0300018000407140e095042a96420340003031a03001c0280a40144001807042c0800140340403407029941c038000c65031000302021840081600d91495017082170341c5440310341281801000c903004243c200b80002c0c455a100c4041102410b60034016000141003841a000001c009000e25402901f180000d0408006c030f00c201c0c0b074507100d07200061040070610848204081010441180c0d4403461280c80454101d50300001a0042e0500c010000d0500702d1070001c120fa01d060200d011004940b200684052460703483d02000309482e51281140007075481c00d800048014101400c1c241100d01c10304003480b40009100c00a000e5122a904080108062100f08a01c4890a01c2158050000c81c20204500c0c031f0f42c01060144811001801010310000054183c0c4c000700f1b2001c3c400b480c40b5040c61 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 210430548 1250 210429298 210429347
    0xf09150302092e06180506040323120705060403080603191112061f060e01080a0506040b0310020919030f1b150c1104050108190204090c06031e09020112020703 70
    0x60503102c0c0510f17500c00c820043c0c200030489160682c2124104e9800c00a81264920207844840c640900c28120070745611a20000c0d460000c0500b014111050164019003441e01d040c3c10090b0030390a00402640c402d030043d20450254000c9425100312454000c0d030070118000c007000c0401c10300040851440a80d1140c039041041d1507020071900e140e040c251301d0281981c41d955140581b516064603020038040780707008000890b9845154005640000f004001003507091102010a0420341d180b0741041c1804d4001601c111a81002902d400381c1c02900000f0962075440d40d00c4610100320181d000411420f21096184a050058140c01000d018101c68940101721401006414909400b0085640003104542584180b4103030bc903544c12940c030400680030a059800c0c03842480580260100d074003a64810000c0b01003285d002ca09400b60039551000240f0241ca8662801c05070304540c001c4085900301140040181d9008a81d440900300e40c0e032003d42c4800d168075050341c081040300c0c26100f001c82c0108 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 210431654 1106 210430548 210430559
    0x30305060607020a060914010503010f0e061201020c0105040b060d0b06041d03030a02030406060e042103020d0c0c03090b040b03011203050705070f09150302092e 71
    0x4001502d01026540040c8207022650410000a0107205050082060303d0100e03001901003400d00e64115850450070003031004c0c8a01070f80e5001121034021a807151500c030045030000c8100c41c001d548448118410034003c040c1120107584464401020071a2810414440c1e180d05810001c1030420755610001e020151500141002c200c448540c0011007000051010b14060541c20801590b00e00b000e051a1050301c10359004100b410490724184000030b403030801c0c507211410704641d001c04403580d815070650090107020700c00000c0b41d00f40354120f09120391218640020b248280c845605203901e8040c080c5041c0110b009402d00c18208100610406103c2e064030361042d8464030380381d40f800095640d914103280869108003200e1921140a01042c41c8c41d00a02031207270b400c483c542c242503140d5000201407900c064200003c1c1c502d0f40380010080020803002842c40d4110741e66074814140d552 = true := by decide +kernel

theorem cover : BRFrame.Cov 210251798 210431654 := by
  have h0 := BRFrame.cov_init 210251798
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 210251798 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 210251798 ≤ n) (h2 : n < 210431654) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
