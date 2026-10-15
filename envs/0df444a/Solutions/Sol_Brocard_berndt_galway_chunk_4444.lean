-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4444
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:38:02.68448+00:00
-- url     : https://prove2.me/submissions/1c2d44be-6c07-41e8-9c78-6cb0d3453fb2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 799100719 ≤ n < 799280575 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 799101969 1250 799100719 799100737
    0xa150804060501080a0b2e1502070911070f11030a150b0f03030f03070c0c030311060a02040f0608060f030114071806050315010c060e250b12040302010b09040c06020d0305150402 78
    0x10b130a40404d400207c4a087c041e042200203607051194025919410492140681a540e80c100700221049003007150901ca4070f400108800348510204041c00100641d080801c071002e4203480354114185064902900b021001962642ca4600d112401d41031040241c0c50858015005500d002d8040a0114007608020b0111040110032080d0900150301620000002c5200b9129a40c40002d01d05405042c194000e1410104074418002080240d02c80c80601c0c040301e0a50515001c2c607140c07600898002d806604a281d015030800482d21041c040002001d440341070103949407507a640b184503400d000703804d552184400046051000c24a45802050300c4248013030305061460194103559070309170607902200c0105600d9040030607401e5500a001c44118412400c900b4a065003600b030183c009544c3c019844d9420014510340c0c006410903000b5880f0018084c0002d000007907602e49403820442d401050700508005020359001d00441500a000b05401018002108219595a0700c140710007074101241c5 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 799103219 1250 799101969 799102021
    0x5030a0810270513030e0f06040b0315092d0c16030e270a050417040906031e0b0c2109010506100503130206090a150804060501080a0b 59
    0x800298900070404400c4241c0180020590508951204004685008008180070164035030001c00180e0310105941d900181147c0410900b882c11020401a0141750000c42c860840001800300005039004090f809503400c841c0e0910654603914501940c0d6406042500052940c080655090001889241c0d1045440342c1c1c460500c2c805169400c0843d4110900f0743c00b098901c080da81c03143c18941ca895100300100c020040b0075038848040308002603030007030201c0c02d42c0b5074440105007000200280b000030320318006045a100c5403034000e400300504d80d0748411140248000000c054020040b100c00ca507075500f0002c400c0c500c2d9140d07030380800740c0e1340a60720200440d40440c5c17004903c0801800118092400e030b4000180900d0100203222081601c0c00c000014400181304002d0070242d40721042480d154141c8a1940320890307140414552011b030340000c0c005100c03e039400400198001a818071a5004680c248696684d4803039542d100e41003480c02805500c42640010190401c90703450340140703170500700 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 799104469 1250 799103219 799103251
    0xb0d030e060a0e1801061803020114090303070f150507170703240e010e0108010509100b010201110703030213090b1327050708060109020406080a091a1e1305030a08 72
    0x213011a041401c00d80e0305914140c010b00c085a0310401c002d2900100e01c440d0100b45080d500040c240901c03090b07200c174050b40b001170200d003161414004d0b520210b61000c6844c801100924000341c0f1481344011813004c0518000015000601c41c080c105031101c051036a004007620344460880c060f0400401407031050f944a00780c0081495100041802001d000054059035410018415008641030340299520703814a014810b91001c0410b031241074071103d540c000340340428000140d01401e0103c4140410034030120b0b0020034540c058004084121060629214042e20b40c06448221044900d91a0700180100139082c2c1c40045940b00c1881e080c04c0003480e2400d0701c882b01000c3c0d82d980d603411003102c1940010390308110261080164901400002c1e5084d82001c0c1001c000420f0160001c100400c2c40380c8807042c141c2401001d00a40350f800c7c403070500050691429408108084070b014004c0022566503400280100c540c150708000d0690b48200914607002c00003800f20380c0d03400c0207011000d112a0041c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 799105719 1250 799104469 799104497
    0xe0303030c090904331b050a0f020f0a0b06030f07030804050103020901030902090108031905030121080705010501060e03070609050a0b031012060f0515010c12090f080a02040b0d030e060a 82
    0x46005d0117641543c24002c804104072000c04065500840ca06400201c400c121111125080300654440c034001c1e2034082121041c0c010101d261182d080900c07030741409104002c0007480304e03c02e80c3d58410346007541112000c229044425a64010500c4040d246a0080c0000d001da9842a0001d06200c00145404210080d203500040c440c80c10130f03480b5030402d90001030f584c01d00c04802000b240201c901801c1440c110342c5800004842448502840c0d0500708402e510401000250020740d0070407600480208a20341e107811025040360304040010384130b480342c2a00041d115202e140e268041e41c402038a0306091038500040300b280c13074001800360800b10f80d00d0300d07003c21050500303810070000301d01404000c541200580134074021600f0242410280714a207050815213a41c00822001c8030591141c4414034000c2e03403520485811156810071442044141030000342800700082041e001da008542c2084559686c20400c410b13500304080007400308068001000720740c0340c41005085508294180030318044812 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 799106969 1250 799105719 799105763
    0x250503070e1207050a0b211e0406060602070506042909030607032406170a02160305040317040f0306020919090e0c040c0e0622030507060e0303030c090904 68
    0x20340c1c2d8405258030444003001300c1d1616143d04401808000c401740d1405401038040700130b03140508502c000544811000c0b5995110a403000c034405ea415040310341070b0f030400f03181800c05810140b15440041c403807a0004038491801100316801c0307031440748884c10050107200d2503041800c0080b031100c96840341440f13160316549060000701c2c424600f40d81c0024002003284100290407143d9507003040b0032015043c05010b010f030400c0c59100c40800080036440385980e00500310300070380b00e80b400c40754030003840000403001c2640000180090340e10402502d1441c0000d0b017080e141500072485240014001c1d4202080072800366801042c1d40900a0000c0c00607212000500d0790048640d88041002c0d941c1d072400390011401400652480d9804403018000c60004880042c0020070212460b48150710015206050341a8090aa000c1ca0301031901c072400d85a1342d04000b92943c59510804022410004502c1390310310f0040100c0b48130300d224400c0241018510f505105041000400c22502802c1c002d007010449900 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 799108219 1250 799106969 799106989
    0x50c09030715111204091d01020a050904052202060a0210050c030a0c0f02030919050a09020712030606020712050c090a06051302040302061803191a250503070e 70
    0x1402c6031072071801c182200502c80c00ea5007075500040d4000e81c0c4991440741005003110115920b4281c0480e041c106d852462111300c01404d04000c2030740c40003600201140d04400a030245241c01c130307070802181e0b5504202e00148015401006000140500003000615107640a0300281c0399a204442c2c5003110f4081d9502200c0041c0d07441c1344100804020005010118000c03600340011a1074500c00980d00c110000c0d40d00d00884030454070880030b150508100102c1030034101e0090400405201c1c14a9480c0c010800030343c007058003a10660484209503c03075034001e0041c80d089400d158001c11110f40b5081c2c4252500f203901c00304907400e0040b2004150140d940d480c04138002d0042d104009007103840e1600f0088800d10008255800c0c40c01400200003513074990081d0b03100c9000116154404c5030141000034100045144036140d001c0d00c0310102c1080c00700061511201d10190185845603850700d5140301b0707860350201c0d14490001c04406040c5c01c2c061055029607040030260400740c0b24541300000103480852 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 799109469 1250 799108219 799108229
    0xd0513170a0507031a06060c060712091502070b09030a0903061d1b0a06031a060702150703110c01090806040311010e2b0801051f090f0e0a050a0e0709050c090307 71
    0x1705c0306043e04030301c0c0e002140c0e05800c00021281c40303241140d4042e40a445d82e000401540a1011014003d4010500c68111a5603140e101103541040f040080408009400246084ea00018504001000407100004403a0704c460240c1311070455a00e190f0343c03d009086544c166021804078407010b4001001d08201d066031010580103140c106410100521400b40110703440a000c05007009020507440c888a40ca04170703e02e0301a103034a41d9a0b8014000f00300e2118550040003880000000c9001c24181d02c9000b250100003281d096039220803540c0011103801e00c4074001d00800340c00c24030200e400640220a0300045089020000c00c90003d15094030b400c018030913400c45003108040c00c0444c550090f040c1c14042880d450b0410070302c25410480820101190343c085500552218a00480564000c0e50400020261104c40ca48241c4c2c0750312606111900595071020440c1c240070100e165485c45015055500c11600d009000452611503150050000a005018907440810500e61191818000000944 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 799110719 1250 799109469 799109483
    0x8040303050703020c0103151406070c0e0a06050d0209010e090109121d030a05031c1b091d0103150207060f050a09020a083d09030306080d0513170a050703 68
    0x10540307040203401c190b0303909031003410180740c544511010150f04040c031041c0c500460240031150b003441c0200780f00380310f00e0000cd84401c80040001400d4102d07001e80910402e801e850a10002e5991000c5c84002c4003a040003c3d4485a40300044c8604040c0c07040e041d501072642000441c00718010313254542c40c21404100e040005104819151403c4008014a52840016801801041c1c2c158590689074010310030030348201c980385030422803904000c1d00400e050040d8039180100c0c000d8041d40190054046100d030344000d0610204040824140d184803504807074100384424291012100c84500950007044121003540c2c0c0d07a400d0041e6038003280300d584c1c440c007a00d520001c0c07901410b004000b107207010355000d0f0310340c0d504c5000d10740c151442e075040280140c88141c1921040d0106000425550346040354502c44051030100b0040605500d0740150b001c03214410207883c0b526000c0c100486607071052130013280c0c40540c030003020010744502c031900051000107503052340c9941d106c541e61141004030741c1d44292a20 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 799111969 1250 799110719 799110727
    0x503100b040f0510120e0d17090d03020a0909061202120a0305070807020a03081207080c27030a0c0b030403030b0d0201121e0c0810080c03060a020904090804030305 72
    0x4910200111806410581100350429203456960303089038070705006035801403211401240c2c40c0703030184060f642c071200ca05805010340d01100d1a183d40d951400320b400070004a400b041400002094440107004090000150148108049003900691b00c41c010707103810401200e81c0090004141d00c00c900190100c07001c940c858030700740c2c01005100e540448604046802c464441c0d800a50400116040d00b07500452003038803009980002081c14150303a002410a8a00058000c81282d4421891b4031070300081c0c56400581c1c80342940f40b074440c000e030784003243d03030710030b0104007002402e0004c210903600c420090481d81480c034035130f42d400c04d00807084c0d11148141c90044280410950940100c9079060f40550301014008011f8000a04003240e940c0845026945ea010184408002410070002440b6900003485400c0420f607000f40b045400700c0e20f150426901c002c011601c02008588281f00c004020b0081016840e41c0340490000c1d44031300d244940c81566003c0c2d01d00018243d801030401580039071945612 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 799113219 1250 799111969 799111981
    0xb0423011a030706050409090c050a03150e0616081b070f050c04111b0a050f0c031603020102030f0318012a0806130b0607210207060203340b01060503 66
    0x900d601e280d5003510a400144090060540c400284c40403519403d9000c90314641e0360518542d400d00b15000190403450344000031083c1b02102520711030181c4581020400440d54204040d191031007540c41c41030b08009240d002910740d201f00030301ca800c46041d000d45005070150683e0003015a12660040311801901800070040c810140141034070303030b070054409100f0841c3e6410100c40c640710341700303960041b00c2d061000020700e018200481c004c0254030002316942541301c1d003011641c400507404494804d204800d060026015801c190a040b01e506800030f500b0201e880e110140503070030051424000c5042d0407460401c00200340221000d41d104e000c0c005955040c400180044075107070703e05000921501809203c160349610010390180740100b480000d10544c4000026000d20958401824680480700d0418504c920f080101414640e103030216070a542d0707174000981c0c0340e01400020180745480d002070780c84c2c4444090552004052003241028142000e65211041f50350b0030381041000540110070050 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 799114469 1250 799113219 799113251
    0x180b0f011e0302040c030b0306012909090f07180f090b01030b010c0209090a08130e0f041e0c0503030711032a040c0302090a080d02060c04060c0b042301 67
    0x4003512422650400009541000740c0e80344409100082c01543c0c1c034456442c840d8030903801300c006c3e01402030959005581d5145110014001d15091891081c00d07081d1204500d46820101c1e004014090600001540c40d030206400d4600003c100c10103110b61b10007a90041c1c00d02d101c02d50040d01d464a000c2d90901e0070b10b58448101c03415001150705051801814801d03603038100c0b40321418985c3c101d5001c600e0350707550420141400c04c181001040601f0105800d91b52600b108807007402d82d041d150a45020341d482103c01d1183d10001da40240c24005000c140c4024181c0c00c440c5600224002ca604006a565a5010a00e5540464000e541c0d1b40054070301c82401d45405d100b0761941c4202040406e06024001e28041000c02100c17001340e1080740d80da240c00c1490740c080d405a64080d07500814000c49541c0d5042519180d04071040540014011140002d50305e40c03040c0c040e1410790b02d4030b64803100d031a110750744c9a0030801c002610070f991441045102122200c09640040d01072104440040b6607000c0c001c5040c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 799115719 1250 799114469 799114471
    0x2190501110d0c1d010206190e1209090703020f070b070509120f2b110a05010c1205070519031e060807140a06050a0c1104020426060106090909030201180b0f 69
    0x740c1548154613041403a03079001905680001002409003040082003087d10001c01405000c80c1140c0034003142c01052041e008041c000d00e0303c0c25106901190340e40c500131000c910030f159403a86800000d000c801d0102d1007803540d141d40030945040c80ea02c0e02c1082c1c000201c0c2c543c9035449030812a8001040c0f42501c4809104141c8508490100c80c0c03811044a0440300d80703020300d03445000170040a10000c1c0d580c0401009024280f6170041d000700200564080000c001441541407045868289070103c0c0c46540f2560450f01c2016445c002d045050180002c1240502882d40360040d125150444000041d5168410035000345002d20052444600c1c0c4080b004c0e11800343c00700a44035000c2108100710b5150020225070404e682490007441d00304c400d203400300b1808180054030b6086072002c2808600300410740707580d0260807001100c50600e50707540a0b0b01a9101c609000c0c020000789482400c10080074550807000c545480ba00000c6105804650300505007039168905807103100701d107428040d14001c140411 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 799116969 1250 799115719 799115747
    0x6030f060f0c0806010f1b0c08060c07050d050c10051510030e03040332030901090510020a08030a0e01020313230601140607060c0c110d0302190501110d0c 68
    0xa2114410b0690040c0a01038001d044034140442e11030b41d40440c81c4036542140400d0995204c1014100050a040313411103400e00074800c0780d2054002141307580b010401510f951680c004020840410a040e044a680c0c00c000f014011302c1c8981c021780c128010040c01082c0c4201c80480d00200c071000d08200f08541c65000a003c00245854100142c04100c0040100c90550390410082c07140385882c9071000e00d2001610540047c0c8080044202c43c81000100c010000c2a07001d9884c5048180c5880405c80307030102026410380903a000d0704280303000a0701d08000e5507100740c040c000007a07454440b072011801c0e80d2045501d00400c00019508104003d9000300c0080d8004892240700701d00c14250300b0341e41d5a914180109411720f485401e03110381645d9541c084401c2298807003030910074046014000341092140501c2104c1a24000d400e0031054100303410f580583c0f9426900500711240946407407152520070485c180c0d41c0c2c5d5203074103031180090340c0080142003041c0300010001c2e284142044c014032070000c0f0407003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 799118219 1250 799116969 799116971
    0x607030e100212010312020715020606030c010806180a061806030b071b08030c0f0409150611101515080411040c0e010f0e0301050c0c06100f18020d06030f060f 70
    0x20000c0c1903410f214490540740d1082403082e9204801c0002c6c1e00e048940e6220010078851200180e095a1703020038142c0c000c0b03000780e0440e20781246040065030540c0c0d00b1160560042d01010800118070045010540c004895103800140030392122181e4002580e42c103038958040742c84090030070421003501402684000d2900d004012185484100d005400a01402502c042d2021001ca4140040328049812049550050543d0f40b69a982c00c0710160030700e42d8101c07100114541000440c14080e42c4506024070250740034200b000d0100070340310014549001c1140088180c00c0c0041280c90f00011008c808144944a044a074038191609440ba499441d414901845c1840c000c4640d1035000076802040b1602400c09042810442c0012140045020f40c100e505600303100c00d100d40207500400501850203040281ca030180c0d202c61070000c042c02903100d0000315a034140f6041210f241100601c103550107007200058a004034007040201921400c0d042991003402e221902170130095203100380c43c880f100401d0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 799119469 1250 799118219 799118227
    0x3070b1201090905070e0718150f0c230a020a0303020115090c08060f040e1204081b0a210506010b0d06080a0f061d0a0b10050a18020a0905030607030e1002 68
    0x41c0c3c1c01c1c1c4400041c41b03600080020301005c20482400b501c00c20311250030031410040380b0303030365004c40b440b500b1a40d21410000c110610454680140b0a030b840c10001900b0091050b40d05c0c50580d03404003400d9202d0803984503405440081c80c0180e9400c500700c070080d4029800400e803a003030181d44902100250740b0a400041c0340400c00d5a80b035401641c0260301c0002200c2501c000f030740c0b9101140240a0340001d407500e07401100c40030038170958483d0142040e41d01080846503105440314010342e5194000030315681c829680320040bc00403420504008201842c54000c4003650380554484d49416003e070008200340102040c2104c00884503c00c1d0360052a040009004005070750303d41c42d12078034420710098071450700e80040314010540500b0510801c07070a40100c440214040c10054004007050b1229410154055000180d500e801c1c1e200300f051b50112182c080da05281031808a000b0341c8000e001509000d00000001950750701030040d103101d4182074902003410740c20012001d0503d0641070916410307601c180 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 799120719 1250 799119469 799119473
    0x3141311040b0310090c0f031a06060d180c0b070b0a020904021603020c09070801140d0c0510080402090f042a090905061803191116031a01061d011b0203070b12010909 73
    0x2821804800e24042c132a040a41ca8032b0020411904c500b1448510460a1203020292404640b080121003809040d1051325541c8075081c020042c401c01d94054040d505580c040740181c80564010082508020f00c01454007201001d1802031480105003600940c00c41c1400c948603090640d000c640c01041442c003040a9810b090070580090292820b0038040d00c01d04c100101003142a2000c0c001400c40103003410349070303105540003c0460300210f5040707021700784d1003010401d40c1901c00101800b607036000c4207a14801c5400d038540811642805650700021034112000100036a00d442029a0107001e080944007038a040d40d030141c8441c0c0042c41c8a406540200202044400e200b4403080500d94a031410861205071040030f00d280102061404402240028001003007103004455903d0b5101c101c49c40e10443da03a00c5e013017500d070910303002e014480c604000c25480d446503102c1d181c007180303a40c03943c0e580c840c15441d2034000c40d14010040d009a10700e00c60004801d40740013241880140140300380c5400b848245a1030b = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 799121969 1250 799120719 799120733
    0xc160b1b06131b090510090e011a240a080a15030507140a08032b060e01061412010915210602030702031c0c03141311040b0310090c0f03 60
    0x1081000d000d50480c0d01641c21960740c800303518402424265405d01250a0200404d521003825102e542c078600d191508840a645060103412221800c014030010090440d105000756001d140260ba10310443c58801100440c6944000c2c050700c11186d50303031019928121041c04200c4040036201d000030300d6032101c2003002560000e0502c080d101402c1450442a06070000300301405000c0e08aa5894000070603201d4908070f10040600e110420441c036261690f41428540d030449040f0f001e0880c0c403c64040040c0111400340e484102e10b8040401d00c14545030f507080e880d0050800a810071405180c072240d4100c20384804601181c060081e0002182032140030b800b00007254074609100404503900480010600d5000b4801d4850300030102d8548103180c4210f80052008220041c00b11001c68a0112500341680d609460f1a1052100c2900485c1d071070354584842d007903000213400c010380c429151283c120080d1414003a82503441014500416102018540307600c103006c080d00080d1110607185000c001003101 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 799123219 1250 799121969 799122001
    0x301030c053a050609061501050f030114060904020327011503110406080a1505070f020a172511101b050a0c081014090c060c160b1b06 59
    0x240c14044511220010318410952100402c09012070244404010080c000410300c0b5206540f00d650420140c2e030404010356403402159910405202e0610050003031082c00784640302d40400051605041015100000d0203070b034001c841200c441400f11070000784100e011000c409602203403000030301441032040d54103500c091540c44083c2010f01000c03030365140c584503a0320800c060074000c0c003500c2c2c0b40c03a21828031304064040c800c00c08070303054a0000060a51440740343e2803560000c699000d800c200c903031515020f10920841c51004501c000030804051003085484411031900518110384490600c54100100300042c00b404281c00303441001d51412a941c0d1081c0807004000b40007a0320510140715041961a0003840c80c0000c0c809800b40750045100c0c035001030f9004522042d504103020403035060a250740d060609a41507480d550202081c5c409514040000d0220100d190089424800200e0441b0004d1440c55120503039a610001c2d44c2400d064a1701030201040b0002c40080019052550112842c418 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 799124469 1250 799123219 799123279
    0x5030106061428200a020a0303080402010210020d0b240a0503100f0611010f0912050c100c111216020f04021903020406091e03080a090b0706020301030c05 68
    0x10004683c0c00b00c070070b4481500ca650b0900c030501600821100380240c00c3d0900c43c40c4650488024845880c03107048000386503400d696000d00310702e10042c42d540c0c080e2807641c00a4800c0b8154002c10080d100d0213491440641110030041401041c00041031042c4030310501002c88403196400510400e5060f2988107084070400741080c07400f15660341d1400701e401820f0400740c2010508410005001a001d03520006c0c0074682d0201d100200064003150780a60304072410715000411311540c1600c80a0041d0003000900380210b401400e8640259181301d611007261a95882c51000c110807868001004078100b140b03030700a03040b008643d8546040741c812449030301c0070600002d200c1d03015203180b1205c9440d81c0d016030301d811405070031082c5ca60000c280b01070043c0d000307409200001f80c0d01c4007000a4403480801c050309400c40300c03901d40c2c02c19400c6880d900d0042e03001c0d8501c5000d100000300006040b202102c000d02c0500d0150000586170350440c0b500300a6000d60f6070120744982e8070840244036030f09014110600240d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 799125719 1250 799124469 799124507
    0x705150708090603040503040f0803070204050603010c1e02030c010612030201050c12013c031205120a0207030e0d03030606030b060f180f1233070e060d021801090503010606 76
    0x20b0b07a1031521b40d1551103113402203004a046114000390b0a5400806098800c0c400c0301d007480550f41c1d0381c00781801c13214200f041c1d0700090704003400c0c400002703103881020003a0103641c0b050340d241401d00c11801c1d080d124994000400c01001c26030f03031406d15034284181c0d600000148036140c075203900030f29001003511040c0150400341140422240d00450000520200f5001100c4101d030541c500c00032184861405100990704952000c1000169a114404941107106005440d10442e161b180007003009401c4a40c040702840450b445404080d5146180422602d100c0c4e9401f048203424168010281c842d0008010301031441401683c40880c4c7c0c02040c1c1e4194401140e200c00002600b030001400040803602a5401c0340c50b80f02c11104003030011500420b94509010007020600ba2100000d440004a04281d248a40c0c2c0c0004600040e10405440c0c4244070010400d0341440d04450020089070300c086080012044d0a40c0030701e01d256000528100140800c40003000b40c0752520601074000c585401c0c1d005a01 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 799126969 1250 799125719 799125721
    0x150418030806040f0c021b0a121509050106180c030b06070b04060b04051501090b0f121305031602030d02070302060316260103230c01080a020d0c020705150708090603 73
    0xa8031550321010050400703030820701c9000301042000e51920f41d014584e41c00c0c05465042408542000301035001180c483c0003811050500503203800002031800c0242e040384ae501c84038500c000c51001d02504019150344900b8151050a000c02e0100711040004407006041c1404040d03001540c0b1002a00c2800f07400c00d01c6404580c1c0d651500c0e4000f0891500b0a43d4814034000521400b1601c4804000c0c0700030080e2210002c031511910b482c84540207814610500074810001e84560a40c2001d0641d040703150500350107500c1740c86075207840c01e581110f108a0361010356400d0a205511b01005a418159a94009450030078216008291144002482d80c024541d404e29800180361180c815103000d00c0b80902c800b03003544a240c4210514400170306c001c0c0c440c07920b0480208844039290b000c0702d401340d02d244020010040c8600055802c07500007030101c40100d500740f25503d011039003070203002c484009a90240c410740d41400100406030000701e10180588a0a100e0240002c002d6000c4580710a0122002600e03 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 799128219 1250 799126969 799126981
    0xf1f09050606040f14010e06031513030e1206010303050904141603270c060305060915010813080c0105090d17011a07020a0b120a0e031c06050406030b1504180308 71
    0x21704400c2e51840d00c0100c210340001449802c02c60002d0040008806036a5400001c0f0302c003044800095640392850103481008100181c0207001801034640054110f110080b010443d0b94201402648140c021a000040c282034070b16144c0708a0b010740d0349032050b0031044d003824410a003d0805450140c0107043c0d691380d9888080c13450611301080c2e502c03444050202950a0300d00141c802e1101c0c0706003400f090916010410624042321080e1164144040c0c66180c0f03801640112094040503101254030400e480f0b4640106100700300814051021000104003424800c2c0000d140030201404036042283d081e8041440c000034024850454882e0310003098182c2c0e500a02c1200d5124a40000b940006020741c0014501c500c48058150f108500d03d890f07810f55100300c00c0303405448852140f0f1040b50010020442c3c0e4910390072491001203144240025a03941b04e20100d4101c1e04960070030f5070350480312010064001921243c6404185041d10280032031002d1341001840144d001c180102071011394030001e42 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 799129469 1250 799128219 799128221
    0x50a12150b0a0c02121219051e07110a120602130b03181c0c03080a06050303160c050a030803060105030c07080301031217280902030f1f09050606040f 66
    0x301030314190741e60703039a241400007001d4591408000d0482c000d003a1501c4070040c03100d01046c1c0c104008202140f0901d41410302e00410901050040d41c0c500f84074040c8104070000200e403d00100120210b1a1140c2d60000c0341851810301100b0070503644640f1907100148802d07940c07200c0b024031580c0e11075030140c1c44940851783c030b200d10413880d0082050000c021023000095480b480c501c1c055207100d03105071008624110072200c4002211607149010800300050040080d02c03481000c1d500c000000c40c006400c07900d9000081c02d55000c40c40074034001c400c0c01e400609200c0440740b140c004190460340265245d266a031360f030300c0354000200a9414001d020000840d800c0c00b0700221810309034004a0709035250784a01c0e0983d071a0340810f0300d100000f80c10403420000c00120000035409141e160030f4010070310564141003072100e42c50304881400030f80c0320754201005840030800c40c03012904035805045004145d0084042c0c0e10000300d020740480b0308022030300000c0303500420b8140e00000709903004150070b021801480 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 799130719 1250 799129469 799129511
    0x9040b030304180617010c02032a0f1c020106080a030c05120705160e090703060e070801060806010501110a081603091206090b0903041d0703060b04080c10050a12 71
    0x494010408040c500000e009035202c60f0540304112207a1101505c4c40800600301c48041d0f0082002d82d0003000b4003034084884003100300d000303515289851440044241c040c1d0416544200c026203942c004100542c4249051560314201c0c0c005200070043d8920b0410b6041e6104064031000e02031002048940c014170006000106203114240900c0d55615100d1a0143e500c00d030078128141d103c000218089801c18296a1088c000e011705001024803d040d501c3c0d0358000c00781e06990359400e02c03401c1e00001e022a02070003000000c0540d8400340507250301d070100141101c21079140e9412a07800c0b0603810400600080151004ca91003107a03d104101a01e141c00c1d1421451600001030090f9103034506800c100a5800c00b900103846040d820361140c40b003280e0075640740210f00401c41d5040c8000c1c400081c1c06070703580700d5981c021550710740469450354644a031348440d4010f07000418540c0201c40305102d11b041034210428980c400345002440c00e1400c0b40300500046103848100c850b83c0e1a040c82d171040900001040c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 799131969 1250 799130719 799130729
    0x30f03040503250512071112010e010f0b1002030702130203270a03031113050d110a0e1005060a17060109051002010c03110406090e0702030403050a0309181109040b030304 75
    0xf0f01074440065080303800d21641000101c40364407900011211903200703031040d40c80081d4404070721602e1507254020003800e480181c0c0b214200d0b40d6501600342081c9400d00400c450341d00ca1100018480400d07106000300e4107152400300c415580104041001611010541d4002584503a0f00580b01d441d2002e043c00010200442d0200c03000100c038030717940124004903072041201e00c644c074100608500340c0403040f09805035519101001c0c1011400304010701b00b0a072280e407003a109034195400110301000041400781c144d04007403036000354001007140b01240d0840400142104031101c6081c00d450150013018104076003070b100d03082c2c0c4001c80818230716401030700c0882c05840001c0404074182c003001e030001d00900401d030b68580042d00b04000c001410034074104076402d0310340b00c2ea01c4055141c00d1444290084101801c500218030041000001040083c0500da140328401d0380c592280f2860882020200700b080101031920314035010705002440c18060031502048001d42d400308030080d1020009040d40529480 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 799133219 1250 799131969 799131997
    0x507020d0303110a0f230a031503020405040b01181b2a11040f09050a06092105040603050f0906010e07050418050703240b03040212100f06080c03030f03040503 70
    0x803024850303402074111a0719000581e240c501c0300c243c042d80b0a9161410503421414150700b0000c0c7c1012034400c1d0804548a46101c00d40010305589a0104084031003c807816a18080d01c0401484006c07810304031302480386a41441441344400c00803441e658000b003c24183d092008400f40c0c2011800c0300039036401741e05505a502d15607240b050400c02040161442c0c42403082d494440e51015180a92050081b40303500a80280200002a41d4001c01480301e81c40075a004010708401800d21b850b03090704074181c0c06e0903070349481e2124034001018044e110040c004200d001c80790b100f000707026940052600d0440721500c000300c015458005c030075640c0e0701c22500305c11420029043c4e540b080c82142d070003103401a00180d404000c807180711400080c0c070404c502e03800090740c046184100520003900c4040c6030028001440d039410942c02d92005031809202c000361481c0070341c480000c0a05c145030b41c8a580b00405440740a4200b40c640b42c00004e0f103038410044c1010f503041004c8041804e0042c100281c0f2140115042 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 799134469 1250 799133219 799133227
    0x6151e120604021906080a051b0a02210c0a03030b01051c0b030706020703150e0c100c0b01091109060d09060e10060b090f06180310091505070507020d030311 69
    0x960280c4415080b94241c3c0240d5241d01aa034600046664403030454000d41c0c1c0b0b2004a844e41c9012502401014148000d038525401d50762440208100c003c083c0c1900f0f6070000d10340700d117109010034161240c0d25425080e6100901595034000b00c0440e402204072742c90724001a44401820040c2c4650260001c60071180700303116401e404581c070a9000704c00c1d262048084544040c0d40e82c1c800c99403208103000c000c014550074000c021121107030f034108400d4070402c1c40c241c884541e000408903490b0300d0b00c801108005400b01088a042c49401c4d00300e14058007140c00c0500c46041c011b1840e01441c0300b50790901d801000001103402c000500ca07840f40103001e074000f009001040b894000c0946d907004202c155000e00d0316010300000c195543ca8222204030001810104128100780c0402c480c4da0030220320017014211a840542480e42d052141409080c1101c0002980409130b040075102c8404e086000b0a200380341c58140f0284582020a0701c0e000d130790488030452046060301c0c044004c0c0403082d08074180031074082 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 799135719 1250 799134469 799134499
    0x6150902030109060e063c10030b011b03020319050c03031008060a1b0e0102010e3304021806030a0c0e0403110105070804032003070f0b060306151e 65
    0x501314008641005400704050f40b00c4d401003084040884130601d0b0000205481444101e0340544d4260890b28550b038680c0f04030a119004c10820f101412001c40000d40d510341d80c41c46580c1202c5584400041c0c4d5598800310801960040e54a202c0c05540e560305c4202a046030000e00d2080044a010710040400d90340c50741000b4000124507a00c0f402441d0341c6000b028000303400c403140780c800c84040850070103c07010340031070414040e900ba00704206414115521100340e016050020401000c284c031030964a18100d0000b080c03c007001800d0a0b516016054032030043c0030241e65201101c0c84200310702200140103845010010345400740d008030091020107808000101e001040e80301e1403107a800313512640e04903032040d0f90321422200200c411310007003007070b16021a02180c461641801e000402c40712228148040384541445c541003424111850141010355100b08004400e01d00c2e000ba90503001001e107414080111041b1444503001203000d0303014402020442c51941602245640d8094a070230104c1041c9 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 799136969 1250 799135719 799135721
    0x61d03010f0507022802060304060e150103030f030c0e060a0c24110c150a0204051216081f150b030703150501050a1d0d02180a1a06040306150902030109 67
    0x80703c0500c003501500440721881c45280c00320100070004c9051000003000540d081003143d0f00301a0050b10700d9503480000f0071020000300192007144a050500c40d15540c59440e00800700088124804209801c10401d40d044540283c2d94049000301202c545031220b0580c42d04944d810b41e5544c0c05000c2480403215000d2903012000302d00c0740c2c0c160040080c41200a600a04120340c1316240000c01c0981c440420385010f80311840c0740642008803510058901607503140041c04000780013000345501c0d002250005103600604105600400381c4501030441c4510340006041e10103040300c4040707c42c40e1a1010a00035a50341010030000e000d80b01c0c03581e034490502d104014001c0889001e0b01702c5c00f2001400200b200c0d8000c0007600c80001c00f41d40c5000441d00b82014884440a4000c003458000e600da501150050ba5030758002480c41840721550300382450481142000c0d20340f102c40a032004516400421640e44031442201c0a9a4101c1d40120b104803a180301c2c1e04841d000c60344945091440480003149604a07 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 799138219 1250 799136969 799136971
    0x301b0b0a0305010506130e131407140405160c0f0b0a050603010b1207050f06070b07021507080106090902210907080c01050f090f01090b0f0301170607020601061d03010f05 75
    0x203a40c0c04110b40d03a250350070b014186c46040f01007481581e5140381044804e16101455038803850b40040541f6902903681c4480707119101212104464001c004c0c20301c24841030041004031107904540501c11400c0c0f10344802d0190065034000c404010080700c2050034044007210514206912504050062814569100c004c100981d03d480c401c0d401c000b1015680d140c1603001d24042d420000241001a1a00007040b0418510008490300454103120083c042105040d25920404550300905410800d920b04440c04080092559051219002c01400381c140d02954407070644200041c0142c0d10340056400781c0c0c03c2c0d00d200b800d41101c1a00360313040001d9140041003d0342240c0c800300c11910158000801500c840c010780d400721500007130034030a20b61289084030501d889060103040c05a160b5031106c9264025502c58650342c189440004010000302c0c0400c1e00c080b03d130700306040141c0424248044003c3d11400107103c2c80c810440c000000d62450010703426070704a1890010003c004100e000006c079405414 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 799139469 1250 799138219 799138237
    0xf0a0801051c12031503060207080406140c0d0e0105070f030f09060e0108160e030a0b011a0c03070201030504020a0b04230105040f1203030b040e0115301b0b 69
    0x14030744903000b1908030010074001082d80540c5849020700e680300100d00074140c0c002d08410311034030fa0700000701080640c40200541d50059206035504c6052842c0030b0511a83c49207505004001080741070741004012844601d10046890000801e03a4034400407616402082c00c0a0804070402c0a04001c06400604425400350540c4842c06c00310394490099685140340840580440d130868002070b1910080148442419010f092042d1101540c10109142407584001103541d865000f00501c5411a2060348016141e002c200075850454070b803d4607500e0b8040c11034004e05068955003c1811943e803018107401403d911340c206a101c40d5103964030070b87c09071030040800c0350180725420b440d01075110718200c5041d1006005030620741845c0004030480d9440d030101c00d404145c0d484a60201550f80d80c0103c0c1e09071824071b000414440d040007000f0501d500c080e4403d18a10b40e81d94003600e200121170840403020101010800e00c504030f1400d01800201c1042c07085030952610a902059003000c1901a01c4040 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 799140719 1250 799139469 799139479
    0xe060304030f230901080c0903070e040f062c03070c090b0d240e010b03061b0d051003060513031e0903050313031e020a0311040209031f0b010513030b07050f0a080105 73
    0xa1291502035502d03200e23034400c564160300a03010500042c00038140d5a80c1140c8107564010302015240c550a00729210044940c01c10f4180081c01c042c601d000070401e44c2c000026001661070b020590741c8226034010288290083c0d47d07180c0000d6a40d1303607241c0510310003140c0c22a4052200141002002003807410001c51800d05c9441d11107c400e0440c4148904100c94801600900b400c2c1c6a103c90082c072444c2d8040e004040362000c11489400e000180289030081c030424080440c05811032800c842030743c6004010005081c0d6010804000c641c1c08503120310301c502d00d52600118100903002c12102114240c00207002844001005001b80c0d695070b14090890b40540d1030012105600c000c1c00c0d81e001c01030300700690301c010076003c2440452901110841d45000007040140b50a0340c03607002c03a080c43e150b01450452040901905e2109500500441d80500d10034a03001e850802a0081042d001041c1d02002c2c041d00302000c00030b15a103029004541040042c020b1042e15078090b040014140c0000340500381c09a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 799141969 1250 799140719 799140721
    0x50d080702102a0b0f0606040f060203070b1609060e0a09051e060d0f08031e180f07051e0604170f0c0d030c0204050705130816060e060304030f23090108 67
    0x400c0001d003e00308460b40445440f05989428003c4058200040e040652104080000044003003114401e140103010071340141d500c8401c1401e040984100c0240b180c00c0e9032041d029028045d5078400050825079600f03080c104440b038207860103d1130250294001003116450001441141074a50080025042c038002190140ea52210180a01c51404480c010022508645164001441800a55030249000d07040b00c20060b5807100c800062401640c1c1d02030403503c481102e10010300184004603201a02d000100101d600e4180030070703000c440d02c0700062101d0400c07003011301841c2d803294201c038001c001c4400d407010310610100300140c903107101c018411214850807458040780d040020003481c4080c3c05898880303c6100c035800384409080020494070400000b001444254103000218101401140d80101780015461103100240c2c1d200303400500502c01141c02034881562400c0849a005506151009220340d41010986102c1807640246483c0b849001d2940c00480c59000034003038065099948240d5 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 799143219 1250 799141969 799142027
    0xf020d0605150d0506180403050a02070f0b070212100504081b0706120203090c03030d14010e060a06110a061e0b0405090304060f18140102070e010f050d08070210 71
    0xc01c10306240e28070100c070802d0041d19401d0f00360b54001940440c01a2042038002e20612200e40081004c580880208802240b4100f6050b8108024009440002c02c1a1902ca0034a20b4102d05e90041400007403080420b0980e140148009006003031040b904440f09108604043c6012015500101322510180820060107186180c002400ca811150a07803907842c1031040e0650900040c1d800141100302901c030780a0b60b40410348040000b003d0b002d6800600050384100380c64819000041a07000c024040c10348414022113958000310030f01180c5160421240321094510100e081090056002e4095858128090719180301135015070450640c2e02d1040200081c240b0800003244e005a0741200c0c55441031109100d01d0b0300841810212082a080813101500c50a444051086a0ba001003108820381c580c50110b07560100913410240014072520b90142d81403d405811440c01c81c07258030710440000700e040086c040c0b081c1c00c03101082e030007070480781c4400ca00d02409400845000301e00030011a0160386412 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 799144469 1250 799143219 799143229
    0x70f0305060915060f0d060b030a060e01062408070c1226091c09090e070801060e070806042c07180b150a030b09010e04060f050402010e19090f020d0605 67
    0x841360100400c0410102d83e120281703c5460560304003122a10b0350746104011507031b800c2000c44c0a061180c84041801042c81e0f10322401e4a000e40d00032011075a0b5540090316800001940e4003110099141402c41550707508000c031420140c111001d08914a91802120703555405404606400c0001c1c0b054040680301c0031841a4045086070511380c41d030030a090407861810401032014100041d49017207008151250310b90401c403114801c19800c2d580c000ca80400c0059028061600100b011031070100300c07454100c1018000170002410f09100701d076034194031528250748100c1010f004c0f45d85031440110100c40181c05640b216240540e10000310f444588003040fa14900640c01e01940c041c2c9085285030004950f201d8a4001054001c10b054841703010101944856281a009003101d00d95001241002e05191007140d441906e200c01060420f000c01000d40d0308030540742c51824082d035a03101101c450720710324004940160081d40803541800d860500301c400c41c3d0064420000030950401c21185d83c1c03c1040 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 799145719 1250 799144469 799144471
    0x110918060f01031a1b0409020c01050604180602090406121202121303061a1008010e10030b06091306150614041a0c071503020304260d0c02070f0305060915 68
    0x1300031162408a0300601c080b07480035150440c00c01c440c000c0f480760050500c40c240760000c2c0c101c48001030307010454503042402401801d40000050354100990b0081e0f900101c010340d00150701030002e90700003c0d6640d041e00d43d50b00c440d00414a035601400906041d181050308001007504100040c030662341403501614012049500c0580e486026045592440c1c0c2c03020090b19081d00900021405001070399032030b0300c50f000c08440c42a45a683c1540c158184184c0002c02200603000c61101c4440c8401400000c901a0364540c000304203d5404156035107442c90302c042d091008400800c018140500031161b2580411510282c030800e031946081d001c0c0c6034090f00e1090061380301d07196020070088500d480c1252130200402a8034039217825220010707201e40e102c5e51100440ca2090700043e500008000511081d240b201c0352945108d6607049100b1040150131278207000e569940c405aa070f46065501c5c15134020440d56009040103c0c003a48909d960b410000c0e15078404a44000c59805040c00511418103022106 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 799146969 1250 799145719 799145723
    0x518123004020906100f0e120f030a0801080c0d020d020f0415060e04020c030a0f1808070603050c1207050a0c020d05010c020c03030304170a2601060e0109050d02060304110918060f0103 81
    0xc540d22408200d021140c401f8542d805640190303d001040b100310b2400d00c07040d4621b00c030040c021541c03206105d900400e5550146d00a14003508111a40c8500303130703500004400400d40468426034041c80500000c0c900505001e0310356070242c0341c0044c06002042d41d05e240ca08070b580341d4445126421450b014032040c1e10801c000c101041c0c100300711002c510740c01011061481d20a61a14044002021201c00701056060300403089030350103907070100000c075403500440e035005180704400c605001c6500aa040510f82c0900741d14180700000c500d440c8054820340008440d103030000c0410340d45401c0c1d82400c3d030003401c0e16941c1c2401030140100c5000241000022680925445140b00c1411000d40401c44810f8010082681c10041000214050003025049101544e41d55840c00300803945002130140144000b0f039030450601180b480d00b00010303650700490300b00c1c05405036076850f500d541da0300d4000240c141040c0303859403008800c2c090146070803004601806210040007211219110034000d802d5400c0b0034800 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 799148219 1250 799146969 799146977
    0x91b0a030c08130c051201020c1009110f031b1c030305060a1e060f0219030e030d0f020c060904020d06060804300f02070906080f01051812300402090610 67
    0x108110f86d060007103445082140c107500050038400e40041c8242020124103090050307030340741c41e00e075000e0091044444401e1082103600c0b0701c1d00750320040420f07254959802c008058410041210240b6107a03901c07040c082610030b03e1891250080c919002e0001d01083d00c40d540940c0c240b10010071440b240c00040320310031640d000b0040b02c0300d00d05035040700c2101c40c0407001707001c5008407030f44000c440541825582d50315101e40c44000344040d20348145894400908941010440007100102c1c940b500031070a0503c0035020341d100c55079140d034000400c010744900680441540d00d00301e00055643d85c0600242d0086200311045d42c1c1c10074845520301c031008020280d50010004405401051a01520000c580c551041c016140c0b400d6803055400c080f1589940148030369000445d40510b81c00d0207103c0d01c1e9112607922040c0c81c01e0385000d0200d540c2c2d115141a81032407240005492000c2406140c004071b40401422400365504000035800c0100c031302c3c152000c81c060b294101c040765161410b21128a484030255035 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 799149469 1250 799148219 799148243
    0x11150c250b031b04030b04050f0c090a0e0a0c03060c090807030b01051e0d03090911041202010e0a15020703110618010e0409060612050c01110c091b0a030c0813 70
    0x1616074072a400034108072400505042441030685909018000a5002c0e410104a5103402d060050030700c0d82010010b50180c015000c031203155500c000d10180c1050815000182000c000b2250a24185400070040d0509418890000c10411032b604075241c07203820f99455521a0b0340e180013041d0342c0c03101804010096000c00005203e00d051070340c1010001342020440503454001000400c0d50303921001002e400103521b01d0b0341441950326500400160250301c0c40030520f00381c40e024030034900c484a80300c02410400c4072201203210f82d603500b58010240081c41c0c6040c5a0360300c0c401c00a035a07008680f200321002003c1c0d40d114082c078949402500d801c10041e40b005a042200600119503400214021a5100390b0754510700c80441d5492064102500702400e8414452881d070030442d1030b0910040d6180d0410002e8409901c000f000450188040030301552040e4284d1241c0035203002d160512040d02d40040c001003066044240d1541040308002c1c05030f2180b03219608c8600c40c144519140d0744001c0c2034817901603 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 799150719 1250 799149469 799149479
    0x150f0105041a0333040510030f120c12020601030b0106090b0a11031b0105100f030c090902030304050405071e0e1027170c100e060711150c25 62
    0x4001150b01039503185541800c4007401d95001e01d42203482200c1500c4d032000101301019030910f4401c05421038540b01220304c0f07079840c0d81e4410310301c40442c0704001c2441b07a038040078450007400307104266074003070313011000c0142075019403002540d5040910064500e140b40100004400380911024000da90018401d87d01e450741c4e104041e640711403042d07241d062922082048180b03441098010740180e400302030000c00c10341002d071b180701d0700413800e40c2040b070fa480102a010000511140d070170f081110320303411000c60380c1019400041d05501642d884960440d00b04000c02503200d40c0400711481c0103400320700300344c0c401000500440b42810b010784080d400081207011307502d0a50180c04260303012600d4030300628006d10286400c0c0980c041e0366120a0302c190307118014038584e600510542d4a10b0000307440080041465800003030440107501c9901c3d00803407001a0240c240003450716031088014019000c0205480c19a40300132455000c00701e0001c190180c1030029a080700b510000c00c50b681425410551418101 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 799151969 1250 799150719 799150769
    0xb0105041b030c0908070603060f05030c03030304030f0e0301050109020309010c1728060e0907080c0307050d060b0d0803070e150415050c060124030506090c0c0705040203150f010504 80
    0x1181e0f0805224401c1c80029081c0c000f00030800c0500401e5070086100ca244c900e160030001400c0e00711922170303040b0a41188098a0000682c1c0e40070f1780600d41840300309c10600080d00c1c0d08030740310900c54141d400c0c4000030808a549800460003006500020400d8401005048952207940c6071803540100c582c0f400f0619803401c4014598011216501205501c81114080f0041b5081c551081001252400811044810034050100248911006010040c120000181e1241103d000e02807280e1201c0401d8400e200089e400030321041d4025104615940d00c40c100021950001c890382030001d180303c500403e55007000c2c0e40c4103502c0b21103200b815080c18100201c0d8000f000d0b8a080c800100031081c00030010100f003c104c540d0007000521100c140c66800d11010b241141c1c0e1a1a60105042c24401400f120782c5035840140e5110028010007600ca1786136403055418015968840c82d402400030041c445030000044000c44c00304011181c1001c28500c2c8001501d15000300e1107052a82414200107250080c90 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 799153219 1250 799151969 799151981
    0x170f190506030c03160e011a0d1104150207170c090f0604090f03051210050f0d03050c0a0b01091b0c06022505010c0f0203030108100e07210b0105041b03 67
    0x4010b060312015440980807030b252040c0520784d150180e0000c0010000a5609002c05006d0310100e180d54040240241011001d4030924400c010b41d903640d0031141742d41281030010340300605482c1000b1714694031014002540c2d50494024111000860f070040700c0050030000705000010b0024100942c0e82d9149034a58131080780c024085900207403585600c2000503482d500202000740b01c1d0b1034458136a80079908072900c8c888020000c03074240c8105031003406070707964410850307583c0b10045410031503c1c00140b40850f0203001c1c0001b003c1042c812031000740200b05108086034141d403880b00041000b2100e880305403031164891502a0046640021030f00041010750b00109224200c003515081d8045139a58441101c100c182c406035680d035518003800a00580c81001c010307200b031040c1300031811035062901c200d480d0840601c0340403410b640d80101451041c0c0900c600001800010b02d81c0ea0765802d40041d104140540080483e05111000008140784c5002d210384041442400203890001c0040300c0164001d0070 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 799154469 1250 799153219 799153231
    0x90a1206020906070c030303050705030f040f030306180f0b06180d080403021507060b0f03060a090309210c09060b0f0a0c0f0302011a0a05031b0d12170f1905 69
    0x6001c01480c2c0094440000802e01940300385141402a861070800404644000e80080201f110401c1409881010740007000d40180e045007072170110301c0581c90b00303a0041000b940441d51014080003210a80c140c030307034821a601700840d0000d210780380007003081020303501c135000d54000754540d10b12084c2c00c40e040402a03c12058454000640741c0354507a000108021580014440c503010000342d9041082110b02914449120603901c0f144554000030000b5110103008080540227a9a20403250030f05208100003030040c0b14081d10360f103400000a07180c603072201d074100702590291030600c0c0004030b2603020f11800b13040300c1d0300315065800c05030310302407007109035000070003131800c000d00c5407a1403000c0b90b00c1f07890440c80d045c484e03000081c02060030301e0403403810034026200c24425259440d08010a032008201009a0003070b019039445540410400555404105080030346103d00e61259641040d0f080f52400e2107051903402c1c40500c80e6210120380741919401c41b0010320a003403c4c0da0103486640103800880d0000303 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 799155719 1250 799154469 799154471
    0x6010b030c13090905030417030702030d0e01200606010801170a030e011205100807050d1112011b080901060902040b12060a050402070f0c0b0705031210052d01020102090a1206 77
    0x250764003082001c0d10314260007981c5c40d4100003002c00c07905a40d503069607030920000d03025509000031500081d8a910030102c4074818030030303c1c5044040a0b84100350796203020441c1c0e441c158070304038200c2d01250b50300402c40c1d01c05d0114a003140041040e0107440040254100c41c0e900515544190349e808440c1a580070503041d0510250030a11402060340b4000c2d54420f0014082c43c401242c81c000c0003903c2d107842c962000d402211152001c0000c19641c81401c90040386c2a00c2001c922001005828010600306910980c055045000402d48580c401e407494001d00c00d00c0024801c1a4407400140202d1140b4441c40d00d0f400720801c13004101c01d03079103190700e8be01440081414a04550301c0012800b41d074080381040340c1441c070b0a0040c600308001c014405014110164282c0c1c202000340e902e1907901c0c41120615240c6502410000e440102e000c0410005405d0141c054403614032290000a50700c04480440503000c2d0000c1c1b4400f00355441407083c3c07815000010700d0401c116103030130791030340d07407000c05038800e40d059 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 799156969 1250 799155719 799155757
    0x60904080a0923030c011d060c0f01090321060b09040c090e01120303060b0304111201110d0e0606030d1e052502011214040b06030a02092706010b030c 66
    0x503604140f2441044242c40d01441039018400c003014201380c2c0041c0c119042c0105001c03818100c0c0759071480600036600a80d0b00390782d1002e01100403440d0005c83c00c8a445190300340300030401003561004a42d284141e000c00f80500720b000d401d44440581c1c0c1580900c8850f0842441743c0b4529180c00d41100c80e482c149800c080c861152540c02415284600740c20013a040041e00041c4020160300d40300302c0d4000e100d42ca46007800c50400d80d40f10040c105400c4c4c079051045422130306246106000794414115000605461a50359440388080f034050302056003038106c82d014000004103c2d040200e0350b01001e0403140d90b8003903030008038000041380c1c8407145000002c21009010204041c9400b509956404648030481000190b03a440010200607010702071804450411f40d21120b002210034900da006175000258030500d59803030b00403918003c20100044d501041c50801e201c2c4007c40900800f005580140082c40a840c168440342d0307032220f081c410f04001181c100001140885200c02500030001c1c40d803207000c56 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 799158219 1250 799156969 799156979
    0xb01021f14070810090624020f03030f01030b010501030509100c03061d1503070b09101710170a0819050405060d05061e0d02010e0a0902040902041508060904080a09 72
    0x1e40c040444104010400020500080344070548008000344581c0f00180203c07424200340c1040e010507446842401c4100000a04003503000b800b804441100c1041100d0312440c04080f0340c0d0313002d00203100556050300100e0020600c0d500c01d000d00781c4107a014400901a030307181600f20100400c2002c156504060f51580007080c3c4910820b07034214070780c007000c6d006259800c122600780384414030300091304c0c801c0d84041400c01c1008805070613100c40c850102da280801480060b01903441c0c005202101500d43d40306410820381204003040070080d11901d80b0b15082d00442c0d0385c0065561191036602030031071401030161104404880396543d003413081920b40107003890390700c402086035900709003d40c0d240661600704019240c103001d9035213507444441e40c0d0451009030303443c00807480c118640203029040080d504a2404070b074480800580040032207003c215078590b6290304030b100a400c44d0003054044a200d05000e172074a4441e044450003103400801c4c01000f41c81d1580c449401b0760001d83c50409021001d840020 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 799159469 1250 799158219 799158251
    0xc01140d061206150305070b0304051002040305010f050709060e0402030c1b0d0f0f0f110106030203100222140904140304031202060a05040c120f06020403050a0b0a0b01021f 76
    0x700804000d40b0619850040745000b5058502030f500c0c81c500307245000c404001180d00081c14000701c0d48803d291aa594989041882c1032000312441055080e000080000c100101580030460019081908000c81d0315080012101c518a9115520004050402c46802e5107015401540c10070b22468903030303251118042200a9011010700410100d0b04080c40002031325821104a00300000e01e40b8002c00603015110024124048107c0d2003010844802400c1c416030409500c07000240d50000c1c21130350014100328104010b5480035080c1188040301c9409030001d842100c031710030309035104a5443c6800c4103440003800104040100305039001103041d4140d6582031414030003000550f0144494800e051203280c0043d180c0000604102c00103440c1401b044003241040750800269a00d0000306414003840342005022817440003405400c1c144002400400c101c40001c1003219244034114000c5d0547e500d040c2d401c100c40707044484501681000c1d5070b84007690501ca480c002d02401c1c0b8103001590000b8403108039 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 799160719 1250 799159469 799159481
    0x14060a03090b1503060a0b09070f0c0f0b0106030b03010e03070609020a181a0613150e0303040905090d050408070e0c070623132103061502060a14090c01140d 69
    0x200c918268103002043d80c0c20309024076031b40031001d2a0305024075800c030030105a403a84001c100341c0c20001c074084844906403007500c181105030f8001982140103059070074080c00304c80b0280310b2580420310f818148106410b060081a041c1550b07040510b06000140d1100c2010f009800412a4880192403000c610360560007001c1260a01d81c18002550303c00020b0861064035801c1c480602c201c4090092a94081e0901440740c1903800ca50b4080d4583c1014180548600285070b040310340c17600010501044034805584003034459406041100d040389810ba805a0303803841140500d8140c0c1c2c0100e030707050207e001d5202c421078214a2030340805103020b11a45a010840c2c120700400d0818140d80350b9000305020b07207501d4040d001402c1c0c01c01a0480481d43e5100c0540d4191200006080040040320b101c5160081c2e0102d001040d11942e81d1044480c1c140d070080d120841100c1000c01c1600e4a42c04060250001c024644078001040080406004400c015108501004030300039000e03504100fa02840b0b83d0b07900680d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 799161969 1250 799160719 799160731
    0x3060d1a0a09050d0e1f0504120303091a09071a070804080303040203070506160b180114161821080a0f20030301060f0908010513020102100614060a03090b 68
    0x6012a41c501e01a130900820340640d80402c02021000f4159a0311a011040610264a5000e000344d20000c0c09988a000310351041036a40002000e403c180b6070550444100e4500c03075461841c42000c41d040e8041031040503680d150880d4080c450034424521142500780f40410340c3c0b203e19040410503030721110b55a10a0300300102e03980010003400110701301004010050681100c0003818805c1a944200002680c814050003080d006000b1034001c40c60783c001c14160124a600900290006e08003860800b80e0039200b012044182c043c003402c1840c4907141c0c2e0240640b0f0381c1c00f90300403140b0300300f14880448082c1240d5958040b60754808000650880000c1122265648600c540b9843c00c4502802c540c1600034019400c900011200700010300c0841181d0640380a400c4c4410311000032402121a10342c0c0f50031402140d03103010f00344903025442940b0a550f1a2007607084a03c4840071000002c1590b800c2c0c0300320150540c1c2c0c0d400560312460540301820101701c0c42d10300000e074408903840710203900350b0a89407 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 799163219 1250 799161969 799161971
    0x305031f0503070b190c030f05250807021507030c2d0c05011211040e10080105071d0d0506060f01020a0c0f05150403030219141c020d030605030303060d1a0a 69
    0xa00d0200c5d0000140c0104071a6041c10b02c00a030045588000e060580e0350b0f50300300d0401c00001000310510b105440340240001090318210540d0003186414151944409002d91140922141500100609101321083c0316855501c01460603401d65030b160102e480d800d110140ca400c0322400d842e80400860302c4503016805200301a11503454000058480045c2c050105001801c0214010304231890710201d40403202510005892030f6907004c6006100c9120f44c21800c001d500b030070140702d41d80c2d80c401e1000c41c0c405a210300055a01c076030f46d41007045480da03a010041050700070800281461400d88146a070b000c106006a414248440c0e0361701c0302d4050203401a5501100c0d070401400542004041c5001400c1c01c00800c3d85428115140070f503640981d505075503034074480401040d08001058080481c1c0340e02100465074541c148854000100301c81445600c014403d8289481c8801c1c468010102295400b402451658554005100d00f844114809a9141018040c50130040d4207985d1442d109484120f0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 799164469 1250 799163219 799163227
    0x90b1525140d0305010512120c0c03030f04060807090503060f060303091c0c06020a150c0507150c030f060b0a05070831060f080106030b1216080f03070305031f0503070b 74
    0xb0007900712503042c1c12083c0203010a00f210a0b411200140c1480741400302c030482c1e920f80364100d0744c82e840c125103071000c903416000c046080b40680365114081c04c141d5915880da84600e50325044200c4030b207640ca00c10543e0540c015008210400140f050050300305e140034081d28a01910140071805005941c41e0030384402d0a10389100d0203001d00002000060f00d507601c00740140c00183e0700c0310405004a0904c01100a0361003c0c41c900050040003201d2469a029581c102c2d09186914014020140154404042410001d16680000f110301c5008162180a00002e0a0011419045409400100c02150628000c2040e51540c0507a008a0403103100c0b5242c094080c40313200700c440c03d40580c442c1d00030307014003c0742c403030455815400c040e0b01415240c040c60002a600c0501001035140d00c110b0050250070300a0714502d000c400c040c1c850450550764880200d8403007841c143d80c0c0d80e989100d0703000301800040042c000f0801813140744071480d503440d000b400d12410b080c1c0c407400040d007401c0c9141c1c80001401e900003 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 799165719 1250 799164469 799164493
    0xc140c1e0c120d020601031202070503100b1c0201051903020f180310050103030801150302070c061e0503090c010503041704080c131b110f1006090b152514 68
    0x60b12108001450070003900c910b0620030800395543e070041c0401000b95640c00c2c24015805d100700000001010000d00300c0f0f1040c100350310b40c0401000c2800e081d0f40944401c1c1402c0c182036828122480310b469040c0d542c2450010300e00380100300c0b2401c1c0d0203140304241d000c224010741c41245001810340d003000000b2a200100c04201018504010f14400c0030f01c042c100801000801d401820880c119490b0400f03102070b4010805084009118516000300072004104e0003051203a44140c0840e0005084d010f0504c0c2000c5e1078800f951140400c0703481030340c0396010300c0b03400500703502c00c101958110344500c40180c5641c07200c4803081030a0b0000c1c0c00c0101c3c55401025000301d030b031820b480716000e00490440100b01d541e820754015400140c02c840d080d03062003103c2105003039410082290003208140c25080d2503211034800103400c00762104d80f0500300400c0c28940303d5841c41c6000301d0300108906c2c44080c010703d00010b4610907440b40c902c0f1056102072001001a0701d000c80c0c01040ca01c0050680c801c0a4018043d50b1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 799166969 1250 799165719 799165729
    0x20d1203060f0f0e060402090418020f0d05031e1303050a060b0a0608072a1b0602010b0a210b010b070210111203060307030221010606030c140c1e0c 65
    0xa40c042c0d084100c1400040000c1c521600300c401c10f6036403403444050540d88840c0454041c3c8110486550020314040000701841e44d030000c0c91048902c219844881c010030042040a101e6002c1c0300500603030000c105c80c41110980140d40744001c0d045c1ca241c41c0c100494030400c2c185030040d50740141c0e45500985000001c2104a2003a00d100b65400c480f10340140b0706182004140c0c42e00204044c081c4442c0000c00020900d8041c2c800c5020030000890718404202443c2640107021120240921804d0018001ca801070044c050001c1c0590f004d040c1e0740c001803524200c2500c000100a14056035082d2880003004600c244000901921191400f5a0750307040a02c1440402c511202641e0204100117160000386880810246404a00d110307070b2079104e48881d000a4102000c0b0350001f0750040b01c460028003560001c0001c15403421310700000704001c50b038a180076400d503600700404000084d1b6142035a081d00079088040d00390a80b000c0c00b01c52040320503c504c000c260b99082c078400b0544d4848a68800306242c0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 799168219 1250 799166969 799166981
    0xe10020408030a080a06030b0f0a090204020307050403030e2407030908070f1410120b0604050306011d0906060a0905070e03060a060f08012901050c06040602030a0c0e0102071809020d1203 82
    0x2d0008100c007c1c615110b0510162024000c401c2c004022004a1352600e0706c3d401111100790014402c5540b402e0200d00074011b80d206100032008108142c0341d43c502031404821104544214000c0044218003507041100583d01095044041c4085c440010038264001c00002001c0c2440303c004002850800c80881c0e90b4100a000003071041480c54080d40c4501e03030100d200511849412400318541d4100d60000703003035010b15007000f60107100e03400c00060800341604003501c01002404050145484940440381c54160071542d881d0425140a0100302801300741d0b0080f6803200f05c0c5e1406c4c41d28000300100080c1421000d8541c10131540d15118240706628044c1c00000c010280c1e40001c02661079080c0980c4090601020020b400c0c3c008480720707000590284040b0b4024a000d0000e03103142d4601440c2c000b000750000c0d21080459440d102010700d5403070194802d0b021044050b00280b44507442d105404040d174079021058070030151249004001a2105500e040000d481580030091524901c2001011142 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 799169469 1250 799168219 799168231
    0x10e071a1209033f070e10050c030d0507180605070f110d140f0304240c0c0306020c0c01050a050d050405071706091216110402040b030c0714010510090e10020408030a08 74
    0xa10041881181e54010406c00c9804009440b400c1d100700b50f803502980c25002e80a0b107070100e4040082e281c401c4818075070203244912840e40b1080d0314a42e07200d80780c541c030300078130f02030600130500810005012a00c0800d11a100f03e1061245040d00f020040204210101660f01110720302e80c12407544c90042003e1040035545007041e13005506041c640603c4550b200d588803a0410300040300c2418406081c400c074004c52902e50071900411849a59141104c02036006a09564a1740100d6414032800e41c41181150850040c607a241d604180000d0744000003800080e008aa13a4402d1200c0056101001b02e080703841d2141d01006481d0710f140c81001a070074844403403003660171079400b00254030040300b80342e0f80e04c40c0c1a80c1120424250001ca400450000d05c120307049908901004420401030030311030001040b840d0701c10116400c0042e095081c1b18280e62068592a440503a104802e2252031080d91000a40d000c88004540c81c030880003103a11304a0340b154016580c503801c00540d442456030011090380d0020303 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 799170719 1250 799169469 799169587
    0x9150f0412030c030212160312020c0105091006350f12130905071421161101050f15040f05090109050d090506030f07180602010e071a120903 62
    0x8805090b001200081c1e860005040c01800654203c452709582d0540d03440500040080040b4100b0703a901c69030706c1c400c1c07884800c1050f04080000c40c00c11400f11812489046925161b40700416900c001600f43c6052464842d5a200e92510300a00360010400c078182c442c0c0c1000400e540b0044204038050641c400d41003040c00030304100034401ca056000804258255000d88546d890712544070440e50039000100c249681c00002405100d21203205c01801c4c803405680e51900902070140090342400d0380e0045420721051304090740010804c40c056500d0043c13070ba200800014440700960890700480b03000356503101441e0b548000745401c20000f0001e40070380c01c075941065040e42d0304e8040003030303a1440f000345048000c02e001070100f000540079250b401981543c1400d0b413095a81c031084000d0003840c1c5004103554912a030310000442851b46c0d54180d40c1c1416150000e4945142031080d42d1404001801c41e1b4440c2c0b00070000c01c10101c081d049060f0b0702c2e401032154500380c400550b00010300109402203002d051 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 799171969 1250 799170719 799170727
    0x20a06091b0503060613020f0409060f06080f0f04060b0303041e1d1501051b030d0f050106030e1011070b1f0b120f09160605030a0c0509150f0412030c030212 69
    0x1951141c072000510320302c0c6c04000d6519010a040c3d03400034000e40c1c0c082ca1100d814000049031004500d5100f109980d280d9444005690311391040550381c80c801d60300c40c03120034001004200840d2840d0010014600c024040301d1509554a0120480000c482c01d024051a02500e042c080d8460071800c0c2c40784820000904103050034030160289941440c0054030781032123030000b111440274924000b503100c0240450f0940c1c0e00c03034003d01c0b400c1000e4a189a100300a040c0740000200320719009108074481c90403408000c00b480021440a18001c04954484103160a028401d103400241c501080c10304c50f404d850001e91141c01c8100100c4180142a040f1120814091198500350409000f10a03400780041120841c29110812103606004400c0903081420711800c001061494100c8002c0d40120041030313041081c1d15822400f291680216501541e2003000d4034820705e000007200000d82001004101d1b61481c00f81c1e207403115264030301c11002c1100030030400c1500401381a018045800c4011400ca800c80c54 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 799173219 1250 799171969 799171981
    0xe0c040603080d050402030a08120907060813200a24050f030f0411130b0a0b04030507030b1f060f20060604020c0a0606060806130624020a06091b050306 67
    0x1a0040b050108100c503611000030717040d0340d02004460922a00511220340c0c90084030b0791007060403000c44000585100300c060004200b481815100d10413101280c0082036a0b075070b0307541c9108207030100c00402d01050358090701008941d00d20b1100801094408003025152000c1d540010017000c0daa40c0d43c0d028401c0030311403074000132280300840743d0051004c011041541e540d89440b00409011000c0c03ea00920750012145540c0400d40c404249104101c1d160b40e43d2540c0e03086101c3c0c0f0352007903001c001c0281d000352000300005039091002d10741210551400d0b8640440c002c0380c0010f03c83c0541d01080004a081c0018240c2ca500406000044418150580c04c03000d241a03c85076a1200a800306000d50b43c00501481121000c2c0010b8110030303803006040c0055945c3d120020040300703090320001e200b6800910100408901442008200c4120050340c50441d0b5000e100c00070014000b82c1c2a0b415801400041400500c10f482404c185520481d14a00c41086005409800442c182c10a0b800313035000d6014402 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 799174469 1250 799173219 799173233
    0x61d0709060207180f0f0b041a0d060522060c0905031b100201150803040501030c0f0f2a03020106090b04020f0f0d15060206090606040603031e03060b0d0e0c040603 72
    0x4e0f54203000488480e640d6001580d00148408a19080040c1c9030540f03607404071001d03401000c042034044905101540100780e14502c961000c801d500e0f0b0200301e00100d0f10000344ad0360411640f0039846101d0703500d48801042c1240384941800c0c000c541441d078400c40d40160316000050318000d4401030300104158000c00160312240007900410307038800c0c03000030b407080030b200e10035007002400c0312440c0d10088885507a00c60703c03036880d080b0f401981d02003030806a030842010312845140c901d030120756840c06400f00070f000065801080700041c01c003001140390400070320b0f020156845081b8612982c00043d0703840c600300030b020840e480400c6c1640720340d00402002d040144043e058400300810307200541e5030350030080034000090405804e51b0361040c409100008a1540108040f8400c802000507544983d441c103040008450040c00001c001c6034040b000e400c00480c007980081d500341e403182400503140e525100d80b41d00541000314108401c5841c1c00b0b0451810600740015161b20030251740c1400124295645d0035 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 799175719 1250 799174469 799174483
    0x10305010f0803071b0909060b0f04020901050d02070f061d070b1c0b2407060b01030207080a110f012f03010608010b0717040e01260304050103020c07030204061d07090602 75
    0xb4094017404c0081c1d1000c8211181e005004000c00d20041142d10074034604840503213015018148a070b600e00054107031600301402101c3c56440140c1d261490000b04076101d0009401585003562881c003500c5050000800c20f10912141c0300d00c001c64118809580b000c80352519025800170b03c40100103000905290000c3c00800e83e0b25612600702081d00c4044d040455850410309031000c800601d80c2c11030031001612200200751183c0142020700061840f0401501130f44140c410081211004021740030145100d41d60400307e013091074090b40c030645c01007042503080d80c0030908001c0c0c5030079810b40b0302c0d42c1e0391110061207041714020003420343c00c0d50b1500c00041c1400505200d59981c200e00000c0c01820800301850802004500c106640c0d00c1c0d5845002e02d4000381001d01031b4038094503643e2401c1c000804a048202c00b61b1500d82d000310310b0f280c104001180a500480185030080c46071010100050f03450740120b01c0038000655947c06850581e8180301c0000101800c00d8041c4030013000184000c41e408148130f = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 799176969 1250 799175719 799175723
    0x60c06022203060506123403120207081b0607061e06051003050f04110109030b09060f01060e09160c0204020f0d150e0c34060e0111250803070e010305010f080307 71
    0x1440e6003044c0c0d1143ca2281c01c82c031620001c241f00c8a40300200070081c0048041c41000001d60031110020b8030355420301d64400648482c501003102c0524080b550386869002007002030311030031021980858480e4803601059070145003480907a00e504090010b400e00c2545031603501441d10b0144030724140310118106090b0050406050254940b4035881c259000e0410040150350001142d0321b80d20303200740305540344e5100392072050001d400000001070452041011300c6004130000c0c00800c45407244880c0040d2000c0b0075500800740a0940c04501c0903945601c05000c1d9401c05106c59591007011882000494500c444098008050702c00705020900864034150350144a0524070765a81000d1404036074001c2000c0ca59943e400300b09110402c540301081c0d010b2070301c184981000d001310303280c0001e00b9007031b24003040e0083da0b092003c0c031019541c40010700e0458032158103940e01d10301c0c410f060348410405900850300c5501050060044140c95649840307018010a0f01400c030030340a07418248460340b20703c510140 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 799178219 1250 799176969 799177003
    0x2704050a0c1b08070506040b0f06010c1a0702070f0806040210110a0311160303020a1403040627030c030309290909150306151f09060c0602220306050612 67
    0x40b03682000440011144115040b408031090740c0303040d00c0c0c020074090317003191080f0354050390101003000d9502550030301c034400303602c41007586101d10210a54024028001d080c0000c5114000d8005040a04a031780071000d0862240544040e26050061041d00c0c86043c101804000601c0c05800b03040034041214903d02c8d605103031140c088900710588178908084221901400880c00700c0001c101900003c0c01c0424a100354152001c00f010300c195581c03680194440c1401294100b0106045401502038480028016000c080201274590326483d0f500b00c1103410480108554010900c1403625142200241100d44603880210301c400100030400b5005404504d07028603034480c00f14811020410090000c1103010b0200d031b1441c9026504029900080701100d03002300824041b01002d021002000c2d06100c1043e198018014a0b101041ba20800045ca0507030b020383d428020314040c4200e602c0d06540f090404035a401e241811350800004070f4a000d003160f0301c01c01c0f5003000b10038020004240c86036040400c0368 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 799179469 1250 799178219 799178267
    0x7061209061109040c02010b09060d0f050114010618030809014b020102040f0e071101020f04050f01020c09041403070c080f0c121507052704050a0c 65
    0x15048000e0600d98034010605800c2c8050000a002c0e2803024100f03004040f0340500c010429000168201d681c02c41c2c01c150404042030014559050000d500b501103485454042d01c440800d481c0d2070708440720b100205034a10b0011004000e415801680340d201d02040481c950442482d582e10700100d8810400036a0600c540d07031800c00442820301404090101c8c010140b0f490301d049082000781060354030400c42ca10400c1d00c9003080b41083c414401c0e03c00b50742d6074082051206080c280010001c00700240302e5001c10031040d482213043c0b4403c2c00540171200040c07020644070360903c01040f02d058069401c540c11540072900b440d0050361000e66040c0c01a400584c8107400121903c203641c2140701e003034030148c151900c62000060740b0000040309115640040e0940300403208803020401209005080342d0707500e602c800c0301c00105035440410f0030381104050034007e107422403450070b00040c20050710b8403011540e890200521fa9040c240101d41d4000d188440c1000350350702c0c0442c041d2103603102c03080e2040c0040b4048 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 799180719 1250 799179469 799179497
    0xd0f11010f2c040903020a1205070c0302150708391902060c01020403051f020406020d050d150e0609070503060d030c020d0501050408070611070f1524140d050706 71
    0x410041d6079482c1c041d0041c4902c0b442ca09002e5910300160a080300c00306000c01054607000c3c400c074140d40f42140c0c00310301d001c4041d185808004010240081011503060100800000203000c0002040c1220360010040303864410720000180301040184000d038001c0c0e81c01c03121640c000e00811007407848624410b9181101c600b13800460014012120303a08625880080c3c084240400010a00c0c4a1540341241007220071254098105070b0290b40704440140e400300d211003a5441c018005050b10702020341000880358480c410040c1280200d600c0012880402c40500495043c542c034078a80c0321083d82407492850a000c00031820701400c0d440007404108240c01c464086640d040901444c641d04007000380041e003090704000070254810306089558070318020141d044a10600182c8079059002117405001e00c00300d4403130303041a810503902020003903076840d01c88011007a84070349592507901c402c1e100c6004500303003e948400e18455040042c81030720b00804e81400100c0000720350041c2d805601d40410000316030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 799181969 1250 799180719 799180787
    0xd060510181d1902010c1704030807020f0103060312050714030309031908040c09021c06090c02010f060b0921070b1926150d0f11010f 59
    0x1900050481d50711100034604201103034000048541542d00c03941c0c000c103051011a07030744180c01e01c502c00b2060242d100b03450166005007480000700e070051403041c5001c443d0302401c609590080d001281c03030100c04101242036007003142102544800030f00b030400540341551258148138080403408020001c00162400400c0b0850486d810034904680c200ca0f22070422456890b01d0303410036038012030001240c031100c814241c8034002c070500843c2c10540d00c4140700c0c00c10345100003951200911519a110b554040001c00c41c80388148801803140f00c000107005004030380c0003400e46a41b4a207502d031081c103164042c014007100000320b403481c6c45d040380c86c4905103080110501038400b40e0482c0015900451400140049501c070041000c94490404400c15200c4c18074243c1742c480c4d0040341d0520800c0c4100303160707600407081d20525810180c0c6800500100007441e00180c004820114220b0f0b6001101c1024030400600bd9405407a104003400e00d41c198610f0554010310081c0c800c40c56038844d40f01c3c01d0100040c0114 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 799183219 1250 799181969 799182001
    0x308011e05042301170f030415050f190c201e030c03060916210609050c040204060519050403030f08060409080f033102040e01020f04030c060306080303060d0605 71
    0x3070440c02100e5a90b4608600d10040c0e0108a03000034024801051b81001c404030456080d101402201d00f11780d10000c20440e02d41d00948034210018a041240101da0345012404d4040d201040e07580c450000aa460301c50086120f00c80d81c0001750428400c0201d099a0302802c80d022a82c4884110922110030b00c0040d213401c005540321605405542c0620140d5040400d0710000c1e4a203a83c1700e444540d540341901c43c6000a504401c1c1c0144409422460000d0515041503a5060040084403c00010a400903081781d0051340181c012a00000b000ca40d40d4107080b0040d40350314181c0c10024103107132654402800e4003042c51680010441c410340060a203550b20303848004801d410400b22070326680c080c607204a0a52085d512444d55914001c09440c03d5910004410303004040001050140d0409500340009400b1b604901c14a6540074400307810540b61020160008500501050504615108014044034015004010581c004108000c81034403a600484400b84d03201174009142c1d81c44031031944803000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 799184469 1250 799183219 799183271
    0x2102011b0c031401050601020d140903070f06030204060e0604060206190f050109020c06180d18091109090c0306010c020d110d0615080a0b01150c1a040308011e0504 72
    0x44480340102c14041120780c034140c140e01480c020001910b0b49001640d964032500c1d03466000501d40d000001584044401501074060080c040780c0300c203915440121f01c24000340d0450350010340d0108003000348542c026000310715218180c0302031f0714150400340000e480301ca006044065507010303a6404070441010b507201e0005000000810049075840e501c50700040e50001c11800810311903074021840094804011031502c0c420503000700b0358070301005000d032040100e0b481c090441c010b101d5400100e904840c094120041d80b0f01c503195a5400c1c111040150410020746884200001803080013290b0b41c105208a210680444441051130700d6490008072140d0560101034014600600400c200040e64100d01522000340300f4800071540c81c0c50b046640c03080703020b40150459101c0700042101140703039a07100402c609076281401207845140c50300c200c0994a4080c4030000c002c084100b20901d50f00410382c9000d0004c06800c008402c225042c1031002e2a018019180b00e00da4901c4916020788040d403040c0b000c40 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 799185719 1250 799184469 799184483
    0x19290a090903020c040b100206010611070e36070b0904090813030b090d050708131703030a060e010302030c121009060f0e0606100309030e120f072102011b 68
    0x1c1e02e280003510340400e003c141e0f0040d4100b03143c07078044d407411860654210310207a00801c038a17031801c0021101031072901c4000d0040c3c0580f460200d80c00389507441c224441d1311000300c0b1340414024080c004049900b0200c0c40c0e51034191850186a0510b80481c3e000122425a9080390700c501c2c4a00019000300b203180780c020089440042c0305000c16000303840a108a074042c071000e241c1c0c2d5403402d00150320351606c0c00c010b600042e0204500300014480034003401c01c03103d01c01c3e421691642c6500106c080c00d100624014420b50011081203000310842c054003028007540350382d21000354510f0340400d58030380e00072801501ca050a1080f03803903440c000308500e022041e0024002d0004901c03500b0140014000403080b10401424004600300343d41c03000508134000e03100500786c20000c2c00240b104400405504c0011420803001420342c41c6aa921140e200251446107401740c01300c520404c00451902045600590403030070f0250101d400b556180703800220603074082c28020401e4481080c074040f81c01031404010030039 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 799186969 1250 799185719 799185731
    0x10e0d181d0703140105150706020d14090d090608010909060e0105070504060809060103020f0928020a030506010e0627120105070909090c051309060f0519290a09 71
    0x40c8210903002409100251810804850349521013a103008013401015044000440c03c140c4a040071402008828040c500050901042c0b000c02d5050700d040402120520480800b4080e09090500c401c2031000020304181c86440d1502c2c44c0989030440500c40c0030210b6548180c4201032028981003c54000403400080059141424029000d90014098030000480c0840090380e045000034030b090680f50001e0591002c0d252413410801403000040c800c10803484010011459019051000d040315100e10b50090f88070340c000c0703400804440004101078100a0380782041c1140c2e844903002c4410401c403d40680c00700c0c02c0e2490300302c0381020918a80036004007426091201124042d0b0086010303440740e0369030003651543c4106000070360b2000c18014103a0001c203203080009207405050600074009003030700441c24004031f854580c01c43e000d219086c0c40d800e48030b10412054400801c0030040c69580200300b042100b00a10724404109440f1560311014044000070519030b170b0342d4110b40402006544800d01c82 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 799188219 1250 799186969 799187009
    0x60d240e0f011103010810020703121a0f01030b0907080618010306060e09070f060e0411070c050123090904110a1d070c02010509041a032409010e0d18 66
    0x150792070080007080e4551900c001002400700c00000c49040741c003900d00900e0405281c2d0658002580305040840901c6000000e031543d08000340940f04003039000001404040b00e06906002002c4441c080b41410589440710f0030600da940d114080382c11100784d2030301e071420f980c0302400310b131180c254400e04071141003c181c0000104806034000c01c0580708898030034161502e03841c035440c2c1d42d90414042d441103020039203401d100c0e00f881070092030001c54004001050203554100100b07980d074810349042d19203c5501e4420300ca1075030801c455500e031b032440544600c00c00304020b502c1c030076a02508003040d106d055950041000c1c058540318002d400c05004003403040242d50744a0101002148400c00f11808000078006004140200960f4203512380613100e4a203821418810800108000000030000d540d96090404041d20300b080303480f540409002c00c18450b848034441e5030515010060901902d41c0c1400490241c5580c00b084405042d60389003414815480348460308001420160000300400c141d0f0100404 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 799189469 1250 799188219 799188223
    0xc091314011805031c1506031a090112030f023f13150206040f060e10060609030314041401081806100e13050d0e0d06090305030403110105060d240e 65
    0x803c0e2402074200b422500c0b03019080041c0d0354a901540b060481051b002c024a5010342c220035055007000c4280c850008000000031044803081c2c01028050078502c0b055401c1680103444242403d0042c0020a07290300c1c2d2440c0321494096850241a5142c030b0840d40040d0b12080fa09400d0008202c22070068070b1b0300100c800144c281c1854401c0c0301340034425180c02004203001040f540c0c040c6422600003d8000b200f0b0321154058010031505c960144124118500440c0c1d0300d00c13604010700825030320300c20700da8a5814001c4c05041030f1400348481d42010071040001800119040021403c00c0c20000702c1591100c1c42c00c02c440760810091100e60150f0030420404205940201058800c0d0240c0b420807a00c647c1400090310b02480001032031680a10100344c1000e005807940c42c8600e0008000740c5120385240e450310180d5a42c04c01c1100451404030601040540242542d101c4004040c020403061600780d0000b51103092103400134000c1c54054070401c2c00641e4681800040003840413080c0610310040c00059 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 799190719 1250 799189469 799189477
    0x3050f0703020405150309190503131406070b0c16060501060306080a0b1f03050f060603071a180402070501050906040209060123090d0b0a020703020c09131401180503 73
    0x105140204200103228580a4401ea4098500107880c0c4441e107491003070000366a44c006000803200380728844101c1c0c1e582c0a0790704e44c0b80c06144a9030181d038541c494509216000308050700810780d048071080d140241c03a2a1501520210385c1c000b81007801d15192000520b401c1e2282002c41a0355900c5502d000d0103001040e00500e04071a00d03560208890756403003220540f00d01018000401d601140e00110303215662000301100c00302c0911502510369541d0756241860050148080c10450b081081003104c50310b000c1c440c1c103004001c03190400c42092240c03071480c1c01c1803040c00e404d51441c80d1500b00d5105661560741c10341d10400c1d480f1008006500b040c0e030790a9501c45084500b02d204c0c0c022a00015002d500ca5400107840715446041c56420155004003410b40e0b4115030100b50b0404a072140d071402040b580c507022801035a854400683d90400c6041c02406d0610600640c0c2c003e007442c20611005030700020070701c1c480700d0b0800d020103400e400c00542c080c09020290351b240448584251070006105e0040020 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 799191969 1250 799190719 799190731
    0x3030213140a12022103040b2d0406201e100b0f13091502040e040b011d0c030702161508092b0207050901140301150e01060e030309040203070305 64
    0x840740140d0380f207469411a54805034000e40000e0485a040e600c030340b600500b0117540213110300b96410309445102c042c2aa400030300b01a210003500c4420404030001c01c101c1d207607241001421182c9003070b041213405084002d0b110800002d003aa8607107000007486d4140301d1034030418050070881d81da45000759a0300781d9401c546290000d90f1071502d0a4008145440c505059112101034280c200024220000c0301c024000c03010251208280d0f644180038841142c401071019040310206401d10307003000e0070302c58130384041604010201190104003002400001003100e41c05807070713240100c2c0e8981e66944201d00b45000020192008a851321020038802c0d01c40f544612420a5551076400743d0341c0d4000c0d040da4a80800ca06070780c070104106490040c0500081e814182030701d03240100c4542550303c4012800c0e08200764807110032610201001c0305185428010604580119101c141d0014104000b1100740c040c1840f0b00c8050041c0189107810545007481500d6041070f0041c030441d01e914107180043c014100460307079 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 799193219 1250 799191969 799191979
    0xf021f09061a01091401090e040b09151911120c34060c11030c01051504022a0a0803010b0703090e0c04030b0a0b0d150c09180203040303021314 63
    0x100d001c40d4085100d0b81c0c0110300c4160341d0101c5580c581200240c00348901250141003180d14840172883d2038240010383c2c0110b115051142c81c034500741912908000c400d5a20a41c29129a420b03c440103a5408010324980340c3c2800c00039036250551203c411621401901d8404420140d0800c408d10f0303c00d00107020214090019507175500389883c020100c4060814800385903407039030000d400c04220250b000b189145428103005040c3c04070f825007245142c1003d000ca0015a441c0c2c0300300003c1152908141c00c05040c1580c056013040d4000b10a102501d013031005a9030145a05040404400d004100010a00e034209031115a01c2d41c6400031070039282d21660f000c1d004521132150018040c201a00090f00c2070301c15a03140f60034242075984c0d4004108014000791001510382c00012800e6441c103929241440c4181a44002c1c0b05c2e040c0c03c064103640b0041210000c0c40540f00d0b0030045d15120480d009401352800e000143e480e44e441c07400303800034002c02c8900c840d10b0346209008601d00300402640c80c0340a070100e0f0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 799194469 1250 799193219 799193231
    0x901090606050d150f0e030d02040504060f08030319110a020c03060106050c0318010c060c1d0a0b160f06060f030506010e221718090a0911010f021f0906 67
    0x60046000e06220001e000001c0c100e90040305601c02d034019910361103032403001b00d4440310202602c2d1075600075503c0c0b2400310382c1c000342c10001c91034240b081d48010316151994004041c41e0000e0b15031a0702000f0001d1200d030404200d01141001513a101c800380702100c0041a40310540310030002d64640101032164003a00c80c01c40040340986c055000d0302c0014020000451401b240480c190940c808070000160520951841a000280d1940a11840080180d490381210f01c0c1482001900c95080304055004400c070350700c1880512051000c50f040205403030446000c0600619013150b1007044910046e1449107450008a0a501c15107201d10442e8001c204648050f41c030f500010900d02400d43e600c2c81074420000059044800901365040094024004d502c840d4900320143c000c954800c40c085180c980441c420410280f400c003401d03681240e11b00380100161145c903910b285c521600c2a14441c1400305c00408500998820802c403501d402c020090038010300c6540c0d041d40013500c0007050403145039060039 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 799195719 1250 799194469 799194479
    0x100513031119120e090412030f0c050a030b06040302130b0120060105221103180a0203030f0702190306020a080a230711030403140c01090308030415020705060901090606 74
    0x180c40240c00703071051040149509680d40e80107084140f10701c400c040c800c5403aa01d8400d07681c1d003108103106902420403002c000b8501ea00003030886040d5001000b083d4507018518484c99071007019140703c61100e04000407000542d1002800c02c0c065039000a41c0041c403c0064008601650041c4040034400e0303c492a40c801403180b40000203610700d002003040d91200004010f145003c01100841c1018030103103601c031640a01d0141d0a5441c8000d1600f80d200000050103040b0720a0580b103100500440003a1220f03a584c0d43c0040c1d103d200701081007403911000f1a10006665424031050148100211aa1615a980d1601001035085914004003141200001a51070351650081c41100c012042a407810b000190780302c00f8201c03002401d640d040203420180e00d4824101080200301450040c00c02c80050103000240741c0c60003041c080404c0c10083c45020420006d9104800d898100d607000d0110011100d04102240c001d000d40712010300301c3d10a100500002031030651140a51900410b010b0090326169 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 799196969 1250 799195719 799195723
    0x20f0a0c031e0f12030e060f1501090b03060d032a02040f02030108030723070b0c1006050d08070305070804090b1e01120e01110a050c0f06060a06050307021005130311 73
    0x80a000342c12103d058120301e0000303140440e0702801c4030307150900040e00310549842034500f04080300e18441030f4003070301c0600c4440c902001c0d0751110484240b030115403090610850b034445000160005004c4c0c251070000100305401020030b0802e40d007003020300c107041c8040d58000115250785003100741e008a00c2c04484011024a41c02200e059510540c0150718103422176503402c010381c0b8071034403081c640040440b02e103640c12001d0007448010a074101030551500001120304d4245009501d9143c11146042800c006589400105a0042c2d82001d5407546a001500f005c0e02d403032060010040103420006000301705004180e1000d6040e95059444081c82805900d0001e014102140980d005c18003c071115464207003203400c940c40b99608040080307580072100101c1c4445800036540710000c203c1c0811944074481d4100000c0d18161068001040c4c43d08041c0c2c045074001301240184010440000b0000c2c86d84e078020030001c41c1f92506000c04021320314100760414000c440d0340104400107107200c08400211000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 799198219 1250 799196969 799197023
    0xc0109121e1704060e0601090b03060a0603020306010b0f04080106170d090305060606131205280b0103020d11030a0516060c112205070807030b01050c0d0807020f0a0c03 74
    0x100d03190060400164100c034001914010004c840340b9444c0c03562404045014461a40207010489000c00d00b0040d0004250a02d42d0003080080c400f0300c1c000b820009039500141d0141150508203a0a68410b02a17441d025180300c0d54024000c17039030030640000f50743c40001070380703100c88003030030096604820f0546001c030344208161201618583c4040301107040d03407400d84001e1400c502504000c903104d070b43d52a080c0100807010b01c0d09480b203400080642005403400c80765540c0740c02040c01301044040d1240c0d00c56406c0a410301010340607800c4180d64030200080c40651107a1800700078101ea441c3d40c00d9140c41e42c0c1d0796218444d541c491034485040095558040d04042031910344c000780b04412400c02d0414017640500d10380310040d0f10090859110300c00f0345c4511031b030f0303000d02001c0d958070074245801203000d03054450340c401143c104070041003050b010034400300c0c4103141d002081c03810481c65140d042e000c07031500e14031605142c00e50144501e01400c0201030207904007142c0c1310325800540c1000c6100e0701a00944 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 799199469 1250 799198219 799198277
    0x8070b13062a21021b090a020919090e0706210b03010e0601050102010e030a0504050f0301090218040c0e1e0709080d020303041211070b0304060f0609090308091207020f060c010912 79
    0x141c4d10000305c1c80c944125015030002c00084018200740c1c0250004440e41d00104224021070001002403098109a0044043c5040308030f00a00a41f407403e00700810001e5904034000050021502207480154a40c003c0030894800070004c0c00000904250691118020b10406000d036180107030b8940e0750781b00801500d604001d686c0340c1c14102450f220601c5503454040c0c2841342d140d561019010010ba03111060200c43c6107200b16003415924051510000000c0160400300c0c41051400411050720600652611000440e642281190316442000e03220b203050b0360056141d902903485240760503640007025620850250711203048001d01180b00f91100c0024607110201c9800c101024041c00b40401c00841d046449103000007002c0d55556400e03821500540c02403c0c0b46501c0c4d08040013030550051ba840c1c2c00c01030302d401901c10806043c0300c3c420b483c031400d40000d00410106900d00740b150341c1c40e400d4910a0f01042c009220744407032407800341c000111210400020404444c0d0040c200e0303401040d00c0000b12 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 799200719 1250 799199469 799199503
    0x50f18041d1b03010906051003110904020d02120708010203090a200306060919020d1b0206061f09030b040602210c120903130f08070b13062a2102 64
    0x71900d41402d460301080441c00a40640d01c5000c4c1c20300013140f92044a2188c98807450042015095182030b021401c0c182e0280d5210750501c1c0c0a1102580e20511240c0300a60f048903542006d041500c0070608150580e0300001480d480402006a240741c0819020000340c41507408003084800150141d4150400d451079a80543c0000001075450401c12207068001003c241b0300e191041f6409080b074180da0142c0e540211007902c0d030701010800c0343d0182003201c99003800c1c0054a000d1400d400402c01203920742c01c402c00800b04582c04000b095010b004150080c6070020648035040c501400c1400203540a5410003240c3e02c8a20a1b80704800c00c03140b081c138044c1c1c000d50b408a180083c1c1041c00d040c01c14014006507524002001504020b000c1414039000510341000404812032504262601744081307503103d9a86050104540e468080380d0203040426560700d8100f48001d281943e08901c10203944500c11030890300c00c0002d001c10300803034200c0364001c061103240491403c844280c0c200c0e110384110300400b10b22 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 799201969 1250 799200719 799200733
    0xa0602010209040f093311040302090109051603020a05040f030c050a0b1603051e030403021f020f190e090a1b03020909060d02150f1b0703020108010b0307050f18041d 73
    0x2c02201400d40001070291103030428180b60b08584001221f801135803149a01c0400902041142090340589004000030b2404203e20300d4558010a20303041c400541d0420154001800c200d214024400e54001c2d103040039031851025103d01d42081584254040c00d841000c001e40d000030b60b16002001c0f078070150f807411003c4040e980f03175035401c0d18603411240d42118100e030120002019a019400034501c628025801854160f95100070780101d442d5000d16951424010007a031481d0080c0b0310125080358140202c020b401c8444000200d03504240700b44c9a551000300482403090383d02d4150080386120142c4040b82e620010440c40070350481c843d4601d101d400c1030590000801c0340c030303161500d601002e00241020240600f08241c2c180c9551044c2d150810000f0042021135040d51829042480b00c248800208191411600040c04100c41480341e1440d640c40040000c02c0d42e845503088e9032003003e4855240e41c1f1400d80c0858111030785007a60549018500d46208600710130600300302d02d00f00e10010000b90440d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 799203219 1250 799201969 799202003
    0x5010305210f0f0715020a030c0f021f14010b070308090307020108040206090d1205130f03020904140a020406090c0e090c180316090c0809070e0c03150a0602010209040f09 75
    0x295422180010690010620910022941c0c40c1100d60601e402d0f101c0041c5d1f100c003034071390180484406128100070010845100200030340c00141510402d10101080813940140341c410b0b80c0074000740b500000e02c00388110b000091181c1c440c80600002e621030340303d20942da9600b5102d942e8038041c05034040d00140000f400b040150401900809481c1c1c005044540310554036141d0800b0410400061400510001080203440910704404406081054514400c03185035400250301041c0c0588003503c80d402c408964407164908201030502194058030612116984160307100c002d0142d58185070100d40d40840007060340c40d00040a0303120f114007a80720740c00c101803154001e00f00c40c0360042c607942501c10010881d001d5104403d0582c001d05201070f001ca070059040714020501c04020b17006641d5070384092414032060740484c40d020b5010781582d0070181c032640e0381c00000200b15000814a50400c00041010071706039410f40051035403590583d014071048104008030303011500c001e03030050400d060280c0c0c5214 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 799204469 1250 799203219 799203247
    0x203070f0c030203131701150b03040615240809030a140901031e020d0b010c03090905151e0312040305070b07032f010c0302090d0f240501030521 64
    0x1d2898040e104807400c100140c00e021464020a81200007001ea407841d0303854522909014843d80c09141d00081a04540b4180d5200701c035000180000b01850780b28450201a2940d00840f800144810380c0b070071503810261000c814011141e0742651300051082c400050000c1d60000c100c0d8074100081c1c1d140c158800c16140020b440d034015201203810544c80303410b47c0c5c0902c119612102c612401e44103005079903045140c0b090085800141d11141802044481c1d18042504101c40070708481c0a60b101090541d1a603040100b2942d002c401503034806400e040c899141c3c154441c2c0e040a9450940032140c0011034040640d505009a1000403c0c55110110500c01030903180050030b00e00e4402d0414040b0340403421943c40c1303000d00ca90103546928968001085140701c1c01d00900d0403c809a003411890021200d002c07400c2c1c205005c0000d02103403030421000301000288080c0030800e840c1068081240a401c2d0b9001000d04000c1c88256540d21480744016030034400c0b17018040f1141016816986041e03055903c0340 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 799205719 1250 799204469 799204487
    0x30c0f03050a1e020414011b080307090b0a02160816260d021c0503040c0e1306020307110f0f030405090406150e0601110706210b1018090203070f 64
    0x45051a29084404a640340c090b60300c5a0700c1c40f842002507120350a002d00c11002c00140c03803520703040140540310100001c1d00300e011a10380c2a0400300142d070720b5032070810940e02806182d04c03241854100148103e204c49c0d0201d409140c4140031041c4142c1c059a543c1d02030307a901d101c1e049404281490304410414600300011071a100b26107003100320350400c00301003110704001203c02d10074050f070004941380e42c20104010028201c0c10390f50401a04504017038681c00344410140c001c4a84c41e902120100e4100d0710320071458000d442d44601c007590749280441000341080004441c0301c51134802c1d000d002c040ca01001c10212402c24806000350700301450704c0200190104c018000b0f07554282d945d00d1641c20320850764000300c0a40b90948816802c1e0500382e00040030803910f244480f80d140c102c00000e00a80c0c1e44181912840a4403200031043c40d9407080408005010242d000390b07000c080300a5014006401190070482c2e03084109580038042d44d0f80d20385105038401110240009245c440341e8541141c0600005 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 799206969 1250 799205719 799205731
    0xf0b030d120b030a1a0115050703030f021216022b140c061006090b18150c0a060614031b090a060b1303020a050301060b070b04020d0209011d07030c0f0305 68
    0x10440c0b00102c40404c1c01d000031200c040d02c1d1500e250311041100204a102c3d0b40c01049031608211035400c01c40702c020034500505c8801402c25450340700c4241c07040c0c0180c041d24400202142c07100900d04241140b180a0180681124054040c605a601400803803400c510035000e5200c2e890804142d544c141110845125039042c5036400081c0101c51081400f000b48a02c82c000d5014070300c2409040c0100501584000e603c13118080004000360854064801c0410031003ca0640300c0007082c031007001b6a00302c14090f95510300d0486c883d05104009000d0150000001c0300c9442c400d41625070207680c2410744855032030b5964901000001442d001a06202d184140d000c0d4110303200096a94541c141c018040e402117014000795954408280700f58900040c2441c01010f01714000c110240c6002c1c2c2070100c5018118001e456040d02400040035500c0780700030048200d40c02400842150386034542031505010201c114040040341c1800600b21500920a4502c1c116140e1942e40d01c03105032040c21030181000820b4 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 799208219 1250 799206969 799206971
    0xd020c0a14010912051011030601020d1107090207030801030c0614030f1b0301030b1005220b15030c13080307031d0f0405070c03080a140106110a170702040f0b030d12 73
    0x200013a0140c40182c440300491042c0d014000440c0da542c040000c0d540440c40307224290f84104148162681c000800302c07484406400c040e40300900c001049402d10650380c0c021305a031030000483d6420076074080510b905892103085011400343d00d50344110341c3e0481c04070300c14038a88410404900003800c0a080643e11148091602041c0c00700420081c88070703002a0b204036402c807808800d116038202d40411340c101401e001c2c0c80c0c02040001090500c4030102c0c00301490441c0550300d000518480e00d80424041080542420003542d80c00c000007001d0700f0790702002807904400300e1000c1c0840c01401c0402200d400c5030305940d50305511141d419011001e00890b0014903480f00341c00d1102c41c0d541e100c5001d0184101d206e510703200da40e20001d081c080d044020061100c0001440c10104000300503850000905564240c9007100f4080c2c40c81c10044e00d854507084020300541305501d07000d00d000280000600b4103c0c4243e03420301048211040e118150f1b03142040555060308420031b90010303144034201c0d199040320700c518 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 799209469 1250 799208219 799208237
    0x50a0c0c0807080904060b03040b06042f0906131707030503030c09060c010e010e0c010c17030603031b0106090f14010504200712020706080702030f0d060806070f020d020c0a1401 78
    0x103003250705e42c1d480740d003904002004000502c00c032b00030681e07400b1005580a2000d119122503100881243d1444408242101d003c0308041030350321016542c05060141c0013640d1107549912200000c1054810007119000c0ca03c440b4000c01c00200b400000c4941c841c0044d800d641b1000c0c1c100320141c0110107080d070011130a01045204200c24003a10281021a200000c1e0000042c004142040f4196000d141440140031000300001c2c00488070005c0e50380040182c5480f43c81d05070020b401c520401108100c001070307410aa01c4c041206600c4a000c5414521080100361801507150041c0d07152031286d46840d0324200d0042005082580003422016268042c0003074800305404484050b42102d4016600864203003401d0059580411400001d8540c3d801d18189600e002c0c000255203208454882c1c5071a403002c80e030040a40e41740d0700200301078600b250640c0d041e03140110004041d014050403d41c0144505030701046080c0c00400d400c0400040980805002030814001915100000b00510304001e4640 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 799210719 1250 799209469 799209487
    0x5090409080711090a180f0203031b0c0102061e071d0303131802040b0a0507050c10080901060f050321070203060f0a0608060618130c090e01050a0c0c080708 69
    0x1c0c00418000f8450041c06482071003042c180083d4120082c500303401c03146401d00015003007008100302e410b20b40e4003001003c0070300c00600c007003030842c00350011041000c1c0a5032110301c40244040350322421144c0c2a400ca9400e5a24900140c480010510388000360302948d1010409091060302c00c0d5058003494a8800782c981000804a441c6a2120325044500306500506100464041001c0002600440000e50a203030600380600307405d201d907184030024444005403c0d410041c00f403180c580e110304010302c1940c40380c84144000d081000119800502e035481c000c00455690410a00310060b582c0240007060342862040032081100c0c0242c1e06c0d60309509085c040140181d03800c12102d0303c500d8581d8842010f81c10080b0028051f03961682101215400004c00c204181d2102031681c00703070a12003407000000e81c85081403680174204600002e80f0b03201c0080c2d008510107420390007102ca045040c01c003c00455079004110303011901e03000100c80000f000082500f01045840001c0d0400601481045140c00c50362 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 799211969 1250 799210719 799210733
    0x1914090d05310f14150928050301050109021c150501140c010c020a1505060907030902131422110d0302070806091606030c1e230310050a0b0a05090409 66
    0x2c0e0300010380d01303904000e612510306116807140d00f440a05071500b420154020300007100714104070f00ca03920b00e031900000045c0c04698034441100070b100150082140d961540302e610301940c400b9182c2e400041c081c00c0f0b1000c2e2074403644241e4540000300c054102000d0b060900445807040041100c001400d428481408010001e03c91481901c105030000e1aa1030310902e00640307084c2c040c2c2d031480d529038640002c111654460541c05d030740c810107528000590803000d10002d00b04003c0300502101061500c100389800c12040301d5014000c21628100780100903101c02505403035090008002c11201207000d0100e00750904045084400d0320030700544a0841d1900000b900c0c0c40c0044901d00c2a9901031601800313011607507d0b500025100c1480d00380031085110034060180f4688040d140b21046490b40e440c4061841140341c5203042a420350482c0c02034156103051141d5420030307600d90b8850006a24005480d14144480400300e601c81500f103414206044821780c2c1c44d400c041a125081034403510520300040c08 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 799213219 1250 799211969 799211999
    0x111030906180102062401031e050907230f040b04180f120e030a02010f0306120308160807080a0e0a120c05010c0f0c02091914090d0531 60
    0x9001c202c0e00ba0020035000092510401800d10b00300704906008180349074081e0103080e1805107080c280414940040d01007030305900320b1595400a0203182400b840111440400e444040794080910344e82d01442580541c00961400152140c1c00023000010104d1402c060b085a290100c1c0100006100c5403a10b001e4100c149850204940c0c001c0c0d00c600c2c0d1820411001200c0060303082c2c0b440c080c0380d1b415907000480c0d41c6050f0a40040e05101500a12014007440ba40100001c0e00c940d8242c202c00e01898900906461010f45d104945c0d00034100c2042c0702d1500c564a4544a0000340c0d5030200c1d9526210070306001002240000c000ca401000001ca000c1150484c016240d1100b540c2c50340d419150700e041c020300312860f400302082084004601d4000c820303030003a03140380c186404644400340e64841c03071552222182c900000d0310089007403e601e904988881440140b1a02d15001a41d210075140c40b800c031524803d4441c0200d003180090f880405c0c1017001c42c03074800c020f101c04803200c1c41d041e107030100c400d10114 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 799214469 1250 799213219 799213237
    0x30204091a04140d05041409060d12030603030e0301020c0322031a070807170a020c011e020405010f02070620100e07091112161b0605010e13110111030906 68
    0x20001d00c00c640f0903020031144841001c0e6180a5080c20f043c00a4004203040c0260294412401007010070070311f54490007080c0000303038813024102c2582808000600076060703611054004c9520701020030710505060084800304005400658546554940c01028082204d0070f280f4400c1c23101c10010000828040b64070300c005040042100702483c0c038090080642c1d1008000004004007501100165402001e98541000960101685a8202c11041801481d90120b03058146900c2070409003005e606600404c02d60b6000c3c2e0300c800c1d004d290400140d030f44414034821500003410070710140642600c003c41844a00012030190b40545d010a48800182d8000e041c0d00c200a80210400b0001000c0d24402d083c00c1ca100c820506050603c0c5038079203e4020340081683d10060750341420511018801e00b074083e0028926800d0780041840b90030301000905090140d406d020000c5000b08071102481c51817210300700d601800d40202450b50000445400320350801188041c401403201500c99514800035020045c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 799215719 1250 799214469 799214483
    0x45070320040612051302010207030312230a05010b030c071e0b1f06020a0506060909120c0d0f2a021c0b060901050603160f090902030106050315040c0207030204091a04 73
    0x5801d2615403c1201c1c4083c1c03044c800c419000c00d40744c00507600402d03810200c80c8c05040074088504000c21140140990b2901d0008820324442002210308280810700c2c0564101c550401280e030301c981c29130360a44010780302e418030960148150380026403c0031151400e045600d4071041c00c0300583d40c405144c0e010646001404c460031141c402c070b1a5104142402c002c03e01440200a480c02c1c07512ba450711000058001c070301440f0a00d00007821030320100901c1001041c824a00c50380c42e000624a50789070b8003074820740c40005101001d031100396440f40003070f401c0e504000c2083d01c0c03003c14012000150041c4e00300f022078001c0006100c018019000c82d0302a0324941c0140c4c900f0006240800401040d0b4005030486441801c062052200c03220207a210440c011031141090500c10940140c1900c0101c95a40041c0d56103000100205441e5400006076004591110800c0d0500d8045020441981c540640d004016449004100090701c0c0542004104074040d4001d0301c80b42041398000c4114200803a07080d80d650f = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 799216969 1250 799215719 799215737
    0x280b07051b030a0c02060c01110715061e12030e030f070e130b13061107030e040e0718020a1b0602040e010e01030209010b0d0209450703200406 63
    0x10a0701d0003039a500c44030001c1c020314a04503404102a0000c182c03044042c0c019280410b03800780722402540310134980340c01400415210011071406a104100103101c480c40d0f50700305003001400e540c550604810801c90407803032202030b6041455581c44140240e02c02e0301044002540e14240d44c0b0280505400001c146001c1d280303850400899145003080a00021951411112907a01181d0f04800c00f580058595602103030300a03250604c4005025994050581800000b030014205a0492400f6868030010340d020301003031051105560312150781e842101403640b02c1c3e900f00d2a00000c103600402c00000f19080009030105803110169000c50200030481e405540010103011510009034140c1c0140070f450003070b903440d60443e804108070701c8045c030425001c10400b095003000b800b8940c05a072408c2078060024000c91440c2c11400d4182e411603000c1002d03d590290700c2940000d50281c1030840e1520802e1407040f55100c0300c070100e00a00001954000d680043c94041000b544c1a100800080c1601d55958280b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 799218219 1250 799216969 799216987
    0x6040c02100c0f2d0c0311100f0507020c090402010305090f0708011d0601180504060914060a0b0d050303010e1305030301331e05130f031202070305280b0705 69
    0x110280560b45916a44c008620741411070a4101c80030140c290624003850f90310300e18901a102c0b00c0c40c00ca00c019083c010071104800003101580510f04010200d0300901c025150700d0000c0e6111211001c146400a21000016000d54060341050350840c1404040320030b06010120068200303d03058206400360f035159110b403008c4550b54650305290741c1800c0003070f2566514001c0c50011102c5109030306080c0303980350000034042c85455441710310482d0b0008000c61100b00512615904c03224209d0b4840341c414030744600003009092105900050692080040d45540d00f031500c0080720b83d00050444908003001c403500c6000640c140040c50003400244802c242c44100c060070311099000c45080c05000a03001c181621499502850038007a42103035400040d10070441d241d08440303d114810022070320806d9854001454420341140034101c84c01403080e0220640000401c0b601c5440900c0003034541c0e88541d007240c002c03a07454031207408051555141c079191050141e0311652041e20440b0000082903003c151112 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 799219469 1250 799218219 799218227
    0x915130914060f0913061107060b040f05060d1104110c0a0c1208040e060d02040c02030d0609060b12090309040c200609060705210a020702011d0906040c02100c0f 71
    0xe044030045a11003210a05800402c1c4c3e6010020a8060510041d800101c14000640d00c1f140c40c01c0a6915041d0b82c403080c9050142c09040c5600d0b130389006e9450079150007656049132248500030400200f07060a41d1795540c840c4007044890000d5154440d84d01c174076031903030503890070004d183c0419030002030000080c007420503080c0c40301283d01500070440c0c0c0c4068100000e6100040b00c080d10521010420641c0301c96010442040090400a401c145040051062786800001a241400c0031410900600f40c4540e9440240c48281c401c3c102214014400b400d00070005914507603002c00f110b001c0301c1c10030b00d481d4001803e41c1c8034210340801044862152007060541d4103454602003003064014500c506000300c801e50313500070050000b070802c0004140c91190002c45142000b000380042011307820703400d10185810080d80701d110100e02094a180d200746205402e504404400c0b84000d03c103480c1a55482c0a00000d08840d40c07002045002d540710b00840d60a01d441520094a0556503c0c0604407803001e000e4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 799220719 1250 799219469 799219471
    0x40f051501061b0f0f0302010e0c150706021e160b06192d0e0601030c090e010302010c240c081f03113007050906060915130914 56
    0x103040340d0000001880159006410fa4216640080d1464544407060a0031080081c10100080110342031403020003c1c16815003044200000c2541a6482072074004100310038240d1aa043c1c203c8910280240380108825a014110301080c4942a62110710528201d5078507502c40300a201d5814101880790050019000c0e03e2640b000040e2496600342c0004c0007942c030145818841c4004171070030051240481c168008061040a0840c00883d40d03030742c2c450458000c1c81078210b565500181c0381507800b80702603205031000310031903a080e3310340300913a4219001124180ba45100683e110403140c828651003542d0300035a1007294040c0c4c0d200066104003c2001052804094080a42841818040134405800e0310650080341d03845400e4508000c1c00102140b110302c10382402d815040990b402a02545210b1441d40f0960086841a00c0305251210204018610181c0d1581d400101c1441a4051030500401000980c40c2000e2450300307191204441202c250b0311900032248450f101d9410000000003d0171031 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 799221969 1250 799220719 799220743
    0x904120f0504030209040609050c18011d13031206050607050607030c09080c0d11121e01110d0e0f07090b010305090a050a1209030b040812150a050607021503040f05 72
    0x482c035092460300003588010b80a00064009907555560b035040040410118118500c0a4502004560b911100f5500060309124500441401a030f903030031102080d10800d881504c032126408031005040c0c4040781d0381445403000f65802a030303410020442e076a610000d0211544244001d0205107000c86005081c1c8500c2500c2070f040c0304808005104000f0003040d51455810b054520b0f6891010908010304235520728041d43d500410340d00070182c04610046041640440d800346503850790b444400c01d59080b602c01b01c1e10b6542541c4280310300e1206210f103402c4407524011500c229800d003070080032924103001880d0300c13100c400396a07030040e200d170b0703581501501d44e00c0301001000d0b0401560b541c4440d030b02d80354608c1c0014902000c55030703800885405180c120f009543c12810f091a50f241c50724007182c141e4031100503000400400000074416001c044a60243c256014003c5151645031509000417504581c0e4101d80c1b100b6040c0040d8100c1d190500514450341c05104868038003007080c248142042c2c511500 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 799223219 1250 799221969 799221977
    0x150f1b0424080411010c0c0504020c0307170c060a111207120c180312120c03090b09030901021f0207061107020a0f030c06081504051f06030c0c0b04050c0904120f 71
    0xf00008a40d0108240c48064820b007030605981c1424a0010000c220782e8015aa02c64800b085202d0341000000180520501c1027441003000084018094001d00906449817441d0384100001810f0745841c1e00014503140150740885d040403000034400d00e404c1c2c412982e050000341030030070b40408200280034002018030b41d41090b04601c445625003902c03c510900020345410030f4800c50503500c27407203100f00c10300c0c0c0686090104050107010000602a014204043e00d8041c0342c40b0100e081094040102d810b030783c0050300200380381400c40c0080d4020203400c140402659a00340402c4011440e0390145024034290b010700103540b010544108035004806070094003858916941c18000652200341d0401035890504081d882c560300c0f540c5100d03407003a54130320346034001e41064103201c010381100025280321840d180390500ca0a4980d8412400c485001d4014000202c80241c240c001c16440c3c40440c0e0000c0c060170555012900020102e46403800941e002c490881040c1030b2240210303070200c180c007082480707494 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 799224469 1250 799223219 799223221
    0x90f041b0825090905070207081c02060601080f160311040801051f03263609090703081303141e0106060c03050c1006060306080609150f1b042408 64
    0x2d401880c1505601035081241d07641c0b804500040d0007040100002c1c40039104643c804d10a5800c10318511750700d017030744001504c04c24010074241d40c0200c00403440b0b03d401e02c12800300d503560224103405020407002c0d200107041c1da81015000005000380100081c107615000407030310b420024082c0490340c01702c0303400b600c1c00050141e05000142501c4085810f001e419410b80b4041707580d1520882003880b503469407600d860b402d90190303040301c800412801c1c502407100c00106071503004541031003c511400c580d0059950401c2d44c00740009400d02014002000190312183c440980741c1da1841103240360310380c00d89095440521085055068084003508883c4480003c1c08140e251090180040c0c211000040501070702241c02e903404441000360142d1146200c0041c480e541c2e840301c019001309254005c000060148030300140c3c00b12030000702c1f00b80b1403406010089040c1ea0360624038220705c8003d00004400301c2c0110fa002801e81d2210b0150020b09000c0111000040301d44030707920902600e030002d07031f014001c0101c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 799225719 1250 799224469 799224541
    0x614043b1908270901230d0309050d030903080301120510020702030a02010807050d0c080910020702150f0f0c010c09140102060a0e070f12020103060e0c090f041b08 72
    0x2078884030b24020a40c801c480c0f0103658905010014a20519000790007180000303410b10f00100ca40c0c4001900802d8056502e81c05018480c142144103000f81c0410b0342007004100b1420a00b00341c589e4540a450a415003a0701c1c0d40e40da44150b4000e80c44001117002a80b401400d010061107c0c0c0364030003120308114a4011a9408651070f0780540e00043d0510100b04001000103006070210b406420317000e1410844800d256101501c400b4099805410b54031401303211329034611030b61003104c0b002c0b80c0082480380d44a02c25602900260710105030702ca1044014002108a0b19101004e00381d003030194400400d40c074502000003020b010071a03003c0c820803500c1898500681e40c0200b61190000c01d07621003c603440141114440c581039055221940c136125066002038585440c004ca1074001d03100f60707014000141d80340702d4034140507020369160a0a076420002c0c41e106240000c000215400090004203c0d00007220894458240316100c460110b244038042001604000302d412110400b241201d2801d41800 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 799226969 1250 799225719 799225733
    0x7050115030c090b01050c0109030305190606090e100305070608060f1f08090c03120c0f0303010b16050c0411120109181506030206070f1101030614043b19 68
    0x2e4802c5000a640c1d4003810034059105004a0341c070f1080b040006c2c451242c81d86801401403100711602842105411158540000c407405004210f071581c0d07036104125410a200c412400034041d001c4038090003030060001c0010024064000100364a48444085140040611281482e001c0ea510f02c560b07915154441210811402d001c0c41244604d0141c2e00c0365541d40c5da007807402a410342101e03494030031407625855200b2f2500091a400901c0400c6d5012a100d5081c2199a40820300464008a005000105032070340174141c1c0300300030b9001e502204c5c20b52030200d001c40c0441c0c101e40380c10f0000303041c001010740440d20359481c900c0c018000c0c0c1c1070401041d00c0c0d817580301442403003164006100d2006076640e0f045640c42c64101c01c0c0035507001055039591740003a113008000d118070200220740a0022890a0070a90b0107072007a0f2046644100c058000c1c450b0540070040103007a043c0d030000b4140030703003007005d44603903120080440d056005003101c440003145140d140345409801c6240d44550100b06460800090038 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 799228219 1250 799226969 799226993
    0xc06041401181703100801390f0f021204121b05011b1106030703020924030402010f02031b030405150708090405070c060504111203070506010311030c150705011503 72
    0x40c40d64644d00c1c5e0b242c018030b0304a4500707190300443c02e960900300e680422440d401e9004100002140ca00d45031002c00308544085424800c8001d40440c600d0890f00400c103019031f05074100442070348180c984d02000c128504a041c0c2064000090603503c902c240001c02000402e21104403011145064016261800003000214a60754189880d00e4001081d4100498844202c28440004220a88a140c43c3d04014001c3d04015030b424807401d800d60703a000102d072101c2e04020501010a080a2070341e034540d0015250030040d21044002c602c82001402c03002010340c10218810f2001d24041c4be642c62410040054100003400d0750741118070200500c0c00041c0140040740c0200005813404501585c0c0c000c401e851004002c00050035244c180000c210400805118928048104444021800c0d480110a640c0c4c0d02650500614a5018500501c0400c204040500407a403004040742c1b07076000018045030310281c3d01c000700c50b0000c3d00411b505041240a02560440c0f45909003021030702e600d183c55081e5007440d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 799229469 1250 799228219 799228253
    0x70b10330203070b130c050604030503070b07050c0105100302040f0c02030715110409090b1005090a0e0c031006080f0c0d0602130b0f09090604052a0c0604140118 71
    0x148401480c242203009105480e80150005243d0a072850400c203c2180000700e0710b81100c0310040d242e03020910745440802c1d03a05507500a0021400e00d54140e46500015030003074241014030138288003120700c060302405100e20421041d16540301030340c80c610500c0190740c1000304820342141411600c812150340042610b02c042e4100c14a1400a0f002541e46c0700182118645025080030010700410010840c0d08920460303403080f1401c0019950b00380c0c1d4001d00d80558000c01c0e5000d1403410208602d03542d6034110000000206099440b403030382c584002882c01540784888020581c5600d82001070321030034403074030809000c21001f070b110644480000880300c200c143e900800465002c4dc001100c01c2c288400b000103410700034421f03507a0346400c5032001d69540141c401580f1905c83c1d2000503405051038001c05000303e02240d658020144000b21185010140441082e5460014231005a00003c1049258012805105260320703441c283c0c0c1c0b405080d82c8840f108901400300c0104031030000380c10040140071384a = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 799230719 1250 799229469 799229549
    0x901120809041112091204050105030708092d0f1c0f050f030a020d15030c1502030903030a03051b0405060f1b0f0f10050108151b070b10 60
    0x803030702000600142040300710300e00704920103d10b41e0300308115046894045d01840007111010034140524428610850040d1030000d9810700100b400380e4000c00001e50012059026516121618804c05042c8960b400441204040142507208030840c103021544456880c600501440c1c40584140d89501c851510442e040142c4440308681703040c891415245a00b01c00349885035203007080415600a504510110b842140c84c200010b964104256042c0b0112907000350300d846081c1c9010420b2031004180190081503000c2080a401c1980d4203100800303042803a03860001c2c540c10500c201d11003900c080c06200300c01c0b410800c000e001564818058600d001c00c0c0f038684c0c56440745071201c450903144110040303100394803811800d4404a50042400040050a4012600855030006405042d60000e1040340d5090300900c1c00d00507424004031040b940018040188100300301130b4101c1c0c0e00d0390380c0900300c1601c4086100f0148080d010790001842c0080c052800c1302c540000b100090220394010030240c2c61108 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 799231969 1250 799230719 799230727
    0xe030d09110910031a04064a0631031206061e030e0a080d0f060b072a0b070c030b07020d0e0d1e0f02011d060307030903120207060618020a090e1003020d050d080609011208 75
    0x1022b1600516854105e10200c410501c8400d07150181c5203030121240c940815060032030200308544501e044184000800c8015948104000000d500610000c0d95504060080181c0b16021802c5800100b5030101c2011001401c400d10f0130602044610581114140316002c00229001c140e0000d94654184540040300e441c800b00e004410078030090795802204001004a40c580520a01400d0385040781d00500c6842040e644060040380c0303414000742c02001142e4040000201801c00c0002c02d21141e100e00705080403c04221008002000040c00131201d074482c0d180f040d0304550b070080202c003400540120440c0807100c0900015500d00004204004056480c0062000d0501c03400100040002ca2001107548445a04000e005401e16000f900c00c5a01001074411121402d40300b16030100703259940300301d54542002029284c1080c00b520b2050815105c003000f00141c0d60b1244000c0b5000e12510081c80710110ba4180a00403800042c4003a100b1407103640100b1550180702424103c0c1d80c0d0190180340d403 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 799233219 1250 799231969 799232011
    0x70c05032103060406181e0b0109061404050303070f03020106050603071e0909020f09040e030903060c0c0f010c0c060b0405010b0901030e030d09110910031a04064a06 73
    0x8000c81c1d8000303414061b4441c940c950800040d405a20200504200d0075484000c00341c1540a44d2640501a80001d05008003041014401c800083c0746c501d11345007140c0303041d558100103032440c0c00542040d038075601e41345090010580c0920400006242c00d0740d1a034214030348590040c015030480400e00380308814008683c00210b106000810261100d040704544446a0402d0103901e6046100130a025500d403802c1c100c2102c500105440e0072040040081030950380d1210f410503242c008078141401c03031261000404140310280a081034281e0641e596405140c0141440d205940020301802e014a00d4200148000b060b81c20883c1c2c4001c1c8282404a98400d45d04001807440c401d010403680450f1600c225842000700b01c0300110061b041c02c03500c0c01515200c04021200d04081880010181c100e0403490103030708400811015072041c06108005160003012102d01c0100611800c40210501140f811031848642d5824401060004044c84c1d606044003180b5240e03102c0002d800300444040c01c09130041 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 799234469 1250 799233219 799233221
    0x619020c2b060b190620060105030c042a0203180f030c010f05040e010f0302010f1803030c020d0b070e1c02030c060711121f0c0e090a1d03070c050321030604 69
    0xb001141c60829544180e0b07030700705c01880001020042150101d940d1400701258100180b4a41650402409420340b81080c404001c01498600046160f4106004031809a01c0507a081500382c0d2034150099540c41824541400400d0b040f20400d03845400419810102a140005c41e20ac0040702800c0018a4001921050f1010b004035407010204e01c5181001040000d451030500d8202c2e8803e8840480d032040100096648100000b505c0a030301500703413010070210307200346a4a0002400503108159190107034503221840341c01199008041a807400c05a010ba00300000410410070704008442e1301c41d03540d44c0c0040d0321031190f00411071240c2004500142070164108982c19a40d100501110030000070030f041580b07a00d40150a18400315102e9212501c0b80c8940c00388407a0003c2a6030703143e4001c41e20104100c03882c5005003000580581c3c2d54159401c0170401d668002416164130001c5440b4800e61906a0504c1580e80004e4040c0d0007001034140c4070b1400e00351a102d40031089960640344e903a0600403c2c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 799235719 1250 799234469 799234489
    0x9090a03081008100902040e0c0d0f06140a050f1f060810090204060804060f051003030c03030e010204140906060703090b031e0c0d050a06060f030b0619020c2b060b 72
    0x50750a0241e88000e13025a070007940507064a92007076605122505d0401603058583c0c07034560301143c000801034000400100d600352012074892003954005402d08a000104401c07480c11148103800070b40d03c00502458003080d0b03503195400048040c08a1010000c1070440c407506403c1d103d02d0b41445002004120701560808090004d052201d004548884c0e458a001b02030390420355040e02c00303510f0001c210200703103040e004041c0300380801c01c00b0310341130391540c1e038119482420032605804150760b070104012001400c0c001800201890004075003414001c4040118082024200341d00c01d410401c010380000750080403d02c21105000003c40e160f03580d0554100550840640407507021031144100000c0984d00806001d01c0400018100041d40d240c01600c02214880d01558000c40d204400e0f240070703140300760001500060003602e40c2d410b00e2103510100020a40c0d501c20400540c00c00c502e01c1d070840c03c0446551304204a80c0c9204081441004961903c11022180140200392030301d60010142d29425007070 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 799236969 1250 799235719 799235729
    0xc19020f0307050610080303010302010212090402070b0901050106020c031c0f0207080312070f0e1e0112090b0f071701050d420614130e030a03050403090509090a030810 74
    0x502d079648001d20304952282c1c801c44503003070008211000031070325400c008140c0303069030741c1a0003c142c03000c240b140010298000e071510315841781c1c00300821800a0140500c041c0905015000031590303504000d00a401e10041c0000f040c040d5000d44105d201100c1e0310000d200b0300d0100307406c240401c3e00c0604c0703080307080032142e40040c80603104c0055080c1c440c1c0e500301071051162645540303600700b504940e0421100b200f01000f44507403008001b400003200c2d40d00e6652158500e501414880640d041c00c030913a00030f0324107020007030b140d103000441001510f071000840c0c16030042c503900d0f000c0d81c6003124900c55500101e0600400f07004000607000d113001c00101d212001969003240310036114413000c004070202d0705030f400444450451014802260900202e0050300300b1383c0d041244c01214070212806201c0703d4040000c4e0706d03451940340e00404a04031000c2c0014a8806459a4045494581801c015291003455407100d0300804414007085403036500400c180f0201945890700c41c04a0700c4502d2180b800c4110b982003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 799238219 1250 799236969 799236973
    0xf0816050303010608010b0703021e190804030b0c1c1802040e060709060f050d020c10052706010312200706020c041a010c03050d0603050709051801050c19020f 70
    0x24141803203030000185040f104c1c0382e030310241d080e0b8940c401039050380125040200580d210000c0c9000c1d020300800b150b00209090000c48421001440700f90050f00c1c200382058603500c00c0003c0034010f104070040d00c2940034160008080c40d02202240701c00089506d81c40e0380409070340d600c560f4840d10f504880181c1c0d031241c008000340301005d05403a115031600701c240d0302c441c007180e80d4040c009052400340315404005105d07915024148045804900c01070f40c4860140301182c041c4001031b40c0c031140c0702c2c070a0318040c5041503a41c510300c0c0513440c00500c41400342428503040b80c4c0640c00400c0040d003100000801c1025a1400851081081400b0300c0c0c841c540b180705d40003d0044070070214010394000340f140d945400c11034050000c8a80b0302280d80405020016444c0028120380c0300402003401180200005565000c0c001071280d07907610f0f12424451250801410302d43c0f0b99091202e2100007180c00e62400350380e54020400c0c1d0400000c400c03142e20441016040d8040c81407041d40040d07000380484048005000300f = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 799239469 1250 799238219 799238257
    0x90f050129040b031510030905101503020306011401020d140703031121090c010314010509060a08010c0e13021602040b1305160f0f090302041a1306030605060312070f08 74
    0x2203400c805c84860320403035001e046c0010089a03028824002d5405541c2c019028154122940c852074002d80390b4499031101158001c2400401600c003042418020852480d0b05001c1d0140d900009060841c50b0507000c00b040740d00420345689080e02000c0b24011507140c20002000440c3c50689045030041040c50540000b88910a00c5c01521486d031981c4070303440c50000e9803040c0300200019400c4031200c2440000c3e1009840050029007071080040e500090014500100e5640c4d07500b90600391380754a001701001640a400440b52810b0030760310900c0904082c0000d40c10840b00c030130801120388015601078480c0b5210319085859444003801c40784083c0144c0303401d20682c900180b030301c10700d00301050007440000d801a811059180c031a0090314110384280d078411b0509850340c0c08000140071050140c62802845c00c020565a50b950609107610303010020b004205a803450400340202c910023007800c0d00a41101c100c4601d240346040c1201e026a40c8240032011003050f50400c00d019006181d030800300006034403 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 799240719 1250 799239469 799239481
    0xf200307060e0709020c0303160c0b1f0b0f031512010e031309050f0a0e0c180609010602030306010e190902070c03140a080307050c0a051006090f050129040b03 70
    0x500b02010605107041124074032542c80c07003400120720440900540541092000c149011101c615544c8844031a01d046c0b031710311104e510f41c060320704400d40d40302801c10349120400c11f0780726180850340020255124880d081805821200c6201d200c000c3c45003000303c810388410702540c1d840d000d01420102e00d0400802000301c950015030ba030b0b40d110b1300640b000d003584498001081c0090b405664407480720340c5040105030b150b54030b64001505e04144440f40600403480524900d072031710502d1083c07200c1444120b8180d07080c134100f801a01c27403040c0c00410841d00f0400030016140d03049000480520019181c09000301c2036080301e0704880c042d81d0403e00d941d07400040c01c801880860804a401e4901642450109000d88008540c1c1c170324007240010319654050001941e070718003c50250000009003c1a10382c07101190ba112402c040f80b480d580a610387d96040103000c04a55407041984103001040208840d5041280c83d507a01c6000031000c0e800c50a01c20f03540000480c030502614020300b00401010707243e007055 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 799241969 1250 799240719 799240721
    0x90509040c05241b010e03090f06030417161208071b020a030c0801020403151b05090609131a0301091106030c130303030911220f090b04061b08070f20030706 69
    0x1044c0c540d840d0b00701020926414000300880c1d0b00b05000400094040707081d5010300c4640d0b040100305640741400d90350326801040200c001000840c1c1c2450381e8030900c2c42246014464881c818041c141045100c104000d0b0351130300140000c5030080903400003559003405100040144071560401030040d0060b42d000030341041d054002d813058a108502000d54490070b00403031406c6401040d170180140e02c0d0041c0e00d80c000c1d80180020700320002d0140507240f9048501001c682545002101e440351a0b07520009a03212903000d101c03149849030110008d1040c2003160705d07114213400c1d1041d9403a1042c1f600102050041c0e030701e401211100d4200016501e840c0d581c030b0034064000c000030003090350741c047d62550416940c074054000400d41000c404058007180003410600b0000c01ca07005001c9a191b0780d4441e41c002060940c059240318a12030700c00420b004160035410a00002d840b40e51806101e03024092199003504038900c042d40c0070b0103160803402200c0c1c00803200c81030f1154065002450100081c0c0409006107 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 799243219 1250 799241969 799242007
    0x110705030408210703021b010c0516030209060a05061909050a1203030c050301050105032406040e1918260304140105010b0310030605190608030a090509040c0524 71
    0x3c602d40589002c0111010407085104001d002001600901552101c40510000c16403040f00d0600d006901803901d0340d0b4540c5030035000050701c04405204201081180340c207070791840d404401034a512600741c0c5800c0120b4464050501192030300b0043c660b8041d1010b100303c0c816001450000c1420390142d55440c3c500c00810804072040e0002800c1900021180b80a041102d04984043c3d480707a18507624164109010028a8030981c00d024100c6c0a900b1a55100c1020300040d0450360f003400001d08002c6003401c02002c85156a40581c1e0510200e030f00d00310180501d1504064012010050b1022080c0f01902049034608800080c1000402844203101050001c0f94074820803a00821250345c03203051540d01c07400115044e100034220ba14050000400341d4101d00c0e000064413a500028081d2042072409458441d00100104e40c03000c1281c041c4281d01a4000340148420b80d03482c00741d41400d0b10384541c441980c0c0101c500a100c42141c0c4c0006010309559084524400021030b61901c68024150084100c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 799244469 1250 799243219 799243243
    0x1803010903260402010c0213060305070b0d0608070f03022806120b09060901090911040c0e10030c14071a0f0703110306031e25030215090d0303110705030408 69
    0x30689600110240721030b09141c0540d405031103c03500342c0005d50030040c2d02030b01c1402c03030020551541c0002000078070030040c031800341840d80111a1109100e0307a418048030200d40c011642541b0480040080114400088003501e4042c0d0b12880700040d07064054440c80021200c80810b19000c400006285a004490010341c0f01c00c07034824000d0800b035408010718441d043d15803070750049191004100301401c07944420300c1503108680503409944071030300103411652800c0301100896041030000009103441e0b0988611b400c003d0800f00644040c0d080c000f00001049069810151400150701050140002c1001d031400c0c01a101e025291500760682c0d1003009064800034003007418500341c9800000c019050701d104140180c028071510761031a041c4502c0b25423108c514285800b483c0c0b8030103450b9403151100c4514040c800341c4c050b0010314500c1400417a4000300f03580000d94005110b04005503942a507000e40c001d405103004035030038044a03400341c0644210030000780148800100000d201102180000b0058 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 799245719 1250 799244469 799244507
    0xc160516060f111c05031504060312020105091506010e0406150c020306010602030c1213030b0708040b0f0105010e22021204060e0d021e210306130b01020709021803010903 75
    0x1400d210340150794113510320518900c000d0254100500c140720314059a4418044c0300048200250603000c6412a01103400940d4840302113a013050071681c09004080d0040c1c00035004000b0051406101208003102400e080d0400110f882c00707400c99500c0780c021001502d03038000c2d00d46003011250b0016016003000c500803130007030150340300004416001009648201e51403a029209444a181d00c2d40305943c07000c00904e0b0300c3d002e8040c0100200e403413941d820317200744400c1e05d50054908240c14901039810000b00130000c00903841005101c0b80c1d074826200d01315660140c42d05503484041c0001707002010001c400102c1d0f010710200391000704854141030175000e1406071100b002807140910a85450300140351020016a10110404400c0380c0c0400290001d0548101904e0964a007161905a05003d9000c902401031010060140910301030202041c03082048004202e82d1120100203500c400301403003584c0829a01151458141d031a513125503290b480c00500030802181c041c500a0f00340410444462040 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 799246969 1250 799245719 799245737
    0x1a130f080309120f0c0402070c090606050304060b0306010609060c030207091b0e0306010e0f09030c164401091401091208100302121c03050910050c160516060f 70
    0x3c580402c2c0b60750a69007102c0070f0505400018103001c060360042808a907148203d8200159a14851040f04044c204070340d9420b540781054185030040e00c1c51a480c041c4a50820401000315a4000100504803055414080e0b1080d075a400c060b0b0030a0b40b00d600840c150f80c1448080d588000f01d10100d40c6240d19682c0f51003603150540b105240d0343c0d060902503001043c03401030204096452040210f039102040c02e0459152000102d01f1f00d013010079203001021407010306e410600185043c40e840c84815807080180d0143c000760085202d03100000980f910140350340c441c2d0035090302c2c5000c0d000084825002050001103500f4490003078001d0658010a4030007030803c0e0940c0b070005100300142401145030350010040182143c003000300101c55120440390600c1141c3d511851510b44038500d0400d0000754500242c280b4001c1d640c1402c01501c55288030300180742c64208250180c442007a140144030407040615102594500503150200740c8054800c10600c1500c0081e0382580b00201c68031800c9981c0d514140 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 799248219 1250 799246969 799246999
    0x70e010602071a0412051006030b0f24040b01090b030f1f06020d0e1809010b040f27021801080c01030f0c0219170a050c161a130f080309 60
    0x20400c40003682c60120102000f04201d48a041a440010b01b4000c40544024050368061401115060791040700c0210805040044858022909503800250780c50401003108c0c0c0011088600c51500b00010700c80c3c1d5840001942a900c108441005001410182545c03410007142001c0300f201d007100d00e5010090781d08646181701c11401c0e400800c49403160000c004801501707030143c074101481442550400c1407404000b40e00460400401e00801c5030a00008260083c0018441550048900e482c40a41081c013072400105500d000024070f0340309404550410361300c500c0014403d516840c1c064a540761100c0020441c1e5002048044c40349001b602c040002080000400c0700361140c000e01d0001503004a038480810295081822405a1117400200c0d21083c3c41808440309402c6540d025000440c00309402c10b119804110880e9228074140e2208011850207040080f89e270b80e01f5a10300425100031420040c0f0300190b400400107000d11004024603203803101146a500c0d0800001148114010340300c0600c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 799249469 1250 799248219 799248239
    0x62809020708090913050a0308040302010f0501060c06060519180f090b2d070305070309081309050f09030a0c050f060708060310050f150a05090c1c0606120f0e070e01060207 76
    0x1910a0b407180147c10032000b03a48090300c0c0700c0d200510650540d5201c5840c11803000c0c1e10700c625406482192280701c65103007141401000c542498100300d019a1041c0440138030400f00d00c5030401120801d01c01205060300d0b000c6994040c144c501007102000703090105e0101000341c4510041d10404075440c1171112964030400031105002a2000340c0c20082c294008103220610039004207622042c0c504002c201c464290b907039806907610036071103a03000000c001800e0000700141e008554005003c49900812803c000d4522502c2c0c1c4600905442800319a03030140040103803e118a800c924078420541d045440e0002c0060070001c42200c0c0d5620030300030113025119032407a82c4a10750140a080403900e982e0358070b1462994410009840c030550007400d031280007429a0b01c01a106215540d103030500354850500142c00b105400159118040c01ca0070140148a45644034a81c5c52440144610105088881080c018002c0c420190711007441e000300003000c52503081e03903034019048070016400c69941503540e82d0040 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 799250719 1250 799249469 799249501
    0x804120c02060a0503071106090d0e04150b0924120903120a050c0c0109051c0507110405280b010206072c0103021b0609070e0628090207080909 63
    0x80d030095051007180d10507032003000615485805404c001c14611840c07503499180180c00c44003207e40c0e81c400c54056078482c2c0d0007264644801c40650f414020700444000c0c02e001203700e030040001015021410850550369003001440d00240144100c007180280e07013020f8900d502500d8801c26054010b004100d071040d001046070a21140c0060444040e103c1c41c901002070304c400f4200a42d041000c0c40702910068081c40f400707048030f1064000388116a840e628031614070514249000074040e0510a81c2d0114402e68261969030904440014032507503040c9104840704402c0011021140002003810405281039110382001c2d0000d8080b04d1950f562184100e131040c0440c00c0125521040788149500044c000910103d60401410003505110680014028005c2c045818040c1a1f0020f0280203e000702801382ca4098807084141051030715000c0b02088150324108805895244030310840640081e440040c8005420b403203900355a11115401c0a010741d4100700d00b100d20a42007030000c03031150756040d0b4130a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 799251969 1250 799250719 799250723
    0x1b0309010e1e09071e09080606011803240207110f06090a06030905011d061009021905031b0a030207020108010b092206260d020d14070c150804120c 65
    0x1503544442c90030140b1400361009000300050100b01c1c59084000c80c1155188a80720406a44545910307190680701450024003034856410301c11404401c505802c0c51682002c282c9401c03400c100c611452520f265015811076600c940b00c0c039440461032004011201012102d0804200c840c0d500c821741140401502e072080d4a103281d800405030404000407030081d007040311000d00400001540301180e003e0100d0004040c0850005038000204110300380d200000e4090217007505200450520000180d070700840b80759003844038248440880080c210340101d5402c40c42e611802c0000310380340c02c1c10312405030107900101d00480c04200f800c00040b40e001001400d983c0b01d0800101080282c80a1140c1c90b10b0344400d000c031032580b1548460b0b0118003407140b005540605809a02501610216031049500741214038050804542190904240881e8480044002400031441040c0e0b101c0d914a4420b45288040e40414844208420a9243d4a4004103040d10883c00340d0023800e400680e220045070184005800 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 799253219 1250 799251969 799252009
    0x60d1a0102010e030d11040914010303080c03090304090b0f030a05160815070806120d1d060a09030210030f1107030f0804030804030822120e030a0f1401021b0309010e 73
    0x70440a0170035040f04409102e0704400b135203026164010070050f40c94900320341000c0411030f0010400c01d40d1065401d1b501080c10101c950460a00c40724650b02c8e4855442880381094035030b1111440382c0d48082d21031210800050488040d8156441c006132a40c40c1d1600d81c0c403006044980c0003c0081c1c020400c1a40c101800c10810707042c0c1d0f1034100c252908000604001c1c0c01c1507558003a5440142c0401c515020141e90b5100da8583e04c403c0165040c103108002c00d114010034091000008103500150310409a80d03040b289900d140c0c0506200703d0081c0859145400c4076808d2020b41d07071f0340303d52010040a21070300960f80c140282d00850000d8401c46000d440081c0003800c401c1c00203012910904001c3e4000341c4c02c11080b840c0080400342d2440d241e0200c203055a403c2134030741d285140307140c1005952820038006e8020b0406140603031140382012040441c05803203a021502480d44201c0300b94110b48880080c40b1042410000c08401e00e540c07508100b031010301140c41c17000c544280307103480c4540034a62280240 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 799254469 1250 799253219 799253227
    0x180c1409061b070506040b042102030c0405040204020c100603140604050d0f02010b090108030a08090601050f0108090a12021e0114180c04231e070f0c02060d1a0102010e03 75
    0x45840c605085040c442d4070700036048040b07601e55400d03004100414441c1e1040381c1f22410940c890a8100c901014507650042484400c0d005840220f200304002d18215030014580d42d0700c4c000300d800380c0f0a03c03811401034058007a00502004560788a030042d240101d294000ca50381402145550700c0041e00c0141460340040110700f0180e01c02e10003900b44202c948008681208824003003910020213070032038602a08007180361582180d20541195100c0c2c03102c0002e01c265450300f4041240542d144410038100f00507034000a00380e0b071041201c00410390f48005181d07810b4100700f400079207400e085641507801403200383c8001500c1c101406507074070000f0846c0540c011500c50035601e1140003407185000300540135100b6904a243d940e0310a001000c4c0151000501854400b4054101035000030005070f00703805503420401c406071000250561059460802400801c1c01807402c0d0f8010040301c4000b0f601c41000905000020880d0f0058000c4412404c2c034038100c400004010390a031641108040c0560340144 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 799255719 1250 799254469 799254487
    0xc010b06031e10090204030b0a1a091f0b0a08090f0c090c0325020708150f040b04151a09070f1e17012603041802030a06180c140906 58
    0x1038003500700d14410000303110301c0d03a04c103101e00a80e04150300c1907801000b008104610102280100400c0c0b05400e400078030000c60000018100a80c0604400501a01104130f038190304040f045100240034581100c80e100d900d54880201480c4d81202c51090500903078400c5c41c140070300013074440d5641d00014203d0f81035540d5a142c5440340d4000505000800f0000b40c0198a0140030390016031100c2a01c5e400740100c0c40c02e044015161200c0000403d41d490003075002c00c002c018150b440c06030010b034440b01e0000701e900c460801c04107140b84080c1c20100310380f600007100e0102c0ca9900209842d4401543d000f00507964401003507803820f840d450002301003101100c0c1491401d0494100002d400f00301e041c2884100f20400c60160a41001d81148101850341036052660192180fa21301602e01c65030000c51600741450b101d001104082c0903501c0800d82c0200100e07201400f5608604050050340021482c0c000c40f0a500340040d048007c00c0c0008243c7c0000c4601015040708110f5650040183c03c040c5096004 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 799256969 1250 799255719 799255771
    0x210215040f1404090206070f122c0f1305011805072f0f07030611040521011b05071a01060e0d05010b0d1a070f0f1818020c010b0603 58
    0x40b40340c25403140d611410400181d031201c001e400c125020b03144480100030640350000341c010303550049105108582008081304400740b069101244428820000246402c4012480e00d01d2811a0507034000c180d200760a2950300658000d0303040340c0385808042d48010f00801110102c1d14140e400b403000404448001448001901400040e1904000304810f000d400924944c10000d10103002d10711504078640030020b105d81c40c0245102c8a000c1c100007440c0ca0720309800144441045041e00d02104c4aa1781c101000340340030b40c441c416202003070b2510017042c0f00e68203000f8641d502101d82156000f620160701c04014070ba241c5403d06071945c1d40c85592110350310504104282130800c200b240c4035925003090300030345d80b541079040542900c101c140302441c040e40641c500481a00403c0c4008010905901c00021a0320040808402c440c500740360215030848004003040040603042205541502602c41840c50758075030081a140035450000c010140e00710301045880c0c0b10690b50850b0700e00820000664940c41 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 799258219 1250 799256969 799256999
    0x2120f06012705040b0901081f020c06150310111c290901090908030601031109040c020d02070602070b18010c0609030c060e06090a0803060406210215040f 68
    0x1050400856a46011082c0c00340c6803101c1848429107001c0090030403181c00d02e0f000d4040100801c4421303405543c1480340065842d5455041982d03071010514440d03c24440543c110780148030b6043c26149a40b0b0700702c00500745d4105450302c00c0d0086c81610301c1e02d99455120301c80d03540c2c12040003003020316003200070798010060344071070ba0103039980c6580741d850114038032042600b001d09403000384078420403000c80c00c03c00100c0c510503408525003e080086000010f001002100d030b105c03600b402e0018480c0c600341d03424030242c02001e5034260010302d842c2c000208036400160365000c140b0a070b42140c80786901c3d044100d80341c1e20644542ca80c0700c0400e01c0105c05002810000003580703170041c98015014491a1210070580340082130540100e121038050105200003402070280d0390213900b005085904000c200999119150340c80078007112000310114074079595507040200101003031540041e040b03901405e525121000306500703d1207032402040e51802c501e0031038241c03021100782403010b00e4682c0c82c1400142103c40e03 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 799259469 1250 799258219 799258231
    0x2010e0d0b01090209060912210f04030f1509050a020a0b0f0319140a062c0f04020f101206050d080a080615030c03060a060e030a03260712050a02120f 66
    0x42d051198105c0d62312a40b041c14940307924040145900550071605242c001c4d400e54502d6070b02401082441c00e03020f0007000703d404895204419000050319801d040d081d0000c60316080d01c00d94204440f50041c4078000440c00120350080b0380300501e055072803280c8095849060765038801c407642031001030005103e00c0c05c01281c0c003200550108541072000303050100041d08580d000c1c210741c1e80d0f400c00d004070544072501e04070703490b003c2403c41520000d01c1d007072000088005040e102112a0340001500b1912080020b100005010700800300987d07214501031300c0e80350210500c0341101c0c0780c110b00055a1900391001200e8a80041506203403203420501201c0012006240c203800c00248145002d000900d88011031003400880740b05034030f0703060140401c1002621366001c44104180202441034943d00460080c044507030500703101c1035000d4103188103515500744011001c40c3d601e1003010030405940110314510b00f01b5492404001c0ca9440b51400000c90280ca84010310100022002502101140c492190408 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 799260719 1250 799259469 799259479
    0x3040606030c12151107080c0f06190b040506060f031f03030c020130021e0c010b030708070e0c0a0c0606291603050a050c01020c01050402010e0d0b01090209 69
    0x240c4948404440c0300ca0340e40121075a81403d00d0407424002c0e440d20140d00c0d200300036070901c20b020403140710810324014018003610412001604801100d81000110b00308854441542c049261004e194410300c1c0c41401c0c0d4107066800c00c55060711038640f41c403a841c42040c0042945040c401c108860610740e420041680101c6006503000c1c0903981c8114400c0c030002c6119940340ca41e025018400109010384115001c000300c8820740311220046d4401210010083c5284801a200c2420720b614050040c00c00254002c07035440010040d80d4a00190006280d90300c003501100c0c2d102d5510907215540b803819114050700000d059001ca40382048500c010041c1c0521171414000c00307000e5446510450704150308c01c0c101030b042186210404540c03424000f0344490010903a0b814480f03400c40e80255407045440040820000140741d5503414010419184200d4104000310b48800e01548e5843c02086d0a840a90200e80c0c440403ca0192425007841e00040d0713809642c480d426484c1c83c4684010350042c0e95042e62007 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 799261969 1250 799260719 799260731
    0xc070c0806010311012c060d090204060f03111e0d0f021809010e0706050f0c01140a02041a0316110f0102130e0a0204050105041406070f06090516050a0b030406 70
    0x10510401180b4040c40c0124650600011604005000302d0700e85207502c04502240c3c50000791495800b400e0354860b02040d5022603448411a800500810594000039880f514000f03020403542070640450b0142c9210b9144400c6010f5080b04102c0d64002204d03034040c03113580e00d81c20b003045401c040816595240c850601c190b0303590302c985d0002d41091900f503109140b4013654420481c01030002d008070a42e0401d41805030440500f420710007000c91085050401d1303442000203c0c201110300940c003861100140b24000b031200c0c107019400002039417051003488009903040200820301c4c020358049038051314105a403c00399480320070040d220120300711001c031240e010769205900141002c1c00100350114042410455503402c1010380c00c2c4e060006465414000c2c414001440140d0300041100c040d580358030068070b000c100d1580002d1035403098041c0103100d0603500c00740c42d04001141d0080c41180344079005490103520080031001c0c42c0101d91103030980c4160070401c00c22513200403600440e040741c0610710101d01 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 799263219 1250 799261969 799261979
    0x12240b1c020f030907060906090501110309030f0307060f060f0e1e09030a0201052203110102070818102a0501110c07150c03050901030b0409050d0906030e0f060c070c 73
    0x89810007030542c00c1148001003004400c810500500000d00054100aa0310a0914400600f0881d107405158140300d440121400c0c0d0400c10070075182d40d00f070018101c4115a04080059403070b41c000101c21039034581030440d26144139800b0f0241c04141c0391a801d0400600c3d2a00c0c210900700f000107000602c068190322810343c4042c0d21040c0b101e11416540008607542c22049000030308580700105040040510009001e843c0300d050320b11341c0c0b42203405207410ba032a10b04507420640203101c1c5000c0244031400014a46509805440054140c000115010104030103506015210b1542c60721031060180440d902c0030700400d110184440006000d6000015108070403c416031450b0320110601c2d010358400a010440b620b03001001c003880c980c25150000080001c1d96018005010300c0021034180741c5c480d4500788a50711698004100b041e0008100c800c03080c00030303c1c040d00d8443c0d5402020002400d10400b04002c3c8800501c00c1d600703003001781c0100303c1a07031030418454142d040304200706c651240c41100021 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 799264469 1250 799263219 799263221
    0x1505060d0312090b07111501080c010c05120c07030303050a18080a0c231c020a0f031223090a0203070311060f04090b0316061e1101020a12240b1c 64
    0xc40303208651507902c284032020414500c3d103404c00650700e0722921f043c0014043e07098046048041c0403801e003003501d0111820310f085d178104401d030411400d982d0000b28030f0f1a600031002850304100c901a44080045490707480848084d038000308032000e00a54101038020004201c0801880400c5042c40d00f100008d520343d6076680c606440413442080355000d10943c122800c000e000f0f001c050514002024a64610b822001e51580003500010340b21962985920f802e25001360414684c000765540100402800000002054041c5048680c081c0c01c3c0900043c205120004410a500c1d800400414890389186d44034040408601d1515030402828400049244294405440074049040010551090023414545401495548071030b407114403040821045400038907100025040c8401020820390420099079502d100f8074802140358400103011601540c004100b19810305203080505c000c484640d0340c0b1422045881e6105031050b1003900400030304542c03000416100c8080c02018a110b00301d03070040307c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 799265719 1250 799264469 799264471
    0x405030a180f0f0e330409150f05010e0702031806040801110403120c11041a060a0e180f0712060b04090f140c0f0708251505060d0312090b 61
    0x200f15000c01c04024403c3e03060b045a41c3e6031240c00b484111440e0b011441c007034051159400e0401c624402c0d4000c0171010340c1ca4035004600c1c2543c12175000001c00d4860840a402006a025180d1005241500100b4408241e8864500812496000f103085c03064546c2d40c00c1400103501c80c01c0358802c0b0300304070001d0b9080082c0180011414440304031503e841c034604180c0c1c43c80d0024111117040002c0c458110000400c8030b00b030240da1200a440001320206000307003202a444000c00f0041d8051400b1602305821641b018504441c800141c0c1c02440d00e101100712488501b0060b034001c0c0b0500464000a01524803403070401c9603c10303403d00302103070850750313401c102e90581d206401150300d040e05c400c040c640c400824000c840030380d0b60380405030f00c1c01e18001c1000005401011070b00083d0000002d9640188180402074074400401b0126100406059401140218107c1031040f118200e5200444034000100d00c1139910405000c0c1402c01d04060541e400c03503503094616208800c06075100c9060002c00d104400072 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 799266969 1250 799265719 799265729
    0x13081911012618060a060f06080702010921090806150d03120c0905011e0e010503060a17030a0201112701140c0105060118030309230303030703050f0601080405030a180f 74
    0x100103241004583c0c2c1c2c200403000344a0103c450410314100b109007502107039070040307803c5480c0152281e119428200c3c0501456074010b01001c0741ca84104000460071017400255104607220700d000d49584002864440904586100b030f044600413640c42e0500b0600134400c90980b180c03030080340c540c827103241c501d0444180404200000704018400d00c01c55070411440084a01c006000f0190858169001403400d040d085009041220100110304203454091000001c2d006c815816491011181541ca0750790308031180b01b01c01917080014181000d50302c44220b07040101c0404001e4041c101d48403081441e20303010b030442d90421083e44a03101c5910960405003e070105220000705103400c0443c0010a100c0d22a02d66500b141d030126400c10000380c10101100071a8244041d0b01217100072510b007034800007c015a890f802d07000c0041005030150b803650080d486908581d82100a030740300c00004580881e422940204154820001c621007030b8050505003c4403460034510000d9107031035403850013000803d5408 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 799268219 1250 799266969 799266991
    0x30509040c0302190c0309120807060b041803180b13030b0601140316081f140619210c0903060b1906090806160c02060d0e0102130819110126 62
    0x804400c0650001f1001c008195015035580520705540307400c0a5032082e0400140720640e1501a0740b00c07520382d90000309124881c489805052145804c0280c9240420f500140d2900410b00c0f01003441400340050350300910481c812415210300b0755403018078035032010b04a1418050580511111102110b005622034100700204803d42d01c0307602000707401014083c003141900c0340001101045c02007960541d1088500c0c0d060907801d81e400800224003644960301c6048090840780c40741c03c03881508100c11040c044a240711000d241d0710500101c104413010411540001001c001e01000401d200750014141d1a800500800484d108017450042d401c0c001c0d448080480d0203c0002c100410041c8901c40d800303002655942c0540d035010700000c2015035000c0000380314041c0070a80c4842510294001d186080c0d1101c0215900c00d01c0d6194000d0300809807260705090300c02c0c2c000590b42012074550080a65900c00508804070100d500156020b6211001e070120b0a0b1344805180300e0301d030a40700d0040c05881c40d015 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 799269469 1250 799268219 799268237
    0x2121303050c010309030e19080d0908100b0d0b0a0f050702100b030c03070515070605010f1502240919150b0306010b0a18050613091503030509040c030219 68
    0x41e20904081010301e286050600c1e000c0c0203004290044407040c07a6100c11078042d09580818465401d880b0f525030408025445a024800c942030340018400c415210804111155000307071182960540d90800ca03426002a1290080000111070100440d04400403540214280c03e0141c604400c44008440050041c2c0c0301c2c0d07040d1158000c02e4440c201d400d4105030041d0003600071000200c0d640f4020f07441043e000b0510764050702c4403a8101c1042da19096030080003800b4950359541c504210081a00526040095003200100003500014120b00c0034003c82680070312501d40b241d580c0a011800411552540c003410061000c011303260404010703040e11958a101d60400c400382c1d02000c80e00403003141400f80d48003d00606c84485980c3c1502d4080b9618900068103c3c00340341000000e02081d403045410034804542c201e0092920410a0151409400d00f0464034510f042c014a15402c103200140125404200c0c01259040940004403e60305c035050140c80d007500c4011090410004400790000225545 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 799270719 1250 799269469 799269473
    0x3050f030a020c0f1c09140f030102210105150a0e0f1306080703060f0509030403120509040501120204050903040609120c0312110105070c0206030c0d060e0703020a11060c0708030702121303 83
    0x40d10200c1c000014503017107540c01d003004001001141c3e071f03284107840340c00e10059541c071980e0250120b903101031800c2d410050a2041400508410380c0a0250300c5c802d1340c101c40607485a4411340f00b958104101640c030403500a080506004110108484075900802c075a401c031818600035001d60b100400900c0000c04101d0b141d410204d0031640118409c1c5078050400c0184441130030004180c0c2c040e6a0005803554800c09a9070040e01c65100f4480740640003820b2400000340028280001000c840c02a5410310081d40c41d40c96003602c9104c0c0c0e006031030125801200500a0400c008000442d10707224001c006841912a104c0e05509081c0e4410203002800707270070b52023207000c20a000c0d0a41146403820001000741a0f50300041860100420024407100c01141c902c081c000542c000000400a03011100c45074180410020f02a500c03204840340070411040c502d1001c2203000403e940326003200c408040c14005c091b51041081d61014201c1c3c001c5118500b00c0b049400041c000600d00b028000740122001e42c958 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 799271969 1250 799270719 799270753
    0x30102040810111204030f0504053a02091308070602180a141507020301150303020102090a170601030b100e070f0801080303190c030f0207120305010803040303050f030a020c0f 77
    0x1100c0079901d101018416610744e03030408900660444d91508180655030400042120540100d9000e03a600402607000c056142c0d412504503c1a001607015030003d0241c1154400440011884001c0d049480c280010700034030003190410152a10401d0400c0c90001e91b80c030794070300b07907005260b85060140031034003080d16620782100f0b8440140441036000c00000244800902075503400c0117a041441c2c4005150011941c0a40c84006618140c84030410141d8a07030038003c0c000e40001e0030950003107450b410013241d580d06081c02d102001e054600203100356070131170b0b4900d02c403940060100c98900000400c007203440c515043d01103100d034005950709000d820100100602c07809040c1c0c462100d42d0010018004d000141a0902ea150100301c0f41c0070400b01e110090031001010600c1c4424045803012414008001a544617418070710740641d02402182d03201e000b1662a446203100080100381c00b0011045211061000342d42d20040e906001800d00d25825240c9040c0100b1100070512500002d540325140d60803 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 799273219 1250 799271969 799271981
    0x2f0102160c14122e050702300f220b0d050c0a050702310e122701230a0906110c0103020d060f08030307020106050f061207020c030102040810 62
    0x11110b080710003050064260310b9a2202c141503003078900120305026100907102c00c5841494060b1380400042c91300740402034450030b0658002811640204c1c0c550102c0c104080c4458500640800062030005105041e0140c0e900080e01214960098442d949440d034003407080070020126410000d0340c485c24400d046048500042032103010300814807818040035031100039100c405905a03201604c911044481100da05030428480c5601d411261617080400f2540e00f04400401d42c000403200610a118500041c0b4000c1c420051440130840340411001011605140f20490301070400541c004042c0550480c40103c440c60608030407000500d40e581e1507401840c880003041d140c90311301459541202c2c02074481100120050405401049940c030503805503100c40d0040560440301119640d032480d101c1e86a40007110150050352130100d00180b242007800781500e034030b10002c05151a00602c000c015010f00da01600040840c4144038043c107036a1070920040000c1c015a030000c1400070f90f190320f014240c0c2c030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 799274469 1250 799273219 799273259
    0x30f1403180108040203011103070207140904051906110a0c021206070f03020f0c0712050d0801030803010308031512030408010e150a050c0f0a120501062f0102160c 72
    0x1008114503007094030300007a0340764070860918095a841d2628000680502000c50480c45c080c0000003e00c174200d41c0000d43c0314100d401841140354440a0324040100401044038058201d400080d00700b00b803e8140540c21483d1403044000085074210141081c00c40d070494588000400c00d502d44140662411a03240c0e50a80c50782c100503e11840e1400c070003008007030b40b030b5590380c18075401050001c1842c80341d406985006e080c4100b2038a03c259034040104c04c5001d41c010503100c0d8083d283d40c205065118035411410789402461151969185990f540340581c8014a4002c401849400e00100c2d642c800f07000c008445c400da8000c3d521182401d0f081c3e4219503c050382000d0551000c0c800c90001c0104204141c0d0042102000181d9582d1f00105581180b0a494100c00c0c1407100041da41003c43e00b221403855085480380d01001180c0c1c80d20426510000d101400d048a6410841081404442080291941c81d080000541000c07031041c0c8111080d05240703402c440c402550002030140546054090000c0c2c6 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 799275719 1250 799274469 799274473
    0x10f090f020702010f0e01120911120f1b04020d0c0309051e19020a030f030306060f0306030818011229013207140c010e0103150b0912010501030f14 65
    0x10b250b640c0080c1410064002020030310218507004c400a030301641d01c102c0b03002840744051042c41014600030450186007107a143c4030b44000002c000c81c1402c0002d0889074121484010003e868500c220a111b9500f00810f50341e2180d02085404007048040c00350b894820b69a480216060140d80b80141c02c107643c603288800005840f107501d041d04100014400000c8081420505400d54240045089079000d500003030a4506a44842410154158450001c4644035034507009a50755450007282030754044c3c440500032010a00c445d40e4010200c0c8842150f000050412507052080e117112901900c1c05402c50000c030022200d020284070494050385905000d0920f070200d83c2070240c00c140703030421603042440e00101c80c0001201c500240c0100803200f01c0c0e50804510420550b003000440d40d200c00042d4118005034011000c021107500034040c01421640c0380200c011240e040c01d41480d0035030401c0c1c206a0b0f010b040c40520307502010b801c0c8140790285010320070401039840c060030007111f2020301c4001582c9075 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 799276969 1250 799275719 799275727
    0xc03110a0203041806080f1b0d021f030b03100911151615150602011a150a12020c0607090605030402030a150e0708011a040e0606060a0504030b010f090f02 68
    0x181e0101c120350940300080e03030680104951107600380003004580c0100c1c9640c8076840080f2211100010b11001d117108508910a413002a14240501c0d040c2000000307411a014040109441c80b8001e6074000c50f450f1844d0024010a025000a1400110404140c016561074450318207000710744900d07003100d2400707503039007043c0e00829400008184100344560050b06850081c0000b0440740d040324076207a508440c070a02c412000c0c03680d0140c2d0148144a9180598070389500801100c01c012024001c04100400c6a01d0900c414071100e4403030350212911008012a41c0f2a10300b18204130b00c003034001510a9402442c0074602503601030040d40c2141c00001c140001401000010790303000413414030042e48402e41c0e041e9940e0f405d034a04c02400c0d0360903181040740540c0343c01143c0500305603c0040481190505d00c1d01584031a42030108550714998289101d0304410006803540c10100000d098a0400e4034015107070170f03a2915040c0ca8403038280c00080b0405042c0d20100004032450140d01081c020020b030451038 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 799278219 1250 799276969 799276987
    0x919150815030a0309150e0306011205150a0501090b010f0c0204020307021e0a0606270c120518060a09080706050705070f0b09070501050406051611130b03101b0806040603060f0c0311 80
    0xa80c00301481504080300c0d0092304bc10820400381310603201e04039a881e00401505003240c4000180100740200c032510f17071800c1a81c1d25550705c5a04082da0400c86500d890385825440d400740006540001c10003425449615895000340c443c60300c403111a400300300e0180880344041e180c107000362079403603110048003103e150b500050751001580e4440f49410009000407420200e00702582e100c40104200302200b480c050800800e20702001d141400454201d090352502e545620300310080b00e00c00c0c1000f41440c001403040313800080d00c03030b0b01035500a1003070700f003260415083d641c0390040204030070421201c0003402c800744041d4201c10404100685824200a42810705200008040c2c3c080c0c9090502035a09003040d5100b441440003000d0290368025000c11a01c81c8040d06080160084420040c003a1280b604614805101c62040d03030030030b40e401d000300c080d0340c4040902103407200030140100307602550b21080000020301e148590361200c045510007241041d508440030701100c060007001044940208a0011 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 799279469 1250 799278219 799278223
    0x4020306162a060b03011a0f13020c03130b03011a2a0115120c060828050702190b1602010912050919150815030a0309150e03 55
    0x1a00400c08007441c0760440806a00711501601101c0e1080b0345107120400c2c05269035510442d0084501801c801e0104c207200f44107260803942c1c0303808a04045041c0b400d030145145041481d138800340400502c400b071044928884101240c0c071400c06c440c940d07400096540180481d25103210000c05180042e141598548059560002103600c21070449003000075984410110070f0200e01881540c81090305004111034940c1b42c02445038a1011000781e0141200061654a0205c071f076241c10382c06044510280d14040055a0301c0078080d10003085050070806042c03440030501c4408031840394042020446060000c0060300b42510a40d0800c070240001c8a031401150040c00041c0e0000d80f103104440b0180d800d210b04a0041c010110000c2c030385910441407548155200000c1c210300841140d145224444000da50410308942e4414407988450100e280300d0014010750500d80e114003800b900212841903a0300180c00c0c5540c0304003c41c081002202d0902c0070a1810040b012030310210b0628031020440100040c1d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 799280575 1106 799279469 799279471
    0xb010611010f15052b050114010e2419030803010f0b16020910030f1a07030c21110d02030403020c040b061e0405121f0504020306 57
    0x5140400d00d00c10440d510001c8400400c0451a0800f030042601702940300c001c4c81003510724180b804d910b88804100c54144140d00000c0c505101d62224101003606800400c500e00e4000304012401d04520700300c50060400000000da071512040000d000310456505407141c212041c0d10000820035010b0245060790060400c0107155034442102d43d00500406030700c0c1c2d0901c903034080003001506113000602d40158035071885c0103d141d260385500420700b12440c021a42c12006000145044050b04000c640102d45468180f204013103980d030042ca0f0030070103245c02030140c002e1000780030608a07544c004a014050300c0c4040380c42d0240400031400030f401c2140d00303130054003888851078600d2030039100340c40c55400010041030a240070011002d66400301e4a420b000001c2d0308110101c1c0560300c0401d03056280c0e82d000700601c1c114004510b6080380d5640c8801680804c0c1c24a0180030045e5800301c0c0403 = true := by decide +kernel

theorem cover : BRFrame.Cov 799100719 799280575 := by
  have h0 := BRFrame.cov_init 799100719
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 799100719 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 799100719 ≤ n) (h2 : n < 799280575) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
