-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5115
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:47:44.319107+00:00
-- url     : https://prove2.me/submissions/0c7650c9-46b1-4d65-a169-811aa382eca0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 919784172 ≤ n < 919964028 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 919785422 1250 919784172 919784189
    0x91a0c0912100204081c0302030f0708070c020d1b06050f0d09020a053c09010b03190c050d1803170405030705060c0702090609040c1208130f03200a 65
    0x2100849080c104150429184000b200b1980c541d00c548040c2d41d039407011051a104a882c0b0750100318220310a00969000d5050007007840903a840c0c1d80000d581000c00106040104100000311001680e034420041c01c1180c0141e41440c10040c400703070540081500c0b500320000f800780400c151503000e41c1000403681841c0c0041d0000401c40c01134030004851a0b82036100c0c5501c000a040c046c0304441c3e0201e40051005031001044110401e0170442010310031010310596840504000108461500c8000450f44080d00e8184064102c0318030041d082118401d01140c030000f0b01c00318200e1080340c5144915808502c03c0802c0c0d6044115070340d0000c0a000030340c02c088100c0c0c034000000c601007020400617039483c25170240c2551128501841b4850050708910710070f9100d000c040e8040f4820303040c4040010701654119000c10901c0d4100124500d030320207107500403a18213208100011900494080c0b8030050501703005124100c514500f802600e08080009224070191030325071812260341c1d41c0c0c43c40b00448284c0e0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 919786672 1250 919785422 919785439
    0x41205160204060308130e011a0a02100e07050f090103170901090e070206070e0d230a0c0803040510170403030c09081b1e03030d020318070306091a0c09 67
    0xe0025911860a4000094001e410702c030300401000001e0025000300c985a0502c5418107650303c0c0d0810340300303500f84500042d034910b0800d00840b02c184c0714000d00c04d548240c0100e441c511045d4272640106c980c0c0320b903400420380100314180082d160400c00c0c4000c00c40c0c22903c026280d41540c980314411000c0310702c20954410009020403850b40035055a400800902c01c010000749841880a500e50400b10341410004207059001161442c00c5000903802d503812001110b60001110400c0c0f0002c0700c07592000000740701760380c044c0c000903046440140140c130651015584513464130080c0b26660048a101d1400d1207501c24034246810303185000b180d071054140c0b402103284a0710078400c0d103c411190704409007070b008060421105400c2080c001020000c00c0e00d02c0080c0030742d020300003014031240d844c04a91503001008240320900050b0040c540040354181c0c40c0c021100516101460135015034011502a52a242030b90300b44900000d00101010b89031030700d20594504a05100b04605c5000e407c1c40c42040c85 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 919787922 1250 919786672 919786687
    0xa09050d0c08070e0108010609090819030b120a0203010c020604120c1b1203020c0406120f21022a01090302041a0310140a0603080f0a030e0102030f0a14041205 70
    0x4541c800c500420691042d2100c0030307150b02c004190349209004001e80c075800c042d40060f080e0118440c440d481078210084c1401c0c103170301e03101514482004005c0581010744816010031156903160040c0d01c1050030100030800c0456501c1414250f032100c0c260320040d0f4010001308800300c0e07032004e0340c0826042586410ba220341140e15148441c800c10004065500b00c0846012503c1a588140b101d06103000360201c411200c0203404210a6500c41d000d1070319000c03040e0100300c000030815501000070301c0c8101545c141281d2625070490100049241c00e00c0142c2c02001c1802281110702410b03a55043c03000c20b8541c0d8104080c00180040346280310003401280e4a11b02044450400054414441d80003400d0780c0344044c04c10700701d001400e22040b1f1321200984076004144030b0005c0b1302c10103045951000c915400c00b55082c4659005411000c82001030646a1072000e41021082c4015071144400802c03452160408500d0390049901c03007000c000d02c100c04035050001186048004150070002c601c0c100da0394880 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 919789172 1250 919787922 919787933
    0x3030c0305070f0c0302090f0403020705040207050109051606090906051c0203150408030951040b011d0405120c0705030a0c090e1b0f0f0d0b100b0a09050d 68
    0x1a0807026110021003a500400c01c040c4c1e6040c90b049074001c07540101c0e180c45c1c201410364080070544006015a00800080029043c03d402418801e8050030000916044940310142000401c40b03860b5056000c1640070b00006030004042e402600100700100041070826002c10550742b80003180e200b41000d801c8100c1c2c1196000c00c5403c911030100780039180c1c1d83c1418034042e01140c00c01c0d100e0608500454a54500341031311007060700d5140004403100349124800304070010110f203282c2c44000c00c410b012080045d03141594003a40340542d20071070070344606604d402ea0484198440300b041031424800c02044c800030072400251101d07203544081c80b403556046000e81051614110b03610075601030068030900014031904020074801c0b20100c00c0140401c560a05549880d511034510009149074107120442050800c5007584941c1c8002601d1320903640c3c40c55001500d4030200d4201110440d1075142040901c00200c00c1c40c0001301140007005042200201c806010000a1702889000e400e400c00d00d98140302 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 919790422 1250 919789172 919789177
    0x1b0f030f0f071e030f080c0c07031e0803100524070209060a15170a090510050c090a320d06200705070602120403020a1401030e0102130f1703030103030c0305 69
    0x140941d0040f00c501d8541c1c5005403401e1080b201c00804101100e0000d20002041c10443d0040045800509001ca045035952408140103404088100304d001c0c040c41300060f035075070085020364815400600000e01e01000c02c1080b0005410344450418041080401d985032107059411301e0364121000d1180b962030f5004982c16504691010b2202103842070244002c0b500000003c0503240c801800030000e654406000f000d44036002d82c001c0803075210b000106410103c036400280c0290361042c8852030600c001e000500c1402080d0803040c54140c00a94208a56003640607040a038141c01640f40b60050510000929800004c9000340180d5200c01d000c500184041050355515800c80b0113143d25032455007041c035603c0302c0c280554005803066000342030050b1003001c141d0b0102e95004000710840f074100500b031a0628a941a40750503d9201e0108140c000000c1c0003a1222072214403071402250f140c4034070752120084982c40112010b010700b0340c01040c034802008403410749805080030744400c86940b0b401c03145803 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 919791672 1250 919790422 919790453
    0xf0f0304060e0118020109080a11270106051b150136240b0913090b1812131203090b0c0714090702060a180204021b0f030f0f07 56
    0x194a0300c0b2441351800860000f459003d4003e9943c1c1c0d941e41d03201e440c0981d956040200c054503014505842810314078040d040045110206001d04011450240c0c1a0880c42e4003a00b04402140020030941c110401c0743d400700250301c0d507101c010700d03260494503402405014180120030b40c42d2070942003000c021070028192001d0404c441ca410fa0728001c084668001400c4501c0a2400900c1101c88a0325500110304488182c1d500c00b03131954680740741b40041080d40345000403c10800e503240d119500c00b2801408100d845161940460350a401034050804e0500380d1100007582a06020302030204100c60381c20380f441c01e59082030012034410b10541800d0b2290309031075010307402d05d440000381c40c4105140825900c01702c404021030100ca8030303c4202003001c05642215807100507807209002407080c0025800440003007032140b04102c0884c1d52038000c00d05981c02103000c400e0b0485900000740026000b00254001b42010901039410080041031100003803050700002044e5a8000c5002c2e000e1001501140002 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 919792922 1250 919791672 919791701
    0x1204030809031c0e0c031c05030a140702010e21030c031005030a0311070905280b0607050a1a010e01270e210415050304050109080307020f070504020f0f030406 70
    0x6000e0f0f1400070280940c3d91454189010f028140245804c000034003091290407010503005401c400302c4111440d4100401c4c0d501c0e915213554904660b10440d002890090b6040c4c0e0020421005101c4004d01e001d2013207041010000440c130343c00240c48401c0302030f03d81011080c0100f654079100e24245000c0c64003143c000543c507008400381c4c2020980c00200103148070301c0c003e090b40c403c1c0e0703500c0030050220b8804680c80c030005007440504215402c44501c00c110140410440080c078000c41c0c50108045412499049402d68030404140081c8164244d042c0054008003000101c1981005440204840c0602c03403942114092620000c80549110785204140500501003140c100710348600c9035100c2d988401c856400340c4440c24080780b0200c140494090790a590705007101c0c4401c0c11002c507020352000b4415100c555a4040620000d50350000a41c000e11080e0f0050145c0c9040c3c0901600b84074082c0c1c0306030b12841c4100f003003100301e55000e4191245100310075922038582d41e0314144503001d070002d00c01040c0e0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 919794172 1250 919792922 919792957
    0x1506040e010501121202010b060714250f0b0c152d0f060a1a0901120f022104030c02040c170403030f0b060c0a021c0f030c021203120403080903 63
    0xd10700d41d00e900752001c1901a05032518500c85040701070307080702e5a90030000c3e00724004200d031801089107160300541c00d0561504441d807001d58cc1094008070301b168a59901800117240041241280d000c1258016249140e81d00707141c00b1580480558442160324100029041032000903000441c0d1502046600d691041c80c68021401c42841c1c000c804040300c050000c0b240306408503000f82045100c00c801d90f48915515034981707010b200404210341004010786d0400184075491860b240460150606024415401580703030595800824025040e070402c48440c0038802081002080c2d01401c0d0203846501a0f0300040c03c40c01140c4111a04e0b031803a501e00c01142800c03000d0100b010b0345544428070344000150104694541c96041008902c0343c820807080f5540180685409407a1030f51101010818040301c01444180c10760b1034200c56400080c0039400300381c010441e0410350600e03040a00c030202522018601c0e0040ca071400702002c1c1e80c098005070400059000184008804004607400010748482852 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 919795422 1250 919794172 919794179
    0xf3f03130204060603052a0f0d0204030c052218020907110d0903020a0e0601110f06100b0c0607200a200102071802070309051012050105121506040e010501 68
    0x149580d024001207015901c0c10b240010030038030901c140c50168a040c2240051880c0c2c00300c6d00d1028880c03800c0301d4a1000020401516904507a1004000ca110a4a8056111440d5007000d03d00b003c5154480c80c012040650382c0c80010200e2a46148456407034900041c40307801405185170311002c40c280003500309580806108041c0c1d08906d811400f40c1090f4100c80c80f880d40c0d15022110303c100c40c84000c0d0401800141030081d00000e0035000c0d84080103150001c00903190000513850718103c0040d00b000c54000400b440781c912402540d54010307005050311180f0b06100030042543e100c100800640404c180d140c107841c0c0f0146000001c03401c0f42d4202c02180c0114085003014442c2000b9000b41c040141d0582690b204c941d4008076900c011074030500c903406002d00ea0400640042c1d84030a008600300000f40340041070564039141d0303c50541c41142c1d1030707611000c400041d00b0200c481c1a04054401c2603840c418108092000402800c00780700400780e6881929080003040141c1400799441107554200800031 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 919796672 1250 919795422 919795441
    0x40e0109090c1a0d180807030504030c090507120b0a030c090605040f0b0d02011d0301060b04051009080d0f09030c030b070f08010e010b071b080607020f3f03 69
    0x7400082d00407480c1c103500c0c40e5501c4012088461441c625000700b1000e00000314401034640c020030344801825140790720880c041d524043c06500103a421404650081303824000d003e01e40001c2000391080d500100003608000d030010300782880742480c81d40c000b0b0715004c1d101e40310745980b5250300c011544100015501c68541e041c00d80a4022405414000c0e03142507440070902506005200c046680a440404400f41e070740c00450b00390000003c0032010410b0f10140c1b4601d91800d01c0741078001c0050612142d11241840104001c400301e184da02e900f0009015001e00403208081140c8042045905200c01000d0032900140c0d2402c42a51000d014010040c10000a0181819416215002c0e0390381c0e01b1a8200094410b45031500c0c00e000b140007444108005016a5894100404c002406118010100581d000e030400c6294007940104680d5003082c014800802d40405c01d008200c1c050780c4c090481500703010b0301c000c0020155a80710104a11400d00c0000d800f580c2e00102207045d100345181660307460300b541c00 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 919797922 1250 919796672 919796681
    0x504051c0905031209090f070207030b040c0302090702030c15100f0801020702040b0a0e0c0f0c012309011415010311312301111605090901060b0d020f040e0109 70
    0x1070501134040d8144c04010100070740300700c0f5500307100281005c8503070301e40d190001c242402c002d00400541c82000004400308016115030340c811032064881004d860f04520612003015000790110003954818001c81c5054a00418421400440205105503680d224800750301d1000c115800003200d00100f0b40d000c1030400041d0002d0130140d00aa4040c03020084801c18819086450300c07409406c0080000801c5403d02c11034001c0c039122040b503440c0f034285911058550300b140c2c1d121a25500ea008000040395030420200c400b1030784902042c00030403003911480881c280840000301405c0c030700317008090383c0c2e08260b001b80d00844c25400e101c01347c1c07a110140c039150b202c45904100110410441c880c610050140c174061705c0c20007990040001c0d803807214003001001d52501d100600f2a41404034240b0003903940f000030001c1d402c0c05d0300009403c0e202a8508001e0040344080a00500556410064144154080301046400403070710b08400503501d100c1050a20920700903030b0001144441c7c81d4000103229074032030b0031 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 919799172 1250 919797922 919797929
    0x1920090403171f030b1006020304030302072c0112021503190e0f03030405030a031802100e28090b030706020d080a09200f0f10050d0e010507020319080c0d0504051c09 73
    0x640f11b1080d44138941a0f81d41e0040d8400200143e1290700140014030104103411000204040221705030742e00030400c40030070380c0700340c008081c8116455100780a51500c130528204907001c08210614600344810500c50424001150350003e5865416a040101d01080080c01201c04a400e60f6100d082a00e805900d03036000088000c0001d040130440202d00150b90050b042c0190f000f4100e83c2d000c044404291000e4403840991503014422034500a0003280e40d41c15000c041d0314440001c503c032400d1a0810040382c0c0100c0885020742c0c0141020700c00c850700024982005040d9040200c0ca0344c3c0c2d0104d0711005803845031f000a210b40340c0c2500701600c00d10300d4902c0040c2d540b070403206000440340742c0c41130002000000300b07040c0c0c0c004804020385000c1406140240384040c4901408903846440008280c00c0d039806986440059000041c00455100010340342140140c0c00d203000c0d10103040c0510110b14502903510002400d5503144045010003038200000307090501e100141e44076018a1340c00c00b80821200d4407 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 919800422 1250 919799172 919799191
    0x100309120906050a08091e0102131e051c081810110c040e0c0d05070302190305030a030203060621070f02070e0c0a021920090403171f030b 61
    0xc0151030440c040d070200c0080c2d8403140e4620b030130115215130403280303940701414503182c0d40142d109030701d00d21400c0324954060400c50000503a90700c80000d01c02010301826804007a50300c0e2203030310030600b03984029240780440380100d0b2580c0b202500010803110598000e01c000b050f0007800111a0055030503503503550400c0ea400c0760202c40e01c0c112410155088107221220400f1501300c000c0c0f0b400e441c60507900004c034001c0c04000301d90071884030501041c014403074502c1c143c48583c081182001185000b52141100003a04402d070581c0b0380c0303195100d9a40f4010fa4100300141030300880050551f0b2940c40a035481406201d41c0b40c02c0c254205105a040a0b07400d4509030000b1b2007520062041c00c1c000140f020854401890444056840300c107115600c2c3c1041c81e4500843c01101c0005164441d115402d907a5240204082c0e010b5000074140b400d111442c540e0b1050041c0b0506040001213900000c2102414008245000f481e44c0c40b04d2003051100804a60803012500032032011084c02a9509900d21407401070 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 919801672 1250 919800422 919800443
    0x100e04060605151213081b010501051203090604150302120403030c03142202060c070e0730020c0a0c0b0714070506040501050c01060503070b0a020105100608061e100309 74
    0x612100280d02c2100002c440e00c2c4104c50200d8402905840c0c0f03e1240c074005c0c2c00d2203041c136140440010076100c11400e443c02581d1030f030005005618001d03030100b9280303600324010341c6803006040200c0d6040c0118030550840c8100c0784d0001ca440342c0242c04590085090841c220414600340c0350140042405c8119140042e240201c64150701140d40b10a80c050841d21000c004880e009882d0306000d1380180c48200c0e00000305004c00e00c400402084268046c1c41c4640d1000b00c1031400501c010b03ca030300c40d03441e40c405400281e030b5800030011902450280c0c01600c2c18001d070b42c810824403402c1c07602041c034400070680303181a00005401640f000c040c1c10460301c9024500588043c540301c965841c90240549640300d9000c100030800b66001d0b10051a240449100210748140d5810019040c101254481c180b09000051a4035505e6428811280d00244000400c02040e0030305000401140005005902a421050f4541d584000307028a081684100425540050103800b400401a101181c0f0440c1e00722a803 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 919802922 1250 919801672 919801699
    0x313180603050106300b15010c0c030f030f0903110909030c0f100e0303010806060103020a12050f0a052202130603170706051008060a09030903050a0303051005010201020c0a0b100e04060605 83
    0x2c08004001c1c540d080f560003030890700d0300d070b29184941f280d2083c0981801202100c000010f00c080d4080801140240d40c100d014181c24100907004080e0f81032010200824a0018000144021201c110040040d01c024483d41c1e5a002d100d03146119a00340b06001c0c1c4212840e0810400c4000740400051702948414020701442c3e5041c0d60382c0e40000c1c060074005800c0071000503407951080d03018003000380045c580800c0d80a11401031200300d9400b568841604551203042052224039400b4240d0415090800502c107110303007000458904a100900a22070389500c610907a458403650880e0340030f035801003503200c0b402c40207415243c1030764070403441140c00c03d003800005540594a010944115400c480c0030b00034a6899003007480040c0070403030003101441844000400400c02c1003000081d05442500c002805040c1040b5849c00c03a41103074480c5046a0040010482000d0049031080d105a44084825850386613000614404540c50b0841e0000c40b000104100034828540c204404aa9040d02c0224074100c4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 919804172 1250 919802922 919802999
    0x3111b0f0f0712121b030527180423100c09030c171f02090906040b180c090d1a06100c081b01020c0114090313180603050106 55
    0x6507889862545016021000041030244410802d004c03210700e0200e2940c0381d50454100b0711000303001c003500002e00c0801c5a142070b0b004100d1084503842405107178201808942d001902011100f8406105013585102080402100ea000000001080110122005140c0f07241e40d903076030324610480203180d080c9011300f50041e000d1340c1e4020907280c00a038503c070414140a01ea481c01499103490000510410302600950308181c10041d980506004d8050380d200e8242040150741040030341900d208514000070081c03603a13a01000b004440440000b140b01035500c3c1002e060326401101506034002050388800020003028603070002c1c0024a5a01100090f2110310901c50308004506d081804940694441d00c041758007000a03004003d40403441807440c280c031650f29401da82041c3c1072002135a4540000e141d00713040c5000d07174a0b8000c111030b00175410801000c00e44414110300e4031400101c40c1e40461012495549600300ca0080c640020081c0700d820707540c103103070810801880e64200c4460700c00200c4080510 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 919805422 1250 919804172 919804183
    0x22d061e010605070510020f0d0b1f27080705030706031802040209040207050a0c0f050f0609060c07080703030c030f08041109070e04050103061a060a0f03111b0f0f 72
    0x80d5048000850303082070000d42e90369011400594091240110414081d405030004015070304096100030b403a400003285031070039500c041c2c0c001c1d0b205d8107220345841070600a4031603807903192945140034594030340d840701c880542440d42d001ca100b8004848401052a410000b0901c0840c1c00c190704468a10741d031082e04400311003007070710705040355a0b4100a03480940303040d07006010507020041c4014a8603801c0d42d038035450640a071004581e80c80c0444002c000041c07050000000812060780c03080740c1400e002e00041c203244144041c80303210714030125400c0d01c5404100112005405a07404840c00b01c0e0b00c2e0308000e090405015011800124645400c0282e14451038000d4050781d80071801c200c03103905290410220b00c1c0010508801c01600c031041081596540c041d15000710b0003407000282e8100c400036403280e181420300303142e40600c400b00030480c441940b08452000001d55490700080c00c41c0d1070010700e0003900c41c92101c500e940f008003900c240302410108800f03080450030f801700c0f00f108802e00c80c101d4464 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 919806672 1250 919805422 919805461
    0x204081903080708100e131b080a02041505150310091e050403050d15051302030f0411010e13050601030b030613060f0906020a1107050d081603022d06 66
    0xa03100101140ea49400303565429041403c20507140025510f444850301c500350200d9105000110442c120424028020b00a0100c4a00c00d86010011424209c805550b8009400000d0260f80d035070701c120103d25071808034613018100081118000300504070051420b40c006841500700070140142c00228030b10300744915600846030035003060440c8508445c0600400b0010010390602c02c040000f503041200d24030850038500c502c1010f03910340c00e0030700342400442100e00c504401034600c10002e0045800e02c0602d420fa016038841051400000f1184c0103c1e41c401402c0c4c810350b00300001d41000b1981c001260405840303814280e0b400c100000c11201050b0340c0311001d0781c011120301480146240070401c01d801c4090000400c1d01c000c50106150781d5000100d034041061000010700c141c960710220b801c00c1c0100c03001030504941050340c44103075880300c2c6041e114170044019000c450f004802c0c10140280f250130b007540310f14a10b2403043c8904d414200d0307030a180c00c00f4102d40f5000b0200021980051004400c410 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 919807922 1250 919806672 919806677
    0x4030c090b01200c0a0f030515100b07050309090a1a030a17090a0f0801060806070906210f14060f040e2104090e011e0b09040305090a05030609010204081903 69
    0x80c83c0e580030f84008608500d08500c10f0600420a039a1484c1e20b41200785001002d41142a00840d455424094200200c01148180c8a500c580c2404810b100025840e02a01d6000140c00e0703a82c100c6241482c80e6114101280360481e02c46010045001000e5201c00c1114902c0c0c01e821421a40c03040400d601c904030f0303201c0200310819409a500c1e401010070040c00c0c4045015010304003690310b4000214984c1d4042c2c0c4403a00e203079190394090040e180d05104603a08001e642c180000c02c2c60400d48003510541d64464000c2400c400842c1542003e55190003031340c90b0303101c190b00c100030494201701e11314cc80ca0b00c220341081c020070070b48003070004c282010310a0008400c1140b0160280d01c5403080300b200d21104003041d03410040000c1c0008a412038007445080e41441d60704000180100b841900012042035000024000d030b45006104c044c2c0d600c440126036441a0b042c50304a54a83d420400030f1043c0c0300d10b81000fa0036100d00810402030800550041c4107490141c1f00701e074902da060004100e800034064200500 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 919809172 1250 919807922 919807937
    0x2a100b060703120b04020405030a081902121e040b180f010f091e08060901090302070614071506260c0901030f030302030613020307020a020906030f07060e1f0504030c090b01 76
    0x4040f0784c88041401030042000d07280c07a546d500028079040340300c0010b84400e01d0005820100300e22400c40e81782694910700141050b42d403410b800d080b01d4024210520140e01301141c514404144050840b0b025100415000781c51b101946004680b0640b89104030340260845c5000007040c0d03002e564114414061596142d00650a02c500c1d00c0e41020701940e80000c40342e2000c0b010411304800d002080c881c200072000050b17510001d0400a103022859400181800325042501500009080c12918043c1d00001011030215403646110002c01560703001899400454164481d4000a420031a42030003002c400c0360111410f0b501003000b00030b020720004140c07514000900380024021740103190f1041c0000c00b0400314644485042c41681d000719941d0006810060f040021031520340b540340c0c1c110380141c00500702c800300c12150036034a0303505000740014010001d6840c0c09035038071a06c4040640d128848102100c040c1480d002d000c030b0f00a80002c980c0c8404810740480e00702c5042c401c484050005944c0c018 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 919810422 1250 919809172 919809197
    0xe01050d0f11031509100204060806010f1e02030a090905100e04060921110c0f12100c0810140303072306010803040911071101052a100b060703 63
    0x240d41c0e03600d0102c0c0c03090800d01519546603801c0c0120407441a1420040402e442c181300380f00c0c1490214030103051b034240305000a0200b10340c4a81d000e64011800e007420124101c05542c144c88140d104280c0200d130754401d080d01240180d0210160001d02e4040d112004e405031074044400c15102c2c07c403201c08811035000c0c0e003003103681540c101250700180540c1c00019512070325120360f83d0000e405204400c920314021904c40d801030707110010140c0701100c40d01421642d5001400200400d1144d11005d105408501c1d6400c0e81c1c50061007034143c2c00195a400300f001c0309030307004060072050003102d82c550000031000000804880740e15440e003078407000602440c60512320b42d03106171f50b04030031407030068421521b4800760350400e508103c0c942c041c201c020000c5850314a88070401c025203050b90501d0303010b00c40a02100000809a000c400303d004c01c242045510744004101780300350101d079007908a00303c0c0c4e800403645954940104081d000994000402d02c441c004201c2400b90030b100e03103440107000460110201 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 919811672 1250 919810422 919810433
    0x60402010c140601090605010e030a260f180901050d03020a03050f0403060f0501051302040b0f0915070c06080a0920041803020313140303030703090c0f060203090301060e01050d 78
    0x10624402c1c00e2800050031000403840c81c0c108260080c502c1243d84032024041581c02a401d805407010450007007980c070407941d8810f04105004859103071006071000c003880d24060402d041c4c0f6003e9544486030b40d21a0101000008045400341e00d00e4002c1e0300d4140042490704090100340d14542c2c0680050003411440c0c0c0d01124141c0c01003c0c4032a0204041c480840080c4980c051108150300c5003601151740c1d4109810002021009088038100740d10400040120503c16400c0d80d07102104a02d0341c40c1c032410300ad00445e442e565401c0041c0c003030000010340c500c1000502207811060b51000d42e11207201d079417440a100202d89501d00c1c0a014010000c045a01003030351500c4032540074101400102c2d420702108400700c0070040c410011000740e040868507501100d42e060b40350b002480c070421000b070801e5012020903103910014000908141d1928a0401030015480342800140b180d4940c500086030b980700e00035201d800c00072203984254203103400011800085009181680c10050003204801c0303055640 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 919812922 1250 919811672 919811687
    0xe0f01081b0a0b0d0203040501060522090804091b0801140a05040e0f010507030c1416082203060b1e1c0312020f03040c060201181518030302091206060306040201 71
    0x8194401c201c1e100c08584990003030040c107a5907942c1140035860b81420f24005080d512b81e40c00803801058681c07003007001c51803500040c882411002d44c001a0f00249414000118402c40e0007514145090084200409503e09409404286141e80e251007598a40d01501940030f11016040c1d4440640e44052020345010f51000004040e4481110400103500a146003543c0c41100c000000c43e9484038846110398100c0c07204111384e000541c11a2034a05c1c402200305002c0742c0d541018211210101d1300600381100000310014a589070440a1a4266603281140140c500c0c0c85506002c0c100c0070110140208801021040580f0020041e9201513071f510701c6e0466110044000341c2c108400441402c9050300d0a10003000b005583c1441e031076032441c0c00d0802c00d0b003001840e448002160726123464031054403000443c0d070801f20780c0311913039400580120202318042c04841ca403060040301010110f000b0903402da802081060b0003500c6684412044000503a1102c404844071038054224500007801503114440c03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 919814172 1250 919812922 919812973
    0x10b09060a051e0d110702030703060509030d06030b07032301060e01031814070602030a09230306090601050a0801020a1e031803020a030347030102130e0f0108 70
    0x40c003038148044505190f40842400c08050780d54500040c0e01c1d04440c5060160401c03c4020311102403404a1990100399207030854480505810798500204400410a00440c4c9903440c1e240c5007409010b4580c1407500764008103a44130f2001c80e20380807a02c0481a030504146407541180303004495580e02e414000d0310034001c11183d141c10142c2e280b20080c01c062410241001d0b40340100c5004020070611a0894070384405a0044015980300303110411100c1c0e400016039095401d03040a5014a802074200c2181c50703030102c4a81036241c0907100030001c08803c001ba2141c101c0c0d00885840003c143e462030240c0c201d20850035040000f0382c03406021a020308810b11054040c501a240000381402a4501a00300c2d42c42e104c0220011f8011445250505905004903c005403480781840c0c100611a01d010180c1040d180140a042061038034401c10481402d2840814010140c020365031800f090186500080b081d00908280720011340205005580b200e03a528141ca6002004000c10404002c03002d0b040d520500 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 919815422 1250 919814172 919814177
    0xe01030b0f210606030f280204092004021c0b0a0305070f080f0106120b10080d02030403061d07060c2f010f0e011e0909020c070e0f010b09060a 63
    0x10041c00641d16503840658804040405081141054a80d1103041ca032010741540e1180c0c0c810700819000c0c031400325100e16641c01c1001c504201400840d43c800c4401c603001c3c00070f50700c41d00d050f811721b082c015032000c1704081a091405c903290044154007044100c0c02a21600b85410000700c10b8807940101e15485603540e424003c1c00727001600d50b6036481914101c96038010007002ca040c1e030820070018030100440d41240c49488000d000c414200341441c00200c1c58180082d003e0050354010403202d08010207250042c1901d1400c0d0784082c40c40d4800656690700c01d1104030f81c40c0b807070007125000d0700e000c521448a00c200c12402601c0550b181140481e44480111000c5e80d01c44030190250303106064030320421012000c180e18078580b100490b4009010306900c590f5031400c0c090700c150740403038070f0303030700400a04101c0e0391601c40c5029403942c14021148248150059562a0b2000400804061001950b44200c9441d0a40040c1c02e80e9032500c01c034604e801c28402d5000c61201071000f8085450030f07a006c1c108041c2c040c03 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 919816672 1250 919815422 919815439
    0x908100c091a0918130602090f09100f080f060106030510090903030603140105060904060e010e06042316150c0206030a050406050106020f0c121f050f160e01030b 71
    0x4404a0410420b072001c00295100c0c0041e11000c1d40c1000c0403481d10045000030748840300e152070040700e43c001000740d900403c1340d980094100003d070f03149000b40200e4000070748010218908000c200c44800103a01461551000320707000060341c10750018103007a4103403a82025007090f03440c24a0650207404090110f95003080480c40100d20b0912a103d90b08885010f950080340851070350610301c00001104505160300c1e410708042000c2c03915a40c7e4003a400680c895400900c4541c0400b0260040c070300d4407404806801007a05110074044043c208622100c940c81c1018000e00c0f490f00c200c1e565440b80c41c0c501d4080303000345e2001c000a155141010a448425051410070080c1c5640081e40a0307000f101d0030748925949409010034401d01e84503560141486000515880c18a155046d598034143d80b85e152280510441442c0e01501c1801480c07003464061040290110001d00414090442101c603c203550100d54000344034256042104240100c60b40c0340e1440c050903460044010705150401c1c6034021480 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 919817922 1250 919816672 919816679
    0xa0e0418080c030315011b231504050111070c120203031903020d1b05040315060806070f02060717010e04032001090212060103021513120f060b010908100c09 69
    0x500002c05030049407070040c0d940d030b00c1c104641000d001e441d0103441d0b04000001c000f0078003c940248202c072030f15030442c0d101041c0b441c0d070b40400428140c01d0040554103004408070801581e50742c40000e4000c80c4a100240045d0120950080b0b00c1d019000018001c2c40400808001001c1c080340038500c0b80e8005000c0d40e00c0c3c07410203003280d1400500c4044407000258009001c0021180d07620600c03102800c3c0404003038018a00700c0001b040350280380000b400c0d17180d20600c601c800032455070060005001c40402d540845c0350015025100164811900016010b139600203034145100c4d144c03805009000182c540140d900f0b2031240021880010b00c1102888060b101d0b07003a603010031002514418148074008200030b92184103024080c491079004034004c1d402140180016600c100e4070714401060707240a00d40b83d0340800d200611002d0507a2111000005500c42c40c8180700089103145117480c01141c0501480d00c847c40116811101da02c141d400c1074110250540424416400c04644881103241c000802900e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 919819172 1250 919817922 919817933
    0x309060309030904091a100f05010f0203160605060114070f0f0503070c0312090e010b18030a0c09020717190315081f05161706270a0e030a0e0418 64
    0x1350605c080c1c40e511940c42400d101c001342d24058640c840c0301c01c014004294500084402c2005103070140074140403100100350042c6108006880210210700518000c00a050800c040184003d88415000418080095a40d104100c003101d50169224103000074100d4161a6105a1035041d8400c4495002c00c0002e9808500c0e1541d110000c0c41c05400b04405aa111203c00f030041041a405a15a40c000c00e004000401128040d105102030340015210810f0200c00040d08008000a00404141e0030000108010395264050400d0328403c618003a12a903024104403041e02034111508051a40700784600c995610039040500d01e1741c1c1007420300c0411600d1f141366500305030880038050620340000c0300d0301442c0702050003803e801c0b130310b0140b10726040741c44000001c005401d08170021002103100c002056480c0c40d20820888031010540c2800e511111540d10301080356015200c004c1c600c0d04000900b1080e100201c12100440859182d4550f0303d18110240400b50960b040c6400740f11031450404004100d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 919820422 1250 919819172 919819181
    0x41a0d03080105130e06040f05010921032d0b060c0111121308191e0f020c011416050307080f04150e010f0503060427060b0904050309060309030904 65
    0x144a5200c8072a198100000e012100707480074000340d003081c2040490b10444c0d8011820702c1e000780e04012151203892403030408901500701480001c20703141030301c2180078101c3c4500314010000e049030755081c80540740c03004c41d44424595440084008400401150303848912540c008511000e0103400c2c1400c1402d41c1c4c8503903007110f40c002084946c5680c0050b5480d5042d040d25132003075018000068140c0300c0d000c0c50715000c00c3c900407840580c1d1101c0070031402280d941d0080411600040070500404010001801e000b421004850520b05c05481048090411503000e520700f0560a1301d40c012030343c1464203060300444042e44564050301e51707000c01c01444002c103910400130681c01c1c2045a80542d140c1c6020015510846158069001c01c031060340c02d4411aa486400590310804628105490761202c0000030b00400341c910b0102c41c4501c0078075421680d80c2c9190301d112071082c090342c010400c400d045404e200003180c08440041050300100138480c128507118015640056680341145e040c01440d0022504a4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 919821672 1250 919820422 919820449
    0x40f121b0f0501030b040e0303041419080901020f150c180303130503061501050702040506010e090f01090c0203030108150910060e0a1d0c040513230c03030a0905041a 73
    0xe05162002c0c0705958141c003030400c58000645041050029180c16551207010142c802414410954101e00e0700d540c3c03c00840c680c01003007220590752401c65290070700450340181003590240c0503c414040c4481001f01d00a4030700c010b091500d0a05a4503101c0381c20240d40502d031154600150b5081813115502c040018010018a94118000c100d0402007014603082c4000d11310f03000b092640e008041281d038010107551507180d058070b0204043d150400142d42500ba4070a41680201ea10b8040081200280d10064100d03882d19604200d150480001240c4034072003401606407a9110080400c500319991080b03d80c4020020f090380d16484070310701b45005541041c0e2141d07511036100c2041c44441d01d840d02c51015a910102494a140c11211001c20345a000c80c06a0300d100d1584c0b1070018060340802042e800c0c00b61360200b4601c0e11800d00c0000d044486ca03c0307a4070480507206250f031000751418000201d9502a20725224020070a00e081c04100c00340c140b807003940780c801010400d500100e4440c1000c0f41c00c2e4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 919822922 1250 919821672 919821689
    0xa021b18190e03131809060c170907030f0b04110d0501020a0905060306010c14010b060d091704050a0e0702010f021803010c05032406070212150606040f121b 69
    0x2060000d80d41c0505452801181c1001a0401c01c800440341d030103524180110f0b21448400d600000900c80c03968001c20304030394094900b60501c09040101507010000c070800c1199900c480c1d413691102910381c1d41d40d221600000341090f9800d1498004540c42c1500309901c10310070980802060b1207c0e0100300300e141200c600f00c070240e4000c00c024464a030482d4841000d0203089e00d0003821807914600080000c00741c0b900c0038020460707561034185c1424083d00800804180170f885541c0e1103612100150040440d444191082e01da000d4120501401001c00c0300c00701e800003098075120300e05141c4404501c1001620544c15996100024100440325002800b01d00b8000e0810307030310900c843c605144c2514601300111042100c00c00c108544041c4807411854014551358003221681c02240100c0c01c0340c841c0e840081d5004582c40c456034500d50f0000742e00e1000ca40f010700c041004c0e440d06020b1203524000c6008104420800c00000e2106100070314420b10710074003858200340411003c0290b1038840105c0d4104003031 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 919824172 1250 919822922 919822951
    0xf0602030d0e060f0610030b3d020c060a030905120301030b0f0c0a0f0909050c130e0906072114220b0402012d09030204110a021b18 58
    0x1c03080420301c2084401240d400c00b800360b078504a4003002401d0700c0140381a1069500028281c1100d00c258804544204040e0404410340241e00600b9034001420300e20b540009a858081840c20724000070328900b13000303240c008005200301c40c0100005600900300400070150750b100541c002c01c80c00c00900e100404440e030703040d542e9411401e159480c110300803d517201e88010b10703060200c000da240c1c04482000906280011000b41c00714400c403814801680030180c090304141c240100250444020300b80b0046141d490030001e41e85024080407400c00b01c41492030743e0040c1d0b002078a4070b402180c406200803240b260709205031914044400460b0317182c1d0400620f4844e180c08010500c1410803400180d1710038001d16890320012607a8002071800000c2001781003100c00081d94484034030030505141004000c050405020070603550040606413907200503485603080c01c482e25031110122044405070345c07241e4041d10001d0040d03d0760300180c400303540369141c00001036600d085030303400310150780c07030041030304050321f14 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 919825422 1250 919824172 919824187
    0xd05070c0614090a03052208011b0216050f010c0501090b04020a0f03082212050c030601060309120e0f03010c030e0f030a05180a0902040b13150c1502040f060203 71
    0x412510b245202c0c81c02c2e00340000c103012406030000740c1070607440d52604d045991207412420000070800e0340030490341d00d5904c5400100f5401383c10740107043d822942c40d1500348080c060001c12a91081d03040e0b83c11488015142040c0700034280010750b11006d000604001c240c080c400e03500c050840e140100d040d81d43e203032900144011843e015070090000c10115500c50032440c00c6892300001449003454203010f14400300d541049411102114000034450406020a482d07100d0425a45480743ea0341e2080c4039028140012400a0083c0b0802143c65000818811445039440c0107540302a20040d850354080c900481e426000e9900b40501752000240d550007095003a8a0984940f804880718404581034206014400c40107901c0020f031440850204582405500007201040d80d94043d40c003c0c83e000f81c000140419040b16500041050040b004820b98801d50756811641341d410468140600042c55101ca040108403c8441d0341142081108014902903a9502d42d08940e1401e0f400000980c01c00b0a440 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 919826672 1250 919825422 919825433
    0xe0d0b0a0f050709061205090c060a08012405070f0f1b0306050f041218091a09090c01080610050f040f050310020712051606240b0c10110d05070c 64
    0x1c1c0c000031a42000041c182c00c000c00a48842d4885421006c04d65551000039983c1d0340400010700d09040c0603080c1da0783e6244440d0001c0180409000f142200351100e41241d041204040000500d07001c640d071900e083c030320b496a404106008454054a422051054110201d001d01203507015620764010060a000c2c5107182a00030fa6500908001400700b40c90200300c0400c2c81405000f000f02070500d00840e42000d800c002c0340c4a4041d070380251840c10b2030080c0090a001d8258100d29010030212412501552802d556685d02d0850002050001c0e000c100452a00e080100e2001c160990a003040c50401d00444036035035060304268403c0045115511040125042c148101d01c1130384d042020a40c03402c078250f05c5041040035001903020030498001426800c80030810300019115034443c6060195402400754020220319142c0d90060540d084a03001507050100700498601e80151006003510f0030702e80e0007082c0200082007400181e0074080250710407015a600c1401e124a0782d9407911000ea900c5810003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 919827922 1250 919826672 919826681
    0x50907031b02010f0f09110405070c0803090615060c120309010905122a030f0304081605010c1107031e0201050708030a02220503100f061e030b090613030e0d0b0a0f 72
    0x5505c0001e1600e42e080002c0b915030311008502403025180422552290001102c04c0c50b030b00c800240001d100403051007444403001c24100d014203d2841c05250300a80c101c01c1100130302c0340e01140e1000794494040f2141300041c42c0050745e03200e4641000011002c01e1600c500b070600d91b8038500800c0001c030002d04c24100b50185c0031951400cd6241c203181034520402a000c65591283d101040620f14001c00010100301c0440101c40007011401141c10102e03060340340603070281000101701004900a6201d12014402c00600c1000701c0390007000002000d1080116100c0d0340326001c0003a8104081004143c0100e090440110f0150401040040e686d08e03601e0100007034038100d9944d00b49620441102002680e90000e038021018181880c001012080c1010910041405500c6684c0811449143c584543d5800413480c003128007920304c421169880340b0b036082d100c140c102d0340748100d0300b00d100305d0f000840d204050300b0038240ba021f0443c6082c4400c43e1913241f0110801c640200c1c1183d1251001c210100a0307015 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 919829172 1250 919827922 919827941
    0xc0106080102031e0408091302070210030e0a110f0406080609060604060321090801060605090310050106090b0a02030c03030c041401030b01050d0207050102070c08160e10050907031b02010f 83
    0x8500f981081919100c041520152060010101070041420300c5803480481e1140180240300120005007010708030043c7d040f2070010784c85107208030139035840d0300d00034001c480b560b140200c05001c1000003940d0308014120585c4115800860410702070b9107988a0f0721590000e8880c0f4402040d00d4501250b1003483c0105c01010280268208075040000404003004040c0c1001c011801038031315400904200c51200306580100301c10741c201070000440d00d822100074805040d0603019907514040d030002d070100341c640a2146c00000341c41e80004000100c0074102030003076200c903881500d140c00d04402089146801c02c2c1c2d0306840c03840c0b001504000c0c042105510380c1103104207082c01c0c03219214410020b80540140000ba218654002035400200082903040740c2825901801c580541502c1e500300c9580c854000c40d0059400d01800030110301d2003000c20400d40310310f0f41640403080d030500380380c1400341c06040900342c41c003407644606041180d042190941150161f141e80001011031103035032050b090f1a4243c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 919830422 1250 919829172 919829189
    0xe030c1b09010303030b120a0c0602010b010302090d0605040f1a010e071701052214071b110d020a0824100f1a1905040e0a0b09190e0708030c0106 64
    0x124060381c90388925941140d40508000a9034090440821180342d6446c9207030055026810040c0d040080e0021100203a400540c020007081c1e101d000194124492a480650700c100e4080600000030344540060351321a00c509094203c003600341d0303903d1080c807056507c2c45c480800c420340144101c1c04401c031840d038050400c1c50121072001d81525100d40b00c00c01801280e000b40540c2060b94110100c00c030050f60701200d8040100000c003c80507081c40b0340c5c00d09446620004556005c44103104007580009034000e0340200c403107103441c88488104450700103814012a0840b411820001d400300d0140001c0640007a032135858603440d2801d002155681800501c3c002440204200511015000c04440701c20b4465814030000b82845d000352108150288040a580786030004150882440d4008003420480c3e44445d0045629100e001600090302d1002c00403582185117600054072540c00e03100e9030344521011010000c2c180d10900c110b40c4c2003404c5500b0000c030302c1e4000100120440703000d200701d000400440 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 919831672 1250 919830422 919830463
    0xd080319090209070f0e100e1011060a09060603210e01020d09062f030c0114070e040515030708010902270402220510030b061503060d030504090e030c 66
    0xb540000c400d00d10190040081001941500c402c0c20b00450420110200082403d481c4620021008281100c090481806010100408000b5500810501c1d8002000c0e0012300816603540c04101c0c010001d0340300542d1041d4441d000040403c044c0c07d1000004091031411407030b28012070b039011341a4080c180643d030440d441310000d00141c1da8031141000a603542441c280300c508403980300e0140e007070b111002042d092403080800c02000d414000010665a03035070100922072101040b03c510301080c1e085802d10b0200780728400700482440d1642c070265001070905410480349580d000482c1c604015500082c000c1e0799691242801d62801d26205010800664050200c1142201c40e4103407002c00500000d0140388500400503040c0740d084420031504400d20f03020001c61a2107000c12069050510054611044001c04038115060810003e11209440c00380d40c4e1841d1a10300034008200c02d8502e090301004410321000c036030030115000e180000420300c0300541c0c5800c0900c18103400c0100e1441000115540c4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 919832922 1250 919831672 919831691
    0x10519051003020c100e061609060f05031305060901020913060506070809030a12081815071206090204121a150f0418030c06180206070f030c020d080319 67
    0x14807103014042016840c01503101c0071040c40341c40c42c20019465992140b8144241c180303c03070200007482071040009264030440e0300c990348025125285503010382c1001940402000100c14040c50055400c000c0d05000c040001555858140c14184262014481650002042e9082c1d1030028000e010605900b02c04009040c074120004155100d11000108421008503248007541da0034003003902c2d140e411a9540d04000e12011006066007000caa10300b00c034030304501e110102c0b418002000032590390380c110016141c2c0c0707502c0c806581c041a4001c80042150711200c020940254031300250005050814041508001c0d030300d022004e03404513150343c481c2101d09408100c1c0c100d0b021488900399200944a41a5108140000c100a44092039000e440c1002d0640c80c1c8080503844103902030300d24080c00c010030240c1200d0007140e82e6042000c0000c0c0d0302031030600a6002041000803d00c200c14403a0401400305080d660200303036040c005031001d4030300a50100070000703a00044960741c40290a10442040381840c07 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 919834172 1250 919832922 919832929
    0x13060603052d060406030b0405070303030f0209090f0a0e121b03160605041712060f01140a140405030d0507030908010c0c110a05040218040b030c030a1e080f0301051905 74
    0x501195208401c2d0524001ca034240d04c40c0e9001001440c1c101c101484145881d0405555036070f6148070440c0002e14250701225550130a200b6510024030003840708401d40c640b43c5890600f6000540041ca07d556a46884036820000b08140c171510031290500f02e86810394822000e030100c0b40e0302c10816442d0030800110840e00040800607940d558803840025090f207450906840f054106a498007201310002540609002d1091440344038000480b40c1d41941c1804100464491455009180c541c11042c800b240100f4061428148103801041c8001d0078030f0307038441c0042e191901c10040c0031701051000414905169012031107101820001000780326400d51200002c050030404440a08a0254034121030031541d46c0d41702c000c005000050040d501d501045c00c0303d04241e0281c0141740d100314500a1032040c00d00f80070511100c0c190303006000c4d0100c164217454030f0400f80c40010322004000b1400c1c560a000580c00000b0341242c1b00c0840e402601d80d8102000d02141044920012900318250b83e81007080740c1c1e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 919835422 1250 919834172 919834231
    0x405060c03070507060204033519030917030f0a060b0d18021905122113080a050304060305010803072105070b0a02071208070c02041a1306060305 64
    0x580101015642e540d071480480b03540c000c0e071600811640c000138000091000d06880242c604466031110700441840221003121081c9240102c02031030414000030740c081400c1100126003200d1400d010407001d000350b0381e44048c1c1c1d0300c1d0028200c00070804400c0c003a04910510344950710907141c03a01003140900300148004540590000e607500a91500d0403041044907403400e81040b56030151502c0c134020582c8115100342025030181c00e02690001c0c101080c2d8040014184000070340007640641c08000741c01158516500c01100001010f00030b13840001c00340303001c2001c195083d0180c0f01440c4c82e181058801000d071801a0b00800300b9500c24082c03880031500d504070100c113002083e5450485112404000d84050042c1c40010b03080300400c00c00c00046403240d400410b8142d2140c2224002d203038692400340c8035500d044d162180010a00030907400107040c550300c040c03030a10a5072030f200b0000755042d0000301d5a802c0e5207007600460307803146400c00c6000e8041c014280c1000103683c10411001040d0002180607 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 919836672 1250 919835422 919835431
    0x11030a0b06090403210b1e010804150605030d080906060a141e04060f0905060307030f151b0201200c0d05030a0e0304032a0b0d0902040f15051305040506 67
    0x1544503001141c201401a10034400d0f01345ca0703107160080410403481340ca0043c505221054081e00601e50174840312000b10b8000740500d6416100d110142d00c4544503c0c0c080780245a031403034810340c4d665000c61542ea08111014903c9081c4e507800740c240c507140c940607040032006880c003402010103101c00d008011050080600461055410042e0300d104040034101c42c2550900454115281800c04601d4540440600c800d55404000038001620740d00300b4140c0c3c0384402d03c0003801c00f0b200044d400b0000b500701184400e070f589a002001c1525103600e00403c000c0d003420000300002d80e40d0341d811019610101c405c1c8101000f6600c26090800c0206150710382c403502804080b100b0008004000360907091954010602651240c04403602d0b991a0f250500c9102c000380c0444415554000c03c890007051200d514100751101800e040d401e01d045854840c01034907010008070303441a1a101c41034074451a9124540400c841c000d60810500d10b04000d0007034500320f00c0d10040b680341c142020000410130014540e07402 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 919837922 1250 919836672 919836679
    0x609050409021c050703120f020f030307090512010f020a09031203060b030a0213030512070302120309031e36031b0d020a0b0409140a0209010207060807030204050402070f11030a0b06 80
    0x50140fa2400b1410850f20b41c04c001e01d001da40c00c074108000d55110035502070418a1340c00f140c0414400788425a035030300040b6a4900020b190050a10040c20100d44c4451f040c01b111b00081468402e5902036016604403031407480000c2c0c8074620420034058031410488400c00d041c00c040009608185504800c2d210042c45640807640001c1e41d04404000120110019a082001e40e9100566520000c0040c0c0c000f14007074005105040d940259125050101c0b400366142c04011440c0070243c6c2010904a1681c4480f92203415081c070080080140f40c01070141d404020707410700340000d044041e0000c0c80094508610f070281c4d00508aa071425001022010b140740b100301e8a502c00050f40d0f1000410008168102000790381c0c0100c2c0000300512203420481d050130360074401303090b20798401c001c0350224000c401d030340ba0041e4003028081105500400d8010740140f03191401601d403580302c1001c201a030707120b0401101c071404440520418844042d01c43c003a400402c43c090851601c8544580c041c0303c5001c2c088510 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 919839172 1250 919837922 919837969
    0x110a0f080f061507080304050a060b2e0909020a020f011109010c0807020a0b07080a020606012c04062d0f0f270905060f0f01080d0c020424060905040902 67
    0x440f21540d105485400342d019007410b507240303018a08161100c808402c121902410319040c18024075080c2e858072040041804412203c081e545454540102c8013655501407000600001c0340b40c1c0307100e0000f030484e2200c0c0e4001f23000b01f40c4410140703403c403214041412104030301030000888cc2c1c0c1e401106202e4207030300480c003030352100b01c24000101014001c0d40403506400c4000384803402c01c00036001a10007811550240e4404e030362000300545600340382c203ca03004041c0e12884603c0000441651100300d100003e4000140710b900c40350000c0001403c40c4c1c0120200c180400f45100c031a00106100c0c002d02421417100350680d2034500039140a00f01350081049007002c040100b121220304852000034414180410300840c80e0a08090340c8905041c0c0300f10580d0568007000851003c2c3c0000080d040321111001080910126901280c0800c071510089900c01c1c0c4800700414603e032400b510044088120410b104020300d0240045c0440060390f0009000728141a03207240940e5608800303000c5909000d0b003410 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 919840422 1250 919839172 919839199
    0x2030106090603020d150e04050606010203120606031308040603060905010b1306082e0905070305040c05010309050f2e0b0603010905130b07021c02010b1e0102030d110a0f080f06 78
    0x1014002e86c1003c808030103241040065035500403400740d0700490080c4261480c5032501c40c0126105d12503082c020040018441c0400c40a050580045601c0600e0300000c030050b68199a501d48a540316a00c0040043c1d2120001e218100d124455180140a21505189821118912107501c0e05440c400c140a2201d0800001c0340c0d00080d00340d401140361844101d0080084003000300000c0c00090080403403940c40c0a0006403001e00a1080e5402140c10541480708a413a000044001d03042c561030480f01405000c1040da4030b42410003010080e80306840840c0c10065001c60135440c025401c854811149042c00d403000d01c162101402c8074156100028081516a04e064440034401c1403c900204440041002c005d0f202e5404182100c038284a074041c1d00b0721100c2260100d0036580c7c448526540041c010403816400c0d090603800e180c0c01d0f281030040d2428449803180010032200c041074010480c51000818488041d8404480d41e04042181410074807410701030440015003030020801c074021500402c4d1103 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 919841672 1250 919840422 919840447
    0x80f130321020406080c03042303120c1803031204030315081609060501031112060d021e03060a0608190606050a180506101b030c0f081b010203010609060302 69
    0x90240301d032054a014060018000e2540250b20510500c0300003401c02022070074100001044074002c41d081030400034007410a000301100d4007001d21580b1582c1c0310810220b01e0400050a556224440403000c458540b0840b0020b03401d44c604240c9181c0c0310f504100420741c2c0d182e500d04031080d049a01483c0000784039112981103e205601031f00703d100207209055401c41b80380c100d00d50030401c2e10401c12040c000e15507210010b600f5284c100c2c18500a035841408406000c00940060341c1e84910000e16006000302160041029204d030326000e00c045e80c206001d0000c890400f00219504610442400c005040c17501c4080c903110000511002d6204400392044010311074960064400340200070450020720b5500c0e12400b00c10812096140909030070100010918a405000d0004000183d11a6084141003040004a801c42a60100c0c14019109581c4001c11101144442d500c2c3c23180006c140c0d0f07455001c00d89a45c103004440c00c0c0d400c1d41c0c0104010302600c1d911400d00c0045400c241000751b280e1004051a = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 919842922 1250 919841672 919841687
    0x209031507091221090b0a0305091501080f010507210b130c0527010206010312121a2d130f020313120801061403090c18090d080f1303 59
    0x3e60040070996102c201400b0864145401c0a40084141800b54074024030a40d440080c80c0300d09940100140b0508100034081c0d04019805811001a07d028884980340520060020b1700310550540c8980c604950340f1809204041d0800c41c2c0e4245801080801480d0540701c80d00034418500b02911101101e100e925000390072400c01106080030301c29048080700040980c1c00003075600ca04010104c0400d00d4144140612400c0610b06034040d211070307829500c03125000c0d518200103a080060312611030402220724860800c1e00704052504804408200c000c01ca00307800342d80d03070580194000e0b5000410100f80412001d02044050701c0c0c0021b810250280c210040c007084100ba800c06000004110643c1e6050000d4544184241c50942000c1d910000440d082c1509001d5000442c072554091945610031401840e0b110031080e003101d01403088000880d014108801001d000240c049052202101003400f12b0300381a0480c0c50000c1080c500b4103040ca00001e0090034400811030b40071136142c24140714201 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 919844172 1250 919842922 919842929
    0x50724230d0b0402160809041107051b03030c030c0303040b0c2d0705060f010e010f140f0a08031611040c05090907180b0304030f050f070215040f0e060a0801020903150709 75
    0x45c254042019420304c0390b801c0e80b0959009118502c1c0c490700862005090341070350341c40c1e07030004000c02c038a4140e500050382400c00c810b03609906100c140240096810304000038000680760402468607400e1034078000015000142901c2e1040c9801d0088010003c8114506a08a0603e0b5420020584200c019100e02d00c41d949001c0c20a0092008001c2d5010780310070000c5c100d512f000d11035482c82e0303070341c10102c07011030560300442c6041c881a100c629028601810101c1200500900b0141c0060307498082c0c0f031665000080c1d5600001c0740200f01e10522080990700c4000c0042503c0c24080e44940000040c0684950244107106250703400c00f258030540310f01c0304a006651024003d4903029110310804d078540d081258210005a0000d070260400d034424020f031103160110340c4205080401590070480300000321855402161703003d0000081070042d0019450042c0b1004900901c1410044213000800103282c210482d2070b8010804400141c03000100502c0031034901c440c60a081e15100f60403030b20401c2d40d03030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 919845422 1250 919844172 919844197
    0xa020705220c050d111e0309031b030f0706050708150102030d2408100f06061b03170a020c0c04200d06051509010f0f0813050724230d0b0402 62
    0x10006804103405c00a248039410415120080e5041da17907046903034801215504031b15081840070081b05204c10b244420001382c0a0305407402d200c00307001021341542100c1c2d410b4480948072402d0040247e00080b00c1c1e9080340141d15089100c40000380044c0d82e0344510300442c40d166942d005101c101240423103008a0f1195403035a41081555960415a076680d241c0001007403652800310607000300100c0b44034840c00ca81441c0c4a04201401c004888440040300c0102601030110070b24101035410860380c0c00520034401d801005071a1004201014686040d0303500781c40c003e0b86414002201c4ca21090b0800c8034102480d4241966980e00c4510900a00f1f0141d10281c0c01a00b0604811070720000040600080395003a42c0b228014074040c2c03003c444800c0d901c0d00c07060100780020007054001e645400e46000860140d4211802039075200c081420007a00c1c42000141c01d00d20101c40400b95611021200c10314421400d10b5000301040d02c1041c80a00c40c141c0182a05c40e5207810030302158540390152548241d610 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 919846672 1250 919845422 919845431
    0x417030702150a0906110604170706050106030c0210150509062209020f061303080a030914070609080f1207020a0909032015150d0b0103080a020705220c050d 69
    0x6598441443e04004a10740102d1481200841d04a00c9420b800080d011200700519031601e49403140c13100c0c42c1031160000450401000800045034041c05400d0003400b61788d50011355007028000080c1070200046606004038240a8420b0380b0041d04181c40c4161042200c22a500b9111700001820710206884c0f60800700b9820311941040740322644c411120701d802910843e0022180204215440c0300d00792036105a440300c14001d03c0400ca07880042d108160540c20002852101502c031382c0241e007080d440300810340d0300110052041c103510014127802440c0354002130022020886200d91144c140d44220340140710b0110743c080a55440000780c0b4020420b00004001409042c1002030540100c030030326100355200d040561034102400100f80b89242d0092494032800d443c4d8082000d45070405036401c96111019440240202e6014400300d802944580095070780c0c1c1107a0710000e402c00b0616405280700e05c03003002c040f0009129440f02d50f50f40c48980b0f48001134400001e0008d0303425014040030141d40341e107403 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 919847922 1250 919846672 919846699
    0x512010303020c09070f1e090b0d0f0b010804020d030804030201140106020c040b120c040b040f0606050a020c270723090a09060303141804050406230c0417030702 71
    0x30404410f602c0003941d078024280e4590302c00740e540d070041c9440c450020700a600d8003c03d124240145070340031582441c017a03441c80d6036410240025000307607083d52207190390349401502441482c80b0300b2107030b0442820882c0c0c80d894580c00203145c0e11012100501445920800281018400c0d404202c512403801401c005550315002c1c001c6d680d9419480160003103103001e401203031500c2c00c80da00441000446000305110590304081c03101400d00043e403590010384444100103c05580d00668002e40300341e969103a15a98802c80c0240780000e41640d182c068500030880c040030000b40c0784100082c000c041c1c0701251a4543e108101d0b110b8811840140d490112146c8100034881e60800901d03807103100315180310610f9191200c0c08202c980a104c014045841049081d000c4d61480010304007031000e1888000300c0842e01c0003c00d041c3d0740110b60803140a03580c0c0b5403000148082200003144181100c01d241601c3c6401400048548076501aa004407540003070308140002040045074032030341e4040c0014910041 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 919849172 1250 919847922 919847927
    0x50c1003020d021218011a1018060804031704151a03010501032f030601090902010216180c0302121812070507030309060c12030504020a2612090303030a05070512010303 74
    0x1511707201000d000d006020448024140290000e52610f450f0480107205078804103c0700340d200042200c00e1181c101d610350151140003400c2001440c95440d0020a85814034000301030303d01e01c906100c0000980000d200114048204c88030504c00c484200081e0030001c0d280b0744c1031844618400030f925600b044004000c01880305621030072144205d959a44a220f40703030100610032680200c3c1034040e8440001009005450b03041000c01e1401801a03c010020b140c030b44410120036500044d0341840510451401800203200e45240c443c50303864214240111224901440500542442504140c031848004122411301006142d80c15801040e5a034203140d1078600d0f140d110a10080d00400c1e101c0c6000600d460041110400c01c0341d11150ba00d01d0700d244040181e000303143c080d01c00e070b8100c400d03003801040324038105804410055861000340d11885c80b02081c1490b102842100c020b041d04148000f2005450000580b90811901d45003c603050740d545004966500a4442c000c0d00307128240b00010074540c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 919850422 1250 919849172 919849207
    0x30f07080702061c0b01020c01030b090c031b03090a021e01020c0103111917010602010b0a0b18121b040c090302040b03100c08090706050301050927030c0d0e0d050c1003020d02 77
    0x21f030250785103003a210b001541210204010107800800030000034000c40404002140e11040d022443c00401d041c80f01e419456801c119003d001d503a110501807815843c1c128062000d4405c40c4082813000e188010000703440b44200c801343d90605032070301c00c520207100c1d291040c2d529044180481307289a0401c100006d05507031206030510b2841c902a00049040d92060261654402020340b240040914020f541407043c1c2c48812046480d0b4000440b0103a1540d41c42c0b010200300681310b008041c003551003000e4501841e00018050b120364a00b0080900700c0e50840e52407000c403130701107030005050b4581c807003c02d04019601e0b03e01d01010b803401440d0700e1611b80051380103001c0c0d08013030b048425160b215501a1a58070003802840e9010030784d0000205586420503c0003a20f00340b94400d107000703205a0ba41c1c0d910310740143c1035040070b94000d5082c040741e540c1e02c42102c60441008550810040703070740751034094950107984555070044424881804034140641c040700e000040e1283e08540c0c03507031006056640003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 919851672 1250 919850422 919850441
    0x3110a0f1206051c11180103020414070e040b01020102040b040905092a060309010e06040b0a0b0a1206020f2115040506090a270c0611030f07080702061c 67
    0x81c03084001181c030400500c00c030000d44101034507107050203400daa0f0040000e013030300b0411079050707030450491411500c0e0002254800c80f008440100a5410761041000f0f6550011011681000020410646944c0b00c42c3d220741c80c1c0029280042c048020000403806442242c1000d078002500040000390540c0d80d5005078400e46c001400e90b1880c19a01e580c800c10720101036100c00e0030010002e840e800ba45460002150801c072400c000185040c0c0b4402c0d154203014007140e0035035166800c03500300050b6640c0c50141004000040b280c086005007000c00f0308048074114400038040c10303401b1540b014040c0012045504903844500420032400c1c680b10490400142140e0b2013925120b201c1540364103003098002e0301d004441c010710303892499450100e0000146041e10100045080842410110000703408511086a00415108903005d09000002d0110754800c0d61180043d4002c003c4600e10b540c189064652040c0e10441083d5105a1400003903640c1c002c0402840000c2c600300420f0082e0040d550007000d19 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 919852922 1250 919851672 919851677
    0xe0a08011a120d090e0c0d1d0106080a031209030e09011403011b081503011d03090a0602160b0c0c0a18050a0b030703031119120e060712030203040303110a0f 69
    0xc8818899030b880d181c41c11114203101007801d080040c000c10b103014089a50140c58215200e0804005c2c845903000d840c010748a04140140055000c1c40c01030080c002c0d04058003411005080c40401654020041c0200c06060b86455580721010002c26100c0d480c0840ca580c40102800d40f1541c41d64220b086225010344103510a6207082c00212944107070364811070780c000c29a00ca5030343c5c0341c0c0c4140d888a40007403090001303039041d581c0d140303525601d08103913140c40e410240d218000c0d034845041c00f0902c80c2d8124203800080030f42d840046041d03502e41ca0301c40c0041c2940c410740840c0d0344584403645a246454240451140d1160701e490000c00c103107440b0701d02001c260b89081414000c5840d8081c2d28011900c42070f81081d010f03003010030244086402080b008041c0c000c00c1d412103640007803200b03002050b1403030121f0403254ad8250010300201241c0c445d00320314400d078080b68242d240148030703581d9104403282c440b1020141034010000400303040c080e0388500421800f400c01c259a946900c0d400402c8a410510b80102 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 919854172 1250 919852922 919852939
    0x1d0d0b01082806090c08070f05130504050a081e12090c0109060e01030b01050d090c0833060f0307060809070b090303030402040207140a03080106080f060a060e0a08011a 74
    0x11208814203014030034001a20300d800d1445140c40303150140c190b42a085d00c05030100c10380054200d00800070b4200414001c40f110040c1404c090401c40b14604441c1c06413459800d0509000101c0d0021a1409869600414481c0d0b0b80e1000040c03501e0507422781c20b01039a0a440800c80b6125400c1c0c60300070070301c105081c4d0250303162961103500543d440550b03800f800c0001035500707103002210750090b4030070300240f003050400b141010400400e010561382903450499508085000401803c00b04020002c21056980e072420100c80102034481c1c042a842001320903c5801c0d003000c20f02d03030b071a004c046a0340b001c40a01541c89541d11103102929118064409100c503124031100040e0403500075041d502403040041c091480d50b1600c0d001c01029401c0490143c950900c64040314001160402804a01c14401c0d06d400c4520740c5404030103045000d008118001010b03080003044820350f1000f20740410b03221103060010309840f002012802c0e244090700115031561070304d2585143c1440c000d113050700002048850301c4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 919855422 1250 919854172 919854193
    0x310020a050a112b03060905090705010f0516232401050105090a03060b0f061602010f09050f010c14010c0c050d0908070608060f131e020a050a1d0d0b0108 68
    0x2da850004a042201002004032403a0f03207619045080c0300741013010700e40860002d480315101002c454064610018540c442d1a0400195801031582c042c14411410715501b410700c94420351604031002139000300301714480306158010050f4100204403441128040350203000065040100c1030049100380341404080c100009425071144080390558000580f514454030b1960303544401400658141640c007460015000006446800140101200c04c0a940301010050300016002240b142c800400f04446514107120940b0380d00501070203204207192900c0e03045882e0401402c1909039a40c201c4084d4200048001303880d900120b0408800d0107003064550001e82c4200c29611035100d0311455850360040301c420003000d4020310740960b1094003c0c1501034100c400c0000106a62030001c084030f40b0303a54400b0451214801c420030f004082096003402c503e400c02c5c0c2c901c094498000c03d0820020450a00b1090f092455040f4400703009500252094000b61078900d042c115401c402d0284200da40b00300c07044403 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 919856672 1250 919855422 919855457
    0x3180308031e0108010b0102030a0c0c1a070606090b2803060204090905100e0601122111010509070e160c02030f0c1504030c2d08070f2309060310020a050a 68
    0x40078181b8160019480c0982c640c50613985040e01039420740344500c82040000302c481e032680d08140710000b0f1045d4140c0e20110303440e03c2e00458200d60402d4900a180603140e000340e840360064000060420046c404010340044103071008801203420082c0140d002040001e504006a0064a00c440c40307607050b11f5050f601a000302c821a0502030000352280c3c400c50042004140790302842c2c0000e401503908942494403421650707a080c0c00780000741c0018030460500382c1038480070711450790400384010180c500c1e1407a25185800d12600a841190345c1c40c1d40d0044114034074050000b0320120f0b90f0140a035011807003030560403038a03102a003c0d620b000d000e00411040c2c2c1c10400008803400e49600400f900701d2507040529000c080003c594070490000c2071468650502e0101081c46c10041c1010801000403d0601c02022036003443c83d4001c0340c0c5428804d819a0550741c2c12113488560b51015aa000f80640da0000000e10f000e40e060711000c480d03840017425071040e079400f60081c11000d1150f03c50f0510344141d01d442 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 919857922 1250 919856672 919856681
    0x6020d020708160909080f0f041d040b0f13020a090606020c01080c072603090604050708030408071404110403030503010e060915040510080d0c0204050106110a03180308031e010801 79
    0xe2003c0c2c6481840c18000f059080d8004066035018440380c50400c080a110103c02d540b020068040c0d0b00400b20303040040300060740d000c4203c0440c0b210801c8070380c205541c0716410590003404240c0e2154200c00040d81d80d074035204e2200d0180f81c005003003200040c1d1f5040302500921550150380010b002d60014080c542d40124049070084401c81820381c9001c1e5180c07501104210304005c080c0b241c1c0342c40c03401548520b850f40003441c001c41c50000070741074074240b034a0842e01d8101b45a00010307003508244400c200f0303400017050890842e10a141c00b040c0100f104800100240549410103030030020200f804424154808003941c141d84404440010f99102d5604108280d002296425000115607802980500306500400e410000d1640c1289070781c1c0c1c440858074100220420f1040000e401228a030041d0701c0c1a0103214014a1981040c1407180499602e55441d154458030103018000701c4000d086146002180c1c00000b185c01a070200d03140c0c10503844204507486c602c41e5240d14540414004210f409042c410f = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 919859172 1250 919857922 919857943
    0x7021e0a0e151c0b040f061d0705010e0d171207020706030b01021513030c021002012307080103290c070210020105060f120106150e0a06090e06040f0f0606020d020708 73
    0x280c0740004880e44c8400b9a507000030800c940c0d5140c529440000a281c40c0102c03007280c90310310180076040c401c04544a2400c60280c0c010703810404400c2d00034010b41c50741c01000a01275007044490420601e07508585807184a4201e0164607071800d041009030007503000c5260400d0390707030660f001e1041000003c01240e07120792201590900c400b0030b00110700c11900031142c003c1e06034428108085110a02e03000101102034184c080b002607515000d00d4100341d2000c07061000d0031680c940f812140d904206074014861030b41400010702c03481d04a6031145111120b54000c290813a0048480c2c601454004140310a640025804a0182c3c40300c1c6181ea40c06401800303068801c0c680070344854a020013280030000410142c00c0c020056550700c0d5008146e000c400410340000b1003044e207a1110403ca000180b0001c080103a10000411405420910041c0d00301c20603260045001c407000303e02c180c0791004010041c40c3c0c03414075811880c9000700005540b90013107070841c504400c1c0c1d02a2840d95035070b162a01d480e200f1517003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 919860422 1250 919859172 919859209
    0xc051c05040519170307180609050102070b040308030f0603160909110301091104201314030f0d0305181b0102010608030f030a0903050c060f040c0f0b07021e0a0e15 72
    0x1404940140308984c060b551224481c9070080325a000d0449401c400d8841d03811900000d1003c2109118551b010803840c402059140000d602d02443d585400c81c2d039000161100c0140140d400106404d540c0400c0101c02c60300c15020400840d90340c810490005103030020086038141a80c410395003043c075042c82800000da802c82c01071001d2590340070410004103140d10310903050404c4224101e20303040c01700340680342ea01c0580e8010141e080c02c11542150a552400c00b5503c80e030302c50342654544803000700b801c100301075984c00c0c04103950310743c081254404c5c4404003507280140300302840d60020302100a041018203c0a800820442d900c4801040e00c910030640310031884841000802c0a1a0302540480180d074043d20f04181400940018581171180c01e1701c1d010140c1c04d0007414081800035025606004007024120480380c50300d4242da11140d0300030860080e100c3c0311244446003602d90001003201e89020001c2c040c3d1403a42c0c03901d1484072100d000352110204000382c1c960b09030a0f4100b40b80800701140202 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 919861672 1250 919860422 919860443
    0x1206070f080f041211010f02030f0a0603260d02070f0b22020d05031e04031202060f0601120b090a020c07170303010b0d14010b04030b090705130c051c05040519 70
    0x1d46400d4405002c24103c031082104016480e400b1171001c0c0310f141c420504001015950b070500c04080440c034900902040c1005150900810000c0c0c01081107400e20300e44028404000d08000901080ca8040c510307034132000c1c5d8000100c4000b0800c010126a8107248906040b10711a2182d1501042000500c3c90514510048901c1c00d00580742078520b810002c0e1150089030320b442101007070300149048880c202601c0031000b28007801044813002803034000c03650ba40300601c103500d03100740b40d9021200701901c058148000c0c620031100801040d0008400b441000e0000911b50130101c41d2000294003210f000d110034000d6500118100c480a00800701c8000b040f001107065900700344115045512901401104a40e00c031103001c560351003c0e424900030101c91541130b4903645141031581040400929041ced06801c8010240119903440200d000030082c0300e04001410422000d0503903291060030b110b440f10704a028400c400e040515040148590b1084d4140c40d0082043d828012006500d002d000b090801030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 919862922 1250 919861672 919861681
    0x60c0e0f011b02030f010603120302030712090515040506010915080d032703020a02040615020601150c050610050a0e090a030813232a0f0402091206070f080f 69
    0xd030204410311004110102542e4030b490780002d00d80f00b600b610f04566079441e12002c00910401c0ea00e440441051420151f1031850b00b10001480c00790000503441c2c0403556401050203001d020801a4074036940da120f4006141000e003070842c0c2e00c3c2070902c00c01703804034180a010310082e0f120040c00400c0300c000e54010300a0120034503040d0040d02540000c2448100c05420480c0c1809030080340c0304003a80240c000d088c4001c160b005100c182d402d903800c0500251501a901e506840d070005d8480d0440c1d40302403041246a913015402c07030340107d002c80701400901c19041446821130501d04c2c0c080490340700302ca1840030241c3c2c6000e01c0802030700441e01c0b4949138004100307082c00300340600051540903118441005a819060703441c9000d60500324019a1050131419140407401410440d0b08103044510100710761040c1c0700b4602c0154000c0008209000d0042d09800c580385da00c407034041c2d4400480041400d620308950650403a6121400ca030000c1c00581100c0040c10b14900480e100c50007100c0b0001901c040d40e68 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 919864172 1250 919862922 919862927
    0x30a0b030631021f03140a0207050c010f050d020c01021c0506010801170c1c03020106291c020307120b09150631050906031c1b1b03060c0e0f01 63
    0x10381c0582681c000111689503c800d06240d0310b881c08601c0c40f6200046c030784080b00c200c8110313540c000b0b25141a0920410891003c144002040b4040150901c0e1021502c0c1c00e01401329a1800707058900c1c1d02c524008500030f508075006402910424404481545011902c40c840105071002652440d01003003801005105503001500001106c04c1c4050031105584101c10100e15550031500b01d50b06582c5a8016913030800d0b0742030281000030017178002c2c0a1807044400c1948581418880c40ca0800f120001400c122100800f010005011030f407003808540380d14110001514032140c0b98281c180a07172501c07003588114a00303070b07019500444c1410980152a000d5000b4400f8030741c0302c8014845041d080b010088807455601e64045012003c500aa41e8094907000074004422806401248a81c01c9490600b80054102d41102c0c981110b9182c903200d15807440031005004582860041d0085002000300c07410b804000b02014200c0340b09441c01c0240309000c0d1030448843d0310280b8110ba004034417602c1540150f1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 919865422 1250 919864172 919864261
    0x30c0b031506130306140601090902091206070e1f090311010c0204090606080d051204020d021825020d020706120609050108060402040e03070f0620030a0b0306 70
    0x40d4524040d11a030040c0c4000520a4000740200300c10f62032a1403044c4204525400748100e4400508003500d41c034201280041c00817002802030b0410303c2d0703000c500c0790282c2d40e0f000320340018504c035038054911340c1c28440c3c001802c42c4a00d80c24903000d03000300000504a04101010f0030502c402580e5002415421a81c0381c000c0e40c07030f21440d40c90400041c0004000940e07a00c1c0700307808100d44a03040004801c2d15103c401400e180041c008041030040500001e10303491482c0c0502030348164126001c19146134a440002e402c0c01881c401e0a080c0c2d2202020840350241c1880c4410410300800c2d0801d17480c490f90307001240e03140d146850030401070b04001d104005490103100501e2818003021400314041d80c0300c02d00c680403100264403500140e40321000340821350426204401001c641e80002c0d525101c0551209a102c4403200b00c01402c03144d0764030b10408040b5050307001c003140307a490041165803424141d41c00d501600010b40d04910034084d0318040340c40c00041745800010f59000e0000e5000d010101603020141c02e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 919866672 1250 919865422 919865431
    0x918030206040807230a14030c1221070305150f0d0b040507080a031220040b0a0c1e0309080c0120011503140c060306092d101806030c0b03 61
    0x544c038901c40c5d40304400ca1031030160117001204002c00080060b414034955103808082000e0980c0c0003042950000800420351045d01c070588841d481d510b002540048003c01e880b04a00400b180e41a0140841180d16821960048502003c0d165000e01058200980d1598504040ea80115041c188030006507000c0f951980c8039004800303036805260f80d041c2d40740c1031451701101100026084603680b003c88425104800f1200407000e4910981e6080002d0740201e0b22803401103424440c0007084c0c07845030740d00c51108450102e50040399410005841c0c0c04407000382c01ca10b60101c011410105021070701c600009a48500e00c08140c1d00c40080583e115054454105020f03102021035403075205108105809401c5400214803484542c004800324420050070f082c1100d90b5140b1a00d0200107014083da20b40c84035641107044109070544100e0420340701142ca03c0d04c2507501900c42d4440c010070640e0914400ca1404a4001001018409054088042c12141b66000042c04a000c0c6c1c402804420804009550300 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 919867922 1250 919866672 919866683
    0x1511040e1501030906050106020d120509061b040b07060b09150f060d0917040e0a0b01020a021002010b04050c09031932030706060f090e0d080c0d150918030206040807 73
    0x13241d00c58075060140c401c00d8204801581c05200102410360340301c01585011002c10700200004d050284001d42c0703c48010b80b0000080b4410210142d515009500300d84c001c0140541d60b964074501031070a00058100b400301c461052220000007441d040b1044403001502200400c0d0f0070790380d03188000b0041e468000c21005804540c1d1580400006203807850700480c295201020151204e00c0e00c0c1c41074141d0030005105180300742c01c00c80240704030f0f6000078091400c198106c503070f40360410301c0d500b00703c2c010210602c140345d0290400d024018107e080c4e50003440c1d0704a041d01a00c100054081202e50304181c120002050121000c054010403949080d00300c1080303070907084040051180d01c052078510303001441c2c1a6030182d500e990400010031010380f000020b001c0100144a0b00e1140300040d61100070015003641849050000591444180c000b1101c4044409808000840341944003070794480c2c0b6406011007a6240454084407412040c509255081c2e00da0300409a90352640d6aa2486070813010b01242c4 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 919869172 1250 919867922 919867931
    0x61b02123f18030a0f112d190609050a02120303010806010f0302130b041d0f0606190627030b040201020d0810120515041511040e150103 60
    0x804940d84406492030744001d0891108081c0c48100703504620304040d000750341d00c0d440001e039401d4075075020059074030203881410542d6400b039043d10152040c02c1d0200301c0220901524085c0c800010031495030744c1d07003441c00c1604e01201400b03940c101a91402c0101e07500700000ca00d40030550003e00b107500f1003650644074070140c920848241d40490441c2403200181c5500e0380001c0014032890404000650040405000000500740703982c0208444542d4640e0940c00b01e9141d2000841c00d4403243c11529811590a0712056030340e5010a65646074a41640c00020320b000304000b0407158a42000900d0048403215400105146042c80585803980c565001140403142e0313441c5400341000421260f40158081c14042410b0300c1c01d80300080c140074082c0559010301091a09100c000c0740f140c440d5001361106084d244506002c1e0303051a030b28146403105013203602250b04d0304000c108544054030006144d40c01409000200202000114501440c09098800c0b4451800900140008441c40314200018140000c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 919870422 1250 919869172 919869217
    0xf020907051903050705030f07020f030d0212010b07050c12071a04090b040c09050f1c060c0f02010204030213020d09061d0c01230a02070b0412061b0212 67
    0x24084802103800001044002c42d01c442e03004039440540b03030791030b010386030800c490316151801034541d000181c010041e10381c140e80000d040340e008006c440a100360020032680c441a208442001961001c1e040070b4040113054000691241144141c0b07a0b03c80d406000b4142e60342c01034051129040022034a0302251113050000100b824031014000c6c4031001c00d1600d107940c2ca06140b1040140e038148408039004603e045080000750703521000040540342c4c21103659001480c5400041d41818041e880c144842178101151010000e803503002e81081c003d1600c0e400512150124240c1c00c0303007d24400607420540440c0b030340400720183d9008000d01d81d05030700b0015014000e500c42c02e00711401003440c1034202d1003502140710740903410800460120790918228208040d2102071406202ca07008281082c000c000c5460703030b0315a009110003000f800c4442042910307680ea4103031030154012503400a468031807401034880c007800c0e903006001d00c07910a290024400c0d1101040500103c0d030090102000305544c10700000f = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 919871672 1250 919870422 919870429
    0x80c041a1213020a03110103140901091a010305030a0807140d05010e2202150705160518040809010f030b12011d010917090f0409031814060f070f02 65
    0x14420103882580306600c841d6402102000c44901074504001002030b02110001a80e5800003142926400300003c0700c400040d5005902401c090348121541d40045030411812a00550040d01124010a40d0403c02c005540460744080028040500260003c1003a00c04150258090300d40020f482e10f007014603100322000c404102d030844801d80c8205074940c4010841d000c644408070340c00005059004910024002e010111100301210003805800496040f81e102c05034002034405680e000800e44400654054000ba070349686400399502c2072441484509035502040d012620481d4051a020310f4007656100542307101d07804103a03603010161900141d00c0d107915441480241401e0030340003c00c0d9407135060720039444803050000d040c00707031b0385090a03540205a000c0c4c401e85005050307082e29a1b507414190041490400003550080e0064104250041090b60049240e088018521100041c181c1c4a06071300c7d502c80c0403140d865a00034024002106098055030042c20828411000e420300001f00341e020 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 919872922 1250 919871672 919871699
    0x1602010915020d080a02090604140310060308070b0c071a06030f100f05011415030a020d02030c120a150b2206020307030f0503070507030e03150901021801081501080c04 74
    0x4030310058210900c401901a0861360b200e8103c03140500540c140540342002c00c1c0b2030b0086114080c040c1260041c6610b00e40c4062081c02c04a05580109010554030703800c100d0441c3d400840120b0703561268400007005500d150303050340c50003613200901d00c11541c81301c1e0101d1240880544043c0d4140202030194a100b0420040300102c1e01c410940804ca55040c1c0700c0c2d038011203c0c140c3c0411a0345007403030402503282da2501a40c0b50082e40403182130b9200e4951049440090080e60f01150b13070303a480041070000c0201c00310301400c0b21015041c1090a541d440c5941d40098a804415003549907584040034060886c0c1d1201074620241420b0070944503d8020f903d011440c490f6030300c0039025130000a050424941c0c001d9030201003c1b410b08000c7c3c5182065000103156108850000e010002c1c6030301584415030703040c080c1640300b2248c0c1c41b14009038102224101c1c001c2d8454801e01c400604248181c107090350068030b84501c1490802d59240f110560340e0010f640f0030303800a03c1e00c52001800c21000c6031002c0c90313400 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 919874172 1250 919872922 919872959
    0xc33090f12060a1503020603160c0804030b0f1e0a02031f0e150901060e060a0c080307030501140418060506010e1e09010f2601020d061701050a1116020109 68
    0x106400d00f041c014220459088000113143c2d0400d210092025807510780840380c00c04040300000d514882c1d60714085a01c2d1040050040200100240c0041800140383d1640d00034810700140d80d83c503866165003c580c14070700c0480b0110505200c1c1c000f44040010794003450380f00c030700c0380c2074a417001002c020441c01c528442c3e006190350307002c01300074824070740301041c44506140c4003913800c40707103550520501503c003140a8030803911032103002500f0985184141114000258058545070f128213203400c0180251100b40540f88100d0001d50320914140b800e8010f00201c03c00c2402c170341c0580041502c0f16409040c00901e824148520315041c42100e46407503a140390854406040c15801c0c0d55083c00b0040f021006070700c0f044480e041d02800388400c0c1d0843c0115600248a60b01c0c081060101c10754260290245034070b0344002034075003540090614803038900c0b40018000000200003d6880304124012540700740d08109131083d0900c5030305d411200790200180d402e40141051b0f61100e070b07114046501c01c400d00c003 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 919875422 1250 919874172 919874209
    0x1c0506060d1404061802030312040507261015031707120203071509030e0f19120203370c05030105010315050f0c22090207050c33090f 59
    0xb081005201e81c40c800c44078410f080d071210070496003031600029500d01074032440700c580b603203050003182c01c010040120300d00800001400101c000351030b501d00b04481c41c60490f910071a000d0f6210504403500f003031151019824821000c40055400c50702c40c035100c2c00340c030001d80380c010000300f000c00080b507407030080d424001500c0c0d4011645c030032607880c10800c05c40c0c000c80300060345804c0107100f40020b60008042d0901000c203546007205292168001042d4401c0c014015a0003040c010000c40c070780d45562441208140250b0071625100480e0850007450310245e42c03040c45003403240460200e401c040080c8041083c2c003555600d6038442d00d0360002401c5a034280d100b101d000480801403242c0340518020b050b400b41d03249c510744882d03203007a403025520317803050100c0d2681802c00c80d07940f03031000c1c140a84c078003029111709507003151641101d10b411650348507041c40440c81b6055100d00b000481c0c1015441c1c004541c00e0340520340b80702c0030540c080c0c4584d400032907903268808480040400d203034550700d1011006080e584c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 919876672 1250 919875422 919875461
    0x41205010902101718011b0f02070509040b1303110304090b0a0b0717030a020c16030c0b0316030b0d0506040303050109150b0909071e020a050606061c0506060d 70
    0x500c10014400f0b8903580c3d00081c001090390800c0404100650340d540502c07000c2601082c103040c40380d2503004004c4030325006d050395480303020649004d9011180150114842d000c03039003c0798441e4200304586200301e600a1803401c1200024509052442008a01a03c0b9050164040c00e0724080c05085070456007011a02d240d4460b42c3c0031680c5004207146d001004503410144c64580c080d1101c08031400c1f40d11514043c000000302007031007051f042e1b04940f8180200000c0e1188008003031425002885a44400d40300e840300b1000205070030400600f104c1c0101c64801142c4400100c8400030750280c204080b0341e0f41c3c0061092050004a4402e1000764441c5100390b034005581d6040031400e0b000c40c0d2280e003801d400350200d014240903011802040b500c07071348811144181390b03558101003155400b455528130302100d000c920079445855000214a11281d104030203584613966804144140d03030244000e030b1800300305840545880c4680550010707400c8200a004149030241c41c000400076030b002d042c000001074562 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 919877922 1250 919876672 919876691
    0x50a05060411101106130201120c0503060f2e0302040b04060e01110705030d0c11040e060f0a110403080a030b0303190306081605130605040911032b120204120501 71
    0xb1144900a200507401e0013403080c002d00026a994550003003595a005030948416401c0da80185e0303a032640d1503800c4c0000c1c02017180c80c04c070060041d041599601d0141650400c1c100c40c5142107400702001c0700d01002070328064247c004036201d207085d40c0c80c040020f05a08100120f01d001c5000000c202500c2c19444980104030403000040c4000c09040b202900c0b038015010602440d6000305103142025041d01d0802031224150910030007200445190f1640180780c0082e0540002d03011940c6480356000446e080c2e402c3d1340c0c3c0c042190680380040500788058804010501c0010f0151010703101c4140a440c0009520f1252404203107142d1003100030a00360fa08420031034004580c1070003080003404515020f0612100e00c098010503110640c003c0c24070800c14024000d681c1e2900f81c0c060390040100410034044601c00b401c2c482c405d400721490440c0a801070007441031708460343e0341608071080001d07a030022291001c5a8112010485010700d060360729001c08c800103c03065a1135507001120701507400050040503 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 919879172 1250 919877922 919877929
    0x3180b0105120a03051b0705131d060106090e0a02130e0912090618030f25081c0e040b06070501020d1506140310030602120604180816050a05060411 65
    0x540501c0721182d6407003400e0031400668050b05071240d07080026900488005040342c9942800e00581143d500b14a524042461840c400c0d005075101c44038411100c42c2c3e0605d1107082c0e03501c0302c0d001d00848002ca40107120400c03001c1040ca00046d403158403040d005003008030204100d40d4040782035000e06c2c0019111001c1c0213039500240125901d00940403030075807030201010085002401030780c034a5480b200b812054064191024000361900036041400c9e03032040c1d45040710802514246028050158841c1d586c041402030001850380781c04584401a40c4030132607550701c12070745403e481f0403860b000303515900c99202070780b200300190411754810f000142c0c49925201e6500129004a44010040c403020f8208000a60308095105104d400113102c1c1566a924070004c020703103c2e02640010038981c400650041c154001050076401480300300c03000c0c400411820229409038601c0c240103008017a0420628800d5202001034280e110f00c60300554229074076070340341d860500004440030340c1e4490410714030404038038 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 919880422 1250 919879172 919879189
    0x3050a0c02010624020708070807080d112a03030703120e06040f03030f11070303090b240420030705130f0e01150c050f070f05041a010f03180b0105 65
    0x3003240c4001c2004918000340003203002528040c9035a07444042ca000740c1e041d40b09210b1440034055a1044880f5282c0d5840075a61b2403040c1c0c8a40c10a40c001d00441d01c908620a045600c04107007604000e0040140781c5181d117080748a0003202d5a240300300707101008a2518107101401c401030284d01d564210750074420f002d1059988034003505440e500114104400200031400398440b050701445d0000b1508040c1c985400184401e40c0f10210b9100042910800c056058200240751403080350165695240d502070110079450310041204040074004aa01580c200743d44941111a1a198014026642c01030410965071003a80c42000040c800500b15078202001040d80700217046c00c3c400100c5440c5404141c1c1548072040c0140024140311408100340e69210302c02c01812543c1103c1a220b002c56201c161660b101594865280300040ca08000202ca00e0b00784a40003207889a11405106a6508401151030b43c40080c0007109040c2c0d240b2f44000c40d094507411000040b48104181c4070781354184001c001c2c101c0d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 919881672 1250 919880422 919880441
    0xe0d08010b16200307030f051b03030d02090607020402040605040807080703020609040e0c0a151b08180d06020c0109210915050702060f0d05070c12120207020405040303050a 76
    0x5000410928000d0010b074907034080d01d142c01014415410074000c400889490b000d010140d4180b00d007010100c288100e061800d200c02c0c0c0300e802110444414001440324080c002d15031103074160400d000d1030343d40101d180c00074601c1d8840103141501e800d8003540010202e030020f400840001d600824184000c000800c41c05003d0f0602d0b00040580e2481c6030300080d80f51050750142400703961110020180710804204156548a00401100344207840b03010b40e424072140c42d8004070028002e0f00e100305940007080d44c254851608221100c0c90071031a2039151024500f4510b2243e04400c0c21804c40c1c0c042075283c4003410792080e03000c0000c1451046420010721403100020080f00032002007024558440c1c2140040e422070301d030036504021400385440155214041d040c1d01030b4001200107801030108038603000a01000c40c4100d0101f00c0d544132a18204c4490b80120401400146020010080d0b075006914035801c403c10303680c0241c6808440d6000c24190340c8141d034110040703500c0b50144074000165008600c42c2 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 919882922 1250 919881672 919881689
    0x60d0905030c240c2b02180103051b0706020730030c1d0d020301060b0a0509030d020c060a08060d060908071122050613020301030b1b03071d01120e0d0801 68
    0x507030416000040b45032017181d42d141090007180900114964220705018014400c2100444d260140320214441007a5000740b2640040e1070000010a420341b884c0c0c1a0114024200845080c100540c0c0d5440003548048010369440034200d01c00f00c5003402080d642180200001020b40000d01d1462002e130542d07108083c1c0d00248800140b040c3c00e2a0440084414560001c03581305500441074000f182c0101510741050b036117282d000498886140e000341c014100e48405408a43c02450a01000c076141c544e20ba0b10340e54001c81c100504190648500089a00709070002c0220300640c0d1543e891804a5405210071164018003203020024084110001e400044081c0d440d01441c0b10140015900c0070041c51694a0150341c0d20082180d035100c06039182e00301c14400404550f20f584a04140244110844030018041c08031081000b04c0108001030f68011105d0b511510708070394529103918180c108a4030340c1410801248841011100c03140600030140f80390a0280403141091400205200c0050b0420301c103 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 919884172 1250 919882922 919882993
    0x408100501060518180a0b180408030f04061512030e011e03020703031401090e070902070c0620060a150501020a0f0201050913020f0307200c060d0905030c 68
    0x9403a0030008440002104c00380d40324246000f603000a840100b00c542c3c990109403640c04000440481398042505482c08444800b00c0c0902100b44a400d2002140d00400c0c1c2c220600119414021400059400c80e22408c2c001c00c0c03400c40fa1855000d621102d41c00800b5440b20070004a080c550488440c1180140a00e0240f40700e08411111440340c0d0030040034082011b40c0082e2020505202e86d001180700425050b00e4110b41d60341390018005800e0103980841540245d20703000440e20058822070385050b900001d02f001040c507064098411030b00c1200c4c420b040c9010942b40c407091440c00d001c441d1013005038000002d82e141341001031088022041d080b942c1903510440c0c0d0007011030300d2085524001076091905c640e4130340c54440810780006807190b80c03888443c0040703045c00c460070100d40554801c440590350b09540d1421412045e10015548120111300c1d08020b481500c40e0512800509407000307555000706038517040d40c1d100c0c3d180d607020400039030103030700003e4958046103903412041d40b0340303d6218082c80 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 919885422 1250 919884172 919884179
    0xc12040b061c0c0b0a050c030c03090312040f0506070c0512011b020d14030c09150a120204030b131b12050f12030c4b041214010902150408100501 64
    0x340350f05000e009050503c04003144001404e80b2030720444d0f0100c14600706903600c4581081d445075994101e580b14a109010b4002d00d5240342ca4640c040e1022a40504100b1350346520b030409005480d8491401500c5c20201018040383d641c54004161503210755450002400a13a03030311690240565200c2c81070115004a2000184607500ca00014000310401d50300316580c0e1a100281401e910800c140980c01411441c0c0c0d03101040003000c041e2125040ba525a40c5080140381c150380102e2007103000003409000d500380400d03103400039141100703180340c80740104008000c080900c44c03030462550740c4005d0701500942000400c020382800000240c86095006100040b148032002d14035010080c02d003040703e080450075072107410f00201d85642a010f5410380c540b103100c0000c100c0543d84031942c0d080f1944542c0114500700c001c60541110210b502000a145042d446550b45001d1440b105280c0f00484d0348580e00c1c4000359a8044001c07821005808820b6501e51403c030080b03041403249621401d40300d14000042 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 919886672 1250 919885422 919885433
    0xe0a0b0f0d050114041d0a080904230a050105030d0f0806041d0a0c1a0307081315051f0b0a0e0415060f080901090209060f061c060815040c0302090c12040b061c 70
    0xb20400741d40050003507118a01a00032600030400c00c2e00300840bc01c500c03200c50740c03030752801c0c1000ca006550303e070410310290f07032540c003030659a8044040c40c00c0040d80e064046c01009100d0782c0d000360800e10062000c5042149900c10304000705480d00858241d820406100d0100414800404024003400e0020340c845002d401c500c020034080180039600344510180001c00403580c0f09200007000d03501003660031091400c3d1925800400d0100d801d250950b0550081c0800407042449810031210203900321b6184c0245100100c40c006a000c2100750840c0d140d141d4105140d00d050a4400a0301099a81c2400c01101510090122a01400c2040d50764508603121000da10349241e915802041681c48100c84569180450305a11a07910b40c0301360310700789070403c40781c5a5050700560204c4120500315240c500c5144002851480140c80081840318201e41c108018189100c17035a901003000b49145091407050300d5056004101220100d40d48884081042144d00e4050100064440d141009a03202c20856844 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 919887922 1250 919886672 919886683
    0xf0503011a040b0117070c2901090c0c080f0703032d0203060625020307090e19050a0c1202041b0203070b0402060c07170105070e0a0b0f0d050114041d 66
    0x9501079a1103000382d4442d6400740c0711000d1a00c045c409003400900e0038200082181420100032141003108050000001503446c80d0210701081c0200210b86691a041e0100001c080740d4034100c003400f041e6902c050208500300041e11000c0c000103440c07940c07071100b0300c1e00404031804803101480d1140440c03e215103a079000d18018040400c08040183c0d60344516000440f9401520f40218038480c0310080b00c07090710343c1d01d226569414400e8007205c02094503034009005480c031685c50030003207030f0040719030b81d03203001200e4020070100740101c2c161070b100e50fa251580410340c0d80d2a0000c0ca41580034841e07100860a0a10440702c1c41c0c091940c40030448903050b0030003900c0341701d20040030344100821000305e0207540e00e980407a54003500d0441140e4038180e0742d02e0a580b007103500707540004081d4a8440041c03451409401e004150b10001400d01d9929400e00a64900d2074120306130f1110b10190030b1040e404190b90740d1080601070040c040300b0100015061080100760b464002c000e800c00841143c0e00840b28800103023 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 919889172 1250 919887922 919887971
    0xc061e07020a030e030106090501030f020a090b0f190504020301080303010608100312120f0204080a02040b0a0302031213080d081914010909080c1504050706110a020111250f050301 79
    0x10103004c4c046074000040d002d4501604071310055441d000000042007072200703080d16014802c0c0c0c0d80c04034141eaa12000000c0320b146a000981102d400352030941ea0385049583e14104078110400c00c1140c82d281e03030224007243c100f604107107200e500000042c042c0c0e5400450503640310f0000001c12450a09560355551f441c54084c040e4030500c081c0510680b00c0303032100d0301306481c20f441002085441e190307035121007a0355648645050340158030300006c400c014207103a900001070380c0c0c0141c000e2145510800c40c601260340b06000c0840c4086241c0400b083e680424000c40e8a000303880c0d41c40c1d0100c0e003810588140210200380c0c480302c031140340c4500c614458424550150441e148810001610301c3c550400d50000d1060450040d01c9001302c06800d101c50807600d0b1000d00a5000b0004c8551168039058191019580c400200307110364403560b02500150b205401b405080410101552045c0080c600d40c91440b9401803101609000c420200344001305000e40120001e00080b0000e000c070f0300880c0b0321036802c8501c594 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 919890422 1250 919889172 919889177
    0x150f080603010b040e010506010e061204080a110a05070501140304030801051522030c050904030c0605180a15110a1407020303040513150603090b0f07090b0c061e07020a03 75
    0x10005035299000c0d480030410060142c4240040803130080f44a00822084622a0100700841c3c0d10700d40504160301a07429107911071aa27000f850701d941d100c90580c0d406c0800040e00304614041c2010140c9014400c0c81c00310351244009200c103a04260014000900010020348d4202c41441004082a44000214112002514504c05001e04005041039521464140701a0036140d11803946100c940b61059034210b0740140190507107141c450701002088482643c3c0a00000c10765100d500110f04180d10407900181400c518a000c1039856240604040c03502a09480f40c0012401c8101800d0003800388400d4000440d9002e07103002d0040401070500214903414640c014408181c01046441c02c00c110b03405010020702100f07861181030a000054445084400c103500e03d024000108139010380a0f10141581c405900f080d15911196004282c0900802030406c1100d01c00000400c03103011070007419484003d101a002e1850310010780314910300c140c242c02c10501d06140c100400c0300e501050327112045500d803 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 919891672 1250 919890422 919890437
    0xb0f090424030b070905040209012708070e01170a0b07050913050903030906070e18041713080706090f050111102c07060c0b0703241706070504050d0203010216060510150f 75
    0xbe01200600f52150380103114103101d4600040750740345090325914100d51103200c415484441a04285407200881c05000309106a000301144040340110302410f1601c40141041040e21601d03091901560020b0350140300c1034100100f03120f03110f40300f405159840400e40c100724049070b940e0030100304d00d024030005400009840d41d0110703003005030810705012580f0346c0720b40b41d68554020b600c2400007030050748234071702c2e0700d00c0741c840001031541c00740300240c08465000130a20011864100199181c0401c580401240d01401e20202c0421001d1300c80e2200409014544000b090048848100750f82009403018400741d00503101049026442100e2691941d17000b0400d40c1c19458100b400d2340503281c0501510381c800805141000100c0c008100d0f50100c40d194a8140350584402d00340c9921400152460310001d242000281b040f8101410541c03900303440500014038007100d032304144030b005c207200d041190700307a464000b07000c580c1083c04551400307015500c822200c10480268040c000b1402c8000d40701c00e10120 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 919892922 1250 919891672 919891727
    0x3050c0313031401052413020c01020a0f020709110f070302010b0301090c1404020c06070e060d06082413020f151614030a350901090c0b0f090424030b07090504020901 73
    0x45030151100c002e0104001c0d5214074010b6030151480402504de81c0051195040c0001c0c01c9280340190088403030740601542c90222260700380e504961002c203064040d5901c2c0d007403960b01d9807003d200c0d034031a40d80a000c1c40c4070058108043c0c0f4090900602409210300d005102d1541803c0000c00c669070465050b00b4044100300641000c01c0060045001001640b40740c820000345410000c9203080c00c550398040c11500c1c00180327141c0c4204146083e41d14a03858460714a80c1d100604000c2c0d06285c802000401d403691a40b081030040350241e02111901224a401715200c1e020000400c000340304580d13524000e1420540da58200808600e6a542c2c89001e91000c0e1b15020078080d5101101500b4000c0030141c1400341c0b82c1074150b180a040c102d003048032240e582a00c00a03200c1042e0060f10800625800c4c2e107031500c00c5c441e0400c80500302054000c02c0446120142d00200b000d100c215000440c4201c0a0b2040e51070300d08005031000449500c12801240100500e44070f42e0f80c0089621180c641d03881704244203c04 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 919894172 1250 919892922 919892959
    0x61b0333080d091a03090a0b09030f0c07150e0d1709060703020d0e04061d0a1803090801060e041a07090302030f03120c0703050703050c03130314010524 67
    0x440c1e0011000e070040c20721040001c2c0d80600780ca0b0903161240302a001e850550882503115100c1202d03841d4132500200002d00024010400a40c0c21048003c00c903401e01d1441091408164131030f8001452641c09498204450728010352440380740009401c2200003030b1107080210701214840e8400070405240d1100c10401c60005001b500c101c94000303410706031181101d14020b0b40d940c10206042c80442e076040c0a00041d8549400307030905450342c1c110014100810043c4400340c00340301034502d1781019100c11804400c1107504500281d014001d6071803c0421385051405421569075411400d41d0ba900e0308100b00105090000c04000101c203100481a03940d681d42c4110b60912143d080250306015849443c0d250240000207004181118160010180c492a4400365148519400280411011b06c09440420302402c040c105440c14403081ea450544000003a140452881d0400c9840007281560ba0020720000d10034107500400041c0d0a16140030039003603036401d46030341e03d0348144108000711030012040c1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 919895422 1250 919894172 919894271
    0xd0c080403080a051b0703080a03020a0c1a010315051003080d02071209150e0d060c2a060f0e07051003021b03121f090c0e0904061b03 59
    0x19002142c03641c0303a003150b840c002c15981c4940b0340740c03400815514201014040118409040b00c0e032054000e482d00d80304c0c030300c280e001e50010340c0408140002d074406007002c903900017003180c2c01d4155184054142e41c10b515040458510869502080e03514017030810026030b461030442c01c03c0e00e400124260b201c0007941501c0010744650b84005207048044c040c261900340d0003400d40c20549241e8550f00d0701150f040402181c007900310120640e80719040740e5440010525542c419114000c01c9c1ca0080c03041203514075081c08031108140741400406801174582e091080501c2031070800c080480003801070000142805503030301502d0081a224010a400c2d840c089402036040300c070786001050056030319a89490302c0d280c90b034004040c850504000c01c40081ca424028ed8160300400d20040f4520a495003009074800003040d140850105000d5188d040083c6592500c0e8864407030740c4100400301d083c00c815200e0303180f1540211100000e00d400d0044080314120219560803071140c2103401d045c0119102c0c0420071800 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 919896672 1250 919895422 919895429
    0x30d020a0308011239050411040902090402070b070c0312090f021e041107120504060c060e0703150b18010602070303081306060608040c0b1213030c02030609070501020705030f0d0c0804 81
    0x840710103c5c541c80700201c003202608484c540c0086034481660311802d200543d5034200305a10244001c000c2400a00c08030b6000d01303150000070780f00600b0301199540d800000d440540d030410220725500012410581e1209080078100b44584090008900555038482450103014000f48145010814034030f0001840e5116040e1500081c42030160004102c1c0f101d20306d038003084041e0f07085000d92140604681c00340d01110107c03601540d649401d90b880f074854a00500c02c0f8080032042d802914400404151004410f40c0c036080701210000d41c1070b804100300001c0e0100b040610000000e82c6004005d91900800c0100849400d41000d60055651041250072106000c100410161512038082036144d40002801d1065100b04a07004805458148a0681c0d0054043d01110600c0200000d480d0f48014070480031102d1190801440c0948a60b001904080f821150074003541e016100c204400d40e8100101c5004000030b4006d4142c400b00a070507152990000080c2806015a03009040c1c2000b420b8400c45004 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 919897922 1250 919896672 919896713
    0x5100c1401320939060f091903110d03090e01030606170604020d08070218040503091e0a050f0303040f030503090906040c0207141c060902030d020a03080112 69
    0x4078a80807007402e900361110781000c80551010300000d600040c00003108845080c603c0030b001945002d07645004410b58600079051440c82d440c00c5500391907150140509540310680c118503407201119000e00c0008081e180c20b014010a8040c81000860081807401e0103080054502843c0c403540d904023a00c010901d40c0c00301001c490701c50000403d1111651284c000e940c9800000d01c00c01d0b45c155030050ba80c20094a010398400344c1c0b81300c8040000e0005009005007803004e090328445113031499403400380b000121000c4d102c58000242d811098503014498000450780e00380075921000c0b00078081041040305000345030091000d80c0445003156401c000703540090854071034805205840c0c1c684691139802240540380078010007804038600386420700400754000381690041020614000c03000a589000d20800d07508500070441840c0740d03e020003c81b10006025480210300283c807032052501d04040c4400e08001c54202d51054000a40c0c041881070450b44102a070764841c0c02e032400d0801031203041c41201c2d000e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 919899172 1250 919897922 919897961
    0x180c0305030307020106060206090304060f14070c0e0a02070807080a0302071b212109171b0906060a080a0b0907030c12050108030406030f0b03061e0105100c1401 71
    0x20000300000440c4034103100e6000307001d066030700e0600781c1e6601e1080d80c1021240d08284014070000748100e15140817081c0034600b0245003036442a10000550000e0780030389440b03501c1c820030300008404c40149900505100802c501c0c00815031900700b40f43c002c40300000c1c04208002114207025100f0340607500300d150404001d85060240c40700002c1410303007500c50089505080c540501503000740600c2c180c401c0e90003080d40707400086d04120b02412501401a10024007076000300200e000d208000400070098032400041a1400d40d0003c00c071075016044103194458210300081204580702c0c113043e2800c0440900303141d8095142c5424190203804400f42d119009010407040082d07032a41904900c4507407040d03440700c1c1c50001c840c48489050700d409002e80146644100710811809100e540107150a40300d210703000808080000c0000d060041c10f43e1a02d03003500d0080314000c94010403007189401440c003103c0d41035440c40c2e0310f00c01602c81c10030140040d105040c2c04245035040c14003900311544040b44200c0041 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 919900422 1250 919899172 919899179
    0x28140618010507020102040e0a020304020a15113d0603150b0111060702071a0705060408031b04030f030c110307081e061005121204080309040b010215040204180c 71
    0xe00c509204006194103609007004500341ea8010700c211400c5d60840307913560040ba0307a0000098065403010300f00f02d802140015000030b0350701c0320501c15003e0311001da440003c02011080b5845c90041d00c0305040d100740d01414107041044140210a02e2492041510781c140d912003c0c2440005000c5944083c01c02c050250101c401c02040d40d0000030800740980f180704103600c82405c1c1941c0d45000721016030240e071245006001041d2001c4407203e103000c54203169413400c400c0b076072450300f00603003982c08a5082c0400700601915000820030800c02d00b203030803031039070419103103841c0d080c03500c1000c00c0d0150034466500e50150501c16191214114200090100d600d490740c0c03582c070380355207501000500d0701c030403040c4810243d440004140140200b00c1c4222000078079085c103082081c0581a0201e0071110b1042c200781c44861007182c80500000d144410180d511880140140000e80e82007001e00340c1150407002c501c18094285040c41900560196400100c00220071440e1040500189000e0041c0026a8002 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 919901672 1250 919900422 919900441
    0x3070f230304090f02030f0a021b0a2d0c0e0c07051902010932031c0804020f0d0b2404060315060b0a0503010b1c06031b08281406 57
    0x8100f103c003802030400c94401380108400490005507400c103007002c1c8090100c2c509500503005003e0f25112140307002d042d0344112200e40c1c900f4001070000c07101d40150381402a1a03402c0010303004c522080701d071400d40700c0c2402580d41c85c490507800d020380303201450742d240850074040e400810340c1c0320b481c0d10004517100e11805910720b400d00d4480700341c1280060310200d80032508203041c0007248810340140d81c0c40c12015076881c1d06030405546829031580c0510440c4411000d03006940e00c8065042000c5c0c4845041d8101401444440000d944185001d5292034907041c4c0010390400000b980204440b81e400140703400920f18814268200c100c0680c00b60405901000b4000c000079901c40c3c81200c41410800740b940c2d80448032050040710b6001000c21802e10041103007064442c01084000020410403502c4a245a50141101c000f90000e480700904418008010000900000042c10902c0000d000390208803609007400d140c40d02c80b83e03000300d86111000040103601e03607240c4030107060742060b0368072840c1000d800d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 919902922 1250 919901672 919901677
    0x4031e0f12170606090307030803060414042303070804090504050c030f0f07050a050f090a021201030f02011d15091f03090c060c0302030a2d051309050903070f2303 72
    0x102a0b9036440302001c40e8062800c40300720358941c6005405041080d14681b5801d806420060589810540340c0705a4190f031080080c0a5100748c0c442d01c51503198040d01c880700d00d482c00103e420a04242d00403c01e5001044c450015078040303d64803400800c0303503030311480c1146c00c2800c03059609030140300c2c02442c8095040b020400303640c00300f07140d403c0f02c200c82c0c0d90b1760030450342001c244250340d080080310b101d223401030604110081e80511102009840c0000740785d891101004264000e9509034a0a064101150b030702c8054041002162080903608004400c00121110307042e410300340031403c1c00100440141c0b5041000708000c1c10a03442d49002222005015010300346001d411a03041c8414403010031018003c2c48001c0c02103425600541c10b04920031000d03210f010b020000f004041c02d259882d000b60a546043e0242d00705401d60350140c40304a0650f00e002c0c8406c00f0380121840904140803c02e01240000c02d50301c005130070080a000e00101030419a0710f0000103c1181c00c240c001c03910002010000000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 919904172 1250 919902922 919902947
    0x20601120b010e420102061603020f070c09061401050715050a0f0509010506090106022b0c052424040f060509010b13150e100e0406030b100b04031e0f12 67
    0x18013404083c800004a0710350070121451036490500c0540c400b101403080d0b000d05480c4103000311640c5810304580306c01e004001194414501240c548000340051114a034582d840c01c01c080c288181044c0b503954a603185030140b42410244a035030703140041c0c4900500e400010a000c1d05d05800c02a41c00c0003e040c5002e050103c416038001c039010030000440510015204030b07410780254182800f0085c045196140c0d101802c8000104050302d40440c0c0414010700335400250140310414217202c0500c0804641c0040c001d166881307143c0410f4141e8010100100c24094600c1c04a80010707215964444079801810250020380e00b00400307034008554820b900c401005403401e03081c111035049079158502d0044285048120f40003805120b85200d150402c0680a082d03848181415186d9541c80c4000c40c003201d815500c2a0b5029032000c0501034100c16214900b00900994081c00d8540f03425504c54104d02a00600c4040581d6a46001e142c10311003e202c0f03001d09161310840d0382c1c110021040009180c0d949012 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 919905422 1250 919904172 919904281
    0x5130504111804060e0703150f06051219140703050604030219020d030c390e010620240601020105070903150207050f010507050a020601120b010e 64
    0x1e80390307185094010100501c40d0002e40340301d41c0d0740d11360314180608414066014144509500400024491540303803016500c44400091b0408044403c1d00c03d980e01076200c54021106200c0005603040302166040100440c440c204c01446141c6c0340c400c031180001d4545c0c0e5558007960101104100c40840d945000b20b01030782c200d030300d61280642c12108603041c032100254046010740108000a00851203600014011000b102c1d640390581194012103c02c00084070b03c048481800401d9034403032000e0000074011000740e11110b0360504001401801d1803032030031603880150400c041011501000032402040c51201502c0e51070707188164481884209668550165007802e0001e10f4440c13180401c0b01c1109d820030111500b01c0c402d280b0160080d07104080c00d0b41c10b4040c507031a4201c0048240141030041300715958440e07594014200c02400c00006801000030104022403e201080705900e040e810360300304000100e000d80f00c2030140009050890403580d041c2d0034004900c00104125030a400c41743d0b9209 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 919906672 1250 919905422 919905443
    0xa03080705010519140f13020a060f020f060408030a150b0f04050f041406090709080a050304030b07050c1c05040914060f03010605011d01020705060d0c0e0a032a05130504 75
    0x702c11007003c3e140c0d000e55042c9040c0303403140000c411b80c81c6580390b5078000c00d99401e03e10701c0780390319008210701007042e411000228656a0103800c10b01c5e0b04102484182c104034000d80110705240e91028003520020b00007411607a11104030311881e03c00403078044010030600c01c5840e0303204021410300c001c68026118461281a0649070b00c4143c3c10036004460080300b0b5280c007044a541c4140810010420207011003003048215031000c240308104001e50806503004900558407a455803401641c0340384001c06220400105012240b03884c000052990450410300e01c18481100c254101217030385004503401a0507050a20300c0b44043c000c049a5094020f100544402000c852903074181400e841144c0315450000c0c11600d006071158006060b505c0f0800702c148141c6400350359070000101140c000f90078022800703035500c03941d01c009500420080b807052410786a01d000689561074015000c051050600850362843c1c020071041241070040740c0250000800e03414060141028040007881c04680032215030410 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 919907922 1250 919906672 919906711
    0xd020c0402071e06110a030f050901020a02070b0a17070c0210030203010503030d020d0204030605011502210708210c1c180f050109060207060b100c05070605090a030807050105 77
    0xa0007182d90030341d041441c40b101811424460b049040043d2025540d551350303001c2040c2009030050040c170500505135808030b02000304a02200c11070300d028000010030f078030421046841d50780200d00d80049458070003410b0780300c02d0810820355030350b440035046086001180c410002d00b203400c8a001d41000b0b00985243d100d500e40f000e025022440203019196050348280403000c17043d81e0070380082c009001504005401d141d03890f170f0b504c3d0a950081c0c02c03140300350a00a0503442007580c100308503202c4c4031030904d0440601242490f154914841d000c00a8481200082c1c1010004403884200e4015500d6541d03101c0d5138075000d020716006400141c9515548200d040a02d12030300964050a00d00301c2c0d0031a40041c3c4bc8820341e0707030345401d207240c03550454241d5200d01904000c90f002e13101400c10240185400314880c200300c820442c00501c002140428050303140ba041e800f00d0b00c0012043c007921220b040841e941c2c2084030015001070001c0d4001010a0000102c920400c4410740245002e14a50f030349017000c1c3d081 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 919909172 1250 919907922 919907929
    0x3010c110606150d0f110a050307170606041401031503030509040c2a17040f0e010b0a0206060103050a15090c180b070b0408160b01050901050f0a03020904020f120d020c 74
    0xe4003030030000c0c00014441c0c51110b800d02c0d4464407160f41c1700900080e00e030300007000d0340310260008124140402c4c400701c104507045070002800841c040e050114039600345000000030f00d617406280225624140803404c0184541d02a5100488a000284401c0c0082d036403440d000300070f80d10003c6100e0140d800c10180004850249201c0906091444c04508100d01340c0000b1810320908104103413410950007890b440c007203100000403c05001c40320820f0300307801d040520411200506034041303a49030808010502165a0205031a0b400031003d18011880391501c01c9404041c0c8140501400c2d404100e500000311424140e0007011900e9903911020101059141c0844480301e461043c0c2140c1042003195500080d000c0c2c4c1e10b16480740c0315100d00d50501208001c42c611107d60306604880d01c1102d0b0006020310310388001c4e0f850040000f1103c03060041d202c0300200d4038480d15880000e021318449404541159a003034a80c5c198100007070000b1291390200d852030f03503841c41011008005030140e034a80030107a04 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 919910422 1250 919909172 919909189
    0x1505040501020604080a0c0b0f011a121f05040c02010b0a12080403060f181211010507200a05030712090b1905090f0301020f040905010504090f120e03010c110606 71
    0x39016000741106985545440c2410780c4615030080401003416a0305000401c82150030780661118482e40490798107181107200c3c50001c1c42c03590101c405050042040d00f0010103142c50740009455654002c848003881c480e60350400c0c03a0400c80c1d005050241b9104400c3c0e0552020007000c00c101d83c0101030594444250b81581c0b1900d83c0030301501c1d000c0100340701007180d0b50005042c5004410000401001010540c1110070b0895021940c28440900380426203502100311540c003406ca8000300075505050001030300c007403581c0780380b07468041640c00705401191040c02440b500340d23084000c1c5c9a032740d0382601c2c012003070790744140460000c120038803000f088809241c0259448940400040e82401040c2d503425a031035048104200c0e440820404e42c600030f61028000b810742d00155000141d112414803038024140c5005030016800b80e032501c601c00000c134a00300b07640d01342c15801095041103100c1c80c1d00e080310500c0c59140300540540c240085141ca16600c00d00c4008800514801d4030400e448604c05c2010700b4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 919911672 1250 919910422 919910429
    0x1514090f0f04080c0f071d0f0f150a050a0608060a09050708060402032d0a0b150406050915030405150603030712080705070b1e06180a0b13050a06150504 67
    0x700a407000100014200d400400c0c844580d2412100710102c00d550039031400100360000d000d0895a040c51420950403584010340000c181924540d841c50320750060710352408010010641066a001c8401941c2c039591003140240c080901344444641d15030101401c1007400342d600a000d8040e81000240c52503161144070300410141e683c49c1c409844000170000030303400c00380c1315041380d4401910000d960800e1a0303440405010b0800200580d260440050301202e0010b65040d0142d803114910389881c0c84c4013000c0314140d6403181012911f03201c1000125a0740c080340044070743d803000c001003440300b886400150409146200c10b0041510341d00d1005058490140d29002410714400c4254541d81d41d020b00c0500c0d0344000203140c041c1c20a19540c8500c0b00c64002520069880c1110482d40008001d030420815400542500c42e207900b015a007549980c070b030728010500308840f07650301c207000780719610010b625803403895100303040c0410b003841d0400000038141031080f0b003060100c8484c41c0300780b940030b81c0907074049 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 919912922 1250 919911672 919911691
    0x2120d020d020d0e1e01140f0901020f030907091a1f05090d1a01080c0a0b090d0c0e2a0d020c030c01090c03120203040b0d0905011514090f 61
    0x14a8120842840650030030740ca181030007a000d1000d0340020394684520521000c07000000c240c1340720342d0b1511000001c000c21100ca40ca9041c60807192148090081c42600560f40d40590035059907800790a900a010368401d007815420008141b0084920008283c0c0030740720f50110070010399410111070260300c07510829013500810b002c0c1c43c4440b1070055185145000184c0e08000386817000d01c0700001c0d00ba0071810000c440380c02c2504901303107142c07109151550142080300000c006035179025000a60300307106c611a05d102001c00048108864840b8065682c41590003c0110102c5031901144041f01104079005d9003040d00440c0601c02080040b0030707142da050942e401007441c007544080e400380607612803203610f18944800c01410303101100034410401d44074050303040c061003103085107031a011041c0c8000310f03001154010f000901c1150152811600e80c02440540000c41810310f1801c0e90142078030b0810302c0491000c4d4000060000f003007440c50042a4001c030340e03030846581d480d481c0340e92003402924201003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 919914172 1250 919912922 919912927
    0x1a1603021e07150e0d080d020c060609040b0c0a3e010902011b0201091724060f040504031101090606080c0612010b0703090f061d0420460212 62
    0x59030003100418008000600034a40c40c0341d090311002d1b400c0e8007480c81c10900070390000c2c141c1b408a4050180581020003150301140380e05281d251542070303120203055100c4065001a03c14035441c0038602051b0130611681005494201c3d2105242248210501500d91040c08400781e244030305040c40340e42c0c2c0c030a6050b102d4400b1004944002180e042d0040c0c0100d052060241010590301000310354059640900d50080c441c3c060829100d0606052036000040108289001c0c4403807951194032188500d43c0c01e0703034009000d80e200e0908aa941d51410803401741946400c480070705101d0b2640084041d221a0b03012280285008820300c0b03103510541955440102e5808018008000034500610710705c2e000e0316041d424951550038908180d403644c1d2100001c201035554110b940352412080e0418110216020000030009802c299042c01001501d404048000503d140402225001d41d0240c480100000e00a0900b001c6c00c2203412400700600d240750788a0000c20900161000944818071503942c04a1030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 919915422 1250 919914172 919914209
    0x3090e0405120a120e100b010f0806060703030906020315010201050610140a030b0a0801060302150f0a2d02010b03060901150b0306040b04020a051e040605041a1603021e07 75
    0x2000e6400103103010b42040411186000c1000040c003e14017034481c01c20103094000401c1c1c054200300c2e40034400042c107000100c81070500780c0d50005e220560050301600d0312a69030340c2c02d25040300144001a40100003d102006000d1050066500160116000e030002c106907110750042000d100c2001014500190741d02500304803a0b4405400360903c12190305011a540c2d210304000740d0305000940101400d81c1d0744480400540c54004008650712202c40145458800303c0039918803280300390f141100c00d1100e220350f8050120041111030b404142803100958203002d01840090190100d014101e1083c4111404903044003410710549014406506e0400345030361601765007030183c1e00003c140c4c41d4003555031210308840c4d490750300050000d18016a101d90390b0b030f000100c0c3c50080014049d00810a50018401440380350341000864081d03980c0c0c0080b001030118101404c904512541103040e100c1c9044403108003c2603000070302c24500120355000c5025105619a42d246e86010a22a50b03103494807505142 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 919916672 1250 919915422 919915453
    0xc141b060c091507050c030303040f150c1d010c021c030825110a05010207060506100216120f0210090314061329010e0a180507260a0f03090e0405 64
    0x40034540c5c4110706450721810701200003811500708680607070b02c580c1e40045260800041c1031101040c0d4035412402c000014103404024a00c0541d500c941c0c2c110301940520740810303800b0b40e44452260750300500040d2180e0b120001581400454101240400d42002c0400d03044020b90551020b41c07a01240740007400c0004003012100c1001d40710700300c0c0880c0200940e02c800f01d02d0a000a0007458007034038010130241042014840141f810070086021500515041142c41c1c0300b00503400115141070b03500c80c020701c1e507c0c20011040c8004080083d880a0030515806503035411414610840c1c0c0170b01c0f08241c15910b0b00d0186920303850129000c40a62420a04080004a680c1c096011104c050300c04118942143d81c0e0400805030283c1204000c01c1c1d01c141000881400c1d40a00380c1e01c0c2004441c18000c43d0790960350555107000380c0c018403010401c800f100e00a10704142ca40180503010b4401101c3c05141542001c00000510502c19800582d9208020070885548140f16014540c800000c1080d000c0f0240b02 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 919917922 1250 919916672 919916677
    0x10b012c010507050f03090109122f061201210b0109110c01091a010605070b0f06030a08191b0503031609050a03051608010c020d030c141b060c0915 65
    0x1a01e041c0b0409100240214404020f42c08100903140020344da202c10701c00014003d0b840550014100c4a40903c1480c00120749420100000303c41554000c400035420b01c0481e29603030386050751900b04001040c0a01408010b403022070480b6540400d205100c0030034000300e420601500c4000d85050b04080041062000c076a020100c5004841c042d0740c01c14041c101c020b030a440e5065026602c0007036010140000c010182442c80c0149100d043c1076240c03803032560b610107402c0d000904070121025200b0000340c0c1c945051207805a1241e1107046a5038440c1e4102004078411140f008500019401e0705a9206d05001035010b41c00340c0d90000015400c3d51b40d150303120718500c18180c0d165020881021400140c40c1c4441a00c1d801440c40781010308180744118020075034041041c2d020b81e2a0384c0c104400040c00c140c000c10b611034102014034001c20000d0809001360b42004805442002d28000090400d2000d001c0001441a071860350042c1e0301c198940f901c00310024000d04004990040c102d500d209241000e00e0300 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 919919172 1250 919917922 919918007
    0x90501170327090a020a0801060f170c16051b0604060905040c0e03060a0e2506050307050c07060507121701091d06010e06030d0212030601120b04090303020a02010b01 73
    0x15401c40b0304400852140c590a48000b840c10740c02203240000c50303030854911805020140340540c5448030b4018001c0181c0040f480504036441c0f124040b4403161a80c4003142c1803490b140f1210107261040d840d000340d94881c2085122400e0701e0010980c6580e18100d41100d0481d21030b540d40b00c40c0e4074100400c020041c003104040c007090021829007039a403a14240003203803150341402c0002900006800115080000c140d4140400e58018140340481945620825041c1c1f0714601e003132926699865801d039603a1241448407803140c400c1d4540001c00c1a0300600512181d8859004c0d4200354584c0700b000c3d0340c3c90041858680c1032001c600010300a00d00f0b681d001c4210000c40b14400c07982480141c02c02400c2c1042a00f01c580c50032004820418103003020000703814050b8041c8010300da6007001084d242c51600002c0e0010381001400300340d103840d0b11055040401c0006004104001c00d4129203809002540402201030140d400e140c1d809420703600403200682c03035410542e07038890310030001500e4008501040c1d1 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 919920422 1250 919919172 919919227
    0x3020601090f0f1406040c08010302150306060c0f0601050a08161a040e0108010c030b0306010b090114070615050118050f132423030307030c030e120105010905011703 73
    0x2150783c007140c0180c0c02041080100741a4100c001e080c60024401951041510141800302103001000103888402c50841c0c00664600501d03104d440c1c0c040000c0c404d2044460310f8802c4d1041c40c2d0101400302c8003107111412202d0846810034131a581c1c85c920b03a01e85000484145000110a0703042140030140380e640000e450031641024a456121024400c00c220281c00c010741d16036441c0044805103806208007401220100c00515241d8908600441240b02d420125810080801c00700342d8a0080d60f41912f1160313500890034031418141031891811804548200341c0003c00e0002503d000768080e400c0309094600243c80380204403800710901c0070701e604404082001c66034840c01901e180c0c0c030300c0e0014003c0300710348100c03122041d207003003510a442810f00c01706542021008520107401e660000850b03c041d0351506242c070303500200b8207041c3c80d00c03040d84180b0380d0058901ba0845088040660095041e00c041034400c2025980324800400c1010703150800c005554001c0181008010204035000070842d03a1740b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 919921672 1250 919920422 919920431
    0x506060915030a020427060f060603020903071809080d05090d1b2303040605041a090105180406050301050106051312110904060b03100b01030c0c080f0a050f0c07060f090303020601090f 81
    0x1410501c40080f11b45001e44403141d8034100904251807602504c402031070f0910f000d44c10002100300090301d85100f8401e01046440400d2815014612504414280c1d42c000000c25204d06070b00040340d01808040362030f03941c180035a1092240c11405041c40b000740f846a41c0c03409200340c50a41d030340d203194515040c15005110700000d40d004818070410003071000d801d25965143e1501c0c07400e1102000c8107450300466040741d0b41403001c010316036804400c1c2c841e80352521201018070b071a1400410010812500400d8055091a001003a013a03007210003001d40c030403400704007001e0607514844445881541a4010216032142640c0d503400d16120309101d42240c062403001503109c0310b07000000d1505181003a03031900203840741603a090940e0940310b010300340c1c031075400c111954a03aa0b0b542c45c10f00b4402c50040350314240b000701307400c0c6425210f98207031000d1a520140841d03445400c603a05527a00d01f414862800004c843c1c03d040341c4450700c220407140807a581038004102c9a4208486d040103440a00455401255107 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 919922922 1250 919921672 919921721
    0xe250e031204030c0312050316030c0c0b0708070e030c0a050f0a170709110a020c100e041415060f03070e0d021309030e0105130b030903160506060915030a0204 70
    0x1c0c500a200452082828071640c034a145081d40889910840750b0007800b40610400c204501d01d510007070008002c600d0002102011104169500400d030100900040c1c2000c0c1000710140e04a00b600340a01c0068540f0020403414008240e9240c40c403c01230b54010000c420100401d00f000c1003241510030f4001d003000d031101d8441540820240e840100f001c400d60100781d0410040500c4d200d1210038810241049151070704484000e5500c02034510b85600591070074a0010303040b4490703031524410703010082080c002c60340840200200084162107150312040130140f410140d2a00c2e6040765800348a0111007402c60340c40078416901e4411440c245604096500d01e068010307550000007124504001000068804260a00030846617000203c20305003c03080203000148400e06500b501111684880680d683d1344052405046000e20b070b1142c0002912007403007400f048004604c0070321544050722000c840f82d40342181f849a20005180c0d040d0540c22000c191009400c03d60051a4071040b05d103000c8600051 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 919924172 1250 919922922 919922953
    0x90d0609080a0503040219151808010204120c051f0c050a020a080303040b01050102010501060c080f040b030903072f1e10050a030506030c09070516021005040e250e03 73
    0x101c2c610360b000098000041200314036201c8007489000c6c2580189144841c200528810070800d4180414180041e9a55008500002d040ca00005c0c208410080d51255614280d807174101e07402040072254040b4100c800705c3c06081c20912599031106041c007141c00c8244072402a240e582418400361094010140508003684070466100020b2044200650792442d01c1d00342484440d0b410f800c80c904590518004000ca44e41c407130062020b554005a14642e00c110441f804a000c1c0300b1644070f1070743c9000110070094000c00102c007400c011406803c5c1e64100c24400c2002c503031a00e17098140119a0100c0c4400c1e1085030408002024812400300c44100340c0c2004940010115400101c10038005540040d1180820360b140c058950800d5082d001803000d01c0196002a001400c014190320030404046090030592451020900341141c002c0c10f00d186c12080204000c10a070f01c03a002e0008400d00c98808508c8100c1d041564111880c205407404440c4458000d0844005065104030380d0705208124030380d41a400c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 919925422 1250 919924172 919924177
    0x160b0403320406110a06051005030609030424020f0106031b080111031501091503050f07080402010e040b0a050406090b090702030f09211c0201050a060b090d060908 72
    0x5000340c0325910304024a41851600c00e9820801801d030244103454024204014000d03141940c0c603a0804841d50302d01c202500c0e10300310999070003030140b900f000d0030b020301e02600034030b1401914402d43c140c1c0c0380d568509414564910581c81000098075117809655414116015001c078619002d00c107030b8040c403019050a500f0b4440a80003590080040d21000e02003811004d0080c0c01003050b9070003881091840307100007886020007800742c8511403071500c0c03850050303100b5600780e8054950800c8a1081d0300e0840300c01002042c0807900d10002100510128030307043c1c040d407505445607074165262980840e2100900010344480011240c12041c1d001000c94203982d14000c0c1005440c144500066054400003005050880900707000c0070354100700b203c1d80d032284545e41200c490034000d1b95001c00c3d45d010101fa404c0300c141001c6d55020103005071746802c60404003241c0e170b5a41c0840740703600070b0005440e0b850300c42040710307031034420007107002801c00070184107090081040e00510b020741c0c40017030500080e0721400080e5 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 919926672 1250 919925422 919925431
    0x50703020f060705010c020d120b06030c030604090210020129030c10030e0a060902030c040605130203040c170102090906010513090509010e0a0b1b03040b010909050c0a0f170d08010605160b 83
    0x40c0c0200360030141032540003278007102c004404501488110100350108000741310141a11203100c0300000000c4942e196500000c2d20154003034040803480041450090080c000402e0055403480701c206540301e0205080d0059030b082c00000c0260691078250410400c0503408030341004140340c1c0b182607107500c4a50610882081d50700402c00402c03002010300c1051b04001a200d00d00c2c1c41a45009014001a01d450b40c0120070030b0340d00d034001039481e225800c0140c91942180d000905950544019038141c005c1034018150200d001d46101c40a82ca90300e0042d04c0c0b1b8000c800410003416040f940401c845039254201c650018400000003e000040c820794504180f03100e0000d031003000b2880280441829409001c500307440c1079243c81800e500300390380c96201113074040c0b04002c0055152038104003882400e0007031114560780105207400c650340e261400d0144a0380c503c10709175420280d50b00c1c01c0001c6404948031360010342c2590340c11b015a00b0080292071541003d803100845a07144265140094015202d46005 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 919927922 1250 919926672 919926677
    0x50105090a0201080a060e060d081201030c090f050712090f0203070308041806030809040c0210050901151212032003010b19051204030815190503010c02060103050703020f060705010c 80
    0xc961281c0005413403403030003030402c1c0b114901d4250200484000503801d1030300a142251150850303819410541814003c0c64222081d108000c8000820400700702c00040441d01d030402d041c44401484483c0104440003111100b0208040320b40c07100a1031280e910250810384103900c0d00e89000c2c129001300b440c1c01c0b010b82040716622000503081c82640c80080c01d900705e80c8100c0200b8000c850440c0d44240460203140e01280c0919150a0f00010300c9000b404526201035903c40b04009618101c0c0c3c4582c081c2000c00c05084038841c10080100e140002d10503080c1840d13400003003080e0000c00300344085004286031000b60866402900d4283c0500110000940c020070203000555124002008140f926112100030603052100401c41510b1000500300000e80c4243c05042500850b81c616554015000e10034146961142d0030018018402160f8071035030007a40c100750700070003801c611500c2c142c2c2c0da01006e000143c460b504c409010001031a00380b0030315400c51405000b0f0b6090290039601e2509480c0354005032000b = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 919929172 1250 919927922 919927933
    0x1e040806100f18020a120504120e0402160206090f12060126060403030b210303040c0f0b1801170f0405160b04050d0c05030609240705220305010509 65
    0x300800503802003024110010904141c9441d011040000c50100c1210041d82074011a0015110380038143c0300c0107001c606c1400b40510300d41031629100001003c085940070a00400024841d42858401d43c1c482000d141408190f8040640130840c0d40d421100d501544401c440c09c01501589540c0007419402c0c04120003884e40e541070642c010144c40b400200c0ca2817190002031203007482580021130680107a090f00f0001280d40c1d000f00460741003490401103940c0218a00810060900004021403040c2d00a0814401464482020490b90922882418040c8105000710140ca89050704540c282c01d0050524415442d40d030380104030ba96404031030303c1200702c100e182080301703104040c04485c50380407000900ea80380600341080461180224045d46001d0349041029000304900302c01014040c26009040b20301519000da925a91103508900c0c0e003c00c01116100f0b0920105020b0070391b800b40340e20340c880608140c80500408107510020b0008007101d4071810002001c24403e101d9540149030a0000c0c00 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 919930422 1250 919929172 919929181
    0x4090f0906230601051207180312050426121620010e040e100c0203070c0b03190b0315220302061b04050f092508011703030f010303051e040806 63
    0x119800c100a0500b07040c801e00b00050a00401100262a0b004940313081841d03081030746034040f238800d000a80000745aa008115107201036a080700240c012950100c01703da00c170026841e801e0000203a8810b228500b6880421598080c205600180c5102a40c40c9440305031031806480300c03100324440c00c1c4030b00056002c6400000517944d000504e01c804100980d028031144c0200011280d6506840001c4c90141d80d0742e9480060141c030034800c0b00c0c203a81c0c102040300c8500f0384503101e519180d401a0b844a400303252610a0311400c400500404c4d0804c1001005007440f240c9800c042c2d14000c90082245c040080c5003402c0300c486002003440c0c0202c490103035000306214540903000840703612484030b02001010082c0420003a5540304811400c81400c29503800da40d83c2c0307a0040c0450680804903110200d6a558030160726141d130b10000d42c81c12901012351589034100840c034450340301d00c0240e9001c581c0c0ca10850060000c603008200805600303a00c0ca13080e103100140001c109140307822507008451079810090a10 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 919931672 1250 919930422 919930481
    0x5120409060513020a17090c0909030a03050919080d2304030306141c0503091806030c010c03022e0e1f0608071a2b05070206060604090f0906 62
    0x3c0382030100c18004514007105283c01811081c0600c9098981201c5200050000082170010002c00c0c280074044030101e0600204141d1a03401c4995240d00207803800d000104460000580140900c030300e040c180c0385071410303902c070003085601c104000c94089882d0301030035407000e103d80480001c43c124241440041d041c1440c004059a030298004812454425105400e079929400c05000201c0e4081400442699516205095009501c5c490768003128070030a1041d1603a4800b4401e10901081742500d480000a800658840b0b00400c0050010f84c03000c0b00c00b0001210718140d0015441040364034260000540c1114010b40b076600c95031500c039401c58000740145510007140c01030341201c941414456035050400c482e640e4509481409074400d181e021950001d1010800c88060700c6445c0d852516800000404112404a21703400b6039880d4940f4000a100e0b40c800b080c1e1b540180e800800702490907180502444c050030400c80885202941c074880540010300030b100300004021a108100046001076a00 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 919932922 1250 919931672 919931689
    0x12050109050c0a0e0d021f020d0810030318050405090c030f0304050f011202040504050c030f0a0b10050d020f040f08150103020d080f1c020d0f09050a0f051204090605 73
    0x1203015281040e09001012244406450346900b003490f2010112540e003001a244060490019400c0b00007204001c000c01483d1207032455003551602201e0348036218010480d0f00201c2120b1200100b00707003103000e00029209040c60941340c0003c101d0141d210352103500180854202303417200041503204110741d05042c203051101c0e8201110200196085c00d2400c0c0c0440d41d03034022050041d040010441c1c80c0054040b0740d034181e4000d0a0040e10030002481c00002220441d4400d03034060001e112148000b80308001d15000d454020388020b070000c42c0c00d03a01c0500c1900c1d60b8100030001c402e040d80900c03050b10001d600d40098001005040c105400e072070b1030100400d044c100244000070000b0b15200c010f1002da00c0d0714041c2c140e8541e12904032513072205140c040442501614410300300000c8800111450f2480c50b0700a000b40d03810f820401c000080b0126182d504176419514018404c0e00048000b001242d5100e0650036a030b402a81694040800f15203440341c43d911981000705071f40e5581c002030209061031000d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 919934172 1250 919932922 919932929
    0x11120c0f12070618060e070e13020d120311070c1502070f0e040f02030a061505030102090a05060a021501030f031403250504050301020703050d0b030607080a0b031c120501 75
    0x191850707070001c5060450070710807110301a2450740c440c440080d00402030180c522885030440c40070070200a0611300039840e41c1e001c1c807032907044003a180e011650b201c6c8040f03111f0314010350040011507110019510320342d500d00c80b0101d140a165a40e10f4904480e42c1c034000900d12244226080392a15091106118003040c00181240840d4401c10090014003000c46500007580c0d84110729074020b07034543c41d140342c00e02c0c00c400c070080d01801581c1110040285035006180054810341300c01600703d850f041418200c2c041c0075602c0d9072003894480704009a0038280c005002c1440c1c184159180310b1001d0352000e801050a0313008550b00d070620180c1c80c00b4140c0c4440034002c0411628103640c55410000c51012a0481e00800c030b440c02105c15141520503801402210020040030340250345800b134904000c0d04503017050b1071845405051507451705541c6004540c1c18400c42e01c035140e889030b03074954103015801041210348040c0c041c460000c80000c148074201d070840e0040c5284e50ae030001ca584458144041d039074180d0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 919935422 1250 919934172 919934203
    0xa030e0c21190f0f05100e010e0105090f120d0603061b02190b010b0a090e0723090102070e15030714010e090c032a03040503070317010509011511120c 66
    0xc2503031000400c0382c1180d6003c540c01c90300741c1c0110076460400b1400d01881c2030b81c004110745458890300310104c06400680801078104000c115035035481d40826203c0250702440f1245400080314000034858546c090840c00744040340005812f6180d9980c0d00444191590000d81241030702d0711450701583c1040401005204828138025100f50b60f5206040984103000304886c541d800f01d904202c440c46620342d20001d00d002141d40029003050300002c3c1207401d10b54401c031002c80e02a00e5840d070b0142842d0488103099010790061060034030b85803002004400c050b00400301844030300d500c1003040e902001020017801c0b190b0ac91082e11611a40090000006a0240760043c010740f010026403a10344010b60758429122003081003844803d000350550070b011041c1d210301c01d420100a020901c01c00101070901644a0f88403140e81c41400d101e1154002001d00c40c09034420f08107001031240d007803001c18801c1901070604084e4140b02400000a00f80022451500034020000c03c031080d41003401c00207040c004182e01c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 919936672 1250 919935422 919935463
    0x5040b07080c0d2c270601140f0313020109030f030503061201051b0c0c04050c0903160b040911190e0f0a06080f061507060c090f08030a030e0c21 64
    0x40d040804099202c40c03213441d140304050810310843e10b95400b650841c910030903401c050003c5c040136001070250159203031741c005004200841e1044d10b1070000c94451403509003c0e20b0465858400024100b036030004206d04009101c0000000507481c011180d88440c4070740c03140c1e602d81c034046084c0003e02d002c40b1003201d22a8101002e012942403034031300140341180d04041c1e0741c0e5100d401c00d058502c1c040143c51707000d801a00d4213081007021844000500301140c0110141c034910450800d46201c5000c050040e414008410002048201e00a6102014000010b03100704d00305405104810001c08014410310301180b085d80d14003080d842d1140c1045001c0382c0850343c000d15030303040070001000f096000303190012250f92400810700b103951303611011040c3c01842004d15641c26041c60458040d052007054100490b0140001080802d20040c4000a50790042c000b5401c204c45e40004502801010811040324003991049040c1038890981280070310078600240c0c1c203c00304a0909501d404d032000c0320500c0b000f80303c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 919937922 1250 919936672 919936697
    0x10516110910290702040c03111308060705121f180c140c0c060d0b1c05010509010501060f0c031707020f070503030703140c030d090b010303112b05040b07080c0d 71
    0x1003c042d5140660140c5d40060074410071841540201426015110f4184000c20b50700260141c84204005844604003a11060740b10820b0544440c010100540303100c1d100c40001071407040c19507041200300035166540401280d41c803016448100740c1c0180c50002d0580b0b44034404031082d00300050841c1a4890002c440c58060913210141e102c046021000380720700000120840351000381d0304201c82c008402084e1459040385c540c00320661003140c1000320703465420040000c48a01e01031107424104c40f61510b4201750800d00d05022154000104800c406004002c0611440110343c0d17220148100c4003500201030702c100d1f50078070529041131607000a01c80c0d4401c100d41c6000960150000c0300000102c941c0c2d540740c03244122114254002e8003a4402800d00d42100c110030f00601e059454103c81c02501c2d0080041640c16a00e0303242e640c0b40e001d100c070650400703404c10b10070075000c09040035006440c503249003002c0c0c843e40c03003165690100301d098542e460301003000c0182d030200780850200a2080d04007008403084 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 919939172 1250 919937922 919937999
    0x140d030806010e01051b0303100b0705070e070203161103010e01060b0a05250b040b13020d02130b0306010e010609081c080703060306050420040b010516110910 70
    0x6008019034100160f008031040164012403d486800a403500040841102840020b0342c942007115800c814006c151800038207080500b0847d5090780d0002c020f40b000c98201040c01c0a01c08014001c942184000c219400402010550801c04644030303000b40a02089000e00305400d6410390604861140d240840411644503040b04484000c2d60070300f0442c5c3c48241a0784c585007a900c0b49a07041081c0106018944100b100d030700d00292045100d07421515443e1074803106503a0307610b030311038009400602130003c0071b001d89003080034410400028800810881104008281400d10a902400380041008010701906400c0544180505004c8c0c004010007414646130441c040c070000000c10a104119000c13891fa244250440c20240d50881014001c42c1460300c0d20210307030083c08000340004654011441c900b448c2034020960b100005030b689074104140c1400031a2044240b9104031071015200b0031a4420361284803030b0612034a0b1600400051078034003801d440d9803205034030688442040e40c0b0768040c01c181 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 919940422 1250 919939172 919939187
    0x102030c190203011e090c060c150b0301020d0f092010050f0904020a050c0d080712110c0d0909050601020304060903060e0a1b090b12070e07030f0213140d03 69
    0x500900454288041c0e002182c010703c800c0b4400c5103060808071090b61105160781000105510a0507042071072039803124125180c0d030320058000c1501e01c00c20b80204210714590007a15001c80300a00051600d503007003e058084810442140070026141c6401100340000700c8110a0000c103003c110721004c01c1054001030f03a019103031000710180440851a41403840b995010760f4000304003d04119510214260003814640102c604483c452048078803075201c46100f81d0300e41c0d0003402c4c01c0e1140a8428800c2d040280a04014410f00b440701e074003031001c1100010b00f08030071055285203803100607040e403c003c1c5480a03a00010462030642d842044208100f40e8045e41550441b9089480040c2c00780d0f00100c0a800d144032002c01030001d80d0850712084e158901744c020881111007034003080060541ca030040c88a0502b01c0c50090519030032404042060380c0e0719804e220340c48040c5103400101c003041000300d00201d800601b04406404103080d001d2000b8041038480c014140822184000e4061003541c009100c0e1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 919941672 1250 919940422 919940443
    0x60303030405030f0f070606030b010e0a0c021e0a02031002040f060305130308090a0b180714030a031112040909030806030f060103110a0b03011e17190809030118110102030c 76
    0x2c001c0050401030404101c000c0c2d0744981da000c60302340f05466490400d038601c08020b018400c1495004408602c54011511811041d903044d500070701200c0c0d0340e2480802a10a03054400501d5019a001c0840142d405000c8406c400a54800043e1039900b80a20021142061342250092501d00024031280000c1c000c0360b0f100b02641880e01e040165100314803d82004e040c0400142080c1801c0140041c081c079202c403030b002c604001d000b10741e1025a03c87c0240852a010451a509a080880c40030b010a03c2000c0042c1c00c00350789000c6942406c4412101000b50340103a0021001658918107501010342c015002e94002400f20000c03c8556407178040c4640b20740040c0320040001c000c44050820700c0c0c54280f104801000450030070341c0c8941c2d4402e1080f180d00131492004210800c00100070400818511441da09858004024000c0c00c1c0140b01c00000f29041c1c0328181c4801e1400c1c000d84040d40d400740100c00081c60240b00031038103034945103000d241004061b0031260540d0000d004102c0700d64000a184c8900e03 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 919942922 1250 919941672 919941697
    0x606110703030c0209180a030e031b1302130e010f0305120315040b040605060a0504080d0801030507060e19080a0302101107080702041407231e070624090506030303040503 75
    0x540c1b100001004c01c03039030001c0c5003010b0707004404c1444d00785500600900c030f000340d064040d1034400309030350140c11215012008442d405104950f202d40c0710f5185601801d0005121800b1901454030350035079074521042641305040c440c2d0035031014800c11900b4488074101e491007134409401d60900740300c00002061984480c0340580c0c0c3c2d5400094003507441707030841c000403c00600482ea80b40440c14008002c1e070700c90300840c041442040340300251548034130446412030740c015019080040c2800d40881d0442c6070512070340d5004003841c0c0c0751500078814965101c01000042d0041c4020704c2e107403a001e41894900202078518074507041c0c0314003d1926541c11100a5039020003c9503565290b44000307001010050100ca0180e40c400c42008110354002ca18004140210240000f1030594021124058491758010f00700080c01c04008041d000c03280c0025040452041c5c80108003070310412280550322606e0f105214040c135000204101044c454814030b030f00410107401031803661910b078070398a51306c1c800c0107001500d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 919944172 1250 919942922 919942939
    0x21020606101b06050c0714030c150a0608060703091a160e01120204080d1d1807021c0e0109060203070b060105030709090609050a0e0a17030a0213090606110703030c02 73
    0x1080c6000c08801c440551043e02001641007080c082c050681015030f0403940d04000c1c4c0345040e10501c5c000300b5216035001007070040182c50051550080c5205000d000c4c20019916201e01240000c41405030a1140c1030740c1e500054400c0603428190244800c5011219440100009100c3c9841c2d0300c802240b0382c1e00c12420705040030b05034500102c4100d401412442400b51000c21301090702840401e401d00000c1c0d1940d15000180d604960100950070500350701ca81c401d0400160300c100b24081140b03181d101a5900644030480b4420b580341c1c102040c1d00c0301c40800030396440f0306143e10b90307007142181c0081e2400384011401d04000d275890852400c1c0c09400c0f1418001c012000511661160320650058856148207100199407144480060001034610309881400d200ca003411600001412410058004080c00526a904c19004289070f1015010901440d0200007030a4a00440c0070100010905c111000502500d000001010031080c40c0c600c00040d00446400c0000c00c2c2c2c002c0103a61995011501c558 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 919945422 1250 919944172 919944197
    0x20c0610150905150405040624090b1206010905031005060111160b2d0c010501210b0c0912070f0b0309030406120209040504050102070303050603070b0a08060a050a032102060610 78
    0x40c000d0003179902c2154458107102020a100303001c4801040003908081c000488500544000c2da0030164a00550b000b2601c03d01c0441c0b852448203681a401640604018441d40d8884003c41c0c140044020b000600303685030300501081e540c2c0100040d4a120159024245025450300c40c00d0403074005110301110100b01080300010413003403031090440b1684a01b00011311806c0c0c007000c5000780e045604a45060352070701e000000c01144001f691910504c0c4070b000352040d004103070745085840b0400343c52034251080501c4a01081c1e00c0c2d250301c0a85441d108c8009011443c0742031036103000d01800350848003000d601401800740d501400003c1d40c0c240e590303d05000c02001d0100592a0082c0a05808139034018206800e100034494198010a0440d0213607a00303109a694841c14555925024440c03424508410884020311600c949003440d005800200f107003441e181c5e81c00c0024840d5440c1d403c02c0c1d49030020031280714070720040c112481a006441c2d00140240b4030b00075000481d42d502c240d00807400e000b101807240 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 919946672 1250 919945422 919945459
    0x10803070201080618040c06110a030c0201030507020709050a02070b1b03011523091014030a0c0e131b1106060906190b1b030c0303010b070f06020c0610150905 70
    0x810074890a40d8010070f451074141840d070300d51100c600c88c070030125114191994030282e000c42c07445401e07501916461071201c120b03030044004002c0185404118040c0500209500d03480c6e01800d401040303c2c010168072098136080074003c45c00040d00c1c10344030000d005504100000e400d000d40e0b0440e01c141c0c1d0145000d0b000d240e011368440b07000010b4000c4801a9250604d40c021004003d400152410344003103102d02c80c05032065407024454458450008401d0001a0105455401400455920b458440c071a10001d501092039000062410140341751102070102c4c08909001811100c0001464080581503d0381d2240d0380322032018110a001d1241038000440f1038a403850f903001982d480e4200342c1a25070396031a001c0d03441d0300300f9100c8280140a8590b03200d1505d030000190b510b00603c2002541c07840e480d103898a50280d000600450320b04088800000200e082d40c809001d0b2000d046020b8200d81c40d0030100560f0541040d04002c00302c060003200058000d42c003a0b403207402e032134094400c10640c1c40c110004 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 919947922 1250 919946672 919946689
    0x60e13050f190b01080c011e050c01020d270f170c060403090305060705120f090124050906090c03070c082a01060803192109030512060103050108030702010806 70
    0x1008852141c0c60000e20160a042c000300340490140028444a0b42c0b15050300741c452902022850000d0029421504504040303121544245040d061103454181c0e410390060a9811001e100c400c200e9031a00c481d01100210050101c240d0100c2d40e60b1110600583e4031184542000c3e0b40142c4450800e070f07130a01d803001c1d000c400c8808038160356081b600c480c81d00c0d2030000c02e0862940412542030281c0000305a1081c000c1c0240c46003c1c1c9194031381ca1107a03603150b101444030700e03005111000564031070f0310741c2020404070105031190506c0080b03080e101504002c01d10a4030319018103014000c1b4401820019049150b60550742c000000d460524003101e1142003410550203909554108881d11490032030414903041281c44040702180b000b4823043d9034500f00b107916809005843c106005c200710840402c140700b0004601c10110b001e822546001d005c0c103110048400c0b00c1d80441c00301c0c60005070007021070300491285600c40403d2034140a9503042c00a01512401001d030b009041c400c0080220301550340700c504 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 919949172 1250 919947922 919947943
    0xc030f0a1b110109050312041e0504021209060705070b150d0b0a020912010c080106050705070332011a010e040f0c02031b160608040503120a06050112060e1305 70
    0x44009621003420300c40142c080503680c440c0030500c042c000068500780840c0c0141c9140d04503003001c0c209441d0001d00c0720030682c0008915081e44280710042002e0b0746900c043e0074150034845d00315540389000083c03d407404501034140c80601074148010000113002c05607883d80500c065013101e0451240c41c0c045491141f2035003005014545d20410407101c2600c0d980681824402115403d070500c0701c203c0103031708941803a00c0000c00220030800500c1111b000b8001046101d04c107100b11601070b9580d868a00002501140386c201c019400d102020300c030724410450350507540300300d4000c001c41110900c1d042e4a20407018021414051107070311300945607856904c03808110112407401d02140305101c5000f91a940002040b105208101c03c0c22004410700140341d01002c841010603880b0340d424410241c40d2040001c0041361a407204001c01c0071000a40020140a480d00382004a009800c0030700140400c1104c074a001949071070030030200000b40070303800b80980010030205884031004550070b0282c200840e110 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 919950422 1250 919949172 919949207
    0x60702030a080a020c0108010305061b0d0e0715030c02100e07090905061f0627031a060301230a09060e072903070e012a1a0a020c030f0a 60
    0xd001070a21a40b10014401c0548690960b03d04544850040d110f1000030700010301294840303000606060709100c2d1320300707000d124080e090303042114200c4036a05030340450b6641d0480b50032590301004021540e2010100c000443d007000d000040c01307658000c0d9165506281104100e494103090314048c001405502e020b00381d802d0042c01801c4050a101c0e0341c030741d13041d01d4010142002c83c40544c00e9226101d07000068441c1c6545140001d0803081030441034a0383d03560341c0d002040701c0040c000001000541070940342e1000d003000321211f20704030003018215205120303000e009902d40200000d240002114140e4050707144000040c2c40017281c201140288001c0401ca40540b2407290081110380c0c0e54091100c1002d24006a0340c13001590b044600890b00060783c0d5040030501c61003980d101580a00700503000c0348201000640d200c948101001c0441d0148501543c106600d1030741c0039804d109460407641c1c0044900001d524059008010554920a094100301451000704000b15170794881d5034150341c03078407a85 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 919951672 1250 919950422 919950433
    0x824120d0302040f1502070b07031403010303020604062f0313050111070c27051f170c09010f0320030105070504081c0509060a03020403020d050c01110f100b06070203 73
    0x540980254058044d41c00400000c00c000601050b1018021600d20f40d1a4040c0031b01a28142d40c02196400601049041c040c560300c249a00c00c504001441c001c5001e9170040089003170034100744088070604031800300341d0303e00443c10346880c1d00041400000c0110b03801c805a0303641d51710840c940e00781010400c018819420080b2038003a21032040090042540641c1181c12400d9640d0094080504040000500b61500410754402c08180c2c0c3d00103a44040c1408001c2c80d501c0c0451082c41e00003032540c002c0c1d00140b24888000c03a147c41e00700100940381c4010b66030000d0759410228000c003081d01c039200041c013030b0360035030000124030485040c2c07a0300302400a40288481d00f080003024041e80c205001c5c2c4040c3c0e01c6102c1c0101c440e0380309001d090b10240d2880d1600e61174010b203281400296400003078403005040d000c0100000684402051444007030143d00a4003070602c0b548001080740d02001080360842e44103518940041d9008201044000c5403c003002400780d055001140705d6002d0044040e50501a4 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 919952922 1250 919951672 919951693
    0xc1401030f091a0f090c0d030e0405011e1211090c0d05040b010e07050a081501182c04031407030306080607020d0e0105181324090c082412 61
    0x10310454000100c41040907104070703075508404044e1108200c58020065000e40c40094244c02c02d4110900d45501a1402d40707114501040800c06075002030740807104c0700e070007000700e0554442c501445401510f05e25921703507540d440c0c5440322707201c0080104a40d4030520810000c00d07250040c0904850358040300c2202031020f881c1900f0708490848003485000b008101140004001c1e6100340300712144884581c59800b00c4d51600e041d00a854100401600c0c1844003000c0c0100807687c2d81c41041005202c101c0c0c02e0b01c001091790401a030302c1e45040250709180c0501c8414040042e8001c0c44005d9010150000c4980381c6402d401c044000e0042079112603081e0050340306020b0000da000ca03890054a0b082c0e21040030460050004544c60301c100d800c0584080f0041c0c59640e01132400818421020054010204400385002c0440340380980c60919201a070800c103008208a5520b8018403401c40304a00302281c0e41c1c50300c0f0700b005840000402c203404040c0d661000016699a40910400100b001c0d2002c4400c503450 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 919954172 1250 919952922 919952933
    0x307030e0a111f020d110f120301082e0f380118090f111308191505060109092909010302030312070e06210a0501030c1401030f09 57
    0x42122003401000310001d290b01c00f051072049a4020700f110740c0200306544101004031450140480c6000c1940181c00c070341e406901d41000641b00081e50715180594a5244c103840e54036103191140845141304605402300442e0000501c065624003410601082ca1841062030900800740d0850201401d0500803420b450000c48503243c251625000282001914990b0015a10540101d108403041c040120f001e2007941034035007021004500070940403404031003100c108a01030300302c215041c508002e4558100b0142c40304000001c24103030183c089409071a1180c031401612602000e4107034446803250003180caa0391040102c5401001c40540c20018142102003100340c1c040038201045501c0c1039100d03040301c20314010f041141240d600400071450150035544000a0705401020700042c802d000c610085a03481c0c41e030040200103041d2020044ac00720720302d10085500c002404d020011443c10005000248030b000c500d030191000c8035400900081280e00480140c01c6296240300c100d0304100640c6c0c10400d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 919955422 1250 919954172 919954193
    0x909040305090f0d0c050418051b011d21150709090f05090a0f0203071505040f2102040e0c0a0e06030111070f0209180609100b030d0c080307030e0a 65
    0x11001c541580c004002e50f0100881d103542c401002e014040310400c200304a141c26889000101d400c141c2d6243c001141d903c03160f0600410359802c401d030090411094440e0f40c0c3c04050405003c04820f440c051280091011076a102035009002c12920146240204091402c000302901c004c00c4103000105440d0240d402800226280318889004cc1000e0031000d000141d030049510801130341c07004000040441d1580249000e050b0416a050300805201080070400c000e20203c100d007043c4c95260380e4600d4040c10100c150710f2540321000c4085e00d5203030b26031440c0c041803640512640490740402e100c2003040c402c07030500e10300c0b003041030f8040a411f10000711915001c21652007448114000c00c428240e01c82c504120784a0810020074503149a0341600c01450540715171900b040e50300760580704141201010301d1800009451031145076020003243c64880c89680601e0542c96019006420710f0001d036100030706446d0444000408180020002841c135503c2540071f102c05c0898007045500303101d001c0c2403410162 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 919956672 1250 919955422 919955437
    0xc06090b09070812070203060420030303010b1201300c15020a050d1403010902030a0204030803040f050c0609030a0b0c07060612030f05090a260313170a03050301050d080909040305 79
    0x40c080c1d601d101e41380310124410344005680140103010203981d26a41c50004a8030178120f02d034000c4076200250130a17142000618040d00c0b500c41d1441e038035000040e014940c108168030104405a5030740340101b00402249642d0380340080082c6540741c1c42074914101d0565001c9030000540c8803240b17054050042d0340028046109030081b0159680d4075031101044481002442134007082901c104010400c10350194002d642c445605d120050400ea1207544180159000b520181c5900090640c0b142c00e0003c288521702d07100c002190340b94603140840f40440c0d2200c01000d006402180024001040d0355070200031114400e90250003003003001d40700d40c244141c3d140000000e40000f1440382040030001c1c002c4040303502612000b080740303118501d03042c2c8285901d0710907050721000040c0307014490700042007007024020030007000322954407160600c40323840040703194103030008480d0340480a010b011903003201c1101c6c1500c00544500402d035400c0d00341551944200c969554000c2102010001403550160261002 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 919957922 1250 919956672 919956689
    0x20f100e0109141c05013b060906130f1401020c0d0305010317070f15020301091107020901031e330e070b090a09050405010e0606060c07060c06090b0907 67
    0x1e180d00c4064000100c4000c107161504404da80031004080c0500d21029807825106030004111180e000b501003410b0f00d50080d04040c4520390341224a503e480301843d02d42c1829020300103220514101030207a5a548028164080e0a1204070101080c00042868100000c0c0c2104070b40000c0c9808041e0309000754864280300c0210b01800e049001007074805c2c0030b018100c81c0c02c084c50180c98801d64445152907404030340100d507140d220340c010a0000b5103c03504800040c440d24001a142e600d490100c005880402030040450f1408100e03500050740c03081b2017981565000040041d0048203008004d07401c5400c0c24020700314608051506007c0c0041500b46090403840e10340b10490640e800101e602541c0008400c44402d0700001d00c1031003e90752170800782c41e0080300102a1200c20741e44640341700c101d0b41c05131010344c2c0d180d44032210010944020480c1e1500180141c0300701d40380080c00c80c51107441c2e0a141c0180d80400c003001c0b02d410140102d540040c010a0380005140440f41469003400e980d87d4040d10642c40e0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 919959172 1250 919957922 919957937
    0x1605190303060608010b0306101707020a050105060102031e094b010f080705130303091a030c04060f02031c20130b030414250b04050d0f020f100e01 65
    0x3c00b00c0c0b144d0780b024100e4041004d11030940d00d40f14100903001e403a51600c6010042046140e650718044011254046c2d0540d401600350860942026404e4401c01800c2c681036500410801c0700f24800111040e41111082201e0b503100d04424002030440b000e805c03030070352140c840c03812012070500c171801004135410b4030440b030413281e14a4040881c0c285144184900c0c00700302ca940c44102290f0049405e80e030b01c078955151062400c9203080240f00340c850385400542c00034074484020b0054082c0b103044020100c030301c501d080342140b070128030343d1855110700e004800c00c2055414101540b517001f08155150011080d089151000d101500b050007020360451080c40d1003c40c0010b10700d0310043c0b03800c80d2000103000704212405070a00304000c10303e5001400489524080c80300d41520b450382408205103000322107260590055150040001e41800354010411540c010041041145e42d0100e0041031954015440066284a4000905c0d805003040d40f00d6005541c0220555005901c14540030110b13000340c03a00203 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 919960422 1250 919959172 919959179
    0x2040e190c050f090d05060a150e160c1b030b040b1506030a090809030303070e122e020d0905060601110a051e03040b0c1006090e0a0602160519030306 66
    0x250365400d01001e0116000300107440d5002d016a00410540c4405002800b100a46a9615140c4202203851401d07582d1b840e501c1400c2d5070030f4034060b07000034054101880b0702828101c84c01c441c40444507031a00f007444444010701081081441004042c00b900010403200f866407814022116501110221603500d02e500025602100d044941600c41c80c0203030643d41036070340d040740c403100900c0140030513116403905120b555415541000210b00c00d00341651307020180203030709080c031804240000d0648100d40109901e584000342c00b100d6000f131002c05d200c1072954800c280100600911a00d1418800f10303080800030001e00c08005041c50148100303a850f215079080e42400326031901c0300014000d040745c02440740301c840c3e0607522035101541c00842d0180c0e45096076550401c1d000341d12a4590710583e41001312901d03110412449514000c1900d118180094264800c1003500d401844070010300480d40440c10403d00580400848182c56001d4112211003071544c0c2e00c01042c541c100c008800003400c0c0740010 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 919961672 1250 919960422 919960471
    0x160210020a112101090501020d05010803120406020a0e1f0e0a0305120f19080403081602032b020c1b03010c0507030e010c06061401021c02030a0302070206040902040e 73
    0x10404640c20109140c0151203100400101a205501650740d800c0040e0f01d0318803881c0c1c203108850340c041c0b00e02c0005944071407030701d0040140c40d4160b1010301e080d00b040c40142e0380800c192070141d900c140d012600590701c00714204c00356080c0707035042c44141e0000ca2005084181c00c1044441184448250703c4550341840c00200300726481c06107020061040d000804000c400441071406040c1c00c654040c0d80c24100a6502d4140f000440c000380c1107800109072070140014503820465207a04001c060841c4d04501e1168a03000c0d540348101461086c0303c00405a0704010482e4004501c86240d00688096507a00000444682c0c1d40c04684020658108850340139107140c90140304000c10420141c4513075080006548007512f604030070118035814015050915000500203104600150840801d41809500100c00082c68007c8100707081200c2d6140b138850241c0c07182c00200759000c8285a02d030141e03807101e840c030101d845801103600c80e48005001150126500f500040d00c4d03807241c0301c0201300d2100d014000d0b10f039 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 919962922 1250 919961672 919961683
    0x30605040615060c083a0b030604080414120105070f1b2f09070908010e0708071503061e0317030610052521030b060a03021c0216021002 60
    0x1110081507040c0c20b20000244040c002d820703007150300d2046042890300e4801c2400f10303c624900c610108824032144140d6480d01f4841d86911550550003070207203244c65a00c145443c0f0a07405910305041100985a2041d91039800c0203a48003100402405541005440a060081800b008d60040f8080403c0e9200d2411800020111241c111402c4044c10280c0201c4041254010511100711002041004229112800da0764005c4005543d4410014a400c0c0041d00b1541d0365030058481d50020340c070030009210002207400981c0ca1f0300c0401c00317034080c113000142d000f454243e0060707402e00b0308907626240c4404d841d400c2034210303402809144c111034003600f8111501d1204981d029441300c11841111007141c4141c0140c0f500f040c172914420008413040c00144188001110105c1d0840b0381280440250031000d1011604c00400307003018041d4601280024055018040150080590205004406107001844c2c0004000d541c2821996542054921034121a52000c00d82c02001c00481218a06d440041c6 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 919964028 1106 919962922 919962929
    0x4030503070302070e061e010e130510062303241e040605030a0c0902070c031208160e03030a11010e0316020a2106050402010315030605040615 63
    0x4808038050320046c4140e0140240c1d205d010702079441c8143e20300c261142403c1100140101001091948124940400389181072105000c40000f6000300c03082503442a030303102200310040d00320550480860310044400181c08000003190700c07003508404810403080d01032810f0504001d0300041c8176541030b880d000c24110706403425a20f043c40c05116000003082c00790054100f2060f542c407219949120746c0f0078500e260350001052030402841c421030a01641d445007a0503001125041c0c010121302048410341d25143c8100c60385030801b4002e84040302d407900018000c40c80c242901c0021640501c84040c010035564980c81101c0300c50505101400b55520b515482004421160040041c04d040320f6115803006041c440b001e40081060348044900c1a40108003c1401c0e215403004800030441d2403903001c0c801070500f07808000c1260329001680190301076841880315040707e05809000343d02510 = true := by decide +kernel

theorem cover : BRFrame.Cov 919784172 919964028 := by
  have h0 := BRFrame.cov_init 919784172
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 919784172 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 919784172 ≤ n) (h2 : n < 919964028) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
