-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5400
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:44:50.554565+00:00
-- url     : https://prove2.me/submissions/99835cab-5a3c-42cd-b27f-d6e5b20a49ef

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 971043165 ≤ n < 971223021 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 971044415 1250 971043165 971043173
    0xc052503080c18191203080412020613061503020913050606040e25030804031b062a1b0605180a0b0f030c07020306010303090518060f060a0228 63
    0x18a015000c090868020400c102064200101d0500c104101310380d56814600d508010700a58010b5a100c1090301c5484621a0b00b1705070001c1d0a20712071800f942211206c114009412a12074000301d40160403004407650080106990b90701103c5020001420348101d15203a4000039040070303042321341c5a129128540140200807003404400d400c4601504d080c0100450030008a45502c0384100444414004894904250070441e460000540d001812035590f070740c4030b00b008651052407040d14580d02e1842040021140d10070545003688090301d90f0305001101007591656071440022100750f448a00101e1038414060250b1640f50007801c15480715030782c035440003000241d918562142d4074494203407101c041081c80802c104440d15001301d02c6c51f0b16620380d1080b001c1c5841d400b40b0000030390940304220020080513001a885c1040d5030013181e40c104045121540d410301c00208540103900404405c4041d002810031001038140020306005551001c000207038500c003813281e210030100c0742e00305c003455000601c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 971045665 1250 971044415 971044427
    0x30c03040b100801180212071a070305041203020d021506150d020c060a0518031204080306030a050d030902152704020f03040501060509072619050405010c03051e01090c052503 77
    0x13078200c47e01030424640341042c0c0070b100d01c016112140300c0386800550b400825124a040310301400007960140702c1c0e40d4003410025500c1254051000151140380074444e644c002c15901c0710703c02c200003072107006c1d01e400d003500408858000a000c08101d0303030240180032030f6450604c11075100307482038140001c0c2c0d0714082c000c640e41d14501c000044081e400c2044840701c0d10a2907140e84e94860b400c8a81d9071354984441000c42e04c0c2c400c0f0400081c0ca540110304c000c1c507080d681030b04803a64060080344c6000c0e48444400c0b05894602c07070100c0950b80c0c182c1c14a50000001c00c500c00400308400002c0005041c600207652030101c5a00840b0b00b12540e941d14601402945411110560010001c1c54200030015100003483d0a21400d01d0501c10a00c240708000782503241c8021450084008043e4240b000d8105407030300b40d000e00000c48007040424140b10001d0000c1c56115500d0301c50f100d090300c00b80f40b903901c0c00d520311005062113503840c020070a00f0040000200304038904010320b02d050180c440c41c1d000786c0d41130041c42c03 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 971046915 1250 971045665 971045689
    0xb1b0d090311190b070311010c09080a06110d1e1b050307140910080702061b0d0504080d020f070312020a08010312020717011a0402030c03040b1008011802 68
    0x1030089544052001c140a1649840540d409a0b1165003a0400a41c2d0035043c60702c41e0f1200b20194400580641010b60090b141183c9a000300003c0c050044075840944110001d405140080d5022241110209015030440328007003403611406441c000203102024140d905170125494490006000950302c900207100b0206041001c8460b41016500184014000d200282c132540411154060519170305a62004075500300c4001003220055014203000a0440e0200b11900c9001d40202c50004516101a80706646410401000f09243c10002ea10703010080c000904146c5900c00284404c2c100c0940d03a100601a0109405905031106100c0c503004113811158048135040c140148121102c07550003c52043c152548a203500f03400f035448881c01c034600384455001186211421481900070708040d8001840b000700c0d45007000c950040802404141c3c4030039105c41582a00c00c10004020600440b000c03604450840c60504c0b800340e032100e01c00d00303444001c02d41130201c3d58814190301c11481c10b4890241 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 971048165 1250 971046915 971046917
    0x2c09010b1b0d09050603070203190f08100e07050c0a0501151a07020303030109050c0d0f052d06011803050304300c03080315041104030204050f130f06060b1b0d 70
    0xb549101214018210416849958026940440804c5206009001ba179281204646608046191110006000c0c115580600d4003040b01100860618081c08065009031200d220381c260041e2240d000855683d0f012581e00c003030034007440e0800310000c5d50a001e1300a148100c3d54000c6403181c01c142401030707501503100031803880801c10881c8400580b800310a40e0f044030b21f1300b000011207644da00d0543d0181d100703611912512500e0103616280c01015640228040d200c40c00e00d0b805c01008206040c4003100b0301801c008241001e44002805075031003940141080d400d4071210307101e030a96942c0e51030b140d500590130050780c40520710182e05840d0340000c00c40302044901178446003080801d80750074540c01c46901028050801c000700151000640742d0351001c030301e44050801c010340a010300c1070400a402034042240702d5400c000c00f00d0f00c4003440781c15160207103100114524503180a0b035110011a004044d04690b100d4a031000003818139078540c00790150740101e008010514041500083c00c00e035903009910 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 971049415 1250 971048165 971048173
    0x8151c210e031c08130218011a07051009110a090b09060f1c03110a110906010c0201080112020a231002010507120f020904020403140601050f012c09010b1b 68
    0xc1881d0f0301c2140d414681412508000c0415210454156110f40035480b0194000d04505d44603400030791110865070407603030700e0341420905140d80032300d10f520352103092800f03041c41d030103070341c5068111115070311403603807d03100d4600b00041107014000301d20854055404418900c0d52000e01181505002a00b5a4403010454110b40b00650890000320a030790741c840208050403661034203c0030940110000c911101d85039003201d00c280b8480c038046044008846481c0e02a00555020884650103042c280f0750090381611904400d82c20a69607420000640006a13407190a0003400110340202811101c02801440d261512114620081c00381024000d1041000c41e17241c40704005101e58419205c100e150758401011030080e50070b400c160040e01502041030b9104d880001d00204100004200030100a20300c0103484e100ea07aa0810401e1a00010b20101d002c1401ca69454601c7c22418160003014401d2400d240c10844103040454165603090300302c11861040043c00d0444441003285820801141344c000b0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 971050665 1250 971049415 971049433
    0x7080607050d1b174611090922030305040b181c050f16020a0906140927060106030f02031306090503160c140108151c210e03 55
    0xb05441e5241c2d8540d030700202070b500402c100c0301d078002c104100d100039008035035131703541d52100d210355510000c04002060b00c2e079441400140c2c0c103507801100c1d010030741100d60314100500700090111280005220040c02049205500390b00b500030030212491a000b95000203592400b45010580e603030019100c0112110309015012940e0030000b004191002c5410014004013945642500c8a0048000220702a0000f0510300000c80c81051880038181c02250202c068aa880941c3e00c1100c8103401041403c40154000c45401c1c00d08640540c3c000001d2081403082d0303503124001d880c98521151071401e040d005440100803140d4180540703040103130000400c5180d41003410034074000c0e4810300401801c1c00e844220b0b400502100b070043e0b51006280c0c4039101001049450000c8420445000301e901e03d444886800782194030070701444d0b200341d0b04140ca03400b0b2a009042009018a10084401030b00c0740c0608922000a21140c1c0310020307001c608040c00d80c0d140301550701614194603c0c880d58080c2d0f12600c01 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 971051915 1250 971050665 971050667
    0x27040201090503031204021e090a02130b040e07031805030a081f0608130317100914040210142b0c0e06030f071202030c090a0504060b0403021207080607050d1b 70
    0x3140c21650440723204661400c0b41d145880f03100d0a80d40e00030342c000081e10401011051039001400320b145c4580c40d010f5404d45417921602d01c1d00443c0110000315040400148030107000f0384c021101c40b0101c10b01d051145a15a80d00b5103150f004c560228000365035442884504140b08251f070003c21074070310714002d8145c1000001850700400401082000701e50303003184010b160148080980400701c0c00c01422107803030030050565548803103200e020480e500d01040400500445055a4007450340148640c0206107269011500394525245490a1140070403800300c0c41a041400d0111020f484000107441d00d503103407001400c4900d0f0804400c00d000404c051101255201001c43e40d001300c000300700441ca42ca0322003044610010b4080b07540784180c400070030700c9011544180a846558005c54255040940303450a0109640c200e00c560300d5200c0e02440244014544444900000400d040c111340b01d071941d81604a00d07012040c1c404002082e00010480000e00950094403070041000303201c54034000d08540 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 971053165 1250 971051915 971051947
    0x702190510031e0c20070b0d0c0e031f060503030f030f0712060303050705060a0e0d12240503060c120a0e01090f200306040c030f022704020109050303 66
    0xd901d01c2019503400000200001681032140400f400c00d104000314680e010026220f040500e07150b00e110700308006842c84100c00050840280c9259582090811031042c40ea02e024100c10342c1c000082c000c12010441903900e0410451103411405000c000b20403860040f08802c6030361907045540a50070411401c0d12814100044980001c0301326803142c2180da40941c02c844091800c3d81d00401d0034209040081419840b00141c075105000e403003651020f440f081d450004071000da0380b10245c26081030780000d411600401803030b010100184000b1650490b1200c900c00c04150803c2c000600018041c5c080c040c82c142048007943c420680203007070b4506020350028451040000f070896260700c1d12444400410b803800e4221040455000ca21f85c0d010310150b2400303042010007800c882c0e440b0000c683d03101219260001c1e0540c050b9802c12000f0020790305580302c0050104150720240e802c0111485a0514114007501c4000c600e20b05d08851009802c0c03d100041103582c0340c5d448240b1036030080c4a8090200c42c2c0c16 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 971054415 1250 971053165 971053189
    0xf17010e0601050c010501230607021e0103020d0e01020c0f0601080a150902090a090203010b040b1c1b0626071707141b060721020a091a07021905 64
    0x180e10019640d64910040783c1d80d00c9031a00c1c3e642d0315403c01c00002007004802d0390f41603c05c180c528290003d024090f0600c03a96025010019510000c1115282d400700804680010100c02c189409460822104900030a0b6108003580b18000c1c0c1d40080c079107090761818490030100909981c00b034051945820744003030b650010000b0241501c926101d80182d071f88220740c0549030b440d902070401c1140b464100c1501004040f8210180d000394205160b80c008d510f07180c072581c2071144005103400c0f80301b1414040000040c0d9060000c40707550300f40c4190a01d2118000c0015402800203a0318850081480d008000d030211040f10345600100c0b900c001c1c051169041484480c000c40034510340e4100f980c42100441f600030000c200c6441d614800940020480f03510103c29560284443c2141d0326501c64290445000c0079001039900712800d0000d02e0404655240c000b030401405503d004510651660701181c84034081c4801c8140541d0006810720450074030319680055440f0803ca100040e61500000c60210300440d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 971055665 1250 971054415 971054429
    0x160e0f0106050d0f021b10061e06031805070305060109060902090f0111012c15011a0a1701061713030e010c0507090e030702031b010210050c0d0510060f1701 69
    0x500515602191950503100c881b4030b4460000c20070031440403101d40712246404107116440c100715003c070309007410306032141441800d003400d1040b5501d400b108400900c044000d2900d05040000c1c1d20000c40c00401110001d580550040c00640d450000110308441c0f643d4018080d060041c001c0044c15522403181c4031ba01c0c01d003800d201005841d1545580c1c010501c0346100702a603500e8038601c00132507079650f6000c99410400c00440700d24110381617809500c02001d1084211408540c1050f8481d114040050032020341c450a04900301c0d10710790041c100d0700909030000d4000403032008450440709005811a9046542102844031040303894900070b100747d10006800e814003210920031800c0103000c104400c01050946030400c05186041401922a0300c8000c059100e4490030000d00c003102d02c1500181006001600207000c0c01c1400725108000d0300009008040705030090049103052001c5000f2103105488203e124443d541c00c00e00082c041d08590540c80c8104142d4080b031582c0c80d00c203002414195084 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 971056915 1250 971055665 971055671
    0x1005030604140f0f0c010e010203070c03020105091207092c0a03031512260414091504090f0303150f171204140102060106030212070806040e160e0f0106050d 69
    0x2e01d8060b0310784240003600c0ca90b14490b9980700d00c04894081503032100340d1000d0f81e46000d40e030f024000490350b81c0607254000c1c002d203030b000b082000151300900007054207800103040080e07441c5520205a052000c1070740035901998583c0c03000791520032001078251820240304803041c2804a510481c994410380148018103141d940e108900000071840b88220081c4003000d50600c140686117408030001c2403c01c1882846c4c03051111507051158a04282c90a482c580c00e41c245403100103c00708010300402810740ea00d88840c020003c9031507256400340e081418011803211b043c500d400e2a008003102d010019a01080d0b1040200388803075000c0e80c40c1e83d422226040c0381c02030304881900702d0905040340c808940064080004001135108809440d10050181c01d8098446680c1d071200e06070203900c5000420300c02103a60b880014200c0340150700203504540090070024003402188120781ca0180d0006c042e09a004505500300041c04c01c21185a51102d044821039509514140000d446402051030814449803 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 971058165 1250 971056915 971056943
    0xa08030a120e01060b04150306081b0a0e0f04110402040b2d0309070e4002130b0f030a020906100c1b14040944030f1005030604 56
    0x19a04045180000b1000030404959a2000454035501c603118103440c0290200c0c1c41a09a80a07106010846040a005d0300320282d07007613024034500420492240c2d10001d00c80d00455a0701d0040c2c806445941c1618001615040c50304100b001c40e8104010b291040d401000248902e071100002c0e200002d20007415400e00d18000010076071940131111a2418441c00070041100a584c0040c0c84000c4442c01a40c0782040c6e12441002d120600200c1c400c0110481300d905c6118201d0104000da017200406e558800101c13002c103034005070a80c9403140001c0101030700c032007500c1020700c0c18111400881c031044009004801c20355011450b001d8000340403600c118003076002c029005003c5c14084814542c002c02d10302c48110001e0241e07c04403071034007400d46220328090104405007000c1c81030850392034000c004a41c6050b01500c845468031505130102b81920110340030440340592070307030448448030913010720b040d141d151002c00c603054014014006455088566010042501d0102d560b98100c2d030403078044480741c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 971059415 1250 971058165 971058197
    0x91409100e03120705070b01060305060a0b0a12061701060503070e06040513080304080403030e09100e060406030510020304050d08042027070806010302040305100f0b1203180a08030a 80
    0x1020f141e9002c50441c00e2801085102c03070b4458003e16820b440340c088a049a43c03200000c60485a084542640203200c195040c09a45e644a024010b10b0500b4544500111808820390081c1e4505034131a030010341e19a1031000060a0030f002e40806020190700600c14245454150100c100d03010b445540a2a66200820480c44004145454890300020305664030708051030116410340c803e100950004a800002c5000d80c608204201c1c0550380b84501c5840407820140d00c0505940003605050740f0569a01001001602c14005004052104d1200503106d2410707040442c181501e410134007081207050070070080001c1041e0002c026013100d98510300c0c158940500820307201c0d0070301505c03006403103d10040891212104481c030b0f48a0b03140341c0e48504041d200d601c015801e034000c900004150381c00c68484400320034a5175100b0504404a450046801c10340701000c502c072000c001250740310640001854543e40122503401d400c14200070340340151220702e0665900c4d12400341c020f030403082000141c2d01982803 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 971060665 1250 971059415 971059417
    0x1112060d08070f0b010e0c03280612081201090603050304060e030304050a090218010813031103070f1a060d0f021c0501020d090201080906070801060f02011e06091409100e03 76
    0x25404107102c0c40b1010f0608120103403030340c00d1107900700d00e4a040340082d07044d0311000309407401800030321a011100102c4240d100411215204d0400c010f5a680b41d0026074100043d2003940d00d40d000303054142d40d03003245000d00103080c90140c011843da5800c1000400c00500000219000c481d41c42ca0700e88003e40700440002d0641c03085500480d44a0900079002c01c0d14006d541c02001c3c403640147c01c2200e4000c0e908015980715030129840e82c2d025420661140100780600650002001100207503813070b011031a44c5155100700c1c40c00090309d0111400c0c03c60401c0000b1031068940160b070881d16280c1040640e6100a42c82040000c001d0007540e00d100c151580384072807c0b00044185d800002552a641005002c02c010844260140c0c00111410045900e0310b10100345140100084e81d1030b84096800e10f10b0544200f504011410115035880d000021041c0c0070701c1c031050600b60710100100d8070b54502030700319040d111500d15484500c1c20710305c20f00c11080340000e040c44c000c0407034000210b64051102841415 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 971061915 1250 971060665 971060677
    0x503041509061a01090b180406030503030403110610081e0a050f0610051206060103094101050906010608310b0903030405030d1a04140403031112060d08 67
    0x400307410102401e080200716040100c10316400540c5211812006004458040300b41c4548007685a0400004440101380f001100740d8113000740c00441d20540d00d99426280d940b00310303004c0c0c0c005000c443c4018100b510a1114a401580030f9041c081280e0401a0b101d45072443d40b10340e0700745111a20841c0440b841c0c180021000310f5000703429101d0a0711030046054507100c0444000c0c0c01c071504608003080078178054226180030483d0000404250b555600103400800040c8010340308010201c954a512010b90308405100c480306044900615a084a00ca03020203141d0103500c0c85079040604008200c000021954110358540c5000103107030312030130040742114082c040518000c1b40d05074505404031581c0310340b4151442c030902c601c3c110b595a003111a80ca038001034400402a4200700030101c8449400c0d00701180d4034502800391681c0ba8440d50025085410103000e122040c00b00c2c1040005261301886000c050814044000d07107089841464001e41c2c10008202611a2070705011007410700100e9015110 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 971063165 1250 971061915 971061953
    0x307110f12300c062703070204020c0a080d060317030c070b041104061d090c0a09020a140403050a111e06221205160b0427060b0c0c03010b010f050304 66
    0x703541c1625003181510307140700300d4078145116900c96085c00c0d0f901d60b0f0100085486050405035080104942c20071003c0c0d4025000381d101480740c00d5605000c40c6001c00140f1903500c0d80711b40010130516516001800c560f07405082e04000000303001304002066030100302d81d02558803201004441c1c1e25032408516188440402c0364101e890550080380300c40e695040c80195482c920420045591414440c5658444890b98140c00400c05041040240d03001d8014002d244120708010030300c6000ba8048012070b8205a0042c0c1302a40010340c2d940a000841c45808200b02e030989244021110002d90b0101040d03460351854021400007030101c0f0f50502d00c41080c4042c107001001165a5580c40740e121010001841060ba0b6a020380b20008030148011081c03401150b140c24812820145448029180e2440e074540c02541c11102c0015800d44810902c21709001d400004840c2d610362044506162400e60001c00b01402680341c04038404082e0b03088003008503401d60070715241c1d5407a0b445240021160300c078848484 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 971064415 1250 971063165 971063167
    0x70b0a0f0e0a020a05060406140f09220b0f0907120e070816080102040f0b091305010f0911030c030615160f12030b300307110f1230 58
    0x3a40090003140c90414140211348030302c01940c991003000f806110300e126240214a200700039101890307542c4013a02072041500100740c14034001c8404100fa5014610520b00c244c0c040c00d08200d241d00e0035105001501070155440340e80b8030b091401040c10b80300041c1090301801440701800c149041140c004031038168464054409903507070b84031010399640c5411440c207012a2141c07000700f0710110502c29501180c07003102c141b1010524003800c0e00c0090f070020728100c1c0c2240a00720384080307190301c0c4d0003000d000b84000c90103055950318024001c411242080140c6490440800501100034180c0d01504c1d00b040e0b040314440303821901c055041d06180b05100c0c03051118042402101c2c00e010312000010109806000e414060881da00c40403001c413040d0f007109545c00600d4820f0309602d1a20400221103801c010004a03546450703508a052450704181011120030100721f08000075402c20500f140f100038402c1e903003042c141c800d0480158440800a00401d219252440c0041c1400345c0b1003a0070325a107021103101 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 971065665 1250 971064415 971064431
    0x70e040209061b030c06160914060405100905030c0a0302030703060b010323090d0e100f020708010f0605031204030807150b060307020f0d14041211040608030a031a06070b0a0f 77
    0x143e503d94000d01d02a2809000d0000041c0303611707500c2c40820b928080c40340e5415000508003588010440080c000c0ba541004050001207066100c040d195401c541c10390300e0303400c50780d85010f00b054a4400003d034454003401148030204010703180060800309507a44010702041074898240124000c0451200548510ba98140c01084500d078031600c070b5010f03c1c410070a48a9010300d58205a6509541c0500796800000031801000b120348100f110740d03c031600381e10640e0320b40c0d43e4402c1c070280ae45071103100248401d40d071400300f0001071408103c80e902010841112a00b0309207191202907c0d40110440944a85120040e00300d0340500366220f03900241e0001e043c03c1e228141020025514460307d5030320941e607c90f00c41050883da0040d02c60b00d00c5583d0b0b4142143c6424140001d41c1555448040d0072103d42d882c820042815030344900404000e0038080740250344800c181d1000500b990301821000004600c0303500c001540362120700449240c00c0c0c0103148000141c0710380c42000010720804041c50748180c40d014134 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 971066915 1250 971065665 971065717
    0x141c090f120305010f0e0c09010e28091119030902040204090f0b0a0f14010905090403021501060e03102a030629070f0f0503070302070609090203070e04020906 70
    0x1c400000140350b502009940c2e00c80365240c5c02c81c4494050800306180c0d110005e10300340c1781c40c07000306940030044c9803241c00c0d1003a440118501607408510a40c010703120b01005004602c8914611004102000c0309010403800001003800038851000701e8000c3c14078820808d0fa58a0094100480c1e003035005c0e00c00c65981c0e0381e07411440c0c010310441240710703196810320101c0e40d2503140c240400020342d01d00004040b503030791800c0c003038031140411003007054140400700340005070b1669140141c0d8801c82c081d03006803041c0e1009403003c1000800c140c0040007840020342d0310044c59103000609100e070090070311002a104240740114049000d414244101e0004541100e0003401d034190803000840b421080322030100b072071640c20b6038030b8600b0842c03400b00d50340810304c0800301050032954a400e403a8050103000c00d450929407141415640503031420b0300035034030265003000304d268058130780402000310120460940c10411001081840503558052040750041107055441d5075006c102c03016058403150201c046558406 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 971068165 1250 971066915 971066933
    0xd0302030f091b060a03090204060311030f072907052508070303121a030604060504200d021e06041e080a150c020307170d060501141c090f 61
    0x3908221034020002060b50241c0c0042e86554480e035083c0c1d030341c402e104900240030407031700f2204110007019281d200800150315288103210281d0b000e201c1012415008070140b41c40c0071814a01442940c1c0594410054200c00c80d180c0c4a202c4100c81d411400007150340381c054294019041f025016009407883c56104440c211032406c01074011021096400355038144940d00c4490303620014000c540c060b03d580c002da0501d070703014410102c151a02c032280035000c800801d1801208580442e1140e0b034601c05d00c4244130305074123100e41240e4031800301503001c1010707408210380c9181d00c180240540c0031320a075004001c29030450707600e2902d0007521032500c0703503611410f150a9403088000c107158009008800704103c000841e40e0301400760460b0003202c1d038940e00c00c0135000414904c0c038042d04502080c0f04081c0013483c61100c2507002c8041140b61074a0f40030002100080780c48030350102d414440380c0c000d20402034500c0c0d416540040f40340408000c2c0c520030705d0000e40203000785620050603159203a84c00c0c001c22046074 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 971069415 1250 971068165 971068171
    0x140d02040c020f060a0c1709190305071b05060d0e0a1b090f060e07050a140403080c1902010f0f0314010801051b04080a0204091e0809130227120d030203 67
    0x401c40f03e00340c68040c1c800c406c071094490003000080080240c0b1700780b0f0f00e0307200e1190b03044001c40007110686600740400c0140a00220400c80000340d0001ea01d00030b000d03a80768848044640301817003005403468000000c140c1d101c0c42d0411104070b5103e1442ca12003803018440001c1c00781e0409002c5810344c2c1c0b8441c80003a03a460314003d04000300d250070840e1026541b903100300e806a4481030200c00e043d88580100782c03000d0b0401c2c140d075020410340d1a50340d000000c0004c05040210710071580720392150802c60070b480c184443c0b1744506400a01d0608140f0160f80d0021604655100c03034245041c0340301c0441c104601514013040c0052405400200000d4074480560000303100c2c0c0310703c460f0fa1801102c41d1304110742a02ca580b00744a550f40c802c13038040c009454241d0000c8c4415100d004001427005816084d240341040440302641c505130080740000313581c00e11111540a48a003040114645820442240c0c0d811202809035034081c0400a907110310383d102d0070a200101c0500d20704030780b24440c000c500103010b54412 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 971070665 1250 971069415 971069443
    0x1201150e09060103021b0c03100509070311030a050f0c040e060603060403030f090c080609010501060f0905060307170411120d09090e07080a060f18030f030c0311070c050a050f0604140d02040c02 85
    0x1401c1272109802142c46414010b58160010b8812140341d82c8402c00a031f4003e0307030300f10703031502075950440e0008901304141840c800c6500d026181409030881003004546011280652582203001045020b680220301568410b505007000039000c140030f9403d80c000c0004400050120400c0388000c2040080015080c0c800c240d2800203200c0d90b070722420b0842e00005407807041e5000c500c07140c00c2400185410745c06103510246a2409405003150b51034001e4104000f80c80c155105041d18000000311704015400000c04001d0700c00400c44403a140000905440d040d01c1049006690743c0711082c942d407030034130007000140f03c8801191400301040c10500c000b00110000ca0301002e15050fa20314020304150f040c00041501a02c4a40004000c081c0540140140507091010190781d4220003c150030b41d20302414a05000c0d607c600e074505d0600d0b00388500c00605800c06481075486548030034183c2e665a0450741aa810700e5040021421902c0215540002c000c01c02507000381004101d80801c3e50000f5007010b05528 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 971071915 1250 971070665 971070673
    0xe0601140f060a2c040204090b15090607080304022b140706091404110a090f080a03050f0d0b030f0d08182e0f0f0b0108240609040e031201150e09060103021b0c03 71
    0x1c0741102b074684030708031900b60400b005001100225442801641d40705002600603111900c4064001c000d0403015061441104141c87c23214043c48805031624002900c0d50b401800e0680c1441409400c0013600c1c8a03080616001480c629019100d40c0c000012881c90340e04a01e0301c84400c0c40d0040c00d104014040c48484822104001130030b0500040d4014115405880ccc4910f0701031140c8000401c0d5000140100b01182c03a4440603419031810400c01c0038200401e0b0142c03071584540c02d0010803000018111807071022001303103040142e5101054007205d003101100d0f9105840a803080403244840e50784286000d03a4507240140c0c0003216190805001d15031020030400c1815403020040d1348004066a8410000803100b2a10300c034440725882c8510b0082c0010900e0f400c00700d400c80003030140d07070b07960341107081d00d40010075601415406510680d01412840c0d4080c001d00c052400000c00ca2591402d8052254031440040741140e4020f030b04a4074000f404007440e4540428901c2110354841c110306d074943c000d00c1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 971073165 1250 971071915 971071939
    0x9010b0c0115060801060210143103030f0b03070f090903110604050c042f030a02040e130c15080a1806020d06060e040b03030d0b03010e0601140f060a2c040204090b 72
    0x1031512400d0080080640827010f551140e440381c6414810250342d4405152103010702600455152000301c0c0654402c0d5000314000036a01c01003010f603000c291045000358041d00d002c0c011050900c0440d01950b104400000e20700c0a079003800c450b400c0303130f94003201e5150043c030041c8070503c031003c0b408111010003510248206481c902e28141c600710b10b807800281080311606480507182801008580140101c400507080640324107080b2080072050310b60000c0f00c981e03024008200180d08054000034291207020160320100c1e02e00191001d84000c0c10105039a544042d042d04034109a9085d070030464200c0001c40d1a14041086400200118010780000c80e00e18400301c0c07150718250003000d500c204090b02850038003201e10314040140c01c58200f050741c10f5490b1501c00b020643d041180394000c060702c892440c40d0422080c10b2240c00600c0100c464082c2c03504202c2e501741c1c99000a00342810080c0e0803082e840950115141240a05d0030504050780310b40006000a003511182e00b0500c2c0061703044448600d005 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 971074415 1250 971073165 971073193
    0xf0708180a110111150103110a1a031308040902070510020c0a060b0315040b01031a0c0307110a0b010f05040e240414101b0c0209010b0c01150608010602 67
    0x40c15600d40c0340a99000c803019400048500c5840d071010078044c10314070f8000c498040c42d20705000c4184000e400c184200300040052040c0d42540d504401000d803400000306040076410590200395407604e01600d031000011500c02041520448601c80d001030f40300b13450311307200c0c50b601c006580800310644035885401130f110310114951080f280e40564080c000c00080080350703941c4000c2d0140c0c00c0c500d6410300903e011450030308081814030303200e6803141c01340541c558114035141f1241940a45c3c84a2080e10f00010802d2115140341207a070004028140300c030030310310100d811034034284480344001d0400c2c0800c400000e44030a00c48602c01a150704807014004103621001095840040c00b0341c1c0502d901082d80000351107000c02d034900d90024083d040c400180780500d549030b850001c0c050461010503540c1c00d4245000006d100034409124194074140c100142c4a4001401d03940043c010f1410f900400a109249900254007603481440020030400550f41e5136400940840001d01c50000903024500b245507890f = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 971075665 1250 971074415 971074441
    0xc040c0c120815010c08091215010803040b072d03121107020a0b0a110102040609140d02090601031a042a05120f04080c0f0601180902011d180f0708 65
    0x1e0003040c0320254140a10f10b00440b4211104541a03c90784010082032409860b401040800d64074001c008054034a0706000c40303041644140d1090030190402c1c0414800c4111a0080750b000075001107e4422215103c1d000d55008101c11000312000000c0c0d944000415070005001c244c8003030100410028218500c0c00e100c6144a412030096015a1080d001d0140000d00d102910252640385054a034200c1c1c01581d043c01c9a006410080c08a10b00c24010420940c0341c06c15102c600c842a10000a0b208407179022918100001d0b200c28140f688606500c6101c01091420640031080108180030314603503036903003020024038a00d01f001ea42c2d280791807180039640550100c403004d6480703030542d5034217076154451700c1c20340c000c0600101c030620010050000c2d81d010070024201c484881d1800b6119551510f000d900a200c0f244c0a401c9030b05085c010488003507070b00720b450030310b445803540030060003101340800103081038013002108020062640c00b801310000c01504a6031041029450354803407900c80045040a0f = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 971076915 1250 971075665 971075671
    0x1051003020a2304090303201c09240b0a030c0302040c02011503170d0906141602030406050708070204090803090105101505160c0801271e050c040c0c1208 68
    0x540703c200e00d00c0040505080d031081802c01d01a1800044034550b40e400024401700069440c0f407007202c04034420701041c80410221400101c640410002c3c40c042d81c1e030b83e0760100481c80541c00300c030101c403242052001d03140e00b00c5081d207039008102c044015102e10700101120f083c0d0005a0082e8545a4003011860052045040702d914003181d204596185a5070030b4928050010440701c40801403101885050190056074030f1984a9100401c410120010b864150304005020500700148403500070440d81d0040115001e031001481c050765122024100044c4600c0344d01c0d0000c1d00f040c9011301a8060142140165015184282c000c0c441d42c0c98004007481d90101c0c901810b03012128040241c01114000c0e4000c10040d0000b60251300c00001d143c94202d003011607076100801c0c2d80d440c0c9141800062104e00009203681c0c06400f0035003503001c80e84950010748451a0b0802900f660656110244201040000065000107001780f0400c00c810344001c00010007020103c0e651403200700070458107400380c842288 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 971078165 1250 971076915 971076959
    0x307031e03020405031606020c090c180321030f0106180e1806090718050f2e0914060d0f030f090909110117090d03110c01051003020a 59
    0x100c44014410042101254440100a0640c204400200390701c041c002c410000c01d001800000d103901d0190040e0070403680c4480c09100e40c0b0a0307008c000603448980196802180d09100c003d40110362400840c2c949100e08484c1002c0c56a41c540040b01c11340d9203401113108541095041e40180d03681c0c2170680300840b004000040804420344140a080c0721605055400003070a640c0c00084903000729a81d040c00000d442c010225000a04288440500700c494000c0c040d0306e82c04d00304028601400d540c00311060190100c421400c000c0300041d1014074805c902b181c03104541084001d150f80c2d4080f8840100b60025025001010210001d05130303117801c40b8400c2c1c01c40e402c4903100a54100554084420821421405044c04100c0034040396000f09032240d03d0300d0304d00c80c7c110310400d801c0c9100090070700300c4a04080d6401404190401101010120f07040160450605001c100d410300502000481e02418008e03800c0c1d50311f01170401840c103030501044411a070082c0e403041902d40d00c0306c2c1549460032810103000 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 971079415 1250 971078165 971078177
    0x80304030e24160b1905060d050304140607080406030c0f2c0415061d04020c07033503040c05090705090105031005040204030b04050c0f0f040203041a0901020417030703 74
    0x103641d42442c0018030360000c010181885140d1190354200100406550b101c00106051148440c8036803144105600010704846417020342c2030b9556226502d1182c5d01980d145c00341105680f251540728002501c42e0710350f001c8802c82d2201c1d20b40e5001801031881001d10000a1840f400318004240250301c0d9003a615820345c02070040c010020780b0b0030400d242c01145207802541e00c0500343d480c01c0754800c110024003e503075250543e913072140503807181c9020f001800c20300c100d10401580015400000c5c0d8041126880601c0081e00190826282065190102c0b01c100c072203078403042c0d111000f036060b0080d44124420034030101041d85850070b11a042100311600b42c040b41c4204401105907000b1f41c003540d4058a00d030300c2c50051a4590003c02d05a0300309900842d0911540c1007801300b000400e014010b494501a610881c4003504a00020300c003030b110003401402a540000801e06101e00200182140039509182914904207098031600035030040c803900441c0650041e00409a02010080700e0060360503075101 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 971080665 1250 971079415 971079469
    0x18050607050928050a1715010e04020d03140706090b1e01090b0406170606120a0c03080304021305010e06030f0714010311040f26010c1205060418080304030e 69
    0x260030380c9400c51907043c1e5401d04107074005800d648010810002c3e0612031515a9a8a0544425891302c49090180d0700c03407850420051044030054103140d81c1c07254045600030146103013402d082e50800444801c243d035111000400b10305000d5550000b0503041d10030080c03000140e840840c0550070002c150011007640c0f00800041002d58030a411140301200d00800c0021000e81e82d0090400304461222540002e8001c1070400071245400003c5061074070001c0b025001c0c5900b5940c03200416074083c08000c3c402000440460706640702c000c0003080d0807030754800800842d40c42c0d81d1852000442243d685209101d48110140310800202d110b200300c41c000540c0e503041c889140c0064001d40709100051103d01020b0000141d04c0062888500041c04405500d800c020032028090800c000c080443c15120380c1009501b1140703d6004030b14098840900c40c00103020f40b1240c3c0001d02070b0060004400700c0d00c1034480510203020010380114040d0b4841c0e2902083c07803080c0c50901c0420440030b041c040e040a50740c001 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 971081915 1250 971080665 971080699
    0x370804030305070924030b151608040e2a070507150221040911190c060b150903060f070f0315050a120b0a020f07020607060b04180506070509 62
    0x80960400c0362403c2c03003c0081d40b03843c0880303410a0445c0a41e102034080c880c04034031044c0c043c840c17010f030a20b0940b0f50140c0c09043c0c18102005110328901814080700f01200e0f5400c2c00140d00c2034902030143c0e610030055506000c800200d10410911a000720514070103091260420980215002d0030b50140181c01031503c3e2085101140400e4048602903010790707a0003040101d11100d04810354150340e007080e52510700f42041c0d03508030703030340208004000b4101704503035080c0b9605601407203040d280500e4904c0c20043c1030300d020b40c0948181203480b900007c4446050200c9501d010240c4106c407003d4013203035003a56030800b440100070b90a0700c0d400085981007059010003413103a0072080fa028601c0c445d6009240e03642c00450080301c441d9000360215000350850a0412410010503500044041015401c1511a038040d84407481415402445180000703196010454660482001150b009104002d1980c500030640354518408508031201c0c020f000015003240d0081080d06c2d0400e4001c1c041d4150300300400c030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 971083165 1250 971081915 971081921
    0x309061018051e10080c010201110d0504020307030c0b0403021302040f0b0309210c0f06070212090d060f05061203180d03110703030f110c031903050706023708040303 73
    0x319a001d40d00c25940c42c81da41e121484207000f5610700300d660250500c0c005c070700c90926010601c02411a41825580202e03604504290707000182d5030b080c0040c0a81710341c40003916000d00c2d03031b100070962044080d0000b0a4240c107409041140c2c0284c45840e800c4911406000480c86030b401072541211032602c083c8071154440c0f0103940d03c807807640d00315001120015410b41905080013059401c0d00300c0061a521520700030b0010f086104200d000501a50501c2d241c01303074136200300580c0301141c11000724080d5001c0d500c41c0d030130000d0740c0d41103e020020101060000300c050801119514000d00c000807840c40039078400011a05520511221300080028800c100090010f41c820306404104c3c42c102d540304064000d004210003948030b03031030f00421034044030009440c0c10544501d18000d60003240d000000da0300e01041e60f208495410b1180b05031a6035600d0f0540b100d0040c01805041c062010951402c80c0c4505107800d1803140c040324400b03010300f640303900a249090660900800250b264008a400030b40250 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 971084415 1250 971083165 971083171
    0x510060201091a0417040e060f01020f0d141e07050d05040f0501120207050f01270201080112082206080606361023090306010608091c05030906101805 66
    0xb68501d24040541c4102419941143c0c01c080348142016051110505c2c0003090262401c1003030000e84028800315240c240c4800c00444dd03030040c440044034984181d1040c0080720980c082c0744409805d59506400d0480da1a000000700303c1d071b94841e45480c800030710f004406440c01c0340c0c44110348041c0581010011121343c2034014042da0b010b9000d000d00d80c0020000e01c849204090741074000201c0f846d03100444a00801a441158140c54603000d43d070b80940d920440075415240310303501000e0800000e180140c1d29114200c00401945c0503204140d05c80e4141e15001d00449900350b40340f1032113459060070032802d4400c40503500f1508118004441d003866000041440a840b0310860b10a1502d10001003030100c800000030350005040070f03030034038002601a80090302c5d40001215071400c2c0007408010035542d0030180242e100748a0340e900090380110f000c1101c2c0c0c0ba0948070013041440095111000b4042d60805c0d1050b40180c000c1c070300006c001c0c2e000201e80400f1030341d0b0300d04002000f030859443c6400904002d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 971085665 1250 971084415 971084423
    0x9050706140f03131a060f0405090a02180f0f190c0c050102040b0c060a06052812031706220b0a12050a17031303031d060a0510060201091a04 62
    0x148820306081c0703030420185102d81c90481309980002e24620f49148046185400c4500d10913181040c80305a44411000780135550003510001003940f594601c5615122000000030350001003401d8000000341a242503a01800303110900c10b0b11b40c0c030b0b10300c840130803011300301c507001c044854020403420580410f8000708440c0840382444803066025803501c90982c0c1c0580c01c5a00f00e501c00280d281440300d8200b01250380103401040404c046da0030100000c0c5010384284030000c0d810b000042c0c00a0750410b503044d44001b000e101c40f0000e030b840380910f800782403904102210841d940a01c0001100d6040c03104a1608200c040c0021200c5040c01b401c040b0010700d070340c48080340c104800c0100820760028600e00300d007400c1e015000a0442d50032600c0c2c803032190960880c00701240074042c000d0242111008100c890b6069042c10302084d204100590b01141010214a01010b441032509212a5544540c006800b50320140380ca14281a214041a42a9691a18004c02c12415a8044c000981c03c1003d02034025101d = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 971086915 1250 971085665 971085667
    0x61315090b0c09180a05010501020d1e05131d0621120c070f090b1f080a0504020d0b0709080f120f03130c031104060e0c0d09111009180905070614 64
    0x1c07244c4480421000301d0b1440f444595802c0180f10075a01000f40c10344880d134038034119101580f03000b408200004500101024044042a115005058240c40d04081c07c58440d5200301d100e0700d06002c0f0003845082e41e02c80e00a007001c107111140441c0c4003103159190f4001100402c50710000145501195014840703003551030048140102d038286000e6840e20090000c02e4010031001c1c419000c0203002c00b00761050a0f032503c1101800c0f401e1503080040307281d0004401900040c50b68690001c21250380400000130410b151940c1080461030300480c0315815034049004480b0100411740c3c0c2c0554460b2010180300c41800248162070440205000455004150795400d0030140319a641e02190900f59800803200e81081d000c490009062600c214001080c501d01c0780b1840b400c0610f0781918500c5400000d03281707245c650086070244a40d003065100e1005014044000b500c0e4122401410014240109260741c5c0b0250021101a0f0150044c011111741200c0980f1155140000585980f0b00e1101000145e4078 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 971088165 1250 971086915 971086939
    0x501020c0703030e09010602060708010b1e07081e030615090307080304030c030317070f080703090b09030904181a04140d0305072d03090c0503061315090b0c09 70
    0x1024080000214401d854000c070031480c4e54200100900142c020504551000080004559008101c281124004200c65035146282400c6150000c14905901440303000000c641c420020444018400348020300300b8644a80d40c60714050101c1d00c0300790f86d05130348011000002e441201d014402803046030b80040454030620ba075110240e007160025032007504d110105401c00c0007815040040c00041000807102051030b89440c4502400b40881c201458041000c072070002034069010b80c1c0106000740d08940e410200e0303c2c042c00000e603a41c2c800d14503d4003450600c074164015160000c1141d01e166030000020440702c030764000300000000000c1c800d0342c041c6024040082028000d000300c0c8421101590080340c1c51400c40c40c086c0007031035440e1114488004c5942402c8442c102d231960b6484150440c60046500c0c80c150820400001060f00714650601401e0300307110f1526920f803d5590168450510b074411610000c01200c11079034403020103001411104009416089001e000741035080004003075078110343c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 971089415 1250 971088165 971088187
    0x30605010822050d0305070906081e07020c19050a080619050c0d15060305010806091c0e121b0d0f0f140a03034805040506070503071104020405061204050102 69
    0x2c0388500c213541c0441c1d560802d01c00426407100405016010a003000c1c800c2d42441c0f008410010b815003014120504004003081605109108060011600624004e13822094800c000d0b401d100b14030030f01d84502da000000081c2e003c40400c4e042d2081c9510310400340310b8030b4100020806010010442281d0b03840410a03035800400303521410182020059000d2034803424602c020b0200e840c182c01c001d0745680104108203201c4000604089100d00803c20a001d80c845e080058030440c011404041d0b000e02c8202e8105e00003000001c90b04e18012034a0101c0580115003402d00660400c666001740c00145c0c1410300002003605140403020861061400d101c103c00c50083c400d0805000b5241100020b407560514040d460a90405080307400c2190760803000c00780840c100300032034140c0c03421400d0181c480420a442d042c1c0200152001444054281c80d44e03a009850000d860351300c405821500d1000d1407480b020b16040c01e02c02c0c0c409440026280c0341c6000108000c2c1540d0b56130043c4125041c5d03401b001045504 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 971090665 1250 971089415 971089423
    0x50f0c03130f030506070801052116061224090b0105070b0103050a0b01140f2b05030325090303051309020f0c10090c06050a0315150f03060501082205 66
    0x4120700d5001ca0416030030f41c41c02a04141d405054001080b50007001403205581d0072a1a4406078040c000c01c20040c0c0f0151034445c10241d69240e01c00d0640c64840700003491540040c00c101401031200000c22612a00180136104034003100591004154440d2044c004964140e06c00c401000050601c5814a200c0d0307520501400d00980088440b504844920002c0102148605014000309545000000901d10200c0d040e10030140d1654400c0141d92828100d14900c1e581946500b420070000540d03940507401c029a482c0d0041d203c46818055107008010540610041c004880d501d03507a50300c1c1c54504c0c6880845443d0090030503012500e00881c03001a11045a200038042c55034a20200c1d80c40c0c00f031a10041c0d0800d60071065118003541031840c00b60024500f011010306540007801e0007900e81001c410110000c1007501450403822008070703030100320300c15802c103450b69031a20b5035a10000a0211101101039681d94820640401d1548021881c2240c195010500711015005400d8043c0a90b403200340c50 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 971091915 1250 971090665 971090669
    0x7080403050421020f01020d050f0d0b030a0303061d0402101202130320060f0403141c080f070c0b0109020c010e190209010f060f0c0204020405040c080906090d050f0c0313 75
    0x150b0f810941c0c0c0c0f1800c500304075160300789425090029010800c003000740680140304041044485060028180500c816103a1050b2030410005d002c42e01400e11503c6d01500400550003a46111806009541200d0402503101485283d01920120040c0016081940c54880c2d401c00c44403511303000c0c030607041c403507503036450f403000442c0681c00d08401000762403800000ba203038400c440341c056101006500d210700c204008440450380e019200d281c0381c06006542900b030a090500b1034140c5000d03440303014044ac2c0d200d00c44901410003c01028626110600143c0e4803c0c000c4000030000854000100041c01455000c2e10008d50304a0000c00c10142000380107080050700704000c0d03c40048210040258240b100625002d0610499200c1000307041442c040c1c0a105020b185004001c0e1031b60122085440e15010740c1e00a1402500c10b0001d01042d81c40940401411104030300380d4445c101c00541507050010748810710b42d696488051502511080f00841a80300c5141c400321480100a80740c6040214011040 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 971093165 1250 971091915 971091959
    0x50c09070915030504060b01021911061209030a030b09071b050c0316080c01261b0c01051806130f0203121306030e0106050a0501080402030703021509010e18070804030504 75
    0x184c03925284c50000111980030b44c5450444d0700900114030803001075440c0041c03d0750000c944d59402009000059401e00c01c481c0d40030303141442c6a0a010301c0c1080040903025142c0151400c1c08020100c00611220a00c1241c88500284213007c4c0f0601a00b110364645110a005070195249650381e84046807401c0209503501c0341903e0310b08002c02000c10280210700e051380302440c00b500c0c0160601540c8002c14020045c4007003101c40a404122400d54000d440c003017052034000782035160950270240e180201401c90b0708082004e0f146482603d4110049400ca1103550503048240d200c14140d101d2a809103070341d4a04036014400c0c500d040f185400401c01500340c01681c0030035480500e041c543d005050b41d4601941200e40d0f81800300501069a80c1024001a02e03030078038044045550b54000030745043c000d07030300282d0444071006540348028100740040481c40420388510a0600c60201800300d14251030003050000030b03014000c0b500c82c40c4506c3d441e80e0041d02034a0300a05041d1a80d90480c5c10b0b80c0704001d018 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 971094415 1250 971093165 971093171
    0x6160206270604060203030f090c1504090c0e0312161a06010f0927091a1f03080a050304020102031b150711060105100306030503040f21050c0907091503 67
    0x94164403207403000022044182c40140c1480e241c15006996804050080d200c0c1400a1002030351a1302c0c2004100c0007044000d181503020340c20380040c420142e00c28069038809a0900400413101401410001402c810150050140c8044a144c4115030703040700c1c500402d5001044800004a250501c09148400c001d140c8400f503030500340c002519250300041e544060203403000f8104a010310541040f840700d4406040016613011100c41040201560f0b00002c1060b04800c030090581d0a06618592040c11040b01503982988200d0515160548510009008000400c07061506074881d001450f00184180122030510080b200500d80160004004100940c03200800030390101d0200301c0b0035041602810003501d07551451407000d0b11540140540d0f07000c0c20812046440c41e500c654054001941c014003680d841b240c45e403503141c0000d0f130603100c1c8113409840108900c0b6499440c03100d05011640c04401009507040c9038060015101c0000c4c00e24080c0990002c0005609110020011310319400369000 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 971095665 1250 971094415 971094457
    0x901290306091c0e1f0905010801080c0310020f070c0e0604110c0604140f01020a200c0d140319020307020102010c021603021203130602150c030705040506160206 71
    0xc1880c01c0300042511000703911001c0004a00065818050081031051500c0e2034801180320100d03d200c0300300412020a5050840d281c081103a0000c1401c0035121300b60703a001c080d641d03117540d00303a55a41c19010196050b00010045c1104082e60b40c010504400030b00c0070310307041074640d0b01c41d002d082041d6030001c0b60700d101c030b8010410340f80340a22500c0400c2043c0c94406003005900112039940d4540240010152442c1440c0c0d0010103604110003603075407407d98025542e88003040b03c000d00da203079030044004000b0034141c4040e00c58540801c0e094503000d000b4008507039070032443d241c40c0e2960041d041152004e020412400e5888446000d01040d524a550001e50391040700340f00090071160800e01007003c54000082c64143d40e22907801e9001204d40449070048454038020006003036114441c01c50180b417103515000100d650300820701703c0c00003c00020b40d0000d640d80c103103805100d120882c4e0041c00a0010001840316280c0f410103044880311100302410754024650100381164804807889016908103405 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 971096915 1250 971095665 971095669
    0x81b130e150c120c0901020f0105072111031f030b010909140d05041502190f1203060b030a0f090b0c25080a27150e030a0f0605090129 59
    0x10350360300010159850b501d0020b50f03000600e003444002c0e11070320301034070300040000b81c5070300c00c001c0da503155650701c00208140e040100f40a130003003558248154100702401882c80c0c42100714454541401e60f0740050302e25641e162400d07102920207800b00b04603410b11580e40400811340103207070fa6010349003001000441c1645030400c0d1103410444543c1520942c80b10080b8079503641d0007800e5030103c1b0103040004c0a444102c0c40240d04194000c5072589851100c4484001484480030080305d80030b0080101840015032000c00f03c0580d0000e0040c081034150820202da5078401c9035010855a0300d112500003081a4070b0313074031102d210b402901e02545150000c24554100d40c5c800c0001080e510444010046910b000e548624080c060607403d0814004401c510708a64481010110400d001d81140101c22649544c84407001e99901e611003000980d00d6100f584190400264103e4010b0700048011001500c0e9610f64010780743c0107080102554a41c0b0407084011134042c038030280c51011101d9002e000010b041 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 971098165 1250 971096915 971096953
    0x20a02010c031a100e0607021305071806020705091023130204030201020c3604030207091103041202191a0907031e0528060b0604081b130e 61
    0x440002c45101071012215903503074941c51409a10340a0401c0c0010b000d21800003056401181f1010f5013015036018210f1403084554841441007560b86c1301c1043c000342910b800d4403a103034640194401340c4c0c441007007070202d8500750001ea9800300284000a00054907034543c0121402001d0a203456911610090b21051400896900785005c0800086040a14640000b0740d20200f40803202e0080034141207130007404920941c41d040f010180040d011403590b02200c005000102144e064005000e03a2402080c5890140241240d0441d8500c40c4c5045890300c0d16181c00c0c0c020f0210103a8103600c42e1342c80492140c0d803e9070401c0d0000e402003081c0140d50000064069285800404070407040e0844842400000c03210100d40100d01c2442d140b0844080181c5099071500151507034001c020410300c1d04643c0d03000f03280c1c0f01c0a081544103402c00d00c041d0003514140311641c0554054055650407002440d248188100308103044941c008110300340b10100d0680840403501d02d0b42c424080c82c2c000030010240050030b03034 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 971099415 1250 971098165 971098181
    0x32d14090d0f0309050319020303100b090607110409050115031b06050712020a0804090603050c030a0305030c0c0118033b060f09041d010e03131a0706020a02010c03 72
    0x10140c661201c0000380141803110b907150500600d0b5582d0a840144901001565411984a42255442c096899010b503881d0812a9401c4000c41440004951100b01c4001d8803031003203000c0d00b0346040001980d03404900d20710390350405d904036585801c2440410b0003402014820b11562200f20a81b90179802c0000c220340300300c0c48003c44012908410041140e01c10700f15048180c018031400e8000c150f52204904040b605400030340004000301c0c010a1071041540b156080702d104d02c040341d24190030310043c1601c6803030804029001ca0300510006251940c0c400080090043c4040001495065418040000f0301264001d40000b010a40003140d04800090081104840e4122014500510f240480032280e6101c6210f405030001040249071030540750305403100340c4e000406c2400a8040302178001c422801d0661004459070800360540f00219020048500440c8828400d100042c2080404603c4400c0c8035800ea50302c190400a160100c0c003280301801640b003155002040708061204001d00341d40c0c5003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 971100665 1250 971099415 971099431
    0x70f090b1c08070807060e031b0c010c0b0604090206030c03091905031903060825050604030b010e180a1b0f06020307031215080a0b0703020301080d032d14 68
    0x369841d60059032100341c044074103501c0a8100d6441400b0301c2c0044c207501030210020445d43c03c20258645044010026003406d010701c142104000c0401e001d056600c1050403090f5020554a11407207021408940784180d03c00c038007500105200d0035603404105c1c01c0d801250041904c0c440030090200010f03061000001ca190b00e0503103000d55030300940740c1d192207102d4940c203480c25140c5e80d200d9100c0b040c002d4000300004c14040054540340083d20038410030b180070000c1d2114488004410110300ea1404105440c1520341045041400d40e0804c01c0003070248034003404100030700020352800c0c0342d080401c100b020301e0707140304002c040c0d05008002d00f14195010503800046c10520b100310140020390703002080d29011034062516030501c40055007c00c005114000426022422005002c20901d80000f0b00c0d031011440707511280180d0352100710032400c0740001e01950040703030030074034082c1d165034440c4d0031071071100c0021941101c4e2581c0c9203904000c440710400c0d400041a480b100840b0740521103000655010b07101d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 971101915 1250 971100665 971100679
    0xd0903060615140c01180305130b0a0909150b04031a010e070503060d0212160810061214010b04050f07120c0816210b0a14010503042003070f090b 64
    0x10030000d0b00880684940c602c0e400c6010036103100c0108250420000101c00c21b0709615031003c00e040040050780070f00003181c0d5200d0011400a031070600d0104442c500f01b444d640c2d80b01414101345030715020300401d2035280510101e40001051103c210700040004600c140091b20040100d02038041c0120380580c0003c01e0480e00c00200805903400400301c81d032113403044030010250f00f03040c4001010329801d454440400d2040e103107040c5078180b1000d000015211500101c5a4105c441c01c010300c1950100d0007a00d10185004148500250306110114042d44c0f0070800480c00c203000001050403204101c0c0c0f001c00b20342864003400740c0560003ca54005201104109111b00c42030031038041c0070a94007502000350594001000405144120180784040b40705221070f01c10780d81c480c4445130103804142001d5101d04100000064030b82021f0b0071217802c0c01e03c10b0710798504580d5a500c41c50303a601941d000302d5081034400740700640d250340d0034004070009d0082c0d030701140001c0c1e0400058004031004998001e0058103 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 971103165 1250 971101915 971101949
    0xf0d1b0b13020d0b0f151509090c040b071104050f130222050c07110102030301080715030b0d0b041511071721010617010605091207080d09030606 64
    0x400030a406600a48001c2010001025480030440807586840e01601c91428003007403101030f200d45011640248004458841110320320350400150783c4503441d01551044041008805a0504080c169884000c28081a08255960200d02c14962080c1402c9440490103c038103011441c0c00e104007134020300007010346186450200005440c40344aa00061300c12800b158407081030807600462803410b100790640038049070503c5800f500032500884012160910300c0d10b400c504551001095078101d441500080c0241480c3c02c01c0c000b03010454251001c01c040d25080c100030580c440100e03501001d4414505480103183c1400e210365800d0043c40c070342c1e0b215410030080307603c000600e038140e0340000d03003000203480242000c101c20050361040e088001d01d56844c14814100044120343c106040718050b40f81c01c1d0349002c075001e20f000c56403024000c00b40828014000d003d9503042001c600b02148800100300c400c034603110030105290122401412000644081c010300400129004007802092510740542c8040 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 971104415 1250 971103165 971103173
    0x210a02030615010c060902120a060614040908160203150f0f0c0307050a0513050d0803160c0c0905150316050102010f02070b13031704080a08070c05120a09080f0d1b 72
    0xc04507031301810040e110780f100e00541d500d613a1010419003900c0c041f915009410318104020b050944070b0741e10000002c00c0d02031b150341898000c0226507980010362504c4d000d03d4006844602c0c040d183c040e40c00d44184541580c0c1c1e07244103a0310368001c03070054003000c049190070041460f100b00010100d448440081c810b104115402405585204900c1c0c101030342c03214150240c40805103015440143d100c201c0c051224184210355000f903005001181910640078084441510318001802e80200f80d601204800c0002a00d0b95103e1900140320302140d100c010880c0300060305d422411803c0494810281f1303410407440d80c0900c02e200c0f140c00d81020035030900b03034907850f1520640d100602d07498410000003416010540300302000303980c01000c4d0640c40064205424600c1c02d5410261045000c542c0e40c0c004134204501903800510842c0d8800c00404440700040c0c3c3c447e403c4e400a401c0711041c8102c541001c0342d09001405140c0c8100300700341c001c040000340c4c004c00900000d0a20200d1100c8102d04060901007 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 971105665 1250 971104415 971104427
    0xb010306050604090207060216080a020f0606090402090c1e0306012a03080705041a040f06030e060705180d06090b0c040b0f0702151c061d0f06210a0203061501 70
    0x4480311307040181c036590700d0b04121020344120101c010307109500084c10010031400d100580710b14000c503400c0701c5e44580c20092665480b8015120140e2103034190001070014a041000300e5807004600407214244403400303a40192406d00d5a0b0402c00c0d0440100411070a0352344211031081c5410120251a540c08240400f460220701da080042c0c100300d203e400065030a0301480846000b17090720918201030700946121242c2071740103405100c00000f02d109001900f41e200f4040d82c13954944040190007162510001500d9650100303855124145441f0022106a5910041e00508901031400440c1d41c100c14581001d061500500031101101e05010a01400084000703a40042c814004020f5449109000003107000350446400e0054620000e54908800c00c202544406001d04403020301031107032070704003680e5070080c045010b291b010309440005a000041c03c1c1d0454000e81c01070f1980075000c565007603003034080400220740340860780450103020841c00c0c101f00180d801801c280b045100c0d050104002020 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 971106915 1250 971105665 971105669
    0xd112406060a2003120a050103240b120703051509100b180403030b030c01020c030c090604090609081e130608040203070e1815060a211a06040b010306050604 69
    0x19000415103180b62401001c0388038040c041002480982021425402c1d038030745c0040004403106aa00b004030350a044035002d00d505803036000585e04150031314411400100442140b050f4405605d03048034223842d4076039107130038181000080701070020325040d1300300301d86440548090707048001120340400980351404140c842249400940c0850702e90030724000105502e0388500e55241c1441904140001c0681651000c1d40100050b815540100c000000582e210b0642107141038064200001c1040549801d0b00b0780e913071000780204001807020303641d00c4e004220b903485102222280e400041110940321144469411506e5160a142c42d040c004000880000410700c80c407414850080041021075034107009a00c0903080da4046586140b5240d007850304021303001d200c849290f000b12480341084080d0030803402d00c290310150141c10400e113400c140c0482082494010708a0200d03050071040000c1c2c4407001c01090f1040c0107108603403070504208200c1110000e0081505040c5426010412a280c900603a01 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 971108165 1250 971106915 971106919
    0xe0106030c12020a0e0c04210b070807050414061e3a0506030a35181c06020301080105040b1f0510050408061009060f0810020f0c0d112406 61
    0x4216100d0214060f03850160b608805891264400d14100fa4230009100340040742c0036031000c0300581c48882060342d84600c19150340d400038608010910038012342060f00c000c00100940b00926000c442c802d0403428020210a000700c081001500418150b4442c52200b6400a581320340701e04078845c0210383c5500b410440f0039481c01a192800903540c2e64080c01313802c0b0300300d800030b2400c01e051103400d41302034900309520300002d4040c40d01040044141000e80a64486650030b4084038004078050040101c03000503802000e00c0f00c6840c0704403000040e41c500256000b4101300300041a21300700740c5000150714800501030458050241e558a0406012a108100302e030000c0d40c1004900a0440048503980308030382183c0c59500c207020610841c280301c13001c0b840440d68008070800070903846070840d801c2e00805214090140d40400c00350269501c0903130060a81d076200e1204d082c50f0484031403c49040c1000740100b440800c001d01d404a150034014082c0100d2030302c030a036402c0d91007200c0c2c80001c0e95441c03000d08028 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 971109415 1250 971108165 971108189
    0x609010e030a0c020d02042d0c0302070c14060408120d0c0c12030b0105160c080c240f1b010e07050910091d0105090d0f020703031b150e0106030c12020a 67
    0x1000790741312507008d0448200d100700e81781c446217002c042d400860381e4510704040d11603250480a0042c1c41c440e10a48510680c406a40f981c503510300011002c1860300908aa64848010440025903135820481d80310a102044071080e2614a910490b2040340e24800c01881440644802440001c0380542921446115410001a4142d81200480b0107000e5840d0386100310411500100078052070030000401c6800b003104130b0f11008030060510544a0a11200510b64045403489420b03691780c40b0003410584c030b09074409d6800c0c00740074411070782c0c403084503409021035940d12403100004080a01215000d41810340d85405207003040601c04602990f14400c0e07011141e514410540081d83c43c4008003010220103000b848181403090090346c503032500d034441c030001c60740003501c1004c40c0b80041034900440790540c54582440d86550f10ba50000628014100d605505803d01d8042031072403032045081a071004000000c43c1429450140c0141d28547c000d010141d460004800050742e40440800555180700014 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 971110665 1250 971109415 971109439
    0x914090f2205010e031e09060a050a03020d1a011e020601090e0f030c06010608100807060e060705010504081306022a0307030b0c0720010c12020712050609010e030a0c02 74
    0x1a08000190541c01040e035401e00f0011030348a08008090802d150541104c4441d1400401c280081d03881000030fa1500308005014210102d401000a080c0c1c2c0300c164240585080c070b118a02c8012620f0062800040600354000103009581c0040f1403102c82030410345608400144080180d5200414030515070040c1d1251210a080e2030248502d002c001228001c91351281607080300192201000d01801c1d0002e40c10100164060240401d07a03812500504003800c03e0506001048403185e00080c04180c1100e000c208080014500340701d4248a13038020985075850b54246821700c06a520203500c400210350082c9200c900190304244d030f0b01022010540100240e50085c0c020074103003a60f69001611440c0780e8010000c1149024000382003241c4512102264440386000440407441103c07000d0b8001064409043d0002e911000e560402103440e00490b99400d0360744a28128080401104a44940091040c46503c0c24240034200780004140f01850419522500c001e21307081c1103002c041c0c4500603800c0c039 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 971111915 1250 971110665 971110711
    0x207030e120705090a05010501111203040204020d090503030a06140409020906100c120e0f060c151f090e010f0501030503071b09020d0911030c310207030914090f 71
    0x14040003400090300080f040d2a0170800030300244400d1050b540403a880d191880f00842001c02d43c07005050890401314290345881d000e22009410421260362001e1b40c070344540012030300070005075210794510380004c84c0c04c60070704030651391440d1420307000b074002d9051441c1c050042c2d403003010956000006544804a038200c02d001124031901080001c0d200c80031413421850701507401a8290b071100720a07100300071140c07801402d01805200f0700000b54250b4100328246000d440c1c101c66403a0f005600401d072190514014981001500aa607108ae410117503075642d00c01c3d020744280140c5c81202c3c1c038202c1c1049158515111581c0300d1280700001405e00081405e043c40380d8800c91000009050720705011034552070107410040040085100a50f10701038040d081400e18580064810000000a001064184030844109030b0031100308820380d81480c0c4403010307000f465030188042d2803120300a030790700c03059035190450008c40460090031700c40c06580d1144c2003150054644618503003200c1d4490131902c224052042c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 971113165 1250 971111915 971111923
    0x20c061b010c091a070618210c1703090a0b01060302040608060f0102071e120305030105040e06071e03022712030306010e0108280218191a1303150f0207030e12 70
    0x4420401e043c01e4151080c48403d42220008c100e00300040488001c000000b0340d00c244903610000c2c08240700710003801d441c81508001c0e5405c01030b03840c102e0b00140b1655a40c00b00c104805d80201c400290f0114041105a80c0000d000350041d000f41d03124566070104d0300001f519164240142290440b60040c80c042e10000c200c074507001486a40001c80300406075180c001c1c0b5036031082c4682881035080031100c485c0c0c0540850480d014442984500514618032407400086401c9240c10070241a0309000c6010104003a410038100054548220740e6074010b0303442000350f1820805040d55141d4014001c1080340d907040402c0d041c05241c24200402507a0b02d0001c1d44607460110310096054551400950125210980150004590001c40d0a1107044100288035203e460051804c0b1040111481000003491548030701c003030000c01705801c030715003c2003001d64400d540c0305610844403002d18003c00300000841c0e202e01002d0b41000e00055142050a1324000c1c03501d5400400240b04140068030080000801c00c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 971114415 1250 971113165 971113181
    0x702060d0c12090c090e0d0e01261008070e04080720041a011101200d0e060705120105010801031113060801090b0901061703031501020c061b010c091a0706 68
    0x48002d21880da8140f5044d0300a060381d10400440c2420507900300703420000400c00022030f115640e0341d0780c44211175000465036240c3c0d4030b6910240d0581010f103145880100c2e480144500d05030160031801c1c42c80d2070b2599140181561000f020f030003001c000c2c000010f09500c01c9902c0da41d0040340b01e21a6040c851200c48000c4240d2141c42c0c0e001d4900b0482440040a20250022a807001d0321900e488040a03d0b009013030721545030a00c0a1030520304031440440001e00081d00c10341540300c000051a00c00704484a29199050324201e004c1000030032000408a101d503070f1580540401e2074400c025514603500c03607483c041d0364118176129140000c81303240385481c0703548058000c02c0b5400003130042007240e003062001d203003013668032007080d5091290120340049252021210440c2039001580340d6a5150161841040980d038101d045002d000304d1401d2941c4d400001c5c003082c1c110a6105080c1001402c0c240d801c4076035000c442414041c0700b032000c00c00612818162000d54400d410425510f040901e44480207101003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 971115665 1250 971114415 971114447
    0x1a0405040e0a0201030b040c0f080411040c090315020a0c030f14042c010305030702090a0b060310080d0806011409030a14060105090a0203040c062714030c060702060d0c 74
    0x111040800781040041e0480300e05000382c90400502d03022405000a48050503100e0b400b043c9200141190544501612548207001da00d49440302009040010280c4001070b00480000341e40781030074010310502c0c180107811405131210440c541036070310b04041c03c001600c40c000707414040550f070100c82503802001ca00701c04400c950390155540b41ca50382e021101d2010f500c1d00d40800000c94007146181c11a00d0030720b506036a0000015820310301c0690800615100003000301030706c0d503242d02015039035485030300166010f10800c0c080c0504860801100602c2c00120702748881c204103802d8107000301640c1010034000d206a11501150313075110f05201080c54061071003802080c80a404141c403049490105600c1c1c143e603400c03120380030302d80c440d10303001416400107460113404404982001c00181340104400c00c000e4040925500e00e8240c0c40410004221055100240115001020201c14a02030202050042c01110b02d1400c000301c45d00403864501a411161400710382d070341c152207882801514000e0010b100 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 971116915 1250 971115665 971115671
    0xc0206090127083f0c03151801150e010804030c0b07170c0c0105091f0b2b020109080a03090b0306031c020a1104110a0f03180b06030705010206101a040504 68
    0x1c05801c082c00d151202c2d11680900e0010001604d04091551068000c07403800d0f40d00703030071511610013032400003a2080d20142d0001d03100058a00d401201403019001348444440201d10098505001e849405154466030400060100b0040041e80228840c1c02c030a4020081000b242c0e00c02d042a1006040113412610161020007000604059540102484080c401c02441030f034580103660796440300940c0700c010b01e010702d20310090603034400c0303a000c3c01140700010011101134068407881558034051200003c0d0f00303498104448190350300003108000070f0021400600c14030340252001000c41219004c0c020b0030b0f2000002080702640d0420005202c400c000108500b10902d510300a03603500f071a0103044545e0f1005403660002c0e4901071050003917004116104520b01a03400c00110384500041000e60141555107580c8424440d040d050207505900c1030008070b08a05082e0101480e101d2a54001e82c115408a001c1040c940f0024004500300c0304c000b000c4501d11444680344401600464103d40e801900d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 971118165 1250 971116915 971116957
    0xd080406180b1602030a05180a090624081605031008061009060f0302010e0904030903060501270b0616140d052808060f0a180c020609012708 62
    0x30403119414042d0071960321403e4002d2110006076100e000b8201c1e03000104a050201509690090700c1c010715400c0c00030f10b2010f0264a4841020480c0c07001d400105122140515540400c0ea044000000060180c10600701500d40241c600c0208410015650700704200070010406102c0b428200350040c03c14402a42c40d141b030b2055016000300c1192152040700fa0403c1d0001681000103480306068a8040c6d5805a195005400748090100e01810403820030010480000c049005840b919002c4c0040f96002d420f07110681580507600340e5410a40002c803842c0202a800540e181d100321028000c05900c0070010201a00f031070518902c2c0c03d420207886004091003a4940c5910000070000041c3d0340182511304072020500c60b5500d10340d400524049000070012691900e4240c282c0c85000200805048415450744010340255950744044030301c5544910000101c0c40c3c040c80b0070341e0310146079002002254103a0401c0340c0303580075100841081c0102c032840074003444490002c4602e680788180900c44030403 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 971119415 1250 971118165 971118173
    0x10b1503061c08190f08070903080a0e19062303010509190e010203061e0d0b0c1c0204060e09040c0605090402070b181207200a1d01091a01020d08040618 67
    0x44c4403a07503400c0000c060304c0948114900440c031a074080e02d001d40c0ca030002c250450381c545c2010391021040e141400305102c28070005e5a035490140c02c1d6000c010700510003461409101400e591666011140c8040203500031910091082d8290f0341140e804072002e04031a16444246200d0080d603401d030905050410640c4113600314150011801640c007500d138810400158400d00c80d011800454056200007503101c3c0c4004121003010803a001076035020480d10342220b2060030782820350241703400f01c591600030400f0408250000600303d2812802e507140442440e042e5030b960001d544501a900501c08042040030f110b46640c0e05a889a540c8078919036618105025202404a24550080091302c00c00765211001a030841c251400103034408020031a05d803002043c00340c82031036500746a400901000c40010140e44410b0f06050340200c4034552a015410010b0761030584030200c10401071009018103480c150b90340090303003040c4604645446440754480b4a0700e81d004c0c00310341510072a44001090044140 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 971120665 1250 971119415 971119447
    0x307021e090a0204180207080706091119031a1e0408040e0405010e480307180c02010c0c031d130b19051507060e010f0e010b1503061c08 60
    0xe81d00385c030f03c81d54403107012400e108207904c100341c0d00521465086c8000740001d4140c0d0000340704188502d660410000800d400b14411500841c5110b0306447c00b100c04103b0b00601e8070503c2c0025040d103070100c46074070b44040b402d03642014007040140ea2252010001702801001c00c10384000c2d050640e50401281024280503029081c0c07542d64450340d0082c0c00e801c00c00c0c080b007030810344404140044014503100d400602088000141440c1306004e0b12000c4403600c0782c1d50103201c864040d01c04c0740d2680110340140a0340004940600007180156850031300d102200702e80041280c14160703410302e0701c048003180e0103001441814181685603002044101061001d81640d08002285141500c0b00b000040001610410019081c41165000100da05a03221a0690080100300940c081c64000c5018030f89908040c0c2101c01aa44040582c0e0703460030f01440b003150038015400450011100640c2401c0601c505600303a2002404003841034503441940040c801d5000c0c0c10243e42d030342102185d0340310b6822145031515 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 971121915 1250 971120665 971120669
    0x9190b040b0d0f05100b0a020f060406020703090b0915030711010e0f10090b010b0a1404030506071e140310030203100603030e120303041b08010c020a05011505030307021e090a0204 79
    0x40c99007071103544840c00003d8490180700d407404491034030300c45103081d000c00030a910a5820701d0460147c4024459002010000d0301d005502c20400183d941c4100e003002000c1542c1c9801c0228800010841406c03d6130310b20049402840880130041c0c2c1d685c403461000d56003041d003444200e82c25400d1800e203000302030011a696081e90b40c1541905e0320a9a07101d058021210040e0000382840320b00c0700148070346010040a01811550760030040c810b00ca1707130301403c10380b034001740d10842c0c142c0e02c4503040024095010042039055071032003403032070515001448050030903845c02200b540c00860101c00540d204440b880700000440e005801e542c580a00d100c0041d0203802540800d40103e0312251b0549003d003800400c08501d240008040d40c10b60301c0c0d03a41c5000001c680d20712030313840c49020550040f070580002e02c145000c030045030b0010300b084043e030300c0d140c0d0070340342c40004180040c0c3c4da0007810031207078501104980c10a075040754001155001d00e440e100c020304000c1282c81c2c10419000c100001c4959903401001 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 971123165 1250 971121915 971121937
    0x1b1810090602070915030809060721020c090705030f1906060905030118080a12061706040b090d0903030513030b072712080d0608030a050d0b0d0809190b040b 69
    0x80303626107407881d0f102551782480304103d07440800382c4204040f0391008054411031100810b0145030142c6a00ca001248102c07000003000540c160400300262501044080d004190a42c0c0c884403918002134040c100d800005d1a03013409030829400201941302e6441400200f600c014802c01005440f080000c101e9181e500540c2e0185d03192440030b0060300f00c2c400c00f110559511a86030303490a00710300c6003210607400300814054030944445000c107009800003d0442c1480f00b8500500151400c0d09082c0320401c005007881d038254009540b44d0303045540c030000305810703203400d410482d80e581040c09860f00c50359055840640890080780030b003c00340d54080c00f82e41040c0f04120701841026803030385110050340c552344501d00991305103506100001c0c055030090500c0d05030914000030314542e280252800c42d88175482420000c3c00004100300013080c0e0388136092105c04180c8191000d54015552061a846401d08481c8101c00d11050038416000c031110172009408902c5001b40c1311580c072005d1054a4000d0f801000c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 971124415 1250 971123165 971123173
    0x31202030a02120301050603070f0905060d0e2109120312011d010801020f0a0f1709010605010914030a0809031c0c06060b0c0d030e030f21010b031b1810090602 70
    0x4820810f00d50540f03041c0c60004048500e9511b400d0341c2503520f1602907000c0410700112980c000761a9503101c01604d117080355104045011817085080310308101c440702000d00548090180102469452800d03120000340c01d039421480840d0314002c00f4074502a0415001400c02c10700008039022525032100a2040380f0608003a400741d03203410b04242030b070054900c0b982030f054041c0302c81605644280040c0c1c510030001c0c01e000408241c030082011101c1000c1303c14010b03ea445490421071035900038800c03401090000c0c8071103a45c4501d140003d071161910344014080b210085203070011a40d0034444400b2564501c0d6400114560900780940101b10450083e65802e14190001919200100c111207224038900003501500d02140d00c1603004280c0720201006c280f200b4040309400f80803020051011280403400d1800c01c101c403003600701c4030340c905800400320050207109018043c100c44003800007100319240c0241c0c681c4501302c0c40c00c501c0000c207100c3e00d074080030741d42e00c901d0f660707070400403d105640c0c00d41c3c01d030f07 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 971125665 1250 971124415 971124433
    0x5100207053f0a030e010903120e0307081203010510030e100b0405161e03020d0f02031b0405090c1602060301060804051605062a0609100b0301140606090109031202030a02 75
    0x2d0840c001c0030280d800300030f400503411000028807640006031042d0050504610854032070701c43d03d580507001503a003c01b241c2d201100700e00901d01007120304018126213005002890030032108015901041c85070300e005071007104d80c141000e4040c3e0021005080301e0811100d02c0c21601c4000405480790b004114011841c22001c900842c80c1e0305000100c880164079041c080c1d9660074081c0f110800842100ea0030103500b80040c10001400d0f0180d500c801d0051140036132a070510341500c0c401c194204a5001d040001000f04101584505035215401309038941416240ca841c1e041e0b0f9550381d242518000d41c002000070000c550035801407038407401240524100d03500b24802d401144030b00c5030103000302640004103021440c000041c003a000c113007650b064202000d5003c40c40310f2007482e00c001600d244c00701d81c2100100785114441c2c1d20400302e50310812030082c403d446041c1d0280c40781807805002030b80911720010308150107034000d80082d030046a001a0440c101804020022349942003060200b0040c007528070f41c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 971126915 1250 971125665 971125759
    0x1a03101a130609050d020907021c020706090803071109070201020c0109061d012a1b030f020f010b060d1a0a0308030907050604030809120f03030a091a09070510020705 73
    0x3c103030603283c0140c640752000c0d030103400700a0604070040c03002c0114481d015000d103a135861a601d07503030600d003280c0060074032a04015001c1c2c000f40c0c09800c0208503600a20180c408985130006044021505861a40301034444802c124068868448220350075030030040c400c410441c0d158410000a509a184a070107015400421820b803009040a100701ca845922032141c258a2850704607507000c0075007442d1075030001021110f05d2185d080e0a0a4010800d60540200f81da031b0140551145040390b02d000304115140e02c5e0000f003250090301100d07194591b89000714091180c2510301c4c2001075100521507600141d4a1030441510361086880352803e00880d0340000f15410300c20190760960b640081607504007040c5109001d400030465105040d180b06056480c0c6100e10300b80020b40c00740c114903e010403124107a040c264072210040964102d02c058200230009842c0010403814207841080f1002a000491000c00300d1815045401265000038111003003000c0c2960100c07000b00c541d09094003c100b07400100c035 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 971128165 1250 971126915 971126927
    0x1703090c0f03030c0d030c090e0a020c0d02030a0815060c06090105150d0b010302040509010b0a03030f1d180a0b1c1103010513080a030207150b03060606041a03101a1306 74
    0x21081c2051780c09114040100d030300a40208a4020310340c50030806140e50317040c0300c85040000f99201c0c1c0e940c60380020003046c7c441c02484042c40c0d40307449000952400c88080320092204e9002040e48441401100c8020415a5014100c841080383c0000300c44540c2052401203009010580d151941032038032020a500c141003c00030600ca90b9006002d518071a0320395001d10000d0040146255415540c1c0c2074091880ea417451842e9010714001e581d41c410545000b68060181c10581180100100440304400380640e600d101c50507510584424203111906e84019035000b45c0050781413554803510070540300007040c445107000007005000d01841590401100285803c0701e01c1a01d501c4030384140031390000f0205920788020055400b551400520b0229107441d142c0b00c0508101d2004c4c1c8042d1583c0041c29545810080d80781c0002c01281d01e245041c0c030b000c1c0100c001030724000201d58049001710028810310a6421103400920a007692002c13a1030040c0e0041070654060601c075160314415101c00f040c5944112 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 971129415 1250 971128165 971128177
    0x31503060709080c0d020a0803070c0e13020a050402092d010320040b1605010c0305040b06040c051824190e0a0918020d0507090c1b0209041703090c0f0303 68
    0x54091301c8081441c0080c4282e00d48030f80020303604521400800502080c2c10001810058000d0501c55031036418010064504000030b0014000700100f6034114002d03981700c840e00700884408460050b5180090b00201d03146011100b40d1090000d003810b0582c07104080e000019070202400d03a0104074010b20640d041d0340d41c00304049030040c41c0c24140418045030801b0002040a04864004c810071101d0581c1ca0714292480c004480002940380d0051204101c0d021031944d40180d421030b014049080d1f070040080c036034014403420f0008002031291207402c5072105032038065030380c600709204910800d50b03080c0c00c0904d078004107800c504204101c40002c0300d203120f2618022144030040811051138985044d4001601e002d240520515952003038050040e0303070750042c0031001841500603142d40384c90f2000100449020090446c28800000120308400c1c03803031510820b14aa046400384100d0b1070350b043c07200700c040f2841031803038180743d0000501c0082403001a2135040e801c405c4070042c281015200070701d03440c1d000342 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 971130665 1250 971129415 971129429
    0x90c031b0403050a0206070309091a150c12030a0f0204080a0308090d0c0f03030f0f0903030b03031206060a0207150203040306380f060a050c0706051201061211031503060709 76
    0x140da04c0401460840014803045010303141114540d601d800c12842260920414002c3c8907120700800d509601b058220034441c07400d9040840e0a00080c500312030b445491000b010a004040040010007000082d401003299003000a011900e481d2a05100c681d03c40d04071200f50301080d4054000360702c010300000c040c980f0240c1ca81c0d030760403503800b03d0342c0d0042400b8144100b1800d040d01c5115441980314203101c0c2e40c0341054007440c0402d1641c0182006000c03191401a614000d4004022591001c240d2038440da0300320303070181c0d44c183d030383c80710404100d00301078860f0000e510b00d2022020091016500101900580e4002c0c0410440c2c03500143d040080c0c224170b0300d50340310051401d08030030a00e640d00e210329400c41080174050003c030070700703007000102070340c0c0b007400300303070b0204802088a40c1c81280402038a005480301d1700b0814548130341900048411101486030104022000d90f502c1d00c0d0840540005814501c20f0940c00d490b4100040c0304010102541c080d075009120f4140000c100078070822a1b01c1c121100 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 971131915 1250 971130665 971130673
    0x30403080d05040609021c0b010b0a051c0905010203010f03140c01080411180a020a0e030105010540020415020606090718050a0611070801140c07060902090c031b040305 74
    0x45116000142070014802e0720a02e40da44243c0c800360b118141c50006107107e103400d40788000e0740751400300031511060b0070124000da014000501c8440d0000c0890348105a1400e2416084c0c0a440040f806410302e500d0080440d4008000060340060440300b603002e0741c1c8112031841c040155095110f40e100e05041c80f41d8002000a0007140100703000e100d42003190ba901030a00b410000103c8800c80c4000b2090703d0340c88440b40e00040034001568084440f0380001022030003070005526100010b201100c00c401e5200c0034912413588880c070243d03002300445618803112620b4a84a44881100303000350014401c0c43c0000e2101e1204004403440450b007603204200041c02490f050f03e07001011070b8076801000c0380c0c1444940041010074159195401d030350091006540740140710400c909040c1c02c1c0301c65540b1400c0c05a0500d0081060144200005907124101881e855141e401c0c2d410a98081e0000d214041d40190703881c0300384112140c008004500c91303a00340030145108007000320210014821444040e1213908 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 971133165 1250 971131915 971131927
    0x3020c0d03020c030c1c0e0f03031e0d180c05040504020a090c0302041205160b1e0d27030318170d0e2e060803161415041403040308 58
    0x4001d902824003403800e00100d9040c1401c54004d2840c0449406c4604281000d07141d207090307055030045202014042c2665141500d81034070380440e540340554900120038007a9840545090b040f903800391446806040c2c0d05200501c031aa9540c4070310407480b80c081d1403000d10701c50003040c2800c1c14001e40f40910360142c0414941403030042030100030541c44441c801055000c001c00203480404030400080d0f14040c0020f4600011400c007244500c00003588107000c91181401118550000802401000120101d40170355400c0b0341c0b81148001d114075845c450101104040340001c0d658601607440110384251400c01030744143c00f650303001c1c902c452140240740031040c1c82c1c200005c1504a02411403140ba80c03c0104404d0500c038040c07402c013003440300d176003004030000402032004d1204c5a003c00d081465448040010905000d10143c99201d00424003600e407180e04882030800482c4a100d0b560325080e4400e45444984039200407490b140c090f20141ea1a41d42c001402d801e58201000321001c4950090550f4500701c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 971134415 1250 971133165 971133167
    0x25031206170a1103030c07060306180e0d0804021c030f02060708060d02062d0c1b0d0201030b030a02060a050d0501090c08040f0c0906170d02012903070312091503020c0d 74
    0x151541d400e4a130140001c1c401c2e144903031002c0084102405107500c001c101c4508040d5000e03010b1100c06140b080040c1003000d042000c03480400d04005103c09417a00507010360702d90003c0f420001006811000d01018080340700103250b488458407241400f6035083d00d01c41e031103081c03049401120540d002c07036200c1c3d001d1300768000500d0700400a00341c0e12030b00d610f20741103060881102d02c16000c4204071102e00d10000502d21078104010300100008170110140d4003200c032800300c0410320384600340800074149a5179440455503590100407040585600034241503031080e00e080010007940086480c070014509010010880448901400b104d10302255500e00e1141d0b510745550400700034498080d1080744c240e0401182c444654001e2401030401c850541e4100298850082d00c0e00049a4414046902d003100310150303412425101c60b0a50300c030040030300724100c504001030b080c8000c0d13600050082c0400b80300f4031081038011514a0888081501c24409903008000503800e920445a003c08960004409031140c2 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 971135665 1250 971134415 971134433
    0x6010b1b15010618080105150909030a200a050610050415030506041b032a0905090d0e060c0f06070806032407030207060c0201060f0503190825031206170a 68
    0x1034001c0c2c2c607008030540d5541c185003161000d42d00001c8e0a282401802d001d424900007058000c0315500045117029026080140b02d40031035802d46400c44a4801010059502003100201d00c6030403800340d41c0b245c105003409070310445a51083c00d0103503003000c04021180c48082c80c0b160480307403c20058101c0307699a0341d03201100d50480040c62010540d03140c02002140001d4441800b29041080039507010380700340b1001000325004d501517000359080c81c007002079256001c1134890350003070182005c0580c00540c4000845500030f58a1080461107040482030b132402c00001c8140c0a000030ba102e884c082d868141c00e05841380c001c2d40040c0c41c0c4044403003024400c4840d0355159940000603140060801e1100e68810040d03030742c094410b40050791200f200348117074102e8941c00c400a0070210020004501400d90b500400154108054918400840c0310300030355102c903001449400740741e1a006d00c6680d440c50003400300c0540200c0412030614000d80403482c1c2a01606510034820040c004062440055440840c5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 971136915 1250 971135665 971135687
    0x815040605090f100b030a020a0e06040312030c051b1609050708040b040309180510090c0207061805060316021b1503100905010603020a0201110a0503010b0f04030506010b1b150106 79
    0x80011701d541c0844007960040c15203500c00742e0340e4944004010f1008032401c01031403080d40204010000128101041d030300740440e0382404589050400c8054450f4028142c286069440341040d0340245400420440c0500d803d6003441c0c2581a100c0b881d02c0708840e412904a13000c03811090105000c250840b4400f540b02d031007440c00c96031041c0c80380ba048124005a078070440c080b58948051002c42c40400110310041c180c031800810a05281e400000d64030046441400d0030301802c5103110b4001004400004041e100c00340c0341e19543e04000c040c065000d440d0307503841401070007103484031040e03030005076a0550100401424410031030380d0a4042c403025840946000e12040300c030500000d410b0154001c040c020005500d0050721042d101202070301751079400454195100007003050b04000d60300142528151012045c080c0c1e107503c000040c810940c842e40e0005031092150400007d282c103140310040006190300c3c0403007060403146002c607503076400a2407028004810210014000d032485504142d032 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 971138165 1250 971136915 971136931
    0x8010e010f1506140705190f0303140f0a0e07050a030b1611070e060f030f010c091d0c091c081c05070c02130605040e0706090e0907060c020d120815040605090f 70
    0x180d600308481044928400d4220208c440030001c64592051641502c1141030000c400c1c41300800c02e00d0080c01d0903071408001022405001e80d92100b0040144082204901070031003e044640025201d0034605208002162103541c004066111290300510808072175141c400140300030101c55040180f400c80c5150003c1580f81c0004414007102c2296400304405103050116800005603d80410b10003807078240b007078100410314044080c01c1c0d20014440484181e204000c41e407402e44a4039041c000071003082403e01c01600860900c459001880723000c9009100100700c480c904c0c0da02a0101080409440e002c490101c041000b50103443c000d401c00300c40f000c1100d400840c0015004c2c0e203640c0041c04440070140800c0c0c0baa8400c0d4818000380ea0480b0403640030300402c05280016180469046e5030351500c03805500d08108540d4030010854981c65407210740154084d20810080303044031001011018100c402c07403407691644034038018600b001d1081009a030405001941141e4401c50019689c0902401041d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 971139415 1250 971138165 971138173
    0x10f0b1213060f09030e01170a05090c1909061a16020406051302030f0f060d08070813080303090d030513030e120105040b04050c01091410020708010e010f1506140705 73
    0x180010349284560f1040b000b546800054151603810010321000c00c10100038180408451986880c42c0e0b4076030741c0c0d54000f460701c0004c1090f590726141981012240151550000c8950001402c40c0d070001500c103091b1031540508001960350742204115442c029120608600340810140d4900900e122482c0c403014005840410318540e80c3c1c020030224607001c2d8040500d294080309110560f0215240c3c51381040ba04c9807510b00074200900091140703c28200c9c02401e140c1c0c0000d4070000c01c2207140c00d031200d01550388210300800c1d80d1118119200d034412514200a030007100741c0003200a001c0c1c464a40074604201045136000b0166400341c961000c9151040e6100c0710300030200217244801d01030070784240d1041f0f03650085824036140041ca4060070341156410b109a0300740607c256900f401c10b041d01d091040780d056aa000d00340c06c1c180c2c18a506a04440a6542040c0518a06200541000401407184c40c01000300c44418580b5148040ca0350103504002801500505509640ca40103400703454020000c0ea = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 971140665 1250 971139415 971139451
    0xd0312021819050f09150603130f03090303180810020904060f0902040f09090213020a050c01061403070b12070309020a1d060a0905041109090a0b0108030d05010f0b12 73
    0x1e01400402c1041c089000c2e0540e1081c012403c0124a00d00d01344001d507042020b505117030100f001c01e5425400e030903001c0c1c407011000410760b00c445070411407410f410043c4040504500d04001300340580c1400144d01059505202d4074044024078040012108110050700340d880804416501070b512001015a009455070800b00700006011206070091161310801070781c4900d0400d08103106e08040d400128081c0c904440e01016031a01d200c0c0b0b1524075042d44005a54681400099505004025200049600e0980d0116200744120308458085004600b11401c150762071a00070b21500c15105000c107a0b00040002c242d07498041d41014914501c001c0c00400704980f1035401001e1140e00200c0d11500d0100242800b0721418000e101e58060280513000b880145069211503070210003406101d80102048000200c0800b024071643e505141e00004821055070342e00c2c08255281c102c030031400801460030700006080d880d0b50212400f12070304001d101381840d20881c01c140c20301f50020507403d03c000c60f688003 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 971141915 1250 971140665 971140669
    0x312061c11010903060f1b020d080a0c0306030f0b0103020f0d020f0d031103030c0a090b070305090d080d0c021e070509070503070e0a0620010c09030b060f030f06150d03120218 77
    0x1034140c0344a1050b070005007c1c0c0d5001d00d50f001090520101d0400d40d0011500060010390152078698450384403000460074000c80c80b821001414540c1c4064510301c1a004003a08102440d10903a040364000c55204001008103403c011071011078145c001e6025101102c4100c481c101240a500070300d0090a042c407058075004185030455004549104c5949800595000b00f10f4120b104000a04420101030342001e202d594054002c1c420705c03a0b880c2c4500c152100300020000340204880d142c0d0035429090041c1c080002010b55600d845003098000e070030310040100825940058903108036440140495640d440c0c1c20303c10b541c2940007030211010000440b80c071452a450707440503040102001d59035001007501c03840309214002c1500c907400c80142d041900d0300d010294424880b0307081d00c0d00705900c240280c0b02d42d800143c6000300d9800c0c0e5601070007010b2080d00c004070b020030098410341404007102004c0300c545080011001c100b070700080c00703d800c4814034200811140d0242c80340c11460f11341c5d8030340e1038a0340d00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 971143165 1250 971141915 971141921
    0x503090705130b060c0a17070b0c1305060c0309210c13020d050c0903150903091306090501141009051f201c0309050705010f02030d05090312061c1101090306 69
    0x1748080039482039120004018130403485071301591902c0d000b00d0800880366180d030301034440075018590201d40032400540364030b802140d1b94002c06004103982e070fa0b42106900c4940740d80003194058440c1001002400c41100c1d40f04441b00c400402c940902030410084080080d03410040b003403030a4495090100c401d442d0424411140250540d801540d100c2003410304061070240c500081428210554050129103a4004152101d0342401c890702d084400b0f46c881d0301d900400183d4800049a420a000001d54043d1000708280080042c1d0300794102030300c12003050b120300f01140315007030700502c01110341e241008507200c980d6682c881500d0000bc6001c0744645000c20320181a9603c13030380d5009412104100700f100707204510301420301c1c101400714540b070b030721902d031902158031a030340c140a000d200d842e100e176100780b040300c9603045001c00410460a1220607940d03281c12511024a0450144020642e50300d484803040002e40340c4001152104042c59560741c56800311001c41c54140f0550f402c011000940d030f40 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 971144415 1250 971143165 971143177
    0xd02040602011b0c11100c0c0b0d11040308031306021902100c03180204020d060b0307020a151107062d092003060a1a040f1b0503090705130b06 63
    0x1038000301e004144640404050b0000903d03550601c09008003840029080f12001c1503051000c41c0d00310380103404c000d01610011601c00c0014101d6400002c08030b0a00110000340101ca89201d1003084031403503514110400384500e0001401c54101800052100c48007407400d01b0441e0b104500150400355034031410840914920401800741c1c0200041030303510340040c45511010822446e0900038003060161100007130700a203901902864001440c403608102e25000f5000410161142d81c0d030741e10b4a024001d403624140b4208594219049050b00424216802244e281c5c002e075070301b11890f156140c0e83d101c0041c59000c00c22505c40c030404141010746400003000d000f81d6840d844000c9284202868901c091018000c50351103c1e80c40210b0600c4140c4001462991054440f0000141d0b0310052030820b210031900300a141c2c0c1f0909000151031500042e40000c540c58601514130003400d007446030191420b0000f01e40a101d550b010200800552920304c590941c0f28100c5040029201c400320081281c0c1d074021 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 971145665 1250 971144415 971144417
    0x201033c050121150507230f040b030901020c0d0908160b180a030210180e040f0201181203030212070903022d04020d0903080906040209070c0212060f0114031c0507080d020406 77
    0x40789110f01c02041e5007c031210380c1c0420104600d4041004045105401140107945505e00048000fa2400381d095040300d1106254078115500d403001402c0c001c048170142d020310981c074021400004901404001da02c800d40780a04102403c024044908028030075402480310b51005501d000000503840e01c912000f101079440d600c09210181c080c4900501c00303031960140103640d11502c10000820b913210340c54281c00703a092030004810032400c102e080910115030060300c48410b076681c4120400d505a8020300300310305140c5111444e691094402d594221071351001035045421034101518200c134055140c54007103079001c582442c480a80002c10103c0c2c00090000c070b8100d60b40ea0204003403581020505621400e480020714091070a279000c200c0c07040010f0801000d00004e000900115903d203d241001c003441641112071310300c0c0040381803032020020720641500d2210a40e410029080200e410400480035031a0350705801010b6604030303401d91080c101a1141c03403003403142e400c080c840d074001007000f0001 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 971146915 1250 971145665 971145677
    0x111507050d080712151e05060702090603070f0905071106040c0506130803030411030115030305250b091c0203120414070302060c0709051e0406090201033c050121150507 74
    0x3058050004518103d401c501c6486c0075940801003036580004843c4019030594a040c02512094003003441c0c07011b950001c0c1c55131030000e08003180070f1345070342e0240303100c1c80d00340e601c1c822a1309914809a444440a840240440040040c24030260038904002e1030b10f61083c52000411030f55800e151425074005581c21a16154555031110b090b1a003401040201b41c50341e07061040a0740f1796074001d40a0b21406181a9400084030190b40100010620807442940c0010b03003681640340c114600b41d02c8407404108009a0b000c940c051101072840002a0307013041e20b01c4960108503031034544030000310450300500448140301e811b80c0400180c4491380900110b10070b0303100820785642841b400f072083d128028030000d41c081c0c8144888051080301d0104a400541004c000241e0310348500040700500340c01c00c420000c1441c80b002c0c01001a2490340880c0c1140400361545105840c1000804291070083c454014040b0341040741140480e02815074040c02c42c410000c0c4914004100c00e5a020340d1802c4840c0808500 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 971148165 1250 971146915 971146919
    0xb0409050a06051c050102210604050a06180203060316060c0b0c0f04031b0308040b04050a0803090609091e0109020306010831060612111507050d08071215 68
    0x2116025194124070081c00600a250605000ca000b44940f420800c103902200300044081c070800794111200c030440402c1304020002c000c1d1209041c02d209079443c50041d031801000805180140c4590004d80d9891203900380401f841e4208a0b010750000b604040d0301d0b015564900040c160b032060040010302280c1c6079580300c4080c60038500540c01b0010840d04482c1c1c1d00b0060900b20900d103e04070b0f001da80e80a401c1d07020b56540c02e50420b481404030f8200030800c1d4000078003c21141c401102410440d0022600e04082d59151100b0544900582001c282c0200c01030088080034a4503000300c0d43d00c03d000301c00c8400c00d014842c0c3c3c0d81c0d890744000e038840d844180e07001043c40131950b885905603901190082405500c1011000074811900c00d0300302c1500ea1480e604060340401600e03400ca80e000f81080552810400c1e03444c2018440ca004100741075205a0407142c5100d50030a0300c805407080650844090840b001c80400151280880205030b50100a00c12200d100c010740c5600c1003012a404010400b04054 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 971149415 1250 971148165 971148179
    0x42009040213152601050904151e180c0e04020312130e0601050306090103030e03030f1314090c0a050a050c0102030a06051302180f1c0305090a170a060507180b04 71
    0x2202013003000c008603040304101c1a00c6614402c00b2030445e10196010340e203542e140e003890752000440300b0031035101c80d060544250800b085854482603400c6a8a0b04000c901c418000703010340306002000c000c0c0000e044a43c104030036030004080e140d010b8000780545002245000c58407040d60301c401000c1c0900000c01340c00f03124016800c0f4404e58082c0c0c0a080c068694205200010140c1205101c020100030b01c0100801c0c06481c140240c43c1717200444160a03455208586400300104c0e0340d4000c1d09510071210f05645011728191852600031280e50032a075140a171405e030304881c25031141003810203101007085642d688500074401188101071040001400c03d04241c100002401442c400c2c41920340144000755400001040da004040305c1111140f40c0030340c1c0c0034081031103802015642c07003c00740f40c010300c8024960480e0003028460f008803903d000e01c03620ba01601e00c00546441c50700f002a4884014040002d405500c01e0b90008903d0610350240007003e0501c000308401d54001c0b0b80c204001007001c0082c1c1d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 971150665 1250 971149415 971149427
    0x61e03062d0506040b1611030a060608011b21060e04050a0201110c0a0e130b100f060c15090c03060203070509010e030304050d02130f050a0605010e04200904021315 72
    0x1034201254030f075242510b03129241886001e6808210110340100d0728500400002441c400300d450350142c2550110801400d00600404440c03103070000a5080c0800032040700c0070508500550903c0d03440d2581c40060141580da21300c91030740695840b40e981c40f100070440c0300c003050f18030b486940b04900800e400821440010b0560440121420480d031201c20030340f44c250364102d6241e055803c4250399440a40d240b43e1074075440340d040d01001d0700c00000c010030302418895609451043d55404001000e07060f5403850102c8000203000c07406811400b80c5604401c0002c69904050107803030044055008160300c0b034440350f04a900035201440450320001d045406542c0004484403c100d0440c091810545410003203014240348a90080c03040c45001c031207400031040c6521800074109180f20402c800c1c41c00b500c4060090115000315404150403507805806407030a4001d021510080343c81d85401c4200103002031700560407071251140e204e6024801080464520086170340200000b51500240511000015100c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 971151915 1250 971150665 971150669
    0x60414011815020702030a020d03090e1521030c100213050a0305030a0804020102101b0809010e0d1d15030f09030f0a0f11161806061e03062d 62
    0x800721542603400081280103a05190000a401002d60b840c03400d440081e041042591000758841c100030006818154440005401d440c03800385202040e864502038a528a12000320091303204185900c9000110b0001c10b204991600742c00490381840c995410403030800038242602c01e9006d40c04100320542d05143e48042e0020f04080d03405503007542c00c6466641d1a80326849401050000c1240401d045910030031021807171081581041082d0480b59840200e8824503108020004540c540422818441032007900e50291501d00240100c0c45000070035511181075880d051342001910b200c0d14516254081c942c3c10445900c44042e6881c40d0151285a07400c0000d40243c001e81d10910800800d88058022206101280c3c00d01200d1101441003c441c00340340120b0582480c0100c01e000f05016250002c1c140a40b01c6140000304052881d10309001203030481c0c41000001a14880140f013118030b61405280203102c540350228030651035150000014032640291407031010790450b9016070a070700d410380da00 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 971153165 1250 971151915 971151941
    0x305060a031e0c030213060303021b030312180f0c0a0b070507270f020703030509030a090605090a0b0c0607140304030f11012c062a0d020c06041401 65
    0x1004a0031a01d035040da084041c03081c01c18406002c0110001c1c00b060b0039a04000b9503005041c158a40d10004506018100c0c80c071017103000d4814402e041d040d1488918008200c4c0d00007600030350824081600c2110358007800307000131071054080151020440300502004c807052b0001c50042040011040511228100990003401198018891040051800f04214023262801041e5600c50800b1880c28103007a1440c040000d8000d1424501500314612500600110341c00707070310700b0403207a40c45000054507031041441c02c07000035109042c240905400340000d4443d0440140c0040b110350b4480f60a80029809804030401560200c0d0030010031560020100300c1a010007035442e4258105547c0203000540c10444010500002448055001d0001d503c0800c00310040e1101d04100c00320b0748201c0c2d1030003074500340080d407902440c40080ea4030300e00142e008410b140000c4480801100705200c55555030002d00701154120740801065018190402816006e140a506529420020900e41608483d00000024 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 971154415 1250 971153165 971153179
    0x30b090f06060a05101d030102160515010b03010b0f091305090d022d10050109020d0e03040503060a0213150833040f0e011112060612040609030e130507030506 70
    0x1010649030002c200c0c5c41d030121420b104000802c00c807540c89801c038522154517019071001c83d01e004c0601c61544606c40d076078090801e40b000e90000c48251400002c00b40140201280100300400070fa00003000285003032907440c07a105040c980d07140b0029041c94503200c2000c24460301c0308248155104217100e00c44103981240000e001040c80f4240c1d20f241d06032400b1651840030080070345481070301020300850304281d40d0380404220942c0c5422944000b900300b2950b94801914000904140ca0b20000455055403c014010015030384e45044040180d409503040814402480c0c4e0000b4102c2c0184150000030031607a2a0390a032440c1034021132240901402001200403c00c5c962901d0b2000c203030b903c401000d40141d030007140000c840e140340006000b106034590215881d1105843c10580100701401903a020350150381e900340c0b101c0302001158080c00c0303103407001e0411000c0820f0016820340c1c03003601c600d0301c60700f44950000c21460000310000f90880030701041c142c031042003020155041c490140d01480494403c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 971155665 1250 971154415 971154419
    0x3020d0c03022505120106171f1a0303030405031206040b1012110f0d2f030405070e0a02091003050c0a0804080d02070317070309030503041209030b090f06060a 70
    0x290740e0846a03405460410021100d901c0e1222011081e002402c400f8081704a56541c0801c46402410f141c4a182202d540c5071200714000c1801103031004a24042c43d56240d07003010107141200042003001703008000c0c59084001410700c1c1e141803015503c114003610240d40c03106082d07040780103040c42c000d008910652522480c0400b640e00e800700c01303241d1143c0d8035042148540d00032480d0010700b82c04a180f0070340d81d4042110103100038503000070055120012024802d0210407042090110200c2034040c00580807075604445003100304001c1c59025000e60100d81d00c0b6544e0780d0903158203503415610004603640000d64004642032040c01c119004601d46030401252504120481c3d403800303005240401c0044807408201800303820815521602c900031401c640e900024507024100f40c040b02c00c01c503041390003000050403075802840341c40069a0035032500d0386035540325591003101c8098502d024091106004020010618000700c0c01e1103000c1100c02802140003600b03669281c09002000d45104001100c41 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 971156915 1250 971155665 971155667
    0x3190b0c04051e030c032d070e16090b040b07032304120c15020601031a090a06020a30060f08031603020f100c030c03180b06030c040203100303020d0c03 67
    0x1c03118014920515440415a0400005d08064134860220382c9845089a407425046030700c1007402c0c11060005c1060b0101140554803a150300c0e0901c1140030b412004800550002c0d1148510041e0705514034003203a4075511380385002c02d1500150404085420040340c2c6004042c1c200c208807551106204240144d59011000003019200b680100d0800260000d620f2040042078a105005400c2c01980300d02009107100000395120b000344011b5803031145102d10b4119040c40440e455009141d81000f03040c0038452616054040d500400915080102107544414104040a44000c1c0c040d15006c42d50341414210030f01a046d1011504003c40c41034408100b000b8101e07000003100ca40c0301d41451054034130102801c00303134140103040b800111203001d003488411010b51070368441a40c0d034203161010400c1c182c21040442c11684005400c1400c50080c080340000716610361102030740090000c0464510100380d2000c5010b80e0015034450490845102081c810503406009200e403600c42403410b2601c050003610 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 971158165 1250 971156915 971156929
    0x6090c14010518012105010321090806040209060a0e0f01150e01080a180f0b090601091b0c0c1502150603060c03010905060f1005030612030306130f060503190b0c0405 73
    0x42c070740c0c18010008880810740042c54590b05c44100300c01c00c208030b50340c1d40b41031001c000203415030030601e0048414021002240102c21000603035a2000050401c5e50b126400d0292820005e0401c590008242000113016910180f00c188101024000e0303d4040d49000500300105510b4161030050200002d2050f007a641c1c01814150b006400034004120f0602e080d20f070144110041401402d5240c00e80311000038044d80e1165036000d032203040304581070790b039a8940c510115500203c541a080003901c0b161070700e00b881050001181d60040c11000c1006640e030300603c00c54405070003447c0140e080311841105584404c400154000c1d001e4025200328078040d141c10740075102c14059211083e6803240807a43d01e8484580004041d0000b030490011418450300c041d066420846c4c60512a10031001030030300040010055034010407000c0c1034008568404403203074015000040300c0302c43c210b030750300030002d080da400304500020401d0340c01110041807079600300b0500005009007e0195110104010440368884803 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 971159415 1250 971158165 971158207
    0x10213170705010327060905030a080708090d0f1d030f07050406140a06050706020c060a060e10060503060402070615090212070302030c040b09061c0e010c08090a170706090c140105 79
    0x1205440039990911b4140d000300b001c1d040c041d20511012441140f85600400704900408650702c6141c581d5031400c0885903900030368200707140012a08540c581c0d01c2401303090201124040c0b84c03440c00c148038410020a15050007203401e0034403503021400810060038981701c0c10b0041c00035008414600352095011888074001071140c038040080000349a0306001584d81270302c0c40306440e481624492f06005c00d0701400f400302401403044021780500411038501654044d981180d0064440c1c41c1103a40d010704000c000c0d00010015101e075a220010110300d00c4012110b030780038120f000380041e183d50561050760050080244540285441042444030804080055508a40400b09210340da144410086100703406075100450540d1588007240558028541200081c10105c00003000131815601c0100c42c0524280c40a0b2100d40203200f0503004214407000c43c0310391a842d05c002d5450041d4650360f070b508442c26540141c40c0708c1c50003042486844a031700c0e40312031038100c00d10f8810300f003013041c500c00d04c1002e40c81c0c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 971160665 1250 971159415 971159471
    0x40b071115270318090a0f0e0d1106090a020d150e010c02060a060308090f0105070f030c05010c0c2316030305120105040e06010306020c0102131707050103 68
    0x880440d005250302001449159140c1980c1c0c0ca2032814004a441d08500700c440b40c1c111191904280041c10782c0d400000e403001c40a204c1c00e024543c100c900103000c8020f9002c1d15849601c2d8580c110385420309050b024004000100100504008104d00d00081c03007a2a03541c0211040c0d01b102090010035200003518007601a0112580d0000c031035245030007152036151603400c0c4001420040119403400e81988000505007080d02514034070b40d90880701c2e00449040e070000626160b014400141142050301d03c40d03d10410606040e443d090864445940307261011170120b00040103020003208000c000c5c0900c0c0d0751002c2c141051441c184017542c0d0000346001e15045068040b007400403c41841008102c40404800e140701001d032050380342d00740101940c1c003410b0303d00740314600c21740000381609061042c81d00d0808000c0c00790000c0e90031076840e64040d50045000e10f0f803e64091003910800640e814402000300b03d90403001c1c0c02c02a0b8078480d5800e220407039109030305140c17901e4542c5017070308020a05c1101c89442 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 971161915 1250 971160665 971160677
    0x1e022401030c060e0d02220e030a0507031107031a01080d0c0209060f01090e100305070e04020a030f06061a0306131b0c0312050411120304120609080c2a0405040b07 72
    0x4d40c0012907144150108065884100c4201d42c1000e04800007500503c210191001e01c03100310615032003070341c0740318121049000035010042240032a2140c1c018502c1d410200c41900c17070459981c3c0b00c0c8d1100f601121845444589541d00400c1000c0e8100420140000c4c0e03428001200940c6400045440c0300040c05140140c5500c0a038812903032054009000ad03000f0560340c0303615402d2110307c0700004105408112140c0c407920b80007282240c0c050181d6403180da8000c04045c6001c1c03d541d24140c10200c000c03002c030b03186503c401c40802c1500c0090041c1d5006100c0500c510784924001c030800100c110b00c1804130901c1131034401c2e41030240401e9090920340303004e83d0602803013000c2d152070110b540a15141d426000285002e0501c030804caa955015144000708403030807901d0380c8001410320703141c0c401c0d4429001c590780346008284c0006c0c6070340c20541c0401c3c056500c480c20020543e021605005c0c80e510148040081100c6d904800000d40c0360303100d072144090300c04000d140b401d540e9051003504054041c07018041 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 971163165 1250 971161915 971161937
    0x605100804081308010e07061805040903021501180b1012020a020c210d051303120e03010c11062412030702031006050f09150108071e022401030c06 65
    0xd0b80003203440da40d040f00b4000074100d6490208900134850b4420001c0607015415000a00702d12819103000e01554a0f00117200e000c1c036240401009040e02e0b6022019405000042000c0b180c040007028020141090a20007800c034030340d450021031b044952110300c100c070289908000d00341e100c2048075024106180c016507450240030141e240c0080398002540c09512900c2201503144060950590810f6600c121001d8021a000a440c50b014441c00707075040014140003000840c19907110b00691142504020441031942d50120342542e171406800b1000c20195400010036040410460354403000d80064004001c0d084881c01c000c00c1e100c403514a118285096580d5900780003801120940c40c1d005041f40d00310b404903103098011703189900c50a40704914001080300c840c24550189442140c1385480741004001c00001500d8031900502642c0c1004042500a40c80c01c82409610740749e40101d8000b0a01e000c0b4030b0fa40401041403880f480341405c5900710041000a641d8a40c24096401601308410040 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 971164415 1250 971163165 971163173
    0x3020313110a05031006031704030321150b0a1e0f0503100f03120f02010c09151106100f0b211302040c0302070308100e1b0c0d0e12010605100804 64
    0x641c1000d0341c5800340e814810291001940621b0031207105007855000c1031240c521540303c138052072001801052021000340d9a84890303075951340400400000005600002005882819100381c01c44d0050060000d040140b40750840356890718012035401c0004000c18041e0010217400e402c4540909125010000c206017004880004001d001045d15445143d940e82c1000c1c0f0700d030382103100c04401180801c507101c80001c1c07060103464080d0030192100b00b401071410310780036003280e4140c10800410003070304840d000720901840440d000e0702c01348603e103011500f803000c00590400c4c25480799010000801201007124802e6014481c0075004540000f5280e8560a982c50a40203000000754401e1406440c01c810300d030141d000e00700460181da03400005980f5490002e5000e58035000d41f5045207841030000700315481180001e040c0c0c4044405a0f424205c0d03113400c05150415140d210350210b010b1410f50300302404e00d2104000c203050410028041c04e0310f01004101c0e04a0650420303030412a00c2030005041c0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 971165665 1250 971164415 971164429
    0x1030b1e1219050c09150121090f030e010e01020a02130e0a0602040617130510021803030720060403030801120c08061608090a030e131b0806010f0302031311 69
    0x2d41200c1c090203016641c02d142c019280c203034141c21540b103682c0f031102154100f080c44a14103c00f44040c0c44001e441c072041042846030030032100080c02c100751518041c100207510304c08213856282c400c0c2c031089202c0544034009407800c0d0146010384d0441d400607138101c02507607803503018041d003085100c80040c210f0024517060f4202101040d01400d59800001c000034100e5201554440c020400c40c030380e01054844400c9609d06c00c00104c00070704540d003d44001c0d0b181c4a402d5000300500e01c1501c008404030442d12000c80c1c1140c10103d001c0e140e01100c82d415103110301000d100071030009411104140b8160542d40e001e8098401030060450701c2e624503000401b001a045910720250107940211500e0f031400c0f5a110ba440303955918114001102d1001040b110000003d000e000f41d6895151600d00c44100000c3c04010308014420f8442140c840405d4083c0140030b00360802d040c1c5141e030782c0340c0c1c19140200c000f421a40c0440400780405204104228040c0340b156040d1101ca46d22641a002140842000482c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 971166915 1250 971165665 971165683
    0x60c09010c0503030106090306060e06030a12090f0806270d0f090f030624120828080f06030d0c120216120309080a02060307050f070503040e0601030b1e12 68
    0xf44400000440c034241c0004001040307a2040d10240202a00e8110360054180c00786d0380d880c3c1540c4441050740c001441100043d101e22014a45a00d80715a900040e00385403000d80c1c4010740390f810040500210b10300030742151071628102c101c21502c030007846090950b2020040c82c3d4004000ca5000450304452043d4030801c002c2401c004c1211495403641850002007102c1003a4840d90741038413194081d90f60481407400c4c02c6444142d512410b240a54840f01c69545c40421401640ea80407110415050034005441c032940020761b89100051821000c2a00e000b0301c094046403080d4803a17540c290549900501b4440714a41c4996507088400d01c540e8181d02d4650951244c400305c0502090210740c131303000e02c2034080303483d4085d655012045176660684c6446000300d4030065088401000055030841c0241d0061022003a5410441e01d8003140d600c40728210340041d0803580c45415001c061048940c2d0500510700543d004451121444107a0154802880708645130715000380440f200ca840006414400307111 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 971168165 1250 971166915 971166923
    0x30b040f2306090706050d0216060c0507051204050f130b040c020615010804110f061e04050103050114031e0a020301150e0702030f090112090f0c050a0611060c09010c 73
    0x80076042081886800c0c070380300d5451035510803400014141040050786008540381921240c4c9400b51800001c2c000e5440317842000403201040070349a0000b1154031500308542056619a5112103592a1060401080510412a07001c1c01c2c4401d1005030303030f450101e42d810704003150b0071000007801c0d601d000040c15080d200c0caa0310038580a203140c00250041003107441400c00c40c140d0700f039200b1720070b0040d06d01070415500600442e0b11000000414240031000240c5200000c1805082220301d104950406841c4102d0200c1302802180c10030455801d8050580134100403081844a0301d810360210741e0300c52807c000d00001d02841900008243c50a00a8a85298014000b4000010841c0076084000d0142c0309000100203180001f820092000c000c4d0303806078500c0e002c0c4900d0040c0c12801103810b03071110403a1920080d030713070324680d80080c1441d034400c0102c0e80b04802a050b014601b008200903800356074003040c11301c000e2403940aa0b43d680440c420341d0000140120039150389170580103c80c0b0f0014010000c1c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 971169415 1250 971168165 971168183
    0xc0303061d010302091b07060c0203041212031b0c0609020a121a0a060303080c09150406020105100f05060702060714060103080c071406161103030f090301050a0510030b040f 76
    0x700440a000400c0c140c070b0080d107480c6140d480d03a00114003400d0303880d94840d4800c4000d1140d2030004401e074225441b000481d00c122070426813103511844e03001044040c211142d051100c9910035294140c01a140e58030740103514051a0088841c02074401c0703030042d0b00200b0315a40c8100a008656404c51000041d126503036001440e002640f82c40c0c0c0e001300710301c10b16195117a900310004802180601603842038907455500c9040e59256880e0340200d80c0c22401c909c50388809110540105a12a040640000d2015600104040c10f00504401d090601c5030040869681044001d014030713142c0170200e4840e0395042d00d10556908060814007031006802450800c0760141c90000014003000002516801042d13006544607650f4134101d15000c0041c04103200c0e000ba20078012201d10011219800070b0040c06036080c0150b5801000c002411a80040991407901c01c000c100341050b81000d04c240d81d80145682030410142c20081060b1010f1192880010881020000081c04108080342c10a80c001e90102080c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 971170665 1250 971169415 971169449
    0x110606150d200a03021e0316050a0507060c09050f0a080d0e03190b04031202030f04031409031626121b0627061b0d1d0102120c030411010c030306 64
    0x703000e07510000203d116040001c02c41c0d00386c207400c031041f40c0c000e45c2d400e03005021074401d001041e01e440d000f109080040c4001800030f01c0100d1401e000350568000c096071405045401d04042004980310144e04500609035150244290740001800c00ca09d91b030242000d0700e00c0c0110034000703450050381c500d418481c0111b082d5400c1c10000092251806107100b40c552104000f04049450101d020840307030485400881c1001c1004280a111503000c0004404101d6150031204404a8a07081607001c50450065061504015200704401c8142510401482d0302c1c0d40c400300d4010303042c0e0f2101007030110745039000d0018040000501a4040c11038800c00b0000fa203150389032004900c000f4081c9044814a00000600072004440000c144240304070b00707207a041090005682c1c10030307a20783c01c19100c0944040da515080550540002401d03a0306904903000907a5401c11800703840d42d0228041c1401284203428014000003c28080030482281801e2030502055506030508401500301030b44101d0005c2400410 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 971171915 1250 971170665 971170667
    0x10050a080105090921250b060d060e0105070c15063c0f05010215010b1b10111305010206011208031e0c12090c06071b0306020a110606150d200a 63
    0xe02141e50781200da0805819091041e012001c43c42000101f035903901c40300241403132808003500c1c03102d18024000010046103495800382101d00903501d00f004542000b548504000065032a41030b040d001800c184206031415040101c00d4006419101b81c20001062903450310380b0008a00c48003030512a200001e03140e80301c102840ca280785002e024018003540406584021141e45a036048a2042c0f072035900d04140d420301031360024559219980c1d680100010790410041a00483c0c9004008004290381e1f0600c000701844214419809141075410a200420003020541600d07200d04d034103c051141d407a0390b40e00b10300b14443d680729681c41405103400c0038045484c0f180c0d00605450f44c0c200441240300d0711a01402580c6074044c1c0422a800001000b007000080c91039120b40d0600c2180f041b1404201b61280c2da6102a42c2128070103800044558403400400c00d802c002c0a50030100644080e84e145c18509c840950740e200c0d0035080c11000b0b440752000017481014641000b05107000000807600c4081d8008 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 971173165 1250 971171915 971171917
    0xa0906020705060a0f030905010609020a270308030f0c0405180f0f060603070507060209041815020a05180d210f0306081005040804031a01030210050a080105090921 72
    0x50400521610750086141e043c000126000084d50352140c0242c1e044600046016041c9420100c643d0754a8810019041c0224000f40c0b070030301b099403661583e018100307c2c18091454003074902c2c14002a0b405040010036806400c42c1d801c48485852641250b643c111200e0940c810784c1c0c400707600320416a00b11a6a04040084c41303024140342c07aa10045ea8030740c03d4003184502c1d0161000c0354045802c00c081191030b40540010108607206400150900e103041d0001000c81d2143c48541313009039040c011503801c1120700312016150103081c410842c01c100e80048000e00c07501801c0c00148100f01c80c110310307002540da42400321523566484402a051891800c00c6220b0354009500b40901059001c682c1d0b025840c080e004810a4030a02402001c1500b06540210047d203005001560f01040801010021810f403a81e21082000055000d05803075146105020206d6103908045040003802c0c007002030f2003a800703003507141150401c80303250700c0585802140300e0a00c85200300007814085010035101e00c44240728 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 971174415 1250 971173165 971173169
    0xe042a08100b04020309280b10090c0c08040311040209030303070215071407061d19051b06031f0801020711031c020a120909090b0f06010914120a080a09 67
    0x46090080c07008000902090740000d1b0f88108490b044161482d500030100006026400110b80d05405045120744500b494400e0503140c6d080d111142010611242055002e42c2d00707494114a00304260f034100340c403180c500d400759000c0100080001c0844203001d681399010b544114900800341d070b03a281880b00010356180c3c030400034900882d101c100041d9401d8051120b0441c005425103030140740054682e00c003002002c0044101003083c10391f41900c0000752003040180c004480c840d00c8a10003140b81d0402529107144540c0f4000d00c0c00c040c000c480720395100e110542c4e030021250320551900c07101d88800030b04c0310300603904898820362001c038a003020b0001d540b4141c10303a81c105030140d03100d00c0f540407260444002480c83c143c1c0507a001d4408a40000c08024101c21480b01d24a01030340c6458452100c42c0c20f0750540794082d1640800c036402d10200091411002d6081442401c0410f2290729107945503020081b110030070307881441c8098100c10b02990901000d05d80680c0034603015a10b4041c01c4014201c0c801c58 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 971175665 1250 971174415 971174443
    0x30f010506031611250e0a020a200c0405151806030c09041a0a0e012d11091c03020706032304021311030601030b03070e042a08 56
    0x90905003401220b004401008200c3c001c210150415102d507078000d00c0e00c800718403031101860303c0c0d0800b00d0043c0c651010700b0202d8604441c1741100364042c101d00038111400e03441c410008502c0498002c0c681d001e001107001c802d6071401d02c40391602d41c10300c1240741c40d49804c51700f08410000b8211a40007415240791080300c444150050600d100080007500705e40040e0541d0022000100621f05041410b0b80144507004000742102c511a410000ca4800d0f81d0140780da0f500c1d040270300c148010a00640c00c080809440c469002da4001c0c142194003224000742400655407200303080f68210365074049498902000d0144c804200100300030440d5a240080e060f00140544c45010908a20901401c001b0303540003d030720715000703480c0ca4032018401d0703024100700d030310040360640c00c900f52846000300c94408030800120307600d81c9030000c00502070b1036440004904c00d4110b03160601110b08204025500281c111010418031500c401114004e200701e800b1009020300c070032030005143e034800100b900640d458 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 971176915 1250 971175665 971175691
    0x17030d0c030204060906020f100e0a060f050a06150f0f090b040b09040e1b060a17040312051501021002031f08010c020c010e03102423010804030f0f030219020303 71
    0x51b400049072100b10a0340032a605400040c040d002c2040a50040d0350000f80f40f800f81d480585050b99000203e9240805c424200da484000300700e100d00c0d0710b22801d03000b840b6100b0101c1c01640740000041041520742c1000081c403d00c8070070420590310a131741c07030740252100c4401c15a95075160360907400190460050603109508245140b40e9074000460403030001080e1001282400140104104080d0400c03d4400108080e800138590009030545103580998041d0301c403140e81060032f44260007902c000030036a01c48918205082122a6400182500d03550032007000140c607a115000303030781110050300d03a1294002c41c91000c00303d8000410350000002c40c03815000c403030032030307213504011748500e0980c1540a6054000c1401e40b100300ba09030308480c0c003010250411814640314540310340d02c408a0b0381c02020208900072036011403003010383c10601e641582400d140551b0f2605940040244807080d02d95010088031004c1840380b00d00035019104030885510003041c0b44c28004600a42d260011a105091058 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 971178165 1250 971176915 971176919
    0x80c1b0709051015030e0a08030c0c0105010806011409090a2a05030705060a12060306021803100525050705030406080f13030516020105040f140915010917030d0c0302040609 76
    0xf05010050b41107882101501805401800042d402014500c074040c0040c0a03440c0352500246401005612601d000d00382c403500e5401d07041c500d81c2101c4d4140c002003e158030420061049140740e05148290312070072681d072101c950760a0310007814451407060042400c4407041403001840103820041d07401080305840c0c01396295442c010544d80301d40c00e2107050342080e0700f00090f009403881040200300c0b6107945000811216a1396503281d0890340034024540c0f01c000426502110381c6024081c68035010b403498806d0040b41080212211400b44840ca010034081c01c00310410402c5001e502660050342c0c00030266034440d607403098041e000c0c40041350100850f02e50318000071007a21511101d98035280d0140d8584d4144045017900d0b10198102d580140e044c008244800191945251058800b529030745410440c980b07048401d22200f050040c01d21710304001c45a00401c5541d030705c001e258003107030100c105501c24000e2404120382103100d01074100a0301414240309032074141d0141c0040c0111202a0b6403181101c2d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 971179415 1250 971178165 971178181
    0x50c03150103020a050d060219020330061014400311010c1e0201020d08221a040b04020a050a1a07030212070510060504021801080c1b070905 62
    0xc0402d01009500c2804c00350107000d01c0c1841103103002103a100303440051800030500020070301100c4040780301c801644009020b02c40084210290840460354501035500080d00c0500c201c02d01c0340042c02c03a80074640f4a401000020b11900e04401041c540303030b5072507568a182c8050359408822050340407440402d030390380c004032256810603050601c2500c45c22402000c2d040d65200d0350b41c0038108006504020384600100d020900b5401076920f109058600c81d05820090b100280c1082d000c0748001c3d080c000e0040070001540038000f0b400001c07400c40825001c0d508040d1405149404405071441c08c01104901080104201c601704240100d000300d0b0055240c81d41da8003040908070943c0942240d0500e01180010500070090240441620a0042e194241000101c0c10030310741040b00c00ba0b845620201c5045500314a40c1305150191600752000d51030440842000c01c0199181d10b40c282c104400400040d03100c000d0703803003034855600800d00b602440c03600160419075150381a0041c60314052900d40854555 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 971180665 1250 971179415 971179453
    0x305030a05060d030c030315180501080c06070507032a0e0a060e190e10022803020a050405090711010513020405060904030e0603100306020406091e05151303060603050c03 75
    0x102d41c141d4034005c000c0d0b03040d503080b400380140c802e0802c015000200d0105840c050030b1890006110400400134041d03241c02c111519228030030490500481e010003c0001281e004501c0703400350f83d040701c05c1307040030700070704210700d003401045600c0101c032501402d408034042400c9c440440c0a4608924284030316902c0c0d8418006901007500e000030700f2030002c556a050040f107504058400007000c41a280900c2141c01d00800fa41c0c0080c1c3d0341815420514031050b8100159001c0d64030308403803441d04506003000d03058058610701c42d6008251044002d140061031541c80b0b0505854a980d45000034000d90900f070403204100071201c94201d2156050800066032400c1444819103e00d80580d04d41840c001d603007080c411030340c0c07003c4c0140048a01560001c00415500d00003440142030303c1ea66a014140f901044510254043d0340346100208500d0040000e503803044a1502622044011180d8134000f101c0f92032188441580011300301410720400009001002c00c000490341006da080c0c1e2410000410520300c8 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 971181915 1250 971180665 971180689
    0x24030c020d1d12060c090a060e100e04090501151406030f07080712020c15070201021c0b0307051314060307081203070521101e140d020d0305030a0506 66
    0x500c5000100581c0391410303034040b1400360103080101a404540300d094244181103903c00c6941030700041b1541c044c1891040c0c0001007042e4035040c01514182000200000c031040d1848080108400b600c0240340e40741c3c1d120403103040e4040c0c020042c6004a01e4160001007881c070615048e10304070b0540780003e003007072006c41c0e00c90940400c100d0059035030b2460982c0c4a55015006404011a6040d94902c1114900c010030044540e80020142d1340c0090300780b0011000000d003124210f9005101ca00e0041c00104c8413440d1b90480300d41c0102d44940c240010a01d00002c0380e200582c0200341c4030742020040160b5000d043e8000381415000040d580d0f070802d0540c0c3c3d2240384140f20b902d500951500003140135800c09142c21000e549030240c50081150b000c9940d03008201c0050500c0c0712210140000341d00c801003560003c000c82881007004418907854810301c15954807800d500703542a440d5200042e9a06204640ea041c1e006250b18600f204d28240242a504101d406023090f61902c004200b107803400ba21002c2e0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 971183165 1250 971181915 971181917
    0x24060c0a151a270108010207200303030a091b090608010605150304031202040509090d020d110705090406091205130e0103020f0f040b09070f17101a0424030c020d 71
    0x100d040c1590b09221140c80c4106681d4006180c801d2116040442006000e000f809180005030301c03a0403a09000706070792600c054207689026010140d5500792000700591740d100003140e0001030200030381d007411442c072140342110f0f105601c003040020421034565803100c41654046002008400e44a800f44981c8000e83c070342000c220b40040c000600020f200b8503c220f14500740210150a20ba82d46001c81c00416081d83c490044c1e8000d08050007005078104074400d00d4490914101e00000400d00c02c080c1c0300d203014010343d405030310701d000060706000054001540881e8810740080003040e103240010300700c2c0c00c00c40c01c42901d242c50000000d2a607041c4919281a6038008000190600f04217003044030241140c02c070243c100380c0700d91070344c03145a680c0706901d0f21a001c0c540b98104031440c0808020000526900000443e03500304c4288400714100d20312850658601e500340d044101c01c090300c01d4100380540d43c8100b500c401c00200c511001c00304542a01c0d1290003940b41030280c010b403450f00341d80b1101e210117214 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 971184415 1250 971183165 971183201
    0x5120604080a0c1a04020414150d03140412120f12020703030e060a0218150301060e03030d06080715051903230a09052424060c0a15 58
    0x1004200c6481c0100384030029400c00a00c180110703a43c0761944031100b039402940c401c41000300310640c10b041c040c00d45d8100260072075800c04d103404d50f8100c3d8100f0b440480c2c54041d4900c503011004060061440c1d5208804424140d9200c80c1d5a40540706d50615440040740d0301340c1c2801001400d58054109a40100525241d07076184400f403000c00c40003504200b500398209a2140c0f103d000c8148103000490040c40050805a5034078540c5c2d003070401d81c42c02d200c0081d0241d000c40450781940c1c4160826030b415183c00c0d02c2c00300000031071000003d155016400c41f000d2614a414400542203000140c480300b00c0344c8080c804020a10920003c2e10140036221410540000c601c42c40e4807030a209502c010220103401070311140c13042796240191244d074800c0340c42c1d040056903002d1080074402e041180c035021106c415501208030215600324840d45a0242081260240040f0560040c200c400484130300c64030050207464440b507a101e680350340e503541d4660583d140c0802d002c3c600111100c41c06203038060000c0c44044 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 971185665 1250 971184415 971184421
    0x70b06030f0321130b0f0603010605010c0510020306041d0c010f05090915011206080609010b120d080604061203120506030105060a060c080c070810240909060b030d0c0c051206 77
    0xb403e0701020060045249080f581c00d110300180c0969000e03400380d42241c1c0d285045250250a144c2150b10b01e40015050111070011180081d07000074503040f44e81964034025840b40c450102003006014006e00208103080400806001c0800020304805070302026610458505940341e0203450a1080452040e00a440303e0009a044214050744c625210010314140e040c0112000d1610110740e80758021440a0300860140084403409020356003403420101c0742c1c40150440044150354460741000440c0900c2914000124035a0302c546c4a00010103035500038802c40e04a80c0b500070020000c1e00800c880b080c0c5070001042aa050500c035092180380090949030308a030810301c09603501680294110f5041c0801c0003541d08548042c0309020041480304001c1c048070100b801c1050554065100303198080c12020641c02610138020180e0045400c402d00000d614ac00c0ca050082c05800d0a0000942510401510b41c0c42d09900c030360203901a600a0510f09036a41c4c0740c0041045e140c075840105260b40d8089808 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 971186915 1250 971185665 971185717
    0xf030216020d020d080c0115080706080601080910020a0503040b180c190302100e28090b1305191104081e1f090b07020c0d11010311070b06030f03 64
    0x42020442c00108501d440444d20b5440c80180d601c08907600c050b60b51119202c20342c070300700c2010000150103d10054031145092580042c00c01d0300082c6490704014101c0d01003580a102444070b0003c1c40c81089095503516100e06000d843d0358002d40c0d003205c0078615200010b0804090b0107403200300e101040090301002c1c01c401c00300f105810302142a100d041158100c00070041e41d400070118607111081c0c075081140e0755041c0c20031040c002e1520300b4070401a034045021100d0548040510183c0307450322000070b401011000030a103080300035111200c5882c03801d400d1040c1c45000e94000f800602e100c500c1031103140071000d0320944900582c81280d0b05c50303124904264102c240e0920b00350318078000c81d08564483c0468082c0c80001c2824041e1030309096514905c02083c8010f0321200303680003c041c00180649000d00c0c01050542c01420006040c614200102400c0e581c4607421484210180200b4580c4484042c180f105040c04151001c034400d10841c624210042e0f404002d0f10760101c0149a451240c442c0f20034 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 971188165 1250 971186915 971186929
    0x80403080a0608030d0506040b0d11131b030e1b0f1e03030f030f0f01050f13180503220e04240c1206080613231c0f03021602 55
    0x104244107540c884030049001c1808101416a540308001c0105183c2007500604c4119048480319500a02203a40c114012420620846c000604180c541446c04c10986152000030a2014900d0300d038082c0c01c0300680520382e45500600f03694048401940c0340c6184d18402d0209a40010501e507801ca172040704210100d2600d01032001040c402c8401451401d101440001c1c207650040320b00702c1e0101d0001c014001d90109030252a07034880700c4440c4034003980d4106030000d039209000e02900c6216403100ba04101c00a1900c0d044800043c0207441194004215403a11907180d400035640132800c001d040c0c1031041c404200e0703655107040390821000715207562110b4880304070701000303841440f09611010120601028003071040031000703503055582125899403800e1000680e11203910203100c44e070002c42401000f070950005c80e1125544040c200c1401ca8618840700942030510002005601900c106440085140e11580004200703030390300c0036245051058140e04034058520074600d00010282000010706041c4c2c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 971189415 1250 971188165 971188171
    0xf0711100b06070807051e0102040b09040905070906080d080a06060818070806041a090c010522030218012d031202012004050112020313020d0c03151e0b0108040308 72
    0xb401603860012151540703d031681c8040030459160303000301c442d030f1041d05001003400603040e410030082d860305280111b00d40480c020650000e00c10703643c41200d035007040400c100e80c6004040341c54041c001260340d0f983c1c1584600081031740034007040034040000c02c81c102c3c1d4400c0c0026113050780c0310026103440f2200910150244000004c03083c2c45019000b040d02d42d0100314252049101e4104003254045003a01d2000c6007101401c11490f43d480a5401000e42e0f030004203036000400c2000070000c115000d02e940701d004c0d01c8140d0007e03420500c528114000003240c3c6424030b0503249182100d603c0c80160340c14105111404c00c004004a4045007024800640c40b130b03034100e06029aa01c004200d00c03040800d404480d24803031115030001d541c002070070407042d6044040c001074515141c40c110304503d00a405845420000c40009206825441030311003005080c1c0302c1c1d0009107801c8804030b12222129601c1c0001400023420b101c4001d05c1044001111a42038002e105020406a4031301c51517803a00e550a9903070180107 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 971190665 1250 971189415 971189419
    0x3060e07050319050c0703030c0516020613030206030a09051c0203070b071e17100303140702060f1c064106070302030306040f0605030316170c01050f0711100b 70
    0x70740c3d028040b19180c05054020742040041d1581c84041d880c01a0844010300c48010a000091111031480340d00d200e03401030040d0b015502a42c0e9020401040d815206a43d04000d61001c80401880500f030066880400f8480c07054003158078401031090000c0c0407812144a850051f4420804040000c240b40302140c0c02075800d007024901034900780660000d04420110100c000340c1085800307400b0380c5520102940000b05040d0051003181103840040518051002c40d2101c1b140000e07030507045490320011904d0341441d95004644036015030000305010011004100d038210b05002000ca4504248008601034504c1154290040d000c00101c00348106041e0307007032040e0700075180008115030700c403407000300412882503000e540e9a242100411007242c210b50031040c400752810b0001c1c84a81c0f00041100d10350388020018540250103841d0004400c1d040f1500102d071010003080111110205400c05c07409040551403d40c410b5885107012506002941c200902c60351200d10b202004100680c0716030303045000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 971191915 1250 971190665 971190691
    0x1002070f0209180625030b06070524010515030a0509010e1621033f290901170a08040e061207030f02060f13230103060e070503 56
    0x1500002c01c1088100c0304211400f0f6440140e0020020070300603a0362006030b07015015100c10a0722102001c51800021000c203061307580c03400c150160b881e80c0a441300390b580f0070220b03101c2c05049044e80c944900301100103e02240c1400021603e4034021200740c035004000da801d24203643e111140403001d00340240410138195070711000c00000b6913080c0505c0d4000e90b034100c01500b02600e00710341c2c0000c1c80551002e0341c450254844c04400000c1e401410707032140c820700380703c20f0103c814040c1e440b9100b080010316502956004c0e10340340201061a0300101400030340b200d50300300c00d100c0030020f040708025100d40d0300341d1240c1e24000602991072900c203000c55600c3c0810031184588449e0355100f0455220f034204a04400ba001d0411580d0320742080b1011030380c1c9140c40940707000c9247d80e030b894094550641009200c0c040204400540b0403040c400e442865803002d06100216a440c3d040c001042018070909090600b58110080300307500900504045451110030b22003eaa00c07201c08880e03e030006051800b68440b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 971193165 1250 971191915 971191943
    0x131a120a090c03050d1b0c030204051b190906050909160917060402040b0a0e0a1e1406100509031b010e0310060e1b03130302030c010f02090a050a0503100207 69
    0x7040c44200b070041c500c40d80040050180590014042d09150b242d00281c12842000c00300c002005006690304807603060b10f010480792a0104403220304400d10582a41c84280400c00c107440c400b01c501040700018080d201d10f01d1154680314100c5041c800e10f510a0781000c80c00010400e81104006c00c031203d01309500e00f032545a62250301d0301c2c44000e140c080c0110b880c1c0c01013040c0015450503100e50200e044003182c070888100d1510014445c0d6030401442a80c0082e41c6042c18007170311401118100e0312043c20030342000a0102e04520320312050042c0d41644c080c107440070111004034060000c440a952004005103203014440c0c100140103c16075401c28108174a1610280103914100090301d511100840089206420318945400481008001036606110100814202d1103408103d98000b5010725440303c0c1d0b81943d08003a881c612420f10840c07240e601e4101020201c0d5484d41c007500c40d2b46d8040b00c0318112180c1e6002045000c4019000303c99042d0003140a0041d000c0d01c44d4002c0c24030a1080d4070f1034810003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 971194415 1250 971193165 971193173
    0xa2313060810060807061e0e0102160603050a0f06060c080f071a0f2d070c21020c030115060c0321061518050f03120f131a120a09 57
    0x145002e0100c001003500c40d03005000b4201c0920114000d0040e81c506240d040c9102c041c000c014400441e441c6061012400c80c00703290364824000c554040b2000d01200402680d50310004000b4101241d006000514040c504038880505000301d408880c1d0b84d651303803150a0b000d40c59029175503101240840304c01000300134100001d0b0090030264245c2d04108000102032038841400160120300410f8030190310284859910200365680c001001d0321019440303140d055a84007800d942c1f00e01d1802014046140400162078440c0c1d019524000c00700c81d640c240c81e22180c812092500343d4480f8800c002d101c0700b055106100240c40b03158204500c41c00703854182004100c0c0030900c07450347d4000303140701d24640c0c584074244855441110468450403d80c0341000d10150030300400d556454150107413611844000d142820340303540411071001000841c1c410fa903603400140450f80c51591008400511154402c20f00060309248090a0440340c403481500b60314002010404000c0b90600410081650741d07503111300700100d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 971195665 1250 971194415 971194423
    0xb0604050c1c1b0f02062d060d141006080c0307060e030307140607080124080c1c0507200c22020a02070f12051903032007020a23130608 60
    0x507105901c0c0c11107103001c5070000a0070540005c0002d107414040d409070080d030300da0247e02c24a640200710b440d18043d4486000180a000c1c008101030300507030b20102c1107180650045101c4990b40d0200c2001c03c0010740d100486500c40e6107840c0d0303d80c0d150300007007010403015016048000c142040107080c1d0f40b8048195507040c42402440c107409005911403001c000120f83c0210184d805401c000d004600b40c10b00b001d61407900103038843c0c0c01c04200f1251501003421a8903a0b8103440e148803103517000c03005e80003480002c040109411100240007510b88420f118401d181851800c0c0d02c60014806025a90f074000140013400390405200486802e01540001c07442c4011301c003402c025000d03503003c0c3c4600c6251540d040001d803410b400c40b13444036001d4401d00000402c0000e1b0b0303900b5030661004007a0200311504059000b401c42c400d440104404480c100720000001d0740c01401118400c41740101c0b0740e510f4440c0c402940f4880d414142c50003e40c101048560301d03201d03011401d069440b41001c20b4040e1118829424 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 971196915 1250 971195665 971195711
    0x10170c061608030c0a1b02030a260708090913020105032a030103050102090a1e0e151504030317010e0408340309140307060c08250b0604050c1c 63
    0x103130100410508140e03030307204044002d006036140c844200c0c07840c0313900060307110011080018410b07200701e80e1981d01002c00040c042d01c1c4a0005503015221945400c01d10216800a41058840c0c4010b5000610065120400e0b015850b0182c0d1154150381e158401d80c1305002d1071825202e40040e80b00145a440071020f001540a18490382c000340e1160100300a210540660360807030f990801e529015007411411191103002154002010f030304050310f5241d481c0380c03000000c000160300701c2002d4503054000003d0301c0091045a2080c2d86d00f41041510040501c100f54080c00380d00c80500d408400b0802040d031010243c00301c4445219031158070151441010208191082030301000e051070b0742e8543c113041e049001c030401008202c00a047d241e011000003911035265003e1042400846950303802441501000e442000040407440703c00301228029a20f2001440c00c1c045981e10030950001d0a54201070107084d0051040200d02030400303200b200d03080140d20526140c2124030381c3c2c1e5412030303c0a150406a03502 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 971198165 1250 971196915 971196931
    0xc02090a091b1e180b0112020409060f0e01030b010b03070513060f0f05033903040c03060605060a1d01030e190308070207080a080a03022110170c06160803 68
    0x142c60f103011051100f01001e220704016074580b0420400c01a00050481000300000308800a500141c0100690300400040d00c070944491010802145444c0c0e103912880c141c80f01145d940305c0b40340d650700711601a080c09000047c42c010540004000e49c9801c10061500081d80d81401c41c1400200a081c030081000c941c444000a0b52390b80c20100c106800080c01004080c141c41d0051441c580304c200c0403441500d070103507050096015030401103680c85081000010040b4004155600d04003802d00029240d0103003c1640c1c15494224009114904241264810f114a1b101c04102d00182c082c05461054500a00c5052544070300c1030304800300c8140400c8100301305a1000f00715805040c14014100640140b0440a56100400900100b580085d400b20a03580c460307001c0741d07502289031040307000e4014182c98180e0f80f0b480a00380d4030508400f0a80b80d1285403640014600700c2e566083c0180d0464130104000d01941264001d007641c2c1c20800d0050508405109540609043c00d6a030404141d1080711211 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 971199415 1250 971198165 971198213
    0xc0c190b21061c20030f10050709050f040f0b03030f0403050c0105130b030604060b04060201050636092e0609090c05010804060e0712020f0d030c02090a09 68
    0x34114828a0070705500000140c80d6940300d5140c02e008001c0c5030100c29005480400c15480d40c92600c048450100c03030b0b01d0405025614a0208800d050340d492042050108042c1d0a000000381d04903c01c1002e0411114020301d61003851b01c80394240320080c020340340074542d0241c680c00506182c2d18200000c0c00800404072504c0da442c6c1c55800e1850810480c0d092503030400030300b0032000240c0807815010b6400d81d02c141245545d40c1e22007000090040078240d2208611b00d901050000704640c040d80402d210b100305031010340083c40207003103402845031118860804180800c1a400b01207102d4040c103940500c003038003110702c0240e400009150581080c019084481041c002d000a140e25600480c0010082480b0130b00107031840b5070b601d17403400a95009213410444148006000c0c03001d150080c000c00c2c204502610b10b4642c4900240007921030340780341a4021031081e2104c2c905814604540180039805560b8030505040c0c40e400c02c42488800340404ca045620b610b4000045013504550602c00c1040e88010 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 971200665 1250 971199415 971199457
    0x806010903120e09010b0708071416240201052e03080301031211010506030a120521011a0c030a111005152b0311120d090b0c0c0c190b 59
    0x44203909050300020907420040c0f215100023407599080c0c442541d44200b01040402e1088012032070182d02412a08147c0c40c07000e00001c0c0004035001a215500d201c241d00d140c1610764140580c240c0358169100b150004a0b1034002c0b5480f107084018058950300c0c0d03880001c856682c0d071a100132035042030f0010340c7c418100790f007070115030781e0040c0300101c0c0804400300a200c2d900d48440020b460f20600c400c0503040d541c40310807444040d1300c240e08560121000500384400c064210150f0141c03094240541c0318641c0700103214035000f40d11401511036000400006516101c101d503011507410f0b4850400e04040e125181041d82d00034840c2c01313058401c10f1140c1c09482605c1307203482002a00740401903008070f00019074030301c020381c640c1010440e032145800d8140b01c6981c0d4102c0a04501d04500010407213004100882d03078506211141e003201003414014004a002c0352207140742248c3d14814084081d0b095071015408400c1c600700310100b03a400100c2c103641c40411070340d220040703080c40c0e2000c01182c514441401c84 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 971201915 1250 971200665 971200669
    0x1032004030c090c0903030906142a011a150a031e020703090918060504020316120b070807024c1109010e1201090503070c03050c01020a02010c030806010903120e 71
    0x1494034480f04c2c600e80b02900c2851900c002d0440e6070640100f004000c112449503103203040400488140182071028810a181e002d402c0049040c0200c0c0780c8910b0f5401d1010104424681c0b42111920700c5008103c01c4940c0169182412954040c1e0201803e040c0c480200515540391403103203940b0b9040e880c81c0540d0392022403400030020400c54228034140e030f00d420017550188884480556801f5800b02001136141c0322800000d18020130801000603000c400800411240c00e1008800c1d0058031441d50f6030902c0c1c442240039100d0034000c80d2074800685c41f001081e40070351080c855542141d149d00d0b201a440e900c401e805ea1610301801c040c00c401c1c1d01c403668404070210481d072040c242c092206200450501613080002440740e0190080d55100741c0c01064520b540040030340c080c8003e16440707801c682d074802061a04040c10410b07403109440d203010780be0f090442940003040743da6107250b0594504200321203d640580b240403010b4019810004141004400614901c1c4100100c44041e200c280c00303e024401 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 971203165 1250 971201915 971201921
    0x1c02041410150305010f060c0f29010e04080a1404030614090f121902010b1c0b0702010e030712170106031e1e020c030d050a05010512010203100501032004030c09 71
    0x50940b0416181000403c180d150100404050702c005180491115160303082061000300c603100050403c185072052601c411030481070a600361a81040781001c03607a0f03200742e0040317003c06c12240a85062410001018298801d10b0360f1031803a103c0b0b0030383d5402c068903501ea00080f22601e040115800c10413006014061004000c10703120001c2c102c004007076004e10800d0f408052f019281200c80200b03480c1c3d0800119a00039002104d040340041c00c0c601c00300c2c1042200d4a042400400251030074031510020401540c030600036405881510780c025854002d0380c0d501e42c1d49403040402e2807000c0101b80c404000c203150802481d14001c001a81d00840c8403911b400e110020f0740420802a08000d16001e042030418043c189030b82c0c80c4000d0440c005840b451400d5080b81035101b9020743d560224982004c20a034541a46e0085059030310a460740025107280722426400c07480282c40801402407030403c1000369620a0b0080b000fa52408910500d010140c0c010045c981c0e0042c1d0030403540c3e414100c1040c4803001c0148 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 971204415 1250 971203165 971203199
    0x60709140d1101080705040315200f0301180f02031501110a0b010e10051018090b012705060f0318070b0a3b011701051c02041410 57
    0x11000e10380340c1c006940e104004a0184041c905004408000544990255081e90021034100404841c1c0e41d0071080900010700c00949400156060a2690895103801a05444043c0703161900c0758078503401c00c29000221401900d04a80346501c0350030301d079086001c0380013442c003c1c942c8100114181a240c000544041c404000310a1590f0248250401040209840f103044502c941c08600f20b41d2280c800d84a02d1070040e4100580003e034050305260181da2000c822108404020b4810948548411450f400c1d540e010340c0003400503480d651012420081c0d60f04000340b2540513005002c00e82e0b40c0f03d001c42d800390010a50030080c10700100402088488000c0c070001c800c00301c500500070aa00b0811002c840b0701944000008101032518500340c2e9040820350324012590b40e103400105c8035007502c551213104c86c94266681c0028940c414480c01085400310703440c10f890b0700821110a040c2c80f01007030110044010b505030791050700c5100420034112016506801810910301d035610aa080240d101070b030b50340742 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 971205665 1250 971204415 971204419
    0x40201090806150108060a150f082a0c210405090109090b040f050705150d1812140909040809210604060908093001020405151b06070914 60
    0x14000f00601c603428051040b4903400c09081506507a1103081c08038007040304c940c1003040d20000700303910b0340505900800e4a84410307a86aa49101541c0d407281400079021440c035580d41d608c0c003040341c5050b1600305013000c2c1c040c0400c0134080f1441103a00c8184441e00c0c1e8030703003a240724510100040c144580d040028026014080d45402804280443d9a9440404000503c0035101c40360741503c2e802005428001d032401400014441840001d500c141c031000d507800401e00c80c140314130700740300746090312601401151144e80125040650041840c0103844002c2c0d02011008030a4040012640941da09403110340107038017420403540c461013540148004c4c0c0380d50300e50b8404070030312840106c00d1181e000074010303521903440f100c0070031014002d2908146901803141d8003607021441071040c9002c24040d00a08210400c00304011108170070010666080340320301d029598014a1040300f086207140f84100400d81e00d41a100d4803800300c0d0304403a50a0030020290360741c40004151300d80403c01e8004240d030300e80d485441 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 971206915 1250 971205665 971205673
    0xc0f151603090b0a052d0a0c08070e130609060801021306020610150c050316050c060702031b0111071202130e0303151c06090c080607080c0c070315050402010908 71
    0x2080d00d030f00010b07540040c4600510364960000454005800c100e04003008558241408802505c5041c007101c500100c1d00a100c0c107240050b0100c149100307040103405a100f503120310521355410030510101c00c0b1a01c1c0c104400544803000015031525030710034580280100c40005840c0c085401d0820001102c6074003000440d40a002400050444a0582c40031140852034000c040441c601d4241d038150b40260014000380030200d0707000e10000c4040000303c01d182c416000e40f007164920108111860140c083d0103905940480c1030300340e0360980840b002000020506003403889542c00c54240b813805c1c41c40d030849006441203a030104210708201d40044040c04030010144a82c941d02c8103e10b0741c81c00000d02c1401c414118419800325615600140850310581f40350240b040060744c00c058000d0414141c044465500c09440019103810210304140100d8003070362002c1140e160005c20300040d4012030480505802292400400501d242e03900f00741c24465600d0116140c58540005003140c800342c0e02060031600 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 971208165 1250 971206915 971206931
    0xc04050709060f0e1306030b0f10060f03020306030c090403050c01060920070f080c010b01090e06060703110c0301051801180308060d03030e0d0203070213150b0c0f151603 75
    0x6002801640c12210510b03100940d190520002070700510b0003140945c00c246414008800d00c800350710f400348103416000e8079600f503484604c0944040480e03481383d0380c00206200103022815110340c0040d500070710000d0884601481c603c0005a03546010303501180440ca00062817010f2400038080c900040020700d40c00c010361040441da584600b80c9029400c410320704005050000c006904140074062500004001e0b1500303910613440b4020034503034008070b0100301e40f40c0c8001040d0340b40c4410f041c8124805400c40d400c1c00255034050314a143c049101000600403420102101c0d01c2c244034661080030103841d0f0050404000040c5801c5400750300d40980c400c0c0c0211585d6020070380000c1c0c0a60443d0042d2440c0c0c111b503649080450041c04034820240c003038010290940020b6a001000d440c110f40200c81a81c40510100804401c440020740c003800b000340b130b503a01040058035420252a6046118054030000030400d81424182458070034004124003101c2c05008007003408440c049560b4203e4142044841 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 971209415 1250 971208165 971208167
    0xe07050703050f160804051801050d0b042102010204050a060816080c0c030d05100b160807151503110a060905280303050711040b0d0f080415020c0405070906 69
    0xc82080400380c1400303800a00c4001c40382c00d5008a40c2c0c5140c18a48100520380d5a01d0441c2c2564000c0c81410b226614200b2a042c03044094410b17203040380d1005102d0884900103a69581e02850000d20a0303420001c00c0790403250700380c02c0400002c07651010344c0c00140e41f1410141040002103050300142c0800404000300500d480e84034154220801980c1440c0742140e03075450030402140f0170000020014000032030581c00380c0055400050040e81c09082a07920f051f240c08504e100c6010300312030120701c2e1645000c0e08000c94001d80c02414064041c41c02d00710307201e03141070040e029101c080c03943d003000401d1010108144140040203941c0c9075001c40700f04007420701d400802801000980511803144000034281080d040c007500c0c0124410f42034440d50603c880c0c2e01e00b0040c026420160044d1303051050010781b40541e203414881c0a40500303004200071080592616080c00f410030304482150700410810012400c1c2d402c094400c114805994000c1524058041c140001d035000035282c0401d00006103000e10090b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 971210665 1250 971209415 971209417
    0x3031401061e170f0a150f03050d14190e1e180c0a1809060806070e0f0105040e1314011a0303040503120f04150c020f09010b030a0e0a02280e0705 64
    0x10141c081d40780411505d40368004c00013410b511000d5140c0e0140440f0016515010360a110126401101a16644010014180e6202000c0d42121402e9035042004524480d2002108200d0100c0c515040e02c03030144403404a80c0190030203112001400100c4150030b041d2404160040700940c1e074426014203414070a440c50414011910344409105030f001c03051041c1644004210010514500140020b55844201a45400d020b4481c0000109500d090004a040042c1e440000b528103a4810703241038a07109104004810140c0540300c0d040001c1c0e08840850529011101074518440000841c0000d40402c0000081071220040c040c0e0001c2c002044603640218210071541d2400d155269188070a03005441284a2900048075983c580d044800400d913004070240342075442610b5000c3c00b0b02800c1d04028410509200702d1198480800c0016041c403500e0700602803401000d030807103c26112580c0082c0030b45201e04081e07045a0340450490443c10b004098050080c451002c1e442014103010000903c1 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 971211915 1250 971210665 971210671
    0x913020403050c030a08030c0d201b0703030915050d092009060603042a0603060e06010c0b0a0b150304060b090c04060203030402010f17090c030601060315050d03031401061e17 77
    0x81c23094041216040d4800d00d4000444002c60100d400e2000c512150701701c07040f0f800c08440d0500c03289000200c010419030000c2e08030b056940549925064a01c2c04442e88802080ca100800800ca4144403007a4011458026684220312503074405880d00c1801d103218490051030800180700300403850502c0110b444500840790455001900090250002001005800c05e2051a49803070684009e0014005034542d100c101a00e4103e24003102c0c5440c0c0b200111895150b00c203001d0110409000843d4003400d00354400222180064004e644030f11070f40e8001401034000301c40984040741c6031000c006c224500f510722603034000200d0004500706070134440c1c02540d034000288004c0c14000031803091114280603a2000307200f80c61030303510b80382e5511307064041c40c1d2030b5038054001078042d120301400841c01d28068010602c040301c50a00d804025031030803041205d10000300000380c05155a03001c3d0748e44410300340e01c00c15003c2c01e442e03220a070001401003582c2ca504000d0311070f00f008106c1e00300d86001c0155040b50507190 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 971213165 1250 971211915 971211931
    0x280905071b17090a0801140705190c0213021201050f010c210504050a030609140c032d061f120b0402040207060617010c0206010906031e080913020403050c030a0803 72
    0x100a5030307034000b2058500c155146241e201c50503a40006403403105420055440040c07884204061300c2c0c4034800c2e0348a0080c03a00f00300c41071506195030740e10355105900c501d0240340020001540210203415a5081f80e1246c00d020851030a540700500c01410500001201680c00b0710341a82d80040700d4803500410021004160384403000a11a01e21041c401c50541c1c0252100400e0941c46550741d00d040da00038040d0200845407480c80e10400c82010002041c18848210090050140506840c004a603480340340040ca020308154500815002c1e101040f00c9440385442c000142800b2900000d2001a06201e502c40303403107022a041d0603070015000025035a001a411388000d03888403041e00d428009024aa0400542400e001303514500b9503105400c00b4540c0c2c6180d40a0b0342107640c076003007540b06039005c40c040039281251100003401c2c0d03200381e984040b40d0710780103509460034a402140011030080d403468915041980102e81801403100520405800007421070003040090500da0340e211090100420b140 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 971214415 1250 971213165 971213183
    0xf0708060f0c0d0609060302040c0801080d0534170301030314070501140a0204060324030f020307170303040c1d060415080102160c05090f0a0902280905071b 69
    0x82d1807103200c207040c0e0784804041c074014000b007515403009030010000c80c441030b8441d9090041a4941c41c4c01281c48606a0b0030460140c070f10f5054004090b959540010207498900c405040189100c41000304ca040075020301800421b04545a0700b030405590450001c0c1440300c55040004000181e041400ca0b80c2e07102c491544261543ca4a0034005d0041a01c81886009404060104100f4060985c000d0043c1c5400351400c00000c0b890310342d880b440f002c1d0036040840d1500b9050091000c2100c064060b100544010101e03500c940d1200d030244109016900300e40c180b5071020040c0300070411039601c003002402481c2c0b0f60044450f280d0303d0b070201c0240003808980c0220b507910b034070151110f8150420409000c2d498000c0d5a00c000000d0a03544c10700d89110b0a82e40b5103c0c031308000c211440e009403058010718881441151540300c603061132004091003d42240e02042c004443c1c07508c0314441d62051480900d801c2130040840c81c1030802c0741034410003003002040043c0d07010b40400c211108254100100e8200c5409 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 971215665 1250 971214415 971214421
    0xc02210909182407051e07020609061606230601080a0f020412020f091303110c1c1101030e0a0f170f0a2a020f010210020d0b01020f0708060f 62
    0x4420340d6034040c800310418010300004401c50b903c0d60502215003090f8410601480e5501d40d011a01401080140f16070100c0c0c40d0162459280420081c106160004140038a00000a40091226401510310310603030910401041c00f44407652240070080c03440207075112030712007c0f40c0e0020000000144024140304082020a0002d00a03a1200410900011003103540316104d100d02541c5001d460002c03841981c2d16004082d43c1d082040440d0b00840154529101d40300ca695400c0d41d906001991242da98810b0300041d030a01c1e43c40b028440c484a002851030115545541426142107054110f0103051600b0031b4901040d00c030307001810030f600c03642100e13049050103c540703050b840101022541c4070000c400071901ca9a0040d11a0080c11060305945600c401580d40740c0c045500070404512419150168080e00409070a0401054003400814810303908078a11200c0d20104030f80000305103c40496039004204c03515601040f00c013080c07000e40d000800940d4508110242c1c3e65000800c401c2c0710603580404 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 971216915 1250 971215665 971215681
    0x5040303090219082418121603110d050d020c070504050c031008010b060f1c09030503090f19060903020a14151f0905190f0c02210909 59
    0x403074540d82d8014400d152040600f200444002c00c64090404d003801800c910240382c0c1880b0416181d480405c40815100e039541d03018a00300ba1b080b04d0150700081c040c0881d6039602c082e01d1002006414034041c14843da1420a007001040542407501d61181e690181c00203c0030650020107654010341c4205015a450348500001c03818401143e002c550424100b1050100a94025020f54070420b61040640d2850740d48202450988080e8411550001410000d07044555401c0b4001c00130b0305510003030f00c1041700440c0c0c3c0400840341021419800140b012060012604003444280040842200101103d45800603841d8030047d040300002d00495962414804060003400b100d45c0007604403200c011242c55640300e49440b2044c21980c1684004980d00164039605500f0003100c0c8040140c04400d03589043c681c06400920019080c80e05402d41141400e00e030b0030b07081c001c965540780c14060120304007a8008000e803420228618083c1d02d05420042c00c1d6100c0040811b4801e0600211400200340c2c1765028 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 971218165 1250 971216915 971216921
    0xa051306080105040b093904021210030c080a020114030901060b0414030d11030a030507140d0902091302060d0c031d030304030801080c060d0b360106050301030c060305040303 77
    0xc007034019542410200000e1060807500140700c1d40c0d00320182c42c0c440000500300c1000210b240e603030035506034040c01150b000b608001c2e2286003080d8098001898102c00b01e00481400008481900340900c80f0007042c0700b003146c203d226a0081c030041004122190080d0b0010700f6602c075200c0090040800840082c004c1c02e070940080c4000c1542c40d40c202e80d100d0b219100c0e06030020754141c13250b02920a08040b2038050380304400c1b59a01e009400099400c00c400704008a015004c060001d4042010084407107110701468001050085404d0200090150091041c012030950003000304041e90a10036200015071a0760007207a20b1003048070340000300245080c009900034003580c4800c0c8494202075400a1851400000640c01b641c02500c40c2c2c03030560307644c50305166941b4400307c4407034002105001e041540e00c00d40d00601403407000102499260006840e038280031840804660040c00f5880c160314003003e10ba5140b5a001d0300180c17030b00a02c2d40d0b0442c1c5402078504a188540380800d076850000400b818401c1d4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 971219415 1250 971218165 971218169
    0xd05041413020c1e030304030e1e190911161b0b070f06050612030a30090c060801080c0f1306032618010f36140a051306 53
    0x3100c00c40d03c0d2103210000958590800c410801c803101210070521203280c000090b00d211384e42c1555804072003403030b0205100c031040200081850190b0800309000c402c0d40e03040042c05091008040828400b032501700180190307942c04400601c11a0100b101d1014100030030706240f44160405080146100c40b0384040703140c0042913126441c458008104081001982e04141903000d0140d80d0a10142d140c000c1080121081c1c80950a0290f0040018105050142c44071480c106580c035480ba0000540e00703001542d191000e4031011040750740c1d807804001c0105001009000d01400c0c43e11100030340c140f4807103d640c0d0711350751002031141d9103513a90003045d5070314031b03062800d51581090300b03000b960340d2840c01e8001c036040d083e0021076100c1c108001c0100000304409941030140f07004000c0e400c011484005480025840c40c2c1402040944860030201d00444407c0900d61084034500903602d407031314003517001b4013144d82d00700304180f11400010400f43d80d207020044d410303143c0c2129125121508000a10001c168503 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 971220665 1250 971219415 971219449
    0x5040507030b06060c0d0f031109240c01021c1b141b030a0c1e02062a03070b01150c0203150a0b100206040b06010e1c021305090c01110d050414 63
    0x48664400744c10713489075002c1f02241030783d00c041c049108818818003446c060000d0064000c80301c41f00da540d14100401c08088100c1c0c450600c6490300d60b0882200b42a03034004c058455007510700d50100b00c4100424840c2c80303482814011607646140c80741d00b000b880d02e550010104070380400480e4030a103455005c03071003101030000a000c907503941205840161107051000801d6440028031030f05410760700700c1d0f0503005102d590300500e058034040040441c3c00c40e143c04131000c400407050825144543d024100000e2251900440300b00d405585400207040d0320014040c40c000400c0101d681400040e240010800019186401e075610141d03036180d4031000030300354030390000d900800c008804141603401081e00da0080e40200c454004568610005481c207003c00c50146410566118030306480d0b01040c1544000d45200410400455505580c80400d80b003058903940036a401040340055250307000300b03c0680659800b006440903114214010b41140201e1051510400c00c840020569a5903500f1150540c452 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 971221915 1250 971220665 971220673
    0x11b0201051629010b0405010c050709090318050105040509061e1c15050405030a0f0201091a010521061b0418050601180e0106031d100c030b0405040507030b06060c 72
    0xa07800e110b40003003400d107485920f0600c0c520090b00044103404440c0e050b940c0407841c40d440c003031030b280045030021303600d00082d1410300610700c01117400d4585014091800f030295a030f040340b0900a004628840395142c0c0491f060210400040101c0c0e144e066000354132030310481e014454006240914000b60750342ca80c0d0568081610a5440114048905000c0140c1d010742007440203160b400c0c130702500b00e4030b0548003c0d0140c1d0042c4a40640148604c00f00558a041d0340b0011400b592659100c0c7c6c8500b02d004800705071919181c006020a003800b40d0007002c03240407810720340c582080c84200981c0b1001d0180c40e42e4231100e10550403200920000c006c580003020742e18000240b04a428004038010f04040d40c40f1400140c0031030310240b406048203c1007007554140c5c0c0180c1e20036480e05500354000c00f0b03110248044180291000703506a50140801450454480c00c0440c030300c54244801022190001c2407280320700e24150901011074000a505d00c252688240c0301c5e550b6854483c00204540624142540c40d441 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 971223021 1106 971221915 971221957
    0xc1808161203210b0405130b011502030702031207050c0a0e1f030212010f180b1501050f0406030b0a05040903020d0e010504090f05011d0105011b020105 67
    0x8420f060105842e0003000c038101122503511500d03500c095803640502c2c0710382440e00074254000c1c1c81d00f40d51600c441240d41ca183c0c0b0303050180620089050300c0094a190b0034020000c40381c50940040441e8071800116503c00200ea00080084905004880361b512690130006140c405880c0540900c40c101c0c1d07078116803000c038024081140481c80786502c070004003580f070b808240c403403655103d8004507040c4a00c4901c40240d40d0041c0501c981e50400400510214400c4208113401030284101c02d6003403281c003401240c4a02524080f0b900300c2c280010001a0740e03400d0350200e4035100b401e60301220075130340d80c1042008442101c10013401681203454181c00300c1d0300c1000b1206900e0070505241c2e05041d1108001e038102c81e0340410140c46583d84030018440700340c22000000b60304e10300c0d038802032080d81028002450001a0400d9400304030001540c0b40c110f80c056419518500b255600c201d00c008 = true := by decide +kernel

theorem cover : BRFrame.Cov 971043165 971223021 := by
  have h0 := BRFrame.cov_init 971043165
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 971043165 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 971043165 ≤ n) (h2 : n < 971223021) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
