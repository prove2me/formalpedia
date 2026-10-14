-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0141
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:04:28.443043+00:00
-- url     : https://prove2.me/submissions/878a4a88-fae6-4d7f-98ba-d83512fa2253

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 25179862 ≤ n < 25359718 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 25181112 1250 25179862 25179881
    0xc0a0309090c03110a0c02010c0804080a0c06020c0a17070306020304060204030c08030a0203120712140604054b103b06130212090106060305010e0a18020d0303 70
    0x42c9080e01c40c2042500c00d200d14441100790a001900d002441c10701581c8401c1d40c04012070400c280341c00c0c8940002c1e441409440109030500043c8200c7c400c501d41400d80801ca03030004421544003140c9134601d556030505002c211090080d110b419041842c2043d0f0400d03c4c19000541000d00020a02c810040e260f40204100d82c0690700241800c0d44490300381d40c0f2441841078138030041e481070000004001c02c01c07403e01e41003292400d0401c500301240d00e02805440e11504000c4051207543c040050b2420306000d1076500583c4800e240303042c000c58100111598008030007005d0b410203000702501c51320b0342c1d11051410030b00001c020151a860f1003a50108a100c15008003105e9140401501c0c0650010340c0300456035003c40504402500c2985881c00c1259600410551340051040010184090948010684031011003d040d41c185021400d250941c6e40d0b030350041d402c240c80c0400421428600c07010707a581096410310040791290a6205140d03035280f104101030f51100118944104254250f072101404 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 25182362 1250 25181112 25181129
    0x82208070501110a050d110d0507030207020f1225050d0503070302070905040f02060304020d080d060303090f03051917030f0118060b04140103180506040b09011811060c0a0309 77
    0x1c4002c511080080c2c0101c40410003c00da040c00400c110104030707080101c40244600047d400c107120300e914201a10020350700c03100880d90015015046d8104071039aa4801c5100b1f9801183c0208120f0000b0740d6881000f551848130059080074000071002c07185100d0041000030003a415a00e000c1c14030b5612680b0495048000d40b05601c0d00242850440c041c0c20300c00c41d00311107010b030700322426003d1042c981d000600803640440c0650040c000a0300c3c02000e025a072907002d6000940781d007141b4000d4140c096541054480c16607110b410000140c000034800e150505580000c03101400c546086058004501c001b1b50b0b43c00c80100c10040101000b1220318100d4030202c408000c882007e10b000070803102d450040400e8120100424030460380031584040d0390702070601d030001e181e03404500280301100c545807003214181c000e1001d000c28042e900c04400e8201c014400200a1401001a100320385449800f00804e264251595003940d80d03a42c070300b40c580e100001c40c20b070340b10100c66150040200244e40a515503 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 25183612 1250 25182362 25182371
    0x140702011809020319050907051e04090501021e0c190c0e01060201051605070c06030507051c0203010618150e060403060c0c02100306030206040506090411040306050601170c030403082208070501 85
    0x3c401a00c0c01507034040c03407011001d81207542c11302703060003001c0303021200100380c10071202c14240701500c1e00e202c2d02c3c441c1c9026100041c1c82c0c0405e81c0301d54280003d005a800003400d0300f844002485003010603900700b40c2c040101603030b002e030600789024048505180d0110a0205404000103981d03030b01900a28410314141000714030281d40382c20152a640513a000c090508041c4100c144040e5000fa406250408414208035003441d0042c8815078900c111003008026054021004110282d0030255801012442030b001080701424400070740144d894000c0381d8800c11035030f0041c01c015500c0d0401107034003542d0000e10a100065200c030340502031265108c0304038019040410f0707001c4c0b43d5100388107107000d481d070041c1603914242ca48000c221494002e0381038240d01c19038a03021801070140d464014070055200d0a800310300c80c6084800075202d00c41c00301c54024030100000401200304403050440b0742c400e5042c2080aa05c3c0c42c0c041e100c17412068421601508034000101c00000d101c80c1c80c1c081c0c030199204030000d11 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 25184862 1250 25183612 25183651
    0x60807050105031603050a02040f03060902030d030605090f06010309020d03020105060102060105010f17040203010e030304030903111e0d05010b0a0f0806010803090307060f02030c01020304030302040815071407020118090203 98
    0x10b0325071000300e81088829192041100c0d40d24400c0e00090b80096140300098203064a40d020480c0340c0c0c909500880d41c890351003000b50f003141028401ba10889070141020410702d8504400b1502500d070060250019604200000d08540c1c02540b2850f82e06402802014000f040c52030041d000f0041038032014094800c0d20000540e5600c20a8841d07048038281c1c0e00ca504240014641c0b04031410081e0080340e15540741d0b404082c901c68100050351045001c1e540d030f521b5481c03441c203012944d80f0504100c54042c100d101c1c0307001485220311541c0d40e6201da00340d1303603003020240b2418094010b11040003c01d41c800c01e8180c00061240c100201d210544c1d0311b01061707407040d03642d500100e80d491044400b8244c05412001c0c0c100f000343c2c06100396040184070380c010b9030302c1c016401c0011800c9a00881c1c04a01080c0d005c03c2c2440010320800c9104d022034001c007484403440c1800880588419510407120421400000303000d070031648112140060106421402117126071610103690180d003013100c0c4412250351441868 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 25186112 1250 25184862 25184867
    0xd02070c0608130228120b071103040503060c0d0b030105090c040b01030905120309070e010f06090509091b030c0d0503120601090303050a03150503030310061b03120c03140405010608070501 83
    0x3c0300d07564020000180001564032904940c1140c1890070782c180369941000506c20310042d0398103182441052844010318140744040d0240c08115500e001340ea0003031005002903100090819000090a40d81c3d80e2100c2190301d45d00050002c00b0800e03a059400e000a000760507900150000600e0011501807207204d00b186c00440848690305400703001940105200b182044460005540003179442c801d403000e09840e40031141ca15102a03203c40c00910302c201d01040380c2070b8000c0841d405410300721005141410581401030b0356000c5203001c40602c5d0400c00c24545584d40c1005080341404000e800d5491204590601076241e810107801035400c250104006001d07584079501540540e40d0503201d4508110103500220010055400906a81c6240900c04501558204003031807145401d0310003446000c1c2861f400410304406044003021175081d07a692400003e400c8441094002071a204c0080d1a91400a08402030a8900c580404400c0d202c01408180030064001100342e540b000b08031600d03190313500b004 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 25187362 1250 25186112 25186141
    0x405060d0c050607030302071209030b01090c08061009051903021c030206010603050408070b010308030402041b0e01140d05010e010e0105010c0f111f0207140a150f02030d02070c0608 80
    0x9101c894154024003152a01030090100d16020345001420001c2996031a2109825514005c003c40e6201d0030410400170210070490240071002818455001b070340c0800f03407600d10081c18861051b603c0444c0240224450300c05080103040041408505a00e04003c201e0428000d0000343c0c060741c902049800013076000f034800040799a15500803c2280c0c80e02900320000c0c0b00142044500c0c40c1c0030080900426580c00b0b055010307602900183e50b49003042c0c4100030071039105032503818401600301d02500c09642c0050300b00203040c03000c3c00c1c817505000a00e20b00040e00c2c0b0608040d29400c074904000410b507100304030100ba05865400c00360701c0c240d903201c2d401582d0355000128028102185810742900040000e40c10020a00026203800340901100380c051103148048074000d00141d118440030840e0341554208812420070640340d540030242041401401a1126a0402c041c40303c0322655202444c402c2080344c11820039220215200d1101d4030340a182524503205078000030348054086039030482000d24 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 25188612 1250 25187362 25187389
    0xc04060207050406050d0f0303060504110301060f08040c0b0a140c03070521041205010912080a060501030b030703020126041101030509030a0c060506060f030c0d14070207030809120109050606040506 87
    0x24028406c0c0443c0d84010400c0e1380540304a0405407101d00004040d152401141514005004c0e202d84039814040c0c01041c0302c20740c55400c2e0800c0031410510003c241a240c00d5000d0301c0e8900b103002d0b074aa26881007960203061301c6c0314110904a000500340c1c512040400030748103051003401a21807501e03121031140c00d08900c052406102810800042042c240800c201055443c8030304004607402a05072209540c03c0300128500c40407030000700c2008900c000c0341c807c8030042e00b0242020041d06800e500840e580341c40b24000241030194120042004250010030510400440d84070050140350502d8401c020f02210b0842d540800e043c82c000c2540d0b80070100c1590160501e0380d89034231035401651103c1001e82400707482581c21030301c1003100c840401d19050040d80306208441c119503440c1200c440441c1155402111140e032701200c6010300000c0c580c0482c82c6800caa03000720b01551123040e400c0005a104413841c3c2c601d169580781072100070403c42c020a80901c80c282c2202d04000a40d1360340144034900503100d0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 25189862 1250 25188612 25188619
    0x304110906011d04020306010c12080613060303021207020f0a03080a03060e0c071b050d1407060807020d050a030b060a020a1b0b0d02031302040212010311031204060c03170c0406020705040605 84
    0x701c0200a42c10301742d02460388480c0515041c644119543c03904440d1745148106500015280c000f081200d00b489030742d00c0b41c01d20320f0000800003603280d42c030001d49501007030b99007034404e510000c1d2040c29560350348264210007400504000c42142c5d2403030030380e0540c1d01164034403011a081220018521b141042c0d014429060030007107a152000e05e9588505c4400c00c00507404075020401c1020503161508a40b000401d40305880d42ca0104091000c0c00d031601215a12020410814004001e100c982c0401c0003a1040021b0821603180c042c80e2805402511440c01040e4000e4070100d60301c40c8450b0300040455000340204640c2c1e0110040001401d0900000d00540d04600c40030031600e0521540741c0d00440c0e1018a86680840702d03292640064145c1c1c0c040842d68192103030100040c400c2c003104c40c440c03a0344020200d00416600b00504071110050055208100c02d0000c940044810715001d03130925038a0604a07076040a65140041418015410901481006111308107000c141420284906000d80710003d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 25191112 1250 25189862 25189907
    0x807061403040c0e0a0f05101404020f0a0507050a051002030406051303080c180d0303090311030310030206030405191421031501020a05070801060311010813020405090a08030411090601 81
    0x613501c0301100040e103000040d980d00d0140c00030600030746c421603000302c201401c2d40d0241c51510201031011001040200d100364410440d0220b0500c018003291304d0723103405013003031501d41e009810a90b0401d0014000a40729000362050210440d007290700542c4654840d00781040743c0d071913201441c0600041c220005000c500c600001c00d200780105000f400c0700049040c180144440e504022900038a5400d0044003c00e40b174121510800d0f070020404554811200300550030b501e003008a00142c00d03028480039018090000c045801c0c01024005c60b031190850361540703010a156494032001580301d0740444d104a01407815044002803040700c541c0078280d0040d082501f561071b07403000103400508c1200d03004d05500c40c0b801c140000030010b00141c1c0080c550100001085803030350504070302c003002041d072041c104026007040003c43c2c9000342c2804000f980548000031140c3d01c10201910385005045c01405151001c41080108508403022242c02031050341c01c81000d4490780015034880342c6c01c07500c00c910115034 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 25192362 1250 25191112 25191119
    0x304020307090b0d05070e07030617060105040902040902041409010501080106051e19030c090f05091903090b070c0503010e0c0102030304030c1104020f090306090c0a0b180306010807061403040c 85
    0x5410614480b18000d056461404c0f80d40d036203619010540e0b1020805800500401000d60b0b01881060010035086144507104a14001d92503150941406168840c80c0d0b143c00c420151f480c0e40e4032000c42d1540c041c02c100030080b0342c403038a80c40403c03003211030f08103a6007040c0020458a2040c011013007115009407a0700c00e215070400880c00c00e507109240e4284c12480403450000081860322205008601a68061140c103040044400545604854600c0c040341820b043c080000030003d030a030740307120342d004101c0c0761203105260841d00c0235078039401400060008a00c0400340008410042d0403624102c00030052001c0300704205407141c00c040101805601f0a0000401180c080c240312400b140c03058200e02d84c0c00340e4500c0060101e800011194407903207004640c0d0841c1c4d00781009015000034000c00200000e071a1003001071220600c80c018ac600003540420040740d00e01440101c10020744008080d9491581c556481c10740c4e034845480341a0010381d404d0303100c10070025544222030103690400501da078040d05 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 25193612 1250 25192362 25192379
    0x80a031b0315090b0609041119110c01090b0403020907030e01020a0302040e0a20130518060108090c03071806080304030b07140c100903020f010c0905030d03021c1d01050f06090109020304020307 85
    0x100100841100380f0100f029105100127520b040c810800345d52150705408060100703040c40c0900c02a0f01c103040c440d03110030600010ba45002545e044960440380880d0b16503600c4030403005001c108110803040d43c0041041c01e503075a015000b50042d2400c0e103002c0b81103075a030311501c04180c5004003044501100e841024a540c0d0015000806080c00c0c0241745119207951400803460301b020f051110710324130000d0760078400c643d03a0122500341c004d00800001c2424040400000780c0320203030313481080506801c0c4035058081d05081d0300040014800f100031b82c2d0b160b0341d0340d0a080d4402c090895186d400141100c0303003443c0d208140790944440c0b006a800030980e1744150425180100085a400c0e41544035500c48a018101c0034014000c00d034400d60789180300e02e4903100034141381282a009003000c0c180148900c020300503c0b4031103a402c10500110104455680c0301d680d070b00220490b41c014600354201801c000070b20303d0202103507006400507200b002c00f681c1d858a40314224081079800a5160304040400c115020 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 25194862 1250 25193612 25193621
    0x32802100b060a0e0307151214040b0703200c0102031e13020f0a1206090510020705030717121015050403020904030c080405060d050108060a09050604080a031b0315090b060904 77
    0x700c016048506c46034450704144448000c9201040001d101d85280440c080042d0007a108410203550340152142816500c148841c0002854081056a01d80b6007000200101920b403420310020074a80d955100040c06840c00307503000b00e0b21070801020304030f410a03540b10800361042c420003c207041e5041c1d8003129420010340c1d800c03440056511040c1d107040441e0340c030410300413100b03150b104040c00a8030404616041d4240b07150400080b900510500c602000302e41d01000301c0301d00d19400400ca0000c0c401070b0f80d40b228035000b003600c14002006524100483c1700205c204103010754590081102000c0c0540300111054490760000039040f030348001c04100001d0040c00000d050601c900111820103840d58041081600040540c0200c81c0d00c6000402c00d0070414480d180c3c018030031100c1032000851584520303940d80c1000d00000c1c0308032400140d026040c0d1080d808031460362130004082405040b075140007006801841a032401000c070200001900d9480d40c85462801203014102e9030806001c0c504202c001d2 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 25196112 1250 25194862 25194887
    0x60a02030705131401030f0506010c0f1518030207050307050622090c0c02040b0a0e040807030311030711150f01060516021201150801090309030b0603032802100b060a 73
    0x1401e000401c900070080d683c00e000b810024400c180344404000004013035401b0403610200440c50001840f00f6130342c0c4251005885504203404102c092800d00d40b04201c45c0000c4164800c0750301d0005685074200302c00200042c042d01a03400c55080b103840d101015145c070040d20800360700042c104081402c203400000d40b40034041c101d4069030035645d5220041001d441c03c1102820000c1d80c0c103045403085103804d2281d1a505a0309a030300708007a5082050000c41d452000e080603000e400080390510070141705e90460300094982503c0305440c0e05102901400c001548006080d00740284052403001400c003854403072289040326401261a46020400d440355449114005200306158100d00c026072100181503000340c000600000761051102c00030400d60200c3d8010900c1a41080018004681c1c840c03440400d50381c00c091a00c00603115680041d00c2c6101b20701d0849152003800e070700c95408440c00380c40d0000006040d0250744400c110703421103204441d0504051640f151040c450404c280784240700e09240b1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 25197362 1250 25196112 25196117
    0x8031006090617071115011502010902100e0a090905060114040504020a151211030901050115020312060d120210240b0714060a0f0c110d080406020d060b0d0c020c0102060a020307 78
    0x2070004c40505d450401d0b40300e6000c0111600580c00412550b508121296400c0e1428030007041031014550000b46910b000511180400540b01c0040d4040c1c0d8400c10300000412003880d0401c44500c05150640c1c880c0003d116610503c0d02030b180410301030600e80a00c51155030b0044c0b0440495007061a601c030212001100c150400411858440040341c1a1080c2c180c090000200e0580324981301100d44d080d40d0f016005202d11082c0c081207247c0c040d03000800ea0740d0b05040321904400643e84c6001142400507050b5000d84001250901c038006c031600402d030b54003c000f80741c3c82404100e500111807004500c10842804441d15800310030001654008050845140f041203d90f62500c00c00141c10700d031010650703030000300c42c1d9140c20400c03000074503105202200c1c1c881d040001000d4030080b030042d00c41d44a04545814480d400c40003e0170000300b80d044503c0f40c02038080c20007107a501c62a00a00c10b400c0241412007040c54a600e00b0076003400001c007403c0c0f000d4143e004214995075031710a5400b0703400c040c004405 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 25198612 1250 25197362 25197377
    0x40c08042f06070605040b010506070203070e0903090a0b09090c0301050f0d0609020604031a01080115050405150303040b0406080105060f03040f030c0507120b07030c022107020603040803100609061707 88
    0x380d0303070b9081c0043c03d181380100c02c0071410342000e0908807059101130748030a120304800c10070240180ca020039440b0484410442465503a03941c411039501310b100f0240655400f524903080404d80c9203820001d00304080c006e41d007400e11552000c1c0c254660348800c0c02001e521075003a840384600b516005400d5404c2a1158070082020542031307000c03c050b43c029400803116002c03100950201c028003050201d005060280081c400e00c03c0901c603440346150343c1d008060140b9221301c000350b848041091034012414010301100e03a22030303880100f465240c215008880006190700000510351030030300103444034541151850340c074645455075042c4062100c150101d06200ba51410700b40424000c2c05200010683c0340b0b1000400d11041c503111800601c001c20a5040c5464244c4085040d50b001072088034035008010103400d401451480c03184180180c07200207510090010411081248901c0a140100c00c03548034a80c0e02a1203020a40c6c2d00d03c0c0c1e50003032000141d400c03045411881c0352006da00d034020004c0d0600c040b = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 25199862 1250 25198612 25198703
    0x100c0605040b1b09010503040f030c02030609030a1202180d1b06030203070e01031505101116050a06020304030b0703050c07050102030a09050708070608012d060c02040c0804 76
    0x4090320412102961000d05490400c110301006030b101c18030000c0101d80382460030b5204000605540000b03400a0300020940b2603000405010740d503407141c0781d5001001c50b8228a05010b5255036a0700054054002401190351651195035500035291070360355103c1d640d110040c080080c082c00c8258150151814508440395a410208045074000504003035600540e403460514009001d83d011050068109440c003030a004841c0300d2000c01c2c1d070079220111a01080d00c8501c800484000b90030080100c10780c040c030500c9210b03640000c8074000071100d00365008050150380340301c01d03070710f070701a0744400b030030717030120300000806291180d44030076484141e0b04901d42c200007a64440c182241c0007150ba100c0e015503617015840034028100003100060201200404010b07007091401014814113100e042400119441513003600c1e50700c3c45460081845024800840e07135600c4c900205a0500344070140d008a151620f22401544070b0b0302d11500c11a0000c88410000c0804007420f582c0b9842c0c0180854481d05401003003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 25201112 1250 25199862 25199873
    0x31101180b28020c0306060105180f011e08090c010207080303010902070c031202010504170f0922050c0d050709050a0308070501060e01120507120203060f041403040603050108010e010c0e100c 84
    0x70b200c0102a0700a102c143c40850906261150250206041c04401e000c074030301c03000c0820000701e200c100584000a01144035001610a500e01d440390f80c03100c9c101c41c043c05924540c0a00700900c100780c204101c42001c031000005a03182c1141c0c0c042c1c4c000c140c0040005004c0d070f15650300202040c0d845030f50300e20821b6a490703c030001070782e42c600e01e4140182d4540050005010545500d400f103460030460301442c0982c0300c41d01003074501ca804009401f800b0a841044001247c0341134030840c00f1800b039000c1c046403505003070301201e030b90012600786401840c002c04111494402c03c0b4200503210050200401c450442c2c440085581200c503084515640700d010114513401240f00c480e00030190001c0c0004201800d10301203080007907135045140c00c207014510010141e90001b400e20703086051001d03074207607545481c1400301c110001848001540e100012740021450340c0341e48014100d92803500200130740300030314122a00340c410744003608002814080c00c101e07040c40c0480e00805155100d013806a841113072030303840303 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 25202362 1250 25201112 25201177
    0xf02060a0905010f0f1b0317040606031502030403020c1203130b0c01060503031309020906131d0a180308070203092706010906050301140a050301050907031101180b 72
    0x10300107104458108015600480400c09000031070600154800c800c4000030103082018803240c84190101d00510240750060400c1d02c0005007400d83c5854a203080c1c10280040c2c5103c5c07008951840c08105150540f0b02c66200b5039018a9040d406050452010700c00c00c03119101814082a20f4002000130076406d4211a44480c02441403400c01612551200f400600f107072042c0d400140260802c0001001d10a8032034280300a40d0350000e070040c1c45981c03290100d4140d00030712a00703c03109024000d005c1007040b80c100107a5074400700064020340036603620f08840142ca80c8a00410761074001c9440f000300180c010790700740e64482820310443e4140900f800c0018003003111109550b43c02c0d9100c9000002042c1040c01c0c00b540040d0030300304030b4040c40c41c102c1c0081081c1720510626001c45050142e060203541c8404003030000300380040080c0f1003801c1030f0310704503101c040390702c0300b1074240410301e1030030390294001d0b02150100d011480401d050751307240844803492503001b0180003c1e5964080c1450181c0c0b002e1815 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 25203612 1250 25202362 25202377
    0x110910020105041509080d0c02160e01090515030604060903181415040b0307030209010201060902040b0c0705030c030c0405062e020615060d0b010c140307050606060a0c0f0f0206 78
    0x402c15080508240c84400b41c041c2150413820304142800300407908070012901203101e9100d0000b035440d1540c3c812802c00d00305803902d0306d200c0b07460381e0001644c00010044606860328540c0810058498000b00280d50585828603905500990001004200c1d20340c41780d030b003030740c0641000c42d14005011007450703950f0100e40020b0106402c0c403084070154140f2100c1c0390350004103026411b00e0310b41004203856284c0401422a8109500011002e0059100703400c5000200300d84e4005648132519803000d140b283e0441e03181d403689441412400038143c0790000e00009241c0015029008605640e000c2c40090304000349a1034014444902d904011188180c510803d5501000848000741030400024101340d0040c00c609444541c141d1061441d0f038070780003202c40c0141e074900300003159841c0f48010384201e40300d0100038200b40c1905039200c2d846407000c0b004112051294007078038002d0741c440f0204242801b485028000103800340168000058402680400c0540980605d45007000c1d43c1d400170300217601025 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 25204862 1250 25203612 25203617
    0x3020301110c0129060c0307081b0d090e01170708060f06090a0605010807270b0408010c0318080306030a06091104060803090306070807030608071202090c0f0d110910 73
    0x72000580380c2c0070b01c030366056101c085004c0411000a110024044024215482d10501c4001103590f00c1e110100229003505a001e00d6498442c3c41c0e00b986611000a5811301c24494081c0102908440781710341c81400030f880c80000c5800840e420420030980c0017400201c0107140344a03484003c00c855004004c880e01c6801004180740b11881c080080c04034004000c1c042c04507a0b0308191092100e41c3c0c1090380240e0004071441e1000100b01c10001003c810aa02000642200345240000c2051001c02000b001558400b10080c0b0803815454400c504031142c0c15098003d003514508544c0018207014000d41d04a80003c0858007210290345584c411180c540d0021903a40c1030020018240381480e01030f0354014028440614105843c0f84042525042d0041880b4100100c910001d959540a640054090185841122400d80e129120301c0c22140a07298107a2140701c031400000c03040404102101c55034201d61032101d0900714200c6e480c001400100d6075a03100c90005208220582c0c84004000e072150748640d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 25206112 1250 25204862 25204867
    0x2811010501031b0b030106050301030615030b040c030b071d100c05030406030e1009020d030324060305040b0f01060c080f091305150f0604030b06060d02040303020d02060916120c0302030111 83
    0x10161503011081036000d40e81404d070501c010481706820000703890441b0b41264000c28240d000805449003d1220740004100d804500c09000c24401b44000c0081600d205184100d925141e0b15001d03140c94000c0340c040d03038520700012840784031030810b281c0781002c0011505150752580c82a0340c81a045400541180740000c0d07464200c9220858100100005ca510a6208200034491a004108900a142400707801d06482d10504c0540142d04280c580700d000d03164045070096a1514001030142105442c191109441c080105040c2442041c04a04031061a1540031b41541d254ae41d100c0b460700250240240c0a0040c0f2100900303441d01482012900c68440300012076180030711401180c040011400c60140300010400007080d05d41c00101c80940b50042c04103030196449000243c903610510440c00c00046c0080747c0002015000200125000e1550702a81c440c3e9603040f0306540d0714051405c09a6240c02d01002c10007400c164141003100c1c1e28010101c00c1141c0d51290046800d4900645a400e01210300 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 25207362 1250 25206112 25206143
    0xa140708120c150403050304020613091b09150f0c03020c06031602061e220203010e0d1407080703050d02070c23060f18030f010e010614030102281101050103 69
    0xd001d0f9a40e0740c1d101e030340120601e042a4500502d640030080c4001c1c000c000001d00c004100c3e00c82d042c9800100b400d0710052010991080e04011260f01180b200004204c20b0800801d5024641e009800141e501c0e60f645515001c0c030390021103111503007040540542c01040440c4140d0b8071400011481540403801215850f101048000c0c1380c018014180c9114490300f00300c041c1a85140302c1d8607038000b8803694228502510b05d800c220b861070204000254590310b410341c0d0041c14100403400d00320341446d503100c01c41015a0104000a1840356510080c000f0340c0800061001902400103490341c80d41000006083c605c43d60f072104030320714081d003003050800041c0d514600c40c0114840d01d8440c095060350b820341802142c25128905010305107660340d46413402d803000d09064400b042007075003282031340000348220140c00198a00810050040c0000420010f81d802194101402102e1a0314417943c008030a60b030707900154840f40ca40c1c003040703081004081c014607401108240102c5011354091a01810710115 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 25208612 1250 25207362 25207387
    0x206010f0803120403031d010f1406010504080d12090807050703060e030414060a21020301050102070e041a180706080901050a060302010206010b160209040503030f15030a14070812 79
    0x80c00c0c0d014165550042050740080c00824000540041c2d150130081241c1901e8895200c040200301451803a9610304800f4031201c0c185500140700c0c8401c02e00d030b11001501e0300801101c3c0d5118500410b90070342c0c401001c440c1c0300c500c50f84400b070501c295540c000074075610035980d10f070703440d40802c0d0190b07130300e40c0030040074418407105118220784110603030300541c6843e10f4150350005200010700300d1840b50001242600ea002d020b119100c45884007101d0144a041c02c44030300b180290000e0282a005101c1d44e0b102060200014000c14040c41e0400600c8420003004902c4101858000b4141c00ca4408280005044901d003040101c0140016072569409880c10018803070031560000c0415a50034140001080542d030089911070542c0c8002190035603d411282503920509401c00c00207402c40c090100f0841030000110140d0f01551080c00e1814650b15104411210211a00070559054128215000c0000d6041c45448140204038003503c80141e0f48850043c14202d64107511540c0d0b090014a0154942 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 25209862 1250 25208612 25208639
    0x601050f0a06030e070e10030308010806060607060507020106053607140a0509130203010503010506010806060a050903010b0402070609021206010303080c0703020a021306060912120509010903060606020601 90
    0x40140c810800544016000455550440c4281801e142c2c1c3e904005a951400b445240050503942400040a040100034598521400c2c8402e40c005407041c8000b0811400101d809409108001c0c012802c0c9900c0d82c403450000e1501500c1d09003599a40d00c6c0c00550f640312150002e5560408035280360f002d511b9100c009441507a8828281c01440c0c4400802c1421078128400d800340081c8410f219403129507020b001da80c184034201980ea071007099604414003142064000b1416260107800031300442d00e9040064808a60642d42039501c14070900081079101c0c8184060071551030010004900c1809802c0840d0803a84190416601c1c0380e1034070b00c41d9080d0300701358001114444042000b80100d40c5151802800d87c0d0000e003001190304c4000400c1806d0510030800001c402d60010400b81e82c2c400900e040394001e1140c2d10070040412200200003841c505400306039031103e0342100c10700700e032010006012104c5920280c60603060165550300803011495500c500c00103440a50001c0c542541081c00310380000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 25211112 1250 25209862 25209869
    0x30b01050312040e07080709080a050610050d020f060a0903021503060a12030f0f050705030a0e2b0206070206040807080307110409030f210e0601090c140307080c0f03180601 76
    0x902d0810007000035483c092201e40c4d10407030615042c40344c0c1e1580c5104840c2800a86d0040c149032041c1d200030800d004011a046020355030300368080081c60303502d02c02d020f40034070241c402a40c032081c0141c40f0b0740141080c20080070300030001d1800714901ea0301c1c0e40c0003d0510450b25007411248201104200d0f850512907261030162448030041130003560340c0d9a0003410741440008000811035a010700ca60000e0250040e1540c0f69401815652510b0050100a160b520b94440042c4141050080902c6104201c2c2a0349001c2243c41c05035a219030281e005d01229a000c1e20049801c41010480040c480f0300c1030000d10094991a03005d195a150141001080b132292440707084c0c807407032900c400800002d800034410700c440e96007410f0601c4440000b9502d80c40d0002c1c0d80740400c4a0500301003043c4042d43e00810100e0694007850001c11a601c40b000080342c801e01440c0c000281c03c04200040f0390500d008115241d4003000742017040c0c1ca0701690110307002d00c90b0403d50700810f6444601d203170429808020320226014 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 25212362 1250 25211112 25211143
    0x10605040203040f0602090102030d0c1116060c06020f070501090506010810021606091b0f05120307080a14040b04150e0904120309020a0512060f0a0e060403031107020307030b010503 80
    0x460425413201e410701c04000300014012940014264000c0e4028415683c403031080704800c05c01c1915070a00600300c00050000f90115010b8034095000301d2051840180507200d19030382e06400d4a24540e100d200a60000c142e1784060802440103d001030001d005042801d81305d207002d40703400d51521100d42d240c1581c1e10034035401d49005028810455000070421514581c114401040060607818071b070069a08540030f90f0b1500a5040300829403009105c00d060440d00103a41c0049442c2c03035000401e480c1d000b01107008040c006c0c10000e0305920341c41640c0648401c1058004589480d55844050915038410f40c00540c44203501800751002c26001584418100c405171341000c2c042c90681c2c0d9044103c0313030031942441410754030a03214042d5140d00b022071015210240542c3d540083c1800415698801150b10f8030409040c0d000150300420107014160000318410000c0174182c4a603601900036100c00c4004811561040c0b0003000503a8042014a0045018121100c03465042c50103060404006040030030340c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 25213612 1250 25212362 25212367
    0x717010e0705090f040209180105030d02010e060622060303030f0b0103020a170709050a0806060301111204080d0219030e07060905011b0606051203030601030c0e03060708090c040e0a050106050402 86
    0x41d041d402c0000c50b0a9200c0440300701000402200000b0001d0041e603210541280709100130040c06000f00a5607416074408608484413071b8a03c0100302d0a1740c03600d014100b440c0c1c201e04003107030060501042e0326240707081304074140320701c0c0d00011640c90495080c1c0d0320a40000380c031094030080c50f01a0780b050301400039080c84e00307614201c02c810740035003101141e4903200b54160300d1200007640e00e889424200083c080060241108035a200101942e5070b000703a0700c55100303502c2c1900710301d0420007000072180c0c510700f40d035a490303110340c0c0c0e030340320042c140d0401404c40360ba0503020401301208075110901d0506011aa40300000c642600c00c20349803810000e60009828013011160034002c03a030b0000001e40a0741c0040c072000e0700e0b190030303890050050042540000d0b00641c440720055030141002c030186104070002e0b0780800c003020710786030111a2082c85400304d9405400c50360128804030310605d1441d61051403201100d2070380d1142004941240d111a403801b44a030441b12003a420008213025401c02044119025030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 25214862 1250 25213612 25213621
    0xa150602060f071107060203130f1a0c1507030c09080d17040609021504090e07050a05040f0912020a0201080108010212070507060b030601120204050a05160c0204060803030717010e 79
    0x20741d50407024140e001854072242c00903104034468540000540080d0b4241c803800c0b56100c0b0301035a02e80002808e108650442c42022032040c40d10401c0c0800c682c280280000300504078000e8400d954003001c03410405014052000c80303000c0c801c10fa0b1a010307218035540003a081d1407041d80205000f40c5900500c8840d000705201000090f445020884003c00e2035000340456119171409600501030000c0003508503041041214089403140050300444400712818881100803802e559120350550003070b143d1120649030148514141584030b0218420480400203d17a8100d444590015462241050050780310000400841d64031000c05070060a00f14000c3d03041c00341360300c0c1180901c0d4009011000300080800c0020a004942e00400410708019003030341c40c0365848055043d0802c40f0fa281c1030f4040c41c2803c2c042040e44056101d6284500c00308a580000084004401c8035038440c40d0400342e030700644455000c108250b05000640c003445d903645903100204020320240021890503800141410001c00420 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 25216112 1250 25214862 25214867
    0x4050c10120c0c0204060905061f080a0506120114091006030c0e07170a0207031b020904240f02070302010506030a050604060f110d0c0908070b09190302090406050a1506 74
    0x1025401002100800c0041034400d04983e00340c281d0310041d5206060560000c0c80c00025801540961025a2540c4811405402c214004a6a0380002d00003c840400080c881120355021a8000300010a08084d000303010351491f003598803403070f0211940300f401c0341844034880081208200381403440030180146840c6841d6840744904074401c100b00e80c8140e80001c1d089130300c82c11510701c05111030200100142001e5079800e0094110120480100f951520740303ca01e114940307034120341154020507240c030a65031550780900029024080340b40d0420f10520100d0040f2407801400400361070400c0060703c0d0309150a000f42920f1000c0c10040c0243c000c01540c0d0080780380468804c0c0d1083d0814008195540b00344400300003459003114440c902070000c5003071348800d10340d90000e191040080d91540f59142e151040c0b283c4a4000703105034141c0c4041004034860b1410404840318810000c4001070305520340d680c002c92000722013200c08407915580c0d0000c010040d5034911a1140b40c1980e08003400e181814420701 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 25217362 1250 25216112 25216127
    0xd080717180307020a171002030114010e0102010b03030c102301090c021005010303021e0f0d1101020405061615021e07050106081002040303030612050c090916030b04050c10 76
    0x1072445001441c0500e4110701d030400c02c48282c15406001114550fa81d4440a4080c000c0c0306030a008600031401c081c00e00d10000d0007580c0c1038800100d480200b01c00c02200540e842c0740988000c0341595220860219070b0b9900748083c15885280d00068411060f0740204002190304203400b040170803c00486112145c05c00030b032403505542a02100041c444012602649803280060703c05c80351a0400c4000300426030301103442c94141005c0c020284482a110704047d4a5801d1201846119071000305044400ea02c5182074401488451000518154445e00403410035448004070220904840c050300e81041440b030406003500001c6801141400d100e10381d01a0401c100084120003400d0200300e05080c00b200703601c4400140030001c00c507550f500f0015070354400b80d08a840705a020a280c02e400140d012900358040344803d92240140c81d090306490b0422090000c00b8017017031a644100400900849901403011003d98069000d0351000e280910f001c0f40703040710540c4168041e0b024241104015078200300c8 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 25218612 1250 25217362 25217371
    0xa060614030703020408060403030e1603053406050406091202030c0904060e0a0506060112050105030c0411040b07080403060e0c0a050603092a0a0501021f020a1b050d080717 76
    0x100303075641d072100b41044000e80616044600702e800741340180403c1681580c44a80c00c4103400e426038018600c42070703018003245c04a11014090341c01540055180300503a400600120410100b022201000c010511034140f8498001c0d0010030b0000409002903a0400c0e0140014401a62901d503090301c10781c042500c8044a0800034041d26480e40400d040005640201da060072000c3d08440c900411428519500c507400d03158540401e00c105808100c0c0c3c40035025183c1a02e00290042070f503006d00005000c010030b1810000340b410a0140000300740300070a0401070192038052500305841d1790842c20b04400300c1c1c2d008420f0410740d5101034951007058854003100011500f08a810a480e80e661102c0141443d07407401303c3d20380c080a400600807c90303817101c00c4411145020360b4020441500d5400581c0c0c2c412040c00c040b03203042114400c580c100c0101350010022885d20f0700e020003800c540b80846038482003a5107800c8846802c44192400280d6000c07004903842111454420032025400003150580e000150 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 25219862 1250 25218612 25218647
    0x5120a0317150301020d0b040b0609030a0b07050c0d0c0213020412060b06040815040c05030307030804121e1101050c030606040603050c1303050703030207050102030901170712050c0901080a0606 85
    0x10000b4840b401000b26444159034090000d555070f03940720b100e450041c020074880c103101d40c1c500380c0c003030000d41014400e0340c01c41c00026004121440081d00c55609409000b007050041200410010b002c00d94140b06d029250425070301c4821912485104110440310409580e40782188140001c01c03468442441c11000540c001030002401c85d1070383c021507460301c0340b42c1141d103052041182c0c880c102c0030b03070f030301900d21642c06902d100c0c440c0c90315001050380f40e02c286d540140010f0400340211300440c982e06080e50b089156418024020500080000d009000c01480d003004102e4010741d010050741c081c003a00b0750021100040b149540350640000d00c042c00f50703024100c00c040c0c1d6480007408441000c8203c0b03040803002040004c2140d030b03a141040e039998481c04203c0043c081e450b40041d0650000080d035101c144142c403446502d00d032110b0f844040703000040654007046202c6d150000c24008611071076000c0c103c1a403406170713503024084c0054142c080c0a0b02c00109586081d8040220303d9201459a08484284 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 25221112 1250 25219862 25219907
    0x412111006080a1e020603061e04050f04120206040c1206060e16090b120f06040b0904030908070f12080c0321040201080105010e0a0b0a0c150605120a03 67
    0x915254035188a560341019858506900416401c80c00200040e0f043d100750055282c4100c6440c1c40100183c900500070740041e420b0000c40c1540c50b095114036030300c030184140c0c0c5110640c00400039003960801c1c0c61050054000f402404140046510b000103881060300040c0a5820103580b05641408688a011a1144050070000820006401240041009071803402c41b0341050392001a107a114031a911000c2440c100000a00400c16030a0f030b4000c807001807003007000f6a00c140c18400c0507280200300d581e000e039803004544003542c0c0381e0b607065000c3c5020340d4851079201d0070680070920340a40d81d0455029181e552004114100c0e40b071603d40c50250b0b0002e0500c4d1a04407890400d40385000789600381c40249a00c404100881c6e81070300c032462003907000b643c1e610f003966030b00c0005441d01e00c407102003c1d410041c04030301409050702500040001d4081c5103022130000d0b1580d01c40b60441d0024a109054980d15220100303d14170344000281c1c000d24907240902801c90080e03038040c0c50401015411101e03056103 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 25222362 1250 25221112 25221137
    0x50c0111070e0c0a090f080d030b040b04090b0109050a0603080306040903020a05070e0f011a0702010e210102071202010b03060f04020f0409031806020304060f0507080c030c0601080606090412 84
    0x501c0710000500078a000c024081c18007100040d00c40d00088102000908000000a51040032403003c00032603800b40c3c0600801e100d02d04088020f044440400c90b04680c03144410091a105c174880e40c40c1d101d002e00c0812801d135041c00708034020358001400642c800f5080c01c405101261160084a8108108960003e020203913490309908105849201038400c0c02030020005100407846d4010b40300f54481c0062081680c1c03a4040070002241140c06244014000e0004030300650295402210042006000304c4950016011030b401000c45854198540e07500403a60100704540d5910200390761010780000d0040c46007400c00f00c1d0381c1d03083c020034650324149014041425500d4079044942100c40291052103200d401d4100034004032005102d81e10100a030140003d540351001c815141a10f01c240d88600d40042480c01c111510341218400755400202007144842c0d2003820002000c50044c4a400b500e031540c58940c04030f04106006015a0082030800b08010004900c203d0050b500751482c103022611700308 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 25223612 1250 25222362 25222397
    0xb0304021215150406030305040303120618020403020901080303040b0f040807060f06060206130c06050903010204050607060507080723070819020c0f0406031e05161d01050409050c01 80
    0x4441a807079403180200e40d40320182210901c07a243c41200080e00d030320001220441840111203007848080d0000c0c20501091000a218140442205010a0000c910a500c8110400b0011506a200641141e00280030000c40c1440301d4002d0040c00364501860a5141c20385502000741001081c0f601840100c0c400202082440e80958003900e40003181008172513268050304000f04014041c5501612800001810f43d407000c540c2041034075407203000c9140e09450f04105540c90f23040310103001c1d49950240808655a2140c10141000500488020541b030a00d290041c203150405071a65041001e01c6002c5030f0072a801205842e0010150036000d50344911070b013080582d0b401400c1143c5103060030000038420355640040e101181d69021601c0800c000e000600b08000c8802c2031000030140c944410608841140c10f4184817000c2d4040d1066404009510a220349020900d801c415007200240f4480000d651015041c60302505055400700102030036529080c1d962410188041d04000d500c000f0b540e080344 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 25224862 1250 25223612 25223629
    0x6180c02120304080d0b0607050d081b070b0106090b0301080a02061804020d0e0c0d0201021504020a0305030705100501050a050f0d080d09141029060f0301090f0e01050601090b030402 80
    0x840c541e95101e04051400021540c02801940b443d1801d00039411914601501122110307940200100713007111501d20140c1d441600100703000010240c0c031000b003000107032100090030000d00c01c0200c00c0b010740c14248041c00a00454019207a409400d00040c040d1440020703006c07035055011200145ca0b2001c3c2c4013048882118001d006030014000305440002c10006d0704201e042030b4444041d14020012881071005000c0c400c1c8000e401a80301040c10345103800d002a5494100c0d0010303201494554407502c1d01807031940180400c40e456071203080c80000302c0032140f14183c00341c942200c001e0b01e854030f4000041c030003984661a140c800c501c0d0500c0c03a400c07c01c2e84c1342113602d01440c2c80750070301c0862241d0805081550344481e002c1080d01401d40055504119442003c4400e6184c810355003601c5402400300c1c04034000b400e4444e401410401c17800351207134500005103000300a0214080780e24000300c1c4941003601c0310f00c0202601a03042405006007a030308442d4010030b8951401000740c40f603845000146044 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 25226112 1250 25224862 25224883
    0x601030308220501020d050901020a1202030a020403050607050c0607020601120803100305010c05070519050a0f11040501030b160f020d0c03030906020c0102120c0301080c060f0706060e0106030f06180c02 89
    0x9401558200e080010640141003c40001b100800c016a1000c0700380f13081c0e01c5000b82e0600084d901320086074110460b5806190040e046203401401d06490360780701c81c5070100555150002c03d03004160b48008580c104003c40c3d0168062020b807103554034102001c8040c0c0c2e03808030018045040440012007c0c4c0700c0d040100000c64014000780032182d02d000024081d9404080107454902900b030702c04c01560084110030001c80d503c20010250034006454030a0040b100300720844081c101100040d00580d078500409010314000d4901103000e00f4101842d032245a4011595400c2c0540281620602c64022601410500320343c2840c020821580ca07049006000280000f0044c51021803000c4d80010158040c04c032603001d0b13003414800c64840074a1100d07030340000d00c19a55943c1c81044242d956040c1f400c0540030300303568404c3c014100462555101c0079035039260403049858400c54010440d039541809007040e03075100c000b81001018180201c504400000030701480306142c49030101c401c224800c10040182 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 25227362 1250 25226112 25226161
    0xf091207030c1a030907030305090d0b0a02190c020a0306050601020f010203091612200d121d04020a090b0304032a050c0105030702060403140903010603030e130c020601030308 77
    0x68072403502c14000c015600038014400f11042400401000c1c41040f240117044150050008500d10b0f5030444882d44087c0b8596080721135041548001051006500d006408401c00581c6860001c0800403001103003066030b800b001403241038000981c0b100100c00040c2da8100c1c0020aa5695400c010f1340340c1901891041c541d507200104101002401080c090002c140c0780c240e44040c580d4560000800c80a6610007070702c02260b200100000000200d905400800f001e08020500c218a89581428401405268000ca440c4c4c0e81100c2540858078400a05848202d90840c100b502102e0000d10240e050f008401c103841b4000b01040a243c00340f03204817042c405c0c510100c03607803110f181e0110106890307165044a40f84603801c046040e543c0500c3c00d60784980c09550040480e540c032500c3c05c4402074124640036803c02002c01c400f207003580382800360001860094483d1212105110709009138036030f4081d01411700c82d240022001034981d010038024110f81d018609203a254032006403d034090301c00054100706 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 25228612 1250 25227362 25227373
    0x1030221010f080706050d0c0c02040903020c0307060809030702010c060f06230d08180103060801060803120108031218190f0203010f060f090c050d0903051c0e030f0912 74
    0x284460006146060350010309260b18031560750352070b07103588500d10701035030000c28800c0c0011020444142d202c0b0594021a141079072251140d07401042c100d038520941600140c012660021442c2010031140c00101110314201d4010316200c0d44080d142d005454000341000305400c944000c0c015590045000c201d17000078104159951160801800500711408045160b40101c4080d450300d4488401c1d4020b81e0011405840c10460468001c0f411f0621407595050565590b408a0390030340902c911000307000110700440d601c1280525034a01c0c0703001640251026070042046004c0d0906031751106811070802c5154543c2c4a2151000c0c47c142011100c3c00c1c0c90300100e00c050304042c4084441a1000c0d0760003034000300b04074040c400c0070307000b40e55481c0106011090b03160300410800106502030001c00041d40340090034500f0700f88084c42542c0c600602940011004190304980055020328005442d5449504214640b99488032584901410392170964080000c2001407882c0c0300c1c00c603410040140302040d980c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 25229862 1250 25228612 25228657
    0x705090c0702030d0809061b19020610120528062306030604030819060e0f0406060509090a06020f16140d020703030804150b0303190e06070b0a0b010302 67
    0x2481d0000c0a06912a11a12480d880c0032401115054011a802005000e0503074500482c00034001d402003854404890402501080c51600034058103d000541d018042031306114104a40d1107860b90440c040c400c501180580000d00001000b007150b040700050158448840b454007104000c00500242199041080e002000c5580004158010b1506150341c115906c8101c01d05907640c204560082c04190b4100103d11400001c030641c928051030410b010909a40b12481d071250341105444200c60fa08000041c0070401017240545005020165010308007841c1a90341e00741d8071520b501000e010380e0303400074211107159039034002c58811000c0f00b8039003a40700d030140c0340551080b205480b280c4610300880c1001c0314214400704504c0c1c112501540e807140b240e120f0b80c50f101e0224030803c1c422510642c2c7d400e030110294a080c0007801c4842c0440000030701310601688d0261a40c0f0908000c01d102e44002c02a00300014a403d0589810048605001840e00c07003000060f0000c0c8641d042c000001501d024400 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 25231112 1250 25229862 25229881
    0x70309080d0903031406130e0102210415020a0503070e030106030209040b06040b030c150c031201030b04050601060503010609030f02040905120c070801020a0e0d06090c030303050115091503090302070509 89
    0x1c40018803c0e1340401015130640c0440c0401017054881359801200c1114030040305400b900040c881c180071000041c90a412641905100321030010405071100603034041000b800b240415080300c240050105501c1d24901d1200108103120042200d014480f00c4d107103200361602c01351310403001741d5409002c1c8211410141403c007240102191170503c1642000c240310550700f00464603040701071025251076501ca0703541542210701d40100c1c0c10500144014442d400240305e07051800d03030080d400b4480c0c1490354142410b0a60411005811000501004000400c01c09a00c02910012250031150b040c3d81d0038075034030005020380b8040b10302900f24440c500b01c0080015045000b000200c001000712040d00d40d032410010f09074002c1c0580c070808074200e46134260071801c020b0707005020940320b00000995203002e030351000c0510200c2d81043c1d0001f03a0301c03801803215001458100c18902000d06000c40000d240107a140c1001c41c13000301c0e100030552144010800c150080000001400000704548103614106501 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 25232362 1250 25231112 25231121
    0xa030305060f040b060f090d050607080402011b020916111c1d030d050c150c070201030f050f010303030e100518070b25020112050a060501030b0f09040b070309080d 72
    0x74074071400300044015200c1c905449100e010001c0501004d00b804485000030000e50060345040e600000b9442c90100098402d00c00d01e0b00c200800d88400b0300c1c0e0b041c107000040c0010440c0701c00130b41c407100c20f5204101580da00d0540325407008080034500108405a4000c40d041140130304030090314401c03000c1da0065038800b11004a4815190b0b9103403001e2450440c0e050391041150000359805400400984d6035592051006018420890080764045001200324400034807080360000c52164020503140304540c3e0601901c800c00c0c0f4180014003041c2040b0000300c41c0c108040c8802014140d5030002c003041c04009100303010b0078000e51202080315281c440c80b00c600040030310742d054006024400001c1000320503841581d900c3c0710005240d4001b920040d0f0b44101c40e0701b02c024203906000030000701760030009841c01072074410004030340041000c52601001400b9141da28820354490301c1c2c014012030a0341c0725035003001e90043e049840b441541e111400f0036402044014009072001100062f009440c0c4040d800 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 25233612 1250 25232362 25232371
    0x2011115010e060a2904170303011a04060203090108040c050d03080103120f05071707060c0c0209090714010302030a0b090711070e041502090f0406090606110c0303031609080a030305 80
    0x11811041e5030304410041e1002d81070080f6035003c0e1240380c0c8549142440011044400304010703416160503100c41e4107212a1407100e07c0034145500000c01880f21007412110001d6006010b0005410705d420000040e4486c01240300c094100055000001c0c1441401140b010040101420503484a480da050040840303600b40000d9821010400065456511900c0c0c0f68807102c8140e56901d0600309180c0d80c07054010020040d0201c08c01c01403101d170022070301c075114881e0303c40441d032950068030182e84144401003100508068007900164400c11500b0449460360003c6542480c00594a03036542542d40001c000d02801e880e0040c0c100b00400010f59000078401021000903c1210183d52b41d40340003985194003228028a8103108800002007801c4580182104000051240710703070b85244d5010a08075582c5501040c041034440f82c0821419400c5443e0700000c1c400c61028001075010080440e40d240b0000d09107642c52050000640300461103001c0c0319015041200c2510401d4150b0704006010b441e003030320b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 25234862 1250 25233612 25233629
    0x15040203160305060d1a04033c03110307030b0607050601030b04020a151209060209030a06021806210705190504030b070e09010b0c011d061b040315090201111501 71
    0x1401301d81070f0302c0c1502040e0b041c0c0da444555420610400a041c800c038103c041c004605020107525540c1c80c06071801480760150107205841a1350f5102c80318134444100c031102015003810b1500301c40c403c0140801302225801030260502041c40d506001c0460750038480e00380040c0c21f07030041c0301c004403c2042c00e009150042c0e008494030b4508513101c80111000d020380180303440100715405855684090140c0200504500551006080091b1040801d007030940881d412903e06070300145010700314040000400810368207444090600321354409100d4100101405030002100e41d20001c0c042501c82c41c103c414045480300c1444407127041c40e001400c0c0390800c2c042110444018400140c140d840f9000001890030000e000ca0302c1e80c6d1a10703078182d180394806641f25403655254004070100c042c5c40e050007007401c800780b801010585000c160741d006510050200d003141c1e140030030081010a0141e0342e0b00d40005029070700080c40340640d20050702d0180c1c0c60b03010b281031350141c81107101e1500070725121a8100c0da0001e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 25236112 1250 25234862 25234871
    0x307080c0309070509070e0d0b060307170709020d09050d05070c05010806030303070324030807060501050609100f020c090108010f0b0f0303041202060d060b0318011401030b150402031603 82
    0x441094640740422601411658800103042000e032616070403882d003142c02810004800100e840c0800c0c040018541d044d6821013085084c0034803420104600c0006102c1004a1454480c05102413030319103100b0310a18441940208034082600e407551702c02c4487d56448411180d01c002c4886024010380c21810055a030b190380002c00161550290a20768030842005000d1880c1d03944154054004120003040000050021401703901686d60403a50380c4041d601800c411500d40c2c40d249032030410703640e0581285015190a20200e982c070b0b1110003008440094134203009151540c0d10404920307080400c0d600075031040840d80002400c50301036202c02c0340e220702c514080c0081c80f10202403141c450482d41c140c030313010350041000308030216800c0880820584014555441c19001a21a030103072075564000e4414554004203011040072200d00d901c0ea006520fa000b444031800600e10408194030500c0094100e1f28000700041f800400265084486a8010401c648a0810040780742e00e441c075103041100072a280 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 25237362 1250 25236112 25236121
    0x309030d060e010614070c12050109060e010b0f12031e09030a0f050607030c0801051504030813060207081c03020a0516060c120b090a180605070c02101d0f030703050111030708 77
    0x2688100c0b280b06d03404c902244459403928144403081d12400700306440300d5580e0303406000060103030b0041143c081000000810042074a0301040308085a1980c60341c801c0d6484500c1824150000c01a10f814500025001081c556140b042d00403e00c901c0502075450b015070b445990030001c038104071051060241d0120340f6290743d00c0b84260102c0705079441303050100d24140010419858645054501110811a001d0a107982d0703a80305810ba810411102950f80320340744040c46481d5040100b60020021800240030700d0100304145000c683c4500035000c00c06800281040610b8010012540e41e4031403008242c00c0704207a030401c44001e04d00e0340024000680c050724561001c0c0c0040c0202446184014902c1d02141c941c220400000c3c04003940c04541d40303004a46180c0070400d50301c2003d02c10b61040e02c4103904103040e407041102c22030300340300d802d4180300030440710866001001a402c40500c1080d120105135441500006e49482c54a80c0700400303d40c2040c140700b0202e0301d000061f6028003400d031149406601ca = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 25238612 1250 25237362 25237397
    0x10507170705131502070305060c0306030f03031501050318061603060f0f0e090c060403050601060801090903020604020d08040510091401020a0512070303140a0504031e0c02060309030d060e0106 85
    0x3d03400c54200300501c0e4407050040403100f00858611659500440340a50358070b5850904219003254a0810420080200806401d00f44082c002c4a044500518034525003104203494005000c04090f04214000c40040c440700809441c0320300202e035020490b0240c1c6031000c0c0f00880340c44030503803050000742800341c0010b02c0b0b0303180b00c280015240a0b51031540c0940c10030300707240aa140b00407c080c00301d21800110882a44a180c0144042e40c05040606069130420038060491407041e484000580c0c501035458000c241c0c007045554015074100c07403d80c803c180f5410030554601440d04420f6000f42074018021025802240c1d480403624032105010252000500580c0c803040180380103440340d084280c1480b084100c0c0001002000e103e400c00007aa80641c4280b140da031882121807490559481c000e06c4249070b000100a81c0796248032150000068003950020104641c846e4000d01a590100100311084000c0c400d40f840912400c90410003146d80d200f0700300c4410301c01e00c10f040202d002d5068440443c01c = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 25239862 1250 25238612 25238617
    0x5031c05011202041e020a0f0216050a030b0402030703080c0f01060e070c081b030d020a020118020a1503140403170c040308030c09040e060f0105040f02040e06060702060c010507170705 81
    0x414010708002d03100019000d01000d4181a900000f94055045010343e81022501c007828149a45075580d0440440900002c2c1c80d15a40511448c40111910070404c070755a40c1a45076011740354401840c09083c2c45034400701380340c152142c100034201800884c80308600103000a40c0002c03400c1510081c0034081e526580310f0044d107019909503002900c5c040c1520040707411000140303c0c00501415130b0104842c2c2040742d600319000a0300e1030f005150005003990400e80c1c24054400c0004009a0ba204010303e16400100700791034510440340502c00a0780c003007044074001e520074101c0b903500340703802010f03442c2c1850000e02c0c00300340e0071240034150b48907800303d0f003002e6080007954240c075841030741207285071103411800e0500c3d0465002d0f5684262103407120302d420902486014015046071380d0300d00c1194105020481501c1440152486180c0b05100c10041c0c0d144a440b200d80094098600e00d0b6104401d0000c94030a11076040201459804c200038071070350f80e43c0111038050790712844002d60020b13201d030cc00072a07451 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 25241112 1250 25239862 25239869
    0x20102100c0806030114160e010c1e111f0f0903080705030a03110304050615060d09051e0f1216021c02030105130323220f05040c0504030f110402040305031c0501 71
    0x301f610f00e50220040d0203030810b03860710141410103189400c40c55590101070401d0b10390710f9950b6030520341d414041281580303d24642c440111101d8110f00c2140800c58401c0903041c1003101000750004540e58424010040c80d0059900014266aa50381d9401c0040c1d41c0d40c0300401d2500060310700120340440c196044180c074021035110b0003a10f8143c0780c3c000c82b4000420812840c943c003007030402401038100498420807682c0c510510141600b06401c6005a90458146128959940128000302642c000105044440c0c01c01d0040032512142001d030550810408030b0b0000b0b404c80b000c1c8000707403807204180602184c2180708900a022560315a900c0c028121501000140801c82040c426048003805424039041c07a108050280c3c10140580a010fa502a02142662846107035600500150560322100800741c042903d080c00703541000350000305075100740c1c8030281003e040504058208106020f4881001300000c00c255240c0da12820040d45a510942080c900351044100c401100860360103444c1c1203 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 25242362 1250 25241112 25241131
    0xf030219050901030609020a05042903030306030d03110705010c05030a0609060302060a030216080d090b0a020c0312090106080601060e04050906040308130201050702090f06030d0201050907050607020102100c0806030114 96
    0x702e929550319170740900704c80d0750100e0740300c248460082520344583c07295a808280300442261005100d225511440301411200c6000e90001c00410109890005508001c0810381c03030700107011000502007850318056090024565400e0620454001d64000e0245009800301c42d8100961507541343c0c140d0841d00c152100a400900c00d01c01d283d220384c000c0d8040e110064805020365041500c40e030303409840c2c2c0c0c040044400031513a02d880150600c40e00c0c3c2110b0380d004402c3d032000c43c07401074940c40e281c2e568040d0a1743d0080c03800ca100002451700d1303005e4010740c00038441c1e10102c0c2c846585484010344403005a081150180d8600030010385041000250503003d107406884001c50781d111741041c4241c0c1794041130282d06001082101c6801030311040926403080042c500314640030b0a05004140c2401d21003000d040031a070410003800808a000300b4000200c42085803510b07516072003480140d007450141d1100500e8903250849020046800025581c0b0402049000700141100d05640343d15048084c4c1c0d62400 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 25243612 1250 25242362 25242379
    0xc0f0903050d050309030d0509030d1a0d060c18030602030109050901020a09050907030b090103110907020a030e090415020c060105010f02070806012303071205060a0b1c08040801060f03021905 84
    0x58003400f0344011504400b01505585c50300780d00c90843c0042e18410b881d8500180d05c00110040000e01c90320664107a40170341140141c007488620005443c0c82162800944030542c1c0b4003441c0103441c02613240c040800e10015000f0032072640e0f414402c009410901c03980c0481c42c1850005102c07802d040c402c894000302c068451030b1007181042c05006071010300a0a01041c55915480e12151342e0328840e8141c0203522820300c0c43c0c030008103801405021040540300310f041d9485405070000080d00035040407540c480582e8840040d83d594144100f00032518800604024800100391003910303400f0400d941030380d03c2a292203a001c25140422a42c5210a105030300382d5404c001c0051149003441406040c000010f40c000080aa0640000904152955101001500d071034914170040240601010750b00c0641c0c00000c0002e10548000300324181032604203c0404402c1c0f80c1010100030a403800d503009415401d0080159a846440d02c040c594100e000070392003407044c2d201310224001d000300d0210075184007602000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 25244862 1250 25243612 25243633
    0x30c0f0e030d0e011407050109110108100303030b01030f09030807090b03010b04090203060409050f10060b030c0a1b05060106020705040f050c070f05120a03022502031f06080a060c0f090305 83
    0x150f14000c2d0710b15040c100003008021405c0030f80031501600d40300f801440001103076103043c0351905181c00c00e408003a046c009a1010000c180e80003580300c00840307800d410081041050341004800078107180c07020341c0d01e01e403815040d10103151780003200f00d01c280e03a662100609507442e110440841c0c0824411921303d6031013040144404410b0b5006590070038005400411400116540c450a149801c10745105540c009105055200c1e42402224000c0000044103840c500b03021901d14028824414020103022206500260940541851038a902c0c0c111060b10384558660708025201c0410740318840c4180d040401c80c0341e054450b4802c143c015100c000b0f525241c2009030b0b88054442c20441402e4600740145519100c41450000082814030a1a900142e403105000728202448005039003001c0e0130241030a900005032000551602c409000c54005541090509c1d0f82d034000c0c0540342c010051500071680941c0402049421103025810162204569054221000c41e000b9080c0e10003d000c40d4440c0041c0c1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 25246112 1250 25244862 25244867
    0x60f05100501020d081528030515010603060303020607030923010c0f02010b0a03140703080a030c120e0c041e021602030618030307080c092d031603060506010e0907030c0f0e030d 78
    0x2403000110703816030102e40025007c8070f181c100600d68070954281d003010904038040280c0038200e40c098440d50900300211425a1802540e5100041840b0103050359160340400b03108408520310b43c00004c04a8400301e1030016810a07000e4402e200e441d5001c034200709541c005290040c003c1d90741d214000707000d44e0b8000c2d01c2c60311120a03a0650101c1c02044e4002d4540c08404148800c00030b105103002524042003000242d03030000c2c40180d0080c0140002e038607002442c0e2140c2000f0a00380101a001c07540460130030002511000a400048200007000d031001403041c03240c0351442e036501049402203099607070f03954501901001e03811461320049070580081000440d450b0043c0350058100246100150030051881c1c00314242210403c901d07210011002d00030051100881150038002c030007580a00740488000e82c1e8852880a1070200a28440e140e00c0041c00a900c01d01840c480003500400600c010f00f8400c6014000301fa0a001080c001030300c1b480c401072080c0c0694014007a410000d00201040560f03040e08 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 25247362 1250 25246112 25246129
    0xf050606091302091503040308100909050d1404090903020705090c030403020607050a021006030b09010609020f041701091a1902030106080606030601030e030c0d0e0d0816060f05100501020d0815 85
    0x103036201e42041c400d90401c08245001e181f00d54800e84820030a41400ca12864950100d40e10070a041070074080075000280c00400da40101c3c0ca001c0c10540142c20060300503241c9805240c10040c0700074a0910010103150340046c0000890b802610700400c140c50701c0c081401144400c48001d40568040390101e80854855002070021000d20720548564108007010780c41a2001c9600c2500c03108020800d002030b0308020b00c00d0710f00400328804110b251500c40b4406901a000c0c40c4580512118907881e19040740c1001e40200740915801422404454508100350407041c0302a540421104000100c6002185492003100d060310b9058607001d42c10f54440c41042016400144a5410103031a180301441c151020800751601e103295001030170400603100c0c0014020111800325502c560101c43e90400410f4000d011a8820071200300d0580880500d414500f015041100e8140340c1c191800c0104504103600c0c2c143c1e501901c1090782920f50031413440c8400c131000d40c41500e0200303801e00b49111000c050700e0016103 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 25248612 1250 25247362 25247377
    0x51503030403021c120309150e1207051002030903040303021203281401060203030a15030803010e040c0f030c1706100522050f011e08030d0527010f050606091302 71
    0x4c81410b9419a03149803012122086000129407141c1058041141400103004411540c2404000da80c142081c500d654a226a0304141c407548001506c1c0b041c0141401100010a071101c0155503c1c14400800b5540758024401900103000d042c406c00050200300302101d00a02109803022046218000300b8074504403880c1e000340280b43e13120285080070040c500f0750340c0282000c0d0003031922072804040d102c05948028411603450407410800780006101c00003540c0c10344000e0f20080600c7e41c1c40b0b2904810301c1c07210341c020a4100044030400410007a900e03100405a450309203500049a10521051356110302c1a1003283d010301c183c00051107d800d00851001d1011545400c480070038180c4184002103580c15900510300741d0744000180843c4613140031405c000041c5000081c00d035403803d402b040d1280141d18240141a807100b01043c1010704142d101c000d00c00d8080e0000451541500b1500d000340301c103283c03103022036003420001000c5141120650b0010780700070f00b4030700e050042403003c0c40080d4001407 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 25249862 1250 25248612 25248649
    0x50306010f03020405031c03050c120412030209180103020a090b06030414100204120501050c0a0512070201060e0702060f0105040213030201030b06280806100512250f0305150303040302 81
    0x440003070300350f50410142110307c081d803000000017040c002c40207082e101d000b0262100e40b40304100504054001c2441164000d41041099009480004044001c0d201d0b82011982c40b150404444610801e030700a164101c81c406c5503d06041707940c0c0e440030815a00041c2c101c0d40e10140503c0007602045070f02c08460360710040c4409548110421106500c12a001900020003901c0c840f03560004002092042642146860083c5400c014402e000104a07100b00c0b00789201031682d510109050318000d4100c80c001c1c20800b02ca0030032929107220003c1d950720040300c90007800c1c64001c000003079605241c070896944850841003d1110340c110340054010300f0903030704015080b0004004800280490450000e01e00d0320030000881d4004405100500c1418064150f5200302943c0c01003d080c0b0340c0190448540440c0c90120170300550354124100340e00454020044582c5100f02022022154403040c50b17101418603440402c41c94540d40010310030718050030100ba4141c0c0c0308110510152910080252828000c107 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 25251112 1250 25249862 25249867
    0x612071e02151513020301060306030311070b030c0c030f180f0406061e0207090504060e0d030612060f02070501090602031b07021e13020a030b0f120a120c0602070f020a05060a050306010f0302 84
    0x2404d05100701c1c0c1c0b00760b0110001036580d41c0140105544040900c0e80c121100c0001c003580b40c2071440d120442d00c0003504080010000044004410200b482075880090000620783c3d04d07031541465520488440e40101c138851241c2c90b2448045140c01d11654003a00c0039951084e151281d80200b079100501c0400d0001c0c254403401800142004450143c0fa101c0c0340b041c071010036001c065240244ca4841080c560006041c1000424003010220200180700320382c0044021581c80e40e45c8408030024490100007070401c0d400d104010061040640040d0302501b207526001046c5031090101002074029084029409164040c003d00c419000d000e08555122004040307114207424881104100da020602a1000c030752111001380292a052900d8140c1080c141c0d050251074654400c901d0b11118000300c020f0401c4448505440306a01c03400c40c54090550000c802c541c0c07424541018507640c10003210172445004500b10104090030504290344012820352a51030844c0c4606d001580c8210315041d1041c1015406d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 25252362 1250 25251112 25251139
    0xc0f031f06240801260f070807060f1b020411070b0f010801020c0a0f050f03040603060807060c02010e09040303020d15080613030507060506030c060f0a020616020304050f0612071e021515 82
    0x1b44a614041408903008011051421242d130342000860ba02c80e505204110207841490740d0803000d550794084042c8a1415120391600c001801814458217450801c403000c074000041107031000383c25000380c13402c1141000f9030381d1b250900f0303081c2e10440d0203480e4a508070b42800b00005130019040c040f410700c1801666118640101c07100c0c41c40d04141e002d0300008ad2102010440500140903070000b801d03051412140941868002030f14542000c28983d0240e50781800150600d803007a810790700d050b165003006001e01010201702001911150040100f10f0281b00082404041c500f0b58034460760307915455040c10281e0355203829004003001441d030798043c011207040042e9544d5041c000d044448203460b01039100c0e020300340002c0c81d003d0020704609200c1750b02040b02d800a9000000d4070f084038000c91320030b4140103540300800c0b69405400b0030130b60400e08040038405542e0704103001207030708a4a280040c22902d0042002ca0355600140902d1801c001c070720021511300001a200d00c040306a01420050b03a0004 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 25253612 1250 25252362 25252439
    0x6030705091302090705190e0f0607060f02040f180501060c0f030c17030115090315020a09090f0c02060c030c09010809011b0206090d050304050c0f031f06240801 71
    0x14200c1740c40000981c0007400304860b2141242d941c015030306500e026801140c54801145c00c114082d02032900c2004040b40c0002000300581040b50703228480c200a40d1100d1340c54540304543c040300c0c051070705c072142c4080d20101c012443e441407034100c440341d41c0e62008031074094031036440340082d8940c10303800c10942803859404554502c1d00075030081d200c0c1d0b44a583c0c07589000481008a5092101e0b1001c100000702c08202040030294886111581c10200503903c00d50a14180c1c2c640380d00b030b404500031500b0484401c42003000c0b03503c0b400200f05c0396004c2d41d0315523550500a0b034140c0310841c3d142554000034407030064a03510a0398255402240100002020201502109060004400c0e5800140e0100080000000c020f208007018100181070a508504250781d0307040c0c40d0412032071460300230030782802d0b503804990307042002c04078054810314a40640038030003c055000d05030314004c1d003485a034148590540d40340c4c2030804802c4102076035624440d80e400c0c01400d9941c40c0028154511500791030700003140740407 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 25254862 1250 25253612 25253629
    0x20a0801060b030402040c030b0102060c0c070e0414010b0102031c020901171825030f02030a020d0302010204050301061202100c081b060f0a0506030604031b0b070201020304050c0906030705091302 86
    0x102c0209425200d01d4144104030503142d00c010300e0410581800e5440d041640c000402c1c0c0d03048216414040d4488501509451620240f42c1c0001d0860742c0d50400d01040c8200000c9904204012000074000501402c00699583c4035160071503c800c00b000340001c0404034503502805221a05151080d10242e80350000310356050b00303403510f0300c0d1910705200305a030a0008003e484c050100003002c4a00c5408404001c85d0084c80500c0058605281d400301c203811507400740444d1803001d50007021400c80c40e416082c001d0003034019005842c040c1d8604100499141001604c252403154010800210312406000849203c445414100d510003020300c01074100b00100800701200f800000010400c500e060300e0280103411010742a4004189080140300c0b039038402250496210703806003400541600d0a45d02800b81c0d000528001d07102c600c520080c8284140c0c103400850080e401041114040014541082214941615002d61662190301d0821460510001e0107a002c80c012000d0200e80255801140441 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 25256112 1250 25254862 25254869
    0x30c050f0309031902070605070f050102070206070516050303031b161203090308151804030e0301051003110907020d030903030f09060b01110307030801030b060f1011070801020f04030609020a080106 87
    0x1a040404c48280084406503858429180d0348002d003092460300901034401c0c441da641c0a081c04000c0140142030010940488440c241d000d0300403585c0d14074605100b46c954000c4c80708030f07061b02c0042c00d00141c245000030540b805026801084040003058081d2403106500256000c0c40c1504214005004540d1013022001504040e0710040f402804030303d030081074510300500c4048081410152061507031aa5409600080cec400f0200c2d10f242c2d20366080555a1344085100194590f0904040001c50300c42000e0403030440b0311035165140c4078078401c41007081c10501190010300590103180e8264107544260072a0f00c0c002e002c0d0a0000d1100403608a050a03107041041c1600d49036140c507440c48032568440c501800c030080031005103050500d2070b03900914015040c40b0161030000403c000c00c01da0790b02e401d29001368500041818800c0180007401900403005000d0500060280800c0015801418001c40b40038114031b0600524043c210340c0c4090041111366000e03078120f1410300000c10045024031491028 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 25257362 1250 25256112 25256131
    0x1b060902090f100e040804050907090b0309010f0608010c23070f120e06040305030a03050613090b01090e03090306041203020c0303100311100818010b03030f090f04050412030c050f03 80
    0x6850003590400f0003c1581e400b240703901800c10200000f0941e088141c80c2610300c01c460030340d09601e800da0215111100f0750485841542e0010a00c4091207055004840007107030440d0a2202950b18522a0b080f140030001da100401c280c103d108000c1007a1402202810408002d0f50f41021507686803001d00710125075049800c0911401c070510916004501d988541c1e8003112010300d01401c40d5156501c03809442a40340034940c0300d4010945541e03071082400b85808000f001013005507103134146503007002003e110f4100da0519001c00010300080120440340084005401030030652101e58900040f00e000d4500102056401c3c800b084c4010020b10085000e20003a08420b07846908508181020101e5545c4143c400d00301d070b40b681e54a864002e104c2a50010481218084e0f50030300c00c101c140074005200c101c580c0350000094144981e4851400303008198000d03960600544035020a02c0700b11070b010380d006000382116a602c00e0f001c5219801100620005240180c2400c2c16140d034100b00c0d8000313540c024034 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 25258612 1250 25257362 25257391
    0xf0c02030306030f0706050403240c05070210050405060a080406021308070e010b040303090608060114030a02041409010302010215040302010e0703030905040c09050f190305060f09060709061b06090209 88
    0x9032407404004640c2a11400d40117008214a0700b1005010703840f442c44002c045003e650910720a84114075914501900d554505000c0361b03501d031070000d10396030040400300e2003080c0340041014072901c20815542914009003201e468102c15480903103149400405c00c8904079000c01070700022105040204cc000c0891000070b2940c1030405110b13001035034050304041400f41080c0001c10100350700922000480340241480c44643c1c46032001210395602400d40034480c464000144000c2414580c001e0084401c1c2c1048001141c0c101c1e001c014256a0178400640147d002d950316180024800d090650002d101e0700000416081d01e0034110305055680e0b00c298040b0311400010065414180a035590304102c9152240c08503040c1000201518070704c0d14568003410306200030013809030907400c0d80c602458000b400c490051802c030aa2803144130045419000c280289000b09142034000c00c0d03244161400c680703d0f01884034035480c400703d400810900650781c040d1030385048400360b00e4804180303004d007011f0340c2801c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 25259862 1250 25258612 25258621
    0x11d06060907051801110a02040507050a030b01020f250807030308010302042f1b0102130311010c0804050603060f060a0201050f01060906020606091503030408030a021009031706040f0c020303 84
    0x3034800200b100c820302100b0000c400c4d0802e050244906005400d00f0000d050200307000d503035803a08102040094126141405121846030030034042c100285040d0313020302c0310301c0d0b80c90012626031a00844d0030010798840d100040114503669188400901a4103081c501346551300f80c5545022402d42c030940c042401203005005605042c0698030b070201c040700584550717500c00d450300e002224030f0003645040d40c04c0c0822808051064441d1040141800900940d1a518508040302c10542584811907815102401194440d40a0400d003400c01e81c01144180c2032a15000034080951700c010b10392980702c045090140c44940d2000081d0518912a40c00010390f49018000500c103500706800000078401c3c10f41041102d540d0004003568020401c0c1d4031001c554581c01d44d03100b0121240c1000c240c0c58000481d000c2101100040a014006c40c258200c8000c044d85040b140c003141d070340c802c0280c005112181c134441c1903001702111a402a03000390001030305a10500340340c41251983c1e104500140c00000621 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 25261112 1250 25259862 25259869
    0x31b1c080609010609031109090c04090308060f0306010e01140d08040b0307090e0c0a03020d06030c080307061116060e0c03010f0902040605040507080612120a0503011805040201050912011d0606 85
    0xa405401e03a81865031140d421501d031000d15800041b0f03118822640900020380010381408200303c10840540f040c0700c00c0331149005800c9190441d205400340010680107119440c00159080c1207442d51110540642d0038a20380a6610540c462000e811281c03040b041d50010321000002c10003030001082403616030030800c500074054021948603050424540050201e002c0e40300080320b04040c580d0900603074818141c1c0c9240c000e44525400600b10820019000030420b001000401d80e041c41100200607031044a803000c81340f401100714155060a208030394100107601a40044c4d072144901c0100c681d5012003400207801c2d41c0c581183c500c5c0141d200e0203a841182094003845003d840f007200c046c0510320344088000c07c5075034001c0c0072a200d40a01c80465083c10b07000e001402681a000c0d10080c1c2c1c038a403040c4007409030742c002c1c4543d0040400007400c88294204620900707014540c16591649010f50b80e03401c1004465400700303441801d550740d411402150310201c1200040c0044000a881e8900d0070b0002c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 25262362 1250 25261112 25261129
    0x31c020a1e05030105061303020607060204060f02010525020a050105070e0114040b0306011404030c030503070201081305060103061d0609010c0215220303060302040f0e0105010b0705031b1c0806 85
    0x21400481c0070303440d08001500241a20b041d52000d0f10f0080c1c60f8500980c0c0e421403043c02c1d900103500040b00140c5e80090000356001070081d5000c54850003d4002213003c00c0b401c854049034031290460f2030340c0086d0f03200c69400b04d8807001c0118501c103d48690000c1d4560f01d007140c000b03a81d6840400c10066144808e5600045454549040c6100d003500b8640717000340d0810030744030061006040040701100c0c0d001007988402070314003843c0c00464403c0b40948900e00340c0c2e5607a01c030000c142d0104922100007444000a800002c950641c00030103810075910310340c5d41c90040d280c1070000b840e6210208040e000d9810301003112500c148418000402e00001941000c1d0416050985408001c0d500b1000c11070001c0c180c00c2c06c903540745100e5101114244846c10200e00505c50b64200952082c1003143c2c40f6170030341c1c00e078100340a65603003c4000c102d26640e401c81c1c07107014803441c103000b00360743c005102d409003c0c51903041d00910900306206454042000341d80c02071100e01019890004540b515051008a0406044 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 25263612 1250 25262362 25262387
    0xe0c01020d02060a05180a030c0614090a0f02030c03010e0c0a090203090307030c03170a090203070603022104050c031e07080d090e04030e0a08011a060a08040b0702031c020a 76
    0x290000003040350000303443e804018011005075440b036010a914a803120b42014502c0800429510858a6490300400c003503112030040e1105418090a00b20300f9600101c80d47c05000c25000034600c02100d0380c2d40d0f49084182502c1641e06000b44c40c0800e116440038011003008500c802c000c0e0140e102e22500b0054002070316001505a18810310410404010010032191150340500741154803000f145802c41d03aa02c60f008040f40200d043c070091051000040e04034040b1244220300307940b101034907a0822404c902a4280e40728880c40e40880d02201c058080091a4200b4001c0b001e5031004c80c181d001081c50001c140708e8086110116540c140b0010400b4008200545078400c00f0304560b054481c40201348201501902d10b1160048010508150141091200030a00503290340342003903503090102d00030441d444806000703041d40da1040c1083d15111046034030b100e1090321420100e4440340c40302031134100010301030003d507c42000001000c01500480c5130804801110141c0e803045000e400420800d09030300d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 25264862 1250 25263612 25263617
    0x5060a05010e04030804080d06180e1218040e06090a0c0e0c070206030a1806020a0f0806061207020f03130302040c0503040203060a1104030c18050c0705070315090602030a0e0c01 78
    0x200140129410850050f40058042c68001d0301500c072070900081074814880c481c803485142180004510301d070400c82d00c1ca1048503020030030040407000310b01504d400d140c00c540040064204800075081a07c01e03244141d81501900002c0c03916a000c40261500200343c0309240c0c2c40e44100f42c424104214400079201400034034200701074508003842200300600601000a105a002000082c0000140d03400070403084000e0a1580c901002410a140254014aa070100280c10180f850310654050025a4020507000c0d14070352803d0092007207200340c03040181910086000320b41802040000403c00ba10850780556925609586184104011074a020100e8804c5c4035050041101680e4040f6010341d0010000300f010403146030005105e507561040d90002030442c3c0c48070303030045048402c90514541c99005240200a503031030310748010f0040d021351180107010b940000d50a200040d040c0020000a4180c01d030049102d081540e140b4003a40c108641201c00c0c69918414101e5040c0b0822452a08000c20b0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 25266112 1250 25264862 25264871
    0x120408070b22060f02090d03200102040b0912010204051306050906040911010f020c10090e060f130f11040b0c01050106030c05070311030403060c080f06011e030507120606020a05060a 80
    0x629150b41a00119040500202d0752415000440c07151034044440201d0300501c50564800c0e6407401401100c82c2041000b51000f864a03103034600300052080310203590a50ba0001d007426101004c20024039400d16112195540038480065a42c65401d44021044400322010603c18289000d000c0d1059005107128815414124100e022034005059611045028a0300e41c0300044d00030401d81c41c10b4884003005403c0005004c41000c0760354020700ba101070300d010010103140c58540c001002502d580110310103a10035003843c50a486404541d1120614401100000c0790600200f680f5801e6604075074490284440b001903120b0800f2420f2040d80e014040c203040c2000403010301c0d600144030b0301403200d005083c0031114406441c1403a080083d14019544000c0c240b02e42140090020b012920580d50408000d11510114996600030120781546500021054441c0c40d0924801c8015200280400060002a0008844942042c080e20000e0b151580080c03090891a01d0300502d41103005000030351f6180790 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 25267362 1250 25266112 25266151
    0xa0318020a030807050705091303030e06060603070f0912030e01030c1d12070305030d090209090c010f2f06071209080406051c022101050306090c04020f120408070b 72
    0x1a141d025080d00c1d0815021a100c0406182c140d1401c215900f29940c0454110200719410300075104181c01a8441c0c2d600340a1884200410f5036101404d81c0c0c40780e406201480006c0603544504146190070720f01d0300e072144049a403000c400d0a80d01c842d620590000c4c02600c410285940c050142440500e40c510380124400e98a802404cd00c001060030b242c42101e045040b010000c0b800c02c021805560814280daa130395103029045801040c100f48124000c810101c0011000c11021640300050101030315594290b041034001210400e40807298036410807901d207188100d08104001d03805855104400800403428520b0015082000421052030070030709041c404c00029103c50180c0d0b00310750140c106280c46d6020000503031025100d42400c1d001140c0302140302031900b0004000801542a40100c10718103036203031024103803201c2045a9601c0d07280c1c0000103034002410968020800168601f00340d50a140f070019110700c001c0401c0e0343c01d80c2d1001c00030441c90188004180d140b0b400030341107000b09802042c0e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 25268612 1250 25267362 25267369
    0x1a04090c0207031a06091b040302040218040b091504020a0318030306082808030406090b15010905040203070206040b07050f0c10060b04080d030507030f05160806100c080903030f030c0a031802 84
    0x240100b1a10f01c1c003101c1c600041010800e0002d45000d55401001074dd104d0310364060320f00c910710104000c1e070300c2942407160b00e00c1d450408504560180311644080300d4403030707070b40c2c024000a503000078525410103940d10b0001c842c0340403445240712030b01d11a0750003103070541c98003080c1d074074003030f00c80346503241c2d2050090103001d4401c0341c0e4040d040a01d501c12100c6487e075840f42005402454100c3d07028121640d000d0401903200d08038007401c112048241c85200815480720140412400201c1d10000560700c40b030041804290a0240e02c1c0c1e1224007803424a2810034400030401c0d40d034010305065900e41c0c1c05902d00e40a103542c58060741c3c0142c0b405c2d98020341010b01d82402c01b903a80414030f40d91020b2540d2403021600191003600964800803010b24103204a080c036400080c582c40c44600304200152043d40070034100d01d0035201c1c00304040c0d400d50798082c43c02801e440701841c0d54860b8400540c944010061001800386d804013842c03007964210740b407039101d03582d440000e0142d403043d11406a051035191038000041e0b4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 25269862 1250 25268612 25268629
    0x30f030e0606031906180c0801050702030405090105060705010902060d020d18080f03090a021009050306060406030b0c0a1e0207080d02010c020304060e04020715061406070206041a04090c0207031a06 87
    0x101d4441c0001c0c400c03400e4101038000340b0340c42a01440541d10011b043d8207001503078a0310411114000004c20043d61045000c82c0c590103140a140c0d48251000c00400c801d14210000c0c00500b4020800052101c07640d43c00500c0c0b541c412400c500f003036178000c151541c4591291040e025443c940503003404584170156520100c17031280d0f407900c0c1c607044000300200c4c81406c0e0400c41c1840890380a040200302a804445c05080d050306445200d00c24030a800000382e490402d40907504c100d035442910007409440743e280b100350350b8000151760381c2041141ea01320003040d4055003842d400a10250080d01c3d4490401c4c170f940d0300741111038100405583c1040924907809a00204880c201c4226181030305074181240700190292080c0c1b1005485145d607070140750820402580041e00700d07044844591114082c40052214a000b002c2000c0d42c407241c1030004015148001e0070580600000b00d402602d09526400c8100444445020050050b4042070301402080440d2070082003c4891104441062512000150281 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 25271112 1250 25269862 25269883
    0x108070902030606031f120510060611100b0303130b070309050315010618030b0a0b100c0803010302090414060c0703080c040e070c05030c0304080a06060603020705030304140c060403030f030e060603 87
    0x443c000070342040c4a80306a81601b01410600006040c0d258441c20300594480303030003c9825680d89010030010381c286c09802e040c0404039012001d02419520b212003d002480101074030f41d014001046543c0a1720385520045014060b00c1548035105c1c0c4550800801c0d003460344d000706019038003407010b2161848400c1003003811a8454500f00480d0350004003203503811082c0e41d1008000307003003072804d00100c43c01e1504009035501c000e031400c00c0078107400c0c00d089900741c0303032a0406802c5841c00c000500140c280110b4090344171b805180160355007100c00c50726038600300b811100d80030011004682c04042503400000c4076001a41081c038181098207100111a00e428040c258030244042c010f42e120401100340113403040482070805607a102c070303502d141c02074030b8164100c1c0807a41c01b440c0541c0442e40e6402031007a9004036401030002d42c103641e5140d60700c42c40c00c483c99442c920f2910803403030b1601d00c41d990b2500a0006d541300c2c1e628540f280007a2007010b01590340c40c100c1240f0a13045102081243d860004110108 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 25272362 1250 25271112 25271131
    0x606050304060b04110a0804020108070f050a0e150703080411010c02090a0513020303180102100515010507030201090803070c0308060a05090a0b060c0109030504030215030108030901050a0302090a0608010807090203060603 97
    0xf50f00040740024003e15505024a0302d10b4808240c030304001e1307040010b081c0300354000e884155182c0e40f00e8008550340c0e0b28004000d004640140302003a2a180305d0034084c5880d030310117007050481810382c0c240c48100d500107850032000511040100000c11441042c00014681d080c00c0070f688560442c0e0001d52114001884042c20030395450020fa03854078200b609089054000e8180ca6440702d00c1e10004181120b050728040c05807150300e49642080003540324032481540a10030310a0090350744001101c056011040aa00b15900e0720401400300300908000d500648460b101c9107940c19417840e01410b8840000e0050b481841494400c00803501c071401502c0c0c1c071040038000041c3c800494000202c2502454001408561070412003108164101e4000c0050b00e0003220b0034101440940e200340c5051109001c0c0c1061a0804d002c0100c048d4090f030050810b501e41c50402604161004000c5010b2044e15030203140041d442c0f030010007400c001402a000680401b5038158a18682a00030506505c0050300702d205 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 25273612 1250 25272362 25272371
    0x90603020c1509150f0601110f0d0806031509060106141303020108070c0b01030809090606070309030209060109080d080103020411040b0405120a050f032206020a060509011b02010608070504060605030406 89
    0x4040100303003c0c04006051110b101151405c20040e4600380120072100c4034080342c644011413551300800038a9240d1104010018001da20b40044110780014005d00655014402d0350b8841c4001c0b484c0c1d407140b03882541600014a52036141c000c0062003110f200004028924040282194100940c0d1440c03095980a0030107003020745827504203c0382c204207240d01401031138000e00040100006000185081e807400c4544a1890b2144000c01000d4491a080100800c2010b2000c0005042485000b80e10150505020840c19035407690b440c10700014450040c000345100c0014011840d103480381c40c00300c0d841d0005450401d410420346454a1086025180c0f082580c03070203d00c10ba1804011a0503601c0d03015003981c2880c01752003000e9949402a441d0303e45e03006081d24054291149001702102260290b5004022803426034030340d038005010103880c0950b29500c48811040d050442207115252041c50f9000003a42440c0865582c103101c84c0d6000700344a1742c2008810001e4650000590750003075044840001c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 25274862 1250 25273612 25273621
    0x30507120e070503011508150c070c090c08070801180207050c1005040f050301110a0305190c0f0314010b0712020a060603030504090b040b0603070c0f020a0312090603020c15 76
    0x110010080080c1005260800314940a00080450040110360b030540080c421698104085e013410251400340d000b03664410105002da81443d4440c03190401c2c0340385074261411b11562641d13105a5055040b042c0019143d010015181703904c12080c59000100340382804039541420003040901c0a000100f50311160007080e69411702ca002c0c03009400c1c283c4010300604018a405034050804d41051142a0807504100c10010303841c2010300484000b0105004e6040c0741454905081e00102006072841054106188920161440c00d10032040c1820403a2a411042c03142d4260040c161590b440903003a20f0905000104403944442055882d9a03902014a0312088000c4408074503080007408007a100508003c000070074507401400610580f85021018009041080c05004c1551465590140c000350300b040021141481840825409071040c486a4501c040c1030700000da942d52107400c251000181d0f100100e0030305070080c146500500d0282025414170050680e441d40310200e00007070b02200b515400024 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 25276112 1250 25274862 25274867
    0xa021e211c02060703090c170d0207060c0b060405070c0c080105090d0207080601060c0203031c02030103060b0d0c0603020c0309030102030c031008070303140a120504030c060b0301020909010302040902180f0a140103080a030507 99
    0x80010304480140345403000da01142c8e60b82d03160362126010340540030707442000c03d18a11401d500c0303e038580c10100031f6a641d21102d050200030074000341524100042c140303400380000c01f40e840300001002c1c09000801c1d01d0402500641c00c0114214022096501ca440104070b8020040f500342d044804600340104440480c1c0003290943c40303010700c00007108412007030380b40d00c0202d158051030503a4001d40c0c08000103c107400c1400170030203c00c2c001812000802e8410031065219400138150800302c18182c81c14510040c01080c02d80c1c0050301c00c5d01a40c2008400c0000018090444070024180b04000b0042d181c030350b86000d003400380d0210010800805c0040d62a41d410701a0448401e8013400c060100240c1c60f09007001009007205907012a681030900950340c02515050090f103100e000014100c100c164610343c20000100b101580498024038022008110504140d04080c821488441158030a1130603481510407211540a140d50b403440000060000c5007081040c0c0e0003100d00382c1000500e40e102d07448103 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 25277362 1250 25276112 25276133
    0xc01020f03011508060603040803160207091103010302090a0203060d0b060301180b0a05070504140d02040b030a030804050601080d05030402010509010c020a080a170406020a021e211c0206070309 85
    0x242140403002000056075800c04a20401c02070041d81d07000380750b81703500d01007017250b2009840c060501107051010400407900b070041c2001c111441d00440345440c0c3c0d5140b240055132500c9050254049003c8010820350404025090344501c42c010218070714944100000c60101c5d120304094944030307141c000141c00b0b0f1001d44c02071450580c00040c400d88140d20346001341440c1000c035440c4a22a00744070218042e50700940a8070255192401c062004070b010350180121070744410401e0b40e2040d190400d10a194405002c0a81c03514025610302d00340c1d01c0d041c00c0c002d24003203044e409103a003544070b010040c42c0da50f8800c050341d030840d0342480c1c8266940072410040b14603040c0319201a5001c1020000011580000150820b500748a6852084400000c40300328005020303500c01c42c005a00325480d00b000610f842c1c00c2810041c02042c041c90b15941500c404550300c62034054020030b6403c1c6c611107003039400f070041007a41c0d10807001207083c000c00d0403400e000039241d130b102a0800091545030b0784c11900b0808101c12 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 25278612 1250 25277362 25277377
    0x512070309050a0b0a110114060d06150f050a0608071407051f15090501050f27010605071406100510030b030f030703030c020304030c06081504020a020c03010627020c0102 75
    0x8002c03d40c0e80341d039500d580300d034402c0d0803100200c1c01081486003c81c0c01070040d100e813080e401c1c0e00070099a8412080c4100e900382d0300000c03a0650f40e00d03290240542047c88003640581180c0360080025410310060101000c1e8036009101404590f2042100003139001204841d507a045440349604d891003440c1103483c004100403081c0c140045184000c280c020f19502109003a4101c0840c201031a0b03841d6008811180203010361394002c424210785500030f052100d0b82c901c2c540914948000782c401e80355000f180d08202a00540001480081c944c018055100c00c0e041c0965a0f10006c0c149034100507a80919a198521806004080c0320703420143c81030180d8448480c0c0100541920750354005040401d88a501045084021130300d00941e804c007561000099909480d0710607000c411103400c0c207009032818400208005c4100c1440030b030b1404030340c0359400644941103880d0010303e404c0b03000c80201400e4a02607080230003034405001d1040c049420904240c464070403a107000681da040c601d00050701a1103241c4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 25279862 1250 25278612 25278619
    0xe060d080c010c0e150901080406050c070f0807020915030604030f020f010c0504180522050c1003020c120a0212090a0b030f071101050c0306010810030605160206060a03051207030905 80
    0x1016983c0c0c0c1c0303070499100302d043d041c101c4001103500000402080d0324045c1c884014000f60544002400040d4540d1141350048480c020031801d10b405950351040c4060549411201a00302081030000c60601c4400c0a40008000b00d034000700500a1000c280d607908000c2010301001305403246000c407507000788080403010902000030b012048018402800c0341d40240b040c41e187e040c03e2200149c00c5c40c1e15225481c003c0202d021500300c800d0030903482d542c203110514410b9425014911703d021159454a50341c1c40200310b0f5840c00350b20303440c482d48450309158101c4010f07030030781804000c20071100f940480c0111890f408001443c1d12442070601048a08110f50440c18128000000340410028600c610510500d460341e210f100f1305146080181c240d90045d51401d01c01041031020032200c3d0300443c0001e520000c551600c031a210380d680c595009488058031180e5405400111911034250305018180c0d002d801602ea0199642c038540d20307560388a030f0140c02e01c00b11620129079041058483c5a10100030308005 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 25281112 1250 25279862 25279871
    0x30b070c17090a0e07020309150301060903030513080303070305150f01020303010b07050f0d09080714010507060509031c02030603071e060f1b240b0d080c10021201030c0509010e060d080c01 83
    0x140047e40d29400350340614800c1c44101420041d00750a0300c2244d06039030240c1e542c0d0f0312003491645c080d1869007040c81c4008109101840100b480b850400141d072141c55659030100d85401d113150902c490554001c1c2c540d0080c1c010410000c004d980000440c1d0468140725009a5560740c07500b405820844ea0203480da180e40207502038101c180e07030301046410603200c07560b003900c29803655128004030070f141030303020079002c070308240300400120700700d80c3c840380e0b01c00380220130342e80382000c030046000c030012084a0310783c085c540c04414080c49040806c10032000e421025030349042250040754000714040f192094408000e0034030b02d420500c3d8400c0b0007141004c501c091000346488201c0c507201d4010314442c501818605811107000b08521a64016101005009892204403505a4403500502e44c0324500303a0361144a940300780c00d658507480c401007900071400c580300034140d415450700404d0081ca81d404588140c803c64014400d080b0200981a0003003c1102c006070305680518280383d42c0c2c0100801d801036940790 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 25282362 1250 25281112 25281121
    0xf01020c0a030b060108071107030611093312060909011407020604110109150804030e0a0b041409190b0d08030711062202010c080d05070504030b070c17090a0e 70
    0x40c041d003e8095a800d0b04c8030045956a00c0301103c051062002492896200223010004101c4a90151040e4800550110725141d50040420340d0301400038000b0b10401d1400c510100c1c40c913200344290650031015400a07240c9031041d44080400180170b000244220394110210304c0c40340c0258000c0c014406010002c0070071307140041c0d01035290081110140c030070754860740b80c40300702c2c1d0301c2982d02c0c00c00e40e005204602180744003424111055040200b0440c1032003000c003100301c10355843c00e03c9000200114021156581d08100c0b41581c1c1c0ca4048010314058003841e000d101051981040c0103040ca50714060010301035503001c002a40b5551480d001401d06007000081c030071829032003607040f00040e61600c1111515194a420b200d005602c0c1140207048540c54101400103600c980314240d001409400740a04100d4540301e4002110b0b82560320f180801d0340003a0400030403940c1c00c0c00c02c1d400085400c206881c80030700c1d00d80043c82064010711681180f40003610700b1031907854a4411001e84490842c2d203d00c2e00c2d0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 25283612 1250 25282362 25282373
    0x617060d0204230703060e0a09050705030f07140d081c0219090509090c0102030a050d020d020c0105041a06030307060e010e01050406061a0f0912031b1005010e04020d020f01020c0a03 80
    0x6100361020707103c40880000b90799501074000c00f0f045404542c14403915655550024005000c50001190a400783d00c400007402d036000c00403074074001ca01001600066140c40381100903150491800b40c000c4840459503400701d1b403940c0c262a007a899010300311525050040300e4100074803822032072280c0318800a00000b08158056003801c155502503e4165407501c1d110111580c1d201c940141a0040e4801c20047c4103a500c258054515100c048401504185070002e40c0703010303070b0404040901960743d14810801072280c1c50483e41804036600900e48150709184010907100d104203030019003075545072084031184000940c020708058138494000c1046052910708480500702610078104003a0140c2003c0c6015040350044428000b11681081d190a0846003441151041c0360080302150106001218516410500b180c2041d14240c01a164950384400c540b41100c1068100c0c0000281c85001c000058407410640240180c04540103004000b042d00100d1070701d21500c200301c2d0070841c040d000004100 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 25284862 1250 25283612 25283651
    0xc080307030b090a0e0c040b0a03080c0d030501060801060c111503090a0c06031103060d020a05090c03060405070309110f041104031103061f030f0201030207060c0807020709060617060d0204 83
    0x4034101d0b91142c15880b10784c680b03020344641490400340c0360804514031156281c01e030300161101d003000e4055005a503981d180d00750540c009110701c4080340c11090750b003080f0a525104840c0506414101a1129410010010080003010000a2540c810000c2d4030b11160341c3c011480c40c02a5242500e10ba892402809680d1200c03081c04040f181800f10000c0414424000c0c02172500383d4501d0380c00769055650301c0701000481c0840d41070507608120081808250ba84400090502c0785140e03d5010fa603d0400c041030104a80004020038201803502c4414000664074045c1c1a4111400711404203d6407006030008004141c104407201e44140006400800c0100241c10400680000c805440709a941c01e807480b00030601d6040d40ca0300c2c02c00401c209200003003240458041030f60062500500740303a0341d03540d58000c0b40e2141d46c050003c80c21600420289990401c2484007400f601041807250b6460903a001e8124541060b0804a40940100044840c1c0355082e952000030b80040090000541c0c40401030500d5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 25286112 1250 25284862 25284881
    0x4060b0a08010f211106070305030f1e0123030f0c01030f060803040b07080918010e070903030203030c0705240613020c0c06070f060608100f0b0d02040c0c08030703 72
    0x98940340000b455202000d41c1d0004c580c601c3c1001840b1280154001c000700e0010402282e00001000003410951500340c05445024441c0d02c61907546d00300860284400d00b401442d910f03c450b40200c41e84290480c402d455811640c4c0c268542000ea0800c0e80c0300b80c1500c0c100c030b0300075070140300d84082081940c2c000560f4000280082c1c808005880580382c1100070303984580910282980104402c0081301c0854000b80407550003074042c030707003014a8100021a080c00c68200521200c1d81d0100601ca923400c078250303160304201c00342000000c16146070303000ba440e400b0041510725900c134081108001d0120521008203042c10380c901032846450000c02400c0c021009546290044014040240c6050703218403c542465680d50010050320010000304802c80c1e02520040790085500307114480001c680740034074005400120b024051800742c040043c1c0440f50760240d03c02260f828140c0e410880e88070308001022182d010b8a0105a02e0fa40c020280c4032030000c1300008000007800000c10141950582c00030b000c2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 25287362 1250 25286112 25286117
    0x20a0506090706032703141308010c0f0201090b01030201030c0c060608030301080f0a03050d050c0f0706060501020c01030204032604080d08090c010806060d050a0b060d0509190c18060504060b0a 85
    0x40c0c60201d0130702450701e0103400b001428041d8005c3e282010a0040c0030b10a0007080450f80c036460009041d2948038104035560001649a4684911000f1243c000c91401c0840d1040d200801407022591070b130140e44241848044d060541e01c00180b182188156603601d5021f4115000b805015510090f043d5a0f0303100748103000340c0340030b0041c2c0e205400e00f0214101d810759030982e90b214100f9000510301001030601502c41c07c00c0c4070040013410020751480d40540481c600130000020745e54505400603040c02c19a000c81d0f0304040c4104024800242da2180118510300040c0d011011440d211010703401d1403160340c1100e85640b142c42d0203c00c99942c4aa9400c1c4213024071001c1e5944030030041c005460b00070065031b034584c0c8460180b0651142403115404207034884c40c0310702d0100e111481c0c82e0100350141c0c022104c4406180d2581c081140503c2e0421800c4040800880c814141003056102d82d0010019030288460710454103038004103038041074001a01901d401070080042c00e5840042c1d01c0715030704c0704000402 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 25288612 1250 25287362 25287371
    0x11030a0c09080703060b0616060218040506030d030906240303020706030615051315090504060b070f0209040303060911030603060f01060909020702060c03160209090604050a12020a050609070603 85
    0x40180c03003400074004030342226000300095411035403060045c2c2407a03007405402c00c0080c800c40c85040140d026170121280500c0c0c0040e50b943c40c0d90b0487c40d254200e542d070180118141410312503142c5000800150181c014540002c0600303452400c2c1d009041c55100e90248802c051a580440e5240002c1706001c41c3c5c441e400315046142d46407000d4042e52414426504400001d2900c01c00c0140110020498440008000305001d5202e010803070607240545428000500001800e000c1c0707040c5807240401a002d00c406080c00d2200c142c1e110b0f02c09003040c40780240682e110201013420035001350804005061100d006201101070004410110b800444005100e17120307410204040b10485500c00381615540c0d51403403040360030086008065803117548100c0e04180104000411030000744054203000300070261202c4254994010048683c102610b040101d4000d90300f480b0010b040094041c00c1d40785d02c03c100880c21140460140d003000d07051030001d00a40128002c11031603c2e00800d4510075204140c80811 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 25289862 1250 25288612 25288631
    0xc060d02131409060405040305121005010210020c0d0e01120c020a0332030709170d0e01050a08060d080c061305010501080c010509090a06050d11130203040201080a0b060d11030a 78
    0x4090b10403486070001605808500c140c03c0c40c2d00030641c40b500908210f8904034154280e84074001c401c503880d41000103e04400d01440d0780c144800b01c1c08040000056003440303004130f00940c40d00c1eaa150014140407201c907c204c4940d0107980410002d146c4001c00b00209050b0101c0a915880c2140c0114002220001c43c2401c1c3c0030282d0703900d00149003041325040503160a0780c884140380d10103810071041c89055000050203540018000c0348507682500504400b540b081c001420348440080c0b502c0c107120090003518911540403040c50340c4641d0440d800414510903042c0f81c1c5040c13142c80d4060041c1c1c0a01000c220740340d00035140b00b0340154402c6000b04480ea0703980c2201030300c448000442c83c1c00503100f00120880303441c01103402030700010381501c0000c81c1c41c2da900002e83c08120500d011128861b002086074400e1034003c041e40c102541b140ea0942c51840c203680000c29290004140742510b6645001c0f409464035100142c908009240c2c004129103000201d00803d04c3d001100c074081c030241481c0102 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 25291112 1250 25289862 25289879
    0x602010b180403080612191a040305160201030902060708070309090c02100902061201081f0b060901030e0a080301060c0209090c0105121b07030c0317090c0d050c060d0213 75
    0x1100e8080039441c03000e1050700d45035000c6903150f9024202a5000714a8510704681c0c480500107002c0006c102118070301c158601380781003480f00c8401664505c0c204204010080440e0304041100c14285880ca80400c1a000f0781c40181d00402c52901d001c3c5d0481400714003035003013002003c0100400c5000c0d845000c281507441d1410720589010803141c90040e000340d40500a60311854119114040c07006005a003801c0184260711503440c403d074041c80095000258a42c00e54624021840392481c0a8070b092144051241c0850100e00c100184941015034544480030380c40410b0201c0c246841c0d1201c40303160b82c0d503521940281034000c1014127038480c61182c1d01150360310400146007801d0507410384603e420025a02100703243d5201c01003480d2240e01d07095034020500048003009154a5101c0d4482145400003030030024864035a9482101c3c0c42d41c501001e001c140c0134001489602070000b20340d0b22942d00d4a80c039042d4103004001c54010f07085140441c080c02c401c0e565070080d290742c8040318907601000e550b03104607 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 25292362 1250 25291112 25291129
    0x70b07110f100f18050402130e0f040203070509091c0521010f031103030706020403052a030703140114011202030609061308090f0303070f02010206010b0a091401030e0a030206010602010b 82
    0x64007140b120041c0034840e034040c1c4001403074440b402540d00c80051742c0314085000c0c1d82c400748160803803858010080c0003100d250707400c1a400ca204490010140c0c036043d401700e40e0f200d42501178984903038003102c002058881e08000c04181116958800803d4111108014080b42c000051500001c7c1d02000c008840030760448126040303a91040c0140c030aa4a1a2521b1000700100e294554142c0801c00c840404214140020401103226a0003800b002c038204400d10700c11a120f6008000500e8405071000c0e4940d0b000681c201620f80020b48030000640c04440d05005054020001c0900e80d030301400003c03002c500414000e0003034000c0e026100156120b1307003282c4d1101c0b400c0f0b44180c01079640200c4030300803c40800142003409000b400d03e5030f850500c000068516004040c00300e0318000343c0c03401c0300115641400070600400c41901c8480c1000c0d264a0058684900e80c05001d1580440111090b0b10342c0c4a90490310005400c2810b9032001c0c00c013401c4c0207403205403d0096001541c208100305200d0308180d00c1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 25293612 1250 25292362 25292389
    0x3033306090626040812090304090501050406060c03111e030d060905010e040305071113020304020a090509030d0f141602011401050f060a030603020918070b030609070c05070b07110f 80
    0x80380025030003a0020343c00d91101900590321020180301120310807100048140c010100e0344010b41d01c03a480d01c103104d825101d0580010b030040c3d0614808000c0140c0207584505503551501340f01d080403100402041c03034020041051503500c0c04001100c00c1401000c0020024214903500912003192207002540c1512028840d200554044100040200348504040c00c1080e1042c0c3c40400514402c00c0021201001d104038441015070000500046103040c070300c00c400411040708280040d240515016450340507103d210240710342c66a000030074000040d0300030745049002d0b1080021768145025080407000c880206000598a803001c0481540c20039100c4504036000244440840c099040910450390402d024080905886181c04070042e62007110191150309402d140c04414a41100c0c002c0c80e001c82c940c010100d03083c0410034001c140d01ca440b00141e0050761401c11100c08105441c08130300d85441940f05100c0140017007100c01c1080558002c3c2400510201c492040c1c0081500c10440400c03086d42 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 25294862 1250 25293612 25293647
    0xf062a01060f150302040f0b041521020f0d06060c02011106060901050d050c0a0303030c090b12010306090f0f050318060909040b06150c0109060c110703030333060906 73
    0x80042142881030f400c40c440c011040d20b005401c056480072086900d800e917400014009601040c1803116482c0c00143c000400c1c9103140200d500e0390590001050701d207040c13030050720554000501c001003111031400c40f03c044200c41000c0080e00e50f68440200201e0113034034200c0c0091081e46407107482e0300b0006241c0f80940390040160320781e6480d00c070402c0b50a0101010450700c5001c1c0c1c0c0c050460365641e10700b1b48001036019840c0428110a12800100224420741120000050901c07020088010540029064940c40f100000e0034061703c0c141b01074800c6000d03070020001d42005400b0810000007101403d04104044c42e203018401e001f208020b0701c2c0c0595806160001d0702c3c00d0010f00810418003505401003030191160030f0f040c0242100c01103c0e4001410082140c0d11031900008002041c4030380d042040c802e24040301c02e0458690b00d943c541c009480f0140406484081c0034a844022819000716000c17009115400c0015910f800c811b000007070700c00c4102180c0d06d0040050b84078010401c441d040d28411 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 25296112 1250 25294862 25294889
    0x60c28030503060105130305010915050c040609031202010917040905060907020c011805060f040314070302060d0e161d0a1814030c06010611010c05070c03020f0f062a0106 75
    0x11605d50f082540c0140503150140f2001010540c00c0c03140c41c045c1e0b03000340030000d060342c40d40032120203481000d000032618210401040201c0ea500001e2142500e030721000040641125000c201e0261411083c0030300034421070500d46607280301103030041c022550841000d00c05903566100b08403644004407044805608000082b110359846a08041e0103688913420040240e912840407a440c0d070464102d4070030603400090144207000e4000141e22212030380900900e11039095030301182890290f000d501c20083c0d22000e603101c0700d483c02e0040d5001120b0103e60140340075500c00c0c1c00d04d44010480407089541d000b50010030181c02150150792955a41c0314031080e55407400c0e036038040c0d40c00205c600c10f140b00c0c0030501091460700001d00c401030081c00a60ba030300161800c00810b19007151048211401401420094600020700106107401101d80403501c80f4200d013903650100c0c000f01d48400c0140d42c881c500140c401c000310305280080b00803021072040010032500d10300d0501e080307510b98000d03a010318001 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 25297362 1250 25296112 25296121
    0xe10050a0b0f030604060f0602030a0206090708070303080c09040906020d0506010804110f0d02090901050115020705090412031d032101080712020d06020a02010506011202030f0c031005060c28030503 87
    0x2c800045410103030251000030025952801d072501500b151b004072005030000200302624990401c0400d42110111015140305032030403040503904d01c000c3c031005081c05080d1000541c1d40009030180c03942c0d8500600140526007142ca0084000e40c00a02980c415601d008003190555200305107051295602c01000c0c0703d102c00e00e03020481c400316400480c4e9403006240c1807100041c1c0350030043c00d0044800714000b00b51541442820001c00485002c50000c65021340c000b003209546e20000c5540007038124041c03003c0034102140c1140030b8040c1c004000c41c032907041c916540c0800b4000004000d440890328001c80c8603028605a555024000e2003143e00591210ba0240a15180001c400d807907584000e0182d83d89210329079074141030741c10010301d160261750b480f8100489960480007480c910f61500c2011171861070036030840c080440003d04600c00031180400050707401e42041c412000a40001000c0b50f4903800c040d101030b50b45400c0031845980e14005076880c14080d01c40d107040c4058150341030b101c050443c2e58 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 25298612 1250 25297362 25297387
    0x150903060714041d040501060501050a0c020d0614040f0512070f0b0a02070b010305010608060105040507050703030b0105270f010309030504060f05040302090108010b1206013803010e10050a0b 84
    0x241c5034611482c0203000c0000145900421015070300c20b00b0f40080030070b030318a031038100142181c54035800541445810480810500d0b84605004072580c0d0403991000204850308001005240290782c1c00e071040c1c1c4520070301c400d102c001244c011010307202e1021603184010404c809202402070410080031705480542100002d484c103410385a1160407102c0050070031802c0c0d140c41d031480d1170a90040e6181c0c0d54603c0140640784e818000075016000c1503070306011506207042c0041ca50f2084420280426030307601c1d401e921f5a1301c20b808a5409500500c10501314003076016401070495480010144180390300000d03aa40ba50090060245140d0103846150406241c18815070ba0448004075400800001704000f0005940c0c0b151058064650f0300000903040402c14244954003500c0304194506912002c010084c508000d90305034050301041d02094440c0d40020324400c074030400801c9044031207802100100b50801d807803200c1403046042008000381c1540e604280005900c00e800740020030074041220344041d15 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 25299862 1250 25298612 25298627
    0xf0a080309060309030d1b0f020615060306010c06020f0405010315050306180a051002030a0b0406030b07120f0c030902090a02120a02030717010f050a08030405030307031107080604111509030607 85
    0x1c008905032071810001200030821102078481f01109520040c0340f2804082d4003607400701502d0703503900080440d0304101d1000b421115038155814800c3c6000400961180d01c06c040802c1c401e54000029901c495003c0019102d5030002d01911340001c0c17030500840d000d03146c10b03012041180c3c00640900b010b82c0342c0092121030080c00c1d03421240c8502c81d0303440800c0003030410010001c00e405100c100586070f00b841070910b001c0d203207a4002c40e0302c03ea0400300140086094618150b41041c0c840c00c1c03030084468032402c0c00001e06142c40401c10418034086000307200d40d415400c9820460b100712010389049e920012020120b004130411032005c01c100c000001c0e2070342100d900a40d0860000c0c10030f508000c1c01d104041d200c0b80400d030000c010000340a0000c1045050203402003001e40980000b0707504160406011958070701480d440038007000414210800c4901c000d0240d01e000e0a5800c050300c05d40d26140c1440940249034803030b403034060304111110000e86541c0109888103244d005005c4c2c001622046000c40340c56 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 25301112 1250 25299862 25299871
    0x14041a0402190b0304200f01050d06030605040606033c020604050d05011401060c08030a02030403030e030a05340b0403020f031803010b0a050a0905040c0e040302030304020f0a0803090603 82
    0x41154200d0007009180050b840c008285003408641d5900d820719125a42240b0060840641c1c00c0c40080802c10756510350092032603c60a183c0907455030300712000800542006e500103001607192400340006d0281c1034001c501500e000e40c12501a654140840300d03c1a0b20b032510900d1846c0311f2181001c1c0b10810009640441400285090700b89511000020b4442c4142c1404496a0395958140b9507824844e410300b6004002a00b040d01006150741c0390010355120050900c10b41c1980000020101800380e4481483c02d040740d42200d8440c003154402400c1640644550094201488001181c0400c02216550407108907420385000aa843c1d41c0c1c0c026504000e80102c4c2075010f462810241d401c0100042c256004800750000565440c2c4002d050840e482c40c49400c0c0a03000d95a0140840e4030f440f00c001044440b8441c0c0040d1654a9040029a880e095003201d122695107e042c001070640c0000030358041c0d4000c4490b203070208090000c1140240c1c4030710408800350170920040d4a00d1030403a0142d03030700 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 25302362 1250 25301112 25301119
    0x6010617060612070f0206010e090a0311030403060207080c0106050d0f11010e030303150a0f06090501050309010e07030303020304030e0a03110f01050702030f0708160e0a110d050103030306080114041a0402 90
    0x400e8040c80a0341c860303d000300c4003003001030740307034039001d030a40c2c0d0704109041c01060188010b0200d4148a5405525503205880c05010b0000411240031001c8007002110011500020215103911640c50b090710300d548400e007010602c0d82020700120700f03440c2507030a4441182d0f10402d54001c3c069180d65039600308041b071401031706100405500a865403014002903200d0108041c1031030109924400304080100d040d001150814003861007030080c81d400030303006000d81b002420200e440396600283c1d80d014249441610009008000c070010805030181c004c8e41c0114800d0301d036a00c0c1c400001e02030208851540c400901004038001c0c16000c141441038400410032410314229141a40700d4000c40c0c88c017140e101c1000340e0ba80c8025010800c844060010340c16940300511403003180c40c58a00008030b40c28014102c080e2280d90381039017464501c40c02080340d9107916482000e000a6039607040280050500d4030450a0035400e00d400c074040d200860304004c0c81142d001c0360342a8108032009040242010040040380c1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 25303612 1250 25302362 25302367
    0x10c0209040606080708010e070e0405030f0406050a08010522020d060503060415110307021f020c06090a060e01060503060406050408070203030d05040c0f0e1305010b040e030702040e060106170606 86
    0x56240e84010501c1603001e024003143c40c5160042c118034020040d840300c26182d15041c54610300600c0803a661044408101c8102415211800e09034203601ca06074a401c3e0054001500086003900a0060003d40c0d0b90358803241c1a50380e0399030a201041880041c00707007440854441c0344021444a6001e04510000101d0009a4540301d0001c00d15000c0d041e501914410324000301000f0000c1d090040e01465403c1055003030660030000742c081d40e51110ba611403a8100c07200445c0320f10b03914595042c0c941ea41a002c04a800a00300308081907100d046c0301d0004c0d02d00310b040c07a4914081c0c0300e050003114100d800c0a8028610f6943d10384851004001c042c204032044102005100d0150741c0802c00341120703440d100d0307001426040c43e10f021035400c1642e40c030020550083c1c14041047e04401004584e01404a01220802c1107051901c0d9005101c83e40c44141c0c864900703002c1166000000002c4d00c4140c3c030a80d02000016001984550b450030244603020008074030281c0307283d000d055103442a80004003d040b02c1d0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 25304862 1250 25303612 25303637
    0xc070b0c0903010c0809010b0103111213060f0509060106090b04050603091c050a230a03020d0608060c07020301060b090609060d06090911090a06030818150403050d0908010c020c0d0201 81
    0x20700f983c030405070200c0019580c03c14050446c03000e00c6003800a0009090030072003d4480c0031080254040c044809141041480c001010b1288081c0c0c036184066108404114051026031f1010080c14152a902c01d144182000400c0c064091140d000940e080510300c40d0401c1d140c0400c0007000e46c07004085010901400d501521040361003504104850101d4407101d45804000f1030050150241d814200000a007250840c480c08410002f294a591080c5c580903079640c54546448020704519449075410344a407004200800369140d015001d402e01c00c40092004942e240c0030892940104070b456030f8442c604019030901490860010030096074000c0d00807410729681c541d21700c00c4804010007991821071600e058030440c60036110b0580c4c4144900020400b82d070035030310b600c4058003d05062015402060060003a2030741c420380503607001100d04202641c1d45031207140607501c2d8ac90310f44038038000c580c5400340850301c40418090003421060036402883e244504d51704010120710039480590600c60b0500c10030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 25306112 1250 25304862 25304869
    0xf0f0a030c080f100216030e01030209090907050f030604020a05061e03010906060e09041208060a0e01080a0b010807030b04080d02190309030813080414040216140601050105030c070b0c09 82
    0x180181081c001804090f181542050f0401c0e8507401c80340c00c0c1d5441007165902c100000c070340d0715940981501d801150301000b200181c0003403041054461788141242c0406c040380e0800961042540c105a0307800707a90903541c0c1c0a141e03640790150307802544080c4850082c40141090001f50051503503500303c000140c1411281d07807401da4821381117204815268030007400b02c190007081d400a034050542d0b19080310324158555009030f50b0800288801c11401e81c000c507280380d80d9030f500c81000d06480a41c0c44401d59444400326502d41480104841c010f00c9400001184600801c90504407600200100e05607030741eaa4907101d041c1d00c4104005181542404404414400c2c00b0320641c1100e280d880000d00d0a00a040103040d0100003000300170074403421402c203000980542c0a40c0e040b25000410080d54254280004010740540700d107511100010748160010302034080c0c2200458490102a80c29690b203600c011505031004540300c00300700004100b01c41c0001c2150071541c1e48048200049800d004518000 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 25307362 1250 25306112 25306133
    0xd0c03050a020114040b1603030b040e0307020a05030105040215030a0609050f0403110102030105010c08090a05040527030f0919050a060f09080601051c060f02030f0103050d020a020f0f0a03 83
    0x203a8141d48541403071821942c0007488075085000b58000350703041030b140c424218681d118050071035049160300d9803a03a041500a030404030502c00c00900501c03c0c20780c00500da603540d42000c4416885400c400200240a04061003807500894002c2c02004100185c0301480420744e0001d0302507042c19684100004040c07115204843c0644014141000c00f410117080041442c298040c2d4180075920400c0100a40c0c0c0e0003001400f0b00c079921400c55500c501d451030008110b10a46e92246400504110410100c06002c0407964200181c20b05241807a0040316415540d0703005208900c0c42544080000d01205d142c00807400078846140880d0020203515400883c40340411644004013284081311251081a00a040103018200ea01c000300550f624140000308007000f08443e40d2480c16103a0026024403481d60410121703c82600415990b9050024031480380c0c0340700344021346080c0030312525042d0003403001c21140001f0303400822203d021020320f01001081c0a002100c190f21080311200040006c000340e08 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 25308612 1250 25307362 25307369
    0x3080c070204020d0603030206160e0f0a170303070212030708010302040905100c03020307031805060106031e0c02070509011202090a0203060402070203010f0212060a08120307030603081c0c0c1703060d0c 89
    0x22179039a28620300a0303d003100c0a00050350041000c03003002c0700c0d02d901140c0d14403448021152565481c250350b01091010003603402142c101a1b8410a4995039803000009500440c0310f40d0842d580039107402d170010303941d00081c0c52201c001400c01c1e0041016140c241c102c0d1103d50301032402da65405403240601d0089401490320007010035004000c20404036010721410007210304000c1449258480e070f54503261201d20502401c0305240c1d6400c20040000d01409220000c060880f0003044809081c0c0400780d03440c003007403003524071482400e000403c1d400103a036404010654080c0c0780e9003407078451000b501c000c0e42004001c56086a402c1c800c1d440542c1e424001c0d4a80c1c1042110010b03a0307144d40c00e501e0849030400034489030203454180c0c02003004070707000a0410820868245141c0d200d80351868201c0160400382e00107483e0140126540e4080340d0b0111054210b010155010001811548016584100d034158090301540300030402d035544080d000c000316031100000f81801c000480310358034840204459003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 25309862 1250 25308612 25308637
    0xc02060d0203090d03150b09120304051905040501060908060a0e0f0d0c0c050102010c0516170a080a0b120c010e030102040909140d18051e1e1504030305030403080c07020402 76
    0xa40d0b401900b070f0184110041e010610f544600c6090800b40d44441500c0340342c8d070079401040b00d601c0750201040b0a00a80e000f4190040600e000c090645603600c000d1540c50280700e20a034a00000010010700a550300811580a140074213800d960b14141203004000940b100080d9010310040c003031400105001452001e565500e0b00b425203180303410800464101038202c2419a80360007508003000303421005550005010000c01c2040c25102c0ca0305800c8030060700b12a0369100008140501f02d680c20100c000d200c2c00d60742e0000c000b064200400c214002040b80301c1c011083e00329009804455100720402d140307a2002500142c605507032003c0c0a400c5841207542694644000414007072040710520910101c40c0261030106a42d032490400169080724034030030248985040524116501220304100801c503000030641100c0c10f60b0701c1c280e03d1011850740d13000c0b885000c1a1021840105118040c2c80c00c1d42c2d05540d49600b903070740e00c1d507007910f141501070904032111070107210050069440d80000e2149400d01c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 25311112 1250 25309862 25309873
    0x111120406020114040206030f040f02040f020c0d0c03090902070c051c1502091f1e02060a06050105030103170f07080f0414090f0a0f02072a05010216060c02060d020309 74
    0x1c140282140c200c08059040800709a09120150b62a4001c1c1c0b40c001c11912990300c0c06446900d00840394501c10400290000e0500414400301c2280f40d000e49071040800083e038440280280041b04c1c5804261401400b00d0790018041c002402642e0140c00805c4c030900350700d00e12640f22000150702000104040c40310032140f0542008000c02c5103848102d0308030b0100f040d410002c554001444020710031088501e1208801403031449940b003010a1b400300f4511450400800443c09002522107034206c8910300d045052910002d01c03548030343c0499049942010f03030100311071409020421160f10901c2c0c5c00d094038905004403000f181141e4010714500c44144074065650780740c001c055030008104401d00744102c9a950404c01850762105200d03a008480410005170036504ea9a994028012000050b003ca40c1466108540e04103900708005419181250920116503e000490f50344a1a105041e00340c888208104289070240b015000030b180300400c051f04144078440b2402c12a00102c801003800d80c050b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 25312362 1250 25311112 25311119
    0x1002060403030f20030109110f0405040207020a0b12010302090c0403030c0b07091a03040b06220b060f13050405090a0c060e03031c020a11010c09030b0c040503060103030207080105060405010e1501111204 89
    0x80d00c0723490f50704007000c109581407078062000c0404901943c481c05000c0c9400044084c1150b603065000005001c0b90702c2066286c004444203080743c00c0c000d00003240910101b0300460207504100c404c0d18103d0b41e16a583c00000c440c0f90741c83d01c60560700a04284203000740404d010417141040d000d504102e81250701029220b01c0c16040170180080058405401480c0e40341b640e042aa08031500c140c42c1100b200c201060700601140801c03000d100c1c40f10520800750000c5400000d00b503080c01e0705821190200c4040c4115190385483c0d80c0c0342c0c040c10000030318a1030091001c000302402800311080c00300f401000d503400c3c1b200d01d00440c981110800010a9040d40c00500e07940460b0b0008000310301c20788150020403900030040c1e0041c009040f5800007915140c40003001402d40a00107007294080e00010701a2105541d60f4540690345402c03d01801d4030315400c200006070241410711a480c129804520b102e480e03511940f190162040103401841e0400200e07040050820f0400c10006072499480450190303140d24 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 25313612 1250 25312362 25312379
    0x1060c0501050109060509060405091c05210c0304170910170f070503010b0c0307020d06060305151003030302030601030e06070e12060405030a0525050601141002060403030f200301 79
    0x2c16001001c0c1c142c41d00c1c0081c000e6407034002000b80e004a007545c0000d15a00c80c1c000080c58507142c0000280542180f004080d24540d11402401c0b0a103015010500b17500c11601c40a900b400b4211522640c40e0410300010313001c41d0f1a0004600542902d4100030302d0402e00c100482d50341e1201000340e60104c2c8003001c2450812601d141d020b940301b460040061280d041a500c0100340344418850424110300100320f241d082d0005004903000c1e00c0e070007020048000214030303003038010300340920090301e2901400341203004c0101c40c0c060107403207000360030710507103500b03041d03540941c001c0d04090103050405079902d0401c020043d003080080c0c040c4049480713004041d80c41c58100240c0400e4252080d500e60030850900000a47c0001580c4004046040035034451310340c01880311901d01010400b0f02c00c80f50f540051000d10802184030f0341614035140b2a401c0d400c4500007800131201d109002c0380016809900000c01003442075003c2001041d001e8008110f180520310726900c400409000e01100d50f03c0000100300845 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 25314862 1250 25313612 25313621
    0xa050609070509030c010302030907050a08011407020304060516030c060504060b040c02030a120911030303040303020337050a0b0409031101150617060d14010c1202090f040f0b060301060c0501 84
    0x1041403402e28a4004030101181e04c498081c3c2003079040c160040041075440c4c40034071960380038260203014400880e54030240310f80a410302c402c8101180004a01059200e4800b20440e000e031400d5445461070254400320030341d11038280070001d8080100c05d04405000418500480d80100d0052001140b643c1c00c0c0c0080000711402e0070882415503000300189507000790002150100c00103450300016441c809410030020094105e07028550500000003044209500350340914054441b11070701030300074044503511800250051b16103407400e80e492040e046400c0006d400581c0c0c0302c4981d040100704000440007040075111640411800b04140c00d106000c01d20007403280d003100310203000c1650140392800601410080540c2540919079401d04006070054960301480c803c0796030b1052420030021a240701c1c040c000d0418400c00c03000182200032408249103d8005e5504001005001502416896003000002c0c4210700c0e5010a4a89568502e040b0340d4900d00951b00a1106444401d010103040c5070650859 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 25316112 1250 25314862 25314871
    0x90a0b1005010e04020309011d0303040b010522020a1206060f0e0612040807030c0c12050c030d05030109090f06060303020705120a0c0315020c070305031b0c03030a030908040b030a050609 82
    0x21200d65082250b6a4000c001003140341050b500140c3e25220101040e015003080c80e408000c91240c2c15100301e462000000852149010b8038158009903200c004022b040b211240d00c558144224101516805078580d004100019043c208580005015900101038070f240740d00c1751010030500c900c44450941c020070760407090441100c0751440e06a007894044081131000d0301c0a40b5400c004120001050b000d40944c9100641000003501125524400b01c5501c0e2051b0200f183c150055038060b403e2401c00081103449a440758481c54116807c10001c0002070840300401d48030624110782403404605e0911440c406540694050001c4504200a010103c2d0105504230340301d0f40040d8a907404541c11442100030b880d802a141c00001500c2524080a4010740120954a0207882e00000801000000030848010540340603644440d6420750251112031a0f0700d060b8154004010301c14109120ba800351624170b10840d1034a0034251904808489a0400c851000d03060f42d40e40d060154510708800304a512 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 25317362 1250 25316112 25316131
    0x100f080a081602030703080d0203160c0302060117070306090606080d0504140609010908031305010e0f01020604111513030314070f06050405031903050411030706091509090203090a0b 80
    0x100c1200e9035410301c14480c0050309404901070720454021940d041c00381a000f942c200601c60780311601c200c4140d00130b51003a40c550307500c2c1d810361a86004c2c03039000303903170f4111080e42603005854680e203807140002c102c085010011016009518010001410601c60612814020382000809074100303a01c240c907001800c540304007400014041007084440000745130400340000e540854841c0301020041e166400c1d82e070407140c4503000201d10b14a0300c1e08104140c4089400c240d80e0050130407402340174440c00c042444c0e140ba0058002800041c0450701c4100c5001800038054060f6440d0710034490b0350000c9801450f0050041000d5800030418141e10488500b04016541d5800b89046460390360b0134030161b5a010b00408041d11400004d06100d418820348640040b0f0240300020303242004802130081c14226000ca0701a0394041440c1401c3c14000707480b00c1a20100d0301e40c40380d0b807070400242014447d211a200c1042100110011a0000b036070300256001d80c00d00c0380104481603140c501103c03004401800d40c0d12 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 25318612 1250 25317362 25317373
    0x20301050906030a05060c0c100c02010f0606051303030c050a02030d0215070201050705031302031002030a02091302131211030a03050901120507080c070305040806040305040518060f01031a09100f08 87
    0x46107020801c1c640044044103c55680c07500b0300c0001d800c02703070400c1c1ca00c405240780070b484585440c0c06410032550141107001c01c211150700c1d080140e40c0b40c010001b040d0609002e010080c00020b000f01c0c10310f4200c6019100311141e0290035400a0b00c0d001c0d5141e00000140c0203522070542c1540c0b0168a5900012540020b002c1c516200400610f1800000c08684181c6006541d14056440034056034614091040040d942c0746030040403440a980b040070001c1c0501c03131541c0d41c11a03810382c80c82540c40c016071341d04c2c0400030146006201c10884104440039107005c40b444101c0050b82d80e0130030031441101e00c03a8a0b815101e2221400240100c0c1010b84040c80b000d04000030000307120344c0b200c0e0690f400040c8511998803504d5a080c201c1e1580030700c0d0401d0800744100818002410f4005000d081101e030112092405000d07541682d841e1000c1c107985c01134100c00c500f1001d440710360081c2c1001303902600c900c5406603810500c1c000200810804d5815107680c2152140900c920450303413a00740083c107038540c000c00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 25319862 1250 25318612 25318633
    0x6030e0114010b07031704021e120a2001020703020d02010804081204030903140c01080127020f030105030c0a030308070e060c010f0f0c020c010804060911090705040603051006050316021f02030105090603 89
    0xf4004000449d280c464000318941003502a40c2e10040062a140224204d440d180003501e041400641110941544c00c1d5004210340c5545d8030010b00ba4059a030702030180388000b07659600541d2031410240040790094400e20070b5040380541c1c108124404c41c000e0383d035180180e18600307049000c0c0d41a10000f01d80342e003281e00400032507600322820314111030b0403070603940b2180c0b44c80401203a0ba00c480304150040342e000203400030800c2180000f45042e039400f03c090321520306100042100e0000e191000a0104c0e01e040001060305005008102e2028800b612640c83c201804481c0341c03c4072047c245d02d54901c2d03900c902198645c1a24818203a0704002d50004004d240701081c00a04990801000144800d4071101c00f0410007170240f0a2244c4400041d040180f141042c42c9c1c090000c0d000750060f2400a8501030008030002c07a83c0191000f01c41b2252502c52864858919030108200341c180114154450795141c020260200c80c4070103000741d1800001a280e5041c60104128550003030030b1b440c46980080c00e02d4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 25321112 1250 25319862 25319869
    0x61207030c031a2b0b010302090708010315021810020a1a060307090504020301020702090c030103052401060c050a02030601140f040b0315070306050303160b1f06030e0114010b0703170402 82
    0x190750b080c00403980e484c00181208452140181c41198a440380003c5040c0d076810032203a9440d0303606992080719030304015078800008590f041003d12018103080c07007510f032050b204121a4000c014032541b0900405440c588440850000b04a0507580720041e801282610300f88441174031201e2802400c060500e499080040000e86d8980050040642190703840f00802c08654007503044560080e80a0004002c40c038150004900913002480199124014400c440c0030044110f102d032542c186105244841d541d0802c881155540512401200c1d1403154840d00c1c0c003da60308002440c020055440480345204002085c27080405e44a0070503030085040250b411955600030402104000301e201000c00c01c0d070789428089000e00241d03844035405d800700040b042c40d1104c03110f2581202c00d001c3c5e0450b40e184e803200c000034000200410030049011000c2e40e0244052442500034501002c80e1000116120480302118902181300b0b81c40300d01d11040000c0c2c501c003010b80019000e0409003900c00d07030525916058020 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 25322362 1250 25321112 25321151
    0x3150b03010b0f0103020a05040305010f05090f07060807110a0c081c05030103050303040b06060f180109060c020d080a111905010606050f040e0402180a050106021605011e030902061207030c03 84
    0x3c041c1459008035810350b00c81c2c45030b4290303801980c116001b801282100040ca800408065400c8016801900070580c1c0c586000501e40040340c299a4a040e9255203104c02168003444094501c4942d0241c1d9002001003001d076200344018110420103000c042441c0c140c02a00545911305480c20700c4030030302c010400301e503010040d694019008080c070f04041d40c590001441600c07d0303503086035540f2004514800038044459076400506c0d002c0c6c032104042c0d91030342001e640e0280d04401c003c2d032040c010301003c00096060009441d40d0b410324186481510141d40c1850f090180c140400710314a1070501140003400030074003507a4000d00c05408c1151130404607203290710300c43c8180d0245900040041001c14119100c50404038040e031000040d4040d2403d1491030100500300a01c00c00005100343c102400046c400300307104004a400c140c550400005244110b480217845820443d41499902c802c41030260b1600c1004245500e2442644407062410f40000b4044882c600850030030946002d500090342e4601108 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 25323612 1250 25322362 25322389
    0x10e01170c090406030c032004020712030c0e0406030305030615040501020a03111002030703020d0f020f07110f12100e010606050a08270109020405150a052803150b03010b 75
    0x101c0e01d40e54080800401e0182c8042c0d07100030854401e06000205104070704140d1459540c0402000c00c40305100307402c210903030080c00e00250001000c0c2c0000c80c1118080d03400907100c12441d003400414883c443c0000780c01c480f113551090b004160000100301c00c0e032802803100c40154203001846070401d810800001d54900301c50070020248160300d44460f4040d40d0810a0000d04c641c0381000303640c3d030324021030024013a403c0086d00c00300c15410581941300f83c4905000382c48844512203140d0f4280055901d40880d1025541da0242d00400086100716950319080c010f1408444908003c02e489600c4c400280201e8000c8903144d8541c1c0d140000078440030b64000c0c1100e4142886252600c0c05441c3ca0300101650741d52807000c0c6034400e000342096002c81006400008070b060085400308000d660b01000744183d58041040b107640300c007603800140654a400349420000500d0b09210064028032545003010340f00e001e0b0810749403002011059000c00480303004100010b44194000c0c46a075100c40d01081c4038122441d03 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 25324862 1250 25323612 25323631
    0x20703020c1903060c1d030a03020c010c11030303010b12010e160302072102072c060d0c03170403020405070507050d03110c0715080f090307060f0209030f010506010e0117 75
    0x181090903007400202d540c0107940c02041c1048180820b000240c4114001480502e031340c0000060b818680c68085040740080e42c05030090960300403000c00442d03035001c1950007196008080e91445805440400240d07000c0c017100c101087da41c1440c0c105000b03104805a2050300816500d0381001804107400c0c035100d806450038200903031601528a0b00d010118404078040e00110814003c0c090340a50000e1410200e07103000350b200b00d81007008130890740309902c4030001c0c00101075a00c0125046e800c0c4030b1805c004283c0034041c82520541c4035034900c80c014100e040d441c200f0300404601402540381500c40e0503007000541c18100e04d04170050340c9142d114030b4420541018580d6903c82c0c0030340442d200e8121080b2912410648609035100c44c1d04040700440022183d0004481b000050b040f0601c004000303000d03054080045080460b0350380c554000c2c10311300d050101a26000d02505015880070415180c0440c82140003145c54a4500001003c440c1451180341c104182c114040c030500d00140344a82d00946240e = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 25326112 1250 25324862 25324879
    0x40302010302130302100c15060e270304030c03110108060906040906060b0406020601030c0603020408070e040c05060d020306090f0705070b040f020619020613030e09041401020307020102071401020703020c 90
    0x20f0030910340f1895400607402c002104180e94140b540103000310a414131501070300c0608150101030500300c40d01402040f90991a80c000310709406040c1c2400b40c0750310754007164406001d0607540460b06540055104a40c20b10441c5028010403540007042c840b00c500030329003c0c80900c0c00c203001900202001d8070150041c0d584004103014844c1e01e40160340135004500b003041d41d681d5144e00082d07844200344029141c0062030100400d40700e01c02c1c0210303012104401e008110880c1040100010048007a100321150400800001040e481c0c903805041095020400140c50346495006d10214031002881403038609000810415059008015a9190f03034120a056200d941c543c0392111031600c607000003a501c92000324502144a01c2039200080003039480d030a0b10b080792034014020781010310074400200403d0081c0b000e100e59040103c07015601500848020001d551080e0580d42281d01c160340e01d40c0141d400003060350511000351070201140744000000c61a20400b503c0082d2201896085d0301d2092205 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 25327362 1250 25326112 25326127
    0xe0102030f180f0a060c060605090c040501050c0f06010b0a030b030a1e11090a020702150405100302030c0d0905010203061509090105010c050a050118140a0c0603020a0504030f0503040e0606030c040302010302 91
    0x70101490024000a42801c8140b6192640500b0521006d841100c4407400c2680104031401c040c41014041ca0a40e8003050909050800540d1135030800550047e00e40b09101f81410a19030400c0b8041c024035007804007550340c07890800c004081e2405107050754065880b600003200050001e80d60003207607003010301c82030036208000d10f0700840e4a640c40b18041d50103c901401e00c101001c0b940c1c01460014801c40b841c400c006113481c40d10b034441c000c5e881075075030000381c0d0909480d0460094006643c130a0030180280c1c5080e001e101c407a421141113010507a031582d404010410241041918024012000030102e810400300c6000206080c505000715810004040001c00802c03200300400d1340b41e5544003000740014040003440c0c0c2511044210103451402011944896003400401c3c9818036036005442200c0a505101007500a540040f00c42002c0001c100000000b164001952000540c4108080c0d0ba41e21b02d0110701c1d0a841a010705903e102e01c200f0000d00c0100d8501e48115801ca96080c200035884009 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 25328612 1250 25327362 25327369
    0x213180e030d020301140108041a07090e07110706020f030d0c0c080d022701020604020f06130e0114060408100c0504030609051c02011802090a09051207030e0102030f18 74
    0x22108851a0544070120b94001500c846030081c0d030590f01c1e4802481c01c1480e51b03900445e00a442980c02034512508251700307120406081106952015150034501045a520940c40021000469103540014014440c9500c20744060010380010b14252008010000600d119581c40e440307449200c924040c0c1d100780040f40580204040c4030900e1b008030b0030a4036980455104006507001c0c480541300d000701c0455001000044c56014403c5c1401a4002c3c0700540e0fa65080c4418100b48503002c075403241043c040441c245040701900800303424020542c05095262041e2507001603681044a0700c6808148020b11a181c0d000070b509185001c3c0741004180c03020f40c50b006036401c0c400c6070005044c5a00700458030341441030008000241100403601c0a6400048420890803a860161082440280d1410f0040981f41224a03980c2111604c0800a0341000c1035403114546503420340d81c07581003c0701290300c0702450b400514050031100300380091450b14800c580700e4043e900c02d030030100b2120320341450f41c4011500c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 25329862 1250 25328612 25328621
    0x405071b110a060c14010501030305030415060312030204060e0604080312180304090c0f080405030f09060909040f1208011a0307021005010303120e030403110108060d060501141003021318 82
    0x30710140405019540354072004000480c4408191010303040411745002d0b00105208881c1265010740e80d59045407a680e40703030100c0240d051107156000340c45041c080081030021828031100c0101d85c80045e56940b03803240141a1050880c0c610740f0648085c08204240503003c003c80304520082c54000075140e0f40d56030020a2151101070000081c030000c2408542c481c115408408070303072042d442d4003501002100c1c0c02c13507081034202d40003816a041449004a058149401b600c0a108000d00241c2400c0f40d0b10b0106011001c22142528003031099441c0106002c5911500011380010745405a550360401c03001c00c2c1d64003520850060f001070004001000315101303201d4504114141d9200b07201c00e5942e03003001000001c0701c83e002d4219a01e80800301d104ca103800021030b401c40c1ea01000c2d01e8140c5883d42c005441c900c90081c00303190480011003609000a00c0340c49854040d04105011044c1260241c4c103008803a00544441410705104004401d40444881460001c450b4001d400c001150107014000d030180 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 25331112 1250 25329862 25329893
    0xf02070b030702070311040513060f1118010305070503090c0d0c080a0b0108010b0a03050c040c0516050f0c09040308270106060206091c050a0302070f0f0807020405060405071b 77
    0x21503021007803112280d07001c250f8800722070003010f210001c100c16104010071503505a0705400c000000b07018072000507119070081c2c402180c074000d00003241c4070401e007100c0c15548100020044550482341705003c540e011703c1250b0b0020103503d092402e610f01151a07590741d089041d081441240e50703502a00801108482001c05403000038151002c190b824a4101e181150078040c0342e00a50800d81c070b44400d41001c000c41d0084a8001004140c0c8405e80010700000f012020702620801504100c40e000303400941c0b3b00445490b03c034800400a46103d012164200b8050f46581031040040005000100354001344440d0001003044c2d00305484000040280304803040040d92403929401c10800242d400c1e00440c00500c10380d0203009845541c10740040ea0030020495505202c0400d005100340c010140c802d030b0251443c0d0b0b00c0b0742d00c886c005126903119440c40c452500000c03594900c0000b500740850400c1d028031034200000b95005d021714145148064000c10245058059020003428900103003c07a030f4001e4030300c5 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 25332362 1250 25331112 25331129
    0xe01060c1e020f040e06040302010c050a050d2c03030a0605010302091003020a1215050306010e040b0c13050402070b01140405070e010f0e090c0a1e0807030c020c210709020702030d0f0207 82
    0x2442c0d44400170702d0319850300301c3c4d003039001d175280c2a017454085000354115075800c0c809680c3c0a10301101c0c152500000d0011006168400041550300c3e4484401c40040b0b40c0c400741340704001c5849282a01340c0c0d03000d59056801c007504160052007030760b2140d00d484284600c8600c850401580310710318403074200c90800d80000d281d006c20341420103540880200803c0041525020307001d640207a030302c1c1c2c2039648480074240c6e00240150480c20000c1d1600d0840c8018011040d00e4a620800342941e03440014180e8000301d0f42640c00c0202e000c01001408081401c80310651400c0d0b605000c10714002c0e001400303410501e221207040c40b0098040407101d0f882802e4070210244001c101401c603051a070000070003904030414150100d0400141d04000d052008950400150306540d5580c1940d68103004070302408200203072070b0640c8540411103010703580d090480010400070003100110441c000d0031952030b14100358801038006104000c4000540c41c007003400081c21303d00c0d0500f41716008254070128681407850740f0084a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 25333612 1250 25332362 25332371
    0x90a0e07020c0102030c07050405061f05180103090210050904020405090405010504061503050706050d020c010203180c1203040e06030a080d1406010816030e030415090e01060c1e020f04 81
    0x4044008116a501415403a401c9031500320008005907520322902c110000709900c0340c0420001450f068000304c0d03021030081d10450341c28203e00c2d90000018000344e10f84010940108808d03540c58440e200075034100e00c003441c0600c01040c140e00441c480302d0a8400c0c59040110000d400c00407600d40b0707011a0000c0c0b030068151030b51846c0a080450080070207035003c845050410700e100301074044883c40101034a170414080c2a5031f91920800356515071280448003d1140c00744660020f584080c4047c1d8800d4980500c0c03900c0100311f10345800e0a216030000c0c50f610542500800b00c0b015400001614151400c1840e0285583c441c10006032900615580041400100103101c0c108000980c103c020680c550526610560711810019901a20100e6011544141c94034002811907c40c3d00290028540f050550f444d01e41c80308541541e41e01032007181000305034411020041032200c41c0740240102079500d84006914040c1d40d8103803401c030001c61105200c440e102030010955840100302100038030028410032 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 25334862 1250 25333612 25333619
    0x4060b070302010506090a020c1203130609050a05100c02070e090114070f030e0d0e0904031107060903020102060a0213051203090406091a01020a050c0409060905070303030212091902060c0102090a 86
    0x80c0640422100326000741b5403040441e0750b5004070700070303150b001b41258080d00d040c0c2c2140490414a0b0401440d040300603848410210100746c06200f9440d00074001d42c0541101001400c055103002046054030300c800340f612566400d0b09501060303e03c282c841944c540039070380d00c503401d0035030140400d40310031004000701c4e1003032091064210319090121500c9840a1291080071343c030381798030b90103039454200c00308000845da90040c1c54000080c95105120381060b0032201404950145400c041e5000200468119001803055680400115a000821000075440c0106417022011000e00c0f03071051790302804c090450702249040503c2034400209000e4801c10800c0c2c2e80b810b940002d8850140307401c894084400320100d89502c04145030301c0703441d0448000d06c0124182c0c401d00004111080c42503400b02d545050803000035800b4081d08009602a83e400351b150b030800075800015000141001881c3d41c04489082003000190101c0404660101c900540b5041101c0d110350180c8101d03000664441010070020 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 25336112 1250 25334862 25334867
    0x318080a030c08010b04050a031101030905070602030a020111090a050f0105071a0a0609141807030606031505010501020703030c0308070504050405161b020d080c070b0c070e060117041104060b0703 86
    0x190a00b05455580210f80e0b40e8408182005120b03c1c0070b09604000b003200305101007007880c005034031460810b16001a510f1883c1c0c5031281070003071907085500142c200140e86071515509006086035180d1002c1c8240c54194481e00040418444c1d1242602655889c4504111a805003060310b000740c0e0041201c0c10081c040300d02d6540c100c07800300c951882c1c6070320380440802d140c7d10910660441e107141a045003540d0300c5200b088414000824041500c2c0e02c110a0040f00003402c0340a828002c511559102080c14401410720040c0d400580102d411036005010030000300b5407160100c0c50007a010300303043c2101d40b02c02c002102e0358403e5800113500309040100f4070001d03400400030040341e0540d55480390217220682c440042d86459108029600601011102001c00d803144010080b203810207003140c241c04c1d600c4445812a4002200307411594010050030000c0002c0c030100903070301c82c03805d203045600c2d01c0e40c4142c1c030840c2d03441c0940054144096580e082d541a02c0e00c1c1c0c0034102900e034400b40329850304440e2800 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 25337362 1250 25336112 25336121
    0x6010807060216060e0d02040204090c020109140a0305040308030403021006060e10020d0c020f030a0c0303120506010507210c080412050c090103080403030f050d05011202040c1805010318080a03 85
    0x46100610400c92240d884505031940c03d0260780441d40d4134000c0c90074410030810030300f4040c1c00c00c1e40d100c1d60030000010084a00d202e262070070b4149400100d040301d640d0800326401035070a004d64800380c20050841d00003e41c00301c02c07101034030f074400c1000b5140e880d42d040480c507210324107400802152800001185042c1c00c0440101c0d0040200c40329844003240c12400c9894042c04030010b0041010f40044c50014641514010100035001d003c41d1602000390300c0d03102500410b0390040e00440c100d4100e0b15000c0303502e401444e62101080c24220b191030300701d950709090082110144c20203502202c9860828900c03e1805501558100014035121074841300c0c1c0090404039001c0859503403090280c0e0b80c030729007800d21100e8101c94002010b641801d146840655014039090241ea04105007005120440000da20a660207818083c1c402d4192080a01c103100880341c80340300803418000d24800c0300d8051400d011a403800d80d0b0b000c0c80e0120b50f511401c0c030610f0400141a000030a803550124020400c01e515a02 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 25338612 1250 25337362 25337369
    0x6030c04031101020106150c030309210212070b06151303060c09090615050318030d06150203030f040210020a050102030c030402041b0c0605101d010311011d090a02070506010807 78
    0xb01d426522500340042e400c80c0d62500c40d03e6410383c000c5c1c030216215805001c07141d103064080e081c046003076100c070b0380d519502e5080d0082540301d20710618241c0d0400c650400c102500c0c03d4404044624003045512910644200100403030b10482ca82101c00c6c4241030880155080b4944086540e0030880d168600900508a0030783d000c000203081002c0040c4a202e18001d000844401c44500004110483c81c100c2d510344c03004191262241030b10400c2283c10b0010002401c01e81481040000c40c10300f440e03080340d0940c8072004200308561080c02030244a00840104a4009078121082c40b0304404100083e400c0080a00e0040d0070703544003008114800142d00000c2d0f1240344210303410089070f401003d1010b81c158001c02003c0000e18030802c42c0c000581294412030f0014130401c0141c15080c0c3c1d4882128254030001908a8002c0e800401003040001549c420f030b0301a402406c03c000c142c0c281e54070102d02058107494040c841c0c600708021525032401c5a0440701c10750b4010083c2d8880f582c4400031140d4034040da20 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 25339862 1250 25338612 25338623
    0x3030609041a070206010504050a140103060b010203090d11010f082e0f0e091e06040822080a060609020a120218040212090f0111031f080105090c150702010503160c0206030c0403 78
    0x80024083c00e64600c07607138a40c0d240800cbe0309052a400c1d52a203a0003030107040020303415407004204404142d40d902450840d810310986280a44401100c00102451141c0e0131800511000509001032070598502c42c66640c0c806040140301941c00d10490050482c00c0c0d403054001c817040000206980340454001c6104815490444586e0340026070000700e0440041d0120004c0e400c00c0700400c0005090500034040d85a21450080c0c441d001113000e09118400c0e0b0740145d60079841032841c01c00704403090142ca4001c000c0703184210f00781400500b01600201c5d441001c81407081e800070304c0e40003444c000d000501ca503003c058000c5446024050000320300380b00c00d0790505d10500c1203240010359081c05021f25118160740c05a050708548414150840d00b01000b010149540300f081004182da030310900c01c5e544254000300080c00113100d03240602100004407603210801040c10091200981d0704030086a4009244031090b07000c5a40c0010100c0e58612442da009500480c00010701c0034002c3c51201610079a4001d4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 25341112 1250 25339862 25339871
    0x2040801090203070807080a0f05010209060406050705010f06032402040b0409060302030f1605040207020607020405160f1112030603100606080703060603020c060105060a170a050103050d09030503030609041a070206010504 97
    0x4540d01543c54205207d0381000354002071040c0b000071b2560002e412007a219200140c00c00705054001503143d00103402000c0000d501003450010301c0824014500e4030a03070403508002c4207045480311246c0c2501c60909034000690b640320300d4064046941214010080c0b100d03e60345540c0c46882000241c40144416403080c07095112164403141c0106040480a05e1103103d804c01c13601e0142400041e4005160030707a4080414449900540c13114080c02c0d01c03541c850787d003070040006042005044030050325820420030014950708180510005024100c0d013111300d88a60701c03a901c00c40042c0ca0f10000c00503240b0824201940002e80340c2c1c03c2444540aa60261010720082d0b0311000110200d00824001c3e0040e540300000400c11820940001c0822107610301c1d011944400e4045081c49200c002d55034400065552001001486070034070100350541800e01c0e007001e44519503241ea030740c0c0740000b030441c511031046240400d04000241e903644011150880c0e1819042c40c04a4019480d81700034411140180e00380b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 25342362 1250 25341112 25341119
    0x180913020a0815010b04060507020f04091209031b0e040618021306090f0b060904110d09050c090c030603030d0c050910030515040b10050706020d02120a1505220f0204080109020307 79
    0x1720030076039090301c0040e513882d81840c0950302040900403904406079000395440c880000410681c0d51802801030a644450044500d14039141e24000b800c1c4426483d0b014108400b8420341403443c2040f504641c0014000c1004212810b84425405500b00000c1d8842d4245001c020b50074903a800040c100c42001c1c00c204140c4900003902003d03100c006090b554003110030000c25615152580c40b904401e5081c5c40b800741094000d610b01003c07600802c07029512544065045225490003c00603135005039102c5c203060450a0000c00721341d43c0d01a5601441074507458044c9071030f40384c0c411403d03104001c400420100007a40401c40260080030261500c0c1101d0003401d55040d514103160190b001c4080d409418a40c001e540884119250340040c001162515020061140241500e00240030842c3c011480e220060a04649210481d446448202034441d1911010012551129000d011301005402800c44041300201840f004002040329420910304c080b070f000c10040390561002031240d200703500b1248160745 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 25343612 1250 25342362 25342379
    0x3010e03072913030f030e01020409020c0106120206040308030702030d140906090a0203030a0e01030e01060915090b0a09020702040905070e01150503010b0d0903090308030c070b0606180913020a081501 88
    0x40c00c94103443c82c280507003680c1000900c200c03a1221104540d28001603032601c1614510f003aa801684013021050f00803400640117002031007440c0c02031515a00c5c8412148650340420030f40d00803840044c003c2e040100c006642d4500034001c80b00c0c0803205100810040507480b040b01004002a6000c00d02403041600003100504005403c041c1107070020002c5007003a0408004540d14060b1a5105041544590b00d0f000d0302c00302405140f014020118012035111000c003460040f00019520110000b03041ca075885805da110954104280c500300000540d40d494603002090203022070480040c29881004000541e0502482016040e52402880300782841e101080849040c0820300503021150300800042803c0c0000d90f2100d4012072080c00c001d04c001d99641c403084141d400488566941e010002203000070040c016082540c41401190120708041c1d040d007541800c12082c0701d055005c0c0c6050400f1904480481f4114800c16900400e0481b0040e100c0c2d0a1549800b40000321003640c161200000c0389019 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 25344862 1250 25343612 25343693
    0x1a07150507020a080d060b070605010e10060909020d090b09060702010b0607080405040902010e03030a0201020d230402010f1209061b09080d08040c1502030304031404050604031103010e0307 83
    0x80641d000f004100c840b6128103540d0361014151107081da0380c1e481c0000b900400d08000d056068024100000e01750315012094648120040c04c010a40c5140e13081442001e80010050f42501c1c011b00005890700390078034002e0002c00c1a82d00103058095070204000307048900080503407003220350f68000c0c446a032595017800b00340e0256080042c4500300502051100381032507071000f00310a00516004042c07002000c0406d0642d4419a00303c8010f17500010509207065050140101c40440c40b5688903001c11898400b0094480140009040100341001261001c3c410010303a091205403520400120f002481d0440003884110612100c120180201c008601c1c083c900742012200100d0141c0b00000c0b4030041294116001401161b041000300c5000c04c4213400e4880c0d100130740841d500110b980303003003d0401600400840c12054090481040b0902054131918240da040300d9000c01d040c80c0305040480042e014100b40303000303210176100200f402014403c0c00b40a8035000484845100c292258008484e0500b2 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 25346112 1250 25344862 25344871
    0xa1119241a090402060409020c0d030b031603060e010f230a0204050f10110604060603050f1b01031104030516170607021b03010207121e08090606060c03041a071505 72
    0x600039041080d49410b0181040790f20600c010012403034161506515801c90300140d4a0007003591050515601942c0c251080c0b00ca807084c1240200008130741d8010100f0600d10a010080000e910750303a01030100c0c8400d411101e1880c46c104024401c010346014075980b8404d80140d4641d8035070b0402c0205040722518400c0310f0030f644000d842c2c0c0d80e0003a42c1c60180318628801c0b221550402071800c5554000c10b501b406018019171042c18003255842c6181006813a081840e02e079a840d42d00301c400c04008210f5030701c14440001c4c1080c03d0115031180d5540001c200d5026541c0094060300070981480c601004441000080c0c40100e42140c000d80e01d4500010b64640084450602691180c17003d005408132080c00b82c800e0040081c009440e000700341e0f8031410521007200c1e095000c0381d4037031200c0c40c80039021899413120311110b03e400409071900c07025031a42c941003d420540110390000e072001300001d09200702e0700a0418882e442c128080d8451b056281940440d00079240703080d01d48140f00c107102031402261b005 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 25347362 1250 25346112 25346141
    0x90c03070f030b0d030f0c060222080c0a1a210919080a030f0905030c0708060c130506090102070803030c072609090c09040603050616030903050a111924 67
    0x21300115542c1910400c0c103442c440e105114541000c000051036500080404040301c5400011483e40381c2e1030745d590440c1c141c00c43c000c1da0300700702c010342100c0d2181d1b03268000f1136007440c10030b061600306080d0044003445142000d540c0d1102c40b11241701d00301c0f0800c0031a80280e100c0d408540104e80080c1040b80248040700005051041c1084540566840303a04185030045960344005291030041d034800d40703558418500020f03241c200c207508020021060140c00e9100c081108960728205105030700150b00079460190038818040825131200301d920801602d40a408e42100b201c1e52800d003500f45038000d41000343c040782c5802c0e04401641503500291102110131204242440c1802148000c1000c80350f0300034014903c2000038030241c40d20303035910b01442000b54011030180203141005074400d0b580741138400c401c0041c1410011130303100080d0b00074100c0d207000c413440c40d0020300d202c10160b00c00d060020380c1e6000310415104c10740e0a400c3c001000510449690807a02203008403510240c040103544140e41c03e080d0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 25348612 1250 25347362 25347379
    0x604050d0c0807080d06090c17061203091e0901030c14100e0907021c030603030e040504030f0f050d09030e01020114010609170c180108060907030f08070f02090c03070f030b 76
    0x9013a100c05001c2e810100e8801056803a00c4460305412542c40341c103410300250165a5801d811156450341d10b80000042c2d03420b6171080100010701da941e108200201e40250030f06102e2466100c82190b2280d01040c006000c1145540d507030525141d01180d5009001046a145002543e5840c00c1207000350556565160040000901410040c01c10002030605c030650182c2422410010001c0c502e40f05030300042e446c001049811030400505507084226441e00491415003400003181e005600c075050288146042d190642422908580d28003c502c06070130000d003442e005604150308030000854083d0203a008000c82c0d100c80b80c022500200038403074040880c1002d8800d10110215006c500296881d0784111040f8038407030404580d076808007401d80d8140210160041c480c40205000054000d071301c5d40010f101543c2581c4524155041030880200400000980c860804c684c064201009940040207100c0714a040f0341c075540e2951049134440006000d43c03003140c15940c003034418585a040003416011 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 25349862 1250 25348612 25348627
    0x507050108040305070219140105070816081b010603060e0105040c050f0a0e09030d0e0604030503060d0c030206070302010504030e01020f03041203020c03030711041104052d060c0604050d0c08 84
    0x141c0140340a8030982c20003804009400150700e0b01e00c0d00070345190f8a00b02c0c0c010310916042904d03036101000d442e01d904002c010400d07880480d01c000c081d1801b0203002d9542000d209901c0c6809a0341c1e128010a02c4190414441e6404030360b40e040d070024084a0003010148045004004184e00f01c0d01c08450040020007420800d11031410980c444082485020307008409071900c0c0e91540681c1081240c4540440c3d000103040b5880d54818052240b41e40010b80c01448075041c81d0390090315501004000303500a071032070380812040c0a9541e10360001584c004e852035aa880301c0e0306000b030103000c08540a0380407a61205214501e0352000071446410202e44000d18185401d00000141080320a1816011441085006045664140300501c83c0c44d20990640c1015100c00050005851107034405d00c81294051104001940760024140d0104092030195014413100100c00741e064490380d400540c1104010503e110703c1400081c800f40104c0c0100e048581c1c0e500b00030070403244013000040080c00b501042c010300 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 25351112 1250 25349862 25349867
    0x60307030905010b0607050f0f01022704020f030702030306210a020d05030d0e06010306050106090609060e0a090606030f060e04111201140a1a120c0f0402040308030a020a091205070501 81
    0x1201d08910501c00842c800e1030510025030f40e5002200141d420b0740102c04031068220b010480500d400844200079820310400c030b10303d100f480300d45040da81c5c140d41140700d0b01c00260352254102c6214881c1d43d02e40039102d05055000a55980040301c4003030103200c3c0a40c142e16515900700c0001c0c80a07001d2001890342201503400e0004082e8900c03821070705032106000240108034280110070006c031600d801000c0c658590304008054520682c081070500c41c1e151400e018140d4032480240694141d800d0005141c1c503007a01181940c00c61740e20a09490740740290114040303900d604070901c026141c0c0130030b010845d1140b4540c0c0100b0820703100241900103040105038107040c00c034140f8680e8a44500001540d03000070b440c0380c6070241c080300c4104405540c0e104001e01010388108021001000340d40000f0910300300d03409142c0d641101d03001a4800c4a81204003005980c45804a801850f848442d86481e42041a4030074040d410441900c1c2c0804c5210802041814404401080007a088401405d1003490070005 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 25352362 1250 25351112 25351121
    0x1a0a0f060f09030203060414100b1c03020f0d050903070906050a03060e15070c2013020309010e070b18190e040303180f02010305010506070506011e210203060a0204030206030703 78
    0x4003810310040220001c05039034280101032289004e034402d03401c0c2c048e03061141428070304c003da010080c0034035081c042180c948810300740d1001840440460700844503507007404d9280c4640b084000004e4460424a04141036225000d0210948140c1c100c5100640741c50b415001d40c2c2c103500a8940228800c88100085220740c2c100420007030566041d5410700c2d40c608a84002da02085440b8808904c4549140c410420f281002e00001d84c03c012699080340407070340006002000c0200c6081c505a008804900941020351044111719214030444110646d44c070035032803a0350400000c000d00130800d40119021801c100d11045561807940c85407400050420340340c0c0c0d8400001030000e074101543c454840c856040d40784260940e10340900e61010780d403903941c400103007a604141c004032f0252109103d01390029000041443c15070b021050751100f200801c15084ca8100c0301c6502000c00024408101041c5a00d0415a41103290082d030a0760032983d100303c54081070b481540f0009400c0001000000c0d44035119600 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 25353612 1250 25352362 25352387
    0x604090f02060304060b0f060910030c030b03151006020f0607050d06030209130b0105150a0507051507080109061401170603102c011103070804050307020307091a0a0f06 74
    0x440140d82209030049922900708070307411a00ca5035640d03070000c0c9504d8842000d211802d011251280f8100300000460440745401d10308100f419164003020384070310b0198020102807000501155401e0881604004840d10181c51213030000d81140d80108001c0d10201d824200c15101c00020324a0b030302c0f0043c040702c05600031041840c000303654070000b000590300c0910880c0940c503800c007095004041030400c000011410707404544100c0d00c03042d80c1a00d13098020140c508060850501c0d58a45030745d0704046080c020031541c85500d20030050100004c0a8005050314140c6d4404141004415294030300301072980d4804a8050102d00031140458a03908040c001030741c440e4028003581c900c0340900c1300000c19150341c5003140d00000036080d40c10302e512011160403805240e091000788405441e103011580144405417480041100c2c0c2400101400003c004072040da0364050304541100b44c1da410b040c1c0080c0351000c00e0b01f64210300c036482c0d29501d00d005955501580c2d444003401c44c805160402c1039404030709465 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 25354862 1250 25353612 25353623
    0x603070c02150705101e1506030902030a020604150f0207080709050a020d0504030f021011040504020c073803060a0608060a1205030409050c130311120123060a06020303060409 77
    0x107280002a024491600070030000b18011440c4a2101950a1100d000b907064142c12031078507e9450600b40b00c085a00d007200c0007400c001501c14482d001090a084400001039040300c0c000400017400400e00c108001820303032aa4810094403c030381d00032a1121175503c43c80000d64043c50341440940c01c650f02c06600510306860052510f1000c420110950354100e60940209500c661840c0e0016018001a1070014001c4402c001d5843e240400180ca8000d5000c0c19008580c041804010044200442c0c4080c00c40b4010480012854060020355440740580b1317116401c16114a1007002c0c1c054000f500e000700402010340003810b003030850072111844020141584480540000980e2106070340e210152070b03025801640d61141000d8910f402d483c4068500c0641640822042c064012030f103610005036540804010850030040c40003540e01a94620540f04030351800801c0e0f000c4070b0b611154400c41301001061070b240c50f41d515042140181c0c06100d01030160700204005046460550702c0f0031102445130 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 25356112 1250 25354862 25354867
    0x170a020f040e0f0c0405010b0a1b06091b03021509130b010201061802030109062403020309240703050601050a0c030818030705030a1407020d02060a0306090f0902040b0603070c0215 79
    0x42115140050b4010f1000c00c41d0030244000050b81403034081c00f070140602c03e00c203915000444500900e089172840c040a41c0618182d000740400c121a0022805560010010f4010301840380c0d1010f40f0504074401244a110880d44040a007001d14066480d0004020840190b4420414045000d40041e481043c115580d83d01c0102d21135a82c18a28420041503030030050300c0e581000d0100003111015041400341a60303e042588083c042030a289003020410301c0c0140c3c80340c8a05005618011040103110f802c9007141c2c88030f0000107400c9003601c0c480c3d00c8655040c8003d0710b031900192154411000c0f030800082c901440304020a0080038a95042030210034540c5d5103507081018141907400086085400350070020302c41121980c809002e40d01000f400315400d15111040c0d002404614587e130000f40036100c04140340005074020760080d4020b0103c900d080c031841e1540d24003800100300c0144201e2081d07207000c000600034106202540d104465940320403440c004a83c08105c030098606504c91403c03c0e08 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 25357362 1250 25356112 25356131
    0x50715020c010b04050a0608030316090e01030f050d0f0504051c05030310030512030717070309060e070501140c0c0d02030f0706020a03080f0709050f0604030206070807020109170a020f04 82
    0x26100410854500c00700015a4000c0a01048281c9030050321800c07060381010410b109480c1d021046030b030840300c44101007041918016003a902c03440c6542c442c485101095000000b030140e00c00c00c41403080d00c07800030788141e01180d480a84030385820f0050f2078002501407009224030305180b1440402c1010b03808013411040c040c0d0b5a00c0307207182c1c41241d02c04008003c4440401c10440100660425070309100344850031440d082400031320300c9481200d2007104244060109550034000e511450405810810901c8800c0c0000301c0c03596181114460540041c10081000c91200d0001050340c002a00440203480d81e405d083d81000070030046034609a9050140c40117016070580100904401001250007501c001265410301030076800000b40301e43c180e500000100300307103d5402280082590300c1104c50601804d841d001003171050086800c000d40000707000841c03600b80503400c0003500398903100340d840c04807568507610802001c184001c0705100c168440c00e502801032504404021348048040c100080070b090 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 25358612 1250 25357362 25357403
    0xe010513090f05010617060105071a070309050c03030403030c080c01060f0f0305070902120601080c1c0b090a060803040911070210030b09060109060f081003080307081806060f010507 80
    0x510381c054884182c2d11100801e900d02d480c09000d00402c2a81002e442c80c100c500040c4014080041921f03042110000e41242001603240002d004050a140c9000781880c141f50043c004040c901000d80302841f450030100b005190001c200c80c281e079815911905560f8181c0e03106052074004480b81d031015500d42c40f000c03551200803036450703004007051840316400303515500f052810b01034182c204020a9004105482402900e0640f00c1d030028420319204c100c0f81e8800c800f40030a80204100b44107080c5581940d032000840940050382c0b0401e080352620340e5500c956946d202150054800c2c2c001c5500240b20400641482d43e00c6020b07407015180f4000d00c4c08619500003141664026040004265144149010b9041c40ca219607032010080c00c1003036007142800d002030101000388890030200001500003600c181c8071804003200440e4070003c0d441d1203081c0030754050403030b00c2d040301c0c0c807090000c0d16a80800c203010001812401084040c021080000324140116041c0e0300000c41a11281c445c1011b0b14035850 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 25359718 1106 25358612 25358647
    0x906030f050402062b1505010e0a050a0308130810050108060a0e060114010c08030f060310021309090305130801021b060609160c050105010e060406150f0e0105 70
    0x900440030740350045c4000b800b50303201904054003600340e165184188030070f030340c0f090300d51804901082c401d010000b0380c540704031548512480340030800708080e10f000303040703808406041c007101c151590802454500001c045d1960359a54034010022000e0920003e500020740250601a036540c210b01581d44000600a28280e01c040079803140c03280c0e005a40500000e0303030204c8032a0303d9251110080100040c06c0b02c0f424003078020049504204180c038030032100341c901c0e42d0b0401b00600e400c00030340900401c5c001a00724103010b41000200150718100d240c090040c41c4050001d41d5400c0581301004002ea40c08290b03c00540c4900203002c4182c3c0c1c0c030440b650b800000700461605a20b06000c08454650303015002031b00c40d5181038004a0240a0b044c2590302c904000e075802e02040d0382e10099184032201d401141000a0494644100c40600c2490548881c510515056080c86180d90704800c00b036 = true := by decide +kernel

theorem cover : BRFrame.Cov 25179862 25359718 := by
  have h0 := BRFrame.cov_init 25179862
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 25179862 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 25179862 ≤ n) (h2 : n < 25359718) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
