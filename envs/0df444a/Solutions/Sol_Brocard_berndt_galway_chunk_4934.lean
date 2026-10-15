-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4934
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:12:18.982874+00:00
-- url     : https://prove2.me/submissions/61bd0aaf-6f51-457f-b6b6-68a1dca92bf4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 887230215 ≤ n < 887410071 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 887231465 1250 887230215 887230219
    0x60b030a241512060216060c0f1205042f0a0806060102061f0612020c101a1009122a091b1b0302070902130509010f03020114070320030309100b 63
    0x41d0402e030128030581c0107860364a0750385a9560300b1086c2540c1c0c0c60100d03482c4080c40780204d51010185203003142c02407220001c03080c07401000c3c00700e0718050ba00d0305802c90601d0703441c07130582d1041083c801000b8054140314801200150505020f0754a0f40c0080742e60f80c00864909005102d01000a031018220b0120b0045805000302c450b1101c900745076082e646004901550010b90381c0c20f000300c180b040c0c2c0402c055091110348a400061903003401c200c0460722011141c4003402007000c080b001000c154043d425000f200c2e11302c641c28101082c0ca00d40015000e102c284068041c94244039581002c04444803210104ca00c60a000c101d000c4100c800580341c0148801e21303e004c18130140c08034203008900100300d03092500c40d106841c40a611510707000c0c100d81180c04000106258044140124100300f10720a014003c031308014913801d861076000a081009000c49009111404120340d000c0502134120b8810004114100072180003813184030903583c0d04201d400450310320402f18419181410b61103100c00328140 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 887232715 1250 887231465 887231489
    0x1080607031b230403060b0118050312070204020408030a120e1605100908010c030c02120c120706180b0a0516020607030c1407030513140d060b030a2415 67
    0x802c1070b01d00000040803450900c0031070740c0d0070099840100007003000d9441800c0010b9040b4001c000107000c0074003500308543c002c41c110313400c0c003403507800042d891203181807404115507a2500d48080b0700a8020303580460043d120204042e21601c0d000341c2850302102541404005911909801035540c000000440c00301c408540780034807580c104405e18140f0b00d65103003080614182e036911454211241d10071804002565200700c900460b505200c40301030440b41110351030030b0020f00030340381b0f44030041d81b102001c202a001840004004460b00841c0e0900e0120310407000030300803820a8126220203c0f60f0000c490328180000e25a6034900451003206ca0741c81d07004102d5540d0b2280e06400600c1c50740850002c0c080d000d20ba0b418902c0c600c6008020891181d954951507100041050060704013030340046188a85011000408ce03c6000d02907002c5030b00240003050411101d8003103414100700d4140549517544032035580104400000000c940d69112880030060300704e02c50400c920103500b9011b00c56032296 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 887233965 1250 887232715 887232761
    0x206042706050a0b03090a0c1403070501180e1306021201050112140a0507270306150b0306040c0302070b131b14100e12010e1011070f03030f11030108060703 69
    0x13082406143d02400800c1219465a07058a40c4240d2810303035131003113021210258460b4031030306060011400a013800c1c200840304003001024000c009283e4014030b20740b0b045490000702c0c034000c86180c10084940040003159114039a44550707104650034000ca038046114a040c48222819611071801c00d0402020380d40c1050b11040310f180c003d000003414010410080f442040d02055610b07401c0342041e410b50b52200715107407540c600041991405c113140048403402c2034040010581c600102e81d030044044500003203c460b0b40d041640280034450001d80b200c5021020440fa0b2020403185c000381c14000c0b0b800b4001186503941c04a00130340d40f40580202801040820301c01c0782001d400200c6a00c43c3d5040400321000c410380030174030044221841d0b01c40740c1e441d1030804280b00800d02c05040c4000b54040207200901c9443c0e0100350038860032000400c25901c400144003410b1180c3d0208002c05804513041c0002c11468401d1100c0d90800e0046402c24000c4a000c01c0b480c5029215018014210f003030318103080d034 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 887235215 1250 887233965 887233979
    0x5060405100f0e0307060e1206090a29010602010c110f0d0c020609042a140a11120d0e100605011403101d0a05130b220206042706050a 59
    0x480d0302120388144004900010703144d540c1400b2581c041e00b0a80c0d50341c2c490b01210004c1045210041c80e0007a01500807005102c00c05030040740c00a4070700d80040c02626001c40700847c01131031b50312540161503185800400401c902d035064008541050341f41d40c0f00011412030004003070319098140403041442d48200102c440c1140500c2c0018030769400104a582060104400300d419030b0071045071900c03c071a065542ca0205408409121000f0056291005062004540e00d0701d0341d206020180c0300344004031a481d90206000c0101c00702a4103440c09160300e0f001c2440b05540903200803032442d032041c0140e11013a0304004152144804584059480c4090364882484184681d40007914940000001200204031a40c9000405450000c040d10240702803903c85d2044c0100d903406814038510ac0044104000461409200c840d0803000384a00c4511405020000b50560040000c009412240100b000a541c98249008154000301c0404070066140c0c2e4841540841d003082c098280d0011940100780b00c22 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 887236465 1250 887235215 887235227
    0x7060906030902030f030d0507090b03060901050603040f06380904030f090e04030815011707030b0409051905070b0a020a0b0c0f0d0e01060503030c0a0209041109041b0506040510 78
    0x2c2070000c0c00340d4240c2040100005c0c00c1d0340c8034130744144401c0d4803070041c481c034641d102c40024010310006180702d046040800002d0240003041c0b0406128800200c00b080c1407143c180300050610754411810003103100340080b062007030071280007204030900d00c0e002120000d0300381030801c1c254080001c0c1002169079603580d042e207882c40210101401c001030044d001c5031b07003030f08918214041c50283c0c903100c845261034104820b6000b681c1c0340d6113040103510b5030305007208807910b107a0f00c2d081219801c0100d00d40d8461740105000308030303218015016108590702502c1c2404c2410b958a07000f4019800d0303d402c240c442d05501040c1c810001a4801a4822841d10000ca81020000354004000985c41440e06081d007806c0c0981d0740000c3c41d5000025918100003007031030b03424400c190003404194003a50800100c0500d0b5034951005101c06401240e1000c00a01040801010b0100296001b48141c04908160500419070b602d6026030310440851113031b010546140c1070068030115a40203101e0010503000d01011550 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 887237715 1250 887236465 887236481
    0x30603020f131d061009020708090108090c13050a180b0f040303020909161706180c0f03070815091b0a0c021c0c090912050a1806030e06090706090603 66
    0x403940d034808070f41d10b001042c0100014025910740041080e81010381601800381d0159000c1a8110b104000d0a000900788030140c540c1a07400b4240800543da90710551030801d840d550405070300180f02401006c00344c04507070000f4000c0c1400352040001031801d01d00e01048550180c00900324081d02c00000300100303850540d507a803091203454090b083c103c1d8003000c01e006140503603808070308400d5804540e24041e480201042d920b00c605490007604c0c108500480e014006d400321302d81d20708007804005212588400220b07003215003401e060b01c1d078038030700b60384028a8175109540360142d000b0500030b455918505102e5550043c45e0b030450032000440341d0103c4454583c001940304d802c0c0140c076207110015982e005c0007030341e5554a03049a00907003141480c19207010306154100c400c00500e0000d0180204603a16004101c20200341070070b550303c002c071440a94172130081032100a50b18800c40004100158540c000c901703412141411584103490f0552019150802c0707005042c00240751340c0c020000340784280c1002d09 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 887238965 1250 887237715 887237749
    0x203270604030e0628050301080f0622060e0d030b190b121f180c140414030a060501030f2906040b15040306050906090703030801053a060507030603020f 67
    0x1c031260b03d505d511142c0c0c140600c42c0d60200340d010004108404082c0052001c182da0103019041910b8038030544c2d00002490000f4198490000c044401040201c0d0300817100c42155008450700042c82c40002005030444a851078010b854a6150004aa5200a900054401c2d072641642046c04070310141042070310081044040f81c102c0d40300018440c1c6400048800791440d40050701d9000788072040003059561003800a81081050301c52648049514410b070b0f8140e80d8000c2e0316115040d50180000d1600410f032001505051030b1000000404c00102c0c1c05000140c41004001200300341000041c0300458185c2c50301c06171000d1040003400c07600d804d61100284850040850220302039281c48070742c00d074000c0d03002210300c6503a8000307021400030704008207948203050070020304940341150fa00419001040c81000e001f1000b1054000c10f58851244150840d10010700f071403643c81c120352080c42d00b89002e0405403030003450f04e40819071003446401a00c00b0b0304d030054407c001c3c1c8080030003072100d00c03054a00000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 887240215 1250 887238965 887238997
    0xf02060f0a1104090e0a050d0e031e0c060a020109060f060b030a05041502070c03050610060512091207030320130302090c0d02070309140103151203020c040203270604030e06 76
    0xca8030310151711840d00d01d80c114070700a09000d010f07407420601c0c145400d070002c801e02050800b03140080d603002540030a14040b03180406048425107902e9031411240c07080040c2d1000b0301040b042d010582c150312a021403030050a051245408d5451040d0032901c56018103080310f90108005103451103542c1010341c00502c6560403644505440e54140c080307030020041107030801000c40d01001440002c0181d0360700111300c0042c85ca0080c2ca0410090030034801c0c129440d00d407542903000291042818481030a0b540d00c01a40260b840e5018030300140140340c20b0810030141c000d8050301849110104041c0c2e904402c8147e0b145911030309607003c01101c404020310742c81d5550420071803404000c8850001d04030052081d1581340b00a4203109840f82610340f1034019604241c500702c0b07041c400d902e105800000701c1b06000d50304450440141402c030b0a01c0d50403114075811900000503c45410170201d00c6480341141002500c2d50442c201340e40b1070f180d100644018000900f10302d1140800d10304200100900080d0000c05 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 887241465 1250 887240215 887240219
    0x140d18050108070c03180b120606090f0d030311040f09140108030f091914030708010218220510090f021903110d090b070305060d0201020d0e03100501080109030f02060f0a1104 77
    0x3031421a08541101d54009004203e040e1008c00307004002d6046141115014140342760300000c036547e4051409421301c03034040019000141400390f800880784444501c0c48559a6440d2206000c5a450b244a1010018901002c1541c030760720310056207040e81c603250040c6180c2030010000380003940042e05203a0340145d40d401400c4102e8a43c9a0040c014252442c151070b0039610b000406090545a40c850000c9034010044024003004000c5070b007036400002c44080c2c80c0b03081301d08460b2060204a14225424900d01400d210110182e150340d5012034240c07075010310152050140000590003103024890340c070003002d006900a42e000303402c026100e03585c96260130b040404003504402650301c10001034030103054440520034040e6050098a0b441501a9524001c400c6290300007035448290300c80c20340800c40d000d5040080d980d01807204845012480000b170183d5612164042d00070801e080b01100460400b400404c02107001191041c81407a10a40d440c600381c1d1201c007080050307c192164600316040070000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 887242715 1250 887241465 887241497
    0x70c06050a060f0f08060718090203040f0218040b0606090618030f1b0102010c1b0b180d0206010513061d09010609021c0b040209060403031b140d18050108070c03 71
    0x81e0b002013400031440c031801c51800381d20030304100c40541100704011401e00030000500c00d401c4c40500b01c410350040147d903542c1d00c1c10045041c44604600079403005000c051041c600701b841d8142030203580070781814038140d1900f2007080124400e1f2220150840c0c0d0502428290020301e42d951881507402406030790405001c003912909000700b980d01000700210b0078018640343c3d40d0911a09164209904240d03000754118400c0c60611450141c0c0101000240d0b07001802d1802c04640320b030f503074140410031665820200f040107510f6110034054140584254041903499a0b2180600c004456040f00942002101c21608002540000704000b100359208e00c80061501040c0c8000c1120362408480c900000007405000c1c41030f03424806209208500502081405984e01c4007181c0480e94107042c140c40d100500140c080c1c1c0c0c030b030800002030413900c0d0381100c4103048440469803d04402081d5100b00c4000ca207070112115030419070007414001a00740c00000e002d140690b004480d07050003418403421410035041 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 887243965 1250 887242715 887242739
    0x1509071d04110402091e03070b0f121617130510060e09070312030b0a030204050408071704060f0e01051b0c011d10200703111305070c06050a06 63
    0x20003009215184400c1100340960240c400014041c221020351409905800117600003100038441c100148030131207003400c550f90401a10008040c809251a29030782c41f81900c859031b40282c685d8101112458002410a0403962a1640400e200c2c0e180c50070035104102c50501042d00051041100c803c01e05032880200e1020080070304d10a6403090045039460034808003c0e07003c000604112401c0d842a18244006602441040c2d116038452400140b22001000000c02e001445e0703102941240c0b820f024401030000c0c4000505a603030040d141991190001c1e9074240c158440c81c85a0b400040d280b840303405540740716070351810003040140b40c00c0e0b04001d000c5070601082d01c8590303081005503000810008041d40c00104840c0302640711000200000da0002c045480000026260360401600320140400c003d4400c03540c07660720011314119000c840d201c0c44c1c60b03d0590042a1828847d00282d00202800c807482c1c0107992141240da600d03198000d041d50f6641020f004080c080c0c0031496164100401c60b846010 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 887245215 1250 887243965 887243999
    0x140604030506090c0f24030910060b040305071703040509041109280e0705061303080403030c1b0305030d0c110a0302060a0c02030f0a0c030e21070b0a02150907 70
    0x4001c4c2404076020410030080115801085001e080040444054040102500300d036202604070000c2d07991340c0f00b40c0d0f20360900800640c0c082d1054640200418103c407220040c006503481039044400340c54071000003840500c001d4008031383c10342c02000103200c1800c100d01000d401900c00d811481c45d848400c00010060982103c4801401610b0714010002840c1144004c179007900700d14003000381d2441d1054a0b500c4003c0d41c01024001c0000144828806100c00301060085130803180c0141c035180c4a2400502c02101d0400c29940c4540c402c2c81455154480c0c0f803900c04070795000340214600024034103100080d217104032000c0300f4458040700b180c940500070b00c20310884912aa02501d02d600d441c0054000310341c0c07079030440d80843d8410b20458142c3c60100b0201c40500c42c0038140b00025210f585021907203c89010441c030b0704540e0500c29802100c50f000b080e5580c289204050b19510ba450b01500942800b942c1540300050f480160841502540405065040030018041d50503140d11414420703240c02d500 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 887246465 1250 887245215 887245231
    0x9040f0209100311090d0516080f06091c0815102003070309031b0801020d0c020d11060117190807021206010803091513030620090a140604030506 64
    0x1e12001c035203020080011299410b003030400409022600440e2140101130b4403502601d80e1608100034040100b1400c0454194940c80030780c059125500c40b030f00c3e82d410b64840304482c072408000c200454404541c4040304508980448001c0c3d0030044100e800d140080d000d4086007015460a0446803225881c4c00c8180e0081d86808440010000505042c890702146159072508140041030002c4e91100c1100d045941225071001d000944080e40031a40c0c40c07d40c04001c0c103610000e03c4c0c48103c10141c1024505550b21380a0b0f400cbc40c1c0d9800070940e031600060364800f0740d40d0050380c014490075000c010305401240984048a81348502c40f480d0418519a420041d80c9480002c1908000c518180b004c00c403115400310040d08031549485032503652801a0000b281c0f190800c25950f1010034030440a40703240a00c400e01a2000c0e43eaa130a04100030304402c1030603c005034242000200030124030007164111540a0803228180c2e19112501d55030404070391489031b1000f02000000049a010804c141c0a2460 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 887247715 1250 887246465 887246467
    0x9130f0f110913060311040902060c240106020a210302071e0c0510050304060911040c080702060a111903020f03101401030c1d0114040e04140105100311030309040f02 73
    0x1801040106403a442c1c194007819a044c00c40510024840f500040b411741c2080d01c012500041030301c0007403c24042c45009003e103214103035502d143c2000304240c042c2e00100468003980320743d0300d400b0120f0b00d0300c003400780c0a40070078402c901403d400d281041000c0300d2410704c0e00e401420721010780d0329992420814075a51700990300d81c01586061060401440b03004002c200c964132500c5074005030141040c000180003a10684e0340700c4500f0140001c0100c0129400b0340104100034000c45450090446132050b14124010f100321800146801440d204484d54020102a82800c0c00072000e59401419500d51007001003623002d001e049a03d0f04884040d500074942c00041c0c5100c0790420480f000c0e02405401c0c860304050400044001094010b4080c01441c1c0c001c2208010300700f80d100041e92000f84441002e13654140004001544484018405019520411802c1c46410404001c41d00743c6905a0340c00c81101c6000c81c04100003104d07088543c020200c0070342a60300700300d0003034001811a040206e9014031160 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 887248965 1250 887247715 887247727
    0xf0618102304050c120c0915030c031509060a170708030a081501080f0f150918011a011b060e0102040909150501270f0f02040501090b09130f0f11 64
    0xd8940100f0b0f50203510a0203442c200111102020036951003d001c0b11013142c40000d00e805180c840c44051642d100c08501c51503641e00f04581040700580c0110b52403102c0c17552080c008802c41c50a418041d004120050440004da0308210001d00f080c0b1941c01442e80b03c0c03148401c0080ca080c020700103800d0301501601c580380c0078502541c181003005441504c142c10068164100045807454580302601301c00b03207184003c0d46035201000d211a1002507400194000c90b0301003080702d0801c100f04c213020b03a164240001c1c0580d13114076050b02440d602c4045030501040860700790143e080000d50444980c540150008103100107103407049422070340650841036100c1d850340b03440e00138800e80d03801204420000500c04c0049600d40510119403001d41c41e00320300020000c072031800b02d405450300100020b20340c05408200c0000501c2460000354010f22900303011400c02d5400085034003514060382c00e0000054131043d10003004564071030003044010401d202d07695070340014442d40d280c82d229002c00386040c01640b995a407 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 887250215 1250 887248965 887248969
    0xb0a030b090f060108091f0c050d0501030c051e060405090423030a030608030307021c030905010f0b0f03030313080a0912030f23192706080f06181023 66
    0x41c0140400d50359403001d000f10f03200480b45d100c4071600007000580003132300540d4550200e900d849002d49504001e414600040244514449010216070301103603400e03018050040a0f400b05600301e0042d550141c1c0c203000c20030440c01d026032f0300341d48188240089425100c0d400103403515000340110285280d4400b01d10168503540601c583e6000c1c0110900030350031883e00c85070095984e4003580a0018061455490a030b0b0b29001713401500e2071f10750100003400b10440c000d10000040c24110b51803072080ca4480702e03040d40c504020040724000d4110100100c0402c4450722116140e0384140c103000c0820075034034400186d81c1844410740312407a21070780e103140c4822080480205807000c0d04480e071018007681d004102920141004843d210030b03582c1c01e100701ca82d0030040280d800840102060301c100c0c1c0500151034190001c510118240c0b41982c40c0d1200680710f0300760440c580d88081f901c80d0740003981441c420000710820442c030fa41c0180402410703190035071150000300c0440504070404811001c202400040c0d8 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 887251465 1250 887250215 887250227
    0x201050601140c0c22020f0c0c010903051011040f03060506280614090907050406080109051003150e030a0323090d1209020307180b010e0a0b0a030b090f0601 69
    0x402a14032900d00f014040351410340c9a003895860144181c0c1060811030840c05034416208070f103854507404545404c4511547c000b9540f1612414006006038802c180e100d6010f004048141da4004000305800041d026101d4010300320030306160761494081c04005030392104403800c2e8000d14841c46010a80e07062000503c9400240580c403101002c808280c944e0503c2c0311a807400b01107031040e1501a603144240348043c040b51181e603e82d1a0000c0c440c0c01013058403904000180304582d8035944444842e0f985100000031a03005540001106c03104e584100040703040d41e62030300000e519a410014605d0780e0a07840500d5503202e45107010100b07480d00e910001c20b03107106200c8240d440342d000c00100240b0700680c881da101c955038440c1c0414028100d2003118284400c1e400050038903405004ca481250b29010b01504a800c209908140b860070410703034064a512030000030300400006042040c0250800d41c1030311860300301480c2c2004040e070341c24169070281e482d005228025071004644010b1414100c00041603 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 887252715 1250 887251465 887251487
    0x61b0c0303030614150f0f07060c08062103090103020c15010f0f060c2a0807180c0f020703020f1c150c17220501050f06030d0e0306060d080412030201050601 69
    0x410000e101141d885c41e0b0060b8100c45182c43c4081145645908040c0c2c000c2a5025902c0c001e0101403030419854600d0f0b401c400c1d0103008490803590590300c032406100c8602d600e04001d81d0719000750014012004154000c0d00501610312082050303480d000726110681481c20750980c415040c00c2d0220b4010040421740250b441302401582c0360200b0700c15502e848980814040f104594401400002603035045a1051204009482c091007541e01d0795550f03c900e01d16200081c044038500f50300c0d0410b4020010b00820b8030440060244e005031105925503001c00c01020b020b038000f160404812801050b41400c40d98001089521440c000b05140554224103801c2b5030310710511806010b2811200380b5581d14101149a03c00d14480c00824070440080c01c0b0310b00c405101600030020f609150900c130001e101001c04920070b41d015004c586281ccc9103d4022601500d10312140d54140d0064000310310182403121034001c20307500800d0047d01d05a0f440390900072107030340c150003540142d541e20305108a56900c0101004 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 887253965 1250 887252715 887252719
    0x80c0a0c050414010311040e0703120207050d0f020907300c050403260f0f03040b06030606130f090c06082406030a020c25050f03010203010807061b0c0303030614 71
    0x1d4101c210f81180140a8180405404107400c0d07a01c4000d0340c2d4071500501d0700362a0903c00d07661000d03540e2403d25800f4280401d040d000d8080c06a0219090420354101c13103c454021011307104900543d0240031680340c0240800d0304226411811000010301c130f02c030080d03844c0780b919030802040450b900150100d40d42c0181d21020002c080000304007040185030710140c80351464400d4803003020070300d80356030161182c03411048100b200030500070090300b154005903100c1c1d8020503030520166251000c0607200e020407501c0d00c0d4400e0044e46419640c000c15031000e4440219041d0000340c1d03114071b407030300340c0d480790336500075000260076074100000c1d1100c50b07040c0c060343c40b03442242018111411000518a000c010440c0d403403e5800b1948041c1c18404002000160800080703c1c000c0c4400d00c1d10304510090a405003d0003622900c0e030b004800c2c1014030840e812200c069018000c0345050907411206000449070301c1c1c2c10340e501d41e40d02c0e8012900411200700210300c40d4900061280c5090a1017401c1c0110800c114 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 887255215 1250 887253965 887253971
    0x31716180b03011a0c0109111f050a0518120a05280b06130e0303180303090c0f010c0b01080d03112107091a180603010f05090a09080c0a0c0504 63
    0x300d05a5014282c2c1d041d03500b404455803000c00b2030b055001c0d65016070243d003440d960034411210300740403510300e000d10701030816500f058900182c15607008a4134011022040054410001c0d80115446100a4a01040c40401d80d46802d16020000343c2180040a012412a00507034821010000100103451a03442d00e900500b10b28224034244030744841d110f05000d03010352041c074000b610701d80d1109940d03900d00e40e00c00010050313000107120896030394004550804102e1005032075065240400001d5a100e16451401040b1f0454241d0501c01201100c011490510001c2d10300c890010354040c1c200e50180c0040d80061041b8400400020709554503d60300e40502003040220034109a170b0700e400c140404e070840761540c003540c0790701c80201c80990090f40403030415a5126400080d5240c050300900d1507403000c200000b0704407050010070009103c2807144071064040000100b0090404580075a4440c82d090f8000410003003a80360030200d84e0002c80310755201d0300001c11400400044201a60150400740c80030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 887256465 1250 887255215 887255219
    0x151406030a0302070303200105040f1b0e06061e2701050f0a201005150a05090f070c0803010608091608030909060a1d01090f091e03171618 61
    0x1030b444d18400d000160070804038a04100e1209403245007150f02c03101c42c0e802001103140c00c1c1458512280307504411981c0444040d519041c140c24000b142e010740d03203c04410a11910364804100d42ca500080003151001e03000350303260034185100380c040c02d0a20707490b000c0c01100c04c2182c001c10130304d0303c60440b03014140301051001d020030b8001c520a90301040040d05102d000056044a00e01c000054601410080d22800b00074030440c0c0104c0c0c000382d002c0c08041c02c08001c60003000c010480101042d005080d048084c00340000c076941050024190002101d06003c03820070a95101d042c030607402604214082540c88061140d40002007001481603082c80d00080546030a1107412a00c0b8801d00007107034405e03154800072036900d50b550f101060040091140101055500d1210045480024402d40d6a40e51800800d42410507443c012071180590022002200c0a09030004c8001502c5454055007008012100c65095180c0307465030902994003480281010801880000c01c1e4841c0b40c45116130000d642141 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 887257715 1250 887256465 887256467
    0x22b0b07080c1603021c05070b0907150c1b0f140f0a0501030b061201260c0f0108040809090702011a0105070c0303051b03040b07060608010213090e0a151406030a03 72
    0x15a020200d803038405440000303d50804a00d0490521245101031009140700c21140790844020540980b05032200c0159035240558603456400c035101d503000b05005201000030340d911881e001484140700e1402040c0c80400b000e044010303198140c208080c0c501010805207d44280016070b401c1c110f5007125944802c4030b0900c0414076003405445003174189622001c3d19820303595038200761081510342422004280d80c3d0340c2500b0034541d101c203010b000540c40c0c80c40b42c1c01783c0742c0b1f0118401111b1207004e40a17200c0300720068011207900d80014001e8504240c244191006603552506180c01504903500205003101410f0a25240407415900e003410f01c142080402d0000756017038001e070f04580c3c250401c81c1d10742c0f10405032010a4860103103485118000080c0205d00c07100030710040c0c408035000301c0081102c83c1d1181b0403a400c0344140305403101c841c03a40c150f04100700c511540150003541c1e1102e058803611a42030f0b58100e099100707650b20400382502d500000c0c00040701d140880d0b80c48202100100030b404200d4074 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 887258965 1250 887257715 887257717
    0x21c0f1d010c241407030509120304170d1b0207141804030302090307031202100603031b050f12120c0412140304170604030f0e0f010c022b0b07080c 65
    0x30002d1485820b43e0840203401d0340800110030100c0c0751a000e0100c00450701800b40724107001c0b94103002103403600010800502c0c0010340084c26168110159186480f103440d01e03400020b001c401c2c002c501c0f000700300160801c260340c01400b02c2c4d0400c500300900085c10450003e402d14200381c000d804081401e0038800314903a15800c2c0d268140c107041100410035150b03402c00310003910404100f5a0144200030000042000109440030703001c4a6a0940e0070004030919140d09452961001a00240d0b200301040c0e500c1c0240c480080c074291140c17040b10141456023000a06007890300b024401d41441c0492207a40010744060f10a500c00d060002d4246044e05103001c0e055480343d4540060100000d10a1400c996041002100e01078007419414922641d00116845da482c0002c0300d040740040c3c0700c0c0c1c8840742074600501114504403802003120a40d166040011a9105144042a03901a13a4050300c02c985c0f1030100d108070b00f0300c4100c0444017801041401c164100308006403180e801c00419004018201180d00 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 887260215 1250 887258965 887258987
    0xf06030d09060c050106051c0309080111190c060e0102120c0403080a140d091211070324020706060b03010518010302030a140102070203070e0604150e04080a021c0f1d01 74
    0x10030305525540f982d06102d0300525158000c141c0150000381d410382a01c010f0000034400074402d9903000b0000f0707103d6920500343c1d01c42c1501c0c0038120100348000c00c00401881f82c01c8034000d40d980f6000503901c010707803922006e60300202503800060b5400105121400400c0c0c07461607004440307814461906147d40c1c0c0d050541e02c10842000104810711200c0d0880040700d030100c6a060300c3c2181d050000141d181040c8243c139683c000300b000400da00360a4100855000705825003204d420040700c54203426181c0c542d1205c007078000a520f06142e401c100e01c0001070418401c0c0c001500310049a59102d6042c00c0c2800000311304410001030007105e0f50010801030b40c0018800c0400c580c0300c400d81321007240d50010140a40500e400007541805150004501940d41e801814403801c0111400c0c050300c0101071402940210711f00440a100003100002030210345041c0c020712003d48241304131114410f205080310b501460207128040000c0701040d1003490247c0c4141000440a4032107103106041c41e91100180c00c400c201 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 887261465 1250 887260215 887260217
    0x30106090621150b0c030a09050103200c0a02130b0306090f035809080f030402061e040f090204181e02040609170a12080a110a080f06030d0906 63
    0x204001c2c596821000c0518000300742001c5070b00d44640841d801691203400c100e0704200080e03c2400c0c0009c443d8401d01a9a50414a116192000580c044005083ca500c030490300d4000e0322981010b040183c8916000c22201170100d00001a841c2000c802c2600704400a0204105035004603e0100e42e21000300803219412100790170003401005280e41145403844c042d039491400914440d0700c42d98110010f005074601d00956030704c4800a664450403c0c11a000c000010b001c4180030f0110494456100000b160000c2c001070509050040b82500058040c0303880b81800300601d400f207002c2100511103400b0710080c0400c00415400c2074203010f202c3e60040c801162103003403240c5800c907070301010ba6403204500000c0130a44065542c1c50300d80b48007501107000c03440ba0800c456945508100fa5880200c2d1401010782e100842d8003007180400004c440001c000380a0300724040ea0340c2051064070400c00c0007052002c0d00d43c2c817418030500d040004841c00c40401003026009400c4590029003d0782d11051040588100d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 887262715 1250 887261465 887261471
    0x306031c12090503030f0108010c05040302011d03030c0a030206150f221a150304020105030f100b03041a0f0103260417010605190b030a0926030106090621 68
    0x30010484031141d091441d00d25061034803491a050243c04002184076000404079880360341d03a1000040c0c00c0307e050301c0102000644c240300500041d8400c0c0d48284030059a02450298968002c0029045510854043c0200e074817004000d001c258040c030a45d0790087c00c0ea000714407440c400c000461460b44003001c20a20642c8501c07d20055001e105031140c0000103908010003000c029041c030355400701044031b000c521581030035501141c81000101100e100320303810b955182c195114040300c00a8060f01404c00c003000410190b0205042d102503020b03500c524020b8000d4009920100701c5154844800fa00c603540c02074007040140049400c141e50500010706043d82d00210b41e80301c0304200d10f24015508101d00f81580243d11681c0000705401c4002510000c80e12000054214072036009540143e11a16807205424000200c0e507100c5580156005030044140245c055055521818504101c604840c41e0b80d0011006000540e403040c5004081e00640c2800c0b849503201e501010100c50703001c072040d454652 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 887263965 1250 887262715 887262763
    0x12010f06110c0913050607210603080921030f0901030b03010203070c170702042c0d1b0c050d0b160306260f070603020a1d130e03091203070501060605030603 69
    0x40d01d00c0303d020241c004050b5406d90130003d07001413001070100b54901c0c51035031014a2480386030051140c00704a940c4048901e24040603141402514034107a803c4403400c0c80385001035011041c0074002040055a49000075580351f082000260482e11010724450203a84140100050182c200d03051380c1e01980c00a80940d205c000e0051003803158420042c009400605200080c44074803078040c1c0c0ca621100000c1d0f1181e00399040a580d50765600c5c1481c10200014500e806040c0449101e04525086070f40a031135545040c944070004208030322100b100442d24160503108100c5030000218614a40650300e16042c42801e1411002521f00504081200000c61101c04201c1a440d410400320740c4041217502580e5a0304e51f5040060002d4000c030980d00007040c607041d03141640c100d0145194491090090038845ca420708241160001c00c211116586079100c1080001c0706551000940d641742000140195a9040c0b0b07450801d0035204a940002c06000c0b0600c144001643e003c42c0080c002c4428620f2040214 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 887265215 1250 887263965 887263981
    0x10309060e0f010f0b0405041212020403230d02190809040b0a060203120a0b0a06030509160801090201030e060403090509070306180905060603160612060b12010f06110c09 75
    0x100010380d03080078402c001005201e414190003c28895a41c0d200400001000c0c00610050b02c500b00c034001e001a5007040180f12030341c000d40c258a001b11000c44014202a101d5580c0006501c2110316103828026603003440c0c0e2841c50402103604c5100051019014400d01d502400751805e0000c2d40040c05048003040a50b8a51201d138801c6958010003450628903a540b084082d4581d442004440e200981010001e40801014014a0224807015110074121880c2080031401490040d02440c014001d204034030587c045171940d54002340010074000a20102107200140454008031403c3e07078982c001404100101e90032200083c11500183c981240d0355407840021030043c05140c001d19140d16400310140c23400d900f96070144103114400c4007151320540325003042555034001148842400c0031020010300000c0e1241c0c0c3c0c0c00c0403c408480700800c4080d19121b596180350003100c1c01803200d003d50001000744894011681c80205880e0500c03112a4502c400c605458182c1015114014031140303003c50b40388 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 887266465 1250 887265215 887265221
    0x30a05010908070209160f050901051207080a0e01060f1214060703090209010504021602271807060504032d08120a0f020a0c0f0309050d06020307081005030303040201030906 76
    0x2944000204400c190310b25203022150801c08043c0d014440107800503626405501308440040040d85480300c0b04030445008503030a41c84405054100035080c40440030301d9003070f44801d034040e10b296155a13640b80b400071118421a110840215801d81c181a0304000c8940e94031300e5241564000d0740c0c030b03e0a80026050100f99140c660007018010302c29602009000759040c3e100500e0644201c6411010380d0380c81040009074013444421060b05010580100d0051401119600c4140d015040030440301075080102000f6090442c0d0464850580c1050070480e04020300c94000588118101981014150f0721254400c03104000444100c0440d4030702d0a144001e0550031032802d41c6e201000b00c1c3d03100401c22900b11011825a080c06000e4140490300b650081a030082d1090510142c0c1c41402010441d120f10035450b401030f00640c240512417030041426101d82c084c64800500841d009a80c0c0c0c10030650062140c20010401032040d185000309001da640c010084a8006409190114441515041c40740003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 887267715 1250 887266465 887266483
    0x41a070c211404080f01060501210f0f06080114060415090c03020409110c060a02390f0a11090103030909020904060519090f0e0d081e041a090d1202070203 68
    0x2c1c601c0d001c40c00281c0c0c203200244c400a10700100780240102031755600191004070071030b5000102d0034807444400c070041880703602188120790140008038400901c00105001c9418175001003109035101e4211031407011682d50708d04d4010340c0641e0100500840e541c601a0307032a02c9405503105203500c03084190f2141c2c0c820b40580c3c018000b002e00800c00b80740c0d9012101c1ca00e6000c002d441c041401a840040c20700345d480d100340e81200320350580561100c85c003505aa003065240710100d9004c40039425024640c0030041140251b020310120041c06804600e0400a008980a00c180c070710444a00f001800000e070f00c1100035086070840742001d6214000d140010f0050300d61900500e400021160b07203c650646854641011a10050020803082009401c850140c61110502ca61b241d0301c10403840341020b100740310090740301c4042d021080a448032103102c0c0041c0e044c15071f01900c0b07100207000b94503900001c40c0c400c140c105100c8401004140d41364040030b854072620b2440c50f40260350100d800c90a54801f4480c000c4 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 887268965 1250 887267715 887267747
    0x9151e130503130f09140903030c0f040b130806010b0703020307120e130516020723012d03050105060c150c0906032401050c0601030204150509041a070c21 68
    0x203030f442d10040d0104d5a03840c85548426804c154040c00d54500e0b02010501a5901c040039500e540d8940f0707030042150780b140c0c0006541e00000c00c00020040c02c048090411880c240e0402c803d580d20348101d440c90030304103070031107000c00400300300000c00240c00100b00c5044945c07220b9034142140080d1000e984040300c0c4040150050884080d581c9400c80c0c0f41e10091041d070380300b0207205040c019840c040344d0b0307103445001d41741c5c3d030114503c0840385460602c4070070440c0d06014540004070410a03951308001c5606018260a0444042c1c00040c81c140c060091a02408055488c141001c086035405a980c80c007200982c04110120700c08240b0032034040048407820070000d41155500e04003001c452141900589190740d0032010070150722000d61086003250840da018100409059080d41c003004000e1140c00b460441915070b16000240644611403100c0c852400781d440400e889480b07a0a050892800421200811014100c01c0b00001c502c07080c18001c1001c4030001c0d0040c0001144c0c166100584118801 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 887270215 1250 887268965 887268997
    0xf080114060c010c020114102919050c10230408220807080321061306090b04051005180c1204050610090501030b0601081e09151e130503 60
    0x4113150150003501c020102000380603081da03501d155124001143d4001e40d0368281029a0500f010007501c1141c2d0180301030504503074944000307051100400010b03420b444020036030201c0c08181c1404140b01c0d003910120960000c2c89240d00695071140e00741c48074110401900c06040c0401c00b4044000e0940e44e4100c0303030604098440202d030550306034600040c0719102c400c0c41407440204000720040180ea0502a0508809900076408040d41104c034500406881d00450100121140485c80d030091030010300d0068000680c2d0031900b41884240c0300010305591414104920400032500c0e0312840c89580c00e00072140710065255016402c10398490300c20528140c6251500f4403052003804201c59000f00d155450104c17210341e44074860016980c09102c00303041c104a5600141c4294000c900311f07079105031b0b40070007240804c03003a04103844000c100380c4800e039403503001e405a0070141c03240000003500000403000448030b00131810400b0f5400c40000f440d54941c5802d0b003650004016080050b1504140c2603000d50b = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 887271465 1250 887270215 887270231
    0x20f0d14070c1a040e0c040510110c060a120c02280201170108061008060f070c0305160b01060e180412091809031e02060114030a0b0a15060f080114060c01 68
    0x6079055812500410074000c0c1d171000881d41c610385101c221812940042c1101c1c2c00103c1507802070391440c0e0750307015554141c0208407c890007542d0310001020755440d6a2075440e06550b80e100c07032200b162010500c100555025003a2507241e086c0206071182c1007480c2c80034601c0c60480e64030040f10032800c0c000c0046030481c03004001055200010520702e00c2041c000300700d0303034890350364201040e1340302020307108c0c0c07031103a014400401c249030b2140320724070411030181c20003d240c00c0340c0760010100b038900d10750140d586a1070380c00103020705a4485811080040c04072041e10200781c1c2c040407100403000c041d1005040204c501d80004405d80a4000e040c02042e240aa840381c002d001c1c1a504064201c61104400003100580100b01c050700955004901d140c0c02e074010440390b800d100340038164880c01c075900ca6244c424540300ea40001c00654018ac8a001100e0000c5101c41c443d00030601000c102d5048142405241002059626172000485044520300e030b906240340c07540c03d0b010070218490289007103641d508000788 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 887272715 1250 887271465 887271509
    0x1e0d2304030e090714030c19020601030f02040b040207081611030a03020616030b06220e01080607080405010f0c0e10140a0503040c320f0d170c061303020f0d14070c 72
    0x180c6224040712382440c0d80030b110028101e840d400240001810030341c1d00b9000b50054203150380100040070000c1c1c001071419195032600503198011070030070403621242100e4081005103548101c4200142507009041e1481160340180d100c40e00144041200c500c00c0f802038844602c05e0b0016200c101d00600241e5980510148469005846101e03180004100c1680001c1c55a042c5040504032a00c0700060f2150340c6840100301c81640000d4020341d8150b40fa00d02c40c0f840001d4a10440f244c013881a2545035844001405208a10086405050500c20001c04c03076100e03103c100040b00c071445403134501907559944030304d4a074691400b40c1d007003003051008480c18a90101d842004400c8051000c44907082015600000c1050706019526401d800451452500300058012440c10318201d508488050600c60302d40c4a080c1f070080700b210908a0316076202016410305805009189a001580d8007400d090841c107d009414001e00c0545041800400507140d8180702980341e0302c80181166104506c0c0000307070040 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 887273965 1250 887272715 887272717
    0x10f26040c03030e01050703050904200c0318090705040e04050a06090605010e060f061603200601170a05150a2a020106051e061e0d2304030e090714030c 67
    0xb10046100740210400031741c0500c05035140c1d02d92542e510307482c1c50504000c2c44044c0291441c521040c00f88080039242c1a000d482c0075024451210004540700d80d49048080d038840003099040c0d009440100511444075030100840c0c050700d04112801d1030070344031840c000b483c250703a800016000341e261004a4041107600d4000c0741c1241c220006950f203a403140c50402c02c3d0032458002c0703103500c80001c00c89070302d07159044424003075464000c5c1840790900f4103403182d40d001840302e80c0c141d0110340c02010052009140310103808a645031214010701c02c0c2c0c44150b46c0c0130b644104032120b01800b05002e500217007002c1c01d81d0b000f4200c960001c0e9001003000b040d49890a8000105491210155092400105040c1401494007425940ca030541045149050060001b1076110400c000c01c5089050300790112640b82200416042018100000d01006000500e0700341008291103c0c0d86c0e0a175400c20b00001c2030740b20400c016102c0048544000319101c0c08410345581c0680550140c0c0d4040202c200148064044 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 887275215 1250 887273965 887273969
    0xa030504200310051009060e010501090b0f0406050706270c1d01090207020f061606050a09030e04112505060c0c0601151209080d0b090105010f26040c 66
    0x1c040d40c41181e180d01d480c1c1c51040406090503090f030301c42800044030f940c50340c203d00d40144c0304102d001002d03501c0d040c600058032100e13080280a61300e004010006541e00400d4100200341e52141e890401c491483e846a451046116000c200320011405205200403a0710020104c01700d440429880062007106400c9149024005d44000911000001d002003103c881071804410f00b0074a0301c0c00341e081158020094104120070b0303030880018600769100782c850100070041c8200000c42c0d42103803002e03441e24000703139000103000009003402d0100a00000e07400c00207841e0000d80450f4082a0020400b41404650040321002030f00b070120b80200c040f81c410080241000180100162022640c1d4104a441a0b20030564040415403100004100d41d0030b80c011525500481450aa0700d550700884180f01a60b51f128015a06010b000036080f034031410300d11a04580d088140c981610030b43c900b9001805100b420341900d000e0089085444155007002a1466084030000200594504040c00c1c40903100700b441c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 887276465 1250 887275215 887275223
    0x904060f081f0b130e0319080a050c091c0f08030a091b26010908030a02041401140d2c0a02131109060a030b030703060f14010f090908040b0a030504 65
    0x31030a203000095040c09080d81c1010081d1034088952980c1c4829401400740d82404030113030000f444544c0c00c1d400042c50309198047d45950704400d6092401001040341c4010307110320004541046280c00d42e840306048110b044003001803441d020703907190612064261034100300401d514000002c1007000e12080d40584d107614000d001c1284c0003611030b000444160114020b00074107482d41444c1c592445011100c42090302182c1d400400c034a280c0395103031002e540080c0c0f0070400c01034000c1018407071014051241d0b6540c000900c1c007004000c01304074112619108040140b1202030300d600c1c0741110340190b0705d141d4040d0018203209000354417804041c00e403100304143e8201d105003101d01c0c0d800c90220781c90140412503e9111521890100e604041100701ea000c04d8200d8245922440d0850340c03694148000001103000311408600c5030202d150203012200c40c10741030130000c80000014481440000640c1c03094404006d0300143c1c86019080c840e9250184d03920040840382e001911008669041d04202d01980c82 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 887277715 1250 887276465 887276503
    0x3030f140c0a050d1b080403060e0a0623131121030c16080a05030306010e010309060507090503071d130f0f150609050c070f2603040b0a0203010501020a06020904060f08 74
    0x3c004070200c40010410014046c0b0005100920114446901c0401084222012205100c145940302c800380e421a209a811450038203480d416919003d07100703554070628640c2030f1140060117590701204d0600c80d40042d4012a208011840c0c500f00c0c5400141c8078041a000300d941740c84840448654461300c400700c0d6800d0f1140020002440180040d001c18400d0b0302501450440d40d4080045400d4035041040303a0406445600000106440c1c0c881d40d80201c14a03940d00910600b4001854541035030713940101c0d544d0b407040155500c01000c60101c95082560b0905015100b0340d1803c0c00405902d40320700c05008008241101020082880c40c040e0007070329441001e1000310b40c1c41c40c2c080200c982c01c4408840441c1c0c20001400090300518000b01d81c540316080002d0a20640b4059500c0b081c041c5035000c064200c00000c1c00f0a1010040030306a000400100a501c0c42d810040002d44403028038034000c0c9603e40126000150380e4079038110030064040da0308000a0255220b04152b60350b000d0b20941c02c10015 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 887278965 1250 887277715 887277737
    0xb0c0c0a110a05030d0c060f110706051b090a03020d170a0507140106060c03031523030606030714120c1509270612031b010203090f030403030f140c0a050d 68
    0x40105a414517886542c0380da0076403450320707210700010f4002e03001400d081075650058042c00080300800b400c1c005006d0070f400070305031400003503540d0542e8008082c0d184000085c031144080d5540c081084040d640d041c2d80041800701c8034580440010607140d001d518030701010a480d00450780c40406012800c1c02504620351454409984c00d00700e80e120b000d0100022840b941400119000790421203031120154003422259544940751020407450f00126520740c45244483e125504c2e00300b1103d60410000c502070280176141c001600c080c40d40a080caa40103039401c0d030480d03044003000c1c05510f034080e0001e001c0c100661141041d043d440e0303024062080c4034120400c80101804205181810300002000000c40a51140e808100c0c00001c0d1144034401d07880108044000c0400d16175611200c10003003030000d030f16401c0c59003d0702d0801081ca00d1110b095030040c0820004294008189040340140e130508296511f60b415543c0180e00c20380c161410f89218401407141000b0000070f8115050b401640c0d0380d80444 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 887280215 1250 887278965 887278969
    0x130c2108040e1e0c09060a2003031801060503030a08040f0b04030203090907050306010806120a0c0320011b083a0f0606021b01092d060503130b0c0c0a110a05 69
    0x500c01381c400c0c103103000c0c041c029407405041400080840e4440c038140b50038011000014124034448c54801200950000f00c1030065404c0c600700054100f01008000303100c07083c106000304c0e5483c0501c1c60b80400b0441c403040440c09009035075905441c02130300040950032524007810080e517030381c2c0812517490240c4004c0300094007252240094a020790016903a0042e01d40f10181041604405074a0201c554080c0d032920790300141b50005100000c6200b0228100088880c15020f0b50040f81000801e05101e03681810101340e035070381041f0007107040e40040050b4540345100084020301c512a620b82c400e40a504c40304143c0c1c0c0e5944150003482480b07164080c400c591001a03944161034581c4650f8015078003100e08080501807100760800030202c185031104a8550764000c441e00c01500700c0c05503100300903da02d1847c6004c2495a030501800c4241007452a500784010b100283c2d468281c8058810a0b101012030b0151803020308032588001c48030700304d0b10082c0460400a4411040301c144a00c42c540d000e500040324 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 887281465 1250 887280215 887280271
    0x30e0906040c0221190306090c020a0c03080705101406041d0d03020c01020f030c070b010e0408030c0a0e041104091d070303050c011104031a130c2108040e 68
    0x3011550140400d048075614000d0104902c00581d0304600c000c2c4010305c110a9010307412114803a80d81da000c10200e02d8010442c0c110b41000c0c400c00110340144000d01c2c0862002480c0d1012244e000396071580c0c4042c280ac0240c2082c80301000310306214180882c0302e002c41c80c2d580010b03000e660f00721400c210030a0065040141801d011a02050300e4003e05010f840580c0240d000d0b040c09180c0743e0016152540400d49444254030450b58500b079210003003844010711144081c00e902420200100c9201410651114501170000601c012405040003c59035015482800000c01c86000508140f0122410001c4500c5680090259015080c0340c070b01c070141d1070280e00e44403080b4685100040e02c20107045407022a1250300440c1c0420080d03480b0b80c242009400740c4070080000314003c01386013030000d10551040038403900103461280189070780e8000300301048000c00351310f0459102c3c600c4080000f144080f0025140420348002d001600301107000105035184007d42d078032801030400403e154030104942c81c070340 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 887282715 1250 887281465 887281481
    0xe0a060905090c1e010e0405010b19030e07090209010e09010e06041107020f01111f090b010501030c090e09100203010e061206130308190e010e12040513050414030403030e090604 78
    0x4040304c012074200c96000030381d401102c40503043c9804550b8a1490002c2002c1e10002e82c0480300341d010000d40180101880501c0150f01d49485c601408070410070300c120741d921240780c014a0407a950000e100115a0700460403040ca0040143c585a629a136500750702651240880e40070303020304c0c03c125940050f000074404403100e1b00ea00034041050804490011504d225821107440030b030744211000342008902e5400c3c07114403203a92600201d100b42d441c0c5050501d041c01a4012414141428048400c0d00d4100721004151009400c07900010350381c4191680c038001c401c0c2e10f9003c0c0944000b0020480c103045001c004e10401007921100d40068140819682d910001c94800c180306201504c00f800007031003962400e40016010050110540c030100500741201e8503016407c0017a0b548a44080708002c05001822901480000c41ca04162800000c00e900380c000b80d402e01041075071080003404000d0340c500302d11001810300341140d40313650303d07860301400000040200c248180300c040006129407409000d2440 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 887283965 1250 887282715 887282719
    0x170601080d14030f1008030c010504050c09010b030406150924060e01140a022109013209040e19150204051011120d09030801091104060f03060e0a060905090c 69
    0xc51556100c4030713142c02410180406448605400f400500a4000c00180061980e4000009a54142403234880d161004036400f190040c00002c00400448944005071b95009401840c0401d2288a07481c0f012641059600103010b450b10702210302503084082507404842083c100c0240704c0840e01c0b5003094400d010200d104a00040b500b610300038815032050060310b400315080c0109c0300c1501841060082d40e11044180c5444910046442c070035a40c0e000f0705a0603003c3c0315680400d10354038010b2010789144182035030b24060a10008601e0b00d140c90b5980520780d440001170995003074008490300c003610104000c10503109402c06c46007080511040303100b1281180c070000c1c02200700300070704941918552401c0322104004d005d0850b0800c000d03101c2e10000d00088043d10380c00660b44180d440c018003441c40681290003480c8c0740c800e07001e00c0c445c0c20704211016500e25051030321a245a0070421000b034040c942090184e0402c40040c081009000c0c0c0000043c1c4e803090a083c07041d50f442e1401240d60f4100001015 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 887285215 1250 887283965 887283967
    0x314011b020f06150d35120703060315090201090312110f0303070e0913020d0506061003110a08060a0807090b1017160512090703060c0f0804080310170601080d14 71
    0x90020780400d1480b40c0d080d06030050b080c1c1d80201550022444440c06e03185500d028000a4650301011800c44010350044c0c107802d040120a0542e10380c881c18040e141316031422107640d1604107041d603005a50200045a2000c0030754942003403500000c0c40d08000488955051240540c2d80e0725182d000700559101358800c1d40d41541032680d030410000c0248e13001c2c204982c00704005600d500581c0780c03070a240d52060701a6000300100d0410800344000d09030300c141c2c1c1c0030170503242c40201c0f6507010400c2c1c2111501c3c1e5041c41c0c960b070b15031030b12400103064000e5a032150005200380354000580e16503035003041c56080400ca42c8070020744008002a566090022820302501c0c000c0700c0051448950140c1c19526513000c0e140c064200301240800d80c0300100b040d43d845085070b00040082003048007a005420307003580d084c0b070f1801001d00106d03009442500041c0006050310404800108401c1c4094500001071403041c8030103000c0d10302441283d807908407e0044010034050080c80032032a9005504031908003034820402 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 887286465 1250 887285215 887285239
    0xc01181a070e130e01090c1e18110c19020301060b041d090c06040602060103020f0105120f09010906050a0c080f0c09090c1b030406030513020a0314011b020f0615 71
    0x10720350200c04802103000d0380e04c40f480d29a07074909124103a0118410302010388654103240c44510b8a4031803030860507203206400d200f40540495800c5011100c0d41e80351001c5140158001100d406004020b80c89410b44244000c00d0000c2c1d10312400082803a000354000c0015a8550020060134403840c0201c8021104207445100c90348070405000d0b50006641054640380c54243c00050700381e0b40298014001644240014030540c540240620302d00300c002d0038034a142240c450514080820014050b410072100580000d000010a41080e01d50719400001000761780740c61078918006200f00300c003240c000358a410029040c031480c080542d000700b14a86080341040c03070300300820501600082c000002d01c401840090210700d070621051541095841c06940c4407410702d100181161001404520380740c60300500f000c0941c0724030805030b0940341c009020910380c0d451500b4280c05030800480000080400b40b00b0000354607804100c464801c1403000c2a0380b80c1c1d03240c01d1034002e030900f410342c815503000c404d440d00 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 887287715 1250 887286465 887286469
    0x611041208031803041715010815040512040e070f031424210f030a120207081306020d12200a0212180f01030c020601050f060c01181a070e 61
    0x2c0c40d802100710100c2d07003104a0744288107045420513440000d16040010000807180b04c103200d120341c0c01c8030008a90f40300c0e600d0103034415a40d00b04072805003005c04100b030100c2d040c0b200c1480060480c50180c0c50080e03070b0755640c072500c610450782118a100058a0b031030105c1a035622a019654071480c00f110010129207942034145100701c451001034841c0d000e41907200900751201c620f14140400a41c40031010010590303000c03801e0461404220006130410000f00c0c003010f802c8140380e51140f564540c01615801c49141140980c815099183d030940300400300001d99540c00a095881c585141d6a0984075034922030704541511104110700d00c800f42c5034011500e20901c0500505030800c0310f4812924071a10403243d641c000d500c1440e0104090440d03000620b118104150300c408404020702e0100314002074184004c0d2101e206008403032064005c10210308199880100b51a01c0100e282e0082050a60306120035200250030321040300e808407601030b040e10003030140b03d9852107074010352a80c100c0c1c0310407801 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 887288965 1250 887287715 887287717
    0x924080c120c07021e090402150d090b0702070e1b03100503100509010b01140f091908060108060f0717090c0a060309142e060e010b091206060d03051308011401030611041208 76
    0x400f9041c22700a00ca4400c130107459004e2001180d000d8901110542001200242003c1507078100d0294001c00b0001e10060b041e241c0440c10140390846c3d083d1b80c894440b04860509504168040c1c1d42c18403820300e480200c0611a889680281c1c030180c001c200b5011504010340e6260b5840700c15002d038500503c44580324894802c01454580320080a58080d45041200c02c06000d1240e000f500c49507010f1401880307010000c00034150000a1141803450518040b00e0061103d0303d4400c40d40100c01c140808110302034410011038038043c50061441c50403c0c1c480500034020050070b24255200603181e0001814140046135a080c5070190210845490409500c4103810860300e6541d01021503540d10001090746c0c40c2e0f094507020786000181160346980c00010001035030302114501038607400c042c05101060b52018079401c81590315042c06600d41c4814400c103c1035030702941c4581c1442d400c20f000301c80500c10075070700603060b20f02c0340034200700302c0d4181e42d5840f14a00480c01035203505800c0b002100c0c003042c8540 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 887290215 1250 887288965 887288989
    0x90203010209150a020d0507080307030b0a09110c10021603050310080109030e0102012316031e0504150905070306090807020a060f0924080c120c07021e090402 70
    0x2400161600d02d07180c0c0801c660400030b1043c03808244001c5001c140c480c1c1e0501a01d48002004d00c0d2083c100303a50368440d94100d01c409024101490740d5102000745a494402e011401030540220402000d100c140340b10310654048035400c013a60007004080050000385100b51a004607110340184417091032035500762041d40c03000c1d180c035071170006e034038000500003800340203d40c0800d100342d82c4c003104188540c001a096031b00c2d440c8401000760090702010400203041084950000c01d1404102c1044032030030056000703240c00b1104900300b209081d485a42d80e5455005103025074881d800c11b10400b005552600c04a0300c60ba48010881c0e004070394100007092190300303e440c0041c040c00006140c038102d030740007030418013103a840301c404200c1c41500b480c000b42e08800c1c4540109070700e00b03540b58250001000c10100015541c005000c0c84085804100e94407051400d513010203405070200302c0e00f070928210322400f98003c02001ca00c43c0110035903c0b4000d9a400b01100050000a880b900c0c0c01e03180e581c00c001c0d11030844 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 887291465 1250 887290215 887290219
    0x70b07050f040603020d0c030513080a0507060f0e0708030c0601060507031e03050f0c040609051306080d080907090c02100c050919050a06030908180d080d15090e0309040902 76
    0x1e02201d1420622203004000400c81d50b2001a512144455030105030340340b984a080a05282804000800c481d8000f88041c0700c0d80300e4100f0b03549405a20064402e40903c44014080c18904041ca40007402168004481240d604080380c207d141d40307261041d81e81c403880240b000103800003401009654018006098428401d00f406ca00300317003060700a019194480e0f4034000c00640c0700c0044c0b001204d02c00c03002913000016048000d203058103104d00031f00245014807419002c3c800c100301d528503004581d40300c0c0300506590360641d0f00da00d04808d8014040c2006a801088500480000142001c07484c41160f00f604596000382c82e810080020940043c9104180d580c1406020404011203643d0701907240901800000500c0c0c6140c2050f081c041d10740d2041d009042803618041240010610440940308807420b050010f00c2c00401c0c18002c10030320300304030400409940d80030603100d90f81ca0250b000402c90040c102407818045940d05000c40985410380c014660503041005564410306090b04821b40351400 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 887292715 1250 887291465 887291467
    0x1090608030723030d0c020303100f080c060315040615020105060306010e06060d0e0106080a05120a1b050304030f0f140c0109050d05010612050a020108011d0a0e21030603150c070b0705 81
    0x103811000046e5021380008030b0040c2c01c008100903054448000b0b407c06412083c8400c1c612904020341d09035a00a40a001c5d8401d80b0302100184c0310000c010303540e140542300680309101d0195a011f0b940c0500c606034107401e0141d420440051501e04000400300c1c100c0d008204c040c4119100c0f401031010b50b5022080da4440703507407250740010702d120003402101d000388404002403280036403604109007000401d03807402c0d21200b410005010642c3c2d100c0c045606880c3c4200002c0d419a8291501e6440d602c00c40d80020200754100209209001c095030700d600d40c030380c0520800b03450161145641501e400864410074049650001d043c00f49003080e42843c900300303100700c000185080d151190302691944014080782e550f484034400030119680649010700408400401c0c0c0180860304601c1e1100c0301c40108403c00950f80c0e03001c040d0f62800b00300003480541ca8400c1c0008000f5802403c90300d000d034000c40d10b5070f00034810242408405078800c040148074441c44200541007003050340d10310703d4001002d405c071170030010 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 887293965 1250 887292715 887292727
    0xf24030f0a050705011b050d1808121c0902011e030e16060306061b061835040506121305151005040506100f12140109060803072303 58
    0x208011592103140904000d0184520f080001400e13502d584014801c1d10101807800c06c006040085c066030203520608091540100881302007040f5451035110420f00d00c92102c0b49100761f049100102a0a02c54540c1c03201183d0b100e4405405072800c000340280003c0a40f45460715400500c140c2603285c03481031a0100b002143c0d50b16031403803e41c64103000c0700310b0401c00d14200001501445000b005105904211000c05205001860380c0002c0d00d502900f05602d51582580c04500003910001041c0d000180041c1283c070401120075803030700d114102c00d0410018040348480c0148409030381c11207200400782e51070300103da140030650890140c525151840340c0d03249200040e03424041001c0c0e52001440244e018034003650346007016407041c1c1c0141c0c00343d0f01d08028001c19854403011410007508908000d0090130001c50100c481414840c45040c0240c50b000d81c0000c00580e8a003858101c0394140d0003400000c0d1202d614540720301ca0b05500070502c110034000c006070340c08030790191000c0352541070940c2c5c1044 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 887295215 1250 887293965 887293993
    0x30c0c17131d0906010e040f030203120c0c120f0d020f0d360b04020105220602100608031224030105040c0503010c0c02060d0e16080a0203060f2403 65
    0x5050b00301e5205018615046030030034401c42105540100d268000300781340d51401c2d0032294503060260002c0d0190300012500030170f1500804c00c4615800841414510a280003218103007560484007036511207006800c0c1100c43c00711002c090b15111082507054518108401203408025071200080c40d1614400340030625072283d045c8100e401e5410024600f00340d00f5680e1010900301100c1031040c004031401882000041480b2003041135001ea420300b0003c0e074851a510100d501040c40301d2990741601c010a00c0420303c1d0343d001c50003550b102c50a0005105842c1c66070101500c90080241d0900304259000002e104c800c03001e00030308440c802d110007481295036420003182c00c4d98800c035002d849003ca1030000300802d0a0900c61071006815514040200203c20b03030029201d40b05401d041c1030f040703403186e80786119004140310107140315a801480300354079541c3d840607a40702d0418a000340d210303010380d0b4001485540b041d02e105104241503483c40f44201029141c130f105240308199210741622540241c14180 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 887296465 1250 887295215 887295247
    0xc030f0f0603020111010c020706030207050f070b1306110a0618050105010e1008010513060506282907120c060911040b0f030309041802100f090501030c0c17 69
    0x20100c000801c210782980005001c03454620641515070303141500304000503070302003040800e4520358500075a4451160400c10300c0c1080d140d40d0900780c0d0083c550001400e04a940041c1100d068075007a4144803603490303505580320902c2c8100c1c1d00840d08040c500f00001502c41d0301010503d0000003105440000e151561401c60f00244c0220001d8800282030200401580e41414010f0180f02c00074007191503c1c0094405800340020b005045503200c0003c50340a684981504110103281c09200d108041c54030000080c040d1184110385130564104001d092141c0400601d144091003003d84030300d401394580d030f000503007181074040104115024154200003401d40c00b446691034080e0491005220140c0208001c4903503a0040d94441c8a06d4a0039408d40d440c0441070301c8203114200d400103040100903100c0404034982c074100942c0510a83c50303080b03c1e0b17504218814040c83c2603030703510108561528019030480324500c0601c0c0119045140b4000001e004041d00003103650541e80b000e0800f03140342241041 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 887297715 1250 887296465 887296481
    0x1060e01080c0a0909030c0609080f070609060501050901060219051e0d0210021314030703021008040b07020a20040906020a11060609010b0a11010221180609100c030f 73
    0x1c15000303003490781003d160100700b4901078104214204018091554003502003002c4940080c8500d4940060317070240b241c104145d03080e15007182941d641c3c488040ca00000148030302c0900b03c2d407680c5050000315581c00e10f00585416180d0640003010b055008000402144d0202c0c0ca04844038407031507491100c190101c0780326074020703c40300e00101130a1180640190038804012070b48091507106000300905040d843d090032045800c41030001840f1545103011a00300324a030b07080607400141030110b00c1c40c92035000d0b000900c650f015a501c1003d45c0c032410300c100c0c0c80b02503080f80989134808a00103a04110820010314142003402000050408000d0780c641080e40c0041010070041042020b41415920b03090100c3c590040044800d028558180b07490340c01c00b8020400c40da07007000b1030600c2c040003140c0254102e960896141070f01d45060441e564a040702c1d520112031400b82080c101101d07a1080301d002410500a0502ca405099000c4200d0240e0000f4881c51003800f04050304c80001e040700c00b81d80e11403218 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 887298965 1250 887297715 887297729
    0x3050f0d061701230105060a020106080d0503010f120803042a0602011512120e0604090203151f0806120c120f330402010306080607020106080d030b18040501060e01 72
    0x3160400700400c05003140d40c1d0800c4c40006060305035034a1000c003130921001c0e05550048440070740351540e03c0341c12401451035401007003041c491059200061a04000514100c80101c61001c0b01941c484042120215842e900140071050138400318000940004126060740740e008214500c0e50321003100c010040c0c40682c01600942d42d2a5881e45c10000d118000e01c001d007400070310451045c0781c9640d070b048480c00d00e001c5a03000c112101062203025a00d1a00b25001020b00c58815901c03410080c04603401c101c500800948a06030441d921858154040107080c84c440c0251104450780d940e071000d202e00e034112040e00c2c4d00d05001e45000701140360354034080c880050722100c005040800d04a0030309441c04000303a1404004002c6040035500080d14418400c049400004402e444ad440758070058000e007506401480684c01070208025540d9815806141110010b0003110040d00c8140b809804035000c40854070f03040390105158500460303400e448117812511038000000c10030345c0c0d00405210b01341300781c0285c0303 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 887300215 1250 887298965 887298989
    0x607120309032a0f110603012c0c09220e0c0f012d0323040213020301050604030b041e0b01080f1b010e01110726060705040303050f0d06 60
    0x1006056020761984076085054080614003503003141c40c5420404411001000040b0001080d020001c110740301201c1c80401610302030303d95860b51004c0b41800100ca6000a02748212401c0d1040d0281030754903280150000905c29251882e0242800045500c00d24a08698044140c18801e140701d50310800400041e003034080c4c004e4a840d5000c10880c201140091410071080e03000111107440644010303d02d01380c03500360b0101c0d04800440180d000d414040031310368641c944a056800003031003101c1e01512861084034100da0307400d0342c00310f0102240002e0260a400c80c8042c0410700000d600d9252254101c1c0c040c041000710b21201000884280f1840e450440384610318038010410080100070f003112070700d1110045c1c154020782900c1a8000f0500c2d1070014104100c803640041310f64010452250804003043c1600c20391519150f001c4020740c1d001c0c96400c08560358400c44015a24041120390050599684651600d0b14540f02103030143c212a100405075007082114a40211041c49072800402c80702080b5 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 887301465 1250 887300215 887300231
    0x120216050409021216050a081b06031b0403031d0306190c090308041e08011803030c121d0c0d050303010e04030909020d09110301090c030201180330050c030f0906071203 74
    0x10002d00c0c44a58094805540005043c41c9d00c070a1081c400010104240c800e2510b075903d4404240c1e01c1c01d008407903a2510240024040b0a155116100d040c464050200355590305551b0702c28561b841c01300b11011201c940090800418072131064102920014441c035010780c05039140d0f2a02e88041c1d0065001d06007030b00700c0300c8100e10f6400a441070403004064800003001a052844034407440090203030001010907965400071140140603002c030804c40740d4100f6042028115854040640000c1e07100301864038400c0e42c0d0301045505e02802c00d882c0c86507001000d5130840e403920100903490300d0040c108405100c1c0c070070004030b00072280f840980309a816801020a2703001d400d01701003404540000d0014060790400c3c50b00008150303003000203404c90f40d0a20744007400a440020310b00c10401d1640000b40015000301510071710880b0080c43d54100d56558038030000004082c0d0003911240309100c41c800c01500148414400c0d2407096014120886c0f0141011b07181c5545940c0f035206480744034000d0b0020950b50707016 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 887302715 1250 887301465 887301469
    0x30c020c030f1b0d0f0605061302030a0f05150d0b0709170d18140904080918091009030801170a060507081e0601020c130b040504030c12021605040902121605 69
    0xd4003070201800c4c3c88448400c0c1c0c80740c0344c84e0300d0306030001e802909031503c03000070603296112a030700402c5078011480115202d040410201028119000c40c00303487e507041c040800c41c01d62031411000c1c0061001080c413550500c0c03558440c0d00d0504010f0044c424082d15100000c0c0d050340c10312101c200c01054a02910030480358a40c003074042c00101c0400380001450240600420658207240d080f60300c4221120120350b919032400001901c030780794029400c0001c91210420503240608940e000724017090641c0d014201e18280c0e1411195800006000544100010031010340c040d04121020304403042911201c840c591203200c10303913200350307030103800100d0000400150641e03000d10001d00c04d400403000b0010341000d4000030f40c1c66411109482c0710300c100010211141c6038550142031802c0e00540103102d0f41c500380c10050034195a048040d641c3c3c0c1c0703159001c04080d44c8045403000780302e1400d142c02c1400e142011300f40320081002c00e03006c0303801020100222914035003c100031510065440d1035489540d042100b = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 887303965 1250 887302715 887302753
    0x30d1d03030f0417070f06082806030c120206030f040c0b0724060605040b0a0306080d020607021209100503040f1a060114070209041e0f050c0406081c030c020c030f 72
    0x1c13100303c580c0189105100160728084c03e10206c2e10549005e145580740c503016a8161071450841821000d81085a83c0d00d01c00c0075017101c41120f01800324215401e503038556103d140c58182100039807000041002440c0c403070740044420b40043c020902090340a468400500d0a039100b40411740c0e12004052184107043c0b44002100000e5006800030b00c0701510340f0740050050700440c000c500700c14101280030740c03005100e070b845000200081412a03941c0b4082100107074480340241d03504801806211034000e0140c01039070480e04054005000e1030021004040c00700c52076080a0411165a02c1024a41020900741e614200170a4060561000503040c908000342100c14111000041e10710107000302005a661841113036402a0044081d003034503040f01c0c203000e00d0745000500080260700c0c201c64120074401d0018034442c040b0b8055030100541d039124640280d407282d5101013101c907040e100300780d003001d540300340c201d030301410707500e0044071400c5180720002410104003d15510955200707144581101d29512 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 887305215 1250 887303965 887303999
    0x70b0f220605042d080a0311040f0f1719030c12111009050316050106120507031a06030a02130608010e150c040503030a0309030e041d06070509030d1d03030f04 70
    0x4a110f4a10020a000314001500c4c0400b0704180c00224140c10b4250281c0c04c5464442401c0c01250b40d1a9120010b007000c401050140c2c044540c41c404010424005603103000070003800d00340082440b4007a0004440040c80e10003404c4040111385590440040da0b442c80c40c0d1402c100130344540031500914040c483c40c0101003040c00e1901402c1c01c00000110f1000300846108218006801080d0211810304034003401c0c0641c80745800e141c03d2968441440b00200782c01d426644611404c0c0004d4000d032504c240600c0094036410380c15003011241400510382840180054041080041811a500c0c40540e0840d03848071040886904248200e21402ca41d00560f90b0340300307040030901420b150400c07001c00d0740e078020030280105040e51010a2001e0601452490b444040020024000340d1100e00c5003102083c1c0700c078603000040c0b08100c0812580fa0044007a24060540079004000001540c8000c6a450308800702c46500b2489050781c2083c50746081c00104019289000b566030746900d810718205410b0110 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 887306465 1250 887305215 887305253
    0xe060a15090b06070b1801150b030105010503130b010909140706090b0a0309060630020f01230301060e090106030605030d0c061b0306060f0203070b0f22060504 70
    0xc0080465020011a84400d03111500800150041c41c0c00105150b4401d103140603003181294010401d034010716032142c034507000d0003100a1003024141100c07214211070a009070701c02d40b0420300051000e5441840619400041d6510b51860b0340959150f0001c1c1103400c0c2c121014007a1240801400d010003c007680079013105420092800d1441c100c4001c1c2103207014040d544e8203c2c1e001070403012007407281e00001c05454001c4000c1100e55074484441e44210011201c01e0a4601c44080c0e10301641d4212071440c00c2c0c06e0700546042d09142203d001112a444204074580b20840d24080c640980409040914081d10450b00c890314004608801c00140c0d41050780000700309070808009101c00d403070100f860f507003019060620318a900a01c1c54603c001c1e01c200c80341304004048600300300c5040350345900000100c800903210b04d8204151707090202d171039100c0d203040a0604480d6801048908140d1a144c40e885407202404014a4104403c0d403242d800320900c00341d030f40a865500b404280885c814038405110301c9 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 887307715 1250 887306465 887306471
    0xb091c05031f0819230a1a2e030f050c2b02090403030f050f0406050c04080714030c03071206060b0c1e1207050304090509120f18060d0e060a 62
    0x82c203c0107507594807410189202050020844104100001d804583c0400c50540f4452503034865444c1c0655800c001c1740c003607958010746001d50f580d01c40c006000b40c0c047c4107030342c2c182d800010514000256004605201c5100c4160108002000c184403941c202d80c003e2003000681600c015030010401202030703007000d002c80d001035001080c0c941000d055612280c0da505481c049072a50350303800c080d4020000b0500e0606403500b0301e401c0151103580103c2c011301c110b126050401240c0c640c980c01c0341182c081d030b000300002944802c41c04d120b218415800000c0003a13000707040700c130100c08400100b810304c10303660704c0030f81d109089188120400c4102d003d4000030f0210904c40e18203020170408455034420b413421005c4009445580e0070440e0700018008480d03038441144000f83d0301c03c0c540c40d00c02d0342caa2140c1f10740040700707103080c0120317080ca00003060407030381a100703441614200840040e141206511074910083c0b000b9215a000e04642c03201005460720803040e5900041e21000c8042d201d05141c0000d2103010650302e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 887308965 1250 887307715 887307719
    0x20106060203073c0b07020304120b060d05010c020304080d080709180b21010b1c0210030b0d0804061707080109090602040504020c0d09150c0b091c05031f 68
    0x35000081d9403480740c00c000c1c20140c0c0200100000d2100c02100a19181c195900c1035246045584c0c0104400c034521402c40c90083c0c0c0d5450b50100c0c1c07280180e0103010710940c070403440040415001c0c82d0041d08800001d044007084180c50782c602e401c40c0c10301707190a405600045420801d40744103119804940000b800c01c030915103441040108000c8043c0140254000c94040312440c0318110b901084040e81c01421b075075840f4032544140c51000f8000000386035198240b4070f480c961818011540d051444030403088411003c01c1c5e0b0708000a0440640d01c503001c0681c1c61441c030949540c0c01c101840c6040c060f04181d0790b5241403550040441c0f0065021255009000060104031944080c066044503122072000404810b20701e4020045c1c031895008a6109001050014003404040f0f4090412506a16801215940c40707201100c42046102800041a04800103102040460300d02560084640c0c080c4d90030540311540d104490032030745c1c00110010f1004404c100b00d58403040a5020130000130160013901038 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 887310215 1250 887308965 887308967
    0x90501030c0b1801030e010902120c130218090613111902010506030a032604140106051008042d0605011e03150c020a0b0103060f060b09180903190302030109050702010606 75
    0x2500f641929410156185003d005500c000e5010f000701c26401000361048000c42059103561300b80151001d0701c80d280b900110003048189100710341e920f498124201d0407518840007000001c9500034015070708000b41c8402420a84031030700c02d01010100c0e070646242c4a02d246914444008404046c41007560315040500c002075800141202c03646505192218400940b036011450048890792101103120b8140c00380410404005e10100c001c1500c0e100030080706940710308002d00c44191000d4800411800b00116004c40d204040b14841d52040c0340558607007025440764545060018407056a07144d550b1001800148142e034031030004107001c103030b4940c00c40c1c0c00c2d92103507660002074881c0111020340d501054500030340203002140b6040e82000c3c0201c06503a49003014400380c040018020ba6051400ea401b081010950301681e1151001a01200e0101200f40c4600c0950310081c000142d00e200511201003440003103c069244603009980158880d490006600140c1c7c0d0302034015400e5905042c02803042c1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 887311465 1250 887310215 887310247
    0x180509061306060b0c0f0c06270a12030302090f091e09071e0e010b120a09030e131d0d050f0d0618230105030c0f03010e0304090501030c0b 61
    0x4010489030301c0c0c0c0302949240802c010207480d030001d03021010108a0800c0c1e408049104003c1006850a584030100310f4010021140709084401d80090062041c80a00d0700500c50741e03450540e03001d40220003082c2c8542d620354000c80440c1c03085000036000a40b5005a04040071811000c01040e1180c0c0c06904000c980a42c03440c2200b0030180460341288000360f21201b042111500a1200d4070514602502550b0580601140b5004800c44106a00000207071251500103c07030741e402e1500c0c0880b4043d1141a4044082c0c40b02a03000e500700030001580704041d6a620700c080d0304c0e01110102c001611001c00c0406844030517581442206070b0402c808080809400804445107102100d15030345d0340f04a080c02300b0740140342d01d820502c80740380640141c2d900803e4907400301e002c0855000358540d4400444e1503402159030240222901a00301d003040c15441e051140c0a880d01007002800450140c9064044030320f190415440307030404039210307030041040c012a10100009003d095540e981ba06180440c54074407 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 887312715 1250 887311465 887311471
    0x818100906140717090306070207060c081c1d011413061d03040b0a030b09100b0a02010b150301030c1a07230a05070f060c0201020c043318050906 64
    0x42c071004258014012078004121200e00740e00c0000901070b8101000620000e81001405900034840c07000841c504030700010b1684210340341513403107c0e40c00886903034646c642e810070710300c0442c0140460281e0007006e010b030203203a12400c00045004200135030501c0a03400d4494244101c1000c100396414090300783c005c0c505100b07919402c05000725081e8603000108201141c003880307203c01804042008038145440800800103032515075010f1206003400010400591800d41300410013200e110020824fd544a0000e0945071800c0c0c000000c0c3c0100100101d601d070700b07522111708002c440000c01441044a42810040070f0b1543c0003007440008041584001507106581d0041d03c1320034824400c405507040f414160624009841c1501c254088a24090356070740c2c0306000300c4003e10400b02010070031380c0c846d055440e14250140d006005034003e51085c0300007403281510700400900c0c9035800131010005983d081c100034019400c1c0341080380c5000846c01d0a03844039038a8407104ca040c00140312094000250307441e0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 887313965 1250 887312715 887312717
    0x504050a09020c1c181a09130605030a06091208040803010e2208030708071e1b080f0304060f18320a03020c041b0c0305040e040818100906 61
    0xc3e854619500c050b20300010b0601c0c00030600314845511030129401083c559651051021000d2400d880304071180d041007040c0c00c00400804180181006460b0900c403140c2d00788041400003d5040e16076020a0906001c101c0548240761959029400c210b0074443d0b41c270940d010ba00d00a00385003841ea072007046a00c8188661030b50480b004010a01d0390540703001c19420703400c10304c032844803502044c46d24100c580c0003207034490086035205001072030301406050b14524800040b490034042c8100c84405981001100c0e91100e0700c82080201200042c1200000341000011345117407944902d85440c181d02941c9680b5108000d1a00301800c500310044801004006143e0000360022880ca2440004d00c9045280406014018007808059540e800100324401d40358084d1317007542c0b40000060144001d4804950144202c81151419006400d101e89400c1c82d09900c45d01d010f92070300307540f01f902100d014400d6600f52003440780000c1c00c1e10950b69155a1b040c3c20b003000d0312070040c4d505c040c21024020117001c0c0300d018 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 887315215 1250 887313965 887313967
    0x809031206060a121401180c020613170310030c12020d0f051f02040602010c0203030c0a0f09030c06170a0b22061a0705060c040f120606080d0f0207060504050a0902 72
    0x30000301e01401d0079079110108448100074402007449917200c4e1030300a12480303442c0a210031525603c103c0d0790050002002e1141c000708503030348072403900e2140540aa00151034101c480a5141c25414400c001140108200307600014000d055050002032045681c2c000c110000b015a04903005171155111401400e400c109100d614002c80d04200d410a003880c54003607041c150b55444483c0c113002d16400780058030302d01d5008102c40c10a569080e82d03280310907a07000e48806010f0100444080c4900e40c4841201c1031890b0102c012a13a0b561404010922a040003011030440c0b00020302801e2510b5600b9808502c0d0903061204e1701c68000442c40d240e0192448000b075410045030080031407a1500310000402c0c0f1004080c2206400050000031a0420041183c0c24040c16022a1114a209041e00c01350344c03c0d11280c0b4102490000120002103007240e0071034a8a444090020b030080082c0129215141107480d00001c14004c544000c0c100350682d0084402e0000c28442408161180c1e2140c409640c01d82d0401 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 887316465 1250 887315215 887315227
    0x18020a0311070507080d091202090a140a06061407020d0b09070f030b04051e1b010314130309050118170f2509020405060d0b0d060e0706080903120606 66
    0x4a000c1c1124041200c0480c0c000101c150810100045140841d0070740b800341c030304003603070b041080759808058481c849204944c02101c1026280c442407058108001e0200040d00342180b030b40100748110211181075000340c0c0c401082100680004600011101c40400c0f01d00d401c10b9507001400380c0100510240000d800140000c02001c020800708024210508420642560b203103081c1407021004c42e0204c07118010504041d4079000c010303040c0040506a03201800ca441c2c51070701c910800100902e8440d04254a4501e048040d0000c040c50b18010341c2d071181d407440c0c074240030308020307188400690080341044440c11640b0070200890713070403000383ca01c0107020744c05d00c0c840b4505441c82c0001c6d00101c0007a6015812401c55443d0720300360b4603e949602c8003010544903076070b071400f0300890046125168001d40b0412411011a40369030007215401c5000744035140d100002d483c0da00c201c801450803480c00368800582070040b01d800810b06640b0100c2c0c01c006600d400101207140f0070014028010b02e02548001ca28 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 887317715 1250 887316465 887316467
    0x5060117040c0515070317010326090a0308040e060f0f01030e070b0c01050106270e1e0711150402150c10020f0414030d0e22050a0b030c090118020a 65
    0xb5180080100400030001c21441075140403260b84042c40840110f940b85d035076001d8038004848614104c1780c0007001c81c40540f10300b48003244c0041d12548038101c0309030100702030074641d40c60120610140d0f0081300750b192224140b400211001c07502900c4c0e07a110b0194403e980c0300e207a881400800111000f0303c1c020901fa14200980c91a11150b071b0403080c864640400e004100840562241c1e04a840c2e50340c45824100051000c17403d41c0410210349941840c03104428031601050002c101e03088a45002c4c2002104407440c20b485088100b5039118001594075146924410300411980038521030076013040c952420b00c3c1cad000605084080425900c0c40d500410514420b902c10700000c01d0801c1d220b9001d554a02e60b022040c441a8854010380e490810b15a80b040114100000c00c100319603156260300c07407000c00013005c000b03c0d4070394842c441140c011a09813002d00010340e4000d10f401181c2e0598042816280301c0708040c180070907082c8481c00f902100c03004101c0d44048402c98907a010303c00300016651002004 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 887318965 1250 887317715 887317733
    0xa1404120c05030c031e0c0703060b0111150a0501140d0b06010c12110d1e030b060d090c0e0a0c1205220302060624091c12081501030506011704 63
    0xd000b030300001c103541c2500da6010004142c1c00360030980131a1158040440c0e020389019440d600c0005a000c01018000922141d00c400c011480506058a8158a07090440c0c6400201c51000095810360824000f1301c0c0414003910340503010001d0050104036031200407404040307060b200034012641c1380f008919144d00a03038a00100030782119440518100d4814060aa02410500803149200701049103810074407a480d0700020784100400d800d800400c110f4120094924461b131140d03c4241080540003180301c3e407041c01c0c0914890004c1c400840e02c1c2000745461400010095136966007009a400c0b82983e025025100c00070020034000381540362540b503030b82035403006030003480d085030039031305103010300d5000901d80f8071541c81181c80f030402500c0a0488554800344407400044c480040c40861140c0c5005101410342c903180300d110040464503500c60420000c0d000b824140400c500209000b02c1401c865000e0500c10f03800e0038280042e052130f00c0000c18494092036054004440a8089030030494200 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 887320215 1250 887318965 887318987
    0xb0f100c1103030f0f1c15210c050d020310020c07180c0504060c0c09090308091603020306160201090b070e030d05070803040b0c07021f111506101e050d050a140412 72
    0x2d06c00c01ca48a01c0301255600d15566001c0d030070b0f410242c8041c030440203071208a40303001d40368001a00e036141850300301442082e034801302d4103d80c54042c2901005c0300c84041d101030f0074608420b00042c50810700e4008280f805150f80d100d1501518104260f075581c80d5040421502260901e16086a04031003609003501407410070780228100c0b9003040340003001d065002c074100380204015025a483c041c9803000f01c0500021030701c0f000350983c10900c0081d040812058103000d0100d41c0f0700000c1080011699074040b100300407030305a0b022170145180030640741030030841d45401c281c190500904d4030202d621181c2d05070200400041c49150640000354900020009440115602a102c1004418140140d0700032450002c003140010741201c080d03c50340000091850400100501b801505407501405e101c010030400b9030801c180986140c08200c040076002d0300d0b03210350b6041c0e80c5907500c801c0300007610000c2d94805007030a0243c1e41068050101000c414005d650020b500000720036039080d469505031540c40d044 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 887321465 1250 887320215 887320267
    0x8090a06060f03020109060e0f01030f0e07092c150c0c0105090a0311071a0a0c0c0b040303020d08010e0619180f0b031207060b0f100c1103030f0f 64
    0x3141c400030391050702188000a9a01c02d880d004805c40c3c581400300c685a1080d407540303600569065441219500940c008844520049404141c40e5070120907189080e219520207030706d048d910390380082000507150b503c10340e0725400444400b003c4a0b0a4007103039690504a6403001211414000c03800c000c0e54541181c0a4070904c42c024070280c6002d0f40490f44034488079038180e000c0346541050070a01c510100d00442515481030b40f41c0e1004c0e00d03403150001c0940044c040c0e0030500ca002520040840d8107444214001c204844141e9076503429440e009081c0148200c1c20024080e02d4801440f2a02d06280019407012060f00e81d0707924104000d114480c031a165a101c501405c04002e801c10411a281d00502541c0741e000c2000d0200c00e01120a060b0764525681404680420034070083c4009200c1d50041154444002d250500d0000720400180911244c1c804000201d145889440c0411100c001e0000c0d050b40300b140650305101c80b10071901207520078400700c01140c032800600d018400240070350801d860031207 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 887322715 1250 887321465 887321471
    0x6041a0405090114040e1f020d020903070e01061403040c03240e030c0c0312040501080c04051c03110a02090a15080609030903060a0b011205130210020715021c08090a06 74
    0x740c2c0c1a910381304030b490760340d043c022410000c0c0100076070b10004241c012030084480001d940302c16503140200a40121025a0107507400304001c903110f0b80e04200b4100a448450300c050b000c1d516104016003041d0948440c1c2400c00c8003030040102207806ca202010803680c00c80d0445800c11084429400d0b2070300880a0b030742101c0e20348500d80540d500c0c000040c04c80d034040c00c802c0304c5154000303400305542c0d0031222a40341c80c0300008000900c42d40d4407400206030806407601109042548400008246000806104600c0c0d80c22070549021b060717000c40d19a82c846813074400f42213030640741d801040010b0001440b600090340c6a0810310042c110542112008244c24410354403c0d007003150229440307a0004886c3d0340700c0c1c818a40481c10200061040c01c41254058642592980074118420050080208080d500380340c042c40000c00360b00c84502048495680d5400b6014003420840b101c589849102c9842d800c650080400c0c0c10b5008164800c00b101d6071050411890559400c681c240c0390004001004111a003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 887323965 1250 887322715 887322719
    0x904170a0912082205101b12030c0e040204150318050303090c0a12121b0b010b030405011103070206010302040b0a03050307061d0d1b050a0f15060b0c030d110d060f18020906041a04050901 82
    0x645648080e0b03d030416642c4d84076680780042f0402c016030046005901a0f00c400c00103101029010758417140e210008200c1503c00c3e00d40c1a2681811900200c2d000c0050740c01c0101070a8082c43c1110044002c0c000c042412420786c802611823460384e0081003114414404000c00c07a05c10b92801065603a6910b40c410030036021907031501005405078005a604550715820105001c0289007a64103591103840c1c3d5500402c2e40ea07107113400704005428400e01c1e40c4e800c41031680001c130201e07800b80010325103e4005c0601150101e01d90103800011003071800840c235244c01c01d519182d10142d000034440e1000c131a40c41d101c010364501c0e04045050120f03082004144404101079141008580041220b005001d02e0003082040c0c0d0359000311070588241c1c00c180320150002c0181003540341c825801041c0c60f83e80848191b0401c644410350300c1c11641d0940203109240400300c400c011519003401d540c0e5449100d04025428808050b020a003580a580141c401d601e01c0f25500d0080310405105440081c040104150f4043d6 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 887325215 1250 887323965 887323967
    0xa2315120a02040e0a122102030a0209030d2c1305010e040618031407050f06070c11240a030219090905060904170a0912082205101b12 59
    0x34070408000c03070160b030502400c2030703e00c1c0000c1406198160010400c0803000702d02d131403c4400070301072011041030000d49080f0f28008036640c409103200c1c01d44074400581d1000750204142c9000f04006007613007000508458140050007030184c5040c203142400600203503515200c005080c12025a044900044c03074800001003143c03a07050194016405081c040100d010503042e02800540195400340200e01c00145145169103000028814180281c00759484050068580780c24044282c4140380000c02e209155018441401f68800d0b5040048071189144803000d80166090807200c50440080d07100843e4001085000741c049030100c0442c02451045500e8107600503240b440180210b4482c43e150a000840600302220070501580c0c10101c3e04141c001d00c00c40b50501c03070f4026002e410401070380a000083c881000c2002400407440b411b01e0540f0707448180c151400080c8500c40c01003413040428400c000c81c1c0c0b940c0384a180f11920601d0860301e200e10440d032440070045035004c020301d20072804260086007 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 887326465 1250 887325215 887325223
    0x10020606190602071503020c150105030f0c10050906070506190c031a0f0111101b02060103030c0f1703130203010e0325030c05070602070504050a231512 67
    0x8820484040001840704040c0040040d801d000d280c02580c441107003442400380c2504a003000070340718940945400a0410500e0800440c000011460002070b00180881d1030184150704600c060300000b031108052890006a4003200180d501d424000b00141501c81070b2941000c40d021140c120f0111f6485007082000c10344107541c1681003241e0302d444c200300b00320841e109014004040c140003c0140b0380902c10b01c00c00c4030400c14190302c01d040c0102c0c0414441c25517424480140c40111408000941141140042d150fa0021002440440d04000014800a90000c100000035034110104411181041c070b4910407002443c1d52800340c10201104000c803407140e6802c2d044245200781c0080c0107140410403200c0c0e1b240a0240b60b0b40050940c40c154982e07142801c014210303481e011b454a202c8682e403540751242072040c15006a401030300142e0061003181064083c0a1b08031085543c100a03070741e1000c0c2c07481480442c26a81580003008030300480c024590301207200051060040031556842c290725205603071 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 887327715 1250 887326465 887326471
    0x1b0f020a1a031b04050102030703030f0f06030f1b0503030f0c010f020c0c030f01050112020402070507031e0c0f06080406020a12021308100204031101120e01090609030806040504050309130209100206 87
    0xb983c0c00c1c62401d9a03c1c1c01c40b5005507012a901078004500f4090f01e41d90a0700a800d00c0305035003070802d9680d2040c200005190003100008d5020310b85001c1d0004043c00e00100c0c964418030020744105448008101d56100041180c412103170341d00c400e03070315040e0204240380500303501c3c0489680140085112400c040b004140346500c18003c804540c03141d9451031000d42a41d0003445444d40b80c41c080820740000d410b094006011091040c000d540c4401c2c0c4035910490160102103901c201c0c00c10300914603040015648241000e44011a2210f40052a205005100780c80050008205a4010402400e483e000700b05c0b0300c1c98074a041000355111010803c0703141098034584500342c024860b0180000c4007c00c80d10031101625040b40c845050780c0c00700300040d40d8000c41a02041c01059940070700c400c82030400e01c02c13413070b1080c89044042001d800c20300b002018000090300d01d9206500d01410301c0b0000c0c0b0000304540d4149402e40d0940130040b0744404000c000c0c0100043c0c1e80d00b000340903482601c4150301003440da00c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 887328965 1250 887327715 887327731
    0x14011b020d030b03060a020903150a09020a120803060d112d010e0d03030b030709050a091703060906010e0d05070b0c06010807030f020d060204051008090d1b0f020a1a03 74
    0x1040c41c60004102c040e941410100b5805820080201e841000c640c0c00402da500000303000c0310380300c1c410340f0b086902c5010100c4080d1021640e03140c803c821131501054250040c55190701c61799004100da05c9030300d0b00c1d200240005100e2180d00003080d04210003200390110380c0d100101a59204183d07400c40da10318a0700b40c42500c240d8105000524a45c0d800707116900103042016100c160304211030b540179030041220f4450303c0c1d8144a40c07400001d2101c25409101c1c4648104180800c0f008940c1c64850030100145e20320541280c024010010161610b0228076400102442c2c6240c68000e0240462207015484601030541e0007081808030359a803a0340010105121050111445680e0341c1d450b290300c0c2c000b04c0c00010301c11582116076001515001048542490099200528265650780000c0109035160110808034085100300003509809214402c0c0c1500c8a0408240040084400c481d2031350101d900146040c1030384900d9003e549075444064081c1600c2c1d2091040d07000d9a2007280c10a0b0000c49080c4 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 887330215 1250 887328965 887328973
    0x18030821010611060a0c051605030d0c3b04020a09140f010f030e03090a08010f140603030a12020903010e1c0512010e0a1b0f1701030206040b0714011b02 67
    0x205148998401c880043c0208043c2000d5100d00104a019200c0460114100b0906011502141d412080c0301d02a50744254015030b960f42d001b454100540d4103420084083c4000700d4190401c03500c0030f01c00558100740102c41030b43c00d202005001c4601703008084005030400e1001c10b0303d4240340d0304030f45d07020180c9041842c0400d0072606c80003000000320100080c1400640c01803200040d441c0031b80c2203213800c250034070203490074418480c002c00c4800840f80d101c44510380d101c0b40c070010008000c0c0700f0318040c005d001c141c49105113085d00c007181d900d218054202c820000e08280d00c0c0c24010255069a2010350024024400c1300d91480160f40e8070f51000f118101418528590a689680140d0407242d9011034044038001c0e6a10b01100085000001441010b0f019103e201c1d0140d1500350800074a0604459252100d030100b9104000b01081e0741041d04040345a04103005001503560703182a10308844001880654401a910348100c003082c000110415642c28100314880358540d2540c0b951030080c2540c202c03 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 887331465 1250 887330215 887330219
    0x90807080a050309091527090f0c22090c0314010c39060e0f0111030c0a050c010c030b0f061e09120f1c0c0809011803082101 55
    0xc0c9445141c035040c010115441088601c0960074000401076003e114144980d000140800115411a02042070302898070ba5101051810001e03a42400f80c1115042c001019a008640e44150b074407210000f5461241000070703440c90f00d038000000202d071030040c00802401a4422840e003142c03c5416030008507000c0038800c600010000c014410000f200031a40d44920342458044e0960041030340c03244d88000101c9078106044204880307180109622849040c0009505012202c45420311444541d940c0340381e41080704c03c1109442c8041641d4000895810b40b0395103075901101903036540f00e00c0010421950800605440803038041d8403200410a00780d420b50b02c407204117820032049100e4054240c43c800807081c441110584180050940e044014011000f4070701046d0034689090f0011410790800da004204003220021404262080401a410441954001e90b500c1500d07501500750701390304000720300494001484100c00780900550304150317800c1d030710315403c04148104051112507a01c186120400 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 887332715 1250 887331465 887331479
    0x1806180b0601210f090506071b1115030403090801060b0a0903151b1d0d12200114090c060408100207110604180b190302090a0902181b0f0706020a0201110406090807 72
    0x89026a070272a0a01500d90365581d50381c080c1e05030700460382d40380c00c024654070a485d070421940045000701d0007602d40d40f01c00351400b42282e081d55900e82182201c00c0042c41003404868000034000300341d070780c404403006800b11002c4001004006060782103040c451010903001116400c1215450307000010550341116100761002d10403c02c801c080c00505441900c080400504e11560100d142e502954080d20014540e05880301d003036030ba4414844503c81c2d14201403103a050300c10407008030152419030307815043c2440c0100054440202009400c40541c0004501c020040040104003038004000c0486850f20781769094616031600d0500c034115070a2030415541d0b4189022202200f6421041c0c6501d003403141541e007800340c41d0070b0107045182296180c0148134010703558149080002c050f0420b03108020329040010001e06080d41000d010030220801640340051081011034100300d812001c0035a8642038213000300e0040c00d8400c45c0385042000400c1c041141c9600c00426002c03204032100311050f01c0c4d11658 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 887333965 1250 887332715 887332727
    0x51611180f0c0a050702010c02133905220302090c091c080d18020405070203031e010e04022808060109060603021201090e101806180b0601210f09050607 67
    0x803e150110740c00b0b001003001980307d25182c9a100c1e1000d08030884240d04d0164038400e4480c2c0c0804030364619104003403c21115144903644d900010104500c80c0c540320356a001510a1142030070000c0001800d03215450003d80760790707040d0002c40d4040c0c000401031501880c0c1f0466600109555072061128104c2d041107480d00180307407e8030f150068030040c6000070803c0b00000406c46203118090411840c40c414000d40d0fa0780c8100c0c0c2c4115903c0d00036660320300e0030815500b10680c1384190443e400840c0401440b0304031401a03402c2d8001d40c103071903180d40d01011400140d400d135200c024002d00380c0d03051000494004c0b80406d1040c12208900341c24404151141819070507405100b03019200010008010003001906400243c904a840016184103640e0300c82d0403801d807280107168803004000d6450078000c21443c1d00c5101840c08180c150b4004424460380c46881e940320107820305041100c4041c641c210b001c4405940c032031944098130200030301d21000f00b00d00064207400b04140c82c0c0e40226400a0041d9000d40 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 887335215 1250 887333965 887333977
    0xf0f030f0115090611010902040222050105040e04121715090a14060d08040b16201e06041e030c08190f0c0504020301090905060109060501051611180f0c 67
    0xa1292500c03c0d0514000310745807000342d000029959280c036603002c0561106d10007440e1030001c901074034104410b441506040403140b03501550400100304801c110f03051011411b25005644003218810840c0303028802c480303604000841e02500e95540301440801020800d0403a9684020303206411280e032020740190807901442039080746901517400007049490722a448801b403610030300d9454149a01d5248800b480d40204404d80d2468050b1070301c09090080303906c0402c40fa400b414121040041d0749902003a00180c4805202421902240c038072140365440d14140c4010b03165010b5524200d940c0d6044002004489220a5a80340070310800480c80d0840441c42c400d8848440900c204d000b18075a9650200040095040d41c4c3e0b100309038800308069880340010750080446000105e065000340c2051401c10300103030300c100340c0a07103011400c01450f42c000c42503540b00c081d00e4501d20700451a42c03d041d280c050072840305550241304104401006041d40c06141c0c0950f600c40c990803059650b110700c0507040c0c422a = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 887336465 1250 887335215 887335217
    0x3080f1801031a190306020703020d0206091b010e041103100915380a031a010e03100905070302130207050601120c03020625140111070c0314030f0f030f0115 69
    0x102d12032002401c1160300c6201013132940c13001850300c50b07580d2203010480c2c01c05841140140c20010501202950411002e0f8100d180340f40a043c0350344a00c80911403041c0d840f5001414010303240b046d500b003503945501c05484ca8040442940d85ca24009201c0e506071007481c01030a802a241811100c03051507401040d82c00e40f43c880c01d1808048009804d03080c0c080990700c1d001d000b40f15020446019440703c20700980000c0f105620042440001c4040c05c18140c807a0380c1d025810000e881c405c41045c3d179000141040700031049030001810400340c2c100b55041c481180c1019412002d284003241d5504010350041180c107025100350313030960341c83c1c441800d002c07409000040c105502d107840078405403038800e0003041c2010414112000912240e0600408a03910341820369044a100301500c05140083c050b0310701030807101d500140303004d0b85951110313032003000b07808081c1840081205911400808008940a51020301e81071070311940d90500105003a44112401082c4405c3c05000007110403003041c0c00307144c142c02 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 887337715 1250 887336465 887336501
    0x30d0809060a05190e011d15151302030f15270a02160b040213020c070b0c070503070f050406090902090a090302070b070510050702161205030403080f180103 69
    0x100c01c8540c000e04009090000640d03035507040701205520a20030aa4200c0d414000420754080440307d8000c0d00c051000407201d66000340300c24a43c1d0b00d9181c100e86074441c6490003114040c45110011981c6842d01803482c4140c14400014484031103c2c42401e1f9100304034079542d145070580c4a0741481900b943c078800340015100700e400082c100000d190207065115208010060a103408150b000687c2d8242c0c00c17065411070456011700c420340c109500d4100c0e88800380d05e070540c134140e00041036540e00c10441c4140b44429802191448038000c040c0411300007408021304a44015844032588103043e8854845d540c40b0702d02d88030300085c205189004148442d5002010741e0295910040090050651410104c0c114080c40d240421840e840002030145d8502a00080c030b401541400e0030340440c1c030060803000a65100c141c45d80c809401c0259910296408600906413448062030450315601a5410041c49040c1c041151968440f140000d485040b4000c0345142e04820070702c00640444020202e482c0704000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 887338965 1250 887337715 887337721
    0x1106010501230304021804030507050f06070c11120f061e101418010810150509130816060b040b0a050a0b0a020316110324070e0103021c0b030d080906 66
    0x1241d401442d4050300142c034030b140111b400090703058005400c48080700401c1c40460503606103c000c0003011082d1201704001c02282c24509800ba040b880740d1500144461100c910488894a03041701d01411306909404984008040403081c3c4e03103900c0100d0705440750364481c542140c010481c2c01103481c0034001c120303403200d0303004e0500f0504008460600c0c140c1d500b041828408a40c0303113051044d003070f00901c0c0510140c20240c042a04843c282c0c1e02d5840c0780c01c50448100070900c06507072512801030308545c03002e105807118009071816040701e025100300d442640141701603d41c10b00c88260485034414034111020441b02d0074240030020009071038050300f6046031041d00b05014890303a01c0000e0401c00300d20f004480c1050311464a804420341d5802003101d4061044140104a090400800b510144810700401043c0c00c1c0701c929644c2a0001026401000012100c000040c2d0007641240c00120307200140d204060030000130440500907528206009100381c0d034030700d0071062148081ea40038200c054050030840d1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 887340215 1250 887338965 887339027
    0x1813090317240f120d0e030303010f050d0201120e0a1205130b09010e04090c030501110a27030b180709020f040b03090304051f0801090903020a03030c11030a1106010501 74
    0x2e0040515500925112042030103640c40900d2134084010003002410340b1159094001e140e541202c207014000d0340300f03000510400101c40000d900761071040e1407440c012039140c00105d4100c001d804146041d00c0c90080b1302246180b001c50b0107070100e800b9408005003804198400c95007446404c4c82400300402508091201c1816075006180c0348005143c04500c40050030300180840b21000011035a11000d8541041040828048d40020846105030503003800702140000e007207480f601001c4a601006841c2e00900501ba030403201d0041c540007006580350380340060081c582d189134031120b8141c61040903000103086140e0b000300c404007101c280304507040614000d20f2040641020f001c84800d80420304c070100f100d45504648031303002010020081050040d402d000303050f00e901a04020415400c00c3d5185000c45c0e0000f68425000340d02d40742c00141d90208120403100010a29810040e90000081030032846500c080092110a070340419102c00380d0ba11401500d03540d040c014043c8100741110035031002a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 887341465 1250 887340215 887340271
    0x7020a030809160f1a07020904080c1c0503100f0803040506130503011e0e07120b060d0b07020309040e0607080f0a090606120b100b09061813090317 65
    0x110b84603100301d40894002102200054866402c480c0041003000d0341080740020a02904813200070983c5140e1800741c254011170754590005002034440940002d40c1c407a07541c01000341040c0301840030f41900d40c10401100080c800c2c1e04c1614050021020400c000c59103016015001084620303102c011031400b8a8501030080c40d40007201080e0322003901c19400101781d10207002c0c0580017510542d40341002e112424000701101c1114141051a500a01701440f4100082801a05c019000490400c0a9036520006104079500e02001004100c2900c1445036181d000000380c03030b1910085038203108203621150416981d80040f9003100000300f04801164500c450a09215040300780c280000c101d42511740c540c41e00ba900301ea405080040395440d590300602c603110308110381044081d0070700700700c0d07510f001c20390750042c040d035a010b40c42402e0000700700c10070380020000e05100e002d01901c44102ca6400c000c1030340c01010805019004180780180c60315610724241c0c9210300c58400c0141003401520018860104 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 887342715 1250 887341465 887341471
    0x190b04060f09170c010f0f3015171b010305040f17031012120e1903200303070b010603052706060312090f0f06070c141807020a0308 58
    0x14482500c10201d007408030791184401502440d802032489110900005100c00100003d240070400c1100e40d00c100f0390780c040e2302440d60b003001550b001d80602800e001c000d840d50a4140d410002c0e03140070074071000d81c0705110956080f52140301108904100011009803510090101e9404918200d900028a58065400b16800c1400341155800d40302056413007c0c9201030400c4c20580c501008820009a101c1c050902405444400302418480c2600c0d510443c18000c210418014080352100408958031010080300030787c10445020f00119030389080549a01c40c48030301e04803044107a01c20540c0349080000c01c60f0005a4040081c05050780382c01c00490003400b0141c05000c4c5c07640310100c01003d4401c0a00030416900745c1001070007980c02c0c2103081520740b03070b04010512040c9100384181d545581d140034500109010a840003a45440d808002800d60310a101c00207080e0380d00c00c0c01c08501042c202c00c0718603490780240d4040f403511441c083c80901ca184210b480301d00590000d500c2c4400240304044440d0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 887343965 1250 887342715 887342717
    0x60907061814130b0a03061b0306150c05120f0c1612110d080c0d02071e093b06060f09010b07050a051b0a0905041a070909060b0306190b04060f 63
    0x8003d0f0320321000800c201c5185e4801e8030a1529001c80e2081c0500207008c0d00c400c542d85042c104043c5103420711079402d1000c4228804140660b0132342c0c407414020103000c0107110388896082c40390b665503d0010300301c13a50440051201c0b41d11910010342d01d0442007000e4103043d103454040000d801011559040c196202a400c0c0729040803c0190050008001f9000703029003000d410003406803102080350003450428954400d104d03400192109000b01c421070000b20040c1e6044040210700004c08410103aa036038800000c2800b581042155185625100078041c90f04072869400c3d41c400b6216074080084541029000c942d110601600403c180c0348031070b00601e107840c407401c26602d4041c1d03551181802c00c0c2800714001e11500020b00c40c0a400d01e045020b4034007809585a00304040d0400e07407600107100105c2203a040b01d0215583c00700382502d0141c0042d200030404a0018445503803541c101c904d1a81061703490314040c024070307041c0111160b4040d110b501950202c5103000d00300340c50824116030400513008148 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 887345215 1250 887343965 887343971
    0x2e06080f0307350712020a0206030601030b04060512030304120c020102031c0b0d322d0304091509090f081b010207050c010f180e07050c06090706181413 67
    0x241e942e51040b82d8a48000c0102e49480d07207138590760410285503020801400d003190004100840140e40d5103041c0c1e50030803000c0c0f8000038440182c0300460014040d50f040035a0040c0c4840036510b03964000001140f0851043e800c030f044d0710034a01001e0b100074402c80070007400b5070020304c000034143c82c1800c90b880450380c29a10100d001d0104c2e50100310b110600482c25900b420b50700802880082240c0405005002c41e400c0d049540715540c3d640540350a0100c4113a41200407070622356043d40c032010681d041101e5144d0649503907580d11000d24004081c42c22485050280c0c078200080c2801c9070317118801c5e40b150000c040c50320542c10b41d80c2d401c0455001244c1d1811131384035a4141d07141c1640c24405001c14034400c038010a10307d030b003242c00901020f02182620042000b404401161070168090100440351440c4e10139002d03886628040c0e130240540c449020241c031854040100b80307080050321108a0361151130b0102c450020f00301802d6006418026044001680c1d048000a13040c4144141e40440c0546000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 887346465 1250 887345215 887345273
    0x309050d060f0f0603061a0109050906031f0501060f051c0f15030501022710050304031b0b16021209060306030a05070303090311061602040e2e06080f0307 68
    0x150101e40380c205001c1c1440390346220170700c00c000091040500c03000c8409807805a618190740020b007008000e00905004000000c085001c4e5107080201207030401440c07500a820b409103030b01030390003450f00344100340009025170890080a07020340200c41030710450100c1841449003144e400d002506444413501d461980d14070703201d00c909014503101d4014610940015030341f000204400040d02040032950103008036568132a907229600c01c101c8580105041c00c1450304c80d5160300301611040641c22416011000899082041010781184544503500c003c01705229000322241c102c2e40d0315502d00341e807400d04104001e802228a000c0e0051a4450002011039800040d15601c0d01c2c2802e2456000310041029060144200403031140c0354000c004054421600f0b040002010002d03021411001a0040c0d580b1424586003017170078000c81c3c402c00e0380c0416448510584006411000310044c080b22466803500340003080031300000c2000754400101d080158249002502d490f6508800b0307168100342c2400c2e24241d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 887347715 1250 887346465 887346491
    0xc0402030705271c0615060c12170c030402011d090a09080d060b0a0f030b010806010f1106160318050d0e0d0b0106051e030601020d030f14040b04110d0309050d06 71
    0x101e0b299800074084e100030b10740e118a0070780305071030284210904418000405012603940035081880300b540240303090040c0e68090000780d81c02904090f854a5007408002040000790440e0300440c0618401c0c0d84a5098881400e030700040b000b5040e1340c0303030f0b40114000d000c60703081181b5801100d6014010350700349103000702c6140f01da000c0b1102d0354048041e41001048000056030440c0104500d10000d050512a688900b030008000106c028501030500c1207440e08144038510410701a0110301120007120b0260414201403405081622465000242400024809038003601050f1800340e500c80001d00f60b02c801102d0680b50440c00118964000381e2030f0100704040b40b2243d06541c001d001c0340c0c40c1c007503580303404c80b03161035281400c250442da98500400a1002c2a40d0020300001d4182c803500e400501082448511000341014005080e00e41e00c01105200910030b900c003501e8051807044282154a201c0c0c80e0501c91242806400a40440c501500811581c10300d40c14030750300207126803000a4003d8002ca0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 887348965 1250 887347715 887347729
    0xa020d0e07060e01090e0a02030a022205032802100e09010609050a06030903050d050603190b06041a03070b0304020307031707050105070527040b1804050c040203070527 74
    0x100000d580c40031204002080d0040001e0316499401c2c0781210750716042502c1d28040318000ba06155880d6400030020761703d074403954160b6401d0741100311240ca01074003001a62a03018810701505219000e5041c000d081040d00d000c0d018490950849805180c41d065020804a0200c4000300b07400d00101203c02102591507100c120701a1415031503100380380e42410103208080c0d41c141c03c41c3d170078103140001003008130f600001a01c40350158510040341a2f030310900420f00b000c44441305080c80d07000c0e840d030340f20401c00ca000e01c4602c900c2080d5420441040d03c10745184c00401245a201d801d40c000543c18019000103030000d41c1c0c00760024003124030080d030703e07554800b10380b030a0485601c0f601004607100041000c03e001c0e29404c09030606d00316050180400d1035419180d810480120b00640508d40d6405640355600600ca103003800421070043c45400400f90407030781c1401c8a08a44038051507004c01018070f0035100b640c0c000c02550380e6490030300f00500c00140281d0701115000005800d5042c4140c0c0030f40d0340309 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 887350215 1250 887348965 887348981
    0x303200c10180209010e040c1a0d050a020f0f03041106070807020111061b0c011118030f0106121e050d121512031404080706050415050915030a020d 65
    0x401800c40714a5030054108461a040c40700750000702d088200c8003da520000030030b0640d01e1030b100036110f0307448030300c0d000014802d154040703590801507035860b2409403001000381040c10f5007100240125610b070400902203100380e00031206500301c10701031034004940e0880596840746c07040c3d80032003400c007404001403425000203c044498102c001108030865900144007100702c80b0702c0000307003002e052a407400a244032003040b1029841e40b010540c00c1240e282500f050409548408081e03685903442d8801b0034102001c0c80c000c034041c1c450040e000d10303210014411441200e038501c60b9445420584d03959001081100d404081440c1d100807256008101c0510040c01003c0391501c4203000e40720200e0199040c3c0f000f291201c1054048200c08000e400c001c814011141541403038002c41c264215105c10b107941c002ca82003a42584600100070030407581110060013580d03c1c0c1152032114400072041140c5502c11181c0081d007210f4001900601010460302554020303804943c00b42c1000205000001212200303 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 887351465 1250 887350215 887350237
    0xf24050705030c0a030e04090c050919021305090c031b1b060a050703241a0c12130b1c0902130903030b0406090e0a031b0803090f16080a030320 63
    0xb0700c00f548109071b0801058074a40500780d505002e04156500d55107181b014500c200e5000d4018440040d00543c0d0b50043e4488900c0012401c5403244d1180c0f2402501c9a81030080ca4042d00400010807100e500c41010740c0d10804600d0680c422150340c001104419800564210104410f0031800d040d4400003400420311820403840009007510302907400800303448610700070f501c1c0d0141c01034521000d90714071f00f110f47c1510540c000c1078040080c8446010810310502c2a03400460042c0080c0c0080c2141580090103c282c125450340c0d080b98a81c0341c02c078103603c116030f803040c1600d07501040042140000c7e000300f00510b000410003022110030304507410a550100c0c008400090341d0b84480c4e039030b81c9412f1088a002d480f41c600100700c11030039880c0e400d40e9481c40d000f010b001c1c80300355007001c040c0ca0190300040322a6544040095283c2c140082081d41c0d40129021901d45800303442d1a0255000d008504401110042c070010221380b092920158010084055541c0c0584035880d60305c020014108000d103000161 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 887352715 1250 887351465 887351473
    0x70f080f0c01050a05180607081204150b1e01031103070c05101802060c0709020d020c01050f0c0f130f06110f06060d241103100f24050705030c 63
    0x31000141040000c504150611806008507400c01e5402010788415104c070350418496000f9040001d88507000c1c04c0d000501c01b0750000307100c0009400a50300396014a11825148400b06550750740314086d0382c40c2d0322030369070010354542d003844c0d9050101010545622040c14001540030008119083ca54802c6a4240109501c1c5442e8810040c00704918200c07400008010002035a004070110560000d101c0064401e10b404214284615802c0c010b807070082031000c034110340d40c2110030030368406508541240c24465207000001a1400003480c41d07030340b0418038a1002490034400031b8a134281074202c42d100c1c285901c180344001c070314001c1c880341d00809840c0c01c2e1540c2c4070440358140607600c0c003019141c90510940010041c13203185c1d180c101c15052105d07440071641c9a4503010248010509042c150790807000da00b002d001c4507d02008100942c000e2a400c105806900e0700d69103040a5401e080c801c16400000032814107106003c025010341001030607141c85460400c2686034179165410141c4140d2003500 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 887353965 1250 887352715 887352733
    0x3090209090c0a0b030c0a2706080708011d0103060518070b040305011b09050d020402090402220501050c060a1805070905070801050915100201062309010503120a0c0302070f08 77
    0x740143c3c42000404070300c0606451403070262110710450241110503428022a44040b1020f80e070b03440c0849814844120803079208568a08004040142c10349001c00890040c0d8000b01d00c5100d6000342c9050081d900c0c403a001b06918541d42c04004100003040382c0c3c00340d964442c1c010b600010512100b401044508820782e2110300314100386d400c4078041e001c2007825511b80026422103e401000d14012a6401c6030714209040944c000301e03001e80316882d45a64032510015030300e544000201100441c08824086054605442c1e0005441c01d01c00c020644095500c007400144148006400402c0d182403250f1404602c44c15580d1181d140c00c03031580000846903106c03410458150343c01000b490062400f2511442d6504041c541c5007008021400781c140241500d10440504074000d40100c8014208011032200c85d40204217901c0c81002c0020009108501813000040c480c500001c081100d1012403641c503203460440002030303960741030741e0508034150301a60000040300300500301d01d200104010000381810300c03 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 887355215 1250 887353965 887353969
    0x2040303200706020601030b040201030f060909030909020a02121b030708030403030f09030e01030f060b0313020103050f040c0b0d09050d081608010e1506070f050a12110c0405060103090209090c 85
    0x74902100c4895900a0000b00040b950009100341103a1700040044065115400101c0103002da4601d0310740d10500b8000e000414805541c0322580304c9020f59110f01e00740f52600c202070168880d81ea048001a400310507407401e411004002005100d04a642c001140701c1403a8015043d134005020980c0c150b1008003c10003030540501688420f00300c0e9034820441c480c1e01d0b40d8050140c61141c001581015aa112500125005541300c24007074100900107907140e02c1c1c040150f600b07019445104900007401d050201d10101250003034540959400840c04444a00749001c0740c0d51504028001800940c41c0c000ec04d0201d00c09004460b01510703c1c0e83c40054918203032245440024429a140040001d41c10040049040b0366581c950048101120342182494640005115014100c0042c1852031054403d100300200000c4c844007541c0b14603810800c0d0b64108c2d0003038403550002c4110340c0e5981c012400500240c50198001d40c1d10400505002901400580100300c1c4a4811a40e95140d9442240015454 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 887356465 1250 887355215 887355257
    0x10c020c0a08060c1e090301061716050901060e0a030f0c090b0609090403050a0c0506160f09150503190e010906110901020c040504050307081201090513021e01110102040303 76
    0x14103411001410f0500b420380d41c40c80b507489036503406203010031a9850301c03000d1003110382102e89120307008009002050700c81c000c1400c122400d46211f90309220304a51800103480b2803441d41c04070369006100740d11682c40c050041d6440502105ca4551018404901200060340710304150801030182c01000407050800700481d0854450510140c0b00341c07000d01c00801d042c0d64481d14907903c81e0381403900c01c0e110808104244c55080340c0703400c001c0860045c4401c01c40881e00c1801f0302c51400c40c07941d0381d604280618410030f4402d000c15025140b61358000ac060502014020390080d50405100780724040400105d00401e021a014100d6a8505946505200007840300d28001c484002035441405e5281100540010759074552146e4103501590711900058140501401950030711900a90100ea45148000208110181c24011420f40e02e15160104074240c91645020b000c003540a040c001c0044182d441640d514241c4d000b012b8100a0005040c2d00d8180b428006003000358808d0710f4154400b542e8245481c06 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 887357715 1250 887356465 887356469
    0xd0207050c060304050a0201030e01020c010204090e07060905013501090c0807020102090d0b090a0b132d031d040c0f1b020306041202010b041a01120624090305010c020c0a 75
    0xc02c000900511010aa010680c0f400040e42401c4c00222a0074800303496019018404286e211035101090018080c11181c01c4007003003001c2c0c101943d01507521103406948502d000d000301e44c0000c21050342c1c081c110200308000d40310385050180000310b500c95080c01c540070b003500743c101200c001e4460503c1541c298000d11100d40001c820700007541890101400318030841702d1000054081401d2343c0108030204010300008070100c0c1c01c108010002d291504084064418074882207034440c0600e43d1418040014010300b8005240610920154050b1914200c907620300300c0790803c0b0509601e1185030b1003996144203038060b0340c0d40b03501c9502d011185007074064040c4415510000030f50707170880d40a0300182d40200d10154015806100c0100380341004404a004101600905410902c0c000360030710420322035410b5a21000b002d0380c1e070f5401d00d100c403207505013500c04034441d0140c0f480180701d00b440003410203000b41101913054641454583c2e41c0c2c0c0c4400d401d4421617900741001d070300101d0800c041c81c2801d604c1200 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 887358965 1250 887357715 887357719
    0x3121e030605010522080106030f021912020d060b091810150e0718031a130f11030a06021210050102030a05040506092716090e150301020c030d0207050c 67
    0x8991454140043e03c079204000d04034116607420043d40010302185c3c0d0120f0050580d0340c0081140ca40c40b45800007a100c0b88100591284444081c1110004041884d88059038400c104120b01032100381e0900880e403030b81c80d03000c8071125110b44002130241c403504169849242c0490000003480c1c0c40c101c180d401c10540c0031031101d01c0b909201220300241c41160300d81c01101c001000f11039281c0e41d000742c1101c504003100b404010325080c1090000c00e00840b462101c0030540d0f00c0a00c28250340714004035865003994460b0003020755811498440114500510003030341850080c0c290340c1d1400003a2b50b404100d922400b5004100c00c00340b010300400082c58651000501000c1c0002c0d843c028060b4070140c200d0080c0d00c28a4030481c0c00182608e600e40b43c5062407920000101e414180e4441c0010b8034402a600444523110000302d513540a001007480780c204802154584064042c06485181201ca032603a0302c4003c0c95003542d020485040b00c140100018282c03007460002c0141c8502044c50305a0510300d9602e5800c0c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 887360215 1250 887358965 887358971
    0x70815060405060307020325032606150910031a0a0f1e0b0c1522080c12070b070e030d050d0c0201060b0c071d010323030403121e03 58
    0x4800e8844100320307801d6036822102d00740c903a41c80030401c920394800c0400c1d07030780300c1c0045404030600243e24103001c4140038803030380b00c05845840521602c2070030040c4e01c2c1c40844000059001c640c0c03906000710741d1019403043c0242c10707107800710364000300300ca100443c0030140010344e5641c0c154054214410482c009042c0885001d1440340c50b00000d0040b002a80c0640e414244000c03e07600490502144044014604903000644803500a80d4070b41e2900104941c9000c0e101040000443d00d602c000107004000f039917a01c141d1149160740e143e6480030b401c0b4155100716403081c00950300d010301284003d8051103105c0c9070201c1443c03038500001040346249414150180e40300c124103015164202080c0d60480886072000148800300c9603089002d40215848400088000507960000100100c0c4c010141c40300303801c2045500c03240401103101c06209100241c030b50100d4510000c0726010700380b03641b400031025000b12803c068803034949004030585440321a011507606810311400c40340740811440c403440c84d401d0030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 887361465 1250 887360215 887360251
    0x80705070510050c010501080a110108071b1a0603010e190807080d0c12110d0908070b090d030c2a031716030507020f1c02150c0301170613081e120708 66
    0x10030000c170552b410036040c000e921000a183d01d00c84c4000c816010012144048400f12038180b520306600392490b44140b10403003e0002e84142414040c103401e03602c0b810000e00c060326000300c0220f80b886512b40203c2d0820383c20400b003030110380a040501441c103490400001c4130083d4142c00f402034901c03015018038150401c020b1041e00052101596240100203401294000c40c9107013200d95031141300c00040c0320420b001d00b44007040b48002650220803101d9102040307000426101a9040c0d1403982400d0740600b489641d00e50341186003915041d800e80300b428174502c0b001c140c0304c849a42c21300c11500014682d580f407142c01c0c0c030580d15020b9160000c60394006040111065000181c54209400401c0460303004a07411050140c401c10800c1000030410700240d105050050000c61140d2084c0b14a0904032001c100480c0446000318005025034101c94040c4c455050554170300c0b90700e800880708600c841c0c0c0c4e48103600352101c0310b0760010305001414402d580c480d8904030b0406000c85001030b08500000344000e501c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 887362715 1250 887361465 887361473
    0x14010f03080702061305030f060604380d0c0801050403021b0f09222301060f06080705070b010305150108030414010302181513140607080705070510050c010501080a 72
    0x220b607081601a5002030307035124103007607540f00e450007036025a03050310446000d00091240450400e0044500319024002d015908041a0008603101c9088441c1083c4101320402003600b800324142da1400509000303130000b159241c11009914680c4040e400307945401c108000c156052011204440400803002c1c0e800c0c2d040c0e00412520014882c41074000c80b410b101040800e00515840000210340c010801000c1009280001901c500a43c0340021070b00c140c0d07010340c41c030314040c00785005a52003401d0041500d4074001d402c031400341c0302901ca4400c0c420100119004602e40e00f40e80d90186000d10010405071005000c60b6014480581c020b002c207420a1100703010b0b40d112141504584682440c0260b01ca4040c0c3d003902d84084241501c5540c040c0e54079145d540039850340006030602a040400450046654820f02000300110920072a0311020411100c0d000a08040242c08001d02450888a402d51a14003240c000300b48402120701042d0b0110700d20320044024041c02d03000d0140c0401421010361aa51 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 887363965 1250 887362715 887362717
    0x3010602190c051002012c01060815040f0f1505190606080604021b0d0c050f03090109050d0f060e0303011505040e1b1303061505030c2107050901080114010f0308 71
    0x8940c441c0352000c2d000c0c80080d200b50845821805103840d5080c880b1801d02031f0040044503090900c41c503501b02030000070034071004240c0c56004803204128071000d0b6107a07540c4076181d81148904640f88442021300c0400308503104482c44880c0840d460008540c1480407003251035031042c0380e0320450542800030502401d94444000342c0c0001c0190b40150312100d0701e0075481c00c1c961b500e0321550300d03501c90b43c0c02180c56280d20440503d044e0303011f18152a4201d01005030540c036441402440b03804210a89420403680c1040c42680380440d00480740600c014a282d56088250b80c4080107900f5260300220044c80400c1c14048401043d9465044c268506403400822468603400100004035842c15002d507184601e00d40001c42c0c441c05038421424500135201e2400b2401071201c08070740031204990700408110b0f400d000800703412076a001003518200700d081c90010602e4032008007000c543c50150500015030341c0c4441e08500c0c0079140d100008102c1d01041030003400a01130590000c1c405289112040001c500c0080c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 887365215 1250 887363965 887363969
    0x1090c05040b330403150c142502152a0109200103022b1407022104080a2102010b011e05070f031e020106051c060b06030c03010602190c 60
    0x107007181100a5402c5810071405181d001806c002411082207040d0702c840c1c0e00c50181044a501d07403c14090f01d00e0130904150090283c0306900c01c044c04070b2000d844039100035030340140d48001d000038103250241c503c215491700000c07003a40c1140f02c51500090011010085a0242005c8100801161145880d40c05029034a0304400d02c500000114400c501d074400e40440360b0595041c00c00441100381e110301c110240d10304042e81210303549020754aa103143e21039144c1602910a070360013040009002c4a21100b80c403424150340c0f56580b401c04c40051031440a00511200318054007048100ca905040700d8080c00a000b000c0790116450411200080d0fa0403c07031401c01d007110280002c0000b014200292524443e1010203010318001c60320f10803c041c3e01003080c07406003162491f03803d401589003000303038242d9945001d810b500903024002301da44a460080404140380c040c030000f00d42e88850350041411540151070640b60800c2c00401842401d404000c22100d804107a41c05207100da2b040e85410758194514 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 887366465 1250 887365215 887365279
    0x1503070501081302060c070e010b0405010e1009030501050c0408010e031e0d140a0203090d020a020109050f0604170604021906020304050402180a06050408100603020d12020f01090c05040b 82
    0x70401058505180c180408a46507016103211b035960040c144031507540b4600c0c8a0200070f10400800490140c0800f0243c404544068440c49032115401c0104a5520303000041d1204101c42c103140040130480134050360b4001d80c80424010b6441c0c3c00d00120b030342034924504401000e54002c000024080003103030515006622000b03482d58840d4145000207001e080d00105a1341102c90410034032000e05034507170045d030203118031000720f8405588170001079840d0144040041e0100c0c8141200b00f0841c01c12085100040000400b007510340b035141e1985481c4200320649000c5c45a04c4001000b0850900c00440c90102c2c1628403414945413070202d0007507a078480d43c09800d000d2600480d20505990744081003d0340c032400102800041070319111f004055401922601b000c0d4451040c21001b6049e02e8402d00d810f881d000380100200e80800d460b08000c820200c03000c4011031050301410920700c1c0b420300c5815001c600c03030302100c1610347c640001c002c16070b401d042105101d1040c1445001860495001e00c82c240300d59 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 887367715 1250 887366465 887366477
    0x605191e09050f03270108102705100504060e1003020d0804080d0816090602072607030f02040c030c02030d0504020a0510030207060501140102210f0f121503070501 72
    0xc207240c11820702201d414401e41a20011511183c1032003005d400c000084030244da0620484c0c01000112103481d01a2404420b030005901c0500141d600210b244071214640e20001044144100381031044400c01c41e041c09144460800501091a00c0e0150a0081414070b00300301c03a42c2052001044148094400284560100d04105080100c030800365402010b0760800d4800051201801922004c0100e45c0040c600381609179000c24140503040c003005071607641d8000c0c0002400e104071b601f65041c502060354680e49039000412141001000540003461041c1040800d5100c2d13481800150790403e000403092500f80801c0b60382160303000041e180502002800890700d0340b102d0002c00c0d98052242c00030b41d0070101200300d10440641540007003031214414030041140307a0343c03441444448018a80f5180c01078004620a242c240703040c12a02003803281004185d890410310702c502040e9035200120f50aa070000114144591000e0518001d51085c0fa04542c4c0303075000072900009884400e070380513007814031030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 887368965 1250 887367715 887367731
    0x409060b070512070215040b0910030e1f0204031209060210020304033e01090c05040e030a0f020118140f15010b070309050d2f030d050906070204090605191e 69
    0x25a2405d003d519040244506c1d582c1c5494084075012984008103a90107012140788100c0128481d1060f1890003280e003018000038142e2a40c280d040071a5070f20b4010b40b26400380b20100c007203406000c01882c01d200d5600d07101e07401483d184000e0700741b1411b49030003807490348180300308008aa0804142051505242640b070410070210706140b5210031202569450601d00000c840204901580000b00303242c01208010301c129a2401004140d44120342803074070940090100d9000c8030b010f41e48000c0d540e80b03140004620558881120801e090690b030058600b000c40c84c1e0141000b12051010449588219014107450052081e5600c0050010301c112042c1510008109041c1882002c1c00005080020901c40007403840d030800d034ac0c516061143c002c0102c0c8000700c0110f02c50981c9a40c0102c0d09002802605041c00d40c1501501e450700f0240406d0b411050401050005036a280b02d00500e1a10440c000a402d040144098074039401007040058401d2070981c0b00151401002007201d144c3c1528440031403800 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 887370215 1250 887368965 887368969
    0x4081608030f040b031f0e0709050d08090103020f0c2407031a010f0504081002090315010819110325050307030218150901080109120c0803060d030e060406050409060b0705120702 78
    0x6e1740c80c0354845580140c5c100c00b15229413016051805030010395908610240c8943c104510380030341d00001800c1e201c04001c0021a0750298003d4400140146041424000c079485407a007409421a0504900000500d070450340b001102e4615802000b0b6150400c10504d400c1005144003410b40d010383d060054010034045140d100340c0896001e4458501074801e80c800c8140c42030085d41020b007803503129009400340c120740c3c0c4150b10300c0b0604a5440307d005052110701d200646004082005c402c1d109884466890a100d0b1420005901c1c200301840e80000342a15440c0000e00c00240350304241d110790400002040540d58000001c54a00c440290410303d07034a500d0000b8080c42c20500202d600b1014142c000202968190b2000c0e00150154103221050b80d10110212421401c413a0700038404041400400c660342403d140c0ca0400c14860709000d203e075258100040c01541107a44990001800001d060003c0c0c5454002c0d1001070605014440c280002503450507250b9040070b0742e500c0540c0c0301090b048155 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 887371465 1250 887370215 887370241
    0x30a0b060619050304060b040203060d060506060f221502070501081e07090f090519051504020c0a020111032a0c04110301050120071a070804081608030f040b03 70
    0x400303014030b4800c0c58070380508009800350300202c40c19210b11b0700e40800d0300704078103090003140e1081000034246000845243c0c0d52000502e005041c41d03820250901520340505001c00c01408480d0300124010044a00e150000c084428507400c00c0400321030241020380c02d142c00081c40c0f41964000d0038448030b5503480c00d2200c0034000d841082a22000608814846840e0708a1000d00944442e880685141502c1e04074900a5070015a10410134a1719000c1c0b400000380c070303940620780000c1500728440c02c0300039081c0000c0c16078202c14560740c80d42d000031445804668001500369104035a0001960408420020000342c0c0228100030702d00d98110b2038020b2505590034809040003060081007000107503943c2054000c10b800c04d025aa001ca02ca040707079441112060000407861501c0340c001072000d581805d000b510300c6030300d03c3e9507106030b1030062050400040000d800340000d032213080024003c0800c007140700e0700c20400c25800340015410401285a0740400b10007110151500302444942d2515454001d40c06c6c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 887372715 1250 887371465 887371477
    0x409060b0a0b040303110304140607290a0b0103051501030c090b0d0c030c080424020418020d05070c050c09060111010903021605012c0a0302030a060e010c030209030a0b0606 76
    0x100480d800c1010482c0c01101010f4401e44c2d00903030f100400101420841a900d120714050b901e400c03154042d6103080d07440c0c00002080228401c00d218900d24481c1400941e640780521044150902d134641000a0185540300f020440e80c02403070140907070305180741918800111541c0c110304140e1103035002a001801030004000910040201c01c2e5144040011803004001c1e001c0c4400c00241005010b42d50b42d445454118001c580005040d080141c506001c41020542003141e11080c580a01000642100382550004c8200d1101009669038030090944002c43d00000c24180c248500464840302081d800200070280358000e5903103241035180c207001070300d8521642554104d95824090039a04040c1d01264851501c144003a000045e039071035800542d8000300400010f0501c102a050000307080201c040100b44809001d401d403d5615100e80109040031340a00040d207005403100120034014000b441030030001c0000e891f085080c01e10090010741c9034000610082c09684e410004101607a442c8012640 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 887373965 1250 887372715 887372719
    0x201140d14040803060324270106080a14071a0310050418061103014217010b0414060a020f0607020c010e030a170a0507020913140d05090409060b 64
    0x9081d14003031514a603d68400c0715151b02034011491105c1b4a0403102c900d5079a07987d102d076450f403103a50703a601051705003201c0c46210301140c4161260756103442100303200d02c0c405802d854015144151090404080a4080c004901e1107580303c6a8104601500c06103608088924908040d64a03140e0508080c941c041303a401460b40a0310309a0210340000449030354580d841c2c8030f00018854000c5c038101000007408240b03d0720001c040320400030203001d0219550001c5001c82a80c0c0342e489801c1c0c4011a00304d02c0f5100a03144007043c00811b84641e01060900c0050044c0600c001151810f03061007401c1c0a03034050949014061240031a1285030680240940e6404080307000480d040f915040000035030301c4c2d41c90300c0c103035012500c00c55214440c7d00b0003142414036a6000742103800041109080801c45a008101d0a0100002441350300016a107143d1071600844c00221092403178030490501030400510071814111b59400080342900c0e144e040030a88681c1c00e42250002041c280b40c0c20003201405e0340400c256 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 887375215 1250 887373965 887374001
    0xf190606031a0108300a020f030f030f15030304090e0312040c050a1409070c020303120a0b01090909030e0105130b040806040b07170f10170607030c0c0201140d 70
    0x26026071071140500e070480d800c44c4122141d2080d107072680c1c2984c0300c5986603907400d84041741918440324100e50080c250344130b0780d1040b030b0944c48442c0d003150f0464226004c5820341c006d0000034400e800444140c2240c00101180c0e00c08030003112500003079924402d034400e0113041c42d20fa0000e1070171048140180d4454107402c402c3d05a03c0e2070310741341c410710225541c01101c0c410000e084011810805022141555040161070081301c0c2d111072a060f9420514058100d9261004006401c05220900d003104d0082c2c445180100e00080d0081c000342c4100e100d501b00340ea0061400c507140000ca41d0100c121701d000d400c282402543e4840b800304070502614160400c104044c1c0c0064002211800020810321482c083c000c4c500c40703034694100459200e13858100c6040707103018440100c1c0118180201098000e00d00f81010f0103002c0c0e885180903a802880720f01aa417542104003000704294250017040010b040d6841e043d21514031035800a068806050b00d00d03007030404d02242c20000080241c0c06101d41241c1c0c0303283d070 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 887376465 1250 887375215 887375243
    0x3110109050a051b061b070b0a0c02010e0108070f141e030109060f0e07050a030b0918070f08070e271b18070305040f0c14030f0f19060603 61
    0x10300d580c0c4101c0b520448480c8105201c5020601c0b0390940c10506400c0101420b00d0548010030003150302005600300007190003440c03c0015136401c190000d01c00c007601c50712400074081c078500002d080d9441043c0301905000c00c0c5010800b403681d100052012101650901c050700c040d0f1011083d0003070142050105100e81c5640d162842552107601450480e155500b081c484641c541c00d9401c060030951103811926028440840c03003c42c082c00142c420f0b41518503001680d820307050001181d9200c26525010481c00d06c4210042c0702e901409440042c000c2c00700481c1015240240080d55480184503280301c9035074010203e1208280d00d03410f18043c804007808402105440f58146031a030000503a135204502c1d0010710040a8141000c0c00380c04509000081c1b40556240c100690213030100a004651045003559440e0026240300010809482500052404806264203042c0b4005100c0c030703501c0444c2d00039600b00c09040400644d0161410700c5c3c14550004029900d0708802900a98200800c0790707003000d5503 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 887377715 1250 887376465 887376473
    0x60f0e041e120507050c0402041406390d020d0828090501051f050604090507031805030915070c03110109031527030c141501090b0901051c0f03110109 66
    0x4d01001405102500d1406450204001c12031082d0b200d144000c9890180740d00782498103a010300801c045002c0702801c04050b004d00d018101e100c540441103001009081044180030801c40e00030080c00c1d600062040c81140400500715034402441500c41c07006403825444441000d6040c482c8c070b200c68a0303040c000c130080c600c1c011f8040d1000712000b1041280b042e074821409445008403400700c0360080c15983c0f4050030b14500e100030b400014075a0f000d02d601c8203c3c4c4104520440080000c440c0075a0295403110302c5c4a0410003141c0100c050319a140d08144811700200701100c2098048070341c4054040c048204903401a2035005043c0e0000e84240007424459a400000340c00021100d41441400c00070300300740c00d030308c9400311070f90520160000e0fa00c5000d20000401e01d00c003090001000c0d2741283d554407107000c920f15000310240c008101064036400000803e041200f443c2c3c5c00f43c101100d8101e07a0400d803883d10310301d50142606c050024403400e81080d0900d4001d05601c5240261480248036590346810 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 887378965 1250 887377715 887377717
    0x40602040602010b0a060c1b051009060311071e1704060c030807110d18170703020406150f1d0405010b0a080c190507141f060f0e041e1205 61
    0x86007502650a00303482038080d141c070078852402d98905440c1c40e0202d14154407203030766900098803e5502c05409030804030303095459035480127516800d0f586180140e818400c0013400d4074203c03000041c00c560103110314000107074218010030701000f5500258004451a0500717050a0b01003424614250400080106445a00120f0f1015103030081d11148101e454020f0100da000c5a40422500682c0101e00400714032845840d07010041d060040004c0e20507a00c8902c505490504488420480e0740722000410450400703002d480018540215060f414040000018003108110085c7c00c0c2042402c03c2152071648006400b44a41072015008110030340c1c5550f113180440d400180c0920104201000003940c04001104465485a000c0300795030380c0c4c2c4070b10744055846402c11300044801d40601e003240c20101d01c00300181c0110140300c44001208103d1308044034100e401030781140c0158400c1080c01d00ca1403100070750f1039400c603501825211545050440c00e205c1c00300c6018005101400c07a10741c5062440d8440 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 887380215 1250 887378965 887378969
    0x50310050a030b250c0b1b0c0f0c10140f12070818010b0f010c020a030b0f061903230102070c081b03011e0e07090905010609050a0203190e100504060204 67
    0x215001d201e0903408584c1e1840b00d10441d84010003d000c0c014500c001aa03203200c00c5401409400e02010310310803078100010150020310000440358454400c2c203406180070010011401d40607103412404d403000501c0100110544000c0501c140e10004540120280a00465005c02c1d400350582025050104d0001d10b03c0b0000c0e0740d040d0000c1480c0b504080007900c1885060044140205200300360001800151100c03648002d040e030380650307003840001c0898040c174583d500c42c00c1400e990601038540942000108641c0040c11402d03030349000f81c14800100000c0140401c40c4601016075880000043d1130b6029100d007080090155109400010300e110000441c0c11424100441080e500720b080030900d0b08035107a40c800300c0d000140c401c1d10360340305008030360003800c0a15030202944c2045488050348030540e003194a0885040c0c0d950301c1c003044410745500c03d80342c2085042401394950308150742111280e4a41c50300c02d810142c0e4030308007142c16040070425080c0b000070b040024400d618180c20404000e4000d4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 887381465 1250 887380215 887380231
    0x70c030c0608061210110909130218100603050a06050d0b06010e03030705120f0c151006030b030606010e040f0f1418031902120d02030a06060311040501050310050a030b 74
    0x20700464103a107801c1110444c00c07840b85004000785a40000000d0290074901680305021030100301c080d0258860740d0482e88507000203441000c402815105000911000000c81c6540901c0701d000d11082c0300c4080307424811182230b8070b00850303552517442160f001042c80b070380701030382c01600c06400504029007154400d20401c026200c220324138414405268480c80303403240c000c01c40d030046200309a18608040c081c20301c0301d0450303045500700b09c00c5501162a200040001d1203409004008000080a8084034140901000c0c0780601c80000d207500031a07910a00580300a06202c584e10740350205444541c00b1680b03a08185e80706120840e0703c1080c61005040750042d048100d1250800580c1c40c90061004440c03644c65a0011813803e0312001052141d04407084d4800b00314004c6040c03407c1e541c61404046c284807030007900f0069490402d80c0f010400c80786c5652010041c54240481c20104100001c141c3e42125000e0031316540c0c07560b0303924540b2480700d03d64228951047e4105c101000b8448420301582c4642c2e84 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 887382715 1250 887381465 887381477
    0xe0723030c030705030c0d320609030909400512090a061407020303070b16020a03090909060e01110703090803070b04080702010e120309030c06121803070c030c06 71
    0x510000c2c107860300024001e41c0c1d059400000e91921360b0610031402040300740900c40701002c0d080300c2a12802c0c030411a000c034100d48080c180074182c507080e00f0b01007660081429401540340c0f200500100e40d003c20000c05040014006040c0e15004011150410b90680f9141e030302d00b52148000d60018210180a207400d075030b503204070f90b06100c161000e01d0880c2c0e034166009119500391440c0200455510801600c140030050003480000300680f0100050b0080600c941214486450007200c0610140740d14214402150300022000000c00c0e0444400019102c6080000c20032408030b00303024001d0b00c080c98030480298605024101284110340281400368403075611181c456994000955072030045071805004421418042400612014020408070f032040c100b51842006803800912180c41001d110850b98000150402c2140744c18014220660000c41e1214108000715242c4060201c009080403081c410600003a500a0020410750702c06942c065110080b160f1a4035140c0c401560714880c41c004100 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 887383965 1250 887382715 887382733
    0x1e01060f0f05070804050d030207090f0518160b031519050a17030d0c090e13050706050a050d0509070f08010c090909030f0f030b040f09050709140a0e072303 69
    0x2104408a80f21a50003010780f6040a0800f004c1002d00b240c4c1c0034045040d44510300c800a200351450140b001c07000b0640e0800240b0b440e0007041151301c140345803400219600b04540201c2d00d149218100410b450020114030340702e9407030b140e060740c402441d24141079000ea8240142c0d0440d20865000f84142da405441e103548041d0754040c0400032250446002002d60403c2c00000e288035204c0e402094040c03075a04d0510300440d5558000c0004e030b082030350120014007003020b1490501c042000088001d010358509146001d0722031f08014028003584004021031910340022800221041240782c011f005000c4aa210700b07a0781c1c22041d8001c0180559900100750301a10005a10440344160100c154050300d491002da01091021030b03d80300c1100d6401d05041e5074114441894440f840b942c1030000325501c0005a090690820600d441e281340d00402402e0301f40800c0141d0303413854100a90300541c20401c0801c441c99420815408c09405400070360344000e2040d0407052815501c440342e43d01c004242e0980d03900700 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 887385215 1250 887383965 887383967
    0x609022d1503011a030406020712030c02010b15040308090d0c060c03030c1d0402030a0f020a030603060f330803070c0510320d0c0207030b07030603020a0e1e01060f0f 73
    0x40024410302203407803d03418003004c0f00c1c040040110741c001d10400b001480d0107480e03076034103401d5245030f007514000982d60030508207403680912442c00800790032140c0c040580d440b413041040d0303442540001809680040b9040c007040e1503514a070f0803071341e5010080401507502c0f54001412074108900503000282024030940f40d15028070030010a4003054641c9006491070316060201941c4003034100810190754170881c845224003403015045803c0d40d5078001c907803640743d0f003000b80598511a00000c4410700c1c000a80b80c85010180c4a5207024022050b14007560b52244041d13000112240d102980c6404001010010010703030703510340703025148202c2d00300d00c0da90070901c800c42c9e4800e281c036042607044244440141c000c0e068412a02214020507a00910f0001d800c0c2072a17094030020444034015900001051081003010ba200691040d150f01c1e0030403810f4a140c00048242d030251290f900d9440724000400c4821050408409221048250b6032a45595502000301107017a940c0708000000c180f01d1080c0002 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 887386465 1250 887385215 887385217
    0x20102030709120f03031d12090109060e0303030114060d0f0921020d3c0f05030705090616021c020907050a09031415090f0c1c0609022d15 61
    0x3181c0000555007241340c10342d0700b54028680382c1c1c10031010f540c629403000d50f05601008403004912000780c00c0c80c0c5805003a03002400c444041c1d00701505022a1401c2c5080a48000040c0ca0440c0d65004c14901c000d2501400b084040c459061420324041c140801928000c00c0b9400600c16a8441d5050710305900d640d495003544407414011040042c0c0007030100c0d05000307119504000445100a01001700060040140c900c0b00040801090f54a0f1607802d09140c0c1c26003141d0301d00141d03400c44c1802d03481c0d450001c0004185104401c580c40c032606010904401451041150a241a6000d000792a404a0034055640c0305110300b03200302d118075600750020b04018414019280e8100303482d10303034001c154115512180d5241043e41801c1507880b0b40b00d82d030036441c026000064001c801da10040c203042c1071003110042c1850800c60905004a180c00a2900441b4105280e01c00c0c682d0080c50009074850700b440000c0b0006030080301e600700c088003407611214807a90003400c0202050110703a04031114003141a55411 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 887387715 1250 887386465 887386499
    0x70609081911030f010b04060e070c0b0403141b01062c190c0807090608061513050301110a17010b030f0705090303030a05040b0f161101060b0406020102030709 70
    0x141d0002444090580a0240e82003003042c40344421101071107140700402d182204c0328440c500c80780c4d19040b000c0b200341018071070a0054012880c00d1380d60313482c255034098040b03466800000c240044000004090600c182080007510000b050344a0340c0f50802d51014503121080300560006520305000010002d0104001d0b81c2e00c90f103908031640d4111400c4680d40c01c05c00e00180301d03291840f1551180d204c4951680302c2d0b590160491b844141d180c1c01c1a07070f00200a900203402910030320407004184459981c41480c2c0514103504809965512124540400d1498600340c0c000758041d828041c180c210401404040d0145c50a00e03524000c0c46000400c19050300b0f0006e1040d880003002c1007000c00c00c1d00c84440501c5601c00071030f05249140030030300b502091640e80b04449070507034250f80f00107020403c40d070078104940107000c0c40b01208550030803017661806520141309080901200546009081d0070a4010500a0034040c0a85490700e0740c840001e400f030343c0212400000100d6500700030514070340030004206 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 887388965 1250 887387715 887387729
    0x703230c0f0601210524010314010501180902030a021002010507030b012a0203150f040209090c012c041406091023040f05090d08151806011106010b0705070609 70
    0x21385100701000d80810500c0e01d07056515001d03090403121a0160300c0301c046803855540c9181642503165003030070f440005070034100301d0460f4140401007001030420038852000404d222400500c60040e1b1000074a0240340282c02034002a900c011102c1868040d0300c003503c50005a107003030092041400045030841401d0307601c0e00f1080d4205480e00010f1940c12810346600f403000d000c0340d00c8d11803540c04013141032200b10760302c0100d501c8100800c01181001600c01c3d80220070400180028598a40041c051903e0034500c410085da04ca440c25a000a46c54a604100d05001d4803c2052803640e82101c2c103040c0c001c90b401405100c90001082c985000f0303050b0842140c8002d0704545400070000000c0c0c2d1b10390501e43c15142d100d91209000d200d92212881413901031a0031200420404490000181200d10028221400031403094000c04658441c0540e1030b01d42500043c25444a68500006a5441c0e44d50f01184546200d90030011a0600c0c00100030301030903018074200c0b4912a80c4210403a1000c0d07003801040 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 887390215 1250 887388965 887388989
    0x40201080121150228030f0b130f06180509070605030408190509060f09090f0c0a08091203011e05030d090504050403030b0402160b0903070809060703230c0f0601 71
    0x103000b0840f000e000c2d1000382c0d8007030005841c3c142c501e480c9406200c0c00740d250101503910b6081c0b01c4041c6806114030130300542c03083c1080c440180c40c0b000040c1c06a44c145459103455486000080c10500254000405808000011b6003a001254500001050b0844010403030744520720300030410b02c0c001c80a4034030840e401001d40e880c3c0300345581e8004040c8455083d003c180807051000d00982e0341c1d1a0701600700c2203c40600c407600c0b41c441c1030800c074072044040c2c2000300c03040b142c405201c48100940d0441c2e80030320180c104528a6160000c20500d00110280321401000e008000800d1000440032400c03482c41c02d040b04143c00c1d6131640105512401040c0d00000462282c402c100802d047c280c00c0240c4c014000c0c200010311400c41c03408141030364042d40d10004480a500001c004200d410f48115402007491001582880752607034800c085807013076001c040d00c2106d0205016080500c1000b48400e03c14000d500034903c9024100309800f81e801c80000b40e038040c06a04050102e080000034124101d0785510004 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 887391465 1250 887390215 887390279
    0x60507031a1203092707120c030b010207090b03070b040f080d020d0e12150f271203100b070501020702040b0d02031f020c03042301050708180f090a050402010801 71
    0xc15140320002c3e10002c8480600c4a51710340c86521320500c074002c175440e801743c0303442d404000004035a021102001072600d0700d01044002e0b41d001510105983c07804500041e41020075000031f1800c42c55170300a079501400007a0201e40c402403c1c102c03c08070703001c04089840d4040c8491003aa12244442c0c6907030f000441d401e00704142450403881c81007004881500b96076940c00c0022036070308000000c8a03400c511281d180184601c00401a04885241d044620880c13407020082000b6070f01c400c44120003820098010000c940c0440719441e0701d00c006d0180260150f6a40c0d00791800c0d602030742050200742d104503e051140141420001101d100b50303075000b0013034881c1c1c41c40d040c200c005c201c81c2c690029001039030034040321611034010001400a803084910000029001e01c1031540b01c40010100c050410009028820000308400f0a031120902c1e072955624001c0e10f41e00100b045008003212803544003c0d40014865601c100781d1000340503a0003030b6034043c40c1d030fa217884000ea047c2d082500604894000a105 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 887392715 1250 887391465 887391469
    0x8010501140f0a0302120a0603020a05030a170a260f01050603060609130b03010911030d050c2109130906050f010b04030206030402030309040c051b1204140a03060507031a120309 78
    0x2840d03460303100e01300142060160741d45500365020465280141c1940e4140a00540c0b0f4441621001000110002d08480b4415901c0c00b000569510124207500b40c04106203e0f054001c0444d056a8140c00d41845c80c2a00e44c070152040d503d1091b250040200d400c80004105421305000300c9200e01c8014201d5481c0c426600d09005082201480c1e081075a90303540942e154039602070050160060095041c1c24003a07805208160070f00e6a800c0c2408140801008600f482c0d01c0040b0360074400b041480800c1c0307101403260319400c0d10791042040719030340705440544035189440d01d0360100e0303000b502030201000159074200070003041c000c080c010011010401d0101b0401854032400075940280b019081c0d07810320340c860300801c0a49e00341010400124002203290211040d0b10740000049034100703802400801202140100b040c4524040c3d081902c80505e0380d006c2075182c01e18080300642d400300080007185801c420007002400d004000d0a41c012107449d500c84145001141c04034290754040141d1716122030082 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 887393965 1250 887392715 887392717
    0xb070f1706030a061e0501050303090d17070b072a0302060a0f021b0d080f01050907080c22050a08010e070605030919030c0c0801090b0406020a020309130c08010501140f 74
    0x10301949407040000c2203001690318060708207008505c0c400c6a00b211240401c0806484058100e14000c0e03105208484503a0b40304200160001d800504420f0310454070b010f0200ca0740715500000e06450b42160600411075030101c001c5c50002d04032011040d0104081641040ca509000702c0035006910101c0403540c0085070fa403002000181c0030100600d00b0303030b410441a41c1d10644082142c2d0030b800082c000c400c0250070500362a0301240c2c00c01d52614641c105000191400340c041d00301000c0004220004401031204001c42d40d8a07803401010008004120002851291050150b14051504450f000516020502440c00d100c402d0001515006081c0341044640b0780004041c2911031045c0181c0e80d1011400c0f980c00039401e0300a40e980b500c15151410b0091a403002984000e1481e1314189510002c5080740220ba60401d500032005070303882881d01800c9296001d0301c4486a4012200e0b80c0c4080c1100d61035022800094090b140c80b038442eaa5180103580b69003410004448d1071004009212003215998 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 887395215 1250 887393965 887393971
    0x3200109080a0f0b07020a0510020a30020904021c05060f01110601090b01021f050604150b09010e040b03070b0705060106050c07090b19030f021206010b0a05070c1d040b070f17 77
    0x4411510180700980300e1909e8403a0348c00c07440300d0090380021081c0609605c0100303200d00040505008074000801c459402c00c0a481c14020941d03140d02080b404440e6881e901160030012248032111220b0403002d038030400500c410f032240307445001417200d0f080e10b95020700d21854070307901c0c43e60241189030301e040501000b404180c1031003411030244042c84208160301d40403895682d115131301d0008030303441c04006010854a080240d488175082c003c400b00b0801d179040303040b0751388400c0a282c00036041f4160b1003c00e018049130151030358540924407001c6040340424001e068461702403000c450050740e07900c00648bc1442508000c0d00203400c0080240801480d0307030041d080c0c10002904900515640079558482c0b10040c0d0000c82c0d0b940b04a4842c40300390720380900a800d44041440290444e945020742200e1984128810103044c0100401d40d4414041c015517560b000340480103810601007016172614140075401c48084031740b481c5207804500d03106c1c86079851011310141512401644080c00e861851101d03401 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 887396465 1250 887395215 887395217
    0x31207030e18190e0106180c110105070c0b0c03010e04230303101706010b04140f06070501230108120304050f0a15111303060e0703200109080a0f0b07 66
    0x200000b012046004074031620404104803020103030300d80b212541e001e881d14500e41c0032450781048004d200341c000d44100780d096049200d000060721075201c0e406403251144c15803107400c0395107032404000060340c000d806460454440d41c003c440030317aa0381c103150450740020301520500e50f5107040068001800400d03101d240040110040d03107072400c205d02161460f4003c681030500b4100c1d44904000b1002406104914418140040c0c001581041d00d004004e010303074800c1c80706880843c11030010903221200c0301d61408502a041e2075403154a07003050ba0182090800c804400c241c41075054402c100d04501d181c0c180c03488000540b400fa00c401e00d5030f40042c1c001500030341e5903000b09202d00e044c6190070040f08880922807100e0300d00c00307100205004125039501030415130340f8208000b0500e00280c42c914040940b0b520100000742001301d5481a8070745003da0f0030040684407443d08008201c0c2c1d14041d110304004090f41c0b80103c5a844490f41500ca441c0740e07500500581001c80d0f40310005010010a0303510003a6 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 887397715 1250 887396465 887396479
    0xc0405041d1b090c0a230d0603081206030304061209021f211404020409060b0904030e090106030b030318030c060f040e070905060a0c05031b010b010e031207030e 71
    0x1c00c0410780d0820520b82e42c081c0c1000300d81c42d004510340c1046100d260780f180f6207818030360034890a618003070031882181d2a550a0003c8400480070140c80c1c04041d92120811383c1820000c0c2c54891503e444141d00c811a002c40c00c5900310300042c90b0303180020440e4141c6080b83c0d070720303941c2030084a942c134094044884103e0b44550180d0b011000034030b00c42075248201d580c50340ea0b5079030032540c0421a41c2803911400500d1245041c05070071860307040c44008041c0c04c1907041d100040c944805003400300062061040036540302c83c1100600050581c040d040000c914022200046e013666102800c4d011105907da4450b00342c0c2051143c1180140e800f000380d0705041004c0e00b034404034010800020303002e500401c401c0b0030007200420240042c2109038240340e401030707131400c245000a0400000407110f0142d240140200722004040c0400c02a062050320b0000c825a00d03952010040300348440e0180c40b0980e8103600042c0701103640e180c14507000401c0701e243d10700c501d603051501c6416102180c0039030300e44d05060340080b2 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 887398965 1250 887397715 887397761
    0xb0d1e020409030c0b06060915030618010f0f0f030b0403030e01141906050f0913080c010603030f03050a0606090513141608070f0503010b030712110c0c0103050c040504 74
    0xd0302d00a8a2079030740302c2d65078042ca4402e54070f0320307161481000e400240254000d0015000d05e4852a21015550144000c426140d603944000950841072000100542d02414000021403c007510352410640c7c0e510306010030402d1700c6e1f5010380c6501781d06200240002102e00d010802090090340510002d03015003001103240b41c80385051402510f01511040b80c80019103d1080400e1068070504000c1c15080301d590300b0326540c450010343c10305005010340c08116800e02d11902008a82d0080310288101d071402402915500e04010b02024840340d90070001c6030800c0700045070030440e17105880582e500c5850302c0d184181007100f031000340308405420315030181da42c00d55949140c292141841c458038808c800c6c0c00d240b074018a0000c0407030301c010b8087c505220001900711403507a0404192810b50300c088207219120303035407440c00311564a24000c1a40f80b40b89843d0034084543ca020008003443d02d4484112100c04400000444c21900c0c12a50034400340411f1005000c01e2500c1d412054503620904010b002e14030b = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 887400215 1250 887398965 887398969
    0x90409021e0111010b060403060b1912171c1e062301080f040204020a1b0b010303090b0406360b0307020105073e1209130b0d1e02 57
    0xc6007030440100590300c00115035082e43e404209541d007640780c00300a2102148180224000d40504d0000603c600d407900b0140c0803503241c070346069580c03604507610601215130360b28542003114900030040d19040c0c42c103003010007440d400c0800c60b641411042100d0760310449800322980204808084105c800c03030000300b1084030350058000c600280c100404050391a0841c1001d025180c0c9290071801c0c1841846020420300c03034128280581d110790183c40c007507035030507007a1030440c0d161442300d402d0080f04000a00020910401100e1981a28402d440b41d5001d5a12102019083c0c0120310407500091a4030803018001260a580858807240c4101801d054041c1d90142850002164204580154011080004080e8240541904070090b810a400d2106005c8039642c5103901e4020035100c194054240c40b811005000c4003031080e80c2108041e00e219400c140d010580c0b50348030510b503a04c601c20b9241c4a074840100c5103c0e013401610000c00e50341c0100d01c66510b010f035107241d003048429100444085c82c005a = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 887401465 1250 887400215 887400229
    0x1506060c0d05090a140112050a0b06040816091b0311120408120f0103020f0607240603050601080d08040b13120c03180e0105010e03120a0c23070b09040902 68
    0x81d800940740c0d1501c03400c0f00d40510203540c40c1070f44602c00f500e01d21740d200c4140342d07082105020004020040800c3d41e54460001344050480068401d421040c002000610312102080341003440380402c41c00c00b44a0f9131f4054110944d021300c0160903155060510401c071071402640100e000d203d0b003207101401c00c0c00401e14201c1a80c8103e03030645002d0400110300c0341e0200c8440a40380d000001001c1c042255045030085109482c201c103c03140121000100041440305c0030240e20240c9070103a10002034000c1e0a80c15002034107292104468034414100003248d0044041030010400d070381a0758003c120391711511446120080545050b0860000803074400100e208140c41400c401e500f0380310399004c1d115600d00123089480d08418940b58503070740101400031850701d40605d8110380782440c0168085c07a4810009080003140301c2e81c0769003041c001550f8019607400c00600d017400360141c6916081c1128040d00701c3d600303013403002e0300d61103540101c041400300c00030705005004030400107440055003a45d103034089501 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 887402715 1250 887401465 887401483
    0x6080907030308180f0105100612140103060902130606110f0a020f06090d080a0801180c09090b19081506060703091505040909050c24032403100209030c010c051506060c 74
    0x9454030f60b690900642c0d411000740615a080c4aca0200702901440c0100240b80724103020091110740c503000d0120030740d56181c03650428040035140403c00342d680c07520064244011080340d1100303030080d03050003428a2804940f40c800c0940151040d0041c03c800000c01c0101c2d4042c65005038000e40344442c0301c010401c800041c1481c1d81042c0c49403802e950400080c102c4400c290000c15000740c1c10a40040b0304603900170100404c6503103142e00803d000400c0400510402200340107060f0783c6500c800000744200002644900080049404070a03985505051025a214078040a004584200c50802103180641105015100e4610b00a801c00d030b19015103009849810805881c03079031041b244007003280303000c0180000446d51030100034480d41800c5c0d00104c5030300000780003405403112a007924429001c040360041c14100000c0c140c0391140200354010009410100410b13029120b40001000c165004144400040e0b41110050401e1107030f0451106074450000c01031030700302d4428840000c8000c001c000410b4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 887403965 1250 887402715 887402731
    0x50307030c030305010f2612070c0302040b090615181e1801152001020403050303070207050a030f080702150d06170106030b01170703020d0303020406080907030308180f0105 76
    0x54641118280141039981c182c118240d051b0300700314208a2000d0360b0480140002000d0f240350b0009481801d141e09216a0500c0c4402e007840014030f40003000703d401c00000590b84200c0c0c04000d210564424400c101200f160080e401c001c0082503441080c0070b60300503140c0d40c00c2800d5101d03605402440450300d40c1e003603102c07a03002c0540b03100c401c10124905000d000d28080207851884802d50f00d041146240241c1904480080c4000354070300301e001d0116940c000344d048607400700946d643d0303a481c582659260300c102c0c0c0701030040c00b80c65000300c1e4a21389007107842c08032604040481d46460072900c070514141d02c0060f080fa4040141880d2b21142c081d2080034048403c1041d4000483d5031030020035402007605000d0b448117991600d142400000c0c449001941520001c204501a00714171458444ca0b050581e080654008520f00301001015072680040060b0b91031540c41c8840f0780c40f0422141da07034803144d010080101c1c80440c0011521900d200c0d0f83d021004c048070486007641c0790070102c1e9003100c005440002c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 887405215 1250 887403965 887403977
    0xf0403140c060706022104110d030c0819020d020606060415030f060e010f0603051905100b070b070e0d050d0513090609140903040303020a0314071202010b1003140a051305030703 78
    0x102c2086208100c0780000c110042c821b0035075141942d501d04072480000703442c0b40310b010b04001900074940b04064548911782d0140f02d0070340d038900c80c100c40004902501c100038014464101e60074110340c030110b0010b008120240502e81803d04018036410804c041c0f40515040641d5140e000c000c0b0310150040b00c2c000c040c0f410708901c0d594180141e00e4022005038000209041c240014850381d110b1140440b06640c80d000800070322910f1315881d00300312a125a02280c840e01e00072510ba002d011102242e175000740074a40719090803034641000d000800d491b080015045401070f18020112034000c00060462550300c0d611680410340301c10b86002140c080340c0100d800307980d13121104c56914490380030341604500d1a000950030300d45503039402582c451440c4401820401581400c2c0811080d281c203640c0740700d0740040001d0b8100c0c21540005c4c0280710200d510380c49002c084c1020b800e0305021344105000b118840d52441c02030b66480e00c000d000780c03030003400300b5a500714034503510400700d8003d001a1000c40d2181c2c1da08 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 887406465 1250 887405215 887405227
    0xf2a09060504020703080a090c18060503010c08090d081b0d060906061e0509210c0a06090609060507021206091f06050a1211150406080c0f0403140c06070602 69
    0x810200d41203504264066441081048080383c2c100006540c004014038000ca000641d0b850000d43c007403180e50094107071411141031002041441c0e0004001d030740065000300100203100d2001c81e490a0180c2d40002c268201c1c40c00522010300c900e0f00d0307a522041030b444d0a5001c2c954410f00803000d91080000c0c003004d6648800a0042d078680c1d000f080003d16140c641a001c003006106686190070108444005001d4002000f1040351940d00c02119000c181d81803442c100700001d04000d0300e038a46003d070903124001c82903011440c140076003008426200d841e561100381e14203107031003601c0b90740c41003000b0381c0c1c817080450202862540400c034051151100d00060400c0ca9040c00c0e6103000e01603080742141c00315060802c28030546d06c83e00d041034102d0f60f0546054030100a1414000c030500313180d0684d9a000002181d50320a9954104020320446085070f4805c403040d074540042e81801d000d140d529202d050300802c010800300380020342c14409000341038142d402c01b0f0308410028106074132605048234525004213003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 887407715 1250 887406465 887406479
    0x110d0905010b0906030c0907030618060e1e0a0e0f070f051023090609030d030e0c0616030c150614010314360312060901080d09030f2a 59
    0x91030300b030321400d860081d82030601500294407090346201e15802054000005901144203801150080481040d0f160780c1c0e04a4001480c0601028040d01c584100c915010500703440c0d9080008040c03040448500301503884a00150000d00946541fa040c98803842440c240c105a007402002c0086c020700c0d840c009124600414442d204061940c0707030f0280f0007510715505074000c0e02c8603085c00315038140030380c00d5549807203070002422401200180c907018484c01001c07440c0326405610540a02030440102c4080160101c1040080e2040d440042d40d50408a801031000038001c4282851151258540e00500001480c44004583c2d80754801e804072000080110200c1d6014030640c1c0940c64030784045039007450b205250704040c001c0c00d01400740682c03c0601c0c021046c583e0380400c6da00c40c0105000e6995446020000c4141c3c5141511051f00ca041c42c070780006120f040c00100040310510307a403262048140341d07071181e00481c23076141d038180e4000e0a0215514640c0849a00440790b03c80b8103080c00075801e080c020 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 887408965 1250 887407715 887407721
    0x1b082701091a1b010c08090a0804060f0c060216061a130c031407030501151106060d031206030503030109140402030a08090109030c080604210207230306010e15030a0b0a0f110d090501 80
    0x100100d400d230462503400300495282001c5030141c1d9110f00700400ca1001d1154100c0e42003001c001d014011510111b49000c11505c2808200000b030701440003409130490002010803118048400550302440e03501780c0a40030071640d089405444c04508002a0110410b44419008030702111140b0000b9580da0040c8541c400c4000000b05216091524800c0f04220685095603620301a01d0750780310f8550450900c040600c030f00302c0c6560550ba00c1e90306110243c0e40b80f4010b5500e420078016869043d0810b41802e244511068504e48a290001c0c020118100c80b44c03141e4040d40d000c0010581007140089004c004580c20320012802090340e20000d214618180c01c25540140c016000d41c07485090705100c490130680d000907410b003a42c031580032030781400c0c1c5460904040400103580480d014081c840c0000766140260340200c3c403488070307480c005c04c010110310201602d844400200a1401c10300030003040c007884141c2c0c050007221040703140000300390301007500c0480d09030000500800030b80d4a0719002020442d080c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 887410071 1106 887408965 887408971
    0x15010305040f170c010b0607081e19050d1b1d0301090605090307051b0102072105060a02091009080705040504031b082701091a1b010c08 60
    0x1520903000c0313400000010f03029520748866a50142010400c48009640c04105a49404208100504890000c0710341150a21042c0082a900340c09014143c1c0650f24540b0ba690300c0d40741506500b0141c410307010242c0c0881183d0021045400e1304038041034440d40080b81070141080d0401d011070700600c03100324040c04090518061208501c00400244040c034000c005440803d41039280910b10103030001c03240760042c6e10040080120541c280745034038411a500d103440b80051001d481307191903c1015581540c1c250f50003e02c01440e0701d8598080103402c0d100707040c4090780c10300c1d00c54156164006840b6403070169031110001001c05200e01d22001880541c00c0c00000304010703e0805d01040e402a842010071102c0c1c0601c090321464000c506105e04210503921201414204018808001c80301c90748400d50751420320500304a00340d440e4002000c04a1140001500e440b100360003085a0700103 = true := by decide +kernel

theorem cover : BRFrame.Cov 887230215 887410071 := by
  have h0 := BRFrame.cov_init 887230215
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 887230215 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 887230215 ≤ n) (h2 : n < 887410071) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
