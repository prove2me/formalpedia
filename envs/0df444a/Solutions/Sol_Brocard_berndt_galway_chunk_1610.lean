-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1610
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:51:09.936097+00:00
-- url     : https://prove2.me/submissions/a7f27673-fdc8-4048-b0bd-9d5e8bb326fa

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 289388489 ≤ n < 289568345 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 289389739 1250 289388489 289388497
    0xb0706020c01050403030b01030c02160e1b0309010c09150818072105010b010c0804060c060608010504030c1707030903022407080408010b0f010807031104090c020a0203010f140f0606 80
    0xa07600080106107450314001d40100714603010300d4006860900d04900890002a00c1d14240200c501800081c524015004488800041c0902404180e02154001c240e02c850080e502498130b010002c5042c665030b0720700400303160365544010007507038000e60349401d140c1c3c125040581020090003082c1050600d10501850800c4552209102c2040904000c0100c0110040c02407210b115000a0100c04840401101c03981d00790304000e40580c000f080200700707030350203450440c0d02c2c170340308403004103401c3da035910034074211182158298085500030110703804020941e03042e41007200320700280606004150b10000c020045500000f8000ea01d2103954220503000e5441c0710405000842c8016503400ca5803400210542051281308060340c201107100f403051801c0d140102181006a40354403856449441c220050300002410030f00c094410880414107050700c1c016041e807160f2a400402209445205060841d00e0b40303074562406a240c2600d6101d040606100150828ac000c10a100e01b522200b00007030741846 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 289390989 1250 289389739 289389757
    0xa0221101b180f090504021c0213020304020a0512030304122a05030408010203190b09133f080c0703021c030f1416020f031b190c050312130b070602 65
    0x80c0c8030704000f600d030310585c00c5a03120f40c1c800d41c0d01017103034030008004400864030381070000c0d80b000a8400003150740b04581e02556019000a2094241c5940c507070100b00c2004202e44400e2542c1c000200300414820414502f804420b20741c0b5103141100b95078031200e82c0c180300341040164000600303100e81003031180410a6901030300380c500085603641001080d081f81c0c013400d80804e111440c00e110380d403016480c1080d2400e2242ea986c807851080c000d11aa5155107485000c103400311011481141710050500c0b02410208a6188030704440b00520402d03405000d4a10041000c0c4080d1070810101700000ea0214260701703d10829200040034044055056020f80740e03042c10326a030903113021603020300c03a00c40d501c00be40100c008240304e80010311a80401c0341c5a542150091120340e1040100004495460109520703001c2540c094807281c0c8041c0300c91402017002140c090b540c0c40d0302804140b0103480c0c01e0011100c05281403000e680350142c1c00d02992040e050b0342c410541c41d08070105d400c0050120355011140c2c500 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 289392239 1250 289390989 289391009
    0xc020f151b0c070b070c06020a1a0c0705070602010203190608030406052820010b0a0e06010903051902100206070c1209030614190204030b0c09030a0221101b18 70
    0xf40e201d003240940d41e040701c0005d0380d00980312000003485c1d600215070780e082c0c81e03008080105541000018403210000181000d0f000c1d000400010700411170511404001c6c0c00180e0000d40d0341e0a00001081008554410f00c00c20249001002c0001000010488041300c2050401ea0307103c00081c00c008030302e00640c1c1d1108400450903542c1007019035105181c00c0b070100e981c0d50410b0440d03506c070103454201c4003c09912904481c4021040c07091514040000c0e9001005140c03068402c0c3d204e03a103550410120361040081042c44a45d60811031500d182c2c15130400c041c62004202c00e141214008040241000002e4040d40c51108401c5249200c3c104110180d83c00180074002c0720040c0305008041c10040b54218500061510609032500240c0221802ca1360416035200300c03900e03502c075408941c3d0b09c50341ea080da041c4a100e45080042c0c5030f034070406440c8003866400c0c1864240d4200c89504001c91030203a182c043d850b0200601c1c0a8204108003030b1010390614080258a01c95041d20b991410580c000c20680 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 289393489 1250 289392239 289392253
    0xb0307120b0a050114220204051914030d12050403140a020a060e190b0903070b0c070606080d09090c11010e1b0a0e06090a0f020a030c020f151b0c 64
    0x21240707004040307002d1108800c04203c03d03030340c890801303006100312500a03511030381c00001100600c0703c0c2d40b8001d95200b01c0c003000506e0141d9880000308010112801c8502140c03130b0b01c03c100318a000e80d03003008a40721810b6006e01003004070194010f00918602c21410001070382e40300401d007418400d001041e0b002404010841c0d035003075100006075039912040412074280d0705149a1000b015008152072812400c03034058840c407034074690380b07040b0360032001009008944414086840403600d028920b0340509292106242d03102071600f0400c00740c1d482c0717400180c02a07000907160300843d0f0388401e0b14400c40300c02c81e000240c80104100101d40c1c40c0d8080c2c103100d40d03941c241418840ba120010036080c070042c00c0c500c107401c5040e0200d000e12503a116144101e401010f506000074000342880c2c171000ba44610300700400210b240620381c0840c1240c100200d038800203a0703030380710b410012601004660704038150400100703100baa45840c15054a0b0780104036048041b1000303150036200c0d502e40304dd10f0b1440500d0b401e41c0c0c42 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 289394739 1250 289393489 289393493
    0x1b03060203040b09061003050d0c030e0301092102060606070b0604180506060103151a160c03030504030209010504020304050a060f0e0132070f0c020a0816030314090102100b030712 79
    0x140080a4802443d0750184c036010652282c03048002d0701c1181c0e8448e0107004101142c440960f1141d00c030f07038426024400214059000e84c0d50a100ba00c0d82148108a20780c1c0c503100000000c8244a124141e000541d4841230500400d40d88900a55050940c801340764030031a9a80404030703000d06004804085815298100001001804509584110000e030780400c001813503590454803d40680c4110351303a2203401d60110b800390034120000d1080422060028400c61600d0b82ca0301d416504680c401c0e000910007003010320031031814508141c01004200e81c19821805c01e0348030240c5a02904100030310180e82d070554918020110f0b00f0840c040d000d044000c0020080300103441407005180355960b041500118031007646094102c1c19140980502d81d20020400727482c540540b80c10071200030070380e8040c4404000182c1c440c42001840104248083c1c003e02e2030380341d0303e8090f0040700d544014030510903091061401a9900080003107561800b98000725030102010080b07810070049422080702e003038200301c035401 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 289395989 1250 289394739 289394753
    0x80103061d060a0f1116020d05070b040810060501110c0907020c130603021003050c0a0e0a180b09060a08030901200a0807140c0d082a0708120304030c1b0306020304 72
    0x5005080500c14401e5298241d002c01d07242c4503540c0c0741c5e04044005030500016050100146c23100b180b00c5e03005ca03465a41c8400c3c503895560419030224046a000340d180c02d4038501c580c040e00f80140002c0c03d200440c0106c541c805d0b0307140c030a503078040d500490300781e0001440d1a1003080855a04c00000d40140b0700301203440d00703560103001540801d03401407840e09085003000d80b00b407050501c20382c0702c2c1010030f0520145070011a841d4400390300f800d5001c8884900441c9022402034000c400190505000070b450000005201d0f07001002480280318000840701005020380100440301822030901c0c006072010001c00720360f4a120003081c0603442c00e2103421025010001c40f03a0040c503015005964405046004e000010703501c0041d122403580003480032a0507800500c102d00509030700c42001c480c0240480c446007240504508101408825030b100c8501000b420000f400350480000199260525620742603c01034207482d6044402000740c10300000c0c032144110060400c001460f80408195a28181030901003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 289397239 1250 289395989 289396001
    0x5100e0a05010e0303100315020705030a030902090f060307090b031204080a0c0b04050a12030201090f03020c010f050f040b09060d02070f02010801080c010210050903040f24050a080103061d060a 85
    0xc500b0341c40c001d0000514040041131300d110b400032034103204002e800c6035211010190034030310328008603800b40301d030303d0000307506101030041c00c03038280e500007201c072241c0c010420321040150001c800c0403c40d0042c403840742c0300071444d0425644c0508000c121207800741c022030319103111030020740c0d806c03070000c00c000c01c01c21301c040b0355680c3c2c55010307080707040b801e90b21520500603600c514420b45a010100d44002c2202c05102c090000c40710703000b4000059103c038a07498581d88d89041c04411030060b040314640715a0b81d80c0040040d00c060119181890030034140d07696143d03103445540280c500c07240000c194403106958110448481c03903a450f6055448005601d0300c017054045040d400c03408900b90744004202c10030001117400301000164014014a0f0001c1c4602c8010a00a4100e600c0340c0000c010202e0110210005180280704240f5580e0444002d0384e0401c0d5003031000000d11041203002c02810390960340c80a000381c1500c2e00644001075011050382210b82e90101032407101d0450182100700308100d07040c0c1e4041 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 289398489 1250 289397239 289397243
    0x20d051006052b0614040b070813030c0209130c14150a02150a0e010c0203030912090a150215250e031b06070203010204150306080613080705100e0a 65
    0x207214240d2101c082009200c0c1002043c015901100402c04034a0044045542000d004040c000740420213840e60486a8104031000c0c1d030201d02210600500c103502000b420340c002004401041e00c4050790750001d16100903020064483c2c14414003160f41c500c100c440075001598413030605074002d541d030310740c00405080810505214512501d00d54070004105004c55681002d1940a84880f035491281c0a105020207403003814000d03070700c2422082c244001d1051285285481d0005e40e02ca2802090146c9890900106400603038418000d11b201034540841c04419660704040403000c00802d460308900e0b1040d03402180441100020601010301481e60031703040400501e00540361102000107060700d5115078a8012505540004c041c54248200402d450590380d0004244901d131030800d40000c3d00f0380e00f040d003050401003240c0c050310400c02d801d841243c0c024019003019007001e20748030302802c40d84105c942000c2c1424000140c41c41c10864280409040c0a40c42c0000b040a80c46000d40355540e60307400f01c01 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 289399739 1250 289398489 289398491
    0xe010231080304050a181b0207140a03020907110c04060311030f010c080112030c05010e030306090906010f05040f0f0507021c110a0813031505151e100c020d0510 71
    0x481d003103502004442c2942c5002d0200401940381c407400c508501600e0101592143d5900800f01c00c0607070301001c0700c03c141065401840c1d558280b4240e11446400e00740564400d14080c03004000584840074019440038481c28201c501c4031010044d24102805103055541c001c3c42c20034007004000724031040d0101600c00f03804aa840ba5030ba40030203401c030f0700340f1020940070034440d80c010008940140c8410583c0c41c4207142810489009541e11402e41e20031010047c0ba60b00b0120802c0754038282844d1896100c1e0907000205415450b00400081401090107585d01581d11030320307120442c00081d040385008441d400020800c6c1d20b000c1200a40740d000e00000c117440214440c0c483c1c100309100d000110389244049014000440040d0f94142c05948269102503401d802d004000020842038180c0342c0c2c030740624090108480ca0800004104010350103055031103000404001000134207594044494028151241d00d840b1a40703110544004100740c80003540f00714004124410440b010a080f05480003482c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 289400989 1250 289399739 289399837
    0xf070b0a0e030705060414030f040b0a18060503190912021f02040e010e070c080a020106081e0a03300e0105061c0b04030e0d0602090109090204060905040e0102 70
    0x540700d0348a1103105800381c04c40c1e0001340460302107411003855052070450744003102c0ca041102d02c1d8105050300107500c1401c02d04000703d40c141e400c94011101022020427681200485030504202401c02d000140c1001c2032044203c08000c0c44118941c401c003201e035002001e0a60032089454000d42d240c09610100c09000440302d40114130105a0007a24152407030004039401503800d260070b84400c03040007844e100400c41c8200d40c000228070342030010010302a4503400402c1c4a400e100c1c00301d15142c3c000910b0a80c5c180008501c0c4510303071000c0350514865070716107001641e80010704003068111007500d03281d0600801250240601c4481039002c0780001c41458003e000640c2d5a80c03c018040c000745105003140c201201160002404030440c460b4030501c030f0700309488110b43c0000841c18120030f0650403100d1960001303c0150325a080001e04004210500d02135243c142841c0313009285100912469008944401082030049001c0d0162400c07503414080175880320140c0c1d920302007180c604012098007001544 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 289402239 1250 289400989 289401011
    0xa080306031014040516051c0816050708060705070c140102010e03040f0e0f0105010905060a02070e19140601050d02070807020d111e030d0c031e0801090b030604021309080f070b0a 79
    0x100f011040f03a000030020081103521400d005416140c526003111410010408442c018400d101650ac1c0c060240d0010020103090880940c5070940151149040c80014010003002610440416080c1d4507100f107030b54000303960744006034050100100030896070f003c0490040f55100c00c00c20000101c612038203410342c2e42d07203402900c401020401e0054500050200b02c01744a2070424000401e2900c079180b0454001079034800d240d41488209482d0240080c20704000102c6420160240780e00003065401050300710b05180001030500d10660744143c904c035802180c15010320060700140c8240701c3e009420741302e00103554a0070000c3d000c2d490402611407078403410405079565a2a855054810b00030b401410202d885400a98402c0c030800022010000d010700003540c1000c8202d038144520307403580c4403008176504040b140f00a50f1400d59a9600a80c010410003015a55000b00f006291654030300000714183c3c9030400403540e204011144024240c0010340300104100d41452911a9007007810811a02c0203030 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 289403489 1250 289402239 289402273
    0xa0e100f080307020904020114070f0b091605120f100207020a120c0303031104360915020309030903120408010b0901060c020405151e040614030a0803060310140405 72
    0x64029640150b10078003032180107003084400590800e005060001d0010b403410a4410f41d94000c403400c6a0695004d04180708001174203503c290012000d0780640b415004069001044203000d10034144501c0207240c081c10f0750f0005004050040c02a5016190070901c0307514218007075404988102c3c002c81c0c4010b000160004a030086800c15540401e80d40300c00c605d1900c084015012200d1640ea218000304000a05010280d444405018441c44501400742481101c6000300c07001c90100d05002d402c121400000901020101406074002c050041e1642c49540b52940b40d40144071009405225001c51740c01d03049040310160088641c0e0310002d200c00130310b01013030002c502d0742031288101058552200b003005103001e800007940031201480c007441c081c1e030b84000075240000c068511040c081c00380910b03252600303090081c50702804d89010411191540741000c240d90f4013a0101c0a00320410100c0850016581407001d10750f4400f140c0c0c170074000c91020a4500f9a50300c000c2e54202c880380b03c0c1803030b031500302803107 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 289404739 1250 289403489 289403519
    0x927070c03140a02010213090b0103061e031e0204050903030f1e01060e150a090306060504090209042a030c090f050702190302010207021305240f0411090a0e10 70
    0x70607541c41160512869640240780c003e660180290354081c444245424074407403210000302818500800d6180800002400b25400758022010600c040710222041c043c817002c0741e60031254044802003511103884500c0080b01140c11000b940141800c1c2880528100040950f00130b1a512110b135207a51500c403005c910424642800c0c285d0b200c0b9540042060380d0090410345040040904a20108144202d05520035403001d2080c1010034260602401440207500c281000381400b07440030041d0240c2d43e000240100307001000203041221030100c3c42410f40c15170b0b554441400c856030600c0c0e02c403a128503054441d4006401030f500040c0c58400100310f0800c0718000d01d80981e605030058004a80152440030003607040c03401c280c055640800003038005840b441c0e0001c90400358040c2c0080c55003004205c3c0c400018410f40e9484102822040042241d0754014030b08101220403a0700140309554804806840d015020703266a2003c2040800680a210900c0581c4520102c201d60f108080d00d03407400b03080c090b127 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 289405989 1250 289404739 289404743
    0x9030d180302090702030c07080601260c0405040c09020307050d05072d140409020406171b0a12020304030e010206012108030c04180912050c0d080406020927070c 71
    0x1080801c10240c10302031281c0350440020b1059915010301e40031703a00d1818110768808622640103000400004501411824244402008181c035080c2918103659a4070307414414648100d5507000880c0401459494a00040c900200150f4032484c060a01800c0ca40000303000544a41c20407000400e0725104402030107101c00ca03504a9400a442c03011840f40b00102241540207008a5295280c2c0480210000e40028034960f2409607881e4200100282036001081d1249082e03d088030501002c02c55154081c0c48610071a0521a180c034105c081c02c036041d504400103813001c1440041400103150307001d040512141000e800319042e1b640d0b95220710401b0f1400c1c2c03241c44c510409901001000031a0100219041180602654141501c910441120f844482b0030f0340c100c0c1d990f480d000c000300800d0010345007131302807981445130521007500340340c41d203a5002500c05020081d5900002d0304002160b0b060b1200c0c0b01c009010380100c01c180c901d5012804061041c00152414068000382c03c1900c281100840d0603 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 289407239 1250 289405989 289406027
    0x5010b0c1c0207050d0b0604060608070c031110060e0a1109031209041b05040905100302010e0f04150b0a0320090907020a0b0f011404060f2d080309030d 67
    0x11444258528841d001c0c1401031003140a002c90004003075480d048504442da02800c4000181d05001040100f110704681c42402840190b00800c03812139080f07042041195010b09180c5069400311007040d0410201c07840c0b034004a80f40090118403880b4404d1030030300c121407440c1c082041600c668503501c100c0c000d0807111a499031003503450300d90140141e000f0344814403024102003284482a0501444800b1b44500340e4000b46c0042001c1143c0680fa00031141c000f100c0c1241d43c04014290b400090030394036180300c0e80b070113440b20301e902000645969101000e840c503c90304080f003031074446505000c2c0358491010760b00040d0411118400b810f90004540190700f0b42c50f40e1541c54086044144440c4180081150082d80203650a400205d285940341038400c440701c0f100d07204150b0410480c001e2140e100011980110718110040c004140804405000c0d518074103951341035481220070034480f075004000880c5103184090070000d5000c000001070211128200c0903038800c8440d4240803030b194484000511300074 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 289408489 1250 289407239 289407253
    0x9153624010e062208010c0c0209070f02031e0d09050102180306060604030222020a08040303180302060f0c04051302090f090c0703080a14071701060f020312071701061205010b0c 78
    0x9003003410707480b04213803005140441c05641d0702c403058211540c03440d1a502059807640000704601d44018072692218940c104410641c491010095507401400d25018a404158200a0094284401340d81110404140a20041042c2d14201e0b020b5041510001540389150742c60011031320b008100c90344501c001510560030b09281d41c0030010003140222006600c105051600d000d5401d1600080c0701110a54882606500b007078a0300030101e03550461100441d403000454000080c0d804a01242c0202c6c80c60b940c400940c4800c11140c1b40d51150780e1085500ca5140c1c0703044000042141c000e002c3e00007085070401401000c84040c00780d82402101e18580c190000c0241000080c0904651900000381200c0010128086400d0222403d410f8640b140841d80305000004010f01480c034031405855145002061900300b0034020703640703000303401c0c01c991410241070004103201c0c461144a049072007500304210465a440c82c010313152039051701406000310300b00700000c1108040a401c0361500f03d0305000401407 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 289409739 1250 289408489 289408507
    0x5030c0f0406050607200406050303192114090703050a06020d02090607111f021009021201020307051903090b0103082a0c09153624010e06 61
    0x282201916403154030569603074001c549601c2d5900a0001c6500c200603d0380c101688200d0f045c0c5010282c900a0322890410b482440303d5107001c01954200c4059485c00d841c003d001000035261501c02480920710a07180d80b080018100c1c46411606200002280841c0039896202c074645c0c644401c0d000142044c1d01c400038400c00030300701c0c1d0b0080c403425200101c01824803041c0c0d80010610390186900b0385800d07040d451000f8061402000304549803400d64001410060640400307501c80c0d40c900c02a03d4031507928443e207070564891400c445000e42406000310b5032880c0c074060207001c0d80c0042902010301103a02e03104001003402446544261034020034415035503861566428000e0341704030800b0018600c058901d40c1c0d0b40b10601d00060340c4a540038007500349440098184608580001c10300c02c3c010705401c580340a5910b0780780300ba118206014a504030020582c80d03c0d0362600ea1000f4200c82004203600c100300b01040c1560400d032010144030100e080e038200007001110000d404001c2e140c3c0c0080f041022080c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 289410989 1250 289409739 289409749
    0x907020a0803092a10020c011b0312021308070602070503070b0a02030c070b0301050f01080f0403050304030c080a090f05092712120114121002031312020f100605030c 73
    0x9030264440080b00c1c044d4111a40d280805240341c800e00407080390b1203001e4a214039000d22031300c0c0040ca5520040040b00c24120008000901507290302081d0f413034003110003040c14451b082e1400200c200c0c590656840f0403040d17213180e07001094800c5400c2c9001e000e2000c1591880414601e0480d00c0040082c0341081c140a404951a8085aa820190f10003003124480b8030f0f005106201c0200043d0030b807182ca941c074000c213220600300a400042d04108024040258032159144001c0c2c001d41c0625256841390349070310701584d00701864407015014000100b88540e040d80c1c05550001039484011100c81d03031540d54014030149600903180e0b4405401410010408840f0328903840c0c401036640d0046549100700342d209001c050780149001400c0c0d040d01801030041c0c601e10760211000d007100b924407440d5000012180d07900d40f442074649440d074507000404207002c0c005510841d01c23400e8100d41c9803d07180710500d01c043c0d0354000d00818540c05010704a48001010401d00c038201c01c84001802402181c45c0d40130800c5 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 289412239 1250 289410989 289410991
    0x30a1a010f080a021c0f0516351501080303010f09090b06040917130e0108030f0403080f0415110c120d0809070e0c0c010b03073206030c07020a050907020a0803 70
    0x286145c1c1c0702001d010554906041010381e008202400a20700b41c60787d907110020403904140c0c5200740100a0200703c0030903050b400101c0d010b00c01040c103003c2c1041c8034941010001640d20320140000800407070044c4003c401507040304c41d469070100000356150b80810954041c2640075000403014030000d8800d040a80040750014890700020ac40d0b46031b041034001c2150840c40907481c0303170442200e0500a2003004203409002d46402002541800f3328025425518800e50100a1080c3c101056000b031240642d41550058502c0e2000a0052107055600424079030888000c44014458004120304504000c10a4004440381c00040e00503884c80d2081614491000740a40f1900d1090780c80000d94041c482d220709000d18200d003851550350400444031401d42da5403520091094006103070070008070510540c608412404900008a100300c00054401924100510160402030000400908403e5200108480d500c21643d0f803481e680c84a080c4880384108494040c05070744440084030110b042d01010f1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 289413489 1250 289412239 289412269
    0x80f06010c0210020a03020f030316050c10090809030607030902090a0c0c05030301061710080319021504080d0f06031101050309070812030a0507080f07050c0705030a1a010f080a02 79
    0x40301d4a9070030350110700c0754040e0b00c10000068104141d800200740e07040c08800c0c81a0072800042d42982041100f5464041007481a54103210001a4800d442031050060107020051300a040094020b80d08107043c150b80100707072030b0f44203015410004424600901c58a9550b9801030030b902655030750540814020000d0302c07020400c4c48010030100c00011402c07c0194041c100c20b645000002289500802070130101030070740100d40741504030500c03514200109076180d0701034401464003413000c4140164101285a5104054455800104800d02164a00074401d8510f00c0c0010403181c084120003100b21055408000d15071156081101c10740d601c103601840c0c0001c0703104143c94100350744400303862510000b01042401c80f42c01000b000039a02d41480b0320380d07104403a030915030414a000c101c800310b180b80060540007807050102d64040b29075030402101c80640300103812528241c0440c18403e4148110941c440c5040404034000b14084100f000d007041211400c5000f00a0100d5070703800c2000700c500041030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 289414739 1250 289413489 289413497
    0x9041a0702030f03010b0c01051b0d110c0a050d1d0303040905071b0b0415020301050d30020a0c0f0e01170102130b030f010905060d0204051f03031701060f080f0601 72
    0xc1c00b43c152003a44010f41c001d0007420707151603a502d84880d2050035903000500000c0c24204020b44d6400307851a10048500080c607120001a400c0c5200510b5045402600500c44e11849a1044c1c0070803c000000c81001d01a10741e02c034080d050500c01540e1034800e00041c6031135016007092104100400312074101e581c10205504003540c00100320070b0790b071003d10301600098450305071b240300748000e0051000740140103841da400154915130409010644400008800600c010500e0b00d501205041d052000780410704084070240c0d1030010110000c0d80e5044003002950740c542c105c04006580c070f030b07000ba1483c100c0300d40c080f4800c120303880d0001c948034500b40c060120003a5502001f1a01d00c50701c0d00410724000c3c00a240c0155181c1c204907031a1030100c1816085484103e24003c14000c09076544441d000c00c4a80c12980130a442c0c3e034484025038501d1490755680042484248080f082680140b60341840030010b0141543c141ea807200211010f42d500e85605021584c03032008119504140240391354030003c10b041c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 289415989 1250 289414739 289414747
    0x507150908070b04060c0e0906240406020106060e041b0c080f0313030e0a032103140903190503010b04051002031218010b0103020906120601020712050601060e09041a070203 76
    0x720504540d01c580e030b04944444802d4100030801c846482804a50903151801c40c2e80300c449800400c0130400b01900061041c2c0680400002c03d0700c000a20b100205406502c1c02d0311681e5074200a4044c000e24010a03010407102c0c0394110403030625110f580e256450105266040041005054464010f0040c050740c10000030812040c00c4c40c0c1440085d401340b05030b0310180c4d021941c1d50038000c0c240e00040030709500c1117204440400c0802c058040c1c100300e0b040c1240305030521101c4200c3c15402031140e03100236030325420030381c041114660011003e042401120080e112104c2103d20b01228184000d008030280a0f80600040c807480c00d0808030900c1e4420280103d03403a0044d04138203103c810304111141d8425044582c041e2642c0340080c05200300342e00f000e0905508028420300003480d40d0040896402c078903090b6600261107030784200417038001041c5c12088001a68440d040c10340c1c94040900900c00422105c5084007524185807440900c11500030b100396040c51500b6600c80c2030000050128421440b00b40 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 289417239 1250 289415989 289415993
    0xd03050d090b010906091401030605070e1c03030e031207050d020d0f061806060e15160b060901050d0b070f09090e1b0625050a0f03030c0206010b090105071509 70
    0x441020740190240c000081190726124065040d10b50681104c00804c0c06d040000d40c0100a10000c40c1c1940d60001011500380e640410403101900c1d1078895513400408407040112710501c8100c402100343c00381da0140490f5102110f09642d9208417200f003803100024000003010b40c0e10440c0a40a0118032480162600c001040396000b40d0718100fa038080d41541d64081000000c164104000500c0290b00e4144541031800350007800304261080050f01a202084000981446003c1104d182d0355940b40c2d01710740d880c500d0074910349100301200c045000e051300e100045280e00e0501c48502c10036074803842c01100c9607204081145c081c2c1a4010303603400e0044c1d4040c0801c01010b0f5004500e101a9568000e0840c0c1000d5804070301c16803038a01919000b40d100700b0810012992021b480101d020780c400b84841d00013050b01d0403500d03005241d040076200080030b4807070343c081640c1500f04150041d415800c94078a42d80ba1078040b252403041c589200e0101d00204200c400003020030611100e1811041400a10640c4607 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 289418489 1250 289417239 289417241
    0xe06092208070b091005090304060c0606080102030c040317090d0807140f0c0a090c20030405040f022a0d0c0309051005040602190201120203150a0305030c0f030708090d03050d 77
    0x2d0324040f10030401020400481d0b070b0040100d001000c3c0016424010350a01e03183c1d203520f0707204034051241000300000700311091190640140700105101c5001310340e2407419000d025101d40090200b00c440742400c01c0880c40c4180030600b80c40b00344000404d0100c0c05030603170b80c54101551144c0000c0303401508103001450038200511080301c50010784000780c070385054400204811034103035801c40eaa605d80741c640058281640031080304020025924055004000d03469214518007940d071015134402c1c18034901031180768043d0094811038111510240703902540701e031405238a0411078490202a03001c11034031205140304100d91000c1034024100600f100b81c60b000850314403120541c03558041070300001c1c20481c1542c100625aa80610a001e10b00442107a6000906803800c03819100d00350350f004004500f8044d0401c40c0c0540030345004003641c600940c2c82c034251f03449801403022210140200702119490b002d0100c100c44007241e0000d4640d14080d5072104006480200007010382c00c0007000d2040c20305900b11 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 289419739 1250 289418489 289418497
    0x50303190b19060f02010212060603040c0b18040b03010e0a02130b0603040506040c05030604050705190b03040f050705060702010c0b0a020f030a050406111c110f0a0c0b010e06092208 80
    0x1591451000b210b0030b0110291071244141c01031000c40e803040000e035803c1030a103001c09401400c1104c929940307859030b0510f800800e4141d00310060001c0001280180001000802815080185c1c1d05116001035002010300b00d6040002d5031030140c000c0b04000005141c14145414040002880040c1140d100e0012513180d4204485c11907443d400341d400d000c18490340001120007000220020180e82c5042c1c1e40382901c6038030510986002d16524801c80c4544200030220708050413504001d40d449103003901b490380b166518040190b8240c01410404107107400c0400407140d00e9501a110122400300319601d1035445107004003013000550b820300c504c0e10651401d01c02103009060701540030805d4101030421004449601c94841075060040001900c20200224030802800034004002503100100703420600b240318610038105c0280c3e000419641d82d5030441d04070f003109030141009100e42c1c2e80314441000507a10035102c1c4ca50046e55074000811000031607090f01001e01051510710600c540d103a0f100007903504 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 289420989 1250 289419739 289419769
    0x6060f12040b010801090309030b060a050d1a010f0807052106010e0406050a02160303021e03090304170102070534030602180102010c1b0807020a06031b0903050303190b 74
    0x445842844140001c507030842e80540224002045094060780d0041c045039681d2000034500b00000c000110b45507103402c0d08600504000e0030642c81e0061a151400014960751496038403800e41c0c000100c1e0b800003044003541516000340040004a042c0020040c07051903400e0842240c10182d40310303090481084c0074260007403c50f84a240c11038200341c6000c00c2600d0380144281e691601c140000c504881c44440005451a01410016a1100c4403020398100120341d951440d100c0400009108294200000a104941c80e118214422400400640b030a0307115005c2e024089034000070080080080c0d5103502036880c40e14004458103480c2072011025002030742d500070b95800e40c0c081014035140081a0b90849015030910080180758680c4130301402c41e0400c0804001e403d01c601c1448c00401240804031020182c0082c01642c4c40799a409004014221080403143c01a100913601810140034030500c0c801e40c0d501c50080c5056550b8422050000110156040780d550744035042030365103880303540704200c00039 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 289422239 1250 289420989 289421017
    0x801022206030504050a1e0605090c0a050108010f05060c3301050f09010b0306010203070807140c0303030c07031b12090501090f180903212703080f06060f 68
    0x603100300046494802541c400c10502d802c050030003000031000b02d560441d20b46d0180c0b40710106038186184901a141c2510b00504440c900400d00500840c00100b08085c401c0440c3e08079050781c0c40d1401121500c500f84140484456028414130070b0307152050107428a4010441220700d1081c4a110b000d01041e02c0c40c00039448100c54072003003c1e0700d054603000d1383d02502d000d50300c0030030700f4140e0b001180d40344205104840e51001d0120101741c06a100b0b0048851494021400980f9001d8a0800060b9000d55071500c3c0300c01e01c00d81960364070340e017008400da0f4807e59801e1802400d201a40d00d06a0703102c010341045001b07031a025003203c40000c0d585144031030701142c00e903502e28600c0d0a140000d442032600c0d0b00240601120707001c080004104401c2c0700050103010074000304007541c1c2c526081da000c0400f200b00050003484251f0b40c9211100541c0410b0002010014103110111800140041c207240d03588003800007100c14000603040c4050328080350704200c0207800c19103041c0c150704030141c15421440002d0000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 289423489 1250 289422239 289422277
    0x405060d050d0503011d0903071101051e0c010c0212030c0d0b1201050a0e01050c180402070605090f0d0c03120507021005090f1c1b03140d02030106030f05091b0307080102 75
    0x801320f141902d000c10344001b86084550304003c802203030b0f60301a05000400c0703404050f143e80e040782d101c0c0c0155144102031080410720300031000c00c44941d40c2c204890300034041d8a40700102c0c6400384005030180342e482d1071005d480c0c911780714060108041e0b4080e1515004841c1c031004001c200c2c0c4c665203048840d50f0400350001810303040c40f1720700c0e2043d00e40c4e4490b15505a8100000d0003080c2625004840d41d01c008241074580740c411f0100420040d01035018080c2101e4a84010032000440100307520200020b16800d80c0e01c5909040710640e000c04e010729014002401d0310300401e40b40491503200039084291801299a211100c10f194800e0303400480303a44150383c024560200c0905010400e02903c9540c4400d410130781c100000c4002c0110380c0102c2d920000486070300343c00d400e05005d40000d001c860300500c100b0b643e802207100c07084041c0d0b20a204100000b860314011003c0803080c0d114050180c0b10700c00c0034100b0025240804080101c20700d401e00d60500400303c0014a0901c244000c0843c146050074090300 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 289424739 1250 289423489 289423499
    0x1050318030d050603301c0617070803120f040302101b0e03070b0d15030c0b07031209020a030b1e0a0504170f04090203100b0c0c1309110405060d050d050301 69
    0x10701001c507450440701c00b0101058070624076400404219a80320b20959501c600c0000e1a0100155011504090342d500c0c000011030100e281c0c046034489400d00c007042b900074a80c1c0303880c0d10356030740314805660f00105009008140343c1c00d101e00303003250400d010f48104c8001800d11541d00b02121409500d80c440041d084003c078060a4206891105006048001c0e081061500c842e440f031521600e0410150729680362040c01e080d0f1031455040c2d001d1504008011a803c2e2160a44a5603921581055001c18201e1030001c101e55100c0c09541c0358640c7c050220f04132903166542c3d00e103403804050280c40080b00760040e98207401585140b101d00c180000040400c00303007042d0400200b17100082400d1510840200001241c41c2d00f843c08031030484240b0b5800581e01d5442003581c0f0021007103034000d0664071200180320240341d0000503511490600446018100100ca4000712046887c0da00c1700a082c19075015030300e074031807602d94400b82e84913002408815000b8203d6481c141060689110744001c5040400180f103 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 289425989 1250 289424739 289424743
    0x915070b0f1b0405060702040f15090507031103070e1009051e0a060c05190206041a0d110405030a060209040b0d03090801051e0f0a11030709031e02060901050318030d050603 76
    0x100c4603200c800b00b40c034260800c40814154072440720b0280c0101c2d110210b12180c100c4940c0410404011800354038180fa40b00c60366400039042c181c40c0040024100705507602481da0348402c0324000e81b280d840300840042590203200400880e11600018420b01c0342000802d0303141c0c1c03180d50b03921100001d50380d0620520310042090080e400d400c0703001000154660314001440009044902e680e0f4050301d00c0b210709541c07000030740600c46e6801c4401280310540350b1070f021080900181c00c000f11039140c24002003006d00300c503154500a84c80b030282c0c55802181c01c2804a41c069004204910f80504045003401c0f507280810102c1c800c02c002100004c00760a002c108240c000c0c40381641003826859640c10b1401c5a01001e2200e0f030740075040140d0f0281410200b512005160f000d55200350325103d145440e450031140207007100e0b04c1480b00361801d424000384041c0c101c3c00c5c04880506c030382e8014900c509110b0950011502500000c00c489030a210115410200c51000c1001c1d14540c50b40c000081010321b0403406242c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 289427239 1250 289425989 289426021
    0x41e0e01140921030405120a0c0b13030f11030c16150315030b1e040605070e0312040902160b0405010605151c0e0709090b06030d11030915070b0f 64
    0x8441d00300800707140740f400414600c542c921200762401d80c1c4945513420142c7c10003e0240c1e2048440100240702c140280c0c01c0300746041001e01030550405142d40d0081c0c8007172403240f0400c0050005401d05002541c003801110285030200d0f600742101c0c100101600910b242c00b02500f0141400c0101d4042080420220740c8146550202c1c2c0c6424443d1001d2000b0800400e102800001c10003000b1100255030011400b8030310f038002101c4402100e480c1050308020009003015111300f00001e4840030742d40302500700064501c4010aa2059241c5018540b404440080d0010000f002e801c00c030a0f1441000f03d015030b14000e0040d8082d00000501c58544410130240e401024129504450140005c03120384122141ca100719070400000484da01035003440b41400c01c481901702c01502071a02c1c076020140700100f80d40301e00c54a0207404440300703607102460a94820305240d4070b52015910800100c455403c0c10064612543d0240c0d880c203050140ca9982c50012001c100e0740e810000b12144100300001e82c2d41202e070 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 289428489 1250 289427239 289427251
    0x32a0706060f0b07080715021306090501110a02090621010204140d020f010c03050c1b15070c03171207020a060b091005010503040f0b091b01030b010806041e0e0114 72
    0x1030070340d24900b160700f0156004403280a4a0300a000c503c00301840034040442d090001e1400c0c045540f80341e00102d81200c0c440c98092000068041d020128a5500504803991081034290040500001d41d0382040303200314000f890980c02400012005c1e10a0452104020400e1014000540c880e82400d850015003806561240d114480d986841000340e107901080d0000b1007030a183c1008044900d04050340c0c0d40c414054850075511400005c144001e40403640400000011913480c041d03c0c00b403d004600c1c502035414040e24011168104000140304400d4044900d1240a0b5407802c100000ca4144140e0354204d810740f000d07030040d29164041102505c60505035107400c98040c20345050647c4c1e018158a846c0c0562814004000081010311440b100c403842580d80c06104c0702241d103000014144c4078801c00c440311081c04132041ca03252007580603004004540310182c0d84c100b01581d400040001408048468000b0245d080d039001c00c03807201c10f000780c0c0c208088003000030404ad030140281880001d002418 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 289429739 1250 289428489 289428509
    0x21b0f01080c0c0703021905090f160c050a060f0e10060612090c090e01090b01080a050606060a230a0207060212161406010e061309050d05032a070606 66
    0x5480490380e002424660404500100d0544855503142074070314140103a00080e5100081407010741260014860720020f40c3d0054810110984900c8000c0c980c551081d9450003241d506036070030843c402c1c0325092000070203004604440d450b01454642008131044005400c0c0c0781600c1c1e82012075140750403c06800c0c0c07a40c80b0002000801c0c50035400802c1c00c0c0c90f80d4544c405894407003540d041400320718080840503123004141005002284000c460003804043c104030f440101c040000140c0c2c0d000404c00c1444503411a028101030f69a000400c503483d40181d0300e12040c01202c09105044003035501d0700e40c01c49200d81c448075940b000131700d2000c0d00e48201071b03110b03808545c000c0001e400d600ca1414180c2d4501040c850905420081078030b090f030040480c141c1c2d07a164034494030000080c02c218100c00180204000e41e0708400c00606003010400f40c41941d01d0280103640158280010a84103100075176015501000c01c1d404000c061240810f60380e00009001541c160102c0c440c018000d56101d000d00070824006 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 289430989 1250 289429739 289429759
    0x220905010218010e010c02150d0203090606120703030e04020f040305030313060515011e05041e0635040c0503030d020c070f0518041506060c030e03010b01051210030204020703021b 79
    0x2000034601b5070580030081c06403001300d00b10501075000805807604812410019500c914110803507c2d503560003120b81511540c0e4015002e83d08403004207011040d250580c1c0c403450b404c0150010712001c0c1d40080100113100b4000c000c000040b5205001031405030005084a800204003400c002082e1071000d000410480d0149458000c140c0e00100305a0281508a0005a41d0000000140e402c0c2c01150300c00c1955080d40500c003c0e16000c841c0c1d601c001c0c1c96040d11440200d40b441703000100311000700c0b980c08141030740d40c400c0401e04007000308505503c54460000342032542e45800100381160442690b40310120b401251250401d031b814804000503040086505551504c0e2900145d05e00a050000c401d002003890301040c240b01d42144640744208241c030041c0151039668100070442d15200d4800e038005200c669066a5514060003000314212059640383e06050902603002c500000241040ea00307240c00c4000000103844600182c20650300a1700170b4054250722486480310b5881040700107126020303440c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 289432239 1250 289430989 289431017
    0x18030d0e060702010804060b06070c0315050118050405010e070609050a050303090319030c0b010b030105040e0c1f030204050a0f030c081507110c09010e270304030222090501021801 79
    0x350070b44500310340901c0e013110b403603d407400c140d0018041c2d20212a0014000950390301800300801e407440480740f1404108011303c3c0c2003504142103800038040d948506914030150b09000d10180c1296403c54010800010a00840c10040c1c1c83c1c00c80542c040c4020851540c0100f0292515100010040c40c3c10380185207401c0c2c030100020303120b070200104c000514102c0c0d41c85900b8140308185401c51117908c50180354040d41c68651030083d0780c20920400b071240e1b00300700d07000000c0013000c911811008006001c901d15461240d400c4039124201c031039a08100355003400700203950343e9142c944000034514603000034a40d40c01c45c1016140d0000c0e0350400c12980e40078070a6081a07141c5500b0b010b9000c40146040b40183e881410701605295080340040d0340064541d0001c14101203041645004210460304000312007400740d036502a540c40b400541507542c00c248410009801c0514032014109042009a820611400051412100307601d40a48081e9404206000d44883c03051001c11018001d0806007d0304810b6 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 289433489 1250 289432239 289432249
    0x1009060b19050d05090c12011a10031104180b0d03050d110903100f050108010902060417010e0307080715020906030a0b030f0d121406010f08091218030d0e 68
    0x10705804001403210034030101070a4401d5065400200803000c003072005080149503d69903205090309107100d41c88140c082c4203203c00500c940c100c02c00701c0310742c1041d0300f644030410000201508041c0e0018143c49081407015050a80000c0c005050b007000403510207000c9c1c80c40d40e404c0b00c0035500d805000da0581070b202c20109800909640b100402d07140c1c0410541040c0c2044c0c41c4601510b47c0840e0948030380e000301c000d0f03880300d030f0000c100e000d03811502000107030799984580d4242c035043c02c0080d40181c400c000c18002120b80c2142402440059000030070010740741c48100740b96600c062420b958040000c81c05030200000500e0340300c9d000c41070b0002503080c007a5000004002d0f100c0640002d8020b540c0e100051b030162018060046420b4a0700d0540381e00d000780083c05070007131300206020303090f1038505201d9292070b039090f000341d0b4040d00b0180d54019003614000816541c4e250007030f014551511440ca80604038400308401850100740c2c1c805c0c1100c4400b00700c018185001d4281c1038050522000c101100099111 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 289434739 1250 289433489 289433497
    0x303030118090c0e0103060207032d080604020c07030803070906030c050301060e0d0b0a0e01060f0806060105130807150315030201021f150b03091e0a061d01141009060b 74
    0x2400000541e01a64079002c0c3c0300d036003d03610441d075000c0510000000e0003080d034090608d607030194803000c804035150045040550390307900d000c08001c440c9100c080c0c185032042203000d0744524041d00040c0380508000c501d61605401341d204694100000007041011540003c405c1c0003028a8101803040007075132640030704903000502070203003004203601d51500c059a9500541c080c6540196890505040c8612000007034a00b40c9001101903013400400113002078486121411101600040c3c105034031030000440f000d0780728881002001440320404104848240004c0004000e003ca1599601c0840d20f0043c0940d4426015141030201c051020000760740c0100d14080d180464600c088103585808074071000038104c041d03040c2c20b04140400c5c0032440e0304030703080254007402c8001c1c1103c14003141990303210004401c40100c2070302030700041c01c14000144280c001082c40304940041c0191110040581402c4030200115000e00102c40e205001d540d207224488540a001b24240a0150758203042d40d60420f03102d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 289435989 1250 289434739 289434779
    0x10510080604091a06010e0102030c030a0c05070b031311010206040c06050c0f060a021809220821060108060303210c0f04121226150a060908060603030301 68
    0x3807226990307079103d00364a0f83e210469001c0400141d0118206040403905a800300714691008800d540c000401d9441d650100e2000b1840e04060620856020b0b040d100106c3d0f41d885480000b155008126010390b01c01c5840d030070054520700c801e003800850103440004003415500244148004200100b4041c000c0d02c10b5800c0c03650391481c000703142e01c0c500506010031441c0c500442e400c0c4119865141c0040c81d80220200c0d01c3d10165209404120411106a03400411102002020403075040004800c0c1c40460180c1076140c00c10026080c8140e20885401105458459502c00c1166039030300060010340000c8281c000718105181e1758640c02000f80034040e5501e03036041000025854030103460841e1740c01c1800305c0015844690f00c1d2100300c40d01d031220808542000d8101c0c010f20358503100f040e90306100c4000b050400c261116000401c0f4101c2000380c84041e81010716842c803a11034135218204801803805541d03680c091484e281580f4100000038120610940081004001580100641801000f = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 289437239 1250 289435989 289435997
    0x5030604020f2b140d080a0f181401050f070c020f0a03020604080a0b01050d020a050d0203210711030d0e1903060f060509070905090106050711060c030a17010510 71
    0x40740c00000102d039240240300b1100c0500c043c000f080041c0d6101e4000d0000d003440b858425205000c4600016240e4450308030000000300f207400041c0840e20180c010303021200317a0f007000044803400c01c0c0c0003903000000d11901303503500d204510404180341000d1040725030002540c103c0e00304a060480c8000c0c030b6041c19001c040e00c81da0000c00c0e0b214842e500d44111100442d0b0081505036615a100d004c15200c2460650690780c5280100000510341440198000099401040244514103003410006403680c107010580e01480340110031030090b64504840e1020324181015a612640c661415002201c0f01580b15402f0b43c020018941070030340c00c400d4103c0c071102d0485850078011791000c01c24140322110b0f03002901e041d042190071644600c0c0c1798051400c1d41c0307040d50b00480da035850040c00d4401065902c40c4c40d4100000200411020344036030050a03002d445403034905c00035400400011050b810803d074103503941d0000501c51000507007083c004100d0114040d401c00c0c0540c902000610810620310041040c0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 289438489 1250 289437239 289437259
    0x3160c0519080c01050f04021e01090605030a0b090709181514031c050301060f021f051003170c07120b01090209040e100b100c2a120305070209010504060503060402 72
    0xb140c2c0082c0e901007007448000704010f02d04085002e000c0f00d0305a506901451030940000090029201140404030040c1c4641806030f10f041021070b01075100074202c10219546010181d250ba0700c0800443c0a0b05490f0f440c41481400c181d00d018103a440700740c141400c13902d420040e2420990b440c40d9102101c094a5030840128481c901183c101300c2a04400c0700d0048a00341c1c1c1c0c00840d034102001c1e60580d245a42e4080721107020280c260703510f1030810040c4140d040c158600204024070382e0421940410a8400c0c010280c0d900c2d6a2861144040c200c04e028004010542c003e00040402012004020000d102030003501e0684441031225410b00510309455000501c04003580c580c3e41180c0300c000088e004503008004a090b04100130001900e000e88254009100102054031035600f0100300c54010ac500410340461011f00e141c044e00f800c5451711501c0280c400001ca4400d401804480107010341c480035504c080078410041c1c8054142c02161043e85816001d110302c3d1800126039038050790645910200e = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 289439739 1250 289438489 289438493
    0x9040b040c0801021206060c0307050601061d0103020c0339010f051513020c1f02070605060316062d080907050d0c03060518010608010903080603010b0108040f03030207120503160c0519 81
    0x64ac81143c00241c1503120340d200000c0c1031a0f0110340c646c40e801d580c40d0003048610f540340044040c1d1080ca00e40100541c0140850881c40e90600d8005405404000c4100488581c40d004210b612075120303103c690a965403024400171110034028030f03a00c030004c82040301d050310079030b0005070400c006c050504441581c086070032001650300b003042e190444038400035001c0c400807030708444003c0e612a18088580f113003007001003089414005250b161100e24102200001402c2000c00c6400402d801511000089541304e86902240b040c942c00c6002c605550350385a0600d440d040861901d4040e61005011f400107480384404140e0075811842900d5016001044988a80d17004000e211b52a09826210394680b0400140c007290540c00078000a1090311191160303620030040501b00c0d0b100d003500c140030400800c0002d00080d402c50084083d01e100741001420030b5480d45032000005000360400002c580d0010500890108071880e405440700c05180c840024045a074a5540790324030710b10b01c40c0c500f804030700010017 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 289440989 1250 289439739 289439743
    0x30c060901140c181f0f0201090b0604021606090b0103170705030319020705010c0f030c08010b030402010c150e060103030e041e1a040e010f180c1a0909040b040c0801021206060c 78
    0x68a00c600170440175a01c80540c1c081a00c0c0e035020303008400402e9070091500708190040c01b03050003aa4000b48001055620030040c0300186d400908400d180028030880c83d4009840d51251003801e40c003903030440140d503040d0704e4400310301c0e411441c1c03071070400d603003841220300007240041280e510000000d1171002650300024008080d0150060042c00c5508100313105103891380c01740c00c1840740200c0d541c06100c005003c080554000c2070a00855149920810001d405940031f007141910541c400d580260402c2441400b42c0115050285c80c400543c005800400078142c3c401a62641032504840c01c02c01c003034a0f400c2c810170341054030296442c2c01d9121803040d2000c008602100800b4030700680103002105030041454002c0c002d80240002d031514048204040700f602d02404040c035540941404000b50400305d42c10300e18400391160005030340342080000200e440d0512124096481002521034034100780c81e000c261500313544c02081490b171040c0b10000074012401d401982120040d22540d07950301d0700c0e0030028 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 289442239 1250 289440989 289441027
    0xf0b030403050d1803020a110a030804031106042301030b060f0304020d020f04110306040606090609090213150c0b1f0b03100902040b0301090b060f0703120e0609030c060901140c 78
    0x44c0e80750a44141e20b03030074180c000c91120302a40c89141c0c0c1d144069601c0303080061000050002605100003131106000007610030310110701d0301800411190415982d200441a221032240d41841c0e103220411281c0c6095070103000b41e80c2e42e030504448160422140c000ea03240c803400700038006403003440302940010079910303000c9480c00401400351050008045803050f451003a030094560900a2385003000c000380242c81020184156201c980c3c8807a112440c107601e800180d0061040d240440c11045000144030503003404520410b4219180ca01041801d402d007404592001820814107007025030a8520103440340002d40b0649212001e03085e102d132110b044810001004c0d41000c40e080d44000340c0420540b00010141d030407101400000c0c0310407450241402080e01030b02500b205100824814040002c0c0244032200e0328880c413000000e800c0403c0d40c00c0034030b4801b064940c01c01d2034200241a480d005401e012244d4032090312402405580c4549065103168000200b07105010320000c21465076002c0c4a01c800 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 289443489 1250 289442239 289442261
    0x2071e030327052407050a09050d03030905010b0111030a1b120818011a010302090616061d01021603080405030d1112010e06010c060e100212010f0f0b030403050d 71
    0x20400e6640410a8012140690300c0a603014407030013203205800d2241c00400c8254008150144030544c80712441601c80b03400492401c0240800c0480c049801e0303c8078100d56048034001d6601040c0000070342412401c45125084c040e04001200740c91050b013b000100301c40310300400d407034890161503551181034044024487c1c0208000a01181641ca90387e1103000326000741c2d42c0007803100c1111070203103030719003200c0d20003990700002c0041e8020401d030b942c0030368041c00d9000f03400360640b4070b032442b030000c001e206140e04502202c116540c2c2510003e4010203a90540384042c0b2a002180381405030014205402030f840e000800304411800000d0410500784295845e0714282503090008034001112a035035504003482e44080d01d1480307000001c0c143c14050a07940103c0040e10380488034071030340e01c552000e080001030f00f204501c0f802c00c4076400a8924802401c820300c0354a0446e81c1941045040c240422056000750514080040706002c14210f45040781d402c80d5140c1400c07a96014650b00c0030029042c1d002074 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 289444739 1250 289443489 289443521
    0xb040602030106020d020d021b01120c1806020c0f04050403050906070303050714091804140d0e03010b030102030103120e0d02090c03070306090510030f1403030108150a02071e0303 79
    0x14402000895005107060710350a40035580c1c05808207400301e82e504c00381241710300181d200441c40c02c5a2841c000040540e1310040c94260101c4041000e16815216005035503000500c0480c50072082440295039400948868400b52030b03122281e9000400c07076840c0c0000715110700c0d0b4501c04181094000c000721005608007802c06501c44400c0d00f0054020107044905002081207024010403012910741203e1060200900092182100a8000108110041c02111615605401d020481404000301100407880d0b940798040c004070750050600391006000c0d454080c0c5e005000500c0003030401d540d081a066844d18004045242100001e00303540c520040c0079402694a100340608035440c2001140700c5d2489440c28441607688a0b800c800320354084500e900302c0030764044140002900c00081c0c84155002d1501c50180250200e280c0c1d0940e40280d0281c0256803044844648442c00c0d599120340c411442ca1007181070034907d1310b03082c0200401da0300503500035501d0302c3c8160070580254469a018040341d2a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 289445989 1250 289444739 289444741
    0x60906121b081e0112060507020109061b0e03160e04030c0b0c0a030506180c160b18060a0209030c060a17070e03100e0a06021b03070615140d12020a0b 66
    0x8070240180405840e00da98000081180c0094001c420011904a0f012440c28010701402621503500825000e402e440c110f540703070103074100801d00d9405201c042090124807601c891081e01d10107400e0043c1d03012014003070780180c00b5940d48004815003110845000c04e807150059a180d25049840c1401c1c0400200044444010310042801c20310150a1540d401d88080046403078440410a10306500ca01c0c0d4420301e0500d40010b07240d40b40000150120550003841e100c140c4a00307aa400c0720700c003000c40d0b00e110800c50015403205800700400180f5041141d40c05c086107461075550120b40ca401d4000182400340380005421000c0c00d228440d90f41c051340804601403003508142c007000701200d100d03a8280c1d110b446004441400030003603104040c03c0810690052900711059580c0201940085480d9a0081c0c0c406c402410700300005c0c070017085080c0c883d80300000c0c0300140e80c02454000d03034a41c0099120300110040b10001c1d44507031805940d01a04502607603605c25000c0710492038125109401010315441034 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 289447239 1250 289445989 289446041
    0xb01060203041809050a023010050f09070519030602030711010e1603060905120406180e16120e030f0d0608191103010b040e0a02010305070906090612 66
    0xc00600143d071080d4072100051585421032006079884601e0141c182d80040210000619240b80c0b50095541c02200e08140b540071b181d0360940c07099400e19202950342100300340501c2001c892150a074441c42007007055400341051641c06640b05aa801003d0182c00400b0300480c442c4401d040000003154090ac0a44d6617140140b001407140002c028411969802c1c9403190200384c201045c1489440110a5203401e42450340c0c407080042e03c01100141c40c503009400401c0c00b00c440c004010000f82050740c482c88141c0e0b9501d83d0b910b40a02c1c040e8801344040c1c900e41c0034401c0b0314401540d400c18a5559103040400310150313211a400801e00740b080e0034482d12001444401c080d1940001d000c415070204c0c410801c8aa440b1001030b2201c00d80022722000010b0f44401300d000820300c802510b5680405000014035203848408141203a0003000f2040701640424003950456030305010303080d4814418500051420b180c510b0141c10b40105000d018107214880542e0340604400d81c4c00b0a808003802145a5800c41c025 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 289448489 1250 289447239 289447243
    0x31124090d290109061505070804051017010e0106050a110c0a1401090b040e19090206070b06040c020a02100f030e070f170604080d02070f060509060a0f0908180105070b010602 77
    0x500d22018501c0c82c0500000b075500e09070300c10b140445030909140459807015540440b85075000300c0088030303000c4051101150586031071000d4044507002e526600e1170342d10b240790300c2500707000141e02080c1d0340a540401800315940c408141c03001900706042c00e00d40d940140c480d850410404102c2e454010700040310020b01d00d507060a080d02d2010081e00c40340410b544401030400640304074011143c0c404503081c045010388551083c110208641850005031080144d40001c0903a4410002070700d00740185002c0c40002d103020710407910041c209000802007509150301181c0d0f140d540e40030000a001000340038201050003a0030440044910400356520540c543c07265003c501018000c00c4801c1c94401d481c12602d0308001141e500603604155500d08041c594003d5074045d500c8440c0403902027140448510000300035019043c01402448080d103528500a0012012541e90106c080c42084c01c10321045c000c695003c0032a03024418404015010407040303030050f6264411082c000b000c0c0321449000081003540 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 289449739 1250 289448489 289448543
    0x1a0d060204060f080f150111060f04020a0905041203020f0c19060510060507021e1e0405090c010c020904020f060a02010b031b03060a15180204031124090d 68
    0xb980c5520940c491100000c8900d00e0f0102c1d2242d104000d0303140404c40a4855a0b40c140000a051615021782200c00345c01030b0a004096540510140d806024802103151011410001d400b940c0c00410262400745c58181c2855640c6036200281a80000ca5130142c0b1100c1d800c83d00369640340c80c2111103144554140d0508505141d50944115150001090101004c0e04401040707071450ba40b00341c03c16000d502004280d0224504042d10150380c00e41501094558242507641c98204e80c08804040000300309110075107600030310034000c0741c01c615100ac5e401c0c0c0c1c1000c50b4049160b019900e000b1656030350b00c00304222a001c1075191341c0c41100801c000017a40e60541000b0350361036098041c0c0d103010b080324601c15020024004541d07410b400c6a400242d40c0276482e441800840140c0031002c2c0b0455480c18004505601c4615050405400050038014003030031041c922200c0d241a5030901884515480b02507a48001d00614031842000090400041c3e64440245003001d40101e0501d003045844100005a400 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 289450989 1250 289449739 289449749
    0xb040b010f08030d0b01050702040606080412051c0b040e12030921090d020301150b0703030e0f0d050304060605061201030203010b01030c020601090b031203070e0913030c02041a0d060204 82
    0x1a00100303440d45403540103030840e610300008500b01442022100003038071100d800c090422500b40140c0c805640c0b9030113130360000c00203612441d00504041c00c000342c03440a120703210000c0c8441000100c80b040c03000005600c00e46c503040310024070040c0d110001002b03007004101245007031082220720308400f040030000b1401004000112a61781d0080c94128849801702c0c0d0984228503018820360580741001c41d850031070710b1303c010000141c07247e03202c070203000340000d03a0496803072500045542010960148502800ca022010040c03009041c0080e10503a110f52060307800040000c0440440c0810616400880151030001c14030b644903417510988405402c801d00c8164407944c01d2040b803a800d54060301c00e803500701c0700607030142c0120380c01d102740f4001902420803895010b100d0790014015803517500001e10300410b282c1d0365400e0403010078020440480005070100050180f00c182ca640000d4001c295441e00d0340d81950041040319884030410010451150341680200c4015204d5042044548c02001550 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 289452239 1250 289450989 289451003
    0x30c0f010c020f06010303020604030503040204090b0103150609050907060f051308150705090d0b07020f06090a0506010b04080a0615030204020d0605010f03140609040807021c031e08130204020f070b04 88
    0x303400c4040d43c590710502888094090b80002022901092003240110b6003d8005400480d1018a660f5202c02201003644103072112010600d0103008403405000b400024a101501400f82c1d051191401d505d03055036204050900c42e07141002e500e0b0b62300410540d002e91040d42034401500390b8074030040c0c4d210703040c0e107020501d00d805103c001054603000e001918014030380508044251007195580780441c5401a168200f58030a6115410041c070040004905c500d2044000d407041400c00d1408034034000060f0003501e4080381c240300500c054500022107c0d005504041e0125620f40c41098272403542649810183d00a0300010b02c0003d14081a04082c1c00c07940d080e81c3d420310b0b400700b500045080350003040c0f0003041e1005080100795a440c00c0034155402600819090b80350108079800111043c181800e5000b04c2002d040700c9005050304800010301076421542a034120400700300000f420980700600e02800c00502d12003480940d125070381540e10300014800801c0e0303150f40302d0038524454134044800321088 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 289453489 1250 289452239 289452253
    0x31b1b0605090109301103011107050c033918090705030309011d0a0b071401140c191101051005150c06010b030c1213050f0a11010f02030c0f010c02 65
    0xe10029540081d04180388109440c06170314a10040b0b4440c1540b8207a41e42c980c0c80c218000c440d40c1c28881c1240b034008280c00036540e2034451824504062004240c18803d801c05000c1e44282030802e5080340d0070f2141e11640e8025084445c5030351200116000c4c4131900551400041004541506011342c01000c050046800480c0c1d18005c150f41d911682216900048820310040601c802d150700c2c031100c5101c000c10901c1410b440701c010403c10340266000b954001080116001210828840c00d0038034481042e07091141c3c58a40c9003a00c580c0b01740840c110140c8bc0084080601b21310591000b4072909400c402030000e4186405801c641000c4c0d802031500c00c0900710181d000c0311610b24116181901c40d00081c1c03010340c1ca0410400c0381600001c00900c4820700412100d032406a00500c13640c0300707c1800100c000d500605082ca42d14001d2081003003030b1707286d0000082101146050900c50300c400c0092900381048461074404a0441c040c09503495000d2003807803850703010604103400c8600610655400c40d0f5107 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 289454739 1250 289453489 289453499
    0x24090c0a0312030f0204090f200a09051203091009090605091009050601021011040905060d320f0d080606040f090c030e0a0308060f030109031b1b0605090109 69
    0x40c1032100d2100901401c0c940885102081c0207400a80301c0640031000142015510400c10b82039462070345440e41070710b585010346091204a142c55404140032031007101c0c18080d501d04083d00000c01401464842c40c29110614410320701001141c4c1020340180541c2c0c001d00781c03a140501460414000c0304140d07404c0040c0031915080c50214a1301c00c024010494105624102e045001000301510315411070090803140d40715a003003802070786c0c400310600c85e05a0760b032842c2010318404c884000e00883e01c0b4164a440081c080b8000c0410410007480d0113400340c2d0300c41003070100004546122004a203141c000c4540c100e5100c1400305100c001e0710100d89414039990f5032002000107902c00c5005a070700f054800c040a01050034907a1003603c24001506001130005a501c05280c5044d6520f40d046000076601020004a13040c5050420040c4c0303815002444440c04035500074144524200160303080820750100100ad020700403c00089032a948035510070310030384860008020b0340c0300010842c0803944d9000b001403 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 289455989 1250 289454739 289454749
    0xf0a0b15070627051c110a1b0e06011e090f030f0b011406040603050402060d02310506090603100b03040803160f0e0f0d050f0309040e010605060901080924090c 70
    0x1d00f640d2040142100b41c008401c00d80c0c1d140d07040041c03501080805034480410303140130440341c101d05020b10605540c48013280f20031003000b6041e41284540845031401d100e09039820244a40401d801040c904c800000100801c40f880e428660001c08100d284410010600500401c2d44001500030b440c901300740da80746c196a40a000355083d42c940c00c144100000c201d600e119a101e0303a000ba10040c0740700c1c600545076540d002682c00003034580d80c144000c2554030307030046c03048000211424801e100380008646004002008c0317005001c030140c0540300000015100500041c010300140c80d2801001d6142d04042c20315000541080300c3c0903501704002d644001c02c032400745a0181070030401da616507803014902c000b40407400403404001c40e004440721902100245003030207140010701c00c0000030350b00c8108180c100020f80742d8081c0c544010380d1400c5814032250300c4400854a070060282000d6042e074607a001800c0c83e000c1444541c403042105901c0081d140c030801d20050340110000003c4405036949001041 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 289457239 1250 289455989 289456061
    0x207240f0e060720030408100c020c0108091002130b0706020a080c0c0705040b0111070e0601090519090c0219030f0e031605120705030a0b010501080f0f0a0b150706 72
    0x407010601d110013102084090007088030194002d14160b90030250342e155018a070200141208840948454500e210154104603654040200340b03070403d02c9040c40d082094940041868020b1150340001c0c00c00202c94410b0b16a0000380025150140d407035a04e81001d00c002e400c402144000078540101241880c500c0c00152040040020051300410b4580700c204401800b00c4002e141c188007041641840082c07080c091600100080c220720300a51030040001401d00c0d203240c10042c4103110310101c03910078074017401d00d200c01d0700c0d10760800083d00d016060041e450240011000e09041034168041e0f010141e202d103440f5465009500c0d8500c4c1c5a281008040e1195a445400c002c0e0400303a0104005900d8a5004c04020424410030750307100d0b0341c460010908145200100703845000c0700d41c00400440d42d011702403c3c5c0c1314029118248a80c01c01c0030001c0d00c0c04801800080c0308603211407440403a90350750120042848040c03001c482d82d0302c4003450503c0c027404442c03010429484090101c801c02e403206c1e807100 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 289458489 1250 289457239 289457251
    0x20406020c0d080d090c0e3402061302010c02090405010b0103180f0201031e020a08010e0606090102060f091c02011b02030427020409050c070c0501170103060207240f0e06 75
    0x1030804c00d00c25603910041c070071a9016030746403128180014000c030002e00064054292055101891200b1400b090034985e9a80d40012151b805250b0001d08140c0c0412859000000d01c840801706000074001282c0a0109481c065032014140702404200401540001900d07903082c6c030140700e0094901d500350041040c02c40003504456884520b8001984a0340c4078910640d032207202e040c81c0c4004181e113402242c01814001001c00c507103000600c10701300c905540b01e50003c81110228601400403000075190600039141c00d030000800310208070344600c2404948003041f444000307245140800240240038010309400034840c09004012110030610102c00c072016103840002040103203c13040c00e44400c498080d21706e90310b250f43c28000480c07486000e014103401440d00c240041e49800c0701d402c011340c0f540d0060f13101c6414054444074001d9a034041c903103250b0440e50040c100503100c2c1190708042122007421440d4480f10181080c41030740d54442503100391200c070030031002003000a200c0e011582d80c803c0e00303850f8 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 289459739 1250 289458489 289458503
    0x3040309030b0a111303020102060109060b04030201140c01050709150c03080c0702060403021309170307020705062203030206010f0b090a1e0f090b090a02091e040b13020406020c0d 79
    0x34000b18045508142d004907000000103000c0011040c0e8103a82d401100d02c08980142c0c0c01420070035507904012103030140046072410400c140c9003089030b80092040d40310003814080c040c1c46003442307084408150380402c03041c0700003030005141c0303d2401441da085501880c00918841ca000f0f155052085000400ba030307600d5200c0020680f25041e40c4006500700c200100c0e0702100400c0044010b840d42808450807032944200070a01d027125142840c0d4400400038001c1c074039042401080f0000381d00060200485006840d0b01d55075415050706080d110400341c1840482c01c4c2e90031000030825a0001340e0504030303400300c50281689600c0c0d0420268a101d8281c0407507128040550a02c05481c00c609001241500b14808681c0e159841c05000652140c550182c10300c550b40e52a9042c8170b0400b08802584517144907011460b004c0c1600c0000d0780824841d00140c0321800144030b04a1544407070388401300340c100081410080eaa03021800d04040e500501500d0018040c3e22002092418054024809190300440b = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 289460989 1250 289459739 289459757
    0x60c080702250506040905062e0302030402010504081e01050a0c02070b0a0504170d0f090509130503131412010519051015110c06130e0c3c030403 64
    0x56441c2d4101c001c2800100120a485000039a0b03078604004100900c48008045440d1400c07004000281c080d00211403102d0800144000b031121500c0880d14800340b190400603200d8585000484950180d904800742d9440b50888810b00d9441c00000001c2c02c2240000034409a550301c03144809403001e0740318520142c1d010b030805010300101c2d10050071007030480d850920304190341c0d4000c007480b4000e40501e00105401030745c804280b0355070204c0300451a01c807034100684401e140c40c0201d80d034514018501c0c41003601c05900c0340300300603091007140d00d4041c4011164001130340320b0b0b40491a510027005141d100781d41c1540c030000c079098103000d5144602041030010b01c251f0300701d208400c060840100050170340c03812650085030034180c035450b1100105d0180d4070f01d81380c5980394041a24103807200300790a12070101441000313000090030010a0548418102c81c800e552580780304141903000d0074041c3c02841f07045c0325038a16680c41500040e00000c82507040c000b200c1010740b8411741c45100075200900081e04082c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 289462239 1250 289460989 289461013
    0x30c1209080325023a0305090103090510050c040608010504180b0702010f110301050910050918071805160c12030b010e10020102030109060e2a130b07060c080702 71
    0x11032a80c0041489094055400440d0300044405e0010001054080030900124540a1035590021391140d0a0703016808500841d8074040c0c41402003241c2c85e8101500c0703401940c00c0040901c82108403640180c1e041c02103081140f42e040c0b03d50414000e55001400d10300c00003690745024003175401c2d1007204106103914000389495598138004002c0541040d99200e0450382c41600e0079100e0b0784480d071581203c164680d4103100800584c0d28010f009400440c4d500341060005071f84000b40c454010540748041034007a541c66280a081102036440307614080811030700103501c5651504214400c0c0150601e4400a011480007501d528a00c4003018020b8603040d803400344054001e038001010008141050001441d0000c0040e00c0c0000d02120080181d40102c01080800000d00485028000610b88d820301443c110030b0340d9210451071030f2050b200800780b40040c008150064110351003406400005100d080e254915003500e40d0003404e0032500c5c189840f10403c10188194102c41c000e0710b03d58050440181c0403 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 289463489 1250 289462239 289462267
    0x20f070f1a070c14090604051b03190501080a060b010908030a05090a0905071121070206180607030306030b0708040816020a051003290303071401090f030c12090803 72
    0x11040c08907001030402000d800700c0e41c460490f8000781180020303503510943c03403424040c140f01e0180c10180030b01c4c201014802001c0e111403046454076425951a502c981d152809410807e15880c3d104d000545004004202d412000ca0040b103018000e180c00e004040718007004442c400703a18880c5001603007003070021801d102c1c4158020001150010038070101251540d0710201111806d03900e800102d0148945c002000c2030a000481a48882c09048040321820035250702d42480344550080c49004001041c8032501c03842e62001da280440506050380301c10035850043d000b040240029114038440c0000604c0031031140703030785910030782c0e000c5007540c00c02102d403500e004840310005040382e2000703000c00c3c0441c180c2c80f8104002c5070451b884c4d802083d0ba0800580c40800145480046a0202881141c0401780c1d00e0010894440584c4003007504110200b00070028014041c2c0381340100019131210382241410780c05018902030740e000b01030f00c400414080c0c1061700e86480501c11003040350000d0100200d19007031 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 289464739 1250 289463489 289463519
    0x9040e1509160608091f0b010905031c0507050304030c150801080c0d020f0102011e020403140105011a0705010b03030d06080c0a0302130c02120f0a270905041b0303020607020f070f 79
    0x3202d03044407111010304549501b00c4000b07624005001d0795034110030b41e40751b9201001500416003a005400440008a110440c660b400840380092110010707514040000400c211001140c0000d000200c1c15100c0c0c040f410314a16800000000484190000c01c1c0403001281c10780403002c004158114881c025400d010182105007291410b6540e5003001c529050300c3e54500095010034648010f80e01c609604d064400303158035519810041e0b24010050002140d845014490711014400351078440c410751804c9400340c500340b01c1082d00340c003000c12111040360a540240c801d41300310030240d070800b0a60301b090020b80c03016440f0103075001c8904281074801880c01e0b881384903841014810f45101e004200600c1801b980079004901a4102c002640d400c0d6070b42c004600c40e8030200416180301240b40b40d4440030345850f110b0150f40180c1da52100030908000706030345034056a030305c40e4464407000c2d0303541e060294480b142240d0f9100075000388100300d5500b21011601c5810f9440c0c400641a883e81084e14854140036 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 289465989 1250 289464739 289464751
    0x206060906030109050114060406060201151a040815161806030c020f0304120512030c0d15090f09020405060a050307090218060c0709110306030a031409040e1509160608 74
    0x50707200e10300004180d082c0503107d0040b0300600b4000c1c030f50130f041c81403108941107a84030358116403500c54451400d403242c5027000103da180140500586030b908049541c10b110340d9000e0040c902c6120106012007a001c10080e200741446800d540c500d064140d0b013951302007206822410a5841c442080c808103000e9880301103041485d1040380e540b00382081c0c0c1c4074075603800754212440c0e4542c844980e000700702081020320b00386001b0054a5003541000501306646000304521000342503110142c12907101d071400851801414003800c1405454010700407440100440c810076405a410a00040c0040c2401319140301211006401840305600c1c0050440094000501041e440130380800000b104ea82c800700a0840010008041c01040d0b182c000c0d00c40c2101c141d01c5030b4454007070007401002299070703010805841c020b030142000d544660090318016914031440d2074140d441072510041e440d088a000444004e0005261100e030b00540b05c182c400c03603441d40c25200c484a404005003050000c02e1140e641160056 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 289467239 1250 289465989 289465991
    0xd050102090d0309031401110301170c270f1b1608070c08010510050607030e01090b0f070b0609040f140703060c051c0b060a1b050105090d170702060609060301 70
    0x5001400181d880c0c0c851002900015070013001072041c4101c80351021314000024000300704691004c01c0758143e500051203410003a11465400000c81d0006000e440450500282132950100b2f100801203c00d904001d44040300c4080d41000805000100d1000d50184014030310355079110400c410300101550140340c0349201403c0c280e08960008101a01400c4007521640b40707090204e0520760420708544c00241007240b0440300d148100000e449003000c940006070107181c4100500302200041e603c0060590001c0e00c11140040d04640640c2030002038100d2520030303030b14100d542e110002008410501a1409803070b02e00148800400210300c59041046555808103135001203a50b41c488500310b658030385040c408580001481040446845440e140c90216140100030039100400491098024141c00c0005e01071903c2000700c3c5050520f0501e05d10784c0c4c0c4640280810320b0402000c03500e41000f030407118041005242404002a0180500c0e8032030100c950007000c0035660841080110140a000c03e0303055 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 289468489 1250 289467239 289467247
    0x305120a180b1b07170f100504020f090403031b051306030203220203190303090c06020f060a05060310060308040f0605070f0f11030d0305070801051e0f040b0a1401030f0501030803060d050102 84
    0x1088003c05e0201c0c0c511400050000107110340c00707a42c18100d800c0742c02074041d89803208000059407810706210b180d4a043d142c0c02011750f16883c0079001402120303290000440002094056217038040700922822040b504001070310356a52109605901094900c0d2145040c9441c020a040801040b0151841d00040490740740c454601820084442c040d0700c143d0000b52602c50302003c3c441441292801030862340b0003807260801d4000216107801d400b40c4180c01140d00c07040410100e80d800c100e031030b072803c801c60410820150f0f05d04d041e00c101d5101e8865041c1c11061008000b5046008030261140103420111182008200d917036000c0b00006030b0300b422280d848002c0c1c0d002880381c904104000c06803c483d1000a03443c1000380303014060142c141c0c03009201e0250301c01c00c10000540d01e00c82c0280e02e84161110540504400005009021080c90654005980b0000081c00c3d481004501c845d8510a880c100600300d140e80d503050a44c0e10900015104000400c00300e120ba0428807205103400740036034001414 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 289469739 1250 289468489 289468499
    0x20c031c02030603070641040b031008070605070b19020d09020111010e0705190509100929010507060b040e070501031a0a0303050f040305120a180b1b07 67
    0xc4560400c8816001c1d070200030040c00c0e05007003054102400090401500003011000240b00500310120340620107440810380b80c00c41d0010005206410185144803500c480c0c580c56100030300d400c2204c0c54010300c0c10390440001c40e04808290b40c019a03640390f585500d412445e45600032400c2011381015031002d1000c07141800c080491000c0c1c8210007040d80c01040101c200d000040c24007180e1800941180d06d415100c03a00d101c00041c070a021150181ca01550b040000e181e9a01459010361005400c44000030400c04000c2e56802c4990030384455290800150360300d44d004003035000c000300c0071955070701903007030308290710b42c01a400b0740312040c4207000c00304200c0010700109041d1000e41154100da9800701c28188410340c0c02d8040c40041d68103070103150304540041c10028040d0821340c40007409200c3c0008002c5000010441103d010359001421213010b0360030030050040c00e900c22100903000070314070300c103010380024081008021a02c1c1d045800341803080802d01c600a02114860516282c40307405e1001403 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 289470989 1250 289469739 289469767
    0x7051906110c03030d1a0301060b091002120a03090201020d020609030324040c0206070f0503061c08070605040f12020f1f1806050f010e0108063610061401080406020c03 74
    0x20b440400c05c000454141c480300011104440d2a01c1ca051007641420000c2c04031164050980703000c20400c440906411143d840142c6c01c1580058511220320303800600c02c1007068242c3c1004800038403e0742207440c801500041280c8030b0800359074940b12900108041105002c40c20280d10f0724142032008801100440c400040071120f4100c0c042000d83c010108122231190021301d521044106404c20324030314540800064401843c0c10700c4808010b00907a04801401155003d6035051680034038200241e09090030114040c08000d00200c60200d01c066640c4505c1e0720200f81c9a1605ea00d034001130007451115203452071750311400110020000e6848007200c048800c0c4010760090b01740554000121800d00303049420445005030003245054003010f00402c07500d0b00010701c05074050020041c0070a00d006010305d14076440301d199034000d0800b20544818a010300041110001e10080843c04c01416036074800041e1100e141d80310381800f096800c00001c0c0801e405800800e0030486d200c0540b49810000301c0d07d20 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 289472239 1250 289470989 289470997
    0x121f09020a0b0a081f050303070b151306030605180c090c0c10020417010b0303030118150311030606040e0c13020d05180d02120702010509180a0207030207051906110c0303 75
    0x3c800507034001e09120790031140c4502003400d42c006022001034142418080f9507644210f0100a160708540c0b00015030303510007117a9109584400608601072440d85010000180c110340c04251012403415010a000d00d400d8000f004100e02510f000d40886550b02d0300300864001c008120303103001681044000c0f2210414001000c0d4411012401a2603a08042603000d00310a5184040d103180e141c1346005103990340005c1500d0444402c031540902c25800c10011b4005400e03022043e02d4042c06465000c020080e08091800e0174800942c112049940d5517000c0100791280c000801d9150307008070801d0710032801c1c0745a00c2b0f0070940d400038001d468071403410003800869200722421501254403050f00048280c0c24800800c0030900380c8014a41d1601c07440340c3c40702921071004024144900000d120010ba29903c45e81c41c41b815041c42c620fa200c0c941035041d54080c5d07010362411801030040441c040b0341450000011224090b00700c0d8150807203410444103803035901c01054021902d20406048105a9030200014 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 289473489 1250 289472239 289472257
    0xb2803090c0f0503060c0a0c080d0203010815040803060f040b06030403021c020111250f0506010915080d08090f010e07060305070e010807030c030f09060209121f09020a0b 75
    0x1000c800078207040740d120446402c10000402e010b0010481c0da900020f00c3d42c0c00c0307824001c0310b9694151a90b41a00d14451110703004001004c04070382c07401001c0f05980598100c2c0c07002c0080d59814450903541001019044034003d04100c824800314550341400302204c101d03000082c200160360312005000840b141c01c111000c0b00180e00118114120207440507040300404030a000034014201c81ca80c08100d00e024071840075090b403c01c00b0a8402c0c6140d8007900e0b0072043c1c0c2007022081e00f4400f9003030264951400340644041e079810003030005c001c10110b000c0e440840303400310042c0c4003210391034008450544010304920707003610403505c801e860b820081c440c000380030100800801400d4038201002e401e4500040c0340340180210340c40104085d980106045610219900d00092270500c4240260018590b10605100003880c03c502d0104018450b8024000e603003003260810219103a8850880d50b84a01b81100c01104280410304010011160840340d00503100a02c10001c5540328401c48405402005403 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 289474739 1250 289473489 289473491
    0x70b01140a090f06120f030318150b0d21021b0603011e0b04060207090c031413051f1a0a03020a0605030910020a02030d0606030606090308031b0a02030c06010504050f010b2803 77
    0x103004041d05445549e1a028a078a464940e410082c0c4490b06090107001e00c00400ca9140c410b4403400350346000e14818080d6210780c0c00414020007501c45511000d5490005025206450001c00070307400d0721400d102001c00c01082d680c5503a0030601380e400030030742150151500149a200201e612400b850141018101c6940245a01480c01550034188c0c0c1039243c00400340340c64905400d40103418003203c81e50210b42201d0740c144e51482407501d6860480400c81610040190750004168075110f90001078000034000f0700c42c4c0212401c0c10400100200710701c00251f0003141610100040c40c00344000c0c503170001c9880c06031543c070302810506409030380c031001c40316005807c0020030b510003500314464500a40001d01e8200601420160003130705030700d49400007804407440070000403a110884000d064103c01d01e8034000f0380b900e9907100c3c041d641c4e40003810800c020b40115400030a99080501ca42071182c004400520ba0b2646001c0818043c2d0344998404d54846009101111401d001a280154030342c00c1c50354 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 289475989 1250 289474739 289474763
    0xa0e03070b0c2802060304020120060709170106060e010c1403031314062e090c09080d030c0f0c0303091209080f06041110091a070b01140a090f0612 65
    0x603240901e0803051280c00d141c80a503d45100c05600c1d08000d69501560a0030110b4511001140c0d020746011031211803d0b10744155010001c0c001d84c050398940440d500c51214140d1196803030f003035500342c40482c0900c0d07000644004039140950b104d40c11518645002781d180d0740820800350f012900b10303030045a100343c54000c007110400420140c52801c2c3c0b0f901000d46c1c00b906050411046c00c0c0b2101103444104995100b880019054052600c40f0a1000744082003003009441400c44c00509644081e200e00140344c058865000c0036940640900b4559413100d5840b12442c4035581c40035100610040403d50170540e40e43c031340d100003c4825407001e801e600d07161101c0045501e04800c03640740100665544030303207400c18414480040c1c031482c10741c0ca06c0d9000310303000300d0207a0075140c0413201d0314080d501c4400d042c00b00800010080d41824000d000182c0103c00440340c9a8840c0e5806038100002107406811001d007008c00c112419041d1b0260301c0b0100380c9500403c8142ea104100e801c810a03050041d00c023510414 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 289477239 1250 289475989 289476013
    0x902180c0705161419060e010e13060911030f06010c080403061409010c0203040609141818070906030503030f04030e0a060210060915090e1e0a0209010501080c0a0e03070b0c 76
    0x810080c90348800703c0e07500040074940f0100d159840c40758405c0c08180281d01800c7c4469038004d0541003000403000c0c1c00004020981b002e844081c155070701c00c0540e46440c0150009010a03242d0032a4070444900c0d00c043c20b117844890044032100410281982c40b4101880040000703006402450205401468208180e082180c4442d00311070310844941d056600401040000733641000501040b1050038040b80c003081040300104025841c44d41c008480c202101c02002084e41c5a810068a2524800102d4608a4444c0c0804040303e405000181039948240f00062601410710840c6078080d1017071900d0380e4038ac41c131030020a207281e40542010002d600103840f03911010203288150320081c0f06022040c015941090b400c051100000c0c010408081c3e1a44040403495600f0807a41c1382e40341d0300d6882100088520a0415100d00b80c0c2e1030304a100e03001c1180000b032198032881c000360080316040c003564030703041410005982c096007261a964050144590011b840c0303032540060040c03801442c01a200383e031143d03 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 289478489 1250 289477239 289477259
    0x9170a030b04090605090c061806030411060c0d170712020901020f0d020f1606050f0c013b1506040b0d050706030c140301060c0609080d0f0605040605040902180c070516 74
    0x2220301074000c11040c06034a1212704030448503080c0e480191034841d56a00d903400d00169100c00d03810050b800050000350070421503000540501c1410300da03603900007210481c1950000e100d2055840c800010300300030700c640380804142d008160710941401210034030b1f00889148e608010319030340c03d00050b130448010010b13040e10602002250b1041600c280a4180c14010003404034002c504074411408000314050180d42c409521802507400343c2e628411801d03010911004c20302d45014052941d62410a29040000c080024804040142002c1c4891142c1d245024032006180d0800406c2e40400784030030303880100d80140501c030060702865130b0200f00403960b070700701400c201c5122041c42c0c1c40080400040020036486104096900da21a0022901000e1810000c0c024080c000c0440c2c801442e05a10502551050740150101c1c1c070142c409119040d83c46003040200e501d1070034081d4028042c00c68080e051340c1100926507008040301ca181f41802401d4864600e055000308681c082210030304002d20100da04 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 289479739 1250 289478489 289478503
    0x315240b031b0705121605030f03040c08010207020f13020706050108010f0c081e04030525050c19050909210705010621140705130603060b0409170a030b0409060509 72
    0x4070042c1c0d260000f207a903074a5403103480c0a014012908041850300c403a40324550650100d0342c0010803251148814030100f03070540d0003900e040b00c0c3d07020300e0480042c4468040c003d964280390003d000d00c1c0c16059010500c07241c1800c0c00669641c4590800901c40000c00ca40300f07040c0039110b010000185a0504030945007200c0c03000c00d4440503c580c036010440111106d2809889003205805055001d84480ca0150362501a03c40c5400c04940002109450003041c0f0074094190303401030381103400750203840c0c0c01d214044012401002d44000c0c0c1c40f8060105003841c1003e2a0404045411a009948009412020300f90f0289180c1c01403c0005000380074054240a440e01602071070305c084030300305018001c000340b00044001c02800c2940615401e102158280700c0c0c4e00052030042c29914070703001c50300b001000818550000301c84d128a49400c0080c10304083c03194140d015801440e150038400e9005c0b441d681604040c005004140c2c1307a285c00e544036142c6005204c80303d40f103000301140d941020240c0314100f0031 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 289480989 1250 289479739 289479781
    0x306040506030c130b04021e07020a09110403110a03050304030b04210e0909012c010e01020307050703110c061803100c0801051c0813050a09060315240b03 68
    0x12200034209a5603585128540e2081d03080c2030300040c9405c902d000300d40640903503c1811a84030201c2e0880650042c1c0c40010150b00f482103c1c0304140e140ca4114410450f00300321041d413028501403000703000052000070f1002000c0d01c010045262650385e030380c03040c1c0b03140e005800c111481c459402c00e0004000c03040c194100c003003400c9200202c28410101d8001d2030360810842841c420881d0300b0105021180c02c1d84800718076000345201000b460b010601e242d1020440c511a11785c590310b05a0006100c8030103100360b900030650781e03507803624100d160784085601c4525100034500b035000c0e500c00e00c105a40c0d1480100381d165858041e490011040e0420035041154415118084500f060000f03a4141e900040c01030640e07070100c0702003800b040314086507800c40c0e0b007000009244c4000050560b801ea280052064200c5504075010001603864a9030701d402d4500500c0002d064049100c4240740510440d003280c43c0b0889103d06a5041800d00010010802070300e03840401340c12000070510286c4003104c090021009 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 289482239 1250 289480989 289480993
    0x603020a060f050702010c1406070e01020c040b0319030908010501031505011d06090c0d090c1a0406090902030a020f07060b01080c120c07020f0d0302070e1003110103090203010204050d0503030604050603 89
    0x1140d0400b016120b880380000007810440305990650800c2608010605000c81060454490f407031310351130103440e50030380c0f00903180944103104007000d00d407400c2d02500e0700710032020b40500119071003140c1801181541000072018000d4603000481e0002c0700748030359402180036030a8005240f01502c402821150185c00c501d42a480d400c804d0700b03401c4e0303a05a03030035000041510325070702c0c642d20740c03c0c4491903004d000384040c2443c0c140020102805030415014080d02d24444020b41803081d8103084139018031561041c400851003180e000c01900b401a4080c561096202501514200b00c40121904c00ea02c070039005c0b00e05650700c6810030001d5921094182d44061450311b22442c010700681c1310200780e5402030000c224688006080811900c40c0040d4003003400c40940080c0c4080340500e40603440345110300441840088890002d0280014801d96a007100d41044e200b4000d0010076004601420340c08030142d070503640800c0002640c1d00d510542d03080d458010381c003458881c2800000c05c0155003014159034031075 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 289483489 1250 289482239 289482257
    0x9070804150209061603050408190c14090c09010c020d06020a0e030d05041e0306050903180d021e0109050316092a05030a090c0b30010b0f19030603020a06 68
    0x5031620000c80381700800c01401010000c03114a011901486640c204034000e00038044410440f045d8008009442403013860b0812885490b482c0c103494802404242e141d100907100040b1360003801002c014540d104040c90540005181900807030f03102a4480c070b040300e40541c0003c2d02c101c06a805650030050380c904601808078941c16580c02409805903000380890f0002112a5100c0c032003d4041c2e140c01183c0c002c0b400c2c4400e18000011329202c0d080054140c0d2280c0110003014181e16003400d4400c03010358003c005000420305100b86507451000c80704401e0500500203000f04069600b000400354080c01c032817104131031900300010281520b0034080341c1e139076a01401000e07803081d1300200c1da40f40010304149803a540b240d5440c40420050807440b04050400f60074504040f84400890000708080460004a060314280c0048440301c0720407040d1a60000303241e558014401da1400c5001811134031403211981e030905d4001880c1002d01c0301030105a00203c0c0d41da15040086040c8122250001e1045040201e00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 289484739 1250 289483489 289483507
    0xc031805010e120705041a190506030c16050114060f0a0e0103030e0a0b0a050702151e030a151725050f0112020307030c140903190c05090708041502 65
    0x1e01e05240c0d00b22403158119020b6000301c1502000104010100108140300c031240c003492070048042d9103448207000b15031101500b0301d03980020b40701d04100c1d84050100c601e036544050792044590450841d8800d080b000b01086408240240201e20359440c0042004200781002c808203d190302c1c604040070301500d00c0c08400c1107450400004a0704607a01420080c1c91015108009a036503035880c1c000301503800740450910030030780d44000507100e2a80300340c0d1401e10040c03c2c3c41d1000c850740504481d8020040c04d25103130f112001c2203c2c000d50f82103030b07181c100442c0c0410050a803200340e03046900180c2e08421701d0385008400840810041d08045a1520a10010ba031111050b184103042030042c42d010f10300c80304c0102c81c00c0e4410b544564582021040854603418140342c0140684000fa1310540010140c0c02907040c4002c1240441c0c110b00c000130b0050031905500340c840b034485000c41c90140c8141401c19000101626134040347c0b40b107001b840e41e40f10900d04e402d00c0e007007803114165200c0000300742c41404003400e = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 289485989 1250 289484739 289484747
    0xd0c180b010215090a050303010305070f090504051f1104091a01050316030b1503011403073f050a03200106060914150408010b01030e0f031222030c03180501 69
    0x2051603c010301c9a03d2a640d1015440c540604100010114440000000140400800c00d242581d40d20000c0c10200d5903a0810b803c2602d2040d540039040350400d21859482444080c5106500c0f5441c050118813034003151001a901c0d0820340c0402c0c0c065445078000410615806a150792150003424200c0c1913040049504000d400c401d0b07140c809043c0c0c1c0303081ca0019075507000841d09505448509107540ca68445559403440701890040d54013903c64454003142014502c1d0580d00c02510309070400c80c0003c038940c04c0c1031400f802800d41c0d0ba4a16031108806020860501c03081091354065114a9110140c004090900d207400c000d103082140d00d03140062000a500c1913002d01280e2505006c07412014543e000a540b142ca9000c24030034082000074001020b00047d000741c84900703000d807020003110b02100e118a490f1407a4440d4010f194004200310400e4403031024a03250041e003100c141d07040d41c603c074603080400180c86100940104080503441801c00d5804480e2041282c41e03040f41c48841e924100000c0c1c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 289487239 1250 289485989 289486003
    0xf060b070b0a0f02070609110907080c0a0302040807030b19020f070b060303090a290c1c05121311060702010804030e060d091b0605030114100c020d0c180b0102 70
    0x80c050a034081c0407030254070040d00600c82c848901c040071503450060340f5118000300302c0c07450308403101141c0c224200d00302c0c980341140500c160130b02d0300c8440d0301d07030f40321445018194009480340c020300d07070700744400f01744a1410003d08001d0340c400c0c00701c0b44c407034100426407010210f4402104040306004109040c0b03844181002c0d12500c50f0b2050a101c0603407076400c0001e046004510410360004001c200c0010f140000f54022628075a1200b1070000d1180c0418141102d403056901d00030a6a012092540b03044070100304590601c0e4452404038240700c000300b03980c0d11282e401c0d44c0d10444400c44a541e541032000101c04203c10f503004449203450500c0300c3c0c0c00680002c500500240a00c40e107414441e2180d20b43c04200c4604c80d0070040e0130440c8044520b847c500301e007800c1c4000240740d903000d2400b1940078044c1d000c480c1615a034131410008101c15008100d450118011103c08100f000d29814005032030b003c00e820303c41d034451140c4902160500c5000381401079160140125182400b50010031039030003050341 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 289488489 1250 289487239 289487243
    0x210a050a05070209130308070203160b130804080115090902090a1509061d07090e131506060519051303020d050106030f0b09010c14030112030e030d0c0201030f060b07 73
    0x600c0d1112500c16040c0da040c001c02e00040d4200070781d0307402c01040c40900080e24101a02c0b070788819030302e80c403204001c0f0380d03900600039419106240600c1f020040f407140c600c19030380540c0920044d410b200b034507541c10440e90071a9000280580d11780d510210505c81d079507030f254082c1424241c00c000100f80e035000986089005132401c408682c3e18103500544048101c0300328040c110040c0140304090f030700c40c410310034403803001ca42c4401e03401d50802241c3c10034400d030020f50880700820f80b807003100d843d440090403244070b0075801250030b00809849010754003401e004820080081d5241d03d2f4640c12a640b4607184055058440d90410200708070010350380c0c0d801c0c00b005041d6501540d50840140f018a8071500402c00d5410141070150401f2001c4104564040203500c5031441800038001d200076506c041e10242140d1035881c500510500050122244190307500700540e001c2c0c60500310103c00000441c0c207083c01d0071100340001d60947d913030b8400d40d6010300454000341018541041014a440d40811007070241c1c03600 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 289489739 1250 289488489 289488497
    0x608011a0d15030203011a03070506090307061b150b030f0d080112030905041103100b0a02070317120403020c0411130909030507050615040608010b1008060d23210a 72
    0xb5003004960411a1005942e0140007048800e107850118050328a60080342c40c42485070183c0400c56040400c00d441c0788540c0a130080c200681000410b40d00300c0041000545544605000030002c0f428003202e1028000c00000c002480c007120030181810715100741844801540000303400311045621441150444900400e451601e0206180885508106500403a403103820b099000c0c95034074140d4004e50060042c035642e968500c1d513030809401140280300304c03040903030440d00b000c0000c00da000c3e04c2c0c0ea0802400418961511b96900740716005030034203035002d0300140c1c4080c6c41000385003464802d00480c0710a000b401420040101047d86071f070821806205815a04c4101c07400806002d07078140c41c24560702c00c0984100d4a811005140c0e03004a00402900ca14201140018941c006104880100c0c2000d441016801d9180f40c00f42d411a2010385425000451490311201103a014007520460700348800c198094508200c20390303841c4c047c0080c0481c511040440164100307803002d20890b0181452410 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 289490989 1250 289489739 289489751
    0x90c0c060403110c03011e0501080a0302030906160828030b03120d110a020f0c0109050d0b090c0d0609020f0103050f0117011d0d0f050301140d0f0f0c0608011a0d 71
    0x1c0c20701c0c04d000c200f00c1a981c0541c2010255800301014041e814855664400100003903a81e9141c160368401c40d00c003016025070030400c4141110309003100200401000c02c0400460001181c0e40c0d40c440e54000000414a50030b030140e4003070304140508406c04500260701d002d000c5a820f1500207500d0300d0f880f080c6030781909000901080c00d00003a4201038281c51000b80702c0c0341c8500d48076101a403599440b040a001034020050f01c5403840d030144000c0c1c4203480010b0074041d4504490344e904a20020007400d0107546100d10034402055a541c2c81041001911448005c100e501152040c440d41c414400300443c10700d81400100802d1201d860342c8a41121000c000040c0c0d00381074000410700504c00c802c0d002e002050101c9841e0914400000c504840681650321801d05003c010310840346404280107004c0000c0c400f4034450000c0ca410f0200d44800c03405020030038003a846030b03951100c0600030b9860890700c08801c520100314072504441c849004104c0f1030202c4208075a0f280203e0030314801d078991a12095941c034 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 289492239 1250 289490989 289491017
    0x5010f05130b060408060403080a021e130302040c0f11030901050306131b17071103191701121b14040c0309052a010c020d03030209030a1709090c0c060403 68
    0x20300005042a0042d050f640d0b0345807548005500c03200c00b00ca080d004101d0610102c3e0400711184212400c040384150700c04600c402a0041140c1c5902c0001c00c1c00c2c0400d5442c1000c40540e60340d216000f424040c0380c4076001146c1040002422901028600401c55001400404000e036001001c0345e600500481c2c40c0c02ca8188105044070040403080d044c0048a00342e9501d2134101904044940360000324103c40314036691ba01e150855075488111b0302a8904e41083c4088078030409030090301100310044d418947d400c1c0052014002e00c07001c09a00255000745a003081d0010320071221400c0e203000c0d01500300342c400a0705088000c079032501928075142c0a00c2c0d480f200c15507034503c81d40c051407106a10409071581c0c4030b2001c0c030004100b00d01d03a00355501d80c9060854200c40c1c0d80901510240c103540070304041004242c41d10154005d412283d00700790540a41070382c07180001c41c40f1007200d0a160140701825100c10100d01804002e030790040005080781003c000240c1601e81c0004e100c0e0f0f0007a41032510510b011426 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 289493489 1250 289492239 289492241
    0x10e03070e100e0c0301030212010b0a0b0f04080f16080d1b06020f03070206240f04050a02120406060305010c05030415051b071401050903490b010206060405010f0513 73
    0x50344050303d4070702c20034188140208a6001141240d001700c1d9170b251b540480d0030b4154200c0b140d803994241d00600c100b204120980c200000b07466540d44000705076060941e903031012420640a503000d254035400c05054103000d00c000550326030181c00c200000b4007600003400d501a0103403294140d2458001d01400300c0c0d5080004503011640ca80301a413410a4490a02c031802964807002607602c00c088101b01c025103206c502540110f8040002c00420000040814405100c010140503207a81c240c0c130b408003c102c420b42e0011030400c1c0130b1445010001011480c6050080c2107940103410300c010401c0c01c20030310020070100e074420548807400e2540010070f500d50103184219060441440b040ba21000b0640c001442406a401610300c6410030082c0181c0c0d44007800a40c60b80304d80d0100c454400c0000c40304090300c01402d40c082001b0030820860012603803401804400b6079100690906a091b100c00c42d4400650b4180025030700800309840601095041406808120f182c2d03019003802950304010242c801c2c141 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 289494739 1250 289493489 289493521
    0xf0b010614121f0e0601230906030a0b04060303050a0f0f0801050613030204050703020706150b031303020120040303030b041e020901121406120d0206130f140303010f05010e03070e 79
    0x40f01606100c043da51414400103443c111101408140c4013040018405040d4902401c0c0040814025141c001c03c1010414031340c0014110402c92a603a80f804100c5880741d21480740910300940702c207500c030f81c90340fa0b000f04446101c50324081080f400a031405841b0b41c103c03070020b06541040340c00e03540b9860841d210000342591640080d600604113401e120349141c01d98000c0c200c843c02480c081c040b110720070004000c80d402c039101c0c0c5804030104000050205030044104040b041c403c0c070003c60030341545011401c0304040c40040b0075010400050400c101740c0c040c4038030004000c00b96810b00c800c410900c041070415094100080880742c00040f241103d0380300c0e050025814410300e1040120000800111a020740d080314114080d18146500c1008000d0001d03441c0e141c403500c1d500400c403942c1d8940b8441c0110b0035a000440d44405540203410004a4161403100d100c54068001c685943c0f401d907040c0c0301a20298440c60500c01d44d804092910380b00030815600b030380c0e00c036010078410351103000c1c001c8a4151 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 289495989 1250 289494739 289494781
    0x1d06120c0108010506031e01270b0904111f0228050a062409020702120a200f130b0306060f0d06021e180102280f02011101090f0b01061412 61
    0x10002140d00340b903500c83d0600500c120010709c000320100703484160413501001295980714010000280000e03203080c4120960042c06081290303032424500c0140e007001e0394000381402581007031001d1114810180d007206802449a644086907888079108c1e0f607203034607911001030002da4685550190841c1c200001d0b00460080c0300030400929903400d03100d002900803980492250581107030340e1810101c0001d60240403600a51400809a6280e0a6100300400119040e420112540c081c21150b034500344041c0b0a070100c0e440102d1340b002402c042600b0100000c01c0c1e1445140746805415081c1c84404a10401503400200141ea6030070014030011003020900d5540740d01c1c880000c100ca901d02c4900406008000280c00b155000380c807101400c3d00b00d20b42c1c9800c0c281e943c0440c04d04c02c40414049807103d02c0b0640181060b4407541c80d46003101c0d0a4404800b002d4460305c0b88230300080200b110300b03031941340100300c580b5262aa0312440d50300003003a0f01c1403443d410304083d030300e001241002c4a40d143c00e0340400 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 289497239 1250 289495989 289496041
    0x60a03030c060e1e0f060c13090b04062607092007020a05030a03020f010e010507050f0d09020604090c1d030607110c030d030e010506011806050a05041d06120c010801050603 76
    0x1803101407040e903135117000803041280da014000100315411100320585403080018042c040350381d402c006a0301d00078414040215803041d20340500145a17441b2140d041500080703900780c500203500469509240c05501d902031130f0f00314540007078822044401d002086121818048140e0f40750054000a1005c80303450700040d605000304500c140030103030005060369002075070728028021205203003400d500301c4004442410101d0410011010002c2e4400002d1203141116400003c594845c0d80200343c0325086600184805984c582c607954105400805818110101c0202024244651390110f600c0e40b0340a0180014802c804444010900003408089942d40000d011660300303004c801d01c014040e003002c50b41090303154604404a0015403140c1c111104000595039040841464000100c0b2194400103450080110500c804101202144100c41700900c05000030310b454201001001000003060300c000300c0d650720400003030b006a6086a00303070307044610440b19240c80f55202c1c401d101980030100d403140c03104 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 289498489 1250 289497239 289497283
    0xc0a020301050726010e01090c050d0c0504090f060b07020603090a06050703202701091a030103051504050c060d090822150e090709031502030708060a03030c060e 71
    0x1644c0c2c042e0b0203000d4042007081601d0103040c4c424422066060a002d001d2039084003900520070f1180c1c98000030010f400a1070a1072034012030030040e82c01c4814982d950b00000714000360811406100e030140200d100d034942d4013086113501d02100380203648a02d4000a0261b1070100014662580c103000380c81076075800c8401800382c3e1a1080c8010001c2c9640c50170701e01c80c218a8030200c041070b2441000d03503a48070f1285184011500340185507141a01100c04420304209090324045842c807121841c451122002f004010740365415442c01d80e00703145160360304000410400007000041580010840490780303013030702e201d6510500b400d1024007901038018068500e01c000070303c0c106003102c101100030301c8038924800494007980394808103201000c001002c0000800e80c42055200d1328220010b240c01004608000d200c0a44da95100e505083c00704603203064855004c02006607a0741c00c403995691120b01150f00c0c24020b0b0031950090b11510b00a00302804641d540c1c481c1200f0000104000703003202d44211041c28003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 289499739 1250 289498489 289498501
    0xc0a030309021e0102061305160303020304211e080708220911090405130b010320010c0b13060605040e010905010e03040503070b0a03110307082d010504020c0a02030105 74
    0x90110001c0c01c81c000c0050000080d5002e240070740e40c610600059001e4940340d12200044000d11410030340c2a07645001e101c6000008422405026008512030b4000e95180d602d0a2884d405e0341c00741d039410f24810340080000b0702c00a151074500032308546141440c3d00c804c070b80b10b081144543c01110340c01801c00c40e0000d4407441c000c165500d01e0031035550b401c60f5280001c0e21101c1040076178032a0a40e02034007a500b8400c004262400b6000203501030345105070b0440b00c44064490160034982a4410b50700e440030741e80c92419459029900b504500400e0038259601c5000d6650441907000040c00c5200b490344003036100d82003000b1500038400070b2400400602090360600c1250f4001c00620004695562903c0510100c481002c010760341201c50050207050030a00e80404020140d000b004041c1c10035590380006038280c0c0d5564007540c01303000595500003c0340351002941c118141008100da04820350b50b4100b9000001807602c10b0f06440045d174015807207a00650b0564509081d03000001c1d455402c003410040 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 289500989 1250 289499739 289499741
    0x907050a122a0c020108060f010c150501030308010b2805090312040609090b09010e060613080d091d0a0e151e0c03070804020f0609040c0f020601090b031906020c0a0303 74
    0x200005040c03075821021240c0800aa43d40d5020003002408103078410b0006203203280010b100d01c500b40040c100050410001e954441903416507240e0150301599600040c818075510154481c050308220304118500303444424200c990381c82d40c0ba83c0424940780741e262407075018411015142600c0000d022160100c1d41c00c0e45140450f000f9002c4d500004510003000140a481d41c0102c0746101e902401d500100c0e402c205114034006001408650010020040721008155003071002000740078880c060044400c0e107150042c107820117035100581c080f044000c4901a42d4410090640189600341d0000398107400b850018203000c1205002c044080e03c040030442d00348581d207511181c1045040c010100d40c0d88146541c0d140340002d55600c030001d01004002001401e11a8059011030001480541000d02c2540040d00340c41540844100103a2280755045001e07404100007809401c0c0303400180606030350b52000c2991030403a110309098021409040c8c074184101d9504646501c1d80c0001a290312204904000d4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 289502239 1250 289500989 289501031
    0x1507110f010c0f030c051801140304050307060f02030c0306040b01091208031602070f030f0204150b0901032708030604061d07020f0114011715091b0f0907050a12 71
    0x902080e0354a140f14021407103072050b0103600c1e41c1038880c60b05281480c1e22801404258403d0541400800321a22038840c540001641c0b1861042004654030103c515000098440543d60407550b94014401d12051960040a6950100049da000079040e201640122000c0015901004210720003120390001d0026420095200d00f01d0402062601d00f0403840480c0c0c0c1d0b10f00b521403101c2148078070b941403000400c0c0100c0500c00d00d00051012480e002e0101c19840d81142c0c6903c00c00c50100d0004400b1103c0d6014007802d00304480d00c1800085000d0020740c200c0003520b00c48401080804000000781490350395500200282c114040d0001e0124102046418041e005461203c05445000140c0481d810140030f5400c1d410303400c0d480c0e604e0b140d1070a50500050300b5142c0541c0103030b01032501d000302a41c4030340c81110700c241c1550004155003000c0410000281c1d0b42511094003421103080b0011842c2c40d10a2a03075000502442c03c181e4480c0416070171954050020901264503041c0404079552105004600c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 289503489 1250 289502239 289502261
    0x2b1703160219080f0d06081507080f0610030f0216060e100504080a0c020301020c0a030e1507390311040507021504020118030c090e0f0d021507110f01 66
    0x22000c081880990221080400b00000d203640c8003080303e6020010382d000030b403401c1e0700381c60008625180c40b41d0015051203184510000b840c0b5940e000c108010764004615500841c071040c0344041e43c01d1001c0450500e80760181c2003002e0545502060070010304da9030440d0300280c00c400300c0c54907500d4145450030113400609080f40692142c8202905010224480e1501807a4401210f41c034004080109403025081e441701a07070315560030321012106240c14046562403510039a0b0b00440088464100007104500c500207400145003070203540f000510324101d4542c400c842001002d4844040300300e0240d42d0040403845004030011203800020405044440020507000f12402e02140d655803501b03d960304440743c03d005290a103880440c001d940a501c050b0314540c9806444004a61203844a040b418120b51100036003030b5941107107465100c0c09000b0b003000c1c15803500140c03000c2001400000d41d1030f00b100b5014481d0303c0402d004501d00c14000c0080ca803c2042c0e03803043c0d0360b0f15101e02007828001c0c180e00c800 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 289504739 1250 289503489 289503493
    0xe0705040606050a0e0d030e0d050606010f02010204030506060f0a080f0a050c010c031d03010204080115150203030f01030312090b01120212010b0607031101020f0c07030606052b17031602 82
    0x1c04103480e030107803041e50f5403d4100d60b5440010034100d0100844500000c8042d42400b01c50280119251640380081c10101c0c011350060000c0e04003000010814440b0b40004c2085920600042c000190041825504102c044800010b40385219001074080e0301c00340e020b03900e24400d50892125480340451440401c40c01102030750100b200e10001911b820141e03503001000500f01044031030708141c581142c0e10000101500043c1440c0e10b43e00c6203070844041c4032030809004003680d0200000c1406d60744181b503410b6248061030941c117190200c3c180340c40c81804001c041c02101e50381d001c80369134968055444075802001c41000c0d0b507903507401c00540e910fa100040c3d00850740d0345e440044803003050050110900c4003030440d514100c81c5840445e040030704e18203e810a0354007001031441115240e00030b0306c05041800060540d061851808004132000d951115008502100390b001584400606101001d9141814101003801c1480c16800c8000e44840402d2420000706c01e10000102c4451740708840c45454007 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 289505989 1250 289504739 289504751
    0xf03050105010504121202150907030507080d090e0712150e06040603021c0f020d081903060807030807031701091a03120906130806070c060609020a0905060f07060e070504 75
    0x110f070284210f00500700200810310500000548100a4544440c25841a01c0c1d07118881c00203440c810703034280c0300b54603694404a01481440f200384000302c01010700d0002840d040004100281c01c0403039522a120425200c40d0001d40d503070b03005040c031004485074004100718422840300c031003030305255901907054201202030005400782020f2284006032500204211140c440403000c4107050400c400c801c4a0303040c050070072240161201ca03401c1c016140300f20680d81e00ca00c900c1d410125101296041c44080500b040c8040010650200341303202940e0f088840280d4903199400c043c0c546100c004808800c8940311000002e440c07200e03501100380f074490700481e03001c1d1144001c105540d6040c40080074190798410045071f00903103000c100074440d00d1600703400740c40ea40c1d03550b039241c500b411021030720f0b91b0200701c07880046010800c031407045074041c05540d803085050121620000304120024011325004000010f0b00035200901301c0181c0b05a181d114205014000921089584401082c419103009604003a = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 289507239 1250 289505989 289505999
    0x906010f060c050a02040f0603080d060504050906040f0b0c041805010503070803130504020c010b0d0f02010314010e070809010b0d0f050105130312020f071e1a06062d0a0f030501 78
    0x100702c030050768102c1c005041c500100c0c2c003080010000c070047d200707070190785940000020b0280f40c0682010f0300c460700000b402c24940002d20003035410003044203503a500810100800182000001c0c1503854100354120002c3e03440da50f6102040c41581c000603c45a41001014014452508010305030380c410790503244a40d075a40091070380e030b00402212074082082c0280612007410b059001e4100140c0d01800402c552030081d0100e956049849010b440e400603038050401996050f0040340c0c1c01000c1d0f001c07481e900d5031510075020026100a481c00c0100944000441c920240035082464441802481118042440d1a000fa83c0300d461160403a155405c05000500800346201e6682119405481d2078910000000001c1c4c000d5201128030125181c00340141c001041514550003004403a850200782007606509040b04c2c036004406e216854903010b241007191540f644401d035000b0407184032806c0e00410350712200010680d000310350480541e90100300c402110b54400c05140d6103900c1500c3c00c202690300d030 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 289508489 1250 289507239 289507247
    0x302071e020a1a04051e0901060210140105011209020409020a0803091203040b090d0503071b330e04090b10030c080f0d08130b16020c030f1903020f060906010f06 71
    0x5644103100e48030f000d00c4100b0171410500140c1404035040b500808150052000140f01007070301307801400041c1d101007800e00402c440c6106084042c00e2080f0000c0156140c40f00081400c000c528140700b541784c40341c200c0d000719103807034011700e200307035401041c0078405901c4400c0a0740d00d03000703104802e01c60180310924000e08035002c400c07607042d46d003000e040c0c500e41a2a0f800b8480f05900d01da0003240ca81c8010440300000c691685d4004841a501b002ca0342c80c6c0d98078203403c0c003965007403494280c0c0c403140304084c6c0719002545040344140c6000c0d02c0e0801c080c80058000000700107003802500035040034140b10400c40e64500c11400310083d02e1240b00312180300d54a80d0160b43c0d6920150502540d00d41c0100840c0807298040d40c5007aa0201c0308400d0011884c03c0c5d5a50707405400c0040d1a000d017071000c800080500349130103002c2c1c0d142e480700c15402030203000f45110030b46503103090711143d100700c120060030079406061003805048094450442281c145040000095603520001d21403500c210480b100c02180312482 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 289509739 1250 289508489 289508519
    0x303150409020f0d050304350102180f0a0806010e2d0109050414101a100504180b12030909070c05030315120709050a270609030302071e020a 62
    0x43c181600c0c00e82c0500030700c001000d03094002e88451009110004c4c80440360f400580b0074104c03007411105142090700c0c0074840a141c200004d404d5074011700481d0341c5203011030509401c4c0d4002f110300800b140c02000204040420f0794220f59000d0050078004a805010780314801e01880d9104480018810b01d0402851003011810300c07820003820311401000f4100d029081603400030700680e50484005d001c1c0c8466484c00b540005441000d40d2034000c0f10b50f01d00c1c0490804103030000241d0700c1d0300e210750080f0001885403103036000d20000c840305c108502c820161a58030a80e409500608510704220307841c1e2156070380390046001244280789241c0000c0c0c10038030481c05021115030050040d41161100c0d14416004102c0d01000394006840e040840d16880041008a0080108503000a81814041c0401c001c0c1c2d000301240c0d2009009044d11240c002c90842c401c8802941c1200c0006440422858101d0192007104030180c0809558500c01c0700c0088500340c44980307076100300d445d54442603442600c0703007076004 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 289510989 1250 289509739 289509743
    0xa02040602030414040b10080f15030304031b030602070312050a0911060309010b2701050604051804060b0a030b1e0709061b02060c07080d0302040b0901030c110a03020303150409 78
    0xc2c40b04010304e482000d50050610001800030441d5042d91011404100c0c01c0b000c03040000d03103400f0a00281108015086400803003c028284516100c4408a41e42e031183d4030000301004c083c0c80c0c5440e40d501c0008030400196521800c290741c0c0700181d04000b00405508070000140700e1404003c2440c41e6043e00c203074045680d100c1144507444e200ac031700308a41508010488003040d500c884070403640d5900c4034841036004008620000c04c10b044445c1c07110300450141c200c2402814204000e1025540303c40302d01001400c0026150400ea8691504a002e84a103000154105603020004403c2060b1405094402c1003510010710381c3c224060101d001e40e6a080e280704011508001051011501c24000500945410750500c20340320165030101c0d00c0d5903c81100001d4607041020188612102840b005c05135031a40d1a0540c20241088052030380f51080031803282c18185d41d00010700031580148400140000080142c5a01212904020391240c0c4104c500c0c280c1c1e500c2c3c0c0d24003500a0301d03051044001040d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 289512239 1250 289510989 289510993
    0xe03210105011d0616080a0e04060509060d0c08160e0c09010e2b0501021b060403090618030203030d0c03050711100509010e0f0c130e1906020904020c150a02040602 72
    0x2a000c010000c0c0d07029050800c184c014204100c080741c0320001189a0705220301c01c16003d692003060000c003c04d0b4440482103036100e00e003020030400c2940d40302e02080360045021655010310310454607104200e190158840030303c07070251031886242d40e0001b6000c101104c05005080070301d699404000380e598401d254070301e404141c000310100e219040031b18054204900e9140d14207000c40c00d0440c0c8100e003800d420401c03281d070f030340018020801c0a20399409803102a9907078018089805c00e980c0103420003245010381020030625801c40c403a82c18072822280025034001d002d90343d44130142441c00c0050006850306802082c2401c0108000501c240181c218804000c806050031801b030344001405440094080d50207907484254105244038280156800051000006c0488100d03290510003070100c5c801400b40700d00d1030f003c945c0013054030105183c6800711840c0c40c001440101c2d0700d8450000c3c02200901034219101158070b1080000000d501104802514020f41465844100c09401c0e4800da0003034000607 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 289513489 1250 289512239 289512257
    0x16120f021c0807031509110d0c0f0507030c020a0308030403020f0106051c02060c030d05160e04180b040f080f09040612030219030909110318010603120c02040f0e0321010501 76
    0x5910035031220320440c0c107401c41520411b13500d0800000390385032111040005003002800906c955514030405251100a0402800901030703041d0144c018040c1140c0075041c0420144c04408654415048801850303010720300540f2800c15007002503603400800300321b114644c6421004907451420707040320743c0c1006003454106078600140c4d0034030500713802030205201144420b000d0307440f0030016405068421008009120f000c50a503610007002d42004901c81d50046190075550400c804101c1a000180361700320842c68220340310f03845c11000415000784094800b810104610103e07007403000040001900440d018018141c030b6000400440310726000040250b0711440499007010071a2000441050180c01c4c44c00ca10f5584007981d006440d041042c200c04554000700704000d840e08003c010240720380c1d28000700f208905554035588070040d1220444144480c40000b0b02c115685d641000c400c600403220148543d18070f0340461950b0f80c00c8000162000c0d45d044a288586010044006049031016940d00401d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 289514739 1250 289513489 289513501
    0x61311120709020a0908010603060b0310110d05040302031b0f010b120703120c080d090314091503090c04091a012909041103070206040b090c060f16120f021c08 70
    0xb5800480b480003800088100000d0021b020310511b00210701412010400d0300d0040c08150820382100b140036880c41c40c02c00490601d0081c03e05580000c08407420000c1c1a0315141000c1c1c0c59809045200c480b07840500000040206021403008056801e01e8000d00500c86844104425214002c5000e110369012207c01c001141c00c0e4468110603e84a090180d0b404440b0b44444185902102d07511003840d0300c5034a18000c16034000403010581903036246c803605250403040020710741e4070340701f00301c0c0b0700c502000c00410a407500c14410b00100d003034020000c10444400c1d2a1003100c07580318008142d251081c6500000319954038a0400018850004c020040300410307000000d02a0030501c103840c0c0056642400d2061006204021405242c0d01c2d0020055860646895140003200800c414682d0b04501f030700e481203440310010713030301001349042c061525a1072034540909842c08880002e4020706060071b0400f5100e0700314a4444010344560b00303a916200315911100c0068951900d550f001031040e40c00a00 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 289515989 1250 289514739 289514741
    0x1415130908071b06091d0a06030c06050a0e01050304240b1c021e060a0f0207270501061e050d0b031903320c1c0306210c05091305061311120709 63
    0x791007c2c0010340001e000340c0701c0c2c0380c220354400a500a040414400661160155002601214551001d1808614600c2c183c0d0381c201c8003480d02003484a095540b5500032000160640016101c8807000d08614a034060001000701c20030080070b8164018550184000310051030144d80400c81034014164901d492001c0c001101c080759480102c104600615402107a9425040b9a1b494519604803080c10f0481d07004840504640c0c040c0d0100050142c03400051100ca00f205030a481c00030f509051058440080700b14500140641801142e4140135402c5103d40140301381e0107501c21103020341e84800000030202c82d48102c180d40c1300d00281039404442d0489008a1000000f03100c0d13640840241e035040e00740300400725003604004280e203022903102ca005002d0f44007d0814081c10386560700060074071001588404280c2985401140e015880303100c0041c1d107442c1c0300c540c0004100d6111b401c07190585002d00701c2c2c10041411a5040310b00411003a281c0708189804481c024040a02c0400b6200c8686040b003008 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 289517239 1250 289515989 289515991
    0x30201050f0c0705030a062408120a02030c0109080a020d03090b010902220f05030d0c150b01020708060f0709050f0f040e0a0c08101415130908071b06091d 68
    0x28902e8828003502180ba074070240503119040c1d03c1000003061720401d0350003200a00c2a80d0f91a6500000e20748010054a080001c150340300e4088100f0440da2004501c0c412404e42c81240b14081440d800c080080042260120041000c68450380c02c0d50300c1001045000c800303882d140c90000c0e1651802c1401800000c0742c0da4001c2003201104101c0b610455401a0505140701b101c0e07200d100f071248148420007084c1014441160505010714141441c2c510595640000001c00c8015180580d0303102881c540c580d00801c40c2d40054005079049404a1130489a9050a40000c13a000e000041c1415070008084c2404140c6c211103450040084000e0114a42031200800081c900c01e0440d2107480840e00110300083c00880c0030344580c00250024800304841d14090b0b5600c02c0215900e0403542042000203418540ca000003960100c48030b88158031103c0815000d00030000010307102060001d54242045410701c0c400c0c07019481d2140f00207030641c0e50b43c800c1e0758029052150f4006040718010984042c11108106 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 289518489 1250 289517239 289517257
    0x11808061f0f051e13090302120f04090b010c0206030103061a040612060c031d0a0501050c030907030b04020102070b0f07151a0904150c1205090a0f03030e0c10050406030b0901030201050f 82
    0x14130708031190400103040001000a010b00180e50f80701003000b8140e051101500c422440384540e0f140c0743c03079071106010520407845840c50066039142c0380f6020340c0c41100320b21421900200081c2d01c0356128148900280302c0301c2c185004400100e00480741c9420f103405001d040342e41c5158585c4003145c5940701c21010f01190001034003010368401d05101c2c0000f80c1808c0500c0d00104400034243c1e480c0618100d400c403030015000d59030446061007000403106001840b00c05070b03680000729460980711840103030f241c1203203600800c40c1e2034030100b6020101c117130805c00b4003134490242c0310120f2020074800b0b10000b19800c0d220201100400e001160301203051034009140c0041c07180145031a88032000340c1340030403910301c0542c2034001038440d49420388014540c01415000540e400241c440e03800c5a07580c2c12500400700030b008061544549030101168814040c9202c03a0307030f014101e02c1184003e000001c002d075125019140211b494210000d019040400e0780c0d1f81641d03030603110549400c441000100d0660000000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 289519739 1250 289518489 289518529
    0x40c06030f0b030f0c04140f0610020a0b1620060a1508031305011e05030708090c040905030a021002030108030307051e0d060e0610020a02010e011808061f0f05 70
    0x542c045807000c0002404510580c006829000003560400056882100c01a10195200014401c02d1070031601c410f50000750481d49004240300d415800d034104900d810300644200000310802c064040c9151320007000c2400b0f5a900030f82c62142c0410104065001c8194421941c007180020b10041c031035622214480441207130101003e640e0b0f003095403440d44800206040d00514490801041d608810440301000d00c40ca120608481c03001e000402c03500000b0030000801c440c810120f010f007001840f2040c850000a8800d00240001e4104140c4d039900c070240800c0144591004800c0c08100c0f4400e070ba06076441c64020710315680f100310f002c07140780d0132218000248442c40c1103000c83c5400d11200801480d05541c00110f006442c150444c0c0394044000e10042c000c0360107400d60443d00e41d01041440c495030742400d100c240007004500407500081c19180c03050342e400307405401040d0780300d0004d01284141c040d01740b500fa454452402d40820242c01d4071448883c00c40c404c006200074900403280e1228031900303401c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 289520989 1250 289519739 289519751
    0x3041403360904080909010b12060d02040b1305041506030f02060918010f050f0d050d110115082802150a02210c1b010c02040f1103040312050f040c06030f 68
    0xc00a14410b600b034500b1680315000251104c0b181c1800c0300e030b80c0c0c010a00041c0150810083d9890000c140f0341c01400a44224031802e829011583d643c1c0c00040240406415280525007156075031000300030980d807e580407905000507442c0c0000c0382c0980e805480c1c1c80b110000000906030b00344200c94002d1031045a0058403101144846040303520394600a0828025101d0a20b140006101098019000b034600031402021580b005c11000100c0e424107200b51719140c0b000c50080e80840c0c0c0140351411007609a071490305800107050f10b00054204c800744032803004072460405855444c04012450500075041950305104105418400d0060b0020812500545281110810f00309000006880c02c03002c41c0100072842415604040181c05016890315040480d81100f960011300b43c00d545210081c865501c4519120121450b03400101e18241c031b240d102901c82c01e2524000e4a038030582d07400701060510303200000b450030180a24603030290740c1281902d07000900f0300d80d04030085c08240d01d000440701d403140 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 289522239 1250 289520989 289521097
    0xa0807180905010509061803030c03070e030c150a08010b07020307030b04033f061a0a02070b072102010c0c02041a03060a0e0d0206010503030a03050613020c0303041403 74
    0x2c050940714403171245c050040751400d00011a052101c20300002c0a6902c1441000048111101242e0b001882820113110001800d40040c0c038002e41c03405002d402c0036081c43c0c101004100c0c1ea0203844c4030202c81d1189600c41ea201e0300b80e0401c074000e200c00070707505500946003000420840d81071190418003e241c03d40403055000902203a0136961505050981e080d0080c1e2941d25404004a20b6500740a160500c2548c1c0b034524002c00041040321111541800040c000340203034001c002d0f1200074000116000e44401c0c0c541440d0584200588003084910b643c240115146032041c407d258255002c3c1d00d80c6640341da619002d01005000c40c20b10410000c0c0030240d6050195404c02401c1d214005280f000b003003041040011a050030050b030b00000956001070014810760b980402542c0c2c05200b98030703000605036100303000a51510040785040301460b10006440010b140c001c002144101d0044810b03400b9000c1c0c10f88040c1e41c910070340f81c281c0d0424241001d403030b080000410417540581a03404040f10310083c10 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 289523489 1250 289522239 289522241
    0x2309061504030b0c0414091513022109070e012102130e01050612012d1409070f0b041d1803131509051f0c0f0f0c050a080718090501 58
    0x103458011184d000420108000f208403420007040200a9030b840546007001214111b1910304011503500c603a014a40c3c002c24005140c0c140d442025143c80284d904043d0358803140304140c42540e5540d075500034402c0104400b178140b0f5260b8125121f1040d800c89200007042d940c0514404040c0480c2c0c8900d031800f1f10fa000d12030034028504004400c1000240320b050001c02c00001c00701d90f445510f004d0341401311003100380c3c14446104a08404c0d00c4039036405e501c4504560001030101c00e0340341c43c046800740d00f80030a8800000700c0703800352603941c0b140450039925000c1616180c00340740315038030f046c4a002e03610203540a8260300c00c0750091075160320b01c0940b081110b521800c607042800e035101c24040d40c003020040c503028100c610220781d04034103114640d203041a001c50844000c6400e00056400803164814156100d07002e08102d0b1034105500c1d0a80450518105000401100098804001710000860140b03400b01d0245c088400302802440303c5440c0250714140080000700102d1282e5403603910001098003 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 289524739 1250 289523489 289523491
    0x7050d0204060810350a0501060f0e091506060c0708011806050f0705030c03070c0f0b070e01090b0a030e0a020d080406080a0209031005060303070606030c2309061504030b 75
    0x5464020a41c6040c40c0d041c020001350341c0c00b601600512003400321074410350808558422141603000e070000c0c004151414500742c0c1d00c82c8000c00d80d45ca010300001d0300d91090039041080c1d6401c4500005980c65885080d0780d1540002c02d8001800514001f14480f4500b441c002e100c0036481d135003035a2040e41e44150f91800c4402e22a125140250000184c104003c1c50b8400c0540c040040c100c0d500c240d0425210041c1507002c001c001e80d262100000218815500641c0f884038500e0780035200024000452500c000c00c000b050307811384040355903140844411360103600e0103c10785a00c2030b20b071420107a9244086003e01100d0f4010100c501078280d030300d005a00c0d003000d10000c0d64043c6200a0f0340d85c0c6000303c020a0345000401c61101544180402000313503034081204241488102d40101e420303103c480000341075104500004245c0c80c40d081000081001078049501100d41c14051007a503141b0b580c80c84607408464020351030780030b000e0740b0000d00c540c64500300c10300c0c5000c406180c00e0704080d03e84da42c04d08000e030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 289525989 1250 289524739 289524749
    0x5090606032d1906030503161406072c18100801020c011d06100902130e131202121e07080403050c0411070b040609080c07030303050415020a051207050d0204 69
    0x80b008100700d03980d01001e03511201000d0301007084940e01d151501c036101e00034100701c1c1c01ea00000d01100b20900c0309482d50f0050802200c415100d65042840f000340c841100000300c41a540400c584c010910301c0440c43e04c603101100074100481004070700440071841e40c0020000c0081328889040400c01c20000d03c0589102150b650001408000c1340c410091000d203a40418030080e4004420004850741096600d01200c0c8200d001688034035040c080300c601d103202a0421601c6141e42070421002001541a0f100d07614085c030700300c1006244000c0200d881d02c82920f41c0d000748050400c081c042011042d100600164203c114160a0000e03584e41c1c050aa48240e105990542c00182030440501e481c1c1304a02140f115000d01ca8580111a510303e00201402003000d0b241950750218003060161145c1103c406120341c0041e2803c41d0f8407864060000c06080e101907942c1c05004651901c0c003500b6200303c4d60800c07080d031580c50a00581503482c00007000004c200a0030440c3c288000c9280038090b00292001d02 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 289527239 1250 289525989 289526071
    0xa0b210c101808060906090f0a0f05070506120f22080c0a0b01030311060c070c03020f040908160b0f06010503040b07170403050a0e011403060411130b21010509060603 73
    0x802c5c5117072110314040d0064440c810ba5000a420700c0c1d00150f0015902034900e5002c4148051794980d41032032414154a548865040b003c000764080e100d10060170f2503881103c11290704403c0d500c3c0c5040b1003c1905085440d44c0f8203502020802000c01c0b64200a4402c1c0142e4004a0f6031141040d034a544130060283d1040740403402080a00411030b44c180074050b401000551403900744030b46900d41f52102d001c0c510000c3c4c000d4001590100b21a15203401c414241900021055918100d01100c45050380c800c03182903d5902d00758020804c5980c04012141c02094165101070030340d25640c4030001c0c041c10140030301c010310844084080b001c03012006000d00c528043e40311b05851780e00c1010301501480d00c640b0b1090400541280401c80c0d010b01c8003e0f260800003d4800044c0111106010007880c4152481003010a00b03420000844900c40c03802031402c0b0124502000e040c1c000700405014a8000703008031540940700300001405420110040d552020003004039000b0903803c80c000600daa1100201310101c0d07 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 289528489 1250 289527239 289527241
    0x607110303040e04150c020d030f140c09041503150203070c06090305040e06060a270b07060207020a06140406030c05070f05010b10140306270a0b210c10180806 70
    0x4017105d00445450810624810b000d860309010000b5140c0d900702e441201815503940184410403680d521190b6000f40e150500e040c0350410142a20704c42c1c00c100700d01481542440052a011100c1852101c101e0b179014240038000c80c031001c18100650801416070080203610310001e00452290301170030207110702a499031680d40d424900c0c1d02680040c002c28042c000d0108015071300101d9406031034030080844038100d040c030b92030390031100d040e900c040e90388946007210740400d200c0180f000329401480c0c801d00c229242c2c00c5c000d6880c40107443e01c081c0c0c1100207100c0e02003031104010103400f81d0401450000742d45012407800782107503203000d9003078443d1000792039680d904e00342120075041c20116a40208058200074082003070040c5881424440100414007814800000d090b80d61500e624225803043e041d04261000d251400a00006007885120701b0305c03841000101c5041c02c1813444861000e08105805004001d2201c024002d045400c04c552804001d070150030500c42104000c042c44c09041030384060071407 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 289529739 1250 289528489 289528493
    0x1030c05030d030b030a060b01020f0f1c0201090c0308070c0b0412050d02010e100b0d0501050705030a180206040605090a050303040b0a1d0306040f030306031a0103050d0e09060607110303040e04 85
    0x50310030b0090510050514020314a20541d40000303140001c0c0f9403150000c82e080c009400100d041c40b10b5418110309501c42d0f603103015a000c0e008504003070301100d02da80d1060404003110049090700c2c000b410251001d0301c0401c060000c91010001096024026040e481e80c0c00c2c0c0e680c0300d0030502ea01640c01100c080d4845100d03c3d080200900040c14400711a100901803800348001840d20ba034450307920554565035864a50000c1d8441d82c085100654004000700322920740b4140c0541903900880309980024540b401c0300c0003403032560807000b4405401510850405081040a883d00c2e8440c0c440150300c00007006002a556800304000e2024000c2c400d022030311000400e50140c030300d1540cd01403103410054041021055180020415030164206080c81c00009a83c01c042d0000c00d81504040e16800080a90002030300441070340c1c90482c0c1c4201c049a0490744189001ca410f0000540c41c2d980c0002e0031404070b1428a042d2000e454528041c190103003100d6032460001e840d40e48503601115a00b5081e00402017 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 289530989 1250 289529739 289529743
    0x50703030c14032206050421110d050c1f0f0c1704020f0d080403030305010617040c1701060905240303030906010e070912150c0f02030f0a110601030c0503 68
    0x2185000d051520b00203107030400903000e43c00001c01201650701005825100a010316020380710f0303075130818404c00140c1440c4c1802058008020704126806103420318183c0021311818440c448506d580029080070201a503045030258096848040184a0b459507603030900d511458160003502602170008104c80c00c0300c2814291130313540101101f806950710002950b1101e440029904c5a4101d030102c2151070b2080c0087d108000c21000178125072404603011080640640c8881d040c1c5000d0744810012800c00c2d020502c6130a402c0b2402000c1c811414420400d0405000a82d41401d01c2d903400420b16544030340f928003c454080314181c0b240c41507280c507400e0704002c9030340b8192058402d4015515626052240541d00c0006100c1e81c0050050440002d001510522281010b0044103c201039080d0003130501754814070011245040311031403d14004815402540300c0844418640c0155040c141119516000764003c1c94200003444084484884015003d10246001c0c40c030650004030030b24141401d140c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 289532239 1250 289530989 289531001
    0xa0e310506010f050904020702011b0c08070b09010507061e0213050a06111902040209040e100f0531050f0a05070504020403111c0606090b090a0908070b0903130605070303 75
    0x90b040c41101460050309070303408422202485000e89003da9a8062880102c840d0309183d201c00410200c2505582c0401090304202c20441e40c15804445409440c1d01201c0403038402e00070000d001c079904025030400190f042c2c1206818560114890f10112401610801640e1024055120181c5400000d00082ca0000070f8440500002e242074404540c0d08203902e5035070010b00c2440c0d50381d640c251288808560321501150342d4002c01400601048103034001e4595180c0811207072144d01030801580030828516846003e201e04c524080654015102103011462540c803480100b070101c0c40041603078081401013101000f003034120b100501800c01c203805d1540c2800c6007604080d00ca40e0040004001140741c0e103050704200001110703010503074401c1c501e001c040001f203110028442d074101080020107480c030358801c01051800b0355008626951302690740d801c5888107a00144203d805002d5800070503502082181d0001000040306e282401c1c007004500c0065141d80428002030001070f6010405506014803 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 289533489 1250 289532239 289532251
    0x40c030b120309030d080a09020d080a2607030b030f03070b0f09070303081504020c01150906170a0f150e0304061d0307060f020a0b040f050105090706050a0e3105 71
    0x90b5040c40b0400300040e850303c02a0403050108000f01c00031500c1c005103940310042c01a4001e18032140740000d0310300108950400e101a03170100d148412000700800300c403220107854400d010f54100940d0f8850b0350590050a0810001d6090700c1200c03011450040e00f08024801c050040342140128a090300241503080801030549880350000c680c1040060b41155126400c20030700c0502000b954888404070f0000e00800f000400c01d07600700f00c00d2590030a0403100003403d490340c186061282e1916075464281060312038080300d03026480301410320085001d0380c1003904194882c00340c54401e000c09011090075201000c841c4a925040003508000711034110b209075681c0031a00c0108000d91600d140040d40f101c9061040c14107120040c26900e1110340700303100c4685005d5105407114182d04141c104443c48078070205048485610f0500030402e034010000e8100103c40307259807002d15020603850304640350135454113002e40280b002d003110308001c0160101c4c40030f03c507031101c250321500c8504400d50003516009010 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 289534739 1250 289533489 289533493
    0x6030d0c12030b0f04090b150a0501090302040209120709020a0f080103020102060f072006090d051c0f090807060209180105100c140307050a060f02030c0301050d030e040c030b12 78
    0x100c40009481500d0066510603181000203051000001040c1d41c071042d5030781c0c503a000740740401d220100f14495030100d005520407551a000d49400d00207004a100c110700a50380803406070242000185403d0f00200b0611070081d2800040040c0040302a01d00482a0000c090a5801140440642d0303407001e14201c55007c2450002035652442e00044d44035000602030143d04030303c0c6000501d055000d00410207150343c8100d81055090841002142c4840040d1071070b40032400fa15000380c5c60988100306894851404070711030202503114458241c001c01c20040020032850301c80460102003201e0902500d01c02d0b015540c056035500d210b80803c00075542c25010410070400d403000501c000d40765003041000002260500d02c60102c080d050205064410690b40d00c4540710000f080020094041b5030192100d208a406204400302e803081c95082c0e0200300c6202e804e1100c14001040117140805044061601a04124002034402c501040c1a120040840d401082d201d9200742620b0030130a240f14840d1050f080 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 289535989 1250 289534739 289534757
    0x3050c01090b04170a0b07020703031101090b0f071106010f030303050f0103120302070515041202060f06130908070515060f03010b06070204090c0b07050607030b010201180b090c150306030d 83
    0x303030007a00d001d940180c4d0400c3c8070044140708180e5017080400752040d0002c001440a180c6000300075513980e0389000131400180c01c000c903101402014007800d0003050380040e20710f00c075a80b240c0f82d00c40781850041940c0100641c0000040c003150043c80301c103000e0708007224a006c9031821814041c00f82c610240900100e030102e0340040000c02c402030f0030402101c105140150b91030010b801c0c1945004042d14100450188a0040c0020080328a84061218166400340c2e64599155111240c207071038101c0d4030642010050f1042c00041c010703503000481d4a4425078505007041d045803181e902d0306000c3c0c0c0801c180c050707400c5c0034400280741811800d03548101c02c4000f880019404008921527000d800390003802151549401020426407420460140c6000704441d03489203a1424400d54581064a510020914040b04144a03502c1030050841003c880c00003d4070145041e03484c61001032004000741c405016031495080103590300084210f0042c45040c40a845c1d040110406051110900420017840b003209 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 289537239 1250 289535989 289535999
    0x4030c0c0902090f0d0507090c050c011b0212030708010506070312020a080612010b030c0409021c050102091014190207050316030c0b040509010e0a021b030a021b0a0905060a0504020a050403050c0109 87
    0x509002a03402341c940104003440b109e030060b18076005003a4030400755404d11066004d0030f490502040d401100070740c00c0300e51106107010100d21511080d04e5070300020b0010390042c17000c0d08050005054091007868100341c00702c0c0845401049810003951080002c03400018401d15203400c8102d019900b054500801c500c40c84240065621401d2049080c080c03619800312000b0755482c020111503445484821580305071803864071b107000790300c0748240314801d04c440c2000d040c41c5417044200c0000f1521082c500c902d000808250203002031300002c085021445402404039940e1002d2000c0181072401143c00c62034142907182480340c80c052904110702c1c02d01c0a00c010402036880c41c05450440d0020200c20101d03488845684000c0e10401d40902000c16081240a0443c80004010068101c5076401d640900341203201001241890948480d401034915500b408502c9095200541042005000c55407032690780c0046001e907000b0030050404164041810030920a05000b0450440424a40308007550300309 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 289538489 1250 289537239 289537243
    0x4020301060f0804080c0d02061b0403120315151110020c0d0f090306051e060d050c010530040516050105070602251b06030e07030b04030c0c0902090f0d05 68
    0x34150280800c0440404a001c5c000b0080440740c0030b03520603064400c4842414406559810180c400c4880c02110b0704040c480c1c0000002903405a0f80c1c051a60b09840011580860140204090004610249150000b40004070001c405049070050b01c80c480040c0380481e80500b00460600351000306070040100c150034070000b20300307140b0324015402c1c2410498810002200c0c000426000203021b507141c0b03400d0084100c59609200010b100d03010400005030703501024040c00042d0081d00414550000b0340700c0b8600e6000320050304c00064104a50500240340d60f003003c20041a2001c1c40c40b022840c10b0600c03040c0401440890506030b40301d032075042c02907d814002802489904000b4003201d501050400041030317a8901c00926a00f0789410504410842c1001c2d0880f00c01e11014402d03054002e074001607a18007034010400c0111110011307040e003500d10380b02e00750319910042c0304400f0017445120f00c00020300c908003814040e00000b00d006031107010300c01c24440441d83c80107519106041c454000c800142d00 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 289539739 1250 289538489 289538507
    0xf0e0105010f0312050c0d0c022e0311090315150d050a06021309021b16051809120307020106090612200102030c03040803090a050904150513080c01090201020c0402030106 75
    0xc41003400d0081410780c042215075004119116080b4040c442c042447c0303961210040b80c00303a008554400003004004580c507180307110030350a07013150f443c0c0c0d840c00328005000e0b5110925103100000c41c0d80c41c1201000019090000324007a14400e540c00c501400840c8000c15009800d000041c0c038400741649543d101c6640d601c40c1c074080107001a0300000c0000a01c0c941201c80300c01803060040c25520361100d040d4034041c0d40c0c824640c00b00540700f08101c805c0e440240740311410482c1c001909030003181c0502165000f202c18018080d064511134607604d492483c5000008602c9401150300004850382030080510540380c3c240e000701c1440142c00c0e50307000441c2c172080f0344404501c07690700b240813802c6143c00146c2c11801107594008050102280c00030b0710305404401000000c1c800c075603540c12191640300700318251600b6a0701800405040d2209003070941c503644503941012240d803030510f1000286e51112080d501c64031010202da512005001e085503010081c07061b580108075015400c2d91f0501c0801428000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 289540989 1250 289539739 289539743
    0x140114280f08030d0515150d060b0a050301090c0306060e09072304030c09020c03091e15090909010b01050307030c0c080f1b0a1a180f010f0e0105010f03 67
    0x540c0840081160040c29101402088054041c02480d0341e10725003643c032604001c0c48907036a541040000703044032103106241c03042c01c074000b82110b071021914000f0400c00d07002010b0281010b60b54200116012401d8070181c96140603a0b62080d41d20340c1080d11f100181c1c1c0718094008141030070258144045c9030400d4013082c1039407040d98014200d540f03003641250b2203000d80c90301c42c0301581c0400c0514000c0500e50010300c2600c2c0152000c0d0490765807040200224800e401e00d244441d0000d2004140034544941e408001070020940842045401c0f0b00180c0b50203c0001040c4400314000703110070290800007051503121041d100204049003140001034981c0c400100f121080590f14422421035600480c8041c50300c0c1c1d04495003e03255500d43c52006060b6004225680303d8a100c10040c211001000503001d4510303521280d01005c3c1c010066000d8400000607000341c0390403070380350b0000308001c004201d41049618454001300310700710a814070400f2035006045201a50741010700500c03c0300318800706081125 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 289542239 1250 289540989 289541029
    0x23100b030a02090406090509160f050613090507030c0807180315061205030306090907060c0b190e0606100e09010b070204020702030d0314180d0c020105160501140114 73
    0x3503640309941d002403140322855035000386810b1010642e0302c4654004e03485001d0700c1d000c98401d41403070b04411840100912078211100300d403c4042c0007a042c80390240003202c8005070240207290b15a0441c5042d541c0440d00390001998481f4160308544c2c0c8001055007007511350a100b03105603041d003c0c6241404d8107010140c0b5540280846101e1500240e202c0d000603e200300300b8044140a52404039180e03401955100c2c4079002220124001c560081040d03804c03268161980018030815980b2091410402040d449003584080c1190300c0c041c1c1c030f90182c031100d5146400680306914014003080010068103440b8000c028601e540c1100340c1e00d07048103a60646a99030852601e90034680b000801a124039000203405024030f1a80300c03e03d41d00340e082252280c0c06444031124559a1a14200c000340e00742c0a12401c940c010800100200c1c01081103501090040c034000e843c2c1510910003c400c22180d1100b1151a0340d680fa4401d00401110079450161545813841100b8109040020b0003608141d1300554440b = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 289543489 1250 289542239 289542241
    0x1f0609060e0612070b0d0203011401030b090a051b0301180f051b070804030f14101103150a0302062706040302010903080a052203030e010c030801150215010923100b03 73
    0x3d00c9003044010b00900620581030790314182090b102000c1d41081c41076104405801d55000c0566000b8000c80184990250580c12030f9a60824032002401020b400d410881084410b0071001e16200f00c01140a8609010403010001c081507101085900030700d910a021481c01082c03221001c100241240d10880180355140c845030a81481c4080d88583c1d40b00a1042c01c0650300001003002c0f544240001802e281e090341c43c521143c0101c1c0c0d084d680120301201c04200c081001441940c0c601e8881c01a111002d000540303c44d07165400714a25601c041c5c1005840c1c401b50030300300da40e5820242c1c0490070101c2918890700b460302c0c6030300103000001c1d01e0000900c0c590001c03500c0c0a4041c802d500b030b140d01ca1082041d524054422001104100e4800d0000787c0002d0a80c00d00400c240d4012441045800d1740759035010881d85c6817001c801c042c00c000c01d161400714052800c01c50901414060154041d0000130000a0104407940308504d100c4421148100306500c0d9000b0003490f0310813400864126246c012000750b407 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 289544739 1250 289543489 289543519
    0x10c030203042606010303090513020301052b140c033f0c01091209091506140c0a0507080f0703050303060904061d010c121107020d0303020c1f0609060e06 68
    0x240368a11000b0741d220f84a13200001003410b90044400c1c0c205c650555410800b490030b400007405910090240b01e03082000c0c5440c101070700c0d0301000340c94001c40c02020843e0700700c00c980d0760381400003442a84c0c9011076440f031140b40d1310615090003018142c40114406018140c88111140072040c40b50140c000c0f0b1001050740c0441c400100e90880e039140011388000c10094040c1d20303009003420110541c07840010a20080803600611521a5001c081d1364041c8102542c0d141207401c4070b10310514a850040c180081c0b15402d070403041008131500306131082020305102030500821a141c8004070341003000f190720250b010000300d180031048035080b04058460248a0ba40c600b420005841c0461003069024448031400b2035200042d444201050429030300d0f50242483d040b5241c09036160038100504004c01044900010b180961000d52458402d08015082824094505050401c2441c03c040002d00103080b040b0f0f8420303140300d980c01402da100d8042120314140356200b00b4020004142500402603110389100d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 289545989 1250 289544739 289544789
    0x2090d142a0d02041808040303020105010f060e090613090803010306050f07080f040305070f11090c04050307092013060e0d030c110109090203010f050a090504050303070c06060b0406031a010c03020304 88
    0x501d030117100540000d0042e8518100f880b5a00900c802e41c0103502e03150011502c0c48000120408071031055403451070550f100b904004100f000503000c1d84c1d01201c1d1342028200300c14140a4122100c1c0244a4030751079601d1400d09406030b40300140040c072010000804c008886c2c1e0002c021541008181030303401481d580b14035040e250b5114001c0c010b03000003044040d100420112801304060340314103881e005c1303043c1c54420420b84140141d01455926822010b82440034101035840b071450444410b6503c11040355088071043356900c034440100d0401c1701d181041c40f103103030814010603800c2801d8074107943c92125a01c0003403500c95500340080000040e6000804503038801d00074070003c0c1135045011542d0f56920036a801000b0501c0c030550340a0119442d00150821240c41450701c56a0844003443c50741e522504100c40e40d10b00307a82c0444a1942e00d41d004aa440364140107480070f0f00d060b48001455544103c1400ca0a45070402d9140c10441d003407803e080020750100c10f503412620910107400d81c51302c004101e00 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 289547239 1250 289545989 289546001
    0xc03080d020408060c071407080615060409150305072c151009080c030102041824030b01060806060316080604090b040b040615121502090d142a0d0204 66
    0x50180e2040c9030901c07005203005c2d00200007062040301da01d501c0c0d41c111a0390300d85961041c403d03940c440c0c001c140081ca068150402501c003d800041880b4501610703079440000300c410349282004401e20044090040040400c003220240040c1c1100a01c8800c4a80d4940301c941800c060685400d030512000c04d001c3e00b881441d8584903040101002905084403500600150061041c0074462040600e001c142c1e0070188222400d03100c5804045031119408280c000c0901600c4600c020004104240045101c0e814a4204040d61148508660304c1d45003070001806202e01600007031003007600f04144800c0c404020311941e0382003501c0c106001e241e5581d4001400420550780e0141c8010740500420080205801c1050b00c03e0f03120341401c00c03040c002b0100c1e048101da214051150080e400d2200c0b4404603001c4049102010054000986051024000f0519115000c0402c551075483d14400001860060001d4201c1c1408654180c096200d80c2800c1c44aa0004141c2c007409464540302c0603096444507000342d = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 289548489 1250 289547239 289547249
    0x7060906050a0510061103040e04020105041d060103050c0414011d100503040212071a0d020712021b09060105161a1f0501090501200c19060909090c03080d0204 70
    0x10000e902e016080c400c007811040740c0c04c1d03440c04050341010594a0042c3c801c9028a0560001075045c01d08000e02801095005001a41409000d010015178055402c100794030050b6980f920440504000b4005011350320060328010703a50700180f200b4454060b0781c08090420440c2480c00c640c10002c45d150307140d0340f034891050081d086280c260307607020f40d0b0b50000010f43c0218801c1d00d07240500003440d0303103041d101c1043e80181c4100101000030401500c0004003d0302480d401c08800500d4490729550711000c461a0504c0d07440980c0221341c0d002c80803501e009030074150303840640f41034005141840c002013213032007104001c40d15481c28429000521200e100c0400c842003408a050340e460030200000c511070580003482c400750080a403c0490742e94850082d5504840040c3c5aa9101ca4101c00308155032118130207140d0a00e12911020710503e0b0b5440000031049064400c030395060307500f4264000c29074401c5410480c07405062140b400001000b0040311801c070707500400c14580307d070140320005001e84515800 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 289549739 1250 289548489 289548491
    0x3060b04080c090f040b040b0a0f020d060503061f0902070f080d021e07050a0f0312050f18010e0303010b07021804030302030a06080109030e01051b100507110f0a020607060906 77
    0x8608150009548a82c0351011203200700da655440280b011002c0701250001d040c071401101160010301c1d0496402e80084115502080d6005034211003400c030b0300325201040459480b500100024103003880307520741010000340f4224425240648608440c2c140d071252485050340010740000b4030141c501c0d5600015402029141c4c0d861140c0c0c2c04a010b504070b07034500710190f07180e00040c90205a07014200c868440c0d10601420200307140c0d0b183c221a00c1d080650507801e100016140190607001c511816110380d1401e414a40e0508092002142142c0364102007609a8500301000348032640000a480c110b40340702d01280d070b46145610208030640070001c503c0510740f840000340320406800d0780140d40718000c140320800880c3c0e951402c40d800e1740c0c1c5200000e0085142d02040d41c095521a80007031055400140300d004500700d070380c441d480c41c20122885495820b07540310280062a0303030103031505441c040400014000058039644541e260200110024131681c0700041420802c00580c21034501d107508154 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 289550989 1250 289549739 289549747
    0x5120a030e030a17130512120d021b1b06040303020703020f010c0b0a051608010b0909040c0b270901050102060c070507050907021c08070e04020d06080109142b080703060b 75
    0x3002e08815003042000002158a405c40403507141050b0107440c00e100382c141700500c4e041107292441810387e4002c000d2491003980030845005403208440782540b5461100000b018408604401054401205807009104840421040021950010348030050300d40484008100e00c501b0f0780161282d20408800500103100441040305000056110300d203c1c04d03081c03900c525101c0308101d04441003e001d0281d0b0b0050441030100c401c0702d042c100d0499510510502027410f03046d0b19440d01d44540d030828100b20f003101f02e442c408403640c0d00260b0425509010280d41304952941040c001030b440b004000c1001405c4000804e20009210040101c40010321029041303002c10304001d030340252244008c4200c210120344413640004103501c2542c1c3c492180714280d5880c14070702c1040003000080c1d13110341e0320b03001c00720f4440c6408034104400f80308035480e152180420003205468448014100b081c5001c40700d6148000b58050b030607138440700b4150a21903080c1e242c207240303c1d40d851500380d00400c1c842e0850146c82e0f01c042 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 289552239 1250 289550989 289551023
    0xc1306021501050108010303090e06030a0501060801021c02030403020705090919080c0d0e0a060e040f0609090b070804080712030e0a0602271f050d020c070e0105120a030e030a 77
    0x420760000010070401019426a03e071801034940c81c01c00c0c840140024103811003005400c4090ba007040c0c0103480201519038056043c4c99150a4070301640000115943c00112189000400e05861840d58403072a0294114905500c0182d2602d0083c800e440c007550410300081e42100061100328001151807241034900c012906004900323400140c12a680da05c00d0042d40c8072030781c2c051480d1111440c4000c020b480030606082048818401d04000e05e5003003601c51500c0304e408001c1d0b008420107031140c0c01d13000810704018100041028000742c880d205001d03106051102080101e4100c6207800e4104c510072140000c1c100742100200340704030000c4802e001d01900c0c0302c00c1185030b4004040c85000c10b010b4404444022684210f03500c104484541e0103540c0348146829465000c05890707040382c06c0d00700103050640301c156007000d9034454410401d040d00020350510070212900b0001d4050101560404405219541c902c1d0392034400740809018812500b5500400c1c2d030701000004c043c0c070340c00038410016407812 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 289553489 1250 289552239 289552243
    0x506270106032702130f140703180302060403140906120403091a070210110f0708060109091515090c03020705120a02030d150515030702330c130602 65
    0x78003030400020b00f8945504800822a42011070351008180c8030110400315500304180c2000489207400d4013900c40c01e04c21445556407103681000440c001c198042403420150040464405100c205d14504a4860070004645d00080842c0d1069250030401c42d81401785641c20418018050144d900201c0010115241d40c2c88034041805640b1079200c10900301d40b42c4d08035100100e00400007145d04441448001701518000200111003102e03400c0c602000042148123508045822542b8201a84000d4041044e1402088207a00600c1c2c018410003801d8440d90300d01400c0514240792100c5d154440002c0c0440c00310941404000340106201003080405400c00a0040c7d0840c034000c3d0303500d000b88582c0d0310180244c40c0c101c0f00c00c0c2c00c40d0b6014600d84000f040c0d96200810300c4401080c40701c9204c00300480c01d5115a1b0b800707103041540e031210303039282d01c0c200300c0091900c43c01959110004200c00651703803511746048084101c010310603a5003500d69942c1445070700e083c003440500c00e0b018000c0e0f0000084007500 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 289554739 1250 289553489 289553491
    0xc1005120604050712050a09050105090618011505040c0e040507090305010506060309191703040308160201061820031f1d0f060d0507080f0706170a050627 68
    0x8045481040d549407410002221800c40c0d689001c203591062017400011954001a80208002e10018400886031101401c5410071174180d0301580c0044140000d48004894800c140e10040000b03001400c0010f00c400342403002071040c207014940303c2045003a018000c0c50700c03070780c0c1e01400307042042a4500680e0081c8074071054071055465520b420701145a508040084a20a0252100a14070601c3c07954819411842401003a1030403407480c5d41e01d8070340c042d4420045020394041c0d60356150b6810015003d0303080385203844a00044d6072400c00104010480011061b24072101b0400c001040d03103c51081c0601a010005402e840310000010448840c00b40c555503600394000151690350580c683c078000511001d10740508101750320340c40015942645980f1103d51041024040030104a80c50356001d240bc13090ba0031445158100d203c000168400810020300101058540120310004030480c03018214030281c48080f42c2510ba20014090783c444042c11100c54100c01245101344000d6202000c038244 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 289555989 1250 289554739 289554757
    0x61504031a092a1c08030c0306030a0b0103060c08090a0f020112180503070b060a0e010308130b071101020d0c0b1603090503120901050123040c030b040f1b02070602060106110c1005 79
    0x65580d20344c0c3e600c0020301e00341c0c10b00c1d40c3d07202c05070a10310341340e110701842d003500000c1586a144c450001c4070000070718010402d600a510400c0003140580d200e59010f490784400401e00070190388420800c00100d0f18076640c0d280311f0740c0c080c00d280707510b0580c4a4210303000d40184000350043c41c0300c0302030082c01c009001000382a0301d07001e40c10040c5140c81e0802042000303e6148107210440c4142d00042c400b103100178000303109003602c2800f082d81003503a494440450f6040705800351400c1609180649941d41c05001c505000455440d000304100c82d1603544039601900a8141420f05800700401d07401c030741c001d6100540494001e0105c940b120482655039590f140222101d007030030f50914000245541201600302007000d991907000c0b012403106000c1c40014800c51551004154403440d1409141d01e03180f03e00c000c501105080404c0c50803265842d44e03101e00162080604552181408115055020030030506680051518140050700000311503e0701582c2a25039038800e000105182c8469045401004a01 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 289557239 1250 289555989 289555999
    0x1906090503010f110f0c07030b0c07140d1d18010f03060c0e0d02010c0f020a08010605010809060f070807050423010305090a0506070c080c15061504031a092a 69
    0x3c900d205010060751907001c1c51890341001809140c1208084030b0107020031508031001c03106d00d2aa01d41ba00a011201640c29941801d40041c0c000700b80303c0c1e0303003c900d0380c0000c0b200010300102c0082034005140040c0c60b506902821540003d0b1402a40c581900b004803d001e241c410200707507103c40c0107a202290382d11089400904c1c2280302d80109000760080e80402c103005240313400c044034075001982c4080703203000e0803940188036481d9100141d50ba04400000750024038000140182080005003170300034080c0c801c518652009041000404031050090740c4a00c2c2c5190100c09501c0d003850650b001d00441d0885814020030303a000341060508442201c0d6401002d0360240010385440c094a030321880d03807a001400baa0020000160958024040d61541c140f0800e42c403031401d08501c1902e42030401807070341c580800e8200030074450f462030f090422102103001d850720140381a15568400c0010920141852000f10400000a503200030900c84070029002e001d02d80300d48900d042903104c507503280c1c400101c1d00c03403 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 289558489 1250 289557239 289557251
    0x4030b07021f0509030d2712023c030714060402040c05090a0303050c100e0f07050604120609030323040209010b04030c09090204090c030606050414070f030902190609050301 76
    0x3040d43d0081d14010101003010358640030070201008080c20103440170081c02ca0460141c41080e0071424628500140030f602013400344220303800024101030441c0041da00f03403a45815004020842c04017540c44c00b503a812520b2205000321103206046016001010f441c242e498001c08080c030740b000c104580304034030840d010848009052826101405504011600709101100c01d00002e402280105050350795032046609800f491544041a0b8243d5269560ba5402c060104a004d0800300606006031004076645030a15040015504411280120150013071743c84429a005141c021ba01c60700d0030900c1030072603c584903084c00444130000c4091704c08a0051825100000310803502d80196026258049600f4068518065000014000030b4009983c0141c0c0c500004000030b040c5000ba20095100f81808280645010100b00860312126070050111142208004440350310244100b19010381b41000154003180b4004140042e02075a40340d19110300112020403880c1d081080c0100f20b880460091001c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 289559739 1250 289558489 289558543
    0x2309010f03020306160f0c1b030c0314010e0a0305130308040305010b090919140705030d022a0d06020319110d050a0207030f08180d050c010f09030e060f04030b0702 72
    0x924010343d117400640116000e1b89207512564076200c074540108003001920041254100f40060a684201c45120b84003a0070402c0100500311402601340410003000001410000c142e100e400308513000741081800510a246451030803240c602842e007182c0b10603102c0d5104d1400c18001c000140e40c0d2441a01540c0004107807900003d01c000124501c4442c640324230040396a0803280030f0021400c419079010742d00000c82e0f0f60301e0070040030000304000d9004107080c1042041818500310344940c0040c8030180f1407074915164072070300494182d256110742c00699036612032032517103600091390b00c030100380714104240c0d10b00015011014145040c11050200a59103d00901108900c0740740c500402050034480c805111500500c00d0340c1c0e21144c000030341028811040380460901114121070404954045071703010800a0920401c0c4103e140710804010610042d10003070b2410220000303080c4103030000108411440b0705c40f42950000c580c0b0581c0003400d8180050041d403168444894041c19641d80b45039051 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 289560989 1250 289559739 289559761
    0xb090316180c110d08251409040905070f09060b1305010c0311060f070e220e03120115181a09010302071406060a0602030a02072309010f03020306 64
    0x100311095011103981e1a00e01d030901c400a06003a00c0d0000a204000306001c600020a006614070000269108400d83c54100c04d0201a03203118030f0891b0915005a0403000390301d070419980100500c24868041e240d03040e450008000d0440c1e5000100140039110b000907680502c00060b0054a04038681800810f0305c41c034240c40b840c02031240c1c040000c9000c1200b08521f5000b503140790b500782d000703240c001c41d20365105010a00d0000d003610f02120840a00c1d0802c11542d500c42030340c0151030800c96500190400d21500303115040f00c42d06586000c0c9944000c1c0e0708400408204032510a00700c0c5221041541e514012100f030300c1b2115907804081032040540c00003e2040203041c80c1583e080401d1601100140d0988a00503004825400d040c10750802904003c10101e654407080322540b84000e00700d9150134020b0040c500f109078000010341d030042c80140b0000360045084402d907101c40c10503003030b0310306040310781301010224100b544d8111100c480003180716403510480e00d040d68025011100c0c0f0703464180c0c5d090 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 289562239 1250 289560989 289561033
    0x5120d031d0705040506010c080f04060329012a030810060c05030a0e04090803040803160207050d02120106090c0906030e07030f06050603010f050a0207030305090109020607121101060b0903 83
    0x9080e5040400c0c184904e161031740c4001e03002241850a8505400d981d034400c250303a80700c2440740c0c03d00318001c5030070030240e503050080e148135900d0a40c10304d2011204c0c1e00d02c50f1902d210351030000c0c1400241080038400305414085800000540d4041003c4a0410704010b010740314190741c0d840200c0c442d2000820f2444c080d00c03466407411782c440d009516203810900100c075001d03407007524180d01c251a99000700100e000c50300594000c83c0200181540c90a04e801c010100383c1081d00130a0540d08044020001996405910000c494058640200300c04c06809100e00408058004559803898400c81c0c2d0364040d400030611050740c60030340b01041011103003c2d41540d00e0040b071100422074019680402d0003d9160b4110541201c000703800401e10110b1641e003a030a580c01100c08046060307012800009040e03040c022144c002c0300340c000802400000340c02003226441040005400410341103000c0c00024820f8007103003500f40d8408001c02505848011994040c1c1c810441c40d4400d2050005681101281601413 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 289563489 1250 289562239 289562291
    0x200909100b0f030705090d030e04050a0e0304121a09070816140609130c02030a0e0a0807060503060111060103050c1e0a090c05090306010e06150313030e0a05120d03 72
    0x54107000b010404018142c0c0010009030801505004059190300c030300360030031080380c8240c0702c404014580009000417200002c0104035441e080500903507040d50003200329000c0e2146819404060041410805404900b40c032000d24442c4110041040c20741c8045860720964041c141500d490340c16648007a01200c0e4039000340600c0f212451185410343c0b802c040200410032000d040c007400c644008161000320b840c44100b0300e02503000004d090700619401441010202c0044904214407410002d5003a610701140c021402405070010200341360782e008182c14410011210112849076842e0704d40360303807035646401c0b10341c1c0584104542d013414000b40340e0004d000088040d20300f02d84545000c1981000e08070341006401488001c0004c0801620706201050107040035101450703803410700d038050005074031402848440f004001d005101d5140c2001c00311506030394041c58000b6100103480001002400b880d030141c2da014821011141c450200815890450146070302d04000c080400c81385041c000100000c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 289564739 1250 289563489 289563509
    0x1703030604200307030c09080d080a0b0103020c0601080a020906060918040831060e011b1e1101020c0109050a030602030414070305031b01020403031205070320090910 73
    0x80c003030741002d600c40c00d02c072900d00300d91160880c040c00020266603c10b440e1000013035200c141c0700710f80ba9000f0102d038000b071080000900641c01120b02c01008a407001e0720140315640c48400f83e0400e03030300c01c4d0103454101c0b411000342c81a03540d642810a54968107240101d000319001d40000706103117401000d4461545014004008044a0740000c20442c040100704803608001840242041c0e071a684490500110f00d070308010303100c0c0c0d02070b01905000c0c1540d4451070401c41c8d101403040c02a6030011500e4550040205440c2e0560024608404c4e00b4503205540301541c408403200900f44405008110b1210700203800342c0390050b03030b600011100400680112034120074646030800029116600440d03200340500070f00c02812020f07100e01c5083c411158000c1c0c0d8654800b041a85001030182c10405600c4404002180741514547d006454940c10100c071511702942e850028451501a401c9840034404440c60740301c070788859100720720031604851003460158240b0000183e01203002c140c0a41900c456a407 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 289565989 1250 289564739 289564741
    0x40f0e130311100203070309030206010911090d0c08060c210603030316020309121c0503011a0d0902181902030105030a0f020316260c0d15020f180307170303 69
    0x41c1a0396500500002d001d0a02c80c0300280d10050380f15101640c06044280d03004200d071101c0f8103000b8980740e41030304000310390f601d03002d070061441d8400001ca808400d401c0d07985149401030344c1043d20a03e1201da100d03ca060081c0c904010354042008002c10007562010038074010400c8c00001c6e40101401140e5691b0550f00410200d50307541c4027184484000f01d102d1040720700d07200c07042012413070036800c240020321582d01c07807412803005401e5403410680b45606882c19600715890200c1c29007503030704880e880f080d0700c44001030003091105c256081080001e0300507001c0b9454611b81620304010a03011103944000600360022007120f44010f0003164100e84005006094043c4240c8900d0742c1702510180c100e034540703d0515151008088400180003d01c2c0d040003040c2e0300013001d130700c4c02c0020000ca0a00003441e000322020807004d9441000e0320481c2070300544c0200e041e424050f010802403290200c118051900410314070842c044428030340700320400a03415a40203c0c0e8410700f9012543d01800646610b0308140 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 289567239 1250 289565989 289565993
    0x1b0209010306050a020403080d020a0201141b070317071d0d030207050f030304150206090d0e010507060e070f032015160201020304090c030203090c10090303140f040b040f0e13 77
    0xa004181c00c2040130740b00501c0c00e40e403540c0701c14040e0b00c40590401c049070041540340240d40c080c4101c61b8088500d00900050740303049030802d0120544209100b99081000c684002418810401441179000048062159040c180303000740c801410b4816903030021460070400ca0050405090319240b03594190024050603007045c0810070411000b0202075010300c824000090390f4581c140000181c01404e402500281c1440c10401d0f08101000d1030950902c80721007420115030340d1000442da074403600440000350030391204018a080c10360551108800c0c030104100070040c03002842004800b2100c00761305c0300445072041c040c07082d001c8883c901c2c0344900c1d5040c8010844280003980c44a85280305106413490543c031000711500f1211007079900d800103a03001c41041410501001002da800f070040303a8000504451040080c41c3c0c81140c00005c0c10000d000f0190111a1a1902624242011002d200740c4564480c2000807032500075100d8903941200658001840000c0200c9007405514601c0104406030301c15 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 289568345 1106 289567239 289567241
    0x9090b0a27050c064b130e07050a022b11010605030303040c0e060102061605070203070e0c2205101d090a1a0f030c151b0105071b0209010306 62
    0x180d44031780e8024904441703620000c5861411070744ea6184e101054642000c6034040604941c0032424050529004005001d280d081942110b180c1100f00d840ca12441000b1440112240c0e0060241038080740704181285140b2910380010601c20350780d1002c603217075902c204c5003907944a01400301485a91000b03621207402003001d1000700000c0c280f4461001080b070048404c9130910000058a000b1034809009800003019012522441451306803e483ea99034410b10b211026000102004602c03030b6410034400d030503964050800c1500b00c0c0500c2c0b041c2ca403500c142038511a04607881c1d098003419915080d06178881c0d101d60f200451381588004115002030460042e00f4807890112040c107849031400211a51000c104580500c183c901c4140b031018240b140802c10b8089103034669000c204010150405030041446a035000040070401410708162050160001d5103c40c1e044010000b00d125 = true := by decide +kernel

theorem cover : BRFrame.Cov 289388489 289568345 := by
  have h0 := BRFrame.cov_init 289388489
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 289388489 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 289388489 ≤ n) (h2 : n < 289568345) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
