-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3205
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:58:49.020764+00:00
-- url     : https://prove2.me/submissions/5f45cb34-f2a1-4e78-b7e4-d3ec4736daf5

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 576258992 ≤ n < 576438848 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 576260242 1250 576258992 576259001
    0x150307081e01180b100c0b041e14010e0a24140a090317060a060f0c020a120501141b0d020708071b06050a0206060405150301090605150d1505060a030b0103030c12032d 73
    0x600604552035254604101030304401c4180396102e18024403105952527445500c590990728000e20aa412100b805050810f00100c5c4ed8a51448900014403215240e204245c0d4407046501e5500207a0302d4101204054010744058a0f181c098240c811461030854049442c5a41a01685040c800c00c0700d0024002441100d540208039405010303100101d80d5451740304924045090101d07542c0d420010b0200c100b0189241c464800d58060520034239400c044075003512958440303d15a64269003c01c203480100b886e000c0246a01c1c1e1140c0580d4074907181140c1c0340c1e1011006034002400b04a0200303c0ea0141c1a40012050340004044a00040c1f545075070020981c0e000003092415015400d0081c840e00b0310860b070380f14a1240100e28000e810010031101044030920019800078a5807005079001012446240e001079404034000c0d0001c401071341c49803500c8800301e100764000c400003412240c1440030454103400c019041d41940c00c0502080e0051407c0c0400000d02641c042003025102d414000c0805641c1c11 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 576261492 1250 576260242 576260273
    0xb04152d0305070305031308030a020a08030a0204030c140103050906040807061a090703060f0504060605031b0405120705030d0c1a0402011806110705150307081e01180b100c0b04 78
    0x440342084e07036034580b44c1d0b101d410000d114007103110145000100a0800b0045500301e00203507010b8080c081c3c2580d5103800721740000d00724107021a400d100c0440014405080710003e0300380345001c00c001811000c001400c0d514010000841c0e074000009010000342d81200396501240c0c4a013011070b464031008880d41016560b060308a600103240c909004105401d0b9000308141e50307000b000c11030b4494135001403200f41c442e54490000020000c100281003034100d0039043c3e1011500ba80054a801c0d514000107216000507410b003502504041d10030042460200070071880744200742042c0803202a070340c030340a141850140a640e80b4803100000101160311611500c003802059244001c0b0154650f1001042100c011a60052074452a00082580c0c500041140c0d07103608444e000340e107969101503048030440f001402989080030f541c4a900300818000500c14041c003403203214140307501a27252400c01510703503c0003c80c2c042c825110480222036444214080d079190001500c205544540c980078070500c12651 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 576262742 1250 576261492 576261503
    0xb011b050307150504140d020a11030f0106150e0d0b16030e010213051c0b0c0a0e040c030c0305100b0f070516031214040503100c0c02030d030b04152d03 67
    0x3c208194a041d512460080f40640c02610348155801801650b803514a080c03103016a200001c074100043e034a0200e240705a801509880c1c41c1002c0802d81801e41d81306811901800c080c0501d008103250340065115500c86c07044955000801030f41c0c68403010701c2000340003401646080d02480403468000d800400102c110302000b1940c2d00030046d8890200303082806a5440388402806030109c48034145a079402103504000800c220b91100c40b01c9081560251881c6005d20064401d0039429542d60302c180c01c0b00304a141c50104038084e4140b4018210381005001c4140b456003d001800054100c0055414640b9800c4032260381e40102d0608070700c0c2010072440d00b455014071440110800c08106051100c1e01600d0700c40040781070465210034024003c1d0301079950103600860300c0110390100b0342c10103000142d440c00e00829010380c680101e0b0824840c01155408261107441e03412150520380710780340c07c5000c03500203a0001420301d4803250301d800703004141081d5846218441c2c42035a02c42d1004100031540708 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 576263992 1250 576262742 576262763
    0x1090b0c0c220c020303090606190305060415050105030a110120060112110102060f0f0403030e1009150b060904052205060a0c09030b06191e080c01030b011b050307 72
    0x100e448181c1c040402c0c2155030300e42440003103400c0500010542c4d000d003a01e40080d1030350fa5580028418200ca1550051800001c8104000041203007801940d00545c041d200c1d101c1000e81e2100088281c0f101a80000d01a80c09071318050089088465190000c0c1003d2802d08000b421501608000003440e4052801a00500000180d004441c05480001501c1601c4c00b113842c400110040e41c032490121a206400c070300640001d0310300f03080c000c0310030790151003401c0006180100c82d00c15880c051040349800c0002e96511010024000c1c3c0c0b140c80350100d1502c28040c08410382250218000d0b029800d116805992100041030400380341c820360b8000f010340c40b20300120400c034074180560faa0303a0558620b8a428a4181c0d10b12180f8071824442090320f8000c0d0040d2101e0300c9401c140244609076080f42c80c1d62568111b0040386071901e40d203100d00d0400300010407645040c06d1031013103070070041c0080c00c41b0b040c1480c00b1203800c0c0d03503600090750323640c07543c00300c91401d0f01c20341c0d6800c01038114440e60300c00a03e43d8209 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 576265242 1250 576263992 576264019
    0x31c0605190f12210314070f230a03020c0a05060c0310140913020d02100c05060109050906070f02010615030207110405090c0f01140a020f150601090b0c0c 68
    0x9800349003150b0041103555990707a91074259615444000f0409401d421040040042c507400d50b020590700c02620307280c002216600b00b20042c92041c0103603100000600070000036044950b00c00f003001c50344003001d0144008010201e14590403481046100d0342416000b0900764500d090901460310103981060030b0701d28a00d820f1074641c5560b030086071801484021404040b52080840341d0465a00801603c201d51036100c03d440172010950650040368854000783c00e240060300c0d8030214400f55100b0b07403583c110a03020b82c50400d0030002c050b000b40341a9454a030030041200c10020f03003244c0100541c100307184000288071049000d080c107a00842c4564800d000b22038500780e030550003001a103001c1e01d50445801c04010030002520002e032480d00203a8401c030020030031458010445030b24003405042400b0068918004046185c20450b07084016030440c0e8401d83e4100b0081c010202d1850003281310080354a8000c0020b003000740c250080702005031011a565034410005c22103620f414034000c101550b11080b = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 576266492 1250 576265242 576265279
    0x403021002010209030f0c0102030a0509040f1a1005091e0d120504150c030c06020c19060902030c181b0d0509250f030f230a030e0603060102031c0605 66
    0xf00c6030300382d4013a200706ea07409403201c0c00100d030034402540305a0182d460702124220440780c980212036125071059444628190080b894421108614608000e49844c0703001c1104024a450495a0f07100600c101001144900d91760201040400d001d003002d01c014802c00c04c0f010400300040001d000303016041104000d250135400c030016004840519400c060601850901101c984186070030040101e000440c81c0c4000481d96005805400356100480303500100a0300e551016118200060360203135030b9810300b07106508003404090039102c1d00f41c4641991034880c00200c08580e10080c0420340384100a82030325401c20030ba00807500f01548060b07051102e8100400d51a85454044804213031401c1414541c2a583e04007603014000c0340e82500d00b44801614540352040c0d644280541114016400c40c0100074164580c1e0500404107440720041c207403119245400b6006c102c010340040d10849080c410015071ba80d0000440303483c44c03070f001442c0c141503090084810182200e80c100d1a80300c4007111141e002101c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 576267742 1250 576266492 576266497
    0x306051f080f0705060a020613030521010306060506031003060c090509041a01060801080a02060d0609020f1306090509060d030309080c160902090a0608040f06060e090c03060f0106031104030210020102 88
    0x2c1002d083c0c6044070764030002c0112511410840d280542c229100042103c2051028951054080c0c1880c03490803c410201381440300c000400400d08260082c014018400346125a80103004c0643e2024a0350401030741034091035043d444000d0910362141d0b41d030b04480b84075142e850001c0002602c842c089003000d1601814800300b0045880d0309600000001842d43d00c2452054100c1d03004e10080c0804107650707001d000035507110352912410107449400004211080c3d02c02030003080a41032201c3e40710062511038208d8011107074486020040b2259041c00907035141e030303900b5401240441d01c0402000c05440d060700508403202025140c04004102036000047c04510320301007c4510b20f04201850715081c4100c12401404e0740160040c40c00007080c0300d8540240412900a406000e51071202915035640314256032264100700c40300e903225000e000c1050002c200a22400b00d0480152005160501d0b0740c4000690511404d0308058541c000c10586548400440300511740203440c1ca4200d00780c03924064080c3d03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 576268992 1250 576267742 576267763
    0x8031303121202070830160c14010524090a1a090108030a0f080903030c0c10050c07111804230f010e0f03030403120506060c0d02010903020105060f0a0306051f08 71
    0xa4414100140c42405a5090203150009040c034000d0b880f4103458510f0550030044e04028088001c10000109d00c00306406141b08022000100b1146407402e40d8580102148a0820b65005a80c25000907981d07012012a80050f000c100001c0c10055011290f19a04010304165042000b2030008110b0140100c01046207034010b4507160aa00070b510000c0b644044d0441c0e004840f41c00c00d001049122800c90014240c1d0b00c01c0d44e0072980000c5801803400101c5005031030b41720102a0000e00c030340420094081140c0d02c0c08040f20614121840c50600e0004048020802000c2c4200901e94a48d4283c80b408241511500c000c22143e1203000204590b00801494182c14010702c5a03e88500283c040001141c2c4a0750781652018512074481e60304e400900006001c040d4010303801d02c40f14101050812441c400d171a404c2d800800c100703946050283c2150006012540510040c010105041e01d83e0083e40044075449400046c06540d402200750b550001800c220700384544154000440100010b00c49001 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 576270242 1250 576268992 576269017
    0x61c1503020a05060a0206040f03090e010f150912060b031f05090c060a050f03100e0c12010603180308040c0906030818040c0f03150806100906080313031212020708 72
    0x781903c480400800380501c4843d680140d01450001d0300151207980302d10800d41c07007070500a84c080c1d140c56100c01d49400981120144210402c0f04000c1c0c8100e004172181d02480e81d041500080d428002001014041c002e00a8004c0d40c5609100c04261020010000b1503000703641c10407064050301c0030000c054502691005024490081059210300d0003808645161000d51121480c0044100091000e0781004213162820b20012a00080c81005084801c0c4122a14051035a071801c8401c0023501100041e0040700c101454098248600e075070f040740d1002525007604021440d580c4900d007100404201d40c102c0c098140c28808000304010440000c1c0c0404003c01500c0510140c0032400e04c4211800c0e6010000080c1c2001160103016020381d01c1140c0c0224000c41846140c0d80300c0c0b0301d20f481c004054540b5030468500440410110402d446030368064100440030b1840c3ca11401c2c20084466420300004c1c002c82c1104003a80ca025016410100070000100c00c1551a07002e20706100504e5000f003040c07541c1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 576271492 1250 576270242 576270259
    0x31f020903010f060f030311010608011802190b040b071e03020c01080c030c03040b040519031107050303090a060e130c030203060a060c120e13090b060111060114061c150302 76
    0x80c140158000d400c00c5d128107081082d030551a6450494030703000d20f04641a43e80d56111800700d100e600c203008540d01c141d500e600e9651110424070500880017a800e04a01c0e1032800000f00740084d01240044600711001e01f50403507210456401d06114880c0b41e41803801c2c08488072450f8800305500030643c5081904241c8915015654080080e8050f01c0700b180c000700031130000c000040004540718031964005015400301ca120301041e412071411400e0a1001354027003040c0da100114220401c0100308060041030340658203104a20002c00c03d001d040d4010302d07090002070aa03007003190321418000085116450750500003034040e03a001a009501c2500c0080c0601c640303c002180f254050b0f0f01c61031450380e00c0f6200394000b98502108841140d41a00b071250710456100d002d52006000740218000b05024024080180c1030840c005084031648000061031900100010000a4001d14000509030000e4410aa889402500d21006084425035003002181352030b070900528500300403030200307680c401ea40118 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 576272742 1250 576271492 576271511
    0xd0b090607090e0c07060b090a05041b08060406091704060f0e0d12180906030503090a0501081e09070e010e07030b030c220905190605060f09011202031f02090301 71
    0x1100c2c08020301507102180d0340740e800316016900c4140100a8a806440d00080f50103002c0c00148150409954540401e91100107020601c21542d800f003061404c0480d101511034a00600d80d42c0725030000740054031540d540c0c482030041c403600c881e43c040d2070140c551209076910b8495030050141900c000810001642070201c5204505003485440b02198102c0240024405400000c0710810012880b03d01d074a44c407035030000ba036190903008180180d40f06001851b210740f001c00030305c02c0e1015540e01c1503042000807030600c03003040c0c2071540005140003010102c444c16903845007401d10300300c45540107114103000d45000140c5980100300150140015540074482901100101a40c039030314051420f038403080100c0c41110030b22581a0300c000001c04090007090400301900d45a0503c1845103450f02d1240c1d4003003a043c00c202180c80762130b03801a811201518440c0c0e01101003001e580c0c0502030345441d000b0900243c0c0541d5010800e440c624003144004074204140040c462020350041003241e070096003400e08a4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 576273992 1250 576272742 576272747
    0x31050102041503060e07050409020c160f05090901110306060708042301110633060c1f0e0705090a1b02010608150f070c17180f09100608070e0d0b090607 67
    0x158003a6191fa031b50701d406e290900c1c081000940c440c022081e000d202d82d00218002407130a124134001066480e81c5811228038003c144a09010010301c100043d91400e02d1150300840508292a040002691080d407503840525000c80c0505c5243c200400c03c3d1003194503044003441d40070180b50003103c02e0fa103015108140e4204169928815142000c40b400f25580615001144043c8c004075480001112807500003d10003241c3c0c1d07548400540f090680010007000c04c94002c6070301c181884688818204029105100c1c07607070301c44a044c05200c0c4a02c090b04081506070000745c0002e546411758050001c1807038a4290041d000345402c2c442d181c2d0710b010302c203400e01c1d10401076110b07103104518941e5580f0300781d0354280f402c49034020391200c1118160000d61900040503440d00103003107070046d1021000f10004150082020400000760300ca48103a201d403040100d4020034404000807111641044042602c030040180c41d40b550b2050701d19000400346c0c0c070340b106000e14a00034070301800c40e00060b14460340f501e1408 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 576275242 1250 576273992 576274019
    0x20409060b090f0f030111070c062003090906040f1d010c180311011e0e150924043f030c14071809020f0303033105010204150306 57
    0x410f83c003114450440005041100b40c00703800f22002000042c040c2002e00141c1c0054000c58800e4860303102d00301040c03005603007022034621071991044d01c20902d40c50300c4500700d60303910030600400c1c00f6080613008106e1949a582180404005000302800704000211240075440c07034240840310b00350308021115060b1401007446004240109001029050454a51135041e12580c0900c1d41040861950141c10758540c2182c01c40c200d02c1030b80e601108129803001c01103142c0c5449111281c0c09810880071107950b4601c4945661032082c1040103403040403030040c1e0710150040d41d21900c807a46400e0342d01689101e40382004d504281081c2111210030401120580d42035415803401030200b40c3c0001e0344008144680941c013001805081119151900d6120540c00807211014000000307440d03001c0c2d00c08603d4103d0006007281401c1d4001c50551511405205050f03902c80d050031983c030300d60040c0d03000c80c0584224000d2144d0b000300082d50340e10745d80c005002c140410307207041c00300103032a10a000c07441c1225030b00e4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 576276492 1250 576275242 576275257
    0x1c020a050919021602061c0c08010f14010c02121005220816020a0f080c030a030530010303020d09120209040b1305070e10060201020f07060b03070305030d020409060b 73
    0x31611040d41100d00d01c400a41c0f2940c0d80e106031500504c20100166100802081c1000107e540064012081c0d00100281c03410100300d0002c0c411618014002d00b02c0d82055201203c004480c0d0b0950044003a0040c0c8214a02c0c3e84040d411136800d07003a144414400054241441c10041c4080001e9601c505e0500c0d0303259030745440c2403103090000e050840894070040c0074082241003492464140506a03000500c1c00e00345501100c82d83d810901c0c02c002c03031603080c048c000c140f0400b13a000e41025003d0380e800900c10300c62500d2810140e0000b500d0090b1000c0c006242100c01c81080650035161350b1241406540c130281d469021000544071000420041000241e0086a0b54050160300803034443d56209062140000d1040c020701100c40401d401060040007884010007016122260508000321509407481150f00804150f80c01045000c1c03401d10701504540c50241c204000007188410300002a013000b19031303031001c1c01038800400d04c006030400380c1d401041100c4025404114056440444403100d024514 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 576277742 1250 576276492 576276511
    0x221d070f230d031205041101111906110705070e06120a03020a06024504020405030a1e080307030204060318050309280e27030a0309050c1c020a0509 65
    0x165080c1c00c0141c40348180a1084c01d00b481c0c401d803048190710807141d08603026941c00c41c14800c0303281740f0358024140c00b03c01003820001d0305103c00c40085030303548008480350049c0304955440494103000341110588520303d91140c15107500d50b43c4c0b602d0419913000260382207440f81451403140600716400040b1f9051407907164010b8402000c1c25141d9000035042128900d82e101000d07080ca0b071306c82e4201c482410908018071049907008524030040540b954101065501a51040106100c6640c0001e10344e4800c1c6c1c0d000c2010ba0403c0142400031540420580c03006102081c040288400c59401d600507006507115070b0340400c1a007d1894000d0141120b0380c8020780190401c011400039810315410000e0320700c03100e04440d05402c40200409103940c0c8641d021481c5110344505000d20071481400c04a00f10035041c07180300c1000c42c2d0903460f54903407003000e45400c1410344e5005000100201880820a41600145401030010b4140ba43d144600c01c1d104089100324071808010038285801d40c0220700030345201 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 576278992 1250 576277742 576277799
    0xa06060e0f0c0c030906040e07030c1107120609020603100e0f0c040b0306011106012303070807060c0606050904030e09160504142d0901090b221d070f 66
    0x505007840b81e4441078044a480c001041844032540303d03007000784010401d401040b90685040c28001b42203075030507011a030800c02c8081100d0b10100e000203410081d0b9406030b800b82d482601030302e0000d0003405028030003500309501008000202d0074501d032034000c5030014285900c40d9514003042d9445020f0032191000104402d00c001e110809282c1d0244d90720a206040998548082c414094903020090380700203150380d400c40205032014031221100e444240c081e4001c0c0803542c2029202030302c88a81d03004d41400c0007030300d103045400c2c818190409401004050607010307090505050041c0f8012a405490340501448004161710070480a1107822010059940900700b6082036400d01c90f4075100c2c280c0a83c0004003003002c4110005000850101c12810340380040300041d58820710096031b00507804601020314041884840e030b00c58450002c551148113440000c5100119a040d0040c100c0f46508812000c24003007009160500141030000c1e908034409426040313680b201040c0824042c0007412000c4900b0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 576280242 1250 576278992 576279001
    0x30103030806030a06050c0c0d111213030c06020705120c030c091803030a0e160f140d0f120207080705150d0608030f0a030c08040b060f040f0e0a06060e0f 68
    0x68410340b500000c008041da82d54200c1601e0f4107056600c199040710b40303038030005022924288208060312030b49040d828140b00030b4060f0203201da1030307491400c103400c070350440002e85040034140284000c020310352111001444176121000203540d07032010300407603000b001d40e03c10500c8075000024008801220040003043c0d0340403103d00b44461044050000320380d905c007060f18401b02c007405001941c8500c0000d00c0000708040004040c1c0d1a040e642c4800350b50000c01140e0902c0a00b85403640c0e10140c4500d54580d607650482c40d8040f580c02001d01e00c018043c414118161010030034000b0403510040995030841744040e4440182c07580341d20240c800c1a502c0074695110501d100c1100e4050700510781e60410001d101caa46884082c250341c0240880101c0d0000000c010301030640500ca405c02148480c0b80c030320818a082e81d15110241c07000707403175903120348125070803020182c1e1903030001044070046640501614030781c10042517844130f100800310340302030600c90085034160f9a40b0240b84200e03022122505240c59 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 576281492 1250 576280242 576280247
    0x90c0e060712030e0f0102160210050408060106140d0c020d0801050f0a06080a0b040e030310060203041a0c16060c0209090c030604030c0609330c2304030b0f010509091203010303 78
    0x480d0582181c02c0d01641d281d05e00c88480a1000d0152042e40c1c1161091041a0348104403182d410031100c5070501000b400103102d2010f00181d0750f41036965070704281041c40e40d80c12120000d030003980300c2d00c0d001e5030038440c100c2003180d4007288000e041d8042c1c1e22000a241d0301e0720b040148188210080c0354100118503400c01c0f0540c030400d4050341000e42d80c2800518075003403501103405d0341c940c450900101d41c00001841074155030110604002c195a01c040d40c02c0c40d0902c14a5070241000032003c4152190210b51000d58010034400c00b450911942c05080c0c02641d901f4000d0300c11258950180d2148921030000b904040c000700383e1423080f000c020050400390b5903568041e5035100070b000c019142c1c5560b440c4c0c1c07403000038003a02405240d400d6510421141e91a5288103465a12059000d1454541080703090f840c01c90300700110f208801079241c041c81d011120388411466a000c0c590025280c650420b00348214004d0350b0100c0e6050340c0080d10160300c1075445101d007c0d0b842142d21480d1046400c04c00040010a1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 576282742 1250 576281492 576281501
    0xc010f0206060415051305160806010206181005010f23030a0204110412081206030f07050103021b0a060204060915120207030507050a050f07051815030115090c0e06071203 75
    0x6101c1c003402c1d40e01c1c5e00c61020a282c038000040455002ea81c46041c49074801920041c8040c1003224034040d01a0b1520b100001d4540c480076060794683c42e445010b100713a001081c88540e8004070400c00410041d85d4405040b245043c10340301e8400c1c0304040040d80c030500f008120018800c0f20b0081d0083c0785c8030b1100d03824040108141c000e0148100d006000100d0040d001c00801b0045034040d444c19601c40d0520301c40f121a008000d000e9520039401000c0c0100c0c0c500010908504940d001d080050300d640c580203850080b2902480101c60034002c0210300400c00c1000c5d806442230b540c03140c0e61104001c0d25055110044403040e01c80f8408190401242c10128107181c0081000c0e51013450228204000c555409207092000d00c1c04880b81d0300041829002d800c0d04104880c0149402c232801e10040426110500306407074043d002000c0d000c0d080c00703040190b8400750400e201c004407400483c0d10455448040380c00508010704d0300400a003903840d4000b0b10745091801e17109031b10b401c40702d4030360307011040b010940092 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 576283992 1250 576282742 576282761
    0x22d0607051c021f0501030b0a0605011d04020c0a030203031b0a0c142103090d02010501061d040605030604052104030206090418140c0a05090c030f0907030c0609080c010f02060604 79
    0x14407070511303e0050401130080d1858620080040443c00b54154a8094004034006000301c80880c508101000707507030390107078481e404002462401c2c00150311000100d0b01030307c1100360041c400d00c54a00d4110070181e0000065218600c0c2c90b44c0319030b100d5600003600d019482405a040002620b42c0c00d001d02081c0c4004c3c0c480d0140041078200c0310742c50f01720864695803241c2c4118000410402008020702c82d007080c000741c440100c10f031000300865070400302c1c080d2a50718600651452251200008021619158800c4000c3e280040440e5070926091030001c0d0340d40e0490007245940b0240030343d2820130350450300c20740d400d60340c1c0100994204140c50302440014410004961000c034041c0c5648004540d09c10402c41e01c0421100181203207041c5c40013400501c0d44d59502040c0144800c2c0100404004114103403900140301c000c121201c1c2e103070400b0740c1e85008102c3d00003400f401500300c0300250b681c0d000848682101c0700002034030001190f91300190369103540a20701d100560030080014400d4a026803220952 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 576285242 1250 576283992 576283997
    0x13080f0d05011202040b010315170118050102070201110601050306060d050312040c171f0e0a1a071b0312050606070f0803040605130f080313022d0607051c 68
    0x3044040c00600c01580d400380d02245005841c5806038084d0300f00b600418516000a003010701003185070b001c41640e0110184030302c01c110a0003800c3c417540c24400703401c04a440842480d0346001080c0c10f05119000f0341c050030003240890b14254075000745101c003042c0c45048070380042c06850f0300d41d24401803147c0d02c1c0700014111070f43e000800150700102d003100e8003039010350702410392014010704207180d4402d2a010b080d0440880c3d408420b14101c0340461044490603680e168201250020305145107030300d081a0000002d1902440340e403a01e100c22001d10003075103e0b410560f51b404c0400704c4000d185904400900014000036030480b00b0701009203880d0841900b00002030040341c545985170315211603d00307070080b04a440070f03000001d000030700001c1e004040e001741c0500b01800001200350f0724065a4a0100ea00400c07422020000540c0100b40003140300103076801401000f03038410407010150342040c40140c1c01031040c00e00d804052413800c00000741e880c8164003500400b412119441c0e04501c0f44100c070a190304 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 576286492 1250 576285242 576285247
    0x130e0705121003050d0e012a12050c06150a0b0c030a0f09050a0f080d02120a030b0f040e0609070801020903100b030a171902031606090201090b0307210513080f 70
    0x100c041003280d01029146d43c4900d022003400c00018225290060a0742c1100344840c0040c02d0040d0408050510036440141d004200702c5405050b50103028140b00c13007010380101c204020404084000f040c013074000c01c441c22404c0c10b1b140c014800250203904044501d40e4424894449041c0c090044c5548901060070f0002e2a10760324400503030b040e10f00d43c0080e807000c03006180421038500c040220319124032407400900342c1c0c0881c0d282d120003d805a62028010182c03a1001001d66403210104034a842c01d010304140321680100c08041d0791000192035050007817003080380001e41c2c914103100340c1c1e81da0013008019050007240405d40340080c020b40165144d041c0104088200040e001e0400035200f40150200107880740812000011110f80070f1030311000b550410071009204005000200b14440e60050303000904002a0004941c182d03183c0c0c001c40c3d00c4050000901c0441030300044070483c504104a007000e400040d1011660955106880d0502102c0500d030141c40051100005070a000c47c2d00d4000d0750 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 576287742 1250 576286492 576286499
    0x12060d0b0901090b010f061e030e011a10020d080604020903070b160c120503250f0b0912040b030141010801080a0c051302120408130e07051210 63
    0x41000c08159800d0455a54400006040000e10b6401d28010705030322040d854040e191410140c40c45625000445d01140105464141341d4000d9210074a2901e0300700080000c40d000c8243c100d0013840c1041d10500c1074600310801c032034003440050690720907000d55480040d203440d007405110180d0000b14a641d494010ba090109503a460000034280465000c008682d00d40c0709400c00d0006070580703800c255a002547c03442070021a07000802ca030511050700f001111300c41c0e08000720500740c510612004280a110310280c0040c41159400303d401110141c043d51416070580f5900c00c0c40f8031451203444801e9406100401c181152071028a40c5614444540b1841007206800c2c5c0d07140482c40740522099840c402e148034003550340030310b5650140c00c028000f41240381160311040c410340114480c0d1071040510142d603003911081901540c07003548404101400904103880c2c101215001a00c0d0700c030300c140402c2000100b844526021500465641e12440c1c5081c42c00d00b1864060213008150b840781c19190361000 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 576288992 1250 576287742 576287753
    0x7090e0a0b0a09060e0a03080c0a03061d18010b030c06181203030a06121e020102030d1d240f0a0204120b040b060102030414011809060e04052112060d 66
    0x55115a0031104001001c03811484d0200441e425460a071380d0503072180011100286d080f00b10b4503002001020860703241c000c0144101d01808041c1c10880b40351003100d44090f040203810703242e81c0c0260118030308860680d801a00342d80c01c030703035504111682c1a40000b00f000101c1c14258014040c00e801200019402c401480108241e8404a10b000e81c250f4400800c01003034480c68802c00c00544842c8403100484540c5072601c042c2034000304035645005480b01c82d076074116030080045940402e480e02c02803103c1c03000107503041401c22140701d12941c6800340000064186030051070702021134942c24003068031a00c4204c02c1c0192194000c20045186600f004081441c0d249400c0c158421849040d40d01c1452a2619001c0d410b204040c2020b4150740c000c1c0000d00c150f2400d00c42101d031511080c81d168420020000c02ea0100c10f00692041800314034144000c81c840340000244c038400c6010f6800c1307a002106407042848416004109a00e10329800c0c01405444009540710a401c007100420a40c0955019206c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 576290242 1250 576288992 576289013
    0xc010605041a2b03180b0918180f0a06060b030105010203030c0a0207120f02042405010c0503070b090f060112030906120207051c1103090a0e091c020d080c090307090e0a 74
    0x68022640c05071921700c14051703c0341c00001030f10300076601c94203000c0c600c4049580c551140685003907003461040010403092502540110861308a02201c00d64049904043e88030706da00c003000c2e20f54600b45074000c54a103c9400c01c072070482d5010b0b0b00071413a65850258825540e0862902c48007140150107002a20600c80c0b68414007a42c01013100260343c0006204110032645186542e49014016600c1039400915000c64070b400c4440a00302203100e41c0070307454040c0c194416628010031489010051003904603000a10402401800c01122116601c0305601600041440c000400013050180140082c1e40300380c461000c03074111000054180310555490904150010a4881f000300001c26000202030b4012406e1451105182c0610b150040d120301156600e42140580c02d070440c820300c041040c10000300030450b214100c80c9040c41181c01c00b601c00940343e68082c85c0c800c00141160020949140600c07007282c003030180050085c1501e43c030346221f000140012408072100da016003000300c5c01007188a9031 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 576291492 1250 576290242 576290329
    0xe070c020d051c110105161d090a06060201050618160c0812090c0a0b03060d030504030c180c05030618100801110c0f010605030d0c15110c010605041a 66
    0xf40200d00000c401c009005685018030b004042e030400342401040f54151591200b108200d00c1d01c00b1000001c2c0c401a4103460050112940100404007080030002440c0d100c44182d03103040c1c0c002c1c130041d150f40042040401076141b0001d4000c01c6500425040640f10500707005a14107030a010426101a4895494907000001d12590611a035020401c41c403501b403164900200c400c40b900c100c10750078550108a40e02008042d11300900b0700208400a050007441642c00640e0f1016041d40001d40300ca80e80d500e4618040c3c0b08810140c209051041c8050140080c2c900c42c2340090107101d81c40200c2a11405544000381142c80390120310140403400600a00032b960303260310900000d6582d0b03003000503040d2070500c0042c0c00c1200c41c0d240000a10644d0781c0030406502d000700c00d00d80000c214040382030100c1450001d901080705c0d1b0b8a4049540406000040500350144d001c80c020131403540d0b60018002607807103143c614542c2100305503104590f4582b140000c12062500030042e103180c60981d1810525008115 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 576292742 1250 576291492 576291523
    0x60509060108190507090b0703023706022a0706020712080f28030606083d0909030923130f020c060108151e0a020f1603050c01150e070c020d05 63
    0x10b40f0301e00700701c400313490b51a01d17004451061402400c0720820bc00d6441c140303030040c600754000509030358661286044041c2500c4001c6060400b902110030b542e0340d8881d81c0b04000243c06940c60006400d00300e01c0b80b00f001d4682201a04d881c220001d0b802c100e8130350045040714030108030140c01c031071030580740c1024a1207850592400075145050540141000d42d0040588142060841404841005400c0f800045192602040f450f140e4582082503888100d5040288000c0c0745c10440010f01d948895840111114a43c00c1c011125442d41c5083c00040314421007508000001401d03400c00d04194005035071960303050b50050612402400107424580281d0141c44240d110300001d8003520041444507411840380780c0304500d0840200103050b102c00c1d009016071110769000c100c1404200000c01105c410000707100300c4035400d0060b850301800c42c0d08602d0740c03080d80358031384040c0b841d00104107660034043e61502100c0c4115907442c2c1c00100d600d80381d0981c0403038000703203038041c620002141003004800e00d0300d01c2c8 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 576293992 1250 576292742 576292753
    0x100b0304030c030c0615080d1205130f1511190509090708181e0610060f050901050f0c010518120d0f090c18140c090904061b03060509060108190507090b070302 70
    0x10100201100d849e5003e240000b4a801c5c203000307140c108800d1401c07100754010f05058400b449420209038081c2d03107400c11170003e8200520341c400e034003061005100c1c3c1000ca000c0342c20200e00c60841292280920305200c0d4000303200b60702050010b4000c040e030a0b80011030100020390140a490410305000201e0040711144088001000c283e0340213000c540e61001c00304032507505091600c00000e2910300d110303020000b8400e0026607000c0503440390045403c0c00c14010050350341c50444517402d500034a401c840f40d8105038000744c0a00303e80384012503c10300c2c583d900c08419080285e0301c07480c90700400391442815903c0c2e40e01e250480c0011000c200342d50040c4a00140b01d00c2d422141c404483c182d44c25007003001c916a020000f0040070165550664001d44030070b50300d509066459190450003040202035071400c16a550340001c59180e4990444426240251407441d5140c40383c600641e480362060b501d41c80c45804400030300805001da40c2c0100d40c402603a01d401140140e42c0e025401c3c0941c840e504c140c0050300503 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 576295242 1250 576293992 576294013
    0x2010203040204050105120d03020a200a020f06270402091207060e030a030f030209010327051006120305070c09050f010311090402010f0e190e100b0304030c030c061508 74
    0x140c070804e401460162111148601441b414540310750303003008243c0030f041e404190320448500c901d8400c02e00301c420541a600541e9400c00095035401e5000080b0300c0ae443c801c0e000800c03410000c05071f4030301080f030750030007203483d40b5400c403c20710900c9482003150860342c00d000340000c9688003041f03d40e0903c00d640241103164101000102441b05012005000307600c026100720000360300401811402e00d4901d401601c98840c2c000480c05012044503c5215260b1050001151010102148012445003044422080b50805000d095502510406004204520529011030302400041c0312030381c0b1070107243e0078003078a0f4081b00c2c04858050760f0089014484200601c00c10030500c0820000c0c0c6411124009031b80742941c0028940704150001c1c40030415060340c11061034451420310900c000084c128001c1d41e0f07807201c06421003454110f800300712303c6d0b80c1c030381c400180c10b0111800c482c040c40c0c059036114111001a2003e48118200f404210740c00f5603219000d049105401c45c0d00000f8042040150984199 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 576296492 1250 576295242 576295249
    0x3020306091311040c05090406030303020406030c03061a09010507051501051003180303020903010b06120f06120d14040512251421060a05010504060e070c110f10020102030402 77
    0x4000b080004160258220040800c04982c80c0e182c50720780c01c507404a150f8440b41811581c0e4050907420941007400d1220200405406070040c1041e14500d40e01001880e0002000320140c680380e100b100c40c60030701a50000c2198203908000c180c00078040c14403138a811071030360b201071070000440d0b5102c10411001c00140850f01d449103030b10240704418942804450340d4421920190f40c1280c0c070040074143d00085130012a10290000b03d0310341d400030100764446208039100d1070614422240d40400d113281500144142ca4034111591142e01d40300c005001c2900742404c256182d84103558040840601400b0006240d0b440d15003041c2e00f00d1903640607249038000d122104500428002d00403140648840c001c4c4070401d85103c850785100390499a0f4000300d405860415802d0358681c25403e4680a5070042145000c55500301d18100d6205840070400039a55821005100405072500000250703191203000c0400d110305c8039050b04040042074118188046800204c54800607120507000d40d4010041100354038 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 576297742 1250 576296492 576296509
    0x203041707210c120e1f05090a050901120f0317041b141518090414070801050c12091e0a15090c1701090b0a02030a0506030c06180312030703020306 65
    0x4034034100030700101d81c1544d45003032603d0203840003020483c0400036005140d68010105088205d00d80c101c0e4255030080000410962140004501806541c80c0002e843d0400840440c102d9581c6015452019050b60f141001d10150520641c20048112164211140f40f43e0b0403c1c00345225a1068294070f0424107000c0030b03900d11398440421800b143c131004000d80c84114204d0500098442400d9403910124121040d074400e20458540000b454420002080400f0180d500444041070854070300c05c1e541d02d4036030f0907107008584c1d4900b144007c0c490b450f80e5101e02442d50b90810714100c143e07504000910311a100c0f18066401000080c4e200a00340c40c2446600e4508410145220005000703200342c075160044481070521a02400300b14070b810005034081d0a51121036161ba0081800743d041c1011000758002e50410745041103030381c1c074240100d081c0f8640061684030b45076015114508112005003181500c81070603d0700c54050081f404e04500b0019040025403141e000c944005846e41001003e000400 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 576298992 1250 576297742 576297803
    0x10180605031e04031409010908010204060305090f0f0c0d080705011a1801030f260403231504081c1103090c01080c0414040b10021f02040b0d0203041707 67
    0x182c0418003011a600803030b0b11001c0c090b54807170155548800401220700803030a80c8000415440400c1c003080c540e6068109a0198041004840c14900001182034642e815805805034503802154a11081d04044418224080c001c180740ca0401d500740c0c603201d080d607940301c00c5440e00030040c0142503110300c2d01145903d1090782d01d143d400f2203581180d8510a841022240c0a444a45096846001882002555008100d144040584a59403403402c5881c240b182941028401c84d02e00840b1a916400508010b59840300014800300303440365101c440c03460307001d40540da0b041031000107440521607440c0100d114588034015880e590f803502684260910103c42c81c10f9040114540c2030100e40300c0c1c0003080c0e5003039034141c10951aa8007a10400a4014502d901c420b80d00556101425030304643c0103c0c000c511500d8a0304503080011004071400128412800b0f00700480c0e03018001740c6040701c030075405586d00c00e104081904c60000b0700c2071440c082d608041d10031604c0000744841d101d000b00f2010307441c1640 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 576300242 1250 576298992 576299041
    0x206070306080312150609180402031b30010204030f0b1012063210140102030706020c070b030c18010e010c030e0f1009061e0c021018060503 62
    0x1810300d5108100e00e504c901a10b50b4250441c4d40c40905615610a4100c07040d1081c0140903917100c140d9004c0c4203004500c00c460aa209004049200000540c000600c0c0c0d040107008045155265505103a48104201320391594490601d000b40c038540460244001c002940c002c01c07101c0d04101003440c288501c0f01c001060b138060010540010084041e6547ca04640c80303600c0702c1c010540245400c02d104941d40450f155007180ea180c952484200d0800014240c002c8242101d44850f45840b14603101c41401500169401030b402049108082010b9030301401c100350f06a001e890329150385403100d42403078200f61418504031800140c001101084040711620003138080c02e24520510a0b1000640b044403181c0026060108401800b031580e643c1e0391048104010045c01074545001d00c00c401044030781980960804104082c013404a944881d45c00d440508040c1d650350f44262050307a003448465509040c0e10424030440c0707070488455100e20240701025100a80eaa01e4680c40c2100354504003100860381c9608 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 576301492 1250 576300242 576300247
    0x201021c0c0c080c0f100b01111501120c050301020f0a0f082a0702030a0b0a11040e0c0f16030e090105011706091b0d1410060522030204020a02060703060803 69
    0x1c000390007103403405420360002545501c0b1010076044c103050001c540c84150b040d004402c40011140803030f6006001503102a038078007903503020b1081169a07480d9040310707007800010304800420801400c0708901d5903c511071055030b584076942e480440d003680c10410075040100c50100f0010071031503220504040c00d001c02d140c41101030400c200100d200c8080c00c03d01c0f03030101c0c17610060004580340d10f404407038880354081c0c01c6507181409070074109501d4030250307241c0710b00c5810884011905c4d0100d80980e41a070702c010014540390f0711b07001650744150307000c1d9416002e103280070301030401502e03541c104c4400301c103010ba00c3c0c034010016030408011400b10160083c0f4144411407880d100301d00c4d601c561055004c141500c0040c9261078030310328196030300700d40e00c0f0300b94130b144000559681c041070507003010541c40f1014881c0030294686071100030048183c0d0290b000020303024044003403400c20030301aa191221808080200c40c6072240c0214003079034405844100580e002d0402d00a803283c0c54480e48004140380c0c0081c60 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 576302742 1250 576301492 576301511
    0x11040e0d080601120b1003060315020a140703300b060a0c02040c050423040506040509101e02030406051b13060806060c2406030a1a071701060201021c 66
    0x140070300c10241010f810000c00c500030607035002c903a912843c0d1081c8000c0400742007004902005020b00402d0208460b4004452850b0032031034158001d03030303078103011507101c040040764034106414154000740f1080e41004104103500d0500c4991740c00b41c0400b4590140c0c9150b003c03060105c1d0000307480d815880c560203880104021200305510000f0803a541c1c0c2d0444010961400140d0101e810303004940141c0d54016903001c1c2607200c11018061012607200a5030300340315981d50a0100400c036502190468002d800003000da41250f50142d1000d16a4250780c4000c00c0d580c0e47d45648072003260411034040b10b61965807070610559612842074031a0703e81090052501d001e001c6510303200100d00c94800e4006201030540070606590f201410303a01501001302c00c840303040c6a024030b0b140d000a40030040d148001900c0002c01c401d810041441717800e00d0781140d8040d40e480150442110800002842c1208204c484115801d221000d00c15581c001c6c0724a03400541c80d010740b4604000c1412020030207000035481c01c40d218 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 576303992 1250 576302742 576302747
    0x1b061116060b102709020c1011030c0403120c061b030b0f060a14040801020c07050a060306080304031101031805010e2517030c0303040309030b0c0319050901020408070311040e0d 78
    0x41c10f0300c504030080185a0003100c200820a91a0342c01082e5071741d00220302d072240003a0000302d50548031a5040f0a021a05a65030300c145984070035a000c5c490303c4001c2209202090035141c401030380344080c0c9080c0a014101351110700032a28005504440101803517940c985060703040c0104542d543d000c8a1001d04c02d0a06000506144260695101841601034a036443c0c0226041503500420b100b40c001d65982108450942d10baa13014000e01d84503020401005c01c1d000d220307110312400e540b90400218509411519a40c2016500c0b003666410035482e4046980c0f1001001c4600d00030324450740000c00c2528101c0d4016040c401e5070003c0c07445a40c00a94901600210710640d20110355170140da4001c400400c1c20348a0441c420f810028519210010a01080541c0003404070100d9000314000b000b10f03114044015003600c010b80b0a0460700111520025025140c0c2c1e01094100302203074001450555181e01c2c047c10044184e105461081440406000c1c60810303004440c258014007014041c2e038013220401 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 576305242 1250 576303992 576304007
    0xa0e1908031006171801060b0f0c060f0108030904050a0b0607060f05130309030209091c0e0108150f0f01031506020703061802010206070f020304030b09160503030a1b061116060b10 79
    0x40030307981c0c1d81700c03442c20040103082d0300c40c2020708004244103558080141d19107005c1e0b4400c050040551046000003000c0410036401141a54507900140d49080320100400001c0d09000d02050601030790355035548160f598110080851502c02e000c042510b0300c019603e401184c2000b010000000e0306c448002002a901025241c2620b034103c4413800152212406545001c030004125a529890a01c00b82d40301034201c804820014000d036942900340c0e4030804c8102c0310000e000f480581009644964000c103280c20000201560018540000d00314400d144800b0b0781030555100d0805038109070014424403505004111161104a0300705440034030340d50000b599039000070540c8080240c00005413820341d2080c02190000c6801c00c900c404d0764100022035079110741c2c603850404002c010390540007516080102c20355000422989844087c808211800213401c41541c0c01140d1641e910721030340e0703040301081d4060101d40b00149603510900c40c2c81d103032500488006a00c41e034070689943ca0540303a00c42d4005003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 576306492 1250 576305242 576305251
    0xc0b0703060b04380403110d020d061a0411040f09050f040f080c030703081e0c0a0f02100f020405190e010b070602190e030706170a0e190803100617 65
    0x6002c4c9030608a0315000d9000901c0c1842011140c08440d50158600140009801507034040d00700c4d0441e00d1400350401524038074a0038001c2d00300140c0b00740340002c58040d502007007050000040520f104052000010111505221942000840420103100d0301428000640c09010182010003840c00c2400300701c048040001d02c014401c0f140340d00807030308201c040320942d5540324641c0c0c01c0300e40780c100510b8083c000030003c8035040388420b04100d809000d2183d0205a60203504101e407100c4c5802c13812082141c0406840d5806402e5200d8030501e0400440240306204c2481c5010000513191414501003011545035450500038072001c00805028207a442400700b0304544055504554403016458284d01070300074003c449240b00b080d00d80b02e0a2498102c03c105801c090100e055407681900c03014143c0300910350480c4000780400080004103114103c4e489192450241ca04071030408242d8203041c0070070390301408101d0b03100c2404803d000c03101d14020300e10000760a1a0604418005a8100192980a0042 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 576307742 1250 576306492 576306509
    0x503030f09010c0c030c230d02040e070506030a05090c060c33040b01140d2015030106020c10030501080a060b0406080d171f0e07120603030c0b0703060b04 68
    0xa420041ea801180c0d014a001da00c02125040c1e244d03070381041540c4089900c6030140c41c0346038180c07004601c1e0000010a06060700240072404210554003031000501c05800d0454240c8103810011980b50780301ca000e140b044090820100b8149440c150150905c1c0c0c044444502910f014003064400280118220825001d20244a0500785039054151108480b13001801400709801c4240300c2071051020420b4103882c0040c80404100800e201484580c52504c00c1c0a03048541058a105000c500840d51302c0708618010400c401c2c0c106040765481c9564403e80c00440564031a804000d0982406050381d0358038961414104600d45c90403d07441c2c0c03106c410800060508da600c80f140e00055580f07038040f001815195040b1844005c82d0040509002c0801c1c00280d2040810800550001c40450030308100040c4400030582c074600d07000310ac455401d00600704200b48251003200c45090324080c0716460085000396079040c0e00c0a058100822201c0020301888101820200144107000301d0600315000c0301d02c8803 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 576308992 1250 576307742 576307747
    0x30507030f0201020d090b0624040506030a0908130e06011701051c0605150901080d020a080c010917090108181c030b100504150e2d09040b01060f090503030f 69
    0x74002c0380217204081680302080e2400414805101c00300344245c1c49803205075040c0c04145140c08282e0000f041c00380c41da01c988130f0100028080d5040c401c02030340d0010842d80c404900c040050782e5a1f80150001e040d480b014880d621810000540d0600019410410a0814801d002c00b0702903d5a408041405124000c581ca8030100031031000395214012040d4000e8020411810508040b04a104540084500c2443d42800204010030085095002420683c000b01031240d543d603a20443d54214565902095503107945a03c041800650340f8614030480e118003076a00c481d28030000d4144071000d410201000000c8600c220341480000d0108101c0c18000924003108182c12012400360096a0a05070092040c0705c81015154204001d0820b94081c4c03500c140c0c1e0010484030445e00003901c541c0c142d80c042010740305410800c00f10310403140c0618146200080303030088400030480c02c040544044035610f17004001013040540c0b0031020f011503515031500060542c039040c0003964a0050060881080000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 576310242 1250 576308992 576309017
    0xc03040827150a03060512030a0804080409060306060e2d0a090813050301061514090a15020606090106020114011a130909020117060603040b10270e0a03050703 70
    0x100401e110000c80000c060382030601a54a021406400c074506102c0400d040070408107203403400c2070316450721440000086040240c0380388101e0714240302400c182c031452410031011070a0317603071401120041c5000d15000300300e4030701c0d10b1106103200074000c1526070131720743d000303000b94240c0303011408401140c00e2040c0701400c68442550b140010100c07090020140e0780000b61443c0c06290480d0408204d500c101d00800c551540c6107650030010054a40741740000f194140c06200c11140c83c0050301f400803000d0f001d03581194403400d8020051045144801c09640724100b08405498022002d6024004c144001c4c042c03600008100380082606000d100032210814007003010b0354140d40c00f5908281d448071a40380500350390394141802400403a00a13800071348404144c94500101236a1140192400b0b080720b86951399903100d44d22600000b034a4810030014001e00000e8400d07041d0b1400041c50060741c10201d442100c61915011a0460714865100f5006603d5200210b500182501c607040d415081c0740c540007070b1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 576311492 1250 576310242 576310297
    0xb130302011b080103021002011413060603020405040b06090c0a05090105070f0b0f04050f06151e0339030c0d1e150c020c060f072d05060c030408 64
    0x9202c04036030781c100307441c20401d030455034401143c60480b03000b0741e044840800e81d220100d00340d0f84403080c411410000c50003c034140303911300c01c0e42016242c0600c20015000d6143e070700080c1940d20554045e210008903038144145403a05004043c2c000c1d07a1251800c0c548685804050500c0c0030300c0d03c50034107110b00407a8a405200c0403407043d404290744610850001c4c58078411a40c80c10105880c03d5a06104e1550048900a000035129000f91244100e488004a031141042080d0000c20070030390341c40c90340c00d10026160b1010096203004419003c4041800e00e8003108409410a01403000d54144d0603000b800440c44d04c001c81c0001e248030050342c124903110458203000803004c1450a20303074100c0304a9110501231100064400c22210441c550500070007192040803030381c0700300300b4030095403041c02001800495081e4074000c4c41c203144100c0c800003014491001d4880c00f490100c03d0350005040001c808020401f041c40503980c07242421741c01d00d0640c20f05440b0103000340940c43d9818198911491303115407910 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 576312742 1250 576311492 576311501
    0xa06051312060504050f010e060c090301022a1005010b0706090203030f04090f1b020c1002120708090a0b07080415030608010203090f0d09050102031806041203030207030f0c0b13030201 81
    0x4141c41007955491614078203074004000c201d9040d07900380500491008842d1040c081c440c024804000100340588400c80e00e1031265102c5912164076650802807261002d449190704941d208180080794400c407030b104401030800d2405140d02140d203181c0b00c01806007800c1c000644100c1a081007000420640c1403012a183d0b120f0450418580c07240482c000407100c0c942c1e000032203448001c0384c041c4441092502000003540d280501c3d400580c200412401c020304011044294006440c4100e40d90400c1c1060b0042c001c1e84403810035104040b00085008035820031402207030045c981010b14920744a12a01d5001c00c074001c60042503c402c40c62498451504d109400080c050240200215500e0400c46c250076642ea442d031110000f240164035242003e1801601c005044600c10380180d450030142d220024500c50034a0b14899000340140004120440361140c059203641c0700703840041c3d850710300e8100030b00150302c041030300c10401c00400e100d000003404a6101640209a00051600c40c0c08c0c0c1d440d0580c00360 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 576313992 1250 576312742 576312749
    0xc0f1e1219170f10120206090f061e07140309010f14190c02030c01081b0c0f07060507050705030307080703032f0405280515070c030308011509050a060513 68
    0x21003000b030902c0001c0a031103d81c9400742c8001041140f10507a80c0c400700402c2c1000f1140654081c100717001500950a020b01646142e10f070040c0b035186000c4051403c00300884211246106441e40852809c1c100800344100900c0d4580c031000850038001d10b131300020858141915000304000460304000c01c11000e8005494400c900300c2014882c4c0d1101c0710000341048820079080c0d1003031050068054403075004100f560b0183c080f10341440c0f0095a41060200070b0781c001c2262002d1449040006503040609200460240090765101d5a9030030003814140c3ca0a440b58210901c81e0f001000902d0004203404102c071415a890b090100e01c00031060001c400342c0d42007003040f0704a110200d0404192407075000003002600c01c12119504d07007500140d41c060280207801810300d042c11020300c06002c0f6142120000d542c290300e440e000751401c11980d540f070320300403455402180400d810100500c40c042c618146220010520f00e072141e6203a01d0040024011155482003100f400400101007219540d2551050042c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 576315242 1250 576313992 576314027
    0x312030908030703050610080702070605160b1e010602190f061808190206010320060c030f3103060b240c15090601090c03020c0f1e1219 60
    0x2d91620f1107026015040c1201e005100b80c4801e040c0d40d84490003500354274013880b04e03940245407841c180201502c0343d601c0302ea00781496005601c140400074001c40700c81c9105804d81907024588038044520020f0021040c2c0182065400c60381600340408122011000d100c0e401c46040180001103090040082c5603a071075400c005181d40d0400300038011884000c0c05072082039001c540d00e505444030201d8a901d400e01001f80b080306c42c90030307801d5112440b0184488401e03004000a01d0048000521451075000d16000d60030200040795960210300104100c00802910440c10083d9969110b0305142a46982c0802082180d48800c15100c82e02c03400c0203941090390308015070380c50081a0b40704210680203201d503d900c3d4400e01d0b912412010040c40d00c0e500507000ca40040900b0b07400c0420030405001014059402c06a0900c40340d40340640170800c010341da0f034001c4040d20078a00b208109041d80c130140042407400381e000d2500c15051131242d10803a000340e412010031003800158540d08940c03854820242c07289 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 576316492 1250 576315242 576315247
    0x709030204052e0b0708180a0306050103050c0d03020a0308100b04061e03060503100513020d24050907030611040306050405060a051f06080402041e0207030e090f010312030908 77
    0x218080030500525054040c140100ca00d060405010030f90090039002d00c0c02c000c10284a03400010311107502134502c03410441090680480302901051003684564816117880351604010400e114080c000300da0500025100c00c4845181510007941d80c0c80d60340e50080820015500107800600d0150700c0b240904a10000350b6912984c8031401040c10400c001501c00ca00c6c010129a8100d600911501e0100c44018001d4070408502000d80f9000f0a0002c0c0700c0c01143c40f00407042401655040440505a0b1040003011045014102c0406502a0803d0210700c2d4502c0c11302030000304c000000b40d80c011a5401003001c1411501200240c001340038907480141303100d0500b8140820001c0105001e8481e0101c03d82c02c1040b580e80c400900d8850001d40d290f1071904000c1002070101c80d100f0001e00e5880b6001610224a01407110000040928003819401501d60f0108001c0101513000d4040070040030b08803504051400c0c00848580705c03001c10f110041a120584c02c01e029140c0c041e402c1344180a400056164 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 576317742 1250 576316492 576316501
    0x61b0708030a0305180d0807031506110f0115090c03090506130201020f2a1c05010608120415030c1103160b1e190914031e040b03060108070903020405 66
    0x1540c03030b0024100034002c2030a1200107203411000c00009904854008001c2c1203030b402c014010380f107010000c0e00c90010941ca41e0121440c0c10180625031008051a1361548140e00b003641456081c400044250a8544d04000c8003002c502d1006004200f541d0084c140041d1901c08008198001c111200c030040c92402490204400241e02c510381c80f4405000b0780946081007941541240c454400806440043c210302c0310f407182040c400820b070034202c080a40803018100400c498003000b8102c10780d080300d290303444110038420080140600d44550018045160809003020420403250a006503202c040540d2040e0840e4030511847c51401c1100c040c0060320369405018055146209844000b40c84005601c3e0108442d03a40c984018a20306084445c0706016403141c52450b915a24203c81400316a6218800100407e0094500d0316024504800641d036a024401c40790804c110b40060030b040c0e0400c1880200040111642244d03842442481e00ca251a0354448068400b8400d940021350001c0c41d08c4101b0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 576318992 1250 576317742 576317759
    0x6060903160e09070501090b031909020d05070f14031c030b06070803010608010e0c03040605090c120304050906060a08070e211b0603150d060f020c03030106030f140402061b07 77
    0x194000c40e800f400b600c050944810040d07aa0502c1841600c2d0346072010000a0144132103000300c42240450f2100104100419400107090312182c5941543e0075000a5030070048200b043c3c1c0c200c0020081c0d19200080524001e0002c1d80310b00d90030b05c0b604441455440042d00b40751003541310202c1c01e1001803810740c54443c14102140d00b60800d00420f00424141300007c44c06201c2c0d0b10406210b110201d41c020700c5c56403280d460714003610340906081d080c1d1283c158820015030741d80d030000d803900b8100c40003175407114544010014540d0001e8400c600840007002402c950940c48007003654000880e0038a2503400748100c020949046181444580f06101d014400074001c1001c40c00d05105d02d001c00003690700980c2c0c8001c02c03901e880140d8440406c040072040f90b403440d05200080500280c05803000042a0300307170180c00e8041c0d07808400110222b4000000500540390180705002d6400c858080030056041030348228001203101420181c8030703960102d0000440001914045e140c40c6440007038600042c3d40780101d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 576320242 1250 576318992 576319019
    0x4050a0f0303020f03040b0f0c0a0b071205060904080703083102010305060a080d11010e070e041a010e010b0f0c12040f09140601031805010e030d0c030209090606090316 74
    0xb01c005000700708480d0340035400007055509403002441c00c1850004103d0342191903030711039014880d85008010060010540040d001d40c402d010744d03150404106610089003044800042c020341c45088880306100104540100b6680e9155040c00c1040d61a00c6403501c80c00304884d41c0c0ea0030f0220880d00c01d120a058030810709076000480c402e032001d10081e22540200880032074075006603150340c0c0c00141040b54461240404c10414111040001605c2d006880302da403e04119401c09001e0070140000e010070006817640031003a10708000c64054165041c0100d5104061040c41010f443e80004581040c2c03030200c1d0750850b0400502c56085540910420b4018100c540152054960301c00900b0400a0796421038020b01d840041c0300380742c0030000e03924000158000c081100a140b04aa0102507040004401b4414403110000c5d2000a40e1580e80640b03001c000d842c602481c2804160041c04240320688440b900035800c00710850303c20382c544841d0004a031400403003454400c51400210b2002030014007034250b = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 576321492 1250 576320242 576320249
    0xa02070b090604214410350c01032301050907030b0d03081f03260c03040603050114030309031519050f100806060d0609050304050a0f 59
    0x1002015507502440c5a2180000c503405800d12074000b00700e100c0f440e0360f0213001d070115903030307041c0424606070102410030400c401089200000741c075180383c40480784607201d4480c0304001048200c002880c0c080c501c00083c014903c54044085010103c0c1500c03030030a1301c9014610000c01d450480c079211103100c06076903000c0314203099000c01e03d00300c50228001c0010050711440e030321121900e00c40c0d902c1c05e81400080c68004050408040e5203010501071a5904040e07084071034025544c8492034101010700391018807a00c18a00443d5000400400004d503150a80c00d45450160806110100d100714005e0a00d00c00d212032195503010000300444c0c43c640641c0024180c80c0c2c410007407400150004103244d40c030710500740c1c400e5059001c5030012003400190f4074500e51011180030b90740c001c0840f83e00c412041d00c074140c5030141140800420803048240304200da600501510008149078100180444c842c444055005010b103a111080301052090401c02c176030042c4000340c401032180d6603601035507243d000c0600 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 576322742 1250 576321492 576321503
    0x80a05090406080601051e040e07121a0118051302030118031407081c0b091006080603010b06090411040812071203021c020901030b09180705031212100e0a0207 70
    0x400483e04000018009041e0380025000e240c44075290b424503444108603e5196602585030000c000c1198828400c140041110441c1e00d004002070b45803591400001803410b440c0100c1002c0100001e54032810780460f00c5216580c0086c07241c444010f0044d81400c01c00000e5015070800e03600601d40c0000c000348001d058003c1da2459403007954881c0344d1204e849003000251101c40b084c40794051105244961030440420350703c0015001c07080c0000314060705803c4454030024006003108020b040c0c3c0203030429134416811402000001102c074002822805001c0107517000c1c958074062088000c0d1070b84129809003681c1c9007200c01d103003030301c40a00b481e0f41d1000d40200c5d10401c88001c03542d01c190003402a03983d155080c1307445648407051881c0a200030b4000b4140c550402d03440b03103000c0900d500c861032040d00030b081c1400781ca101d51020020180c544960340c0e02ca54001e9211000d030340c043c40e030030800350b41c0312190b1103602002d65115560740c600890102c4d04030315495840f400c14400350640d294010400c2a200340d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 576323992 1250 576322742 576322751
    0x2120f0907080a0f02090606040f080c040c020a051b06160c031101020f0705060304060609020d0e240135150106080103080703180b04060210051006120507020307080a050904 76
    0x1850074a403070b20f02005005205040c40c15403d001860680a91a44110040e03d035030b0074280d0f6592990b008d00d03c2c03035110019540141d00d416016042c540524036914200b40024035001031141c0d20140c0d110302440d503604403e82084000015030303880104a8051042c100c0c41c40c0b280b00b0b024100b04034510500c0c4422980351108414100b1194004241440940180f2002e0400b1a10700f078180000c0380e100030001c5800503a586404900c007030481c805888403001200c40029159041c0701da1a292504e1050810030000c00c0031302040c02c05e015450510306407140d4140c048081e116050251621491520703509910060100408204200002c4c51191000070740181d000d150740c1e1240d042e1004d00c428000a0302800c1c0070404400030902a50000e15482c005d101c0ca42c509035a602d00d4000c40d608550840c80068005e01e40019802215004850300401f000b0240d00e0161300e0007502900840a480d00c060f140354403800010103407070003481540c041a8100c1d8a00356a110840001070165001c962180c0c420f0f480c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 576325242 1250 576323992 576323999
    0x10609060e0a0615030506030c0607050a0b01320409020a03080d050f060a03080c2a040f020c0a1b1503090b070908034f241202120f0907 60
    0xf4055481100c8a52403000541c1c41c010300f0480142900514080e014414880d0082e00c586a030380003440c00c01e0242010302030502461904045018040e400704058220031040385503d5139440040740181c40e00110741c0c624a1135814045805001e100c60003035400051143e0020901400e64002c0500306215081042995a5003104c04400c000c2034070b615170026410103090000640c014010606280c0b404100c9485c004000c60074002020164101d9140601009030b010003401c00d030291000380b01c0d5103e8258107051400c8a000c2e40c612090601400e211003c1034226600f41d03c1522160107010a5100485072a640360b00c05009440c06c02c9085481c000c4910000e50703080c1c45844e21405540300c81740510718001d000c9580c008413046125443c80030206100c01480c42031108402094116000c1407542400304020750820201422503200c143d032608041c0c0700c401c0407002044409a00301041c103140200051103010030300240147d072911502070946400780010301d84500d80e414410501c27802103d225985 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 576326492 1250 576325242 576325261
    0x1219090e040305090628021b1507021908060420010806060310080f01051f030c06031508061f080706050d050735010b030606030a1d010609060e 63
    0xe11841428540c00300114000a204000034840381400400c1d140c288110051700c0c0a141c40c42c07051190203d0b06d0350303407071018554050248200401440300340d103140c4490f560104d0b1041c901080811601c00e00083c44004550b100c140d0402000540b0350107041d519150203007a03030794010030b45055520014120000c0c0d13030703641c030401c002c200c0581c1070352584d101d13450302018809140c0003e891084441c0c070032a40070a40900801c0a500513450310700000c00d00f424404e55044822000000f0920f030841d2034003081c00421140540301040f00d805160005011001c41d018005071031182e00400e40c1e90062005208080071400f1041500f89244a02c0c5040c456803036012696401d00c41c4140000b00c0e60610105868a105a1000e648a1994149981c0c140e480d0203100c40b124890b14501100185404aa0001d002011410038050310807588524a14148500000c600f40001401c18802036112003445102d000000060710a1071034480c000d01202c5c0d00c4401c090081c00e6540541e400302c002c02c0001440341003 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 576327742 1250 576326492 576326507
    0x6011a030106020c1e1203070b130c1502010207020406080c03010f020307020c0f030f061920030a0b0d171b03070c2d0311120a0c090902121219 63
    0x551a40050007950544003e1140ca40000c403942c00d0a031001d50805d2480d0b407034401040d00e4400241000e0f550310340080c640002201c5010380407200005d54250304800107143c51100209980c0059000c035090000440704a0191007003400c000d422a04101000940700000200c032664200100c0c024401440c3c2c003141c03001280004c948541c01a0f0200c0070740305075410424030502d82c94901800351002c0c020012002441c1007400ea8407038000080705540c00803e03c403144501030f21307034540c0c0c01d4070069034983d40c0003a035907400701400405850340d960004150319610500510501c5520003203800c1500141038405109800c800920b902401050314140400702c00481202c3d00d40d03500030000559a810030b08401400114480c0140c0c0e04490819180821100b914080005510070182c0c540c5d54001c2c90140080340e1400c080004c529405110108002845e1400707031029280140320001f20014540005120400300071580300c0603001e401354031360b07421001e10018048140b15030109010030b074a482c4111480d1 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 576328992 1250 576327742 576327749
    0x1a1305060a182a0f0203090102060103060f140411030c030105041a07120f09140c01080c09030304120b060109060507050d05361507080f09120a030206011a0301 70
    0x1c50204240005034500e1040c802100508034000b940816010845100309100300324543c4800300710039031844182e0f001e00803082e40100b40c405103090444440020390740d00d40600000340317002c0e211070580c00b01049075841810300c000c550300701d001c880c1007a040040c842c803865034400e8080c2c0202e4150004906050142c1401240d01c11700002d0210444c0c00f444844100c040c08990070010b490711007016800d05809903400460300543c0018103166249030508014204250360a0143c02c0104005500c1ea0070480c2d840c0c1c040d00c15003204d5650381e800c100003425031080f85c011988010b40310b41d0042c240304c4418150340c4250401e0300d40841c950340b500010303107080c09207000043c002d9001421001115100d44040c02480380b00e166881d00002080c036424040201d9804004640e0050050340a0245813150455a03403c5029007960700d0404140c0700d61403544519042c076004903000150015890700c80c52000300301d020b9140140c845101700c920300203445002c01e00c168054a09151580000d164074001168104c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 576330242 1250 576328992 576328999
    0xf040b0a090902060c25211b0b0d02030906010906080604120311280905012c0a121106180904110a140a0906060507020915041a130506 59
    0x10306190044103070140c4489001240c00400c01d00004082c0e40e02000284010b8021081c0c03c40d0101141c040300140ca400785d03100c030b07051241c000410b030182c01008000c54404e5800880418002241c1900c1c403040c6066540318031484034000840e1022044283d01940c0108400c60540c3e0261740e90707181240940e2aa0302841c401c541000010a0010342049a80a0080c2c1c0c5400d01081140d083c42c1c00104a030030981600c40714a041b0084011a001942100c00c0b6004150070102005410480001c1c0517a800b000c0c102040c00100c400000e05103a1150841c924080040c54400c010f0b868080700301c22165103010440d482e1f4442d5070084071b50f1424105943d40c518941c40301803680d07074520080011480780a00142c1301800201c1e01c0c030700d154552034000d10203000314021540c402210304080c00038440903a40100d0b000d51820303109003e044d51000444101513012501c0105d1503e6824600c1420701105a580354090b2800400ea480700100321030b10116180c08a801030a00000440c05105540c822194540e0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 576331492 1250 576330242 576330259
    0x30c050d030e1e0406060e01030b090108070b0c01141303021002071a07051908160801030803040b22030806011704021008090a08030f01080c03120307030c1101090c050f040b 76
    0x11070400d240b00c035402d048000800640f8502000c0400c08958060300301a00140361100d0f117051558040c040e582a0b0101030303803403e10540c0340000070307505c800a42c003508000c4034001074040103140c02500181009082c0fa0031541141c02e24281d03040d204030b103800c02100036009618001d0201c11051081d201c00e0b581200340400c10103c1842c50f040108402000c20342070000c248241100380c00380d0703502491000350030340340c0030850b082044200703e1001e0100840b00c1040311060060000494040940ba08540c1c01500814540c58600d9a42e580a59004044601100714800d070350502d80d10489540c0070b0307042038031b4070404d102c2480c1d02e040184404680103174025015100ca072880f50b21821001c0d07800728615023035078400d130780c2070342c40368241c0e030003a82e4140e043d82001c0010701c9103050901080b51902c46c214000c003106803030300791120400c0c00001c04840605548200c1400342e54010000c070780c02d10010500800201e46180b918452209050154034003800d10600c1c0c031034003800d041c890b10784000c030300918108 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 576332742 1250 576331492 576331517
    0x3030809070b1c090b0406050a05060a0b07110114130e060a080a0314090d050a060f230603070e0405150907120605100b040e070e09040201140c1501060306030c050d03 73
    0x1060303603520f610340c5420340d80d0b94492000701d180a18080e014610510000c1600d092506d01e00303040c2d4502401e0640b00f1355107804108481c2c0403035000c07a13134650341c401c01d611000d0300c4120068036054024001a11020000505450111003600d00700040c1d0303401c2e080660700d58854500340000e00b4801e00402c8000d030700c8036082c02e020078002c2c40c80b03001c0c1d80c17801c3c0c54441c5840c4402c40424410b12420300304071400d52080c3d08440401100d030040d141103034945c910030007459814201450956001e54004c079025034911001c2922502c061000d80c0161540440c80001401c01d0305c0e1183d0758102006481da2024801c0c004103040400120b180b40440e9070600300100c400c00320361948001440d018105402c0500010303000900c0c03c0406003c0d03c010010305008071203624003806d01a14541003c81002e214000510130400141c2e0030078440b0030450000c40003540c550040444131454051600d2268070803094600002843e00d515400280a480c1718038003c1e22810740c0d41c0c0522041c5031441d180100454050032000c1c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 576333992 1250 576332742 576332767
    0xe090d0207090903090509180f0706090801090803010e090a0b0f0a0c0e100f090f0b030906010609050907050703110105041110030608250b0c030d0e03030601020d0f0507020405010b030103030809070b 87
    0x150040d5141240e02d01004550510b545070800103402710344260007807602001120381049401c401442c0b80c3d0000c1c80003c43c6650b41c01414030050040c0200c0e19220008030390032400400003034865650200800c00142400b2980d10003001048804050700e50504409a145610840c0c050340c9102002d44203c80300c03140341505942441c215042c01e070401039541c8001500c16003415200700100141c3e840980d9034101184e100381045c0058100340103000e001401081a5211141c410b0703480165032906a48a0109140844d104180d140d03010280758204001e02050121250702c8280c12041150720352500201520154107403585440b4407080e603005220480001c520100e407610319162824a001842074540c0041c110a402504070b0403020307400480c1e0b140a941284c07040080e80709080c00210704521348400000c0d95040415104010810000c85000c1070307031b00039000d990b20582c2c028414451907844040000c802c0c4c00920096000a4254010134101c0c100407813900155121a100e1030310301510f0f075404 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 576335242 1250 576333992 576334009
    0x1b010305090a0213090b061002030901050702012007090c1107091109180108060c1602130e01060b0306031005040302060708070903150e1005060f010e0303040e090d02070909030905 79
    0x200c40c118002d0420328001640e48007554881e03071103040c80002d00b81c00c0305e0524055440380201540e0203008140786031540242c0001c141c0d4100700d401d207401990750a0324401210b0640301c601d0900b400011400101c004201c000c101142540d200a4042014041c022000c40d01c4041e0083e20341580c0e08417540500107109141c1043d0a120801e04407203203070180c4c0002044151854140e001100c0d01d991005104880e801d0150705d41000e00101a0343c00e00641555201015000c2c4100a21136203846540400c2050309030000c3e80c2c00a01c2c18001c00145548002c80d2602d540300701c41017840390041d038a12500201306403145a0141ea0136900800c81c2d6903a0360b006882e19803003d0410710a120980380e001001568482a24181c04c410480201f01c590b001e10b040c0d49042c0e001c100b07000c4000c0c1403804000c1a6102c1598049421a0920300201c009000c4000719040d48a10340080c02403845440c100024000000f8004c0c003110741e02c1c2e0031542c1880d61165064111105148000e0004510701e00030049450052907 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 576336492 1250 576335242 576335251
    0x1a0901050f1309051e0c0102150c090a050a08250b1c1506030e0c011d10030906020706091e050307060509010e0a031808031e07080c0703030804020a081b010305 70
    0x10009003c025980b00c5920303102c040c3c10140c51101404100b070071002000d01040b010b200003800180503c0e03158924040100740c004000b082800c07004281c100f226510340b043c41000f85000b86c54015520746400415450703c02e5041c203080802d581001103080c4180c040e605004031005440d1280c10702031303820011500412418600000d59469801d8805080380300c03c49800180340b2514006804401d421007141010041039a0506105181d50064208000c6148031100f0b000c0468611540d81107220080d4018061008082c04552000c90400c0030041903030b1040314524050320448032025280056214028280100241260002e200c0040020f203a500960340016070a80081070b0400045442807030050081e40035400280d50780303440d1010a000b06800800b074000880a18907140640e000c0d07014241035505003200741100080c1c1c0310140b000100179520148040010345417040d0742ca040c010608481610160b20802c491040080e01c030342d00045a100346030178165101c00d82c0d4035010056001306801403 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 576337742 1250 576336492 576336529
    0xc06050903150f010302010905010f021b0310050108030a08011509090203060409060203070801050922020d060912030f14060f0108061f020109061404080712090b030103061a0901050f 80
    0x86039074020020460710580300f03e2402154000355171650000504904544e8030140c1403129254a1302d408650210350300010f20702c803007444201c145102001c6490000110301c1e00f90304515080011503030744808802441c54207a1030780d4000030781e40c0721070680301820094078402000c0303019500704001050203034001d140c1c482001040028500312a0301c0e404c0980c0e00440d915000500c00f0300041c000351410788942034200c914803020400700500900030b11500c14215101910a04c103904050041020b0b0f030b041040c3c100c3d88000c00d41000c2801100c050081c000205100074000d00b410301c4500e0f40309414401500c140b20041400da02c03034001c43c00640e40080702810450300a071078130142e0300c9a4003000c40c1580c280031560780001181c0c1014281078040711580509010031076145001e00c8045980c03082a10340351034111552446400110100340c40880060b4003280c2ca000002c0000810f0000c258095504076042c1c038111035484181d50200640e12200340540c07075100c0000460a50303107042a4008090000c101d0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 576338992 1250 576337742 576337753
    0x608040b07090b180339120102120106110d0f050a020708070f0501031a010c120e0409030c030305100605160206131410020616030b19060504060215040c06050903 71
    0x1c10001c000f9a01080000e411300d01d00c0c8001d1103242c1020405802c0c2001c400c891280040303900c2099460103200000400404004028032564694075611781000301c001d598000c40d80c1d900c8220503222104402d10560303002c1010b2541441c041b00000c914040c1c0c0418070390712100461030783c203400c0c0c1d01a0806084501140b04010340440c480004000e041c01030302c6c0d0200340f0601d840ca4000010180c0d204148071400e01415101104880c1e6040034071010741c580c1c0108042d10a82c5035410482e0345515041c266a4001d007040c8001040c160401400c0070041d02a50302848117580c1c20203116003031036036449030390700044003085210180e0709102042059030b84010189440c240749085010752914441c0c0110031010321250350b0340c0d550b192402420500c0c0f651030002e27140c0d91505242080741c007003443c2400c00500d41ca4031444c0700f003a41c6204240103480e004a0365045965100c0c0001000c0d508140289005071003901c1d03070f82005106101c683c91081d81e000790083c1c201c41c1441c2e0122415085061100d4251040 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 576340242 1250 576338992 576338999
    0xf0a051504030c17030a06080111040e130605040c0302090603030a0c12020322090b091b0d020405040f0f0c09050906121c020c040b0a0518072f160608040b0709 70
    0xc040609040401304400c17920303424000707000e2040392a00d91200802d603240c090014540e40b1948143c1e000c854290384000c15990710902d0300612183d90010040c4082c0c80c000402c000c00c901030103071a0a59009441c5103043d41d40b05001c1c50781d00e03c9800036443c0801c840d6092000040d42008a22a026075548141d80c181384600d84a00341860a0031200040740d0301042d0180710314440f604c100c4100850485081803e420118540c40642529070588180b1880001c1c2c05100e520040d011600181805041003091100d070340705480083c00c105045034842c1d400c0c1070a0b41d4a2911801d03e050990313100901503035113616080200b10070020082413440325400346809180505440c0c2c11001c007103504c0354015000c1d80310350f00c1c03c101c1210300c0740561512a8860710024001c0f1340f19039844455029804880300025101d0180c1560003402100089444801d0120006c240c1100300042010800702102180c5081c1000ca401080c030101500030030000912820004021814981c0b003560000c0113405c01e140b0503a01c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 576341492 1250 576340242 576340253
    0x110c1009020f040e0618151302060f0c060f0108070803040501262e060509100c051f1a01140a090e1006080a0e120a0e04020d0c020f0a051504030c 64
    0x84604c2e0007040c3d0300a04100a643d03540c148180c0c01e0035910300042c294815400c503a044000038080e03c500307d0080040c025404548807803089030f0002e40f074120403e8540c001c100d205a07640000300e40984a806484d00001441240040c40300306855040000d181010700340001100d140d148407820b1740300d1070502c4062400711039044400038014502e92040500b2005144100701078443e0b80703071490741494200d1000f04021548482503800009048440751004505103038115850381000b00054018086c2280c401482da81001090911032509078081c801902002c0d010494031044013002d5000c9140b03500b80c1c213100400c4000074449144141007006807951030b510b00941c8010111644080c41c80f000c1c9081c40700075040b582e1250700000c030420500c44541803c0100342c540110369401d6040401c0402c1243c40b103801180d00310b0b5103802c0608215141ca9400035035401034404c00301f6030809402400b803450440e0501117001c03407590f5080030080c00790002035841d10b4001c4d640200706600300408205d01100240 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 576342742 1250 576341492 576341501
    0xd060b040803041509051c0303141501020c0d200d050304030f140f0a021302090405040809280b0706020d0207060507141e1605031c110c1009020f04 65
    0x101c1e210007140c503a0700345191020224601c104507004c0c094980c5003000079070f440301c0c83d5035080d052903210b017600c4e03032020715096010f44481003000e0701d000382182c10840700780d8003802d108803030b16003d900300c070551032040049c40071031414424040c0040459040444801c1d103000e2109140260140c409111554607880305030450300241c0084690050300449407040c08026500400050070f5807014090f010121041166900c1e29620024000ea07000c0e00c071038180121a070305980c08084040c00c18481c52800d840c0c10440c56004a113454441c0c142110b8081d00f808607035164140d52500c110500c8a00360811884520076003100c00210385054081155240080b07681c00a084080d03c11800440d07141000100900720b40e400c2c1c020703040b035071009011a021138031002c0351040c0000c800c01502a40c8845c200321518a400398000050040e00c4001528020202c40f451640c07080080c415003040100d02120012000d485043c2a416082e40005000c4440c9486903001c400900c1c401026010009245c001040594 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 576343992 1250 576342742 576342749
    0x90503092b0305031b0c1f0605040c23090108070c050c0a1d091b0f1206040507060e0402033c090a031403060a0608130506100512210d060b04 62
    0x3030004400d101c54031032541a00c1005d0303803010452500300917004004540c0c410328045c40c03850031901e1042c1c44e0880951948654007812000c1c00501c1410740c10a00940400039400501071004018003d0f616581c0300041a04c028000503503416000340c0700c10800310703201121100141e07118060103c0d892101d42c1c544030f13481c000703085000009440100c100702041880c2d40080140d540ca403c82c80c0f01404010000e102050702d2801110550320000910b00401c58504070820b540c2000d2040b001800280040001c4081c121111507644d050408200c405010a81c001a05c0512806500c00038800c0b0900034100c601060700364051054140940d012010040c0366002c0c0d46048482e00505188001c7c141e0104200c485002c000c04024a503043c01804502d5220b500d100e0b400c20040203401003000704012100c140f18454014088403181e0401d4420312145074500c0c030a4a1080c425190304441c81d90002c5508a1000340d1400760342c42104203220036803040e90018422164060f6149804190094424007a0014 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 576345242 1250 576343992 576343997
    0x140c0d030903170103120c0c0503010c052206081306140c0901030e1902060f0f0304050c09060906180a06030c0b0405030105060d050604020112090f0501050712090503092b03 76
    0x103080c0030304003d0a1141d004410602000d0300100500109071400c01d50b0003403007950318000c1c920510a040104550806d604615895401c3c080c016040560040240580e21031714014451402c1d00c41c1001030480400b031103894003080c07100380040e140da0322043d940001d80b4000d10b40400d20a460070406481204102c1710b41d042e103000812203145559061040c2e80c01c1014070801003a00c020a010487c0e60a00321010082c80743c00300181180d02d41a40f40280c8103e000303042030315900c070b08080c6429512548070610141c05241c10301c0000d541d6261441c0154012400500307010f007404440d9a8140f5084402003140148585541001001802c6000440010304511a540391114103103002c041c2990400b50016102d51584200000880e9020580075002073b82428031400454841c0704e0390000d4050703c1806041d40300b10300000c80c180319064010902c51005603840c0d400035200c8180c64021184203000c0600b050b03109000480352810b00c8414400c1d0711003500f8075861843c0d00d66112001c18101e0b42c004500 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 576346492 1250 576345242 576345251
    0x31101050718060e03060114010507051f0b0405010b0a110f070305010905060106080c1213080d0e010608010e030a0c0c17210403150203041a091f06060906140c0d03 72
    0x9101100516002c05026a4644041092003410000e65212418043d1030980d03801130b0032041c40c80e0302a00841e800d4a82c440d00350341300c0c441d146100d100c100080a2200e11564100444441c140c80c0c43e1258605840d0028901c6041c5410040304481403454103038030700014450750707000c03076900c10007003181c00c00441c414000402c50581c00d00c1e02c281030081c1a030142c001d102c01d0005000c186811300c8280c41460000c452034005075622140000c92103e20807201800e0084000340c049103000040d041820510150002401110340e10340c2e5007402c0390704814946049402c148801c2400c640718808103544240100c0056481c1c54030f64002c40a01d0007080c011443e9a0302c04111301c4200285040c0180000d41d2095509052901d19100e001d503070703c0030650713902416900100141c1002010704c4900110030249400d1585483c0455949075500c814201004020411503079082800d2002c2c0100004e44045588040d22075103070081c1030300c103a0201191280e10070b0050014040c1483c04025840c258140d030b90700440c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 576347742 1250 576346492 576346517
    0x605130b041b0c080c28060c020d0e061803100606112d10090305040501090b0702030c01030504020102100e3910090f09360605040311010507 62
    0x12600c4070b080800b90082c040810318502c1d6084000001042e4000c0308041c1d44201750405942022030043c1d1405401c0042442a005002061260450039108a808010701c0b49048001e80e9291191411100000c0420b1642882d80c2081400f0b071008100c50441540d00c84c1c102c0700000d0906103424076200d505640c80c0c00400c0440c0c0c1c40a81ca0f003840e00d071480a002036001094151001c19034007461001d10f0720f20403c0d403d551600800203000400444642000290400d1400070100c2d8014450b55000a10f2640c002c203d4000b1070382242c00b5264028000c16500407203c0066019000040059041d4050610442079500d07080c003410b1518006075002c0c048002007100040d40420a403034031045502d1005108401c0030113004003103021900102c5003148a0014942c04468941241d0043c0e00841c0304031200080c0c44000717801405045020504a00711302c585003044107191040c1c10754441d450300c1808100c03400304d1380d180c0c4460382150007890044091182590b519007075841c150380184c000f82c409000d18 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 576348992 1250 576347742 576347749
    0x30f0105011818080a0c030c02031f0b041e051e0412080f0f0f0405071802030f072c01090b030f04050f0105010f0509090f161d01050a06050306040605130b 68
    0x303024850b640707240c1c0010b8025500d90b080c1034045e5010500a120b440410308090500a0803c506c190750b000741102c1c20f80080c0c41407070540c0c00301488403085041c02c02c2000130702482c0c039016005c03040302c20130008041c0c0c485100024020b04000b800b103102ca80c1149840c13103e6601c03608a0740744038074000e1300002110b0f01d4040303008007200c030001d20102c030b8002150244442c09514480701c035045030b82e14540b0030322900c89060080c00c1140c0d03030788140e40c03464201035500c88501e031a40243d481000008103850040d81d48507400d0756603544c51b41c800910340400e1010706440c078108241454400c1818500b188115440e500026480da2090f903142e1070140600b000c00082110070080c00c07031080c5008000b44025454403041c248110503e0288601c1031b02c00000040c0e05040c00c0096031504c00d5418122003078880803264807000b00c0021300801d1403044166a4040c0c00004110310281205c0c0003400c60008107144c504110b40329000644660b80c0143ca40500060030b07038504880c48080e50099100150300c040308004c1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 576350242 1250 576348992 576349001
    0x6091f09020904020d02040b090a0f0e060c040b0f0403060903030608060a0e060c0a0216170601090c080115020f1510051906080402130c05070b0f060a05040b030f01050118 75
    0x4904450a229214006032161000d06812550546424a818000c0d00c000786c0500f085408142d04a5100410440800030036084103240c000ca03044100900d2045003a40c640f2038100300d61311110a0010001008810b0803400248041e0038801d0b001400c19459540b03500545800c81e40640009031034980c28410900188640c5800506c840001c000305070750003003c030742c031a00c000305200e0000d4408183c0c07405a5009100c0580d15142c980f1050031a00e450744213190107042c012480003050701c504c00011624000600c2424403a0f2229140c00055a192070f02c3c41c40340081004144045015050b0300c01e001a004120740140003a60070503070303002c07031408159010000d042640f0280c41060340e80d10700c5400725407824001064500e2441c06248030b030348600104548202c1a0b4070314450520b00701c0c01b02a001d0f40a0040c0c605c05100d4090100b03191210800800700c4601170300e00d80c2c0e102c540000100003c0c5071641c0010240d1a0240a540b0b200780e4640d64242100c03001d80c4000044c181e2041c600501040c203101d03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 576351492 1250 576350242 576350293
    0x30513060e010905040b0402070606090204173403020402190e0103020901090b07140a0309080c0105040e18071e090b010503011a0315090a0b0a150c0f11030609 70
    0x4010014040041c0000c1c000c2e100c502c2020300030344c4d4650404c40c2c551a40d40444d226542c0010050169a58981d00074000394810f100d14010455811840c8000310400308005482900c05140c0f050010300380007000c002c0c0031081241c16045048400000016152030001c0e042d1051052030f2006400d58900b805091139031308800040c10580304005499007a81c0040041094a1000308051348401c203502c2d041e4071005800303540e4a002d101e03d54007001050b5000b004207081e02c40b0001503a02c03892a980054801740114002c3c07e002c8800710000031203484594504c62030380c1018508803030300c4035170b0b85214005202030b803800c11998135004a010b12111205003d004001e0303e0a180039440c56245c80410031034107150303d40103114460004085224002d44002454030080b00502d40d000c0da05141981000400154500034040c21202c4000104142c410058501e03038911519012a10030b480d40d0b800526064065084a4001c03400c0d00102040d00d04111651056000100500381954003c40c51800b0036990307503 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 576352742 1250 576351492 576351497
    0x1a09090318030c131a03031b100203040c060503040501110c0703050f21131508010504050f04030f0e03100501060c0b09011517010e2d0604050c0907110a03051306 71
    0x807500d81c1c0c1c4c480105242c010b0107200e0001541d070007074050854280204e565400d038548808540045245501c0440c0e07940c4103210012210890f110220030b0040e4041140c0203071494540260812050303000710015540288076400004040302404005410b507080348104900b0b5501100050080241c04c01c86408121814002400820600d29040014201c51480155241c1001c104e42d540b80580b05d00d00f001a240c040d81222068917a810000c001003400d1291a20481c240400708900d8101c0c1d000642c015501540c41007904030001105442d8204a0f082c01c41c0c240c8200c011f0039202c00c44a02c600c0380a80030590790740e01ca8201c2807d03e0f84160001070000d041c141d16218003003442d4010000b49070101da81c2c0140410004224491840c01400c1c000c4e040c2d903280c090355400b100b52041000000e002e0020340c0040040350350414459a03910003049070020015800324206021074a004608072380c3c010500d1820440e010000c4100c01d041c100c10716402c0340072450100d82e40900c003c400000d8409440540b = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 576353992 1250 576352742 576352753
    0x605100b030402090103060b19151d0f2704051506030f07050904020406080607180b0f0d090501020c0304150e040e0d080c1905120112020604091a0909031803 69
    0x3d400082e100304041c800200000e03500c140348911a103440c0c02c1180800c0b9644036000400b03a40d107818400d2001e00340c2d00040000c0716040d820306080e9002000902c5010081d008028803950036040c4184460384044056501c000001c11171000d020414040c0c0c891803080000c0c082a01c80c400c1442c42da400e016141c18401e8005124a01d103140000402d401140d41c01c441140454a860010400902040d0020003050142c80702b0401565001011490aa00d071005008485641d03030750340c0d607107502404410030f100c4501004144201259a003040031500c0c040c030001450201782c3c00020346154000d5001544007001342600d003144e650441402c03801c400054074244410001c0c9d0f0001c40c0c86c3e103c1d60301890706024072140410742011160045e10b40922000c2c0005071035245074500178000d50803000041000c800141c2c004180030150041d0390300f2080d8040c00f00e42c06d0600b003100200103045010100c11090b40340d09140d000e6941c40c0758200b80202c40c5400a140e41d418500420048900c0c907480c1140030f41d001c0e = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 576355242 1250 576353992 576354001
    0x30b01120207051606031e0515090a05040c0b03070e0607050f1609050c0f09090421200c0a0b07080903120c0f010615030225030906020f0703170c190605100b03 70
    0x5242e06040d080148030000681c0d641c402c09c071070b8106d0652602268200c41150b08100c0562a980e001c03a00440c0030b00c07144441d6956424841d00759200440d02d680c0001d41d4048407803502d003400b4000d00721083c4250180c444008900404600e004901c03580d5007000c448020080229041901c03805401c00d01e0000801d01d00b03607180c1445c0a80f4410745104c540a5040d42000405010307403800700021110120094503079034100e0f010001c00907100303003820401c014540701421140c03440010700e8000106000d0044c50303a051030400200015042103109032285002001500c1d01950180803480d880381124110544030300c120812540340c1072042d900051641e25290042c8402d040007500403448460341e180142e07641e00c0810b00b0f1036522840c0e008140901031010701c0c0c0703000c054001c0078030410341e08260308950203c6807401c000c41c3e84040a05c80079000118100b10116078081500007000c9a2098000700c4e200003401d195501c0d5031003403801c01500c00d140c0e51024004051003101420b0010500d1004246c00d5090 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 576356492 1250 576355242 576355271
    0x90603020d0f020f030f0106140d021e1306090911101706040f020408280c150504120c06030e03091305040c0308070507031110020d030b0112020705160603 68
    0x10704034005030064107080d40290440d40c40c00f500c03040d40000503054030041c43c51020b2040c06082180590300f030b560110042e440d41070900341c40702907040ba0010190003035840281005e800d40940305210340d4001c035030610000410701d41ca02030b42005100c0c04d4000038480c0340500708140c040400400f01e900c15801e4070084800c00c1d50000700c1c100c1140720409014120b4841c000058024142d5501180200f130022400040f40781001c10a82d4040b940c0742c052001c6410010119820130050032401413461300c064a052000f681c92500030000d031501c50030800d103480c0d1205030a6a001c11200d508071140321440000703100980c9e01d4042c1c5016005818021410203660b0300014200c134540e20036803203009556600040c240454030340384c0001036402c0410160307242410b0070900d0702c80c241d034041035441c032801d0081b40c4a5400d180303280424080541d0f0280000143d488800c401800002271814100700b4928000c0004144500c01000300c0d80c800c000602ea83c2c0c0c040c1d01201c20702111540074809140c5810126000c001 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 576357742 1250 576356492 576356509
    0x14040c08150405150c13081e03090307061d040516020106080303070c03140403020d0c0f050d0b0a05040606171506033016060b090a3605030304110a09060302 69
    0x1383c0c0600203003869440c0c401c06405801001e08040d80d61003071031400654020042190b0f41104030300441d83c5081c03090080b50b0f60341c0340310300950309401d0340c40594200007c034410f10300013641c85501188a6002101140014203a46040c1c40020a00d102c1c00304c10007440d41c09100300d00060809034050340c05c0d481e00d10342c05011300c1307460000a03041c4604403e040c0d040d1090201101c0c0034642c0207101130030030815402c089080f500140034480011605c280c0110f0185440003a10324079650040c079014041c1c1c1c0e41018140902005071048400c0b688500011625844051414125116880003030024003101c079100c0d580d001001d010b59002e60400c130005409200c0244c00300c0040e00e2813074080090b1407200c0303002c816244a100340c21000340c111001140b00708190354004041e040c00448620707a068a418509401711400703284010b0b0781c15200a80000c03200149000080a030321020b412164450741030702c6507421540100c2e030440d00c0050326406605207203084003e15010b403a120104002c0c450850740802c40b80c0 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 576358992 1250 576357742 576357763
    0x41406101205010806040c0905010b03041403160602030a15032310020315270f06010c0506130302070b030c0319020f0a03050a1a0303040b0d14040c08150405 69
    0x55041410104005009180709181ea07031000710100842e694804030b00c0e4441c401980c0803183c06980003030018000f081070042505035040186181e00c0d5449031f03a2105203107440b205000005000034040301003114403610b151001c1c1801800056580d20307105a403102100e0110200910760394801c041800452000814603030404020303680da024140e980402c007407a2a42c25160310003101c0c00002040782140c0410034039102c090f41511260000180d400141c8010610600d0040c400c42040340040c64a4001c00281c0e90010305c18108404c46203083e880701b37401c02108070b98030007a880514a550041503810404071008050101445080d03040084030f1807018400901003002c0040b042200001c110740517070403a0702001ca9031203000e640741c81001c1c01801400048a052003180d10701556a89035401c0c61005909048004000d5881c0ca8180081e440442c0c1000d40504001070343c9500c0c0802c11741d440600d0a00660182c103141000350302d0280b085203049540c0c90500781207000503044c07200007940002c120154 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 576360242 1250 576358992 576358999
    0x81503101d010c0e09070e100903050715020309010e01030e01060308070b1024020114130b0a051306021c021c060501050f270406180b0f01020c0d24020c010506041406 73
    0x46d480301d00f400c07034903000b110404a5024616008403600d40d6042000c0c40b04882c814007d80e240207070380304018400094410124409a0010804030700070b03622501e075250400805040014900ca200e00c410741c210342154100715100c810024480050017001610315600c0032115290444c06414020b10304c807105440c500840f1440005200680800e00039041040c0c152030654107013041d8a444855844145103105058550080700008540511118065540300b28691810210072469a580ba640254800c40396003940294880559551001900042002c03017a40391141d0800305d05041210115113407944180c0c1480010021030600c01070380d038250f84084a009103444150032903030b8843d080302d51400e0304613540a03282801c041000680a1507591409a0462080012002007020310000120f0307001940d0159200341d05104d11490303c412000c80c80f61191010b00c403084a5090815000d42c01c1040c910643c44e0003040000a8000910400c1d2748620111024841e1a5028003003640c10200601282d02 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 576361492 1250 576360242 576360259
    0xd140a021309020f060c0f010507050a030b040504030e060d020405060d060513270809100f0f080f040b13080a030204060f030504170307020c030f0a0209010602150106081503101d010c0e 81
    0x60070310042c4284121f80c04410000e100d24035240600910b294015a001004032b46000c0b111041420280700307282c0300300e50613290200100703446e40400c4119000f0000c8010982d80802010a9586542010b090100d83e004c0001c180c03d41000100300b8110886c042c02018140381001030340380558159000640303110200641c1250380b030301c2d0601107443c1c4034003a80c0c0c540003856245040f088a91001c41d005014101c0d5076005644040c4100807035071780d401a102a05440900d001190100b03114901c0603401010340105080d80d4040756444041a8000410f0782c004241c0c0403908208058004402080c40d02d1549800c201514180e03640002d005100c0101c4d601140002c00040d0400340200315426031800014200c521640c2503d85207035940709040022402007105400000c1c4942c00014094000364055841024a83c2051803c03a80c0c50b0000307000098460103558030020945060102d10080c2080b2000420400c10202d1080d4445440c281482840c0c3c0c58090010000d9502c28a125181202200c00c181d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 576362742 1250 576361492 576361507
    0x20d02040504091a01050d020f04020c150403051305010801080327060714070b0702010801170c0d0302060610110a23060f07120209010e0f0d140a021309020f06 70
    0x10000c0c09990009a0080e241c1000300d0b09014010255883d1000c601d460100c1ca60388032024400c06400700c0800942111221120307035a02e21f09170300900300744170b404000c5445003450092074010880d4182c03015004150001080000f05202d001b4000260000b030034013a00c194540202983c0e00e00c1414591090300d10714914a0300b1403030300d60001c100f80702001410540c032045181885004490a5019050540700e05600001c43d0720100060701c0310070b90141c4601c8216072030702160040400710040350410034010f000d9440180d0360380542203040d96000380e008100525001051020700154122043d090004060445004075000a42e10310195844940c255040741142103081000c0d05009000005000ea0f904204c0c0d00c07400001068820039042d680c6014448005005078200c0c4181c1400c1400603100d0024000c1508062400450707070400504050350b050400e0721038031088018109424601d0300850b00d48019442c00b0790004800700c03408a400c00c1490a00d40c0080c01c400f12101c421030080002060300c4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 576363992 1250 576362742 576362767
    0x901090c0303170a050c0a11120a1706030a030c12090902030f07180302030d120b030a0803071419030518070303080603150c16050f010c0305010e0c1305011b0f0809010305071d0402 79
    0x80c507427800da0801e0540303800d46600e020341714003200e100c0251a0400039000030300910f400940c425240390542c0720b00030910010707101c9242e410a41ea0354402030090103100010b00c0c9042d84011803240120b03079049551801c1c210002060503401281d40c0c1c1d4808202c40090025079004224004d104059050010000c86005600409002c0310416030b6414011661510140060140118810211692080c0d6080304e420f112000c54040d400d1740702284c810000d14022410b0195201c41c0d000b03000c02500403456400600b013940340c01c0007170300114006800d45e024030401d03090400032100d9480c3e8412100b0b8680c58002210b10b02c2c0e0181d00866035142503040450406c3c48400c0c400600f01443c010000e222000903020043c0c040c000a10400c0300240003000010100841309c0242d80184000c00b0305102c50a01c0d0800450b4044000c4982001d01540b00201e440000c03a0582340d50304032840784840940700c8090b90005402c0302c20007440f12042c0000740c2d007000b090020580404240c41c0c012200140c80e0302206484 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 576365242 1250 576363992 576364003
    0x18140f1518091c0918090c0b0c0a0309080109020112050c071713050406080c0d032a110108090601031509080c010b04060906120b0901090c0303170a050c0a11 69
    0x199545100a2014440341240c08100d030f000c1c14040308841c4a1500c2c0066045480254620581c0507181e09404684c0c4031550940103480202d01409000200310788a1486581c594850241c91301180d00c906000420036420141200c014401d440080001d55a1a0006000c07040c0d2440800c521030342c2c80c00040c000b03131070440c280c0e19460b4015640c4200b1550640003585180d108502c00f1000312007100d0001000d2909005803811307905070b44040d0112801310320a00400c1c000b201011011702000b104440380312120b4554100e181d6600c002d0444101d646401e207035440c8440c1581c120304112080b010040500b40000d1303181e044980c0040001c00c0c14070902d010000905c903240000309200c00011700b00c2e040030415088500d11100c2203a00300101c540d90a0418210ba6440c0705240d4600c4400200c3c10104400c030b5085070740320f441ca600200340540a0b9503444028811600308801007011030f03413082c007202c4a01541c0c0380d000120800800581c02d0806d180b1041c0d0152544e01c3c2c0c03c00c22000806281c20409018 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 576366492 1250 576365242 576365269
    0x2040b12160602010506300a080a03060f05120c13150e060f0907020c0103020703031803021609020708041404020d06080319090e01120201170118140f15 67
    0x16612080940c0440e8405051075105000041d8203000102d42c561502d4141d184c2c2d44030b48540c3c903000010745c0c4004c01940007400354403804540590001240811021802041440d90668001602600b05003079907038030b40555000302c3d0090080102c0d01c0c0314140005801c083c102021100700c80403040d828410801f03001320400c0b002e00341041110008584180903111800303003a040300c0c0710585000580a02c000f8140c101c80c80310041e408006501120750203540200f8606009182c00701718081800c640030030031a28204104c00590000400801e402e84010070780c400f84c42490010341c0b4100d06138907021114041c50048254107202064903900d130380e4865046a44148070a071003032184c5a41c601147c0d8603900200860f90f92901281a1b1205443c070800a25080c0c0c3c00f4218142a90390811381072600e00c96000710202d040c0001600300c81680101610642d0080524a020010a14800180605885024011490f049001000e00c8408003020144036406905010300d0854621705000180d0519010795 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 576367742 1250 576366492 576366529
    0xa0c030506030c09060a031e03030c0e09070e010c0f052b08010918051609150515210c03040201140703020a2d0305070c080c0d0609110a080102120703021602040b 71
    0x1510300703600c410385008c3c20060382d000707481c10004c1f00454101501c0c0400071100c030580c0881c45d4030002390b443c3d0056240442607401031420350201c02d51603a48040703c00b608030041d5080d60085140c0c4641aa061301c803412403010b105031603040503511002c00340c00300006000c0c0e2140c10b500c80444100c4c5070f40e2215038020075038100040360100c1e12448056003c90381d16008114140f42002a0041d0304d1181c41c11142c00c4030006482034442040100201c2456000260f01c0c0e40040691030f00c014008134182503441c010740388411a00d0f41ea092034800507058290201c02050242e000f071095202185e00400c01c030745c003150001c213042e1103107000d4808803000e0996115040740b4241800c140c1d10505a0040c00741c070207076104094a41d8020f03142c2c403aa990f5001d010190681c0411341c03400910004080750480103100d885800041751041c11100040c500e04640c1d001290700c0d80d40411892070349054003565030340001d001d003411840d000d840c180042e045d1a1003080640a00d8440c001d8000c5515101605650b07403403100f = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 576368992 1250 576367742 576367763
    0x3090307142b0c0303031b090503030403111306060914031b0d050c0307080703062016050c0301060e0402100f02030d11040e0a02070506010e0c071101200102030a0c030506030c09060a03 81
    0x5c0c900038004240c81c500380c2e5403e042d1040d801d08081d008030584415141c0040c021410b05203165119101651240001c85e00a800178220000d401214002c000c05040c5076291000780310300300800301e0309208081940728813a501030290001d0b180e0170201c00d840545800d0340c22010310500c90174880d02e810b8250203103540612a02900180c09000401d1020650748071b81002c0c041042203c00100850000d0503504150034401c0000703070810b18180c1c4052101e00e200d60140d0780f0740c000001c0045d0031500f80d0b90020000000400c10072046143c00d00c94140b6144907828100018a0041e0000355240a505018800f141d50380c04090040e0f03604101b51001046854011016880c0a0301c591029400001c001c4440f4030a013400404c0c0c0700007840610748105035140781c59060407007944450240100031020300781440440240d4941d60400c400302c0101e0708100c24005039480c2000e480c00e42c101d80c0304c01c29210070036261109001e03042e03801240f0182800d8040f100b15415413901800240c90030b4580e8401031010100 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 576370242 1250 576368992 576368999
    0x516110d110a120809040914100203040b0f040b0106080604020706020f130f06020c0114040314010903020c0102070303080a0203100e1504050112031b0519030203090307142b0c 77
    0x1441c505034410350241c4107000e107140e07990882c0d25094450380d002889503a003407010341110308060b400480002e002d0441d512550070080d854500b80402e108403500d0b0650004108824000780204468200c2548004001c99161603116001191018082c52003004074000c0800d85c19030b2190103451485800c00c20466407805001a240303210b90043c2024030650114440004001c0359040301c140c1110416000741c16142c0c040001103981041c41101290042c07421301c03010021420102c2132540c641d01c2c01d400004c0d0361006040191910b04902c1e20340c0d0443d844110300380300290f403000c2880d81103000f0080c096220344030b00340c8541e442079150b001540c07911040700402508060703c180d60001e03004187c1d4100242d90300d5503d6001070000b00300020700440c01e80d9602d00fa04030b01d28400215400d01076410f07a05410f001d00d05000a0126007502070300140c0c8085200a514071b400d000010041440c041c00c0b171402038681000c5076140703002d09019802408080315801b8442c3c081c04e0108160355100799030b494007a88 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 576371492 1250 576370242 576370253
    0x507051c0603260f0a12060b07060e060108030d05060a050d031701140108010b09011403150f041a062d0307020c240715020d050123010516110d 63
    0x6140c4001e555441c010030060080b4029600d007421921a520720613850703d905101c6281c0c8541c00b071240401044511900100303462a6440760401074103181280c1e640e41c03806414560b0507034a07030346868105070700f061004102d002c000000711b54500030100008903513541c4000c0055070428039a401189c011006917091010180c1c802554010754034a44c0342800640d80316030030107496001c13a990043c0800c012800502500da2103c01500d040c000524000701c44490fa24080c03003642c0c00c240d5001104860541c03090701d452510400704001e94005980030040c0700c06d55505082c801c0b41c0c50310b94078018407000425584c80c0100f1004441d50014460300c410300c000e125039502c230803070b0f00440c1c0010050260181e08103692412294058014031f58000b080600082801d10341c0460b40501c1c4112010a0a128005486030352400900601c80d40303504000b035903615207000900c10011000791601000d1034003814210581c1c103d41a81c241d04803522000c0180c040500d043c62a00344650700d466403000b4200384240c100301 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 576372742 1250 576371492 576371501
    0x72604081c09110108091f0507020c01110604060213090e060403121b0302030916080a0b0903030106050f070c05090f060a080708100b01021606032301050904060507051c 74
    0x790301400031100044445904100c2e1040d040040080840e0301c02d6588561003111041d130480349010544290310b0b0f54028100c044108484518622905c600400180540501820508100c01e017401d10b00d440000c03e045445000040006050035404a014010858150030080280500c4802000a80c803045600f0b99501c1d42120106c001030046c14075000d01040c10b018281c0003a8400d501d8a0848412007015070107504002c10855182c40b0341c101c4040030601012030700c0d0042400d0000b800000c4040d0500c111500001041e8440781d038010001040340b1a0b018003181d25482510117441c0e140e030070030729011020407966400140d005003400c05015410228014160150008031900f0555030b40da0400d0320b88a0716144107426254200a90340c000100d000c2c0c01101e001081481901c990303506821201d407500e0001d4004a0010343c4da84011031440002c6000c00c14010440b000001156241c03100103260315200810007000e094684000c00c1480303000350300750745da1101600100d450b0140c40b200c0000090 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 576373992 1250 576372742 576372757
    0x32b02010e0a031205060f010f0c03030f09030503090706050a080c18131409010b030309040e070302090103050a0c050d1212060906090903020601120209071d0301051e06011707260408 80
    0x4074500320210b0030713038035100703011f0b00040c2410f17102e04072005401641980c16100c4142c0a801349516641c078090981003a200c0c013075081c0d12a882d059101e041880c10180f80c48020782102c000d00c00108144941242c00090480e031154031804115559254810f0011150000014081d0403034510101e8000c0010725400031141c802a184060a055850104aa00380c840910700e007601a00100503421242c10f090b00002084903408040b12001540c81d804074040c3d0000741d2050f1540c0d041000540e003048064901d807402000200c0740614280003d44030b11007251440b44d0f844050121317006060031001025009803005091f0403000300900e90ba0780c025113018046401d401c0300140205e0002080440d08110000c0c140d60700035004e003406e07564040050740c0800c580700d5130280300c1c0f0300b0b2007a02d60700b03590074060359206000c01e4046100e02d004194200b02e1003840078200c54107210280c50503480703a020459446074000028608002da65410012170420300d0505401803046c030050004000030300031440000c0c02071 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 576375242 1250 576373992 576374027
    0x60c1505010608011806030b04120f090b0a0f02160b04050102010f050c07060203060a2c090606130b131404111210021e03041a0105032b02010e0a03 65
    0x150008249204680d001d001c0ca0300410b009200502000b26051000303080005003d100150a40d12a254214021411141203c14650340100482801d0340204003c28082550521070b00450500501c8a07003800740603142e004010b43d507550324809920802045242c003403c0600d03403640c140c84d0740702404103502c2400303110302643c282207502040103100e01c10b503442903080001030b82c01c0c201e0301e99581c0041d42c0007411880d40030818020114101c000d8103c2001444001d180803058040c40d000101003080e002044880142c01c69001c1003120f4803032607909040d181d040800055800c070304a00190f0107000e0398840210040c6406074401d5110755018205010701d028800e69449109420704000e1031100024503c40700350020b01c0020041d91080c0c01900600620788003601c0740c80c640c00400811500121030a83d901220725550210a00044140c1030141c10145c0180c09036035204c10710308610301d04a4680540c0030388040325a10000303100f903101c1345140d01c0d268150780c0900c4003820000c2800740491904802d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 576376492 1250 576375242 576375263
    0x12070903020a0b0c06040f1703010e190b1008091c020f060f04050703080702061615110f27030a03120e03091f09030803190e03040e0415020c07060c 65
    0x183d01e108801940c0c030300380d0b0080c01004d0580d144c1d0340b01900c0703040442003225481074100700c201004400902950291613207070a07000c07071071070b00300002041d402600c50300d00b1905152103203000481d114807005650460132820040741d076444240b0b0880c079221307541c036214800140d140c1c540e410455000c41d51081d00d000e440c003140c40c551120714050041e44016100100385e44d0112200300001114030300601a071500084c5510304100b411102c015410b441803100311003c0c1c5070a81d84a59804151040000700c0c45802c02e8981000f4180c07541070a070b4410b02501e020400040d90040f0a81c807609aa601c1d02c96501030140c6a4040c1c491030017400c0c00d0a02c0044140702800d10445803e81c010010944440100042050030810000c1c0d0b056213404070484012003c1104c1150088046680e20009502890403c02400c0c1054205014070003200c4400f41018a143c0042101700420348004070055081a0003843e000e101c00700e40ba1415001744200010328505010b032034400100300c0c1e04803800007200c0d80265403085 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 576377742 1250 576376492 576376499
    0xa02011b0f11010b030a0c05030f0106050a18020d09050109031403070c0809010c020d03050301081605130522110f0301020a022d0a0503071103160605070812070903020a 74
    0xc980c51084054000703480c040c10a20784900c00c84441c9403000459000041080340e20f00030071300b0304654140940c1d00d0340b10860200054242080400801005100204046400c1c840090f500120030301c92219003030f207403a021000d4101c040d81120014540d03810f041003d480a03282260103421207400079408264586488002c2010708021644070300700e0340d030320881c7c550320325510b100080e0800c41c42141000203c845503801620f402050920039406a101c03681c40358500700c03a461a11002e16032105150014001c00c00032901c0710300445951507810000828640e840c02510069040708501c1346012211603a48801032092400722103e0303841c01940c1820f00b80c400b12061501341e209000324640187d12030118062000100141403685418009284031503c5004001500e482d9070071200342c0340c0b6040002c06c2000c01c1600001c2d9003c1b084160083d1041c10000b81d1003501d880564410582480360010300041086241011501a20300c0c410301e0380c14500703186400500e41c5c2c140e404100d02440d0300c8140032 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 576378992 1250 576377742 576377771
    0xa0614100b0f13031a01170102070809040504051212070206061e0409080d020d0204090c0906050f03040f021e040506031902010513150c060609051005060315040507050a0201 76
    0x5825036200400e5030740390002c034840c000030680c0060340d90180c00b000d14802100040f41c00c2060310207400d05500c10102541480c0d16000808421040503940d6032040044c100002c6115050f51b400b182c00301c4000070681c0c0d80342070603400c101040301c1044d850710b0b00181410f8401c00c0d8400003406402282d0840d6030681d03541080c4200d910701458007140001d840c000b1f4165524041d007020702c400b4807600301503040004415044060380c010189206465401080500404400748252401042c0c0c41c030340088a1480c01c003026226114090a10306800070010006041c400c11007885c00741d40341e002c0d0400e000342503985149502c1001c17540e402403140303041c00d02050541c540094800417102180a40110b50242c684c015100d50340603076808095601c0320780d070002d0408020b01c400303203081005845800400e0303980c0c0f900d181244d40310740107000d03018036103014009954405083c04065400c10b84074103580b0340f100c0182c01c950140c859055680641884200010f41c0c1e8040003030000700340740d60000e0003511894000f8 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 576380242 1250 576378992 576379021
    0x20307021605010c11060703092102151e03070c050706050d0f151517040501140a060609050402030606070501050a061d0c0a0503070507121e031802040b0102010e0a0614 74
    0x151502c45c01c03415020030f40c60030a0040c0035070751007401c05c1400300703541740000d03080c0551609c01541070070720300b0740d074801035041c203904407003090146455641c64040c509a1041d40c1030f103104003134008994041b000944003401282400c41720364100c1c3c1220360450380c4000040c5243d0103a060042d800e0300b40300d41d02e0030014060107044400da020030041d021781828809007008141440f0703a00000c00c00e108000318030803003080f1030301409580514000b00b91940d429040c4000e80d60090110941e00340750074070400c04513600c04600030540b4812940941e49882d0040007070401c1c000c80744050b203554a020207010081d801c2d64401e43c119800442c00d480c0c0400c40c011404030410040b0b486815a400c104140000140f0400c015507000009080240c1070100f99256510703021240c3c1920404191140b484d00000c08040c1404610a0071919052140240103600c4418250411400030701481c1c40d55801d0f01e13268000e40148003076952070380884007055040e081c1800903110503640500e8038250303240403440403481d5410 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 576381492 1250 576380242 576380267
    0x12020c1002030601021509030309070819020f0609030105070905010831020613030507032d03350a1505010503040b10030c150206071112030903040902030702160501 72
    0xc0d048411020004801a500060003241140218001034003a08984200e0790700411101c0e004680341d00d003070341040386481e03036a82040181e944400d19480d010841c041d1032508082e816641e244d81b02521001182c0c142c0600394885601d94203107000c100b1030b103501502d03110446000b669007408035201d035000703054040b00c06402c20f0a54103603204610744110000940c4601d0350300c050712051400071101c0110059400940040b20b054200e40c0081003480040d5034001c249003001c65014140c203c541102d40b11040010400606200c09803640c1c0d0028000c40a905074845d032503141c25520205072140c1103140302c0045410744121842c008090000340924144441a03d03810f1b126146941c451f80c84540d060341c0300410100c2d0320801c02d0b4000c00090300303080002004103d9026081c440405440d000790038200002d11240070130400c0c0c03903100070000c8001150b141020040d8501030781c030785410201c0ba00f98415a00300307084044c000130600413850381c0050800b004104200001950548480044510019034071 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 576382742 1250 576381492 576381517
    0x6060605030915060a03050109121d1c11041d071205281203050726150402120903070b15010503070e120615120a0506040308130c0e04031202 62
    0x468460f140243c05003041d0000c1009010012851b43c0303607140d41c01e56145c44001c880c544c61440e940380a00d81c000600141c4c1c80600000b0201f05c0c0d5507200414030b142d9041c42c1003050101220103e50502000c441001c101c000064014001a045440c0c68511b5862072800f410707543c45002000242940400c14001131194000c01070301203107040c10300201d144e50b680125060321107800c2821030002110008181e0030741400e41c401048038034110001074811803607014020441511303000c0c0c000c0c0c840d030000009940400b207080154003e010080109000303009001c858024100c0413400c0c0a1031000000c0076000052181450f0440345d034408150110010001000034007050003480811006802002c044141580c05032000e000011801c0c10781e40b41c2807080d0384880030445030140201080c14220040698050640000c0075041c030b2a070b65459441c1d80c0100003504020069000c18030709800c2c2c1a4a8001e20380003940c40c0c100c40e86581105c6070502e02581c044010504610341700c00d408000d0b009481e903034803146 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 576383992 1250 576382742 576382753
    0x1819020c03040501181d060a1202010c02130b1c11120a0b071e0305090106080a0314090d050307060e071406030a09033c08010e180109060207030c060606050309 70
    0x401034070459407218161505c0d0030828400b040344a40c0300f24046080700200c070403154030308052041c04880c6809812004920070346e8404440075036081314461400580c1511004d9018000c294142d004202100c44698088452041c0706c9042c0501c1268100c0a40501c11114a4922035002c02c0269840118615866040803001c040482c2030340170550703884109400c000030003800780051041d41112510b94100800d556405000d01c1c030303400344503500c0034010b204018400f0001903140500500c07054448034000c4d0702e00280200c81511564090000301d603110080386c0e00c0306424900003003e82820ba03048135291148000005807807451000520380345038081e000b03510350f032580e041d494040c049240043c1c090011840c1241e03005400d515642d401c0b8001081064071300515504480407140100c0b440303c1c01c000a050060241c0c205400c0d48a40010b42984164820010242400e02400310080302502052003c9104818180c0100c0f140803460310a01040280d075407a80c600740e590f0302090310070141c41c0d03102 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 576385242 1250 576383992 576383999
    0xf010303030507030b040204030b070906030213050f03030904061d0f0f010e0402010e0a1e0e06101b0c0f03050105182a0306091c0206040206271819020c0304 69
    0x25800b2541000380b42c5004603805d640b440101d0143da03c40d91044948242101c00c0051315a0702107820303c0038094614040d8a800c0c05080c410f95201440c2c080c0030311400c1d0424080e0780c0fa130340801c00c540c60840082d2050051560751a20541d181588481c46c404140d8514009814245c080b5581d070710500d05880401c01c3c1c1c0e42042d02e0844c0881004004078180031055103d101d5682e98192036000070101550300b00c41da17103525144c0c0d000f000c01c183d106003545851002840310641e02e03400000e03030004451501000300442c1d43d0f0184000008008040e2040310012004588214010707103c000303403805140240071540740c0b000721055039084c200004440ea000354200401c904812554000900070403074410894818500002c0d043c1401542d2040e080e42c0030074100315000860715000d8481a94a001402e00c80c5413a40105c0c1d558800da80101c0d212aa0240e807040028400c80c00201c0913010190200f61321481c200e12a00c40c400303040d148100daa1a090034007181541080c0200d80c2404803003409541003a18 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 576386492 1250 576385242 576385247
    0x210020721182619030c080d0203090c0f030d08011a09150d050609191e021b01150506040302040b030c030a0f0b010605040b03070f0203130602010f0f050f010303 71
    0x150412000c00708030000c02800c02a03002429000083c24860040c98002544090400a5980764546080e09034004c0c00310381c03011511104071608110b825080003240c500c15490000c480d84500c3d10807661251011003440206200000c030110b5001d01074520f071140c00b407240c00b056a52040d5440c440c0c0011640d10050001d808141c0785c00c00c1100040c05c1711401e1603412400141103201806003a00241d401007203410540f003550080e640c0120047d9011440b50a001e080c0c44c1e000c0480d044031244891b100c034278104c21031762044801c440c40d0a00380011521103003031211042c0001920084000350790700b000d031040c1c0031290710200343c01250001032040d840e242c80c660901004e4a844101180e05004800203101c80d61402d01046001c2d82c030404289805502501d8058858507041c0c10050170003206001c01d0012010700700840703401c01484d0501e00310761903194104a103148503406050b118500c40150001d01719405401002d88a002d5100600c010104408810700f1548112598404860000b0041001c81d0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 576387742 1250 576386492 576386543
    0x1110030509030d1e060306091b0302010903060b0a03060c021e0d0f0c0c2115020a051210170304080615011709012009090f150415080a0c0602100207 65
    0x8134016030252102141690303004031100e5500c1600c0030740c0c0f54a40700d0704114500c001c4003174809041500c0c80d40c003815038000a000c1e9a00e0702004144035900d205041d000d40d110700444000b143c0c8440103011520702440000d4440d503985000444144000700248079840000c40ea584040c0284d0b9a800800405260100c0b11a1148a810b840300c2d2003641000c51000b1048010b00100c100d99010b00c003212030649031800c8501006400c1c0c1ea90740d84144a151a0b0940c800200c3d10b032441142a1140329440d444444104e58056030703c11844c01500d01c800102119010015208844003034040e6091581d41c1720b684507101e800e0310000d90000d858040f0801c2c5061b00107460039004256034000040b154034a0070502080da04841c00c4000f01c4501060140c1646003032207815500044407807882e042801d2011584180d2202c41c000b0768461038403071945032102610024080010400e0714115400001181055003a0004030301900c00107000b180e42c1003040140030b0003160b4243d58044500140000e10116030704208 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 576388992 1250 576387742 576387761
    0x301050127060e1b12161407030903060914060411011106090c06030709180603110117060418020613050126160302040302040e0f161202100215041110030509030d 71
    0x1003d00c20754217202c4200000901c103402c180e0704540c80c200342000207490b401a42c200c2c0c1010190401c42c0b040040d9004c00020101ca60001e400700d190b00c01403909600002c0060b8031030101d0311540c0c08100c180110482081074120080c0c90348030440300064030031600d0310310440341d09034194090400340081d81050380007140d000c4650f203064103280d503c900304c503c240d861500c6424001c640b215070074801e101844508020484003400e0000c4440d468603030200d0303001350045c0b096118a43c2e40000f40380c40c01a0052a21445030b0092030b5035074070203130740000c1d10312445030b070280c0b500040300c070504096808141e004544a005d1400e040f03034081e542c2d805090700e010601510314800c1503001d000c00001a2214054101001c4d00c600203007000d070101206451408541005000e000c1802c03400c10400614020700305101c1039015100b030204034189810a074030340b0458400c20101891145e042009014040c0c0c81e03982e01010071a0f081600300da49200440c03d8810550f02e100d465001001140344102d0f20b5806020380 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 576390242 1250 576388992 576389041
    0x40b0a0c020a0f03020a090501180903020705060a05030405010e031629090a0611180105210108030c0c011706011b061b02010609091205030709050301050127060e 71
    0x501495078041402c140982c0c0c081210000400d02c113004625115900d4409050494410061585001130070b0b03c035240030400d0580075903501c01030a41810320a1129030050b02d8003800084c2d60b200007450040c40c5500440f030079070762946080c038075002c43c1c0c50220440e1500840c40150b00700849090300d90356072960501030300c0140516103a4448440001104005200300190005040c650b040e034241a0190b52651080348042d803020402d480510640385514803c10500f8685507071181c841c655009807c454410910144540c070100014a00800000170200c1d40f50080030b6a4000392000b00640d00500e004131a81c8100c2c0240c2e00084855100b440700c080c00f0f101c0584072451404440d200e820031034207039501c1100340d0100ca260a141498090090f20028151800c080025050a450381d211405c0b0254140301040350020100303d9251284645d00050903004000700240e594034003402c4071b031005803030151036058400b0048040c40e501904c202c0040791aa00c0d41d0004503600c075064000c0050140c40038646 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 576391492 1250 576390242 576390257
    0x30c04030b1603140c0406030e0102040506030a06150315090b010c0b16180e040822060e1c05060a0e10091109010e070f0c0f0605040b0601030b0f06040b0a 68
    0x101d141d980045000d500500700442d10031810040007000e46820701d240d0711691541c0814003040c0042c0c002240c0c101d542918001400d50220001c890185c82141d2100380d2005010083c01840c0c0041e6100c44100da03120303240b44145c100604000e40039a18001510300b815038401c60204900800c9400c41e510a89051402440301d9900e40d50b4812628030540e008000b5801d100e03050081c480c0c1040c03070074020625042208144514140803d0718004001740001c0c0400c1e80031170503404001101004200300060290701e02d0046885400c02425400003541c1148100700c20840200c141003210000281181c001000c1c0c000b641d00d050042d8082c2c1032024072000c0c01e01c1a48207501002c0c5030b074072629072403c0c0301e0b0300001d240c50300440400280f101706800c03040344401004103101030140c005000d036402c0132641c1840115003000c2c0c2440d406c0f941103500081d05041c10082000100144c400c1c083d44074580c262010071001d14010706008418443ca1180d5400010420042c00f107941880090440a540c5140006 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 576392742 1250 576391492 576391499
    0xe0123060906030709030b06150d0f140a090b0f04110f030c180a0b0f030a03111501030308162c060d0c020a0b090307020d0b07020f0d1d0d1106030c04 66
    0x81181d0703c00c64100700041d00c0d01c0c03c00e200f04040c04032850307003184007150402c0144900c070081501c0c0744104444881d0480c0c0e100c0742c205024155400880c6104443d02d40c5403901d10b00410f45074040c040c188e0048407058042c20000710998048501d00c0c1c0590341202d180456032000304107010140e003005041503414841c1240004580d907038004204888041c42c0d0b142c4845d42010031405051b01c0900c0c40c85482903800c4002102a0346000602001140c2c151800c0307015106628603542c00c0003822040844c001480e0b5001109140e000780201d40545003040c450b00c952003010f02e0440349400c0c40704c11160038101c010402c00300d005c41d904e03080c900404002e044618014400c9084006c43d0320010f050005071300444603c5052062004d031145c0e00800c40ca002e036103001d200740e0000d042d043d90000001c00031f0b5075070400b05805520030000c55580d540c040c001c40300c20800394680a0241000d03400140d9000c08080811029030916000b4246403551020340c008011440b401040000c0c0c1000300400d9844000b8071000 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 576393992 1250 576392742 576392749
    0x21b06190e3904050726060d02100e090f2205100c02070b1206031b030c06071e2102031c02070305070b0f010e01090b03060105151e0901090e01230609 66
    0x117402801c0c25115280c0ea02248412010314010070b0003e4016450b4850410103070340c440040c100041541150701c00403441c184d21054842c444011039a90700400203804110005583c0e08019000300e900100400d0111030400130300c01c000e00b00e14401020354103d400321f20340b841030f0340e00401d882c52118010f41d0020b540321624603410760028107001d40002010750034482981410300c000c204101080c0500d410704029040443c0d5901a20204c00780268400101d40040c040000480100c0072000780b00003248061034107200c0d2141d51141060411140010090222140000101d5610403409050541c9a0300d005200000a400c43c420580c01d1103070402c182d20001d540345011900c41c650242c3d41001e694102a44954941e41c142c0012800c24500325000c5840e1390000380c1e2904540045807544040103840e0341101403801a04020140300307002d0200403003a02d008a004e0500282d0030b903542084140e4400551b90b49840a1181002e50110309290250f008400f10510120300c90141c4a50b00d00b00d00340020 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 576395242 1250 576393992 576394001
    0x1503080f0a03060f080c010804020a1721090d020f060403080a080a05060406030b0412050d1d060609060d1205070b01171e030d021b06190e3904 63
    0x4540048000038030607011540500c100780c068a0344408001480d801c1989140d80c80b81146c1d43c170303810300c5940b00008046555075066040a4413442c3e2a000f01350355000349a9640e00b0031003140b41008000502c1c40700403140500155014bc40b00148480441030003502442000c0285002e0103030003010400001c0046600721004109080f07180d5100e101e50724003591803404554018010501c1070b82401020004a10b04464403500a90070007003000d030040c01010180c0f030720300ca0030041286150809000203a4250401d0448800c91020350070381e00355554950420100c8036040340c1c69a40070558040c42c001003440541c40581d42103142c00e10364908140340e201c1e03e18036a0241c3c4101e08a0060948008000c1414403200172040d10516506c4c203001c010b54400751322030103000d000200d040d50220703040030544030074080e810146140301b050310401d08043c0e24070480610004140d00b21207051107000c0700c5001001800e60301401480c4035601c0d645001c80039401d80c105035412859080d4448183c24805940c40c0d101e0b = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 576396492 1250 576395242 576395257
    0x50d11030d0207090e06190c27030b0604050c0703051e0301150f0804050606060705100c0306030c0e04030f0e030c030f0606041409060417160c14031f150308 69
    0x144102e9140407000c00a82d010f8501054030346c1c2282c0c051284004c01c0202e0005924581440840c01c010059401c954000001813041c050055400a116062a40444500a417809100412030944e11a030a003c203407101500e0340740750408108680c0001c80e00c22400703440a03200203a04008500800192190103400030381103081524007010007000201d42101c0610703003001403401c04010b1860103031200c0f9120035004089030b02031040040c01e4020000705100700d005c13480281408100c40c41c0c45c203000030001c002c81e00040b145104c4e940400b00b8144000440c15129039030503600c41030003803503025007140d00304c0280180320382510a46101407016601804104094243c0030000c18903840c02c0c00c02c00c0700b591407510004491440d86014046001808500c0640c0503403c102e02250320030704000000d14921941d08100341c4032800311030103020416200b8a55003195032083c01403da1007943c0003056207510107100a481c00c02c0c2c60001c410b11824950b0450300d6080040711040e054159a9102c1e101213a001c0351 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 576397742 1250 576396492 576396497
    0xb2506020318062e1701020a0f11070513060909050c011206030b06090709030b011707090203091e102313030504171c020102070b06040510050d11030d 66
    0x8026034022000310050030380042c0c6000700454107000d4032000503c0718407203900780c24180d4001004445986541c07010028140600c0d90900c10009642d158002c1d04001541c100007400d030415004064411401a10444240c1002d4501d00b0700e440100f04400c108505003003151501c6100000b03c0004611801c030303242d8050005441c081d070490b800101185019844455554a440301c20300100f0a82040030b50b001000391000041900c0b03200302561007500f81d07400140042c00c0b910000c01c425106603181c14400301d05800f2076490b10f0300d41380d00d00d059010484e00e05656078006080440c1100340c0b442c121407004090410750318010a0448910180e600f486044603030582030040b407015070125407850302d030302014221a904210100e603030700501c18410340c810a114080c004100e0340440000740506007a080788040e50403641c00c060f40c00039011b50010b46060710140c01142c0082c015003014054648035034480b484194400d0f081400b001918400e0180962b00040740083c11211600c0c104241003100b110381c0c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 576398992 1250 576397742 576397747
    0x100f081b0a020109060506091501050c030f070f0309081506100e100302041a07020102060408071104060e090d0908100c020f01410601050c011e021908100b250602 71
    0x60070017000b03440000c0d110601611544c801c004410025400c1c890182c4801d180140da115022203900e4552b01584440c0107824a00017226010000c84d00b01c40075016101e40c50b421045592606816101e00280d03004032844000e560010703010349401c030000d43c803086590410b400c26030715600110300b04006212031000400c1d400501804181d0081c0c2806e50048079084406151441c00da0000303448840c081c000820204c07002c0746141c20030030884035042e24003001800401c0326035070740d0210052007c0144c440b01c03400d00840484682d071612400003901a56a10401401350a12001c0001c0c000c12203e102c240840c0210805402c0c066401e00030181680621200c880f0401c445244030007801000708014403c1d001d0380700340220320003442e09900b9030109090800c0c5844034a0780045c240035080d05080d008202024501190307100d2069405040b038002d100420601500d030345101a180280107403020b103407400c0140300c10020701d03058000400200401b0240908011980a20200384c01c40121003100d40c40e401 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 576400242 1250 576398992 576399011
    0x705010e010e010b03010608030a0f09092306030f0703080c0a0602030c0c070503061306180b0f0901050604111606020c0303010609030528060504030516080c0705100f081b0a0201 78
    0x4d0080c2a40324104400802130b9519042c0781d160740b0302c105c59950052044148103e80070902804104000f402c40340c0301400300300740e2043d00b8454001441e6011040c0f598034400300e805410001040c1a0608807a0010400c90b41036441d18043c0d0781182e140c00420384618021503002820300e001460140d04201600c41e280c2d203410072400c0c180200750304903d000394000d800f04a61502d44a40c514007082d040000003074a1003500b04070280000e0800c101914a03082c02c020b0103001b030480c0350014404d0b8501d070000c10454036110200401da50314410210408081400b1012114010817005152580700d0a001803070310340c0d020110742c01c5410076070061020030307003018081050050500c8511420850740e00c0c80c041841030b5044101c0d40002107103025103003590f07410020301010b0041c801c6800301212100c10b00c0c801c882d14903043c0c485a108a410340007a0042800001d414103250441c0002c10182d41c075141d800d00000f201c121202c0900404039064190050f4150741021b0103980100b000b42e00907030000c60280304 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 576401492 1250 576400242 576400271
    0x90a0e031626030c030406090c06050912060114090907030b070810090b130915020d060503010605030a03020d080901090c0b0426031b160b03061804110d080705010e01 73
    0x703800700c8001d10b10851001210020190422654490440c507049a01c0792254141600140205030f40113050055003040412403540101c044c000c1d148041360755a440450303c2e40825201d07030007071003102d20b00030541c41f12000a00d019440180d000da00b00f01104e05066a0740c640c2c403c1031505451540102d82681c09002c004540300580070042c0c0350310302d03047c02600340c1400402c29800c140c0000c0c128882e510401c1b14100051090022200100c00ca020f640f25100d040c3c2040040160f882080e101390300c2d0400010346400c000c680b2464541d0550041c1018000703010050316000002455800155a00d00310700740018446040a8060000001060340ba141010402e0103070306030108100d900e20050080c02e55a4480000c200c4001c049264105c8081d202102c480c030789001e105003100ea000c4107080201080d410360000140d4852002100e00c500c10003014a1123450150003524064960440c44588130a242000d44107040c1007071182c00818070b0003809448540c01c5a19180c001500d0340d440b005d42844540 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 576402742 1250 576401492 576401513
    0xe1b01020d05031b030402011806050406020114010f05040b0a0b0d021809041211101d011104120f020f0d030207050306060102030a1d0a03050d0806101d090a0e0316 72
    0x80090074010f14600304500046882e000d000d45000c56114008002000c69200309041c1c500300031480b0b0703440200740c0c6840000e05540c00c070740507040056280c081030200c2525000760460407140e007101810000741c100820300029214020002d034100c2002c543c009044166a001800032460264005072216011030900040d00a940010751041420200780408101c010100c0300c00700d070140c2441100209d00728842030400d414620301407002c43c42c2c44158080e00740800142801641d542c0020810b40f49104031201090060f03020b440304280e41800800e0004090254909455000a100700b214108060004c4c0007101c2c2800200d0040e0000c1c80100020300f4100422a00301c24240051403c00d14260001894075040220002c01814100700103091926504a4140915007010030389518403811003000d41040d800381d5045d03000b00404541107180c06e1003080c60000e441d14402c0a0b40150f150081040790700302010b0141346e002ca40c0d03010342c1222840d04000401d05c03200c4d94003000c550324600b0b040584440 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 576403992 1250 576402742 576402763
    0x9060409020703200606130b031203090d080112260304210206060d150b060c030a080f0106051c150f030201020f010e03030402012001020d02030114010c08041203030e1b0102 76
    0x1182d513603400100e80396010412542c130000684078060f951001c028803001130300d0884141501400344010500c0c881c907202000b5482101c0c0c890032035241303511503039040380c3c0e9810922070030b8446a0300c2c242080020703c0603500b050a07603040f001c0c0c4031f90074130051162030072652060303d0031582980d005803603840500104011141c82d50250000e003030345180079000b107184610304a000070080b40e543d41007031404007031550018060440c0a802c003603c0c0d55901c07140307541d03d038800648500441c1c4404001003004218081c00d0703050310360035600e0034100b480741c5a42a0007003056040907003010343c8074060011060709035290390000708000303104c42513a54910300000e03083c00da01300000c3c4aa039040c480400a0b680c000801c40c2e4005034280b0304800c1c10f01d001082c50b83e02c0c9541d88228a540d50001900d420400025005581601d0144048900a80281c0019079000c010a81d0042c1320030400d03c01000301c82078030301405039402e000323050214804010180c2e00c1c1c1001e01000d01d055410318012114603155904000e07a9165 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 576405242 1250 576403992 576404027
    0x60c0c120c0c0501030e070b0a0c1e030905012010021c050c19110307120311070506041511040f06030b2e031b0e011b0b0c0f09060409020703 62
    0x9507555220302c820500326004960502d901c4141c4461140020001c440044c0743c6021300d01e81f6180d11041c01440200d682d5020303664071031410030004040310703e101605207181c0d0689881c0c2c602480d0000640c4c2d60680940305001070b0184543c0b00304410020300066200c284103040059603000103100c900c1c494914119206101840c000c1084880612441220103a1032010424012100011807c80c1d1b000070300b580907801408045200810849020085d814100c0e09807000d0180300305144800c0320501a48501814039403217400440d010400d1294496842c4401c0000400d03c1000c01a01ca20030358880c3c2c3c0408803041b0044020807540c0e038544a9102c05000868001c407150390622000100820107c904002c0075050356844042280a03034001c02d0341005880c80c146110348084409065182c61000848c0401e29141c10760311881c1f8840782e0009031a500c400c156005440c5c2c403103000001d4000b2841c00000c480c5c104500641642c528001c0e000402c5403c801684d07034410703860001c04040c0f000c00250003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 576406492 1250 576405242 576405257
    0x102403150602070b07050106050d030e0f010c1220030408030705010e070501050a0e010912060c080c03090a0f020d0f2303040e0c031b04080109050615031c020703060c0c12 75
    0x101e0754080f0714103080722103039450951140b8041c10f165004000d0f680c840c3c0d03484603020214408054115134202204001100d500251824110040d00c403d65840c600070302d081d8689103a241903601440418041c5c1303846010000d5102401e07080701d45550300c59080090161300101d04d140c2000024024015042940c034040c0c80c00034982400600640220035100050000c40345009034a40d101e480d00d60000e00b02c0d04244101083d150a260780204500100c20b0006006800010004be298004036801646000010154807034140c8595204c40c94601c4120703030111000c61104041580302c0c09041e90503000391580344054000300751942203154944220641ca4100380800c1103d9035140a45c0340e030010040324180c0e52591801c131000c0b1010780003107203480218004100450b4000e415405001d045108204954042c2c0350000032045440c0003440b07030795140d404064142d25802110891000000c4140102c0d10625226610700064800000e00c140c002903844400409001d031080450460841302d041c1480c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 576407742 1250 576406492 576406499
    0x180301050c28021c1716081005011e0309050d02060f070c031d06070f030f02100605030a0609150c03140f07020706081e093009040510240315 62
    0x13034440030b001c4046200c80c610f07110f1030300e2054041d042400780d0342e0301c0714203502041c030300710b48a107540418116009002546143c0000d5002c0c0c0d46c1c034801c605a80d4140c450807403d0001c14400307881180304400030020942c4460404000920400c4034040e00045500a883e05141c0200c544040000041c260010040c0081030340f004a500328000f036440c0381c1240d00a80303101010304041003451050f41c0d4004d20b900c5000540809059219802a0f03041c0350503801d58598131041001d00c4181c480b01e0040681c19004083c500e0000384a0b60f00854000f4441d10303a0440c1c1c6107160243d03208440b05014144003094584207100c10b00603144202130fa11840b002c500d20302c141000b800003580c5504c03c0c002c0000744403801c00031460040d0362003c002401c0007113414803201890240c1c050303512031120085048034451803210500502d002194041079170200b40016078108100d41e41044041c050141003050000c60800000c03c006089100b6119107410360b01014880381e420080c01401c50f1900852251184030386441407 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 576408992 1250 576407742 576407747
    0x702030a2001110f2d071b03120306060216080c0f0d080c01050105040528050709051e0a0923060f151b0601061b06020d02130f05010201060303090506180301050c28 72
    0x280c1d41160040002d44503d82c0100010500303c482360406066843d032044aa0b01060f4503401c2344090314126400d41b1200d1084135501d0006038000d008481d0035800c03188130403095091281070308a8826000302450106c9510352105906070b4000075010000365101c100501060500380030b655088a07805104583d00580c80840521f14200b000003284501e03120404159158403c24005014000060401c1e00e0800000114100f901044400703501804800d80001142951889130040500524002e84000c060360b040c4503000d100010691684000d0f40f04601c0c42c5a110810b130032888100c161442a510360610a9801040c03040c0000da410541c01180180400c0d80d021000c0041556207241c5058945000d19045002c1c7c020600c2c480c061a10114803c00d0301031505c882c0b4821105d01b50841c0c0b030b440352a00c004900380d0341540409008240850341c20481802e100d001840c011000c24901841d880c002000a800e40301d0a4901c184111004140890010280006c0d24034404050201007010007500101 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 576410242 1250 576408992 576408997
    0x1203060607060504140118050708070501020715020715030b0414061e040f39090608040203011d01060f09090b130206041703120702030a2001110f2d 65
    0x80c000b50300d9030046004c2081c80c991420a204684000f40b004084d10880000411070424041d1a40c2c4110140040d24140118504080d107106a0113415050b041050030702c8071910522860382103100c6ca0000144445015800c046e8098540d41c0c0403c01d00c0c440c004000036a81102030380341102000000380881c5036600d40c0d6485c020605100b801c2d0f2030795001000200200f00342101c001c0d041c1d09025146018452080081c401c1d030494201c0144503c442d01c0c10b220000300c403500313800082955072030180102d901400165520610050000c5402001d00d080a400302103000d4000013640e45032041440880301d0005414040d102c0d008040001c0e051a4450401022010b80a05050075000700600c0654890700708a80c0501013440032200300010120002d81e0348d0b840540390144c1c0b40100c00102e458103102204907040ca520176525104600d551480d15862646100d0f9412219940c0340d034180c1684003030102070300382295240559519903081400d804856071803070303400c01599003180b143c802010154505 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 576411492 1250 576410242 576410257
    0x202209050103170c1c0528020106060c050c04090f1505070f020c030a08070609230c0a260f011a0a0504090b0c16020406090b010e0102010e1e03121812030606 69
    0x6940505100c517041034409214404044580001e0181c01c1845804011900c100d050b516034000c10425030350307c1c2d00312421003000c600101550002412030340c13140b8258028000d070500404190414812030f0b620789a42260516404181a45403400c010b081500454130412446041c0043d0842000001c0029102d2068003401013003158003042c41424011240d21094145500c05200c1c101c42d00111003006180704518010b040500c648a285100350400383c3d40700b002c035075980c041421015807406c003580c41c4030280d81ca418402c0c0305100070305404203024090380584c001256030f245e4000c1e44041c1407044a450039041280101c0c20021068005841c45200c0c551003001d51140c1600c628080b11801d900f410440c001030740c02030800300049840c0300d652344200c03c0340e03000340c03030302e51046030f1500069090f200c04181d4103440d40c100c0c4c1d00d40f00c0349030950441250390020310000d480c5002c41d00b01204e00d04803019280e00c0d401c1f105210030940580c1d010050004005d85c0302200301d0035450044006801c2e441101e0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 576412742 1250 576411492 576411523
    0x510030c17011214031e04030b010f030b0a02161e1b1d0a0b0301021201050415030305030c09030309090103080c12040f1205011506030f0609202209050103170c 70
    0x140704d03000107405106030350203402030102c1589024500088404035421501082c3c840301c1051000189100c3c1c400d6943c0b080320303404165156290380301c100d810700941004184024492401c0d60120009404401d04001c10301409880d44400d021401e11581c1c1582c5940801700b602914001070102901c2914001e01701d215010600460303542d41d6010364050020b03000a15019800800c9005140c91024000c03410b8501c20f9504010101c0f096455181c0e0007103a1002902040c0200003094402064000038400704001608032413810740300e00040340502c41c0c00d07170007138030004004a5071000103001403105d03900c4012030b06200ea06060404203102d0230040d2510600145420146107038003000400c0d0460100c0c102c94580030101c4a9031a48003a0140604540c060400ca162010201d2500101d1080311981c44803000c6811024002040d8080f556001195800e4450486176192442d0f0011242c9040a014640e001046551451814004d0810011300040c401c28061007004292580090065114103524 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 576413992 1250 576412742 576412763
    0x616110102030c070303030f1b080114040b06040308030609090604031d1203032401020a0c0b0d1d010c021b100f0e04060303020a12020706080c030408040510030c170112 74
    0x800607880d40c8120107030b040c2c403402a42400800e0540503407041d4280e055444041c40107044e10304143d110818611681c40104d6410070060241101030459044481009000041d0b005c14000c002620741d0000d5000312143c440002c208891400c080c0c0815070800c401d54010083c074202980d01400d00c0c2070501030041e02c1c7c1000410700d9640c0e5200722841806c088814262627881c10404c8228441e00841ca1030301c003014190207151400b6520020380c12800c0f036000705181b1503650904d000315a00b98490030b003580c041d07a20340074545c03448504690218405000138000041984a514010341400c1410301500482e0030703103c6200030f16498070751024000c880f85140603509840d204c401034424408501c242c640041ca031a0001c03040540014501001e079009030754010304421205c00880c0d94080d01c0c040c102c005004100403407220003039000a190428401c68500c4c3c2002e44500104d8600004848104c0000b034444401904040d04822200c40e110500e6410701129030402035a00d40001c11041d000f403900071748 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 576415242 1250 576413992 576414023
    0x1b080907030f15050108060601090f0803040b0313060c090608010506030714030604063c051c0602040810140906040b151f08010f06050310230a0807090b0616 69
    0x1040f40c2e01040c1900c500c101301035615982016500c2c0e1003100c5460114502c2040410200380d50160300c41110b00355402107180c03906200340c0310b0140c0c00283c090309080c0111022507000550034040d8070558041641c0b000030b400d1510b00010888007042e404103014040070010f001c00035500c00c408440020031000c40da41d481d00c3d5003001c2002020564845110340307111441c480f00c1c000c014200d40441c5925907041c020148205400c3c422600b81601c6459800501c80c184004443d120401d0060140d001d848010306090707440820a080c40c000301500076003507a891000d076100107084003c032a009103070380f00140407903e8141d607002529200170b0448804101e56030901d9025690300c0408401c004001c001302c003010107540710050700312182801100c1201500042c041602c500c241e05880c440c0c403006a50800ba98a0100303031400710150003224a42410100c80345109948070b00040000070004ea0004290725860801360a08840081c081c2d24490a001c001c3c002100002408100666800c0301521108528 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 576416492 1250 576415242 576415253
    0x70303080c09030d02071e080706110709020f070c150c080309070b120f0708070e01050a050d1d06011a0d15080d030b01022b0e040e0708011b080907030f 67
    0x2d066086505101c1e446541894503404100a030865031544800300803560b5824981c0019507040c05210b0741548124420809207114031018a00511810241c404803a110340141e03090b030b80960b0448848400c0020260200003011340d0b03800050404a4441c000c0d03411810008285804515010f464500d001c00403c0c0c1417401070000c04000e040000c03200b65240481a0440035608040f1010664640c0c8080001c0c4503d00503500c640c070038906551007443c0c0c00c4c0044019035540d007114141000300141401000402c1c10a40700d4484041d0001051246172015009050b1920f10160010610f01ba440001c50082c0c1c8902c40a681c02d100c0c0025010400d018030400e81880740790181e000040034480e2803065810303160103034841d8400550070707030030341d10301417804c9084864003103501401c3c0e004180071007403800105214440f40103108030010310110b1070070040000f4070300e0114550008000f5954032044120000d00a640c0c0065185480c1008611841c0c808039890300c4032168230001e002003032070f04080d008118 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 576417742 1250 576416492 576416497
    0x180501061d1e0a0605060403050c04050a0203070903030f171807091e0b04022b0c0206010302060909060f0306010b0a0e10021915020d1d01141501020c031b1f02070303080c 75
    0x9010308803030388890723417420310f140e880c280224040e005030f2034070300400c1121500f030081302d20416a64848100d2245103640441c2d00c20b0314804440100801616020b040c01841a8600d006140d110f0b0b1000c9440d4080000c1402d0208c0c5510951459152148054120402380c44070f030717544001c50f000007c0aa502c0d0000c10080c3c4145241d00a21032010960100201c0b500010a80e004000755000c03c02241032110690fa0b551080c000650b014070300b0301040e0524901032224a911640143c070012401c0c0c00c074000310f481d1080a0304544191100814445d065562080c001c50003404120b80a160b484503920019458842c0b04802c4c00301d40d00700d017082030f0501c0b010521310380e040d0049980c2150390340e8816102038000c108001000c507885041c80e51003882c2c1d180502980d88000603038003811005448040008500c0580b250500b419400f4010803011180d40038828008082004078101103101c0d035680812210070f900303180c0303401c3e00c18242c999081800c3d400034400b81503950508208459440f42e00c42518030f070 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 576418992 1250 576417742 576417749
    0x8070510032715090b0a0f020c0106150201151406130f06020c041a010e09090f030d0606080c0304050715091e08010513050a1203180501061d1e0a06 65
    0xb02940a03074615540740d400e0002c07489000305006560710510b40390300c1c4140d03080000090001442c200103e8010300181d400480d0410032140018a0542282e400a007922a00e511440140580b48504480701d0b80a002d40c815a51a82c9105000c41d4103103050200c1a0f224010720a00407000030a0150b040c41c0d240180102428036000101042079845070003c1d501e0300002c4400b409582003281c84079500409440401315418141c642e242da440a59080c0700300542c00138004910381c840e02e01000d10b2b1000600c010720503003134144000700d04103040100162100c007018003070485da0201041000049000440c890081c0d4007990201320030b181480000311a000d4440d0808040f0140780c1c00b42c110060304414010088035490701c02400542e0722409044102000080087c165410225000b070008041c00c1030f14042c036480307060003c6c4400c102c00c642002d04900c1541218a60b554150900c504504013801c112041500040b00086142040300c511000103500b01c00d03101d89401d8800310356468140d80003500035 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 576420242 1250 576418992 576419021
    0x203090a02121606030c05030406091e0602180a080d0507020a0e0a050a0f0204182013060e09040c060c0215270a120f0623011503060807051003 63
    0xb41980c0c90126107811541c082030b4001c01d425440020309901034050201081d41c5525642d04599031619000007030010824201c84036000700002600c0c20740c5e00d0592807540713130052000580754140058811159601c58070101d01c284200304040110b101c0010b03410000105d20310700103840310064408107000040c036170000815904040c04200c1041c500f81e00c400c1c4181c0340b0103030500c1807a603a030315020304070b00c43c8ac00341c00800d20042c000014401c0c5c080e085410401c1012074003000c00002004500803513007001034040b0b4000800e080c10041c860303004410844202040381c11140608056543c1050900603100e0941407260100901055564510a00c4811a28004400e44d91034140764850002103031030385043e203103107000d694000d07050a0000c025010b64002420325681106141c41d99200480303c071204440307176600c5401c6206110310305c02c01007244c3e18010320030644d2541080a107a006e03143c5090600300701490088208681400040c40d0070460f0300a0b01c1041c1c0300442e100044000d000e034500358105 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 576421492 1250 576420242 576420259
    0x1110f0901030507030905030d090c080f01020a0207060e0603011203030216260f040b1b0a0c230a18020c06041a0709030507360b040506041e0203090a02 67
    0x11a410108024650000d090b80e0822160b0b4a194040c1d044841c0350310301502550080c8800026031155a01c1716480901680d00c0c60007185da1845c20602c0c1c2442e01d44030320b101d80d4000c43c464135071035010010413002d070455003400c20700088910042111030005100b411070141701c0c4c4107100249030080c2c1c103d90622480b40000307080e040190402c88803201c6800c2d1080c03600c860718a118074601d181c00381625901c06080c200c0303a03e4640340c5410702c1019001a0983c2400d01002c0d2050402c84904100640060784548268205541b03040105144502503a040c0040d281040070002d20f2a0b0712401c0f03003020345030803242c901031000d0340101701c0c4001c0c0180005c0750074521588080c40288105c02025110020b988040d0100554075003100f01ea01c02c007984001441644207603000e100e00340004201d850003185a402038403000c1107045818144140ca003001000079981c8000c0504242001e00030264042d109403070902c001ca40e40b000e5012034020b45402e0702400fa47c04004185101401d00c82002c029400070400c04 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 576422742 1250 576421492 576421507
    0x2702010f050d0c09080709020c1b0f03030403031706090105010e100905150c0c0301020f0d051902040e10050a06020a0609060e060405030d381201050703060602070e010b03180111 78
    0x349031380348034025a00c01384102d071000a103d86032802101e504003044000303800310340030048500300200d04850165601c0120300640103104d07101080900001d5020b45e6440010714002107003200e40341c402811190140101030014031044c0d0304001d1300a5035204c1aa45c850302c130908010115015105600029401000804403405c0b2800a2010f80302422441003655000130003072080500300d1003450104648800c041c86180c01c0b00407a42d1000754019044880683c4100c0c100b52214101e0b44903801c50f1450b0138030241840343e80d0500d48190000b40c181a03480e844820300f0300c48085d40d02c414454005051549070305008040001d9600030a0070030000e01d0490364142041d203009034880d04050300d4a50040e00c2c050340c09000001d10300c03031b44900b4064001e1181c1502d107840441310f450303001c030308010b900b0441d07100004051450034482c091003a8002d070b400160241c04c141c030090411900d54000c0303480e21031140043c40920340d018103c0340c0141202202980710030311420401d001d08142d8510310080700c4041080e0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 576423992 1250 576422742 576422747
    0x1806030902040b031603080703020f030706020c0628180519150902060403031214070801060e0102150f06130c021605030f0c0111010f0e0a062702010f050d0c 69
    0x290803540300711010703ca40442c0c00203242c0d440c825156a44051507540c1d10030030105510350010300c401400780c819a0000035080c0641440c5034440401103440640c0080c89102ea4102488815004854200e07050684016850301e104240d505034000055182d0b104842e02d440304d400d00140c00c40c280d01c6020307070f41c0c055102c403007488601c101c0302c2d408d03201840c030b000b000d203026180340c070547c0a941e50042030307a821b00741543c8003282d1000d0040c00070030702c1e1ba40c0c6000c600c0394101018100c0d8070951007941c0d2003e80c1c2d13040c540002c01554081c0c0040d0305550011441008045494015903805900004505415541c400000d01010f40c010401c088061600501c0740c0724a0313000c40c10000d0000f14058450302d8650314403c0c0340e40e83c502801904526005400303003084079803160070a100c1c100d40c0306002140d502005511742c021540c500300c3c6019942c4c00540c84008000391802030300942600004080e2180110708030032015842c001074000c1c104211122403c0c1c015000e4010f5808405071150100706040c00d44001 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 576425242 1250 576423992 576424001
    0x90f0307080607030b0105040605190504031a01080d0509091f0513060915080a0605040809060a0c110f031e030415030b030106140303070305072d06060617060907180603 74
    0x3d09000906007020441c3d00d5029000700c80c119181c60341c45074500500d103507040d24446030300c1c2041c0082101c2007000001256075141e1450380d0741601d0102c0040c65140c00141441d00c2101e5000ea403e000041c002000340359656a0240e510a070b0b910a03a04248060800c0250701200c2c07908600c0d800b082030980c00700500c0e0300d60310410654281c410100907081d90200055800c2c0500e1251555544c01000c8550001d043c43d0081c5400c40d04c1003000504150305000001c020360041c008680004802c1d42d00c01050002c1213584004014040d1a031910540440d00800d4456a016403260710000322000701c44815a401c20840380284002c848030304540c2400c100080140410b8400c1a11039802c0200104c0d000c4004905489100320040c010f62812071360756400e4480341c01c00c000544081c1010030700c98001400340802c04080342a0440b41c1d050406452808404960710f0b5000036041100c051040c5402540d54a60b45030098400c4070f40c001c05581e840d50403141d102840580d8411400a44000101103405421 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 576426492 1250 576425242 576425251
    0x1b020405090c22060f15050903100f0c031109150703020f010f0e06060a141003060f030303051806101802130e0105120303060603070f02030c03030c03010f0506071106090f03070806 79
    0x1007030007620f41d91940c45ca02d00705580a21000c0f0314840c5160b0828501910041c60f200030701400303640d4640b005031090750484002441d100c0145031100351200c0b0302d551502c22181c00100c000c034510b00300720042000c80c12000c0815500071140000089403001d141c02004003958080c7e00780001c2c000c02408001c0e010151202c020500d21a229010114007079280408070042500c00a010f141c001c844420308005094110003030300b0742030554034907001ca500d200d030001341000b42d40070361000700d058100511410030b40500030000b006e440d044441405061540b468042040341d130207031502458a1101000800203200b901189240d00c55801742c0080d40305080d08115048880483c1c99140d040303079420600d0f45a02c0102ca4a0f0f03403190041002508103070140403d640c8400251040343e06000310400020310b1a401502e500c0c40070300c1c01000402181c1e050f0a01c0380042e05c0161a420304003240f0b9602c3c111080460482e10313109000100350320f04540c4440c821410124001405c07200756036038805103141c6030b45054a = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 576427742 1250 576426492 576426559
    0x207020f060304030c020103331e0e0a0510090c0c140703032a050f030403120504120b06040b0402070803150d0b01060f0201020f180a061b020405090c 66
    0xc00c40d8505142000c16203100f680c168032200c540d00caa6038011801046041d0b01610200700e1100c0d0003000040800360000200c1502110380405030415814100c01140d2030100940340d08921001e000709244580300f2504040d104a01090b01d031038802c4200703100d00b00354001101082c60404400d400541c0080c00ea1035090182c0c0c0c000001d0107910305000c0e21450b40f4040074001c40d40317082c94108080d441003101039001c014503031a110800c84650341d0a0400003851511900b1b948003017020300610000c10380c00480c00c0024145640350904e081c66010307a2040b044405000703495600001405912030b80c00240307541c7c200030b00031943c07a401850001d202d900261001445403044051102c580c1c02c08010035130025800c5140c060050b8078120040310030303c500c200301d03008554003405241c1c1c0440e6888068243c09100200144a011403201804071800440d80701004001c0380c0c1c0b01382c00030f68610022203820b00d501074402181d46e82c0c400f40082d10308a21641c0064003e0b50303440e075200f80e414244402032103009034034 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 576428992 1250 576427742 576427759
    0xa060b0f1801050f09010e030c1c0b01060f0801120302010f0c050a1403040b01230a03290c041e030206131805040213090303150b1b2d0709050109020702 67
    0x70001140c0c2e83c01a4190030742c04c0d500400403807265601544120503401001001c4510302c1000c000480c221a0740c00c0c6107208450f62500400007000b88059600e805850289010000d00640ca80004c05c1d440042c030458444101c1100ea100501d4400c1d00207001d40f81005c0c0062000300c294100081843d805140a0340004e00300c01020800d004c000800c6038000c58212198801a9091a0385a0350400c860541aa14100e260f4810150382e29a025a400250300450b03d5140c03d20041e07480300840442d18281c08000c1c0040d01c10800c600c80081c0a41c0d099503a400c2c0c148045495041c1c1811420001d500060340c015004507407000e01a1340c800c010410f41c1d40341181242000745150041d0242c0364280d500135482800b40002070b070507140983c4013100790390081c0340200d2400540c0d11000301c20f1025420042007540001440c0b0582001840360941640750980200343c190051656015140900c502c401e1111a14496010001004001c000e02500c0140b80030445540c0da0481c440c004c4d030010504902a1524 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 576430242 1250 576428992 576429037
    0x307050a1e0b04140c0d080301090b0a03061a04050f06030604140708010e060717090a0305130512010506270a050403050f0c160506070803131e03081b07030f03050a060b0f 75
    0x6c51064003880f0341c07000056003144d007400004c80c05041200b45c070982000c003800b8004041406806019407030340c00d16004a0489041400b800b003500c5004000113008107085040c800030b80c400084042d40242c000c0034080d41d01c444401094141889030f402a440c640c00d0a109600500d808111030380a00c002d40c4806a060010841001d10f03440211064411900300e5650040828040e8005000324004a1480b100940d180c0c1d000a151000c9402c40c4105ca039501d00c10042981050201c4408190082c00c40e00714980304403036060b0b404c200003014103c0307598450001c04e08150152003600c00c40d52003822100d4840c41210252603850000b000701400719140d40a0008150422004a9150f40e8002007890300e5640d9404000b41c200c083da5034100c440e10804c590709044507a502d403140413694800e548001c0582090715004650707500d41c0c1c88120080340104103142c0082d070062015190741d6150f08010400b66070f1000b40e03800800d101d90109070000310000c0c2d0703100c18428400041c1718807011010203000c0d41e0720 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 576431492 1250 576430242 576430249
    0x130b01120921030908040603020c010b0402031e06090105150702061905071a0609071d041d0105060a0e040212070f180c0c020a140a030206040f06110307050a1e0b04140c 74
    0x4c000d015100070020082801040d01c250010f200c00705903400085050700303d03840840c040781e2040318071000101108100c54080305908401c00c0c0c201c0300c1258261420350400000803558140c140b40a43e04100c00215a801c40d25080f0136176070200b000400980c00056192005001a03000302000c079a4081d002518a103041e0285008a001e5100942084c1c0d20b66507600060314010340c9543d1854900c801c2c0214081147d407103000b01100d0b0100c0060345030520540d130500740c0c01d441019000512451030520107005031071000e000301d0342c0030f60100c9902594070031a0141e0350400d88207402c18018034907a44004541d60710f80399040d6840902400080005040c80d071021140c4442e4500000e620443e44a400c20095074881203604401900030401658196240d00044907948a1340c0328809004400c030f420003029400000340700d0500304140c091407800f030a40d5250381c2c0b03505059100800341c3d10003905000508220301e41c4d5010035540070700301c08401d0520307040030644144e03403000e15001ca106410a0710040e09 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 576432742 1250 576431492 576431501
    0x4030c1a01081b0613080c0f0405010503190f0b2401021f0c02151510081308030a0b0603090c09160206040b0604020c0717010c0509130b0112092103 65
    0x41c52500a02164900303c00302c0c120101c401d00b06260320404c140103921618030b110f40b00c0342c01030200310000d115105050b42800b1031118140c01403803160f4500001003200c1d460105856440642c1841c5001c0603901d1841c050080074201a405000f00d0f00420030003890180b480b81c010340c8801c0c1034000a03488070700c41004a999007030901002c51401c50844030703007107483d8454200804048550040d40c3c1a0207481042e481d000c0012500204150500c0150b1f0742207080c85014424072041500c0c254440c1c0c500700e01d00501e921b40c42900106546400800102200c000d81d0000381b100d28000c011655909009040503555009d408206100b041e1890220b12912884600300c50702c20000e80203841c42c0d0380d07152107022820340c0083c0b800d900030340c0803c60188400418030080d00902590102c40b03030425886582d070b170708480045001d90103000d0300700f200b18be1541e6809121240c00500c400041590107014004031a5011050f00c0c3c4480701c0c0c2400e11540030803108c03000c060031010200740d0301e207040300203840103c040c3d4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 576433992 1250 576432742 576432749
    0x605040b0a030201052208011103010e07020d08150409020d060227030a081803150109050c0703090b0c0a02041107021f0507021009050a03061a01020c0303090120010504030c1a01 78
    0x19908104140c2d070a16490803000d1164911b22505a00980e81e002c860300f5142d421074130340e000c404004014801e8041c06c402144e00041c140c40106015800b50a000d40f01c0403024000104ca04000c55400106a4036600605000b960281c98252408003500d040c0010703401c00d4003010803448a5204041d10030441c0460310f580444000c1c000c00146407aa101c4045503805001d02c5c1880c1d42240200d00519102004042c0c0c014000485c8100326614041100b011960007330008041c0180070450f180100f640191441c0039210710740c0d64079135900c1c102000c8a2070420380c3c800003504941007080e0710b41c21098a0b809458500d0007a40c201c00c40000c00c002c0341110b0f03079003036a460000c15001d126910150410410a1119407000d0800a0300140c59400040d1141c40540c02100d9098961008440b0121001a0307408601420700090180c90300000000e9241d02900c02201e04102c030311a404070b410505c100101d258100840001c20503400c15050050113242c5034602039544040002c1c21707500c2540d01c40c0c08a4102c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 576435242 1250 576433992 576433997
    0x20f0c0907051804051609150203040303032a0e031204030b040f080d1b03110a120b0301020d0905070801291e100e01020c030102040b0d0905120403060605040b0a030201 74
    0x496807401400d4505410000240c50b045220550390082a10780340304081c090260150003e90404620000401100d03240e0030107410031810302c40001d202600041600e0650394541030200700c4002002c0c102da88401400b41c800d4003c1407110200c2c104030b40245085c2e00541040c1e054841807440e00f424031915100b6444000e003480780d104000390204800a01444681d07114902440ca03140c0c0d884c942600f900d254481c450620f100c11080d1041c169010700c2006441c40001924900386030480e074020341b074102e80550312045a03880d00c44048090340c00390304503003086485480030080b604880c107145a48950070f028100556203420316010624407049400342114243c5d4604403030586408085c498a0f0440c0310160b201c9888072120145680e9a80031a0840e10190356648904c00300703002d0009140025044490380243d00c100030030300003c4c50b00f1080341d081e0401c1c402d000c1040201480c0c50792074036200c441c0300c1250082c041000300402034550403100c201c03907003180c0c00d04c90301e0f0003102049806042840000d01 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 576436492 1250 576435242 576435259
    0x6051f06031e0e03040503070b040906050111190203070b0c01051503060c0a05090f0a08030a02100c1b08040302090708010f060e100806041506030b12150c070f150606020f0c 76
    0x507118041d04850000d052103070560f810f040d1b54001107880c011407908802c24035180070400b8041e84c08144505c1c0000c10003441d101c4074001441c494262142d07070484501c00700d407026040c1141036490801051004180325940030f41e4510109042a0080105403441d1200c401c0c00d50b071070205480d0001e03009000349039021002c0c7c035002a02c1001c0d141c03640254031542d00212281d03c5048950350b01c084050003440c044003e1940d414004900074100962440055a0189480b0612aa41da030000c2c40303800b0000d109030b01d4111844941441c09940c0a036500c000c0d881388034142000302280e48818014104d82411a1a200c96a1691b806581404044c501a50015981074400c01090701c41c11445400140180001604d115001c1c4218259009138000d00042511420503113501c6c10108910155960618042e00000d115542402280c08001d0174146190001240007001e110b2418150800c4070781c0004080642d860f030560b4040038000d1486121301502030000100111360000c186c4c0e08082000900101 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 576437742 1250 576436492 576436541
    0x270506031915021308012d0209011116081608032b06030b06030705010905060901030c02030c01020307081602061006050c0a0611070209011e0e0c0706051f0603 70
    0x80c1c800311115000da40d2000003180300501080540300900710704200807180640c060408403503a0070f41d001d0902a95015017070003e0a02207841d10600564000b02042026a550b0100801241d801d078101100011328015880d406a141c40685841c90440d500903040d147d500001141880d007c07a110720070090b06400030048107603200002040d1405105420044075054089501c0447c1165015001100c034160f101040c81150320341000103c0c0100800d181c0901003d05040105030203000724114203040c1503d80c0b074a145446d000b40f040d101e0b0181c0c0c040c004c41d01d0b441e0a583c020544941605d840b4184410b1200740d400441c804914107110f4030360540c0b035407081d40c0741c004100e51301d6010003c030055602071401d00b000003582a0050030740070007075645c010f6200e601c82e0040000341003040c0d00a280300d0303a07008140402d107150303510340008940e070f201401407c0d6541c0703004406071441144002041a4540020006050351045680744050390180c00010aa81c5906c0d041d030881c2e03c10b1987d000c0101d100705501 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 576438848 1106 576437742 576437773
    0x913030516050a061505042304030921030f0e1e0f0307090209040b0303070b010e0718060f110d0c110a0b0c0307060e0105010608010b091927050603 65
    0xc0042e0755540a14003241d80041c0d0303008d08951106400102890300a609600081c64180d0444040d103201302c0c1402d03a02c002055040f4085581007240d04001445004ac0008180014080e40781c00045403180806111510105540c003110008804c1e2844d2814441d000041c0403501015031282c452a0802c002c1d03030507514401c0e0003030b40148071040104400a24045c1120344002c100c0016882e03440040701c00000e2120300d0340c01e03180350403400240c00703502c4403041c040c40c4019a0b41d503c00d404212206901c0d03030032010150002030080307201030b00480d000451000f001c0b034004000c3ca2130640d13241e2003011180c220b00403c41da6504085034807400d06c0342034080c000d0520300c1c280c004c01c200c0d0304010026100c800b060040d0032030710002150f145c0c034548030421031030044080f4001c5000e0310b0766145070390cd6461b808415060400070701000d10040c4204d6038001d071030080d180280500311800c80305245 = true := by decide +kernel

theorem cover : BRFrame.Cov 576258992 576438848 := by
  have h0 := BRFrame.cov_init 576258992
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 576258992 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 576258992 ≤ n) (h2 : n < 576438848) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
