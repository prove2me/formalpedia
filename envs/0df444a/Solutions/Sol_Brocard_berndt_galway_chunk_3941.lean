-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3941
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:07:28.108266+00:00
-- url     : https://prove2.me/submissions/4a19992b-3f0e-4e8f-8f40-5c3f239453f9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 708633093 ≤ n < 708812949 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 708634343 1250 708633093 708633109
    0x81201090501031a070504060c110a351903021011031803090d1115030705070314070c09110403061a0109060f0c030c0218160f020c061603050702 64
    0x445000010301d95065040c0f2006500040e00302c0d40079002c0038410465030310f03031180030344080b980541010403100b0710628240500101c2501d8150f08500018000165403034105041071072801c00e1110816894900210503181c488a40c032030b130350203a2100070380000742c000544040320030303a01070720544060703054500d008001c0d14491a17003200c0840010080c8802041c5401c040c0c403038007105000a40c5070900c12800700340029080c100140000800d000300782503e8540000500c40c0d40c00b1490300315501d150002000c1d12941000304158005035070304010140c148202d00441e0083d6030003131010400a80761081c0c160140800714a0401c0e81c03001400700000040715405003920b0111001e0080d1445000b40300010701c8024a40d01110400c103007201500006c43d08002c5000d0b00f01e405103895440100721340045000d9130544142c80100c041010704200144a04107030700c402a01300b543d11014041c03d4070038120b07551041c140300568420410411041c038800030396141081c462080c1443c90070910260000342d507003 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 708635593 1250 708634343 708634349
    0x19180801150f0f05241b1f110723030705010e0c090106080f091c1e0203030105010f08100308070f0501200d0f0e061527060d081201 58
    0x440718031009205505403204460003600100502281151915001414103010404080c04c00f0050200b48603404001c0703800c031845a008030f28215440c440718115141d8a90300280741001e6100b04603078901100c2198003d40300500385400c0424184a0f10f0340301d039149481d0044034001c86081014031851018801d001510585005500025000c52141701c12404c024210502c540300e064060b005020b2107410501d080d40090541c1540c207815940d80d41450301d0851408d4903140a00c000d2a12103013032546c0860802103008030b00001c00341000300d600e8144d80c1d0740000e00400d404100810701e4005d110b03106070442d40e84402c00e071200308680c540d00d440d040176a900940e010754118021211520a1220900402040a180403907440c1940c9000220038080e0003800302700400d00b9200d030800c130514001d035001040c10000c60790a641e0207051225001c503010002c0f040d102c0c080c00741c0400b40d115003590701600c10103110b80221099159910b000412046d94a0020102d4604101341f090140482005540c01c0c06 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 708636843 1250 708635593 708635621
    0xc09010e1c02041d030a050c0c061201180911010e03121b070608060d02063108010e0f06070305280606030506060715020f0c060a0504060b0619180801 66
    0x18425401404207807100c080b641c4102213591071000e044540b000003155800070551070015100c072540741c000d07410101200c03800b541c4001c006c52010012440ca6050078101d50860b404070300c1d0500c2c22003009041c0c580e0004050510380304030032051125402000d440080031001400e9400901010506401f60307003041441185880300608001c505074020050900034047c20f05109859251280c0003843c0c0b04041c81000780500e501040a0440984801950842a031408090b111008049021030702840840c03040034420340c200711410030820408548841c21540d40320181101e1b0703603500001e4000d0301002e8101ca080b0203076503019800d00301040203800e551110484000c5a0b4501e00384000f03080d5071003d80142e1191004203c804000b8484040c0304c80462020300c0c0141c0c803080215260b41d924010651103044502506041000c1c24085611003889940700e41c108005400340d00040c00440d00581c4444c00081aa08040b1134140b0f01070501c43c9106051401c50040c0341b41c40b04041400c4d17504003a60180 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 708638093 1250 708636843 708636889
    0x23040605040209070903150f0e0604110910060e1005070807030203031e0903121005041a1305011217090a0801050402100f05090105070f020d0305030103031706090c09010e 75
    0x45183c9220580d4100c20350785402e6006900703544a610340f000511841c00045903a40e00402d201030348581046a0810103041035803040d10307080c241070340c03040304030100325104208050005a49400140070b80c41500c130303030f542c8903254048103400707010518044030b8402c014130600380a0040040c1da000b004020140c0f11743d01443c0c0340c2c01c1802c8016035024045801c40c581049103400c02003950400010f03648102e54407041414151100800400d40c515150021900306040c1082c4002d00c040d00108014049000e0710100204000c104201c4c0484200780120b0712081c80d40740035100800c0000c003204903106c1e0b8030010a40b40c1201038001400405080e4072591050351581c041106502d480c01e400d0006012ba418a44222420f00100824030b1044d902c8550601901041c071506016034a00b0364294036070b0140c000610480c2504010f42150024070042700003403504044054002940c083c0140911406070191a403a00d0740c40c0104090b030800030002c0e040200904800171942c0c0c0e00316505201822619a5603 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 708639343 1250 708638093 708638101
    0x2060d09120c0c05010509010519090f0906140901050d02060a1205191802130e10020d060e0c040303020706141c0c020d0e03070608131a220b040623040605 68
    0x780b0f91009980c0881d041c010107026400007a41c0110840e50b4504889100100c00401d8460544030034441e50048000b0303203110303000440d007510694000d0042d21010310716441610303c0340042225195090003803e0300010f080e92440e005003800b4002d000404224200010700303942d004041c1007203031000c0310501c5003018211071028840c0c8492040d003090b40b11064585060a442c0c1d00032134011040a04040340c1c0c142da0742040e030003050f4103118201e05c0c00d04000080d5501d82000020001500b818000c210010001c1404a90040000411107080b01c1e41500600719040c508941521b05044441da1540080c10800c0a4882211607a81001032202d03951400240d003282094000e04e40980880f071082488484070240c0c03526030f000140e41741115158588103940340c0c3c03807103a0000224000740d00100b01d10020003224a9905800d60031512481410b22141e15114900c480c00681c01c10510001e01070304100000306010a0180d00400c1c1d81ea205120121208400184250700050003103030300790341ca9a5240140 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 708640593 1250 708639343 708639353
    0x23030408190c0308041e080f040510050705070b0f1b0f011d07050d021c0b0f1311010f03150b070c090e030a1115042603070c02060d09120c 61
    0x5551240d0945000ba82140103aa00a07081c00c0010784044c02174003e102000d9807510380726460500d02580035074030b19184c0c01d00289084064005010b01480352004c410b2640031588150281c81c0c0c1c00350000004e01c0d00b9483c00996030010340c4001c8024408800411408800b042501c2039a1a0290b580000f0f1081101070441103003143c4101903200480b403003c03102d1001c811310004542c03045d40c1c01280c41d0405c0c0d400354030010755101e84210f00794202d42503251504040c001c01ca014544100028030003140e00d50b903150300401c61001d480380010613480300e07035424414651080d207844054021900380040d82c440030007004400c010050f0300030800100000b4652042001140c070106c000c016400d02400110b07000e4141d03603100c0c05100010300800c8000c0e5a03180d00010204864501c60020465140640c1801c1c1444403185070244144002150003403510f03030114043e0b10469100e0380d1103070350f82c0242041550804c12640c0c40001c10227000c6490306c01c03040108203071804105842d070a0b912003400500c80ba10380 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 708641843 1250 708640593 708640627
    0xa03020d02010c09030b0c0424090501020d0f030b030f160503100603031e05091008010617090d0f020f0f0c01110a0b0a051f23030705060a23030408 65
    0x602001c40e41054801100c241c1c010494005036548101105542d03134410034034240c240246c1d44801715415a100001c03644e855950320100f411180307a51400340c140d860b40f005aaa528400d8100000a0000907070100c08901c694088521008010300f91404041107540c26442c2198031254880c040c41e07140001c10041c41c04003c482090240c0c041e05103c00303891910043c1c02e0405855900c000c1e20071a803000704507503104408a03500894010400300b0101c02054000b0501e02c001d0003000086135820144188000c1d1001c041481101c01d08001c0201d020440000c5400794a04140c0000350b1040070901e168011007803050f50030107100d020082250359a140001800300c50b15540030120ba0700703c450804042122140220340c404080030300415540c680b24a010501d0801d00080034081002c018042203041c0c1c4503032541c145604204116004070949401c06498800c507101e11a4061003c00011071064000d61031280c4c0c0e543e10b0b86030411042d10307000310251035500071101115146c8000403070800c1c2940c4000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 708643093 1250 708641843 708641863
    0x6090c0102150a020307050c0d09140f130b060d05040b040b06060c0d05070305090306040f0204050105040213031205070203150702010f02121f0513050105040c0203120f040f140a0302 80
    0x4010250b100030704580c810b900314064440e0b446650004009200a0300a10403140c00c0c2008000301c40e50052064002015130b0082c3c080e00100000900d00c04601c0d1605e0204844080c1d03008200451000d0082100002031210003c11a0400028082d00d80c40490911840e48900e0054114100c80d1800b460089400314004164a205d214248290f003406280000c0c0f5031f01c0801c450800c1a6900602d08040d17500d030048480b419410b103e0201040708014000c00010582c910907201400140d89070f00801041e8040c400400401302c01948003000841c1020300c2d0040e0701959806c1c8145490b0854004c40e040c607901725000818400c520b41400415542440740b14228142064118100b805d4040ca011711041c02030402058120800d80c081516000c4103040c00081c00001d0020041d00040220304025000912070325210b20f1520200181290000c0304580c095044000d04c841e15075518ae80d5003515150181060f5070014108c07500c180001c400c0440004c001c410200104641d255910b002898084010 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 708644343 1250 708643093 708643097
    0x3060b0c0c2806180923090d12050c0d06030b15030622060e100c020c0f030c120c15030a0c030902090a020a0320040315150909110d030206090c01 64
    0x811900c100704007210040d16290324000b0412841c505904030384e640160071101c40e01d40b1b0700e100c00b0070700b00002005c40c1004039040c94903c030b103594260505846a4800c2d810001291068021141e00b039035079400035038080e60b580040390402d000100c402003120385a4000f220b405c0f11620078407100018000c018120301c50708030006c2c0f01d81d10b40b400e001d42c00303e50840c52100003074516504040811045da08980c9410325128200c03804048211038940c0940036002282c40580030b400504455402c121042c03200106010b0000c0180301c0383c0ea400d05c01c44d00d0b021000c017076103409000c1080c96035648403642d040000200b25401c07900c0341440b81d1810100c600c5504003c061525000c0d0040048e01c9a940d440c0d0300241451005895203c16041030380604850280541c0c1c0c59240303e91030f413010f40100040d20a4a00440346010b50403024040202141c400300a0042030501e601010000c09a054000300d90300c51203080d82c00700e2000314001262142040e1103044002d81c008404200251404004155101800f4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 708645593 1250 708644343 708644389
    0x120e06270309011209140c10090e0f0606071203060302090105041506080901151205070e010f03080d110a2714061602090108030d05010605070305160303060b0c0c 71
    0x90405580b03110b24940c003810301c002900800e140d4542c6500103200a07411582401c600011218850b498141e0782c500c81d0f1141c060380c0042d04d600c0d442108150150f88007169103082e9502c800d500184145002481c0641c490401c02850300000c841c2e05180c103100c601034402003521811441001032003074050f0010340c0500c1c0341c1071b0340d90081040c0841c03840c103c2d202410100d50307648400e00c0c80780c050250340c0207000e2036024001c0005220340700b00c034042101c00e0103001650748043d00c48298030b11030309080c40f81080c4000780030800d0022403088401030508102e013003400215145d00c0d45486015400c10703800c2802240e03e09228140713119050035101c104440030811654102e05142060102c540c00410050141e9404900c08091000d05060000c480350020101d40081d07941d40c0401350b40707a0088100600f600e003081c4c00000c81e140514150366182da450340b115802c00301b22a0034a14110a101030660805441d1080003e004020200901d00c12001901604807200f040c414001c5107003020300140508029 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 708646843 1250 708645593 708645661
    0x108010510170411030f0f190b1b1e13140102151b19030c0e010804020103020c1011072109050d111507061401030819120e06 55
    0x11050450a8054110a00031070b41e450b01d05040000252080000d900f611500f90000c00c006400a145440c1c019100c1c201c400c1480134010100701c0e03455000c40184824a10b8000c00c0c0710b070500d00d09148101e400d0744182030072300c00300201c10f500142e1104440c6801e1480081c84070115058082135a01400d40c8007140b00f20540e40b040000c1d80c44814002420341114030402160403002908001c1300900f44107000c1c96140c22051280d54a0090322441c1d003000b0903d003290719030704180a41000403003404140c68884c0c460365242c0055001e98065150b20016005110001085158070720881d541070064003105601c1e03014500d060541c0d040d05405420a4403c0000c030030140603844110349003620001e4030340301200000d910b440b2010070540700401e42d1112508550351410740a11024000c01406114144028040041c1c014184003080c0809407000c0810000748042d042982c2c090716503200380d49042d01e1003d1511314010b04a8406a01d120f00342c0d0405010300030041c1d070101c2c1d41d000c401c411102d800121b131a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 708648093 1250 708646843 708646847
    0x403170405030d0c0e191e0602061b0d0c0513090516031d03030f0a110702371706100b040e0403033c15031b05030d0302090108010510 59
    0x3000c030040f164a842e00090a002446840c4100e90000b002c0c02c0d1892244280d41d10222062860082c100c1d80b9060140a03081503181d078909004440c00c0d500a0f00e42922030310f0301d1814450345c5074490000107404209100d0b2848207441100d4041c0110350383c0d55151000e4428403041c203255907100e109503a01300001c2c001d81c0c41044842c1c501c100c0c0c082c1030001e2440ea0100032420060355504030080140404420018040070301d0341040d1042c203c500c42000307403046104041c14640241c080103074010f0340c510404030341500e4810b6210030100040001c1c0514041100306282c000269410001100400180e00c1c0040441001a03c0d0080e503190050001242005034010140c05144035205410344003030701041c10716000b5070204003110120100c08011400300440c05100840d4400d821200f180b07004030304d407925140313449a2158555482c0440c0f59107440e54131403100810f910200c4c0485000404800691540c0400140080111a0300e015845046900015140500c140d1005024440204807096a15 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 708649343 1250 708648093 708648097
    0xf0b010203180f0d170702040b010f02060a0e030405130b0f0d020325090501090e0c01030c0e040e03120f010f0b030c0301150201150b040f0b07083708040317040503 72
    0x2d10151a03260341c4441d00800140d03003241418001d40319a804070200c844001082c0001c0c031040380240c4061200100490045455003426a96040140c001c1d0007c240d000c59650040001d5201020899040a8032500060b02c500c0c80f280c1c1d0364013942c1d550900302c4a541844080d030900050100c8241581038000c5e00841d844082581c0d4901183d81d4440746c42d203485030360380c0381d0340080c0c00c0400301001030b50b03180c0304200002c00700d400c0c0e00d207014800c48150f600c9561190040d4110102140c0d140082d40c0904020300021344030007180c850141c0010300045411110141c5164800d8201031800c0d03905514080e40700009408682051081c0c1004004014195081c8400c03a8111440091a00d41e0160b800700100d004000301b040602c6014024100002ea89061502500075110b011078400003003984c0300002185441018401040c00c103050052020014250540302034001c90010103800142d40020700144c42d02d4031401210114a046042c4400c0c994003002ca0340c04580c2903980d98a2500b03183c2c03a503d80d28 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 708650593 1250 708649343 708649387
    0x303060d060608010c0905011d012c13061818020607020d0506180c06090f060f1e070b071d1005070c140913031b0c0b0703030f0b010203 60
    0x4806110001040080310b610034401801888020410214507100061411000c5d204043c001100030700d41c4020040000340034107529038142c481a0481034602d4a800807000000f10b80c2c11120f0080091901030b4a5a1090307950542d80d840000071202d00746101c84e2080c0d14152003240c840ea10702805c02454001001098041e43e0301285c0c529102c3d5001d00c00100c5490002c00300901600800c020700500f00306c1800d160311240010070036100301c5403240060111601a820704207500404052403111075003000c20040145021444419107440e0561007025540030300080080c8200d88001011010700074080072564001c50380389008441e031500da0345c5580624400d410005d12850850780110310f480d01600c01c89014503403101141014654070400c11006501e06039085001b090200002508401000e94003000f050341a1a04406001003007820107140d40903220072200b41010380401f14440490501526105101c0e03500815200d5004c10800e041e642d9241045040d580280310749580500101c29140307130 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 708651843 1250 708650593 708650599
    0x5010e0108070e010303050a0810080f0607020c01020c0f0603040314160203010612020127080a030e040e0303090a0b06030a020618010e0a081f02070209010609140105040b03070305130206160b06030f030306 90
    0x1e034072041458004c012b019400103001d80b0a80ea1800300740c1c8000701b030862161140d0740984240c04c00c1d030001680c541d00042e1009a11449000c101d54461070300c0c002554101d802858607440c0c0da008550741f07000503400402c0b03400c14101e4941110302140307824000c50b009018840880708948007e0350020300b054120440d804480a2404070741c1000807401c603030307000042c0b000800300c0c0c20248250074064203001c0d172854201c0c0160300340300040a0880c4000201d0740682c4445006005a04c4191960240c150020340b040754940540800807000d81c1da201c018000801098600e00304609000001414465010310500d01840c0c0140701041004404103000111720b140691200d1003803008501c040092040d040020b40c0401d40400200b1961780c00b01080c801c1d43d500018185040b14840010b403810b012b02c0c0700d00c25148408100203807080d48603070405500700144110b40c42001043c3c0c0d00142030383d045000c05040c5644078044050611806210554000c0000e402906900c91100c800310340b284001814580 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 708653093 1250 708651843 708651857
    0x42d06020c0f03040b0c0c0901080c010c0c030203100e0d0306080d120204090608030702091f0510120603030e0f0a0f03020103110c0f01050f0609070e13090605010e0108070e010303050a 81
    0x191107602800844070402e260000d407581c4607101c040d0011a508441c0350080b85201300e1600c860981403045a81e1b050b5404203008244c0d016100300115940030002200302c3d404000c0500010040e14200290f0340101180c60011035100c0c075901c042443e20362400c56003010107080c440100050b01000c03daa8003110404d02d40890b900c1c5003014441e020344583c1e400b1215041c540314001940030000710103400c5040c803c89204c075a9445021030040160030420468801c078140c040104041c1c40c05110188500406041503001445601d44500c02c0b04e0442c1c0c8150041842001207003281e01d030008078818a00c10440701401c04508042420a50207000e01000f4103042c0d580650098002061040e6060300026108886620482c402401d000c1d01007a0f9080c144895a130b0049000d6180c42400940304504541c0c407940e00304803210801202c01440764101a000e581d48000d807010aa041c01030a01801021a86400651400110760710f011001e5100f00c03083e0841c0300042c40066403010440b0b03818200307454848 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 708654343 1250 708653093 708653107
    0x5101e0b1c15060b130f0e15091902030a0b041506090e100302120109031b0f06051b070605190213060e061626031501030f0f0603050303042d0602 64
    0x20b000741401d400c1035450b03000104016541c040d005e0710b004c007130701c441d050012902a6035003141c0066000642d0301c0307060030b444004441030350304151041e99408800711150241c005140000502241c2c000d17110070301d40340d48400d0440e01d10308041c0038400703800703d9140c41140614a03000005007080c1c081e02964421119403000700d83d000860301000e40c00b464000b0602038038038a119110038000c001d117900460124081103030441c40340d400c1c82c00e4000800c1e00a00e1740d800c40c80d0f1950310040144001421240c90f410090f911b4000d60402002400d21a03100f004002080d08180400306459514102c126040340d00400001420781002c2500c0002c582076420061010640900014010702844403006d0020710f61410b50020711100c0051207207040040440384400e2180c04454115a01c0121405120a42e03403040307125543d44240d20801f040395580c03d0000701000310000440c140c1d81190b2050307545034004018441071002c7c00d8103c1828002d21580c01514560003c1c5224a4a107500009406607038007280e52 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 708655593 1250 708654343 708654383
    0x100e0d02040f200d0f110a0507051e0c0111010902010e10120c0306090b1002061603090b0c07030f020304051c02240307170c03040f05101e0b1c 63
    0xf054450b040c0b40341c28085180001e181d000c158200800b1101080d0900e21044e003615420b00ca4142a03c1d01c017031043d8902860030700c0c02d851642c040c00c4125128442da12024400d040c070803181d4840d40d00b440011b000000d850400061a586509410504c0d030f034505480900140c0c0c00842c50072500c1001c1c3c0b5036250081d12440191501c1d040c01007000ca20f036040c500100841c3c0d905510690a58848041c2005000c10f44018052019011603101c009603000e40c1c04144034560f14000c11290070850714000c1003601c1d0607540d401b042c90054030811700140b004100c1008242e04010662440e070f03140d10041d0b0800c4d2134040060b120040381407081d003490403d124040255110603042400400381e60404201c24140e5550094440d4401c1720103000245540d0050718040380d810b8682d501602440300141d0079600c03079440c0c41c2c101455908003114580f040c01c004000505040c000c40c4100b482500e02c0c0000c42c81180004400d458004000b94030944c0f8503100300c0d47e500050001c03d003c007500700c4081c0c11782600308840 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 708656843 1250 708655593 708655601
    0x21070828150e0a1e031409030705130e070b250809041811010309050304171e0607081005131512050f1509070b070201030216060b100e0d02040f 63
    0x40690024184442c4440550300002c0d42110f003803241000c20800f41c949402c804000041000050024050b8003148654a01ca20042c0014101c0182600c180a59540000d0208102012040003150b100c8048080c48241070040c0c0c0001c0c020a02c07694075000a4400581103184141070f00500c0c2020003c000c000d100140b07080c3d600071480a0003c018001c045240b180300240441c000711481c2040302880400c0d944640205158254054011800c5c9420303c9922140d02c80d4181c01200307544221009140c01205400c00520700c070f0b620750041d01081c200000010f242080c0200340c40402164036804200c69102e1000903840403100c0000058042b1044240c1ca00031500c5038019991041e04403a1041030140201d8a1005100010121103030030745200702c180303501d50040701c0c40d202540260301d0030000380204000810300c081c4145001481e201d51003044019407002002c007075031030702d81c0c680040080e402c0419500c291089070f424140301c000c3c1c0d03c6000902c0c907003020100901564070303090149108006508 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 708658093 1250 708656843 708656873
    0x9020403030c200604090f0501051518030a02041b0201060b040b09090604061707182007060e0303010906090b090603061308091c021c020d060c020c21070828 69
    0x445035586988410301d1b005003855842188025190800010303c510b40050040303425101001403600b4422823141444400c11061003450b014010511441c5c0142e4591261140e24240c1521240302d81140d10b20080c00c4581c0c0e40c22000d81030030200030a100a11003181950049502125070484958078840400c1c0904520341c03003520200c1039001d007480d4132070010a2407019a031900e0000e08100d4269a50380d01501c6480410400e005d03460900b041e42c0c040c8190040150340d0055001140304590200001d2456109a0109034a00e503176650074092042140a060340854085459601c203042500000f41c8694010340030180705001140545c00b006062030650304d1880e07004054164481601c05221018210305904078810346805402c0c0d006003503840001c50015030040c100c0e10301e085003603945030001c05032455600150301c90000d0392102569802d1903001254140300d02c40c9401665080072a1a00005401600395a08403035400384990316507503011503800c080307a821445962500d0a1115403008590 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 708659343 1250 708658093 708658099
    0xc070b090a050a0305030a11070804050d030c320a03090b0310050d060f0509190b060607060c021615140a1407030507020a06050712080721090c09020403030c20 70
    0x510f0000d160700000550311503915148140410303c10507020700f480b4814690010320240e4141f1060005003030484034054014464100007030704036250b0300d4829a103031411141d40290b50080b2440141c00c0710902e0500500c02000300180ba52004559000d004403505000f850341910004c030004540b507107420403650090002502d0035491030043d003015400b41451550110000d410030010404041c00000c100401d03e0040905800e403601650b940900200060030440c0d01c40420701c042c00c00f00e0038602c5003c410b14801e8004195011703090444651881d03059101c00700209090710030804441e00445803036101e0f03c40c206a20340c0c40c1a2500240c1d20600b000421200d2004003007880000c15406c070b0020150f250088801560950f1340360412201440341c2d90b0010310705415041070035485801241000e0300001503042040540b0080f190204d002c0d507410307400107500c0351140d01410601c141080b030036002d409000700a40c81c150440e2005032484e42c1c00c1500910300c005e040254403213100d184803072484155000b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 708660593 1250 708659343 708659353
    0xd0b010e040f020301090b1f1409040c050903060c04050114090a0305030412060b03060c091c02100c0b060f18040c091a032401141f02061e0c070b090a05 67
    0x1003200c42c002c0d0401d000350004207240410002d0303140390001c2c04040150f20103140b2100049080c1d02140c140741c0c1d901b43c411041c90f080c81241c40550341da00408040000c03582d555600c640c5140200751424801800044003200100000d20503a640300140c3e81c0103003801100190f41d0344000b4040351801141c1e6201401501000c9404100002003503500e4503070743c0c0100414044c400c43c4504154552200b030b240b4002080b003c1149002a00300340c940081500420204c3d45051240d58010a901c410345008078000901c10640701010800600c1010f90403900c15070386031002030416404204810884114404c1000f4450001000c201c808182074029002c0250288822503101c1249038001120720100c82c824050312542029510310007480d0351000703040340070440281e46860002100041e84840e081d8000340d240d040381221480b2080d804071000e10540c020807091810096201c10807000342031420840206c8028007590403804401ea0f0310300c6801c9282d05c500342d140c1080440c03400b032600200034a64050 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 708661843 1250 708660593 708660611
    0xf09030a06060915060206010608160c0c0602030a17060d0605040c090c05040e0a0524031018020405010608091f140702060103110105210c0403081306020106060f050d0b010e04 77
    0xc80c1c0c0125800301d9055002c3c00000f070311045c050303031103503c00d0150b000081e000f0400a00c04440c21001c6521041c00303400c0c041220f07034603611810340340d6842e0b803c000007680c80068062041984089807184a0720340b1480559075090000000d241412250030186c00140c8a00102e000e2105202a1100402c40b9400c200b000386003000024143e90000e1042ca5201c465020000303400c800705024030751180300752400b08480b8000066032445564014081d503501846124001c00c00780526115840f0f240c4031101c080c1c030342120b40384100019500d0581020f01000300c0d000510503050070000e200c0e8140c01d0031007000b0740412121444c140080c895a80c5003400d60740c1020901c80715540205816050341e01841002079003150000040d80da901c40e5100b001e0503105078148140d203c1c21300365052034009070038103912450141c3c0c81d203611005401200403101031001100d410841d807a0248a0700c4000c02160401c2c044003001e180d4080d015001d01c3d600d51407813a48038000392606a2180c4c40d07402504400400800c01c4081d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 708663093 1250 708661843 708661859
    0x1f051b0a0906080a050103050604120306150c050d03180605040f0204110a02070f0501050412050c06070818090c030c030406091e031103030c031b071e050d030605060f09030a0606 78
    0x31a0b20408001c18001c03004600b8003e854058941a04e800070700510340c1d520b40d40c0d140c44c9400c06440e010010140e4612020607400b0030b5100f090071500c800d40e80c40072042040c1c28200c0c2010b8000b2903000a15140040903420143d00040c65001103820030800a915035403400c00240c081c000800c000d40c013901c0e02d0f200c8511007103403902502c4014081d81c21100340c0b94a42c8107a0f070104c0380034003a00d8007084050108010070b41165064001c0715102c0d00645841d01581c0c00815000e8000c00c0c011100202e022440c07076208800014031901000301140d541c0769a050804c034408040c440a4401c000c4100c1c0000020705210305504280e400f542d004054030201d8141c0700c405001c081c80f080c011800542c2000b4241c5000da00001542e0145411045a515503280c3c84c500b0300341d05403410f025890300c15050019001240b03d4040d00c103030004030a03400142404441c0f40c40d5040164110313041080c140b900d0340501041e101c1c0303015642c00704402e0246681c0c2d258544002483c104107403038018909800c0800c0030031181 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 708664343 1250 708663093 708663107
    0x9060501032a090f060806090a020117010513021b0a03091e0308030621120403030f0807020c0913061b020c0108040302030915070f050d09081f051b0a 66
    0x2030040d0031555a0982c030440b40c0095030000009560741400424040c07181c20b0360340c2d101c4003602c0d10031400014450358a45c2c1c802e04000c000c40749200f864100c5030a0f0ba081d0350300805184c2501103605ca1200040d8148000950821504031880c3c403482d038013040c40420114121001c030802c1d6001000c4481b001021b1a00424603100ca0180c81c141c04000101c00000d0107030150710302e05880d8000b002ea410742c1d40d110700707002043c03403a54904c0441c0c0030240031300e903080303a0b09208081c40e030100c91903603035500d50843c00d021700b02852600c20b00e010002c1d1007042001041d03010440180c01c0d0380c1150765818a4942e40c140c60b0a5101546024180c245492501c01094800e0740c129000000c1603020741d8841c0221400544100008450240c0940c008220000b25458820340401500c00307424078079410144140c884103400031701e00784111000da20002e418000325420011520050481c54010700c000404000603404242003030480450700c0d620707040032460304c042e05500300c0e03c021307003100030b140c0c8034900600c00400b40 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 708665593 1250 708664343 708664349
    0x507060e1e0d02030705030306060c07050a1806050901080c010c032007030b011409011203031103091b032409030c030f04030b0106091a03130b0916050306040c0618030609060501 78
    0x780c07003a1046110914004005d98140ea038010002e0360541d56000c01707200203940030b8004d00000c1d000701000132070f481d0345000b0410301420141e601c1c02180d8041c4000001210701940100c6d12134514400100200c44000910303130f209550a01c3c06034405c0c0200e140c00d48010074002402840b80074200702030348003003100051080489004203031902d03150f42d072485800301c07040c9200b503a40e07005001e010040c0091401ccc0e4803058641807092034001101701d43d225100c8065002640d4a034000c0e00401c80001920f00c0f0364200380a046000c40c0a091600c140541d0a003106103610100701c2c03071101040002d000d540007842176941c05540e01d01035039980c0c08140d00107810340c0c2c03003800101c5005c802030f8000700f816441151450251b41c40c1c0120380003180c00202c40c0503d203401c0141751030100000d010005001400d44400395000b9103081006102c0340201449882a181160300814000d40c800380803c00800c10202d42c10040b28654180004403485028019104804d84c2c1c001900ca0750408140f88104101a4059412 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 708666843 1250 708665593 708665653
    0xc0106031e0b0a0e07030311160b04030506181f0e060414060a05090c01080402040f060b030106110a0503220305031809070e15030601090e18150103120507060e 70
    0x24a80d030b1140c3c250102c1d00c6022920360542d0101c0401c1c0300007030080b4080d01d5403003141000c035a078401e0301034144000b0b80700c1e9402050751098085070030402c0107402c00c03003107811107440401010700c2c10302a0a003554070788001c840681e03a40581d2030980b4144013650310526100c0c00d4041540ca0501d840d00740b601d211242c01d5000324a501c1008001550300001d032180a0054400c130010701248a521001100c1d03000c00508140d034040e03915001020b9101c203611545000b0101e4107001600d941c03505a024000340700032569000b06802c589066000147c012080b5105020005000c41540c0184581a40020070307a4000505520000805081e220340d080c51aa540003001c85074080141d803003e404030341c01c01c0c0c3c007aa000d8200324000c0d00d9031343c0d440350340024681c0650b0601d0407070751517aaa104541c0080710255040d6030790369402120a001c4010900054074544805207a401d00765156076901010320b00240326510401c240840e210301003143ca034200a030350503140c10440c0c0032080d0440c0c9140d0501c0c007482203101 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 708668093 1250 708666843 708666863
    0x3030f090c090408040e0403050408060a0f050105010903020f0904050705030a0302061611100b040f020703050c010609021e03250807020c1207051504080f07061107030c030303020c0106031e 83
    0x80349000303010180f03e07a0b44541d0031401c2915081c0c3e90ba041d548050300440030f001c03040c000401e180804006031417086084010114070614007031070301002c9074410f03001a410032501290600c09a215411914207029060b80d92000d41d94403410f01c5410188544c1080b50315020308107041c000d040c3d0000d500d5014a00514000b420344090400542d20401d0020060b001c54021000f840401070590f44504071030315000d4000300b40320f180f03024120120380c400f081c2100807607030118548000e03a10034070405000c0c0200d6102145803c4980da5a840c9440b5441e06c0711000201c00000a5260005014400340300390b5000650040c1c1ca032480e20140c88440100c8030980140310381140c0892a1401c2c120405004800c4070141002a040c0414041d90002010f4260740901e0100000543c1c07441c200001800003501c038000d08040d0742004402484440c0d21440070495a004910070310200300814094011607034541401a9585030746000030303001d08900c1e440a480300d80d5103058030403071099003820441202d1180d00c03504 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 708669343 1250 708668093 708668113
    0xb01030605090a0e0c09010803040603050a0b01050f03040302030f0f0a030f2a020a02130c0f020a0305190c060f0203090f070323030706050106030f0f05060d080f04030503030f09 78
    0x101140d0251240350307404014080410300303180c040d038403d0205104180640d5100d051141c0403a20425082c1d1150099600000e17007001010f5052242ca40c200745516003d2140e00074100000b40b141c0619543e0a03500c100001c00328040600804c2103d4a8824221455448010341e50040c05c0030340054004001207414040355101d40c00c410300c40c00c1c4440c401e43c04040d0851510b1100e054483c8000da641c3c00c103520410411101585e0340f0760380100100d1102e500840c10200f10080140808003c01c0007000795070240d911440000e4004d0140d5280079502d0910350b00fa221b1096080720398082c0312001908092501c003d0000401680c9c00441c42000380e04d00310f42d0359100f05402243e0300d010307500c0081c2030b46030502080d8182070b060b4500710089002c04000c407401d0454603280c0f041194000e0340100c3c0441d036a02c60352100502e0758041c0c04030404842038200114644030020890404e145400244000780000c0c0c0f04081c50030303070030644020b150003808481c0c40349490041000300310002c0d956402c25118094207e = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 708670593 1250 708669343 708669347
    0x1606030f0c0c081c0513030207050102190308131a1f0302061903090b0a0509070506180d080417061f030c12210c02010f020706020c0f150417010b01 65
    0x160707003100550340701d012100c001e8a848450341c00c04c402010358007121020100d15064217024440c0541d0403000f80d140c20b0340d507034540a03103840c00c1580a00d065401c514000c004980c031a0103040c6e801905400c1100107980c0b003102843c0e1440d0142002416203081c1281c00c1803000044c5101d600c14010265002801520310350b0340707041c801c6141700c029801038081104004070059010081904811749c1404a080f01c03240d07075a82200134003102e0358094035960790104074443e03108000c208014202603924602e042d203071600c030740c2810b0031008581380642820310f942000c11007a1000c543c0285041c40c40c404080030440d00311a15220192030b0020318200001c001c101d2049403003c14012298001d090104692404d0002c00e1320105080c000c0d2403e0380350090b44c0c21680d07152003004912426660300e00300c14210910001d001c48104544c070b00115400340805100741130f0002041c03503504a00f11640c0030b46210440000e0007a00701c00c00031000e08000420000340900081d80310b0052580346e040284100da40358001 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 708671843 1250 708670593 708670601
    0xe010e2a01230a1407083a0e07120b100e060109090513061d07170c0d2f032a0f03030c010f02030105030f16060e040902040c08220507091d1606030f 65
    0x7c8108900340481580005002d40d20002a805c3d1002c192500140d80d00380c01820700c0e910240071f48000300c100b030400400e41000c140141c050700a00f682c0c04e28078101100002d010492034001d18640d55603c030080703401c2e0140c9524032000c00c2e6101105010a0b8002d8036482c08000f040300340c03011503100b9140f000c02d880001040e035288194a400080034001e02d60300412558611840d825901d0440480c4001c00c3c10201102d03529404c0c008001c0151484c88203003d052805000001000c048180000180c003140301203010480d0b803010445110000720b80010000741184035051a001c52907280c800018481206500954104c5070100e069030010150f00c00c141d902d442105604110807050301c60144a1640a091a0f520b00ca01c041c000242d8000d032a40407070202c900c048141030106a81000300304c0794005c13109080c2d48039010a110304034045095a2120342c0c404c0390f40641c174040e60702c520010702a0324804c0c003503c0d084080201100c0d0348405103140e001c000da1250244030300290400c4c900c0d0300700000b1402 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 708673093 1250 708671843 708671917
    0x40e0102130605041820131511100218031504050c0a06051c0b0909150a06030b04150e120d050a050115030e010e2a01230a140708 57
    0x17040d01d04009550a01c100038100704c62002100840e501e200a003200780d80000c0d24060400008040c0020b04003441c44010015440c0110100100c40ea1504400540070030300c00440c245040000d600c9031a01006591000c4c2c15215542e01031142d4201c015040034502070042c09070b0b00681c02d641d2800c407800709000c2c0040d1980510004a035040180a142e42c040038810300000b254204001307162418403001480c2e001e415503588205030b102900310b40c080380130f03002102d80013209400300300b00c1140f459880c0300581d400200080c010303841c6121080c0480c815908006180750f01102030b80c406800048144140d44c00c00a000d64a003850000010207987c014410b4a040e02c0307607405422400304074001c086000e0003500c0041c00c00c40d501d806001c02c1b0b0860800244002071f01c0b030354442c0e15070078007861855214412010a64100000b2074500d410b00011005030203101c0c404802c0ca9541c9850134a0140d0322403005254500c8410740c0080c0d15418442e03000007900041500c2c12007401010b40d01a014070300304c1e1a4013 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 708674343 1250 708673093 708673109
    0x70f02042301150909060306020309010e010c09060302031306020c0714040b010e06091801120317010501051b12030c0c0c0909060106051305040603061506050f09130b040e010213060504 81
    0x140140802c103480c3d0541d1032403540925000041c203480c4c2a00c1030035151075070300858606401005100d2000800e00402402c0041a0020416404600d070001c140b02c07401c0c030038038041c582e00001145200c02c460651920309500454151742c0e920300117881c19610006842000c40c070808500301c1030061300e010300502030140c005950f4000001149410030010f82e0140c0c064a621000b00c1c0a40d042c040c0e2084020f50090428000715001c0450f41c1c20701034211000c0d1005d111034501100d005126980e08001030340c107086440461350220140745034816280121889102e03c0345513011082000405a2000901101e2007200903a0418100c08092205810080c0d4040760107800c00f01c0107008403445100903048261440d142207040c944c1e6540400c0c11a92140c200782c0d94180c540f61070000c041028a1000000c042031701d040c0b45840c00e41074070030a850080c100d0161181c0031303082c044c070342d07041c40340e0010011264010410000c400d86d10140074000d502542c1103400e144002000092400e0181041c0d4088a81e0702d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 708675593 1250 708674343 708674411
    0xb280903020c011205160e01170405070807060302040b0d0c0215040c0906080c01080105040509031e0a03060b0c070b07020f031f0c0516060917040609080709020304031b051002070f0204 81
    0x426a150007c420750141004103a40c07003190088070800303925000360f0141c1c018125590504020f01d0030040c164209206041c0100020080394220008070b9031005d1119000080030000030b04200e05001c0c41d004682241542070302804107206400001508860003004100401035555000c0d645a0030501141804161150300402c02400d0030741000764450240c41c03d40e442e10784d221100910900c074010988041c10b1020410001d000e03014840c030301c0640801071029050803942c8920b20b41c1c0b29840c0c020150070600100d144400c640742c542007013400b044000c2c181c41c4c440c0b1030113030f10501c8a08064505904d15040540e03020380d59000c2e000325954204c04108034404080180c8458000c2c2c80900f1084a120701d08241d0012640b0f030010180014150640d10300030010700e811076240c6403801c05d4100140712403040081c40000313a04695446000c042d10504589600c41c0d50402d281400100390b00c000c00e1900014418040208103000c140540b4421141082400c02e4221301c281e60504002e00c1a03c24055 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 708676843 1250 708675593 708675631
    0x3010906300b061504080319021911010315060201020901180b0f130504090b040b0604110a030507030617071d13021207030501360b280903020c011205 66
    0x2c68041e0f2008015110441510a0328146407950340709900003a60ba800110b2403625148002984803000c2d0340910060280303a0b0703005a0402108410305005281041c5c52000c07140d030703034040c0c0c214042502d8044082d111169039282c01a020303610080f212030002d03c2c1c2c120b09a800d040c92440f620309541540c0c90300c50400789000030484890b403003460b2182100039144400106507a95020b00c405161203a90360380e6503410285045400d500c2c001c2c0030303984183c0c20a54044c1c101180c900a940134024145000f0030146c807aa07100750014101504264801c080c0c0260340d0710b17140c00c0050b02d01e04482d5641402c0055411412503000750f000b095540c10018580c1c0c89410000d1f00c0d20041c0c9800556200d4159144907649070b840c0740c00c40e200410011407150341c40c0400941041034050000b100c0e00c81d000503900d01d1010390f45003a0030340e10041000c10000b100984900e94201b640540c4c000141c04035030104105010303428060b40c0ea01c40c070415503000a9004401241c40c1e440750149a01a112091601404040d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 708678093 1250 708676843 708676853
    0x50405060f0405030102210c07050319110715021005010b04050d1509061509090b27060916171f0906050a06030204230a110c030301090630 61
    0x1c086001c0c00030040d014800498165800c2c80104180000100c0b00403818042c1c022000740c0c2c0d08001e0a00c00345001c1803002001286d40401218190781d400c1c4101c2171060416a0291500e5051210740202d902c60310788046200c5032000c03d880b0450307019400310780d240304c003105e202419100c0901400b01010420702c0100800e003411420711f200c0c84d02c180303240c41000e240300348070a0484102310b4068a09988034005440748500780c4420201504103240c0034010a0402c0c1c451050303090014011032500c84184a20141e075000c40e03a00b0920382c44081d0242c640381c2c146020091b54518100b036005103079074050000040e440c6003c09500c450003250078040e001c9000001d039031180c1c06880301201445162244402400a100381c810203100e243e8030803000a4003070450050100710b0340c091401000200360200003080c068500820664001403685010407a80d0b001e1810050078058061001c88921012001181c130000c140c118030155042c2c040c100f400301064142d0400703a400d41c0381640c20904054001c003000300d5 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 708679343 1250 708678093 708678097
    0x801180f0f0303060e070c0201120603050613050309040c17070905010801061d1f1106191805030a0c1716080d060b16020301052d040609060527060705040506 69
    0x3400b030b00b40000e4095599914440d081421925800001c81440381802150303001551000507001c075a40421070342e03046541d82c076039464018050581141038140b071141000420002c03100b24040240c0240550203010300043d040c500150800111810b41030001400248a924440101e4a0503511803680b03900c0e003142583c000c60348803024034031202d4020f00c90140361144282100c04503408003010004e130368603020051100201d1906400307260400800e10035100007541a110010581090000d848c12066034041200c03100094001c06d140008610b4141d42d0343c0005000c54414066800e5440c0c3c01c0800320090424810450840c0f886901151030b800880c0c01c2d000a0107201087c51700008009031183c0203610180c00c0b668035591052040312680b000c50500303005150b044030030f021405c21440104041c000792101001500e131005941ca000040030700150f0b401c204e0902d40c228004220714200321a61200341d01c6c1100201a00407100d00d0340f885c0c0014001081486001d4039a51035090508100c02c005080d = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 708680593 1250 708679343 708679373
    0x4020d1209150509130614120109020a09020c0d030203070507061a030a05010e0c0f060409020a09030c0e071b0210030e0a0206040f05010f050a0503060607060e030a090801180f 77
    0x2040580011909000c2d0030240034025905442e0329481d080310104004159201182000d003080c180b01d0208607034204844022000f0030100c81309600401035110f45401003000040c042d600542d2480c1c00030301d541d10f660040580040060580340001031201c0140d0a91005845000002d00c08000120100b10140d2246a0305c00c1f2400c0032029845000001900d00842c42d41d060700d00f41d42d110100002c41c202041020031203042510411040c2c0c0c1d85000144542c0201d2140c240103640000303588110b0340c422102880074690001d0000180c0d40c5840e0130300c4451900300d880c0c41c0420911404030703015030561543e0160282d07005042c4610f1100c280011005000c0c0b15003140c0d00c900c2a480004016078524014201400c1c44100da052518945400100b21040c2c0c0000d0a090090400400000300d0b800703003c5a5020700140c60b42c0750780d01d0440c030f8444010894041c804d455400081051021264402d511008440002000b801514076128001a00c1d4005190040c4000e210f40c0007940000c82c41107840d513079 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 708681843 1250 708680593 708680597
    0x30302162304090609030e03070503280c17031201060302030c03130c090f0b1c08070303110d0c020109030801061407060527150708010e0c1602100c150504020d12 71
    0x80c4000b144e42c0c280070740f11502d80480205101401d104040d00701001100001c0c03004030010301c0c8410340106840d112036038049181d41c510440781e00d05414030075140e41c04801050b04180022202c00119241601c9401c1544040701d0300c2c80c0200001420b078070a00980340a041e00420303852441d100c5205010880c02000022034461020100004041110784506200c2c1100d60300c0c0441c50750080c1d01040002c1c101994003a491351145a000030120303284109946005601d400d000030095281240724400303008102c4030784071050405501194041d8103404c00c1d0303c814402e80700c1600503604c1e0f4030309a03071a040408051828200502c04540803510700d802258210707070030040c641a0079083c0b13011992446205d0704507481c80d520840c4074406100405503600e40c44801c501e45107440d5410160346060241000c2d1181121034008030380c0b25003c0c005c0304120701e00d1980c02000740341c1140131a2005408003c0302c010944000b07007940e4120007001041d0192a203d00d44c0141051803401d52550b641c1c45200760814440f003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 708683093 1250 708681843 708681851
    0x2011515020f2a1c02271003030e010212190c14010b0102072106090318090b010909090c12080d0f02190e031c050c010f06030302162304 60
    0x1842000e00c040c1e620343d8041103004086203003a0540c00400c545082416000d102441042d10200e8411402030900039412035585518844a10340d0007016200445007190010074101800189034000110904880c4640c5651441c9001d6200581e00e80448800f1505e04440421841008103440c44104040303120746d003403d00d40045c0303d88415102080c85c6e0704105290795141d54594030783d80c0400c01c240007000035510b05904c64002c045406002c1d104c03103000801c404e4039501828200341c040d035060200004a090711484407641d42c00c10728041c14035880d5041c0480d40e00341e0301045184030780c019807032116004070310002c507075291400201c11641c00150964800d803045c051042450114083c074181042401005616410000c040c19a403400c050200700c00c0c00145004420344e514082108000c0003c03205021300f2000711808151103521400c24050b160354a041c13680c6507104015840482a24000d60864021040c8003618044182403406000300314080c0c1d2458130541c0792082d0b00213010307540142c0045 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 708684343 1250 708683093 708683113
    0x1e0c020112020c060c131a070b190504050c010305070c05150a06080d030203070212030124120903180801060f0e070c06180605060f130203060d0f0f060c0201151502 72
    0x9814501d0030749100381040000106903042d14546c2c845007002d03051100c1e500e50300a2950444640e0f9101c0c0302c0005141b500c6090009000a4010060180441034020240980d00d0306140440c0c6594003410301d49d004c24901000310701068440c100f0f02d00c800394040001c1014514070351203500020750003040401c16541720340b40400c0c0058103101c8507140c2e05a58501584234144448064242042003c1c0c1010741603081c401001035641090841c03403002100c08500544c00c0203444202d0303404c0240c00105c2000c508058448040541c0b06141c80300d0f520108500c25000e946407071109081c0c400b00d2290300c4203014640401d00c200340307440d2540c0d60000c51a00300b44168019070f680309411340d401107000c25039121300046d418042c00118056194010000c03110303098030007070031000039058880302c0d81500703074459000c0001080b903186c005d0441d050581000c049001101c05d4640b0f6505800040d2046500d1810000c004001c04d005008411024088e0800308002604140c00382a0841d80c05442004505c80c0740c1d050 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 708685593 1250 708684343 708684367
    0x40504140f0d14071e060f0e0c010909020a082403070609090b150d1104170a031205090c0f0d0b0108010b03010b030a080a050313060218011e0c02011202 67
    0x8900911501c006031441041e21500a840b030400d011610443d480c0800c4a080064800010310011040b541c8500c01e0780c2e4144d05000009110014070125124030342949140c211800290001d6946001d90b1010141c1d034441080205038083e0006c9030340450100d1000c503444a04010032640c3d09101484c1c602c12500780000000d00d400b40642c80760020480c950010300c040c1d01e0a0044405202e026104004504403030180c00e100c43c07141000d070141c50342d40e170501000743d030b10300b003044a00a06030700034940300394601b000c400b5448840504080780881d084030840842e82d00b05020f00ea100702111009801201c158406000381002002501036208045107040400a66603066407070103031134040c000041980c0d80e2402e0500312003110a1103846580440c014400165100742110b0102c0c100345030150b1039407200b01062410108a00d4000d201c18004965100165070040d028803080509a9134840c03103094030031480d404c11542000c2075001800c40c40083c0d000d5401003201c0300c25490001801481c000d143c00c00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 708686843 1250 708685593 708685603
    0xc04200a05120a1d030901021b060c0102211803030403030c0509060304050d024303050601060c0201090e010e04120504051905040c020c030304060315050411070b0702061504050414 79
    0x4242c10a90344c40c0a0150082002078040c415641031600179442d01381c0c0c05001030340e00e80b000c51030206801d9450141041c0c0d501e400d000d8070342c600302c038000941d1600240281c0c50001c3c2c14801e40548075000000000b4043c8c070075805848140c01865000c2c600d1625540c074100c0c06014a02c1002080c80000c2005505035140e0f00001d520582c005d401401c04500d081c0002400c15142d0400341c55a03090240c504030a840641070b01401c00100407032001c42111410038114200d90700350340082d2440c002c0e41c1c0002146a0062510a440c034800d98070400d00ca42c80b8504030b51101e00c28006d034503012f4180c00000e0002811422040c5440d812810100c0c02c29995100203007418402000810810408010410140c142405400400c050b00e0015000c0e550440010a98a0240f031081404068603200000d0200d00e160b18200d000e090058010701950100c00504a1b0301c0d8400c00e021117200202c200080c903180c1c40421164050780c5955144140c040340c0e44104130141c10058015109550010450480c0c0042045 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 708688093 1250 708686843 708686851
    0xa061205010e0c030c0a091a0d03120507050f0a0e0a1e05121c05030a110f071a0f150a0e0126070506030c0304030e120705030c04200a0512 61
    0x3042d50748594110900f00700702000d009000e0b500050443c0c9031a0307100c55400381a00c4102100064100103410704100e9815090f2010340c20600b40d280350428558800c6030f03032a072218600000d020a84900c04102d8241c812801d20b05810417050080155140c031501c1c2c0c5159080c2c0060010300d1302600c8013807101c034200304000240f5005880035800c214900301003210290254007800a801e1200013604100c01c0314000030210303420003000000046400c0c4840e402401c2c5980c4100100791a5018900710701c8842e40951415611101189050150070b00c1481089104000c0341300e0701d45840c0ca40685080303e1102d00480e150340715045d60008034003d20f170072070030a00138107821103413080303124000003020442d8009200d079004075000301c0402e0000791206022030340c202255404060740c9942d0f600f412500703111091406980078010b0b010015020303c0c00600e00c0c094070401c5095504042000e005c10045600d0071101210f1b890102c00d08004201c0c501d0040c0100d5100307403e0151800e680700d869140d00f00b404032 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 708689343 1250 708688093 708688103
    0xb03130219080c0d0507030b070216080a1109070f08070203070230030f03071209060c020703060e1506040207110a03060e0c09012d270c090f030602030a0612 69
    0x80010000640100101d0029200550301c0700c68115984d02c40d46d4440c3c034640800303449900d120000c611854404c04c0755a403c0800703440c20b500160348500c91070fa11800c15210075512a818500091074034034040b50303c1c90003090145c440300410245d5102c155a51180103056609601040c81340c00e000da00e4020001e203201c583d50301d1494280211808041441e800c80c1000740701c0d8ac0c0140460750480e1280c0c1c013102c6d0040c449060080030b45420001300406040030030001080d943c24420202a844d400007085800d40b403042105210b9075180041c040d40c0d420347e003400c3c09059250300d80030a03c40c2c1070079070041c44a180507024030311500540c0004920301240c03580c82114280e07942c84803581c84a000b4000440d40c2070045030065500d500d440f81e25010b9100f50400340051641350512542c800003400c1050004003172441c151580801490440c8522003001d1541c42c0c0c3d6141009048081244034241040603100d49000f1462168159100e0034001d40005089954407175895002040603468100401c81003071150b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 708690593 1250 708689343 708689389
    0x6051b09060a27030b011806080604060b060f040b1905090d1b03051219020307020901050906130f090615050913050c0a180e060105060301150905100207060908030c070b031302 77
    0x3c030105511a1052845591800b07280c010140a0f2751400705465170001e4200c440401c07220310040014040f4443c481044004210029000405004c118064811031140c00c11406050880d0744040d00c60313105844110340c0c0000000b00e60000034221207856050013171104041a0240c0d16036955501d040c00142031807000c0b60700421004c5820782c6010150104986074800341d4140f0019601054070003c060244a01c550440400540f00b603c44400d010500c0c0450724051180c0c080c8281070074018042850162541c60410313840c0f4800140107a0008100c40025100706c1550b621107511242c050900b5070203c03068000c0c1d1000400740e58840ea041c102901ca106d02c4420041ca4140c1c0e00c0088401c01d003201c03095038100c000108103136a0b811080c3c9044904411070022207805c020000c580d9039660380c01113517014014180058040794002408815503045864803128952644c80b51a074a00544410784810713400558284040180600590b03000313045604110300c2c61807194002052030035118030441c0c0700300380 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 708691843 1250 708690593 708690599
    0x2210312040c0e0c07080306010f11010501090c1d0d0219080d0207180c0905040c05040e040b0604060e04110f010903081b010b0103020703020a170f0706051b09060a27030b01 76
    0xc5000304541003103104c1102d62402805544124550000030203841c140812081d400d100b0310b024980f00c80807440c140008111795a190076102d801010360090220003d1010191811400d01304492020b10034001450040803107103950030000c03020781042c80006500f00d020360004122104000407500c40b10550050f258860800406100c641e4005009403202030400e500c4190042d0420300b04002c1d10801d807004a016003071410705451600c0780d68800400161400200310500c80036410040c010070044800340f000382c0e40d07981313104034800065801a007402403c002500091500403420000e100c0d040c14103401195507615120111742142d0600c9019413603032560b2290b55170080c8100c02c0c150b1024242103003030541c01d0300d000755111032a04009041022000007500400207400030b48185582501d084d566944079440e00c9000342c00282e07204801c4003410110342c0f9854410b68117450300105c000c4c0109007440c91004c0f040344c1d00308180c1d6017202c003100c864180b100805c15401004000d940900c0e08c490032545 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 708693093 1250 708691843 708691859
    0x905040206090307150813020108040b09160906030c0e04080d02030a060b04091b081b0f0f0f1c05042111032a070b0406110c1f0305060103060302210312040c 69
    0x40c001f0010b528480b644049040140e822054594106400100454155a50505031440d00c0c0390a041036040c1d103104000007801c4401c1e90005400e49200300c45ca180c03201d60b07079040043c80c0c0300107480040c003002c014801c50001d405640e0143d58003514200c00803401c0341d601c040300348083c0c2c007640100200a4440d20444e12850903c0000e000784207180c40c100038a464010f25016000f42406421441d4283c002050712001d42004207039041d141c0d000460f59a555031400201600d6800303045101d00c60700103902c9000980609101c0d003442240c1200761940e580c6902031078081c0300000075081005120309034614422071141000070b080740718140000c21942d581101e48c1d00e030300c080c0f001c0e075440442c1d44951300500051041c041a201200c0325130421103030034851500030908001900e403185e42c02201940c001043c10071b1100080100e00d803551000c000380d4032580011000e5461130301001e5001035000301da02c0000c00101080c148803844401c04d490804140c9500d02d41084030a60301540e110b022a4400e0007590 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 708694343 1250 708693093 708693107
    0x81905180306040803010b0f04090e03040510090e070e060c06010306050132060901020a12021f180201080901020403080c070f060206090a020f0604050603070f0210060807090504020609030715 84
    0x610304900500882ca029560703080c4a03c014054850344a00118004502c80207007002da50181c00c10300030510200c0e43c101c00c0e4903902d80142c440c0314426113001d10301141e141e010343c6000d016200b0398510808543c1e507100007603d044015003a002d8006804000700c00007945c0070300c0b840c1c2c040d52080300042100c2d4034010700001c0c250860510001c2c040d075550080004850010401d110b007803001c0e100c803a119203c80700140d0820002110140c00d18090b80705200d4080c1c0d000c20f640d80c540d1036000091030b814100b1610b4004035410304c1c4954082c00903030b242020156014a041d00c2d8010f40200001d0302d82500c03980e0f0f54205401c800811080e6a0001b0414440301c100b24042c0c40203401288000d040b00d2401110642e620100086c0107406030001d06000c05e40b07515400100c2d80501000b0704201e55078180400010400086203840b0001405404410f1b000050140100c108031a06d00c4020440c580c208440707840108405881264082401c100d800c046480a110060040c22407050001c0c0f400c1c2c5040004c3c0450f = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 708695593 1250 708694343 708694387
    0x506090105040212030a0c141915050106110c0411040b040b0705060915010918020607211e1d180f010e040c0b18120109151116081905 59
    0x4d074100703200f40780071a6400a20035843c40c0e00001c9907d00e0f01700d880225401c1c07083da040c084001001d8040c01606202036035014111034141d080c1d0403c026a610001102c12048184480140d81c0140103200c0300c4d4542508203403c010a00600756141503595040421554403580c40711041070004114402070003014441c03180d0041c80303400070300030008071241d60050f8550140100300d481581e903030040403807903000251140b0060f8003810041c0c1d200d81c0c5043c802c003190b076101c10b10038200001500800e4014030442702d0803000207035801301100e02000c07501c096840405401766141c5014200030860760ba0ba803045001241c0c00301d0800400018100380c030305003c10f9a01604070b0082c070400d690900c400100038008160445600140243d101d00d0940600318408600c015519444142d00e03120142c03001040d84020300803440b802d4000c1e80e411005103030800380c546c0714651042c032a006101d5003108c1c0c6241200c449643d44508001c501e001034600840880d414601c40e150001070001c02d4086103211048056011 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 708696843 1250 708695593 708695629
    0x10902040506030c0c0f100b040b04110306120a082b0203010609030209091e031b0c0a0603050601020f010603050d110a0f1b0308040e0a1409121605060901050402 71
    0x340c241800301040c92440003810f80040603000080110b92203c007800120115104501078078014003001042c4006002c0e040b0704144101d103481000e10040c500f602c580060303400340c1c05565040d5952801080900e0307815000108060181039484000110a01c0003000d40300d503101c1d0401d0322000c1030215903c0e009144204086c09174410401407140b0341d0041600c60840e0b40c12a45804103a42d1400d140d801d101c1a0700614404802d400715080440c1008000791181d00d014a07818203448500100c1d840c5d440115150040e0451403000041c0522446500320039804803043c0122a40703144c040361418219a51a40f0a40d09500011000b12000e48d00c048408900000100205081402d030389444039801e14909000f019010050100a04000f13000080c9009580190199444603130b1403c010208460460300b0000c6140f034191350b8004412075005c064011000440101405024446107a02551000b04480110714880c11142c0004104200c60740c403c2d200c410012409041502c1030044210004168500d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 708698093 1250 708696843 708696847
    0x50f0319140403080d060801020316120c120908040e150418120f0905060705060f010e01031e110418050d030203070e010e1201090b01060e0a05220b1f08010902 70
    0xc05035081a41c00f503903001800d0b10f58903400d144055000b0581540b00e8602d55001004012281610701205502840036484a804009500301c40c54119040d0000b441d010508041c1480d03640e201651190b134199115002280c9001d03101c8001000c180821505280e0500005030714284609007401651591405e64940d125205001c0e51901c81c074050102006003080742c00c0c1031205500d44111020801030034013403c0780d039603500281062038032420202d81c0c001c08985d61000000310300105400e00350481c0d17003001d146407080410010342140187c1c240700a541091900400d01d08aa456111f400b00c00c10400402c110101c1781850050309181d10050040f050610500800c040143c20444190034824246440d425900c002c00c001148441071a80701403541d80f1f030800d00801c011120b1046c1c0e069642c1030302c58000c50840c0408200c0020301500400d5000342c00b401da00c1e16400b0059071045200c540105c40400c071043c441010400b40700c42c44402c0032100070301c501c807003820325001918503003d00107400c8194 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 708699343 1250 708698093 708698117
    0x1d1605040b0d0b01090314250501142b020315010309030207090b1f030501050909010c020709020708070605090606040b0d170703020f070b1306030b01020601030201050d09050f0319 79
    0x501900071800415070041c0c50f41045040703603110303240550240d9800422142a000f0002c0502e0340e614459180703a084d140d0514042d403226414142810440340b050351610034445850005000e20303000920145081d1807011403c108a01c038500084804481400c00140c5a04d042078601d0041c4080080b0a0b0505281800e50000b1076808621390050300c441140206a4040e07550200380d008032482e03c80000c500c03c0d40041000a54180c1219048031000c03540704a480d01c031051611300300d4480100d9040540d2200404000c40700c40340e0040e048160080001c40e00304881e40d1200c0e01030b41c0b800c8403c0c00306908000108007041c40d107403040c80c0c0c501c001035640d102d5450160380e03031092089015186040260300800c0701d0003054803c008400c00c04543c601500c10841c3e940182410311b4002c2d249102c1d15502040d03021808034800e1085a510100580c01000103900e181c00544240e403010304240300da03c0d215026480414001c22401074415500c2d0700450b5182c0c804a2140801a81a2030207c1005800c04c040 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 708700593 1250 708699343 708699359
    0x170c0d051e0c03091009080c0c0303120f070c050307051c0e0607060509030708042301050a0e01140d020f070c0b03010807150507020405090c01030f0b1e04061d160504 73
    0x1041d8806901c002c01c1c0c1d6651036445226103040300400e201041941046485000c00003110068402a50140211000c0540c0d141c2055260301800440d200c0d03030704548001030720b00c20b030100d03103076401100300d04107804e0821882d02c0c0c15055030f20805068840b5485000d0000c09000040901c907220203a0b483e00280120910340090b0345407141a501807c1e0315181c4c00482c13030b111801e104a400c01a400000e60707965a80e00c103110f884032540c41c100e2040803015000c01e0303032265002c1d50845001c0311082d5920910102a0b0006403142c0d80241e008030280c900a0104402c6199244024017640f40300428041e1641d5007403811000d45602d542005405203402d1004111b84480006c90310f054a8410000c100c082c24102c000300c0b1039004031680030750b00c5820002801116880031421700701c1002d00b030340e00f800899200802c40080e15000c5169030740080034100c0040b0038914038110b1003103a281c010b1010404954440c00c907980c580d81401403040682149080c0041042048401c61001009041650a0910702444 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 708701843 1250 708700593 708700651
    0x50f01080a0f020d4409010e032404110906011b140105010609080c0301021813021e18030703020108070c030c1b05100306060206240a080d030e0105010506031303170c0d05 75
    0x406c0d0600440b10340803200ca64061194460031050340440d0352440001202c0903920351002e43d0251400215074080c180141041d02581d4803c01c010784131050011684408200c1c2040c965030103888480315507040f1200c0500a014050003040c4559803c000c0e241031845045c108408129a244242c0c81000306140308400c019032516003040c1100c2c04017092504580c900064070441c090101d14110101c0c040c01010b0200014004070b08211307800c04101400769082c075640b143d15000290100d00c601c0000313690740c0e202c1c108001b481c0d4420b00c5e020303c042e183c1da03686480204001c00c2501d00c0b044038420520907800c0c07144070100e81d42641d18043c01000d160605c060344500c000b41a0103810360b460a1041060a41c000c0e103110180307400f23402d40fa8100e035070f02c41c065203440801c0d688400180c1003200c481010300c814000e00d170507a80d009218501e982c4a01c00020162040b8003021000c0c009260010428000e901020030302c034841c3c2d641d0703150f0b94400300d105140480e40d00402400200010315040d20b41c2200e4411 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 708703093 1250 708701843 708701857
    0x30d09120e0d0b010b1c020a12060b07050c0405151e030f070e01060e0a120605010f05060703050f0a090e1018051311010509060d0b04050f01080a0f020d44 68
    0xd04d0903968146c007241d01010842000f6030220141c000180100030f0750340329031900c0d2101c80500b42000610340350ba000708400d10070000094016442400c1180481c502640455004600c002e140201d120ba4400401d0181101000303120402c1071818075400070f82024400401c54690000250101a0034981c030300c040b40006004281c20050101c8600055407070b01c1201c2c01c00381c842410303503035082e03410380c600003000e0802405042040048182c002030207080200945542e146d142d101c842c2459200e20740c458903070b00f02002d41c10810199103c00964014046005400f8007602055032000c1810802c2710320024101c411184078062402080102c04406c0c030110041c4150b1003c100d20400f01c84a004a038a802001001948008001904040e0040c564045d08000105035801e101580e02c1e05146110780b58248541c088507000b9030f034000002070314402c8200069100410099415000b929090300411003003009205401101103035407030b900503203440c000240c008218500c40364540340e004a41a80501a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 708704343 1250 708703093 708703109
    0x20703112413050102030f180a0504020c0a12020303010609060e0a0e010f0614070c050d0602160b060f040606020c011112030403052206080612030d09120e0d0b01 71
    0x894200c54035528407428200455161420014090030312010550540c0320031001e801c00b8965803000900365001200341c03032002131510b4809007024100c00e021011543c0d1991035a51014101d480850255074900c054420820144000e040450391840c10500c142400c6002e0303829903206000400056074041d0030482503441c02e162030811101103001242c0100e00f01e40001c440400108004034006900001c07020489126950740303121f085680b40c0442c41c610904030042d100003968001484641080058002e02620550340145400451030a0320540f00084400b100c501d0800f006104207841c01800c00040d01c03004450030005640360900c00b0350380f48004014135041c07000b0641c90055029007404030703582c10b107000102540c0c0c916040c40c000349154004404480000444135000d040680041041416a40c8540b43c61806413500c00411900c0105030b80c5559071440100480c1403440414040e9084c1030f07104000c03070452007004040103084d403941c0c01006030280c00d030900c1c2c448c0400c0c1207100c540e04603003440f = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 708705593 1250 708704343 708704363
    0x603070e030a0609110a060314010501050318030c0a060608010e150c070c030b040210110303221a0f06060906030c070c0e1603050a0b0f130b0411040f060f020703 71
    0x1003010a0614180c018007400681c41c0c4484142401800c034040f41488070304503101240320f0b44801d8240c0480c1c1c0c40c698416880d0000700018001c55020f40c0007150841c40d14010300c0000b81100900c285158032400413001981c1000e11a1320821540f0f010f240d01520340c0e00005e200d6001c0c180c0c5080d030b4443c10858241c42800d101130100381c055407000d08489486803c81240302d001d0340c40b804d0a0120b44802e0300c04038040c0e0300c81d0001c0c2e1003032441103110003403594030000514516151402d44000180d1444070701d0070b8002c401a12840001c41d40091031603400d8504141d00b0311460f011403d08131030440146024018101000341070115915541141d40c4400503280954035a2001e0502d004030785040e4102007012810314092000303601d1401d5803001d4112041d0b8003400179030350f8580c015007914101004140c1000440760f000c01d85107005584a4491040901e0011f8000d4450300002c0c266075414a088440fa480090140301c0707174043c058428041c15603070038055004002580c000350748030304070310004c3c0c01d540308 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 708706843 1250 708705593 708705617
    0x12070f0b18010903030902130c0903030e1f11070e150111070914091c0e130b0a0617010b0a050933180f0a150e100c051b060307 56
    0x102070051000407801c0003005401c2032458090020440d03440140e12130811300c50300c0403010707020b0300031118140c11580d140c0c191039140d0750f000da07680d200d02402203030b00a125800219210856807801310722642c01e0340c1c5401e81810003a08040c10402d9641001000e20700c1017040118402a038000c1e44100700003031030700050724503240034118100320460308681009801d0910004c0032004903030089000f1041c01c000c3c1c800d0650350900c61203212000b14040d03408141c42c8040845a0320704060100d0a140d0307128008504036040b0381c00543c04440640212010510031086519104c031054410790250620629151a1200034140909a0b010300e0226902c02e1884024981c0c41d80043e22a5440c0d10030308151800c050b4880d01c18090304d50f040510301c80e218041e01ca07205007581c03a0446d4140d071030b07a4028100d0740f0030b1801c10041c2a208500b1042e4a000e110300300b402c0806540f0f8080c174442100303005940381c02000d0031078585542010010500d0101d0b201c031002c408103443d6103202c1102d800a415080071152001 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 708708093 1250 708706843 708706861
    0x22805010e12010e0601031e020f090910110a090b030606070f031106040c15081b0c0a0b2a0a020705010e04090b1005040e030f0d0504020105090316050312070f0b 71
    0x454061010b0b141e50030300b0550114420001080341c1aa44244a9580b80740c9100041403030700000c00030080e5015042c0701802d80182000100303160414180001d4510011a1548030301c151030344107000e0f242d01900094a42c1c0341070340c010700d912b0283c403801c1c0720f040c0f960400c47c0c0013900d507009242000d4060004603030000100360041030000441000e5030b017690030780e1a1608100888408603c00c0d4940d4011100100e0046440f031140e036441140c0508440f0620450700ea602006a003180c031000d0359911400c1240000b1070070300c18519100c1e620303904640c01c1a42c40094011415051040c00400035a401c0c051085034a80206005003501c000f881c2a00712a1404030000e030250600710070190030020440240004904040300d40c0b420380360251f806000300481c00201987d2445643d4403185982d0040c4000501041c154000da504217005140060429201c1c00000381449200305054400400484003004117080a1100c80e810441c00380006042103070603112504030858240300103240074212400548408 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 708709343 1250 708708093 708708109
    0xe0f030f0d0203180a08100b120304030506160306030209161709010c090806060d0215040302030f0304080f0c01080703020c01060906080f280206030a020c1603022805010e 75
    0x50204507000010480d40107900d079480030340c40c10200004101c41114074103089089004483e143c500810303546817840304c000d0003000b42c05031043d4000c20628001003c810308001030f101070f5000d440900b58074240baa08030315041c00045c4a0310103040c01c040042025960b0400c1150784126103016034000b030001d0b000308844071008040410380c103001a8050021880055004010143c100d17150044140d0301c40015a54540c4101c80150340208031101110041c1803107103481000c2da0401d440c00d801c1980340d0b40020b0800c050034110821561011808110442c0704000300c01d03a101502006d0041c2560000008140101c006d10280905400045101c203200096001c3c000402d00c141c42005842e48601503292145064030050796580b14020b02d280c800c00200c0180031726000150586254a0010381c01e020700c5800007805d00300200d034280180515100184141417408124640323800c0454110f00c1000b81d05155200d0329014265142504900c26551030680015514242000c010401072440018118 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 708710593 1250 708709343 708709363
    0x40c0504050f010905090601080705011101021309200304030f030b1f030f0c02010218040b0307030c030c06030f0c301a0109050d03080109020901050f0a020601240e0f03 74
    0x80c500010082c1d0b10a090303900314140c80b8051001c2c00503803580040541e0b40c10702030144800907080142c0801c50740d0301800215260303801850000d41030078060078201c030f5001c0c0c0729486848141c1d240c00154100c1c01d100c150402600386241045411802e06890003002200341d0040b20060660f0b4441c9000c0a079200720f4600c0300c05800d10a0160400d40201004028250146800c0215805c0c030185280190041c001d0328001c9680400c0c9960001205080002415039110b111782c00d402211008800324010a0b01030001e54022490041000d2614000400f06c80c80f840c0d240c0740f05840c0c084200d80b500c2d48400c00052902182004c0c103480645111000303464004d101d9045001c61a0421500d02e03468450b0808100420913210340003a666203900380055503030f00d03840080000d451040107010810b526806840c26802c1803402c141040c003002e162034800ea00c200310550140c0d001c80c00400410700318206411800c0c1d482d00c1d00c40008984501d014062140c0c00c0e94107485500d00707666150350341c2c604010240706 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 708711843 1250 708710593 708710599
    0x31905040602090936060c0d1401080d0e040b0f0f030f330405120a0909021b01050612070b07021203221d010b0a0201061503021b24040c05 61
    0x41c1400468003030300303010304800350102c082c0c62403400545174500b520f14441d600818002d80400e9440c180082c04aa01440c2000c0b14159140345264500700f0020720070f8040c18000d0010303c60700300d0028000d010400720940d4144a81d01300ba1655500e074803250700d040c1032100161100181018001d000904010003859845030134401c51102e052044030fa91544030302c0c10103115442215048068203c02c440d0000c503800307002a8000c405071000d02500303500030032185800c0d203003a400c000d407521003000a0782d001c44011303d40d066010221400b14030782841400d0304030908486423180a201100416100c01480c401d0402c0c6070804a856415521440c0c00100d8501002050b25034406007400201c0a0064101f011840440c6402001c20000ba01ca035020f640324074100c240c000a42e28001e00d4030b000d0391000da00c0c03100b107540343d88000655140700c83c00d4a06110050300d0240e110040554403203400f0358034490089030f83e031203001c40b04050b012030884511124007050250580e980e4a007001c40c4160515406550 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 708713093 1250 708711843 708711859
    0xb0d0b1324090b01020a02090703140103080309060a15150201020d02040f0e0f040506060d030210050414161a031e01080606130b10051c021b0d0503190504060209 71
    0x154255000d99880c030070152944540120984407000c1204686415090f41e0169111442a80140c60850701096000325245000318084021240c5036200e510300780d000f00c4a4071000b009000e041c00040c0308250f4000c42e414010001c032203104071041100800382c400c1c205c0241541944d00308140c401c1d012203070400400d00c2c09660b22036070740e03d900308825128030803a4448004500801c40d1140020704550150750404000c1046460300c20410200c81da001100b1015803180040c01181081a80a8940b003640540c8815070030314400811581042c1801042481d10064800188800b0162742642c03480450880f055139240e949503a030030896544102070381205041114000030b10350790300050f200d200c5c0c0416140400c01c4541d00c5041c8068855a0310500e43c46010360615400091250002d0068102c00c164600001218250004100e0707218800c9101c4000102601d043c4500081007040c008518a14040e40303145040301105194020700e01c85911a85d460310040b4080c0515034040c0c65a810000705900 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 708714343 1250 708713093 708713111
    0x130608010618061e091e0905010e010e07030c090e0a140a03031a0f100201150e090706020a12030b0a050a120201080604020a0f050c1905250b0d0b13 65
    0x2035007900060000b6200141095008501c1c581c02451007080d2204c0c11004284450420500d08050032074014202c10420040c1d80002c0c220400307016100a2500800000a52a2408013900d082d148000545c030384550007440d0810010f4041441201120340e00400001c0304c034942c2c503030242010b030300c0b0714041d1111602e001480c400000101300802e00d60b1090702c08000030310a80310000558100b1507602d542c40792614642001d90b0801d800d6080310341e580d0b84000220803145100d50125046d46030003200c0782d100c040e070410070180c800308542d03006000a07000600c0000d4032542c03010380010301c0a20120815446680c0222540c607220384a40c040c207002865011110b4880191520f005100c907410707030004000101042e054203240c822680c0c110041d94a0209c0c810a00c5025507517684011a00f9040340301d190391f8800706681e200d80b00c049103441349001d01078024046200c407219035100303000c55202c6c880d2180e00708255030062045814250100700702190002142000401200300254030b203c030b040c24000c0d11 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 708715593 1250 708714343 708714359
    0x3250e0d1109040506190507140307021f14010b07020901151e050d0b1e041a120303090607030615082a1c0b0a06080402120319120504111306080106 65
    0x10906c00d145848508110443c04000d0f101030360415100030000c2a038101401403145111401507502c051107004803090b00440e1002104c074640b580341c9150304203589140241a85040c109550b004101d01941c0c00c0c10b08085030005084035006100346450a1010b0351401e1105004607608429461091807502c294400400041d09079401081600403451902c803002d0220f14080b060161985515010101048180c0c0248801012151032601c5203c0040b035034890182d4030703180310784c0030700c01d040c8080c0da204c0c20703d004200d02e0094080c02040900d403c129042c030003c58100012481e00b50145402c04a81d1151070a140002c550748221250012031042c0503400b81e60508000c0048a6224010501244401e1092400c441015410603403240f440d42c070400100384280b01d0a904a8001008880e041c41d0f003c1c00c02d40b86034483c0310183c0c00c4002e0b0398080e02c184c641190388561150400d00040c0f05038901569100151617412104901c1440000440800b445541d88203d0140c07496200070444180c4032990 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 708716843 1250 708715593 708715603
    0x302240633030906393103110108130204020a030b0603100f170c0d06020408030a170f0c190306171e0d0503040818060f03250e0d11090405 61
    0x16060fa00c1210032011041c0d520071040075418105404044801c210040314130410783d4858481c0024046d0540c0c00e209101c00c1d00f403841c58032440b400c54080c16580c034514040780720540c82650213040c0040d001c00c0080c6031819690520f5141d5045070010b030340c5d0340400300507030080001090007500140c022003006440d07080005110b00b07032505101c01c0991517980380c401102c50b03090400b015600b40c000700035000c41c80c2800c400f001c031909d125000150500340c98036a114950741140700d00000240c01c4490303803500d0350704048000ea0040c0b00180c403941d45245c5122103070740c4c0d4854405911101507091491180852080e404000a020107480202e65581d01801c0242d403081c8243c50308030035803148c0c4c070010000740d000240b10707035801041d0f00d0b6242143d445032294181078000503440d05204c101165010b07512b60b1071074005c11282140b40e140d42d48a00745031200c0b03a002c51100301d2180d40212403031194001e0680040740300300e44481c120390380e8171101c000d4034082125401000307005401c15850403e0204021000c10 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 708718093 1250 708716843 708716851
    0xf0b040f031205100326130905060d120807030b0319021c020904020111121303050f07060806120a05030406110d030c050301121e0302240633030906 65
    0x30350080007140300c0d8407140072500f05903500d01e510582c1d10b40c20800200e141140c81d0550b228040c1032000f002422043d443c075644817180140005001440503c00c0c0c00c068890709030001416949903925100954408591840034100042801aa45d0000e0007091183c1c106a5543c2400384c00c3c1d407008410403420200880381d000007244200c50544c084a180c601c1a0205d0300d00740e80080c145c01590b02c2c0e980041d50010520081a103846c050b031250120f45140b90001442c0003031000c0d00822103030b407460034850304007100c2c144802d1460300f080e40100300e4103a003c113515402080440722501048048100b4500d404881c5500510500004c06c0009035181c010f02c0780d54180d0440d809407003d070320b21014100c0444800c462144c0115100748014004041c0e5640000e030540e200c0c544a02240c08480a0460503225504c81100180e00203680e0040051f41c0780800c0d03482844030034241801c4d0420740b000528000b4625207405050f0718540c10b90380816903040c401e070000003000400c0c5e50390b0304100c14500c0c0c5603c0121 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 708719343 1250 708718093 708718097
    0x3060f12010f240b0a0507050f0d1e0e0405060f0d05010b090c0c0604030318020315010906080c010c12020a1e05010b06041203030c0201110d1d0115120f0b040f03 71
    0x20003041c05107102240f6410301c0c4140703162401859810106411410b8102620341c20410806104a00001d0b40402805040400d60070040c01034464003100280508940c42c494071914030300390141290030f50010380d50b003210502220082030603a2440b001c0b0340500c4180040c180d00c038a5000d110002c0c00010350005056060681e244c2c42680d8501130000c2d002c1c4030303003130800e08a5400840003401181c460f1b403061141764400001d0060078040380d00040c3c80c1540305c804c24107205c205640100310700790003442070f50010603c0c9009070a004000e01c001a0200441500142c8000354101840c40028424000201d80591003484500380e900b00c503026900010b441003003111150721300035400c01c0e10f1600740c054034200e4030303a048840d03503c44940c0d9044015100c4071a202c402d664850140c202681d20240142c19014044400000c1c0e144405000e82c1415000300e0400305680d00d410398481100700e003207003841c041c1d941007a880d6940048a2078842c0c031405500002803c080c0c01700701488108090044c60203e420701075 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 708720593 1250 708719343 708719351
    0x8090406090b19210204020426010c020d02071e030503040602030304121418030a0606061713080a050f0c060c0408010507090b03131a070807140301120803060f12010f 73
    0x4080540700c3c440c882c0c041c1c081010300a00440e100c10005a00366042940301800160510740c0d59059617581c0100e041788000011040c00c0051807010091040c0da011544900c018a00f502c005d1314040c0d25403040c1d005140d258072182507900e0b11000c000440c88000c1d688002120ba4881d41c8100082d100e403c10344040307070f0303034044407811040680c0b040000c0c80030b41807900b03121845c0c0b603200307001d64100021050740c9030b4140c007070403040d040811210f00c00d401c02059a40c4888028525451a40d8032240005103502c40b08e170f0004a0080c0810f0300384003580c40c5140e890525035550900782691004902492100c2c0b06240304e42d40c108801030461802800807228440000d10040e00c07070901c16603581d0381c4c500441c04614001e000081d0a0f0444c0081c2c255854014107070104640c0000b00c2141c5102c82c1210002c000c02d1581052181c0d580d031040e41100e00d5401018014119410800b00e50440080b407c00684030b0040840070540e07560700c00803e0300e102c4100405218500d4244150103000c0d121550b4450403107490 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 708721843 1250 708720593 708720619
    0xc031b0c150c06010e0402040e070621021e0a02070305070308040609063b04050109090b0c12060f180907090f0b060405100903080403061a060f0d050408090406090b 72
    0x1c901d0981c1c1960031100b000c0c0490341e0070321426000d0401c000780140e0740070380c541c401814010401d200c0742001d01820b80d108941562408a03880c1105450320074200a180304110030760011011008814141030982c049603030740d45c1c903142c040b454121103400280503805030344000020001468001d10071580c00b0348030440303c00c2d80c506040d2903001c140503c0f940301450000c0480e1020000d130800c403203d1510300104840d640f0508000c20115030098102d08d88881d03a6602801c00e2040b078881c6a544000c1c0b000000b03140c205841514040040040e000900820300e03201c0c20a12551b444005101504095846000506c1c0c58111640d07103540ca032249010042c941405041e0b10181c900501900c83c6024005600e003034a440240003070403a40780c41410030880121804400511003500400c002c1d4003070003012580c80007140d00c0305030251134161198841d180801880325001c0096040d100d02844000c40000c8130307512070030a03045900c1900d062030383c0545000004075058080341d0001c1d44507078033500c849844041c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 708723093 1250 708721843 708721879
    0xb03090d030b010815010909020d0b040e01090201091806091a1201050c0a140c03030103122703110a0b0c0a0b0c090924060d060503100b0901050103020c031b0c 70
    0x4140e540060340c1300c00040c0b072440780000c030f1801030641071420f010358035503928804040307800200708106401d866619001e19450300b03000701050000030703e008000c2a583c40d40041d2407100640300324000a503000018840c24046039200300014400208184081307078440c0031214846030307560101841094520a094003c00e0144141c0b845200d40e4440c0794a0000c50000030340d0001c80315600d41300041001c0081c004d00510504c0514002c51250000c003c3e8100c00c108050140410408490340401d070f00c908040014822035812400c40380c001c070309040b40e4a00f06010401c0950103800140440d840050042c40750800003520b01d00d8180244910b40d015118949540344920072100c680d907100e404080854011901c9020248050426800c1c21119421510200301d5a800100e041e55801d507441c0410407980c2004d0000d03080c00c402400c804c0200c840540001164901c0c10b00a0604140d40810814003130031080007111200810390600c420b03014426000207070340e840c07003030b40e0b00d40580e04140200142c42 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 708724343 1250 708723093 708723101
    0x30c0e0402040e1b060c030702150c150610030e0c0907120b040e0c06090d14031201150906050306010c061103010311100f23132d050603040204090c0b03090d03 70
    0x300c40846094280301d135041080810b0700000d02c00700e1203001c200030403070041e500c0c440144201800e01400b56160500140c0040c108995820400c40d201d007500d0070010180e44a6104050141050400045600e00400c08500e095461045980c1100600003404880d0f1340001c840c0030b2003050705c0024807805c0a10402d00050300c90404004800d94082000c8004500e0820098000b010f0060414072051105440700d0060001c942040c90594100280036030a16000c40c860a0150402c400606072554013070030001d1502c1c0040c030807081040000b10106a0980c421007810a090750809800d1280b41c04121140d2140d90080c80300300c0f0748044000310000d190038080862600d44e0601d8030b40110a0289040c00d40704217982c0684540c2540102c421489206c0442c2c01820881007070401c0314030454104900c1401450b018400380b41c0ca80e003c0175000c00b000c1e40008480301034480960714a07460f5141c502c003041c060454500010150030000c940070549660f00303005144921880e00443d13000e0300001206804071 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 708725593 1250 708724343 708724363
    0x10312091535181b0402090f060412020108011a03040b040501181b080c0d0f060b0414060103060b0306030703062708120618010308090315070306030c0e010605090d0309030c0e0402040e 81
    0xc41580340301201a05d003542c00b074007400c0f078090160035801c030040700020703443d50058000b066201c003804000420342d6842842140904480384940d60302c1c0300d15000c02401408010801810342e40814001020042c003034000d000c0114000455005024039494042c11058929505000c0c0562100b0001868030001070309c07051950740036204145d044003c0e1101c10904118410076100300340c94210040d821b8441c0d202e0102112045100b504250903e400010300741c0e25a540034008104087c03013482960340d00440e41d007044036400703000010b00356000810810f0005c0c01048002d201c4504004a4080c801d04400a01d812075070401540300565803201048081c100c048120201d80c455007005200042040b0700903c00c0c094000e08941e8500c42c3c040121440711800c64107100000d858003400c0040144440400e0f0141120402d8454698100203000f0814003440420900c50281008038006040c0589d4a844c003858200c06454621920345021506014003a6800ca01481c41c14a816895510202d007040c95 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 708726843 1250 708725593 708725623
    0x1080901060e070c050f0613020909151314100e0f070b0405011110090819022418152205100f0605030106090501031209153518 56
    0x103643c4841c0740031070320740079402e000312128407809407844d000ca4001c1240ca846040104081c001c0406a841488801d40340902040d41a900498403043c41d0100a5412540021070014445041d6001c2c01c11891529800903140001e000d071080340315100c015032b0840d80c252400c10085400514402e8200c0e95254440c2c841e5940d6110b09000034002980300f1403500741d050310000120fa4407050a5800201121a454000c8610510002e040d03107540480c980c00400d8042c4600280c4078889403040c03512107014002400d10360310114140002d000030607490011403030010105c2201d40c1c1c1500c4005040306020140d41c004120300c1140605030034400301e451106020350380030019002680401c6445006807000799034074078895444920216054401340f08041c010061110041100d52441c03c1c100b8146032001c046c1420032202030301c00e110030940030100c0104102075140c1040300300701c0c60911460181102c030600c90104400a0701c40e0f000301c00e20200c10300070a003490500c00f03038150616226644101e10105050 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 708728093 1250 708726843 708726869
    0xd0f020a15210b030d090501030f09260c120301060e060703020d1416051b04020f0a121b0e010806370905010806040b0c0a09090902010c02030d0e0108090106 69
    0xd8030810b00000b18959045000c07030a01c0d100c00000c0d0411202c11400780000304c180f0b908000c59a4540141c1c43c400d01100c03810031400302e09031512816440880c1400c00c0b880100d2100c902e00811a0341181d08061500042c0c90001f941e131010450254028413a0710300142807541d00c4500ca00d00b4804484030325900d5001402d282083c0360341640c8200c400c40c1c042500c0003041c002c15003281c04994040c01d0030380c411006810044020981c20708041125000f8601552060060120640d0110b0845189001d60f040050b1100d0565109102405001e131407100522070191000c24010f8008003036000d408800d032500c55030f0799140340c00d00518003025541d00c20b440400307000c0640d000d0307100d1009034000c80c101c2406e515043d468071405002d0b540e003030344499055406402000184814440c10a030003102401c3c0e0345281600c0041c0042141e54180504c004050340c843c01e00d811a80180159280c0d40ea026054440003040390340702400c1681c0340c440342c03070204174054001000d143c010311a12094440b546400d40d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 708729343 1250 708728093 708728117
    0x1140f1e0402090423010207230a0f05121603080f19090f12020708190f022107230108061005030c0d050c0403030e09090d080c090d0f020a15 62
    0x2841c3c03000580305442e411441c010048078083c4045410140103180d100150f0380d512203241130200e0811446441d60105000700c0c94061030341021518494445d08903101c06c0d004200c904004c2d0500900a02019810b040002e58800ea52002041e615405000b80c807006940d54403444c0c0031b280c0300310440745001000241035202d40020709585c480540d25008152028a0b410b0954501d200d201540c4140f4000d030344406800c00a5400802c00946d88014142a0102c99110743e560440c45030f0030b40c0c1001748079607800b080c6108101c107828840d004541d5070004580d025588c070103041c50310150041c24a01e2448202841e081254011a0168001d16000d0724810348000075600486403a04060070340000c90104011224444c98270f806200d00500d14840540c0c0c0e05c030f1545c50003500400300710070502d0107100ba403000c0007110500031078000d804440508241100d9640c034449000544154000c8540c021807080c0081d0034082e400446800c558801d031344192125071124400b03c290400b2011140024450001e49 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 708730593 1250 708729343 708729349
    0xa0f0606032a127d04021318080a0c050a030807090e04080306040c2a0b0603030f1b15010305060703050109110f091201140f1e0402 58
    0x90801c521901e0000e0b4428a2120044190b0b03404e410101025108198100600480501d841100301c207284050200c1c030840003c20701220001c203190b21281c00b03054400c51607104400e20000d00440b0a0101c843c610800310148000e9a00f0690b0280d0240100c288207a07089852849040c22130301d401001e07901005041d50320210305c3d81c003440201c400c22440611690000d9000c0210b440180e00c00e44038103200f480d20314001424221554845840411001c041c03002040300351007142d030011000e4402080c0e4075140c150a071000004451541214000c20305400c110a10200c011000b292156290b040d1585680d410542d4a0056100f5014401c0c8100b19800d80c100f0039240c04511402024103443c2c2c610f1942c0408107110100342c1c4203852580041081020040e80f51043d0340c050100e00c1c0d010001c0a06862001401d070142c2c84424040c150f000500c3c0300507a41d00d0b0700032134484400600a029040d0810140b404d98030301610b140d0155494400443c24440c40316980301c040490f94840010b95580320380070 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 708731843 1250 708730593 708730661
    0xa06050603160f06020f0a02060a030b030c120c0102010b060a0e0108070e0d0c06021015061209060c020718020702062a0d030203061e03120c0709050a0f060603 70
    0x14590380361140c66000c0c040b039500907a0700c00003808240040141c00f443c08601034107141d103114010300c003504506444001640d82100381c440c0000c01f45000581e86020602003483c0000a000d2594400310410740c603000181c001501c0d0038020420f80c02801401519424040c42d4059040480007240c12000300324640d510a4007480d60004142c5044511151024040740016030f00710401d580d124801002482502d4041181c6c0c6000402070030f04002d0014500b01311441078140c5d02900c410440da0f007400c0c80382c45041c2e403c81d254854028808000300c800c0564040e590342080c3c42810340a8000345140300140c0ba40340301340c40300740350040e192a1403c005110503400503070040d011800c070b1100684881548400400191200380c007a900d0041c1e0700e00b0440c0c02c0000c0580407100b060310a0f050003500c81c41d2a20b0200c1c2c014042d1408106244c1c843c03030b11624140c2070a003d60040e50920b4580800c010804c0740d1a0081081c021940c0002c00002d9210013046050301d00240148924200380803036100c0c9141d56001d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 708733093 1250 708731843 708731851
    0x714010b12030903100c050f0c030a0e06030f0711031c141b1e040e07032c12030c0405120709050a1103070f09050604030309030501110301030f060c020c0d210f020a0605 74
    0x7d03109280500190700320030781e900004100d606a51000c100078007410b0300440a8641c0301400c664660440c17614031101903100030014800d4082144113140c1d010200000c200765100c4401c08255200714850004008004181000c500c2210390a8000815000c00c115007d00c4064400304400c42e240290180d00441c2c0000720b40c03010041144200070000d2002c50080e505405200707240da02040700660054611504440b442241c201c1e2000d500a00c04114000506402070020309038071a52039170b0307484078408840d0066900ca60b42054045000d0700c1c0d500780100761101075680e005000c200b1900c0c1c01243c54122540c1040c1c044424100300042204240940c1302c0002c500443d14144505c20b40790b0b408180150050f40c1b0860100f611401c061041103030138080c0064805410002d5419589540c903400c459908104d8041c0c40c107a42d0301c022200c0d031032080c0520120b061018000c0c0039440068500f056400000b86040d14040842261611013030b840340610300c0c03980c1303299801003640c14080e44600000b010302030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 708734343 1250 708733093 708733097
    0x703110f03010308120106030b280509010303020d0f0c0b0c03060a08030430170304060209030105010b071505010e0a020a030f1b0f0906170604020714010b12030903100c 74
    0x40804100c0540c4000294003075480782c3c0d0074949a46540000c2000d01c1d0060f004401494100501c0400780d07261214000703d440e0321500007800901000340201c0148510b42c02082d000810000080145900001c0b035039207501c0345a40d0300c0d8010240b01c03400c851b40e10201c4802400da28000000c1070000a49602440d007058008120104030307a0b440e89201e01c0d40d8042d40c8210003000c8003d100201c100b01000603070090084041ca001200303140355a48001d03800d000f828000c1c4180c40840400c1c00d01030396134140d070541c0e02d002c0c00805c240d58486168080681001c031080f5801c141405604d50103880da801194100c0705082040a00e54a440c002d01c030194100161200c1016904c4403040298440d03802034408030400413800030143c0c0080d220060001c04090500c00610010481c1080354543c00817420f120500c7d4016002c1da151203003000140030344280c44014018242c060210300300001d041d4440c42c540d0000715441c894001210254039200d0280c4940c2c2540f64001e4010113810a405812004184c00c440c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 708735593 1250 708734343 708734347
    0x2030a0308181605010f020708070e090f030c01060330030c0203211b0a0c061d010911031006031502030a1e0606180503100e1207200f0306070311 64
    0x1181c0d5910388450f0a0704a811151442d104011658021030030508071074951019080740c500300140c0b29901c01c0300c1e206184400002c1000108408410700c203100030300d0b46210a5035601c00301803420764080e10581c002030754000c0007c3c0070303e41c0d1240000900344034450a00381401d90302003800e40c1a4000d003102e2102c0015400f0412076210f0040f81401442d24600b40c0100300a01c40c00c115000c4400d2044225006102500030065003010302e421880080388194440004103495240246e40004511801b03194103041d800c0c4003a01c010010221781c0710044c00c1c425001c880322040c5500b480300560b00c5a2102601c25410012121034940050b0019079000000c000e0200700c0000040e02100c900d0854000c0c10351060f80d40c1c200f4040d81d540a82e059003481080030340d00c280b56040030300007911005030354074491b4259910400640619000d020b4400781b0f44808600c06c2c3c0b01c03015800d2a5440903850f8400040300c40740c60880110b00c0c5841c950800c0041000f90081038555605c0d1400d4005100b04128174141c1c40381 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 708736843 1250 708735593 708735631
    0x18050d03090c1a030a1437020c1b1512040807170a0305010e01030c05060c010f061e0f0f0b0307030207020907030903020d140315060706090c0303080c030402030a0308 73
    0x4080d0000204181843c15141e0701e2608141e40002c55042d00c061306109410b4100340106490031040c0c00c20190196006d043e414005900b200140c0300c001d90400101c940003092140c0a0003020801c0c0b0f80140d03d03c022040e60391404030401c11048440d00c09803920340c0061007100303900d4030301d50303801d6a000d0302c10080d8034034140040e1500c0d502104d001d09000381c1e410001440340c2d5240d030f0600546005007507605032405954196940c030380b0030701005d0294900038a00070904840003003003504010104900600300308600303511800e05070b516003a10750b030300c0882a075800700000f001341e550b2500404881c5044440c043e40b03424401240100e500141c0344000301a000d0041002580d0344440a074010180e640740021402c1440c50044c1c10080550000d5041c04072900200402080032021290b00200070850f180080c1c024038006100d600610401802c103d180c6422841000881241581901d019440b0022a9a1400403400480c03108850003500b40e001280e1030300029001e50003040d00a03400800000d9202c4c8 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 708738093 1250 708736843 708736859
    0x1d090d1413030b28050c03150105130b09040c11060105062d120c070f1e0f050d0e06040f0302040216060e070303110f2a12070918050d03090c 62
    0x100c1901c62400507442d81c01902d005001380130000c02c8191a0302000c0c0030f01d150450000c0024040181104008000c86000143d2a88940200d0300079010800c2c0901c2c403d0f480781110700d0150010360071540103030303d04140b8010103401491000718101c901c00003000140c3c2464207114154008450550840c6845107558400d60441580000c120120102460b02e030500307a01c40c41c908903406041101c3c0000100483d00201c0c40e004070301c040036504116405980c0e075840359280f030802c10b2164090303c03140c8010b1058042003400704002c81040500d1340e070014a0070200c1e04005091145115103180700340898010401410245c0180202d802c140e408000c0d044c0550321400140c4840080450709a042207600740100364000314020328046040000307101d40c014552078940c0d500350b5004403000e03450300c00b000a80c21450741502082d00b150050980b03500300745904059540e0b100140550403c980c1071094100705020314000b1540d03c04e0300310b0000d012001440c84150001c280000c1c00b52000c185c08280481c07508 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 708739343 1250 708738093 708738113
    0x2a11030a0c0501061401051605070b040b07110a0e1b131701050a0501050f04020c010f0c122d0b210c0f0405040503311d090d141303 58
    0x401180c031240d880c1c03590361070081d003103070b8142d00143d00940e5200642d0b01700c0c0e40c1c484280d032a0034854800d050703200c1d502d03820003619000361507100c203240c00f00000f0085078400000b0302410000e442a050b01030a550060100324002d84c5501403420803642c030400080c086602c2c070914142890710009224540040364002c503035403000c560051500080d0700403400307076103100901c20960710240142d000c00c50380d41402d0014030490b003840403e0340700359004281c40c40c0e46c7c4800c0d80244081c0c020600c003003106016240014100313420700c240054650380350100144004030121a0664000d50030082c003285102e9400c540c3c0000e181408105412507401d1410742601c405036000e141a1000100c010085039101c1c00401c000c901c038203443d06000780e05080500c40000d0b000000c0e034500c00601141d6030300341c000c100307800da40440840200b600d00c1d401649000030f41c03860300a11420100c818130040c112594400d01090780d20007035403007880d000504441503940443c0b140c41c00340000000d02c54031001071030303620788035002c0389 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 708740593 1250 708739343 708739357
    0x801110a120b271008120a020c04090c0512060906060d11030607021c03020c0d230712120212041407030507080f01050915040b060d08030708192a1103 66
    0x5040c0c11a400a800852071a2503580089134003c158040d03070034040c1503529445da00c003803c0040c000c04240c814a8030b000388502c0580c0c10340031f002001155128103008846070054840c9030700030500c0a00e03041d18104003140561040c07013444014006500c0c0d543c00e018a603260004151380d1420b1605802c0103d65044c0b182c9401001e143d0700030f110005101c2258107080c1c130304869030824984100400d2080403004200510200200c0c100496204030310300b10140c07246600c0143d485240c0c000a0407004000e52a0414500218183d5840000d40301c4d40c60304200720f10907958283d5441500000050009a01d8480003416102820a8070080f5540b0f44e1018a003400d203030410001604400000e0344404001d10810794051a0a002400c00403840310803041190f2010300b000e007001c070209000820315111511050451a441070050307a5070b1400d00c0740104413205c00e580303d10510a0542c1c50761884a400d004005000c0068460800030368513005d110a04040110458014444400c5103840f54003401e00141500e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 708741843 1250 708740593 708740629
    0xa020f0d05070f020c150a11120a02160b030f2a0702090705040501050301060e0d020a090b01120e07051e0d0b18010908250206030c070c0801110a120b 66
    0x9141011071003d04400d0075401103004540c89440d01c1000c40d83e0b91210b2180c0b01d16a07007929a900c0689500032200d04614141c00080b51280404000109240000074000b540141d0309484001004500000c02544213210382650b28a060010843c100c0d0030f460f80c81e400a8100c101d01000302405421801c01d00174074450114500d902096040550400c00d00541d4000001d2903c0e502c0d0905200010340780740010b020b11410060807010f80002900d0381710780d001c16150000d040000d220350f02c0001001401d46140c11a001514240102103120520300070040300600910280c00d5803400c0c042072000071880012681c0d2854070403640403038543c450500b46003e103800707480f010600e0b240c810880d41285c0507200c281900c2da8504554607021640c0c045c240d45410350350100100503c00c9040401c6a2280c449034042d500240000510880081d510000c000003841520500c10345075650081c20b00721030026981e840c80c2c5904120016110344503200300f00c02d20b490924001104014440854400c240003501220 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 708743093 1250 708741843 708741851
    0xc01050c0a0545120f060f040f0f120f020115140102030d0501120b0f04020109031202150702030c01060f030206071b1703030403080609040f1b3f05060c030a020f0d 72
    0x5040c24a016004c122003c1d01c801464415000041c859603048014070711030710b080429010408020720400c0b000800c5801485050085120b03040500b2800400041a00890201c9801044150042c0103182e880c10320704984a9a0529211040d2000c01400c10900e0440c001040030600d00d0303919100b0079003e091407040c20003211149182030041a100500071107107a111786010000140c0c0d200c074000742542c0c1d0000c0c0e1121201c200315000d0b882c0401071280c400c9404852030400000940c0000030f0130310480300788000e04c81c0c0381c1d4402c1880301803161030202940248041001001250701c510341201c000748040700c5241e00707542d07504400c015180b13a001182c03140d07080041444107050340040210342040084861210a060968401d502c698080344010654422081581802952400e08100801c0b041c0160401000d4038201d040105c5003a11066200308104540035042c0102c252840c00c2c000d502c20024065919001d0032a40180c2005102080700c070380030003070940c102e55540301034424000101e1000c2 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 708744343 1250 708743093 708743227
    0x803100b1902070605031b13030203031c05010501111509030f0418050c0c060a0c02100c17010b0a020d0804060b04090302010218040b0f010309060f0c050c01050c0a05 73
    0x782080d41d144d1140d02040401e000303103c454054480004591007502000c0c0c0c1e030303070621000c28580317002055101035411300001c505500c95405144e030300944442d4194003005039a803a44015030728508043d1400e0265440a030302020901103070f03680c036600003110303408032820080303804007004d4079070f0103904400326030528804c40303482001650040a41003115412220b085c007030101d61540c0c0d10040217009941032500c41c2c6181100702d00921640740e0a80c125170b0284001c050246014062071605d150307601248070a02c000003031007213402c0165801001c0c2540580b1f0188800c10301142e2141000c1e0080c1c84a55032502081c0d11959103125004c1d02c02d01c40c0d0000360719002081d03a42d000000340d0b0300d0203c0c011030408100f41c00c82c3d503c1490f80552400d09007800641054242403610042886509021619140540c2d0351509600300015141c0c0800c031800034030a56661240d281c2030b81c0510907561003c24000d210491442c03541c3c01e80c8200c0300d005030302e691441030000038883d005c0c0003102c02034100e0070406501c91 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 708745593 1250 708744343 708744347
    0xc080a03020c0a150c020d0206040f032306040b0903040e0a06060e0f06091c02090406021e160201080702010e06070f02070b030c04030320030d0f0501050108040b040803100b19 77
    0x41d84502c4811100514440d10f41104864266101d601240c20840704507800d108540d98400341d040fa450300a40802c1c0c44a4580e0700ca51038502882c003040e1381d003046c0340c210401f101c18042040d01404c0001d0740940b0250300d6a544d251315a49001e4002e40c1a400288004600c01c003907803000cbc9210300c0c500a0b000c82d00c28078201000e0044c11040c1c0e0080c0c01181813950004503074940804498884c0401c0e204100160b02e0361140090141c51010001c0d48200d02c1010702c01840311039001751004e50003003840d04c40070392400c03a07100c1180c0c0719448034617000656070855a00503600071401a80d100d00d40e4000855222000c0c58401d0800c801114407402084a5105041c1032680c1002607801034060100700c1459810035003440038030b5010b1407000074100310007190003102c21194258440550082c0b030080741d444030000700940d0040c2c0030503015800c2043c0380400000d001c0d840ba05059001d0340d000454450140c403103481b030854580c00181081d00b104e000603000034006141170001d0210408000c9c0c80420084c4500300 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 708746843 1250 708745593 708745603
    0x1e0f08130609050f01090e060d15050108010605010c1a0613090f03080105030109031209021f0c02010815090403121d07080105151c0302070306060b0d0b0a1505090d0c080a0302 77
    0x14038004c0c81c3c41210a4080d98000c83d0140c282d5140311103402e0640c1e503070340c0024140c1c0b050703a0b002844500000c00b0900aa103442e000641030300c001c240240400c540319001100c503030000071030142400349092a84641c3c002c142d2201ea40002c00507000964044004d800913040d40c034441c9044071082d114614513002d041d80007130445d0140100310002d007c0000242c800030003e40d601e041c1c0780d81e001e43c0c8075000802c41d62124245104c245100005d000c9400503420f018040f03041c074800a901285900b030009161000284107010381850048c0880401d48507901c0407030b00b07801017050807000709541341141c0c0c4030178002c4420414544d0004005140050070302071002d003900c101410b03854600c04035400002090b1f8604480d54075a44403403604001c1007140e0b050032403034085694005403543d8070708407000c50301d40d402400a00154032601c5090141465605c02c0c800851000c2c4542c91038500c500d400001480d11500060002c0003000b800d0010800044d207403c2c1046400303a10040d542d038803a03102c500c01c164040c42 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 708748093 1250 708746843 708746849
    0x1050a150b09012c150a092729030d12052e140a060e13020d3e040b13170303040b0f04150e42041e0f08130609 49
    0x9178843c1050f0345548068841145c0740603000d00486031014481468003000b40c84560704030b072290140001d501c0c5580c1d80d00521188035140840c0700c01120294a18200041c0815501d0001d83c0c030102d055098000d600c7c014040605881044800c1d0000c080c1541040c829480c8120440105003004c0d9191841c1a0007107501798103e00d011303511502041080c140c218945070400c480a40d18400303100c402120b100c000388207160184030000d03d00210f082c00840c0e107101aa6121620b0310141016501181d40080c2080d0092100034042008120601c0300c0c105200250480001000e5000e100da40ca50522044903000c004a60865500100401c803d105501007000d4004000340f034003600301d043c69250b8080c1d0710307840244603800307985078902c100d0405030410076480b0302880503107005403820124115040300e1004000c002500d1a0507001d4124040d0f2030940740340642d074024007a17050034040c907007a2580030300303519020350f03004210342907101c0414003020007000e80b1124060803001e5241841005801500307250 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 708749343 1250 708748093 708748129
    0xf140601121104120f052a04020c07050f13052a120c2a061f0803030610030204050a0e100f030803070305041707050f01050a150b09012c 60
    0x42c2805064480007088034103441114409100450030341c106003107816903400e4000e10a106652000342d00244418032040054216042e10f19004001e40420080c1e0184139106042608454810401490214410129802d000c0c0130040300101c0800c81000702c80040b900f04503c810561007050213901085008980e0826426000c0d0402c03415112400c0b40e958010b10000070045c0008905030408050780c0c83c040d150005032020700144065641490321040280ca0400401780280416140e0b4070000c903040e419039181c0380c011810743d950807040000107000072502406145c1d00700008122920740007042c40203494404000c41b03403802d007180480b0140d07400364030a014002c1a1081400054004070407690411003078900400e01c4d032540c1c180b0713040c0380d000c0040607401c031200000c01208100c0e010644000103413811000304559601c454008055a01281160080154208003802540300501c047d106000042c0b42c00608052030281d81e01c841d50b03d1071140c0084561840e0b29040343e01e0b005000010003074241c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 708750593 1250 708749343 708749351
    0xe0106050705190c050d05010911030601060f05093c1008040206070c0801051807080d02031c0e0105010b12070f0918020915090901080309010c11040f14060112 70
    0x15032680307611854030b5808018414103800f52030303052040c00c10840020b484004d050032642c1d0070516003207009114160341141c0b4a004106058075030f103400704600e41207034103e8454280315111402c04035015800280020344c8107100c0014501504030030002218044010512280302c3d21266442d141258400c9001c03500c1842c00080201d000c9a00030241500326906442131074a80c401032420059a0301e460300094019840c0500300f0076404c905190a0b00309000c00d02c1a42c1440f91207041340e41d1144030500e034140c0540d01c2005510a56143c1c110301c9035090444040c009184981c3e088583e0a440007a40842071103080494461400701c030b0700e80b440350413901a0422511814a10b540074000e920b69210307000b0142c00040340000d1803001c0e40c0480d448482c1c02420742c42003142148088040d80c0101003000d008105000000c1050070380001203552110303058483e5200c0300041d0f510b100f00541810b003840d410039180c1c80ca9014041140c050031242c162505c40050881c1b80890004102d4150304030314003070a80c14 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 708751843 1250 708750593 708750607
    0x10020a08120702160f0b0a020c0d05010203180601080c0d02011b030216240f030b030114010e0c03281419150b04091a12070905240f120102130e010605 66
    0x3445d54901c04c41c0c209805207038544130491020f80c101041a0051038103c200442000c00304201940214443c18144508581095a080c442a0760304424010b01a6a41c00314400141c50b140102010172214414074007100700c10a221102c141d10000307000202e001d85c0c814118100220102c0c2038a1014042c42c202c8480030803500945c0000801c1d030001c3c120184040c141c103148240c1d05c01e80080b4585a0054002d01040b0601c0d44071001800d400d00c0344007122041f0001040fa441060801c03680120303c0050800c547d840681c03100d000412205151641450f902c44d09448240d1211300b00900c035500140c81c80c1500100701140c1c000b41e40704156800c0e400d00241d43c090010507004002c2e0303810b90b0710f210000605600c1d1900e180011800a500e500e611922000b800c910300d103400210941a1b507003211081c0540c0d10742456154850b03030710301c50494048121002c0c100582c10800c0d410340c00c10a0017005a02208281c0641c203089901015210f110b14030450014012000e8240000f0b0041065140003450502 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 708753093 1250 708751843 708751859
    0x3070b0f1e0402061b0309040b010305090604080c07031e02010e27041a1312020d080402060a0207030602160b18060c0a0e040c050405130501080c10020a0812070216 72
    0x318002030740710201c80d950045000d548901c002d803154100b140c6114140d80c010a4062030b520f400c00f240c0d2910071820f20000700c04d5540700340201805043d03100c00800c00741d21140d450054540041c26080c1d158030030f4003000008110001c41c040c1c0044460300e5680084541d078000100b454a8103012031b809141900d031000f040b1940159042440301414109400070740380c0b85062040c007010040d03c860b8014000c8148144040d401a5040380c0503c40c40d549081c6918400090b42c480c4904100385010032071280000b009400c040009100b090060300c1034442d042e03240d94070507040380c106006206003080103910304020003040102480e08481040780d09141080c80245441e0b40b48802800042411000304109840314001da051000303410b8018803d01006581e400000e0070354100d840b81c0c0c0d204000023070a4014144241c0f0503039050719100300141c40400981e100380004840d00360380400442c4900180d81001c50008405000180e5074130101c6081828070340300c02480c1c01e00084031418504400c40d01084050 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 708754343 1250 708753093 708753121
    0xb03010c0527031203101d07050a030b0301050c22050306040f0201091d04200a0506030606070b010e07020c011805041109030a1101110304060207090906090f0503070b0f 74
    0x300102c194000350354110700400916805003007445805100d424001d007201109040594410401020b0711003040f640c5248030f140200301aa4082c3e40754800382c001c9900c0c00d12950040841444e20308010449030b4401c40800e08445e0112400112008003107410603060307092003100b00c8000000c0c000c3d100680d0070400066290240a000107110148008103881164012080040181000d001c5100702404001100030403d108840445a81f042600c540c0640f84440001c0181241c0107005410b085050400b800615030000d01030303030703405101070040400041d12000018043c0c941030f180b443c0c95040c501c0c0c4c041c5c0352030b800d0103c40d4140010880741d401404000103038401203030011a004a08201e0148a16155210308121140c040c050080c0e00020312028905841f10701100fa40c44003c003440740ca0307034262640154054500103802016082000603040d40041c020180030b800009000c501e00d0380e03484041c3c500c07108120380c41e401c04684142030041e40081307585e00107109103000003a45031a010400000c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 708755593 1250 708754343 708754357
    0x10091b0e0c031302060301061214250e060c010b04060e010518040c0b0a0206060a060e030718020405210d03050114060a0c15140c12130f0c09050106030b03010c05 71
    0x5003000c4001070f024102c00d071a499540d500580b03000c0e940c3d41c40e0307080201124859002c50700000c2c140703892541020803184e02c1c10311031001c0d01c040b1a8101c00d400e19140001001d0151081042000d110310000c1740e90f500010111203100c0000080d903504a1f4042c401900c859500c0420700300c800c84010062902d40c0d1040c1815a285202d4001880e5901e01e403680c42002d040c2c2014202140108050002540004226001d404121001ca0310659201c4046403404980c08401d40c0540004402b00510582e00e419041038060181e0094102910781d03020408000c042000541c8541071045261071800050200d150400c109103000e000c20340c1040700080550010880c024041d50000030001c031041c0c42184007262859105400c1c1680f58000e01e000400b51014011345038060b151840410070810080d011038003183c1d0200500382141d076441c0500d5800403a03030030050703074100002002c00000604c11a6083e0241500500010382541001c2c030090071101024651802a894074058441c080e1b04902900c0b02 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 708756843 1250 708755593 708755611
    0x1a09031e01150f050301050a0908091306241b0807080f0706060306050105120609061f090c1716020c101106090d02150709050904030c0510091b0e 64
    0xe00254018050041800302c10000d100400d2000206000d6a810300074800c4a108070000d010988038481c4190880d05400d60040082004100c0441d050074003120b4006e0800c9a82070000c1c1c1507a442e070703080200b20030140508071300d4104840741c03601d0b4607048002c5906001c40345400880c04003065980c1d808501c107480c00542048030115110748034500301030403030b03201c143e0040043c44020355030319051001d40030070700445104022446180c0001140003e02c24800c201d0300c4020a880d44a4500f1004500c48440d04441640d00f03c03540400c809109001d0203004e03e2017641d03480c50244040c4a00380c40c162002d00304417105043c80c0700040714594001120032003c0300c112009147c9616140064600c0c0c060a40415043c1c00785d0010401c9294000c06c80403040c903425000c2e079010b0241401d0301c85210408480346004143c840101307103c0340c142031400e903601500c01d00b0311002e0b401d141c1c3c071418a021200070305c9152680d00c3d03441c440c1c01c02000352407141c404110596000112800e03c07062041003c4010a9080 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 708758093 1250 708756843 708756883
    0x305151b0702012d02150c070305030402090702010605060304050601080106050a030818040605040f0b0310051e09190b07020c1e010e0301110f130b210a1d071a0903 72
    0x1102841419201c1540c2d4010100c02c040000d0f0a10080e4072407050b240d54540700c20001b40010321090310503088908550380740ea542c5107140d4940d400c1204400300136040341b04540d61044041555103920006602650151005242962403c0b10030b80c252001c60700b141d8002e5808400c200009030590080da210300c440e0000f4090f2941d00e001c0494000c0c101540041d500c903007801c06030340c44240300341d0100c1c14021003602614458070003c602242550015104540703044200d90030500181c1680700e19681024070030050341c8545104400d007404144944500381d4801b01c5100500201c40d0301000781551102d0143e03070903064010140d01c0c0710035244000c0803403410b0260317141e000011603400b036011180d805c104850f02500d40d101064400215040380c8100d080c204003504010902c8892041960714050040001f0b0020041141c0d05645d0f9034030181c0740d201055220500c0540d0000905100b02c2c0c18a003100041410301d1500c3e016a04e07030368544c030300070495090400ca08a240c2e2400308030524941348400c0c83c06 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 708759343 1250 708758093 708758117
    0x39050c0103061a0c0f0d0306080c04050403090b07031403040c05011704020105270d030f020d020a2d0b0109021c1b1b0615090e0d08150402130305151b070201 69
    0x1360a100700c00441ca1494010b01100d201c0e210b81550100b0300f1340b5140c400b20341000c15160240030448a003a6000740104482240401c030304c100250041c2400340c800d1800861181c2c00050414030380d0800d40d021210484402014405942d004c2000c9065800c04400d0340e0b50703410f03d600060042c2c41459032100c4a80c0d170802c240c00c0030112415003600141005030007030f08d410060741001002034110400c01001409010300100c0c699100007040700005402000c1d9190307000a024000c0780030000b90070707203420031241000307804007182441666600030b1610900150740d030813808101c19001d90424a02003d04c5240004810a421303000784260890f640d1800d00e40f5078031444002117440203d000034000c00240c1417000e403200b003c06e01d10300c1304121402c101003030102820909101e0f41315401803020800050081c40040c0035000310300124044130401800044c5001074060904001000b2a002511035a100c601c0c00070f281d05a01c8041648146440300c2d151040c001010b0500441c817a41c5006410801c420001d2 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 708760593 1250 708759343 708759367
    0xe180402150d0212090a02090106020a050d3e071e05060d11130f0e161422030212070803030406020903031605060403200a020139050c0103061a 63
    0x981c4c10854006401e00703a86001401c540ea07400e10401d040f0300445d807500c0000f07034650002035070390001540b19002c1c10008814200403140f1051081183c1100030342031601c0c0d0200c1c0070f07000c00f0301d0240c1ca480c441a8070102c003c000e843c5c604451a40448904c03e40c152150f911039210580d540300355041203c58503074a5070b80d003022001070055054004421403001403041244040384c1e20881c1280c541c0c02001d20520341e500a40301c80c00b40d040f2540039001805500450032540314002e00c125a0006010440c10210300b00500e180707220361280000159080c004040c410752800711021080c103007080300240740310790900c410103440c1d000c0544003d241079008a01030921b598144260380b0007500300c4400b40c0300c60105050032a9514410703502030380403510540040f0910300781107401c40013180446000b8100d02c24507a00444010345810650105154010004603081200c80d41c1c40c881207180900e00344e00c403481420306a00f4680d50320012414540b030a80108130440801140c480321000c0750b01804c0d03e07a1021848 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 708761843 1250 708760593 708760597
    0x50d080c091806030a290a02070308161206091d0c06120711031306110c030712080f0d020901110309010804030311070b1f0504110702101e0e180402150d02 68
    0x2000303240c001a690000400b041500c10011b41e04121320002c11140c0382c0d24201c808074451417001600064401c000603a2400b0545000b1018034550300e00308100c0141c03464039008039040d6810011185844100110505049041e400c00c0420120003800700d2004190000b07001d48984400b80851584950014803001e02640702d6120354411074003680d69406010381c104561a150340918400b15088801004843c140001d100c14025405002400810b0821040302001d4151001c12a00d14904210310403e461203080a4072554110080c003503110b80d499000900329800803540f5500d2a8020b003c0b2018681e480801c2a80040c0c040c1000503060300d13010301c0c4620610550201401e070b00449000d109010750314960f6111400c40074880612600e480e1820001a0f4021180410610034280029000340c41d103910200409809400c014094980c4c6000c07140f00c000d0703295151404124030311200000c500341050b05c0c2c1e000c0c0211002c0382d415440c06900051100030404522141c186022035080c03007199440d81 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 708763093 1250 708761843 708761863
    0x30c1404090b2d2d1309050f0715170601030209040638040f140a0e0702100f0513061a0315100905090d050d140103050d080c09180603 59
    0x1580c980142c0c2c00300ca02ca41e0810300c0462030283c0c03a0a4450011502d9a01034034140302c02c41010100002413070001c01000004e90410114010340c0d80c40344e03400041c02081080700301910302e40641180d03803610b91800c07442950b0411701818810104661100c110400d21000d0780030701c0034200182c480b900007010800802007a000303000422120a95107814440010200851003048a108a10862201c001d089240280d10035040b5580300c1d000b040c4a406050b420151800030040e1880c0262940c481c4001c9906d20207075040300140e00034416100703011050380030341d030700140e4030481c1482142040c00345510890980360014244c6a95100d41045441d2225501c4a80010040880d600e4030350119040c407640d5016144100700c03245030744000600c40072a01803603100e0710751b18000d401070030b030b41a1040d18140d00c00100d800000d9902c035102c0c0680442c99209502840c00795000b01400c0030580000f600c080409001e042c07114500b8805004660f591041d030644a010700c00b04480b0075292000401e2418407150 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 708764343 1250 708763093 708763129
    0xb040510060b0c0105010f06020c0f2803051207020d0305280e0f0a0608041509050709020d0b12061609170109170a05030a0b0f130b01030c1404090b 65
    0x1c00245604002c00034080540702040200b200d40d036074a0007040301c41158807484015821400da00e40d814605800f00c00d04e401c0e0b0161407005402442c448040c00300400c0e414501e43c008070500203105000c0104810b1052040e00c00003245401d00540004d1400110b49400508000001030502080100d1580106000140b01c041081a414242010340010865014540a2607a001669076107281c0408510101d6901d0349848140d0f48a0341c482403e20520300307075840c01780394a602030500040c108204d84070041c14250001a180c103008070410f0160b50500003901d20a04007900b014101900c0840d6241d04500e101c004040803000c000b0094980e10391075071002d5501c084d1040d8946540006401403105140300d445034420f140c411000300304250152040b0400080c03424000140b070140c555000009410004041c02d400d40d881e100010100f0110b8240444900c0e240d807030396641960140039503030700d01c9114200703440c0e0340207219140e0307071240903500c00c403504a5110400b0b072040d03845122100246080710 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 708765593 1250 708764343 708764351
    0x5120a0906090203150603102a090807030b06010809150a1d06010f0f060f0f0c020d0203010f0b0f04141909020a0b04030b0a020f07062004091407110a0b040510 70
    0x440c5e0804507280c41292420b000c1d0040070184503002c1498803949004030040740c0c13510a5490350080c4031000d086141d4121062015141d800309203941c04020742d1009521654030072113a894107000051128802412a42495100ba211a001e00c003086143c2e950000d0040380004180040050200c62410005030b11700050103020b001060b80b0f1280c0708002c082e10201081c0c84000d81e0b4450045801d036034211210701c00180c2400368045254442d80503400034500060483c1c400304aa9000030382105c01205026030b0300e85d562110043c45040c054031440080c4000c850811440b40304581c010402c40004044003d04891300c1c0414402c20683e40c081400c498001e4511181136807100002e1a43d948036001c282ca143e400d1074002802ea91003170007201d01c18607a910700d6034144103e07691282d001d48010140d0044410448940840b030144140142004203200040823400d0035082e01c000c84030f80400b80581c420401317070b00c0008580480000311042c007141e10840000b05a47ca6003409401c003100c2040184080c2d0070 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 708766843 1250 708765593 708765613
    0x50c1f0842030d09050306070f050f040e090705010315030602030402030f030a121b0e01110f0f0309120c0d0b070905061204030206090a0302060a02130f0b040f0605120a0906090203 79
    0x1e840352000030302419421640141411003042d250038a0622070386a00d50701540000b07030441c6c418036070b1008180310303404c11070709020a0b282c0d902c0d002c0c1c00c0768011444076108035081000c441c60810155005210a003020045003a802c0e8100c8626011408081e243c00d030000049411501e0811100c001900c0c0801039075215218290700030300895845005504c3d660030807a481580d000b0098241040c0c580d280c031010000c4c2e40050040d281f540d11120070090b41e0117640004074140009200c045a0020318802560741c1d00003120420840006d144240886603201e050481041c0d2030781c1e0b0481d0503054002d012002030ba03480560440f600621600300341c1e0400008a95824101881c0c4102760103140b080d001c1d075400e541c8000105135580c40600380640164419004507040074641c1e0300600c0c40781d00c0d60140e019007546440040c440d014242d40211108100018100905054400031502410003445c10500d00441c916098150300c2000c1e120340b8007155648610010018242e0045502c5a40035064542402c0c0e = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 708768093 1250 708766843 708766951
    0x30403050109140d12050c0c0106060e1002060c04031704090c170105031906200f040602010b1c0818190f0603091505070c0f050c1f08 59
    0x20038414203c4400801501c0840c212070003044502c40c2c0191070360b80d48214508144580003924028000b207240080070400c0246480081c05104080c0003036440e070510180411090249142c10b50129800b113400c90014040b040d07010b4400c1710212a0045940746000b10569243c400c240300d40c2c0c0c000c2c070486151500185e2300e6034001000d0b92205121441904880c1c1e40c881c18951101411420342d6410700120f009176001501a9000d400a654484940820a001c1d02101c0f80141d0094104000d041c80105003044920b0342400f5002042d80191200c09000c000082050500311500d84020640240481d403641e40620401850407d040c004100c07a003980d41c40040341414240c140101e0989081d0000c02042a50103030181035174495004106003080d03070459001800504015002d08204180c014905010402842c401c0c000d050181014003540261304040040c1c0094220304034450000c03207050108a075400101c183d80c13000c40b081c040c5403106041c1031111581007500c1c4034400c10480d5403410b01c4c0c5180c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 708769343 1250 708768093 708768101
    0x30b0627100b04030203031e0405040e1b1005190509040204150807091a0d09021002030417070b0a0e030106090f241a18040c0c02100809030406110f0304030501 70
    0x10040c054250169516030107030302d08501c074a0002a401d9401040881d01d00c42c3d2200000c2c40c0c1c181e5054015080c0741d180c0c0d0006050b01c585c60030007004c0794400c8103401c0d244099500c2c150b05071841241ca40d010310400d044054030324014528070100016a80e40c1da0721119010300100c819510000740119a2240c6604000c3c8060b030202e43c02400141c846000100c1c5135001d0780210090700c044038040300241030b000f00900503c2e07010354900c00045440c1d00c20307440180c495080d00d05441c900c2e9009103446a00b810301c00024646001c00c00b602d1584000f0301000012810802c80b8804807191600030989501c4c02d0102e4003400143d40074010552400391112000702e800e5100040806c1c11004602c0301000026150400040c54002c0c1c00190f02c4034000c000d00740c0c1920380100b2040310190079504104060900040848500c080c928010504a0300003008502e400c45203600c6030021420301c0d810b241000c401c06c0e0751b40d0141d4007401c0b0920500c3d40040d002c10008211030750346064076400722640d450700c0340792a602070 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 708770593 1250 708769343 708769351
    0xa0f030c0f1208100830070c030b1b07111206070504060f1404270212160c1a0613020d02090a0803070302030a0c061e0b010e03010207020109030b0627 66
    0x45218004c200b44402001c0c00508a4140300000c01084000604c50040030085000140780302402110400342c203200e04015001050040000c1e44c056840c50402d01c200b2280180044840b0100b40310380b5045940400607145e810b50002132844034290901c1c0400d1b03000883c12003d0703100388a40010043c80c964082c1c010f0095503625075a4a401c0c06070040240c0324200e20114414410b071061105000740c180c014051681c1c3c0254007040d100c400c0d900c4c08070b071040313900803080c40300055010b1080001c8507105c001e1480704aa0305181a209521072600d60750b2050302c0103e07048546411150200c0ca4030743d540f000681115680c40d1781103503103074004441e4000a500010a46001d2218910001139500011007942c07825505038020354030f40040c081d1b08481700301411700116859a603486400398100c54171102c0c410481c00f000c0000500c20000310000d003007802283d4036903103e40e004001007070050741e00031516000c82e42e00440c45003883d00c9200000c1c20450f1000031151610340717003140401020392991041402 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 708771843 1250 708770593 708770597
    0xd080c0c040e150f040602040b04030303091205090d021504051909200d0e070b0d020a08010e011d0a1b02071805010311090603010e01112503020a0f030c0f12 69
    0xd40c80c10541d40d01d440d0610000740b40c000c00841c0f00000c3c400004c3d1038085601602c1014014900307510381f0b0031844150011341059001941da44d640360b08001d00351aa0780e460840034100f10b41001c5400001424034220704000034007510a69025801c1c040041040e41d0103410000d04140c01403841e610b10300c40710b2815118444415080c00e0f92070701d000b801100b401c00e03100d85010b0130510f4003100d402003501900b00c00c0750304040c0340b00381c180000703440c00044050110380c06c4106025a0300c0c1d401c607500400b4050180c00c0166013844100040081c1c01ea001c04c0c40c075070b10340c1c81204840319540d080381c0c0100801100c400ca01c4803180b003290006483d82d0201d10b283c2a80e000181041a400c50a80f49008884003404000c1008850302d6440782c003031810b04030107039000b10010008100241c44c118013030300350f03001e0718520140700201280d0360704c14240401c1c454442c04400c0070b122050f2421500c0007596011102d1000d019440343e5100013040c1071055442c4400590040ca0181e0410320514082031600c0101d4035a02c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 708773093 1250 708771843 708771851
    0x601180b0319060e09060426070605150306010b09010c110d12020601060201111206030a0512090a05011419050f03011203030b03010504051c020f120304050705060403200d080c0c04 79
    0x1203400c1d03400c00d41c0c1c2c00703240c0c1d0000034001a62035658944c0d051040722002100d002c800042310300e40d4100c03080205042d0b80306060202d403900b1b000c1c083c02d581c51038055015110340c01213801401003c2c403003400e507a030f9500300b480c02280404041c01d110801456521415411800344100300b01032000d001c9019095401c0b560031265160b984403012400c858020342c000f000540c00300440304400d07111a01140d00140010180c8810302c00c00c4d540e861400782c89990780d00c0c9401d0082403643d000d242003950517000b80402e00f00107080c28090410304505104415000076203121070403040907898411130680c0c65246140c0c0c4215501d5841e82c0d141c2010b101035801c100d00003400e009601d4001e00b418040c3c180155801340c000d1250241e00c040307451200002160a5045110311100c210700c5040811003008008400d02075540e5a04042c02c01e6410104076170072881c0520b0042104200050b8803100d544100c011148000d0002c40566002070350310745a031180031700085400725800f0784015001c5054040400f045030104 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 708774343 1250 708773093 708773099
    0x70807180801091b0f030f020f03010c020c0102060c070302030d11040f03050102040f090605030a03030c26090601050409120c060b0d030203090f040b01050702010c051c050a0909140601180b031906 86
    0x1100509000d5405106105c010400c00140f001492160140c070041100d0103504a40c004603003140c2c0c41204207401070744056502c501c0341d40c062180daa000b04a84c03e11600d401c1c003a8801a58078070801d1028140c1c141c0e90f002c0d2000000788501514040d1000800001c2041d5032424600d000c6d41042c000c0707a90040c0e4244001650705660b200721021110040c01502c00d10002d41c80070380007006068040002d0261041e0180201c490001101c10201900141c017121800d0010b0624a880d40580000d4000c51410f04402e01084c2821387c1641110403a03c2e11042d2900035280c0840070304843c1c031035590408074010200c020580c000c0050020300d40103584a40382c111207d000c00c819110003409050110700300300016070165109200510308180103e08a9805029600e102452002c042c0b0325440020408588019480d902143c05001007105480030b01c44034030303203c00d44415180082c0c00e80381400340c22a110b9001070b668844190040c600040c040d84c40346840c28030859485002d045410080349051408 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 708775593 1250 708774343 708774383
    0xa09022d09040c03020d060b06030a09051e03070f050f03070c0819030504140a03080f071a010815040213110a090503030c0d081906140f090f07080718080109 69
    0x241c0e10450f00b004035182c80c9442d5400380300f05d43d400e03990107a800b10385079020f901850322418020343c01041e0801c0c0000300005c0c242041403c00c1743c4503404400ca054030035260300c921200001510344040c1c00c030300c80b450303540c40500e8518600385038100500b00311b01000ca00107083c0f01100c034480c1c046852070300584604444034135180324032410b4400d0040c0400d000340400d20030700c50004080c117a4004054400300180b0344075161000107400000c615080d01d8400111001001103012220701003a200f8030f1544400c0d41041c030b502e92551028646d440d40480540002000d40d599110290b448598400003042111544403000011740d02003c800e0010903014100000c49080000071110421030341c030040c10703030741c03001c48411a1050b9010304480d4071151f9035501d90900a40344d203d100010612510300d02030200100040c0131130b2030440c3c1d2165105891140400003c00041c0310340542c4904103180c0701c038142da29400d094030f00910403020407008542c0c00c203020520840560000c0e902c2405136444411042e601c07011 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 708776843 1250 708775593 708775609
    0x21010f080307030206071b0213050405160f030b042f0f0d05190303060e100e0a0e061506130b0d110319150e070305040b06060306060901080a09022d 65
    0x7000f00164003000005640a02c100714060b030b414240b05d001ca00864a03500041e418210144a04a1159079002840704200e010801c0c0d450940c00400002d50161400200c012030490038440940564905400501042000f81c2080d010714041c5203404001b00d003524000110800c0c03034072214003402e107a08002c00d4618010603205403159016005107d01c482d07042c2d165004243e0b51400b20b09140c0c84804c007148001c0c0a04501d0710824003880801203841c80d0903289081c0b02e6000d40320015213440c101e5245803000010503040d900c0b14000c0d080951034080d0a001c241c80d0b2042000e145091804000b01003000806407008080790410084240301c40007001c01a40b205e407105860740d4108613140d42c0c040e5481030454000e0035014496001c051004c5a68500d0300031207020403920200040d50350340400041110750517026410100590f0018118075011010030614411041c2050600c0b0108002428081450304402c2d041c5502511218a40e0150140d01064042c0503204840c507002a103064211810103901d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 708778093 1250 708776843 708776857
    0x70333050109151a0d09020d05030c0f010f1a060a110601090e011b020d081f090c2304170a0c090207030f0201050c09012006071211040506040905060621010f0803 71
    0x40c1031352810041ca0b00080051820040498016840300455400b045052014101c1210180c000c0e00a0381c1d0412240c9003101c0050f8001403c076441c2101c68181541580501c402c101c1050798050f94691009206407840000300e403120020780305200010030880c0031600420544000d6100a0000079082c1140a42d07100c01c2404a0300180d0002620782181171280040d5900110b00190703961119604a07501c9040200301d4120945d080e80702d0016040460b80200340c418030010407250003080c10002e04048442e440745110b240c124009164040340050401c0c4944001e8641c07088151400319503541c0c184000c2e411003142a0f02042900d16910110390042c0207440c41500840c80d4646407031324100c015124040c440d81c41028000d5021251882c4120820006001c2c0003d41c50b0304036115480b00d02c00042d502c1048000424860501080010351201070680b01a41c0441102046507070311807000c5007035801b42c1100c83c040040ca80c01c100350f4007016507482c0d43c141c1d0800000c071030580f925100344986d603224280c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 708779343 1250 708778093 708778139
    0x3010c27150309230706122a140309100b06040b0d110c0d02060a110a021002091207030803060301060f03020607060e0c030d02010e0f07033305010915 66
    0x240c0c9040300180b00c0c0c3c0c07100100502c100c0d0000021610440d507480922025070140400e40c0c0305140c2440305e260000740b4200c280102c000305210301182c06041040f6000405040621206d010b20348a02ea0340c0500c004d61044c801e41c03910725459280a03000c866880d40c400c41c140b140c441c6002d2058001c0d00341001210141d60b200411580b400803401c85040041201c0e111240045d10107020810001d502441200d0154560368020a5181804801d000444400c00c1224543c088100103840005401140d02c02403280c145c0d0006840f15a10800305642404240820b031540c040e041001c0104031001c4051809000150f00822415469187e1284000400c0c00069480b000501100c00040c0d0780360803100320914040c003551616000f610101e0b14104517a000000544d4603070000001d4601d00b00108005001c0980082c070701d0034655120314000481702045159903111040c02c1e00d0100d06003410320a003184205200300076660f034409000004011502600d0068040c0d250002500d210311a041810800a9 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 708780593 1250 708779343 708779369
    0x20303220f2618010807030e1b031227040203071b060603021309060b1905060a050f180103050f040201050d020a030b030111040e011e14060903010c27 66
    0x1500d8018074244000d0b0089800041410407400c840c8110001e480e186550310759030080c07044500005407003c1e400401c0e95081500d070000c0034041d2070b4001070b080e60045800400c4402c400440b4007003410705e0186007050005540c0000d000176145650381c2e070428459840c0504c0140250601e08000c10382c401540c41c080015500c2c80310f12074007400f441d400b480d441d101d07030300001d102960b0b030b80415000d5200c1daa203d640f4035696152501440300c203004481c1581002c85074105044000601c03032021040d9800781c180920004120001220f029404980c0c020103c000c4490302d400d0403030800305124241014550000b400c29012402000180705054003880e816102e260402c0e513081001d07070082d0800182d100c101170300c44840850b217481c01c1c41070400d0003d281e10b615682d54100180806085010713404600718640d00a400074410440d060715a0070344002010b100b02c0203060400040f614040c42c80100e6040d440c161000003981d810071301030502c1701040b04c42d08001c4071100060301d4580d1900e00c903211800b011 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 708781843 1250 708780593 708780623
    0xa020d030b0105090415061b0215091903150f1401090c0207050d060501170d050a0e04111c05060f060403110d0804030506221101030903051902030322 66
    0x9030001c000c03040d41803400070b00300041500060103a07404041c01c1c5004a0003031a0501440341e100206610300c005440a01d41e843c00341e54081040465140c0c0b55a140c040003040400c4580c0d41e04641c810080c0d403511000189645034104280c8203140705074401c0c0400c1c942181e18414100c40d0060050f50040b44d000400540e203007090384c1000c1c164050700030046000705007000c1420364400c85040820f501810b0b0001c2d4a605005520368007920b0740400414550180708241d01190303008088801e044030b180f80078040f1400c00000700d0040c10300001a05829900071421b402c000e10070441815140d4a0342c0707400e2086448207810301c01d035941085415500848204400d002040c41045010304030301028191150b17509690b00c600c2d01980090b00125000d400440601c110485915002c4640c07000380d080c41b085c0200c0680c1d58504518940f288141891345840c502c0c4285400780c1d00341c0e8400d200c050b1007080243c3c2c410000039101d910456403103070300551141d40300c10680018800f0b1a071403944081400032401e0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 708783093 1250 708781843 708781847
    0x100b01120905191713090b061201170718020a1205091e030f04032906060301331107141513080706050702040507030b060d09060b060301080c0907050a020d 68
    0x400784030a481d041c0c440780e20300304e420003148020841e2440c1401501861410150300200382c645050050303204000a00400e140040c0a480c45070468044040108a4003001c003012800c12184e544203060100004030840b865001c20b40080240e20460780c0c070300048410702040d1608688066072800c2d0f90fa4007480751000f40c0401c03851000c0d070b18100c840489040805034807208100350b0150b001107032001c20403003602c10030708140304d890310304a05010140c600920f008004107409000510441101d0003c019140c0381c01b0260451409542d82c41c80c210301070807840d04502030310152101c00c03040ca183c8100640021f01c49070040c0d041c04825001081040b290754042003c0342c540c0c000344402c0300d0303254002c48005585241003000e0001400580c4405031109150b004105c00c88100514241c245030621420629070341d5400201d032518040c2150000d91300010f4205600205803095102c0d8000100100110b00860000340540c448002110b54260b190f450000c1110540180b04d540000b5912002500308814 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 708784343 1250 708783093 708783133
    0x907050d0b0109030204050414060c040605190c0f0c0503070b160b060102071203020a0b180a120c020402030903070c0618092007111002010212040609020a0503100b01120905 76
    0x1105142c90070000b03480745c0010301200d209440c1143d03106103500d80c0216006040c070a2075072080d039500c18282010320740315018045100300c140c500c024045050140c0110f9005000c0907020603088615008034403400d25188884204501880d80700b44550079000407440c1040742250081c26409004085001c80c039500c40400140190031581907019480000c03440032807600324594168025801010111031758106002e0021015002814020124000d01d2040340700003102c180d62580f221099010581a074021541d0039031340304000b948180000203105120b1800800b800f6205d01600b590401280d03582000d60350301c40600c1801000811031541000f118400358020700036007001082940164940740602c1c0c400341d0280c04101d4018201c000b101007281001100021000030300d000031480c003019001c100c900d04c10004c000420460303c0c1d1488000315156a16400002c0c04007400711008440d960420101510b100110207000030040c0c200e00c55103500d68096280340c5030b0042d0141c04aa25440030008420f = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 708785593 1250 708784343 708784361
    0x60904020306040b13090606050d0f021011070f030b010b0a0c0b060409020d030c03170c07140f01110414240d0902060313110d0b06010503071107090506010e0907050d 73
    0x1959000b5180c0e880d2202c0508989403443e851000440302d40d82d2510030210f403060380140b40100303140b10b01c2100248030800044070040d0101c0737802c007030301c2c987c0c00c4211540c002040f03400340345000b000e40c00034030346c030340c52140005803807081c0804c000b40e80e2101e482c0103030b5000303a2040100091904801001142240303013540e40204020300041000603075078010500070503407440111b0015400c5501d07071080c0f55009441440c51480620058481d00700041d000000b4007401c0000341c0007007021041411580410490a250054000028070045035501d4201c00144c200744074180500300d014120014a250080d0f00c0340500e83e1000101c0140d0b03081600c2500c0b00c0d042442400500c6564805440169540001a510802c64000d052980a025280035102441408102402100742074040400a410044407603440042803a1480d200e95514401300c84500b01000500401d004810000c07603200f4598000d41d2140d8800c3c2c0311503480e14824400d02c15940c1085819200045090206121030a440d40202c3e902c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 708786843 1250 708785593 708785599
    0xc01020303040f0503040f0e0a0f0606080711070f1212020106080a140c0d060b210304151b210e1503151e030118050a030f0c05010f050106030f0209060904020306 71
    0x6c1c141c8656103440ea210843d0081115001004200146d1440b940a20000324081000c280811031918101030004040607002800b40101b00d810800c00183c10040700b0300138070998082413841030b55851052000780c0d2414054804fc0f0010241c580a1401402440105c500c81002407103c0e06958448440303170380020b80341c00c0e014010046848120b94401c4c042c8201035008a4001616452000030007008111085104004600c4da8055041041c400701c2034804466008800202c012a94103003201c4a41941c659420b07100309003500300c010b1010700028200820540440003a134004110001e49400e1440d0b101c40c1d40c0b1003c1d4880058808107200c014540010314140369034003c0c100c1e00006680b00ea049410b15500008000c8210614a000d0140c01144a0242000d5141400ca601d50603250258401c0c0a41032281e01c08804010318865619003200d682c006008002202003c0314070741c0500401e01c0349034000380c01c0c000a001451018400c65207802e00c002c1c1aa45820004011300010390001040c0e954 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 708788093 1250 708786843 708786847
    0x1080712020a020c1009030201051e12070c110a0509070e031204030b1b040b0315032404021807090909020d1a010f0e0105090601050c0f1b120c01020303040f0503 71
    0x4090310031400a40740ca2610b980107000b003a0b07a42c406001c505440e861000040000301c00c4d00f003016036048401c480312282940458031000342c00b03400c200124402e10480c0408d203201e4404010009600032036840e100340c864a02d0701030b103410040400c0a2400c00e80182c2e81d0005240c004144c420b8059403082401e02c1d0301400355620a19800f1544116400940c4207813000b0041da01000000c1c085030198905030295088400c2c113050500811142c0b501000749841562081034000c0841a038040000e200e40006506000558602c07100c141c0d0703034068054504034002ca0100300d803810480003140d40d80d4400e40031552074a000702c2c1340c00c1000002d4890068240c0c0c20500b1000101d0106600300c0944515403842c00000c5020352601341c140140024a9010044680640c0014803c075900c914440750081d0702407030304030b441c4e01640c0d421a0414040c0f00d0514654400d900e5000d03040d9022011110b280d1108032110301d07424154101c22515412811080c5005070420400a00000c0d00c41d90a44005402241128 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 708789343 1250 708788093 708788117
    0xf12060b040b0a02070e071b06021309020703030e0615010c080706020a080f010902040609060f110708060712021801110a05010c020a06291c0b04060509010b0a06050306010807 77
    0x6015481608503960402c000118406025010400700000707103560b507110015071070808001400d841400084800240030a06520140652a0142e0781200410490f1103c22942ea52114001394032040e01240400c2c2000141d035103d41d804030f00944138a0350808842003100c104401164160172a030401c442c2030100384800b4012460a1024107070680550b00c031640070f03007080c0c1c0251541080c143e101000d01801084184152644282d45004584043c00c142414a20201003500c091050759050300481c403600000180000d400640700e40a80040d8603001e03e501002c2106006a102c0ca146a0b4400d40106005000c1c6502c01c0310442e0b8290082d0050300c3d00303000075956403801d460034030b5000d00c0160f1014a03004144039503403040c83d022066500120005400c1d9116240500307a00014480c407504441903800581503003803c22940d21a44140c00c450036180074503244004200507118520298a40300011125091a41a4005840298079464150ba654400441d01c5a05c01406201001841c1c200c0c1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 708790593 1250 708789343 708789359
    0x10050706090f0201080108060c0f1c140402090c040f120201050c030c0106150503070e040b011209081b01060305030412020420070201020d14041202040209030604150e010203070f1206 80
    0x1407280144100c050310784035451030000429946040c0c0148000350800000e0003440003200e0100c42c03c500c0c4450300140c8416004100d4034101150301446104d843c200718400726420002041c052051b8401c0b0349140703154940300c903102c0881c0070710700448006844040c01405541c1c180480c00722010720501d0b240b13183c064001702150030340d00204500c019681d194442032103003070002071250088000300d03e8003504500e850080103142030340b401071043c001c1d90341c0d03103038210030364441c1c1c442920b080780e48001800030400350700e00703e0403079441101b4003c07170303049900d14125401c8011701400080b01d411070011420b041c03c1c9000450302d80c541a0080340c2c41a034070101c06030a0342450070f003079201d42d0320348900c0741e11100030340006814000d018406c101004050707016064124803050a443c10782c0d80380740314625211998400301e8000c0c415580c10503418401e00041000b00000d01c0200b00221f00d42d4034090141c0603552403aa4243d020079564200429806802da14560307205843c0203071941c003403900c0420380d180da070040 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 708791843 1250 708790593 708790601
    0x1091d01022b380301020910030506010c1205040f08070b0a1d0904030e04140106020d05070303110f09131b08190903110f0c0d06090312024510050706 66
    0x91502c15424407980c4807041c0403100310f807100010a0340250700d008902800a400710b4500c03500042855a0340000c51440e911460390b4400555210600c0c02c1000ba000002902c6a0428030440c10160718400012507115404140c03103046071003031442c041c10003285120a0361400c140d084a44d14205030420f61002d83d90b210032406004501a44520601c680800203010a4404803110520074880110040040990000342104104042e1400030f8440c03210b490100c0c046c2a00c40242d624040010030700c0c141c0d03c1c0003e802406e281d04112000c10600d0904104602a078030132079055200080c44c0551700d032040e4003030006550700c0051500711550a260700c0000604032003240030b05600090360410343c40b06800040241c422070340c1c0305000400d00400d04200060034a089198010001910750051108050041c1050031400c4800d490541d12800010050000d80036021640c203102d80c0003501c4800c81c00710341240f29800c11042c1040041880444080c01001c40014100b0406c005042041c2e502003100c42c85 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 708793093 1250 708791843 708791891
    0x22503030b09181005150303040906140306041101080406240608060d1e050309030d05070317071b020a09060902030907060306080303040b061801091d01022b 69
    0x2000118085280280010100000d000b4140241c185040d602d1107640084c00422018000c4c01c049807550759440140648010f05850a4051101080100d440300090f00101d0541e038a640284070341c0e540100425640f40401e44000d0020f02c41c3c1118074150754804c0f80001e41c814003e0360041401882101c05810300c00c0c7c168403891101c0c0303c800d424054141e20014a0b90003500c100c0d910204424140c48500e4029070300380070540d050780240081010442e043c410345203d681c009080e40c640269101d4003030450750040c541100002c088206c0303441d00b0f0841034038441c0906001d94990919200e644040041c800507003200303030b9007e10070303900c0080d081031039000c2d40c3c02a011004d40562a82050f51000c4d1500714560018420f150074103400f4012102c002040c0d99205802490304242c80d1204400f0885402c0c0c803024424651600302c00100e003e980079040200d51081d426151352890024a07410340c200c1c0203a503003218000943d08100707000b40c00b800c01d0500c0d4100c2070402c0010000210f5a140f804810034003 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 708794343 1250 708793093 708793097
    0x17150d060b240d0f06080604030207080111161104060915052d01050f0403020315071e08070c0809030615180105090103061d0a030e0f0105090d0303022503 68
    0x50007140e91030804160050303144810059a4030418191031601d100c0307000d180a58074545a035040d031072161030074076045a40102005016115903041c1805d00135180d10305405103a500e5806d25440c15142ea86c0c5600b10341003850008030448454105a03640009414010790b0b0a0744682c4659001c0360181e510301c914039081e80400c0c1c101402c6440c200c10300220b180100803030348911243e48010341c42d55541910151100009107485507652002c03140700c01c0300b8040c5800107500343c855032940712440348116005078040c10081c0c507406000000100000c030940f000e5503006000030300e07502c04119901d0142d1240d20701c1318071a0884078240703203560001c6803030000101c030300d0049550482901c8809040c80c2a4407518182010998041c643c1050081040610706202c01014669200e10070134840b1085942c0c1070079030b041041500c58102c01824010001d802c03c80003584100181000d2104075030054040740e0340c9000280c800220341c401610207134001c0d007148294848155508150170342c0201c1c40c1c40941030b0207200c3c0e = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 708795593 1250 708794343 708794351
    0x40501050a0c020a35060c03040f1407032003070501050904060824070809030301030f0303060902070f06060f051f030e030c06090d0507030c0209102705090a020117150d06 75
    0x404440d500d210f44002c544110381051517500d401202e400316100c0d86c4283c0362034440d030b81c03a144d524000c03000c3c1841202c00342c01c02055120041d15101d01044080403039028251180e10111540040e00480f4a03c01180d6459400154200300c594096005444842c034000c1000451654420151b03042402c0e1000440e05081800c006601c038050007601035030008510700d843e00030352030403001d010794910041c00041c00e4600440400020540b00350081409070501c9101592124040d01c0d000840f0101c10104441c3c0c1401c000b0040f440200300c0708004c080300e84c01401802243c8251901c00d506401400250080548071130414103000810401001d2a50b205402049a40341400c1b1043c10004a1602d90301000b00401508000c40d9020f621050b4007130301201c5084040c3c40714a503840d07804a041c1e0011406c3c0250b502c00304c2c1c6802600c2d6840f03081303100008080c4030356a03442105603241e8101c00f5000340890101ca000490500c41c0e030551983c81032003191006500061403000903031119503500111421516 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 708796843 1250 708795593 708795629
    0x90a1a030d020c040c02010605010807050d09080a110106091a0103020714070b0d05060a1a0c01061809350a020a061a040e070501140a0c02100c0201021908040501050a0c020a 76
    0xe8805c08850714102c1c80200140c50030000024a1000701400010811001080f066040ca000e6403114291591001c0e0f810355032605620080c00f07100c00c14034103104651038140006078090490065004c4000c003003110300c00070f4402c40300540094000303000540b0014039034182580c00b0f500412404000d0f00034040c2c9243c0f100221100710301520390052181d8010402418100078214805c491140a846075031081619949020f952034010840742c1c1c001c0900000b500e10b00c1b0100101c0740e102c1107e860081c040c000304040c55807805452074500314082528084020044002d0611200140c8070a168a2041d074011100b6500c649046d150450340c046419003400b1000c0009180612034000c0c124100d03405081c48902e004006009217200040598095030001016070300c0d103100b115504c680300d6005205024032896810010100d000c9131400704d0140c420346190304001c030340118030a13000340d50000000e49064201001101d503030300000115000c3c04000d140c0030005a0f507100f1414040c0030500f07191016405 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 708798093 1250 708796843 708796849
    0x40504061e14010b070305070204050711070e0c030c07170f03060f0103090b0703050901060806160f0206010b04060c030302040b0c0f0c040e06040f0c0b1305010e040b090a1a030d020c 80
    0x2034010780290720514204070703003a00c02d14624003541120000e20a85481d0403c5050a07181e034414404001e40c45031170801004101c0d070f00a519503500851840480e40b40e5612880307802d4051500382c582524451040c80010810202d1200528030320b4402c15414900300189104a074042d042001600700c3d112011042103102d0420410381c03101c1c001c2c24a401c1c0000001e07611180b070010009440d00c801c1649990000e40119800d4001e400100009030850b5140d2400b5110845480c1d400c00c0103900051440d80c0200c480303440020018107079145100e40524051400800781c0f41d052609000b2010705800303120006030400300034040c007105180500130702031400f040f100045c1400060000148030790314241c5201100040024150303801070b440030b818035003680d41e41050b400f082082ea01501d40b041000942810200490a1120840701c082c0c0b65042d40c0d282500c10001a80c181c5419650402503a80c000340c4548071a0300305541c11542e460b00c03081900369900109060888610030070015901c80758442005007 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 708799343 1250 708798093 708798131
    0x807020102160f091119030e0f1504120e1c1703130506160c0b1003060e07060906090e0a05181905060c0301050306010303140c0706080609101a1804050406 68
    0x503829822584c46d2100c00c105a0b0808625403001c0c20800d543c5404000c5041c2041041880740901502180d401040a807070391701031840e04407011192114400310442e5250300481806400301401482100d1141c1c5444002040c808501c0e41900e04956014400c2d21420022004500941400d01c0d0403c4400755801c201e0314005002e04050991310f005410315410951120041c0c80140d4401042591a1a0f69441ea01411a0760b0800741840f40341c024400420f503000145101240c10035140c5da10b0720382d51080140c40c0880d891158810b221100303000100003080940c001507000304000800f40018099506062405000800100d01003d100038100c05201d41000443e51005141c1c50f000c0c0b44d98100130100e40c80d034006200040c144052822100c0b0228005019100300e01c481d101140c4481d513440b03100070245a41600e010340100070810100d80211880b5911409940034403640f150525086028112982e004808010000025568001f0310750b54074003030203008178018400803850351481c8101c0c10081c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 708800593 1250 708799343 708799361
    0x506030429270f06070e0109030519120306050306070302030a1506090f0503030f0a0810030b0408090a06030207020f120c030a06320103020d02061c090605060604050d0807020102160f09 81
    0x43d500c0307a803030804801400158642d02c404d06250510f480e451000c0103a40603145a00014001d0160310b032030b418a80083e05820104a000b10603050880300301c011f00354202c03519806481d03010780244001902d40c9000e0703002550004d850010008422034003103070152044196411510019495100030005003039401d080001a110440c0554079100350a8001c0e0030324400d0884402c203120300301001032520010003816000640d005420084a45050f02e0001c03166846280950301c00c1c42040c0000c200e5512034401c6d1703145240c0c080c110261030420f0a0411031000c0b1480c426210610509094840c2520b0601c40c2480903482900c0224503210b40c1c443c3c64402c05072041408525240011a900c0050480c1a117141140d4050756041e80554903400491518840c0700d1480002e40115051241042c2075030348400c1e580e6014040400007a01d41404100d1148964400c042e480316040a03400007140d4860001c0c00300a205004407181000e410555405426850384000b070802c2040c842040900d603d4000d40d400 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 708801843 1250 708800593 708800671
    0x1b0a0b0a0509010c05030f040317010b0d06060306061d0f040c120b030c0a0605030705130e06010207050114090f04020903010501240201050106091202010e0406180609060506030429 79
    0x15111141c3e04c01045c900004098088001d0068041000e250244c1c0c001c0402e10340c1c00302c21120541c0c4034000290281d12111000030900c1c0f030039000241891180c411101901e100350b039403601c11f00700c0000082900d0802403001c1e0388944628004000ca41c0c0710302c00c0400180d01034480000c040f1440050000b12040c404e007550081c0c01503034001140c1c3d501c1c1d4591009480c580e04025407aa21402e000725414054040600b00d10455203602184525480e90b015100c3c2d00f0903401c40c1d404540fa4001181c100300c50111580e001102404452214030300a0820485080301a00060070038862000107400e5900a82c480840e40c01030300c1002c140b09122140d41400c00790380d8002400203500d0041c0050034550729105514510078415000d90442e84141120031411740010001d0191903100c0d030060301c0c4e050290f40c1c4244098a0400000342d049181c0c05040c0c1201c0c0700510103419940c4a454205480a0b48072426180c0c008a496918804c6440060280200b0192006c4404100c10302c820040f450301d19000301ca0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 708803093 1250 708801843 708801851
    0x504023105090c0f0316023331110406030605011a360a0b0301080c03011503061d01061409090616050d0f0e030711060309030d021b0a0b0a050901 64
    0x1c1e840d0400300316900140000006c20b91507002c0d0400f02e00745240c19000c0c503401444290700c4d41540d8000c2c6c010b030344542c81d807800b058000e1700e43e1004076000d8210a1017078800e14141d03041141c207801c2e21040c0c1445090107510501100c000b45c6001a00300c40aa400071110150b03a0170052002801000214001051100c00c0614007112141c06074915010640782902c001402c0c1c3c00309444858041c81d540303078800007400c00344000e42c94605032285504240192041071040029041c4146014050b40490340405621041c6540c21a04c944003e0292110407a20181701c81d008083d0803002442040c0c000c00b034100c203c25000d4900020400d1110000e0200e0400794800c400340650381c07008003810184c56a04e81030943d0344030f105d00501320240845d003804501d01450441100c0c0d02003400300003082036074800c00c64000e04040400801626001c250303400c8186a1080c411550369248990003040d049032000300e0320359544202c252407450101481c004843d200d00a80500401d05491f0142a0b00001c480700240 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 708804343 1250 708803093 708803107
    0xd0e12090d03030f1514060f030c0307020c100306052e0f14070308060310090c090209040b041b08010b090f06180405040b160801050a0504023105090c 66
    0x2414034040c0c81a054031454441c802034040600a0b403089400d40c03c100300c280482c0090381e490108280240c49404139401038901745200c1c600c0c02038212130011280310011401c640b59100c203115150001800c078000d5101d030420709002d50703480c1b014510b010b961070741e00401d4035410b00301844040901d0f03080704c910b00040c3d91201d14220b075110070300500c4020300b8a003210b41c40f0020003086400001611082c103c6503030001c3c1300c0e8203150f0b0240300503102ea03d080c0c00712a055480d8141d040b08803214444060b00072004200c1c14800400e180e0001c02002c00000c101180c503102a000017001c480c10805c1c0b1b10018040308403003828480e00451020b004200e881c40007410403103042e0101d91010150f104551285078000b0701d1403810444040034040f4544041c004200f203140c645801226420b0680e400080141c4940030440c1032449014494141d81000e800c0408407482c000c00d001c06504190804041851007925118243c0c0d5803100c1c0c038601084440f0700022171440d04061240a10740506074840d4001c04002031 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 708805593 1250 708804343 708804373
    0x7150e06102619050604060f1a0405040303200d06080d08040221070b18030a03020c06070f080f09130e1504140609060105040605060309031b1e0c0901140a05010518150d0e 75
    0x8180a10412b480c089030980e02c40c941103005021102141310400681c06404000d1059100540034500e80c2070313020442c1c903449000c1c25036611441040e0000003008540002c00500313080e11a03285c0c211a1014402000402c0802c0c14180310b20707074012400004020030b900c2018400601e0700c510390101903024220488990310000d44841038200304074042c2c0c02c005403500411954038100b640e03150b0000300320750305d90f06200c11044840e0b1113101c41324071500d91640c81002c3d081d400c1c0f08000311060220024030440114071841c452407800208140d4205130761425a400704031080c080e0714442d0f24240050510396040a00304400c40c0c41c0703500000c2c062070040c0100002010004200c80182c039403031010314008080003090928082c03900c0e80882c1c03005080f4642c05a400307400502c000b5150801c440c404642da8a5031600c6406041c416085503100031000c500300030310f50181d0005e12001010141840d5030705040004100c00c0c0480407103082000d000055840000619403182c40d0f030404180c405000654140c03000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 708806843 1250 708805593 708805631
    0x703020703120c0c031b05190302041a03030d09020a0f0b31080607030b0d0b04150b120609060114012307150e06102619050604060f 58
    0x30081040e1a4004a42e40d01806420140b042c0781c1c0c041010612140c80e4030f0469864030303400354068a041c50041340814145000d0072042c03940070fa0101507107013192640d000c000203000e41900c08102081d48942c0c10f40d442d1002c1c001800d0050300c490011078a01101e1040c030191a1a23a0700008a0361005e690500040c8074410407581d08880d41d40b041003031481d080c5110702081309180511078100304400c10004142c500440d80314408c01242d101005400c0d4000180040c02da08a24000d11110440001a000a59034180b4646054410300005005400040030803498110b101c588021a4032600c00c100c080b94042124a0241420b00095008220640c00107481203928450b900510052614081c1400200710103a919440c0c010101c94042c00305030b8a035a00400411314000e03040d000d6240003900070089100c40400321a500c81050000310005114081044411202180c0d03d008150401100182008a0105441c000c00c0070344554103081c909a421503580c900c8080d040790820114a5401d14507500c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 708808093 1250 708806843 708806849
    0x50c0403030c110301050f01080606010c08120a0e060a1d0c0904020111160f091a01052d030106030c0f030b06090607150f0e10020304020a120201120c080609060607030207 75
    0xa280c03100d9a514900f83c5400000c502526030150719000c10444000e0003602814102c8100030203803030b01c40d2150001140c08440e80e02c0e024200303041c204802120050040c242a41c0404d03031010014a0301010741d0003030f06200d020740d22044001c1c4c9a1600c0039168007100c00d001c07250024100100010b1586c90046112040014030181c188180791a4401d41440306200811400400502e2000b00d00d8640d501000701c24040e02500003203e10b402900148080281d56036215014140c40d081d01f4a0f01c0040940e500000040c1d0b101c08407007200c0340211240804501a5001e4405a10003040300a00340d10300038224810308105208060600c80020307403e407151400c443d42d02d101500c3c0540d80f0340c0c030341c1000d62a000003040d01c44566850901050140d482a80c0850078014098080c1d8100d10340007143c40040c3e000688001c0d51003300a1030400c54810200e0103030603583d1060422020000329501c14038100d0710504d5030000490080003c005052a1034800030b94041011101c440c14004161402036907111640 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 708809343 1250 708808093 708808097
    0x60f0103090f14030f0c0a0b07030c0917070e01030602091504060e010f0c12020a0c08010b0f0d0f050304060507120311030a050901060b0c1c0809030a030c0c0c08060f060103050c040303 81
    0x2045107940c8000f4011038409244c0707041411b94403800410503541e140d042810917100c03008083d0104000a00c24022064407540755512001d1050500180c901c001c821503202510621811000184c0b03494114001e50007940503040c0181c445c0810818480c00b040114183d504011042100707201c5980c02018801850000386131a03000c2041220003560810400000980400c0381c164041d402503500261a01c042c9100e441c144071542c0d901d503402400d880c0d98001c3d4941c0303c203248580f600d0a041c40868491040c4c002d141030040030055480303280c00d50340590082070001d8000a4640244001101012040c0c05645070411074074a00800100c1d40c1d00002d414408655200c00210390511800d40004000d404daa4030210344c3c07454800240c941d501d12074080c1051106a06d090041344501981c0c4152154414102543c60001ca90318110018428082030f80d09102d50903d007100410703401441d40c0040e01d080700c0184020f00341040416102e0000038072490401d400e007020440c442c4550410354046036414 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 708810593 1250 708809343 708809363
    0x150302130902010509040914010b0f010c08030c0d0c0c0c140904060b030c0604080c0a050d0b06190e040c05040e060c0d02070c030b130c120302060f0a0f0e06060f0103090f 75
    0x30b407004031520b10490170190760040c140003041051004e03281d08e41b03044464820003003140b40404400d1040442003440705034041041500b00130003050818004580c00b8692582c842e20340301081425004543c0c86081e0b070710000d0703d03008812081000198039240502007100c0e110440e602150002241500c0050000b46203548403114410651020000740179401c80003000141c503203417120b880c41d0340d03400d044400d1845100303540e00019041c202014014030490700018249142d585940900404031154a0110220682800001010441940d03020300031440b984035400c8080c42c0c1410803007592116201034190742c20640500c1072190842c0f0841c1c0a28aa05c6805130301c40d42a810690782165896101806600b400d100300030211207912544050107114241400c0c00544601c0003408880080c8801009a4840d40101703000c0b2101000c115482071040e031010030700f4003140c0e00c2070003520508801852564400f8062141c1071500b00703040200210203180c00c00012103661100f140f40703030780300001810075805c0c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 708811843 1250 708810593 708810611
    0xc030b0c0403051e100501180f020301030c05040209130c020607090608060108150a0801021216051e07060b0d0f1104020f1206010507082209050606071101020c210115030213 76
    0x6005c2c400103048201e03410400f41d80e4070310550350040d0307441c1d0320780e0205071030085280300d003518503c26281070325040074210084a00f48810711000f90300c070020803135005422040500b030301d203028010b10720000201c0c0c1c040c02079820074110140c076800481d001501407240c1e58081140c0c60741d019455503400a203040d00c03901662188004504404641d03008401d4550001402d024407503e408141401040a900e406d48142c00f0311404681a004c5c2d001404854548510b842c10710b5000f890140503054000c000004958854500065900c601c442c41150055010071841083c17015900001c8240e01094509503c0d1544241d1608068815980d81500b19400000410a243d1158096039036107035111b0705043c0e4400c00180c1c4481040c090003e403e201c8201c0e800c01081c01d02a5029480c0a468040e00701030034100f00d9501d0401001c942c0e080c0320304510444052018a50794009849947c800c0710300801c441507510f41642d405d486883d0050444800f188108200586488181c208181e0301c90303400003800c0799 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 708812949 1106 708811843 708811903
    0xf1812030c0f030f0b0621070e03070e0a06152102040e0f04030e09070c530703110c012a050a050a0c030b0c040305 51
    0x3210a02c070400d2540240c2003120752540300c541c00f18058a000001c02c041c0e403c4001c0b80d08074240c842c51700100114120020b241c0080c003a2400305c085038001d0021941d16080b030b00ca2041e007401c011000071154440e0754841006070886c2030103180044203400e401002010740e042803008444054501030080c040310b100310340498480000b00360465a444070782c3c52803504020415001c2c85085030039226580d803260140c5101e0480340c4c5030b000d00c14010f42030094401d51100c00e907100300001c40c3c5400c0c0001c0d0340c28100030848075029036014020010081d070f0300500c00d501e00f030b50102c8010100d480400c040d0420038103241000c01200300c440b00d00000d0700440d500c034202000440c04005800d01c42e800c514540340c65507034250144041300c0c00110341ea92000d2500f94018400c1d20b034940c11500030b00800008400d00c94004402c0c0310607074201030454945030744480e5031940800d0380d0000d0b00c1c9103a1480d4 = true := by decide +kernel

theorem cover : BRFrame.Cov 708633093 708812949 := by
  have h0 := BRFrame.cov_init 708633093
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 708633093 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 708633093 ≤ n) (h2 : n < 708812949) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
