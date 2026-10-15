-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4630
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:14:09.046573+00:00
-- url     : https://prove2.me/submissions/f9ceebd5-8b5c-48a4-9ace-2063120ba357

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 832553956 ≤ n < 832733812 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 832555206 1250 832553956 832553987
    0x60302010c06050703021e071101020703050607030e1e0a03020d2a0204090b091608070308040b070302011d0703030810050312030a0b03152a031302010c0b0a060f06020d 74
    0x3e160348414600310003910811054081c109070b41e071f80c04101703d000c5a0040c40c00d42e204214960076094000c005a0f05c0d0100c034400a003041d0030000005020303d01a81140c60200b01c1041600d0a90b01c040d10010781102107804001d071ba643c00f07002000c041540400581c400c41500b410444c0104400840360015030350410141d0700038241d05d1442c0d074215112a000580070f11342c0420b07070740c10506d0300d0340160381d4503000807400325072406503540d000918400108582003079a400070b000501c0c2c94180030101c466030340a00402c80866503100040e841140c811000790131400c2c214400380081c13928504005103c100007030a4440c4040941c00c0c100560b580024141807100282054240c030f030341e2801c2c8200d00506007940215050700a40c2c3c0000e081860b14009903202f00b8402121440c3c11098075070200f208020281c0c8414210000c10201d004000454140700010344145003800c1441c4255a403d0328503074055411000607a22814140110100c01e0040400b4006034070080000d41c1c071050f8000d045120085011 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 832556456 1250 832555206 832555211
    0x70305121302030c040f14041a010e1608071206030309081014280f0b0103050f041101080a0906021c140903070206070821071d0303030c0d1404110a0603060302010c06 73
    0x10140321489400c000311044540031071a4023803415040c007181c43c1d0703000c482d12603000c4082400403400801c8000001e005e201a580510550085004255010303100603005400b4090b810341008690030583c09000d020314425079641c1150340c50141d14614060210040094203810710900000c120428100a5030100420300400d81440c0c0e0682442030810480c0c1e900e0f1502410407828410003010f54102c148000000c2c1c1e0100165500c00d03410b010a05004c1e98010710079607205c030b000c0700f556106500190f0009054000019240c215983d100101d90080352a00421140c0c0c03a1841901400c0b441000001800303001c54925032f1900002d581c2d101d2080800c000c3c0306082c00301d00c0c242405070903821745084c600013122075120302451208146a040c0116107510004401030355800d002440242100d001c03502c080d0042d42592154403204c3c1240c3c200f15240000c10360340300c140340d04e40fa075408d01060160380036500d005c11904490081c0002903090b03070400000e06003000010130040c3d9000000a00c55500440300 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 832557706 1250 832556456 832556471
    0x11a18101206060503060604090f031112161403031009090302120c0c0f030304050a031e1b082505190305060c09091b071412070305121302030c04 64
    0x1100c0000049800425008011004a00c10865180c3c0143d00742c540803411104242d48540810090311260b81d001024a4556205880001c3c00b4000c2c021100e070701407081da01c0c0300360698901e071850340000c00d00300a1541001302140074480c500c0040c11507241d99601075403075844c09441d8010803a84a206020300315071742d10700d0385080c18804d10101940034403007080746586000c400a055658140c1c40d00b058030a80e1100c10000711032030000100c40440764050304180807180b45440c0e401d806000108014541c401030f074841c100003003801c00c04004640c2c007036032603109190400da40c141c070703011034000201c100442d04030300c07030365001607015000040743c500300c4400108016103d1307840304200c0c0340ea000905600c14481032080b01c0b00090042e00b1f600206036100f40907a81e415050105400c4946101d2401d80303410840d40d0045021108108464400c0804590340c0e11001805440c107035026000a0b00002c60104003901141485034249800a8688460501c0c0140580000c1d84442c14080507901c9a80d6a401 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 832558956 1250 832557706 832557721
    0x10e090705030718052410051605010c0f020d02060112240507030b0901050a21080c0604030801080f061906051302090301050108070b0f0d06050d060905011a18 70
    0x4520041c010103425036112903a02c5002018100078a150703146181d0900d13002400c82d1040c1c3d004884241000c14251060000b44400d2000c0c0e000304984d240108032040003100c1e812003c4131109101a440360000140c24500b40c10000e14501310301c8000000c5410050000c8401e40d0300080303950560b00040c1d4141d00e9041c59240100e410310040b860140350381c0420b02543c51007800740c1c0c001031188041e030f1030034003c0c10054010400c01c0030090060942c80710030f01c10148502110300d02a80810134030403514101a080710340f036021041e00554105034050344a40308200405038080c480b24010650760300204023106034101e48030386940380100b00000216005c5110714400956402100003000058498141e0303200e01040c44000c0d6100c1511507000358200000040e007401c0000c0c1503c00c507015264035034100000329110380c0380743c1e0100010703d0840751260400324803940c480c0442d00c02c040c0302d113100280c1004186007070307420340700000306880d0001000d00710600103480385550b100388a2442c1c0f203002c901c0e1345c8610 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 832560206 1250 832558956 832558963
    0x11071d070c20130504050d081006080a020a020f060901020304020a12080a0c03120608030702030d0f091208091302090306090c0105310b07060e03090609040504020a030803100f080f0303010e09 84
    0x483d0888640c00d21013804140320002c203040a48403540c2d031300c00841d60340382441d001c001e00c41c0b80308480000b01c89a00240da00901c0307602a2110000fa441a00c00040d0051003607881c00000f905d1039981e07170b5400020b00c000c510780040d520000301003000100c007540045803102041400303040d16413030510402c417410108040c400c51071401240000c0c0300c100501c644402c5d06541e2608000d004a00074498007400e40c20781400340742c3e104000d043d03d40d01d514260b420244140d602c0540340e0350803a01c2c0c1c0010320a11841e90b441400845001d5000c110041e02c500c03002080520b402c1014002c40b00d1500503050400569074440c00f229154183d100c1c0501c071000a150354034882d10840492902208508940032420b200c00100400540c2c1c080c0780c01307101400800d481039032644100340303020350700660400c008907560405800030350b40240000e007159107003540d9032103080700c0350300403903240d00c242c104081d0a01c5010304020400d40541900da0052070020041d00900d0b07507a11060180003200c0301450000b0301580c0082 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 832561456 1250 832560206 832560229
    0xa06050a081503060a0603061a031f1103070806030c01031109120f01020f0702030d180e0a0228030f02030f010b031b0a050d0506031f0b0111071d070c20 67
    0x743c125041ca24014900000800244c0070484440d801c0504100882e001c48034051052070005010340f0552201101100c400400c1c16401045651071f00c00c6843d508007400080d501c20000d94403610101e04d01841014203089501c01441d041c1890f00501c80d1001410704161085200103503080000001812140c0b0f1400c00c00c40030001c0c107980000780b5400189003400103401c850b803083d000c448800d0380441003901c1e041e441c00b203541c1420a55004c204291501c00018940100003010010319002054900b80654010b03401d000320304007442d9a140005580c1441100c56075146a6821401c5040841c1c40c1d10300080c040c072415440d804040086168030100f550390346000c86000407056503640103010003519640195889200c954908000900c06040216954128450700710420240c1006170740604000d0100118941c10070550501c0c103240b0b2241084070202a001c41c1e1001c031091400c4960301c040c4203400510140030800e00c13204040000d0114109034812010702c2c104400240b078000085604d00b41c0701c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 832562706 1250 832561456 832561459
    0x1a0d052d030309160e0118150825090209061602061201091e2d20030901050907030f030e030a06091103011a1026041208060a06050a0815 60
    0x410b0001040d400110103658101181c5524115135070740c0317101c4a0300700c400d10411200c00640601c41480720403070b6001107540c030910303a980c3c2c40940d1101d0481b881d007001105240013030258240049180b000034500040100b00f07010055203007010b00d0b008a04640614003000c0c5100440303541709030031035486100380c42c00c4410440c0d00225540e520f4402d0405405903400a030b0410000505101440c0d26034045e024074111071442240c0d54542c134034459010342c246640882c00c2995240141100c40c3c26852428440c030802110a58036410b02c1240f01d42100e030b0103441a0b44a60010f242000041e41604d07501001c44d405080c1606140301c0040800d060440e0150001d010900d000c084e44200440c0255042c400c0d08250020002d0701910158a91031175045140140d1114044001490081c801c00007440341c000c0d81904c0158004401880c9240100261000c4400194031000280450b80c0303e00700c0d03984200101c0300c0c00c00d80391501e0300c00f801500c00c20860104012021002a46540310341079034541c003000 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 832563956 1250 832562706 832562713
    0xe03182b021f020318031605010e150414030118020109060503100f0306060e1609051507060513052503060f0b10092105190212060a1a0d052d 62
    0x10074400a403691705ca48464402d042200314241c074141000100b4600000004241034a0141441d00540d016010945116400009106403000880d05100070304010403005045200d840f1050041600b901c1500c0950456081d002c4410070260b03074030182c05012038405d4106142d694941c410b410601d105503030041d00040150401c001304104165000c00300302c4140d20007090003a12505030900c1e0707a4510358030010004043d07200a014034034004081941820007203440c18501341ca00d07a1340d801030360b2040751050300804502103050288503040c0451340b40e88511150718100d0394084c4480c0069000c4a010190441c1d1766212f00c0c40c0042d417654004610b44070018500c0c15480d202080007444810075002d200c0c00c42402016602e140c5070482a00142c00781c0c0000500742c52407032103082840c100c0c003810050b40e0090100700262900310007031202c240079130048980840e246051000d40f0f44d07050f44e0b00188900400b9021414804a0b1011a1200e0103202c3c40500c044d444e056805a1000c400150040c00d0103800b = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 832565206 1250 832563956 832564009
    0x40501031119210507020a0809031f0f140403081504110310030c05030f19030207120c0503010b060307080f2802090f0402070b01031209090e03182b02 66
    0x143c010a80002c121580c5a140d24400610000c0e50141e038015030740640982c0c0810308600004440102810401c0400b804482150380c41d42c41345264a100b06030140f0a141d51803250102aa41d81e0003400758904411304a2444c5080c1568000c0c071842c4010442081514086014841e5a850741c000341c840c51005200280ca1f0309001601e19a41040c51004a4050b89400c00010707282c00c2c040b0f0070400c8038440d60701400b181d845151801800e10842d100480c114000c001010541883c0102c42c212460300817408040d10b241040c05050071070f00964285031103980140100200b080e0702210311680001854040303040c1b61a400d01228420340345820044084640c548a0148480a9409001c60f5001191442030000441082c80304901c64003501501d03940010b401400030035011b1296072400c1d0010714001e0903690740e4050781e408981980c080d440e46a000001c0984641110304100204031340101c40071210445050450064201103022140d5015030100081042d5a0b03200307c40c00d00b0b9051b0000400d50314 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 832566456 1250 832565206 832565257
    0x3021002030307020705040510030807140601120614040b060d030e09070c020913052802031207061d031b010207150e0f0601150c02041e0518120405010311 68
    0x70b030802c0f103a40e401072141100028a40c5054040d0301e0103120403800b00074006045884c0c89003650701c032010590b4018090360450101100402140b4000c00d82854603035180440c0740307041000d8501100610801c12880c8040c0804038200c0e03641c2a411002c01c50b04403c9a407140e00c1c09880803510400750035030080d40902001845500000d04564040c800c1350360f05c09c295105000f0101000410700c014150740c1c00100000d841d2100401c0c8090500d0160411418040135940000d18181041c244450080f40200d00303202000342c24003d401d0140b400c0309214501032038242c2d40f150350f8000c002d00c401c0d02c0001d54030345007101c1c0d43c2035040b9070000d50840400d411404e1101e1001e03029000c2e0602d008850301c501503000040020116299040e1500862500003202da015812190107902c2d40050743c4c0503a4070400000010f4084e103500070403e040c080081071901d030101440200c0b01e08040501507a802c0b088401c507140509000701e50550300300742000552444a011304403030034081c0440500300600f0881030700b0f0f801d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 832567706 1250 832566456 832566463
    0x70b03150448050c060606130e01030609120e010e04050606091804290a110c0607090e07090530060a09061505030d11030f0406051309060602030a1803021002 69
    0x70144070400603403045035040d90444081c4120310a5241076001710020403424944131009007400240144000f00142d00d620308428015001c2e0300441d041a039030440c40d0100603052038046555421030520f02034119800c00040c102c0007440c05c407944103076524000282c00ea036030001a1104490054030a02000e2039007110900c018030291420760f0311448030707240c0725541c0d2034401040880c440346480320001d64903a05d03e96001303460a2089040758100034854400d0500701044114032400d80313030381c3d09803800c1d00d054442c20a591317000d405241003100703011080c0540c0d1500d8080c505400c20759030404000c58141c40d2802516001c8080100241c001c8006004401c08543c2201d0001402040104a40040e0f0615410118801d1280d00c0c2c050f002088070204207402468041d801180c0c000c140c0e4606003003203070700350350f83c5c0d119070055004208080350000c28540c09043c0300703000c1c1110f0201004001d04002005c4d540b03002da908400200001d42e10040982d82d02d90b0400c1004580c0984000c03015039103070744042d45 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 832568956 1250 832567706 832567811
    0x7020106090c1d0901051e0607140a0204061a071b080f2103060f010c03110303070f080606130b0705070503030d05010e060901050a1206021b0304030203070b031504 72
    0xe11010f024403c2c0350000a950483d00e000b8844801d070900c0c4000117481100301c1504940c4404148201400f18010401c00d14a9222450142621950510400003201c5284d08801d1165452240e486e4681a145040364032264020345c14078119082c81502400325a410340100300d0a02074580c4107905504001066400c1d8084140c4580c3c9402c40d0341d18441060004682d502d612006e084202201075000c0d007a03d483d00c3e4003030720b00a059941c804082ca443c551042e510a000201c2c54000c2040701c2c1d038410a510b40080c4102e540c60b10b80580000214a21107407030180c91664080081ca08003000001c00006004000280c152a215808219010000d1100344203030140098044005150b5107001e101d554140d400007800c0d180410b05000510004040340b110172903c0075400c11851080f0b420401003001c00c13000d441d0065580b01c2c1035105040c2810384651040c0b007140c60520a2005050300e086000c410305805031400104400310b402c0304481c603003014019442c040010b011020910890266410 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 832570206 1250 832568956 832568987
    0x312020102040e0114030a02060309100501031103010c020111030412050c070e06041803020709050c04030c0e06040b010c0f02091b1207030b03030901090302120f0f1c0e061207020106090c 82
    0x1c50756031762001d50805201c40e03482000d505802c010810030051502501858100c410072048442c00385003c001d1204541081e00140c446204050380d0481c0e44c43c0c24003c0f0641c007041d620080c05440307503d410858481c080503000421060b94915007004151244003900d00c440e410400301c03043d460b543e444030701031540161016406241440e1036a80040000034510188a0b45a4014400f941c5000c030301b0001890301a04819000e0000c0000002080e03c1c423242030040c20150f0141801802d00c075040000b03c580d24441386050080c580000390101d401c4400c54546150180c0b001301d45a40c2d0522121506041c4001003c45503c001c645400c16059010381c4910503113040d01c08100101401040503030b24000c00c1d1019000074440748003800141400c108200507003103c00b003154003011000340030504054003213415040c0f40d44201005801118102440e40030104217041a112805201c5c0200d015445041204102804414086040507200b5030202000b822600c1d020800c2043c62a00149403006108901 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 832571456 1250 832570206 832570229
    0x1b06320709050609091501091205030903010b150a03050c0d0c03140907081207050c060c10060504090201092c27060c0a0c05010b0a0603020403051005091015031202010204 75
    0x11078203090901c1201c450000081048a05d83c0c0c40300389030040540b030180b40b00d04001161400042c420b800c0b20149180d01d00c108080c5444080b54005d15084448a60f00715109040344400c0c0d0b04c50816000854040c00400c0c5400700d02c680c0d90881100562094514440c03d892030805480341c416403550169400002c1c15078640e03486c1e100d0710b00d220354454050040d800c0e26040919080050307a01d40c1c0050009620580c00d0340c40c0349c16110002002a0444042420342e80c2081d20081c038924802d2040700c0180c00700300c40130000351841ea0002004a4900d000e048205aa8445407601c1401c8100b0002101079140e005042c1600e489807061200310608548103021549440103651801c8010490603c1090319902c0b40d8140141000100d0b24552840b00079205d41d540c41504029940b80d0040e070b4005810705440150381d4a1440c81c4c020f00d412207180d4403002e40d5207040240008400082500c01803200460804100f030181c0c2e08410360000e200d42d000030403403007070741a4070075610b901900904112080302264 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 832572706 1250 832571456 832571459
    0x2490605091b0d0c05040906060f12050703060f090c030c1e050d0b1b030a05010f170604060b1912020108090d05040308070305090904061b1b06320709 66
    0x2050760703240b282403242c1d20b1003035107000680307103050414481001d9070003658042c10301d03075452010030200d8039911003d83d0502d40b2a2414000038040300031840041170b510f00c00d10b00c850b01e02d4503a29210b5030385000040400d61039200b240034030f04854020030002900304401c2884181d81e45840a0303180c0e100e109030724460341c014103d4444448620910011240050110320341d02640d5603a801241200904143ca0140707100c6803088003480010103544034060400d4000794950425011044144541d40103540e804541981409545008582231340c1141d03000002041c0c00200d00300240d407010807076200400c540321215000401c181c980980c038918600030780b80c0c4540781e114002d071079803030b02426800c05d400b00b24104400c02c000b824140041c141c45002c0d04d4031604200020002450500d01a00d01380c4d174007500c1e5049821120250440c403681c203045810710f1200440780d1a04181514504440039101c10b596031000c50407914904400900e480444038103a07003e03036240140303050302d4500b980c0020015888140 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 832573956 1250 832572706 832572721
    0x81308060703060b090d0201030207050d02070e010923152d030304121707060915060b04080c010c1106160c081902040e0f0f01020406030f02030402490605 68
    0x1405064070a0981342c18500701804050008400002c4d4040303040540c00c03c010404203406004c0c0907100a0143d01400b805071501c0390343c0c2d0042c91306030070003103d8a01e030200500018202d24010140034844640400c49a551100100105090000381075044844a92100a070300e00c19103035090b1046110f42c2c42401c51001c0404d16549018030b003d01403142d24600148004103002000aa80320150b004c1024030b090403541d90203043d41c0c00c080d02207503507a86078200b00c209110580582c2018044500071641424580300e0100c0ea075030085010b8905002c058091103040c0841900341d000c0340b850140c40c5944d95502c00080398003520b160403003903483c1c51300a84082403c04010030304100105008441c01804405602040b0043c408000001010710840c02c0803031084d04248640c0c1007a400d180700050b00c0740d1071f14030b0240a546606140a542d2481001008016605c00d00b01000c0300f81690000300b0241c0c0000011890303400800380d12040090100c0010030010358141c3d9046009120340b80600540e158040c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 832575206 1250 832573956 832573961
    0xf041d010f0e1239010603030c290705091f0e0a080105130b0c090405092401030209070302030912220621020c0a0803090607020c030d02120a0903081308060703 70
    0x110540000c00304121074090102c01c010304c0640940c1481000050b0302c1c144540608490b01039204a0110f2410540d0401340003040d000868a21034058207800d180c1c0c02c07650402c030303124402000c0605002d40420100e9281c0c8408074001c51002a41d603415000d5500e0070300140c10084080d044c540300c0c2c850a50080f90180c0c040c0105401078034111190300000e07a507503403a56100c00005011843e1000d0a1050341d940d40e4a034080d06000c0d01c031000190038501008880e5840203503070901c0060b61140e10710010001a00d40c0e98555901902d54900107840751941c6071420f040220400c1883c40030340000c02c050000000398840740d21546000c8000c400c080796a1070017555200d644101c4000c144d0740c40c9520342c88924164005002c0ca882c1c078020788600417150b17541c00026400039a0b40c11000d134006000c0040f641d40400c003601c1403280c00c9004001c00070304200000d54038156000c40d5a01d11401180035003109000d4140303c40516031241c0016102c040281035000c4050541c40741c035050303204c2c000200356094080c1c07 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 832576456 1250 832575206 832575217
    0x105010f0501021501060f3e01020408100c0509090f0718050d110303093f03030a0230040c06080603070b030c1e07030306140f041d010f0e12 62
    0x188030784d8507603a01c2c159003070340c040c103031400786130705002070125880079252844c144800110054841000041850a8104007502061b849519940e2041000348003940000170030120784250b0358408625400c490f02c0c1100c060085410103a046400c1900703100c20782c04003820091103034025646603041852140e0514331851307401c0c80b842c4d030003501109803c8085103091440e041c0300a40542200d1030001c503030010805442c805d600c0c0b8500316850f02182c140030703078000d108540b02c80d01b07821007400c1e12070038803255030303224400a4031038501540d002172a00700d2030007025040411a444031150362140204005810008503044030704466060007082c0c085049805183c90900408014008020490a204944505500181080040c80024400d05022400c0ca261400d0050000010540c80d84500d00d8007506545a40d003042c4c0ea0000000f4082c03025843d81100c0c40e142000c100d80c0450302d072000807651100c200e000e10071007020b9401c20381002a40d691540000b0401152841151260302c250340e8000102d0160 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 832577706 1250 832576456 832576483
    0x71b05010906050928050301110a0e1e2223010b07031404060f1e0c08090d0501051006142d040801021c050708040f170d0e0105010f050102 61
    0x144081400a584110701a1408100281078882c1100713000c003060780c1c0b1720145040c0c0b55041c0d011020900441c1802c4c050366540114021a180c00c04141c60006404008480d00780c5001d4250b030200641110000b4014012482000e8800740c11460f042480503102c1800380c48640702c041c1407002a2443c220920540c60701c10340020328141c426400c01d00c1410300790380090400e0701040f491340c0c07030b04058900c4400100001c0c561620b500859480d06840581500d0f418a090f07461003031a01424103250350030000003000c050b40585080d94803074040340000e184800b00080031b0b01562800040144802c4023000031020745119455502009040304080a203610548200218103000b030072082200c0058241e0f42d010303404484100b18101901d420000307089030800f2800000b4000d0700d001c0b00c03e251486110352604207841d03180a40d114646074a6042000a10744001011500c10414843c684408a800d4824000c3c408109008120a411420340030b01800c3c06030221001003041d00242e59800050903040d440e52 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 832578956 1250 832577706 832577717
    0x141e0f01120f05130201090f080a02010f0302070510050f0a020a050904020304030207050607030903170712080402010207090f02040815270a020907020f010e01020a0e1c050a08071b0501 81
    0xa52401120304038840900d1103015502d40c00d0600000c0c4450040f10711520842e052100e4080c3d040c00018408120b5900010007903580607014061000085a00d030b607441d80a003020300e14001c582c40110300a118004018060f40101c03883c42001e10700d16000710b406180c18051070085030301c03048440400c901c54101070b200455402c1003e274125044c02c3d0040c540c4140240140d4540c1ca94a13808941903601c01e00c000c40000e0030300c0506204011101c0300154070320b07159044c0d5604040442d9109819404041402d0040c41641d00020f006c5a00c204421806020f10803020b014051203900340d00080d410500524000c1d01400360840d0104c0050894244900a07441101d440c00c10050010764052424415415540c0605101440541c0b1034140142c0075800c103074001d003600c01220700c8003400c5032107010002540b640100003d001d016444544c2c1e91b40610200d03180c030710880103145e595501d1106084000d080f4001ca58158007800307281b0028200403402180c284154040c028240300401d6000d02905000c201c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 832580206 1250 832578956 832578979
    0xb120709060318030c050705041b091d0c0c0115090c0e04051e070e10200a200301020417010603030f0e03071203030902130e07090218040c090f141e 65
    0x20700c03411040c44400d02406c20b54800c1612200407c003a20380c080f040c604081e0707096448410141e40a001c0400400c403420090071020344401a41500d007901400d02c41d10050081400c491054083d840401051501e050546140e80d031016194042c0202855050208007001d86542c042c1c20140500340c4100246003082000b41d58030502c40b0383d150030203001d550800c5503694074012140c0f07507414a14080400c0d502d4480d0218280548071412144203025007049410904003100060310300308540d550201c1845440035080c2d00000800d00a0107964000441b0010441c0041076082042d88028241c80c0244d4459201154068043d9080002c01d130b0740c0c40e0503500080041080310100034604108611910f8007040c0c1c120b5075000540d1081440610f4450240c0e2002081c06403001006850010100c02d84158205403403507610000c81201d01c0c4030303d4011034903580030324912449154048060701800714420300503501c50a036050f1a402180300b280c05111034a2021400c080100802040e030f4100910031040340 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 832581456 1250 832580206 832580213
    0x411130306021b0d03021206011e0302030a1806150e150409020a0528060f0206040f0f0503030103030f020106050604081902040b120f0c06030402090c130b120709060318 74
    0x3c1d40f04040b440e846651141140301061028001c01c0c240103401d13a80942c4070562a00c1003a142c01000d0191418001d07c1c040044113000210220701f5000b500f03003001a180e0381c83e2507020f07000e8000c01c81181c20310b241d8140841c1c10003e25038440a141c00e01c4a02e1039607101d40750609100300303410503a90400301d24160541001949003039006060742c51720103803d44420950795004164003110036007201d40300558074401600c1d14042c41d181080100301da0310384402c1000c400c520280d15100d0291000d45652281c005140034841d40e108464141c90703000cc1103c5e520f40c1c4d6410028101603020b24803600650030550700140519109056405440c113450141c04600000d00d04030b400010540d0003246c0041e00d0780c0201481d50740314103481075845451009000034500d04144a41056050705420b0f00c110010b00c1403001680b140038030a81d00404e014980e660381d00442000d890050b4040c3c4c006105001c00042c800450310008451a00036162621841840c68543e44142c003074038403048807000980c05081112011 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 832582706 1250 832581456 832581461
    0x11031603051303030e0405090309060412050102300c3901021903450c030f11150a26040f0b0c0f1806270411130306 51
    0x9561180c182a482d2004480d00c1d0404030360241e2065010442c50300031401103013050b002d0140c4c005000c1002c0d40c5005030a500154080c050360050541c10400519540100442541100c6034030b01d03448807080014442da1800c241c12542c4000c25031074410040041060050f070307441500c2502d52141e003008a0b000c0c0321440801601000b42d507020000c1c44500740010401001c0c8014034240300a540056101400210042c003030701c0e003034625081003004070b25520158480d0340909040f110944102201800c0700140e20242049288030094204407581400000b00602d49818043d5a4400d01c50040c070b0440780744c204070602c40250340c034904840c001c124424010f4800d800403001d00901e40050149000905d081e0345c02e05500b12800c4416410540202e824007681c9200654810b404203040c41c6403901c0440520070728000d040086800d841c810b1500d40b405c0d136400007920111000c1e854180704000030300320201000da04d03000c4014082c92501c9008104841c8110490707140c04824541c0066041c03a55842500 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 832583956 1250 832582706 832582747
    0x110d2f04030b0a02180904050f070e04021c02270a0509031201030201142808131212020c060a050a050903040311191a040311090613050c0f0a1d011103 66
    0x5a410051780100c003669100d03100a0b004030f0091004200d5030306a04000d614102d042d07048010303003009090420005940b0310b04580e048de41d116422140d12069440860000d0600404003004d030f054440d03020045200d120520751103114116010720040d2142c049258903441110442c2051403034840050003d940074000d159840c5580349000d40c5044502c10b8000400c00c2c851814013007800c003d42482c0205a8094035040e000008100352028903440382d03482030b0001901d1340b0700209111030705440102026480c1d0598012101610603640c9910f01810708030010041203c08515242c68400071520348140001501e0640b68400c910030700b46941d10741088803040e034089201e0341d00002c0450108014003404038401c0344c1c0c000084e8454860b03085280c00042042c00300411030084070100100899030b9548080c0e01c24040303070210006116180d10101034503520561411281d240c3e0001f44400f55180d00c84440824104000c4174010160b4420004544070562850301c20956401440b0090076404d029503003c4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 832585206 1250 832583956 832583977
    0x903020c0a032a091505100509010503070e040f090809012309090402030321010e0c03100905040510060602070e010e0405060103140c100816080c0d110d2f04030b0a02 73
    0x24416034900c03041d400d45d502c1c140c0d400d1500313009120410641c00c00383c060741a51001d50034800d00345007801c0c0000f816408001e0080f410001c000114074520744441e03110300c107111284a4203010501043c00c000c0f030740e54480341134240040c40949c0d502a9101c3d6010b00c10078045007a0303004501e03000ca02810044c5660002c6c2c0203a034540000c0118550a0320001c0d002030036070141d19202d040d81c1d0301d4220320094006d8010540d00c00c0a01c01c02c01c000280815034441000e0340c2040000080396191400d01c2443d242000409105080c23400c5d00c0814840d400250701c1c001c550401c0364408075a070722003660b0006e694096400038850307031101005200140140039140200d00469041b102009404000a980020000c100902240c121001c0c01034011400444c64500400c6007021496818020003248851040c4d00014000c0d0796200580d0021543d110100e80d0389003149a0f0a05c03011003d108035a80b607071a040e07a8001071090b441108002072403031006460450707801200300b2f03002d0394440407407202a40c80b005188 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 832586456 1250 832585206 832585283
    0x290603030d091b080a0c1d07031a18100906050d080f13060f0318050604080306010201020f04171c05070320100b09062215050904060903020c0a03 64
    0x160f48079010f10b1051004180c8840148090403007402c0403000000c5681000980700f1b04000d01c20b8031800d8030b0f86503503003104061a001500346003440c0100701c2da0044544a0f40d00c42a140e040c01124041140468020340020000702003d940d201c20200483e8183e00c5903903041002c20721500007050041300036120b604100c2c01c03d02d241480d8201c20a01d24103440d081103000c03803984c4030401d5050380d00d44a040c14848050f924554100c081e901c40fa545c84a0040000f811b040d400000100e56910039015210500440020743c4d803251340302c101d1004501080803418140744200068a10a00e2488518800415031911898541030841e1021200301e0700500d070703261070f0320b101103400c0d503000404106444501250034000241c046504003000740540003e481a0b03c244444010080540f4060500c046101a8504000340712140e58034000c042e40b07800d07404641c0c86400c0b10100310a2044903003207540700350310913425076119230305500422001c40344600000d08007690045810050480c0030202d00561140038149 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 832587706 1250 832586456 832586483
    0xf020604151805100c03020405090a1a0a031103100615030902010302070b01030f15060501050d0e07080f070317041404090204090b1e010911091c050a290603030d09 72
    0x1c038800039189a8080360f03580e1004103a0030722190a0311070b40c0d14003000c52070305611300f46c03034040020140100a0b0000a81a54495504205444003d07420310584806440b48070080e07500d0038141010703000040a03034044d010b01000c00300c28080303034880c0a0582d0b08004a2103130a00c180e1000310000c00301d600381281410f908119100c00b013140b000c40c95000314403500d003000300790080c0d140013050600c00fa1103c200762400c14805108a230303001784c01e8070b04052141e0000510090a140168074003850ba901080141c06040504814030402092600c00c0e0f0740a01190a0401e00001001d806c40c8544d10940c03000f44151b042a40c2145881d811030012140001d001141c80300b0709450380201c00109540a20180c40c04241c0704007004924242e0034010004e0410811901d4600030305041a403044401d000c1c40741603a03115148500e0131100410704001c3c4c2000854000700a01c2c60500c00c5141082440c447d448800b402e55101224110301301c03846000058082c40c10220031110354006002a50821104031411216 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 832588956 1250 832587706 832587731
    0x1e0918030306050301151512050f39090604090c021c05070f0b0703021b070f050109050306070305040206120a09020901090c02071509090f0f051f050d0c0806040b0603010b010f02060415 81
    0x141c42d001c0d4014a010b04001e02f00702901c1c1001039429102c0702549088070201340e8044980090703001003959004c0d20301c0c1c3da0b5004640007584521032500540160b03031401a2880c1d1265001417041c042a509003070303c5140444491051300e843c0541c407001040180214010000200050300d9260005424280035041000410012100308080240308001f9400074000f00014140850020b006000c282002c42d41c036400c180110b516110000c00500c14152240d02150440d00c0e0321048845007440b4440e40500c0703080040310b420140c4184c150507449005000004580b180c618070855004c40010f070018401c49262000603081c0305482c012100510076100c0c2c0000e401c0e080350140c0000403141c06000685e0180c5540e40d2030460b14040c0c0100d000c804511100689140b42207642c900b610070494016046004c5450003081344580c9402c081011300071442071008015154034641e02410f13040380203221002d2207000448800d42c054240c500146e100744041404074420040960400f6414840410030b03804550 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 832590206 1250 832588956 832588961
    0x1804050606120c0912240105010306060210020702190906050112021213020105090a0b030a110a05041419030b04061b0f0804060b030f03031515041e0918030306050301151512 76
    0x1405283c46401c0381031046100d43c1c900b07200d0387c0542002d080802085050580c000d580d480011148220790b580051504150364446141c60140c0d5098591042126120315282020f0030300780c0702d464041408803024002c00b041e60b0094130107400c00c000800c103ca0343c0d05c2c1d40d005030740d1881c48001e0341400000c1203130004540398002158098140b2564141d03890800140c8074084502e6114002030a03203040c0040401c2c42d900408541c101c40740d801101d80001c0c0200c00080c0c8691700c00c1745800103a02c2c081000000c002c140703076006116038020310b004c0100d890322040c10303d0420f102d0726004001940c0301440031481f0340a618859001401510005421842400482d181c40050001220b160340040304100401044014030402001c0c16128040d080d40d000817a84107901650150b10b036210301448840030340580d0395102c00010030000c0024010020614458913058144420580c0001d0921102180c1402e0500501d882c00080b00c90031000706240a072000e160740d500690050400c01c040750190090103050 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 832591456 1250 832590206 832590223
    0xf03100207020306090a11091f0e07020f0105010317130f030308100f030b0402060c03220f060203030f010920120106030c08090a0308090c061804050606120c0912 71
    0x2088016540d404a00400d807508500030003001c1c0c950310503004100054442d040c0e0708620724040c1c8080b0fa850311020b1301040c01001c0003400a04101c00200005011129110628010203107034007030350411603d0300313581c5090b0360f004d0202030a900c1d6910318011070b035442c0d48024900709908410000c1c0d040d0300c03881d0341040da40f81039000790700044483c0184405241004c2d05a001003120400d46689545942e0b00d807038034004020000307885908045001d5900400a00440d40284583c5012104100b0740030000d4a6020507070090051035405a0350108440e0300000840f40644e50410f100c8072260701e425101c030041c2071030407221444414100d544078801c650300809030003645080ca01380b0405604109005048602050090080000f55409e10034040c0012640034481c5415181400250303840950b20340c5030001d132103880d40c2c01000010304011500d0110f800400c14801c02c940c148225124041006580d000b1000326000e84011400820300e8403010b04020800c460b030241903030300d2600611103c0d60804825 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 832592706 1250 832591456 832591483
    0xf030c0a0c050904031e0e120616020d020601031419080405090a02040308030708180d030203150d0302121c050906162105040f060903021501090204140f0f03 69
    0x4940c8200030040c4002480c005810192007182c828034064a000701341c040308182000c4400903264096103400d200e00e003c8201c103a0702070508010080702c800401e9440718120b881c07203480c0340342001520040b8400b04107640703c1001a402441103900710b0b150700009015900c0c2211451141e00089045c0120700303010303114050700419001ea12980382c5403d02071000b400405030501148104010f00c001913400080c0ca0300201c40d86040400c03640e860414491101e245010b6a0b114441c41c1d40441800380d054006502c140f01c82902807415500c4181400741c4c04410340300007009600085405002038012002601c180c0f80740086090801c2c00d1050f80c031089400c180c400310b48a405c190100b02c0c0381500002c002071045510315101e00711450302d100c3c3c00401125136112004494079400441d080c00300e11042d404416410400c20448407025203400780d03070380e01c1c0705003000106500c45000242c1217000b4400c3d10125040a0b10040340300d10b09a041011180481d000d075644003140710900c5915807400c00060601100 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 832593956 1250 832592706 832592713
    0x50f12252c0f060a080304080109050c100c08030c0f130603180809040902010309050d0f0f02070503070603271514091207051e060609060402030f0105060307020f030c 73
    0x42803501d012408601403001c140041c031010000c001c105500e5081e03404200d065114080d07440355000541c0710b0207198403114440c840841c2c0842c1c1c86c41c066100c0483e5a1045048a03103601001090008500700d40580c44007094000440340c001c01c84402c01036900140c0b9401051421207820005042d541101005200040c00c41c2c81c1800a00d42600c511079012114585079203200985036174002d180e200c1c1c0ada130340d4087c9031200c24070350869010f0781050000b1680581a1642ea6614001c010031110200026400045484003071400c11030001c035654051701d5000c0c0c041c01403142059001c0e0050030301c484003000c8080c00c0d03403810002c1c0401e26030034510081c032442407502c420808012800c03d9410006044400f01c2008090101c1800c00146c0a807051b00c0741501c0903280d90050500b64101800815007401e915060f0b8111500003401103881c0c2d110303240813902c00740a6210041407004a01040356120443d050313070001030049190a801459100c54544100c8101d45802c0d000c4038250340240908904590 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 832595206 1250 832593956 832593959
    0xe060c0c07030512030601270506131d060906060301030b0c1e1605010e07180f02070212061b070302030a08040524180f031903091a090f07050f1225 65
    0x41c1d210049042100e02c07100b24000d0a5854a0f400c154423919100311441008001240455100841100310042ca4481440c0040d00403a10310078489001c11924144241c0001d40000e4040c9010825203040e250002101e0b071746540d902222036043c0e405102c1202c1b6143c21051240107400540001f040c01c030b00664240281400c052400d1406d41b40074484c0049075800150b8240503d48403c842d1200c40e180b141404100c11020052072070091043c604040d4000081100c00d0514003030000d0002d000701c0851160441e205051448070f86140991080140180c004228040c4014420a1000d420601400039150088003140044601641d01070223510300c0600401040b01c4e00b0f000148188940b03d07942d0140406c140358001c82c58492040c0b0030b24042c4481000d0640340700a12a61100c0702565014000f03002201c4000c0040b00030007402c455a07c0c0d42e10503018050381801d00441c4010445e0000f40041c06036182410400c100304024080c0845280b00d00546e015035a100d40120011904009071030b086040e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 832596456 1250 832595206 832595209
    0x90a180b031f05040c150f1211030109051915050301110906040b2d04050f1e15161a010f0303020d0f030902041514040e060c0c070305120306 62
    0x4416480da000d1090b0082240007000040e00070712041580c0b641440052240d5607460001c4010701141c1000c12025005a0600c0c0c070190410f99a0300306001503111f1040380404040213506480302c80c110301d040b00c802400100403550558000d00c2d00000380d0004000b0700c940d442800011101701744a000003425102c041040281401e01ca8a07611910014484c0e141031200e10200706140704910030603c4406001400310070340c1442c1000205100344040313448003428504440020150400d01400c0d205991000050040f80340c00b854000849c90350810180c510040079040101080c1d004c640d240c200b40c002c0002c2100001c41880007854548100018854980400900c10200005070032405c0c616680c0300302400841e4000842840400c8640f804c10100b083c4108224041c01800b040290070a05266003200c03080303034000e885401d0f1501c404801049010110801064a1040b0049030541e0002c40124040ca03c421000701201c503400812500442c2e075a0355a54540b0030304141c40d882c0d030320303010061080c179 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 832597706 1250 832596456 832596461
    0xc04140f130c03061505181009120f03171b0a021906020d0c170103060c050405060c0d030f15090f0603021306030210030621051c0e040e070f0b03060402090a18 70
    0x40c8106440c2c82030901e1488035000442e0510241f000f0b200b079865141d401c10701780c0719510000c094005400082c00240031887c11f00329050110300110049510450111100226000d8051050a4110000f500904120700180841c1d0007200d0324011805111610303402030711102007070b00c10148101e40059070f4156043c00001203400e880002000c01480d030b14aa6440c40c5000c01103410b40741c103c0c00000b10b212174420282c03024400c03035009a80081000c0b5601c0040036003c03541030002c101e0340d00c003402140b122a00c8401111209042ea10b407054441c8014007600420794080502030990180000701c40751a50001810041c0151100c0100303916180c041c0210300700405108011001c80c00c040c403140d4140003919040d030702c1ea0012044080464844882800400c204020766101c0c071003440e6003600307015800101001042d00085020b541410701081240da00019944111494990341403a01030420010309a00c2d80b028240d603500680034081640c0341e940e02008030009103040150144910002000d0205 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 832598956 1250 832597706 832597739
    0xf0f0648070603050606040e090c040c030e0106062c0f0a080610050109030b010e150a060914150906070302010e030406051809090606010f0309060908070b0c04140f130c0306 76
    0x801d42044d007809003644488050f1803d5540d2445000a01e40c0c9140c8010b1400030035a04440e401400d100155075441c1c0c050f8000041080d01c50020700840da11040240c400842d201d0341c07103660140403603840d14a02071200c00c900c034190b40241407a40313000d003007400a49050b840c0d802070302007904400c0600200c6854420100014442802d00c0803283c1d141d5200c1c40890803052161102e03803100f80c80041e01842c0c0e807040c541c0c50804010050f005958076403000030480002c5000b0041108441101d11005190a440585441d600885590310f0040440240b0045410081d021025903490f1042551050001d101a2028107141c0e0307200340c0c42e92201200241802c07401e1580c01d00800031801840b01d00000441c81c2c0c0d41c42102030900c01e803909451403044000b0000060058655890040035004101054009001850140040c10f01c981c48900e0f42540c1031041c0e1207503400b40210001c00c2e0a450600e0120350340e40c614010300040031130321107103510015201008801d01c0017998416052116105181e00c016 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 832600206 1250 832598956 832598969
    0x403120f090312140d15080f060402090a1d0d0302341e0501060f05033702210a020406080708030315030a0f03030203060f0f064807 58
    0x1e890038503584030503556204541854041284012035048105840c008492040700c0b40903080044071042d00a80b690303114940a5801240a091050202d01c0000a07401c3d00554000b030140700d458035501c3c0c81d980244445e00c000fa00c011600310b40c0741d50640b010710900c50f0006c06c0381c0300540c2c3c3d403036100c0e483e41c4914040240c1440c002484030a420b0598046007001094590012004110440304200c2c05c2c0070b4908002c0040180d800c20401040d0740780d02210f40b40445a00742c0c101c030450b0100143e00000d40407104040c00f04a0040d08071010f001c131022616485480c00a0441098204011105031134000362410050b0035a0003286010304504141c8079101c001c0001130049c00c06241070a01d015124407001c2e004c420541c407800e04d2071219540502a01d40e00b81c2e03002544407150302c407502c0d02038040d40044030110b10030030005012003030b5400c1c00c0d820701c107100c078008200f145400d02e50003c00803498640031814540c1c0040128469180c0f60880d03000c8500c0040109000444054003070180ca8400030350040c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 832601456 1250 832600206 832600217
    0x12060605010f1106041704051324080a11041b02010914072d050402031009060504050609040602030907170f010e010b09060d030302090d03050903013606060b0403120f 73
    0x90f03100030102d0701c2a002a400500c0317420742c18034001ca102c402d0046802141c5c1c002103208001003200b07041c0d40b04d40b059902c24810340c00d0381d00100e040e42140080c18810f5881641190020b50f00007030700c09010301c2c1c6002c0010000181124120480740c0228034800300070380942e644540c0309050000c40c40d00c400340000a60001c1242506100065a00d28407944800f0f8400d0003c0c007807003070840c861111590103094086c00464880c6003491804003134851901c00c4130b20103841c000011401d41010701070144545400741400d91240c0702c80c0d40c1d03071740250301c01050b101680c0190b41c00428090454012502c3c102c11640060425aaa42e54500c0c2100d4003004105c1a6038984680d200460311400d1a4135401f580882e00301501164500b4280c000c1d00c50148419400010002d075102015002005001030200590082040000e03a0041c4c3c4094400c186c2511411710b400803103d294040050b010011b00d5101d62800700b01c0c1c41d0741d0a080e0076079070040d80040b194211038150000d10503038080d80c5401869610b281a = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 832602706 1250 832601456 832601477
    0x161b030b09060709060309080d0f0b090a0207030c02010c060219080a0c030506030a0b061516031106060f06220b071e030f05031b03040510110423040612060605010f 72
    0xe01000d101d8170425091640350030304034043c010040142c031246002d9203400d11124044a068034001d04288000d503218410860100d143e1685910984131b000d40c0c107031503824140102c1d800548041c0744040c4100c2c2c64a4081240041c201100800f901e403640b980d440301c000a0508410b0b880540b6030310003a00c802c06140504000c0c1c590f9001500d03a81c80782d00b200e04550191514400f040112040c030249501107540040c0303440c00503a01e9500385066500950300e4515100c8085060b1380c03030760000d80712541d1020301300f01c41881c0e82ca1305000404281d55020005c0444007800d48038540c0c600329039408030052030000303d2020107002c0340803885d04204412100303240e00c421780da98020b40502c400103039420802c20f012001492003a01d180c1c1c0031a01980b1002229141d2900c0e00c0c00607034401c9c0301c2d00c0007070600d41819607400410480c4820740d8281c0b00c00d5501031445491b507492017880c1c004e100c44045d5103c3d0f110840000d24804003840b81500038000c1001003001818040058078100305403826208005004d0607 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 832603956 1250 832602706 832602721
    0xf0a09050a02060a1b1209060f02060a0c03150f0302180705030112050c040e0a0203071502071e090501030b0a0b0603040b0c0c16090204080f0109020312161b030b0906 73
    0x4008080340e40c121045500d0b44c040d104100c848080444618110105001880d07003800303810f8084400d00061341c4d032065442c2d504c07400121400d006140c018009030f4041c00104484c07840036007000020503254a000101030708040080300c00c1c12002e03840303003640c0705503c7d03400c0c01542002c8000b060988001c00b130207480c60802c141c0081441c03105110303209c000d40109030207108100b01440108400f00e002001400218800070255440301710285040748a413180610010b40c3c2c009085009540d0784003500075060051801002c1c812a403034142100e0011401d20380c0c04141c000e100c1c49054044c6024440c0304205161418900044a90140616118182c240304100001d400110040d40c044c0c0c3c00c1c5d01c51501c030175040001e1490901100d085060920000d50042441d03169a4068011521540c0031a91041c0341d08800b1422502d000c07501075019040f800d07444031003000c01401410704012403481c0c2004031019403540c0300546244400d904001039011410002c0c0182c52000c036400101c401d002e09601d050106 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 832605206 1250 832603956 832603963
    0xd0c090c0e370b0a051308070f090f0b100507020109180509120702030303040312020c0f0c0f120604060e2112061008041407120b090706020a0b01030b060d020d03080f0a0905 76
    0x200c00078100100062200c443c070710700d42c41e06c0c4e00510071001100d1005440301d9450000030704e20300034904540d10b00040a4503000550080d45420305000c2e0804000d500302d0001180c45034440c0c002607050044009000070b4070310f42c0d00821039482d0714500000810f81460300e00c003410160f00c014040c40d8644240502c102607076011007101d4000d0340c1800c06003991010240104064010350119080501590041902884000c40c0c0f0f01c210000490f00003204858140c00c01c03c803800403800484096201c03400040004110380d01075030300500c1550495103100b442142d00d42c4043e528104a0180b020045281d410646241c640e580c0c0180d02140d42400e20502d0341801003421100410250546107042040c3d1120740040c485103002d02841251030091003c581016400f141041e60b83c0e83e40b51240d1100012418804184072442951018004506900c0c6480e4480d000201a000981c010000eaa40c2401070781d0385112014101e2103500d601c01507140150009554030001003007080018186401c3c0d0300001d0011 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 832606456 1250 832605206 832605217
    0x8060d11060a1e1817032a070f03060501140603060d0222020417030313030c1b080109050c010306050102070e130204051003050c0d0c090c0e370b 64
    0x291011600c0300303400c1100315100c0100301c80020820401d1044120350381e44c003a4403610361030342403080750078616910154100e00c86000c02403690310390024480e183c0c03160589482d021079803982d45a404010185003400c682416515400ba40510070654010800c1180078050f4034011b1020030b5000002e1070b40000405d005103c01840184200c03100090001155211850300c401140740100d880c009500740781c400d4000354414041c0c1c00e90740c00013451000c40d12800108981c441d0040313519091881095a9066038090300c10f1408995040e241c0c0c0d48040c0000566400c1001003582000200e134280d024201181402072442020707042500348130060007070b40d0300042c00b07400302c424500c8080314655480c502102c0d04050030300000d51290422060000a4000158820580c0c1c080c0081c2c4103c00150810009403e548020051903011146010059461941c1c0705140302a03aa0414803188190f030300000c3c01000c1e0279041800e80d0082905441c20440103c0380f4010840b1311030420314059801c00c01d9885650151 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 832607706 1250 832606456 832606459
    0x2072108090c040c0f0810090c0905120a030507080d3b0d092c01080a0302060a0902090606071e0b09150f04060513061a0108071707080a09020901030501050708060d11 73
    0x21000300c1c0340020300c7c9021000402401030200000f0103841d01c000c000e04046d00c40c4920405440310b141d5040d000204100c0d041c0d9506444841ca00f8150b03585410198012600001d012a6500450055694002180d051030744441d082401b03010501c000d8242c82c8502503802c038005602102190712480e42060501c416100e608070281c1a540114050018a59020b02c1c1d40280f14070020000172b0030381c40010021a01031280d02910004c7d554000f10303500b1034010304030180d07120390801c0108149061800050003070134090000da001c280710003072885019826044048810710041c0c0c00300400c0c90340c03d000720b15a6045150b40038041d4204034800c8040c40c00050001741665694001250140c075550f00c0f0398040741c2c0c0c003910501c4204000012401e05070544042d55001c1421600061450340c80f03036590000c10f1500121410340c54039141011200d8620090040255950f1442e01101683d80d680780c0c41c1c001c52083c800411685000400101642d0303024205a0140d1903000740315002580c01d143c403140c80c000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 832608956 1250 832607706 832607717
    0xa21050601080c0d0608011b031b0e040c09091401030b0a09030203070206090f0a090507020601060903020d060506060d020d0e1506130c120e01141501021002072108090c040c0f 77
    0x44104c0c00303401019150f0005899604c0d10195040241009840c0b0f070a01c41c19403420882c0c0103c10321960200c0200425080005030720f150100a81e192541c401d00344880d00e4035001140c42c0e102d420f6001114401400601d400b0f04881c0100304002e000004240d00119210090050084a680181d0b0b41c1c00b0321807009120305c102046007038458039601000c0c09902002052412901d94400a0000404065404500500030540046403c9000303100c04801caa41c050103a0011080c55150710000308400f50500c1d90007102080340c07001610003400a00082512582d00003600c54804981c2c81c03400042100e130042116000c41000066510b11005200766400b100c80070811100356041218005824118843c0140c81c1c00380c000c04407901544504140030a1a004400a440e200000b250788440882c4460069120800803e5032940c2c6801500000e071143d4201814a9070b00e403090305003265102c0801c0b0003d59020100814080200040a140c0f5800e807010800300c0e0340d0310703002050440380701584000d01c103 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 832610206 1250 832608956 832608967
    0x703080903130b03070306050a18020d060e0106171012020d05010905010504060b09150604170a05032d090f0108060112050708090705030f030910050c030a21050601080c 74
    0x91040c81211507400b06840380302442034860021841d10b400c1500c0580000307261010101d05403d200b465a4140e440103a40c001c0c0c481a13aa1002c80a94000a51754915030f4580e54001440c52001031224040e044131740301c0c081d044040c2e03100a4040e04005290446045440340d0803ca0441c103070806500303180e0150b500b454a040c3d20309010380504100c0100074801d40ca0401000309001641d8803241c0038140450700d10b50303141c65100e00a052820100021580b0072010401084a4005040f8182c5c00400e94000e50720220025201c050851f04940f1000350a19060344c161042500f001c200030044810345640035040c0440400810001500349442c2030520812002141090780078007030f0203004c503103003c400780700624165030000e0138010182d458400f6442008004a0240760100380c0c2c0e207c44400000940c100303040d2504021805141029510502000300f100c0304400c027003031000302240000c0351a21100581601c00012800b4910f00510154a140400340007460380d0107280303540c001e031140039840c0e00d48 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 832611456 1250 832610206 832610221
    0xa0f030623190906090f020a0806061305031c020606031612020f130b031e0a020d0807080315270406091b0303080f06040603231f050a0e03040b070308 66
    0x2009540d00b021a0721600036800103942d01d4079082041640c00d5401e00340604038141d22103009902881d0140070104e621880064800d04004010340340010303035506000220b1350b46d0b0010034109001e1961541c2409d005d0004902d03010340400c18190071040a50081c100070301c08141c13500441c401c42c080e030601c021080200d007040d0340c0c40b44210303409501d008144e42080c108501011008101001c003007402401a0600030b0007041103210100304854a102c064805104168204041d02c842c415044032442c1050051402007601c1401031071003076452030300b4034404e020310b01c00304040c0c80c0780d510104a450402c0c0c507101d0183c1c416040503981160b440b50000c41c4c41d020914000c0e0150100408200754051050030000c181036009001d079006032140c032607c0541c0c1c1c0303c034400c1c0700a66500d4080608542144981c10300b40e00c05400c00b0b983c2c1b900425064075071541031001c01d9900c1c4403001c85a4281d03140c545091040143e501d201c0c10000c6800d010003140740c14500030f1050494001d01c1303406814841c1000010b10340 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 832612706 1250 832611456 832611469
    0x4080f04090203070c03030b06130506030901090f0c0608250302090310180309090905060c1b100501181413140303270303060d11011e050a0f030623 65
    0x3600890380c1c295100d1070842001000c50b00545026400642040000c03011418901c0840b5210711b0f0380c403000ea15060034001800802c0d2303c0505101e40300c1d940d80b1001404101e13014000c0314441c1c0f180011000b06850400020b0051038094600c0c154110400300000c0c140b003541d40345400ca075410f0b060160315203201400203810201100480701016050051022240301c140740c160341102c1c0b0940301c000059481c1d82c01201100c0c20102c00800070350085012500c21903044001e030900d40209940e05a00b100d501c0c000a040807071071130502507210b1b15400140502e00c3c2000a10703609034a01941000241500d103015400b610003d401e8901c0d000d0560714220502044004405c030320601c08044a81d81c2c106072403000c0501401d8071810305046a43c4030b01003000d20000c4100c2c0e001e94401010615428000c1d1241c0840340496902141403101001600030600c00c0140c581003804a13a8450545404801c0c80c041d2402c68085015800c05151000901214820140005000d003032900842102c035507010205e1342 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 832613956 1250 832612706 832612709
    0x12062406050a1413030f081b010209040501050303090d060b03030c0a140c10080402061612020a11121b01051e030601021002030114131808070b010e09030304080f04 72
    0x94104401a02050030394011008107003a100703941d540000000c8000b05000b040c081c46100d0a8040d05018080000c24a03050151061501500c01c041c94940520b0307407034440602c200602d01103a5004507440185e4a414480c4500401080e00a1440c00c1d500b0b10014413041100e80004007585c2c0e480e0b00c8405191030400c141c4d0300c110441743c111030b1010b040741001200d0640c007145015141c0303e06c10074014203044c480741203d41e4580079254000740b0b0305c466081240940010030300700c028000c84807880001c00d801c8201d00400d0107040d00980205401c6041082038002c40781c840c140201d0503034043d000c801200244240c0460b0900c42065042c40032800103c8c0c0b540318840703116107802c0c20b2241c0e0f0081090220015809108241c0865980d10b00f452100426030009100c0c41491182c1000d017112030b41003440400c4c000d5008680000b604410b10002030801c1000c40c80140d07010100030038128108084d80d40154090660094a083c103858100300041d92403100520040c945180840d4480e030000160007070720f0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 832615206 1250 832613956 832614011
    0x9050105010c150f1808121b04060807140403060504021809070e192307031e0c1205010f050109080a020d140c09130231020a09030203010c08010e0906011206 69
    0xe0170405a041c441c10603040855104100281c3c1c802065902101860800000c80c5044403507051910f024401c2d0b0301038400034910030600c44140c5460115107400310061011314420000000d00b0b04090051102200c1c4445041d03804600b07103003e11812090008640d401c6680304400240c0555500710a5030007a841c00140e120403505220003200c901c08130100c0d41d031610405200d107854580d03440d00f0460a4030070100c0e03030424111103c41905000c4502ea04040790074141c07400d08121000d541980c80d4200c030400d90058208400f42c4105100a6074004119402014801c000f08031505458000031100510007030000c0840001c1c40100400d0f400500c211103035508003c2222040e4900009250309820640c0300403032064207036403800b0b8010350700440700003035442d100120046080803980c0c00320000d5110001e50300a200043c0c03400001a9001d00440181e0342007070f41c81860b02c0d49440c5c1c09080c8050040c0900707140307400c85001400311150850300c640002d9000100410301d80500158600c00040c9c03c0c0640 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 832616456 1250 832615206 832615241
    0x60904090807051c031811120d0503060a050a05060307050319020412020405130f1101030e0f1c0f14070c1701051f0803031f080f0709050105010c150f 66
    0x1c800c0c800040b51044000400a03820715005540c801e08034104d5414030f80502c501c0034121079040c041842c1c0c0d1141c1100e00b8001c1d01c076962086400e11407902d000060380c03014000a038000700304330040c00c0c140c500340c00404094442ca400303642001f0001d61580401461235041040100005206410071490840c80320070800c0115a01d644030b0300502d0389188c00d004141d0040d410301001c07a4545d41e42030488500750340c00030b00f03d00e036012041d84c5040c5070100c0009007a040684a00824031a05010b1281401c054280d03001400001030504014003a0014009054180511418114809500061400c00000700081030039550a014074100309102220b40108081840d940f01809240c01c055004030b02030b250140103072440482c1200071a10b840b003d805041d40b01c0c0c20620105407a0080c07141e043c60503444400135801040e1315000201e20f4400240100c4a299024410030041000b2138400c3d80d001d0070003868900501009a203801e40d18120f00940c80c620b050f42c2e2620100300c2c0d94264002140d500c0e5000a5 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 832617706 1250 832616456 832616467
    0x19030207030507051507111215061203030708070e03030f0703050a0e030c01020d181d16020c150705011b17100501020a08030403020f1509150103050304050609040908 73
    0xd540e480107000c00c49951140c0c01c4041241e24000000c4145a202513820600d00303032140c2c0c4d9590040c1002d50040342c01c01700ca502003000c40b69040c0011900d00d500031046450703c2c58402c0812682d050300403070340d00e0706030010018040e05580c000302c2c840d480682418070095082884004c60b01d0340c4070705885041000004903662042560001c000d02401d2030541c1d80034a414854000c1580342c2c81c2000350240541c0c8411415800140111803040441405101395031381c8d25524081103400800442000051026640820103448026040413407100240d00c010004507402002141d151014901c03d03607510b51000ca20142003020941080c00d80c120500d11015202c85100700c060000c04140d40c0b03400d0300ca0031070000942805612440f130341c21100305a00078002c800c1191299510b83d40301400c25400c600132502c0e103240f000c4080148000d2954803a684410750b00d40701c299141408880b001d4446581e070b0341401080032810010549050f81c208664880c0da508000000800901d81c0074030003816401c02240 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 832618956 1250 832617706 832617713
    0x7080607090e06030f0303150d0602183a141c260703090807081809060405190c120f09020405100e1303121b030b0604230319 55
    0x2040e80440c0c4000d240740d003450f1500010543ca50003030725003501d01503000b40009511442c1e5030010032105040035090f0489045103448407802da03408081407000c05188901040164140450505042004c20201856100d08220512003015a2074410740d181d249c280145401c0c030891010409420700300c0c0c8111420901c2d040c4a0003101c00c1c0449043d00450300851110109074900c0303044224041d202c0c081411240e490080580c007c0449070030580e04502d00b40a10700000708400002e0108a00031103a10302040c0440342045003146004164a000350304100610903280703088a07510284030300b441808500c1c03044c0700600f1104801420712107403155040130740094682500c0d9000c801801d00a85003800f0990380c3c0160a9051407080c401e029220003d40c2c0040e10751415002d2800700280f091a2280c00314018801406c20b4400e665020f03068100d44d00c0c200d81c1803030340501c80c0c203441c040c1c2955014141803400c05a0700b01e0007814909021800c00c0c09420100320394040c0b10020300000c2c00c84107841c0100705800e = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 832620206 1250 832618956 832618967
    0x40f021204061d030705030f130b0a0201021c06030f1218030b180c03061605040509040b061e010f050c0a0203061e06010309170a090f0b0d05010b09060a08070207080607 74
    0x805180725011840f036076002c420040200c5072419040740080d40307004441c10f040c881503802903011482000e600040810b40b040242b0041244c0102d60380096140ca0b420740414616040103000c440000749444070810014402c1c0ca1841d00b4950000d100c00b0200c00359040a45184201510300c03c03514034a000003104104071094602c0c02080d409001d05040f4607201e9000c0d98441100280c40d92641c080070004054806601d41c401030a0710381d140113424a0755840c046408103400b1342d421142c0c0200c510820400f810500c130300001803911984464202c00e0030200203042010b110340c1d21800c1000c005038054025a0410009000581c040c0841d0701c04e2503c21306060b0f0320301180181c6d550455203140400c0283d031007809000c28080d000814182403052814045046e50b021802e90700900192200014001d5066a00000180758841c03160b0303540d401c580300030342c104c0e1416082031355040e0341400900c1098807204103460b8080040e040640c0d083d01d40803001ea203403c1050744414039a00c40c01d001c00c002c803039010 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 832621456 1250 832620206 832620221
    0x11040602100e01051b0a09080106060f030c081504180b01060f0f14030604091110030b190b180a0317192102030c071b0816080c040f02120406 62
    0x208200b210300400040d0300b83d881c20343c2d040c54501c0c120341169804a282500038008190182040300d90315030388002c25403c0d00c0155008001044181c620f0350050fa8060162000c82c2d42e0340d00d482c0280b403a040d60080801660303105003a00480c0d4800300754400c005410803144c8079035000880c0d8001d56075507020050550f80d5000345400000c001c08801c02600c2e00640901c01c400c22030315940c03400c1d5510320090000070001c0d00002c0c0c40b404080040100c403a15082e0003482002010350b0080b0300c001268003031103142084980306201d48440c04204219421107401510f09640042e03c0e0450600d041d603001039030711422900080d1005003030071481d64400a002000300525280d0055515081c040c20b10700b501d0b6401055051205580c2036010508401c02e964015a4480e40c80200941482a1622001e01141c1c41d40d041d040700c1e000004042c044458104405d0811015a2000100f038034106500240c40721902d200c40b601a07034480003400071241c2e8540584004c040440c0d0390051600d0581408805054172 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 832622706 1250 832621456 832621483
    0x6050d060b220b0a0f03090213091a07020f0703060c0302040308030a060503070605030f0f07030e0f301c020906070f030e010f05041217040b03180a02010f03050a11040602 75
    0x2c0a0380020029158415500c4800c01034071001c51140500e0400d401600c0780601c100d900c110504032501041070648250800035010f440343da07040403c80d0b071010034540d001620510565121078020304d4014800642081030701d90141c00414131000840c0190007a00445d00010a00d0b080401080220b280a5205400725a400c80407941a50390320901030342c00f0720040d078028035980c038010f00091034440c1038070809800400c1440c000030001600307100e03281084060020000140c02a86020f0343c502080c41c01d00743c4460107403c210302d031a410703101100c0280c41128011200c0b8130100e09082c1c14802258140c0c0c003a85c40c0900415980c41452404001b40b07240c002084020981800c0c4103103095125182038504800151515440c080c107008800e4600080c40748216040300f4540741940d00411190081e10062543d0010540c43e400c1402c5041240c00640c400ca102a03403000510001503a80100d004640800a0500140586943d132110015066241034507481440000b070019156a0010350032941160 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 832623956 1250 832622706 832622767
    0x307050c0a0b04030807051e01020a02100c02030702012601030f060c020604020a0b0706061d01031202030a050d050705090301060b030604060b072316080606210706050d060b 76
    0xd6a50411010852900801c0304002c0b042c0818400201030000038010a4050401c441400039515040f500c25900110003400a94001c500450065010000291541007501042c401880a043c00070340e24055110b01a040081c07130080d50308104d66143c13404401c41810300300e0108960312414402e107114a10300b800c41b280c6140030b500e48032051022075414003403039004001c1c4140926055155005803c1035a09545030795441c00005405021200c00085440809649000300d40c5582440c0125521200301c2a041d90410021202080d0740042103890050044100048a49400d0400c854034024000d2141d019072078018003164406c0e00d807010354400e81080700e0501000b40c944842000074040d9001c0281402940032888e0001c40b04c1141e44a5105010303002c890020280750b42003c45c4142c5d83d440f02405070030001c148440340c14031492815a0024000402e070713504503883d45440c0d5a20f203910440e4100315010503220344100c40c82d00503200428101564a880310a884064164002203041c490302c00c91 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 832625206 1250 832623956 832623973
    0x1e0b040b090303060f04020d020c190606050616120c0f0311010b0a030f020d022809050708040b060f220f060503010b13020306062a0d020105310c08030705 68
    0x8400421244122005404040e401d16080c046c000a500b02c0240702c0711058007030082c2c102c00c15041014111000103810a001c070301c034203030419004030381146d01300300e0203a40708004a40c00544482e041c1e02d01d4550064100400022003801155042c0032510000c00300300f1103030703000d0040c03640c8090921b1803802110001c002c120702403810802c01044c90b11000304030600e039044100152070420407480c0d07c1030025007051030640300002c0c0310322001e4001c3c00140221150704410310001a0f1440f0b0554094000d041a10981c109a00d542052820081900e4840d00450452400076141d60620040316441e550103400d0005401c44600043c081c540108c1c0121890708000040601d41400b9049038800d020704940c440e20b02d100405006940000c080a400c12820440700d40402803035080303104144c0d80c4c0d5480303580e1001c02265903401c3c070440c09401011681017600780124000a08144184e840201d900260865815441051442d400c03805c00303440d04115030800600c5c0391000c80205200b41c032442c1600c4560 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 832626456 1250 832625206 832625221
    0xa032f15150307030f0c15050408071a04090b010309021903022e050c0703120f02101b0e04090b040c08070e15010503090f0601151112070b041e0b040b 66
    0x1c1030308604941d1551052408101054101c0c00258030b25004841c05424151071b00d2001d080406201070f0b00340014000501003058600900200307000e0040d42d000d0002c004100411494240218050012016915071003200c0aa000307910040d02c5d40c1d400307010b2181c46040300c07511051200c16448182d01440180e1040315009c50392a45141440e110b440d210740390941e542504941076000302d04892004e108440c00480802c00404410241d0101a50740f0131044082a2000781005030004c14400540d0070220728213512140b0b1410380404036602c1c134041210214040c0004d02a0000b114040c0020956505000070b0001089242e400d0b02c0c4050101d0741d00990b01d0060141c491022034100030120741102e56182150308c2000119004191740d0700301c98907000030300c3c441c40c1004030aa10070624406081d070341c20308941d0052805812200751078080c051500d54540d03000c4e03240c403650000400d040708010001e8100040c0400190404159040e200031a0209251442c1e840005440039118020340710b0004100 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 832627706 1250 832626456 832626481
    0x6120606130207021c08071707030e01030b0103150e09061806370c03050c0702130c140c24040320010204170a021009080a032f15 57
    0x11000603000840d080c010700054002904820302c100d81c0700409624481c02244c2c0d00001521442c0590f03907035a901c01c1ca5280c401c44004107001c0000e001c4100b80680c10203c3d8011a0748440c4010078240495002889001200289002688858172804034200030072a1141810900e1081001000301c0741c03151920244081204481c1c09840c420380c2c0100f001032142001c84003200410761544203e0020340071000c5d184c050252f1070700000c440702965898040101a45806a5600701c00b040c1940307840c00419070082815103102c40d141940041c1c844005525081c4615039000032844250226a140c0081d8100030381c861a40c1d841040342d104046200c030303440400003402140510360544403144c0c410f8204000c008140b03080c00102c440b83d5800c3c00b0004440070703d80204110728007410068a50305116204200321980c102102c0c0d02040300290091100070400144102e141c0d0700750a120820f440324080130300300d001010700da41c0e0300e0b81c040c030b0440c1441140006800500004007500003c080c0c0d2354070710140b01d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 832628956 1250 832627706 832627711
    0x31104021c09030e0913020306011517090307050a08030108070f0e0f151f0810210f0501090605010608180d0e1f0c03260a0b060c0a0b061206 62
    0x1020341e1030380302014401c0e1507600440601d03110b130400c3d050349184030000440c1c111044031110b001d03449210080d411481e0900c00355002d8408407a0600f44034900c010001d22924021400503035a151000128001500030030540310b2031903111007203c401c0481450108560340080c480d5031032900c51440702144914402154905480c18000d000c8025035604080c8400c031080548160101d140001000740340b0f443e2000040d0140c14101c821580414003884020621080103115640c0d032504d1080500404001255000500020840d00c450607030079130821210800110300c00030103540c0b0b845684070810610f608524100d560640b2000b00641e585203510101030100c01014079190401407144140728050800c00082000241400100d8817601e207e2034840103260144c42c010490517800c40b420940e00c01120f220320640814405040c1c3d0101c0d03421600310001408030190a91a01e0142c0c00e07503100d10058480180c082012105000d045040c48a200d0720b0a5450328051005c0c0c0200d0058032500260710350 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 832630206 1250 832628956 832628977
    0xd090506121e010b090f030a0503091519020706091d1605040b03090105010e0726250e0f0f0a1a0f1b06070c02090703090c09020a0903110402 62
    0x34a407035040c01c014998810000c1408240620120707080074100724220380c4501030119205036076502c403400010440903c421002003407207544a00c40c0f080c00070b04044140c841182d4180d40f01c1071210803a41d86200325010f480800d141d00c6007104049180141c0c0098148104e59203611008662030f11581000b01080c40700003042240340010380814400c58074400194440d01c0b0038604941455211980081c1c2030380207550440c4d0a079103490040c4820f0581514140e001007640c100401100c8400c04180b001141d03005c40a46541c40308400245900e003003d507900a111070240c007402c1c141150740400fa10010300d00f00198010f5110b200710381001c2c2404000520100c1001384006411450400d200302c07800000750403c1d1058106001d001c0c480c0300312001510422807103180705003004a10340201441e00c07034020700710010030202c00000c0c0d0142e02d0f030b00d11840c1c01040386d01d800701c2c00500703506010400d8850f80d88042951440080c075541c81c15407210480d015207206d01d482503020301584040000342c1c0110990907 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 832631456 1250 832630206 832630219
    0xf0b06032a2b02040b0706060513060510050a02031225030c09091d010606050318010c0c080d0e0607050a171021080426060108060a0e0a0f03020a050d0905 68
    0x9120a055100c2c616440c445400c40151400d52641500c48158010400c202c40103078642030184050b02c1c262a0000d1a050017110030003000303151000003206440305006100c144103000850003c664030078411101e02c000801c20342c014909080400007510380c80d08601d05941c0b00c20316288201c081c420301980803030512540d6820710312420800541c1c02880e00289030105181650441080ca03c400e006100c028441b5407200f689914181d0300c1c0e02d8094000f03031102c0d40c0591400603804441a045505e0014494110701d100340c0b00c2400b01310400081c030071070b0401701c0f091158608120313055621000808000a880e9916407070074920180804841c2e9050f24101152b020080050102d0340c411000c81c2118006160054082039a030f4071215129030090b08202082400411002d40d911741040f009500d007001c0f40c0c000c10707a940c0341c41c20090325038034050603d134a8161110b400b200d444408011880c2020b41000e03410740d56649510f4080d54801c09144202e42c10b000b110100b5000a014211000403220040e101 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 832632706 1250 832631456 832631497
    0x60b12150d05031b0312100807060203040501140304060b040e061602030309070302010509240310051c03030b0a030c080c010e0a0b040b0f16061e0b0a090f0b06032a 72
    0x2050840c4944550341066120034045104141086841b041c02a201c140d00d108010341004101400c05035a0b40094007594030801042000340d070700280c581d00c4003003806503d90701da40b41c61a00101034405594030384c0d4018103055402a4008004c14140e0240d0400c0a1220740102c0118042c1c1c0c40e8041181e001d00c00b90414031041001d075000768014600044001c06c4113500b0f82101d00180c4d102001a1110b440704e50f00482044040da00040c101400f4240490301c1f40080042c5511503d241981c4510044c105611840c040c151500c6994036140074550060718102100d484295080d81d820902041314005201011f03030007458103003401243c086c0c81d00103000ca86010308206405006a001d0784004680340001c1100b201441750640c20b03903010500c18400071a0105016060a80f0144895011f442c041e1410301300b42c84580c2e0740a1088102c8648260124000602c1d4203c0c00081080d041080d800100000c20022031090300c40c00c003900c4005c1401015a54440300846010320b0040303000120541440c44907 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 832633956 1250 832632706 832632727
    0xa0f090504092102010b1801030203060c1206010e01090b2b0c020304140d02040c08090d020c101b08070f060501081b13110c030d0b0301021608070303060b12150d0503 73
    0x4455845030315000204100d1b00f2540480c0d800c000104200c62400080001882140340038006541c0000c02d0b2b51615081455442c80c05980c400050011810300008140d9043c613070f4080c107920801000c9408c41c5644407200640c1c1c504148040010b603542080582c0841c650080c694410f01e400c04241d540250700b800d042040c509407401c0e94103c07243d4400c21031000440143e499005200340090710f0b81c0c030a4840e08200480919005070608070310155045862018196107842c89086c0c3e58203468501641d081600160491001e00d202601618001d000a00f60702800a0341c5210031405105050030005c580e40c0d00c40594848000303148214444a2503d100c0c081450402a80704402c0c0c0c0c5030b84002400b6120082c0d12801d540981d05003a625000801c02c04030807400c5114034801d1080640003540b5000090346850b01030f2001c41c000034040e0901052004c1850b00c01c0e030268000d0050228040e035200414980780b036a903d0221284520b03620302c44a501900e0400c4442c004259a00600440c00d00e50b00c01d5 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 832635206 1250 832633956 832634003
    0x50910052413140114031b090613140c030420010207031410062d080d140c01050c040905010602010c0806060307020a02060f090102010510030c0312140a0f09050409 72
    0x100420465115034445440564843e0050700900c01d03501c420407000d844000703150a003443c08031005651403606010080c0e80c0c07140f60700243d00503000c451410391400c2076054035008059011800850242e900104610058080011400f6602525443c02c454461010301c9803c000101c415900581100301c2c1000007030f4403245060a02d078209002e841002c0030b0002d024088400c1c0358403002d0161003072441c0403124070a100000c0d0780d0401c4c0341000040c850a080a044d40c895401d001d0808010302012440740030101c000c01c0e501c4200d640002840642030043d402d43d8290400e005038521b2514090000646500510503440e038580c01d500c030320b4100d81c1ca00381000b0280d0401022541540514201c8000580d01d070b400130491079504c41162920f0300c1c0294002821a41c0045c2010780720034803a901400400d8044005604403a1310400080b0284484401100e0400303d2041080240c000418401c4003941c22208440c80004166903091000e80e80303804000985071502005480c00c0058400c0c140e0783e51400 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 832636456 1250 832635206 832635229
    0xf06020610180b0d0818040e190807080c0a03090612024306020d060f05010818010b0a0602010f270327030f12020607091502100509100524 61
    0x406081c040001078440d02d1072031b40007003c441410f030780001c2c1d1100d071403a09108142018100768001c14a208440124427900290288064070075000829190200716480080300e82202c107072810b48022000341c1c41c01800c403a1a40c0100d10100311040a1200f410a10b40300780c40d203120140c44544c24401d41480d103000f0160800d2083c0754903042031820001f075540c8408400080c1303807041c0310042e503448980d00000202d5003aa0044003410010b842d04100680e808440e094000451446010001180e102e2580c014404510745680000d1000e800203001d580650020000f80c40c2c107a414844034103c400c440c0340c8549000320400d150a548490400440d110384840c3d141d4402c04101a070440311001c0c0f1076105001180e0085032001c0c00482204200b05120700c1010a0084500050900d030800c40700241200c10300f8040d0401d42d4108580012500b071003000280440740c22000200324504040090584850911500c10a940d042c03601282c0c1c0c114207803502c010421f00c142540d029070107030341c0308202d00c52508 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 832637706 1250 832636456 832636459
    0xa0e130903050304030327082101140f040504030e0114070c060e030d0c17182814061e39070b1921020406140903070308220f06020610180b 61
    0x103009c4000e50840c4024506000e00b003852001c49100c2c544e4070800190140d05000c0390302a50811080c030001942100140e040e000b000d082c0382540220040c1c001407a400348000c003500701580c2107400900d50303800c45480d0241c10415070a8441c2043c655505a42c2512030b031030300421440c030907108601c0482c1070700084d10400407100421020b401800000800001e01c191541c0c1111443c51280e9662407901141c0701c00801034100600e054140800000c0c00c24002c1c0303103000341c41d030500c040c05070340882c8640111051040d00d4400500c2c400040000c07000c0340c010229201a0101050032110825000069000120744011441c0e074039100a11440a1007901d03203034041001c2c84811411a014100001d101840d4030310420401a2560326111008024121a2040381c9400c5006c0141c03040700c0e2030104c3c0501c140c9402c024007a6030390242c00095000210a20300502984034402c101041d0031400f50030140c121510b5500322a201e0700c0c2e41c900c141e03030618a881440c54010040700345603c400003580008106100 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 832638956 1250 832637706 832637737
    0x80702030d05010f0e1e0a0f14070905030609120315191d0106080105030a120e0d0f020306010e060904030c02031c031b02120a0e13090305030403032708 67
    0x4103401020507180d00fa080714a058040800502c03218242c0701d2000c0d80321980b031b003401c1c6403996440e070b00c0141c9800190203018a9500c6a1122420000a07005480105200c1c50b10300c0301458600c0008107100c000b400b03003d1090089001003046180d000540110006643d690946180c40e8107018086140d90384100c6500510141e541c0c648110200e603040c8007c084000394044007161240c404100c3d60310503040705c0244100000148165100080e02551080d4400740d98a20040c0e000e000340d8414103480a4240d11000040c1910200140c10000c50019842034045400a0741c803540c1d400e80c030708070407160700750000310200004011a100d2585161200c1c00501500e13494041242e5a8032128001d000c00340110303413110241460202140e0812078024103034805000d613154030a50000541c4141600340c0e0070001c4005103c01310380c1c3c481c00d045400f552003d4081050000d14a005043d80e0403c0320283c012a141040c45018205480340c10304014a05401c069606101e9a4403000c031500511074141c022007 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 832640206 1250 832638956 832638967
    0xe060307030c1229010306020a0e03030c0d110c240f070b0708090c1311190207030302060f0103020913050a020a0314070f14090601020a0f15060914010608070203 71
    0x84410b100d0401819103480314494001450901501003e12440c041c589080c000025041c0340c4e008110321410b6a40c400350160f41c07240b00340d404880f0b042c08880fa1540c54000010f071100c125000003180d6001c00041d44603080507039902c0140a440c0c01c00e00c4406a00084801c41c1c00700302c2030001103100284100243d460b0300b0420202c0290303074a0b40004204540c105180b4090001c400d8218038002e5000241070010005040c0320341c0403030900300081c24214115501c843da01e8510b20403590a448210f45c10000b10070105840c404004d50354155840160702600507803002c40d80c0402d02c03094860507681c000d444400d039601c07154941d002d5104050015036580c0140c281100041c1d40d00322104000b18010020404108118400075042c03603000d5110380d80540300c070342080051240d00d815a044190b002c6481560701d0b40c50741c0040c1e090030400d58000b0448441c000c000c504012421100840d400008802000102d03160364014045881401040b800f40b188000100010380c4910b0360b05034400c1c0f40b40f0650f410304 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 832641456 1250 832640206 832640213
    0x22118070f05010e0a090923030a020c040f0605031c0f0f0f231305030d03020c0a26030a020d0f020408030711060d0204080a061404030c0b040309240f11070e06030703 73
    0x2c9118200c00c6680080c0401141d050231007a0108014100300c0002840c40d000d01035201039540d02003170310111f016a4036104146400d461503844440107000c00b809480300310305120101d6010312804100007000c43d2070120b488500900c00c60a16010300802d44441c40c0a50b001001540c103aa003029059080c610030343e19000c4c1c06002c8070040c0011a601c4d500801619060004160420621007070310000c140c41880300c0d280c102000286036010640220f108006103900d04805143c01d81400c100c5100c02800106008055580d540242800344114008011a884100b400381c01e078130a40c4607000040d0b10038458007010a001d00503c80c5020001404c1510742010f03501e544003681c100394000e104a0f00401190304c244881030188091200266031a0844c5242654000d4450156180041c2683c651040050f007007500810450000e006c0c0744002829840300020740040d0350300c00e066110300040640300c07218501c0e03000f5074440200314510805003840310700b070030303168600c64800030801c640c50b00c128140000407 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 832642706 1250 832641456 832641461
    0xf07050705040207060e061b0414030a0506040f03030b010e0904081317030d0f090f0803190f0b12010507050a050c120703030203250f080a022118070f05010e0a09 71
    0x2003442001c5c0401d011150660a504046005103e0018855010680711404254108883c01c2d507440c80018400d180c040d8001c20319140402c80024042d1049205000500c80d4600000090034800e40d403e003d80c000c01801107a100140318005a00503090001180001d000500a000c40c010600d401c0d00e40150b9482c20030118510f64840900742e50000070704218003100038041d100c21009040c2d001d00641880780d4034501c01540101000d4680d1402001141400c411003800b1140000d0241e014000d008055a201004152001d98030b446028824070a80c1c0084060042030b114050948500d414019a800f054401e070340240310f400c45901a8101060400688030081c2030054000c1e40c00603180d15141450004600e69900c043d8087c4101c42000d110050b4440c9080240000c5890030101a031245000c800103030280342018402c440d40c50f0f15228005400c09101846a040c0030303200d2000d00b00c0c6901003912201d10380520348004a5460003071200d54001c01e035100c3c0f054005001001c00d41e585000da2400c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 832643956 1250 832642706 832642717
    0x1707051f021c030c1202040b0f090307171605010e030d1b020d060501051c080301091a13050f132018090606040b0f010806010c141029060f070507050402 67
    0xf1a544880c12165903034420034502d099829003108520b0315040003441600f03401256181d01b66840c0014248840e074500340040401460007400750425000007a8003940c032950304082c00c9000c00720b0003000150742d43c4108500100c540f03000d00076160643e0b120004841c0e192226281c44400c10550345003000586440040c0f015060142c0300000f82c42d41880100300704040d80440d074036000000250f0b08804594403000300c90446108040000b14209851000010501841d9429174032402605001c204028143c110078403940140c2582c0072203075508071911240010f40c000142c1f0407405403803c4041003841480c01040d501000304040c558030410102c0d0304504a00f210304240756000031042c030400c0c0c10103002d117060440d01140c2038221154a540001c012480081007203040103030542110017031020002001080c1c40d0a2001e40e4240c541e466182c0d809800c880b00362000c0540c261101020b42c92020500e00191070004000c0307842d1515003500e603607907a04194001d580900902100240c5590f90303200819 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 832645206 1250 832643956 832644013
    0x20102040b2802073606090c02100519020714030304050d090b03011404020d090c15080c040803070b0a0b04091212060509010b160b0109061707051f02 66
    0x10012501030ba10001c078110b0007600c40c400e65010b01c90511140c00441056110200051014081c03451030361401d1940080c03240300c0c540128900b9401103020310103a04048080c0319150201e501803900c494080b02160002c50f214541c802c03100c0c5015180e401c45800500c145070054a40028001c48031020714115842528115015405500c01511503078002c1c00c00e078001c004c2c6020300390440d80b410000ba014401d20719100c0d849203900007010040036804d54000316500c5d4000e8003c01546403a09010032841501c1c2d00c0c1c1e240891444030003e401d2025160031141911040c4001e103042a006a44410031080d005c2c2000c0b0b030090b1102c23805500d98480348203803409503018002800c06c6c944207100240800d0808440034800318101003041c4215182d68114504565680c0705080c2d4620703165805100d42400b6990091220030b04600000e40c003000394000100f6960303110001a25500085c0302c095a409162048540002c28801191140703014012a4082e0018500607122542210f04d4800c282c2604401c206 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 832646456 1250 832645206 832645237
    0x80a02010c090602100c35130308010302011407051203220f0206090105040e0903090414060108040206030901330501180303080a020c0a0308151512070201150611011a0f0d03020102040b 81
    0x30a0b0141f42c501c0c40e1601b10346243c402c030031800c600c2d480c02050007105000280c140868040c0c2d00241074880c90441d10180d8100301502c41c4146515901c4010354410f85026100d40510382c0700f01200050342c1c803030000040d0320820003001140d00741c5c00d10106811091002c1d0500c42d0a200004161060020b0300e0b21408008001d59620a42003007000110f41c95520ba9001e210051401c00c0100d98100c20110342042d01100c1ca940c0b00e80da4110107a0160544031000300b020b10b20b00000700c11494810000c011a05102c125081410f5160801112041c810191102a0b4183c03d00104080303801b40043c9608080c1c0880302600d4813004051040c6040701c440d404400281c4802d04110b1340119117010904001c00c1103411901e02d43c1140300c5000b0074001c4040a840010351800443c452070300035808171013006c500e100130308031241d61340b00c01400045004810031195400e00e01041c03582c2c80008244010b0a00050074604900f1032a410711131066615541201559801c000202e1643c40d04005810800d281440c403 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 832647706 1250 832646456 832646537
    0xb0c090d1502040b0d06030501050a09051f1805070e071e030b060f070f030909200c0c091f0b0906070303090309090203180705060702180a1107080a02010c090602100c 73
    0x2203084440050072000740a2330200d02c540003800c08160907019802401810100d003a0381c402d684c00411000380061105c031483e002e54401c022011078454102c61002d65401f4244e0b85407041034458420600d41489118070030f0000000c0e8600a034800c03100540003070305039814076001e460546116400078406a8250040400c0384042641c00000343c409007420080900201007410a0400303022600c5501c140040c0003c07549941d901d0082081d4081140020001c03c80c60618448400e1201e1a40e110b401c0740043d010008288401c0e01703001c80c0d440100103000d10f0b18082d0340351000c80003800207078012000c0100c0300d40300041c6510140043c500a0451114294030003460b560484d1401649074041801044140f04000240e921042c3d82040030603600310702d0103142d680c0d5402e50000c0c09059807a8080d03080c0802e4402c280300c40b01c0d001e130101c040c003038008116602030301105541010343d600c6840010b0b400150751986060392600324003444ad9040c2007000c2c09442003407101080e080d45411004c0300d811200f24 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 832648956 1250 832647706 832647713
    0xc090c130906090f0b0105040b09010c0203060f0906070e0913020102011b02161725030c0b09131a01050d1103191b1b03050c06040c030b0c090d1502040b0d0603 70
    0x61685130300e4542c10100001c034000c20020700640110b00c184d043e45800800c0f40216079014071500c100c0c0c1903004050f2800e40c81c00300b0302c0d114000415210310030984107040005c1c2100b80100002d1140240041c15603400782d468041200c03040c00602000ca046540b60f400380130b080c29001d407607001800c1168000e405c2140d0118054101004140d01001c0d0410707030f00b4000410305501050304111070003400241d6218040c508a03941c0c103030000741d0000700850b07000a00015442000006810100310032144a418165849000d0741522a44078080020307c40804034294258000c0d00240450598040082048507020501071615003040312095034a0032403545142c4620954072800441441518490184800c90707680104400741030792003c103201200c1d8140c401490700510940300c040269104444061503e4035107080c0c05c80092008450030302c100d5002c078504110081c1620118003020304000c0b41a181900d5690b5004101a2082c5045900308004154426000014005001004e001080d02842c518 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 832650206 1250 832648956 832648961
    0xf030907080c01091a070501020702100c0c120809040c030b040608071502030c07060f170106030e10050610031802061914040b04030201050c1e1506120c090c13090609 73
    0x10209040000c4c501060260549841c528085124030494082d1034000c6c51512500903c190301c0065030080c0c50360761825807d5400984002500d10806205d000b281d59440c0702c0d010b1680c1d41c540101029024001e168150070907501090a94035030303240204110f4408400301d01101c0e2079402050303864024480520540daa074038100710141e0341610080d45014400c003001754903806d960054104000c18142c81030320080c0705000149200e0b80060b1206055692980081c0061032400c030415401d0107960180210b0940601c038140c031480c00642605226594064110010114003c08006005014200d080507803251400740410601c03010000c0705022643c04003030b00c0380c61a100b00c42013a00040000307004507000c61040c3d608403642801c1268480a25580c03c0d4100300a000344c0107042c214400010301484030010786280190001e201e40341c481e44410081c0819a05801004099a0300003410711050341441c5440941c0411454001c90a091a680010107801801d078445410f203030300c80c082030000d0300161 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 832651456 1250 832650206 832650223
    0x103050907060f050d091a0910060f050d0510050a05060a09050112060903170702031b01020f1210030519020108090606010801090b01120f051012080d0c050f03090708 73
    0x4004010840c50010014460103009040f0310811201007010101c200c0a0340004109503440020b404c0385513468403040c0980002141d088070244584c522102d00a1468420401508c902e0200031350f40c903082c0814051131140403441110700e44240c2000d0450f43c69548140c6000e0780b010701c0b0200e0305082c42420805c0615803a0045d03121a4503001c0104a035a201c0c2c090b201d43c40c1c1d44440040b0303400c10542015100d6031040300300c0e00103506642c001c01c410300e0f41c00300050100340680e40c081c3c454000f44a445a0803070241030001d48402c0010003030003101c1100f0050042d0300020003280c030f0032035030b4896440d44c1c01c2103283d82400f0070210011508004560300000c6d03c541c49125580286214a45031000800000b41803080d18400d82d030700c05050505911481740c1459031001d060061048003100346148009050072a1812020305109c4000720b144480c60030342c9801c0542100b41c070b170700f024071003000d21009144440041c0c050200c100560001006004042c61003200c408000e0584246400b00103404c0c9800e8 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 832652706 1250 832651456 832651471
    0xa060c0e0907020c0112090506070210050c09240403020604030303020c0d0c02010804020108040c0803070803041a010602120315040f0507200d0c17070b070e2d0a0302090a020405010305 81
    0x518040002c00c0c1c0c0d0000300031040307010920341030481904440502e002080c0c84907000d4128000c0341c0c02c0184160700010b1680c0400784d034000420150303070303800030b040550f006400c2450f0380025903108221801c8004114024600303c440d04651420369030398005401640b050740b08802090f00400c000300110402d0058040100c40303410a415a50801d03800200202d0340204001d0600c001b4ac03002c6014031064512000140c0782c1d10b01126510002c80c1405c00035078008440842e102243c48940b000016034821440d4100c40d072030340080c101c1007088019406150001000180c10070781608802c0c00d0360713456024101740078240781d0000406090001d0b00a211000ca18020380e900d407050000c05a40110014210040a04a140006c90801c451421140e5491085a04403d801001c10010203010490031168001ca030981c80d8201004512002d22904140d02c92045401c0503102d041c0c0821b40748041c05500b0368420092203543e060740c0344c0e03000034983c4d1000e03941600501c0d404201403140756014800c0c160410348 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 832653956 1250 832652706 832652719
    0x10c2a17011806050a0b040606030b0a1217071109070e0418150b01020708012a08010320130905030406180305030306012102040e072601090507020f0a060c0e 69
    0x710140c42c03003248440c4010040c9129542d00000756200495845001c3d072540c001c0042c04030559864005001d000034404051083c601404c0014800411a042060441d400b100c458918450521816a1a0000c020580d0801c8800030001050342c0e5414400c1e2151103d620703100d00000380302c418441103c030701d4900c040281c21300701c5014010425a102c1c81c0d0250811404c00300e02202d5000040781007115a501c04200d641c20240d00384241290713000144628241901d102c00900d0700712000325051102884082e1a440030703070621000c4814600030444079100c1c05001c4103c5034008000510444009980c15101500003040500140754400912090404d10300d0a038000c403400c584506450b44005000c443c140140c0310700c001c02080c0c402c0140c001b01440c0030f508544540da50800420740c4003040b030304200010b07030000c01c0c0e200c402c0c40080803044150711800049503581c01c05082c48024400900040c080d44a0000c0e10301981d10f0400c90b4400951244101040c4c1124600d0080c14031106100381601c20301 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 832655206 1250 832653956 832653971
    0xe030a09080102090f040c020703050703111008040b0c070f02030d18090e1f1e1e050f04030815030a080d0e12070f030302040f0806040218090c010c2a1701 68
    0x1680c98a61700c2002004a80014074100000401c0e460108c15501c0104103010791000042842075200c041c0d2112078085c0d40c00e0030340740d40661f0100d4203204100d400070001e01030080811281c2c100400940360503407007200300c005112450780010740b608180d00303803900c001605800e80c400f0465140d411003008190000d03040c0806210340e402162940c8503a011894071070701e00070301b0b107241001c907030401c113034100013440d40c06449060315102c078004d8038141c40138940f001d1021380a070303548040610640f4804c0b1251410300c0e400f40c9466a0403a2a214080d02803420000c000c010f540d09644d003406918549481034007000d03500c203a04000320003075860480801009400802c14a80d8078400c01d000c6034280b9502400f2403000350341070325044c0c009005641180881d00c00525000c20701c0000001c525000d00c2c0222104c1403150000182182e200908441509050704000d0102c0c0c03181d4001d01d109600c1d01d10801e102c5403600006100e0864801209010604507004103504100001c0030150300c1032200e0300e0030020302022 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 832656456 1250 832655206 832655209
    0xf04051011040e0a11040609060801051e06090a030b0c0414062a0f2e151401020123060a08060c0f1b10052221120e030a0908010209 58
    0x5000e184103c00c1c12025000002e040e91002d54050205444501c0c4821703112511294020720441c1c8500600000c114407000100306850301c0b201c5142c1c110855003040d072400d0110414001207401c112800380e0041c420580110005401c2c1000038030442c03481d030b5019122458603840341000059140b00d140038040401024064040c2c8468032550074248584e0304d028030b0044000140b5006261803460164020303c1131003612040d81c010a0520069429140c405e07585124407084103c5900c01011800344100180030040120286038006c0041c0d014000010220010740d6a040d80070400c02707203103c465010204000c100d2428038142c07000f4104400082020385410b4030f01140904c103079130340b801000001003045100520a0342941d8044801ea205a4000d200c0160040c4041e104c140d510740f00500120014282d05000181c00e8442c86401c0701028001c3c2180c03140c04174601111040c21010040c12403e440d030b560442c1c1c0240302d640f45000d80110359030940d1803c01880c403c1d80d600454182c3e4010403020030f09 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 832657706 1250 832656456 832656491
    0xa061d120d080402031c031a03030307020d030c0207050d112b031d10020105091b01050f0a0507020303040f060315121b090c080a0b060306030607080a140f040510 71
    0x107554200340341662202e000007403501e070581100c09000c5c500070fa01c01d0815a03258000d1282940081c02d241c3d030134003500c010542c85e80021140704006038003611400c040b051187c2c00c00c069a40250064601c903640b0754010682d81503c5a01c03d6448400d168810a0141032408051080d2948031003002108080400e100d00341100c215405010011190066500f40078408a103400c40c0c5c80041c80c05d445810380b503001a010308011135122007617014029404134a0140500d5800700700301c059440600e0f005054800341403680152003001c042200034040440180c40400003800078148600c50122142d10300740f0000c0a0301c41d201c09092032824401c7c5c04100004203900caa0039603c2d400a40d0380c5440c2d92604400c201034030f141d4003000b2440d0818054000c0650000318060060070504418004501042c00b071100e188825501150164001030005541c80e02c6441d03c150828005440030520a0004000c0505000180c980c02035031500103080c00104102000040041c0341c1c0c8040c280603810740032540c0b412 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 832658956 1250 832657706 832657723
    0xd020a031715060313020906030316031101020912100b010519030f1b030603110306010b190201110d0c03050f041e05100e15011413090f020a061d12 65
    0x8140075804a902c0303561100e901c565441d80a003543d51240f41c00700000002007414001030380507140c0e020100c0c050342408800c64000740011818841d60001d00e0b0342c00c4984170f02045583c0d94555080c421940695114184240402074040c01409000c0440320080d00705c039100f482c40380c140003040000c02d0b0800c80b0070b00c2840104400c0d080024071071100c00d0b841b4000d04407550006500381090382c40300741e03682e030140d0013541502c0c01001a10040c1061390705060b03480b4802e00450081070003c1c04041008401c44001100c0104a44004200f40c000802507203943d80100c00c600e4021034841c1ca401d6102507142c41542d900c244006c0c6100414202501e4046c19580014250691400100c242c1800c0c45000c02c400340750003480d200d041090450250700d6a4851007502d440300386400403407000160410000f0300300d41c0b41440040064201228861340072008041c2c4010490701c0144400005003d6a90420028010002521015019070440002004403200514014482c40c8410080c00001300006040103 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 832660206 1250 832658956 832658987
    0xa050904020301200301090b060c0a0b0c070c060e010e04140105040f060506070605010302030c09070228050607020c040f0c17100302060403080903060105010306051c1e0f050d020a03 80
    0x61a46950010a014003809003040610440007044803080c8100b010081d0304032482d05000b04541c0d4038a10401ca0203201d0901e80554591100c0035040c040380450000315080225444a1f5280c10507941c2c0303003c2140b0303682d4008404140c15040901103035030441080b140c50a001c45040048400340c1d0004245000180901c50043c0d0b40d03841c0010718015198811340140800a229580703c19603450705030090314090100328068060120110b410381003400915005084940140228030210083c0d03400748034400d114503003180300012114020800070700c43c0c14054441036015125a000b00d00c10b10007901d9103d03011003c098034124550b00880d9010350441e215111b0004c4a450355140c1c4c040701850002290006940640009000000c1040b41c0006121329403040d400e03105280e27617500064040354514403d50f900300901d004160102e84486600c99526803003219105031040d6415a0105018000582111030100d20365400b0140041007100c048544003910003407441d0302141d5001410140070030480c5 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 832661456 1250 832660206 832660219
    0x15060e220e1504061109030a080703120501060c05060c04080316150606120e062502011b0203130e01140d0312140a0c032028030c08070e0a05 62
    0xc50301a440c1c002100c28820081200e0300290007101500a03000c2c140c40840d0701034944115170841d90150000c0e0f80740100024003a061005950302c43e40d110b40d03c410812010001c0e814420b81038069188500c60217003005980d54044c1801c1840c000d49070420151042c0040c1e20244020440070400204540710000007040300410042c49281402e50004441660b46095043c040e0105441d50710001c014000921074406107d0103400441d540d0725400c003901e0b80c1c00c40c440105621110544030b00792054500c595840000350fa2800020600020003911645400580000440c070410000c3d80240d5030107011100da00d01c01c2c1d94503040502c1c21001100c0b0041d4020840241a0024103000316021102c000340750308180031000540700e03030f0072440c2c070110b940700302c102d290461412105101e4860300000302d41060038840c150010341c0b240c01483d040b441c02d84d02c03032421a200002c181c1c0405c019000a0800716100803904d07a0540c840504000d0307004141c04208074a0700b0081030710baa51f140340042100d00a9802 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 832662706 1250 832661456 832661509
    0x2100b0603062205011415131203170903181c0b0702120c0601030c0b030411040e0a0204020c0604061b171b1603270521060403020115060e 61
    0x1a02e40d0b60000c004924003da1030b020000841e060040d8103042a201d00f2620486c07925406c4404e98254001c030004907841c00c80c00c020174490245001c4041c4130f4540a0305091034001c00351140303c03182c100102e40203002c0d41c00100d4488010340c400311414407005800c48001c0401c241c1800488a5007a42441c0540f40d081000c0c0466035a80c003e00201c100d011503511120342d103000b030000d041e5942c04280f00440e8101100500040c41e41c005138140c074040d03640445084800d4030342d242040f024081e00d030481c080e64052200108010381e41c600c010502c01d40c503800600410300e0706092200445600c2040501c500c0d440811216819510851600f010350000d50348103000e4486201b401d002e07021040c1182c1d480200064030550500001d88000d02d0703103109a4900030401181084c0f00600001c00d803440c40c00b0b82c0b10307450900c501d181c000b01382c08015401c1040d000350449100c5100e49040010b84041c1c0140c0d41d2124074601d61680041200090605418145410f01040c008112801c941c03140500300c0400b401207 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 832663956 1250 832662706 832662739
    0xf050705030747100605032e081006150819020409050112121b0206091203040e04060f1103070813050f01020a030f0908191b110102100b060306 63
    0x240c03800c41e0003034a401e0916590703041000002d0a01000111030307035580f10380041e5071159034840a005803160b51762028115150385c443c1414804001e03040c25a80d42420306000f4441002c030000000400c80c0c02e0040402011100c050421038100f40c0041c0c224101100b04d04140c280c0202420350405400429031824070501903114000340101d4000317a1942d41824000109041200c8050015074060720352108042e861100070350f0072501280e494040c886811207010098500700c8003030610f9000140403140c06c007004450f00c60440d40282c01c014100b56040c410b020500c019072103042d080017221070040041400c06c20031042c036800004c02c0041000802030024100005140c08500d11b81d90040440302c01c000f5a1080174044d41241d0461350005c0d240c800860f40540b098060b111b070094100f2001450000a002c3c44c8180c0290f0384400c405001e00700c140184140c2e11903038000100c1c1e0041c6001c1010012440c002410304502482610146080c000400142d50342c5000301c03a08040c0844003014880c0c050603 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 832665206 1250 832663956 832664003
    0x3080411090a02070302060906072003070b1003050d02012c010b031c02151e0421020d1b1a06010c08070b07080115170c27010f0507050307 61
    0x20319400036498000d000c0100325640180210f18860340030b89a4594607542c0c0b195854000300d400400290781d032004030b41d0899508800f4210a100f91042e64581402030f2520803100c21700b40c40e0745807031a01c404030420030311a0511241c42c10300050b2000f8041c0382600f0700340c92010344004152002d41030004c0500e010002e42584415180013000d02030b0f030110303a01c0345003050302c200c11580c0c4030f0058010300c5aa5500c4c8a403224007280b080e40c01d500b840320500980383c8803850203400108126010601c01c407144c64403c1400b00718209210b80799000f40710a14071020020b10034901000700c1909000d00400b01c60019241c070360040c00051442d1000103040c0e6134031004031034009040801a20100c4002142e1040c00305d03031040244900081c1d2680400390340c2c0e40038140031480020903403600080801c083e0303d000061100109400c4080d4019090505043d04890070cc1d8041e070781c4040c2e40d45076040860300343e5946c100c4002e0b58200c4060601500304501526003680b0380c4140c0c0001803d0240f01c0700030030b40030030558 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 832666456 1250 832665206 832665233
    0x706080c131412010504051e0a03120c0e031207060c1103090d08040504150509070207081903030605300313031b030c0e010e01050603101509030203010203071722030804 74
    0x200000c1c422030500d811f00503260310b011a44602d00040c016880354003610009840010280d0581e80c80c4402403c0b103ca85006003c03080d0180c0030031585c15000469640c08100b03213601e0b900c080031120b5643c125403600f20108c6148041c054140051a1055924640d010003a11400c1d00280c030003c0740c07041c00b403074584100c0c8600d03084151701512300080d02540c04401120034003621015506041c0da0788406505a03034460303a604c20601e1961082040030300041c41000c05404143c4242008a802ea403200001a0004401c080504ca291108400d4100d0003441c0e43c2d40c205441a24000b443c5410244000480403c0d0306000142c680558107040368090107171114900003c5070442d1100e8140c5880c1c44061400b200c081c800e40b151610030300d001160724945041100d014104203454440b05900d4031070002c0380a800c034622082031007a016400000343c0ca013800214450020f6507203400412002004054004038082c043c026640142d280c0c2103405017003900c00d400c3d01030301800e10720800d540720b15061030380001c1d4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 832667706 1250 832666456 832666489
    0x4060504081b0904153c050f010501350415060803091e15090a1e141f031b1701170a0606030602120c1e1804020403050706080c1314 58
    0x94601800d42c1d20f0034041e08901b81141c040081600c00c40d400c1005d01565019240b541c5071144403c0100203d600074801140c620852826401d00281a840080f02c9902a90050080000c044042000f00803d61400525481c005641003200f04d05051103a560707030103800b03140b80c05000c0c2101c0d6a60712101e008600c540c4c049000b03103100707081316411035800700680000340014002c9041480201d4401c610450040301b85800705240c6058038139240740618015540d0302144c0d0440070700021076400300c03100340d030000442c43d007a180840e40c0829542c0c40140a081090840c00700f01d001d40d01491008c4040300b60604441101c0e101103141070f6444092030402d052580001c01c3d99280c01400010405035070058050b10390340944907100d540d502d565402440c492041168040d0036220342c500105854140a0a601d14074510314100941c03070360000c80c1c1241c3c0150015a034503030000508205c5a54090701065000035600e0030203041c080c20001c60a4801d88070b0003421161340c5004040c0c540b58660020040c0714850 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 832668956 1250 832667706 832667741
    0x91127010201091b090c020609060a021c050a060f05040c0c15060b04080f06010e060f1207050d0606050f030109021819020415020607020c030a03080c090604060504081b090415 77
    0x40c0070030783d0540783e080d84c17191000081c00d0244400d48580080b0781d06105460034800f5102c0350340c82c80300755402940312114040040e00c07080002501c40c00f06200e96445545904000207245050901c018102001a0300c01c0d8420b905050031020070780d600c40250150580d0024200c10f030f074001e0b8202c460283c004e80d0042015034002040000714940c0010300c59502424100c1a80c60b03590300c840b01c0e07031454030b4102c0d03616400c0003200c01c40c8141800e000f00b402420312701e070b001500d4006c0c0c0c40360001203c1100c100c405a608544408082c013080c5000002da54a48101310001c0092005660224441811810b80152036014281c00120104140d042e00b0403201044802155280c0e20760f00b00d81103c80f00d14500d000144030300400120b000e400010840d007042c0d40100185403070b4200703a9007143c420000a0170182d040e9420f21903013407140c41d403070043c001a0503280c45054882e070400c1d941c285401a807410315190241c0c6000080001c3d120041ca003600a5007004860483c4511a07200601a040d280034500040d030 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 832670206 1250 832668956 832668983
    0x3030e03040509071e0305060a0e04050f0d030b01090f0311310207030e0306270709090302030306151e03062d1507170a180f09112701020109 62
    0xa07400b9220315104200007100402c050008017003181199008c591107034121039000410701c10001c007014110391083c818001c03a500390503025896428166214003d80200361180000005580c000540e2405818011241708a451440d242c12500600e1961524001c2070034520039145161691100348640e00000e503244a0203403c920701000030340c00020107500294103000701c003190b4900403030868002c00c1446880c1624205858090781e0000308284440300500c5468000500d41565025071030300507000303070095910381c50600f05001550094000500908a007040740403400501a021101e030701030000903241d07d80c0c0e151000301e1032003540d00480030540d50000b00412860213103050b0340c5e4103610303060301d0414204807114a003c229010f546401414021000407940000d0f440b140508000403192400082500b4484c10b1309403100150341142d00c080c85090814801c079000c41c01420100440c01005514141d2003d01c40c0403040d40100c07410040f00d200d0706410081d40c0c400d400046105420401d0701f006c18 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 832671456 1250 832670206 832670221
    0xe13020a050708070c03061103060d0b1329010602030c030a030203072c01030c3b0d0302010209150f0702040506210703050d0e01081302031608011e02090a0303030e03040509 76
    0xb40311600c0111106403d0085000f44c4040c0241a2402441c2c098500d02960120b88ccc0e400c20360301c2c0b00a02c022504403102c182000444e90754101414407070342c2e4104c100c2c0402c501398440180b00c1416080700f0309660042208400c221400001c07039007400c845240050f20794484150480e4541e84074861101c00111000c01c040300308003041298269680700b62030070850f21000020a803072248207a50035580034141d281900001021040320b040c891500ca0400803042c014010004812581030b40703058006030760116a1402c182402c5841400b40a1840800b0b41000300756100e007000c91081c0ea0000b8003443e100c00204000343c9504220050f60300c2c80c044a20b0740c600c164031540f55100050301c025075903403003510030002c80d070b5004502c1c1440701003040c4d40b00320003640d40d042404080c1d8203081007241c051003680c0340301d40c0c8864401900c0740541030f00c6001280d405144008032000303244000020542d14410410013940741e50750402001242c0d8103041c0495011100160365045025640c00203800109010800208 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 832672706 1250 832671456 832671473
    0x5091c121d061501120e010e0f0f060f010521120d0c090e010807030803150619020606040c020712170703090302090a09050a03030f0213030c060f0e13020a05070807 72
    0x1407103440c00c202c0e1226030310203100c0d12000b401602610301083c40e010300d251134a2031980000343c0d0720a00130004a8400c40480a4030715240d0441c034410040c0e042840e207c20846024031041c2c0e0060360480c0500d40715410400007500d40c2c50702d003441d899802ea0a05804015140620403140c080e501c0c0344407a82c07140d80840c40c1b8805404001e645100140da42070300171400b1510266000d059a0144005240182c1541c1c1c981b034540e400a0200d00e240c0c00f901c61018070583d01c1d20001c00e1400c0d2018051080140d46840c080e19010f006482c203442030f801c1444503455260300140b03000444640010481000f03d003800c01407414048508c214802c0c0000040d02000d05410040c0041189d100b03442e00c041c517590f01c804c1300040343d1428000918580150020402086c03113904403000311158a40018a0041e0106d10070384000c440f070740211031740c12084404100090700601c2491103c0c0c0e0070709001084c00700200c0080d04841506104030445680820142d400c20304c10b500780d80042d640180602e90326120b40c14031190 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 832673956 1250 832672706 832672751
    0xa0e040b090f191b1107030b0405010f0e010507021c0e040501141009080709150504150501020d05070c0b0c0a0c0f1e23032404140105091c12 62
    0x182801200b08100950f0381c40c49070b408606240081380c00102002041242c0480c102c808004a40c8105040807012542c00306205000f68030800000940404410b40c1801365070241c9240c52107649400c0410170456004110400e020740100310000180228130800e8400036080503d90f0f40051a01c000840d003040445210111000c0c2203581c0b0305040d804520498413084140145c50440c0c00c02c400400c400507171a044030218507064081c03154001d482e1808076040b1b41140900848104000e5030410545d60140071132095100186081407801382d681e1500c4615969070310445034044c800041100040e90f00740450f02840303910035034035400141c0d14040e107403070b89180e40100c0800d5211882401e20030f8400800c007030100c4529000e0f03a01c031074420304c10004040c007004c2c81c0240c1600600d4000a54401034200c080c8003403400c8c0340700d52640d017024104003d41560383c50416045038540401d00045034000149001c004920b140c410070361354030500003161040c0e405400c0d1100142009002010102141801c2a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 832675206 1250 832673956 832673971
    0x1107060605040e0a051e0a060c0201150506030c0a120f14071e0807050c07080f070614070f022704080405010f0e24041d04150b060a0e040b090f 63
    0x20b5243c10b0400b40c40703040011000f0090b9109415580208169003003440d100040542035820110a42d218503082e100001d401500507592000c00102d414452110400a0300c403d881c006d09520300769140310b05a21070002401c00b0701a4000010b0f0200c003094015901c085e08401050043c01c50310500d461200100f070305d165012a1100842100c034071110041d6407040421580c92200039201c0c80c0054425074001c60384900305008100e0041000c0a0030880090548200070040c043703a840d0910041810341100c5c4e480f200d094040281c100410400b242940d80c00e030b01190082c008420a04a405003184d80680000a40012408120030300c40b0040281c1304689080e20f0b4000c1e00001c04808a8401d80e04460041d0701c002e1022040b5100c02c1059020480107107010001d5240944911201c0d0705d402204030805a0709542a00704410010304500900c0000c10011081c440030100c1000600c0381d010b040c00c00c108000d50f00c05400170940c0e03541c0200c010381038058545403241c00c0001c0000c500f1401240c200 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 832676456 1250 832675206 832675211
    0x120f0204210c08010504200f0a0b04090e0f0604060b0a180501050405061c08090d08040b0702030f03030c03040f0c0512010515030d05030406020d0608060c0c1b22110706060504 77
    0xc0c1002c3e060140303920441e44407190144c20342d0303155070140c545d5000b00855a004282d41180914a848000009025001c0001f5039900c8030710f0417a2100603200c4160042c0110307045148500019030000940c0342d0859844800460400b5084c0c01003000c94030b0a610606152000000c041d010f046c5951003107050b5007003600e041c440c6a803081306000c1c96004021500034200580d0101d0000314400c000a0305550400078580312465013aa00e61140d96007103900068640c002c0061328900714602004a080d0007013114000d58218a0803140c0c518030742c040200082c00c1010402e860608201c04609180c0141034000c100900030346400d00058000c0c0411640c404240c20ba20308001c0051130001110008009650398a42c5143d441d0b90341c00000e900303d4085881181e8036400040380d074080611419100d416014495a2152001c640c024034290204555400c20030b408544081140c80d14024140e004145c120b1340c0e17414002106140e0000c040003021540108400325611003000ba194100d0000c580003214103 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 832677706 1250 832676456 832676459
    0x303090c0609030b040b040503190207081501060f110c040501180e010b0607081803121e04051509010c0501050703020c01060e070f0f090806040c08100b01120f0204210c 74
    0xb600e00001c5030001401089480002500182c0c211442d50b911600c5102601e09142407684841114440d03805500007580104405110b1010104021030200681920700101035141c0407000d05240980054902003014030340e68181c0d44101040703145440003000c1c0c0204a01c0da900d003180c0307c140d142c03810585c41450130240c0241e16440c050040c1299001c005214501e01000e80c0d490315101e900000c0c003004800c2c041010103c644e5010b0001380c3c0c41261701640307540e6481040a090082c485800d0402900754400d0000340156168448007600c1a2881c84046a0728110800140e03050768107075a00501d1503003040100900d55502d42c001d8005840c03200004d100c0241c03244c4001d461501308460290004002c6e0540e00c4c1514407642600380015a282000a050ba44400d01c40c0e05210703080380e003540c011034841010080304400300007402c0000e020b01380c204a030100e410b000030140c041d6040102000c40d10b800038900700240f00e42c1210020041d11062800c0c1c03880100d2403d0785400c142000f501c800303060490 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 832678956 1250 832677706 832677719
    0x60c0307020d0f1e21090b07020a0c06050c161707050d0b1308070c06180602011407030515031b030d05040b2203080a0804061824020f070303090c 64
    0x18001448100c0e900c40c00560304204c0040110048a1408802044100380304403651a252115180e02401d1002d80890104400e05200305900c501078009411503200c1c0c903406c5c02181c8190205070913150300c0e282c60b5071303a421508252450284002580e0030980700c40580020b44000034140580114400e4040d501c58955034001c00821003044c83d0080d00107808440001e00c004440d080701440d00b4803808119081039900d40380d083d130000154102c040800c403c4001c0b03031285001064040024415880280800da05825080c80620006031034a41815180c2c07010480028088050480800e4081c046030308041450780801040c00218a0481c000d02a501c101c0e43c2c010302c11011181610740306d40405240c000303180051700c2d02035148100200a00000140403000609100c028001201e072aa22108181000d0500008803540106500c16401000703014400140251000102031242d6007445502c60052203110b030040e101d2054181c0000314001500e03c209074040d070003944664040d030481d020440e222103 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 832680206 1250 832678956 832678967
    0x191d240c1b0a1d06010309080409091104020405030a20040e0a061d06011211040c05030f0606090d0803060f030313030c060918020315061b0c0402070c12030c05060c0307020d 76
    0x3900c0c400701880f101c81c2540b00007040760680041062500184098403500c0f172814541180e0843c040940d1501284000c3c050b0b801c2d00c2c4402c0000840301185000d00d4100001c1d99440e805000600903031491800f0302c04d07026079140125244801178010312020503407030302c09900d42c3d0302c0d414119038251074008082c0210032514103003022804000c004103aa49d08089912008000000303003114401e50f014011200313616030340036409428050342c89058480c1880c0c0c031000c0f46020004c0105004941c14003c00602c1d84c1c5180d4015555508415410b07500d494200c08600501d081503036154052000050b003e407010103a4900d4400c9034007401e40a030315070790dd0301c0c1c0480d1080d429204052252888240e8210010b4841e8001c54000c181c021540050541c84004170711660020500040004040140e03014a14018480c005254100300d80441c94420155a002141070145c044d882c4c821442ea92582c08050055689440f6070390172004460702c170300d0f112008a80c50350088440100500401e0200d100c11401007 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 832681456 1250 832680206 832680209
    0x15010e06041b2c030c060d020d18050c03060402090106050c010e07120c120302031207182d0f0e0907080102270105030f0406020f070f0503191d240c1b0a 67
    0x6000d000c003644030000300300e07031600b20f03860200781180d0800641e003601028ac030030840600204280340411000038248142000c001501290098000c0010000140d48a00110f4191141c3c1c0c14a15280c0507402e84c060700502612224814510910030081180c10841c1d409440303072486480400082a115840c0080c080055007005004d40e00078040e4041d003040b200d03942e550203e800d141c41c1c0003180c0d050700c079a03820307610551101c450001a9100c8401c044041c81c40041e0340c5810740c07858400580341041e8901041d04520800c8404003522000c1030403c0c0e020b20100d80240714070f1000755101c44144c40700481d441102958140c10040e000700c0f0414950052095900c18101d003426400c203581c83d6112000a9030011103101a0702500b0011030b40001d1800f03040d5003c3d02c1c0100001c50700d0341c00d40400044102c401078440d1040c0700140c110a9901c84205010894840c0141c501200c4410001c4140d003264881ca0342d90200914041106503403400006850010a07808000a400d02e12000d0144811121705 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 832682706 1250 832681456 832681459
    0x106051513050402030415051006080a020901051b0102190302040e0112030210051807030507031e020d110324040606050121050606130303051b15010e06041b2c 70
    0x80401c10802460070354040c56100303000e102012641c03092244140304641040716040100e410516080c440281d104407044e52150001808524014111002800c80c0c003410300f0290b68642c1d00112500c005400390180d640d00c0084800c0f680442a8840004e0b02942003406007004888a140002403212140c0c20740fa4802501500500300c00c05100b070120016110050040304100d0724621007030f01c4000c0400104004601417009003c0c0a81107191814441e81007061107010b42d1a007944110240c1d5450319490240b59000004103185401800404e003824400ca080c0d00d250300550740301d2038920f00301110841c891882000d0070045103031540019a4802000e600d4400b10b2443c61400c00c00403d10f644c8425044030000700100d00f00f181d080c42aa0380b50145030001c034005140420350501c400360010b0f0605090010b0740203420100c0610111100c012014420a1440341564022469944803640a4031401c0b0302024035481c0006480c0001c0c1c150000103810038030422404034101070103903d0b07045100c0031400 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 832683956 1250 832682706 832682737
    0x626060f0a150f06111507021905011103010f03020906010c08041202061c06030515010b070605071b050102130f030b06091e09010c090602151801020c060901060515 72
    0xc440241e0801010500c1060007803026215000c100641c110741c144005165560b00d0340b41c82040101c2c4182400c41402078103094110b80d4081c000c820b600070800c0b07030241020310f001c000c0040b003d0519601510150030f880d40e50110020010540d652420303080015070740261003054898540300c004403555040c006014003469414442071201c02408040742680900007049541407500c0074408000900003411092002d80d40e45204104000303003803014110403c405544481d640d8500309192801d1320030380c00010061073f910000074075034501411b540c103481b5445002c1e40c0d601c0c115601e070070382c004d51006440f2510a44441c0b000140b06502d04a03000580b9030243c880c0c9680d4480b501803000c040c0c1c0140c005d03170704840c0035002a012844810b46951180c5042c5c0700200c2c0741903c920f00504013182ca41c1020b4119040002100b41086120a580350854051180c24181626140310b00e402805a1090203089009440a104e100801500301c0303016901c08a41c201d0a5400881c485030039441481a40c0380401c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 832685206 1250 832683956 832683961
    0x110a020c13020f0318010501060504141c1a19062d031704050a150f080621150c1204150f0912020f0c030c090c04090626060f 55
    0x1048941118100a500c6001d420720f0b4a40010040c1600102d0310417810f460700c00c00202c0d50300c0090040a00505e02402c000d8507003400c000310f00781248142210540554901020507140c3e252400c0342a540e1900140c0c200c44001c107807144801402300c1901c000214038040003003068030400030312540c81182c4005021116900407812240c090303060810000380600f107000c0000010400056080300910158494155518241340800400c0341c016008048185e110421030301003140c004101016013480d905142585079150360014080034902c02c0d012450746079014586003c2e42001640e0444401040c046507469901d0890341105030003602007ca100c3c42c2d103030000c038011864200317400c2e00000c400c10300442c0945045d0500815184030030400c5424002c03240140000f90350602c4a480c8051100002e448270b040c0703410000740c1d62240700301d00038813600417170300860302e05084001101c00030a040032082c050f01d50380b084034415442900c03180b0544d0700c811050134400604040340c0b1510900041c0802e80799034 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 832686456 1250 832685206 832685209
    0x30703120213060207060f080601090519031509060b03210d021927140628030c1103120708041e0605060406080106080705091905010e0703110a020c 65
    0xc0c0c140c1142039205a0800402c945262441980c001820310303600100a8545028001030400d06c001002d642081904c0e028014940e80c00015001212800c03500c0d296507075081d000030045000c1940c00141060303007000000c00c0c0d2090b16001082d1040c041c002c01c00006e6052010706407150041d001041c94080909442100541c04c08060220000c40481c01820503400307840d840c0f0710000022461012804100820310b084024a1000d00884811450008624542030f0707440c070100046500d16208030701c041121000c6a05120b80300c003074884826003008444d404020081c0c010502e004950780041e600c0d00340c1005880c40042111075039140c4007503414141d5207040e003c440020002d4001c0b1903041d0301e08040c1e4540ba49540382450074034001c000019203410b1030010881115607680c0030122590501e5010070500d000840c0305400c03a14140c400d0300300c1d991207100d40854a01c25541101da000c0c41c1000101e9003400e4803400900c54501901c0c1041800d005d944481c0c2180501802000180d020010340c1019 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 832687706 1250 832686456 832686467
    0x1b0b0408190c18380108070311040b070b0106020307050a030f120905060f06010903080f07021f02060a180b130302010615031b0305010f1a0d11091002060702030703 72
    0xc05000b000001c030310b00e44800340c81501e9034010344100c2d00c850b110f18070304000148008500210028044501c0d000030303640d40395072418600700000c0606005e40b031000214001d00980004180c4003964154903643c44e141e120b4403030141c201d240c0c180e902111001c00494000e0001048544183c4c100c0010144103140d03039400c035029088800b002d400c00400c08400d1041e01031038012008445d20540150016240850102aa00c0d000500240c10005c1c10039042000c940c060301155180d015854085a85c3d941c070380040381c8420314a41c0c4520050070302c40201c0d10301e40d44c0400e4090003800303426010701c0900c515445000c103e10702000094064012000880d5024180940591001d44030f80000f05070f0310344e40e0804c07000321846401076001203912524204c1c0d00340b02e91b80d03015048002d40d040c208000e504003030b87d0041c01103007809250328002c0e0102e440c0c20046840c4068901c41070884409014107410001c1c000100e8005842003805002070100e1000e07400e0003c41c120f403203500035500850502210f52002c860 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 832688956 1250 832687706 832687753
    0x15010b120f07020c0405070f0e0303040609030b1324050709050a06030e0f1c1101060b030c030901020d1a0f09090613020a050301060e010501090b03090304060c03020f0a1b0b0408 78
    0x83d841642d14801807612070f4001c0e0b41c800d13a155110403000b00303180c0c88064070031000d00280c2407194104110500c903068002e50088141ca800002c0004241d80d168a0951fa06e4464500580040f0301640c500d1020007029a0204c40040310403403d10090b1507050041e102d902d100c0c010980c7c403600000741440a2442035202c008440c02c244100c817105942c040d4401c2c10903082644800c0702d030401e070082c44480c0d45c1220350201400d056400810200f450b040b840705031408090800018040000040b0300507aa00350181c40403803084103001c108080b20b070100e10f1003600300c00d8034850042e12032500318a0286418a0785e00c3c07003115120081d0840baa54100d0000841e171000c1800ca901043d091400b03d0651001d2243c071001d003d11800c2121254107101c00900342c8916544884194030f0100204158000040180e4048404070b0610504403851458203074108010604069070038403d240e40e220034400c0a000214086124041401c82e81d0789030030405000c4d100301d003e8401390307130301010310306103903200c000c11001 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 832690206 1250 832688956 832688971
    0x7080c090c070c080102040501030606050309060714040b030f24100305100e0c0304020301051003120f03110a08150d110906150c012301060f030c11070815010b120f 72
    0x5141c00216a0f410705800d02907042000d843c1e50104080c810742d41c05100c0c49000d40103c0c1041da04501c0d012440f5503480c01b004043da42003029141c64030214880043c1920302400b885071001d0b450b4641024070422a80e421a89013505d0303051503d0000046541404c0703901010400303840c000c3c4039a00c2c40070640282c8400f4107403c924003030041000441c450802104d501503181c1505e11076580c14031340101401d60f68040d0403030b2500303001808104000b0300c0d0801c40c070314a40c1690030074002282c0601c00507801001300041002c0c1003500090542c07070032a0700400c001d01c10001d01171021503514100d0103005207001c0d588002400c40d030202c1c81c0380f0424502201e2082c0d00440062050644c00c0102a0183c51600049402101c5039114124840304a000c400b6600825801d0742d24800c43d989008001000090107540c00c105165844150000d181d124030354800c00021f4071012a00015500c80345503540e07001100d0032040140302e0301c0020034144910001c907828180f0000106a123929611102c144901c009890f10 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 832691456 1250 832690206 832690231
    0xf03081803040909060507110304030b0406021c200406020c04020715060e0a0506030604120e030a05010516080f283801030618090f0f05031b07080c09 66
    0x205001000700001c00182c05071190110f894001440d041050740c1c0c02038400c0b014800341c2c0344e22000449001065404490700b00610b484107440d9800c1003c02071203180c00344032020312030317040440c1d229565810940e1240450040380e2100d8180c43c00306c034030074000d40c002d040040c1c0001c22500b15900d80b9801400400f8000d242503015541e25412580c2125030740d60214891034140d100f005944207991080c117178046403d602405e114079041d0754540703042c8000600d4009110f20320422140ca914100301602240d036011000f00a2400d1440260300d0034502107c01d840000c1209000442c454601c104240c010b03400540d118207031072200d44991038050141034111540310750b82d25102c00101820b01600460380101c0c1c0c50100001a1003201e00d444042d84521541070600302501000507a080e140ca1021209036036400051440040c54040080700b150240640404440007000f000d122002c00186065041d1009007000c3d40d0003400d20303d40f502c0e001d2042040d07a8000100c806824148070040750741c071100302c0c00c64 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 832692706 1250 832691456 832691491
    0x17032a0426010e06070f05040e0402010305131a01150315030206070813090f0c053a050c03060a050a0815220614010f0b0412030201020408061509010b03040f0308 71
    0x142194500e03002d00c3ea42e903101e2414041c0c450b07002184400d81c0c03039591624074641420040c05507000040908001d04259071140050840408002140d2480368000040300700e50b09844408962300300c0a009902500011410403202a402446481030411403030000800413072454080081a402c41c04c42542c0a5100308070001c01884078080400241980e04000680b940c1d90f15034800c11264194443ca09106007089516550042d020508008503811213411111524100b1103081c0e1141101c2d5500c1154208810310017441465400b8510455007078a0004181707a80f10100820440144101c200d650055886440d003014007406065004242c13004907013486c0d50b09803a900a80c0c0c01024291040e680d100c0c429002c8503150070303009005211311a640b82d100380c00d11500c80d40c244118440e15401c42142d2400504140c001c2d01034600811151081e40d00b5482c0011078500d000d03405603038840c820041d81c800407a280039500e064038003482d00010840f0920702070740e0303050361040001780c100942c4c100c05109 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 832693956 1250 832692706 832692779
    0x50711060a0b030a080a0c0515190f110f0d0b030601120f060b09150a080f0d030b0a0503010507200d0e0907180f09141b0a0c17032a04 59
    0x60540c90300554464440c5447c0342005421722040b209650315100c0c1e03460920030a000c85249600d20600e103c0e000065803080d0043c0e56000340b40d0500f034210b101030045070003044041e84a002d480010440784e0203000c00c000f41020151035100901a41d00001c034504001000300b00c0346412000c5407071242200241c0018180005500382c00119030101c0543c1c88542040c8440c02c080c01e0001c020729040b07008010310a0a00d82494498012950380402c05a8455080040399a03582ea50f10050070b028008000600f0b1500c1d00801d1900010151084010303130940740c21101300c0000781c1b800c500c002c43d42d0b0b41c3c0e0700d0300600040000f994400f805020810690400c2000b01d440039095070f00080c044003202000892a00040c20203842c02c64410304513a861610804c13000c44202d807183d228038040c40402d0b96035640d55042c10b4885182c00d03040900b1000d82180d540c1c009020620045008442090703c1d00503440c0e6102030051907207507480301100e10030007e01040280c3c40700b00f61199010003080c821150f60040b03140 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 832695206 1250 832693956 832693973
    0x501141b011406130605010207120213050901020318030a12022b0b0a061107120812010f061421070516120908060f0106051308030d090501050711060a0b030a 69
    0xc0d1821001c1070030b03500303003d460300d0f0014100c10305285400040c400a480d0200103500c4100368031400341d0011042c1482811550b031130701e001600c1000450100414186003e245000750021a1003074800c1e81c035405036121000f8000151441c42e052950341c1450406050000c00294200541c000003808520b80c034603604013200c0e10080c2101200d800001000d180910130000480c1039581f08006010f52000c20b4a501440450400240d03240e02c00001c501582d94a42450544201816031134034000c0d0f08008208140c2c10000ca608588141d42e41c200c2c0c200440e45191b201d44250b10200324014005810314004801c603020141d440001070900c50b0034032590305800c07020a08034180c11a44010303040440c00c40103800c500c5010181c22640020089071500102c2c15080c0034040c0940b406205000c50780f0100c026a8218000c0a00781c12015a5280d0101a880e400604418001141d142d400c2c040000c0550380305214541c108103121004100580351006210028480c0f043d141d40c05010f880080c4001c41c2404 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 832696456 1250 832695206 832695221
    0x618031502073806060a0518060702030703050c0315071215050d08030417030118090c0302060a0c03021c090311130207050303011809020a05040b19060221040501141b01 74
    0x10360b42e8a2000d034500f042d08507658001080c0c244100c2c003d0046065050780441074944030b42c1c002640d8451403200e1400501c6500403014002d5041c4200e400c00b0080040100d451400b03002d0135000c4039842158030300e03144000305003242c00c4800075995404140d1102a25044508454000000c074100580c0324408142420b08054096441450000602080146140ba00030101000070003442c01c65040078034482c1515035000c170341840542c4a90341c04040c0709548445c24000c640c0205003550b54602040040c001ca2400c1c07c2c00e9000d0b00400071103400450300301131032041012a0b90f076000306c41070031980c8451140b4580040c07250041400d503246030b00440280b0080030402e000310015034696161041403c40c0c01200500d64611600705107080d030050310b804c4014002e541c412140800c01d8402134001c1103440b0747c000b1380303190444800d6000082490b004900c400394a481d918400300e02038000407500046208a11510b80025586009000b9500016018107042e010000480400c030410f00300060039100c58 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 832697706 1250 832696456 832696523
    0x308040f020a1a0a0909090b060d1e060e0607030b0609150f070f0528060c030b19080c0f060d0c050f0f030709091a130b1207061803150207 61
    0xc0c0d03a0075155040b074100305c000c1c508442c2c07c1c040c01884d07035103100000b400030303001074040c00c0c0b000010740801c220420311050130351200d5220280040c0fa400c250014104502e207459140c01030501043c0003502c00c0c000e1106102007d0b01e81440e100c0b6000510134100e142160500c1000b100b40042d02e000380ba410000d003100c6000b099043d81c40c0a01d82865404c20101c145045202c50000030203d086584c0c403180403010726006000012540b600000c1500906a260040c50740400c21410f031078404466081d895080e00c0c89141101e928801103400d2285816074280e40c40c0d400f0000303011203000d14a05402807208005107241090400342501e100c0c0175a6000130080c0038128001104210500380c0c00b15440d401441c0180e424048240321544503000e01031411186409002e140f65072981040e01a00400c0380381c40081d040c1c500c1c5200c1c9c0d00e44585c860406004680006029480b81c0002207103c0c5c0c030744000e50b5000a4103009003401400b0700300007580840000c0780c00199208403010400407464250b59040c01 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 832698956 1250 832697706 832697759
    0xb030619060e22080c01090308090d03020c030306060d09050d02010c0e270a110403080306150705060a0921020c030609012706020408030301080a140a0308040f020a 72
    0x3080d800e000c1510040d822014800300e0700070402c0402440c109100d40d2907020408807040100c01401d004920b44981c00c903000d1198241a007030000c055000c0c241c01d03c01ca41c030b0b000b031380c07850201604201d00f070f442058050480d40d803003440882d04600d0114020303e1144030030700f0006069030b02c40d50b50f00c0c20a81000c0801c80541d40d82c0380c0e640d581c103421012810007002c045880a92559142a40c2103103940c1442e00f00c885908440006411146168049051201c58609058507960b0300d1819039810303841290020b02840109280392519080f00068500c5a940800030340140d580301403e000040108000c02d98514403070f108aa003503030a000500d880710b0383c60365014207041303521300c0140340c034020014020010700d0789000003002e0511498030180c6403480703000b1a505098481410003002030300403900034410740d00001000088180001030400d44035482980c0c4800b0302070807401405e0326000f070641c000c1d0100320b0b040001000107004403080c1015520003880c1c0711056465800e107561602035910b03a85620358 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 832700206 1250 832698956 832698991
    0x60a0608150f1201061d0603150129030c13051813030509041107111f0e06130605120708040f020105160b10062c1c05010504060209132d0b0306 63
    0x8100d001080e1f10a10603801058142210305600c201140c1c1481000c02803c000c003520514504640286410f60704002d000c4c42e1641071070383c0192000d61000703480162408409030001a542820381c240004508159141491075641994100701145141c00c00c07001c001042280020542d51441201d11207209140c0f196100c040900d002001c40000b400342d2440b403014441c04035100428060b21100040c840e2030328002840041011030518000c40c003980360107407140c440200300365a00201920304282d0b2070320074881c9034070b4000d015a00890150340107001c0c01c04000015001d540981c00404c065030b50700b01317900900c800946230b20b0a00b0b441a954040c40d240c000c4401c106456100c58100c01e400142150107242c410314068010341c0741c0c50a42100c2c02280940448424a4081032031080b800ea00900244413031318141c81c0400003035028064481c80313406a003d264001a8061103a4201c0389120310340c0c002e06c1150103109410001003007c0d00c041c400d0322400d0450043c1c80174040d86004d50f1a501c101c52004 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 832701456 1250 832700206 832700249
    0x1204080d0501050303030402032a030304150807050304050a03081003060513031412010302120304080715030f0c0c03081b0c07090c0c24020d0212060a0608150f120106 73
    0x807041a071060307200f5802070040c080035a9001c5002002ca102e203031000554480c031300007960414090340024640c0741c000820000340803628070f0440702600341b4a6071110f800b591031420030703a0306000c10340340580342e54401060b020003e070284001ca034000103409019101c4a60303aa4070a002d40303800701c03818075200308050641c90415800100030740700306501e072200c94141222116000352502c0305100191140c1140002ca80c035188041c42142e01524080d4203807100903441e44200081003c00045640009180c00c5800580d861288a800035030f94542d6220391110b5601c0d00c0071a10484007610001d10406800c080d820303200000c80c0205640c03410b031805015920702d400104400c0703801603100b080a101242c0341c58000190150481c0000d0341a000188141e030742d54604010090140d55000c0c113a881c0f0000300e10000c945051344442c441c0004070b5050b002d442d01e541e07003104c0c044416107104911800034001c060035446c098420b220380c0d00e4040c158690b042841142c0c0e0b404d40301e04d40c0c030003101c14a0229007000c01 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 832702706 1250 832701456 832701461
    0x30d08010603051e1608090c010518060f0313110901030b0a051b1309050f0c0f0a020c060412020f0a0f09020a05070b0708071b03020d0f17010b040f1a0a0e0102031204080d 75
    0x10801c018064032681f0155230003c0d1980c840c80448a2200f002c0d140c1401185d40d540c03013035540c6200c40402894483c41e016014583c900d0100e081902c2080d8011203007076642c64040b6006040e2580708034802d480da16100b035141e02900c1c025050075100003030491443c0c82c510500e8050900b41c081f02c0c0b100002c007440c006002c0201d81d405080c1d030032607140303c0b410440c9420b440d50849096105c1200c00d541d407103111180803410712003048101c81d4403840000d1b0014101c1e02d8000e683c0012070007140c60a80b103180340c0c000c1012000c464851f244807402160401c00086581d039014120803400c60415600d410314568035500f4865040b43e80e0350125401c1418011280da0216196004100d03d4280d5504407945860203981c42680ca104c0c0c1d003c225400034240c0c109072040f0700c9603a1502e180f080581107035842c4c10450090350410f00400348004802800021a911303440203480e16504034104403441c0190301602200c007031181c448000d043d84000c21883e00780d88000030f54a0b100300e020707403089521400c440c2c02000c00d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 832703956 1250 832702706 832702711
    0x60d1208160201151401091a03010306051501080105041d01060b12090307030c0f02220c1101060614030601200601060e040204081902041509090b06030d08010603051e1608 75
    0x45a25084c502107181003803d01850903280e41c100315088202020004a4040700c0c02e802210300e807017800229800a96840010b1070580384111801d0265903070740c4812001070244441e21500048045004001c0d600742544680c81031158201c04000108001e500ba5080d60a181c2c054040c202c00040c1c0304910315003d0444981001c65800030354940031030741d14001c0c420340355079030301a01c0f203004030000104540d994018461914076010381440d05030500d0020000501c0e1030200c86010440000544a1004061044800b6110162181e0460382101841840b26400c018449818001c0c0191a070a00c045070b00341c0391841c0080340c00181803640c10107900410b11001a9400d80c09a40148010f100043c00800c4405400507040142081514103000040103172451100c1c000342d41c42400008a042d001903000044128040c01a03480c60307407a480d0a03d0740e942c254007a47c400003480030005200c02d03071103504623541003c000c06800791900144082482d8000068400b8100b4a10222000c848280c0250700b03142d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 832705206 1250 832703956 832704001
    0xe03160e090c15090607020a0b0d050601080603031b01090605090f07090204180c020703080309010f05100e0c0a032a0807140f0a090308131d1509060d1208 68
    0x240c030740c020b0080f44039460541082d080001000c2200a03843d1510002d0700c1134203030001d004a1384299a00d51a20203a030014603080d48072410880020380d03950080814034022680070300214544500e981012010001d0000350341c902e552a0303c0440d000c0ba005001e154020342c0a00301401c80c41d13024541044c0762035899405030604900500040210800040d000d407140303919400c2c0815100b440305400c030705080142d00010b010b080080140220310405510402d10601000070420098407010000301700100700740f0404e8581c8200500240001c070b050000350014203032600740843c0d070050f0040c40a09486107005004400e40c0e10b5100589410b5100c800d0a4020726035040414612001c480e0102080c441e0318180000038000244840d8102d1181c90765400171900003014a4594200090044103107070a4866443d48040681c484030102000d811a00d01429028103d0b5403103a0850b0140112440b000b032140e640901071694100224440c01c0e11404e0702c1c10380e9a07402095280c11000030321002740041c402c0c03 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 832706456 1250 832705206 832705213
    0x2111130906020414100e0906010f21151202030307020d0812040b040215030421110f030406180803180d02100f08090d05040b0d06050a06030603051504021f0e03160e09 73
    0x15200d403108902c0c10b401c25000c1c0b0300704440300107610003911030140c4c1100c2c0081d2403103d40d1440bc1301d00d1069001102054068440200d041c0e500c3c10081c9030303039103080000f96140d0010000c810041c54081d2803250518070400c80e95017803031f424868000c807038103080b40d059600143c280104000c61804480025103c00556000d9085007065140c4a2454401032030b0318429a0b001c240d1010068011600e488944c807200003101c2c3c0b0500118440c907240c5d00944201e10102c0d544200b108400003a8282c0482070b900600003c5040141182940d8110740e0065a42034211120b04452005a22140caa41070b0454090301d0304003100c505120010108500107096410541081c00a01130040d8000200c404440441c070090340c40e000d81403803110044c000c1e035000e035074080c0311504000740c11a01500b250040380d010744240d80440900c074081701d00c45181290020741c48820404070039444420101c011300700d0707916440c003c4142c0625801003440c0c00c1c0060360b82140e407800500c042018403d80c4040a43c88407166015 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 832707706 1250 832706456 832706477
    0x61c0b1b0c030703030b03010b1011060a09120c060b060408030901080c0a0e150c010912120b01120c030b13090c08150c03280204211113090602041410 66
    0x30340c2c0c9074000e0460040070540c40b0036003000d040d94250082d02260300005c0c501140c194130510701030f103400d0041c1c4c021703c042d01601001a058120f1440780c1114244c1080c0384036801c0142d0601200c120385002c204489690743c9981980301616402c0c058405031981c28000e6589042c2c050006d40b0030b240003400c1c66001c00e01040b042407119030104031700780007000980d401d405040e01100300814500554401d00c00359880c20034241c092003610399229217131036160f8441c00d04a810004e42c0c80184c034180518680414075891004685021075406841c202d0b5007481d000410710203e07400503810b0403102d009003818948941e00354081c01075044520000f040b08000a002d08100c8081c14640014010000e5404601c080005510444010110b8401d0304a50310b00800e40071540381210029005030048240302016038200c0302a07004140103088203550060f0000c1c1d0190764100c204480c00c1400503050350308a40302c1c19410f0019001f800600064042c45c0f00c141d000303a000805000d07540480c10004ca04001d909100c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 832708956 1250 832707706 832707727
    0x406030e0a0519031704050d1416031b050609070f05060c0d03021606050c0307080601020f061918060b030c1c02061b0303102d0b03061c0b1b 62
    0x10f0184040c03030300d100d4003c541e010034102501c0c0010504100030701c0c200850300700800c006010501e400c009405c0d07200c00c41c0300c034103a40c2039000e03501aa2600411059610500002090180180000003c20300f503000c0140440303583c03041c4c20588180e42c94010b51f0702c504030a102c12002c101c00c040162030283c802c00c1c24003259011899031450510991010706030300040c00690301c1c01c403880c0703501055000003080c004c42c24151210500d50b4022a10301d8000b0b00c494020810303540c030106001d40c014109800400041e220320280700c050b0384900e900003a040760307150111f2507051602040340e0442ca0041d000010800e0300340d030500d828035145021140c0b19800a4660001154a070760040c0e2030180c041c2c608544400082c0050b007594120391050051611000c0b040001290503400031a0940e2201003894800703040d109250f03810018644030b0000480500c4505008201140303010307580c840d200400c10402402080b81c3d1807144070350b046050b00c560611101f001800680360900b104840003210f029441c00800da034 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 832710206 1250 832708956 832708963
    0x8040f120305061f09120f0c0605030a15050306040605071806080f090d0f140d0f0f0b011b08130f030c08011a0f1018080a0317040507050d0c0305010504080406030e0a05 74
    0xd00404a540d94004c1b810f00402003240f105084c2c0c4003404c62041034a500300039016420032120070f40c405086c500d00000242d0140060070403200040c008140a031641d03503130f0201806000700303d44d08009901d0440d12010174810900002071a160b00c0d0244d15083c84603d9004180300202281000e50103903a4900c0c0555110251810040303a030301c5c0011403030340e10449080c950301c940a020300c40d0a007011140907140c0050744c010900d10750307686030400075408a0401951680e007501e02c8051400d1404c885240840c0015000340764078040e20701c11726091900d443da815000c101a8006450540c030440051041180900c540000010060f0b0680c505018440000b01084000e8482078080c1581198102c41540642100d6002011180c00300880984401d4440c1d0b4801c001d0380194005650064555901c44e071841074280100d4120000d00b841d1410901446040305821104849a0182100000c04103000b841681d01540c45000502da0721840c04600400380c1c1c2d1181c01c048055002a04002e00045000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 832711456 1250 832710206 832710209
    0x1e0c0206160206041b032018060901060c08130e0702060114150a030b0306070e1513260a05060403090b133c0906060504030f0308040f120305061f09 65
    0x170f07050380d22030500441842ca15056039031000300601607104020414145484001d0700c21001a80d00d520413252880006070f0f02c1205848450b0450711040c01440581e114469000005008039640f518141e800101003144c3c00c0c0c141c0c448501c03001c10300c0c28040c0c4282d040c40b4060044c00f4100f81006044202000a40c40001d090340c1c0b800200c000084184030280250403a446d11070f001400d60707140d86801d510241c03882c0359413054903204280240c2083c07125200c52047d034080a10a00314a1070b0141043e1842c521082d80600c2500d001ca460214100500030070040243c5c4148a00d010f8031903410549000b4085460b55084200d040c0703800d114400040c0d0a400d01c0f102144c1015941d4002e4041072400039040d04004414085202210301582035035400159081c003c444030400100f01d00341da0f400049507540541d00004001c28041c402000c0842c0c0704064840d006402100640c42000035139581c0a090080c00c0403800c04645c0b00e50820100b40341003100030005ca0440c01e4600400011044010b0414508d03 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 832712706 1250 832711456 832711463
    0x35100e100510030b03010e0f100c09150207030f08070203070e090c041508030f2101030c03080d140f070201051501050406030504080702060a09081207080a0e041e0c020616020604 78
    0x1401c0d500c042c1c0e18404d4005000250001d00208000d07480700c0796090311000391400030b00c050302c10f400c0602000700781071203010041c0841c2d40d030390300110741020310f101c07100d125114000c41103100d08600800455010a120081c06100d145000c1c0c2d41c030860310500d400c20480d81e03c20003201107054200300c20241c01040c0f041e80060111f6001800d40003070b030742c0010f04800582041e00b282c4004203014400c0b41e0040d0003899144241d4900c0448040c462403560503441d002d003c014460618020104009640c0345c01406801420315808a200711030340071080c0802c2070845841d00803010301e1042c080e015070288075850708440000d1030780e00300c80d68100018000c0d108a1040328105651600080c050010b0344040d154425030040402e592000e0300740300103041450f80e019100450042c0c001c0d107900039100100319100b15a1110502e03082041250080e0b42e20f4800000664000381c2311071340c1d0301d140280c14000d038008032181d40000404140003400203180000040a0902d11003401468075001c40e0000b80f035680c0950f2 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 832713956 1250 832712706 832712719
    0x9041707020d050d02011a0a03170c07181d12030630010501050a0e0103031707021f2403020a09050423060f070c1235100e1005 56
    0x524070118100421050707024141c0c3c003e000100604660640083e20465000315040813495540003c100340040203120080a070030440c3d044003001c140b141e010700205c42290003034440c62903032030010760012102a07502080382c40d614400842485d040307024500400304241d008100d16402d44003403040c0c0f0700c40502121f2199083c400e804000c2c80321038a04160140d0b406140b040382580d0030091038080d10f03081c060540301d8085100c0c00b03d5000c244030b0303102d8102c0740c06a46441624185191700620060b024001c88118028060341801040308442c0c4008824980c2400045292140207424108003021f00c120a0742004d8440030000b50b96107180840c2034031303d49a0002070311707103c915000440c1e50540c0e602d00365441c0843c80b1010903050210384140309054900c0549200e68038070004540305600c07810300404846120340c800300998811f0440b400081c1c05075001c01c071007020484400e9406203140d000041c22030140c504000720101d540c00313450018007108850700090305016150040c00300103405002d02498 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 832715206 1250 832713956 832713967
    0x303031805070f080618060f130f21021b120a1b0302010e0d080d1a030102070501061401020d021f0f050109140c1905070503190207060e090417 63
    0x316000045040c2a40301084031090b41ea0b0f10800c14500c400b80c81580058050240000c45a0240014500c41012860301511555032101c101d19404100500034903402c906515102000a90b440d8001c801c1d51702850382c40070381d07040c1003074400300080880c607144c402c6410075404001103980114403203103507840898440000c482c1c9290070758034081d500c100181410f402c40840d0460349a50340b2001013500e00030390f658100368251406001c6456146000206002c00800404094403031a40c483c80c841c0c15800c12540540748100c00007400ea03000080d040c2c6450b59039440c02c10141c0c280b21043c803e052303005e0014110540100034041e4a4402c48a8040315180002070f02c450605e44590001c4001000c0d07800400030f03546c4581d2000000d206150003215640036801c0402d0300383c850032042e6a02c52100062101d48580c032035004480e107130004034084070140300130320240b0346541221400316403110140e0300408030245004001410412060105400303083d200c0c09110102d020425000c02c030030356602c052503030344 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 832716456 1250 832715206 832715231
    0x3070b040611041508060108060a0315060306020a0f02010b1816140a0806010e04060506030c0f070204050103063e0921070906080c0f040510030609050a03080c03060a030303 76
    0x40c2161080210710250000740400e050600b1291904644c1c496a00c01005030782c0c00300190782d280c1d03064075043e0384000c040c03504000280c0683e45044040009220128440d562a6108800c0c0d0f003094009034040f80400c81c0d005003540e424800e0308250901190107041410804551000500d00504002c244000d0074001c130032803138012140032a18104c1d0030000c0e90f5a03030150000401001c0140d80c1140080c0c248180e03407001c3d2405d801500d0540f203005100b1403440d01e0b0344541c01c509902c880880c8818010074400318015a0300c80c0306060003036003d00000b00b14208100196040341020034a101450380071116901da4070006aa00c4050101c20711104541d5000b0101c00604401181c1034541c02011f0344035255001d008001c01c180e0210b075400e8005001f02074076105c0c01070315014106c0c1400d0b00134842428403000c510b030542003160040440f0701c11100d01d945030346441d01603503141c2c04140d6203580308410031010180d01c04465a404440c0408150850800d400001c4119031030780710290805803200100c0740700 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 832717706 1250 832716456 832716461
    0x50c0a0e030a14030d0f0c02070e101d1503030c031225020c01020607020c180c0c030f210622022101050301060f050306040b1003060903031b1103070b0406 68
    0x1050b03008407200c2e81c80d0004035040f40d600e6001002c40e0003914103100ca0981081344074003030342460188030740103031144e0f50601d1040c0000880080081c24416042e16001074a0002280503642e050030910b6454042d00d81120210401404480d1250280e44100201941c40c05c0120644601c01002c0c1c5e000307542038580281505a09600d4549a103c1e1080c009402410310703000a070314003c0002c01c2c0c00340d030340399501c0207003d0ba110901c0c0c0e40c16541040f82980c2d02d40c040c400c031407900c075803000d0781900d4a401c24400301c81280c07440d0070494a03020900000100f100d070032a60114690402d0f0078903691401140b40c80b101003a4242c258603038407200a840340c558001ca041c1650140d9621340b100c50790303c0889080c030201c4403001d01000e119141c069440e1080106c1c80b010440800401c0e80c502030003c05103134640e903482a41d1040e00400c2e500703c0c480907031800300008120340070b17000c0d04c540607036004180c8030140c030688030021b40348410760000c4c002026500301401c4000b00075144000d41000e08081c1d0769070789040c00c00c003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 832718956 1250 832717706 832717723
    0x1a04050a18060e0a050a1103060a0b030a02040f030c06081b041217130302010e0907170c091507020906030d0e100e1206011a03130204020705011509020903010f050c0a0e03 75
    0xc90441c3e50704019410905612451040c0f00f0303000c05004601c2e1040d8072200710310094a96035000f8192250a2010352001c50055401c15040140146440c0c1c0c5c51074503c1700380303a0b01d80086405c4c920041082042541c840c0484d908511141c98403003541d500040b00103158461072044110948868103503405106442031143c03500c0711000c003e5a503402c000d10101c0b0340c403d01800104e011845107180c140b00c074108888203d1054489880d0fa00801d85180111040c0300381c014030300482d00b8005c100101203a118600c030382c121071015064503030300c40206104000204400610090007584800d03801c2a020b82d2092044005400c261114131740f540e1410012240105412600c0b0740184c13140c44426201800081c04070304a0712154801c0041d22228410310b0410311080e02e05411038000d0742c0c0c0320000f5150641c010b200061082c4000034004103182081c000206042e4801c0011540c08503170400c427807e00f030081d142c18480c008410085031900000880860003418030360800c2201400400400d038404001805 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 832720206 1250 832718956 832718969
    0x2031303050d090905090703030809161d090d080f1e1503011b022509181101020a0807060906020906160218130201030e100e071a04050a1806 62
    0x8611a00ca007021591000c1502109000418a040020301c24030248106802640003c0280882a00c6c5490442d480540900000e4482c0145508204440110100a4010448c2c56400181542c0120348614040d5000f020b084258100d012490703d5980c0c0134581607841008443c601c101d90b105c3c062007000080740c00d810f001c10820305d1002e0040d207806900e50700c03101840c224020706c40b290035280c280341141d4603040100c02591085030502200400c000d1003002440203c1c07000302076207940d0045603095901d8040070b13102c403c1e00c0001c03801c180081c520080c41050001e000404024085682c2c41c0c80f2481004005010f37965280102d00800032150101c035441c810080400c0c1e21040998004c035400112400c04a1040c000300c0758480319110000b40c4280300f81e10b448108880c2c4c5005d900194040c0c5210300c030000c0036002d40003600c0c00d00e82d41c2d072052b03d90400421001b800d509080c40301c05030040daa08007841d8100c20090104001a60b2004a4542a01c021910046d000281e400418000d000d407900f000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 832721456 1250 832720206 832720237
    0x203130803071b12030815041d0610080c01110f0a08040608060f090a0203040c0e0705040906080319050c1c080f060409020907200604031115090c0f010203 68
    0x2010400000070b002d40d10700541c1c1881d440859103400c034a41260720302c50401e040135041c0c0d001021034000c0d44110b07400407a052a11000b02d0164001074103c441c28103281d106081052881c0300038140030001558400304bc0c01906400700d050250b965512100c40440a040007c40340c0241c61081c81440540300c184501400c0710010f542500c3d0100d80c94000c1d019800004410800040705450703d521400c1c00036034080c1c40319010344c8030344065801940c80104159208a0940d0000a0000384d841c907840c414446a901c6944032070500880c14181c1781244d010080d00c0d8005d01c81440640da0041601c04201c0e0a410407a81ea0801c02c0b518900b031100690044c01c1400031849e0940c480c907004210f00b4400d030303a400b0303a14034565180350801c4115000820b0103508a01032000166000d4004c440e4403841e4034020180c0c0f8030b880140d41030149440c000b140c0880000300d9803a29408c81403003c00c00c0d48100c0c03c41c1ca4104a191909507944d5588810f80b09506108405414002ca40740e4000e0040b1941d02c88010080b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 832722706 1250 832721456 832721459
    0xf01050904021b0f1f050a090506090d020c03030301300501060b0d0b03012d1404060911011e0302030403110319080919020607030314070914061216020313 68
    0x303a1010701e540f04100f03a07070b500460b00b40003200440400c0c2079040c602100014000341100e44000b0b0300414008140034041d5070342c1c25a10000ca1010801a88039080042c010a02c20000c1d100007400e001d40c03564618000c1d0b009100603c000705001c50305403494403c03401c3c0b01d1000005450b0019a000c204107010740503510b490b0003c05c2c03d0f8981360051000e203014420502c034a00854051500702d0728100c05030420606001c025444203d00c01c01c040141f590a900c010a0084655664400c88141501d0843d400c566506081041100040304502200c1d000d003440c070304100f03544d4415032103d01840c3d030000030558000005000c150180102c0148104d40c441140d4807100b0080404c0800c0c2c0309a07414a002c980880c000074589400026103000903850112008042d903074980c02d000c16134103c101c080b01415160490503950b22040d1044510923103a50307959000081c5402e001080010000c0001c0340142020041c0303101054200410541021105030322541c0910340d98004c90541c00343c9042c100140c2d041020 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 832723956 1250 832722706 832722727
    0x10513030f05160e07081513020d050a090206160c12080705060c0306031b04020f070b0a180305090607050106032111010218120703021f0e18060f0105090402 69
    0x100d242100d4072942c1100d040d41940c20803003024180a00c610b00041402c00c0c0041e000ca4443c580f40c58011101d10354805103840240e000800d01c0580200229089a0100d07004030110140e0140c1c0d500191011070400501040c3d4001c12002e02c0385241c50042e91000c1c403d8681085090548480244021001d124611510345002c0c103040e07000c40015641441020b02003415494090212405080000c1c0107180c00c5c49180c1c00e4154403881d040c501a1320079400d000c0c0070314101d4500010901540b04214481861600e00c4401044a01c1040010072088155500c100029040030441d1303005081200c845859401a1428034098070741a040101101d00056031210a203034140780e02540c18505484008050105c0e4001e50301303d020300030444200c102d100c00700203218103001a8140c41c4042020503164100d440b90041404406000041c00029414400002c84150b0200d01d01c0340d4101c04a50404001170414024070f480b52005d40041c1c410300d43c01100f144a44e004a0894480c10406041503445035907080 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 832725206 1250 832723956 832723973
    0xd2006041503140f16021203100303021b0f04090204020c0a140c0108190203040c08010c05040504050c0a0801170304091d060702160e33100e0306130201051303 70
    0x4040e503001c00c0c1044142c55030300b51026210340c40344c8518118130300c007540c9040d400e200030051012074a095004a524804007501c0040080d1311803403000303034034041007461845e00924010785484041040500102e840106070303200d88000000d00000c560200d20300d81680001002031045215440481c03140a03c43c0c401c000941580c1034070301c5503e5050710508041c00005507229201200e200c080301c00c01080c00003865034103a028640040c00782400c805096151464582190b0000040401040000c04c0420013850706025456020b11000845400c0001075000036080101c10f01800e603115403500c00350403420a04005540040008440c1801a20551040032410f13201c242e01c43c0d004c9000d820009100c103800040e03401e500d0005800303110740c92480c01000c0c0d01c0d5030201070000a00f038450064813004102c2610f101654191000140c200064009401c010004c9580800c8105222065901c400302cad541c042007003035000008003ea42a80b00c0d891004848610420540d4080040e038240003000b40b04540 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 832726456 1250 832725206 832725239
    0x31205070308283b060414032b1104060c0632040b01060305090d1d1f0e030c06270603040c0e0c0f0306121c0302270d200604 55
    0x142010006105054141070b04c06802c00000c010644c0804082070014401c48054040481a0b405a0f41044111400e00c0705070704001c1e4170300c10515100307104884005524490402900e00c19001c40745050b2401d800074240c51003250002e04000c0d9034016425079441c15548011800342c800040b02040c1c014850045280c51f4256000d0350300d84824030010946038041e1140a0041484070b00030840751407450021664918002007000c0358004404502d021600c0760050f6491a014850705c9072452400150010044c0180821003480b9500240f900c66490b01c80702c040b070381039600182d070086000348407010300c400300003c2c4410503811003400020082440400400d00c4262900b00d50004e54607140c1c00c2c0d14031004e0103280d000b8541c00303400f000451543c1c98035940404c03011841900781e864140034403d1001a0002650140340800d800041004002134492030300c00d1104e6840d4481d040e41d500c0300e400b01c0d040d1030380301500510241c6c0e02c40c491b485241c1050019948800020187c1e940d490b2120800c880e84000c5 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 832727706 1250 832726456 832726511
    0xc120301081e070506071506090c110606090403050901030f180305040509071404050607230606040c05040b030127060b0a09140f100509030105040c03120507030828 72
    0x10450904110001181c3e1800300c0304024409404e001e0300703072900000c0828440001510960354000000c003002540036800303041d6415141e1a842403130301540581821001030050b40700346404c0d81000006078001081e2a03452200f0301c1c000491207006034650004040745200442c802c001419a0401c0545c0030300208151742c0155500e41264035003500540f601c1d45c420b00b2540d07209074284400c0c0860b09041028255890041c0480f204640e02e603038110035152094030740594036030040300400100742820300840100e0f844034903043e0324051800144115034001809141c070201942007190512854048012a60100c01d61041041c990365601030b6440c1e40c85030943c400400c224650006a04c05203d5819200c200003401d00041800005e00700005840000710346414040c0510400440751002d210382c51041d4411074040c41b40c3c80c15420b098607030760000001c40040003c1003007800b0000354004513841c0c00c507001d605a001060f2004802c42c50a00d01d034140c08107424074202c104150440840a0000310300d08 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 832728956 1250 832727706 832727743
    0x301230a0c0801060905010509010905040203070806030129040c230309070b040308070b06010318050a050606040c05040e0c09100807140901020a1e020a030b04050c0a06080c0c12030108 81
    0x75003803040d582c5400034070591000c201169020805940508000c0810f00014541f034164681c440d40010120b800a580d1540025140b404000107030500344954003001079102c0c8070541e4500d88407103460340a0301b8401054004d940740d5514584403405103101d044800c134442d030380300300c1e010074041c1006264208450b0f00701d40d0300c00d0910019849541800b00c0e020740380c12135811450f1407000e031102804424082d01040c100340d6540d149160300240200d03035002d401e101d00003404140740c80b0b040c804e10b070080c040c012300c1c13189181404103140c00f0b8000c01228129030428540741c03115503581921a000d802104103540d00440d50140041115074000081ca10485d00d507221400222580c8001058070b0144450842c0940d00804036100031840500310364415282c1c2d10b50002080da40c550108401c42d449910444001450400f0312040103130a02c00d5902600094441c60686460010002d241034030141606440800003d0100358600e01407100d07859081e1140069a900c0d6501d424140e0340c0c00300648071001006 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 832730206 1250 832728956 832728971
    0xc0312070c080901030911130f15140d060204090507050309190b150f0409030905090a020705030f030402060702030708160e0108030a0f0504270f090b0a0b0301230a 72
    0x14041c10800700c01a030048840750500030340d00300640041507201c1094928036641d54228255a03681a5180204100e26a01103011b541c102e44410a80c0c1d170059101c0502e40e0072040c10f208a00000c88001c101c88811280c14106441c9400c2a400074802e64000011940c180300030050000d030024010350290440c281146d0f498550078155214002102ca002491040310300e01003884400c0d0351541050b0713039000511240302d04a0030000503048903900641200410081c507c100704914120b01707819803002d5030380810f6180900b10341e00c040d1680f04601c420000000c002c404101903440e00e000340c40003d9400703000c40e4080c0e915040207580d5030910785803861041c0c044410100b40310f6411810b2a040310f02800007141400c80030390080c3ca07030340700744c5560208001003444006521503907800e07484618a0704800021082e00100c880c0030a6840c420301900826040c030100c500041e040842896001c0311070800000d00072020000a405443c20300c1c0303018402c0e182c00b0b42c00d22041c0c00740c82c00580141201c0b03100300080d4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 832731456 1250 832730206 832730221
    0x121a0603030910030506040e15041a0c070b07030f02130e070c021c03180b0a03110f190e0d03052101120b0604110a050702100201022a10020c0312 64
    0x70700c25a044a41c1103c2103203240c1c100c2034001e030880c94104000070800b141d04e01b295601c851034008610010300040341c8000030711080c001c9001c0c11144003100b05040d44043d103890289e0641b01d200c2d07444002c00e16100200080e035514030a40c00b0020a041c1c1a03030540d524001c0c50101001c2e002e05004464226981c10301180c140381c02044e10081d00f079406410605c4a10030f60a41c1482040118819001c0c0101c1c43c81c101034039420030000348094812008001d880d680d04400c014115042c0070174140800b80e0400c440150000740105458014007403900440084840801c00c40703400402d070709419000720001807103108154000000d89500800d400340c1c241507000b2440c20381c40840c07081c031490b06200c4151007107101203501c0020700703a8400c40103480030680c50030402c5000b4541e130011440713200240000c1400400c61404003103001d0602d205100a600700f00004d180303d1038019680c100e19100c40241d0a86a040b16414000c02c0d6100c0100f9108545841300d0343d80260b1130b80d2001d80314903030b01c0b0704510004002 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 832732706 1250 832731456 832731463
    0xa05070801150b0d0905030f1806070f0b1801020415080606090a0e04060e0d030e1903080114010207181509050103030507080f070c06091d0609040318121a0603 70
    0x1100b80d042d144503034152421844070b0f090b0740144003002009454040c0007021a00030401401881c030900c11a9030f541851b130360005c2d003240d91580c0b030300d100d62402c000450206104a41d280c40e100e070844460303440c6807030b00030b500080d091400140240c5540045070009003c10b0500c0d24402c1520303180ca0340e00c1c0030765a0302c0400403035110f10000c05500610220003800503c000034201c1d070f4841c2c07140500040000150f03c5441c50200300d0210200000e44501c8003000c03842040c00f8501d00161001c00c014011062590003030a81c0f0014002d54082441c41c192000c810b0b0b1081018400030042e05545e4400b041c5176401d0a80a401002102e10f0b0541c020b03803001406000c140301d044c2c1200d42607074502e0309200c026503c0c150030303901140e240c2082e45014406c0e04040360301402010010101911000205480d0003042d0558886091248041c41518010444035480300c07003905a0007585854000f44040f0364a400c241c1c01d13501904546e181009415402c02005403080100d01010a070820f114150f903540c4042654 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 832733812 1106 832732706 832732721
    0x70b130905190b010815040b0a03020603091b01110304140f06030720010c0c0209061809010b210a02010e03010e0a03120501050907052d04080a05070801 67
    0x4030b406403190841040080c2010360043c5008010030031014140c00000d80a180c507080464066559a8180800345a0003459161641480c60381ca41c0d4500f000007000c5405407080c21000b50560040000c40190140310008601e0182407550011040c0c441f0311940d9003016030400c04c40c5050391400080e51061400d50740c1c0392404014802d54482c200c2c1800c02100f026407500c40f0030314180d9030001c98101580d8054442d011181c032000d0225003a980040c0e650361040b000c02092115822040d0802c0005c0cc3d0221000c44940f89111141c11820038116202245688002c18800041d4015202e050302501d005000240b481c80824450f810000540000c5001030003a90202c00c50005901ca610301500d4245c0382c0c0d0b040d40c070f4102c10280c0140300b4050000c9044c01e40d60003414400f455882c281a80c1c0d007547d980c003034071b031942c1e40c0201d5502c800131003040341c1e980034507080410158014400c010 = true := by decide +kernel

theorem cover : BRFrame.Cov 832553956 832733812 := by
  have h0 := BRFrame.cov_init 832553956
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 832553956 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 832553956 ≤ n) (h2 : n < 832733812) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
