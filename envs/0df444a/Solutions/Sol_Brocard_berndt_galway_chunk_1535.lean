-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1535
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:26:55.819415+00:00
-- url     : https://prove2.me/submissions/c0dfc581-c115-43f5-8135-0d2e6dc4d4f7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 275899280 ≤ n < 276079136 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 275900530 1250 275899280 275899297
    0x3060e150a1a1b1606050d06050405041506060e180a0605090903040f1202091305010e0d12050c0a02121c021305030c04090b180c031b0a0e1e06060c060903 68
    0x40358403226800c0d41d030720390704c44804005180050200c5410b020991141c0300400d40c5005010000c0381050311403001500f10307a81551700300d40d22141302e120003404080f0350040600514440c1412441c82150307102040790040b8096808000c014414001620440701d82d101c10090000944601c1e00c41ca44020200e40e02d51090160620000200600142e40701c0707034680600b1b5135a800b0303105540303d0b100c000b07040e44d122024400469081d500c0d8a00900d0005041100305400c54903983c94040e0101c1040707030700007100c201502011810700100011500f03681c0025039070480c069032140555803022603e2181b2801c00c40c6501d544070240c000111000600ca03c0401801a2002142075070fa030b00703502000300b004440885100401c0300102c0d10024901341c02858642072949106000d60b42e00500700ca00182c00d000a88a1482c030100030108644000c0c10002070140c0078141d070030381889a9047c00716841c46003a0745904640000c2c0c01e40f8000500d02c3d2039040c1901c0c4a051110100c500504096000f00d4503074115013070 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 275901780 1250 275900530 275900557
    0x5011b091701020f0a141e190516020105030601021c030f06080a0f0210030b04020706060303030c08070903021e090a0e0c0103110702040b0402040b0406090e060103060e150a1a 77
    0x24410401c0061080358800051006101e01c1d14507031240030344520404170000701c5020800d0121400c5142e05a0321080c0081a09454a5031200c00102070710016088400f0b000c00c0280c01d00000e0203001460180c01c05098090078a981c80c0c0d918100102d142c4a00d00e00084542c41c2c800d504641e0844e05074115070000100304d0b030180702c10794880000b00d543e01d040c114040c00000c2d0b1040c5040c0036040040311091403071024540420b01e5030107400450300340e07480003004654241e910749007002890344c940700d0007200f980d05152044082c20000b10091107080c090001a100c0d80c1c0d6500c0d0a0034a00011085980000024013040c400c0c0c604102400d00034000c40c510400b150040075401c14080d8401d21444101d0600c0c0b9105da4103000e2300c2c0d0240700080500101d4a508580d0801012901d4120340c1c1c080d01c02040c260769a41c900605001c1e4801001c9030240c0858180342c00c000c010b1080c55005400e080d48845a1201001030400010009003080300c15840700e0b0744902c2e00b00014001e90150402044200c0301c0c00ca = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 275903030 1250 275901780 275901809
    0x11b020309030c0103090206070b040606091e060b0a050403061a041112010b090a0e13060e030a02010b0103050402060a08070c0b070e030c091b071103061003060e0f0309010c05011b09 80
    0x15004d554a1b150004d5100c0c0d41000260002000b598409130002d015010016001b0707160507500c03085600c02201f0890030341146c038030a100302400e4040d40001e0711600e0f1119003040c1c02140f0140950140b80070090041d0f44849110509109190503000b010200070300901c07200b0010442007141d94420580000304451810020500702c92a00c01c0b240401409442801c4007445e003100c500004c44090300d00507000f10003003150320114203580150b48020a103007004d15030b550b0380c000f4080d084483c106c40c40360501d03007004200005a66a502075514200381030614081c00d9962410403a0340039081040244004281070a1084840d4400301d0440d07003041c00c2c3d0448040c20300490030081e90600480d03000740d0f1008540030010700c000b00c05015000c40d034400c095089185003404002400c01c0c0e001c4802250003050070108000744249402080101a507c4010f04180c2100708804c648030b120f040d54050520282075192420414250b003c5003040c81c05030601c194420203403800070f0440c8002c4c4112403d01c410003 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 275904280 1250 275903030 275903053
    0x180807050f1f0221090115170d050904090609110a09090221070b07030216120f0308070c0821091515130510050102071a041205011b02030903 62
    0x240307001c0401c0010442d0388800903030344100400303544800905880c5050003c034118500c0519120301d801030401c2c00000c1440551107004108a0f1442d40c070200c8800000366600b0000200461103403440709540c6031540d514584907000c60042d0103000d03030080002e45004407600070700000902c942d01d4100b0490342058215554400354007900d0707120b1406035000c48203c14041c0080001364001c0100402c860940f500d09035100807040300c0d908020405c1e40513170040c0000034042c00c2500c607004098424242c01302401d2003a038499059002c42003100606000071100490341240c00380c455800f4080e401b1030301c550b450309802103000400ca49149400b104115840c0030581ca1500071541c030040d41039100401030f16079070345d016a01404019554032608860688030310ac88410381409628400c0e0a14108040c40621345000286044859408040058402e094610a6170308200845c2c00b00e0f540c907407140150701442c0c1841c034010400329200003032641c0500c3c40d203600241c010000c0c00c40740000301e0a451b00280403 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 275905530 1250 275904280 275904283
    0x304050d030f1e020c0f121206120a110103060906030c030b010e2a0913090b061f0302030c0412031214010608010e04050c04231e1306180807050f 64
    0x803440010300701e10301a005080f061150380c0501700c00f00c52a0100c2c3c8504a40d104280d003080390349081c5404003131000079040402810708020130380141090340d04203510f48170310a042e0303126000d4082c01006025105100c1034980c1c4a0340180d0040c10b142e0340e04020b455520702d0202e120744401d1000300c13060040040000b407401344c00304280f440b45404010088903500d00c0c03c5142d0b41040920140400314500348028030007610707859244004014201c00004034920b090901d20462840202001d220b068a04841c000a12901c42c480c040a102e50401584903201c01c0701c0490180510f030494194034200ca0410800e06611005002814400c041c04103d00c0c203040044180802c0d09011707640105490100407c0710000460307540b6402409102a24545c0c2d0b41c030f0001405640c02c00d03451000c000c03231086c500440300d5406150544c0013001c554420510709003004800c0b9540000500700303501c522f0f07000784181c1407280b03d81205812003031402d0351383c0841c03403145041c072a0b03600000e40507901d0b40324254881d4140b040 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 275906780 1250 275905530 275905541
    0x907171204051207031e05190809010c05070905091608071202010f0c0c0b1918120c0e0a1e02090a0e1305030304230d09060f0302040b0304050d030f 65
    0x2054400c1403506080c1002d02c900c0015001030b0071881e20418078000089441c01d4a012032040000450f4515500d0505000b0714218101c41d401c940e00114150003400140c44c4400c4503d050000e09060031140b40900b45a8100f980a0380300d40f4505040ca810407107602e0740456090f2a03ea405c120751407500383c1741c41c00c050b03480d18580680d84500000b001180301540c02011510442d190034502500004015542c55a1881003030740f140007482c8001c1100000b4082c4644501c81c045a945856285044100380a40280016203e140d8840007903540715018070150141c10000340c100b50403031001c5400d2481d40d0074010600128040c203690840b90070795806d208180210f0b407003590001c0c04601d941d820000d6255407000301a0001c40401181c6400d80000344091020318030030350003000c10000600200120212201105040f0f441c1500403803d41081c2c203401030305050542d44245081444941982c80503002881143c02451b03a41ca03001c8204400c002d000100002818404c0d40c0520602030340c4101b44040c0c48 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 275908030 1250 275906780 275906803
    0x6020d080106080705130b07050c0f0d0209061201020c0d0801060f030c0f03320406111201091a09010308130b0309070314210c0c010c02061903060b03090717 69
    0x2115003020a07541031040d03002c0c00326440d060000c0d001b0180e650040c1c50140e07004030012203080d04180b200440c54030b0501c04418500e00b003651111140d009550000b41900c5004190728400d00720410100c01c0c2e2042541505c141c000068101c03064014400300140448009204082c0090f07000d10160708240d203e030044041d10145600d940d40203869422054003e0700c8040390072110519618401e0b4032281c0003c3c05800040c40c000040c49050070329003440d80c2903071904031000180329801c000d90800620123107a2541190710000000507903a86204281180003602aa469400040400044280180d50004040b600010644025059614850a2014041142c00000580205408101040c156001244000310080c10b41d118181c01c2003035201c4502c0c0800041100003808201c104031950100700300e00c0516024280080a0222640028240d1096550005851188400090f4182c1c0a90808405862201d03907403600c0780392400200391f4a0782d043c800c500f6000b082d801c003c8080e69000c24540d900c0d1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 275909280 1250 275908030 275908037
    0x10060501020c060304141507030c0201230708041401090c080c03010e210d050a0b15030f071209060905012f040b030403090b0c0307020a0902120612070302091006020d080106 76
    0x517521341d25800d09840c0804a04e0485014017601145107911012440388910b2441e02c00007405480484002e085894001e6600f0f6244600300100f01d03030108101e01554401c0aa1910070915642c61a04140850101602e2a8103600b04454002040103e05c9100203464010044840c004042c204050a03500c42c0b16840100750440c20860f004901d103a20410028048544c40d035182481448205040b210200d500c100029540c20400301d180c600001105181c4450a440600310300300540b81d2a404c80c4050a1b0000f270200807050303143d80d00140d82010306850741011041140c1465414524040d010700031144445000a0001e819004041159000100165000702d402c10303080118194003948040c001f5410700807446c40000d68403100340c2c0101052821b41020b99110a003d2040c04503101d81174025007070043c014050500917245404005074016400c44c1c260070203001c1e00d8280d40c00c1c82c09681001c0e410140107000c011402094010f042c044072419801c6452031a10410102c032000000e0280320b000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 275910530 1250 275909280 275909287
    0x11030a0f050c010f0521060f03100b100f1205070921110406080604020603060409170d050c0414130f151403030c0d030c0915020105100501080903040306092310060501020c06 76
    0x80c04081c110164000f4001d008d20f0301c0750721400f00080c50061041c41c40400d00e51141d65a01c92802c0c0030f004c007d681a40d0382484003041c400307014040c08540c14040d81482c21a507600c0041d44813441580c014009140f0710420701e103e0010141605105088202c00b80c6112000d03d406c1400d0f1f0a00703103e0001240c9010028002503100ca03401c0003440d92024120542c00358680000348003040c0440403150035560110500355490400d0100078003a10710007040420221420b210400a0b84402c3d0180b400b01c0030111020340d82000c0f1043c641f0300400011071410f01c824a0090b88803084803019402a0039900c0030070940d1180c46400c0101540c80c45481805c00481e00406130403110035020f6004424524468281a84115107030f001d06000c16850103a031034010307074440382440000412003640501500b004e2034698079a11b0301080c0d2a40da4810fa200040041e50344002d5001403000d40d118103505074048110060340a403540b4141607039011407003204a9050320b8100b000800d5070002038400e0140354050b01c079905 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 275911780 1250 275910530 275910577
    0xa05181207020d060c08010801050703150311030a1205041404090503041a0403060f02030f060d0201080106110313030f0510090201170403050705121b030c070311030a0f050c010f05 79
    0x503140c00004003280c1150401c1d03030705030000d411805006111190fa81d14842c40d90325000b2240e0940d5030203020380d01070526010401c0d40300b89058401d1029aa04030084d162010360f10703c046480e0800c05076018004039241c0b1720340c15501e54400300400456090318040944106c0803003c0004031600190000d04540c42000100480619211240880700b0025000b608150307685e100c4c0c0080d035039038a030030322940d9138004100200310b0100c030441381c0c0000c402d0302c00d0180c0328803d500103094036006005400c1481942440281c00300802c00c126004ad05101182409140c1d070ad1900010349041c40710222011300502d072501c41644d22910a140b80e4580503503039030b42c00000038841d9501898018005400b046820041c2c44082b0b4010000c00c1a00b0403d04032140c1d4462141c0c607030610000301c2d0800007460750010443c0b501851300008000047e2900700120040c00400f250019207006207031440140442d681e884540180103002c540d000c000d107020b07240c2b00f1404140240c00c07141403113500008607184244420141 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 275913030 1250 275911780 275911813
    0x303090c0d0201141c061401091a04030203070e010302150c0c040f0204030b0f24030307080307110d02010f0606050405130e010b120105240a0e041502120a0518 70
    0x300d41c0350060400030071030700d0042020740c2e85030f00c0b0340c4141c07401c24115007000c00b104416204000082554030100502c43c9510310000b0452a013038414000450f19041117800ca0030700500841c0c008550007003c4541c826a00d10b90134071046400d01c07099108414801c3c1c038a02c80030b03408040741e581c0712a640c0948455001c44c000c000c014800c103440301c000c66500b0f12003c00001e40b83c110590289106020150b80ba1500600c030340703040a400000e00d074401035103401e04c2003903403000400d480d8071550140c50180c480d50f500c030b022540003510884008251290080d154090398040d406117043e9180c4d804113100c080d4841400303642c944101d105898100307481c1e0010007900d101035809014003044040002c84c5001500000868030f1034040d0101a10b80d540700140442000340c840750301c021417022140c06801154403000660035030082d01c108085034142000180801640d00140214540382840441d02c8a8034000c1094000c4411680c540d802803518000c141840d10080080c940c0500050040110400303492864 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 275914280 1250 275913030 275913049
    0x30609040f060603150902032802131b0507110312090904060e1b0103051302060f0f0403170a0e0a1a13170109260a0f1209030305180303090c 62
    0x40c2c59440d42d50718040001102c0c2e44103007a21024500001c105140f2500425041c0503050041c42100700c0f040c059002280c203154001000160111442640c2214001d0b00101801707403103500c0d0003040e894001002c11581c2040c054845e00b40528a8007030f141c1d032400c0070b05646180807407180401034000d008504231132910301c5110ba446489400f0214045c410001483c0c5000c2484040804204030411070072042d503414415079500159560a441460007070303801040d500c5c402c42c00c29100f0200c00184d0102e0032510407040300c000710303480018415100c9002c5e014a503260003250b00800000da80681101040c640444601d0550340a0f603240c10705606181d61286030f80d4000d40c244407005116560004594000340b030783c29115121071f000032035520a41e00d460f41900020100050b940240c03203203400b400042e80c40503208a01c00d9070500c00c059080112054400c1c07103400f2180a031403030a01c1c1d41c1108044d40740d00701500948207054080300a15000034551f46a010803910300c0020350280c801802c0c1841c0040d1038 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 275915530 1250 275914280 275914283
    0x60306030a05151821161e060b060a02060c0904060f120302010506010f09050906010516060b0109120305030a050c0403141b010c02010e0120010f0506040c0203030609040f 75
    0x1c031148007100703555581c200080c0f00c03040264000a0b5080103540a02d40384921460311104003e402c4443e44501c18444260062032148134613440480c4411480303082c0c400800d1010b800c407900002c4032400c65000442c0004248048a00b1402e06100340c0e2103050040a0390701d4509240c024245030b58902501900c20307009104103641c402c0c1c82d801c001541c03e00342c02d4044050f010f2a60700440a400c036040c06400e59030003500301810004041d00202410307502c510780c941907400440d465080d58441c00012281c502500601100600500c200e12041040c590301c03c40600c002a03c03001d545966840010401c83c106517806004218100005040b021140e8041c50f070101883d041d0030b007050b0b229202c4002080d048080640c0a5000b100c4a680c4159420301806100f682440c049082d0f80c2c6d1640000c1c007a08030700110f94103101c0142000d149003542c0c055000d040c0d0320a10000c04c004104401d03554003410041c1d172400d002e18900803003540664804030807070740702d501c01074141c00d12921140e81e2122000300c240390 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 275916780 1250 275915530 275915533
    0x114010e0a05040c2012030103030302030705090919060e060a0b0c19050a050f0c061b010b030d0c150905030910110105010f0e1f0b0a0c0206040303053606030603 71
    0x41826a2140b090009000030384d5034500c1e05000c5c0290349024060030181c05412540329003410184028100216410340e030745440c0250702c036154490705131002d01440425640c007405101c1000f1400e403410f43d0808228510130810300902e40ea171a411a40904281c2c1d08540100300300c0414000f0707030f220200402d80c080e0310404035044010810307a80d449641c2d50910403100307500010240c00900c41c040140a007003030b0b0005d01030a0010b01e4003000036078074400c59000c07240382a010040d130041c1a10a512541543c0d4006d0b0a503460060340740070060440745100d00449808002c0b40e044554200144212408642d00200071031416001c02c04001062440400c51010400c880c0c3c0601c1b0058003c0c05100d00074400310410072030160409075580b1f101d00d402090325058502600d103090050900000c28070803140e15107001d03a41c0e00f0040710110b82460308248060f401ca5400180002010351083c000d00b800c0e0b00c4107210309020500e03076450b8402101c00c42c51200291103a482000c00314905a001190000c034000c0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 275918030 1250 275916780 275916799
    0x1120c0305010204170f010b01020a0f1a04060c0f020109020f0d17180a0501030e0c040507091a040806011d070302090a120b04120c030c08090103110f070512030114010e 74
    0x75902802d80e03115803c4110688115000c440451408000e16100b408014009028001a040000b507441020050117880c6501c01402102444599500c2d070590036580e03210a00c003440e05040220291260000703007070008c0e24030300000340c01ca0320601c203c4c9480c944c000d104a074050301d00c808124480c0d03600d503800e41b0034420708052901246003e078024980d0891a440c2540c101600c1001c102c40c6026030b901c614103060a01001070240c0d01b000c0f915801000044500041c19281e110041b00c03411415000343e4072440c400c2c200451050303201c0d4041e108496034030f0300304c4040360703201d1002203016040e00c0326103000c68001002003042c0900940151204402c003401488a01e03564180c0c0f03620903c810302e826110050180c09000a21a012844509180c0141041a0198015038009019410102019012490215858401e80c2c802e81111401d01090082540c4407141b000d00c62810b54401c1900319020b1140b050b0100c004102e0781c054a04071505002208481500d51005640d0543d00e021125805440c0301e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 275919280 1250 275918030 275918033
    0xc02030601030b151f08011a0904110c01022106060f04031101050d09150f05090705060309010f2412170c0106030b01060f09050d08040302120312250e0901120c03 71
    0x184850828821a07602d2640c05e80101c402802c120b00603003142040003108581e120804502c0c5044031052981900c000519803003212080032a80a20040100c880d4000150030142c04020f4508954014000404005540f240000c0144600c6081e0500f59454000e200410208008640031144004103041481c40e2a160480d0601181c5051004407010082c20f0344505a0441c00c0c411002c20740050034040040e81410103815135a0400351044901c101000400a0358051083d08030103400442120b003405413894043c00c840620780700c80c0c86207082c15404c280c005210010090308542e03858000001c0c519040b2110762211240d03000c1b04d08486103648074100000090074000816000300b0840e6220b40088802c82401000201c00d81d02c000c0c891007051300343e8030210b1403240465048a604550041c0c55168003e951411406132841d407070b45803203411040000d0800c03408100720180511210040407800100001e40b2450741001465821014030030042c003e2400c00c0c048651f60701d0103100b211030200d54a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 275920530 1250 275919280 275919289
    0x10e0402131b0305010617070e1507020d0c06021216141504060b150f03130311060103030e1002010507020c0f060721140c0c040207020402120f0f070c02030601030b15 73
    0xc0b1104400080d92880108001d80c0c0c4540102800c0021118046090502c0070004084540b0704500c28412030415108920110000d01101c0d031060b80985040c00015107810035012480c000e129500c0075008113070455804003c1101100c450a4410070f2881c0d0f01d051684444c03c4440b030640001c215071190901c040c1d40c00445004a40c4694400c00d0085140c3c44101c0c2440311003500c0d1141050f00070f4051150b1041c100560040e81e501c505103000143d000145420121619800102281498090b00c0008000d040e031068000306803601c2511000d000e000086422402c8450803180200180c2104150b203455151110b001c0350010001082e0a041960b0ba0311000e08080161401c50f42d002050048514882d401c80444c0d10044044000d040c24224141d0302d454903840700c2a04144244c0d8002803410841d42c0c3d9a060710701c5003510514115288c500900ca01c10441010340f018182c52413607600144031603110b0312081d1440d0343e02801a01480c0d182d640c52200103070001d03000d40d10081e12440881440e80b40c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 275921780 1250 275920530 275920571
    0x150f020909090a0606050d03020a060f0b0a06170709240e0301060801150801110f0703090906141906020705060325020a0b01090b011e020705031014090303010e040213 73
    0x150001401c1c22400c80d291031012285c407a40241c0c0940c0005c410380c4003194000c0b032040c03c5a600600c001c82e900c01d100b400c0c64010300100e03490981c0b106005001013296540002140c0b885c0d03610620030490390321114010740e2040040d06c9031348040900c480d06a181ea2150074108607205807030f42070060441a50000003800c1d0f80349a00211107582d5900308645111540030300070001818400000c010828048500c0c0c4a10700c500304003126100c0000599108140c4034210301001480c0041042003001c1d1030307496400c00030480c070b440c0c41e00c01c4c01e8000e114980a91008140c0048452580081403803505c0d14042c492a500000c0101401e10300c15090a800d01401c2c1980c00c038080c015502900b0840d04078a40006049410307040f1299070742ca800980b0280340d0300310341d44510454007600082e4280c0700b03400c0202d00c1c0064680016070180100200341804002e542c004a4000701100b0850840c0d47d92a59081d580340000d104106019111a01050250510b280100004859035002013100c1203803a40b216283c51 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 275923030 1250 275921780 275921791
    0x204060b1603020114040b0708040f0b01031a10051f03060506040e190204080c060c210315010201050f010b071712070809010902090604020c19060b0f0904150f020909 73
    0x1c40c14440c18200b40e8203100c0d0a4031089825800622401c1c140c032042d6a007080100303450107012000001c5000c1c8000a41c0d1400216406100190b8541c1c491810081854104140100e00300c4d1034000f189807000707800840e105588018100480d0040c003078011408020110031a44241070f5503d40215140d1242d500500180c00c0e8200c180055003003251010b00907003400e560003c205d42c8103000038444442c0c045094030131351108a07600c68403024541d2015062041082000d10501001e0f400c052030b840f0000c0c0650320441c240ba8100d4400a88400164245d441c2192071040056101c0014406644180c1c054450305002c2e14080c1140c1c40d0b01c040f00c880f1036101100ca01c00094101040150180d4014200c90b4082220300081c8801d400e16030115041c0c4001030b1015118503000b141c211f020075000c0219510207248000443d0b45000c2c41d013403100040000f010740354010102c00300c00150b03905080300307c680541d9100100340781a110880005006203c5510b0a2014039001c0068135101d6940510303260142 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 275924280 1250 275923030 275923057
    0xf11040207050307120e06030c041203140d050108060105310e030c06060405010b1c0506062b06061812110a0e0a0507030507120218031213050f0d0f0204060b 69
    0x3084d07001c3c40a8a24490b00c610544252020010801c272901503000b03990481d1031205030744005070381d103140c1510070010241804e4880032000c2540e48240d58250000c5048620356000c0e00d800c0d0362540c040c02548444c01c40c60345405150b000002017400c9a0f262034030090240e50f6000120008042420f070300316400342c554201d455014000f409010b10f06403142d5401480b44441440c90724100351542e05920780c0001d602d551007980c41c2c1c00110f030740d20352404031940c15078500026a0070000b5800c2e541c1c002040364010803c0c43d49000b00114005000e0807800c42e0400250102040c41464a4548031605400407011510042440c0c1d403c03402d0303291000c401c1e0151500e91402c000c20f190a031100d104a800040c5007804040c03c1c04240400a50402c1c4126640c10140307402598071300094014000c03600c000d902c1d254041c49000740c600c2c900341020000e41038921044080c60b61480e0350f1002c102d0706e580ca80e416950710003c143e58080c0001c14240341403c1c5c0a1005d000400c0d480d0f5030719268001030700010105c0e03055 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 275925530 1250 275924280 275924303
    0xd021903080304051509010b100e0f030d03090605131703070c12050c100c0509120106080d021f0e0c06030a1503110103141b0a0c0816060b030a0f11040207050307 71
    0x80785c1004060380076850340c00801020780c42c0c4000940d0b060782c032050f180900c10160625105605d448110604a100c05000c40d03042011020700200205203120068403014a000c010882d80131084450090843d00a104144002001c407541c1c01d060340082c000e00140b000b003010607000100c002e6100c10000c201da0700c4198595030386464160034a1201a03411081503d41070716070345080c0d0404159010240c0540d41000f50159800a032401421140c111003414401c2042040c0c3c10360380098003010380c0340d0425031400130400c030f05408020340c1e2005104d000780350414041071000b81890405944c0c4207160010210700b810000c8241e5400c2203d40e00141c82c003500c9da01040d4080d5805001e03404482c440d194400b810f61910280011180f45041000d00021500241c0850368520840c003450000c0d422020050362441a013295400c00c0804060455401d402c25019030601d20703000c2401401280c000a040e40504000d640b03803e02140b220130040e500640c280002400b00340300300080e0840724841c0000d0600d = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 275926780 1250 275925530 275925553
    0xd121b0305130b100f0b0a1409010215090703020111071415090907020a02011d090c09010918090c0504050f040605100f060207031e020105070b0406020f12150105090d02190308030405 80
    0x42200d10b1b0f0400800c1070010040402d10551003080400300138280c103000746c0c0302c4e0003a40040b8101007000548840301c000e06020311000c0c0078082101011030b4400d072140301d11000301302041034030b410291041444496849603413240c1401c20310302e28045070342c41884240c9000c10b25030015280042c156031880059112112000843d600400604920007883c4078280b924003282c2c0005001820040c0880803108001c2100e41559000e04495000380000c180c62070103045400aa20004041e1081d0966202c5d84c052400030303450410784107241c02000c0807942404d81d0b03a6192918405400003410700048054032210005000100e1116000071380a41d50251911524605103408403200b42820294156244110007005070b03003010440315190790120900c801a5038904284c0001c1c04ac0c4190149480000158454a01e85496400d840361a41d582005281080100111010300070001d01d650411140c1c40c0071809441d0400c0062007102081c204040221b48903039613a03010ba081650300b2540caa00040c600740 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 275928030 1250 275926780 275926799
    0x61b0507060b120d0c050a060e0a0c091107021210022b06050108010e1510050c011802060d020c0c030f0c0915032d0a050d121b0305130b10 61
    0x155030b0450b5036400c8030140900700c6407106004c200c113000380642003e200c01048030622158001d103030804004c012482c400b541207034442e28503a40407106001603000200f280c10041c811644520400da5aa60031b12406030309010420281248086c80c0e8410082061191000c41c00104500c81c024518030010640c00980401591045000320002c0c90034440103100c40e9900020303482c1140c4141d0016a4241c0783e00094040480c038002400c0d070040484402e00c1031158116005107510080c0d10000c00c41030710f054130072582c14010388034000d40c04002048001c1c0e200c40c5540250600c0700c0c4520955624040c5840040c1c50400d604000c80c007e40c204142c0d4031680d2a210150584c00442440111810041c0c0320009071130b00c900850031210b00d10411314100784c400003035010032480080340c1d040318a24452406e0299071080289004400200c0350040004445098000d0841c0e40c1c20840ca900e07c042110303070054025007001030200000c051041d041c0350214819208060040b0f031040d000b021072601b40403949 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 275929280 1250 275928030 275928041
    0x3060d0b0a0605040b0a121712041a0108060f07180f09390f090503030d05090f030a170403021203010315140601020307020d02011803060f0c030c050a050304061b050706 74
    0x1707841030007032200c100315100644d080e00801c01e80c82403050051800c0403007010480c2c05020410800031312010100710812142078603040c0480c0006c5a40302c807581c0d075040030641e5194100c40c01d240c0803020030302240c3c0945c02540e42c6240180d4120091660b5501c50b81a20180b0341164000546a41c40e1003070903100e002e6600c0c00c225402041e20b41d4001002d150141c0d1503003030071030711030354403c014141c40301c2e090301e501c6840d91070301801e0000d0549a807104010600005010b0030b540c02c648034012040b60140841000003140c0c0d402c401502c507000d040d445990034038540f11004100ba81035005410700600041020002903000c0e512510300c08407920300c13201d860300032200b5403d08208034603602810b00181d44c2e00001070b1540309604850000d960f41c030a100480340a10322025503898800780410110411146800003450341100c01001c1120f511a03401c11420f484c03000b00200c0100b0010420001240d110302c0007164040d0145101003045005007185401e0002c00c1e04001000500200b1000104109030040 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 275930530 1250 275929280 275929301
    0xf0512270d02010f0804050c0a03111002060106141b06010f030c05010e0108060d02150c030a020c0d0c061b08040b0403030807030509070b0c0a0c060908120f030106030203060d0b0a060504 82
    0x10360701480180c0d00103071a04100d40003070700501000703200042c01c206040090031000003001e4a1012410740d24902403115a408a0f01c10f0700c2040d1040601003880e200260283c121452075035070000200190011075a6075214903404200242040c01410010743c04001c07843c000c11491162582c2140b4500f06140140b005800140c100103c07081202c0441c0c7c1d0001c5080c1d0001821201015103190600c0050300314a240c084a418502c000305160052650120140ca81e94696401380d4064444141c10081440c182940081407842079000505c0030900c00c0e002110380c6005c899140c01210016150580103801662140769143c20024050003019481b180c4643c20280c1414140440d051040202d9205e1410f409100305206003c6500c1003072071000c100c00e2104a41000c503001d116602c0380c000030440368150042d07407007a100740100050070548620480e61850303482031060b8110b90078054210041d6002514682e4417408100962010886180195001e204a0742002a41510740001d110540307404010 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 275931780 1250 275930530 275930539
    0x503070207060e2b06090809100306081c18030602030103060605030609120a020709020c0a06050609070207030204150b120a0b06090f040203040c15020706031d0a0f051227 75
    0x100c0700b42e2030b9081c0398a00c4d81d070540803024030000d0041c40180110034003080540000d050616400600c0407030350040000c0013054441d00b070344c1855110103400f542c0c11b41c401d000c0c3c2540f0076600601d130f40f011062066102d0b40685020703485480105960142d512031a0800e85800754000b004008001c614031442c80203050603000340607280340c140082912001e40e0307480d0341c40f030441c0000c0eaa0000c501c00c1c44a500505560303441107441ea0400c4120564a00070140110359462402e40402e0042c90080314003413044e0810f50090040600b140d0a00000d0418003003c81a070f80340c1400040f0f5064402d8019080340c41e2080105c051602d001040c820503900355501c2c1c240a414204003891790f548880032800c21040c010790b00540d40e901c603480c003401d03090000d6000d00300e138a030790aa0303400c00a079000c11043c08481c2c6c030b55020721070000c4a07203107020440707810500240e5590104064800007035078054426000c90056003a80c04003a003103003482c401a48020715068010200665820848800140d403003240d04041d40c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 275933030 1250 275931780 275931797
    0x60f0f01080a0f05010204120303021213020604090b1f030902010e0108060a0608181f0b09010b040509060f060426060f0106081003020d11090a0b0a0b2503050307020706 74
    0x3150641c5480000e5070103807503c0c3e0300050b0340050040c00d404503001450050f1714084442071a0400a0094100c00200c01c080e000b0040440c610529000540b415a60003c0034141b43c246000b101c43c004110104105030420399500000e24a90a040600300e010462510301150b81c628910004141302c400800141c10300c8203000034080c0c6600e0701d08011007a07680500f80201e890b01c5406000342e828502c2d8440c00311921825403001040340d040d038070044807400c050a0a01c41004650b00f089005402401911003050050008000518146100903005100a0700109a00350100040740305a4881d40180701c1041613600211500c5980346250103030406540050036160410030700340d41810806100300390400c284900030076100c04048481030011076004283c1161400f03580307042c1c09201c081c4800140f14600d13010010300c11307a400f4043e00340b032030750002c001c0700700b25003010203054094010701d603068111483c02850f0000701c40c1280c0801001030180c0c641a860385003d1341d00903d01141790f0007d104010004 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 275934280 1250 275933030 275933039
    0x109060902090f310f062910080406140103080c120708040302040b03030f0c0c040606051c0507030e030c0703142a06190e01020d0309030804110d0b010602060f0f01 72
    0x3944880382c0ea055040e400650149494840703020b13041413203003d807140c15502481c808200542d0701001c21000145c104180c444403020003031005d411000c0c50743d03800038008011601c0d4580320342c400a60040c481c140c006064030100c1c40c2065000826002154600d9001441000c1d0b00c00c2000000c3c0444240000350b071410070140d0310001240294440240116100e01c0d825025a40030300660310b5800002c0100740d15a181800c686a4401c8019841fa0190b07182c410085400c2d40320b60b003143c3d0040c2d80500303074209200400e910180101030003000c0400f01982d41881340307802c040038001807680520480c005c1600f0341c1141080420b0b12010694442554004000c94902e5060850000283c90002d05c50124a10b09480420324500c00c40324501110800c24018010040d08010b0400951000b0303400c45208109010084e03007103c03850031010300800c0314400050009040640541000003000c1c00c1809401171a0340c50300703a01074003a0005005030b0040380400242100034448079034801c0c450801e01c480b55140 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 275935530 1250 275934280 275934301
    0x60804083a1d0c2b02060d020304110907080f07050d1409070e01030f030e18090a140610090b0604050a0b0403060e0114040210020c21060108031e0c0f0109060902090f 73
    0x542e50f1080944030103102130000a142d020003041440e005003c007551020386d22044c074000d5000300c0e009c40754078083e01c2c000708060030000120780c844d565986402050b500d440f000e0740c101000041c0304034200201003017101504800ea0040c280c4040415270b924280342811107072113023083d40c2504862602d449860040020a15403402400d0980c0c0506240341200049404544214104003540c400c6080040500403800340c00a00010124060400b021803454141d9200b600c8010650710407400c4c204c052800e00c008803a95000740f8410380010680352519658401240e02039810743d010784036140d004035040060000034021800112100380003008021000c41040810200281c006401103011405003044c1d20b0082102042c000c07001803a0710405511044d4001c6e40c2e1021413031400c07103130244500003d0034500020950720707000038688642185101103e6460300603000500b0856142c800d056850340001002e108440c0228000c103070215207100c007401881915000a44200c40d181e0030142001403001a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 275936780 1250 275935530 275935549
    0xa0510090507060521150907020f030d0e0a1202030a0801080a0302061612050a02041401170105220f0f061d0c030603010204081209030601060804083a1d0c 68
    0x41c00d005444103d204290148001980700000340f5156200034000f001307020440402950786e04440a0b001e0350b40c0c010701282c645003500c04403c125070041c040407080001540169001207442c8003202c4541d010b0f6250f60311028101421200983c0000034500c10060b8442d000e60701405544008006501c13655034000c1d41e444000700920080f420413240c880c0c602e031140c00e0714061295841024446820304e4005503000750300c00d1245910006040c089001c46500070a10504003108401800c20385030300c0c000c14800c114401e810010350003c40088810520303515489441090529060005100c0b040c802005044072007680000c40041804402c4064004021a02540c05071f1601d80c25622a04c8440100303000e4011030300705001c40e0050307810722442c1d2500c4101801c51001c040f01210032603666804155069107040d18050700042d41040661108100c0303000b0b0741070302c2c40c9101c94803c000d0740e03129081c0351204c500c1c02e041c46c8880e00c2d07002d402403682c07911805040078503810010341003031150100090503410 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 275938030 1250 275936780 275936789
    0x100f080604080d06170c040c0306050d060e0a1e11040504050d0c052a130204120f0503040e0c13080c010c030318290f01060c020108130804080a0510090507 68
    0x603070005216118a1090b08007000038102820540800d020810340c6031b03214800c1030000b078040c0d03103004441d00555109002c0e00b0110343c1c0c050050900201c0303544603040541071804c142a00c0f0b101d1000502d0000707a03000900005070300c100310502c0e034a88036072901c5000024003c0d41a8030480c280740511012070000300385603e0300c1c10203043c40941c0c84035915205081c40b40c004550711307480301d01c03120180210781d9031040d803108102c4c125607000c1482e15021000d01280524056070004c10316440c0c1110005111f014940c16441c000c1040b40c0c10680e61354100c09084400301d5007070303c803c0b4002c6001600d003481d00c4202c4015040c9607016280001d041c000081c050103070f0003005001c05480758215808a507030156070b2070000e50404030407181ca418482c0d040070001d4041a115015180d2075000545c6440025070040c182c0303540395603000c64120340780c004550081015265050f09081d820200c400650f80c1d10040008200c5000580307200c0f10f050801d903081c000000f1444c141c1c207003407078000e81c0082c9020403980180c4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 275939280 1250 275938030 275938043
    0x30306010801060e010c060606030c080109060609030f030908070b0c101a0d0f17033313021209060a0e0f030910050d06180b010203121b09030312100f080604 69
    0x111307504001242c0701c5406840240900307107802400300e1030580c503410010391b40c143c5440e0380000340d07178403075042080300c13100c5c0302d128002120f101e8140002184003100340c21180c028034046031140d0f101d18406041c078080d5070000d0780380f0138000f44881810100303002c84001c807540d283d02005001181802c060401c510f89401c41e114900304120081040100c880944100380c014118000a02200021011641c411b442c100002012841c03412404d141d81c4403d14022180c0340c00b201303d1038a2400910028940c064050006075809000008665084d10740c05842452040d00508d0241013a040c803900302d60105181203141d07040500510300c5120f00004560440f0010b5540f03c68100707200340c088403031b4054945450f81d0282411000940082840c030103844007841c0074410404552031170f0041e652071140907503240c0d46004d410005000748140f400e1100400184038500b07490511f030b010009095a1082c46d859035550006d0b024401c911001100c043c1c0079200d44484000c0203410404800d030f036400c0007071004100 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 275940530 1250 275939280 275939297
    0x31b0a21090c0b09031014090f1605010309151802040b120a0b100e0708010e330303040b0a17060a080a1e020a03080d14220503040f0308040e070203030601080106 71
    0xa840400c82c05d8102106c4010400204569080c20040c40d071302554003481e80d1140f065100b01f01407010601d2080500014207450445181070019030140c04440c1e000e84441030549a010780b200380794020707400480003c60040810038501d1041200702d03030030035000318019400846548299600050a4031680c4e400c4020100c0c00e59400107104240b09954209420f010030040612010617007141d8001c1c140c3e0443c145001e41696240c82a0320b000d01840d5080034801c0140744200c14803a1065540700001c2c2000c2c3c10350746000c0e00d8000000440e40f200c070340b000c000361411001d296050030040303000340c04c004112405a142403030100e445646071201e01000d485201a0707100d0605a00e0108a05030034107038080c00e02269995a8106100d0300e42000440b11019404c042090700c40b8503018908510440807000e00d140c04c00008941c0d818410380710340b021650340c0302c104404601c80e83ca4400380c02c002c51089105940d51410300400100150001c0c107050107640c130900034448540e03009551141910f501d440c08121 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 275941780 1250 275940530 275940547
    0xa020702040903020a0b06060316110f06010f030309051203070b10030209070e120d0f0c0c0906090903020d030216080708090d11030f0f070605031b0a21090c0b 70
    0xa1060500080d03100340382520300d500300f41d0003080c0c528107180603002124007640c91805005c0c1500c021104200444c890300c484000a90281c2d007103034010001c3c00105e611644c080c06038989801000e802002101c06440802c004042c1d01c10b0840001e8003080e60503403417034a80132401715568000c600008001c424028000745014130490039840c0207640003014108103003448800602201c00c42e0140d42e000b42c000b00f87c0340301401300024508a0b0304421b65154000c08480b0001142d590940041c1114005901140020301c0c4406004034006499141c6001849490030b1030064035121140c071a034024540148440001140005041c80115400000c0580d80b44140c4c0703000da440303105a843c42035200e05007a40d90400e111240c13890354444031007034040350100b4044005040d51a00c00c800024043c1e441600280111442400030316003040c0c41c841c0c8003102035121000c21800341c00000901e0300041c1d680214034104100417000209915100004000c242c0f9a078075510303a41c1402e40680134030314000080415 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 275943030 1250 275941780 275941801
    0x50916030c0b0f0d111b010b010806010e2e0305180a0204021606050f0103050706020f0c040e0c090403020a05010c03020702010e010e0609130515060307020a061107060509030d150605070605 83
    0xc074030742c030030880421640344c0e05016641795401200c00100d20601440e1440a100b205204035030940c10140c40e0100d59540d001c00450710000100d1340c031500728130300d4a440b0540b8442811826444800400d1041c910383c103110000342210030040c5180750403d618186a04110f00218141080980680300541e0f10351402110f84d002d81c0030184020441d514060800c034040a42d998118180d82c1b0400581d00320907035a2000f280d4038852007025400d01d80011000f1003061505500008424030000251520818507000055404404940580240c2c02c10100c001c10400f0a200d840360305c0400b41007c42c2040a13580000308042240042a414001040c0c3c0300500f50781d566064420700d0000800307608075002440c0ca6800a4141076404070b41c440a81c0c0d850894030b00d0100180c0780b180617103900900303600e130158442c00007030240c2c043d041c00e682108011600106490b4040d0034450700c407603801107a070750090300c0150040703620000030b10031078a446007028000503501c141200c0d4250780041303001c0756a44480c030681 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 275944280 1250 275943030 275943037
    0x60c170106082508060102010605030606060f07110d030c060f11040b0a02100606170f01060c17040909141b0102100b01030e16030b010608010e160e03070801050916030c0b0f 76
    0x10300401900f1100301d0341240d1221405210b400c00b80c0c028469680d41342c091598802d41980d0003a800803007402540c81c43c0c0011000340c0000f50140b12080e0303000c400b03000829160410000e00f900010a101b005000b80078990040248024a00704104109100c10900d50a540a5401001d20308900024501c0d4180e10130405010030341e040d1642001175070707039481018240c042480324844008445c4070015000680b441d034403604030b91054642051000c016640c4400c202c41d58441d40c00c2e441c01c24080410b002c9541c0c8243d04441d41308200c81ca21843c00c001c2c2044c0780600c24041c5803034038030125150340074690b030200703212003c0e12002a01242030030100005801410325411284481c0c070859040034003249031603a980f41220300030140440d09903210941214140024004c1500300e41c07046011a1500c0503c09a440c5070203482d1074001d16580700b0b800000c0c00c2c039100e0303408a80d190307449005011604030248915205112440354000c0924650f0342c428540200a1103107804082d408a003200b00d4941e40001ca = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 275945530 1250 275944280 275944321
    0x903030905060c130807150e0a031703010914041203052a040911040602030a0509210f1c020714030a08030f250e150405060412060c17010608 62
    0x2660749a00d054010020f4581028524800d5036201c0390b400581100c000c5950b1060301e640f04161440c1070011242540c0d41903031381c44a44c1c0c201030643d1001000c14803084c01005480344036900c06a030b0354507200f007a00c141c8030401c00800080a00c0000d1000041808600c0142c0c0c4115003000300c1d0b141d94100c148003030010100e25821301002c01c5a95480d8144100d0000c0c0300b41d078044101040440c01d14402000e4034002e600882016900410456100c240030b01c018050020008003c482d046160144d907030700e450465581000a9480840301101c280c4060108404050120008a28150301660029034814662059a1140101044502c040e440920503208075035041400c942e42c81c00d010000d41403501003103d261055014a070070507003504403011090b804c0a08c06940d05180c6104003402c0001400c6a80d0a10070001d108101c00185034881c071001d0002000d88444401c1405034900b0321030150785140746110304222601e5a200c1c504801c2c02c211a055500d246801d80350765540311040300305084400314 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 275946780 1250 275945530 275945533
    0xc130e030307120605060703030b0a060e13020705030f0d0c0801090227030705100807080f01030c0320030106140f09090d110f011b1b0503030601030b01140d02041d040201080a0903030905 82
    0x3041d03000e05270190000902d041c400d61705912030700c2d03035144101d4240b242400003680c40200b860901c90013450b40d801402001d4099010742c1d24020049020754590340c44280b0000b40c0540f104031407030845030003000f038900510b2603100943c0340c22f403402081c2182d08441d842d02c50503041c2c031404c1d000d00794404000c1c00001e0000030304840709980721f2134006428080116903000c001422000022280e1039a99103850499502204c0e0014060640c0d8030f452185a5008180210074140301c100d2a81d43c0d000d018540080c801d07a00440c0303220116105000302c0701300c0c9a40c1036008601030024407150040000f2041484c1410f481c01c80300f19452011a20308100140c1c9201803d0340c2080b844030b2207146030000e01068107145440724041c00302140c5102c1500d45500d000604150014400140345501a4100c03007540141450190015424000340140c3c640181480701c03102a030224040c440c1440116100780408450280b5040354079259000031b259100003484042c040d62100c00440c1007500076004206940c0c1d0010 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 275948030 1250 275946780 275946787
    0x10f171504140601061b02010807020a12050409110f07080f0412050309010f0816080c09030114091905060109090c030807030c1709150c07170c130e03030712060506 72
    0x1085010980100341e20080c2d030060000000b98240503c908800500180c01c4515880e100390b001550300b01c0004200e0300a41c00b515840e180015800310083e541d54205440b1240c0b03441c00d242c6000121011084082c1c0e88400800c0000e003100c040d030042e6140305500062031039035100010324040d5a80207a6121b000230071440b21300c1070200300001c0040d2003049020f903a081c4181390346c80400c4a40d010140c03804507120204c6055069400d214894507541310310035000c2c1c0e03440d0042a40c082421286000c00f8171380e0080c805410b200344000d0610901810381c655056113518510700f0340b601c40e119071041c4940c4084a64074501901080f92001401009541141c90a0b80f66001c600300680014026102100e8007400e4100312580580d0303140035070304c540c00081c020136010341452440c101a40e0041d04284041e20803044000f41440c2843c8000e005884c100e4041c00c500780c8000144501e1000c11041410114140340380f0000760780c1c00106603544000340745481807002d40e21302a120001d10701508440d40003000003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 275949280 1250 275948030 275948033
    0x10051210030b07030504021f030204051503040b1003080a08060a0317030402040b011407060b03010f0204080a05060702070b0d0207030c080d0c14030408040b0a05091c021206010f171504 81
    0x60850100301d0b402155404102d5407904000c50403203400310341c001d502c130401000b04880c031050f0401960203000c103404d00510b803d0700c6900117a0500e65900d440500c00d1800001c000030040c2600700e807034100d01810070600e80d290655036200818014070f00c099041180c0140058000d40c1d41d55601002180c02c40e8401e241d00c0080b00106545600032501640118201a005005944110340c000041c070074000695040c0202540c81c00b01800d4660300305e40d803564130f031000116240c0075480100300900000f001001d03210001d140050901200402403003c0d034103d98410810900040e00310303480400c280000690701c14040c0340940b0320981c800c5018044007008540381e01c64404a522211074000726848002d5034007180822035400b440110740042210b0402e01c0100014038110f000b91014826500300039080c8144e100108902046d41018603241c0c802e25035820307040d03090124503000c1d06038680703002d4051503040054501d0042d0b1a4460070b240d50000ba0540000340405000c2c0d280b1001513810340000c02e040c107 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 275950530 1250 275949280 275949301
    0xa11040e010e071d13020702130b0a1e0509040f060509010c020f1b0105031305060a0c14091f051309060501030b0d0521120f07110c030606100512 64
    0xd01829802040c0c4402040b9064040c01101c068030200c03d0004403c84c0000050103080740009000c8184a0303003e001407401a60381d101106449624202e000411072040c1c000c0108110483e8041140c9d2410074120760204034140684000f0764206540710800c40e08c8514015418091070800a86031034038100603c202030034103402c9034000c0c203241c0d0f08840002c0e103120300054564030440ea80c3c400c4841c6003500880d07254001d0014640c0310710003001451000816850381c500b04607007190b41e40d00f9190b0f00c149603030348290040c4034030b442c0b2250320604a0070103074501b010031025101d04613405c0c01c0030300144d51707403080f603110341c040700c02c0c10600001e0203013400c0e41e82d18884d0140c006401418003280c01c0c498204558180700c071415444980140c000c04c102100452402c62071503140c0148e0b41c04c1c1c142004081128144044c00e035008131304804d41c1c0825450100402045414016800c0e20503800ca9104082c0c584d40000b00250850812503e82e21841041d0209440c603108443c3c483d0740c42da003100100b08c1c40c0141b = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 275951780 1250 275950530 275950559
    0xd08120415020711101107031506080a0b01080115122003010207030305041e080f090d120e09090613061505030109120f020102030f0406020d060306181b0302010212030a1104 76
    0x101038034058541ca0105d002500c0030b070552542803032a0780c008941080895010811004102d207c07070000aa61529400000e0404c0b20300c10041e07030b80c04440c00c01004100e009115283c000e0385078245404c5110300b8206c07068003d000900e000b5002c8034004003078078960400301c003071708074402c00050003199104103074600076001d090700721400d4541009400c1030038031450340110b80e4880158031020302441e06900c06511039883c2c1058403850303040b00140d44c1c8080005c140020301e1118003002d4481d4111207181c403007000b222020080c4004c85a400840c00d10620500704011803444030b41c0180f006c18521000142c0d03440a078120f6000319403560900b003036501400705d00b400140c0e0105141d6140c008940301c1078402c3c1e090744021740c1c2100c0c080d0b040b44c00017400300b82d60350f014110344030040703030081401507480e1100010f440c200701091070550b410003044020401e211340300b04030800c0e0040b10510030304d142d500043c1d00e0724dd05000b982c1c003401300000052031a80702648051001c0506442403038466840d40080d03092180d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 275953030 1250 275951780 275951813
    0x5010305010803030403080612070b030408031501090b04060f1206170609010504020a06111c1107060206040c050f031203010305033001090e0f0f0114060d081204150207 74
    0x2450503001003008640482200d20950305922a0143c913241d03013040c4540119036070800c180343d024880b030118101c032242c0000e6000c0c0b8012403030f45031207003040c40c3c2060a080e04080020306220b014601017010b200100156002c81c0d101d400d1840c111940c05000f80d407100d260f032500c001240c0c0350501c0403408003d00b401082c00c22040c0760072100305540d5400541d00300c8030142c1e0302070340c0f0130b000142c00c0044034410411003200740040002d8a0400d02180003544600c6070403155038012448038079821100c03c1b01086068024a158801826582000d0f01d588510061a0080c14090b03582d400d880452904c007041460313808d11000c4482643c0b580d40f400d000b512508444078401c0103905c0c2802a600d00324149199208030303903840e802c1420603417a1100541c0142101c0d50710111302d004046041d205850b0910000d01030101040021400d943c020740080d031000e0004180070700c943d420b05014008200703a402590415442a0719181003a10355040503500d0544035401e0018843c00001c0e62420014109240028034 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 275954280 1250 275953030 275953037
    0xf03061803090a08060702071d04080d0e01020c0706081605040504050a060b1c0b060301230f0a0b03271c02070b030a020c060106030612060b040608031201180501060e12250501 77
    0x540c9614800318000274404103030035000402c401141c0462135038001460108601035001035500301c901311950036600010380e010004d4111780d404003c6940c0007070010303038048110307030024104e00c201d204094040e0055000301c500840d0b940b03002501001340b9500c02009032542c94080c9455200d840081044501302001491885040c100020302c80e09008003681c2c10794591304107000070900c000801c0010403052100060b40003a26012226050719001410701c0078000b0703185c081d5581c0c50080c2000d250301c006214010201c44d444c0030441c1d078405010035013036030042c054950904103000703202003249071031182d810501000301d0010038065010c48640c0100781c03031060300b0300b03a50050380c1e02e0400340c0440701d03588500401c1d0b442c0031001d1400100207500580307180c5401040000c1a40d210302c502460741e00422034400511030040014407100848164006506031441c0d4244031960420313000030100750001c41802e0083e02d0002c0d01c802078010502480403000c429214500302d03a00b00414001c000900340c403505010 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 275955530 1250 275954280 275954293
    0x30606020c0109030b0604060e010b040302030c061614031309270507050409060e0d0e0a140a181d030a03110f040509040317100608060f03061803090a08060702 70
    0x1400881c84210a101c141c540501d02807442e12132114440008101c00e034055594000400e0a45040d6134081c06000b58410703054890742140705140ca04421a0350143c0f0403e01800f4681440d02005804403c0360361010458200c2d01340c0040e51440c0d8007982c04120350703103600d020001c01c0e40c1c003081d808050008251a010f556802410902a58030504010081c3c002d8100c800140071904058014104040c8235990000e40b0b07100e007820b141d041982104040b00009c0c0c520044020781d01d01100d00700c018162000079440c80b500e8050002e2445950784c400c2c1c61644452800d0b00c004100158410811008203000140d078a095144000c0e0b102e510100003140402d00d0005610f102c21041c900ba210215003240d1204d19203418481004040d0000034411010044003e601004000c20b9805260156120714a10702600741001d4001e842102e0080c4a02d0080d450b22600c1d40450707400040b00364001c81e006c9aa140c4464240d007280d410361007410a881d401000b28500003444c00340002d0102e01c00c00e62542030798a03 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 275956780 1250 275955530 275955539
    0x70816051b13020c070501081509041a091c08070c02030f0a0605100e0402040e03040b0f07150c020d0309031b08030a050106080105060d0b010c06060b0703090509060604120215070b01060306 83
    0x200d0041000c4d03520346510140b000d000c15402441219041041c841d0309843d00504440058411030301210200c0b0504a08903540000011f00f6810030b4114544102410360000503d8280b03005481c049900c81c00c010b90140402c400600aa0f54618660340240540e104505074003642c0342d4941c00b41341e044607154a09000903481030b0780d142d40041540c0c4074101e002045e4030740c0c2d020440035084d411010b00c0e250100704800100742c44143e0050610058480196480e16401e040ca1701d0300b8181d001c101000d0f00d0a1540c0c644249901003500e00c0685424200000c55050300d003401c0b1141d107514500d00300c042403101d50220a00c0154006584110300c4480e080c03040760f899030000c4900200030300c202c940044d024480c240581d0503d03000000780860614000b20850801c5c4c54032010f59400e9407002c4003050000030301c0c4003070541c01081d44000d4031042c0e030024094105200465031a21842c462042c1007106401500f085540e6120f650840203040300d8440c0d280e02d203500300714504420030300c10b15020915040e0000b8 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 275958030 1250 275956780 275956819
    0x13110a0210020c0703030806030312100305010c02010911130e01050106030b1201060501090b0708090a0f05090f010b1803070302030607020105010501180501080f06031c02010507030b090408070816051b 88
    0x3008007014030f0142240901d55a030030f980d040c5010340410340c140000d00419400038ac41c11401c52040392094109484140346081080c2118645003020b021641810010f101007040c85800396201c000584010041e491004514002000c044108864035420f21000107022640740e040314040610440d04141c40c160a4042c0d14201c5100b4418140401d00001c41048403004442c0900440c90180c82c04a01d40102c06000420007076981d089042c40503000c80c401e00803401c0c10640d940d0711525001a0120550400f04152001d0054010400e2218410100308103141c6080c41071100850b0302500b202c145080c0058040d000c0c0c038003400380c0c60000300e01d950a49280355002e010681140c0c0180c681c8001522180301c00c41101000030600e6805116410014801e94656848061685001d41c0000303003600b05400c0040170b42d2a1040001e07c5080c2d1031007400f0103d44144111001c050340260b10607a0b0340b4204442c0c0768000e10046010308580907013005030039295803c1e410200c010400311882190010540002d0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 275959280 1250 275958030 275958037
    0x90b1801050901060c0302030714100f051005060d0f060311120d170709081c021c02071203020111040f030209250c020a0f080c03060105010309081813110a021002 71
    0x10b5101001200401555002e869140d0300030707000748181da180203165100c451083e50b0315814600942c0c005904002c010f41c03144520a50f10700809030502040c100720015150440050240c01d201d400001040703845035886501a1500c0c1031110002d003c0303165281486191030150310302a80c0180c61545145031500c4010031030100c0c0e11203e80b2014110129500591802b0100800342c1040c08061100420111003c01034030007101032444154580700400f0304001c0c2801c1c81c1030b2141e000d00307100503e5020320b69008203c8105448001101e10355039852424101d000d04940b55205d4401d850004010400f8051503121400740c0b8000e807060b514071341355407007120801801c100810010044440d02d50021034866124011030703d000404803a46140c9801403040c1d580c00701d501c51800c40c1d002c09030304803041c1024410180144001d0800704145401611603044900c98800106002c046940d0808684e07a90b45070910350001003440100720700e0200c42000f80042c0e003c00c050a01502c1044214030300c0b50b25a0007213 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 275960530 1250 275959280 275959289
    0x15090f140702030f1812031b0c030d030905010b0a030c06090b1804150b13061d030616020708120a030b0406081b0609030d0e090c0304050d0c0219090b1801 68
    0x3d5252806000c1480e240da080440700c0000c84413001c0450000d0b80d140f002903c2c500601d00b0107036954180e0362441c1442110900d01410090300030803c0d14105540110302c11640100300d0601007612990740c0b51403401040e8260400707500103650000032060142030583c000c141c0d20543c40e00703805a80c0301c030852010342c001e04000f07080310f01c41d207980e1403898102034000d08041040800b81120541e20f440072804075800079071121104045944d000c11040d54800c2070310000e40c02d141d0b2100c09500361980400d4442e40c0040140c04c44103001c0e906903280b01e02c01c11074080200205001e680c20500c1200006455520182c01007000908225150280740341c1403191030211495100140990444007100d1580c415880c0c4681e94000c40a0040100d6a101400716803080640740d500c80070044611010020501000391020f258401c01b031042200084001840b0520320b11141840e02c5440054030000d07500017090b0b48410348102c0300d03400008024080f81c00020500d0412108000245010400680301076000d115 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 275961780 1250 275960530 275960533
    0x8030409110d05010306051b03010e040308101701090303051f030b0601020120070302071a0a08060f0d03020c13110702060f1204111f020c090a15090f140702 69
    0x1004240c00341d500c00d84a10007503804050a0845024040702100c8099006464903600c41080000d0840007109402040e4003000d42c40e0300317550420b074074040b41440081005060161020100f0440d072441c0051000502c901c1d40084070f0000032800d054044c0c5502e0408401003424517001c160200c54207103000b0810301d800c46401c080c40d89192107080c008000035200905556a480000c550102400494000b1b4041c1c4603446588018900d0000d00d041c00d40d07400f485601c0340e811400c0c000d94003080200da1081640303203024034040d168000050760300181c01003140ea01c0510382e00503800701900400c040f100341c44103c4076480702500480307070356003a106400040c01e02c4010401a150051801c000545990310034505003038141000001c80d4400b101042d682540c428420305100059072901e154461105c0381440c0854104030342c44070029580c1e12107086075510411005001400e5007050354001d040c07407070101074500c0000c1d0703941070f29000505c8402d03100e540f8035080040c40c021480d1010100c5000c0d55443c0d0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 275963030 1250 275961780 275961787
    0x90e090c042703110706050307090e0406180311060702120409150506160b0c040f17151f050a240201020702130227010e061309060314070b040803 64
    0x1080000901c0a074401c0c06005040700025041400d01c0d42825003203503c280c550880031800d03051010b19217202a0301000410004004000d8642d920034000411144954203807102070b10346151180107800c0f05007400a141c01d40340280424036500c418074440080411058540b2034684081c1217072907000c00c591aa0708203138208020481d40c252a07028a0142c0c00d810070400d442602c5000142c1c4a0b88010480001480390010900c2030001e0001d030340d500704484400e000e00e450f25101e02030041203081c0c030900e400c20308181422414143c0500402d442a00e90072012111840c0200002c0035003122402e5400300c06550900116803402e054450340162441107090401410241107036040c00700d00341d18601d045540a1003200c0c01602c86041811005500390400f40c1c90f500804903081c0d0701640111942d18031038003561002400d0760091070002c0c040d0400e0320307950b650340112407000c0c031044926880305c1482c0b490040d0000c10301c025200701480c44000c510960312503d59410a0741e0b0540144d00421070b981d08100f = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 275964280 1250 275963030 275963053
    0xf10080c060901030b10050714010c1e030906050c04060e01030e060105090907080d1707030b090a0c05040b0d0b01110a0c060507030c0602120106031d100e151303090e09 74
    0x194042c12040005140c0410036850080100d002002800380312008a01d01058580410590b1080c81c05545522002008482c14813100180429940500011000003403000003114074460f80207010603c1c2c0124042c4203a080920026400d98000d108840009484516001d1990300c2030181074400500c1500030240c136400c080802502030405010309a041c07254042c0007584200c28051201d02e580a510703007070f03241c96103040b00703146401000300104101450014002c003d0358507860501e80000c1c1c064400107a00480d010b05544c141329075046030a0301000818241c8803001c00e6049821000020b90380e0405484401081c6135680710602c9d0004d0092240b20000d118480c415030280801900a180450004e81692500c00490f03001c041d0084501c940b8030014040740340c060140e40d55422503210b0b0f600d1001d0b4400409512000500313011282281c0b0744d6208d5004040800181000420f0b0002e904010300304200800d0101c071128000700c0100e00c0d01040050740c55030703410056201c2d01010f000780c8a0000700c0b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 275965530 1250 275964280 275964289
    0x7030201080117010207141501060c0f110303090a2408130303110d0203150a0609062703050304081e070303120e1e070e0c030c07080703030b0d03080f10080c 69
    0x1c103a44691990f00303010380000b081d1f03180c2200f101030080f800908440080c0c0da04481c00384005030042428409801200000902109088045550025901000040d030680041d0452050b500070300d6015841d0f810104807040419041d0320036214160b000c1c100551101c0099401c1c82007122294580c4401031440008a8001c1e000300e18003041c000000d0b843d1440b0081ea043c00c0740c0080d500850203060005094400741401c6c1400b1015103000c0c00c200040e030780b40c034000804c4000114006005a0810116840d01c8039070892440d001d1035026040c0e1f40c44548030f9522031755404480041019052141114009115000c200d00e802c1c0d9415503610014401251403d01c09008201d9144169205540b110442c01540e0801e01c6072104891000d403840e1494044001c1c94007801801c6403160746401c206100c18403903002c2c1190302c8030758442441c42d15a00141016002045010320710381e0045120114031003003550180e03020348681c8200d61100030740c3e218403040030084840c070f002d40d04060f8000401400345160 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 275966780 1250 275965530 275965559
    0x3011b12060306050406050712051603150e01080c0109140109090b0d02210d081512120d091a040c05040e030405030109060b040b120c01081503010c090302040b03070302010801 77
    0x550306010a289580e5540c0104481e0704071015110a0b568100f0700c1010355118060400400c5000310611041c142820b80c5601c140550400c00c1c24556501428900c0e120300c840804010070700154480700f690f0f5a0404c00ea00e504410346818000f841d81c80c0040b03842280400400401c00307040c0d540340c06007402d183c0814018961940e8183e4000681d0144100590341e054405007001e402c0e034042c94510109202051400204142001c240300c69102088503c0c64012200d139003d2004589070503111656244450412a0f0300039503144144000035408000d14840d00410000c92080c1192510b920300034040f45070010b810703280106100c44004007000146882c0c0c1042d14113940145c20740746059a28400a42103400040c4100c1704039445492010a40c80c040c818816980420b40e14481420301c481001911401d0f00c45000b414804a240800c2d80700300040507540201c10301500030000b0640200c0007505004007844100e1280b8200030b1422404d08001c50600c00b140ea040c0c44204141e42401020004003c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 275968030 1250 275966780 275966807
    0x190f120c090302060a030b030601060903050303040807022b0318061715040608071701090210030f0603020907120c0e060f09030a08030f0103060b03010519090c08120d060503011b 78
    0xd01c030a0100141c1c0c4c440d0000d101c0a0056100000c5031100740b03040c0750800d50140e101000780011241d0070004a04040100c99209501540a550f543c44910008503582c0e424a00d02c44c0c580300c0006940c4441c00f1109404d0080d502035140d200301d80c01c80341952000e84c29070303018107000113030840c5800100b00b034098540340d00020003582034810301c01c41c900450222100c0768803a103001c0e4400301e010044078078007401010900380c4000c000c1c09a4034007600415000c1d150340b2200c000b00b665070601844442101c0d0700079000395600426500f0315007400c1070010321800e1000800700301c3c1c901c0c004c141d05029004600c0c00b400d107030000d0f20044c20405a100ba44000360049040300b40c150044403070002c00520140c0c011445128030300109005035044d400d04004036141c0e035075514000da242800344216083d44103606402800d000300040360038000cd00e0500980a0654425107091040d40184070200d4001030141c034488400c01020002c1c5580c0e0000c1600780e270000160815042c09214413043e007144605c81038048107 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 275969280 1250 275968030 275968037
    0x90f0d0201020f1b0109050a05011b030509101110050115050901021c020102190306030f0602250b150d020904290903070b070c20040f020f190f120c 65
    0x3d010380314095051220000d4001c0301e1a060b0503488000351707004040b440c007070b101c1652002d65203800c000020f0105c440034601104c448112491040415120700100e0791240b401608013900421009805032010140d00c418611a0007826000c81015030940b00d4181200c40e807660310f1400032a1950140c440382c1c02403507924114060742842e4542c0c628400402000c0403000d0b400143ea0341c95a00e8420400440132282104040c100f40080021518210901140c99080100165200607281c0d518011154101030010700c5c0f0034029030390b801c0c491000007061040d54604c0c00d0b52024000b210400c54002e001e401d0095001290001040218900d105101c0d980000c01c0e0b401e1a003000201034062030280100e901c401140c0c000111082041101400075400100c2414005a840f00740e6480e640448044800102c1c0c80c58503500305034065407246c000001039440781408650b81d036202c0d01f02402c1e40e8071954401604088071035400000600c201c00c42d004090413550380030440034240410358047c040100021081 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 275970530 1250 275969280 275969293
    0x2205070801062d0c0c0816050102030c0705100302090306070c0605010f030b130302031605030915040b0a1d0a030317090c01051611180a0509010507050703051e0301080d0311090f0d020102 82
    0x249155081030058010389006140702c21f5000b140c104410140d4100341d0464200b407040c54a811400190303003050340da0880d44080c4140444008800a00800c20700a03414441c00e401e2015290300305a003400c10070700801d0f040c40b85030303210382c904240480c003440018003c0e58200005441d548062007031400e500c0c42803041d83e14180003e4015952030b400004281d840f60000100c4d0b01951805506030307103203c505018818105440c00d40403682c107001383c41e40d0b03006004c104004101285e80146500c11144001084400c0d400d40b0303410300501689501680c482c48000f0700020071100303d00001c0c45007115070141d44080c54000c0c0c503240c09121503d0f0f0f182c2100c20a807018054105951080920440e240c80c10342180040e16240700722a0a40307002401700034403039141074148100103600c0011070381c10075050308040b6038403000266000b80d01030140310205440000400007054904001c02c034039405c44180d0354184490702003005907085600c204c5044545c00000b820f00c003070380c0e420700e541c119080a0050040d5203e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 275971780 1250 275970530 275970533
    0x61505120d05091f26060a1806090606051c05010e0402010c0f050105040b04121809110d050109090c08060705090d060b042f071a062205070801062d0c 66
    0x1410401483c10404290a40188032403004038a170b81e50042010a002c400e05401c040c0c0102e410003800740a003060044e0100c10210103508260002c034005c20403484100b0807103950ba0f5000b80550019030242e00a50030049800101c2c00482c051a03058800d80403601500c1d4555500640322140307505401c859188034001d010001c5902842807600c2a8000c1d8400103c0317181c40c0c50b22080f82894102c1d420144080e0540d41c00440c0004030698054a0760004002086825980352140600030000d1000306182000004110507905811807140030348502c0280074101d4403823a00b04d4039100c00301e441100280090180070382c1440c0006800c80d00b40d000b208006507040240010a0645000c041d058198542c001d003006201c103a03020a90240c0310310303400098244605a652048049820080381d0540244080400c0c042c3d0340b000707030a12404d240c150b0240104241300d13409501030301d811a100404900c1140000403614003506400080f1032100440741001c03003103003042e000f900800b40d03c92010010002030220 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 275973030 1250 275971780 275971819
    0xb0307090905070509010509160e01020a0605040507030501050c03070518151602091003030206040605100e0403020604120801080a1511070501050a2301030b061c061505120d0509 78
    0x1c1c1a0340181c0140002c03600b0718090040c030010680c8a0390040100f601044450507540c01480c0754608545040000c0070400f000407072500e41e1800f400741202d842c040601c0100900000c420301207034443c4009201c20340c0c0301101d901c1140002c44d031400110350208800300030b080745046050841c00d0002e00c40348001c1d800d4407039228181c02c6196610f4070109881c10010952400da446194071000ca0001d88803014110b9030002c2d103c140161000349490740f55030200707805520001480001d0a02c015251041c1d1405040003540c402041d107040d0b404908944114000d184201c8146045e50401402802e000d40c240e513441100f401a0705071900300d907a8a00c8544640c0c60018001e207500d5000b4400421031341403502d03003442101c855026041074841803001d2502c00c1c1e12070b100528112034211070b001001e43d90303000c0490000300d500d003400040d4a0915071840c0c10080310b0384c030402406184e084c02ca0845519003080c414880182c0840d401164003419400302c049116200400c101d00000e0040300b02150301d11500c3c0c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 275974280 1250 275973030 275973041
    0x501023606040f090207050a021503070908010506061605070b0d020c16050d15021c02120708010506190203070812070813020a05040b030a020a06032309030d0b030709 73
    0x11080e00520006a510005009000c404615085807014a03251901d80e944214030790700d01c1422110340d00480c036030090203070500680c403001c0d80140c164000710801071082000340d8401c49031903012030304080020640728414420f1501c6060040c04203860961a211316044003080500112001c0c46500d6011a04046900c050106082104005600c81b09070602c100d0402d03c2000940d200380034024030800440d524940c254401c00e400070740a04007500c11002d041c0181c801c2940ca45108201003a0000b007001c6540d00030542c025105076842d040307032100c0b04103c48100f402c1c490300f0351100d020301c15100000080741070140c81d11068011649003230302d55034401d502500031003480d0380d51750401010840c0594001c020580d2007a101404c19000c2d0302180c2c0060708442542c000d0b1806581e4900c521141c1d078030104185400c540c3c00801e50441107a650500030042c005404440860602075000341c1d003001081d901260041c0c68000c080d50811a4482c3c4420090108040403a41449541000203d066691040 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 275975530 1250 275974280 275974327
    0x20303030109240806072d03090c0918060b0603060907030b0307030b040605010609080a0c03201e040c02010b060702240c010b030111070206030f070e12030d05070509031504050102 79
    0x40c106500d040031b4003800801061021010303c26841142d12485940d05404036403c000504000070b81d840f1310f0070030721452035660700210301c1c0501d80070700f82040028513104203031000e00c00e40b0b0601004003280b06120309400190f882c2174000c40c040c00881c1c280c500a400120100801604a030310440d66a1182c4210b490152030640d0215510750050000701e5004000b035010f414101d006080724100303a070760036415048511004e07002c01c04060b918a00c4d5000c0c01c04c80700c402d01000b02151451600f04080032100c5003180d01c07861050789000b0518a040c0e006005100040d000280410304003100794080c07007507202e02032255005030f011000c0f85001904040b805411802040400041c941ca040d5051508481140b040348801500c00e00107200142d5884d000c80340d21041d541e40140e03242e155158107617800c0c40030f1946668000301648864405a800001602c0c10b140d916400b0301113a01c50007c261894458148402d4241e0404805011000b00803015980c00070b200d0f40005142091a280b03139840161182d04 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 275976780 1250 275975530 275975533
    0xc030a0312050603060c0a11030f0d0b12061b071103012306220c0c0204020412060f020f03010501081e070801080d030c08070e040906050f011e030203030301092408 72
    0x2100300c0d5054a02c10035038000c4040e0000c000c03900f410381440c1ea03e8083e208150040100920200c551120103009940d07405584282c2030b41c071400e52090141c090444111018040c2c820706a01804100001400b0350103400300c103011a20903090442c80d80401d80c071800303040e240d862603902d00c0c80c1e050300c1c01d100701c00048034180340318004010080c02115200601a142d9441406a4492041c1280f5550b00242c0d980c0140c01000030180c0443d041035442e8808181d01941c070520119000403031903001d01a4404052203550100b2060300001d07116400ca004e405c0d11008040300510052019501070f440c65a000140d41d034081201d160300324042c481032102291041c00044541c4010002224100000742038101ca0703090038441820280f07802082d250004002d4030411401e0b0f040410162203681c0240c0c2c02540001052000d8500341c008648500d900f880361044040e9004c1080c482e000c0c5440011065a0380100a545140d00e440c03000c2000d882d0080310b40ca01070700011560101748031403010b0140108440c80 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 275978030 1250 275976780 275976797
    0x605030c0f130608010f080109110f0f0a0f06030c091401030b03120409020a0f0309030c0b1503160503062a0d020c06180f010b011b081902010902100507051e0c030a03 73
    0x2561031510146c9600000e81603050150610021b41c07401840e042c0942d055a40c1c06100d071401000984011420394900d4000c50100008034504505c28002415a19540c8003880410b4100c5004c503039005291007440c1c3c8424040c0000301c1e1940c0700c0d80201c81005001012540f22144000e268145988140d0141040c59400118041d0b504d41058401401002d203003070030040d480c055240546600310020004018208030b40005151400746d00c528101d0480c09411a40e500e0120300704c0c4000b01015008061203441503400162800b0110303d11948070300740c0c01d04a42031500030251602d031540c00419525003290780900815102a100700681441900541c0b10910386161001d00541040091920300100d41d0500d48031b002580d82140c4c0c2e40c81c1550551071071581c0f1001c241041c814a0084010041c4625115445004030550540100c150035008861030109507500d00015150340c4a1418001d080d60403507401c1b803c40a02c03050301003000c07081800075907070300103203940002e07082c058540002c40105101c034 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 275979280 1250 275978030 275978039
    0xf1f0b070606150f030507050f0d1e090302060117070602120d061206020304020405150a062708070e0106080103170a020a17070323040b1c05010608041406010605030c0f13060801 78
    0x6001b801e4002c41c041c201181b0346240d0720302d0440640b14445820401a480d4007540d5405045500414100c0e40d4142c0c041182c204146002500e401007842401180303042ea01c0601c842c1480451004116200c03900108420810405518044d8000450707034010301e0354a140001d0041c28400c1e00a0105120380c01c0180d981c98244100811954003400c0d03d0b40b4900002c0544502e6150007a01c0c070240c80781401c0c081f0a8200c01c1c100001100e81d1590301c46869401c054001403203500004011081e80c113100442c10392aa201d40003142d00103801d00c030281604000d80e8000310300247e00b000810303031130380c2a10503a26104042e4035402441d0701000900405004001030580c28960b21416001880c40d4440380c111100c4a0070361400018002c030b0051260100780080e248050380700400798000362840c558020300c62583d413035a016000e44c80444040d1400e680c4458024015000414000d0590f001038440314150740310f000c400c03405038122220001c9480d104000c01e00b40360b0b120f624008006c00d890f07988c030301156061 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 275980530 1250 275979280 275979287
    0x42a0c05030327010e0309010e0d1a040c0b0304020105091002030c0a08090102010e0312060906120a2004020910271214030403080d0b1f02060f1f0b070606150f 70
    0x340010002140d02d040c0b00c0385c00400c07000c41200c440030000d03e085450a044000014007540a0750340c02401c44180390f0400c42c088a1010a107031203a8001c840e03082000f581c48006040310f20003202d000b03000600810608049140c01c1c072032001801d03072074412642895501b0fa0798030f140440c41441038500300e4000c030304481c00350b9090051140d80c0160002550900310310406010248202410302441410410005506d0ba1241c01062103150f44c035a0488952021078142040c03c01075014804154215032068044582401e00031a40300b25400703816a05000035002c8200d070b00822041010f50042e9103541420072615480e81c01c04054134422035680141c929501c1c000401000300302c1180c54a8005110070008078080c1c0c0c09640e60454840d001142c1c0005841c0001c040390004420b0f5030b03a9002c2d026a4030304c2c03d50f00180103032080c1e980161240c2103454440c0702602c0c0c1e040f03525014201e00760041d018426882100c000d8680c45100c0c078004900c4903140c02c481d41e04507a1040342c0200040e84944a4000d2951 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 275981780 1250 275980530 275980591
    0x80102160606080a0209011a09060a051908040b0f0c0903162c0112020d060e010906050105090112150f110a080f01260f0607030b030606042a0c050303 66
    0x3600074804c00810744d01160030340c01c05110b094203d10b040700e816180410114101c0e0306481006103000c0d922100d1810103046500302c0b00a28411125000072006210300a0007001d02440e00f21041c210b1640e0340301c07e402000e00c8000c1603404003807000d1281c0103482d20300700001080d00001800180b1490300349081c1640c180d04d20001a10040610208603c600400c0c0810a05403200c080464401d06050b001107005102a0a00184954588606c11200c01819846a6007461042000340026640e84c020032850307510030b0141404801001f81c5d500005414901c5415004c0243d0703c0104040b0f424080560071a45914014055080000358544682e03902c2944281c0c0300c07158910304500755040000d60307089002c0d001041500542c10b0184034030700040401150356180700c004116182c1d81303400d4800502516080044070b0013403054002107910341c82e01d4052980594404040106042541501c281c1101c910343c002c0000d11180d1003403140130440170710042d80b0602041000609055450000b101217a0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 275983030 1250 275981780 275981789
    0x80c0303090901060c0c0b0d0507081608280504110907020d0206151801090218040207050c04050402061207031e1406130605090103050c01020c010c03080606070804080102160606 78
    0x800c100010303940e5a403880d0304103040d10780310f25188104003043d1810320b00c2510140c110782d900c90000304208101041c0d58028a10841c11981e91507040c5e16030f21480615002907045050215000c440000e035950052503581c0000ca40102c402c039000c0f1202d00c40300f411101c0584042d15081c064856a881d00d0400045c0741d6045106807000703026003480c0d410001c3d20b0b441c1c0988800881543c01515202640d10701020309100c925440c00d15003c0d5a403103a03d04000c2d8014006c801022886007544801880c052003641c0c00107400901a11540d943c482c100001414010012680440700f80012034410b016810305034401c10441d10000303881c01e4211170800b070a4001090741c2c001c41d03003000c2080004e1a800b03803090f80c000d0400d9a4003520702c801070400b10040e15080c0c010079001280311000209002002403600e0b031001081c0c0a864121051700300444110b66800005000721710710b40013041060608000900c00140500850b85c14075032240205426a8803007843d52004000c200040030a1140710300c078082c01003 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 275984280 1250 275983030 275983033
    0x15050408030406031a03030c070f0b21040f080304060606030f0207080703110f0a0b1b09010801120807171c0b0f04050402040b1f0215040c030605071206090204080c03 73
    0x1460800981da5a00c5180514010180c60300654000312070406190150080010256038a40c60035450b1641d8440c481c1c450329080e05500100001c0b03000c030340750031106c10b00c2403070309040a04502e000d040314815602410071642511807000322000300b2a074401444c050740c403801c0302261007890010000c00343c0d06249a08088184108643c40001e800302d4200c4030129130600300390300c3c1c0401500050b410b005004c0c040c00c1e00c80c05001814000c00c62b12070300d2140702c0c2e00ca182503441e02c03c0340703500c40aa0038001c01e860580410a0000180306080045070325504041c41007074058a451903d541d2105000a0314881c078030135000120702c4580100703203038010070600c0e40400ba0030021380d000140040d20000c012002036002d15900c1c8042400d5443e036411500c2d50b110050543c8a40416500c40c81c1c03502907080e00200f00500889021000b00c08003443d50902681d005103018210b00d09540303849005001c040c03e240c2c14040c9503286422208814094440108110300c1d0041e01c45242000c0c42d8201000360685512a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 275985530 1250 275984280 275984287
    0xd03050d05160801090f0b1005040504110403020306010e040501060308120603010e011407031505060328090f0201050f09100201270c1401020f16140f0a03080d0908131505 75
    0x89501c04400c504417281c0110100f410032808000700014080d8140e0141c00c0304615101f0f020b0550044000e0080326800e1320204289030809051201500407800000e5042c1c004100402002c0081003009411901507070000801659942c0c0300d0250b5030042414005030302e00c440400460713103002c0c422032401c905904002d010040c1d410b1144200600014004400e0542d0345540d082e143d120120410302070007001d050140c3c0c0c0d0406041701410740461443c8044a10740001c021603110005021702010568840c80c00c0c03c04130f18950056615801580300c0400041c01405828847ea4510f1816080014a90000111003000309004192054545030601d0348004070200b0200281856040c001114108281c41c01c5207540c09004078100f801c01c100116140c031503250000203c0036030701c1c1c41e0011100c280d004126903008400c00e200804034250b0b0307800da0081c80d0348070400c08190608010300e0440c445113030000d102602540d9002c41c903009400e03001e0f0030b410042024824607480344458a41440b450404c01d09 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 275986780 1250 275985530 275985571
    0x30305010f05011d04020f0d09060504023c0d06181416090213032f04050708040b0603071205030403050d03050603120d0204030803090309040507141b0c0d03050d05 72
    0xd621460a85130f4003440d07001803104046440a003d84004841c810400d2042003000e0a24101a240c1603905a20130140f002180044a40c8540c400d02002c1e4801112000e000c0406070340c5084100c0c004006401046102c1243d0000b0305070f116820004030652000d034401e100360709261500341412010b07601541d0254142005051134803180802b1102451705c09640e60949031031001580b1001c0e84001e0012800000941464501802000a0444c0f030611141c14226035000c100c01e451041e074000002ca440da6000c54041109165400d41c0130b0320241c00c44803155a07907290000105418117055403d9000402c040c0100481440309010a000a1030305000c2820914000b070f03216900c081848070241e00016184000958a405a40045402100050300e0303280c848c40c03181d00c0e40d0200720002d10031450000080ea4103801085081031064030f60194a0a280640c0500ea1005910f00c4c0240b905100c1c02c0202d207125650019158603480c403c0d9212900d0780d034072603280742c240c450150406000b40400d20700182e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 275988030 1250 275986780 275986817
    0x60b030316020d0606030512040602100209010503010b0d06081b040b0306040b06060307230405120736051302120601060c030f0c0606060801180b150c0316030305010f0501 75
    0x31141c80d011100320100320002e14080c0000c042541c0000c241d401030340c1d1040c41508042010f0001c4928075000e9802c0500da212a00b0102d01c5900450b038003080e0b00303000612040b004007004d0401d0740c0410b880050b1590310391104901c2c0c0050407001c0d6005d9044541c0080403400c05000c0d00c603038081c0c26802010070781820b50741e450407418001c0200c1d00818012001031540b034803c4145202402c1c0e141003942c041d44200c540046641e100b8064640107541509140d02500400550602110094040001858144107094111a803000d403800d02441400d0007504041c200c40c032440340900103281c5080c1c40034102d4410701004400c0c0860b03110154000701d0040041d25009000c0400c5250f0524161640240c441c4044c1d0b01300002d2000503100c0c1d4039060000c641150410f003240e040c0c03201ea82c030b2820030b08042160801541d004a03070041d01f00d104003545482100248024101c1a1202c4050343e04140c0012200e04061403c194150006505d94004002c141c408a5503100a40700a1070a000710f41d401c012002c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 275989280 1250 275988030 275988067
    0x501090e090303070809070306141608060f240301090906060503060103170d180b0a051b0d020a020a24050708040201081303020f030409020c160f0911070b070804060b0303 75
    0x744188905c420014161000070702c00a4081c0d41d11903c01c2050425001c0d61414a1030212000d008100840780c08441ca24002d49030648211802441084d144401c00248464000c0c82d00c1e02032030240c101c00c42201302c405240c0c00345010380415800065018250708200c01554810b9110038004c7d0450350060000c203084019041e03001c03103030b20300d0260398040e030911100003045100c000c80580203142410104100810410354041c0803005414002c2e40c4984042c062030f136604010084010b5010030194280c20080d4015103060b000a0040c0d4801c003400d6200c490390407440903000b08480340d1115222400c1041c6109050300029a40791004552170f01d83c1c0068a0300001a10410100308100d10180070140f081020000c0840c04c2015a034641e50f0f10082c000c042c2d000741124880c140180b050140d05040c1060501003203c00c0f601c01341480b18646520400204400e1007070350001001003040ca0080341c080f0221a00407411580e50784e07507500e042e040c4001114811000141300390020002040000b1300d2000c80c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 275990530 1250 275989280 275989291
    0xc0309130207020d110607080d0c2d1103040801060b0a03051014040e1f02070308090a02010c0312111611040b0f10020102090406121703010602190317040c0501090e090303 75
    0x80103505c00d65000020001d000e109001015500000740c0356500c10b64a40104034091743c183c0780e01803210104044500c03e811b10100d900c0d4141c040d440d1001005100d011031081001014059a142640b9009004e0a507007850b00121000d0400003140b20342c0035410f101d102d0744400a030405010460030b00d20803c1c03000d95000009841a5192610303500b501a0501441c551030b48018507000000d1800005000a034100c41ca095002c9540200015500400455540c05c038640c16503842d52080c540d41d40640f107600c440d01c0041d42d401ea8a401c011704a801010040280300008203548110f101c25103070861703100e1011411140580c0c10680441a981c861050304d4180001c111500601c0c00403210049009000d0340d140d81d5445810300000050750b00212050000890045000710144500b00101002d00c0c40203108040050340302c64610f04907045000031030581e541c400d14105080d40082024540040342c1903409071007a03804204104519070704079540100600c446004000545400702c0225240d0000800 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 275991780 1250 275990530 275990543
    0x30405010c0312151401030501120f050a050a030201150b091e030102160f02010206010501022404020a09050403111009080403060c0318030203182d01050c030c0309130207020d 77
    0x907000c00c06004082d804000d0859000401c000c0002c1c0c1e0403501c1d02d000d1131080b841e10780c008400d0003881d54401d000740c9050726101c203148908884640e4403070001038008082902c1e94013480c0c4100c80000d00501802415a0007940003040b200c815039942003007000c1c01d0b40031190f007a0041004c0da02e00e80700d6a0030100d5812a8503400c41c40810203101107400381c4142d4142034000304c03100e03800d20f00f0070020702c60800300f0034004e0782110700c05da89610042e640c804030301c1165656003021a80c6d41007a0040d01c566140c0c054409004d1070000380d030720415502998005d403412000300c0d0701c01980c0d032007001d020041c0a0350207212a0b004e112104003511078100d541320b1404083c0035243c136007502c00100703030103030f000f030507125132103000d10034a03600c803070400a4403500305101b0584140d41b480315403240b03440c0600221032032500e1700076440004180d0b00340004214a2400100d41440b105101c040001d4000340040c20b40d80c1c250401940d600d089400c2000021610415249001481440000050b80301c11800829180e40f002 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 275993030 1250 275991780 275991797
    0x15030a0b0a0b150c070b0f0f03060a030f03020102181c0b1f06020703111906050a020a0206031608010e01060e060307020316120e04050f07031a151903020c03040501 72
    0x24004000e004604500d9030015106039106082c0f80c0c052000740103680d401c6040d0f814003a110070200c0c605200b503021680c0004402d00c040341030106560001c64020700c00905070094155a59948900400702c40360980250b5400310f511100c50502040751020601c0c01c41e24801200c02c002940c420038084400302805a500c4103000441500300b011a00e032256a558003042c90507940d6110083d51a00075010459500341039041e500e0060500d0606000107401180c0b1881c1850b080c041c0481305500040e00c00c0d400c501c02da0800360007686800005501420071002003941c0c019445c0c4004d07201c950103074010010000c004004012060740100050f00c4918115078856403034803400300892440c01400742c561848603089000300e041028481c0b80035051101616250102c4061340108000c0715001ca4008031020b031400002000c01d0b1095102c901140c0d80b151075613040700040c4e0003041001a4480c01010881000030340b6060507000c4001d06030120009140540c5014100c405170740c0c0380d004074450b003414028200d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 275994280 1250 275993030 275993041
    0xf0206150301180602270d03050a05130f080f06040f0b06120601060509040c0314010e13060504080301090e070609030b0c041502010501060e0d05030714011512060515030a0b 76
    0xc1d003241e14444a01d1601e58440815810031344000d40c0000c402000154080c42e410120000c00302c0c40041e9100014181484003405880a442d20303801405018100042000030100800c44240e004003c1c240800c400c1d1510340c242541103117410014080803031203612000c00c120009814500103003840b0b9101c240c2c49040e0f100c06000c40c1c84105440305580040c010704001180450f071100262051060031142030244084440c0140c04560080b07680c0d03c00c0e03210447c0180701102800c000302c0d8000c110000b80c6007459800c0e0300c44002311001501d003154444400001041403400300e002e80e001d80c03454000500314880c40c011002e885084288001032840360120002240c400c121030696008003c1401c10142e0482c008000074000c0509015481c081240c40c5c0c0c401082d810040035180c18154804000c0d850b004041d1250f800120791002c15402c25903c90400b40a03100c82181420300602e08004440f030499440e01e4401c050301d80c010302c81c0620104074103080c41c0d40e5500041192109400503903041c2a51550f = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 275995530 1250 275994280 275994283
    0x90705070c03230d1815020d0e0114070c030c050609030a240501080c01140a0f0e030f0a1a060303030c0d0b0429010315050f010f0e040501030c090c0f02061503 70
    0x902c80c42122a025000d40c515115800c0400b44080d04170020400c10700c01e13142d43d2506107005a8000078801079114034080c00025021310325406000310141481c00800c0040d0440d8201036008201c07c55946501d941304204101a16004d20041c210403540c8030f0500c41d5000c003003503584a5801c80509034070b1140003e020741040254900d4140c00009074140704e19a1a1800c1e16514521034000500040319180320f00d0100304403a06035191340d2110b81ea03030110300844080840c3d08400c4080d03556130601032050010000c4508010318a90313148507a04802c4051691200280e240d1001400c1901a410070410404030b144c2100031501245c180d0900080c2c40c58820f80818000d00e0078500000948030a001805007420320034401503d40b00c03090381e080c0300c500995903403c03840390118820350380c10000180c0700d42c0040d8041e40303c10300040390b6071921082011071a00003400780c5000b03034030945d41d011207108180280682e03400380c1d441124090038090700011101200941d41e210051590143da0392200049155030740 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 275996780 1250 275995530 275995583
    0x6060d1a07050702060403140615011211090423070306081f0e0717190f0b04030507050106060503040201110c0a0618051e011e0c08030c0f0315090705070c03 69
    0x4024100703540b40c0b9100e142c80e0710314076040d0003252301c41d03c82c0b0300c0040c0419510300140d100310703401030350b41348a0300207088206000b80c10f0880510341086410b00440c0c07230725219482505d1a44000c6200000e10003400b0070711040b0900060810720405003040414008140c0c00542e0301b40c0c210320703210360010101540d1461402024103891101582c0140d00000410107203d08442d0aa5502c0130191038188101000454034015a500000c0000c0320665104012614400c200c03070748140a800c00e146030048642ea103e00b11403140e00300502091021045c0300540d6071051802030401c0316a00242101c0200400042c02e120b01481160200308030024014000400748031040f0060001a00802500c41626120b4070038000d05606140083c3c07600070010700c0d401c10726031641c0c3c1206007504d0740052078101da101c1c20640d0340000d200f0f01c03103c20100070039034600791424021071240f00c0d001e0707904200b011103d080010899012301101c0c1045801e000c4440800c40342c41c811001c6907440484510141540a10982c4122 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 275998030 1250 275996780 275996783
    0x110105040b070302010b0f0d150b0f030f011a0a03150c020f0a080403170f04210b0103050a12030e0c0118030b0f040501180819032004060206060d1a070507 68
    0x7001054080030541c05402c140d0002004032401c80565118206102243c110b0002c040c2285080c0d00c2d41c91282a06540708144003000505982e00c0c41154101192911481000561890703540f901718404440c02010140c10b00a030071110039589d40c0c0b858485102e2107240c006000101903481143c111241d0003000200e00c103008150645030407130700904259050740c003d484141c50035000201c1070502d40c1d560b202124440c092106860b803c290501c0d103015000701882c908141181d031950485004a181e0901d014005c46c0300c0e10041c406201140340c1102100e42540d000014542425141e4000440c0815441ca2460b001c0c40c1ca1044040c00040c40c4100800940c0007400502868081c401d404c0005100940300714000c400038071054401e010100c288981054001d4a840e10038071801700b508035100401000700a443c58003251045103a4844440c40203034840b0000ca410002404205540d0140300d1540e201001322200f500300701c1180c98000000002c01103a0340541d07242d0000500c20b5018800390b41006 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 275999280 1250 275998030 275998049
    0x60307030b010b121503190f021807020c0901030b01060e040623100c050303040f0602090307150201060e09030313050304081b040b040c1e020f190c050a0605040311010504 75
    0x1035943c1d40120920342e10511049100100b40b0000950040e0398100e401aa40780180052041d0340760032100218403104810111120b10f44c5a2644d00580d0710314180003407141030049150000d040910300640341005c4911040e004500c00b0f03004102180100c0d101038116101410003201000b11040020014080c682080d003d51020b00c4403940c00c190204040040c60009640940c2c451003041c2d030544095840c4000140960700c20800a4001a403103900282c0103482204058100424800042e0600c001d03908074521082c1c01100c0d0341c082035824000c0000510804000721824206141c071140c0724800108443e120802600602040010030011140140007040c159154042e80e80340c05d8900540d404039051055003025403003202490103100c6d40c91503032019100c142409070007002603030000706c0540c454000d502903000b064000758001d101c002100081c4002d13501024032180380440b0400d040c0d410890080000400074001d0a421004032410303207400184403003851985e0740c0102c4052055402080c0300 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 276000530 1250 275999280 275999303
    0xd0f1502070803090a1217151309050604060b1009050f1906020609070906080316020406080d0302090307090501030203030f16140d090e0702071205010209061308120307080f06030703 80
    0x404022980a1a43d41b10b16078641038882007031000c48222164035030003154040300d0408680d203c2403525885000c840040c0400d510008000c4207402201c29400050f1059044003040104102041c8035003a803490088580440180410400600b00f45050103414050303007003058048180c0d035030403051310540c90210400000441d12194000e4440c4410303185001148a00540030900070b032036000340c0b010351312014015401c080c2c04200281445010450685e00181c0d90900031038809000d0003842084091742c0c8000d0703a1003000c001414a4040e16a1140710304624000c010f20040c1e5000c8201d0b00c042000d2910346803510f124103a1140d4003840d0280003001554034150311404c120b80441e000f000b0162940301c8030000c9654003040d031020722088452a0050300304c120300780b00c0b00401d103000c0315807580110300050a080724000410103c0e0f0248110100440400504100100040150b18181e110780c3c0004c5040d4100210054412400a406985243c40910024429807010001a0f00968012404401 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 276001780 1250 276000530 276000541
    0x1b0513030602090609061b0111090f01121e1514010e131b120f11032a0d0b0901061416021c0605010911070b07050f071203050a0501050d0f1502070803 66
    0x7402021a0134039072950a02210030204030505050b01c03500e00d4041d0604e910704410500440745900c02d0080c100d40380d0b036556110ee2103414801480707101d0b05c0402d0ba001484004000c61003419012980c40880174100f501c800b0003091b40c1c06818032034203110503210141141090b00b61800901189800c551811000c01400740505500406c4010788107954041044107001c2e217000c3c2002d64007070008072001507208201190070f04012121036240150340e00d83c13194003843c50703820309035403503200c001c900400b2521240841480d10341207203150b0040051342006103240600220a003070754094100c0d200c21b05140b07044244295201c03100741520200032480351a520310024071704400100820300402c480c1e0b41c513040b0500001a5403808880c217013500f05401001d25941d0307020890f0305134054011004019000d0146c640020002600b660214020f51004900c600d0700000c0e1004442d01613014912a8801c134042001041420001060003904060750206024400b0a264081c2c4600031000b007203100c0000c104031 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 276003030 1250 276001780 276001807
    0x607020721170f0d090507030b18060103120504180e010c020703350d0204080606150909040804211101020610090c0207181b051303060209060906 64
    0x81c0c0d01802030115600c1d07016411080181080300d0010b056640b0540800404803501010b03100e044942a201440c00c0026110b030f1065176146101201e096211481c14000c0061a16080e42c2c0401146a070b10001107c05002960700c1c0310620011302030f62101020308030203d2081084401428003205c44c4030305038170346001507001411501d2072043d155103003034400b0000910104505084a422890f817202c0c042c000726401882081113948590300c12040e040c0c3c02880d1a07208090f0104584851005841d0f6280101c0d0a007080b20040290b48289020040c1d00180e500440c1602ca5000003038495051540e140d1502c9051440313240c01402c4000e120010700583c900c421036414110b144a82c0c0340b0600d0703900c120010b81c0d940b28141c50540c900c101c2c8142c1800003651540c80301c01105210f204840980707951780000440c3c0400201c844104c261103000d03544120380e41d21100d41208101d46043c61900403c00581100d25246010082c101c54001803040b0080da18842910316000c030003003500e40e80301540058072 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 276004280 1250 276003030 276003043
    0x6020f0304061d0d110708070806160f050403150b060309160f030b0f0903040b0f040510180b0d09050304080f060109060509011418070810090e030f1308060702 70
    0x3164040d0034224100e44a0001c3c3c90f80080720700199000300044c1c14404d005460b0844c150316405007510503260009901901088400010400d00001e014181070401020343c0340e181d00c0d0505000c4c441c211201507000343d4400d084804a82c4c11030070f500a103007042040380018000d1054056032000c404002d104050401280d10b080609200c00003084041d500d001116031105c2c00c6c440a44060a5000014030204204200e5544601250b0640f4909903d4022850894001c40e00200082c01c000c0380c00c0c445418100180c5511184a0078040d80c04080000068070308c074a6406003000320301d008510b44c804022a500844199a0700206032038445841e071624a5a440c4905105120751142e24000940000c1a10424003a50006080709280741c4c00d0200e2100710301356070007845800100003100403001540c21070049000c3c180c0f9a0b2400d140d4104903001403104031064000c0b884d5546403200413060f078100081121050f000840042e922a41d8554120030340310302d550b001287c180240020800160342c0400c2e030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 276005530 1250 276004280 276004283
    0x90f06050417010e064305160b0a1a09270c03030301080114130f030503060f090f040c05100914010516051c050403030c170409060f030213050f010b0d0906020f0304 72
    0x4860f5418402115400d24070b2800b601c1d0103280c509002103a02c4684180020601c040070444030100ba568183c0d510f822754142281e828903010303600c1b14a80e001e80c02d5400c80d2480858116081c0e1814209409811080c0c04114202d5510058603c176042c0f6201c030a016269890720014180c075140e40e5182200341c064489214040700780c0131b01d50300090104005824800080750001102c4510380350b551340c203451a9201415031540440b0301c00d01802c1036038450050911541c81007502c202035080c146041d9004800c1900081c0c400c1400803003008869a100501c90102c8920003c5c03100d00440307040c0169a180f0414080b61415044040b00f2300c1803120000d80d01810035420f416107081145004011201c60140740070050020301e0140c04503000c909102c00f06c410f003103021880c00c1d00d00355590905d08103c0d405544000080400c1d0034080007540350a441410045000500603c01854100c6075881c0020050262400100c1c000c01c8440c082c0b091580404505903103c14115921a20b04800c003800f50401c071030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 276006780 1250 276005530 276005581
    0x3020627030a0e1008040308130312051501170106120b040b120610080d0f0f09080d0309051006050a030b04030309060903030515031c0e030a0602071101090f06050417010e06 76
    0x21910704441c0b10717841080c4542e815660b5038240b0313198008001050700d048070040d41084107114494240f0307091442200d0040700b0005800d0301071039050300090004020450240607081103600104607103500403080788480700c2090b4000410440c5900000e00601ca00740090741c224410b81040c0c072200800080a078083c0c40042da41c404282c0d030b2041825030311040c2001440c0003e0711508a10080350148082071283c1d2040d081c110500350f251030306949852000c003080c5c800213860701c5220013401b0003801640350098100340240259802c0c8408118249142d00c001040300b0010301c001820701d4030a0b4040c0c0b00a03540b0803001c1c00b441c049030400501801c1c094407154004020b1154440b05850005050746029205984500301e448a000e01680c6c2003a144020b1340d01801840600c8001884520040a0f00e9200d501081144040c0e4030004100b207130550031a140260420030107004082c1c200d03041e5000c03950102d01c10f00c0d60484614000d4017402015006480a00c1060f0134860313200384507085a00b03c0c801c02035 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 276008030 1250 276006780 276006799
    0x7031d06040308011d061e041e051f03020d03230304080304030f0e0915030f011e0605060c0604080d060302030a03030518071a031e01090506030709060303020627030a0e 74
    0x404c0508405001e072070040d407140c2407d494034038201a2180d81c0d000070800070310000e00d500101e8180b0000502c511400c1c00d40380da60320104108864550300c40e00101104400311100c1034110ba01282951045000142c01d01c001800300a14140001500e1150403c1a98002da01e0f400d05140c40196604117503402c0340420030099410b4441841100c50a2000303c008040340e89030344510301c12000d80098000032540502030070301214203542090203010f980580d5090000c8104e0300d2018850b0440e0302d15044144203000c00c01c9084148100011030f0381c3c006410090781a0340b1800d4140768002409550b00094043c080c07080100249905944400d1140d410650698130000701d1140365070b10350425015000d0806d409105004c03001c201e142c040c6521505c050486082611170003c800401402680028601c68440c03081085608050041400609032107000b88184da0550354060f4441d00002c014504020400c0c000300040203000007021007198280302500d540d0410b44000500c007584050042c2c0c042c50504 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 276009280 1250 276008030 276008069
    0x61503060c020607031e0b0102010209060a020705040513020306160302070c060509091008120c0f0604261e0921012a0f2012040905091507031d0604030801 68
    0x240600080d10b807144106d40c0d000300b65400e001004107003d005d002c0c1159400d03c002c9455440e50401000d01e441642c00500d0300714a040d041006907038004141000000314240c007480140c41c005002d0ba0000b000c00030303140080004c071100b100240a650704c040d00c0503041c00c000290594001006049016098410100c1583c43c82078000210000d880744440c50352107002c0140d01c02d03005001410b03d003084481620300c6850b070b141c6800e01d032550a0b5029030b1003503681c04566014a0140750003100302c800b040c148608056064410082040f01c8555074401080000b42400d0030769108036143c00110348401d0b00d10303da80d51004801d4020180220a8074005c0921685200c00300000d000e40503540c84242d4501079000d1500200720756800e182084a00c505140039546850380d030043c0150302120000c2c10010303880c0c03813504214401b500c0380680501000d41160b0319002c0440041c04455a114046050220311016042c1580411213505006640d03280602130a000800d603005d17144030b041b6140d520042e0400b0a40 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 276010530 1250 276009280 276009287
    0x10b1c0507021c05160830010e04030c020d0b060f060711010c0f05010f05060f0f0d03110f060a150b120f040f0b0f0f01061106010e04061503060c020607 67
    0x2503507100007581c04419030303890348a01c00701c004a00b2451072030030030300303003080c24910740c0704160103590484401c1c802007044c42c818400c9141c928110000b80c10032004406818074800280101070080c42ca42103601c00018043c076005400300c0c210702da405055a846080d11381044006400207445142c4a00044092071009241007000d40700e1140d000045621030b044140d00549003546d2041c411078401c00c140030b40102041c0300303200e0f5240d045d150382d10200e450716111040100d0300d101040c0d039500c69202c2c142420840d4039400c2ca41403581d0340c1802c159545481c040001407610320000007000f45032144c0020406041038a03008040010480451801e000e600d81c41c20140c0b50040301c20061400c050a00000c1c1d0807040c0c40c440c00d400a0180c0350b0b403466030b100f035100d043c8039030011500c0f2480b400076041881030000c00220254010070040c50244800d910340c0c129251101810311031401c42044080124041c0225948141c5250414211450301e00342c1d03a03d40203000e01100032813a00503004040001d02210300 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 276011780 1250 276010530 276010541
    0x207060908120307090f15030506040203010b030f090102130603061e030b0c1303060606170901060501020d0c080904091401061d04060f0609050117071203171e010b1c 73
    0x70040e00e440d003400002612290402000c640410110050000300302c1203903403451014118035828512511344990002d0182c4001170451401a0f10400042214040303800070340e50071401304095910b05882d0901664060300461118508410b200c50002031a80e41540c4a0b10445550540007202042031000c602c2e0340204c188400303080c00c801140069128140c8100a00f440d00c0391400c110075203a1240c680f070f42196a281c21070008a0514403a41141300b04846086903c03942850090000d0750800f00000e4880c091880350409025464900e0000c1103d40d0040c1c0d2000c01d07002d003042010501c07605254035004080340111410307510781980811080400c6103c4412510b1030120150962070799692103008204510207000c03030030750710365000c20002c000d801081d0083c90391380075401032035082024842c1045103550022021681c203403207020009811010551020310040b402da0b04079640e92201c082c09030403c0800420320000300700003042c036600110103406c05101c012200710309440c00550712421200c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 276013030 1250 276011780 276011789
    0x11151f05043e040f05031c1d01031b02011407020105090c0105090301020c010614040f0603020d0201080415060b03040b0f060a03080a030b0904080918071209020d0813050102070609 79
    0x2031094030340010000c40c0d85044150b100c40309104841c0818030104a401c03a030030a030480110a244908204401d242c00c010503401c02d80304401d900c2c203415100314050008401c16030544042900d0703c80220150380281c0c0480e5462185940d250611a40420001e00030305500100f011040101c00119a4035841440b0321481141d400009040b0740180e1001510f542d00030707100f801d03850340d000c002d040c5a250080c01802c0c0104024003200d001e90700080208010703280d6504050045510300f801c10400343c2c1d140010170b800d003034082c01c107607560f52650b0520440416915022118040c20058001041241000114071030390050720b680d402c0751030f1160f8480095601b074031081d6100c450309005001043e4000c0082804004030b0400240f884140004034484c1340b4211030503509964082002d5005080907003490340300460060a6540b6890b060f00041c050048101000d64801d54581a160454541c0300c4803008a80e00f18081503182d6214030a0140400c1460051500600440600107004c90003010b03a1000d69 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 276014280 1250 276013030 276013061
    0x90c05070506070c02040f0f050f01290d020c0a051f05010503031b030d0606020a050d090602060411040f181202010219030216080a12060e060d0311151f0504 69
    0x26101c1d080d04460081d0144c2c0c0036a40f083c0d980c614440800e255200ea6035001001c0c140c04191490408500000650140c0c010303028004250048081d20003510300c0b00402140c0d0ba400103031078208408c110380c000d00400e001007840e44110140f0700c00340b110016610303198070341140d001d00c6108490341c420020780d0f100784140e54160b130041c025200c13201c01c0c510862005111601c212400c01481109400c2900c5951380312801682081c0442d0003030000a00255584040e50304260500714074000e402540d0b420000c0004d049010300c014403564590362500903140420b450700003401840c1000c451001c000030003080803544a503034404500340e458010f0003503d288640441a9100442c8260402d03806503200028012001030f070307908108001031500380900a042c0341c80d9604811032041c800700131308031002a00402002c503400c10030005240e075500780f4001d44903171610340000038100b80748500d07240c42105802100c131580d85c0e0b010045c01c0b640e55071001d20785440c40508540b100d139540d4103120480c3d18209804403003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 276015530 1250 276014280 276014293
    0x1d100605030112020409080f04090f1401050105070311100507031a090a1a0604031103100603170a111c09050d0807021c050312010312051c11070c0e01090c050705 71
    0x110004600f05455890000d007000c0350001c6180e4480700c0c1540300400088408402003001e002014981c890000302c0c801c04802002161a40064070840c004144039941c1048800950300341010f02c1140b452048404017000c40304262201d5000f007002d0302085a007440020700e03007000820940c1c41071010800e5003001901480d401d484000c010000303803988590010220010503400c8840c1e4590308024070046001d90301200c1c0b8083c18504250070a501c0303d071000d268505004080c0041152031215076000d4081a4015645900754a005d403805a41d04000090380d0040c0035081c4003400c0c42c0312070f4002802c0c09a807000c250984600c20020f45031208031014000d04814801c150043c1080d81030910401c04406034031007140090350f0f6051031980103c1c4003c0d81c201c8000010401c01c810301854800c031049a080c4942080b0001c29200c109070912100c884840e502c441f1004001000314048512040c4c20080f2014107070f4070366440b507035005428030031440e01c00c1c81c00d120b00c140c040c850021380390502d030b0000c060187c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 276016780 1250 276015530 276015539
    0x32705011b0206030408030a0623220c0c050d020d020618070503030313060c0c03050702040b010e1005040f0806011a1305060304060902091609050d0503131d1006050301 74
    0x2005010150346441c614806001d00e0050382d00ca101440c829446519040e0340e03858510000d40985075035601803400c00c101c140408409660381c00b141c01000c9000d40c2da5091120303c028001c00070455206040091034605462200340c240d120ba800c0e070056005038116036130300340300d20f80480ea81c0000d280c2010050b040780c0003091142d44008160030b40d14a250382190040d5803144006415507105841d0401241d084098010401656024000c0b000005007020344111101d501c01800031b00c5019002440f540c0e41e21b0081c0c10300c1e03000385140c002040001d0000103203000060b8014180f80c0c064060221103d103076000005030010000f40c01e506940d140c21401041c2804201d00010540000118a100207034465020034142c441901452166004d42404100d001d600e0041c081d00c80740140541d03003602c0c0082208001070b42c1003c409012078100b07076110030035940380381040344c11401000c482069450480d1000200c040954403c0040080005264440ca4484400724001045644124404a80107100411 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 276018030 1250 276016780 276016787
    0x903280b0606121618050901050609030708061501080a09050a0f060f020d06090b040b2b05060f0106110a05060a020a02011d012708030a1e050906010303270501 70
    0x941000000e05035038141800f0791100b681200c000c03603403401c01803900b22004440513445440c2c3d60920180042e0700003000d0408022a0440005008860081500044062285e14100300c010000c3c0206070030f0311841d0400324903031207030011070250715400a144a000f10344000c0203845011141a4040002c03e141d0019544448000d02115019104a55149843c45184020f400186400c2e001c3e9800007602c00d04260200c0c04840c1080740c2140036900d00394100301680c44809a0120514100e407000701130b158654803009503200e2104005005000710005d02141030b2171800c4540c140c0300e01c2d8545030b0309022440e003800e988040e41c910103031165000c02c0202d0710b5281654020b1414008900c004140707010782c000445050000f1380e4080c03138260b5607800c082642c55034281d58048410648603448000b41c0c040d0300d42c00d100740000f603d0860030030f54403418403c2c081c50705840388010b0321055005000d9031402c201c096449000034401900410700c0c004004030304100540c240140d40c00741c40c10f4600c0f003d00303010045 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 276019280 1250 276018030 276018053
    0x60c0a030f02030d050c04051305160e03030702031204050301061d070507030e0d030c0b06060a09210f08031006050a0f0e13090b1801060303090e0a060515090328 71
    0x201540000c01c50500041114050184540302a03816147d9036480d0000744440c070321000c02004941890481448154040659009001c501c42e03d007d9101f1040000041c2c2107200e10400250702d8403e001c2441c02111504c0050300480344120001c2001c2c5a41c0c481c090f882855004e003210240c1010301c00141520300440182150700d01a1619070100310101d000710351503503411441503000c47c5403440c0c1c1d5010450980d10381580868103031a400e05242458501425902c80c1c0d004402c0e4540503c51000c00c01e08007810303200c00098005c802e04804500c1ea04042030141d1080e80c042c0d404401074000820300c01d00032000c44500d40d0b465902c1c1d920201c07100d04101c40c6818400801940844003510400030701c4001d005501307441d4040c04100856040c007404804a030401e80000c0e160590501c0410404250064502c00859400e40090022681c50f0104540107261a030460350340b046001d041310502a0800e40684a03038201070b42214080384018003540c9008124011244ca14280000b00c04000b4044200c0c4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 276020530 1250 276019280 276019307
    0x307080d020909010602011406040b062a06041a0708040f0602070323040f08070b04180e0a060c0f03150504320402030706080702100c020f0f0c0f060c0a03 68
    0x50400401d240040c8100f0000ea010b0001030b0344402100300d0030060026141d03084402201d0800031180d600300812811b0280705502c2600c9100e1400d10401c0010a0b0f01d8130009400740010303154245024540444403000bd0b00d00300c0c400c0c4103001c00282100d80210300e924001c03030b00302d00100c81074509030b80c40740080d5029507411000c0145041c0d041c0003e40c25090300140c1c6041d00b00046450b03034201000c1030303040c25060f40032050a51214400b04001c0078820b086405a50403000030500007207180b0140c5014203240700020200e40700f00156042032058540c00064415900e9031110381784076840001300e043e1200ba4007011080b840618040006150503070285000c04c11409200e40d2420450790308294110140f050804600100f60812045140500501d000762040d403d00810500700520000c0d501c4030521001204503940301c41e0080110b00810101410044100843c2d036202c102c55581621841042d038400d000b80c90a4601c801d60f8503101d800e4400c192160f078014070602000c1e442c210382a90012a1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 276021780 1250 276020530 276020557
    0x1206020d0609061503020304020603060d241b0e030d0f0e0a08010b010201060b0c06010320030105100501030b0f01080f040f020604171603200a08010f05040210020303010602030708 79
    0xc0c030300031051a03008800c0180302001000890f0b5280c959031100d00100c14208004040c41082081300603510041a00e400c51030030307507402440003003c1c5494143d0304019501d41d64110050300b0b8111600d034003500120040c0e1440a5908007001290790150741c1d10342034441c11980350b00001c0412071058880c24919012004900e03001700da0400c0940840c0d5181215003041a003651240c400980c02d50302402405c009081628800740340410391072502c2c0d00c440040c00000c16403002c0c802d0428a81c9055009800c640d60010001c1005040114078203828440710300c260741c00710b41015074811042c0741440c00461407e00c103031100c00e4aa07943c4215501406402071040311803900301004080541c03200c00140000c0c2195450f14602c002644000c8d5107000c4400700d01d04002d00d4582c10910004d07080c140f11100004d6044d4008450200c50400030ba881452504094081d6182820443d061034141d00581d0040c1e000b617540080a40100e00308070307140d1009001e00000342c1e20400421002405130001004213010140 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 276023030 1250 276021780 276021787
    0x1f0e0a15061a07330b09010b0703090b37020601080d0504032d0312060b19030902010c060513140a11011404181a032a0102070807030305220807120602 66
    0x803502e04850842d0005140e5864151645c2d081009105014005a1601500b010501e5a00501082d0b150241d1441048042040c089218909409080b140c5d11a000e1401d40303800c1c2c0704038100310030a80d04060010b20071240000b0f0010740120710f015130b0720516900c4903e8241035854a01c02c001012000c40b065020342d10030354602004c0300180c0c0507810f00c03943d12550010000c860840584000303810000d01c1620400a1101614008002500c1c0300c0c0070382008901c0848900040e030b502428074001400700b0b804c0004000c840c051903038010003202d128030803100318880031944090382e414514400410104002c1d0204480f50300507800510f10031150b505030303480c09880b560803c64003612400c0c5064459118007060f000411381d50603001700b401c2d0503001001d06000b0032008034000c10006807071140300c901c50a0709010300c1e44280f004a0181030108100c5905030340e00c3c41c001784240d101c012188113000d4103005120480d00000c811600305c44103180280603650500d04042400d04c0b15842c211000c96080 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 276024280 1250 276023030 276023093
    0x705180102070305030f13080708030a0e040f0e01060609091802040b120a0605161e05090109090603080d0507111c030914060106020705040c021f0e0a15061a07 70
    0x8200801d00500f090b21b900fa00e9221321100c900a41e54150005041500a0351003484041c9001050360010445c07884c0600840c42d1050114000740380305c54898503c80c0c28007010301ca00181c15000b0204075807030360f60f5002d030883c2d44814000880e40351804415800c040c1001c494003600d8a0741001d41c900c2001001980d2121440f0519440e14040131004c461300e68441d41008841301801844204044050a101c1718400301c1100700106400f00e000124203000001ca030300c03c1c0310391042c1c0c0c040307000d801c101c1400c004040e160b0401d0300181c0c014840784003040c0c3c2014000b5140611881e135481c00001140020700403411144d00c00002c0752546030040742010b0f504c2c0b4600020170700c400e624041e83c03400107014040b41d50422000030706004042d004a801103060100122017580d0005086540039144c9840071800d107101007507000038020324481030242c0e11810034180c0912040490705280784041034820801030b81d9640c8241480f20404202000014040c050000842c40c400400c1241039140035001445440c1c1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 276025530 1250 276024280 276024283
    0x50108010e071b033504060c0306150201090c0603110f0a0e130e0d0908190609060c050d050108010501030c0506090406050301151d010f052403040f15050705180102070305 75
    0x245044d000910b40003107415110059100c0582c42c0c26224881900000440c0520000d003030000d0401010f80780c2c3e0303c2003c08002e22030340c010006000841c6850409125007280207000e400c0071401540c101189020000c4d120f80684520404a8910f42c003680c01c00010308502440f07908444000024001c8080c80702d009556500410311451005400001e911014625814503200341e16021009200c1821414001050002111019520305d0702074568003c00d18a412409801c41607402032107035051080843d02c40743c014002e082d00c280720b01d1040059a0361204814283e410a01c0060045682d220083c0300074102200103094941e805800400c413560f82d1001701c4e084540e440542000d0480d46941441168030100e0b41500841b040e03c203c0440754104059240203506c40d10410b8480d1184c1d00181064419030440c08811740000418541c40345004e0405a11a280304842159100920010041040480d20034140640e205507200350801003182003180b07003182c25950060652180c040c2c0080040c20 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 276026780 1250 276025530 276025577
    0x3150608060604021303031202041a0c0d080402011e090902040e1b04030c060c06020c0601091d0309091f031403130806070c081305030f0c180108060f0a0b060705010b030606030304050108010e07 85
    0x4bc4015100d60b1030460b01900f600385441101d4100400c481c3c14148000344c2c0c0e020040108440101d450034040ca00c0f010000e82e1160383c682c0c08003500500105001500070200309400f03206154400340302c0700094006115601038822230100a1521400c82024407060f80b040203242d00061240c1001031a00c008810703228540002617104142c19500d9a06050310510305141c00c544030b203030460085003031003010b20002d1810b05c0014541c0c8906840300504035080e40c1d14455200056800442c0301c840c0b1001c4401d419107035440b420b1200b10669060400061850300024250722a420070340e9120f1101c440e80e43d646440364802c0d450565400141c0c04081130554040c014030300200030010041c40d2081d00081070000200f240d034408203842010000401415401185280d030104800d100d0440d5659074107540c000920b042540f6582052001c9902030070008150704c50003042e10224101c0300107545540805a50b4071441c0075072800501c04d003004002c45001e0011207a042900c5003011540303c80e00010b440d11016 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 276028030 1250 276026780 276026819
    0x120a0c0203030c100b0105041202040b030c06030a0506091b0306040b01050c010606020304090513150b011b0b071206051c020301060503011e0605090c030414070315060806060402130303120204 84
    0x2004244480600d130118400c2c00040c0d113082c2402070400340b0707040c04140c0c0c0d4030340500040d00594895070001c0321070b6001c0c04a4203013800001c2c41d1580b00c2c10580910300040c0011160b030740c021200301c4081820403e1180034481c4401502050501d941c2d03418040c440075100b003c011074184034050004c405015030a009a0000d44400d900854130346290040c02010390382c01500d00d5410800205001000c0380f03080801e0307280b91a0303205002c1007a24041d401260055051070090354420310346c2403154100100354010340e0081c40c503651060364800c0b07901522800c4400e1481010341c0070684d00134554100e02070784125201140001c00015002e43d4690100e425a195402c1d28620156004030000051115124650140a06450540c1c06140c02c2202c0c10480c030000d8400750180b8240d800400440d8010041c00d0041c51340921010340c00300b4001204000f9056500a10340c450003410300003201400d1610959180c1c141c102100000d00d482c41d1801d0350300c45507004403107680c15020000402d2080103002041c0701913 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 276029280 1250 276028030 276028033
    0x619030c142103030f0c040806010f0e0601020c09160c0804060309021009060c0807140703050c03011d1c09230405090d0e100507061d01060503060108120a0c0203030c 73
    0x1c2426104000c50041c03101d8031414484000309400780004400800c1d04c0e07001c1030603811203000f034503800e01c0380d00a402280d018201500c601800414101858003195088600d0182a103065480d41c9005a0f1504030201c0c590390040e100d03000184440e0742c20440c22040145505024944101c26110050b46511540003207002c80d441780628011810b144441d12003441e107610b02000802e09000c001452050400310240020380c0210728002448882c002101c1380401450440344003950f82d103040340c4c50301048803aa41c400c0d4a0410b486400c2d480c90508403003500c0240000c0d06800c180c115000046140ca0000362013004070351103000c9580c0305010704600f405004c01240102d418281800c201c20740d1710090442c1629003100c6d0301200b0160300301003020001d40040750103102d101c9450b0000c403107d024058010340428104420401c94420b08a0340d0017807020f210780240300080c4c8030800c0c1950b492081c0705411550303102d00040c4054108090141002500501d0310403c1c58140f600042c1c82c5400814280b00359 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 276030530 1250 276029280 276029309
    0x180f030203060c030c030115120f0501090b0d0809040203072c03070b0a0c120323040b0a06121407180f0b0306010b070b0411090f0403030509010902090619030c 70
    0x1035107020000c440e8401c0c014001e940c80c501c5c01c040c07102d50b20700062050442004c10b80410b0080307140913005151704020f41ca1010811018040822000ba04080c8216154103140c841010203d041c500b4140f0f0995401c43d089a1801d40c41d00d00b84002548002d00510811180c08042e140006103041c007002c1030f04852070f0104608000b141058100240390740400440380d810001c03415a00d8100c10030000e800d0300a8640f07827550411880c2503000e0419411030502240a500c0c9045070300ca00900014011401014202a40c3d40c1d0700105c0313030403503502d0b005650fa142800a684130020b008281000240e0000310281c489980c1da070400180c03038020102001c00344a03120030319401c8145051144030b40d003e00880041443e9450490018103900c14900040c2070700311110000b5051001c0640340a0b09080c0240031107140b8508698240f2001106940850003e401c110106900c040e0500031405003640080c5251203a8440c1801c210941c4180c140d40c20340c009002e90000042092840c0d440010045040c07407508 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 276031780 1250 276030530 276030533
    0x61f0804031e0e09040303090804080a060b0307080606191211091303120207050c06030a0603050f06041e050c1e011407120e011b0503070c090219030c180f03 69
    0x19490b820700d900b50300310211858150a550b1050701d000021800303680c04851629542801c5000e01090080174069205c001000a665400010b408840c10b0145104000000c1d108081503250301c0380c3d1084245079807019000c03407003e142051082648402da4500301d004542d444d00035590909140700c09907422400040700b600070b420401811a400b69080b03c0c42c7d2079449241e503018141442000f40189003650215900c810403008124030200c0303200041180d41c403071900648500117407210313000440d014013602206201c941400110039005a5000011603000303441d0008500100c41285000d5445d0300c07608103858955210844007144000006542d46410b031020800034005803e445820b026030b4601700318480100c3e140c00388011010029243c5402c3c010741d0040103d0b039511000290161602c1241c582508202d40080101000751040305030714199952020742001300c0c003e09a031100d00c019185140140148298401071403920242442c61042e030050980f0b0a0814858009045280e01e0306010310 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 276033030 1250 276031780 276031787
    0xd08190522090e06061809030d06080d18060507020f010c080d09110a05010e041a0306070206090c010e0105190306120614011530020304050303070e0301020a0e09061f080403 76
    0x2800c3e018100a2a05043c013102184544184191410540c080040400c60200b0248202c984030010b02c3c00c24064651207a0819468050809c407210101d003038211880c044422f54800607085039010740300c15040c11038540a118912403800606410040747c0d001c408000390480e40034001c6201e41880008849040b4500b000081030b5002c4410300c1901d50300b1081015070780c80140303d0421601950003069841d50002510500850f403070095a150040600304101e081e40083c2c1c49100369039400499005050a000560311201e06951280c0000e000b042020359040c148111390116100c5450000f84181d6201c80000c0b900d9100c407401c0f07482c03680b11400c9243d203804100701240507103448481c90104c03030b5200c1c0313001e002d40c82d000d150040d601d0403004010010501000040400042a0f0383c08d5540303103410f00d04170742c1740d900448078107001c45c640d0080e0310b00c242014829074220b204140c03a03c1040016050400006480086c10b8661041a407041c64005450901315190b200d186519464001e04040c07078082c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 276034280 1250 276033030 276033041
    0x4090209100e15090303040e071806080f0105040518120c1005061809030903010504140f0c0109090b0301090606080604031704020f041d071401020c0d0819052209 71
    0xe2040028003031a40c09183d54030081c000c9880000007085607200c507284003090450146a10990003010080c040003600c4d80c00103401c042e0851000c8100b0b601c2c0d40c50744002d6440300d0084d02d0b0749051203a01c1700140b040307007401d500c1580c2004040900400c46100800d180b0700d4011614000c031a40040411213001c0d06a0070080e03403089141c1042d040c4014034001011585c50005400c030f103040c00000d41c001c03480c000018000c448500388058002c0c4014941424040e0400c0b000b81d0b060446841403142841a10a02203070341d40c1d0400e0143e66441c0301601e40f43c50000a0040302c2001581951380745810000036807039105e09070051101d080944298606800c002c0c0c65110341e40708a500c01c010903810000142d507401c100c005514011280010043d140f00045a0341d4200c40a0740085031049510105d180707040640150482c0d1403d900701c034210b0300c20300b0502c12800c1d00070200410b5440c06011a1428180408a411034a20a0b00d4402e040030580d203120514809041c1826100d42c07403400040c001003607a07008a = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 276035530 1250 276034280 276034309
    0x7230d050d0614090606090d05030a210902010e060307032d0e190807111905120307030e10020f0303100905010b090108070c020a050612160318110a0b04090209 70
    0x4003003884843c40302180c000900140018031942d400110400c036585c5104080850311340250407a500d074030021102400c84d02a0b01d0803801c112040750043c907618a198020b10208540c10703034440c85103040c1c0d54140300640d00042c00c50411f15454822110103168000320780b40020b02a20b14803880b00b22214024021610800c00003199600b0500340040c2d08400289c20080580d4001041666028241052111030740240c84565210000602c0c00500d00c4200d014181a40c034101c48501c9961081001e5075660710032088000c01244010010320003601c2c040c1380004800407a0300540d104003508021190966104403041c10b60300070040d01c103021010180c0319950243c0303c0e02c441c184c90301e85500006405290001d01400411145201d414115103440c1422402003401822403a113402408100c44100350f800c030303001c80c18080101e8400e107003503119014140204c100054110114105a141d940040400d507991942245000e200061318a081d5001003005243c410801a02c0342e224904000c10400103401 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 276036780 1250 276035530 276035549
    0x141501031104030f030912050a062706110d050f15010203040e011e080115082a01050703021903030614040507020304050f03010f02071b0e01030807230d050d06 70
    0x10380c05901001c24201c030162900b04c04c4440344100e00f403404540c0100301e5003010310104000601c900c1080f00c000b0350300d5a0f01d03202d500103002c80340d18441c030040ca4981500c40d030850440f4220300e0b0740105046501511600c4500d1080307514100c20b14500905450007501c041800442010402c00c0a245524590b04108001d1028524044c0b4040d0130b4004400c1c10301410b2070108828000c003031442650800b490041505000a20070100c0700c002c41c00108809200d21202c50148503001841080345003c1640e2000300002000900e021302001110681c01c50346080302948981080c1c0c8178010704403c4c000000d42d2007990080303200d80c05d1180e07002c80e1081c02100640900e050005000391740f074000c015139080e50b8064400000100703400000a0247c035041c20307002c211034800142c1750309004c01a0048510020307481d401040590b0b031808031000c0c0341003d2101408250080c44400c0001e010464481003100f80c2a844442240207141440d0800040004c42c0002c0b030000900600d41400a0159000500f100c4e10f = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 276038030 1250 276036780 276036791
    0x120b091002070803060402090103090f080a020708010b0a0b07020a0b04030507090b030d0c06110f1225020a300e01030c05040509010b0f071b0906140f090408090414150103 75
    0x1e99142484c00041c0280703220b1a00856008181d0348640c0c8000134840e04103503040f030354164a0500c2d44d15648103c1d5503e0050040200c0411541d1050142c3c83c00d405024008020306c504d4000030000507004003404a078401400000010400d404e1406003005e1401100078241c1c032450150030034103c0709005000360181d0422542e07036103170942007904201ca00f43c01c4040420344903200c2402e0300c040c2c0321f440011074124001250b8400000f43c0c400d0b04070b1190700d00c04107000d00c103444a002c0c03404240c10700d458540180d0100b00920001060091000407481091400a140406e907520b091085100002c8010001e10002d2140712150307414001d40d0721302d58032810468501030505011a11400c014020b100c590280044c440c0d00c1c441400c421100495081141240000490034a00c07000200c60311074107020604165010031100342c0c04a02c00031403100103204004132040101400301d511001841a50510014001c02d40242c41ea4081c03080c12000001034140c80c0d20740075010341c0882240650050401d85020b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 276039280 1250 276038030 276038033
    0x106090c080f0702070b07030503090f12192001020307170603100e0312040b0f06060a1215050a0f03150b1014131511010b03060a0b0a120b09100207 65
    0x10005540152400c0082c03802a540c04005030b03d44002903204000070400002c2d03020500da40200a036018013102800d407440c1100002c03000e07030380f21603c0703807140409c40c41007040d1300f08080440c202c01c00c0c1094909028020015106140b55030200c074880388d00040e5000010404201e03440b000f140050507200900d40301a00b031280110f50786400424050340807035512003450020000c1003060721003c05003c4e603032035810710341880c061b00c400e14165105110038401d1808207505140c0482550fa040c0c03020354510030b84005000c0c0b02000740200c601c0d0346890001c00079011415484907a11071001e05840111840b00b6032031894011141d12142a0449010340b50042d20404c55443d85403210143c0024548500e04040d01c01d40003046110700310030800303e14420200000c400e901411280202201e80d152034100c618a501814240d440c40c01210f540350300940001120818a41e021000c84c0001401010440f03440e2856206440260a0140d40c002c002c03604001548804000608080340e46510650408529 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 276040530 1250 276039280 276039287
    0x504030e04020906070c08010c0215040510092109140a0e010506130f03031d01030c02070605030a111b0c19050d02060c030a0e130e06040f030203041205030c0106090c 73
    0x3030800c06114540000340b070306107540c0712016540842d40010201254503512444140200140c14003030016010355044011400c10601b801c41c8140d4018010306152080180480c00410064504464003241d0b104070303503000b02510900d803201c00c0303850f02d8030b80c01c03181044414600040310958a610a8041e50424404259203035500c1341152401d46500ea280d0188110b02c2901003204e030004032070700e64659030010034554045440b4081140d4445c200d4a41d10382d640045003910302c0c0c811110050382c03101c0010000b15200300b00850b0b0051850100080030300358122543c12550000948905010007640540c0c1162024011840d02e0742d41100c0c1d0320007221800c010300c2035591091103124424540f10794003000755140c03601107075841303011107080d690b4403050981d001d0141e428442c07540e8010030980c00513101e040300074421040c44803e54070040440703507110b9843c000c00030301100046003180018000052640c6607110100c007035a01c00c802440e2991b04180b5002d003114025446082191b04016441818540 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 276041780 1250 276040530 276040547
    0x6060a08100e0f0a050c01030f0501030b04021e030d182405070302070e090d08150609090c210702010f0c0c020d1a0c180307080d05160b0c030406050901050403 70
    0x100c001c40070441c5103480300307401c1c1041d1580603540094084c4400e40f60030404007050740340c12504240c0341002500f807084198801c0301d10901008254100741e8002c40c001d4500340301c82100d40300e108080100d03a403111002003800c3c10ba502c0f02010104503002c1c82c0710a00b80740e40342518041c00c4005c0b09030800012004100208040c582400028040002039400034184244900d0f400b60174140d00c44481c1d0304100b1503e5030344101042280d00000c40035008281c0030100c8500310070010200501607410813020030f08200390030b280070b86803c4004108008120001c41da44500d0010340d0b03111890151a45010440030b825a9185584261018500005044166001100e500c902d68064440d80c81000451034a114500c0c600075151041700212000c00c1210110380004085420b41420b401510f07040c075000b8107a031510a40180c0c1002c0c0c02000019000e503214402410003401034440116030420951220101958207460481d02da400000401081c03103400d0040d140c010a030032000300503a10345600c0c010003480 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 276043030 1250 276041780 276041803
    0x15040f0f05040e1903050403020301140711070305030414120d030207030809061e071101050c0c010c030203060f04021c051501030614030c06030c13090b0f010801030b011a04030b0a050906060a08 85
    0x244c070211000a1620a905480203558050002c000180c103800e890301014608444410018020000d1811000f1700411010100c0c2e9006000b18102405c06e1041d002c1a07044e0f07640a60002401e00d43c480c1409001c0155804d07128982c1c80040c0d82e0201800c0c01050a13030018580343d00c540c03000c1c06214cc095402c1e00314041000c41000c05d840e031900c0d40441245c1e14000700741003c00541c00d10042c0400100210010b04440030b952008005a6154600a0341a40011030b1103a0b80440ca00d034070903980b802d1640040c24810072500440e440110010b0108044a8060720510055042c24511801a51f0148a11000740900c0d821601c0180d01180009030340c1c05145003842e000f04001b00c003040c4005003040580d04118803503041400d002d034039000180e0040c01306080907803080448001c07401103940105820750507070f6000516040140e0803e00c100f1030420101c03860485290003004000003041040d4290f5005000014002c01e603418440c50341e62500c200503107210706c81e45080300e0030400104005000c00340c84 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 276044280 1250 276043030 276043063
    0x21c120c060b0d0b0924060f030c030d0e130203010e040318080a03020a0605100b030a150306060b0c0127110a081606020601080d0f0c0215040f0f05040e 67
    0x15141480e051015018212074140c00501039a00380b4100001e22150500c101e403013070300310354026480c078242620101031860100c1801e50201b000c5055414120907043c41c003500a000c8a96007261040400c1c030300010300011000052118641050364078280420701e075103240e48081035045504001d43d0460450010700000c2c14001008010000000d060398001d00030a06030040d288405e0190402a49481094200f21b403107a203418002284000801da5007400d552007004c00c5415070b96024241c400078800c152a0006440100c040040010b19a0045a02414502d120182c80d03e026052007820360b010079000800d0141510f10198154981505c10a808d80d000702d4064030700305000020608181e16038020228074081e10b03030381b41d10225069800c074003154000d60071034401d80c0c0d0324001c254441c8640d659000014510b42503898010740300d06039550845000a04e03040313503400079201c45101c0f544a1342c89141d400f000d0910070840022303810203c000a00054070288148170f125002e16880703124607242100b10 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 276045530 1250 276044280 276044297
    0x4060f05040b010c0c0f1809031b03030e032718060103110f0301080a14061902030705130833130507090207060b0a06051306050c0c060d09021c12 64
    0x2c9030321600700c04864503002410381000c02d4595060509400d850701030b804e60485000c1c0045070591583c8030720f80c1d58a0705560303007102490002c001c0050700c1c10428415401c060300c40005000b0b111061004008404000a010b1500200482d140e4040302c00c2c980340074401c40011101001440408910070740c00070b000d28000602400280d4982010b024801c400b00a244012001040e0720300c000400c400310501600c010500c03404481410b50740d4a804860060203021141c1a011400400b41c01442e040101ea088c400d0800c62a0703940c1040d40342ea181d12040316070340f00c0c1048080c0244c010f1811054428995220031100044050403018504007801e11030717140c041c81c20308506014083c400d00029000c01c5505655915160809030060b149003100c4510500190900155190082d4102c40c1c110440400c0d40710403910307180d0151459045800c15055600512000c1030740355075980c00034009004081000911201d85d80140400810002da00b100c800ca40b4042d448046100140c01001c014240c0c5004103d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 276046780 1250 276045530 276045551
    0xf010b09031609050402040506060a120506060403050a0b0f0a0e070314162310210605030f1b0102010204180c020705120d1403070c110f0306041b0504060f0504 70
    0x14020a9980d0a003201032007442c0801da43c1c1c0a070304100d000d640211401d010548400c0300301701d80c9115059400700030504030040d0510240168010540c0b02c40000e154078101a9a515010f0800d91401d9003101c001c1c00c035a04110f0b11881d0f40c560990030021000003008000e10320081c0c280e0f140298040a070070180031000900c220082001160385041e102d2022005840d90f4078402c120a8040380c1a8404880c084581041d0a0800440c4110303a40519525050340c03950410800281903605a034418140380c0320040490261000c1220240c640240030050004400162503000580e8454041070b04590040000b04a41c1d44040b02c0d603920311454040001d0004e5040350140c0c0341c140650700c02d40e0040e11085c08080e503590041040c507800f10494842c01c903940503280c104c0c40c140c4021559080490705200c007160204040d60b21541d40008040c4c004000c0c01c0c1c0d5400080d203000d0084a0403039403440b50410340d500c4545004101d20040c08161001d03c611810000c280c450208036024050280782c0d2180c1402 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 276048030 1250 276046780 276046783
    0x309030d0c15110310060833030f030a020c09010b0a05030703021315120c080a0b0a0302131b0504030c03061e090b0a0b0a031a0714030708040c0504050f010b0903 71
    0xd045120b0007800c20840d40c820510a1054004031882c82c04c442080c18002140d50151484600c1032081c2001783c5201510140e16001d03110082030707600c0302140c01d02d5800030030f0f407010060008484111401582c4843c4107080017460040d1410480f030258981c24010403040b0341403c01da60000700c9500304591282d8840c48110024062550798121240c002c2400103844840300e070780c41c02c11101d25966603046480f0952000180c0741d4041c010000905500002580d4804551001c1c4950400402d0b040480f540e94001800403500c11159010481c2c0c2c80307042581880d50a1a2400c0003160b500f0117504180c559281c61111100900c00a8400c03525103a0f0f81441d10008215080c0300042544100101c01700c0e070412006c2c900c0c0442d04010440d2401e031300c01516207410345581c42100d9004140e0403541c0440d49a48550020241240e001e100a0b421140000032030480079520400d526600c00c440c518190921a8120741c02d544010700603031400d070500c051099640f0b1090b0648140ca041250340c0c44011000c40d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 276049280 1250 276048030 276048053
    0xf0d0b09030c160e01080c030c062d03162c04141609080109050318010c0b01140406141806010e060d050a1d03041208042606090309030d0c 61
    0x2c40203030043c408901e110401e02803c1600741c07402c0c46910b004982e00c415000b990b0f0040c0d8580503034154881d50b00210306190500050840748815030041100d07426402c0901809000e03110309000c80325011040021510300c920156001c034103e450f220050008581445180700407425900c482c4001c481481e0809442e40c3c0c0010004c8010388010f807890313203030550410145165200c0010009041c2d91000a040c40c41401911822034001c2e000d146030803d5002000302502d0030b40384181c10f00c440c4a1500010502d6680b07107a000b4161503c5468071010040200422611143c00018202031b201c036500c1803030740303a210303224607031810041001230103884500046c1d0f98a14031100d19a0b10040016110142d2440364002c28042c0c40380850911034082c0c50050b1001d4000312440743c04196006110400042e0000d071200d1841a001b1031803207141ca42c49840300821450050580c040d50380038071034101941913007048001d50040500d0055070038003890328002a12080f05200e40c404002da03542240c0180440103854 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 276050530 1250 276049280 276049297
    0x303011a0708070312110c060f010f080c09151c060f0212060f010309171312030c081b01060e041a0402060405040b1c061b170f0a020d0c020601090b0f0d0b0903 70
    0x10b05840c0c0e00402113803a602d032340c100c500d455403d070a10000a480702c40c503980304083c0c403075102c098000c10250602340300d0344280003800784402513009020b5034002d0301c950010b44105c40100340c10300d008800038209403040c7c3d070005583d034110910400c085c6a20003401000a5003001c01220042d000c08030100040b800780902c020b018110400c90b08071103a80c82c54100080010b180300065480346165035441d811000c0c204c890000d0042400d0186140000340160000d00c000020549916034901081080c80c4c2110803641011401d18904820321050040303035083c40158007580307208120549080d0303010401900892144502440d103c400940096544020b80c0010f079403200c24104011110341441805000000518003c0321070b07411410100c240f08845181f90040348440b03400c515140c500624031300c81401802507800c035138248000500300c40c0c5805080c4001c90789600520b22941000041800c5943e5007144622440500110941507190000c10b0208180c100e100740c03403541e40d46040d181c11072003550030 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 276051780 1250 276050530 276050561
    0x80a0c06050708090114090a060504170316090e0709090b03030d020d0507110a0b01140d0807060b0103050a021c020703110604080a120209010c0f061b020303011a0708070312 76
    0x100809107900460f1244a00c141c03000034001d510408007912241c05040d503900701241c1103400c030800460304e90340209401620901c0400401894a0000003207500141c81e001c07030103264188409401c44e44060b000026102d005401d01007400d10752400342c45031401e0b11580112644400d40154166000d10a903000011a900c095550701c807038034180301c0108021500320011a15080781d440c0400e81c0080c1d14a00035601c40e250445030390a00b425007012440614040c1d83c000c04c900c40c09000605250b02420340c641c418a40130540c03070050340000d01034610050403400000e205100000c0801b50011050200b003d04290040ea20382030790408071841036a4180840f17840c42840c060004108130100205004081580d4844544490250480507445106819800034204141c490080b070550600c81100c40c0c0b1414001818228140030006d9812100c0e030414056000440104207404040c103100d900049502640d62403c0349550b42c1020900500c44040c040011100801312402000da100e0340c12100b0008 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 276053030 1250 276051780 276051791
    0x9060306060d03022104080f060c0d0902040920012304290c101a0a06030e0c1f17010b1b030705030f0a0e0907050d09060204031a06100509030a080a0c06 67
    0x38089491b0362182c0301e841000e110700c00708000784280110380180100b5070082614034101c65843c102c00600001d040a9a115a982900c2000640d04a000340c4107a0b1500d01a07126001c1c8010026200b11040b0440c407443c200b40754160384030520300b41c04460584040b107040008074106905001101b005806004002800000d009290a840000c0000c940c0207000420301c039008035604206503032603580f007102d5002042520301b4400315009800003261101040f0480b50007010181c00600781d2819404150b22001c8942055601e13668401d410340c44010500b414a1815494401d02480324801c1840e0103565030007070301004010070800d000312105940c0140031281c44040348151100240c1c0452800c0c408142c4200211015003000709105101d031500f030f21107504144044924034041c000a40084403443d90810000c030000d9500002c8003c18141e045a402a40c80c05e902800291002c4c500c4160034800280142410b503038001851031401341d484140f01e902c6a00c62081690041900c960040200b824003 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 276054280 1250 276053030 276053083
    0x100e03280803091c0203040f05120115031211010504020901030209090304120c0f23010e04090501050a020c06070519210c21150509130b0c030a0b09060306060d0302 72
    0x1134030781300d90f4806040d8062094964100b80e0740c13403286201d5844000f064039410006482d1022080c040211403600110380c84246c80c0140f044244181c000315000c22504405426041d4482e0411415001c4c1c1c000800007801e080c3c0005808a0f01440f0007886003071060300141c441c490038002d0324001c2104030310044e611303a4a803403c102c0300c1102d800ba20003908502000020a002d11a0f200e13a94082c1030050740c040b101d001001190012000d04131150015103404501e00090700c248101885041a581d005848000c3c9100090410002402c4c21040280a101c00310501014a47c58906103900341441d500842506503824100354800c5200020985814000322060b07802c940c80d8041040c000441002540b08052003504991000c0101a43c450311100140311a042106865400a02d011551980c600d050303030318900c5c81c0c00201c50040e001c80e00482440340c040d01d603001715180c810301103030450b07110b01d00600840d40c1e581c030040c05544140d26151410040c54024004c03501401840b038584031901244 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 276055530 1250 276054280 276054283
    0x4120b061518040b0f01050304120e0303040f08010510051309020418110a0f1a0f0c030c0a06050903041206020703090503010e03120906090303070c2103050105100e0328080309 77
    0x8581c0ba0901541c24948541d0807841e0041c3c060144000c16107640e42140c8a984400c200d00801440107020301c1064081009540e07001c0010b40011700c80d90003c0617400d420429520309440c0050602420b541010a040c001c07030f03030f0f8000d8090260344414400601d007941800010007400701c1e09040002c0381c1103146e005c4c4c01e0185c00f07104c89441c4c05042d40d00f22541982c80070002c400458502c58014105da407c4514036200c200c1d13030000d1054070303044410242014400c01c69141154400750300b010f0103a100c03800a0041207458081c02d03501801e08005107041c6490644111140c03580b003d0001c110a03030002e04034041500480d1803030080d00e405002004400585541c5a03542d500c0340400d21180f141e02c07130014594100c001a0f803071041000c1c40c082c50541e2108041a584003c40150440348500614925000300c0c1901404c0c03212000315607408903503549044140580501342684102c104910b611106203207450029030034103042500740301c250511104011200301602e1101000386100000030034131500000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 276056780 1250 276055530 276055567
    0xf032a0504021b0c010f0504060c030207030203031305130207050a03051b011505010e1912080d1401170c0901030318090504110a170c0108070905090406090b0c04120b0615 75
    0x1201d0f0200d808104540c4010345540240e04040c0e40041c0c0704110030702030345128240410a00380f1a004581600b030700c1c0e500281c1036070064403d20040f0415140308003c5803400114280324030401e40d20440c5440c15680b00c040c0c5440c140c48002c3e00703103d00003800e0786031040200136100e0071345003800c02000f2481a0b900c14890902d894484c2d24005982c00d03841604524042c400b942c05000010107680c02c0a14089000300740f4103038400c00340e0340d140043c8829170740024140034240e43c19074504040c02556040c081c0050b081d48180340d03c1501a03001c60030030203054449014031410b503034040c2040e03000d24800301d6401e40300090581105540c90b0911003440208500301c401954900c0c81100c01c4000340743c8880006420b13998820642c8499800816500c41c154068900300c0d8201410389000094191240b02041c003040e41928116000750780c40d0307442d40901c0021a691500b1120282c01c40d490546040c40312000030400f0351018090320b0400300071506541e501440d800442d814085074644805189044924641 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 276058030 1250 276056780 276056827
    0x203010e0105072705121504140601172e06061701050904030804030c050a0b0c130e0106020c01050d021306080109150e070507060b090901020a090f032a050402 70
    0x404654113901840f41807040031203584140382e101070311a8646401c03c03060407100c0c0c0181605000302d11211140006104526104500a4242925641020600601d0510141d004082c0805240c070300f100b0082010509075089000145440ca060480400b9140ca00140a40c80413130076152010000c1c0f0343d0707040144030303030000b4100d00e1101c0240c0e0381d44184003035402d04860040c0003175006400540082c1c01142d0140059000f00101d039100d401607550080c01d92002e8174062506a0040b4600c0c000001d00145c81c4060168802800259490620082d507a02c0c04c1c11166030500c4000300341e0001003205039068541004507844000030080c2d8950014100b0030080c0a00a101801e0043c40d0014403036070f5110b42c0c04c4074840940504143d46c1c00d6801c681c1500050381c22100c468540c4080e01c3ca0380d0315403800c1030042ca0340200040e030300c9032000005050b4040c103074440002541401003c00100c0e1102064014981e1007149200e105443c015424031501c10301c0e00001d5001d40b001c94881c81e0080325216001c0c181d03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 276059280 1250 276058030 276058037
    0x8030a030c1d01020a080f12011d1f06050c0f060f0711010203060616020f090109050907061b03080c0c0a0302010b01030e031c0b06070614040302250e0705070203010e010507 76
    0x42c2e10010740c12218403150286540542d208202203030000c4c50b103000801509101211060600d1140110300042140a0b88030991750380c010349030f002d1a912410714681d08155040a21070710302962160000000e48540f10309801d105002c43c20107843e5506100e8403000042d110252a42860310440c040d15241702a1501d10000d80012008a040081442202e0203814002e0800f800d1800c4620658188640c403442207801050740e01214055071a0315141c1d41c0a09103545e4046854900340c0902d0303107010441d078820810000e803005c0d01c0c41c04040302e2a1101d280c5405190a401035659820701c0822446080c00204807071040103030328014194198406041d5050990382400981301d0080200e64a01400314800083c40d450004065144619403100000c9180a0700e41402d0800d039884007800c4035481c2c0103035070280510314200002c040d410b10103844940301e48442d80c00b0b201d0410f450f0b070442a465004124036442d0310700110302c40ca03000c2c0c802d0701c200039402002448803001e44583d141c041e0a0540c1d20a010 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 276060530 1250 276059280 276059297
    0x12100e070e091f02040302091003060f02040f0b0f040e0f0106080c04082d12031b0c1209030106051309060c0516060504060f090f03020601060201091e020a08030a030c 73
    0x825081c0c120034024600b040040051410200c0c081204028050b41a41d81d26800c00c00080143c49002c0503612650f40c403510860b00d20f1031414804280c8080301d640c4119148104810f01000c034083c400f44054032002c0301e220752100c495001041d8039208540007503150340300b0031b420004020b00300c00c141c0781a150107980f010000d4442c0000200315020300c0c050b00e100382d0404020703d40207030107440e507044421104034914401d0000c440307240c0742401807a900c4000d62041c00020482000719800006141c01c84c140e803030300c0c034108610010603110b0203400043c08401c40005900c1000c3c1c0d03000d400503005008001c1801010f03111601d4200f000308612a011980d2fa400e01c00c003080642d00680070398107a070540c0ea14081e41089183d4a1000600c0c000304111466903450540700d00129107031040304240c5108031454800340b002802c0191800300c0c164081011a0b041800382c2000622034880061000d9000d070100c00794510900c00a481212542c0180b4164440443c0000d031a642c1038002c0303c4405600d0311840c01c03 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 276061780 1250 276060530 276060539
    0x20c06010315050708010b131e170706020a03080a0f020307200a020f2107030503071509020a0e04061407081e0f0705031f0308040914040b010303080612100e07 70
    0x165901204c0a001250102d80100300b00c80c40540142010119078056042d00303521900804440c1203c1c1072581200ca0051100340701e030a981031070184040c5944c900a203540741c0f9040e0020340c0c0700441080281006148030118401d02c0701038012541c0000740400642d182d152001c00104140003803010340341d170007003941407650f0101c502007005901d494000e810030f44540490002e1208400302d079000d0300301c200c1d881c003806d0394400e00c28000d00c800f4521860286a0702c6590381031020002c1300c85040303d0b903d10314000100005981c0ca04160048981d0090100d40907503440c1414001001e4005845025440c1d10041010159000c0c0c0004d100720000c6000e01c25500f040c0421540303c5408460000b002200d0102007035000703001c2c00246a2001e0140404261003052801c0d65012400a0b07104072144c44000c40c050180f0f40b0140100d5100104004160344c2c24a02910348178400d04062001900380260240821015100c44544c0690082c107001154541d24215402200602401c41100094059a100400c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 276063030 1250 276061780 276061823
    0xa0b0408090a050f10081909080a0206160f0c02010311070b04020a14010c0609020f061c06060305070203120402063105060c070e0601020a0f050309240a05160501020c060103 76
    0x4da4400001d048020200d15103e002d0380c03442000740071480d4a1950910f56409407090b07005038544503115104850300c5000e05d4001900c1c20201030b201300034640c0200d05452a81d03512000740104a002c52030f0024042c00c2d00d0005a0003000314400c0380056010000e01001400503000802d4004c42c800d4030401d110a80c0c030722100000b00f40311081c0c3d60008080007032042c00b0925a402c040342090000300840c1c4000c24000c0050714550040814950030341a14a0f149250005446104010700480c01c0a01c29403401c008029201e128503002002c52815010105081d502e41c07600b030b9803d84003009079403010300c24080318031016000c2c0320b81003801100d0000804100d6060030781c155414800c1c3c4c1001010550b0504421595499008000c14118400e007000240401d803803081800b038050058000c0c41c1d4030b980060038401d0422080100c81c50800b08a9804240c00a540040b605412610300c1d1068440c803444ca0070304d103000062034014040c0c1d8004a00900804404204281200d00c19115280c03011401040305 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 276064280 1250 276063030 276063049
    0x5031f060807120209030318040605030703050f0f06060604030609060f021303060e160b030a0f0203041101020c0108090d050d020f0c06010e0f010803030412030b191401030501081902030a0b0408090a05 88
    0x130f1750103410900c00c0c42008c51402c0c0243c03000d684028400306046448101081ca000440d50080e1348035071120800042101c07090162982204200700600540e20300310000c104584158800104446c0c0c0c1d43e0701d83e00c1403003200c0d806010740940040003559160400d550f82c80129070640026201315181c1a000100301070f000615107204140204804005464400e51442a0700300400941141b0b499030f1a2101401141c40110322661181c41031000250200000a2508a41c200c42606006059040c45400d070400184c1e00c245881e9464504d941c0e10503031541c0d40290051190000c02c05602040610001e2000308902d4140e8003146000460b42d5910500c1c010801005e1007803120341c0d001040405d001c501881e19802c0405442e04022690b00d4415000c213008000034010b01c0701e030001c13440f41030006004071100c8012580c0c003442c09000c80d5052051031500c80c00c0607a940502c0c8007285642c282192818006088226003000251f0b12520b403078200301201c0e40c41065050312402d100b6a001c0b441c0d181200f00b0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 276065530 1250 276064280 276064297
    0x306090106030c05070c0b030f0a090b0619120803090105060a120611041707030302010c0c030e190e0901140a14040f031430010302010f05031f0608071202 68
    0x15900030303464a48190010b0000d240318400f0800104405030100300015144001002c01d498003d680c2d03d08120b05850091000d0240080c06003445490b0020a400b0401503800c25403c850b21198080d107007002104140c1c1940c440103941e130401c4084402e0050100180d03104046000013440300c0e03a40e280c100407120016004400740e2802a610f964081110351f4001181500103150540c501a00c400386e007140311480c2e01d118034150344000014410154203006a1000041c6803c00c00c01c441c0460303401501d11200c4111141c0101c002d028280e1854030401d81d442d0003400004800410307820300c03215040c040c1441d0744460341800000703400301d41c41400d14400c812408940c00c1400481c0c2c0c0f6141d480c8940340c424000c0550801000302d04900b110100c0600034442264503040c0b040916441000c1c003408542c0095407411840103460040003d81d0700820418505c03002490525503070b540308000030001038440600d50001540040c030108803145c201c6002070203105161980610995681c6021081c0d1080801 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 276066780 1250 276065530 276065539
    0x15090c030a0506160504050904080a020f011512020607020405130302061f14010c023a0210050706090b070305040b0f010b0a0c080f030703140115020601030f020d05161a0306 76
    0x2820303504c2607400d800605851480c28500c0d20381c1c1e4000040d85540c003a45d0690701e001c1e00003200c40000381c0400c0144580380c220740083c020350002018510b0010342501c6040b2050a120008030115540e407400c550116500800410032410000500d4070b6100444004070058425500030a10741c254155071700c0040202201c048001c0c42c140301010241c0d021f254011414000c0002c4002c0c0142d440134010002d00602c52040c29140096000c41054200e4004401c41d0001c14144050090307241e21001030880c0c082e90074200d80d98810f51030118003c040a09016003440000e20030320481d03540c55000b2a0240b03000f43c40c90b00c0c894854000c241c035140c10a110b4022503403010401007101d5409000710f00151401072083c5410481e004034002c0c40f0394800c0f200080029a10b12000d0028240480e50034050080e12038000149228024080c0d51408103000c083d2114040b000c096085603182c00e44949203551280c160b805050203040c0c400d01c0700c0e8940c040c640408084443c0391414000150540e40304580003031 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 276068030 1250 276066780 276066793
    0x3050f180a03050705340f0803040b07020d0611071502180f06070f08040f060203181507050f06060913031403132f040915110c15090c030a05 62
    0x2501615558020a0202c8060149924044440d20101015002c0086440f1241c01e410440c850b01039914066801603074100081c900280702c2040000180d07022f4404503107140790b54560500000d5003d6614000007007455041c0485012181c2d0000054113100740706440c0c40e1002907910010000364040c0c0c407198040b40005c0065050b40d450440c10701e0650381c2010f02610701d00b8181d81c5135450050000002035036003000c0000d0401440102510440080076188086d50400c04610044080007a100e8551440f81100082c42a2400741a004031045194864212204030310240480c5465600460b80f151013113038200005010713400c81d080a8060550b242c0c3e00d441d11600c1c42c46000d4210b810141410001c40850070000b00051411540d1000c80161986450310403100c003024000100c8414200e68021820700487c2000920400504140c003040041e010a01c0b112101010540b4019075142e51058403c000040104444400c0d00500840b00c1000740c07519098160700b81aa074035504000101158840c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 276069280 1250 276068030 276068033
    0x6040e06040c03110a03020c0f070b040915050a0e0906070801290904090506010312020d201606090311060408120a030906091406100602060a15080105010603050f180a 73
    0x250b0160342100014240010700300c0c0001440c4045800c0030401e44003180c1c0c00105490350010400a0952148000c0c0042410324100003900880c1d015501c62104100c2c2c6603400130009035480903400c000340c9000350000710b0382d9603220352483d4601c00544075190b1501400000ca04050700c50204c40f07042c2c940c1d00031a4680c0144840ca040100c84189506030030600c414880c00e855a500c0d40103444206001da4002c3c505941142085000c6070b0b80c00130200c042d5400030990a440300d07007015a5099a4600400c542036030286803403654140b07800345c400002d4680800d1004101180c010030700e1000c1d070340220301e02c6d40d000f0320074400c0c091248624002d08800c1d80c040449000c0380c407825401441c2409542c80d01040042d1903a480c0802e43d4151042110074902c0e040390080e0241c02003250700c1c0d110704103e004002281c0b4141011351190700240c2444007203600d9003058404e0824917182c0307000400c8100c0003082a0360351804020003d10042e0f4003031000407820307408200b80700c1080011041a0170303040c02500e6500200d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 276070530 1250 276069280 276069289
    0xd0c0e011d1c140d020601060e10030903021e01020d0f110f0919060e090a20090303120f100b0f042306030406090b09010908091005090604080d0e06040e06 68
    0x2d5050741642e20103815000485811034210149800c02c014442000c00c184060f081403016080507040007070009411300c440e5a0340e1500b0140034401e0600164120341c07030908a05091000c010b080780703880b030441054006101540100346044401c50108203050b102c0d4103007801c1e9243d43c0c0c180c0141d00003c0c841c2000350340c0103000130030b900f90008000d00085c801140a007000020719512907004106880c00b045503d04150001c1a03112807140010031240030041e0060051703d01032070720820030900c0424508443d8404208403000404021000d0413146032171411000140340459581e0010102101d000451041c1e0340c02f0348008088580505040030700b41220340400361181e600800c8424a400c0300d1740c4082d141d1000840c020f0b80a03c50106012240b400c018000f04000f409000c06a85400030210100d241401a2500301c60100da208031401350f004412541030044c1c0c0382c0107034000d000290020f00c0310030010382d40100d004261075800740200d041080181c1c80c0524447c2501c20688140003d174540b81 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 276071780 1250 276070530 276070549
    0x1605130b1c031706010e03060f06120a0c1802030108060c0307020a120302030a06051c0b060409020a0f0602161815030813050a080c010203070201050c070b0d0c0e011d 73
    0x28090100c28007600701c1d5140001e8141090010703404105140d099030140111484655130004080c00c2980524200c18046980c8a13001817000f43d0f0300100e82c0215a8540c1d0340112010b140250004945080d40326007050500d41d4551b10841c00030800b03030a08034039050000d000f40d80c1222022006042030381e42c1c0c00d01000d0360750310040c20401140103114080c4001840e46e0b403c40d060b14600e0b1390040c0c50f80b070240404400c0b210180c0000c1e2181603100000b81c3d0140040c88a000c82d140e00c004604116251280420080c20030080c00a40c81042c4c42e00125074101400c2e4508200c1d0b01650864a0180c01103418250307202c0360b4040c0d01c9542d00596110034484941c1e800c0031320f50300c03040701c100c1c05029a2521441c0107500203d40f813950509510504020f0340c5480103403a00a04803204c084c00702c038862100007035500d1140c214000d05100300031035190340200060051800820740e000340c10790744425a0002200800002840c3c2e4081200c050021000b0351292115a101b5064203a1324100d28500380104640c0c0312 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 276073030 1250 276071780 276071801
    0x2030d0f05040b0336061302040f050a0207171201030201080c0c01060f0f05010809070608060d060c0c0210080402030a080d0f060f03030306050616060f060305010914160513 76
    0x800700300c001003001c202001144a000107684855034802c4403404030301398841c1c400c0f0402e00400080805c405006021421070f41001642c40f0700d0355171080c10b20104000c0d100c0303d040054400c0c81c240400400c1a0b0365002000c0151040d1304000f01da84198954100701d0140101268003141082e0051006502540883e6040035406043c030f42803012503807001c1c1c00c2d00d84c00d8110420703141d1940302c00c01c100811006510301500742420103200c5842d0009040c0d039181090300c1540b0421514101141c000d4071003000d841c1d203031a0002801d001070f81d035003040540b205024150881c058051040440300042c4a480102e0207203600501a29282c515601c0d400d255420039001c905a442e5140d66603081044e09200b18001050406100010507145090140854405a108600484080058180c19100c1c13645201d406940480001140c808070718141000341f00c943c00c01000e0f90b02e0009200140580c002440c0541c1004c0002c41b035801c88010348540100c0c604d48030b01a0800700400d500346840c80070b500001200d1 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 276074280 1250 276073030 276073037
    0x70c080703031d2a01050f090f01090e0a1e090f03080a02040503010e06010312031e090f0b010b07060501051c06050414070609060f021c1b080f120f0402030d0f 70
    0x2922818259400c00d00c1361280e003140c0c0390a40000340d080c2c0807206807001e0700035000d09150f8102660345002c440b07a0703c50801118407a030080314040d04281c1c02504000042c110f10b014580c1c1502e0004034000081c0601601070741041074112814651590b03902890301c065074800e070343d50030301140c1c1d80d42690441e00203001541c8064003403202003501c0e2001d11aa0707a40c0441500240040e52550070b0540c030000094805030100750405072a581d08400d10441e6405c640c902510000e030005280c101440152141040181032051070000000c491070036502802000d4010102007040c1c0c0d90320b104006050207110135903800c1c0384141c1540b0020501c0c95108cd81d00c030f8000e0590303149030200e000e43c0a007001120307000070000c1010303098184544c1c1d9218110402c940b01a00081c29440344580000c03640180842a400c10400c100b00d10039800700101c1e8189141c01d0340405103640b10b10880680300b1550b000b8030181021403a0803030001d191000e80303021160103540c018010786003051040e0012a0290011040302050 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 276075530 1250 276074280 276074321
    0xb100e0a02071101180e07090512061e13080d0203060315060123130b0a020610031a07120f020c0f0a0b04080901090b03090604030f051207031d0a0c03020405070c08070303 75
    0x1e1549001b40a44201501e5841c03560440c189001c10041c0445520454213940c070150800001000e000491400c1c500403002c0c082c1c0c50b0b030300c00202c121000a2820018880c8002044210076241c1c25000b444c002e290450584400301c01040050380000002c4403090300050740049030f0341d13440c10162081090107581c0e2800f14641101d46401000302444d5a0010400f10000905420002c0d410712000f904450140300607440145035890750b40500c1203501c4408201e828510105130b80314000c2801c501c040d251001c040c05400700d994100c00017500807803c54441c0b402011143c41c8410350210b6400301103a40024503601907142c5444052560304283c60490512801100200e40100c0540240d40f007a50940020721186c542450000c00903500340200c0703c103010090000400c089815010560300107154500094035000390514001400185a201b0300c1c9405403003503071814800c42c8900b50060b24025101801980c441501c100c0e24417000060250182d030742800b1010000344281c105607414100c1001c0c14a4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 276076780 1250 276075530 276075539
    0x10c0b0c0901181e080703170904020d0507090905161e020a021c1707020603060d020f060403060e15101505090915130209010c020d020307030b100e0a0207110118 71
    0x60440541c0c00c807044c41500c821a50164044404a0030050b001d0b050251228030b2030b5564000c010031035440c001054403408585000c0d0ba485982c1a200c0001290000784014201100007804820060007824038007401c03c00090300c02c00302000840400d10155554006610350306c010382413030040741e01c000e40450088010010160740e4909020514914407505101e181c0c2082c0740c10300340d00c0101010b03820351440078020300000da5140b00541e40e000720152034202400d100d92002403400226200c283e40e20180204e008403d1000c03030342c07000341010001c508885c0551103000c090140650204c40c500904d9480701000e00400c41036a0b001d2054283c00e088c100e08101103000091300155044490803407507401d100c041e131020300c0d101d640c0c0070a1003d03110045181100c440002801d4009244001e4010b405801034075003151400c000d64402560001254811030070040e40205404016120f50b0500c2d80e0f514000c40d000e4046842200c0001c2c0e400581c000542e200311005460f51030300802600003c1c0307040c920009 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 276078030 1250 276076780 276076817
    0xc12010e070f0306060e0d060608120703081503060c070809040c110c040b1e01050d0504050705090f0c030115020c130c031505060711030f100614010c0b0c0901 70
    0x501900d09541440640e103001400144080c1c1240320450070142030200030002d1075000030541c400c1440070381d0001c2d4552501d0800c0e10150507258818569403103a0b1449042e204528009015034038401e542d0b207907068075040d00196540e040d0b0202c0d26419080140810040390007030b402418400d200780760b060b0810300c607c4009002ca60400c2e1034403011445e1608681007040040c450006401030031a02002000c0240b000310b144201c00e108211840d4452a1840c0358584c002c4017560781d4200d500f00140090301d010b1810702d480300441c0c85058040c22300003012610104003080070b603105891543c0700781c2c12b580c40d00281e207503401c13802d000840c00d5004103c010307406904c2d44540402c0b80381d030000000c5110704010800a003180c881d810034075203502d88560140219520355044600741a00540341000325902203000908046180402040b01c1c400e02071540800e0280b41c210704100d900b410045942c02e40408015540d00540c51030040c00070313030010000f901c00e44100d0081c0030b96100615041907441c20356207104 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 276079136 1106 276078030 276078067
    0xe030c100c030e010603080c060106020a12050310080f2a011211120f0108100207020306070c17040303021011040e0a020f07020d0b09010f0605010905090c 68
    0xc0300740c0d2007504603810300b00116000300f003501c0d0b50303140c036550541c03041d03c641c444c40c000c0714000a10103001243c1c040045800400344248100c0903e030072940ca074402040345110004010000c21014400c001d100b094801450041c0345146100c00036107400590101d801001100003503d680f1140da0000b441c0000044100c030101e41f0403ca00b095441c64000d0850320401c0241e500100083c100324500810704965a0100b516035540030081d0341c6099100d02000030750558444000709a0003842558440c0c032481c01642c011306a9084a00c008100ba80964003d6005034070440580082a441e0310540c2040c0e4203000b0507910b094601800144154002401d090041e507020134001d44100102080301c2c10f45078000c240e40c82c01c0c0744500d04441e500703a064480b00802c1d0710b06aa80446040c030340c42400203646058448610041c84d000821589800052151202080074840c4005c011380c00c0c2d208 = true := by decide +kernel

theorem cover : BRFrame.Cov 275899280 276079136 := by
  have h0 := BRFrame.cov_init 275899280
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275899280 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 275899280 ≤ n) (h2 : n < 276079136) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
