-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4794
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:44:58.254442+00:00
-- url     : https://prove2.me/submissions/59423063-b995-433b-a340-3c3a9683498b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 862050359 ≤ n < 862230215 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 862051609 1250 862050359 862050361
    0x305061c0308070804020a1503020d050c07030903080a050708030c1e030603190519030f08242119020301140103030e061c0c0801140301050127060b030126070e 70
    0xd5441203200f56001840034201c00e508039140ca02e022606180c0c2c2309a140060360101b0f41141c20f01203401007981050031790036010b24100c0c044d02c00038040e0384d8500014120000020302003251034440c00c00c80390040e42100c0882d40368101445940b02c41d40c401e2984115441c64450515180301600003100d0240300024001c1141010420007602e96141d4408155054000c0c1c242090500810000c103a1120b4800c2c0e03152640da00f00c030711028184a0000e00207840700e1419180d0350050501001d10203251300d100701c405001148608400c0c10070000000003e008500500c00021a1003401d81d8800080318422402804070b20134003818000c1d581c909100c041d00141942080301d0141c2451001404140d00c0441f5030318629041c00715540583d1740d07503165000042c2d80074004001c0400d001152039032240e401c5000380b000f54941200401d00d2101c0701c0c43c80c100106003504d11444454558000d038010089869246d07202d6958080c40c01202605400c05440c1500d0301c88200d556180100c0c04a0580741e014110f0301807 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 862052859 1250 862051609 862051621
    0xf10090c02030d090602130b0901020d1218060c02150f0103060203060102030c0d0e100305091b03030405090406200c120d0902040e1c020d0210020a020a0f030305061c0308 75
    0x6011400c0c054400d6002c00c11603810385545078003039180c40502030321001d640c030346d284d903068503819445a1041c1040031003030041003d16030340407807030030303092032a500e401001105c0000003800108045040c5560b42d9215002010070000035030400213200005809488011000c9000c2111044049506000b02b0343c45400501c000754040d8040e40e0000c0040c81181d080c151101500382c038043d10340d501c10b0041203010318002003e1801075030451109529190030300c2103082012540c0c3e0b46484070b1560802c1c45000b0010440291000c0090320300904d001480160a4242800d15000a00e44039585002088641c010103900e4000344046414804061006000e41c21150b101e00b40a5004150719232001502d801040780035075a80e00581040024645c05004a1080c044a084482d01030844d00810341d044110312452054000c14244000f458408025907112103041c400c1b401c000d4420700040c51091402c0c2500140741d85548480e110360410384e00c2c2684120840000c401e51441040020300080c1e8650010710 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 862054109 1250 862052859 862052861
    0xc0803090f040f110c0102030f070f020a02010c02150d02030a0e030a0f030c0c1a0603161508060d052a01030b1c0501091202010b0901120b0f1905010312080f1009 71
    0xc103100200382d00080003401001c138820781d035000c142080c20300c0c0e4020041c0b115030441815030396082074080c2400c4070840d00303c0c0c1029444203e07180c4041e05100c92014004199142d03000d00c40855005c54003000c2ea980c90042c0208002d410503a000c4054074500803400300803440c00000c580030070340662154a404a40240220701401d03e104030351041003503016500001824458041c0720480311014546a90300e460f0040c5803034050060f914400c8002c6003082009440f0b203113848003c0000540c03901445645d52031000c1400c1e007140460082c06885030748250140b81004d2501083c00a21040a60501500b40001102980d000041d07050303000340300718411807083c07000d82115401284203000101e1a1012902c039000c5002c24103600c5405071b5124071020b105071038150403290140070610b51312403100301d998640914580d8002c1c010040d490300c84000c204840c0c20903c40d0701004924003414089987c4920b41800780308414200c19000c5608640801c08883c03500b10b00521aa1051710f00030806071034004124 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 862055359 1250 862054109 862054121
    0xf0a0b13030804030602030103020f040614040f0e03070c0e010609080c04050402130c09170a0c1e09060b28021f06050604030b061f0f03020304210c0c0803090f04 71
    0x415041112400030009038500d0107403000314045d41005840358514018002040011502e1900c51840d04a090040c10040410001544c00688001410591064241005144039000c101003403201003101010000040e044001f540c001045e07a910f1642d03102c00c181c1c0ca0356110f0082101c0c680084a50b0540c034102a404103a0050000b803050140c0c002c04a8480100c2e2040218003000610f000d4051103401042403400b00c6800c0498010501f01045480c1e030202c4140a010700840071407150745042880c000c1a0f15600607016808ac00c000096544d0348403e5254000190245c409414016000407103004004480c58003209030040c0ca00821011905031401c022001d10640141d80e6000100c4d198072248080c00195204150f514090300300340d020842c12110903040071644011072004912030660011f22514503800303a084c0940c80b034a41e440d0900c0c401a03c2880f21503412440780b035201960340d01990070704100b03000f20404c5213490344075900c0644070b200f14004070740c0201495040c503920341840ea12038 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 862056609 1250 862055359 862055377
    0x109030e03161203170a06061404030c0308030c0906030703060501021501031a06240d0b1c0f02060d020a120c181a090901031203050c03040b0109090213050a15050f0a0b 74
    0xb404150030350b9165005c41403040c0d40e0345485595801c400d122444e00081c3d581030203e940b400d00c40c00d051555139195807035440c1e40001040f00402102103540395a040741a2480030200604098807440e08c0800180140068400c1360700521070910400640b400c1e0840b80d034107903504074a040c59100e56400316128202c4d00030344010b801a0034102c0070300880440c061880740f01b03a1004401907032941c622039100e0545010407a210300c1014007841c1400c5050790791040d000d1f07055014101d1242410b4a0000800764040c003810700c0c6159000189602844c0d6004200000544c060b00003000005141542141c4a00e11414400142401300e0f800f8401c25480942c0100d131908810901490320507828040b0b44400c500381c5c4102c40700390b000034001100c1601406600e038010401c117601420b600d8192100c135620302d41032003a00841c1e035a80245405540f07800c107420144060103003013400306003400e03170203500106040b2002c5c02000001d203401091501d03004414003280400184440030950404a0b410b6990b8048401 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 862057859 1250 862056609 862056617
    0xa0b011806050a0e0a06020a0308010801020a0e12010e01050406062c0105061b0d05070b2202041d01090308091b060d0203061c080a0e0906011d01050702060c0109030e03161203 77
    0xc1c00c440307503503480c0005e000f41400d640600130081c86880c0241c416041a00b183d905a40180285071090340d110a240d400c12404a4056549111a02c1940d004244580d0380308001d509203000c103c28400c0c2600006d04448003401c02510710344028005402c01080007440180c1d110110004000300e10303060f0017621b010402c2d0100621030012820000e8984803140c240d11010480105403981800541c034007446d400708a440051000305146a2514804031400600a104a41e5040540030203044080cd519035020078400030030024400f070030f02502e2600d08480007000347c442c8900050108120400005c1c08035030252036030782000307403245110700a900300502460304160340601501042d2100328140708924001c5001b140d41c0c49006200030004001004041d003e50b41c7e20040c000f990b41d101003000c0c22086014108044600b0020049820348252400a9402000801c2102c400c220641c0a001c0300d5111352102c5440110140038551605044061030340441034070582000707a00c540c8a11031282c44e100b450 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 862059109 1250 862057859 862057877
    0x20414030f060c1e070b06031c020a08030a0603141e07050d0206090f0303180a050d030c0605040c23030f070e01150c1509170c1f0e0102120a0b011806050a 68
    0x1080351401c5d00f05020a030f604140c2e040901c040780c1414490880000c280701280601d40482082c080d68a50b80458002d08842c400070004218120592001014683c4a0b4114030010805142142c0d20322407000d000a100c1c0a07182403840d400000240c1b041158000341c0659507141c1c4940070001c4640181544a1700503e0101031004559070500042102618820b07081d184111324a0a2100186d45078103d64003031b6120320482e2000c01d401007a210006c690008003c5101da035107103040106070030664080c007a1301c001952140b02da28680307510105861016011920141d07100c28903180d603003c40780303c1c0c51414200c40700140705104007412001404c0d04a82085142d4030925600c14481001e00900000071345d5030343e20004c0030400400c0d160000030103101003d40c145100010340680740d200c00030080d04251201d1000380c1c0d011210380c010240905089000b152180a410610743c0c55003011070b00d0800e0700740303803a01c490700960044000e00c8112816030b86200103941003580654032903001200f05070502031902 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 862060359 1250 862059109 862059157
    0x3010f17280c0518040809240903011b0509010f1b0303060504290f01020115080703050f0a0c0306110d06090204080d0c0b0a0504030909050103030201020414030f060c 73
    0x608100c49414041e209001403080d0a00d4038808003a9040360340304109015514001c90805400d00e50450b41000120707903512000350001e91136103141c0600300003601e9800c0c81402d11654101c050b0a104105a000b8440d0784114501c02c0c60360240200b101c000b2503024040382c566544608a68050070000c0d0820a804403908041a0441486841c04400107611507805120b1270409001d05c030028401106461080c145d80c44031a40000256450740b40540d080902d6000560b2003500300d0310b00f0044c8800c10f80d00898441c07500d59160f051502083c1d43c04e1003041503000c24204001118284d1680099004c62814115525800a42408200017801d048184000d800c254442c0c031a043c0104102c9100513038552400d141a401c204001d42c0c1c8000340073342c80d00c4c401c02048800402c65480900090005019540c034a01a20300c80015003205024901e00350000c000c2540550007003059404c0091000300703003039074401050744d680220a40d8000c143c0080340800c6d0500c01e20000f62001d02c0f80f036140007503070050b03136 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 862061609 1250 862060359 862060393
    0xc0b0c0d09360513120203070302060606030a0204090504050f150411010827010b011812140a080d090302060105060403021806030c030307060f0606080c03010308340209090303010f17 80
    0x242c070309841440520f9204e004105840c51106070718041d600196007040320035107010f51200c10040c4400e01031040000011040f62541c0d0460b4042c0c80c815004000c2c604281c01c00c00d990301148180704845100c0c00a00030581266a540340c1d208640c03000c128105944a0070044886480190406c8003041c1c040710449202c25000c010354104240744d000025002c07407070000052610302c00b490744414110b512a4144001610b006281c080183c101400f01042c003440c0304c12903d8410900009400c19001003661031040341a5003000346000d02075404c4a400d41d89600401207948151701c8000e500c29540d800502c5649a0b242003141d101c6402420745540740c041e000031034203591180c041201e8041e540d0486100e19852841182d0242c081490118001c3c5006c82c0c01f03a00d98072041c040504642c5010400c00314040003410b04036210021100b500e07040c180900200c050204601c04201c1c420300303191000820603c070010a5034125400c420030100c0a914004006510814808420702940110240e901110000d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 862062859 1250 862061609 862061611
    0x6041b14130b0702190f03020d020613180b03030405090402130e06010b07050f0c060a081b0409020309100b0907030902060d24120507060f03090c0b0c0d093605 70
    0x80c4224030b42d503802c1c2500c1000300000d84083d400c509012240e4060060701e64090703403002980d234142c811040304c4880380009400c90042e2450284205c41021011805100c0800c5401508042c480f041c024000310b10105a00d0340a640642d43d004459040002c02521f0600c10784c02004090880c00100c02c40c078058103d0401009070064813400b100013480c0c0040000801940800556080150407020701c2040021190300c00c00c01c16a0410200f1000f040c90401a0071a03804080c44100e0060358a40c6c0c1ca402d100069002201d80c0700d418041c620000c40304c0415401202d0000c180280101c9032540c500744260b0060803041c00683e0800c400344450102c40850707210341c100b846a2092000c689440c0c0c110741030851943c3da040001001d03465180040050b20001d1751505455060400796010000968124000c2c056103402500da24102c0030300042c030080078401020040d5814050726181d0301c0343e96055402400c90305c118610383d1036525111581510400b03000e000041001d184100b10042c1c8602c0c00180c0318 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 862064109 1250 862062859 862062869
    0x40c0201020a090e090a0b07090f03031e020c01120c03142502030415210c0f18031e140303150a09060b0a0309050106080102120a0506041b1413 63
    0x26001861800b0190800003600c01400100034020541c50048005500e981800324010704440719140070681c010b00030b20540001d098105038a007280740c1d413410024064040155403114000135002e88000c41031000c10501e04802060b141d0751440008a143c00005001944049003015500d10042601200c2808030a008403404e4072844204030780548009000d0b6017640404040d98820001003101940c1001c16424181c6603081c42003c1841225105e0070094441c50200402c81c078168400c0320007900011812002c052650b20800400c41840500401145601002c2d00806403045600b240d030030386d5140a211544102d02e420150b803a2502e0003407454200b03541c0440140c003901840700a5052900000c00200680c3c80e040c003605180034041d42e81445a1859042090b484203100002d0202c03d4110390300510a600c000c40d980d0a00d101e00284441d02610741c00a0207081201050ba14138050051920089500d4580c0d00311081ca12070070740f406041c040d00b18080309014002c500d00b802508200c040100 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 862065359 1250 862064109 862064111
    0xc030c05090d0201020127110d0b041e1406190203010501050418060e19050a05060d120e0303032a12160908192913080f03070c03110601140103050a0209040c0201 71
    0x13000c522346280f01000d00c80007580101d00090240f0b0105000e841400d4116420100842200061158101d101c185108c0c016000b41d40c0341c1815000304400281c1030748500d020510784a91040f5824040c03040c3d1000380304a90001e0021710040c01000000d111090b0419400302d000100959039400710002e5010495440d01e22102e451001d000e081c1c664000e407540040c821300c04026900d400c500103000c5400d0210080c18a003119031409000900a403000a84640014100c942b00e241c103912110594100144e28200b2201c650556000c091590701510041d5900c100c500c22983d85040d025010b080c90250301c841007151207400003d0410051100d044160741e000c8550000c5e42490810008000d401000c5508a22414a4542c1e0700070a40940c43d410040303410890701c1644603810b003810a030003100340326041d4507400014045070541200d8687c50192094a41102d0486a00c981984038242442001c07181d408504546046602c02e6105640c04110034100504041e0314001107000c5612082c105400350b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 862066609 1250 862065359 862065431
    0x30619032418050f0f0313090506063c030405070e190603150b0d0209010536011d101202120d0206061315121e11040c030c05090d02010201 61
    0x15110a01c20599016100c50045281c071016190716030038900c47e4802c0d406036542e298089201d03580e8450848420f850706280480d0134a4190082040074020009601c20301d048100b9003100030071092040d0b070b03c101c0d0010050550f16241940c10003100070001c08000b10154034803040149074010340b00f000040c6000710f100c110007030001d90700ea00446d068812001c1c40744000c4c5960200507904c81e0b0220341543d00542d20355a000e000103040c0607d5a4913500714002d00c203054041c041c00c0d001c082010504865400c10110008480c904100c0c035842c6c3e080d248a481844400d00520803007c107182d01c0d078080b0341302130f01c1a5a91025542e83c0c6040400032620040180c00c14002e000311840d0000040307440c000c1c0040c0800441d01c80104400b54160302e480b480d0300c18040e032044d12041c03000c600c5050b003040c81d01086c0403101d41101c0c50100b031161f0040441714401c40c41d01e440c144040380b01b485209000301c400c5c0c03141d41c6405041130400203072241c40c40303003281103648500f1200c54149100700140e003002d090502d2580b030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 862067859 1250 862066609 862066633
    0x91b070b011e08301b060f070c1103070b2a0c030d0309150c0504030525120204061503020a0905330d1103061903241805 53
    0x41e010b0307000d0010302c0c210291080c0440040890380c0070b0300b0085142e04c0309002400354540d5000d11400b0480410038036010070f903010080158040d061003c203004040ea031165a0b10180460303074000030381d402e00003d0054140100019904a10302200f42c000400719050103546250440490b0700c20441690820544070810250b9080d0300d95032504c85c00c1038000b4140d40702d40100881c8c1e45907150013003041010b031100e12480c144401083c42c003440060440f81803000c1520100b000c0c01640c000c0c80200c0b414400d6403840d007822079020401003880b0228801d408016880d001c9801680c60041400384d80c0513640300300010750005c0809500004440c2501c0140e16004560001b41100c141548084d004102482c1994940c520060600c80120f000c084600b02150455041e001d540c010030f09980745a5280c54020f01d070184000d8061032042c0400c9a100f41206000191078504041900c8000c042c031144910304083c001032a14080b848142182c4005100e65400c040e0048001104409403081c2d00600d060941c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 862069109 1250 862067859 862067879
    0x30115060f0f020325020d030c030f03050c0313021c03030c0e0301020f040911040b040f0509090a1716020411130e13080f040e070306090b100c02091b070b01 69
    0x40309200c50b042481c0c20b058080300c040e407244100c90b0085400b00c1d0b8031340e02400f6440034141740901190081c0c251411009145400f030603142030802e090300420390150044c90300345d109000c0e1038232500a840619044d5107490808500e5400c1108080f07030710401002e20043c024031621a03108100e40a6036020071320f0034188074082c000e0034082c00d0783c5000e80d00400c42c1b801c1400142c01140d041325103c1c000040e08645c2c02807407080c2809243c006d0905041c001500083c5580c080c20484107035070f4201c4060b441078485a2003e9982c25010320000c0001403000d01d01201c001c002c2024040d802c19101d00d030f9020803030390b6000a04961120075110b03c003003c007107888052403c80c031801034042d1040d1610410a030500c0002c1103c80200014024100711780014800d0380302000e1019980141104520400b4609006602602815a60140814262409580b1005031030107103c0060404040d884460044110b6001d00c0031040c402800501460001525000001c038030030010641c1078000c040031841035042003401c407 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 862070359 1250 862069109 862069127
    0x1050a08030f03130311070602030a180305060a1a041404110118120213020d0b01230a03050c07050312090d09050109090c2a0203010f0c1e0c0203011506 67
    0x200294414000070341982e0007503080740d800090260703044d041c1801503c0c0403070301c21407400301c902d41500440c0d100043d030315000000340c0028509a100c1514002415003000b555203018403002d402a400b460216003c2c91103076111440125a110720303081c81c0e643e102d02050554030048010490001c10340708000520803440b85442c18818246045e1842c8000d0b000c070f070300340d058081c01541c28a4020041070f00440d600c100c114144040ca043c800c1d51507100001c0c0b02e400130295038901501059807501d4600800400c13490607402c001a89224605107502c2c918208c000f05001082200040000c0007180c001c10000c00c0030303140d0700203280480401440d00394503003401c0296a0784100140940580e0034000c1c3c1c0e80299144042d1851080c0011301e03000c100c038046030000a281015883d406075140418958282d603540d0b428118000e4000703009642c40301c030048048507401d101a8000541c80035881028028030401900400c54a15101060110540000e42100e1a500c646202219410303802c0005a420403081 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 862071609 1250 862070359 862070369
    0x313030e0d121101110304050303061201090501140414070f1811030103051e010606080c0304020f091501021b0d030e0102120f090a080628150e0702060903070c05010509010e0d060501050a 82
    0x103501b0f5007040d503a03040ea28000038260300c0c4180b06034020900c401009500c500406c54001000b84004070407001d000030001c0090b241604d401c1035034620000785100c001070750002c60b03044020307142c6620b15150203e081070000c0e44000b14080e44525249000c140008051800707180200042d05140b82c0c00d0381c158100c0b00d00070165410917410110100072542c0c00a0500d0742c05501e815140e6500d949e98400503422855080b100c9601032038031014005c3c003500000140d0b02c030b550280c08548220401c040c2101102d080303407650781d0b4040050ba03a40f40001e4800c2c00003142106040c011102c080c0702da400c1541c42d0360096103a1800d24540401c1403051881c11824100c0108100310140005060040806006a94003803480f00342c1e824081144040c941745a0160542d00c440003141c45086840d0201c84080319429958500140b0510021841000d001f00c12035032040c2d4000b90603c5003a2a120040d00e942c1c100d101010306201040c04c142d105d40e290a40044803013845540c00080641c141010400150303501c1e004 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 862072859 1250 862071609 862071641
    0x902010804231b10110304090b040e0f100e01060e2e0e040507060c1a04020f0301020f031014060d0c02010f0c120507020601060c08030a090203012306060313030e0d121101 75
    0x445d00c441c140401210181d400e0024086903881440300030401801e010140306140b845a500b442450120118103803d0747d0344001c40611200081390380c2142660140c0c01750092007040000071440781c4c110341d0351850301541000042c03100c0c000301c03702006403282c06600410a29000310100420000c0c1444450301406640c240380c0d00b0000c040d21040390001c841d0590360700164247e00442c01b55610300d0307186400341e20300400a56840400160700a0940c1080d074283c240440d40c0800032911400d201540695850040c008505101e803003583c003c0502100c4902e48295542c402c6149201c0d2640c0c003800416184a4032400b86c0c0c4030b070b1000d100b0101c40005207010300315007112005000360b90740b0400e003820041d00802c5141d200d88510b41104014459214002c0d4507610780f01404400a03c00c0b070100e00f44403040f0140101d256283c00a000807844200d4881501d0040543c04800081c000d04040a0781d0002509521004069035200f04e42c1d2400c0200e4040030800120900000d8842401606241702060807 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 862074109 1250 862072859 862072877
    0x361119030b0f0f0105061c180b130b0609040305040305071203122f04090504061b030608280f03030f0b06090d060b010c0b0c090111010902010804231b10 67
    0x30703e03002400601420f48034110000e2444800d10a0090490b00c0c1c0702103103410820141200b040c0312900c032107640c08803040d10508000900d111010314245030b1180d0409001c000680d103c1e01040000c1c04007d1044040c0841400040007090040214030060241c0441c55100d007140c504003d0000070f22404c5890130942040250614280c000910f01848280c0011400e40340001d09a020458002d6070801d01030342c3e10702402c00c0705000564001d48202014000c001c04081c8006404606461880c01501d00c00e0b40034143c00c019282440c080f1000070f482540b446060720415544223503001480c482c0540001e40c823003012164044c140e1081d1002040b084454900c1d140196010604601003407001814980d500c040c40042640948030a60041c1d81c01000490030340740c0360900381c21310b801c5000038030f000800c514107488084805106004030903070140c480042980c1c403551341e0702d0640030341c07200204002d50f403280c040c406000400100d00703044850020415141a400180026500610800307400c11511207 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 862075359 1250 862074109 862074121
    0x12070f170d05160c17070506090601090b0a0b07020112090f03020c0120060c1312080418050f0a09020609060a171320030c10080901361119030b0f 64
    0x29584d004c4070b80c001c0c20b190007442030781c0b900e16850040d060007a1603030041c0004c1094840c80424100d0581e0f02d01c280030446a01c56100780402010030b030103a4500203000f0801d100c095030084042d03400781c607003c1c2008145c41107035a66200d14454007040460140e80991440c2015613000ac02c031100400c9000207500c4189072000215a0b14000a80820001000080c51800d41501e20b00901c010704155144000800f50b40d1900500d02d074041e11451103200560081090041034502030399000740070070204a1040d0325034042041c020428644101da0140040240c90350a07159003000d040700c015151a811915005c41504003800e0600800120040c406802280d00045503801c2200e4440010140443d011440b078000c20300c1c0c45212104a640b05100307207000d10002d980030008500c21300e0940001c1c0094110110700200c0c07481b01b2a0780c2507012807694a00354138a151881d44414041c040c4030741000f815201408228000502214151000e050038400d105014080301001e810020085500303450b8070f40700c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 862076609 1250 862075359 862075367
    0x30b0a090c0f0c051c1806050f09061c2d06030308160207030b010b0a030b0a030c150e040204240e01020c09090c1905030f01020403020312070f170d0516 67
    0x415900060024444070301e010302c40304105d1551041802006508031612410000e81500d21032104481e0080281d0000700d1618443c50603907001c0c09041391090b040503808001c100e4503412039011b00c6034920307083c4e403004d2600c1c510b0702410008240102e085440490200184508a14621445541c280c140401000040c1d072028025a0001b00505c502c0003c04a084040703080600303917440a806030040400110b80c52030007000038440100a80c804006101a210521200307003a1844054900a03000c4010004680340d5200f1307144140345882e0a1180e01c2d60400003c2c12078200f60041410b1900c1410102100051200c0100444040e400e013105d0310f1500c0d800003596070760f4008000e400340e901e0350041104000c08021070554040010048000320b0102c0e01500020310407031103071910030301c80c0041e84660321606100300e4054076006009023080d0712a00e004010f5560001d10b04403030320409500b141002c200065074400c2d1004041c1070b01991806142c413400151072001e05991801c00300340c44003128550300 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 862077859 1250 862076609 862076627
    0x114030c06070804033e0a0e04020906010f020c120a050c0d0c0b28020a03020106050a06050f031510050406080609090d0e0301022208160303171306060303030b0a090c 73
    0x3c01900c4900e102003495420030304628104600110580150000c1500c0d0122408040781b0402a203860319182da9481c4400014041580d0107500000700e0380100c1c0d4603501c13501d4910340c4a24607004842901141c00c02003200365203810104c0b950b5400400480040210030311039244410b80864000303502c450144c03039507032000815208000d002c0d02c0c00140b102903402805003201640592058402440b81c0b03012010351140040041140154600780c40418103180028504c020b0391640d65509041c00305098403d00340c1d0f400038040c80c210358804041540e00d69140030301c0c2c400e000c0f90356823420b4940745000d80140686074050003c80c455912001080081080021308900600303492404984901426001c240203119442103541000140e441c42c04684000042c108101c0701d0b03c0d4100e0301c44269141e083e07080e0082c20301000b0001041e080010004100d40c078417150b0000d052201c0a2a1860590307594000c450b80381d13000710301094440340200914035020302d10310028400a5002d2000c12014113004000c291 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 862079109 1250 862077859 862077863
    0x2060117070e0c16020405041b0e01080c06091504060c0b070801060e1917010605090a02070519050712030f030516090b160c060818010e0604030c0302010e060114030c0607080403 78
    0x140400c40d42203a4a0280840b8415034010300100914100740c1887c03008051003c0190720200309c0340780300250303440d50690000c1c101c807081d001400300303200f45e0002c0119590141001c0c560025402a40103d051210f000920041070303184c60395003020229250007440762000600c0da006001407140104a840c7e000000c510343c10104540d1170308168162491011b8041842c1c11102d40c0030808101101650700550089083d904200c42140071540d603980604103034821500000c0494000fa8000101c0c03014400d03184014a2180007a0791001343c8400c06080d02200c00d80d81a400141c03ca100104001d41610419400100a12038050083d01d154009071941d0003601c15000c850340d000611912103002004101c107003990104d140800d0581c0c03600001d0208005a07050415244008001c04c0600e005100b800300358600000503040750b6541c0d807016503528070545410340565490b04407e010003c03042c0500ca010f0080700c02082d140c14a20400d0602d000303002408907006940c10014180400c08101c1a103003142e03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 862080359 1250 862079109 862079131
    0x601052d0a080f280f02121609050d020d02040504030c17091804030c080c0f0f062e0b0a0c0209040b09100c120b010302090303030109240501050a030c021c02060117070e 74
    0x1c1c1c401c20712400203104003803007d0400403044046c4a0808003107a4246d60001070795a541803502d0700d80c8100040d9514000000754010b860248580c0103040a4000c40c0c0d205010742030500e10302909864010281501c01d14004040c0c1000803840c0b02481c102c3c00e1120801c200b5038003032201e8602554007425007072581c88082c0c24000007065049400d9010400c1504c401785090130b8500c0c40a5000482e5510001a20001095501050002018070702c001c1400f01442e007005000e9000d51610310001c003aa40440c1c0407104000443c00603c0268440c0c1150700d001c0c500c240c440d02d1061416000c00c90900010b0051042e24508003001000074640c0f00c0700101c0001c048000010f9140c0d90000180c1c000d11480090703039003600012000241035401d0b03900501c03401d08100901d091301c002d50b1140000020841c09001e020403000e00c4011030b400d21950000c6001d40481c01220481c6d2005180e80c0d0110032810890310041e07000c01d00622400c4000c07110000c070358642d413009010203800d0420f03403141148020850740480b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 862081609 1250 862080359 862080371
    0x204090507120c140102030f1902150f1605030610140912030310090603021005090a050a080c19031a09210406170601052d0a080f28 58
    0x80441800140c1c010a0003a240d01c040392881e00c2e01c9071001602e440b519007410100351029035954004000c51b107800c1e81040145252205640011840640c14050101140701d2711000140885040100f80d0041000102e5500c1602e4170b0700e0180c0304417208074002e100b00003040c002c3c482d45885d415559010005c9900b00141c00204256a0031640c2c01003281150703201800e10301600c90342c80040021402842074110300100c143c3c03980007030701c00d6846a110094016003002804101544580003070300303101200505880c0840e076100005512203001e604107140e250420f20700c41c1e606182152808611a22024003607014a103180c507150f079014071800c8201c1c02002080c00260301c0440610a24804071224104032480c1d1202206200013034016000780c00101d0b1050f183c071021988081b545034130a4105945480c640304c040d9000c1091902200c0b004112100700604401400010744007800f5144400d5071120304d00d15124810510801c80030b40068402207a04620786c03c5110400b14200308445980404281 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 862082859 1250 862081609 862081613
    0x712090506093a03180302011709010f0603051b0405010509180a0602031609060c0b070f0e090405100b1f030b0f030a12020609010209030604290106030e1005060607020409 75
    0x103d0720703606244810400e0905400c003028080d00e1401601e02d4000c1c4e4407084035240c1d003000c1440381a42c500010b40425020018640f84060445205600ca0709613000880c045052500080a542d11500111240e40000da441512070103c2c00200a42081c11038060041e9490840403d010113000b134044410780030016000040c0410030410201602d44c0048210760b203107004400c0d884241e8409400380c001840c04000000c10610030703141c048005030069101c2c456920340c030360281d80c8900c010400405000202803a2160340e0345c0c0d124014400c1d40510082c04807031015003103000803911003040880c4105800316060700385030002c891007804004503007000156292400300103400303072201865159040c42950b400c0810410706080360714811682da0211060340d12106005401d07030142181090301580b00400041c04070390407808110900044403401509803a00100740792216000740c00c8407001c40d444424560740400e04110040c020049000c08100d142403600004005115514001c0c0c4030700d40f10702030802 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 862084109 1250 862082859 862082899
    0x1506090b042d0b060c0f010506060705060609061f020106050906030a05070b0906091201140708011203200601060908150708070818010507020c030c09090304051017040602071209050609 81
    0x48042c00c01070040ea19182400c0e9040c6da0703031035081030b07201d020750801021131400d007005001e0b1040d81d5880009818540d072403004dc051503690051110340e1082484806c1181c0f5081041c10743c0c035020455001244030f42c04d0005202e028040940f05030b00961008101d4000321300003090f14029540301400e510b0303031424282c0c0010346500072800865401002c1488140312040150701c107600b003840401d820401950303a10b1043d184901e00340b29a50000144608000010f480390460300401c42ea9800f01240c01e40b0040d10b01844c00000740c0001010071041030052042800c100003050b8500a804000c0301c40b45000a0005c14110340038144006000c121400715000c400b1503440380c4443c950040081040d0310341402d00039900c0702c1380c0c00c0580c024001d034082103d446c24071140d410300c6030540100640c41c09240030180080c00341c0035184002048002d1503001e00000518034a0b03800742d400340d180541c1f1a040380c10140e45114202e800b2801784040041c0c04c00481d240d038802d030352551b00111003000c086031904040038 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 862085359 1250 862084109 862084121
    0x102010e03211003021e0907170a090501140f010f230405040206280e030303040b010501080c0d06031a0a050601090302060a0306030c0e040605010b070f02100c1506090b042d 76
    0xe60095101504464207810b41624240e06e1900310351000c0385840e09441030342c101140700828400641c821000803420700300d94000c840850301c42e0000003512852007090100b1003605642002a2581400c0100842a480c186510141900140400508003102e04188280307135840a070740d0290b51030707000003025580d0700415110740c12000074a201290710026403c09130482c1d115090740118001241000342030170004181ca00c25079000da200e100300c1c0d091400540d66104020700307806812004003e01074005003540600802184034020ba01c80e420404111500d6000d802000c2c5480c003803030141040319980c0e1101d452000c0700e8041d5485a911048480c08402030001d0340c10141030480d007440009a200303041001c06102e030b0701400d420484e698a841c90310800c0d01c151080034100c0b0302c030a80030314003600d00703607074494600c082600b06500c050303003a030ba104c4030003040c0c0c1011413325a694200811002000d80140d50502104440c20811086041c1101c1c1c0080410f071210501e481180750311a03400c00c00d40d4400 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 862086609 1250 862085359 862085363
    0x1602030d0902220e0715021207081e180d0b130305041706010326181f0503040c052205220f053009010306030618020102010e03211003 59
    0x10300380c2d120f01c1d1403c0003604019007481d0f1507100301030000032644001d90394014010320a0303002e484403160f0303010184590381010f00c05440b01036080106208900c808060701180001d05452146c65117800d450a2003e650601403c5014114040109000074155244141d210200030048103580e001c9040444086c007842d0000703100d081e810010009001400a0307c0c504a9100701d8042c14100b807a142e030001c0c045000304929190b00c00074041001704281d400c202e00790202004e0300e403e07a4850145215070009106a0030000421000401c6c4020700c6103407000c2101404041e26509401424071a5030b0044461142506003215a01c1012941c4100b6025610b2041144400700c841540064240740240c0042800d084429200d03c1d01c1003810286481d40307150f00385104103000143d1201c1e81003500d403541e218080c0107040660f100c0011000902500c160050204802403d44620b801e83c800a400c6a9015540b91100c0c0d105010061400b0b5001040003442d1101e03551000254941d51062001c02d4626000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 862087859 1250 862086609 862086649
    0x50f01150e060402040621020708070c0320010509040f0615050307020d020609031b01020c0604060f20090d240c03050109181b0f080d081602030d0902 66
    0x8030500402000e04140c0307040c2015611251180d0040000302e01c520b00c65000403509070825408034040300c582d1740105555040d00503140c404035503038003da2540140c804881c280c107040404d00a12000c0082a40e4002030101e518030201400ca002070190b02900916600c03d90b22900348550f0380708507410a40080130b003c281c0400300c0a512202902d19007007266010018171541d150390640300d100080c8180030f07503003c002451400e03007143c000703054452402807480c400350740800c580604003000304811171141d4014500080e940c90b00d2210802500e01541140000141f1503000c640c866004004950090388125000701c600002d624200c4c1103071100c01d41405c0240240810041301755642d800c80e04203102e07650340801c070a03a268110642244c0da040d010b40f013910300510385003001402503901955650941401700a440d03030b4803004c06000c0915a000150141c115a039448042d6403c0034405403c007500884500030507100c008025501c1c01082011a4a84d8542c0c40290554031003207a901c5800c4070802c1 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 862089109 1250 862087859 862087871
    0x10504062a0f080c0f0c011a10211503080901030c2609250320220b0402030a0b030609120d02090301180c0602060a091101050304050f01 60
    0x61880040c00c0d50302503a02880340018807a00c1801401010245801558403070a6248031084001c030b420902c01004440d03081c0e4200850802c00c81c040010b09a440305200001ca0b149131207515801c0502d4603a4030746400781102c40750a4501c990401e110003204100490034104000a10f0294000340449108030401c40d4000f810100c00d1203110b81c024068a0070a0301d05001080841208940d584550014820381a076002000004000d1441030340e50012109822205c0003036a07514005480381e0402046101b11401c68020801c021a00243d1039240716050700c01c1712040d400d01c0205203010403452002d5044100136003003950b40d0741a640101c1e5482d0026204640b20715003240c04070010816500c035144248501c0d000034030b80250010398100184070500d00c042c107007005050385200bc1d401007190a50305540b01d06034103005003200c015585200d400751001c0d0a00e6807500344083d0400344050a01c0c2c81090400c01c0b00d40100d030a26000028072103080c43d0095480e99142451800e02050403201c030155400c00d1 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 862090359 1250 862089109 862089113
    0x9060a09020a1206080a08030c09010e03010c020d09170d0f230d0e0c0102120a110a0507061103040f050105070f0c35070e0603070e0a0516021f1d010504 67
    0x74440d043c0030000150811500e915541d80ca039503580c3c500741c01080548200000744c190703001036024020508041c1805c071602810f04001a081d100c0750036850005a008050040c5655840480c00c0b00a180c1e0507040c14082e42d003100b6242d04d98110703103c907070b0501c0b29004008252511800640d68400940e441022000051040700300080c0d00103001545000e04011200c94400381c082000108148141c008152604038610113018a030011184442801a147c00c6400407442c113100c5603461a02c01d01c00380031064200036000d00150200d62440045600030b10040c05015000303250704003998801d08201d038842701e02c1e280c400003104c03110900802e00c1c0000b9a00003400311401e01010104040c3c03e01501c030301034041d072402c4034904048000e8009a0b00c1424208202112134205903004000981900c0086d9210803554070411420b880e07402c1c615030b9440c204220b51000d40e6444d1000c0e41644094803020384d00c080e0b41120322204054240106554588034200c44c2c1c0c81041c0b032001d41d03003458024001480c243c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 862091609 1250 862090359 862090367
    0xa0507080604020f060309060103020108090c0a030f1a040809240d0e010f0c050d0510080a051b1206041103010e0a05060402040b010e0a0b071506030b090d02160509060a09020a 77
    0x1070741c0c03c0b4091035019660b480d20b407402d002602d210b84d00329401031403540c4c84c6800440e840f10300507114890602410803403040c60344402d0751010141d8000c184403035421240b40360003404075500164903500c55641c1e00900001410010840d4080e0004a403419000e544500c504401c00811241c240004000010039402c615031039048001c407003052100030040c030810711544509655100d200d001c0007034810005059900c1056200702d030055021290344a040c0e49680343c0a2508a9507201074030035a00080c0500c0d01505600c46455004400f41c4452040e075506400142e40c0b06406032004028405009181006440941c00414010002402c40d9032445450514a07214070055406a00840c00c0c2341603803003554000e4050369110390010307102c5054a03207041c2c806c1c0c082c2c1c1c0188108907140081c10664203c0801c060080c00081d44c00381038115801d041c100c4450346816011100d201c259004150f0904121404032820303401c03528241c0f1702c4015903071030000003920b200c004d82105038640c0c030114101003481c0e44 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 862092859 1250 862091609 862091611
    0x3090607060b0a2c010b03150d060209040c0c0b0901021912090206130801050603010b0f010c050a0803010e06041811040b01090b070605090706090311060d0912050913060312110a05070806 82
    0x1c0084c4141070340c90b0860340c030381403108503900501c00041050603005410a909800950f44c0140e900504091a03100001e064406c00852030002521222880303017800b610b10861b94211008800852a12426010096004407900d04100500c48240300030101c102c16900111382c0d4941c004e01c510341da41905009100d503010350b405001095841c000004205050520601103070030310061a08135845008401195081d00071002210a405031640d18800645840c0196010f4410309180071806c2c50440144021249100c40001460034200c000c0e070045131020884090307100003902d002c0f03a6601c0610042e00c6042d042c0d0301044030400001180c01c144000e5503c054050070a103000c2e5003100380c0d2072a040301c0b00b01d01800003400009060501c1041071030708400625070a40e1840f004640c045090b2a0504410180242103001c1100003800e103105250800d4a06950510800204402429516020f025a2000303004405020043c0050a0340d148100300d989074581d0700a08462040351213203409911104 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 862094109 1250 862092859 862092929
    0x903011d01060806060901031b0b07031d0103090f080f1605010203060a060503010602070e1506120a0c05041a0a0203070f062a08063001140903090607060b0a 69
    0x12802c08040340910010942038040d48004001c99856402d6489441125a8084c425403001e0b0520500083e41e20600300904540c902030345500000102542540c81c608602000c514105890180c0e8080000c01d1900c0c1e07045d065420541c480d884903c80380c1101250700c00c02c60803804a425000c801c6c01040b005400039441507800b82d4640c558940d41c1c500681d403900080c003c800141e003100c4400d00c035001d580da9503e0362001084036443d10780f41c41400403507001c3d80301f03400908000040c1410090f014980380210900e429030380c5021464289041203841f41d082c1c0d05034540fa40c00c1000144080c04074401c1080d5200301d9048001035100c04494502a401884a2160304c034400101c06408020700c1c60341421202600c0b1141c640740f41540d07990042101182144584c400703603111038061421185400303405881d800280e03100004070016880700c10b40a54900411302d40c4c0950080004038826114241591041980080086602a00d6000041450340160014803510324080320101d00d140b25482564142c030 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 862095359 1250 862094109 862094111
    0x22080c03060c0d0c0912150b0108191802041b02060601030c0906110a0813060207172107081306080703090506010b070201030e070b0304021306061d060903011d01 71
    0x1100a40a040e00c5000454144242d0581444010404811904160082c8505282000c03180d61255000d6948915403101904d13205881e80a000003050310344600010150242813501841c03400040a1080348986102c46042c59241c07860401041c0745d000b080c05d0090f500620600014051101c0c030701c43c0d0b00f0304006071801480360401148840d4000e12a11040c59030645d1801c0415090040a50b0311000d103001050f0319218002c040741c08544414054011030200f25003010b003251030050000d2070950542c0214500ca45208010030a1000004000c60250f1014490807020810320100c000346000320702c3c0240401000044042440790594800c9007a141c40d5203400c1d01a44840400b04d04231600c84000608690001c801400344034031140152114901c1403501103a11aa69045e140c1408081d1b44100d060313000110a020451800840740c903100909500308114151030b100703005085900d50f0044941c0d245240b0000021070301c41204030342c4100806130081c442c0d070110042d00c0169900f00b051444541d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 862096609 1250 862095359 862095373
    0x3180b070c0b040e040b1e0f090106080f06040605270109060c08270102090a08010b120d050415091d010302190503030403080a170411042d0903052208 66
    0x1e9452805481c10f84d801d03200c16038440e41d1540d4400b55403106c0034040c002c19090120144e0380d041d64070280d007442040c1d810800005400c003e0722035801c1d104c05070440000e80d000240140c0c110400014411340c0550405400f007541e881c0c0030054441d01e080e01e0002080030304454010b48200030150000e8004607c500000c0160308041d800480701800305481c3c6460300b141700051100180246010040c09030400f1000610708102d982c001400311444c0c0d8080182a5110902c00302c4a10f0a5074800041d220b0b40e00250080321388d803910051507480756000d00381803500040c40e0400401d1107450120702074000300c28403583c40a5507650407404641c0c01d20089101d141c02c11246181104046e04020440b6800360040d42001e0031581c400005401480302001040700301c80f03d0f200e0464000103050702540c003818042c00c00d0f0015400380f206840200310000003290001045c1040c000440c490b00500004081000810840d5403804036118841e001e92130301d5081402030500c4240860b2600704c7d08030f501d541c00722b540b8 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 862097859 1250 862096609 862096619
    0xb043903050c1e1605210712110a0602180f04200706020702180403020d08070906050307021c02070f0f0518090f030f0711010201110306040903180b070c 67
    0x1a58070459011908650501c40d0300c20001c07443e1a2182c0c4000001800d508100203164204030801c40103c0c165040d51080f04a03000f0012904680020200913512252403c03d8948440070946440d80d0003a08026030884501341840062155018441c0e1002d0150b546000380c2c0d02100310081031460103403180c4140600e01010f07292501c141e00250b00d0980101c0700640d08461040c01e00c0e085071009440e0240c082151400582e2090440b0b02ca40e0b0107100403d03503904141c00c0007440c00340c030b9080441c00e210022003840309140d0418000c40848000d494007a9490750340c001d00b03d09029080740302020a0381131607180c030901c0e5004141c00c0151030181c13841c00e842681c0e44040c00d05401091181c0b503004051a41c061454680c001c2c5660383c4681e0000881d03140c03400440d4202e2455101e2003c0403081400803070820100080040d1a541000d02440280305406440700d59080700d100180820303215598520240c02018011407004d504c14a0014202c85c1c1c00e03544031190182e590004204480309081c10201041b = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 862099109 1250 862097859 862097861
    0x21230a0809011806080a1d100e4c0e06060f03031804022a010507030f0b01082e0f151403070e01120203042012100b043903 54
    0x801c8611302d503100030340d0f44c8400c0f014134001c00000c1c413005152042c0a00c201e580120402c08450300f101b010340c00150a040a2190504018141004400c1d802500d40740c00340c0324601c1c121004480c124140c3d658900c04014004803200a110100e449199040002c3c21402d100d0110314140303c3d8806680380504c5a481004160f140d10070360400019440c51040c880c0e00c1801c181e03000d860496a00040036208111460728090a52030840d100b4440341e448a04018140e41c0c140186c01407405400410321540c00c2200019003440401010403080d411041554080f500c001c1484010303400100d071010010b03544400041c20042d00c00d004078013000c40baa14090424504c50012010002842420a421912100b100711000300680100300d04102c00352152082400c410f10045000c0e502c1031140c02200950307035018400e0b01000e0607159114807540b00b9003086801c03000c603600136000d800342c100140c04508100041e005101100c0c0ca0640c0640c0040c00e070440c2d44040555800446c02016441e5002c6a6005c080b0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 862100359 1250 862099109 862099157
    0xd050606040c17011a4b270d03030b030d08091902010201090b07030e07080c0102120c070803071202010b09070504120302070b030c040306050121230a080901 69
    0x1c80b1034402c0b80010440d511242174000c40c00340c034501610f440c0541030241c24012412040d85e0740614001015605002c0140150100c48a019418860140d048000b82d544107401504142c2e642148600c6a0f120006e1444515007815000103010421204032410014020aa4079211900a00c91404c1e02070219000c1c1038414412021034005040110001c1c0804101e40c1e5244001ca05540d2240c0d160000a440764410a10880f5166030005287c101501d1035441c0115a5110324041c0e000300768005050b036808a01c00d01c0711020203060360b50714403918506510300409540034040501002c500c400411056030030342d0039010705a50081c08090000f400b00058001e0640d1202d012407010041041000300c8400d40070031582c064016942455511660503207030758803c070740c0c82d0341d104400941071041213072030700c1010702500c00501c0c0301509001c0e021809074031240002028192030240c0401042010324a100e03641c1c0e07202d804041e540040600c1ca80b43c10a0b422601099000c01d0802d08402e000d42c2442c0640 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 862101609 1250 862100359 862100387
    0x80f1b030d05070317150f0a08030415050702032508030f120a0f060e090709331520010207050607030c020c0d05060f060a030f02130b0d050606040c 65
    0x707015580d6a200007565070360300c000000c4080c0f00f840c5d203400c01d041c103044480c0c0d40300b0503841400c801a030102200300054000180038485c0b252004030024800401c0000035541a5030346907c50034600761076a2420703200e50141c0300e8000e60600c100380da0300f228081a0004910070a001d00000320015440342501d81d164040c02e040041d006101b401800044985004507541140d040c52001030540101003159040d12881c0c3c11100343c002425003440f1003044d00b08204401000030010400c800f41c03408620300c01a4044210309010f202c0008490080c8205481400340103000c200d00e0001820402140075080c1e2034082040c3c2d400040008450656007018000c440a950744240504181d96403000158002c10405010b401107104480400c1055200c29040c060240e001c0c000402003440c041300683e0410b90001e141c0da000703444243d0100001007130200921807651b0704440e404030308040000d102004294400c015a40309800128050500001180e01402190180c800b440031030244a400d84410045901c1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 862102859 1250 862101609 862101613
    0x20f04080d0903050a23011b0e01020a051b12072c0f040b04110a14040510030b280603080d0e070f030f081909300624080f1b03 56
    0x3040700010740b100c8515501c031b800e00700c9656500c451000403d0854003004101075080c40031201c041d0785150041e000c0c0c000c2d408248000d29502d060b035a1030603180c00c001e120405010301c52031105c5d07406580c1d54001c00035885115088410b804d0307440380c0f065006100000d040028046240741c0006034480040c645204425101d41c0701459140d56642c5910100d00800588070407000103c02c1c081a5036407a554001840d41401152100c2020b60400080784d00103404c10000001108082001588118015070b10a900e99100a900740421007280420158104025241c13490100d010003042000406850400c1c20544100800141d8507900da9840385103004542c00512280d108000043ca110300100080b4400c680641c10300040c132007103104070203902900304046900b0300d80c14003001007440e40c00d501503c1243c041c405000000340c0c01f924110400c030f001800041c1c95103492040c01c1042980c4103020f81c4064038009407a661005a0782d2100910842c020460041544440540c0300e0916107101107500280 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 862104109 1250 862102859 862102873
    0x30f160c0b0609090705061c0501081b12030c19060f0501081b0f03060f2a0306010e01020c030a0c060f050f0d02090114040e0403090923071101020f04080d090305 71
    0x1040064003c0020002d683c14400c40e079000c9041d48485014043e12a50825801c0500c1e1800d60001c041c0c0740140c00480c42d943c00401e845a2a403242e01420036030407400c0e10200d031002e54080031039013103110383c0102c114a4880c13205180301c1100340100540c0400d0060000f0011034003202510701c1550020302c05c00c911684001e21000101c501a0900c000b1944020a45c5100034032580100341031880464120142d81c2c5058100400c840110403440041100849011440d03503025440e203800b400098103060403c030040c00c1d0700b1680d034000c0109841c12003004017110041c0b20710313140580d5103450134061070001a000391214070490b4002c01c2911a0004019241d504080c0340359941c0e40250840c0d00340b0b6041102e0a8000b074031440c12400100050039415551007807a00c0c050070003510401c030300e5000e400090318114040204115040003d00d2000100801841c680c84030907040b81d1092800c201c0b0110b03035200052080c1400c00081c014400c0b9517464041d127414504110301a20406018030000e003c942060b2 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 862105359 1250 862104109 862104121
    0xf110f12070e06210318090c0301030312090501020c010b03070f0308161b08071d070c380610020a05211303031d06040513090f0206030f160c0b 63
    0x2c16115800000030340001c039440400505410305488243c504001c80d000040d40c112510b200b0b94034032000c1d49040d030b98817401c1d0802a00f110300c00e2005100240130032100c401400703040c04554000808540d005002551901c00040d802802414400070151091288440c000b0304a0b24816502003120341014802e07052071500d02403600102074401c03003282c800144490b030085907101c03131900c40701405a040c02001d20b1401c2100d18000040800b1240d40c020416a0410003610340c405400d403a980d0380b107200c254654107501c0c44107003820020b121070200d171010040185110052448482e119180c116003801900990354000d0341c451400200150082e04200701e401c0780c5425203882440100e10107010149007000e95540401d0080003608110300150314030b0401041c89000d0826100000000c07614186090314240005442540c00e4a60091661320b89120a0502c0315801c00c003c201e0b82c026110035a2803401240c8650079501c100c80d200e100310481c080200289200b0024566030a5120885c20803d494107 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 862106609 1250 862105359 862105379
    0x7080a022406061c0e0114070324060f090b030c0903120307020a03050a02121603020610140d020109090609140901150302040b13090c05031207021c0f0f110f1207 71
    0x1c0d0040412034070b501003a903407117609109101c900c0300c908907081081d00700303900c00800380e80703140016051913080280c041c1d441341901d20f11401102c032142004070100ba00ca80003583c01c0c1c00542e00a404481e4003204000820789180018550301e07000300e0a4a60100d044002c2480c2804181d40c1000140d20045004e4002030162000302081105c0d07004413506526482c440185070740c45080d40b841f41c03141062a081c209501007050382c0d0044040482583c050b401d051128460284610480303102d45001c01c821001c1da40a0079166014041202e0144a03894442a16501904d01020304050000d22000003400c8e85d4410700c00c0c3c1050f08036900369490324501d55001c110140241075040c6911440d41072000e500f4030454400c02c205944510f115002c070704d02e41820141807900280054006490030032220f00141d87c4c03c0314590400c3c20440c16800b400089040601000400c450020804000790108030248002540c00c05841103040300c0001007036604500b4440501c020b038850030210b501802e0140141108 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 862107859 1250 862106609 862106647
    0x50903010c1403130807120e0a050904030c1506090624020304030c0b0d0605040509060103050d02070b0d0c050405060703090f06030b0904150b04091b09150b0f07080a02240606 77
    0x10b841070034186042ca403600c81440204d1f95685001c6011004100030328249030200c40b004003012034200c03d180c80c0c243c5000c1e1103034216a4009103aa90001010800400709a004034003505121208011070750300d600301c42c0a01c8004140c117500300030224180c240301ca80700000301c90a07039901603640031842e4903200d144085600409003010701c00d030300c072840810381d601e45124091083c980304008041d5545503081c0a0300f041c010030145000c54211440078080310141d0301c203d07a48000a0f5500094a0900e107808503014011a0800c0d503010780700041000c207040d40700c2401c1041d14034001401502035541c81040c1c003140d40742141c058000180c440041d010644414084942c0c040d4040c011a600301514005012241004421114088840d0410365070100c091040c0002d4640d005d410000500c600a000d42108402e20481300c00110014075000040b920300203540300d01e94883e64554848421200294640030084000401da1200b500c000201d810300304a400d000b80f6020f0304251604070840e05400f41042 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 862109109 1250 862107859 862107863
    0x40609031407091112090c010e190305060709060e01180e0604091e06140408090910050a1701050a0603022b080a0c050f010c0e10170106050903010c140313 68
    0xd9000005140b40c1c5070140074200ca041152413960380881700e803000300000e030203031180d1382aa10600d010185641c014500c0341900100311400f02c080b442d00c62001703003210102c0e0070040c0f8501610090104c443d030803c02000550794103499020750081000c00441d00307000790941d03510590380341000810294503040c8032a80c0000018002180410141d00c0747c0c047d60009280c1c5c0e201d04c5194041550a100039480b508109000c01d008a848508094545050074060700e90b80070f00c65489480811701001010745845c000740409000e034010030740d844000b0384510070250f4440700e4a5080c000003075a02c0c02e80d44918029603900500060800c1d10120145201004440c407402580e00315000710301c0402c0d641c1d40a050341080740d0750342c05528541841c1030742c14078a40c8072844400b41e0400b600c1462258012003809600030b0242c9200e43c9051500504665801e07105400094100e200d60001c1881c44c0d004000b8150803209034024410003000c0241110b9900360b8035182c000178101800441c241101c14444403045034 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 862110359 1250 862109109 862109113
    0x30e0a03031d1c030e0a02090a05221a180d0e0f061602010212070c1802090603070201062c0c0309030705070b04091107031209080c0a08070b0c0406090314 68
    0x70822030b420318582812146044a100e4081c3d00d900d240ba80c2c1405115001d01c4908040d06050300360b035020a070b042d035000e003800741d42ca51508001034006030f00008460020400310310205041d4054107101043d074403440118a0402400c0000410300705441a284181c51405402092000702c4c610045841084840440350310105c09006e0055a5544c10041c1c00542c90309480e2480218080c400603160103240b1030200b4070080140500008a8000b543c0d800481d6000025112601a40b03801c050007882a1540c007980420088140445240d056100c1400e49450003808190070368101200350601218104620040088030000743d00c4407914405542c100384d8050880e805c2c0407180d501e4504240e555084030310200c80100f410040c00d80c950190300d0301c0390404504203141c5080c9071801000b206080c005c01d08684d40303c004441c100310100c01140c06004010068828640091804070381d1540214002e4480b050038002144031524846c04440407075500d500e4070700d64140f031503071502a00502010002107074 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 862111609 1250 862110359 862110401
    0x22a030708060117010b03030d0203070c0c03080307030506060f090114092e0915030c0c020312040603361505072f19050307050102190f030e0a0303 65
    0x1685042100a01a14000024125644c100300d1044004440381c0344001890381400c94010315a00c000c002c071184292005005603a9555244090310b0017515114010401c0d00c000d20000140074a040c00f40d4050b404e80d507810312583d11481c0410007140030303004a40500580030005003e056001c0e001c5800d0b000741c84101f0b00e01b80080280020a51a921602c3d138a29010800e010b070b0910500e001e40540207003d07410801e5030a401c28840c1c1010304c0141036100181540c0c0c0c819032340c807030740112140111180e0080403901d2004e00440311240c90703045449080046402c1041605086601e030444c0440d00900640030384500381d100381a0450701c0c80120090b550b10400c401201c0c40c1e40501d0082a1117100340d82c0354070340701510000700c1500300c401c0280c03520240c6c4481420800441c0000c1170386e03010440c2107440380d640c901d56414090b081d8418030301c000f0300300d40c4001042c4d50312403400c1d003858600701201d80b101520080e1515080c0c0035151100c40c02007458001003d090300083c025400000d41d00d8910b0750003000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 862112859 1250 862111609 862111693
    0x702030f060c34060902120a0b010603180c06030c090605040503030703050a110607020a12021b010e1918180503030a110d050723040f141503151f02 65
    0x3802c4401a00c04c1c603201c1880c074081d41014028041780d02840070040802e203600307071183d01074210306026150405031204071601c014240528110101508040c42d00502d41d43c0b080c014004103069100b050203c0d1288000084080c040d4007a101110006000355161032880e64040343d06502040410050010100400c00d200b801044510720a9400c0d40041110312100d052001105032044101011075214401c5107080d0703408192052400002802c1c8049000782c01400104070745036902d1a0210209040c000040d21541c20401480c0013040d81d400f007050241c0308000c64580e40d0300a4015020754010000300b03141d41e000380e0050b60004119113596050000e12440602582c1050341c07400d00080400b0002c0c4d1034040800401d100c05034051843c24030f480e2070844482226000d9104030130410056029484481d165a18030095030601c40c0390f19656442c02a80c20b41e03a0074409a4410300401c03040200324a1080e084150040c909880c0e0001d109640b0300c060040440b0340179010382200901c0301215850 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 862114109 1250 862112859 862112947
    0x301060b04152a0201021018060c1b1b0909021c1104050f090622020111210301031403040e0105040203060d0b010825120b04050c150702030f060c 64
    0x40f065211405030f0540040900009207848846141e010025140550145581d20072070b0010f00802c2e400342012407000f40200c4c099890090404440c640100f4a030b014404204a03903a5a800ba040c4000ca01000c4503210b10741c2204403030034648020340001a0030210000c07002c58076016001c8510411034048400e1084000c41c0a840c0705494a0000513402c406025414109121082e84016090f50303c41c0380c80002c51094100000c40c0d100603040c0701d81049040d10703840b001e1044950f40305400f43e5050802725040b02c015040d520910060300c02d0740d2282c403038000b444008400c4608480d00307044070062130707400c00c2c040000075440589121340c404071002075403001901e403c5189000f400c1d80800b03003074840501c000c041102d40e0015218803442e05080018003c1200840d1104a140d0704107400c107150760307151b29140e8601100c140c16250b002c10100d0320308014408000c010081c1a100b07905403a00b0819080215507101400d569a1035041000d211452294016200b030f0f0006809142413802c01203031581c1050 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 862115359 1250 862114109 862114157
    0x80907050307061707300b0303070c030c06020d090608070e03010e03032202100311161118131502070c0902040e07020d020c0112090503031003050c0301060b0415 71
    0x5000c9001c1c1210030300c16440c1c94002c05e60015903070403c190081840300429540442c50100e0721940c9441d15403207620022030764044200f00d800642180c0d541e04690424580c965250711040f10b003101040b80115001d48040b0380c240b044111516100c0003642400819608450000e103500200705211000009a540034040c40240e11a0440a1540c07800d0802c10b540039005080c0c03a003e942100760605030016251590142c1c5600c1061400048200c0d50071000d4030f0912074600d2a81a100420054005110360510104182d50084540801d01035129911240c003a00071201610100d201c00c0810b40072648101d454100c80702d0b051001803811143d52b90381072410700c075074220620050f4040780c00c2c4610440f42c424181c00030103a000408503080d805500950b100b42c22880c0a0400280c28104802c55040350040303402d06034002c0c15280c507032070110103080c06080a440141e030780703110703c4002c0403031400d040c841d80040d904440205490507003000110320030102d000000302c0800182c3c501d4040709d40a401151 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 862116609 1250 862115359 862115369
    0x8190303050402012d12140604020304030c0b0103030f120905060601080c0d060b0705100603081b030715090506102105070e0106110c01081e06040609230f040201050703080907050307 80
    0x58070710f0700801c0004201138206c1c1c6d585980c0b6490407140040010708640200d44c0000100d0340540c1d031ba1340d2031404660351240c55000803c03000700c21001108047c0c0140c50910344442641e41d00c148010810902425210941c601420a411603001302e01e072548a681200e9000c0304a1048616000507501300e201120003952107250780e0b0402160302000c201d000c1c4240f0949000308441445a241035480d61081d9100700c0440c600080c1c48001501c0c2500000d01c00d454819070052901318060078586a0708018203d03000c0120741c1c50040d034000030b40303c032755507050030044d85c4011280d081e81c500200c201081c0607101c0d80080c0e40d14400d2940000c0c984100c0c20a00d4040d200b19a41e42c243d0350380d0300070f01c20700d024248070b1103d0601c0b030484100324005001c80864984158034481038081c5031103003c080750040400380c00040c0c806051080d1103a10f01501500600390041e280150011035a0742d6a001507064019580240081d60030009103000c42e20a996590f007081e00741c829100b03000d6545c000640350203116444 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 862117859 1250 862116609 862116677
    0x210023606131a18090709050d0f0303140106200c0a030c0e0703020901050f1c0501030605060a05010201020405180414060405150f04030e060f120901150819030305040201 75
    0xe209200e410904099200c3c0c0c0310151034204a1803482c002c80030442a0040c0e4000c505200001c1c90030380c4664160700084c24044c042c1a4905014200401100c000c10015008603042161b000c906d0004810703071504031842a41c0b4008030010040c2500c26080092549041034443d400404810f50384100144c80110703c2002145802407030070345102d000c0e0400811203014144188441d820598000d01103030482c11025061640da020b03174401160f60440e48241080b202441c000c0080108040c0e940a41c0c0107110490345d0360500c030f0385c68004900b43d10460080640100045d4080c0500040e11300d1140d411030b00c1210703003450b4901c04c00c803032a01d4501c04940aa0ba01e030300030070036100c0c0360072404082d80d040720307000c01d80190914103510041c1549580c2c0000034054000055050411400da00039181d400002c04a03498050510244280c0a400d0b4042c1c0c440d10b5034100351000030801d400040c42e14410401034070740d03007502105440980003000000d1060b03051021400499256110205c20155101c2d00596 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 862119109 1250 862117859 862117897
    0x7080d050901110c0d0503040c09051918030e0d02040e030307080712060630060b040e0a0203190e0a02060304081b060c072a080d0210023606 62
    0xc000d80c251101150803600240f010021846000340c0411400c1d020751060034a96030f05e07150b43c41c00b020b10303101580c4000480c40c0ba020500640180b6020901d881414030042803000700300007031204001c5000c0c0b120046c04a404040ca50180d8201404440d51650008100103944a6140012030460380304440440c00901003a0400400a03004000e43c00000441c0c078040042500340403014001501040d5103903011105941c1c00c1c18801e08200c000d040864050300b003480ba0565480c41240f003034100d4014003074905202800200416028800d0704e110350080c6440d400702c000d010261000030504590340d201035024080ca250096100c2c40300460046110b02d0401d80e81d00c0321010401400740040c21140b0140e08a08140800c2c2d40101c02a039995641011944800303c88412080e00c1e40329100d000c103400c4040b0040005001c4502080c080311821540d001d0303c0c0e2549442030340101302d1003000b1200182d000003941c1b403100404540603495081005134500e120700003175040080e9058100c4070200303040d40c148803 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 862120359 1250 862119109 862119121
    0x1005042a06080c043002100e0102011b0206040f032a4206120303020c07172e0e0c180603030d0506010c0b070239100507080d05 56
    0x1502076a805402c4000352420301e41426041580380c192000c0d19007104807085846600281c01c0d9000d0700c017035035009285181c950a5507801070f211004031203445015528211094503007814520603841498156070150400d59102c0c0d640115105099809070304010300004003511a001c07501c1d1480c800501110f2000404605161400e4298a591080540100c00d607803c440e402c0b0301d8040e905c0d094044400c1e09120208091020401050b00d070784800490902d1294940505406074010444042102e05941c2919103171101e400c0e01413141c10588089a000d01821099801c189a90038804140c921540816080020a80c2c0684220340100b622a0f00320542c1c00c9514036050061090032510050140030b203251920010382c403402080684a10603445000043c4143e01c83c6152801056000c4686d602c00d04110500a544d5000704c2c0800290304409500c1c9510340e500c0c0003800351030000000440389040c06807801d20440b060f02c0c01c1124280101032241c180066502406000020030900380020b2a10780340d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 862121609 1250 862120359 862120367
    0x7060f0207020f1224090d1e050711100e0f03120304290403020c01020c0f0d140309040f020903010621030809030909010608060a05030f1005042a06 65
    0x40004004054410440701005031944800303203004041c110f45800000034600710140c2003129080901c0b904001c400120400c4e4604e0011984c0141c948000300c803082c04a241082d00d2800c0c1d00c100102c01106141c0200805034031400080c4140c61182404903115180070021609810303001180c80049004040316800d80d0a00702d1a801045008030000d0a503204007140109040c80080c00150004600f003c0e144402124150b0f401c0503403030b4400fa5203c0c540f60a0800039101d031007031070390140140100c21080340e191404c81030301d000150000344014030002c215075400c41590584403558403d40400e01284009548030b00c136101c2c503400d0451016a031541200209800c54031a900700c440d0b4071240710380090905040e500c40325441a41030500d03400b1501c0b980746a81c5903009850b21280d12040c007000100351558440001c80c0584000d03520751000a03206c03800c241d120199030310a5411a03100c000c500000001076000359400c50b0103040b503c0d00f64280c445000e2603000f62001d48038850610008100300302c03a88 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 862122859 1250 862121609 862121621
    0xc020a080c071502211e0d1103010f0e0a05150d02031615030b0a030317072309030d020a02011209080408030703081012020906040c050904050f0105011d092d0c0706 72
    0x502203080c940340018046c05040b1810500d0307010402c00c007044801c10351005a00c0b40c0303200c80708a2031a41c0c680d82d50354280307040250303940102d10350384400c2c0c0045a9124158014240200090b0583d8410700c10450140010303100c0c040800e80c0d041c4600d6204e04050380c180d40740340d0050300000c0c4085126603440c03c40541070302d4501040e503000d0600780d0303000c02c0442d030300280d500c4060041442da50401d031a18031003107034202c003000031407140c05511040300f4000c440b0010003000001c4080e41900e00000e01242d05031b8a4002d0044080d0108500300701c43e80000c109680041c20803485495094149925184003d1030b40e042600120301103000c080502ca551440d021381c08004200c100034841d80001c4031b501142000c03038090b0000e03000d95203840080403118001c5094440e071200c0640100600e16182c022000002000e100e9180030030590428040095400c144003051564042c1660a450700c80c4000e0b100c510300c001c04440d0403402c490383d1880d48103e0008216000d00003000e40035888503045e050520485034 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 862124109 1250 862122859 862122913
    0x80411091f081b010801120210120606090311040504031e140706020309010e0a05030d050c0913050604050a11070f060914070608060a03030e0f0402040902040e190c020a080c071502 79
    0x4105d0010004401414107480900e42c1c10f64040091300a1044152048003983c0d0310300031500d05040380419000e070721403511401c49000c3d41ca1340040c0b1400d0400d1108540090750040c0000c1d48001e401159001070a02c2c0002d07201140c03608142c04c9030b01c14000c041e540c201c084100c405580005c140304101c082405020703851b0016102510342100283c3e1810b5a0f481050141e000380c5032204009440245c005d410755003449006440745805c4007081c0440401401c0456003a0704c12850280032940600d410300c600300c000e200c40d4004601d8541d69885000010b1a60481100c0158540003468000780c07643c910701421200f11402010800d0400d0005440144001e1034503001b003000d4401080860380c00940103030120015206481400c9101010401911860700091292800001c0000392403660503640d51264038403010303600582070310400c100f05031400e003088000185d0220b50769401084400b4010100510000102d542e40313036840700c004400300341c41c0201c0c0c40980c008500b044030101d105c400d4405490 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 862125359 1250 862124109 862124117
    0x80409091b08123009100609150611010f020f130503031306080402130501180b0301110a0f1701090f0c020f25180207030f080411091f081b01 62
    0x12496280e0743d070340d010b991a038a4441418128100c14144035030005410b2100c844404801e502d8081640c0d80e550a02d00300b0504864902a4002a0800240318410000198007403074200c441c501303107046541a59024990380381d9540d4190024178101203100601c1d80001107000180ca0b056028050345a040d0903a0140c0e0082d082005030918403407441041d4425a04542800100b5413102d0001c40c156490b4440d002c2d0456180c0ba0001c60114501802c0e54510141b440c41404400c0200042c9402d03181c0105004450740780900c00c1c800207a018124031000c000c21403400180b0103d15000c1000800c60030b80c040d800d080d50311a080c0000d04440d009845c00721300140014407400001ca0074140e42d031030010b41c1c1241542c001ca4540241d42901090201c028689a80003c1c08080030500d118021741c8808000c4020a020b5000741659a0203a29154481c80d044421a1080c10040c418003030a031400816007e501c51020110030120121828403402038016140103040c10315908c50a202a17103400c007841d6041c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 862126609 1250 862125359 862125373
    0x20f010908090409030e030a050c1005070c030b0603210418020306030d1b0f060b03060f010b0d0b060c010e0d0306140306060d06020c06070f0f0f1b080409091b08 71
    0x8540c07000300300c039020081036600042c00310160070119041d601442103258107000b4511a1010700100140c50300000700d003120110a4051030a0040e43d980c0f0891380010004200c50302c042022481034465640e010780e001d01510450031400001040c00754140e0807580d05d20340081000c0c004412100110005e110002c44114514100500002e81c0e406540042ea0108001c1046404050300940d00100b08140d107c01070340c59220315464103602819410074228000c1c03095800140d485000007019604940b07404004a00d40110408541c0c05417203c2c0150300d130400810001a40180b00905c104c0c014441d1032800380c80c0c555004400142070f03a68941c0003107010b44401051b1b00c6161b5011444542203582191810702a50b1589002e170081d028201da0100c050141900704406035800040803030030403100707a440381320b15219200c00356803420381540000009090007000d22210003060946154060040703100c10704007a0b0b100120800e882b01030700c0445652000b011419101a4021444806088940090090 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 862127859 1250 862126609 862126613
    0x62b0b070801060c11030c060403050106360e1507110f03090a0e04061116060e070f0b0306011e03060501020f07050102030703051309090609051c050a11070b0c0706020f0109 76
    0x10205042003e170940203070030035080680c2c0d8100a1200201c40c080d01258907280d8070300302580207012030300c10214640c22800f0310351004070186171040c200d108030107110454481803001080061100c0c402c0c5070705620400c11001f4192080d01d42c094400ca4090f0f4030100e0070410740020340d08240c1001043c0240798000e20000344176603a108201307070550758810301d0700f0305550321401c102c80900b2280714103c80c603010002e0655111106406101b400500490b02440303070103508134610382e0b1030701c00c1c0c8102caa0440d5001d80134000104544011a002101450311150807899410030f98a0b07a52102c00000100c1d43c2d07040d00b0056540c06011480c4541006005000c4041c903010000c0d442c0c1c420307079200400300800018160381c00403203954107030302510810b1802c001003200c1d850301400500c26000103540f18400e00e1040f00350031407864100d504480c02070f0f85890404900403400c0d80d000c401113600e5111806003442c08070309a4940b401401303c60322104014880306103003a60103070614103188007400345d0364100b90450f40 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 862129109 1250 862127859 862127867
    0xb0702210a050d0b150405090c070b04061e0c1d151e1605060406050906151c0b1e070207080645010c0f1205062b0b07080106 55
    0x50320700c1041c100140e640c003503e03840d10010004215190f6004282861244044000401400942e001078441e15015241c1c1070700c06c10140a8480000c10300d05445001500141080d041400407181c1c1c0e200608007004c41c0c0c0c0350101581e08451a001c00283c100c09500280103001c41c0342c0c00149002c0d0741c100c0e0b660b040c0e4446184a4170515403980307107000b40101c03d800c141130808121a507060a02a5002c2c0024017441d00315200d40d815102500c1190602000c0340706000302007441805400a440100303208203100c4148034043c1c0b0300d101c01659240440e00c41070081040315000038443c1d040c1c040c290071803002c202d0309094614030107000b2a0866020301018400d00d4000541c03640c03c105410902e840300c6003440441ca0f1600707182c00205540121f03158410005903002503180761030402100080c4a26002000101c0e01003075007402c84c0001410520611401c00101e42c0003680080300a800400c003504103d88400340214140780b942e01c1054100005801d104c9040c0742507400c88454034000c0d0607545000c400070 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 862130359 1250 862129109 862129117
    0xa0b010c0b0105120321070807090e040f08090a030f0209100f44072907020a081219021b1e030f0c0102100605090c0703090302030a0b070221 62
    0x82d01541306080700440c0c452007001540e9500f40c07022071105034907541907208241e40c0d40654240c1d0104c3c0340940425940c5020b9610203040c1c504c414168002680ca0340c844201b00b030a90801602c23040410040d00d1100e0300c0780c040c0c0c8400b03980200250b640f81400c13481403046050300107090442c1c9000056041c0075120f803034484901200c04129a500e00803001481e00311030503d104580040150240448149800c3e007409108104071010f42619480742c1d59046900c2841e078990350002c8800080980c00a4030b400d0308025100d0a40040c012041e4203440748212880e2280e4860303142d10341c0c0004541810000c032840d4401d070044206102400c0d2202c0005000c4000c221503400c2d40f0b229912159a0201c4231811071085036520100608881c2440c5007015220b896035081b21440303005014500c5141e00c480c660b0300400044640140a02c01d15030394081c2c07040400c0d00120710031010062009030000c09603800700b14801e10030303014020001c02400d11801c041c0c07900c103102171745a800800c0a440441e040c1401c0e03042d6 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 862131609 1250 862130359 862130369
    0x5070902071109091f05090f070b090607030509100305012102091611010504110a0911030a090f0510021206041e180c08070e070203040f030f290a0b010c0b01 69
    0x80515511481301c021306107840001d61a18603402030249569145440d04002c1c02600298140c4a040b0280c0d80f00075103c9181d80145070300d40404000321007250809500500c0000c0c000e02d4a2030603d101100000c140841c11091180083d413103100511401444580002c0643c17803900740d040201d010340e80880c070804030041032605907450900865010a0054100c418480ba0600c000c000b10b10f058682000d4080707040580c9030092690820105822600d4130030403512803c094445411540ea01c2c0d801c0700580b096080032210384a035030310301100241d0104000c001e9108e002602584a1000507002c804200303000701042c2c490f40c1400c00c2944401c40000b11543c4148014001044400c400c180700054510361340783c0244482c01c40840040d4a60000c40c002041e80e01c15280c444050320b401c2022a40d03401640180412084204400c1000801180610404030f11550386c00104000c1004004040d1561901c0580b035070841c5c00030050801600d120300120b1010074200485601015100c12001280500403 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 862132859 1250 862131609 862131619
    0x90910080c01021b1c05030318390102160b0a140313140325050705030c0303041206110d0e071a0708030603031204080d050907151d061303050709020711 67
    0x210170b111501081301c410000c1c0d008011241c3c0e90400f6100070454074009008031485016180c01101d80e4a0034802a29100401645204103115074440e140c840e0304152004905500c52844a425000500900d605c02441810080c1d52541070310800688542d02800001c0010b000400802c05103e000c00148001c0303540141c483c40d0700d01800850303545503114400046a00415054422091170703234034200d041c065440703103080e600215610001e01d55105200c010301545500280000e0052008000d40060018054131010481100b4103555560b070b980412400701c1c04540360011114031078000c10031580280590a0f10101c1d1310b8903001101c0d414015100c008107109400808102c01c0e50f001c00c1550454480030818000f14207142c07500c00042d900c121800707078005080200080c42c082001c02c034002201c22000da201907101680d50101c401c0c940c0b0002135074402001a83d0313401c00744c8032032014010f8111114402c00159045052051a101d481d6004082c098010040c3d00c000449201d001402c0c0c183c2618 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 862134109 1250 862132859 862132879
    0x210050103150b0a0b030c072006030106050c01020d05150315060f010f12050114030607170705090d141608070542130e0624090910080c01021b 63
    0xf0026090500e0795026021100d00441404441400c0c0801480c0f141d206181403a14590300c10b0050611119140c9810b0380440e060004000440c01840182200d141003800103140c124060809401c580c8152034a0070344060030809520a400c04010391016074141000c2d00343c0724a40100000d07140704d441004076041198828268009d43d005d102c101d01d078601c107400103200a6840c0d084400980c0075210002b0701c280324940105140b18003880c0c0030050b62400e8620114241e45400c42940c082d070240b03075100d4100d0b07514260b500c08182884107c0000314402c1001e406903141c0c0d0900c0100e1040f058002076900c0e0011481040f2581d5601017224140784241c0c26400c100d100c010820209240c02c95a04040300d00080e001d0f0300d081d101100510f00a0f011060a180c942e488418440c580c1302d0446400390080c6124054101407400c2900070030140042c2c1c0b0600707261214100101e0300042080e11070758008400481c050212000034407107059901c40a01c014201043c0f20313040903081900c44404075000b8882a5 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 862135359 1250 862134109 862134131
    0x160302071505070f0807052a010203070f120626070510090503060708040201210e01020705070f050f010512070c0c1508101206022101030b0403021005010315 69
    0x18054658058201445103402500e8030701034005003004452010000e140303616070821450044524a0145040d80daa144c01c04c114141380b02c014000a400d040c10b8000d5003450340da030600342400114814000d540d6652041d0a0022000d000c09920304420074241c1d00b8040c05221b0003220341c110740144602d14042d4104650090359080c00d180f800e4100b96080f84441110151840d048910340742100e100b6000c03940d80382c2e203060040300d080e8002d17100240007490741520a03d04d98451f54248104e5590307080001234660417002c00710b0890740440c00440f0a031300301039030400404503440d28a0000300420b80350407030940c01540000b0460b02c0f510034030414007180d62000c1441507114a907440c1c9543d5000003110221034840d42c4080380e1018001c103400010790302800040295201c00a042c0454020f0010741c52418116034481010b908140300b03000d8000ea498a004c40382201d6804041d000798022407042505007031074200282008510700c6001d9000341820010400280301e0414040e5083c0110b03800900001c02d0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 862136609 1250 862135359 862135361
    0x30c0904080d150303120c0801050d05010e030a09030c0b04150809122710020c06070f0c24030c17040807140313050111030d020f04080601090615171603 67
    0x40b8058410151038500749404004a00c01200e043d0390103500c40050500c4072010b4202030b00c140b0b04040c070015401c40c004001c6410212000d030f00b624480c200100f40d000210040c0392035034000d102c2140c00640d82680810520007583d45900103001c0f4030016a140c58146104407818a02103095101003040070400a201700b2828005a144120901035031644c4400280c20416103903040354211a8503184042c081c4c10901e001c0b648582c140866401902d28250040100111131b0080c032010380702e048100940c4000500248a0080a0b011001c40b00001c202d01c480c012030503a100c1080c040500d8602042c58010360341182621404415291441506903100c0c5003d04031405000303001081003056443c0150529000f00151910f400303080e2070058400d540340b0044503410b0225600000704d030002c210703003106007845400402c0031504180c141443d0a45d1070b0102c500c1e040c4260f1005028a070f4401040c84201c41c3c0d800e02050240c07951602c02082c1c2e01e0000952568071000d0509a0103281b1412000b820300d000b = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 862137859 1250 862136609 862136617
    0x4080414032a01120504050601092d0c2a02150d02120103030807020c150307050712080603010f020f0a030e0f0a03030e100c140d060e160806040b030c090408 69
    0xc42c0450700381c07102e21a00d01c0711a81c64504809000c55a0103440020080340b920a883c4070b076801074000c0541d6442c041c0c008004203800b401600c1002c0804000c01a413160700820b859202580a100050b40a02d01c200200445000ca003022140064082800c0340e120790707640c0100800c3d070110f860003480e040f100050303452841445074040032240041104200c9264000995048a000341c46018043e41c0c1c2d1541240c6030341d018014140c0c403020741e001d040c80080000000d183d0104150401d01d02c0c10b0410f813103101405007840c0c095800501040e003000070509081c02003561702030300704600b5402e000c40080114454015246000209540c658242d581800c04000c00f044201c800741c292014030440381002800352401c0c85e000303016803081d4030350100d10ba0390501c0742c20071415a60343e5040c0202c9450400b85610752101e4005004a61200408549000c0010030180105076003003100c08a050302000c090701c01c070030080c40c0f03902c84d501c2c10009076001d444c04907005102c890222015243c998032440c1180e02c2d405 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 862139109 1250 862137859 862137883
    0xe061f030204180207020f03030f12100506031602070b0a090302040203090a1b06020c03030906090d21030506031c0207060c0311070311030f0a02100f201f050408041403 74
    0x10f401c0d590072120809a00504007503000340c0c2c6c9001c2e903054003018140c1d02d00c07070035181000303403d01000f82d5049142000c0f503490b00721640c1d01041100700d0399040094060380050796803a0303842c858030b2540395140d50104605001402c400f0703201810001500b50103042c101903848042c0c0990b4001000650809052041903240b0340c1c890502004144060982d50203c9118020003025105445c15245546000416a981044010410b5240941d08410f00c18400d158401c03c03a0030001c00109100c0d0a80044030604003120103603030004840c6400000c051900c50400e1ba00c1010040c48a41c101c441503011032804d081d5801c03414800110b400624080b9194007181c10000d0003401111004410080b021003075841d0700c2030031001c890a10040485040e02c0e4101c042000b98071042101c0031040300f40c00745040c0d4848181908000d401d0403038041007980c0f0001c280c400c0454a40080090b42100c150300b40250180c2c000701c0c20104858545a0794042c1903200c0c5001d00e01d11440b000d201d5010682d02000420390001c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 862140359 1250 862139109 862139129
    0x30c03020c0d060b030705030105040f061e02030a1a0d020907030e0c060f030702070b0f03072105130c091505150f0a0201050708130b0f1801090f0b010e061f030204 72
    0x2c942c0c03d0090003020101150b40c030a000e0413800244078603050203100e000d140c120414081080d41603941c003000342075000c00f40a610700c03204c840003c0080ca610203984038900c01600840c0861a0000f1149030360007050300c561040405040400168949000791548600035007000078a980c05805180e1522001e1403000313030300490024044103400c1009014500501e000d4013107807200390312481200c11a00901440042d600c4062000a5030700e031080b0402916080b01420030700c9040340d01d00000064800460301c10340744080c02003020b000c02105440702c2004200104040010260b041c3d00d19002456230b1107024400d5081b00c0300380721460055022030b4ac1880104c8405542c0e08802c51340640600812220b50300032032414000070b0780a040c1c40e040c0001484c1e0081e106040f540c1d0700040d0202c138107405440e100703440f0740d496003006610400f4820000309a001c0c501058242d404c80c9400e031a00b032016049801420480130a020341a02c854280303d0030010340741103605c045420308804a00900940c1d1140044c0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 862141609 1250 862140359 862140379
    0x4080706050a18050f06090d170408070c090902010f0f1b0819020d0e01020d08012c18100b030712081210141f030e01020f0301060806011713030c03020c 67
    0xb00015074180d4503c5e94015181036030f0701d45131201d450382e18207189030340400e03c0c4415803010700814032425036026108162042c1090300e2a04c40c1c400c0014a42c00c200303c056958410001550380021179608641e4481c94120b403818004080284045a1000032039002e05803640450100024102502c2906121030f0034480900c1c188036009503909144c03201200070500c511100203107548081000c240041a54803000c2d201d91034000d030404907103403c600344000b04058002c1c81c20041100380e0700070b01801c00c4054680d07600303110383c9045041600d00c808403040c04e4034118003080d07551004900070041784c00d4095400c900782040c1c10682d0141c4110b2060b410114044001c00c4100390103265418150341000d00004070610303040042c858071070700c00c140c000d0190310f034181404c0c603040c800d4001e68481d401e600c00250420305652940d2440e60030a80000b000301e00d00c2800c1248550f4060b4812030000441c01801643d8201f801c240329002c00c80301d40280402c0500001a0305041c02005034030001c640c06401903603d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 862142859 1250 862141609 862141613
    0x328030e030a051c0e1f181503061409040605180a03030606200709020a020c04050a05150d12140921060907240e10030f050a020304080706050a18 64
    0x4d4501c2016206000c0003142c06002146206040c9000580e602404841da0350140c0304c10344c0d45100c1034202c1d01d02081040b000541280d194800301900501812016299000c0401000350a90f045a00090340003031800c104440255540c010154100e074105400040d5a15460004104c01d001041808042d1103400c0300c2d81c04050b403551061003110035640d00c250154006c500401150b080c01c00c115021a440604280840c000c00c0d40103084020060046507105440100810709481d800c035840d20303840d0303910000c0115003806040c02c10000c1d03400304c400509441d40c07641d8039070111201c00d441d0750401810003800c50302c14941e1012200400720084c0501c0c131791401841e141d0b41c020200318808910740900c40120b001500000b070003c05031041c16200c44090b400e6515048074001002580a08016100ba074400f50340d107034400300c80c020712840d680c04140580300540b0201901d070060800b0050900c10410080460707210400c1d20101c5a024034082a9900c901e210704014198180503244c2c45501d070031050007 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 862144109 1250 862142859 862142863
    0x4031106091e09011202093402011508031204080306010c06050414010b0303042d090c08071b0803040201110c040e2407080402060f0d02030a09030e0328030e030a05 72
    0xb003003220449640c0f81c40d0380c07107602680760102c561900a400801c21000302e21b8808400322000c920034040b07420f8403906203107003001c8808201740d5030813500941d540e802d895050500c400b01c140042c09168004500e0b21036640000c006a140050026144100110106619a2282100804203a000581484141441e040808407a946490b5000d0b2561814155031064280442510111110003004107010302c00445d4031841640e151000080342d4500c3e09012440710028800c1c21000308469551086030314007032001500b41c1c5000c4802038400c2000488210000d50321100701e076845a0b080c80c190310003c8c441024617141111040741d1561041c14001d40907050710000411000311484d110707242c20340302001508000010801e0b140c04000820740c4000501500704500100401c1c13840d920310910b808004c40c1840c00700d030015200d084106072506802010701d1342c041001e07030610404401900000848104560103050851940d00d00c40c6405064030007458042c000891060001030140c030500d07541c62400c19 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 862145359 1250 862144109 862144159
    0x80f0a1e060936021207030b0f0112080d0c1e0206150901050603042a0312030c0e0a2606040b01050a0e0115030216020d050601030b0a0e030403110609 66
    0x4120303282103503160030240c410780440480e03491040c241d01c440c0b41074800310b012024840e03c26a00801d650000018200d01000070400441c040d02c8a51031504180441c1e80091006900000341034103c441d4140200c3d450000700d608561020300f00003420003105909988100c0d26180d00c4108900c0582c800e0b54581d00800c070a40320b40c0049880c90200c030707010001c01c040d00c0428003586400c2038041c0001400201d001110096407400ca0403480039541d03191010145803200d0342c00450b035040c0080b010b642c02903090300506255000d282440e0442481e4000171840c030490134480c400c15200740c221003a448000b620702d10305aa074038503402d6440910f802e080107083c0800a1103514041d120002c00001d0041c440d48065060300c1010b15600820840301400718043e400070140b194503808224980c4006a485a91045c41640b044011b044250b01d9400d0403a000c3c0801800400128140318203006100b201001716400e44e83c1c0120020003118048020864a000b8011a5a04968107006401030100b00c86144 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 862146609 1250 862145359 862145369
    0xb34081308070b040e04021c0203030703021f090b152803110123090a0e01030609021f0c080f0405031f1b050405060306150a050c06090c01080f0a1e06 66
    0x5036540d0f59518580d00c3c0c14130552140c0c2028040321400b150051929240c40113820341d00c11040c100400054002900f15030143d20102e015900030441421003810414000080e0301c3e54280412804060780c40381102404002c0c002500305105600c0100190f8034022507007440b80f0030b4414150700701c841040004002485004c03d807107040030110364400c10b43c4906000b0040d442d030006500664907507040c81e040a41c20424031103500c04090b14011401c01000760681e8000c40c010400894078446c64014408400c3c03d5a41111064451021045030315030402c20001c034099018074800e954606401d0180314a00843e00101d91602910b2165410001d10408090100480c00d07410084405844001ba00e410035a11405000c01c5050104008078900903000e103901c000c01400e01c0001c48444801c40286905c2440418080341000c44c4c8403400368000c000d040c1c2d028801c1030003440c009030001d0001c0c040d203d004001144501e4101c000550924103038200c0340b41c2c900c0c894001001041c04090f0394001d400d0902403 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 862147859 1250 862146609 862146613
    0x1031b090311120d1b050a0b180c1f0c050703030e0306090f0c0f06091908010605010819050405070e0907060f2102030703061a03010f0b34081308 64
    0x800320b002d24150031000b9801a0202c000d20206106000075200d8a003000c103004c511008401c91400420006d0044541c800e100d03140144040c60500d03070207030030005112046103055121518404181d01da104e400007441801c038400f18503840000030202c41002008100501501403c4000020941c01c1031a149070b5500480984030165503140300c66a0300c0d00391445c030300c0c2194021260700d5041d0800108002d89814041c240d249040d110314042042211220110b2034164010201005050004e1140c60060300003403a01c0c040c030b41020b0b4082e040380501071120300309055862010800700304040105200811125803592100d160040281d07492380c00c10311a000c04500305421500c4200c2c8070300e407d17a0131001700058200c0c01c0240950424003e420051000081c180e0301c1d407001c50304045401c201e61103000c110820315680d40c10718000c219900c24550182d0f069540c14019643c20203800d14000d402c210502012641c0b922003848220940a0840c00241080b5030000300030141c6e600d0440c00c0c4096460600c2 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 862149109 1250 862147859 862147883
    0x50c0f0a081515100e0f0111030a0809070503124305010f0509060a09150609061a030121062009030607052d04030c06050c06060a05060a0c0201031b0903 67
    0x2401101020131000c1c40008101e400b610b0b907945015509003090303040615042004010888040d49954003918840021415800802072801302c100400d4015040030b50260800003495004a100c0380a40032048040100a5032031800440c03042241c2d2000183c000d25450340b801c034499403450f600d080c0540a94140d4208070215015005500502e405000000d0041c5040c1e512961110010706a1600c112501e81e1106c2401415034401e0041001405400c04001040c40c80c00c23002882c610740d02c1100f103056102c28401000101d0488054000060b0040a1280201d2242c0381403801030912290b20101501d4904100e00880c40307207405028402020780460783c0a845400f420340c1c40740111f03c3ca4a024101c43d50780a0404141d4a490440c1e110b00500914203081c0c580d5501c4c102d0340b81640240c00010b01c0841c410710b030300c0010401c1c0d41e0444425210222024180300128610380700708a94001401303060650002103912983c040d00e4041d180c07484901401288000c0144500030902c012b40e03005081013 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 862150359 1250 862149109 862149151
    0x7090801050402090106050a11070f081e030714190f05010e0105060916030b0303040303030c09090e0304030f1e05010e011a031005130507151b050c0f0a0815 69
    0x403041c0390185400030860f20103686003407400c95482d8003580e1a4000c000040216141c00102000000050080c603141107194a041088240c034044090024450000d4200b8642c506540040111032a0035004030425880300d20b80e428851030310034080581d0200703c03e03042095044c041c031001720412061140c4000d00080745074150150903100b081c1c2c1c05a600c00000780103e83c2c9a154428602c0180d11281800b040c049942c600080c1907800951059001ca0340314102095107540c05040c2c0300241c5a1031100704828008084050b649009030b0100614134040c460300701c4280940300a281020002c080401d003004803541c0b4006018150f1141d5172482982400590074554102880030341c0b186c480075000303021084110803501c01601c00079200710a0700c00d518200c078000c10000d11451005e8076403402000d40da1485800002c0c07a0301c0300421644000d0303000548100010324049605080008100c030041d00240c1d0000001c0c14050b50b039800400e1038450070820f0000e83e0041d00b05a8820810001c01c288005004 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 862151609 1250 862150359 862150361
    0x6020a020a0e04051b0316080c03010516020a030302030c09040207030207150906051603030b060d05060a0b0301050d060b01140c0a05250b030a02070f052b0203090f040b041407090801 80
    0x15140100150445e5200301d080c2d060700711080c2492100242152049640441200c1c014200f035042015140c20000300c101e0701c1e0409004070f42d0816440751000d002d1100c030303440003520384561000043c20550004003041542c824101540c0f05000001d008540d00c03505441e01955811aa00c03501d04040001010080360310b02400900d01100c06584a01d07181440c0c55641e041b54080511044041c1950f9401c04c080a80b1120081c0641c0348180c5000509802d148040004101701580041d804c0f42c3c0400c014000d54a86030940318050381c5c800c0021601079896801a120290391035440e14a00e540071a184240c541c00266811845000d00c2c26103a042c440c0d0f100b01500403510708407880500120050421164008d2402540d122a4440c0d0041c02c2a2150766035172110813100d4000d44a6502186020103980101110468a49001c15500c03521a6140c0406512806109209445122040e0481c402500c0d6900700160200d4020002c000485c5241d901d880c6400040c1e8003840004c0044101240340d03601 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 862152859 1250 862151609 862151611
    0x120308070203030c0a051c02160b0112020117151306060305160906110a15060815040b130203070504150e0a0b0919150603020a112a0a0f06020a020a0e 66
    0x1d901c2020310748002c0740b10598890b0320043ca07100d0f5441f1845a20440c48043d40f028120800300b82a50007041d0200d401d00c40607a80043c0c0128454115144c0c800c00142e0300141c101180c108001c004001c2c03a80c0d1900403a01c05400ea0300c2240d00045d100c00c003165510021744c0450b041c1ca069860030041525542c0c0da0001d0181c5c2134510750041039580340c0511a140c0036000c0b010114081c182100d00c0c01c4041d0340e612481094000074440c4598440c82c060100000071701128400540000146245180c00e0303c0b00035500e00050110141c42003920300d9a4190b480500012000d00406801481103a01c86a03d070111007080d0b100d5031507a0808880802d506560500a10f443c0140c0140035000ca600c4090b005420001d4004200030b41c00e6443d13944215100e041041070000740010340700181c440c0035248002d45241e500c441b108007540c1041030000701400c1d040c00d9410241c035088010a409426100100380b0305070351500002549010014005200c60f40001c0d52900075100b030341c0b00010a513889000c0b50080318 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 862154109 1250 862152859 862152871
    0x1b0602010615080c0c070803070c4104050c07031e0f08190c020a020406290a020a0209040c0612020a0219060b1c0b010b0322020301060302040612030807020303 70
    0x10745500c0d00110340b4490f0342c00b141c005842440091a100010f0384040c9008066440f200c0c50b9000800c0040034022002c18110003080014504d0380360818102035601c54010b040000e4118a03030904412041c12020090700e80a0040034004024a0030b003030a607511540c200b01c10460000d0700a110000c250b416203c02ea40e80e0b004d450701c542d5040c1082420941d40c0310001080341c00c14400513030741134070184100e0041d60f60031170007500504140c0d03500340140000c1c2c81c580d400070004402a1465854401d51800c9110190b200c0502681e03280d038403000c022410001e617007070041d6015080a003440305000d030410610080b1401030b1104803685486142d81820307130050344160009600007084029648a02e2107500550b03e11035507000588890640000c2c121541c183c840050003810001a18208040381c04014050305045c810241940340c50000b60400c4525102010507900c000307a1b2080071510250000350103190b0082c001d1040c1030b12582c0d80f05003035003208030680000d000400881c01c810b00100c1120701503c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 862155359 1250 862154109 862154129
    0xb130302120c100f03110318060711030702060c030904050414071d01030b040c03051608060c09030613060e030f07060506011d06161a091005190e010f0501031b06020106 74
    0x50529001a0b91a004089184d424180c1340d000740e1080030a400c0c001d61007050030104940030301c180c42c1010781c81d201d00246490f05000c00c0300110800400c00000f601d00b6aa8100e48565951401a88280c02c50041d8895560820304140910003007140461075444c0514040d021109000c4d5a6001c1a14a5926041140c68001024014130116448003a883d41c010701801c1c07070114442c1e8070303500c40385842c1c0c54140080c65000902003e002000d8140b202940102500d50720600301040540080e072074100c0680180d40a200003100d25042110f0b40d04022101185032054a4682c8140d19481206600210742121510314242c000b42041d8020020484900074100c0b610f0410a062402e0041561040320300c0750301c07030342c80d00c007520000343c6007c85141c03a4113040814a4050300340700b05800d00d40400211a41c0c0c2c03c81c01c1408100c0da4690280c07004003980103038807000c200c1d09500c0744002d00515154010701401401e01d40040144008a2090001800c2416818403c2c5030744800803400c0303071418000c9440c00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 862156609 1250 862155359 862155379
    0x30b07020a0206120a1803030527030a080711030a0e042901081918020f09040305030a0902010302091f0801050a03030206010308092706041104081e01060b130302120c 73
    0x2290a10110701c1c0c0c045a5a035002504402206c04202c02c00014581140081d44450410076001d030303192003010440d0391000c10301c18420419035145489001e01300c3c0010810030b00d94009211188145120a03801e840c030415179984101e220303001840c0e158210640b1703003e0b0782411000070020b803030180119206a000d500801d060950704d03004544400000d44904041001d210f00c00d851084141b08030118a280032404120740260391040c40265010515824810f5400204100101ea00841165840303500302c000000c1200981c07005800074081d090b4604d0b0821105602041d1041180703021461224085d00c610865aa89404001552205000090058102034010000500c01401412000100038401c0c0c44075454400415113030704044241b1200e0148080504c101401c1c02e105034076082d400d4072a05441c0505142c032643d03541030002c411540301d88000c1580720700381d48e00303503c04009420000da84c4d581c0c5607019410a600d1710741d0760109900c2039aa58607601242003000174052405d100190119042c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 862157859 1250 862156609 862156627
    0x3011d0910150f0f03211209170408030a1d0a050d17120103060e150126060c0c10091a0903090a0902071112060109020d060e010609030b07020a0206 65
    0x1401e200301548054000354440411001c01003d0008040c00e4410030890700307a465030901400c0ca0145813005150784101e2540803644d50341c84244204099814403001c2a081120301e4411403007a6001d00701ca20081021030040360500010008004440e00340da1001040005840a80f0703035100f050055a600c2200b01800f0002400c000380510031240c040c00b0501040000c941e214030160b40041c2280e18a803101303800500412000d48950304030030350100001d00703125122100020300c414041c00b6502042d4220682080d003141e00a6400400c210020191070480c01c2c200018007898000c10b100c010300e402083d8107d200305c50b0911031309107120380200784400c1c0400700012040412074050b00c14006030008000740304050b02c42d440508000d02c01c00b000103a6407003c1d410064502e800041e0000d00c00c40d450450300d15032141c00030f06a81541e14040c00186c3d600ca039588240001c00043d4484020010041c000044881c0c1010b000d908507405800102034980e80d540c4200d840c0c0410b02e400a5018030180400d280e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 862159109 1250 862157859 862157861
    0x1080d0906200709020d06031b12080c0a050a120e01030e060c0708040e0403051312150b030313081507020303130f02010c05031c06060309030203121b0307020303011d0910 75
    0x45071900b41e80c280c528254481c800c074426607001c54000250a03032201e10170001c0004684031403481282c00da540c1c0301c8440c24003841002c2c0019025018000e0100400c411003078240a002c403004c45681316040b502d5200c039601d01190081440720507040170a0001039490000d50003801481c9400d00d118000d05015502c2045040e82d0b40c000350000c1c3e603004410710020a00054520505003d030f40281c0750240c85000700d2a80382c03122100c0f40c0100310400078002d15000000d01100704407459554000000c1030b8100d000010034518080d5000450021095640c0010150408110444070440c40540c24032980c0e80d480060740d40f444103540003141c00b540011003101040c40e50540c68840341c1305141890701d80314580c0f2010300d5030b0400c604041090262001e094091811481250010b00d643e050610601242e510085c1d201d01946600300c030400b010f01c00240010110200c005240c4e0047c004150b00d07410100e00081d540e410901078000d0a4011341d03d99010044031010355442008590018202140c81c000404 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 862160359 1250 862159109 862159157
    0x120f0c0f020c0303310303020f0c040b030a021e13050117190b06184b0402150403050f070509100501030f0f0f140a0203101505190801080d0906 63
    0x1040380c2d040d001d6401c1d0245c4480d940180118000e500070014050085501070800c80101c0c080c901c00d51600d0114612070700c012800c0703410190101e4170540d070b0031204210050300800c51000035900006841d01ca10b0382c0c40c12503001a058076907202c0343c9075009440d0440d05581c1d02601d16501641c012001e10b40b800a41002c600c01c0c1d0000c809400350744a501c5003800c0660406c401c0c4c5182184d4143d070f4504c41100c0035440d0f85e90044e0701c60032000d031255209242c420000120a032132506514845800080c09544a01480903410030740e90409039529540e03810055101e182c08a2030301814091954002081d1070040d4507a4041c02c5200280d1f000303c3c0c50700b80150000c20310f08040070700f03070b036224000401c05103800c0c4203040e40c010025201041182c85407501c0122040e008044200d2148140300384803182c007003207030345c00280d42600d030210140040c5444142c50700d0280321000f41541501405514440e580170172014101da54080c2101c1d01042030441c181d03081d4403203002d05c100150551013410289840d401e0341c6 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 862161609 1250 862160359 862160407
    0x306130213030b070f020a11011d09010b1b0c03100e0c030a080a1106010e0105040b1305071d01050307120f0e031b06060105040f030b07120f0c0f020c0303 68
    0x51401c440350000002000e0150300558002c1010760070400c90540042e13404500030003d1001c1c0c0350301100d903510000c10140c9001d41e0fa04100c41071084407800c2c3e540f060034086002c8024400d80c04c6603550910a1001d501c280512050280c80250400541d100010f0024403810700070090501c1c1c2080c03000e001c000b440340c00f080712110310811101249a460a20110000300d010740074040c1c1d00e4a090801a00b01000140d243c41d10790311080c0100960a0b1309002241502d40c101c40c040303070801e003210007d02c07200410f00000d00b80f0791501043c00a81a0460700c0021041240d040c3c45140b51071180042d45c4900044407210003080c1d203000c200e1030114041d40201c00740e010610000a90184031003070380d86940c00c40010406c010445042140f03c40b41c040203165800b010920301185040d0070810501d102c0500c034400101400741490116200301d000301046030401e800708000300801407103507801101910300006c0e20b20124035081045030000c0d10101300c003020707000042d00440c50324012196030300c40b840c88502c10b = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 862162859 1250 862161609 862161611
    0x403051602042a09030c05190e090c0102070b0f1b031b0309120f0d05070501060b0d090c0f0b0f2107180b070c0b0c01110a050703030605090903030613 66
    0x140010b0340c5902c14090711407000201d0540c043c01509448a2070b44540e0f040704140b12903620104001651300250105460042d202c001250000c0e00d4885405801500150103104c1004200300e210303600010b0302e0713101d00c200764200c40e0700c41d90b00d034524510741c4195000e804180c0b004100903283e11507041c45180c02c1c4111441200c3c07601401c42e10003d80409845064081c90308000b900c14520f15103841c103c00c42c4c8031034401034a13502d18215081642c0d030302d41c11204070501078086203c2090003802c3d4018801003d00e401c81d1662259002c0489009007410902122026500c0b08003249514100700301006a5601e100380d2850200c000c2148500c54000701403040e200c182000300301e0110f541d0b081e280e034040ca03290b45480d118652240501940050a0742011682030740900c0302c0710110781d40b564a035048480031000c20b42d0300c5015404c0e45000d407400c59920702c40c01e0b0001901d01e075160b0b80440207184160003a13800300003080e2103800f04195000c0644504035140e0050010031017502d814800c5030b1107482003240c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 862164109 1250 862162859 862162897
    0x90d0201180801021305030d2003071a07030c0f0503010611070503010c0507050d050a0c080d14040507150c050a020f270f010806060108040b06010e03160611030c0303040305 76
    0x280d1121141294002440907500480c4010301c03580c8807000c4c203001c1c02084000c4d0000c07403011140140100d81e02590202d44856601c14800c8008090084400701900100c1ca21103140603332550396120343c0306442150001c0d11748101e00300110b125031a002c070150803daa40c249103918204085070128003c0c10a030360103006844000a031650700344145030103041141c0b03600ea02d0741c0481c1440c500f00312040d00e120040c0482004043d845540c05200c010000d6071020803540c9516030340e00f40500038061000c1c004060f217490b80a000c01e101c40002c00c00b04441c0300090b4038003c1c0c419030400f11040c5c4400c4134014090307803200b03821000500e4500031132102e100d4050209099404000b40740040c04204c00c2c0551031700c40b500c070f05011541c503116840501420003440240283e0a000000902c040d00060010f084407803084040740040c0e100e2250010030a0f00101200c0108104031500541c641c005c0c81000003085112120100204020056401c00c50050000d18210fa40f00c2e20180c40581c001c1c0024890000100 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 862165359 1250 862164109 862164137
    0x30801032a080c0f060f04050d0804031515091e020c010e0604030c020a0b090d060e010e0111040e0708070804030e010519020a42020c0a050a0302120f090d0201 70
    0x404080050004800810300f04a004007807109080348201c030180200030400c448842400c108045a0484a06450841200307074a410511402c2c015234000a0652801074900070f0985580d0300003071821188041004551a601c201034400c80304820b4030742c0442800f100669801d184c4a074013038001144c07254001306503010461501400c203c0204e4048000c03403d030b9640350055040024610020740744921005140c80b070500e000880e00d80d0120300040120340c81e10800d03140d600342900614401ea42c3e0100030311a84440143d440b01d1078006004420150354460009004036114888050098a494503a6481c1c0d0712140c0b000c907564079940340400d0500c1820084c43c013243c104001c403c4407025180d4098441cae42c00c180b030721188240b0004a00e0a07600c105044052940c0038440303005201c054181d905091201e5100d13004006402405200d00c6540a0b0a80076410702c8400304a01e14000d11a0b402c1d900309403601c842099450240c180d100d03200344001d0001c8071280c140180c0c1c4200c0b090050404a211a00d46 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 862166609 1250 862165359 862165433
    0xc242a0e0d060e06251e02251d151311040303030c12061a091809060403080a05070f031d0604060b04110c0d0f050c060405010506120102030403080103 66
    0x50083d481c5a003c0d8041280d40b0354024108041c4c10621403030408460803031940100031765a40c1e102d0003503000c4032507007003420203008011120310208207031245113203500100d1105030000c1d582c0c418507091940c80800b10040220f102803031071240c0d01d55031030084442c9003401441601154200306050485d91130311343d80001c00c001805400110b10aa90201c3c000c00e200500501c1c82d0441104003000c0d40c2451702c14088d800c0b0156901701014050211303031b6225031b40c190000d1003d406806008960030020014003142620118510340314600a0302da80c021a211141e00c0030842d07404481100000b000c45403101c2c0442d11a8000304031201144950780424494001c550f410010305450460306a40e0395450307504141000d0040c07032010480f01003020304003c4481c444a4503218090380000400100b181400e0106026106a42c5610142c01c100c420b1450035140ca075000348019070311184a20f00c0c5031038101b008041402100d02c1a541551a90302e540d180d40c7d15031010030a60001138407080b9005106440503060 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 862167859 1250 862166609 862166621
    0x8240a03150203040c080105040b0414150903070b0906130b06060903100f05060d021e04020403050a060c08060d02060d09020102030d090c03021908061302010c242a0e0d06 75
    0x2030040e035070f051034607116244a40b1781c2d1004100c0e0341841d0400c400300d040c02c880c0b01d620a8000747d1600c0b14100000d500c500304280c030320b00043c56a9000781404101c410001c0a4421903110312126240354a56280d0b9a5851074126440ca40c22028074449600094101c60100d421060203403000f0304201010b0006403e012030340d01440300d259034604070254980d95501074950010f00944e407200c0045403d80109003980e05042024103403801d20991441c184e25180e040350015a045019942800160302e0900080c0203108a0000041e11800201e0400e280004814102a41c01080e9500d445180409003000e41402c0805a056000510410761104058046c4c2c0c909188100c207400ca400d0309510401c64554807405d4450340b03030000c07540c050200e954000b505a0300000640c450100c480c10520040728000c0c50044020000401c0d00c0d000c282200c0c402000059140d0501010b025400c501c04400c6844003410500c2403003041c4c1408441c46043c00745019151110014000100d07150f0380c0e4803440d080e520 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 862169109 1250 862167859 862167893
    0x4082e02132c01140306010902090607030e18090f0c041a0f0406031e0611070803240d080a0e010e0105190c051917030f0c1b151608240a03 61
    0x6601d044c540f814501130100a003d40040d03d81141040c1c40710000c50b80a029020b802028040d4544200b1040c0e40c80c851068000150180d652209190003010180c0381d601801ca00c50340c903c02d9607410b000c1840c041c018200f05003403002c141010300c01e10004002c8105a030707902546d080b5580d0a804004201200e1000c02e190703040d03000744041c150903840c4c01e400320340c030b2009014103020003400342c80006440441260f8000300042240c007030316024071203061020a02102d88641c00203114207220108184030001c1d00720142ca945030340d001488240015520754a41c041924001f4904026134080c109501c42e01c60750825803880c02200c290119607407140341800044a11405110400d020000c2004100304124078210105540382581003103003840015100150141c10300c0a0046013150b8840701d081320700c06006140f00d0031603034920403014240300c02200c1506c0200502030108030b00001a405a00800e01510080210701c00500701101e209586c0c0c1c2d00c0c402080d032b21160700c0c0e81c000702040c10041003100c104 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 862170359 1250 862169109 862169129
    0x1140a111b011403010f091d030d060504060803031017030d0f0b09060d050601050103090204110304030e03120c03030a0f0204031703061305161404082e02132c01 71
    0x5144001504003003010395680700300f480810042c400c4140e000708050031540c06040c0880d84408041400e10440b1134030030303c1102d900c004034200d0700c002541d401c80411102c0a407000c1000c5900c2d24900c545a21045411b40f443c5c000802c1c1c10021004049119818200c295047c2c90400c40012645801d0b1511404140515a11088014114a01440b4054110702c0460315100903130150f0ba0341390b8440d41c05200e81c3e03040c10380d960000010740d213840c0c105030395039184a1107150b928680340c41d015048030307140307550f5a000c1d200da0042150740000348400c45440b00c151f00d00840c195a2164500302c05044090401c2d400c160b000d100010002d841e0744015203080e071641e034580352a49451020310031040402248041201e040c4820b120003440e540b000003244071003070300d4a003002020300c0c240c8609901c9590721100040c8a031100ca071413007c00c02c0d000112000002c003040c168100000c20240181c2c0502112030161005021b420040001548400703a01c0044403024000c81c804c101c00a03083d004001d0348440c0d224 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 862171609 1250 862170359 862170403
    0x5060402012d0c140102090a0e0a141303020d05090d060b03100c0f030b03070605030f0a091b031712220b190c03050123040e0102070f2001140a11 64
    0x2c10300141c81480794134008000c50811035100001071aa082c1442240c1c058002c070408102c4080868004a4200c0d0011105451505281a80e01e01d41c0f030562a0540050084d0030742c2da82060b00c03c400b116108840200545003844464564100405940c1441036148c480e595018810190754061000030400e80c0d242e480d0800840000603007515848250b45210713400c05201031080f9508801034075000b03866000310041c6a80e036145103c0090216920290014001c0346c41803060802140c0d10000b92449100c003d0b1024800007082d030400c4c000c805400c03e03010320240019506994076544007207146603000030a042088541c036140c403e81d8080c0d51401035164445120a03a0141501640d2810207061070108050343c035010790120303403445140d2a1510f400341c81d0f0b21488599100d4010351070305041134000715641d00b903500c1c111080101d1204200c9001c0e4031485100c43c1c040644c14481510365045c3c503450a0340c1c400e81416200355100c40c0003c418081e444504c1803c03002d08011134a52b50914803a0943c030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 862172859 1250 862171609 862171613
    0x90e031b0c0a0b0301060801060302030919060c0f0804050a1e080309150601230a230a14030c0418021216030f06140d020a0e04060f060b030405060402012d0c 69
    0x2d1180b4540121030081c1e01007004020b519800000b00b0b04407888e500e00181ca0792541d003903550030201c81d10f41c03100400c0e02d507a00e203805224a40d400f64a104205803232300c9029602d640d1003520440001c44015000d50008014030000c16440d080c540d411541e0407907011800c1d07200d50f44002d210b8100381c0da00070555002d41c3c511150740c80f1202c5020f8004000f402c2142188030300000540d00c0c145503600c409581440802c5420b0964060220000390340d00300368043e000760b107901c91100b120341c10a003c0c1000040f4070f0102c4016040f08d410413a03002d02503950b8400e261504007000300420032039514004503202c2d0b0802400c550210a0545580628510002400d840a120b04002d007a550b80721403041036503180090800c8000c40e1403c8003800f00000356049540d240c4030340000748038007400d6440030450229030307070400080008540c0070562803906681c04010b0350f92a0300045c0c4070350004480052159200c0004500998000d4840400c1030100280d44000013219002c0724186441c43d40385540880e99404440c41 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 862174109 1250 862172859 862172869
    0x11412070e0f0913050309100302120a0204030c03030f0e1305041101030c17060a0305151807030b04030305041719030e0c0f06030c0d051302030f06060a090e031b0c 72
    0x9040d54111501ca59030782c000c40005080d070f000602258483c01c0c1c40d882d1001044802d01c19070f8800c0d080148102c0041c4c01007031003d80a54040880b440d0f01a4407071001454180840c400c0d02c0c10350390801c00c0398000c94190355003174034480d1100c81e064051000113551015540d42d48960f4175881d0b000d1031000314241c10140b030580c10100b080c80402d4180750601a020000e00c9d804007002801520210070369000782c0315200420030005040d0000340c075500800c1c0c03040410354540c01480340a681024103d0700b21100d0f000200b42c0300d240600009002c1401e1030301250202e8842e0b00040d4215016810700401c1360210005560264001c035002090060030302e10083c031980d0140f248410404001019095507044000011051401c2090084c400d110110100d6504103243c2e003900d9031811628820031290030500740d01240b809030840700303d121f44035075101194082e001055440c06442c01910009070307141008100c5029044852020410340b009120022020038203042d60300800c1140000340020002c0241805 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 862175359 1250 862174109 862174127
    0x2b02040302190e06010801140d0305070501020a020f0f16120303020903060a050105190f0918050f2a10050c1603150617030d0504060603021306060f0309110f01141207 73
    0x94103000306c0b100100003a2a6008044072070107000c41d07030300740c84441902c0c045d540e0740035000c4054510342c804240c40001a03000580b051403145d00f00220360001c180844c4903950752000414414030501104403c1041c071200c600107039442032080c02c0250601001102003407410104403180b240c4e040d21000108101c4c1441400d4000b94180c0c4000031120905011b14401007000034800d4400c6595200e010307500b0004003a18144603144d01406031000c2410940c5855900c5041c40a03121088100f0000b112018001c170b941c7c207852500140c80185900c00300b04c0162555009051190720302e0085003003000c2d00002c01c20682e0007840c840e101c048080c2c103005440004851860704074070900c4205000340d002d281c00001c1510000b00740402d020510f036449240c514080c00488d03000079004210102030f0086520300390820000c0c4c9849640305408038403140c900b201602c0700804060a0030017900c0021423242829440d00f030b80d240d010705101440f2543c1d0455a51310380e201c86580c50b00500c0030300a100d65030350301200d00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 862176609 1250 862175359 862175371
    0x702040b060f0a031e0b01080402090c1c090209070906020a02010c03140d23060306010b070f0204020a02060708060103050c37020f0706020703030816090801051314032b02040302190e 80
    0x400c40350742c6d11000a047c09074044e0019204072980c4001414596040003100c4800800c00d0246071200d026444542c00b40944401c22841141c0380c500050300030b8407404000045690550007080607510079001900c40d081103400541c06c00c8a00021a00e0260b1031100038001d140c410355000902c210341c02010304401c0ea000d0074803401c3e059102d00f0300c41c00755030008209056030920683c40d5600d0300180350100b40428a038500a41150020039000150307500441d140c0e1203180316480c2c00009a80d0600110212038003121070441c42101440140c9041c01f00c002990343c0007044600b461000d11060301c4c4450302070006039480005078030981910181e440d040c040320340148460700081c90f800d0b040d0759000d40345400051205080c0300704103814840491160954030021f01380000208001d0600e0400100c82402401c015151140200118180040004219500b4210885140b5040c495445440c1c071003407040f8180102c420b80030301020002da5900034403007241c441000345040301c0b54a0404000b800c03403c01091 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 862177859 1250 862176609 862176611
    0x1206010f03140d1e020309040908030106080f100603020714061003150b090606090d0218090c030304240216060305070807020613021210020301090501030b13080702040b060f0a031e 79
    0xf030004541059481d60b02c105809001c1d6100184400100c0ca0350145100069000b401c2258030340c10f01c9540e000540c1a58400d03501c3c1404c4e9074030b15104144110083d2030304c24030107181901c01c0050300e100c0d81c041e00c1c0241c070846039442c404502a14140c40c18805071011203560110301002c208014404001441100b0050400c5c0084d070900000a201000c0c01004c5c240038101c001010340d841d9803114a018400d0394014110082100103c401d5096200200c443c0da0891060707005100443c6800000c0e102120900701b404070030702260100201040301c01b440404c040d0320402c10613000007060540840702074417055900051629003802c0c01009840045e00034000c2d9004030f02400051b10b00d4070b0281c0362140d01a6503030308103480800780451400314106260b0071040e1001c400031801c2803898004038100c0e4040d030b49841c0070f80c680c020025451b451198004041c06400c10120b030040c102070b004002500d00042600307051021082c1e261405600050208000907039a042c2c001000580741e140020010384000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 862179109 1250 862177859 862177873
    0x9100914010e1e1501030608011503021905060306040e010e15040b1311010c080c010903020f0f12040e0c0f0a0f180f0303080a0b030a0b010317091005091206010f0314 73
    0x45080d0b01d603c4080d05190400d8801e400300011039000e40c1200c0b00a2032284000c000c101c0c400f207200c0340d0150060204034409c9200092200c01549181265010760b4001400c1900e0341d1100c0d01000001c00148184500030b540b0b802c45818030020a00521209410340c0e40900964941071a00f580440e00042420100f200d011260401254564458607280e081c28200700f045148035040c0640c0a0207241c0244081b903007007034800010545c3c04038840600400300e03c100c52030035041400315600c0f80300d4030001811800b000c0c003042259400c60300c0c09a070000c41c1c1c005c0d55403401031900700c00001907001c070640a0101d42034103030503580c803a4051951002c415146000b400854108a0711003011034852001804100c0000d0100c2c15000d005c0d8041009003038001d0844019086503d8180500102488240d454008034501514912000011218405001843c08681440445003a505030304403451003a00165400c942c8000b00c0742c100f0105010f064400d843d20f8203245149000803490b480492070300c2e40303604020 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 862180359 1250 862179109 862179151
    0x50705040f050d0b0a0c0306170c091b03040206220b041409010315090c0e010905181c050304030c0c0e1006050c070510110703111507050c09100914010e 67
    0x4803885d08104920f0012903c04e42ca958220003400342030f000100003200a140c1d000c41014009180708414006581d01c904940e01c65540c96003605c1e0000448039208802c000040052800b180145020051401d00010303071500e00010480120042c0c00c20394043e48002820b11409200c0000403039050001c581100c195030541d5101d444149400c0084400c440d10b92210008000180003804080d0446d0010310f02d15603903d80e045000b406080da2035007143c031a102ca480b558201301203603140303100706030000f051408420000121100e130310041c4158200242ca05800b000100490700307180c014040394000708880d0030f02c0141c4c0e41070400c07a0340c0901c00380001002000074442c00842d0440880d0821980180040c00109090b110050342c04c3d15800f0700d010b000408410840340e02440c110244042e40c2141ca54a08644201c03010b06c600d07000600640d00107401d0640d1072402c020244c2d031051440c00c07a80d4002d50f071121480e0694098403003110304405040018410a800c111000354000030441705900101801 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 862181609 1250 862180359 862180373
    0x20703021b040204030519020a080a1205251b121109041e060203070212120f071809050114040203040f032601090b0f09100e1504050705040f050d 64
    0x44440481c400d200c0ca0303044295510350781954011600074082d10004040030120122644039040200d2189040340700108003680001803400900c0e40c425601c5100030b06520042e01c1c0380c6c100042c80013812890b200421020003203200c0c11164248581440d4050818101d40488641c3c499000b0703050030362105400c5408a481c071415010441815501000261224148000305000501b031340020146521044000c00c10141d005500c11510f070fa00f41c50084010350080c2606110b09100d0940000020b4080f4615481e410503198020070181409404c0c42c1240721082c5c02c200c00782d8040408030b40d039507004004071494418200480b0304200e808615514041d55078000c4611205000340c20008400303003602802400d419002059042d42055480303d694820151003e040540c119502072008020486081c0c02c0420026002c0d00a00c80d002e5000c5040c804403071841d94004215170369180302c01d440c0b0710381a201c6200d014010795131655502d40c0c1d1801c102405c240d6102d1503201030300641140110401003100 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 862182859 1250 862181609 862181623
    0x306010e011d0607211b030818160927142e0b03061618091a01300c1110020d240311030321010f080102070302 49
    0x2428094034030302a208202c000c4440d5200000d400800008600741072050f1114400680c0c6091302c0310441040182208072820108040081c03821160b148400c00020b00481e4496406007409003091b1007180401c0a05107010402000d43c0d00b10f01e0503040c01d01511426000380080040d01d010340e1448031044079a40c01403909031605c0503088029641c070b5602040d034144132008503c880580c1d10341094042c43e070354241001541044110071450159205e50a04001c100700348950001103202008248040c803d40d0440b464500025118131446c60218003540d1522171240426903800c030360700c507982c0304d200050310001101c40103404500034a844240c40303110b24010348426540c20b21000c210824900300546410150f0340c6030010600860182d00381e00060365020b04519041814103201080c608480050203104007000a03d900040c501c0a1022414003456444034003000f5044900d4000c404594005510014000e603aa0b60086001000158041248039002d469124000c40c0340982c90350380a0b640741c01c = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 862184109 1250 862182859 862182887
    0x40314210d23010504021e0c013e1e131518150905040e060906061203070b07020c061201060f0306061e140403081e04050904110418150e03030601 64
    0x1800244002195006100044046515000080e1101e40038000280a0490840c401010b020a503800c00005170ac0a01c0c010706d80b01107041d201c90a080c62804502c210350003901d06080803010000d601d031002864000402c0395910101010314cc007828035442e2111084020300c09010440800c0d00c102d10307060003140b01c03c1102d105100e2110b111004c64010b032a01c0c00c16a0180b0703805841e0220b603d000c1c80c00801e045120700100020346d0b01e20750301c040030840e40300300f00c112078422580140001c400190081c0c480c40d4015606e03004039100b8070450400951554031407146940060304843c010054190020560034003295941824400142854402407215041480d01084000c17a501040c802c1c40c003800503e0007d05074180300301d0341c0356180d05180c80980d2081c041540150b41c84a195068001d000b01658151000100203204503203503038681d42c640c0e00b000791a40d0741c8503640340c1d2001440e118020307840c2e1019218800e04c016441d000c2043d03000715080c07012800c0441d0820002c00c60b00c0d80c6d002e107451103495 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 862185359 1250 862184109 862184111
    0x4050c030105280b0d0c08012702070206040906150212160303090c1707080c31151401020613031b05280c06050f040314210d23010504 59
    0xa0814200e6241c1c1d491a0b201c1115000b0005c0c00c03403c2002130350850070340c05e95951101c41c5240d03660900090118482c42201c210103100445803420300205400a10106d40001e00403802c140e2148202011944164048580f210f180008400483d4051144074001010586940e0420f845841e4010041c1e112080003800c26503186004001c01a001020790054090300c6250055a6499400c0580d143c0306401615040e115015151007507241c110041c15007a0720b20003030300101c0001c4013064000b0500040c207091079182c46408896101506c40020b20042607001010045142d0190003e8203151014080f2083ca2110100703002c0801c1e0130441450007500c4221004948800074100f09050091203051030041790500c60588494000e580901c0340407500864104002e1a6600b0058810f0702c2512540c1071015005d01080011a5043c00001494070900d003c0d03544000d102c0740020310086202c2445410b41d000400d1025a010309072196043e1111000c44111070051a01400c0e255050148603a134815 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 862186609 1250 862185359 862185409
    0x6050304030c06091e03080601030b0d02030715021c0207050120060415020904020d051e010e0c070c030506070c1103010209060d0c1b0b0403140f0a0e01030e0313030204050c030105 79
    0x8200450808000c400390155080b90700b041d0321b070050181e80c06507420303400241851080d1019152408a030f04507503500034003e010381480c01c2261921089480c0ca60b8056001c3e032071103d17030000e4817152070140801e220340c0640052030078503001510a62400c8291f80d24180c0020303c280c400d480000346d003500903820070942c2a0f01642c0c04480e80c00f9100381c115294000b400410580309190660b00700328020720b5910604241011042c07151421200300b4032910383d22441c4070010880b440c8283c00141500350241030030359885516500e55503d0000107442560004401115440500c600342c0e0f4801140300080f0000c0d4940031007080010080c0c0202500b40042c0e0390782d00030ba14003142c0960303018840303400000c032031502d0404181440c0a0b1901c00325001e9001c00c00c0a181081030840403011200000000d4890303a0801d400140115100d002d08209141030641d07d8200e4035000c0000c0020388003000301410100031007070841c4148010394402400360328080030b042c00180b2403541c41000100042140302c1d850307404 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 862187859 1250 862186609 862186613
    0x30302190312151e18020c07061d15030609090c03100506040e0d09140a0303090303080a090b0c2d0304080f09090106051b3903100c0906050304030c0609 67
    0x24100c03840d80304803a0011500ca288213514400d0702c02d901240d410240291500303610718140c00991090480038a00c03070704003070818072005006220150117424100c40e0081c0700880d08003c6154000308141190144001208111107880c1080c04a0b921641c0300000d04100d00810002c250354850700300081d040b4584840002c1d1082c0c550354409030801030300b90204ca0006078900c03005098000c15020f20310405030662400e450314100080030000300ca6159031802e200320300e10303101100c0016014020301011910780c0860b502054052152600916003060103690301c00d520400b0b0030700c400c2c0c04c00a00020342000b1148451200c11601030b01c1d80140c100011981e921441d405500c124030072141e01c268407039a00000803809651010281c004c02c040722405100040710b012806541e82c1090201c0031010126030b040d40403e2101c0041072501043d1042c0c960240d030003010019040c81105446a102c0690320320b188070030070f0340c04034120000b0710076800c0492842c02c0503180108803440d00b49010305a41e0f142e24030241 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 862189109 1250 862187859 862187891
    0xf1506040c14030a0b0f040612021806060304060c050c07080105012c060103360b0109090f03030e010216050c10050c191415040501060504020427060803040e01030302190312 76
    0x6520319004104003c05e94035420303072710040c0c0d40780d49042e40102c407001d9140d04c13003094006195000d03650062640d42035650326502c800c09030204010310301c2084000d0005034040300c000c01004010b0401c0000100b115030400300520055488100d50303070304c0051500004d103110910342140c5d64000500b8a804102ea10917081c40021001410285020340e03030460695610300c024000007242031501c2440600c0c0c80c0d90361070081078160381305050041c0c07080400041480020f030007540b065105118a070005410802c260b10700041032a40b143c0203590301e030059180c242d820300d000c039466480d82001c1d003445404c0c14404411241d80b03040c91211500c103402c0c62040b40b0140034404041d41c0d40800c0d03e0b0100c0342e0008800901d481030305410b840440c1d540d8200b50b804101440c15000b620140c1c2c0514500c44501d1501c50140055028092031105000d503507002c0c0072070200c8042c4010005400380365403a644951440c0303002441c046001068031086486040c1c4e03200026840355100048508026000c6130585084010034 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 862190359 1250 862189109 862189129
    0x9192c090d090e060a0518060f06040503060a0b1309030309050c0306070941330906040b0c160e0f06130b0a12031b0804170f1506040c14030a0b 63
    0x6540700d80e0101f10f401520007404103507446000705035003007071202700d0490600c10340d4007450041c594590000340029528922039400040c210400802144601800315401d0b002c44040f0101a40000c1d00e4450000500c202040b04504284098004040516119400800041c4540125208440d140050060450300343c200e11110072400d401104600c17000581e0742c0c5000c1d8009200318028440d02c50001c0c200800c184049403620304040000800c1c60110007900c54581c000f042880d84124240408940c2a2210007d020b0b090540402044030750001c1101d0403000c045580f00d44590a240e07400c00c040701259101d840c0c1c100340c00351404040c1c0f4104103030a0014040010340640c1104d003038400003034940c0c21551a0521039001c1c0d01e03283d500707042d036410001c5162007280000c2c03c03585040108002c2c1440440307603a0400c602040640d0711000e1007844050500c21101d29405030001c0c0c05052210a1400d80700e5002c2d60642d504000c00f1a01484c400c005090200403c004440c0303640c2d22010246455000140c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 862191609 1250 862190359 862190369
    0x21020309031506090702060c0d0e0a050106030308060114040302010215040609120f1d030309062503051c0b130527010905160b09192c090d090e060a 65
    0x1980c0740c0e48000e000b60000810465a2611070b030b41d13080108144a001088050041c071410410714079040a490300340002d0300e201c100e500e416101e04d03101000820428400e0744080e620a0307413603141a081c844001010b071407a143c24130f4020501044108010b0b80c000401607041d241c05840c2507465503860400b00300034072417010040e16002c160104400341c0d55210340c00030b5250b2800c2d01c50f1120401d81582c1c1c641840c81e950f002da9010b1340f082044105500c2c2c90750142032080103c180300010700c0c801c02068095042000d1046001c5000810307004842c9488000762075004140500412500164400184001032528111a126592040803d1302014010000340007080d0100c4820054080c40c600c2600131714000c2c00980c1c89000d030540300c20071107480610000845a0a62956080804403000c0001042d14000076040e60301203034600103162151645241c4680840007215072100600f000780301c80901008041d8503d6401074001036030440c0d00002414262400c030041115a5039500c0301081c22907500b9042 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 862192859 1250 862191609 862191613
    0x150302060c0c100c1707081b03040603061403060a09170403030e040605030c0105040303080703021611010806030c2101140907090b030705010c1e081909050d2102030903 74
    0x21403920000c000811607102c0e4400d4960000180316044100c601c040316400080441c540c6444803010141d03110003501d18180141c00c03151a01003480c0e58050f403600a110a1901504049400c00405801d44900d1000388180140543e10943c01030020703403944801070440004a59480c4040c040c00000c11800ba202000c564080c0d980d50303183d003400740101e001c040c00075208500727010f1b020446050100e4140e40012040e150706041506568003aa1020b400030106002c03d076003032008001941643d401c8000c82030081040000c444205c80006204200045c90b06009502002c8242d00c680c03030b0004001c4460350b4a11004808202d6020641d0141865001110810115000b1b11450280200c0c907182154401001000150154024161aa03205200d5503000c1400204d440700420032586902601c40c0c0041c5404051590a9441c208180c00007450354586103940900c14074035940082100e4007801081b29500845480740ea81c82030503c104100d00c10410701d5520284608500030003e40300c030300c440142 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 862194109 1250 862192859 862192867
    0xb0c0c0709050a0b091e0c03090a0b0c0c0105161b02010e030706110d21180c150909090203031e071406070f031b18050301060b0307020105010f0e010915030206 70
    0x843d0140100b03501d25071042d4203200100b4100815256200011444845040d01c2036a40382109002600b0040c00c001250080c100307002e000a110b482c0580c4114032160b941d07030f00d400382411100d003107038002849204400740ea0f403812041c5031b820006d809641040741000c1100544c161004a62103803528071050b805105400001c1402c03500011208010346203842111519000a0011219490b110045a0030480ca50340640d00324095904100c0d500086c10004080d9000b41d50342d03101800e0030540c8044085424035038418103095102d00c100d0020000034609201d101c07000e400107a02ca1152a9003801243e19503402140701220071411799410315000b56890310a03124845d4034648840048421000144461500d520914001d225949094102c803401d810460b103000425030ba510f6889a04106c40211034100291540d024001c800260051500c02512400c0c0b40c0c9029080d5201a0013502582451400c10302c40d0440d00c81c0c0c3d207070441e1070200b000b00b40030340c0750000ca21409580360070194000d04005 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 862195359 1250 862194109 862194121
    0x6050702061b0a0c21030b0d110607230a1209060203160302070807060e010210020301120b040606090e0a06050112080f0a0926160513090516030c0e0609040b0c0c070905 74
    0x10440304101c420385e01c01307000c0d0041f00c2c0100a6540c6d01e00c400240440b0b10710310314998a040140203840c0e07180c800d05040d8a114941d2035030b000707812580355210041d5480710340f1307040c01c0203050038034181c030440c0d503042c007051150a25402a45038011000b01d07514580404c2c299206040c03003042103100406c1d41d05c0031b5441a90320f46500402c9420b26000490152043e0700c10303070b4140c540030300c2140d04840cad4842c01e1600000e040ea40c1d003452440050030580740c0300d440300f034003003141440b91041d03916a00f1a00014806000c803440c080d420b840050b803144102e1529440e0b01d40103e180d010480307900c80038080c0c200307941c0c80b45441c0030380b080c5400b900b0180c080d00300d001803660120103080c941f2580105103011100703001d006810311004c081c1e031409040d0308441580c003065641c88850b04001241489041500c3c0289414980b1540340401076005440054201108000440500b482e4a421102c1507490340c10720f1410781c03104401c8540190604d980d400c400140c5190540d820712040c40600705401090001c0d04000f = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 862196609 1250 862195359 862195403
    0x16111c030305010b03281118090108010902061c060b0d0207030201200d020d02091801030b1501020a0b190c081005011b0828050706050702061b0a0c 65
    0x21104801103460301c4000b01c1c00d10211000d0b01c0c0700d02000d00006003a50044803070038400d00d00c1114400d408641740c16070341c8501d424000103009008881058000507070588010000a00e8040e4000805640b400070040e0250f140d0303804441181104104900d0005110740c2250010860b03030340f200105040100d44501d20400340d40090800b0342c02a4028400c040301c0c1c4540c42c070359000f0a1900c03072022408000590301482660060201d00c501c0c41c0006041c070803030f03034046040003113446406101061f01c00c3c0140304000d400100c142c0c0001ea442030700006104a82d002039a182a0403c1c0035004250810000d520005010288a0118590b01003804104000c0070081c100709003c0c3c507440d803003181000d0041a1544a1201805a0188607013450050849500d5070070a50b400019240f0b807003003000301c0014481040d200785074800c1c18103603101c0760b0312502810200d04880000e0480421500080140300141b000741e0700804050900e1408541d076010741d0305042d100041d0302c81004000c00300440301c4003210390b00 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 862197859 1250 862196609 862196659
    0xc080708030c490e060108030d320411041a0102120703080a0209040e1605030706032c160602150601020601060f080601050403020406030b06120d051611 67
    0x1000c0120001507100c1e4180000e01c103000806142c2e04035401c0a641100d0983d444030486021107101c00042c44100c02c00c1a900742502600f10044070ba00000e00310798222641d110f94140c241d07621142e210306150815210704d4600d0b0030381c80390303244410b0103012400380301c100c0c3ea5800d48961300070800c0291a076482c0540c0110405401d40c00c0c0075026240084900d1402c0030100d9035000e89c136545408103503450191950094001c0e4500940141c1d035802c3c40000300004002d08100441803401010300315140004040c6444c445420680400d400c10341c404955002040710b42c10107043c10b4240c0c980320221800304610302088804031448804103035000049a030f4010030040c801d0703411601040c800303580e64801666545400c0c0324810014540e1144140c4c1c2d548581c40c501c2e08401c051500c9840e203952500000c060b1101c0c2d801c250b56560820080c40320b18a0b0054560207040000300141181c032100d9840070305a801802c0320440c0340e9800480b00400c011400041d82c0507108014035001200c071803010b01c1c84101070 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 862199109 1250 862197859 862197877
    0x309030f0a030b062d0a0c080c190506091c0c020d151503020f09040f02010f020f07060906030b040903051c091712070201060f1511060f0702071d01060c080708030c 72
    0x34400c0d117030144030200011601c3c0d40d5240c0d00d44001c0842e09985815055104003100c90345405181100784144920081c61480b15010300002d020300c0c10300d006500e04040070a11150144143e9041640300160849440314480c6d40444841c0041e45407410400343c10000d00e00e115001d40d180507a04c41910500d11500300550340259007100d1410b00e100103202d500d800075107001c1c00c01002124603400542c800c1140700e07080c156606c15905103c00c481a424034214403034100c007003c144555406d010305170789441403c1085c01c04540602c454811071300c0103006845003402828059015048030301c03006440c0c0c0c0001040b01da01404403210044081420001900680301d5995161402004038540c4d610500030340f0700303a8240b21922074460340740642b103601aa008203080d5040c804c0506c009118008180801803003544180f582e0005d0307213000070000741400d400340c000c103240410032035040084e00d0094100b181074400504040d0004039850a1144082c06113010040150100004004081c1c0c12034021b0b2814070 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 862200359 1250 862199109 862199167
    0x71112040906060c02090a090c18091118040b0c072a05010816230a0c12090b03130215070501060f091b18090c0c0212030309030f0a030b06 61
    0xc2c0c407103c0407200401080c03400703540714001c48040794800c0410f912096041d44110f5102d80c280e9500c41114900d041c10f80150580240d50b071010b4401e12101d169942c0e801a802c4810203039100856010508c1c100021740054041c040a90008540701032020403644100d400044111030000f404072001403401d03075285003010460071910009007550040319024003512070042c420039120840c1104641700350170303008020952240c182c0314680c06650721004200c0c1800c5a55a80c2080d0320b241000960031141c000000d0400ca950741040055000c0b0307500742c80d0001400c0300401c000c0011800014000d0220058003001800c000134920100b100550001e0100e824008843c612a0b03a550440300860b40c0c0d0601d141d11803042ea2064500c0360348034900028100340d981403101000c82c1c0350001001141c903d010403a0206800e2a4424198540054080030400044008514620300764400030f803240558682c1d0107100c0000f00e400304000d0f001b900841d0111720060542d640300d140301c44004404681c10319a40c8020 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 862201609 1250 862200359 862200371
    0x20030706060f1203090b030606040b0f1e0901021e0708010e0d110c011b0c090c030c1404031110230301031b0b0913060e130210020a0f03080711120409 66
    0x4806084054182513405848280080c1e1408a43c88840c0d8002402698841010030001c90000c4c0e030700001d499446145039101c0e440d04503400100b544001c0f88107003990b07900d405015010403030b03a0001d684400010000c003550341490f0200c18142c40c08469400c5502d0035400e2000c0c07500ba008000985440e403c2981d41c8003e601c100e4070042d030b9101d1003841340d4107000030101140c200b03c2e42da0403440d03081081d1281c214140e8081d070b241710b0f081c12280708541c44000039031a50443c200c4564410f500440802400c02070300e162501d10b42e900e202c0c40401482d10307030003800000107020500c1e0041a010301c40018140c0c5d080d200342112a5001081da1090208444601582d041c0c801c1581c1400c039000c060301d0712180781901c2d041560b0b0402003013440c108401020262100e0f070101702a16569000b0f03000b041c00d581a21180d0a0b1031040004260b40404524215840707010804089016410602500c6415060850303c90300c4036031003283d100d8070107401034500b40300e501243d600c001001c0000b032080b9070108a08201c1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 862202859 1250 862201609 862201619
    0x2121b0714011205091c02011b08150904050f061501080a0213050f0307050a030501050618040b01051e210d030e1002160b010b0c0c06120720030706060f 67
    0x74803012000c1c0c0300d00045080b500c45400c41d4180c3d100300d800000e800e007280d00050b00c01174858215141241d50b400141d448808001c4003041c0742c0802c1f9025085414801c100d0b01e410b00c20b242c489254540d11521a0001c10007180c1405024808141004090010f694441c0340c154400901039203050b00c068001003d00d00002c194110030b100344e4900341000907480442030302d84007c00a000c8010b04465a040c011404002056500c05084100a61089001080501c0c0c44810004140c0710580419214910b0a080000140c643c40055042d40d80c119111400001c1e0070041490281c0404030f0030b5081a80c10b8451500b8070f41514062041103018000c880c0414601d802c100c050f140c90075502412588204641c680e01c1489402a00c292103125415602000365034803010a4001c00fa80600c0302c0400000d4060a801414002036100304402c4d1140d6142c80d401c0e012040c00c061000740fa500411606d526452495800b8143d00140489044206c9444000d1420000024012446072251000b080240010 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 862204109 1250 862202859 862202879
    0xc03050d031109010c03020708071e081203070324081e01020a17060607060c081b0906091309060507020c030f01050705031b04050a0314211902121b07 66
    0x100b6800a0303030805040000f03040065034213110310a4100c0a600030700c0c8010070208800c02c14040241320100d1001440e103c1901c0c0c0305146c40458000e0140d50304294812070701458070000f144d400c64024500092010b0070011500c29161102407455000c4032455000207181000050240106031006081c201e14003200d00118203d00c6411500c102045016859031012000001040c0d400702028008501d8000980d032003404550030008200080b845500c1486111031a82d090300c40c450f0402156249411301c410002081c80c010f00b03400ca4422481400a401510303101d4000c07015080d0b000700305100368200400040e480d00c151015840c003078400d408002c1c4244505004043c05035503a9125545103480f0861440c8103485083c4410410760420400011a0780b00d0200c0301004500a1840c842e001004910741c6091809860305108004418800d03050440d004408480c0c11455080d54004522617085059042c12035a03c04204090000305051641c124110081001054580b00303450000383c40d0b4003014 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 862205359 1250 862204109 862204121
    0x31b0904090c051c05100c0c0804123804030e040c0201050618060f0f0d1709010f1706010e0a0503011e060608010303081518090706090f03080f180604030c03050d03 72
    0x240032540440340031b054502d800da2101c28620114a8001074481190b2228415548140d2004805100e5402d0803c248640c0211032042555200400000600706d400803810340344104602c8034810500e1004279082500440701c4d034105942c041c0003031254030510100a4020481114680c0c0100507680401079044c0d5007068603841071a000f8040101c0c210040148400000101407090f000039184107001c0104400510b4010b2048451015550b2140404001001c81d041c00e80d401e428401802d9030f0500c0c101510381d04c0c0d503103c2003c0c6003015494521301e00207054204942d100c0d03900f65203404600020720b001c8804902c0d0820b002001400381c56a262001c0318241e009200c040c002640c0000426038401201c046119540b50040c00c42110b02140c401d4800c0090003950f0496081c1e00001c0c04221994110000f04010706117620f00e850081d185444180052041e401441a04000003e07158016180481540300000700074101d00e44813034480c50010301510403800165950700c80c1c500d0f000a50f5100340240 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 862206609 1250 862205359 862205363
    0x90705060903031204020a0308181503010302031507030618020306040b0f10140909010909060509060c0a03110d0606021b1005391e0c0303031b0904090c051c 69
    0x851900b00181307005180d4190140040381c0c02008007400002080c280307006055103041556070f402e007078a600010803250140880031441220420301c010405aa00401d0602d000c5680304842581e03544c40e510210b0040003660041d00140e891b840d000c894801c40340d4095440740c1d80a95080280d5036400c0100039605110081495000d20004000c0350100c1c841c105102c0d5201c1c410003d542444203485c000344070310000b60030150321a959611004103000b598003c0c07503040b440d8030001d82594101400c0211051007400c50300c0c802d00d0f8a44100220004441d030854030444584c034000c02500d0340b034180082d120a191f040f12003105031440060102850b1412030311200840c16103e540c600280050000c00030f80c80c0c040442d2041c01081d10509a0b0042e00040000c0001b4081c064290130041100051114403c907201340001d900a10022045407400012650330800b0004140c2e0b0301c08440602003203511901100503081800c000d44a001c00c01c03032082c01d07000d55208031081d00401d60030041c1e4a021110101700 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 862207859 1250 862206609 862206613
    0x80a020a0f080c01050c0c1021061a0f12040b06120303010b0901030b030307050114180309030604060e0f0a0803240a0302011101060302220c05190e01170a05090705060903 75
    0x440c0c81e56006000400020b0b607406c06540c402c078101c500213144000f00180302e0303000c900c48164079040902082ca21030040510741c4020041c140c10011401e0f52402100c001c0c0c0203080c1c1c0007941d00358407041c42081e5151031041a600140d145010301e0201100041075420a015040501d48200302c2c54000c0152416209212119414460410011000707881e1052201c1e815010810204010801c00e000703440b040e5035180606021800d04840c007521086d629050801d43d070300140202c0c01ea40c0d030086002070b0020380144011840e0141c21483c0c5080501014102c2c8252151000c03c40800c0350290103903100d41d03c14400e01c0d1035090081c0120340400700c0c0d0001d255010604070320030701c01076003e004401d4150028200020b40240c42c0c4c0d001c9100c04400643d0301d184600e640c8004071303c840a234040c41d0181035007403820b01d0400d03400c4845500140800d8001c0d03000e2001e003d5403d074131030344142501031488058000d5201c582c20203185020041400f42c0f0404800d00484801203058180501211081071010340 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 862209109 1250 862207859 862207873
    0x2040c02030c1921020105070e0d03050711040e0304030605240f0103050a2702100e09191e05072a0818062106010305060a03060506011701080a020a0f08 67
    0x5078404941d01c181c07000702c0326110aa4450a061041d6441e10340013031000703400000346801c0025002d400d44040c0c03c0500e1080700103040440001e544201542c3d10550b203c41c0446061046600040180000796420210361102080010500c12180c0101d405000e010030000c0b01c855962081402e80e5042c441c415410960313203102e480095100b544451b510810510f4000b805400d001c41c0002c4e816445486c0720f004012180c1c0c41000c0d4504070b02800807910300760805548003400c0e40013080c000075006110901d00d001c00381c40284000019004000f4410300c2c120140d1210840b8803c2d900182800c2c0c0341d22002400c900000042c803c2d81c40c1d2405071000103142c00d019001c400765164006540300c09001146508076030340404203901c0f10009042c00da680e5050304218150440c43e0540d074007400400c0141010308003418000d89848004180040d80c0d0051000705043c1c1c1c801d0016100007503100000c5580c109442e00000722820b0105500c6102442290001140b5076103880b00000390005005030340198200c42 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 862210359 1250 862209109 862209133
    0x3040602040911071a0f1f0f06020c0a09020c060103120201020c01020a1706010f0219021f050703021506010f141317070801021c1808070303060e0109020c07090b0f03100902040c02030c 81
    0x1005402501c02101800c11995101d40c3c000c8030b600230340d51050000d6880210301c0780d014a03200300030308040c00502c136003181441000c040070350b0b42c1c032411300c03000d0941d82c201d50030000c00500c00c0d01100c0007084800000d540e191020b5400a02000d807200d1902d503039005a4001c03912a40c41a4a19640b1251303076030043c09142200c50040c02c0c120804081203a2000c0f400803448015001000800e180c0c00380c90312110b40301d1501d403c3c06818589008013400d401d003140e200308001c985c0c00424201e001841413400c4003014004440014051140c0002200306226400c000078800b52807400389441d09140030141c451642e510405c480c241d0281500e51103a400180312103d110701e00540c001c4000340602c4400c40b00390a100e44942c0710f0b591050070141d0000392039070030901481911402c600d004084401c821407405001040c000c0c0c071303042c990081c40c4c0c01a403030384600142c40d0384024181000c1d65008081d0b441041461110b00000c01050b48124020b40c00c05052aa40d94000701c142c1308101900800340102d203190b9 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 862211609 1250 862210359 862210381
    0x20a0b07021f3c1d1501030c091e0203090a020f060a05071502040b071a01211b08030d0f150f1203170403020606090c0f0405010503040602040911071a0f 67
    0x80f0707611000b50081c045410459039203a0150310100702d03484142400704190b84400500781045500f0042030f6010328401000007802014603030085568800f000502903007448200300c25010940316588100d80007100b0700081080106240481c0d071702c21148148040d65403000e110883c000e22015101007602804400081442c60031044000c0c102c07800f00525158460300c80a80c1a00300410a440d00c283c0d040352240f80101c840001c901410716090b80507490140c2a20a491042c100c60b0028600b42d500c045259541d10040e410102629070041503a0710365408c0d141c0f00b0010300903494041c8071107017058010b10800c0c020f22294003d481c5001c903090031041c100f02414110700e0a0b28011810840c00400c0c403024a1a1640ba440c0034500c81e034040c1aa03810b0600400c14403550182c0701880c200c004000b000020818003040318210b071001c2c244507443c1da07104d0a2103002030013540e01005044e410002e441400c80051402414858412519000c0c0788070360f0b000004080208a600c00452012103020400c91161 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 862212859 1250 862211609 862211681
    0x1060603060605160206090a17060f01120602070507030c06030e1b010c02010f1202040e060f010e0622080601030605060a060504181107020312030105040f0b0d02060307020a0b07021f 80
    0x50b01d034515052142000c0f803003c5003903278803c2c5081c9034000e00c0e0551408041c030402e074000080b550091640e5050060461488040c2603000f003d46500207008403c100e01030003908000d40d0005180710704540d540d64040c0c0a80b0190745c0b42e52617805408142180d44c0402d10f2241c00618041c2e60302070280b5180d0f40150340d907010418460081c418104040c41f04080280000e1025214042c0c0b1000a41001028464500100032600d8148006203114000617116102541c641d010b03001404080080f210031041004001c1e038100082c40d0190030008000d0100e1500110b008650517180111501e5460030100c1c0e80f400b85005203001e4200c4507003c4000b680180c0c1200310f0003400304454030710341540e540c002403500034015100380b4a0200070004016a02e042d100c0e003081c0c1c036032206081c0300480e44500010b0340d0b00102c1900074030034034010001c1140c82d48204403210009034000c0000406052980b070103541d60a0110000301d101e03810419810107a5454020300f1100503d09070045069500c80000102e1651 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 862214109 1250 862212859 862212863
    0x160807060f091a0405130507170c04032906030f0607120618060302151e180306090a0512040305150405030f1222080d0209040b12030a020106060306060516 68
    0x20b04507101040c51404803c11504000c0250507065a40c1d107001c09210b012011414035168091500d03081110854010221003c4440c0d00450b82c01d007540c1d81c0981d4012030159400183c000001d00013a04041c110811030040c81c1f112034826240c081d9110f0f001c040d5243d1403000c42003100c0c1c00031008102c155000341c00690211458a00c04501c00e0703143d44d00c29000250300600015101c0e02d40c1c0c420003c2d4104030221f1440301e0443c081c114a082425400c903610000908800214604005075042940580400d903658801008040e070fa103a040c10001d00d9a00c8034030040603a140d001e5000421b04518103801100d00701c80d8044007425444100180ca4030b0320043c01482a02c107030000f00003007131002c141500186080c204080c940c50007410700703640d01540c002442d40181c01180d0b0000b11000460660019110102d5140c0d0015a40341c841c000418040e280310468590410031070310f140d11600a020014085c081119070082069640d00d04089095406c28400c10000c40c0d4200403200e40501c031000413451081c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 862215359 1250 862214109 862214117
    0xf03071209030209090d140301061407021c080301090b09041101031d160611010c050702090a0e06100519062001060803130612020304030207092a0201020a02160807060f 74
    0xb5526000700788854011076980c0220b0b00f02083c205401500594040142d500142855046605151001d002200d801e0300f0200742e0100803803114110355030311510036440c150002002e0000c041f9850440416002030080700309043c1402d0b1560040d0a1621010380f1464104120701910808500150f00030406101d205419900f609034a0140c240c003088011905c0b01a500d014400514001c401085542c01d01c3c1c007024640d0505a0b480c0102e54002c007503e80c0507030108c5411032503032560400c1c00000e2043d6481c500345800b1340410441040c2d0604260b0f400c0712000d54180c0c1251b407048491400084087c000c250114020010960b03902e106540c0145842d11031100028015888556462561300411075296103201141420301040b9445000f5200c1e03042400d800f03605504060707401a4498009010307892415513101e0244098000d040500030750000ba40c1c0000291703408001c00207003c0d50094408502501c40c00c0305000ba9800c1840340a82180c40210240c00c0392030822004885640e0b16001c03001c104 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 862216609 1250 862215359 862215377
    0x10c0c02150d0e0c03071707090c051e03070305061c0611090d11030d050c071a2503080117100507172a0a0206060d020402040803040915080f030712 65
    0x4072110388140c181001080f03000b003088007030701402c25107000e005030000e80a0307050306440040d941c1c00001d940000e84803a500c01061820040d041200d4034001d01c280b0002980052004102a1001e02d000b10b018210551307007032013194dc0e10780c280310400c0c9068080c035408448090038440030850780d501015645250144251500301d5140006007055078143c0140c401c901140904245460308028260403a45030342030107814007130644000c0d80c0360f003054440c11080c40d0440e10001a1102d00303904a464801080c500b04990680344002c901320b18080000c00c4000c10081e90000c03944e45400c0501d00d00210030f9800808a0150009059014004c0a4206401c0c4044000002d80400c0802030709403059401c210b1100b07910000e1100010300316510000b2228802c03042014110075a804200ea541c401d10984400000a441d8800300b0000e01c11a03200240c070740008103012840c3c00d483c1d00107460840b071412605202644410040740c503044403e00c4c4014aa108003c2c03d40043c265400d902060341c8141003681170 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 862217859 1250 862216609 862216627
    0x150303050d0905031c0b030c0d020a120c0909031101050601031509090f08033c15030a08042d050a06080405070503060a0b120c0a09020711100e0909010c0c0215 70
    0x80110010100085c0d41c3c5070503005100b81010044a00622002c0700c0f003514011064010504090b55801180f001c490314858040a0000d405500350040c40c2c0341000700700a041c18280200014902d1b0840b0340154200300c0401d03c40d601c6402032024424680c0c807000c0701a4175064802c07005059074803080303402181c0c01c0c10420100304500c024500c1110048bc01450180d030140302c00303010030305104554440882801a4002c0f07588040391581c0c3c08146004000d90024440002034540008250300801031500081c1c0450007400070300c0361307001e40c103a04080e44141c00e0f80e03056200c1071034585009503600300300380c0081000441d101d0204540c0260040094400c07854840340400d080040c211108400c0b59115126a425030074071040e4881c9445600014154940d042000039401800764429820703240e801081d04003e01640740b03280d138410800148142d07014030503072501402d0301001050180c030a045401c0001c0f2143d0040c0a00ac40f03040c0240c1c0c07003e52600c51303582001441c009414042da1200e00521040f00 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 862219109 1250 862217859 862217887
    0x1a010806061b07170607091a03010303080a0b0a17070806090c10140a0c2102070e0a0e060906040209240411040902070c1503020a020a02130b0a120303150303050d090503 74
    0x204954104c0060020340c5004d003000b0b0076540d290351200d2003500700c84051032418213100d0243c034152079061800200369119464564060046815841d900041000340090682c0030a2055004403440c3d2080c0c0c0d0006950b008038503116081201c00c1d54298001c1c810319011841c02419084100c1e509041c1651460064080e2036004e81000c5840d80c081a08500f194040c0000c0d144040d0521400d010f09483c1801007050094481d102440348110707051001300810b546503a1a00301460090b00c00003154902e103085003060f5034070790060710180d02a081880204000001980b00c5034081e03940121410f0300b850307105003480b0090903510138008034950248808604210640006d00c1c5d941c1c096988030810a0078804980503101c104407511040c1441080902c81142d000304800e03800c2501112007003420000b9070800d0000d07020400f5050362100d02d135a0045085c800f44100a126140a82d50801034a0700542d001c08949074107000140101e03c007400441c8072451140c00c54043c561182040e02d080c0900401706130303 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 862220359 1250 862219109 862219139
    0x100c050c070305070915050f10090803070305030f0601090807060c02180106080411010306151209020a03120305010801090f0209090f0102130806150105071b050607061a010806061b07 80
    0x30340913002550100b00d03621040c00b034811a014400d0980588924000000303541e660032440e201d00485080a00e0314405000f0f4180c90020325061082c2c982d922014a070003000d03030f40100c400f200c000743c0c400702244465101d0310000e400c0d40e020720000e00e142414200140d40e181c0031040700700e03800035001400c5c150298008100c81e00901d1903454144503401c01d807500c0081c0a4406c0d11040c1094900901040900483c001d0401c4040b69410644071000040c00d00308050f0048400194101003400d100108010001480c03c10307030812554200003e98841c14071600b40d400700007000e00b1010a840c010710252a1082c202d83c1c011510504031074060740c0c40d0f442c070b509903001107900c2120003000c031000300841c2400b440701c1944041007011801000c5400e10019046028802000c1c2203803100010002011201c04074200c0a0903000b840a0345483c2c080c51b000d805420213000c82a201d4500b202d404a00d9401042094000c0e40e00a2010f400c01d18144003450308005210700d45d4805209000c000150946000a14 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 862221609 1250 862220359 862220363
    0x30406030e060702060f06040c14030906011e0503070302060307020a0209100503071d070f02070f230f0f040513020904060203012904090f0204090f060510050903100c050c0703 77
    0x1c15205150380015003070207002008842507400100070441104c8110390840e0344072504440014042e983e60508841200b540350b00c0506040c80003040c88098440016400d040300d00d89241071080c98854402c40402c01584c2c45099090380c00f540d001d200600c0e10303038003442d448460362040320311690f403d800150f00740000744c62580c18451048424429410180145006005a69040a020242c254503040040340c02044082040681800315020174828090240148542c92840004a86492080360b02e900c4100c2e40e160001e00d004103c41c00c3c1c4c184042c610f41460001042000c2c06d400c040240070151400078458109060012050340040e680d5451150080d401450010f0316581050001e100300042907541c200b6144140101101e0303030441c10121800d130b4040c54808515410400580b4001c1c0c051034019003a1181041c540071a055007540c4440c0880e84125945036114000f08401e5506214882d43c0c3c50b00340e08418060f4505440035000745403400e40a2804900d40300150110500b000416001 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 862222859 1250 862221609 862221611
    0x22020316080c010f0813170c0c0415080a0320070b0306090136020d0204240320180411030103140d120b0312040f030b0c0304050a080f0c03040603 64
    0xc10300004900704110301c1d11000a082a0a00404074040540095002001c600482415610320303010001ea001841d2140c0c08242071407034440c042510360395141d0070704811081c0940d190096603480c0c0b285000a1000f110601c1000c1d2070680d43d01d0314100c0701c152109a12061105108200000054040101c03800400660b0007882d1241420741c100043c0d244113a010700d0340d00300d0613940c5506100d01513144c0191030403880058040c010000c0036400c083e0044c84006809a440440e0016914541d06001180c00c0c44c0028a03100240d01c0311000e904072f5154a40c41e440e401d11ba0780503c0643d05441c00140040741c48141c2c2c000c4008100400581a034020f20f0340290810800704c010401c101420755101d40c620402006041550040303c0f0041900c54010350003440e513600d03001550b500d601c0501c0b42c003243e40060703001c02e907641303440300c07a454100e80c000c0c03100f2205001d43c04009103040480070250780c000e681c000c0180c0007001207a04d85c08510b400c1030240d00d042c114200607a180e40c00c4200010002041a510 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 862224109 1250 862222859 862222903
    0xf061a0406030e070e0105060313050601060f083603070c090207050708010e122d0c191208061801080616020a0b04020907120203040c080705030f06220203 68
    0x1400506603500043c01144a611003c010b00010007903855a5040d10403d5451a40301e5171040402341c20300c45080d030050140c0c0034400c0042202d6510445800b84c649aa80312140285c80f4580c123606401020081010603a255550b203d50012422000842c0e140b0340c082228240595034883c00a241c8107548400c116503400100c2c1000c02105220408c000c005910007004840888103601d902d441411000d0071510a00296a05c1030801d80802c10040b04079650703a0310240419100401c0e1554000c0300d90410034810000500f042e1901c045101b008150300c0b003440940d24807026815500a10081c0020344d1218040b206880b10051000300103009000b0f41008140c42e040a07000c000718811801c0ea20340c119000381c5080400310384080c0c0c6c00d6801550565510242d42d80c2c2503012a910207844030780020030b81c000401c0c002070180d0104190141c480602c29a005d80c0c0c1c0c0d5004040d03869050401481480e00060000340580003440f409200150381000b504070b070403106900080c20300341c00f10084020317202240 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 862225359 1250 862224109 862224119
    0xd0e093114030a050703140408190c1a0d0903020120070b100b092407050703050601051012050604091e06060b03060607020d051510032f040f061a04 65
    0x1112907011990055441c26011400c01030041c071135145d0140074480c01c0350786990a50002c101700c0380200301c80000e4902c51100c501c5080300c4c184c0700482c1552442d0109c400030512401c01e400260034821040c2c4010b140801c4884440b000d072503210825429950b9802001d06003800030b82c0c40c1c8000004a00d2a65070b9410701346800b018540c0301601c1040c01201d0134405100002802c01142e400d00c1003100c260b0103480384030000410044044803038000000c804103091003040800202d61040c0e0380720750251503060780c0f90030a00450b41c1c0c84e03100d580002591049901c0c0c042d841c1ea40b0442e0030560140c000301c0c41007019201d03458425403a1501203e003d1002200c40d043c00003a200704000341c149261f00e10301d5401d141c00011090301403001c0c082e1146281d62840006c000d020006c44400c11400009146c051500d00f89049050751135120655608640f90044d507844103600d42148907500e510604132142c0c6400d401403000a080030000c0d10b07440d079695030b000300310141c149141811f081c0c48420016511420301c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 862226609 1250 862225359 862225373
    0x5060d0512070b22020d020a0305010c210504020904020603090f03040303051c0606090b1606060905040309060302070b150607060f050a0608010b1003020708040f0b03070e030d0e0931 80
    0x8000094880840031540f02100311300f400f0118103601150000583c21141c00012100c1c2030070f03400140076601e0320a5546102d9040f040c640004280803203c040040c1c0c501c1d05840c1514021a00207501440308000a030041c548100a56044100e00003203491429001114a05c2c1d548540c005074049440841d244d88440208503410201d1080340c101401100d01e0544c0180211509000c0c1d01c3e02c13141d0201e40c01d2038240360081d0b01120190000403e114650b40c07480080001c1000740c1c0c095001504418001c512103020b40215010640e028a000c5055a00d903803d03006003000d50096558010b1041000b20041442030040c00099a280c0000165504004000d0000c0301c1c00d079881040d584e41003106081e0643d03030781e40302484c1c080c01c0ea060141c0e9407402854070f0318151285401c040c10b402015000415182c601401462080c4229220744070300000c3e910400d83e40d4859030b105540081d00170b0480914a04080e590260401c400754080d44070400c00d8160a002c0d0b030981c551401308022160512001d0001c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 862227859 1250 862226609 862226611
    0x3010e060405071b02101b0f031707090b0306010c080d0506030c100c11030c0a09060e31020f12011406100815030a0b07030c030b030f0d0305060d0512070b 68
    0xa0381008a070300300048408000c130100c1454040d118558400303503068511302a8080d80b038807009555211040729403c2c44c14500c5510040d9040c0d00040403501c1c085200314005180300d01652568607010340351850079044000c241e000610742c03070400051b110607000099841d8060003440d0300c90040403410345040f41c245440c3c0800c0f41000d41c4284c907118050302c1c2e902d420480c65041141c001c0100c4100080c2100860324007040786007650340141032603d001031488140c2d481441603801080012005445880c03005080146d50007118801d0860380d079084103098801001805010301c06040d50165070503000c0000c0460070000000c1f04265107880d1180403280360300d0116940000c2c201c4110030b50071807420005204500c001c0040341540700c4414140314580e000c11040303080369802010709983d464045401000341203a181c080c40485c0c1071017000d02891401240c40c2c141c0c9020f41c0010800304c415402c044028040260205401090b11900d0360701040c000e008074001e52141d85021030b0b45104d146451584004 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 862229109 1250 862227859 862227871
    0x5101409010b060418091103070e040309050301200c070317120109050c12040809040219030c030b061602010c02040603050a120509030a0b07181502010c020a12050c030c010203010e060405 82
    0x6030800007480502040340d42c24032280c031785050019038021103180c4100152994034583d0390511a0640024000040404091180c0d201c0e581e64905aa980c00915090340d80c540d045c1c1105041052511240200c084080d10798282001d044a88003543d0351982c0204072000d1508100011000030940c110028901c41d442c01060341c00010007507490050130420060103800c000344034070a800c4007ca03080c80341100c155507d0100c024811981c4101100c660002a01c03103210010109080036080b034480307402071041100f180c134042c000c540707400482600a0b05070340c440e0104a05000c20100d058000d40c071031b440341c10059841030000f802c04254900b01100c5005100b061001040010008064103482c08514103d00c29849041c2d103565807a840402d44440c0c0f003070031258041c1c00413080c1c0080c1c90b624000140011a00b103070020002030311001400c86e102d0f00c0f40a00940050301007110009058031800003011001030b540c040da4201590110403e09907402a0300c204152a41d0009200840c41c09106060f0018 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 862230215 1106 862229109 862229119
    0x30b0f13060c0905010908060601020706030c05070c09020405090c0c0706050a05070213140901020f0301181e0209041103060306040f0320100608031c0905101409010b 73
    0xc0d42d03510513640010803401e00050031400100307070300e0302400d41a8041c022480c02d11b4025800307001c00100540c1000401c10052012517400c0700d006001d807020001c050703552032400c3c082003501e02c0094011084007900b0000101c8003070001034410304442c06410a80c1d107402041c80140c0f5940181000690082100ca4031407001c02069400304600c0b002014004c2c01c25200c800c3c8803400c0303019010519120003410001030040c03444110502000c0022680c0100d800740c1012910007221082c2429a03c2482e004648603030305142c98040c4001c1d0b000140c41d0300d0706610300340d80003c0c1d982402820140407492040c6004050501c542c0744007043d5031000001040541e005003940c0c0c0e45021112a0001007454404041403200b00481225204d003a07a028402c2c00c11001c444080003400d2411040b152403240001600ea01001070180d103030001160909007403a881c142404a0030b60366090784080c421 = true := by decide +kernel

theorem cover : BRFrame.Cov 862050359 862230215 := by
  have h0 := BRFrame.cov_init 862050359
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 862050359 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 862050359 ≤ n) (h2 : n < 862230215) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
