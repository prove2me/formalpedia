-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0445
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:51:16.339558+00:00
-- url     : https://prove2.me/submissions/fbc43745-ad01-43be-845c-6abd8c679a1b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 79856116 ≤ n < 80035972 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 79857366 1250 79856116 79856129
    0x6030206040305150f04020d0201030f111804050a09050304060f0903050d0f03050907081f0e011803180305060c0c010212010e0709120f020f0a030606030609060b0102060601090b0d020c010501 84
    0x800c0340513509580014640076169000403510035081000503680c09103000d420303076420b2070003055907a8604621805030058180c2c135851900b011405e804408070010820b40507000444091000b034890340c3e040c0040303c60240000d003031a003042000b4026580100d4040301c5116036442c1c000002c0d5a0b0761995802c0c0740001c040b6000184a412010140070b0385801240d40100310b07030002c0d22036a45416070203a514560130030412180c524050480ca032402c51a8080880e0303841c144000c3c06491203044c400b080c03800d0350a6003200411101c4103030720000c4080300050400d80350b00c1300080c4680d80f648000f48541c3e400a20303240103559020011070b03041000e0484060f00810b0150400d56041c104210007400403c982d0b0400d54205058001c0c0c400803690b42644402559011b68030042402c0d007070350104000501a42014194505019000003007010303942c8800c0889004543c10401d140e003000c01261140e50035941540046d00c00c00042c001d00070848024136941480c00c4e00185800002c4000710b003550b80c26800310 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 79858616 1250 79857366 79857373
    0x306030303060b0336100207030201060e0c040902030a0b040207050f070602030a0813020604030b040503030406050612030307080c0d0c08090706020d080411040906060b0318010506060d050a06030206040305 90
    0x20000c040d01070040401900325125424190300e02040300780940c02542900c039145101300c14000c044064444095101c803040c0d10185c44001c40140080c0c8060b5010f41803c400661170031400103003a40c4125041d80c040d2040000044c41d2070314060008000c2d400240c03000402d641d8030111006555100d2006100711031141028004510401c0d40050401c2e800380d1041c801d640080040d000c0c1c042d80050007542c0b11500080d040d42c08489030002c600d05010f10340001380340e00c54603418001400750010145200c1c6100c0d0320240301c03a54401c02400410200c281c4508442da0052011801c098016801d2680c403050300c070901c908043c030408007181980c680c03490b08408107504006025070741000b17101e01405072507a80010840340e440c620b0020005000108040c0940b03111504825855845800c1100e40b641c00c0f510503c000b64540c10584405d610983c3c0c94250070300b0b42940704203945010701481d4420980104041c2c202007005400d0000307800d00500b104116582c0ea03c0210050b5504400380000d5409032008 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 79859866 1250 79858616 79858619
    0x1d03011e0c080609131e1406010f1a03060f130c050405030c06090306010e18011b0315080709020c010204051002010c020708010504050607030c02010b030106061101060506032e09020a0306 82
    0x1804002e4041c2416020b80f03104410440d140380307a00030140c1c5050b0b20468058021004501c1c400002e504407400400030100054441800d420004a41c1e060303820044408207241d44d2032000c152803144846aa004213501480020954500a030280c3d03a0014007030200da40749440f2000c44003c8031103a440400c0400c00c0480d0601c042e0404200703503090000c00f035032810314210040d0300183c0e0702c4c4c1052103081c200e800c12000080007400881d42c1803401361020320080c0311102c11021030303892001002c5490000a8906421011380402a81c0900c0032a00380d00043c144032400c00030f0581c040d501104110380c1c5503401308000113858484400e8060b6403541680009010200c00320300038140042039000110680c141418031002c1040800d161703820400c1c0e820001403450311144145e0140c42d5450603d40d1552808400050060308080c00e403141d402d00708020010030b620f5000b0020180020744008071304024a0702003074280741041c0b83c8444030005408600e11038513070b0342c0403800070380e48480080300000703448000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 79861116 1250 79859866 79859891
    0x9080a090906030203030415050f030a1407031b0305060f0a0801021b0d050f0313060c020c030f0336031b0f010c2109080d0c1406071d03011e 62
    0xe10140403840c40a025280c61600025940d000714007440d4000e1118444d0000310f28000da04a801a068542d100b41d1240380500050300204070b041c000c40448099000003c604034802d1192140e84460020121648012110114010000145015000f21000e0b8914090740e0384c460426000303104c20310001d83e542c41001c002c40c410714041309291034a81e002009208405070020203490820407054802c0341c40c0d54440c0c42d0704402d500c0943c00544071519146803282040d03804196aa001081078040f00c90a0800a04041c0d8130300c5040c40d1300d12010320411854010b1042046414041d4050061600035080c0300381c006030502150603c00c00601e22140400b601c0d40c14050324403180c01c01d003420440c030020314680b6402503142d00c40a1000403524400c0c107883d400ba002c3c600c0c00f0060711444040b2002c1c0c95103848058004914140c0540300070040404812403000001005485002c0790340e50324040000072407030300f45440800c0446c42d0745552a03501d1001850000821a112100010f40100711403d1404 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 79862366 1250 79861116 79861127
    0x5040207050a0f0302190b16050702010f0507020103140403020c01030510060903081e120702010605030106030201050406050c010603120c020102061015052d040e0708010f050d0804030b0403090510020723010309050109080a 97
    0x8d08080900409019000140c2e8104007200c84083c8103007026680d51606100403401002840390034050240528184014180e000401000002d000c2e28204082c0c1c4412012480301c800724880c1d0400250b0303c1c20144005128040901200f040c000f200e104038402116826419403c600340b401e882215a404012403103034240100e100405064008000035421a00000e15131300c52401240180400020142560703070007544420700454104110844044012600a100801244059005101c0d000100722030001e11204ac0e000c90340780340702000302242c400405070b40c9508081c500300162001c080605040d2584200c0500108038072584240c0d54604020030b8107034141010740400c0c100009000103001c5c0118804829003510400c5600c241c04542e90300e07100480f446550001044001c0d01420300c0304054011200a041d608208d81d980700305100710200301d0760b0343c4151140154214a02103461000910f0909a4840d560185804140611103455050030359000e0300084500580000d4a4071507181d001 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 79863616 1250 79862366 79862401
    0x3080717090309011b050f0d120621080c010c050a0807021501050f15070605061c0f0609021f1706040c05180604030b0a0b0a05040207050a0f0302190b 66
    0x500310010203060452810340d4a0084400c0c16052000180b0610061009004841c06040e07120040f0f807006d003010141d840d01ca044651218003c02e05c0c080200e40000c286008444c103944102c107500300d01c184400842100110104410346540d2410880c00c00a42020300a400141c00243c0328695204400e10005101500003031000046401c0f4020640401c080072480c24110361084690100401c0f000300020484540c182c220703d5101000107000c4100100b0b602702d03074441d4004507807142000c8a02052109c035403015100c010500450200210001009513000202c21030000d888502c80d003646100d00c00c00d48204c00009800b05840f0406040315601140c809640281e00340c405008022a4250143c90750040c0c6100c1c0c4010041c110222b07039035803116815500219080660500b150508100030802810a10411805016000e00c007040d507007814000c07204803d03802002418a40415161f0309030728003030304000f01c2c118003501c0e10580c0000f1400360b181000174050b5004001d81d0a003014518000e0400 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 79864866 1250 79863616 79863647
    0x20a03051b01050405100f03060b040602010b0f040504050d030e03070605010b03160f0e090a02120403050c06070c08040e06040b030d110c09060108041205040503010f1b08040503190201021204030807 87
    0x4100c05d00036500c2e5a44a1440c0301014200f01010008014064000d45860b03048031700064004031340080c83d17950540000700007850903124070610a07504414007040e90b0302200c000d1700542c01030110807511840303540002010003101c42a2401c00c0b03001e075603e8044e20030a9100c181c07441404821300555446146242c000c00030b981c24900141120900040c0c803403d6080703e5144106400d000180f1082019011549000e0125140b541e6901d01454090101d4000c030f811041144039420004d4140c9000342c2d1290350454002c0c034040e0815140010382c60345508020320440d00151213110380310311500c00f0003102400d4605511100100c02202002c9403401c030520b460184964114801e00c030307491744c11004040c0c215420139071909548070085000d407028400c03980465052362a248003421101c08607800244903c403030614184440d904040e0813508440e048c0c43c0074140381c008006c0109409481110352115955900025050400500b418a425401154240e011030480c400b0080d815902c0305030511030580c03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 79866116 1250 79864866 79864877
    0x1508090607020705060c28030f02030915071406010b0d1a0f0d031e020a1401090312020903012a0206180303040f02061204060b130b0102120d0207020a03051b01 70
    0x10704000003580d840d240c2c4580390166078002042500c1c4502403014807005402590f41d00940c0340c00c1d441101014015003c16400100e8800800002d40d1011044680025000b0000c01207000345080501407503001507411030740104d0310040450313042c60034813402e8000c0000030403840c0c903039884e8050a0709440c803030400002d80b140700005402d00d91b43c401042141914050300c022403400b0092509440700400700c5028403102e10700101d0788494590016881c22424483c91022401d022030101941c2610303010007000303001c52a50384100801441581c082e2102420050011520200030440084003103030300400030340451418503500498039010820f0b150801019203000140201c810742c06502d0b4000604000c0442d6161034035801507540b0706040d50501c14140060044608051500301c0090610483c0c050040d02400a1a541c2126510a0401500c01030b00a40704920042e24007400340d17071240169101d520703428801000561180d000a03405503125400601c0d210700360b8840c00c1c14284a603a2054100007 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 79867366 1250 79866116 79866121
    0xc06030c080c1b03040e0601020d0809150405011e0b0405010b030621030d0c03020d0606090807090e191209140f010507050c0907020a0c0506130b03070e03030415080906 74
    0xd52201c1e01c154080080082107485910902c0c2881d000322107510b8407030191101240105800484020342400340c0306c260210b501030606900280c0f40800301312509000ba400846803032102c034406000066125115900006c3c0400c10f40502135418920000c1080340c4680d511f1000f912800d0600c9020b024140c68400c190070b601c0d1034000103140f00c2508192103420b80d240f21403504410020410b549034020b01e80700900481d415480010002d42148404040702c40c10b05400042541c010400c43d41a1a00304001d0700081d41801090801b41c0481c10680070144502480300388050414034045a000344540080740c0c3d00800088000c045890581100400401403a005285036a0b02d040c010700c03a407000e0030000d49610b101c0c105981806c600d4442141c126248004110780b550340412085021403059003800302c410307121420f01c801c50103407000c42c40400f50213800501050f132900d006540e1000d450b01d80311580700442c00110b030554015030700136591000910b00c401c0c03c1c0d6401c03602180d0f0200740f20004060301d1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 79868616 1250 79867366 79867391
    0x306010b04060215150118090212060f0a0e0601051b0304120507090b030d030e030d0e10140402130b0303040f030b0a1d0d1b0605151005030108060f190f05040c0603 72
    0x540c1c5862418480311000340315a1541f41e03420314004005450b821500c0f915942d002c14500d03002281c1c0640300b403064444e80981c903c5c0c043e4036101511541d10340210380d65540d1005440942c44608603c1a2250001c0c0300407101c0c40400080c405411204070525100311203280007480d0921039008801c0035403c01c055a041910000b6440042051034a4085103116541c44444c2c00c1d8440c05000d95042420320340b25460382c690020300d03002e03222204002000303501070449a82c0c01000c2c00355002984603441c6000032250103015080300c0040724008090b41d14080e079038400301c101d05000d6841202c07600e00080810460002920503900711445c4201d1416045110111740354846811045040c103003c0c112000300d030207004a186460105d81d101c80100018109000100c40080c103502020f0301c1407500f0203a44a1217442a0f05070b80c1255541c000400d85511000c0b222000d201d801802501614104503100b149414130f409124061200d18100140508080c180300e08400385580004042c0b600f400c0214214 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 79869866 1250 79868616 79868641
    0xd02070e0a020a090819020901060f0804020603040302010e060406050601021501050d030311040b040906050906190909050c0d1b1a040b03040f14072c010608070e0306010b04060215 79
    0x46040803400596030f64242d18180c6142e055508442d80741d204041500e01444024400c524a09008491803407190ba81c50008a501c8103022078004001000c5030041001401d165028541082c427a00012400c14201a40d080c13a0002c12201660306580301c1091081d5940c050000708040c0708c0103070001e1000d43c10000824100c11801034010100b6a80754170030b40e0343d802c0c16800d0f10007810004148681c2c8036541e408030700142c101c50103107d20801440f80440d6091400107040120001818003203d9182e103009008001080042029a450301640c407107080b56984552207403603103038410a14001050240c40703801002c8a19900300308241e00c01d079489030010101100031744040304c4d00c072052a542c23a503952910311054500c0d00d6004003400c1c5840103030800b541c40800d07060155070f9560f503811040000c0044c001c5200b2400d440000c08204c03294010b105052240c0303100c651252450812244074102d41e00441d1801d90300b40d200201611002ca007d110360b903810710280700340078401050305a00f4200500890304 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 79871116 1250 79869866 79869871
    0xb01020a03080f13020a08071403030304020312030403020106031b0305010506040b090a11040302060309060f100501050a1202130b0a030e031908040f05010507030501090e061003020105090a0801020403060e0d02070e 94
    0xc00b110f080014140048054002c504c603501408000d0300716943c1e56543e80c1da1446000c1d20a040c846510480228180001540e2080d50020024884094080b07581401d079800680240e046548600700400482d200f9240c0c2d0340403c88440b2605649859800c00508542c000f40c801c922490074032000c0031180e511140410340100d840710000922003565210032401b8440c80c1c4c00250403410120820014010100c4c1e824490308091040d4027480d6100103400c000b98401c1d008580c003140d001d100c02c0303142c035129451214101c13016034401490312010807001c0200800a0f4801d60b88082e0004403020100c0e8136004040c0d658042000070760404084414040c1d0314011448403808000311840001c06200a00d2000340045030414020055410141c400501804090103034400b400d00b06817110403480b00000c1ca95110b220202c0c2900500780c1590300445013544445d5409501151168011032482420f1000f400210712840001403444500c0b039885050103481c5294030b00355000f40e08108100c40c0000401c41c1d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 79872366 1250 79871116 79871131
    0x2060f01140109031506140604080307150b0d050a02010e2d0402120711071502030d0902041e060302041104050901180615110709060605071e0b040807060b01020a0308 73
    0x125800201c0100d8142c54580d002401468404003c000c0b542065840f103000d0b281503180199010600304288601c80c800c074425481141c0c0200300c7c41c000b0915101d2255550140c1d441c010900da01c510740000c0d18103100b02015143ca0b0025496a0304560700443c400c0505081507610a0030a4024820760340000d00070003a00e040054140407141c031a5480b40c2c11211010481958482036081640d001080148180102c214a00c180c03400840c0804060320941418442d070750081d0b00c0e000b110b00c880d00c0a06901c0500300d80260f00e482c545c10040c0c614410710501b41408640000310306141d40100419204040041007034000c0c1000280035a45819800070b0648418800d01024081140050b40040110364055121090015001040f042d171010b883d0725491010300440d03414584030384240080f40c02d280300ea02d02291080140d2800150604c1401c1c24482584075078200c040501c0e180c500100e503045804840403a0b0004060f020029035114001d0800c0d405c3c801010030380c519a9001e0007101c40a840340 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 79873616 1250 79872366 79872389
    0xc03061215060909050a030909021306030e0c2101050a0b060403021509060a0903060e010c1b170a020a0507080601080a1103010e0f010f06050d1106070503040923010602060f01 77
    0x8091001c69041440200441c403010068141d05003003a5840ba40d4000c001c07000104034100014482c5618001c1d24440340d0311782e1408507858905502034000b06032030a00c0702e01034040c6410312003182d0307a80000300342c800e942c0c00104141ca039000b500c50360844d00d00800000019241400c15074240e220074041d6010380f50305551940c5641c1d52140c023501e4070b000340203859a00040010700800c040d680154083d040f81e101c2c000a0000428038520b541c00e9440d1007004400241c40c203821309420080c0099109501da00498a008108500184003410303588140c01c5030b0050380c0301051030030800c01c0401541000b00070500107000349504107149182c88400f00803010341824040b5007810200da800707602c4a640c01c10708104840c820120b441e2654060100700c410341c4060341c98050005500d042c05031a10110b95440820460034801c202e0410201d81c0140305c00b51041c0c401404003290300701513445418001c0305084d19400c02c20040780085100c1140581114046410420601c80e8004c1c80304003143c10742c5c1030100341 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 79874866 1250 79873616 79873643
    0xc03070c050307080a031805060c0f0f0d0c0e19060f1b03080a0506240f1608040320010c03031d0106090504050c0d02060d050703140a050a0c030612 65
    0x8031242411104060040d000c0000c0c554100589000240b210307031026101440303a040c4100c1c00c0c0d005609141d0340640160481c000003558648694000c10044004180b03242c200341c0f440c0b45010103604201c0c44641c5180e03403098140809900600b0907407840a0480d07d401c04480c16a2801251201030300c03428003800313110002401d00c940034048410390250000d040091409090900070600d107010b039104404c0fa4030b40700101c0c5146c00c001c00a00c84582201c64844540d42280144040aa0000e1780c1036040450038030084521000c10f2903020001b6010300340a6450b40d040d07040200c2c52948266845100742d0424207602d0007a6003140410340d0080d01418009106568040005181c020403410300c002546000804074005c1226030086000340d00640450745848038410500540981c090b20195000e2014005a446001310b138000300d600102c3c074034000c074002d51045580c080b41e80d0107480c035501c11911ba00030803443c00550b100f044c0d0001c00034941030002519182c0344101d16609140090705203c00034a0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 79876116 1250 79874866 79874881
    0x40303110703060c030c18060203040e060604080106080706140a140304020a03060507031e021303020603570306060a02030412050c1503010509061e040c111204030b0c03 74
    0x4003401543c20000034001c0981c80d5070014002c1403a19080c401180d5500e0f0002e00e000f0b06085c10909a0301290000c1d0301d85820b1414000d0884801001154000c3e410403010828035001e0261000902090000f48891801c0c200d0180001d2441c14851429010038040c03501c85581c0040d100403001d032145989552610340e40080f0340d004645801c040d203928140414002025407540c05011315180c00801405601590076002e0b06a120307000300c540800b2034401043c005850480001e40d0000e510421a1103003000c82c8822411803005104d441401c103001207070107003e0f0410000c01094035401110414040c030b16003060000740c1d000142210307006d01c001007800c3c6030141c020811a0f0283ca00c4846445507041c181c585a5507615031180310502039107081a01c6e00d0b0382c10000040c0ca05030354006029148554034031080c040d61100f040b00c0c000920080702082a1240c9403482240c0c2c5001240d070703c8540303040c858200c180ca40081c103072029241800800c01040410120401d00d80c000c00580442075407030315101e5 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 79877366 1250 79876116 79876123
    0x90c0108090a06241a041505070b040c0501080114030a03080709030209040c050a0b0f16150c0e0f0d030c0204050a2003071b2001120609090b060d030504030311 70
    0x204018141460b0a114410b04803140c220250700103e280013800c145503c0c3c10b0703164011103c5201d150b0100c4014042400b90003011040500d201d04289411030900d9103903100c880401d48269801d8940046585041c401c43d40d00c80311580c09000480300400b4403200240100e03582e94400304018040100700b0300815a00ba100b00074090040d50003e003a08001c0c01c145c145141180d10720310880307104a900c5100019441c078108145ea6072000740c454894108801502042c4401d0b200440840d45030f642803a8412a01681d4860002c8800040c0e40b602c1c440c441035030510444020140c50b42c0e02c0303202d4048080000a43c850102503842d5410f81d03000c0303820384a50008601130801141045600380e00d00000b00c1c440c040500c040c41c4115800e076180425400900107403c100900c410000c0c280c1c074807409888000125601c1070900c0c0b20b1061600b220701c0100781c8050000c590380b5401c05215a1346480c011024841c080708029004841103880b1408480990303005440d0344203034840141802072111502015031002d2 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 79878616 1250 79877366 79877383
    0x1006090b0a180b07060f14090d0c03140d0903020c0103020c030403020609060903030c100c030c080f10080106120203010e01022104030302160807060e0a080d1109061902060708090c010809 82
    0x810035140c40e2204c62a00c4009082c4002840e0260b6103815112490b0703e040000050103050007501902c0c01e0110000200e419019500707042c0c05001c0c5110002110164880c0106001c41c220540003515500b14a4001c2c10001c0840c042410140144840750721b180300441100d0031640d0441d46250b131140d07039102064241c0640034043ea410b00021031450300d02400802d100010100c104030400150400000650840362140c0800e03001844580001e00300308501040250001d10401c1d9021215958034251401e42d1010741006400c5542c0c086420b0460609008802001c00000025400c103542e8907048007041228103c125140410840400d0515000303038110b40061441325001c100c4001e05040080b03c0307500050081350b07034601e01001c0c1c00c00d9050218070000800e5004034414502211240d019014103102d1501103a40d10b41000350500b40c5e0744a4000300f800000c0c2824101c1c0c50070414a0190800d41c000b0a542c0a209081d0104240240b0109440f00d002c002400c060400303840c3d030103010f450310160 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 79879866 1250 79878616 79878629
    0xc021305010602060f0108070e0402010f1101090305040510021b0d1a1005181302010e04060e0118051003030e04020a032c0601080c01020606040507170f1006090b0a18 73
    0x2400d00100b211a4003050051181e840c6424005d00350b6a40c0d2841c2e40d40e5400e61003895001190340340458019842100c0c00c030740030076007454800c080760390140b051421101c1c3c940003140424000181080603080c1540c1c4403141c03410f00d0001d041c880004240c102006198464080e214554480c81c503410090450304082079809400c10000162801d070401da0905101030180a2250248008500c1c4d240d070420344c0241300e16880ca2641301009810750064030481c41c1010200d034031a896003000300c2c0305580c0c0d00078a802488034040707001301c00d50321206200c00c80b0300c06002c09014900002c01440400d421103030a540002040d40d00503520072480c41e04900424002c8003482d1114480700100b8a03991007030149690034095a02581c2c0213903610b000c0d9075643c040940c080c9025811103000200e203441c265020550020a5050004100c40001100c40003103800710303400020260b80c0d01c02d01920340c1c00549000043e2103503090101d032503070074941c5196981c01a200c083e02000822114030301001c246042c1e0760010b011 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 79881116 1250 79879866 79879871
    0x30c03030109020403061401050609040e030c030a080402040b0f06070f0602040e0a0f0506030118080d02040510020f120a05030c0a090b0d020c06060a1d07050c061302010206061008070c0213 83
    0xc5a40402d006544a8441551864140517244410248a03034406048850060246140c4504913003804060b101d60015007100303000c1400340b12141c01003400103240000c2c0b569915080d0b46840c0c8100001c4480152a00740620303c401034000c401e403210400c0b0351501d81c0001c0c070052148014a880c0300a03129541019030704424120605c0915000c2d0342101e410f40800701c03004d205076510481854200c80c1041003180d0780841440c03040c0e01003401c0100901c9022a403c0d0b02501e0151124042900000c00e03054890050f4840b041c01080e0703102c14040d5003103080313400c1110352918044e283c009216000260040300d098400145883c078860080c02410001d001400c80181c8407a40740c3c800c2402900b01c85020180360055000286491510009040a43d41c85582c1264142140c0b165032074403e80050148040c403508000001c440003040200510409003010b00100310001440028107200010b000340d40600e0000110303854458000150fa5402825494882400b10a50001a1400e54485582503a2a1 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 79882366 1250 79881116 79881119
    0x80d06081605040c030c020304050114090402070804050a0e010b0327060a020d0f0b0a090b011b050604060b01030b0127050405040804061115150a0b1819030320030c030301 75
    0x410209022180b04031000c101401c1c0c0b01d20160180c03440d0380030301c4006070800c21003800030f50b008800310b000241d1000c004500384610000410200c0c0d00201c03060300d20b00d901003002c002c145002c40c40840a03200c00110301001c1e516200c00d40c503481c04060001c0058445001c584e110420a00250034400a001412110755080049541d0000d41c4007082402d2054203128001c0c52806860060150b0b134407010b0800121640350104003402000c1d00c0d030074581044010f0f10540d800302042c25480d10783e14080d01c003902c2141001d1030300400f21041c69203603a05044c20000c8600d07441c0e820403111450306e0342c1032429a1010408002c603040d5440d00d0740203158810701d0901808140104c160141081c0c0d8019140c401c06a040700300e03e02c2c0e403402c00c200300002103282c010000c1c0620380e94400f5200589400391050200a4507003015014a4020503241e20740c1e0341d800f4034040001d26013410305403c001c9c1034689000034030b811600c00408040007070045990054400a65501440003081225050714034001541d4507075 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 79883616 1250 79882366 79882393
    0x2060c01091b05030f0c120f03030403030608070f18090501020c01090f02030114090a110f0d0539120a08070b04110303040b03010e060315011202091003030804080d0608 74
    0x42d2020149080000b507080c0010a490500181d4000c15081032401070003100205020801090022401403000d4000c4c0307160300d5040c1308200081d600a900c681c401090060034100c00b545844042d603c61000420020010480c10342420003500c6525034035400820911310030704007a8003910a221509465600c0c1055038010700042e5001d20780c03801c1c0700f03c000b4882c40c0b4001840001240c01600d090a054010100002c0028400f0510075034500001c3c191140212031000010f05030940390707409454541060100c003544460291b002010244031780c1d031000d0b1607000843c41c941c85c0d02c03440740b40e10b00a1308403d45501c14403904000b02006241e00000f1290340340c050b8500190302a400341c0342210132a0440741d010f0700070b240c08001e840c1a2508100910b085a00e4442030901c0d036600075040d9034150089000c8002c28a20390807090303010b06019511503a84d000c1d1841803200307030000149030364002039031108140300007a840f241a1340c00c0b6800c400126110201c0d14010001030402d64084040c1d80300e4a90a081013 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 79884866 1250 79883616 79883633
    0x20c060409020702150708030c07060908030106030204140a0321030603060e010213080111030708041a071805040213060e1f020a060506060306010c080d0e3a0210050402060c0109 78
    0xf60748207484c002020f0815049440300d9002d000c030001c0400c402400016a00c0c0300e02c1000e840c403140994004219000181c030755160581c420b0f0003010001703400007030a220f43c1800e120704590054090320340c80d1100c0d1441c0c480aa00c030500098550b400c40d15410721000c2140701c2c1d0803190103903400c00b1081040c00f994406040c003c0d8007000080390940b03440301c00000c0300380040c13180140f00302c04015a545140d9801004032140c00c4010001c6030b2500102030b4a05035855040c025512801c3c02d501c07401001c10a030300340c0c0120509158403842c4903e00411007201e00800b0041c43e0021a442802c021000b4000711002400303d40c0b50410000522080c00d12a604850780000c17981501c4e80200c004103c15280c04c0c050100500c401c840c0d60740400c1c0721603060310002d80e40900501000c45118400500300440000c66030074510f0542e400881c410180d030414400c5c1c5c283c04081c0c40d46101040c0b4074450f405036100c2c0a5180c1c1c03100d100072103150341d42e43c00050641d00c517042104d1102042c00005c00c4205a03d01d00b4800 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 79886116 1250 79884866 79884877
    0x31005010908070b0909221505010f08030418061208030601090b070b070c0510021b120301060215060406050d080a0e0a0501020c1e030109080319020412030c03020c06040902 76
    0x241140e0301c00100403001164034400e84000360358040c5002030304024070500c0030007d041c040f203042042e1048012003c00001e80000213118082120b4100302040110b4282c42c3c1c10b8210307060701980c601c1c00300b082030070000455084414030192400c03042c0004c2c0c00040140541d0307200201740000c4501520410491b00002d40c440d15003600e48441643d03c410f10307002c507030041141c020103501e1100041407416005002c5036074050f10480450716400a500c1d00c4030166000321400c8031542d80701c1c032910a0001c40c1070000514092180341010f0440d807410400959500200d003030012001740c50703408502c09454581040003d408d01402000d102c80c160f160090f065400303243c4082c002280001080305920b0711404400c100d0314164000d040208a00f02002074158480d0040d40c08094020654901a28280105100c45008442140d01c2c3e240c010511790301814071403071002d199441004244400400300b464400c1c05a054504550941c9880c542603150541054003240d221f0008a0000350f00140c5030002c0a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 79887366 1250 79886116 79886119
    0xa08030f0112030507030e03250603110705071a0903030f030a0506031b010f050c010c1e03091a0601020a1403040501021b0904111302070302100b010f020601050103050c04080102031005 81
    0x241a82e0740d418002c10b581c2515900100041c2080100c0b0780441d01c2209184100c20000307050b0341c048200180c10440c030320b21800011900100424007003140365090b100300f012a45070186424601900e542d1400e8a03040c0c9030113900d544c08100b02042420205680542d452104040c0840703076200f1130000e042d04c40d80c008070381a0786070609080c0050300609000c149900700d0089908040610743c0c1040064880f011844201e40401106211040d107c603801d01030820790440a8403003031460034066401d40110500d9580d5842814200b170711420014035085000c0340d41c00306124042001741c5609004034206012031001420140701520104030400b408401082100c40036000c8541440c54101100100e00034012043d078010412400100416100c072811b0850380e00c010043d544111260107250100c1c0c0003180c09030011f90010308008495142031003010a07400c004d08104202c0945c01000a640b140b05008017410552140086200b03e150341d421780c1c020707040f507000941d141e280a40c958840f00c0858490503 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 79888616 1250 79887366 79887391
    0x4090507020303060901080f0a030f03090c09050402040606050304050703020f0d0206030a05010e0a0903020c090705040b0304050c01030f06080604030c1e050f01050c090a15020c10030f06080606030c0904060603050a0803 96
    0x5c11780d40004500304908c51203c0540b543c0c4026403820b551452400300c415042c1602d80c00250b0000b6440e8450101074080440001840c0c00d150051000300d466a401980c103109040042c0004108005031780701c12a0b80c1129042c1c4000e81c50408104441d2020400940000e40072090200d04c5942c0c1d048a03068403040e9112000b142d03580e0400c001076805044010300580c0055119000c90f052040400da0302151a0402c10314090b030318810981e0300d50089031b040c0c0e459004050500740030f60341070145401c118000760003800304900300340d43c1c9502c800001d04010180101c0e49040401c028607d54254a820b041392640d1000c00902d0500c16256004c1841d800d07459460000011080d410072002e5500a54015007208180390810304142e800701a94140c01080d8410010f03a41c540e6a10846100d100601d02e40d800300344840340d445c4400569a090f000040a500050100003260702c00091260200400b00c91409541d00c03a401d04400603c17068101608a005420fa003205001e07641c40110b000b2800400300 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 79889866 1250 79888616 79888619
    0xa0203010509030a170903210f0901060506030106031a100c1502030403140c010e07260705010206131127090105090a062a030608010c0201020405130c0504090507020303060901 77
    0x505849201d014404004190130005c1112101c42e00784810b0703404400c10007104d2070641c044003210b44200005450540e5900010704019000102066494100003050024400c90707040500090080c0814068a03081550300d10300e035010701314003003041c80c1c90400240c892501c500c0f0594004108054801c2c0a0303c142030b0000c9541280d0009208a900c1190150381e17604a201406900c01050707071248010401c0356483c0e012204090b50709200c040300500c1140112240c88103c1e03900040ca100311243c00c0301003500304240070030441c3d80100b40e07e07500416a450100c0c1c01c00f0701d0315004008000800c5ca0940284a0104e03e070308200c9400c100390004000400701c0025956401002400e841d0700325004101900300707641c1c0c40c0024202e038020b900c03003404800c50310400308519a80008070702e00b00169800040d41301c00d410001400d013031151782c1c0703c001c09200952806040c940070403090b000c81c2c64859440d075075902e0640d03080c503c0740080d01d0280480ea46c05100d02d040000340290744c0d80040e10300c02d1013800d01100 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 79891116 1250 79889866 79889881
    0x60516060b04231e0f0c0306010c05070905011d15010503070207080610140d030c0b131e030311040506092404060e030607030c020a0204051503070b0c01140723040b03090a02030105 79
    0x11110300c203007083c0c03880085c51317910361345805a0b64002500c154103100d2144903120001e07100703201c540090110080001619171512030003a10102c21100f603a118103c1080500084410700b1400044800e82030030a0355583e03c580500b286400520b51180f542802403a060003c0a40c446c1042d030111000010480c14101c182000c02600c0740c60301d840200480c0d04598403200040440310000d5004036003401000264201d40c0b50080c8000108a6481070003010f003c0620816816100c0e40103822144207500341450308000220b2094401c04244034130031880e5041507164088803002840c0464490015152525529070010741003062424542d803013405000006596a48a4802e80003030f040b081e80105003000c10f94081c04006c007009410700d500d003070a10206007140d88040103404010414001c80f41d9840d2004518036085800e0101001c414810103003d000d1982e078014015642784a4280360540c1403288840c8141e2179120301e0b88050051300010003007060315030010034203412140c000d41c028015130b615100e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 79892366 1250 79891116 79891171
    0x1060602030a12090602030c09090c0412030e040f021321030c060b030703020616050c0312090111010e10020409201903060504020f04060207060516060b0423 69
    0x18000168010302c080700703125210f8040d260440c181401c0002d06a0010340722942680c0c401c0711180e4041000060007280c0c6d0804035400e550201c2064001c5090500b444986c2d618410511009002c0125448000c09595107960101034520380e20780c42156603e0401540c2c10180d002d48c40b400303103000000003200307500800264003012802d6041d40c440120703044982da48402070030010b410f0350b0544985d00000c00140c4030880103000c0301d41c400011580e9565140340103458424001d0050340203070403c0000e00640300d15141920142042400c011861a04400b025401000207204d42d00c0c607445614082000030750254020015190104014050000340c01c003940754402200310b00c0d6510b903104100e0700c030064000703444802c104611841c01280082e51500001e05a801080d01980300103c00102002120780410228008155a080c12818284851050f49010b03c16182c081d003a43d03110040b4009036980e90780078074000c0595007991f07407401d080e0100010300e040c4125414603180060403070036000b106110 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 79893616 1250 79892366 79892369
    0xe04021c030f050c0a02131a0619050c030d060b09091e071b0c0f0f0501080708240d030201050a0c032c01060f0b0901020c0f0105090907090b0705030c010b01020106 72
    0x41e10b90310007580380340c24210b400394000c16880009010f2500c3d0300c030060341e5024140da5044510745003c0388003128418001d445400303404005214034410003000001c03c40a0034542104141414410345500c40300e1003860441c400c01207403e075003500c0d124002c590340c842030025100d9048156280c0001e95900405041c045000464440380000942e0000d18564818803202319421001c4401100d00e00140c0e0780d41107030340019040400c43c2c8040e100d040c031081c1088a4210001c0c01c09280000f000e00f024000981a0300c03014110301d0414010144c559170f60114071848596181740a0f120000c40801424001d00904081d00d121890031304200781034906521902030b00b1080761005000c03641300d00c0100c2c3c4982c0200004c10360b010316952901000284c2c0014029143c000b004a0070307403656610824400242029000748204e44200703103010600c1d610f664820180c1e0f28131801502c43c89281e40340e04000303507000f0701e0310381c0896040080040c0b10001c001021000e0302c1d9204895000340045140200168240d403240d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 79894866 1250 79893616 79893623
    0x8030d0c0521040206190804110f0a0b030907031203090203010b03010b01020c040213050a03080a08010e040b0118090b100603051b1207030204180605030d0c0c0504090503090301060e04021c 83
    0x4801c001c8114650308a40a80c00510050401d490004500e600502081c01c815128010420080401c020720450b446d040c1c4149d681154036030242000c100020340412054003c000c41c500c40800040c541c0c180801c610030255800854280400751a2500100a0503031100102c0c041c1d42403005094190030140204001801c0503006402c00b1a15202840000d410050900001844e0420b0020b40c0d51100083c460180d400b400100383c0d100290b10000d85608010b07844440342d140e040d0100030200701e58094441c152240300400e844040145992000640500e540150002c00c0513018010202a484c64110488080c0d031814045a03840d01000f01d180691460b00002c4030204200d000c58843d401d00c0b200d5400001410010701b0715444646104004018031080c207040c540d511000d01c8070b450100600d218208040ca04001c003000385950780300d0562a58403580f401540c440940074100403051082d1000040d0140c000c2000e95a2201a0100303c04255010707800750285003420300ca241908031b80d91451941 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 79896116 1250 79894866 79894897
    0xb04060501020322030606080604140c01120e0a0c060801140f030303040f0327090f0203090d0f021e06040b0610080105010804020105121e09010b0d060203130c08030d0c05 75
    0xe42d603441d5101d0703020035069418910341310404000140188503070806801d001c0010001d034940380c40d20011558611266a0035076009081901c4a40e034001c00115084020150200c2c5c10030040c81c2592600e100b02c08010802906102c000c41c2140e40440c0c0300f4101c40e10084240b40f140000c40030700040b101d500360b0058142e00100b000801040d03040030b03126540c1d8401d28110801c1c0710007016450304080d039102c03949105501c0120811104d48503001e40703581513041a40440c81c60030b081e9805070392980c1102c41c403414070010340c140100f0076000344500031789503802a4000c40400c5641c42116268401218220713141070340074011810382e043c82e0800a108140b00d8070340008903402d100040d28082d030020700c200d04011081001d8005425103451642c018801e500c4500503100750711110321100f142c010700b010b09585c0751003c0c0301c401c0d07a10b010300c640c00580c0190380140d69841d40c011855424074100805024541801000103407032000000904444d41040720400442d00000340c201c80324824508c601ca03010780c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 79897366 1250 79896116 79896127
    0x7050103150b0c0f07031103010b010e030a0212160815090c010c150219081005091303030f1d2a13051302100905090108030c0304060c0f0b190b040605010203 69
    0x41c1100300910081980c60308903168400d02182c0310f0300d440f5003a00101e85083d51860703074486a023804d00071000a1002401c03c15441d02e0f154000c01d42c0da00007040042d20524421070700b00000002480f1108031030100160054150b5211a14550b1721b4146602c0c803850860640300090f180310002c00c0580d83c500e8165141e800c1100c9030b8039008103c6800f410103491040d800c20840b10b50360f522102c2d65059070000d8076a4045441c02c01d2400c1801d074219071100b8000d039180d90403c400e0b00011600704042c603a260034001411038240303485400500e401101d90f032444090b540d00400e01000024144045000c0620a0010300b0190040e594020502c3d50041d4000c0c5148183d908202d8035504401c3d4002a0000004141c00c41c3c0d8000032110f0003007420342004a1003021080c017050030456602405400d00030021803818155000182e628419071003140100f02140e2208020001c08441d01c20220350040814441c2c1d081c04128141040c0f50034001251130792030401406501d04080c0034010031a54140c0142d421300d0b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 79898616 1250 79897366 79897379
    0xf0f04120509040f230c0f0a09080304080109050712110d020d0204050c0405011b0804031212110315011805010302090609030105090303040204050c04030b070e0604080118050705010315 81
    0x108803446540050241c140002c9034241c80d10302c074541c2d0410403c60003003403d034841c2c03003200904110b000038611205400c030108210341c4003203400c40750511042c07400c5e035a4400b200403003201c100a458001c400d02c2d001c00500020400d005400030300c4071034007920075100440c0c1e544440c0c2d98507030031071600144202d110900b11005450002c0a4004181c0068280c404c030981c180e00007400c44808540c440802d840100b418051075a1028541c5c0b220075041d580034000c4a0503444001031801140700050800501d0080400b00c03a204640c0503074209041241403000b203208000b01c1c2400d800c2101c034040c8a1003000ca1103080c03503204110105240031640c0e2280030131410000114065441440d980342c100404200201d40b5807002d1080f2403042d001c1c0030107140c076410300d4410072056841c050403203a80c0d09003e02050001c0741d9a01d4140fa003000640c02c0107400514101d011400c41c0c0110b5000201652030078102e80c0351070725401080d841491158083d10301d04e075124001502120075102d0341105801d40c00c8810f01c0345 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 79899866 1250 79898616 79898633
    0xe06070801211a07020d0806030c1c0f0b040302060601030c050f0a18051509030606090103080f0901031d06064e010e07180203010612050a14130b0f0f04 67
    0x802d40240d142100e2680d6240980e0908803040c0c4800e0300503444240742c56910341c0d0101d2180d4200e01d00b20050b14000c00a200014a4402100020802d8a6040d80c1100c01c000c03113243e205070200c7d0310501c0d411541c030342401d0107500d40c402200c10502290400c1c56100d0801d2250044a2051200030002410034001680c00c44e00c00426104000762100d4450022541e0794a01a40a022102d2403490503034800d5100141403c2c0a0081d211500411094005200003201c03901681ca414110007241520f0b501c0f2100100c0280068100d0a481c841c04144c004011400c0460218071801c0c081d600f414089034490028144851400c8205000122942e503078814054040341c0000600b5041550030400e01c0710710b000908451050003800c540703500043d02001581c441a21340e01402c8002c3c6401c506542c90140060221588501c110101ca40d8941c0022031500c520b03800000040c01c02c5c0310713080b954a4070391015001d4020701403080d42c20304030000008480e1000c0c514031a10583d0701d60182146901c641e540d04d81c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 79901116 1250 79899866 79899929
    0x308040807080c130e160f06110106030302030403200d0f020102010c110304170c04020a020609060a0614060f0706050f152e020a060e0604110415050906040603060603060e06070801 79
    0x340da0007211b8110083c095043c901c80080e1100d0910b01031141d14102d4050021418100c1070583c5074100181000803940101c2583d0072203400c0301048000e010030001c0c40b00e800310074203201980002c01d40c00c24024011040602070350ba40c401c1e0001c01040c0d0055409841c0c00c0c00016140e1442d0344200300c01d1041d0100207010303007980c2001c1030803076030a009108002403da030445850380b40140d0051040212411003048065003121401000304541c5060140b01e54840e106c201410b402100e00040c1110710424010482c0d03245034101000300711505022000900440d01070700c40c1c0395102c6030403d401409203805000440702215a01a4900088011a03070015a0500701002c00c01d6010b4851408017294090003080c4400140c800688400d280525107645d07901c0842251900483ca814082d003080c0c8884c842040541d2002c51b0440c405a4500300000c014004542004050504202001081281c0780d00070b0a07c0269041c1902c090343e6444008490320b100920410842e0704080c00c11100c10032a444c038070325 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 79902366 1250 79901116 79901141
    0x1b01051f080a0b01053303060114071a060a1e0503070b090612040206071a0106080c120703050a02041a03061201020a0c0609050114090d02070e09340308040807080c13 73
    0x3034003050000c0e03a00700c001c2c0c14586d1502c03900100008012644d0390240100c031f690307001c43d084941408010380324103c0c0b044540c54000d8590100101094240d13682001d101c0c0200300c107030410100c0350b4103101071b0010380c021071151502900c0740000c00b247d1315201c1015175030384140140c10241441284c0080c2d115000e009402660015410884000800c110b40040c00a090040f807510420b035241010090503503000402e9021030f00742c1070100c2c0401c40201041c0d0f5030000590324020441d07855030210340d40244565440b1818055408038418813104480300a51f100d800b084641c02c54454001108a00340d00c1403514480004086136245000102568468218240242c0c0002083c0020600c8030803c3c84041d92180440e50140c62140c070300c0c40d4108003240242c25a03881440b4030b81000a4243d40e561154400c0820300c00c42c0035003110000d00a40c5520000c80c0240c24540c01090b03507800c0801081d4003d0190121501031090b01007002180001e14101e0110080c150381c482200c10741d104802000d9161610 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 79903616 1250 79902366 79902409
    0xe0d0201050702130e03040f0902031608060a080f010e120f040b07030306080d080108010c022b031b0504051008070c0609020402120a0b131104030303021b01051f080a0b0105 76
    0x10962104d544030f081d007110420740045a541d820070000c6910b241c020b0f40403200c041d00400411810811410040c1c40c043d45c241828882515590006103400e00103130043e40d480d21682621101c100c03c15001110144003000948441c4164001c0c00b54540c824107940b0f14401508120400040030b80d0001059000d00a140010300c150700c4011003801c06240d1021080003440420051261283c203201c0d0b011444581c2c0010f00e0344401441c0220005000c00b010a2070280031510311070b600c14002d8201000303000303c4411000402440c140f01400582060062078080c010782d078062240789004030042030040341280c9520005502d95900d4202a040d0382d04102e030890380a00c002d88c008170340713020094000c03080c083c00812440c5803c4103002640060107451107500e030500c154246451903042c111015240c0520b00580c2c0d44920740c542d8407051201c1d00c0c2681c025841c04e01001100004981021140d0303841310144405642d440c59582d503250013109000d0034103800d41d001000b0034034152801014081004811 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 79904866 1250 79903616 79903639
    0xa020d0b090f0a0809010306050418110102101401080f0f100b010915030b01030b0d110603060303070f0809150a0f0e12100b03060604050106080f0a09021302070507060e0d0201050702 80
    0x2c56083c40780390207003190102c8000c581d8144940c2c00d03025442c060f14007a50100818010b000903058800c090f82d1019140e060081d0061f81540d2082c4a10703000c11b8241e03e0240110302c0800360001800400340306441940c000c140d449841041c02041c05544481800b00400d10303000c5d250440002091039076401d5046c1310b42e5400c00a00001c010340480b8805140b41c0b40086c140d00400001340170b5500d0040c04c54801c0d607032181098000395003800030804400701070710019181d03540c1501191442c0f1558201402c940c461724046002c000c2400010840c4100a03030303041c1d0b120703840e075110551540505518a1302007404842000d522a100360300364001a00c008204202c544585c400540c03c140446003048216521011040807509080298a0304648191070402c6550325049000701000307005090f5204240c0c41c00d011404100d0140c01c00440c09400400c0c5403091607995903100000c0d4010310b0304071039a000e0641c0010700a030080c000c03180b8942c0c01a1440030315400381c0e4011200c0768001582281d000c15990744 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 79906116 1250 79904866 79904893
    0xd050711060d0c3906090206070206030c0a030c1d090a14011e05031903141c051501020609060703020c07080604030507020901080109150c170702030a0906020a020d0b09 74
    0x2907690250a9511803045519a0390100410b132034620000038182c40070414203008800091444580c4160404d50004000c1131600c00142148038407100a9801039001c401d03c04159030391001051490401c2d141040000040c50056070201c0d07211020b00007000b140081c0200900b00403d50560041e000e00d40084ca2514a40503221b04406c00e81010303900b03800703c040c00042010201c10003000350500720020f0074480c2080026454803070003204000d0030040c030001c074040b201d440241552a540c070070345603061001c0c000300d04003001010304440802440c1180115204554004144140100410009080d45990f455010381c080d501c0088802d60300d20480b0b000040103071041c001540564829620039544d10741500401010200c1078010011b41c0e45890010000103602e98110240c1035031408010540c440c800b401135070000b4400e040959508880020407230300035070110042c800c5aa40351101c00708551180001c0381d03180588a0001c3d00541e0000c060720215280c142e6480e844106c1c50b0855400030883c20 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 79907366 1250 79906116 79906121
    0xa060504052d100c0203040803221e03080a0207030606181506020a021009050904030c05240a02070f081914070f060e01150b070606080d050711060d 65
    0x32000d03145a00708089401a20303214007004007584208190481042107500b904940f107043c0e41d03500d81180f6a8901481c2c40c401c0c001c0c02070718028880c0c1c505803a00c13009004600400d419020071540042e0251140100358403070700c400c0c000c0c1e803554078040486000b415640c0f15141a4070080780b0809620998200000040341405072601400c1c2c01d40c0902e80c003ca02040907002d54440002c0c09891407910300307050000c560300203000d10003140c04884890a5244017041a96100400d80005401c0710341001080281608409524603191040046405004120b110310040d048031410307841080400001040b034803a0300390050b1061350f016032603031044241540e0300d0703140c0c590107801540c261030311f04841c2418280c0c21600b090f1160046095040c64040d0341d42d9805013001c070560005140994680e50448408130035031180c203000c0b074001070f039000303043e1039084040f420b8000301011110390741080030100d0724035001305801c996011691038681c201244c0382e0b00c031201c29241c602003941005090201040200850 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 79908616 1250 79907366 79907371
    0x103020f0408070302090f0906070509041d0607110304060c17092205101503020c0f07170c0f0603010b0304050c0607120318032a05010f060f0911030606030402030a0605 74
    0x40c0c010210f0a1451061103074001e002403074111a0300751181008404900801d03e42e500669030716003280d0318082d00000500800c81c1c2c00130b141c02100c0b60030302000c2904001412500560540d100c140205d0151400943e43e031146015100004d0483c1056100183c0c10200c1310201c02c1010f0b100c642860002408a2260300c0e161a50480150b0243d9030341c04040501d04c10700c1e4000000c1d892050002c3d0510b44080031082040390400209540001c5a2280e01c0d01444a441901e003080d040d03917402503440340d0b00031080d000c0e41e51410450040705002186460001b03c844901034001d03181e035041d82e02e0310156500301d070001001616540544c88244505944801c01000b4030b61107424540144060540010b04482a43c080c4404200702d0503005008a0f400060318400d60031071200c0410018504a101401c00e100b02400504960038100200d02884450300300c5000d4882c02c00300c0d00c20155403030981c04207403510301e274200c04036203000c0020442c90304150f0300840d03203d0300150850352803002075501c2c40d0480307104 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 79909866 1250 79908616 79908629
    0xc03030405070f090606021c0e04061814060f0f010203190804110102030c0c04020903011404061406060301060f080c07080309070f0801090308130c0503070605030703180809040b0103020f04 83
    0xb8400e1051503095004840a440812401c00816003405030195880304000f90741c0c02c6669860000800742c03031040400e9111140c0241080c040c0c26664005690005038100d1380000c0303503040c004030242d080d121600d5144110801414071440c29016028028107a08002100b030450108200304050080301c1d25a0030001d2040e503070f41c5d548529123414803614461401d4a607034119002001402000140091100d41c4410304035801652a404880024010306001c40b009240014020410050001e150b10021404040900e2190151b0f03400b020401548005d008800205005040000815210322002544070b010040c00340d00c2c1000795168540070b60000c560810507940700d60400d000e00c4022520010052011034000d000008c101e5401500a50340140101d51404540d00d4140912401c0b6200e00010a0050140c40c005030311028014901e41c07080341c07100d021a0a00340c4180d00c1610217030f41c002074141c2149900341002070398401c000141420001041c1016001d0000416100c88000204020285c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 79911116 1250 79909866 79909873
    0x10e060901171f050a0e0a0f06120b0a14010e010603020705030405060706020a1202130e13080304050a051b150a0e04060f06120506030c01080703020c07030309030212010c0509060c030c03030405 85
    0x1c3c0b01960b2085100d400003401002d041004200c816052031505030060310f201404a102e0450b10002c000030805544404110545035840340c00b8058803aa01e1405040410310a001000c0098046045440e080c42400c906007043c10042015070712176405022002d01c00c2090740d2805990314000780036034202c0d0000751031140d800145220b005801411125011200520942c10011154400303c40400316100354424031100b54001000708071000114583c1c0e5500150303094580c03c10b410700503940c640155045840e0b125030f541070038040c00001110302e041c00000b081c0030000940f002000c4010b4200d5034070302d024000c503601c103445035607154000c02018207018800340c4800c41ca4038800800b411250030742803036400c0c80c3c0028070242d13460101e92403408083c02c0c01c00030075a07203501c0e004400030311803000880128012814003100301548040c184003101e00880c0c090280b20901e69046080b44c0e4446080c00c00700d40100040c02040c00d040019018003201801624100891030b05042d0a5038400c40d0212510381 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 79912366 1250 79911116 79911151
    0x3170403020a06060605031f0807150e0604060509120303091c02010e0a0b070e150406031814060406050606130e090a0209010801060512070602060a020d06090219021b010e06090117 79
    0x3041c2c154a4520b244250681300151601107027685494207400b40708110f0541c2801d1000485c01007114064400f070250079503580d240e4806005100303801849201d449007035132054001005000000780c07802480c00d003000e45102108025032a0914848818080a65485040902032100103208003850240900c8444003d031500240017806002c80e10740319840381c045207010b420300c108024191019a0f5050400140c24098080222010715503a40c000300010815000c1c0801900702041d0341d401a4401c4205028503111042000b2040c00741788455610040c0c0c14070100841141510702981040c10300007a1416448070350080341207444260041c0318580c1d11503004000c0b5003064400300f0b030300c0d081001c054520b043c14420002d44400d00a821540c00e40d401045441600c04183e00803002040c000900f15512001c0345410034608446103600f41c00340c0521513144402c00c000400005040070141e6030030420240407010028035410130041c0f58100b00a4848407560351419007407081c054102ca2510301e8081 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 79913616 1250 79912366 79912381
    0x311010606030908070231090201081003112e110d0c0803040b0c0d0207121218020603041106161103070b0a0f11060a0b1c03170403020a0606060503 65
    0x161401e910650802d0718041e9410b01140140043e1025030754116000240d01c0220a441d00091240b1803201508014603a0f00900c000e1096100341c4880d40300323880f4103003190744219800044903c90710015004602007088024146894205c501003c904180d60394040700246060031240740c68106103202190301c5000d003000015040000e43d250180e14940801c040c4015514a9040d000c09400280261107407008034160f0402c9400740c41d200709540108540700c03a464103148010003d141d5039200400c0303502000c004115034600410a4403d54401d400700050b00c180d00f4800c03168001070050710b00d01c0441c8220781c100e50320840188005000c2940c0c0103030107442810031800c0340e107049101d20711a0703000c480304000d5041034034141c0789840054181101c030025140400e440100c0340300740d02c01e014041d4100f000303104940c03648101680c20050740c0460b070400384101000c11021003240d001e000300703c004410f440c2d000b001c0424180e220341300e441070703070349000a699038001540e05903080f40000c280d002c000c01900 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 79914866 1250 79913616 79913621
    0x2090a0f17010b0a03020f01110109121d010216060c0507050a0801050103020a0b0c0a1205090a0801022a06010b0306010908030705010f0515090408030c1b03030105030712030e1c0609031101 83
    0xf0b40904403a1501c510b80341d90f0006585904181c451810700400c282150810042903005448458100ca618010f203400c41030700502c0502c03040d031007462368103012016031141d501c0011031506ca070784420b801498050820078180d5200e20380c0320040700d440c0b10310100403d0507250031000c580282801d074008101c5505500c100001200c65170011050010284000d020314040000c2d503110341e540000c0110840b0b140c00e10102d40e24802c0390071041d0440e109070400100f44205600a00b0301e94100f00101407503c5c01123001c2c004000c52007041140652082005101d2a0a2500210740049050414100480e1f464044508642025006440c10b03595100d00c03c000081900800c2d61002110b80b250152456000018084d2003000c0d001500392100070002460400c01d8004031100400d81541085ca5011483c2c09180d07280c0c42401524003074001d1000014104040c04030418419074141c4030004e004110300c0501105401a41e0020204085081b101c000714400d807082c21a1140269650803210350020101404d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 79916116 1250 79914866 79914881
    0xc0a0507080f060c07060b040e01050f040204110403020102030f0a050c0a050106060206012111010e06070c08250b0703090b0703020a0215030106020703060203040f120c05011506080103020402090a0f1701 89
    0x24039040a010016010010011590400e078401d10002d074000401c00031230018091140030002661926007402508040111a284514403c40d000d100d00000f60868507050b01030340c80024096030003480b0700c1940030340150150500840620300b460410000d220762901e043c1000c0c0050307504d650744241c00e1090690622245003d000025250740d807504a40b145d40000b20036441000d0016641980a11184d84c483c182d100000c0c0801010701c2c0d103403240360500f404004240c0c407502c129032248603101e151805080950001d0590850b04441005141007203261051380a114101c0821403011000f040e40043d000c007400c6098007030b5004100c01c5502d0b1042c003449a802c0a52889101014001000001ea0008503981520740c01400035860fa21203140130702c419601114010130741090140ca250748282d210311140d10345030080009100c00182d85202c7c1640113002c0c01034100142c0040014000350420350014500c150700540300321143d03507940303c580110001e02e402c10314600c0854424606010400d00803100c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 79917366 1250 79916116 79916143
    0x181311010c120309060f110405011d0306060d050a050616030b0d120f140c01020a080a0902030601030b07110f030405040b031903030e0a382a0c0a050708 67
    0x6444056140d50400302c40c1a80d1080825448076402401c002c1709070045071003041e5420041c0484104525000b034a81c010380101400030b1410402c00d4802c0e04280310440c00c141e0301030090007182d1202c000380304002c03101c000d083d03d9912802400600003981004418030426216441004007404085d006090301e444d09280f6201d490482d0300712010480200700c0c1c507652039543c24121690804507400791207885400100000030308000ca0203291051064008040011959403008460f541d010b980c0704c210340740b02c0ca01070b40640c490001440000c0e0000c5846400034458200925290010b407001031401e92076000c058030f01c0c1c101007010041c50800b4002d06280e03010031800303414141d4521412610740c95a0305806010544c6944c49a8101903003444545903542d00101d04814070840c0e16054120640301003200c004002c20a030401084c84043e0800758020010060790011f40d2401030342a00b4086019418540d0441d001c10119143e01c80030800440301f40d02c42c130090403443d4502052141440340181080 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 79918616 1250 79917366 79917377
    0x302040c0c200310020f04080106270b04020c061005010e0321090409020909030322050a020103050919050601050909030a020706120605090a020c0106080c1e18131101 73
    0x40001500741e1080b5050844060610211018241c0040c3c904180218803c0c034440c80000c1291600d581000100103590a14000b070045039619610303149400703000c1c800300861410054580b901c7c170034241c000780742c61100203002606200c0280811824a0302c15103503030040402c0b50760304101f40c0d600701440c441000e104030081e0201c84883c0e04800000e01502c044e00c03041c0340c000907428409030750f503900507045160054103ca2981c640101202d94942c000d803848000e050850520403401c012050341003e1156011000c1c1c00410955801540945809000c146241c0614031251104050300c80021070302602881c001c0c081da514010512207480d030003800e056100d03001004252122034000500c1001c5980ea0300d00048091340c21659003000700b005411103035102c2015014002d60700d1303850300070380f0707150b28004000c016150707869051a5a804424001541201c1d01d65644006404d130382201a2076001c016147c242e5008440c800402045400c541c0007055100001c0a4824400c0e88104503808880c00c0c02e05 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 79919866 1250 79918616 79918637
    0x913050d0216090b120604030906032007030804241a0301021306050a090b0d0b0f0108010608010603020d0e060708180c010c02220603050106060314010e0f060105160c0302040c 77
    0x40075442410b00a841202d52100213403035803515150118200b89103840c0640d071040c249071400525800c1d06100e0000040e051600c1c0c8440311420001c0350720708040c443c05084c0380c03c141d5a416034120b28010426514030010041803401c00107080c1c609010407414010014010103840d060104c0140c0c2100403500aa00c1070040b810040080280d140543d02c0505001361581c0c81c10004441d4907000d90030102c1c2000020030301c40c4030a03107180c00039640030f18103d07405000c00c5104401141c0441e0244a4200043c0d0084010131207203010794001c2c030000510640c0481c1e80c6100558803481c0400c261410400603419004020071020041c0800c00b6100c00d00300580120b2032003400081c070000750604064171070f801c0b00c40e0403641a01010380b8241c454030508414040790303580b4109070703009002c58410700001ca8100000074041c810212031440c165049103400700d4a507212070484052001c1c1c014155411b21008018660503640d41c3e60b802001d56224100c0003151b00e04500c1030009a500c510b40040034442603c01 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 79921116 1250 79919866 79919893
    0xe010b03010e1305030d0501061b0302070501050a0c020306010305030403110d11010e0117090c01110705011b0305040522061203020312060a0518010e070804050304060e0f0913050d02 80
    0x84034116220514840c615880700f800c11101c001401070020128030000078007040802180d00014101c0745d464613103050841c0b400c60340700d50519508000400580000c0d0781404590f0081018044c55442032428450300c074916070221340f03440c0c02070304141c4013540041810010451b11010f0000700c0c2c203064800d10380b82c01c2c20703903070700e145136140c2c036034905c0c14040560010360250b4402d80d100d2030030714000362a2200c07906210b80d1aa0312000d00980450008004941c045112032002451200b2980b069440d100f54803010a5042d040d14a064011020031404000010f6161348003030b0808000c5000801d02200541d083e4100403c44507075a00447c01000d21004541c08207401009554548881000126403590344000095141109401483d0f000c140e0500d800003103035100c3d484606858051b05408403944440380d0903106200700301e40080040e8810001800f0681c46a40101210280034000c654001c00c03400024480c0a000c481140240d80041b0303640e0148203040080030849460f42c0060000d00442c6103 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 79922366 1250 79921116 79921139
    0x50108071809021903120f02010515190b04080d021c140d0e070803070209010f080c0118090903030f0b0405011a0a1110050105030d080c1b011e020c070e01 68
    0x294030700c9982c941d408025521081c00c81e004211a021400606a0b181c0c504003c0710b0f0380d036800340c000043c85004543e24a07801481401d01074002c00012405c08400041005800d03003405c035201c40048466840010307409080b402920150154801030310903502031840081c42c0c0100c0c8d18010b10a1503000c00c1d144401608140680d08031441c0d104201d41e1490040000c0019220400940c00c0c2445a01307400a12040003001400c1c0e250b108681d034250301c0c0d030fa44020301001501c60140c8541908140c00042c0d607580101403004d02c494143c003040d140ca658507043c96003102d01500007a000300307880e10300780e101d03080c070611840b10ba40e4001c407010403203075050100041c100195681c0014005500280c94034550b805103402d161a200c2d241e0071104010404004540645002c0c803446003c0c0c80360501e19110b250158440b588120a107910080c1810400990810985407010100c40d4556840350945480c5e03541861140d0642019500581e440da60301400c50310702292503100d580015107000040c8207000801 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 79923616 1250 79922366 79922399
    0x70b060105030403030b0d03090611030c07060c020d05060403090603050f1306020a020a0602040f0510090b092e081609032402090a0f061202090904030c0c1508010905010807 76
    0x3031030402d44030b0b0307aa4503042c0c0080c034203030740290b80c40703018498408109544905c65005442d001c0d0780d41e045505511000741c2c0d480c00303070591015968024075424000760b8803c1c200280c050740002c00c81c0e16154107513101e482c20414103171020b03400a03200783c07010b0162541500405400c0f10605c103280c0120328045652078503c20b1458801010300340c0029280f02d40903c20403100b02026041842155541c1d40c89000c0076214a0701d00c10303203003c0c0d28161403201c40c143c0107420620440e2800c1602925061480f8100a09400c40100404590742143c440301e10381603c0c40b03d180d04031015922510342e60b041c0701c0c42544a0890b0200e800c81041000700c01400000c400800b29141c10440e50b82c0700054940c0190003402034002d00003195000000c3305400650180b40107869400c40381c4585070034222004801001c420391040c504066040308400340030a00107403040c0390701000203000707410144845071030b000d0000c071503545035000e00c00140c51040180041c400d540301d043d0052400c40c00900d003045c03602d682b8204060700c8 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 79924866 1250 79923616 79923619
    0x21e040608043513080105010806010e06060f03130302161a030405010f0203130b0702010908090f0d05030c07170706091502010e030d061404090507180209030f01051b070b06 76
    0x700c1a80720380307102504460712802110a031060204042c5444400b110780c005001045203080244c20000d00140f06102d00b5040c0c600d148003400250b820b1403110b103004640a881c15070480c10420012004030b50410155000d10401510b5841c0c0c0b00007402e0081c82c0071906d8440002c207460b074400c10400418441002c40e9600b10080c40d80d91281e5a80c142180101800b5004143c104d000008005076240c0e1800c0744205d1030310460500e0032607180d2034022400c0303a03031084e4010b20701c5404110540c00340c0750151010a1075000180a0035851001d641d07800d00715000701010030a55802244144100345c40c0701e44007a030544115005100f07691030000014000c07001c900c580d030b201140b00680000007500c00c1d00102c005e05201002c481d560301d10340101c44000d000900c114214410645407a684601d0540030b40500c050700000244480d034205040b026904600d0f101d10158164200403c1c00d2a480c2401030b140a10151000041c1e0383c9401c3c3c0c58544180e8400d00d04e6610391100b000076a000500741080716801000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 79926116 1250 79924866 79924883
    0x30c090105040c0c06110c0d02060f01060c0503090a090515060705060f042904060507030b0f09070203130305010203040308010e0c040e04020a0305030304050c0a050a0302090a0c14040603021e04060804 88
    0x114510507208440080400781c10141032452420030801100d00501182010031f084601c0d22800d018202d845600c2a9500c107041c40c1e07a1b00040040750310861a01c2c0c081c50042d000c5c4c0b4909403000c07002030045026607008070001ca4035201084080c418031582000201c0c0c0594881e442d00219607a0180c0303d080c020007942210440c8030200702482a400c6040414000c250f02002c183c44505003286880d01045a040f0380580c1000000f6200c50300c28090240d030404050003402e06030441c8400c1010044004000204601c800e114840301800c21040c0180114007070000165641441c0c10000c00204050308080e0100c0180720501560744200303011281114140c00d183c0c10300f0740b41c0340300080300b459107903102034594403012050009020002ca8001c511540888029088654034014410000c5182c8800380d40500c4160000307100004580142c07002c0c085130700d04031090102d1030204c050140c105e60888400658042850f140002c1561030980d1a41c01080c2128241460180024240310b0000e200901000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 79927366 1250 79926116 79926131
    0x2071202040f0603050a1a25080a020f040b04080c040b0109030b0c070f1103070602061611210d0f05010b04060f1106011202010813050706050a111507030b030c09010504 74
    0x1215030f40008043d580c070005039150000c042c1012500c003540f12070380724a21800c4502003002010b806503400000386a01c80101e0300042c0c02d18094901260040c050342c0002d07002c000d0010319a004038028400781070300c0031103070341c40310308201445240c80c1c054103280c6c2c00380e464880a80040c1c5e802c0300481c01101d0713001d50b00401e1541d81c542210b071180224500240103809880c550010045003900b1180048001c0e011561a15a10b000482e074821042e0b07084500c400314008001100c51007411404d5100c50f0b02230880d048040c0e1404640c01e120301007040c134040400041040d0000040c80d001e91149041002024482e550615815480c42d1140d445548240030718103560300900c900940c1c249a07411405420b031481580d544140a0340d0b881301c260308900050780f034030026014102c1c3c80491620079421000910426080003015662503000d216080140511548007614110302000181c04a201c0c4100c2c0d00b0050401c00d202a00350380702c61034000d00c2508040c1e0107598075110f05442c0e03811120f040707401003201e5 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 79928616 1250 79927366 79927391
    0x6090b0d080f0405060406080915010501050313110a08011b05030103210314010e0a0e060c1905040b07030e010e01110d080a06050a0806160c03210e030313030f0207120204 75
    0xf40b04590090790000400300340011a240c0007020340b4454482d00080d661001456044403008002c2400303143e011a1b418030102d404030100c007005a40840c402c0181c074454805034000940c80c40000d0b0b1049186a455120b00c0c095840d8003c070441000285041850540d410b41d6980a1061040c0454007010904100c4640312988250800060019070b03040c0c8000a5850b4804e40000c2c400c201c5400b2034041c14800301d02d4401c43c2c0050708078492123044001606040070042c052494124008011003000024080071411810360b90060290500c2511803c072103038400400901032525114006050000c441d80342840102c0100c0c020040981500d0500c80790ba6031002c41c1001003125801141e0081c214101c003080b05000010158056901381c46401142e102c2170904075030b00301c510000180010704806103140100b4500041881103568080b003c6407000c040300c003592640d00708070b8181c3c3c51100e140790b91401381500494140003500c03491020b41302e0b25042c0704801d0348650f110b09009000c0e40d540e00750184075 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 79929866 1250 79928616 79928647
    0x10503150405090a05010605030c01080a05060a1814010501050a0503070f1101090503071b1d062e090b0c03040e0a021b03040f090c090501030e0c090c040906090b0d08 73
    0x150350014010000d60501c001d4042d40e40b0702c004000c858941c64128089030320701d40001d44074a6a10165200c8c1c0c1c4947c0d0b0108540060030000c1c0445410170715040300030401b02c500c0c543c00090f8001d44440007904061540c3c044001c5041070748921305005040140594950b4821304072a840300035414502005031060408840240030802c90031000e5180c4040ca01c00c100c0003000030110381d809071500d0a005c03407445100e0700055102c2c3c462040003007031400c610074198512030b1889a00c0f0344020069824030007c0764482846451070f1400103155160002c000611580084d0110301820418002034141008038280d25036a101314013405001d02c2c9003000040407510550126901068000715030583c24002c2e4541ca682c030382050090400c405548400030481c1e170002e1140b40b400c00003540c0c40310b030b0301441c0900640082c0008620200d40e4050700280d89182d440d032100b09402064007805165a0b14070304002c2c401111002d41202100304d0600d26503080c65038600c146200802d41002105603901e40d000c080000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 79931116 1250 79929866 79929901
    0x30308130201090b13060801090507320d050f0721090206070f06060e0a0b090c07030e0a06021e0f120f1c09120f091814010e0a0c0207080a02010503 65
    0x14440c0005449502803134806002c00c1241c60030f4882c0d1f04c259881e40c2c004410740f0001c8030000c000070b400c03d1807005425a01040034450036054841016070680517410100d03503501c00d07840d5100880c2c0700c038140322441c1c0302c0324141c41d07000751245403c40a0405040c2550403861f40315042801958480f01e48106540c1c0b2281222161544072004060440240c50a000680190710510307000540d0718000480d220400c0c051403170506001401e00b24a0380e41c820006003190001d020540c10008105003100b4142ca5200c6c141d4003030000b030b800500c002c0140c429910139000406580d1400703904160903601c8a0319000450640700f8452981c06030b01c1d07a41d440310701c007058041e003016030725155414540c0144034074265009614048c02a070b08218040781c1c0010984501c00544c0c10340c2c0001d8450407041040354404640d00140c40d0031040c002c686845c040121404940b030a0b00304600d500c3c00001800384102903480f407031111091900240006c03901d0002116190f41c4030b0300d03010341801000000107800386d016000055 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 79932366 1250 79931116 79931129
    0x12250f060506182a040e190b040228050708190e06040e040b06092a0409090813120203030a110102040905010305061b030628050301050c13050a03030813020109 70
    0x49403521100342c4651001c1070410100c4851024012008000741384110341c1940c611581c001c1503030b102d1085840381c1c000180c51340c030782441d80c072000105640d445000402a9803641280034242c6000071503403107102c00d00d2a0441c7c040c001c0c10031030480003c0c944410341e14482c110300e13000c50034945c22407001c0d2000031114171410303808100000c0115084039102646070080c0e000d88401c810300d960318024005503c2050303811220a0f100c10b4600d80c40c0582906000c0004402c0540340703400c2503502d0038000d00b91120540111048540420113690b420803c0d03420344010120300c00004a0200a500401e407207225400e921020051250307051401d8050075012500200002c4e9802c202039039407030820342d03190f07401500c511444120004000303100704207410a0364081c08004080c0101d10403070003007000640407106980d11100b450107200180301c0e5020301c0b541e8421000b582120741d8518421201100c942c500e500118400d00c9105420300100340d02c80500ca51010407181001d148032514001620100c040380d1160 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 79933616 1250 79932366 79932409
    0xd15150e240a020105060105090a050d03020f0106060314060301150501080c0702060d020c0c030601031e050a0b01060c0219030803010303050c03070f030201020c010b03011103040201031d12250f060506 88
    0x940701c014218010031200300168020444c80c0c503460011641071056616040d071202c1d982509010a01d002c048440c100c030b1003030040703408090f45d882c1400d00f920707034039800381c00400da48070f120811000246021a030301c40700490003082400401c0c08050a80d1b2b0460080604004003440020801941c42c4200d4100700c0c4c00034100c5840f03030f600c0305615019522172204025103028101031070007117041c005a01c50580e68801603100c4120300000f03084010001a400c19034017071141c29001c501103030070518120301a044698800c40d014600740184107403800e40c1090040040f80b118800c00c041202c003020380341500d0349450141c2d51011226011480c1d4010002c0103070000c80d80f20380b0341d01010740550080c030480642900074014016800101800c0700c8900d1554004241c04000080045d8800c3d40400b4504001e01e5107000c41f803540b04680c45c5420340c4454400c603c1800010fa4003401d01c4000b07981520707a00f40740c5004c0c4030010190b40e0708500c02140100104925211000302c1c89654a40c10060400d0034072201c03c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 79934866 1250 79933616 79933669
    0xd0b0310090803060f040905060c1c020d09030f0f0f08070c02040c0903110409021e03150c0a17070f0f032702040e030703020607270306020d15150e 65
    0x340b06a50058031a54400d0458426490440c00c0a009071071405401034044e024503910100f0503041a40110780702803880600303000307946041d905480503000710645220009203c0c0c8041c6030241c1081881314089007030107a400030340e05000382d00c4071b1580c84801c940c0c90700282c00c1d10b551800340e403d142c128600a44c080c1c1448071108009038000e48100031a030150f03100c1c00b04100707002c0503c81200c60a00300690081c0500e02400307500070902c0c0500310440c00c0941110b20125100c18a0344200c402521542141c1100107140140340f50f000184c02c0d07011803020b02c00e40050410703803070180111800e050480207119441d2a6003410750b010707038082d8071310705a40f00c0d40404e0031f81c1d41003d1080058000108911907490006a00702d106400826903c0712503064004202c2a100c0380019500031403460380041405000030305619a050b40c41551b08002c40c0f0920001d0303296200c1c00004e0b000e8030601d60304400c41c2d15924100300703c41c040100c10324250035150708000e001440700c6002f007000100b103000c40000c0d48400210 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 79936116 1250 79934866 79934873
    0x111f02010219030b030a060203130c0e04050c09070807080604060806070f090e10030201120e030a0c060e0f1207030e06030c0726030a0f0906050c0c0f0303010305030d0b031009 77
    0x2000000050307801c0e441c0d0101e0702d80080e021998010549600740c0d004120301e40000c0d070b080d0300464010703900301d5811a030100300b5513564044103103940080c1c20604044081c041041001c20030040302e104201c454201900d003000b001840c10800034009000c019281c400304400b42c50725480640600a400140c40310751514041c0607250340245001c82c4005a15220001b0b080250a50305500a072502046e00e1030152071b603001114150b81502201c039400e503442040c654507503000c00080c0400740b0b281d12443c00c61034440c1002c00480f240d180c2d144001da0481c001c0c50001c0440490340c400b0141d20000c0c120f84407801414110303200081310844c903401c02c04c008240401c414404001d00101403056a03040003c2c0e048010344030004080d145c4250780d03e0300074808202108800d41002c10300324001400050f03142825100c0c201602c0045c1c1e00341c601d040c0300148401c1401d40c1404100d42c4501c1060040d03286d545141d80b02c5580740315040e00040320359514030841d041139900740702202e04184c0504083c8840d00c41c504 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 79937366 1250 79936116 79936121
    0x16020901090c0905030102040b0904110d09120e0f010c170909010e0109061e030807080c16030b070314040809030703021306060806090603030d09020a171006050d0b04111f0201 77
    0x1041000c2180c895001442d441c0500854064950b010940d03802e00040303e0500010344cd410841031041c03c1c0074415030300842ca80d0320803a6509401842415081540400060546500048180d00910702c0e04290b032410790b04116201da01580c031081100b000210a41040114000c030080d59512107034400c0000f4034804050543c6040e5109220100102c9544d150b26070450032400c8841202c01040e8202000030484220203417002c0e5010345001842c042e0b84035a1a03090091080e520f201016140784103200784100300b030003150f00005030700f020041c0c01d50000140b01000d80080c002001080c0000d80c05510fa2014001d020080d68041d022000703148041550602401c4103004100001d04604002260391601e84420307401003070081c021798902402507610002801510000ba0782010782c044000039110490507040d0b13020308103140034029504410402c01e040d2200744c0c4c410b510680d0a025040c02103a052045a0f4125034016640c20122071880042003c800d900081e000c2500d100310074040320544c064 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 79938616 1250 79937366 79937381
    0x6030812090109120c0f0804080607030e01060b16020f03010c020a050f2e0b09071808030f0316020703020402030406060302010206060a0803040b0c07050a06020d1403040213021602090109 82
    0x1000c11969595912410500300c40311000080c02c1c0100e20540c4203001400703442040642800f440c0010f0001c4155207850300280d00662003041c3c3c030342c04001048582e41c1c4c148034070100150044002d01c0000d19181c55440240600781c1703000c81c10300490700a10115560300c11a650000d00c080c00a210395120050f02a403524a4001c09480703c0c095806201c221050108500202101020140540c107007a000305007070f150160100c8140541d501c0040008941e60070020b90702c074403490365600911030540075003940d607000f495010b20303442e50050200e031070402c00e80750a0300c0d4044d0411180444516034001c04070700c0c0c91101d900c0a500320384000700344010b0208503040a001c4d24000e07005c4800342d4680714248852000b003480b4041c40f9400911091113407540407001441c0c1000300004503100640c0340c100042c240e9503113074400405a4840840017020a421000c228950b40708100d0a0781145050b4000c26a29006031350701107401940000c1507182c0c5031032290510800358000d01515129a1502d80c88030081a01 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 79939866 1250 79938616 79938637
    0xc020108090c030d030506010c1704081b03060a0221040605010f0b031501030c020703050f0706090b040f030305070609080c0d03060909020d06050601111002192607050c01060308 78
    0x14006240340c074000603886010a8081c2c02466415000e840850003490301501880c1000000149040440c6220304090b0030f26000138080341d84d6605c0c00081c6880c11886030345001904409589807146030360003158550380500c5071000035958600c0003100804001d009800f1a80c06d10031b007400d1200b40003650740400d050704d503100d407094500d6807111502a1213010490300010901d680e0107800c01a0b5100343c01c003040101c6240100c0c1c800755102c0ea00c1e40e041242e8a00400c0781c0e6486444200040c03588480b9942c018007580c0002480c160420f400d01c100715045010160900400180c200b04110700395012103210350700400f000e900c130060400899161011894110700081c1031100114034030881d40700c0e200c0140d0707005008441807038260703030707114003034200103105c98148030000ca00d4041c600c500740120407111015460040c1d40d08907801125040344501c020003c1001180201c03040840400c011000c09964410901c001c1651255421203182c814440c0651080d420300200108104062024140c2c1000 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 79941116 1250 79939866 79939877
    0x7020d140d020c0d08180f040908030a0b0103050103032312040809030105010509150d0f17030106020f150a0513080c010903020114040507030201050a020309090106090509071809020c010b0a060c0201 87
    0x2820f0200541d441103c24064040c10041240b092800c09106800701c1c1c06034058440f1060121440010703007110365880302a16841340010030403100b40003030702c10343c00516001d00f0100301d03030350441e200113200240d20b0801c00210000c0000e80d18800c2103050540e0b02d0041140d1144e107030340c509482e02c2946034000c800801e0280d82402e0000c11035143c9001c120781301ea400700641c61082c400d01070800c40894440035041d640d1044003280d1101190308416440740c0c84406402c040d0b62075140c020001d10b00a0700144032410394102401d061400000da01000d500601b0311940031a01d5240d0107201404001d0030400200340507070002d4065402001900480c00e071a0090f0000c0003070907030802d10002e08860458004046402481007400198002c10103000c0c2c1b60b440e48122800d1010b82d0001c204246403e801502c0800c1e10900c08006501e00118010703440082803500d0501c0d03003042e501c080f1247c01140640b110240d00403c032203a01890940c8842d4495000820703035844695100c40140c420111010182e00141 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 79942366 1250 79941116 79941133
    0x19090f0b1c060b030a0903030b03150117011a0f120f070617150103091b0914061002060a18050109080903010e03040f03080f04030b04050d0f03140c07020d140d02 71
    0x101500c1070208640840744454655a1100f179035000030101040c0031002c1c903645a1021f032103510700700a90005c115145003050300c194180341d103580c6001007000c014801681412441d062903120034080c0c01680c0820f032510a4101d08441c00603490b0642000307a90402d100b2241c02c2c000421000400000701c40c8680c81b80461042c400c8010580c8000c200e44da0001d5048660400d0255442644182c800d540906c0748140c0e054083c40c002d044410495000414054591140c440c01114502d9080d801501c00c48130148422500003000c1e44800c0c2c001c1c0301040b525900c205502c0c80d03882400310300d079000d917000000700001d490b81e1a0075844e40d00060000b500944c6480106214104000b00710750940300c1c90aa243d1485246645500b0342d035105900302c1c49882014000003000503110401070340602e229002920b0610016200100500b540f140c80d00c08060400d03c2d10802d081c03c002406800c5003100c40e1460740c0707460600114940a24245e0003c00c0d183d08c1c016140c40d206400301d81e42d011000c01e5801da50351324 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 79943616 1250 79942366 79942417
    0x40305010920120a0b0907180c02010f0c080a2f1201120308010b030714040e0a0f051005060708071415070216060807030605060a0509150c0319090f0b 66
    0x245040b11032540b55800a004e01020800301194681d01111a000b110350311501e40c0b0040d000500011945034540e51144d85040d041c4e50280100e540040802a041156258881000f132800c036001e06403809035541c56001c609604590080725403243d00e8030000c8414020700c5c0c80c810082e50310002d4010b00c91400c0000110306c10310704038440b1a44540550311081564248441842c296001070080c82c1840b4031040160a2307150500701820007040780c04003500d0f0704c1c600940c0307140070744540b100c4009042d8038240801140d406804608010f03200701742c1da065106c0c0c170306243c1140c1520840c400a410070701c54080024168000040c0151400c100c07010b11103441d01c034018240d81e0341c842880c00381031049203440c0502001c0c0c800c265183d0700441c5468041041c5603107902040003070303000070185000260b000501c10030500300394244c90011010840d20a00e0140084001c030b03203e0081082013207256081e0001c1140300c42c0b00d42c41c40d82c042d000c403150f000441581d4001c505844d80c41445c150041740205000b1440e90b = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 79944866 1250 79943616 79943629
    0x131118031212070903050709050711060603030f070809041b0207080105130201030515090403050c160f030f0201050d0203010603140a020a0903020f0103090c080c01032403080708040305010920 84
    0x722181d000d41034141950480906500d002c01840c140400403850000800b24008005804c0140000d600c0081d15007803401005006070040501c0000d035601404c2884170a48000040306c0010342c0058060b034a40b805840d1122451003110b006c80d512504200c514038401c0e582152664140240f50200c6002580d0303108030713900340c0c0d008841d80e42c01012000f100c00c02550003500815444403070600303038034a030000000c000340b07a07a44240e030158001000480d540e42c04200400c905180100380e079441200061a1580c2c3c091408144d0100501a0000c0c4100d2307021640141c095030f02c0d00301101c006540320b68458800400034251034444040d1100c458001c19041202ea00c200d408044442e031350792490a0841c1c090240e2501c1040314107040698805a0902041071075841360045c000080103401080501b00004040e1060018442c2e8440e51000d000f40541114141100860340e000403001d48070400340c2040101ca001d01c4e40050700c69402d00c8046030402102c6801030000403421844850100030ba20b007400039 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 79946116 1250 79944866 79944883
    0x20705400e0a15020702060904020a03050402030f030705060a0c0306031a070206070c02030309040509030903010e160b0a0f0e010306030803011514210a0b030a0f12140a030b13111803 80
    0x8100240f2079000d580000540003492400c0c00640054540100d001c04181281e120100e0070001a81c1d6205010451805010101003d401c1c8002142495801d440c0e468a6600c050254484075a850a02c04ca03154000d03004840215000540c030428803000103000040c40000f19401401406010002101c0902440181c04c0c5241c0140c001c60801088105220040002500712503a42c132003800000100d580074028444aa114840942220300403d445008a42480d03002200c0c1c0c00401e0203a1095150702c40698002c80400d8508038020390394607001600100269040603068403c008000308200f8519200f0780140c90060f544c00e5000080b5401c40d400e87d0040d418100c11040400000c0703002c40a1f519819504035492080000b404c0c1c0d1a2400a4030708441c0700011280e03d20600d18682c1800f007a4840e000b405402410a81070040400040079018400c03a0700c10010316039108880444c13902c2d9109110000c6e48080c40c1000364080d42c0031507502c0d5800c0600b0800040c02901400007003810081580b15 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 79947366 1250 79946116 79946123
    0x140d031503030e0102070317040602060f060d03140d0204150806010201090308271605030d030605030604030c050a0b10050a090212010e06180109050709080d020705400e0a 75
    0x41409007103903001c48024007085422811131140050100c007040000e605408003145030038140b0ba03218074240001e403d1010040010000c2d82c509020084643c42e1001029a00c1d81d061a0a00303011992008000c1d2034000d038140ca039800b07440030602140d0700003c006030b03c2c07441d690303602d42d4030390703903585c1c0004909036905400020700142c0305101040218940300d14410b003100c0c0301481d07400d0240b255030b00189004c407440c448101b28641c07030f1410080b41c1810700850880225500c0c040c80710341d05240203e543c0b0b14000e4070003002c200007290501d05000e024440d1882e903e500c09040000d609004004030060021405454401c02d400c9a000403440d20b41e1086509400d50b032140d21501342c1c82c2c00e02d007000206000302800d0700050082c10310b01e1022507005c0e00d07070302a28134050000380b21b01f031020006147d0042034100d1031031680500150707100c1640000722002101c2040f622448904805a0241c140c00024180c41d503014625102002040742d52440c503014607820000d04012a004801c140c1b50b03100317540b11024 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 79948616 1250 79947366 79947401
    0x50904030507140c0108060d0c140f040f090b181f1b0e0108010510090506130b070303020d060e04081801020106080115090e1501090b03010209130f05060916030504050a0807140d03 79
    0x1040014200782b044110504020003e0b80c503101104086800c0c0c51804c003a091030b291344c5002c1241000100004907801c08076031601d195400d6030410402d84e8030110000c0254500d0000040541d40d903038141c000c24801c81c0f10070800154020060b0300a0300011100804c2804554030000102c0c06080c038003401081e102c0c142c0d0324401114600014410140d1054403405c0e090541800c02080310700290380105012446a940141c0da02846c444100850325076401900c92120302000f8003002c500b582d000d1350300031180000c52070f1f0420045001030380182000d40c814242075003002c2e0380100c4104c01c2c2d9a0303801214801c60003404248021011240c581990b1041d6810084103440180280b8240b0360128241c0100540010310300548500001e01d2400702d10f0300c040000b03460f0b10200c1440c00e030b280107464020302d05a82100f41c80c201038180e08449085509888209581e880009052250801840c500d40c2e400c80d032100e50310201070a0070741d101107103e40c0c601c5e20345c0319112100820600c00d208001c400403500380c92 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 79949866 1250 79948616 79948619
    0x607020d0201150e18030714010501060906050414130c03020a030b0d030912030504030b0c04031211030306011103090405010909030f0c0f17130602011a040510050904030507140c0108060d0c 83
    0x14800207103c0504807444500f05d0035010341c03001d40c2c2000200b16050258503c1d107248034451099500f5200140c0116080001d04041041603e810200b030f00c0c141e03140104402030841562010072690764540b21082000c43c1880050001b080e0940d0007450808420781c0c09001034128842400081d180f45040100080ca030104204120030f4002c84542c1628420b103031107403030241c0e691550306070804c05032010103081d0400101041004061001e8002440c0c02e4180f50f0880c1610031507098917800000e02c1541800f0860345803600071881030080707601440e00103004000c1540c481460758000c085443c03085010035070401a0503c0740d0300400d180140c40d6440066814007007101d80e10200f205044501c17006c0a55000e02c107020034400b02c0c04d8400e0141803194000604092210002420803512000c0d09015902d818140300040054170002c0c801d6420a481c500e035161030751300d400c88441c49400300c0507140000c0c000c2e040389403003000708204108a038241c1e1105280e464180c104140100100002080750121500 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 79951116 1250 79949866 79949879
    0x9090601080603030705070f05010809161a040302030703050303060103180c060c0204020702041a01140a0804060e0f120403110a05010203160c080a0b010801050a11040e0c1b0607020d020115 83
    0x441d41d00290260a490902c1c04641e905854800702d85c104080c00e03861080188080e50307206064941c0085880e009120311100e40d0200d0340984860700a5854400402c4042508010f2070750844005640c003802311004690780f400c3c1a5160f8006850343ea0011382040c0b0321300a500011140488034030341202240686619000095490303003c40c0e00200e070083c0d000d00c01e603000b5903034034800c900d0b00d50360484003946201400e800040000c05581001d06507540180909200b030f0780e004400b10340c002e6000300300040d00c0280c803842524200034040a10150f12484d04030b90303001c19003900030b0030459100390b1410044600300d4040104450b41405100d0041c3e000b40924488030494030194544103014484840c2216103c44166080058640e000c2e07891072021401045105424410b80340d00901c1d615082040c50b1810755550407621540c070075495015180804520b061a100701110460505242c3c01c518510f19030260607103501040b030f0b40034058000c08501140c840d00600038821040e049079200d5103910b06100 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 79952366 1250 79951116 79951127
    0x308070309111201050a0e010509070311040204080304120c0803031311180106020c01080619060c05011107061407080103080f180301050f060316060801140d050a0602090102100209090601 82
    0x50068990401d0000100d070140c036900f6a2030301c002881c20000c200c500d0f1600803401550b010218410840c0c1c034003000c20503629400314203001941ea002c50114207151000b00020060b00135508401268000007800041403500c4040c00d8031414030a0030003d210656801303c841e12030108540b2480008081d41c4410000303000300b0030100e00c3c0d4500170051236401c0341d030500390120501e00b40c002e840942e1080d204001c1c55a0018001d071b612440484962400c80361405c030980f500095072003110140b040c01d9a818003040020340080403e040d4403052039403a070b105410488060007100aca4440b581203005c0c04035001601c0b42d0040b41c1a607800484040c40c0903040580748409a00001c0600740c0365000328401b85a03640c080c024940541c0a11a40d40103908140c000c050600130500c0c000e44a441000c8410480c45401c0050107044480d4000c1d404a0950301c3c501140c072107040400b00a12074001d20300400100501a4040e04000c1c0007a4210740e260b0381d921400400301d110320060f06a102c412000041c48562264 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 79953616 1250 79952366 79952381
    0x20703140c03070606080c011205040c14011e021501060201020a020a1104060503100603020301060506041818020619030501050303040315090302010b060c03030411010c150e0309031f061203080703 86
    0xc4116403405a980d21108116105c2d85c100c40656007100c01010310035a07200301c1c000a010182c0304200314034181562404020f6010344111503001d00601040c2070385a00074050708440d50f070070041c2e80301d4520902200030740350484281c03001c3d8407024280000c24410320510036903c0b07643c138980042207520340588a111412075900085035105445060100361034400380f0140101016021000c1071107803d510400d42500d02c60b410403801000240010001c11300c030070400d030849100c0d118000440d51072036894080400300010000e904208005a1003513202e00310300c04142e039040565410026a42c90346d080603264459072102814620b00c0c089480c90342441c0354810350940307210780000547c0520404c040703010358104800d182d500383c10200810041c440d00c3d08140101c102d00b440c0065100d00b1a540c0d00902041c05202c0200e440c1c2d40c5c03046400c0311842041103a642c2c000042c05c882040c401c00c16a4024070f0003e40c05003400c01c3c1040000140c0d1803440132143d890b9941911280c0065070b138140110008d0032403 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 79954866 1250 79953616 79953637
    0x10e150c10020301180b24250b010602010e030f130509041a060301110403081c0f090c0b0906040612090602040905041a0c0301060309060905030c070f0902070314 71
    0x800a42212020400c0078100c100d240107400750322076140000e041c40e00360a034295841a03034141203091034a559049000110071000407442407204600050703601c201c0c0038044404139007001d03000b07800c04842244484a4070480c807c0a1245c0e0302d0383c841c10207c1c2070312203048503443d80ea0320038001d80b01e010a8010150807494031540c045561300340e6550007e20340c1c1c41c0030780d02130302e5a605101c40e080341d207498251360980c0100164028000100c848842c103800d80f00380c0c40064210a07021603101204d94450b5001001400030100601c8042c0d0001000e00050000541c2205d944038517820004940c5d1040081d5411114000c142c1401c0500c1c1050a03170700344080e204100c1c1100c0e510b01c40d00e80003603100d10291000c3c00b80f0b4000000c80e0302d021b2030010315410341c080180031b400b41c20804100150500c14126030641d04145004201751039a8917000340a800c2841000701540000301b41c1030903038200040c05a00b200c00c20940d002d821692120f8a078228490381c0000380000d40103030000e01c1141c940400030280c0025 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 79956116 1250 79954866 79954909
    0x30b130602070605010e01080607051914120709081009080304140a1202010207030e0102030c070317041d0a0605100903020d1a15030607050c0304030b041a04050a0203010c0806010e 79
    0x741a070f01d41c801c881d82600f040746004038200051003441c00c04c100c103607031022482c02e019140c600700129281c04250300700d8201c010085081ca141411240a0043c0c5041441c4800001c00c1ea04201c00040e04294982c01061032511408600402d038900300d0245c00f00040d080f9100ca40307540c03100d454091600000c06940c503514824207035102d0010344100443c1c00d50004550006803207800c1e5240007003600755455129411540300b481480c0744d203280402c10004030b0741d1207003007078141031801410700c64a8001d9a011030392846540445005141000424034460f008050341000003946032810416045102400703400001d059101c1030006040c01e06c1100010340c0110301703030404100c200c064800c0f08a812118034050391074414141ca000c0c00d040100d290040c00c9420321074203204c15048040d65138002c0c1c1c40082d00c15180fa0000c60300b80f00302d00080030004080b2920400007881d103401d03c42c1d41c582802500324000d61901f01110000c622803616a805118141c0d03800d40172040b030804001c40303411a265240d400d4603 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 79957366 1250 79956116 79956127
    0x3080c0a050a081c0c0509010c05010605040603050c0a09060308161104020706090b0114060d1802061b0c0103060b040909151a01120608030306120109020d060f0510030b130602 77
    0x301d0811100158510558000d6030710354609210550800003507200801d114140b11703203001c0d00c0b82c004050341c2d0200c60030b107000004202e0500740180504500c1d400640c0151030030402009100300441c48030001941954840101d5560b960104215000d030f10001e4800b400500003620020211514044903034082c000c803421a001c0c0c9800035003280d1146400f122095a6010030f1010098802d00e440e00410101c00d22074445048100403500602c10603c002040c0e03a99144106980c2100c02944190300303030040d10090700e036968801c0100b41c440c1022011041d42c46070f00564001507120b070085405a4003c011401e0802d4544091880a4454844110761003029054061403101d840d12844400d146800d21000060000c03100250440e1021209141e0241c10500b05000c1000004200c0703411034400c4d9905d103452104e110f4442c1c0100b04c219002540110f1100c205814050300707410007000030070740038010800780c0c81c2c2d2120000e410303800d8400200080b2094000440e001038280c071016626006030300152924 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 79958616 1250 79957366 79957373
    0x9030f080d1107050f151302150a0c03021009120c06020912011a0402070b01032405010b042d030305090d060e01020301080d050c0606060306010306090c02010c0e01020d0903080c0a 79
    0x3216958200b2400301004a0b0310414010100100e65403a002d01000e020184a1204210f01851006005061000006802008544507040d81c1502588101c42d51a1120040c2d03800502c0c0a84041d4260018402e24481a0701c420302440380390031840e4001c16130180c4508005060350340740c06804098030040e40c01e000b034451035220030000700d801c0c4d25064000100d04005040c00600c3d110360001c0a40601d1051000340c1c001131803c00058190b80e00007040340c0c00c4010f0a901d40b41d5800e9010b9a4510351030a00c0000a80000c44a01400607680310424180e90540f01c240104581c906014030311007201d06119003000400d01401c001c203444180507140220941c86501d03001d003030b1442c20040c030310b1903980080100001c02042c400340105540c05e2030028544401c66820035592000544080d10a9000001203030040c0e00030f0740080001c10300d0306802d010054000102a009000740403c4002003001ca20401501d90b20100344208680842e40b10000601c7c1152030b03140542d04100d41501c094804c1e07803180c9020 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 79959866 1250 79958616 79958621
    0xc050c06090705040c030209090112111804030906140304060507030e0d2f070e06010c141b0603010b250822050303030408090d11100e0306010e01050109030f080d 71
    0x11003450307009110051526080c4801c45900701d2184040605c14040e000503582d8244000b4111107141070f99058546003414030314801d0031481c6140c1d81c812001a90051a42d1003e496603106a009468820300e9559484007a02d07446414140303d1520b10301000043c0001d105603114540204140c0380028442d12941410f91500010130001008102c103074a22141d010614804800e0160000c80e45101d03847c1c0d00803225a076000d40b4064400310182034000500640d00c5201c1c6405025000100143c1290704110695100e41051070f1103885d00e02c60900352100340c20704d601101d0480312044103042c60040d00d0303901110285840b0b020700510316405009800810f00d4080580b0b01201c1501e241c4e15180d0001c0300301901c208450380413501a800900130480403070000000d80c4c10700e110903a01e403030084610307142070101d020300c2070301450b4400540480a00819803f9100c8203207103406070100d032980c1c0d8a40e005100c070600248505400560381c0d83c401e00001d144e0201d01070115200c0d0300e4050412100c402003105 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 79961116 1250 79959866 79959871
    0x310080f0703210c0f080904060b030114010305100909030504030b1512011407120e0706020c12010e0c06090a030804080607090608090d0813020d05060a0c0f02100c050c06 75
    0x85907210003024002d001c0504148180c00c180201a20390b6030181031000b030221040010058840d03440943d11100744450201120242180140100802501c030242246141c00c00e01401c601c010000f0406e00b00c0354001e1050780e0080b80700c0d04485007540c0c03800c01450b0151101c901d0031400c00100740800000110822045401a4200c1c0f0b88400c080c400701c2d050245c150000c43c411021a81403c00343c80110a003841c0c900c0d0480924900050701440580c40d041c0034091140311a42280301c0c80e000040d0042d03000c100d15569940480e06040145120092a8281c0350b01024581d4550000010b029613454084010480b06601a0143c224183c1d42d44814031580c1050b401481990090420024069880f05414010b00001c0c03c1009a9003850348955648000d0400d200f401d010200c3c011440300a0010381505d1031a41c004e02c414516906e5203003003500c0309000d031030303044005050881241c0054011000341000040c6a4010540722011740300d0074000d003901480420a0100030004041a140140031051 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 79962366 1250 79961116 79961143
    0x90b0706061706040f080d0b060d050109060b1201092003010303020606031005011d04032a0209060d051018020d14060907150c050313060804051009080708031008 71
    0x509038076201c014411014055422075450f00180100000035529800860391a0381015149803a61032040f101030040c404207150560019021a2460100f50940c00c00c1e03050b81d9a00c00144951035940d545010903001e20051621070005840060010382e1a551042d1030586480803000f000d8170180e40882095402070700b0690058002004001c024141000311305621819403104101c03c0d03240500c45081000246503424907030400724081014540b143c5002903040081da500c4000100c1e5011000da80b141c94844128041c21030080040c44501c1d103031109500040d0003402421100c80794814441c020407141b1901c60340c13814400680005621503440f130980c41d910800121102094000d0070078a4500d0080000116901105041c00b000f4000449010880740131700b000100d24060f454030030f04500449030f00304000c01c5a034400044855100c3c10303443c042c900520607554050003841e61081500c01140d4050090381c0b00308190350004850b030f0b008550054100d44920300b1141c880424a0600f03841c0d07800803 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 79963616 1250 79962366 79962371
    0x2040b070309060c030c02010305041b0929010206010308072a081006050f0f010512070207030311010e07030f081603030c03060501030501050d2306040609060c0503190c090b0706 78
    0x104101500032106001038025410301c01d002030740e6545e00508440d00c1440090405440e4404101000060700b8441000e00d28034500303881c195200d48003200285400c00041c482d00344031000141ca0401c500764a039002c428180d015100ca03030708507101d408a03036100210840700c0d03070a000c01c85581144101003034400449900300641c0c1c1585052880c91030b20301402510b258252500c80200407690f81c0c000700c05107015080d500c200700c43c203815006032003e000320400c81020765021020406a45c0d804a58981901d229444041101002c16829401c9800010100e103a59208107414804111280009584148180d031107901d0300134142c503103400555401ca0308802003619200c8140f0f04903058020400a08000c0c40c0401c4150315042c005211a8402480601848000540449e1225070014030a842100480c226965410300749070490050000710001d54109113404000302c03406105200312402907910015980c0300c0150f0700b80079401004044001010f00100140020712480c50b20f001c0c103e0350b400355500 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 79964866 1250 79963616 79963627
    0x6060603060e07260702010e03071b08060c0d05040206090303130e011205120a0302070c08030901030c0906020303060f01181212210c03090c03050f0f160501120207020402040b 77
    0x64403003540300908994280302d5501c62a0a00150f00c80f08003040440034413002e0000c2d181c0349000ea00500b6100300440d03040c00700140d00d02c2404850400b00b10008507c50303001c0b031566540e010031512034406036546a5114810801c4400820064101c10f0308203000504851802c299080002c3c6194860141e0707403c0070690a42c05c0000b00000320400340140b00c0e00c540f5184500440d6581912400040c0107100700070f038007003803007100d0510980c151003d459000e00c1c2001e0043d10b507644555a40c00040885000900300314001d00e84030322402071042150213a400442c110b8640d2010024100041e4100904115982504103079890112200c00024000c0413010390740c210b06410064010110505a00207020241d1145d00940804c1401005c8460814030000380703000040c1412006007510340c001610751038400302c3c040184000421070508548400c0110b40410100ba000c00d5212000e038030300b107140346e60210410031141d4003d401e00745c0c010800c1400107140124560001c0c2c200d80040c0c02c2213115010100d41c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 79966116 1250 79964866 79964879
    0x603061b090d030810050105090604061206050303070311011802010e0f040e0102160309050d0506010b030405010b180a0509060610110705040c030204050a0b07080702150c060703020a020c0f0604090b030a0606060306 94
    0x2c840503210a2a0040c90485250081201440be03841460100005034a62040c513003565803261001c0c1000a083d42d075500c4081c00c00800d00039a088003d0f0155280860307040009640340e07012068142c0c180c5801c00c08071030305003c11404800d443c82107600300f601c42d118001000740a200410701c0105022400b14141c0503810b008140070001d4101a002d0b000d0790b40b030306e40818030000c0c5443c111581250364a5480c0c0d5189401030260404840d05504945204205007040030001e8045200b85030f114401c0105603281030130700e030351481d080c2c5030250092140c44080080e02e1196482020301c0b180c1d00e080f1803240d541c0f000480c0481703031910303034842c0020350208061020340b4002c02044010424151524249400b03512941280c4c85039980081c4941d901d240d40e42d102d08044020380d40f40720030400aa84135450b00078005406035004044c0b1600500800d45461020b103880120380b900d2002c0940b040303007000d060252400081250501c0f1300c1c2d2521602c445000040c07554041e60f00a44002d03a03010442c18544034 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 79967366 1250 79966116 79966141
    0x606060e0306150405041a0405070e0604021606020306190803070201031103011a090103060801021c05010906240306030b130b0705030103050d230f210603061b090d0308 74
    0x314807a411210074014592140c444402d0741c3c007400c80c1c00040544039440c01038102030003610000c8450b44400304002c2031110108400d0126401c0400040d03082c0e65650801040f442105026120b03840d0440c140c0c000b180059010391b42c01840076060110003d451200100b01103c542d2243c58150720000e9941c04550b454050021808101a2104e04650521a0b000903449000200c4903e01c08089a800300303d030b1003034002c07000030103094000f15901c150080d0785800e64443c5500300a04c05003040700021365000ba07480380d001203a08815102c2d9600d5600b02d080c40d00c1381441c5004004250700d603403021002c6001100c55074003c03d00f91003204a040d02a15180c00080320040a036814001705000405c0400c6000c280f86107002200e2520446080c0310ba580f80030310b180e100e8000d90414074081101390680118000901d100c1c81c100704c1041a0710b8225285560840d8101c41d030642503004400400c8613a00c1c0c40036001c07100c921a200300703814404984045603508a510300150002101441400502d85045 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 79968616 1250 79967366 79967387
    0xf0619050103050a0f06110c0a02041512170403120c0311060408070209041b060905190b1c0b090720070602030a11010f0f090b070503011a1c09060606 66
    0x68000d205941c07441c0c40c0d49884141440000e40101c1c20030b443d6074100102507100780300204103015000d0300c1c0c110010720181e440300d0450040340101c0c50700e510203c204104600c00400c0703544180209544100781d6481040d2048041b07202400c404080c0404000030380e440120888040d0340355075145141d080707420020220341c00003880c00c4403038000e00c081c000418a1801241c0d1499019100f40c405030300c1d6880c001100503078083e50300d40c0d5501380da10041569984844040100e8100b1144030300c0b40c2c210361030260302060840c442c01580000c100300c20284021800010141c0390000f80700041c0401c200d201044c9010000c41e035460001d42c03000070042410040103520360b015015500142075007414403401030354a1140c006048184040ca2444032031003102504400d00c0520381100c10302c80c00d5600c41c2900081d05020b50708440c0c18101070b0000e0325551044c0e054030304880101d01080408281140700c24003d41c044094000f100144904810005503d8083c0c03c0c1c0303c0344039000001d8030718036100c030040866410707 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 79969866 1250 79968616 79968661
    0x14091803030106030b2706010221090d051504030c020411070f0305131208040608130c03020108040f080324101709030c0703030207050a050103020a08040b0c04080f06 73
    0x4284540501400010507241034a07090b08001a03126180ca0018803521a08001c8031101c1c0b807403281c541101240d13920b0040c0142000e80807541e514a803052000c090300c10410002d03c86c40c4040c800d0300114a018500e44684900600c140c4181c009003d01d13510710110115415404115403c200008500b0688076903250103007203806540c109076466440c64501e07041c07081c000d010084040f42c00c1034000402e0700c2c18001807a00b12451841c40d1414a414501a08140b05510100e80800005018032401d50592101103512118041301d280c2154015142058080d0068448400340306086000035038540007140070350344042e054039904407c071951a000c00019000c181c0a0815081c0c41d01e80306030440c0c007600311411b54902004150b0b44e1350001911354040c1048055041c81540303000020302d0f401040304425103405840d501d1001b1703140c00040d4180e1182d80b41080c005480100040e0105800746c0340b80d50413a040c540d9041c0342a0750340445070314000b0304009400c081d0704550140420501094004190300c1d84 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 79971116 1250 79969866 79969891
    0xa0309050f0d02042007050f0c0901030b1f17030c070b1602040f0f050c0a080f16030b0307030510020d0b090112201e1c0c0510090504061409 62
    0x76440d0110b0410240d03408024042ea403203150004c86445c2c8000a10400084003401c1a10340c84142405650b4061803104180315020300621402a41040040c0c09e060325044078030029030381c880c648400074003800741021b194100400072012811900d0341012500000c2d0443c02541c44121804071a030400405520840180d00d0400c014102c0310042c20401d02169012500080c46072000740b11540684080310a80010a280008104281c6407180280001c10f001e6500c64805030b584030074541845109803000300d0040e10014602210134465004051038840c0a0207039400b160fa20355682c0d10f020b40036005810580c0d0042070884a031000c0744101002054111881012540340c41148611101e510f40058100088690103040114030203103180482c94010340383c440d510010a610b440c822003842e070124810074401240e804c1c0141e4078003101c407000360441e80b06e240c110320700020025021800e07070074030052040720a00011142d0701c5200d01e000401c030f60710f880001100d8800402120a1000f000d5820790b95 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 79972366 1250 79971116 79971139
    0xa17030a150e1303050918041a040b06060c01090f14010c020316020f01170405060f070e0f0108060a050604090516090602032208160501030f020a081302010306030b090a030905 77
    0x111034078080b6800c1206802208070100781030804440610403081007e400c940320503242003418800b10006482a0702030036543c01c520802d07a2310b44210400030703a03004d010304800340042122840c00e540149450700b46100000741c10700c010340e81c483c406c1e0500001558414240c0440c45400310080c0551a1316605902c0690b2501e00d9414002040c403030f00c240c000c1d000c0c080c0c115943c402d5034020980c000e14044680214103192400340b8101da519a4112555040c16000c20b000c211928059100184160380c0101124800840f060044071590402801c10740e00400e180d400158035240c41000380040c2c1014040400d5520340003003850711401d0041900c1d020000891010041c1540c0032050f40c001c542e40d440060b90b00d140d00303100d86481c100c080d00056894058044580e040c20b80f18000c9104480081c2c90502108418034041c000702e0094916400c0468500e10000d00d000003032801c844c1c88144141000030303005441380c554590a15045811286e26805480c00000349504280300500a00c01202c0741c06004 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 79973616 1250 79972366 79972379
    0x60f060316090c05160f120906050712031d010605090c0a0507030302030c07020a14030c01050903030a110102130608070923060c0a0506070201020405010e06040f170a17030a15 77
    0x14815807080316815555440505a0213204004441c6543d1602c03075510f205002500b000c2c0428540f84500b222410203c00c1d0150003103014840c0f681c2110203d407035050400300c140d12010f403030020345c8a00404150f9500100c0781c00d07040c52418400e0300b1070143c00014440d410308082c0584103001508280344074005100c91075a0079404030880e82410f40c14030b000b6840f61150740388401513010740d0718001e500007407905010540b80098020082114000c90488031042c0e080c1e00151154032070781902c0e41d05a00200a1924024052098480b024600c07000041c90154030008000c440720301c0380c101c031000400540502c060140e101d94048041c121412441d43ca20041b0840641c50f1000380c030a9038000c40b40400d8010000c001400702c12500c1c0c1c1c10100340c540d0ba2900c1e110081c003c0d8000d0080902184669802a005007000d40584003601c504010000c0001e050201c0d07a8120300340d0030344480c0d0394801e070b03504a800240220030902440c9a81c09001d0303143c1c2016031424043d034034403113881c20a0481401c0100070360f = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 79974866 1250 79973616 79973653
    0xd11070807021c02030307080a031d210f04030605090d050a050412110405010b030a0e030909061917030a0305070804050705060a05070501060b0307030e0a1109060d02090405060f0603 80
    0x2940e07044981c1d209466100f800380c0080b009200010394540404206242800443c8000b07090000d0160b404004c041a042c21400c0081000c0000205952200f2501a078a154401da4952100340f005009800c25440c031030729199581c8070740c004441803900c80703041c0092240b0801a083c107203002c1303003440380c14500d0850000f001d40c0200d03c20614500005403901042c40f20074446103520403070207002800345603100c100300e064544c0240d0700442d00c64a03143c5d43d02000c43d400300942c3c2e5801d03001030002e80d04d5154130081050420612400b0a01041110000584020324100c10707900607115002854854200d0781303024080780c0c0014003d205102d286001c00001032004900c060030740ea0120745050701c070203011000316050300803848001e00542c40c0820104900350b184002d540f00f01c685031f03424007a41481040d03158441800300e00091034a040c00907841e00c18502400b8841e40218090a079808880c4681c001030543c40080e00d060352250085414402d110030364200180d80440e0640040401d0003a51968000 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 79976116 1250 79974866 79974877
    0x106060806060f0715020405100801030c0609180e030405030d020609060a0207050c0904231506010c0b0f0c1606090c050f01120506120105040503040f090501180207030c050105010b0d110708 83
    0x141e60607080171385050026a5041d9009404050300900301d239044035101800f040400c3c001580c03004245000042c0d03103413040c060401920451074011440500c8019680068015080e81c0b25180c001440085541d440410001c60304500e03a034010881420007810043c1058009419880040e00401000001ca03100207140303219103505850045480e5594149007020100a4941c100440c1c4d0000c031a4004110001d03c19480c40c16690304d04401e9103416005403114103c1020040c0450b00c1c10002a80701d400322280c2c3d0707074090010b44583d8500b40c002c01280303000c240d5481c81101c1d415074501005043c402c49414200140c501074030140000351015001800c101d0680408222660f101d200080194995141800c114a0490002d00040c02e041c03400d1500c0307400c1406011914025107000090b0721006014440c102da4140078040480502a011600654400071085c0d05200380200a000000c0703003485424001c20388401550f81b00c40c030520405007511052183d510780c3c010b050100300041744d120400c850 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 79977366 1250 79976116 79976123
    0x10605070f02040603080d020c1b09041e02030703080406230418090503040e180c1503040303150e01080f070f140a08010f0207060c020d0804030f200106060806060f07 73
    0x300c41c02424030014018010b80d17040104040741c089102401c1c1c400d01c2d0041c1441a11803810303105250030800b00485101d00403461282e0045496000c200801c007013400e5106440162201504070000d180c000c24940740c00e541c41100c40f0140080c0801c20b00e40c0c03000301d045607941701442c082443c1c465920720386440d000b14025000c122404050200072603040c1e42c046003601c0d5000781902d407a0b0f40d680700711140048044400200c0010102c00680090070003003510700380e03464000c00c0240b021111200030080d9800082c401c50901d43e6070301c40c0402c00040d00c0c032514005c080e4260400420340c10201c009040c0f128030202d20041e41d1254209002c440010b0b80c4440c01d0f02d401c4039082040410741400141c0b80320300341d0b1120005d54079080034078440d00042d40080c001203008010a129050381d000d030407661030340303548055030004050102007000248107141145054140d490802030020b111002c21166281c1034070100b145030340d5148100030140e000b0358406c1d4440390842d026400c14019003000c0f003c92281c0b03940103 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 79978616 1250 79977366 79977383
    0xe0f040507140613030b011a070b0c0306010c06050f0402030c06121605040e010902030403090e041509030329030d050901020316031809021c0209010f030e07030215070b07020601060507 81
    0x200260b00c83e0802c1d0f902503110704a07000d007143c0c3d690402441c440002e001300a0b900075000a1200d0342c5d142c0ba001c4403101580b1400c103d0180d40c074000340b424540c0000c0e01c8507040080e5a1888400700d01c440c0100360181203240010341c0c0e503003083d104040c84e0605003041d441c040c00091001c0c00c02c80d0952082d4a501c062121024010f066800c9421940ca12580c0c020b002c907441ca401c004101d0f140390f680654480e40c4207480e0850015181c1c02c80c0c400c005000c0f07030024040d400d04034030410f10140c01c0d04051421440380c1000b09081d1b01b08804000e219103c00e600030040c1043c070456400600e410401e00504003164181180741007070083c0001e40768407480d00d0400a83c044014100109403190750245901110708106144450301c48440038041c2d401202c0f075103a400200d07a6150382d101d42d103200f11000b5a1050b1917080c079840c800e403000e4002d000c1401000140d405202c01c00005a16545c0150940b88c0800c10740c00e41d503a03801d24000303136441400fa20040455011000610403150013808032450141c01c403003503 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 79979866 1250 79978616 79978649
    0x120d0207052202040e0106030e0c0d120e0301060b12060a080a0f030504080610051002070e07030b0a03060216030206070f0e041d0f03040503101a04020c071203090e0f040507 76
    0x11014142428900846000e20004000071400c40034074000c6d040e200e1940d018841400a03040b6566100f070400d900c5580b00500d91481030004480703250303e5200716000c1c207000740000d0007040040d084420a910210413280001882040d2440404096902410842d10a003455041914407651b492124000504011803c01c00700141402031003554000c0c10b8001c2103c6a5240144918401351410f00c0791900a039081d00010100300c1c00801c680080d9074548080d00e800356110841140540848040d894015040c3c4502002007a658002070001d140c141000d002110304a2900920302000100020200803800f81500603043e8070101d0103410b03c100700c5020134116000710460501e05440b41007240070b4428807078541281320303006c4080c00c212003040341920302035184d680380710701603800b0182411230030f89c00c1c0c1c41054501c0c40c16030b0150442e9501e035800c941c10251070310170046244110140940114880d01070800c04091062072103a8043e210b856088028100342e510580d44a00d140205490001000107 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 79981116 1250 79979866 79979899
    0x1b0a121106070c1d0604020a021b06090301020d09030e1503040b0703060e15030708012d020f030709090501140f3f010605040c020a0b04020307170c120d020705 70
    0x2075030b0840d6000300303407070008a6940a00d80c11601210030402440488080052251319040c4251043c01c1030540246c145c40c0c090055240008550030402540800c05003c2d40189450034805081040c2d01e4040006000d1018280138040810b448105131280200502c407a41d44010340044e80e41159000d44850b05507203c800041d80605695007000c240c0400300d008000e180b039030074910321121200560603161031980b95a030150a03100d01300024031030318015204490084801856080c10a00c4800c0011f0410f03140e0503074860aa84240d07003440c001800c0440910901c920b51240c1801040314118514921724410045000c802a001d1441e22445004004030507140101010745003c404481d62015200342c25030042c0d01d68803903a111024558030303020000c9042e0815224000c618081e640048ca80c1146075952182d13840c80042c81240c050240d1000059000030314070040c103030b07054402c014044242c02c48051002c558056903c2a603e544414840500300390045441001e03608141c44031b040180d035406 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 79982366 1250 79981116 79981129
    0x504091806090503071b0807051203040b12090708011404020d060906020a0c0311010b0102060c03180a0f02010f020703031434020a0614030703051f081b0a1211 70
    0x41001e07114908112141c0200400400148202840381c414401c44800702d0070488009040e85c0100d800302c0c0d01041c0140305900d0080001d184170020003044a141075287c449080d441d070014100c80d805d52201c5402d10080d8041170241030090603190303008028203010644805a0700c00040c0001c0c2c0501680200b034000d00406030480c2c0d10607a00001e00350b551300c000001c001c041e82c0c0c46903400d60000700b0030a020051900103001d800510001640100b1043e05d0f152a805103d600282550305002d590784859019880107100c0c03441664000c001039103010819000152140028031030707200841d0400e440500010350094076040f0852100000ba40d20344400c0c0c0c192008080280401004801000003144030100810f488500b030544240c42c1e02c85003e50f904819039640c00081191010300c5000e200182d0340034466482143e114007000d04040740d80050b0880c090b4161416003040c989500980b0802c00c07102409140944400401d442080082d40380c030a2510810741a804020046001d040e0000f850b541d0f1507 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 79983616 1250 79982366 79982411
    0x40f1532090a0308030a0e061501140d0e06041a060108011509090f0203150603010e07030203060d0b10030308090a150e010b120601060207050d11040b01020f0304030605090708010903050409 83
    0x544050041616030900d84c105400c111815660f00d424040f84a1340801c000c901d150250108610280603000b8120054034a540c1c400107116150400f030150342c81d40001405001100c0d9640c03c041c1880741894245a01c2810007215160048629502404505c0c2d1340300754520b0445009440c40d9184000e84442121b541c2180e602ca00703a6070381070001e114110b60b050750041d809000e4030320b0741071025003141003848294042440360001c02c1c0c4500c00003505ca6406031b0011644031900030424a0403c00555070701c9a801703801c0d030f0f07860f05045c078030300d000c1c2300305500301c50f03650b4120b440000181103424a0b86d992501c0305100074824004541c941c80f103050000c60941001c00b842070020002004154001030180d81d42d5030911034040184290880000c460800041032081c0c0e0740c06c200000f00d110b401c4014440a0038564400300d0440c481d402d0780101d400d03024000f500107584104004140e5090080040d4a80a040c2e0441c804a900d0400ca078000290818100d42c120703a10310b01d0126030380c0305d203a1010180342100c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 79984866 1250 79983616 79983619
    0x1f08070804032006060a0e0601090b1806030106020d18080d0309080408030c0d090509060d1103070509070504052806110a020d150c0804110609040b0402040f153209 72
    0x31254065181c10002c15014440e00307041e640254140e9440440500038a016540a40420310303140040c40651040e0008001ca00cc441240015200c1a100030400c558401da02000c010382040c42501800e960226482146050a02c600162582850700325515400464042c80c01e040c1d8030441c0e4802c112030710050743d0003015518150fa484010421080713445840e041d405000141803a48007041070719101d4107641c0201405002424444c3e103d94401244c400051a0700341d05100e460b000240564810307580c18401c41c040c1c0d8680d0b4036540303000184047e0600b4001d01a0035030002840c160034107040c4000304012944c0310b00d4400d070070515008940742010a03507080a03400c4640e25a9100074010011240c80100182d031408202006904000312030003441510000e0090140d406145406d113000405058401c1d80180000b440d0141000094100e83c00759011964191481000b0089802201c011251040b20342c208000c4404440019102c41002206084100c1900c5251488002e002c0810760b000d81030b0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 79986116 1250 79984866 79984907
    0x1090510020f0109080a0206090d120b0d0506101d091002070f08040b030f090c011d01030f05150405061e0405040f02030105040b1b0408071a0f16021f0807080403 71
    0x11030034a5081c0303610a002280151207160007280141d4030010703518503007001d2969480c560b81c160742f41c601c010781820f181040e80312081c1c04200c0c0104405105481c019491180303d0032150303142000c441070903c1800a081c040702405070820025100101c3c11980301c24035054011784d00d00d0700e071600445440038124003400b10000401d0204c0e00b202054000c501500454200d2050f60750343c004150341d40c11200c4082800901483c1e13074220304005083d410004901d0504011410130703802d41c030303030802c0b12000c44400381e640c201c10702810103d050900c201908404d05540b01300300150441c0c8441050009024114051540c401c005401e120459203a0150158001c0007845a81828200305c400200c054850111602c0300310304a440300d854a00132141103c1c42036014207c035524041d001c403038800c2c10342502c0907000010008050301d0150075005041501103c4940c844c0720300c103030050114201d5a8414042075142c100c00c20091a41c114810550010089c6003486030b941e103519088541105a4903e482c0549 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 79987366 1250 79986116 79986131
    0x7080d021204052e111006060210050a060512030915210a0f09050c0f060a090b0c03090a0602160504020301030c0509070e0406090603020f091012110d0803061c0201090510020f01 78
    0x303501604c403080210704003048448030f0206c541c0080440d18207124050147e8808000304517652001c1d007040d42c0c4211094070000301d0903590340118500e202d110942c1c0000b41c00010715a0000c0c034101030444054061403007094100082c15210700144d1044880921070300d40c50500141d40e455058000100301c6202441c02d010584041c50800e540c4d54162041c4d920811f4410298002401e14000340d40802d0300507662400c42034645001c03005694051181c40120340001c0041200980722030f0044402490258020180d021200c4908010029185c210a110750300420041020032500c826003000d5030701c112010300141c0c0303401d0320903200c080444607a66001801d001300003072044101e40c000001c880c003e4600c0000400404100544103c04882048040542c00c5062146600b9540c3d402d00f058401d02c02403c80d0031a1500048050028a6040721154400806c105103400d007605400344e0203419000e2403498002d540d00182100003203000307d0740150b0102c208030044ac0d108224140d00030038107000800602 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 79988616 1250 79987366 79987459
    0x20d0c060e1504060e06242803140a03020a0303020d090204050c13060507050714010903050f0303150d110114160c06031401150c0804080f07080d02120405 68
    0x1028202c6040d2035040c0b404145ca07401e9200420544d208070b46024500c02042a0112004240c50101c1c00103034010205030001e102c150280005041d4200e81080c48140c81403541c600481108039504014400780c1211099500080d00000c01040c481e6041c1405600d07000c2542401004224800380a5400380c100300500188043c00c60041014941080382c0d00000ca407119070968440c452204c00130902c1c0e1120b2420415070054a14410280c00c2c14506400841d40d00d44510b0328122900100209075000007007404029544110a414040d5054500d40484041a2515100742502107000f505000340001c0b00307821040400301b1210071070b0007800d05401c0703801c4a0070451729000042c0540381c04686070250100c2c168190b015598100c0c1e40841000803074038241c0c0800c442d40344142c6012a03c808007403002290f00700090250120b071660880c010644070780fa12080c40e00c0c21034a000300b0000e641002103c9400303c2040000c65082c1c900a403848180c40f03002c44861321840c25110103125a9802400041810 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 79989866 1250 79988616 79988653
    0x806090a0219090315090305090f03150f09060601110d0e04290a060e060417030d05151503150607021801030f140102040e151306150909020901020d0c060e 68
    0x2070360b005400300780c420743c5003401405c22180002000740c08550180188812464811400501752202406948450b459040011400302d404d8405c3c2003034000d0801040082038081104c0e42e8000c109180189030040000700a5486020400c101000c12800014000603a19540c1103810700108610400002800b801a012480c60f05000090301c80c20901c04005291407040e01e03842c0300010003c1c10b00f40360071724124500512401c4400354003000e010902807200c0c003040501c03032181709602c1200883c9401487c1c00402803c4190580034044541003413090000f08488503510f0000d90005458803541e5010b42e00009027402c286d42e03544c01d80c4140d641c00200411213070410400c44184521500507a02031398403609400d07402240218100103188a002600d0100002ca0101d403140000c0c11159a081c02907420006a414907000162001c40c0c9180b00b0b0952580103031200d0050241c0303c400c504005240000075102d1300c252060504001c81c03178562809000e510303445812611007850845a10b07040da68001c506 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 79991116 1250 79989866 79989869
    0x5012a02030619050a050403020d0503100b030c030103060e060c18060d0e0102122d06120a14190f030c0201050c070906050406080105070f14090306040f0b06010f0806090a021909 78
    0x1401d0501c40805c441d52036a010301c0340503640c99006072003400019182190a41c02c02001c00c00260442000001c181003410000c5000e403244204899907507045040000079208401138424440c0d01640402c50410348950565000e0401d260400c142c5080301c0e00014a6800f84000d4404040e150840f03540d0000f205600820070300000382e40040c002d03501c11154031144181c600c50800070a40a078040440c07864004101980110000c090100101c10480f4161802c806100c08072003114104811902c00d00d4100b00c001e0807103400701e107046044c102c19074038040c440c0c28120f4010103000c2c2941e03400341168001d00c00c0d01c080218036000c4980d815566800070029050314420b00d8002c0c1d00c2c040d008604200f040c0155440b0b0403594441c9881c150800e482120281480d0303400081c4054244501e092a54043c0220750003180500b80303072a0034481d03600b0640c3c0b11b09030181c50345062211b4021a1028250050780301607002c80215207901c1565102144080a0300c21003e00d4100040c81600900e503c1ea0400002da0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 79992366 1250 79991116 79991161
    0x7140a0203010b09044b0b06060c150402040b06030a060e0a020a2304080709060e0a05061c02040204091e06140a03020f03010902033405012a020306 65
    0x60f20400d030041c841c1c0407900341d4000e40a00c0820841265a400b451403040101e0b0039155a00320700c0307040030044900d41c00c44441004440d0304d49079080f02402050268582c0145d8120364840c540712440301c0c442c3c2d4944215800d190840010710000c2c0655845910000610741d01505e019601d161010b8107400820090141c007030610142030200c3c90303c409a100b9504000c6180d2501e2190310041ca1000325a4a10415020a541810000407640c424240708100040c02d26560104146040c250502ca400350000c02140c9110300e07080800c2101e590b03078845205004d000600c00880d4000030b0000c035019220b140c00c03001e0071a0500000444440361000000484200040c0400183e034a4021000c2403001038070619038030601d0910180b01518000e155204000e4004000080d081141e9000ca8105202880d111202040306512000b540064140000300b1002040194402c40e04120003c7c0c505016010b100001c01c110082c1031070741340174103104d03203441c2c680081c11540d03503240407440e0100303c11201c050034 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 79993616 1250 79992366 79992371
    0x20607020102090612042f010801050f010804150e0601150e011d010e21010204081605060d0f0902130c030c090b070b10180b0f19030605070507140a020301 68
    0x4184600c18400e94200d450000c00c107501e0520454510009000c01034800d0b180306403017020340441d0580c40c0e52101c0240101d000349070b02d104448000546161016030141c1d003e07150310b4500c40710681c2e01100d55680b00b030307100b05001c00c0100901c103210020420040d800b261441104004107108620703003880560075009a43d10f19480d0503510044950605901c0503008010019104408960242c0181035100c000a00005130128024888800350019018034040756580000c06202a800601426403030328841544170700c006192a01290141c41030b45000d81c0c969a0311080c41000c000c458021f00308164008280200108800e11201c004025110642002c2450700304080180c034003980441c0c003201e500301003c9081c0800c40d02c0c0d090110b10b00610454050015030404505002d08071490b000c2450010000035080d4400030074494401060040c0d070f0b10590150800040d0250b0b4a5052800d4a60107100450030b40c49042080c1e400b4010a50018100c101791245468985400030340304150314000c80c001d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 79994866 1250 79993616 79993621
    0x7050a060509090a05060402070f1208071806230304030e041b090e0c1603020601030203070b031603090203030c0304060305040b01091803030c0e060a020a05010e03040b25020406030506070206 84
    0x151603911862804a400c039400000080e20004d0560103a0341c040c0c80504058034011003a0b035400c4c04280000302c11152060710000c00d0901035032001c0102d9010125040100010740641850001540350784640d10800c4260301268111111841114900c0f903149900310342c42c0e08203032901509103100e90b80c3c001c2c000c42c40c1c40400741894514046e896504880c42c0c031843c1c007240c2801c1c1e4800354040010414242d07030504000d0740d0b40402e0b06011010f001400f903805441e055046104250900030b440d40070f101c8910007881402000c07030740200c4440002d2441d0a001403203851034404039096000b003110480c40c1d4080440d0014407260143c05c124412446029000600d03a02c40d10a5000c8820189415049582c140c00d12800070b8002e07802004070740c5190502c80900c10008001428951014a40c80e00680040c024001000001d0141c00485170640c405142483c0c1041a558158050001d840300c9860340c8242c20380e0b00f40300c0901846802d54010f841404a940c6900b00541d4460f0184c407010014440c8400 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 79996116 1250 79994866 79994879
    0xb031501050a090302190503070305101a0f060c0f01020a0c14010603080703080c040504111b0d020c040f02040b04090603050d05030708010e071b05060a0c0e060301030b100b040807050a 81
    0x101c54a000d0381c0d494140e402400e607000d02010310310006c3e072245001d401810200e1690340400c40b8074000d501c200000c2c1040301c44402c2581c25500c0c031120701002d00d05101020542075942d2130840001320000e47e0708503228030410382ca4514207500c2c1c0980d0a6194800031311104030f540e00c0440081818003034188610310800e06000300d8205e40041c071001c0c0590381c05001201c0024414903840d900300412040d01800c1039120400103007150806105900680c10010701c3c98016800340d005128148110005404032804007400a5185c0080c1101103218960b1100440c6070802c5540c1985d0203459a018103980310390b1942c4030140103080c43c1c08280c0702c501c07940390982c0c0020310500403284241d61a548088260b480c00609e41c0c041540681400c2c03d01c54000f140158400c040311400120030b0042c40104614101151004200c4200707441001c00c10541c1426550b182d01d82200b01c038112580701022a443e03070342d6040c00c80b14020554020842450b80014001440c0000080c01000d8130000c032102c0103081c0c0d0b00d00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 79997366 1250 79996116 79996127
    0xa060c1e08010b04060311040e070503071b03080f0c120c0702041d0307020f1512041b0515070c0509010801020c010b040b0f010c03090b0d020c01061409040b0402030a0b010b031501 79
    0x3003800f0303020b60700b00000c1c030103c3d01c079030031030542050b01046207410161112001b440b08a022100e21300018404002c2148881e44528504017418214107044a10300490718000c4c040c0400400b818203000c00000811050001002220210703038419070038071194103142ca1b60411395484010700b640300d00d00301580c1141348112010203105180070350300114500299542032081c117444d03240d03500d40e201c4070790b50500140e00d401e2001030240c801881c4008040f8909854060000c5101c00f0740240380c01c0c18003000f40580c1d01e440010800200c2c072044600d45031441071404164020842c1c02154100c07904c1070001403280d205401a00100da8080700034000d210540702031001711040d00000540c4014491090240c650250100302543c900074a009070691351140c04c103501962214030481d14440e4000f804030f200502c20310840707018110900714003855081c0b01c000180c040501800191000000c0e602150442d6410005128907562004140b0059a03480b19a032400f0b41049440d1810f0850300401620360f50b2195 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 79998616 1250 79997366 79997369
    0x506040509010e0604030f090b0d0903090b04050120030c0706080f091209010f0e0405070c030e0d0206040b0a090503010911030118051c030908040b071b0e0c0703020a060c1e0801 78
    0xc0010f024a41c4d860b2001ca80300c4d1055401d550134418230580116a140d10540100442032102c0c0001c41c5840007854000d01042c03184e404648074400c00d0205100683c1c0c4072104080701600441a1441080341c50021400c51069015024480c400c980f8000348070380c0c019100a104031b052280c2d03603003556907d112399615410126a806c200a0041000380101d41c00f8600c1110004014030308121030f1208a0085003c80c0e10903030300d420101e80d603c2c14510030140c0c0042c000c140d008043c0d4184e900a0a150301096050180c1d0003001841000816441010340c46a04000003d08004000340b0a151580c14003030000304407031800d28000d50030903800e800f03240399044803000c0c4182e110340144440d801c151120348817200105011020140c80380b14070380c04280b10001a002411400c511641d07217600900e803181e142011a80311001c8120828030412004410840d00c91b440140c0c1105296a4962032070100d051a2480d080103000d140b40800010b00954040441c030380003c02600203944624001600317540c189000d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 79999866 1250 79998616 79998641
    0x1203042f0f0907020c0a030b061908030f0a050c01060b030a0e03211807080f0c0108070c1b1e06030c05070507051207030b19060f05031506061c050604050901 69
    0x24241e2281001c0305140d03400601803045d6101000344030001609a8601e501c142c4004c0c10040500c5264902081e52032502128451910141440c00c44140e440e4024000c01080c0120301043c21250580a101101d11150880c002000055101c3d000c100b80754000381d03507c10342c0e280340c45001c0c211000000200d4050811380f0807026101e654003c2c00f003901040082c0304500c40c03075400440c0c12074000308102c01400f4180c400081c140345032302e040816140410a8090b6410004100300303000b505074018507020082c83d00103407004514a02034258904e03140450b408003c045101c0851180304030b19140180381507400035038080c403540568000448060044100c003078419008030b00c04000c68074140300880055485074041c2d40741c0c076550340c0b20040b10140486e000e52601c8030741e110010080b8064442c09000e00401790582035042d040c038011075603560a41c865042c8000703010010401c10b40d90007003035070b85207404451640c90003c004030540c00070f8441075a16034052424100401c000b0441802540100a030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 80001116 1250 79999866 79999879
    0x60117070b0306130504211d0102070b0a0f0e10020d08060603060a0504150b130905060105070f080a12020a0c020f0d0f1e06021602130c02070510021203042f 69
    0x1312240c120001e04014004880001c2a54500c15a070000c0c44481c04400619440e0710403000c03542036405400381903c203003050440d08108000d0042c0d050075000d41d000703050b00d0700d0036811140c0b108009903105103080c1e0b00c095000c90607040c0018440c0e400602c020024806030f5607000f468a418050010300c6c04141c1d096039000b81c05031402e10180c28594801010b00222040340100d1030b940d2280c40301142d000940a401002c135905041c000c5800030700603030b074104100b0700c5c04030316080c1543c8400160951351a001018030314002441580c251042e46120b00f00760141c03100710364070220101c01402c0000880c0b4224000d5110084a07241c516241c640505540e0f04803860020240255642c0400220355600e490004d5111100c0c2401050b06440030b012010006000c00d80d4001240c01002a8074500410720204a81011040238800e540454031808491041e070b0303205071541444200380d0030306030980f00345600007070040304020a1204100881503140c2440d00c84220101b81c07444030705454450402003541094 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 80002366 1250 80001116 80001139
    0x30f0906120b060712050408070b041a390c010201150e130b0415050112021809030408151803070323090d060b031b0d02090c0705060117070b0306 64
    0x1a620307000350700003010083c4014500502550755460508110740c503200000c00104003801190740801480001d0411240e64506061401c1c800c00440402403285852025012030001031031039011000c03103260b010440380c043c884890001040304040004010107011f01c5200030340409940181f142c0d180414011500c1c1c600340d0306100300c4914910010340038944208001502c440482c0740c0700b1004e8003039482800d801c960103d0070842c007000d461042c2c03c030b840b007118a802c036000140d881e1005404a04c6280503807845582d80c40d15842d0440c002c80e80000c44900800c142c880c1810148000700f84035202c181640d10101e50403561059580c01480b40c0240803030b03519503115007803e01080001e110514220282c51520010f000440d4400c060600c08071200c0e91901c003400d8240c5000e005101d9030003083e02c4401e1545040400082c11010b88000180c0542c21030700100312000a003d045407080ba42180444003030356503a40698119102d540c1c01900c5030301580d000410001968000c1380c1c0a0a0010105010706 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 80003616 1250 80002366 80002397
    0x10311030f15060304060204090c0801051f14070605040204200d05060f060703080a060b03060f1c050313080709020301032a090f02040f0801020901140d090501060b0304030f0906 78
    0x3004050100b1050700710a0340c411480ba070710b03e002144900d2284601580351840c00a0640503200e03801700300c10034404018010b200d140c4825050082e068080da611070700c0100301000907503000c4078142c0c0111034010009012400d0200503088240298400d480400c5510f2054003410783c000c8130200c2c4101042c100b00200000b0881b50340000d900400010501c500064650f4002401540140c00c110089120341d800c00070640c2d12841030308000c094034a80545140b1741000043c2000c85200149403060313006040b1070200c01c2044590706419a400300480341d444800c50000d401000b01803003841800d102d80a00030a80000d40d0080d6030403a80c0c40711940c06a105036032900609614100a04000f06d07078400070000d001c14590282889441741d11000503921814154042c03800c0c9900d40101c13002c3ea00420407050181d9201c90300340035040508503401d4588a00c042a8000360810700006400783d82003200c046001d07581d0714020744c0103e00c6901d95000c2c01460740c101f9628150b480c420080803600860106422 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 80004866 1250 80003616 80003641
    0x3020d110c0a03030c1505100515040b07061b18030609080c0601180c020106050306040308041a0c0306120d020a1407030512040f0e0c0d020d060b030702010b0f01031103 74
    0x5a03000101590220700d41880464503105142d44241c001070300c107252100610030350b41855208010b0500702070002e4508407031012420110703403241a009251a05c0c00152140d24001070350007601107880780700c0e45e0718001c0c10a0000f84c01440381c0350106a612601c050030083c080d8080a0402014098400820b80703191220700c001c200464040e10918000c00c004041c66a00b80300c281d000c1e081d16140c05070104803044803001210740b440b255005582c5808014012943c0018900ba0300a6047c82d0601075550381e8508070611500000d080001d900307a540c2031043c820445000b44d84103040c19102d07006d0281c0c05039090b80e91500410018070143e000a25a200032400003080001d180c11094101d4412568a50300c061408601240c8850036540102e8240650b018083c0341c40001e1000c58202c801a00b841030050b401c41c82960003100590340d00140c182906a510f8020500401c100b0881c00d899262200c000b030702030a152400e051107900f0140c04c0090700d60007442802c0d0858401003001e41036603114104001d4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 80006116 1250 80004866 80004887
    0x509010b1923041e09060509031303061109030d0e0315010e370e07050312030a0e151e01051009030807021c0804030302101b0302071703180609070303020d 68
    0x401507114110788014160310100302ca8107129004d40025010200d041103c2180c9010309010966003041100038040034240800f0402e0380e400800014466000c207004800c14420854542d8040c020b44d500c540080790401c5007080402010341c00c2d20724102c1c8641c0d18415005090191041144007900403814030031002d40488240e0f00160310119004100026102c0b00c105130501e05606640c40e01d0810181c0c010a01409005000c182d000b40280c1403422842030045c0001010078808540d103c84411300400100301c070b01c02c41c2d8503404158045041154843c0b54510700543c04c0440e03054000000a01c03410030b041c060502c10455920700c0881411941c4003002d540c0010300590307104524000d058281d030514200e00030700a00c00c0010303d43e2a403451401904000d403140403e203e8920b000200d074940100b064540300107004900d001039840c065403a10110140c203424020b00c80c000080100f140d20104121102c40c00c5c602c110849075695150180c043c3c0e961107034080200184c202944c98803446004111580 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 80007366 1250 80006116 80006119
    0xa060c060b040510091407022a0907080108190c1401140c2503050a0b070c050106060306051207030c0521030304032109030c240509010b1923 62
    0x15260700c00000541502d00507600d0304040d0707190082c204244e40719481004207070b0701040036108a5240040000c2d4070340c1c004a0100c85d2803084400200070045015102102000e002405114241002100140b000c002400703505124420341d01032200c45400072081c03426465201300b01d145540c3c10240c0752000306a6000307025050022428003450150300351005010754201980082101940400810303081e28a405080da0b0300504c60b0780c0a10214502141c0204169003161450003245c80d0103004448407040804050855480e00a0114010b07500d078200782c040312030445200b4440742c1c034581d8440c1c0f682c0861000803c594086038080080d410090f400b00c03620f8a40b034010002000f03130b240d500390440d0700460301100080c0c1d80042040c0d03203185a00c4035026215000740b040021751165540a05201080d00028041e44048038030040c1684004112000041208400340b150382050748246000e01401c018440c85032824208400b011411402c0c082d00302d81030001820482d5107028001d100700c10744420f207103 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 80008616 1250 80007366 80007371
    0x7022404120602030610091a07080d0c0206090c04230405011b030501031505070503150307051908010c020319140d02040e040605061f20060403050310050109050a060c06 74
    0x9000e030120704200400c80d000c1c0d1805a83c034500b520800001205101100302400040030050092240140f909080b1142c1c2c0f220b030590720702c4581040783e0039002d21a1061031050619021103485a03011400d00d000e628210216807941e641b0303800300400c5e20f62440f540c000000441c485000307000d540700102c83e0494040c50000909406200312900740003020b05110f0080303a2500d00420401c0b070b1000300300100007141c80c0d0410060a080038000c01c0b920000d070050b1120202c580c0b00c00c4580e070b401d02590307000f008004c00d120383c050003040a04105400d50f00c168000d03035281c5030001610340d0000c000c441a00210b14500580520401029103210311010301c03030b0841c16000d111000111056100600180c1200c10100000c5d252601e410030503500014100d6024949010703014010503088018600c03410060b0030b0105040d0070711540310501c660075061108240c413900e02404107150b0450000c1d8062450030092a9560351200010744500007544512600300708411002c22542c1c2c81440d104010520a0901 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 80009866 1250 80008616 80008619
    0x4120b0726040212060903031008030901080604020706060503160314010b1c060e010507050304060b031209120a020a12031e020703080c010e07060f020d02011401090c111203010e010b07022404 84
    0x1561800c0340c106c420b40c415a0002044c0903950a851544e503004192102c0158607019034400003c144641c060541402113030042106800c04c80c158215001801c0c02030102c41c008960356070302c1c010800e1103100c107a43e01401e19170b403050399034010b00415502020260102c031458100c101d80300701240182c02d0544409030341c0c030850300780c5000a00986008055034ae803801c0d16402c2a085c8401107400e140c540522a80c840035690760301c0c40c0f2060945615500032506609108444806141000b007040e400a500c281000030102c1d0720600c0714482068a0b000390b4502400c020500c00486071940949000d40143e0300c0340c0d004000007852540105000083d450020410800c1140da05e0b180035602c1d004040850074113182a04610b60411807000404121302c000c0c08461036864844443c0c6206001e900c03600c5440300b4100079180d0040123842e14504100041312140c5202c0c1c40c7d000419007080c0280c00444c0c451000000300b8442120546854580083c5100141912500a0400b400c990160340c0e00c4031406100 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 80011116 1250 80009866 80009899
    0x60506030403050306270708070c0b0f0604060f0e04060506060c030304020907050403051519020a0804020d030207050901090203090613020310090215130911030106050a140d0204120b07260402 84
    0x1c40310902006402c080800d091103031f4094540d000003011482003140ca031124402140701400725542004a0401501c100d8482c0d07404100a001e10303400c240300c20b600c600000a410200b50b0f400601c130303c2c041c0c1e4003004180c03680780030080144911200c81b009a801070012030094071704175010075045652424507914141ea17036999681000f000b0002401c12030740c178504000800d481c22a900c070721241c0d4003030b04600d002d41145001c9c01800340680003178042c17203000c80b410013094001c11032440076140090110a1540c1d6a481030713030107503008036520711040c0107010100300f4149200100b544282c1d40200580441813510380703800c0052070000c0c3c0503a880702103207408066001502c401064151401c5804d4005241482d464209555608021910f1840c041004002072030f84141951075940d2640342c54180322420115241e03d60060420041e009031000500181c00d941e10341c01100b41d07600c9500c035000180d5900302c003600e01030760310078504900c00e444240000500100c281c055078020304c000c01d000310300c80c1040c4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 80012366 1250 80011116 80011159
    0x90503040612021e0c011b0f211b030c08040b06010809011d0c04050609060d020613180c0e0301092319050106060212090a0b0f090d1b09060506030403050306 69
    0x18035960b100c0c1c4c00010411040c41007801070b09a03003540804240700442904c00c004209014030004a000c00c00036040c0e4400d0601d01418000006001080034002008144207468000c42d111440402280c90f040684410900a607030840c4902d07003209041000f50341d0200152891fa500424811003950381d420ba28260034000da50780f444000418000704500301d5804180301c1102c501520311441019810104415a9900107400c0d0b007a0b5030607184503460b010880c0d8024840490354004d05141c12954907141076910b2607034000c07045181c10b9964501d27804100c406160899801150242c0380008243c9480d10009405a03c030302c80b0070740c8604039118003008441540e55010342d2001243c540c0d446000405c15960304201514a0000407100a8074201046001076507404951107044201e0340c02189241c94a140e142c15079900e040b0282000401922a00d02152407801002002c440a42043c80110780c0c1d60140c400c0301d0035114080c000500c0e6407541d807403d81d00e035040145450340c001c82000c61080c5409c442c6d03 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 80013616 1250 80012366 80012407
    0x6020c09070512010e06120a170702010c050109080307030c031a040c020c0616050f03030708040605060d050a0c06110307081804090804080c04050105121005040804260d0309050304061202 82
    0x141d038880301418103c00300000e00d4422403201f4615403144254501103403207580a41c40403284021103c0c2c2d2000144010b031405d096030302703024116501e4510144180442e081c01544202185c0c0d400b0090b0019409007135007250034074011142c0380c560900d01c0c00c06905180e80511201042801180c9203402183c2c002503503035004040118090004807051001c020b0108190031038401c400010394158504804010301c001e40082c0043c16960316400802e6590b02c0f83c0780103900c0c10343c2100645d01c01080c182403000b841555441204001250301130610920f20340070003641c0c405640034009074a00070182c0120310501045803060340e8010380e20000140028802d0b4020401031000c0340140514030408002c000403100168803140c0204001803820002c80780110740703941e04844d00f0200042c2500ca60070403103014021600044a040e038425a0811010b051031007180200d85810211500358841030022410380d0100e00006140768070502042c401d2a0080c0c180710701180c00d1543c01410020781140681040000c07 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 80014866 1250 80013616 80013629
    0x240a0b0f0c0c0d052107060903021e01060f030303020c0106090207030c0507050f150a02070b031e010b12010b0a110d05090f012a02060702100818060106020c0907051201 74
    0x4902511a00500c02d4046082080710805081100c0751905510f0f507528542c54a880042a140002c64803110030945a01d0b80e00400c0800c1030382c0f030707900d00650395007518000e2501903e44030b10180001c0b6014003420044d1203552000c96552442e543d0b05401940010101c0780c90342d5211240403401d88528405007030214040e6036404801c60050030032a04002c415000540140c0e140010305d0641d490740c0c1c82910840c0400800e09541c0c0508000c2203003091100e03044842042000014080c1400511804401303044004020324426640c1e180c280d012485001c404030800500c440040059412030005800090030a042202d43c0c02d0b525808035041c41004154040403c80210307040d501e50800101c2c08584000a0800e001c0b1004441460340004110b03074408141241c135008014215120b0740305031107156602510600514a0105c0040c0c14607004507402c0b610308420f0446a0340700d40700058018100c50880d0082e004030070200043c091401d40082c5040c3c207002080282d441c5180d01d04c094140240403 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 80016116 1250 80014866 80014897
    0x30918010303121103010b0703020109050106090e1e120309070b041d150d0210210e010e060705030a0b010c0206120114180a020714060403090e0601030203240a0b 71
    0x15841d02500500b019459141524980035840704860030340c0080341d05580c90843d80b00d88036078231481c08a02401010500602071350a041000504480d103070051aa00510f1800b51004074030b82c08000648a100c6800d044150760165900302c1e2094803800045410101c100151030109440343c00a00d52680554040418640300e411030314010403007440a41c0c6c210840c0700800c103401c807a140006035440b200850280c4030350901202d00000d0b134050720b202145241c1403100e0307c1c0d01c0c0310a51201c00062220280c28041135081181000c5845400b1404510503440381e00c4403401c2d80c58000d0660b005008600035941404200050003002da5203d8001d841001d51300f00607800258141070448030f00101c1600d80390b0007100c2d40120711820000c00744840c0c0d8402411f0741c1c01a12070245052103034801980158002d40760150005000074964810390070700c1640d0b4003c03004419a01c841d401101240310848800c0d00c3c858100940e001c4084a040ca00c0d002404000c04a8440d941ca620000c0c42c0303580034084e80c0b00d9010 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 80017366 1250 80016116 80016119
    0x20d0b070e040b0d020105030f070203190c0c050d02010503041407030b09011b02060108031e090a0608010e010e0c040302010c03020c030d02010b090a090803070c05070306060b1b010e100b0303091801 87
    0x303803500400c4041c1c801031300c64008606007980003070034034000a007181f802403041c5070005114078400c1060f500d20640c5860000422900500c02810407184804266032409030351601003802e0910810084132268181e5070309107541c0d9181c6464844803540f8106040f64010f90740c0000c0400c016010440c025110000002001e2a06400303280d12128007a0007501550000d200401185c94040140e81d00482400c100c07078480061607196402c1707441284085940660344100120300c580c0c3c022541c0c0c0c1a26044010388403280d0325102c00441c1c4004c00c81e40b003440080100001e000552090f5100d8038014030a0040f1080c542d92500082e0401c80880310070760041c0c2d550a40342065290800f840f41d041600003000b0440914141c0b1148040d110041101c03061111030505541007040800c0450000c0d41c10140070400680c43d81c96000d00303984a5a2948600d4200b440303152b203010410701c50102140c01c800010507400e03448651600103400040301581e4903000900403100755840f02c811203045007034140c00300151507 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 80018616 1250 80017366 80017369
    0x30705041a0405040906060e0a200c07050a060c0302060a020412031b0b091605040b10110708060901050105090109140712060b030c041e03050d1206080312060103110705070909020d0b070e 82
    0x23a100401ca0314820741040b09003034801100e0907011100545500480da03540414480b201e1608409038412900940004c0d40062000d030b0206210355441e00c00c1c0d0a6800b01d448400c00d1005900903405910b4074050303540035210000b4050050200741601c0c0c4460070001e1030039520b504030090350403500c3d0b91141d000103142d0203070307282c4400491028001c100d808100406107000810051681840c500080c40390812105401d020104004401002c64034221070081c68642080d601802c428459a401520410004540f05d5028041c032060035403c5510b4541ca6a41c0e50804c40e11680c1c054848501142d40300c00220701c500302c800042d403003542e0a00690b03a40304e10b000a070002d2196001511021801d03400310520002d0390105043c0401449072030500c04002003105400c0040c0b03007550240d2001d01c030014490305007881a180f40e92086000344c0703040020b00800200c0c29141e20a0810043c0140c01209013400414595401051118005001ca141140e803694a80b0141482034400b4804606200c112410310b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 80019866 1250 80018616 80018639
    0xa2118060e03040f170304080615090c030f0f0a02041802070c06140711130203012301020304081905010f0e0a0b0a180204090f0512040911030705041a040504090606 72
    0x84030100381c0114a071900e40030300c4c5130084010340140700b015900c03003644040024003041601c01800000040e900d07142400350991810302007030100780d0f00034626000001c0c074184c1102c0079a44507800040e030320740e10740d0fa45601c07078034103042d000348100d141650900001c0341c400110301d010510314003031880c0142d07189540e003001d241c9000698410003c00686050200c80320b0000700940d1742e12036101024101400d0f070680041d403003051705031006801034408000002c00c0c54403400103826102c002a484d00d42d070350a81c001281c07284514094120903070b000070010004030001007541602240920000242028003480320016207607800c074150b4295011380c040801b03001003141c41540120042000f000058048814015040245100a84501d41d2006e03034000344044c0f82c00110741107500000380c0381410b04038031441000e0b41003800f94420151038808003100e6545400c04607802840c85848944c20241f40c0403901c001c1700e01ca044d62410200e028040050140c440c1c0c0a0202c807540701c5e02c0082040f50902000216 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 80021116 1250 80019866 80019881
    0x6010902090102031204060b0415050f0405090616020a0c0b040612020403030f32031b04050307050607140111041d040f02040b0312030a09020108100b0a211806 70
    0x404038410880710320325a0b0000304941c49485101124400b076a03c600f0300c00010860500ca00741c000d4205160121100800d4003d14143c620894514542d18030400a00003103840880d42d0025651020000c00e61b89040e400300005410114411259600d9442d9a5407540718400c1d0300035803061002240c02d22081d030b00418000040194100700314102891a207005149281d00c80c24501442400d18007000700315203071040c1d00132120a10300180b9090300020354440c9254001c0315001d580a140340c224040b12131404044400320741c0024002e00c0414241001c0000560105a08403000c50600c0c00e90020703201d0a0040d401c2d19814000100c1d115131804240581e0b60b83c1c0d06e00090150035480e400c00000030030000a4030303240c5070156000a517050301c17000860728084008500b05440c40f8084200481e0600d140c01c0000421f1003039030741d2241a200c81d08502c51094041c0503c50100700b040c40301d024180d20030f00c18083e1407440654400c149030300000f021011500c2c0240341c3c5420b01072007050401402520b015841 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 80022366 1250 80021116 80021129
    0x2070314070b0a02090105070618110a0302091815010e010e06010f05180109090e3a080705090409210908030405010c0203010219051e030106080c03040222020703020601 74
    0x1464101165242c004403540100501060350340810201c0c07107640b080301a00e03041d560001c1c04004080000c0c10183c040074540b4007c0f0740c0e020f4607406120081c20074511840c1140c0c1d01400350111922107041050350030314a80f28402071841203c3c1805813043c82c202c8914020455510540300c40d50405403084a00b0100030001414862800d1070011815440411102000c09188440a80c0050307040121501030081d0300c032035002382c00c000c0d0003844904041000d0b030310a02103807614030041141c282003404240402031800c00c20030f2641c022180300350042c0012517019410780380c40c030710b01510b1030300060480b119080241e850b0348001094140800c082c0d08406503000d00360404c0203125162040041c2d403442a409205d04012080501c0c41c11510250182c620342e0104041484440010801c0200b240e0800415403800032000c95200341072034035520440e4141c42c210f90316061030b60340f1045010655840070340226080450400140c0032030584508244003101802000761b42c0d0701c41410001e1801d074041c1c2008 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 80023616 1250 80022366 80022407
    0x7020619020c0418120e1002030d060f0e0408070f020603010306090302010b010201050609010b0c07090212071d0303040504020304050f070806060a05030f3a030b010921060203060409060f020703 85
    0x100c03a8620200c0c0c4c882d41c0c01ea100041480c10494a6011200455000f90180c0c000300f1444503d000a40c000c0060300f80e11240740000c00015544510010400180d4413680940403159804240410820b4000b4100c060180503100300681d500c7d40800d4107a4000d900c20b58000e175880800104240d070a00901140c07030300c244028002802c040f800509026018810b150700000009541692300109122035030050403a100704548900104070b00c40c0c0645c104981480000c2c0207031040e03c0c2c2c281c0f12440030406110003d070040d42050700701002d00c8001d502c06801074840b4416000200d05842d01005640041e0030b1078400f400c480d0901d4014011103806d070340c001e40d10035006007030b1104010070001402581e203111051044d07545034231030580d0891100b50002d040040d02c014010f00d40e10343c0e0590881040440c0c2a83c501d18080e5460546080340d8810009100003050703054410f4000c51419005982c1280f1300400010f00c1c49000d41e545812500103d070070304a06900800d200d000e1682048111000311070700301b00c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 80024866 1250 80023616 80023631
    0x20a030612020f0111011103130b090706080604110906130302010306050f1807030e070f0608101214070929030304150f0c17180609030d031107020619020c04 69
    0xd0302c40102d0380c3d8043d04014060780700c002c103450f0075000700f517030101d00d20481ea0b42c0342400f130051141e0004c56003041d2421304401340403400d4003000213100c100306c0341195207222483e100c003010803002d481148020700b0b84050501070780c20150b40c5c074002007541460505d034022205143d0b100141c255003d139801075104103603070a003402c1c25440c3c031020440c04d041544000e114030360f6030f0f01c0183d00034402c102d107206585c42124004a1000004443c0100b0b407011529074400343d03a0340c588007044258150080036071032185101d90000007244520743d0600251103000b80c9000c9519911004116a9030b0241540000c454140616401c0c4c07007070394402040c0c0d41c00e4001d1860a0b04150401c040d83d2241000042008000e10803e002c07680f09203c02076410b644080003071001890b03810450900e400c82c00c0c00345108409846400340500d4000d040341d4810070b016001d072541ca450303450150700404c8070400344604804200401e1006a48141c004c0040300b6103107075942001030581c24001c2c94072010b210340600442c9820300 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 80026116 1250 80024866 80024869
    0x7020c01080109020f0d020d022b110a0c0308180d0207031511030403110309040204090b1002010608070603020a051216081509060d030c0f050c030c0901031502130803070303020a03061202 82
    0x846c0d00c0003050380c50159944428055a400038407541c0c40c0c5070702c21441362001c050640b01d00c20a0300f0448003020403e200440e11420b044c800740c82250207030408103152030a020b00180c00351000c4c5501501ca1030a440341d2040c9580c5140c05c21240b03250b0400143c0000e1018010020080500c2c1001d01c00c032030080058200040a44004c0d202c007502c060184182c0001020010301c007003040b540300e21806003041d501c641c0d44801380d001a0803940e01c040d200311040b0404c04640d40c03052041c03804a44445008040b01490070000360f0080d0301c001c58210802404101d8170032010003034070300385000d02e2049084d030780072249500303004280300c802030a40c00307507243c1e500c4010145a4a81c10ac40c2d811003412a0074103a05862850300361079000002d60000c080e50441c01e2008107002004c1001d154055081e03050701c060422540c200110020240401081c040544100d100c1158035680541642c003002c265100f007003903e818406240d6001540c040340000c2c0c000420b624403a0b454000c43d0014008045c01030755482840d070 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 80027366 1250 80026116 80026147
    0x1d0408040504150801090f0c0504020922060e1302041d0a110d2405010504180f02010903021f09060804050c0f040f06090504050606030c090103030f0c020907020c0108010902 76
    0x40303068403442d26840310f141a260019000002800c902c0020003198100d481c02480041c00745106490141011030001800d0030903000319400900010f00b14680740f480403c110000c03a00017210802203507585c42010400103c02091355005900494690310680010301c100425150148003007040c110522a030288204000200640e04030390040080420440344808900340d02000c4001a20a10440d611117200315502013508901d80c000320f100f4022a13072034a00b8841607440d4803407200c50b11080c02d4580c00101c0c1d000d0101c001ca0503c1450300041d819500d4002074002925600032130300c000050f50507000c226801441000081c186410304101d00e2805403103c1ea16250816110b40c042c04628007020083da5440d480407200c65400340c0e00b040020349075180640203001c100c408407054807810021480c549000a01c601d507103000140040c0e41c0e42e0860350116440703040d100c41d50301481504a0502c0040c1e40c1c0000c0c940c818406c980c010014898020001440c090060780b1030090203204124242c1c1c0c541707455 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 80028616 1250 80027366 80027369
    0x1407030209011704032c01020106061d0105090d060203071709070e0604090318090b040e1b060d060e130605100b1806040302030a05150711060a0c020a05070f1d040804 73
    0xc091000681c3c130b81c2000e49a00b0820b10507000c404541c40030490049402140420440c802a8002c00003161640c0f010303101d03001034045a00c501480b00102c40700d9907104d13900521045a010b080c0381151040e980e14841641c0007034501c1d00118806050b51055185e03120b2003640d200d020b04005110b8940361140d0040c4800c400707400700d40941d49640168052600450410002c4003801c40140003d5a81716400d00081c1301c0c282148e8032841c14034405401502c40014074000350740080682d03a003918100410450303268066806950381d662103507400119122131844072485a240f10440420408131440e1400440700018002c800417031061005000003010b250550b60f460041d84040501324404000051050140b40c1c0000c1d45403062950701d608004c000310b001c1c65080310085680c4500d45030002c0a031000840500c04116551050b4005510501103070000d40e5142c4107030042e140315060680388d4034244001900010f181c01d000480030802c80f4415450306152441010101c006420682c2ea00501032059 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 80029866 1250 80028616 80028647
    0x14060108090a0c26070f050a08030315060901020a08070f020a150e01050a0c02090108010e0d02210d0b130b01022104090e030f070303060503191104050408130603140703020901 77
    0x84c1c00b40340c081c8110a100e84c044000d10a0101c0ba01650390701c1e0440c40750b5145003c0c140c01859005000242c1500000950307000b401d86555030380c4180285401e010fa590000550030341103101c3d000c009404074040c0c20080403514003e00141e1568940c0b0b0061103004005640300ad07407541c580c0c0642c10241c0d03030b100c181c01803030348000d01e0003950303990500904948050f980b81c4069489410880006405541540910940440354003940e011500b99030b0300780e0b10384000340c030500701c0c0b0202014100802110040107041d0040c1044e8009041d036010b00129400800d402c4102481503521070240c0c07140c0d81c040140700c490000300c44010134100020750031203046002d54071540e05000e4030740c1600441254144251103d84400703641868603113500c1d00380140039240c64443c503402801100c501d81c1c49510000e2503200d00d29000310101021070354600501000303210080c4242c802100c14080380524480850074000186115640803480740d11010340700c041210043d0100d01814070401c0318000598008010306002010b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 80031116 1250 80029866 80029889
    0x1d01080406151715010f0b03070c080d0203040f05210d09080c2406010801050108041103010b03190507050409050601030803090a0b040b040b0f0405071406090414060108090a0c 77
    0x19214541050401030742003115070b000c0d0f003020f040303a4480004800c030070b0060505030450301d40d81e2443c010311180c00302e003c0e4150b120340030000990482e006001403d2028840e9014929090400210400f26002030f6422544101c80c01d21400900400b0072070188a406a035013030f481d50041c55407032200c0a200e802c00140b2840d071103454400c180403d10782620b02d802c91076015500c12419440c0c0c1c01d0b02e42c2c8400003404500031040b001055195200702c81c1181078403410b85480b070b810f03111794480001105c2e418500036419900e5031448441910103005000c2290000140c40442c52082d03d840ca05141e050307000386028a10b00548030000c1440041c61a045a0700482c010340d99850f842549800c0034180400034144080401c180f0040104010750340307110b0f601038281200c0c0b5032503004407021221401d903000b030b203164419101401003204003072040c0c4004500030801031425444c40c0201c8c06941d03208101203406903112041140b02d5070804440c0e036200e0720350b402822a461060307442904504044c041c802d82ca84 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 80032366 1250 80031116 80031131
    0x70e010b04151106010623030106030608150603060402060d0b0a090615020604080403111908370b0c040509040c0504180302070b0f04080a230a02010206040809030111040b0a1d01080406 81
    0x30800110121076482c020165540c1d038568901402030724cc14400c20f48984a00300208d0024680b400829005c0d540c001c2c060506525140c007005403d4115012905c40700e41d8421200718586d0300c400070040101200302001c5045480c08414207400041d00c03414400f95040482004006640041200c1c183c81c0c0c88031f0500d010841c03007400b1a002d071a00030f0304051211001c040204031040c0008505071440c40040d413550310003c0040c0c4204000c426a0030319140c450101942d2000a00d0040210f54080d00024103142050f82d10b00c0020342c00242518141c1e00b06040400c1406070f4100f600070f98985c1c0e100800481c103641c0d42e5074ac0080d5900d00030302c00c10700320760004140ca2400000840440e030040c1103003001c550301e8210030b08044d0071102d281881d91908045503481c42d80c00d2940469803100b2107405030054030040e519601c502009901541c011981550384858562492032003a0143c0040d2500851890700c961b02a000603100d014105400d880c0c01213038441811190b03074001c14540d80300741d0060b0080303060f4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 80033616 1250 80032366 80032397
    0x40b0702331b040f09060501171306020d0c050909131208060105160302150105040e0a0305221d0601020a0b06040f09021002030919030308010314070e010b041511060106 74
    0x880b003071a0410040100050009000c854104406060302e010490400040f6520707030040d20390040f4481185400c80c107400004840301a1200e0170118103000758005403400c080264888105c5809243c0c480c08102e01044509031804c2c9030604550107003e1002d810a811429220300c003840c04001c42420410540000003200e0f0303403040c1c09807403007031001e0502c07071011008070b180c0a5103c4c0d01120bc814807403c256400010149845c0c041c0071103800c0c0880103001c2402c0705841c115065440028041415580c441c1080c95801180d081d8000030858080f4400089803180360343d072941d90303001e03104ca1f0442d4401c4101e038010920f98200d081d002401100c3c0080c8400c0c0c0005080007070072000350042d41c00754184201034203141d008001041c103c4011121420a061072041c1e40010101a000c0500010725007001800002d110018046504180f05c0807503e4150303680c207180548200c241c020015000340494100880e0311076004918082d4014108040f03c5039111041c0e80d51080144215801c02510341e1400c5440c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 80034866 1250 80033616 80033641
    0xf071728090b071a06010c0c0b0a14040e0f0702010903020d0e030f100606090906030c0b03100306020301030320010209031f1104090b011719020304061103040b070233 73
    0x505846180036264943c50030302e09510384d26940741034140e4042e4030000c0c00c02c0d0700c510006a411a403004040d08aa0300f0a0b0b8100d410b6000100d911090010f0700d100303500740b0080c2c60007810003094084020400d5291000341d80302c0184015007114107680c10026000002500801c42d5a01604c0c507240070191540c44000103403070700f140060040c0b000d02550907442c800307500e540c01c4013080e12001d40b9141c401c2c69480102d102243e074a8400500042920781050101c140e0400095030000c20b00500c08a2854032622150304aa10a0703100302e01080105844214140030038407a00c2d0032048050085003414050340100c1e1b1600d85601642d42e410042400f0b401c00b001c100d1307001c92444450100d04a445545400200c0014440310520501251924001c1d4051580c400c40c807501c104c904204510020700d1800103030303000e5000a0f2003198240d031507620524100301e005000d9880385000e203405081e01d0600e010042d00340103052a03901c151040103c49005417507841d60070414143d44400c5803803c60307030314805d44016 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 80035972 1106 80034866 80034869
    0x115020a0b070c0203101b0c0f0204110d020c010e160609060c0218040303140906100308090d0209040b1006021b04020a03060503030f07172809 63
    0x10728085905420111034102400940364a0340020f0610807902c0e505080c00303580d40c500100501c80120110700401d0a4104000d00d050b264686e04458100e07141c000e401680c41d0000c005d80614214101c98065000c200215103e0110550023806000d8210a82c3c41c184240b9842c1c980740012000c168040b502170b40c81e00700d00c00e031401d90141e41c030300e0b01410281da02c0700d82c000170071a1201021940c503201e107102c4d9500080000e002010500441c6001d4540c0945500480401007000490201c00040c1e03a00304403829181d40701d00d800035490b5034603030400a4120411605020401c9005003800703004000700030144c0304c5507031181c5049944090301742e10b414112540280d40921801c5c9a8000c00c151812440c02041e0152517501081c5150311040401c5482c1400107008020710408403410503441002c100c1452816810000d184840114007040180b841d0010341c1051455020f10500760 = true := by decide +kernel

theorem cover : BRFrame.Cov 79856116 80035972 := by
  have h0 := BRFrame.cov_init 79856116
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 79856116 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 79856116 ≤ n) (h2 : n < 80035972) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
