-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0968
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T00:33:34.072353+00:00
-- url     : https://prove2.me/submissions/f6f04ca9-3a4b-4bf1-8bb0-1dddd6729371

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 173920863 ≤ n < 174100719 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 173922113 1250 173920863 173920891
    0x80a09020a150c020405250315060311040e090304050a0801021606050c0d0509010606020c1008010312030e0d020703020f150f030901020f1903060905042f040e03120f01030308 77
    0xb900101c0e0000052000a580241880180000f08001301200086c010070511440314104004105409a804184492500045245081022034030a43c4281601815601c03000d24040e6101a40b04079641c1c00d80340d04041da08001402c12041c9040c0004000038902e0f10029801d140c000d40a011410030100ca000d0a2282c41c2c50020b150784c18807000711041c41c15558010403580c10042a070310300074821402010058800e183c1200030624001e103614416031410390f5424056800c40e40d0b50028640148500c02c185074035000b10b0382c509841800401c01600c42540103201103071840c010012114010f00b295405030000c0c403280b90fa10300b074040c105c400701054181d1341503407030319441c60440c0244030341080140f44800201d030100d0944030b6040401c080c0300c29030f9418040c250300c0d044160225501518005d0440d03086040d410941700383e5407900d0440112a018090100f40940040b400b80c3d4032034a0907880719040000d52201c03a80c600d1a999800c81041d00c2080025070656402030040c0d080901015114180c0c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 173923363 1250 173922113 173922149
    0x70507060c021c090f0504060503060a0905030720240f03041a010303050304060e06010b090409060e06090a06140702030301061404120804051f080601050702030f060f0403080a09020a 80
    0x3c000e59100301042445a280491400000030b00c80d4034507000c1d04110f40c0841800040510b428020321003a5400180505081c2d00c0d409001d20084c60140f0701110039000a11085d07012940c03e44407548588184088060008003a604000c0181c0124910450703006d0215a4030042e480100c096410a40514031a0340da00d480f20300f050010368880e004111400c00f110f1001104145c1d12102860003940704510610030403510000303003a2101024000c803010000180840d0100d0314094210b08401401000002034103c464940c1c07030b040042c00c858810099000c11a0b00c401c0291510462480e50040303c1b884034030f400d00c2c14009480c0c0c401803181d0b500b000300840c80122000c0c9400111402854640b802c0078804041307103402a90ba03041340c41841d204075a03000c0451100142e054551416070960b030b42c0d4000c0c59403403100550b00340c0c1104200341d0305880b40d4800d05041203400c0000c04d01800c0038065080980ca41032800900041009201c0c040f041c1c1090300100040c0c84091605080c2e68600d002c003418411 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 173924613 1250 173923363 173923367
    0x10e07030504050d0c0c0f0618080718020307031e0b2803020d150c0206040309150e0418150b030c01090e04150f0c09030201020d030b090406020a03020f0304050705030d08070507060c 80
    0x8025088024441c981000000c8c415410411044440080181311500556110003603900d0f61020b1281300724080c02540060b694403060790003946d0007225410700060104030390701032607c05036a03941030882c1180c0e50b121403031545c500040340d02c074140380c0d20316603462034603111390000e0701e01c126440020300800d50801c941e0304000760178810b03500740388001000308144419070100075503640095034203902082c0c1c0803034007040e109d0311030040c0714640070305d500c1e8442424506424040240301e07400780121100c0c00480f03044001110040400300caa03021240102d81c0080920400d402c006071002c0d4541800b540f00c6042100403030103580aa1f01c42e8010783c080143c0003140005002422411041040386031900701ca01801c140c0003c045d43c1070700c0c001e86c00c6030240c003414201a41150400710316258040c0741030700083c00040c82a0010542c500003442c1c00b605000c0400c0401c400e6400c29034007200d542e004401e061015080810111481400502c0d00d14038030309000d1000782c0f5911554001400342e0b511440e100119074 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 173925863 1250 173924613 173924633
    0x52d03010b030a06140705030108060712020f0f041a070309030b0702010906320c07020409080903060c0d0e07050d0f0318060c0b01150f050307021014010e07030504050d0c 75
    0x6407019050300c030b0061103450030354010140502c01e21445445600452000c07803041059038142c862880c018192a1200c10056400794104401007a100d9001c0040310303030b00000038010b002880025054161680e051950908100b103c0c00101c085000040c0319041c0441d138000242001c03179810a80710035264030b55090490151064080c094805801c280000c1e401844200511007a11261076000c0510091011f192141003003c3c3c1d1090343d40081401a28003500c1c4c1035004456003803040d19214640300500f808a418104121050070001d40080b0f000b00e42d00201d030156000c078020300c0c006464581d041000140190004410280508400c0d1124a04050041070860000c0108001401449075a21070082c48001044001c031401c3c80700e4000001c500c00c9500c189001d0407003545030110704581c0110101c4660f00010101d000714841c1c03003080ea048207845c1c404d1103d651803a00004c405581072000071481c1140240c9514105413130001048007080c004640d120040b61103107802d10300104a810f010f2500 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 173927113 1250 173925863 173925881
    0x50d020c0d0503090c03010501030c1a0705070e04020a0e04020607030c02040b04061e291e03070203131e0911070213020919080d0302030a0216050c0a052d0301 70
    0xa00c280601044042d8009001d54428079800048030030303a01c040c1041c03600342c030b20a10000305070003502c0406004002d0941c5101046803860141d4038188815a2507052038881c10b6031101590611010600c400d40c18010201c002900b0740c200110041d04207540401d045d48a16000a0104020800140c04541e12600403980f8040024030501c0301039152640801c140541d19000c2c10a54010340c400548403100d1820204020030030b181c481801d000a03c0402074a5000101c1e0401c005244c1c01984680710100c0007841c040d0440b1380c000d58880d00017180070460316480ba0443c8107441c910307900064001044007201e40c203640c5951004601011488101421400760b088001e41c80343d04c2c4a86001c07030aa03d580505101e0748121b800c041c03480c404030b03586504102c1c14020100039820070354203000468041e4006641000c42c20030018504100c551880d502820f00c03140031515030300500309144862070242c203180040c020881d00388010030044128079895000031114455150204445d00c1d90f2960294420a21 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 173928363 1250 173927113 173927137
    0x1002120a050f03040b07080a1503060b1c0507030c0b090916051e070c05060f0a110a080f0d0501170a1e1b0e0901050c0414130213080609150601050d02 66
    0x101e00b0b06180080c8171103011284100000c84e150001107505500c1e0181021207055112005840d90030350703d811001c0c0455550b215088a45948000d9018440e01800d070700c006c4c0560301504441d81180781c21a1440c1c407a0f40200300c2c0700703c148010b034069600d50785910b4100401d00d400c00030450448005446078060030ba041da5440510150549035110300c40000c000040c810007210f40380726103400400c020b9000d040150100900d084c44403402d918000d01c09540c52100100c110744c801075040c0d54101036a4884509601840400f18a0300d1811038a4002e9a024000c442d002d46225445c4410a0744d0300ea10103200540000104003030a2450307070002d15072074030b06904890750804981c582d5044103100c600d64400c070b18100c490100083c0d0380700018880d0601402900c040d040c949031402600c0034200b400466102e600082c080500100711019200804081c400345400000701c915007100e450a101008010040e1600701407107540d062864100010750284e4242440d82c2c98031180f00440c40240914040405 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 173929613 1250 173928363 173928367
    0xf0b03101707180504051f0b0604090b09090609031c0209090a020a12050c093006090c090105061207120e150105060c0d0e010e090f01141002120a050f 66
    0x10710381002c9420340c01d50b5206070b4010900e0324032403510402c035107044402034181d41242c4003010418058080e0b0401e100401e401c0031952580c3c00c80060820f5000e544080000ca42d1110b000381542044c18489034000b48003400b0f4140c40c80c01c3c2281329120700c02c1042c081040402010702405c1c000b000c2d41910300c0e51102400d951118a0308a40c1c001c001d501c074000450104011441c01415040d95025040c07003407800c03080b1181071003440c6051150040c440111050407204d010008002c4207040500720804e482c001d8001e00441c100b55644d14280030640c2c03c44c6004000c030200501403501ca040c02c48050500d0080680a2075444040031109030391901100e8900740d0a28110000c0104000303200082060308040865159030307070300f0403c50540305e451107030b02c13403900034000f010501d0f8090907001030004010304000b8502c214410001e0090082250b10240002020005200d130b0070785d40d221010581000d40720b02d400c100c1540380c00780d0b56580400303009284204c002030011070944640c09031800c0c8100c10b88025 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 173930863 1250 173929613 173929649
    0x1807121209081906020a050409090c030224030c090406050303030405011e060302010e010e03030904020d0608010606020c0a230406170105070201020a0509041808040305070303180f0b0310 82
    0x20355201008004000150190380041480b040c00f2a04280e2001c601030b20412041d010341c0c070700f07010350010000101840002c3c40b001511828034020820154881d580c41000e03d4114410000c803481409040540071807071500c2842064010405c60380c01114410340c003500d032515680003c0282c000c4d60030040d014000070003404100541500b198541002400c241070b10f160100c80e0020460f001440041c0c001175010054804e69401038500304074811000d01070303034644040c08010600b6030b4080201c0904066961004200074034081c407640c000341000348040d1006a1143c0005500040a80901461020300c0d5100f1607804c06000041580803202420070b100042d65a003140610207003002008000e035080000040041e03106100b181c82c0303408103485084c00c0c50500340034800103000c03d41e14100d00c04a403104d088040b5413110b010780300452107000100199811072800400c0080d80c11011104880c11100610948540d910104207039141d102595880b61f88140c2e0081d00d03201d41e40c1c40000d0b14083c0304020 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 173932113 1250 173930863 173930873
    0x30309170c150f040f0609030e0a1203020c0307050d0b0a0e1c0e0a0503100209060c0f060709291c09031d0306090d0e0a03060501090c110312180712 65
    0x99400314500010504443e5243c0192640c0b00c00100d030004d2240c20203440d404009401d81d031000940790700a14001803031300c070b10502041080c10550042040f500d10001d0303950030550b041081c150081e405070050400c0c01c4c40e2102151280102c080d0003001044031400207820f80019600161300d1005080c21204107016a4036082c41d440384d94101680040d0031485000c062b07040803850001283c0c0050020054054442c504031f0084d00035012090b44160100501040e0810400c5101c05810902d400b4256609042c20054001c2401c0d500040741074403201e003200c110503942d501e0703000980d400140c0b465541110414001e56031510b01c1850710740c24070b8020200c050640c05014510100e0b40300d03248005586c03204082640e039032400c46a105040e4007221090152601c14154100c1e440005090300d1f40058a9503905829188242c1000441d65998a4840080b503441170b1015030180b07802e0040d500d045640700c841c49007090018224000240c042203954201d550400450008003e10f00e402082d5a605241c6 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 173933363 1250 173932113 173932123
    0x3060b061c0b040c0503090c27040c0906051509040c2001151202090a230106020607140c19020f0d140d03051015050f0c0a03020d03020405030a030309170c 68
    0x102e2406240382000c1204418040e00c1100d0080c240d41c00100780d013220751002c00a40d0540402c0c25408a000e0302c1009511215030300a06000b00c0c422690038007800d0800d00c04204031403050f80710038800c110001c0100502607201d42220f062010945000c100b401400006031080e820380d441c0d407840d144040e800f000c1d90540661180e1840c4020500c2a2801c0e59251a03003910b44a20340c0c5c01a40c46081e10011172036800fa00d52091324030204d02001e0f19000d407540f4520401c039500c04d9000c00301580003101004119a840301d0b001c1c1c0820161840b06050104c0ca4021715900c1204020201d040d03114046240705560f1030040c28a0b401200400301d0750441128a8612098800c0602908592182c0c0c1c1d05290070500900a880c803507840d60368201c450720310b007002c0e507421481913480c1c0b0300510004104010a4000c0c40009180050b0980020403480ea242e140003840d014410f030b45082050301c1031000303100a95022070b07108092034052a02280301c0c6001e084c046a8800070013141c00b04044000351001000b00c000c10 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 173934613 1250 173933363 173933381
    0x3a020d0506040213122303030702070b0f040306020c010f11040609090b030327040c0e090a0606120b01140408070f0b0a0806010c14010c0e1302040b0403060b061c 71
    0x414030054a49505100076400f480d10320b040031a4400e24148501181404240419802402c0c8170b4071a41c80755101c4120000d07070800782403c0d5040041040701c1c403034040110a004010800045140004100c10380015001d01d0100030003032500007900c2e500035002500051039020341c0b13440030040840140c0441a160b4000d11410002c0b440a00e400913440c0716503c1400442030004d00a146420a069441035521300d41c40c84a400d05900c0d5040751059490310b125031a00d044964442d080381c410040c0401003c040b004113001407407418044103200d800d43c4004260b41c1c3c440e80c00c00206d8100680c0005964611406500c078803110000305000440c80000200c0700f04641542c50300c01002e545800c4190450710509070b80901089008001c500705511070700e0411061400761901200c0d0b561480c02d101d0a58412203801000680c210310b8545151901f400450800300200008500e0645425096000c40c0568400600019911605c00788903485403001c4405010030000300940c0300040703070a00c00042c4003880c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 173935863 1250 173934613 173934637
    0x90c06031a0a15050c1905011a06030610082d0106080106020d0c0209100512010b120a020306040212010e060f07021506090f0c0412080d0e0607053a02 66
    0x4107141c07442d0800c001500c0680d981189161001180c1d52825100d5621880040702c042c417940c07281038024800c3c142da400d482032291002003405100f0300c42c036180ea505030341501403040c0030810a11440d941c0d840408000402c2d43d04150b142551010009a103502445d00c0d1860385031007168080302140800415a816200d1540700d0103e141d0325040c1c126610b10320715150401141083c401c0c90050324040b80004e9110303846100c86000b80341c035600460511a40c50401105580d102d01e0b02490610b03005150f101181c1352038000785442c1d11f050700069950900500080c0c00f9070b0142e285c1a407001c00c00e40100a001502c45c0c200e40c107500b0115401040203004440c0840140200f020003000e06207111262030003800c00a1000f203198403201c0d4a41014800a0845d0301559020040007171110300044c50440f120303018459558480c501d0b28005015a010f28004504540000c810002c95a81001c01d03100c20081c030403c00c241000c0d5001500801c0d48440e903010009228400008000304446d0300140042c105035 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 173937113 1250 173935863 173935901
    0x21e04050639100e0304050303040e060d12030e07140f1507060203010e07090608042a0302030601180b060403121b0203010528060807120f060207060603120203090303090f010201090c0603 82
    0x6440c9680301c0c046c6004180e03268100f0401000f00f03141d907904181d040b45006020a40c00c01da1951140c101850303081c070170b4010035182c1550910a080c28003048000b840c0340c4604a04805007000002c1e0ba089625040328030502c8a2030f049005000c0c607800b07032420300c1d1f8070450855495031940d245940e01c5008444d17440001d03081046c0440c500e031103040003038040c035808203520f00310466040c0104400f41c076020301d000802c080c030540000036a0381086040e0003080301e01d4a900e00014001d0380c1070182c030422901c040c00f4a208000800000c0c020b1440101468043d2609000042800c80c44e00402000200c000c1d40c5903003050240f2030415000c522001004042c00000403212000b00e8075002600c0d564490081c240d00300280c00c1200300242d0100d07080081c41900319000505580c0c0d80c0c40100d03044180c0594040ea52000706008000407010b40081d07448490001794140b58003480001da0382c5c0300c1e0700500c0d401b8400c0b041030f0841a1b4004d400c030080a076840304008105c10b84900c0b00400901c01c40b020030502da00d01e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 173938363 1250 173937113 173937131
    0x100e132301030c09020c070e04110316090e01091109130c080606010807030c0c0201050f0c030d0b030712200411031905070e0a030210110a06021e0405063910 69
    0x124400c5032110b0611b00050507015142c00030000301a00024801d490031a01c0c1c61325001141d405020034001c0d40c442c42c49a41081d0b040c42000c10483d0030640c0c03020000e0b0314040d03a06001c00c4011b400c1c4800800304075183d00890392a01540300018102150040004178985070100b44e4541c0800e0380c512462081e601c50301c1319510140120305840b0070b20300c42d07404074002411400c09544540c0007000b0111403ca4424945840c0000c1c0a00e190b00c00c9054900183e5261003070400b903e01070007000001c0c400c0500d0a22500050740760742410541140c030700380c03210740c1c2c0007046602d0352950f411110050341c0003440561a407408580e124aa1406207036034488691800c00000c0c1c143d40a11000d08940790b01030b102035489401c0d542801881056210074800344044400046980c000412450404c103114903809601d480d064141d1060650001418100a0006201c01e2000e03480b25016254141050541d03080818005c020340c0800055008070f5096184126800f03c00b80b4400040206084140080030400000303 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 173939613 1250 173938363 173938379
    0xc01020c1911040506011b24050702070b0c012306040b030d09030f050f010912020d02010b010c030f11070609031e03210b0a030b01090b100e132301030c 67
    0x5081d600007801e505241c0080a59410541d00043d80300c032040c14680301d5800ba1800803405400ea9600032603070303400076036000b0024060098081113402d15401c81403001c0d080a07800a51280110700034240054000f241c00c004610f001d400c80c2072003000c0884d010600c50050300c58220518021109240504d00b0601c0980d42401e000a401410510399078500c5002030131075440705007600780c2c14403e55640c4036804076a0080c010a110340154144134a107075007811640104007909100d81c0300350450035a4034291442180d642c000510032480d81c2d00d45400340201c1d12a142c140c03120051521381444a216101000c914143c0182044c03040e03038003070341040e00c0003607144a00003031410f00407000800080b100c80b151402541124010b147c40340c0c070444c001c43c0c2e0481c0000802c07804006ca81c0701390741030010070004000424840c4240111413000f0b0301e0050705030b0344c3d2000151030010700c03913101802030701d241c071440803852020350081c580c00300c04c0c604400502d0b503925500703241342000780010f5a12456006000070450 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 173940863 1250 173939613 173939653
    0x3041d0106202503060e0a0512030f0610030207140c0a141003051b03070206150102010911090c09031c090803070b15010c060c020601030314040602070312030902060c01020c 76
    0x202100401034221400010407201515442c203c01c4003186010101c0010541c0c083d41c03060490001c01050b400009092544c6081c81d80020b04001510410520405a60b0b40e07200790380c0000c0981e207014040c090150114000d100d0360070003504411100c60440382118001c114910100e50403170b503010089441e0300c0c0d403256840c21403190f180e0100880840b9030f0810301a0b0401a0302280c8030306d030049040380308010181e81e40e0080b5044001030308224104003501d2003e00860440c0e600a10080281c16202d50302c03070203039140040040b4072511000c400541070f030390b9140840c1c904d0a40501501d0700c06100c10b0064215400840070400450b01451700422034480000994401540000c8448003640b42d00841e0070840e5440112141004214000d51001c0380b9540540002c000f240d41c003e0140750700d1030800030452000c80c04184035254040004001e202d5002400c0c0341943e8002000020301c0007c0c0070f094004280d50301000390400070208006000f044103502074840320640c907055521900d04502042c50030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 173942113 1250 173940863 173940917
    0x40510060e0a05040203010204170328080a051918050d050307090303050f040b030403050d0c020f0d030509190f12090614030915090109020301060b280203041d0106 72
    0x410701c54000034280702540d0700304a81090016000600d02034803845171110b03004911401940590000803942100d42440c00e0b480b00f00202c0d00085060f10f60750820040c25400080c0c2035404030303078891011600c00e40309040d52003903002040100b04603642c0341d01c40c0072801007a101002e490600400e19262510b600a20840b481480c0e03e984540301181156400e40d845e030841c0c444240440b4080c8804208000f014000307500590180d2180c0f921030382448042c6003500ca0707030101c8004641110460004000c4001035007007021150781030100f145e13551b81c0c2109140c40030000080301c0c06401b881c00c4c00c0c18010122013140503079001d00281c81213030115000a9442600e40e00c5040c0004100904454803546940c0c003958020100d0790945112000c401c0038100000000c2c2d5100352140d541c4c1c4070810451070248100c500814604041c941000c00083c3e40080e01c802d00801e500d58002451042c9003014428000c403005040102184104041e01d183c80d511070807024011600410300400ca48110300707603000f00c2100b01c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 173943363 1250 173942113 173942129
    0x110c1b0a05013002131412072108040b1b12030106110f100e010e060c0409020903070905070509010e0102030705100b01051b0a020118150e060d02030a0504051006 71
    0x82250701189070f09140381c0c502c9070000015414040d400b4400c0c0c8900081804000350b19490201609140300c0b0100c0c8421141d41e98402d089118044048280c0442e0903400c961010240f94120f046602c2c42109052401c48000c0603400c0004000c06c5011402e8060140c00364801e000b81684115400700c25500c078403035100965842d20520040101501c500e203800c441c081c0c0f040940300358080990740f6907d03180e007501d99000030b80e40761314058810442c240306030001c000b020801401c16050000041c1601d20942c01005151900060044900d440c100490001031000324000c0045150a41c401042c98201c0e00d500b5001400340b401402d4558030000aa405480d0840043d000d500509803d0790001c4c131070800348a0506c001840181400440c203408140581c060f40040d120189851000410f48180400090004003c0c0401841040b069642580a000580c03c0441d00090920006006c500901002040181c000400c02a800045411642c0218410401c98030808101015042610158049c1d906 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 173944613 1250 173943363 173943377
    0x21206090f060607020d021002060f0703150506090d1e1203050411090720031b062208040b070807030905060306030a03030510031703010e1506030a0b04110c1b0a0501 73
    0x466842c00034004c0160900c0201901c0c1514101d41c00b0580c2a40301d076a00c400903800c0f0008010708034146041d100d40c8071000b450104100e004d142010240c120302d902078503004110100c0c8000a5403641400a03a9140d00070030303000b030b489480e0f0000301d00700c030042102107031443e0400d051306031802e009010b854004c44c0d110300401c1094680d01c05000e12800c00400c0384042101085c4815610807030700064044403e940c1340610343c0d484a501c450001596407031040f40403588400d080000d240c4003103140ca0b50b15004500898800540c500f454400ca00079a04800b164005c0024500d041040000080a600d48a41c86041c1d40319650f404210440c0000c898068060b0000d00c41c0c5030010b0700ca40d11280c1d101c07680000041321151240c41d00010106603071448040200004010310003041110006903104a0403d007540c8041f0500010a846000c082e041001c9189c880502100e141e480745c02180300c4884680800d0b44515400d46803940da81444031011021920000501d005810001c0500040e210107845040e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 173945863 1250 173944613 173944621
    0x5010b07140c013606021b0a030f0206070507090f0b01030f0603320d200a050d0302160213020306040c050403020603040b071107150906171f051201021206090f 70
    0x10079810104d540207490301c0401c10b0031084d04100c0101e020040c040303a44c01001c1c4500c4030003c01c640c1d50b66080400e0320036060f015040000881140c180b2843c203034140e82254880d401c40c9000c43c500b0ba0b46812a0803414100290090014a581c1c0b1004404009980500452a00074464012101507000141480c54005003c0818100980002c0340d10b1024404009500d52074100141c20450510b41e601d00140d24001d50070f50107182114440340b8461080b001d0076440610381d41d12543c4180d00e08200040c107801180c10b00c2030fa900882c01c8110650058011b5458002c004090002540100ea0003441189042c08089605101e0000e85041d00e034040d101038990307101c1c0c1d00c0c0d10003039900041254040007018040c0705031901052146200034107519008050b04030300c052000c4c0c041c0020785c0204c3d04001140d441310150008800405070005140e4900807000c003140419500305d1f6075280c00150704034a6516450442010540c01048180340e0700c42062060f445190400920260603206180d0000c50b803000300d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 173947113 1250 173945863 173945897
    0xc0105090604050315040b011725080a030201140a020c10020f0f0c030d0606030c230c070806160c0c09020d0f0906020a02010e07080d08060301060905010b07140c01 72
    0xc0800d208000c20041c02c083e5207000203494005502203501c01c1300491003e1200700403c9621460140000607504090a841c07650321301d83e10541920359600004510440c01c600070f2110118501600c01c4406a40c0300c0d041d00c0c103000c2d010304007807281c6540419500b40055031130001c0d4401e860020307e100c0003400b0b0109206480074082d40059030300c840a40010030440c01c20008074002040310317460b0b0401a503150018440c1d030034201c0b816640030b08181400d00040000c1c085d4891201d500a03000c001400710703004507200c000851030042c248840c44501ca05071002c1001303800011402d1141c0e101c2816050f1150134a03004490035016904c009244060303901080c81005900e4014251000d007099001601c0b001c00e144002c143c3e1100041a244254001001650130354280629008001c021004240780341c40d001d005544d40d11400c039004108017040007c545903a40a4000800401a4083c113000e15611a0252039a6502040302141c0c00c03284505222146040800d00e59503500c2c058403500d410548030940 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 173948363 1250 173947113 173947117
    0x9020f03061603021309020307120b1005090607050106090c050d05010803040e01030b0910021801020d03111815070c06020d030606020606090406020c150604060b090f0d020a0801060315061401020c0105 88
    0x310017401201c25001c54002100c1c4055886030301c0c01c0d41c072801c0018880103580c080301d80e050b544501502e0301c18090344955402100302d40c40124150342c060394070704050509a00410070b032380165648a0800315a0007032558040080c3c5007000ca000e82c1040340740d9940c000181c6c1c81c40769100c0c01d43c2030020000100045001c03400c4041e80030552009481603c4a46c00f04107049901030118600400b040222050080d42d040000b40c40314405400c0410081d460f802c04400c640c015481d4440000702c055258800c1a264040e0a20100740309480d03c03512080c00e03181080d0034002500803800148601d429080c0345906c24083d500440340300e600074040d00d0f00e8413418090b4102000300709461054080010102e120010000030071044030b00740d4610141c2c00d140040000741c82d140ea010321245c800c14003d10b06c40780e94030761070f00b07602c00c1d4101d50b00c0f404201a80301040c100080e0780d200034555481c0040010a000b6901e8030b050030f40c00040c008001071911a210f40846803248011907005034408d0400078520350003200 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 173949613 1250 173948363 173948377
    0x50a0f020a0e10030c0e070903060c02120d0903080f0f060d212a0510360203010c0813030e041e09060b03030403050a170d060909020f0306160302 64
    0x10000550580700c1d040950782e0380302a42e040d0503241d1050300402c2403200d00fa041c5405424400fa17051414140b011004084800c2c034000500442e90b1007400d040300740e000308001046181803105064a5039031480d296070041160340c0007900801e500d0f400048043c008600341c14400c1d400c64405220f1a22a682480105204544101c40d624943d001d80082c41034004501080070125545900c61404420280105119045800103142038100c03503031000101d000c2002c10100f082c44a000500ca42c000c04614140448290f007002ca85000016071000c00440c0d503c400262030007a802448105a0100102c4014008a48a0400c02c1400a0002c00a0b02c40e0588580340580100042002c2d40c940701014080884d1410800c4220343d5405444c0070405d0701d00500c00d812400710050f50405245486203030301d899881200601c0401d150710002d07070810404046d20100c50361a082085102c2c1c403102002d0046c0007516040c0d10601e24086002142d10b03001601d0303441103900f038510300102c07102514140c002e508111 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 173950863 1250 173949613 173949619
    0x4050c04020313020a0f0810020d110a020f0105060108060603010e04060f150501020f0f0d0c03090e0a0605040b03070b0a18030b04050c01080a020a080c070f0b0106030b030706030603050a0f02 84
    0x2a0142056900c900281d406001143e4007034107001602e10402c4440813943e40400404c1d00300320346c00c1141d6000442e00f600600c2c034814000d40d0700c0c00415411001042a6142e00740c141d41e01194050700e082d40000e19508006800c4004c0000b901d601c4019070306404100d4101703500c00c100b00014002c2a60881031a900700d4428440402c4c0640311a21450036154010070141d000142078004100b10369040000a4902c40a0405003090902c070003d6181c84a10002c150802e029800813200100743c440c0d80050006c140c003808240303060038400208800380c50305d032003402c0c0b06900b02150f0840c50b01d804a85c10084692211085181c884072a909a69880d0407050183c01700c807160348000041924070f15081d120324403840160644043c00c4e8000750031108e014210403585481840007000c15070704503602c035410403225868103031601598030b000c1d09a13540c080e10003000c000e1401c0c0000f44113901908075001d8918120280c030b6040d46ca44d2422000c4402c00d00c805002680001c43d09000300d00840700c4941c505d400a = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 173952113 1250 173950863 173950873
    0x120204110d05161b0c0302040b0102070906030302031c0216060507140d0b0907080103030206010302011206081c0f1b020d0206040f03080c010b010f0e01030c110115050a0602150f0405 80
    0x40c00c8500b25007044401c5041a8034501d0342940301684407076080700d14080003d101c825000a51213040319006240002405550f8924410441e41e008000c248000c0641400500c075860700d91500948940000c2e509051030002185586c0031803086000b0742d40e0055120b41c0204070000c864840002418001d442e98040c003c41d00741485400200c1401000400c8203140d0115444a940b014403041202c02410319007000215001480041c1e404036540c1d0440760246800a481032040c4684802803645603c00365a500c101c618a40041d00002d10200c2d1022007901d426506100c1554140d80040038861512048041c0981e42401841d1000307000d20b80c9400a4400c070308043d120014015403805e80c1d0015519550b02103103c1e001c0c0d900034000c00301309020038602048000000a40a0004080b50011a05141c4c0700c6c20600c240300c0c840c1d4107a054a481c42d9000344a2040481410300402505005040c022860711a020815a0000481e00f02d20801001246003560b40c40ea5100004040640202c61502038 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 173953363 1250 173952113 173952127
    0x20a060f36030804030c092f12091b19050411091008150409020d12030b15041806060503061e04051e0f0c430b07020712020411 56
    0x446151030020b544508240c656450035420580614800c5a00c042c03100780c244544844007185007055156000c1c2e0505c164840320700410200109406041211185003000340d0070080f500c030001580d20081110521034a200081080510402d41e84c1058900c0080a100c507041000e0704040e4848201c6c085a09001801c000310200005c12007084c06011313000040c824401d01168000b102c2e04001181d804803000c002515042d40440c0c0003040c171490281c02002003c020300719090190308401940d403002000d10311000c40360091055036400c1402600f01050400440210109083c42580b05494403a110182165500f0041109030f8451109e0b11002400000000407c0d84a40c02801e010703042c40b603103802d0303424100080445102e8005244ca400c00c0903820a105980001104466890794003100c814030042d4011a1445682c110807900e0407881e003094008080040e880d034a40030b046114240c0031041e920f403000b040b079807003215000c0c000d1038004101c0048014945079110131605000020104e0401c50 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 173954613 1250 173953363 173953457
    0xc2c0d1a090c03060109200306010e0a0f06200c060c030f0c010207030f1814030708190501050f0c1215060c0a0201090504110304110607050a0609020a060f 68
    0x40c19540550264010100000300b03180c00d114203809041030301c0701009001c22070721140c1c40c04c18002003004140c001c00030121304240d108030700c50a403c010290484003001e0381e4501ca271401d10317064402d030000207401000c948424030440640d01c100c0c4102c04001c1c813006000750100320845d400091b801c403141c84100902548074421001410003150f10303000050300d4007014100a4114160f0180a44c1045080c1c0d00070f1100c40c040845c00421384052401d1401c074404110007007490a000e58207d0381d080d01c07660014410048e0880c81a0a80318440c80082c44142c507102490115900c041e902c42c070006c5020301001c070559002405103680b00707002d100d05014541c0d8401c046201544111121003694010084580035541c2020b600c500814050320204180544502003100601010f400200b0406418040350a01e85d40d1001392489260020b00740c940d01241031074040f0003018001d000b01d003d02c0c2030810003d03415000e040000e40ca8045078072450b03903240d6507020905640304c00645191000300074a01a4460070 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 173955863 1250 173954613 173954663
    0xd0b040b1f0305070510030c02030a0f030f09060b0f0f010507030c05011803080a050c09030307080c010603080406090f0902030609070503040c180207050c0607031416060f0c2c0d 78
    0x54010f20140044074100390511103148400742800c0185801c2c581883c40d8558000126a1901070b180b52060fa01c0030846421806809080c81015031242802402000c0c0035155111082807101100c05180003106c0400388000291861140c50204209000e80da010070300070302d10901002c0c843c0e0000107840c81c0b00031511503c00c6a00360150b00003a40d0b24108200340940d4403031180c00051105001303080c0940c0d0000640d49202d0680000c080300c00124964a803071909401403000703142e100e0000d0340c03203680300c000c028000c142d54814407801c02c00791080042c2c551618802c9074082c1e0405007a500c100c0d95400400d032810752000d8811110707016900000a05000b80d200410f003808030314500540c0d0f41c280b03803c0c05850052080640c40c85032808110740c0c00040d07000710103501c071b00340e111806d5526080002c1c0d00c0f00ca4108a40d40140c0860305101d00341e9248410390340404035035040303030f103403104018031401083c44130014400c00078043d44501400c42d4054a03248041c502842d00c03480c04640c4180d40c22010024074 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 173957113 1250 173955863 173955869
    0x8150708101203030903020105072f1507180609060f050c2a01020c010801140904080c010504030203090a080303040f020609030a02120109030305070c0f080a05040312020f0c0d0b040b1f 81
    0x260750750004410540d0a011380c82d0041c00a14000e02200c06050107460400c85000900d507407650202c850007900b0708240402a3300b9814034540c0103051802c10f2026028900036001c0b0041d1000c000404115180640c02d18025504150754010000410100035030315548001c644580700d10400c040003052540000704100c451250460400c0d00d1132082001900e09032500243ca410301203a0001030040d0346100c400703040ca9841c12150000140c65506109800d4440d01201e00115403e00f020801410740020043c401c510040d5904014a41d6032030100b0b45038041920010300e602d601821800c054900440030308001d82005040e2120b20b0f1841d0300045103c1d440003800c03c0d069440e01d07018018950544901e66004009007400c0903415002e0f55410440103c80000801f002c0c1c0c081800e4032003501c6202603070040c55001241d20140641c0650182d540d03489035001c03106902c2901414821403c102c0001d0300840c0e4041ca400119403510303502d15079125801490710120131112607041e0f181c5640100c1c00740003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 173958363 1250 173957113 173957117
    0x70804050f040603023007030302060a0c030605090903041802040e06100509030114040b0901090308070f0201110c0105040c090b010912020328050606011d1c0210090e0108150708101203 81
    0xc003901b41c0c000d03040c082d10340c00300309012500409005c101182d004554198051814040011551046402a402084103820460f04402844200018158004020b0040d600b0f0320103c0561003540c1701211040c1d20460003000360000300741d40881e40c0ea0070040c8580a0b000d030b80d420044c2c1040c020300080303800c40e83d0300012016084060700c24001032001050200e0b80002039940280543c81041d200030b00010005402c01042080007404441014400e5214030030001a0010580c0c1c0d8001028026000e45803e80e010348001c002d2680002e81b00c140303449442d22007a810303100c142d0000c1ca089201821010b00c00420707a0580140800710081c11b10b001000a410004546064490041401c200b403901c03100600b9181032201c1140d141003000131a040b140c201c034104030b0358042c40c1120b24102c4a4040c910b664001d401c03441c001400c0c2c14082e01b0180c22401e40b140c42c00c18607035a0780d9414140f0b0b500c0012640e18040354100702c0c04180e105104211869001c40c111510f0200036a82e14400c031400f032110300041d00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 173959613 1250 173958363 173958409
    0x190806134721061014060a0207120f0803160e0a05011e11120c07060f08010b0d090501050c0c0115030f06050705040320041404020f010e030c1c1106070804050f04060302 74
    0x100f00031060f1801c0003002c005407806070030000d0701c1c1f0000e03644001c070340104020341010501800402c0702c0303071079040011640f10718550b0720707800c1075880d00d40c01c1440a100c4802154003050a15058140610000215181603403240031f0b80c003450028142050300c1840d802c0800641e00801140401c040010164120048440c19502e850102109040c01c1e6150012000c000032140001c004075884000c66064036030b49400340e55200041c200460040080c9000148154200b804100c12440c440d4080d100c0548820000d03c0120342141542c0003010709800003d104441c91403540c0086500c0382e00143d400500c03030504515107900c9485a82d041c8226250500414024007010080c1d4102401180509103050001240d5410250b00040b4104ca00004c60b504015900aa010180c3c1c2c0030050100603c601070b00481d038602108900c2c2076583d03288541a940c00c404246ca010450601c84121250386400c0509a818541000e0400ca4000e00400310ac6600c1074540c42c0c048050b80d070f5048003821a840e2540700c0c0c2 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 173960863 1250 173959613 173959619
    0x80a02150c1b0f030f0d09021e0901120305120411030a0b040507050f1e04060b0c100509030901080a0504030507060c0203031503031908061347210610 66
    0x854414a41640c10450350800441e10545910000c10717101500340c0030380003586801481c004c2c8801002c03140000384d800700c0380030114425007240d0503864801000a0382c040346640e0300c40c690a529241940b900800240040050070350002c180c40c0306a800c40c0c841c05481181750a4180000d141c20118402556050051b0040c0810003801700941d200414042d214014280400c07400501d104000d03032400450252006801d1416a407103a104170041c0c082003010b55104c480c04030503a176581040343c1c860310660345000c01003849010b0000c26510f042c80169643d04203a6101030682d0041d00b8058400c4050000178448000021660300503000d801c41f80d035000f1a1203240c82510000c1d070b201d140c200c0303c1c0a030300200891041a5400450008827400307074140082c0310b0301d8074000300d036441c4400c40001c0900783c41c2201258900c91003d2000518000c59007911840307030305508410030144d4000c1039201c9102c80201207003640e4140441150441504501250b03d001c42020903141440000c0b58200c100400c4200d0034 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 173962113 1250 173960863 173960887
    0x3050d0306050a0302180403090503010c0e010e030102131703040302030d052d0d020c101802090708090319120f051603090c09090804031403040501030b0603040f080a02150c 76
    0x700005020032102840c2180c51600400d404030700915010361046030000000f820302d4080d0454000030840500200010000181c008206850706071221340000e5203004403104603d03050003610b001034064841e1140d018a8401101c940f13014001000362a800309000000260f0380610602007021525200c140d900c0c10b8134810100010402000c5500c00808402c44140d0301c003651066507010030401200507508d5440000e41854404041c0e8507029890a091840011412840013003060034405d40301c09066071655082038420f100103c4806049501c02d1115800c20405841c429182c034089052a66114580742008403e540b485420f10324506e403030f441400394022880107001e0320b0200a2070302f0800c048c02950350340074034003240c030500d55000c1d140c040c18018003004070101c0e03000b145d11103a5024041c0903401c0703180d26900300f8030a007030209250048142d02418194100d81c442c40d48101e80e000f090244e40c1d0b0b03983c2190814200b482c110f114412982d0543e00c11003803040d0103027180b08101d60b1180e482d1658 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 173963363 1250 173962113 173962121
    0xf010c050304170703020c0910030213020a030b010801060e0603042909060a020c03070b090319032f1e0d15080c0105090114090117010b090a060806010f0804060e060103050d03 77
    0x20481d0104100101c0172990200d02d0700318800b411501c1400712740b6900540202159503401c045d620070104812511a521030340e008004035103054900740310321058400156005c1c0824403031b260108804081c084450700c1c0c030344000c1d640180700d502200108405900701c07440302e102d031810003000c0c850440c0600006000401035164004805003003940740800407008180c8900401100414400d14003020500400e010700c01c0c0d656084107407000b84820f603550b10009025003800703032040d02651b015205814004a0300c0180c11421460007030441e19020f415a804072203010f28448000d444038046c03100380c6400c1c003c5c4c000d0340e08000380c4611b2903d071a42407030604d904010030b08442a040c400c04102d031008903608001031211010014040a49485c10400181c1e8654902d180f4a00302000c900c2c000315801e00e841000c1e10006505440100315542c0b92030095840c0d000c281c6005001c191042d500c1808988140c0026a020b0310441c4080740300c0640c03100711440c040c001c0e001250517400020180c0c102c183c0c1813003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 173964613 1250 173963363 173963393
    0x50c010e01020f0403140c06030c040e060604060f0f03110a121103040209060d050102090d060501061107061b03090b03010f0302120c0906090717160215010f0909050f010c050304 78
    0x3103150440b401030b00d41c540e205511001b0210002c0d84424002c140c0240882c148485010341440d560340f501c5441c100702980280a18004d2900140c00714242d420884140d42c02d43d440342d2a207001d02141c88c482a40c094110910404c00c154440c4a00c01204031208080c100c1c0e2035550300c480220300f800c0024801603502a1200900d001c00900802015990302c2400541103542501c0505204060b410080d0185c4200030380f407500b1a0b0760340780500400085070301a41c100da15070b90308d4000d01201207004a4803040c807803290000280c084120804280e203926510080607219050142c900c0e41e4902a40051740c109904c0039400c052041420015410301450320044030784ca4401606858034000006118050041c240301d000d000b415000444d001d0051034850840707000c40307041480c103240809903250004200100c9000600a1700f00e4018800c001182c264140d0301c58005490720241081c01c944001d0900100540705840b4590118000303090a12600320460015902c1990700c1c0f8180c1064440741003200 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 173965863 1250 173964613 173964641
    0x1c1202060702010614061b160e04030905010e0102071e03051f0c050c06010909030c050f07051002010b03190501062d0509040b06010c08090a06020f160305060a0e010f0507050c01 78
    0x901407000e5600c40b007c071043d03400a03103084600b0380e1403000002e180031095441151050b10207c0c021a496070b4006145200e140303e80e8940c101c017a180c01c01111040e150031102400360303112400c10310460042800c042c00c04030001d400e480600c2d40c1ca4841919100d400000d0010761104c00d105a14aa41c1a002c2e0554264107802c10901c0e01ea800c240041d0f4459052083c501c03820b6807035079a00d0805120303203081c8030340b50f40001c1203440441c00c7c054469180d450a11070b6512030302c2000c0c528030b40d0700d0042c00f070f41c10580380080191080401c0c3e030800c840440000c0f80102c82c41d550300c0d0f4000c44c444281c541d00b4400e481c0321001d542160150400301d1910380d405900014410510007040000003404010003550144003880c0c0070741c00c40e40300e1824004030f004e507018060b0702c20911030300403407201d900203000340045403000121040bc0d42c503034070402100304680c00083e29039004840015111002d9812404098820071b00010300a8003003282101102c0c010b448400001d400000c02d0f801081c001d024140e41c4a80030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 173967113 1250 173965863 173965889
    0x70624030308010e070507060603060b030601050a0f0902180a121103030f04060320030a02180409050304150c0f030c0506151e0105070501091a13050c1c12020607020106 74
    0x10380700940b003030205100e142c1c08081c00c0380015044034411010b072152558020424800582c603864a0310161180c40741150103403182c1ca0001401d1703d0f01504603811104840c2c45d900026081020303043c003962002e540c8001c00c14189a071701ca125224140040001c0400034200c2c0031808003450121950b8607800c000c1c41c440d0784288808200c4110070b004950032514181000500d44941708d040c1001080c0520342d0310080300b008000c108042c9016002488200c529001524500300d45404200442d1452003002e080c69101f44002e1040441d0070010028000301d9040c1120f48000c9a5210550a804084201c0001c1d4043c54142d00304201088860b80114902e070500003051101c07008501e10030041100e04141039041d103000201c5034059400c81e2101500540280101052414070440062109954a0ba55148500018104802c8000e0381c1d1400c1c0d440000f51010300c20001c20800141860701011406c00c0c504646074002a0340310b0400501d08200b90050061860584000303421603015501c08003894640c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 173968363 1250 173967113 173967119
    0x20124080d140a0e120604050606030c04020f0a0305070c08030c19050a0c0b0703090506150a080d09030303020d06050301090f0507060c050307080708040b0309101104031104051902070624 82
    0x402900c051030004e142000861240d240060360710707071032284c00415501804041c0024008045903c0d480b50380d0950448800c2c00404084c00220300c240c1e45401e03440c03941401005101c81c4a43c000a401540910f0000c1c004101910f440c0200d070b1094a208241c103a00149400d902c1c1c9042481d4042c00b8460304005007044078611010780310009240c40207094024640c00203500900a60241110766003000441e545454004040a51070b200e04108511510007100b0000344003200040400000c6041d13581c0120070351956405901a401c100d2521034174a07100c0402050700e8900f480780c10380302c03805814500c0100d0a0350038424282080c5405c0760041100320407081010880000486070b0140d84008040c1c0d8905880c10402c8042c02590031940d882540001442031513140082d003c04d03601c2001808000100440e000415148a140f0001303066480548138030f00c1c1841e0582c0074541c13010b46e040502e288500c01c2c1c0101012684001c008039146952071407010b51001000ca4000740e0081000841e500041c2 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 173969613 1250 173968363 173968397
    0x30c0906080a15020c030a03150f08030a0e03010b06030a02030a06080d0923100801170319030c0e0303031e0f010308030f09150c1909061d01020124080d 67
    0xb0024030290601055442e4403c0c01070300c036811140894052400e8075226010140001c001d8140d4520f107003e99a8003001c04620302c1c0030444448201c0c0c1d06600203502e4585000b070706603183e07400019225450755840d140c408258440705c00070f502c80c25105400603628a021014402155103030b4210039500c1d4440b00150b4403e40d04009000140d4030041021561000711504c20107480300c0002c805074200c414280d55140315508442481d069400c000549080080017181455407401015280740300b551005501b80e00c0ba80c0203502070010103c1900d00085110340d4400400e00e07551007914030019540e0060030403c8400d58074609150010442d2029100343c0d413540e151145d541c0005019090010700d010003098001c281008401d40400d101843e07101d1616054a0b5141030740c1111842d403141040341c17051142c0851040f903021080e20b0460300c850390452000301e01c3e80e402d25110200d0906641da598005083d01c265010041d01c41410301e0022a081030420071a50b0401c01400ea08100b0710540c030015036a150 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 173970863 1250 173969613 173969623
    0x206070c1502071106070f15020306011e2006100603020f030601140706050901050601110c31020313050f070e06090a020721081303080a1a1207030c090608 68
    0x1407001c01685406490400c0844211a8000d0950001c400240d030020490401713055100c46d4091850311541c0c000c40d80d6058103900c401c0301c445001648111989200805006000703104501a00d414405400288004001c00340c9044c0c50403480d80c0300c0b404000301020366031420b4011306110b00d4250304011940078000107900010340682e051003d107030303d241031044c2c2c02e01c03d035090560004c1040c04541008119207000f40020f0701e460780096000c00c00112886030024491086104c05000c1408103d2214038802230305081c0c01c0045800c00c1801d042402c8002c40e030010b540100c650401c0d4100000c4e00f03160240c0782c0380c0c41a11181250b04507080800001c0310705e4540507030040c803c0e00c42c0300d25540c0d9411907030024800c400b8024141c21a440115940640801c2d00102103951a01d034a1815104c20607010b074a50601e000c000c00140d09440050a90010b0341c01c000f64000860000142d62421000000d26500e031140c50000d850780400801c1060000b00300703000d0006c000020381000030609110020b80c0b26 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 173972113 1250 173970863 173970893
    0x71a010510020d05300a02030708310203010b030a05061602010b0310020715020706090b010e1b130305070e1b070c05040c0e1908060603010c17190603080301060206070c 74
    0x5130781249803204500d6000540c8128203034805c070405c030b0289018a20b4000a4009a4110000915500c0010080350300010a0b1803090440c41950080303410803c028100820004001c0f81c05549400c3e40c000d1549040001d85509032090028000c2c03407400d1003d0b41812107044c050401160b04003a9102c0e03064501150442c00744041c6c9601503a502803506084848030300342001c00c41c039075100052450900503103600100b83e00d0301c40c200030300b06a641c4030b524990003001607640d524800c5c10807451800d859400001004540c40345c4072030003101d079900c0d210642841b907182e12038130108424808010703604407144d800362084000d0302d00f043e0804030a034644c1058103030280121405607594001081402c0c1c003d08011000501c02080351030000c9258100c43d4803a4081d1246060f10f21609005c1041840c0c107015034201d8200036036600c025200080b8129000c0b400c06020150400703940c02c01200480600d0203803030301550140301840d42c0d9500d00780d030003442c05070006c004508100f104000c000000d0060100e103160 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 173973363 1250 173972113 173972137
    0xf090f01060c051203150414040201050307030f0e0303090303060901121106030a1d010e010c03090f06090f06020703180605030702061902041706011a030912030a02071a010510020d05 80
    0x80850b2441c185181008802046001c60004401c0115050401900e89101d81c41650203000002e80c8040500b4640b10541e0001d01003042800005c4240f4881ea00c4094900a42100400c4c148030900300745046510540303440405820001c108941424424206401004141c038242085801501c0d00c00503142d00c4c070750640c418100080405d02e02105500100f0b0081c4007000703400400584911140e000f4418055400070035402d001050b90064000c0c0b00c1e18a803e0780115400e600c902c810381d2544024a4001c90844010030b02c0301c009004250f5070b01c05040010b100e52141d40c4800d41551141c0000241c0380c0c0410b040020400400c6885540454425000030024031500c04103010141c030300019015641107220a4418200010311203480002c0300f9041f1504410f8441c1901911003002c01c86200465200c02030b503201c035030403000003050398000396400500b1036001400c0654030342d0790020030140c0090840070038aa990041c04186804070b402040318a450009186140c1080c1004d4454029a00840302d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 173974613 1250 173973363 173973377
    0x5030d02190614070c050d020d020a02060901111005061305131202010e10060f08010912080402010219060f0e030a0e0103090503040510350c16060507030b0f090f0106 73
    0x81100d55000310240b000f9590300b800d164a4000c03001856401e800e80e056a40d403080c8503008070401d0000c6001f940003c4170764050039914465400384110355005580c500d0400601d00c07071400341c00d0024480c0801000d03101001017801d040c1740f400c00ca4410800d1030120441c0d8071341010b0184108000b447c0c0860254041800e0480010322103003030703005001c90780c41c0d450300340a10f40d051694444560f1088040d500c20f10030400080b511100b00318200ea80708900141001e012503003454445021f1242c065000b84148119840300c0884212005603021411040300e8407a1545c100702440551030040d000d001d0100002941400d941c0f07c001850001e02d840d259050550340c050080920a040c0f040714040d160140000c800c01d003000703000806c00000b000d0304d450300100d800404a18511403010f40740c184503002038120f145485120801405500c0103030242054070310810040c0015600e03020703c40c803d5105880024429821005114500d81c541118030f108440308030420040400081c440c03819548a0700d8481 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 173975863 1250 173974613 173974663
    0x20c01080601260108010903030e1501031407050415030302010f0c0e040c11061302120c0603040b070c14010209150c0607050a0c0c09050601090b280e090c070201080105030d02 77
    0x14000c81000a00407110740c0c1d41c10f001080250b01504046246840307658100106040d00c3d18003902e86801507641100346a0100042022170061074180380d64440680650b11244e540d40b0014003200d0380305401c03031004240903004000341078081c410345420000003e81441000c5501c0401400c005404081c00d110310760b80e20010a21500c50b69801c45003e10010807030391703241000110300045a4418000302d10400203c640302d140d03404045a4038583c46005030809065480e04e1b81c400c04c0325180200140704000c108840c80011881032100a43d00c0a800400181d940e140d0f407042c060f10184802e84040613500070003009145450028489503c045140740503900c6201041040307841c13040c4540d01400c0184130b41d1340803420a44540c000ca009140c2600c800161507500c0d180000e040c010b00070b990040944038134038110b96942052440715070b20000d16000076843c3c0c420f0001020003006441e6000c043c2e002060810840d6080861a400b40404900401043c07041d0340c0000d41e941a10508160036241c200c3c424 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 173977113 1250 173975863 173975897
    0x80106050d020f040308071214030408160203030a08040b060a08120a020a17030a061d04020f0310020715050601142b18110a2d030b0f04060606020c01080601 69
    0xd0f400c2c6801c03440c0600c0d07032250307607040050440e00005030130380e148204c0003c00400c1e103010304290f001400c5a40c15460460343c1d107443e20340e4240c000000d01081510012403240040ea0284010602500992112001801d0a0800300382d08440181348901840b42c014083c401c404001803916040c00c0c4840d881c50341c4000d0080100c0c140070309140014491340090350000c2e068a640170143d440b4a07600074080005039511380e03c03c052a020f09903c1c50078501600049009402c243c4809028000042c8c22210200095021101203038081c403c2541c04200d8040c1c21a0014224011285c100b40246050140d0701c010072200c1000b03210300400300310086280b044022201134090300d100412104910100205e5654901c450301d28400c00c10212119102c1d10564003040c07803e040d101082e15071900c0c00400d2241c3c0e48040400c4107000e014622001e2560b0a0000009170b100c0e10518810324081402ca005400d140c60701c0400c1d594031b03030080015900101e00305030703281e42d22400c11540080c0928140b10490303001c42c3c6c0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 173978363 1250 173977113 173977117
    0x140d0605040203010308040905070801030c0e04030e0913021f080f070c05101a04051006030207060e03040f050a09050f060103090f060501090c1119060b03031204050c0901090c080106050d02 83
    0x10407500240040000814004220040e1045501244051085a41c2c0004c22101400c00b40001400040052000c0c0000c60410004540c058464100004000b45041c005030b181103088908007012200c0c1d0140700b0450401d00d5070181c80c104494140800c1c103218a0028010400007895030b00480d908800288186204010300d000042c0c210082c2c4502003003040d030403005010740c41c18070b80c0348410f0709803008118142841581c0c407615035000d107566503d003041000c80196106201c261501e80d1511503145040c10240001c1c0000d00300846c0003040340346400180300c0880070b00c1e0710194482c1e280004105c88a0400ca440c41c1d41318900340b80000303500c040c1e1703c1d004400150f5104094000d610302400411f010140d544524030041240e242d00c1c41b00103210b03846995498050108c0000201c0c41904000010402d80011008210045c242c0c0c1c10440340600c0e036611400129416102c69020700b9441c0070382e051909107a0b025002c062001c1c0011108110080c00c84001032140108001c40000c80c854812400d0341 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 173979613 1250 173978363 173978369
    0x90906060a020a0b04080403030305061c061806050108060a0b01020604030903260a02100510060c060c03180b07080c030610080c0f0406030209041b0c08090316090c021b01140d06 78
    0x2100345505290a0001b001d0700709000c200e000c40d1030035010545600d00300b2400414140a110140c5541255544a80250401c2084403005508003080d4100040c218000c0c140a440c1020043c862840c04081e1041903a0104c040c4030305640000d401c0c0000300e9840010301040e01d0f0850000000c24465001d2055580400310440207000c4001c0b60300c220180c1d0110350105000d114a400388200d489100c038642040b0820b1003184d003c2207800c0c0c41c47c80003500303d410140301c80505090020360103180251014400416500440711003245404201489800490594000c0605c444090540c0390070008140c9480c24219080705020312540042c007980c0c254011209c00d082d610400903196540c1c1c0710301502940103110014851400c00b0110100c40c00401c40103004014a079469030001a4141c903030b00120303800f02040d0754050003035203071050171a103051603030b1002481030090000d41070b0200030f8002d04107451802c8000400b4185d100c0b0701d443c0da0303000034010801043c0c428055034451800000c0c6000f0620391b4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 173980863 1250 173979613 173979623
    0x1503240b040e190c0f030c1b03030e01200a021005010e0403080a0e10090506010905101e152a0507171903051b0c0307030f02010e030a0c1505090906060a020a 69
    0xf51400d0001e501c000b1039030700c01d221600e06202c005000302c0203854188100d065801c07508d030040904c03008203210b6003181003111040e4000051041d0307a03845500404541d4103070b800d03565100081d01210700d581042045d48440114004004550503c40480c04400001c1c002038200b00c04030b0081041182e1b241c2c01150f048040004454807000c2e15007030400506003411003039603d80030f403000000340c41403d40a51481903c8076100c00d20000d04206021264a04c01220300c4082da001100104050039120881e0b1159441e0351101240d1605130b1007101140c5004080741e110364600520700b10f000a07000039415040d07900c41c1030118801952600d03401d113040c010b051501c4011305001e440e081890303004401440c1c0109004201500400000d0059a54141d40450283c0540c13140c681003020460119643d0805841494112001d625080000b458100d001d04151410300a82104000d84007811542c40070f140b1040c288075003000d0814002031043d03000181a86d0041000150010b200d034400d015000c1242e51203 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 173982113 1250 173980863 173980871
    0x6020913060501020106080a020916050c0703081b010b0d062d0c14070b1314030a0306050102010b030d0e12010b0a090212060d0503071b1503240b040e19 67
    0x1140304030041c020520400d400341d440e00070042074040700481c0380b01c03045401a10701101078403120420f03008403050650030010801c080c070507008014824007088000f180228996a1124813051280c110000740c6540c490140e0316010b6251040d4071041074441d8400e420000021b1881c480045460310304410403200a0720540008041100f00b680e030380004400a01e60b03642021540e041c90050350380c2d214120002d424600030a00191014031000190000d29200c0c4200024042060340114517581001d801c85010079101c62080c8441e59091140218405080f0014001c00c0c48240c0003914000051280c139010b0340040c0d401640c40c4009401c1a50040005041240742e80c2c0d80303820240003904070300300140c4850407000c082001854515003009440d0b030081c01039131400c12036959801d840b1a0648000c2800f00c18400009084114207000140c0341416443c08528890710300c200c1082c0c642f61320100c828110075240148075211804055034240c94080082007030075250402242e031895001301800300f80e107042c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 173983363 1250 173982113 173982139
    0x1c03020408070303020708070e061c03030207061b1403011a09030102130e0103140a0c06031d0607111e06061003020904230912090f01180f030515070f0804060209 71
    0x10001b01c040803500504191032141c0c0d214004a9049042074889640c0580c90030446803101c8103080d041c032202c40c821b0900524041c8107583c0c0409a0b80900140d00c209101000401e99480d04648020000c08007491410316540c10314001c04a65041c545881c40c0800c0045a0031000b0b40b4254121035030900b040e41400942641c4804680f0b15040c240411182580031000c4c8400c060800115811703038513440800240580d0030700504800800004801a800d003204c0ca0400e00d0000081c03003094090302c200e5856183d0f01150040451500102d25110300801c140364081d0801c103400480e445030444070071241ca60080d8610030b0228003134060443c686a0140c41d01c403090113501d1014a600041603924160b400d1a60348490360385c0e481e90880200401c68070005c21070000203241c21017080380592014101510100b00f0a040810702850542010001d102d50102c20700030301600300001545080d9140411542340f0348040b0003480d0114100100c82030003240000308042200c41c1e0180c0e45440c2000c0c2820002c090 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 173984613 1250 173983363 173983367
    0xc0c03050d32071101020406020a020108040206160501050615130b0a050705030301060206011805100303080c0c1203041a070906032c2112060d020f060d091e051c03020408070303 78
    0x543e00140442c0001d980c6428111040c026502140c40540280c01c036000c294005641203400240304030303400341041001898520340781450040391030241000003200c0c50724206110701e9400074841000c41d86018864940d02c0324860004405171800540020744600e1100410303180f90050030720003041ca0002000110f1303880c0d40081c19504891480b0800342107040400300303120880c1da05a0721200c80c0c0c28402014808240200c8036641c011221320540381c40e100d1040801c0d42441d070401102c003010500041440107109000c1b21511031080c418130712651604103803e010704540030510415040c15107844501e4100142a0403081c1030380c04400865581051b4040c803e620740305120b00c0d403054200d503400c007002403528807c140e8055011124540701c0c1a10ba140c104140c0e003040c80c0c0100d074440c1811115180c19150310001c0c0144002180c0017185664103441c0601c100080071100c1002c0052780c4840402080000841e031308089824214000743c01000c0504074080c1c171440c4c000032080e100c6c11720b0001c01c0607 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 173985863 1250 173984613 173984711
    0x30f0613020a060302030c031f050a120c050906030a060f0f1e05090303010b0d0902031c0503040c05030c09041203112d0403020d0b0c041a03040201030c0c03050d 71
    0x744220b4825464070707115002541240001c1d600300a01079001c3c4005901c0c0b04560344018215400850f4646003076a6a00c00034900d0441c40d0405a2100700007102d0f44100300190040402402048a00380c40c649440c03070201c1d81d5403002e160301401e9141c82d092145c5003401298002400243c8180b400d001c1c8030340c046c81141485084c0c07a1701c661103924200000e0060b0401000f0f8030305070740c18102901e00e80081c41516101030f1032000003d0340e05010b9991041444402001c2c2003417a100c040d1038880d02d80c07a06040640382502540d211a004e900421050031a5560342014140c0c00b55008050742c48081c2440d10440c01001c00d0b1101281c1041e00181c110403030724004081e88061071081d003219008a6015440d864203010320312000390044400c240704030015455031f400c0d50744219110b0700e01d42802d58401040ca50300c500c10b00512a915400418442596494000c058034850503051513802c0380110b96004107603125551005000541e140142070304189580c0c20011214404406441c44100e0b45e24002002 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 173987113 1250 173985863 173985901
    0xe060a0806100801030b010b1c0c0e1003020408060c0f0702030d0e1306051507080d09080a030e010c09030611040b0c07170d080a0b0d0212070906050d05061302030f06 73
    0x40c0b0b041101d1094080d00c100c182c1410b90358452104078550346009442d0f03000790021550003e41c5400c00000003c01012486822818003c5a849502584441080c42aa0708400010b80105070040006000126000483c180c12120200700b40b0342d80c004a2088074014018804002d50600502021a031042c0d40500c44078102c801c00c4501c2886101c0b1803040350100c03503070303031090ba45c10121600078042c5030350b0b080010345042030140b42c00c00e14182c10419034600320b80841408641c1d003c40400e06501c0303581c0c107200304500040203000070170000000305005800f80341503100042125864010400039140e20348141c6004003480195030780c85009140c2e05c1a01d400c550f0244442c00d040c07055655a040b040000c94000c0d041c03880d241c1608584072440c8040242091445064008118606890040c2c451032025541184540058440c060400504401740ca5413980464441e03041800104003082c40440c4d013030b030062507110418264904500c0424188111b2040b802464013a0404220a42000003004014 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 173988363 1250 173987113 173987119
    0xc030706061806060903060509070806090604030f0305130609080f0406120c0e01080703150308040602011505030d120207020d0609050f0606010c0b18070807180e1b060a0e060a0806 79
    0x6100ca2442c006040301c60900c00e400000e0f9002e0010130218095034041508044031000b56820680c03114413181c50301506442c0e003072050780014100014990301580941c542e0965240602c014103141011b207a09000d0307520040e1090365100d02443c108032105048400c00e44100c03981503100ca50b04d0700c0180000401d40400000340381070141c2c410140e13104948005071030005840d50106500e40680480c01464076003a00e0302240f0640e071010000c0303452500503100802c07803503001240c008090000300d41020343c2544a10300aa02100504000d9a0132201c010320075840c2100043e140d0465000003801d2240c0781002400f0145825051014070402240301000310b4a02021903209072203c1d801101e0095132200080c240c03691100200b001c80c444044100040e6200c41e003256091919013a03424185985a4080b0400400c02b0040c0701e201d00706401902041c030590700141010144600500c08400030343d040e082d01c15a000034281000314000c85400c580038901505d0142c45000350200a400307010141d1315544 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 173989613 1250 173988363 173988389
    0xc12050408100905070b07060608031b0c0a051c23070608070507110d050c0310020a0306140a1e15080105090609060d08030702150f0708010b040b0301060e060c03070606 74
    0x36080e00540111802154404d005011161404881c01040c0e044420200e86040e150840003999840401c0504442e40c0095405100c0d810324294142c6011103290601d40207070300e0507004000d0b590b101051400d40e00600a000c00c0b00100e01d1a01d581d8485080302c0c1c60316480c0100b03040da035081000158000c00d6a0b0700c1d0b240d00300e01d034940701c50540b403a019804004014807100107800d211420030b02408051584500100e60440101000180c10954116200d2041927030215040200d59898040c003801841c400c44007030f01d00320300c0e40d01240c0c01810380d005074161100304198242c1c2e24414060f41c0710061503004d03840303119011304500080c8910402e01c921417103070350140040740c00b500c0d103c1001030080704014240303195000d440d80c518009400c02030007002940121107c10681c0c000a01210f48169030072044410240740035a03015098003c181c0007420b0f40b0704144401d0048585a50440f41514024103043d046e036000d8a00180e40e9215095201042c0d0002040d0441049030640200007543c3d41180111 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 173990863 1250 173989613 173989633
    0x10903050703080a0f020f03070807021c0b060405011406030423060901020d0b01030b01050a08100f18050106080402280b07060c080105010e03030d0b0a030c15140304020109150c12050408 82
    0x76615000489107d4841e0800c000110009544600030310210b440a41070584042a510742800650102c80d400e8540c520000c081108600c5c103480740c42c0c050b05030848665006d1028402003009800010002441c0c0b00071140c4030641040c0c1a42048800d01200d8101d4160303103003d5880300d020f500907421410700b083c1460150301e015802805410f4074020180c1d00d050801808410481e1078010180817095035281e07051000c1062000071118402410110614150901214450f801104c03c16400b800c10401d03441c0a1000503556811118408101600c050320942c08100d403030340c211701d03884c0d0000300007080c000b07169410040140c00040f001446500c8003078040c1c1e44d4400544029005c0c81506030305410400501403140342c90340c08100c40c468081c001300c950796100d64072482410265040420140d41c90b034030940c074041c3e018909442e040e001d407058074198202940064211455800f1341703daa0100411000803103072084031105816a08580d48021541140750003034801d0b882806a0420750041800340 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 173992113 1250 173990863 173990867
    0xc0703060b0f030d2607051615020406031508060103110d08090d0b04061401050603180a120c0b150609040b1305070f12150b07021225051c02010e010903050703080a0f 73
    0x3a9110303506e9900d8540ca80081804802006402401c007207480c030f1402030310007050042d03900c0604040c00c0d00f600c001a801035020700c03003021503040e940300ba80d443d40403138010700000350a82c00030900c001040d62801d400c10302500d411003440c020418603e40040c0b0410b00791050000b41d0304003500440c0a050b0801c00d801800c01c0710f0103c19424050b00344c00441c2000800e1a420343c1d4401451965903842c140c4003400c07515900d100000f0109006100000c8001c0810b406001c417802c806504580401100030b00a01150042211400780c60031032403103241c1c2d5100c041e8458403240c0316070140c2c2e0110901004989000c0c540a050013000c444070b94001500c0d01c1802001c51030500c20031421030b044c544100030f003a2501d0382400140c1c2c0701c1c10f41241c0014020211000302d04003000012400c0d40e00c81107020021050141400c20406e859101600c80c1c151803041400c80048180380f0714203540c081c41c0c10000e10400d100141d51103116540010181d11412400106101c240405010040100d945852041e192100c0c2 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 173993363 1250 173992113 173992187
    0x14070503040b0414010b03060f040c0f14090a1d071a09030a170405090a0b0913020d1104020f07030c051e120903010f020315030d02030c0703060b0f030d 67
    0x1c010003840c04075001c40c0205100c051002c80d2581030200100308140e03d907001c42e05000c010358034007070b01c046100180410800c400851002030720740c036407600a005d0314081000b101140c42066035401f40702950041401510741d50010034044112581034542c1b040c130160314a541d64594480c100c0d81039850300b09807075410055021500301c84001401003642c1103290310741c00800c903c21550310390789001c2004001380076104c42658074801da000303840c00034003180c000003444035110006105014503841ea802c1c3c1c40040c0d0780d02044511640c0c100d05040c41d65084940400c0081c854811048500480803950303d0416034001e24a450041c4240300382c400a90001d0b203a00d42070302c080115804030340c10621810401c000b110029010b0100700800204500b00e034420b42a040342c0c025210160040c2095440700c0903820300b00241c422448844c4009c0d0b1800c259000090307224100ca000090001c3d842d000054407941e03413103080300766002009040e90741200402e4000b40128000c5110365040143c030491800c075400d0380c411 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 173994613 1250 173993363 173993371
    0x1080c0301200d0e0319020d0908030307080c0a140d02070512161203180b0105031608070501050a0201090c0803090a0f030206030a0209010c1a01170601050d06020f04081014070503 79
    0x5410604400d21080180000d103000d0740a52005004106c2c11050342644014040450340140c0030795240c6c01c0c1c0c010301619542c0c000452a0780100144840d030f542c070152443d440381090003a162641100b170012100100c418110805002c408122a824105c0c240c2c02801c0041c0700e2000c450000802c1e850204403402242003017840d82e0a00b0011300e0100e98100040848058036140000c0c04000700c102451601c1d00b80c44040e40c0d0b24201074010b00603810b0401204442c218405065151185401880f0342c1d11500c03406120f04105000c07840d40d00c0c0314001d400a010095100c0c3d1036103489501d408901d42e81c3d41003103400b288914881103001402e40c41c5000d07410151384c3c001c1c058078035551341c003400700d00079600c0f803881103040010990b480d2000c1051029036002c9000d100c54503000c070f5450000703006118180a1044202038200c44010445580c030013001e50322003503100d2000768959140203446d1146000c2c5910541d04c9005429444810b9585a400002c055000d62a0006c8030b455055085544e40800c503 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 173995863 1250 173994613 173994671
    0x80d090f0b070203031b0303040c050603060a0303031a060d0c14120105060a0c1a0603061005010801030f0807080408011e0b010f03050c19080609010905090a06020a090e01080c0301 79
    0x840d040c000040700c0c0340240046400039080fa880c0100d210203401c58801c0140e56199581c2001c014401001000c180319402440201c2c0ca5a0031410440e0004078015090311004003807558521f0440b066501d10f2101e1058050000c10700f0741c0343c95a90000b8400780074009480300000c0c20315003180142115076030035a00002d8030903003001d045170b080105100c0c942e1301802c2c844040c002d000c401c0c0c1000134969003107800c0340003500c40c0c3c0074140d08244040c949095006066061036900d11101404540d82c0500304030b04680d00100030400412450511468500c61404007a207030f003500080108210700150001009250800c0c030b010700071404847c80100b110801d280032030000e0414480aa10f5034402d800c119002500c0401c806d00c5d0010302103480300104851207054000c00ca00604101d15454541c0c034150041c52100402d00c154074040e154941c0f90750b012030000300219030103c0c241c6a020b02c54600c4a000c0c05003903040c070f41d155854501c03640d13035400ea0340c0a00384250b09240304e103140030001d03850f2540030401030 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 173997113 1250 173995863 173995889
    0x603060c040b0f040f09020d050714120c1b0d080105180f0a0f0c170a020c070b211e0703150b0c120a0c17030903090f1f0504080d09 58
    0x40868002150f0003640482d00801c4203000101d280c0300184c000c54010080500700607900c400001c944001d442c0001d0480b01440302c81d11401c10304030003090032580341c3c04419000c4880e56440a03d41c2d02c083c010500003800f4482e9600c1e80521a42d00054610b07494000d5880c2c51510fa07076500108845d40304030540c4510320b0112030020416819258142581061264030089000f5041e0501038089584003009980000c444980100005120190b03594001210000540c0b400100311112039851a0902c54048c08020000d010900400140c19280e140c00311200408014103100904094140c4c40b0340d5200380b04034242004c54040c901920428541040001c0081c42e003500d8a201041aa0400005209180102240b18642403401001019242d0f001e440b1050b00c900c40303080100d141522040a610441002c006000d080c1000109899900104442080d1034010305d1000c9036150105c1d03086c655495000155000d441500715000d4170640755404201c0740c1c00080a141142e00549038400c00c09000e601c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 173998363 1250 173997113 173997119
    0x408010b12060c0403060c0507050a050106050a060903020d1e14060604180308010e090a0b010b0714070e0406050a02070605070c050d140306061e0403080a03050601050403020f1e030a0503120603060c04 88
    0x6c0c40c1c1003a402c100c1c507400e000d401c080846e1982400c100b0341c00001c0b07a860355904001d0000c0d10f4042c40c5075024000601e05482246e00b568089280700b2029603010b80050413002c0004107004031640d000a90036489210102c580f001c1700282540d584c0e0070745c1d03050f00c01c604090f1908840c0c28504040b00b580c641507074800b10103918041083c078604102400881c0f66000d041e1004011504040109000741500c0c0c9455980c1d0303c40b0305145e05584161003403680260096503040052002100c08507420039000400012182c440010400084c0f007410030041440d401c100801500b0307900f0a4500b03a4460003101a108042900b403000c403180000a000b002c2600305c00d00104c0c0260034400003800950703100e20b640c4280c14110074072988003500300c0e506c110355103507000900050b05a0301d409110307040442030130041d08290440e030009481100007064180581d001c616151545c101c8000f0b03405207918083c0540e00700c00c1503410b041c2d0b201c1c0e1002c0812103158417840f01080042c02c00050140c0310702d400c0d003855424603003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 173999613 1250 173998363 173998373
    0xb030c0a080601030b12060105180702070603050c12011202130c091701020c070f151b060209030a1b03050c09040b2208040b030405010509070302101202040b0408010b12060c0403 78
    0x1d0040d01050400d580d9004589841c1c4860b13100d1720001101c000288200d62428040002503c00480031004240052060000c0b0a4001646900307480320b505001c5400d40e00c000b00450103010302001074a000c44210000110301d6443c1c00f0564115009032180b440224801801e081a02c0d144805080000c410040c00c0010003034410060300b503421000c2c005482e103250720440e20f01c0c042c0345801502d031342854948200306031070f04c441d920746524841d410009004003d407150661803907818040504030580004110141d80e078107200310317903d8592200c0b11340143c40800808100000c0300f400111031912a040351080307d840d018803114402c80d0300c0101400b0903501c03290580195446020b0101041003528101d0700001d00002c080c1c00600b071620021500c070b2619040080c25148081c2246e007282c0c005281c00e00c05610b4001c264038185055040034030750301d0311076003540b002807140b58800d00762a4004038000c206050103411814040c1012980080a102003907042034480e54181c8940d11403030010003003000016 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 174000863 1250 173999613 173999627
    0x1801090e060607081b0105012c190f0c020d020d021c18031401050a1812050c1905010606020c060a050d05070e21010c020a0b01141f03090501060b030c0a 67
    0x80c4107002c07860819154081c81c17502141d8103080312400c0d9445100601000d0b100f8002640c0e0000350101000030070325400c81e1000140400350010900e15080c0da03100040c07443c81e402c040342c2d044000c00200251a4403100094841203402d10345001400b50301e1402111520000e10440300f051440d1940140b2065001d080d6070310304c1c0340c0d9600454400350501c004003054440d00000041c4110718004141880c00c5c11500c0211001050409010f0035200400c4012540b40c4800c01c181c2800d41c10181e0790f88100e4000300c1d01d011004c02d0700e030500d0f000d26050801004419044041100c1c1c1c59001c036082c100001e0300f0094503014a00c41e580026200b07001550300300d01d041d0006608020203040c440082d04083c00070503c40031440c000104d01210624084034000307000d104252601c1c08a04c0906810000c1e6910090924010312600d000c1403440e420300d5190b0b1703031000c100c502001c50721a01d030048508100d0025024120980c8d05880315481c10200080001c454801c50b407240d044840700c43d29203034030131600369011 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 174002113 1250 174000863 174000877
    0x70503180a0b040b090f0d050309041e0c35040305090f06070605062e050304020a08060103050d0201051501050904050a0b06162117130209010b1801090e0606 69
    0x11400c1844001a00c001c02c00c010000b404008242c0d9a5590148051282c02c20341550300320f010b603a001d980040030907030100989491040031603001c00c610703081c20011955000c454801000251501082401d040d810010304070106410140791031043e4107500440e1100c501c095210349031500180001070019104000811031640c0042800251170210700200c0d0003034011000880e461543c800038416280782c0f5020b01d50400340c580b081e900303130300b0004007104620800351403010092000202c0071030115a500707811100034001c14000c88080d9a90b80c2807090f5034011054075078015510b0000030420452441c09850185201038480d00d15124440c0701384002000700070001c1820555030300b0b01c40e9035036a0700c0c0010a06a00280700c215858541c42c2009981603410002c80d0b01400002c3c0c000a0007241c0100c01949450401030020070b159440c000070314003800e5807100081d07010700301100200d492580c0d90b0107040000c0300090783c500d81c0c030303650001520052001c0c011b217007095001c4800580d551516500803d40313 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 174003363 1250 174002113 174002119
    0x902100c03030e03040e010602100b030c04090206041203080708070207030b01030f03110a0606080c180c0a11030703030203012607140a180501060e0d0f0303020711090901090c0602010207050318 85
    0x8900c4103c04103034156045038200200b0082d04400421065a041005407034000121078108002d810400005c0c6c1e81700c40300b000c003500840d145c44108081d5510132080d10014100d01090036008103003450010720a090480314500407030000030110b007610748006203010980740e0040142c40d441c0d08607154503441100b005d0007101004084032848036000410310003150558802d000204086081000311070a0040e400e00040c020030030400b041109510584840b40c1000404610559a1400c1a42180c0305007035404254501e200c0024141c08055141e40110f0480324015a0300406061180002d00c800301481021815980109000e1250083c2c03406025a0785500401c3c03007908907a6600608040030480300c242d0082e030782d076030f004010b2540c004224103540303401200d9402600400d696824103107140f242002c0d0130075601050400410800403141409448014160740d12403078210f0310140030348141d10702280c0301000b2500c0012507a00500a0f5070f0101d6104000d1400c1062501c1d040d11b001c07044411841e4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 174004613 1250 174003363 174003371
    0xa0807180f022206020120070f02061e04030204060b03040807060e011e060314010204030c060c0807060e011b0206090307062a0f0905030d090e04030905030f0109050606040902100c0303 81
    0xb504112041101003c0301500c28600d543c689452006400c60790401000811400c46001e501c989000c40f504480c040340c0e0050002d0403e6129001044040c0602e0360300b40c0b40701c181002242182d04c519006002202d200311002c1c4006601c1301c8001906010903034006010002c18410500001c3c500d4100010b4180001d00000d085000047d607510229919200d11000540c0d0b403100f8424440b03c80481002d4508800081d40303000c2c550780d100d041d842a613200314810480144900070400040302c2c1110701c1c2c0c1d9000701c418171800101c800891b0080c5a00401007160f00c0c02400c41c40c240074004142c85200e80d11110103581080400e48415010300040d604e200007030545841d50020048800021001d40d6540366524050104110f201400b161a41d0300124402e074000c0c0407444219034000b02200a80c1d4500300803024944552809644180031600440d5060081c2604108122415840454028026812034000d03482c1c0c601404200d0310740039400703500610104141204c40e0301410520300d0180c4640341c002 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 174005863 1250 174004613 174004627
    0x604020304050c1f02010e0a020f01080705040e2e0620010908030705091503091011091f141920070e0709050103020c07140415080c0a0807180f02 64
    0x6000100c5502c2026468a12484060308217a09204600e400e28001d0010951000b0503000102000c080d4500581007219034000124594401c0c0281d40003014010140c6041c4c1c03d12900c82802c100d80042d208001c800a150078034030714011880301008480060325204001e160f0780000004464591102281d150340b20400c410000b490100154815a00c9a8503e502d8443e02c0c010065074005a080302d9404580038024030600c2003002c20651003440c0941c01c000b550858250104011340540c820380e41d401404895200b002404450900c041d0703240a642d003c4a10100c60280e0b070280c02581c1003a1030b0810118034034541c0900400307682036191034811111010b05d41e045010341c601159500a000c100007071406010155412560405c050107003400d00f58100348801c00c0d41e83c0da481c0c0c948560b048510440803c5030040e255988045000c0e054001607a4141c3c3e142c2c00344642c0e60b0150301240340104d48601e80051504004503581c000d8480350303a205885240220b011034041c18a05c0c45070b455840d405c10a40e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 174007113 1250 174005863 174005869
    0x40204050d0c050901060503070806040b0d0210030c0807020109082d070f031403040f030309030e040608060603061f03030e060415170a06060c0813081e0c030c01080604020304050c 79
    0x1d821480c4100c01003a42d26040605100345083c3c1070380000e0a2081c1170041c00b07585078100421070b50050040e20700090030708000d00007980000c1046d2020703401c02c01014a04001c1c0358550400040041c01f41c503040c10b01c0e1100389089088410150016000305011300806e071042041d11040c40506003490021084507070016170b00c0070759520000044540c089481d105d5820181c011802c2c0c0800c02444c0d46c3c071411442c0646424a0721400048020101a074808403042010f020741d40c81810400090810400c0945412900d80d6568042c0c2d6403500c6403158100190044e154540d540541d40401c0154103c550b285640a07168040700824403a448402400041180000300550342c08d2211540c0d01c0500000d9000001441c010010b01f02c6103445081c01824011690000345800e14981e00c64080343d521542000d00103c0b041c960b802c0341d00180a01915840c04a0402c0300018904407001c017034074800b481c0e02c4200340d80d4801d180840b90100380300c100040c06c0c6e89455806141d0060094041c2e4075403041035000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 174008363 1250 174007113 174007129
    0x5030d050403060c021204091e021c15150f020a020301090606032901050d0f0203010f15061d01030c1e020601091125050f0a030f0305090c090a020904020405 69
    0x5a03000c541002448010700984003034030341c28000341804028501c04003c0d00c0c41903001d400c03041c0f5203800709000ca000a002e0300703044540c440f103002c5440340700c40910319509050f000b103002d02d42400c202d16011582e05004029080761952040014403c242c43c006403540e502c0040c802d011350040c0030f01c0c0d42c0507031400c1c02140b0403240310381d13130000d082400e500d0001000c0e0b03040720000102c1c16088041c0d030814881060360505648084400c2403081480b40f51051001509103002901542840c01c442c0b6000d2554100380f0000503030195648030162180b1040342e500000f001c01d62801665140c01c84440e5000c1da0201c2c60314211498191124081111075500040442d0038101c0103a0145004101364551442441b402440c0f108449207030503a07801c21201d54018001041d00641c0d40e8001c100100030041003102400e2540c1e809580040d0040d04018017080d1a010204001c40e04102c0055140c06010400002001d00244200680c4e242c3c08000310013500070145898001ea800c0101282e80ea6490032 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 174009613 1250 174008363 174008383
    0x90f0303160324030f0b09010e251205070e18070911070b0709140103060b09100903120309020f1c0b06030708010f02032a07030e03070f08010c110d0203070803040c0503 74
    0x540191417010b945031514074040300a1a04d0040d9140c03209000c8000f0b804240c0c484403007101550b0f401e50445842e4a0341240b011030344050024594904942c0401c8404685c0c4c0381190fa9420098866503640705040d1050070b1007281224079604150f00500290160b940b0042d40190303155400c0741060059602c00c1c1c15101e00b99070540c0070070000202081100700c0021540a100d0003841d00740700203842c02c603c128442c020014032610440700c1c45c02c03c004181c802c13002e0000941d009284003054214001c0f001d0028540510180d00074001c848005145051101500301c24200c0001405059083e80d142c800001078003602031507060003400030000c0c146009018072440d4400c0703e07100603500d00708441680f03030084403100354407074122881d440c14990400f600140d645060701414284d8042510800090401103141c1290b031810064200200e04481305502a041000c42510380d9034001000001040c0c0d0b810046202900580c810810000003490010165410600c00d030034005195480b800043c1c00c1c8654a2 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 174010863 1250 174009613 174009623
    0x20a03090c0f05060421241107080306010c141605011101090305040506030a11040e010603050f0417070813030506060108010b0f09060a0521090f030316032403 70
    0x30301480309000c4500d050300000c010300600d404965107004080341503402180300d4198040004242126525400c000348250598840a0040c0d04007004035420b08041028251048040c98100404a021881c004450100b5040304e6813504603030f0f58400440e1034405411003150303e103041ea94424240c040030891015407464502200401f541040001007040303402a60012040c0e042540f40c5000c09e41040440c2c0030382c3c07019260160351f95070b4901d0f144044d004071003880c0942d40000500044490a00081d24160f41c131555040c0b00d0703510f50b0f9039600030a20f025503014119902000102420018900080218a108400050500f02c0e154604ca007603084a42c003d803142d400640400c04030b5030b4000902da000d02101c4e80345a04120410b880c0712091b006800c8030302d00484001980c030441e01d00601c1071310860031800008607002d044c5d000daa464010783c242e4000c4441d06c00d5030200b03645800040b003600e114446003d012034861030f682c4022405041a0440319402ca1264400e4154000d20940c820016500071 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 174012113 1250 174010863 174010871
    0x90a0b130c02010b09131b03050604050304090e0c0a05041805120705010b061908063d0306050102120f0f0318060a05010305060a0f1b030605030f03091c030c0204020a03 74
    0x2451010f4252461080d02e144150100020070034840c04035020241d419401c880341600700308240622040c071242d560005800da2281d01c08100c10807200000400603501e040500b4806105000d40d0b2a0340c4411603680564844c4201e141032029091039484be03007003203014040c1001d2a500c0c0d900d4035402c01500f0704010307408c46000241281402400d001d5100d0850b000d9411902c1c15507403070005090380302441070050411100d180130070f0541d69981000c82d200384d0000d4030081008034042a110b03c01e0a4500004200748021404c80d495034024131079013048a006802900155400d00c1c41c40c54558003201424020308828031240c0c1e490f16040028511544003400c507065602103211802d440d01ca8010003082000c1e0400b0018000960046000c5070090031409011030341615158080020704400504501403202c05029086101d6161300040b0444009030181c0b41818003000303081d9180c3c403c0d840c14941010003c0001c42d0f800c604501030070101406403a00c140c0c8503665a0002d0141e9101915800000c0d0702c0b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 174013363 1250 174012113 174012131
    0x71b210c0e01030b04030e0619030504031101020a05122703071403070f060e0a17070b100506091201020d090b190e060c070501060e0108070806150102030702090a0b13 73
    0x4101880001d485080d0071039000e0b602d9036494014406000304020104803401c04841e00c0350300e4400c01c1d076202d02c4413600300308140d90504000800400e000c0710103a000600d05884130036410300602c2204d0201046550b580e1401c4950600c00149000c054185484402d441030030204012000c00b01c0000924010b0207503590b60360034202034007544840804015150400c007c040c0000d02005244030a075540031030701103960440b07446102d06001030303501c014142e1035070aa81c0c1c480902c13a0000401c030b9184562441d00150712000c00701d03c10300849000d1581c110740e08002140355460a00041d64085601c18009031034145440403030720948500d00821503001c82290240200031000301c1e04480001080041000400c0c000c4c940751780d0383c40b00640040180c81d000140c5609202c0d0a41000e009459024158445541c1d9009101d540790704030300c0785154034001c407000302d20300040e2101280c6400b00160300850034a402c0780c00f00805210003030700304010241c3d5807010f60702d0347d00ca07031500795000100384400282c2508 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 174014613 1250 174013363 174013373
    0xc03030603070f0b04090b060909040804061205100e04080408150a06080105070e01030203090a0203122d040b0f040e07030b040e07060903060c030b0d050601031e0305071b21 76
    0x42c1c19007242c10350010300c40060180920324800e4400710b8402d10340125000102e0301c0401c44901c2791a07002ca82140f00c0d6010071007440b02400c002c0c006c884141d66107055210b9250710750011144150341d022070b003007a10003040000001c1c0c200c145410a004620161401c1c0c3d460740710618024090030000b80ca960007104204030748005108178401021904002c1c40f1503d400500100481107211203a411301d03501102290000c00c040015007100c4bd4081c04603244062440b0017401c041d0407008041128484601c2542c0340c0071100c8000d04074500d66050f003941041e050419107034240d04810074068035800188000600c204c41c44103811300070901a140080c45407840b0b010700007030700c14513076008101d0380c41326100b005a580d01400c46d10071aa0400c000064140ca00c1d1b0702200546030500031194000709000025050100c0464036078100d07407140488101d4110412444104562404030240208006025400100d200d5603105040d0310148840c41c1b03034060316011031640032011701e11010f0400e42442c40b0902000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 174015863 1250 174014613 174014623
    0x10507080708070818100f02031008010e030301091a090c03071413050d0f060617060609060d060209030703080f0a03050a02090a1503020405130207060c1e1b05030c03030603 76
    0x2441d00d280ca8507503031030f0072840078100030800740008140e410208440e44260f171003031090304a002a1124244500c000c0964114007035001926811002580d0960008401005100300448818900301641c01d6030b180000c4007009207140d00d05644818150110a00182d43c0d507180c09128100e04004c070f54882c14580001810342c01c0350340100110076410001c0841c0030b510768407032804840c000ca0761481406698a42400c09612400000306014148440072465103122644000309650710403c0f5005603031081c0400003004000d0360b150307802a00c0894905c01289080e0010074614030094101c4003050766039500d00032513601600854040c414081058401c0350307030501400d030304807020400640c200081d200025003030a4552207100110700507144404d20250103034056400901004040c040b62031000c24100b00a94007411044904038078142212900b1805024001c0300e1622120007035009101c0c00800baa030440d4100031103614181c5040112000600400042000c10700c500080c58880c02d00005051400c = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 174017113 1250 174015863 174015871
    0x3030509010504020a050607060204170c180c040909050a0b090309010e0301060311042d0605043b03070503070c05033901030912021c0306050303030606030405160801050708 76
    0x307641030100b40000760751100d0301c2c0410303a80210749071a900c103024138000c0024410f580c41058400c5860119a840c4540400c030407a01800c16240c50500c44c000c40901c400d1040101c0d070700004130300c060005100c035412540c42100f03114401c0c003c5800030b20a5450b0344500b41d07801c0740c3c10b428950000603132106950b030286030086d07950014ac0082c440503055680e4036880040b560721b154002c5603641c0d000c00f019803164119000e151641d112840e01e031001580c1100150006000ea24080c07401d0048800041e01c1c00c410040300c4c1081c41c2c2243c4030041048039081550840501c405100d41300610210000c91403e0000306652442414070b8660349190200b4982003440003010840b040e40300c12078040c000e00000c0c904440900c0c29800c0504d81d00000030040c2c00030305844370301400c6130309030f180e03008121500040c504c0c3c010b101110a0744c0d44030420140c101c003a1402c601510340c041d0014408280282002c4001e50740281c881c1082d40d0580307452104401074031026511480303041c0c2d140c60900078407941140c000c030b0b04 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 174018363 1250 174017113 174017131
    0xe01090c050409080304020d060902120304061403010b030402010c17180a080705060a030203131203051504150b0d0906050c270f09094305030a021302070b010f03030305 74
    0x60f200481c1ca03420040e010003807006c5e00824000d5034203010402c85910030445141c2c0280007018020101251903a40c1c1c10500501c004148540301d41610280c2e441c041d28100c940303d443c2c0901e180d81d680e00440700b84504a0044588401ca117480084600c080030103000c4000c1e001c0841064040120204034101e0003950250134903800440080c001034403400d00f22444208181005a501d1310b403c001423441040c441c01c080c11010203181c1c603003d015410b03008140200e006505c42418040404104401c8503c00909000f0111221108100166000700035184150107158005a442d25545031401560ba0845e1034040010001039020b08071800500036861960386400d0281c40c540748440842c4103d903540e11024442c004180000d0001d080410584986440700701d59080002080b1102d41a050400c0c807080c041320404d00081c03036402542c42040011114010010301a0852940a0001482036101720207100764080041c1070101d480c00312054000c00f0099160b100d410b1840c14002d086810107007034004 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 174019613 1250 174018363 174018371
    0x1407020318040c021203040c080604080c10050c031f0e07020a0209010e01060e0d110301111308030c1e16060c0b0a05160509012c01090803040e0c070606090e01090c0504 74
    0x9603444d030004448007417019002d001c1ea500c1c0c8650408403c0e003031203079124000520503d0104000c022001340940541c1904c6402c542c004d602403843e10090700c008440a004005050000401c042d10048501d00c00c4800d440400010940b20b52005064140450b140005070380210008021800c01c4280e0350300500c00c00582110550410700001d03e603404880e00140f2400703940071070340c041c85442c1900700b5000d00000c000b00100311610ba4036021940010840c2c9881001c0b802c80010303846004001c079a144104c01010300f110a20f0350f0854600d00e51890071005441c81204072003032030030076507148000150205840740ea846220a00d400042d844009120340855800d01040c04606e64050140b9080d208036410405c2e2114003400040712a20301c40c40238001251101d40d44100011021600e0f03d42e0704d03100fa0f0781d00800a031580c2c04e8560303038403440c813402104d8a4564001161049184040d00d05036100790070125040d40d07034411b0002034400c20440c5d0f241c6170350350302c1b480401c000020640500600c802c0da4144 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 174020863 1250 174019613 174019631
    0x20f07050618130603050c030106141009050a06020709051602030915160b04050616050d050c09040207060e0c030c01050a12090503040303020607020613021e0103140702031804 77
    0x1584524a511400303015a07400304044070746440082ca00180c41401410b9400d18207890a894005441144004e0342e650280f51203c1c0f0700b6040c18040c086c1500c00c0640e04188000c0f02806000402844945000c104490280c0108803660340c0c0041d10014101c95000301019410700e030703c2004461025000b42c1060807101903100300e00d5000300a84503a0b400032140782017042c40c00c25070702e0414482c1008950b645400840235004200c0741c0900d480c080e90155040b20281d07900d22103690413a030601c043d100080f40382400ba10900c0410f9410295100741a100301e181040080400300b4166006181d04480854807007440d00d03680802008504100e48003200148180031155001910601c10143d6040401000e034152054202e9141c1126007143e038458112a40c50f0750348d003002500e030001500d0360001030181d000400c4500d5568880c85106a40040040131045000201c00c2e5511100f60002c0b81410384840880c184403040944191148100c0d0f0065550341408210780180455182442e40c40f03245004010 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 174022113 1250 174020863 174020893
    0x10302090613060e130b100509190902030109080909090c091803040b04090c0906050903060c1b060109060630090816030507060b030c0d030315051503070f02 69
    0x2180c1c00500940302c1400440c00320b0000702c05845a9004000c0c9194003206102e95141c112190100280c040d9079400181d031520420750380b09200c0d41c404d80f0340c003480d100c011590034030200106000550101d040011040f003d40c2c0400d080d11400b00040e04c0d0003502180d84c1d141400c0ca032100b65802000300c00904807114851340018061007000c0d000c681c5801034012a8030390058200110b402401d418103603030303449a41d582c4a4402508004640100080380800c00050150041c026035004031401000b5240030f980d04505080c542d00f103852140c3c5a6000103014140c1071200b40095400307012011408107240d030811201a005034142489040e0400390020552200000030b0414503211a82c41000301301e4003042d04181d1031600410f28020500c0301d00c401200100758004008042e0702e8855001445031400400406031224203d40505420007884203045000903c0713540001031101d00300c00702c0d00e070751602e42d40490343c1c00e940304880c90030310340300001032060058006e6504405010b0510082201c0e0780c0801607 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 174023363 1250 174022113 174022129
    0x1706040b030d110f15010f060f1b0312021209060c0c1c14030703020a090609180504080c030a09050439020312091e06070e01051c02030916060305010302 67
    0x140003000209000f800041c0404e0244d103d40c1451881201d250070080490440c14860070f2107170440005410000044450103a030b5510640501d030344543c00c0c2c1e0503040c1d05c0c41d00710002c0140d0440400c1b0281c40f4500d140103642c03000e0040843e01e110128002d11304811021302d4048040c040d807010b02014070802551480c00075400d8030941e04000045a1004105015035140f191003504070132685001c010406602d52503406040192011780d40d00c0310403a5a02c1d000e8416003d10302172503a024400e10584c110450080d004030340c10501c9055036602e424024402541550003400080340000c0b1614001c20041c6410b000d06034005951462940d920038464071030350460058803480307400402001c492804a42e00074819220f401c2c0d01c50302120716a141429882c0e032612121001d07060f039800c0e203020008050000080d0030384101015116210b821100328015a902d800c209581c2241d120206100814100140060750040410700010403402614100365908241c2ca82c0011042510340401000941d4a52803 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 174024613 1250 174023363 174023383
    0xf07050f0409060f090b070e0105070317090c0312041806150f03150905010321050306060f07020301090602071a040803040b0603030909070206010503160b371706040b03 74
    0x500007520300c00ca16203900a8084d11100c0703c2c51a207460310f068284515424014030403003095480d509495844401136519000381d80024001407410300c1c20340c010300200900c507500524400c044032114456800040c5ca01450003108149450010400300440000c0b0400c84a50b208035003001d02030f0b5420312510020700c0e0000d00d05041044500140c0ba800306000c0e03407219034000406031000340f009490700c8000300640420300c000c4600783c0854111505580e138042d080c0801110130f60360700f45181c81e02410864030342c014880407041c01d07508129420059600f40f140038545031080c0009601d0303450310b040107078242148060110304815600c04000005040d1021a5407150788141d07a1459622354101091540c054011110b03000310403003080c01801034001840782c2c1284d60842c11140212081e40c200b90881955100d4544560b800703200f038044840000114242c42180310a0790860760000768030141810b80c0343c0300c0032004246805103450f500080c801200e503200d1380c103683c03d11500d441e210110740e4500f0000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 174025863 1250 174024613 174024619
    0x207080d21050903130905101a13090501150212070204050c0d0504050f06061219020303070804090204031709060d0e120a021501050d08030406020a030609021801020f07050f 76
    0x200e00e1a07040d460000c0300c81e140020302181000300786010b52206550340d0201500b80b500c003818010002c3e008400b40240e034810a03039292050000c0e4948000b15080001541c8481d00c002410701c03407041e03020101400c2c003000300b40c07580e404146035140c6030188030055580d02001045400100a10082402080c200ca0304240d050b01d00152545d1443c030b0044c503e020304809041c00e24140010f04c014403a00040d005455001c0f6420780e000c0b5201c3c0005c010710049220641c40701900302a04034a20000c1c4d03101d081e0100c074005030540345801031543d108042d585c07042d00b00f0385000394003080900c00e203d107a140680e04c68100343d204038035010f48030000034003600402c22410300a40c1c031a4500ba42800041c8140000b11940d9601140c680c01400342c046d48070002401c801c150b4003100c20000441d49051401000d02d5a0418001840c0d0348481c3c50b00d81c040d42c010504003040c591581000900c0e040c2d00e1000341900d00000110001d6030000400081c1843d000e02044852540801001c0c0a240c0d00d0f140d0841e6004011 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 174027113 1250 174025863 174025877
    0x160c05060c1c090b040e070e0a1d0c0904060e090709140a09050a02060301060201022d040308250f0210020c030309060a030603060f021306020f0c06180306040c080705010207080d 78
    0x10700400c44220509401a1004100c0424006401490401c2c66409003543e0384810080514031400d000c5150860300c6600700c00c0600c8ac02029032a020315040c95001880071034407d10700850349000c04c007611000d030f0001c10540641800c1089a602c14003845001d1b0030400018401401540ba0080c00008040e0103840c00075907403c25002004400c10280721455400303000b440d221340e9038500c041c0c001e40000f90760300d43d00308040f40b035a40618003401403115000c1d4402599230503d130641d21280e1141c0c12442740a0342405400f1003ca14030000301c4944c5c140d2070f00c612041500713900f051040c48003528031411003a00b994014207081318507560100550303074001d0382554003c1d125400e00714110701400c003e61001c0c02c05031074a021030000c01c545800800711100d4402e407003900d6941d00c4c10103d940f48407460048840380c011480c10203903071134080000c085041c001034608450041c41c0700002d041907810703130b0704a0b02036811081c200f0200100380040da000348424000703070650529280610b070301e4480905c0310808010031 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 174028363 1250 174027113 174027163
    0x602150106270603050109060602010209030d050f0c0106081b010c170c1006090507020c0612190b060d050402010e01140706090c120f061503081b070902160c05060c 72
    0x181c0c40502e6446503159940c415030ba031090050001e01c800c1c05100c1701c0d50b0508801040d050f005008071404414050020409080340c400103da03281c01c001124046001c0800c1134408004090281e40c0140c80900e01500252400ea81c4071091101c00305584d03414044001c41041c0455030250f1010159444400d00d641c0d0f8484450b0a90700303103040d007402400341600d05a4041519200d80d400706200310465002c441c01640b09204111003401861010150010b2140c00511401070032583c40b0003c3e5000b0801040064030100015815007003500b01d422815500c60410055691180013013416850a0900988940f90024980400e204075240584110340b191005402c00003030b454200e0060200082400c3c80c1001d52a004448425005d81502e01c00c3c184004844486082c007540790032240e000581a140103039170310252503000c10115000d4590b014401001502031441e000401382c01d810058500d000c454139140041d10b0032200c0e0040c0380076080a10000208100016040350701d0415041c4102030040 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 174029613 1250 174028363 174028397
    0xb0f0108090316050f0706110d0302090402070b13060501140f1c170301060801090b010c030c0302070b13090608030702100513030503130312020624151303020108010602150106 77
    0x20440307070120541403c0004940c00c0c8440491244103070200041561440d41d581c030030450715414010707514480346c0c11201c4080007140c000c0d801024003440240c000760038007206841d47c0c20508000c0300ca2010324607101241104010183c420680035004001c0308152a00c00304c004108094944401c2e140991645001505800502101e80c040680d00281c00701501780c0015050340250420310030280426031070b10010070301e40c132680148078801d40e06030744000c10002c543c2c80440312003103031003019001c0d400f821101052070303c18000100844240420100b034600d181840001c11103400750f00851042d00103001000c01030342d8041e0b8002e03034004140342c101c0c1c81e006001c4504624007400c0e80000e0451000241c1c5241d005040d290507000c0b01c2c024120340104541002c1d0590700e5003001c499031034080e00ca028004035000203904061841c004d02034004000411941c510110981c050100e05001d041814010400c541e4800100c5014240602c083c1c072030300003c02603041c00c0c0a0306000d00170a2050070590003507180307 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 174030863 1250 174029613 174029617
    0x3091206020d060306060303020f0d0c2a06050a020f07081b03030c0304060309020406060f0c150605091918240b030321070c170306060714010506040b040b0f01080903 73
    0x380b404004000090341c80c5801070017054144421800340c050201a4980c00b00d001c00c0b052507000a9403140090300c1126603451b80326020020000d54220703002c05800032141c140da5803860103480145c6516903a4040394602a01d01030000e215040075074800201403040d4040450300340e02a0003040340400110101c0d000007400d42c095084001501d100110300000d1070f55145c0c000c0d0030704a000361420044103803204021122410141d0300540415200d02c24403001415521071900c03482814400050510380355800100c0522090381c49048442a0060601c0306510512a203801c4568024104851080b16035070030491000c03032804a2100ea011558822038499607400c00707030341e81d10018281c80d40c0f841c201803800103ca2440d482c02c05c0c0c28140000250029008550745001d0640080603c0f000b41032254504109910091601750000d505210303810001f403070180c4107541a03002400100b8545842400d2104036008c240515100b02e08141c0c02c2c40003a01c901e646082800002c3c80c0507501e0750b079268440b51440c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 174032113 1250 174030863 174030877
    0x1707050d030201090b36010b030a03050c0706081b070302070909080d0c26060d1704090510060f0305060409081305010201060510050909040f0f060209100c0309120602 73
    0x881a1495a410160b040d071003a04041e11a1741000d02540341d06459804400361219100c072203698074104204648030314440a6009a50500045084c9081c0000321f41091480700086000c01c00c0881d004121500a21000c4044c1c0704914210070380f031600141c8141d01c880e40d20f8446240031400900602450710034003c171409040071540c140102c419034a030407001c1d6400307070070181c4d0305502d418054808036100f900c003001c4460300f04200801c0000400030844016102404403035104810070503800001d0311610311210029410a005600d883c5031500300c40685000504480940c01104d1060024a41140da040740f080c0582ca00001c0558a40010a00034070301da01d4080e12400d40410140020401e90800c801590400c0e402808a241d4070014020180004048240400c0d0140582d42d203d081402c071a0758007d000d104502445819a02c3e0070b8022403403d031003070310b104c1d1b000a41400141021903845050141ca49040001c0c54100d8a00a0404405000b0346c1c03000da03403a040001c00e100d03803a01500d0704 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 174033363 1250 174032113 174032119
    0x1e0606270c0702030c09060105040611010f0c05030412030b061215030f0106050a0e060604050d03090e0703090c0e06010c060b03030d021308060c0f09090c12070c1713170705 76
    0xa418030301d04492507a080188103d00ca40b01e4041050310a090080085009040603110340782454100601a25280150340120f13080390b583d040019a40c2d000c90003082c1c0c0156051311010b43c0c905080c04d150505a0100303800f5010f05080c04410f440c1a11508221011041322080c4001c0310b8548560080403d80e10021060b0b05208071801116451011b60085007141c0c421654404c209a4566541c140c0d240c040310807076407003c000d22003040142044d0410251051003840c0c5000601c3e203540010101540950320f03200060307030f548418401c01400c81e4114010305811804110a4505000001c00040d80302d240140703103d80f40d0921203402d88007001030328100b80d03101d001903460342d0031002a40f03844402c621034070b800751250402244000302c0a604541810080300305692401c80710300244041514082c20052610300c0400c03200c402c140c4610591802200341d0398440b100a0341504200301c0480060340400e0040000300b01c2d0402141c54841c0c03210072250030900c0304070914403400400b82800c08036031040d90 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 174034613 1250 174033363 174033439
    0x411030607020c1f0c1407150e030c01050f030a0f0612050105090d080403090911070c03050a06050106032c0a0209010605030a060f03030e060912010c0509031e0606 72
    0x111040c1c000c6844a000d4606650400040c5880307002d0401d103414984d055404129030540220204141e40c541288203000e400440d5a000e0f91500b08100b80c0c1212196000001c03014080086580b806100c010308400c401d192942c145060021118824403001d80802840d964030000d520202c3c80700c1e001f075001418074034425403030040c4c1410001d010f0903045031940001d0059402d034401d294081e09042d07018070380540e2590038007424080d05500904419103a512040418005c0400041d000034014001d03610445c05811012601d24000040c0c540680112060505140150703ca03640d158441e0610040411000031039801d00c903503458240380001c0c0000c1d401c80e80750b03170010502940046c01180141c0060307504006280da101e14001c000c008030b0000030b00190302c6131488001480c0c400060122401c006081244445440e1401803c50700103002443c04104081103a1303880d07207414000202019140c000507129039080151141d00e40d00000c0c5030501c1410000e0a4103488041071135011022682c80135900 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 174035863 1250 174034613 174034621
    0x130b04090e070e010e070f140310030210030c080c1c0516080c030601021b01182d05151c020a030b1203120106050d0b04090f0201141c0504110306 64
    0x98040d00902600110911803030318005030f00041c6140c0c49040f99800180e043c1c540d103a070041118002c188069179420401c15070107041e40307074441800450003001d21001910003540b5610502c5010b80c81d400700541030500d0031604d034200580107100d440e4001144103001d551000c0d800d2030b501000240003010320725907141004000700303088a005028110348540e11450042c1d95148001c481a20044916900603040200034004024960403007a8050105060155030440d40d18510783c40400c080d071004014a8078189080210042e42c150b000000130480c06c0b091595003040d01103410340c00310340d41400a01e00001008841c40640d0400750b4545100f404040d55919840c110040140088011040c440c0745244c4110180441c004121080b40301030003a1960580c1ca0002c064501da040f91000384041515182004080c0c0d03034920801e407a0502c00c400f80d4070202414000181800d4030204a903490103010404100d204e0403020101d041e034290a0008a119692031805440fa1a00c00c2442505845580180 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 174037113 1250 174035863 174035879
    0xe011101023004080f071103060f010603060602010621030e06041805010501080f0402040c050d0915110f03040f0c0f080102180307120314040e0f0108010b04091205130b04 75
    0x1295100c401c00380705140c01d440c0c0e0300c6080c140b20007501d000b480e00b44100070f403850b8010100d02070302c0a02d00541014580c02c0c0b084020a00381442100d080f48a22090f60041c41301607098400c0c0b41c040c082d00e1008000d81030822180d954103100e108070040c601408810b02008043c401c2180d064001303c00f50055860703c2d580c60780c5186aa050000c81d42c0340b64248400803030294440d0000034071803a0702145041b0203803200e8003484002c155081c125020080100109288c0384213900550154138410400300c0d9140308080f00080c00c6604d400b103005403001003084400760020041c0207032908142c00541001d80c41d41549820001e4866075445112004d61303e00300021003201c194054401c0010b041c562840c40c0c0c9010042641f03640c02801030342800000c8003680c5011030311071011400b040f4082c101052500381c84151800080100315807a50b4800c803004018480400207020b1400150011344007403050440b59500c04200c415004500410400041010440d030040848500020719540307401c2666144c443c200 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 174038363 1250 174037113 174037147
    0x513240303020601060c030504090b0a08010c090e090303090706080a020d060b03190e030d020a11010501170f0601030b16051c02090a140609060c0a050d120507020606030703030e01110102 82
    0x10540150140500000302e05014004100f0031039417540d88c0324074150401c14040020542451402d0308482003030b2001c070300444244214001c0b44000e8a07140c0d07680b4942102c0001c0300100804d9118550421710500002c0b070310009041041d1421820216121b0b981c400c40c141c000d0081d0b0802000d51818007030300050070700e1a50000c500841551804250800c155003a01094414650500301190300c00c00031903800d0340d01070b0b0250140d8482c43c5810884540c204012900f5039030700307070821400ca03841d1291480c645c190801000c2503a241030005000e0780c3d8555102c58000590042c130610444e00c819a003d040c4622440031210300c0c06402c0301d042010280009000025044001d000303000c3e03c8402d90104119110b520f80d8840c11000810007450001c030481402400e4101c030740c15009604c2410201da00050003406903084285080d6500301c40080704213011404d44601400e0705040d50028401e100482e1001f042620a17a038144c00c0090b1240a94401280c00c404e428042070b0780d652000c9849900024a840 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 174039613 1250 174038363 174038369
    0x403081e0406230603100203100e040804240813020d0b090c03010b19140103020f04090219030504030c0201111204090207060b01090608070804110909060402010324051324 75
    0x3183c400c101040c1d950240340241c4106a041d0700c803050740202c05070260000e42e48880400c5130303290101d0f5180c21051030064241c400322002c3c040480c061024040301a40c000320058135002e041da201e02c41000190500c0c4c070180450000c0c640840c90602951204608890056885082e603c207a18021001d1502d0760400200b151081d400c0442c13800c01442c4c01241e020948004100075a029403500c0b1500207100000710141c0d05150b0244161045005100c0181000300034000f0056540e003182d00003410460200d010400900d0302c3d0205001c046036000c41100000d507428200402e4400c080241d2628050790742c01c00f1040c5441c0010042041402c0f50040e0050034130031003083c021000e0020054135044840e000c0d8100040c12400054840c62080b01d0040e003003801040c0c052400300900e0041142088119640200c1c0d82c8480c06101c1156814410301010103080c02400b0740701048203c504280103800d21506220f200b443e20700d0702c0b4006241e03101c401110402070084070480401d480011540203544 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 174040863 1250 174039613 174039641
    0xc030c130e0705210108070608060406030206041701140f0f060d02060a09170a0816030c0804032a060f030b0604090603050a0308090309010c060c020c03010f060f0506040e0403081e0406 81
    0x200c668901d18610180c075410784251b0809080d1a03400c091007180c50310f000800d603584c0075858500010258841200400140c01c81071000800700c042e11302900d0a50360700342c0600140c80c4c014806c11a00e0b00e9640360715034208158001060f06a242c40300060000c40a18a0203540880c1c00290303074650a40105a81085510005036a2000080a5005074640610b107801402c1d11204100c1050107040d05008805403510905202c13901800e16181c044481d045a04115010002540714002c4400d804000041d00003a04101503e090b0503d0350041038680d00000401c1810340303030301608070300e544e46100b40c8020b0201c096040119950b282466907690740340c24000c5d0045504080800d50903400801110850030045e103601c901c080c0b990343e6050040016128540c11030040d001f40b00d141d0703542070091220074054000007084860406c1c034060561503a40d403200d03201e05020081007080030100c00640b5402501800c00450030760310386000340001114025000d5104101c4802c2204114403580429522032500e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 174042113 1250 174040863 174040897
    0xb0a020306150f0405040506030703061a040b1002070504020a05091201140f1b0d0204030605071806050903060126061807090605031c140f210c030c130e0705 69
    0x1a00c5203564a02ca03d40c8450f14403a0100b20a00090409810490308a000501264811552902d40c0000c69005007131020700c1407469000c6091a1038103020308110802c00700c41e03026144c40340c002c010303694522500c101d9000d0794010484650041c0204181e99108802502003034a08a54264150080402c40b803040701c1081e000b40883c100130041d400080c4240020303029525600c41038800e01129030402c8000b420b100780c007044044002043e40c000d1500481705901c076000009480c0c4c40880180e0426000303502080f405000d5154241e1740002c0460440d68071041039034985824103a00380480c0c42c1941c401080303214802c28040110b561880702c145100384001540d00c2c840c0c95801c40410ba03a90383c400e0540c9030b8048a00f496580c20b03812682d0041071214101452480c4410000001541107120180c082400200d0441d0030300000000224103100894000003846c0341c4521700b40b00d140000b410585a0207008901000e005101d10100e4028000003560311000340381c1001c00614a5100c1c2c84d5103e090206 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 174043363 1250 174042113 174042139
    0x5190f0605041d0603011b08061503190f020d42090b0a08060114180702030304080705030d090b01031103010c0e010c0c05090408040807080c01021009030c0b0a020306 73
    0x4604280c030142d0f5a0b10005941104810214a00c040d03009881e42d50315541e43c9000c0c0b09880d6071074000319489440f54541414614040f0100206401028250007034802d00300100004201004000010760502100c00500044034034403281c000d003c0c0c007003070030325a6140a44014204201070b400c2410040c40240b0f03010441007600d0210350b0b411403a100f01c0c600d82c81400c0140240050394000848101000c0c08151829642741034480c17070700f1000e0f8005240c1042e0000d0184040c1070a040184030840904983d584504000c400250b42e40300c01000540380701c6000c02c210040203400d104460b41121103c0f01480080440e041240038420288000c46038403400741d000c852241018040d600e031004184d154128011080300043d2047d010180048884890b80c0d1000700300ba1340c41c038810320b020314002c01006445904100545290010b0394000030580d0780030441c064140e0307900086c40c0002d840c5011001c1910440d900e0191a0364918280040800652200b004a05461940918458a800c480312002094 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 174044613 1250 174043363 174043367
    0x201050105031009050619140a0501090e15011401110607050306040606030905250503010504050f010b0d1101030f0b0d200a1a03060d15060906140102031c0605190f06 73
    0x8650300c000388546c01080001d4081d903425820300c0705036550340402080d29000c07a5000d85985004a9202004598070801406800f8140c400c07a005680745000030070007000154100d007640c0b14148100a0703082e1003621998072503440340a8015040404030100c0300c440c100020050256002203548030f018500d462000105140710303025034200280c100010380061070300c1518010403240b20030203d40240422000c0019581c0302445000d1103180140050104405400b01c000d080da041e02c0040c52049400b64030b03940200703030710040c0041900310034200018600e8105000d0005841c034480030740d511809a610b0318040c03018403a036900d511402c440800503048604070401004134804c0c09520300400c140c48149100c62000c10046401c202e0081c252221990903a0b0f5002000c4440c0701c000420ba13846030810031010140d07000f0000a0002080c2e0300c00202004c000007035481c003c10206010402d034022a40300d90340150350120000d050090003a20390401d00b010346449007501c0707118042400b480f0783c10000e0254 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 174045863 1250 174044613 174044621
    0x30606010915030905031c1508060f0c030a0f06060f1206120201031109090103080d2012040204270b011e03082101120b060103090b01091a090702010501050310 70
    0x556040d202801204240c00b0850003070058050440b003500c010850303180d40c6200340000c198a0b61400340c000c00c001d01101c0d00780c0407100b0103030b001102540c0700e141030103030f50071000208680c0403146100190722075a031103450700050036004411455051500e4004605664010784104800070b56491307260003040070600d07010450300203100702e940d107400d0240c80d00015071103a0800003c007603180f1a01030800e0002000103405078402e9000715541380d0002254450407041b4050081412010601408101c41c2007820146c40c2c802c44458110301068140000d046565503400701010405425001c0280c043c401d00034060181410000d6403445100400016400c80907003034074842c651f483d50074103212859595003554980001048406d410a8203000b1101a00300381c26030b45c001e00300e100d5841c10140090600c600c410317801400c1c4c0c504140c20200c056001c00d5108644504503103000360001068007541070313210030103542c01c9051544042940f045c441240e0f4150001410394104806454404120240b404216 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 174047113 1250 174045863 174045869
    0x5074707080402011d03030d0c111501030309030201031e051f08010902150721030207030909140412050c03070b04020102060f090718060306020a080708010603060b070f050c030a060b0306060109 85
    0x180c04003c5c034400f15960860410010700003804a0303040c41445442d01080d1421036052400055954000c1905024100002c0d0803d01510341c00744155411520024045540d03400040d042c1b43d16412800121300d1804254041071685200412850814402d5049108801d031000740181750100800700b0030b41d1040c4070b02180710741e0040210301e115600c804405029000080300742c9004180c07003080548095001c0e4080607008040d07a0042c0d48510500e400b030f02100c22a00000e00c0070f490003e08110000d822040709401542141c54a91450401c09044034140b0039044424400c1c040450600100008205002c0c0034500c01d800751401c40c0d5a202c0b110310f1400040320040b0895000010030442c040340c6a2848400030070310321000c0b4805803207885020507a4011030001d00050980c0d003c02050642c410692809002c05280a0003101d1400d098000301c3d024140d006044103000c13210401c100b100c1007013072842e18800a01651583c01e003908106004090b0b490030903009020312000529250f02c544001815 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 174048363 1250 174047113 174047117
    0x105100905090c04120510050708090a110a050301060f0806090c0306040f03030b090702030c01140105060d0b0409020909240705121519060207150507470708040201 72
    0x90520302002c02142101c0a00700e000341c05000c100220306501310b4102001801c3c040c2c402003032805454201c00342142d500070092000c00800206011400202041101c0d520742c000c1803c46540c141c140001c0c00c0c50289a000031343c150b2901c40002101002c0365181c5049840580552b80c0382da60304a825526100e60032a150f5054100000041c005400e5107140700e13055000b8070340021526240030204540980588540c4096070000c548000003510900078251945c0180441c5030b481e503d0003000c102c0d640113001050408c562120000c402a40f0f43e98400a980e0b6002007000100341803055030b03a0b4984121400d180d03882d005201c05020301c07002c00c00c0140e0241040d640e9003450034100c4c01c041084c1c84400b501c41014840f0003072030b8030b00ca552480f0303c2c180344400907084a59078600d048070103490304182d58041c1070342d605494040d00c403894214047e81c020030f4100390380007499000030a040440f0303144182292520080c0c0c8004a850410052145071001e1015815054075100d00e101510080360481d00240 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 174049613 1250 174048363 174048377
    0x70e040b04090327050a230109051c11030307110306010f0506070b0702010e1f0e07080604082a030405090c0705070512030702040204120b07090b0d0b0109031401050f010510 76
    0x40c518804034010801440c800801300d4103a160340015402083c143e204004480c1544200060030601c04a0822440300900342140d00e00d181902049010306031104035100e203000b188120040c080c815820309504d43c001010343c2d940f26920b150251071324180d284414007904c1054004140c4061102080c0c090b520024810b83c1017080c01da0b100c403001300e070003040c0d00b0455481d610803032040c982c20840e2524130707600c0c2950b40340105039800d0354100303e402c00b040e108001e510120301003147d1500441c8445d0030a803c5a080e07550303440d15a001c9100c400918000e50003104521610225415000c000380058981c200c862107442c0d1204040880d10f030185110150281d0420402040a440c05a895842c1d020000d825242401440d800250898000f80d00190107407001c041e0030010010150300079a48070343c00b814281c80550500502c03c200340511300d00140342c1d42d541c0c40903078016801254002d008640c050300c0c0700800100024806d0103040240c614805401120f0000716440c0b80035181201840320b50f9544907 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 174050863 1250 174049613 174049637
    0x2071503320709060806060708071e0605060607080d090c05180403080a050411130f1103010e0108010510030605060a0b07110a090c05070803040f0209041211010212010506130e070e040b040903 84
    0x800140e009231030444030048100208400100300c0c4168a9503a400440f800c2400411400d000064400080500748100810000c40300010155000d60b10018410000041d50950b246858000380065410030b560284216107124000c01d82942c4052003540f00e952100f041c0c4e00c0390303012541560010f440c0200410b8840c10404000d003451074115803040b4403000d010906e6242089464100d801c22196160142e00000041c07040005505049005000000003007002e4900324400110501d140d0100828260f1988080707080c6650b400c0001000d00424030a8a0b03851503685414070000c1840130700780e4001d55100ca070004541c400d510602d10711180584500340f03807540c00c2c0e0b980c1c1c0d516070004000321200d0041c25595005030b1104003802d8403c2d840380011400c050800200034000c0303440f40e150154070707a00400015010715081101541159002e54000b500c2c0d04900c040c0c2c0040ca0000d41000c0110001c603401c01100382d03031001441d80782d11801d8404011030a0075805220a8406040700070700420303180a219 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 174052113 1250 174050863 174050869
    0x901030203072106052b0219090f06080105070e03060115020109050109081c0501050607020f01020f0105070e010e0d0503090d020111030301060e010905040c02071503320709060806 79
    0x1140d0085851901060340300c0f440030301d0407940010088000c5425a03840c0d06102034140107980d0209031138944000c941001001e84600007000c4450002400340740c110908038281740200c0944005008800000c0c444c05407201c140300d00828040c400c0c04203640c00c190200346054040d0286020080015010b4a43d07030382415681c00200c3c0d41282c0310380031990b80358507040200f10280715a100b0f1520814805658031904a0703402401c8110f02e46082d01c0038070340300040015941e9041200e04041c0d054550a0401c004540182e040c100c621b9611041035080904020450754015081842c024003601c0d0b002041e0064418080175240d0243d0080c4260300030000241e140c94030800b0540218030500d071204209103502802400c6410a91189003c80d0b00032085000c15a008158080030344802c1d1020820840758240080d80c5840703a04c10b00c0c3c5d4521032411401c0f200f521907040242041c4034070200381503140000034100c0c407600c0c491403142c2040b50740d01c01180307207588203000d4401203401503990f003412a2121010 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 174053363 1250 174052113 174052117
    0x20906040b1e0a0506040b0d0606021209040b13090b180c0a050420040602070f050402091c1b0f03020907080108060708070903060c08070f1119020a0506070b040606060c0809010302 79
    0x9510f910042c2c90200203a142e40c3d80000f04090141703014619240c01300a0b1202c0c00380e80c00c603080380b400e6402c642036803008044107a0035030f0344230711040300c1c0032801c4090340c008100001410f01144c1c480b5030030700360610248150080030340e005006030031401034214154000c460300ea103100003005d81c0c8407000942c108984e183c1500306403000e006010f4000010b007200c0050300a00c0c3d0207944400e0160304000810801241e0600c080c0c40289000e89080d464028003800146c51940c00404000c0b0381c1248001620620401401003111b99481d0203000244a441301014400c40029100c224490304420300050009481200214100e9103481d00404c0d8503121480203a400e803030020310a004000307803000008040740e0035009203954820552900c4070303581007850008110403881d40d901402d0019072141810030383c600041c000305483c0c80c1011030b00503030341a10010b08026038561140794000c501044281c00c0c41004810036003d18407502c8108102c907a15201511fa17004001e0000d00075800030301c1043c0c215402900 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 174054613 1250 174053363 174053419
    0x3060f09020315061308060108060106053109021e180d06020c0105070f02160b18030307020405150a09150e0402060706062606160f111009020906040b 66
    0x80810100038a280201e41e094200030782143c541d05d10580c040109410500c0410f000d420340c0d00c040c008960415201030282d20038440d00a5102d86032403080381d001c59941c82c00090303c40f000c1c0c0ea9420081d9031006050f010307400c208c61414207010b196840c440c8960562044039600c10000482c11009404682044102c202104081c1e84290f001c02c035082e02100700303208040c8a4129910b5980700d424800000a151110750000c00349900c10029050240305200d00c01c1d55018201ca0f00d0443c03518404c940400d055000e41d2000a400a040074184041e1000c0c83c98428035070b48041d0b84100850343e5490031034080d501d00443d0915051690981441108041030003180c0c042e00107040a8602b9685607100c404548080e032000745a07940c00801c11840482c0e02c0f1000c1c0300c40c0a004002c00c010300300300c8400090b103070401007000c050003498019041010300410701d4000382c648070070582c3c56001c5000f03002d01c081c00c50100200e20a9201000154080c6007911800d0b9217403c000d003140d60484031034110401000c0d4041 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 174055863 1250 174054613 174054631
    0x608060a030b0415060605091818030705030301170d0804020f01110a0c15030b0f1002070308040803041a04060203070209040606090903020c03010e010c02100f021606020a0f03060f090203 82
    0x450007002042044484034015072044880842d900c42c410314080441d41c040d0413510411108100c240000d0741e91413865000b5054040b403c1c0000e889003220138880c0d5204605024150001103001ca080c0070000c8065030403103100d400788000b00d00280300403640700d600015a00021405d40350100e009820000d00703810004406050803103c4044e604100c5142c0700315944c1c1101c46104886050000304500f4030b40e6680900c1c20f09091184a4100c40012008800d050280e8041e030341d4181c00b00d8105108010a0009542214041c4d560f6904d44a900b9103070361023030045401d080311554800c02e0b0704400300c045274100c40c5580e01a504100481d82004002e0348060403c1c0d61464941c1400700e02d051040c0302d001c108911940082c00c50381c4a00c41490b007513074050b00d0000484c0c0d141c26103000403d6008104294007500c1020f000803014240c500842c02070003101d410408120107155150204200340c2d008002d0501c050b1585118070b14501000c5040d286c1c0f60003003000e08403050400f00026840f07900610380020040e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 174057113 1250 174055863 174055879
    0x403030f0c140a03090509090c01110c090106110c0102030711090a1b0f0912023706120f1a010e0a08010903170f04030c0b152e0201020301030507060806 67
    0x5448100d42d020a14401480d581c110f102c07180209600503513508001c0509441d0b0300d2582c6024800d840d140e94200042a05201d1220424591a84240900c403082d0038001c0c6138412550b110000104800408034010030030744901c3d03c15035a0743d070000040c1c48441e0ba001d0b001c0c02c2d00c110800107002190002900c860113680d02c40001001c0c402c10a9005880d02c07409a4611700039062040e001000c00000d03900c411000d525540c00480075884142050b03480840080030302041c80d080800d0031004000d001810012404041000729040b54030200d02c00755914070300c3c414403240303500000302c034112208044408030f40c07100e1103105510b5500408000700040c800405800c04241d0310f2000501303481070340d46c0441c00542d0b01032881d500c8000410740c8035089007002046000524041d03070081d048640d400030142555280b64000b64200d000581c0310f4200d25400b608030a1a5010020000b20380b05881d61241c003904506108448203910520a8a040300e4001d00205292480d0802c1a181e160016040e25040700c00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 174058363 1250 174057113 174057137
    0x21c0b1807081b0f0301051005040b04080a020117060108070e01020f06010f0f080f0705040f06080f0a331d03071406060604181e0e030403060c0e0102030403030f 71
    0xc0c664a03144a451151035502903460003552148080f100d12084011400051040f960b06086aa080c1c07815100203546564075045030b100152140c0c020b590000c035181000060210300f4803000b0504251061003a205e4071a4088000041d01184000300c510078002841c036400145040d104202c000e1141106006880d210f028030360b403450819009800c0115801660181000400f007010043d100500948001d0f219446140d045262202400e00c2441e1049469202000c88800c50b40d125900074401e243c1103d03810a00c1c01100c540b901c3c00e8120580c0e4103249880851a00382d007074200c4414210904444503040091421f21000825100d1605d1046080c41208280303140070400c01800e803240113030003808401c490210321920700140113040c18000c80b02070208000004c125410000c035140c40740c0c40403c4a92042541c0d0b05011415085200741c06c1c249208074042087c084014010b50b4050141401a03d0040e04151024000020001e0069204000820110348945408140785000b4a8040c1d00c03002 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 174059613 1250 174058363 174058399
    0x103050c0c0a2004020f03130501060b0715050115020a30110708010c05180d02030d170a060501080402010c0c05090a020a120b0619230703020f01021c0b 67
    0x203501000f240c01044043c0d00340c5440c03070701d642607075802036003140c0551a00c3d001621600490002502201e03068410002440400101707410500c0909030104031103807200700d06d0038003c3c00032400c00070049a141c42c080c008103414410054048107501c2d1500142580704c81682d40c0e408000d041700e54072a180204000880b4000d5124010801218082c0d8844001000d5955580d00f8401a0351003090359a26201c0045c50044d0090281c4000702e180e001d10017031031010400440e948262042d002545030194201c0710850303640140003c520000b4040860606079030320031000c1d04441d0741b030080502041644002030700562180c25914441707403143c04100c241540d11404140210400d44000b0507850b008035840e0701c8950710214101001c4040780c400d0040c8074010340072440e0741c400d1860100100d20b9148020300f040d40559070800c02810300300e0007000b81c1d050890440c10550818031003200140121141c4102100050081d2012461804506c0e210341038a03c041c14003d107040c0d000035400511601100300251 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 174060863 1250 174059613 174059623
    0xa120303020c0d052a120702041506110d080609060d020a03060c0c02100807090e07050c060a09050106060504030c140d02030105070c050f1f0b01030204050307120606060512060103050c0c 82
    0xc0c0e075902e030380341c40e0740100003000c1d45202c481d10410405c03882c1d40911107200c04000b899a041100c104041d81d83c0d08042d0001c90082d1080758a18034200c40d21000000d41664001420401e8806900c15140030f141c802504440c50141910210750144c0e21074042403452408019040d5001e1000f40080b0300c0f80e590380d0b6407205640e120080e02000c6003145003e0015030400140261000c1487e10b010304c16444c2000014001030280d005003007484a01c080022600b40c00b46040312089801c0e44c0842d001450802d66133300c042c107400c5108440301e500f48800060500d0140c0e05803000e42c0e030310081800b08e00742400d40000d251181c129000703601041141220000d03031000c1c03007018003600d2183e403000c43d0111207082c01840e14021800300602c9a02c22120840250040000309980c11800800441c0c03045150004030044c0c00380b600300580c107000d1488005980403500030701d042e071130340f240c03c0030b11600d980d404003a140b81c02420314941d100680700c000170f01a98402d0b40300795032022201c14402d04001c09100058504 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 174062113 1250 174060863 174060883
    0x70507051510031401020319290415080604150209010f0f020106030c0e04050705100507060e070803270406060f030b03010603060609060905010b0903030a0c080d0203070f0f09050a120303020c 84
    0x142d500100340980006129048c840c04013a60391306010750020707040700091140c03803440810200301d05103c2001b0030395990340246000c1520039001191140d1514a00340e16114140d0b0221103102441c284000c40c00700a0085d110201c00c161503000c180c0380924002c0e5800c1e004000d0441c2195607070745005c4001011a40084084d0080980c0c901c110f18251401d10702c2d10b28143c01c407070303c00d0f061405203d9903682d011084400349a0b205102103225141e04110624140842e0810342550001081300c004880d06100182e01008104070224600d0047c002400125680f03405888001070404204910440c026000402036040260000034100e42d0707a03e580c6e00300d4125030060210b46494500070444102e6900a450151051450307580c6003908490000356030344103201030602400700c2c0c403080348140003464040d40d1450404000944d2b8030b04e080c240041c50756a00f00511300c0820421031100725894481c40c0100c054940c082d0041c00b24604040b28240340c4c2e40e070601c0441c00c05408120401344080c050021480c0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 174063363 1250 174062113 174062153
    0xc05030a030c02012a03020c0a050727050103020f04020711040c020705010f0302130905060a0b0d091e020d030e030c03010204080601030203011d0a0204020f2701020607050705151003 80
    0x102c040c581c10003800c1d6480345c001035013102040980004000d6602008846003000740c100161b40741d00d05241c0a04060300b610010300304d400394840001e204a000c2c0b04280450344146001b845ca082140340d8602103600a01010790404110a000350745810f056006154090050f26911003e00344940040c0070384040848d024010380080e8000c100c81d517042030121404c04c94504040d420320a5048140850702c2c420f1044940040d201e802150064840c10094000340504241e40c031782d1007160540f800d02510000d5403c07550342e608801503843c0301f0007039115030a86030f600406074000001151022144100a4058540e240c00f40103808400c2341d5003440100000e101000151104d07616500401d400c4401c071030790040e01418074240e0702141240c040746644046904840050300c0d0b403034104d045c0566003c0c0d900c03100c444c00e00b0300c0c0c4203c0c51503020500d5041c000a09071b08451040ea540081100c260240d1032009062f40e00950307a08400000200c2000e501000f01b0601001c3e4554035101c8000380c10b100c2c544502 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 174064613 1250 174063363 174063371
    0x10312170702070e011712070204140a1b05121801060b0a020718050403090308031f0e090c04180f1505040c060206060a0f1413050a0b0102010e19020904030c05030a03 73
    0x211a0b44c040d10100d00602c42400e05c243c1c075042c1d080c0840d0b2207000e1035107011364110000031003000710f54465101d0004460b10071184c00491a020107080c0c02850000034a00d03002400302d0080a8141c801d00886480418191131442c00b40c445c0050040000150420b21645540b17400c00808c00303c00102c00742c02d40c4903c0c0d60003000c1580c54007070203448024a80344a882c0ca213007041d04010100e600a14207a084035400051280d49a03a43d007101c40d040e02a2003070b0140801d6043c3c000040300d84200c140940140701c504191340e51010198108000ca4040110588a01100340d0300035010848a40d01109058050000d21030038100c090b6140085800807103040752240e0015038140401d0b9030411000b80d1111081d00c91000b414100000f44026244d0303803190510f0348003040c08084641d210405070007543d503d0750b0000c1c041070800040c5800a0460b03541400d00540c41c044003000b0b58500003d86800300c0e81c0aa29040300c0541503000d2102c0000e005009a0900480f140c11400250040000b44401589954009 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 174065863 1250 174064613 174064619
    0x6030207050c0306280e060619050406060c0317010513020a170403030c0f0509010909110c010903120f05060d0f0222060509060303033d080303040614010e01031217070207 75
    0x11070ba685048107174071460b52405a0101156a0028025411610403580307480c10003022107090341429140d800103a0410f0808400003030070350b00100c001c008075200303440d016075017840c061001400100074401d1580c0070628a001d00480c0e4203d60041c140c40b6030900e42404951071505801e140110309807400c80000381d807103036210700c078562005e9580180412450700300c0c5031008110000f42594805c1c0168a945541c600382e03d03038100d112404031860442c448001b0b01c0820540e080103454941e40c400c00030011801c201191a1a200d144503140c4211002000810319850f240c6842181410040342203070018400c400252000700c4088084610400e040c0000c6001c609040070310000705405080b281c040c0e4018030034010305d0812541601135403007008041941e1295007190350820383c420a00c803040480f403100c40c089200c4030003000551146000e50014805592240c0301c820070340e1070900c2201c140c03143c0c0c9001480004c0c540400611502000e20300000c0300c800310000c40070010030a42da1400540c1c0302241c20 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 174067113 1250 174065863 174065911
    0x30c050f030c03100b07030c060b010c12020f0f07030c0b030601090e010e0702010b0f09070e19030305280f03020901090e0f1504180b040204020714160b0307050406030207050c0306 79
    0x1e9405000e80d4180c4609001b084d540141242060f6080201750301e80300c1c00c10003c640d103e980c0312001143c01c02c038201410345419401a48810848010184034080c03202020341c0703903100203140c9040702e602c55185e2200310f00d03002c4504060303000a0101810410990300003c0c55140300b504041c007a0013514100d20303803030624110103400c44070759810143c0281049421000b1039610400c1407540190300b802c058001038904000180c81450885019000e650969404018580e00c00094903602031841c004040080280c00100d041304241070003480050310000034401c41c10301c01c0c0c0152041c40d00604240603001d03214000d414400008442c03003031110384a07404011400001902200c01d0140a071401c22103282942c208002040c80c00802074089210100070404545990b0b04950300740d031b0016440d4180c200032805960f141d01e04105081282030825030301080c0316040c64107c0f40a007266454079840c080c03810000364040d4000900c265035500803403040c0e500a4038107003c194070034a10a021044442161800 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 174068363 1250 174067113 174067141
    0x8010f05010e04020d0201031d010e120403080415021009030c02040506011112070f02030f0106060f02030c031204020d02181b13060513082506170601030c050f030c03 73
    0x952244242808010001e03848141049500306405039410410301c040c034001a00545050102d4500d841802070810b002600194003844030902c00d04103036040d192074a4660200c0d40643d00014168520401c803c05c2403005540c0d010400c1e040c0c0340183c0380c403840c040310a8000c403100e01e11b0a42c00325142c0c904000844c5400c4c070502c0c1c0e0185090a2140441030a401d28a50741d21b02180c481181e5070300041c040046c40301d0030392030b4580310b9401802c0300d002c1c20032002c511b4082c1055118800c00300328040522500d940c0003000b0703541e1103038440c401541040422440e1032050320024005981084400d04080b001d80c0790411030741500743d6800115002c500b00801d0b9581c6900c4080c020b103464000c28010244010922000d0f070044840a11302551110034656440381044034030790203008070344030320117900c0304056582990361003449041d0002d48900e0b5803401c00755000b03080c00380b0030030030842c00341c2c00150b07198000c1d0301c031010050046c9407150a0150b10b0303948050f41c0e032094030300c140528804002c104110940d240 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 174069613 1250 174068363 174068381
    0x90d050d1e0c032012070503280206041b0e07030b0906030106080a060b0619020a020f0603010305150a060807080304050a17031e090402040b0d05010906051012140705040801 76
    0x190021012009440007840020740d03556102c10088101d000885032402004031042e1444035680496886e10645405692036111001505420000e80850101e2640c0740241d1030745519250090900e070342d541d5549050041c003014815400305225580802c40004960000d4402c51080e00c1c0016a01c2511081082012004000d00e00c26030400400348081d00003c180740301e5a9174031034004500908801c00060f194003800242c00a04028441c011740d0b4664006003101100d4005e56000b090317490014107014035071009000c080e001d42c0c0001c0c01c0c00c3d21040d40346611a445644400005012038540c00c001d81441780e2070b40213001a51020501340b2161402003041402040001c486124455402e956140c0380c3c0615820a600203a100341c60305c01d0011b00c0380031501c000c0e0b0f00074821555146c0301c0190100d9a0081020000218940000410340c00f203507200708030035541300901e103c034100b00b00b060450381c40d02140c081c04401903c075180307100c08100b1001c0b614003a161580b0b4260315142812400e41c2107c0c02c02c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 174070863 1250 174069613 174069617
    0x30702100c031a06090d0303050a330e0105060f0a0c060606111912051c0c0914030105060f0f0f0910050112061223060114030c0102010b09060105090d050d1e 69
    0x40441d101c1c2d0f899171403032800c1c647d05043c041010f5a60300c2c4804014008203440c4681c040c080207401e01d5958900100f0101400f080d000c580c50b02d030311034a0704217a110090190a802400806c00c4110820103107028061003641807504288140c81c80d81c40005031111580600041240004144008441072100d130408c0c7d4000303400d42000c0d450071303291418880300744a1401d00744000000c03056115951000c402404448008081c03000b6000014010956095440342c06003440107855500383d1842c060040350b00851000307001e6100340d4000d00810407481039a40c0307a143e004a66030b8107001a5201e000c0c80034820000307ca20117030a2440d2100251280c410035440c030041d40d2600d035052008007400001681065003003150003045000702c0c12042544116100c108801c1c0c400c0c1000080e040c10780300081a01d0b900c0640545000480741c20041e030a0398480c0d400540c0c00030712440059115485580070301406080101007501048450326a075060111049003280000c800140d21240200d4164440320540098 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 174072113 1250 174070863 174070867
    0xf1c0507020301020d36050a02040e1509150903090102210702031204030b10080d051c0e0706020106170303010b0304020411030f04030906140a0c050f01150509010602030406090b030702100c031a06 86
    0x187c3c2e206070312030125090003031155070b0310040d441d84031004010040002c50088001009800c00300b800c650b48003400311880e901c88854034001aa9801c0200c183c0c0c2d404c49060700104013038179000072201201d030101c608100d150300043c801c1c04050f079010800c20320703240f40e2100c140b0380d06c5047d800c08200e280c80060505920700760425040003001c10000315403800101619015498096003a1906003d042c2c2480b405405401c0038000c000a88000c40d428040303130225002040342e01c0c0c1c1c841c0e60001e0100b050414941c5a00240010000070b48100c0065501501c000c000241442002d4194409600181d5440084140304001c100400d900f00f030065000d00702608000c0c3d1b9000781c40181001c18441c0700034080402000308100e0042050801044e0f00008d420402440140c9c06500001484280e40c8101441600c0c40320000859038001b208540a513695595900c1805003058001c0320306a1002e0907101c03c510030810300840d41c070840c0c81035031503100069502056030006025805d102c0d41c10151035620640702 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 174073363 1250 174072113 174072221
    0x1210050303070f061b02010b030c040c0e12030c0f030409060806010b0403030c030306080f0a020103060e0606092202120a0b0301050702030d0f1409030c0f1c0507020301020d 76
    0x20a4502d1140e10006244035110b041c42d00c1000344c4114032071007200710081002c044825406401c60b108211041d011242001d01403010403055543c1162850046004504012400d080440c50040001d90035001c4925205842c9581880c003100700c11844210340002c1400c2c003039640b95020790801052104010705c1c40d5410125405030911840c40000e092103043d80c0c0f0b40080602a410100c000e11005050b076180ba00c09441700c540701c180c0e201040380020f2030102c010602d550301708141da0192501034982420080d640c014425940101101c28084401c1450741c03070301c048280c0c0010006200f10600e11816810030f4103084094404100502d071184e4141030400c03031126400003d40d010301d0b0070320001040680041c4040c1000b001141c8981c040343c145c8070f0420104000000040c035100b0150401c55000300d0350081b000e0748034003009290311010205d1000f10f504551040b0041d001e050300084c0010305e04290600660100ca081c0b40002d55015202d2882c1003000c51208219a10184a00102e070301c0180 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 174074613 1250 174073363 174073369
    0xf0106090602101a04050403080a230106050906120108011a04090f170c01090803040c170d0302030c0c06090c030f0304030c120501060e0a0e0615090708060102010e0111121005 77
    0x515603c4000700242d40300c000005201d4140c02d00d4684a001820401131802c19050061503a002104d2038031009042030350000c0803444800c0004544a285900000243d08004003101d255020b80c40082d409041400703840d070b01240781d4402c1c500810b0f061000180c000318010805806880b1800024415468281c803107022601d00e009803880c0c16400340c02100020401d20712011b2500a240e1320f02d29540c40d03c01c2c09000c01c00d54100944c01180104048180c1a540d01c1e941c0c83d004c0360805060007950000c512054089001c2c0e00656045451241c0700b50900035401c0b4043d1408008a420882ca6801248800d40a040c1403050350089800c1c10060b5291070305588903000006402c0c4644c01c50323040600030700c5061103829480000640450103c8442c00d052031105400980280c0b40303a80c00b17078007508001c42c40102e80102003080a42d005080b2071019030300d0410680c1c1c0700400070040c42c15035403285101600c4160a1003807056810303444c0052038403000c040c4c00c44112550000e1100e5040b44552105100c955 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 174075863 1250 174074613 174074623
    0x20c0d08151e04050402040e0a0b010e1302060a03020a050712021c020c21010b100503010e0708161220070516051c240606020c031b040908070510050f0106090602 71
    0x40342940c0c0440d1941703407480880d000303002c541c0c0700d24018040c3c01c0c0018200045042c1150486150241045035034850003501d070b40381c56030140000e502031010030003d91454000e0700030342050b84050606d00d00f00056510340103540c8480941c14001600400600d40324520540c807074002d00340003440105130041590b0041540c2c50031052029008880b528031200c2c5c001425007001c038103501e025145402e030f000c2c41039000e06585c10030300a404990110100007221144581122441207500e40701100450503200c9040e901000b03001802400c0d6525415109110b480c0e0301291984004010700e00d90303454425040190405040549215151400080400a6550b4404a12040c006411440c0707034240b1a031030246140031501c00c4c2c5244403941c412448040030002d50001c1d00300c940703a8080c0d030101d9030080d08040d00c0740c220088500d01003080b480103460508082d40301070740580c41412818900701c1151945880e06624a03441c0c2c895a454030b08000d50b55402004440c0140810308000400a050201c060344031 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 174077113 1250 174075863 174075919
    0x6080a09120e060d061202131107150e060106120605010e0303030406110c07150305070c031d210c03070f08070e0c04050d031101061403150a020c0d0815 67
    0x1d0b002c01800c0540e9201d0b0120b81a42200607001c01c4002c1d51640349400558502e10f00364840e03c28914210b14400a5000c0c2c130700c03c0c65210109610f000183d9070349000002000440c5c00402daa240f5031410544003c00c801c0b40a007129440c0c1c21021101440e410b0700b80c82c091b4000760304101e02d10440f43c2c50741d02c00000383c5c0d03040780e4400303004210460003c541120a0252010005043c0302d04000012a110346010000d42003000e6a011702007680c038080c0c140c40d01c0092000c001c001841914900c510704d0100c1e0b01042c09444002c2c100701d841c50030245c81c0784115440c90211641a040041071503200d01d001c0101d0f800504070740014084040c40c1c01c403500c1c2c60b40d03042e101d0303600c1c403003007020002c3d11424000080701c0150800030182c0c1d00382e02440c10000d02e24030f10441c032100d1941c6040004508440d0700b0302c000100c504010001c09407640c600c10f442446070809418001c009400b0310070113162140c140300e18910407455079203059a501e400400658000c02d4a0b0f480c1b0701034000ca40386180440e58400c104840 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 174078363 1250 174077113 174077117
    0x15090d080703050c06100305120306010507030e0a0807091410180209190305010f0515280f180c080403050a030506120f010e0c03010b0109210f060606080a0912 70
    0x90300c020b41415240d40c440c4542050b614010304040107008503914549034103881c06602110a050070014070300c000340c48165603150114009208100000340b058101080403000a0300078001e141e0707204401880c0c01c007a130308203081041d00d0321540b2000445860b0102c5c0d010300100341c0320308601c0ca4030500402c0084141946011950001420001a151040030f800c0144485854511940d6203082080c0240030b400d640140c5d150a1030003150f58408291540341400c2c00003852210300e01ca030800810781074003954085c0a00b11505003030000305c159540d2401c400414a030340300c0d4003a0b54070030780c003820850301c40c01d00c10014000c0420508c00441c0d40802a6848440541000141621007034002031084814415041d0944031b080c03080d413880c82c019042251007520740d408448800440c101010700380c501c2c00707541e070340044e00614080044002c4500d01e141e21001c031125076001c0115644501208911914003501c09d1516001c041086a521506460f032100200d40e040000c03200f00d644003c0c0e010510581542 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 174079613 1250 174078363 174078367
    0x503070810080318011707050f0a0306050d0809010f050f1b0109060e0d030606020c031b0d0501090b0105011403090c090702010b040501030f02210303130c0305150615090d08 76
    0x901403001503804809054010b0440391680c21030012003204000018103140019010301c003a00345200e504241c1402a44075803106828103045030709040040d04001d501c041010740324034001545481d0702042c2e0340514003030b1410542d41c190f80c00000d0301e442c03007a80e040320400508202150300003038580c09690110803030f4032041c00c0440500d000d060160856500107003069140c42800310400c1000108807884c080030703850601c5040d680c2d40c401d90300c4d0000c642089416410a498000d6004a20840084010401080150b00c0890b41c0c07525803c40d100c0e00f004448184a0000600c12507801901c003030a0141080311551451420b2855952a4400408024003400c0f181011480c882d000f900000700b10314002d00100080c0d82d4a00300081c0701000c010060303009600c41c400841160031101d00440000100c00000d518548600c5101200c242e1842000c0d603240d402c0d1080480001c0e005d001c00c40000c00400e600c20302c2c9092081c100074144c5010124052200340c20488103542c0c2c0c541c1e00e0301d12440b030740040d0900e03 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 174080863 1250 174079613 174079621
    0x6051f180908031305010f0204051509010311031003050714010507060c0302090d0812060909030301140f04090b0f07020106050102120d0e060115020d090608220b01080124030305030708 81
    0x402400070a1001044410301004000d040400034004001e01c50140000b8802007040600c454204e1040c3d000b11a044206c22003a0507426144a006000100b4103243c0010198001c44164490f60025039002d4050106000c0c10010300c0310400140c030280c05051001682030b40c00e040003034198418200b0003411700340ca4001d03240d103050181d07065031081d1501400d0706020000c28900310b529680005402e1089a5000000c50110706059441622070f41400006502e0750f42414a01040c24900210556000c08041440281d82d00d0b1401a007107400c0c4a00c601000c5801c0c41240b07402e100c00014200001c582c500881007107180e90001d5100e26a2440f040340666500540035464090407160003046c501d40306403000000e40100c01e2105d050100340c3d56098440c0102c1640302200d00c10600c0c41392000040c1c2050106101b404101e03107040f8454200001d07000110026902d103401030704268070280071655180b5000341e6505a5241800d100000031841040072800c5581c05842404090b15520800518000103 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 174082113 1250 174080863 174080909
    0x3031809140115030e030c01061a181207260d110d11030d060806040209010e151002010b03060a0b0a0e041e050f030705010b010e031f23040c0306051f 66
    0x1110501700c00c2802e030303a038482608803840d018104074070804100000054548102170f05910665503841108002902c3d90102802008548491003002d0074441c0652480084e22072031419a484141940950841100d58010b000d00e007003030103012401041c48042848007032008400708804114101c0703404c082c0350310780008002e02d01e180111a079100703169141c080046a24100004e841740308a100701d881178010f03a02c80f0409100c010013900c05406240841d02211031901c1d080703601300401d084a1000080040080340007900c1d1030350a0303071910b28055444690784018207105c0340342c40280102c0c0400b2025800c1c5552814001183c5400b0781d03660081040a000811500780900024006940c0c03c59441d0b08050030050b00810701c0c044214041400703607410b50b126042c042401c2d00400e50780d035500003c0d4610b9040c040f02501c031a01d03031880c1400750400d03441000302c102d43d6520702a034003822a0703100c15800d500e4010f040f503002a0458150f1300102c6d442c480000c401500140982e4460400040d08091036821 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 174083363 1250 174082113 174082121
    0x280c08010212040213090b0f0406060b07030e01081914040b090c0d02040c110a0c05040b010905030d030c030b040204060809011d1c090b1c0b0402030c04060c02060d060303180914011503 81
    0x2e080040c07900c12300c4054101003440038041e42c06041d04100540c0d4400b00030b0003a00c255800207021696a29004441e580200000d41d84008600300448801141c00d158004894001d00c20742c2c00000280103200510904002d41c541c40003a82c030040004a0582001030302d00403510000074466a00c070359010400c60302c9450a007092035a032070200c40220760186401c1c0c02941441c011b1900641c9040d080d40d040c2d41c032403950881111070140181c6402c103115807040780a00800c0703013410141a15440d601e162502c6600c02800281100ea0342c1c1000d03401d04426460a44500c08661050b2540c0183c016282e200c001c034200d035400304050265034041001a41c01e407a0341100e60b11100744501c1c080ba9208000506000c0c4200420b00d18504200b070030741c04810007041780000c2d11500e1725042c041c0405d001c1503010340312070121140020130180c01c180340300d0010300544006402c11400940205d20265000202100c608042c1912400500c00c00e220440807108440051060000789150350010506080c007a0780 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 174084613 1250 174083363 174083381
    0x50909070e070c03030c210506030109020a060504030c09140f0a180b0f06151e07020406030302070302150702090a111308071502060603030708070302280c08010212040213 75
    0x804503505242c40e28014004401103181980400c2c1803855021040307200389030700d00d803154001c00b150442c1e005010000e4018400184865003544d0b13103218010140e0b88200070380d40100307041d0faa8643d0303560039440c0c1841e00104a910090016041442450f82e035007141e08103e9110f011001c40c0080c80c1d8501d40361380d01070034103032484420802498620034240301c2c150300060b1040c0f4002c0304481c0191a8a070501c4180039101c607201d01600340610201481c80e14241e1600c0e00c0640302030426007040c1850b00007504556141d4012000760f40620001c004500b000c2080d40c04006c405112141810000c0d00428400c2c00020800c0c0d00c01c69480c000c1400340701c400400d44178070b4020801d4180388261681101540e51245014401c0c0420780000440340d10382c40040c0207489a640500a582052591b076106102e039001b4000450a500503003135150704003010260205900085403c3c010f105405030f09143d05200c8054008a404d81d00402c041c56100b20003820b103e400c690b043d12046a020502c107082d20003046001 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 174085863 1250 174084613 174084629
    0xe01151512060305010204170d080708060307030b09060708011505030106030903050c03070b01080c0402160f05120c03090a051c03080406180302031b07030b0106050c120f0d0b0102011505090907 85
    0x2c900803060010540c003902c1640d100c0041d003038040722040301c159641c2003000805400100148001940b0b01d21450307880d0303086100030f0119000760b0307140e81d5580605a0111040748545e4040001c100c0c1c842da0044566005012155501b109440042c90091503444140241c0c018181c441e5058810035200e00101c0d02c104c4c0300b60742078030b864214914083d410a0340a1043c0000c900c07810500445501e030510843c0d1008c1c211039842c24660219036078404190001d090140c8050040710b0394a0b441c609241c0003442041c0301c0744003465680302041d08010340700e021900114002d010300056800d500e9020fa040c4583d450b0582040102507840703241080181c007652055620012074816402c080603000800303414081d40441c40c1024400e00007079040d9840482e0320002d403112034524010403550380108011b201d800e6618081d01e14584260070204000d81c0700d03144541301c2c050006170081120240348541c604590f4248003d001c0f4441d00082e00f5840d03031040c0101d07449100081c000c101030507030070404bc02c0208059 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 174087113 1250 174085863 174085871
    0x6051303210306050105090a12080c0a030801061806200c0301020a0e01140702010f08150405100314010501050108070521010b1306050909160e090a060602010e01151512 74
    0x28020311003941c0444040700010908101c00411070350302401c1502c24002c0058080d08940e0318080504412044206040e41c0a200801104000300301c1880b1503841d040c001c0e2903054241d40b501c08000c207c03034030f8402402041c41c0d4000060054503486000c000030b06020b8100d640d12043e014000c1410903030400c00c0c940d85503200158909060380c01c12403481540600b40c948070090507002c81100b1191041540080c0006d40c030301c0e01042c25034094100b80e81c20450569180d10030340e40390070120302166801d4910702080949840c0c2041000700c004082041011580000c0c811545081c00180031280050482000d1002c00704060b204010b00ca10f0410030003d04058801c0c071541d40b031a01580c941d211081c00b84a10003203d20104000c1d0180b8126040c208028008507110355803c03818109400480100100304400c40c81d404006545071404070b40075040c14400000c0d031504d010000f170b08403074205050300c0d0180d040510f200780851500108008071019081e101d05e141000304000c5510501c086880900240f078 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 174088363 1250 174087113 174087143
    0x50d0c0e0d14010e01020c0601050d1b180b0609010e06031b0409050105040e0703030c1e08030a050708010f0308040302101403040c0302040b0906090a0902120d03020309070e040b0106051303 83
    0x10702507010480401c00c1c0204803200308444036134280d104007c001e00955109070010052810f00c1ca481501391406402100c0384c5250304c1030310040410107944004003401002ca410502020188280382440c00101c903003510f00780001001070701e4503006080113880b030503000c00011805c041c402c070183e410324224803407565150f0300c80a13610001c140038054179014900e04482c0b00c5c01104000780120580b40c0503143c8400d0300c90790b9550103020b01502d1000560541c115850040001c84840284d40a400da205011866150010000705803100507400009a070cc00c803a020408030320888100c0301039a4050f5003907000e00464413410f881804200c1800082081d002080106002080344d140081d00d1080f1001e01c800e079401000c00044420a480c50350340250380c0d401040550605501c45c000f00791002e030682d10410b04290400d410721901a4102c00460b030000f042001c00401404400d010b0310b0a6002d5840340d04107a1580d02224805004000c18454005008080e0f03014034002c110003140c1c0080b1600064030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 174089613 1250 174088363 174088373
    0x22107110d080414030403080d0b0d021c030806060310210b040309030311010522110901060323011202090a110a0f1815030c050904140906130201050d0c0e0d 69
    0x480f03003035500e4101191030307102c448008800c0710308681d00081c5103424018000429001018118401c983c080310701c0c008400141c0b20100911202c0642501a41c448051800c000e440f404000304081d2240c1010004c02c809032001c00304a100f6140d402080202c91f10305c074101030107400205180a00711010440c01c210400da4854218130a491099844e44220a80b403031030103080c0c3e1401d42d800b01c103003050b4501c501c031954200304040540c6030088030f4108030700801c00d0200d500f4040c01c0e0811320000f5100e40031724a10b5800031006000389841c2c14401909985000c490141101009070700a201d24508004104401e1070f580081c1c0e1511034a580308d0780d886503440005056050141880d8004c02d4802c0503d0080d09034000e10f05084511480484c0202d180c01c42c0e0440040001070360120904c00c0a01001d1484e441c2c5214901c4413511140c103812031070510421580c54040f000b41a181d0001700000d00c80c0050b41d01000756a500842c804000c220350034081429218113041d40001500300c841e60155505000c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 174090863 1250 174089613 174089627
    0x903200f130209100c0b011401031b050c070b0708031518090d030b0d0203060601030e0106090603050a060b031f050c0f0c0109020406140307031106091f02010f022107110d 75
    0xf90300f00c41400d034000e0003000170344200000d841c0203402c01441000400501d500c000075880380700414940060070000111400c1804601858408000384002c00d1f0480310746020020074010b0445114102d0818a055817030380404d120041c000c03848115030180303092168441600c1c1c1400c0044440e0020001e140a2036810307500c064180400c40000d06200040403142401041e40030099000350150000d030391102e0065025050001c49501c2940d41c840c4000b60010b118031454000c0c41c400c0001e40b42050841c1440c01c10360300030340c0a9074429003000c070b09916503101000c24900c406143d640003103410345d160b6903181c4842c000d11038221040d000c00076074036400c3d26041d4810102103208980c10402e55840310600701c52800c0c403454054041d400200d0a1020550310079009103100001080d5a14012040000c1900d0034203d071041040c000c00c00da045069140c080c00340a0143d400203901b1802e02c410590329020200c3e03180d6a101100080b0408150141d100d00078043c107528a0504075041c1904c9520000c1003c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 174092113 1250 174090863 174090877
    0xe0601030503030406051012122a05100c0c0609050304030b010b03040b07050307050912011d0d14283513030804030819060b030114010903200f1302 65
    0x24903010010320a0b040d044881c1043c2c40868500e04504112340e561660300b00c00c080442c0d0248045a00040a405080e1008600c031804003021110203645d146000c81ca0310380140c4c50b0742050b0f0b0404142da44484c1d03120981d4840a80c000002280320709071410010704511850700040d013070185910011803000c4007000254011031048400d5010b565400c0b070100c91600007031700e2550005004000c03495051030030380800496000320b4000052501542c3e060742000b0750151480305a01c0e084105006c5003242c018040c1d05035040c962031100c0c6409098031300e1400a010508290010394a03204400d0003091003415004c81a50500084414001ca042c10200201804030301e12130b000e41250b80001c512466481d2500b41d841da16450750401c645441c0e0f41920350f690010414001c804020000541c50704039405028010204410200e80c5e035410b040904c0004a0150511414441010b008100154005501d80380ca109010380c038948510250000401848051083c00d90004022136201c21006003a0700402d60 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 174093363 1250 174092113 174092123
    0xd030507020d0206060604050d11090405241302010c05010b03070b190302040f03060513080703090e0f040c0b090a091d0d080405030702011d041b0e121b040e06010305030304 76
    0x9504002c2c01260740d880c04036010798000341e050000f00002d0410900c07101086204800700040c1440e4100803803002c090803541036802e940301c00c01d5180c020351052441c040c00119a081d80d1b05518040c1c05084201c1341c800d030000c0c1000118045403060040c20b600801200c2d0300201921142d55480d030912005801c001d6881103108540003007c2d208038003e208890032070b500366501000316465516070030001d1000401c01c5000150100368000010301003002400d03180e00c01c1d128024110305142e03d04000304030090082c0101c44507407083c8004154042c03c41030896001030440c1c1da03210020004200100150b43c40b0142c030714249a481c000c04075001681011074040306045500c001c104007002c440340c500945000d82281c10400000c0c0140d4802d1a0304098025502d062220800183e00864101d80d04a65110300200102040d00180d81d400803144007643c40440d40c141a5002280a182c1c682441d04107103041d0424094290030380b030320360380c00c10342108004005907000782d030b56800e12a80381d0748125003c41d4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 174094613 1250 174093363 174093373
    0x1b0305060109020901120902030703020303030103060e10050f131b060815010521060604050a0801050601031109010504050d050c1207060f0c081204020d02150d05060315190207050d03050702 83
    0x1c45050354404d5601c0f0850580d640c10a0008250000c001494450403c0c1c2e0540100000840940c070108015802184034400001b619104651190b0801081c00304000c6194100818400c540b006100724680140400e080320156104501c0c00b2030203a0f00030751080e500c8002030080061425041540548101d2001c200700d41342800d500300456041c86180c8100002c211f1652441c2c401510301403407183c1c00800030b0100d41c038050300c81c4001600d070a4141c0c8004056034680c405c0000c00c0d40e0501500070804a4128000c0c200b00d031050010b80140114080c042c050740541c2a20b1040c80410400e1200b003410107000028100102040da50b1070703d10700d0141700040303440c000d40d110b0301074469141f208815070884555400d0840f901015055004090026a404040c0b031101401582d111000f0b03080c40c5107000c48050340c590a2403516420f55000178402031003904018214180c80d60394448050740321440b17102d070190082c0c0e442d40050090041c0040a4068030030b900c0e1180940d070705a80001d02484140d008c80b2 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 174095863 1250 174094613 174094619
    0xe010e06180c09060a061214040c061803020f040b0409060c0c031107152d0e130207020303070206031b0703020a14011a04020f07050a0501050601090819020118031b03050601 76
    0x34401800743d41451708000c0c101c404001d1a4812004108000950b85021a01c004200c801d403090365000d40b82602d284100c2c200c10000c1903049000c98005c98091070604414030300d0350b000150b0391502e03440d805010700d4803055800d04a9a40f64841060582c1c000d10070406108031102c0200707041c001203c01c034003007011940102501c010003e8000110340c910402000351b00d021394800c0b00d200c130071215a90440d040e5100743d1181c2180c9660191004241a5210145c3c4041801000301e1103060b05020f80364588108070910250314040129100e141d0150307602941c98540703205c21420500365a00c0b650b030f60540071070700c01e0805601144100c40305009143c00c0400d40401c45c9018201d4020301c2c4401081800030401c800e160400307801030305110000380c00c20303030038034a403034072000d04108030403c1c1120607964030810030844d980c101488501810704a0024078006616210035541c013403034000081d050003c00e000c50704111030340c400400d02a590056120448031612004000c503036041c0c0c0011140d070f01440c4004 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 174097113 1250 174095863 174095869
    0x9040606020304451509090c05120309090a060e0106053c0a0905030706030b0603070311041203021c02031303030c060609051003060608010213090e010e06180c 70
    0x1580507141d80030260f0810f0001c0341400100c2e00620300f501310f0100f840402c100c840a041000e10030500d000010081154024410126512031031a0001c000041c60300d2038950104032190040341c1a52000d50302030000007030198520b0310b03502422000c80e0340404803070200450340b80e190300402c0c100c8080c2500c079105a41c840c0000d403110301902c0080614058005c45082c0f03503402d1814040d11044000e489001c018019020406241d0f0240c0303411700c081111100304000c1030a04221a00080c9003526007040701c4000d031070020300d030341c40098001810140c030364031006045070720f00f01100e00903c0d031000c1c0705048040900e4040d48a040c8045000824003000304000c1b03280d80044220b03144c103048034400707880250460340e041e034032071201000645145954070070110b150909845418011000e00c1d69000160b4607501d403900580d00b15403c224032903401032001903951484c00e035012081d90f90006020035100d1814401c00d00400501d84400341324070922003800344100c807000d0034020384400720f0255070564520701300b4 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 174098363 1250 174097113 174097117
    0xf0a0e0405060d15061503090b0117030301230301020a090e101a07050a1a0402031917030408130b090f15163f1b021207080102040b090406060203 64
    0x403450f0010380310402d2400007800d00404280c490144000014030540b150014421900c0a01303500d808281d488074440180b20030b000400d17005050b0300c24400c9501d503440c1c445503100d00040c03041c3e18203180c4003c1c07002c0003200940004c00715038001800842d1200d80b1701100410409140c0301b8141c0d092a82008548007200002640059030075070800d11201038882c0f402d21015602041d000e8074603000300041a000150031100c1e002c1041800d00c100b001328201b600401d41072004404000724520b540109400c001b4806000c10100710226180851700d0340d40390f0414001510920403c4111104242c10108507078000c9005000b1200d41075404900382e8a4010a00242511141d070010904d601400724170148185403d00410381807240031820444541a01e540d104242205c40b21480c0050410708180240e03291071002c1c0b4440024586080c0c0a60714003d60041042c1c1010040e010f100c20400070a802c0c0b80402c155401814610b008550305c1c2ea450000d10442d81000010b40c1c0700c0d80c2015070024001d880007003 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 174099613 1250 174098363 174098371
    0xb04110303070c140a0504060e010f06050c0d032d1a1005030606070305070c03120e0d0f0f0c080d09091503120e040b06030c130501110a0308100b0f0a0e0405 69
    0x14180f40d0a114060021200001e1003541c00b8003240700104107501c1c3d0340201002403100c0e11204507a941007100801c2d203405030b0f03003240d000c000080c40750100800001400100c2b2403541e0900240f40071008042c00214040e02e096442c2d183c0c1d068500304a50991a4004050a841098901c1c1004100401c021143d5100a020380c009031080c00860540d01d0400c0c01848201c5c82414090701c0c10815a07214004d00c504c0340d005131101c8040b50720380c238032854000001e00643e290487d81ca01c0c0130740c0a51744251506a00040180500380030f81c0780002004500038011000e0b0140c503007154400d4002a9008280b102180a400034240c28800800c0c1c025450104500c262a400681e8880306464441c0c21591829044002c2d5801034603010305039120745550300258040c10060780d52590b1119030b1440e11407002c4081d4400742c10030400005041d0490004aa00c103501c681c180340500700d6443d0712400c03018510392600700c140c0c1c4100c00a40100184007860040880b51001d864103000c51058000304821218215 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 174100719 1106 174099613 174099623
    0x303020d02130b13052209030e030102031006020705151209070e0a0603060e06090601120201120606230a0504090209060c1e0f0109050c06071e0b0411030307 69
    0x300c14001382101b139485410440985400302d15801000c40f000385820780d648a48000c0500c103c008044020300100207548904002d8940c0d8900c110074414000584100c0303100040c3c90501c800320016046140a0060030802c02c0303d1002410380000b400244203008074400421141c5807044140e00900d28410300240079800e526101c2e003141c1c04100511866030000f0104041c10703030006001419205030311484075030344600d80b0040e01c07980000e035031900361141481c01c04030310107074441c0c48c04500c25541c41c49207115491303074024040d46209400c00c0800140b020441400081b00319001055807000c06082503191624005a10b802c000300244407641c9107601d04005009442c3c100b18281100302030301d008012030705c01582c800d5a41c2c03000302007144c020a40420f00e00c0034466000300070100c080c1c004140c001502501e03c1c11006040e0103c0b000c0312840e80c2c2840d00f10840c00d000003607400ca9980f007 = true := by decide +kernel

theorem cover : BRFrame.Cov 173920863 174100719 := by
  have h0 := BRFrame.cov_init 173920863
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 173920863 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 173920863 ≤ n) (h2 : n < 174100719) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
