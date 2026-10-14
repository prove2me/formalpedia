-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2743
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:36:36.200331+00:00
-- url     : https://prove2.me/submissions/30383af1-7d71-4ebe-9dab-407687221eda

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 493165467 ≤ n < 493345323 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 493166717 1250 493165467 493165481
    0x61a2b020f0d051506040b070302120307020105062106130303020d0903031d03030108060c0309240402090c0924090405130b060913030e1809070e10081e030427 70
    0x110701c1000744d8110952291030035101502c03c014800341c2c0d103580d030742802e034035224180030307100003498000042005455040d0451030080101b03452030203d10307441145500049055540b00c501035030040d00022003000d4403143d0b00a02c64041d0400601e0800d01c200c48005585561000741d020a49660070018050901444481e0241c141d03000f42d801e65042c036502c80c1d12880301030306015400c0030100110701020814010341e090030483d0640c00f003e2841e60f00092004e403000320340c160b21910a500001c5c101c02e2008007114144280104541d07003800c000556460340703804804070007044150501034000d01e82c40d90f20a460080c58a40442000485d6503e4412a0088000c160a0250b0340800034410001c5e41e902030b40d0304691740b50030500400d1810350042051070300b02200240c1100803040c14041c07800c10200d8484280d4030011005d0b43c1c180d850b1039a15100500fa407191003800c0c0c0c0705041e921054841030b00300c060034003450000d82c1d02e003598070a510303c0420f2104042e009110007906240000311a03e1044c45 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 493167967 1250 493166717 493166731
    0x110f0d030806092203032403021305071b03120b010305130f03110f0708010f0e03120a0207080a050a1805130203191b0f030606081306060308030c0706061a2b020f0d05 73
    0xa4001ca0849c0e020540703090200002d00210341e12000450343d8035000d90442d4580010300580811070039118100100a0b003c504620746005160448481e415440ba004035803091540314038041d09400543d4a03500c3c400d112500070307010403801d01c190702a420340c103006001002d218407004000c00342c00d00e00c0e000d003140e41010b4560a0240f810758074403890100841910b16a07824802c441c940d980e40e0249840103441080401071407910000390700030780d49401c4405804040e00300c2da2002c9002c00703025001320f500820350161550104541c54501c501140c00d40085a21000450504120341003a40244094a591988101d111140750107041a0190701000d800c040d80c0040c6010310400b40344c13030301c041c00100000d49403100c14078809904209119540d044440110351081c2450b03078a10703044054141e1038124403422910b013810304030001aa071042d80c0d10480000b83c4202c0c0c0c1840d12107402003102c605140343c1050300c80d01004000308000501a0710240c503c4460062002e6038601100784001c0407220001c10740 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 493169217 1250 493167967 493168031
    0x3090b0109150b031e040804051009030317010806061504030506070c12030b09180c09040312060603091205031803031e010902190509060904020403110f0d03080609220303 75
    0x4040640a01110601d421082480805c0e1351074905042c5814400da82003107070001103200b40e4000203030b8003050b070400321b90083c1e49415018451040106401c1401e200705850355010801040329860015040c80f0369200c0042000c0c9000e64980e0f410b405d200c81200d410b000b1461440c80700c000c0c80201a001c14031b58280c4d1a0401076011503000054017024042c1618000004000b4400e80d2000d0400544003261001028400c1500d001d103802405001d23030614103040c3c5810840c0008559019001d03801080f54420740800900710124401c80710307034000900d0705400c1e18407007410301a0310324180300031805902514182e0403500e0401d20582200d50b0103a02400c610351041001031150309204618a0900c2c1c8075281c00381e0303281c500b100003591901580030b90f15809032002400204020140c184010300d0b8905880da44801d60943c4100114034070020700180c00304503000005507180c82d20340380503940180c10100104220902900020002c6503185045000c250390781d0403454540720034042d0352641192003a80e = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 493170467 1250 493169217 493169221
    0xa0516050a0c0312110d320f060415090f0518060a0507110f1e0102090a0902030705210405060609010b0a140c0f03041811160303090b0109150b03 64
    0x80038082da420015080111040013805800ca440d081061081a0304000e1511829921000e500619940310652070710490841e0007000c411203103050b004100a0142d03108056031b03803030b540e40001d504002d192651041e900c424401c140514190341c600644052000001e00c61000c00c0300008452015065003481c00d1100d10141c51202c000900962120750410003007426111090155010b03403c0b94002031003805102c0b0f14290a200003c1c806103160500743e01001407800200145080344100361f01d40e500098120421300051700103800454000146142c050301c1c00b44600e2180602040000e40300007001054010720040c00350800207180c101f80c00b2500c81070f0b59498100e21075101c0c861090f081e1b003171205c80d05103c26420008026034943c10101302c08d840e021030a0b401c450b0340f00da2290045540000d0b0041d4242400c7e403c51140d8844440d15404452074090049401070010300c1d4184120200340e12210ba600001d8040d041c007500800718502c000c20048400d14207d420400f480d08100c445d0141802 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 493171717 1250 493170467 493170487
    0xf030605030309130b0420130e10060f0c0609080301080d36080a230a1505043f180303081306090b060f030a020a06030218090a051605 59
    0x5101080c40100c1d81c000581c5c25003000890302071b02c0c036040e01544101001c40004031401c451401090600303850601d001005407103a001c080c44601c240c03100708452040100a00006000c1c0421b07010340e0b591390809101c2e4520301d90340c43c0291581d00d58115001240800100004032040200510004203130030007020011000e0ba0b01d03034911041610b4948900000102c161034800c0c50000c10011b0700c80c44040d50b051490500300422504031909480c407014032a4582010000e0002c11f101d8400c59200d01c40c1f070301100f5126070001c05400003401c1039900c1842014800c4c0d80d400c80345980c0c03801142c80c03203200c0c0c100704041544044012400da904e40501984a400d00c98440c0001400000d40b83e150501002c162036941c1d41c1c1c482409007800c02030000d45090505c00c10701284840c414881c520854003201c81002010030f00d61149000b40c002508075a1981003400064001c0d0080c0c0408800000c035041005003142c006100302005451407a50680c0c0c6e2424003030009031180d0384126400716030826a24001c0401 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 493172967 1250 493171717 493171729
    0x9100e0a0b1f0e010b0a09060c030e090717090c090a090809060703090b070302070801060b09010c1106160b0103061d060a02031e01150206010e090c0105090f030604030f030605030309 80
    0x1800c0d212115003440448290641d00141030015066142c5030f821a50b840d04145442e5920003081e03030000c6468171000040381403041d00d042c08004c0d4966503054032140d000f0140b11454001814550500c0100107454540a440c5840103219001420081c03a0f00103142c0c3c180400c1c00700180c00000d0481c03d0000940104d1000403c440c4968000e481840e6600382c507041c100c5404485421000c000c88000030158180340e40090f0702d07829940404000c00500d955540b40510b203204405007a03001c20030340141000401d008401000d020342d00a825035140c80003210042001400d141011281602c02c64014030034820035200d842c5d005059020328805003560030401a42d074100c0140382050007a000000187c100790450042c500590302c0044221065031100d00034880740074007c0600340188280b02c00040e0a00c0c842d859a80244c0820000d0003141c400600111036590100341c50079000342c007907520550292001c002c514410750081c0e4800404082c600c81c000c00b540d52640c0054429441448020001d585213 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 493174217 1250 493172967 493172971
    0x9030201050c10182001120914250f0b0712020709060e04030e090f27030403140d020703120807030b1002030a0e120a021c0b09100e0a0b 60
    0x90806644403242c1070140c501d008040d000031074441d82000c5540012090000b203007000588684049000c00640260748100070030300c0c200040c0010070240c4801701ca041160310440752070b070107144002c180f07450305142585410b1002461040d48000300e03800c040c2d06000319103050082c0241100340d000151500629030b04034084c0c0c880240003000e0003600c5488560007000000002d150303150f82480116541c985c4624150406c071025008600d10007004262880d144505a1080d0609a4500b2803a112030031900703078100043c2d03c81c030b4000d9000036000003030705801c0016000a6101d0f03100c042180701a40000c609181007204040c042d03501004d4244000f41010920381c0c0e400c00c0764640407400e0313611040203c0181054030030458005999886100308640d010008114090b1507031100d113a40d420320301c207022402255210380d2520b0b03048000a4001490502c110f02c003468007240c18800c0c00c2000352680c030010601911140308e00e9202d4444d2100c010031031701038030307240b41d00e0040500103010140c0c44a444d51070300 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 493175467 1250 493174217 493174219
    0x2d0807020c1c080307171501030506030a03120c0e0411090102071e15090b13030b0705160b13020901140108100b0d1e060306020d06080c010f050306010c1a16030b01090302 75
    0x1000040342248a4506801c41e0031b8500301c4c100c400d08008940c807481003900840c0d28002820180012800c3c10000b0341050308a900d0340c0d450051006c11140c5200401c031000352a005c0140c0d426100d07206a43e0f5000b2000c1840361205141c0d80e0b2110f010000e0301e0481c83d07a10107049107114509400700412411001000c42d400020072004910313030f5190449a0033749607040301160000103d080b1650921141070071003178034841e020003e4640c84a4500b61040c1c06000480400000148007034000a141100722503089140e00728040c280392035503400182c0d00765090300800352110b43d1004101c800c0d0b0717000c1d5215800c5140310b0f602d55012402d00c45811800d200301c640e0540b5a945074080210040c601e0024444c80b005240e004001d403a84a1500c1c2e00030f540080605440c3d035040c41c2c804030b00a903000c03800401850f4143c50380c2140001d04041641c803a04000e012506000c051807052b400304117441d01c0211301c00d4010703291600030301c1c003064413403024041c50310510201442e00031030310004e90b04148a09c050b650 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 493176717 1250 493175467 493175483
    0xe010e0a15061d040606080601120201050f0702220501060810060f020a061506020f0c0f090c070609080c0f3007050f1e010b030a032d0807020c1c 64
    0x2941c00c0d41038050a00e0380d02c00300c00c49042c0350403801003002e5101814001c510428040c4403a0307039582e41c096642c580a004000840f280812100010340c01807004101940344c00c0c1038941848000d8001410b013801c01d4000801d5901c3c0d9124065096482e44900f9014003480d041c5000075003070800d402105034107107000f41c1080c880341a00f5000618000c21480c40340d260b009805008101c00d419011b01a001907201d0310000d8030803410001190403001c140300102c0c2501130012011865001c0c1041100113001d41421010042000f101e00480c55501400c0c005034011190b640d130320300c805081d0a1900b1400c200b0412941c001d0429080c200501c1c014045160403500c5031124100c0101024440600c11004010100e02c1041c1e00c510688002107414a0020110000c140018004040060980740c00c069000d03895045030b503138500001c0c0140c0750030182c000d40403441c000803182d1a4121169002d0002500302040100702005600c6a04101c500c2c2c819400750742d01701440c802801d40300039500c4562001803050b4 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 493177967 1250 493176717 493176743
    0xc0b0901020f0a0813080604150213030503040807030b060415051311041409070203030f010e0411060d0f060b0a02191407030819050306061e0d0218040e010e0a 70
    0xe07100704180000100b452054410700d5020f89410203803030b8481000329001c0d80f03002c00c00248001010566512440c0c118841104902d0143d0950f03009600a1040d0300014a1a0b1804004520100003800140460741c006008903800c6041c43c0c10380c00001001248900d0070607030281031002c49004444100d82d001c3c0da000105540003010203014160390000802424400700b8001030000300c101041c810517106446c1300c1569281c901c012626488102e401c452044584001005040002c5010b039034071602031441c412010740c1c0a400200c4a9000340703022000340f5101c05c0c0c000900b01d61071241000600d500b48020b494000395400c043d40300d0700c0c0c55070401e401c1140c0070382c42c00034040d00c200099000100070081d10005d60711307032070b00d1042e1360000e18280754901c001c105d101d0103103401582101c2c0581d40c020007840c10010f50301808500304040038031144c1d82050510401d0030700b880c507002030110704020300c01283c0101089014003044a02c014442060703030381001620b401101b00032525800c6984c110980c0d4042c0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 493179217 1250 493177967 493177969
    0x5041a0a0b0d110f030622020609060f0a02010b0609010f050304170a02060f0901090b0112020a0915050112021608070c08060103031e0804030210090c050a0f0806130c0b09 75
    0x3000407403600e90700190310481030010400c5111040e406188200e8464140e161028207156840500f1110481c00100903800322008611030003403681e01d1f910017001d151608550344081a02d0340c11100341d045c2d44c0c407000324844101d99020700800d00c401d10141d6030b40d030500f0600c800003002e948111500303600740070000002c20b0038403e01a0561101104080405a40d0300070410002d545800c12030725030b250300307040c800442c1e0000c40c1030007846210360300310100c1001a420851002140201c20400302e900401003140050b04584030b000c1c1242d5403400c007a0005030680340c00d001400c82c2c10482c42001e105032041042241c4900508915202103130010030039078070b400e070900c5c2c460800c81c0742e40c21007029423003031074000070805034044a1500c0408008009058604800d03009482110003a2801409078001421402c8111107a80c0f1520050340200c510b102c03995a00c002085603004990418414001201d1050050a404005c4143c00c01107940c40e04031138988a442c0d421100c8094094042103000c00111482d10b = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 493180467 1250 493179217 493179221
    0x1020609030f0c0f01090b040b150d080a0e0a080d0f030603170f0c0106090510052d0301090f0506040212030325030b031b040f020c03120901110a09081005041a0a 71
    0x81350300c64002041321401c01d0604d02c64aa502300c80841380b12241e000019050103004015000300000a0300390310039001d4640c5c0e203e006400064455041045400310f00021340d6a4468460041001101500d11204032038001850116001c10040501d0b0500408000060107100d9a182803a0300c90300054645001c002145114850f070504035003207608002c00880c00405070b07070055001d48108a41d400702c5950351014010002a0118464039113066907032407544081015200c018402401030001801d00c4841e5074605c5c100c0b45c840004c0c0e40320343c09602000110705100501580100c0c8a0004604505e0070302d00142c00c0301f101816800720740501c002002c00b4540241c000c2401144020103490706940f0301c05403128055034420303d252007181051940110144d452007260002c0740300c040518905045100048203035100903050700220b660714041c144100c41090060301d041c0c1906c1c0d0320240c2c402c1c0341080092802e601005044421841d1000780300002d807200e0041d016486247e414200c041d030b41d809031400 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 493181717 1250 493180467 493180483
    0x60717040e01150e122113060306080c01111b010c0803151e06040506160c080f01060602010b221103011509080a2409060213050102010b01020609030f0c 67
    0x7441600c400403e5000c50344400b0a07000b0b006949032903002040c0e2081012030354100390b030500d031038004110310756031025503084070500c40c04802c081030f15180c00220340c0803144003581d01420003c0d036545803c0c4048102408444800300342441d00b2150f1000351000a500c60003608080103501c5280020001c3e164000d507401040b15400010441d2245000b400342c40b44c0081c0d09807501d01c5100b030034102d8100c6440c01442918003400c0540a01c0c241803d0406004190340042c1c0180d200c1e8840c00c00fa0780c0041c83c00c3c0d01080c082c00004020305805a010a078103400d66513190080070659040c00c501c10803d0310341c110101d420b07120600072481c0940b0341070344480003800c0180d00c10008440000010420700229404405080001d41c1d0750b1071459614440c3d562070b50344081c801001c00c0910b4070642c0140301402e0350a603404000d09400134400401340d84d00003c0b03900c03012141d9042c100004081101c1e40e02071207100b4441d4428005000686401e05a89860703210743c1c250300613181c2c0080307416080383c0030400002d0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 493182967 1250 493181717 493181729
    0xc100f27050a020a09050f06030a200d08180111030304030c03032403080c2503081b01061d090118080a030917071b03030f0e06090d06050702010506010c0206071704 72
    0x207040317403100d10007009010110340395900200000c0c04103190f4100055002e5450760402211042801c00c0d80340d440d00d1101d04906294081350030507034003003c2a0352600400100e070344803480d514a0107082c8005040d0f006080c0d51456903030014801c02012075003200121711066450310f80010b4403403680c8a1003c081081803829540d1591036170001c42048148001404080e100c80111181c0054928107138805c11822050098500c00851040000415500141c814403d5155503260891842c10a4608440255000c030055260503640c04e00307a1a4100c50042d009028038000340305040344000d0b44189080d00c001300401d100b20006022150610aa01c801c0d42d05e0b6100d6041c00300c41c030000c015402079420018007600d0314004e941c1c3c2c0040640e40383d440241125410303201d9109071112568180c4001001c00307901900b0807000c205641c4c29542c0c85581030348030b42c0310381c0000030301d410080c0000713085035070041a00e41404586100c07003025035582c1c01550f40140d840044e8460360b0001e500c80b0141d50041e41c2c402 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 493184217 1250 493182967 493182979
    0x1014030f090c030d0e10030e03030708010303090506040803070b04020a091107061a1f0320130906060e04050a06030f0803010e070c02150a02120c100f27050a02 70
    0x400000d8400c0e184860064511404944508030481c040549921910a000e40030035040c01c00c031112802c100e8000c0065040f14180007079001e8050a1090440e4800c98202001441c001c1c0103000709600a40a00041c2c5000da03035084c142420000070b203a80b40309084c405001c04504030006000c56494030311a00281203050000e00c040368140030414660b802041e0100c0e080c4d420000740c904411445905072000c100010545104001c03c10b40080c510a40001c1403801c0685403441c080403113188614401e5191a041400341e61aa080d2003400700d02c2c036160f0810f109075410024100061a030010000d400392104030340008151719a02c2c111340042446500080c81d8540200000090000c10b50145048035107140c001619a6500b030b8044941040c0182d00a610008880317041800d6400d440143c0740e2103601e0300440e019005540322008441d0068070480402d039101005810301c2c1005401000700c13582d420325080c02206400d02c4400c4a8500700e0780c1031010441206c0c07002060200c1003102203400b43c0c010f000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 493185467 1250 493184217 493184221
    0xa170609010218040b240904140606040347071d011202041a03010503150c180d050601090501091404080702060705120705010204090608060403021e0f06010b032502030405101403 78
    0x203400501c0c0c07c682c143c148102d1130107440040010301c06000501c121001452149032509690b1016175010540f1031030381400307a100e2030100404582043e842ca804652450541c0c42108442001d02150801004913042040c558510440346000d08040141000c0908201d0745194024511070024001d6900c03200f0a10061000b50000f41030b801c00440c169001078098802600074000901140e00c0c043c1c1c0c1c0d0340704010f800c11101d5010312504409000b00300005140c2a40d208182c0c407120b181000a80050700791395a620010031941145224601001d18403a241400c00c5c42c0c0380d01c801c00640101e40700a8040c020004160701084014482020b65002134405e044d1182050700b0114001e41250040d11111854944003184600740007610390310841d8194010491441c84d602c0c070f40c40d842c6074108140000d07c11a203c0e40803200040c0b08650107401041c000c15242e141ca43e04001220072000d00c4504441d0028103410a41ca60210480e410f841080e0360400145400d18012295003000c0c1000158007500401 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 493186717 1250 493185467 493185529
    0x71b0308150f090c1c150504060f0803030a2a03050a0b040b010e04200708040801050f15101103160215070c0e0601120f090215090f010e0409020a170609010218040b 72
    0x20680c41903904c16032302009a1600d81000d03001c01c25145c00b51030800d82c01440003448001140e004000920250290001c6180b0040800c1666070602d1341c500307012039150300800485502c40e10a40402d00360460742402040e03000800641200b803c40085400b65480c0c2000040300306035a8412582d4400d602c1c1841e41d0360602e03040038240b80d04a401101c0381035003090040350031303503203a02c031120f001e90340603545c8411285110f810883c0310300a42407090300f444203a401c00b440001e0188060a01c8560b2032a4180790100148108868882c1c0c4001e89058200c00303210220104110308400816604885003540e07151b2100c00040e0388201c030a01d080108503080681c0b120b03d00015811505101c2d00c240c032860885080540c811441d4050450301c00d41120101e4800c141541c41105001d4044401810001c1c40d0045138000c03e280803050382208102c404091001d100c4084100f04c82644100c5800086042c8a00b402c0340d84039000301401e40317030320a0707480380644880341e6100c89123610324800401f655098405280 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 493187967 1250 493186717 493186751
    0x7060603050d0807110c060d1e0c0905040b1f2d050d050708090c01180b0c0d0f0206092a03150106020115030b010e071b0308150f090c1c 60
    0x613a03c00015036900c07003110307a40d0f40000359107100e0344c0010500c03030034142c034565035a00601280b6032a04c20015448003d001507500c2e072054990200059495114060510061100361900d2600032401003580c03803240010302c0351209515100f0049403812482c80400342540325a04c050b0080c1c0460265411500d00c401140c1242c001d00700740c44640310a101503030b030f011801c0c0e4482804031140075070b540103a203047c6940c1d8440c0001131a9410600d0301000e8403520782420f0101d40d000a200c06c141a0b1162891140c45074104000014808861000b01118540307402c00c1521a0300405150806240b006400317064007091038243c0d28101d0018040b101c440c43e07400c003103200201c004e1107608090b5107003880c24000280c04006c2c2200341c98112160395682c3e443c0c00605d041d0382c00c00800241c00c01104109500c002003401c2c148080d1a40139a480c00e00302d0501c1c1c0c0d2981c2c048004807201510030301403040c071007219032104491240c0c40310342c200015490b43e885401061840d1025008c40020b40e2500d068049070517240 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 493189217 1250 493187967 493187971
    0x12a02150123060c191202010504110103020c19200d0c0e190f050f09070b180102032106030607030608150603160905150a0602150903090604080c1513060507060603050d08 75
    0xd610b00000d10b446c0d03004243e0803240b00b41c5000e0030381080d04041065130b500903001800c158816104484028040241c030184079580680200c5014810894101e00803a0103089520f84400403651460500c1c420381d10f42d8164941845000c82c2e040651000600f03000290310301e4000050700311028000400d11902c1d110060004443c00c00b15649130001151002070300190b0202615080e150444c80d001d100c00000c5800600001c0007030462208020080c040410900300c10340c281234030300e400116030500000b09810400010600c8040501d0008200408400020802d440060340c10b120700c510b8840f680802c0c02c00750303070f1140c1c1d020545403041e00003090074903640207501c59586900c07040d510b00700e0b10f810082424454404e0a0050748a24800216410b4240806400c81000c00442e40b600301c5010125805401c40d5200100b83d8016109403805810710890b1004000300003402c052414641c034449400035025400b9040c00c0120101d101820441160b008901550708081100c18045085000500007081 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 493190467 1250 493189217 493189223
    0x40902070f020312090303070b04020a0f06020d030c081e270f060108010207050618150408090405100536090319020c09010501050309012a02150123060c19 68
    0x20b40d10101c4d007000007601074405201e0018095880c1890b1921021040c1e03c02034000c0e139208014500028800d803101410b080282429005488100840348015007107629600100050041200801c0440740210030100e122080b030150801140e10b44144136494001c000e40c010360081d884040d40340c0031440c0003c2c00000ba22088048541c0c903a00c0750800ca090f4055044018170380d40c810004245e0048403600559280301380801203811004c69941da2011543e0140e40503645100c1c001140c40c01401c1c10300450794404560260340080c1c603c0c01004c80e1a034484466408038814140307040c410501909141000b0300400020515028140780d440180c903179118402d0b10030110300d800c0a0b510558004610500405002412000c66a18000c0156200c0c0d03c02445901c04c0d55990b0408500c003401c1c586140c1ca0380a005400509415800700040c1ca4039015036003000e0000b5020b001009a152130006103018248100c001c07140c080c202d140416010f000c0c5200e44042c03800750707000701a00000c03051503640300c01e40 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 493191717 1250 493190467 493190473
    0x702100f0f11041208090d0b0c03060f010c020a0b0306040e030c06010f060804261611010f170a020c01090803011202150a020a030c1b0b0408150906130602040902070f0203 75
    0x1d9140190481c80c400c910130300c10620082d50a440100307a41101400300000c018180000c207000382d030b8a00d084604c04540145101d000801842601d003000b4100030f441c801c00303082040b0b0050060700041c004019a204001c2d05100010024240351a1608402d02502d0120300300c0e61903004032214135440b02000d000300301e102c8074014400a0b40c188564620341c001d5410040001402902d46030856040020b81c2800001520402158203015990501d9900e154080c6104c0800740e81c16400040413071070343c41c2c6001e04004104a01c80d680150300c600c1c0c02d4100c0030301480140e0f40e0000300c0c07819015000002c4040d261600200c00050400d6090103480c02c45442110410280d080d81d10102c09075000c2d954400c2c0c0141e1141c0c18400009020300741842003c0d0190070503520200f00881040080300031504040380384400480c08004280040240d10100a443c060580782c6240c04580c0d00e80da108001c0c100303091017143c01c2911040c0811a41120040c002c40d2200b5543c03022141001ca10f01050418100d000384 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 493192967 1250 493191717 493191731
    0x60806101b03030519020f070f06020f0d0506040605031c03090f060507020d0e04020a0e01050304020a05061b1b0d020913081201080d0e010206130602120a0905150105030c01080702100f0f 82
    0x22103240300301d491000041200a080520a8603240c42001051802b165819801c01121860342c02e0380c0e01900c0aa031810001141601d01002884240c50b0150301480c000d0313028000244903082d40c240d1001c29103d0510740084e81018604002c2641c903036860001d0902c42c0b4003014840715540c04555500da141260304c40c941e290711070600340801c0303100d42880d06001a0010402907100d40c0700d0401503411030300040c89451a580c80d040001d04c103610500c8200c0d80300414410445003a070b003e2080101c00c29500801c0c1130050f645802013400381d41c1d0040c0003482803410000040e101401815214242900490956100e058007942160346210a024141c1d491161211920f202c912428407032840b60380c1030740a0400b035120802d01103080b00c5042012501e0503000e00c54030b1421100c0402c1c1c1c0b8400d2680c0000816130401a080590502690380309015504200000500094900091071030480c4002c2c68041d0300e80c2d4480c1c004030b06184401a1b0514002d06000911801e020a600303c1e00100da80d403103042041c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 493194217 1250 493192967 493193011
    0x10030213060e010c06051810020d0f02040f0e060111010906090c05040c0f1206030b0a0605091f0b1605010c0c050708071809050f032809060806101b030305 68
    0x140768803800607000500d45134200c40000d5a90b00441d400940c00001608106080d00156050036140c00c0c10548143d8046240b244224950241042c18910b640c011071400d41046141c080c842c074240140d0100319241008140e60b030344a41c20b103911910700e0310001c00610440e450180f01a03c80c071341e410740d44504061008165441c103071280b00c82d417501c0382e00d42003805140e1000580b00d420454020300001965448004041540d05010601c5001100e000060701d50800003000809a0043c2c10a24020002c0c10381d4807800111040000c00d031a422581240c0b140054940c2d42281101008003c01c02e50070485d6080c0c001740c0003208159114494010f6440203a11900002c1e554610340c82031440c0307403039400134810380045250700482c1642c0c000c4041d0752400300032103940e52456000c0691014020700a206da603080500c121a1000144a50300c0c10b10921451f0400090405001a000c5031142c005400940106409103080c10340c0e031061404a40005152400c0140c02880119490302c1f0102800c2000e604c4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 493195467 1250 493194217 493194227
    0xf03012909010c03050c0102070503030a050a02040509040b10050a08011b0f210908040e100803120c130510020307050123160e0a1814060a0b0703030b1003021306 71
    0x4522003800d200c50070301200324011560078450150680a01c50100245001c5c41e0080c002054107e025500950752814001207940c201c420041980140c1841880180310b640d40d8503100e01e4101d80c2004c1e1400d034545440400c0d102180d05075001e640e10140d880d80c00520101c064110958030f140a203110b200d0b007020303864140c418206a043c101e00103004d0042d14000c01218288120040c42050700001e04840b503551940d1081d40960040c8210b48641c8040003140b030385004078007024208400140d81400b006500f241715107100036040040d1034901180d80080c41d619000c41c0c00040c4001402c141c2c103520308241c040c0d00c0e0340c0041070503281942007041d502141006c200d48400c3c844071601c08060140c1e207400440350076041d00c034090820440c41050222443d035030110340c180580300e2701c0d0300d002141d0000c0300c40b041255400a002c0e4200841202040700d5560ba0f00c5002085440111030141e076000340340b804030010302c1c1c0c0b007d400c1d0b4001c0d41140310415555059028084c122082c9109185c05034550b00c0941e0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 493196717 1250 493195467 493195529
    0xa1202013c0c0206030907081204030c050909010b0409062301030503040e0709030f0b0123010f1202040527060a030b161b060507021b01091202030c060f0301 69
    0x418503200108122101c01e211200c10901d4150b281815105080c2e90000300036078010350310121941d004201c18040180c00740003410403001c0c80721610385801c1c6955104284a6018443c1500c1003054000003410488207402c41500c411000304100018a03480c5003103401031a01c1151a4511018000300c849000c440e1800320b03059980040c011070030681b512190044c01c4500900150421030040800000100001d4582d0700c03480c451526001c1720340c10300201322206c1d00c4205440078000c0b4400c003454540c2e60021207441485103149451107007982d406242802a20403070388101d82001086d000401e050403844070340305071021803001700012601d50380200302c0b000c001800090203040080000c180e142e044251078440c2182241015442c2c0f00b0510103400301030070b10706402d4442070f80b191b0810607060313810b100d60321420080700b8001c4044500800004c01a02607401209000317001203038000159681000340401d5104010429175403218901481c0140350028803c00c0010401c031400c1c51000b01066549036 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 493197967 1250 493196717 493196777
    0xd0e06180607020a0302181906031e030917071503110d020306030109020901080c01090509010b0417120403150507050a1b0c0e130c0b090a170c0a120201 67
    0x602620419010482030b90b01c0000c08a070f000407919800170051315030b4040d12191540b5903444598500c1c10b80506884100440d21442c02149420828000a802034030060703000340d4000c107104c04c000351518041d1003405698000039000b2001c01018003003950700142d130310155442d907940c20821500e1440305500765021040c22003441c0d101440542000c03001a40030710b17030140d0002c001041d00142500404c440d060280c201c40b030300350807104207801c0c2540c0002c400c40083c10180c03400a0158900080032a250069009410503911100400c11010900f000b6080b07110803031004043d0b071940c1e217182c0040d003c6201900c01c41c0700c40c00d2500040c00300e8060015038402509075101d9415451106078046116046442e040324400c45825001c01d244000b80703a418403030380c08005540d0b4060030a017818131104105074003440c9900d80401a840b01500d451004000311411070034203459952404030f100c0d0800450116294024401c1070001462603138214000f40c3c440e00070b898115602005890a00c3c030303104000e801c1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 493199217 1250 493197967 493197997
    0x240e010e01121b4104020a0507062c030301050306070c03020f07030b090106080c06071b0b0a050d0b040b01091a09040501030c060201180b0f0606070803090d0e06 71
    0x402800c40108190102c45204415241c403800044400010300c072456003188100c5940004c0c030b0741c02c080512900c101d42805a40d22070910b1011800c86220002448102074040c0d030b008102034801380d000b54269249958420f9060000140c1c0480700e920701d880c20031410303580ba94120402e002038400032003240e05940001e0040d0010303035a01c0c007040e0303201e01280c4800c40440c444d00303010302e406000c00e05c0300e140030f14855104a20785050034a80d103401c1d20085d80040b1043d801000c66415282c8e241004c407071145034007214040a0f8034011061101100e8240c0c0000055800007555800b120362106c0208140c09245608000801c41d40c0181300446014610380307030200e20045404d01c180c515800c140100d107400d0a0b160b615040c5900085001d0300e1007a4011102084e000205010b003c0d0280503400f020034010950300540e426a03190b1956901c0301800c0c20030002c200201146268840c1c90440d2440354000e2045560b80c10700030202e41c2d80d6015420150005202c14132060001e2902c44200c440c050300000705 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 493200467 1250 493199217 493199219
    0x150509010c0903051c1e0e0f0303090f040b041506020f1902090406050408090a0315140c03040609030e040c05030603011406010207030b090109060e07030606060912080913240e010e01 80
    0x4949040b01745038801d10044070111080d03100480341440c4e642e44581da440c08680000ca013400701c81903080b400b003032090308280b2050781c2039100d41001c20310586088401103610000f08010400500c0d042030644c180410200c4085002a000503403a01801c40200450f1030b91810540e001d80c80040380305e00254484414800300d00070900030b400803030b001800b800c1960714141540c0d0018003503d84a51041311800d440c0000d050148a03207115000300007100c05490011883c01e00480d4207540701c0204010100c50751100b071201030600c1049040c803101c1c4007a0080001d1a0040b070043e0254004413807840c032a41c01d191700c000740c2c40040e07803100c1d004207c1070700248899411075440d103900c1c04005000c4d6251350350f190840c0011400d203004000403200c00c6d0700506180750031030805105955081d08100240440120300300f06070b04ca11418014125008100261200c10309800505098451640c2e508141d080c40c2c940035440c620590680c414450745200300100301c0e664460085000024440c812042c0e2840c80 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 493201717 1250 493200467 493200493
    0x10507030806031608071a030105030c0d0602040905070c11010c020906010c020102190305130b031006030504060b1504150219110d05070f0504060501230d09150509010c090305 77
    0x400c0754101600405403000d4900191010003800410791150710300341e100f05404c00c039981070298660030702404640154078560404000c00d950788003c03080c0b640aa400f0348400303c1400380b0741c1d05540160900346400d000e50f0510b080000e00c10300011005441030441e020082550b58082c21100d0b50f0582d001d040f828440c0d8400005441c8000a200c0c240d040d4040c05410f42160111201407a82480c800e89425132914404070b5040000e400301e410404078031340100140091f40d980ba180840c116851403a0201c3e03540d5030f614144015103543c403101500a080b42d440c07070042c4003c080141c000daaa180120b299140348d1407030100c0c2e44040600451503100002e80c044030100b045030780c8400c00014040c244000044441d50f070303203240000c00e9001700d1041c5da04107010310443c41e00b4061140200302c24030b44804407000c4c0002c1080300c000e0f404615107200900040904141489403c490030407601702100110000c1900ca800d0040d000488085886505c1d08801c0e03030f00f8130301808180003a0707a00b002c0281480502d80e4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 493202967 1250 493201717 493201727
    0x10e0f01140c01021b1c0206130c081906050c0906040302060904231e070203031f0f03060209130501031707030c0605090d12020c0c0d0620180f01050703 67
    0x103507194603610402c00c54440782d00400d00043c040105441c10360010314600300541c1341480da900003040b0071960f82c84000a08039500080054003e4021070600794955014502014401200d0780440b02d24080d5440e65089040004921005640140818031242e81d40c0c003824505803081a5000c0d9122000380810302c094105480580800c580140000451140d42d43c198041100c04440d240c8111070391404010048a080c2040041922045d89465550500e5480039480703000041507940b030482c10b07650f650300800100744110003e2020710480c01040d5223b00342003019600c01100940502d200c10b800d010000450301c143e07030480b50014409182903440452803d00d6902c104000c0c0c00300109440384501044003481098080d02458000340811380740105e01600c4264440c54444aaa106002e00311f144031010075103504801c811107400388002103d2504900500c50f13035a991044a488035441c400d500d81d00b00041850001103000d00000a001204100c0b80d84960614240000c106012000c0013900071 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 493204217 1250 493202967 493202987
    0x7051b0f06010f09110f0f090117010807060315051008090a06020412021305070e010e0d1a072a02012d050a0e061e070213060f090605010e0f01 63
    0x49040d00d01103803001035914034003502a086140c800f400d0b060f0820241032540304160450f20004c56481c200748203280610501d010328420b50b00070410001d5503256503031042c603000b541c020a030071000315296107500100d552507075240291400700e03142c14030501d010601c0708400c1c1e084607030040c04500c240c80d40340ca0823901c2e5603018240c043d5600c070b2081c482c00080c1c2c150000d400a4000200042d60798902401005140200d9400320924145000d0038410005e80c00329484850003401c0c20b01040071424003000c9080704200b150068100031024068181c200503514840c0d000703030042daa900b03c010a490403d6000c1202c05803d1207810103800014000650140020360268024084400749205000349484418980c1e031a04000090001803c001e240750080c0710030804a05c00c0e40c08604102c0040c07000e2044c0c1814082940040030003150316001c540c0c03151900b42003cad113505018000d203651803401c81c54078045c501821000905194000ca2a940700340101413380c000181400710520303048006440d4a444 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 493205467 1250 493204217 493204267
    0x3050709020f120103050a0b010e250e120106140a1514091002010c03150803090d051c030c09050103110d09020a050406060509090105090906162f06010803030705 71
    0x801e2100ca00c03075003640301c6114025800354025100071f0603c3d207458a142401600614403100c00e240500a4182c04d00443c1d0f140e94000b180d0700c52402e1034400003070340c122002089242d48009642080c900310041900220101e9080c0c044800c103000140c4100541001035000ba140240503105c44a02d172035114410316030111011620503490302243c1e401003803001c0130072003400d40587e45500007065200d41c18802c401c0c41021916014000d41c0c144048591603111f80072125120300b000001090900105001315460514891824400c040400e080500503256900b00a00401d40e400030014241d4080d01529501c3c1e078009110501e41000c2600c014001d02000d20b0a0b0380103c030000001c101502c03140318120103000943c40301d5803181c8030b0b0000c02c00c88850503003119000d01c1000c803d010002d200091441c0d04561305d20600b5601c1e8110b94000c07510a1506150303240c152130403d1000803581d00c454450070016103110b085c1c40e180c0c0e0f00c80003c07aa980c07100342c03076a20015804201c225001c6500f004180c80c41d9103 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 493206717 1250 493205467 493205497
    0xb0306130807110616050f07060903140115030c14010f05040302011b050105190f1b0c0f020303040b0903010f0905060c09190806070210050708061e12160905010305070902 75
    0xc1e03c40115030250403085410046103408440401072100c01c0192002c0c8490305c60080c04220304264008000340342511000340010f4462061100b004429007017248207601000d0511b030419500c0c105290004107502c83c44080c059883c1e0010004d501c900c44e44540741c2c8040d100e00c1c1c505440c5500440b0701040103a00e20340141c1c820300242c00010340a004150007200d02210344030210b10010b11030740413100c490b801c0000e0a45000c040d104800d00ba20301a946259141c10b080600ca00d90b41440494000c00c3c1c4030080d81400b00103404241c0d401140702400910009400802540400c0c02101044400c1d510f40036003070303510010000b42c40441c420010701c400300300075103404400910140b0400440031150840d00180c2c111800300710b24980e04005a00401d040d0030828009401d01001c003901010020704054040c0e003801d9092881d81c1510400f54980d02c2c8041d14081c03400d40c1821210740c450084c1c1ea1000b08c2c0d2003001ea00000c1d80403190142d14140d94001c0090808185000d0f1000001e5011070208807403a4 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 493207967 1250 493206717 493206743
    0x12180102070f0501060609080a150c05070c0e01060306171b01140c010501140117060906010507050a03180503070b12180a0c0501081e04020f1c03120b0306130807 71
    0x3020501d282d06014450000032032044d08181010300409580c2d00580c030b00b40e100124100218a0a2070440b0124527100000506144001c2d82256140303c0c8000c00313480201180d00c00500d4800d4902c82174100e50a55808005d400d4a6031300742500c079582c0303099000305540124034000c1205060b03145e10070709180504050303041212042c40240075400080380f0401507550740c0c00402c03d21042e074908101d1104246003812041204112005400301c001d0095401040100c000440700d9005004980c9c91540000c02c5071850146443e000300f401401c4007021925071a100000200f9040010b00482500c9520741064240401d945a101040c0d100500e07146003c030f0f0242c006880400180a034449140c0100b00591102c0c1c2050000b5052041c060101080c011608079120003012a58145a4209904503046040000c02c03000061000604080c582e042e15101c954000c105038100030342040440381424284100b21822042503203030f0b44201d54660600c0c004206c0c84001426000040c14191f111743d1a1814035 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 493209217 1250 493207967 493207973
    0x1807030b0d05030304020f0303030601020d030c0e0a030b100b1602060f09040e48040906020c0d0201061502030703120608011404060b030a02130c02030c10201218010207 74
    0x21038803214003030b162a04000280000e509041c6d00d94080180e041c1e00451031800c010300000d5445418000d90410181d4940822003c944203c1d180921403d00500307101085445e41810303070407103805a03500341d4010104140001c18241c000c040e6065040b42014540e01c03c030240e000d002c4207074811555408100c00030090740806a031144902c1906050ba103009001c000640f410740c052440c42d61000301d40821083c40305980340041c0741d00c00c482d082c40325103092400c2c44180e0042006081183c500821050002c1010100da410001d6504180310085d07000303000b416600d0055803400100201ea22005820410140f000319020702900c1c00b20f613154880004060390b840c84520b007104c0454644110b031310141020310050000a0081c604419411005060152050f038001021010704d803c81c2c005c2182c940050000860007407054075002c511400c165504004c0d0003c0030401411581d20741c480400070748050400b0703a200501581c840305100b404a60302174462010791010b07a16580030a000c199001c1203002c0c00 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 493210467 1250 493209217 493209229
    0x90609030a03030209011b02030a0f08070609060b131104140d0b0c030106120e0c121504050f1614040f090213051006050f07140a120c0c0906051807030b 67
    0x1090b000b9903006868480c4800010040503c001c82040300e403007072214401c056540803030b100d07000390b81c8440d02c8101c1224078070b0405258002d040010345007600c1d00301e0040c1031002640020980c5c4104a8100d04410f181100303500c00c9803800d0082c410092401c2c0410700a4885403d0410310b41040286050074180d1030380d40c0c90482100031a20341c41c80c3e0a02200400190f030b08680c105649441c00704007440300d982d1a0759810359a0020944051140035007407643c03550000300307000c002d100040820301030b042460141042d0759140c035503c00e024518450040c2c0012007450200d41842607502010f0414000346040c4100300250a40001d181a095500e00c140c60040c0c1d220001c01e91a400c0c3c050003c640c0785095690341544440b5584030409021040156a164000ca1001c030340545030302c080545520004608035501d00001c511008018074400032405098540018003036100600c9003000702d603c2515101c040302541c0540c411031342c018502c010000403c00c800c0314815407101d140e2400003030b0f000c0d84d0400210 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 493211717 1250 493210467 493210483
    0x903110d020d090f05010503151f0815060a0906050a050f03071805190b0c0309030a081201050d0b0105010f0e060417010b0a050a0308030712021306030b090403050a0509060903 77
    0x4056070000e00d9004401d50045a04801000c003a41c00140c04d5180c600082c01520006012090721010071a44c4076060f55100c5118071010103248401121109141001d89141d8054808848000c500748076480c00d403902c8811035070000e50b640ea8a031121881d200c015250358211900e89401c0c40406e008041c903211101d00034500c500302554802c0d07020700d0031900001e00c00405810039400303042c1013041c4500c04914451071204458441c50110748c0d4103420010715040d0f0094081d62580341c01115030700340c14454820040c0c150700810703000c415142e980e41e40400c9100c04000800400e0b411817240100701940c014000c0f401051110b003020000300e0600b4000404590054000710f442105900c28010606000d10171851002001d0b240c6a9416040400081d00d820f003902c401030100b0703000000682414490700c461000c0b01c1880205540b28011900540000c003c54020040000d1900c1841c10007031502400c0140500d4150f1a21443c0c0110b17083d00310f03110b600c24908103030811020400045c040d2030400c0310392 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 493212967 1250 493211717 493211743
    0x301f150302030718291314010b0702060d050f010303110c010215070203120709090c052505030d05010306021b1c050904060b030a0e150c18040906021201060e03150109090311 76
    0xb190050320402c00052012006c0c0074010240f0f0200d42d81520725030002240c0c1501d050102c0d0540314141d902c0003d84502c91080503894481c10a0248110591131520050580703100303032940c142c20b800040170280c1d07410240e51110700680c0000c4262280190b224042a080401c0d441900d103409103541c0d2540000c00b0030ba5070100055202c0404100b0702a00d40b1500011481e00d1a0640c80c00224940c1502080400800e50300b804516071001020040100111000b800915074284907a680d02c0c20048000e403c44110020340002500c4d007019985004107071a402504d03411109009085196000c8806401449103150015510f800c0420b054002d04055445040b030000c01003641c40310007119a060a000c1c016204010518006110b00303c037180c425141100ca010400501038525603000502174010410050302d4188000740400c034010640541605071051612a10414401241419030310884250800c1c405141c00005001e07000560304100b00c014068540f0034940c0d480108598140040e540b494 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 493214217 1250 493212967 493213031
    0x81c0e06180a030e15040305060a0c1209080a080405010b0a030809040e1203070f090e0114010215061c0501090204021b0105010b030105301f150302030718 68
    0x18a030680d4a80c00141c00100242020400c996405030501d0140e00c0c00c0e1380f1480419a80404003903003070064030000c50304141100c6282c10148100d0004001081c5400000381900c0700e505c01a079883d01440a070385601c035241501d400c64551742190021001b900480e215500c4080c60010ba544e0010701c8000345000300b48050303071a241c5d50204012103020300900b80040c1c0104107009101004001035030b07404100c074100300c42030810400d0101c1d0840080e801c0154110110000894441e80401b0342c0c4250010a800302d803180d24541601543c1860122019580014034513030200f03040c2d29282f04082668410700020072010b03c540d0010b81030340c00c04083d903501034802c0e03110215011402d00032240140507070074250780f031541444080b8210390030a0041020805119000d945000741000c0f004c41c14190380c400744c4000c0030006c3c40d03d1024079081c18401d0155420a440d02e16a0060209110102c9a0041c01071640301d2a00406a01c030301c11683c0040703e6143e0f90594803144405402456540428503158 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 493215467 1250 493214217 493214221
    0x130506070f080a06030c0b131a07020306092a010903050d23030f0402010f021516090b13030f0203120d0f060e07021e0309130507020c100c081c0e06 65
    0xc210402c01010180620308103101000030890100048082c2d0340e10711042940c3d440c150610301024907240d4010b004090400e400384141451000140c007166100b1010b480b101d84542886c40c0d5103059000503041c9030280039059025a4005251071078000606061000056690391207050030207140b00d440d200404d0010028031503801200c2e2000d610180000040e0341582004c039511502d04100820090502a50859100b120b074020400d48070750903041807907020782d498100c50760810f85ca5540ca40c08041054403001048000d442e900761030281c2240e440f401403803440d40e21048001e9000c60016605401003034021010840004000c00c140100f048010598203801180b40701100c5841c0c0c012107010500740300303021044d903010405028041d01804a4050402c00700ca0385030441c881c220303003141e1192440203a0314851905130481849810700b41c00350b0f494401c0c05000c0c422400e4140e5410340004aa0a089000003481c40001e4140e0400c6041244020080119503904481001041c0800e9a2015007 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 493216717 1250 493215467 493215497
    0x2f06010906080703050a0f0c0308180108010609080316061d01090213020a0509040507051b0601080618150910060306092609120309060a1805010201020a050301050913050607 76
    0x7031000102281401000d44a142d07480351600c4144a00000349242d080744500402d0004041d6107002454114140350390b00e01d03410b02e10340340c0084074407180c174089101c40f80000381c454000c0c95100d086604880c003440c0b501100e00b2180400c6441c64034107c1d0516134131041c0e080205d0140c0d04000b01c0c40150320001584000c6801000001101100700c4648140104686400213501c542a94103a4006550200b0662101c50040e507903806002550078500306040c4580c0142c0e040054500e04070b0b0101001d030386850316415000203c00c0554403410080354000c4d0b03075180400c01e200d24550b501045200039034500d81524031100054035241d5000783c0da01c40d21020200c05003c0410700501c0c80d10100e041d2452011400598160540030380042244030b080c01c42100004040c0510486141c0c2c0002002e959480010303100c058180382c3d0200800785103440700c02c2d0228880d40144201c0700380884076110241160b01e0001007120380000140144000c44c038030034034580018010440c0302e002e400e80f82c486d980507455001d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 493217967 1250 493216717 493216721
    0x2120c0d1506050405130f0f0b1f0c02280303030c020d03060501020d05090d06050c0a08090f0304170f0a210201090c0b031f0e0411040b0906012f060109 67
    0x5549509400301c40c40030444107421100300c9048a000756040c05480b03400100b000001c100c49210f0140305400e010b8811071080c8641d01c240402a0210b401c480d400d03040d01402504c0010507003814000c0340c00b50042d0030161070300c4421010808102200c405043c111401711000c2451a81e00480c0443d440b03451a00c149901840494200303038891030108441490200003d6503400601c18840900200117101400d94854410b00d180c0243c0081d0203100c0ba007000140e9043d10750094645100050103440814040b1a010500c007031040a0000118241420510701900205403048141e00d60310032100707140603038041400480d0314580115002003640181045400c05030b80c1c2c031325400c0d045902d041c0c0f1040019900f8910001540c86030340340e01da12507803800500c0010f80700e02c09025500e80c407010303070020b80803009042c40c5101c1d0303100b00303d0b000d11080b4403011700040c2c070fa421145540c018828030000d030495201c0c100b5982c07490b00f01d1050300e840d201c424009926a02d0803020b00101a000360b001480703806554 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 493219217 1250 493217967 493217981
    0x80406080406060e041a071418030c0d110919050709170d0804140f030415020705060c0c040c02012408060105030a080d09110907020307020406080d0c060209030102120c0d 75
    0x10301c1c070b400f1342c5152a5a5518803100d9460f007015a080c0600c01248081d80300d945041c02640041c2941c1d6940e402c1c1086401e8400c0140d10490b12921a000d0f0711941030a2002000341700700da00640c5440a03807941001c111010400402d1184c1004416080b9400c01ea65030045071301500031500c5030040d081c249031044a18900d02940d000480d44841035100b44075a01c00c2c1750b2648690400c072031440c0c100d41366404509150f0601481103051002042c046858074000440152965840d003c540c25140d40d1001d004032406041900c04468100030081340030782c01c26400c10200c0b200c80b88000162050302488020121031820f82e1080518510f40313091200440030000759014210450080a010b015956440694402c3c1243c00c64034035140d40d480010024200c00c0030604c180c000342b100c0f2040c5031002c1c00a41e25000090705038031582c106040007880210100e60510b803100e41c0e0741d8500c84005140c4885000c0d5020300c0d40240c141d0f5082260030089403800701d00d50301514892400a945080c41f0003200b00750749003 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 493220467 1250 493219217 493219229
    0x12010b030a141302090a110a050316020a020a060e130515011211070f0305090406032d080f0a1202030702060106110106210f060e0709060e040804050f03070308040608040606 76
    0x10090612125040d03c0450b0341e003860703044540b001c032940d9030000400946000c8641c462080804983d03131196540060185103e903900348485615454491000c0b61384d821301c890046d4100101c94420312407070b880f41104031103910000d4500c44003045460201d00441d10304070b510030380d071502c8002214050760340051202c0510002010521400201c1120306c0311900c00c0c088006c016184d140c9610042500070820340e0301003100240200074180d980e08000742c01e42201950850b0764001ca841408100112084181b59181c10000117405d0440c1c050b00410b00303a10400301001800000d030740030107080d4450300040d44101600c3e4040d0070103502d0500050010100d40312800f43c582d050190a11191940f0302c1030380000b42054540554228041c1014001c52104250281c903850030400759040c41d0300001280c4080310b1200108221284da89c0c400310004040c1590010040740c8200301c1040145030104040400000007400c0d01d034500e41c7c80d900c420480d486580240040703085041040281303c141d1040a004084c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 493221717 1250 493220467 493220501
    0x201021308031b0c0f0609120607080612031c020f07020604080307110114030411180a0b1c111203040b03090a03080105040902030c0405091c02030c070807050105030711010212010b030a 81
    0x880020300844014204140944800b1a4041e00d564451541e140899502301c00e484450500e8180203152110407a0554025040440b0501e03008800208641d110002070b800000100a9540110003a512001d0382811641d800c0c09a0303400b60b6070b41300003003005040240046542d45503624255919105040005050001c4070409800354100c01045a030b02c80d0b4003060110250311a0030004580500d0449034954682d0043c1c03c010245040c0c0c0e100e03040d0480c04440c001a5001c5a0010615900400c83c3c0280407140365002440c1a04140e003c240340c2210410503030b030500c0c0e10303040b1a02c0745810403620300c5c80b20783c80314101740c05248d04203140324090842514248140122600820350302c0300c031000800d00480d030368400903880703030010720003070f000d82d84400c8001001c0704250f40000d40c3c9820640d440005402510b500059000e000242d8600300c440603164942140c2d03071180107552003001841442980d5408214441d0403400020120f400780c0300784140c0c41e48a0901d0900241190384044c5100c0083c5 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 493222967 1250 493221717 493221733
    0x31206030f0d0e04060308031603050c16170705031210090b09041101110105100303030f0203060a0b0708040305070f1503050c2703011b0807030b1305070201021308031b 74
    0x510041048880c102c410304156040350761000118005141c00da0024103255008014044240301e40070000744004220ba4041c0080d40340d030b1070003241e5803060038440c540206403c02014005000c40d42541040480800414140718013a2280c6003994031004280545c415807000f04400c803101d0b10340304005400c140104011035010000800c00018014201034100c4004220101e0b40740c0c401c92200a035040620004d11490500c15007046404110b80000c4002c24149000b03401240518400d03244920030080031103914a00d40040000f16a01400e4182d40c80c0c0c004201c04000329804001c0f4400a01a1a03a407026062030104c030311b41c0340118142110704240c108400d11041541c500150340ea225000e43c1c42e01c0c01c0301d294940780f024000001c1c402c00d425500342162112028281000f4107078100848e12084040e03501e08100310200c03480d03142a01d0388812a086d8100708503210340d10031603218242c2d000052505003904c0d6440207101c09584450780540c0009094010b0846e80290040d0800580c00104154 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 493224217 1250 493222967 493222993
    0xb01080d050711040b04150503010c05030f04030e0607060504120f0f08010b0a0908010f09060b101e1b050a020102070b1804020703090e0c07060c17240a0803120603 72
    0x103105403030001d00403ca0a583d40300d03840e5200da216420b2444011710412101a0200c448038501126100d004d10035403030000d0190815001e02d044030b11403104803101c510b03035584990701078400e0860580000e400880034401d1100190840c4110b50042d4000c1d080c0054022010000074410001c10b13006108005100901c1c0f00d4036900300c01828151030b0002c246540310000700000300c80c04181136101124960070a00e1812000009500011601e4066002440700341948028010401c00d9040d840c0e00041c551060100003a0440140d134400f07100b6458003c40c404101155019401c06105040d191904904801d504660b010003126009000d1010030901b4901024142c085511581c080940201c0d0001159410148070700c002c0d6000d003541d0b004003046820611112047c540202c2803c942d905d282408c01c0c42e60600510381242d0701e81e05c00455901d60b90711850058080d90401500d204010b84060000c2c515507111221140681002001580c40b10042d001c0100484006044103010f50400107626800d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 493225467 1250 493224217 493224227
    0x1050a150c0b090c060f0903010c0f0c030804061509020319051b030c0708130311040203010b0a030b1807020c01020c153a090201022a1302040806040309030b01080d 72
    0x45800c8411010b059031550000c6081000c1c21440030383c040ca0020305080f000c10484080c3c98075580c00d80003000a5aa508000d8892844655214020034255540800000d10405a0300e5010f4411040801c800303980c81005a814851a0000c000c80354000c000c124000c0010318039a4000d41c04860244480e0501c0c086004a07403580f00c1090202c03800003c0000d10750500e10701107485840d40140225500e034078401c0c4a501c81d10280c0021039030b8040a00d02c9605502e8603009881c182e40c0c102c0c0c8010b2418000007001c0d8024403008515a400c045119000c0c0c8c101518101e040388120718a40240a0070070120000a040c10400104680304020207160044444002402d682c40800b8030390b08210001090494104072000610795180e40703200c2814008207081c4180c00c0040741c10700c03c0c1c085030189204100c03040d4074a100d0f034801091454855618590b1481c103070a03003003003036039215070014030703058554076050301305142100c041c0d000ca032085100b0400c100715009180e004240140c05800c0714031a03500020300c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 493226717 1250 493225467 493225487
    0x1212010e07090b0f2a01051009020406050f07110a150e1804020409081b030403030801090b130b01051c14160f08070905100809010c0e0f060c0102160b01050a15 70
    0x30241c0d00401d068545d48036640c9420b040d0201040500034040580b051316018040c01c03100300821140b80702e00000c00340350900a540548480352680d604241940c42243c1142d008100f00b56100041404841d103541c850b00016000b506c3c0400590100b46890032015000c005c040d0740841c0528032030650001010070b9079030420342003030b030448000c1011800341c04c1402d424010501840c28018052510b80300d00b0100200a200305d92003525182d00e2684c0e030301c0350710302242c09401401d5004a054032906481c0805580101030b0664141059400c0c06a0340b4801c0303261414075a85104c4180d590400740c0c3c2d801302c410000651050400d107d411411002c860000d00700158070710351006101c410404611402d000b8107000000c4c0c440a004015400f50000300140880000c4e90f030030050354070b00180e82c20824814000c5c00c000349000360159040082102c03c0c02410740c40509601c4c5903550a010b107110b034040f8003501e41030340f6000c0d0b40030790555410a0100f19000403980d0203005211821481071200325000f6100320 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 493227967 1250 493226717 493226737
    0x30203040b030a060b0301121b08060f0903130609090b0402041a070c03140c011d01052a010219030501050409200d12050d32091212010e07090b 63
    0x50380b26240d4003000c00203401942c1110364010401306c00810141004c000c20817500307001c0c6a0200151503041c2c4584100351107400341038138641040001802e40442c0b080ad44d41c000c0b07104000c5900e05106858103900b9149239410600005521000801a00f00280900c110100d01110304628ac1880c1400070710602c00c06468980543c00301183d80014081d80c1d4a141004640200e0080b4102c460314010580340c2c00011101800304104100440c1b0b50942203946c803000a1060311a0b42c41c12007412120761305035a4200c210b15070102700d07401e000d0008000380050701201001100b100c1000380c81d14000740507954160081c4e0300441c0b50210100c04205607030701c07103408001e82c5464a01803800d0301001c10318011a0040c083e0164050030302882c00242d0000c010441982c04110400c20031000711040f09403160200f100c0d011007141041d09143c100a44085146c10a42940885800c4611829150495080b010349403c0101e92100100030301c44440300410b60000d01850010318007820810354800c00e0052001e12 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 493229217 1250 493227967 493227989
    0x2130c020309010f03020c01050703090605100506040915050a0b03011a1201121506140414060f10090f03030f0801050102010c020d1416060923030a0305060f0915090601020a03020304 80
    0x1380309a41c0a681182c00520041009201da4a00b0000281c098900e441d0300b00d840c1460240000d00c4000c02a032170005071840240a01c2c64540340080b414040e1441291004074441d601500040e642d996540001c000c09404c50301c180c4a625014062401030129041480205c0f420060001141c0c2c40d520080d05542c200b40c01703143c03112512300b4040718104008001c04a400d15016010540c042c0c0c0b01b96025003004111000c2c01041142c020340310308035106441d030170340120034042d03042c105c0e02d4551841100c00f2154541040140e03a10b045017183c907803440d44240c003c5110000c10840050b400810310740034007400c0c0000c1c007810244800003503a1751880c410f402c08020b240c0340c0d6040d50311628012500c0700c0d8190302180104107218100000101041d000803600440c3c01c00c0e00c1610341034190030162484101c2c07030240d4203200b80c510b0180c000c2c1c4001004140c1c040d0840007164515551109120301480000c4407092003d07002c0410b00c01901400741900b13040d076001030052000254000221020380b084a004 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 493230467 1250 493229217 493229237
    0x20124060c080d0c0801080f030906030f1803180406150507140309060c01020c010b0102010b09010e0a2c0d09050a2904170c0604120620031302130c02030901 69
    0x200c2242401000324000140d803c1004109640d0345c40300d0028180c69015041d0366160998031151692032051686594011809000044440072899280c542c00058106607108805400043e6400c40c0c5c0255401c005400072031802d0541d5040500c1094041c06035070b000404601e0101d50080c0641c000d0303070001411244e1803410780410700014002d440400c00c000c0c00740c94070b4038182190f49010303401c40720541c0d01942ca4221418042e41c81401000300c0a40c000c0d10f00100790b420b0181c10514240300500703208005844540740e420030031900111420030310307600480c1c03a60f010072403014908005844440c81c080140c400001d000d10342d03843c3c02c00f41c215040c501c00780d0400544075801c074120785106040c02311040c0740071600140c00503401003820004c003104002d8444400710b81e400c0000300d0150380507100e111100205e004000601d5076001d4852010840602064100360703003d501810380c0300b299003030304801143c130701c5400b1424000060880c0042c07030701d024014000d140030002e640c1d00407042c83d14100020005 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 493231717 1250 493230467 493230473
    0x30509120d0e100c020f1606080c131805150108070f030902150c0703121809020703020a140c031002070b06010c021f0e09070c0c090b18010e07020124060c 68
    0x3a2031480c20103c0140081e00d400d15020703440f1690214003480c00c0c040c03142030800c3e02d410650040d085da805038460102d00e49440d024201c01d90080780220210b24600d100104004420054015076110032101c04645803510842c46041c50035000d400c0d6040c001c809092002145d0031860320304070107800d03150000c0c94050600000d017241008008451002400003190802c0c0400070a549095034001d0a100302825540c090480d401421005003e2074021171046c24000c20040307800502d0900d00901c100e401c1801c0940700e2a03420b10320000204e14943c4842c6a07601d96007400d0028880003440d4030011414803c0a03121000400e40c000c00305410040d101d00c140c411541c0c0c240389510980701c45c2c41404208000410042c1c81d0380000d50990b803140c1011000242c100d4490020036070b20540c131004105215181c20030550160280043c0d40c2d9001c00100e000c480322050301b0090710300074010034004901d2810303c1030001c0e08407041007c40a2020b0068004000d01415160300c560456020f440d1400290744181 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 493232967 1250 493231717 493231723
    0x3110a08040b090c090a0c080105010815040c030204150f1b1703060a1706040506250f05190306031a1611030d09060504030f080915041e12030509120d0e 67
    0x11005580c0a02181c0c244021b43c0c400340e000c042c4a0245864415181e41c0700c400540d40610101c40e40e10026484010400003410036030010b000220150034003504260710f9003080e2003031f0044401c4100c001500540c80130f1400e90301c42c514150030084003004040070384043d140d2080b40d41405078041e503002000030205404d610ba01c0301a50041100c44200082180f00a030440d4403a00c0a46040c0e82510421021524002d20303032420380450a0501c00221030041c000340d0035215281c03994005000c2c040144514541d5044580340107003d80d41d03540c0c000402d107042d41b0f030904106d10700001f80c143c030100c0842080081c44d00d100411802403000e0411400e07030101b05040303600d075200b181850b0550340c1c03d000c107602c1000581d80025020301d10944461002e040012000c842c80a0100c801d003005600400801e0b1103120040e01c0b080c2c0042c00f031070f040d80b80c1c024040700344181000c00500441d00380403401003421049601d4401d80390408080006460480c1d030346059244e1500035100011425680c810628158107c20 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 493234217 1250 493232967 493232983
    0x512100c030c020a110a0e010308030406060608150103090501060503030c160b0901021e19060c0e0103050403080a0e0a0b1f090b0d11040f0914010c0504050d24110a03110a08040b09 79
    0x6071800c074407c1c4d0786a203400c05a0790019035085988504111001c031b0f4907030084c403000b44114400240b8a4a0070640d100440151402100c00d0f1441d56807002c021696403400e200900d05a60484020710031003020400e1118584130507807000319039410500140d003c036a400304130810703104020091144000d112038650b6082040395050b84610420704080041040440d07085200800d1054680007440c4d0004001034050ba0012580200041c80f41350008aa010071030707100d005400000e00403100d82c09c049076124000c240302130711207003110b102c2401400034607500382091402410069006004052150003c00c00c07804440600a15503564000c524500d6140c5030310441d8400f011200501000406081480ca40909117107800019402c010300048841d01517411602216009000780000c9039a5480d002200754400c00c401e1541d940394050488035074030500888090400f92b00a080d6602030300381020b02124007249070360f01c2400007400454955500404255807007904103034440c61079502c54103010308107a08 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 493235467 1250 493234217 493234229
    0x8090709051003030f0309020d0b0c0f07081905040806010905221a011719032f100501030510050402031e010b040e03190c06060512100c030c020a110a 66
    0x80d200401031282d110811107800c4078000d45034402c000c441e0410490581d00030480107500994440e80f0b01c80051255803206034003131b02c114101410484011801900c80d80320b003c090720b21038004141c940510100140c2c100e401540f50a0062506190021464031081e0510503080c155035254000341001c9441e0107403c1398100c22404940e070354199464020600c1494480c9241d0410101d40041000c000b0030820800c1b400a0340c00810070501c00c40c41803182003480590071010407580c14900207440c000700080e120b920199005000c01054070b01c0c40586031000611080710a20308100040010940115400752200707100100031455560768004213241200781c101038000c12442000092805906502403000440100c0c0d052044101c20851299603018201011600075000c031f07031a074850f074001c0c2031010036280708080c0426a50380e540cdc0001c040c0404071441882603041444146481c01942c450310980c0c85141c10300300061000c5083c02541c0b004e00042c0203200041d00400300d0307440d9030340039000001001 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 493236717 1250 493235467 493235471
    0x209010603020c060604110d051e10030501051609210510020d0501080f0c010f09080313080c030a051e0a060222081b01080c0910110705090903040608090709 69
    0x6500ca000400942c00030040c034229000d10b5000c80e10910f014086c518114220500c0d6600341682c0175200c800400019040740b082d4002c107a001c0781c00010300038566200741c45a0500e441200e00c0d500b0708500752580101180f50000940c07683c100c4407070308084240d0540d29103100080203440092520081c01181f90701c0a40f4901c01e48003000700c009180c2c1c004004460b0350003410302c260390b80e40b000aa80c032140708005054a4009a03081e5419522807032a101045803540b07031040b61903a403808207500b19448108404000c1410300c5040c0b002420400c4400c06075801600180740d1004680c4a0540322000b9010950002581c2000440c0003502001401c400075080581150b1300c5400e0f030b40003d101d10a001c0b040b007805180c808005681d010100722050260b10800e4820001e110341c5004669442004080d1a5032040a0280c5c2800b6114820303403005c031452546800310034111002c1b00310310f031407107650007240300c5c00c004801c0282c43c60022003503400325031060601c6001c0b516078904940c107040d016000007000034 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 493237967 1250 493236717 493236719
    0x30f0f230c011407021e0a12060b01030c051e0d0905010513020102061608130c0e0a06030b01050402040303024603030f02030610201b0306070318030f02010603020901 73
    0x215010070451280c550980350504500301c1803403940001e0040c2407010707601c55545544c80910400c1e02030400043c0d88000c2451540e1900e5600a0742030f10421007044d0b031561b42d00c20300e080c00303540c051290300120302c441d003071242c106240c5c64200206502c041c101e80160b400085007211800440c3d03082480f00a42c00300003445a803502c401031801d00300300080c060340188108404a01b006a03021030701242c2070159500c64059035910181d41760004038aa00880b803002c01c04c240003408112400c0c0150184164400100702e2030701c1c50030050240c4406130405e070320484c41040b042000a4002410480c1c102c01c0f180807880742c035041d0061a0301030310040701307a400808400c11010040c031840c45c80c100d05284030303172400c00c0392500e041c1c604401c038002110829000311041e9540301807a802207070400c01e150701212001040580c03c809160814080d40501000c8046202e072514551134240b00a90703110805203010410b01030301901d0400184071481002c0d090000450212084600c01e4202c0c5c0f02030341d000742c05240c00b5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 493239217 1250 493237967 493238033
    0x30402130c09270b180a0506030307170307030e0118060b06040b04060c050d0f08041410060b070311010e0a03120e0a08030624032701110a021501030f0f 67
    0x100781d01c02d814039106181c4404180c0d1860a43c1444c90007417a110100351043c0c0c0c0308510710000f0403002e000c8070b40c0b52000740404000100480d201e0481c00309500f601a8403801c20b0100903094810060f42900b01d41d0400044060007400b15800c1111b10b6009400800c1d0040001c0105d00070f403085403c0380702074840004000c41d902d80c00140e480c44241c8103804640d05000072640c100d8104070750031458400205072201041c003041c8a8030101300c8207010001625004412035080108868040d407041d0714044001c9003e00038103400c0383e124038240b90000028080761142c1e11107640ca4421243d8014180403034642074042c0c1d40c003180d0001c124005001c00316040c54025090400954000304e81091007482e181400c200400c200007420505401c0b40e132141d504507264102c00e06581188501442509000c421016403016024010820b100c9207040083e0b075140d4500d207009041c4503010b1851000c40400d2401000018491030b820341045400c864608807604a51912910b601c81c603c1e804c08013030200c3c506103014 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 493240467 1250 493239217 493239269
    0xd050309030d030608030414040f1d0c04051006180308070302060a0e01090c0303110a170a0311130b0a050c010c03060503070503191511070f031202030402130c09 71
    0x6046401c034100e40010242c1501107050300c020703000b01129500f00740001c02600e4000030501c516400700820220301c82d04c6030f1044004a4040002c0c080e20002111170a042d040018440c803101c40c80150b034284a0b138500384811030204509072080c40e0030005444000308042500c3c0909070091503105a0140d0b0710200c604000307607a00c0055900c190070918001e080584508144901d0180d180e0100e03510b600c080c0b5540b42035820300d8240110040074056014a00d0000c3e483c512941694881020f4840d11081c50b100001d0445160143c3d014500d801042009107030990003034171000722071215002954442140700101c802e4000d408000710302b0342c00d084046100c580c042d00100b0603504c00350100c070040e95440080503910041e080340034802004c41800b090204410000403400a0000c000c04580c80101d480c903808580d08c0000183c80005400500c002059880444815100c12031b4406506604040d0001917200300040350346a0034699038820340d58114019000c0387c0050508103d07200200190a0582503 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 493241717 1250 493240467 493240477
    0xf03050303160c022d060703020f1203060102070e25020c0411040b1b0a0506010e072c010507030e0303030a0c03050a02070f12111e010515031f0b0d0503 67
    0x3081e420b020858505282c4100e09a40e07086400505102808520003050720309034400d5074002484240d2225140e540f41c94100003081602d209030300400720100c5005050381020282c00005002c40c00c1042801840c2e03038000303085001c3c0c070720ba0b00c018092074640000400c3d4204807080f00e904c520708400846004548c0109109014190695042c40030303034681d0500c02080d11441c00340e6000440140f0100000b00107080072040764002d0201121742c41012600c1d82481e242c000d80c082c030b00310200b61042003e12940a107200482e40011004a1040303580c0001c02d0070001001e540c014100800400c1110525101e500d80c6182c080300038082e40d0f07803820f014800b80040c190450000001c03e041a004c038450703481c00d1084074241d50f00942d20b04d1140b4036030340d6940e000040c0c0c2e81d58842080504408407010100c2407080c4a04030280c002c0310b0261300c070114041401c0d140010503003111800d00d030a0007100703620081052a01c0c031080041111098103203070358503002030101801c42900940103107201001c00c000007000304 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 493242967 1250 493241717 493241731
    0x509090a020301060620210d0204090f0213080601061e0e150301081203010f1406191e020c10050306120f01150e0106050703080a0f02070f06110a08130201090f03050303 74
    0x1051210040006547c0d40314400c260564690101c102c40403103040802c040c09441044100141ca0141e0710585c0302c0503141c09e0340c0d403006d0503940020b00e81c190b000642d400500030f2800c0c8018040030b600d021005000003042c1c0700b65986a506000e00c041c109841554050110007001703121180341c056070f40c1005c40940090084a00c00d201d155010184d14a900c42960b04941440c605503001505001440d54000d500400481e048141440801c2080e942001407501c5101c040d41c4648811041d00c01505001100d075000800359082501c2a86482e204c51800340e40e03010042c10040d5583c0c9896001c17170001552070b601824036020320907500b00000b1064104498400c01d840c209000c1c19115031341c004034010207110754408200b00b00100300000313000f8208180d00280c04040007400e0901e2458583c04e03070384a074100729030480c8070040c100c01b002400c1c8640c0f2102041180d003c0e0600611040140010a002d40460381c0302c15148089011a0f120f250407070050501498465840d981c0c0e0716045540b0340013500c40e9 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 493244217 1250 493242967 493243007
    0xd06030b0703020c0a14031902010c18030206071b05030109051608070e0406051f090b041103060105042601150e070c080712141b061806010509090a0203010606 70
    0x101d22101c1c828004d603204000ca001c0505032281569407150346400b1290900000d41c04140281c6400302c2400e1011080000c40350000b1800e11030520004104009104164035082803013401840982c42c0c22080c1c40d404c40c3d00c41c2012695010b0840c2c007021a41144c0d00141c1d1542c00d05058008010000c0307902070601c003501d042048d0481e121083c05449030083d0248071494035070b0707e0000780451078981009030000c4e52694030381061090a00c001d04841c0e503d4101d1140b15440d03035644003290800d4414000c507070b10324883c17080c01c50500c030740000e0051290f8442c05041d18075071084400381c003100800282a107040f1070001c000c4821005100704503605544aa9640d04a01c00c0004a80034003440040c080544c2c00b05180b4a0030101d6a11625214070411040c41084001c5031a002143c4600c001000c01011f81641c03044245612900d0311702d070106c002c0914504004104580321102d0000440700d041d0b950450355007420b580e50800452a01c801020003a60641c00c110000602a410040da100003003849109 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 493245467 1250 493244217 493244221
    0x2100509090a0902010c03050f0721080709140f0f090a1d0309010c0210031d1b0301020c030a030c14040b1c050411010e0105040905010902090907020703030c080702010c06020d06030b 80
    0x20007421591140f078080d020800008040001a100d203006000920031f210300c9900b041d03120b85458040e140302805054001c902550b061140310f03000b110942d4080e540b880c2030f5281c3c40c204a02000d07030303091004010340680b0740751600d0344040c0e40e500c0a0030518100501010303118945440840f020300100507414104014412030030302c0b1f118010040705d07000d20068440d8205108c036071707003400b80c01c40c56411042c0801d5038864140007030342c1c03803192201303034800b020401001604604101c1c08000010421018800d0784100309041c0800804801e8542003001070a0028160182200517617581507075441da01c504440008000c10000305000c050704071601c08c500b5007000d580441399058200d420541d400f400700d030a40500c400181d0b100e803900c1c1c443e500e4113141c524140f81d40c0b4050101607a10030780004c0304058012a81881e03501b0000c108a610022500c02400007503e141c50281c000824a40c0c042c102880c005a450b0540e406541c550203c145d000c603085640f90a41c51340c850082c601030104560316628080 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 493246717 1250 493245467 493245481
    0xe19030e030f060c030c090904030c050609010612060e07050d060e150c07110609130203160206060603040b13021e0406060e06040905090a1e03110a0c06050706090210050909 76
    0x69030b000300b00420310061180b9102c11070340042d90f4000804136403c1100800100000d621001200c50249110b40c440c50945402c92034018207100c2c009080702d005a140040030890742c0c8800c06103101c81c6410090000d000101040320074145100c5820054220580940c15410040a50f0003d08480031160507500c80c0b122800014410001c20342ccc48040c000742c28050000814452031541d12141d030000d1100d85020321000c003180031070402c0202c2811603503001c4108a60207030304100907064600148003a24003072030711000189a80c0406000a010781d4040c6002800101f111140c0c040f80ca9001801e00d0341101c1200c00c1c0481c2c03e0032205010f40240d050400002d10b59004034805402100000c0c813803818941410040310052400038000c4660b031041003002c0c80880c45103204014600d12a503074480b2440503d080203442e042c010003013490240c1c0000d9400020450000319001a0f4003540340a0b6640c07c0700c1d060110141010000c080e5101c5280c0a8004120760050010651003106903506065550307206 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 493247967 1250 493246717 493246723
    0x21b06041505070e10120606030f0e060609180c3105010b041e0e090d090b09060a0c0327061407020310150f0e0f060402070f0206030a0e19030e03 64
    0x2c0c8240c00030802041c40144249044060300e54171411134900340c4480f899100e0080c040c1d40e1140c1c010700100e40c1d07666140d007500000b8040c0b0400c1e0024140200200c5c1808408100c11039001014900500001c8400400c4018140182040c1002c000e0071000c035030310036007440c0030614030040d810f02c5694002030300d0070707010700141c002d1a0403100200c06090924ac5007505050014000500d0420150650040416407851800820f801107044400034038030240944009000b04a0942200c29460000d01c42e1905070364681084075a10501c03031610061004c914602503a480c507401d05d00791014400013412503d0204202e8510040b00c500390399001c070000420100008a10414001a40641190020340c1c0c030300c0031580000c842120131900404819550b1142c184c1c82000640041580c03031410b07001c0c4811030908140590b001a000c56045141100740c0c0d0340c4200c038042010000340074007004000100c80310001d62050380d02180d030030144c07200d4400c02000f25490023842d1030708501151110341c4212082c2800 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 493249217 1250 493247967 493247971
    0x3010914130507030201120b04151d0432100e070b0f071e02030d0305060a050a0b0d050a1107030809070603020a140f1e090a050405060f040f021b06041505 68
    0x1140c00391951030f0445d00112100c140340b0540300d14082d01c4142c030a20303e0700d40f48100e81c4c41c9880e04d804d0000c0c5a041c4122061a401450414040c490200d411302010912441460300098103121034907402c0c501d9940310002c40300c8403c40c130070420f0203880e4180e60391400c00e4100880020740311080d108641d80f5043d5280640c011401e0310402818140040c0300007845061490110343e10440384840c02054640c0001d00d444e003914078000c0042d49440a1181604203281c035000030340400c641e031604c210f06040e10341005016001000310650b0325080030905000ca65070103a41c14560144240d070703980c0030070f003000340c1001030980d0041007034440c403072000505e41e21038822741e0b0300c00c078540d50f43c03d8058141d0044903019400034000d00c41070341c400304000341007110401078221408208800c8241c940545004000420940ea8803503805a818139007084220394808850310141682180e0000d0000070b184103c6000b400360f40628003903214078030701c0394000d030b600041e00c5031041e03115800c61b000c003d0300c08800c4416941d007 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 493250467 1250 493249217 493249223
    0x20a08121605160305070602070b0304030c0303020d1d03040f1202010f080c090a031a06011e0302070309050a120209070519050904150b090f06070807260301091413 72
    0xc2030041000d505001c0030407051a41c081c00440c0c0705095004074500b85000e40754011121940019070401500d0b406000030f00043c2070042c0321504501d0207840180640d078800c1d02c01003c260307000445e074000e14079980c04440c01c0013000c0c2c001141985a1032415503a6486405480b0b02c403240c0c1c02c800142d6201003043c00604035410395130120101a127100c04d55910001a10340302c400c0900344147c2d0a961607180343c0e0801140501076100a41700101d00e03425180340c1c040d00c15410000c9070000d85a8044012403e00d02d00240c078035006035502e110b42400c4030190840d40005920540b401d01c00200200107840a1000340d0080b140ca24558456550644180c820385003101407021400080c1081c890003100900741c02c417005040400c07109181d1620340141c12860300000f05105d00070480320690305116a40442a0005440d064a80301c8141c40310741480c00307840001003048100004c44400790364501e01200521320209201c0e40c0b2540c50700405000741904002030713104602e11100203002c0c0410901e01c0040513030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 493251717 1250 493250467 493250503
    0x6030b0306061e13051609080303071e11031209010b09090604020d140102130602122d0f0c1f06060c060b01030e150a0e0c03060115090509070c020a08 66
    0x820b03000d8003c410410309079204924041101c4038005600543e4803d43c424050407800999003600035051104a800055440e441170003009455a000380c07100d5188200d030681000400c0201004541024000d1804003590002040c92034241c0400ca070f07000d0003007500f4002407000340516000e02c01081d404440d8013125510107030115015042070306003600e400380596144611080001c2040d400e99220060f0302c1c4044002c420200100e560500810440031600b04600385403100c04e200c0501002c05506034420b03003900071000d440d4007402200c01c46000c50a0200c0381621100c0852240740c464882400e004c40020400c496002c915105202e240c0c140d80c26511070188402031621440002c0c0100c07103440c0e050598542c04007040d580d040000720718403600e80122100e103181c042c809009444402c030f48040b042d48014010b0750aa0b0b0082809419100d420008070b0800700c03030a030b0442c1d003540f136130b482290080c0c604020300120a0340305410b25851402902c0b6200c105035603042d001da50300300241a07003109036 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 493252967 1250 493251717 493251739
    0xf0d0305032e0315090b0c09030607110304032907172203030c0306170309120d170703110d05060f090c0d020d022a21031b0d0c020706030b030606 64
    0x800e620088200010000b000141644041d42d80680181c030680e03584d5031f00355010410014501d03081095a6000406186c000d8121414505a40c2d4034000d81c040200740e100205640e1042400c401c0705d022000d5150a181c080c1403c2088014005140e80390f10390f5103000c51100060002d11900c0524020b02090020040d0b901c00b032034030210018216481c0700010076442d41c1c8000303401e0f01313118410b0322202080000366941d20340c103c082241c250100610660550000110040226045060f100700010640c0041e00c6d6503803808422401404817500d8080610300c0815132030510b01c90f55002a100700c80c21344401080790f80010422820f0081203c1001d086541000650b00b04026600070340503101d01c09078054181104d00c440034550452481c0014195203109550800715079042200000d0010650540c411700c40c0072108c0c0310b18510000700b500186180c512082100c403e4044110380c0015081d4004210102c4402402515107043d03104903030009080188080300d91130040361880c06144028910700400c = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 493254217 1250 493252967 493252973
    0xa0b07050d0e100c1701030c030201051e0315012007061d0d110405100e010608310c0602011109150c07030602040e07050a050a0e0f0d0305032e03 64
    0x1580c481c21400850a88444944210510401c06814100b840da040403801213070801c0001c010400c41c50140688800c44801000418403182074031007602c0c4c080c80c11079601d4808502d148141d200840c80b4207a045030000400180c1c101812100400000903601c40070000c81c030341c0c146d044000c1a03100c250b9150300850301c1002001e00034028020941802e581c9456200701042c0007482c06c11042070b0030303074912003c0d10b1134684924040c410503900c0341441980501250030681d0790b0740c0f5140305020b13802c10302c41110080303504400140c0401d281e40c000054034180840c0000400342009a9008041f82c07600340b034490105d441801805009000080c0130f024500706150344080202c40b072820000320065070300070440316816000a000001c05140500301c050b03a21032400107181c40c3d81c0c00040c02e00040043c14082603108a030b011089440144203464030030f80c217000000c0052503c000400d5590352040200030901c00f00f64008001e503209807101c000c903c18983e003885034a0000e5001d0a81c540e00286000424800 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 493255467 1250 493254217 493254227
    0xf0304020f220c1e050c0c0604030314071b14040506040204080a1104020d0c11150103020d240c0e0901090905060708070e03030403061d161205120a030b01110a0b07 72
    0x20107009240c1100d2596030020b44241d06024001c1003130000310001007110407608104588504581b042c1c800600c1c0905c0c5850041841d20782e0b0051203005d1000245103418411011042805285130f00c600c160381a039100c502c020b0602500700054042c0e410400052410f02e003600c00da6084464031005022100d61a40c2c0302002039000d450b4066100d070b42400340301690320952113140828002e40c0c072a038246050441d5038914004138241c407080030150800040c0016115404404403080e4414006070740c400030881d43d011030340701030b0800400e07592510000032050f030703400449c02c0204c030000da07543e05aa98841d80354900b0380b5014400038000e0380c01030001c03034109803148000320360000c4c981c039007503510b406c190b00043c0c29035105510640701c0c0c0e501c2c1c0450341c0020b0100102c0e981d140703200c4d9008114584061080340c481c50007a114141d892110140b0b94011300034107002c8043c4240b041c2c5410b582d05c00c414030014000341415000c40780010301314014080300820018002c6c95064022a00d8159030b43c88001c2112 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 493256717 1250 493255467 493255481
    0x60a09080927010806071e0509090702030d2d060b0703050901180803041a03060307050f040f061d160206060603040c170f06070504050d06110405060f0304020f22 71
    0x201801c8000c01402d02c00c0140000c2406090142d01070031443c208040010f0070040c84841e620046251a0850b03c241d0303800104a40c40ca4034181c0701038041340d45d00321069042d801000d0401a0709810000d4920120819280440b00180c03440f10f00030464003800c48060407242c1501030070955280c10801d4402180c0140d001e046da590051400007003010700d50b60f510341550900d5009803242e510109091024580c500c03030709003a40d012a03221500b10300d017041c0020399682c064402d80e03005242a1017860495200ea40040c0e034140c085850138090f150340e031200360b040150074500540745401c001000c92801100000407980741540c0d50300810341a140d030001c202c559480900b0848500f1080c40c400111804100b10086030040c911014003110151307000927500301000240800d0030000c2c200300c14010f95403200c050b5819580c000000044503a1a01c1c02e02840b8811500030b1a44294081841603400c038066004520680c42903d4281e5800f644009010701111866000c14441a01c140e040300324050940c4545 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 493257967 1250 493256717 493256749
    0xc10050402120f0106030201031a0127090614040605060304030f080c04120f02010801141309060f1d01060803030408030420100203040509010b030903030f101805040302060a090809 79
    0x46203481da0200300c2d0386401424032020000740d459000420a56800d481449910303540f10340c1c47c124000c102c0000a008090740c108070f40c0e400c0441036048820749140400074002d005140c00400003541c03a1010543c0c444030700c001d40c0e44a00e0a1000100750350408000b41d034050360303068441d021401c3c0c021000b80c60b45040248803c900d04403d000004280c0d00c50000501e8190081940420800d1240001004510141c100e04003041060300000303d81e03241c1070503a44490101c0800020000024940704019018000d40c4010b05400e01d203a040a10412822051820003507100802020f0341d500c00075502c070300088a010f8403291080c000100131030004840844c04103219030340c0d07030405c91480000a008000552542c3e0040c0c2c0085428401800c01e03d000c2c0b0f0261a010400a007186005001230f592417100900c1030200310046008034002c0074a1205200c003501c141c80d4664100b102d00e0714400e004141c212002e41c01480754401003110140039210343d801c1641c0007480f46203091401c41c00d00490003100c84001c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 493259217 1250 493257967 493257979
    0xc0c0f0e1b210a0b0f010e0d06020d0e0f0d09080a02100509041104090c09080d030c09170303040b0a0c0e010f050f070819110a02091b03041b0b0c10050402 68
    0x10202200220b540d1402c0c0441c01080720405003000c0710b042084900214140740218446100100c03140c0e005001c65214000485035a44000030324074124010340a00417285d0701c081d041c901261403c440101d072070030000f00060b08603602103c0309102165000c0d014886d80046030000c3d6505070160038200030400c072481640c2420303460300050001140803146085404114400f010a082c0020a00b5008a0000d04004c0c50312040d040c0c05c1c4030803d51580403c414490038107548010b0a01c80500aa4010f8010149411003200500254558a40304e034003c54040310400010000124801d9562117070007a0030005555204500c0a402c0c0103683d4954440801014420240002c2d80e9804001008102280c414160b044d19100303444800200745145180c840c05202c1c0400e404003005e0750000f03070380040d65012500d1075640d84502c02a9140519056400e9104150010400081c0444506000300f00c40da0311039050f072640d42c1e504110499001e051900700664210400d510a0301030741d41c02c13194126000801c5 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 493260467 1250 493259217 493259227
    0x7080103030e15041d060102122502040612060b041b0c0312020409020a0c12140706230a0219050906040b13050a17070609120308090c09070c0c0f0e1b 66
    0x249101d00403c1008843e030540d0300e68100206d5507814001403900c0d48030380640e981044642c0a6005004401c9e6070900c603c2c0809078028010b40d0743d00d400c20b5004107108250440541c1c02070910401402001e034401c1d000314180425030343d52500c0001c0846041184d41d882c0f5000c5042c0d5541101d8070820303a110300c0c0100c0d80921010851461510041c403451085496410210990b8988407102c02e210b03200c07080a2080308208900407180b88400c503080e0340da010340001905003407000510200c0e801e4030b07143c2c40410105000c00804c03c180b60b00903d031841c0ca50040403051280400300301c4042c40b41c280983c0d00000280001c01c0740106420180000b00304450701010fa130744d00e81002c42c81d446030b1980700c140c5000d4140070045203c002400700b50b020b41080c1c5003c4e15036a04046801e5010742130000000c0402005e00009003803000140404000000000d03d88281402d01c51001800004654020f032142c2004201c00200241c1c0c2441607800c50303001c070480c10102d959602000311084a001c115200500081003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 493261717 1250 493260467 493260479
    0xd060e060403112a180c07060509030a0503370e0f0109031202092b03081b07030c05030d050a0f140f0a05180a051b181f0306060902030f07080103030e1504 68
    0x5c0c81031060181c0c0c04580d0701c40308035040010550300003a080c108103070001c2110110980c0d010701184d03440042401c42075548030108a100c91076000c1c1180842c0841c2e800e9140c502080d0454001061011104046403030080390b10194a00b2140d103560f00502094028003040550405a0090100064024612036403041c1d14031105003800a07180380402e0300e40354400170b0010180c004002d143c00c121480a804c0341c03074030032299001c1c2901c07604c0f40c054240402408904d0811004104460f0003000c041c100740100e00304804014050000d603480038001030b04001e11441c007040c24400031449003841a01c081010784880600c203000703041c040c0c800708001ca90030b9400394009030100710708100780c2e100c2c0004040c50700c035804044194070008080781d88204408060200707815240182d09030015403d0b066101100303218203406c0902103050340014601424014001503001d0180e0165100b814050b44900460b6241c0c40100c401807002d02000b00803d1072a641d448482c01c00c062800b079440400460b0502d0280c55403 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 493262967 1250 493261717 493261759
    0x904021201060f081006080d081f09090309050109060201090213051005090c0322081b070f0806010f0506031b070201050721090b190305060d060e060403112a 69
    0x7401c2149241d100c2c0c0e042d5115005e89104040041c03a504002e4075018038009001404102c010700502e64052040e00b80310f01c0d9903503455010f401440c1c076200030400c0c81128039000d0080c030f026204650104266a00024050380180030703070000030358003c03c9292846100c01d6004010302001e84150b040502d6003501145030740f150b41801d405101d110149035140d203071285842e080032045894480c6120002c1000000040d1040f080d507003605030b035580160402914a900074034081250740031610803944901c00044d4441c001c00c01a050715100403c0c500308940741c0d81800300520094480d0f10183e1008850351031044840009040f080348149407281c03501341651103002c401d00072481a0000705140103107000800d034010b11220001e059000900d81400e401480c0c1c50615140c45040d003080c140c54800040f2a503484002e03952045501250401240181308070079955900c0842d400c5002c209008000300031404006400c2c0300701007011420503c0101800c0442004810f0043c841e41c0140004141c3d1142402903 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 493264217 1250 493262967 493262969
    0x50121170f0a110712170306010c020a150e03010515060c010603080d0e0d020a020a05040c021207080301180e0c040c112e090b0f06061b0d031a0904021201060f 70
    0x183c0d40d0800d8145900f010503080011581c0a2180d09a62408180014035039440d004460b5190301030980d2240e4505006950603407403080300035401148054041095036049a820410a510b5501c001310b11801500f4142210000e40303011210a10344090304e01c840c6080c40051900350000d200105106540303070f850760b0103600103140d0b100c1401e0700c401350481103800400242c1c06000c424400ad0008009580100b40e405905000d15402140c0300c6003100403040c02009166008218050101e9982020b400d01001c0f41e00203006e181d01c003200b0115490000d441030b015440101840c403014101100808040100400080c1c541e002440304002c030300024031000f1300ca502800100741c68040c02c44940d8901c002107000403044891062440d0080500110f10009142d40d07202c40c090744131801c103440e040d000400b24001e80038188580c4d4a0700e04405040c2002140380d810341c840380e480500c2404580d007843c1400600618440703400c80d0300c0d00002800b500d4040c0c4a011203498000001030b1043d2076002a0314a05c0791 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 493265467 1250 493264217 493264237
    0x9070603091a09031611010e0105031009150302090a0902040b0603390a030b040605061606020a05090607030c020316031109060a090e0c0f0306010e0403030c0e1c06050121170f 77
    0x100c540341b000e41d40c00103008160759000b481c009155240c91101000e07001c6150150190081e0784041072060041c9111110001e55001000e0241c58a401020380014203041da20881c00b81d8141442e5080904058064900501340e04140850245010400d000a00c2101804401c5d58900c0a140ca01022140004004045a564022030555001c40038070003903a1803540054050b0f0010410003a840141003000244660300c0640541d6880300400101c03174501495400560000000070203d0416800102440c1c109100b0b5043d50022035003240003000b9085188000750501042113000042498585009948110f0003000d8065207621000190101c0b10350100c00720f016030210349042c00c0c40c13501100807001601c00f01d0007094590704003011800b204501410003404c4c0758135038a10241c03950140074000c80d01c030405009800146846803078855807540c640c01c1518400e00c0e041c000704400815000810442d180c402030041c02c4401030340c0c0c1c4004409007041030a0307014414052000d0020780f01c001041d110b55 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 493266717 1250 493265467 493265483
    0x60e04031101060605031023060f0307110a020a0302040c1116090b03030a0207060c0821160206040b06190b040f0f0609030c14180109020309070603091a090316 70
    0x59001c09142100d40c950801001d10606208004005162080c00001c0c1c1e02440542030301c84501c0c0c0c5017580c0902c3d4501d800780c1d100a01103010310100440e040a18811001070b41c5d1440181c55070100161902c900711006500441184428005420300d90000710b200f00040c50704c03886505004000908044a1a0030b603444040707100000c100c941040d00030035403a40d10441c081c5140400000b8080d540d003009114240a000b21403d0141c04e2003454419218074018602d46800000740b1882031188036801102c0e222207003282c3d1a1803800017440001c0d9648603c5c0c1c007018144017a1141e10400015540d05142001d26080c040d0b000f1a007280440f014100a003411000c0326615410a816240c4c51209a0014010805000c0080020a0801d003540013100c1d88812200d1b01c840c8090b0220340e01c1c203000e600340d403012408400001a1524294000d601c210105400e50351081e031101d0003201514001c00e0050b08103041985108001c40603a460b49400280703240c22a0301c0d02c2c03414008600c3c1040d0460f0b0a40d140c41e = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 493267967 1250 493266717 493266737
    0x9070305090f150103110d06061d13050a080306030307141e030309030a05090d061b120e071505130303090609061416080904090c091103160e0301060e0403 68
    0x448200000b441c00c1c540c0e140904041160107110072020041448064001107803200030130115181e05001042481e04070741c00340000754880340b0a4400c00003e50450b40602c1c001310004406250b018441d166899000002c1c4c060b1824586522240f5000a0112941404100a4803001946111036140b11502101c06000c110054055041c510600700c810300342c160f0410070400c80c3c03541d008000c441301201c0500307105403074040c0309000c00c002c040c6010004040e0b5180075566110007044492207503c000c031503503c010401d0500c200810aa980740d841100440e0b100c00c2c0180045604001a508007100382e10b41141050608401c1032012403c590060700400c12544090100c10341c0032890314060b04d01030038000d102024200f6820b01c0c3c0e10540100b40780c0d43d131002c0c450341e04101d014000c4514084000f00148025240343c00e125405401520400310501c0c0b9260200a0400c0c0c0c260540307110f001030f1408031240020704030f01581d1102215041607819583e81d200481d0040c0c00d03e29940c06a8020740c0c40003192 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 493269217 1250 493267967 493267981
    0x405120a05010c050304031209080d02070b0a06061805150f041706060405101e0b04080d020f0604030f0c05030d0609090b06010804050705060a020c030a080c070608060114090f09070305 81
    0x4801041d075103c20001c081040202103500484e003520066465180040d5404480c10700d0440c3d070007100f0303034510365500000d10441030004543c00c03e4003030b420550080210a41c0d0315400d860380d5084105528090800103000c0110b40707001c0d61010a004402c1e0515440d03d94150700115940d031164002e0425482d48101100004a0401a040e40400296401c00a90515403d003070844540382c480c5807440c20016000b004242190710560004000d001c5000d500d4030b496441198554001540c41001072081000142e240000010020f00954141e1110700400d80010300c202c814a059034030a071514842000b004001c06200d210342802040090703000180980c9514200720b03103038805000702c0c0c108a01c540910010410204840e005c443d030844942d40d4403c010b0100340d040000c00c0e103134258940900c4000000f4020342070002e210807501c040a942420b034850070160341c21003040c7c41c40b9000916055100c0ba81c00864002401320400062450515a07000c00001d5040b0790100d68010001c9d840d80700780050 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 493270467 1250 493269217 493269221
    0x150203130b09031b040f090b061503040825120305100806060307090218090f060a060203190302070c030b041103060106090b0708090d02090406060e06120a0212030405120a0501 77
    0x601454440e4900d0000c02c480000d981d640386a100840c460a01950030100d50384a0b48103a80d0031034400c2c4c091144c800242001d24030802c0c1240c0d414080c02440d103000e031003001280304a034800c652000d810303410b010701140f03d0b08503490707410300d9074001669170040c81f400b00b0014400c40c900080145c0d0045220714061510b5551141a9400a001c69002c1020b00420303a034042250001c0c3d035040c560050711984800c0c3e140d5401e180e04051070384c104109c3c0c000e00000f40e00a05099104002c02d550301a881c507991441282d0b40e1040c0c03803010002969a040703010b6854820703002044801c1c043e40711211259201d0b2100d0802e140290380490f144a452a1510039900341441460f00402080c280869054a44030642042c1c1c464544028003500c1c000817440705076640c000107400e02640203446003141d480e103850a03100030803240c001e5651500c5406c00041e010710b0001d02040b00107130024040e2070107041c036600388285080e140f40003030fa49010034000460345403902150131741d4020541c1700509840c445c80c10083cac2 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 493271717 1250 493270467 493270469
    0x1e0c12010c0216031a15040c020105060f0a0f0e0402010c061103040501150f030f02130e2a0d02040905011d070e06030c0d080309120307030506010206180714030715020313 75
    0x7901e00b0f46040c0400108424011144840402a1521000303580d5286c0c0c002c2c0c9500c00d40381c4103601900d040c0c203550300c60b030b0b056010714400c0700f0503104110724a500808100c07038491144244207034050070650610a4043c041c4819402ca031041c100915011080d0f620901925081840480d50100101c20442400001d01802d04031761104007104041908100c0030450900740e60201401c80032424280d070003192521103048411011030041041401c0c2202142c54842a00300380b445100107522182c0c44074a80c440321038102d803d03030040440d002014280c1c2840050915031005580c19540d6081540d10408070200408400240f88003038001d2a04140305651001c0b00030305010b009a04c0b9241c0c2410316140d400c113944010f0b80100d2000d4890342c03020030052030128203541c11111500044248040950907420031402048241c09843c9070340e0750440161880c07594181c556146600c415804c100ca0350050054a00990015041d03448090703c401511400d042c4c901d2040c00140c0c80010040084c4500c4640d2238 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 493272967 1250 493271717 493271743
    0x12050115180609150504051807170c0306010804050a0b09060a1406090c090a0b160605070203271c0b09070503030316080a0624020c010e01021e0c12010c02 68
    0x20701541030000080c0722054034003410780708945040c090302d5118080c0341980c008007001440c0c81c245404a030340342c1d8040c020560307140c000f20360b408412903481410440b8051107015480500c0e81503a45980045406981c054005d65050081445190109010880070752159044100420b690b0070410b015204440c5015003c0310044c01e034109200441d56038050007034200190b42c040a44401040c4e00145011465074060304003606e0000d000051201c00c81c2c08071881500403a4208000d40c0c5910090b0303140d11501c0f10844228641d1000300a07940010301942c0c945040c050b10184c550900f801c5d072410b100900540950f6100018030401c50188002c10003080070348401c2c0c000c1c5055040c14501c404007034025540d640c00b4402e101c00066503c03520f952110004040ca5072030680362111010040103030040207000c2c480103005180a0b80f034254000e911101e00501c060f0b000380821312098010207480c1044031800d0f54203024880c01180981e840c0200c0035640001600009651200781c0c001901d003411800c200 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 493274217 1250 493272967 493273007
    0x216050a120314011503060e07020f122a01060807091b0f0206071d09070f08150a050402162a060c0201051218120c070b0403050a1212050115 62
    0x18110b64090019181104c0d0191403a401741c500b594425009424141c01000040c410b08080210407a030000b05024240b0030030050f5031401000b507000f08014070075000c20798075103c840c8a5441842004038101208010050300024a8548401001e400c026a0343e010450a0380c4a44401440c8040c800030141c005006040c041070a0101d2070b0041c1d02c46400030207050078070003400c0040c50018024407500c00c81c1c0800610a150300c0c90040c0019020005a8081705c0c006242d11000482c640280440c051841500900da00034091070282044082d501c042c13140503420303899296881c0061490101c541807003084030810101c21071414080c0c541c1d103180c0d610402c1049201d2102c02d02503600b0004445101044042030003a607a10110a8090182c2c460035407510b40c0f083c5041401d42e04008005011046201c0c0156507200d50f441c04009440d0043e400f000e0042d4200d0071002d40060a13050b44112900c441e4140b400d040c00e40c908150003216802d07404075051860712484002520351280009448414042c44 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 493275467 1250 493274217 493274231
    0x60510032a03022b0804090c0807120c031401030b01081b011b0f02030a030f090e01151b150606030e060702100e030904020304050102090a0b070f02130216050a1203 72
    0x400e6030400d03000d1002902590f131222094009100e01d0010a04004041c1e12502c241401031402c08420b41c0244200d0388110b16140749000f45500c1a82d4441c001c01d403942c2c9640c070340d09503c103410000700403030b0030103a003810750b14a0b01c156001a00034042c0d000b9400340e061100150b15005090781441303038588500b10f14952020720701c0656a08031854854400d40c060507844001301c0751402c4d024034114558017962521a020629003013590140004101a80550300d003006556030b03255030718410500f8051b440407115480c030300361480d42c843c03000c2407810010081c2804001456440360503c60801c104254507442e1101c00600013035030180104405440280010030651a00c128000e485407540103114040c20740ba030002c1c800441c800c0050b1201d140c0028401c6699051514200e4000d6104101c401d0140c01c0c0d400340001e0402800c026604651b400a041c400b00b140035a08100c04001c51005200c0301d07690910041c18000456249602d41c14491030080000c946641000e110f80000c4ca00e40000300360404a07 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 493276717 1250 493275467 493275533
    0x200604030207050d15020d0e0f01050a060f030201140706020912070e1006050909100503010e0616050705120901090b0a0c0213061206050a022809050603270a06051003 73
    0x1140f54504220841c00580724641d8600c031f0400307444c111280300c0d51071281003000035010106600c10f40c00785407250010054030307654908200301000340f032201074041040c40c045401c4a144002c01050018841c49005143c103803401c0002e80103035034200c807021aa501c084000d21902030507d25442d003000828002400a41c50914001c4c51440f542c0c00c2c0340e000320703e400c0c00b0400e0f01e0002885100034100c010000c0c81045820b180b0740c0c1d50344134205d07405070a806d8014a282c200354001d004449940b0b41001c060100f1a0301c60642014651244901e14104003001100044401110014100c004495070303900085134010f0040082c001d00c8040d440554514200003044801d40540c03074045001d07400303440810306a440408101c001d021301a400086900c5c000f58080061060050300c0340c071040540c441003801c030f45440070b1000031301088860304a4003121003007075501c0128202d100350500085c182100c03100c40069480905849042d124082c1c55919a40d0074410440c0c540c0d9004009941d0701e803400e01c6641062 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 493277967 1250 493276717 493276733
    0x603022224171602070807090207110a0b1b240a140106050d0b010e090a1415090433021305060c192a05130b100f200604030207050d 58
    0xd0006030300ca2038540c0c41d84010300e0007031002100030300906c2c059428490361400300802a512400c0100ca07501d0900c903c1030038030b1400c0c500035007d80711344d07800f220305011550500f5a04002c1880d24003404d07200308007070003080e43d5201d00c0f40308201c10310074800520b5050105010040d90202c010441481e800e540061000c1a0700c041903444c0031802d4500801c4041900005a0b102005e407880c0341c0d00039030342008100c1c941317002790010370081403809400a981c0c5da4812003c43d4040070589007951002000000c20b004c6658808015104810000c408030b01048543c0310140c00b0305a00d04450105801103040750052014091420007810103440c0c0501e81042200280d40f5220012103c403007603510003035440107000d81c0103d5130764068640344503500001b0302d0146101010308544944e0780b00b0703a0b030030f403010f02e05c502076010b1260210390280500000c03aa02100940d1483c049180c1c010412603252008130140c1c50750f039860440105218003400d080d0409040080c18400c240e08150700800d41106400002000c003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 493279217 1250 493277967 493277971
    0x90b0610080a05190617300703030e03120601020610030201020a0b071e0801050f0609090a11190e030c04020a020714061c0218030c0a060302222417 65
    0x1c28001802d81e11026105041e0500400a40741141707028804166030410040c82d6046400000071216044481900c0c1444600b40c0140c4201011611043c164050504c10191010903ca0705000c03074545403640e081d03440c60304400301000c1e1140880d0184149540c0612905401070f031860342503810142140c00103945d8400c0f00d40700030b02941002001032500e91103003600c50400c0d0307650001c28040781083e60000706210428091030b4440c641d642e4200f4000d203080310444034010300143c8081c0b0940c4d12881c2040c01031003402c40d24034a102c02004a4154012008e01001e80c50683d525201007110320300302858917001d076501c0014025841000010440d0341c000408800321038440160100130485000403444501500f2088000c2c010074113040d81c00c00300b20780c014004a0846030380204c0146c0d4010105540c0e0280186015003100d02000140040c500c02c0d0000c09414140f400000480050444d0402410710703180d0042400701d0000a0000d108c0204c40380b48400707400c2c2403904940a0f41020b600704154540 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 493280467 1250 493279217 493279231
    0x30b04151a220b1803010612030804050c12070906050d050c1e041d06090d05190908060a02041a040305150403030e0706020c0a17060a0203040f05060a090b061008 71
    0x80468020010459907520700c4142407240700ba103110960350010300c0f0351900082c984140003009010080313054101440b9039400c41e000c1111684c0c91708002c4d20162034409000e44150382900031884003045588460b42030383e092103610390040c50b080c1e1900408100301d0303559410051044458030149004900c000400b000311000460b15420303040181120303401700d650b007800019000703800c1c840702c6190400c51154051181402c03800360743c8076076602c29020361190040d2540f06c0200b1824040d1641c0041428011046141181003d1804503103030380803582382c02d804680484113140c00240612034142900194050303002804040d909240c2140d54098646c03c072000c0106031140d0220000d0140340c440d80116007108584070039505a00c0c2c80e00402074032840c0d01d0346203074020380307916900196860303a06c5070b0a111000349002070035040d154840464042c1d030003c0c0c01502c019211030b14000110b24280080e6009141114001a11030f045141240440100900180c850051042c641100d01e4000d203042d507025074 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 493281717 1250 493280467 493280519
    0x915040c08010b1e15040e0c0a0305070f090e0a090602070507050a050924040912020c030d09080c1203121e0a270507080f0c1801180218040c030b0415 66
    0xd03265001e07417444c011a8010f0b0305030541c40c024050380501c054004c1a880705160f0f000d2003140c0e5460410780341e154074a03445800040540d902003200c00018009250402e2a034080402e07207811980795032081c0e8008020035646038100040c10802d6240420700035000704410354107107040346001403034203404008140795507004550440010b40aa61340754840019079502075070038160a583c141d0000d5613075500c2e02e500ea000341f280319001c1c1d80341c170701500c59401200c0c810001032140d0a40030f420b2100040c44c11400708590310061115003085c450300008640709141c01d480007080c4e601007000f80c88030f00f14040c007032148107480c1002143c030007034480c0038283d03240d810071000c81c1208032a858410710b81803140d030004121b401080200c118565001c10a0704440000301d0320601003c49854244480500c28800c186400d104210100d04d1050b03140c000d03141d25101140403514185260011130142d80030f0806c01e0740000d03580c44442c0180c0c5017902c103c41c2d000005001014150341070113550840b850401e013174030034140 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 493282967 1250 493281717 493281739
    0x6060f090102241608130611090d120e0a0308070b06150d0c03050916290307051b010b0f010c020604030203070b07030207121a0915040c08010b1e 64
    0x40d000f001940d02140410f8200061011002d5040c50f80c407500360b800078480e400d0045080c035500d1041c0e40c428007500302e01c0c900c440060030720341d00c500c000c01100041a070420810700205109541798511143c03039a0096980000e042e4800d0700c02087d04034005d03d840d01c5a8120f62044c808500b0903000d0381c031b1060340000c070700e0002d445800004101340c03400d02c41c802c81a0070015501092144503000b0030f07403625003906d00344007544803203000c036441c0c04030807420b002456555001000700c0903d4804103071500b0b80c02101c10003600546018000d503607008481000100328001401210035a40001d0025110f038140c000b0450396800723000103200c81c2d584205407410400d513003481e182590fa5200890300210313802422510503c1d518501e400c5c10390460b44094000d409a610700058455108540c0002c1903882400742c55a0500b1030304145d0425406032201c0c032140703d40c41c0004049644800802d0140d4000c02038140114a4a0b0b000d030700350b401812105000d461400d42c98000751101600c25501c05004540b850b03111 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 493284217 1250 493282967 493282969
    0x405030403150e0d02030405030d05210c070803070f1e0819020904020c0d030e0f07060c0c05090f091c050405132306040b0406140d02031c1706030606060f09 69
    0x16180c0f00900c90f01a002d0750705054403075900000104111882981a01d144944120040d6071074028a44544c041e90031083d40d405029000c0104241d00540c0f0700300050410002d80c8030000f2980040326038401182043c04012461500000440e070382c544100c8640580c140b89540040c07661130080c10201a0f14028101c3ca0816001a01a00d032868406001151900e21000c40d030366444410001110210b40317004540364400c43d0102d04888801c2d00300c80100301081c5040006c40c0e81c0075002d001510030b01080c0101103500d0341c40a12150180350700803581031540c10628007086c200501d10f0b440c608800800780d20000c065410905540031120220f8540502c50021305144016261080c0303d00d04100c05610604422035510300709a0207117005a5003007040300844800c1c030003210110300442d418100c1c0844c48480c2032a2071844029030f1132000d4242c440360b40001c22108100804200c012000c21680103840d0306410103070032041d0b44018200c0007801641404c0d0003103400e610641c0e42820f00000f0001b425015 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 493285467 1250 493284217 493284221
    0x204050702030915030f1005010206131b120605090d020d14280f0201050708041b05131a040501120b1b030a060801140103171303060203070309020a0806040503040315 73
    0x1d0080d150b514004c018007008901035208442c556529810b410116038004004141c0006961041e0010700e4540c0b10001c2c040101c0100e0703901103481d000340c1603c941d40c212200c07020318000d050505400d0301d6180c407440c250042c1c64004000045a078004258207051560000e04031231020b00a040003e9201840c003407008507482194440700140c441940c0008003c10a82d00b1484440c0e5590b690705600100c86004a00307071030040d941e0340d0000b80c3c0b00d4007007000b140c80c1c004000307401004410f2001c805a90b41c004690383da560f0400c00b030740340381d6160800f00484110404c0d11040080860b0300300804c0d030420184d100340050340320380500064940360019918089401000d0a10400101065140d24121247c60050092801203079865424020080f55040825000c14141c0740c1c0980000321641d0b4071540000f1039040020348112070a889080080400d1042c0b00030b41c0280c00320f07a40481c10844038014003000554a90103404990300410400011600101c00e480c141c0f5446031b010032039212034188402c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 493286717 1250 493285467 493285477
    0x1205090112061e0f06080115020c0a08071a070206070303091a01030b160e1003020a05120118110703020c010c02040b06031003060e0109031209021909020c0c0d0f020405070203 77
    0x4141c1d00e00100440c8119101c18800031a00c2040303910a4656103480110500000d64491800840e0024005200c00c149410700301c1120307126441180ca0064582c00001c10400301603200350204d42243d0818401c000503034a19041c034040c80003600e450031710349502064084c810600c014041550711000d03c001c022803400d1407004065842000c40055860b414480e41180095841c0010b0341c1c0d10000e9465038500031410f807170b444e80c0020480c21101c104d808095000c0e5120700d18540c01c22800704466070140c5c070400e03945800f030401281081c450799412a646811514007151004403008140101c4001035030000d64155511000e203000340c50a04030384007040103021143c0d092580200c0100070490704108001286003103034000c3c1d0041c401d81c4030103100d003400c030b84e540130000e00015080c08070803100a055411140d01035101800d01022060500e400c223119080c260400500d494002a2400034800c0030403002e10344030011a5140c0f4245103e5480c203850311fa501c44003d001d01d89440001c1c03e518000c0c4241c032 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 493287967 1250 493286717 493286747
    0x20f0406080a050c011b02032d03040b0316050301030804060311091503041505010605161707080a0f0302031003020409020102011407020d02160627030602071113050412050901 77
    0x3010501546020b130b0701c0d9490460220b0010368010130440080c0d4401d841e420000b5000b40103400543d60062480c40100c640342100c8511155280020718440b00400003800140000c4c400f00c2d8a80c207005c0441841d500c58501c0ca281044014801800411001002c5908485c55420001185228009480350394003600780f40799071088190043c101d03404030350300085104502c00d104188010140880c040c044500c03e0240c0c4002070340501241719090850003008002c0c6020301000d0f0b100d5580d01e1000c800503031000750225a80c55001c15015886d0b07030482280360b502c8055041c00e5046103801d860403071481916203c064841c0391a0070b62001964002c3d03019035464803d034130900c921440d1008010307507186070f40ca500350014411b0003010701400c9541c100001c10f44807070340c1d40c944403807007516501e20140c80c076040054202c0c00b50079000000900303148002d08400d88038074158003e00403603000b084103580c4861030003400c0701d013820200300004143c403040d4200f4030501d040540c0c5403141d540c012030b140c000f008801 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 493289217 1250 493287967 493287973
    0x901090602070305120609071d030a050106080304030b070306050303030606212701020f070803101518080604030e1003020f0c0105010f051504060c080c0a0c050a0f0303020a020f040608 81
    0x301403640c054014031701e004403c02c1d81c441d151607540034051203500460b02040024841c1811042265120b1080f4580102c02000c595290201c2d0322200c0c21504a540600001c0d440050100b08101100b4a500e43c030000c035040410510746420701082d268800140544d01c907400004940c0c4c0069080c0b4207035820000300185003016481c0181a240d40200c250280c140c8034444010b030100c041c1014001c0703034103402100d04501c1c01c01c3c1007a42c540b0840d80002c1c0183d4014117500c0800701d8407003068a0070f1036451a65903101c8884401015103035400c0c000c160405505034010504100203e82c100702c0c050907580782607541408150540004800070b0164152201e0034100000390507078508015009075041c1ca2224003080c8945913600704100001200d81e8035020750301c800b40000c0000764025560000380740d0140381d81514059504503801d00700b81000e14111501411000103000314201001e1401c003400b0610001c005182c21341e01c020b59100614500203101d040408141046a10ba41c0c0142d40149503070001c0b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 493290467 1250 493289217 493289227
    0x2060d05070e040b03030c0a0206210403030903031d06041203021306030b090705070b220f0602030714040f0b0c030c1c0f08010f15021203100518010e07080901090602 73
    0x4000c02202200e00c5140c840d41c180040307600130349004802c4800c600c0001c0c0051100e601640c0c207001a0346c2000c802d0b101e0940110b0545444c0b480820450783c1700301d102c0e035000210004585000b90840f1a03440d0201c0281c02c0c0d841d030340641e5090024181390481c4e04a03220039890b0306002c800702d020b4414140f84d0403d101c00c140b00020580c4e010b400c0203284a00c01c07a889c1c900c940e100c100481c0da41c06100c0019110881910120700440c100c100205405405440f407444400d6554503000c0051003486c1c411500b003130b0700200700096a640701c2590300051b030704140c0c040d181500c0d1091b890000f6615000e00c55035500e0004202c030305400c0c100b00301c1e4030b090007003410344807560145565002042d4016115401007080e05415164461081003854183c0e00c4030003d00040e6410801c3c419655011a14440b066104d10b4440c2888443c0180c042c40c45074804c0d88819003082d00300401d214007140c2c100800b00118074483d0040c42407151042c07500754840d050f460140c85c01c2c1e644141c40c50142c0072401003c0c14a900c0051 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 493291717 1250 493290467 493290481
    0x1302030706110114130f0c050307061110060803180d0203060f040c0b0f0a030c03150e061005090d020418061401050406270c09180501090b0303031e0402060d05 70
    0x50603504500030b0340000c1045030021032002600360000c6503484816188507000342d0008805010446505014080c1a40c420741c072074012074038040d103e401c00004604510804211004100031031034644901040600401c0c0c94401840d65074042e800741b108a40c001025505074507210501034030031443d001401c54002e03040c4040710385103210382520207a4070022241404a50681d2007802c9520760241520003501c2d2640c034180840040240803902c50070540c84410707100d1000b42103074480c409000ba06000e1142414040200156140408040340900206206020313980d96400b000381b001d40d80661f404030340c0050044240d0003510440b10020701092070b010700040c07841e1030550030078141c0750213482c04c00000d520359407065041c003400341c0c115031550008554010900140c0e0003801c20748510307052516116403100003800305e084800e8017002c0e070b881d680c6004000e010010f009505100205502451560400648041c480581550039001300fa192001050031520307504221818044242001c00c01810444 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 493292967 1250 493291717 493291727
    0xc022b0f06061203050a0818030c070e0112150509030912010e0d141c0b040f050a0518070b03090a0f05150a1e0e03070515040b0c040e0f1302030706 65
    0x154090791042c0c584600824848083c0c184010b4141d099260700c5e09288590030b00701c400c103c006083d040700d010400384904007404100013400c180c1b0040300103807440303500f012600368603860141e101c1c00e0000d0301d00c030140010401601580d4110340b000310002c190355445000d032034990701c11070721080d8009900da1000002c0240660142d0701d441c0c20300058803483c0c0c032404022149500340038840c4070307500010058100c0000d000c8503c41060b4201c2031001c48c0d650741c1c440001d02200d56140584060f2503c0b0810041d0188440c030510f5409900c191141c103c48442a90f1240d40e52924082d8503802c25000010030600c2c01d0400451304c0e080c0c0d000311101e1200d2118a08143c492154402c059984902840480e038580003030701a505100c0400c211f001d08060070400410050300c82800e01a026000400598010500c103100c260416910720490ba0040d00b03043c6800c40b0a220005e00e0580310b40d4050009000203a22a1009900a200074411901075107800480d52030082c03c15800030361500c908074002640399000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 493294217 1250 493292967 493292993
    0x90f0103060e03070b07030c140307110709060b0f030703020702040203040c1412030a0e06070c08010b13021603050315100e030c0603151908060c1308030702010c022b 73
    0x920700074401c005200e000d159590051990060007000c2010016403001e2180d440030842e028a49089d80d408007024031039000070b510136108070000450030302b9940c086850411019005000c1c034074007000501c0ca07141404149005003e103030002440000089030100d80f00e50151851290000c00c115528201b924000e6070004030341c401d400c0440c5442c0c10865031131070112480213000c0316020145240c041200e0040383c2081840000960004d000c0c00944040361203071a160002d00800c200006034192020104104200c40c08403c416050040080d202804400c0031a00303411581402c2c600c0e00d0381c407080b510b4400050302401094022004501102030b65501400c60904014103a007501e0015844209101092004444110708003034107401010123418202d00e107000c042e0f00002565041621005150704140040d10509070b01c0d4408101d8540303140a810762240144210700045190a07030642c00039149482503c1c0117842614000c401c3e60312a000d00800b00304600c03511802d04070104803450030b0070000e407403 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 493295467 1250 493294217 493294223
    0x607080a090e130c2310030906110406022506050a0c0503191b0b0f041704030c1409040b0708040606120f060e01020703170919080a032007060905010b090f0103 70
    0x1d02c0c003002908103e000c40c440e0381d0681002c84081c8954070308091003d180b80c00c0380b11201f01541c916845001c0340461141d5401c810342c000d035459481c1d19211000345850190503401c04810504c13001900d0f44125000b4010440da17240c100315803620400c21007030342c0c02616aa0090b00d140400180b20500301d500c000c4c054203000e06501d88480c020a0342c2140007820602c1007001f0a8203081c00045407041c1c101202090f4000d1203212040001c1c1c04061002c20560040d6004856600043c0c1c400c1c4034040103001c40c0012810240da540c9614079033511001d03101100500482d00340a0344e1404142072040c0798110768050180f0724144000c4800d24600401640b06210094a980d031600f84140d00710001802142c3e803050300b50303850504a5171080c002d0b2480800c0a020714401d4402c0b00041505020441c0041c070602e0700905030f1944071440d1050180c280d030302d07002c40758210b81150160302a0301450102a03403d45a0800800680841c0e149410f9006000010041ea807010b072580402a085400210050580348 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 493296717 1250 493295467 493295483
    0x903020601081903050d0b060f070b0105041b0c0f080406090501090807030f080f19030e01180210050c011e0615020109120806030307152403020607080a090e13 70
    0x82e8031403800c0c0d2034000501d001c8002001c00c84400c40401e20840103000800d45071000025007120000020710301c1c0c0d0240d8074855001c5c801089100030301c05901106c600501d419501485030304904a1080000e02080f16035100380f28410b40b00700107220f000a00440d92691017030303030740d6602c0d911030601410500c41c920800d80041c2d04a000824141400b00342141140d50046040743e05007c41d554401a40c2c12100b034a40180c0010b009125400c47ea811035a114010b05441c00a0b110240c80c0d41282524406c010780000f07018240d14110068440300012104d11040d45089900c81c25079044442c00760820741c2400085d260140d40300000e006090b84602c2c00c65100c0c00b201d95038031b85814401d90a03503203200006841142c1d0303403404540395401000c05640c0034030010181e07480e05070b86503900d0140407410542d07001c06541d00e031003a90903a10071026594088a07003c0311702100510351360024409214100005040d01300218207002014043c43c0300e00003910003a824040c9034540000240ac2c1c00000c5001521045 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 493297967 1250 493296717 493296719
    0x313020409140111270310110c01060b0d0c0c020a061412041a060102120d05041a0405010b0f180a0e0106030506090f010f0b010516050c03011a0f040b03031b150a0903020601 76
    0x14003417014221325442c0540540b045d00204035000d00200103084100c0b890346003c00589084000030b1040c0c6014142c000c0c241e5031070b80c140c0a1403500301ca11401c0390300103120240d400040542d64030072554085030b5461500c14a10056854010301310f000e100141ca06400c10700b02404100701c4a0441d50100840d005410385560395058012642c500d00d02c80c81d2100141c00700007070644201c80d504051780c0f05003c1c01864500182102d170b9004403541c100d0703003600d070360b55541a078095a14142c4140d0003064011620020055555949d40e41001c4019090751070003903230307100d11100001d8203400000c01540c01006035922841d1400760b180c0c2360404480100015440d00340802e4843d0710170705c00c0160509060759540e042400390203014400c2151040c1c02e5800b8810035030000c00d40d940034080c420300c02003140c0b03200042c41642400c0c0168a101c48408520442c1030007107103119038a000003910981001072154404003450001041d0a18040081074960000c2c45000c0050f0002540c201108035032080e8203c40f226 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 493299217 1250 493297967 493298017
    0x120b0603012003010e2d1b0403151104061b0c080f06011503150b030403030908161b0305060c1305041802030c0307030c060f1205100314030313020409140111 69
    0x540101d0320f50310010808030f44210200d100c0803203550700035207c1c0240d0001011909034859640c10640c411500301801c0199203012200707601079401031081c080e6805041600300380300549110202000318045004081211092000454814008014801c00e0b01c1304540310910030b40c0c80f494240100104003090950341d8000d07500c02d00c980102c81d90a030190f04110f504002d81425203a002410035401c06031100c84903c0030070300400040a90600c0081d0380161010540342801e900010f1007420a007020700c0390000c00200c1c00c04140329078000340600c802d0f41d403601844501c0780f0b103841542041d17801503e007141e000c13100c00f01c13150400c0116008030100c42c0710070000c01c00c059075a08140801032200c103501d2820003031140688082400074140e424514054500c42e0802c9049613000c4810141400c1102c80c10818050780300c8101d05c1c2c105095000e1403461815101030020100010350003401560344803802424402c1d40741030801200c159000034008454844138004076a00214102010b0451100541001d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 493300467 1250 493299217 493299241
    0x905011706031e0c10200304290c060415050109052403010e160e0f0c03150d0f1a182505090109020301061206120b0603012003010e 58
    0x10600004004040d0002c5800c2e150004040d94101c0f070226200740d1054043c241e480b800d4039044640d59544000e040c4038440304207031410890b4860070016400800041c0240c821500d82c40d1882031a01604101003000a16015000c0c0b080d41400c050714000d038024041040380741007030901c5004010781d0901a41c1d888204040c11241c05443d1030b4000e040745070139000109038504070081d50300d100500001d02d06d050bc08102d0305006c0320040016090364600d00c2844020550040a9040203409080301814903000880480501c400342410300702c040e180110000f19518040c500d0702655000051700c40803510742c54049454604441c1d06482c4cc41d190001410807800182c100743d07030301c42e40c100a0804480c50703010501400c64414256900c50140d0002140300d46429000074000d026007140141d070b070b62420307000820745441c4400c0c01c0b041c0c42c1000c004108821203441d02d4924184c00c03a0721800903464076000203006104502078042c0c94529010703024070b40c8d8062005141200c0180501030800d555180341820 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 493301717 1250 493300467 493300471
    0x1e0e0106050c190206130b07060e060601200102040f0803071a130b15060a0203070c050f09040b072a0c08031e03090a08031008010e0c03030d0b03070f0609050117 71
    0x10b03007584580480720b0b5400c00325400714146800585013501d81030505142480d00c00075900510b42d980c9001400c04208007080c810304001140300c0d0050201d50030075000007450000d500e00340005601100345520100c600030b40c103d80003403d5005150603055558400c054880d040600160741494550201d04840322013a20f02c24808c4071408040b01016001e591110304400010b00086040d001484034240c8640302c810050111000c1500295240c1210749030851f803070405034000070b0044122108125160b01d840500d241c01c15031003a40500180c1d40e950003151001200e82c4086904010308048002c580302541508a5103030023030f95000c40407602c5007115682d074825031f200c07400d60508038480b00006a003c000650307080b03064803050b074051008545410416420583c0c41c030020f500c0d003407800c100040382440381422184800000d4180d02d000803001a17107078050034558001c02070701d03803007021b07a19541032006001629642c4100c4500e141c44203002041c0301042d008007400710304808524412840f00500c228 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 493302967 1250 493301717 493301737
    0x90302030f012d0603050a1b1707051302210105100512131703070905180f2e030b09070b2b020d050f10060c0203251e0e010605 56
    0x214140b80c4440c0d080591580315010452011303035940c0040700096052205610944c00b401001c929180741a00c00d2080713074001d0344000d504003010036100750301d220042010f81c03c40e4030840b244004c941030481040043d2041012103a40e44802c022070040500e04800c00905950003a48c00c444800c0c14000d041d00c9521821601e2000b00310b11a002071000860790460440580c81206540012060901c410520381c10654485006c0b1300c0c042c0081c82141414000f0300c07603084080b59a4941d50078000d628441c200d901402d16031040e00c913441e03141281c1720165070f820561400c2c0009080301c5c50742c0b8180214081425140c0b0801c5018007000042d806079540c080c2d90318914400a2a0304c2c040006902e403800d014411124410715809101000981815220f424850191450411000e2500c01c0504018250540020051014144407407000d0386000400060f661040d40d1202c61b400283d142d1030000000a40c17001c0c198140900d070003a079020480044604a5030000f100b80d01d0b42c0d895100035100b60054078615 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 493304217 1250 493302967 493303001
    0x11d06010e0603160b030a0b0a06121a030d02011b020601050a120302150a0c140412080702040b04020a090305010e060c030703150305010e0c010806060309031b1903090302030f01 78
    0x5100032800784a00075000b0384010b0495400c0b0030300661003000884954000c12107600e0110030042041c3c0725010b050a1840c0440c1c000d4000c03802c24401426180e03510300c40c0302c49185d490007523200c140d43d20300c0340c0103552100408641b1000300c0800024082c0002001040041c908294242d02180c000589141070311801441c080304a820045d00c40c603410281d0b441a41144100e9146400380d5100440041c041d10340a0000b01e50346200035000391050641700c83c0001c89100c2000308211880c220010900141e0780020456a51102800060003600c1103500141e8450310000310b8885c419008108803040724401e0000303000f84c00b817181086440f014115001c0300c01d00c4c0100300042d0300b54844d0340661540c1450740c0d1300d80001c9031292103103800c41d0034035008650305a015640d0402c0e55a0007152041d40b0450448181d869071a241c08107071348a0181065a0149404401c204001c9440c01d0042000086004600e030804c0c12003030800803c03003407052109034000d00400b96507080d0000c0601521195400c18000 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 493305467 1250 493304217 493304219
    0x11a0f0a1208121816060f03020d0b13091202030708030601111f0c030e030c1e030412150605010e09070f0c051c030506011b03050d1d0a05011d0601 65
    0x2540000000301d2404444001c0d04005481a0341c2140c244980100d0704d098a410098010b00081c515110b81020b00ca403240b100104200006035020b40c40c0c0e0007416291602580b180091603903c4042e104009889501102d50344500643d0640d50f0301503800c16014021300300b5410f440c02002e90302c81c86102d81c0030b003200c1ca042000602ca54040d0140c4002e0a00d108204e819401d140705201030000081c0c11000801d584a0014409441d03250003224403000d41c10f005503241050401069650380d01491408084091102070088019400e0050750020190405102030704945442d1918040d081030110390b102d1450a1808035203540303d044049021343c17010b40400c14641728541c050314030fa48490022170400682c2c281040004030140440c40e5000d01049410302c560220400c09030541c1c0008103030f181000b1240c03000103000121074020040c1c2c150103090a0703641d03542081e0f0300c00280050035281ca0000c16580e285d040d0b0003000192000d107079070164000300004032009000c503824034402d0301400c41540c01000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 493306717 1250 493305467 493305479
    0x302060109090f06021606060911030a0e0f0304060504060206150f130b0d0c0e0705030601050301060807050702060f12010608010f05091302090412020c01020d120b0120011a0f0a 78
    0x80000b519502440100c4560380c020b5031218160303846101d00c00c028001140c415010408103000380b8018041e19001840100d1142030108454000204000004c0e1345030340140d84c208806100d107010b00d201c0401541c1e0782c0c41d2600c1014000342c0c014429140184505400680d200203880c031001803082c2d0050000300d0f486090380802039038031102d80d0702152155952400841e55030702c0603400350610b4032402c1c040541c1e92500300a01a0000d00501040500504004200461381d01c90301303ca0551740907050030303213460715009011621030103403c0c4d00941045d000208040c0c44000b2501030b1035014550b01c00000030745e0702c0310412141d100003840740c5219203050800501c44c1c0e180c419085a403142022040405c2182c0540020300a0b2006450a54030600c40307120450407980d05000b04254402d0a00062454039018a4020b107039481000c1840c030489e0b924221000b09a2040c54501c8040c80e540e41d600a4000d01d0198150090200c07031110800c8180003103e545150600308451303103a1603002400240b5652402c8 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 493307967 1250 493306717 493306721
    0x60501050a0f14160203010b0f061c0e03211803162402030412050306010207050f010c06050a020d1a060915040f080606092223121909030302060109 65
    0x2601101c1480482140c0c90f001452500c0640b00c1120643ca0341c01d08003525006141c2100e0030307140500d006040d405004134440d2140c9049900031045c5103490380d2866084c0300600018100c01901080b68000016130030400c3d000d2100100c0480c10781540700069888616486003080d00d0910514040d42051000c0c076a00440481e1140ca114001d01441045007134070020b0340b041d003456009209956901000b0f010078403900380300a205039105424442d14500f440360010390354100c184a81481a1074202d0b10500d5039100e80d1104140e140d0204060185007414a448030280d08101100b0104600d4503025400766000e000c0300e2103070000050001c1d45840d034000240812100146a194802c0340c0030070000540c0c240910281006001e40d030042c1460f824000100003d00e8009010125110150090101d45801d186070349410382c1e6110500100001035401c081d4000442d8000205450241e84d0501070701c102c1c000700521211492441d1008680141c007825034128019000c09030044c0d20010046c040001d4903 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 493309217 1250 493307967 493307987
    0x1050402031002130b07050106090b0303030403121d03070c05010f02070b120a090c090204030204060603050108061303030b0310090c0609060f030e0a02090c121b1615060609080709060501050a 84
    0x244e0107220405403544002c0b000c030360042c0c0040315260754501d020004a0000e00c200032981c4412005185503090645008005003542454026a9230365051a0b80c0140e040ca81c800d101c41103100c065940307424841c03c006481e1511413080e203000c03508640340302c0e1841d4404a403040c103075006080454202803260907600c40400004000c00800c0d41d1303c50320180803800702c00d610401041c005c08090f07078440c11441440180c07280b5501000605062100601c6001404603610364411055840f48031180e480d0b06084010700000113299801d4014015400364650954100304101402070ba0b40c120346a0751088200c030058014840c44001510100403550b5203407217074015103054003004085440ea681c0a40005588190903210628000d07000a509030741c1c086104405c2c0c1d406075501c02e180c950407051552041c1c05104160300301c900981900588000c005112400b0714011000d184100007807911044042d16510280c003840400b8401c410000030700081500a0f20203444041e55880e08041d90900103842034500 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 493310467 1250 493309217 493309237
    0xc160b07060b031603140c03060412110c0604080f0c030d020a0b07050f041403100c0f030903170a0207020924010e0d0b09010c11010b100c0213020d0209010e010201050402031002 78
    0x28041344c000c85400c00080300b8003450140c03464100c038405403040245411a2407103828020f4100c2070402012a9000c00c004e6080402da0030a40e14001c10101000c0c10b1200a003a500ea000f4404a07020681c1c00c000074040c0c07882107140048495540c0b01c2070405541d240d0400034030b4016800003000c0400640c010101c260014102e041480c20001d40340855051500142c200a4141269540ca000c0d14901044105502203109400b04040740b041280184070b8603e080c0341d507041c13340b5119036404140c030541c242601480c030050802018106483c000c0e010b5880a001a4840c015201c0401c2104c94840e051007040f41d0309110100b410b81c107080c019150030700d02d08c010950240010010b20041040e1540151003120000000513100000150240c018045848030b840c280c0c0c50680c15540540701c0801c030b08026803c3d401c044290415034400614014440150711414900100f0103c6500d20141c002d008a00c5c026203c109404107010700482c203c5c4c1c812100a0761591000c0000b407100c2e80c1303e03801084401a = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 493311717 1250 493310467 493310473
    0x130902010504090509100b0108100e2805092505010c02040905150402030d03091502090301060807081b09060102190809101709010612120e0409080c160b07060b03 71
    0x507562450000704d9900302c0300f01c07040b40c0240b202442c49030041e100c0c3d8842d01c5424245500c041c1404119010800c00d940140170002c40702e00c02040411a03000f02014140c1e1116590341d030081e8203182210060041038509c030000e441950312600056001111070210044000341c40d500c41498a001118110081801a80c01c1a034030942480424414490740c0c1070408074a2404000c3d04045c4145894440554100d800705840e020040740010f50100b0310702081c15210b60050388030804180020b00500d00f0f0780c40000c00e441031580004000b580814402c1d0300b051084a6031a90021140921041044c120b889600580210104514078840c03001c040c542070340116101030600d01400041001401c950118038040382802a00581000d81800d16650003400100203104c0d051914070031500d0760341507040c01017408020b120076040c820301c501220241c80d50014030501048840e4140481c841c4c1c04901070342c0080c001e170b0340b6041802d001450902c088480001c1c1e080d01d09241520b422000705140010140c1c540 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 493312967 1250 493311717 493311719
    0x1806060203070201021f0f020c060f0a020a0e280f0f060507121206270513030c02010507060908030f0103031206080712020409020a0602061618151b0302100b0906130902010504 77
    0x1072034a1010305070f00509d000041009003000c105168510070002c185154460041100d24a030079030005418600c0c200c00c0e00c003041c0000e00120460680184828442c03407900f68007500203451076011031007908030340a4002c48500b59072644811900c51207403100180040f00304980c0034030310310311076040b41c42482c4e5040b2000480f07130303140c2c20a80300622594086200030140c018100c0c0004d806c6100380d50700510400381d50120200b20340e40150000540c500080c0c140200840c100e41404015000001082e5001c5502c0e681e0f490505114502410700f0701090f4001000240038035048001c134030511007503800003802003464a107022182010000030b000300301d8010b5226501ea800503207e280418006d4280c580180100c0d24100c801c20340103011001c580700412000910815080c1c110541450644501c0b041030840d08080306000e0380d5400305241e820540c04c02c91141c050505502017219020000c8251061040070340c000304103e00c2003420740c2c010350f000081010701c06803020603500020100e4818180346040c2 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 493314217 1250 493312967 493312991
    0x50c0109080301050a121121010504030801030b09010c1d060d06140405091614010c0b13050f0d140702040b0901091e05040b071d0303041806060203070201021f 70
    0x15403242101118400750110044c001460700c0380c00d91018000030740c00415004419280d0142c1c81000e1040e0074000d0b4140e0403c2e01c02c034442c000c1d041040c03440e20310082c0b0a60030b01d807500070140e610034481500c40010082c08208040010f0298080d2404d49650794402102c1441482044680303081d10349500910030407071002020a507000b640c00030150064034214800514050106a60000b44095000e4100e0480110070746500700030202511f00e40400c29640c0707440d200050300c0d4864114000342081c038030001007298418540200e000351511800035180c1505000301d805655800c0480810046180050f00d8050705c40c214015145d8031b0f00050010070309000e401c02003400d00c0341c00e0300f0503030080d81c40700340b484400e981c81d40400040c00c40e00b100411030b5250544500300200b0025180b2010010102c01006900d4281000c014410384014107803a0340303996502900c1c2c1c940c3d05038201224142c0c02c060000441ea8004002c2c1e0b241250107802501000d400c120403039403401c0f9404185500107603140c06031824 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 493315467 1250 493314217 493314221
    0x1c03200a03020303060a09060e0109180204021b010f02090307060c0f14060a0c0203090f091504060b0a090806100b07060204080d050a11061b09010203071e02121603030f050c01 77
    0xc4a01a030061540c0c1d040039000d105010b80c468104640ca00d04226003003000d00010541c7c10f0448020303800c001415003960220325040902424040e50040c0089a203100e06620441c2240000700c030700b0002c2111410300d074615416030150b442c0791f90f4140c0140e07204100a600407000e01141e02e104045003942c080c5d999039606101e042c001c026440a030b02c80b0b020040182003078494000700d4008c0307000550030803107034000068480022403a02d500545500c00854980d980501d4034102581000b0402d00401e51180221502c94000b90680000580810310000d1040c80105400307000d9440d81d4100d00440382051600c42087d400440121380483d42008005181d9005000110340744000d40d40e688e40d146030800009010090039190003809130004414802e45040307003010422507420640c54540c0b52954000140d08600031048003601c0b001101904d4507000d50f245105d541002d10803600d5503586c041c1d21019a40d200d4a00d600c4c411114074442d01400428003d42c032403001c0e5002c528001d031403c00e49a4040782 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 493316717 1250 493315467 493315483
    0x905030307023003060d02030c03010c020c190e16050d05010f050109150806010f0e0a030c031a04080d0203060a1805010303080a090201090b07030c0816060b1c0320 72
    0x40143c0008010000c0b02d465007602600488524070200344041d070702415181c0074800682940c0c41010020200e60443d1028068900000e400400070000c4c51054000030b034459003010085445400b000304620046a8108c00302c1d0281c400b451050150383e9641d0b21440b0589003c070350042d09001060110042011880c01042d000c0e0040a82101d107851074a000500000d2031504211002e4180290b94070046a128040b070b58000401d05e000440c0c0c4541b003100703075001c0030284c0361180c124908550200c2441001c5e16a1000c9a1003074904104580e03443c20b03082d80f241001d8030f0040c50984204410410400705401960700300000505c000d500036600c10800401c3c0703000491404145031100010070a140d042030100b5848401c0302c1c400c1c4a100d0955000900c2d800302e50103280041c050115034001414841d2101c802059402102582c4e1000c00d80883d41140303140b441d040324024101300107580d070f13030524500781c40080c5070640f0321a007202c0b055581030782c2041844501d80201c103c0c1e280105200e010070483d280b = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 493317967 1250 493316717 493316731
    0x11701030209060f060d0906050f0402100f0504080f010b0312040803030a0e071203030b0306090c0f0108040813081c03020901080a0509011e020a080907030f12020f1203010e060f100c0609050303 85
    0x6c241d11f49207011404d4030700c000d141c03000300c9044e00100030150700c449440c03190700f00701440c103141080c101c44010384003030040d500310341e4081c820251050030b5202c055001c0310180c1401c070f00302c1d510101d070104021040d108600804449400c14401f01e002c02c0155004003a0303941c0319a00f62205c294491200d0303c000c001c3d00b0f5040e00042c0d1180440d205509050002c141c00201d9000a4030071034801b1000701d00042da40c20144c60401ca8840300003014085184159031702515031a84040c612076a034401c0c29925952180030200300242865072540d014024401c03205841c5040c2c548203e10307501c200d10000100801003a1241ca5500c0705c8403041240803040ca1445203104200740180c48070701e0301500900219004000000c81d03480b800e000d001180b1818031b1810850b520640e80e022844201d072040f801e000000c411450607120b90008c550040c107520010314169845c2d0303103500c100d50b5503075003c008006100514203904101c1c001c40c6e00c0b12681c803600e030000407940074040101c1d04580641c1c1c0c5c2c43c650b0b40201e40320303 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 493319217 1250 493317967 493317971
    0x60c0a0b0a0c1206030206041802042313020309061602010905120d060603051b2212140307030f0320040e01050901170c0f1c0302070f05011701030209060f060d 70
    0x40c02141d0007119240c46468403030382c10030144e03003141e0104400c1d10036402041da030b80006001914616107281c0464004d881c002d0000c5e450107400041c204480380d540b01c00d00e44510842501e001010485200b5030f032142140c0d40081400fa111580d044203038a440ca801e1104554840e80c20740003180c0c1c01c00c09403501c0c03044880016a1025001401c004885107038206008060030710701480001070000244039003a00000c5e18481d91410b003070411000744038180d078554103260044040010100382c502000884180100455540004003c8001e13032684231300000140460070040140300c00d284654003410a5020000c4c260a00c83c0c1e6071812071050341c00650016110382e0301500140103508100c150640107204080720404c51444121741c5030f859040301d8030340d24000e91811600312059070b0740d290440742000c8074041c0f207200650350382002915860b040c0284c03128a03080c1d5400041c654031810515410820095000d00c0c6030b401c540c02c0080c0480d0203401d50f6840242c40d0b0b0003a5041d55000000c0c10012241900 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 493320467 1250 493319217 493319231
    0x150c040b0a110d0306060e090c121602101107031d0406090209040608030f071113050403021c0906050f030a111201090b06041202010c061e0606200c060c0a0b0a 70
    0x40365151900e804401404c250422004124564010204403c1031500b194507050955484036402070501a201090105c115141c0621503450b05140300707906040c0340ca500ba607110620320345202043d11105004002201c004011003400310344288428055201546141100c0601c036000140503030b0b00d1034020008841c0d00150488c858607291217424001d03c1610040c604018102100d9030603030046600203049016a0f4812248503a00c883c0482c000c0414494200708600b400c0c00c0007542c0d600c1c50074a400400c0004c406003081e90b4001d000c6c0c401201c400359101807510a4030600c085c05904054501c415036a11004551500b20449024102e504101c50710014150700d0009004203130782d200d2600b540904810441408100381e105401030800e41c0a0901e041c03030740c015251420003052000c112032070550512045034600c0c2d1803900400e08982540da6000504201000801d12b04082460044020307444600040103904141015200440d010f078182c640300d03ca585c6408524541c08c58101c401c3c680d440070 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 493321717 1250 493320467 493320497
    0x2012106080f061005100507030338180610030e0a0f05150c040302010c05030904050103062034060204060201050f071b0b31020f010c05150c040b0a 65
    0x100c3d580c4e01c030107840380004a05140c8404185080e030309000c880100304d00000c840003458020340041c1d0181c081c5d02950203150300c07000980310a06980b50316281c18461180300c00501792900c80d03905101c825612030076095035200d0074100030214803d0030884003403640310307454040390f07843c103102c03100c0d60038012004441500a20b10382117040100d400806524020a00d01380400e652000040e0340980b0f90a00303028003508035a0030702e149140070350190036502a007488004001c1044513040b40081410344005411080c030780050180306401900b02c407170031400029002d000341c09160400d04454130012110250350080507222007050b603100c0e40010780075179101d0050180588280d411184e102c0c02d246000c55182d00c007a0302000ba4501c2c1440080c00e1103040720302140340801061385243c5d0758490958215032147c1100102c00c0491007500c0143e02c40da03500303043e00406501441d145801c89510102410440e000c1001c0482d8040c2e02610b580320b001c0c82800007040d180e00c0340d001440300c82c0701c1c1d0322030418200c1120 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 493322967 1250 493321717 493321723
    0x2a0a050108010e1f081014060a05011209030302090d1b0e010b0a0e0a0512010e01060b1207030207060212180f01020a021504080c07030c060311040f0302012106080f 72
    0x6400541000000c900410600c02200c14490304a0080283c0705104050700c0c0d005602c0c07506503041510940074048011b00721041c1d65201c242e40c6a4a11301040032560317601d00704090030340380e841101c0c007080704aa04000b0201039948001001072103414014144104103000c03032106280e0410455420405019a50000032050000b00c002d0020125003c5190f05004003030409008400b01107040c0202603041491984d41c240402c2c01401000e031005050042460380306018000b00404c642e01c03940b0700440441d029410400301e07500e91004900702000382c1c40f00e0b88114000e40c0f05060594030b4681c00c0c000c0c1480340140501c020700607440400100444040700d80c00a0400b41403801000f4503078810420781c440035802050340c4a0082182c03030490a035640d20308003010103101e1084481024080c1c0303003000c01040270b80c2041e44203446061f6802c115000529080140358841c1b801981079a8000380020801503109020150031031030100c82c0000c06a03910b10000040c0c2e2901e4000c458581c00805150305c80403410 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 493324217 1250 493322967 493322969
    0x406150c0506160c080a030605060a051206090105010203191418010219020901140f040e01050f090c090c07240f0c1806200607210207030f050306032a0a 67
    0x4901103e220031101100988040c903e00e030300610610010481d0450f440c007070340c0000b005000c040c103603d60300e11004c10002d1140c0d000c0ca0b14540d1003810300380410002c0c00c10585d83e60503200c1c10380045107081d8086102040c800d00741050041000741d48808011054840d00242048159805050740b03005101400a420803003200721129103418514075840c0565548006181121444040c41083e0444280070698103040b080038190030604080c0080216101540214440c020b0f4040000700b0f522281305054030341c000b07403a00d2540201901e0206140114410041040c0c42c800d4420b4002a01d5500c1401c0008001d08074407040705036601c03000d50704007005020f070000e41c030300900e40000042c2d945000141c1800842c001c81007041050841c030140c901c2500c81e0b10400d0000c02003150042d2030a0003004000c08201000ad00c103855080d42c0e48440c442440c000e40350601d0f419100e02100324130105c0f00b120181c200910050f8180b20303003841d4607600d90307480603404000c0f142c1d60b440c1e0f0005d1403110180403c031226 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 493325467 1250 493324217 493324231
    0x60b071401050709090e0102090603040f0b0105010207062c0d14060a14010e0703110c0a1509030206060118150c06050606040305060a05100302040c121b1d0406150c0506 74
    0x5040810041560111320b880a50303810f11000180c41a81c01011802402442c40c010f4200800000b0710081c00110344c81c100010f44141076074185a80c844004a8441c040f910503803010031520442841d00c0300d8000501c4d0500202484000380c4044400005607031016000c034255a810000c08848100b403c2c203219080d8405181401800741a00d01d100740105654140700e48102803420301c010440281c441c0e00700c0303011200450b541e552584140e808040c2c41e6680c003003040792003114070411a41241d036140242000303190190080d25840d0f46138001900c591000d42c1c03e1080d512038600c4082070004051224001c005c1003603481010083e00742c075012003100c0000d80120f100702c4c1c060004000107580080d013a82c0c4401401070108032600d0718810487d01d0641034000a41c40b60030708020040c000d500114002107144c22240500464009980607250640e1a40c00c99000990311841744040003404012509480c002401c0050312990b01d062207619100b9081d1a0700018610400c0b020600800300189904014 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 493326717 1250 493325467 493325471
    0x12020c0f0f06160605010312300c02070302060f0406030501090209090105190e070f02010b0108060f10090b0d09021806030618150a0f0e011e09050709060b071401 71
    0xd00c500024206400e410300d8521a800000303410000080d400003058a4941c08502480386584031b2814102c0001243c607400700061306e403400c1400129844250502d01f100c007032001101c00c4845103484010300181703561207081d442a19000401038a03008000e1038103840d43d0240c99101c40c1414001800d40c0c1041e0b00214480e070040c003842000fa030381c1800007030444000f103c040c03401c1130036520140000960380d4411810001c0c0c0344204100300c1d4210240d2003c2c09050313802040405c031124015528071405072402900b1960900040045081041c20003206144505281170015510280a64250b0105c40c0c40701d02c494035540c2103000c504040001e84d04514010030350700114608000401c0ea00c0740018030008450301c0b000100300303c6000c240300c8580c024a25081c09001485d21040d8440030707007085c8803c0882c9038580301d990782c0c00036018820010345118403d00c819180002a4599020300520380050380c06004081d000986980144030301e6000340310448d030507520382106013040046c5541d08010312110364 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 493327967 1250 493326717 493326739
    0x303020d0b011e03020a200109150e0d1d04091b0608010305030a080606040b0a02010527060c03040c05100807170112170f04060504090605060705100203041e12020c 72
    0x2040d05004140200d00f5280c0142c80d812a95021620303021000b5444480940a007603008241d42c064001c00b100b00d00500b008a0540301e0300440300200d528050021251750080311642d9220340c850440440707030850b410f894645405c0700c0c0c0c000804940901204072001c9540620038040c2d4620401c08038006c000c2402c08121a601d581c84403a120f12800181c03000f04544e41d400602c0326500e00050703c01410180d502688c640100000184c02090169005a1040c00254a0800780290720708054407035007030800076040644a0b891a9801600041c02c1214425402c041c007240030b441d6014001c2d12221a80d41c0e200c00e5040c60b04024110158424040d174094410b400180310401d80511120541e175400075025621800c003d942181501031607030f030010002030008002814592180262094445480c1c04104035641c6008005261044210003003042c1c014801c8214a030f800c036805158054042c002c0070f001030680ca81c14a003100310200303045811005c3c01c418541300ae94100f250951004055415503084 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 493329217 1250 493327967 493327997
    0xa0b040e06241e0d02041403100e1519050702030d0c0503130f030314130c0b040311010c0602090a09020304030f0c0b0c07080d09030203070317070c0209150d0303020d0b01 75
    0x544200e10b115440d0f0b0010042940101200c00100c07000c52240a4003107481715100c440b491004c0d503000c90300500c80e1250300e1006003400303443d1003090301071b1026000404508940c0300c05048034070390007001402c41d80140d640b1000b0f8100c482c06154418a140d0b070141d9a10004504000d08646410136007000b0014180100070843c0c445001c0304482c40c0d00403210000304a81032a04134060030355a0419a09a0350180610040c20800002c02d44050300c140c0811241c540c4500e0701034800d008500c8040c0468080002c03a0700c45501a00c04070101030b001e2038003d80781c100b400c00441c0700031317201c0d0f440715640030341c000100418954040d0262140904a05e03028941d01c56646901450b5a00909900810880000d00104001080084500c4200c00e68028404110b080c1000381d1a50800398041e0701081c600102040514866212244202103a441d40c0040034055001e000702c080e40240344890722000450740c100356607201c0100e800c045200340e0700541c0c1d60f00c011000c1c1040d100300703c81a40c14822000400505 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 493330467 1250 493329217 493329289
    0x1020d030504080d050c0c15100503012f04080f031201090912030c0c0203011401030b011a07030c0602070501020d050907062102180918010c0e1008060a0b040e06 71
    0x1500800504c0401c141d00c61341c078101c00c10312518440e111244a6084444911078040e0760042c810b0f21400d260400465540040c1420380340906100f0f60a004190460700030249020445250050864a12810b064030762481d245012140c0b0200c1000c1d0f80089071502c01f00704401101405800341080500005c0000e583c0d8080c0c0340a021035031000e16441c0c844140200d44169400001d40790002d00038448404a1201c64040320401c0c04140c0d00d2120100002c9541c5038185104011100c00089007881c1480075201260300000074041101e00c590200725600202d02c090014112400d8524000141800c152440e5480c14a080d44010240100d9602400130a420a00c5070f0602c1c0c1034031040136035107070b003c0b07004a408014010130080e4081d0151040c4030030080310303104001032800c40c41f0080040800703c510a84004d200300307003caa80910310460b0908460b2154a01075044000607001524490b1200c00c915100d4105402100c00000910100991850040031020801d82c0c087c2034914080c0204082d01c1c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 493331717 1250 493330467 493330477
    0x3020d0506160c110922080711030f0a08030601230a0f08070f030203090a120809010609090c06050c010e03030c090901120206031f1805061002070609090f060801110901020d03050408 80
    0x1120b13401240001b81e50801c42040700c032190005caa500362269803a450b02c1d6949810030b40701030300c3c280003402c03110005003400507000b00c1d00081c000042401030440e0303452401a500081c20340e0304000300c41070104643c0c8541900d0b032017000c003030207180ca488507420f1034002c21006c1ca4050400400c13000d078050064058008a02d000e56580c0d5180150f5030340d6401c031426180622500000304121103a0b01300e00c0145901000300b500400923140244581650343d8090026120580e1010b450848400700800c16036005400802d06211000c0000c50701410100c0700e00c1c11070f0400c5521080c680000122120703507107000c0c01d02074050420f00c0c001040241039900070440d81d004c014002100140e1b280c110350000141500820020812540510003010451076103002510041d5100d5004609d50000c00040b980085410401e07905240d4a000304185003807a510064854004a0800c0c1c903a613080c0400c0310321080c024405100460800e490303807408603000091401074841e01c1801050316101c14400001e1042c01158 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 493332967 1250 493331717 493331719
    0x100312170112030201090b070201230601020d050a021c0f09061404060f1215210506070302090d020603040c0602160b070807031b0b04020907050f070b0c0403020d0506160c11 76
    0x2403082e041850281c1c01080c08500251420710381c24100082c0542c150402e121a006c442600e01407c0c100b000300c0c2e460400c09607071240c0545c0101c40348440951003440503000d90304040c812074000d10803d00d02604404484c03640c1ea0700044001802404c182e0704106910024001498950981020030b0b084c1406030060307004050400115a620f00d625521903400070300d040800d620f04112540c02c400031100d4030700d66482160441d051501d6010300714113900c3c04005401d070300103001d80b00c103680d0444c4c01c03002548a04802640403019070300c1580581c8441c0080d41c499031061003c1c50031603040400103071800100d403c060707a4018105038288041d110541c151052154000c0345107480e4402454141d070000020007081013640342e00120b960a00c813290024070302031030003170b80c07030a03507945030302e0021a201d00c0303004c5001106000800c00c0c0350005181825251b40b0031180d026a078245a10307070340000c400f102405401d40d0654051070610014560040c24200814410b050642d089666075a400c030780c0310380d008005 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 493334217 1250 493332967 493332989
    0x1b0f0521090a0312031410090b010302030c0901031e090302240903120c090619090f060504140409060c0206041b050109141f0f09120c0b0f0d051003121701 68
    0x100110324000e03081031454178204442041289000020031f480005c5520031149001c1c2840910722255000344200d03070080320b4200a1528007010240150054451503030040350103d000c44081c0318058091161030300403480703030b80030b80395440c010210400e138181c02a50f1002c608003040c017408403102000049179498003110403814425525406103035028001e01002c5904030390009807004081c0c1d070001c49208007080380e4583c109165111a0310000d111800e01440020810411060007081c02080310000314840040c4045001400c95031283c0985001c070350b840015a20000c24441080806000d460700702880b074100d10821b600e08800200344d51601c0c40303000902c210992103842c0d5501d50141e00c2c0c8503026816000ca402c0d010005000305100304031200b010014181ca440030a0742c0c84151440c5100c03a400c40d00084410342000b000d00e034240d01c09450540c146108024480d10700d02c140c0601d61140b2260075017520031038030f182840d8000415481240c001c03c45180c4c4110420884680218156804c1400c1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 493335467 1250 493334217 493334243
    0x31e0c080f0c0118050a0b19020105090601090e0106030609030302090a23040f18032f07030b2205010515010507031e02030906030c03011e060c031b0f0521090a03 71
    0x440c1c01300c0410341005400040e08440400d00c0341c2100000c01d184281d400d0300c10b00c88040d4610072400c030380c07050b81d9182c0c040c1c002a004103c13040864000c084800700080001400c150790350b07141070072903d050f40d086000c46e40205651900740741000104001b40040c034844a80090a802c2d2090f03030000e034151082c4074680d101030016544a55501000c101c50001e800707850707000708c64100600300030304500201e80504007a00c110320081609103102c1c3c00034030342d2034001d100650555035900c4500038003c0075440c502c910b29030388480300c8060102e41d00d0228012400014503082030b0303641d20b4110544400d6a41407200c10004480040c0c0d00c5250544122414201542e0792a8040400ca0862090b0601281c0c406004424031004641e0440150b04841411440703480c44980a0301d590413508241c40b601000c40d8540d150b40020901030925081c12240d403420340d10026500b0382e19000640c103441300941d12640200c0542e2040e8501400185416010380c610b18100044100014008407043c00000c2c100d12824039 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 493336717 1250 493335467 493335497
    0x61918050a08030408070b0405100b0f0d0b07020c10030608060f04020f0f1309060f0e0a050d111006030803160e031e0307080304050d08060a0b030105010f09031e0c080f0c01 76
    0x140c0d44140d41c401c58407c060309080c14100e956010580030041c0091a041d4840054904141410311152014010b81a07500f500d44801303110301b01c0201110290300600c01e80c40700c95a036800d00258103d07810f4500140060604981600c1e00100a150400e46052041440050f036200c5420342e01c821011100309c9034804007403011810b00c00fa00340190707170074a040c608007200300084c07a0041e1075401003070300c401c0100e20300c00e041e02a034074550b042c00942035030800907404680d1031107000f58a541103200750440d000043c07800080000c0314400d500a685448021091116074040240c90042120b02c929141044d001e00e100002d84840c004520100040118081d10b204a40b0501c1500e8125420548680c0c44c5c0c0380908010740c54048103500780300001e21a500040080c64001640d9081d0398843c4000d90075a8280f400545104044074424000e01501210000008511542da801050150242c0c41c0708164580b030031500201c42030300501b183ea000780d500c1c00d05610001801c0c007680c50342444c00130303500a0707801 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 493337967 1250 493336717 493336733
    0x5090d0303090b0a0e100501061403071103040e1807050a05100221130b07030507032f03041701090210032003240303072003030c061918050a080304 65
    0xc01421201d165081003e501d0310366008031701c0e1841400a907440868141681c404980c000d00038140480c804003908011015440f002e160b101240341040c1c40b220818035001c3e45103421650042c00410482d02c1004441090314403003800112100000300040c031704140000d001c402d000d004441c000d480c1801e01350905403081105c0c00340b176080c40321940d01d1039610006008003a40b05680510b2802c10070940000d0001c03203a01100c0400350103684050909210340e0b003c0301c8050b90100903e5090ba00c549130210040798410300c3c0c0c01c0800c1e0305802903a0311458012241c0e5901d1a0b0500c0b0034075645031140150260300e0714500a0300c8044a4500014800060840c0d4201c6119a005080354590044200103040d02d40d0510303000c0501c840c0b00e8440c01d910b1003804040d580c0c821008014142c583e0426903900c40500340f1059010358100030262030405480000a52803e0011200000c82e17413042074a000d2212564496426a0081c020044100c4100d81e01e4841c2d80c3c0c0c091601c010a540310000010301446802 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 493339217 1250 493337967 493337981
    0x90d03060e060a030308092a03010507080c0421120804020f01050a0c08030606130b0d05060d050a1203020c01090c05090106030905150702160605070204060b09030c040905011b02030301060f030c05090d0303 90
    0x48c91104102e4130b00032104090b0422050014000d600e00000310b0000d41c01103090701d2081c01c10a40061600f810066801d69103c0e04801500f1030750383c060f0444000403801080c1d402d17030074010790b250006442c141c01002881c1c9407218499050010820030b014620740c2c00403007045841c2c2c00140881d40c0e615241e0100b10a40f00790032a0034110031040c0d0022844540c400e00601d042040c0c09002d12043d1100c404222141c104203400a00640c00070030b0308000070714000640c5501e01d4203401c0042c1003680c00e40d1b16900352303465584121070302c6800c0c080500c000e00e80300c42d5481c050840351400b000082882d555603aa03803185282c508200808003000600c00e42d10801c403d01031841d00842841c0307035980d00c10002d00260800c0800324400c40c2000400311f40203c0120030364035100c80080081c803e1620000174000240019803054403195203071090080031150f900c11407080144580e0007503a0700d41c074040c0000c00c80030645100c80704041c100601c03000301940c0142900c0e02c20030200d90641141400c0c0c034082d4010155 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 493340467 1250 493339217 493339243
    0x80612060c04030b010503060c0d18020915090108010e0312130c0e150f0310200414010206150d0311011e0c03140618130605090d03060e060a03030809 66
    0x40d1000c200030001da01e8090400c4a00c180800c2c00e0341d03625403007007503112501110400101001401030396101c1003e0740101840151400d40541d0411850b004640100ca08844081c8540c0b00000302c4051410813410b094018006580204048040c82000c2c41d1030740705070010340d5001c5001001040d009a041004850b00d640e11128422080380d5a58590311a11700458550984d03054070000b020903420851100c2044050083c0a0000ea40b1082c1402c4018003803031070301c040a0101340c10f007503070000305940080011705003526042101c0010407000901c1e0103401044902e0f0b412642204074280c3e15000e8440909903454100251000107480c040c40c0104503401e5000140c1407075958440403440203a10800c102e188980d400d21914105841590b1117140030703035443e0b42041c940740c1850402d511001844c0d800c03003120004024114a1500e507401559410b4540210139003141c9541080e00e80c061041d1401413060001c40c8a107031800a0004012085c6031102509200720741000448014007400061220346c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 493341717 1250 493340467 493340473
    0xa030f020102121210150801150315030803090c180a02030c091008061504062c0307140a05090f0601030c052502180c0403030c1b09050a110306030c01080612 69
    0x13440c00c81c04c80300200706031598544a8900e050100d4120104080307510a10720f01d444040e81a4600000920b2070b0391250304d0a02090f80d02c010585075400307103090500055002d580e04544030306140c114141400741110115220b03409081d0746010303242400415603406848540c00585070b40e1151269501d43c81118001540303d9643c084100c0718541101c1154024042511011040120000030b0300180c482c44c007640d4085400d83c44010070110340c81c80340a41e400048040b18541e40440e501280c41c15546801609003034402c0c25040301c031800e0100c0404014642298a680c160070294440e05002802038410781c10503465103080c01d80d260281c07003155030103a48200d41c142c0c2c166400203a04812600031608900c1016058481c0ca10140781d5540c00b40143d944602d0185090300d540c0e42920320700c0d0003010032074808052540d44c1c40f40c618200b003944010b081c4000d0114952805018102c1107401285e00002c9003403061092000d241c8002a891480c4242030030030510300d44603000000d03502e003008a401c4500344 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 493342967 1250 493341717 493341727
    0x91a0d110304031218020f0f060a050a0e100c02040b010c02031603110402030714031009050a0504050c0a0305030d021e0d0e0f0109080304060911030105040602040f12020a030f02010212 81
    0x10850300940c402e5010ba541c0e008120b949034807240030356035070342c0c05100e031156540342020240c40c0c07601d803000060710010042c525045210740421260b402001c104400b19501042a0f80b040e5006051100e00107403c0b161448068442034000e80807a104400c0a8000e42c3e45412a000d0780e401400c0901e80b160b0003c044946011307240e842d508140c4c616000071680f042061030f5860040c1024000c1d01d008c1c0846850307135409200301d143d08400c1074000403c1007946842c1001c2c0011000198410765004610b13010004c2807501e000d0610a1502d035581d501140642025030081010880100980c0c4400d000d0003009662150240e0301050103445401641d0503184c2e00040400f0214030303aa0140a6402c1070800391082502c0d0f0403a09401c98000450180400e842080001e000814a82c03003400b0310f6204a102d40710001461000c2801c640084608841031540024180803a0818445910080140c1c211080000320103902080c905041448000d1580285102c2d20085a00a0100c0322212021000d004c0c1c0394 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 493344217 1250 493342967 493342991
    0x80108031e071a0106030c050c07060f120f09020906060705120309100f0c03051006050f03060607050d020a03090b0a0219060b060d06050a060f020d0c050106080a0c0e0c0307091a0d 79
    0x8643c02e20507003001c6440e00f01500c000c28081d03002c2d106542c490001806d6410b24040c416a8500703d0035038444200521508071000d01a91441155440180400001042006403040c0031201c0b03030283c2268072801d0103001410001e1000190010803a0090340c04030707101d8841103100c91800c2c4004494051307040c00c003004040703060101d0703021f261070141c00d98081c410358540100300142514180a40b10000c0c07000c008003403d0b03843d00c40c02150440300c0030b07003881c0c03070820540c50b05410585d1a085000058000e849644249a440b080c494068000081714610306152550041d64480e01041002c0540c0d18081541080c80303940d6002140b81000035000340ea4441107401d00030000c2c4034501031180714180101002c60118481c02003142d4201c417035001003001540c1f52406032889115200111019034885038042039102701407107080c0041c1c3c81441c0401440d8100050001e40e1040101110511902070003008510390344a280d007400ca03611005280001447e105810704284201c00010f00220300300000c1003c1 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 493345323 1106 493344217 493344263
    0x30308100b040b031f080c01080a091707060609020403020a090f09150c1b0c0b0309070f1805090a0b220b1005010f080108031e07 57
    0x200ea95a925000d07940d10079004964407000c00301c10711204108013041d80042c003400344c0180b0361070360030444900d0340d464004540314104500c110105d21004001c1e030089038000e4101c0d03e4012540340c142211a550b074040d840c100d45042c070b000800101181a0301c00d640659500070041c958070761625031810041c00d200404582c2c3d0b00d640314910b13400182c521095240b4041112800708100803904030140651441c29000020058107911840c0040d42036034450064454507020a52aa100e6001013880d0404580000606451401020882103c0308204000c0400025018006503407a412025150401150001c004c20000400b0440c0302c1010b12000341a40c500080c826901d80580d190f03540d803001c040e207051415201001c0c05000075644041030078007240c80750801d0b03e2203500d84800c60703a0760711841c0300740c5640d40e07036140b2440d6040101100700ca0500b5003044400820243c01580c01d00c0b = true := by decide +kernel

theorem cover : BRFrame.Cov 493165467 493345323 := by
  have h0 := BRFrame.cov_init 493165467
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 493165467 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 493165467 ≤ n) (h2 : n < 493345323) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
