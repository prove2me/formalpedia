-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3139
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:46:38.593189+00:00
-- url     : https://prove2.me/submissions/3e33b3a8-9812-4b49-bbfb-f9b0f69a15ff

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 564388489 ≤ n < 564568345 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 564389739 1250 564388489 564388523
    0x50c0f15090102120c01050a1a180606090303040e0103141501060e03012307030b0405071202250b0a1415040e2d070909050a12020a0507030b0915010510030e010603 72
    0xa800c056481020840c00d001c9c8000c0301c0702d007017001c2c6c040c401c10142012107004c480d01240007501c02c0103415260032090400240045450074402000907000c01c0440c0c4a042d4034514107a0300c1c150030380755241c0541d080911002888030041e00318a044500c00d151043d0036401d102c0c0080e0040401b282001c45903850f05039540001c10360000854821403107a1010080203915400b4001590740403100500000d500f94030321208450340350701424030040c52007000e04012000c280c84000b0349800880980d01c40d94141e0400455080038000d8080c5c01c90103034544d07803107420500056525036040c140202e00c541d0b240c00500c001e07a24204516840c07445444503842c030301401200d80c0c0701c502d00f003042c0c50800e502a0b04c10100d0703c0d900c10301604045540c042d008080044082d1980d22101125819800850148400000100348200301c1c0b5400303580150303200d88075410420b164618010000880025940292004010503615802c203041c00320038074100400e0501c0076a0425006019580009141c00e8500c41d024035 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 564390989 1250 564389739 564389741
    0x10204090c0f02010c0813150608150a1401050112090b0a0b100e03150c040b03070509010e04051312050f03041211282d050c0f15090102120c01 63
    0x1003505542c58014034a8038842c0c049007a107244d0803984000c1410f98000c280d0240400341c9103a80c00f8017403800c142e6a61007011024040d1120350f0702a02c2a503100c034000c202c078000c10046841d042802100e0800907044200c06980345840144503c03414425540c2c0ca1a1030001241c1180000a60002c0340520320b00e042d00c0050024411405901e0044040b0078040503081d0003103110b0030080c00300130024500381541c0c0e6140b81401d04000e01c4a070030320340d0a01c00060400f18a20146025003c6a15800d8031046910001407406d00103415081c03040c2c0c203240c00d0100d00d001c0c05c202e002d2202d400c8030007514000c41c01c80d030941d0140300398400c1d4280240300000b00003e001501c443c2180b144500d58480324110032a1030b00d40d907219103019442c0c0c109031101c86050b245180c0c50500c51089403094801841d0201d030010220140308481c0b015581e50144505510304010007400000030802e03044604c000342d51500b00209248140030600706103085000100f040721a0b008001c0022941d0849490990741e40d0420b260034 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 564392239 1250 564390989 564391001
    0x30b07050d0c090f091401050609040b03030a0e040506040c0c110a17030301090c05090114131a030a06080106060e0405061804050a060c05030c19170c0a09050f09042301020409 77
    0x4d10820803020001c150004036029031a01c04500900c080d419074206000c014140c3c2c0070152240c1d07c2030b56048014042d071000d1000e811045113980315018208030002c10f100030703075200500803403055240c0b0355803114040e0011100f00c0320640101400440c10b0074030002c15000c1f64aa000401842d20980912092546c000001e41c1602d801003800d01c04210108000d507405d004641410b0301080300300044035820103150b4060113131b04c50046070300c00200b6901e185900d480c2a01c040110250b5a0003c10815604028000c8178000c000402c000c010720781c40d000c0300910408a6105191156460310003040050b13990015030800801c00c41148162418280b400320b0382d810040e8801c60b48941041120f8071954020826244242c4200b4081803031300441c10442801c1f4010640c0c0f00042c01301040102003844500900349110351044119603903540c078112070161544402c0e0b80560b00c1440400b201a1a50700c07075400050b00703d50f118a905550041c803a22000d4195601c0852443c80d603c0840d000889031070070b401c54 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 564393489 1250 564392239 564392249
    0x5030a050a0b1f020f1c050705071a180117060d050f06070305041a010f0b0a051306021f05010b0d0902031c02100b010503061e0319080909130c030b07050d0c09 70
    0x11129485c20b280c1041c0c80341c95810b128462042000408900e50340640c004010052184090312034964032041c54005550150b2600c042e1180085440c0da0000000c11740c17070088580900b040001d94503024502e5a020000400d102e009200d9442c1d241e0410408201c0840824220300a071001807070240b000400505049038240da0f89092011034100001842400605840104040800560030507015480c903500c645d0b4034900304107041005602d901c500014007005001c07a540034040000290b0040c142800030203558030040c42c90280100820485c400c2182c401014044000c2000003203400020b0905018000310780480c0f4000741e01c4403449a001c01c0803c101d40908000b048402d01541c011140ca00040341c013a90400c8046803181c01d1010b8070340240301042c40040803111201e040e10416240b4007010074086401190205566090340b07411005254407940c5894003404144003600c6051601c08107100c050200850759000c103141c18416421115081e0702c1e003100348081540d1140c010812545407240d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 564394739 1250 564393489 564393493
    0x30c01060b09010801050604080309040c0c0b04050a12030b0307170102210a050124030509011b080a0501050102060c18031e0309090603120703080c090a030b070212070305030a050a0b1f02 82
    0x3080c581f80c00d6044e0381c295480a0b00550030091401c2c00d100c014440142004240100f501c40740000654000c0c1380e07407140340303d400a03101101041c980f120a01c16244114810302d0f0415410000c00e0301c002440c6411558a1049044840300340001240244509119810304983d40e00300c1d06985020781d8422030180144e40700c1000350380c1c2d95035092281004036242444214804c0c00da100f03c2540301c0d0300000c3d00b154020000041c1008042c2440107103c5c11503000704081640d103010003e400b001d91040500405087c00a81981c0c0f038070385108042d62060110b81c0c480c020243e10003540c10b4030208401718000c88240d0356590914118072103903a4030b0300200c0da554401c0c05000e00007a8103040100d0080010620806502d040151540e002d507841840203107180601c0c5000e001035400b40d40e40c03401d080e004600414503103070682010200203013800b100700d0300e40100c030108004150020740c0c8035003180e900c040e000900054a4458540803405452461311155100c080c40a6400a82c1480b1511420203022902 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 564395989 1250 564394739 564394741
    0xf020301081e030a09061808030406030c11120703050307031e06030605150a170c0409030e12060402010906080a0e07031b170c0d14060108240405060a0e030c01060b090108 75
    0x3228682d02d00c104c11007080000c140304000c20841c0d00440c0d090500c07e25405800503900d4030346851600d10740080d0700100000352102d0200e000990080d004d102d08040c18005018520f120f8040c8650038401c107600101004030020000302c2c014442c0d4007031800c149000040d00b840c187c4034000f80e40900b64500050783d02031f24003404180301c0100070061b9841c030000542040da41c1407400122009040000c0941403590003620030303050301c5036594890113002038480e4440c100302a4402d0300740300308205480d018000c0ca512003002d100150b0307008540321089414038603101d0700903954030a00c40f014044020201030346100d07010300802045400c011101d103841918001445032070390740301160204440c18044403441d030065074040c0a6030812520380c9004601501c0e00880060880c030015250101c268027611054000013105044014800c1401055049405603103045007000d813215a1038481c040c1c6a0301480d40d4841105504210a0069803c070b02c2202c0000c020559848081480546c48075060a00280d0090 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 564397239 1250 564395989 564396043
    0x19020d0b151e09070f030f1d0c0d0f020d061107051b0a14120a0804090c140711040c110a1113150308161e0308090d1d040f02030108 58
    0x51a402c50248000c0c451010354849640036609a40050303035180030503480b078040d441d00c20700a01510074540008920607090644104030241003186880e01544200b620081d100c1c04a00c904400d18a1240c0449885495810516044000302000c8403a02c10f220310200700c0724240607000c0340c9401c00d501034101d46a83c1c42200010000903980500a5590200c80030741414054204000200500807030741048071040460350b2940070040e0016401251484d0701d40395550341e100c0d400030301480459031507054981004815030751410504001307081c0314010356407520050140ca1041e41021841c0f040b40013501c180038a0341c05c20540c41140d07100c0300d83c064201240101407102c40e81c8191481d0400c003074a00c40250b0306556548580741d000060a244000b1000e4514000c91141c41b40c0002d4209500d10507009803140d442c001e40f0360319001b040c11403e9080180d00c2c04100f504001d6040300085040600340204440380000f0b0700030b21300d8809003c581c5201100100b420130b0b000414840e441d000c00d02442c640132140e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 564398489 1250 564397239 564397279
    0x10120b010e0a180f0527060402010c0803041505151c0321060302040f050906070e031b012d1106040c060e010e0301090606060905090919020d0b15 64
    0x40c44581e50001c406041c10481c3c0d00b11004140e6199a5a14000c9010400d240642007a80c1003074800d20300869420704038518107200c04000d07240c07048045002d0070b0149000d40001c2c001800c0c038240a442c50100000080401c07510007040fa00301211210100158106022a4500c40c040e10351580c4c01420004020150901e103040704913007103a8150346d213443c020711f00c031450504156240ca015841e240c0351600480103954601a0001d2640038100c001054680481000e107005406001e00c009c0c03141e00c0420600310345000c01c040c3d10b50701400105811401400c4c004850001c03091002000f4922200501c0855200c5500c4013084003d02e6900c01c00814080000c0c25210081030341c0040c02000c9026081040d03038000d40200314090414146071041804507400700f42074902c5080125a2035549250500c074054012566801034074003a10411402c0c81c4c00c05485d0358420b02208105449552800c09038115628100034001c1103901503480c902d203050100400c4105048082503500c0787c5d43c0307500100345141d05 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 564399739 1250 564398489 564398507
    0x39061d010e011b050903120c03070606050f10210e1c02120304020904020109030213150b040b070f1410061a160201210e0319050903030d0203130210120b01 68
    0xf8004068080c0e112500240da00d80d0210b05000d4142c010b00d1903c0810041186c050070446503001c0166a0310300062404404451480d00150300c224484041d02c1c0d20b82d210b80c000640f0306500380c2084040c000800031702a81421a00c219002c2103130404906103507240d004110007500401034041c2003016050031106036100c0042d030740703407110b0803500344001800f500d44107040c5608280181040711000e078903500070400d071204e54681844065100c21048560003102d0001800900d00203a926050030b0900310608910310901d00701a0500c109480d102c418000c0c0040500302c1615030200b1600444826030161002d810188603081354030402d0107e041d41d402d41c400440f11001a5400d2510003001c4070fa006450309a101800800c40444d0a6a00700d1031544912030003180d4122800215110850701400c10321421400458804210043c46413811a4030300005407548607001107009a120740d00c0900360b070500d86c5420001313035111026980c009542500700c0c0c010005580c0703140051280320803180054401030300e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 564400989 1250 564399739 564399761
    0x30c12030f0f04060216030206100501051c0f0e0102040f0905010b03100b0a030f1817070506071d0306010b03150a0e160306080f0f070639061d010e01 66
    0x301000000d0300802c52104010b50240c4070307141c01420001c02d244c4c21000c3c502c101e882280540c0c003207020f1251582044004800070b020929140c2e2501c02c4406810401029210000c8003c6440d50044d180c0e0180680045514060800c0210b44482c0d4680380c1400ba0710480c0f161041640c80d01e0000f240c101c500d802228840c0740c0d04004c1c1c03400e09161444002407a441907010034100340d61010061454041ca02424a001059910355520300030b071820322410070700a94803019500ca5082004100042010524550095042c1408d5510f10b0001181d484803400540308107506005010002c9200090380e0040c502400024036408074640a1405100320304aa034001d03055078a017403000140003045204402e8910070020314001c5003559076007102c603244c040b4013440d003805508807503044039880d0300800110004150502d030007050941d5803211000c2804e54506c07203228140c41c4084080100d001d000480789501c0c0d100b0820498180c880001e813402c000d0a01e8054030550030000800e401810500418040305 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 564402239 1250 564400989 564401011
    0x90a08190b0a180b19090c090b040504260c070b1321060f0204050915010e0108011505070204020408031603020706050406021009060e0615040621030309050c03030c030c1203 76
    0x10340c2c1d884001c3e11240c001c2c400c0c030380184480d0f4442c2c000042406200308862048544402813400c01400c0c3c2300781c4050003082c41c000c61070a01048003184070345504555840d44180c40042140d40403103100000e2180345000c810a220b00c01000416820000040041d500d03a501c4450990351100040c0503d50001040c541c00400325840710008680d165000306201094103100520741030b030702e07001300318071840848461030340c007500b02084511540c220b804030039400e500b443e10740030a40c1008400901143c100c0e403018200b14000c03aa244c11506c856040740c0140c220a000c03030b0f480302040451242c43c9080c0000450060180c14400181300c1e0140c000d46046e1342d190f80180800741c3c06118804014020301c032081c0e46440d1100648204010180006c5024800c07011200040c10004400d000540701c00390700400c4c00c01c55018107034661014088001c0100e90b41447d000c5a08809402e2161401d074500d42c50b29414040010741c030300803080000040425002c0c0b0f074140c440c42070038000752002c4d5000489001c001c1c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 564403489 1250 564402239 564402281
    0xa200109150806010e0a1d1003080a030f1805010911011112030910090f0c0816060f0e0a1d0f0f04290f0604050f0417090a08190b0a 58
    0x301d4012903510741d01c51810300d4034040140170040050030000099000c040500c2c0450400d000103601070f2666503220b200045e610a410b441d40c1e0383d0401c0d500c1215881010140e5030a2120300000d81d5800c03400030b1240c2d13280650403d0010341000c50003005203210840303059250780101d8410754044c2c1000c0d8040c200303943c068842e412588144032602e600003001030600d801001520f62148445100e10582c1c68082c04820b450149640b0380f9048401d070039000b00055502c4204141170381c0c4024800541078070b5040c50032130001002040d013980e00c0100601032a030320030760074240801c4010701e00c4d40ca0501c1c10465580d4003050b03202c03100342c00480c2600707450400a4140d8600001d0210b2081d8504641e0038078440e81076220b0610a41003900351510603034100d120840a041400303241d140500803c2c0d000ba0091010515500f0550b4909202000d000d80c944d51300f03940410840050759075110346100901000058690344000b45c41e8403c0c0030300105034112510406400451112049881800380394180d1360b08250403 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 564404739 1250 564403489 564403529
    0x1b0504050a090c0924030501140a021606020d02130311040c08130b060a03080301090204170606030d110102040e0103080c070e09120f1605010b01090801110301030602090d050a200109 80
    0x192491070741c52110361040d400502c6203070f0741c441178210065000d0000052100f050440c2c502100c03402900d0a44d1050041c0b01c00b00382c039048580015900c6600002c01a43d5040e80340d14032010b40607981c10300c901a511850000244a40340c881444295021502000252180002a1008501600c00c1d40341042e45c441000c0004080841d015009a402010052615520350315a12035a000740c000211842d00850200841c40c011904008051100320143c8218500400840d98626248004a0401c013060500c030755120780c290704032000b81c035a43c482e04e905583c4074207083e11a40c2c04144070134440e00c50101d00259280540f601c40b030003010300b140600f402e07050105030040c0640283c0849050804100601d001103500d60500c155aa40305800104101480c000003418076882e40e4442c1e105030341440702c6070340810504001ca9040d20350109005880d010f60354041030300d400d009500182927104210384182401a10307072180c0310401000050055402c00b030350044843c450300b8828020564525a04415 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 564405989 1250 564404739 564404741
    0x8071b0f02040b030303150315010602030d1104051206011a0901080a0507020705101115220507050402030103081902070e1602010e0d0909060504020c0c0d050102071b0504050a090c09 80
    0x240d05000030804501c0c100d1090010f030542d80b013076440340c03131061800a202010b41400c1c0096100c030a44840b00900369850120060341702d00c914040403088a03545c1c908070058481d010141c8020b80400b0340005406000321250b039035a02400e002c0c2c000031401c10385030f070340d501c0640d0000c07642c2a0606942d0803a99448558200c0081c000c042c190a0640c05174140c0804d464450704980710031400c1039640c0840f000100e5840030b041c0311101c0b486004108480c010005808907190290101c010881e865005c8403465003480340c00c108690b000598070600002c000420311135200c01410b2801000203600c3c1d0b40d004001001c0e80d5410092088007a11340d005000140002d05d0b0038100c41c00d120300c900000c940c5080300009141803807031492030700c404505500410301490380345e44600b20141034243c0e0218901508265400d55071288040c1e41c5200382e00c82d500000400c2000e406132840740e94044546516205a440051a8510b05020b500d004030300d44400115215003e014041c04660002d035034407140d03414481008 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 564407239 1250 564405989 564406013
    0x10c030306180603020f100806010e0a030b180d0305130201030905010b1003020d0e0a080301090221090102120f1b2a060406050709030b0a0c0c0204020d05010608071b 73
    0x280a241e51424001800c429405101040840380c50300000d80c281075204100300880c03041c0da100d0045200780303101c041e103c1c1c000040360b03040341e002d0814a1600c4103060004541588a41000b408010752070144040100035001c0402c58121002c00c1e118601c54080b03007182254000c50f449404603510b141c1d0040554000e9028031004c5001c1c0001103410100b690208101e1800c014807040040e50000d02138008818501c00c007042001680c0140890208a45600c592408107014100181358001080b01da440900095104000724060740e2000501d0714414060003904001e18048455184000007100215000006403103040103801c080c0c0340c01208405140280c0100402c1c5501040e0805001e9070b04202543d075031546005e842c000d2103071b480d01d0b02d4004160b44c0d0152000e01808407059007480011030109810f07074020348000740001c40d41005841212207201080b0065001840001c0400285815401c100c0c1a1010344d00c07600410b85402e54122410713082e0703070304000300c51510314101c00000707180c003601d2 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 564408489 1250 564407239 564407243
    0xc060a0228050109032003131502031209070303030f06080a0f0606050604030b1e130b0402312004050904080f03010b07110d0309270e100e0a11010c 65
    0x304104100a42d03801d0308541c01d100c801d0b400700f404000c20914401c0c9003002000c0c1c001c0448050344c10002c500003c601c010840d070003000055240f00e902c04070480c0c420030551f12090304107010310981e81021010309440e0b480301e000980020b414103500203070018440c003802c1c04940c1c1034001080d0121554507540102d94010030304a03155512076100007907039a19403000d0009103000310301c811001e09100d001250f80c03928418040a614045808000e801c1146030200345040350400d8844080b0b13a101e10000d00c00c1e0b01d00c10744120250200c0e00345840302c4451000d00b8003082201e408108010444100d4040030314401e19555050036504001c248410304020a03200d030081d02c00d801440c10901e40d1801403e50350001d03040314044602c00301d002c0d01400315941202d42c82070f1058800070b180000c2030b20018800c090300c1c01048075001d05589a2a005160646011100312009004000d100701e111234590b01c9041c440310a0078054204158111001404540c2c038940c107a0002c0b1a0154005180c01510403034005202 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 564409739 1250 564408489 564408553
    0x204060e10030f0c09090e06090a1e0210080f060312031b1314010f0f17040f0b15012003120916031208070c021516150c020c060a02 58
    0x74220510000e0103a002c82c04440c5d1a0000344900f890800001c50345082054481030b8445c00c00d102d141100412a030345010340100350400002032000d5040c3d0040c26003940250400100120002d40302d80c0600d030280502135101158401742c440100b05944e441052071b0300b0344828030800104204031101c11241e501400021003480c201034025403094049266030740040c600c2924521440480d60b03000002d06140c0040d82450b4200d01075000c8010502003800e080040c0a0f03406902080a018000154140055000c42d001e45103107010700070001d9007910306450b00d005c610021818850701c80c1807811282e1040d640e800440c1000031400040c3c04028015245800078021750b0161140c0d1640d24070144082c40c0680240b18081981c00c0c8001d140c4200288650100f0240311750a0300140d1350303c2c143d100c141d0385001030315445880c802000d5190682c03480000701000344504c084804980140c114015082c01c83d001d444844120005201881c800c1d40601070050700202458a0200e80300a0004082c03205903179 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 564410989 1250 564409739 564409751
    0xa0e0411040203151509090115090303120b040906060302040c0c111c021c0510020c0a022206140f0409030804120c0f14060106090803090d060e010203070504180204060e1003 76
    0x1020131101019a05078091800700007403106d8090600c0c0744220300400354010409000118900c00511a0209002c001c04001c003a40d000302c44c9456035000540c003030354000c00411654040349401c2d801041c25100881c065801c0503485488280608050380e4000d404c080c80c0b80304005580204607000d031141000c8a588000010490050b071100020b0404201420040810061a0341003003803030411500403440c0e03014010408106003080104003903000d29030507117440e1098100d0900509050100c0f80118890300d02e000030005500f01c14190000e250300090b00c801e0b40d42c10814040c44117550071640f001d00802e911101050001d419411903c014040507e0820082c6400d651080c0301d0610141095920811215454101074820311449004110600301003921510304004180c03a40151464940300342008a900424020340350001c4a003001600000c41d07481ca41800f0123000f5800c20b0003200e4100c400c09031041c46c01e80302842141c0c10f50f040c50310b94510300ea80000402c4112404a281c440815803612 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 564412239 1250 564410989 564411031
    0x10090c08010e0a0c1a09040914100b090a14010e07050906130e1023010e03030d090b150a0b07052d0c010c0c05060702060f16020a0e0411040203 63
    0x2110b1060811025005441008100d051428031582e1641000c42003c6480c5050510360881e8070031034164140543e0b01013034400117420030301c01803010300d0041002c41c0506c6005403005036460744002c003003840031a800001c3e502c4496101c41200d0a03402002d1040100d01b0062000d0441c0d8555258440d0582c509a4600810b03207000c1180c81d001505010140b69001800340011a5200c83c42507110380392543c4212064035260103003401216410b1180c0c0014a0381c0c11104c4203034850984500e042c1005000c4958800d2800481c0004000c080c5040e29007420721004150301809041141040d042d000f480e0300070303e90409160956070340c0009404c84241c400c00040e820607044001150f81000313510b10b4030b1304070410443d840c1d50811094203981410050a8100100040c1c19040840160b50042c1c4103540c0b0b8681a00c085034561040b00204901032802250000410444002c8100014420380324500001d60301c0140052240d401d450050018150085429503401e10b0750185034801d4084644620180d012 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 564413489 1250 564412239 564412241
    0x907050f0a030623130203060601122a020115080d05090a05210d050a08040f0c0e100603060501090b09041e0204031a1003030c0803042f0109050906010210090c0801 72
    0x2e0b8100c10301e8144e44c80302a8801c494003005030740220740c042e001c41540102da0001c2c0c1c9901c4001d1805041c0941c0764510300001e9659402200c01854400100d00c0445071644408100b0505003a00f500640c24604801c01b40f554510036042220040da0003410400348180003510140c000e1448560880003086c40000d01e551624002c40c810342e51503054800120300748911b11b0510703e007450702e80c0a00c0b030104106d003801c992040401e035000c0e8214a101c101d03945585000c0880615541c0180c041c5042e0500344000350240122034001c807003041c0c0342007112f25511030054030710051a00c15402d03e083c0900070082035003810703004204a0110031890461016004401c030342241c20a400c1500d03805100404d0840d01200e02c44043c0e08145104452460ba40c61542e0081407252440e400030001c071782c080045800c20aa0051115043c0c070803051058065003000e8010244c0c040e013407001800103140c1d440001c1c007418003000f924012035040e03000c0c015000341799104402a200205088524042c55000000c07801c1c42 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 564414739 1250 564413489 564413501
    0x307060e0c090c0a1806091701020c0f060708150901180f020408010608060a1803050a020a0b0a050402090a05070e1c0f08040e011a070605130b07110d080907050f0a0306 74
    0x2c041200c1d81c4540d0b6650008141000310034200315175881521060240c0c941043c1a03030219003500080c241043c801c15400d60280c018003004000704c0c80307095403c3c00e986e01c0c04070303500380b1a0886a441c44000d954403102d0400c0403541d00c1800741c11400040061128520201e0340384034010310f0b520042413000c044844801280c8c025842180681d5480d10b080c01880c3c41840400e03044840704000b403008a80d4585400c03a00121404020280f2200180e0440042c0c003d00894260a810100c00f42061800d01941c1e005000111000c03881511010005001900c0c24411503001c0c00b019074400e00e60b07c0700841442164110180104403409001c61050000740071a11105412841071180c81e8640d46018003d0003503000680028050728550700184164042e0f06050303450132032700980042510340314034075041800f901c4420050a102045400c0014041c1c1195440a54008910440721f00ea0021003046810705030130b407441040c2d40c0100208111034541291f1302c18481c040204010710b01b0f0f82c0c81d035880c03044540f = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 564415989 1250 564414739 564414751
    0x201030b090c0a091208090105130e0901061d0907031101050f19090b1e160b070f1806140307032315010302090d0201030e0708071e05010c02030307060e0c09 69
    0x900003e040d110580d21602d81802042d241c5c00c20540001c1c81d5965803030a0164035141030400c80301240150207291034503030302c1d0010611442d100301681003100f8028007030301d8a8080c3c070390080007100039249101070815940c1d120b12800c4016154060955840e03103481482c94403010b04000e0244524410700718200e0051030380115069159580c1416030300c001e41180080e511001c0042424401800002c694000c01880504902c0c14071782d541502d00c2882080003002e803070140c5940e110700100840250490b40002200c220398a981100c2c0d030228801d00f111150a028190009200c0303003603125906041c01c0030b990811500d040209401c03450688000480101e05148030520010340709005100d8010383c01c040c055403003880d065161440e0300001c264580703001c80c8024101070385c034060481d000c0700c184202c10240c4904015130310036540e203080032500406c054080000030301c83c19a000030035600a901203041d20394050040c0d404e1011540340c100050400d52140f03031300b90040f2030f981002c50f5178000400b84514 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 564417239 1250 564415989 564416011
    0x906130e0f07060f091e15020f07320d0b07090f0803121504060807060302091908060f07030b041503030216050105041502030d05010323010218010c0201030b09 70
    0x2803207404071034501060b6030320503418000008482602d00e68441400402c0c2c5000c00004c484180b016600100d074a01564440c107410342c3c0b4049900901e9034003240c115106040c84085601844d22100760000d410381082d200b079541c01d410100d0160200c00c00d03000d43c0808000030000c14208040307488000b42040200c0f816000500f920005100c21f1a0344010100035050303190003541000c0c00c405c1c2c0403124807005040d11644000007042c0100310358460300303e0310140004c2006d607190b881d60350602074041e400c030a03989407140341d40300b10744c1070311031152040201160a110001d01a9450b041c0d03818042140191074071080549482c1d501d10540c0701c601070742e071021540318290030403180355050082c00e1a0560100302c0d07502902d0441004a60380c09010707542591003042d501c5071800c801e01e0040c0e1462249900425200d030402000001f81b0606000c50089110107480000c55039541215240c200e10518030500d400002c08589003000394070030240d1314460f51040c1000141105114000b504011040394040842d07 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 564418489 1250 564417239 564417253
    0x512071103071211040504050c0a0f05012a0623090303010302010809010219121e0e01060b07051506060903100f150b0d150b030403030e011505010507020906130e 71
    0x281801c002c207000800380c810a44040b500c040d9581600240c0156105115544500100341441400c1c04800b1080000520f9400364642e11105210084078070b119040c0401c1010b40743c003102b100c0342c400307000b0180000404102c120140355241c0000340034468038600f06102d101900014642c140104601889100d0300840e1650f14500c0010310011000301406070a90042c40b0702030300708100d4403003a201c002da10b041c10070b4505124603c0310007d0130084612034801668550341000c01220f64800b00c164841d079402484900c0c3c40c0d294042c40c911642e072000740940e1001c46030341013a60145220582088000307050a1804501000007841c5c0b10780d0030ba808043c00d64030f034490420040706224040d100101e00e008107110302e11340701c1702c41914005c040841c01141d86407041041441140001c03400901415080151241442d0a000380208940107598510350301c0c1501c00d002d007402c0d2403003071012904165605858406140e082c8902d400c00502181e4000203d4003000040e003a55014000c03400d0fa201c0020101 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 564419739 1250 564418489 564418523
    0x206090d030b0f040902010323060f010c030807050c0a02130c0306050406050a06140d0c26060607030e030c030111071b05062a03030403090905070e011209051207 71
    0x4000066180e0428145044910a89901d0740c00b502c80d200202180c0010300c0c48101c0c00180c000c0c08000e1500711403451183c074949038a00001c1549070140c0c005031605c5d800c00b6030040040d2100691000090b0204416900103004030740304200600e6902c1034001541c00c40b084c5507001c60330b401e2220102d6480340ea00c0381c0b0300b82c10b00b035858859013004102c101d84c1404424940b00c0410380e030380c0c0b09000f21007c00080700c103c60305281300f00013150002032090b5410002c00ca20b84034010911010160600a00001da0081e50302c030800c903221311400344070300030000b921f8010103030b609907451620b0030352694140c05115100852070303a0a100d10000203441030407256a1380b400c2d01d0303d45a0640d03222454940d00c1c924043c00d02c513648070f00c0140c414034800140b80350404031001e5540358225140304d1040c61144070000802041543c00013122003222000354040c00540c84001c0150303940c170200d0000f180019405040d08a145100f03410218206006405460f0001540c000500c0c02d46c0c800031080e207040090a001c400 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 564420989 1250 564419739 564419743
    0x519060210060302010f051e0301120b1608180109060f0e0c041a0609060c07090c080702010912081005040513030801050d08090d02040212070e150c0303010b0f07050706020609 77
    0xd0007680010100312040c29903001a100710201c4036110100710b0086084400c6216a6050303600d04400e900000da129a52101c01c8682c00c1c42650003214031301070410115140d0309040310746500028031601e904a00d644c0f0740c8840507401c031807000c0c034000350f64903040102c0205156104684000c110814003040000c11500611702d0a83d0b0810220300075407402c03031002c0e00300081d8010004141c10403600c2c81d0781c2d002442e000420a01485056130580c0c000c1940018141900d507000740a03215480d1505c0406a4610806900301c5050710000750a2101428009038103900c20035510f54419900030f0410801901c4501150844004a500d142c0500c0e90510706401e043d00110743d1801400200d8042e804119250f40300b00650050710340d460301071614038148204559039501034a0145200820640851810703a45c028090804c0c2d0004e5800ba10002a0354081d100c6140c00326a80307182c0550007503180d40d00c2c14079941c6140d0f00400350754440140a0140a000132001d10424008000360350041c141070a2046403d4 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 564422239 1250 564420989 564421003
    0xb0a030b06210112031407030306050915041104080a02151603020709050c030702120c010b040207060506040b030303060f0d0c031407140d030e090405070306111b030901021e0705190602 81
    0x10203a090f80111140060f5000010301800240320020581f40d1481d4541580604402d40115074000340f048104001484000a4030030100802c1710300380030101c0e1080e01480544124010f50945402429040000d800c0c03400c81c0e13601d001ca0b6541100c3c80c09459910384a400032200c1e0b07085005030401c1e4801c100030035840c003819401006041d0200c1c9942040710010759074503d120f0055070005d1000c201070403080020740c400c400d00030f00640150350750400c2d440d00800400040710418410744c0780051007082e504000090300c0c0304070005044200804202010400c800002c02d200b2556440040350100011728900d0300e140305614904010700c00340703050590405c180034103801c045020702c80e000c02c114040b0342d0003811742c05c2c0d1080c244c406603125225400c0590409180b0380003c1e20341d40c103003089410047c540400612103114031000014440c420540c00350f44902c40e50000c1c074016405600541e01d240307110810411303414840b004949005590340c011603452a4481c50442c16400000000c12803560180015 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 564423489 1250 564422239 564422249
    0xa0305010501140432090102070507062001060605030604020d0914030304020a08160501122c0c06070b06090712050702010f0c020a050d050a050708070c06030b060c06010b0a030b062101 81
    0xf00d41501c94145d40301e81e0800400740744540782010400443e0304918294122504960000143c555407901c41d0b41c040c01d6032400000c00550074084529091802c00c0604c503d0040e9542980c0302450350b10340c03204100280d04080541c04040d5036403040940050b841500d081c0c4200500c501441c1c4914240c01049540c00d40d80e40f20040c00d0300705507203400303c100c0e407000740340d06a40c002d00f04000716a100700c1d018801402e507a1024848045500c44d62883c03071000131000405c200d01802140c040012500501040d40540c03000117000c0445440464540c2c90080700d01984207809203090385a100c41c203a80c4c141510300c10385851000d80d6448404001e41180350203028100d218030300081c4151903140d602d40b035560420a07100003c2010201d200d81c4c1c0c50380300e58200c81240e40c0008030943c8590311420084060002807042c28003103071030414040600e092440545d020302d01d140c4007514882c5e00e046400d070011b5004240100405940d81039510340ca5407208080c0c25402071445103c01350048004008540842c1a088 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 564424739 1250 564423489 564423521
    0x3030702060a050a0b1801090c050c0c040f0905030a0302040e070309020d060b0a050303040305030d1b050406210516080c030c090d1b0803030901050709030b0f060a03050105011404 79
    0x8000010350001080340d0028a218400680c5540c0c03007450f08003c00c04001500c1d4400d084055a0b80001010010303541640c00c1000c0c04c000c11400090b056406210321566034502d6000b00004019030b24055000c161140181c420104404205030b47d481c0c111307400b151080700401da003c6000d000030380010703a42aa000c402814100b00c4424a90005680e075517012a00070000b54443d01c510302283c0b2000c001000400010341129112510f80c50001c1d00e0350003012620180916102181c036840b036800420b00d048003c143c075034610705410050103c45c21018018031422214480402c02240101449120310550440d20411036078241e01e8002060307075102516032144600240f003403040d00305d144030848030a460116042d00c102907e80c07500740c41d9030318903000091203006000000200580084000d62190503400c00800031980d03146030940700e03103102c0d010141030132240070001030302d0700742d0414a2a00020001d049010003a40e99035003909652003600200381e40e01506840d000581070500408518060f9110 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 564425989 1250 564424739 564424741
    0x12304020a0e240103111602040605030601380a0f14040303030e0c030604020a05060d0612060905070b0a1d01051e0c010605041b030c0c0f030807080a140105010f020322170303 77
    0x46c48018014240e0390041c48034443c481c83c04543e510b82c011002801c000e03080c0c039482d6a566403100c400d014105110101e0325238410402c1c00200070403005c01100f00c0081b00203410403403180b20482e0a0700800d114002805844c00d4810419440600540001c510039039003c00c51502c0b482c0303032904040f00303e800c0502a500c140c0510005a413041804010341b1402e446807a20b4441c010405405415a6404076607107940717100c2c682e014840c8903048403a04034010703411a49203c0d52500c284150b8802c1c12282c0001600070742102c07005e4000c0041c00d2801410525181d41045107031608070110409121041814584c00111901500000c2c0901e1004090444080081801903174814040002c5102404105662169840c0c1054085c4004c50f5015030060303a40007504109140180580400b0340b00e10020480d121b0000c0e85062a50042060034003e940d420280c84e46032a0040d508011070401340c80540c00103102130340f520b041d040d100300c50f103a402400c0064060314050703800881e403501d800085090f800400c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 564427239 1250 564425989 564426011
    0xb010e09070f182d150f0306020c07050607030e0405040c210506071d040906020f13091b020d0c0503041505121b041e180504030809012304020a0e240103 67
    0x1504450f01300380f200b0000718408031103070107074034050041c0c1e00504c0716916014004424441c595014000d5001507404542c00783d920340c0b00304051806809001000905403030100700b600d0400d82c0100c1e404c240305600c00880785407103e8a4480d0b201030003121440007100203030b003e0203000c000c100b455002000c0f0f09001d81c1500310030000c1c000782401d00e200c0c00d0055458036180b801708040c5504450824003071600e07180d11050300300c0101080901911a001b01e03107003010aa601280350388140030b400980305d50018207984c850208184d4207224510f800784d503103000a000000754441801700c50180c0e01c6480c1d54042d0354180ca00807a04030340e44040c1410600503025a101b03007041a46c3d00c1144c051fa913801d181408403c1850a9102c1c0001c02038001036001c946400306050440340982000380203620036204c0d1282551130308070305422100580800d9914103114094040082c6a80d1358941d00a400a000180c0140c0c84058010741d490040e90b40060450055102d25184009503828004007142440c05011040c084 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 564428489 1250 564427239 564427301
    0x122909070308071109191506120506030c060a020109030320030130060b211c120e0601080d03050108061801092004060b070b010e09070f18 61
    0x5804002e16210001070058244103240101489208006003034070203503e0a04032220680c0c03d14444104c81a0512004950303140b44c1089442c00e41d15503a54590105000e242010040c14003d00515050701840307403800410b03100d010080c040c1c03a100d50000303c0c0082c803901d00101112070306074010b00354032848105201601c2908040f2411103181d180b0740c0d01da001300324502484400c0301d900801c4040c0c0301c1d15901d03c00c004881d00842c04544d4201d441c04030058042c040d0414008000e40c1c169041d80100550f03a04052b000184040c044040d8030b41400c80118982400c0704540301d462440d02990700c110300410035660100b028081003106454240015454401880d0ba1408050800740c00010f01403520300c50003009510841c1410b412051600003000180c11400079100c0011070280202d00b010000300d0b13103d0101c0e049900441e441004003400741e1030402e174081d50080140c2034120074083c0302000180d454542d1903180160603010000006868042200012034481c0c18114201001d200345040d80d0340c485e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 564429739 1250 564428489 564428503
    0x1704170319050a18060207090c02060709060f03060f030b01241b020f0306150f030705060403200904050f1603020f12010219021608060402090c0d0204122909 69
    0x52414019201c0f110204281c038442040d440040f4010320240380002d007030b640007542c14202e40b807000301045183c02c90a070898507940b08464036004210810300c10460390784500e42c80c00d45407603a4a00000c070346482d040101d0074995681d0055039200c20410050018440d80f1401d1120b800460040c0c2103000e01c031800c0544446110403a50342c91a44107031041056484012007a810550020f082d1030341031500848103100e0702c0c104c03030642d070141c040c2070a510014100018074034155000140410b00305455642c54030710b4002c005117116100034010f001d810b1651260100c00340118454000790410482ea540890300e0403c08040340307a00032054400410247c0c403440d4415903403c000340e410040080101030b41074060b100b04c540141d0740031001e00104034400c0d40810403800120602c020706100301d503240c0f4000d54981003610081c1d400407200c030216a5920300c41004011311540900c0c090f04150f5250640407a0401c500016161640142043e840c80400c1c0c420400c0e0860340f0802d202c0c0241014116940d50700700c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 564430989 1250 564429739 564429787
    0x7051c0507240b0904080a0201110c101a0d0f1203140703050a0b1c0c05061213060b0303040e0105121b060c070e090f100c050306010c030c17041703 65
    0x50800e20b050386000e1283c024142080014103207903054149480d01e18955844240c010005500e840c50b02c2c0e0340c0300c40030422600c903424002d00508102800040d00401010380c000980c0b03242100204001d01030300c2e2050300300c080d140981e044242e054520706110a40c00300034106902054a030503001c09880210503005070300b1041c03902d80021030381c1d2003c540900402c4080074003503005800444a0710030804d11080400d4551280e54030742c541035661020f000c1180591080a1001da101d100003c581d4040703686900b001d54007883c00810074091540c0031a0441e84203400284134400c1000c011702507400d08020180c7c8075004000180340b50b1419401d01e40341c1c0c1d101544c01520440c4006101c40da024010854107002d0310700404180350707504210310020b41d09c641004000003d401002450500e042e000d10a8060b5000c1d59161f15156131358410045540c00201c071022824030441564800c007181c03201c0c111031035480247c40040d5440e401d08904c00b1245400d0304070005280c2c001c0001902032400c03800c004680e08 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 564432239 1250 564430989 564431033
    0xc1b0c031101021e070f050d05030a030e1006060305012112050f070204050108030408250b0d0204320409020f13090215070c050f06120414010207051c0507 68
    0x1898100403401d01c541600e081c10145007000030303201021808203a0800300c0f41b40c03c6020f83c08560381c00a001a465819902500c0c1f6041402800e401c2070007504441c04412180e4103603140354a000b410315040b82c09a0b0407040009070b5440052240a059420b41c00038200551071503150800550740340003084844070824000c00030046902e0340038440e844152040f940c1e004006008641c0c44540c0300d6540d8016225541e074502c500c0d04511030b85100700d85400141f031005820007070350605000d41380802d64042221201419400c00c0002240c0e02905c44000004424409286825201c000da054003d58940400c503c500d1411681070300683e034080c3d401021040a9554407500070009160070020046071801175000340f10458402c6003c600000100074440c82980115003068403402072100c00004c0c8280207820410402254005a0795500003590080c800e400038907104084901c642e0a80c0c01c000750454072640042542c9030125070b14a11140c1a011620b0300318101400c0e82c03a042c0030803445a00e400000 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 564433489 1250 564432239 564432263
    0x91e050111490f0c170c0a050d0207200907020d081819060f0b280906060f030e0102030601020307080a032d0b0901030210120e07090c1b0c03 62
    0x450b451600c80d9050300c140c2010a070406409203881c001d050f04044600006142502c0c419429000c2d610740c030b00382d00020030310000d540e03100d0f40c0400050f0301c521281c0d014080c0500401d80c1418540c0000c2c440c40d445001840b92011881000c928400e01c9a90f00c68495031900c1e003081000c035400541403026802d14a08180b040e1168039a00a010382094448506e0b4000e480c4100340c180c10040240090a00c40c0600b08004004500f405c41183c015940e0540e1040c40c0f05145072011004280d01030349a500781003420010341d03895512904507501da07408000400c0d20504071740035107601407007215482005000290714629150b07000079264816a08018008040445e0b40c0441904c0390b03000000e48900d10380701c110400842524500151070501c603500300b09041507072901182c00d294014904070390740900545401d4002240a68031102c2071394454a24a50702c0400100700201049008001c00041d0702c00a24243c00410061441011b10344000a4029800a00c030009480c1600c10381182e422500903610 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 564434739 1250 564433489 564433567
    0x708060d020d0203070303050429030103030f0e0a06110c0402160807080c030d02030402120a1203050c090a0e07020606030607210f15090b0312071203091e050111 71
    0xc0c0d288000c0184d0544200d403804401c040e040030003401995251540310214184115180100e50f05221010207088002e02c01000000d0003060b078401d200c0100c0c1000b403105544c000100c0c40301c41140d8010800200e1440c50f0980640f001d2214021403601901c00351718041c80f0b15810808203220fa040100340000016041003407042060554111000c01000c0d03a58803150002e0a201079041650241c0c4a843d0743d502d0001140000280c0c03040703455201e0b0070700c1e01000c489041580240340003004040000c408200c1c0142e1640c8001081d8003601a441400c009070406610081c40c00c200105410b000307038450024000c0c540c0e08150340140108506441d00300c0b4a4204070b500c03014020049074601c2082c10009071190101003002d0f540c0558008010401101c1c01e56400c046d5141d0341d504000c0d80f0513104003c00c2010802440050030918054100072519074403503542c0c034440c44024410404100314011452041060a00402980e44840c1c550181031030b450941c1c51814010758004180342502c00c85c04868 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 564435989 1250 564434739 564434749
    0xb041a0d020f04020c030a020f2e0506011103130f0e01031a060303070606030803160914040e0c0918060c04050105030606031b04091505040603080702061c06030f0605060103050708060d02 82
    0x16148141e109032500e951800001030b40c0c41909c00101b4125009150352501e40181007601e03131040c0d583e0a554165001d01e000902d0008120107820341c0e04125001c809a54408000c100030142e4200342044008842d282001c94000e00c4015000745800b10246070042020804c0900111240b081c0350405d4440703500c4280c0080e29500c5041c01c005c205a00303201c1b0002c01d00003018040d41c401c1c05040e114220310b60308080704889a40f00e90182004610481003070114074240b9500064412101d48122100740c030780c0310b00145640104590b00c0e010440d40140e2100000814800d139508003c082842508144c1004006000d60200900c1c840c003440340400090381010f050b580d0705441803e1108441e945540b80d105200142100c0700c031a910b86031601e034000a542c20144122402c483d04603200508080c16582040004e5101c1201c4000f0340c5580f0070102814080d52040000a500c45c2d4480c074621020f40c076001c019a4401840c42e030601d4501030400514a801604090303000c803044410f0b1801904030710004e1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 564437239 1250 564435989 564435997
    0x10b0d0e1509010e2a120f0a031407111314180c0108220302160801060509061815010507170a0206010f0b04030b27010b041a0d020f0402 60
    0x842621560300814803120907401d840340a00d20140007032003600c000716003c5540c0d010451092800c0703c80b9a1805094640d520905040d200c4000c02074901c138894461582d140c425100318100003500b0a11f0b81808042d080b040c1c3c81030620980c2c8900d41020f060f0b4031003000100042c3e250b1401181281c400081c41c0506a0181e450685e280f00c03184102d041000100381204121100448540300b5403044150075801019224440c80080c0d60280001d441d00b40c0c0c4118011001c03000b10203602c01d006418110043d41c040c01000b820520380002405481c01d0100180c0c404054507980c0210030b0800c8100032131500103c1198007003d40d040c0005808404001203030103106405000d0000d1204a4000c814604414010152070380320742c2c00c40394141d0b00c07404c145024006610039030703240d11000c00c02040045d142d03803800c0d944072010309035000940102429500062031f91074200f40040c2d5490001b00202d113001d12038640321200044042c500351802e400030a03001e042d8804040e03c0340c1c50340e100c03606603592140c0480e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 564438489 1250 564437239 564437261
    0x91a0304080f0304112b080a030b03070e0f0114060a230a0c0501060504023103020904081c051b160c08150a2a2709050114010206010b0d 60
    0x102d50f280f40c20b04211210380816888640b01d1890130040d0700c3d00b0305c0201d0406000c6d030305208500b036001440e82d64880382c5a1028250106050b2a040ca0340711b165414000e0340c00034003082001210514090303c554207a640b050300200c48440740240e041c1000d484600030b0b2014003075203081c00715617406640d040c00c4054030703031380c803244c1c40700d2070002e500300000381e120106105451168009019240d240c10420040e40503c24503405000150704008403a1050030b4501a21001c0800c6404101600c0750045880380340c3c00c40b801e0382d1403c400108030007a01c0f0303049400400001b89001c01c0000d4103151361248036100c6955200c505507540031602819448401d6066802250b1007012009201d03501c03641507403518540301e50401d40409110000703040401d28001c007940c5a82ca14100c440482d01c10303086140c80b40340891000100b000300081614248041c207491445135040035500c805d61031904950780e00341c40c0142c03c0504210081c910445050f6000100030381036480c0410519100d00310816014020900060300c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 564439739 1250 564438489 564438517
    0xa200a09090c050c070e070e1c020405010b252307050d063608072f030d090803030408092404090f1503260325091a030408 54
    0xb0a01508580148401c000c11020f0b58902d40d590015102031250495103a404100c03400d640300310a107808640b91802042c2054080401d900c3d0750089000c071a004d801c2540d2108001a84554070520410700da0240ba03141e00969001c2d100951f0381442a000c00a100590b10701c0742c902c01a18000f06024810250001501c0b14003804900d08010024114980c2242e00b2a180c004090a5910401e02c0390030080c00b0310300d400b080480752036a030900d19500000c015204024440d4003802d1280b101e00d0482c0314400310b09010a80c0c900c5201c101130a04014040e130000780290100104185400401900d40c425085100c282e02d0341104d00114110900d42c1112412080c4865034402c00c050415018209403010742004001041d0880d0804044425481c900800d1400c0c40b0800c000207040140d48004c0a070300304c0c096460301d034880b50394500302d50401d0381c403201d11401c8103056071207411440c1d4102c0c1040d025807400c00c0a15190504203407145207211081e9400c05000000141030003107142c01c83e0000c041e4030030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 564440989 1250 564439739 564439751
    0x303020d20120f01080307080a05120f09010513020108040605092d07050904020f2b060603060c05120f06010e0a180e0d1b020f190801050a200a0909 65
    0x50601c0c560380001c140d41e0440c00910041801c161060036090f0583e180100218a0300010352164915070704401002000c01004100b0403404683c12079100d400385001d02468441c0303080c40c201d010f0a580f0000c021310b200e51201248903000d030303920082154005801c00d200085c0b90322035805850030040e402d41414884184c02040d42103015050a100620107003510941e000c194451040080102c0c00352406584001c540c8040d00e154606121200b0701031000d140101d0020103030000a101c18184800191240f5a4070380301002800018003401408042919043d403600710f52010300307450504054504080c0c200d50741c0016000381d001e0300b21491002c000419442050b5035443d04030410b6181804004040b9050010310720341c4100c005003090f1a0882d5499826031010342041c00d0001d4401e50780186d070b102c0141c1600c0689601c403003603441441c08521000b003400c641040485402c1d0744015051403d0325141c01004a007090000c1e510000740c8400b40401680c1d00030401003100c29410035003049034807031300d00f00f = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 564442239 1250 564440989 564441041
    0x3010f06080d080a06060507080c10060807050406051804140708060f180f3d0902100809060103110d0210110d020f1c1103040303050a0e120a0303020d 66
    0x142d1101d0b103080556501090360f03201c044480c10b07035060744640004140e06001850000c0d448801070841d001c00c4e6000c80325004210040d01d801c4c0c03440b6030300541c40d5410500c0280181d06160044101800095a5115003998203141e840031449006202609111120354503000307007941440380e48010202c1034200c4060341001140410601410349944d001c2c0e1a0004c001c800464001c82d14892002280000d02003203c80b500c41d4000c00030f002e03148514260f01009080c14860b000c1160b1814130f07900d00c9800200105280305001c03140d40d40880c2803083c040c505080200194000036401d0560350b0204820010440f0751002c40e1420116010095000c0c0b81e4282c2840c580d40d00a0082030303030b40c0b050030440b0381ca01411030090b621500c180300382c090141c206004000d40440c02d20000640e0802a1401030f11050000f0b00160035074000350411000540300003041c5952a51285008100384000c664141540013840b058590328582c2c442e0040030300d6001325001e442c40c2103607400062a01502c1c03084d54000b4403d1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 564443489 1250 564442239 564442243
    0xc0801050c040f121a0627040302010b03060118110906160203121231060b1011060402092205070e0f1012080f04080a03020d02011104060e03010f0608 66
    0x24003480848541d0004001402e0340f40c4c1d82d003080303116045500c00c521030040480302c1020900007843c00360494555002104a14840900c00c0c1d284201441d1403261801e2501e002030a40b004810304a100c3c0d07001600601c1045a000420074624441140009103162020380a0902c0c1c010751404c10b80c0000041865119002400d800e54401c0c0c0c42102610a17801d800341c107917280c07809600524a540109000001c80c480814402c400410241000041e95242e88100050361a202d220045408544070f001c4011103040000a41a04240500f0300c540460300b9441410303036800780244080c0c0705525410200305e030605540b1708420213061540f002404010f590801c00c2c0d1301c00c528418a5405d4282c41c00081030980019841406450b98104440c51585444d040883c280c44000050f1020702d0200300388000c4040c00c00080005200140251030004070a040207810407501d1030000055905000882c182000400c0403141660068100715034009801c401007801062041d0100818610700b180c080740315000 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 564444739 1250 564443489 564443497
    0x15090a02030c010f0c06020d060b19300b1f03090c0906030209040311120304030801140409081c02040902030406060f080c1f0315031103070803030907030f0c0801050c 73
    0x80c0c0880e03400d0b400c242d00444003200107011000028403c8240361000420b590000c0c800a0000c110100e1116114010059203602904c082090300703101c000440300c6a0f42010304d91401030902501e0340321420800255119280223040254030840e40e0700080e0034943c0e1410044800711404103010011503491142c09070050035490f10544581c07801c0900090200b402e80074030400d0301d030302404030340c41349e2941e0350191007900c40310781440d4190040000c00c0040300311030005103100b41c1c000e41d2003a042c3d500d4507101e42c001e0000c0342003060282d410645050301003550030044072020840b50884010103c0d4070782d030031802401030703402c0703a18941c2c000800d100c2807100c0c42e000b00c4117503a2404c890042290366060796a50380e102504035a90803440482a82d1411600e45440c80b00400c040d0034045803011000038440d20000158000312148a0b0580310924542030422074500500010b01c000d51440c1403000c40c007503440107207200040c610911a8645410880512410802002080000e01017824494031010090b08 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 564445989 1250 564444739 564444743
    0x32003190309060e0a0311100c0b0c070b01080105090a030f0507061415010c032307020405100e0705070201270b0406030b010e0f06031f12050f100507050a050c15090a 73
    0x1a240c60200f525015170703c4012a948403101240241d400003e0040055660703400a040c4607c28034020045080b80040c2d5200b1030003606019030307502c82840e0184207800103801444442e850300041120002001844545a5070182095109181c0010003100e8038440c10030010400d504099100900c030380c4203503d06001d940e511020381c4440c00d54200448603001640740103800503003060300c40d13011941181e501c101c40c0e0b0b00640c05a840c0c441c0d0f80d008203003503c2042c0e4540c2c04001c01103508000b0241103075052a0071802c140b51580c07810b420780c1c000806114041030346178050542646503450442644082c0c4000b4034124081a850b40d6444001900504418884c1d5000c116112084182481d1010116a26040082080d400c50311a8400502e10b40150800015022039599000c1160f1449003040340035903100e0320041c0303800c20700060342c1401d10071040551810f050804c0144882290018140c1c0d641c070070035181103030b110821400b0340c51400d0304c0641001051981d480500c1098103000c00d007815694 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 564447239 1250 564445989 564445997
    0x901080a05151c0605012c06010302070f241803080604020903061006090b0a080a18080c0c0f0303071e08071704090c08100501050a0509041d06070903200319030906 72
    0xa81c1c0d0307001f81e881580d1018404110713032041a00c0a00c41c030062903c404e4000308107240041c1840965651000540d0b0611015590303076000307080c09802078038601542d8902ca8005501401100210001e015905041280c01028000d00d400007550b1a261641900c1e600c4e40c00400f00c82050515402020811407a802620005192142c02080d8801040c0480d4082c081035642c1da5507a650307203200c1500602108103050b400700030b050a01004602440c000d881009405c201600354520340008000c511281001f0f1035019800a000da1000f10300841c0d40d6401d0540e00a03068098000c0310300c1c1600d403d104601005014040c0d851082001182441c040c000303640309141d0400c50030141d05010303102203c0485500e06140282542400719500c260003800784d40f00f180c01d01130305040303c507030005041e02c13001140c0715030700b441e444140701000c0c40400810ba008400340c10071102450454899844400c5134209828a100ca508500c1445440070801c03840c2c03400400001803007a24051400400c904172902c00d80c0300013 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 564448489 1250 564447239 564447241
    0x607080d0212091e0c091504110d061202090a090c0f08100513050601050f0a0b040e0a18120c141902090a141602010b091f0b0901080a05151c0605 64
    0x10a10034540c80c0742809503000805c04441c0d000c0401144401c014606001c10103010703101105601c1d28000e0360894046c0f000380300d407034160000c8036400b02c1d44c281c2d001102205410000f600980c40d6681a07542040340c00b200400d1400190505910f514102ea0112000c4d50050030001905400482d0b000490544041c2c10700c6140c80e0b0f44401c000c8045001d201804e160018001000306107001c0000510103034024110640c050782d01c4010301d2594205501202003000040c0810a00800912604003011000101c036004440c5c6602d812245608034200d51051080d1510860f06020a2003180d00d08441d076030080303da0284910071850140c1c0c440687c1240160b0008000c110f5068044c01080040d252010a140d0143d40700341d45440400c1800b01c43c10159503071199611025155640580c6c800e0949100c0910003420068881c805404103a010280c5880e091007076003041da07032000c00140c000d10845c402080c980c54680c0c4114a101d184481140c0c4980d0554070440f90906001521072660b02071a010406 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 564449739 1250 564448489 564448513
    0x120d0809011437020c0a1e0305180109031502071b06020c01080c0c011508070b190c02041103072109050a03110f0d0507120f09050607080d021209 64
    0x5280080c1d420303000e140011600410f910602c005200b6405010030707018401c010710300c0e4000c4101d03801084405002e4026116410070b00003131491401c40c03507030b0003500310088001c1610000c00d0383c003440c10340051441604401c4115a0310031221040030f140c210015030080798041c00e5400c000c1d0f20004080310450310b03224100030241074840da66421198260090140241070f140111001d4000a019081c0988107101c0424103080910a60340c09481000c540c1d400c0c5400c00120501e03000166100440445080103c107982c520301c0c80740c40380741801c5800e0201207846d6910014024100b8000244d080c0c1e600401000109039205c9403c159091619140114508000c00710000355010a000640a40d009034041000240701d00766050070407100100b03448401c40403004950401d030420310214005080460250140301451100d110742c91450f0a218103000d090341400b402d10006071003000d20444004c2510300500c200a03003140c1e0f0100350340d48119030b1070b141800700414100e01501c10310f100d84902c07005000c0d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 564450989 1250 564449739 564449771
    0x20a0602192003040b0904091b030b0a0c0c020111011b03050601090e01030c1703120a140106020610050909100f020d060e0106051225020705010e0d03090311120d080901 74
    0x1814041150183d86000d04001500e4020351115078115041a0b83c0c011040204450003000e02c902c001e61203074824401c3c9076051103006030718080c1080854502c1c000826000613000701c481200641d0a013002446a446580024010098081c410b0b00b024a10351808018641c55400346200701400d072a0408440c1c0c58400101c8421000d000c024056140300134184134a100f90041d224000d081402180c0c40d1400c0c41d8a40000c1c0c7d0002d640300080a612800010000f410400c196805003995100600c03207480c0c805141008102540f146602640080001c90401d510030b20548652401d4501c05000ea038001808007070095100401d1440e00d240750940120303580020600450480d001075443c103040118a005480d09130801528000718171000110440c1c295003035044a40000301240c001c3c019603454480050540440000d24501c2210800c0e443c2c1c0020b50412031a0301640e401c000c40c0003803143e480c1d0104041140012100f10244180f50b002c09805900c40c0c489407081001400034080200c402c400f0700e03 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 564452239 1250 564450989 564451037
    0x10030b0a090803070f021903140f090a0905100b0705030d0e030409090302030309010507080c0307050a09030b0406140109110d0207110603010e041202011a0d0f0204050a09020934020a060219 83
    0x1000590031048100f058040721010b441e40074020ac8010745898401400500b000d0300c04d50204000c0307a158030400c00342c0403030960358800928030014010b2512145944654603842401040c40a0f41e48e0b40300c1300081c0d19020419140036180084e0108201c008508020b50399801c00c44010b100c070341c203120028145c1031080079510300420f1982c16203400c5032241d40c402d035044d401038a0103408101540b000000030810b10343d40c1034011801000009441c1243d2041d00328114016000a0501810618800700e83c1000c0c10446c0c1c0109a03503038006032078041d20320780785141d556880503440d440b0002000100743e0b003080c01e0f5aa03000b184250420519862181410303400c0e100705100100d0208034055034140030341091608085d4682c420b10241000a1003540000c2c11544195601d41c211591080d9500440c20403144054011800d103040104c200300c0014a040000503c101041034900704448100006000700107036804a0f90141041d920f6041c0384000d5148031304000100340004030441150254464103c0001d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 564453489 1250 564452239 564452243
    0x20c090901061a07080d050c07050c0a0803030105011107050a030809031b30061f1406030a020a12020a0e1810140d0204090503130e10030b0a090803070f0219 69
    0x412800151521440044e4011040a43d01c0e41410459210040c005124a51207001c18520003515000c4509040d403500d044010b62602400110f80207005101d000010340c4d045503400d2801000082c02e142140303040c0701d00da5000d01d03080311081d04040104030b0040b020308100305041d02200c4a005c55116245250714107074006681182d2001d984031042480c0c100c010740d90011144456024440b0402004e1815100b01c881c151395034000828040c2a20010a5590003131158a0f02807107241000d40c0081c030607100c064442c055039940010300002c600e008604150409035182c41c11034075038030341c0031024001548000300c40c0c1c81490700080c42c100f80300868150704e00541403d64454032481c103041584020321001c000c004e1f80510547d40c10f00050b9500d00500e814148900041c513100e0b207003820550020000c5030000d10302c1c0e03070903002005241c0c18220b0024040302d400c43c845c128540c40e200e5400d00200700030003028109104c00410030580341c4e001003949041d040c455084031451100f91071240300d0204550340c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 564454739 1250 564453489 564453509
    0x30203062e0b041a07051606030606030c09091d0a0f0b0105010c050c0d050f120c0c04050403052212060c090b1303021e0603042a030c180608030406020c09090106 71
    0x203110318812181c818041400c0030345013528040481c1c40b11881d250341c5580700342d400103100d901130011a501d40030f610b0040a00c2d0406020040c0440301c041d10700310741d0b401400745e96662009460320399818090449190f83c040c50584625500d0341c182420320044c121400d40c2c10700150300c00041c0d503501c540c0c012400f058100b0050030000119500300101d142d08090140c1d400e100b079110041c05e04509002d60601c0092541c002076444200d1400142007514240009201714078010800c80466000b00480c0e0400c0b000001003c1a4070590b0300d8403101d28480e4000c20040301c00b045ca00010001c05a00c0b55244100688485000d10b81c0d40d100d0b0b00302d510400000303402e00900d009081006041c2465a40303d41c5001c1da500001001d8a40b0100d40c00e900304940c01d9840002104070602110b0381040f008040e40c07002048a0f440c2801c0d40c5070b4141003140392050b8200c004000e0001f00e40d811865000d80050301c447c5090300e5603190303541c000a644541c036611345482588040c001c07a05045052003800111201034003 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 564455989 1250 564454739 564454747
    0x50a032003040f05210a02060603060601020c060a030626150402130915020c1e073002040f05150405130206220906030c09050f060f0406030203062e0b 66
    0x5243c108880c41150304403003e00c50001250100b40c0090b416418048541184588030120003070001d24011000d00b100380a40c00c100240400f60764082068403450740140c0b04103646143c0035400310010107080d4070207108068440c88500c04040100f256200b8841882c0884a01c40310000110490b075005a500a6101010741c09611800d41107030042007402d4003402c2c0b070040001c6040c02c8001a41d21000281443c0d0700440e00c81d520042000000f8480d80a5100003010071508111620080e280113452a914103017a003250308002074004204000040d0b4041c1003802800c40609108014010982d03181e03140071511500e4280e00c0c10701d481668030078002858058100002a02440340c507500049130040101000242c2d9407200e04841840700c01002c43e168001013951135410445000e0100d0b07080307a10850f040c40c0a0101e01401c1001e0190040411a010011500d181001800800c00307540000e40601500c0c04000008000c051440c030341d40e6070001a41c00c404012002050080654081e040485200380 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 564457239 1250 564455989 564455993
    0x9031c0f060305011e06170c1e100f02060612030d091a0f090606041109190f0b09100c12050d060306052401091a0903070e07050a03200304 61
    0x14000500c845580e590014440780c50f51221429201d0407070201c1800c82c028900450545400d1046200030a0703000341540d00d0950600c403454548101005443c45020b4004040c0c038110304400690700d003958000c09010312000002c4000c0d000042c2c00329940090300409000500304e007890240c40401100c00406149401c0c41941d02000802c00d040040c1c03508030072130704604e80480031038000340d0081c80040f211842e149000111a8a40000101910b0040b13051240c00f001907200d071010343ea02c00000f04e4000d603041080d006402510030030b503440041d40c00c035040302c000f8803002190020700c507000c42666000408003c1010036507100d06e8015004100030f142e01c080505880c801c0004d84402c900542004c584903030390787c4544050300c800303803841c802c1c9220720003681005488207000324810950a00305070140c00d2030090500004002014490206403000418456075a418401200582210996080030b0b08245500600c5030b0402056100407900d4880c180140d1381c203950f019511600b5200360f0034695544c1c1c1d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 564458489 1250 564457239 564457241
    0xc11060601050a0c06141003150b0a0302060307230a080108071a0a1e0807020d031a0d15050103030e13021e0c100509060a1805060403080402031005160809031c 70
    0x11100954003586d480c00039140c520050380c9014040d90356445c54170320590071400c05450000402400b407c2a618240c2c908200b500d509010100726a0119102a183d80d11a030781510030402c680705102c000d00d1180c28006441540902900110003540d4030f11450b40e0b00c2c3c2d00c0480d654034143c0988110070701e01c140b40c0a01240000004d080d400329600c1c0c8140b11a01e03034030756105840c4410102a01040c0d1010400c410320360304001040003203845103401e105031401c0409600484080302e0019002c3d510380501c51040c060351a000282c000c003400b904003c5c1c0e40e502e0400034160b01d41003141a105004212418050310094020b8400c03a02c08001c4200c1d04696440800340307143c1c000307058080c542c040c51075100c40044e00d5100c1c45201e84100300c0a07010915200002504540c4138030789440342c0540da0301915000c141b0001d005a03009900d4108000142c03502c0c0000380c40c1c50012031103610f03807500703007000c0140d08841d100d03222140504585a1811684500740201c0d200c4c0030b4500d61b0540b01e160310a5000c02103500b = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 564459739 1250 564458489 564458507
    0x2160305253203030a1e05060f0609011b061508030f0301051903050a0303050709060c030905060d0621170c060708040204020c030c1c03050601120e030f0a02010c11060601050a 77
    0x1021211070419801c0200d0b050075504200c4198a20365a1050102c441c00d1280c140d2429600104c04200712503d040c0000444031840e424000e40108070108451130b00780d010300c0002c010382c10b0200e80720700900071600e880d05c042c0400820380c03404201c40c103100048105000051f91030f02041b8014007401c6a003000c040c070032500da03e4151a0032607039045c100040418000d002e038110181c004d640c003042030700e846d45000d00010030581c801e00030000c855000e400465800503100c02990400c03104155180025030014000d8010f40c0c0081450083c0402c2c4c10050007440640c414040c0e1003540683c0c5c4103500c1c40012407a80c0102d140740546900b04e2000100428407e0140356801031000f0801406d0100e1190741503c1d581018101c0c40644d4406880307041d9038880e084091150040918007400945096000202191035030102c81d8030064035081c1c0010990300c280306540500c0340d40703249562611301c01c900007406801104001c0000c16800e007011001c003140410690f10580042e124603141000101c02207402240d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 564460989 1250 564459739 564459803
    0xf070602070218072a29010b040b07060e2401080d05041d04053309030c0d0513031e03080604090201051801170103050307020316060e040905010216030525 68
    0x144101d64800002c1c1181c00766900d424a10020806c1703860728601103481d8000c1a00700c1c1c40c0402050008000000035001120501c0d43d2094000c18901c1018410515001072102e00390301c10b1208180900030355644010786412a0740920803a00c900707040344000e0ba068401c0740103d9000f015060710468520303000c01500d0750014401c4041342d0b008140c40350004c901030f0148000e204c48600d5200e1400904400c520780340d0300401400061454503107650030a982d0341105401002c21300130085400b002119131394501c40e000755004070300d00f0901d05e050260b201f580001032310200c0114101c0000704000b81064401c0d100900d40c1a1902803070002d01280d204100c06640310180d041000046020045002c5000680d0017907125400071a1207404c00e01c1054104200e614041d5084d840d0100c1c100070383c0b0f40c050804c0d400741c50103840c0040c00043d01e041603030180c80b0b00c07401344c90740c00d5400d42c00c0000c05521100070b111400c22003082401001542d65801d181c066041009402c040c851080b1020b001c80b62241080c03010703 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 564462239 1250 564460989 564461057
    0x13020604090e160b1b01140a09020607060c020606100201020c07061d0a08070302040c0f020a0803071e0c060c050708030402040b0d2120031e0f07060207021807 70
    0x20300b2106405460085600410780a41303011515034200700b09010401da1060321103000784110304111552040c09480103050843c00743c0c807000c248043d0340300c0204445802c0c1d04200c00b8030990100d084046e581d454180c80e650b000309082407466101c1441842619401c4030b03040054100c0030700c1c20500300c482025100403c2800c407085890000c1030f554500040717005100003400350cc9070b07928600401c01143c001402650901c40c002141c0700006502054503a525940022820b03140d4580040488920301c0310103030540101c041c00320403e60241c000c40800c4031284142410b000007003071018110351038016001c0080452000303101040051915401041c901c21018012002211103611190361000c19083e15260401d90311140081c2c40d5031121008140300010380c0861668003646c16020fa4902c1000d00f8103807424610820030708070600106c22200540403200c0d0140d00d9220b036040103030080d4000f00040f0b1080c41600c1301406a207400441c4180b103544540c680b0340d8601c2d888581d01c100c02100d070800308115 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 564463489 1250 564462239 564462253
    0x315050301020711030c010e060301090504030516060b1311040506091206011d10120b060a15050a02070e010819050c0603040c03110306040203190f0206160b13020604090e 75
    0x10303102403000c2c2c29241e024880c18032038800548145030a0072840f5001c941002400032031008251509000c590448049600010b5107640c5d5040840740fa004007940010541c0507101d0010038001d03181c0000350440070460345270900f0035148110318200e4941c0c41c15002594010301007000345103401c8025002100d000350688030900d95004005040ca0001d030001c1415941c00100700c186a034400a00e103070310104418440010a003480c3c0d12080f040030000c001000b032480c100000c3d082e516001d09550051400d4144101300c5444201d000d865500406012801407040d107100003626841c2c03a82d150304a88090340501002e41c1c0302a1001130b400c0b105c0c80c050701c9505c070303491103111103403034040045100f10301071311600b0b500718110304d071000310fa80c86680014400d074852410310026030750104a0341c40f031a40f400301d840d10200441c5405404540c500300017a5101300301040c00000d1039610515020004d110308904e4a65644210300c514102642c800040e403c031100780424420700c0d4290f48840c030300c01161004c0301d0807 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 564464739 1250 564463489 564463499
    0x190603110c0313240c083601110613110a1a0415080f07051b060a050402040e0607090915180c0f05090609040b2403090d0f020307030315 60
    0x34581c08001c2143c164440710f00304100462034102c040340c02c0204031909620029010200a0941050301c9018200c003000007190600c40c50880310340001c2007404051040044c91514041107400c061500090104128151110145e5000300b2103621070385150080e42003811154403450410588004440d070440448400800c1641c0c00c00d01c84055031181d80038080d51982460001c2c00c2030040f08001c8401d03c003a16041c040a0404002040c0c1c1c4290607192042e200c5460075603006c0324248100f030650980c06445e081c4111a0501d41025101d18000e44040c03081c001d00b05907056071500202c0e001070000300300d0300702800360b03007110380108110035425aa10402c02c0d4440626a48800030030480e441000d0b40c0d642070411040e0080b45840042c04035040c05401c0c401c142c40030850b01d00c00c08140510403640c07000c04510390382d01d1a00340b1214400c2000da0035080000c4d94040d0302541c1c002ea440401d17a214032104020380902c600c51201006060758061820a561554264050081008031080001841a000c25 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 564465989 1250 564464739 564464743
    0xe0418020f0109290702090906011401050408250f120c080a030512130221010c0e030c06070f0501050426091507020f10020a030e0f06070f031403100501030b190603110c 74
    0x101030b0080e01c0107000355502d4084411509400bc2210300d06018051004120368040415507401c5d0040fa210340340003491600e0360114200c030301600004081d03551101d0201c2c80790082d81d00030f903407280b160362842d510703544520707031190764039891003004002580c1006984415942d800e502500f0007030755900200c05a007180d001802030308081d00748a11045075003004a400e070303009010b04040310f180307420226a101c4c03104001c240c8a1700041c0b0690701550000030707401d0400000341103030a82640c003d0002c00c040d041c90319200b440001c40715410340c602d00014421414007a00101218412000104103181180303d0090900194201c160160781c010011800c8420039152040c900210840507030140103002158640540101c1301d0345512402142a100d41d40c2c801c2c3c40305400c41d03c4150700700908000b4140c0d21324040302c01d42105007011101d8900407080c00309a60a01c6081416a4800d8900b0b0001e240c403c0e0a000c275002c1466900405284500c8040080380d010b50301010741e81c00c0c4461038a1500c90106d488034 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 564467239 1250 564465989 564465991
    0x109050d14070f031106100f290d061e0605030a0e010902030a080a1709060403080426090112020306010804061a06070f06060b070b0708070e0418020f010929070209 72
    0x10300032904d2810a070090351700501c80d5a1b44080600c0480b45d13094108400016000340ca0701401849070895464042007403408411140f03a10b18214465580c0c0c440f0080e0540989114031504201540e800882e90007001041d8a1405996465882900b15502c000e10040606000301180c4881d550302d01b280c40142c0c500b4403c0403200d034007c030110f40c0d0b64400d994004107000c1c0b00c4403200c10041a01d0742404004e04000c20340e9a0040e805141030440f54403907042000750071402c045981000b00d1440702d4020b40c1d10642004d0102ca03613090720342c40e201c1d120f26261281a44012111540002e0781000088c0c00180540d00c400f82501c85581e80b040d20304010740108140da44501c505075604404c2d8402c0d0020006c00380039101c00341c20b00745c42d002c0c10119240d0b540081140040c0052040c40303440c3d000110364620170261446800780041c001c0c0001440d0200503c1c413200c0e1000264098a240364400240d07501521402c0100c0e60110381c2d41e282d5200b030008160401030054441610395800700f04050141c0e481d00021 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 564468489 1250 564467239 564467243
    0x8071b060c0b24040911190302011e03060f060f0206010b0306131e0207080304140336060f0316030c02030405092a030a0509010b010e040509100218010806030109050d14070f 76
    0x2803400032940042214403887c1000030b00f03a0341e900c01300c20720040c0d078000d0039105584045854001c405e941100c080d006440c050b002811014102040012200e6101c0d0101c90380404076004d07500681d8988590480340d12007101c8658129030354141c00d00b040d410590104919048000b00e02c100014140040300a03640807510564044801206010902074405081c402c207020301c07801185800c002e10f03a07840f02d1400180c02d824000303c0c80d402e40d4050111900d949015880000c041c1603642c1c08900b00240700350000d0b101e169a09001d03820142102e0b000c0d104940c40c0014031740041d401d1603e40002c02903500002001c0d2442c00c40d011440c840704100704110404c3c9034078000f19a80c2c0360700e003003040d030003c85100130107c0040c1da0411540ca000d90744c00c060b0300e40c40385200341c03008502c650300e09081c00d150510a5100f41d00080c400116034441a09004c0da03c0013840b8240d0f58007895880c1c903802c040c00d90ba1242e40c00780540d0080c181204403540208a92035075840b00ea40407074200306682d1a0550394100c0c040003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 564469739 1250 564468489 564468503
    0x304140d15051003060e06011d09030f1204060c09031110030e0607020f0d05030106080a0b01021e0d140c07060509150d0c2601090c050708071b060c0b240409 69
    0x401e04c2007101034000d080c2c0340130151004208540c074001b03001ca07030070050300c02e0118940c80410120350490810310880b0aa00d4803003812695032001c20880d000d0015089600342c9095241500b90401c4500c551390318022260000320a00311121010108116841019840400c0c181e40e809078034521501801210300c500900d4029041001c10750026501340b805000740101045001c00040c04600d4004e40c01036042801c01a0000d1040b681000503403030a840d0800c1c0e0003492070320b02c0e604004c11400040120040d4003c0e9594407a01c00d03000a0b581984c050303c1107030001d0343c00400051003064802e00103040c402400404c0450004102d1040030070300d5022404407049151522200f100c01500300113140c1c0000c8142c0c400e01d00e680c200c07200e040240300301801550121501c4009c840c0c5030b030384550700340e410f065000940c655a8480a00e000c618038040d414800000030110030b00001e11a0248400344ca0f0b6540040280f891a81c0344294248241e981c08444c6804400e100c500140c40d4503030f8444c1440352441296 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 564470989 1250 564469739 564469771
    0xf1819080408070602070e0703020906221701060803121f030308100b0f1905041d0f01060302070b010611120c061504060b090d081e1b0304140d1505 65
    0x20307843d0500d0741a80101043d03500000c002c008030780d5840e0026034044000c1c6401038880401d000081c400b8881c248e4000549484035468220300380b50782c08e60340c04889401081d01c44080c140500203099400701e01c07580c00190002d00840b80400003030b40315664803409860091b8100f007241421002c0150b0355030000e6000400b56006c002003a690310828402500782501c560742010445201c664040c40780b021215080f4080e075109108050158040e1070207004000b000030031682c90400e060800d2401100c0341c00d503400c2140000a00280280b00f1140440c0d00841d1b9052260300b402015208820101c03d00041403103411203918406204002501ca22482da0002d04a01c0c00d140840c00903092881d240203100e50f1910307400b000800921421140f140c0c60030348003884060440d0400c5102030052030440d41c00030150070b0340c600c1800b89100052454040102d0001d40a44690101550360700070340c050100301000210404016142503444c807080d00703206030882e49038040359508200903600c090303503c0e40d84d4200680d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 564472239 1250 564470989 564470999
    0x13240e070801120f030513050a120c050d0c0302060705070914060f090f070e04200901080c07080d33060e060f0a0503061c110f03060f18190804 63
    0x1a2666005006078244035031003c010b900c41d4840540c40510080c14030500045030540041d6446400700202001000d0158250359140f10f2601140280021034049010741e40114043c50701e100700408942c0c100401e48001ca042d5801c0c41041c0e48981d4080e40d003071050400000b450415405280520518100508420305083d8184520707010030815140c0b19420250070040820313485079125612400300d1524096015500d804030380208040c110b0704801070f61121070450343c2c00301c03040202149403003a030300c61101d551035103400b102c06c1c05007030b50080c400d030020801c110501a182c1c01030032a5090305600480c0c20340d418580903201284122018015400031070082050a420000749a8030070425079115241000390040f01c0203138452200a0700504c6000b101003009030f228100c1c40e98140003a04081c10414003d803c00e44070070f07000070b0788162040d42c0c110700c3e5800c503081c0072802da030298071205400c07540d0742c560901c814002c99080041903114880c165184890403010030340c00c0003080c001d14010345d49505103 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 564473489 1250 564472239 564472247
    0xc050304241d210304080708071a0a121e0507090504020a0c0618080c0105010810020a02060403030b0103020c120c0111071e230d120b13240e07 63
    0x46000100703110b040040210049076005200c03402c2a03003202c060461100000e42060f5000600c10016814840490003042d4194009200001d58081c08100c07545555200c00145026540d0b404a0302440824080056a14000c0460250316200c2c980d003c00e41550300b030344903084082c81c00110308031140c54105122480d40c126881c400580303015501949040b0000f10040d00d096000e5000800c9039aa8403240b25400c0c80c0d21414518450b80481003658984601a01d140600400e0050601c0340c00341c030f804840034550741c0c8201c07441c00c00143c000c0c000c00d950740d44045e0001d06c0c0c140791582c180354013084000c01480b400d1100c5007211001028458688281c10505801c48205200b0365007225410401c020206031401d00c161416541c2d40c6040c2941400c900d07111310b851400720594401c2448800284040394804101302181c0c00003a03541040022901d100ca20681d40369028032500324084040e80e40320b00c4455042180e80000e9a000f004400325211012440c17401c503548181d034080e5050041c084a5540 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 564474739 1250 564473489 564473549
    0x1020d0b01020d050702120c04050903040320152818090e060c1602031006030210081b13030b0403090509130c06120912050d0e0303100b0a0c050304 65
    0x200b8401046001c00981016041c0d100769180a8401c0c0101d844400e10820204216007018001030310501a9003813038500e4903940d0704540000c5408500d241c1811980000924210350542002048017218610004140c501980606403400354402801b4182081c0740742051040180307400c40e540d0040d1042c1c005080303d10340c502c03900048440d905000040841d184009082504841d194606550703070110301c41e5500440c44080002134043c094455444641d00c107075440402203900079140c00b144100c4401003203681000803501c0e820303c42e0503d480020005180f10103400000004019100c6081d00e039110340c001008102c80882c000754403010180243c1c2007407003500390080144880b03550395852503900e61841e011503001d04010404800e18010506506030840e0440b5070b00034181c801098058a00201180c0c000700c1f138208028102003122484100001c00c40e442814203010201045081440900e03140d404001c2d64810806614000c4020460510040c001400c2c0300140000340a0f2201e2072600c0c14071 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 564475989 1250 564474739 564474761
    0x411030f100b15071101021603050d080105030f07030b060d02090c0d18030c0204020d020d0f050103060515221409011a090601050702090414070e060307080105010f031415070201020d 80
    0xa4100f200460f84001c141510345060384501e0740300344c000da00b43c0102d03c0d010541246003808800014004140480841c6281911000769540d080680c0c0f210141580c51280313110200c181c1d8807020003000031803ca0412160041340040c20010580210b03000980d4110043da1400d480700340c0020350120704202d520411440300c0f80f08140340c0c5c1801c01618058401c03083c128010340902e030005000101040301b90704842c41001c06403402c10241c07103000342640060009001c03c581181c544000700705092008104090509001090f9883c504160302c02c402e0040020400068059107038000c80b04c008003221685c40c410311501d8000550310301c120b011034122404410215000b08400400d00c00166840b0b000c0303400d4950103454050503a1140e00c0d00030390381a0701d40c4900506000d49a8085020352105030b140e40609001c0b000c0f00e58454550380c416088900038071401114500340b49003000014281103420f40c2406846c4140c1d81c0607541e4400e02d00c2041c000320341142c0143d5000a45422002c1c15202d0124007070 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 564477239 1250 564475989 564475999
    0x5040f0236040222050307060c080a0531050910052e1d0105040b1204030c05011506030609020a0824041509050a050105100c050319051903050c030c030411030f100b 72
    0x161822230040c000d22500740c405080303440001044102d99010340207c441d004809002c1e020266050203891803003860f0b80003080001032110000042078604116554050b003d00500712502500e400d00300f0500c1c10f0f4185d006807154001100c00d1720058030510328544070003929110001144a510743c3c101510112008060501070300380403d02c000384000081e41c848504030b0b0081036080e1501e05041e204190352110040040d82040307802c1c03001000b02000402250681c0e04c1c2840f0b01c0c0d0710303129805c00b40e001e251030320800215001e000a880c0310080b1921021000080341500c06110300801090607100d2000a00c0e404030100403042041c50000d100c1e09502c51406a810041941404000f581c0300f140b0030445002c004a040e410400d00c4401d10440e4501380c6d04800c0c860780c80c410028040c1158100c590000010084015140601802030080e28445c42e1030788203180c6542d48a8407d09456040500180d82c0000b030b05500302036071740b010049150101910301c014071210f00442c0201c8280d43c484e01031903000e6 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 564478489 1250 564477239 564477253
    0x1202011b0305070e09010b0a02010e150703050c04090f091103010924021c091109040b0c030c0c030a031406100507080c1507030605040f02360402220503 67
    0x11110440000c0c0c0400645000314490300c1d03943c812566941034040b4181c0c8880c098000040b6058800c0040c0a0401b2070340003400f0580001041546500d1403610211218180b00f0010780e03001d1003030340016401000c2840003801c050300c841c119011101c90112000c4a65070fa010186d00340001280e07690715500c0220001d1100e0b005a584445180c50003045000340c440c4010f4903030b050580d0a4040d15040c44003d24801d40038240040d001c00600a06d101c16035103c0240700c118411828a150090721464101c040200c1a8036001c4040b15190b100501603040607506112841c1c000b0006e100902c0c00b41450384c0d01107100001c00c15824000c6501601081c0b050600350012520290018183c40e03200c0d0304882c1142c2c0f649690300d032841c03d28420505280304e08000300c2c10000000d0301603000300300750303079040e0780411045098103402c00807849010242200200485518100781c41e4485d8005000d803c40c0d01d0940203418040301203416a00316100e5a00b2035081c1c0b00c5002440042d900c1e981005250850050090b = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 564479739 1250 564478489 564478511
    0x8030706060906050405090307060b011b0f300e06041716090b01120906020c070b030906010f0b0f0a11060117120702100507060e060a021b06010302130902190e04120201 74
    0x2403882240c40c01445242c82f035032040d0075a80035280000c00c406074290007008041482c0b8091003181c00d0070404071901d10412006022203102c10748401400e0b8010011181000a1210240c07626000001c03030b07c0d80001c04000106221641083c81801101c500004013174162441042c690307110349603040a54501e10b041480c0e103240c0c0c1c0c804425607143c100d040000912180c1414414060711500e8444c0b25a4814460006032194640000b181f00701000001d80781e469885040509844c03a0520912342d5104061290060b4420428014800c20b41c079418580001c5504412642c14010244d210402c20044540b108200007001e014518200c4040780360340340342804070360000d140d030021548204100040400c80e8400c0101c103900150756006040304071030041c81c2c9000301c58081d521001c903009a6043c0308200d03140089002440b181a646e0007000d2402e8040d00380c840c14028055240c003070349d001001c1421440442d0b40d688500c800791041c44298119032610b410180391101c010b446c031000316854030600d840 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 564480989 1250 564479739 564479743
    0x10c02010b0f100c0b07080f220803191517072d03200f0102010903080403031509180b1609150e03060717060a0f031205040803070606090605040509 65
    0x1c01840e040fa1061540030b83c405049510b0300c0c1c420001001d20a00d8024030454136004180303c1d102c0e52800400d820250b5030103002d0501444ca0801c1840225210001d110018003148040d40d0f02c07071008080c0059082c003000500c1c094070703110268070040c40300201040c801c010030400a401072620150003400454039213008208440b1543c0e0201d240201e200212010802251014400030750708000e48000384c54001041c000c1c0402d4640ba018400e4005a1040c40694010300413100e80302d402d80c0340c4000c1942c0d283c4055020345442c102041420340d000c040864204038074402c025004440c90601207072142c0351b2074500c00c1031030040c10a50094140c03a142600c1b46505c48140c40607207812043c80074400c44003400559002402030789181e454001c8504101034254003203000c0d00f4114800100404a0300c81c80e081c82203030390aa0107115a4034655500a1012440100c0c191405121300c1c41c0440c0791580e01c0a0b450700315000403404071031a44c1c440343c0c02c02c04001c02c2d028003800303004210740400881c102490129 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 564482239 1250 564480989 564481009
    0x60b03060409030915030b010e100c020f0a0f03030e130608030708090d0b0f190618150e0106021f060b0a030b180c040801270b04080705071403010c02010b 68
    0x1e1003076403241003420401d403003810703100010010804a80c2c00c0c11302d2a000503002c0e00c00091028001114031103100000d02c6c2c8a9401908906903071941c0c0c0c45411030341c084c8543c000b40c0351003035908440c80050004102800c50701d15001180240d4500e5844412681044201c5104251062445042210500c11100c02004640c2d05903803280c0640d6417428001c010a91540300b044002e00f0041e884401c0141030200442094413401c81107102d12000507200c40c5081c112440340c00b41c0e0300702d031082c550020790410103a072200c0311560303210001c01d4101d0744c2c606080780d0300c21098011724010703049010144810074407040c0600c030a0720030039001d21902e400e2100040942c0655441c1004040d02c444420120381c03102110600f03030400c0c401c803021962400480300b03241a409482107100c0e561900c142202450740c060003842c00801c0c03005241c50892180e0705c5011440c1005403003980ca46034200103100000d40c040000c407000704524425403003800c001108150031150051305a505690528042514aa81d07000e016 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 564483489 1250 564482239 564482251
    0x1311010c0314130810060b0a0c020307030212010b010809011b0c03050c06040507080c030a02130207080f0703030605040b01050a0207031401020d0608030d0506010507050604120c0f03091701060b03 86
    0x1503406000141011036000c0000340c841c0c10105000070350441c2c0c001605240740107680030102103a0000340c0c100418422a1494413501c00300c00710600c1410b14841c0700b44840c4004900007000c607010360f40c40780c00180081038522900a5139a41d00c10311500d2658201c040da07607005114400070130031b5030f042c01c0903125120b203070031452820041002c140c5410540a042601d000d601d40700c0480725546800e01c0e10035990b41e03250040c00c90f035200703228030043d81e46400103039111903545c040e01c42416481000746080207504081002c56501c031062000440703070510701024200c581d000755004102585400144000c0b50248800141048010800310040c150001043c0d42140d600044424210310926400c600a0080350743d450101420044009041c2c440080540003803002c58900700260380701d4030019901e45c1f04640d0020081d422020004010410610100e0043e15040c03d1090041f09156165000e4000d8003804a000c02d98400043c095054105030260070841004002c1201a0030149803181c1e5000003088 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 564484739 1250 564483489 564483497
    0x16050403063206010909060803040312030b1027030f02190803040f14040912030507051e0c0c102f12120702030f040302010309020a0515070b131101 65
    0x11405419101049100c154146921001024494011401c12202e03050300d01c00d00042c00102c0c086400700e0a8440e10045071180300007145031030303e19500d07211540445540d0f0414035556409248442c1c60342c040004096030160f8405c8007101c20140c07030042001c85499403070f82c00d1840e24000d00c00a1000e0781c414046640448031480c0c402c014142c0400c9891094002d95401c0c0000310780090007041014000007a103503040518210480b40c0028007040b240d9402e0003402601803004000c11082c082d50003603030040f83c145030051601d0307000d0b016142100500c21601030400c8001440d50446101401501e0781c04000b29214103d086280d407000342078030f140301c1c50f9009820280c21204900c4050312400344803080400140c900075401e02d043c0c10055000a41d081c1d42580390500015100c500c04012180c07694000007a0a042c0380c1950011001001c2410040780c00402c00040801c90b0f0ba00c801d030459400c2502080d0036950b072502d240076580c20708045d2020340c1a100d0f56181000181c403288071a60106402e2030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 564485989 1250 564484739 564484751
    0x31a0906010815060c0f10090f0209100f03081213151515020601080f2d0c042a05160308060102190b0103140d08010501050901031e02121605040306 65
    0x206403d100199050070301e5120100091440c2c030310750017190300110804075a081c0c0d207070400d10b40e80740d0007501c0b069100104008101040040146007107411150458001e0300424190768560500384c1c0c01c0e16843d00166111034012401c1040c2c1104000c50340e9000000440e00201004a0b84c0c1e4820140701c14030941c4451034551070340c443c01001f42c602d032000501c40210341e001040340b0708201a48402007800360000c9030140c03c0103400030002c0091810100d40240400740300c00c5002c0c82003900d4030504c0300911040c0d40110842410701c0e0343c4c2c0340580d01c4111303030315243d001010701210307028003009004842d007505108013442124070484d40c2820440d16660182015403103555541c00403418040e110000742d2501442c07418070410700891200711340c10707640b18404c6441c0c034600e840b800740d03940c01c1600c95420014044000500040d48502d02418010206050100c0c0c22003540806461110b509685e07004020380c003180c00c40c0e0013814042203c1d00b107880908074841300d55a04030001c000b44501d01015009948602c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 564487239 1250 564485989 564486001
    0x1202010c1e050c01061d0907060c0b071e0815031f180816171216050c03071109010b0c060a020f070213020307080c03010f1701020c030a0f031a09060108 67
    0x2800c980d09561644003c0004030f40382e5514039546d00030469065061050400041c07215a0001030710010368030303107403a17031000301303909507641100c03140000c12810400540c44151003100d801c00d440040d10000c1038039002002e15001103640300c2c6221544045120394021000914a0031b9028192000ba18051001296201c1e1a0201004030944010300074000340300009d03030749181c6d021407441e407881c184078920705511128151a104494040ea688205200803560080780311b212000010302c410341031600340310303041070910b14403e4110381108005581100c0500a40451490f00030b103401d001d001c01c00829401c001c0c0c0440141c0d6101c00040104030741c664002100351403a800c0c18280c9085503070049c10440381029080106001e0740051301d005021030196004a0003140145080c0c9058401c4000e4446449107011308000c12210b520908410655003040700030282030301070005010b00603450700c03000940c000c0c284001b0111045454084100701d400e11a9602035661609540d030410801d280440203501c4407 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 564488489 1250 564487239 564487247
    0x15031005120f0d0309020a0e0a090503030c0d0e07062c030a080903010b0906060313020f060703080717070905090c1b0601260a02040c0c0b040f1202010c1e 68
    0x2542000354441141c80035420100c40001d071800300e003444841615a1404041c900790f040c2c03041c02c1c60003907020480807402e00521003240500c42d440b29a8130f60200744803440b0385850781103610035a9140d40034100001c890070400c10a0003400c50310390b0702100400782a0704d00080105045002d00840345c0d56003411424240c00c41c0301c184410291000141500c030581c41ca417908020a500c2000c14501a5003002510081c5140c56401c3c41e1094001804c024919550382c0b4000d41e2003c114101260300207030a420741c208a449100142c41d41d9803003919070720b04e94141810041c1c803500b03110400005442841d000c2008465100c083d5034115002524130030b50f141c0352490004a2070103402e6200b40310180c0c040c4c88540d4107400044070780c105c555070301e400c41d000b0485406410b0541c2014800848076030001e40d5510041c00c0039480399541d40c285c1d144c18015101e1a07555050004425542603c01c0112420700109006031122803000613503d0380020840c1901c5e0181c060941c0049a0f2141c65540c85124a8902c90f401 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 564489739 1250 564488489 564488521
    0x70501260612070e0a060e060d060f1410050f090408040303030507090909120f0c03020c06070f020d030c060f0605010c152d0c03020703051b10050108030918061503 72
    0x10b6070060321501612100400d0307490400b101c2e142c0070281441d0780040d0904a100609000e0400a000c020405965447d0403000d0401494100d03200c42e991080b8080a0801001c15030091100102140b00c43d0314040801c1821350035590401c2c41071100b0000d100c00a02c4690840d0116a80b5080224441d0344002040c0e440c1e1102d0b5001440b011b00f0b1207408010080070943c2c000d00e006103a110034140c40c2460000300c4140d00fa01d2802000359100300c0303d44801e0300c0d1800141081c43d03c1100044804d40e000d50114421b841100411804100520a4007042040b1030003251804c841012040005e40d00d4200000c28000407030801900351450301e00e9403208101c00750420743e903030541d04c1c034210324005d440740381c52110038406440540000e1510202d04150340c030a0081307840e11a010b41d600e40c100018001c12490110707070f0341c0b5034400031701c140c0ca40a42805905e01500f070080c8001030103143c540d00d44005010b10f4900469501000340141c8081020741d6403185100341d80c2210302802941c42e66134082c03008080c913070303 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 564490989 1250 564489739 564489769
    0x804140102160506040212030a0504060311090301060f0305010f0506060703030b0f060c0c270601081807090b0909120a0e010207050307080703020109090b090403030c0315030c080705012606 83
    0x44074140c2d00500c4400030300c240c0618401c0e146104400c0c0c00d400c55507128094008040001a0100b104001e840c3c42500110401d12132040c0e0740f880d0411450010b23084980643c41402000e208000030020b1280a114815a207603200200740014a072843c0064894404d040000f03041c550303605c0c2102459102e40c01488030004c40500042e03648c03400d40d8015607540446c184001d10034010301c4200074107010390034401e486007816070400008584480300195400d140c010718502090816198140080c5030402c06136000f0701070407000080001c904001c0c049a4640209800c420b9032242c0d4050204440c01c200b00c41c55400d1510b0042165890704004070b0400760144d01140d4940b04201010070740310070100b8030100701d03403003601c0fa00d11b000e5540c500d02c81620070060b00e00b0f60250300b1000184c0441d00a4204035401081d51500083e00d290f10a8030301003490642c0c0065400700d0443c81c041c800350f60304219030070181c01c2c2420412110841d070304062080030f49041064140020344000728800c5e403290340d03601c02030203 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 564492239 1250 564490989 564491017
    0x20622020112090f0b15040b03030a0f0507060f02030f0c13051003020408120405040c0c03080403080a09151d01060b03130804081e07051f0c0312180b070504060804140102 75
    0x4c0d015003041900300300d060b590324842c404005003c5510380b520b482501079050000e0040c504109058609961450b04000b0b480305019080000300d000681c2d606c5507801140800400507160b08140c03800000105c4001d001600f078000030420071000c5500e488045040b1035080714920284042890110b029004603070000c102c5220f00c091184110303004201800589206441c104240f01c00700c08102c400c6125804050046144103003c00d01191182d400680d00003c0c0c0b05010030741c1040c0303948c3e000c00342401c1c182e18800640d4503080141c0040100035031254400c10302d0002e00145040841c0c118a03840090000da18180c04c0180d0701e4100314480065030001c2000a055900c254000e02c0c4112040040c044684010701600101040c98501a0138034040b00c076003840c6000c02103000a109403810746407140113500348400c0b0038010110340068000c001038010340600408603030f1001d00d0b083c6101c0e80003900343d00500a060200303002181d81310307041c10f0740a80c00800009800000c0300b4903500a20900500740503034 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 564493489 1250 564492239 564492263
    0x90325050a0905060f01080103080d1119080412020f071202030a02060703020709141b0d0906110a08010b030912070c080a0308040b090a0b1504060b04060f02062202011209 75
    0x180c2c2150300591003090240c0d072500d26017140200456040800f400001e24408040c0700e41404d20b400303540180c1c0303c0c0c020480000c0c680001c01e050600c4480760f114032540005d081c00100b208201e0315454060b009070460004190307088d10f07981402d071601054041c000000b50440c00701c2095540402004817030715000b40145a54260b2414000c2d00c2d8100e034091021210300b0010850b180386044030f505481100902c0a0240720307610611091002c0d0720410000c013400d51203030030880100b01c1510605101d60071603000c980ea5a5500c460242c60780340160f0112042034000c0c4100456810080f6807402d20040d60300000350fa402d403e03c0c20285240c900d403c5060b103442080751031010160040c441d1805180101d480707a8640d45d80d0303105141d517080a903200605000d010400300b803001140c902e00604d04d040c01000429100e88a10640e20079821542c01480010780d1403410110881e01400742e039420400b5142c845c1240400d110301c0741c0303008191400080c1000100c446860180c21990301c00d112040c1d00902c88920 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 564494739 1250 564493489 564493499
    0x80d0203040c15050c030d0914120913090b041403040b0f070606050d120e030132010608040f02100512070c0212031e03060102120307030501030c0b090325050a 70
    0xd000403801158a000340f605101c8040354001c9042d2001120b154000754600f80c0240c00e41c102034451039404031011224014020b400b8603003482a08040c1c0e1000300302c25242c1500c1c030100030b0031481005004a0b254541008440401d60a01e00301d80d04c1600701124408003035451f01c0a610758451070307100c2007898401140b074003034064542c4020100c0c103000345814030501da100d038100001e004040c540109986e10b450200781c92107020301c0c060400320b10002d000080b24500c841154110300701c411901601c46400343c2c6070441c0714008841c580d01408041c50400028605540c84d8144c00c1c05481d40030340320300d9100c0d01c0364003014031a404407150020f2540485055080524000d000f40310540f204038031480e400588440711190020075a4800803c1000382c6080440803c0741d24205e13400909180d046004681440721101d280d10002d5014041e20b50b00000d03150300d94105041e0401458000c500c41306402c00c40c0c038800d607800113038040520300c03040000189c0c3c201c1c0070303064a02800283d0100e600003d00b5000011 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 564495989 1250 564494739 564494753
    0x6180902030a0b100e1e150a1502070e0a050c04140a0f03080903011b0f050c010b0607211409091e090307030306050621190906051806070e010c080d020304 68
    0x482d454401858a40c0e144c0c195464070344a646d142074010b11004000248980c0c04800503504006000b4181c551000d0b121021000080407807440080981d02c281e070204402c03c1d0301035107a513224207000000c0145003021502021180f0842c030528100b9030310707020313401300b182c0d503181521004101880c0315013600da070382c5e14080c0395903002880694401d5181c5401c5e5a0f03031409407800341610140c0c0e030350f45501300521741c0d0040d1295000000403029546d40c650f000702542e01d03201c0041a4090040848c3c000340310700104888136545403100b082d810800b40c201d4850040d03d81c84141c4140040448088074181c1c2da4003806044960003188000c80c003400c41051040b00b2402100428855000c1e03582840840d4803541440000c1c800d030141c00e501c5800310100301107498282c00810340c0058000f030604c8140440428214192801448140c441c9a603590034004041e1494400c50260b461400107049280f60018019001c414200d0440d41401110101e075420060614200d0b917180c14400b10454881c01c1a0520207 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 564497239 1250 564495989 564496021
    0x601030b0a1a0f210706030204150f020d0507050c1305091b1804031202070c050901050d111c02042f03010e010b1818071206180902030a0b 61
    0x5402072505441035034000c140129001c81030070180c10480310105000503c031807000d1403e0036a13410b00d200c5030316140048042c07001d5401400d2958000d0b072942d05001400c1e0440003169422014041005101001141c020681c50030400940c01d001d500c5501c24105541000c0014810720352250131034050042050b80d503400716001e16407a204803840200c0002e104040118201c5040340c0c015141d6110303c5c48207004030104e80c1d0040c070038a01242c0d0603035407031006010b9811541d030071140004010414003460030711080c00d0b0700420341203c1003000043c5940b0f0b610000c14810b007115020746080c3c42d04040c03032850072134017480380d0b903001c1c3c010400ca135540117101c1008410a104071400d400305008170259016941c0a80e41612007041040d05947d00c0c0555607800381e4003803d03c0801c1c0d0071044000181c2944d480204204101e515014010686821580200301044140407000214a841c0301440503503c41d4141c107132f501303c10b140300196021150001a143c1056000001d20a58201e010000c81c0c0000350588 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 564498489 1250 564497239 564497251
    0x2a02060a0b01140324030304030c15091d010618050907140c100501030b0604050603031b0a020909010f0b01020607020c1201060902031906050409080d0c12051017030424050c0601030b 80
    0x1240803800361700105526803265101c00790854501c40828041c0417456030ba01ea43c19074407414101081a99061321040010354810800c02010912004201003600000d56040030101c600344121205d04080004441c03103005084401000800d010308101e4884020885050b0312201048401c503284183d80300c0040d0009000888000f01d1140c0030603070074103040c01640d01a090040203541090b1406003c3d202007507950b1200e50f4184606d45402c80940c6030345420781e008440c040004101d0080b40c0380c480d400d840c2502070290466015004001040b079001c030301202c14940c119402d07211003128031201c1e80035246a4010b0320798107200005100b20710700c0f0200001600a520041400303082c1c0c2d1141004111084110040e001c3c85080000c910100c00c1030b4005c070444000d80c14040a688401c03001501140c0c4102c8040100d130164001c02d110006200141c0c8001110110013180b6150030030014070314007160f08010281910000107600c0c1075901075402d0321010079900b02251019030303583c185622010426522 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 564499739 1250 564498489 564498541
    0xa110f03072003030a080406061517090c210f16081908030a05040302011d0c1c0c090b060409090c0612090b150f0409062a02060a0b011403 61
    0x2942070b0807078a00b010480a00801000f6500704000e196040e100c1c590700510850750107969560108040845c42c41c00400c4082da90740391010241c80d04000c0307644904c054044070b01c0358004242000f07117596050320308150310075880c011340040505801c954548030304038550442c1401070b440d43c0040d18040c00c0740d0b1300450b00c00c0021180c0b03030300c00240d02030311250840380043d04148041000520100c0d85400c00364009210344000500d503000d07000910715280f0041c1103050140c00101403441245481c039480703070492040910110b00c4905503560b0008045841c41541c1c49e454450707410440d55607541003503a0003400200401d0106001510300907103050301b036018400128075800380240303050000d403041852007035000c0000009a140e47c00e800d501640141c102a5104100c10010340b5070740c8a070300a002c10b8511541c400b180d58508000c2d034170004036a0355200c0010b12010540e8524040c1e00090194000b203d070080007132500c1401c1c0c0101c0e444541c00074400341c2c461000040c41384214030f400504c0300300416994 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 564500989 1250 564499739 564499763
    0x1090306091b0b040e07230706060f0501050c0307060507140703080a18031205060301020d140f011403100905120403030e1509010507061a18041406010f03080a110f0307 74
    0x184000f01c034022802503509150080000500703180c0992030708107244841450742d0345034011444c41c003461a804104212280758465208200301508207807044040c01003402c1860500e40521045030356409081c0000c2d25407038459000c0fa1b41203028450444100842d01c2205544003c0c3c0e00f005050a8015140a0b0301c1518002c03c00180290300c0e4021201181d05540e83c04010324003842c5070000d040041d00046c4d05550811042d01c90001502c00c0c0680011200b107080801d1030504046540b1480c142d0003070048002d00710b501401b03a03170045901003800706100d0780050660b04c0c40c2802890030785018100c0d40003000009000c003d25401402000d20344500b1179260548004a90556016009004c0040c2c0407039018044440013401540144c0120751215050780d804048141c00038030302c174825030890701c2560011000c0c0420300c00d100348400785010745c100c020003d2f9454040100e000e584540f00140104101144a0071034070722444c902c0c5e1105400808540c000c119004119440b40c1c40312400f19001b40b1038038 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 564502239 1250 564500989 564500999
    0x1050102150a1a060310060e04050c12131707060b0a150f030b04090606051806060f220e090c2d010219080304110d0203060109020901090306091b 64
    0xa250301c000c20704000e903411a5200c00d41104007074002040031504610a41c000c01c0c04a458030405140700399070900801c2e810301d141441c0901036010242c80e06000310b080404000c1d11448401c02c036100c100e011024034245030b40e804602c071000d08510b40c2c01440c1c5030501c0d00c0d501144900c0c502610005001c0c034400c1120202c44001c00c0b0035011644956402d003056065210ba20790700502c900c400303007802b5040105580c86054001412100744120450702030303a4400d0140041d04040b854901c2c01420fa800488050a1060000d001409003114a01c5c418030b0005030302144040081c810203071003042006442201d03403582d400d8000c019046807525614443d0310450102480c1201400901d4418941c0d0050315041c0440c4a1614000440100d41540300e000c1000c400440c8015010051901512069842c2c1c101450495858000748440354840e02501e080c000261f0380104120381160902c1c4001a66a102240107a900c50300c20b40c0050b14062a09107050284010406200644000d0f005224602a207807 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 564503489 1250 564502239 564502243
    0xc02010513030318060206040b061e0a081c090803040509220506090f0a030e040b01180905070807030e100f15030606081203040f0f020102030d0507030b10020303220c150804050601050102 82
    0x1200c028018182c000d0220340070380be1140c003040182011901c411494408040801d010281c1e5601c151401d43c0f10000c00c0c44521030f00c820380e0b10b45200134613100c1c00203403420058503524059409803510415500c4007056050700e410720242d0703148016060b01c10b170301d014908145444120807142ca110602480c0035014060741d0108be680e8410b54181c80380b002c0b02c8114410301c0020811901014140040906000c0c142c00481c684200102201400440c05160082e0001d00d081009405078040c5030030700d00050081d00c4003152140c0524404400011130f03010504101026100c4075100e1032000005003404010300142e40c200c1701c04d80741c250007180e8030008410703010042072108803400f0b080071810907404000070364031900c5e10380800d005104681c102115056203100302c603415900c1c2804282d442014149034107140c82004034422407070001c0c60a52825201c500d400e805e200c81e0b1807400890726a410ad0070080226542d5020348103241113030540c20030b46240508400403c5ea002d44841c81018000203d43d880 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 564504739 1250 564503489 564503491
    0x111030f070e0d0f0b1f0909020303040e09030705250306020306010c02060c0c09130507032901060306080c01030606020d1404120507050a081f0b130c122007030c02010513030318060206 81
    0x200d6003c0c51b1000f86814404801055025000c0340e00d40020000042d0707100c03000b81c2ca180076504030030103140d40d0080d92800c1c52901c200d0b202d40b05490260b0001624000030b04030241001c4a400403005a075a43ea0140101e481c084182c80c025800100412362444564000416404a40d825a10303000e064071502e928040410120b18003d00c01d0b44400d509100050301c840b5180010744603000303440c100c034000142400100b0307001d0b0080320007e070740c408042014103001c1080c604070a200b0f0808100113418440c000751544041a0041e050020070345040d14401c49807412100103040e00624504000720510b4407603150741c00c51007014800c40b4103802c007294401c40441ca01e10031000c00042821040d03800038605000d018401c1c10300e40d1101400b0440c4000c000700f4052041c80703800d1640c0e81010030909050180407180b10343c026000420b0a1408240303021180011102d0960305810b05200d08500d510048940f442203c00c80c03084c46c4607100c00041050f400c101c914110319003a00c0a500510b442d64402ca03a2020 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 564505989 1250 564504739 564504781
    0x60f0f08130f030207030b0a0903080606131a1201090f0b01021f0c031b02101506020c090901060314011b0e010509012d050309010c020111030f070e0d0f0b 68
    0x75440c030480000039150001c0c90201842801501d0030950b40303454407001803604568400000d92140024000c066120584592200c0100c80305410010011003400d0405414060f14030465440b1a00121118254055038401d1100000c5e401e859038561230100e0140440b0088100c040f41004444030542d0300200d025040020302a1b45013444800b0010804054000701c0001000d0640d41d002098007000703240d4441c2d01c51a40c540040180b0000e00d108001160128196260b61500010b02408101ea002c0b801070141c00d405c88050071240c80300c40115004150542c0010071401140da0b2104007044103420503607102c1c0e612220003034400d08820b002c1d5000000783c4c403600c0c0044c00401070b5000660181a58102410940655020350011184101c079501250310200010074804010004900424090030310b078280988003d010038002d0103400c142500000e000c09404454010020f016203125428021618400910141300036580e800c2c4008061041c02050b1020262240041c88044003000c10005040c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 564507239 1250 564505989 564506011
    0x70c0b07031d04090c03050d090b041401082e0614030411120703061503060b0d08030412020109291605091002032709180606010516020a060f0f08 64
    0x16801441c440b080041d007036501c1d64000c1d903a840c800302140c54400d040001d9440341c80240051030202e18050b107412032039404880c1d410820801070080d408000c0f091000100e080c28450300a486140800845031020700764100e10804c82c0072a5420800c808168104951003900c1d030303554440703203170380220003d100c1190050038805200e80513120a080c00c45017482e008105100703030307007116482c2c0e55140e083d5010341111119030b0780d56450900c14850342d4401d512540b0781c215050320b212541070b501c5e280c07075001c001c0015080144820440c54464000c2d080480300903400310520200180080302070464058501d407200d03010704805d0001c9c40c12101d406d14845804000e486641c202215002005034540c41e0166800440c0018024203a0300c00c440c40341c0d02c414042c2e1040b08511844800c0a00c0081c1c0d0f4028140f502915092920f80c0100d0000b00e1410b400c050300786045940c6d0200600d036442150364131031000790004640c800002da4694008211003801805695001e01013826006c00ca402400c00c5e68068404 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 564508489 1250 564507239 564507257
    0xe0c030c030112150f0f0b0a03020f06032503091202010b01091e0f0e0106021218012006070e03010b0301090510090309080a14121c09170f070c0b0703 66
    0x2032038030520341220300751007002080781c0400d00c0b0034400292542d01c404c0c5d4500644414610f422a0f4281c00303443d000c1c240c203480d039991892545e00042c0c1044641c50800d40600f2000010480040c40720001410140c145a07040c00002222003000300200141c0310182d0b030a034842d21040840a1060140c1a0540c0d4165600c4807181e00780405602c1c4600d0b8642013540e02698100c00103105041c003000d0700d00070141c41012501e03c5d07242040282c117228100d0b4050140801c10403841c914002c019005800c400820319104401c815600300030700070240d680c44074002c14402c040c01c2020881e44620024800c4200740d00a11900440324141400d8541075000103003113420100324030303a40c004254440c6c1703c0036000b8230f000c801b425a100c40540c205403107558250303100503402c20300f80c2103c04204054602c0c00002101289492011042d4440034116a05000506901d5181c10800c2c4001454004000709800c810207a4941041c003456a075a40903000072241d510459100280d085c11902c161000550140c441d9918 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 564509739 1250 564508489 564508499
    0x60c0503010b091018090510080d05041503181101110102040b0d1a1206160203040e1303030b03010c270501170a32100303090501030e03041706010e0c030c0301 70
    0x31915203e01c0420002e1710220240345411a1240010f101c00c08001032a0306001d8044402030095130806e007225441451820020ba03844000c9508580103c0c2409540d4a01007a00310080c1ca41071011010b60005080d00c2024800300c030344640106407098940e60440d400c9020514243e0281e80f1071402290000e0102c01000320864014070386000081901c014410061000907000c02607003010b02409034840c001300b007a404034240d00d151000c040340c002541441e20b0300c65078100d807031401458030710603148102c1070314105400f0340c02141d0080c50050090106620415004000c030314451022560340201002c0300c00e20442886640054403810ba41d031008210703966400c0e0b0003a10015111703040c005c0d91030828407c1035032a091209002c1d01410003031a04400c0607640200c01c22800740c001e42c000d90200c071007040020b406c800c80300102c80f0203003004070b0613003100c41c5118111300485d80901c9402c00701001800340000042906030580b20701044549080c1c0b40c3d020030013014007044a60130622a0200f006000c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 564510989 1250 564509739 564509749
    0xf0e09070c0f0204050c09090a1422050f01020a03060f0f06030b060d05070e10031404140c0d120f090311090a0e01020a0305101205060f0601021207050a060c0503010b09 74
    0x1e6040c01004460b40c0000c0e5036010401700c490032968120040c40114000f1164a050120250040c107112418010310a036031414110103107001c0e120b4414010100e5000c541111000c44040c109500b10b000e603202c448900701014043c0d0300100c4601c3c0001c2c94044c020450410441403003044c1c3c1d0b407041c0516032031401e0000030340052481c00d0810394002024007180401c2683e80c09414403a0103103a5a003090190154144020b60240100d0b0400b810b0030310400240fa400c1515011794804c0e00001003035010b8a0148020b030600100740400c0f40c003d03001d03086a03818425514030740751a00c14541d640807030354012403804442e16501e0b800014001d030144c401140251900c1baa201c0e8001c90452800a20321500c1104242240d005040e01e5002c00c0d00c8074100201d43c41c0222441c2c0003030804004211001c0c01c20341d0740c652904002001c8802c101440e82c04182103900c02c105150700d5040d99807240340e440c80c50342406680c1300300501c0c0448066003042c8080d10003074403135010b990480e0307074511030f0a080c01120f504106d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 564512239 1250 564510989 564511007
    0x50102070e010b0a020c06030a0911060301061b03051605060118110304080904022a1c020d030518031201171902040c0e3f15180109060c0f0e0907 64
    0x408620071b003e920b50f0a603642c2d20055008403203403140080e15145515000083d507400400c0342c0c0c801c0005200410070990005861b0125204030790f0454000407942c50f040c1d4150240492a00c00a03a107588503c00300203002640d00c2c161600d496134285c03040e01c411710346030a03602008081c0c0e0400c1420700c089000180c44034050080c182004102509202c8400e40303034040a400008100b4403941a00040818654184080030000601146034031118240c908040e6541d5500c222004c00c00d99582c00090f02e1142080c1351007902403c200a89035101c04240e05030111050a0107625044420003800304045500003410f029022014001c0108042864007048003d1000c5400c0c58244080460760a820f59259802031120841c1c05406803a04039100c6110604d61020321500507134000070554102080000041da90500075400740301c10300903622206140302c00c84100300c505020f50300b80038542040002540098a9008440d641c000c0e00c00c0c6100710486022201d110240c0d00012102d020600c0c80b44115201 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 564513489 1250 564512239 564512257
    0x923010e0108130b07080412030c1b0602070204050a1d06011202090712050124050f1218010207060b180609070f030213030b090c010504030b0c03070c060e070f050102070e010b 77
    0x10724800f10580c03984140903070101c1d003103800240d8200c10402042800d0980480542492038100181090550050000310f04e0485011001d02c07405201c000f003002903011a10010342c068414032890602400c2c6038003500341942150401034507104504810500080c80d94100c58441001c0744580f080398080c803540d0071000c0c0c241000c02080c20707103441e405080c6018441c000e10529000103203800001a13241c141d142a01a5041003060810609103140d040c6415520041c600d410400300c0c580300c4102480c0071400c030303058240065001083e07030800e01001c3d0780140304a6105170755070b4180c60080b10007a007603001c080320b0701079101c2000d0700404d56031440703402650301340700031400c005281041c201c8214141c04141c0d80111010b4201004000440b04203100d4a81d0a0b08203007007450800c0e00f1692400303a40d250080c00c0c2c0d0a040000300000354850b124900d140c030441d4000004200d00c070302155282d0b884010358000d500094a1605c4002415440020003800329000d111241c40c480e4200617206416500500103 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 564514739 1250 564513489 564513511
    0xe06030616120f09050a0c061d040b0f0a09050613050402060a0f1b08040f1e030b060109030209090a05060601020c030c0904020a09022106061603080612030a0923010e0108 75
    0x15000f0542103110300c40c03803e800b9600602050b4640d2814141440b01c64110300100200c84207400e203a1403008245141d040e40882e004950b20205d44081140e55420082c075a40c840c03041040010600d100f0b0344020300130407084c1d0f108202e5141d100d88003402d032941602c2c020b4000c4002c000f0340e0701d1184540d20700381c01000203141c482c41104240e100550f40498403402a6028a000a010045a480e00d05001c000b4922501d003c0d0071841d00140702b01a13960302e4403001e050b652078080014466071151a4043c081c50b07008003d0081c0341400501d160396000d012030704581c1d502ca1000454a00d600010f207850010b803000340145004d280c2203017801103890307000c0c10880c0c00008040e07002c58001c0d8140080c08144211070302c0e6181c820901c40e13032150410000350446000700d00400529030900940c0ca84110450b41600b00f140c507035120040071801800318000c0345030850201081c011041ca0b4071016500450313000104c41c01e1204007000003c0c00703006020650b02e0100f0790000c40c2e00841e5024140c07a550058011003 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 564515989 1250 564514739 564514751
    0x605030705011b0c09062c040302061920040311030c0a090908040e0a0b0907050c03030c0f0c1209042003180f0f211908060a08010f02040e0603061612 66
    0x51700c101903407032681003c00304541c0381c2014080500021078800c40812484140c80407401c01c2d450103519400081c1826402a524201061441010b900011940381c4a403a0880c440c0701d01903011300d01601710380000c41e1040000c12103035105141c00213801c801c01c100245100c2649203819904402000c241000706d070221000d2100150b10080d00c01414402c440c2c1d1400419003a12800070090803600051403041032000620001e4000e000000a49034000c01b40641580c0c0c811944104040d80e010388a64071241d0f10070030381401c003c0d0140c0c201610409505640601140c0280c20039805803e80000c00391042c94010300000c1c02c401c01d11046104a0142007043e105407448001c52a41041c03480d0050440300da20a080c14035442500b04108400740715035001041c2081c0600d0070b640c07046244c540e1303c0030400003800040303502da5584c40050070041c401c1c5402007290450910020700a50007500c2110b070521612000182c040c240420350a10910610801105000b50b085055a036681e0481c030050105039218 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 564517239 1250 564515989 564515999
    0x207170f071707080f1005040606030203030c01060f051e062a01020a0206150d020d0302190b1b0c030f13090c050c0d02071d090f0102030c0c010605030705011b0c 71
    0xc07081002424602c440c0742101e45020340c18a181115035800760102d40e2100c0624401072030040380d940010701a000021416464505182c0081c0a071a000603516004c00920484142c0c01580f14000300c0c0d0414a550b0b03100d66850007000a240c85402a0041d440b403070488501d01c914190008001503e9a541940340a00703003291107001c401c000c10340401450b0360005114214607010480d0340d500424030403500007443e5030140415082d18080744000d004140c0f06c00b00400b01030003800250403281e2400340f96000071015040607994043c080e01e0480803030707400c405034190b0002840200d50700300c50010015440e04540c507c0c40030b01035010000c3c0d495620611040815160454002c0c041644480e41d80c9680301c0603a0650341d4200742c034450f41d80c4259800b4100410080102d82c0640d0314140c2451000c83c029603520f10310300e0425a0407000c01c0712552000082110b1200c440001d4941001000002c105064544007416590b481500610303003c54506404030040c003900e100f0319941031b440f8600400c0300603921 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 564518489 1250 564517239 564517243
    0xb100c050102130b071103030406050d0504050f1204030b0114031203130c06112b030209062118060403021507020c120717011503080c0a240f020a0207170f 68
    0x1070300700074000d52001501c2c81c01d02c80012800c10031400d049020b10700d8945415005040c40c03042e1114cc040058580000400380b12082c810f05c0104040402658801c01148812040c0c541c4503002c212a000c00b08400491140885043d80004010240041c0908400407105139070075000141200ea09152900700200007030907040e0708038000c0c46603840b1012a20212200c06d0b00b0711b80380c60368446a03c0c0d00c1d2001050480a00020fa011002807810010f82c2c51400341d0204150b881121ba8598641498021001c2d0004034140d4052054001c4860058294500b00d4101c2e1601000d880140042c3c0c40b014002c0d40245034240310a401541900458503010a80800300300d003900340c00f01c0300c0c03c0c980260b1000c0007103034400300c00c900d001c0011000800020840459401c2c1142e020b00004c0c26008010850303100c030190400105c2d44513a0000c00408108002c04a8800200d01c1c0d070303120400c0c10b0f0810040780d000100c076000b5240074070000d4010340340003802d001c41d08560182440540d4071510640c002c3d60084002 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 564519739 1250 564518489 564518527
    0x316380a0f0f0c03020d050f0f0313140609032205040e071a0405091303030921021501031e080f1b15010605040306020c030405060a110705040b100c050102 68
    0x440d03200c1c08428599184042c0c182940b1101e081e0a000f00c110740a00043e50100744510300f10384500b00039444104000e01c02c019400340d45800c844030b517800002d00006d00c10b0012002002446510b075485591040c00320759441d2413090302d00315401d0703109000402040019492a0380b44c03640305905d4050113640c07840010300b500c5c110380b280c3c0411380000c007041c42890702c20188141c1300c16540c07502c03a2820f03140c900400d02c48000100b001c100119112409810144690407000016401000500c0209207a12403481d1600d24051200b0151281c1d1540d28011b0144907a1207040b2a000603105c1d150038030b003000365114500214021600c41e00108450b070004900400a4015140e4400329840c55242003240e03c0d02d054441c0701042c4a03446100010000d81758024111410340c2d031300800160712148190b0100b40b46011710340140e540158081404c080c00da512800300c0c2100709900c000c45108075920310074807044410084040d50010740c01c0b5203001c412070183d00294400340c490b6000601d008120080c1d8000540c0e = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 564520989 1250 564519739 564519757
    0x1515070203240421020307110307030614010e1308120403030e01050718050414160c080403301b210f08010602061003110d02030706050405031638 64
    0x602e0350034401400380c03001c0d900781200752801c030750441e00701c84220180d607134050184010044190700811180303507141440a40000c561140301805224410b1980030300b0980240140000305580500182441c0031885056840b960400082c52800058010070100401c0c0188140c06240d01d40204c031041440c00d1107400e00c103080907599080164056011109404c50591040344501e06000041a132080003102c0e140d04085180800c003051540b810b01540c04146501c4090030390a400b14000041c40030b9881d000e200b00c400c059400803212030050748000c0740e10403074a070034002507404050f00080c40d83e090005000305029054810703e41c016030448000c6582c42c92030316000120440200010203401850117805410b40740043d180f01d02c0e194021041460080c440078002c1070701941440300d82e466442c0c008401a030050240c1d07a519441d040c02400a5101c1e2003514003c0c49886041c8261100d14201765007602d001d91a484c07100300a005101c2601d0034250503003001d0001548480c007500380c2d842d0040c04111 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 564522239 1250 564520989 564521053
    0x90a0218090c04020304020603070e22020306040513110f0a0e0c04080c01020316030e060d0203181002040f030b100506190e010305070e0d0c080111121515070203 71
    0x807801c903441c20304200d4040300c1c4501a90051007072100507524042a20b500510ad450803101d544a41e500151001e0114000c6000c540c44110074200c0090303098008503c602c1d020f0f41d0178031a44e11810f02c9418005580200605aa421440f4400d014075104856441d640030081ca0400365949850155281388010f40d41e0b0881d40400180030480e0303034418403c5910040090010b14101300030081d900e040d010440754003e04018221042e4182c5554035402e0ba182e0140a01c0210b44918280f000c03446198850401342082c0d01c140c00e10343d102d0440c00e000f105c05591805007034010741780c40c550b03485280c0310019003d1a032203440c2074070118041d00d442005e0880103a80c50246000c440d07412402404140b4031070300d0641014241001c00c800682c200e51a202c2c00141940c00c15000800350404084424064014036190350034003a10500d0042c26201410b180345142416103501e441e50004207010b0303400740300503542180e00d4401d03e21081c4802c0c405040c0e098000740035108600a48042a02c1c202e00b20030002d2911 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 564523489 1250 564522239 564522241
    0x40209190906060e130e100513030221090103090c0509090a031707050307050a0905090106090303120510030f051903050d050f0606030612012a0807020304050d030305090a0218 77
    0x22589014600c0104114240040b40c1c2d000c000c04180b5401d4000400301e241a106e041c021080c01d002c00104d5000c629054007000b65041608101d03044040600007540144070303030482084d059808140d4802012025041c3c14508407800d001034010b8201424251110701105100060640b0b50403681407044075000c02800e64980d2034580540f40104050700c40e40828100000c0000f4542c008003100d4100d111414202d03141e00030f40c40101c4a070500354009030f400c00041e0300001003c64115042905803032107030300c4194240300050001400c80344215130042400c10100d9080010075424103405d01ca06004009507052090060704000c00c6003450307041100000c81c0001c00e07548402c0e05200b41e54020254984600c01c5080244c00102980405071003180300302c101c66100141d29100750f00c0310a01a02040748410b840c3c12068400c682d5940001020003c5850303580058a41e0380301000b01d4054a0380104070340f0b18201a500c086000f071100401c030303020910a0b15040310150303403030031400c10428400d100740e2551 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 564524739 1250 564523489 564523499
    0x20c09090d0f090608060108130614090c010512011e030c0b0306100f020a151808090306160c0314091f030e0a032c060f07020108011409040b0604020919 67
    0x2c450450222010404048001d0044660100613250405000d02c1d2501d016101c24960303000391103400c4001070190b45441c211100314104203120324403d081a8050319022200700005444501c00d014225046542c041c005110180d410010084000003500c13100109684990701c001e40c0c20280e42086954240c040304000d0180381407030400b5100002d900d01034000c2011104081d50318080b100c030040a40600c541201c2410a299010260403000c03104401c0e40701185040c1130000340e10007489240a405140002402e03264600605c40c0c0f0040d41e0f03030726143d200700f054070202c038620078407140c10319165010032000c0e0301036540030f00d07158491014083c44080c0203030110020b0308545641c2d800f10b00c1a044203081802298003d0b80c44042040007407030034103055103006000c24441c12100c1c01194410404119482101070302005000b24034400c0c4c0f00d04420b0b9880e5a0426510500a840c090340400c0010001c0c0028550170300154120001800150805262000040744030064941501490b0a44142081 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 564525989 1250 564524739 564524747
    0x306030c0f060f0c060209060403030815030a0b0f090102090409030509030706020c01020c040e0c0913050c0303070b060607030212030711150112020d2618030d0f0f020c09090d 77
    0x501d03646400c8011603280c4107014000301c182c04240d105000d0403103e040280007460701110102d020040c062030781d6a03120318018040c0c940903070304441e0248103154a030405003000503000c0915a00800040102d03901c101c10403c0c1e00d40001d111610395502170200142e207860314041c03c40d8152094880759143c100030028185880d425502c504119030018005400503600801c0c03000612000303540100701c546580002c0786c030b024191072180e600a01d49804000721498042103a00b801403090080c7c8600041c61810141d80e405511030281007a08140049680d0b45041001016890f00c03134016070711146420012500301d0340040b46c1020202d0f13401c1501d00141d1105111043d209108120014503a504100d0011080307000104000d004580021030602848860038041d82030004515546e1040c04c001c1450000e113400c400808a182030690b1900707540ca10700412600c20450950384c50300010309028008803611800e01c20150705502451680b070f0030390f4903070580d0706100e0314444005080115844100030 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 564527239 1250 564525989 564526013
    0x70315090f1503031b0c0e0f07090b0901051b150420030a0f170f03011d090105061e13020d062402030d0507110d0306030308060103060305060c030403110d030603 71
    0x1458820010000c0c4002900005d04000107202001c0304807801903180741000071890740e50003002c04008920700b0000c1804085620070321481d10341d9921040b072aa5003c3d0040c0d1805000020780c0451014001107844100342c0030001207540d42c0b0304c00c0f102046885c0700c1060540b80280c0c0c00362180d1200c0c22502e072242c1d00d07007070341c1c1d05444405400034104441c45448810070300302002c2d0000c0000d590741e03030f68030084100d400c00d03503001540608074540da03035a45080700e0016566083c40042c112240d400004e042441c1031180c0c91281102502450054241d2003044000c40d8103070800c15800314510100e80e254100d1480a019200c40c1d41c440000c2c1e8500780204000260a005191424041c20340101041203a0210545080d0640040007040c56211840300f907403130030703092011440c0c1841552615000917a15401c02d0080b01e00070384464166403101001141a90020b001c007034026802407000c5900d01d0414002154401d020b80b60103184c0e02d0110440500700800006003200094841e4001c0c020b110f40300402c0 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 564528489 1250 564527239 564527261
    0xc09060b0c100c0924030c09080d1121030108010b100c03081b0a02011a1e010c08090d05070e0f070e0420041502100603050312070315090f 61
    0x42820714a844a90a5039090401c0340c0c07402081c3c458400c42c00c0a4000c1c41c00802900c0f100e110100f0030390000343e0440c9000604c10078400020304220749038031061300a110041c1900c002c000078120350790a903401501d42448160701cac1c1d45070384120342004401220804c11410b0801c62500302e80e6603545025529400d4448007a02c280c41030b001d003d2031040075500076000780000d540c5030030b26032000c0d03503801da007a6800e4100d0000254100e100140301842503a043d030003102020030205030207250781800c0c02400140304a203104001c12600e0184c80703c28640c0a40a2400060b20075510b261410b038001d804901c260070f1942c0111440d0307000b2502808080c1060040759802186101000801d28104c00010400c01c030911100740207560712268200e042c0c0503150040c03450b03420201c400d65580c4d99800384040009410200b900107000b600c0310600d0281c458003422040725003280003182841c0d019101004035a50107884102890f6494080c00c9511028104940041c5084d03807002441409444082c41511280a66 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 564529739 1250 564528489 564528509
    0xf09040f080a0f12111617040303050712020601181d0316151103010e070c020301112508071b0f0b090f061e03090c0910031b0e0a0c0c06090c0906 64
    0x5514801e0706408261b0301004004840300401102d18140059009001e040703640b000e500000740801032503000b0009004051042c11901004400b450f400c030b85815084c040c511203e110b45204400003089504014020f00c0d1100c1c8151100001840c290318650042c51858030750031043c00403000780000e0350070140d00d0b001902000d0103003007440d82140141d80310500441c180306440c03a0100340040c6c0300304400d00c06c240c1c0c060020080280e01da9a0a803085e0806640d80c260ba444059400c800303d594120004c00c050703071120300241007101c04e03607407402d001034428981540700c040303450006800c905241014004120720403070300d56101389500600824221501c403c0d8010001040b85118061411880400d1514a02c00c41c0b91aa00c07401a1340c1d0428050904140e8454a00414020360480001c1c8420890b80308012030550012028014080e03000c07244035982c400480540041c0b80550305d908202219805890902a00d240503695481111007189090f102e40d46041c03810f110b00700052041030080c245ea03480c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 564530989 1250 564529739 564529751
    0xe060a050f010f030f11210705120c1c021c1e0320160b03060a060807170403090e2a0f0a0309080702060301060c05010506040b0f09040f080a0f12 64
    0x81540815003203203c000c210200411701c58050164030700401c115004010001d507080207403003e158080350f0540c600780c1000e009030034000a261500c00d414000c0c41d01840041c0154080b03c10070008055a02d402503121064030301103140050b40c4196801c80b1843d11014004240780c003c1c24001103500203454905015503009000303c005c0790b004208100382201c690031400c2c140608042031303801c000ca03a84440365500f078555400324402070010042c510032041a160419016a41c840449019001f078904030081604450103240281203280d5807944503010b0f08080521550303820700c00d012440c0032202e0b40c1801d041056a24640b12000302c481d12000c10217a082410902e000307503500360a12030204030340e061581d9140c0788001c105030f950540782c0e00c0c3e4009010545940c0c2d07a80c0c001d041c6000380b0b003048605510f440001035075460303c0e11031034002c0380018125000e104000c1d001c1c4821648040d101b0f41e0424000350b04500040c040c80e0040c0b1581c0c0c4107584040e5503141441004e00441c1442e6589880103003031035 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 564532239 1250 564530989 564530999
    0x3080d15030c0b0a2309030f01060f03080705030c060f061903170d11070f230c0105220f06111c0c1a150a050f0906220e060a050f01 58
    0x1600304420f90306a400d5190356404120815102c1d8001448a203407000700b201d02c02080a107942d00a440a1a0280d0035625400569040c20307080ba800c44c000e131409100650b10500204141e41c004c1d000c0d0030700c2401140c0c035200c8200b2996181c6038084030074001c410918001c0201c0360601c140c00304030190b103491010550900b140e40d0801c00300c0b5038940311020600c011812010b00c1c0b04582012a005845e034803031580c1d0f5005400c1c103581440034ac0400703440d40c0018034003007a1103400102c004228681c0c11400380503480515030044842d03a2016102d0328142920f0034413145480c418064040c02070801c1a00c2c803001c2032402201500000840448a00c01d402c015843d001c0c1255103914401d424003203180140440c01c207482c9c80403081d0103140b449580f007000101000a0482d00d899100304a00c81124000c0c0055130300c50800400b0f0500082c05a080201d45c00403800e9401c000c0e0400c01504221131680c00149079014944044805014030351800754820380602c203010001d8410300c2c0e0442d9070710400c0f12040d8102 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 564533489 1250 564532239 564532253
    0x40306060503060402030d350a05070206040804050105030703090219080706050c03040e060d0b0a0f1b021515060a1205060109030201021519051305120309071a070c03080d1503 77
    0xc070b411f15040c0600340810030b602c548030340e61000440c0124242400711022440a514210340e0886403072a0052414020078495800010342511450b4013140844c40c050410004580641001d8100c205068440441c0b4006a80c3c3d140c81084108450342d0315141c02e03241107001480d200d51640004140b03d0204081200d2000200c1140c090300c1e00010224030350307141e040100d2441000c1c064041d10703244190082c4507080c0180d812500610310b060700c0c140254024a19894030b15071081c08070b00e001da0300000d44107200d50340d0801110740c0440c0e0040b05818030300040022855648c00300300b01034001220210142c24064561080036005030081c80c16003c500c1c2183d00203540c030101d4070480c50105400c1d000045d49281c1404020450840e421024085400d12106050032175180f03020132a224050030030700380807280288081d20303c10b24401300204040e44c50840c207a10045941030a000e4510f104002c90408541070082141c0210b02c2126455650f90804603900110740003c940c25152001c0c104c0e0400108800c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 564534739 1250 564533489 564533503
    0x6091a0f060a090905040f02030609030c01050c09010c1121030919210f051e1e0303060111070f060807091406030408030703020d0504050718021201030f020114030c04030606050306040203 82
    0x180c07144c001026280c1d030a00303000f100302c0b84000075414840e010401910040210142032500100e90090019446010f40b802c000d020306403c0303d00040342100f03040045103907910560242d11000d0a038161184441c00e004a50300701d0480c00060b558800100c0d401c25003003d007080c26103540303111882d41203a8104031240301c0b10f2482c00520240040c02411103802d1081c102004050350340e000e021100540900c41c4030350000001200c14000314011051002c06140491103000f0402c40d122018600e159907400055644100040d901b04d034502c541400403030040909155403011b00f8060f120020310b8070f030492004040300c80c503410200030030505500d010182c0d00d402c425a03800c01da00400040d01d990310340a003103000b0700903002c0b82c815403800c000c01d00c01071140218621013901c200200c0010290b9408000c8401d0b407240d00c6a041050400c0c00040000c207440c0e0540c0082c19105142c00801c1d2100005110701c035410983d82c108070420002801c20422845d44214001440154050a2146400d0300000c2c0c035580 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 564535989 1250 564534739 564534749
    0x31c1119060b0312030a06030c09051005012a0b06040b0d0c030f0807120e33030a1410266001151206091a0f060a09 51
    0x380303581420082d0342d030600404844842e000b40e4540c0360318001098202800c4180f0080d90000403446012034090f440e405058401c480580141c050585010011148103002c0c0c1c16454030156940641250710040d62211100305029508075034541c1043c4041108650800c0c032207905c104c8422203510300003443c89080e401101d4000c10743e440c1808880c1090341e5980f06011000f8440029801c14401ca113401a421190421040d0703010112100c1040b0340d0340a41c0c0251465030400200c518031569111351a10065030301c4081000c012807502c071080000124140300340d68151001c01803400c24040b80e480303e075441100349000108440304010244ac0d0b140c072540701388081d4042c42d80c0f20b00300a031060f52003001c0e8080d52198401d5a85808003600d90140050585500a01c4000b440c0c05c00103400e058860303113107050310b40360400a0101c00318000241c4002d890b03080b4450030700d916100005880407a038400c643d41520955200c001080c0214100244c0580d0750622038071420707082c0311881d10380d688080408240c803 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 564537239 1250 564535989 564535991
    0x10203041a0a0513060c0303050c04080705122404030e0312040605030709031218090204060807050307110a0c03060e01050709120203030c0a0317010602060603100515031c111906 78
    0x100b1004001c80f114840c0d401e0f001441e041050700002e44d00d501038804451140290f50400490304d4081004410384110300c900c0200b54000b140901140c900440352541000341d08e000c40d100600800100da4842110002103400510745a04000034141c2000841e0310140080b40074241d0068034485c0a00f143c09a4003078803080000c00300000c0d10031405032881c4c0020b160010030314020042081e01c001e100d030594003000c40e854602038000182103a45402910b040d01c55a456900e4241d80d048001c40c1c0942008010303104108408060030350100b010311003800b0150103100350038005811400c100c1c050300e03c01860002a617140c6010029460b60082085045d900805204440c0c95050300000385140101151040940240d00c407040070150400300705101c0006410f2213120b983e030707940700a980301c00c003c503040ea406030011700040034035565950155600c4003804115111f100c03d40b00c0401e02d80400d0600c40f160f0700d20f24040c83d801884d084014002d02844000c010044000d44141c9040e040c1e4604030028149 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 564538489 1250 564537239 564537247
    0xb16020715120c05070209090102030105041a030601090c140a030605120f0715120509010203091c0507021504030807050105040302010f0e120a020106080a0f11041a0909071d06040b010203041a 84
    0x2280b00304c045900594006180842c10b08104410034001c0d4000e2090a01c140d10741071070500b0448000ca18210030041c01005025240c0c1303003450000103091820103850410041c181c002201d0410340000d0000920140d0380051170030b0800092100c441e0500f00c1c605459840200c1c00002602e002412400340c1c0c0c08003803841034403100100f00b0351319080784d100582055406c0c00101b0000c1141503001e18070030b01028044402c0000c0801d5000c0c40720741082d00030000a81d0400442c401342c02c00d0f180e01000d00540d150707810310303055482e260025650002c500c110744594488040c013050617824081c80b180410048400c010401614000075540d904401d041d01c060b400120301c200340c0354000c0d80300d003004003000790131740d0f144000f2850400360304c0c001513a040780c592131180000e400b00d08042c070405d5000032032550920b989624110801081c11001424011729200301e020104106050b880b6000c030403414011030045078200b4100300010741e401d4005c15411580140000c01c00055070402008610910000540d91 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 564539739 1250 564538489 564538511
    0x1209110d080903070801090b0106050c060c0f090a060201050403080c1804091b08060115141b070f170c03061501110703021804030e040b0102030d0b0d0b1602071512 72
    0x7500960300c070280d0500886400040341c0c1c0040d0481281684101c00c25821a07032103031019566070148a0750b80050340c0c008800280c1a488120003410200e1403440207078103000c1d4a10016003c03d499800510050351204244030415411203802508118861600d50a0000808400310b0840c072900f80d05111fa900c0d15030280510507000002c940c0030044d584040b0f0902c1d25074088550322038080c4030307180210303035180c0c2c1d1400e6044c41004035100c55040380040d00e20b490301c60300c00c000c0408220002a2060302821400113401130f400901c01300280500c2d00410080710707100020a081a00041c41c0e00c0c020740100c2c04011114104d5030000f16140b00c242440d0403c900b012145900d01184d5030002500103d16000c2034070f41000990ba840e01c15032103030340c904404000407001d100c01d6940c01c20a1501607803090080c1c807600700054001020f00781c00070700700500040309900c50172000103094583c42c2009042004810a8641c1802032001078810340d400c24014641a0310000c0401c0c0701c0c080a00310180c1e840d508802 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 564540989 1250 564539739 564539753
    0xb0c0a050702040501030c1a0301080a030f1116080706031a1c14033a020c030f0409020d06081501180608060403090503071203120e07180c1209110d 65
    0x452642c020344101315560316440c02c804000064040d55841c0d000003001851502414000c0301e06890028000c0c140e60030595130159100e40034041800c0134801407200781a80704c0c0c0d080203081401401525460109450410307400d04020150300b0643c00c01d030401030301d0001d072a1204099290400f05503a0301c0c0141e03c1c6e54213802081c1803000030061404000000302030360061f000000c1c01f90801d0a9104411052152000b60f480c2c000045038910618130584000442c0713040b85d4042c0c200390004500350303885e0404078948600381d90b12039008043d485501044e05d24010100307114400283c50300100401c5840e03d09802c40c80c0c036100511030448075058840c05c3c1ca00303800407038011000400c1c040c403c84845050628019002082c44d01034140644203010000982c034441144140100703405488032092080d08000110203024510650000352065110000e40310080d4102c004945013210000254030103202070060001004103040c0c0c440d2070030000d00b0030124250804442c90702c0e104450460340c00240340f8000c4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 564542239 1250 564540989 564540997
    0x606061308060c25050a0b0c1e03160e01081f12060b090c0415050702030c0d05030304060e1605040209040b0405131a042a0f06110c0d0b0c0a05 63
    0x1441e1800380e90305021000400c8400342a2041080380240180610300d481a07640381c05034140134215a11200e00c1901040c840352034150400a201c605e9403400440201d400000c0c00c443d103283d640d0010001c00c11502d00c040d034049800c500110f00d80242c1c2d803408800000e1540b50068a0a42c1185d1050340c045001011a03940300e0080441c050300d40c4070300c182c0b410940020030b031090780503014003c9500018025503a842c101d80945042c0659040c0b0403100035000c0b10139800403c8200d0b0940718604e41505c141e03640c8070603207546034031038001141e0700d00c3c05242020a4800b44500344000742c0c80320b803c45142c10900ca082d402528416107006869441900002e001390681011890700f01c2d03cac007800c0c00002d605601041c81c0d56805105205200b141000549a403c4021036008d000ca10160b01500b904000404240010044030b00884088980b00da8910b0045080303940400c0100796100e048641301e21082c80344004580e0104c0340c80c2200452034482c06220780c070040418a62110000741c1c2c4613514080e505503 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 564543489 1250 564542239 564542249
    0x11060f070f090e07112506050c0c0301050f06120c010f050703120903030c02010b0a0506030a02030405071a040e060306070903033614060403110904080f030f04110102010e06060613 79
    0x7440a0a000ca00501405c0040c4142ca885d0700402c040c810500742da0b56003d07044402c0c8003240d215003601e06002100c06810920100055009880b107011950f40c090007903e0003148120721a4000d42441c0007001a5444c06140c0072505402610505071640c1c2c114220300c408020324100708e5035a1130103242c11038113294503148400620b03160031000014075a140d407202c00ea5a40a0300200030040c0010308200580c00c803031041c40d0b804642000007800322410742d005950040d1184007120059a1a8070382c0743c0c09151100d001c0031280074003081c100f0400c03207010280d17174129800b68080c0c1001e090224000f46a00350900003d010f0010300b411000419040343c0d90071b1946a140003e5109983c07188480f9208a400c030b1040c0251132200b003d044c0306501c0c014048604407075103e100e00c0d4004056600340001100300920984514406025420f540000c0a00861003a480d40b1100710035850507141480752040f40d10106411a1315040100022510001d285a009201101d0075515000b01e4240c08980c0085a004 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 564544739 1250 564543489 564543509
    0x6150103150e221211070609050f040b0103023006040902030303041211030c0304170304290d1d1b03030d0b06070813171f0c0324030311060f070f09 65
    0x30413500198041034000711a59240103440d8610364130720088424040703d00030070350700c0341c40000010b0507441d16922107440100103041c0135050000700d030482903002c42c48203d24503008016034884002140042c500340d0b4401c504481c100501c40c60380c0c01103940d81c08003c0c0300900000c8200001c80342540500e0310a00004102d00880c0e90702e00603481c0316500c0740c0140c0320b1282042c004410500c540c900200555041d1000c079240d0081c01c21072084071846642c140c0300940070782e40c0304004110140525000d542c0d1114080604070360081d01c040b16540c07601d500d0000c01c0000e010308000900d641d0340c01104462080f22043d20100b031104501002650505c105100244803050002d16050720f030f041980c000f0b0032600c0e801241c5500005401c011a2500b1a44081c142d510440c51071101c403000650707104400d250b0651400088400b41008601890b200f0781c903c110356019200d400f00f04140e80034100707d0640c244003018041c0d904103801c0c0071740a028098885c81c01d110340d241c0d50640c41c520074402c4200414051031 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 564545989 1250 564544739 564544763
    0x203131502090a080c0105030402060f0d020a0e09090106030c0b09040605041a09070c020102150a090609030306050411090901031101020a05070e16020312010e07030e06150103150e22 80
    0x40c0d800025442260002d026a021500000383d06001140141d44100103848440c070b550745079400c02825500c00145403466400c18000c030400007490344003a010742e548580313401000f03a80c40d80c108031540c40020080d040682c180780c0103000099071807203d44100c0794003d49440d11003150b800080d0260003a9009150407520f0403640d600403400103806e0f10702d406803c1d105425030380c0390107000312600300541c203000e40035a00141c00c20352071460b084409075101c2d1031050000381c84012a5076080c00c1c2e55015106a0019466400502852415218114235410805d8401d03107070628090215001040510019014404409105809074001d200c2d001e4003507400020744ea10300d0f40710040769100d09410354128811b5900070b890354003040d0000086400c1e040199200601c581c1c41d00c4001e811140300203258104041c5c0707130104040c00c10800c211203070040d504550178124030b542c0140010100d40c5100c40211001100490410a40d404503004c00c0d00210118205580036810f42050f64155034190700083c400300d0980 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 564547239 1250 564545989 564546023
    0x1401020f100605040507050c1507170f0a150303140723010213170a060506240c0105060a0302061606020f04030b0601030b0402031608042d031115040303020313 70
    0x3910003410b0343d808031010003803610382030400c41d1a801210300504075940400c001c0c09d000c00184d0356480e03204031107141480440e894081c2031a1580016034241d44000810300601c034400d0742c81c3c01818018031140c000401d05620b1514020701e290b4a814170105003050004034581403000b03944510070b818446a801c07911041014440d14000e5009403036002b0040d010641c0860f00d4020320030f4108100c0694070003010310048503242d9000900d0040d1034940d1101070f10b02e041d07400c0c00c81c41aa4a000300c4805880d151501140d0403192f01f1f41e00000c6c5054860384d120724060005a465500b9070785855010402c1c042000078510b0b04600905ca000f80340c4400c100041000000c0080a0500600c551000c1c0d03410301c8420641c00c01d100a9010540f4403c86522803140c06640492003110b00950040c0503088071043c45c0d95520011050340d1402003101103032407418400d42c081c103410401c0084021925002400c2c1c03442113015203d401d5101900050402d6000030200d035201260654102c10f0030703000040c98198210070 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 564548489 1250 564547239 564547241
    0x1515031f06020a351b0d0f11030a20030702040f02031501230c12040609030b10080c01030e0102090315011404110f070f06090503040314010e071401020f10 68
    0x500c0440e030004450301100c56a44181103800031148004840004055144da21001c00780c001024040010205625200003190304001141d00c0020503140d241c200c91a01c24028010315007180302105c154820000900c942e0341c071500d80b00c9441512110014610032a0f1216400c0d8400c40310082e40c00f40c100301000c60b2005c5e00341e00450081164a80902c00803000f00019035561800c00f0b0b100d4a80c040c80d4450a800340082001407404410700390035101d10600e03402c03101103aa081034000e20001502190244104448080c03800e8000100a00d03c488040c40d229030180d4481d03010358007a04050712808035100d401c2c025015628260b0004054401e0070400611704801001d0902c01d40060b80102c41aa143c0d07030400384902d04906e20706909861410703840305074029155012100c1191400034000d03480d40807540038071070748407564480c3d8090f590740e5142d8104410090725510000c540b60f490b154080000701d500066a60444403521408001407456200607424000808402e406c4c0c1d000b0203061f0701c110303265 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 564549739 1250 564548489 564548503
    0x302071806090c020607020d050306040609020408100c2d050408100522030c0807020a030f03080411060a020c090c0408030a08060a06030509060c090d0602160b1515031f0602 76
    0x15210200f200241c0d1500807603a0700000c1d0382d2040540c01c00c40f6450050b610400056502c072002800100d0080d507503d100d20100c0c0c0c05a4030402c0c1c1a0008001070928808078001d885050040349032101401280305001e100005408484420b41c036202d1800c4841389010744260750003000c038070040d560750307110300e012003000341408680900d0fa44000c0ca205680c0040d1500b00b01c0c81c499050b40d9420560740d003540c1c90300850fa2002c181a40d01400b0800004000741881900c0203200d072082d03840448508007460442c02c60031030250030a02c503020511020440e1940051400d96080c07003150402215100d000004003070388110b07000261170740800104004aa6000145180150f006079450f180d10b070380d141c00840484000b9100550b15410503000f26071050700603000741240c4c40004100c810b004003181e0f60306040b0390002c80b00e4619002d01d860b66406000300341500a512485c038101901c04c0c00151800107400c031418420304504158080040f0320075411450001c4064490404c1c040c4c03909888100195503495 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 564550989 1250 564549739 564549749
    0x7020f010b0a061409040e0a030207060e04110d0f0b030715081b04060f03020c061518060a15021608060105190b0a03021818160306031109040302071806 67
    0x82014801d14080c10324290020854030300d503550190000051000d14001d901005c1700551041d01d80610200c2100107000645045100e034006004d10342c5000402b800341980340c3c01162060b45804d10341c2d000384803444126091a80320801c00a071035500306141030014040d41d842140c141c0300b00440400d0b0501c29082c812030391406030321119010ba03600d00e405c0e000003003034000c99059890240810416140a4080501e089105003805401c088031031609a18001c401c07500c240007529424203000310360410050340c00c0e202038010810201443d01c04d0101c0c46c007414921500003800140391601003240d05c01e0161001385c81d4265040c668030307983c402201d60340f440c00b030041d07522500d48102d25900710441140b038501100e240201d040d0a0005c9218140c00075005000d9050304050501454004e607070b1204c040c01d00d440c0c4844114501820400044840c80004e854460103052902e0001d101103903808a0b0140c4441d0100c03140e098681d250301e400c070300b420b0f01a030100106144004180032802070540100303040d07030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 564552239 1250 564550989 564550991
    0x723090109091e05072c0406120201080c030705160503070506130f020d0201032d0b01020d02101a060f03041209030807140c13090606081f05040302011407020f01 71
    0x40e0b240c803034840440303003c2c440c0002d0ba03407050410076402402c84d4004950090450903c200c50718600b5845010396805450703608a1066004030641c1c0d589000e00c10080030b04000a140c03040a00f89500203440058003030004a11554080005011188500308503403901300c40c0b07038500e45840300614240d5542d4205840c01c40b00e034046c54002402441c4041d0400410390b0300a2942000c201d030503028044c01a00e080000d07030406403607400f24007c890007441e00104c0e0303501d0017a480801200364000e100480b0500036840d8119004103036002d58030382d0300249201c0303010f000c0c3e035000032800d01c0c8103110414080500396540d0014000b00d0100039900030a00914400d07402541040b9201c06100ca08070703501d0603d4000141a444140559404600b150408501c403c41580c01c654013958148005500009800c0c1400e41060700d501c4508100b007898050300005191030002414051a41242845025018240840f200c1e40d500005000c0c54800d40002000300746a0130152060300f0300e45030094846500c4002c03407403d5 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 564553489 1250 564552239 564552257
    0x706090b060118060e030a06050103050c2e03020d0605040c08150d03050a26012c0705091219061b090e161403100e0907030503040e07230901 62
    0x994028054081a0003e41000f06002410a00b0503a00007810164594040c031507002010001076003441002c0c007840c013680c0286030000500d42080121f040c2680d130500107031600101041c04000e80c035980c200010302c504001d42c031900d2412020740101183d40c481640541060300103240b283d00000c8090042c610400300d0600801c0383e106220890350080d00c020002141002981d8040e8896079041344086070f00e4020310b038083d11000303404001d00800e0f040308007240c51043c000000502110210001c24a00400c01000c0f80717031142c005400c5004068900340580308a1039040d681c0034080c0308140040d00d20b04000402c0101900702100144401002039002d42c2205903202911401620610206c1d0b0703030074004491300e58500049691074000340841a06200007402c0e480a01410840035520500810f980b06409601c0c20003021606403000d0031100b0039400070001400410310100c215410358500383e0800708651611b000032a155006809106821802010040c1744908032000074211507109a945c00a5 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 564554739 1250 564553489 564553501
    0x60d230f10140c0c1b0409050a0309080d08090a1211031201091113170705030304030b0a0c0801030804060c03210b010f021504020d0204200901090e0403080721020706090b 75
    0xd60711890300c48918a50060700038415050310b1713840d80192800040c0c0040b41c1003038156101c5140c03807031525003140410061002400031410400100c1480c404a16085003142072806041c0e40300d4807010400380080c4901120900d500340121038140707140003c5803c80b0b03513400d0048001c82c0000400c0c02807060702e506040900841050a41c255044407000b4004400e403140f4220102144541c40f14107240c1c0381c051840001610758007400030b440154082e1444056500d0940c107100d0840d030245c055007090101020040c0081013501094805554440c100300703081c80c40b00c1c2030564508603180d0091580041e800704405c0d55403070540140c0c00c14082031700d80b4000b0380c07074040c0300b0ba0b05c0b0288020113103a10080e4800040244c0b40038102d4042043c0050030000d0401900c0780e4640c0750b4207101c2d210741070714000010000b90550f8007807043d6004261010019419090aa40007040c1903006458002044100303a40d0402c0581148105851290b88500031035403150340e403a0600c050400302c0001c1d1084201d070400508 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 564555989 1250 564554739 564554761
    0x1050c0d08090d05250507120312140c030112020604050901140406230402070c0b03040308040c06051204020f220903080105030102041a0c01090b010e0906060d230f1014 74
    0x1d550402064101c1c0d02c1c42c4400320301440c0c012170007410b0301d861040310030020359000700492403070a01d402592901540d145960102040e1040100044000f207151000c00c0a121444400d036415200c0c11050074456800500010b000d501480d0440d81d840071428000081845503800443c656a80645c0c0901580380e0b03a04c44c1c4602d1115040b600440c00c100d400c0d01031200d00d0b1990082514a2258000d003050588032400c0130a642c0007240d084020817284401c0c402030003081109003004103658503042e4548880301030702c3c20030100701404c02806060000030745615a503070360b44801c0700c4510710103c00e01240007000a51005d803a00e600d00380c02140403e800440c4504040c001c035001c1c0c41c4162001d00e0342ca10f4100400072103501c000000d10080d56107080c1000012040c0070307924000d0206070380702c0b2207a0500310220342c2004000b0f07110601c01c0c1c024050070400124000228020b800d1440102200240700d200203d091214002051403103001d801208442c1000d00e83c03280c110010360020402980d034034a50192 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 564557239 1250 564555989 564555997
    0x605030c0405270f01060609060207080a0507141c030e010e031501171f0f05010b070b0c0a051b24010b070605100803120108250e040201050c0d08090d05 67
    0x150201040750008100f0010900140e02480040002c54282000b01039403a421900590415400a02102420071003150b04000a801400c4000d01901440b035055807000e549003000d11400b10a01d00b1030515142c1c0360703a81074964000310181a201c10100a1710300d0010905501451007501003940d440c8020000e0178000b071904983d00124200d00c803e41d080502c04a03140d1013000e41e5030214071910322405811200041d40f228405401c88010a00c103460f0106031040c2d940c16007008a1111050109002191100740c405402c0440c000029a980c1c28010084905204981d14503a0001071071486451074100000c90700d03d4501e81000e004c050146030001022484000c2c8100160541d0074041d035001314a80d94401c5070041c07030b810700007001181da0705981401c4d500031000603035080100e20010491a801806510a0514109610f4040080c03203500760011000f940928060601c1540014085901640803030b50706c01840f0b4200c800084c0e103828002c24000c0101e5034040640134106c8000c0c40f45003c0e50a80d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 564558489 1250 564557239 564557251
    0x110109020102100906180b04260304030f09050a180c051903021326010507020f1b06040b0403080a030605040513020d02010e090907080c1009050907110d030605030c0405 74
    0x1411031000020303080806020046002d50320642d486c4c1807030100c519401c8018030214850016154146070a00703181001840c0001e21100b0f104450a190840340a42411280d219515051000c800a1407841c11268030100e900301c0340d0017681da1000800c43e07103818100328101c141154018040030f030b1890411601401403040744100900501b503580165400b90f00500001c0ca0060f000c02c200c9135440406607134080c203400080001e0728a219035110306804c28010164048c09a00080009050350965a0799500e5200354a6050401e0030362140c11669a140840b03005000048850303031a19201c2c10085115408000c440c1c011915050b40068641020700403d0310609100380110940d030f005400313010491030070078400c0b030400c005200412500d68640344114020702481e401400502d05150140d45008002c440305481156080c140981c0f0035400b880320740c1034881c1a550443c007519501c006a0304810004074072255400f07843d03484111b055050340b080c02160320840c103c490304004c94080c0402c40c2e1040ea40 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 564559739 1250 564558489 564558493
    0x12150c080c07081201170615330c010209030706090612050a0e0610080d050c031e041205060709092f120906060a0f180f020f03090d110109020102 64
    0x580780d01c0c661030203030400b54001e18100e4681080c04e00d81456004013604200381800d401d29070f00c0500d650421003d50b0000000c0b003070080742952080003a078003c0030910220070440e00681c080000941e1446c5c1c2184c0301d40b26240039501c4050b9003050324041d40002c50f009000c0d02c0f81c4440080c0c0381c0e21440e001c8040384c0f0903856034002088005011000740c500102482c20440d00d522610140140030440c1d41d100e14009946a654141401d10300c074101032140c07940b4020071405000351085420084222a96040e07460f041c0c00d14015030310f9001c502c50059070b11101c91064105560b03c00d03c0404034120788101c902c5e5803100d041603183c10060003100c0c1d8103074070074407050380ca407400e40d440004480c0c000301060090201241041d0350090030b1282d80d04202d41ca10700b030f50482420b10609041494008000d40040a000d402c0d89040c1500c0c02d60f5002d41d8203a0704c0255031242d00070800c04100758100e4004d0396541461690380c2c50b254101d281e482c9694003514002911005200c0f00413a8184146102c0e140e050340 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 564560989 1250 564559739 564559741
    0x150e0d08060607141b030c2d030703050f0601060201050703020a050a11030d06031104050609070219020a05150901020601140d150e0312150108040b0f041b12150c08 72
    0x400e10185402100c022600c13050b80c0000306494000070401124440c94503c135004d0800d210310189810321443c04100f50203081810b0f40e4602c0145400021101c0c400c01a41800354200c07034034002450500e90364806011805021040085101c010640324143c940c4c0d41c00900440d150740504034101d01c2000e072000005401030100464942c4228000b0345035410087c1101e0510108141260407681558021070b1100f194040032091801d01c1e0141940c07000048660700381c6480d081e035000c1c0d01d8202d0640541c0741118848440004c6694255001014010282401d0212204e02491b4242a480300007114058407400c000003c40c401043c00701c4c880740d03402514002400708596181c0702d00d40c00001d549440c41c0e03110440c0641e400310800140801072a00069000d0070b050904852112444000c01c09041040503000c000105044440942c1c02008640c0882c809603220b0911081e040d15246554200b036562400000d0a4040c104e28100c91500400c0b00900303484000f207100d001c440d00e088001e00491900300c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 564562239 1250 564560989 564561001
    0xb0d05010807060f0507060605100306031a013b0a060602010b090105060f0a1202070804050108010f0b0a0f02010b120f070506031b0a020708030a030c11011806020c0c0d150e0d08 78
    0x5000d01b50803807140e030300030a02546442c002a0381461a04072580000d940d4074082003404000c02d132241c01d0442c000780e00c6c1c0d02c0d941009890854500c1e0785051a104952004a961400030000c0c2d000c0c0354282e0411411100b801c0907112540600903a1184000541c00d0401c401464500b11803401d0480f0f02c01040c0c142b400caa100b901c2403c9411241c5240140404020602103004d0280000c081d602d204503426552981441d00151200c501030304001c140d44400340090288500740000c55864401d2800e180e544c41d910311004138054200c0c8000c3c0c3e5041000d0080e54645101c0000e06107181032881c5040d0380c585078441e03080c0f206038001160041c070150040071444003480041001401b41c184684191006261503c0d00c04e45154410460748000070340d10802c02c0754042d8000202c1060202c1d1400901040d0903460090305100c0d41114007804441d070008400010b10403c1100c04000030018224480d0b010b41820080c0506400200e1480d0b01c60034003400c42d02045000c01e0780441c00c5919101c9140e00c0e1282c03 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 564563489 1250 564562239 564562247
    0xe090609070306080a0f1703130b04020604170d0801080a021c0203150103030e030c04020708181314010512010209010906050f040f0b0901030e0304061d060f040b0d05010807060f 78
    0xc1c000005050356900040354503401405480c418902682c42c82015180394a00080300c40c82c184480d40c0c00d680f044c002e1000c0c0703a00c0141000c003040e8206200c03221a45541c0009402486142d20203000d0074aa00428244590081540910b500d901c0d121103e00e070f80d032002425103071340728400001c4d4085143c0c2120040078003d1201c01414034006012a01185030a040810000d0802c0e001500459a6440500700600c1c00f000207181c2800142e030f0641c00c005095403251a94003070705031403c0c04000d83d003241501c1a113454500c0202d21916038410300080a2950409422a40c00e000e000c0c01007070b24140d041e500d01c005008030b60401e10b042c0e441a2481380340c08000c0300e0130781103d40103110403042040001100055074580c400604006105107a481a000001400711140c800c072101e82c98000703100400100d50003401c0307030700d01c189401040d00542c212500001c0c41840b9440c2030300c030401d902050200d861494000074055403115114204016600c403003401d940c1d81070501c42c0c1c20000c1c181100d840002841 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 564564739 1250 564563489 564563491
    0x60e06070c08010c0908161224021602030c041119020a05031801120504050c100e0d080a080a02071203020f13061121091011100501030b06010e090609 66
    0x1a0728000a541d803100949800e65420200510008100070401c2c0000d413400e00c030010f41d41d40344218a038410f81c541039410001c0d0800480c042c0800c0c18a00000c1c072100712813010300821101c081003c40d034804904203555018488460241e010340708103c2000d21609007841400850941e074003040c0e080240070070407801c041d940950301c1e41c214015000d2107400900c0030406018010508240080d580082070f0004081d124149250032400e800c1c0011322001ca07102080c0c007030441500b0794496882c00e1a00130141c0d076414000c200780d07401c4004641c1c800188401c0344040d205d20070140c2d0703a003151a150f103007007007050b8010120302501c40607205c43c4485401e0b000780d0003010f00091040c00d440c2071040c8d20403440c6da500b880342c0c480c402041d040c203081002d0610a00080c044401d802400c040c10f080307406a090f006000c0c01e20400d00849020501d5400709014201c03c0084410301c00842d500041c1c2d280501e80a40000e01c022514540440041411580625500350303810310043d04035900b03075485ca800c009400c10 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 564565989 1250 564564739 564564743
    0x20d0f1d0f03120c0c01030e0c0f010e1513060806010c0305032701140405060a181115280305070206040b0406021306180e06060d050a0213060e01020d020304060e0607 73
    0x803c0d851414100201d00c40a021849240805010800c0040d4005029941c445032407031132031341203400030307464566640c100805460000e180810994800601140c0070741034804030040c080c400401c4080c4c0e900c11418407035054401d9599518050f4450700c0054030561149000240401c005000141221038101c0d549929154414074001903100c400540500b10b8141820700300226140b881008203001d0304000080d000550408100011081114401508071b640c0c00e000f05900320b02c90740441903550b00c1e02c0383d400a010300703000c2030360f900740c000881c4410480000464291100e03042c2c181a0396802172051a2144000d500948440d80e00c59640000c501c80c014801c480c015401c2c01046c8407510312210a00140010361a40000318220308003a642d03581e101c1c0d01280003040d4402c00c0101c0707500c3c0c2030159211a8085000071a042c1c0b107100e0000045e01485030880d00b4250350742c20029549900901b40080040c0071380075514801c0c45064101d03102c2c803441c081c1201017039940c0301c50702e5241852001801c40741c1c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 564567239 1250 564565989 564565993
    0x3130609080703151d0c1023090303070221060f04080d0b010c06020d021e03070509010804050a05010c1710063504030804020a0801090b070c031e020d0f1d0f03 70
    0xb01404a0504200850150145da40d00860b0b10034940d00701904100e11180d640e0805001400160310b01c8202e87d4481c010032908881c0104003400710303480030419900c60075401000c50060400106501c1002e2419503e00b081ca44204404601d2004043c42d02d98061a00420158a082d025501000c06001140c000a040248803660800418024400340c120b080c0c0120001d680c0c2c0700e410b41100300380c5800d94650713414040200140010660401d007150b003003042c00c0c06d101540786e030346003003184c185280301802034425420700c0c440800c0180d10480c0d543c5028800c202d800b20780e49406551044200d241e000c0d2102260b1142d0400742424484d10f85030010800c400c0150200c0940c03a8a444c5031004240d8040340400c0340d010030320085150101d0000042c01005000b0441d40e52541c0702e40401d00b8000d0205030070b205a4419200c103241c40f0301740003280003404061004400010f40700095031550242c0403600096807415642e0350861090b962408907402d02c0500070b10031751504003044640c69140c40140d83c14 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 564568345 1106 564567239 564567251
    0x10e0a02090601091203080105011403130209092401031110050a0c022e033e0c1603030f0309150b040204050d050313060908070315 58
    0x2180e0112400c1889868200060790700070455008496004410440d5034140340c0c221301180d048502c282d03141c048404e42074150410500083e18240e003460201d408540146c504002c01c540c02c54014000c2d50001017441d81658100003100d02c50012152416004100b030081000c801c2140040a5500c4801000c91240041140c450250708005000c110302d00901951602c0c1105102c1549003640c40341503c9450120b006420407032080140040e04001e100705881c0c1c08000080140010414040c000320242030b1040d001d04140028005040c0d024000350810322400c01003007000020110780f045040e42503042c01045144101c0000040c5400c3c43e02d8440020346036940141681e101c1e0100080500b000c00006000c3d2040d170348400e5200000c0a200018490080010703c1c0710407161440d1050941c1e10301c4240c135424010300c501e5100c0d1b00401c43c10008680c9a00440303080d04561107002802e = true := by decide +kernel

theorem cover : BRFrame.Cov 564388489 564568345 := by
  have h0 := BRFrame.cov_init 564388489
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 564388489 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 564388489 ≤ n) (h2 : n < 564568345) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
