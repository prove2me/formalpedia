-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2861
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:57:58.92627+00:00
-- url     : https://prove2.me/submissions/245d48b1-f79a-4a7a-b465-94caf05cced0

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 514388489 ≤ n < 514568345 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 514389739 1250 514388489 514388503
    0x803100e01030503030f220c03110604080d0e04021b060f0a0e0c090402130e10061a0d090213060b09150f0316030b0a18051302060a030207060b090c03060102 69
    0x34582240195410343d12150344c0d1340001062400090030142c0410783e00208865400003415290f0040406060145803981d461420b80c441100c0a80c10100482820b25040d4240e40641d58007000070b10300c180a4200c00c4840c04120201c40e40c009500300b1482440800d9401d440307409001140c010085418880c4510284400051402c0c80342403400014841e2a140410072054010044811310b0752a1a18000200c4054441280c5210309d03281041c00003c0010118a083e1488980e4200700b00e5642c1c0e81010008404204e00c0c810344030001009042c42180c0180c1c00071030854005031901100c00d10b410a0481111000c0d00008087d580116140065241403484058103440c404202400c20180c9004d0102a001c0909000e85003280f00070b11040f402c3c480d901003280b05c0d4000700b07103007007090b945c0305d11800071240d90704285215400c041c0050780d4141030040040303c06274090060352401c041202d08030b00a41200384100e81083c1c130742d030900303509070b0f40d0710101405102c3c200c910641d00d00f0b0401c00a40380600c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 514390989 1250 514389739 514389749
    0x306060f0f192c07031b03020a030f020a090303080f010f06050a23030105130608070509130f0305190f02070b031906080c01020607020a08072003011401051207290c0a080310 76
    0x704100045541017481d0600203004580e034100981c0b200c2705402c0545c003914100f210a08203920100303200900340d6020004e0340840707001c0d4440c1015a00d80d0001112801b400740103c90107007005400421800b4401c5005003910801d51130240c0b500c40c840074070080744803441004929071981c00700c0144806e203045c8150f0407140d4104c083c2007224901c1c0c000e40688800e4240328142c4a2095580000c0c1105400001132410304e60083c403820200800345000313000d40d000851541c200c050011052a2180e00805600c40b01e07044a400509900c0d150480c1070305a42d00041410740500070341940740b203040c0c3d8140141c40190585a015000c0314000300300080c0b030048010100011036102c4050f02c030105007100b084850746500070054601c1d007400703020f00f44086510920810f8040d031030072901c55200d196842c100c1d4161002141c050000d4425402c40f940d41c1c00c0903000b00020b02c503040d100704030000d4594100f030310310b0360110b03400c141007001060b101030521403a00000c0c0d556074400800c00121100d41212000a04 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 514392239 1250 514390989 514390991
    0xf0d1407052505010b060a051201050a0308070f031808060604050c27030102091315080c100503061c21050708041e170304050306060f0f192c0703 64
    0x12403100c480d002403000003401c1070201c80c007016914140032080d080178014030380141074980c0d03c1c1e00910000f01160b024401c095100031891002184525142400c0070460b41c1000c0780600b0400661585400a1714407001202442144008001c516522001c11002060a94080c0c02203140c07540601040d60001860022000402c00440c00d0038005880514117154464036050348003184c0c01c0110740213200f9030144a17446220b0704003034030405800781c002c0d031000a07422030b10741403081d91313003840d2030f5115642c0d00480d44c00b0383c01c1012030300158859005168061001020100c0d4880d05c0059441e0000b0040015588a400b4a8000c84030b0496040b50000900c80d0349800707031a040d001d495070191401039001c0c881510205c0344460300a0507200009074064a400c920521000c010446490394907171091040034000d014210001c2e0462034290014003010030040c01e9000d1030500c1c02c040080d1f005011915180d0825400c0c40444c0c4000581d0414060000c0d0f105404180341e1403c2c0780ca160b818005004100301 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 514393489 1250 514392239 514392247
    0x1b06010f0513020a080711070806010b071a190908090405010305013606020a03020c1c020d030b09010e07050d050405030306010905030624121006061403010e1504020f0d140705 77
    0x1306903c290403940c00400d0b45082c4540c2c4450580d0326003011100d9020803402d11848001141c01d490071310041031220b10500742c0145403404100c6006518604641d050b44043c00101c03929845100e58021400e1580314640301c13890610b5440001d4221202a04181c4080c0e42d61203500322415800080d2100c9064113180c01c04030600c40419000f802d8107035010060103981c011540c100000d00940650325407001d0b00d01507c1c2489168074001d4018400611100014401d4481a03e41680a80305c0e5815591000d0b04022140c0c0c01c14a60b5080e001c0050700050401004000d47c20a040b0b2911940740640d1040c07018661300c1c1441030004100c4600350704414403c5d00305c0c0c024401d10501c85075201c600c03a050b00707400c40c0c0b40480402c00906004c645040006140c010282c0c0850f25041c241c2c00b4905a03062502c890948150702800602d2a000900603450210b10800100301c1902c0c003200075070700c3c511004001600d40400c0d420444401c0e00003040b803200c0191244007020208034541d001951284040c80c0007030074 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 514394739 1250 514393489 514393507
    0x405010e0f1e01030f1e050d0315080318010c080a0305010312080c0d480503040804030f020a090603080c06010902130302220606050309210409021b06010f051302 71
    0x40407810310008100c844170058600411000007600c100381110302905080510041c00d005441d03554014160000a2074492000d555030304c0c0d000620113a030450001182042c42400c3d01c202007004a80075181440301e0342d00140d0001386208010f0061302d110340c1c0d01044551561030701541d4000024010414061080100280380342c0c03130b400b5224101c0107141d0101703440c4800000703001d01e90b0a040c0010501c280824044803400c0c100341c100450944148d818400305140c42208584a000658000344000d0040000b0004208030384000100380c0c1c0003d20300b00200741c0d116003042c211421684200c030449000304544c0303000c045c240300c01e0740180398a21040d45001441200300d000c3c3d03190b41c00000e10a0886211307001540250b11211410f54035a074204020980d100c020162254000301c581c00740c0762049d0041032150a00c4400349140c120800039103281480d090041034400380d000134001420301c11405c2c1d48860500000c0006600810004284565860070101031121981d4880a9440c40e60300401c11601 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 514395989 1250 514394739 514394791
    0xc0a030e0406051518061605060109110901050c1c0309050f01060b0f0f0f0f030f13030c08180a090f0b060711010e01140a020601140d12030209030304050405010e0f 72
    0x241c034007482240f1640d14510703e075030044985c242c2e0403050740104002c01c0020328020070020b5003100500031400c486007170fa680c801c50300a450b200000820002401c2c0a00c2c2490350083c0013130105a02554184c4020303074001901e464003100c86003c21400079440b61810000d0000c20310100311400b2180009009140c10300f04041424450052039910f80500000c1d589260100c035402c3d962a0112080155900c000c650007940300b50300705481405410326000041040c507032000750100c0d4015816101c003a20916a600c640500d9000511182c40101b82e005d1048616030354001d00f00042c0405202c0000d029562050801c110780480d5001070081100b0444000840c1d242c4008080101c000d1821010480203000100c5621120b126102020302c00410160172490700401c0003410303910b0440c8910039000c12441003210071301c0e001101601042c00850107080d1075201b500109402d02010701200c1ca0540c0c0c2d480030a0403190f00340d003c1c1880e07000740c4040c80320704510f4100ba2904481889091620000400101c070 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 514397239 1250 514395989 514396009
    0x80901022803031d0601053c100903030f0810030506191d0309090601030624030f02030c030a1a1201020418090308150d0609030c030e03062404090501020c0a030e040605 74
    0x903c50070382c05203484103079400d982c0a0041158880c98230007900000030103d607084600c2100d402e00c40d400009280308113034420b03848401102d80603a900e1a8111807150140d940020181c00c0c00c4210441340b60100104008000141c010303240c09c0b0b042c1940c003000e08030b4a402c4603c242980080048040c12408400800000b692030440f01107401d1081511501c00580050a046d40108140d01840d844044e00155990306180d44001030f8406008200300144400c0480c0701c200c84010405000b440440e02e00400c9a07c50b0340c1c82c0d0700e4071a03564103e1050500280d000c9544000201440c2c2d0006000d20001c0f4021100b0310352103400d40010b0051606d1558094841302004041004801401013a03100c00d507a40756011288030f420030801c02a209441c107000f04a480100c80550210320300401007806420001102886040ca4003101e400010ae07800c0c5008a0012a41170301c0e03449911591940c020940030b04c014900307000a4001070160115600d00030300940354a9005611a07031904004000070b8954040c0c3c1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 514398489 1250 514397239 514397249
    0x11805060a0e071409150409292e03080c03072001020a080d020403080d02030f180c12030c0102040909051608070b0306130912030e0c030307080901022803031d0601 72
    0x242c005d0f544040c100142c5185200800e9880750411440380d05001042e812206940110001079070000d81f1407103501e5410900791441c0003084802c1c44901c060380351641c50021790f14a1840f542c2e15003035980c1c4072250390360000704040b64290000500c23202049842059001d4585040407071164409507440040d4507490004005003ca0b8030018401d0309034940766049501455005519070f0700e51780da00501c2c6000f0342040b140750384c1000003100030800254004018944400144004001c2c1450110500c41038039107250560100b40320a00c840250301900703001400141c00c039400d0000300300030346041c0b540c584040c0503422501c0c1c442111041c000c0e240c011034050142c42d10300c00069070300d80701c01011604403c028200484802d10b40641002089115220078003410010707034085c800c042100c0342e1917440d1043c41c01000c0d170680c01000048000383c04400902030054050040e194502c456621110464005124070160101e90702160300425800d841100f01501c1100c07148001c0054a10140e0741da44018052 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 514399739 1250 514398489 514398499
    0x2030402120709140a1e0e01060e130203070e0403080609100305060a0f0f0624110a0506070f050a0e0d14010f05150f01051b011805060a0e0714 63
    0x101591541c0428002140421040b100150b550324800c10003050701c00c4039024110701180c089001081c0d14000c1d180e0211695403100d42850b0045548401800b0507072203148255281c2d1030000f6250030400d00c2c640300c0c2d5524007101e10011014810503040406582181d000c003c144030074007001c80d6008032410740c082810350700c858641d2540b02d2001d440301d0f07450b0300052551003024200708403008a03402840b154075400c041400414411341d8040140e40c2d003030195554010640c5040f80039913061b50f241226400e01810a1406100d00740055030803c100e04034261003a601a42c217010000307501141042d41075169140c00c50408905410040110b140304c0c08592080402020201c01c0c401141044070280300400002c02040364641c44400240504907600c0c5004504050349285e2420400b000085070740c016900e5925068002c15401202c1c11401415080c030b6588140300380d028007034880c0140a20340240c00904051901003031388015140800007810141e00f05600030800c8801400d04558154401c4038 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 514400989 1250 514399739 514399741
    0x10e01030b04020d0b04120906020c0315180a200402120a021b1902090f040b0c16080f0403060b0f030c1c1719051303030c06140c030612010e0309040203 67
    0x982e45990800300500170004c81001d00c42003180302102110a01e0564481e69003030ba955a10503a03d440b0203009440d0950040c50b440b1824861401c02154024040780d2011444502c1840445c5040f100030421208035044138914188400070311103184044070112000e500d456100c030480b910400000c0c0c06084429000300b941c00480f40345003000b42c1c0c03544c1c40c4e90880d104020b0055410742e0b02066000306071b026040100c04154060011388800d8031540c2c120601211544805554051a500030300040c1c43d20303400801510001080000144a01d1303000d15109522031303086d0708043e030454110018180c4200381030092510140c80100e6018641001110b00060020960390700c2d1302100c80b96a401006681e5580e02d400b52040700801800003503c2448401c09a071550600c01e0742c440c4513140300c00ca070514010104100203480303020400c6a4911801010407418210380c0c27603101c50300003594590080031000c420040142400502c80e03034011000d00092102c001c0011302180c40e840f810000354060340d0000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 514402239 1250 514400989 514400993
    0x100915021c020c0102070f05030d0f0e0c09040201021e15130b04030e0a0306051e0c07031d01050415020a030224060d0611030106110d0c031b0c052e08010e01030b04 72
    0x94140d81d54250403682d803200810040c0390054903580941640717414240341042f11590800644519044191071070000c003031045070340c0c040280101005000702d0440c4101c540c420450882d03426202102030300079000f00707c05404503c0c00094114024018210b054440a0f0134000c56071400840b50402d4060a006011031030b0000814020600794002600c420305100500494120440c03044000200f01180c002d41915020901d0040c1d1103a081d0203800140c05811090744252604412a0542c005040540c5000e91307448900b520b0ba00d403000c41c540581c200c1d070b14070014540c0601c900a205c103041203140102042c0540e029104c5c40010300002d01942880c05400204802580081ca261107000d2010b505d03513a641400420038038011001c0d8800d4016102c0041004e0301a941420620764503496810340704401c1e011502d10160300407819030b12954075000000d001d072290400c14603501c10704180d107280248040c52000364848000342ca201041641d00040140c1c4280e04071781815250700c400808a152070b54 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 514403489 1250 514402239 514402241
    0x60301020d0c05030901050a05100605030a0b130b1503010803120c040302030313060e090402060a1b0209011203170721060b040f05041b1202090d05100915021c020c01 73
    0x90094509400d2802d1414050a600080a584200444402800310f40d480c4a503803002d0391000e8035005d03040c00d541141070003514040c101540c0d200440701400542d0982000000700c3c800e02d1817055150590b0380382901c032120709159200c0850841e000304d1036861549044025503480c401c107842c0400f15942e81c400f042e4070324420411203008540040440c2c1c0c60340e401c0456410111564072034500441e40507403a100c42820000451341c441c070b800a200c1410803078040c0080d110b175807489030a030071040c81e203940031030041e07844001c1640070b400452000b01d0222200d02d405807525010a241e04840c4071080c082041450380702020f001c000d020759840240400384947c1901c00b4107070076000255203450200d00428420b88c0f41340410100c81080b10180b018221b1613115640114080000340000703040781100c48402101070b00248549480548010030107c16a21100d081503900340c0f00c1c074610781d00c032000b000a02403243d10741040103404074030451904603034400184036081400240303002c50307401040e81101c0c0352003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 514404739 1250 514403489 514403497
    0x312090305090d1b092007020f090f0610030e0a0813090204090b0a0b12180a060204030539091803160b090a020a1e18060905010509040b0f06030102 65
    0x15148648184441c9400d80c0021552900d6002455131100c0018402001e4007505808280d100034510f0f403566180d000140551103402c042c2d0300841e003540000703c292036801103280301e641251203c01c0d20303051035010081d014040b64460420581012030000e4010004900c00f08040e900c100c02c1d90b611240c002000241811702e038031401c01d0a1010800003a00342c801d81101d00c40050443d10280d0b003540700c2024480380c0c0146d51801160b20050300016507001091010910076030f18130000c580d00d0035040c0d0b4510f010b0364003540085801e0b800c11690702d8440c0d802042d8458103405107110a140341803414030018001c0841c0000390303210b07401c00000702f50306403d18001001d01114102c250f9580d2544040e04155048004004681a10810b800213400350004103807120281c0d03000341071360500c61414a20708082e00e00c802c412280c001075904002500401034102c141d48440003a80072030041d180104100864105038040c034040c03a03a0340100300008855210680c0d105c03403042002d580d5501d60700701081c02405 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 514405989 1250 514404739 514404757
    0x616050f0606090f010303170c090a030602040515030103030c06050402060415020c03100c050a12020405041d01051b0a08101517010906050d12020c040f0b0f0d0312090305 75
    0x1500c103180e81003600100d0110310618056038410305507204c80340b1240b610301c424400a4001402c2400418a00d44c0810400e60451501c4d110141001000c0307000825007072096000300c9a5560004040001e8200309480c00e810000d144582415589140c6014060182c044070041205036124000790441d5101e50a0b1070150030030b84100801000d210034003030b568108000b0568403a2045d001300500c0c03014213000c0e0390b800880f203554a504006c00c003001036561210000070780c495180c0900c030102c0e8640b1144074a00e450790003c240c00c1140c4100c5800c0e1821110042c02c40c0c440c1d444400b21040386242414201d844c0054a450f0408041c0e4894010552a9010b034211800c0412140b4420340300c83c1e8090345545004644203848607880c1d0ba1082c2c00c40c101c901900c1400e80101e118145103010070310180040c0c0701003000740140c5800d0070100380000c00701c83e0b1100c0301c10728855480f6407100460515000ca911040001d641d40500c0596a0700d014001341c411401002c0b000d51160100420940b02d20b080d2800f0030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 514407239 1250 514405989 514405993
    0x80601060c06061503020c0f010b011e090b0d09170921150901021306080906010627030c14030d08041b08030d0b18040f030806011b05060604150f05061605 68
    0x20144d0800801035400618031100d40d00c100320201002e0001845101e408103416124901c02c0306500506001401d03c0070641014421266800205013251400600c0c0d00986004001140f441b180740580c000490320074906a400e20a211212080d22001c01241e0a40d1003000500710406540446902d08554207945080c5500c090003440705450054000e840c0c82060700c030703120540d191100c8040f600210304455002702603024030b0042203198061040d0385030351800d401d1046000403c42c400c00c0456101544101c0e184d981c1c1031010000000807a10401c1c0b4850124082c04040e80b02d00e4008100007805013003e403034900400611034103e038924130010014000c0509890f01d406002c0c00040003001e17003981960080c010307a01d00c2c0c10344220100f003407441298082241802d80341b260324100c680031030023084c4505200640358082c0c00207191500041540c1e108000403c1a444c02d101404141c034480c820400d0007440c2c881d0b091000404010090003a02c0c001c9e903403c0d85400109815491000400001400038 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 514408489 1250 514407239 514407269
    0x3110d09030320120c0702041401030c0602010606030219121b05070c0501080118090303060e0f09010c02010e1f020d061d011d150a1a1201050a080601060c0606 70
    0x1070b01030b044249407076590102007108090742c5540018034400c26500c00101500040001c00e0100d5410207000494000f03817000a9007040c0c0b05042c41c0c000000c1c1c0040d507a100c0d01c5202000b120f54240250f802401c8185410b60804800d2003d240482007407281c4407060140003c15041100195032080c03184e03404582e810b0580d08080e1802a00c0e035070024005403118006900080303101d5004180710782c1214031002c0e41403240300f100003000004240000741201055220800055101404000c07035000b80008144543c0c5420b04882d42801c48208252200659040c480d07110402d00001c030300840701071149420f07000100807880c136036002441040a01c003042407030310001040c406e00c0303021064078285580c8196580e50340c0b90b14821402010541200d1070300c07040d18000406140b00e401501400034006400c2d030220035200c1408841c600c01008800c9010034000c680810701e120755280e00703030060400759003a01c0c565052079a8035485640501901d800e201040ca0340c2420054241c5c854401051060958088 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 514409739 1250 514408489 514408493
    0x7170a1e090611031201172d06060405010608012607120b07081302060906120406050a0c0c02131503150b010801140a0515070501050108010e062503110d09 68
    0x2100c4032034029800010560709482c905450f00004990415541c0ea003103a949a28040d1010861700d080d581e10300d030342d0050b40d100300c40440b410b4124410074034012075041e00310224103802602e03222000300750030710560a10300104680d82e0000c1e80541542d20684010604948405411081748031800c1c0c3c0d1501c0b8400c100780000c0d1080c035400c40c0e00041d4400c1d100c44490391900340d402c0700c909905a401f142d2194802603c60b00607d06400140000680584400d040c00b1003ca11710654200444081d81d80300c0c1c031a000c012003051148500b42c0c8017125410842c0c80b00405401080700800118191202c0c59600d40a0109a00b1026803401c011540100205a426140d03603c244c007034000d010010b40032580d80f10001c20140b10b1040342003130701e1178081d0503036072000c1c42c220800143c84205041c0030761786001000008042182030080d54081c1032440000301d0903075524000780749031240050154014143d566140082c600400c2c0174600740c07442914000c182c4600c0724004883d40d00c54510605400e5151243c2402 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 514410989 1250 514409739 514409747
    0x3150302180103030f1418040615230403050318011e03020c07050406080c01030504030e0d0c03110906060711180403020606210a08030c04031a0f0601020307170a1e 72
    0x41030f00e20036514019680c4001005079079204518624001000d01071041800d040745181010700c8100c0020710100705240e5030b003070512090b0b842c2001380d00010364040c1d5003005071540b032030103150302c51410080d54030b400d20310f0b1211501c9000e000f03a80d00b9541c120920182c0d113684140c10b0600402480b0b0503101c42d07441d688030702030002d51090888107003134010b0032000610b519007881080116045100503024070443d0070011001441c000b0b10403424860100c02c0f402044c0c403071241e0a0151842010038001481c254141503036507201c6005107a1080302007504010326070b202c00064a4480d580980c41d2003120301054000350401d0041c403c547c0014000c041004203040e0300150705d6004610585440c542c815031202e0a110b00c40c507004000400760311000e0014001600358004581c0b08601006c2d05003000c1d182d5441c45200802c501c9191902079643c014809021080c55800350001c500340000c61600d001a5107024550780340c0360140d40300042c00f1a1001d101030003100c0e55005604501c8403d0714080b240700003e0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 514412239 1250 514410989 514410991
    0x40203090708033f01091d03030a09020a0b18100c02030a08091c02092e08030307080703090b04020d081216021525110f031b0118030315030218 63
    0x943e6201c5095204103a41c140d0704000131000d001d40b0304007421341c1c206030701e0b0070181400300c503000303581140740124108044040c006140607031002540400c109000d030040001ca4002d5411280790303900c0811803d444104442008150008159500c00e445c1112220543e07082040f110069018000c525002c406c0082c40c400070050500c04660608880c400800d04522600740010300035006140b0700302254800e4110300d154440045200f101a4103201d03004030144da6a0960341c00a1540c0d0300c003001b4400b40b10342184590754801c400e1304d020002c0d9046a2545810f9170000b80020740201d2500e4020b07001e100c1c0312400c07605030b0b111210503c0e406050010703840c002040a4049840103000310b2200342d929552034222140503126614a2808500d50701848031783c043d05501c1c2250500c5011510102c00c4901400002124103088000c2c6881e0711580000341c0c00e800d082d8645228592410904000c8959001e00008065405180000341d40f20400030100c00c00c0c2c26600040c0d802002d010000071016004000c52b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 514413489 1250 514412239 514412287
    0x1404030305120c07030e3106030c05030d14030411040e060103021507030c1101110a06050601030b011e030b0f0301060e04060b04020a080f06180c0306010906050a0e04020309070803 79
    0x1203021590b03603e002c0e1105000e42d50f0300800041e05281480c155142900042c08022040300c41e02e41e000c3c07901c100550750301e4803c44100c0a8140c407030101300140300110100e44010302c81036014102d80042030340c0052540b001c0b942c40c0142c200c00403001c50f0500603441c01014581102500c20408641c10b024070541d1000c0911040344030706411094000c000d9604000d03516403680c1510703034804101c0c540d9075410310340c0c1d41d0300f40f05070400948010000c04003004100050355903002e681c1c00110340c20004001810303295011741d05418440404070b80a03100808803503504110103245400079520811200140d0854918802036a140d0300300000420300c00a003044103401284a4101001480c0c0c00074188000c0c1d006511a20000c20420f5000540c91015000304590081c001407000a6501c400301500740690f20543d00c0c0c0500000c0401004210350708032491801410660a0003030800c1c88008005281d844000c1030a0f005640200114048544c00c020741406040c0940c2900c0d204e44000512600c0c1e06004022 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 514414739 1250 514413489 514413517
    0x4020307060c170705030c0111090121020d0227010f20010f020c1b09130f05010908030709032a1809060926030112200a0f1a0909070e011404030305 65
    0x480b85071429940c103c071400501a160000282c0d90741c16240b1650008500e4338810640821103149803c0e0144000c0801e0340c0c502134070341e43c8603030185e000484080b017040c00740c0e051140f84050502016040903180140ca800c080d0019101107501c511180900043d00340d01f4030550000c1950b403a86280440c10140040c1c42240000350580d2201c00c1107451881a00c09103044c039460080e8030049003101c502c02016a014030300104d0220459520349102d40c0c822107650001680c90031082c41080203000c5010818100403180740e07464042800351b01000c0545204140b580b2481e45417028080b28a600303c0032410307811290812100000c3d042a83c4882203d044e031081c45825511840d04840c1e280090728140c0300e81800ca50100540c6d95281081c0c81c00c04a0501100d007460013000740d142c1d5401d4408806440d04561614584e441e0440c2c0b400420100410320040d500140b06580e01c5071102c1241a43c06910703840c0c0390025860250041e81e0704a01ba8054000c02e00000a001c018940c0081c002c02c004804020 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 514415989 1250 514414739 514414751
    0x106090e010b06040b0a0c08070b010f05041a04051008100b03010c090602030307210e010e010c03061a070c03080307030221150910050604030f11030604020307060c170705030c01 78
    0x304660880d9595003a05910203018007051183c5c000540141400105506003158500d0b4240c913001032540004200f00d5041110780c0c010b11040840c0ba440c04001d10040d01c01780030f903d045070740b10304542e10b07248100ea01850b540e90000710060511200e400041c200e032025510b0340344e00b14483d00003a0000c5a5428002e43c2405c1c1c40ca408103100d0541d1504803a0258061415900d41000454102c640c074107420780e11f0303038500003142461103ca21807403d000d4801c2d00002902040c452215003983c440d5140c0030181890701004200083c48001c0924075080b11405036a519066450031055810755500050728010012003003140158142d0300521004407015961604060090401452510215440f030741c0300030115201e551504084003241e400000d82408091303d10740b128049182a0030681c010744101880065003418802d0003802407a415500f034002c0c100304d28041c1c0100703a80301100e2103850104640858a1401e200701140782c1018490540d01641e07448081d0b082442c0e81e50414030308003a4551070310f0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 514417239 1250 514415989 514416011
    0x1050105030c0a1b02040c0309061a030c04050612060420061801050307200c010305010b03040b040206030a0609140412180b0f07050d110d090513052502010609 70
    0x4400e0724495414000b21500d44490b414045038840840601d0030403090344a940c810060b81c403800b5010484c20281d6001590002605002c000c2e1034844010944d00c11161080256544010a42c010b084200fa100801c2a8031048045a1480d406000c13440507402154180410004011050302c6464001c08204880104102c2040b03514807840446110704661540c89840550007040510f07485403040c286800c0700180003403424409030424a0039485a000744180f40019a010302c905809011421860342c01e41c5095640e00001080240000e8030507800400000d0304030145800c10f00141c4006601405600717650083c1044101c41960308803100b58444652500340e510a4a00002c4803400d8001e1001403494982458400d512082146a00700400c104400c0032032820403519600c010b0390754030f1403e201028003005007080d035110000c404000402c0710812440d070b180c8084e20800c3e0414440020180c44068240258204008420550800c09105082044d4040d40000102da5103020b0900c5214116 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 514418489 1250 514417239 514417247
    0x606090e0c03010501110a0221010f0207050c010c0c03061515031404021023130608040f060f021c05040b06010224102103090f05210c180f010501 64
    0x441c0c811100050600040040358418030b1b503028204100000e40c0d03020800754010612190030148542c0398042441e0341d56a40c00d2091064008001c100c101c110b01f0720130541d54080e160380b003203981c1034108810610107038144400d4040d0040210b81c003a900b009041c0768500c50280742c800c07512545d100c4110054803004071030300a000302c08103544840302c241404e90740d0f0b41c2000346035030f10008200304000480741511881c20a04215580842200d01c602e91500e00c0784110700451001c40d00644108203a041c180000140200224400980d0004010410031000303200c8200902424000c01e4280d4182a000310300140107510043c00b4a014010b00752003961520010b80e0784984109034403025116221901424030840c04090313400540701d804032a05181e98816480c3c03240280c214481c1d2602c00841d2413402c042e01322604000811001c07881041d40341c6000001500200150010401510081c00e0311801600a02c031154041034001d142e40c60300208505003281840c8112443c0c02c1c540c01450020801d5801 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 514419739 1250 514418489 514418491
    0x20a021509090604090602191119150e0a080403081305030d170414120c0601060806010c03030b030f01060f0e0a0603020303070219080703030512060d030207090c1803060606090e 78
    0x805032001c4960340302c3c64140700003800d01c028103a803260703428843c006080c282c1001880c21161655075154240a4000b102400e100b0034030140200c45c4150000600003a215095130068047c040800017402c12208000c3c6081c0111040002e080e0305000070701001300803402c009001030b140a00e8202c098603448406140c0c0d6021008849404590511107400e00318003423441c1c8640c494802c440035a400c5090f40d0317140c5d1030002038490b0703406000f2000c20307000401c113800c100c5180108500c1c13030004040e0800b0300010f452500109005001c0648a008130842618208100c016000344000204125507a03141355000766800381c01818100403581e408518904400d02400c810750390020051032800c2982e134200700180f040c6454030009035130900c4000030210018072542c402180617455455903000c0380c5001d0440d030302c4000c0c00075200b1321000604402103031f4002606010b4030614000003d0341f80407070300f040e240040d0140c40455100355095000c0704000c02c90304903004540351034440800c0103071249025400c13414 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 514420989 1250 514419739 514419757
    0x90a120903080f0d0509120f130513060602100213050108040203030c060f0907060e0f0d14030a020102030708070f090314030c06040c0e0c0a05030a0b010507063905040e0709080d020a0215 82
    0x40134031044075003120400041c011030542501c01c03646543e580ac0410381000602445c2c0d240c1660324101007042d21780501c4007241070011400700f10714100c1c80f1044049000b18078018541080074000c0000d086450400071601c00b41c084900315411407600840422041c00115142010750207460341c0000d4440c02411200340c1c5003c02000c00c005904158180840300105003002d071980520340b107840c1903e6030140014084c01d038107640096900d01d08040042e0104001a00e41d00801906518cc41c12940d4026040400d5982c400f60744141041400701052071b500620201100034060042804104804840340c14100c0c0c0441888503250ba50380c07554100c0c60701941c0b5150020807010030000e81c0c00b0b02d0aa029401c1000305040c407600b000c15549031801180c0200020758080b034a4007030300d001507000c0d1011450b03c0380e900e28210791180010450040090103984161a520070350b60b40482d140a008003006400340898004440c00f68040c140001d590303022441c8207030700940310080b00360041d030088011150105 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 514422239 1250 514420989 514421023
    0xc0e040608100b1903050c01030b0f0303030f040503092206080c0108040609330605090c070311071d1906060509010c1104050903071109090a120903080f0d0509 70
    0x1050080700300680150b5048a81c40002c07290100c040751382c140b905901031405000107100302d40071400090201e4030074000252003940d000b4030300041980c00004683e40302c010301c43c2d00b68442d00c0707d103003c130b1a6000e41900a9403040c04504840701c807a05e409048580c6034001c00b0140714081d03a0b00340321074480c5566030b401400541100001004104660400f000b250320444118024555105000e030303682c106010015400325111410701c02c0e01c8070502840005e800e0449080c2030b24241410520094400d408000f0f090001600f5017403158242030001000400f989031000300070b68041048000700440480d0103248a00c115045511005803070311503201500c08503141c0d18980b40030309005407120708010b8001c03960061300c64000032042c2c840340a03940c0510780003002142c82c0c04803490403072040942c0c1850240500200001c20041c0140000d10540150300603944000610b00c400d402c6070a01c9254001038900100040d0103030004000e02c000b4144a40c46030400c10450311003100c00c6881d0101c0701c80402441e = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 514423489 1250 514422239 514422253
    0x7020f0a23120618031201060306051215070e0406030b0a0504050f0a050705090901021b010b0f0405130b04080d020309100b0105031003030f0528020d050316050702180405010c0e040608 81
    0x104513030348000181124060201c0c0c1c18000500200c00000703d09800603000680c0b2120104182e04286104903440661a40904440841c110b016060604010002010440c01251006040d00c442d44800003454101d2110000751400e145201d02412042e24100c400d80b161280700341511038042565215075500102030003600740303044200059428040c141d061155400c00600c080318810301c0b00490b54135401000031450040309820011400c1c2683c01c4280100c2c03c140030000c0345c045145800e030042d03074420f40b144402c0d09c2c1c1d03003003200341400381581c80e140c018400810b0042c40140020b4881c1c407000001402e0101745601c02c0115030034002030f200c2c1e45420307089040600000e07000303a421200b51b582910b041810500302000c11b107001c00c4280504542d8524071b440f03456405d5410310208007446241c0c14000d00d14141a20508020b03115907401004000c03000c80d101c0219502c4540d025042c62146410308042d05140c1407841c02403c00d9140c51002c6118154a02007a041c2400f400e0129840e0704060041 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 514424739 1250 514423489 514423501
    0x515070b0a0902040b100f080c0a050f0d021606090b01051516060b060a0504030507080c0a06030c030b04110d0605032d0312040305030a0f06030804050607020f0a231206 74
    0x152000300b200b268000d0300c5280700307050340e29103140e404081105e90791075422a14041c10302902d01c16001c0c06800b00c1d81c2040000c1c019454010381200d003030192420a5641c1c4882c00100c2070000d025503080d01743c1d000341851810f410f00c000c03078010a030950b0081168600756640c5074104080c0c141c10304959000b90000b400088991146c5e110101507aa00400010400c418400700240c2c2d41e07888a109680801c4001ca020b1040c41401c203c0100980901001401c0700c3c4410070010700034040911910040680340d819010013944250400c5040c0580548107100c00516a40001519040100341d0340301c4501c2d01000103602c4c680000c0621024500c0811503045181e140002410f108100c09648117600c0100885c0f5110740c005615140304034060398585489003050448041034a25143c3c030010030700d051070018008182c40c4803c0740c08681c0704442d1240c0d2040280b002c0354440901c2e0a4141d8070820300703000041d4140711031000303240450705c841c2004800b98000080061160f554520301c42141d000f0000120 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 514425989 1250 514424739 514424741
    0xd0e0d020f0c01090e06030a060204080f0f1908030703020903010f020c1b130c020f060702031308070321020f0f0303070f030e0d0c140610170a051f0e0312010515070b0a 74
    0x5000b0310047c2c15140c4150300b42c0c48903401d0703030300c640e0090080d6070102e01c10f00240035044c00b0351002c0810844c0585014072043c5c0d0211101440c114014108100000c0802c0038203000360304a500f2010050001d21280668942c100001d40100c9100d55003402500401d03d40d0900c0c00c40e606204039002030040d00411030031102500200146a0514190b01c50240d0070703c4149403c004840c0b01d45030303030381c0110b96408103955550380d0380c109a0700c514104e5210b8081070000600da10000c442031000a00b00c08440510080101c1c6072203c0c1d25020101c43c010169000304003c004030040d4840c1c540b41c2c03550b680e0079403c903100314112a03104101801542050940c1412903110310591782004e40681d41800e0004a0b0540450034070a0170b840c05030911038118420804030342442e500030340841064016190b03030465522000d485030240800300140e48101e50300701d14210340b640d00107610b03806150122912032610841c4500020020b0140340c0c1300d4a8111030380c0714840c00c0c010403904965407103141409035803108100c3c00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 514427239 1250 514425989 514425991
    0x40212010c08010b2515140103113a03080603030f0f0c01110d0c08010b09060a0f05040b18120d1b06091e1203020301061b02060d0e0d020f0c01090e 65
    0x804c048158142d120304070000ca4503001c070540c006c070159402d038451001b80740700312100d11025003141c0609a00400c00328125100700110004180d80c40e0304100300c030b112400d5203c4501018001e040c2c82241041c0f944000424495060394071a1300c608815403200070400d966401022160702210700100411403043c1c00400c081c15503c000703607001140e52520740554180ca6009003910140d800d80d00c2c04500040740e400758600b40100a4102460326200000c00840c3c5140b00d0031034003d0034017101e8218071800d28030520844005101c1d9814541e00d910303a94464003486030f40d03030b4542845114507010410f2100c0000c110b038540f040c9151100c4a0b00c0d515070f140d521880d0f010f50b5050319207980c0c42284401003201150240f041c10a01419051038002924008401d040c10200d070b14109403040c40103000c0030380c201484104040824414200108007071000801e284a503c18071403080c0e051034030003c5100c034000707034a090103134540e02960f20307090300880e5545e5603901c852659030026110103001c11942d04c402e2112 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 514428489 1250 514427239 514427257
    0xd021e030d0f0807050909040f020307080d0507020307051005121b070c0501080a0b03121b071520100b03010e01050f1f051003051f0e040212010c08010b 67
    0x280129a40006401d2850a031004408950054108030350294480761841d4001e201e0f007400d60800b0007030804143c010030014170007030480b0081000041903650402c0340034001c0462204440011312074040c01050741c0c03c000802c0780284031f1120003080178a404140100140b04954a060811034024246c000780103014102e000f04c400120f84614603452110010101540a0030000700510b00d000001824203000420300007020f40380c5000d8060665001c21810b00c1c1600d42000c0549a044000c00728a104010300b0303100c1c415214410b800922980348000d24600c84c0405c0e01d03000304c0c0303020101e46641c0407200040001c07181e030440e034000d01c103c0710290320180031514050000508000740c11442d5003144d000b61001191400303d802004012050342d2500303419188440140b803840340c0361101007910400d54030381c12002c2c9a22003001441e406c182061140c0943c031074003035101c0540d64516502d0210f031411756040c0d0207144d1f4503030b482d00300340030500480c0940c40642c0d692141e240c0c070300100890740360041416 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 514429739 1250 514428489 514428529
    0xc040c09030c0e010f090506151e190305090d02060103020d082106130b06190513030309050907030c0e010c05071d010f080a0222060302100804110108060d02 69
    0x3001080c004422200600b030a4a42000a13505000712001284040d91000aa0300c0c18201000a035481c1c035070710b484280000d422039030b441d40008010100f000002c101c0c032822801001c20f4404094513020b85400c2801e42a4404002c0c4ad11b65420490b02c400c1c0303002d105030142c1e102900400042c10920340c1251045e0091345007a041070312481e04c010164400640d120b622401c05420700041345800e20750720114030740c0741008000100c56440490600d0103a9080301805000b200001107260740140c08881c01707a21090048040f540d100c1c500038201c1c105a0188602503400c1d0800500710602034410001210300607100c500c0802004401100c020744804030880c0c09010f0741100003482c00d60040101d26a00c10000356000030341c10f0040b40310b0050f815a02825a03540149a100c0c0540c076140310011940c0035000c121141814010344100c00b8001c1540300a42288103600c11507489030b40038801c24004c610840d2604100307180703000115051042030741c0e00ba078081c1c40901d1200040c54150061411007d00c101 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 514430989 1250 514429739 514429757
    0x90f0204150e150f0d500615040b0a0807090f0306050405160f05150a05090d1a0f1906080c1201140408071b0803030109020a0c0f0c08010c0503090c040c 67
    0x7486420348a0384c203107203d81e1800a14035a4818140c69241c4104080100000d15020507449041e06d00c094401c0c540d030325244968004115141c45210a81c2034800303410350f01c02d0b41c131a540d9500103c0750b8041c5c9410301c005440d202c00301c0c480314450001901180d14000d52100305500399107501009100180048680e407003142408820f50f0308804561004001041e2144071141c03502051200380601d00c928040213480400803441055000416101d1910080d0344a9000311120b1410300c0d400100c0d0001c50790901c00d80010008142c01d150410b07481074070a000f24218100c0e02c0740120064400c0d81c005e03294130390002a01c009082c10524213075140d00201c14000300e0f24072100142c0e003150300da00ba64140d1b581c240004900d0103204500701d401c0029200c003140130040501d82070b152610f078003040c02003140c040c0c1c00103100104a48915403840d0110340055000703026030030618040010104921400da02542030088801e41d96000301d003541e01c0b901d0070001801c83c1c40f0074a01004000c24906041c0806d00c80914 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 514432239 1250 514430989 514431007
    0xe0c040501032408010606020d05091e03030f03040501061502030705060c0a090b030108100507020f071a072001020f0c0d0b0a090c090b0102100c1710090f0204150e150f 74
    0xd4100004c10ba6000002502c9050580090a004100d0f09050070700c002001040d2003038440e24584821140014000c00c458400740c00000d0442c8103004020813403001c040240001d00106500c2401101d00c48030414450844ca141e040c0c0c1c490041c1c68002e025070b0808000070301e8030f011560052860800700d2511a4075207403104c00018194000381c00030789440c3d10589010b032582c44c1622640717410241c5ca000403d165881011080e9030384190f8000e0741c0c0d103403144409002c00c4201e42030690311200c0d44441a1149505508810001040341500c0140180f1a65a92403800800426400a104c0029082d114080c410b83c851070b815404c040e00c10841d42d0364506420003c501003c120001414124201240d407140c242c2c002454204606001d9410910300000c00c0755254201c5400d42d03154469200100403a501d15420100c640b005e90700c070a000c282818079400200f95150b00620076a082000d200701050345200084800c00c4003011102d401000300604007010a0f117000c094510b444003048038601e40f035056 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 514433489 1250 514432239 514432301
    0x9091c0509180906010e090d0302070533180c010503061302070803040c0b091e0a030501051003020a140f130b031b0306070c11010f031103040f0c0e0c04050103 70
    0x800c031003036074440d840c405100f07407510305205241c01424610140c07070113428081611a11900030708410003d05900161580420409020351080800780ca01144441d2070784002000325030102a40280307412010100198410b00210400e88100070b00d00c0003000d501e01040c005540551000d010340d0380c8040111544284103000e40010881544156400d035202d05081c504055400000d400c1101d000c4810300024146032280f2580c580521681c6900555420006010a07554291600040c210b0750038002000106082283e000080300d20036038940c041c140c0e44200c41c081d00e1182c10710465021160710306c40b00c11481c1c0340b41c21030895081c40000150742c54841d03001a10300200000317002040010381460f00310600d4248580d5a00c1f0103d8105042241601d44d500508800c2c0c0c07548560501408071070562001e40b1035800304055080382c00c03140e0368034201030030003a4010b40385400841c0c04520204001c40c100c000d08030083d0056501d44400c605140c105401940036003402240100030010500781c0c101d41d4898 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 514434739 1250 514433489 514433509
    0xc09080607020106170a0b0402041a090106050a0e0a0515030415020d050a0f0912030e0708010908190207080601050d062405010225090506060403230c09091c0509 71
    0x65000003910a107800017100e100c0801c6694071926030030224124003ca010038039910303807050703044030001040c2810504201842d046101995008501c1c000003044c015040380042418150035103c0b13021001141c2c2c208103c8a03c9400b690340c01a880c1510b5890020180c4043d540040c803400d60a000050700c419100100d0300010741f40201c0d40d48490a100d0000c2c11341c86000404c00e9492018441100140c45100800203010860410180e560b0450200e800080c0700010151000000902128480e8140942c040d0001c40b900261104003500342061a4000100c4008441188010302201d82c41e240400c103010100f50b034240e03007458840780382c41030105503d4081080c003030029812049640c02e0000091500686142142071040c080c2d69003101100c24031400c4040b030745200000f0070b50741e448a01050f0240a907505c010303d0715180020859044842d240d6821800c51904229948800000e00b0451a02d01c1030361003803500d0304540101c4d1070710290040942100c03030b407a007080c3e898543e000c004200700c240 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 514435989 1250 514434739 514434751
    0x7120207090f11070f14151609060e010c06021902011a0f030a11271e01050f041503062d05010b030c07050703020303030a4a0c060403110f090c0a030c090806 69
    0x406c80040202c01400042382095002c69480c240d041c0e1070924a025101000c40d0b5401414020203914001c10040360f0f03012510000301d104407040c00e20043c00b00280c081c1801184241c104034608401540d981821401c096006400400070007520800d9101c42c4581da4048200700c1d00021040074203585118807400b2104002210140c8100904c1c180b04940884414440440d1004841e0790041000744d83e4404004451041203400046014465510407102907407a88010308090078410148030804407031543d10103201d10607042c140002007555620045800900951501c01c1090021405525402000d042110301c42c00071250b49549030b4002919540040b1408220561503481d0111004411000035140041407515000012001100030b580f800040442e00048013141c040d8402d142005c000c1509007000240c4420343d12a06c03804e02c5180c0501c0106031034043c1c0003152586125007072142800c0d20034a06120b002d42440005041200609010340240003000485180031990403800d01a00b40221 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 514437239 1250 514435989 514436023
    0x1211030a0807260121050d030603150b0108220c0801020a020d020f03030f1015171e0a180614090f0604030503190207120207090f11070f14 61
    0x102d8081c00007007850030303008400804110781c648003900340d00c2041082c6055402c0c0724180064109403801d00c440e00c45021202406030320410244104241c0c05910903003c2d00e0183d40524040a03001070854199000c1e01c100500060000f400514072090281c0200244402c40b09030010360541520f503d050100c0c2c0b90010001c90754009400d10300b50340c040203d03175111705071800a0441c04c20908481d40e200e0100401c00001800c0034000200a0180480c2c47c0c80640300d880c0455400c0510400c8c01400c0754060b02c40524400c21a4010441545008480581c1855401c00c4081c55545100703401d0f01400116602d103501c5942c048068000030428018203641543d82e000c0c1002c0780c0b40c0629001d14005013102d040700d03182c0101c418000400d51040031a644805c0b011041c05000400e142c1c400c1c028440c0d03040140402c1c000b500c15840c1d8030760101d0a00103d4007884000e200070120080a401211101448100d40700c008004440004d85c102c628200841d019084408a061100c0116400c6c0459a0402c911107 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 514438489 1250 514437239 514437241
    0xc010807020615060c15010f091509020a0201140403050307030606050316030b0118030f0c120b0f040f020d03080f0a0c0c1124120a050402092419050301050a0207020105071211030a08 80
    0x2034007003403503560300418a07271100f40881d40320074159451071840f0340182c000103600014800d04140c003d4212116642180d50140602e24007428000c2640e003081e82c0041c0000d013000c500285140c402d80c03c1c0c0740036405101d042d50726a203c81c007054000708801a28a414064000e01d48040d03000903d8608000794083c170306403440c5e4111441c2c1030341140056003140103045040c2c409103000c82d4030003101e242d00410100303004603580c940c1d0401e20140902040020760044110b80c81341c00b019407294000e070040c010003140700215241e2840820a0f00d01d541c0c0441c00203400324540d01c02141d41040f858202c2000a48000d080e641070304038400b02e110000240020380c48000031405501b0b000d50740340541c081240c1404100c04d04040d40040c400c080050881d2007161684c01e042c0400c8040c100120030344400c0200894440c84e40c08014281040692060502c0395207000c0014048140c80e0003122900ca50580d50507203001007507555604200c40300410704003009081000100100c13030400013050107520b15100c000f51 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 514439739 1250 514438489 514438499
    0x1060e01060813050d0c060b03210f0423010f03091214041a04170a0f230115050a1403101d0109030207090b040e0a030e0607150e0c010807020615060c1501 68
    0x188c0c3e02d1707281e1090081d4800482801079078982c40b40d40c2007884411089a83e692443c518182d40c50040d6000b1401c02c00050541d644ea0b11700302607041a070200281c0701d5904101c152a025401c8030860b401c0a820b04010b2103001010500c2603280710030440c1240174040c1003540302c04080c0c58441440c071094401c801e00041c28881407080f8081c00b00052107920050034607107a00d42d25a070480c40400001010884036900c2e901503003069500382d40c25490103100800c050f4100c1130401c40c408409100320f50241885e00303004241c0740a001104403c0b044081c000b014511111910f800051904504681d038030035041040c1402100203000b070444240c00b0358010070045e414403136100200c070100100c492150340344c030402130b00c0c0b00400b090383c3d02c906d505420b1204603c00c0e0400411414070650710010b2502d1110000d4220a410b241e000325402c000c0d24bc00c07122990041d10043d01d48800c183c900c41701690103200064140707041c05500224a0ba0b0250519080051611500380b600b00c480300c0707030300c00429081d00602c5 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 514440989 1250 514439739 514439741
    0x8030a09170702120715120f2301080f060c090f030a062715090602090d0813120b0112020d060c11100b0612060402130605190201060e01060813050d0c06 67
    0x10050140300c06460311780d103046034550f2005042070b5071301d0a000128054540c0e602e0143d02080c40400c00410510a0142400034840c2c0d40500d20f01585410f628080049440c0000240200101c0345040c02080244c44d0144008034582225601551001d110084044151028890070004900c550b00114a1070724102c19140882001c100394199150320681020124070600070344c101d01e802d81900002d441c2011b050100191181c00d0400750004050151a010040e2a0008201c00300d03080c4a0001c030b0319103890651440210b8120003030324696004c001400360706481206940d02c81d10040c60031082049640c1d0350b02c103031384907801d404012079203080141451120a00c00d6900b0502844402c00654513040d0000d480ca000f840d5000d803003001e1000001b00d05448960440d0010b500b003100180c9115990240203000d40c0c89031907031428400d01d01c00c0c400c2205005001c7c0c070301a190340080c82015a03007001802c649000000b0440c100325094640e0480114100740b1610315014510368440003a0343c92414184 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 514442239 1250 514440989 514441009
    0x90427030801090c0903060e150106050405030606190b03073015030b0a1109060d020c070b120a0b030307060c1808060f010603111213060f050601080408030a09170702 73
    0xd40c03451300307141d9010651640f000d10681035a034011400254004040002860995000c1c401e41c082c1c184140049029600003000e00101c50b0b0440840e586a0388032801c0c030000c40c5586c0c8030540d80c42c1d620301080c030981803144051941f02e4103c1c0ba054540c811a2401e05243d030380700a03640d1844080a08030858800d031103000d031910030030585105603030381480c654840103c9000100f0b051141640d071503809188404038021210081d40041030f142d151020b00070040020b601c0310040344150301c00c241002510702400025500505e0f52b802d41c100142e600c0e040c41001810302c0010881d89404100007040008415102e540042401d070366950001d2150f0106120460342140c104a0340c0c0c0e40a07400700151003c0790b0070400c0c19540540b8001c42da0a10034644000b82c1e0045c0e400c2d003814103403840100050501e060034420301c0035004110911106200714840e0301100ca041e5480c1d17000030355003c00640443e009500640d006180440002900c0400e0340325040d8a11400c5510911010005103200552034108000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 514443489 1250 514442239 514442249
    0xa0302150c0115091805060c1e120a0b2b020d0f0c320f0114030f220f030806060405030109060603060506010908150601020a0b011202010f080c0f090427030801 70
    0x43c02c03c0d03c0660300c40b00d9947e80010601e000c0f41c2000140c2005500da4841d0141e0643c02520409032501841c240c1014041d0046811062084c50030303c0c00303009031a00381d086503101d06151034400e4440c00800b600600020065000780d80207550f00e092040001e900350f45056605001e9a5108885410322030590781c485841c130b0721a40c8032440c4c0c40c503900310840442180380c4c005404841c4442c80c01480300040e01c0e1440142540e9040380f801101300a000310715490003607c030b1041d030902c135450710080c00204100d02d102075030081d000c4064074100d40006400ba41e21150050002440e407410542d403000013a0a4902d5500200c580f5601d8640c00c02c1000910f000e0745404c90400d0915074440c2e802c00f0420b56551a680030b06a20541203030010840c580d0003804940d42c602e030411201c600a40c0c40d031441e098010030500d0120700203003008002e20800c0e44600b01c030324081c40c0030a241c0c1d440d004498031903080d00c1d0400195150301941d1551011020f22240c08038442d800421200d01c00100c00c94207020707140342c40503440 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 514444739 1250 514443489 514443521
    0x1b06020a0f1809050411040513030201180309030b0727080606090105101407020a03060b03060714031611060115090e010e060112180b060a0609050a0302150c011509 72
    0x30190400120020b040b0640d007400100046660742c600740a060205005010f0b03400c94907000503c50900140600c040391203010760000c1c401d409000700f605481c904101c1d000740028500060901c0080d520384600c0c0d41200051801705030401e041002100380d40f0040e1131f1890740030902c00e0200300404d002d014056100c401111201e0280d0300d4003020506184045c417503072b4200050481564508100c4c413082d905516005800342c00181c0d00c900d050002810f404007072520a105200000c0c90f240e2054508c195022004a8000c2c21606e4a40341d611040110400c00d00c103000c054594842c01004c1041054020f1100ba0524292040342d01809810381800383c10130420003000ca001800500b00807050250000800c1c40c3c0740704502003d05188006002100c180d032840c5142201000604c0001001680911030482e02600b1081c0d5070b1400b0b4030322110070f00c901e54010900f80010130261600c00d0000c10002d010410140c6001e00c040c3d0403908440c03554190100251034500188110300c158415603150801c2060 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 514445989 1250 514444739 514444757
    0xd0905010203130e0408041707090e010b0d02100e0402070c060e0a0803180a08030705060a0b03071a07050f1e010b04050c121504020c031b0607050d0c1b06020a0f 71
    0xf450700d03049402400b0384200c0b214600d0210301040034400464004050400c0401c00700324403503581c4e6440f82c0c018071403a1625414103da415400c0418424400842c60042950440c1d060701da0030700004080030300c4600c06000070719802187c05d444500041c051f00d840b40380d840c1401c2c1c2c20602701410b03a1100241c00d901520840000b07009a150000449a02400300741d03c1320003000c00007001520400c1c0d42e4200ca0101c0c04049186000c00070000303211400780d90428003d0003041c1c00a02419625001ca12070005014049150000703000d19407002005502c2c041c600b5200744c401c082c0413252402c0c07994018480013082c0d42030b0340c1201c3c41080c42048110801140c3c01c2c4114101040058524003c2c1c0c2481d00a07414a480420b4101c41148598509210064415910703170810300203403505c81e00a00c04030603111400880240346260301050342c0c0e20455403038444d036007480e007603c454600510540419030f00780038026241000c4680d40351141003800d0303c40c4030f0250f42c0743e040c21001041300103845035010501500c61 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 514447239 1250 514445989 514446007
    0xf0c03050a0e0327150a020f0706050f0906180405071e0518040506040915090605060d0203070b1b19052109010c0f0f0c0503150402090c0a02010e0f0d0905010203 71
    0x40000054404502409111240c02e180020b9401c0c5c00e1040386800d82d1800509542019004104101e00210341015900a03540c2c42500342c6540c820307680d9403440302004120340c0d07400d49014400340c000f20000c2d211006542c8004008101122801d0b00c0d82c1002c01d2942da9200d811180e503503100c100510f164a0068106179094040714144001c250000d03124030745410016865454a0f4413891000380c00054013017003038400c0c0c0c034440000c0000030010f95030181001d00140c0142002c0c050081140da01400401d4410700d40b0814010541101ca107950f034010076072071000c0007514100700b002400788207a1150030309031600c0e18080d40f520006003028104120002e03403601c2202501c0c03003a07550b25502800d20355a100402d207000d104102031110003c2040100300796110621030714100721740595406804072803640c019003016102c404401c4400950210941001554071043c0d28058041882540004921045110344050801c0010b4001d03120a03408901c00810300c0f0b50005054000b4a400e0000e1450540c00d4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 514448489 1250 514447239 514447267
    0x8031204020103050414060106030e0c0a0510050f040905041101030b010c110f0607060f02070c080610060302070606081f051f0302100e062b050f0f09010f0c03050a0e03 74
    0x5001905040d035460010382849086c401301000e20030400181c1d10780e0760319000c01400070540707240d0940917407241f102d4a07401414103000711010b5a00007030800030b01c0c00109000700c0781d960040b001c8042551041c040000c09071074900a013401207100b1071603c01a641468001412100e004280724100303c026107052001c0760410480081202c8240e451078003c480f000d002c41c0f0fa91103514401881c4d01d01c0e2649000314580d246d03028091203840342d511650300d1982c45800c5a500c2c2c805454483c2c0010074030b501042018001d500400400381301e0038001c201ea81d590540c00c2e04043d0944c0c0e50005205041b00b44d00ca01c000c0764410542d1000080442185800750204000b4500d410b0b400300034011782c6901c1400c80458011039086060940080002e03969040d81e1900240300b0008500b03000300a100402105202c01c0e540c0501d500c651080300301c4840302e0781e0380020160800805010903101e95a1a2007450024a141c021a0303400b0105843c0881c280c14028004000c48208030360a200340c0d041489510006814 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 514449739 1250 514448489 514448491
    0x70903020913080f070c15020f0316020a150f11030a0906050906130f08151b090a0b0f090a0807120308090f0303011d060301091509030207030c120b01080312 69
    0x5031030450415100549082d0340c15118041c440300180c0c134003090b400100040d40e0b40203000c3e500220250304a504140c2c400740c0c0c0c0d401044c001aa00c9400a02c055203441003400b89805c103050004141217131465690f400d0505842e03840240f00000381c10044040c1500d900402c0c140414000300b0010351801100050003050600d9a001c1e0b42c0c204000010048843c1d0f031560244d403000100040c1c5820150760351003142842c4180342c401c0b85990300888000c00202214035540500c69401d01011f81c40c410020048442c0580c003a1881c03076072003440703000c1c042138007442d01010b44a00c0c80c3c0f10242aa0310f40e03000b010401c00c090540c3c8141284d910801007401445810000201d400350b041c100007080d0344a0000e100c2c2070041907420540e0074840072000080303202e0200414100c4950742d40901009450309424142030703982030301700504601104414646040300036407001b16030328000c0c810b8480b6981c03a030b035400000c10702580c80074070109140001c40702403190f003183c0e041c014450000250b291400c0380d0250003046038 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 514450989 1250 514449739 514449751
    0x10f05030f0a0c0b0a210b10020705030a0f0602070c1707050d080f1308010e160503010b0d0201182d050915060d1d060f061002030d0509010b15030108060709030209 72
    0x8040762064101340142140103c04411b00302040c0f400341115000002002a07803000751003503d070340035101d05180c0041441030941d1070140182010302c6080e101d031403002c450b008044a04075400c0241e40041040484030401600a0b001d103034900c0f90859090701c3c03a003d42c0f500703d9403145408620ba00d0005065008a81521461810090b103038100e088103c114495076902c19000b035402c2000003902d40d9004181c45041c181851941001c5030303101c100b45422034803114035050300506003175280300156000b25440c60f1040401000c651945c0d456007038807640301e440104402e80c4002819483c41105100b403810801611040e110020305e480d00004454038080d881348424007a000004000245e038110785c104104181203601c05c1c28955961000b1181d45070001c491140d08207070180046586450510005801d10796290700650030301a0507540c0f100100800f40c1802d9044d9a2966444c0440e00c89104512034400c0040f4165220740c580b40e800e03810710304014600d80402c404200144016035130042c400360440 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 514452239 1250 514450989 514451009
    0xb0405040504020402040f140a171902062101090c02160303031107020a0311041d0d08060301061502160e04020105071401090606081f0e0c010f02030d05010f05030f0a0c 74
    0x10b115400030800030300c5182c000d41d01c6619800000708010003111a120708c0180d0aa8208070402d60780c1d100b850010b5a041d2010716280c01c001c50000201020f0a0701e4200039000130300030791610745030f0702d9048a03205000307800100140300100100040c102910804640600c240040c20011191a05250340c80f10207000007018140d0f03402141c4020510103050311105070b4003905050541d40c41e41006454541d810721807030310a41c03c10040c2c13501c6481c000e0f107005ca034807040b80050544094801d016102007200800c0244c00d0341d40c034440090050082c82c00702e03103510319540103000340d803503015032200c80746e030842e08100c6800069009100050741d016045418160b040480342038a04d610902d00d13400340a082e031004c4d0400381400320225590001007244a064101c1c3c02900001d0380702803402000750751401081b0805508881d0382c1c5859540500002c0030008070b680f0580c1e103801e00c540128011160280c016903800c40e521007080c0010305003040b103022a00b4246e03009000550143c7c0c2c640c0794188550013241000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 514453489 1250 514452239 514452241
    0x1090303140c030a03060821041406090405010b0901080a0e0d080a1404051f05190c020f0a08090906010c0c0b09060918041a0f13030c1220070b04050405 67
    0x44482101907495800a41058076a100f44c0c00340004c0140c00b650203440741d180920b039003614401040000e01c607207081c00b040310181042c6c070704900c1d00c4141100d50b0382c46400180401420016981d144561406040a03014594807400c082000600c0c4650040c000c0302c00714036240300c1304100400015640309544041c03900c680559544242800507041b0340941c404200b03404800d0108001000c1801c400703a4000c00c244590701d40b11940340c0d0045d28801d031626000702d01c0c1041c2100000c0406d0b0400c0c403001c002401100c0800002804851414690403003d852040d030110f210003062500116603a0401d00902c0e00d00b00041e040c0d290846020824403030b070000410001a502c4c42a04e0f110241d91080300c00070a40030454400d0802d1220080c821101100e004440c081001034941002c030302c4501800c1e2092900d00c20ba55000050201032110f0441030b024000d5064507100010010a00c10307040740481d56603031700d0417440d508050407405500c580740c0046412244090100c0c0440c2c1c01500d041b100110341c0411a = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 514454739 1250 514453489 514453517
    0x10f051b030103020f040e06070f021b01050304151b1e0e030c041a0310020c0c04050702120703140304110a0834050409052b0905040b0a1e060e03030901090303 70
    0x10722118100e01a08d0044004100ea03858110000d02c18a0b0110303020303128200d4503440052003240403441c01074007044091011038007003030040491121044a0480028029030218004404102c0b02003442000131601c200b40071021003501101d1200041e281420540f6010140009445802a49403113005690302c0702041004c0d50003609101c5c440d1405010307070b8010098281040c02035403110b0f500c05807511500442104a0605219242c0715541030b50103045c02e00f904030900310075907002ca1001d404006108416010305006070f4000d50040748542020b0038041c0003041031040005255200d19601d41281840d8a8500346840c65a02d03500011300b00f2008404400c00205180f8015401c0740d81c00900c1c040c044400c01400040f801080c4032342c4502a4034a40e143e1a40ea412012180101e400240103004204201e082035000300c103c680006254030303461500e40700300c0802c038061040c48054a002280d0100801a0040c01410103c3c00980246d03182000e11800608a10200d02c801020010104c00c1242 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 514455989 1250 514454739 514454741
    0xa0f0608040203120a0e0901140109030b0702030c1b040c0201090804090c211410030503120c070212030a090f0e070e120303040302152805100b0309010f051b030103020f04 75
    0x42141c01300030aa41d02c8146a0030010301c5413040b2031140d802280e51100115000c11444425912860140c1d505030390f150840d5200010080050100c6c070035444103000b00340d00c91105016641900c6000741a40760301c400400100015500244206c4003075901d444c1d41c3c6004503580030101d07015206044030108941035101003c0742d00301e25102080f20980010307840261182800e4201e420740030420502c03180c1d20b45680b0310b55003040c01c5034070004103658002c000200c141c202104103190300c802c0a8648904005c0c4e25000f20b005268852820885900001845100d1a400c00d0032140a00b0060301b0f00c0d04800e0429035034200c0c0da43d000d0b1201e42400110109140f040d81c4050215806a15001c01c1d261070703040c1890040e6890401400d01c9601000e0000001c00501109880d0f0840c4050b0390a0300b40f514a03410640300041c000500103180d0010541400b0800a0302c250003140601c1d0510000103e04210140c0c06045900c0940f84034805003081a101c002521081c00781e0b41500e4040303507526801c070030910000d8 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 514457239 1250 514455989 514456003
    0x21091e080105100801050f0c07020d061409070e01060c020d0602030c07021e0901050103020a120509030c0729160308070302040f060e01020c0102060610050318011e0b0a0f0608040203 80
    0x2a8156003440b042020088040301403a084420210090002e0b845011192210407412603416000200520141c0302520b8400703644219540100b00c0050014000d00381c00744038184c22155081c5070740c008a010040701c0003680342d2900518061800311400c21150f800034003000315000000d400d41d6000b101040d071543d044000c0358032041d070040400c1c0a5100554400886a500c40a2144144981000012554068021524101160303540e02c503e001d20000000010400642050020300c4240400070300d8000c2000180082c1c0302d80c03520380d40040303008080a0741800286014a5001809001e8400105040301c8270454003035050800002d00e83e94017100310000d00480d88001d00d103280d10315000a013107800c40c0c0500c05a40007a801e07680c91000c000d006903915070302550783c240c102075000d400c0c504192280d80036580000c1c0310200640ba05100c80405401d550914030480788400d2140c01203e8141c445110300003482d0800e07905000098a0800c3c00304210b0082d200c1d02d01071080c00000202155814042e40d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 514458489 1250 514457239 514457249
    0x5030d0204030f0c0f05061b0109080307031517030703050a021207030c02011701030c0b07080903010207060b0a08012003070201090b10060912050a030509061b0a21091e 74
    0x841d1541d03035a0808040158140b5019182000441e0001c525500e0340c2d2071131015103a000d0b00c901d00d841d100318429012500b01e0143c0d5103240d50b03140c0d40c035400a042440118003551240d600400d54042c44d48a03100c5070701a503840141843c000c447c251224050110a03a812240c05050550303d4031010074060742000e2402c03041c4c41c1d401000140c2c000c1055080703154008828000e90b45c806e0305c40784004900304108030a000241c1821aa04000c22141020500034180c1394803403840182000315400201c0e09980098204aa06036212290707001c2c0c41c00c8c1055104010840200248005040b101c101803040b890001c002003035032070000000d074426000f50014000c00354089200304041c03402004030400f030461805600001084020002024000d0b41004548240c000020b00030301c03000f42c0c0e4240e070aa440f0400d120340040c0c0c148000c188401000f40f4014490144001502c607a295500e400c41c49200c981900c8110561102c1c140c5040e10b80c468086001d0351684c5c05d48100030302c0c94030044d00d204a150b9100c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 514459739 1250 514458489 514458491
    0x61a0318060903040f05010503060a0b0d110d0914060c070b04030c0f060605030d0c05031204031e0306090510150e130e010e0d090503060a0f09140d08070f0f030905030d 74
    0x5012103502d001004004071034000c0401c141c080d40710001114144000e03160b240d40084124414002c008690005045403c0d110200190741484080540c1c1d050f0403040004d004641c5d164510300c280141c1d407025000c1200301c000601458540a101c0c0c00c600d0281c0c41c405000940700000140030135008140b0810310a0300a546580341180034034042c0041c0401d801803d0281c0580c41c0c1800441e40601a010841030784038010314102025480e15419084000b40b0540c20050b042400d0000206941d08800c9010525900416401d0900011409a54010f40340811400340154101301d01c130107040320000382c16514035117403d12002d00e900048102c10070100d0b00068611704140c2020050701584000c0b160341201040d0b6881c05404001a5203000c400e11525070540c1004001801090b02d035481415101c00c040030015022115441d41650304000c240500703000d40c0481100c2d000030740c00c07911041d40b0004602d4061305100d00040000c00c0040a1a00c900625484105074010002d0600c265406480c104038 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 514460989 1250 514459739 514459741
    0x3030c0f090f040f02070c0b03010f09240e0a1a090601030903031407020c0906030a080a08091015050111010501081b04091221020f0a0f051608030109060801061a031806 74
    0xb00d030700096121401c122401f40881d0f40c0040d001c01c0c50000da07412100142c401e2020986000f40c200040d00356249071840c20b00303580750301d003010000c00030384000900700c401160041c503d030031075010084a55001802c280e60007484001002070340c0b034500080d413001c03081ca00403e40349124a0280d002d002e401c541c1800741c000c103000f080a01e55002845007200b01007290314481a45427030080c56141c41d4884c10240200d001084408130460040e02101d80129003201281c03144240b2242003c200d50b00c111200201440e0310394100003560740701d5060142081c010b4001c200d50b51610407135550340d142e100c441c2c0380d001e0b0111100449981e0303141e0040c6002500401240246100200014456510529070340549240c0e85060031642c6450b1003540d400c24400b1104a250150081c01503912400786040501003007400c000f908050804460b24608407841081003580301d504143c0030500b40e0307040d50030a90700d82c1e150140c1000601203001501e985e002500180950b65120040c0304814450f40ca108281f06101c2e0070 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 514462239 1250 514460989 514461011
    0x3032c0f1305041b1a0403030813060203090c090c160b0a060320041503030813021516050705040b060d1a0307120c0f080d0f0e0d030e03010b010203030c0f090f04 71
    0x10002c151291301d408800000c030b900c40d050410020a00020282528410320003840024014100290408a0040d802d1304400c603a0742c4000503a4070449001140380c000c90344a150906082c4030740c507040703001940083e041c0031000b05a01380c0401c51000161030807100724045214502d0903444540996080b021602140100c1005c020030b402c81d601e03007180518500000005d0074014081000b0030f480e8169141c03c002e4032403101300780300c1810042c5e017030381e01002c4554510700c0c0c040e0000081100080d4400702c40b01203031071b50a025061850542c042d60084c0d040802ca0143c907515034048506441175800300058428a5904604030f468240c890305400d0321600b01c01090650742d00b030505080078400c0c80b9100d1619283d100740c04000415104041c41544404040c032503141c0540c44c4070050206034a8480c41d5951408005840c00804920a03400304080300b807030856504081c081c0d100d9240302030004502d5030901d414158030f03910a00a000285440110710f03160130340c3e03400c10088400d08d00140148000c1d8822 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 514463489 1250 514462239 514462253
    0x110c070b0306241e09090703090b060102030315060c010e010504050a0b060402160b090c1e04230601050f04050301050708160206042d17030103032c0f130504 69
    0x690b0300c248070b0000c4003110740594403043c241104151104000d0303070422040040c1040740d03201d0452841440c4509010041841d150a030300c462042d440303613802141c0200d15003400c100944000d070403e41190020000c100000d0030301003140681c100181d030519a20542d1124850040c03485002800403542443d00b400240980015400501c0e400340d103003181c00703456207402c100807841b5018890b00f031142d85440640205a80307110140c4e1142210040d0340544c004c4100280032424071711620384d0464003803925034056091922440403049008032032203690300f40b404819001400c00030107a90405c02c0000f103c00d08410300c00147c40050001400a0259062841e8040d210100c04c680c1000c101e0f038140c0c840f8861520000e8403d004903040554225030308081d000340188801d501a402240c28030020820000490760016416102d08004045480394150320340105041c441a042c41e824400c65220002c1900d207800c60280c00800c11185016005400c5020035401511104060740365881c04007000184900 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 514464739 1250 514463489 514463491
    0x31b12040f0e0c07121b05060c0a030c021501051207090c091503020306090601080603011e0c02010c090305070510110a0606060e010311040e04060b03030a030c0e06030903030a110c070b03 82
    0x1821010b0019900d40510721403d008000014000c48124404080900e01651145c400f070001480c07400c224041a4079034038609807003070f84d0680f401100099000d10881d4144150180103950b0700c00382445080003601d6a100000600906206007a654607401c081802041781030004c003018141441340d0714031000d02501c014841d01c0f0300c2d070400011170680345d042ea11078400c480c0716680044c00c02c3e03e0780d210b0300011111070500402550f0950350744c910020301125411080c06030710300c0c04440890010001c0710024251540620088244203103000b040c400240046403140070f5450035551103d8a007403083c0120342001c0c5c00340701080b01e030040d41c40d04014001070780c1002040d01c48035181da40e07105800764011422110468000c00e04201d00344014041c155005030b4850b041401030070701040301010400064203550001a252011035521800d24071003c0d0088010800c050048802c3c40c01d5140c014a0b4648a11000341039031002c075611048120f50603445020b0320140c00c000b6044410340d9888036404000307544 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 514465989 1250 514464739 514464749
    0x17070b0414100c0519051b01060f09090f0b040614130c0b09030a031103040306060b0c150c1c06080304060518090405030405130605090a2c031b12040f 66
    0x24000c2d961484012400743e0340901a090783c62510346540c21424501d8000180014003c000080111006041d03030000020312a020318000003822501c1c04203103030304410341c0760b101c84443e5040000c48004181c840a100d102660041000e60040ea110315110006158a00c087e90303408041400f4445949100070358a00c1e8203210300c2e100032055071151903021a6000360680182d040c0e0004001c000064802d0b00459481008901264185620f130340c0d03400240d42c0c854102103442080440c810b2036140c8104140302841000f40350108160030800244502171107039500c0300c603103c0b00c02d800c0c1a1a140c065032006008000c4e00090b00e0312183c031102e00600c1944003e0801f0301c1d403140c00c048000c1c1072400d003954a000c0d0380d0200086251518000034441143e075110601c0143c0b82ea40e040014050b150b88160350b100d541c140d5030000704043c03810000c0402540000018100c0c13007a0201130150441c000084403c0c0074480f00100880000425041d490300c0302044014408403408903000940301c1d8900324003c02c2e60 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 514467239 1250 514465989 514465993
    0x703090f12062a0507030203040b03010b0325021b0f1008150f032e0f091e0f0605090c12010504020a210305091201140108011503080717070b0414 64
    0x807070302012010010079201404079810620f006680180680c00070300702c084c86801a03a09090380d031384110300d468100341d100c00503170071300001000541c4469a0f1300e9409c0c04100d41c5c1e190120307511140004d40d01c65512044e60480d0300c510f0350140041d690002da084003140700505030706902840d104000d042c240c043d200700d101d02c070502d0715011031450f1580281000c1c21015005103407030402000c990703c8000415400002e00f450300a10300704250454000c001c06c251040002040a1100e854488001d0400c40004502064a12014000507100840128186810210200341d0f0780b0740700445411b00b034422480540c40000480350512024040d00003510460086810200301540d420090200d00c00d803402d00c0036010010140303080002c3c0900302a0003034180c05403032239542c103c000e001e00b403c40d11400c2c13000a18190342c00040108003001d000b010010101b0f4421010414035650b209003050142520040213211000100c48151402030103448039950080e855200d2400c10b03041c0400d0b00b412400215040c0c0c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 514468489 1250 514467239 514467251
    0xf020405030f1e010902281707180b09070c02060903070914071704060c0212280201110406110c18150d020f090405070506040f0e0610050703050703090f1206 69
    0x43e80c01882160009078018103010480503400c180b40050745d900303002d400f5450000d50404508942190310340d0b10792110000060100c141800501c2c0c10103601400b0303060301203090589500050b1118440c02c2c0c0c00031800d0510f001980b40520011711540590580c00d40c05101d02a00000c80040707036041b89075110040c1081c0d10380c0f904d0700201101c051840c03840c00924010a000420006042a40288a040c040744140c0704146142c143c0340c252584801d1500743c0b00140041200c04161103401d4143d8007403051300080200c100d440b06200120300943c4106020302072202c44801c040a41401110100807005101521005c503552100108200544080c0100840300c039040354541040d04001101076001013441c05140002003c02c595040010412140350060341000284c42d2034210280019004212030303a1450f500781030380030b560600001c0966109095050b110030115070401c08035140e01c1c0e01444c1050781d950302d0f41829940100a41c0c8544120a40300b400040d4080e80c001c0b807510824400c20b028400 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 514469739 1250 514468489 514468543
    0x20d051b01030b090403020607080a02091003141008070b0f0c010203010f0e15010e040c1b05010e010b0108060a0605090a080307110406171c030e24011203050306040f020405030f 78
    0xb041c4c00c01c9a005025030300003404541d00754003c0c40c000d580519003001c0507103002140c0780422a404a515210000300b031315429814800080794065a50182c81078071720561003860514400d40e102c07000e114004042000180c007009090700758044546034400c400080d5030340e51f0f442136040c05c0154140305802c034401254010900d0114005800c1414400c140e4510b544100300d4010800103144510b03807007007846100d42d030440d10b001c50325200d50141801070000082001000483e1800d594208148030304100b140003c2094640d01c520b8040142c400c1441c00c19111480b1038046036800306960030183d91884082090b4080140d8041440ea100b0401d41d41480420740e5030001c0700501c1c900078170049446e00102880d210446019507040c0318901d8038900440c000c1da0f180700e100e04080c2060705d02c3c011580e11040622000f0f4030305c02c11030300505004642c2d68100c03070f40e91801020345c007000e031010303108039160781c10b40c5140400c0d80c042d1000b034400141950b01c1341004210306540c0309000c0207140c044031180b03074145030 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 514470989 1250 514469739 514469749
    0xf2703131e0812040902160f03120b0102031c0b0117190c0c0818061c0b030d02370206030a05070201200403060f06080f060702060a1a0d020d051b01030b 67
    0x81c1c60080f4035030307062506103d804006504090500380215458508100200c0e15180c60841c10b40e00075100c4880c14840c024030f2006a038424940c0c2e5055501c104030303401d0b9291104003840c40358408840c002030b96000c4d28004a0b50700343c01d00b502d10040c01c000e00912482d00307518140000d10149648040101c00000b00c0b0556940d0724025014012550038440d0102462110f460002c403804003d100c5d0f440d101015400f41c0d826074203510000c0c200780e135691042d22281030030080c5440001960004007a103040b03002e1030703003003495403e206078000700185c0402c1c805049404000031000c590052840c0c1e120f180c114510801010101c403000010741c206a0701c0c1c09800840b4802e030800c07101e0320300342c68034060841e00c40c070024051010100ea519a0345580019191071b051041154074442c0710060986402e00d4030f07009182040291003a01003074079194211118204d500e82e200c0c0000403e4410508d0305145000069100d440880090007600840305100d1012415000480030164262000c20184038901d046c0301d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 514472239 1250 514470989 514471003
    0x4030215160c0f060b060d02090a0f0b090d03021929191104120f1b150f020a0209090d0f02061608130f0f0b0f2703131e08 54
    0x1080b030000b180c41c0070903514648000c445000d0b410100d0f0080600f40800d050368040c0c92021403155001c19440c60301d1814000c0b4100400c101c0d10026030990401060306581c0c8180c1303210074401da0b4484010402c040c000c0c04420000300041050f0b0286407480c3c10003003c406130b82c0344c01c882d100c8206401150307610b00091215001b010742200c00c58a0b00040351003100182002c0448681454040c000042d00418122071a2040340c80380042c0b0b44041200c4c070785440703a04007018460300b200c1d000320400c0c0320b01c02424499403610320f218a402c00d0b00711001141a0304144807404040c3d0081e40d0401004050f034000229030f4460710550f80ca90030980501341040f07890b8001541d42140c2c0704100d044030b030851881a0500358000e070b9270403030ba00790017255540c0382d07501862819022603002a0454401c07060051030481554040c000103110100c500c1d250004d5035400c40c3d030034408500c0704d40340034000070b0018041042e109012510441301040545070208803409060f00c030414609098218004035000c80e000c126a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 514473489 1250 514472239 514472281
    0x7020105160e0f0901080d0206180d050d020409020c070f060c030c06050c0f0c070509070c0b0601121e0207120302070b0711031e03160516020618040504030215 70
    0x207109501c2800d00202c9220150018056210305020300641e1207076541e404190003011140f00428a960703503000d004c0e0618900514010300c6003c0300d680b450001502041d0f48480440c14942255180e0a450302c1400034001c981104403254404541c0c6003640383c00294507030648001c520202070181d91804110740790b5855180040001c3c42c0002c5610009600b90800e03034000c9001e0780d22904141d020025840c4c960403400c441c0c00540c0c0511800c2144e400c080301c0140d0004e00f640361030081000d02c0d888003a030000010301040d04004001ca040440c2245661103010300d0004211000154030100740d130103002e9004024140d0300d05911005241d282030081c070898180c2c41d0701c0380395250165030f00342094510440880701c081150008020380c0d00d0307042001c1c0100d88100c19600e4121f489041000c5808110b420219000341444003c0040c4461010203903842c8100c0d55046807541c3e9a000c0c0c11b00c5180c05502e0803801f6a420a0030002404205500490880b100d0501e60090451968174040c180760075010706900 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 514474739 1250 514473489 514473511
    0xd0f0327110603100b09041b02030406110601121b0302030319020c180609040609020303191205011404020906162907090311061b070815060a0501030b0d0c06031407020105 75
    0x41017008a1122000c1c0c002800e00420015450007959030050b101c1510802000060304000b8040c0551038002d24020003c050880042c8407640c1004a0310b6000c944540d409000090201c0425500800b0078001001a560180903aa15220000341c8407068583d24840c0318094047c0106164450910100021904011848400c2540c45600a000401c08003400c241c460545614014015840c10001400225900c484101318042031120090a1080010034886443d080c00300401080c81e01c0041c12500e40310031240160f540000030005044c07841003030442100030101c80b81d84000e20404008107000782c0101040701c8103910b6400011003070a503040303808401103002c5220610108901c41c03c10811020060b1009152001560503098000c20001c24409580d1000005210078001404001d00065800800d0070701070601c540020b01400d00c50054504143d501c1c51004030075551700d181180c8241d045040308040948a91004026002691b11100c6071136507440890202c034414032826202d03070b070400783e = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 514475989 1250 514474739 514474771
    0x4030201081308071209050904022b1406090c0a0b04060807050f1c0b180c0f2203020117151e120a060b0907020d0f0327110603 56
    0x1005407407400700909807540304030a100d0010005003200c0c00400c1518041c4080420301040c4010007414000540c1020b40140300000c24000180c95006520842c140441c106101d12180032290b100060100d5002400401d03050440e0040b10038041007042c0602421420348030609920300c140114294544998201504200400c00900784079024683d04a141403424030301c1c007000d030458440340e60045803804404080701c81c04415110254498400090019210034189894145009800300001018244400c1c800168000005003d00071a2012880b40241065020450803600c800c0d0741380b80004c0b404903080000070742c100940c421446103d41d202c015a0030501c040d202c18810303180f44400c0004000c00201014489603036454034076960b5640304100a103d42185030500d08140e03071140c13129a000e00c0303d00051040240e07010070f00d20000703581e60901c80403c5092100450052400099034a00111184a140105441d8200154455001d140c1c098010b001620800c1410f200c1a80c0351700349601103007 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 514477239 1250 514475989 514475993
    0x703090303050d06050d031e0318060b06160f150219030b0307030204050a0209010e0d0506011a070605010312020f15070f03020c070e01030b160e01110109050d0207081902060403 78
    0x2000300743c290341140011444503603420114a4140c00f4036000c40102300e040103c4034544803c20030902032103009240134004882034507801e0742502c507610400b4203056184d018581c00c60311040c0459601c0c030b04921451045130020704001c2c0000c00c0c031a008880b800701c50b40100701d0001d00b41c000d54500f8a1010315514010a030400290001d0107016800b80d0540a864800009640e807813150b64807078062101c01603500c0b032042e00010180800310220314428480b00c025803000c118009182d9044d111100d441c0f0030545200702e5402c60500400100920386410a000030003005400c0e4890044440355030200d07422414184501c680314003045000402c3c08650000007256144200c0c0c5428000f4020f0400600c0c040c0822401070400300309030015013011507400700400400c044200716650040400d0207101c5070621116005140341c03401171056040051145256903680340a40c8210082c6a114040340c004078100b10029450780868462030f6400d0140705943c0704485a004c0a40f512150300900c064079090942d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 514478489 1250 514477239 514477247
    0x12060103030815030d0c02180a0e010f0608060c0a14030c040501080c031e07051b0705010f0809030d020d0f140a0c020d020a02130204050a090605092d1504020f0904060b0703090303 79
    0x1b072102a41e01280b01501041c650000e0411240038510407003020030107140010780c0e6402c7d10450310301c9100c140e11b0802d00b0401e4401c0852840e800001034101d040d03844003404000c0b11031249485200114130300020074000510a500c0081c02211420303244c2d2062076641d4031651100e4007040364034000c40116a40c0c51191044401259035104140d4148181424146403441e9070428810640030001d5100300c105010395a00154400b45008161810002c50f14041e00c01c240c4078011800e0080c400c80d000f280c144240c0c400b6401401e1040e821407820403615130b8100c0c1c1030000306c070183d40410500b407404108186851001c40c1e0b000210361170350001d000d00c5c1c1c000c4d0f0a008826001d030012000040c0c2c28000420550381d248084d20050030034010104d0170905104c10000110405010b403801600b28041d1003403254900c01060114001c038012901c840d03035078941c0c60202c64550225969104d0f100003403402d01014040064548a44140c90402c84242c440c40060354034403504101038042900c5c0c1d2010070001c3e104e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 514479739 1250 514478489 514478507
    0xa020409170a080906010e0108030f0c1507020102030a1d0a15060302040c0809011104060e130b030712050f010b030a0b0a0b06070f120c11060c01020912060103030815030d 75
    0x114100903000d003030303a4003403400349a00605200c90014000f4000d000b64002c0420480d400352000c100307400a254500f603a8143d807841000442d400d01d41021800e02c4120380107002c0811585400702405078a0718100000038003d51040f9800344c403030b41c58a0100302c4d0b860f0f0985500612141502e004044600980d29201c451480e40301030242c01d02d80b5000088016295070060711680380003038484404508190007050300796102154000071100003444100102544000d035441d003c2010754110344001c1c81c804818010f000c010400c16090320514030005149180c20300400c0d94a4000c00079207003103a2078805418240c0f40e01940b0540e06501c40b6140c075000c203c41110180d000004079000203920024480851801c1d040700c0020380300e001c80b20b03111205002c5004141c8030480318a10b0442003641d2140d5905a1000308071040c1406583c000c04c100c00504800d40c111024100010081c00d181071041c0025075490b4024001180058040030102d0100c03020044aa001030f00018060a512015031a045034a058 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 514480989 1250 514479739 514479743
    0x210e0f011d0402120f0f0f010303050d1d0618011e0b0d060606030902040b01030c08011707050d110f0a0e0a0f06090e010c0f0215160e030f03030f0105010507050a020409 74
    0x200c20708007520240d85a2004100890f1800300c3c02c191803400c044906090702c80105010160b400c20010030610040f4081018103580e07140c00c0458440b004052258003d02c00200104c0a5070701400f800e40101d4000910140f059582100324903a400c45824031509030f07000e24207070807002d0b0041080b542c424041c2d07800c0b440509030040d080301d03603424541d00c030502656100e500002c0480d68a0329400e0541c180360140d200900b8007800c0500256035403420090200c40140700e1820b0f41246a000c0022026080c0a0326000f4840140307800f0784103055003400f0050750365030085103204241c08040e0403445d051100204086a500c1c002c00c035034a54a8100b9003019108440000480954840000c0740c00109807180c0c40c940c0341100000100d0341d20007003000d40403c0784090035200399404440c01802c0c0d24a28145603600014012040340c5103c0501d03010f540040c0f03900443c40e494000d020fa455104500000650310501d00070204014690341c50f4010340d128895004080e0903034011320b1401025042035046000f1142c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 514482239 1250 514480989 514481027
    0x61809061b03020406090e010e1305010615090f060801080304090216020a09020904050f061e0307030b01061101050c09100e15030a060503070b0325120603210e0f01 72
    0x740d1a20803104642051a0300800d0740030600348401544107500c040a401860f641703020035418121040302200004007552804650a1f0304c802c200b280039000140105180110346110b9600c46801030a0407005001e204911401e044002440352302c6406454101c0d4a5030b4003441c60681800018000796221031491080c20080c91022030042c0c40d004900d500030706a00c0e10041e221000c0800704402d440024025440d05c04082c1c080c0411595003002e01c1c03002141c851511a0f9125141000c20305003041a40054002c00b900c500020b405600181454801003989008000e282d86280b001c1250740610212140c0108140410302520390060b41c54420040d0020006180c20b05142d054103030550080b9540402c00340c880e0401c01c154142000700a000c4d04004050500350703e0300381002d15183d00d121000d00d142d0900c0c0c0740000c00c02401140040345144600405001468583c203058240920442002503044401d40700702800702e100c0c010000405200408070200e20301c4642c0110360501000b51841d9000c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 514483489 1250 514482239 514482251
    0x9095a160809011e06051c0b0705090310020d140907030503030c0c0c04051906080604020f040b0a0305030313020f01020c1302030a0216050a0605010614030412120216021306180906 79
    0x4511000700038109030711194800305046041109102090f28144a40c280d4039004407c504000303118409100e6004070315240c0507442d0910500064a4141c03090702110310b8920000300a071401d81140c101c01c038920035601d502640e80e100e05400561f0b0360114440500703607800920100354164600070007070280718040812200b4450407440020100d403815140201d0301030b01074800101412140c010180145845e4020300b0080c9450740204010307400c6004c80034070641d030b80d0129030030a540314600300c0042c5400c501165107038681071903182c080540145007a8400c244892110720030358030020318a20481e002904403d52030550205800c041d4001170200b400d4a502031201d44400c1648a080984690140004100b09c034280d0610300212038041e0802c4042100e91880c6641c0300c0201c40c1245e82095025403103003640c0e02c05000031102d00000c9542e05202c103000065242c50304080030703c0e01a0040c000c80740103c3d952042c4200000715407682c0700d2540303d1317200e602c1078030703884107043d030210480a02541c40403c1c6 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 514484739 1250 514483489 514483511
    0x1203160b070302220306050106050c061314060c0705010506060406050703120b0303280903121803061802040f020901090e06030a0b09060708070509095a16080901 71
    0x10314070803400c00a0118042103c03c05c00c0c000c0f00d00a950061480c0c0c2800d92411040c02c005545500c0020010a086200351100c2c0c02003008000311201c2104004003034414504218203102c034654024901074589600b800c02117a81c038038145088404558243d1143c51510340c80e69029100c0c8603850b408200c1301659142004101d440034001480031401c1c401403d02c044081c64100074840d0803081e00d40c0c04000c0c0c3d4400c2800000c81c2d0b50400c0444044c207040c43c49808120920091900445410081c026070501500d407044c3d10074a44004035540c804c0b01c06000081c100c400d0b0408034051141d03001d0001d4075081d010080303070000c821010b8004001030103540000c3c0c5a62240607441c502521240788641c003203401c20403590303403082901c0e420107a41c0ca04245892903c40c00204524409030020043c038500107103054034141051602c103100d40e00e043c400f100d90b00c0705440c2c0503060100400900d421903c2e000c626298102030f0303440684683d84a1558010666080b542111040f900a1010300740351358503640070b03031 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 514485989 1250 514484739 514484767
    0x1a0f1b07091806050f07021207110a060906022512020312030711061803030708090c030a0804050f0616060e12120601110a0506070509180a02091203160b070302 70
    0x3103103001002d41d4400b1200103282c542c04480008285d00101d2801006110700140c0c0071604010b1a8100074506071a81d109080410440d03807400819507100d070301054001050790b00403e03c541200c4042c3c09072900b06441e02069802c601445c694864044400441488548980071040307208600150803203028100f030004d5007503654425920500810307820342019000e801c0403c0300680c00401e01e020300c06205003004c01c180c0d80307010207805101030201030000100a003508000c0b900000b44014112244103e0b01d050080c034603405409024010000321101c0740c010b0600c50200d40e4040c03000301a81403824003545902c4000c2c00c1c01d0351030040718090000324900600400700644001c200354280e00080e0300f041d100160044108210007030098000f80e49a201040c3c011850740c0d07200b01303141012581d80d510791002944143c00c1d2995144400450340c28800729220315400707444580020b85140171102d04002e0030598078014010320715040d50280e5030000004444100f0540c004034a410054182581890080 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 514487239 1250 514485989 514486001
    0xc0e1201061d01051903120c060e0d090e06010f050702060310120b0108210a0c021906170714070f1a040308090d08010f050d0521041a0f1b0709 63
    0x1000761410302c801030200b864607100d00414050001c203020650b5140da03856940c0700c02d41c0c0200c1001d001c0c2c90380b542c0c0203202c840d41040004442041c260347c40000000005055a01c2d2401400348200c0000005080341d401820011500310560312200e0520302e0329030801040b03a100603c6800c002003144000900201c401c070080c801540700b8007240c06a507050074026881c0c0441b8000c07a00004c9440c00204003c1e00507a411240300d08414030b0300204c00401400411800305041400710030603000c80c000050f08580c420600d082c2050000140c62081d100c0c82d800321440c01d01d0001c1c90307011034400c11141c00050a41d08008140074850304448012100da6140c1d443d00d00000c4805401059845007008483c14080c04101d040c2c03a0281080012780d41040400041c02d1500d015146c0501e0070251014207200d03040100c0710f01e4007524141d120989803a40c110041c190401d228591080c0c60304c80000c8800302c0080d003600d800c0b100da02106800d00b040b4545007001058401c0100d940c3d406683e401140d0032103240541 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 514488489 1250 514487239 514487279
    0x9090c091b141804090303060e0907050306060d120537120528020c0304080109030f080c0a0813050601090b131808130e0f1008010c0e120106 62
    0x32040c1d403040e003031001e8401038031101d1501d40c00408000002e2008100030b855001000140c80c002002c02c490301d8107400401c2240c0004082d104400c0400440c594009100401d8030410b07429200207849101c140000c1c1845020000c026035228207001c65024400c01c040c0048520300072028690000f0030f5030714070f00400007107481943c08a03215500b0030065001510414100c001c4801045185031440b141101b01901102951b1180f01c1540034840030320080d016107900941040c1900d58445e80d98500038000c0107400c00440c00b1a019040c0d42e5800c6001d03011245c8201c00b01304000746010318014089a140100800100144000090300e80c0440c40c1009000e0191003203040001e103200c075540400c0491400c01e1050613009081c00880c030b00f03011102c08040100c640c84a070190300c13a818010440c18022a5400140820500104200080c4c01c980c01e21405031030010f5640302d0054540c0c25480c261860182c0507004582801140c00050030001e100c00407500c0104000100e01d600d074152903503645511803038 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 514489739 1250 514488489 514488521
    0x60922030504061b1106031b030c18010c081806040e091509030408102703030203060108060d110919060b0d0e0721021503090604060f110409090c09 65
    0x51040076004103803030700621113419140341d1a45066944040b00001c81c4d840d5802003001102290020212001c035040580494200b203450b45000040a80300f904000c4180c10504c0b402d01a409141d401900c042402c40d402400340d520f0000d18081d000d45800200f81000d80080c020880083c2c04103010001a00424030040a400300951105603000700074805840c8954640041004019400c0c00040030b280c0d20682c4034002c90b10314848003e001c44074481c86250030301c03904135040752010035034550b00840c440c841c00d803501d01a40d00c0c0c4074280007004841c607500802070071102c8811101880d289100a40c4800c42d16030410080340200c525a003a145180d0008068000214510003400c025014804e080c000c0007009044e114a0952840c46005202144803040c0380a0100e0723030290b448500098160b40c4499031810f0b62401e00000362a0340740d108840079942e2501d040307001e02d41d52650313005215202210140d4181841c0c00c00710160001c0c071071410102c074400000040004c0e40075241c05604007522400034 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 514490989 1250 514489739 514489747
    0x81b070807050f07150504030b0a1b020a030f0c0206030109051302040204061106010b0c03030c030a18080d1a01021c09090e061e190906090606140f010e03060609220305 74
    0x74403a1403d13119401c000e8405100300729001040d41d201068a08890f00404942c04a0300c840b080c0100401d00d200d856500640022041d004094000420300c80c4c0c507100340c0d00c0c0b42c103140740b0784021102000d0200b030003540030000304010040c019058000e035070044208a0002d4445a1a500240c12a4400e5115002054680b0302d41070b8210010b0180311b004019514840345000c80c4420065202e00c0020704249041d100400465174083d91340e404040c003d114030108502a0031181001881c54002c0208a8002810083c0544150305030201038a10000103130001c0900302070303850196054802030199407003003043d90440020750741a1801a00c0310940481c000e42030500b403660030030141041e00807000791021070784007d0102c280102d501700001e8100b0400c0010300e603407052030644042d100c1d0a0019003894180980800c0c521548841c0810040040354070000a241c85401904c40d1600e0300300d140d0f4960494030000d8807a082c00d403c450351203890a40040c0c565004035184104000107100c042d400070b90082 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 514492239 1250 514490989 514491013
    0x3020f12060303092e0302030c0a180f0311040b120a060c03020f040308040317130303080403140a110f070f0306150305030c0c0907090b090409230c09070c03081b07080705 75
    0x170b03007900004503c514083d40f55140480841c00103110305480c5508000da00c83c00203072884c0441034a000131b0300e40e001c0e2250040b0307030b01d0600019201d101c041c030a03c0307146804290380715442c2120b81c40742120100009440c0120b0b9549030320008000e82d00c100001e16400304021800460307224000c10184d403049010030384444c110705200d9004604034222940c070340401c000e4400d040300c031911031101316a4180b601e80303040e55451030b0490790b0340300700c90890030f18010114503103c100385c1220184070100b0381c500444040c013134180200b56a0310f0f024490f441a050700383d001072001c100c20380c000c020340d400d05120500f5203036070302e507901480c560065180d41c9164100891201c46071510b001413903004089894403802c034a0401704004e48a00c40c031140b0500c2030b995100d11900f0008608802804c151581d1005900c1190070022991100c0e2503031442440740318808001050079024810754402e50b50940e60344021550b8143d0502007440242c03180b80c12010050041d0000a03002e180108105440741015004440820b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 514493489 1250 514492239 514492309
    0x1203090c060918070e040204121502040b0f0d0204170d23040504180c06180801020a1b06020f0720030a02030d0c060e061e010603020f1206030309 64
    0x10340030a500c203100402c802c403000c1d03444240030320b41400d41021518658580c04d1081c2c4081155010082e002400030900041d40410b010342da0183d5800b035984030000da07030b42e49403007022032145014550049005100c8518008240409070105100198005180a07100c140c40c034010300c00003c4118590713104044600381143d009140201c142410a08484180d6541c100035031036000e240512070082d90fa40718503110044102110380280d6401c10b81c0d03c850341751500c80062a00d41c0c02d90180907030701d400e07500004000d00305100300d4000440e59030b100c0b0070440300c0111449400c0913034242135230203640034412561144200380051040c244515040060001410b00103040040c0190381c0b180b09811505182c000740c2c401061000550b0594035010b0742003542031a03d080248141c0070396000354441c3d50200b1100c4000040f0450051582c5504d0010581c0d0341d02086050744a2842481c9817a441031014500c0f000c2400c40c0c03c4d8000400134252411b014078840418404142c90042d507a038529000d410b0038140b240 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 514494739 1250 514493489 514493503
    0x506160f0203270607060c03020c01111608090303040f0906031109190f090f0f0b060d030e040504150504030e010f02150112061d0f1905061b040503120309 68
    0x140007850030030280c20711036001500000740000c030748140341d44604003a0751003008445159520842c00c001f803080110004000f50030005880241c0e600e41034010301c849d8130341000d8034003440e140c161264440809a403a054903401c185070140e0584410701000c9908403c100003000a002071200000b41c0070324500f0407071105800c580d6507500441c07110003805030303181414002c076022804020000c1166000d284644000308846040900004200c0088504002c2c0c00024884002d014081801c01070300d901040051440c1900390040204190205184035810160040c60307100d4069001500b480200c0c5500006880040b5011000142122006409580c00c00710001080c4d04610081030f03c203950006022802c6410701034041c0004c4c90711080710402c0804d03005440860102c0c40907180361040c01441690381c4114030206280d81c01000820301d103081501d65440784e0260050000c100d03a4540400d280d842c0b0a441010300a0a00b0810020400e03850802129039103100500289569180100445082c181 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 514495989 1250 514494739 514494767
    0xa0f111e01090609150c02012007090501050301231e040b09010f020c030412062c01061415090103110307090f0e1005060f16060f0b0907021018050616 66
    0x4c1521030511040c0c5032402103c0c91036829042c884207001650006031104207900b900d818036214182900e0004110101e5005c0c11074540717840a01c031030390700c50b410942039071068152240fa41c907510f400d109070201c1d00744e0001e0f001842000300741d0707502c180380d252294000d00071034041e00e203003110300c0c2071001d070050900c84d185c2c01500b000411070500716400302598880c40b0351700c182c0c800b02d644128030100780f008581c88607003051030001c0000ca140040100340640290022580703000e0b540381080005000703403540d0450a41500007803485251744144840c010700790704410f210b20304055450307144101c0040340d64003e50054415440d188134441c9801c4008a05410300d81000581c50307426400c2c41004600d00402300f041c0d5508941540d10f07412001030740d1140780101a00e0030710040c0c0000c100d50a00035154003103020300408a500748044440103040c000d01d64000e5840c0c000580c082c1021000060301c0c1d034061515003e08800c8031b88144255120760b89050303000d0320084000c03410307108109031894004e007022590030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 514497239 1250 514495989 514495997
    0x51902030c0406060915050c0303090a020111010b0a05150c070b0904180209040201030c140319050c070312020d06090e010c02160e01090c03060305100c09090209030a0f111e010906 79
    0x11304082005107560403911510700160f181c5644d0a121720701400650b810708210408507510780c5015540c4c143d80d8419028180e0204141ea0080c980c155010b000d032558021010300308460040c602014403105840b05800b128101c4018040010103c1042c04100c00400000024903101d002e56010001200c0300c07508003211903500c006507200182c40e03180c1c513154400e4090a00140f8820041e000f0b80307a092003544025460040002080b0400d0458102450b01c10717000c0c41e0030801c56950050007501840f8244014000c41d840c10105400c141f803503001011820321108000c18140d95601c40301043c0c07451461007400c0340e51102d98803084070b5030401c141000759034400790118402d407914140388220a418000e002019448020810100340a41c01580045501c04202ca0080710881980c9004144d46020f450001d450f08400290146550094820325040100504402559030b501c0c244c5510100300c0c1122581d1f681c1e000000b41d50b5940d400140c001002134840e030740810018000400342e100940021040c0 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 514498489 1250 514497239 514497251
    0x80108070f050d051e1f0e061503072102030c0103060302060d0e070f0617011406090609040603020409082808160207050411041a0c28051902030c04 65
    0x10100d40712480c41100c0d0180d0f040da008004908140e41004800e88860522520b90030055829800c0022404084440b40c0c21540640c0e840245003800d0310000c0c502c00d00d865000790049040407850700300c0300540e044014222003820b0b907a81c10701c2e901c00b04000354003004000380407403000550030103002482c0546003d01e01003050504503800550365004122104e00718650728002c100e0071000800059026104004018403d41d6031448014801c5843c080340c0d82c0c500c020440000760401040030311018003c0014601410844980c090100036008007000e268003d840e0a00040913072038510440002c140039500c45690343c0482546e24410690a0600c260500000c2c0481180990b0014503da08130002d003280840244100104a10303150807a000349501ca440d01400180d1030340044c00900441d04284c1a00701c4448440e0f0248002d8040c1918041664104a41b03464008841c0300305810074503081c822422600d85a6124a0700d0542c154200c0780402210140072801c0d854108050029850215024444 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 514499739 1250 514498489 514498499
    0x2d0a0918080c030720181b2802070501021507080c0c25150c12050c10020403030305040b0c0c0a080903010b1c020f090709120c210308010807 62
    0x34a00c0300e240500140c0010665980380381040c01180c401d9a0040d1801c0c031004048410340e0450701d000c1036510700c00c4001120010080340480074080c850030004030b54002c4c61080010740c004540c8a00c4807030341001840c041402d1028044859680c3e0a859030b8000c1c0009404d001c00a880c0480c0c4400055440c03841c40c00f0081041d52041116501002d421070707a548500c00410098a008180002c54092039414421003022041c03103c00e00c0110b4840514102c0d840118500954103020520809000b41407c90046a103550240000300110416141203812a0042003c1d2004070f8001c1c0c2c00450000e40c842050000380400104a0364001020308801450510503075031700390303441e01c0039040100300c08000706000d4042e070b40070b6102410207240603015607115054420f59815000c0e903041c00300c1c420305240c85004140e04000f5103944c454005c0341c030350047e41820721800c9200035060b1070044440002c01c580c00310b10010100d400c00d071214003030020300040c0d0135603140152500b98160030841c8903610407202008 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 514500989 1250 514499739 514499771
    0x40e030f030103230d080423030d0207030c0b0c07060c09051003240e1006031404060e031e0901200c0f040e0102191101060e152d0a09 59
    0x81120b504c48032441003014825158440c000703488144e90445d000b0364840410058116031400d00c100d120304c0e520000c140405504001e150307208000c10400707900601607250740420903030080111034000c1c01c10910300256959500c0e1003e804513804d080c00b6101080302010402039025246c0d0246480c00c001101e10b0515003c650710002080806003059150281000d044010b0008074034a004443e4154403071035240d5081c0740060754180c404030003e030280b200010f0307414402c0c400d10a01c803540390002e01464950f234445201812074480c1d144914001003000e0206500d1442d5404074008101740c4040c1c595010b4030001d840d6051020400c0940e0900c01d2a814100310302180c5074007840003c5038074080150000001c103008000309021a186503100042c0210051103528800c5900b445641d0341d42c45008400c0341803400c1c1d8825204072500329480b84c01140e221440103014101d60400904880c0d140c60015180800c2072800c1d5800140010030700c106002c2c0c80c04c11540d50400303004480c505010051900300780d40 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 514502239 1250 514500989 514500991
    0xc0f0d02060a050a322b06030203100204120803041a040c031103070e01290c0f070f1a0a020a062c070f06051612050d0b0f0901030206090a050301090b06040e030f03 72
    0x10190039800204680c00c0c1d40d101b42d550445041c00401e4403030381e030b2900251200502240c001684a80300701d07400701c0c81c40c0281c1d000f1501980c036100084100d901059482c190103400c0940304980000300c50505003c0600d80303100081c8142e0145a11b00705991450508011405072490000e0003031701b207203c05012001500300b000c1e0444800d103503000c0b10840300307048440c0070745502d070b021082890b00000c0980802a0024100c210b281d004016142c0f01c1c3e0340c030340568081644c244a1200e1501a40b5484008060303003402030907100e1024010b036014409c0d0307591080129203079480721204119aa9003048807504d09045902c254100c000010b1410314107180003889503c40c0d601c40c446c01c0060006180018950b0703080541c40c1107920054450503803010403005466a04a9540d0380e10452030b1000344405440c10041500c00040c0103018001ca990031502400303120741c4079524071500000718980000d86c5441c248140600107000c6c1041c1150b905200040000b030320342031200142c5590090080140008881e401c072 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 514503489 1250 514502239 514502327
    0xd060801090b190b060c060a05060109030f060b01051b1501090e0613050f0a0b090d031e0b120709050a0b0a0302010207060c051002040e0901110c0c0f0d02060a050a 72
    0x1101d40c0d00c1440f1a220250682071071140d00a2404185503a04607000030300c113402002009818801d542d41c7c44011210040b5612001c1c080c001c10003519000306000c1d034018090034030103140003850241a804440d0161400d00c5203500154000000003c2031401501c40d00c3c050841284c05000c0304d00e070126002c0e580c46016110300c40c0401c51100500821004001915020f051700c000d0b105c3c00d1b5114207201300400000c8812104900984980d4a030140c824482c500d441d044001c440107041001c00303003003002404880f458940104036400c0c1c21411042c10407821000f07144005000c242890180006d0707007030f6100c1040c998091b9075281070a100517a004180300c2e06440a61800800071942801c019140003c1c01d28034918941c40040c0115601070061007580c8100300f45002171002c10903440e01c0b400c16101c1d2008240180d0002071f0b16082d03600d082200680400c40c014003400000c00c603030300010520b82c44244081c0c00303e1000108440c51580000d0b44c00311403071103908211013454a0345000c206950b041c00c10 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 514504739 1250 514503489 514503511
    0x1270b0a090e06011505090619021e010e01060902040b09090c0d06060f020f060403080117010f020a0216080c030309100309060e0705150309030405060a0203120c0d060801090b 77
    0x965265032108690000200a074000c1806041c1c01c048031180c0b500d10a026401007030401240c5821403500403002c44400240142c006842d008980c02015002248104480c003103006250f143d03408030f0400313a00300c55000c50030800000c03881283e0204500310b8040f507201444a40c010f20041041083d1740082c2c484481c0300b5103110719280d548885604a9105041041822500c1d02c10003103800e907448020045107000300e408480c405d010124091f130395010b080380d0040000d2011001401114000f92105203101003810002c12500c01540c003c0060b40c21160046006922050442045030038403005407000b0301909014200340924000403a88a100e080b418600840b400c0801d80010f5200f0342c01541500e81120301040191001c1c16215110701c060701c0340e6440340d8180c3c04108026401001160300a41c0c7c5030001354a0140f4240030b00910b0b400c5140401d0640c0418400740300c61f0464084103d124240142d44c0e143e83d00120810704044910745d821074505a132401047d080010380c207054035a080344030120 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 514505989 1250 514504739 514504751
    0x70e1207060e0d060501030503030a05060319060b01110a060c080106050a021c09051c0512210c070804290703051c020d020d0e0c090c0307080709050409030e090127 72
    0x4040780900081c0480144045e00d000000018030001001441c003d1800c08030501c600c0e100c1c00304040d40e4058518504402e003000d074801a0000d2180c0d0300c44d00150b4018101440458075210301035003401c803202e8003680c0150311041514801580304440360301620150400c542030500a01c00203558200c100304d07004c200d58411285000203801031081c1350003404001c105202d55251103440101d202c951000850f0a4415005560a00743c82001911504004465a520120ae200d10409050100030703081d0896080c0030070041c00826100c030028070103072401145c5040100e4005020039007580e842402454400c20500c032604c002503118040b038507410340b1042e900c0c41000d140b0b000a4000e10a45105107401880040c0382d49e02d081031504882c5040b041582941d03d590152000e002c4582021925007142802c00c1000490107070060000d41c2c1c03c01c689103172000000b034941e408031b02150707071110094020424a943c08034441c0703420900180949140c0300300140312803480380c1c100a00320a11304000c00c5140ca81ca = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 514507239 1250 514505989 514506017
    0x11030d0503071d10030e010b0603150925110606030738030709060e030d051909053f0606040c0c0209011412010b0d02090406140a05070e120706 63
    0x40f05020415a00801042500802d401c004c0c0090240ca03500d00b480c0c3d42040e071480c00614101054a100302005681d07001c03001814020804110001070104900c1d2854040c0e0041464170003a00c0c1c820640d040e1100d1110314850040245031000c0140458402e83c403040d030901604c040240342520032420190708608405410500c1c00191252000d6036521040110410220b5644050440c045880d01e032100400da900500615446011401d40000400c104204c51120114120b4041350212158a040c0c3c0c10245c42d240001c05034400710180c10001c61400b06000d07010b0096980708021501100041c400d4060752050184e01c540c001000c2034030503a541e40707048250a00400941e8413003540204505101c0d0384440f42d04000c0d018580d035060140c1807001f8881c0d031513141480b03000b007031180061a40d018050f590f801c019000d180104219542500c5011200004000e0030144d80035290132100454540792a120041200c00381c0e000d241d20403c4000c1c0c1e80c81c03004a000c0360781415100f8034580b0302c428030300b03003 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 514508489 1250 514507239 514507277
    0x1209050c040b0f1305060a1211010f17070207060f02030909041b2601060b040b070b040f060507120b0103060b1909050a030503070c05060f0316020c0402130311030d050307 75
    0x3e150168122030b0160b014120442c00707a018900c585002c903031510540d0303110000d05010f40c0d09104010a070035486a61503c9660245409801c6200540742031040240c07400d82c1d07202410416601c00000d40d000d09818000309803c50035034881e84540344000c604003031213000096030390703070025101510040b03044010000c03460100460034060409100703c140300d0a8440418141080511400c0211b54a4203a001c0b5451007040111002c99500413000e03401d01c020b945803032020480141c411906850345030b605a00041d0a0b0003071501c2140b0760f44030742c1c0007000c03d54030020654404500050404d807600f4404e000f0303072405a003074590002004404030115102d1140684844280360412a40491421000000c01200000908250340708282006400d81e4076014803483e8010802c0014410000b4400076840d5081c0c06040307041040d0350310444445d042d00d03101090899000344540b082080c103000c01801400400510400d04080950040441c000c2071240104a070001600c0c95080040b449100e12442c120 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 514509739 1250 514508489 514508509
    0x203010e1501080c011815030b0406141807090e04051603081b2b0207050405100311060703052508031006080a0c0212090a030c030803071209050c040b 66
    0x12412910201d00514003108031803000d1091007568071800007110741a5124018032030104c420302e40c054484500b00180f0320880500e00501404150740d070420040d05d0340d02c50241078003c054000924aa0444481c04c0c40510b400d4441d8841418a0702c0c0140700e182940040c040e03084820040e02d045450b00e65107400d508104c2c01000f81d10280d40d100c44c012060068080090810b1021007040d605a400c80302e07599500d03030402d071428004401c0080c00607541a079448041482000305441510003e540350750014085400a4590307800030241501c09104008409043c00c503000402c94403103007001400d590051040c8240d48040d001c5018001159201c1d244400b00403041e20351004607140c4916160440c040c1c000700c548280800540c4041c00300380c0d680380d94480c1c2e80680350258098903e041032030b1086c030815444041442c2e080b0501e0100000031901c03e80e0040c001d14410442d42d5a40d0070701400040502c000003c402c501e81c1e141000c0784001070000981c00031012402d03100416540510000540900300c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 514510989 1250 514509739 514509761
    0x8030a0e18010306140a090507050f27150303040b0405151c0f051f05010f02031303050c04200d05070e1003090c120203120c01110a09060813021804020301 68
    0x901d2600200800030582c0000c21007050300d000420140d954600c001c819034100003c0600b41d078020301010300480c2000c54134524030000107428820300b240200c1101e003241d042d842c400c007031501505041c8041c56420544c101311000b401c500440c1070a007000050383d180d106502ca0b03a8840e500f80220050201e0501081d181c00000b0350200c4a54101d5080d5500003820b90180445ca52902e4440010b131440201d64605010f98809a8130300103a5050a0066a021005000d0403055100074001d0001c0400d0411040e00954810805401c5208048041c0000d65040c6810317100d0031010080e1100e5130302d503030b0815a0b001514004012030f05440342d0505440254007000712a0700b000d2443c480c03050050f015003040c04028440e42c98960020368030840d01051180c0103000941c0f5402260300c00c0e803c0d400700c001510301001c2070b0000083c103482c01084910039a006202940c00b00e95400b10421003150046c2000d5841000505511001c5009a00085038403da210840003c094200c01080540d00c0950102180b81 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 514512239 1250 514510989 514511029
    0x402180f180906011d040809040e0f010905070503060c0309030d09110411091503150d0c2403050106030203041106030a0f0638121306020f03190608030a0e 68
    0x1080c01d5201c15240d400034000d8203e140d000c0710900171a80364a0b81921300c1190082d6007142000c4500080101a22407580900b805119001103c903101500380b0641110324821002051031916000901d801c0410040074640720035024410006d201d040030040307803202600c40b800094080690310f0481d445010101c100c42d005490500c01c07180c01d003096030003450081022220842c8846c91512901d0041c801101e202e15070102501c8145200e0400c4140c0c0c0000d540300c0c400a400301c540b544d0b010034103450b04540301d203070209640c60046074803500743c4225809480360b80b50961035843c160310b45042541c1d50382c05250003200e0001c00180185a99440802546592901417103160b0340c0304000303c005002e00d10074a42912007103444500e102c140d80c0841c003641555117411400c000541c00110798612000703001c50842c464030805140011507503c0100300494510b10a81d480f03003000b1001c00c40720309100c00c02d0301d0100d181c08024040341c0400801c0c0e43c0319181c2d0b1300d0700c2c0c420b0f0800000800c50b070398042c402c4a8100 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 514513489 1250 514512239 514512241
    0xb1c03020f0d0f030b030a02011d060c03120414070e06060706020c010f021b061b09121005010e0f0907030b28020403110a030809010305041109071d0402180f18 70
    0x8160302140d511801c1c0300f1a40c0a011700c0304148105070b140c481144000b40802c1003c04200a0381c1d41c03903409408051002400142409401c19106040d544101808013214500900f00000c0100d402943c10b14080351400a001a9013416200b900d0490003404040c400c1000ac2250002c00c0303030a4040700d004140e5a00244060701208482e20040c0d000442c05000e58428000c034040c1480000500d64814183c0001c2c2045601c00408000c0d0154070880d58030f90845032200c090500c2000c10032460242c50171404001982c1d41c98103820158410700030300300f503c031000503400b8061456000100b03041030300e80007400c01c1c0041c1c0b20040c1e007051800035201921a10000d441d011780c1c1d04000d40c0e0180c4216402a13069034503194680d0200101d809140c0001003059a0030311400d4200d52203580310a51141c420708082e1400540e40c1e000138038005040307030754100042e0070782440281e4015103881d05030b4440701503d0039030610340031600c000700c0398040d04103180c05814544402c0216558601c00c5035100060308110303000d1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 514514739 1250 514513489 514513513
    0x3050a0309060831021c0b1b030c090f040608072d060c0f02150d1a011103071b09061805010618090b040e0d020d02010f0b1c03020f 58
    0x41c00000d40300e040d0100d035000c0b00040300c070401c100403000c41200306006044c003144060207003070860001e4101a030f08805044802c40441002e101640720890282c015010301c1c0ca01245c20034400385403c1c4541c1c081d00e07010f10900006140f41e90580d007030000110342180942e01e014000c1001010594400491817141c104001504003000ca40184503c441d245065101c82083d82120b41081c032601c0b0b014005002c1e04c4c080f070302281c1c2000804103203e100511192444030360702e0505a85e600440d1000e012659200800000100fa904400b0100d480a092221281c03030705010403500d80c050383e80f014199800c00102081d00700245400c00e0b000d00600c000030030881707458008520910302c060845001582c40d00e000403441034040c41c0e0b07030805595110340340d041e41c80c14110703002e0152141c520381c2d81d00301d5200c1005094800040c000808040c60303a500400340c0d9a9200340090035030b4901c0513903540c6945001504001511215a5804680110182e080300301500d450201d10b00700c01c040c4111014020540d020103 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 514515989 1250 514514739 514514747
    0xa0902031f0b01030e1527030708041e0b1603200c031612080c0307050708030c0d0903020d0803221a010618050906010306080102120a14070f1803050a03 67
    0x40b465020b0b6020003402c80c1000e1581d58800c000da00f00c00c10084c25100081c0805001c0300034161441600c040e655240000168252440d08104400c1340c2303508000c1420b00001c00c3e52508528000c503e01d0164030100c0c40e04101c0400344c416000c110802000840005081c54081c3c0c4188400b4100b00c0000c105400258040369100c403031000005101e401741004000e0040d900750441010b40d80b600c5001c0160711902c1c0d503880d055510464500100f804144000c0700400d4007072000000518081c0e001e1555161000e1080f03040803001e41101c018400605814400b503202c420181c110a51300043c8155252030f115024520800c603121400510b00c2030300800c0040185500e8070320f4181903c2c500400d040c2e6240e03d0705035150708400c043c80d071510b80344060400c0185800e501141d040715060500042840e01c40c801c444c2a6400f00c60841d460902010a006040f0714600c9007901400303110403405003504000c10000e220f000704900030810441c0f61b0761012544442d65180c00c00944d0701c20f0456031005010b1a01034 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 514517239 1250 514515989 514516001
    0xc09050603040f110312090d031719050105040213051e060309030403020a060503040b060f0616110a15080109020906160b150901290415020625080a0902031f 69
    0x241c1322200240050301d2814005a0a03020308030f2840c00700d00344801e40e024403800c6011108103904209905241d0303544280f214508501400c0d0160410380da0f00080103062042d00e40c1a840036019a00c10070100c000f40340c1ca20b07844400d07518100d4441c107040220003026030086c0403640911703901c01c100001344418060008010403c0724400d1341e60014203956030500f034035039000803030300a4480010700000035444d1410a081700d61400d401488070b41003031000c0010261901c0301a600319110003c200c880b22603480c0c40070b00e44e4020300d12801440b1696070b501600070700c1ca40741807050181c0e940e00441c1c009929900c480a0381c0d08050003900c0300c40d40c50480e003403416140707005030f60026545c1d41130904c0b01d415040030940e46043c0e50460b0116065400820207015120955640002046900b4440030425410036604041e0342c00d6268014400e6040c0704525284c60261844165107908062112809490b0080c80d659071040ea5000009210340907400820b0070300c220b0742210078400040c0c1c2070385a81044258440 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 514518489 1250 514517239 514517243
    0xc090a060f120309080d08010b03090f0607020d140a050f0c0f0118030e010e03031602010c06021603090603050f0f0411150a0e190308070201110610360c09050603040f 73
    0x80b2080d40e41c3c07584035446d44d100b00e50180014621a0040c00404035440040d608020120111118600c2c90300c0544e003040000c1d03031500d0060b04115062812558080424004c1c80c04031440c1c68a0001200c001034140c0c81040d80d15007040501041c01441c18109110380111600840000d01070303800c2420925080310b2543c581140440c44140048506504c41c80424014802c09001103150041415001c40085101d0704128108400d04119900140e034034000b500402a0308040b060440210346005400942c0940181003094640380400c4020819549010b8020424800118103074a603410207080b00740b145403140e41c01607004100b0710344103068500109804401c07990b40781d414400c480200030340c0112120b02101e500506403030a20208501d80010f1221b00d1050400c04495450180d2580c00e280048540743d95400d44108100305613030a2031800820518a09641001c801e8181d5510320b40c200c140c16900b0300a1760f240c4110350030501a00c070306030280000030070450b00ea01d8a8a8600300d003407141041 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 514519739 1250 514518489 514518497
    0x4080a0f02010912050d090f0b0106030507021b013b12071d0606130303080103020f01030c080411010909020d0506180c07031b14010b100905030c090a060f1203 70
    0x440c4980c0d51062090555030b5900c1002c2c110b1010600c0c00496042e003051080340c9103a80d544c40c160b000a000c10320f240d02e00a10480c2e81030195850000050111500149050155080390000b5130401060130302c1e60800c1c00b401d0030600410151328004003090001c01040980c0042002015840c42c1c2c03000e003c44840300da048501590101c2400314050301e03084144030703203005800000d000b42040c69148102c50752041c00a0001402d05030010300c0d07240c0314540c5034010340109100c00014806c0d4206050404484a42800c00303116007140d20200400c0000000c0c0701a002c0c504203004241140c0c85420f580340145aa19020341d114005002c1d400001c0c0001c0d280a403040e589550841d01e0522099002e9201d005103040301800c0c5200c6450555610007071420304c3d07149001b4080d1079000101d0308201214014009800020b8484491040c00080700207ca801010700180b03ca041000b96000144585170313140c1512079680548a088480c0c0143c01c682e0407a910800301c11402180c07494100c1c0040c24038038000d543d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 514520989 1250 514519739 514519757
    0x16060902040608033619080105070305060a03020d050a051c181401080c040e1504050906040c15050d060b03040b0c04050901050411070c0603060f05012105090a0b04080a 74
    0x20442ea0304d1003483e2076080c06400d80c00181d801c200308013001740c080340301281c1c0002d201d101390800902e888610752110018940300b402d0a014008091254540c442190f0030108014101500060140411484001c1c0309403d0742000c001040810301540c10b6883d0b1240881c2c0c641c03c403c1c2901c00c038101032031054100146608100000c04030296000c80110340e115003036041c444180760011519448010078642c4481f0042200052405001d03d520b80310700201c2d010848006c508404000540f4405030450856a1182c0203010205142c4448138080b10301a88200042480c0807006840034041c0d1a084990b8610700300000803003080400041d442644204400c50450307a0700c0000d0b500b5806070303008450b00116000014099820668051003d080c2060421420b24000f030340c3e541100d0006401c000c0009840e04010421024914ac0c40005483c09090113000000340b20b95201c15a60074081e0b2911281d103907004600c80000511030b03420ba00b07422003421109031509041191705035001c42404000110226 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 514522239 1250 514520989 514520999
    0x8030a0b1c0b18030f0904060b070b010504150f03110414010e040230011a030705030a08070f05030a03020703080105010333050301151d1b0f160609020406 68
    0x2030805144480322204108030050540c035054070410300141021581504080703e100c502c0010000303170034103001542d0001e50303e022810a000684001750b0100000690900042d00000c04d02c0c00c65605459080e2400a5440552010b21258422592015044604418011080c4048010b070088901e005a5040c040c0400d0120300408540d400d10508100c15003800201c2c00615000103c80c102c0e00d070200c15a1700f9000c0b001e40403001d00030302d100341401d90381d56245c2d01c004249901034a61701c905021000341400c0391404000c0f9859010302c090080c0407810004400c4100040d05801100042d040800c0300d450746108800074000790301103501540418080d2000188961080c02040209034102585583c88107810400c02003c101030803500040c0c0d0b0b504180824151000d110b20a000380c0200c2c09840800c0c03402030303002c0b00c009922007880c0b0003250407010007029245440d503008e01c1c5031400301e07a6030703a440000d03051a0f2540a41880d0100d1021201400b00c180140e41c0c022a807014000c40f0204284c541d51 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 514523489 1250 514522239 514522249
    0x110409050108160f03030305090307061814011118030307060504150f0228030e06070c0b150a05120a080304061b0e0108060103020a02070f060314070f020a110d060908030a0b 76
    0x64032813141454107010080c00060701c039800080c0c00003100401c81c3e00f080701c240d0300c44c0300742c070300001c2a170590b81000c65200c400d100c2c16407030211405224800070040c0c151030144241041c8a1a80d00a04260b8454441e8000e92810411150301c2608648100401d0906103464060303014081c1620150908100843c2101c0040b4401c8840c082d001c00e00122880144150381c00310303240ca14190030107041d62000405148031040c010740c0d01c24001a40e41e9103180a281c0b0700000c4541c409001c02c0c0315540040c64400f41515401c000701d051314401c030740d00040c4801c0e040a00b868184041c200400014001c018001002210380001d080000d220f1020541d004480c24200e8008407910b00c0d25001807003e5010851b5940640d0050510207110b10503a0320068907600d00601403004ca501c1500041c3da41c4d40321481d000588082e0a810649624200002d20115180255100107000000d0145816002000345550f503030a4140c4070241e1201e000e00c812085820701035540d400869420f0403550902180c10098a00 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 514524739 1250 514523489 514523533
    0x30d09021804051f0e0319050c0708030915091503130c140a0b0702100809030f16120c080702062b0e010e0a03090306050411030f070f0e04081b01110409050108 70
    0x2176030040d030070b21008a0740114400b4000e5aa001849801c00202d07000507030511019000d421400e00650b0381d01030700806c0c031001c4103246400c0e07081c1d12424003ca0f02a661000000d01c1d004410f1a0142c1c0c403502c5280c402515028244401010f4100301c0c40000780200b00c03030380612420038040319402c1c6d06030f507190002140d5104070f000c020b42c00382101ca8840e025030702600c2c010b6000080e102c116820448003100038100303a03001d00004140719840050b4501005000d100c4041d5000e120703c0c11a4070608565500c46c0780b8002e040d03009100f2180410503645603981c013040d5415104603040000345102130002c81c1d10040c042a000300c0c00c19420104400303e031070b000140ea07a402650641d80c1540d503500e19200c80c8000c041c060000c95101000b0200c40703090355020054a042c00c840007002d04650b524002c0c8060040d500e680c00105060786c00010440418500e4094500e403240d0402002804892031540c02c2c010328600240c0494684041000b00f6074603041e9006906a0702148111000c200e07000c601403c2d5494 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 514525989 1250 514524739 514524761
    0x10608070503061306080111090a05030307050318061314031c0f110f01020406120c080103081603020721060609050903160c091d06061002030d09021804051f 69
    0x40030404079009043c0081e4807070524500b44c0c400039200da252401785082d01c4046a071010000e0002c64000c4091402c03140e143c0041100300c00951030725403603a81d4192640181501d5600105055158a406032107150458818000c440305403441c0c10340f186544c4950a4a1100720360107881810340c00d038004c0050920a501000b80c0e92205682e070a00795404407089002c905a07031200e4042c1c51b5140742800300034005031015010545490750691100301c82c0d03900300c5440310308207401c00c4018001000460074140440d5284802860511480c1245003810382c50500b503031348180c1d210007181800494529801001c0c0c031105200e06000e00101c2e564015040584600703540c540620307001002100b0211440070036218015100d2020074132940d0783d89000004031118021502100c0c7c80e6003094150f24042800041c4e4421004c075540400440c10a50003580c0c1e010b070381384011310345a81d0340584c07056556010003131880030900150710301e9504d0180752443c1c94036810f0745d0b824460740080c02d45404c05a494007503988019 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 514527239 1250 514525989 514525997
    0x40504031b0206070c06020a02192105031314040b01080402132007150b06071709150d061403070b03150d060c0c020f011704060e010e100b01020601060807 68
    0x7030141c1e080112100100402203030300080400c01240051208400c1100801d00707038004e0f0001c80890300520281a90349048641d000815030818450a140c80c2403907010780c850070800c1d550090303c500c4d22500d584640c503c04401c5039000395000448680d18600e424407442c050701c05107e04100c00380190707002d13a400d81d0000c0d40900c0c82c00340c004002500c0d600141e000c118640c00c1d0211044c600d00d0103080750707211140a0f56981001d00b403a4060b20424010950541c80076520340345810081c2d01c4200c803402080000a02145001945803116564490540701d584541d4000b00daa4443d42440d0400a00051080080c0421981e400e02018a4045402001c0b03e10603942c29285640308400340604500341120ba0368404000405400810300c00e01c20000b03410060341303a00040c0140e0740100700300351442100e854100259034001e070ba4290302c00c074119500141c0c040008030b140c1100c8519603014110310000000e0702c1c41400c2489451b0342e43d0360441902039400303800b43d55440e40c0381d0600704e600361011500c40d8003003 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 514528489 1250 514527239 514527257
    0xc06100f060e040903020a0f080910090e0412030b06040b090a0b0f12090a0c060c0c150509010e06120c03040b010b180d11090c0a020c030c03070303050304031e0305040501050604050403 81
    0x30f401d1903082089514400c0c03058a240c00c03100d60710802e940308060015036142e8000b042040c00c605084a0408824140b4101410402c0c44c00c005070307001550003030005254000c81100265803d002c0c0c0c00411307a52500030202c070784541e05c40d0101c41c10341d0020985144a214501030014141400d0412940765644003101c66240c0700d200641c844550101800020701c80c0300d8080f0f03030780c046864814070901030403095590310500d0459003046402043d058216454240581110084d4a5040012a2000102820003d400c4480f00000072014042e014800e0781c0e45c0c580c40308101005800600039407003584540018811641c9903552130300300b801585a24160b0395613260b4445642c3c50b281d10300c11202c903c1002108911313660038000c12407c034000d58103039400c140e000ca03502442c190141300300400d01d1001d500034030515025400081d47c442042c070028050100c000f0101d400d261181c914800c08841d0340c007542f10f0b120a0058014000c1c5022030701929207518100c0403400e00c0c545405001d000d00d0b003607501d002070 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 514529739 1250 514528489 514528517
    0x90105030717030903010c050d050703050108061810020a0c0308010e010b0d0203042307050a05031c030c110109050303010317030f06010815030708010617070303140703140c06100f06 80
    0xc001120b502080388414080d01e060f42c0c0d024060301c0d82140301135032040d45070750001000505903034000d0300d41420300d81060014800040c0004545a014001c64040c424a02041c100c031401c01101021300d0b00681e000180414841d50231450380390070103101c1d44d100c0b003030b42e030780d03031292400e00c000038051a907400004200303089000969402a54102d4010501e140d032104500c10b0400003440c20b01004a120f0300114010086490f0200d990340060030281e0180c5115080d2003c1740000700c1c444168801856a18501150403a00ca0250107004c03c040d03e0003000040c4c66400d1696a030f41003403004031444490b05c01c0400c003040301e100680740614a480c0041c80c49440c0d600054aa01c200182640700e40c240d403da100b400c55034100081d0b80148000c2e00009103040c180421207460214036020307102a580285010000650f1049402c8040c0101c000c0e91a180d10561800300c1703140104480c1ba10050001180540760307490013081c1c03180501c0030600511040c81c1d54a518081d0040c07a84645808101c200e0b0b00606 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 514530989 1250 514529739 514529759
    0x609030310152703051b0114031b0c010906050a18060509100908030f06010509091b0d050103031d03120406030b0a091b020d3009050f0307110901050307 67
    0x191803000e60030b240b080d20824a081c50490b002c081a406031400c0f03000d5081042c04014480308403040c0c80550b050068548410028007a000000205058807100200107107070315030314400f080070101031592a05d030341e80945c00c403d5001c3d00321198256081440c280214032000300714071400540d0344e810745140400510a85038200203003c0282031608602503848512408001032081d42c0c0401d1040d90356544030309194500b120007510082001e81446802c20540e82c5030340d03444400a80c81850200413403044044004094418050009100b0140e4200070003c400c06410803101c28004d0070030444100c1c200d40c4002059a980b4040a00c142e03805001c02c0305000840c4250840c4050300009000c81203100c0d03444940c102245c60000c501d58041c1d0400450150f403540c107002d02c034162215440c00c8030f03004c25060203e100c080c20030101032403120028600750762a1a0aa00188400fa41003000e036503021083c00384031031310380d070080c00102d4038000a500c160b0320524100307038400e06941c8090018100c042c00d00300004 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 514532239 1250 514530989 514531019
    0x20d03030213090e0a031b020d02090406110304060e010b01210f02090d050115060e18041a010905060f0613050603040203070b040b0702040617120f1e030103050609030310 75
    0x280304801e9140400e030700c41d16010b050011201d1400609174004170307090051161014041e580c03c03108090049a0160b60b0740c90b0f00c007001c10b4044508450540b00c51900400914111482503035043e408410402072010345e038040084e0b840b10000174000c0405610044640c042d103030b02500e000000e441d805400c108601d500200203010a10380051820f402d480005d11504074060044843e07a448981f896906015124030034000c1c5070780d06004403400320150009041c0801c2d040010000e501b00340000d02403180c04405071600c0c1c0d4805d1030300711403561150a1031010340000c8034068010007904044490034209141201c8403480050000404641400c040204aa00282059038588101e440101d06024114000c1000304080301540741e0b80e841ca0300c140300560340c5030f90020740d00e1504560560619680030038500755421500303452070f03070781c090304584d41c0020f0044011144d0380c13a10f0b0700341141541442000139416203000d1001ca94180d41c46012190345c0c0d1000b1520b402c40c2a182a10400c20491020244 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 514533489 1250 514532239 514532257
    0x901170604110a050a0e04170a12090f020409050708010e150412090e090f060a0b060d05040201030204081905100204081e1e0607030f0e0309060c0102070b040b07080f0103020d030302 80
    0x12140c4556030000207007549120b405c1001b2401241c0306100c10480d11007011b00c00c6855603a080340c10414161800b401c0320148404070802d0315126180c0b082080700202000c01300c141c1c001d000b04074a007004d0070215a21b129034012903032158640301c140390140c500003620b840014400c2480ba00d00740d44540d50b07880392803203906884050019665010440c14225a0480d200e000584024003964540c500c00c14600308000c3e240503045460141e00701c98a40300d002c101d8078401d000c1840810300b07449920040700203228a0b4800d82441c0034141c0b00541c20701400c0c1411750070341c2c00359044aa44c6450010320304100d114a104082c01c036403004c1100892400c0441001c0540d8000105440601030004d0346c40041c00e00543d036641b8030703030020010424100e030103110340e240c140001d0300e081003a03120124900d6070b00e20840748101d2003048007107a881d481110940454007007641c007481d416020300345407402c20044541550002e0120b5420f000085104d140b6600e41412aa0010a01c14115009440c01c0e402580a1200 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 514534739 1250 514533489 514533499
    0x10501050d08130b190807051306050306130204171204210615033503070315080118021c0305030a0e030721020d02211c1a090117060411 60
    0x2000136000041005410301c0c00790000340034084142000700401da01030051102091200030301c1007080b94655140c0381d0b0141e6540d414030070761360f898030320028002c4a0880384407920f8074000100070070310060300d000304450000440304072010145ca1113000740040c010350041000a1500482101b400910720701c429050500510340021030802d40d1808402080c030710341055466460703a4008a41200c11481909055860100405018000310103500d04c0c0e440083c218504060300c1d030b603840f45101d594114940007414100000c00040c680c0070708a00080503900c0d420b0744500d45030035080110a507000c2c000d20020b503040d40c40e245966640c1071502c0c0204800142e5161600c0140824070000c1d050501211300d0740140c3c40d60025803008100d009151460805010013103400071803281112608103560240c0407a1903100e150303125600c0d112280c0d001c0e40c07001400300666041000100320b00b0100014800c031100d06940700310071a80c03108030b02c04d138803846681d042440d9407100380041d000c00d40c0c03680066018400100 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 514535989 1250 514534739 514534777
    0x3041d01120219030f0c0e010501030c0207140621010e0603030708030103061109030a030c05100605150c0f0327040e030307031104050a090b0a05030127080f0d1b02010501050d08 78
    0x224041719000c00b40701180d40f203400240c1400071110b2624000d0050000340703000c1c0000d05113980001e45032045413203004521883c8042c1d020a590720482690500c400f420b04100300442e05842000c12800e082c41005103103803074a80815542d04000c0111098140c0001c80b4514692070350f40e42100420300c03102071141a030400c0c00a20103e54045c000190158025603c0c0c6042c0400d03418150b0404015841c007944851802c4070410054452004807585003045030315583d00c074602049400e05003461112150180d00001402c444000440b001002c0b140c0454128542c5604081042c401107410701c1501d6506540700307000041c1c0c01d5105c0e8100203900003094140c1340c01c19a490001c1481302c1f58a8100d410600d441d03030a01e40309820580543c0c2c0c02000228001d025100b10440c40005c000720242210311412031008103601841300440c101e40c060001c03c4807503903841500203820802800c01c2c070291042d01074450110800c01e031050040d10f060360b030000c1829a1541060307481d01c0741503110310321000840c08410 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 514537239 1250 514535989 514535993
    0x30a18090204030b041a13021201140f0921090607020d02190614040302012703050715021605030709020a1806200105070530010803041d0112021903 65
    0x4000b070300096105001840302400c2174581003050008500c0755008405030b140822220742c6080d448204940e4040d00d0b420b4694102900e8207002d4029040c950540c00003003403c1c0304421082102903445a0381034000e4622060440c100d400c0c05403004481907a9815043c84036083c6850410020700303206200604144500f2000d6000c19003501240c000e00d0f80400e800d04041101d00d80003422061100350142d4141e151604681c0080d1103034031291290040760444600c0d20349030584008410f4081c6421004131104c1595807032802c3d02560b4000c8260780140280c40c111221880030f00190340c10341e4130080107404c10604040c80340000707402c41030590b0700300068120308800650300c841c0c0140242c035080e80c0d664040d2a44079400f079201c542c0c50490350280c1c1c1c5081d0420020950082c00e13103002d174440700300070101115500000104040030b04e80c4186078840003000001c428030000300610466070752118421700d2100c086038907007500200340309044c08000e061400c00014036000c08141040540c0b603071690449a100e07 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 514538489 1250 514537239 514537241
    0x81306060306021801020703080f130b0d230702070329090303040c0f031e020604150206160903030e0909030c07090605090f0402010e0d060f110921030a1809 69
    0xa90042c0c42c600e50004801c0d080c0b694040c50198402e5003030004029440c07a560f0f40d0f14540c403a50212000110011030040e420f01e112041032002410899911501d03800b070785482c07031b004012000080700c01d0a640280c100c46099840e41c154441d007070603009028060300e1511643c0342c0d540301c0c55508803044e50402c0c0d22000c501685c40d43c42d024543d54401161240741918001c100702d8100d8201c1a40c490264008000003009418945030b80030600041411065141c4081096802a600012207a9105031190a29070340d0000d0090710407808000c00904861510400b91000046404050300041448a2051303190812000641d08000d02400b240d00c2c100c1564501c0c0d0502c400b5070011104203032501d400b0441c5203000f02c1c0140c0c20101c050015400c41c103113a40007a01690303122250902503a0a01c00799428041c1a50013005007810605c01806265508114982160300442842c0c0c4101d49043d0b201c011105c0000301c4003901c010800055141840c040010394802c5c4900201c2d5100c1d04100390003040381203403 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 514539739 1250 514538489 514538501
    0x50d0c0512041e0503060408030c13050d05100501170d0309260a0207080601060f1b150608010f0e030a0c140d0c050c12031e040b0c0c030f030304030206040201081306 73
    0x111240b01c2080c2c040d0041480a6080a513202d280310741d111006100c0400c150b041242e03081094080d084d40c2c1c4642010f00e401d0307442e0490b80202d901640b6200c401c4103000d404218869081503d030020081c0c2e80c0c035480d04000d80022038048401a90107004040c4030316000344d02082d0030300c2c01004215116141ca06100006c030620f0b6904c1d84881c80c1c089407217034070390750100803820190040e1030252980350305144001b003a5400b244018010801e0321506c2e82141040880f00c1c45242e90400e0100ca0001800142200688494031441d01158600001541410002e1003480304020241000d1440c281e0b5681e4226071081c0c11440a40c3c4019a00c03560303000100c0f0810604400105540f101700703d088503824001d0600d000000c01500900340724061104101c0d01004458008181210908a40000c1c1e41c00151500458210644400c00044c1c80844014001007004028904504a07800d0f2244c0400301d54690209680050151b442400800c0066000349411075010b40f1880c10003210007026200e410558032 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 514540989 1250 514539739 514539749
    0xf05071b091d0c0f1011010e0102250b150a0b0d0f053d082409120304021036120c090b040207020a060906020c0d050d0c051204 56
    0x1039144842d24000072028000e60900c00d1031009002e9210829001ca01c03041c0b2503552a5220320140758801a515003d03803407400c04207103000000c00c041d0a120075818000d600412a0441d1992002d0b40082c4c1d4071415100d05441540c0728007000d003140c40d00640340124010040a259004000e03980100d0000c40300300251114894a00740070600140c0c40c40c4003411142c010f441520800c0d00182c03014421440e616040b140c01491400c142d449128942400c811180345401201903406813400050060319401d00404540001c0280c504260f111201080e54454000c80c2c04031081c0d9040c0f000170054903101d400303886000320600305900d02d140000c0031102d41c400c000710088040000e07010001d07900703e0a10995400b4141c640c0300324440d08056154828040c009209801e6800d4641543c3c125548443c0c0556042a90103400401d9a03926150040c1400031240039500c010b00c070340070f401340461a00500b1600f41f00e81103000740c8440c1d009148100c610480b4150151030758899454607420b400c0c0850001d00c0104 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 514542239 1250 514540989 514540991
    0x9010c02030f0a030905270402042d0c08090a030528120c081512010b03160801150515030604093c050d0c051606030c110d0f05071b09 59
    0x3d680d10700907214416540101c2e0052035980321400000d80d42034801810080c100318100e40c15078a62000030003415004045e0b12011942032078903241d4442d038081c0c001178003ea209080c0700d15840444100c0d40568112602c10065210030741741c502180c09240148450f035040c13004a407421103400701c003840d40c085001c0d00e00e002854100d0b54003426042c9124587d145a028542903140e4141603080704114000c1551a40c81344021030030103114604250310441003003c0140c01e58842181481c86103124070254410011503500700384000c511045085182015100c00600d00e0780f40010001d0103030043d800040c2a184c0203035807011000d0114081c4040d541e00b49040b128a141d1280c0c00361028503640c07521b40f20319194521a8901040007490100740c4240c2e80c03500b0f1802203904201707402c0052404040510390724502501d0000410440d9254018145106240e00c54242c1300b10560782040d612030424001c4400a50795a40079410f00303112704001d2001364090185000034490304414040d02c2040c9900c20700c555 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 514543489 1250 514542239 514542253
    0x3010b0301080c09010b03223809030d0f0b04060906090b090c07080901051b011a0603060a060e030703080c0a020918060c030402060c0307050d090510021209010c02030f 74
    0x3408081040030b40c83c0009980311150707545810200c803468003000d403404015104216000c0000242d10a20120350358000405e070030202203a10b604141d070b007002c0001e110708262000d070880c07680e00c0e40e940003409594640c5c011850801d810178400010002d120004008948035031070800d141c0c5d84c4e800b5460141200c8400042d20510340708401045644da004507034001d110a00800c15409400402c0d950480d03000741005030f8400d20140100c44620810300d0384520311444c1ca102c82807908055021010010626103030342c5a807032130f00003000451f000c01c0750310707690100081e0024842144211484a18920050101c0d015651281d5880b41250007040c6282141d0b400305028030f040d8508000b0b0750b0303042a001000c014a208444502c580c880748001c1c880c8001c1c050020219085468444c100d41140300c040090701d0320fa801c2da01d003d82d01ca18881e400c07400051200d02001c2954036010103140080030300b51b0002d00102d00c0d540e0740c1e2142900700d41912414880c44a8103480541c85c1070046503420185207010b840c0c8 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 514544739 1250 514543489 514543499
    0x40909110420030c070501140a1b14031801180b0910050403090e0601180e0405100b031009020a0b030403020f0f01110301050913020a090c031410050d1703010b0301 72
    0x1141c1d8102c080c95080b10041c40c42090860140c01229044614458031a0f660701850420700d0243c8007200002e0a0398060f00c0410540e40301d1a0300c012044481c1c0b0044155216020b1000c482300c88002c04150300b40001040480d038140c80129011051403a50380000c41e000040c80d24000c00c0d1801d000c0181c50400b404400c016503a2800d0101700c52014504030104428105901e004082580500a840300b0f4a01c04021035034903801004404101c0c8000c013041818241c8981001e42c42240a0350100d40710702c10314101034804180e42c010460380380d4000d801000c2c50540c1449440207001111426a00a06035810105201c03e405005600c81c070b0090300200a0140030305e1616150a650820b4050164502042d003003000e0010403c0381c0c110744085403503c03441c1c0c8030b0a140481c103603105031000f5130040e00d5440010b003048554002002c401200e850410014030700c12010203044008844a2105c603610340410720051405a0503040c3c1e042c052540012000c60340040d42d2007a92081e017010ba1000c0001c401000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 514545989 1250 514544739 514544741
    0xf0d030c030f06060804080318031305100305060f040f0603020d0b090d0801051005030711070314160e040609080d0213050901050d030e060a021f061409070203040b09060409091104 79
    0xb9910060032030411581c1e01c1c014008120b00b1018000170001040040400ea403902640f02c10095401c042e0280d0703036140e00340018200107400300e08c203a9002e00c0003041031801590081c4202d61240a015010340d0442d44880104002490702000728072186a07525004005a2590400590514030038410b070085d60130724040c640e103002c04080b00c0c41c04010a25005004071381b00e0030b4103900310801c1400d0181d12a180c0700416103020f100c6948103511031090180000078028a9090109003110010984d05082884804510000c81781d014030005810342001003400a120765100340c2c811405411001d00348030700030281d00244c2c0d102804008013114032140c05d01c03252502c03000c0c0500609045883c2807031030f86156005481c500c514000d141c8a10f0010403461030b402d0090008091303000a582c4062040300361041c1c0e070b0006142a00074034201401810001c0340a09111100501030621500110304141c64445202c00560060080315048030090000045c001c001e070140403201032096120b240100b4003002404 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 514547239 1250 514545989 514546001
    0x6070f17010b0c0f06241c060906240b03100f030c05040b0d02012304090e011d07030201080c090f04020c060703050705041508090708060903040f05031218030f0d030c03 74
    0x880c403a0070500901940904560303c0d00701c5103040c6c1c2c1045002a42d030030001050a4110680c2880715240d4030b1828042241c0c0c1d070301039548144030305020010441c000d1004a444501542074014083c0c0920b400c1c451420490050341e40302440c2c152040e80e003a00c412000c02c00012aa0088502d99500c04040c00140381501410000105c00e0380c0d224500fa5131500000d1203801c20790700707086d140040d40c840c61943d5030311002280e0261080399400d000b003900c680c4032180245143e42440740d5080d442e00300319114460210300b8400f22034050359556115207ea40b80c1b1075a5620130408a5800040c004428205031602d001510b20208480c02909403454070060140c140c0720000e1413081000000c0000780092803240400c1c00e071407a40d504c3e00c181c0d181e4030804140c0ca0400541c0207803040e44134038400c1001100c0008000c3c803c0d5680300b050480040d5841040c5692160400c0340441d6044050101500c031404000c2d00383c020341e000034102c030480c5841c0794505040109210402d0000707a01c1d1402c1e09459600340c06a8 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 514548489 1250 514547239 514547263
    0x3080c06070309030818070302090717090705010807081504060311030615061b01021b331504090c090203150a0302060702010c050304030c060503010f0602010e06070f17010b0c 77
    0x43c080104281d8008002c00c03001080c040410000c1a1020110181007041002455001d01406507600780000e0140c844089000300342c44114842000410008000c00d0410072107006031504081612801c00c169036000c00100a85002440e010140a00740d0302d6018680007035003e68a0203442c0b154540078141040c0d001800c0011020703206280a00e00c2c0c64031000c0300c94901016442032441007080c424540a84500c440c10000d51020200080f60101d000c19422540c200307c0d007600c2c0b03140e04142000301d646501d04001075151110a800904d000783c003d16102d01000b0014400201020b10313039a40071003020076400c03a541c110741c04410804003002114203106a454100e80c0784c01d08030b2030b41d4009102e91088400090400400100c1d80040040030010788016580c030840c0e448200c2d8a44400400c40c0d0000d1042811a007110a0000f64aa0040c80350205442030132000d0001030303a5400781035503c11040340401040003400b014489040644e41c1d051400b8043c00385a4507902c0e540707200303001d142007020800 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 514549739 1250 514548489 514548491
    0x6050d062a05030417031512030412060c0f1e0c080903150603102906120a0504021f020a0f03020319050d060608060a0315090b040501150e10180605040603080c060703 73
    0x28040740c03c1f0f04182c5050101c208480c0302c01c482e0b1134080840d007540103da02c0311141d02842d400040400c00241c000c000006c0c0c0079034a0035000e9040840071181c00d05c03003205a1014011800042d5413032880742e00100c08117030241d10310030b103040f05402c00f092515070010070a00c10152018140546480c050101003054a1130744020700207a866400050b07010380310014801510428903001e9000354031010140c9401c0c1411405040c10b500c0c244000308042c10044030124403400c4403845007000b40e0301401280e5400201c55004100c00072169a034541c2516902c00c056040d88428080080c64045c02c0c100712003401d803ea42c440381c482c06030900072070076a21150400010f0191442c01c000d41d0392200f044140840f0382003080783c0300340201c1001440003081c07840805801606240c0812060000c150401d0419038000201107000755566500b4103d0b5050603034007001d008145080070410710109100c2c2c141c01801c1608006030340b42e50365000504032007013036004441c4818082600c1580340b00601001d0743c4105a410 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 514550989 1250 514549739 514549741
    0x1030209090f061002030c0d08090a12110d052107170703060303120203040809010807050403021512090a050c01030f0e07032301110d0207060f0c08100906050d062a0503041703 77
    0x7c0a03110140751541000300003a503070014401c078804006610500390000c54152440421380300041030141480540b100030b00c108040710011602c104212a419003000041103481c10403e5881210103001608603020030065900b203114820788014450301400250701c0002d403040c5945409804d0940801e00c0b441030300c0c414000c000125010200701c900010092030311118940e00e0840648180c0540d4201031342088103468106141782c22340008080c06400c8001c00034444da9060440d80e0748911040d0002c00d541c002c02c2d190071041d402904211a02101080003003a61415540190f2511091717510503641d0040c4540461240c9103101021020802a40001c0c0050181b05500b42064850010341c110032507400905a42444025800214003107448901030000c0e4120280040411400b030b607107003185403d40c02d40050000c05901c100b00c1110406001d11004400c1c5465031801802000c0480400603000140b503281029621008e00004030305880749600d07420182441142d00c006d009a140300094204 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 514552239 1250 514550989 514551007
    0x120f06180f0a0b03030d0606032c0a1e02120312130506060d020d060507031a010e132a0503090c0a080a060e0c040e150f0105060d02030601030209090f06100203 70
    0x88050b6070101ca8102c0209241c8281c0000c81c2c80c6109210b49644802d142480c080340d0340d68540c215010a00c840740240e2802c1c48901041911000b0712401e0000d164131101d5071030001040780c664803c401c041c4a20300001980c054020680703c0c0c16180800e4002c0e003000445008980d003046542c0d03004034880707450b046004610f81d5265581e80001e00610310a4100803001c10031951040342001106920080038002e42c14a000060098401154201c052500700710049465501c43c0103103200c0c400d0024060b031641c000012000c002001444080f14819441c0c00c091034580f6131a4030b040c2d00c5c4c0015030791855528030b001e84020b400c0003181ca00081c441c136240003040000b40b4002400481d02c54000b03200107415050704410918003820181060741150906052900c0d007a000700340348403400c0359024540003d40d1200c414800781c0301c0c00d008541d4444024003a00050549581c003840e403102c4103040040c605010440014501d0508542200c18514054104030740360501d400c1d0750201401500056040503114 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 514553489 1250 514552239 514552261
    0x4020a110d0c05061306091a04020306060303031b1c060b270d060b03070e010602070602210a0c0c0803070b010503010e07050609010e180405010204030c060207080d05070305120f0618 80
    0x34045d078100e00b14241c40a42800665132094420f00c2d484812a51032040000b52100b007490211010382c402d000d0070000524609010040300d01c250300700200e1400000d10100005c800f07800c442113800f0108058000ca5080501610800c8094400c0f0400e080d1901078458090031078000300c030000480d00100b075442c002c00ba107038904212020780c3c0c000d42c0843c110f045540420302d403400950040740c0c482201400060b080b9008034503882500d80382d600b6140104503100301e0112072420030b442c000c45d10104104650f01548140c0001030100c0c45501046540d6641c1e15000d80756030003080041d503100d05001d004000703d00d400d04c10380c40141d4060f00034200452038000022602c0c048c80612a0500c001230700305c0305556544840c41c104000103c80c0000c03681c00e003802c1140c000e40190008441e20b0802000205116000042c1101120031000040803100302c042c4084840380c101400840502c074080c4003504a03203020080c654400d11900c070350002c50346040700400c46103031013000c12a00070008180521240d0104 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 514554739 1250 514553489 514553491
    0xa1a040501081806181207050721081c0b01021504110a0b03010332061914070f030b04020906030f13051c140924040504020a110d0c0506 60
    0x42400c0c0800c503699841c0004440c61111060b00e0f941d8025801001140c56110a0911078a502c07031040f44c518030066070080646208403013019140e84d110190400404010b907a83c50900d80340540302d5071080c200c55413444484e42000e0350060000c41c1d8001c1d03a00a14500307104d18444140300f40300070880c00124100010b522040600041e0402605018020060f180c40341c0e54801420002c0140341d480d0307901c0c20701c220b68201112802981100c010784480b0b254605480c11800d50740781e10064007643c3c6802041102681c12410040500ca48491840113002d10f021300c854030401681d1911941d203c000e4100408841000c0350031480345205000102c0e01e0b44424040d45d030b2006030348500700520340b036480f81a80030b4264400020120300c109002580114100c01082540c00b1041e1204800000065698002402410340458015800c01e6007001110400e0341c404900548202c201c43c0b610b510f440101d02030b40d02501c84036000c030f0b4401c242c001c240c450400001151108038600201825410b580780c40c2c503041c0c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 514555989 1250 514554739 514554749
    0xd020d0c11040e160605040e0a020403020a2d0b130603020a142203030909050703021608091f0c0c080109170c1603061a0103090c051212040b090a1a04 66
    0x1940d8608102e61080c1040028414114243c04031061039917617500034402c1d07210707004007000d44e14401b0104402211900903a0282c80d4004d040070318050800503800000b2103401a0100340ca040c2d5400407299441c3c40700e4078009025582c01d01a590740d80014079144800c10303940000f0406104101c103042483c1c3c0581003461150000c43c00ca0fa88801c42202e80308060080c400050b0a660328410000400d50442c0103942199103420701401035544040c1d054080380224481c1c4151401e8864020300000c07040c000501080400801b081c080070140f0022034074411804220a0100e4a410b00100900080e06400001400403000031310810005541751401c55140c0340c25410300381008500000e20610a005e0b5646202081d405800d201d584e07410401d0240c901009444050780c881e800d41d01441d440780c01100015900040e60b80b49251415007404034034050110209600c4c01415021902e44802c240200028882c4983d210384400703064003000101d044552101c0311002c00a249940010418010b442c2260 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 514557239 1250 514555989 514555991
    0x60108010303021b031c081803030603060a09080c0f10140412080408040b0a052106152b09110d12050310090903080405010b0103020702060405210703050d020d0c1104 73
    0x404440e003c07034a051281580e1440f5141c000b400e1b41413041c0d0103222180310b5038408501e440040b400c500138031b88901c0151440e54041d082240042d03905840c5810042d056441015280d01e462840e420080c20054400c00c0401c0540000124146003e402c0c06030780c1e22072115240070b4441e0b041c80d030340703030088065125126018400490300080074000c174801a0360003451304651840c0d0360000d0020003410f65202040d10245101400d151000b1000c020261a20030340001d80381c5007100c140b521900c64103401004506050407034000b0705076031a800e0107102c0d095240070000f0100708c044251920310040c0c1a41440780740694041c0d2070000100e0041a5007264905140c2040344d038984483c1942e05a100341500040952800c0651040825074880e00103031090303000300d000708000400e00300110241d1081160207035002d5000e0000780031a14000c1525112a8450860315210405004081e41080030550040d140b9030000131200380800d4050008001c0811907182505035849265a12482d00e1032214500e0b00039 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 514558489 1250 514557239 514557283
    0x70302011a0a06020a0f05010204030f030210110313020f0303041a030108070902030601050313020418030c0b01050a06050f090604170d02150408031611011d0f0d0c17040914010e06010801030302 85
    0x40803080d410ac1f8055508511082c0c0c4200399070801030342c3e41e0030100980c0c0049240003040d2044400f1941540d0050000301810702c0040440d40030040c0d0a4200c0500682c1400704002c00034588045d003218088030300d01610442d0301d96140c10074a0f0306185c1541c0c0054213843c01081080342c1c60f03a100c011250700910420030710041d00310600100e002800c094140390002c0b42c1080841d028150844030929807148950403800301603807140144080c400c0a072103001d0202c1c0b0113002c903c0c89404041c0c06404518005809141030507a034454160022a0684501e10250417151000c1c0c0d88076414003034003081420380c1074100540e0500d070f0340e841d80c94840141340040103a45080081142441070040b22411641c2c04020711500d1b01c0e400c0400e402078505a1318444c0c03480741c260000c00440c40450b01e9907000d101d640340c07a080380c035a540b103032039081900e03174090048203401b00404240200184507500704804602c0745c220266050000c403c49000021b802107060055a9004100180c0d0000f18480c122407011001103072 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 514559739 1250 514558489 514558493
    0x306090c0904110405040b2401020d030c0e0913151119030b031b100207030b0c130f03150b01080f150f0409060b150705121e070302011a0a06020a0f 65
    0x314400d043e4a90342c418288020b000a2160700128140500d90841e0305031050003041d5003000d40c850641c0d54660160b0404000908607034081c7d13110001c0e82d021418200c1d00303e440000019401c01d4200d54a0115080321644401403141007100e0321081d40c1440700c10040e401c0b0b41d03111450b00b80941d0200c01c510461202c600c00304148a500b0043da540005804c0300c483c0c5562446890701c12103400100c600815203003502549d00d51002400a088030341020100c9580c0c0c49884034075030268492007032030700414141e0354009540082c1211131070096004d094548020252910380740240e0700c4981210307041001c180c007031004016010411039000706a015015030462000000b0a01c1c0e8004030103215070041c501000c4905002060304880030b40d0038119034510f1410000c0038200c0803401414130103081c03640661800b110360250f1a00910420040700b04441c282aa0641c1d20101036000d104202d005075111031101f408001070110003043e100080360280e50441c100742000f503035800b001c1d030b000c0c1a80501d0b269080c1 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 514560989 1250 514559739 514559753
    0x3010e0c090604120b041509020f040216150603030206010603020f0a0c29010807061e0c020105130308130b1606020d02160f0b060f010e0906041e06050a050306090c0904 74
    0x1014403112138403040c085400e0011075040111030a54007020008121010f208442c40303005541c507070081000302c1030f4a0b9607041c00004e40103181500c0303007011b4000419001c110a032901950b01a40b203540401c8650a40c5002814104180d01150a05005010114900c02401d06031207640c003c0340b501000050b6a410a800070180d4031204201e406002c61480c0c80d41e0300075009580c1607038191011107080e03943d50310f1f04681c150411030502c200c24801000030782591340b20342007405483e4014500141888a40401d007490a41c05501c05c036a03520002502443c24903002c5407030350050028140e114200005aa650244450350000c020016540002c80c1c0e18840c1581e4183c44003c40c00407510201c640882c900204d0311144008141d4a0650b04000924a4502601a03005490040e2b41d05403648501074240021a08040d11455100d9200c041d1051541800034881100803400400410344518007002d0100e510317255013040b8041e0b0000c00411420080000d21030541c4c1c58255020202c50f52a0b092440e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 514562239 1250 514560989 514560997
    0xd02060f0c010609050c040302120705010e10020a06020f28081603020409020703020d02100b0a050f040f1a011103071a07050403060203280b010f050309070515030a0e0303010e0c0906 80
    0x1c180e494117042c0014840010040c0084e20300c207071104801c0351301c030703005440d40c40c02e69200d800e0004030040e0200c1050300f0b22213281c21801030b503401240c81c118103c0c0d4980c402d0b038000307660003444c02c500456070300d0008050b820520072100c0e5802001c0f403d041c41c018001d049040041c080ea000510f0802c4014005101e41c5c111801099501c80444d1140c0562800039100d46040d880c3d1801407040369503480c881d0159115600615100800300c20350940f504090001c080501f10949a03c150b882c0304418580959008184240038805828078010110000140440d510741c04075400c80c1e401440090002608161114009158155034046542d00d55500f2205840340d030f000108100d0010080c0b0160f42d021034601c8902c110038003011581300301c2a03240d40080b655286003071400a5030050041100c103005800464019080c0c805030307041c140c0ca500c0407801c40500c0d0358003042c0d020000400c01c0a450114030840140c0e01c0c4e40320140d440c5501d40a40d601c0c080802074041240140c0000c0c10007201d41e5400115 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 514563489 1250 514562239 514562249
    0x4020a0215090a0506010b040801270b04110424080a020904020d02150706050105040b1e0d0c1a040302030c0d21020328120506060a0516020603010b0a020c0d02060f0c0106 75
    0x5c2d142c40d030b1500c560941a0f0480d200303c0b2165801c11410310214a48207071404103074141668201520601a280e51908020241080d202a00c03140c0540d5403a0b201e50050000052101c601c0385000350015256003c80c40c007640c841c1c08070341c0083c20354100603034485070758540054040b10700000d2210540001400c4407848003494002200001d4003c2c20040c460b04070381e040342c10868081203200c4040c01840394210241c3c45010031054940d040300098900914581d8100340145100100036856143c1c0381210300c4035503540c0c56060004070301001140707010002031203802c4081e10742c5005ca05407070766110711502c038924202030b28442c207600c8070100301e1080040d2200d040000e00560701000d0095050300c0100381c0c84030a82e000902c0c1304040415a4a06e01816000300000b50060380f51040796401164650080640a5022038210320402e02581c0c644024501a1050a40c2283d4075084030350041d15140507034103d10700440011541c03d02684d2060180c8061b03203d6250840e41d5400c0451081d4010000c2d9001 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 514564739 1250 514563489 514563493
    0x1104090506010e010605040e070f11030d060e011d13050a1514070207180902011b1209080105010e010302010e0409060e030d1409061302011106150f04020a0215090a05 73
    0x4081800340000d0014100c440c43c42040b200c9980390a03003101c0c1307407042d4001c86009602e0070002c6400e0910030010320202c101c0500c2c0443c541c4076030240c0941140c0c0704804603240da40c0c0b079040522030f11654a07105401002d044031181310b2008a82e0160b929000e00038a11080302c49901502d006110003405800503d95200d01c20000030740c03a03204054001d10a40d04185c401c41ca01c01c0000304001d000241c410b01340c3c1c0c4910403480800515900c848050062030300d003207042001d00c0c00e0306005620145180040c01e846021032031140500e4503801003844200390720482d0907a0400004210a020030b000d2181540e0b020310f400c18450b03203180081405130428002c0100000c7c944480d0600750517012019000c01a001036042c45a902010800180401c00361030185440c2c1080000c13601e1048130808030036180b441810b02c008100394201c0c0d11820500d040307900c00c55401c0700c0d4840155900e4000c1000d003641c48102c40444c14450b001000a5580c0c0411408500720070051001c580e506900700001210a40d02000b = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 514565989 1250 514564739 514564751
    0x601180e1f050106030f090b0f06060c0102030f010501020c011d0d0807050d080906070c17070204060e010f1806081b030f19110a05090a1515030207030e03120d02071104 74
    0x192010041000b4030401303002900d440c0400380b2032201030055141310b83c0c00040040d6941c440104c540c0c50110046d0030264000c1b0100b0441950031400e00142d4815100030740b802100d50f16010001e8288407403403928604103c2e0030f44180f8164181481251308508080d201c9900c00655490301840e03e108000c0b02138070521a1300500400c0550003545184240b4400c1c0c00e4681507101c3d100c054403030350a29103009040c40000b00c03040007402c1c0d051000d0107507680014008581243c1c0c034658030755000000e802130041c1249015043c07141c51041b00700b0120340094084100b00151910a00319200c0d04944140020254142c031b502c20fa5503001c201881c07840202c84191800860342c0d007041840f10907a42070440784036070100d4010300c5a10f04070407040116840074041e1817803590780c00131500060107046a00200741044540100b6029107203039003070410f004503407001a555600c5043c094105104510702d1440380c1c0c06100070034660340d844015034061550f210000f6032503003030a00e4903034950070010420540103407600c8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 514567239 1250 514565989 514566043
    0x100c09050604080d0e0f030a02040b0f100f0206010501050f0a0e1503090a0606120c05061c06030c0303170115030209060412380f130c08010f0e0601180e 67
    0x810b04001e80702c9645c40e049800c01c0c000082c080910b5002d150309926400c485115405410660840c02c1844801800c12103116010800510710158840e5000009801c0003801d004140e010840180540424240241081a40007451019215008110b0100840d4010440300c9440301c012000500142218840e243c1c41c1c0f01d1002581c0c0c400c0c512064407aa420480c0000300030f030300801103c21080e003081e01c03240c15900b0401801003d9011905480302040c4203c0c010380400c1d010f100d100081e51007036559407100c03451424024120032607000140584401000100300451960756013152241d020708001d41c4802d56000020000e02031540081124028005407608100c0b078080d52501281da0f200c220201d21450303040a07092440d035081e13141d20307201c079041c0860b4029400c0d00c1e070380307a0191000081c1d94071590940e495082048450b030103002d85070344070032100444c140303240521252083c20000814141d031401c031104291201d02c1d1803d0f0a601d5850020703d4040c00c1c180301502d00300e411012035054052547c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 514568345 1106 514567239 514567243
    0x2c011a010c08190516050a060e0105130308070909060b041d0403080a021b030a02010c030b03010b010c120e0607050703061103060f09070e0d030201020403050618100c0905060408 78
    0x5003c07002c071017030804030480801c030301ca2009000000d01f580b4100080d036508000181d09a410103040088130b038009020b440040d41c1624100b070081d01c449106451032000b41c2c02031031342103080940100301d004000005004641c05e1800c1c01036103d401046a540300c0c0c1007520000e00040024020a50b8640d45030050300340c5485014558452450a070b00c010316542c044100c0e03801507512540103824039601403240740c0503500b00741c000f4001e00701d0f0240002d000702c6030740307000404501100380a2040715206001e08010000c0241400741e8502507810503d6030340000384400c4070f0583c10240026080c45260041d24050031024009410b42104c4204202100070b000740441c00b048505514440150341c2d0000d03c181c0103000c2d03000141d4640c00d40c14064100840108120110401d00004103170701c100020b08075001f540d0b80c800000c1d00c0003500108a68056403a804140d0203140800c000c29400c0300 = true := by decide +kernel

theorem cover : BRFrame.Cov 514388489 514568345 := by
  have h0 := BRFrame.cov_init 514388489
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 514388489 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 514388489 ≤ n) (h2 : n < 514568345) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
