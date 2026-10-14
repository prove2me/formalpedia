-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3114
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:42:05.325984+00:00
-- url     : https://prove2.me/submissions/31eabdff-78b4-4d91-813a-c02fdc925032

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 559892086 ≤ n < 560071942 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 559893336 1250 559892086 559892089
    0x3060403113918010b2a0c100302030c0426060103200406080d08060105040f0e0403090b03060d030509041512050c0102190f0c05190f0506070f080a0302070c080c040c0806 75
    0x241c0c418440d00300b01100010b1915103151290046c041c2d00420000c5090150381c82054136901c1d9414402030328403038080d0310b1450a40750f00a2095034041d00307400400600341401c1c03410300003c0f40c034030062a899003e4041c00c1a00d1600d0f040001e24041c6200790b045c004d01e105d00c809809240a02813150354455800c120003480b0140d4009021108100d20b441e00b070300c1b16160b40006940030301c141d80045d45040320035040840d200440c42001030189219070f950b00c2c1c40e26580c0321480d90700c1c0402c0d2481e90b0f02c1110728081c080030a1080c0050608500300030400501015444441c1400c1e10721a17004071042c242010303076901400300a010042901ca02800680741108440b1444201250024801000f03034011250030b800b4130820940c10f074060070000d00364031181c1090111401408040c6d00c00c03c1211980c440c00891981854010781741c1c0342c0e42c088860a207444295030381041d950040c01600b4209a8203000c0e01011482c14003140005110f854040d01c0e600780c17018284000c1e5000c0c150761300280307c43e8a0500900d0b = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 559894586 1250 559893336 559893379
    0x40321020708280206091309051018030c02061b0a05010f0e03040303030e01020d050a1d0c01020d03021e13030506010b07020609060703030f050c0c1b030604031139 72
    0x61004038000030000c3c0664400110700b070040340505074100c07040115082100701d050740100f01140c0581c04403010300c0070710213110b010f440c0d40e09224946101700030b003400006401003003215651032000301360f141040c810902e5004010500101400c1c56846050071030103008081c0308051010004d82000c4c0108417010544076600e10503403100800300b542d580210f6121039030070360503100c80c1d00011000740850b0030001e0180001d05107944a0002404002544010440c1c00280d0948960010307009040f0941075228190000e402900c200300199a201c4000c00c01240084001c00c0c1980c11007010700c0c1d045045081071403030050142c00c42600002c00704582c401695400040d11003415045448640d0b42c0308600d0210302400c01e001c0c05000720b2741030074103101c40302c0300310405001d0b28014041203880780c5415110030b03203980c02c800710083c4d0150446404603010900c11401007617003815003001c903401c0040d962103039648018036030745d0310302d1007500c6050801040300a09620303101441c046a101c403d424651018455 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 559895836 1250 559894586 559894633
    0xa230c060f040c0b0315120f1902010509120708060a0b1f051c05180118020103090c170703030813120806030c04090501151208090904020105040321020708 68
    0x1203060708440003804000108100401810304901515142c1c10125000f031844240042c0300c070701c80c040d601c054004405001a6500c107400c0501c00074003010320b00141c00c04510b40c0201c030a90420004008110081c3c03541c0c1101c01e588a200c00c0200f03045464404041d0a096000e013000d13219504040e0b2100c02c03640d07051403540000002079031060b40c4101900090743c9900c610180e05080345e1591041170301c21201e031341c04648121036202c2d00058000856110900300c400040c41170201441913000b00c1d015521032752101c10090309c10300f04000740c1511040d640d00b0f0105884d0309684194800d400600400d43d01082c8140c02c0b014412040e0703c003102036030340d101c82071904020314020003002ca8005880f0750740400449540410241c000c1201401ca814864080c285144c1c406941d11300075140054655038a5100208040e008031905050281c6c0390100082102e003d04140e042100034400071021488040348500006d10002c4604040d68079200c0c00381c14024a64030140c8290031200c10301c039044440140141c03 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 559897086 1250 559895836 559895851
    0xe060a0c0507050c0f1f020615151204080f0c010516090537080307020301150e040609060b061903060f080a170409060e01081603020604210501020a230c06 68
    0x2403001e00314000308142ca214103001c1c54406c88030040c003952164020880c14000c40210003200d01e5052640244034160020010300d140308802048118070394560100580c0c0c119120385c80051030400507088500b0650004000180701d6550f40e02803001d28518001c04064881d55400c09030029840c0000140f51105140000540d104070750407001022008100103c0c1c00c44405d1407201c44054403042030030303a6600301c170300202d003e0340c41d102043c0610300352808a4000c84003001c1512a45903216035421018012140007101c215840d616a0010356940a01401c1e28102e41c030040d10740c550800000806980983d1301c85201c44010b601c040c0100900800e0504c14241c0000c0c42143c0c4602e461142260340c441d076440340030035902c0d01c0d002144071741c110340c074003070407600000c044806190001411003511505848000d5100c50304002c00c21040043c081d42402185a1001041784090f141e100c0d2401e9a101840c820b0005e01d5000ca1000c4409004045001d0118001e040b5401e24295101c010343e2210b0150001 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 559898336 1250 559897086 559897099
    0x6030106183c0305011a03071a040510020c0a061d100806040e1903090611010b0a05041814010519050f150a09020a0e090a0c1718010e060a0c0507050c 66
    0x700e41c500440b0840d0003150301c80000c00808925048250302000492035580c1301e406007090008201070b01c103409482031201e00c50b0161816260a04021100282c01c110400350700400d0300480c600d654050041000b4400d44e19255062101a5808070300c0c000486801889204510740304400e030f130ba02c0f203081c171390010040d1000911f2502c034040309890100841807801920301641030507010968445003a10440340c15444151241c1d034008102820384584a040a0300941c241c0c1c2c003005986825004828602008202000c5403040e540325040210a44000c0400c1070f07448034113101000a14881c810351a1201200800403810561022104079001030008a00c41010040c00c1c17425559040481c802001c0a050841d5940c0b1384c80e0014205c00b01201c5158403a2800303c0c00902c04480900501030098001da80c0c202c4c98502ca60300701c0243c40006400800407072002c81141510340d80c24440c034041401800001d1800d468007c1c08942070f07904100c98a0100302d410b2000000260300029800341c19134040f140c8 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 559899586 1250 559898336 559898429
    0x20a021b030a05030711012d0c140105091e0102120a0203071403070c0b13030f0f02010b15090910031a0618240604140103050a0207020603010618 64
    0xc0c81d020700e00030090100d000021720a0b0070800c580186c1102c5c102c081c2c98941990165003007403c0b4050600d048251404007556504091510481000e11982e02c52100000789421590159017128402c03108801c040d44010110300300400c03c041c2d6400d240c280d000080d4900301c9094a0380c0040480500201038aa8011020840f064094200360750486110400c55850b407a151000030a03010020030305940c0301d0350b41004076001802c0c0c1c000c035040e000c1d09a1203107030800c18a21000c56643d0341d643c07211400c656a52031b2801c010b64403d0007040e00d1042c02d90100d621850558204021144050407442d00d10100050800014510303207810004880a8444145240d44801c0031070600342d01c2c45183c041e00714100c400c00030b02c43c81c006100b0031000401c03910359000300c8202c02170003882c2c400c6000d9418144400601c004007584a83c000c0f81c1d000540d1035025041181c1580410b0940e0420b8001c2c401103810018400907054586000c0b0000340050400b00d003100c0e111102030701c49490b50340303616558291103006 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 559900836 1250 559899586 559899589
    0x22b1409040204030f03121109010c080703170106020f01060b090f060d180807030e040b01080a0c0c0501021306120c050304060209220204051005180118090203012304020a021b 77
    0x141d0f0000c580000c40100114400c2c81c0c002c02c901040300400041c2840d103100003403008100e00907034035829810784984203c0c0030720b41c44004c00c2d070308220411410802c020348403101e8424500b140340c0c02010140c00804148803c100406d081d00c00035040312400007428401c1d0324059a4407058860080420348640d5641d00c08150000041c180324480c01c4400c1072541d060000b0801301400a18900d4001c6c2d542610030f8820a0070001910b43c0300a20703a002804400100d903821304e855203c0241c401140c1894007903a009996500d09a800c12644002504c540d0f2001304416904039451448002108004000c1403481d0640130b003050001600160102e030380800e0300300765034852a1b201e29807070151722907010120b1645000c41d400783d405070203120301541e82000c0c1c0700c941e140103400766001d8043d00600b0705c192103082d50046860032055015241c8400c0d5034a000955840301d07100039030280010904c42403580c40d64a000f03440c12140807900c076000c2c1c0d00c10000d03d003409601007078030703140443c11040f8080349044490 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 559902086 1250 559900836 559900841
    0x14030d0305041b06230702130f06030f050105040303050f0f0f070e120703150e12180d0c0f0f150e060c03040902030f0108010603030f0e04090c0303022b140904 70
    0x44040d012035000000b081c4150440000c0c4840c464003400320170102c103501d5074500e0310b009800c0003e4005418100d10810350440c0d070031071318403880c17030000005103141d0300d4880002c0400c1c012410f03039039039640c3e03c240014590706000325039008a54412060070b906180303025420480d401081c1380d004070313454004039031080e01c00d580039540250010421b42c1b0948251a0700f40d00c8004a00c070440707018046d0100c240031042d40e400351184001e03644014040418840c1580c503510340c011455410403a990070020781072540c1e0708032103400381c0340680c4981c030354a0300300300c00f0b130303003000515004131402104aa00401c009102d000c181c00d1480701a03d440c2d40400d85000101d602c6001e858101c03000c034080030070701240040c0382e42c0c044e511803080c60900b12501d07666a0f02d81403c0314000c3c00003078009803860060640d803600030070360301c2c0d0b854002a00004082c1e03c141c8580c0c4644083e40c2080b401a0031500c0300010000002200b0400c104210340843c91003001044040c141c2c890010085040e40f030302107201a07040e0351f1139 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 559903336 1250 559902086 559902113
    0x3030d0e070b1b0d030c09050d0c030f14010507030510170a062f040e0106050f190809061e01050d020604181b030e03040e0a020903010f0e0714030d030504 68
    0x18102c0c261650040c5041501d54100d45100100c580715081000010610078003610280c0516510742850103420081071291103203044a003603c1001403144000001506401f00743d11440c090000307203000100c1e00e1006420b40740c0180c00d0300101400c0c18103200c1301d205140d051038216919511421740590008bc1c2c040d040825449000e40a50f192141004a141c1103070009220805e560000482c521108100003c0724016406800c0740001c0c000b0062004a000d00c0c001d06100c07407844c2413607040800712580b0304240400c408050000694900c00d105040d503041080a800072907080c24545500c41c140300c0c105c5500c1c1c05119462040480c84002e0040d512081d0860f00030f450304069820f9142200070421025000440020381c006103a000c4160150b0f100f4400c1d03c0c040513920340654a0103141018103400c06001a0044854a81c00c0001910f0303541e09126014140b158180d0100c0d413140c8901c501820104103a00c901005c0420310055261590701242c6620071607071a04000034140c0b20341c24803900309681e1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 559904586 1250 559903336 559903349
    0x60f0403090e060409171905160605090a080d0b04060603020c1b01030e030712080f07020c0d0204060503011a120102070201021507090312080105031e1c0e03100b090903040503030d0e07 81
    0x500404000030f59004014401c071f02c3c5180350000d0540d0900401c8800e40b140305070304c0084251043c4514005140c40e003100b41c02024481c110f91800e03150307880d41c2d000c40c0d01c18a0b00b440510350b601c0c056804d500f0140143c00c005d020b036060843c28540d1141c282c035200d0040c5100d010100f040d04403d0b007403e0707000340d001d150780e4551581181e884691a103444506c0030403140d601c501280380c1e4000940d8040c48004024440c014075809040080c07840000c0c4100740661840403a070103074a03954040341e252024481c0e40c1c0540004210104400c0c807690600c04030a202d040c108a6590041000c000540d0300000e400c403203020045004195a568502e00700c1d042c0c02c90760001803494000d8419001041d030f00c5081c1d1410f80c0c4080741500d0b9030400c0504041c0c040c82405d40040c2c01504400445200000d0301e10032448141518100408401c2c042d0001034200611000c0303140042d079886401000c035052448410fa400a074000c0158a024103100000341d503800741c004942030081d00c811070985035900901003035005008 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 559905836 1250 559904586 559904603
    0xb090103020f3007090501050f0310090f080d0b0109090b010e060d180b04120302041212020f060a020403110d0c3b07020f0109080912070b030106050705060f0403090e060409 76
    0x20681c07042a20385086100c1c0108032411b10001140610708084801181c0314028001e0840070754030303440c50780034184140083e20311a00c1c02601d000803518441c02400b41071044500041c44214a100150051519810141170f0525149802c14566004030058030b84d50421904152220390044142c0c0180c41c203002c00310160225400c40700200201031610300d00982c811000d40f0a0810810f00850890085100301d101c0f022502003503801040200106107504130203481a00d2103074180f40c41d810700d04039041e10070b8040c16900090802c180b0104034031488a000c02150f07800d01c102708544403614081410b00950031591b128120410f01129200502c80998521110030000d01c04400c900b40e03102ca200b00d614502500402d41c080c1035440040c07251217001a8000002404c4c201c99206105c0d568254500804440c03040f050013107050200030024500801c0c035aa1140d940d0006450041c0c03d0000240510100c0003564040c007001a8002400348240d03101c034040c0c00320305e9485d100010060300c803200d4080c1c0400e4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 559907086 1250 559905836 559905919
    0x40c0e2404120f03140705070b1c1b020c0312180a17030304060b06070b010614041e030201090f06050301030609020414070306090605060a020a06200f0d0b090103020f 73
    0x1101c510f00180f440c0207480f0154560f401048550b2944103c4030020243c5d049482d042c031586400c01c0c0038190004c00304019504031007400e0010b03400c581814002035544555074822412003070781000500d00c2c1c00b0003034028002035404485001564082e0340007000820340d800360003584645407603c8000062045850040c2c4584100d002192680d0068400f03461003420107005a1290410b0011600216803060094a007a07180c42d0301101c420400814500c0c444004010000b030f00290fa102807403107810708040c02c5915600c1c520014165141c40d901080005044034010440d0b0758101083c0c90440b0303080500416038001744d01c0014014010503903110301e080611810f019505900d40d2120041d50040361040080580314401c00107a8014851306200503401820850005105038003d0310a410310103c030b107181154070b20410602d82c0c0140482202e068008110301c003c04030103001303c9811404c03d45806c010755040d81c0115600040030600c4c5805441d00c0c050300e007840c81d2507189000c80c2807030140c040352024 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 559908336 1250 559907086 559907093
    0xb12100b1804080306090109060815060105040b040b030105040c030b011b0303091203201306050702300607081012140d050901020c030d0e0d060605030a0b06040c0e240412 75
    0x4e40007690314901428030030001142d0301084d407003048161801d640042010403824039020f2581840202210704100040c000001d200302c0f02c0002d8406480c01c01d854030b44a40c1881c0c14401264080c4414000701410018110110707600501d981164180c0d5022002c800c098605058001e4942000000c0c141d0083c003441c3d030032440d4541d10804280c000d5014140c48181543e04040782400784c404510300c55500900708102050042e070042160610140c18540002c025426071164a182428840c100b032022101c00b06000d0410f000c4564440a603003031802550524004030400000203018031883c60008003071100c01d1180c0c1c1401c4150030000c2c0d000701d900d9042c40c20401401e503000042a2405807207a1580d2018a2030003281b44030b070741200c80c3d88407601d0204071010011140f281c21020384010399202000720302c0d81c40500c500030480c0c0c040c20b441040ca0900005000458204030901020001c444100c000141e41d10841050303800c8200e400c40d8144104ca4040104074407980d44059803ca001c0400041007 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 559909586 1250 559908336 559908353
    0x13080d1a040504030f0509030c0904030201020304030912030c03050a1e09081b100f18031a060319020111072105010c020f0705040f020d05040609060b12100b1804 71
    0x3000018485014103401509100680d001910024082102c061507900c2c075610450103003800201c0101150b40414451020402c2802e060f1030540050350000708100525400038109002043c4125044101e06019180144031070341014005040000010324a15480d00c200da010139074604800c184043c082d0700c1200684001e449200300c8204d40110000510f40c90b5034504c203021180000340a07080c502c0c05800c001c035122840700590b078040c002180f03d90040c2c0d08520714154003551181c0d90310034000c40c00041c142c60444000b80300c58482d030f0003049440d1510b9070b0030350b0030780c0e1081d42030070141c0550040c4c111060a040c0507130440914504013040c00680c0c0101c801140086e14081e40c002c100380403035410201d880b54100902142103900c6007100300540c0c2001e900ca401081445400107041002c0c90080106640c001e0f14140c900340c1c0c80344d0000c03003400580d100315103c03200301300c521111000100c1021a25021441c25440100380d5848550440c0c0c2c0b02c00f03103203154103e00304190000c0344c6010b20300b0250 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 559910836 1250 559909586 559909601
    0x402031e0f04051614090705071703060f06030c07020f0301060530060c04030b15040207030f1403060a350d0306050f0d061a19031a060603070813080d 66
    0x242ca00c5114064101c9003900d022010980c2c8603d1605c1041881c96014004410780c06400d60b010004104072240220b245802d224030303c000b800f0303007256980c100281000702081080000c54813802c810030031f12601d004090106c0d61100d0781520309000000d10200000e0050940354419078020b045080d074102c0030b1290100c450300c0c4844074007001c8001c500f407602041da501c5e011180010031302020041480828510144a6409082c40c250300f14005441c5010806a0f0403400c0c040f008201e07108000e030200781e042100301d42c0002004801d1421494650000f4628150a1041350108000b044844620714080004412011880d0400700c03c90300400001e01d9541b080780540c0e9001a18061000c9154034007400b1008100c08020310000c03401e21192200c900502d0054124500d4840c0b91100301340c1a195421440300c00462a588160000c1c690700b880d0004401100d00e079200e401c540c00401a02c0e50b03808013640d41051003881c5c0f13980c4541d142c203c01031840c00c40d15000b40010743e02182c0c407890052550010300 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 559912086 1250 559910836 559910843
    0x8030709032001140c070f060512090f0d0f020102040306142a03070305150a08031c0e03040312120203091b0301020a0903020f010e120303012d050402031e0f04 70
    0x601c4003009880c20350510103901202400504d1000085105910407009442095207180548a11542c0c4418105c5040303550b51000380400c0001c691049009503406c240ba41c0b001141016000600b003c07200300307884151005800c428091a10000b102180c0b007541500d000e035601141c100410f441c103440e058026002100c101580307102061000b007069800441041c0c0016248560741e0454072001301c10f5003e400000e201c3e5440d125220901c019680d12601603400900c1200040c5640705401c2d00031017140c124240b10600c00302e0a00c0080666900000100e80803203401019040513481141c40440e0241840424500040d00200a01c540c0c100c000c00c443c00303c02080342c0070030780d48030f5100145400e030302a280c070b01c60105000e0802080541040203500001010500d00038202c4030b44036000444284a0302e490600d682e00c0030006201003100c017500c84000c141100c10794401c11001104621090406000d142e010317640110204854018246252111030140c1402a40c2071034009141840c018089070280e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 559913336 1250 559912086 559912103
    0x1e030708030a2a020304141f110706090302010509040c020c1210180b06120102090402070501050a0b0d0b0a180c140a060306151b021002060f1006050904180803070903 73
    0xa0a0750f21104080c82ea001ca00d5000795007050301d4034031144010301d40c3c9410240c01008201c0c008003070f81ca4024080800106944031700f1507072881005028540040350700b1000501c40130b40c20601c00740c3e03080400e864200c01c040b2400700c0d03144106641207080c01c61540103d44c000000c0c460180e000c80c0c002c2034000904103044000c004d542c000b901c4039240e05088010140c1100f82e03141c0826000c0c180190b813540300172003510015241c00005800310703049034080c03201619565035400900078942c529005400107600200e490b1030701d0318401d0f10341000c3c1801c0906074031411940c44006a24407003a0b124683c20302c0b60040700081070542d981c0000420281d194003006e220750302203000030441c1c90007445a602a5910f0395540322008032a0340c0251140d40500b003558240344c181400800040e610140401c0300403100340d0150400b8241000b100100c0007001d44815618480524244041c80d070002c25102181c104690114120380031501a03020281c0c00302010340481d20000c200001240c00c042d0940443c0e118000c0f1 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 559914586 1250 559913336 559913381
    0x90c06020f0f0d090b1b030a0c1704030b22020904061a09220f0c12120807020c0d140f0304060e01090f06030b060c030c0c010806030606031e030708030a 67
    0x2140c0b00c510f4000381c3c0340460880c01c800d125840f01d1070f020b0005502d900140c0700c2d0802c043c209441c99500540c5080c4001010002d42400b04000381e0307000c1c000380040c003000604160566171010241d100060488090100518070720780c5448088111034641c0350050701c9134075030341424280f11001d01042103035040c40000040b101c00c82d81c00c0841c0c1e80e40c403c40d85200c1c50140004034046208207006103000036110412410810760200c2c00c07910104000b040b03001e02441410303a403490012411036004091009200c0c564041004443c1c010400000c4020102c4407002d031020f25240c2a0607107000081400d030140700d45858800303a040c00000500c10755002e40c030341e5040c480b0004011500d4418600403020081903207001040520300980243c2e5500800078011410003286030506803842d0800d5169001c00e502001e000041560445115a00850181c0c0504610310f440e60210b950703060304140d80000d48210f03421132501d08506000f51844954000c2d06243d80303052003c0d203440580242c1b0100354a80c0070300c40d40c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 559915836 1250 559914586 559914613
    0x3050a05180d031a150a0305010614030a0b01090902030f0108160315020a022514090420010315030501060e0f01080601060507030c0803010305010507110c0114030a090c06020f 77
    0x921601803203100c4010404061210012400703810202510080394104c0490740560350b85610050500800300c1e1204e6440d414032207001419a80b060307201001384850b103c180c1e2140c114003801c99600106040303000c43d444d140030004940f403004d142c1c031080b02d1038404824405440c8440d880e5038102c47c150340c125401c06007d098901c0c0301000314807000744a01800340800500281a801421081d4440e0041d01c4c105a02030b81c0490941d141e400b6200780084800c0c10900400c1d84600c44500206000d5a040c1d50502d425030750121a100302d0540d8541048111032071000300d82c0301c0d40021504100441c803180c13034a640c924005018040c80c0c0521401c01c60050005028450002d01242c12130710914010712141e403800d1000e64450344101030503401c00c103500c00c0100c046041340340218000d602c62000020646454107000385042412140383c01c16400841012000382c3c3d00079000440000220350590303894403103120800081030303103e00082840483d0040007441c030303402290003103150071420150741d80e42e0118034 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 559917086 1250 559915836 559915861
    0xf15050a06230315070903030807050703090b07060b13020705120c0703200405071e0f0905040f09020d1202060f010510080603031b06100920030402190603050a05 71
    0x40101000b01007902c84401c00c0515890180c0c40c602809981d0307407074080b40d00018411300440b030000100300061000c00825900940c0254440c09a1510504241465074018481e403010b20800310b161038003140c03600501480703501a480c181300042240b01014001000c10000e500550819546402522f40c0b900c4026110030440e0407001c410805407070b48a0850741c07245181c031a002a107881c000f40c10a100f0603a6211071085030300812031034403545030602160f109441c2e4520159120300c00c000500303e48044d10381c1c01101010945400b241c0c00301d4400110404500101000a00a54450110504c10082c00861041c51506807020781c20380d00c042d907030b000f86810f40c18003e202d0160404400341c0003809292080326201d421071401010f4038900214509070112104807072340e411078144c2140c0140190500310301e045000400d6051030034800507010a03040c200b520b02000300c0004240c0004002003c40d0b80380800c1800c1007d40c030b215011203c0d26940020010700c03007203a400010034504004a0402000c24 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 559918336 1250 559917086 559917089
    0x50403080d051003050a050703020a0605121b0d09080a1407050a030813050a21021b100302070218040c090b10141608090406060305010b18030a0f15050a06 68
    0x44034145405039003400c1900501c802450464505840072000c00094000e11600c0b8082d8004d800070098a42580100401d400013644548284401006805408901d000140c0e83c40b03002d44040c0002c1d6841079843d21520701c9600d0345008a946880341030802c02c80b02c44060310b00b060041d0381d60046092048100091071183d803001424030352150700458000b82c8a600e81030340c00102c00245000c0070015a03500fa283c00440341c8215030092001e043c2518144034028001d40b4403006100402d00400742c4002e01c80440c200c0c140e00b41c001c888803102401c1050003a01250300322640940310f0074589410029540c40c2e841c0540d011600d4254682c400a0b0b107600c9400f07161201c2200600e003502201d1741c0b54003035800c07092600200c4000c4c20140305084140402c9198100c0d0103000e1200c09070380b500d0540422017160388076001402072614090050100a10302d074256110b00140b15250f5440030a4107001910300200f008000b004d01c0040e501c0700e001c00c50a070010070000c405811090086413942c088120039200e06 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 559919586 1250 559918336 559918343
    0xf06060912050705090f06011d0105070201110c0904030908010c0f05030105040f140c07021f02061807180608010c0f02190212060c21070f050703020c090a0e0c01050403 74
    0x1150300c140a0040211000c41c401840355046070000c540ea1800315203598022520420000c130014200080355811000000d106030000b25143c140d1050000083d141d0302074003030b010b8104021030f4280c4c1907000301004180b0380d24034000c00c0d441c05032409103001886014207024061055081c5031040c42d07040e00a15001402a441703445590a603030a1900303100043c04c0e51255031090984175049a186030480304583d90081f16400d06250f998207c1c3e005010081c416400040346100c009070554074003d41c041481500460010721300f00c4500818902e0601d44406500f00900071350310b122180413040d00a82c0524101d0310a0301c000c1c007210a80703503010b5070812030a03102e00016030086200c48494440003514100c940d8802000b102c000c5800c0c4107494540481204c40100c082c80c0094102e915041000412142404803000b1068501d031000c0020680c039441200c0306c05200003c20100c0c100350084c008503444e00000303403004507039140640d07a42c00506400c218400c142d010b039003880207165104204803000e8980 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 559920836 1250 559919586 559919597
    0x91e02060304060b03030d06080d0f0e0a0e090f0714180702060604021309020708040609150e060d14040b04021f09120303110d05060f040b0d230a060e010f0606 70
    0xd90352210303c068005083c6159241c0402c200c05050a01c5503c103080240982000034082c070704004102814004180c005181841f14003032010145964604051080d5032a5000e09240350b00d0b100c202d02d10b40100001c4840d054050504042404580c014125890042c201d411000c400700e843d6182d24411401e651102c0140c11640024180e41010340007001000e902c05c15a8025564403d403800480e0000b1a0445203214001810800140d02014580103460440d09075042003942c5c80015000710822a00103015a002203007210040c00c0741d07404004034080c14810241b02c0e107840d19160200580888049204e110402d41d0745084400c14100c01701100e80c1510303242c000b182020310310345002d03c1000341242015180c0361126084034484000d00071607070200d04080f4035410480100584104000d0060b8000c42c0f0b80b4000e0358990351003001c411111500001c4003a03245040010b4000c032240988080e0815204803c1c00f8000c014441e0b212a80091004c00200000015a20301c442610064401c2030002103 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 559922086 1250 559920836 559920841
    0x1060909050c0d03140a0203030a1a06030f0c070b0f06043b1c0503070905040b0f0111010b040e2b0206061539010b061c020d020d091e020603 62
    0x1d04210f6002c1182c02424a0741c0500d000702074403845070340a0310703114005030004424416460040e0013010184001c440d0080c02c0e40b0a00001300340c3c68003005248210f0302002d203010074080720840040b00e003140e412964112a40c90000c050440415040e00c0c943d000e54505956014040708414020f002d4821080810300002030700d0300f2070b0480b1654820481e80c9800360324480b860b076865100d01d4024040fa592603142e20307817a01c0322001e080c0700a168860b601460810000c01c9075661190700100c031a0400342410503b054050080c540100808001c440d0020b240c14003288000b08006003201c2c441210140b40d0b46248007034102e61012000804101d000350348080c020980510b00311442d85803564045072514144100031072008400360b01864051644034808101c000d4800c1c55000380409900070000900003a07406c0000f05a56108082e22000070816880505005440580440d80007140c0701034250b44400c80c51801d40010070011500320703030500180b2400c60700c0c0c107642d07410410030380e0300285040d0456 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 559923336 1250 559922086 559922089
    0x1205060f1201240303080703020c07060f1206081e0c0d020d2f0901360204030b0a05090c221808071a0709051315030c0b0c01060909050c 60
    0x1145010070812155258084a41d9400030724015400c81200b00c1d808964051550501800c518405402034041500420200c09220f500080f48811504289450400e0021004044500100d07845021302c0050500400145000000505940414262000c202c0e01001c0641a41d9940c20341416640c124488099505c05451b01c8038110300c5180c001c000603005a0800d504502c2104200c140d400d01505101c0500c2c05981850118240508104035070707043c0e00c0103280c46280302e0444291107049240700c0100740202200164051f1002940d0008541819080c20b403c14000707030208446a00351403003400000d00d20b43c03500221004135580ba908a00503003c5402400001404c07420b01c8801d59209400c82c84400201c00500030450540a050001c1140c04142560f0541c0c013800f5208c03034108400c1640500403640c1d0b41c0a843d040780c000100002c0c0c40003905014581c3ea02d1a944040d009008010000070307481e0401c80244503540c0c040008202c519142c10703d94088500395800038041e5408555202890b = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 559924586 1250 559923336 559923349
    0x4050d0605060d020613030302011d0a020f0307081618050127020f0a080709050405100e100902042d030f1104061802040509090303010e040b15040207060b011205060f 73
    0x1820203080c00c00f105000e5000300b00980d0081c45014040c0c5203075082002815420b109240940580456800c61740f1014800b5a51f00c0e25032940181c411003090a0071440c0e55420010035001300703501400d5802c01001c080460615801c584a0b09a0240400308005501d40c0c4600c1014160381d007040b100030303282c81c0d0450400d000f000008481d0140c980e082103c4c0307040c80d4281c1d010b41550001507079529001d07e00f581c002000808280c0c881c0740074a0400c000e0001085c440d00145007070303c002c0803c02c01c0d1a554558400b4204d1560f912038503440e8400a0b02141001c0000c1c4001380b148141b0203940c00310303041c20305c90080c1c0740030520011300100403070100803000552020a00d001e81c040100701055a58488e52501114483c50007800542640017604001d103080c804401d941c0458041e0245055614205101c1e51800d0028801400c413110840010080d0344250700138141954040e10454580a143c80d0110051400d00c0e500740c0420b000c1c0400c08030403039850040c18031501004d0303d80b50062000c0f0b001d0118 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 559925836 1250 559924586 559924591
    0x30103081606020f180420031906030c060519140f0d0912030f0b0103020403050c0d0c120f2f06090102010605130501050f010c120f1e110c0604050d0605 67
    0x160310b9000c210813401d118100c000b070f1100504000e0040d030700200360010481240e2840c0d80c0d0a5801c2030f442200303a544582032054a6000110442a0076001d00026170000101115040140408503165010402d203601c0b0700030b42400031144100048000582000755107900b100451502e81c02c20403c40c0300c121480c01c0014284903204a000424405115900d808455079001c105000082d82c4032403075078005c51240100111508203080462401d81191203158680e000540e095000d80c86510103d4208124801160001c00f280d070700c074808243c83c51901d117903940d0000381c1c2600d100702c8106540c040c01005401c9603030513006480b60042520802c00501059800c90038916066550383e500001d625140c1c0f148003009513828980014496040104201910b01001c0f035040c10020800211340009047c0d4295035440c0c0c6175424202101030885a0440303403006038030481c00b03d6849814050070801c0c0c0012903030340c584103e0001c2c1c5a402e500e804c1442650b0090b8405c0ca54030804084c0c40b0380c08920340e07900858 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 559927086 1250 559925836 559925843
    0x40c020a05120a2a0303110403030507020607080912061501170a0905070f1217040513050606040b121611031b0a0609140601090612030e030a1509170301030816 70
    0x30281810182d400340300e20043c40014090ba004e000e044d030816134907100b0340b8030703226031000d20341c1c1041e045440c000e02501070501c00a0283d540040d140040c046041c00355030707100b04003c24414000082100320351710345905590015086844000c0c855103980a112054085c00d0761100381807243c0d0f110004040540101d040c299414000d13203c1c040340c0c00601281200c09000f4017a00589161124504001000710034002034032030707000500082c092036842d075600b44040004400041169110319001403058800d9921000d00749c8800a0b0a000a030841c0603418030880801800c50100c140e84a000c0d590f4030358120450f074507a0001c200003620301c4d0130210004000c20b41c00c030499141e0261641d403042110b003080c6042d2000210a010000010410007501c0d0150002d410140049440c25138a0700340210005001003d100a00700704014984040200c5030b08550000b0420941e800c4000110008100b621030984102440c00043c0c640034a222086034100c81d4804043c501d4000140f41c020080c0403408003c5 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 559928336 1250 559927086 559927097
    0xe060f01090e0711060c0406020304031719080a14220f02030709021905041d072d11030906040e06011202030a0605010816090302011d0604080309040c020a05120a 71
    0x802c0e06802c49a0441c400e284a84803072031111030100600d450864020300850035a801080709001c0c803503022007070f50100d96001c090171248041c405026950390084a1846a55089a0070419229580301c16058010b60300400c0400c8240083d40950350b403c4412280402c1120307c00c40700b0380014000840d4201c03400d0284550100c541c42541c002424003040350b01c00744c4500e402084a84001c03402007000d0402c00b11500f0541d1410b81b414984400420600341d000883c104c0040001d40001e0280611407000c0ca801030080d400c6090080c40501e0750046918001c1c000b8a0544d000c204410000086400780382c5c0040155007071500d030000349040500700070210760400042024445400b80240082d5000d502542e901240c01030815000408003440141103c2401a10f107581d1010640c0151541c01602c1e0203291814042d140c0d8401140d0001e042c511143e00210002400103129130084054040c0385400c880c00c0c0041b42c0c0c80c1c40100c0c0c0e91802124003820980041440c00424222080246055113203400d00 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 559929586 1250 559928336 559928339
    0xf30020408070e0a05010f06080f1512070602060a020a17040501090b0702030306100536061b010c030e0319261f061b061104080d03150e060f0109 64
    0x245800c106441d40204103c04080c41440300e00a07550207040d000d8030303009005000305890000010004800a07201000c81c10020010550102c070b5481d003101d400303401601042600c4840d200c030170b54808003441508010f01507000415a0138406000300c80506c00340c0e03074034007041006842c40100c80300c0c7c3c042c00c100c40640d80c0300c42c088001091404c10912074000f907000b0b961207150410902110301400b407100c0f000c004081007802102d120007610b006140000b10000d2a00c104904101150360507203121a07a0301c07134004a101030940c041c07120b801140b0200074009000482d404c4070258192400207105c554190800c0c003c55030141d5000c40b0fa1f403000c044516250701098081c1d2048021220601c40300c0710004003c0381080003c4140c2d00e00c00541040d01c554801c6c91919010009010b031142d201350300403190604001d9024400507401c2000785001036140b15503030320790b0303600ba0550b40d0721922840130100b800c00b401c541141c0d040003405805c035040c160360300c000c0d07580f8032042041140e802040f9906201042c0d00 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 559930836 1250 559929586 559929599
    0xc030218150c01061d060a15030903171602010e030a050a270e010312020a05060a091b08011d07080a0b06061605010b120106050f01082e060f300204 65
    0x6000005d00c00240750f020f40780340084991034000703801025140194140310382080584a0400f884000c44124a000034494200e864116140881030f010401404080d900b8803075002120340314145269541e400070032200401ca000c054407405400f03a031001155060020804030381c05456044070904052410b100c1c040d40308001d00007483c0007a08580d80c0685120014000c00c0b103414084610103000d40000c100f840702d550f44803951900d00404d1aa403458603000d13044100920459130f6100c01c0142000c0134800e03038440b0103407130080071110f40c0c1c00d0707004030380044108080202158120a0310700d500c015120180030394031140b4441070040d101a410140802c20808500d0760320708021903451180c40003003000c0482c24100904008403105650700c50345401c900300002d40d203400c0034010807103084c248640b040d6101c0700100d0f00c04402d014844141710400068400350b0b240601100d066800c00c0c0c0705c0010403110035030115441044540f0460040388203048000754103c1160701da24800009542c05440e0945809 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 559932086 1250 559930836 559930841
    0x306010507080d15030b1f05120309040e0303150108010f030b150310060920070b090a020a090e15090613060618230603060a0b0414040b0a0c030218150c01 68
    0x10400303155960740d04090080100d43c0c0d03103154205d04d44c071f5400302501c0c5140200e11207100c0d07e403164a00c11100c0b0700820f00340d08414000d5601071140100b0811582007101c4181d5180d900841754280141745c84280c1246942c090b2415606030342440004804050440d6110309129002404414011220b403a481490355420803484c04103140c014408500f051400c0e07200030990390382c2902480007120800c030007038981801505031450341c0c0d0881e0540744240c0301e038900c1c2d90600100f004083c0d00032695110114804881d1307040310a4140894080303400065086141a0300c1101c1581c50540907004500441d00038080130030110030450081c2400640301c1c0d0394154004204140f03a040d41e014035121840b400c0b80144020052180400d14690040c1500c0c01c840001e40341c460017410326580960f181c0f00c0d40c9250b01c4551011900b0390442420002c03a090038242030003005400c41d8105510b5043c40070780031995201c1e00940b500c1081c0c80c8080c400b040c1d981020030406d01c01a01c516104002d0911090325640c40c00d0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 559933336 1250 559932086 559932101
    0x2d060f0305010c0206060a080a2406080a0c140d02240301140909010b0604120c0f0b0d0506030703021e13050a1b05040501050927040803060102071a0306010507080d 72
    0x107030000203005510500c0641801c03401400f0700c0c41003140e104104800c000101d44514025800140c4c10710b030b5100c840f039003d4141c5000f801c02d40c07038518152011450010004050f41e405004200c02c1c42040c1e500c2041002c0f401400300e1258204201c02041c90050400744209100e464103c00140702c1e203003800c0c403003030002e40090344944025459040508540d09200358869000710480c0008c0c0b001c500d1140100c0d2452041d0f101303807182d01c50004607840900c00008001400340807402c01014105039511881074003500219500451a8942000b058482c40c0005000040700d9000e8600c400380d494100c0f4641e4000d00142407683c1003181c03402c00d910504124842d1600c6400e9415001130f111040d000c4910200035210102800c3c800100f00500581e030704401501d000c00c0c02140d462003241030300b03402c503070ba06e09166030310a01500d61002070000f00300d1201c010b1441560281d0840c2e402a13555024840c0007000000c0801001c030b001c0000c1407165104030700030400759014501c682d103000c0400040070100c8210 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 559934586 1250 559933336 559933343
    0x6060904110901030e0a0f140f0106030f0b070c0c0302090a0f1803090b0403031e030e0f07051507030801210506090715080c1615060e011403012d060f03 67
    0x102d08405603003610400c0ba010410000a04c8000c0c001e54403100503045010300a02440001076030040180020003040080c0d1109000a00c0303140d40d40e15201042c52401c4404803080068080098842ca100d28641d00603140c211452850302c42c9150240500d40e81d01401c1121a40d032100802c0030109001e02070300c1010310301d0380362400c0d112b98070341802040d0180d40c0c0c0017090100d004110420100b0350001e908070b4070501c0311400d0140030400c42d00a900500d440841603e0600607449141c00d100c0f03011136034208407401598403511403440003251407668031505030001c0211716190300520075680c4101d901e400d40c0c50721580080c10f2002c1c0381c484515001017220180103d40c0130300700034850850a940f501c540c0c2c1806003060380103414050f4090005000c1c0d04400c181c0a03880c0c2d82e580b0300340855405141126420100c0070010b9589503450340580040c00d01501d00d00f03441001c1d144529050501c504601e00c8001c50090f0b40405903c26030403030307418411130b01e9030034191149004100068641c8141004510 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 559935836 1250 559934586 559934621
    0x50712020f0c0d050a080f0622050a0b010f0c110a1d041b0f061107180225050c011b080313060509060c0d0f15140306280506060904 58
    0x6022600b890404400c3c0050100281405541c1c503454102c0007403500809000d00102c2503650705c01c0800c1c54070091018007045100d800140300604501b44e8042d40c018406840f05010302a0b0490066a00c02226858400020001213095000c20003c2d0344140f003607040108080f00042c0d960560300040200fa6044103107004140082c002040000c000310703400c80c091850892452890040a50b480c40070f01d00c607200034092640700b00a103000044c40404043c0003d8801c641c000c3d02a01400c0d002074221001648200d013100021818030015440f00b080b030141c2c403c0c020502034292000441c0c0341c1129170706400300c2003160b00340f58001424440c0918400d58401e10010408512800c0c004256100900001420703001141844814038803030701111102042c1c548080f601c2441701a50304000c04400c10561500981124082074580310000f4211758080105c04440c815102e90303411602c491041402210400181c004013800c10601e40c01c6191300c404001d0500b428207449501107000d0701e1102c01004020305 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 559937086 1250 559935836 559935847
    0xd1e1b0c0b031603060f0b0f0c0a03020c1c05060a11040305060406020d06120c050405090c040905100e07150e0a05040c03140709030506041b120c1404090312050712020f 74
    0x10030004403001044413890107004035481c1c040c0945484030140101d80c1420b100045c01d03520003013003804907081c0961715421540c1e4001e01d420700030b403640d0f0b071001c00350312072a26115108801c29003e440213020a4000307024059a85800c1600401490303450000500c03040e05020000204409101e0541308601a040c0581c0d034010700900d01d800c641c896040418024684441130707005c40c0d1004c040301c01741d900950b4002045c0d1103150080b4030309000d503440c07103074810300300007480d4200500416158102c4040c0700701884401080902c0c10303113802840c060f403d41800c44003a002d4040d440740060301c14041d4068542c0036010340b510041420340728009034a0000c65213071301c041000022540010343c1e11402d00e18018a8090540d9582c6403280c8014001800c50001d01c203585080000001d01e0b54010480280000c000500c140703014031500355188100514040584100201c40c24540204030110364199592617001e0f4969288500510001d44808200310300c00d402c006c2d80503520701c014009194003030b858a4558 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 559938336 1250 559937086 559937101
    0x501060905120307031d060f0414040c1b080d0e030a0f0e01170a02131211040b060901080414070f030605010f140907021504030c0201020d1e1b0c0b03 66
    0x9429540490b010780706080c00101500c0000c8152065070313074103241c039280024140c02c00381d030001e02c01407845601500000d10302001110f440010021600c1d0780c41e00b0504041000c0c1000704440d030050080c00410441819644000c500c039640040082c85485018100805140003004848040b042000103500000d42e40718010341004448096078a01d20340250b512284100033811241c3e80da50500c13b501000010070160603164054503407210284a1954101b5640e031145422050b404c2c03030980b00800f2424511426040078081c1404112011f880c2e00e01d0080c4040044410b101d004005036942806500c0598101009015140052541180300c180403421400c2c25003c580b010384c0580c40190440340304000030030761010755424092048840c40b1081c1d9900000b41d05000704928a440180509000c2008140d04003000600340d5000b07a088500207000c02c00d0640720100340c181a000008841c41c484580d0700e04c104520340c3c1e255a0b044d03100c003004030195605a00e412007500b011118400110801005 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 559939586 1250 559938336 559938347
    0x1404030c0519120f0207051206041707080f0714060f1b030f13080706020f1b01020705060a0b0a080a06050106030b01141e04030b040f030201060614040e040f1401050106 74
    0xc1c0d92081c000040d04401c0c0d6a81d078000a904030041c034081c130000c1c0c0440210b150003070000c1001450040c20041c682d040c000201611201d04480440340508000141c50088100d002903401030703540700300300d103140072610010240c0a8020060850313040c03071445250b00c00f6072400d2011500815040704212507600b0a42c451440003c81d06003032840b040381c14000c0005030142901416001440c2c1c000340190070781c2504103d1861b00c6a0440604480d00001c3e200340001c114100418612003511104c1840541400040e4280e03c034160300501550301c110041408810a544003064660009210004066880f06a9410700846542c00c0d18001da035580100200741e05401100c0c509a0240303800300c441d84046004060324010480346910303682d481c1e240181c280590344101d4003d1504000f000966180034602420a625a00011001035081a9001a28a000d03265411480c4220401e46090505140c0350449250008000f40c1301e040700c40201002184004e81010768920350400040792070340c18540702500 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 559940836 1250 559939586 559939603
    0xe0d02010c0806121501081b0d030842030c0108010b0403083a0f0501050a14030102040b0a020d0f050a080c0c010605040c0e0a050603010e010312031404030c05 70
    0xa590418402149181c1d00c03606150340807400b1192a039003012001580d620b48001603c1d00251892981c1c00420b03058800684004009a03000c41d1030090740d200300c1441030303c100c1803400802065050000c6070310038402214a522280c558080407100100c0c802500d4410450041041080700c4c041c500f104070b40c01c092000c01000282801c01e4103042d49001280d103480d100340e20000d061603401250409411203290030b446005031803941001a00d003028440c0019032406006010015498080c0f0f43c0003060450141d9070407a08010304240b1194584541e4001c01004024903545c1554204804140d001c200700260a001c00d00d40c0c000d1829000c012000b2380165480c0c0070800511106001220304281d0002c00c5c168000c085c2c54026840e440200340c0b0b40d000d8803998101d1548281015002541544d00c6240c0c400c2814040b607403046030381c0d075031028018144402e0081240d0b4040079001400458a40c1c002c0e9108050580380000d44000c1e41c1341c2201c81d01130196002c5000032003030a01c440611504112082 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 559942086 1250 559940836 559940863
    0x901060509190f210c030b0106030f270606050306010f0515070203120a02160e07030c0e030a060203040312020f040e0c03150f01091e0528051507060c030e 68
    0x1260781020400030440106100303103000c281300e4001100303e00c00c0d8080c040c078074035502944030b401c007684a250003032011909001d4000001d1406042070410001c5026100d0802c000f020000e1441e1046001c2d04000c008110007910040c0d2a00070004098408004090090444a00040071075042c9420043c451111801d101480b0b007090044501694001c0781b0b1440c41242446000e554801da190203904000600390901134602c41d4000020f14420f40040b018851030603694100310100e42c0d080e0948074078142201e260f0305513200c20700031b0303000650b664001c5400134003a080c00300004249815000903a440b1030302d12412003c1c042000c101180101d4003098104c5032140c05c40c0d003145032881048050ba003801120381d00c603011000505003c1d901603500c440c054800c81ea280004180a80c0e003603c0b00642510485000b035400308036020040b2101c1100c88220440c000c0c6410740d103440c140821400c000e51461840b00c140080019400040b054401c0c0300302003d441e00c000c5141c00401c204503050003650010301 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 559943336 1250 559942086 559942129
    0x40b0f27031b0a050705060d0b0904060b0103061502100218100e03100203060603041205040801180b09070e0a020c16080d0909020301120609080c0303180c0301111605010b0901060509 80
    0x280c0080e801082d85c4003607031003c1e44e050351181d98a0382c6c4103003d0301d607100750303250480c000c4410b00c800d2107401d4010103d031030740a0324180541e940d2581c1c05030f00301c03046040c1100180c010030040c0444211540042007080e40102454039001c4000e80040d180d03015400c0703424081601c41c1090300d42c5080c203010043c220a00b0007821420b614205010031010321000b400217090304c6500c84803e0703003180501d055601610301c080081005040001c0640d00d2500544010f0350a229004000b44118100292510584656021014164545100c8280603400c0002031150901410b121088482c51a400110040c0948001010f10b5024000c000d0040019030308880c071314600420061241c2009000d002c0d2155501c180001a4450242008543c03405039240584441c040001031201503061480f0308103640006030183c507003c1e06140d08145c2250100307801c4075010b044c14030910117a65011040002c9450145001180d60302c6120001031a842003600944081800070a0304001400c1c080c20310301003084026102c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 559944586 1250 559943336 559943353
    0x90e10230c0a121509051003051c0e0910030b1306050a0b060414060f04030b01030201080114130c0c0228061d04020708120c0405010f0305040b0f27031b 67
    0x100f600300303140c95040d000da44907845010b400807110344c04801044c0c640e03001c00c46403c002030b840001413000d00c410b54051048080c3c90503510710000c803120203c16603440e4156402114001e1061100b00244002036102e880d20001002c04d0030041114801c3c1840c46400300e0b080e00030b2500c1030032148090803824425180550300c0006840d1402100c0954003c20740e240c811f10942d00005002d841000140360201c1000300740002004106030300c06041ea4802d0303d608079682e80340c94002c01c04043c5407201981c000b01c4038110404000859102c0035010711245410b4891403125004115101c0280980d40340d4503164882d58007544480c011500e004d4401c030300e4400720201c03031400013807000c08240309400d01c1254000343c840d0803c80b80600701d0345514814040000039141143c1e440f20150000c7c407a90340402d40c0416403c070014482d02c200c51003607501c9030106085444448201c20300b850700030b208030713030141ca80c0c081084682d0315940020781c14401e000007996600c0201189441c40303088410700c0d000d10ba201c884c8 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 559945836 1250 559944586 559944607
    0xe0a0608040c0512120412052103150f060a0206040b01080a020303070602030a0b0a170d093f050109020a06050a02150a0207060612110f0604090e10230c 67
    0x20000b048035001c0b50700d0404100403209450900a11001c006040203000400103114481c1b4003500e5a00750140301503402e002c106481c1c0700d848142c3d106034090800410030004181d4018151117060b214000341c040070655100b200400c00300c1c4e0200b00c0801c0540c0c4400100403c00c41c401c101c2c24090410b18025280c01c0769542d0100c1d070380b0701803280020421900030000603d00f8007a40e2181206201c0200b01211441d0341c1c1c0b110110903440f400d21260540220b01d1101d52440c0940e00e64401c031380c00f18246449298a100c04420011300c2c0149800c81100c01d03e2030030000f46070032000401941d010380c1c00003030304480300d1040000c3e091142e488101070250500c01415800d4000c07034084010607400000a0b0f0b20307902c00301820001d1299003030080010345000400701d8003040e101c07801000c00b80f10380c8400380a010350408000030300e0008260300340c3c0804104400d001c0e0314541e8001c00c81d07491000c01140c01c40301c8190314000c203650810040c40d00010941c007501d01610009880075400036128101140740505420 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 559947086 1250 559945836 559945853
    0x21090306071b03121103070f0f0305010605040b09010c0b16030e0d050405210111180409080d090f0602160209100e0106050912100c090f05030303010303030902031504030e0a060804 79
    0x400140c14000400113580d03200e8076640020503402007040400d80d50307162505014103450390013185078001940103800d03128185c0c064440c00d816180251222800c0c14608654041d10b64416450700303040001581d2008000707440301e480395010790400d50710300c4804107804400500b158a003c40c420803940c01400940700c1c464000049a003920f50944181703210080c10440106030021045031251150720b80b02d0006806101900030f4140390642c5500700d0f6599451104020540344c0516001d00303140d501304008082c00725241e01c0141501e00c901c520344140c10b541d0700c92038101c0c0c0019170003505102107222a502140b0f4580000d035440445101c0803442181080c0e80d5682e0440140260b00074050005130f03c0030300381d481c02c0c0440c100e610844110707510800d2000020001c1c01d07450820f980490b0400001040005995910b2020303500080c0040d0700f56840c54030b04034094054100d050340c15016007020170501e026004c903558803482c02521092200c001c1c00060161040140e404401000900300c240000507100c40b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 559948336 1250 559947086 559947137
    0x100f020c0307230a03080f03040c06082412070b1e0c060109091104020d0e0607050408060609060402040807030602040e010909030815030f15270a03112109030607 71
    0x2003c0c0f080d1000902e00411340782d0303013680c0000d04240008240e4106040510008604c220300c60800c0118007a43c1e20400e541d42081607805207524003816040c01c0d00303240701c4c8907641c2441360010300107120309141015141c1400b0083e04820714040c000175402d061940510b00c141c1d000030088124a203001040d041598aa200600500d0011500c804d003a5081c02255031b80c820b80640000c200319616540400e000e0700405c2c400804240c3e602030900010a00d034050003e5408880c150f10240c4056a618001c000369140014445c60b40300c0da00f8040800c6c4050701b00224006188a104010380da103081070440020b4041c142d00c540c00460038400c8c404000f030b40c0490080e8021004c20a400da644440c540001e080a10303a0050b015184134800117581c025680e071803250300a600050210201c2c0c3c80040c600c020103200000b2050382c5601c821b1814001903c214100c44102d030207101544d24048590b980c0c00380807455080380c0e80019030041804541440d041c42400d030400f003181003644100008510300c80d0038500f00d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 559949586 1250 559948336 559948379
    0xe0411030c1815090f09060a0506100e0a091e0510240e09190b060307020703080a020a05030d060305010c03051501230403061b0903031715100f020c0307 67
    0x5075008a103103030f56030100c141c459000007080c00350907207040d80012180d110200ca169126100748004220850507504c5128016100a0804041c80c20040c40560762030f40a500466003040750030a00040e109107038452507045040390f600041700a44074080c1d000645501505d09030b400d6404440c20824140e6110441540b05901000010003040751a029110600107001c41a0001c90000410201a5500c45042c40304035140302c0400c04009a43c0130300c58180411035600000d030348a2038040c80030650080241c101e2070441d2044507588106655481c2c01c0d5000113031080c144586402052040250a00650659098600e0204484d05c0c0852895002c7d056010010741400003114441d0041800041d41a204208a1a05503519a0b0f02d00e4010000c0074001c10142d01407000b060317140c030080d00ca50f00c850112a0103580b10700c118161041c0030304510b200a061280b8200300720501c0c0b240c3e40c403072880d40501c000355521080c2c40c2100111001c0d040084c1c1c4001d280c4281c0003408240000050b400c01217880308070 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 559950836 1250 559949586 559949629
    0x603010306051f09020913020c151f08150a0c0801050906040f060b1b03040810021602101107080f100b010215040b040c0e0105010804140111040e0411030c 68
    0x3030303a804a00f901d4080ca100b0b4001d046400e1404142942503400421110320180c0300c0e4030070b020318080e205c0200d000d0106007071159085481581114030b031000304140c2001c0f89d03800101c5070448103a4441d681078403550184074103400018012251800340540158050002d2000b800010f20004006210601c140203ca200da038090011a020703884942c4003c00d060030013102008100d442e240e0a00e4a900700c0710301c8107001080c440c0088802d00e0088255011554103400800c2c100000c0c0a25002a41021000d68102c050710003030400945d0325400c91820b1075407540c0707409025403480c0e840303181821510780010040d5401913041b056240c0c03000808020300d40064500044084280004030308002d4085008650446402f0612080c0012402e0907070050748144004034072a0f6440070301d000d00150034452540401d01050008000c2100d1a2800c2e42814442c1d0000a19011032069103540360030907004828146000003c000410000c0040308a00490032401020400580d01c0082c1569146140c1e90144c1c01c07 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 559952086 1250 559950836 559950841
    0x10e070e190c02100c0905033d02090409120e030601060f05030606130e070e09010b16170307022808032e12051009152a170106050306060301030605 65
    0x14800d0100f4420f84c0590b00d414450289102c00c02050380364907010b514807a001c0c6184154806421200c0000301042c020070401041d0241801d0b883c0e10a00a560f007101180c08005c0038030300740e55134410360030894440d0102c9010004c001d04014001d888070101e20380258012030061110681101e001c00c1c01010924281342d0300d988031000b0480500a00c43c1c40a09085141e00201e010500442c105110314410b6581c004000c00035010000300b80028490308102171000c1018a040307d0341d2242e4104114080c1c0c0030b2040308070b102400000b07594800c13500ca10050300049200b502c0c0081c0200c61083c81c000842040c0794036681c5231a2205a03210103001d449840034080c034034111030140c2045e000d140382c1d08000317802c210680ea40e0b01426a104140c2013140c42c0d024080d10b0805c4078000d03201d903800c1c0627044480c0380d40d1501032488903070051500000844c0c4080a142d02950408400c50310050700408a54a40890494000409041d000181c1084091140a008008280d15100c0903241103030740000010940d078 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 559953336 1250 559952086 559952111
    0x20a030c0804083f0f100b0901081e0a0204050a0503060108100519090c03120215040602090105071b0f0b0c0a03031808030703050103110418260c010e070e19 69
    0x4e00d001c4030b82c2058071002e560880001c4940c80d841d44a007407a110102d0559482c000e2440c00c2640700e01480c1e00200050080158070752184406580c841c807094258542048046070303500c588501142c2120101d60009010b204a0500c81303070490041406a006046a50402c01015101c20072070301c1d40070708950307103500050700c40110002c0341108801c22181001401c80a007412702c0c5c8011640015521044680b6007052a140300084441d51710307040c414804070701c0d11a940c80901940c03140b821981040801e03c02d04002c00d08168403000d0703191101104003041840c2011004800d1b00590100160b80b01c01d2014191651002c00c2e58807440364140b0300016070094481c820410416540b401402c000c82c04070400c80c90070b41662040d41078902072100304684d8102d04081205951101207407040c64100c0c0c01500700021070441d29010044485a042248566608900e15064010842a03461607444030154074082d0424030000000e055580d07074030309151030001c000000e90302901494100142e6030b008102d001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 559954586 1250 559953336 559953397
    0x3030806040207020f10080406050c04051e01050408250b04030b0403051c052d090a020405041406070f1706010e06030702011d0c01110307052505040609020a030c080408 74
    0x418100606c03203000050b20303000042403028229001c880ca03d1800c0c0210314880c4004003a5012a100205004411004102000041c510130302c1d1642c1403020900c00072074650802d1100c12402d09800d1005a46440c05440100040c070181d030040304510350803c81480403c40c0b00c0c10459100350982405661443c030105071030314018013031500c41a41450102030040304420f4040700b440d1138000b02e24461150f1905107011000980030340d101c3c1d2459000c40040310060400750055031707100c0c2c05802c1540303001000440040c04d1100445507840020408449045c0c0c140c4c0200040d40340c00781942c1d04000d1840e14038000ba0040d054104118450301d03001c800100e91500c00d400c050710b2010b40034108a14203080d61010740d650520310209a0108031101c1e004d10741c1910000a80740c4d180c2d080b030000c00381c07149006131040d0b020244024004507500071040c0414036403524014030303000300b8001100503074504c0d514400034122540703031408900300700c00d880a100c0482e4520081e07031004490329035148038401081c500f4000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 559955836 1250 559954586 559954609
    0x110a06140c070503010920091014010c0501050f06090c0a230904090c0504110c06060d0c0e041a06040902030706051c140406050c07030504150c0b1015090303080604020702 75
    0x2d2540c2480c10751000c201f40d588918000911003801e100124000e00d00300800c501003290742180003e01c0c22000c00c0042100300d80c00c51f10302c0b81810700c410780c41901d48a681c01e6500440c0c00d10a07120b442c9080c00014180309404035880607511400130300341469000020700d000b102c403010624500c0b00c90001d110705140f44040b0340300d558005208100310301881c9002842001e50b407148512503484d1a004007c4510300500b00c85050505e0f10181407699110350800c0141104030806036449001c01c0702c046050b00c00c1c00003150045010b04804003042040e81100a4980e40040c082c078099402d140e02400143c8001071400c00395078803410070685034103203001910310140c0c034003003500c0039503003424001e01c1714040d10f442c9a40110b0040000b4030803661001c540032091300c01e01c80001c00241c001c200800800c0b03500100e580340701c041441c1c008444178403a1030f9034800c07000540340303d40030303450b040d0b0308014110319036000182c011441e0810010803417a58078081d0072520010312190085400040300070855071409903510 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 559957086 1250 559955836 559955839
    0x12170406080606070303110c0a0c050f0a0330030e0606120a02241b01060b040509040602160204051617071709010e03360a061b0b070c110a06140c0705 66
    0x41c1c0320403c0492311039882c040c4070020b03908000900c0d00481c11b42040c08140c4400540501040000da1030740e030314845580f0b00202001106440c07250762850b115514040412a20069036002c00c000303501100540c1004805810144500000160382c503840501041c0c5564a81c3c0468108c020110030074002105940c03009648220801c3c00941580000c00785c5252174000792000008001881d01c07844900841d10481c004c1d1765011070701900160008a0310b800402c0150840603048441054550205041e01c00698041d00744000c0394028900d8660300420340070720301c07400002c4118035040040303001d81a1307410031516030150070001000400d07461094029019581d0000d0840f5500c616178091044181c104d0f0903c0101508046001400b030039110700000041e840040103a403005250030802e4075810792203403009545c09954940100451656035241e880746d059a141d604a908041c0b60000103ca401c14400348130316035415041c01180c0d0f000004610841c0102d04d01a070707910f4450a664a041070700c0d488903 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 559958336 1250 559957086 559957121
    0xe0702010e010e030c3c030705030a2c1e120d020607080a0b1507051e011a0301020f04050d0c0b04150f020109022404090612170406080606070303 64
    0x400d10a00000508020345034405032100d48003001c81042c95081b0985095021040030a01e90300e0058601661b8080b540501d412645800d00d41c1d6241419504540701c0d60713000c034106150011480c13001c6003030180c03900b8004240029090968000a000450140c1c100340400c85118200a551319405452003200a155084a400442071403000350f4900f4120303420800038403200007050404160b40156020700800914850349103000c48114540398011042c140c070103115210078400d003404a11080c3c070200c03140600204106981094010b80040c02e026164040d070310411988a1110203031050320190b0b502214421110041401d00d0b00040c117007600034080000c0001000038260040e01a260850744441d02c03070001c000081d0380300741e01321440070b607001e03410038081c1000008001a041026007000110340c4441c1c00c00e601c1d0901c1c0380480744c540c2c0115419480c003001000038400c1e85040241303011600041517150506010008000c0c2d040039050700c1c0104c4022800c80304040c080e4110306110031684825 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 559959586 1250 559958336 559958351
    0x19060b040f09080a09050d0f1209150314092107051c09050901050904080a030b061309020702030709180b06030a0b09010c08070207081207060b0405040b1f050a0e0702010e01 76
    0x4004641c0c4032421500204205100000b1b060400c0c948001307a00d034004210fa40b80c00d00c1a01c81c0c9040c0c1010700c031035008000801401080c032425082c0042042c12842c0d070001a111009041841c58101c0540309041030350200550f10903160305d40c211916448240c0d40c2c2944c6a010300e1a1291038110b00c0b100542d10540c2d050000e444056100b91070804449040311f0040090340d8590a0000c2800c00f920090401d420401000b090140280c00c10081050040d106a280040784802e88641301e910b9003005c030403e0307000034040c03080d46000c00401c8040c01e810003040110b0390440c4440745c1100418034004005600f8940040c02d51364040c00149041174202840b41d10601d081000c190007841b0303c9260b10003154052001c509001d00c00030311041503500781401040d6075030000f14210343c6500300c084102c40164455036003440e11345960207100d01070f80c403031041c0ba0494100003074081c3c600c040b101c486080b28211f0302d0b01000b0554602d4460401c8a0352084540010740752214128090440c00f0245070456003012230 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 559960836 1250 559959586 559959593
    0xf0708072c130506060906060d0e15100e0903030c071b360515010309150e030406091202060304030c0201050c0a0507060e180117030423011119060b040f09 68
    0x103407800741c503c6603058032a140e5a410401068500c15524590803031030500407440d074903010b50300030b5000380e0400c03003101d98082d180784a46555580841d02103c1a400301300007000350421084200344c001004101a50540c60504031546650003802c1020740701015100e4a85260b07441a11940c01410310014200014904035a0f004510f036240e07860386254941728200d2803c4501c3d0b0f84141030181d0403248080c1d51250f050001100580645001525145ca00c43c0c01d02d200d4010a10808803e40811000b45840707901d4130901a02e600130561004200c2d031310343c840100040c0c0d20302c42207039409a450304103500030031928001203e4600030f0409000d6139200b40305000c4188400040d824044403078950724a02e0b0308240a062029400300300b000e441e1840c000d02e00503c0026109003c101103d42808212400d11b40d485c083c25000d10031843c1e050f01c650300c00d20f4900b80c031560f01102d143c018001c080005d201d50707042d0002841c060700036400c0113400d4507541d0703080a0341030380c6503005550284102d09040c0302c1c081281c00c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 559962086 1250 559960836 559960861
    0x9060f161208090102120f3c0702060906161407030206060423040f03020a080d06060f0903030e0108091002040b1804050106140304030302040512030c0f0708072c 71
    0x3007160100d03402000140d9800014000c035500da84d0301492070311460300c80c51505d1101e50703006012a2914090501c00305580c82440700000c2000c03c1e100c00361180c1040c41c01e012100c0840161004023150402420040c244600182c0c154000740c3c404406003c0c0303c441c003001c84041c60000301c4c0607200800000d415080c503a001606501517002210100104405026103808000c2a030f1021a0f042c003c0c07500040200304602681d18049010380140c7d184000c940c0d5134447c180c0e003e082c031092601c0d034800050200c43c1d84164822000c000604016008904545015001a04108526040105000000d04580710a005125001d01e070030b4002e544460b00c6182c8155540c100e000ba0151807100310700c0d1014a4a003078007540d41222402c1e100c01d400840c0d450240001e81c0d10041080e010b140c0c00304000515520f400d80d52100311041d4501a60b255803501c2d88107130416661158a078410b40c4855410b211004000ca00401100c0d8101012500005090090380a00d40c614070032002070041034080107080c0311100c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 559963336 1250 559962086 559962113
    0xd110718050403080a0b030a030e040b04110712021222080115060311040f03020603040321090204050604060e0105120a1e030f02070b0a0305090a1202010b030d0206090309060f16 78
    0xa854401a45d40c403c082102101c0340c01c86034541c035034003101c9070b03801103800707004407041c0020050704c04100c0300410400b007400e03122106a43d40400710f00140030420f010a40048444070100e501c00350682e0041c2c50744408003802003c0c140b01100c9002e0801c203842c0c0354005070320b40c0203211040092000410445010f50126032500c40c54000c64100204004402130200403075083c1c94104d041d08680505503000d102e0113820081044092040b0708400720a0000c4444003444007030380408000c2a149154030500003640c0c4c01900b107501560500c402442011088510a0706462042da000032103403540b15003c40c80e00300000d40c0504101c03e48000b81c0c080000c1d0401c40b020140c0a80c5032140064001d42c412a52401c09100d20b0200003002e0240840051113904101e0b0402d11000071103105400f40e80301c003607031501200c10a02c0540c1d518060f1082c1400d0900c0341c15412000c07400a0800c600d403002d2450341b07d11424050703900c103110020320440006200d1084d140c070019901c4070440d0a58081c9880c28104092 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 559964586 1250 559963336 559963343
    0xb1503070306050f100f051e040f09200901030908072105030403050f0a050403050607020601030c1401090e0a021603180b2508270a09020901020d1107180504 69
    0xe00c500803c90313081454a104010384003810080ba4081c11180450303e510020506404003c000c00003800c0c0b0f080c9241c0f1080201c00501a0305580b0752030003080d14007580317035540030030785150a040764106000f212600c44107a145290607041d50b1203200700d004034014013112600416204001c1500c80034458035034102c0b03204105400f40c581030341d940b104080d103260204035001070015508001d90518804058090002c20141d81030081c10192a541ca0f281000d20860f244d0005070300c140010814044040103103030041a00789000d4150a11410009010101034021416404000d0002c04c040b0764140c1d04441041c03841741c1d42c00c09690014074005010058111400c07044105e0602c01180c8418824201d4035280210892001040d00042c0c82d80c0b50012444001c4c0c90462080c410740501c6d1200120207a016040da0b40208010014401004600141c2e034108840d0f03030b132051001e200e0382d90b0009003010500710720307090945200061410b61840c0421a81244203045a040c0c4842d24000705900424059480f = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 559965836 1250 559964586 559964591
    0x201121a1005030906040f110607030f08010b04050d0303020f0d0507110c1e0d02030a0803010f030c1a03180a05010914010c02421510141c0b15030703 66
    0x1590807180790000380c91300c030803079007100380884c0004540c800c105e12801d1290107070a03104074202c00040c5c040e0300503d40c150040756101007012081d65010300c1e0180580b0208039081d00345400c20011542c1000760060040c00e040e400214042a2181001503404081c0281c0041c0554680440b004081c0c42211803080118803c1090a11304e40c58815a9603420000030b40d00d1001c14000003041082803421160281e8041c09800004030210340709900840c060315407135440c0b81c0409e11318908000313182c03c10761214008608030b108a545a5000108880c2c0200780107019208030381405039540e0421082d408010510341c0b03049085000c00c000d10100c502c0032990030000700f10344a034a010a07600c4042c2d14000d1060940c41d502c2d03d4100d2441000300001c12140804481001c10356491004013149041d03c00e1100300c201c071000c8041074902101200c050001034984480c4c00422101c0c40622405120074141c1c0035440c9845580e8411040e40c00703480b0710500140006e4540180b0b03980610182d0084e90210006030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 559967086 1250 559965836 559965859
    0x10f062f1627020f07020d030e030d0305150d15021201090b0f18071101140405060108070e0109020f0d020d05010824040b1b1306030b0901210201121a 66
    0x146000140100361812070000b0030295401c4450000075481407000212003841408200b000da15085090240c46101791200301d04206101d08142c500542689044100760411080004490a44100e030040350002d07920395a50242038a0f00700607803080541901c605501c0890b800e191030400c80c00c4503040342c0068004020240e51789082c4040a200340c408075400c0400140311b250b590f0362111000d03501c1000343c03420000c0021107100329425108501ea4508008490600348070910005000c0d181c01000d078500205231b203a160034002110038005104e0f002c01d603503000c00c02d80364504401d02100d8840419000440d903504100f80200000c0c802805214042d2103007004c240e558018243c0010442804070204428a50356969041010308008080c8203840090001507040c2108200240141101c41440c42e40318a00303000d4001c080300e0319a182c442c4240c0c1c4c07a00c01002154603503111340f00402d02e450081c81d500d09643400103071442c24503038601c00e129500c0c00d40c00d03511000007024280001e00040b1003400020 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 559968336 1250 559967086 559967099
    0x30702241c0c09321002030702130b090c16080a080a0b030c030c09090f07080d030b030c0906060c070503070f0e011d1602070312090617010f062f16 65
    0x14a4034011694002e00c501d0300f6039078044c0345041e10760000303000003010020540e14a021810201e9540014005039002003000d10440c0f82180041941e81d2964504105040701c1e81c3c005400d20030013500c2c0d4006000c000815110000004411b050b240307400044c0640d46007100708005101c080126480c40d41280380100101407881c01040007040e91100400070580020290700b00280300002070824219442000859a0111030030b0101c08000c182c0c0303502800032408240c85c061706485aa040c07181c0700b60004c103000c000c030f5511603050710303006401555001d44581c50101c10b689040c9903034209039070502c80d444e80081d82c1d1140c12440025035922100c1a580d599840b80a1141c242207041340a01100d04800060741c0d03a1480c07826429403030383c40d2044900b00356580d203811104209611050000036540700c028802c40b41c121803280ca802d906100e00b10040c1d0324184055044407800e026820805c140fa144005134030013090121181030001c8200702511034a00c14510b5560f946580300e19003600c5c82c031140007907407 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 559969586 1250 559968336 559968347
    0xc0212010603080301050f010e04060e0f10030812090a0c03050705010f03060e0c0901021c03060e15030a0809031216050114010b090105090a03060504050708061305030702241c0c 78
    0x46a80c80f011013400d590074441040343d18195445440d04100040c20502a00c2d40c80d4003030a4020030405841a0490a21040c03029050300002d0083c2e41880201408000141d051021100c00c030a1442c080b90168a59844a50400d20380741409002c1074002e500100600601080c4141240c000740c0343e82c0380c2021341c0703d010740030f8800903c5041c441012032000a5041c218040007003080e4541403050320491042e1110000d4099001403070140000c0e6030303e03420b000d6001000764080c0c10003070701c40c10014000804d0001940e200c01c07455004028041c04a00c800940e1800c018601030000710b0501141c44209550300d00028501c5601c0545282d800c15800c80200410b002d0002c4c181d8050400032440c01080300010355003540301d001c0907034106040c86000400308049108143c0228070880c003901c059454201e1542c0341100c060681051050407003905400100000201d441d8290f041e119803007182282070310510040c50404182c034050030001458078404100f5044110f0480c00d03180c04104241506204594 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 559970836 1250 559969586 559969589
    0x21009080d020a0507180212010f080c040b10030f1d060603010506010305071428031e050c16061d0a21080712090212031c11040605030702010209100c02120106 70
    0x1641117003009110265001c1c04040b25030b5241c400c05032501c00c50001c84100840c0036880383c0c2c0c030503e1260781031104d81818032040805107011101440640c84a00004055958000301c1509059650000c400e09407080c1e00002c0411420340d07c910f00d000c20002016403a0042242c01c1d505c42e510345000148998043e10480e4016070309503503051099161442c01e20101e41c410320b4481d420b14858503901d0844500112902c203010f0a90340c020848400c0619400390080b02c2000d11271400d030914040021480c0a0010703640c6407109501c841c1d1801015090030303002040346c502002414403c500c1c99008100e4001a81508244a10842100381402c0ea003c000200c0510b0641c40014542031302151500c2e01c00d4070140000040f59a001440360702c41d900160b5071081489030f0f00302503000072900584840f0890075100b0f94003000c00742480038200501d24044d0620840c02650240800407010030a0380380300350b060310b224100192882403075240b004802f40c482440d04108034410741c80300800b28002c00042c02240c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 559972086 1250 559970836 559970843
    0x60c12010b03090312040f061b020d030501081002070609020402040e090f060114041a1020010612082d0304020a090903090311060c070b04150f0206070c060207021009080d020a 77
    0x14180035416220300c81485d40036005486945280c40700101003840b902c1401c0b0958040805400c005550fa500a818040300f841030b401454600340041005403c042583d600a090210006a0700c8203185005c10040c04010030107504107101050228211000320941c17130150142e1011600c590303016000d010745c3c0304400d008403e0140b2a580102c490360800381c201c09007035089c0d035111b010612001c82c04519610381c80220040003e400d4817401d648590100a0604000001d200a00440b03081191410140045601c010000c010028000344811404148020102c0e40d50001ea403500e0710705801004640c00c15a801c0c2d11030882e2401c0040c022800d13100e1840c03450341c19194020414a1a22501800b1442015003a00000104106035803080309105000103841e18542c60350302c4a041c20f4000030380d07014001c11a000d0086940c5c515080b03a4002070041c1c0e1164841c07401007680322403854402c010b80103042000f500805226203015146400201100595414000701c03a4444901e040480e680c40c60410f000c0c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 559973336 1250 559972086 559972093
    0x2071a090906060405060c0a0b06030106030b012606040c32120712030207080610180e0319030c020c0f0d0227101d0705041412060c12010b0309 63
    0x8141c10700703224403070380004020802420a96148081001e651002c4180b9400e03070824040b100c20005415025604103000742d000704181c038207654601000c440c2c18003550901d410404d4506401b80748034a4202420905881915401d0800389000b1840b10200d0003180c4500c0800c85588200d91481c000c0001403042d81c6444c20250112a424822043c0c041151306015001d14180800d0417090340800d072841702d100364020010720b442c03c01d1043c14a807002c2c00365003100074907150412168070307980200c1e007407503845040004814030100e84080c950300ca0ba4002030140301c803594400806540542c8504404d21041d02030700c0c01101c00030104407542c00509510b5901c12400c080d01d00140c20011140192a001c01030a501c080c6103010000100510488080d8061203440800740402100000f41c01006403a80144a060742040e08003d03121b400740f402030781c1e0944c6100505400598403046080c0c110303a00d0b0015184182040304502816602c5502d55100c60a05180009150070000007168821001c41025 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 559974586 1250 559973336 559973347
    0xd05150f011b0b1810110f0a0e090a0903080a2007060605120a050f0105060a09110706050c0a030b06070804060315080f0a11010503160f0507080c0a0302071a 69
    0x54456202c110011500503010704110800500d411a03040e02992401403440084140002c096140c0580a10200130240c18218030383c80342c40c03a4030305581303154120240b050345a0118010403500102c0520030158400624001d00141c0c5c46140e00458000f0702964030030b103403903603070303949032004ea908224080d01d1030803154090551045482000c3c08045110740400b1880d01c3d5280c00160304041010307014410740d000440745804114040014403108001e0000a000b585090000900083d0040c40341d246015200c51a5684104001003111402c139441f0b0b10070030050030306942100d007540242c594000400c1c0303800100051403904400b80c410745980040941c0c503040c2824070880c003504000001c0300f4113131045180820b0001d801d0000201e80c0c480f9200034140341d091800d00e8141c407480c8060f4103051004c200103000060074280039000200002d8288071040310094841180c1c1d911500d00058001c40d801f042c8503410410204611840038003039403c40d1600c0303417038614011088000341c03014003061004010 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 559975836 1250 559974586 559974589
    0x1207320a0b1503010207050d0801082b03090803041412040e0103060b0a030503040612110c0c010c210e0f03240a1d0312010915030807020a17030d05150f 67
    0x101e29480901e000d85026016102d0000c00d0998110440c103ea2940003107041040740c0b43d0060030a80108034100080800d8411010354011000d40d00700c1c0400c0c1c0002c214500200c00d0b000c0cac1c0021b001c0560040c29650340e0318050800614154800134401030790f00a01000c40721001303d803001d44040e50480f40410300280d107555680130080858007100340c4c00204204002011800500203040244090b8844440c821075a08000341255003001d0405594401400512070801e0b000460a403015006c1c00c00200350103240c1051011050310f0814102e0540b07202242115803540402000604c0c2740940382c00c480003580c4010940c441c2085001442140703402c40e0554072411866040c00d4001ca0301c40400140003c01049281406c0700540045401ba400060030042c0784034030080c0940184031000c41007042ca030084061060345145480040c00001c1c001c038441045d59111801c1c1e1005013013045e034030440076080c480f059440f6000042d071581003034580f10004080100811428400708001000f14480b0740c40c110 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 559977086 1250 559975836 559975853
    0x603070e0603061f110723040203060a030c09060302040e013602040603030801081b01051e160606080d0e18180d020601050f1c0209091207320a 63
    0x51107a40d21076039500b200d20b801c0f06503043c0d9503505401c981c0e17001114a50301a41c2ca2a020b110380c00450701c81e00c40106841605c15424400000c0d440442d809a0781e07446410000d982d031603c50704060075a661a00e000103807290140d0000c402c8034803e440504c141c0b28204035050885e0701c000ca8018032104016250308107070089004161001c266008050392451064021404560b040c1d00200c011508560050045100c20000003d02c5011142d12009055001000a029018003401e80d07a400f007141240118611074031094900c14503802c1341100803030203141000c10180965104200a038050211a51000c5102c0c45581c42c4040d0042c0862440c01d9489603c1000c038007000744841d000c0c41854442c0d2200c04001d1266070800101940200025414442000704a240803075180384240328403d442c4000a20169078130140540494038080203076500c524181c01c000031802480c010490000d0120304205015040c1d007044541d080341c049030340c80e001c0c103141c80c51070204500340000d03403196501070001104030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 559978336 1250 559977086 559977091
    0x9060309172802010c0e1207060e0f030f0304052e0806010e030d0906110d080117070e011d060603040f020d0c08150f0901050c0d090215030711010b0603070e0603 71
    0x2070405140b000b0140880001542c48030078240050f5103440003034132600d91049400580c5c00f02110b81400c1107016155103a62001d0600c540411710890106004403030b41d691803400106c1c02d024041c1c8135003805920040d51607034003500420307200d421454500344600c491101e007090020030049248802c8001c0040546140310020300c80303810000d51083e0302c0010b071000d00030320004500c41d4443d900910f0811802400090184039500203a40c0512441e0340c00d50740c8151080c2c1101c200c282c0740586800c45100090800031107400805544000d9000007403400e48540c100d5591711001304000a598407280c04200385d0303100550303003e000028045900b40142c60015035030614a8410140c14614075901d503040c508291b107545219030b1020440040001814a50381219800354604000300050329140d10344000500880d103428015903580c40403113007103403925060340c84078410322145035860340f1304810002c0440d400b100020480e5420003503041c246003040000c0c4d83c003034103e6894542d41c5918040500c40740f034000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 559979586 1250 559978336 559978357
    0x4020a030803042d122c0303040308030405060921090f010905040e010c1704030c080d0e030d05090d020d0503060d0503070807122c04020309100e010b010906030917 72
    0x321030912804650100051000607607912001e081070b41c01c0c1004021144175191000c1440700089442030300c5210100204c95810f81c2035011280381c4507003000b00b07185d8003464000400320000007060006101c000202c10344203554010450300b44496015201503c02c10307419070b84c10b08074024440f0984902d0007106800321500180f600700141d81ea160000350030b031440982445460395560041c40300b036607031003d0041651030400e240340340b4071b08040c2d400500307400b0490001b801c41d4101240d4000c580080d50071a0900c1c002a80403203445050362141c1000030a025142103841d48154590751603003a002081c6d14000203a42e03260076055580e64800d002040016050844850000708a000009038410001e051818081e281c980403e50661070082c20500440402c04802c4000b009010f0002020109007400b184003640c02588944030f00000d94a0085400003402d80c4900b443c004c045030400560100c010b04400b42c5c1c40303010300390369190f06804039407982c14043c00382c007061078031005a11903000c02400c40f03481 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 559980836 1250 559979586 559979603
    0x70e06041a22090b190b0901021501260a120807111207032003160c08011d1225020d0b04211b150e070b031006020604020a03080304 58
    0x142e002822181c0350901d80030600606010024440245584250f140c026420f45a140301ca041c2c41d00ca906004c2410b200d58980010001558102a413007441a1a140340380c0441891843d6100e43c1c0a000b1700041801150401c80505a4101c14010000d0b12401c01030700b100d0400d080781c003440402c0340d040c01c00401c06414031011001c1e200803000d0800c9100460054010241d841381080c0c138008101c2214088940307455851131611014108012080741c070b446d007032046611001105840c00702c41034201c44e444000203520309541c000444c02800e1002c80d0002c0747c00c003030360003010000700750704c010340038008150400076044061040c007942000c80030300c5e03214001070080e01e40c42d041d55181c2d21200400c403404c441c1c082c005001292480f0035115a030100b8009810300b03031982d1034900c083c1d5005110712400540540d40c040702030f56100440380d01c0f07002c070070243e0416654603503101d003c907442c0b03640142c488907000c8010b68000104203202046039802243d00622200d403030b92450302c42810780c0c0c0003e0019200740b46c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 559982086 1250 559980836 559980847
    0xe01080402061b100c0e062d0f0a030b042304051516020c030c0904021c170c0f0d051905040b07150e2116050105040303050f070e06041a 60
    0x110000c0301c219801d0b0b110001800903491071080b01050385c10602c0058107014070350070074801d2507075041d042d100828070611011541c040c02c00d517900c0480804c524081848100000c0d820018201c54000700b604080e01c1c1c07030a229000706001408100e4141d420101d03580800d520690515a001064035600140208119410100e4050391080e11007002c0d10308044011307000400c12411340d010310904200c1c03a02100504000c41c446808981c280c2d41c010002807003030810040c65001c420394003c1e112034880d008045403284581c030904040c01a0302080c44090030388900613800314400800255058034030003640d40c0e941815140307640c0b005100d0744d48003848203001c1c0a01020070041c441c4005094400c0c0680240b180060030015808122801055090303c190000d1070548100000708a0343d14031250940c02c400d1b550952011044404c000c0d2041c001d1095080205001c107251345504080d00981140c0d9000100d5220742ca400d503000046054044d0b081031043c0010450030142075503a15800800c4444103103003d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 559983336 1250 559982086 559982107
    0x30d03020a0210050108070f0911040513020c060f060a1a0a0c080706110d06090b032805070e090105070c030e1e030d1e052104030201020f030411010806100e0108040206 74
    0x26134098120125503032280d80300308868aa50703401d1704003e090340748080140001403031140d0383c0c600c41c9000e640c2c003412166401c00e00c9a030b005c1c6d0440d01503210746015100c040c03d0001c4003080701c501c1903c486211f0322409202207030701c42c50a4030540868405910452a00400c7c94041c0d408611054003610003810a00801001c5101d900440481e500c03080303e0b1542e81c80d0700341c4c9070070120703034940c2c12a61070715160104030400c03070301c0c001204070131102d41004483d600f03012040c0001400150b614001c180780282c21000521500607058a405104101e00901c0280d45024084905040c500310240000780321940c031300c25034102a9220204448502d00700d140c0407131040007103485c019a980e104400240c10042e4001890350742c003480b06c4040c1e030b5450010b00d424546048002d4034012102030380d04c246001808102054001d50413610714003c164613042d2285098100410003080c094240350200e1201c0000802c2c500d00340c600e1080504480d12001038020000b030045803104030040c4200d1b0080020481c40d07501 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 559984586 1250 559983336 559983341
    0x1309020103091e05061510080604020d2f03070c030c05010b0402190e041a130e010c020708120f07110f030f03041a0c06180106031b2102030d03020a0210 67
    0x54003d00350492500c03c02c0e40b81403883e0090042200c10301e442ea2051070076940e40d4903592281861102d02d0b1000c0251106800200280324072044004032a1400c1072000350a00400c45440341c040e100240610494041c3c441803d0f6444112048000a10070840c9580002d001d030807001d119901450001a44580340400b0404a80c000c00405140b025080d6406003590303071002c42d01c003240c0070070f403000d0020480100c0e140c1101c00340324000c54400c060003171884000c414184e026800c080034200013070000001c1c10101170b4952106000e0100d0501a02c00458400c400840071100100c4800505518000301ca4844260f91021003c4940d4403e8074a01420600e42d410041c06902807951400b940d9035516006098030441d451076104802848288511100d80350041111035000800f201e6078566808903d2103140100060b4000400c00042c04003c0059005c00340e04590a4803030381d50440140304100f001d030110084180c003000f507241e4800f8460b00070541c0300e50090f040400032070040305c00500110903048107 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 559985836 1250 559984586 559984613
    0x151b0f0f0403020f0a06020d03020d14041110030608060604020c010207061d01060e0f060927030403031101051b09030709110909070f020d20060403030501060e030309130902010309 79
    0x31404030707003802980380100e945429a1012139641c40c580b0b10704a0069201d25802c0100402c2c03650100340340074810202e8020b9400869001e03401035403840d0a10309801604000003400d406010f1005000b640d0700c4c00b81c842e01043e01c101d0030050081790341c0c1504000180d03020a881c94003a540a104940010342c0c5800303032180780050b80141c99100c1202400392400c40da200c0e4800000d060098061014902041c1d103242c2d00407000340c8040c001a40e0b031282c61b41c43e00040c0003c00740d0b984102d20501409138008806042503c1c802c0d070390808801084c02005098480c207880d0000b565445802c201c0d40403103800000c000740d00001c1e040e1007103a50340f040f008080b81c650300441820008000303410f2029240c2102425440102c0d800c00410ba001200002581c0b40702c92152681880108045c070864816804981d0003d0451001140c0381d6141c541742c010054172081c42008003141c1856204065840c010003030b10401c0300c0241040131840c00c895080f40c043c20880710142c0c1403607503480c80c410100301c08100c40030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 559987086 1250 559985836 559985857
    0xe0d1713030314270406080303011205210a03090c121a0a063b04030302090a2103180f120b0a060e010b03150907020f0c03151b0f 57
    0x611240c41c50a001d00a609100610100348070108003107081d01e28800080b00400990b03180c4941c04c64100c0c1d011500800345d40d08400030520010000103440c1989200c1c0b0350741c49204405840d005c400034142030b42140c5402d00b8401c070401003407103400d115601c2036010322410744c0508035075803d180da00d01c410460605001c10a540f01c14800108030a140041c02080f601b20f0b00359101000040d142c0072054410300d040512034040c0354074654403400c1c451030300354a20400d140890120703010350505140c098002e42c0300c04042070298210100029800b0400f80c0300d60040301296a80f285201c59a42d03088801181040302081d030400a07020100710030016090000280c901205e01d49232000305820100c4020100520445e80765040c62001c0c0f180351608142c103411500078140071916600c96140350a448a55000c42c039400c01d02c50400c01540b69070004e01d001c01ba0008000b40d4603c000c07041306154403488250802c1045064820100e00a200060303c1070b0b9808000000032801e0a0311a410b40c0d8450b403186c4c1020 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 559988336 1250 559987086 559987117
    0x507030207050a12290112030210050a05062e05070c0b03010e0103050f0c0109030b04051e0c04181a04080f0406050a030f141b0904050c07060b0d030e0d17 68
    0x100c3c100517480284041007460045460118125800c0c1c042e081c0034140100c07011500f088600c3c0f42014000c0000340d05021504000b40500e207080e0344d0403c002d000440301c0d44d10800c05182c240c021010302c40100d251954046001d01d02030328034803000b038805a21440d000c54102801c044002141603120740554081c140c800d015504651443c1080c2c0d2070025001c03000d14190300700081c051010b0382c00a000c0742c00c4982c000000316140d41c4d0303400d1250800c01c240400c1c04034144221341c461f800072800300d00c11690340d10032501004420b50b0108080040c01c100640242026010044510350f6290204410703481846403800d01e290504a120216580d00700343e0021022410108a0b552865014064541c0c9120020800c12040e40e01500030094a280a0201d00404410160320401c560410044032025400580180000c0c24000c3e08118254016a0207590b0b0710f1801c10388403110b1808000c2d10030b03410b80556401c401d1500784c2c000c000180002d0395003155000941c054401910790040301038180c0c0754010620 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 559989586 1250 559988336 559988369
    0x1305120d020d020708030d110c01021c0606030605011b02061e0405090606030403050304030e010509041103090714130c0507021e21030d051915031109010608070507030207050a 77
    0x40e02d4001200e507031100395080721800788601803000081d1031058206010203d51308a596408200034484c84441e209a5400010201e064800d2035031950768048000c03400300286655102c0c00c030201c9106000313950000f203c016405440070b203614420114140001d2503145400000310003005041c000072094001395001103402c0010307252460102d50700880a6420500c0c40c07800c8d0750000c0040c0300051008080c080c600b1505c0109034442d1055510b00503006c0c004001d00004407048140795042210108020b00c280c400209222819200224810030003800c03401c01c07414070015480140c04180312038400c000b01400700f200966140655216502e0b85188410701d5422a0b100740480c0c003c03203941c0c024122400200c20014060000304031102c400340420006226128146068644948502890201402d0024041c0251315080c40d41085a1007800e4240b9030300580c0080c890480c0c024440e280104207140c00060f0158001c0c07000f0500315200344161524652034800080c0000704036082060b60044a02c3d6 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 559990836 1250 559989586 559989613
    0xd290108060c0f0f0d0b150418061a2101030609021003140601030e0a080f040503061b0301031e0605040303020915091f020f072912040602130512 64
    0x301c0d4200d250220018506442009034960a12440803955907894002030005008103042e8469118540014100c14403880843c02c5540140c2150141d00640c01c0f0b4104130320301038a400d02c2403d00310361158028003540048228580c0c030070780110b0360085e070441203010751034107004034015400d02030343c443c3d50001101c0109e070061048906102e0003140c2854502000c801041e002401f0079688201e091070045446a0429141c80c01e0241480b4011b0a001c0d01081017a810007080e000751042d1a02902280c3c05070343d40c807160520540d4100704107190071030208011f00c00b0650014040301100d501c4082d85603a02c500d27036115000c03500f00722000c0e80020b5000c5242e001d07515100c0750400b00031041403400c0342450000740001f065200501c114a85402000e1020002c4500074011160840c0040080e140202e5030740c440070010001480c18861120140701c07105078000c140ea002d5803c80d0600a070304802565032903a8910003548005018240c000d403440000603540c0c2c45020105031090080083c00e1540001d48 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 559992086 1250 559990836 559990843
    0x70509010b0703140705011a0402090d080915070b0106020d0807080103062a0e09060f130b1504030f030905010801180506030c040627090803070e1c0302032110050d290108 75
    0x2480c90303102784c0c010014032205a4501e0b0301300b80d0306034100c0901c990b030346808030000e44d500b110000c0c142001340300818203500703220052903d541210425003e8681100140310120303006802240d0040204848000500115040d6030010286807032445400fa003103039040300030795100e0a102501400060f01c030710080d0740d0360515142070b07a009242503e100140410200c0010611a64034550f802070036540c00311240e0507a41c03200b128404080941c0e07203503074698072410100703041074030f02070103601045040d840080c45511640c41641202c12240101c200000c9842800c0c000d0030000e003000368184221180e26805507640d00c1900002c001d0460015604c100c7c26a8403201b030a0521881444580340c80160f90201e68100d0450750f104d44949070074030b2401d041f080081e0340e0080307044000d1255041c062180c1c040640001c01081c0d607210380407006405070209850b08045400031142040c020042e0300d8200f0080c20098280d0a4180c0b055100980b680002130303100d4a00001184115004c03c0400c1c01000040d1003070 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 559993336 1250 559992086 559992131
    0x50702030a0b1306063006180f0c081605120c03060108030c0c0609150d0905030427090221070e0a02220f052b030503060f0102070509010b070314070501 67
    0x4214607082d980d1b04003904022034103421111020008040003400800040d940303e50b00b032102280300c1c101c0c400c50300d00744084144241c0d0070480e0116184900421803003000151007941071500b88001540504000c140003e1000b42c1c0c020740050311805107154940c2d6424002180648500c0009507124124400d05603c0d1000c89140c032030084400f0015841591250144c05010f01c40702c103406641c0c1c803c402a001d000340070811001d0305900010401044004100c2c020902c9129483d0b100700105048403083d070101d841e400d0f070080d4003001001c2c040c00b041d001c914a0b8803985189205446030305d0b41d1054201c00841080f1103014959070300188200140800f241e20322852610034104a00c01c81c20003454904004650142c6441400f50700010fa00c0e200001c11342c8004445525160010003000e858041c000f03070020303a4440d124000783c030207500d61540f000524a0440380d004281c9071090340390605a00712684801c5003a82042500102b0450924100e0300600d80d45208078000034000c00e041980702c80c2e09091 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 559994586 1250 559993336 559993349
    0x905010b0103240905100906030b060405060402191d060c010b0109080a1a0c04080307030306050901090c020604110f03120d050a02040e070f05040521150f07050702030a0b130606 78
    0x241d81100002d1001042d124292502000002059290070006c98200b15081c0c0c89502d42c0c0f4140700001c01040303c0003026500440d000e540a200d161206801c21044c2c0c0611001c1201040c02e10402c18600c2e032090280003461480d21070b120400701c11180214031181e12041c940c502680d11034036684115644512204020300c854006030200c007440c0d80d5500c2548101900d40c5c4601507104001c81d0340c00112004860040c0f043c0d10032a56220824540900074184501c9010b10860720b0f400005803190560058403000516070703020b00003da9656595100b080410803000d0f800980c1d0420440468400300681019070004805490711100092407403030a59034001d280d030080c2801800104400d481340041c3e0703500040c1900701800f051014032000c5819000b0781d4400c99008103843c403992164148243e0010b1902e1130042603454104038080440c0700782030103990300f9542070340050028810034802c0010f8201e10744002c090350f04910098032030565844098a1181c2180303056401103081215030300c41e9130020202c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 559995836 1250 559994586 559994621
    0xb061e030609090f03120601021c031a040c02070605030a090b100315021e0a170115030e01050402060a0507060605030106060f020118030f0f110f030406021204050a21060905010b0103 80
    0x1000c480300c3c5d101e0141752180341c5448104404100d5680c02404400140742c440b004801041d40c2086000740030300b02d0600c0c00d00403040101140e0311039080074003503546121840c5c1c0050104625201c42198990f00040c07000380f9455494421100007801c80889034041c610986031484203c1c207508201a80350034000300e5008640c41041048038901c04030348c021007a41140404240c82e40c5141c4400e59109218854010401545030004948500c02d80c144c601e40c1c0c0002c1c3c0c2e0812018003004040b42c03c90b0016500079500c41d03418002515154400c4005004841c842c0340c020552035500c2000ca42926003541281020aa03400b24146055034248a42810480258070300b8072a01181e0320003406042008102c4010414100d200004681c044c3c00ca0880b11601502120107445504144584035041405508014010709440c035a00c1601c40341910181c0700700422008010303151034072642c09590195141449000180401804120380c1d11409000074080e4001081c0b4a42070380005007110690714102c0ca5901 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 559997086 1250 559995836 559995853
    0x50f0708100311030a06240806041109070512091e011505040e03040f0b0d06080607050901050a1b060911031207080a110d020708070b0a050d0b061e03060909 69
    0x7102100216600041c9800d0399044940100341041511072014000f030b4180705882c9040c085251880c81000411941c5150f003d84032031415031101402d99020b0400b00719048022250b20303241e038074a504224281080c03407a15481030030f40c00d1211400c1302c61640e2500510203070002003040e4032a0600d0300358000700070071a017626101c680c03c00d05002e000703483c001c65850032007001440e4100f00315005088400700d07460034160f90388242c16003640300c2d07a080d528950501d80c000a605000150301b0340503c0e0245caa01e41025030440c0115280d8004841da041040751100b00c1604034090700c0714414040c0e02417140401c0c80d81300303814014403e0002c02040340c000d030302c081413031620b0480b0042a221059400a4900c0c0da0348802c01c4100c41c144200e030b40c0f411140c00341145c400841030b0001848012541e40b00150f03501d80769034045007052401450103c00100d28204600e6219190755801443c08140c000c11090400c03141d0302940d04060b1480e4a07481803004001f0a000080ca0600d0409600c090300400814100c0c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 559998336 1250 559997086 559997101
    0x100501050d0b01050d090501020301050310050403021902060d050106030209030d02370209070503040b01050d02060406050c010e0303100f1202211c171003031d04110c01050f0708 78
    0x40c8038000691901d1680c4501128182e0311a5003140c2e03083d010050140700164841c10050300075403007071148501c244242e90300138090030003d000d05031240350150040d258a00c11120141e20300000381000b01d0384040200050340c8045051b00c070b15406803005550050300e90139400c0500d4034003c0085640c50a40d4041c245084183c1100c0007081c845003004540810005a4148841e44034032100e00002c0d4003c0c0f03032104014125a2002c080c40c4030300c0c02884840a40c3c3d0b610018000c207442e01900280d04202c00704418400203005200500002040034000214500303c0301e11117046420036110001c90009100c0b00b046106044100300d006040000c4d0850b14032042c40d40090818080805100145c9158540c0d8401c800303428000f0304042c1044244240c103101c03e0800c001d18405079000401c81c80704060002c1340040718108011015254540c039421981c46400f075221a410980e1440700358444d84602812040404040c050902541001f0012074103007400581da000b0620014401070400850200b0000074 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 559999586 1250 559998336 559998347
    0xe030a050606100c0501090b040b0a0b241b0708121207030e070f030f020909033603100903020f0604050c090705160510060b0c100e0a200405100501 65
    0xc071034203c0c1c0303401407030340100011340307105044101c0500390394a010820028072404103401440b4a216014101d030b207907124986641100c7c0d6800e192a040786480143c02c0c03640c003031050190321808012201310704082d19500c1c07000708403a2010324075040b40c21001041050704010098069104803417070b005818100c210001d2412040001d001000305501c98034410b15002040c004440a000140364410440740c8034244200101c4906204900079034204000840c0014080155510303002005003100580d064030000f40301c03903641541084040006403180700030640d010458541012050007000c2001701c0d503400c010341440669080b058140c3c02440c20000020320115031601ca5200c00c0b40d948605844000b021280e50050050000c42040020050b10900c00c0009100c1e030300480414050298544400c100341c074502818a100420b83c1c0100c608a0840c102c0c2e800c000403840b40709007211142055a04c40100c222185150484062241030b405c0c0390f02c1c00d15004445c3e0001104160501103454400000c01 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 560000836 1250 559999586 559999591
    0x2280306141507050d0906140405090708190903021b0324070909050a0e0d1805060d0b041103091203010e0c03090a0c0b0d150302030712050109051005070e030a0506 72
    0x10640c514036160ba5001da1650944103156040400c80381c000e602c902c00a09036000d14060600804c0f204000850400c00c4801141c06460001d03283c0d03030494840d400e0644064001521600c440b00d80854a410020464030030030340118003a60080c501488244000c818020690300494007a4204c2111704005d41001b2007003000b1110410804062581d440324101c8440e03040760400d03a1200e05040510810900c6a003164a0046441c4d051724150101140140c0d207003240da1b2110042580f014108220515081c005002d8060b40c414011a0516052000901f00e40c011001c07003040350303004030512070070406c00c001041c0484c1003482b405285504040081c80c0c0c08a004064140340500080040c071600c1041c0580d01502d580001c1102c3d0141e22004001e0a41e040f201c8040800d42ca040c0d01d08036290b02d00c0300c00d40210b940260140480c0350518454081c02d0900c0349083d110380d921040f080700000c800300030546004014000c002001c3c241080700808840210b0200d61007030380264460004134801007811078 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 560002086 1250 560000836 560000839
    0x3120c0c1207060f050d0207051603440c0d03050f09010c140a0e0d141002070c030f05070f090209012d030b0d0b09010507081006050313060608010228030614 69
    0x40c0c1b1b070640e484145002c1e10410700010598050703000200c078142c40c1981210b00703981c420040001083e81d810a0303194040000031a44003a01204455408200038603030300b1403855600040c0061400e001110524540241c103514240080d58402c10401c400000704d202c55042a41c10000f030180041b4010700902d020b55150045030700074400204291003d000c0c1c00b845180d0f00340500061041c980c01c0c14100c6d220f60211b010364200e030141c0044098032407258400c50f0045980700c1d094803022811034950120312034409004650301d100307031007020070320a040e21000e01c010180310001590300e600400006010f5a4400c520081e8072701003681072a88000c807103004482d8200079180c00101c41c0c003040002030764400d21070308c00390840c1c600c2c0052040003032040d000345126105a8485200d5515003100e5184200040e11078500010b10500c0895000d0854105040c0050f0060304049501e40e2039070103803401c9a0003918005080000c2c010140200503228000403409412400c1c204500c0c2e241c1480d00d90090040701015 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 560003336 1250 560002086 560002097
    0x10f02030d0b0a0510020d030f09020d1205040506070503070c05041a0405040303021b0c04110a09060311090a080a0303050117070e04050a1218090203040804060e03120c0c1207060f 79
    0x1c25180c42c3c03403540c02e0050000030880603007409680d80194883c2c800114800009081542045901005000301e0000c90f601074600308140031162620250700ca40048040700b000300401c070019840d5502c0700500140d030f0103030000e035a4403030046c940f086908460340d101e00d002e541800d07181e5420340e00c10110300383ca1820545d0b01088650311460101c00900c01e100c03003034001e1100302029114444000a000c00c11070002e9a04100c161081840101d041c000c1d064050001401041c0500241c0e109800c0075008002482941d410580b0440c002083c0980c641c0000c0210740c4900f9800782819818040e06004000360868404100d00900c60745403141d5803030280b100e030001c11002190410108011000303040303401c00d90b0300341c0c20080500001c05aa0b40c02c00d6107202d0308803502022665580d1413085a000716807089840d4a801e181500a07540e4015146006506000e85810f0101100c030910045c400344810401425110180328208090f0076502c0003500d0855008030700502032590000c201c42c04543d45800c0c078 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 560004586 1250 560003336 560003351
    0x6010b04031e08030109090506010f03020f061809040321050709060f0207030602030405011e0b010909051e07050c01061208120c070f080406030b010804020108060906040621030e010f02030d 83
    0x1200001e8102c2c2400030051030000000042540b815884030100d00c0c0f0401c240c50742641e0b99000c200e8401c0b85404040d602410800c5007544d546000d00c020703c2903070703951a401c610007215403000525282c000c99054000c204a10309102601d440c00c588448920629402040f080c10075200080001500b400703040306128000c0d0354400c0c02802004884000e691151041d543d929141c80d0050280c03510115410b1406984100d0060383d400d03500451101c4181a503441e0380c0c03a850452901e0181801030a2a0300c6045088521a00e100d004200740b0311803540ca4850503603c1150280550031100154411341550440d40300280015448504403600b180090103d5000e60b210b8440c186894400e424006002d50b4448204808109a140140045400544040010b0710460b00103541111013250003d001450550004555117040000c2c82e0b04a6000b80000a0a9880e000c2c0002d01000c2402540c0041c80740b510000105940004803410f07410084c64490600b05402001075036070301a2a9443c07800c2c0d9105c2c4603 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 560005836 1250 560004586 560004623
    0x30b031b100e040e0703020f241e030f04022407120504080709050403030f05090d0c050313062304081509010207060c20010c0203040e09030c06040302061806010b0403 73
    0x1c0b07481d16040014003c225031310041c0d000664848803480104c0c09180701d40c00714403240c6000a20800c550806240303803000c2c030a400c1200c0542e075203d06103540030300003011008841281164040c5214104000180c3c49a0805004010100d03840350020485003141c000200030082c5000c0680342e006902c18501e0440516803181903416014942101010780f00700c00f4001000512078008034012030098604100c00020204140c1c10b0314400c865610041d44032880b0b2145051041040e404400c3c02001641c0c10036030348040c41c58a040c90b40d844040047c10300502c0150903030280415400001100740864507040ca42808240c441a08414601c2056404c10019170102c40a40488000503070100007000150030b00301c400f500f200001050309009071800c2c892203040c560b05116180c5441001c1c0c0003542028a0440c0700050404028020561f0303001c00c0c000d500f50a64100511800365100b0b4002c0d1515140903564070313000f15400180c03042264030400040101e21030368001c4405403a0081d4a00084c62010381 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 560007086 1250 560005836 560005847
    0x5070c060f060506221406070206161707060f091e03020703061508010c0e06030610050706110729011a19020f0c030f060c0912010615030b031b10 64
    0x5000f03503088040085c203114204060404003148910800d2900790482e26028105107480a46220503004002000007001515040c0e010b8103001c4015190404481e20a60318400400c42059103035413443c01c040b84050800030035004402c10740741c100304204444522500e03030303842840d090401d2120001c1002d03480d2003071501c20301080004e5038003c5020702c815203a1016030380c0c1001603440b6005007546080310342c142d1640b007440c10000e6004010041410b503221203040200821050083d40d0600c841042050001022801805020310700101d01320b40f618004d0601420560700b541104141c25400300c02215200b802c0508681075900004d60304000e000c04051951f21440746102c1d1648441c0c0a640651034198000381600308010103d00b6140d005040d00281540c0f000d40d80c0811855400560000c2d008080680241c50070301d00003002140300340c0c8a007110500315000ea40000c083c0c0c41c8007401030288250107010710006408282c0040480780c11840754600c14a050b04c074003a00c00e8011040c0c41381c8491080 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 560008336 1250 560007086 560007089
    0x120a0b0a08060c03010f061704060506030a150b090f130f0204020f1206100203040608060f031f02131403060604050c092101060812040902210403110c0405070c060f06 73
    0x1c0048440c0c1d801d1100455503150024440d5200710f0340c1c64100403c0041c0b00300e144031071032940003580c0d10658407a980d441000d0300006003a103405d4450340e1901740c00710304034506907035803041c1013507000034844030117020301094071801000c00c005c2c0301c007050a10186021602003c0081500b08071410582c003d503200003800381c481c29000503000d000101d0443c022001c51880035001d05002c82c0c400414801d230600907603d03805184995000718100000003034540c1007941514260300d00040544400413000040415020b43d02c2048035000c41c2e0216080c443e8450001d4145c1c05049203120411800702e1140010b0b1b510380c070040c20140200e44503c0804c030031040c0c100682d00750000003071080c0d01d030744004115016040a041c4100556600309800040d01682c00b28010309040d60203103c0310302d001d0804940e0000796000f103070188543b40b11100f40d08112051403190702d002d035129a0303804841d845181c0c1c4003854000040300b0725102c0c0385400244a0302940103246007541e26440700d0041040c90301048898002d00d0b15 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 560009586 1250 560008336 560008349
    0x10030b100b120609070206090a0611040b0432090429010803071e03090509100b1216180611031605010504050d02070612051f0305030c070b120a0b0a 65
    0x7040e40c058080242c088148219000d079220102561003880890390b030f40d41036502400784d400c80e481c044049a0540c00c07600b50031500708030b082d00e080c0da50b0340b507039130b231a40f295100171a0002c5000307110107100002d20310340301100d00501030010209a80c000050000340c0c0600700414000d6020a00c101081520042060010748041e60104039a524501c0c107882c0d41c080320702190364126440841e40c3d1090703040488111190140d9600c0d00310740c184001d11000c0c41d006880c003131a29495141c0003500240b2800108000580001107600d036080c8660031a5412085c0000d050034030240000c000346804c100c4c0d907070700d040340c485240c4100c4c80c440c1c00314294218482d1458070310100c0360100303884088c00360542080740550b102d201101d603480c122441c101e0300c4010038050342c0000707040758201ca4150110741e0042504030b114120710048120f8041c04005114140e941300b180e4681010800030b040c4071082c40144000c040f00080f141c0f40103403100641d20003000041a110002e03503a00a0b0f02c10589903000c1050140c0342 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 560010836 1250 560009586 560009609
    0x1509122a0706030c0801181d0609010c0f0f0807050a110601080d0809030708161a0f040302100b09010b0c030909040305091003060810050402030f030403031806030510030b10 76
    0x805080a911012180500b40c00700b81440e40b04080b091207514564100da0b01c00e010958502000709801d0041d00d01281400790507000c0004800c0c40c40c1e018080c40e402424100000944034003618400b50405030200442c03000d0007000340c803149070b454114184650050891030901e55940f0b4810043e6007041528407400d00d94400d0b0300001c00c4244000a004a240b50140c0703580420765240103c560f0f072403090040007001700b2800c0c40800b860820016002c005170f4483c400e00004220f0749444c038041c0200131505e990001d1207807010701003819014080002400c0508000380004101c00700892481c000600c10001c189100050301014080309005485000000030880506401c0505000b4100e8000c001d18600c540304610102c840180a407181008a61440c40501a441c4070b1300a044000c3c90010310507a05400384801000c80a501440240081c5210f80c44015a42144c090f2142d10001903030481c07010b0524107020b104103891541e4030344040303d0340000d002045550b181ca1000e5000000c0c1d00240303ca41 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 560012086 1250 560010836 560010907
    0x605220302030904050a110415170c0712030608210408011d010605041406090a060b042c0105090429070c020102011a0a0504020a090b0a030c02150912 66
    0x41d4040000c1c072250600310303400c0c401307900c80d01056022604480f10010314008200420042501303007a140b04000340305420080070349902c030b084804819004031381d100c07a914000100b000c10040024a04155501207243c100011303400d02180507030710341000d0034041d00c0c5504450390488805145044a0107048031000038000182d50400e510303104114017443c40115400c16401166030700b0f1030310501580c403030482010300c41902c80100380030452001800e0003650f580c9400b00400c0e1840c2e0040184000c10500000720903002c0400d07400b003450131419a00180001d1500300410055a408030950340141d0040321400b0103c44100c94002e040d80c10905030031007004524100411250822007004000707000ba0028480704020a4003120100b0340310f201c039684090101424000350901e40c2c0503100406c0c03182032401030300f038071000c03070b084140c0001c12904e0000b81c84203540404540c1c14006841400d8100e0b9500841d814040462a12a10300840c8404402e0f408592514055000e0292110500c1821072402075031 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 560013336 1250 560012086 560012093
    0x60e12072c070f030b0d0215030a14100618080a0305030423100f022101080c060403030c08133203030f0702042d0516050c0a060522 58
    0x211000c0030401045001c481d02421186100c81d00c00c10070380d9611120700d04016801d50040040362030b00750b0459020528000144c4803400480101007410418640324940032116009072401c1c40011180f900282d8284005408648015001d403811800c069500e0505004001c8400700d07594880a4540700f00c4540c1018190400000c600aa0080001c0c580e615000070010b20111520001c21205502520410701589000da0243c07080700f005690151400748009426171005d01c4074145c62402849210041000c00030401c01c400e5031540c241c80d0682442d1640d20042d2241c1d407100c40c00341c0a180005001ca13016454000004c008d042e50400010500008810301c0f80110082455520812100e01a60900d440d000040c0c1c0c00c0d55458000a42c03410395183c0c20b0201408506080140018000380c074101403801841a040401403600b60004030740c0b078204d6900301e0b11150395400c4020b02c01c04008000c040c0c0d03008100075490a42050004ca03158560150485140e440e00c074046000c0408c40400d40f040 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 560014586 1250 560013336 560013359
    0x60c03040206090a090903031a010f1101060f0b0d0c020706051b0304030215121b0d15080304081b040903080402100c0212010c030e060618070507050a0c08060a1401060e1207 76
    0x46c1030007640c0820001d2241d20003000400c520000c1c15011070f4010300b4810705070303210f40c590030103003100d41d000400c940da80c2d00b10b840c0990495030080c000840303010441103001030651145240f41000c61000f052464079142e0040c040e44140d01c081070062001000b150000001042110300460340130f865990b01642240c050381d1540c03c03444402c0d116000b250045100d824192983c0100c19034030b1391045140900c40e003562801882440e008299000030b034040020004424030250000304881006840c03040c0c1550310312b5852100f110700b0f45104600c1e1182e1302000c03951006545900c41e030705850301016400b0404054170b911849580081d8000101500348070a0001900590300c1078a06440500c825000e8007000c9031180011501d80f60010000c1448010316914040019044141410f1181c540003044e124942080308050f026a0340d403603880000c001d00c503010840b0a905c000143c0d4100240c04200c100640f003694184179020800110703683d600e000da9103480103003000c4c0c1101ca04881c40203554082d41c000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 560015836 1250 560014586 560014601
    0x71b1407032d0512090409021005040602060a020a1e0c0606030320010e100917030403020304030b0a051303110106180c02060f0705040e041104020a021f0c02060c03040206090a09 78
    0x100b0480074603981c0c6031140d510800c0c0105074060040c2000400008400441c1e400510002e5801903c0d047d0300005a240d076100601059000d81d641e0f5692410240080d2030281d019220310006441080710340c0700b00e5841000e4407121800380d20388006040c06014212054404184060501d51408800008047e0804102c49140701103503081030044422940c45400c0320240002010f81e5000058070041c01c202e07507805910024460000c03840441d0b0b6070581e40c3c4c46070300b044800b00c0250f80300240c02c4c024406d400d10300c207902c5002c06e0024011898503400541001c0340180c1d0081c1806618015801000029013149001d0600e505105018402e480d00800240040c0080140540200360125016200609405100e00740988a043c41c140c07a00754851540680140103982070b0711044a1903c05035140d000400504d8510381c001c040540b0507245001981c0030007201e9900a030714050f01014207503004540d45511001d0140d225899035100d0011505500c03810221a40c8104000400300344098903504c1442e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 560017086 1250 560015836 560015873
    0x11205090f0d030c020a230303010306050a0609050c0d050c0405061c0c05040620010b0904080c0106050609150c010209030102040305030406030605041a090403030e011d060609071b140703 82
    0x69030490940b1080d000c442840d191140140c014402440226880301d49501144001c5400340c840c15035201c8200c2d0454000b070300708172601ca490300184a17804585e1301414000c0c1040c81c00800c50760070100006242440b03000d001c0000a40c8513400208140c03500b0f000d603001004c0203045599100381d89064004003000c252012030039107150080080e00c00d44070390f09660984060f91030700c1c4c0080c54541c01d03010054031495201e505940d00d48180c540c4588a0f80b8103580620f1040340010340308c8104030740040c00e440080c0c01280c001d1100340030000943d5140080d004440305105200d903992070225440c540a031151180d500c1c2c02d9800094004100a0000700500480e400c81d0750802929071104100030590300c486404103c00d440405510f00380d0314009080c1030b049882410b0018495848002d0035080d50249015a1200d10503e4a42c0056000a1000650010702200d0f9039503e0702e40460007500c8081d0804989560207240c0d4042c00c20404540ca00403203600d5008122070009640c3e00c3c02c82c8940b50300420707a1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 560018336 1250 560017086 560017093
    0x507031e0506090706052517030402030d0e03030912070506131e05030d0e180a0203010906050609060d0e12042403141f050616110a031e02011205090f 66
    0x600002e10210f64001514400daa40307a07e080e00c01d03a10b648001d100c008071048030150b88405400001c1c2020b9100b5040f41d0500d00b40d984900e8140101420b1088200700f043c00e0184100a2691554010017220385d00b06045444200600044141603d4140c0607080903030080c0e030000e209400d0b4114800400c088540803180c00107200080c8414212814145c40381c5901079004c0c005049940c1c0c010020705011010190050f81300d0a801000300301c1c911020388200085541c000300620041c601406810046d00d0309455507850f007080b80d400b0a09502c194155981200d64891044180c070310144500703400c005541d952a038445072580560500c01502151442e0300d09012a2106480c60190203030016900c451a90f0302103550310308500700106c82101c801d9401000b0442d40100c0e00355240c0e4090400490750140c501e11650051506410729030704451241d200d0b082030070080002130070700264030715805528100d609035540581b0060380e2480f420807600405074102001c00a840b000002c48192503c03660044 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 560019586 1250 560018336 560018341
    0x19031515061107060c110d0f02011d0109030638010806150a0f2319030e03030411040b0909010e0d0305012303031e0406030e010b100c0507031e0506 65
    0xa4807080c0002040d2003103a04806002c02c900d500542240e0381c02401000c15a80c6c089110300007a07034185980400300c56007454131020205550b8807d0b01c0e081640c0a4000702003031850804000b07091a00e540c44024501d9445244103204559104250304c171190b95440002011040d0b1003520f51100540d00c02c1c0c600040300c85001541c54030340340c10b80002d181003001c20146443c03403941080300e61003c40454041840305056524131311401e6080400c1c1d6100e13401e40c4054032155480788d0341c0d91290503011050101401e0007420300000d00c010080f03039001603100120040b4000a0030100d030140c2081c42459500c89408800c215490703070706410424030040c1b00070a81e09003114007441a802c468082c010112008071445540b03034110440307074010001190040c1100e0602844c0c1400c0f850340740310300c5030180d114500410308104554160041040c0e18141c0d00080c00003090702808141040c0d20740d81440100244401d0340b00c03c0c40814440d1502443e00b00c58801040c0814400050390001c0301c0d0011507651142000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 560020836 1250 560019586 560019599
    0x50c090112030f0201060b0c071a0406020718061805010806090a0309060f020312010b2a1002030403030e060f06030c0f0a2705091f0b01090519031515 66
    0x2142410780390341c840502691450341d1011506000750b030988009665031a0307804604100c10310040c181c80b01100c00107201403401d0644110030a10501c2e00c0503e00708052005001d031540204000d8190390b14190b44003843d072030703060041020b040141d010741c0d1101c1c0c4500c105400321070107411103410385600c201210801e0701c400071000d90301d1803e6080540062044c0c682444821701c281c4240d00344d1149403048030b0400b4103041e040d400c01c00e42030380483e090070000034403099400c103c9010b0b0b0101c54810149011030303400e5105040d440307204960f00241169030000005081501a50040c075040b26804200d4801380f41901443c8940c0000f520703020700ca8824210046941c1c50b10078615054050090840082185003001040300700044032481c660120800c00d21800c0c000d55071250610502c1c00718020800c007c00c071b40e5201c1c81d0b601e0410b20310b650a814072a58a401c0d0340c12500e407204032030046c1c0d2003000a2200d400c1c0b040648019400081254141102945102000f40c0280303205e030040e450341d600902e58840 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 560022086 1250 560020836 560020849
    0x90c0b0703020c011d0f1e09091014092d03070c050f121c1e020a020109062c01051c090209010e01030308130609060612050d03020408031806160c03050c 67
    0x103005c0e40e018400040c200c10904280d041c3d89003000d1f406858000d0250300313100054500710300f120324484681c030840300ca58121009000b20a0075001d403045030040b90400c4000140c42d43c6840c0c0030310010700a40c0102c2c03444600040c00f1806008542000e903529040c8628141000d00041e00c02d152245118400350703134142c0340c1030110020b440040c074020303e4940c080140400c2e806103e10009010301040007041d0156028900c9001d006425590143c02407403824800500103c942d608004204030662201c0c0c080c042c2c0880050a1275407011480c8000c141400340100c2e03440c410b00c46803055080301c0404c000030210080c0c2001600301c2c800c407a588000d85c1c80d40189500d0103000d12000e0700280100340452035a00c1d0f940d4404285500845011034000c0390350321210143ca1042c0e000b44a4581100400018402c050000d81502030907850298a0a850040e1560340c9000d190215031106011000c0b031421552401e040350580800d0700c0c0315040142950804c01d25100151001307980c18021201c00000314076045 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 560023336 1250 560022086 560022137
    0x60a0503040b220b0c070c0b0a0801090908041707080f07050f0301090b0127091101020d02150c0f070b010902190e060301060509040f0905061621090c0b0703020c01 72
    0x801d0581c41d100c00c291581030b410200500741540100741000140b007c120420001405030000501c0c00741c0e6417400c00e80050110300e050303121540c0c40342b808500900003200f4a080703c007240c0001600d80c058021640c015401c0c00255807000e14544030b0440070110030400464070300201d5200300c8040180510f840145800d948180360028180c05100005004c1d03a198a10188010f40c4003088a009803140a400c0c1400c550040c5000c0c0d032450381000c040c00e80c9680c10010b11610724290300c06020700c08140144030708400030181900c1c80d49000401c01c020b2040700601074948083c2c015150f801315596400b0140e000354405501d0000c003d2440c40c0b281030f0a409000740d0481c0b90001307400c072423640e031910720101c80302e40090031711660281d110f86009411928601a02410780c1c0980d0141c0030900f4030040281680400d000e2450520403481c0c055441b00c203e1070081c2c0c0501c40501000f2031b442d5847c0c41c00d90041c00690b000042e60000207d400000d050b40040d50200034582030300c980c114854009100150703003006 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 560024586 1250 560023336 560023381
    0xe010b0a0e07202b110a12030e0613031e080106030f0b06030403020606010806100203070f020102240123060711010912030302030906150102120c0c060a0503040b 71
    0xd8804900c9040c492801d0800b0090102c80d02c1041d0200e00c842c0c1030400d0b04440209030281502c0c10003a1a1001c01035400c035200b0400e00301102840991417a90b521401034810160000705035000c001b1600340a03070003c00c1100d01440c143c0341e00346031450f440d404c508504003094001481614445d141078041c50020300105000b900c1d003c44a82c641034089000d84400b10551603081e403920403210302900c4080c0914010740c426000340c141d603e0803500040102c84000d107094403c40000c0d00034501c0c17940100071241040d400907125104403903540010307481c0c02070261a5942d0b070450400500c0100841c1450641a55490310343d400002035510004a25a02200e03100d0f940024200803080020711032601030608a20306040c4243c10950314201c05544d089696010381c007094001003013202c10354080c0809176002a8900c455200024174200003560360b0202c4012180301c45000485055140c0104a0241030345801001146e48248008000300150401e403012145000c0342d4020500d041210141c400c840f016 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 560025836 1250 560024586 560024609
    0xd06090b0c07020d2004060e0a151518150c15270f051b010207050301060b030c0706020415051b062208040509010305070f080d1d03010219030e010b0a 66
    0xd99455401c07950845d010004500c0301212071030110390311580a044014292010b0b6a05d540c6410b1481c90141d40000c00303c104501050304051004500039105081d441c9218500707030300c080c1312844200c2502115600b0640040181003445e4201640c060b0110074140d20803202e05d40581801070781c0f4000d55020010015168404003084c0041060340079003658118019010050f0b0100c158840c242045024805842c010b4424803080c07081d940c0401264000300400d070020064a45000000341d014040a81011001d03d0000361500034444c0a0b018ae40241c140b400c481038080c0d01110b00503003030364000607080b10b03861220307200002c3c0300da00403820b5842100040540c806049041e1081481001052011a03506106002c04038445c2c444021040c040c511510007000224100f800c03a290700b40844d840754185912007400c92000a520990060311910f42c0ca0394460f21a80d000c0000b40039001d00880e902501c09001010080706503d90000b80d074980c0b403200200b041d40300c0c0005110b52001c20b8001c0402080 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 560027086 1250 560025836 560025859
    0x518060306190b09041202120f0a0c030903081c0e1501090b030a0c030c0504150b091507020d0b150105120f070207080706091d04050c041a0d06090b0c0702 68
    0x301c1c00744034101d041c12202c0c000207000c1c0c29800020b5504a0540d03081d80c0c0c2e1043d5400d40f19003550100b0043c0e60320111004d28904001c0302c50340015041c410380c03103548200078204401d103081500481241025550152a15880d0b2011842d0081880b60a06403200068244150020840000b20382106040281c0c000040345a08111050001c0e045600149406100d6803a54a01080048000502840c070450b5200241d42c5460204001c1e602d8807403094549100c0713142300700f221151200444406200c107681610070920810f541c01d00d58013510a000e50001005404801000a480000c1e03115011600054017450100001190a80901d40e103d86607001d0040128518440040849034001c005104840c41d294a800800c1c0c288055a403145020550b401c00500429200c0b10019400c0048000d51046070325042d03d540741d645403401d6010380500e50311034940da5800d442450000ca64280075107000030400c0d10307240040081100460903070340312407140302003110102d10720112400349400824102020 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 560028336 1250 560027086 560027101
    0xe0613050f062a0702012f010c021014100e06040603081603120b03030d020d0e120a080a11070807110604170f01020702010e150c100515010c0201050a0f05090a0f0518060306 76
    0xb401c0d001f040900581e0001100000600340280d2100201c685d015203030001c9070001200c10303140c0c5074003034405001060701004803044220101754101c8065a078400d28a0300c0302d1000c600101101c0c0c201030040440050030f42aa0b50b24400c0041140340700e55640b00b54160052401d80c1200d8641c1c182d943d164204000c0c4005100880d0058082c6480402002440601c484601807418050712a035a14401010420200054210121951059514800b484203056020207121b16104081000b444c00a012808a0a012008060780503449019001c44e40e1261280d400c40040701405010001a104034911034083e004180242e0b071303902d1f5040e1510002c06605c2e0082241e40c654501505002081c1170055402e41e8104201d40320303003034406080c0016941007400303200c003001040041940c144500799942600507644031003102c02e44056840c203d001c1a1400300120f40720700c9910900d6600140ba20004580103c07280c21010445000701c98642c0c5c0d18800c0308c800c01140074100d80c1c41c1d0307252301b0074000200e14 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 560029586 1250 560028336 560028377
    0x6140d030201020c06010602250803091002010f0533030c1c080706091203020304031409120a08190c240603061506020c040e0613050f062a070201 64
    0x1603200380005810031100d06031440c50b10f18241c0c0020300607400b0f00804030548aa090600d5000103001e03510802450130440450b07070313030720904200d180903241ca8500c0c1a1140d00c03c0d03200c4030700740412880c00c0c0b0490800c2d0030100da101c0000b22210400c1d00c2802000040424006103400d01d040700a4003400e85031940900700030000c40915508200000c0040c2541c0c00a5840f600500600f0b126072800600f00110703081c441180c80c00044c00c481454810800d100210743c000c0a8240d0310b02079114103907980d040da0340100304113890950076207e4a00c50740001e09e040008403806014026610300100a111040d090708807030010390b070300e4003034411000d020014403e0851487d600b40314210416010a0540e42c0b0358038042181d580200401c5109034000d0203201196040c0581d1640602c00c82e002d00c02c040e042558162101c0000e821403c0d8030240f408554104901805406030f1014003005480d1302c4c0ca41031218054400c1032900785035845001038842d15440c031007032098407000307034060b96000c0c041d102084e1103590 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 560030836 1250 560029586 560029609
    0xd23010504050c2104031e111e060a05190905010e100b0109090207030e0a03050d08101a0702120f0304030308090303010308030c0325050703140c06192403020907030614 74
    0x4209407000502c0d061142c1c0c0031f0807d81020513a55071501c0d08403035550b550422484201c0d0090304000b03c3c0e8030150050300090815040410804001000c0e16500c0425840544618041100500380f400e0300007800410340c000d0500c05003100c250f40950880c8180c07003080b110700462260221345107030424001206c1c644c0c09044041e02c0307030034002c0200b0759100001f84030080a5008482c1c3d5840010190801680050b000ba0422000500800d102c0d05100280342940c58003560301580c0240810f480c000d640d074061120a8481800342512440d50100c40b80a0320b0380c0c0329000c207402052503000402c1301142c00001b2079040360f0301b0180f0345045880d88848003020354806000504200c441d1031241004941c2c25101044040c0c02c0e407207069980b101458060503141008165414a22081c03041204025000c5610b035800175144804000181c62025012300921401203c003499a144007081610890007100c80d00503030b8022510070001d035a4a12007182682e405019404030341c40d50070a02c0380309080047c020398 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 560032086 1250 560030836 560030843
    0x30c03020a05061302010314070915031b05071b0803030412030e120319090c140102070905040c0e0f0601020a031b0206190318050a080d23010504050c2104 68
    0x4000084580b80c0d945807200130744060b4100c03a003c00c100800c541e0584555680a1898060314281d881c1038000601a000b140c0310b8107a201c050080a200490301c07982c0b092440069000c4019000403c008004245401041d4215020354883c9400c10400c0c1d91b1000000889400f240103600e15a91503a8108a50300119446803d06440c1c0e01c404003104002d00810000503400d018054603032420711400e1216402c1000d8039400145044607503800b24086958203c01d6030144050041c9109803000101c0c640b01d00383d444541024a00700a01040000f46004041110240081403034540c6401c444480306604c03e45045015030300170000d010000340540311190005441d80d42401901d40d450300030909076840b9142544481e202c100a1841007501071050200001e040700c5102219886507076502d42e038003003c40000e0000715000c6030b060501c0100c2c0d0040070076030020700e07030000d1142125014044054002e004040c4914100360002d0740b0860343c2011f031204091003e6104048840a056044030b01a0190056 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 560033336 1250 560032086 560032093
    0x80a03021e0c0c0102070603090201080c0f1306030212070311090904030201061a0d0501080a0c0b0d0f091a070e13020706090c0e0907080a08030c210705070204200304030c0302 77
    0x41c1110846440a020180b414102902900080e24002410140160031480500d46421112400350b684001071544c041e500010780c0350b0b540410031540d8054080d040588540404456003c0b80d10350f85600500791440480490300d0003911070210640c10340d14102900019901c050100c02420300e401526540c0007401390000081e900d0700c450400c00180c3d4280888580c5010000780180024198030070780340100203480240158030202e907100503080ca1a445014845000072500e0b0f03242d2102c603841703160100d16070351082004160341c2c078022412213504081c01280901003000140750078047d4006074280751000313105213a020072800000000390010441a99001ea4581c1d52800007015000840e024001000c100405860b00c03620b56407a022041d0442ca0040c1c00c05020038000803402010760780c001c1421415146c541046840c2640c0504003641140189101041404070854000004121183c000c0e107041c44040007246400007260030004103075124a10030000100443e01c071310440a0810300c00c3c03058 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 560034586 1250 560033336 560033377
    0x3050a14030117060903210a271109160309170d060825030b09030c07170c041a09131505180a0209040308101805011e03080a0302 57
    0x2142841d4000341c000b071203240c6010040340641c50081003074075802540d0400852500d040e00e0480c4901012905001c08900d40c3d0101149420341190084003017100e9038003004880c0060039941440a0100e5001500c144420b5a46003440381400b0918a1282c0b40c900981d41c807140700c26200300c008042d240c0c002c1c0e92540303901c6440148580040020910b0900c8000701103080c0782803400c114209041c511820f001d44031a02e10f4002d081d00754000c0710048941010300c0c103149543e00c0d110103046129680120310305000d10100030640d50324122012515240020032554240f14190621040380e1510a03c0340080c8030380d00c2c1395015460040c87c0c89501184030603880f03050020303e40c1c62540c00d0f84640300700014907481d03204010080c80315040b20340d800c88091006000d0b00d0495000300340c14007000740c006806c001242e4009202500c0c0d40519174014001c008110300c1180d42c0700d05200040c40d00307000e800b400002400d0b6080c0c1d0b0340e51b843c001c1d2080c1d03900b08070314602e0000840310070303002940f00c80c084045030f0012020 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 560035836 1250 560034586 560034617
    0xa030f051e190509031e160b070507140105180c01090902090303041805150114070b040221071802040f091a0a09150803030c041a160c03030201050f07080403050a 71
    0x1da140141542802140c81e12050015412001074a182d10b4142d61400e0103180407d2404580054440e03030000740340c419a88801901b2036040c403a00d0000352402081c0328000c611444158451481100040900d0104d180c2d50040151101d15100783e00340040c80640d4284118032095004181d01c0f00000c2c120b9141a944440030b0a0248102c2c0168405c913664400704240340c4a40c4174600c61420092904011200c0500d5910340940920a0040c00a2074000001421502d481341510b820810f084400c0c404584c00c10451581d41480e40501d2948220030180070f00e00a045009680640e400741c854034460703d04000c0070740d00500350300800d110690f031011840d00f9103407285010b0001910240102150148848442e01d800ca1166400b5070300b40c0d4020020482d10304000d0040d2806d442c4400780750a04103584003000d4446000e1440c0781c0c24541c10003028038040285104000088911a030001d205648e5041074959200718100c90040224003120700050009202d00b00408072500c90f8205207818034403140 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 560037086 1250 560035836 560035841
    0x604060312020a0507050301180b09100501080c0f0d020a150210090b0901150305030405150c07060f02060903160b06041d030306190f0e040c030510020a030f051e19 72
    0x503100400360700080f0100091010600414020780350a400901079034402101c4071205040081c00a881d2000840100d1f207045001d101400c1c0140b5100780520895071541c42e800c3c0c17500044008607204481c40c804079005400c0103c05200d40d55002065000403500d4114a88483c100c0c4e140340b1400c5000c0c908103802c01c00344922820b20a00e01039504a809841d101d0001c60858070b0781d020020380120b202104000045d800030450303003542d0058400c0e0800554482e20003140340134022031000f09000310b0b02c01045080d8059840704141c2090382c202e841c2e54640721011526841100103131039034200c00d200848c021490b0b000403603400820242000410011040074503424202c0011100740c1d85e0000001d1148601d095400300f222013420004d100b110503d0810303a0ba136101014860303801d4140c04400000c050108000d0f5460065401070151555a42503030700590081d88100ba00300c011a24152040c440d072411445034500c80c10f0b003d0350f0020700704202403000510107030003091101058070700d00b4034100008850 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 560038336 1250 560037086 560037113
    0x80c10210b012c010801051c030f0201020d0615020601050d0c090b0f0409030201142409040f02030a0501050a060b09060304061a1e0909031e0a1715031011070b06040603 74
    0x302c409032a070403c0000042040506a02c040d00c9941004a440c21000c01126007801c89179050800040c110482030050740a800340ca01c29001e41480c4c5000022044401e1041107492000c035400c1d54a10380c0c862040141e140b4010201500310200e40d041444458481d91000300700c82d400a00b100140101000000c00341c071100300040340142d448501c5d0811410340d00f42030031313040150904078610052000c0c065007103c52a0504e81c921419900000c281804496910010010340260030b071001d00001e8240070b03010b000c05982c0042420301d00708000a0005008099865946004000c60310319280ca46401b00500034409a0024110035204184101c0c0d9880c11f81c2284408103205a00039400c18004008100c100241381c641190420840b03e900700204400041190800000f025110712407080102d034019114200d0501003034105090151000c00703801440340302d40040f0111480001083e1505040c0ca0380c1c6001115400014000800042c00b59081250700c030102030400109541c1c1c2c1e03103c00b10607103001d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 560039586 1250 560038336 560038397
    0x150a030519060f02070602090f010509010f031e14010e0106050405130218060c0a031103070f02122515020c03031c0e250e040c03080a021006080c10210b01 68
    0x141c02c48d40c1e040c400303084580700500342882400c0c449400000307041c4001441b000c5040580d103202c82000d100c04d82e0b00c902c54a802080d020042026640c41036101c41000f8050724401012403000007659a10a00c12201602c4001d40311000354842c201c016070203500502d49a00080d03070f8280f0303020324a84a550280068204c480c004040c004070314280540581c400f07528003d180d0700100206004141d03001c0c60741d1449541513508041c130b215018286401c2c0f07040c0100e489130043c0388030350b4903035a054040400c2717050720150a28031184040400050340e44011005800d030301608144070031a400d0b003e0b20354050f80404081f6001c18080c880014081c00c0c4141c20a407800d0604000743e4880706031a4810440d005040d0134004103100303090940f20125198094800103040d10070000d20140c03114800d10090001c81405801030108640301c0c1000c41c0c0343c00700440460300904c82030341ea89501c14480e10501d0704040b1015624021035081d4041c2c10b002d0603441003046c4c18481e02d2885890403600950102030380000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 560040836 1250 560039586 560039591
    0xf0912040b030c0c012d090507210b070c021309120503071413062a060504030c0f030206190b0114160209040836120f0a0803150a030519060f020706 65
    0x20f10010741100c4149418a02c4058900790a11000035000164901642c100c110441d0343c040840c0e03c0782b2a41d000841000b0001c12007078041c00166500501d40c0800644200c44510404400080ca0000c6030400c9001a150f0300c00c03a000004039034003032401560030180f246407842121902c64019400c66210740c0c1c80d6140444440070402c0216442010991008406141742c01029040c15000f464001e00d20400380603a565540440c00309401040d85441445e48207a00101400407400c0103520390800b01c803d00d0741c00d8010b4190500c00781c110303c102901044140c480303e10604140e001c0d017407aa0880f0080e025640d20041024001d6a1030002152255206240d580d03682c5295a02c0c04241d501d82c0005a503160960649a104d02034442c1c161160481c01a140e0703407100070300d4880301482d2004646000d40c407405920423600030710084c0002180700b060510f03801400c2621403030911010b5080ba10000e000364002c90010300c400402298052610f5004610204e5031400c800da21100300c0e80000001c80e10240e = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 560042086 1250 560040836 560040881
    0x1d15060c0138060d11070b0702010906050603010c17040212121e0901050d0906060f080307020901050d020f1011030d020a0305060405010324020f0c03030f0912040b030c0c01 76
    0x2071261040b0204420480c103041008070094000c1400740c00b914180140c5185c0f01c0440c200030040c0c24040c0c544503608024041124104040040d00a180c049416074141741050b00044d181d090501038001306071140d56940e0030700308200c040d8502c1181c001e00200d034400b100702d241043c0c08a003007000108141c03001c2000c6036030f1245000480040314000c1c41c449032000b01070262106980e005001c0e190700c96118140421290010301d800c0b80100b03c03a4200600e4200f58490210b90100008041c0c04103c0c070a0368045a0381e40c8400c1000380003120402c1c000c0d88441c0000c2c010383c4034102034142800d5500b0904000d801100d0b001103d9086801c04a44882c1d0643c0c04210180c807554580940394000c44241c1d020817040d41543c98001daa041e2045170318000c0b52a244000c0c20640c4207a0480d4000d10241c0c48203504c8000d40f280e03a548950080c3c90000104840f0408200c498401007219070410306261140c61501d40350914480e61500010b00d18080300900340100084030801b8050803000d503080362801003040 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 560043336 1250 560042086 560042141
    0xf1f44070e010303120b120a03180b07050705012a0302060a1d060a11070507030b0103020910150c060e100c02190c051302160f020a1d15060c01 63
    0xa04203500000740c091840c0c0c0108040781d0840f5030700c2000c0311a5100400e466400c8404651640e402c2c00342000c051052a5003441410b5210200d5001c655584016050f0070340e648080b45018020b561001d005038020381020042580194100841c03442d003155140018881d001418110845800382500560086810401030b403106200d16203101a00058110203c1c141c008c00541d100c41c0100300c1c90f0003a60b00c000403a0310303100003400e803a00141e0000484241c0c64503480d11690221003803004070701402c0c1d5203000c201344200446070300c4141e84098a150406001e0110b040751900e072500c80c15a178043d504d03c4134150050061210403540712480c00c1c0030800c00e1800400a1900700d001d1064500d140d20b08090340001644555400300711030701100c00300c00707811f03c001981c802846216001d04050354403400765010030042c031000c0070b403c50003228080505603981c042000406262a45a104840c10308002410143d504006841c282005002d107400d0842040c1079608442d0340040103d42c2d80095160510304 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 560044586 1250 560043336 560043343
    0x60a050a090b040c0302070f030c020118180b011119080702040e010e0d0e01020307150e1c0206070f0507060f09050d020f2103040b0705130308030f1f44 67
    0x480c481417404501e000499211048a201000c40060030481d8182412041d60304ca42c0b201c00407a4000501c030000c041d03844800050400c0c1e80200078001c90f04042010810b580603a00e100c050034040c002500001102c545201c414121a001c12034082000b070003000d01580b680d115420001035014000242c0001d20025030345018420b0200f40200700750418507030000d903400710580308500c0e800030006501c1d641090401025065454036504580715202012440b2400d0800c1e46582c0c1c016a000c1c1d9030b090301e404008895011020449a0200742d081000100044099102230307000c010103000003030030456660303640782810160213100c00164810414000900d030103100300001802040e5a04a1040001d0700c03070704640c00020809450301181c00000b81d9414068411904a00741040400305140d45034038240340d0310303082a00c00e000040c1005c0e0016400c0c0c8010650b20740904088051242854542000c0c01c0c3c00059550700d40740c541c1c205101c004050041c101000c08000359402000d1a65180c43c03906528 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 560045836 1250 560044586 560044601
    0x501030b1509040c1e02031b0606092202031f0c05070b060405181501060807020a0f0206030903130b18030a0c051c0b0709170a1a060a050a090b04 64
    0x300d0188016010121035072402110a1018180d03400300e1400c451030b6050302c404258002403001d5040f002120403100e0360200040404c2a09020b103191b0301075041280b0303030345c40d02c0c115010390b001035808010a03000640700c108500c40c0c409210b504c100040050380400d040c42c0060074880403080020702d0a130944045070051000560a0745041400e01c075040e00d03654451440030301864010307070780c4001045900d0450b4508581104064003212100c0000c3c1d4003501900109128620016400c0000300310b11520205003a420aa008040065105c189408000d4aa8406410040b0303a10081002700d01442800e26204014074005105c29110600c03410480c800d00050040369100350000031103880080c441840f03003801d030307070058a200359144030300840c800c11001c80102c0a0000d20b011070412401a51000e01c8400780d4021001c03148498036070b114040e980380e4802400401c8140030351050540342c4020076445a00200007044a2174040e5200c005c10070518803500303c1c602c41d0340c403000c40070111304050003002c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 560047086 1250 560045836 560045839
    0x100909020102060114150412050c010e01020637020415030501030213020a090512160b0f120604180b070e01080609010302040b0d050319020f0706050913020c10060501030b 75
    0x8a8405500003501c58205008a210408408142c5d030621340b9200c4500494000c0c07544816a11501e0b1203d030313448003c01c0309040b030341031140700303151046075100c0e910060910006030014030207038440c2c002006052800481819070010784040b1340c4440340c481c071142c500a42000b00016500c4d4105a0040501c04840b0500c00905082400400c01a262400142160f11907583c0040c1c8030040c5101c112011009030780010345c06202e40003031101b21000031813001602002c0102030105265a203400c103e0b140922200c00f00b104405000c03043c0c00d1600e103640e4680c0104001c0c0700041d08180008200f011034044842560f4a615580807c996250449060031210800342003d0b2641d01d031003000903108501c1400000c2c0260380b00e2441501d1a102c01c131580c118a03603c00d080c0c0b03807507880c1842d0490b03004940c0310807000103118012082d049a14049011004e682c0d480c0c0d0b80b1840e08801c04c0901030034110f8400304443c010350820030719000384070a0103140104428024089031051400000400780d800000405 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 560048336 1250 560047086 560047091
    0x90f0b030f04020d2f0f010306081009020d050a03020109051002040510140d09050c1c020a0314072c1602060a1802151905030108060721020d051009 65
    0x2003a01000d0a441c16070060381140e030311805860a20307000c0c0c0b00c0722883c14a821082e01e05c40000040801c0598104c006560684e05110309910340e80c0110140c8400744103003d0a504a015440c010704141d07001640054001744c045660303038041c3d5560618000030310710140c1c0140d40d84c0420f04104002444080036041c044e03a1b09504042c20080018101002205d142c0180079101101081c902d0340141030360040c0e090782d8001c200180e09414040e4031358400b0803001d44503141034805114010045140f0440694010300147c0d00f044c02c555803c1481c0d444105041590310807070100140d0341c0c0c80c02c04207484404030203420000203409001c20802c80c002c0545860030801d44038018071407450f80010f1403580b1202041021a030040f032180602d00682c4075400c040d40145180785001d41e0480103000a142c41d02080300c1d80481c40e1340c0c0c80b504603242d00003800f668600f500300390045040c852003980d031580600d00b454504442180745040320303412644030f4948415541d07261401c00408080000307130300c802000340d96410f = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 560049586 1250 560048336 560048341
    0x160305010f031527060e10020f0d05040501020f030709150e031b01140c0c090105040905120304030203161b0605190815040e062d070309060e0d090f0b03 67
    0x12408442004200f400d80541e42d6646910012002034105a0040000d610300e440507003141003540181085440c000d00d540300c0c500c1d022202021902c21074105c0d10042d89000e09000d840c11090002d050007610580c1c1942d001d100c146014010302c0000c50013801c07103444542102d840c022140c8615000c6034a0102840700074408190b6030b440110344a0542520500304e202060160790060300c061071141c6600e110051701181302034000700001100300f1844811203140442e0380c0c0c1c9404020a58952810060058115100381441e1114903006950860700c6030050b0390601403402405035181203407000640f52032003181014550440100c1024024042c144ad05501d0441054200511000c80f40118020800c2400c0011a12100c55944141155005009101011500f10380a580b08000c0d1000c424814100306203a04d10b0811000c0500ea480a0a03084841e603968410245c004060080c4142c40040d00e80c505000c02190901012000e08110340b510200581050b003010550650742e0008110301104005 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 560050836 1250 560049586 560049593
    0x50604180516210e070621061511012d0507020c030c0f0f10111204031a07050904051006140c06131a01080a170304121b0506160305010f03 61
    0x1d0301030f0420f4001030080c0ca461072280340720014109940c60300840d00885401264540c1d020760104103c032446040d4040c01c03182c0d4204034048400d41c0c800c16020440c00c40c07502c1c01c50341c0248100b595880007400001850700e6020300e5451150200d10092540450001c07007440c41d001c00340300712070f00178016200600c2031124a001003690344039003a00140c410158040f048200341d580c272003160318601000e88100c56040c5500c4000c1c00014446400320360742d003d80d461254854174034506550031203030000074003501c4070600b9200d2452540d0141c0304030200001046000004e03111070040c3d600500c84101c002c80e20703901d001c100501504550444c1e90351300ca802c0005036125840044c4143c1c00040c0c4640d5502480701c0c0c2c1c5002281e2845804d52480350f90fa80d0f0703000280070300001c51032920241c05814503500c919600e031300c03008981c40100d6004140340544604205101d2107800b000b02500141100c00f1039000c003c0e101c1a01c0c0a4085450210490000304c0c0d01c40180d41c540100c0303006050541e2003010850846c0d4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 560052086 1250 560050836 560050847
    0x906081b09060f13020304030305010b0f0703080a06091d06010605041211221b032c01230103060f020906030106030209010c060c02030c2b0c0c050604180516 69
    0x100991240c5001c1022507410341c3c55520346500c3d02001000103410002e49007084003e900100d60030303008030746090300025900b203e00c3c04a030484000c602038503182c20320307540d000e449024010b030041d04690b5550102103000f01039440383c0703e03c040c0411030103403100400c084501d150000c16001102080b1082c0420000e030101004010803059116040480b85242d18000c0741c00c10503002c2015600d200c40c01e0340c000484942e82c0c00b82490801201d00d03951261605c0d00b041c1c1c1503400000800921205800f00d185400070103142205010440000110f089420840084180d404810050f001d000300800100308101d20f0384600c0b001001d03580d0040d81803031681c2000601c9400144202c1c4181034000644a27a42d03842400d041403620743c058010000307070f030725088004d40d80d070408001c40310380348240480b80858154054490002c103011058803424100320400449240784d555504940c0701d04542c00c042002d64800e40540054020f9045650250034581e01071810303250f01500302e144940c402011000300b241d100 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 560053336 1250 560052086 560052133
    0x40b0c091005070206130f0914070509040c090e09010e060a090506010302100c020303070807230715140412030f0f02101802180a0b030c180718030804090608 69
    0x2d082c81030f02d458040c00481d1951240040146448040020104840b440e544e2994251544500300b0007a90307800c50501c0321301000698110000c60f4051042103894545508000090286031800c2040c0035900cec0e00700c00105100340c8440710265154410291211000c00030554804150081402102800d03100e40d504d441c0c040c00068083e10311001646526800b43c0b0f9000503041e405012269514050700300304816411601044900c0300080b95100320000e1940c9412120040000180014a1501d425691418043c42041c030a01c01e24044100c200b42c494405040289001c4030f03c101100329038540102402d110300031003c2407050150015040303550000e420004580468400a80d00652034401040c8004519000754007000c44880304c101d02c0014150701f4000d90460000f40101e0312524209a11214600b079560b0f00000f840c0d02054103241c0c0c0215681e005404d60401c221026100600ca001c140d2032500151428200000c00708041102c40c03080800410800c000b804890844404100c2440c480c2c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 560054586 1250 560053336 560053369
    0xd020f120307030c14040308090f010309050706110f07140a0e100506030a090506090124050105030a1505031b1e1c060f15150c030c06020304031412040b0c09 69
    0x4800c13040183d28040c4a4450003c403541c6101a12141c1e41d14004066501102c80ea90040c0311503c2403455550190049218460b805005061150f003401c00803541c08032040e030301038402d100c2c0ca10391b011a86818401c20b0090100d82c4118060a09180c051180d800c550303501081125003c00c041281da0b001025065059a0048880f070b5500c0e00c80d070f20210041c060130b20000d4000d0041c1000c0c4034000c101548440b8008003d0042e441c4002c00001012014200c903100300360100300c0420024404840540c81040e412200000e040281e94407600482c1c0381040b0101584803084440d40b50b0070881c03404070090343c183c03200c2d84880f00d5603005d850b021070a40c503004001c0101c000b042c444181c0800245400c0030408882148080101070000c1d1651141c075112446184101300c0f82c0d44041c0300003449145c038001c0700d47d00340c1c403070004036015640c416000b50300c014030a60030404000452030308040b1034801011180c0da0125409564201401e00c800503003030140c980106044104907480c03160700c40c1c04c1403c103240321 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 560055836 1250 560054586 560054591
    0x31c021009081e0c0601060905151e07030918020304110607020d061a040f020307090b1303120c05010b0406051c1509060e070801020f030f0a0f0903020d020f12030703 73
    0x403502d010141d0303001c0c0c0ba184007840744003414440b245200701d40c0605881c00500003124003e984c0c406041d134030285640100c0da00b10802c2c5c059620b41c0b0046000800e05044a084414589821482e40c01c410303070404002100001d000701001c01940d0034907a0055000307004900e0131461030802d0764038000700c10021441395000b21800714403c001e42d5114191440c1c00361300003405204403400c024558140e08044881c49200e540b50890803500c2d00d40381c0c0f023524898021500c070780e220b040c10310340d40d4803190304207a001311400c1180f03c3c2d002c000115800d440c0e00c0c1c0180e040d158881400398031b20380182595020740302140658504082000943e9607691126444441e000845482c4502800c00850410311407284851640c00c003444c0d80d040011550010312006290390980e03151646480740b246c240e02c18940d2a102d040001d20100780c418101e04419500203d600c0c50000388c0700000031400080e144808000c1c1c0258011042e09031405805210f0003640c4060301025020030000c00b01103980b81c2c007003c4d100404040d0f = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 560057086 1250 560055836 560055851
    0x315150909160806060a060518151b030304060b1906030b030a0605090f0607050c0303010303050d0b040c03091106120a090501091b03051b030c13061208030105031c0210 74
    0x80c00340446141c400340c81416030307039203c1150503a202015a40f43e40203048403600094030b1403007081500c401034010a0315400c0c05031498100054007421145100104a0800000300d5500528140740c0d000300c000d034051501c80c6400e0078004222500030386039502821150b2440011074400ca0301c0d040685489013400520350240d01c0c0400d15003190303140010002072815041c004c600d1400540001840c0282044a986a031030450841d51400f40c070700b1700d16569005000520004e40500083d000c4400f00d9000028802541c60010b81620200d41312035000c80d42d0307110a8414802007034000c0b62445015079405251001840b9040c95401008040038407065070382c214041044000e402078120560480c42006d940055841408001c0c0745601c0221514822100665090084064021003500009020308800004242841204501c400613240315a5603400080b410b5a51a40711850450103072081c607480350b041400741840c2c8111310606954510352410800703070b116030000e03121108240398034000c02c03640e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 560058336 1250 560057086 560057101
    0x806060108250336030f0302070b0f04170301060c02120a05031b06090a031e21090b010f0e060d08120f270616020c030d090503151509 59
    0x6402c207071800700a0400c80710100599158000c004142d03201e8150b850220f00300b83d13850160b4203003484400d005246143d42500464010100403092000c1800c0162802e45903949185c41104110340c01034052040b002030000307200d0f032100c0e0055030200c26080c20346594180130011b007034100260360082c480d005142c0c94100c00f510621645a4450b0701004070780e01d400c5201d00d0040c1c80d12a4000c55a482e21403000010b83c40c12002550a0145401d91518060360701402c05d040f402e003100700c56400c2400391501d00140140c60300184801c3c01401490005910401403511801c8000103a100d580007181001040c41012982001c19420040481c0c030040c90322403500e0151282d01070103002010032024402013160340c812480e20b0510592203d0b4140d40076002c030390402c162243c148030400038a0f9100e100052405042c41c10307031000b00c0e2050700441d0611401180040d242c543c17000d0800000a10040c1d00300100d04041041e000e10680c1081445a24030f07001c0140e51075904802006072060380400042080d1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 560059586 1250 560058336 560058361
    0x1602010908270d060c08100311040e032205100203030108070b211302041b0c200d05010f0506030d0215100306141b0c03040314070b0d050708010f0806060108 69
    0x540b101409440a062241c00e08a0040c203a601e003640c08502c003840003614040000c1030f80d00a40b940808035a0700341c00ca40d02800b0040006248841d8140b204000c100c01c00e55080e580800301d10b04401601d0600ea00f060305012102c0c40c400721050a640c41400144026040865520155960388031855110f071142c8407c40d8280d840841c5038092560f0050510000120a40c89004402c0c020340b001d0106e00d030494001041d0b000110740d010000b4240000d070400081440c2c02c0d0003081015403081c0c1441c1e440703800002d1002d50740d44004841603035403a4220a5111a140a0507034491b000710040c0003e5001000003a440c0c400d003061603c050304112000a00c1d04840b160f48502440d000722003003001003290080000c2c3e00c02c060700c0ca076409039000e00001300c124060200302c801c60104403000e0350900c1c1c6155240344541c403844204402a01564001280741c050a0000d4107040306403403004142c6003044440a0200d46068000c540960094101480548000561107801090070702c4c0a80842d075518010011 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 560060836 1250 560059586 560059657
    0x11e020705091b0c10060605070f021212041409070306180c170106121113290309070303090605040b0f0904110d060e060a12140102130303081602010908 67
    0xc42c51008604d81203d0301c8002000e0360500d003190410000d550f04e0700400c5d161070082c01001003100c0144c10000005040c50011240203400302c0c03045404c1740064955045c007640140e0404252480310462070001d528009854a4103d80981010000c96080c65a00b00350304082c8004902d805485030600d5080d14401d000000305201a80c14506039540c49540003441a42c13200704184406007000d5012089042c1c2038201c5402c4680d544144030441c1c5030281c61840c410701c03958207540b1802a4101c0c854035110036030003184225920000307080d4480c254540a810401950443c00c00c0090510040c811550001c0440715442c18910b00d20391940c030064000b9021348001100d035100d100d00410b40d24055481900a00e0655103104403404031a0f40f40f0003802030140c21841281103455003c07000d9004195440e0b2400803545040001624040c0c00000c1c02c00d00d5005c0e40d0046001070b46540400c0b04c0030724501107000310520948001c0c0315544241e02c0344240da01600c041c4200204140c48914041d0581051894 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 560062086 1250 560060836 560060881
    0x1404030c060806030f070501050d11070602031f091406010e2206180b0a060c0503040b04031112011a0f1306080c0a0522050705091905011e02070509 65
    0x120450301c440c40100500401d403000e070f0184c410710300785018483c0c003c40c240d000e4420683d111400e103005180d02c200540046a907202038200c0800c10b803804940e10b400118810300380c103400440142c0d070100013080740007030035445181d55502e040e00c8001303420241039150390002c1d0240b0f0310380354210082000070084000040480c0003201d258200d03510758070303003a0400390465190231034000c001d8000c03c0c00d40d8242d500d0b01848036400f003407640c018041d075409180b134401c03024050401c41e801d1644444103108513500603002514080c1c92600e001803640380c4405842540741d03907003000740702c4480b6040405000c04402d940d500c0c41000064101e513a1600c40542c072103030000c4410028040503079688840303a118500500e445010348040780010401d03040c1400c40c403520b01c51250141d0756442d91a20383c50001c060290610342007040c200f118500c40c2e92501c440400171542402840d4240e0714002c000b4203180e001d4102407000c600039190380004940c0210b10300d0704490068821483e075582d01c11030801007181d06031104 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 560063336 1250 560062086 560062103
    0x70e0709030b042d1416030f321b130903030e150a0c1b12231201090b0f0909030c070f060206070203120105060711041b03110a050901140403 62
    0x4043c06519640c000751403074012011702404004c0e081c4819160302d21907020310000000c2403010000100c2d0300c0320b1800c0c918043c030f03440924811011415401048411020030107145018800d540114083c002d809904d003081170585580d8140c800800d0181800b4440a0081c0c0d64401822040c14082d0700441c150706108016117218480d40d87e0081c003e00000d42e40d180c0c90034a003818034500c883c0507103816001d41c16040b5031086141c0180d964000354582010300081004406544c0b41d0000001c00c5041c07414020b041c0e0080c0d21003110403240e98003820142e016010181c20005241101c1e00e501c03072210b0100300709840115095417041b040a14510561032065041e00c2400c2000418900320035035441903519583c01c2d01d196846a120480c4e59008100c001030600491300010030182c5840c40007041210f12070303112070b00c10076106000902200c50841010a50180811a403900395605100781c0c0c0407008041c0d640742c20241c06500c024920b005201ca010b040c009030031320708034403070004030207480013198400004c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 560064586 1250 560063336 560063393
    0x9010c022115070818071a07060c021c0e0d02090c030610050f0d0c020a0212030307020d1701031b170309010f05070b0c0a030e030c030c070e0709030b04 67
    0xc4100405401c0002030080c06549000c10350300d964414003d0b019561043e00d1925000d10341c00fa244c8142000510500c9880710001d100c2408070005400c00000110703181d240c2ca07980c10b085040ea0b0710700d540d510440d0440c4000c2c1003000c181020440320541c243c94007040001e2041c1c04590b10070744004019601400b00004c0102422000c002544501001c0d40c0e1092401043d80b010380b12400380c40091464490144a20050f44004c2d9000c0c1d010941ca134811100c440140b900440d0603a40c16082156407074100000f0002156010030880e03808024500d4091300300c2940c040b141c1e0302d40301c042c00000c2140030480e01c50294032001200c0200507140292030f05040c20b102d511a6980c030342c007904c851804150003284001c01c090117030f020f0302c00040d004114103506595007080403040340c1c00a0110400d2640d40c90500642d050100003410f41d1801e84001182d9842d034405d15140350843d550b100d0650002e2080400074103ea00c2244003080b2607020080c1c00e407a0f01c480c85c1070a80310b0b1030401e90107800d80502c10b0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 560065836 1250 560064586 560064619
    0x415092613080d0228062307030501050108060102030702090c03090a080406030605030c01030504120806011101020c0601210503160503090405040803071107080d05180d0f05010609060609030809010c02 88
    0x140e8192a211640171580740c2944990b90450349030b44850017580000d139410b80da401280c0d260300207030a03d10413409103c05e0050f00ca680900d43c0e050682e18a0002640c81005120a50300031240c560080e0b02400254203000f000d03400584800c3e401000820340381e1021021a070850000c100f164000d580c400d04d400d4075180c45140042c002c01092041501c60300c02e15002c10070550286c440e00f03021700e802c404100410100b001056840202c003400c25410050f1082405020300c40a101401c4a4103007034014060552400074501c6580095804460311a100c407000e00d0001000001180c0010089134421045607030181401b42c15401101c0d20b050b002810141000108040c4500862240c411a200c00441d2800b01c0142035446081b40101d9140e80c1c810b01e01c61200341e004201030840011200981c000c81c460755008543d00004005e012942c01c6415001201003142c01c1c000c2c0400b0741040b10301005424a85540101204013510001e041d0000001d840580350344180c1d002107181c3d40140000944018814 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 560067086 1250 560065836 560065843
    0x10605030d0318080a0c0b0f0601050f130e011d09010b010e0933010f090305191506030c0512160506030916060e0a050f0a05062d03041509261308 64
    0x14211440244c4000150b160250b0202c254010301d030603520f80781020b011503d00096937000140c1031010302d00c0070b03d000031030103e41c1000c140a0018407042c0310810b00c040c80802d101500103060700b41180d0400500702840c0c1d070701035056a6900000c0b60002025160401044d0705400c60240902d401c415010020f10300400401040e00c2d681020380e18000003442c134407022110140781d03020042050300903629070800d020086040c8020b0034001c442c1c04807050035189050045405551080700c42c50b84990303041005281041c0100c02070700314140070341407504600d011901c50f0744e81406082d01c19400440030802e480d90400c40c60004a08103c40d507007403162500406410340c00203000c09446400302d12004255402c2000c40a43c60001c05484038510504001c01c01030290410020305103800103000507240250550100380781c002030515905941c0b030415051110505461441c9031643e1410043c00700000b900300c0c220302600941c9240d40d10082d81ca41c61181c502c0d41700740d5540201d001d03050f4001082186012 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 560068336 1250 560067086 560067107
    0xf1101090e04051507020a0c15051b01090314032511010203070915050406140702010302120408070c09050411040e07081e060f06031b0312030a0504060e010605030d0318080a 76
    0x5405000c0940c3e160758040f6656010500c008140c418088e00030000160f010102c0e03080d0011605140d8241411800d503903002049900701da0680740c0d105c956440503d5000301c080b00d000d84000300e03014618030782510700c4000704450384000c0c9141004070a006518a11030381e62000f4403100f4000139580c03414000001400b1003054054000c40307909107010011041e00400807981264110b84030a4803040348003c6000854010702d0003a814140c003040500451102d40c54402c1c4594411510741c0d480d48124108104c3d03601a0742c2004010524100c20312004c81c9030f010101034404401c440110f18a80380010703281c1003c09ca07038030a0034584030703d100085000500c3d6480c551804001d80c1207407000d41c0c0c4e03a440c52408210a03215540c054004907000a900888800301105000c0c025048903104003283d00a07418079401100d402002c2030341c58050004200550107001802d1402500038407242d03003080002074a0f02d00c2e840c0a9010b15aa800c15400c1240c4a040b48044030380e0008600e0751250029070b809082e900c201c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 560069586 1250 560068336 560068363
    0x50c010e0603070905010315080f0d020d1704200405090102040608060a120b070201060e0f04020f0a0317070212030307110712030c15150305010c030c09030f1101090e0405 75
    0x10380540c0301503400c041c0305a0303108007841d03aa140507452811006400504005191503c013071f080307540220751850b01f0019044018180d0f001006c000074200c9009042114901c118410440454502c0760540c400d00c10140c0c0240d005044c6100c2c4070032a03441c0032807800c0f088050641107400c0500b04090302d00d0640c013610413100c00b501d500940d661072001b085070186190207000400501e0384183c002045e01c40005030b603c2022030000040883e1694107006ca1a1411144102401c3c03031001040118103118421815000b4140c800342c0603641199600c0c103880c3d1103440c2c0c61000340d0b80031a000080d503844c80d0080010300c4040003034907503a0918507001000c1d1010400d0721314803482040c0e07002503082d01090a07205021b07003558404003280c60a0740c0f104120f85d0055070345061aa1560301c4840d858083c00c2544004600c180e00001d1402c500c0718002c0c00b51a10703e5031241c288103000c201000410020351040180360790000f83c4000d40c42c038000c01690303081c600d5000700c440c0285010070402000343c00510038600000d03 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 560070836 1250 560069586 560069597
    0xe03030c16180203060603010902030c070503030a0c09290c07050d060b0109080a11010804020a031a16050901050d09030215040b011a090117060f0607230102030103030c0b0606090607050c01 83
    0x15042d0300403040e440140c400300c0c0c1061040004000d81400d0303901940d0010051411580b03006181d03110940b95420035555803c0c901c1c1d0710600341903c0c41d0002c262500504002d80100061803c84004000c5141044107c0382c00fa6000a01080b004d5814001a40500401092140d0120703c508100d001400203400c0381c0c5c081080040041001040098500c0c1c545502c0034a41c4014654140112181003014004a80114110401000013110781c10b0368845c02e10003d0b00f8031a0341c505480031030780306030308400300005102041152110a90340303c02101c0d06503202c4400419040f240d450200e1601c00782d48a001804266081403008100b403a9082a0489000c14009140304079006100081882089507140c080307186140080c4a02c0d00c40310300c1300d90000c0020050b54109000c80007003040c0341d02c401c800700c98003070340710803903400099215808174034110300e0900840c259810350740c01170502d1507490300241400c100c001c00206d040e0380d51412039445e98009041c1c2902d608041c0390890b550003402484030702146 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 560071942 1106 560070836 560070869
    0xf011b03110f0d06050d030f0201052d0c0f1611030304140d0510111201080d0e09090c030703082709011205030c01140f09030703020703030e03030c16 66
    0x34088e407200d1641c810740d04002401c44200410340070b252543c0644900107001a040172400f004801980d4880d65207900300880c20320700413070000481c5143c0c0050300040101c2c1607200d07000894032823030080003000302e03402c109612800307240552000ca104449920304a8034101010501190156003511035000600e02030100742c2d443c94042c80d0944000040300b032401401e0042041c0104200c40103003423546a004002482c8a161790415807150b140c082c00705400b000c00344042140004020b003210f01181d62480e0041064200c900e41e240103011201c4203212000d550031160142040040c40d400003a1700b0100c01c00d15440290304107558074801400300c44020f40d824810148844604c800c40d48151510500030119070380300070441549034100f440b02c0740001b900000c11b0310503a9454100b0b80314a034150b0000ca0f10714020070007003000c9482054207d44c034003517048140c071058910719491000b901 = true := by decide +kernel

theorem cover : BRFrame.Cov 559892086 560071942 := by
  have h0 := BRFrame.cov_init 559892086
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 559892086 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 559892086 ≤ n) (h2 : n < 560071942) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
