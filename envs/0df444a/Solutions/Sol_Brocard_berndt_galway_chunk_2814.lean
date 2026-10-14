-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2814
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:49:24.586586+00:00
-- url     : https://prove2.me/submissions/e443eaa3-e203-412a-a6e3-fd888566eb12

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 505935251 ≤ n < 506115107 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 505936501 1250 505935251 505935263
    0x4180510210602040b0c010e060415180c080c01120b0603071b06050103140f07122406080c12030306130e0709050a0c020105100303080601120e01150906080102160807 73
    0x720400091000d100610180010b010000c1e1105003001c80c050944d8010244071449800c0b08060100181e0b100d002e54454110030700012844141d9000e10040d5205a24005010b21400307020008000320080340c42403125100303070380f030341c1980700740e4019136013511a2844025000f0300c007040002c101900c0380c00761182c104032142424150700010b032038000a403074080c6c105a07180802190340c041c102c2002c10400f8032a50700c1d2401b80c1422443c000c1042c1408107458805010a034018401124003071486180300c002d007284940070440c00351566a000d5845811b480000d0041d481d000003c00840f60000549200e40c1004095203505058011900d000d4a07069242090a200d41000803a080301d1700d0144a1040844003030000d004441241c0c0207081d210003610704a0000e40d4050b080c0b02203584884100d502c03240a00709a10b002c00300380407071001031807001d014001c2c1d5441c00100c901c1c0024005444400c45810301c206001103611515a14202c0c40749000310010801400c0d2624000707034620000c0d01e2030a01501e = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 505937751 1250 505936501 505936559
    0x203070507020d050d0e0d0803010b0f07050a05070806070c1e0611040305012c0d0f09030b0705070309081606031805070e0f012702090d150204180510 66
    0x2d40454150101240100c42c3e07904510708584440f40d0065620100000c1100e140f038503c501c0352a80d090510041c05041d0380758400103005002d00000c83c003150302c0142e02000311050107541d8240b07140c0342c544074020b200d407030300a80022540580c840ca40111000d80c02419100c0c5600700322208000e094103408040320f209480358400451410355101400046000300004600400d0303c0c001582c52032031520f21590388003580600400584000528072245131240c0c00c100c081c01000750015101c03103031a07500040110030fa8008006203551300c0710103042201d01c03907101c960402d920741c555540c92340420040c0ca04400102c0380100100380c425004161440201c91012040200302e8985034100754483c0c0041240d98100c00c1441020425410810300503c4800d05051081003400c2d008d00a00426900404619070085481c120582d0703441c81600c2d59030303031121544000d0798911074070340c0194015200f090707040c49580707440c9501110309010701e900c24840031640288031400e15000c00d0041e8444035215611240503 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 505939001 1250 505937751 505937753
    0xa090905151509010818060408031008010603030f0e2d0a180501050109090b010207050405041a01030311010c080112031103040e09010b0f0f0a051e1810081f0203070507 74
    0x2e4281d12445070360168465600e8040c0ca0016003e50700251040b03206681c003a0714015803603004102c1c01d400c00c2d80110400d65130780340c5e09059118844250044078440d440c04a00000f0503410500c28000408d95444200c0140014420009040d21096500d00d0039400c070301840c0d5aa030f0003210060901c8034020301c2e200034544c49041140c141c0944503032208100d0b03500e4005100940c0c0021280e0014840003c090010030703907001c0000d45480385441294010381c0c86134003040030401d41800d413102410a02c000318a4541e900e040c0240340e40c81103160102c19510b0950f80d902114400c840a5050710700b88610581d030792510340e40403584100943d41e00d0f4647d0006000101302040e06028460003901100004108030940c4070420011122034980d0358071030303007001129141e161140701302001158411211413014030051814000020091041c46a11450407800c030803e00012449880c0501810208c0016040c0c0301d5442c5940c0f181107840a0401900d0300c0000c5094000540056038000c00d10b241c054200252 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 505940251 1250 505939001 505939009
    0x1d040e07030201030b040f14070212040b04060c060b04020c16050a03020a0b072607050d0e01020c10030e190606090b0303120604110c0604150605061e07080c070603050c0a09090515 79
    0x300c23070325840020b40c1e05000340140c0c1040360b030301e1401c00354640c5842c0501d4050205000d114510401050101c982154800c0c8070450f030140001c4040500159034440a40285030b0711441e0726449213281c0c005058011a940c285030a58409681e0302414100d0040d0074482c5014850f001701c0c40494494800e074000214200f092040c0c0b000310303c0c0c100381039600c82849103842414151126524010410714000c3c21006a0780007810f00c079000010b0b00c9003001001c54500c11000340902c026098400d00c0780c0321015201c500481c4c6011b40450060354200a01500c1e26039038000c0c1c0345010f940d507a041e4000d1204013092940c620382260030600081000072140079030300551020b908000c6501000d5041001040b05002c0100740501801112103010404d450034000002e185009024601130458605101c140244441700c00b1104181d801800b01c0c1c0d11a201c2c4825143c0da06089c0c0100300c002818040460a42606034040d64500101500c880007d2828218040700a2400400c0c9030700f02d00c041c10480c14580c40d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 505941501 1250 505940251 505940261
    0xc080c0408150c071e050606030d0c0308060111030a0504030c0e01061710080a0803150306040803130804050a0b2508031602100c0e0a05030601030c141f1d040e07030201030b040f 78
    0x99507844400c0c0e01021b04205040c40f000a0615000e03400604243d80003503448190200c82075498101028585c45040041f22002119466803015200c0090040c0d4147d4101c4042c2080381e2040f0910003180fa01d0701103482c51001d00303104440205003010000c08203114070b00503082c3c1c4000110107041c045907807402034178980074400b1010340c2c003408004188040c5900003100c407100c51505a000706440e0405541d02a49032000400e546040b4003082c2803442084480400c031402080e0003000c001866454084902c01688400e0382d802400c0406001c9403080305080e0b2300008556004004903007160780710102c084414100ca9a4201140a42d00450120f82c08501c05d083c2c080780c1560300c190740744803a4028448682c1003a04894440d80c881b400400008072890130040685010140300e624440700140800c100410305260a44071862002c1102c40b015071041401c1d0111124030f20103900c41001105000488014001000300c54026000a1000d0b5000b9004948840b41c080d00002d100600b4441c2c8000300c0e4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 505942751 1250 505941501 505941533
    0x30c06070917060402010804060b01050c0109050601060306170a030311070203011d010e0c03100e12190906030b011e051606021e030c04060e0a05060d0c080c0408150c07 74
    0x51100c00144045020301c49260b10440d9184000d250a0400740c0011300702d6040204010902e0703490340a440a164403d60a0380c10710380d9200000d1106541600d80261108024024140000e242000c00200b2108210800e0152503041002c0c04000c4034540301100139003441341c40240c0c0d0f00f5041081c480140c8091294194026601401410030544220003e081d1040c4140c0c3c248298450390700e2070700e1640d0116a102c00e2a40c1c0b42400200500c0c0f000049090002540561008003004603400c2414400b51409003040116591050703110307611042c0550407683d0800c103541c000b0348901500000001d0103503c0c590988064103249003070004820102ca41c2200e442000c60b4015000704200209060645448003c0c07542d80c80301b141903103041d40f0b00c00d030140141d00c5540c00300286500b0700c0c1e40b50740750380795240c01402c00a401d00740c2e0f9a1030714074400c000e0151420f00f14000381c12403000841d0b104104058400b07841d1100003420440d0104544000c965038054003880c0c640c5400c0000900080910014200007 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 505944001 1250 505942751 505942757
    0x3202e1b0302070c051207050d0212121315050708130e181005150d080d02131d0402130c020313060918091203020d0f141f030503030a020903030c0607 66
    0x7443c02e5282c1403522810301e5210f00d004003450511a2942c1c000480c002c401d8481c190785038000c40d00d8500000b0702c078210340501240b45009440c45d02c080d840d00c11000344107030066218885180d40e03681940c4103140b0510594140010400c0c050400040e4040c0010a0103000c04000d4240356038039000318507480107090700c0c41030300c04001c0003181200740010b008090341100c2e001410071040c9000c0e28031146110410820510400c071460746c40c41042050b000f0b580c10400c6142c0c3c01c5455420206200802d0100c82c06040c0b11130180728003d0f00210303814008548520f41c00b074808165000d10107000360182c4426a80070003580024400241c0401103e41c1b03660007407900e42c2d600710640b403501c020703024504801480c441c507003030908035000081001804104145076041c070300142d0755858618010014201541110955800c026680b4a009019181280035148113048450018503030300d02d00c010b10342d80d840018201e80060000036071101d45079001c1c25080c0c0001e801d8078980200c001d84141082d008650701004 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 505945251 1250 505944001 505944007
    0x190c0b0903070c15020f1b12070e060d080705060f06090124050307030b060d09110d03020309010503040f02090a140a02070c0311150403030206100501030c170a1803202e1b0302 77
    0x30615020540c020349088c0800a080b8840c1424007600d50244014205c40c00380401c00305103802c0104203403c0b0b40105d5009020741c0c28030704142400d001c1d00e600c1540c91b144541e40700000441c04203008100b5540c00100c1c9020300e490802140c40550b0b05400090048090682e41d045002c07032070312541d005020b500b0600c180050342040720b14159406000b00351045005030655841c2c0800030350000b049030541c54007402e05945035511403a040881f5000303010b00035007085517038050121107411500403018140103005a10915910000c086003240034500c1c4c040d08034500b00e01c0030404541003072501d640419000c3d1401d40c0a41030241030045913840340c1d00c01c0700182d2003001005500c2840c1814000504801d02e414403040200c61300081042c0c141c1900d1242d08901c81c40407c81a000d0355104035600300850662040e114140e05000d8880d44406012600e840b00a0410880085000ca040b1041640b404400300050003191036424080341c84000c0071214030760790900c4100d41d06901d00c03013480d495903c0e940965 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 505946501 1250 505945251 505945303
    0x11030f041127240d0602070804090606020a060e1f0b060d0e0303150303190807020a050f0a0203010605060405150a030b0d200907050a050c03190c0b0903070c15020f 72
    0x220040c00c0264440070f80c9140c010880c0342c0c0e5080c4040d00e050380151000d41c8565040c201500d40d44126808020031501d0311000103200c94001c070701005418000c0c0d80421410741200030550300d030100c0e501121400c1d030f540804807010382001da1294000c1000a04154100b403820310900080320850744403031700164170210030130403403920103c807240041c4410780c065030420f1080c69444540300c100011820911170014006903440388200588030032950080301300c0301c038400350440080d15040c44940c107034001d5090030b41c00310702400d000c001c0781d0807184e020300b000305400604800903907280c024003035880416494200300c10450351400b280c0f0f04410300416040c040d04c441021412200060641c2c2e19010340f19050810240702d42200580c0c0e08070909003801c640c1d03000c0c044c90781811441407400344000006d003407440e030440682c002d0a1950007071003001044001d440d070703880007650703030064190042118510980c180700c40c0d000001c49000031080d50040769020100142c08508000c0c00d840704904581c101c0380281 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 505947751 1250 505946501 505946521
    0x9020703090510090e0f06010c05101523060a140301030813080a200a1205030c06101a0a091d070311070c0e04050a0b0c0c0111030f041127 61
    0x100c0c001480d420131a101c5072400d200c081e1a00f80081a520740f160011000036001d9010b41e4582c50180e074007030182d81c2c094214080410041001d038114102c00c020644010607040020704080324040840c08054040070f00d040200700c1240c1c406c140480400c2200d00340130b01700c0a041d602840c080d40c855000c0031349410328880650b001c9a40366002c000568800d805d100040340b100310440c00c1542410001009400d55400840c4040480c5d81c0003503100445a003020701840404000303080c03490340c407100341c0e207031a10350700000355101c8401e000d0008042001a041601000b141e8003e101c0d1280300c1c2080030f821640c0309126420413880c03000442c0450700ca541003114480d85071040c4a0101c200200c114140500c50f102e043d0400c00d140504040041c510700880c003406810002c4609280d0b1104410343ea41c64503075030103001900910503c00c2d040d0b0801c031a00d0281940c020690b442890340d620301c42001e44e0303a078540900c40195840c0540d0030015070b48004d00d070031440e40385d8004001c031074040c80009410808990 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 505949001 1250 505947751 505947769
    0x30201050708040206160204061a0d0b01390807030210290607050309030106030c14100e0130060513060e040b0405190c0320090a0e07090207030905 65
    0x440e00700b207018020400140d8484050344d48596126602c150350904c58070101d4001e0006410054040d0302400e1510b6041d1303404d900500907500c280f0310034042407000b0001500c0800207103d0045110030a0742e001d0007014504444c0c800c3c45000c5d2100c0d1050307014143c4580201b640050001c1e40160130101e828003549450b40200303000100f80c0204403907200c8200810b240c01c0c1340310011007803240f0300c0000d101042c000204161039800c44010001c0103030981c1c074139000c080c2d64404d200c0c1c0078100005504000f05840c00b0f00c80e01c4801300441c0c0710702c81d089400c800111000c82d902d0403403018151210201d10030601345a40120070407409144000350060409081280d45d05042c01c150a02504100c0b0a00640b171996524541046e03120108010b151901d16240e030130114481d0050344420f00d03000c039913424401040d603000111703806a464640340d0f043c040075080108181e5542a81c0044124012482c02501640118180316210099030f200540710001402070340d100807825000951084c40c01e2059103441c1d010 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 505950251 1250 505949001 505949011
    0xe0f0709050310020a0306030c08030a09090c02030301091d0f0d03060803090609010305040807080a0309121107050609040603080c03040303020114090703110d0506070309060b12190515100303020105 87
    0x44100254606400250fa80d02e200862902598021600b8080d940c06900310401555001a001030070680300e030f2520790382c9d401c12078a190009200c070070005072900591280204032080d81d40078601c1c40c0e080400000180070001d200d1800151605465514400c050104403514400c2c407000c2c2100c0190708038010292035560708403000a82041101844541d034480850712900c4080c2804240343da29414041c1444c0200f03480907100c00c8001500410150307041d4402144184a04a10303140040d20340c40403a252a09841d0000d40d65000302c00c180824940710014000c0c0c0341000b000416615100d80e603500480d00b00d44500a00366201003030078420542c0a00440504c003c9508041d03e1034a400404c040daa0b840c24480a411290114490b0303208d911074003000b61205401c81c08035a40c0b402c2815000300144160902559174900c0c200840308646409148100c000981a00810440407940d58985050340d0034881101c480c425803070300c0da82a008400109114400c0420511390241c130314140a401c0d81e03c0103007 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 505951501 1250 505950251 505950257
    0x207090605011419140406080937150905210712080702070b040b03061201020309030a201c110c0d06092f04061d07050a0c0c0e0f07 58
    0x102d03540c1c003110340c4400d5909100c01d00c00302603204e101284003900c60315030058165a114000103000310344180c0101595001d0300d03400d0115800d040c40115007210b41040c004e60589901454441402e21000000c04007141c50b014241081054142c0b94001c0708850f0100011904c0e5000881010090329049266818034950500700528040d1550341701840303962000450410300403004041a46240300f0448840a800c3c24900d40f5542c9844100c030704240e1308100c036140c0c170030701c08060254009001030003602e00a08000e0015414a030f1b00f000180c42d100403801c0d010114011444013180ea9000c2040340e5041101030640c1c8001d41c9a1801005103030b0012050b03a04a0b507440003a0244007526040b01003c8016080030b4002000e0a4031b1605111409a60f15840d46806207021000d101c3d85031202801d80c800000c50f410081203640301e0803481491054514500c420349064005040e0301e00074401003000400b245840b40c15031645070794580400030107401040445050408001c1a01500c040c1a034002ea6681 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 505952751 1250 505951501 505951517
    0x50732011b081605090a0e271c030b060f030108120412080309100507020105060f0405010509010303230c0102072d020111070503191a0c03041b0306020307020709060501 74
    0x400042c20440c0041c0c12824400002140519842c3c0f180040c0d6034030000c01451858856a20141c01200801c00d03904042c5d0b42d00c1d80e110305d04000f18040c90100540c104c6001922943e80f130f0010002003841e140e5a0030080c0740d110001000c2ca55075400061662010180c03099072071717504100d249807421a902203401a07c401c10441803009101610b008001540e1000080d40d03296a44000340d401c25841560100295040c50b051061a940642000d4441c0b8825114500f0721384440003008262a03081c0700e059000b091100050012900c61202901c894941c94000c600c540c0103110342d103110b81e10400f0b4080c0c0b580d50125030b8004210809100001c00034580d02d040d03203032414080c808103540e400d080000303040c814500c20343e20100d201800340f01c000b02001011350f40403d14190001040d07044001e811502c81007021240b62114030811806801890284100790956075103503240007501907040d40d94001e0000040b070000000d041c0b0300043d4407500c0785d5806000d1052618541c0c3c420ba540c1504610705201d511 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 505954001 1250 505952751 505952801
    0x1e07051c02090424062c060d0212040f12020a030e06180a09050106080109020910181a0c01110a081306090b190c140d05131403070302060603010b06040605073201 71
    0x800200500c0010407221248d80ba2030101030f0750028420500405201280ea40422080c00a0300c03490381003642c0201458000341e140c11600726110824420000c0116008051140d07050800c28040d10000c012040d594144107003010004803010707460b42c005d140d0360740c0304c000502010717a004044c1030041001c003c055003080030840008406602402c00c1d0010089036800f0040c0016602202100810801280c80324043ca000b03c02e1385564030854469080e9820084403419400c44a8103e0b10341c0506c0780d640460548840e06000d140c0140080241c07050364a42c00d50002040c400c3d64114040c44c00140d0090b445065003000c481135441045003d400c0c048815851060046500216201860fa10382c000800d50b0b00c0081a10303030359800c0d42c0060034214001007440c0700030000100821006000381c003100c4281e40c0d142d04060a9500c28081250821414001002060300075070103002c1d00c500c0307013020541d800051010100000051507020f000800e04c202d039251480300030700c2014030f82c005040081c007d00401c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 505955251 1250 505954001 505954067
    0x10f140109050402360c090307030212030d060902031e0702070b130308040b090316080c04020705010e0f010b010311090609090402010c0501051e07051c0209042406 72
    0x814030500070055142d000150441d07807008514024081903050901200d40f008802c081c4001201d000103440713410001c041100301203100181c03118010000d005003104c1d404c503804e12043c44100c1c000415184030500100172001d0083c00380c00054400340400686a150999624201d6168840c811601202040a02138000d601144a00c1a5000d0164840d0f40d210741c0084003202d83c40315400504280408140070a0941200e030040507204012001c4485043c1801c01c8000306050724820340550f035210b000c0942c0941480d802400c40b16020b14000681da00d20740b145a400c01d01c08100600d1203940d9181003d8456806101e15044a8000d006080c1404110000f14010b4418150013611808c0e11100040c11a0f00c103240991406234840c0c003d201070708044191b9828401170003e00300c20600d040c0000784010344038005640402c01800c4c0c82030769030b91454003140b0095000d45080c54100d5151000c1e00021148040e805469100c0071a08035025817421f94003c15820b0000810007900c1c1c080301e900030074484 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 505956501 1250 505955251 505955291
    0x4050a060b150a020c011733060304050a02040e0d0906120b041d0609160306020f0408070326032202040e070b0d0e030301050114090a1710060b19030b0a0911040602010f 74
    0x50343c86185000c1c48c9002582c003d0701d008202030305c1e46c010340000c104010000007080700007030184283d4051124000d841000f98480070b101484000080c04048104212481021218541c480102c000130f1110740000214084e00c030385111640f6525040718091007002010410036a124503101c001e0980101e00e04001c205500c5280710140102e5004035281400c0f01e400340403600109040c0007120640c564900e0040b204e2004444426400c590507444035441190303000489129805e100c040c0c50100262140c1c02600c800044001d81e042a40d6070300d050440d1004010742c10282c142406000e4580c503860248034281c920444071000700d0713082800100603990b04448040c0072001c8440030162125940390200d109001968024103200d8205c0c4038961081c540840d6610320031132142c0e0705104054844100390124882c5143e42042080d0440805105611942c0301004c04da400030702c08403c0580d60109007050310040713600b0051503480003904003c1e4540901c6404c880c400c1c90070003030128000c14040401001c03 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 505957751 1250 505956501 505956541
    0x3020a0203102f25110904020603060607050109020402030c090301051302100c08091507020108060d0c090e0a0203030d0c110a0c0303030b0121060503070e04050a060b150a020c0117 79
    0x456a041d440f800e104046050300d94201c0310403800000d0f501040708245100e1900030080d1100071450b61816060306080141910503034000d01210f1850701e40c40c09101031030380018801c3d00c03195030304d00d400c07401a59103000a60141d982c4010180d101c0d00385004142c211500a80318100985240d65880e005031030300090541968041d00b031400b400c0740c10381404045407048042503a442240c41c01d00380701401044015003949030003070341c030100342d40d503a50244800296080c0000d0001d5244a4080007900d071940c21084060318400b040e0780d03001034554046891504564800c100390782d21020401034050b844041961007403080c00003170025407072944481e1042105400701404241e120440504940d0180803d1050404804102e040008004116900a1203980079584c40b038083e4610005010054214880c043c07500200a084007003140e40d01c00d001090311061140e00f00540e40c0001200340c0300800030b01014900d58024100080300d05000406600000c5013000050010390144003c0600035207000c2c2000d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 505959001 1250 505957751 505957811
    0x1b060a0b18070509130903090306110a0804080c07031a01170a03140d1803030c110c0315060d0c140301051b0a031109120c0a06030c051c140403020a020310 68
    0x50080d500106564140034401704014505000d001c10415911002000480b8000c21040000380603140504503d81b19036030800001840442c0440c000c94040c500500341054040100c0314080e60741d40d2021401e0201040c20000202c40c0c00041202e0350f0b1000b00c40a4411544001d41043c0260b60b40140c009a5450109640950b01142111010000358815240400b04521518580341245001805000d0040d07400300000c0410f01c0c660a85000003819003a0084001d010b0140c80420580c000307034144000781083d5001c4078001d440300100e11041c0003032002d0b088036030741c0031a0000300710189030a5540c0900004001854190b0055002d28120142c85081c0703540d00d400709000c100103003000d23080d0107458880e035482510b00c04074050500000030b9505840c0010b54615680d15a81c0030240c0840745414a0325010500400640c00107030200111003609a2540781d000074080400d241103403041004940c2200568030044203032003034bc81c007000030300c480c3c0d2290070307080c40560107039061500c5d01030b20905800c01c4c0e = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 505960251 1250 505959001 505959007
    0x7050c090c0a0503060307090e0c1f1202130b071a01050616060b0a05060a03020901140c030f130b0f0304030215042003281505010303140304081b060a0b180705 70
    0x40d0386d080c88100020b14094505015258404030380325203c6001100c0c5510980050b00d200d914599040c442d102003926949844800e48031201ca240c02079131058281308001928080c4c08602844c183d80074103d91401080c00ca421820f40d074103202030303d01c0181c00c00d03481154188a05116110801d1140e0300b130319070240c0d01007000c0e200040440d09152442d00503070f5102d0720118015004580c07560240c121a0006d82c0c508100001c0e9000e840f2072442450540741094208000c94a468049440104103a1041c0b0000034071139079440302d010032103411003000300801c204000b00b80820301d68100110803425030300c0c00d2074440c2da0402d0303a07450951042e8081c009004c0c070210f101c075400e69503041c403e1821011103250720710045142e00343e000d4110104048100d5410800e580740e40c090a0380c520134a03040c1c03075141c1c40e10b010315004c0d10f10340030303c682000748200c8001900304200b19000d82c1552109030401791010051810742400c4a500041e00e601c80724160007542c00540c00494402a0400385400000c0c0b402c019503 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 505961501 1250 505960251 505960261
    0x9030a050d140c0d060f030b0402090402150c070311100207150512010e010801060803120f0613020d05010f060c02030322030c0b0c01050f370f0207050c090c0a0503 72
    0x3020b8074040e07400c1a8652444001c000c0f00680e20402021404d400c41001c0202586a84424070405031034040500b000c910003000900606140b001260460700042000b0300d2402120b8402e80b4641c4117000c1000603400241d400c004111014482e0320305150100ca8500d0085d9002c90000e5650310144200000c02030300c60140040c090042c0e00312000d403100d0030040d134241c4d0b0b100d08085524076000c0c81002c0256223031440000da0300c41c0200a0740c9100005001140c1141c0712030303080840c2682d0181c880c5038031048421510b020785110f0300c000d100030520700c1001303d06907240001d000d804030309503801001402081c41c40d0000580e0003000b15215403407444407200c0c14800750048480070b000b07241c00007400050f030004046000c2c0c0040d4040d01244650350000d224a0340c2d003004501d0a0070003a07030b00401c0c58014200e480d11005425182e260038400e0310b1107140f0741e40c482140010503504062496501a940060400148a030a01c44a5800e0000361698405420703d2603c0d02d94134860034140d2020044088003040c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 505962751 1250 505961501 505961527
    0x20130c0e0919110c070803070c150927050a0506030105070806130f110406121808090f12190201091d01050d050f0714091e06010e0301060f03110909030309030a05 71
    0x107034191044c4d4101c2c0c08207038903124550307525400502d0940e15041c4100b00050351501c41030002188a0031a51081a0070341b41c0300700c0801c0b01d48541901c900c040c0700c0e50030764a60b422461194034800c03e00d407800440c02c0c0c00e050042c5030841d48040e08400c104070f00d21080004688421020b004a40f40c01140002e16210a400401c01001e40f60fa0ba01501e840c001400160b10340c2c40a5040b8420207007060420a01e12005500400721803034a000901c50202401817048500d00400c03581d00380e1030042c05001c000d001c0c05003094101541c4201401c03d00128003150703410b550780301d6145800b8105d1810710501565652031011422780c0148140b03480b134100c028120040040c288102854000c01c1000c441c1011f03107130f820b2102010111410680588006000918148070b485054101003696160510b01c0d5101d1030300441e020820070004940644d2035160018140008401100040d030082c1181603480d203840c4104040200f024001c59042c0d84240244451248080115121080c46040566407083c00580071 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 505964001 1250 505962751 505962757
    0x109030503032a0301080703020603070203070b0109021309020309060103121b03090513022b060b161101091a07020406150909180b0420130c0e091911 66
    0x103103980004000d00108900142514100604007080ca02085640015151460000b4801d031142580600020405070900c240296040310b198030580f403031311035141c8448280c604281e0100342020b50000b06484442038440c40d0001420300d8007015451410400c1c1303041e51b28001808040c000203454400d05100b2402445401e0002d4103610300020541c20608000d0400000e9100300d1b8003c5105407540c3e07274842c6a85c0300700c0d00c9400c07105440d407003840e1007082c0c54130002100401080f0390a030795590200301851240c0142900804c68150803003041d06c50b142891001a040090034144542c10100303000031140500305003007150440508507160300b030a00002d0098a0a940a0380081959110640400368006400400d0b5100503006001d040d803900702150651480e040c1c054143c1412501013000601105104060070303140f9400e04901c08030700000100002d48101c14020529610404010540e0b009002180c00c541c04079828120341c58600280c22410712092844a5450f50301c508035004000d406080d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 505965251 1250 505964001 505964003
    0x20309030f0106062d230c030c370201030b100806010207050907020c0411040509100303090b040b03132316151413050301050a050a1802031b010903 65
    0x480c1c00110919039018020901c1c0e004200000300341c0c014480007901d00c000042c5000d00c000920038100083c2c1e01c02101d885e0040c8170401503090f05039406002049010b005030070481c8a041c007641d611000c4465181c5041c40007080420102d5881c2c0c00548a80428640080d50031007401210800780b1851004038002c2100781d41c0c0c1603000034038200301ca0000d030317015511a1052034213800701d40d01aa01c580801c020410300300c5040005901c00304412031a070074640c0140079080ac03000050390070075480b5400540c00303040465406024144c00c1800f081030540c8100400000c050f0210701038901800c06410b408c0380c0c4400bc1103101d40c000c4003010001000070310122046420b900d81560001002e2400501e9103030913130185490700110140c0000b0480107032191403008120115284d9407514124280c0c08a030039000b0702c040d00800508800001000e48080c020103209a0f9505030003c1c691425038904c008807000c444100007900c0005880c0d60060b2000200b802c209800000e90884503100c0200480f910780403600 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 505966501 1250 505965251 505965253
    0x7120f1212090b0f130803061c0204020d0e0d050a020304030605070e09090f010e15011707090e0a03110a0b07031509110901110616081e0709080706140301031202030903 74
    0x20700e5410301000560745030203407140e0640344c10a616010307540e1901c03020101c00a4170b002400c001041d413078940b01c101200071010740e6140d070b0702d5214a500040c0480c0c00580c180030350380f500c0d050f02c140e403981d0070310081c541c3c144103007401800e0422f403640c0290740380114003005080b5a075600104096501500717091103803200092004800f8035100d480d0984410102600e650550f0902c0001e85100001045603010000a0558145960310f031150f210f03e4151480301541c1e0a00500c480414566036502410410000c075100800c0d0744019490020000c6804114807046500325078000710000d8001800e40fa00100185030100d01c1c0b10040319110343d1058035a0000d03081d20300d00125203014558203009462241c100b600d07051080c06c0307840495529000101c3d001c05000c810001038240c00c9000324105a08003151408400c40303440342c08080240301106442c52000708880040c104001c540420010380907040a20303108001d400e0621052810340010300004212000c17000c2c5d69415a4404c00982e10741d607170024 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 505967751 1250 505966501 505966511
    0x100503070f1422050105090d1203090b1005010f03020c1504020102010f06031a010512031c0b2701080c0f010e0402070c030c0905010503070b070305070203150106050c07120f1212 78
    0x2c050307105242851a00e14503c001c0f05100090560040e0141c654071000130b0258404806d45641c0c501c815204140e0120505075507401d038802042c000c04100740b080300303031f1001c20541a0821001401c000303c4040c0400400d401048100181d080101d14070382100d00005910b005510b4920040c1d0150003106481200d85141040010074041160700d001c010744d0341c6101c507501c1c990300d450502c5441400d0300d4220381641d00c2000811070001072240032105c00742c6082c0c2c0c001030302e0118170005011060304c0c00390b800e009912110b6203e84030802c14a241d0050800070000e0012003425000305020146000915040c01103d03803600c10f00d61210780485500b687d00003009030690344c072450706005600c8640900c134244c5181000201c4c550030300203401e50a0391807994055040c0302040c0e030b04a401c0c0d4010075040741c15003e14040100d44192034010107002e04040d80703810741c0b140c040c03142c1c83c1d01e011700b19804401c4d130040007031a000c081103220840c943c4254101c50600d100d03003882c1400361242110f50186180d500d10748 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 505969001 1250 505967751 505967767
    0x1e0918060504050a06030b1f0b18040c02010c0e10030921120501030f020d0602090d061b020c0a06030c11031c0b041a0405130510020a080105100503070f14 68
    0x180e00000640e082290104015114194a40115036050100800b541d80781c00208400c1890b00747d517184c01e4032802500803c02a01c55218884d0790300f051907007003c000d4841d501051149850700843e6510300d01c501c005c000715610880300901c83e40052250340e015004030801440078610030341200c070705250001c500020790241a00d210f49620820707040e40000030100710380310849540301d0107041c6c12079810941c2518408055003c1081e020b8890b40202c1d06550308016820040d10344408020b070301c40c041d42d4002050a00543e4200003d1060403008003150026030054080380e6a140c0010142d400900d0002070180d090b40081d0303080701c01042d121200c0e110101d640c1d0703640180041502e01104041d030003031042410003002d010980300d036048040303840c00320454001c41504040d801a940561442498910124162a16420840600b0700103484a0300007500b042c0003504440351900400055815030010019528001c3c11400050480c208100700c0843d681d2406101d9048882c201c1d261800385650b854607 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 505970251 1250 505969001 505969049
    0x190509070303171b0a050c0a0b010302040f020405010813230c041512030f0e04060e040215040509070309021504240519030e120301030804061706011e09 67
    0x41c801240026044092004415141c01d2242d003d804281c10311014070f1030001048005401001ca49402c01c40180511034040b03104003c0201c4160181e0303460074031541140184020340c0c281c00b6522280900402040101d640d1001580d5880300d02000750b11488421454410070302d103c80312400b1400d0904060b21b102907100441c0b25008803404035810459001034440201d207110340c1d03100e1224000802c811340c4000c07a002e80301c0d80301c2005861170041e00641503400024210b400541206a010b1200420081141814584407108030a20004141024502000115280c000038011003c141e200e03002d21085407500c000f59200c6807a8a00c6441d1250303150030360220084840e284080255091a013070343c0c1403d0091080f80e00800d070000302c055403600604026400740c01440b8003500d0320b228001d015401c007540c5402441c080c40c0b01d5901e495650740b900c0d01c014400c4a151300202a4034102c8014040c0a80e0004419080304110040a1b00401c0c40d05605441007a11988145641c11102903081020a0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 505971501 1250 505970251 505970263
    0xa060e33040e0a0606080402010f0903050105090a061404020306010512100207060c0e010c05060612070f090605010906031e05041113060501090b03040203032d07150f05040f0605190509 81
    0x203002180b062481e0b84442c0840c05442c1648600400714440b08007150265200f0294484007146d9814000c40d01030f620f81d0303441e0071984201e501012035085403000d0010080719000c2c64103250341140d9000d000d0709154001030344458061113410b101d245006003624003600144054001016481d000310b4035504141004409030070381c449000b002618588e450707500c0d58085d45801c04819000401401980d841005005441d480000b9071480c52080880000300c40d082000060054120300d031300800d0207440d260015106050342d1300a10240b50400344042a94a4140388002070b04e0309118010400c0d40300c60901e031950801d810180ba820500daa540d41c60250450381201c01121001c1c0d0b91072084c03580e00c80c02c00b000741c0030a4500075890f0f001008840c4041504d1880d002004822510b100380d280c000c005903403410791155030304640c0200445405102000f952107129000305000c0b500b03001d90b180c6580c0b95030001d510b442c801010182d81e20302043c0c01c0c502042d403481102c000244104102e090403409141e1b20702d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 505972751 1250 505971501 505971509
    0x911060a091a04060e030a0b070e01091e030210080f040f031101050a0506100309170306040b0904031e0e0d17041206051602121b0c090c09030106050a060e3304 70
    0x2400d17218210b91070305001030b030301d4842504041000f00b207440309581260a1803901300d0f6141040380440b0003040403150700301c0d4641208440b6440c500c0300c91442c07040c80000c5110303004c4a02441801410400c500781c10203040c41c4d1080d40070300c00d0480c081c0300c0d16041e1102c1c030781414420706562800d0108813001800d41e0141f40221f41c1102d07006040640d1100c12010313240301041c000c0100310210381d180c00c01041e04e4003440e0000f000400102d980c04d5640041280c81e03500b1141500041c0c080401100007a208512326822407200d0314000d90b4154940c804180030311905400105140c90a414001c081c030000400d0b5070140c025250b010b2400c0055003001c00203400145e800320000d007411500c41080900008126001c54014542d00342004d05081d0895656840021100c00500491848880e26a1007011a6105608101200c3d4a80e00d940c070915084a42c290460350103580c0c170f00700602c07007117812107084031f440181194090900c08052198041c6810f028801c165141440040014a200900c014200351 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 505974001 1250 505972751 505972757
    0xb040501111b070801021804020d02090301050c0703110d09170f0105010602010903180f0302120a020d030f0f11031912060b031902070809062206110705040911060a091a0406 76
    0x3c15140d0081908038825102d03032602111611806410034106078018202d00c1c05014030060424170708202290948808403880c04640307600146800c10950030007000003c500c1800010050040300d03e8018042080f140100090004010841c1e0001001041000e0541200d54000d200950352198013074044e000c0308400b03e000c545071000c04154200f00c83c400303d04480e007614005511600d140c081c002c06500da0740050a96020300003d05015844044034100001d00c80d0b6202d8107200d0072040300078080c41042d15190204140000c020825600002c15254140c40004204d10460b140b5502a640d010040d5564801c282c10070700002100030a80e0086e61055000d1901d00c9901040c640101e4100c0c403a030f0030010f04080301800140d03002d0a16002402c2c080c140c850cd15800c2c40012100817200c4081584000c0c0081c6442c00a02110b001c280000002043d05482c14030420361030b41e480d19030320158040a1405400c1c0410b50301ca8840c85a0b00310070007096040044803c41c1c2d02000b802c0c6440e03205000f26004 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 505975251 1250 505974001 505974013
    0x5100c0206070f080f0c09060c01090b100801020a0e060901091e17030a09090b0a03021306090f0b030304090c0e060403050d20060406090212030a12050703090f0b040501111b 76
    0x40b10f0301450505200d04240421100c06a40e0090481665041f1440395508050280000342c01000d0901c1b600c22558000c08940d0080c0c58100b04801c0403501580280325580d0050081c04a4580c01211040e1380340b401b1640983c03100c08036401214401d140398400040705e413842c1e2049025911110200741654590141f401c1407003c0d010360951380f4810f00a0010004690314010482020190701c180644640106640380043c1d494001910b0a824150072245140d56080d041003d1401442a000c1d21007001d602130000d6522507000079160301031842000c0740c841d1202c1051031000d100e03103004110038400506407600d4548030f0030103e81d1888600c4154000c50340382040711240c103036051000d840d44007070b035070040001c1d80e926a2040090641031000301c0c3c1002d110460121005001c0c005403502d01d0099440008890b0400c50080c241e40c070240105d0281840e1003c26000302e0704c108100582036810040b5102e8a450340d20b80786005107850b10384003010003004200c05070f0490702000c03842906502d1100300c0309 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 505976501 1250 505975251 505975277
    0x50306130c02030a08090102161b060f0903020415030516140603061f20160b040f06050a0c0606150e09072c1002160902040305060f0405100c020607 65
    0x400c8500030101c41d40036038801c3c0020301c030b41e9104400c0c0d268070400d685c0015040c03c1013903c0709001c7e80d171200300c1192540d0f440101103c00741c100058140040c1501d04c1d04003180600b03110040d07d00c3c2e00500002c0c2c012611640c1064113600d2462801004551000880d00280a140400b5100070a140107482104144406800040c0b4188003030f20f00443e03009042120309001d00e032504458200d24402c0303e00f403104203d130025100100803900794008220074007500e502c0389000c5590b03116030f10513080403a819006200c01d00c180c040161440e07098900d00d0400d150340b58152101902e8010380080002d102c00e050240118170b4404611002e00f09445548a224170201b5810400c0101c8204031a28000a1524070030050382c0452014951560020560b03502811110b5002140d00c0090044040c2d0159201e4840d4460442030b40d06210001c0c42d80c07800071424542144d80e56510f07000040c1089804041a00204003488418000f0710720408251008005c8000820300281d00c03440c08030f170074801260704030002034 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 505977751 1250 505976501 505976539
    0x30f0605160e0906010f110d112a09060303120a021305060c0c01140f0301032a0e04030c060e1006030203010e03071a04081209100f09080304151b050306 67
    0x180312850000c083c0710b05035031100c0045a104a04580c45020000304044201c4054000e00c80110090400d03500d07141c0100c0095034080c51305c4048981048405020080303607088841c01c1540400007401210040e44544904d4002807850013a2007a030071107600904113001d013004295004103071101d41d0b458031a202036030300e2003040654003c45454281c00c0c2c02c0021404007640c17280c0691a07035810400781c02070414504a080c00745681098108039204a00b0162200361402c00b11090f0702c600050710b41d500c4003141480b50107121004082c1c401002d004a00b8598010024250000282840c0e91400c6456900c000000f00c0041d01d020310050703000b0b5107400c002942420000c02110340041c0c0042080c0c61031241803040c550030840040003035231100000e0240500c00040c640c42240103030300d154003d202080380600c4010880b00654040180f492503c02c1260018070240160380e03203d9008025159042c0600b9801005019512142c1d00301541c480d0100c0e1940307401102030f50003002c00b03035615207840e00450020 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 505979001 1250 505977751 505977767
    0xb040501121e090804080a0b0105031b0117060109090f0b010e060f070809040e061602060a14060906040b060d02040e0a020c03030118151202030d020c0a090e0106030f060516 76
    0xb25020408664810115540c0307030400c01c1c0042c440c0c001c0e0741c58950350b031840c0b40c2080110601100c60180050041103585000c00030700002c4122007402c402549442d0002a0102800240d01030b500c542074000280980e000c0d240d1071000740100b181c240203a801072112500200b600080c41070100343c100101c1449828640c082d5200410390340110b070f28006486c0c64680b1a500305100c210350007030701c1b9600b46422803000c1c0f1089000701c100300c81d05904585071a030040d050200c0244802c600605e000d07025540180140076103070304183c0c26155a0110b8403080d000c03e01900c125503036507402050000310b1801495080d401003003294803044039072110341c03146d100c0041684520f8484800c3e40e0310500041c01890030f40c41e00901c103c5400b1100056052402114000310074240d0f0100201c0e24881d21207006505041c450a41e03003000e9840075201204a42000a264012501425400659820070500c001d5400d511050185400240136406104549000340103014100e07490030b03035880348490604074507010f0011 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 505980251 1250 505979001 505979021
    0x4090f0c02030913060302040e1c0507080306010806030f070b0a0923061b060408030a1a030718060305010509160e01030507061211030702060f01050a03020303040911130b04050112 79
    0x6149000c0c960020060002800560010550307070717801d00080107a880d80b00d07203605044090702804803400031160000a51400c0102d032800d02074100b04400000d44064100c03980b129007420f040b00c1c1910741d00042441d00a034031910080714070450401080c40340e000c0001e4030f4a0100d0f90b0b600c2c0c02c207644900d5000302a42c183c40020500d1071072549186174901d8201c001d004848a50030304002300c0314200c020700c1c0c90310400352001d950030500001800b0b40d05c81c031401051815024204441c0b00713000c5e11004255203c40c584203604200007002d8171425002e4481c1c10110056811000070b1005080590449171180380ca2140b03802c00d600301c2100000c010100c900074a0407039400901621425240160984200800b10030001c00d29903544464901e41c08204091802030b0159402440c4d00e1402568249141c181030700400c0c400c0d41d08020800040c1d03000811201503503158800070854182010540d0305502589014ac941040c0c900008187c07088083c024004a42d0f003642c0301948603400c80000000c68001c2c0b81 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 505981501 1250 505980251 505980253
    0xd0f090b070513090203060d0c1206140f2802070b061c0804090e03040b0c01090201030b031606110c030609030d1505010c02010e0f0a090e07081207030c050a0b0c04090f0c02 76
    0x43c10028580c0d40d07406164022405401040e05e072246590f10000f8150b5a00000e1310050748010b40740c2030000c544a901700e1140750055841c003030b0801207100c80039010002c0540c00102c140e40340007140f0600200178210f03128141b00c0705540f40c0e002c914040e4400d54084480ca401a05d0360045214180d5800c095050300e80e80001003d40b801e8240b40c00f0102400c00311f00b01d08498441000001100f500c2e40000f0242d2a12000c000070302014503100040c00d8805080c0c1c00303840380d40420740c0804607104649040c0201c0e0903d09004018405a090319800e0800d48190240d05001300410001d600c000840100700043c0340100412180108260303907c100d46543c0612400165a8800600103500034600d52191440007055500c0381510f10000850141981d04544180350300d034460b01c082031101704230000103042400c02410901c05130340358410150041a40c00b4040203402c55030103060082c2801082440b54000021500ca40760100507140680e00a104500501e1719249048010a0143c4140410300700164 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 505982751 1250 505981501 505981537
    0x2306060910030b041e0803071d06030a1a041506020d052104030c060e0706110f03031b040b040b1201090b030c10120e0109060b01090e040b07050d0f090b0705 69
    0x2d1070f1600454001070088420046a030340c03000030304d11141c0c4c2018a50313210350709007076581c035108000410391501000454a80d00f54030b41d84088036614079040c5e903130207042198005540d6800b000410314030384d404c6042a4005250100101c46d65030351040102c29151250200c0319040a0b88030115224401c80740c0940710b08050100542c13140401030f01003174000b0301a04c0c01711b07400401a1186000c9581c42c0d0303030300d00131580400410442188c00000300383c0742012060141c880704441021040d140d01c40204030100c041d80002e40058403003103c906580107080324513685a00d8a44500801d017450b808491304c00c4012002400002e8035003580e020b110072012015000d00803419114041c0304c90718461034407900901000900101c0ca03048140b04103040401e03081c00100c0c18034030320301f01fa00460740c1c0e01050504205403d0301c1801024103801d4480c2d00544c1c044080075050341c031020b0448180c000c011440380010308104582e91414008d42220002c140508a0b0003c1c80d120030303600780c030702d0b1190076060101031140c4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 505984001 1250 505982751 505982753
    0x1503110a14010f270303020d0c0c0b0c0102040b030f04021f1e020106152f06011203021006140a270f0b0d0b090f01020301030c030206070f230606091003 67
    0x10a081d2031189418140b40c00203162003900350802103049000c4080c0360383c0f03d06041040c180d040003c031600501c2410001c840a4082e11000e5042b900c03405030460440c03000800040c0110b00350704030f6000b401d00f1842980c4905000100e00084402607a00782c6c031444403040c3c0c4076100d580c0a00d00d10617000413912074980c05000c107045800e80c541110700300001d55584481c0060350301e0794201600b0a04003a40d4070100c50800180c1d907140c2c542c1c00380050301b40c1d81d10150702910090800058540c15981c601402071060b06091808a02d807011441c003008040f400c2076000a2550040a10002c0540e811034940840b10784402000310b40d118840100c2a00075400d61002c1c03508181580481d801110889002c64100d90b5100480d406c1c100c42d0302e003104d07560341e8101085800042441003036072002ca0a03000394655499500e0380c400c00c0c1114000603109030781c0001c0003020400c0c014688c80c078180c0d02040c0240c03803001c0b082551204940701e0f41b1a8059000b40d00000e0302c1403801540440c4035a000c846d400c00d0643c19 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 505985251 1250 505984001 505984007
    0x1401030c03090803090a02011101020c120c030f0d050702010b01110613080906180108010f14040f02130b04051503040c0b0903120f090a0506070f060b040b041503110a1401 75
    0x340c0403400207059581110b0740c080b60214008503c91004000204030030790380ba00c001400101c2c038032046180c591061010251000010565680000300c00c084507848180c82d00302c143c2544a50038000d1801c050000e09901d448203035801003032103101c4c10380007004003030860310040d140c002c1060b080d90305d0703900f054000a24804540282104850007045082d00b0b100c504408201c0310360200ba0101c24039461461121425a032000106001d0102541200b99092800a000202c02c200c200f150340300da91108554103400250740c0c180c0e644000080c031000300081d07541c600c660b1164803c0c01050302519080c00d0040d102c1d01c141013124020355000c0d104960300c03442c0600014990f0004030701c01d641801500da80400a5480c48080d2a1004410f030300d480e49d40c0c6a290402108441c568041401007405202d0300d00402d600f4407410440e280c00c040c01140c0490500d0018004140da0342d0541c1e8850305e000002201444c0669554081e00d00c00d00100e0f80a031040d50030031012403114402e941c40401901d09902c11544 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 505986501 1250 505985251 505985261
    0x318170c21030d090605061507020607110d14070803040b0d18020d0b09011b05090f0f030f06040c0e220c09060e070210020a0e010c02030c03060c0c010c0306140103 72
    0xc4240e40c20400a0000c81c8407815030380007400000074036465094030030a12085224183d04032108860480c8402d040044055042c094250064424075020603188248924211031003004038008100c401000000d2801811031403c02d2160a018814483d001c9640a8000116030985034400161410311860000680180230720860040d060b051040034140140c894510032505584607000000032840c0403d6004d00b11405010038603034007000071907540000768006040710118032094034004494082c400c04103054a0b01d00c3d80d2a80c0511503404202c000e1403005c40e00740c1c0110301c00d60454140d141c5d15440010b074404240e82c048a8040c40001002502d00140c042e0b40242e403013402c0c443e422550311080842181d699503c1071003200700100810082c10303410702c20000c10400140086042c5419914014558240440c695050222001c881e0056640030414005440360007000c03030b19149008194501680c0010101c14003941c200080c0345c10441c06070007600e054a40c540c0400000c1c0140c000118080c1c1 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 505987751 1250 505986501 505986529
    0x3160b070c0801110c0f120304030c0f0b130308060406030b01060503100e07120507020d142b0c090807120b070c0c0b04140f060f250318170c 62
    0x940c80501c00102a03900380140ca4a84040102060f00e400340d103010b0303504206e03118030102850f8205940500d208040c500950b90801e805140c8100f0382c14003482c04010000d441500541142c002408001141c044042c41c82d400745d22079a2210b849031101024030040d5030041c0802420002003000510078540700e44061075002d00401002800155201c03900e40d294841540c400000900107402042c040038103000e0700303400c848144020a001403d510000b0070003507840351080c6d11044005000807618003a800a620b4200041003018110140b51440710010144079040d000440c2000742d0004a004011403403004460b4500e01112110300386549501e13100c0c800410690500990303513542004604078100d004041c1c04001c03100d0351b480b802d0400100201101469151280c4108090b403180f41d1170782c0060701c1008030200035082e1030b04100c14250b805041524039035007042e040e0450020901d6401580406080c650450b00303014261102040601c26200084881c615841030841c8562410101d002000e11 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 505989001 1250 505987751 505987763
    0x100b030c0a052b1109012411030d1a040c020d0f0e04111306121a0f030106030206070606030c090504120e0f130506120c1c0807060f050f0603160b07 65
    0x5861038085084141d00741150075039000080809013441c43c10705164140c0900305515028103041c00c41104038540e500c2c0b0130100010050313680c003070f0076840c01c00300142c0e144d48100702c409109000d0702c01c00f12041c141c400c030300c2030b4410360800d150b217640c3d01c1c0041a452000d4809954a81e00b440300c161007610b84402040030550410f40c2c031740710514401c02c548043c12807202521010894645804002410499a184441d151074500f02c11410100b00501d00e40c025040251280c602d01140c040010b4010f1550340d10294010400180600421803140d0141c41600d1160aa40c410152601d0ad085d04480c0300b1a402004030305415046402076000e82104040050014410008158000c000c100c40e0b0303000c1e050b8080c0312501c030401d009452810b90003083c400b40b101d4001703021407982ca1000513071721f15102d8850310034040708a0110081c04059411a1042504003009003c803c82a00c406070060804036480102c5017000c0300828850301d030106a84c3d680d0030340f0780e045c0e50380d4600b0010003145507404a00112a5 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 505990251 1250 505989001 505989049
    0xa0b07031205101d060a09060503031b0f0601080a051b01050906031306110706061a030c0f04050a0b0702030d2118051b13020a0206070e04020c010608100b030c0a05 72
    0x44424507120364111040544071084d0742818000d01280780119084221a182069800d0060b5180002030b100b80c402d0068449070a00c070b8540010b4200750007a295000c2502800c000810229800030b03134890614810b0b8100ea001c1c11300309048001d03004014203174a00250081001c50f1180c42c0945c05146c02c009a80c007040c200d84001d0782c0364030455071046100400c110b0049050001e10001d0702c00c040c010110200f080c0002c10076113195034050b01c001040c5030403146002c01e02c9500040144151400b800001d803a103001151a001c007180c807600217030012442880b840030314801c920f01c10300d41c1d88c007960390705031a6203403c100440d44d44001c2d01c00d1114040502c40241151004560104940003c500304170b5a0000300524a42c280700c0b800f26901040b40749180100500d15807240e0008855a02500074030f440041d1201100015010344035100b1103604035801d0070004038800038049440c0320407508c603d400300321008120091503101e0003000700f8650b00c04811002003010703040c28060395289e03000c2c803000440 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 505991501 1250 505990251 505990259
    0xe010206190f05040b010f1a0d020a35090102181005070204060902030f060306040312052e05010e010306052812080319060e0621010c020105060a0b0703120510 70
    0x300c43c401c44040d15008080801000700500074000300c0060008550034112441021403c94643e1041c4140045c1c0c842d8009005101d1520070602c4402400251100e6400707504a000c40004807440307103032514182c0c40700501140500780144201e80080d080301c46041a4040304c00c00300300782d400910302e185081c42402c2000b80e00694883c85060301806803c007006841c0c6c1401f00d681509500018541d5000f40d00c582c090002190700540b20401ba0100400081242e40c0c0b02100c07408003640b66944251089008480c0040100001c6410401e554082e682d0070602c1607802c0046040e43c03281c0c814550001d03400104010800a20364400e904c810b00d1071820741d05244c4d2180381c0c10f00c1d0041c0c10070541c0c046801005010700400140c0c0d10b9200b001c02e42006101160410303500c603040c410054622482600000c500700d12640950901500c411008030080100039050000030f0301901040b175080e842024013000105091281c2e00545500a03010ba450b0741c140000340f0281c0005010103005407140712003d1800003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 505992751 1250 505991501 505991531
    0x10309111002010603060c080c0d0509010204170a110603130b0603070803041205010b191503090b091b0402070b010b0705120a030f18120f050d11090a060e01020619 72
    0x8001d44506900026100e881c508000c0212116085407000708403140c001e01c03841c004d0001c1035981845c1c5e14007000405480358200c6900901c0b1700d03845514141c10100d40203031110404030340954554050710301c2441440e0710b881005114401203e507142603c641c12000004030711513200c12a40803d02408841003683c645088070f10315000b680c02000b0750340d40102d4540c02c1050a0091100f1044151400e20003e13013a511411501c001a000d10408001c64000041d05544242c01c1030005e203800104001d080d043c0410043d4989240e220000e000b0b50383c0c41c103d2505824144203c0c2d0009811810b4400d0507400c01000400325480b0542c203036840d200d041c605441d02c0c11600e0041014200c0c81d00d0000d80504400402000c0d1801440032070521000320b4601c0d0081215854030707080c01000740c600b00d002101c0c41d080c2a1654018031403580c1082d4580b68a0500d402c01ca4401440d010300f0894103c2c161658a82d0704481e0711005100f004e006030030030320201d0040084003500c00c40c454130800022607a10f207102201 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 505994001 1250 505992751 505992769
    0x11401030501150603110a030e03090d12020d02190b0402030708070e0613020c0c210a0f0203010b09071e0c0b0702250b27060d020909220201030911 65
    0xd40701a59103c1808056100a41100c40100700c10306081c032105040d00030500d40ca0203411541c00a2649075031300104a03503410f008582413a00b0040c8041c1101c1a2414841d05c0004060882009842101c00c11200d03140001540031400c1601591510f044103655a07040c52104050822605132040310b0300420100c1003804182c1c0a00b0266450641c43e01e4448108800f04050b1000c5201d03141c0304000e201600306010031490020b42c410f903900c64140116181c008016000121144503901071200c8841c00c2091aa6129028a00840c02400740445503810010180410343e0100301044803007801142409940c040e07540340702d440c1c1c20900e411914540b0345d0381c02d4031400c580e8072006030001514400d084101c01070b41c0c41c405241071450302d401801e240545c80d0078480c11110344440d065012003800e500802c40300c199030309103000e044561030740e225081c0c000103508101d4000e4455020034000508281844440040101500140000c03118203900190010f00c01c0c0042950040d1860880740380c507032292840 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 505995251 1250 505994001 505994003
    0xe060403021c080103021e01050c07090204081204050d1401020f0a03050711030a0203040e040f02040c020a030e10120209040f06060207080609030c1c090e010e0610031407030e01140103 81
    0x60041c4410701891825440e840b1100081848080c00050000d43c8403000710f6052220110105c140115803240142d0b0310307014001c401c075918422800085401c240310b80207002181c10810072034054013041c03102000d45002e1070050a4008200302400d0000c05e01021103510072082040006183c03102040c511800c1d82d01003000d83e030109407038400384000140e00055444001020b440035504004051200949030321852080708444046100400e0030302280000001e0250b60007082000780000b0417030042d4480402c068160081204144441c0250800c4d0b05001000140c0d6074500e855002c0d082a088000d4211400180d081a0740791340020000c0c0c0369114460103860590000c20344030780ba2244043ca800d60042c8941850740050200c00805040000c6603aa0740140c058010041c200c0c01c0402c5840e42c041c1d500c41030400d100200002816424485500d004250995115484880c00d41e0154196050b8450800300020094000340500d0f100394000322012901c0c20001c40d000f1803900e80d060106400b031b00 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 505996501 1250 505995251 505995253
    0x5030411060315130c0f0f02120a0918090c03060c0309051006081605030618160612240311040b0306091014070206040605041416030201020c01030902060706020a030e06040302 77
    0x1c80f0b00700ca49025013078040b4241c0c031040d041c8a4949020780061052850a6005081c04042c04541032130760300034485144556842c600759a12150104002000780d88240b1801018a4070880c0a034803a110a0003084100f40d00a80c2810540b4915501d02e401400b801c0742003001c01d941c030028680051000e125020160860800c01308003242040c1e6150704112203480341d07042d48440d82c801001180c40116003203074071903c20700c04009402e0501070854286404d03280700c03a0b400b02d5840030210b8916000784802c401d410b184201005a4211044030000105820306610300e4119451402c000064100e501c550034484043c0000c02c4450040010a10300481505c02c8000e6403c1078a1100c00c481031842014562078009503c10043c0c240035030041c0d103440000e040541041d445034006007e01848642d014600ca890b603084403801001c4043c0d1103201d000e40d0104a0050203040003e1615610a000740b001803074008104500d070040c2c035911b4200a501182220043c0354494030b001120740c40c14044076212b50b010760 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 505997751 1250 505996501 505996531
    0x120d0f140415060302092412060f070512191b02012405090411010c020d0503030402041103090c210307081c0603151d1c02010501090516050304110603 66
    0x890a8205500c0700d01e0035003080b51600d0320402c0540d40d20340800b81c000f5800c3d1316172141001c24503128040c6c404440c2c0f245402a09a10003000700c40300008090344a500c0c82500117150342c0710200d04071060303ca1144a1030541c19880c0104504040001580e42a41c951650010314002084065a204c62501d01b2800c0580d54a900c440d1880e01081d440c0c5081050440501500701e0410b40051001e0a01900207440440c0c5a203910440da4011501c00300341c00d400810300c581803115881d2a5950390b000711000c034011400d098a407100001c0000640b800b03510560040c2010458800a21220044402c0c00ca01d0302224500c202c3c0d4105d006000500d089030003509040c0d80c40d42218141e030711401c1814004904945460b0040012a585c440d40bd40312880450000c140c041c03000413019110000103008002502071070041c10000442101d8983d2610b90a070001d01146c0c0c0d80c0c10100b000c9480c11180300240150454114026510541c01581c0c0b2030f1140300f00c4058084230b100810490f400c1100c0220303243d0101 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 505999001 1250 505997751 505997753
    0x503011109010e06091c11090a0209010e0102060103050714181317030403050a0311090414060a090905030301050409080c0105040807030314130215040308180f060408120d0f1404 78
    0x1000d100a1001d100f941c0ca640360017442c00100312400400e800442c508501018403608010007000000c2c466600100340e282c07281400e0311640002d500ca881000c1c04201c114555118550010074031a0489410078003811100d89004411084d805c041024103512002c0b402c4000c13420000c818006000b240e15900846081001d0314001c484e68401e51680d0310780060520800000030b81c880110350324100d05207000b040d12035080b00882d11600a082c0c0c0c0070381c0142000d003c645141504000148a02c204943c91041e0355580c80c018030880d56001c0300501203030010001803080382007a0700a5501240b040d00d0640c6015a004444c60844405030307800c6402c164000798040c02c0c50750501400e0101d42842800388050300340340014200780301c0c01c084c0003401104086a41103007201d6000c00c2c1d030000c58000022650f20303a07034400c040c1450700ea143c00461144111011000309070130702405560548514600038440c0400d150081c001a0300200d840e031440c1900c2d506c8080d03403021240940c0c9140140025601d1480c209 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 506000251 1250 505999001 505999007
    0x1e03060105060415120204051807120605030604060b0315180607050a051801090506070807150506090408090d30050c031b2d060a051e0907050301110901 67
    0x410307400a80718003400e00c010300299100510b4a2001e000c14100300041d102c1003250140030b0301465024a90000fa8601c02000c0e030403041031000d20030782c41036545c10504089860760a048402600a213605a4001c0d40018001421a4842c1404801c0242250280f84900f03094800741c20040f60702c40d40000f4400d9980c0c1c1ca040b41001041d4102c0024185a42403c90b14031004050740140380d21114282520150048164012500f100203410060200c590ba0006402c00c0b8082d44e011392011901e0210701c0c44c0d040c000c0c84c11441403c3c01008000c240320302e04d0700c0d65101c1025a0700210242a031103180782c187c840000350080285c605000740310f00c0104002520843d100100e204200e100410b100042025a280200100894225035400c10310b030300c440c00816110741d00c3d00b6441d00d03011003440c01d50f44003443d4000280320042d9000d5a507004842c40c0b540c1e022050010b4600c1902c0d00400e21640200400802d1501543c4a9200c0f444500b11000343c0d42c0c420006c1d003500c3c8400120000c3d10340015884030b8a50f4 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 506001501 1250 506000251 506000263
    0x14060d05010f03141b06090d06050106020307150b010906230a120b090106140d02040b040602012f04030f05010b031005070905010c05030f1e070c060909140f0c091e03 73
    0x12400e005018040b225207014101c0c070003171105440c800d80340051081c10036540d030018a541c094108500b04015a10b07001e003c0e65a41c0604400e9507400644540d0031790850700b900803280c090303006070343d80510b0320b05e0842c058810140c68000d00105d560204d00041205070f88034054400161340d0b5440404640b0075642007001c480c004050a0f009030001801403001303640003002007a100b44020300d202d82d508081030000c0b00900a0b40c209082c0d031039000070001a065170540121000380b4024221a420015004040700740490840020800f14418030082000c00c0d141500c90b00385a0040300045690400c08001a040150106000400a5072801482485503010003200d000c2d1000707080101145a885e00c2d0641c1c0d0340507800c3c800481c0400003e58030b060b0380503134107289039a49044403030940320301185c50040d1400800340200781c0083c070705007400941a00a40524001e5a181d40b505040301d807100c4d40b0014282c0001007000d0040c201c20010103005032034880c074062050f1180485460501208010141401 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 506002751 1250 506001501 506001533
    0x604060902120604030206011a04080109080301030203060f01140112020d290607020d1101030b06070b09150402011220070803010503060105060c101e0c12050703060b0414060d05010f03 81
    0x1034004010813000a17000039402e03040d20f56460440b68422010a400740540c442c0340c02406444d420301d000e4404120340c000140d4182c1e8400c40982c3d4a07551980c1c5070788081240dd10038803000d0085e030f04a200c0954001c2000c03c012900014001d841c0120f03045018054524002c0345058800d02207507290305107880004440038048085a410745480840e400084041c00124006480801c1c5501511000ea010342d000d01d090303101c041c01c0103444003180e0810700d1300034034221140710f1140103c942c1c88803810544052640701e55030586130706602000c00701e2a0002420404006100d0010500d00850801a1000a4010780d03224846540e0303207604060500d0f003000810f03448103028240921800f0380324100807a807548607070f030f00b21000540003265503c0040d01e005d50840c0c0d9100c040c0703420001e10b4140c0d4802860b40104000300801c0c000c64031050012001c0307604600c604500118180300920185441c2044503000140c01042c0d10f040c4120011031104036802030b4058440c03200e2028080040001e00d0004117a40 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 506004001 1250 506002751 506002753
    0xc0c0516050a0603020c07090908071a01030f060e010e030d091403040f0324020a0504031a240402071b0617010503150403210c0e0a2303030408060406090212 69
    0x1152901000c5494a0000d003d41d800341a000b02e400080341104015010040090500c28008e804550801300402c1d44494015501e544c52a0301031040324990701c880d0303030489034841c404054080031600e034840100740c080e41e207111554a8000803450401c042003d450300103103803140024048600c0c0780c901920020301c074411000e504148810030060f0014005941200c2d0030031840040018a01c0b580e1040c540400c001110389840880c13117044c40d91b4030001906c1580c0c841d51082c00440002445100c070701ba13044031809104021110601511503080045141c408400740026062200942d98030382c42400080da501441148201c0c2002110b40c4100d0f0301e5a9031310305e1640c03114154181004a81c50f10f2140b038032201401940400304040601c80d09040c02071100300c82c4130400f50140045541d0282c00c0802c3d03000009043d1003420300c110703c3e04076190700c01c403101d20070f02c40d504950f00a62039003241403c01c540b5501d404140800652054240b01c02d600c0740d44203000004a6000e144100400316400c034142d2011 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 506005251 1250 506004001 506004043
    0x1106010506070f021f08040611090d080a020703080c01050702070608010b0d02030c04031b2c0a05130206030708010e16170411030106031112010216110607060c0c05 72
    0x740c403500300300c1d00c0242d001030030410407110070300218034807441040c0070301d0b0b01c3c4116100e80c060503988017881d039000e140316031030500c503072803804046d0301050140000c619440300680343c918000032070003c021300d8880d08500640c1d2020b40d480c1c44080c0c440d00048213850740d03651508100000907906208400c080c001750306082109505103800b941d69030284050142c24a031340000480d0300300701d0100503900150350011421440031680c9040c030b48000558030800a680032903d403000b11030704007807110400b10f560241d0561810703516040180c001c1d080c00b130000000c0540302027040c07000d610354100951207180daa0712042055450503040c0305a035140282121861154040303858803080d4030400420103035044d0a54801c81da02c507410300352060116401104e60541ca0b24200004120420381c0c200ca0b00780080721041125201c002c111401e03841a515131032850416455050001111484101e49001029020034101700c1d090391030b203003120310f40030030100420401d017880d904002c400c001c814400d0013a690400c1c1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 506006501 1250 506005251 506005259
    0x403060b3307061d1005090c0f1c080f0a1103190f0210060909050615031513020d030804110301060e01090b0f03030f0304140d120902060d0516110601 66
    0x4400c140e0030703845052407040007030a04103000c5150131a42c4004e800c1c5031040b0901e400140b03041c2ea211807500007840c1440c10100003170305120000c07407008203205024100030301e400784107410801002d032100c81e010901038020062038007140c040d40282840742103e041c040c0d5140b0600c41c0c0a00326100b04140e0b10750591040144009100007003410000410003070a156500003070b03510741a400c2038941c002c0045500d00c0c2c6200001e031846160803403a542d90040013910400d494550b081310100d00403404d21034155108580c0c440a600c240c20b4800d5000340301442c906590b09a65001940d0102c51a405500040c07501051101b0b2042034814420350440881c020403020b49403130305d902800881440313403200c29560707840e04003200d45985040f001d620310000d007584c3d501c10100700b40605941050710141c80035003160940f021018400550f010340104a81c54441d50140444901400740c98451f00483c0c000005004103041c0d0343c0940210360003007410f000c1c04081480e17070700303802001d41c1c4031100c3c52407140c0e10a0f40104 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 506007751 1250 506006501 506006569
    0x11010606031d0c01170402010c05060a0f06060503010b160c030f0f03080c09010f2303040506071b0503041203120e010507081f05100306180209011704200a05060403060b 74
    0x4045020b000301c0300421b942d80f400141e81340000400d0103810344c0518010018100302c194008684044c50100c20003a01d91905801c803141d020900800381618400c00c0f44445668921380911041031140540303502440c0c481d645c01b07007004400c0108840540030844a8010140c22040b19548082a20402414209400c00080c0902051441c2201b448500201002e034500c04207807000d408000e2801c4181d4a080c00e01e0301e0307951881f089410a00080302c0c14000d030110100401820242c6030880000c5040608022131a2508083c0000403424041c2603a03d4074829009400341040c00c00102000140e5840c0c8098003416000d4007e200e040d2045030b801c00307406044281c3c071100c01520015208070b070301c16800b480e0a8004242c150000381a101058005c001011015001081e100000380c0c0c800044402c41e105403014444117031002001c5030b03800504602c2d8001c407011944c3e03003900001c0492458950b11740c00305803194840e0b0420744065469070464280c6007400c0b185001d540514004d540c64991101c100c607 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 506009001 1250 506007751 506007767
    0x20109030e0d110d051e030705010e1203010303050f09100c02240a03181406092104050f0f04020307271d0901020d1505030f01050108071511010606031d0c01 69
    0x3d2807051090f41051014040101701c00115007950300070324080030f0203807407000c0e41c1c0390841c140440301903080c41c04400078644040364008184100710101801d590071581c080d20250441680400010011311207404135a5860500d009203810940710703031080c200103005201d5000e091074032141c0320b5001c1c0201011075440d1380c0704440e6502041e10700002d026688480c01c040d081c9060170007528040328040101a0100b0201d5171502413003500085030604446250003491410140d0740042c0000b02c2480704004078100860909800311004001c11502e540c000d0000d001c0382c005640341c000158105884106655422000d101345402039000c91b501d0608c0d01c0662000f12094068040240301d100000c1031040c5c000f501500c480d02c4030310341c081c402e00c80307a0001d05003101e019100e5580700e4414021900a02d050602c00d05040e24004405481800e00b400b1494404580242411040020000d00c19484110a10500010304020754021803990305030b002c0c04c900e1f454232544894042d000141e90040903a0420b0030 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 506010251 1250 506009001 506009033
    0x16020118110f0406030b040c050a0e07090303030507110f0607021e03090d08040e0705030406111806030613020408070807050612060f120609010c231b011b020109030e0d 74
    0x41d02c90410408003c02c000d030a06910041554901d00144070820400b1002c00041e00d01c2903810100c80381e82c86031303080791502b026103402c0081000a142400468400d42246901005034141000c0b004404c400080c503020071240000e03c5030f001202803140556042c407400c400c0000045841c6c0e0f00240c1000c1094480c031481a9003403180100024510070482d00000ba00d00170400d03801d013170145141011001d401a442241c003240c0191a188418194405a209650344094910301e0b00c4000c250740e00610a040c1d102078030240c0e00c03007110400d580c0f44005130700041c4003800c86d82001d800c1c0b051911240031715000182d00064031400303007030043c0205000c0030412260711440440311912945200d1010441c0c00208040c082c0c0c490103100d007081181c2c0015000040f0100081d503c1444900c03da604440d14030b0b41800d14000700f09010410008280d403e2491114040c541500000d80061030340801400c8000815141002d80d440e401c01800f4181c0011042178100d006441d04640042c5907030310502a50307800c0355 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 506011501 1250 506010251 506010259
    0x201240b031017030307020706031a0d02151b120304052542020d08040821070914090406091104020a210921030e061602011811 56
    0x2d0148142140800003405204000c00c00740041040721900da42c412110320002d480740c3c540004986100e0311034004124001c03042d030754030005c800040042402e903055060ba4402c034480c034030b403040c00400002421808602e62034654004001002c60303081a02800d6541301400d000c0c41004085000410000e00351140c1181c2e05010b448840030355845058275400443c036882401d0443d00c4400310342c0754809c4a060100c821440c026240303242c00b06105140b1030841d00180c024101c0ca1080728003491806401520548c811424014134003170740602c100e80c01e415010110341c8001880929a08014074030050044901c014076012062030104460410140004024076640d010003010312011101d80300315840010415540e07820082c81c0140140706c1035121504140030304c00146894a118482e07910785941c4204242036203001084d800c503280d046041e510081c11b44907040304c07004c44000d00529204900032400c81d50000170183c002400c4036281000802c4280311195402c000c20801d60b08641c0e1040121 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 506012751 1250 506011501 506011507
    0x120a021c0c0b040621091106071110030516110d12020d060b0408012403080c0f030304051b0d0330020301080f01050c03010b040e040f08030a06060201240b 68
    0xc500001c207958594040400624041004203881c0c1c3c0c0420f9000f6410b014640000a800d9100d51140488a04035402400700700e190510141c1c5042c1800070b0103441e4012a0900c40150840300480d1100405051040029949100b0040554151600c03050641c1042c94442e5462443c210402e0350b540303101214100740400d00c0400008400140c040300c500c0e0120040520102daa181042c030780075001806480015400c20014110719030101c50340e40d252521081e400c0c0d450510b191910003240d440305055074440e008403401600b042208200450060b0f2060f4000c3c400d0480d8840700440c104e00748042180304000c2444c1c41000b0903840300c904400400d5120140c0b0650b03001d510009940100c0d01c00c4540f4807800440005881080400d041c41d4103030b044402440569034110f104001c601c0240600300c030450040c002404920603015120350b0042c480c1e40203281d210300c1c0b6200c40140b1b801c02c4602910064a0f19418015954280914003030450021410f518410803070081007680102ea0148103a00c89001c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 506014001 1250 506012751 506012753
    0x105071106012603120114062706070506011e0b1612030e070e0105030d030b060f0f2b0b090601020d12110a0f03050106020705150a140d020405120a021c 67
    0x341c0c4954124208000c00c83e03a83d040c41e105c44c0480b5031024800c3c0c2000e0b0505540901c00d0342020011510010f80d001e040e060301c0912440342e1004044002480d6400450910410b40042c1d42044594040e1808200ca0320f10f51110000c00b000208460b04a061400b405000e0100e100460354007031200740c0e46c80025803140c4100d40c84224001d01e1428040c008512400d80006882c1116803c8a0b05030b0300300380e00307903560382d10500003d4003500c42d04100260000c00410048440c030b031700540504414080845140d140c4040b60901701c1182e401e042420716648480d030b0311a40c0c5c2105ca8400d0005901c1d00351040e68241c54100e0010351102c4000f1144001d100c2d10b01d407250044031040d0310184403c11030608141e1103021000c801405034482c6c02e210000b00340b50100201d0b40d107000140150450304000c01d0316035140042d03607045565070402e0100c0800c2c81a40c801c4100394291f0000030700f900880d98980140c41d249030104010040401c420415644e41200007041d0150301c030981d50707618100906400602c92420b03 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 506015251 1250 506014001 506014049
    0xe0106030f0e120c0f0303041e050703051005061009031707080c03030a02071a010503030327011b021002030105130903171e060909060103110402071e05010507110601 73
    0x12030040049401242401c03801c01c40560b024288a021305070458482c142c550100594034441034401030108207001c40007400401c8001c0c08101c80030302c1201a078000d20356076507500e0f10300507030b40a0311526552a07404220f61800c1c41c1034031520b09602d61500d4070031140307551540e404815091468400070240041c040c41445942e00031940f02601950840f81d0b2480c1c01c7c1014002500300341f004032809440041007441005074010158165407006000c0c51442d02c808001c42e03da005451041c0c0c031a056802c0e10210804400e01c11a0321903104400c42c10454884080e00904102c160060415001d00c1070005000c1501c910020340a60100d043c400210110181000d80f80c40344200c1c142c40c0340c00150300811041540490f01d60015030700b1704103005031a40b40d50b810401070200895a1a8040c0c0c00f0400401c0410340f40c01080c005504003600041c50412503807070b60ba0310b000c4940101032001c940380e9040c1040100900c01c0b01d500400c2458060106100003035074581711001889204080000c1605c0d607900702c00 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 506016501 1250 506015251 506015261
    0x1080606090d0501020a0305010b130605071e0f0605242116090b01110a0b06210307140a050a060209041514030c040507020d0c0c031211070f0e0106030f 67
    0x1c020071003104910700b4900307640130750f0210030101c001a0804000081c40740200c001d440c0d22040c03102c000e004c81d078100b04084646400c289c0042d140c03810012450194950a45d440e070002a0240d09040390801c054241002607540180200010003a0301e00d0304a000641c00642e140300d000102e030382103800074425808a4200c45244559020350281504009040640010200440d0655601409415950b00043d600c208032001c0e084500d80101014030300065850002550065004140c100440304030840b1503120118800600e04a51000034914140142841c004a035141c0e0030b07005040500990380c450307480d41980b0400903c0c4540209400c0110b580d5a0031501ca120720300a5445142981c1d5084003c40c80142c000e910f02038080c662075990541454061a0b100d54116001440b61041ea4541221404070802080c1c41983c00c0303d801000144000c14074080580752a0384a14241152444040c10042a0350180904800818003003140c0740c0c00341017060440b448c506002031840540310102002c1e107 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 506017751 1250 506016501 506016517
    0x7110d0e1807080702160308030a050910180b010e0603030426010c050d38040207080703030606110a0201020d082a031005010513050609060c03031321080601080606 72
    0x200c1d64604100010b980032190350b206480550031104290350041503044008606d010203002c420041001800071075003600300d542c015400e9400c88450401d403403007840440320f1801d01c0d80392a8140b4a0383c04113028030b504010740501422040d420040c204000020b81c1c0b44aa4812002c80b6840000104061040d500005204892080007484000760300380c0014020b6000e41c0c80a0051880c0c0b0060020040307501c10020354541d01d40720503460f0344da20755164100007114004126400760302001420001291032001e090700ca44a500d01180140c104003015140c00c01c1e40c00c100e68141d001004040250381c0c0000ca9917141240e50904c803419480300c000f50700312010110362100c1d00410b4682016229014480150701c145a00b11080c2541600c441c0111001d206041c0d803034403181741c694024010b03441c1110081501030340c002e00c0189042e44000d1800e081d5002201e1011184070b04400000c02e10007203407001e5504150318030305031811400340070b40a050303081c0142071181001803102c0016441d0316140211150341e = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 506019001 1250 506017751 506017789
    0x40212070801110d1b080705090a0306060f0503010c080c0f090d0f1406060d02060f0d0b0a12020f060f0d110c0a14010609061a16060501090902040507110d0e 69
    0xb9200d0600380c00c046138413820f25152110301d00380381c0544c3c1006144142c1e805100a9035540010744805a00b100e80782c102d400c2e890743c00080c240d40000020103601c100402800001c0c8038010940c0303460209030849000d000c01c00140b001d00c408105007501d000c81207030401d12106520070b4907041c0c80400306e54103038444000103000d01c2c0940807542c1881f48024842c054044a002113176019621907041c004640041c51009420580500030340b0207148500c0b01806016000d51030000c1c8500500000a120041d5a80700200000c0c00317909160940c2022401e042007060b0a581a91030251001d200c07504610503903c05041083c2d0324091041e910000504440e1841c111008603038000040d1b0801281c440250248007101d5031a141c00010940d0440c0a400229420285401a0130720040d9190707180b90b100c4160824900c0710f0100d90720000e0f00c0b620400380038207552080001ca601c084d106001c00c58a02504442c144458200d005d10000d0b03000a01d0101a9428642441c1e1000044041030400c1c061400803104 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 506020251 1250 506019001 506019011
    0xa0b1509040506060316060e010818011517060106050712020a0212030c16060c03080705090d0602040519180207020f0405040609050613150b01180305070609090b09040212070801 78
    0x42c46400120280a01c80c03c4058a8144686109059545d03006102d031001085410b003100c1c5080d8060000e456100f4449415408a450390412280c00c50300c9081d1412241d0480c444280240440b01011034002c2900c1c0000307241950524001810b00d029541000305010030121a548016209100c8101055805130a4403c803103048280c0e29240e4118140200c00d910810306c0083c25090000400012540319468000840880342c408895412004044074148507007000742145585800d1000b0103400d00441006071202d05000420011801e5481c460b0224a09920180950700b032180b160361261869150069407000d6078800701e640c610031b581d60654040e103400700f04018014903400140c00c0500ca0000d0b42d00c96580c0086000790800011b80241c000b042404141424a0340744d1702095100005052001c6440b07689400011038800d607030000c075050781106108000e200e40000f526000303404401b8040c0000307141400410804a0020300191043c01c024904d644040700900c1001c02611210f4001c2c01 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 506021501 1250 506020251 506020253
    0x10207020d061a060f0702040b0d050715080105010e010e01030e01090b040c0302091308040302040504031407030e04051b0d0f06170607020d110c09060301060b040611010e030c0a0b150904 82
    0x401090769909412001d82c2c040f840d58501c0c03409070126001e01c449522000d0800d402a002e001c0140282400540c1102d070214031000425001c1101c1c000520116860b0743c0c10810307803400200040d0303040e4015814003100f485500e946a8008608420340030b400c0c0780003c0c10b041c058200070302420580b0405480c2070041d400b44014006402c602205503802525000e0ad02e4031008400c6211103403401000d0492002400140014503003070300140d410034001e02c0c041e000b450081000c500a603209040440c0030800c070082d010b2030340c1001c0c0074040d40541500b08007242001903003000d000c548128900d10300e600342d9403200c9894042c0150f101e600136044180000c452010804180da07070741c240503a0350714050300c40c044070000203a02c9502c01e854a8150403018168000511050044108001d001d00b039165498903000f0a0740e050308000340004105c03075900e012001d400e29000b1030850703251581c4143c030394000300078125002800050f500724581d48411007000c40d64811061070b0f4205e000200300c1e80d0024901c01400 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 506022751 1250 506021501 506021513
    0x6062f0304120c140f090c0f040b0a020303090c060910030e011d0304060219020a033c0b010b0f030f04060f051014030a0327050a0b1e03070804060905010207020d 71
    0x280948084d007480581614103a403c0218940110002c0c60f480344500300000c0a1190b440080c0c280c500b600440d2031300b441e0700c541c1202d0042d000001c400e401a03101208018a1507800c10400260010603603460b440c01c69001d000c28503201d01032a0070b20625403130f40415860b850095002d0f04940800c004c407c0414001e40c81d03091340740c1e4000c3c031442c4014407520a0549590400c14401a10603a0003050550302900d10759070394440d4a610020500140c201c5034a200910b5404002c858050106c00c000e8034908031186484003407080181c00040c0c108006100404903030340d42c9411240c12603441c2d100021207a550746003100281c41c1000002a1a03400c0c01c06101048400040210640301e4000c0441c2003000042d0500d40e60398500b4801030300044500d00903001c0114005e0031340311141e415502007141161602d001c9a002c194a40c000340c06802d000544400c07032889440c02804c800501714015255084c40a00109013410181014090960351001042046405d60403a14490b60142030031a1444c6141085 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 506024001 1250 506022751 506022773
    0x30c13050f07030b1806030c040f150b03040b04110d06060e10081f0c03060801020c0303040b0c030405070312110d0906030e0c06070b0606040b07120306062f030412 72
    0x103207080503210081004240240501c1e603c105010302002d151011207513107040014000f41c945501b501070b1804050392a1135900503591400782d40d40001c551500700e1580320100001f00d5010000310a000c2c420702c40080c29140f480c0350481d4010300742c51000000f05000654441c3d803c01d0040520340703040000620068103100a51107580e0801c94140b00d640e6a407951074449441d040030809880100c50680407521450340030341c0c0d1368195450000b8009440340851806c9920045890384035500100801080189440280d58007072103442c02c0313600b1400c1c03a45d81c0e641e0f40c1c4603500004100750120f1109521081c401c0c003030003001c1a05e40c2c003118025032455401501d00c100030b00601c40060708100c3c1d4421024030015801c10200c00207807010b403600801d9150a240118003515280d8040f504200000390100408003402606016800c68041002c29032400b404442171540880c050004000d00211060f482903030004202004503086407150700c441501a08601c0380303030400010304aa20ba142c5003032045500c58 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 506025251 1250 506024001 506024011
    0xd091707080a2001083304090813050402041a0a030b1c030e0103020f1b1203070f030608010b060d05130b10060306081612080705030403030c21020c01030b030c1305 72
    0x20300c01c00c20b00c3c22801107a44038004c650135610201910300c030810000920303ea2288011543e40440d14102400b03000400b50b5900c500b040e19801000309070001c804000c0b43c03542e00108800c8400f1460240f0f0044021800c0020710460075400c4008101165690300942100603008001170910303010080079a0104002520a4415000200350300c0303608555500074802c40b800d1035500c3d03543d01c0c1042000c4c154490a45004000118a4001e10841e90305050060000e54095131494032401840c4803050700060440306141d021000980c1003095125107034440310225044080c0e4050b010805503183c1801040001d540080189a040c21100b0040c200c10390241c8101912080da400f40003199890349103036500c00180b120501c0c4051000410090160070707a40c1c45040c1c6101d0310680d0b003020042d031607080c21074005034015008508a50840d60400c00d201000001d2800500180761030f00d81c0c00d1000175514501c914a043c14503a5420100205980c10009412090001898601c0281c12103100901411051390 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 506026501 1250 506025251 506025293
    0xf040b06030f030301150912081b0a03080c0a0309050f03092e0e0d0b010b040f120b01050108060a0e010902190825030e0d030c110d091707080a 63
    0x4081080c610300480c4039000b003801c0100460469003445000560350000300b4880d014001c0b04100000c2032000e80a4516440d4001d104c540e031185545180086041302402c01c0b810180c12840c010400030350480e441d1504001402c40080d110b124041c800d4000f8189000c001d80a480f40510501042a0000040c4829441503c41d00c19480d950303d01040c1d0300c40b4916000c5800c00d0b000005084080c810340828800c1030b00200121101d0110303448181c400002a00301041d2040c00040c184440010003103140d00a01505450150b01d2003035480301e03603803518103001d6a4108030807003000c500c01e0356403014443c001d8140404102c1440d65030380031510096118100c01e8069103195030200707214a010380542449020b106200020f441160017001d0f4440035161004828150b0710107640c0c805900400410414240a881c0000c407916140006815110880d11078940350388044d15082c10594850200c41c00c03580b00c601d40c0b40c0e0b245c601d0180756084c840141c0143d040c034440d021182c400d00031102d03000d82c80108595 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 506027751 1250 506026501 506026523
    0x3020c100906060b0720030309100c12050a1205060301110d0b1509010f080702150415150b0f09030f0a211b020904020f100306140d0c060815090f04 65
    0x450ba4820f030191103400b41601001d15101c2c898202000203407603540c0310003401e4274580f6000c038000800e444032050701c1000181c00c10311498100402c1074840c0c00b0041850410a050120442d0005c02c207030034002e2410005038070703503011400d50b440035041403c2c031007103290015440c2c0c034411018900500c04802c0052007040405400c650100482e41100c01602041c0e480608a00d2441c80541d541c0d079014040340c0c03c5124100e1440782e010030008003540214461440706c0c40300005850321805881003008400500310f00c0280402220f008141280e0311003114623112034841d82d40000107407c080d00e000c0701e1446800755002807810007004d611a4200d9041c40d40000340c8031204207008461044642046a0442d19a100709901505d4a2908903610900c000c1c90504003021074008180000351282c202008251034103414407a11303100490728170686030144c0d0681241003d541700d0f0a2070391110710914040c00702c1301d4013040d001008138081541c2c0301c1e0043d00049060514920115203000700700c6040d60b9070032600d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 506029001 1250 506027751 506027759
    0xf1b06020d1404080706140708180907031b0c0201021509010b0109080c060904020d021323010c1109190903090e0a05040c15051c090302010b0102160b0a03020c10090606 74
    0x140d0549050b82d150f83c005100b240c2c2010407d444084000405c45011801403000700c00068044000f8800d030300340e00c2c041210100c0a5002e11002c0c8002411b410141401c2044003644084003180b09a400c28507451305005c550500d00040c1d080c500003100441f1076000300003c03c03c0310601508410801482030340c400702c80ca07a503511307803646410003400200d60004040014500525054010b08030392400001c00514060100b40907a860700c9495020301200300080d4180b103246081540c1c0d40b0341005007130804280807021540c1c0c8411002e041d6200034801c01103000440d501c40c01410a08055a04038075081100b0030b4a4140a060404d6504c512220700048400143c451030f0036000f454090365120100b400381318141001300c0704075081ea42d1942c04025043c803610003801112690480c003510300c4000020142a00d0400134251051401d0389410342d072240c502c108002c1151000d050840307034104842345d00d600a14000302c0c007034451038011007801e1040c45800c52405a050303200c2c04031980305100800040340c0c1c07 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 506030251 1250 506029001 506029037
    0x140c19050f12030f0402040f0203091e010212010312022a190e0a0b01051c020c060a140a0b0411040e1806091e2b02060f04020d0f1b06020d 61
    0x500a01e41c0d004003d0000c2249006551005078000d4802800030030300415001d183c2d07040f038100b1541c00005502007146030940c0c0c06410009010340000400035454100c810a5540980c1302c1884010140e031f2054002299652013401703c1940c4469a0158040002800c030490030b5080b0340d0181e09100b910002e003141c030404c18643e29041103c45120070900f03c0d075112010540140400e801c0d40c3d05010040016844001c0f21120754a0240c610b107000580380e40307010080610b40382c0d006015a0000b440e00301000035040c041c00f10756a104198010100e41d242c04107000c58080c0c813054107a2000c51070041741c0030a982405888003841040701a608070007100c0102203031591118140ca110800760481400203203c90800d440a01c01003440200311000764101e440301321080400e401c12200c1300b0161040112090b6814010503400c00d003100300014042c240354000a60f54910311074007e0074105030345107005c10030060406140090007018030104c90a40d58400294803081514124000100890f950442142c2 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 506031501 1250 506030251 506030263
    0x120b06030115050c0f061006020c27090f011407030c08010b0409020a1e0201140f040201080f130b0a0f11070b070f0c1b03020109050619140c19050f 65
    0x503250300d80403800b0400c03240a4401c2d604c01c0b5484003840c007400e05c01d01c00031041006801e016030001d954844040b85440b000070b0900340307071051041c4508002e454102103d5242840340f00da15500e106981010784071071507004d1903c42000d03070780803480d400c0c01088400c0200411803144181e140b0780301840f58440c80c803c1116800c1c000d000f02380c86800c06100c10310a9101c03c0d409400d000103103081c00c81c840c1a0314a1541036480e00010703a000140c0d11a1104412074500e89816900290405600b0086042030b0780003a0030341400509116003001400d0020344a200215010406583c103c070b1094172500301811068041c10083d09a51051400c00c01c40c40e50300400e0908450000c1d42241340c9464580f144141210070184502480f020001384202010119a0920401c07401654128000c00c0d610301e5031001501c05103642c0d008500c584000d0150b1800d000301d070960f20680c942e851406074010200364030700103c0c81c014051040342e00d20503081c140788901103000c0c0d01070760390f40594121000703e500444020b548030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 506032751 1250 506031501 506031509
    0xe040c03060b0d060e0f0d2a0627110307062012031f06030603020d030e130f060311120304170a020405090102030a0614030c01050904090b0106120b060301 68
    0x19024001080480c0302640b003103011903001003252a00c15016102d640030f6132182d400c03400071500a030b2800501040101305030340010302c540c204401d48107405c0013071038060340c0b0707444c1842c145407000340780c4404015042c1c1c4484909045015a2140d425480780b0f182d132948141c11301141c0045810304081d00510b400034025003260350650b20855101143e000c10040844e09140d0310b005071140040c010003825040b03002e14815101e600b5a46440191414001d918000e264048018140350400501c0960ac0e01203001f0580c50b00b5050094612609030040380301c483c1000e22044080d0b26107908103111b8049c0b40c104a00301ca008502c82c24080d4a0401049403904001c0c1120451b03a004020802204050b0400c0007580390010302521000c8482d500032405440b000c40e2801c40c140d50000803c00620900e03c507080c050041045c0c0e818080314620042035a41d4400364449040c044040340f64030082d503854114a00040d80926001d0030b95039185409003405505940507902c2c50b041250014241c24150142ca0480d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 506034001 1250 506032751 506032763
    0x602010519020913050103050a0b1e060d0c0905160809120717160b01050108090705131e02040f152f03161b0603050f07180f140a0e04 59
    0x108407400744010003036000190164014245070840d01503008540f103114021030055001d030880480380d1034207665804005003c504100382c01803046000b1001c044031503910540c03e54210100c1c51041c180306091b8000c65110722161801d140030031108070310480500e00e10104546820000b500c1c2c080040c0c2e100c1000740a96203a8003400e00c2000d0120310414640c8982e46001044c15180015024012500da014404151401000d0100400031940d000307051550050b914000340c00c0040c100000240c1c0082d80754520f02445403100001002e140c2c140d08000d540300504031085507120b41c1c03020864808505842003175000c1d4440004801041c1c0500c0e9079800000003540d91240c808807103001c4150014031442d8181981c44180507440c5000c4d000300102c418a80a1050b84020624084250030a5070703803a08000304040c00c1101740b289074601002e038103400104a042056002ca0840c80b40904c005060b40200150030741440c0000e0a01d41d5030a480783d80b0711043c2c0e222000203859102c00304c0030401c250b60081079 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 506035251 1250 506034001 506034031
    0xc140306040209150a18080102030912090301060807080115050603040c1a0706180203010f09081605150a02030906010b070201020a20120f15040b040b19020406020d030606020105 78
    0x5141660080c00344860050501c803070040d190f005800e13550032540b81100806c2a4101010076811046401001000c0341c50007946107140c485105500c441141c281c9070120b41010a5988440d503085d00080090100078045a14840c1d507200000c0c080c00910554801510310a0008641801c1101c04c4a00c1550440c110050082c0303082e41c0f20640c011108003066140009004d200001041401610b2640700002213959012a003070040608441c945510300c0c4145103851310850004140c1d40035100c0310020624500c40100c06420190f007403035a0f034600308186901d0441005010300d0b056000d140a032000c0c4d0f08659040ea01c40c00742c0d41c070034400c210019000d40c0c841d0400500007050b04910741140401f0305440d80c03096540030702052584c8180e4040700010b80000c52400d80c40704003004900a025521000c10401381010703140e806c03203004050000b42c58945032038005003d4044030700c00c2c0404910710084c1103580e1030f03480c100252603150216146001a04000c400500e180c41400780c2e50250300032020071a2 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 506036501 1250 506035251 506035261
    0xc08070c06110301060203070b010918080f0403020301050702060114010503040201050d02030709050303041401030513080f070609050610030326150d0206040e0106170108070501032a0905040c1403 86
    0x4100301198801c840080e00c5003840101001c50b54051802419a40c00850b1103d1692620215030401600504030446c0745c600c44020344010f003403120078125000184140c0d296003d46812445114039007004e074056003400140a503180d4002401d6040310300001f080d0b02503011141c01120301d072100b9140640080c4040c80444216840c950055030850300038148400034503a10ba0102e07046802607807200071b4505030041c20355010358041c040d03241d000d01010608050040350fa03448220502454030200c01c11200460624200032075079002980d1540c02ca02214924640200c0c14003040b8241c1c00110002209400002d030100e00240c180c046000c02c0001840c003559443c0510b80c0c4004a01103082e074440807603800303100581c440c00f0080014103010314408115605105020700700c44c502c02255600d5142600041010780d10109803030301510002d29003c154608540c001d06034880c5040c10031000c004100104d901400e801082c990119481510144181010320380c003074582c80122040c02e160010208000b031 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 506037751 1250 506036501 506036507
    0x31911030c0a0e0d121209080d020a020703060f05070e01020a0b040b091f0e0f0d0f080c0c010212040210020c010206040f03091805040c050916110c1315090c0807 71
    0x1246200390341ca0001d081d031810200050f95003540031000e036541584117a0001241d036000300b106078881034070341041c0490345095881118a02c034500c102100d0690104121001034401e205000003160490400c0c490321414000c0740e0000c00003556803d0100c0c4d4025540c000550000c2199404250400320700d090310366880d12811011400204054201c0c010700d1208604c03958299103146001d00008000164a1a010300300b078500001c11042d66500c4d44102c0b0007000f540e500ca0030108608003140b500100780d4072146c01980ea07078024a0000070141d400401c2481040ba004101ca501c01c6000f01c2c1c141c00221f0320035000b0703a20bc0740844000c900582213580041d000c9000c02141c40d00483c4a0f01e44039403407543c2d6080074090600701e80c0b40d56200903102d406000500c01a180381c000034200031549a117031403c1002c10f0407640c00b1010070441c140101310340082200a014805403503000c0024298002003000d01110100501034141c10b9804e0749900d440100301c2e10003900c1240c44050441c0c03620592900e03604819 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 506039001 1250 506037751 506037757
    0x30c060c030b0411040f0605070b0c0a0219030c0c0b031603020309031908010f1d1504060816090f0b0105040315151d09210d0b03070b031911030c 64
    0x20360305041d2202d007441d045840c1c42c840c450b14440300011507030b151400c0540008041c1016801001005400c0c03040d04041440f00c17040d41e400080080b4600e0341c44540440c240e05014801c20b044507181c843e0000c940505411002d0b84052611a29070740201d186c449440c0d0b9030601081d60800d9240015034214400e242c02a40250b070030200100c100e0f801c005c0b000b419148160400000400002c5160004001c00018100c060001c5e03d200082c1d0030740358040d0805108a280001d001050b0800381c030103144134030f8486901540c0036205200541d0032000c000700000760303019080d10500c0043c61604400055400c0071f4807600384a440160360b80e510305851341c0c80351614101a44d04142d03200340c0ea884c480c2c00700c2c1001d60840c0010161662152842000d90280200f0800000e042d100c1d150058984201140f01d50b20750601c4403203084042d035464100a1600d80000d103000380c4000c0d010700c81d0020208142e0342c004d002c0d5118070003000680306130301040d803442c90595044054000444606201107592001c030b680c0a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 506040251 1250 506039001 506039021
    0x509070501050f1b240717071e21091e02010504090207050601060f1107061407080f220e070309140312040303050a18080f130f0e01060c030c06 63
    0xc1a04003158102407441c41d03140d5801064072903001000038105c64000006240140c0b03103010011030689801c4c10702402c02c000c0301c901105004500710004070280e0049400000050702d090381c0806030a5605805041c0b0015901c0624900004105203500c11940b4041d02c4070300c0364042621101c82400d44900e09050201f5041281030203424840845c5400c1350748081d2080c14002ea0003030076654546503002d040045034a0300b410420558010040414000148040860360340345845490034000c81580001c50003001802005050001030f04155031030303810003420900c05820104100741900f548a28159900d81c419458500003050008034120b000740d0107401410700487c0500c0c201e12012100302c0c00c60b4801601310300e0b8040070340b06000606906125103980200b281d6070030050141039441d054001da40801f4002c00001e40028030644910000d402d44100403a00c42000760016115540782d080160940200688261200c000041d00d91150245c3c12a0603050746410341d0007445a21007102500f66441c03 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 506041501 1250 506040251 506040277
    0xf1a22020c03070f03051c050c18460f12080d06030501020706050906070e0411090901060906020f01021912060e070509190302031c0e060a091404050907050105 70
    0x3c240890706443c80d18010b00d100ba5902c0ea13499254a180302021106c4180480c0014a41010081e0040507542110f0030350406070041c1040341400d41c00a07210490111203e204081c1030340d80040c072012240c0300300c1032200e11004442000d4038054443e8012110034816040d85820a8100f0060500040581c0200300e0048084601c0d1a80c140b515070300740c03501e643c0211201c4e1340c0016007000303000540c8112900228002c01420316401c00030340041600107080c0000740b0807561503081c0c010354102e12084520654000e0401100c83d86e5542c40a0007000c000d22482016002e40c0b406485d050006108840d4050240144c084104030140001c403441620329018182c0c166803030700003191601d0b044040b2441400c01741e50381c1e1f0341c1e599000d080c8582c84a000c2c1d8219500c030a420018401030350b000c10080c01e12034041e4228402c00320504411101b1519008203660401e030300054039482d80d0341c4010540c00b40e902c034003001a000c803010b000b0321045810840348145170781c115010030b105962051008003410910b0b01 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 506042751 1250 506041501 506041507
    0x115081c20030f0a020c1009150e09040317090703050a140f06010b130608060d1e08040e07032f030c130b0c0601050118090b130f1a22020c03 62
    0x350140b40786a1100400746a00711001c0b58600d0440d904002e9801420303c16503d0f0b40380f0b00801c00d8044c0c400c035814042c1031900a020b040f041030b8944140022a6076420041000007130303040a007805800b100d403030115102c05102510010b02c4440b03002070000c045a60200040000d5007107a291000060344001d9110f40c1c1c3d0080c0040903140c4001004114060284284610f03235904607100c41ca4025042c0368410303814030042008000081c1c1da5a4404800d007a002241000c04a500c2c201c6103110300d501050062610401203000700c4e100c020a05168480d500c00d4a0401070801500c51003040300190011000942144a0310030294400b00800303980c108036240c940c24200356940050304200c614030307009000505000b186100b1f4141081041da4010102800c01131110381d4442c03411340090b84103005c0c00c100c99850f0b000041d00c50b141d003002d007600c3c280306500800201c0c0e030a502340b0010301580c00054242e4070304c43c0c1000784240391201d641e0403c5400030500d101654650461803010350070a02c50001140024 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 506044001 1250 506042751 506042807
    0x150d0218041515090305060a0b0a080f010f140906070c0c0f140414060102062208070b1005090606121b03010806010e0106030c0e0906040b060c0115081c 67
    0x19000340e24a50125100b00000203050595140f0200b40003107080041140030760b0100081600400c803d03800203240031010550b0040400480c2081d0901d40c80964280301d86c603209290441c06602100c449078050074140126020b865444000354000d0344e650740382d600300d0070115040f02d001d009030b5005c280c81440204045070b0340d141c1c10900c040c10780d400f00f00d1075406809044044d18140c426041c00681c52005000d02e4144500001c0d504c00c4024241c00040808003110b800000b1003d03c248603141e402145a560b03851140781c043e29020003a92640e030041c0392160045220314208880a2140f1806001070703080103900c004101500d0310103010409c083c0b0042142e070800441d4400158060601c400041001354513101030010071880581c8290105441d106102000503032000250441040860b01ca6a19803610400038000304000f004050340f0400010b40d00d00c103150190001d940014802035109400b071398507031030b1030303220029822510080c0c0c844103000d40c00c45010702120130070f561101075148152409 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 506045251 1250 506044001 506044009
    0x302010f08060a0e0910050f04050a0b0403180b091906050a05070c03050f0a031701030f030f021507020f0d0206010b07021c080d0b04051303210e070b1206150d0218 72
    0x4150b5000300c45402070000c540341846e040c041d65070055902c06015050349001c0d142e8940340c600b1210000e00710000c001c04074052521400101070014034084104452a039a41c1c148002e0750300c8440c490303004980340c0e0910486840015000c0c002c90f515912a28170340f80e20010100d50030391000c031003204c00050094000c40031038010402070801c10422001040140e4280c00c02900c1281c4d0b82507420f151083c1280140300040b000800801c0e696454100a001034140d10000d030f044c02400e03440b0680300c605c10020013119650010301c50028012540c01d0f210b4030301004c04203e840c3c0b0002d00070820300c140204000c0005080034044118031340e4a4890210303000070143e445003000d41c8100b220307941d0703d5294403115032185010700c1076a402c030b25141c041441c20019075401401c120203424104040d01a51001070003a80442c0d00584810072082095404040c1c41c0c600c8000a40c020848110720500e030280040d0b0309080100c2d6542250880090755070800409115040103588021450b5400ca124140003185a8035 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 506046501 1250 506045251 506045279
    0x3040305030c0309011b0c1e270e1b1003060e0a05040210050c0a0209090f0f0703060614130c090e0117061b090909120301030819090302010f08060a 65
    0x4121405584d0316400740000410b403031034602c0002008010f104600001511402c015401c40354582d024106001d5800355008000741564424100041c1c690500d9504040042e1448058500c00c4000c01031401c2c0004e502c1d9a0303020704900d003014480d6040c0000001d1800071003071204104540307404111640c0343c0400c40304280c0c2c00e507560300070151100248000c52070840c40c07050900c502484c01030304003403400c0c60165a80400000c081d00450f10170001c41c0b001c40043c45504041003035101110f210300d444030400c0c2e555450a200a0318030901e400340205d0b5608138050780d18034400c0300804040c261500000d0a6000b00001505c1a00744840380c40006445d0498812907030080803081d581d90880c000001000c0e090034001840c03200c9070130411201c9110303c41004217440d4001c1c1c0c141c80400b455907680200c2884d100c081030300c96800c00707808800002008002c100070103449125001ca91203d250240050380c0303018050100034045400c0e03401140c007441c4942c0d1126400303100280740056059480c6100010a9 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 506047751 1250 506046501 506046517
    0x9040f0204060804122c0307080318030c120706080702010b10091e030803010b0c100e0f070f030c0e0c130f090c080f131a070801050a06050a17090304030503 69
    0x9a50f04080005006490f4055000000b0714140180d212200d203500c01c01070903014606030a4000748038558462a1404c0018102600f1450200c03561004004041c800481404129611034800c61a014520b4206008c204400d800b03c1c030018050b460030400190f90154008000c00d007159039a00c0000c2141e90361070001403c82603141c6403400007508151284000b058000b800d071040388018441080000d100604a07411114500303080c589030300d101c504046c104000c3c10041c6454506040300c18201100100e004108100d0040881c0c0b2142d58136941046100c056100107012000c855004110f08200003120603804194000c09601e002e10008d4040e240c2440c58005202c000800d40c030034411882c5520503220010b00c2400c008800385401e215185000354004d0a2400300b100b482407040411280e060072403040760b225080180d551400440c010407040013442a244500c048000001d4014010790443d0a11000c550300d034048103000a911000c9200040d124400504c820400000810300a20147c0705107 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 506049001 1250 506047751 506047757
    0x2a03030801030b010b0319020d020f12062b030c0f1a0a0e0109150f0207021203120c28090f06080108010e071211060d0903020a02040507021b010509040f020406 70
    0x55041d8101110f4002c4143c12a200c044403c00c14000f01040f008400038035052080005aa40c12000b0088400783c01000c410341a080c0000c5402580c04081020403481903006444020924030702e206480900c0344041003100f02400701d0a0b40d00c0100344106040c0820030700503682800c074406251b0343c2200380400480c0030244654404c050009000850103980221100d400091180324120340703464102640000c0400c1109a03140007030041302080380c0558240359002085e000b1030854003c000c0b81c480d4030480c8925003a10741040041d0300890502e044c1e8262008600000d1150301441c5992074244584082240a11866817000980405e079940700380003818642d9a059215451300c480c403400e481c0007107038a142c0c2d0782001105004540100e68103441183c0c10082e030f6004d03181100041111440b0702034100c1c04503818070810800f0701d500040c8003000c06100352000c110f030355550a412629200c400710340034059403050f03800d45190361280010b4840c0b03142c000c00009400744410820000c0fa440b80e4005008 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 506050251 1250 506049001 506049017
    0x30c0916051806071b2304050415060b0a03110307050d020901090509090307031e0221070f1101080703110a0309050c0d030e0a240516050d030b0a0915032a0303 70
    0x30308009090f03604014030303000c28001044c128a1506e041d00100380e519440c052580d941c00a401e100d0b204c2c607040f1044e2580802007111580350301d10610070b07900c44010140803c0c1800300e4010700c08a04000c80f4421400b40d0385603400c1210440600e80a580025101030400005010105032503607180f10710b90081011900442da40c030a14038014040c0c07150690300f440404c0585000e1003000340c020541034040351040200205143c11240c85400c0e60040c1c02015040340d001000203020408402415030b2900f000341c980013000da80d9101e044042c1e071040c91600c05884424403442c90340b00d00236040101c000e44203406841c800c2800b0710101ea01c1d420209400c0d00020011070340ba580030b060541c0054090720805d010700d925880d0310011400f2540101500d1410002c000404201a01300414280d10007030340710059a0f03210500d588014013505d02c0c04101c9201e10f1050400158102c1c03944142e001150048403881300461854940903050000d040c0911400040040d01c2080d0101c11101e00000d10300c00d440350b80c1 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 506051501 1250 506050251 506050283
    0x91b090614030604060507170406051e040f0809040207140606040507080c07020d03091706063c011806050c100203010617040212030a020606030c091605180607 70
    0xd460541d800901500708001c040d5000342c60103e03032242e109400ca82d0105032616044d600b1101301c5a0f080610140c0380d640303010301c020880c3c940c00c901e024054840200402d40804410418455000d5a004010b89510301e030100000c0e0901c00541303452000140014140032940d102c41d0401000c00340d0b40d00d0f250f0481d00c200007052500c0d2141076004422460016020700d4100d64204403441f401d44080d01c10020701010400b094030800f48000500400441c0207030710a102d1b0601079035000240c3c1c0e041c0c450002020302c80c03180084a90780095928100490709491800035491606020006101a04100185c10300859004500508000400701c070780d19241d9820035001d0050616003030080000d0101d0041004005c0d840c1e10001000b548501d89020b0716003a1154400901e400741c8042c0400b1480c00049000d060340c5030007007049481000140d0a61307001200e45000c005c1d41e200104c134998800b8904400c0b585005103c0c9001d020300b9481c0d1106105045500f1000680d590090341080b6000d800c4081180 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 506052751 1250 506051501 506051519
    0x50d0c080609010203190504080721030605010f120b0f0604030b01060f17010e1302040606021608030406050f0c070f141314150303040306060e1e0c030a020d091b 71
    0x281c0e100d101c030b400131811400d20140381c0c410026640740c01d155190b11103020400b0f00440004882800da404091012540103800d0380704804907688548a02081c80c0c0a00054654040e1450300c2c10310469682d034030480b128105542008044903850b554000c280780740e4450160301c60b240208051402542c800c51190b241a80c020b1044886152907410808100380100503507560030b0900b41920310110fa6092641d44200c00900c0054010300c001c2e40c00b500701003000543c15004207000c1003805004d02072096903a2255600c0781d40e4811031040350f000130700401c210513820f843e1070040c3c4005021031040e04c01940d640c035034800b02480980c00608645441c0c001c542e4480ca082000c00290b444040350910a40b03e07e65005170312290300a20101a440c0821000c214955003802140d000e1580130b802007002585940410101d020304854620619101c034980e0203503810003602c0b40d031007003a1040089145030f641e031009c4000381d00410900e00c41c0e41d071165010310003d848100035284e550603a10360044220700d00600c0b4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 506054001 1250 506052751 506052763
    0x140c160602122502040614030c010302071a19050103110112091502130302030709021e0304110f210a150b0303041208070804080109020f040507020a0318050d0c08 71
    0x10010755100701c0a01200b18211400d80f0581d1040b080c07495420401d110144154209091000303601c5840d200002c0743d420b000600d94401d1800c15000c940c0c580f000344005400f244205003001c0c101d0b50f0300308618062a0500140d06903c03040c0d14102413542c9008400d284142d030307002c1c2c00890701500d540f0806a05035a02402070503c0b210100000d0089403d82d07160003c500e6041011060b5094000500344001840103240000640d17010707045546c010382d5804e180c0e00a40061009582540c0362021039040741e4150400c1da030080f40c00a00d40400032240200300081d0111140500d0341140b00c1c0c091210b0351035404000440c141c81c0a20180100d1245454240c0d8041c0c1e01d66510080c3c649010000364182d24008103a5040c0e074404414107801103000d060005041c015420020180c44000601290f003801c1900014429403007652610f0320312000f4000c100a40c1e10490302440142d001d0003200e00401d00c90250040803014140614012588038804146440a5184241c4802d0014401000548020054 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 506055251 1250 506054001 506054009
    0x100509060f06221d1f020f04090f150314060610090506091201020403150b06040302090c090a0915180b030606010f110601030f0b090a050319140c16 65
    0x20003015180000000c0e01503452140344590240006103c21502421940b0140104035100c2e0b442983d8607a112025548019070020b04440b98100e01811400074241c2c002d4803903400d801d4521780d0604d400d04221800410a541050070300319162000c801c9150ac4420203600554010304034950554078101c01c4c14907160020306614010150300d400990f05a81c014099002c2ea4004c440c1c45a0320303480f0500160b5644001c0001c900694400140001045004a0344204024a08c1c40034010340420f0402c220850090340f10194100c080900020200365120009000b9514010950084540c442080344125503220040c44240000e450003407200c021411142d41d0f007451500c4080c07199607044004207460703030809030070395060240810200342c0503030056030344042104070001291030b10340e540e0502d40081406003109a5122204c2008035a42c02008540900701c0e0360030000440c0703070008000305046440320b100303103840400c40c5281c510140340c9110401880195104001001038030520301c1c0f00e040700300e003c2d40 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 506056501 1250 506055251 506055271
    0x607080601051602180a0e07080a0503090105031905040c050f06090d290a0c030e03030702060103030e0301090204110d06050d1104051512161e0e040f0510050906 71
    0x40190580e071003000c550502801c0c00c3c5211082010b032010840050205110081c4400344104101065001e540b14140c0e40804508491095580700304958844524081c042c005400c04c010107420765003ea001150030051407124056512a00030032030048940580f42292151000c276003c2143c0d1070a800c20140420045031214680703022080000c000c1e00141c48014030740e40f107120950900100010603104d486a031421141e60501c0c1078000c4070f00034212480d43c0c80c0441d1900d042d00380b0404001003640d1207001d00c0d40087c4016400c5480035103410b42c02c40344240c1c0c95901c455490340140c03503500440f009610032407000d54844100300f043c0303400c3d144180c21190140c50450403100110781c11a501081e0320a0645000645440b000c0752907044801503d64503400200c41041c46402c003d0000e070355211014002c0341c4030210b9841d02030352030a00c1e0011200c581c0e441031807401804a8489150200c0c0c02070721a10490542d0611a915075003400c1071441740d0800207030349500b04444660144603880d80501c40e05 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 506057751 1250 506056501 506056517
    0x60d02130507080709050a1203110613021f08060409140106060507110603040834050a060c09050a050103180c060504091b051603031d01020408070906080a020d081c0e0607 75
    0x440441d03a03040d4a81f103202155514604a041858010449030a9125150084e10b030703288cc001c1c0310100701000101080b40120800c3c500a00529030f00c410100c40120141e903001c070203072030714410440030700390000b010350f490241f007089400d507114248122002409270b501c07802c0e01c0da05281000340707103c90050b60150242e42c0c10020000042d034690304130340d411442c2c03405201c6548084070750614034480800d298002014001c40c6001402000251811458406c0509020a00f403c1408039000b580c24410150040380c20707041804203601a4110a10b0044098202e0143d0341d1551600300002c1308036880b04002c00c1000505000d80d56242c081c0100565003040300300e40440d101c0c1d030000d1461141000d44900d11070b08030140003c142c400d421000d444d43c26003a03c900380d85007000220b030007980729204a441510a8200009040065018500807510044090300340006960280940305403c9401110b01d0401003004030080f0954403214000844181030016002e0010b8400501e060405096031007808104 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 506059001 1250 506057751 506057759
    0x10b030f0c100504080d03020c100b0907050903030f12010501020706090501090b160b04051e010911060a02070b28030513080a0908100209040c08090a0b060d02130507080709 76
    0x3801d5111680e007568210320071001d10300100d4203806640c1040c0303040d010f00300b4179407207044d03140c0c0182580344107401c10348405e1100100103104555036840d43d40e403c20101000aa086070013000030b040d800d60068281e91610000220315810342c0d001c1c401c081c02c0880c0c202e0040c4501d503810000d5074041c00c002e050800007103041000181020b5141d1042c655020300c001201820104000c034907182050b404403036000513042c02e1030142d45590303820000402003032012410041300e000501a040d942600981c0302c0c0c80c4040341c6070502089a000141c0c4a0035845485400a0b00701e0f8084010f203001d030049004d00103150003560a0700d40e50380582400e0810142040706014038030030b00c00b06502c03c055200d1842a51078a1124003910a80764549c8146060b0040403401441542c10380c00070500b8100492301000311104102090f070314114103654003615640600402c0c400654003071515034010000030f0104403e800c080d8000b802903038104030301c0348416468606000d801600041c10310741004090404200ca6814 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 506060251 1250 506059001 506059003
    0x206010812030709030f2301180b06030703020a0f0303030c051c0b010201061d0a0c0f0203070609061b0c030e030303130f06110310060212090616050708010e070602010b030f 76
    0x42000310481c00d5000004152100d002d00c100400850303000c4d145011400003800c0007149074007200c030b0a5a1082c146d0b00b170040464818070540c003d80540c49080c0105a51503266160489802000d00747c140c483d80c040400541e130352200b5203000f41002044031386c9032802c601e0020103503880c2c0d002d400c05100003805880075a112010240b04a0000f14000064030300c00900100d001d40203a9001076110303000805d03075145030140703d84424420b100080f4280a445c22241003192202d140c062107c2c01a0024843d450004042c1d8024188a034084e4402055080000441c40345001800c121600451500701c908000c154000201ea244500100d010b1811403404864803002010005030040c105800c0e0f030303560720070800d465102c00f00841c00c6010301a22854010300c01c079020a168050b034809880391103400c420b000060012110761513400b07059a81083c011880400e01000d60b24000c0384d060040c0c40010464880034800c11145d075060000800545103804400390031203603501c10550082d040794540e4002c2d084 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 506061501 1250 506060251 506060263
    0x7030e03130501050304050a080301080c0a080a0308040803040c15120b010230130609051804030c0825050303150307150e01140d0203070801140f0f0d0b0f01140102060108 75
    0x40c0c20300740243c2c5c0366030ba490b02d1410040c000c4402080441c1c0800003140500c000519141d010301d050707038000d014076180d48190f5500c0613401001070002e4075403000200010342c00005150054401c2c00c01c40710700c68450034400c1402c1212121440003039113494084440350454002c00c00482800e00160150f8008030a048220070404074074114002c0c040b207120b80070a56148210f9000c0f5801c034070307600d008580b1040014004045449417a200c0d40110100d0302e214500c11240c01d02856154607040080111543c2c1c20090350820584000000100c43e200c203030400101d405c825256108401542e507030701d48170403065188001d1101d2503010764054401071000c0d42c0d420301040030030b00d800e0401031410000c241c0103c0f0340501d041d240b802d60f0240418402450303c20381d0040e600a0b20562100515603032600640b100c1ca101c0b142109a108070042941d1103142407609043c0303041c038000f82c0840a250740710b0700d441ca07001c3c07420f48190f509c4414020040004200500030100210805d101030091540b520f040e4580d01c074 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 506062751 1250 506061501 506061509
    0x1c0b190b09031014040201090f080304030f15050406060503010e0d020a08280203030a06060f020d0f0525020319030801031e06050c0d1104050a12150e030307030e0313 73
    0x50001051106903500f04440c581100326014240001505074a0743c55204200b91012804036403d014045280e075040c550002c20358080d5402141030901d5521941d0022881c60400d5a103200c0c09100b0000968507400348921039805961301184d0385262009150071151405030109e0390750030a2040e4140702c0e50200303003400c070190031041e12600e504142c00810321a080c13111407079030704d903e2846c2c0d55641190040043c500ca440d00550400c8410341c0c50001341c8608034884079040040e0410402c11050078040e83d020080d801c01450164205000e542240313104400d0320b01c403210502d94800c0c48108500d01080001c0100d01d44151180703c8a00b03503074018000880c180401404412603501c0809548a070075a841c040301c0c0c01403001d100c11b0034100e811025a500c2101161961420a40c03000407003104d000c2120f0850380302800020405140001c0010038032080f02c0304a86001c458602c442c10031540740545102c04064030081c40e0303282000e0b040681110700c0601941d050342c10900c0400a500f505103610001c903 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 506064001 1250 506062751 506062769
    0x30e100e1e07090c020d0f080609070f030e01020412050105092107170d05042303180103090501020d06050a09060b070227010312090506040e0112080c031c0b19 70
    0x2000e05200c980d8180280c41c0c0000c00030358a881d080c1d4400f282d001906d43e80341551921007104411607000100d8200300200c42d001d03000104000410b000d0340c8151524101191246400a1140d400749060350980c1c1c069400218030f450400d5501c02400400e00c1500e401401c90070040c40e65103014006800703c0850000281c1103003c0c003054000c2481510341481036001c000e00c042c1e5607200f030030f030741c504000f848252010740c0d40d2400c25000400401d0601c0b441035905054900441c14a4001061150b00314821a40c05040640711079204000490900181141202c00704001c10f425040005000b10355002c0c2e030044100d541031100800c008501d100485110381e8050b1505030005103140da68401d172120f600e030004e43c11100940000705101e5007081100e2840880c0c2d99403521781e607903181080003d01032401106e2080c070714000100520340c5141074880c01544255500c6040c403801d420940d0454000d1060111856030f0384041100340c204511407079820030b50403514a0001c04008000038000003042c0204508 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 506065251 1250 506064001 506064043
    0x201050a0c05250503070b13140a15031d0a02012012030a1b02071a0d02120f0405010c03020903340f0f060c0818010315120b0c0a1b0602040b0406030e100e 68
    0x1038ac840d0b800c0d190141000c100ca8901501d1241e0004004005110701404d204034441c42030256000c01049503007021b50141c1d5000170143c82d00c21444407545c1031000112151183d10030304c010f1402c8032405544a0307042502c00003001d5048404150b04e41d01d16008501c115088043d048c03000c80b90b00d4070340310761000425400f5034803041800a00c42c024454015200700400c01c080400c5000c0c040c03541c2e2184124800c00003072142045898040d002c0c0d0144001700c41d4150040d03a10600c90391070040f06c14059a80d07401a41c502a005141d001c01e0070b42160704694981e1440d0001889003003d1742001c2030091000341341c083c900443c02d4803859a41c2c0520b121780908034440c0048100140e2082d0400c0d07540704443e54090a603155070b050900450f400c0d90700d0071251203010b40e0020b5026401d0000391400c6160a417a540b40360004240c10302070017074a021007191202c0d42403101007100c03c00b04003c1c001420403910b000030b04d1484004142c2c1340910a04c0c90300c1c0007500340038000085d401c020035003070b02c800444040181 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 506066501 1250 506065251 506065289
    0x111b060603191e200a050d0206090303161a09030a050406030c0c0501060b09041a030d050d1e050f0a0603080406140403050609010b09090a0201050a0c05250503070b13 73
    0x82c405001c46403141c007074a50510503d091200404001440c41e500c03c80403a2a40280410700140c20f040c0e100380ca5024016220040c0907081c008020080d88a005080e240740c00140b10175125441a8054295403002407015840c40d203c4da10103082d074219011100460510000f000020544c4c822801014101512160300340c0210380146c44a641743c40d444002400940d0715054854919000310f040c051040381820255002400311074252400d0b480c0c040d0282c140702080c40c078140c1d541c0c1e00c04000079100596442007150214800308079500054080280495681081c00c00c02600e040c0c040e00e403280c17991030b1010800016030b03d04111003c0741c0290a00c0c8404865041c40c1f118140502d0b032000e040b034041d42040101c0100107502070f68507480101c0700c015513521440c09190340c4004c5504000e01040c400c010100d8400d00900c1003114031489001180c490000d4201500c8101d0030480d807140341c4100780070050115180500801016120110a840c2000a00625201c2c2103803d440303040700c0c403241c0d42c00540d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 506067751 1250 506066501 506066513
    0x603100b010e150c0c060309070e04050a350306031b0d0204150501030c090f030b040f080c0d080a02071a060301110f0a0216050d020121111b06060319 66
    0x84241c14000d03c03001140c000650300d048503500c9445035807124000c001c49248a0720b055402d0324020041d0030000c0494034100082424624030141094a080c4120002c45001030586203e01000c1d6805420100034102400101c045500b02c0404045400c40c0c00d00030081d4945000440d8420102418680301c004485031000c903030101c2c0d80d0f200c06504503040c0403402d00d480303989581800444001f0790307003007002001500c01142c1c504070030f005400c2c1c41c5100c94001c202003420904101e800c43d00403071200c12612825500c603000c0e54403c0c0002d000070b400100c4c4900d851500061542c1c4d10840005080d0301e418807590f00d10780343e60b540031680d407c464005d0020498607103096201c0d28020750080c00d16591b500e600074058182e60081005038005106001038010f5004880441100301c800c06400700300800701319801990020111106030825062091400f40c03041c4160041d1803402c40503031082581c03038041007004d040c00c00f1441d10800c200d0340204140703d030585000480202410b604480403a1100c0245000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 506069001 1250 506067751 506067767
    0x9040b0f04020f04050f060309031c0b100f0921030c05011d151e0c070f0219030201030b04020705070e070504050306041109090606060a030c05070803010906050909060603100b01 78
    0x1464001e8408600c0b8810324a00800510aa0700100c4603021704605910411140e84021901c00d00c1640050080303000d00030545560004a041a010110f0010b818001042c41400020507040024241a5070340e52429003010000002d080c02d0020803210306c461060019080c840c0c1040201048030141d10501071003001e40c808500481a00c0742045c1050103440d5155881a1840c0718201080d00140880c01c0c00d80030300c48044214101101c445d000e43c0d142d542c8001a034128901c03c1d40c5000600c00704c00d006945682801c0e8007160b01c1e034091311202e8118000101140c22225449010f40d00c10400c0c9004100000740e848121650619246042d640b1a1802c995038001d40d80480c1e0140b088070240030402184842c004807200782522102100c3d075900b203a540d5240000d40300c8982002d4104000700310b0368840e03001003400c0000b50170503a02d000d000742d807181a5640240d1240d500c403962440c05000302e14000409513040b103595001010a41020800281c0340d640c00c0d41c0c0d480c100e503038a494007002a400b842e05 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 506070251 1250 506069001 506069029
    0x318040212010305061608070815060c0601080601061b0c030609240915020a081501230703171603090609021206070e040614092802040302010f0905010509040b 70
    0x40081d055039249452075031104203903240d81c540000700201172109441030800621800ca03e9481199030780b201e12000781a074400008058001c04100140030340760710108a402d0080c01660028480340d0724010b4000c040c00a4030007440b0840f06603010000119505a40300c4040c5d075003100c0009094162854032070100704801d0269110303903c005088030341016041c0d00080c220743c09070b00150300804800301c00204134030078800340781e0100e410440840c0c0c5006022032200e00c030080c18140706074680c803002d901c09902c44962a002014060005841003003580c0440004c0300362020303024105890a05000050700001d00029400815968102840c24410a6000503200940151130084140c44101403203407900320481e06100030070b540d00059031460030280301d071200302c54512151003d200c5644e420404400c0c001740440005074100d0401958200e149482c1c45480c0b2800080140d03510318510024040c3c203050341e840c0e0240070800e1410800390344c0013401c45202e6501140d0004a00d040b0320000b406500c5c0e0900 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 506071501 1250 506070251 506070277
    0x310b0903100209030120040f0617181f1b03020c0d1b0b041a0f060315130c0605120a020a1b050a29090c010507140a170406080603070803180402 63
    0x71000300141d5080c0d00030008e40e140380b601030f07000070384500c0c0c1503620a000b8510000058030480c00100d28107541000c000303d8006a009039035003009480e040c00445815084c640441e01e90301e0306180015001d445400c0040c2089003000d50078035502c410002e8071807400d41401018429000d01c0c040e1103201c00c1507005c0480380c1c040404001e60030141841d106000064824406002d244000b0a03007881d4800340a83c4034203002001003038109800f8030700c142e16200142040c3c00ca58207103030403800001c401c0e402d44005401181c0d54036860703483c0d208481d072885401411500c0f15a20400c0366240050f400384114409050450400c040c2e0705180c90001c2c40c144001001410b07400030350002005260080005040c500c03011204000a0307140c0024880d120302c5201007050104200300b0001000510070b0103001c03030860300c0c602a103c0320407658445100060110100c00c16050380003909000c800e41000d0050740061080d00203200060411415170399138801c2d0300d103c20840c8441442c40380603580b5034046414142c1003030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 506072751 1250 506071501 506071541
    0x2030c060f090f070f0605070c0b04060c020907232214010207090e0703021c080c240405070306050a0e030d0e0d08041e0602310b09031002090301 64
    0x2551403034060304240d801d5076050041c840300c10243d0100003040c005481459500d00e4803103140410a58540d40f080c04111520407020f075001a00d802c00d4809000100403035140c40010301241e20403c910b050b4020403400078021160050402400711203001781ca09809000f60680d0b4003c078070310007035081c034881554541445101c00045441c440d001c50107806590207800b125101615401a04191654001c00a0040d8017a042c100702516044841c004036440d2a00040303404031040c1c0303800103a40e010840c81911750b0f2100321513450004400c81c403403082c402450301c1002d85040c1540c0f129205d01c42e5100103040c094544021030710010555110001e00c000c1c040450350380e9258007203104041c0c103030184012014000d4400e0f0858070b5005081c03c038031966100704070f0b5016094500303607040c003142f804400b0381c4e1580e400e1214104009001c9000d1540000a012601600d04215258201c041098003d0140900140200146518000b03901e901210f0b03881c2c405a25120284042401860001c00c0d10142c20650 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 506074001 1250 506072751 506072761
    0x1e0201051215150c03181c0803071d03060a050604020d24080601150c0510020406050309060601050f0a260412020d0801050a03020d0f02040e03090108060f010203040e0702030c06 78
    0x142d030701104414810b81d4a010b241d01c00410b07070041401410441c18031504200310410204081c102c0d6101084c41c01001c80c0085000c05001120181c0c61110855944070004140020a600042920300b95900c51b03040007005c442d82c00219440d004043d264211450b00c40010640f180e440f5015202ca101c80100200400000c1041c00e03200664035446403408400c8032200450880008210907041c0e801031302d400ba41c144032281e01200c2140540c1d0081e07883e4022501400c005000c1030004100910f015070ba12900c90401c5080e040c10b106c0060175a40c1807060412000e140d0070002da0030341d00c0cac65450b410070b034411078404009505c0c0c8002c01c2440341000420807080008222644101251650311a800c0f5410340919a034140c1c0c1da00400e001c4d00354446580c8400304018a8030f46100c041c044d00c1044250300c202c182d50301180135030351611011415900042002a81942e0002c40607034006011142c2046404450002039101d2140d4010854804850000203144600800c201c079900d20104080310058a04 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 506075251 1250 506074001 506074021
    0x3150806070203070b132102030c070b090f0307030b0117070302040c08090d030506030c0d1104110405040c020105100e100e040507030218060a06181d0615071e02010512 74
    0x30042d021030340c4504200200d86209030281b001403889900c041000d4011445541d11400c0f000942184400c5103c02c20402042c40700074000c1c403006140b101031640e00c4895080801081c100e440d040d070b60082d40030354810800b1550a1120b9411140301091890181009010860030001180c0010b5040b900b00146013044070b621908841c4201a900d003611000e201c52102142540e6068075640d40c076a203c012090518541060703540b10b074034400d00041158140f52008507050b81d01c0d1300d1124000c1240032408200c107007010700a0008604203032008220918214030801604405c90280902c155440e400085060203d8400c0102a017004464414145000d02c0c109a60301d00c3c6000c1203020720110349405800c19100e210241c080e000c010204540d513801c0c050308590604100b5043c0040108441d80042e81e0b00000c071078860340d81c00e0802401c000f0324004080c0070b111040040b1510030804204201030201e000b6401500c1c40f040004808a10040b00e400101c0b40c5000310a108240720004105005101007 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 506076501 1250 506075251 506075257
    0x9030f22080a030e060d09060c0c0201111515061e0301180c1e0306050d05060f0c09010207060806130204090c140322140703120e03120a03150806070203 67
    0x8154000c0420a81c8803149592220b91001c1c0c0140800c1600c403000d0054035140c400307021074080c01d01300028503480780d44030502602c1d403601880d00843d028005440655902001c8901541d583c40f00610140712210f9405900240080c8800c2496084038403007031695442c01c04840e6801640b284841102444c1c041d8a1010f030b10038440c0d8260003400744040c1e481c0001c240103001104845481d0240d501c4602d1704000d01d4540c4a80c86642015603030900440c803a9140c6c5c0e82d5505960007800140034510784a03851104620015141300c02c021803d0081c207400c3e81c0d00013003030020785a05103014003050b00c4000205030a410107a80340848a4004500480d08001580c05482840c0141d03842c0c4840c405d5402241c034880c8000d0307490006c0702250309640a1644c0e441d03000716040a2248006800d0180c5001d0024140700b06a08112407591420f48044100350f48880d0aa007920811400340c440c2c1000900c0050309441900f030b002c801e16455401210454421001c850020071181d81500c6180c07804d03c40003074a9074 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 506077751 1250 506076501 506076547
    0x4080d09080c090106030216170a0305150a1502072102030d1701091a040504080c06010f050a090f09061e0c03021c051f03030801150315090509030f 65
    0x1051100c00051601c0e001542114504019250842590030183c08802943c06020740030002e0710600a0b00c80015060710113428440c49107412240c55002075000182a01c401900b00c0043d001007000c0f400380d583d240c036117100c00c44800e907584030840110321406900b0402c1e55840030403580c0307001d01548207580403512404c4819100300c060f1400c042c001c0d4002e98442000d501030070f00070650540140220720259004260220107202c400011044d0030001605503042190122203400c404218262103c0c005c001640c0548001c062024055040c5000b0440790080c1d031003102001e84d100c2c452003c40104170350280700c205400250a104074041802c040b450340c4c452007419910340d031600c040c400300f80e8403d200743da0580c5507400c80610b1490b1080000d030b02809003e4000d2042c0007003284940084101880c2070b4000314826122004250f00d0304c0c0c001241a4000300e0402e0905003420fa4200340404142800f40c00c0c4c03014000000740399104c80d0121071031801251078034180c00c14006401401400c1e075240402805c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 506079001 1250 506077751 506077757
    0x6060c02010f170c0c0102090607230f06060d0c051c030e040905030d0c05120f0103062915040503100b032506030b0d081c0509010501060912060e0304080d 68
    0x5000c40030216885818a01c0e80950000c00102113040c0c1000200103102d4480500b0002d420100300c1c3c40042d096a00c42107089503040c00c401c0c00c0d00c007a54201d13203603502c410080c00058a00703507001c91a80fa488080040100b4440c0c1e11280702c400410184510045c00750401404272030807501c24032090052a6a8800c003900881c620410f410211301c0c040c001c00714095030150246051a01031003925002c0c00c0f8004101c001d01009000001038948142280c46c8a0640070000c00400d524504090040320a90541c101400c1a07411354040e40440709103003420f88030420740380000515603100815070b00c0c1c082e9070042039140c052401480d407030201035000382c0800030046054600001240b58410848140003100c01c062030682e1908100081c007a0b8080041d203500a042005403d105981d00d1520380d003d19001e030001081c0550607000251103200e09640581c1d40c5000300100d50400300c01801003102480f03464250050303c28030300c041028607008000b44603103a600300d82d140c54450102070384417000e401d801000 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 506080251 1250 506079001 506079017
    0xb0309010b03060903121911040906080307020f10140c0c030f060103020a032a03030809150c09060a1b0302010606171501121404060c090e0405060a05071206060c0201 73
    0x700d2401003a1107004240000056180a03000700c0041032404d4000c00050422128140034403060a160094025125169007c0341d13076a030a150340c40d4101c4495801020090340107118000040c0c4401800003000b0b50111011100901c0b0124100c4d00f074401f14004a14610300480c07003103d0040f000031454000d01c0304500303560101a80075811580d640c0240b00c00707940841304001c10000b268002c0313400754900751412001c41d403030741f43c81e880381f10820041c0c2e2045001030740c18030410042030b60610003400e4240c031020000c0d14500744600541c1c00e41c01144503051043c03000041c0d00e08841c1c007912880075000d2a00d502070b00111090b0078064002e110ba4452000841c501d80d02d8510013041140c4128850b00640e601010104036001c01141c401482c0720300e000c1656541c0900d600d659074040c00c40703441a481176401250b49600000010072101c400ea03c00910504260180000921301040c01940810702e007900064580d40d054044a00c00c00c0409008116031605078041620b0b5442008001c0c014002c3c3c1307510701 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 506081501 1250 506080251 506080271
    0xa1806080325020a12030801140d0f020906030102070b0a150501050c0715050f031005041107050a060216080a0201090201030b0609090f060303040801060e01030203070801060810020f130b030901 85
    0x145910400d101d4098030710788a0401e0640032140150411020700107420f181e01d485d1a50302445540302480c2c019000702d0b100304010403008104c030081c241c81c000103640407074070500d059803641c400140e010700082c1b08201600000300662425815120000e412010300500c0c1d0400d46a214018112401800400c82e803170503001c19254000e00459207882d002b90018018545002002001d29140794165020007a04007c444624032002015600944003842035030011850441008100c5012414a02180c2000d00242003c150003041500b40d00d0f0304148050b983d01080d031010341441d016140014001c040119000e03144070b90540c0700307040e054401c1e00c003040b902a84000308813180c083c40204541c80b0700448005454001c80304d5000350400c4001d001c0301d0030035071286901400d41d055904092034030031500e0010001d510b800c004040042c03811030000c006040c207000f820383c0c80e070990b030241004d00350b000950003112900741000c40d041000e0002030f1a51458951000388100e9005440e82d9441e036007000c02c924 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 506082751 1250 506081501 506081503
    0x60303210513111816031a13020309070f08030c06010e2404110c15010b0f0922151e14040e0c040509030309060108011104060c08090a180608 62
    0x180a0048489040d4000c1e501c0ea852540441d06034652680120041e0004c0030700074100c00d42107001d2528114110004100098010102ca901d48900c4464203910641480b031070301ca9414209080c0701c402405a52790341ca4414182c680766443d07001d2080314030f01c80c0c0006a54a0088060440a00c0301810b89829036616500344540b40300644a09504001c02c041984d0300b1000c9241d00c1107100c4000d003001c902c8210625102da1250000a0051002c1c1c0215080030003440100c03016030b000d412000689410644400c0d1011018080d013034030a405a1615280e6103c018002b4034100082e0311102000d00540aa1489000064840e4401c10442612042031940b00d007088100d0b900a5400e41c210002000040c9000c100242c010090342c2a042e01503160002065200e500486203c0c4008600031560703410103c0035035107401d005a2140e1480d925100f61031700590030030000c450448d01d55280101d0303800124108110a44280480641e002180c039000280c514481c14050450109460041005503501e00b415 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 506084001 1250 506082751 506082761
    0xb10030809010f021603060c030b06030408030601033c1b0e090c0408011514090f070509130c0e130212041704170c041a0609120c0406030321 62
    0x103040c480c05010581a0394030946082015424510454603891007610000900741c280c0c4d0401e41d00d07641c03100746640743c0b03d8050180b00c5030f00d001660b101d855482c20791036490260101070031031030401d030b04c0c2e0341d4041d251131512011040401d20709070b08540203107201d034106400b052200304448069003091a8203010078000480e01c0039620654544407050401c0c802003240002005020b102d4229060001045000e000d00c07400742070310f482e4110754902c1400c0c01184000091181103c62041c41d00c4010002e250074520f80e200e42254850628a41380c00c40c0e280003032040e500d4440700c1d0480b00d02e440301c0c02c1a419030003d90b03007658039020f5a00220042c43c038000041a031246000c11040715005c003001c240091800c0032050140c1e50800c1c2041e0406032154030200142c0040c2c10031041c1076110305002651442c00c1e20503280d01e40c02506100920910150208030203000d1460030510466114198500000341409182101d5000600c00c0003144d81300e01d406020f01000071890006101c044403981c0c0751502074070070 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 506085251 1250 506084001 506084003
    0xc090906040b090f011a090604110d0b0f0d0f0c1e050d05120a090906050616060504020301060801110c011a030c060703021002161103011b050a03060515070b1003 71
    0x140509075035030740b142004001d026210981078424114030301900320342031060742d4074440500840395400703c40c60104403014002a0186209500e015144000580f90004460400303000304004101c2d00c880500140700021811041c9410616100b030b02000c210040c041101102e00c542d001c3d80d941600c0702c00f00601ca103c000c00890100e600d12600b0b02c40d41c503112104442d81da00c64400c0380e266030007020041041760000080da102041e40080140481c1e0317501c0c000c21014000035a411401c040f200d100400202040020182010307903658080ba05548003900960054031507900244042c80d4002003502c141c0d80030340d200039519403034480070310800c8107002070700080f41078010018001d64008104000c1356503c01d075011003e5124070742d0640c4a03118a80042d1654980341c03030303074060b05103c68200050028403100304240300c0e03403400c00f0fa101d10000c16115000614010302c0c0030790300c407103d10409400070042500004d82c01441423000030f040c030814500070311801e841a0350f40350254489924041ca281c0072400 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 506086501 1250 506085251 506085253
    0xf0b03030a0c1403040905090709090b2809030f0f05130e180f0a021f0827070e04021906081609090f0e010510030209060d03050403230c0909 62
    0x112100c0d0716486440001502800b5524a95030581c01052039495540f0941c00303400400c1d2502c00300704141c00c06001d000c0061000c400180501213440d0796689a017500200501c440708003844c510b81c0d51800b840e501d0008404511000c21080c1c00e14180a4101c042d4900c1c4000010107070f0b05020505c03880b0700150b4071031200c0d40f03240040440c04c005480781c0900b0000e041c040b0b20015081c882080a1080008840d405046006001c50300b80e80e006100040054040b00c4240b0445c21040305d4000e039229003110741c000c0031248461102c10101c840d0100000381d40b44032981071311038030b040402c201254481d80790189108468040b44c942181445d10b9034402c2c20711842c004a101c5100040c4810050300d1120052400c3d8501107054680b50040002103618405217444180d40d100b00340310000c1424801e00c4d8000e00e04600b4040510710350b0f80041e5a0341401005280904515001c10013014090800e41e0013556218603402005524880840e01c043c5c020450b0102600ca5040407481c41d04000c0726947c040c2240d14 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 506087751 1250 506086501 506086507
    0x3020906061e0a03090813060207150e041a040f0b18070206130f06180501060609080304030221070b0711040603032c03070807080c060a0906180e0117010f0b0303 71
    0x10241c56003540020400f401459116400171000504e180020302d903115a40400c00045828003000a00d45016500aa540e08241035910b8900d1904851080540c01c1c3c2150041f400c14844202e0409113001c405225400c18100b43d036600602c4011340065440d0201654190b54070700a134199804101820365040b000b41e04000e01003000200d204425a440d503000b4492480142c42d655500411102c208000c602880e120707c0159042110a0003028004c200034a0180c072600c1c20080159121301c00d03840002e100e100198145c00112a035040d02c644403100e44416146c07181c0c0c2d14000c0720b4030340d882014100c55511b08681011002e25003403140400b03994040e600c420038101d0984038400390540b0490781000182c014501d9203040d540c00c010800280032000040c3c00c00910303100d512031409005200b031b40d20401c1c061084800c030076401031200e8112440b84ca442c04005550068123440d001c82c1d07400409d0328030301640000c034260302c8070050f60350781a840000070411400e00b03521110031a0901038016525810070 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 506089001 1250 506087751 506087797
    0x7200a0807171c0c170c030a050301031a01033504120320060f04062c0d0c020d030f090e1314030a09031101090b21090715120f090501060302090606 65
    0x2031500c60f00c0c05c850000d800c0c40d060b100d4542c0d0745107810a0303a40000240c0000300500400c4061607140100000341c0c1e0f118521035055581d005c81c40b100b900c4040007980441c1c9407130503d0703881da908411204921150500d6445845070765000c0b068003c0e00c0141d000c0740524011654003034080d6800381c1114200c00c0500391a48400c020802c030560050029940c07251034050100d09030509900001020400f801e000400b0a00c160b6468284030100300d102003802004428500580c40312960030544580c10b161040d50b1441280703007135441e184030742c0190003158208400c004410400740851540103010b815403120a0688144042c2e0303c0c881d102d5900700044400c00d0802c001a100e00c030b01c81e0145814180742e15102e17103078015980e03180c111500584110000c50444401c041d90705a600740c01484d030001030400380342406054800c007a9550002c0c401c1060301c50408680a41c80c0c2d01160f001c1c1c06040041c8010541c500b003007400b07170a0a0005030300c55071a10003c110b01d842c0100440795000f1201003110008100 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 506090251 1250 506089001 506089013
    0x40602030d020a050c0f010b210304210c08031216022505030114060f0a03031e020a0c03030c14010506011d0f04050f18010207200a0807171c0c 63
    0x201102d814240981817000482400c4240030071404019010000118140b502c070801122102200c1e648006562048280241c02404400c40c3d06840103084000940007000481c65020a080e030300250410038481004201c0020110080c21680b1800303031020b03032a40300c1c0d458898075150001c100c0070140c1c0c84504404000481200f1103004d006420402100180c0d41d0804242951040c07004c1820b03100c105010411035250000c05080410016500301e41e40d1800c690700940700921000300c0d03c04240c002000b000302d1a1080080344000d80c4d0192a03003905560300c0c54054002036041c01d007182c0202c4200601071402c1014890700e4444d050503076030b4600101c0c0418a1040d183d0f00c1e510f40542152860300e9202407508c850103064010319021a00ea02c1c2e925201030a64548451804c003101c00341d00402400000c00c40b44502e1640d03010f00704041103402d0808000091110f001c45d8803b141901a4402c00503414620040e40f1000010f0b96090b510340d0103007610342c0c02400e4840300542e40810072120300326000c10301e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 506091501 1250 506090251 506090257
    0x71b0f05010f0309080a020106050310020301050d150924051605090105210903071e150b0d15020a03060605090927030424180e0702030d09050a02090c040602030d02 72
    0x1510300f00025044126224410070f03901c5000510b000d41c2d1150020080740c1000c1001c0880101c03000802c60035075040c070001405500e01c200001e040500341d40b1441c68441100d170f0000b100107500c0751246440410b07a5185c50054811700040b035450900d0300000130200d043c40d0302881800081030355070074030b0a914800150b40781d03089090800da4051500203400c812500c0901c200340100d0400000703688810440c60420041a01d440c1e090400c41c0c0380100c800009044c1001070010070160f080007060740000c00010401c011a80321b4040c050050b10300d04007450b00402d5000740341030002503400f409003688601043e2250302c141140682c01101c564002032006000011140b1900c0f440d011254110020301c00c030510b1034210b43c000340103141c801c040449400415202201c406406400c002c1c0c01c1404514015441c41c2051195503441840240005c002920030b01c100e80c40c003220184c0801c000680707801c1046e5105100201203014140d0140421241c1c030701e50301582e08807a980e500131458005500c1990010390 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 506092751 1250 506091501 506091527
    0x402011209020a0e010e010618091e020a0c020901090e03071b150f0806040501080a0312020f07050a11010e060a110c0a030b06010e0a060927020708071b0f0501 70
    0x41d03031904030400503610802c0c03080c028040010891300341d50410142d005c0550041e809030701403240c240e40e800c20598065800a04450a1190028801c0d039000000041101d4499071800318520015100354040d030440080300c3c05034000d550712183c50b0388901c008000c85200130b00e0400381d036106000003000100c0108141c00b900f00000004c618560b07507000032110b101c2140f00c403803010880d21202d18040b0b0b83c0c4080c030309500910441e030600044d49414000ba445103c1c611020301001141c2c170180b00310b0080c0c1d40449104030075a24500703540d41c401d400c000d07031a030700112070403550310080c4500c892882d03110361103100704048004c1c40c6a143c0f000700081136442110341100b000c0640240005010541d43d000e0000c001140143d0100070b8500c2c1902c0010550042c0c0d0243e01d1141d880701a0900c045648620f5903825241140100200d2002c500b000d281c40640e0040f90b40d0000c0d000080701c00030030000d14054002640700d0440d42c110341400714a200e2800040d80a9018820482d5400304178561081410241c24 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 506094001 1250 506092751 506092787
    0xf1409040f0e0304060c060c17010605390f0d090e091c11010c0206010303140a1202131a0705060f0a1506020c01120912030b031009060b04060b030708040201 69
    0x11009042d00e40f81035070016400200400d040d040c02d0002c0c000700d8012025600c205182c408010000e041c429042caa43c1070050b0010000b0110300d10380a183d59400001c203c030800c0380300035540003069161000320301007100311070164051120310345000c4400042001c039642d441d49072440c034281011745030241104001c191001e24490b03400c1c4451600302500001b040390216980708048190704415150035600500300c12800c540c4140c4c010000719134001500707440100b070b2040e03803561001038a00440d03002d500318454108040c40040c10400d103201d1280080121079207a13a200e01c4030307490b60401c62080e006e10348014002d80c00000000e460034000d040490381c440104140051a01103103140d0155040454000c0300c00f503400030501e48515a08180d03c40301c254140b11043c010300045507181e43e401305120141b4410f040e207070380640b070032944d007071045038039190030038504105104003420490f01900d1340c56a030700d00462601001090307810401c012248610099254864a91140e60045801200085104080c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 506095251 1250 506094001 506094011
    0x2403020c070e070905100503061503090a051903020606030a0c030809060708190207080307031209030912030807030513080a0806061606090b0c090a1701021b030304030f1409040f 78
    0x19140701045054060f1020340e440c00e03038140c00c1c00240140f1020a410a406120042c010010155200501c45085005003403441c1e0f2a070300c8611610b4688911500020f000c0d000b0300d401258080303800e100c00000ca5000790700310356640c1c40d5881859101c038600c003c05004044605028401b0610745802000c1c0440c01501180c600034107501c42130321540100c044122a805071542d690501b540c100b00c20f03070140440c4005586080b00f213070740c050700140c6401d0204c28040c2d110100d4909142c05000ca030002003041c448001c102501c1882e00810701c1100701d602e0008640f420007c55441c50900c41d403020820ba002014515003880c84506548a250003403c096000ba0100009284010704030310f46030803d4411440841c00100a04e2300026240d802070000c0801c100500c42c40d44a030b82c03403e0705a000c481205a224021203601c076149800b80c030802c100a68060301d101c0c40c4102e01c1100000652042d4000d039104500242100400c841403500e2000d6452110003d0200f8805032038103030321106243c02c1d40c07540010 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 506096501 1250 506095251 506095259
    0x302030d0509031209300f0a0c03090f06051b0a0510090b0105090402030a081b01022703061b0a030b030703030201050f090c030601030303021b0a080d062403020c07 72
    0x30036604100c030b03508140d403c013044040562140c0c80c0030315001203054010b0161401000901000d4000310140401040e0b00309211280c0054204111407102001c0c1035070640d83ca91881d00038180754030101040340044c0d21400001001903410048100352900d41c0d6031140f81021150003446121506030b00800c036400b400c0340740e1001070020003104901c41400c0038046150403003420a00565038050307000501418140080000582d004601250a150301989103500e9041c0120880808442c115000c15a0b6100040d909001540d0428181542000510070802c90b10403205140e00c0d0b1005a4040b8240314070480c2e552031020f44c480107000d0601062400140c605901c0d4002450720007682d01c1900581d6603802480034180d1680e0303d42d9840f81d00360000741200c01c1e50f20003003641c402e014400501019400b2884402400c1507404e558400c1c1200c4040321307000704141c00e010707419038046200310b0302c81d5143c094000341c00740c40518030391500c0308150320154100c41032081c01d80c00382d88401381352407890055400c041 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 506097751 1250 506096501 506096527
    0x6060918040606080c010c1203050408041205030304120314150303070c0306020a0f02071518050904120f0c0b13020111101b0c05030d150b040e06031b0d0f030203 71
    0x40c0c0708070b00803000481c40c24a0070304064203110300d070220981004541585580030440d000ca11582580403840c5c000340d941d40f1030601604601664000c2c40220a00311002c0e414494000301650256001344420088a070588001790100c0386114034244030072400d0f1000a1804503180418102800058140d81c03a0590036600da0741141000e030012652207501242c0308032050340c40400801041000d00081810354203000c403490540c001c00c40c901e005c1110080c0d08921640c03d10780c2180c003c0001914850581c10306140130795414144c0c0c540340c0002420300c40340c50829840b4440c003483f0681c102d0640c0c0001d4a44103c4c90760140000003069051115007880744809510400c00744000c51030a40d00016070030501800c000318548101044410000740c4030070400402d00100890b06030201c0c40c500001c02e044140242c640454140e8040c00440d030010030000340c10301c0062002841031200300c0603581583e80740466580030040c031025060300302e101c01440c50001507000491006081c02801140d0914071246655 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 506099001 1250 506097751 506097799
    0x1b01030f0b240c240609010501091a09120c03010b0f0d0602030a09021c0b0c03010e0c03090c060a03020429040b07050304051f030c0305060306070311041206090213090506060609 78
    0xc80355603881310400e5054001e05000c3d81d041202180c0d0250194035100000f010000c583c043c1c600c5800021003010b41e6044804112104044040d004510060001160b0b9881d030b02207030205d40c020750801c40c0b240b02c02d1401030903d143c10306008001481c4c6d0551912414000d40009050710141a62840403a002d82e0340c50a8114140b0a031184009142c1c013145462111200041c0015403130003c2400140610752450500e2a449156011142e4481e690555140d190094919696401ca5000aa06d1601503811b400400695420f60009064040e2040d0b00800a4053740642d031020304040c003060012030149001030141c58024421a402d150f01d0b01c00298507510070080e14600445140d00170811240c00d40280030304007600e0b003000c200320300e0301c940400d80355a001000d407010961fa5201002136102c101056034080e14038068817903a4071986107040303c0180226003003a8410811404207210300e035142c1c0901c0d02e0007a4418040c040c592184414032035540c00c50720316107a01c00c4404c10801007862910b10303c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 506100251 1250 506099001 506099023
    0x50f1303140c18090a020f130f05160903020a0302010e01090807120b09010b0315060301140c0301082b0c0602070f0f060608010c02060103080a020f1b01030f0b240c 72
    0x68400c2d0111503041200d0750b0031000e014030362400008200005524003181904416405540702101c0e4103003200043c20850180a528220600e401d1849058400d950f01580c0b04262003a102c84104100e218180c56084603840b00a42c80f0450103c00c1c8015442003444850526060400840b01030300c56103101d00f01110fa41001150541c04010382007400804016a500a00114020848024000042038036070303210228001281140401152a58070300354022a02207811301e003c00d4490801940030a03450f0700c2882108a036106040c254140007101101004012520b0074030180b5000c0d040c0b9045c2c5030140303049000e41d400e03370b0f0900c0b401d001701d0200300e4017001d0340d4801c42c9400390041d05032130041c1c100c680302d03084200180c1c94020070440141d0000f030450f0550b90400b541a840b074200c40022841e2032003803103c0342214018000800000411111807580c4035801362400d01946007030500d01d0040340c4800d856542d000c2201c500358541c8055045481d6040e0b07012004880c41c00348030900d6140743c0408104 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 506101501 1250 506100251 506100253
    0x170c190303020702010e06070b04111c0c0e0a0e100f0b0405040501021c02030907170a020a0303051306031107080a02010608120d06090b1f270303120c050f130314 71
    0x60584110740e481b448804404000315034650804105840781d82e07011000800c010805c6c440c3c40b1001140ba582d0b1045c00c0d4a0310758031140c0d880182e00c1e516044503000314500c42d6290905040021411290540c003c210302c2214400080020144010068001c1d00303000780c2900c0610791325890319800361981d00409110714000d40c00565142c228030400e01303d1020202440840500c1441400400310740454148102e807800c00300329440e0350102101c18102078031100000c0d032020314040c001003007581000c0a00340d00c480c10b03055a06401d545080907000d840280c4052181d17450100199400034940038003401d213500b010b100005586486100d120f14003950044555444800407032000000e00040c02108050311100d5000e1000740000000b1460716942d091700202c051048134a000c8001340304511541500f40c038074100e610601161000300341a4140b0340001d40004100700b00a005154060040b10003030300d04c907a611464050702034000e40098105151449452140300e000102048900b04076101c4281070300 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 506102751 1250 506101501 506101507
    0x14070906080607020c1c11030a03170708071704080c01050c0c2e230103110a050301050f040222020409150e0f012106090507060806010c170c19030302 66
    0x101d481840c1c140010300c120300310351103a4051800e03134a620f807041c168400614084108501e4625202070492103c000c070725054400c0a29040a0540c440311a2440305100304158145450b101c0b01203c43c8201105c0850200d0900a80c5048200d03143e03104603801130150f00c1c1c070741c140f41300544443d094035401d80b5118a41c0b0408200342c1d03113a031401d000317000103071170086000c04041f150081c194082040322010315805994070809007240301c812100030740300c05001c1d50f034800b03036582c407480c003103814092101805000d02418800420780b03080502c200340c020100000204010b540d0b6600f00032106407020002c1500c2c807600e113a010141c10340e07400508098010802c0100d26092025926000005c1c540d0040401d82d101c01e0907c1000c4040c000640d065440000000300035042c1250b9176140101251030040407140340ca5505003d02c440840c01405448003a03840e50119140d5a004603240070054401130245c6141c2021a040c18000318002c042680c0d1901c1030b500850000300c119a40282046402d4020035000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 506104001 1250 506102751 506102759
    0x4050c0a080a1112070b03010f031b030b0a151a030f0c030c0d02090d15051b0405030c010809010b100513060c0c0e061914040e01020a170414070906 65
    0x300c400001421015008140706142d545856000c0c0591510b02405983d0303404050385100c0003405000d0251111019140c4d40307513560041030f40c1c240c48603c4107507444103c0c0104c4a80314a21404000304803504000c82c0c0c680c4e81c0302e048160006120208081008810145e00040c1202c41400c42110100070800b510f41c507450144001c64a034200240004101e040070420070180e0041d44003907900404200200680310f56a04000c103003038568004000c0c0c01d074066649103031000e04441e08907602c144070399260442605105905c1a020380100d000301c5078960094003212983d940f240700200d901051440000c0740700840c540101d542414440000700005a00140540040b014902c1c124010801460300790401c41c1181c403101d110044c41c7c0035910609a250020901c07540d02c0d203420744011092008040780d01355681203150341d009410b120841c007690400c0007000350200180b090341c0721b2143e2078582100550759a10200c5500b0001001203840070000f41038800340f20020000c02024041c01c4c94009201824 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 506105251 1250 506104001 506104009
    0x3100806010602010c170402010c030c260712140d0f020712030c08010807060503011a120108010f0605060301120b2e050a1712030702070302060708030703150b03010e04060b060304050c 81
    0xf0310406c0c203403810080d0240030060341e004480c11a0b1681500e4400481c140f6031420f4130f1340700019550089a0300c65110841200d4640d980185241072250300000d40c8015020801da03010303d6060081050000c06120003031914a01d41c02000300020102d000510303001e0b003a83e07240c00c11810303122103a000907900c030341d0f015111b40c1101340741b40507110003002400300c0b42c40d1020040152105004500d80b80100a40e110a8400110151010702400760b03070060080d038503040d4840c0242038001007070039003074104800081c0c0b0b4100001168140d40c0000c5000c00320300d090351201900c009025060f0201c1c607030081980506010300008003182125803100c01c0060900e041c0c1009110316854101041b610307619070640140400c000340421407160b030015855240e0f5140c4500713906100e00780d880a0341184001804404104088008511401c403e4404001c4c10076001e2003101001e416004800e1b101c07504000500049080c0e1392a1544030703101d4000032490815440104140d50026a030456540d80070000d6801c441c60 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 506106501 1250 506105251 506105267
    0x11b0c03020a081204150c1a04290a0c02031204080408010b0907021c03110d0501150c020307230d05030703110d170903040f03200402040e0402040203100806010602010c 74
    0x1044100815031011613524802844c400d0788518404105201c002c0a41070b809407140102d0309410901c82c004840c043e4407003404128080b14112141a00f23101c10030386030240c0071740f1180280c03440299450300d5500d12a20a008003140c40c00c50042d84800c0c0903085000800e6115607100718440c986d1b8640b100d1405d04204c1c02e4518820080d441549500200034115a0000f00184521042807040131034841d07124040d0014a980030304035407007407070000b500070804403213800041c100c40d400b00003c40041030000713044640c6280303244000c0d850780161204010135000b00b00030b6904180031030304001991040d680062220300340c03040b0031034803a00046018420305030444800300c10140300c0c6001d070108a01650004240707041d8110049000b000e58004203042d00410401d5401420744e20b0351b00c40c102d917102d047c946d4540c003031011900b0403003204a41c0040076040c00d0083d2000c5408100340030380142c031140d003000003a400040c0b243c4503804c0782000004400004100060082c0610f4000003a25100c07404000c2c00e6107 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 506107751 1250 506106501 506106509
    0x1b03030711120a0e06090f0901150908210f04050a120302100b1507050a020411070b1006021b13110d060501080402091b0c010f06050901060201150501030506011b0c03020a 75
    0x1103014403d80010503080b00182c0d80c003c0080301c0c00c0380e0324028580020400101c00c480c00d40c1106142001040307a400244080403110b04c5034581071305180e51115200ea40d80c0f804a0f498415050300004c42e200c2d00b1150020f0201280e80e500c503681050303156130111321101100c0d4400e40c000740705c810180e01030580502020031030650100741072140301e55220115040303119082c003280d82c4040005802c2c0c2404418040d001885600400602c54885201c811004a421100d02540c10003254004240e101c2030340040d08003119040d80180050000800385044d4102100b440580c0040c07220340c0d1080c40c0c4899101d910f60443c2e88040043c0c4460308440b040c0205c0740380ba0849414400814140000340c3d45240c00789a1104403a51035198841000032800c00f94001d84811658540c00d040512401c0c241c0c60308014140c4000761510b02450b0b03a500e80403070990300254070354072184c2e019200501c000d52203a00300c2d03940900c060402402003854007003045e048800c1c0540a403080c13201c801051003180b4000400318014 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 506109001 1250 506107751 506107783
    0x405040e0607020a1112060a2a0210150312020d080c04232103070308160522050a030b010e100605030f101d090f030c0c061b03030711 59
    0x2850700c510041e60711380c0c00c00805072640148184051641c2e40e8420041c0140150b1b80681c4c40a0030000e0006010f801301d0080542c00107c600600020455181c134540d10304040d03a4010b0600c4200c111742080204040003d21344040c1c0c8220707011000c10710300c410402d0340300120742c01403c40300300100004108810151565101c0402008204444e100540150903d420400e07002210090180001040751140010000c1540c100320504000044044043e024035806078407550b003541c0c5c03040c403c0c5100180119903580400c105104240864204e4000c4141280103980d50415007030700d07031340010000e0130603a00c11a8282401c42c01841020301151501b07400100702603501000e01d04044001d800c0e03020040c121714070500d2010010300502c400255502c014040440240b1015883c00036100388540c0490b0110407910410b500c000b04a41c0c0001281c0c1c1f00c940364030140c00318564107010406c0380d0744421590b0703000404070000c1611f0742c035040c80154003600007500c411325920302c203050850400c0c200d43d80600003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 506110251 1250 506109001 506109013
    0x9050a111e040f06090c1107080303060108010b0304020103090b36030316090306020d0203090606150405010f0203090406120b01151b1e0602130b040f03020105031009110405040e 78
    0x44594015000e801d0410440340441c52180200f0b07039000030001a07101e0060103080c0f1140035002c5401a00300c003003506541c415209442c0e2110030385039680c4810b940482c001400800100516140d84000e160420f105240101c1d22100d1354554044a80c0240d81c0040f031491104d1005680c1d03180c2c1c85a80070503444210200c0e10f104d5110240944a0200810201180c0440c52a02d201c01c0d21840e5104041c60b8851021034450350306002440007504211800c51180c0304100105045141450390075146035240308055140900f031100440e00315010441080640c8024003038036001d6034403401034201404481100c0002240b85040c5242c4105042e8050540300e82c03014500e4100c240d05c050801d052070003202d01785030070a03450b10b070104901786da48410300510049440724804010142d0020600d001c40108554110740e241d9a4406a40c03040e1702c1109150280c00c1c03010030055000301f01447c2c0c000e0115109242d501d6942a41e50b09441c9552000d400c9648006000c0c442880c1500c80c1410301c1281d9030081c10 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 506111501 1250 506110251 506110279
    0xa0c090c02060f0705031305030406050d0b0618100309060f02070201140f04052b030906090b0412020f0a0f030b011a12040f02031c031b020309030d0e1309050a11 71
    0x52800f01c040e20075010003100200044440e01820300e030240c013942c010708580d551a44e8503070080154000b02c50f410500e1b8100300b0054108d191807400c1c0c5440c09030100708a4044609901004000090341032244e050580340c002c4034001c10307014880d1402c034012421015940d00814400141b0000014060005213107050080c1d003108080c401c242c4050398001e440a013034005407108200c41c1350042d00e8641c3c4030040d00095401c10540d001104408940054803409025521802e00300c0e064011401095414500304184002628118589040c0114081c15462040d6103685000516800c1c03900241d443e101b003140100160150485651181c2020306404c9003070200110f0380807050f080c060006400a0b25074141c0605541c2c051080c1e080d0445401e0604141044e807440c0500600418060713030300308a02c0034049012880c008400c40300d20b860000d000c0d04103c0444041030300e103080c9412401d5000101740c202c801c01580180304245c4041c2c0558000c18a4803201d06c4c07c180031721000c4214a0040140c040d02d18 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 506112751 1250 506111501 506111521
    0xf0a3b120409050405070b0a020f0607021c08060f0307080616080f190b040606021f11040e090102070c030803060f0f062505150412110706140c0a0c090c0206 69
    0x3016544200b80c00300381601c441c00d0071440c00a1540010f030040300001181d90a0640025500e0403444025050b00d00c0c503603950740c042e80c46134440d00032001100d01090343c00030090700c0f40070001e5106000030200c07a0143c0c042e001091611405402030005076202009200c1c80d21f0324500c002d50a51030320f02d4081e02914002c00056405038000c5c2c990262040e20121a201c0d440c2260091021501e020f0410050b03d507030361134001d41d07030580842e840c0e864035420983d000181d00309000741c00011144a505603e482d1034000d464280c1000245034031032a5500f88160b0f000a900c1503007500003540503240054403402c000c0100a402c240c41020940301c0d90140d0ae20800c4c84c0c0300e0000b51504180030b4000015511071420541c0c0248414400c02020740c0100d10b0706803050314a0001003802540203191040c01100d00c2d10003035401001c10103502a00d03502c154404c00c1000d218081d400c4022058800c024104240040032a251802da81c1d0201c90290700004140042203d81c416481d0800052004004908000c2092 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 506114001 1250 506112751 506112757
    0xf0a0e031204060902121c05070807020d02060417030406030606050a020d03050c040e0412030b1801150c050d1d03010c0c02060309120301120605100303080f0a3b12 72
    0x2407505004010001800d0051542c032002081e5009071131488140341c401c0da5035480b00500030300039043c951180c480314012485001500c14403903001030300610744111034080205094001c14200d078041800c10000c90b500e12080462a002e0010030019905d40e0f007007400240640d00079401550800c4001d2010300d5060364006000100a6058200011907484130903028100d0320035070700032220740700f085402d120030400d62103906031070390000d80c2e000c0100740c0c000010007180c844a0700c0305112454803100113000c142036202ca40014400241080212024a50b440f6410030010220030400704000040700540040500d0f2030341c101000c220002c1001260455002d007116100200181c0030b007101000107210701008000d40f0705103040c04600541c8a40c1d40700c2e00d203840e144408004030389035400e050219000c45061100141640d5040c1c4905000756103004103495000c50041103039180c0341d00c07401620710785e00e41c004d0340c0344006c0d01030640c84c0c2212070142081a6460448d10790200c00c2d03400604880824a012419 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 506115107 1106 506114001 506114017
    0x120b06100302040e151f020c010e03070b040e192f071101050a0c0204180308010e0112030507050a080f0301052707180b0f030f0a0e03 59
    0x11802c0c0e0190f48101541480c1e00c80c00b08480300300c24110f80a456201a200340c0c12011403d041210b842240c04220015803c0044603d0065901c0200d15100c4801030300101202450318103070300c240b40325610030f54424510400c04101030740700d40c003c4104007084403a000c0c00074103089601021150b104044c541e410084800803090250192030950b146030b038002309002001280d10005594682c000980c02c2c003084485059040107a6403031080c21151902500701c031006401c1407901406000c0306804c00b45a00309560010000d107807151200036901545868a95258261403400700e2509500840c010099030002c595a02109000800f45048540c102e8a181c0312800c08250b141c448140c00c41500c06058192000851040c02050690b1840c136844c6d154444090342c0d00c040110681042404600c07049000003030004010048400c00c3e000205178104000e00302441c0c2d40d044c0c1e07038840e03112 = true := by decide +kernel

theorem cover : BRFrame.Cov 505935251 506115107 := by
  have h0 := BRFrame.cov_init 505935251
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 505935251 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 505935251 ≤ n) (h2 : n < 506115107) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
