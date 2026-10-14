-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3495
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:49:29.659542+00:00
-- url     : https://prove2.me/submissions/20c1b311-392b-4a45-bd43-902455cbf274

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 628417266 ≤ n < 628597122 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 628418516 1250 628417266 628417297
    0x203010e0a0302010509031c0c1803030c0b060f031e1903170106031b0f02010609060909031709032b05090303070e010f0e010806041b030f0e030a0f050c1002 69
    0x700d4100a401c2d100002e104c12815001084007483c40341500c4891015030f40440c200142c0000902d80945020840f50030310b01c2c80b5180f10400000f09030f4031a5021305100e1280d0031504082d19114140a10b007082030042542c15000710915464828038020100345212281c0c00316600c8103440c408000501c440702c0c1058000858103a070b400d01981c0381324012401400c29103810000c049058400003413075030354001e5a00412040c20105c2d82c00a02c04d41000b4060290311408000c0c547c2c0d00e420040052054a400710302003003c455a000b81c00e01000e00803446050f941024501d0104410071007480001c210030841c40b080c0310300314a03000564551180b244030308062802141e6a05241c040a8402c0000c5400d05042208500421107043e40c803666000014100b800d0190403600ca600c000350261000f80000400100b865044412135945504202c50501da943d404005046488090b03a80700e1140f955481e001c070708404501c3d802d45209200030300c100080002600e00503460a500603041e64041c0040000002 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 628419766 1250 628418516 628418533
    0x2030705090c091c0506040f11031c23030115050c030309010506030f0d0918090218150126040f05011b121a040f020c0609061b04180b0d0203010e 64
    0xb4070303140428000c4c06580e40d40070600800d0382c403241d944000810040480031900d050f082040300e134040031034070f41d400103065441440d0b0a80d14034070105001d099280c0083c6251280c0c20040ca080301c180c019000c040580e0f1403841e070900702100d40d482c0034900c488042003001c0000c002c60300000e01c080c501074044000080f600b0f08002d02011b240c00001c0e08540700715007080d5000ba1203650006454400c454660a5044c0d503541080d021070001e00745514080e401000c0c910706c180014401c1c0300105e1080c1700c1c1080e415684400e6800444820300404048100ea91100c0600c1d100c03485854852a441840349a0810035054240c0d07401c0c0c2582c1103c1250380070b00e81c944010a0460f5004000d051140303c030848100080d041894540780c600c00024142806550f9500c16020341421980494243b076a0300f204075181e0b0308142c1390f0035a40c0d0703e0856240e01c920311419104140720005008480c121400104000e42200c0c1140013400204900301529070b100742141c501d031005840038064112001003580180074550b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 628421016 1250 628419766 628419769
    0xc041107060609051f1d0726010306060816030602070c03021302030601080c0901080f19060e0a0608070b040b0f1b0d02060702070515090301060306020412120c0b01030f02030705090c09 81
    0x117425900280350341664200c01841000480314140586103078201c2c19078450380303550740c1c00c1c2c0f00031b68880300a07440740c102c0c601c10308500510024441c0c1200c2c4a0241041800e541d5900b542c1c64010a480703108950b0402ca00c00c10100d04141c01504045000c1c802c02402c0b996039900107990b03079008402d0441c146401008104a83d81c00c045071a07030244441c0e10f114035112086c0d000916005004107040e1441c0c80007004545014519850b1425010700c0e14000c105180d2100808021f944040300d065080900340100481c401c0c00116104080301c420340c1207242441e09040c800ca00b07942000519580c910000d001c104000c030422240d02501006040c00307410180100c003c0281480b800901140a5502c05c441c10480c0f0386074080310700502000c0454003038840c0300e060f0000340540b42d1640044d0465001250110b0803014088103818510b02c26041042c003603c000a080d2400800c021002d04400d207200300401c082100701c03109100d02e87c07006051320f0101b03858100140c460101a103003018004400300d1001c905 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 628422266 1250 628421016 628421041
    0xf0f061d060d02010909050a060302100e03120c0616210b2e030207020d080301060e100305240301090c09021e030108120c100c022b020c04110706060905 67
    0x80802e4410b00c011100030b80020300040550722400000607034600000d41101e030b29610000140da401042c15503442000600207102061782c1d04018400d0151034804d0035000c809004680e24100c0700409008142d41d885100c03070044000118020510a5030b00306001614207070260601e000c0140e600002d14260b9040a00841c194014404001c01c41c0b40708112140c808018403112151405140250351740c00305101284249000a100922650001c00041200d07504091811101078040d16600110001403500f20141d440a480301d6013690100140b02060120742e0f10b80380d49040d07016001007200103882e03680c80341c014041d911005038a81d000c106031205400381e5090105684d020080c1034110b504002c01141c07180452010200d12081c00a40070b1542d0702c00b4030580f0a1030404241c10022000c241402a485214045440d588d484818803d21070340001d103810b14003600c0b460390080001d07107084c2062000901d8006d000011400e41885410009082401407a0281801d1800071a0703a0420a407482070 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 628423516 1250 628422266 628422271
    0x402061b0a0821090703020402180d0501060806090a0803040b15130f0b0102030c0312070306170303090c0405010e0f04080d330302060d1503020d080a0801050316090f0f061d 76
    0x5a8080b40300501c150b00c4e00000c0d442007504e80489005070341d03121103400300040100e034611142e00300107031102100c14000c0641c0310300c0860340600181e510666424014544a100504005140e2a02070001c40c000c55003400600754840303032121084511100d940c0020360810911031104600f00c0e250300b02c001c10b14a241c020005410000e000550070003584403040f6032a4000c0e1030546101c070341c2050010782e4281c0300fa080000140a40404400d02c24280c018040d00e03030f40110340341d00c80d40c46130303044100c040d040034404d41e4102c1c0c85000000f0081d88500403242c01051014105032100d40007448100d1103035485100c3c144904010403082441d0101c5c400c10201c80384800301e0802e80c90740d00704004002580742e1714122102194a19000204101c4a070f4220044014036040a034101015080c24403c1055000041c603503400c054603281e199a0360b80d810580e0b2150640110700080c00100c20400c420b802e25041600109424100440d00e07110b04c5100301c044441d10350101c0c6243c02d00320030b40c1e241015500083c0d80c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 628424766 1250 628423516 628423567
    0x17190e030415030506030a020607030c0506061c0807030c1e03020c06070b1303091203032702010f0c060209090c040501080117030703051c0c08060a0504140402061b0a08 74
    0x1410a0314000010300d2142e429401e000500da01d80c4005560342e5002e00c440040142c0c0240300355142c20030390030f00504c204800c4400300c802e441002c010519618003480c8800596802a40000101c4115a590350307694001c00011001d101c080c216807000a099503042c000c03113440f040c44171381017150715040082c90210400e48150082408108200c0440c281003001c4d580807001c0111860004e4143c90201c0340007400354403500d180c1071080854002c1540c5500300325400800d01c80800d003c3e481e100106004484400c0c3c0c020b0114861140c0d036a51540580d1040801b140210401828910f4420102d03680100848940304190400a414041c3d581c00841e9079002d050b180c0b010340240707540500c442d41d0300e21440e180076042c4a0f000c10542d45240c0302540403102c510400c8002d000c0c8000c9688082d019080944200b071194201c004045041d060074807814080c4039204c41090712580b10f03502440380690007200410300108800d0101880d007101002651a45842100c1103680e41104c0b807500344004015000c140c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 628426016 1250 628424766 628424773
    0x15040b0d05030901030e0a1b0603053d18050406050f100509180d09032001120f06050901080f0d0e010f1d04090c030605100617040317190e 61
    0x902003800042991145a000e017800142407105c40d9810380740180d401c000400c0d04d0156061a1411140d00520504448141c0c80078401070315604640111050034201c0202c4107045060390281407100883c003107030f40c602922048140940c40d040c501f404403c0040c001d00703e454070350040c80200411842165440f140841c003807842410015840c08244195200d40b51150016078045218490303000403811001901c1011124960f1740424054045c0b4840e00c801e80c0c20400c0d102801c1800403c15480c5035401c0416554084485038000b10700300101418003402818503500d01c070204098892482960180035500000d05210300c1b0280c403a482d0000c1e0140b50010032010220344d01c0310303036084041e225200c1051700b04000c03515091724400c0507124070076010703c3d44207040004000c00d11a0110786039060301d0040d10240104d5071449140070360f8540602c04c4800041d6482c075880c00400c0141c22080e009803291415090900c00c0d00b05114003414203503000b00e0740c00003022000f0031b07a840a2141400025410015 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 628427266 1250 628426016 628426039
    0x115030e07142215090c0504050603090a060e060f090102090a141f05070c0801020c03032706071e0905010509041d0a05071706160c1a15040b 62
    0x66031900e40610504100000103000100795680b1403120302043e0b9410b400d03120841d4555070030140039002c0c402501038090051600030075051702034025481c802d0415102c1d03600c1e00d46440309014440d40000c15581c818081c400c10280014280d00030040c18650000c0207048a0511201c100140700002e000c0b02041ea01c1081480000d403100e410b14030441c0c5d03a0b413802900b1141002c000c140a101d4a00b14041060b00b20004502c100d42c024006c0c2601c80e0082c0145041a0b4441c0007180c202c2c41000d0a0b011150300900015001c40c1c1c49090110181c003801c440281e41e10340018000e4a4400c013641c44001144000b0000d4400c038807516800803049502e03107049070100f40381c0000640140701d40c00001e0f01940d12a40341c0c0b03070800310b00c80301280080545811a501c0c00d241d41082600c5440310b00030002100801d4031b194030040030001e005409510010701580325414801d5082c1c442d10108a400c80d90880c0205031580e80444082e00b07280320300d0f280c100e0044621013401c20001242d0260400900c42c0210078803 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 628428516 1250 628427266 628427291
    0x9060b100302070f0206031f081b030307020a0b0f0f0d0b01171006140f07080307021e0607030515030a060b120a0305041206110d0b1005070f122303011503 68
    0x422150700754040d161340ea92078580108c00900c01c2c541c0800510751000040c0d000600f03250005018003c0181103200d0030307604921408141e242d01c00c411001e540650300e840140100b4100310006e0a102021070000e514006845607145056003004044141c0d03036a945840038042d5801011009402d1805e041049040c9041d4170034504814483c020034040040500745a200ca83d4488100d03442104071000642d1a0212464034101c0e691044619500601070150030309c0911311880e000030001d40c3c0b9800500020307030f51a0412001020001c004a2440098210844050710240003400c04039004444c08a00540b542c0c086c010840180d1071800350540c418240000441d030720809490030b4a01c040320b0008422064200b00380074010104407110f4442c0002001c0c80c001e07045601045288405981c1c200d480d1189045c00d40345c40c010480043c0051503048410400a0809600c0444142003400c0a440c95281e0135084500110403901c0703a000100000300601210080c0b166054074101c0c203141c01e10094103102e1 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 628429766 1250 628428516 628428533
    0x11131b11101b11120f07060f020a020a030e03100c051207020d0c060f090b0f0405011104031e030306030506010801020703080c0408030a050a0c020603150111010c09060f0903050109060b10030207 85
    0x41c0d40c040102000600710b0140090240110801e440040c00345c44008403030030418568802001111690b191402c0000710800d14000c0c0d8a803c00f1075005000885450786003600c0e04400030034115854007030880c504104441da48902c140780c00c00c1ea41c0c1d5030303100d201715902d8419100000d040310065510940900001030740c082c080b030306081d500080c0030070550303241003862010342042003004001c44003032030400c081168240d4078603205d07500a00082c080040f060200d01418811400040d0010504400300e00108d100302c2070800c00c4902c00c4c80c2c001041543d0303480300e5003002d0302030300400c09c0c59400003014404e040c1c0c02009103401210a0000720716082c68608400d54a2041009100500c040850400302c1d96000701c0f02e031550940c000d80095a40d240070741e040003400040c0b280d2607001c40d100d03c82890b04a401446403070794082a54031440d0786541401816070380f0003030b01003082081018260005c00021020300903640c0d4144a4400480d070403445070108450b1241c0f841100c0100752050200001040900 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 628431016 1250 628429766 628429811
    0x30906070c0507051c062d05060105040303030209130c2f0d0c05030409020307021027110312121e040b010b03130812101211131b1110 59
    0x1700c581e10001000b00d504202003101d41d60000d89080d180c440e0034a00308800000d00303c05250000e00c1384090314a411122000ca0324103440030384c00100140800c0c00002c0c081e600414824a0040101e408100e41c80310040075903240a00001c000340303241c081c0c080c1e050041c01101c140c4c403c881c0c1c44003480c9007a600e215076980b0041e103862802c0000d40200101444010b01c05c03240923007001c0c00300f9981d0740f9042d90040c1d03071490f16840c40c9032103502c6c0000329400405070205c00c00380c81c101d803070031440c1603000c0d501c5184094a6540e14103515010304010004041810401082c2e001305a03091003000d481d100486c003240c41d244003040900b54003c442004001007088540905407210156665104d0300d840e5100d1161310313803401c0003c01a902c001401840f5954040c8118450200d019000030f90135210b80882d66404d000031002095540c1c0152900014031b441100172280b0b468480d40042c51403149081c0d900714140b101068404108500c15035a04164148107128075107500c00004e020018484070300e0100d00307045 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 628432266 1250 628431016 628431019
    0x2070302120a030e1c08010905061e030319090e060108011505280507050106050f222406090b120a0b0a1e05010305100806040f15050c030906070c050705 67
    0x11548040d43c06940a413040042c150708582021810800c0502001125003002c0081502d980002440078528000c0610842e0301924142c00c0140c5649201d12014030005103c3d4103000900071100443e1468131101d0488165940341860710b0702d05034040703c0640c00175007030604122660005001d44000c640c1512030b21507a40c9416a5111005030001051000c0140c0d40f4812016aa070000d50a641c000090485a030194008001d044c0d6104100918001660703003c90b0050340800070f218a001ca00d0340524481070340f0301c13404074010700342140034540401c1030321000703041d0000c0750028000b0552020a82c0003406c0300c0b21406140640007403881843c031038010f2004480c1a250900300d40380792078555003080140f003009000c00384004030201000c05001c940c001c250003c0c1c41d00000907000042c120080081b0342920700541a25101c685600c1065400480c0548945000c4c40c25469201040d03c140791241004d1a091a141d00789401060b080050103425003040007800c61904000c40c00104604c022513070f0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 628433516 1250 628432266 628432303
    0x180d050d080c0408010603030c0614010503100e07050310090314071e0302030904110a0e0d0218070903050a0605010303121505060904090b0a0b010905011107090209060f03160e0402070302 82
    0x1169420702c4554801c0b604004025420103100000b055046101c82d40381c1803003048203100350310001000841110b402d100303582d815400300c1340c220001c5035075038006560300702e00409aa03c09600c84000c0ba18042c0341d610521003143c1d0707036003c00060607844002111030350344090b0140d10300840d41c0c60380d440c0d0650a031840300c41c1450403407801c000c0500070822a061000054010300401e5620314046005400c485000004900803034002c08180c0340c0140030f00d0b0065402040d06174a11010004e402504500070800b0060041016003c00425401c00c400241c452040d040404d0075030444c5030003045004402c40c00200b00e810501842e90b440e140c0300c4124151001628250346070110030700000c000e8502c07400080c0c01d0308001428403480c8212a0000329100e0310a883c1c80f107a0750380e01c0c001100c20850a581405060b00b00c00f50602ca0080542c009150403840140b0391400c10103e41403062156200380d0304d400070000da00c0c070786480040d00022030524000c0d0440742141414403070f8a000e5110001e0704c1c40c0301d0f440c3d074 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 628434766 1250 628433516 628433521
    0x10b0a0f14091c06090b15031f05100305030d060602150403021005060316090b0906150706151d0603160b041806030803070c060b0409240906050c180d050d08 69
    0x5803c4241d2140107038201070288082c1c400d03810a240700007001c4d01c402600c1091542e080e203e40c10001224001c1c441000760220b0207401040c050001420080d00c000304001703160900001141c020800f9060014612500040350740c5402030291a00c000c03500c06103500600c2008000109801180d0341c001d10925400c0031600380c3e0f4540009051030648042020040301c5050003251000e495813040c40d08880a68803104d043e2a444100000c80460001c40c2000540c200407040006e841038200c41908049143c140c0d00e444d40f14107007607294101580100303517580300f40000c1044174941044840912074441125080d954140814072849110b54000c2040e01802084c50305500c8589074080c000640e007054031161603080100004290b050781d900296003181c00c1c005404400c0c0740a10400242c2a032142801e1200701c1107210306414910100410341070540d44420765808a6490b008880c840c0d0108402656030b400005600c0003544030b81d414150013281094110400504c0002e0034070522407460a02c0d13400d82d0f = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 628436016 1250 628434766 628434799
    0x506090c0d1b030603021c0819090302060f070b13083708060306010608150f19080606280506031b0c030406090801140a0c0c020306010b0a0f1409 64
    0x1000301445070b9001d840480c0e8200c4886a2603481281901e1085910044150301c0b4055001c5141e408a0080c00c2c02c8001c0202401c0d0b000e402c11072903d0411241048074450b0f070749400250441e0000c40e0095060840010b451003044425501194000c0381c0e00f20240e042205516645c6180c09001c036000307440002d859046082c0c00b10304022000c03400c10082003108000030721400400c0800240c440a0080c4039000010030654092000184506814400c182528507018100010480070b48031060b04005540c2401d000f00c072141c58194043c08000c40201064140309e024803030810f81d110981c0426090186c00000354030a28101103003110070071a1005e450b9241c200d40f0034408503011026580a03d400144403a00c150044054421180c581c0c60303030300703000d80c0d61523200e426110344121000314000d0720030028107240955403000b06110254500084220140e07404070345819402e0300300000f5031001240c02006103500020036103200d0083d10b030940e03d007403080080d1000c6020b01541315204400707519018840 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 628437266 1250 628436016 628436021
    0x50411061b0307050d030b0109060203090d0314191b0f02090615040806070f0e1c060e0d0201020c0c010e01020601060e060d05180d2115170d020106090506090c0d 71
    0x201261009480e0388905a1a289980f2030800705c241000c282080100341807503029055180c102d414607000b451920b080e0004110300160b00242c21814040c580000028103110200a018014000c1c502c00300100030b87ca40140c902c4000b000c6040862050303000e1030000551a10f000c0b854182e043d900070082e0303100d00d0001400d4155905d03040605140206001a50103000a5510b001d0350054a584048525140080341d0700e9600041c03031074000440403880384004841c241e600319054080c410005407000160002e5080000c1c8a05003001030307401240d0801c0105c0140030f40e9803880703424200451600358900002c1c3d103684051083d802405000445141d07580c403084201c3d4404400300e00d0411440c80e0a2071170303692403002c180d03502480e07109100901c00818010452415503400355003080b00410b114503901ca0251214004e03c03041c121107000c0c00100d9408240f4048041c4c3d07800c10103411244800a0000c0c00c5501c2640300b64030043c2800c05102c81625454203494020303080440b46561407240018206c003 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 628438516 1250 628437266 628437307
    0x90c17150d15111b06040201090311150a03021c090203120d090c030b191401140315090304051c030e090702010b09100f06021501060c0215070f0b0a05041106 69
    0x42c450801d201c80c1c1401d80e4810080904e441c2410303210210044c2440240e585440c2124000c2c08148091000c0c000300301c04011050708008000d00e14629071040d020380e11a04d8102e0910f96000c641c001c43c00c01e844544d0310700ea10030180c040003c104515200c6400003950b81c18100b025000c00c1c03070002580303661100260000188503400000740b901c0103a8a18055050717000484015030444040380900308100c0042c001c0c010440e0a400640d082c40e4200003495400c241440a8654188104c0d481d41602e010304501c514480c04071f05001d152030794a00000c3c0081150012031501c0140044001d0f680002e4008004654086050701e04144668400c48240d005050300e0111079440395400d41049440340300d000c0360400f40c030800710b84000019540d100c1030760f03900c120460060740480c5040041c0010b80c0f1815041050600003803240c0d6407400c1e99039001d0106d9009400c10f0b60040681100e00c024090929450390b04522040070800003071500fa154120040c60171011130b88680c00000d40c48044004c161100b00 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 628439766 1250 628438516 628438553
    0xa0b0f0703120b0a031202150f01050a05011e030507030e1506150403020d0f03030204170105041e0b07081f0603050405010b0a0605030c0d1104090c17150d 68
    0x15510004444440600d41003018101c0004600c003000300210712440c016001805030141120f02d00ca41150b652800c0c20146491040443c461000310b468007000420074580507041450f00c4a84950610007845100c5640e9041541400800506144d101034100b07240428614280380003e03180c1c840c100c04401415801059250038401c4408a410405d4030045407409510300701c17110b2030800148000c010407030085200c042e51081e0300d40c02e02004034850000c10340d084c0d8800e180062501e0b454650245a8806405681d849a035450041100b04111402106104400250f07550b50078440c584d260380c2e40e200000c2c40c203010010824081413081c0c9604582511800c211a0346151080d2030b01c00c000c0061000b16025161507081c402050749500304015103500762096941d441d459076803205844100b075401480e4400300d1696501d128030007070503c003020300090b04142c100808c051480703020051503150260a400d55142060050001d01d00c455040001d040c0d0b0151584845100305041c0282c54031a10143c40 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 628441016 1250 628439766 628439789
    0x30c0b060312190e091009020708070f0507060e1509010c0609050105090a1505090a0305070c0e0c190306050a2102060a03051602030a0c020f030a0f061d1c08060a 71
    0x143c452050502c0301e010001e80c0d148010702c0080020814401c5e810b581d0942c65241c1c80d002031007025a40e400a013161070181144928003407680c0d8404907a484241c1e8140c40603002003c05100441c1d00560440c1410012181903840411b0b00300314103050f2052a504505100c2c00404100070402142c022244180d08000208001c1c500b2481c0395485184051080b140d0f42c141c414012840d0035075201d264007130340c6d055008008101e029036044d20f41d5400200180d81c6c05010400000c0d1641d03a401c801c91164100a40700d58403803582c104409109528048081c0603d8200030090040d1b840d0380b5660b5040711103c40b40c01040940b2082501c5107080010000303500000001200d850083e0580c00480c041c1e0032658803400000702440f004c0341c503030184031408000900c0750191031000d440e05c1c02c081103040500405540082c1425500c11314002c0211204885a585500c0100c00107214011081000200c0c0000b4160519440c40311410301d03a00b440b01c1d075080c400360001140c5503407503e182075005040a03d019 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 628442266 1250 628441016 628441027
    0x90e040f05070e0109110c0705101b080a03050603011b05090d0804140307080a0f15060e25020a0f12021c02010204150306180b04020c03131a0403030c0b060312 70
    0x80005089017402400203003420002043c1895004c0000c47c0d000081c0c500290092504150400002c01c1055054908004480c074181d101c00c4206448004450700c0f511520383d4138628404041c040e2500100b196109900d4011554203d94200115002800881c035240d40d94005940000d00c01801c845006031020402080100e101804002c440c07030b11900480455803141d1b0f65900b600c0da201045a4000c090b0340f0a0b00c000300010b030403540a100101c0150a011604540f2481c00c2c8402e10360444003210003464542116450000180170012400e5180c40540006005034681c0401d141944000070403014402c0d0010321603500c00d101004444a0306100b440491602030301c001e0203500940101c00402d00c0c17044201288038000c0c0700e240121b42c14032010311102182c0141d80300040c1402d120300c80d0002e8003007100b281d02a40510007007003800411380110480c40c1c00d021039000d4604040041101c050020002400845d80100541c01d034640c2c0801001c1c0b6564512010900700364045600001c0103101258 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 628443516 1250 628442266 628442279
    0x10e15041101142a0c0d12030b0a030b1f0b040501050406110703050f0f01051f090b03211c0203220c051807020f0a11040b150d02040e01080c01090e040f0507 69
    0xb20308044c024030008480c09405440c0411040541c00c0d940102a001e600180c0c80310305000350810802250002d000c070101035a85d072500c000811007100c81000c542415010b403405240d1b002001d00292881004940c02e1505100001e8101d10482c003416040c82040d6484d091020b100700805005543e000702511108001c101813581e40d012000f00f18405542800c0020f6216200500c0110b440c2d03c10302c0000b000a49842c00d6180240a003840050301400b90b09a40c2680d1a4612004551519214a0039588004101002000140b00b90084105500400030301424004040c8001060032045403c61010f49036850100c03c4401140e10654004101361000f000120076070200506c10310140d001c1d68081070040440340d440c3c18541100520070650b444081282d401c040c1d000c20b010780ca020f030660440d001d007528130501761340000d1122806150005418441c101d1081203035801040e80100034240e201c280c00010748101000d009a40c819451b0400140600c0b034009013400384141c01a058482c0ea1b525141e = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 628444766 1250 628443516 628443577
    0x706020a050318030a082706190f0204080721060e0c04060509040c09020f13031b0b030708220614010302040509120d0b0f060c010e1504110114 63
    0x300c165101000f199510f04a5420200031246a00d855584045003562422410764205045150358608042040c481d420700310020410b25004026034000e01e41c01f1744030b03503407008141d5203804c000580c01401440100110080002c80f18295001840e080d44840041d1400441341400c04002038605414a05030000e45100032402511480054400740030f015141c100380403034000c0682e001000c0340c80882007044012031a6014102014107400080d2030710314501d2490745030300d481c0d820076540e50b8451018001c92400d0f6102c1c440c02032254006032800c514141c440502445001418100004824040c07000e151146001205459602500c1000b500b004155400e42c802000d02040780281d25040105403d0700c000140b900040e003181c00f4032490a0690755070600a0f0030700c2c1011030f07005401e010790750480b0b50300c40340540f00406d0f801c800012040d04501e605440c2c0703418138a036840b02420304024400465921008150088801c2c01c0c45200300d0380301c074500803991081150320f000940344182c402d8090103000 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 628446016 1250 628444766 628444771
    0x3030902061603080f0c03071215060e0909072402030405040c1e1b080915121f0506121308040801090b0a0c0f08090c030102211501050306150706020a0503 68
    0xc3c0d4070f9041a80c0c803508607401c00b080a0390b100c44400400d0000a0840c9d02c074182d01d09843c04296400303e00b840d5210303840c5401c20803580040000c030f0562240f1100d141088004607511117103440040c02194900044542c44080d40402a0604544c0c1e054500404d4000c00803500240009842003042c0b4a10b034800401c001c1d00c0c1000309401142001002c0d83c1540300301e2600e038042c403003800884082d12055588071915440660116001f01d00d0b56520301b1081c45442c06418801d2a2100c103110707a03d048850300798200c655005a4100c2042c041c014400340e21004291401405540c0340900d441c0c540d10160b003540d00c94654001c12070140060007280c11907042d04661517291040d011038417035840340005042550100139001c400078444000941f4101d1280b84255009260307c0252901d81454202280c2682e001c4041e1a51201d841807160248111611245034000e100c800070500e200c1c50345000074003504c80a0002d45c881e4000c650b00d81703c13801c464000c075200030360300800440d90b40244010217040d54204 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 628447266 1250 628446016 628446023
    0x7050601060906030c0908032a030c280b0a0207050c0307090213290322061505030a02100e030709091a0f100e0403030b06030709030c06020f19030309020616 69
    0x41442650b02c90f4000c6c444001500d0300c0b400913505008004c160103000c00305070230170006404006c030000c00003034a003440207214440858019007811503005101803403481032840ca6841294003840818041082540d0203a0002c0c1c4120f000360340c80718075050007032400c550b038103007031b07501d80521a0009902c5009600800030003101c46550425039a55003001601620060506445031881c038408a01e815507031002945d1100e407540700a20281c09902c41011404d00c0741a048070380c01e41d66400050052a0b0529004c010581203005080104883e0301284141159079a040d0038001100003411644c0e80501c120350141c81a40c0702005601d400e4204554140d2000d801c1024142424020aa018202c030f0b02c014403a80080342912540707450700700341e0150400024400c1d41059591500024a0317035030540210b0042030942d80c1c1d00780250540c1032449131300550782d01c8001558084245a0300400700803400b8944140910110b044071500350030b00f03a02070500c150000354030010001e450900104010400c4030440e00 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 628448516 1250 628447266 628447271
    0x1908060a0504060f0515090c18060a0c08070804081501122d03020313060c020a0315020d0612060617070905100504140901060f030b06062208010204052b0213020705060106090603 78
    0x41c0d00c00b4000b030034072427110007481c124601480221141484001046000b03600d15040503911101e4540903015000310a00311148280000c3c1001310040c2000009200c0101410501d01c0c5d51416403151a004072005000f070100222100b5201034024800102e41405601c82e034a6141c02901e240094031703540030322007540c10528114004140180700306843c01880b0fa01502442402d410354031009a00c01008000d028150f400f000fa41400c0540c41c081c007001068486040400d2401a01d000000e489240d00311050103106041d05030b60304400000c5420440f030300c1d00c0001907180c4568071404251002d85c1c001c5504641041c03070b00c0c0c007104034440a907807040600b68000c010403078807640d4101ca15059403101400d0010b240003c18424a0410b00500440b8407a140084c0321201e5880e52180d644240e0b40301108507580820108220b042c118440308000b1040341c80710708004401c2c10b80184940350080b000c0e000308502d0b240e0f40140c1016504846000b600701007110300701e40e900c400c020b05002d501d0050b240002d0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 628449766 1250 628448516 628448521
    0xf06030b0a081b01031a0d030c06150303030f29060c070819021f050a03180606150e0603010b18150304060515030f1f0f05040c03021908060a0504060f051509 69
    0x10350030700819804206c0180b0000e2642c0d12500c0032903044a103058240c1e0100d64400800002c20801d003039100c001d510a4501264200f8130380554821900751081040100e40c944030717103202001c40600451440402149d480d500c52059190700ca103407091a81102c8601e01c00c64000182c0d555281c8415046903200329003005202090501e0180c2402c007880203100400c0c030500c82036508501070380290103005070b181c0e80e2100c840f01540300d113419a035559004442ca040500d0006003010392050032215252002d545a5245526240c0e5031550303807040489000c6100e4400c448075000da40c400002da1082c41c0c6100f01d40d51607050500b400d0000380380642d800008540c141c3d010001b58100401c14400d401040c00c0078040040d80344140c4158046406020211a84d41c5c0302000c80f0004035100711070080d0702801a0050640c11072060040300a416a0b13282900350203884101700c0414001070300760307001c88400800701d8179440314a0b103440541030031450066000d090204100d003d0b005405201001d0070205c481b040182c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 628451016 1250 628449766 628449791
    0x10603080306091021030c12030c02010b0301060501050403060b0604030f05030307080f0c09040510090905030c0105010602010e0a06090f0f0308060f1f08040c08120c0f06010f06030b0a081b0103 85
    0x2004510a802c080c2c04c05c0f50109140e00703c0c3c10502540c06009040c8a5107071241940d4032070044004080500110396200b014203201542440380d50406007058000b04000ca0900c00003900c103000d20f200c000c1c00e068a91070070900585034902a6402150722a1001c40300d1085494400d4898204646101c001640100000c00c440526050b05005003160801c0e507142c1900d0b80240005013000800c0000640800f4000040366a0305210300192140580c0182d52070f429501c1d506402d40d40103078041007c6a05142040110440c00314110101517032100c03000407213a01500e0802007400c031415001e000781c5024038245007455000295140b091900712007030100e24184c40100200260b00000b05024920040c0c41c40064074020a542d46e0050b025001e030b520041c0d40d07200f0582c900074600c00c0c2c4054190011900141c00079041121100600030b0702c000d80310b5503041040d20308600c0910702c0380d0000c050b100d0307011603403a8a640340c2200103440c00f40c05903801c4194054142c1d00d192441001c0030b0010f450010580c910 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 628452266 1250 628451016 628451041
    0x80d0201090b0f0432010605190e100b0d020307080a05010b03010b0a0e0424291b010507020318030a02030c0607080c070e060109090c0f0311040801060308030609 71
    0x5070350106120860f5140c409110307180c450010421924103c9800d41e42040e03000c2c00c1145109055800b60301c030101c10300c421089082d2012070740558000d07414000050f000554640000060f0b03900300c061402e0b03950b1018192106c2c1010356228001d81100054070303402c4603000da0011445100c45844030060b40e00c40d000b41400300c51091080340b8507800103000500a0fa47c02c0401041c0c1444180740644100c0300c0880084c3c100ea0001c004260329010b070369101450000d12581280c0142404d194464119015143c10003812803000101c40c074000001450600010342614118203982c01c80001b0041071a008001030750f41c1d07000d848036440d03100840141624030f180000b01d410f85030341d003d005021780d072090906000440c0c0100d002111402c2c0188080c13850081c041004100610007002201c03001e00b08800050110301041d00600a000e007001511540b86800000480001d50b00c3d150000d0002c0315039180780c039079026503008142d81d5404e002c0000180044007001c2c5001c2c54080304d20302c2c816210281c3c1e80c10b2 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 628453516 1250 628452266 628452281
    0x1404090213080d0c030509220e0601050603090a02040506060d09030f08100612022503030207030806010903051914010f020d0e0f0615030705180a0606090f09050c0408060907080d0201 80
    0x110704d080f03000700003841400035051445018003621841405803070003117982c82c4260304413442c0503a40c8130086910b11040003410f00400041e00e803d417075828000c150548440100b440030303000c4e5444c1d0000c6006520b80303008940070a0072500082007c2049882d006209554138581c4030002000c4c2d50202d0074222052801004030361035521440d5551a280650201a4200040044202079150441c00401e140080c002c080548a41d40059139079446160103054240d000c2c001e070741001581e620610014000151102d422402162a00f42003000c0d0300e0111321784c0080c03220f252055400c00b40190310803c0190081d2000c0600b1030b20a100311900e60521950300c0040e0796020140382e01c1080810384141d500011160100300242c1a0b8408035100c4012403113800e42283c1529802c40780004101d46544580306640242440345013006480380b42c80134248080e009805402c00303caa881000c5051058030008603001800305609036004c43c070301a110140c40300c01920070000c1031f020b80190082c20a03c103109195 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 628454766 1250 628453516 628453543
    0x11030105010507060f06090207050304030c060e0627030102040f0f09020c0601062d08072606040e010216050a140309091302010c15051515030403050a140409021308 72
    0xa04100c116100c1c0da024041c5c241e244219a03940d0400401c0002081c00105847ca01072801195182c0c0395251200c104005036000300100310302e900c1028510383c1c500702201c506078014042d10300011a00201e140145610b10441c640c550310001c0d0020390321000c80000e800720742d111001c06818940d2200c0d85000d0f03207d04a00c074861500013900601540c0d000702e20852801c0d01412184075240301140e00704c03400c0500c000c002c2c0042443d05003049901a4080c18071424000c00201c00c080610f074800b20300710f859201505492240c1c2d2519078007140740d8070035419540a034610240310700c0d602100d0f0a000e41c85421008082d54002424004010f10600000441d016014054142e100560b1149018002d0904218089041226000c0e10700b0201d150b000302610704c0901183c00245508015821a40f4500b01424207030040082c800420200c424a4050320f42c042e41604085a803110601d8044900641c4540c0e50000100007060224007a00b01e940580f4440d0694407054480b80e48820300d65507104051035200 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 628456016 1250 628454766 628454777
    0x80106060c02100305091203010306020415030b010807230711030c0603070c02010e0604171c0e030a2901061206060801080a02040c110f0307051207172104080903011103010501 77
    0xa0f20124400da101c1c50741b01c0e101c041514400c0004031b207454000e074000c1e401070790303c0c680120781030020145210f80d40c03000380414107003000000303400c0001a0070781c403004101005025445a900d1030552160035080410b0f0140c0310341c036a40d20524640602503401c1c0c403031001c1c0a441144450120350400a013124001c2d4116115a0741a0310203600449031402d1154240750810340501001501c400b031082140180c1000002a145205003424030103540d07070008040000f0800000303400066600e010528104640c0c1100000216040f40e03044170280400a5485440380d0b410a000051110360125010a0f01e11031140244803666681c42c2c2118203650070301075041950404541080145402d034040800703250b0358205a50b05c0704213003214906040c0c04099160ac1381d000098501304110f814440c0401c5003503070350040d9003024010f8075000e01c40b51410303260456240300002c041c0c2a80c0c40714255a0b209202081f111044c502d401c2c50444855003240101600070b41c02c0c41c408013032010307020b800c0d28141c0b00e040c0e440 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 628457266 1250 628456016 628456039
    0x324010f050d021311090901091424040b180915060f1309030c02030d050c101a010f0912030c02042a0c1407060525020a140325080106060c02 62
    0x248008188030b104851711300408000c2001d058903086045d600074010120002610a05610219402800203140443c216403483d07071003c030f00651071040241000e040d140010070549003804144000400c020680300003020201b081811030001603c0d2000c081c101e2102d400d5603c5a20a0184450100300c1c2a0f50200342c48451941c030308842c0d400304078060b0080c40d200313400b0b002c0754001c2414103e62000406c001400000c69000280040100d05046200c4c01c50400222000c49131140d07501640c891b0060420001d215161005072107840d0400150075400c0d20301401c03885030b1038083e141c1511342c03074124021401c1810802c810000d007840484480300702003529120400c000e9040b190310031500011100070007500103407800040c00300034080c040c12003034450f5aa2000b11440c410900718040482c1c0d04e6100864840e070b001600c91503070810132a09d095580e0700514401e5030010b41000c8202c00d0720b1f0b05403103803441c0c401d0340713054948003140c01c82e0001002004100e0302c81c40d04880d10400d054000c2e40003126481c4 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 628458516 1250 628457266 628457299
    0x20d020f1f0b120705010e060301051e0d050106120210030507080403260903030906100308070f0311190212011a060702041803050a0f05190e0324010f050d02 69
    0x4004607501e01080001421000300c00020002e6228540f880925485140c00340015600002801c4403e40308942c0e0070b0845d031600c000940602603441c4080d0071000c060320074089a403a0102026207141d80a0001c0c4140c689440000c40800712805050703102d401c5222004c007502d4024415180035004a0342e8120150340c40703031404c2daa82c5251098038014140e54880c941e003520040101c41d401604a9009181d0302c2c102041d01c18502100a0840d094100340c124041001400d0300c0102c075885079120000c80400c03800e504064481c8071584900310340600800310b03800c182d80111018040c80c00c5c401c9400c2c4004045200d01d040c00c0701c081c0100c8440400781c44000e1100791603c01d02520304a84010000700e081a12030140c0352035450999421030106202082905e05140c20a98043d03441c4018038100e81051440c14109510810300310011060210070840b194003034900b4004012500000d903403a00099402e88a0f05140c8d0400348a40f40d00c00001d0700010030b5519001c4e0440389030980007004800d813501c8104 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 628459766 1250 628458516 628458553
    0x1060215150604090204090522060e0304150e100201110a031d160315180f050a0203120d05010b040b1912050109021206090402241b010c020d020f 64
    0x202020011109080100750a586600050014051140002d82c40c0c1d860440c2e210243e880251240c00d8100340482e85140811034406110b203c20381248000c41e14129a4078001d08610170b0750408101013050b03c05001d126038101180808448003500d00418154203403004908841082c11600310600e0b00304040d1104910070b4208010503514803801c00f40301c448404001e0b24141c4c030400c451900102d0280b0030400d200e44031640140c54078100009004844601e149554002184480188035030001c0c11800306001c000c0020040040e8042c0c21a614004688415070b80390304010b00c1c0100369814000045400c01e0305600380d40440300460800d0342400a041526441b5006145040003041040e447d003500666075402514001d0100714801695090fa0491100300b820b07004200c5401011500140300042c0c8600381701d120b580c0c0c184c40044079100c3c1d0b140030001451003032003140e40748800d1100385210301d03441c1036000100d404482c3d000c441c0c00910003c1b09a0325000d62500328540c542003818211212482c00 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 628461016 1250 628459766 628459771
    0x8091b03010608150711030c0a0b190c2c0f1002120d06051e010e12030c0a050601061701030804030b1005030307120807090311040b010c02100806011701060215 70
    0x2000800c4850f16103005510344107008002d90000c4031240240070003590071809043d00d410398003001c2c6150100850100717944a02c400d0004008001100010f413184034204d100041c03100100d9000d1102e0f41d1900d400038100d40110140507400c000800103100409800030380c080541c41e020309007840b148495406c0010102004d0804010b5004900c50702c1e207040840320042ca045500c0c4280080c000d4144824082c0901c1c0210929840310281003003d0690780e04019805040d03041182d20026151038019003600714000e0300c24100751881032100c21030411101048550680d14565140d0560174191415a55440c0302844090984502003000b4004280b05640301a407200440040f85903d42d82ca00200e461940b00329000d44000562000c003501090307100504541088080c60322203c46403e54852880b034075452112a031083d507950030b004a00b40d010b6407410980c1ca400030171645107103092880140010700101c4a0798000703420700a010382044140030642e0305884803580103105ca414404c91000340003d02 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 628462266 1250 628461016 628461019
    0xc12061803020a2003100906060803070b0f060105031b09210a0b15011d0f150705010f0239120d180f0b0c040803030403091508091b 58
    0x1251062105440a404420003039803080d40140104095400c0500030181c88a804000160043d81030740d40365600018040301c822820380000a0140452901800410560307110f40014003021500700240282c00300c1d07c0b4840c20b641c190002c003035500c2400448280c8412988441c0c40300455555017803401d02d40d0040c000c48030010301343d1340410400b003007921034a15601d4101281680f162146504106084207100d411006812601c0a91b07003901001820211102c6941840c0c0d149184030980180d864441102c24414090901c0c01c488080c0314030240c00b40e0040e08203980641c00d08010407604202442250400c0d80015280010915142c11314040d546a042e41e55000100d01340c0c4450500341d0038459203420001021403c0d40d43d00303440c1d4800040d901500208442100f0340b801c018085007425801d09812036000e0104a542e54850078150041e000300d810108031071001104000805030084184810f4581c02001d2100816000d401119907440803107450b03130507070402c003810704010703001485140d1414070 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 628463516 1250 628462266 628462271
    0x5030403081b060103060f1d0304061d1003020c240109020901030e1005010609050a0b0f031008100504060b0402070c050f01020f0102030915070801060801120218160801080a0c1206 79
    0xb120440c0d25102083c2c0082d20a1542c1d0156003100419600c5082e404101440c100001c0c2007040c4082901ca00403842140144005102000403924103031100e00c500c4000200040462160b982d4010002d411250760000b192048849603c942040da00424403031036030300c02440419a0a042c40c03100139402800c2e24506140d1195081040d440050060b505911005000010207600d8660000e2140115910450240c001400c062214110300802c4a90100c04101c0d01030390381c0c94070483c2e4010024158004c060500860a171046055102c2d04018001c50050030305001c20b100810402040b440750440052003109402000c110600301000d09000c20141401951000d00f0312800c003c0c00c0e60710031071306c010305500300200b9003032081210076446402c500d041c50f0070103c41d0305160f03025211b01e006010303078051060101d040501315a240c00c1c1502181504984444540c10200d607003000e0030ba141203071080030810403000442d21000003c0d40400c01c83e0441a8000b50603c0c0c6040d41c51441103500d4140c51554 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 628464766 1250 628463516 628463557
    0x308070303090f150c090e0a15080a030c050c0108070c02090703020d02042711221715150a061407050105010b04081513112d0f06070503040308 63
    0xc01030a0741e095290b001e2448454a616003683c401c0880b12103c45c01000d120702c0e03c8003800b1801980200590103070808400040003d00d00312848090b43c0d10758014200c03417240e440401c00701648050150092032003041181e07034051214005441ca0501107581000203806104501c003d480c0480a040d0803a02600b401841d0802003100101a64026040080c940c40c514291052481c401c0c5001849020041801c000c3e411324801c40c003001d4404c4214203898102c01d8440110b000d5200d03602400208104043c060a0701039840801c0e0302e030036900c0c514080004e5508000f40000110104220f0402c4d80100b0010b02e0342c2c10300400340ca18950a03031611000f8501444070100007002407151038042d080001c036031515185400c1d102403502d06208100544040201d05000c16a4402c08805054640c4400c441c002000440701041001d1004c0da41840c9041c0865070048003c03100e4074000398040c0040c0e0b40e0100021380842400700d1846900d80007405580308000400200e090381c40a080040040001c503100d14 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 628466016 1250 628464766 628464773
    0x31f050303180109050a050a050628030504061d100c0324081e03030c0c0109050a2006030c1801020f1522020a150c020414010303031d030301030807030309 68
    0x54210840300e0021a0301082d040c8140d6801ca90481c1c01010100d607034007130582c00c100c045200c4403651720540f030254001060400300d0400000f400306c401c0c02489800d03200c60285000040280c041542c1c2610b045142100070b510908c450342034022044440b00081089101001d80d0700010070748403283c0002c1698620340034040d03001303500c0051100014209003444050500c503030079040c55112252503209568420f480410301c0004800e9031791109030016002e454549880c456800341107403142c01000c42c01a1161201000356100e1801190801c540c0c881c0c82006441052041601c01600c169001000500c24800d802c3c410702180e0345010010710554851421380c0e070442d450700f440120381c540c0d003400010400c4180301c94050b40c01d00c9030110480c0710741042140c0d000300d00032540c2400307105c14020020342c45a482074060030910842c1d6501800401044403002c4034114009020300040300001d00b01802074288618085860081c1c2040c20003546c510307440c5680d01a03543e4040c3d001202810f4030350700b025012 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 628467266 1250 628466016 628466023
    0x3051b0a050d08010602031602010c02010c1e0302010f0b130905190302010203090d1b0303051f0f1815290301121208090705010c060b031c11010b0105031f0503 70
    0x2414881e200900c0755403000d00d03025001c02c8050700502c0440d40144110906841d06020018580350282422001c491142c001200c1c529000d400140403000105d452001d0b089038aa0414845401b0b64003c10406110108882c2551403c1c08540c0c1d10260304000ca00b5009001d034071000c2c40c9807141003194106009000031030b265000c0500c0c203030301503540070080100750030b02030010a8444500d40707170520104025040b40750348401100d902804069490002481e29003c0d020300094282e10b103861000a80d0740c810791121403101d80c0c005e41030458240c4519456922036030040d078840103034842c10548030905100804ca4988400b84410710bd04403d0a40c004005c08074030b000354060a181508141c030030b20f103400d000140b0345122001408210711102041300508012500ca010344100b460240d03c035402904041003c0c207010541c040c0e06000e080100300c090b8a0707900b40595030f0039098071030300b400c0544188018202da4030510720030302281e41000002c10100703418440a441860704c418103501c050711407010924 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 628468516 1250 628467266 628467283
    0x90503060601090905060a1715011a0d0b040905030c03040515040b031305010b1009080d21110d02160b0a0e07030305280e0301060f050a170f011518021603051b 70
    0x3060741209a11401c40c00100000a01400e42f0303000214196807052703002d50303091041891183e6900d0740d902048480381d42c0c0f900541c0546400030b0849480f1703510380340c0c0305480f13500c50b2144912424094a440030b0a4008100303807011281144541800d66552145d40035801110040489443d580c0b40b207840e407150b42d48003800400d601c050380c9509105081104552070420a00440e8043c00841d80c440186064000d01d46458141c4128001c01c454155500d01c030300c1c84c02603050050141d4004114584404207043c3d0b19124140541001c0d0307040d46680e4404d40480b44a591003025580064400f800407034040e00081450209008080940300043d0380d1403407801030380c015408001080c52501840a14090244002514400e110001c0c007030714003c001008000c9070711401d10400820000003c040f9424083d440840300100001d04c0502d003034075492554040503000c2ca00b03d91100c2000000140320a1082d65580c1180c1d082c5c0b510009201e403401e0390944c00117045818642e15944030105c100409201c07001 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 628469766 1250 628468516 628468559
    0x90102150c0a031d06070f120603050c091008060609040f0b040c03060b04020a2a1208091c05090f030304180219020606010909090c050405070f090503060601090905060a 74
    0x251280c041e610000c00f41c13440f0030103411662000021100d8000740102c1c2140c1c21090b1401e28030460030921780c09403107040c2201076031101140303400f82c008140714002c14070f503911110880d40c1d80440d6507001059010070019029a2929920410010310107003403c00b02030350402c0c040d50b10b840810b54103a1310960521000c944c01c0b0745080d4000e80410800410340501071192100711420740c14580385007001001c40c920300c80c034012080c900c50944544003485d03984c0007800c0c5402c0301903c6200d00b028031014000c020700340c13a2102c592081c4080c1c4000751a4034041010a401c095031140e2400741c0e500c040010002d044040d456242c0030801c00042da801034a07044c4110034524210158950f03542c098100421041410b0801c155001142000b000383c0e0b202c078081060312107050002401c190b090412205046407904165001868401804087e0350441000c402e11241541c51101d529125402c1c5500c60300161074a6001c100d0885003445401130b160071542d4490341c0600345213a500e80c0c41c1c149038481d50b424800d00 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 628471016 1250 628469766 628469791
    0x1203041502091318030909061d06040e0f06150306010e0604050403200c010e0405090d0804150c0903061505101b0605010b09090106020613060c0c020901030b0a06050a080a020609010215 81
    0x903005c00d0b40103c0030900074803005a040200740d28005070300700d48012405444100c41d114070000389a907074696010100c2c41c16080115076032405100d102c80c7d507480c2d0650709100207480221500e21359150000708203042c0d03000d0b80d0752104151104018000a084060021014003125400241d280310240c5c4800c604001c9000c000c0854103000d074005448004602c000c5805181050200028405c0005010202580920b00000941d0707860809000c26030485c0c080e04c018a09100341807100a601c82d05880a40340901c1b01007125022020b141c610304c030b55a110f10b5412003802402a80d140b07000da904d0205d00d1040c940802d8a0400b03544d101d8084507001d80001010000c0440c0520150411140d00d80c0506421300090240d41032072091300e50f103900e103442d0081000d0307220641600e0580c464440075900980c09004542c45503101d01d0454052201207608150061034940c00250342c3c80c0910004c0102c4e21100e0162a034101140c00340604c0e030b0701400c0c1031815403061413003410403c0c1c030b10080b0078071031500000303d0b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 628472266 1250 628471016 628471061
    0x2003030c16170316122304060f02150105060a0c0c0b070507080303010803072010020a11180103061a03071205100209130f0b0414040512030415020913 66
    0x80c1d00000340c4050b40034200d03403050001000303607500021060012a08541c000348039605402044074010a400004c00c5040c84074884402c0c50102800500141c0d641d91300e03100104032003108200d076100701907018000c0c0040f20800400c59418200018014820f05291179050704125031102c405030381c202d5000403240c00c800200102444000d00a040150925001031480d552420140541d82c0c010307410081d1075103103170b10040384010100b9208015000c40c0502803c08100d00c9150203515180340090030f0f6070040b5a42100d400c245400010030f10000380c601203810b816407c5445400041c6116441c07151f40c260030f440c4040c844e41d41041140010320ba58000813918050034030b0800e00f040f20060607140d002d80140426134080c0d48070221540c11424220380040d1000755040030714060100780140c55082407421080d0780b10302c95200c08913441603000f40d003280c18050395424100380e1844100c4015080303045181c00050f02e440d080d00241400c0b07034001c200602101c00c2805050440d50071005540c0300d442c0f0003d8 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 628473516 1250 628472266 628472279
    0x90309030b070c0b0f070302190e0a0801060506120901090b0f07030c05030f0105240d0204030c050618010f02210a030c030b150d18050a02090a092003030c16 69
    0x1c069200b185482c046003840041d903135280d0409800362104111926003400a00b005110358141c2ea00f8021200d4140d441e0004504040d0000d880301550314022911414042041c0f18140103420413100060000380c40c08038500240781002401a06003000c0e5501c8800d660080f0b240c807500c142c041c2812500d05c1201d404c0921000c0d0840c0d64052400c1c0038044248100502a1900039042d41160303016641e0001c1070907811104403282c00a0349180c010030340040703025402d1091540c06041581e12a600c882030b60350321a000c00c0b03064050480c003103020b071f489880070003c2035100700318041e03a1920b1801210f180c0c14521b203203031049048865141c1080007000c140c4203c441c0d4140203208000c0010b040c00c02c038105006000c60580203112514040d890400200380180017800d0740302c0c05064501d844070304010604e5160058481241c1c9005920074400c660100f054800984071b00382c4e40580c092045956400390044410f030041c0a21003e030750601080c014150041000e1105014685810744d07105001800d050 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 628474766 1250 628473516 628473533
    0x6060206062b0b27010b01090b0f0a27030501020d050601030c080621060a09030807180302130207080315120c03120d021308061e090a020f1309030903 66
    0x540b03040d18840d42c403074050040031030400c550800da4000031074011a80d240c909100d100740c030b0a12061420b500c40c06444402c81c50645c4603010100e000d90b900300d0340c150307680341c82d203000d005040c641b034250042000304080301c3d40070f24241c015945008188030b9010008909110010051364429907899400080c0b10440b24810301c40c1ca9440402400c080050309000703400207003110742c000d101d2805041000c03403616400080c0c1130307419020070b845400c840e49403808040750005002c01c02030442c0413841010201d8180ca004d564a03507502140c0700151000e036465502000f00038001d22041caa01e02e64204240004158a03000031442405d001c2c042e1602c3c0e10300d030424455111405841d000c825007000d55030507843d036004205860003500804c1b0441e02c0d02028400440240310340b034010305200c400c040300050b40b6400865558890383c0030070014160300207250b002201015044801d072a03140c000c104000f0041c0b03480c091708440c504029020100d00c98900a01e20f08469840c44207a004c98401c090030001c004446 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 628476016 1250 628474766 628474789
    0x80d1d100f0b06030712150812070c0f120f0c03020d030c20060702040b03070509070f02010c0e1f031e090c1e1a070818090601020a0206161103010606020606 69
    0x9660301c0e45146040301000740b446d074040e610300c10840e4880704900c580b40e9113069894058507128058a11b50840b0301c01515166100500403550030319000400602c451401800000302c900c0900c0d548000f00582d44c41d0329114030302038001c49100600d41400300140c1c0320801d40c2c91800d0b209031202c0b45030240c6810030f00250701c4c00d90842140c3c0e0034048903040b41d80d202d11080e90002d0754103441c0810a419000b0009040460b2604100c0e00621a0302c00c20603070300e074003004194071814142c0003049283c106401c100e03203205503178490581000c00e0045100341c043d0480da010460030070f40e18001440c0e242008040940039480391000080c00c0d01d6507a40000d01404100402c000c040002c0c05000411921500441400542c452124058000d4072010010200310782191680f584c403892080c1c0d02d88244201d1000c0c171030400c4030b03580608030550028059500000710300c6400390f0010021800e0a41081c0c841c040302301030300000ca0301e905202d208010713282c03000d008040c00381299402a201d285403400a210941ca2007 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 628477266 1250 628476016 628476019
    0x101e050402030d0315030b040f021e100807020f0a03050d060803120412173c0f07091d010914010b040b160803040f030807020a080d1d100f0b 62
    0x106000c0c40300590300040c1040e1008a5802c02080820a8060b4100ea00c0c0c0154001f401c000c00940801082010509566221070300c201c80c82c00190b100358401c030b60007902c01c141187c0c0007005049074a050900030000a5800350140c8103c0d072043d48000b111605280f81d2200841c04203e000c180012409168010a030140500c500111300306105410410101e0002520207014070311010490b02c106886103c0c4003403600c05a40c50310550341814064048000030000d0703400c100e80300051040a184000b8450340341c0c440904540740030300d82c03150b080f14041c82d040680035005208143c01c001401b04241c840281e02d9030366091010140d985884502c5080e26480700410111010003801800070ba007251007603906903425200c0c1c0c541c583c65112885030800c600c146001d4408400801040204803122203031508803840b9945440494540200c00d83c0e603500117100080480405210f07501e1083c0b200d911071a0b50100d80d100038440c85c485444100e0900640300c8941c141c4646640c075021001c1881d02032115074000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 628478516 1250 628477266 628477271
    0x60f0207050402070c270c0815010f031d0102180a0f150507020604090209040606050c0d0815120303070e010f2a020a060f0305090d0903021201020c101e 67
    0x14400944414180c01100d11a0b070f4045040800e1010143c0c500c001780c1000c9440c05840d0078010000264003c0d090a0420020b00300400706044521806e5440c0c0110b81c049690851f00f4602c0c0c0055400400c40c281c48410503a8501200c1c01d00118500e02c440d030a050000010b0391032115800014440520144be24042c080c0d0140810040d07a000083c02d0445c0c00e00136010910f8102c910048600b07208420b8047e43c496004a0045142462503000740400541100c0402200d40d903180159100d018081c0001c3c12504032082c802340d1540561005039000c80919095059444e40364002030134640f1010300580076a10100c100f00120750402407c05580c41e09003400c2d68514820f040080c0306250303400050b11840040c40400c51240e030b00d10700315030810740e002b03043c050b690741c07100c4000b8a2041034110000c0000e06203804a0071140300455141c6410b041076690150107402e64003840954021001c84070320315903003044003d01070074042c4030007040111034000100b010100300c95040c400c4901030321880c05035407 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 628479766 1250 628478516 628478537
    0xc140109050d21090509011d090111040b0f1e030709060503091b041d0f010f0b030606040e0f07140a0824070309020a0305010c030e0312070c0c05190602060106 70
    0x40041c42c448001c0380c1025883d80443c24203d00803121540c0b20351140360440700a10002c01c0c511080320300412030802458040f18569900544030342a60301c20050b0307001c250790800c4203101c104159002440c032680035a8050b0701e80042100c0c1e410305c030b403000b19090301e0b0184040103110f5070755400500c180040189140403800d500b000e0254646803002c855041d03803840720b80201c102007600c0384d800c5010300e00c50301d0031000c04044009043e00e840d4035005003a00480c1d4070f41248036180300c502d84207818800d4009001007429a46603403d03c0002d0a86180007500c0f03200701001501925400c0200401070404907584040d403e20384818409214038941212103190008440d001100e9800c03840850020300360f2425a000e138850807001c4e4003c1c0b0383e810010390461127442000c018820150440c411008896070300304042292201680d40b0b81c0284205c0300d031000398201c0428509441103051008050007041c00d9040340c5e40d140001340780f00c0180c11091540950f108402c100254042c018070740101011b003000c034000e4 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 628481016 1250 628479766 628479773
    0xe010302030634031d010c18030507030605100b0f070c1403032b020708120a0c090e060a0b03011202030c040209030c221401150e1804050a0c140109050d 67
    0x4804254050b00640340780ca08a24000b84130350803051908403484424040b595070311030014060320081d04184040703000801d504643c1013801c41040c08880e0088090081c1c1819996044060b00b030260002c0b0781080c80940126801309030500600050f140406000e5945000d80340c00c86290342164840319448074030207069801d50701c000c030403164206201d1141985000174007803007090007000320459112071440484c4a10820603060002c102c44a60b800305002c1950780d200b402c40503540c901440600140e00d601041000c14119059103030022401824003610700e854045401d080d400991290001c0c00358a840081941400e1295001c1008203403010740c0791004120100f40d0383c0d20082051809800c1c2d09001c68403582c038048510340165940407051001002d80b255034201e03204280104d024044d541003140046500444c2d10041401026108400c0002d001c3d6000710701300401802503405001e4086840001920601e00001624611007410701c00b071090400180020002e4000900030601c2c50104800b0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 628482266 1250 628481016 628481071
    0x8071a070c0e0a0e01180b09031912110a0c020f0f1507050f0102040f0602160617130f0303051e04050304030b060105071703040605090316030e04090c0e0103020306 72
    0x42e1000d600380001e0a46403460801c00912100f034500002d54a0001c0041c0311807040185c420005020703a40c5180c1c182c4510350166100e200d11148548403107800e00c0c203c1c540d98000d5105410000c04003800140c1070202d590740450701c4d0b001c800e441e00003404220500d011858511000140c000c4160b03200d01e943c3da0b440021904100150080408403a000319907071007040b00401800b0380725903c210007991202d44d68541c00540c00d24138040c0b24054082ea004000140740480d02c484103e605a0391801d00c6500221040c5251180c01f4100c050003c210500d00000304010022480b08580710b590001401e1510320490810790003905200d1912048403000c0c8030101e100001640d0540e44c000c2c070034589030b441e0000180c03114462154001e05400c40fa01c101d00060000102440c415030041c00c06000c6992004160b54403032042d1131020b207051301d0b140d02e83c50209104848003240c504010b00300180c0d503e465200d00900400036800440c03440c12060042c002c5003000e0000710780044022403610307200c0070303c011640c84 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 628483516 1250 628482266 628482269
    0x504260705040f0b041409010e0a050303130c090e15090109150c090e09010c03051608070c0201091a0309070f050604090b030111030a0b031510060513050a08071a070c 73
    0xb003292107109091018040741d10075544140001c00400021902d8120b0700741501c81141c1c03018455282c400320075800c40001c18902e0f02503034000701840c51503440c1c0d240264450f10300801543c2244000c10041420340c40d51040d24505010900105480c108050881c03040120050250303000d81d041c0701e210400205002580e6280010103c0007191740710904008803103104042d841164101e10110038040c40d02c10640c05a0202c560f9030f6418402d696a04903101100301c0106103010011340e420000503d80f900c5901c402e0091441403410006c01580c41c640701c50070311041d0b1205408c010001051080f400e10420400005080d0183c2c00010145800300040481c003071441090b000303641703c0b15103492665081d4451520645000075054882c2000c0000000920340c1c810194007034802c1c2c83c11504c484a801269a00c5242441010800380307052142c1281c4603008480541c4181d040b0b0500031885698a070804000b0b403901900a104c000c0c5040c884658040e00103941300107414081200c0c50101d040d408a040 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 628484766 1250 628483516 628483519
    0x5160605070b0916030f06060b09060d02161203063b0403020a0606030c140a0b0f0a090f06110706110a02120f060a02030a0e1203040f0f050d0504260705 67
    0x9503a0b0001080c2803282d20704c0740890005003c40c0101c10404005000d6910701d008035420003401c4d440c3e9200c404070b4032801c000d40e0380c4454144070031655129260001c041e652541c0308501981e10782c0f5540e14018140f10b084540110740c0300c800c1403101c81100c01c000e684440421401c00081d40b0005410600e8101070b0700e030300c61a2058200000d0605000300840f4401d03070f601c507008200c481e680341031802280016000310014603040c00910b02644c0741511a000070307120310004542c90302503414610700141e44540350307900070301400c02d01c0010945070001e9940000c2089444a500d40345d500c3e0b051a04080154000900781304446800451036034001810000c225415502582c1340082051b00b5807416540f40b42800d840d00c6440b013089070b4102c4940107103001da4007428052003480d0020040c2511664125603880c954401400020081410000014500381c000d01806981209a403201401c002440030808040740c030008040124011036100c441280096125044007080ca041c221515450f040c8542c5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 628486016 1250 628484766 628484783
    0x6030610110307050f15012304020901111e010e0a050c01260a0605040615080609040609020a0803032a070201030c02010204150306050f0a0608240d0f0516060507 71
    0x2452490401c004503a081600310085070855003070300c0c035600d03034035541020f040d401101b050000060240d1000351206152489548082c9000c0c0c0b02c0082c44020740214849a0400ca829012405102c0c0244040070f92500c0c17426501500020024001d4292003205000c0c1889034050f008802c045034000c102d10b01c4802d000d191844071511110810406101c030451007001b030310100c6051003d01d5000360300003002c0301c1c000c1e80c06010341039403500303041180c8400c400c220011030803110025070140b814a003a543d02c0f511031030000a101c4596004aa9625207a40112510360300c000305202100c13404465600d07a88001c143ea0254958000300340701001d02500a000781819252505626844c1c002c3d011b07076000d403050b448404000001e03500020050401c0f03206150064001f08041c2c0340a090141e01c0c03400b030b25040e84840300c0c3d50700c1d0540240c402440608054501c1c010313544008070142d03507000c0101c40c928001c410305400c038416818400e04090304030744281903002004100700000c42e0000166280b41d03030807201d00c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 628487266 1250 628486016 628486037
    0x50c0114061825020d0f08090712080f040e1f03150504060902030f0d180b07080711040c0c110d030219050f030703031512021311091203041406030610 66
    0xa9016041e41030038405103d01100050b1030805034000744161890b80b00796030b24084058800f6041d255040300340d407005140d8021070800d100310705064540d8044035210306003807444c000b550306940301c0035002504000c41001410382403001040c07540714452021185c609043c01103a10310f60340c1441c001d140001032100743d0303102c3c000a424080c0d00d41c00100d50540140c1561041a0701140c29900c8002c9190040c01141c0c01808204192000b0400f0005503a8004817852070040c0944400c542a040745e54105c42349000d0303a10743c0e03820307807501d004082d8683c040e40c880b5281c00140d880c00302940312190b212035028a8041c800400443e900080486006c0043c000d4400b100640c0d0401d58101030425100c00c40c07622001a000c401c26501d9402582403a44045211412507141d0054413892030b1240300103584598400d1303150b08042c0441d48101101500300755004d03d09090752001c01c260306980aa034040503080407404125510314104009100081114521320714904100068009200c0800728410404044034 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 628488516 1250 628487266 628487281
    0x111b010909060e1621020a0311070c03020603040c030c12030f02010b13050a0f09110307061e050d0f050711010605010905090a09020303071b0f0b0c1b1f050c01140618 73
    0x8900e0400c01c608a03081a94405c000740354029502041c1e0040001e4a00040344924590301016520b000f46e02841d01da8040d03156408000c0c1e5500f0190090711075900441d0000006101307481032100801040c0c0708145a6012403c0c00360040301d20030340d03407410369041551403180e5960b030580c0004201503c0b23034005441d4641100d40b40044c80d000c0b08010f9890328180085080c048089803105405000b1070441e0345854950000700d41d880c121040300c03041c6500b941c0c9052120390050016100ca10004400040c01c0c501c18502030060722000d0318801c010618000303000a02e40c03020b0141c6c8000c0c00080c2030003190a031810010540700c0c0c500401780009903a85800c00d208640c0c083c0226000325800c044151650080b80541400300c09840c03103420f88130400d90000092064103502a04e414440d154040d00c200d440201d81d140034070b40210020742d4045418080b50301b003c4e0304912586403d50f45565455199104012a5403c49140c81e11540e180b000c9941000099905d040943e0700344285111248101d07100c0384c0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 628489766 1250 628488516 628488527
    0xe060601030e1c030603020f1c03030c0c021008060102070b16030513030812091009080a05031b210906041e0f080d0c1e0801060e01111b010909060e16 66
    0x100c14075503d510b504800f00c0c0d6558942c2000003583d0080f240a00744008060030001c0105200e07010012000880d04443c2c04203020740d00401c0080d40d40e00b85480d8046250380040c0400703248a92810200b0490000c1c0456543d0401540b0098030180c90401c0c41c040c00d1262011111840400040412800117404403200744401042c100946c0d00401c4a07466040c1040c5095260340c00300d034450b06a100b0581c0c1c0120b844110300808009980020003540352044040080f115540300401550514500b03407084d4064080d0003004104200b220114a2058085407484000d80134018020700b03840d0380010300b0700c400b03e042a802140c5100144030500500ca24600e0b00707514400d403000001e04840c1022480c1040c000047e040141040f415558007454540c501e0f00088000c401440c0000000310950010700c4168002c44502c110008141003105403520421601d62920364024880114940d406514082950704280100040c0154000034440a81041026031014030700802d519010300c1c0c41404a1685d50289 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 628491016 1250 628489766 628489783
    0x1b060f2710020f072112050c090a0306020306130605090c071416031a0f06041a09100f052e0c12031505041401030b04080c030a02010902010e040e060601030e 69
    0x40d1015500c544a40601446540010100340d41c514621000c5c0140310340c846040d965014800e807a1444a60045500c400081030020100c170401d000c1000690590ba07601282000150710950b0003507900c0c40c060060081c3c02440b140d180c925582050b43c240491340d0f82c940e03000d5000b80c031002025110045428480b401429010074107201c0e02030703000c10000382c042500b100c009481c06450080c00b02e41c5030641c1d40d030740e1a00841d429010360303800c42d000c83e080345420740141c1c1c0343c0711500e48141203801c6030700c000840088042d180c80d1821210b90204006801c000d012600042c8021940d40350b60890152840c0160701200301d080340c2d042c403203c08460819014184280f555504071184420a000704000680140700c00900138240031a6503800290328540717402a40d6080c0c51003601c0403140d03480e50b81d44e0369a01501038801c1b00c140700b00b440120b124150800203400c503224641d001203021415400050040c0c140d10b000e0070b02032401e010681a0010340014141e80100e42860005408045070341b21600f40141c5 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 628492266 1250 628491016 628491043
    0xc0506092b1403030403081012060b010509032a10080c0c3309011811030a1b060e031b010e211b04090b01150e04021b060f27 55
    0xd01103440e02e0384000000d140320381c1c841d40303820409481e5040b41505090061041100030a406002c802c0095001c1d0030180e1401810f05005042c0030a0300d0000341090a11405e508030030580d41038030000b00f4025940440b1800c03042d180c02091100c212002044004010441454070000080c2d5100c42002004a8401901180c0d004c0b5401071050100b01c003000b000141e03e02d19107040d4170100b6900700f0107102d43c050610900254083c1e1080d15551044641031180c94280d060081e402100040ba01a48244201c00502c2e13001885450078808003501008111000d207010782d02c5040c0f24560004c50360001412110700742407480c0220b072604c0001d880d080086c40b52400075600c03038103020244880007508644900f00c140a4100b0183c0d0901031100b16900704002501c0010300a00400030310044c1c0399001009145850030b4100100b4410104050b2307030061003020240e012803081c218149100340b0006400902c4029403101a00740070072004048081005481e441c40c0d1400b020a100000030081c0061180c1c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 628493516 1250 628492266 628492283
    0x506030c190e190e010e06011e09020a0201061706010506070605060f0d05010c0e03060c030a11130b03070e010c0c090e1e010e0c09010f0b09040b03030705010501030c0506092b 77
    0x188120350b11040c0100040380c0000f00d08041c40c1c1101300c00c2c1801000b41d078100c1c5000512060b860180d4007071000480303d200540511030030401242c044036070300041c200d82460360004680b141c60501c0c0ca8110b5400f05c911240160007040040c0300b180c0e9048202d80420b80c0001c4c011a140d01e0b03142c0040c00c1e981c05030500d140c1c0203494079620010488190003113070308502240c80b40410040000e080c55203601c2c00300ca00c102c100342d0400000f034143c0740c558401442000407825007800c01c06103240d007c0c1d203c4040d410402103144c002c42040700c3e0542c80210072508840078a820030910100e40e41c3c0d007500c8201c601881d111075071078a02408490320208030901801d03d8a0244800405984000500803c1540000302032800707103517240142d908007229414100c0d9640042450268500f00790040d1503005000d6590380311b9180c43c1100165a420405403a1440c0508000a02545503140c18917198802d0307802180507403030512100b4100d5440350000c0d00e009401306c0894640d070b0001d000088888181002c0280340b181d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 628494766 1250 628493516 628493521
    0x51203180f0a1217130804091a090903040303050f030a06150503150114090d111c06180b130305090909060a1a06070b182b050306090103020f03150c070c090506030c190e 74
    0x100728580f00300c031100302ba140c686194881020b241d8403441180405004104100100300141c01e144004551102c0600300c0001d00c107441729110040c00c0d10f89010300d000140c000c01441a034041d0100300b45c040d41800d00706104808052504610756000310321000340b0030030f01078070742c1c405120384580880980c050007804000c82e040c4e420416413250364660790030b0340d069291203003d20140b0340b034a03041e04100d90020845002d0b5501c940c0e1200ca000107800d000c40403c14140050440e94a605210a0091091101802682c03034009a01c400312280420781d01807409120484a0103515070078103c2d1004d40d00305401c08015aa590542090601ca141e5031028a200d1182070840000103020242443c541540c409050f144080c9000c9660b0701042d6074541c5c4c0581e00100410062074803407047d441c00c58002d000c0d03421200401122590344041101c4d40d40c1041c00003c0d6200400c52070b407420744040c01d00c000b0100098180305021a43c4c0e8551800400e00504000c0d030f00300854123083c103112004283d0100a0100e62 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 628496016 1250 628494766 628494791
    0x10b0301061503050c0909010312020f0a03030903030b01020a20030f0a24060305060106050d1506020c010917030301060f090305011b08090109051203180f0a121713080409 75
    0x210b456441c403000030310b0000404c9038103a0020894541c5440200321035031590030344d16200642c01c2504c01c0c0f103080d4403070825002310162050040e2856680207403400a488215810003905545050f4900da046401c2a0b100100040d01c060b44640f154000020000385010098042458101102d0820820b0b12a5008180c00c00a407000794000d4028800002c24800e5010940103007900c505010003446a08400014010f0a100c0c50103000d911b1848400410711102ca1500d01c90046000e811070f2005030801240041d003540c02c00c2a070b5001300140641c9400c039000c14000b441d164041030003000c00300600483c01c145070390321038030340d50014580001c020440b10480801001c240701d03242c10441c0c0803d04100c00200342c0d003030600c200000c59800c00d0182c099404c0a42c2481c9050b40020700392900c8407000000184020740800c41c441c607502c0c030103000340b103d0b1085051014111059025040c200510b540d0003113500218034000580011840403910f030030212a2900703404034041c0760070050301507181a20800d091f = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 628497266 1250 628496016 628496039
    0x70b0f03011e0308090f0105040506070f0b070e0f0405040c080f010204140a0602030703030506150403050c0f09070c031b21140a020c090a2003150108011206020c010b030106 76
    0x4a4885150840042100b40300c04003201070144005071a10005020380751060400006c101c0d2002e0052401918241c3c4600000c1c166820503d4140d9640e04a04440310070480d008000d25000041d0342490b508410356400000e00c404100249940565280e50205080240310f1a403180507182501c1a566030300c01325501c45000350003500c1107400000d6682c1402165007011001e5801b9580940c1c00f6500e00a000e86003a0080e0201804e0103070081c40d0a461041c40445400140001c1c0d4402e40c06054000c00040406c4208001c4203400c0d481503442c4810300400c50f80000c841c400043d40350130040d44408030340044d00c1e00c1d9000208040c03c2c4400120840000fa28199081091010725480d05041c1804286800301c490184402000c0568030201c5081c8103131038545801540f00701240c01c0414020100341003100a03440100301c0e4044d0b60004020f002c0f07041045001c144080000b0700e003010256150440c082c040ca08448809403050390f001030301e004084002c1d04003035404400a0b0080c400c2c40e070760b21601401c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 628498516 1250 628497266 628497269
    0x306020307080f070e09151917060109060e011203030f06030f03081b1606150905010611060c031b090a0618060215041b0e0a1a030d02060414070b0f0301 67
    0x40c40d003003100004c00c042e0180041c840c42007070140820b2182d61b03c82160f200d03014003401d05107a0100444502c3c03190440461704071400391441508400505c1c07529844c2c03924004060b0031813841e150a0a8043c010002201d4055044a02105183c03042d40040c0c00d099009101c031014941e112070a090020007803050360464404054400c0e52421240e80ea08940345d101100c0c0d540340303001c5a040070000807521181c08044041414000c4000103002132036804000c842c642641d000c00007654550b00100070f180d80002030040351040d80006005246007a007a807141c18400108a00e1001140707001c102e001c42c0802007910035007007000e0300b201d002648698014201c8000c030640c2c081c16000700d0b1408904907101003140003a03440703210012410354036190745110105004003c14240e13040d40c00c0e8001040d6000101d5140030710b111010004ea5603401043d16915015598540c60082e4000c41110011581c0017501541c0282c1005030701d4040b40b02610581e090289a1344100300c001c5010a00b10f0412065200960 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 628499766 1250 628498516 628498531
    0xa051323030c0307090506060d091401110406080402010311040b0d200c190305130e0405010c08060303030f0405070f0e10060309230115030807050d2c0406030602030708 74
    0x81205405000305541d0710050b820072034060f000900108400d01083d08950381000c0e00800301403d2407550a913503000c949264100352030440c1e0121118804100078851744100b554a1a2640d00c2c1504104000d441000007800003810140d48240c0820766142c0c48054501078450361420b166140c0d00c01c1501e40c0030f414100184100f000d243d15081d848560810f084070b50010340003000c0d115036a0f507d0a04d15568a64020640500108000c4111618803110019000e003100036050905800c141c01d01508641c1020f40b41414081c102007403008a59001007500c0e80551440004800d5035078610380700741010130307560010b081203c040c8404510b001d0030440d00c600c1141e000f415003902654659003141640d003200ea0107041146c03540c00d90000f048a041c114401c0408020010401ca41b910341c010888440d154826a003202010908004100040c0102d40c4c04100a01d805420801201029218002071150402c4041410018406070f6141c0c0d8008000442d008181192646440400541911000c44000 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 628501016 1250 628499766 628499819
    0x803041208341703090c130e15010608090303100e06040f0c050717030115050304050a0f030c03120b0306070f02010e030403030e0a0801020a0c060506040902101805030c0d02060a0513 80
    0x3c0500c00207120070b6034403c02c480802046800c03250300a01802c0a100e03228510140d444003032480c45603504000c14011148089a00c1c10190301d0044010007481000c1c00025054000300144441c0b80c00e000c01c0d910030b680004030b0400154403840d0000d0b0050100c05d4044101604000d400c88c8542c3e00400509000780c080c1d003000c5201e0131100b0301c04440344070900035030042c4203900e102d01818030300c0380000d503a2282c070400854401d00200d446e50240c0d0003500c202200028032101c01403080680c0140010703100c0441e5007007030000600358000603807201d10060070441004100e80d21041d907a8800d400595582e050403098035541c2c2d8807424001c1a5155843c05c00340200084040092106814421900f00900a42d5080f44081d01c5a4400002e488050716440d0b000380c60300d40480259450a0403601030801030313210030080d0b0703d00300340841c09580030390300c45072088d007200600c5038458440780d440304a40c40c0e040303541564400102d10281d4070780c007440c0d9000113004440031b00850099030001d110745040914103404c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 628502266 1250 628501016 628501043
    0x50702010e210a030908120109020405040f09050a02270a0e0d0504031a040f0515040302071a09060a03270c05042c010605220501080304120834 63
    0x45003020b8521103500c5140d001041002100391199015218140c4203038003d5241c00c5c1c01052050503100283c0005030700310386c009810012450148030b5400c85888456040c88640121784602d80c031040845ca01074020100110140303140c1c0700c1c0881030417150b0007070a08610541850107113000240a030040510341d034880c0075407070b4500794003d80944003102e070300c00900007256004003524500d64902420844000d048080c0000001c1c4c001e2114140d80300222103030a895162a05000f031500140d0381c01030416008074212410349080342070031500c140c501a40c00c6945c4100000c0b00302c00a004244c20300b00003050f643c0c803803460104220001042e00d0301514840d010640c4800c2080101c03050055504a10513405408201c19104450b004e02c40c080d804000280305a62a40031426403906403a141003102d09403015010010700d40e12480740544122402141001c1c141908004240c11003040601282c8010550b211400d8544414425554041c450b250420144940c0791805445085003244c001c140c8141 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 628503516 1250 628502266 628502293
    0x9030e28061107050a09231e0408091203120f010b04050f0109081e060109020f0a050c210a0f180918020a03050a02011d01090501110f01050702010e 65
    0x250010032111491080100d180c49001d440340700d001400c00c0514041d1000c0000c1c00d5071a425480001d003d01c41d00441c00e000e002c50040703642141481a820004040d0303003032090b2000c003c071003103003840410200c1407510748035401c140c040760251801880d8841d8540304007240740d0070088054911840461422441034941e142042c800c0c3c0800d02175a409008140b00400c01840c003a044200644011f060800820b5100c40b000c506062960b00b01000309940c0d80c40d02011421304200d0207004100e501001c40c144803d943c4806058440c4481c19404c0200210303521010321800d00c01e12543d02c540880054203880d0300c902000305500001c01110109e02500d140200d00342c010884400c4240581600810141c10600100b00804607404105850200c1503483c000584a4842501c06503001341e0041051001030301c001081c41d50100e848103c2d01c0900d44942c52645d8000d4410000c0d0b400c24280b581d0103c41900714185030200c1d00c100c0b941d20358208030502072407507019806000c0860b00e50041d141e010100c1503 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 628504766 1250 628503516 628503559
    0x60705190801050906091e010f290414130c0f0306060c0201080105100306170a05071d0105040504061e0c09051008010e0c07150c020d0813030e120109030e 68
    0x3051130740140c02113000890b640b5004007107076808044500d07800b040d800d45590034030311140c00742c002c0320b003003850f103c0103010707403004900300001c40140b842031000d81c2c0704d0104020150340500d11078003102120240300c00c6003c1d510a40c03062045080c07a80f0412907003458200060080c181d0f010341e0700200380303440340c00329206100d20300070781c4c580b0340607142c170350540c0d18201c00e101e4000000358186041640d600404a403031010300b1000c01e40c5040c1040207100869450074480e081500030340c01820820040a168044904a10300c04c60441c3c4080b1000074099845040a1000d81803e41c0035107000303210440030b0460355100707608c04404456143c3c0d99507021502c50060011301018207180001140b80d10340108141038100381140e502020b441083c60900380541d0700d100203541c03940201d4040300c0c2c4078007000000342ea0402120000d4981490841c019081188040d1a03c54441d01d016081081d481814500d641702c240044540760070070300080048032ba80e401d0060503003003400c0025202d102030b04107030b04001c00c450 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 628506016 1250 628504766 628504769
    0x30b040506061204122c030f01051003080c03070602040b0d1401051809070b0c060f090303220309030b090c0306130822050d24090506070c080c060705190801 69
    0x728000e2003107803910384405d054510200301c00010001500314036001c1d2001912400070b440c415210260b217841091007010b0429a100e00e155015038034181c200100403604082c100101c0e40c100402560718460040c0303081c10351080c1035015108500005002400e8402c900080150201030602003141d6482c480e1000300b00c21080c425140e0000d0003109000d10a00489101030b007101581d011100111381c1d51245402d141c22030903d003070040c1c03c50001c010f10024030b4036103182c0c09994a4051803942ca0a44400100342d0941021032a40010001c044410103002e24083c00c05941c205c0c14503195807030700000150791182e028451b04e010b03002d15004201210000309200811a901030311407420300902c100c5040e03921f2180c00607404540c900d16000200f43d04d0708901010010701500307683d001c80990003400198111106e6032618054600300c400e40210310003040c0c0f141c00880d585040d80100d2403034103040f4000c1c09054600344880c0181014001c645030080c000f04a02c0c0d14a00c24000c01408810b810384480c0f509 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 628507266 1250 628506016 628506037
    0x108010504112106191508070314100f060c0b0f131205130803071505070507020a0803040608070804080a030b06070f050a0203120a0e0f0609060a030b04050606 70
    0x55000521451409420000d03011048140d91418030014400421128010031498034482d20340701c081c86201c0c10080084110410040b100007100c51900042c007951940c844002006c0000c1d01c4c0202c4d0300f040c420b4000e848100e4024100b480941010803003000c11001174402ea010754420720200280590152070314824494101800407000e6a8129640c2d00c42c4c20010091490b1180c2d2821034400100d404981c0050f00c4440d90b90191212303c1101260813402e031075080300e40981d00a06c6610f0001d5120302c507184000c01c101c007001c5220b40300c0c910250f54074081c840c4002c0d03001642034400f03e031016000001e0412207100b81d98800d4640c80c1c80c402550100401d07640600103107001c102104c03810380287c00074040340c90068801403404140740c403170000350120715000700c0d21742d002403464030250320f42000718040c0020700005c0b2510300811481c002d000c03000c1d00e461060146021404400b001d42d100d6054588400300589441da41d007800a4005009140034001144514a06404501141400e1007a00da00491 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 628508516 1250 628507266 628507277
    0xa0e07180f0f0909110d03110c06070f1b17030717030603031803031b0d11010c09050103050402060c0a03090e090a0209010b1303051006090e010e0a0807080f030708090c030a0201 78
    0x3c2c01d6121001d4a0000d44c01c1c0c031020122110010992178080700e291816001c0c0da83c10300080c0012646508007011016601e100343c40502c40400445c80740c0100c6070042e503016100c0d412070140c10203181c143e0300a607449102c400e000c072881c02c11400c9001c03005104041c4183e01880d900d409000488010740000d6401680560044c03203104501016070b003010403800750003411a070a10000c444500042c05c2d00d2105440c091f0401072000303400f660440c086008441c0340702c000740701a40200d00c0c002c06501d4a481040e04064a40000c40e00b5074807410216026141c410040d11a0440541805090006244590001c4054607070010300c1690010507200e440b203900804c0c0c913900341d21b001000c040581250384545107a41c1307038006c00000108100300b070a0380c1c28a00d50b000304030145000e2040c01207603901c20380e1040c82d03410304051054040307001c943c41d400b9a0b4030031031107900c54030581040c40b0a03000d8402c550030705c108008184007450f600544003d2144408604072038040c0c20300c2013416182c0b440c50800034003066 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 628509766 1250 628508516 628508519
    0x80d020f3004210501050601020714040b1804030806010908071203050a0e040f0b13020301150f1202030901060e090f1e0c040f1505030f060f060a0e07180f0f 69
    0x5000e5507409030000d985014540c14a0b03100e5140641c40507900303c150010a010001101c100442800b52580c8054240060b1150078a01680b504078900076801480c499030703071501d4658099882c0d04e107240e030182c074107800c03500985494a0b025080040940f0945d01040084800241e04400042c1001c10b88840d0000000b114410350b074180c901303070001e10894040c0400a164000c141c0c507030b8850f043d03051280c14004141c94281105114079030168120b10421f160041006000e4540c0031541c465100c000c0d440c0409901c08441c0f070444c1d07940300201d54020818000801d12046240541024003134a001c41a96142911401c40440c3c3c0e03007400000c0200140c1018080c0300c0c2c9144100810303915090707860203542d0070712034581c0007400311400700007c602c50b55a220890b240e034a07010303604440900029002052604800310140d81e031481c004083c03000914504000800c56101e0407602402082030b4912056941440074000c1e20b00b0b4665920204190105400012019021000b0108a070303103042484241c503 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 628511016 1250 628509766 628509823
    0xa11030418271b0305061611010b0102190203010b090f070e090402010e0d081b061621050613020403080d0b0a23121504060b040504030e010513030c080d020f 69
    0x1c10300300702c02094410315040c0000102d0030620445100742040b0111f0748106800e150040e10b030b84181e12003040f0a0f0315000780c0b610305980014072142111691072000a8860803440020301500e0244451500000503405200440300a80b40740c0703000d01c05a45620100380e10000a0100f0810201c0e4003900007201c100841c1c052b400c3c520441401c1d0383c0101c04852602ca61101960a002102c04480d022030307104001f0010707000e1010188101420711854146002c204020751600b402040070010b190140c0d43e400440c00507600c07210000320a0201c10002d40d00e6981d01c0c1000f9074140c02000202080504101c002c0c1c0403450088126030075240c90564640700030084107040c5503c00551000356400c03d20108204a42c0d041c03c11100804964184c0202e40c43e00d05032038500e05640080801501490604c814000040d400841d0742090003000c0c40c000e0344440110988a4500a2230390000d001842d94040200701101c0101f0903240400c295001c8800c2101c00100c030540d10728002d80102d46440b0003103a40c0c0c00c0c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 628512266 1250 628511016 628511033
    0x503040602070f0501020327060405060f090c032b090302031009020301090615030c06171503030702090a05340e03070924080c090a020a1103041827 65
    0x5500400340c0e86000c0180c1c4d918582241e10a803411910000b202c845102500010100f551941c0760fa0070143c4094141a51031594601d0b001d03088036000c0e02d000e000100c031035400308010780350b88030001c0885038403080d4582250380788091480b04020700c8e90001242000580901c04001c2181e41c050000c01c45000744040860081c0212007040303074036540750280c027804181c007405565a003000c192031006080d45946045940d04490303078802d00c20b00480043c01e80200040651460780090689000c004440a210000382144105140254040b0084050050141181d4803141c410059100c42003900001000f18044480d440f00e8008901490342420000701c46c0f01c0d2a0302e00d100d40002d0f00719402c66483d00203040030386a00f03040000c1c501c010100c402911032043c09213070000301056806841c40703072290404a004403600401c4881c00d6038001071034461076441a20f89600c801c9044060b40d80702c0b52100194840d42d82803041054126040401014400e844041d0180500b900b0601c14001603040d59202c0300d4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 628513516 1250 628512266 628512277
    0x70f030c17101e09050d020d0c0317061f21061212090b0c060610090e070e03031317010c1403190f06080d1205010b04030206180324010b07030503040602 67
    0x12480c000f1a0000b48940e03103000d0035032071034441c00150810300320f4800001e141984a882010410411680b00e00c00700b03410105113000c1c4142440c46c20415034840c03000c20300140401c801480c0b841d121f00300c41104542d1000d88250341d00c03088010310450700005a224001c1d07a220340244182c41c486d076245000010b4480000c0a1464094200303100032680d070794410040b84c0c103c01c0d51030070250420b00c01c210030b514090103404403401c10741c1006501141000c0c0602c00c1d02034024490b605100b00652581c01035a010020784001000c40c803241343c0c1080c0c071240c521a42900100172403030550308000c0b440c03003682e00411405031082c10603200d1034255aa0030400c00349801c0c0c0f8410000825030380703420b50400240c2d6801080d0107801600005c3c00e091007074902c014403c07000b2070940e804080c5400014070900c9800c07011181100c0d011148244c030303100741411003402c031a40440c207980e0601c1a03040200485103081401058601118429030143e81e03112105102ca12403032100600080003000001c8c0000c0c5140c0c003a04 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 628514766 1250 628513516 628513541
    0x8030a0e0a0302040e1014010e0109020d0b0901090914030304050309060f0409060f0501080907060e0f03010e190219051c1a150a0b1204020d0311070f030c1710 70
    0xc002d82d81e8001c5411148048030b031104036006480c00301e11036100b6001c2c42804c54400c0c225042207624004181d51210410301906201d1500040c0036040b02c202030700202c40d8441d005000c4001741d44d40d000ca010050141103400c070340300307a2002d1088600b13070301c0070094910442c0c220f005985081040001c0185540c410103180c05500418007002c2008000351041402800000e0105207007207081c4030014140c0c3c00010120400d0750f1002c4003d1281a030f0000541040d1700c025580302c0110030011000074090080c030072004d0a144101c400305056904000d9010410b54001e03112490f42001d00110b6440c0741c0e0160003131a0b008100c0b040707481e19004000c0c0e0074032101c0f80a201210441281c2c02900c0741e640c40e050f40d40301500105d41c50a844540341403c030a0700108040500c0e54548a00034500d0340b84400d00401c041d101e452420806804e01d4040c0c2140340401c1200310a480341d21f9112900c16103146551702003a980c00e48480400306840010016640c1035181d61030040c580103240e0b20000340900082030701c80 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 628516016 1250 628514766 628514779
    0x10f1a0306181b0703030f1815020a091d0402120a0507060c0f08031305070f0e06061e16031707050d0903030209060d06091503150b060702180a0507050408030a0e 71
    0x440c58aa401405421113910035940072031003010840001d0150b030b40d82264460000000380c0c9220004501032a94181c03018086400f40c1c480d454171a09807001d040c0c6070300c107100b0300c0c5549100c95003c0610308900d511843c821204817024050090240b43d6408149400070415031141c0814070000e4000d18809400303d104211040131081d080d5100386940d0010f40710030010043c00000d0008011007400f80c813002c2c0420301c605054480c9080240b82000c400601804d0048000090110f50140641c6949050103004017500340e0300c036a48110446040c06580d41580001c1d092140710823103216820b007560003000700d40da60500f4000200900c10042c10902000c070b0516900704010841740d1501c81c00b404103a0f2518200048061038261400c7c162103040403246d601900e20903060000405002c0241c240428a80e0006611a81c101c0481c806201d8841c02035400203018070340119045e658920240320309041c080a1185899110095806009038080d89285410900040301902e00c24041c41c0c0c01001c000304032 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 628517266 1250 628516016 628516051
    0x30a020f0a020a0b070206090d05030c0405190608100b0d0b13060b0408071d01061110020301032901080613020411030f0108120403080f090d0b010f1a030618 69
    0x49195015070003810141e00215904018882c079040100e9008445002401e42c0345400655075031245e404500c00001e024010001ca07c55103008400e032005410042c010200c00070a000b00e01d100e40070390307101d194009051080010f00640b03514926000303c88000465a00300000d0a0721200a4900c0207030450b00f100410020548400e01401603000a224440790f0540d40da0a24416a0800d41e0680014445101c0c40c0d10002d4400382c2f034880d540c11a1002c3c03030305200c010005180c03141001075a01510307040d00e00220011051042c0680d0204521020301e00c0b1b08008034543c04500c0d0030710b800340303d11a540d8010f400019131106500d0b5000540c548010000107105201103500710305904160361005070700d80398400601000c24200401e203141d50000b55003d09003403841c0d0360300780c9900c20010841000a00071902c00c080d52a5426011091640f00101048641c0c442c7c4586d544c03000c85100d090861080b03101508501100030045a00859019210683d40c0c40d061902c405c8410000d07200100008070500c0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 628518516 1250 628517266 628517287
    0x180103090506150f0105130b07020a0f0807090c031b0e060708070f140a05120d18060903180b3f0405010b01080105010f080c090d0807060609090b01030305030a02 71
    0x1440d116a580c45002c4041402c5a070a2041c0c24585480c81ca040c06820403640e110b4148040302801180e80310002c1c0c1e0703654001840072980e10b8005334009050003200300008140c1da24003003054025512034035010010b1250544089042e200101c4c51101001c000c0c2d0705000000348601d400700032450015105c00c0c5090156900c2c0c001c96402102c0580b4904a05500c80c07082101e40c50301e604210310350000a0102c42442c3d11101c1c3c40704440c84c2141c2001400040c44145101d4070b80225006040b80a4020401c03151410443c0180c0700b103040031000118a05021818441c82c4c075421000d4450308803645080007103056130030a40002d100d900d404441740c0e030484010034000da841603040c5c215011900b000103050503d4810300352144040500e061100d00c42c01480680da01c840c030301045002c94030349100c080c0c0b107205004503544120b00009812844210002041c00003040040c81418481d440401009039100c91001c222045e60900500d1004400010000f10f4428005503401044a00c8014a440440c80 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 628519766 1250 628518516 628518523
    0x30f0b10030b270115021e2d0712110913060b010e060d05071e27050f01080405190b27060730020c1b061801030905 51
    0x51200001c1d125100b0244504140b80341001419901070040e403010122800303440c520005008150005000500034901135200704410b82c42070b1142d84c010007030948880005512401080206080041f2004400c0f503003803c071626054015580801500e0000e050040d80341303080b21020007d80c0c9405944002903040d0390f85420241c01030301d810240107180c2090786402000c0d03410b004c401d40c0c103108100c5042c0100c3d80b078200c1203c0b00c2003034160001605a4442c1d800f9110304842070b5a98a00480302e07881451020f41101040442c9031500554200410158090341c2d40c55109010b9079401100c0500301c454654080c0312034a0700032b88550243c0390690b840c3c00750b080c110826440f066444507112021310001008628800107a04070719901185808480e0400590310070010303012000700102030a051500c4a02c20100c070003a0100c08801c074012a08280081d400394100000d486407601034030340b041c41c4017480c06a401d0200749014000714242110750b58040041c0083d00307e0a418907850fa061040007420a0 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 628521016 1250 628519766 628519789
    0x14040e0d020d020f06040206030a0e010e010c0f030e0f0c0d03020f0d020709242304020313031806090918080a0207030b0711071a0c1023070f030f0b 65
    0x981c01410710021061000b85498222120f007112034100710148000740c1c440200f100d42c004c81c64038000c91540c0c10300720450f0041c900d00c40d1109141d46400902c11006030b00c000c0c2001310307102565050103401d064009040d10740c810318180406940c098140e1a500d4100504125102030080c01030700d104041c030701109814069850004001030b044000d0510820206120351003250541c1000306510a4440006a010a4031405140300d113a1400084402c04e400c07400840900310380103001951203061007a031582c6060b840c0d10003103002c00e4140d5540c035000e20000080c04100c070050340d5040c041500c2d00c1c85010003000c00f031009443c440d04045640300841d88180051295040a900a1490300c2c41e5090616030120007400501c01c0040c150514000400006130308420f484184001c0d550701c120b41c030180d810074411840102110b000b014003c4080e01c40c41d500100381c0d07864440f5414410b60186501e5540b10800700c5000d4085411240744164652207680174060f0f908042d00001440071891001480c51242c6 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 628522266 1250 628521016 628521043
    0x1118220b100303090608190b0420090a05030109080706180f1a0108010501050d03110c0a120b0604090305070605130206030c04050310111c29030c0307030201020714040e 74
    0x400d5020003c241d4840d030144010106032500200e141021704420311608151007201c000180c481c07451407100e59640e4070400f446109003298003541c1852842d0420181c0040062134801c1c2859140000d4506042c05041c956940c8254800d181c05d5541d5510300007030042516030031510855114010010304806e200c11000381c00750103000a0460004054042c20105800c0141143d04010040129403503001d542c82d15580e050401507041003101d607555207003800d00500c45900c020344c0c080016004442c0010340850310f02510300800a66980004d200903501d440070010002035013040840c012072240d503c80e6410002182030351181c0c1509800080d0150401d4480c01070414000408001c0c0d4a01081185a0801412000e000d41e0342600c0b00c1100780d0203184401800d080c1400c4074a801c09960341d1112041d0050b203d072482910a002804203800580c07902e019010b03200c1c0d03821301b001c54a0001010741c202ca034168000c00d44a401c0c80c0c0da030100801d118030000e03001902c40740e4410b145d007800e12003145070f180e5 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 628523516 1250 628522266 628522291
    0xf06050f070804180b04110a0f140304120f18050d141e010608060903040b09130e0303070f03090213020c0307051b0901051f03050705070203030c0a1118220b 69
    0x2901e406400c403545d414082c0e00c41c501e00010000e2900084007510a000c200e42409803032140075480070b861010515a0180712040c0c004200320811503600303c40d0f40c0c55000ca1761444003c0310a18402c0d03605240700249020031651882d01046103142c04902d590465204084040e04d180001c130b40c1d1850a005802110040e124000900c030400500341300f0742000b0200d80000741614100101080d4072445640175024181000040081040d140c80b0503021407040c8c924000c0000511007200140c4942042e221113001810445205c003249200b400f800b540e40f034000348808500301225004c040254400d075142c1065000c00d01401c0003151092008a2041c1325040d680301526507e0020810516016000725119148251000d91044242e42400b84600414280000ca03a01d408400340c07454000c10b00300070b40c9840006004001c0d008085a0301d40c81620448058000c4240700c010020f01c98882049230702c6540d51040050042c40c0388018050a0507804154000f805c012622103d0f8050030440d0721419102 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 628524766 1250 628523516 628523549
    0x2d08060a0f0506010203090d0f020d05030309060a060515120405011e050a06120c03110d170903010c21050604061505120603030a0e010807030f0c0c1104060f06050f070804 75
    0x1c40b4060b00d540410244043c51410762a10006180145260030160000201040740011500c1e405109040d094000781100d44a2a00410540d86c40364119491042141403201c00511030901c00c130200307141c03110403c41504000c0603284115411000410503113440d900c6105044444c1405807110382c00e02d000d0308010441317142041400043c1c0b101503100615034014400170b5004140001c01c00000e0300e50084068611001d1880001ca08085d01140500342491a24182d541c02c41030600800030321070194000d11020b40e040d03c081c0c0d42604000100f48400044409038414142c40b9840581d20070b0000300000340107511a954940218407412400011400c0098a02c2c100e9a1000c1200d44c440c800b100214a00f801c2030034020602c58824001a050105c1d040114406074080d4201c4840800c0c0400108141c0c0c0010100401f080c08881c03095901c0c1040c52524449070405019200907900c0d0b03a415080e049250038000c84103580600140c0c01420024459080040e025900400080001035081d0f071000 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 628526016 1250 628524766 628524791
    0xf06090609140408040b0f4008030414040f0c0201050106020636011e06050f12060f1e090604060e0307050a0809010c0f0c0e07092d08060a 61
    0x7140600710b06042600d01c00100303c0041e11031400c65054488140d41c0c6070320303414840d000a6450003000041e500c079070000380100280e202c4442e10158080d034044004041101c5503411540e0195070342c0a211a540c00c01c000a102500c0005103007031460b6400381c0005003034188014004112901100c580005035100d0004211686e410407015420140418251581d01000c0382c0e10030811601100d0b075030801403590a0268103450a50101044100b03480f440200ca40306c031075903c2c00410003402006d1040e01c132420325000a0a08446044030404004028455038540c0745821310000f1000380200030310843d06d09102c82803401c1071041802625200c001701404e0030b042c60102c1c165603a100d400c8025074010306c400d030003040001801180c4150400501a90707008080012542d08140784c1010b001c803c150b82100b402c003c200122041265040010300c040c40d00d4820086030b1003010343c4030b00320050f501002580a413002c5242000e080c2401d01ca10341030030700d5541c28203504003174003291400c4265640345d00b2445403 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 628527266 1250 628526016 628526021
    0x30e070b0f0304050607080705090f04060315052517150d050f0d11030313031803031e020102032a070605010b0318010209030d11030909011518050d021002010f06090609 74
    0x3003850340c204160585080c1d040103000303000c0d122555201c0d0172212f040d900c81d9141c80e0b0000d8051138200303032520524100590b0020140c202030303400c981001700d04118110b40203000d80031b02a40141310380e16140c03040300003003904025034030291803065020748070601c01c1081e580d00315101150911900150010810b008145410000941c0c070035000e000745a0742c0c00d0711010010003126031100b41a1035141c40001141422202148404201c60300844218004414150007200c2d1000046000c81c2d40396030b0083d0500100c0c01d03808240d4080c441c8164940395641380c42c0c1c041300d0320100c1c1080c0c0f4001606001d903e0300c3d41c8040d6942a4400c0b41203201c0001401703540c0c041a401ea0031900c401f44000c5d40342c0391500001c26959001640440b0401c1400030241140d80c000f84212004204010180d00c0701756100c03c0301501030162613946030089003400b180e11503040307207403508041107038801801c280c140322b244d4007806029903a03005a0001c41d56a5503403121840310728491035014012441c40014a40d0804041300c08 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 628528516 1250 628527266 628527271
    0x11e0e060301331a0a051c0c0903050c060702100f12140910140a02090a050402040e0105190f030b0403020a0501050c04081203010b030403030216060f0f0f0209010f030e070b0f03040506 81
    0x7010b1394403040110011060b04030345c0c010490340342003a80c5d10700300ba801c1c0764600002c030103410b070080c28000d030a00200d0340301e46940152406403007a114401549020000781340720b075600007500142a03500c9001e00758000d0085a0725100305042c02640b504000b41003a044030300f05501070781c201400c03030140701d900c01c401c00603a00f803000c103540b080204800c1c0c654200b1280c1c2c801041f0741244d680006404a4a440e91200e100081402070025911952108003000942100b40070351800342411104110024052003100e50031201c1c9103070308046242c25500d400e140114010000d4066100d681c2005001950900c80e076841400390710540741d1500d041140c0d10b414020b0001058162000520043c0199a0001c04480d001a032500340141ea80004d0000244046021030025103140c0c0340484010503880c00340c12030003074444402c00422a0035103d0044034200d025000040340040d0940c10f94041c2c83c0c1c000d0703200b005030503604802c403000d190382ca10307903070519502c000030052040c80040706006c00c000d410481d998 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 628529766 1250 628528516 628528529
    0x50307081207080a290a08010203090c1014160c0308120103030e010903031b052406152106030f030a02240f1306021303030314011e0e06030133 63
    0x41c603035034002105c1d0701d10440d10010b481240c13520102c007040e55400c002c80018101034000395102d28007401165100c0110750910b0703001354481010051640e200d854030700c101240c150100c5042c00d87d264040c48440d1141c041c00c4451007862280413010800840141010300019010b0642da98114a0000c200340c409940d00e6061001034501030000135080342455001a180d0300084451143c0740c200313a450564003010450b86404084c0340810394548401c131640c420b560554001da07800703805201e0074003688a091380404074001000702c0181d6001c0c00080c3ea540141b0001d04031166400e40304c444a0a6a100c160a200035070300c2540c401445013004406284c2040316150790070014a01800b41c06001c001c024035180024188010f90400c2205907410b03079194850b0465120300c00d40e144c4c035000d00200348852480904001010001414580c92084488001c0244800c6040140380c511021a200006400350f82e144d52142c103552032030700d4900e0f0704500d409a412190f40400040650301c1c4000040c81d000038 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 628531016 1250 628529766 628529771
    0x160609030230160602030108162306090409020301051e060607020a030206031012080a121109010c05070306020a05190302160b1f06021e0102031e04050307081207080a 73
    0x80c0e01410807a20a00070b941c11108103540c0e0550028800341800c80103034020a02803000c400820f00b034100240160f03c011b50031358404650303602c80561903001c03052481201043e500c581242c0c0c3d500d00f0b19002400c0e002d10050b0022451f032000d80d000a094034801c40d9030350f035100d5030543c0030004a01c2e8485d980740c00807016200c00345001c8198010a0400380e10340800b901030740c400400300340700700450b15900000703100d100c200c0202c440350f0380343c030031510350265100c400010100c004000320400140b194607030048141082a1030811010019141c0028010b401c0d00e16000d03d036000004107815000401401896941e007503500c9511950f50350107540301c498640101072050200881400c0c0200401255075002003102c030140c0e030740f010383c450140d404618002588100f034100080c0560009022860b0070f021149221404000018050803400116242c20342000042c07070b04451400c0380703554150085c0c012403e89103000e006499076281c941c0a8a0554031000481003000b035610381c0042e1310750304034986000a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 628532266 1250 628531016 628531063
    0x709090c050108070903061503020907020303100510121418030a21020f18010e0d03093c06030b10080a0c0210090f140a0206070b0c1606090302 63
    0x60424150030340c029075040c041c021002c188124003072881c180c001e41d401b400512581005003600035074907007684001c0b0700903200380c80400c1c9618001300649100c9d400f8030b07170b922005900d000300300613418100d88050f00900c0b015401500301c084417402501e0626101c103d2480d0340d8184112101a0700c2c800c4501d403c41c1760014444005c195900512103c08000014020000c61411400b400001c0c4980172105a2800000070420304545a140c80500b1560090702c1d40141c0c42080e80c18003000340389904004000908814040c408501441860307020040c41782003840c0b01600e0440d8083c4404607628082c81e031100c01183c1084965818080c2412988041d0f84000003030b082100301900809010309a50511500c1e441036403511747c0f00b0821001e59458028060024500301d0915181d20219031505076101c280481841c00202c500103031950079654007422243c0b0300402070311203070504078000d06044600d1404004080d0f0115a41800000c65402110005040b20203883c000c0d10b4541c8442e41a01241d8a2428 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 628533516 1250 628532266 628532273
    0x3090302030a0503040809100c0308240909030903150a0509031e090f04050a0608010e0d0806010813051002030f07020a0c0b0703020102040506030c09120f2d1c02070909 74
    0x56030410300e2103003010f03520380c0c48502c1c0222490140c102d0321030300b007200d034074003050303240d9104c8d107a004014080d0300e0707850247d240c3c15031140c160b2200c0401c076041c0d54281a00c0a2040c145545a1a4005885000e50342042003010019040142207200154200c18220a01c60214014071509800c010854029880d0448581113442205c940341d1802e0f50680001c12a4a450740b03d0300400c99841a0050041005140c03411241e0b0041c03255004900c8551302c1d2a844a43e031440015403101030702d006496a42550341c40100443c0c01e0076009180000602628541000286041004002d40b40e00300c0d00c003507100d10b40041d0104055000812600440d40940303013960104107501c0910003a42d00003201180d13500240c0c1416806440f95501c8190030040c00000c1201c1540002d01030490032400315840c087c241c0100c044103603941c0360041c9035001da4008e854070764200341c410010242070300c4084182c01c001d80e41031003d1a051081c0300856a4002c03042c000c106545c1c646c141701c1c220150450110400c03803112140c8 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 628534766 1250 628533516 628533523
    0x40227010501110115081b0d0b0402040b150d020304110d0b04081305030304030c0f2705060409050105070f0801150504210203030a0507050c0607150906110d09021003090302 76
    0x10500c1c2c140040300c80015100700d000c2d0450f001454160041c0c030800d82d5144451a6a214605e0182070383c80401040180d140c07a04084049117590080c500340c13036a403100d400300700040400d51041944001d084405020500140c0041d1400804a900040c0c5920b05030070020f1201c0303214009070303200d0724100d00c1840c0021000711415030441d412070545a22450ba880866070040c00c90303000b09a1500c03020900004207c4590344e00385c1034661498120148a0345c0340c504070344d200054244200c0f1070401c0c0c2c40c80a90743c0340395402103903c210020404036021069480302401c4a000b650b40000203541c4080c03507803e030707900b0001c81c1b801400c40a101810340000310200401c1409503001d582c0c80c404444100003242448052142096900102501e58882d180c0f10060807941c0160300460301d40c007443c4600c1130349241c00300503030320115003101401995080707240a501c010900074104a440e142e41e415a0f0312030165003409028445001000004e042400b401003040314403d1310030007c00c040c200001007000a6012 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 628536016 1250 628534766 628534769
    0xa03030b101d1c05210a020a060207020a050d030503090105010e070c0303151a0a1106060d03111608010209120127030908120a0f0f0f050a11100504022701 68
    0x100518034015840c0c0c00012900ca0300e41e110f00641a03165290308080c0f200200340007819a0040d1100c266081032809084803500900343c1000240c0c0288181e8404504150001c140d1184020b0000349520741b21000204842c01200058001440c00700421000f03000901c13815000d480749000b0180c241c42c108800030441306595200904050715000220f03443c105241140b00505403010b40c00c902e034030f4180785071400e0f500320100150000c3d203071103105131a0210204295020340f402a045091040050b107040d6100b4002001d400011301c1403481f822141c03505420070001824240d000541e80d040890100500e9100c002d186c0030490b40f5004580300340790034066021084880040700380c681c00c1481d08050b240c100b425840704009004050a000800c09040010f00048655441c0d1514240021408a0b8600700301d40490001c20301c2c181140c8401402040904a028410300c1c00b031740c8400202e003900303080100f03205049506545500c00e1008615202e003060080049002c91405008511f41d940c9450700c3c410b = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 628537266 1250 628536016 628536047
    0x80a110f0f121c050c09100801031115090901080706110601050f04090302070801090b04030809031603031113090606090e0c0301092307080129030a0c0507050d020a03030b10 76
    0x4004150015a03007a4003c0c110008204200900e468000b00501c0d500c001a0309200da2040304580b07a0050059849a050700c0e04056001d50003400c03481489000c564070142800008010322038485280d540c00c41d4507005e00414030180c0681494604081c040e510101440e010359040200144030300d4640505d007448112040310046120045d5090a074201031b080d40002032036500f0085440e040c00348410030180074921a660381460b60380c07998042d42d100c7c0200c01241100e20081c0341d004002c01d100b50020b40c07400f603000305814a88402c2c495a0100c100f0f66500160201d921440c00f0007200e50040032407001407100490380a410300d003580e101c1405203c140515001c3c0740e50344e1010068021100c41c22501c00c00000c0b5004498184154068183e98003441210520003643c0c4a80c00b54103062540e0300d401003069500030703041d41c4500101101800c1140d07100010004144840c0d408543d00304640c00040140c0c0c1c001d41400200c501b401004c2d41d0403054180d01551019540c01b0405500c454000d285855 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 628538516 1250 628537266 628537303
    0x40819121d0f010e0901090e1203060105090409050712050106142e20010b0f12070909080c0d0908010c051e0d0608010e011d01060602060601050307020a080a110f0f 72
    0x103200b0050361684124800d2030307000729800f0004140d1345800e40c80081d6075210380701100d00ca40c540c0421440c4520017212031500080042c0011866820941c104442e03291141c8255010709440703440114071008004010350300ca039145c401c1002880308050444081440647d0441c400e180030481404030040780c0c900c0d01c150355a040b01d8100c0401e00c00c401c4e074003107900440c0d80307001c1900414100d01d010382410043e69200744450f600340862458032803900302c9010030303e034050f0284070306c2d10090b030f001400802c0d41500c055004118004804001f800803905500581c0c4454070364604001c80396007101e00c512115014000c040015600300700d02190307222000c61200141903030300c42d00718400c0c81c080c1c050303684041d0b03a941c20461080c503102e406400c250142005981b030b09416100c190b200c80d003031302c5c520702c2604003682004011441c81d5200702e00555000d1030500440c0c103405429030350521554843c50880b40050100c1c8a11005190103014207a000d03050300000381400325110804c29101c07800004140042c04 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 628539766 1250 628538516 628538539
    0x402090f07022a01021c09290a0207031a07211b030b0112020306060f03061f031d030a020c060a1101050f040b091209010e06040819121d 60
    0x24420400f00b107101ca90718140c19020420744200701c03048021140590b015014021410b0042401d19541d1040e07118280e5a80c00d226181c1007025840c0f16141c40442590070341c1d03415040c075a208800003031000841c154010304019103142800160710300341c002502d42c4a1003141c1484042c0341c2c44504200d12020200c042c184604c0001c105e00c4c000d1292500305400c804280d00b407148031540550080b0714602c802e80303c0d00c410403641d0b10707504200c0c481115050f5218409002c001860303903601d4003556200c000909241c0742610b04000c1100300202030314508000a4481d0500d100c1043c4090f01c0c140c80100b82c1d00103600705514124040d4483c0f00c045400d5014a40c0440c8500740c06100d4900020f03002100300081010341414031510f00c00800884003035418420603004913032004000030356000c0c1840109191410150310300700442d0012244450203620000030312010034240420300106502c156403120340648241c40f1326210011071520502b00341803150400c00402491f0318840d00e80d4000c80122040004003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 628541016 1250 628539766 628539781
    0x703050a121b03140624090406050d0506091504050c01032406110708030a0c030f03060b190f0807020a0312060e010b071a010b12100812180301050402090f 68
    0x10214500c00d00d2140410007000c034030a50300f542c0460380b02816055900c41540e40c400074000c2c074001c00d0411404207080f00303180f034003041d011102800302014010804600d003a50b0300f0014901c107020b0001542c2c2d91300840180b2000007010440700e030b00c1030758144d1104414a09920b50302d890b26180d40c421030515441d08002107254510348424286c2d90210221040036945030000108900d1b110740100c00a4070420f90049521940013054410182c40c540c0c40804503e490f5600300c0340c24601170116020b03d51074188c0440c0042e00d6402a240700c1085000d90200f4413504075005240318903040310007060180c00000e00540680c08107504601c40c2e003505159003018840d012042c01464994801440240200c00108070204900d000744040c2d401004c2d10002445000302c14003807590284034403443c844042180c2e0303c058056082141d40a50b840c0300003039506a880015606229607114030071010040020ba52a400006903c83c07581ca10054008000314a440d50108003080d101070300804580c200c540004000d0b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 628542266 1250 628541016 628541021
    0x81902030c04170c090f18030d150b190f0507020409110415050a210f0b07020607092301030e0706050301051c0503030a090503042d0605180f0319080d050c0703050a12 73
    0x34107d910007100d0341c80ca100008039008000301d2034038641c01074000000092040209040d500d07807202241403e2040994013101346d5203100c03c02d5004090010602161015a44a1140b1081c2c01d000707400005440c0400790820080380c40e0765003403001100a00405028a488500100c1e0507580f21600c0511030b8079504030158844101c94000424010030b41010b502040350f80d101040c0074150300d80859050b6110020192031001c81360041e0131042e211004070817440d5107401a00303400c110042c1070001d55128010b0541d814140960820004035100100410032424aa858000d04803c1c480e841400401c4650358162603100281c00b60016549480100d41801000c1c02145c00174441c440710400c4014100c6084001d504107500d005035281c6000f8000100c60313020f841124000c01e1040e00032004201d13030004004020900040c400c1c0c161080d10280ca00361030040d42151202c90061214544890340110050f05403600108800000d0b042808030500081d0420151544e00c101400c0101e000c0001c41003a500 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 628543516 1250 628542266 628542301
    0x6060b0c0d081012060b0a08030c0337020c100318060f0e15090607030e0d0c051614040605030c060a0507020612011d150a06081902030c04170c090f 65
    0x4a143c403502c0020880c0c90f1b40865080b080607100010f9a6030b83d248115100d000c3c07d500c800d000e400030404424011103028100c0442090100d50002c10404411100002021002c4900141c1d00c14440c02c3c10354a0994901207080c0e52500d82032000120385400c0700b81200035210010039450701c52687c880c05c1d02c40340d0004804115101c0c226a54489103c030440301441042d218404d05020301070118003268032901039100d030900444010034841144240445255130400c0c01a1820302608145d102141044daa03002c00034840350640202c80134078242000102d907403603170140b8800e901035034084c0400d03101c0c0700c1501c244000605100f03498202a00108100b4811181d0b13203860002c00c9800410805201c100c61541000c4001c891002a5240c4040320540c40890040c1b41c1e01500501080000c2d170310a21030160700500001000300c3c0800c824a046013a40c0042d140c0034004100800c080c440c1c0307419800106c0c2009690030041103250704800c003040000380d0191a220740200c0c0e140000712482d02c410070285 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 628544766 1250 628543516 628543529
    0x3010f0b030c1b030d060f0506040605090d020618031e12070f060504080d1803021f020d0c0c140303240127090c0507021c03090305060c0706060b0c0d0810 68
    0x24903280c0c0d00d0301c0d65102d40c0301140d071050303c520b1b00101054070084e021040c4192200035249514050906005441741e42064207410b42c44094035030008016207074000035201610a10310450700010800c0105818550490020048070605140040c0c0c04031000031319042ca018500d403019038400a90500801d134030070382440070380a070b402e000c00d220412280300010306550802c1c2100300a07103160401440c1166071107040180c0140d0001303c0b140e0360440711015041558a408100600d02100c002e029003c2d52928681200490700504404003405401c01c52000040e20400c0614134605d080c0c80000208121055801d403441e001450a24541c1d00524408901749940c0340b10515424a541089401c0000c0c0e02410b24004d080c000e00900440c082c0302582d51540d0700414082842013229095503000450b40b5003030707003002003074980040072807414028540204000007501d075884c8c043242410826940e06a100500c40301081085071003512000c541c031f02a2201c03d103008500e80d01e4a800194001c8015080391 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 628546016 1250 628544766 628544797
    0x8040f0b011e080118081b120403050114010e0f180f060a0c1b020d020a03080a020f0706090605031f08010c0908150403090e06010c0807050606041103010f0b030c 71
    0x214080310845641c84603410b0300b540003485907448100c91400e84d041180d03c0b0000c42101c000a8001849403000b03010400b04028030101130780c44000b000c51403c1c0c0340b00000c00c80c80c1e000003410700030700c02c00380207003901003280d40015089945800360b900280c1c000181095000c401d0f140100e8020f41d07a8511015030ba40803801241c003a0040705c088140c80b0481507a6051445141081b9400150b000b4115001c04155141c041c4070b44a41d15001d201c4001e51589040707a000c4824000400010000710141a0640d1164000c0c8041845018000d05e4104590444000d101d0360440c00c03c902ca6119045980c0481180068503810384c1ea010307000007803000c80d0020b050650030f25a0103038507641d201c4c1c0075408989903c0d00712009103103205040390b5840404d84010700000c000517014810501c0348400c0390303080314040c5016801c249454480c440c640c0c0260500b00c0d0941c0192003845104d2610f8000c06030300c339020792000d520359450903401000480b07140c415140100341c0840041da454682c0419200420103e10700d5 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 628547266 1250 628546016 628546019
    0x70e0102161e0806190911060c150a02070f060f0b1e09250c051c0c0501140c0d0b040e0319020d0f02030702010804060b0d1220070608040f0b01 63
    0x4080c00c2191802c400c00d58035000c40000071210f0001543c2d50281004c13112900b4030700310b05c21814029056010003503c0038034203489003007003030784407000140328400324180a8510030365240040e25032400046c02d500107aa0040c0b01ea007005c2100307103080000c0290301800008107464040354503805404460001d5921408030ba209121400340e441c2200142201207603500e0b035541d95110381c1105070149100c5014566811041040414052940c110019001c1c000b12600103481d002500c0700b890040e00c6540008010b82c000d13000b00700c401d00450384c4c1054001045075180ca05080c100c10309000b0700100481041d140c02c8808050348450b40a003102c514440b0a49a40c0e01c2000d8a5400c0c40f000011a8401417103400c81c6210f000d8498104108005103c0d0701440c07500d09580c00444603c400603000f55000c0781ea51011549640c0c032000d080d520725201d4084800c240c0c184e480003130040881d8480b803005544591451650240c4003144280680714075042c50501501c55081150340034a408000130404800d2000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 628548516 1250 628547266 628547279
    0x20c0607020f1e03100501080a32030a1409031b0d0b0405030702030d020706021207060b0d150605030d090b0307020708060403120c0c030f031d011e060e01030209070e010216 76
    0x42c0b003007843d10540460380902d4a4802500803100709200e02081d98100400ca90f0014100ba40101d03d03c200c501040e0301c00110068100c68101031041040d409980300142c520405d903001500c000719602c82800702c5040c030080c00040303038985d03140c0c500345038031910031080800f501d0341c1d581c81900c1502e4108010f06403a2402d0b280c802d949a0284900741d00c40c0c41703031705e40304a40d42d4400503030712003a1040c80e40501202d03d0b265442002d01c1d00280707400c5a83c90740392210b061a40c0c1b102a810a44a0702560340e043c0c010f80300007140021200182c05c002d0090700303d00704140ca440c1c4c00400000484403008103407a90b950350309108a00346142c3d80c01020290042c0001c0c407050581c004500c11030708212480400034400100310544202d03c1d20080100410300d0b545c220f1418501a611a03501e9480c622241d91058410448543c21502e02801071841a103d511001703142021901c035900141075036420040b11035040d170300080d01941d001025007040200300d059140c081d07482800303000c010340e06941005031031549480 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 628549766 1250 628548516 628548559
    0xa06050406060e01080d1407020405070c020909191e0c0303050c01060905130201050a020a05060109090b06040603081e0d050114030d03110306040b030304080a060c021606020c0607020f 81
    0xd03426111981441e00114940c1d142400c418101c4038410018581044800410303074030445018022141003106108003800761300c40c0d0140901c0741d911303035803203c02c041c0ea0703031041203071104000d040000c040e800700b609404241c520300542032502d904091458003007215591401c4040700800402002400c5d0500000209034008006d403042800b890000d02005854013096801c440c0102c03440c2580c2c40780c481c0d080000d0350180004002000a610640e250545180c07105442c08200780d0005203460341e250502d00034003201c42e20464004404440c2400640d15503203806210780940d1803c100c0b076240c0d81c200c0c0c06041c5c80c034104035030003030086103414021756940d1200d5104c001800203400380a4040d4008000c078039480f80c41144641040843c4250454486400780001014003020a5406210801011440d81e070200300d00307460140301f600045220090441c00900f00807540040a100358600e550520042c0e80110711001500401d840490702d42c40c5a000281c982c5042407105d5800c04400100942c402c00c512 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 628551016 1250 628549766 628549771
    0x173c0f010203012c0a0f020705060f070e0d02212b08010501170c030702010b0306101418041e02190801110c060f0628140a03052104080a0605 62
    0x164064011180404501504c00d0a50031000461a030f0801c0090140d2020b0b070f0040607400029a801400c01e80ea503901c0c1441c0030b100b40c803500103a4140e00300f04030301144c0c4045213080c885020303100740030081c4007680415030500d103001080c6c00c0c24109605803851020100a00245421842e40c00708058500c1c0000b41403107920fa00c0d40342e0005003001c1c0003003090350186034400d18140168441043c680e65526000001e600042d01c03010442d502c0e10601c0d1101d41c4c0820010380121818203001c08038500d40240700d002c0c00b58031003045010306001013010ba204030301d0724001a4400e070001891911600c0c09550362500c80650540294448000a510f5917092406405d980558050400820280990841c0c1001038080c03282a00495407100300018101124684429048500a002d00b00c06480da40442d070364460031b060b410805002c1c00c0b40c00304240b06029510b20b040910aa030713501c06850a50b110941c5540c04e060f2031000350440c40783c400004041602c212001440d0b03880a403444a04240b60842c05800c05 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 628552266 1250 628551016 628551029
    0x1903050c061b160303061e0f0e0103031209031808061e06030d0e03120f0a080615070609020a24090b0c0d0f03060806010f173c0f01020301 61
    0x62400040220010306501024032003504049400d044000050a41c2c0103c0b1110450405441d0301e00000c65460515145442600c1440b1210180b0704000d03940c0c140e880c1039800800710102c1e480040000c240c10100e076030b440389800304010403d0102800d081d102d10924003c82d1380350340c400c54000a01c4400c0425198005e401c1400d40b81003280b01060305e5981c0040035205994150008180320ba03c00340a65814140182e000d01990b411401802100580390460652a6640d8900080c2c45800786d40c0902aa540300904560010102c3c280c1850600d00d4001c5000044c005c0d0341d946546015540c40e0441e1130300400a05105078406500004080040b011400c0b542d070210345400f002003520740380b560075941c41309482c00080141d00c00e00442120104080034030f08007896654600821b00c244144992800303407170940e45c480c0466103042e0381d8840014640310742c1001a041783e0700c01c03809400e00e900300c41032540c600c0e0301c1c00800d03041c04100e4140036086440c0c8107200c0e100308800e203141c84030306401440c105c600 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 628553516 1250 628552266 628552273
    0x30b03010c021b0d1b030c0806090d080408091305070e191805060604090c020a020108060103050f0105010f1701030c08060c071212020f070605061504120209091903050c 74
    0xc00c0d00181e82d51000003043e00150304040c801c20940d800d184000441c102c0c0a4104580070407542010121000c01d1600262880e902d0450305104841d000c02050b83c225045200801e100b40000c1c1e00100003480c00751005100d811f00080061055417510703031718500f90700e512408105034201048041c080002d0310110702d0050401c100018502846466400c0c2203c401c8000502d180e000d80b024600204002071510703074040d0080c800417030042c51920843c01c901d1080c0c0c0040038000d84078000504a414014111810907041100b003002c0d81d0040240241101c2e003c0c05d0900d04240007050581d20342013882080030a01c02503000000a11611101400c101c82031402a50f000d52501d02c4101c00e544182c080c09804c246500341d144003024843c5a500c00c2c41c801e40c240c01810321000c219951000d50020600341c0d1000d489000b400150302d010340640c1b4549504400301e92615141004e5440300481e0220b01074852407514000980c83e44d01407040c4c0600c40706103c01c50302010054680a80f0a412000446010780b1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 628554766 1250 628553516 628553531
    0x9140117011109060309070305071d0f061c030201110f040e0702010506090103030e0f040507030b040b030102040f05040b040e07180b0406050108010b07061104080705040e0102160b0406020f0a030b0301 88
    0x401031040e52540c41c184212640b620f01c800003030240a40c00078145c00d803d40b02d80500040440c10a1200902904401d0900504a5074180c04050f007440041c1100b5000040d5105100d07490ba603202004440da1b00107959500384c0126814107034010851003922400b24000021802519085c400c0100151900000f113580341c3d0300c81680c204d0032074a04403803640e00700001d1001800441d005114a0000440c02004080108950305c0820159101070b500350000c00e490b0403803420b083c501401120720200058000b10b041c280340400384401c04100d481140d0190790b0319080030300c040d00c841e04010701018a4208858a456851074940782a821a20030460341c50f20342181c141161406000d600704683c01650303605916403c01c2141c6100742d1091408503541513950954200c07001c602e0000c0c0c0010807048003d0480c0750301d0502440b09031455180e001245906c108801420b0750521600701100d250082c000c0701c004d83c0c491038450002e1050040040006c6008561070568a50681081c03850601c142c0003840003c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 628556016 1250 628554766 628554809
    0x240815010f05061c02040305011103010501020c0108070f030209030304091503050709090c1505070f061509021e070507080109050d090503010e0601180f0603050f070807150315091401 80
    0x100e40c1c0d000d02d940c0600e0411424049103c0c440ea08843d14040c00401480d0590f2076440c10700f110060305410717a0b4075501100411144d0780500a0f401d040601382800c03001864107020081903e00c0c580c1004061540c00f2680f1a2252420020390f0050034200e03008100c0b900100107030300038030095071000310703594415100c02292100c0350380512103010358807100180c00700303007098480d84000d0a01840b03002089014090000413880c6200f685050300d010702800198200060b07880804902160442c422040c01088028a40e0303c000911008410081484075201c40d103d180003810401c031a40101e40640c2402c03906c500b0700802003440420490b20b40c8500c111565181d042c1400e175002c00c4c907092a5038000b40010403125400035007042c00250121000650707802d40040701d80c1221055081a5250703801605541d01c6820708000c054050f0902100401401c1e1401c415a071705c40401c60f40b181c080644425154180d202503d2070301029020340c0a003400f03103040c280d40c0700700380c1c0800b4411408410300030310b40708052 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 628557266 1250 628556016 628556039
    0x21090c0605190c020d0b2401050703120506010203040e07080f06120c010c08130303030917030f040311070312020606012a0605220807051005010f0924081501 69
    0x66504100402d00e611001d407800d4904129102d401d90700030b0228038010380028500c4001070b1148441c40e241c102c000540954803a03d610100b0b0009041c000704000600100383c0141401c0c441d50038090b80400e0a685110040341140500d602002c0d500200c403003030050190300262a984121076404a0140690fa04c60130040c00c010111010401d9070050040f070f88255101302c10901d406405031429030b241c01404030310403101b420a13030300550010703981e40011010001d5050a600361540c03078000d82030860a1070609102c0e8040050310060501908109001c43d8141c18000b41c4000c40d006003c84500c4982c1d100060749580b01152204d000640c4000002c11848103030f2003141c45400300000801c81300308240c3d02c8a00410024042c0a20715841d41000521121108580c2e025544a400040e0b10fa44003450043e05e089035501c001c15515043c48014816080b04001030800c40d0607044021958200d08079540090280640c001502d1190280000c200c83d00006076143c4003c1c1d43d2150051a681c2e0356104c10310 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 628558516 1250 628557266 628557277
    0xf0a1104152f0a020102070b090603062b0606050906040c0f0e0103090b090313170606042c0d120e060c07240b0f0f090a050721090c0605 60
    0x1400d800140d00c000195110309200902d400c0c54014641000d84040c0b0340d80001c10002e0b081c03880561248a19108550b41408010010711520380c0e401c0c00e011821001030074600006190a01031f90321800340a80440b9100440d130440700001039080c0580c80c41d8204400644800d0081034018844e1001180490a00e44940c0d03006d0207a50355118604000f012048440c00354203d60300e4109a01d131a00303203000c9952410f00601402d9228010355032450910300c1881e5101c0c2c0c0340d0010501e07100203400d4650107540450503540c0440100c83c000f8402406030400b08420301407004030040b00700b400a60b40c0030a140080c180024880c0c944030341c42c0c4bd1b41c0c0001907030103491356070302586210781003200410f1090102501505000307100c0c1a01a503565490500d0914014078015051855031311841c0401e00c82c1090f0f101c04004110980c0c13043c44041c0828042500b08801421000e0500e07601d02c00210040d10031452000c00b01803d69040c15200c201c180144044d00020314207580011180c807000078a0350081f4115032 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 628559766 1250 628558516 628558529
    0x117030c0c0909150a0f0b010915030c0c1208091b0a030f02311a030a0b0a110a0203030604060905040f08030907210507061823090f0a1104 61
    0xa9036034141d8050007401c61000d400528a4401c080c0e00180d030410340c95041d0721401c41c01c0c600088280c0d01c0d01d140000e40340070500b2a070501103070060501040c0089601e48200c40701d06d04020504092410046802d040815409800e8209280c00300084503441410f01e405080078504a5a2881304d0300c07801c00b2116481400103238860084102000015681c036524103040c0e000900c41086452080a00014200098403205480c1d03074040d005d034006c1c0c00318131540b000d036001200000200c0c001d24021075618201c44201420340246e15001502c25503c6810091500344215041c5032200020200656203400c1501c0e568440c40c00d01c44045103003242882040c0c841c0e5040f10880401500c6519035000c07652001c2d143d0324442c041c2d058045480c4210b401c245078518452420500c030003565041c85410040d00c0d40100e410440410303c1542260108918841552007420088a005001846007840540780c0d1001940101d100300c100412000100c00c901c1c421840a132051140d2104031a00d0461840380780241d4 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 628561016 1250 628559766 628559773
    0x903060a1b03110712021509150f10090c050d0501120302251d0403031b0801060f1b0b0619050d030305071b050706030c0201110409150f0e0117030c 65
    0x3441840c4603412400c2d502d44a540c0d400e140c250b04e1745800102c0303149200500c0c05640302c4110707070303a13035003147d441503640700d50284081d00c101c80c26611800c86260001d04038407100303a21000490400e000e00c42845004103418402041564030446026020360083c2c01600e0200e46451b00000f080c1608a07018408160306a01412003000a180f18110b00d4100c001c59001c078040d2007902007450309540500b0b61910b800c4072070403031030751420b86401002d4840b25a0202080d01650b080f500342150809031003415100141482c1a180005040485d0303654803045a8000d00754002c0c0790748007400301c08040103004810903035030641c3c01c3c025890510065202446599000010300c501038001c6031083c3c0c030454100d400c619104c030b61500c003910001942c80307007004160754031741090307608202181c2c252160300401002c0d40000d00142c000e0b204404224022840f40f04800c5455100b1140c0c600f400170f40780c02c0074083e191f0622401588544440500d0f040c02d000e18000c075100306110342800000001078408185204009 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 628562266 1250 628561016 628561061
    0x70b0103080f0706020c032521050d15060e06040b0304081b061501230f0705120307031a0a0e04060e070b18030706111b0a050a08030903060a 62
    0x1407045550288805007201c0b0b600b406484000f8650740010144071000c07000460700c0e1003c0003010307144000d410110036071461468031082d0005103045000c101d14400c2e465514807482d04074100365800e00c50b844400300d416140c42d0f40d56001400c401c0c082c4080d24015a1084070b2130800d0010f100241c45107015011040c2401d000040005401000501000c22110311200c100c140f19075420345040c0059916600f00c1101d0b0b40300b40c2540d41d002c04422207821030b4081291007a8107a080300b05851217038121103200394030000344420500400300001e950038008240c18a5980c17600c010300500405200700c5902c2d8509014108111920380205800281c0741000090b420a840d542d80d8040180b8640b0086511070107074043c001500c0081801501125045451140c40705100340304240c10018183c01140c1840300e40030280c201030000090125049003941c1030b5825001c1c0540001c1d18410396540401d620402c14000803d1400002c0080e00c0840300c01d0f006c80d82141ca80ba03070000182c4103866a41c91201001850 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 628563516 1250 628562266 628562273
    0x1020a0314010f03031d0319062004050a030303020d02130b030108070816140109030606260105040803040807032102180a0b0a0c030302091f110c010906270e06030f0102070b0103 78
    0x61034007000038010708450140340f46640c4403100c2200c06c1c005440f0250740e800c1d00960b01500700c038401054ad142000003032a2608000000714031a140e8003002d030800d60b012920844400d140c3c1d044400c0d91805409544645503900f450b04c0d110340c0300b4026100782c0d00a8a000007054400002c0100401c580c4d094120030a50070086030b090000702d400b481c030b410400540400000308840e03106600c050008542490b41c0b00e0030f115034920308044038205060082e0b140404001c08144500c098a03001030b070050006076901000d09080358090039400c0c074110400310703009025110a40726030051000c5002d0094141e162108507007085189030107407069000d459405c0100400746d600c50040c049286102e803c006061802c0b00010801c550011071503403200205030903c0f941c1040c1c000180b1145200800c0083c402c20034000002889a0001d1081e60140607034400007588807100982010041480c0344451011070350b503040007008240081c0c0300f5070b009015600c04408100010700840b0b003e1604104514034136440c598 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 628564766 1250 628563516 628563557
    0x60c0f05041a0313170a030b0a0b0d0b120303150a1d01030605071101050a02090108060a1409040303060e041209080a050a080903120703030f0510051804060b0301020a0314010f0303 79
    0x904d10441410140711440004d60240c4c2005055000210440c0d25840504805000c6500400c1142d1280e01350000400c80c000c8101c08a13000040d03002800f01310600c0460200f0030002c000454012140008020429202d00340844005400340884440302408c0d901d090401c0f510410300d944d8610b22503184014400700c0c03803d400c074507040a501d2510300240360401c58090708599003924030b0300e041900080c00c03403429a400524180c1041c0d044805a54540ca404117449d070440c1c6905295004c1c01095000409050103540540e00902e81e102e400e14071407038180350006e004c3d03800c03212b5940800c2a101d030105501400040903008a58868010020350341c05441d84501764205007241d44c0d00d4800c41c0140c42d641c00040d4090100107200b40c41c003040d1142001101c00541ea40102944142102d0300d00c20170031070340c504a16441640c1446101e000302c2d00c1c2c0d41004c102600400d195550036600000d02d0302c082301d5240d0310004075080d100d040000c1030390325100881d0740c0960a00c40500003c41c0c070300c0000a0040070700d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 628566016 1250 628564766 628564771
    0xa0e0105100f180b0912010b060313080f0304061506051c02032518050405151309060203130c120302280203071d1003080a120612060c0f05041a03 64
    0x241482585000c003000ca01d000f82c010754228609082001c1840600f60904440641d010310402000780451900000412443c0c0401031602c0d1126007188050003d024144085440303405040b03038104d0b0340e407400d420000040c22400e03598a1040111680004803e40308200380c4039500d079601040351011211843e903602a410103807190f000a050000032280c11102800c00d0341141d1800d80381c0e60f40c0f191b50b1181c0e0f400082d440383d220900590500d4200b00584192462122030500304858212001105001040c000e105126001740b1540c400428051000742141d0266102441100000300ea50b8951120181c03100c0ca1400080159020b44a06256030800c05602c08410410003060840c03801281c0010f454102d0640c09441c039100001050788180621445080e8412800d8120000e8103185558086051045605003010007040ca42644600b0885811000051500c011800c16180783e600300301c002404400043c2d404200c4040300d21000030f001b82c041d541121750100303403643d04a1401078900b9403035100 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 628567266 1250 628566016 628566047
    0x1810060312110f0712140f060109021b0601060225050f06030921040504050c21060613030503120f22060b040903020c0918030d021b03040803090a0e010510 68
    0x1410058440f00d14100700d418010140941442403040d546d04202012000050240545070405121048480740004410b41103c20140005940d04560102c0400300c81082d142c10a05004440c00040c3d551360014074105e820380c0148080a881c03904602480343c1800c0c0344a8241c100c110900071002a10700f01014582c07010503403040c0c0e0340203001d41c6006241c13017400d60340f0b0200c54800894180320505080c42026481f6414550451a101c040c10104ae4032030303500e80304044800c48280000d2a02d403078480c2500d0582030f544840090480d141d02d041901c0307400240132118400d081c41c1c00250041540d02d0f00c1070040b01000c0c40388542803600820021484018142a114152070780c10351181ea49851141c2c15410b40254040c00c017108401c000c2049004015000700f81080302000f0404055502004942c8040d006050050f6110120002e803640143c403074043c0001d601000c02c000450040200052010b100b04445282d000380d103e2900454404080c000d02d5000303142c0c0e40414640c0c9000340c1c40402c07490030 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 628568516 1250 628567266 628567273
    0x10c1803061532090606030a09020a051005041802270102120c0c2416110a0303090602070602011503080306040f020f0408010b0607120c03050705010203181006031211 73
    0x884080a9031400c6440120440030303030381940d0b0004080c07540507100f00b070300100b16100d07082c500300750000405a020141a400c5015901d0080b00c00b1550307080d107840c0080101525608660204c0c07030000c0c14940107842142240001403030341c90003501483c8202c84001407a8502104035007000076509604210b00f24816044d1301c1075550b04640141d001001d00b40307081d120002480b0151070070003806414640e003001050f4020340240d01101000241003a25585400040c684400d20f21070306003454a000c0202d03025070000345c2d0040100506030f06c803243c0d10580c1c825800321362450b46d49000480c229182c20b1041030000509070010301c00540c094005541180b8001c1000c40d04a4000c206142207074401d421032003500c4000242007100520a004600d030461040390018101442a04da502404c0d8081c80c00d4010000d80c4a40d035020103004034240d410700d50700038008640784d1400c18603403289104c807180c40381d03a02d22800c000003c000c00e007406440103990340107a2104034400707000c0058542c080180c1d2542280e00 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 628569766 1250 628568516 628568519
    0x132306061c0209190914010f0b092101020a081003083106210207050d0c050f0313030213021e030903160c030209090604030f050906070b07080702010c18030615 70
    0x6854078079045812070203404c068441c500d003042c1d050455490329540150030b90200010410111079048080840e8103800602c3e54500700305000488650400544615400d80c01440440c03994056000d8114200c039034503200d00350f486051f201a8040f402c0d00c80100350280410a01504007008803610003481d043c0d40f100c481c8100c0c603030000341800031190072070b00c0010040780491008100444030402c002c14454401c40c40c29401c1e403110b640740d80d904158601440358260404081160800416075200c80314820342c1d07169140041c07141c000c20380c0c92009910410b201c1c0c00d071407805031141c8201c41e15010400340040e01004402607039005600b0007031083d01d15010074440f0035100010311040c0c9800a01c100c41102d131890940c0704110403d0400b61840271141e00080030000042c0e000314065490319024100141c079800c1c1d0360001442441020401080c0c8207040d014040c1c030070780000d985402041203400a1225400500044410741d400e03a034200c3d005118040d0810102e4402e5000402214944e9004040107 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 628571016 1250 628569766 628569769
    0x604060221041202160501052203200f010f0206070e0f0a0e190606080106081b1207020615150c0a06020c030a27090b0f132306061c0209 60
    0x70401220252000c95288951100303c503410300c02c84500d003c04036121075000d403d0400007840c47c0901103100c001c18040c6990509041e210803d040000c40e8001407204c44442c0c5208a07032040860203009a0040100030441e941c0d541c0144400c440c0e9446030f40c000c101660791100119149112104680d8101d001c2c0140c0f8039080c6c880f4050325002d04200c003503001d403074100440c52032058951a007082c00501c1c5803000030b01400740d02c011841d04440705440c0014035a2240301c3d50218403001c50180741540d1000284407114258410011742c441c81c0c854081c4c03203ca59658142c94403030403003160074036440419a0164104c42c1c00e00b401400ca0751480c00111030280301d855454400700e0b030103070104403010341c804102c2c2d50300b541d4030007c1c1902e442e005102c0f01505011138002000043c00718054030080c030ba10b0310b100224584070f440c1c5545a40d80300600009541a03400003280007031520791091740e10344030000f003c0a040032842e145903004e000050819844c0c00c003083c0c0e00e00c02c0e61540001c00040030303400b0005007185 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 628572266 1250 628571016 628571077
    0x140a0e040f061a040303230a200328080f011a0903070f0503060a0c090902030a150f050f03120d0c02100903080a14060d030e040e0a080706050705030906040602 70
    0x24903c24907a080d640b1401c508001d010b0a410303001c000040702c41c6104030b03d0003201d03d4041c0d1704a144141094001d52065000322410039050b0300c8120b07004d21000c81d1844c0c00c0c04040d2840c0030066000813050800080500e02207508080440d5002c95420b8076400400c01040440442c102d0010801e4803541400541c0f00082d0400e203242d030106070f4102a819040c46149002d2102c26085040c0c0b05040000200300e8901602c214640c1c070441080660100024000b9884c0307401c4141050f12506240780c4550b16051a044548103600501d40a0782242240c0d03201c0d401c000502c02c180e109441e007602d0800011800d4500906506003a610031401040100500000140258480369100380ca82482610f07188601c40200ca03014040300d40440311280c10b0003425140c50120b4403040d034252405034030300241c0398013180c05031028280b01c80c1c0c107100c0c00c1004020302081d840a001603a1059000380980d4403071034801c0384c4a0006440c5c80c01e580c1c20113004a0000760969006000b0b0038032405030040240007031740342a0b14 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 628573516 1250 628572266 628572299
    0x1701020f0d02092b031b020409030305090105070309050c060307090302030307050a060f0504030e0f06040f1410050a081f0902120f060108090a0605040c12080a140a0e040f06 76
    0x207800b500401c100e6414513100c00d44040c3ca60710580000d09020000480b403000d6080e162014080c03100102c074001c1602c1243c0e40711101d46401400601c280700c9949401030040000b00e99050455180c00f01250080c0c0c400d028081c0310a801c04000c01d11084840b040048a03880078050034244034152800000585082c03011704101d038040c0000e44030407092828200c0c16904110708051206107404100000a500146a841c0c401029985041940740010106055220f81e800c485c0300500785500000b80d080780041200f5280005940d00c10302640c042800381c80500580e1450b90108046d5400240c113641010141d07058803c0000c000c000b032540c3c944170801264800c09651203400000010007011512184029420034400e281c03d0305146031a001b0180c813644500c1c0000c00d01500d070300c046028010303d0044600a400461404645101d4618043e45250f22114428001c1070500c0b04550305001c01e2001e41d01c080d0156201c1e0390001200c2c00400c0001c0c40000110780c1d40c40d0741c4130b40c0070840ca49990309100c0d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 628574766 1250 628573516 628573537
    0x10207080304180b120f030307030605010525110306090f07051912030306150305011706040803010b07020f09092103010501080403030908071a0109060b041a13120803010e0a0e071701020f 82
    0x48d582d040c42c000090a89000350045070503c038042000c1004070b086d401640b03400340b107000e024048042c003d10b030109101521005030b5038984544828021a14004515540410201400c6402242c1d440301484442c00a0600405501d03028800810680740c1d0b01c0940705079640700c1d190001e8a07a40f600c20358501908950200c000081d80c5900502440110085030380011a03202c0040c529498540d40300d4a10b4407050207000c800b000c0c045410001c5440340311554481d184000c00000c1c075440d00207010359890510385a12100748001a040c0c880418041080381d0680300103a551350741c2c55540e900c0540c00b0f000345040449501d8170400904011a803407800041849441c111000515450100b00d282564540c2d0421160107800700003c00486902d4a034201c0007145103200252583c1c08803a0036868480c02e41d22000724112088030000c1000301c01c1009606071341100202c00302544500880004480d02804444516440a11b051209a82000c0c0d11944003a403000007602e400c01100c11130170184c01148003403 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 628576016 1250 628574766 628574773
    0xc020d033b0405011202150904020c030d2004032015030a0902190e041e12020307020301050109060e070c051f0b03060708060d0b04030507060218010207080304180b120f 74
    0x1200710b454940030345030050110f1400c40c2c1d203413807254000441c54103034030320742030740d000300c00100190141c8440c1c0580d5410351184007a280c42c2c4a60150307090160031403241c02c140705050701c440d030301202e0701d004180e405981d0880d4082c207403200303980404040888515880d07a8440c9a00c41d88099140765440214410303c083d20300404c2c031a1607407040c40b440191142c03800c45802d44c400380901c00520b00da2482980590020f02c0201400c00c04510804030040ca2036000c0c1000d20a0359034455041d400000030410244213500030062070381d030b501443c02220418040d214074001c9c61804031340c15038030a1400050550241040d1200402d45481c0d4100700c0d1100c50741d080b402038407100b52911a01d000d0110036400f203441c0c00d040181c1d162100002d20a0b0100386001812000071102190501d40308400b912203482d0321100840d03031380b011080a030500070038034081e40d0b00601c91040c0106c1c1c00600801940c040318550300c2044030940840020501405d00c1d110900d400c5041c51000300f241403c20003409410845130b8015 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 628577266 1250 628576016 628576127
    0x151202070c15020606100203090906060903070608010f090911091801060609080f0705010c020d150914160303021902010c0b010303181410050d180b07030c0c020d03 72
    0x20381099401480d45201b407217102600d51840341c000c07003112a02c00c0c003103903a0a06580e0f4040050f4003402541d10f1150944501440422400e8000002c47e059501e08494450511f6a0341101400d65108007030003400d5032110703d48540241401c500b100c1e0044405610641c06601804c10607086540641c840000035840311000c10011809008103070001880d180036101307880c24400040c0c0410f0a541000303028442ca01e4419051182000c8902420700c5410418010840e02e42080c071095100d21071184141d010305c6014081c2c502c80c104890382282d516801074600a000500100c103001c40940c9c080e8148643c21054800080704400080c0c00385219440358208220720f80d48110112800e0b41200c02c80c05204c0803c65003da94400d0341a40100ca0b41ca0000d40e0b40c8407044642000e8150a0710b90580d808844080008101018810b540b08a0700766908200686110a0840700d950485102941041c0c5c40c0c001d120210348a004800c003104450f5826604441c00c521541038a00c02d42c1203404000701184a5 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 628578516 1250 628577266 628577309
    0x20313060903030b040e01180215130b07020109061b0209090102120406020d0b1503010e04230106050f03012a020f0a05010203011511031c0609020a0809060709151202070c 75
    0x90701b00b0444003a000300460503103803100d10880f040e001e01c043d22503001c0f441481e0701100d20000701d441064140d0700c0d0a000e40d40e1040c0c807141c1900403c4007207001c41c40100700807442a00c1400c0e00c02c000790110000c1c60807050315400340030741e05038042c018000a5400f000032071010002c45401a000f5445180c00590300c06c204c640110440d21452060f40c803031000b0768080250f048200d0141ca064030b50030041d2200d83d4942d8a4004a22044400b146038011318208440c6013410307040d444981114000d45900d041c05400108240c22a07095202100070142002e03d65680380c010036409844195890044031001164403140b94a0503585d410308440303aa40020050041111416001000c1c3c0482d00306886091040c00f4501c3d140e0107200030403201003401040120a0b4a04d0b03801550050010300e80441d0b941c0d0240c0b074001c29054040b6126049031081d8000303c2c030810b1180307143c1300c211610050403020f000801401110007860316854903942c9030b024490207000c2003c4042c00c06c0248801c040c07044583c0c40659 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 628579766 1250 628578516 628578521
    0x50c060418050a05130308100e0c0721200309031f18030f03150b0307020102070c12050304061d0402030c04060206150603011511100c140a020d03020313060903030b04 73
    0x2828054001c3c200405e0003076500c044101888801d5050422406544e2a40e51102844606e0f07446a00150409014000d410445000a100c074500801c2018440c4101c1c00d000071007100102c160700c0024500200d103211142124441002c00d130b0681d4103881c0707800c0400c0300181c580790156540d0440ca0400540b00095401e17a4400c0c94040040300050012a101a4901500c03244540304142d06144d1a08116a0703d000d002c07001002400440d07200319100e00300381c40028000d400091084603001e1302410080362106603101131010180e0301c140107500d0a0b00740071080781ca404040c00b41c4544807058113002101d564407400514450407a035003030036849a2521500901c1c001020707044a030400740700c00b40540c05803200d2084905540741038051065034480078600301c48404501c40c1ca40700f18041c20002c1d038007481894000130301c64002603440c542d003a14501c60025581c0300f44100e94015a001511720011140682c02a40c3d125507400c50700703048401c107a00e451007aa61a818200d0002e070b0786c0d01d4050b0f0700d0b00c0c151 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 628581016 1250 628579766 628579771
    0x80f0c0109060311070606090b10021c05070c0906120b0c07020d11010219060506030d0906020304140a050409030c030201061a040302060706020f0a0903050d03020304031b050c06041805 81
    0x1100105211064000040e140d89420302582040644441c0860012604da004448039035921040400080d6910344441c801400d031002400d20401009071960080751000801100c550485094840e018854401c143d816601041d0101c0d8012050310002400c20b0891044400404070b90801d21450b50759482d10a40d2403100401c880e140c540140001c40268403550082010142d0020b250f0003084411700050345002040e0405005641e21b0b1101c903003c000e44d9410903801070380143c0c00c4803400144107a0950f042007560042d1801a44280002c2050b00c0c0360031080b200b0948081d000081c401d0b02c4030003003401d99103040c87c10b5003c0f6844c3e030540e0003055824440d580c01401d4040701c00c0b6a89013589041f0340a44520320000e84114000704014040c80020350459445007280d00300d09541c0d005082c0c0c040c3c00355099200a0790305015810304010f0a0b070080c0202c0f131040d94503960303044001031074503c1c40b002ca050380c20081d50244902000c6080344c0d210903000b0400340114154085103040c40b20405019101300 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 628582266 1250 628581016 628581043
    0x506100b0c03030730091403030405030d0c1e021b0307050a0902032706042d200307060e0423160c120306030302060601020609070b0705160b0408 64
    0x820105030188800b0042e41d410148a01e003607244611130010342e0b440003c00c1003d42c2120700e0345000480044a56a200e04000b91003985950001c1000c2601c5945070302045a01400380d4104022612074514039900c00f1521086070b007006000d0051400000c0303003030826100c1480150f4031980c1ca0550780300e45c1514806005000b10b00034450581040702094500c60b2030311800b242980c000c03000c11200d0741c610514901c4590f44503064031400341ca0b24040350380c03190305907000c1c3c550501414041010b17050090007030312403d0f0040c2450300c00e005039950b0510760500721000030403954011854106076940c2441002d008204550b104100aa540b0341000101e6100207151040a2403003903150492044810280c0d9210310b644907403900703a003070390501a91500c80c9884002c04030160904c0080b01c1940560001c4192030180d400ca4030315039204001a699110305903040ca0066201c250204605200d01006041041c800c40540b000b100c45015010650241a0800014408040b5003032101c0c43d810171510140940 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 628583516 1250 628582266 628582289
    0x406210912030905070902131802040e04110f150d0605010509030d1803120201090b01120218060f0402032a0f12060f0306070f0909020a1e0201060305060103050610 72
    0x100d95605480d10003040014400c2c562500024000d118080c0020b400a0129400a6540b101280400d03015114240103440c0c0003600504050826036103442031300d040c0d40c00c84281c21119200c98941000c2308044070603042c0e200f00d441c0c000102548411244c481440d210030422901d80c07554100e120300361002034000b68100441401401144d940000c1d10081c04074040c00c003000144080d10b480c040342e00103500701801f10a660301c1390354001c0d0381c154441e21030035000f03c4880d10340d81d80b1032040c0400c1041402001c1c1d8025411a0301d45203070b10707503460115000880200504222901d140100d01660021580f8540207440701e01e4894640c905100b14580c00424078010342d1030240c540c40c1d0b0302c83c00d020b0f050f6601c08103007980c0b000400303549401092210061009040320031600d0f10000082c1082114031174200000c0362803074006502d610600980d2121450380d00c4450f107014000b00502841a4802c9042d41159210301000011400a10031039010718000d40260032580b074121a031101d10307829640002c03004034 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 628584766 1250 628583516 628583531
    0x307111f0c200609040207020f15030714040b0910030618050402210303040605070903021503160f020d080a0204090501030506070f020c1804050a08040b09030f0303150d17040621 78
    0x260f428003142d000342001c071001070315000b1500101d462a11913140040d001801101440c04160461010314440c80302e55440000710005903160b0501b030301a41c460403c1c402020701204400f444c0c90301c8406070110a510300040d44070350721020704200001c241030903200b4070baa480c00d02041d03040034001e41000c20401d01040f030705101e00d44c001701d50b603100043c8041c00450750b43c4040b40d911403041c0a034800a507002045911380f0715081b003078190254020b840b15540c801c4108400b0003010300400c1c0007541c145140e00500314415030100c0c295103081004007101141e91342004080f17043d030098403030b20340a107000300003c00480c90003560203002c150290030440195400144000705aaa40755030044c03012080c0030070f22507a601d49180051070702520520041c41020085000b05482110340f0262825038011000c480c20036024a007026280d1005a407181703821245806808103509002410807a810700c940105880d0b8600c00001070203540094201c0800100c8008810b00c6410400c6e04500480605950410101 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 628586016 1250 628584766 628584769
    0xe09011103010e0702190606090e0606060d0f0e0307030302030103150902030d0e061b0d1b1e02060d060609030605010905070e0f0f03071706070906020307111f0c20 72
    0x140414482c80c905000e619000640c40ca201b030000701c0380d195002c1d000840264092401d0390140c8500d0091003030451070044001d0f20301c080003404030b0080030301500c054502400201c080000e48184c00b10703510440c3d100c0c10700d07047c9140d04000801081d4080c0c0d40060f01c81d411031401c0c000040c000d00449010394100340404016950204110a482000d42009525001e000300403581c107000398030151941001c05002d81d044203c0c08a01007043c00b0441c1c0e03803003d044060400030309003520010000380c03428018181c2c0c0c03a0074001000064222a0005082d9401e1071a15109582a5540c81d000230001039002c071410410000c0307030b018075805010314080038081d038501014024030581d01e5181040c411a00031620240301d850704040c460440340054140c443c802d44a01805035015019041c0b008944100800106101c1c81154520181c03241036000e5850030355240c0350340c00041c048100d20f680c0b000d020710340703001e200302c0c8401e492400d10303604d0701c0d10041030405080032141c43c07500390034110803554080302c90a5036 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 628587266 1250 628586016 628586051
    0x1218070807090c1403040f020f03030c0319050702030f0f1204030b060d020f0d0507180c140c1c08090c060a0c030813050a0803240a050d060b190e0901 66
    0x182d0719003490008212140c1c0c0300c1203640e010490900d600c5010000140028841c400c1500800c0c1703802587c0c10302c0f118140740c09142c0e6030311500e40c0000c070540050044550849000a64220700360180c60450300308103081d00080c0c00c1c81d1412404002c0741d405155805400b071020b20129072030302000f1020b58240f901e0364580d0307101c60200400c017030b1044050b406c8640440d074918880f240710450180401440f070895141c40d0796602c005014a1154000d41c03081003110a4080c019407003d0742c0980d03138000425003040c1c854120f9401042141c1b0041c0245800c052070000c074420320983e45003090350303091654140303901d0981c109900169000d000b68402c001154910740c1102c1400f0a059143c603000c40981d0f64403800c12602264040300510b0ba02401c2c03d060103025002001d14000c09680d207101420000212950002c14152130b54160081c01c0b0705ea04104c94074015000c07400d06070290320040b131340801150000b0319000005095090b6a03080200602c00d40c854100132503400700701040204100c5064620701c0c0c42 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 628588516 1250 628587266 628587269
    0x7031407120f020a05010e030a030f020301050d0308090c040504210f0203030c13090603030c020a090603021c290901061e09021605010606030209041404171305061218070807 76
    0x203001404100c050030b03e01c00c2111100c1c0d182c0000081048a12203081c8580700c0d8441d240d010002804c110102107400b406100300c0b4100c54008000e10807000b520394040d50500d000404418460042e5008a103550322140a403504c02d41c42844400c80a11020a0701c4010380704400c180020044405003c41c9444c0d000412203820000d20134119841e40100a0b024106007003937000005650f0401c1000000c00d504040c058594602c01c449100072540c44210300822114184006076005050003240350340c803142d40c5556059980a408188407100b000c24400903003c1030040c900f918040c00c202000000b8000303101e80d0019000040c1e0403a640d92004547c0c0d010381606000e050986540001c82c2110302c09003042e0643d416911000a11003540d032001c014009400118030240928104000d40f540e0783c840000c4180308592114651900c0c140d18550344a03103400c120f4000d500202c180d40c2c0031075141d0b100f00103098000080c85290a03103141903100039811001004031151298088001800491000b040200 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 628589766 1250 628588516 628588553
    0x50c09032802030f0102041a12011a0702100c060506010c051f0213060815010f0c11030f0f0c041406130e030f07050d0206090303010609120501110a0507031407 70
    0x540040012005052914400300082d418132520941000e0110113402030021034565030f07000418000c040080802e1485a0348110800e0190300d00103002c64844a0510001d080610140509150556002c18410031103184031a021170385a10320407040101074003807258801c0702071820b07034440c2c5002e51302e469444040282004540038680c404601860899055850084030741c503001d101666249005000c0315010b44004d42d10311202800c3c1441c81d4050300320401052120b503a80c1e00403807069203036072000d480f003d1005603240c080d10510300c01d01001003040c4001040c00e4009022a101070f802040201c521540244007441a440c04003d1603656001c0c004441f00e100e2800811000c2d01200601d056218440f400c6000c1100458944240180054000203543c429000c4401d952035035800c007035490009104180c00550984024061f00c4045225100b9051061002044500c030400c210303509500003400540c0040c4022550700c0501d90312200c407069400004c104686085155201c0c450040b0300810785c031 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 628591016 1250 628589766 628589803
    0xe030f03060414010e070f020303010e0a0c111006050f03010c0906080406020c240a0515100c0203150412080103030507030e0f030601090204080f0102090f090714070c0504050c0903 79
    0x2500740e00e56400500d80c4541c0c4007101d00d015a180c0050b0304c0c0c021029100d000010715102003028200d8000800c40c0d0680b4800d00b0b44100940d039401019000d0500e13502c1420800080700c130b82c4a07400404010980c6c0ba002011404a075142c18041404548a00780102034032136810f0020450070710b90402d5002c020782e822468030400c01d070f4844c1011000b0388a01080e00c07181e071040c40300300121aa501140540303c40d000418400c5a6102c0383c0702c01c0c00303540c0c05a402c0044881c20a05500c4140b801c4041d5500741e0354079050800d905241600028248540388000d01c0300c00702d08504010400c0000321000e004120a41030410080d411520002d1403030182e0300d002002e02c104207034030001039981ca170343d40040303410001c0403503c0c55038692540307002a41192141070810301c1140c0a1007001c60042c000d50705504405030508202c043d05100300062144040d1140c02880f20130003955003131420420003803010a02a03403050604d07501c0d1100307000032204010000e880b00401485400109c3e907000c00c41009421165109 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 628592266 1250 628591016 628591021
    0x506040308070c150c150e0706081f0b0a020f06090705041116050f0601060e030c060a170a090b01061b06050702190b010503070b07020109381201090e030f03 69
    0x16030301d44420341c206850130110210700c000050b902400d01600c1c5480f610410350040003c0700c1100c142c40b288943c000c090382041c030007031140c1840b80703442170b500c904107004810160030801000024a415074200700c1d10401e00040021301650104412030b205a0014001d00c42c03403030400e00440c2c0b030b60308a00030284181c0e280d008640802142030255a1280000c4400c0c145044c1d81c1d20b03003c0c6e66400307d040c4000e41e90103200c000140d224050b03905011880809805002d104002c0c1d0104801540000c00d41c0c42130200c0620030000b211032500d5400d114503a501000a00764000d42444110104164400420000300d44600703100e5010b0b00c1c8113100c00944c081c201041345d440707400040e428805505030305042c40d2003100056050140c40501c06040361400d81c156020301c1d454035031040c0345100b07401001e0301140a40724200311080000ca2200007844040d04006d82094a1a29003040518a003090354020340002c030307054090060b40741c00c450041c00d440000f0070126180351070107a168022030102d04c40c010f201100 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 628593516 1250 628592266 628592273
    0xb061b2401120f06020a080a06080f030d052a12010f0b041e03021c060f0e0a03081e07030f0b12190303110301150f02030306013f0605030f0106050604030807 69
    0x311883d40b5502040545d01c1e00c0b8880001017003000110344410f50035041400010310110003041c4980822940c1d0091854003902c2d0078060068130000d020180c040b0800701041c1034120524003036924a2840300b4409503140ea004445440f10141038000400c80d400030901040100042000c48080765909641c101c040c0c142e204108224208aa1000e50440d200508e81c4850713210401a00300300501ca1201040750b051508030307040486055803103140380c0d980202c0d07220b40032170b000300b0761300d58840162211704981c403031031130350403840030710151015008603444220b00940e0380783c98040c807a075203402520390500f026035030300c03080d0756a100000e41ca8100d1850340d981c0b8410f043c400d4000b40d0540f2001c6020f0780ea203582d02e056a010a5844890140001e0031806405540a1010040300d004d410140e60708041d8820581d642500381a4001710821030a03210f44002011070021002c2d42c03e40e8030f66100000d013051504040c5070616002608100e0641d2400b4018040d5540d5441502e041c0ca800040c0316403242924034 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 628594766 1250 628593516 628593533
    0x909030c10050105031006030b151309111c0213020d0e1c0905030d050906180d0c080601050307030209042607080a0e060708030403030e010b061b240112 67
    0x11003040340100c070300d08504418079810490484d5825003c4070861906120014129007076800000c05a04c0d5070302c04600016840315a211444000900d900c210380700c0740c030f042000ca522401080703422840d0031142100c6803500100e01281c07840b41c6140d840d200d066a0340020244001c200038006110782c0440c104168407a6984809101400c1d007007251645034541104501e58400d6045600004060300341c003040a05001c11514040380d903d8466600f0301e81007000300409500120b0101e200840080303c10070141e901c082c5030344013050152880d031404900b000002d03070400303005811203030290740040c0f01000142c50b48603078a50b005420681104820740180103025100c04208000d00d02c013000456800140002c0ca0020f20480c00d0546480d490060840b081c04042c1c050303280003a00030f60040c400a000b282c0aa0000042d088920740001a03211468001410681205145039040d0a020b85500e00b07900040141038030b0f801000007603e0308101d02108a2406c42014000c81050720003d950306420800d5a5 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 628596016 1250 628594766 628594777
    0x3020906130e0a083109020901031b05090a1710020c15070807170112140a0c09020c01050109021207110f06010929091308070206040609030b0708060a05090903 70
    0x1050350101e0985007004d054a8100c01c04400840802d504006051070407000d0f40442e0048010b8004085443c10b41c19170020b4210380e4545060640f10340110111304010001903180c90070503182c03903845001413814840c50300d926401032104414690b4903030580e09400514000c1480d54000056910140141458203004600460551070400f01051014035034020140307620524441c0c2d9401076080a508089803982020b2281e000d840b2407030310842011841c04044481c03030501803004ca13580d002070707991041171300751255018410f0070350b0200e44009005004c0c00740034010006494158104a180203001007001d502925200500161004000c0c9031070b814041c4240c14219503003070303940b41e40c0c1d20b42e140405004a1100c100040200320706203035a0440d6410788440300d0344060002201e940c0c0302c0e40680044207042a003035540840030304c108001030382c42000600180036107655460000d032440c5001c024600b005131054082c061080308000701c03034481d0711101c81181c1e8111071000540e120001940c0c107502c40c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 628597122 1106 628596016 628596041
    0x70206040b0430030213050102032a151003020f0909120c0102071e0b180d1d10031a0105040b0d09051c020a0204050609010302090613 59
    0x9010644048440720f02c034103241c101000941c420f0180c5400350b054006a00000c1c000b1521000110210040c07801b23000030b40c20300030003014843c0e02e01c8003200b0b8103d803103003d070a04070f0ba01d41c000c21000c052154204c0d001c031100d0400200030661521a0702040c0d01a81e071040c40d14442c0d041c865612441040b858016111082c282001c1d05603503030200e44101a15034017800141d010840c143c00d068192140b00e00101401d81441c900b0714030600c0c00401c140b070299030039009103c1618020905e4051543c9528200640c400d0394135403e41c0d2a85041c0c40141c00c17420b820281e40c0000d4044e88214042d06e43c018801411b420010b004540710320560040402038101031002c002591002c1e003040e8401407107038081c2c0714030075034194034145030700b90704410240107030b0203d0840c4007903080a10460303401c140c0c15100040e281d070554000c51480b41c00079006e580200c8100c0340303c000141c2c0c0b0758400c1c8005442e = true := by decide +kernel

theorem cover : BRFrame.Cov 628417266 628597122 := by
  have h0 := BRFrame.cov_init 628417266
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628417266 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 628417266 ≤ n) (h2 : n < 628597122) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
