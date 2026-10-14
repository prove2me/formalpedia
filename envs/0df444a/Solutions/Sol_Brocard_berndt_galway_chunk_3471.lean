-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3471
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:45:41.014156+00:00
-- url     : https://prove2.me/submissions/949ac775-9cc2-4dff-8004-392815b194f4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 624100719 ≤ n < 624280575 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 624101969 1250 624100719 624100739
    0x310021e030a0914010b010e120a02040f050901061e060c0203070e0f06010e0111060411060c01050103051b030703030905300d120204120f0507080607110615180c04050406 75
    0x40d10041321410070190241d0201c0704117008400f02650305840e414000840b01c030501c4550b800010124109005203e0001d0041e5124454038200c08540200040c461400d110355a003120301981003001d030300d00c0e0a0022188050703641d0118081e14900d28060540d1036040c804207140014507006500b03202000300070031280308107038601c0a00c90142644c0d26100001284010b55440c1c09410104040d900403800060102d00c8061000080d0000a00560300d8454800301c441e084460a8004a40c07a40025260044009a6a05519040304102c1c05403046e0361440c2d0b40504220b10502c109400390985c06011454074000c07460006d100122030440f0f00c544065805c4071516601d0300d1100d000828003e803800407180301c071031080e9415940c1c060701034000440349449500d107440c210441141c0b039100d00c1c00041440e0809000781c500882468483c0900460394a410747e08040000b003035480d04800d0160b5100007541c8020281009806407a8101c25039220310565014620864006c150801d0904000040381c141d4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 624103219 1250 624101969 624101981
    0x141003230402033307020c0a0b031905160c080f0409050717071209020312041214011e0c030e16050405090f03091507020409060204051305060310021e030a 68
    0x400c4068a04d165140504029094000f07041d03c2400202e24085400d40f5a40440e515000021801150246012480000c070804050703000110322810107c03c4c032100301ca00c0903106d00788484521040c041e518007014030240c00080300d0840c008124445140a01340040002103030044003900d0801942e49403103540060181c0300540310300000444e40e2882040c141005410030b0f0041e04a0395841c03000088004500c0050412104260303414064000c0e00070f00844d1400c01407000b0085900084888600f500b80581001c5044100020346d034180121203d0a000700400d507000304440150002d40b5142049e000ca004003210107030b80c50684141020030060031100756507441150b0003260103010a40c0d4442440703456003130f2891400829440dd01c00d070400707450000b00d0b580c803541040112509111150700050203540b00c070700c02550103e0740050103000500b071042407007c02c02a0703240f00f4006410020301080d65160464841111258086924441b027040c064010007180110303203030203440f410240441c1c03005100b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 624104469 1250 624103219 624103223
    0x8030103030e0409030f0c1106071b0f0f060305071e030516170c0304020d05030a1218050c010e210102131e0b0711030a110306010504061410032304 65
    0x7440e400c82c00b10314641070013182c410726803541e510302e03840f84c540005803031408885a0071500100c11a04c605410b803201e901621140380660300603141495599294601040160421155446036031030510603494000614001c90300079103000610795441070340443d403103111145440000e00b181c001210000b0342c9500300030300801120a4000080d84144019128803141142c004c1c208007028000651146600021f164050b00203009001240c4055603100d046600c03002040000c1840141c0041c81440644108410010042d0120300c00300959111141e80e6910310766880c0c1002511024040c407600e5545030458040c02c00003124403c440045140760107500300d2110f116082d007002d4000a010b203481c400141d10300c489003002c02030150a1801c09400c5603c0018152980c103030458529005032000c00180468a01402c02019109907a1040608001c41a84103511540c14104180700405140c021080d01c0701e41101c0850355012808030650103024000d981d038111050314003042a02001201e45148a24 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 624105719 1250 624104469 624104477
    0x112b020912011a012a02010323010806070c050c0405100b040902041409010b0a08060402090a08060a06080d090533040f0905041e0c030c060f0206061f080c090d0803010303 75
    0x40200011204d0300300c40314041500c560503003c0000c3c01c0d9170501c501c80b001801032401280074280000c2c00213840c06080d041c6121103103220010882d0300d01c1842401c0e00b04d103c3d81b4240e000b00b0040d4071202e5950303900342d4215116964900c0401d4685601400040060010070011600c41d550f500c642c1e8000d400c14400d621a42e498241d1081d42c524100030824107840000c075413603050200d0703401d00321078820009004580043d8204004003440d030b50411380d01c2c020440703003000b0002403415003103220903202164825402648004d072591040c642045410081c0d40059442c00401d207041c009048040c1250308038400c1010b0903010f241910901440140143d80ba4800071103901a59078aa6000722401140d01a2107007014800f060103e0810b41240e11909016407c407503200c0e91a500d0300302800e43d4640c420000b141610000101c40340c4c050283c107a01a10840c3c00004940c4071440301152074a03203000500800106170700045050034a00c040d1403120390042e15441a9000c149040e081980c002c0c0000c1e4046 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 624106969 1250 624105719 624105761
    0x11010501140a0e2805041101030903020d0c0813120c0f050105090f0301140a0c110a08040603022101080d031a010914030309040906050a112b02091201 66
    0x4070a15648903500340d0082d1169080b00e00c0e10020280080003d401005501e21114189000e8140182800040200c0060015450405203001281c2c2013000702a01d0506051100c0707030f00469008541000c0c0307010181080985c01d4107901d056800381c0305030f250038400403070681400f00e4202200e0b074144180b00c3c481d004c01c0202985540c0d01c6a6542d05d1445480c0c0024401c0103414224100100103042000d0003900202d61091140070705801341e801105e100c00c019a41e011300308035281d402640812640012006090042102d40701c010f040d202d24001c8c03209160700004d4543e460900300320a10fa4443c080035070301503956141d0400c01d803a00d512500b001c00090400200c815915002c10703100d01c5a400585031300000f549002c0e0440c8405d15407406a65050009100d490034a031601d00070310f003000340305000004613494801c0d40401203a840c0019424030000038001008110080070040103080000070580d041d0800400c0b01e0400380c4210b40c205900b0402e544580c072079503101508030b030b5018031008140e0504 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 624108219 1250 624106969 624106979
    0x4090510050102061005210a06050604050c0403020a0b030421050a18060828020a0e0a060e21120a0809070519030f020301060b0708120c030c0306090601090306060611010501 76
    0x4e519001c3d0380724446114091010051898100c00108900211a18404003100d2142c01c160404016880c00d80300c490303c43c0708104103803400d8400d032079102c26489076a506150450700422100304140c0500238008400001040512230fa20400c2010440840400e00c040c40074140014200d4009519060101d960180d4000701c400040104100b41c501c01c1c0d4905980b560b0708a000b601400a200e4801441c10700442c81d40500c601500082044854644450070b4000e281010700071f016007603600490400200c1c3c010303101103030344082c06003c1441062150400c80c1d100020000c0c1000340907030300705d40310b010002803c1c07603495040790041d0710942c088820f5030507a0360381b070062010707100c2607249035004e5409214041c0002030501d18048030690000c1c0000801980301c0002c0012640f05c2c5500b070340c500ba000f05d1009054518003102c0365200c0c181016880c11402e25400b40c0c030b118040504058403c80b406000590540d104050840045030011410310079075035070300c0c0080c0440e2240e004055a41d420700c400499 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 624109469 1250 624108219 624108223
    0x30317040b04020108041a09030a1107050603040b0912070b0412360b03100807080c0a0512031905030105011d180702030715050106080f04170903100204090510050102 73
    0x300c915000010410159607960044400b200001c000325544101000e01c9000c070700b16028a80d00c0b604080f0b00666450700010b01c0904104592450b00308a60310440060201c2d07220481a00e0708154031000d02c0e61a61611000c490a000b48204c080c4d0702c808001c070340c81090082e070140050140e07024010742004506041822210110205880321050754140c1c81c0701c2401e003110810035841c420352011406c6e0701d9100c0c181c0315a01da0041e600f441062613004801d010154090150400070b001c1c034802410304a8042d40070031502d80a920580f40f190b4040d0070f01e032a045800784101c1c0c00403070624044200e4001d14034400f4105400a00540b40010b247d2070201c20030000d04011012611001800301b016a1a014003290504100a00c5041140024403000b0000f134a00c0c41118039895130040d02044540c140079000b000303000c0c020241c601038100c000600000c910380c0070b2016201b11841040710b40c0c1d141c600021910344009040f078084507070300c000b43c00140d10007660b0140d07000340d4800030554811590340004903 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 624110719 1250 624109469 624109471
    0x50a08060702070e0712050c0a090b12041203060b0703091406070305031906080d0f1d130c05162102030903033001080f0c151215030313030317 63
    0x180240e4440d150034018804d00c2c0740d0041e404401403602e5800410001009070507a0020b85d1a81c481510201b442d044d82c0d44c00c0101500030f080f0300c103402d070708107440c04070549400c500203800500160032108101c01c449110740c000b0310190a0300202c10740d40d1a120701e00146078500d9842000c2c5010700c0c11202c90814a400800c9900c3c2d507405030354150554407002c0b0f50100c40511290151015035440c48001000030041c001500402c61545600c802507240b01c50140081c104600000300070300c07090142192660314030700b0640ea58690500b00180c031401c100d0b01507401d481000a0425000b00510701c2c00104207040070b5070380c400c801c03003176070010740e1070720300310261303604d0140c501c006902d0303001801600c00110602d00c103280d02c0c03040c0744c60148a0f4050b51403a00c82070380d801c1c0c0000410782c2100321040310104040155054005085d100c80c000031400c1c04001e201402508802d6400520b80804140801100360041d500700c1b4004094aa41d80c6044084154505240c44100c000c2204001041700041401d0340b00703 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 624111969 1250 624110719 624110731
    0x150a1506020c01031b0f110f07030f050f070312050304030908160515030105090f090c04020706020c061308041520070f1707051c0501090507080c120c040902220204050a0806 76
    0x3140b0391b11038840c010303103003140b03000f20032029841545d0054900d09410000500114091518241d1400c100d0130280d0800a2403440c0e50b038250f100010400008203c46002d803083c0d070300ca282007038032a00c5600d000c540c0321040750301216051003562080c40f8a101c0c13488612003190f40445540011507881240e00340e041c0801d00c502070b40700318104005021400e4000d512640100c20209407039011004070009422038108500c15540c1560128007507000b5801002034a23000510302d054010000c0c440d5503921508c2c4290300403c0e1100303503210607801c512401442400c0004000400e01c084c0350407140d0106d55605518880c0c002c04040d100740010700320300404032104061101c40b0207800c41d64240000e200002403038042e00001c5402c80c919000110701d0070310899a02d24400e40103480441d02d00082146402c5900c2607061260403802074140d000d20000646c1c1e85580019600868010040c0c00091401685040320720003a52950482528a481a0340104181c0320103e8610307108980324054180e03600c20403220 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 624113219 1250 624111969 624111977
    0x13090614010c2109030605010e09060a0c031404051b0111030a0c022706040c030e03030402100207180209011e21021606020d1805150a1506020c01031b 66
    0x49003940d4402c0741e145000d42d0107203a0120004080350f0308402c045000c2803030900040e00c2c3c2c06050040002d14011240100340007990f0016501704072442940701d400c040c0580ca505c507918076401c107040e0702030340040003049100844044540390134200140c070f9021061b1020000e4006000315140b030341c01903030240d4443c03488800450134020103400549030751440d400240c1e8041c0805500810b4040000100c90780c0d14465410b1104a00b45034081c002a500790b400104285401c20502141081d000000c0d290300c01d0b0102c4208108080d03070041a8140810762b041103007806400c00c0799501494442e00240440c0c54280e803860405001030340186410410b008031480003405889018840f242d10080013020f00340c0145d00103280c220110020b1343c040400b4142155050707001301da4001c90603000e1050301c80c01e424504400d4801d40996490307544075408280d141d42e0070070b811004501541d11075803081c002c4841c0c1c002c1d54040c0548030b02001c0d5552502a900314002800c1040c00b151460500030b06842c0c03203500791a = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 624114469 1250 624113219 624113249
    0x60a0c02071203030f0507020f15072708150412050306011d0f0406090f0b0604080303060105030703090b07110c0d0b0601030f020c01150e090303040b0703020c01090506010605130906 80
    0x5240e9641440b8010a8040546072207017410301407010300ca040d0240340c19070010000c0e1122802e1003414607441d405024000000f90081005403034024210b50000e200c08005038058450480300c0310310b075185a80002415114444c00e40c10002003680480c0d00a9000c2c141c00c18241c0941740c0121058441100c2c180c1c00250030f100003c2e14034561200100c46807400500803006030001c50003090841c0d1190303004081c0643c540041c80b44840c200c0c8903107140c1060a130b4400c0d20f03150811420944d40e12000d0036441c10801d0000c00200f038544241d004400c0d495012202c003000c0c2c14403a100501c1403281620300f03141809440d0012040d0b10b080c4070b0301440f46911600100327080c3d0310180190000c148183c58076070301da5003c00180703484440a1040100046c440300581c043c450400051304108e176002010483c056008005102c046580c8101580d4083e80304c0ca00940d0702c40f22040c01501405886200524902c50b8800200380380e0740000c0075020070390036260744894072039482c5c1ca003400b902c255100b41c0c003005200c41 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 624115719 1250 624114469 624114479
    0x60f061c06090f030203030703060b09060f07050709021602040605011b0303050702150c120c040303020c040209150711010e010507020d02061b03190f03290f030109050a05060a0c0207 80
    0x1030032120200d030040c2070002d600301c034540365030110000e500b40840040e0000000c1084030754052042e83c0150403140c80650410301c1c2d1401180d007500c25048078400c0c01002140603000c1000800020b40982041e0b0303000d548903c0c3c2118841d01c0c600e005038040344124103049005c0303981d5206103050442094072140704010140e540d10190024400602040c4c118040c100d5200500402400c00d1030254051220040d501d54030901590314646014000c80e041c1c860401003080425400224a500580200c078016921402c9100107a020401444001200321b80070132100b050100c0780031480c49189081c2c9801082c1a90b04004440a1007005002903001c4410255080542410400741103c0c2581034900c0c8107401d0085840d61454102c0c107a52140001c0c06106503c29550014424070300200d44d080610403090075294181412459008001d9026041041ca00c015550811030001c2060f000c0c1c000c00c00c0070001e0504645030f0710074440555661245802258504d051445501000085075000d8422079044c6 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 624116969 1250 624115719 624115759
    0xc1002011a09270a06111c09050c190305070501080103081210031a0901050f0108100504020409081b071a1c090b1504140403170702070815010303030f06420c05060f06 73
    0x800707950b28821480d1000ad592110602c14004441e90880100850304d18605503180040c0c0f6040b4504012500004000007007401041d00c0450342810b987e10515994165500c180c02051fa20150144808192940c842c030449190140141207940080c841ca81d035800d141e1106007820300c03401b10700350f0008140b1204801c01d54021034001c0e05c010404a40440030391600c03582504403244100c41e20b1340a858501c4817001c1005850000d004c03d103004008200018015001d60090b024044007000107400e00e0041c81b403039580001006a440154000035003440c5d140c003000201c202c84240d004038a0200e229140e01040108a48200ea0507511455a00c4070f007a094524060080c1c5084c055114000c00804d02e018140441085001075240d05440d561440c14001d040d9010b110069036034030303c1d2013401d0003d5464510540c081c805c080d10410501c00307809520481c802c0c585034650350300f0714400d61994120340c1d1125410881e03c0c00340046581e036455000e800199004256130710390f40598980c3c182c0c0261604 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 624118219 1250 624116969 624116981
    0x8160c02060d020309010b090f0609070c0503091513120206090622030303020a0f0f0914300f0f0c1905040c020c1002011a09270a06111c 60
    0x10140c078032400d0030341c0c4507003200598005990300d82aa0351075503007180b81428081102ca501040b4483c1090301402c000011504000014015800704054a0700c54000c0c03120400844441010141c03d505a0120210502e841c40c1c01c0314040c211042044140002c031484001214200355800a03d901e01c2c00110a0400c06d05a0260010400c9115135007409000c80c4154158a070085020fa00d015070317a003500c8031004110341002ca03010002c1c01810b00540c018154815054800c0d5502050010002e0070520001070302d007200e440ea01d40c2c4d00ca0301c14001c2101010700701c001c06204800d0400f180c0c041c60310401555107880c2041c0268a02c0d921180200c030103842d203c01400300380000d0300001c050f5203440e000406c098400d0141000c0240e0302403114090325040c22000c0c07198025813440204000314240c1542e4180c03607800d40945114030007005c003244050124401a4030507200e001c2d07c0101c40240d541000c1d445032907030001a6885442c1042c40640c2034010700482e049003841107080f0407101c001e50602002411 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 624119469 1250 624118219 624118223
    0x70e0105130e220309050a0501081303030b03100905150a060b030c090d2112021624140a051e01030f1a0a060807050d080910180f06080708160c 63
    0x70250120500d0a1801d911a42c618000e607a40300e017590608041c04a015500c0e40000e04000310785080040c800c0e015456132150070351610b0f0110300c080c41400042d103003600036880c0e60358145ca881103810030004006502021200c248402502d00d03075030f805200048035014403402c1d4010340204000b42402040304001e0240d400010b10040d2031261a4a901004600d0140e0280310800d609884856240c3c1100040392403075800c000c10740c5400700c005d101c860034240314000140800710000301c1c0110b440914408075908030000d042001010450b4108080b4000d064894140c020b181001050349088115620503080722641040011a403a40d52014042c0000d00700940d20350703449610704110f8425001500f4090700000d0300c0071482500301502d440c202091075000b544608600c04c41100000c4801007a46c8010008546640350141000c03000d586400d4403060b0226680f4000d10f01140818082c0100001c0e901c00303540781c01c0107664008042e102404256016040d4658903401040440c3c80b46c51051a198 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 624120719 1250 624119469 624119491
    0x608031207180f09020441063a15030312140a06050f190e060a03060e0a06050603010509100c02070803040906090509030310050415080312070e0105130e 67
    0x59840081140301c90580c4c2061001d02d40008040044006251906030f0707103008008400c0149200314181c945908102c400c168407070201c104421031659540d0f0541e0380341d50642805111051048080d0701811500001c07800886505800741c0403450101d00c40d45407032910f000307400124182035440a4681000c2c03030124818042d2189441e07144004040c18150160307101c508041041c0e818001000306001000295501410700c00c12545044080d90321003004581c0c3e00f014070241070729060081484e00107642c1000e41124201b09a0f609010f100181001c401d5000f841d081106e0384a507410182610700540c0e002d50f4a40c040300c004100407002d54010041803e03d4011034540540d5180c5590554000b40d00074411035503601410488840c141c004c01d0f6202d40704002442c918a04445002c200802c18003c150003980d0b2122010100044801414040c0822004498580030b403140007141844048841c1e000185a48aa0385029400f40c420780e0450b400011701d40b1413150a00701d24113051078000300102510 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 624121969 1250 624120719 624120767
    0x30f0d020d0f050403121406040504030302070b040305090901050d1109070909090308190b030307030c020a0302061803010e0c0f1e0904080301170d050919170d02010608031207 77
    0x45941d40314035036a030a0b921801003902d24060402504405110b518401c0711401c0010320070851100f80040c0790302c40000c640006458480d42402c4000780103004004050f00d610000b40014950403c01511125104031f0350a1101ea88440902100f445280d100401601850030002000d20b8a890b103180c0c00f618914050a005070303107032554825030700f0001040d008511280280070107255241145031044100c004144507022040000c20340e01d00c0750f440050304011100202a0455642c094541c0046400503d440d03140c81410b00000c0c040c100c0940041d201e9803074601001110000822900741460b0018a000c0d06884400c00b8010100f04a041070701240d240e0103000360f440c0d600c0e00b0741e0900841c0600405600c17581401d82d2089040f0749442c032060203a00000b040c0c1583e69000d0125a200c020940e80072140a4034400d07581203070009a044074401c0b525504204000c41000200449024400da00074021190f0399250340e501e9110308007024840b0b810700400030b094580035003469504000820080010 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 624123219 1250 624121969 624121987
    0x9020d0512040306050a0213120305130608090f0706090902090d0203010501060509031b0a1511071403100501030f0825062307080109050c071b08071205030f0d02 71
    0x105030000240040700480850180f0900403148a80307540803c81e58400c515208102006010704005441002c0e01c01c05004002420503100d030302a20401142007001d044107a450704009070514004407009a214811140c0da0020032000203000d80484132561513041c0718a08041e03e010203584141d404c0368124136059803010060700c0901c1882e00030441c0b665080e84500d050030405040208441c000d0140c1206407600007082e0b0f80e410b44841c100c400c6141c5014030b8040780a400d8500c2c0c1d611100b1490b0342e0142e4040065000c80503222585084001c0341640c0380c003021031170700e5022103c2c20700001c0c083d401d4070a202400600c03518001d22a469100c261032500c020250340050300000c034104102c0b811394030b4440300d032030300e0104401c5c00d805640d00200c80306e6180713850b01c00104007020503c109042c0c80e8581d0007090a05c0c20801c04c0750800d0b90000841e00b03490601c6060494400407a2280320a03034402d01c1000101e41121503226410b142d07000001e503240510110224100350820040c0ca44419400c01000d46 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 624124469 1250 624123219 624123223
    0x12140a050c0708220f0e15182e081f0204030203030a03140703020406080703051005120106140a0506040b0304020609060309100e030c07090911090718050114030a09020d05 75
    0x502031000c01340d62a92411010011075800d2003591040700c22a91126050120220002c0d14540c8000300c207071901c82e10500c1000140700c04003410101c80d40030012005200e01203054510308180c0c02c8400415a5014440c0180485124100d00c12110103070040c0c4000814881300142075a00d012070140c025003400d449800290070356124441203030200f95565404821981c0c082d58403903103c01203060441c03c0c5442c080c405070004000821000c201661b600008a107402900d461001405016000c8018540c070409100d0007424540103c901da0701d14031b280c1d0580e503e0004014411369a020702807609040c03415201070111340001d802240d10000c103200004480e141c16003c2c5210b00412001003000d6189123028108a481c4030306900150341082005000c007403c002603040031075075406400552240c49003030016200c86c1c5c4a050940c003041c1c110500c05080c0d4861007000312803140b80c07007611090b9550801910400e00711100b10904010034800507005204e1544030f0f50740903001606004a40081c0d95400d4 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 624125719 1250 624124469 624124477
    0x1317160e0a18020a0e1f060c0312111e04080a0c0905060a0b0910021f0b0a0605120412021929010806041118100612140a050c0708 57
    0x40310528000301040000c0c80c2a000304400d0301c2101e00c0424514040d81c0202d144c0b08070501442d68075100810110302c544940c0740c40b010121186644059001c2d465000c014501d60900070250001010101c0c203003802e105a100c1c050403e00200901031a081103221011090300c00c0890075181c0c04000c1c40005031910081c8280000d16100b5049a944542420541000ca50010308000e0140301030340c10600130601c400003150b4101c2d05c22140a0070104410104928010000e84c0c0718081d1022078888410707900c100d8100000407007045540401c40d40d01e5000c100d4007801400c95000013022a280400e010855a2012041c14955441074402ca035481500140a0480b9054203c400c09a129280101c1e00e143c2d132001e070718043c09007100000b594508440c81b5a0b5a002803c0a04200302e501d1809006941d60304161001c4c103049040e0440b1454180e5080142440d0b03489080046099814420a070307144501c10b0703a201c2070301d40b0028060741e1503c2450a0003814014650b806000080028002207883c1c28060 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 624126969 1250 624125719 624125729
    0x90203010b0415261602030909010303050c10021b010b0904121d060a1107051903060c0224010911090105031b040504020f0306121c0305100302090f0601030b0303131716 74
    0x40142c508041c0070315900c44040817410400c54009010141c50341c0d95402c8101e04498142c641980c8a807408060075060010706003035100214400203070428540038480c808000c41d802d030402048100704050500010707c2d8201e40040025000503a42c0300c04502641c4001c00300342c100d000500c5c4000f8a01d001c20b00b40d40c02450008081030048041840c00131080181034081c0400b80c2c5d030103445030f15000c01d90070301c1c02580c00014612901d55a0282505100b08103040d506045075810030888500c1780d00588000400b802001079090401964141114001d030888006d441e060392024a50355900c2d0762030a81c0c2312021149075144504000000d030554450010f0900500003109181e981c0c1084000c010300307110210041081390300000c4041c0382070050440c68101c10501401c001c60b0b5603a81c590304034400c072101e8000960080c9000b007840300c0c40c216412254401e0000380c030100280074040040555a0049400481c2005010b50381408240c0c0860120f4205402481c110780150301c491076803065002c1c1e87c0d004 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 624128219 1250 624126969 624127037
    0x30f0a020d0e011a1e0618040204030c03031101060302090f04050705061c060806090a080c0a0501020a0f180806070f1205090a0210030e06151f18090203010b0415 71
    0x40b44c100c4404510360b600c3e44803c40c2d403046880c6a0700c41c6084000c1d0f407003014510445000c2864940f4121207800c44841c0b6030000d00840d43c40340c0381e01d08034031280300d240402d0300050b0350310070b070000c2444052081100740c87d00200380030102e0f03440c880e90500c0403200600807035807030081c80340c00516503d5407030180c5880401398401d0060082010100d0f4122622030b40100e01e984d028605002c41084041210501e540c1c1161400b640c541000007032610f0310000359402480b543c800180c00f03001950145560303110000c59030307440b10421082c520070741c000c14040c0a440c83d0f40e040007002c40e04142c041c0720031102d061442c0c01c2000038014200d0102088800803140703803020340c011250740021803070506030546000401e030604000000c0310b00007003940c0c0c50008200b9180707409400e4a010035607541861350488030f2200c0c8905203003005000c0005010011440303d8160241040030042942c1c80c41e402038138181c0f1482824035007060300d044030020503101038244a4060107401c00d4900ca802c1c0e01034009514003032603030407 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 624129469 1250 624128219 624128231
    0x9010c1a061008060f040e0a0b010603150512330a060e0106080c030703052502151e0f040f120509030d090602060f040c090e0a0c1a030f0a020d0e01 65
    0x20b2040c0b48580b021200100103091003008183d0b0383c2d988142074810002c0e500004c040426107503140c60848040400f400862425000056055258028841071000c0c0c1504030802030b581d609114448131081940c0c2210b8110915041103206c4081c854210340454142245000d5071048882d00542e80c142c4080000e0703600d466090100d114003c031400d005100d5031400c80060315220501d1141d0740400b4101d1010140c80e200400c90842c408000794103840701c110364840d84007040c1d840c047d5132010105c21a00c403480709200000e08081e64030a01d40d43d44140302d03000b0542c60340c07400d03200380a004004108940c54a40d45040d1400300b82c100302105003080140d10303000d40d58000102018030386000365020404101d0303001020b110700c030340c08a1115048400120b111804d5125031900030388050721600419081d5241203884034510400054806d89680544070341c60b900c076240c07940108404105c1401200c071020802c040340c10110080d800e0340e17000c00450401800c22008081c0761050f1750484001d102c0d50f0b91141 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 624130719 1250 624129469 624129481
    0x100315090e0d2102071a16020601170304180f02040b03040b0a151421010914030403170d090f0605040303180210050a020a050a030206040512030106050d0209010c1a 72
    0x105650b051904080e10b03a81c0d280c000d003808801c0c0d25040203800540100d008802c0101081c207a1a85820b108400d2400b443c0c42001900342c2a511007040f001031061000009680c2c0582c405144c6021080f40654505030030002400c0c0311048102070501500c1d50780ca01030700c41400343e03c05080030b4080140311658909290402c00351864020780074030150340c545510f12818220241e4100215002ca00c0042d10029090f00001d0f400c000000011481c1c0c1721b2800400910001984140390551003400300f4807001c1c0750300c0203150b070741e0183d40001001c1c500303150076040700494400c0c0501001507202d01c010800600d29a01c000f911401c0b807004070340030307500d13078060008140d0540120395400041c0384528880382c13543d400144e0303409001d11002091007400180880498428444208000c0d0020b04540c6051124600250354440c226010755550244030580e00c034180c0601c1c1200d0403582c3c03035030ba4079041000d8800300384000d40c007a0b038465060140d641c940c040011060203060010030450f4036030002c2844d03d0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 624131969 1250 624130719 624130723
    0x80a03020a1515180209120304150c0209130507080d09060e011704031b0501021207031503030e060f0d0507020609010b010905090f13150e07140906100315090e 70
    0x150346001c00c160030103c41e108401c6201030580100e40300d0704003c03601d07102a2074241c00240b048408090300a60820901c01c100c0c88000010001c0b0748026480c100e110000742c074104c03210b070180e100095000814201142010340e00d000269241740c041c000b03031221079594a8100385408200700e2890301091000c0410401c2940101e6604a400000c0c2480d0b09607400140a132001401d00130300c0102408103211080700c0180258210804181d4000021580c1d04142c4042004c0924210307000e400007800c140508801c43e0414a50100700c0b58140c94145118014608124030b6400c0700d1401014600144240d030302c40c103481d000e210301508075500541840e0405e020b4140c05c1d41c05080c4060305201e545802000b05e500d4550005600a141c2c1c40410059107d8002ca6a441e4010000150072800c440030580f403030620651110300002d4001c0b0803189010ba48500c460b0f14030780c4199410754400e000500155050800c0c8404c0c1009140c24a4000f4000040b1400da1201c0741403508529140c50783e4848243c400354003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 624133219 1250 624131969 624131993
    0x8030d0b0f010c030818031c050103020907090e01060804060908030a141030080c0d0e040603020607060c0201150b07020a0906080307080d0902040207060506090a0506060f13080a03020a 81
    0x1c03c0c41c0450203c0c0f25910050070f01c0101920682c5c90203c141d06000704400c052043c0d50500d0b1515000144400b40855542d01611703003800180e2080e00010041050325010700c0900c0c08541c0340780c6400d20f01d07a01e815019108810000d006481b0740c2e0719000e1880001c3c2e6403800031840b6140c681000290707400c07003454a02d442c0340000c0020600101e0300400340000c1c0040c0049184076402104896022490aa07025040072054030f4003c06000c1c3c045440d1a0040005c40c00f865441c1c060b6a40250813400c44041100740d850611001c1d4010350300300701c41008a141a049a41a07280c01d00000c01e4040c06403c1c4140515640e911490002d0390120300807085207131070420b42c0014460103006020782800e0800c4a9128850048011b019180005091500034001e402004185030020700441d00e80003603040ca00040d00302121094464481d80d00000d040130315071300c01d19018050107031010382066001d035551540703980301410310800265004000120600c0c100310401c0d035103201364040c005080042c40c1035028010 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 624134469 1250 624133219 624133249
    0x20f0307110a080d0c0e06070c0611030f070f020d0f050601060f0c050c010c170d1e0219030b0f0a030809030105070903110d0618030306030312090c0302150408030d0b 73
    0x1102e0520003040840082e224a08408034002a64003070040003075801d40030034051182c00c07201c04241c04c0107000881c203440b000c0700c180b5264480ca420b0500c4e8059280d1081950140015500307100f40c20114000c4140103030042c1c400360460b00680c0e01030b100d4900004201d44211001d902801c014003005074040b07480c0d28a401b284c18220908080c1da516aa01e4810016030207040042400150052007003841441e0084036100326000d65a481400f40c0c00d000c1c11032103a41d900340b1408a01d60500034800c62088402800c425150403110807030004003100a0440c490000754030a81450075891181d580d443d01034015445211001c0c1d4400c071310b40501d425600020000d000b40f0556030820030108250804401c203112084580c0d6481c41005d1915100a11750041c0d8000e0700300d20003132a08109909603220300180e9002e5190304c4400d60a0b002d82d182610402c0c1e81c014117650646500700f00504060403910315034103000509a04290301c0b960348910307541161340d100400c00d40324804460103040024400010303030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 624135719 1250 624134469 624134473
    0xc06010906060908061503010912031a0105040e0f04140d0903110405070801270606050705070e0601020a110604030503070804090b03012a0905060d0c0206010e0403230d020f030711 79
    0x80d01d4101c40381c1e11880700501460140c81d441c25001b416035000c0d440302d6429035010104010807111400020f006102e030080740c1d01203482c01c864003409503004200303450848141003e400c5076035413070060000e00300704090000c03140d000806040b00b10180041c4140b803105160707a583e954003c0c2c55803c2c0071854580e00f10320140901d25040901102e2507200da00c89064403001d10781c0180307400204c0c01c03100c08100f030912440340d16440e004c0042071207540300006041d141d02810450f0101c986905906090340d9040e900f141c00740e400407000c0b000150380700c0132500c4c003110300902c094180f658a80b9042d05552000b80111480540081c0a02824095220798021904198000c1188421480d690101c2101031071751224070600040800340c040c1d2003030082001400707000d03040548a03d0030200480260506101e00c8025014502c00840c840801d601820310403500343e620f40c0c0302070040f00d102c1c102d5841e070440f5640310003d08100b07000c1494018001807100e00c081080c3c0680e01d02d45034000030030000801400014503 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 624136969 1250 624135719 624135737
    0xe16060518040b0f0d0c050a03060902032415030a061d1005010803090d0503090414150d050706051c0603050304050a0603051b0306121b030c0a03050709051b0c0601090606 75
    0xe86481d012001d080c0b00585000d80704a05c50705080c90b040d400c90f444141d01c40e05040700030081014a030440ca00c5140f0030f40171656030926070304401d84412661410084481200b000245006030900900c01903503902405682500000b03072590002e9448250b0700382d0b9400d81d442d003090007046003080f041d1564800c280c01040b041d41058060707a228820540003c0c172840350741c901807050002c1841101d005903002007040052400180e001100c0c00b40c11540e005100b0b403413001c01c800e03e0402c041d0400720180d201029000c1d40d0305100b8140e446030840043d0131807541d801e42c0d101c1d01800c110f01c6543c02035400380004580381c07440d00c004c00018102a41001c81014140b400740420141d4920100041118a441c070640300e85c5d46001150030703a8000301011002d0b10444142c049d0082d00c1081c095040d0b2016016a00c201800405100600d401d44c44001c0c1103a01100c000c0000085560107030b034008c5005103402c004905104083c00d95501325041d0f0b1480c45e00010010803401c550fa200b01c10041c00141420402 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 624138219 1250 624136969 624136991
    0x18091605031c20010207030c0c09090206030c181207050405180d030903020f1b100305060607080a09030b04060e0706030606090504020c01180f1202031801030e1606051804 75
    0x31500062100307009000f081101040190500c104080510f40d14800840d16080681802400654209019210040d800c0c0021524888a02800d0511030f0041c00c070a1454498480058403627100e048a01c620b81540b0a21141980d282c2c20940078842550b001002c40600780020001100c0e40a00107000c400038100140340e03103100228440503502c610b130400241ea1200c034107080c0e003003070f00001c00640e81e401810550401048a04841800403506403001310303800d8441c200607000c0b0780d42540d00c240d00810620904002408200081141039201d1070035641e0f440d520764480804002c15542107610742d4441c680801c0010040141b08010481c1c1d01d024802c10b45450030241c40d010941c003801d80115000600b00d14464025040503c10511034026070f403148115052a00a0302c25a40b42111640c11840d41c0d4038070b040c4004140c3e0100f2410500c2c010b0103184031001500106100002800e581c021543d00c4400b9003017402d4103c0042c605500e900360b448c07211642d103e0390404441c507090701c0743d480c106911b82 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 624139469 1250 624138219 624138253
    0x2090906010807090306110409061505030402090a11030c0703030b0a0b04120c050a240207180e010b0904082d0703030507020a0512120c0304020d111809160503 70
    0x24221500382007031070050f01c4201048540003890380001d44040d0900105010441d580c0000300101c49245104005403525003810460800004019800254090004c075003d45850524103400689039103001904e240c0c600102c5159400c200d03200d10583e5000b00d0600245a01b41c020b07401c140b0030488182c40e1841c141243c0c0e5209010f00d0098010300d12856070301d0b0041000340702a00c0d01801004003101d8646a0700d111040c2180b18442ea005c0070505d005450a4241e03000107000002d40359000d18841ca11840700407007400130441c5241c421703a15034031001d20607507648508400d1801603020b00c3d0429620203682811031048203e01c04541807603140c40329490251040e5105640c0c0d6030b0350501d070125283d203450500300d182c0718422801a000740030388901e48240d514080c008000e501462000007460360356040900940780012100070f074100a8518080c00011a148a800a0381c07000400012000380305540803440301004842c80300c0a40d10010301d0b01e05000c15030403940c006010840007421030b0302c11051401 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 624140719 1250 624139469 624139471
    0x90f06010905010e01052431050a08070608070309020a05130917070305090603040203072111270c0409021b0120191205070f1d010c17040801050106020a060f020909 72
    0xd02e1004081903030a0325002050079617140f108100b1180d0240c60846d0414230301c81c1d4080c400d00f440b440c004800015910340110724041215031644a16126903580f41d001d50180a8400701203078441103000340440c11b9601da01001d10402d924600c0055062524507103120041103441c040618802d00b0302c28200001e5010007204e24a14080d100b039501c980751071021a00c0c0c5100d1b80c005803603500c480040501c0d40714551740070172100c0d80502c120140720304100081c0445103c1c00641d15002c4001174001041d040c0020701d056400a805504991810f0390b107412400032a0841c0f007106c0c00802d084551030406100902640b8040c4107002c034401485044042072000610654040c00c42101c4c2d01c070041c007070843c0281c040b001d201030390400501c42480c050000500858801c141d07400440c8581d5888000e8080070000c079030010703106840b586850703203140d10f90000c404414450202440340030000450000303800c1c05401e00038201ca80007849049802c1c5401c1c000d0792502c10313040301800c0c41030105400c1c65603556029 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 624141969 1250 624140719 624140779
    0xc0b0a020310061b32030d060909030f030903020f010c0201020705070f0e0f0411060a030209030d0801060503071407050a050d02071d0f070c020d0b1506040b040608090f06010905010e0105 82
    0xc800417110344050329031842c2c1c0742840c80c203074400c50030f04d0724001081c040014103042c800040100400c0380c94100c0d0b0b078115070104c030015000920940228043c50301951084042e1030080c012100d14103400044207095850030880a0010303500881c41c5410000108028800b525000104090140c2841031514890750000d2412108035400408201031000183c4000030040016006551701d91490202401950054131001c0c001c1c03040e11885c041c8288641c00090503140640c1d911840c684551204944c480a45585951070384030420849000440411240c9200d52080c0d010302805140705d40042d080c10b003203034030076070700c5001030410368021201c40705026901141c04010080b40f62144403040321140d0740c01000030f4006c02c28003031150038450340c1504203200d000d440404001c4000c00e1400d011882c080c0d84101001003005010611405026980d401d5101c1c0200c4211075282e101084020300c1c00100780d200c0c140b2030359a00c006021029001d510310340501000d50350320f1603802d00711601c0d0400410309086 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 624143219 1250 624141969 624141983
    0xf090e0c0411040815010f12050c04050a0b03071509080321040f020913020307090b010801030b0402011e032405010f14041e1401020a0515070c0b0a020310061b 70
    0x10082c02c540e14106840c054103c0d40c08849070320b00300800ca0155a80f0a02860038414040d2100086401003407408040c8a5840780c003410070824180103003c090032000c0c000c100007603254100b0301c0f002e440411009004018080000b030b4016078018000d031813410290040025500100208460345858250300d0042e00b80303075031110700150b460742032144407806060343c02944a003984d410301c14010884030401a00900850940b01b0071076176011603604940d2240c00d0940440d01601c010004180700d0070344070b503005006040c041c1142840c101c0e17007030440b4581e05040700030075914074040440242c000c1d00e4840c0e01488040e110310250034000040c142071490040581040140180361100c05071190a480042842c3c04010f40c03201800306210413912024003482c040040c8901940d04903610006181ca490390300607019000c00c0c01c0200d079803080d82500803e20418001303007102010000740c8031101d0358400c003270f010750058482c00c0102008800358800c0c0c1c0420108201c3c803140e0407101c05e0f004e0601000e03c1d440300c1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 624144469 1250 624143219 624143231
    0x30a0f1b0f03080c01052a0d0f020708130b0304210c02030f1014040f02100203070209040b090c0109030b010902160c0807290405060d180503040f090e0c04 68
    0xc20303900e20109411103000c40031204030000400c105400a032005829400091166540380580354400300d0102d141c001e8180821a4402c7c0c500c0014001400e6026040e880071543c1c2d400c50007502d00f40e030311032081107403840c0380014000d4034a1400102d2102801c88040320502e1803c054507040d0740c00038181160100350070b0b10040c40704070030b000d800c0902c810740d405401d4651914181260540b2250340ba68500501030409001c000b01585a42845110355407120386650204c210303409010b180c917903040390401584010440d08003d652540c10341445140310341112401450201000c42c2000c282c8900a410301102010a00018101c0c42c0340034150366841e94010384406600c40c6240c0322840000000d40300f400450000b01c7d91030b9001c45d0031010b60b0310318529a28035801c0c4419000c822000030400400c1c0700401e100c1449145411801495100075100010078000c084008070600d076003417540704440030b0340300190400540354590891340c014121140f0030080d00c414010f007a602d920020384030b0741c85156210 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 624145719 1250 624144469 624144503
    0x80d0e010e090f160509061b030d1b0e09060f15120406020d05060a0b0a030b01050c1f1a01020a1511030709060e0409080d051b1c050105030a0f 63
    0x116a596200764000e200390601d04100b0401c4211203c00d50300006a005119015a1014060000c4403014000a0036451078020107010900701d8101000d21415580403c021410a4901c83d004464203132104e45110504000c0500c0041c003039490085070180900b400c0c5d010480e8a5907004110001498190380c9a8210340d0210700f40e20b90391003041a17540c980d80d803040602040c8600f5602800f544421940100055101d501c10032282000c2d51054014044040100c030050503ca50800707070005206040403420310544488643c18800020410608003c03c03440001114207980601181d141904201290b1480d401000035210511028040c042c140740c8008004011001d600582d940c5506d1144c01381c60341400d4100804003150391040310001600030040804030300c0c0a11a01d48400d40c40380105103821550300c0e40c14068031000740490060300101840300501e00d1444020180c505100c070038440040740b610b045004441c01a0001402a0f10586015001551180c0d2049226803c0442840b1004400c = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 624146969 1250 624145719 624145727
    0x30f0711030a020708151603020903030f0a11070b0c0304170a0206040e07140f04171e03070308090a0807080708040302041505040c0806060f160b04111207080d0e01 72
    0x1000085407480001085010140c1c08621003040e11010b00c1600d005019003003918440d16800c0c6d401c00b620031180038003445154040c1d40203101d5040040c00707503420404283c0444800b078000610700e50102e5020000e4407030300d460030304c6043c0141c941100c01ca42071400360404a90780f0b0150340100c040360084c050050b0b510740001c006040329107038010300075982c450b2a1690314000c04001d45021000c40c003100120381caa0700364075082c0c0320007041c102e0000307003400d00c0d008041e110709260341c01e800c005000b07120380001442109005c072480ba00c2000300039566210a850010507034100201440025040070741020b000071504012648456000400a61941064280911203200d43c1d40004d51092800c165080146601c402c000c040740c0c4c00700c4d0b00b0000c0b01c3d0a0300c0c007a120442c04070340555001d101080305080c5201d13804050203c95680c5001d03180260386176075409050001c140c60907100c00c129840140d44604d4121062900715010401900e0b50350300e842e1071940e41e00494149070341485803c0b106400c02d6445 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 624148219 1250 624146969 624146987
    0x100f03140d0309120f0215100512030a0c11120106170c190e06120d231201030201080a090804081605030f10180b0f15040612082d090a050411030f07 65
    0x8a080c00f0b1f610b608003181e16894114a6104d25405103c8060000150410200640304840211340b145240c0c1c40131569091b00395003a011003190701002e59198028409000d01c140c1024009402d1009810001b08400710b1a20340b5940c00e0030700c5100c0014580710600c00140035482280c0c000508154140c0310180001e11f0942204146071440c442c1540d03940b0a5640102c582c5d0060820204403400c800c5001d03050b403640e20803030122400b28200e18004000551041040c2a4452041034000400004e140c4da07081300c941c0207030703c410784a500c40124444000c1c104064075008103801c45c000c01c8a40c41c80120b2985940b1a0b50b0303a9004141c1d5170100c1c1c0602e1400100600c14158808500c1c501450811401100070006070f50941c0c050341c4013100c1003440e042601c51041a40c41d82c48142245010036540c0311840d90088200d8040d60307080800c1100320850101d14400803188080e20a40c031901c14800f4803000d04015808640b050341012038050383c0b003c6140c1165080030f602d6039070400301d540fa05001c0e503407010 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 624149469 1250 624148219 624148243
    0x9030f0703080709170d080a151212090e0a09080f0409090b010806060105090d060209030f0a1403091003020a0201060b1c06050324100f03140d0309120f02 68
    0x25002840ca42015844808144241075139181d5442d000c1d20350020102140c840c4860521039480641d20007081c0d40983c2d1960381c400c00c005000f0500e1030740c915030f211a00c0556840660719103c0d4440240801040f044141c1c04070030145488070b203903442d210383e4004210b405032031986010b13500c4150901344210b803002c5441400b074115102d941c41c2da0390b80f240c50041040c0c01c03041e2056000d85002107007a40c00854200e0044070140c1d6041c1c00d05010000304100c11901000486132a5401c010958642d03e042c42200003010344032000e0401840281410a40d5140c40102055140c01c00c0023585400c1d520b91103900440d103030340c0c9030058070b0385561601a0f00401c80c40c0c100540507100400c03803000e80d4072051020504c03010070718400d0144607641c9060695602c07074040d00c5e00b07000d590301621264503030954041aa00216119040741d0056035441865418000b80e00166200100c000c4607181e02c0c2003c01c02d10350900d000340b43c2000403241c0c9440d007010f010005003414040041010b10b00d8065403080006501c0c00e0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 624150719 1250 624149469 624149497
    0x219110d0b1515040b1308120a0809010b0a1403031210090f0506030601140a0b1801030612170c010b04020301080c0102010b0604060e100c060923120d050903 69
    0x22026041c00c41c0e08060889200408a007018141809410040c00c100110015182401c1c1020b08050507540582c0041d41c07203424810300410002a2000100150340f422450100340a03a80c4000000003003110701c0040c1b03000c40c1681000d0003280d2948070503e00700200d0350000c0445104010308000281544180c4404501094110013407200d5241e90311249011a50b416501300806507001c041d01c07042c0c0358101e8080e60b00d03401000c010440c00242c0e402d14002e441c0c1c02842c450215490301c150b010701c4e80291101c805a07840e60b03800c00d1815601480350cc009010040410308441049903100c004150342d121040824903004030b40141014401d402c400030b41d000040042d9207940c0c43c0c43d0103a541d1401020039a00541c2040302c015400d050841c111000d480706030f52681100c9180405000042c145003d10f101003203001c4407124040f9180780309518180340305500300c4184507601004e1070800790192031000c005400c000c00181c41c0c04000310886408042a0001182c140d607100031560940c010100446014 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 624151969 1250 624150719 624150739
    0x4180f110d0e0c100203040e060402070206040f0e1803090f0316030f0501060b03070c2d08092d010804050f07150f03060308040902030925061d01021911 67
    0x5001250002104041c031a001c803100d2040c11030820440f241380052000158008000a020340802c0004107544008058005031505800e5030200d2400c0d8007a81c00021000810f100901040d0708151440f038118207001750342c0c1c000611a00c4016107c0c4030340c455180c4150203902c00450300d901c0c203010144055900403000710300159682807010f0402c504507c200e5055190a078041a030307003181004c0d40d010706880e54035041c010b4859507070706d11503410381041c42105c0b000001d07280103282543c54105078038520443c0026210404c03442441075148a1011522980310010701c0036005000400258112400918203031030180c640d828000d00b400074030710780711549000381080420301c40030a501d81042e4581c0c6541d802824404820110101da046010080011a00b00010010200541c001d1508160302c1400c3c3c403403520301c000a01b00d591001030214201c0341c4d4a28070820017560404000c8041442050704040d41c14481c800003900c07540107001c4482c1400d041e0a010040c072123106402078840708060962500 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 624153219 1250 624151969 624151987
    0xe06120303131a0906070f172d01060f1b02131b0e031905010e1c110105130212070b0c0109060b0d0f1205071b1a04180f11 54
    0xa68202032000d0f00c0480b00070084040411000c0003240c41001510b024041c82d481d5000101c404d800e04032080010059408d40d0441c551054000e0b16014034800b0401041021305a41041c40000300c1201c1d0014001d411030040000d140c06c4000b40f4101d000e11700d0040304c003204e010442d0344c0707446040c00060340001e034500403c0d0245a00d81e210aa40042c955440500e2410f201405c03980070781d01d0b450164040d0002040c00c2020500b01082d5641a4400d00011503001048107440d07140c18080b002c0c050b001c8403603400c0b001483e40c0100380e03d08032921540c000d012915203100010b80b2100d040200a00510514581c1400b20b8000d02511002e000813803111992400e600c4201c0f406020643c0e0140d5552b407910307824501e0303403601501c0441802e5001900302140078164844100b85e580081406050000400541d400603d241040300484c9400c4129200940e003001030300c1601c2d43c000600380c100010100401d021081d00005060620311504401041051901d00104003412042500251180380441d090034 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 624154469 1250 624153219 624153241
    0x1e130306140106170108030a0c0c050910050909030c03190513090501050907080108060f04060605030f0703060606050f0d020f0706091203050f060d030e2403160512010e06120303 78
    0x304031051680e07204000032a50000c1e00b111300c000e1081968030f901c01c001c403006140c01a05058406401070403880710302613942c4041903441d1800c072001c1420460b140414413807440c1c0a10001e8001c49184004c500f800300508800f6528420b0307030314004014203104007005185120380111508403d0320a40d041c400d958641c41c1ea40a464207009242c032803c0300c000094616841010924103d84200c001458940c80b042c07054030b4003003000307807003600c0b01500d42c00c0200b401e440822584503100c100030018940607145040c04d604440c2990000c5082040401c94402103241d01002d450019286a10040c0d89020341a0881c8040c8036401e0010401404c7c080400184641d041480c01c7e00c15251f14240600c0d036454294041007071080341c482c1da020054002003030100744035040201c214040a040140c1c800001c181c010980481c414000390440720000c02c005038085200e88100ea0440b0381d050080c1450550b180007443e100b0140a9404100b2608002403140e542d50303040f1031020792030360b000d503076403070500d007006039 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 624155719 1250 624154469 624154471
    0x3030712090906210b100503060114040f051501121e09020301051315110c010212040c060c0b040605060102251e15051c020d09171e13030614 62
    0x403012a141c144001054604e481d1220810f1500a481d00c2d2000301c42e944070030384c0010240a501c00c40717403600404656610100107042c041c0c4040b94040c140d0490f144100819101d0000a1201e4035040c541440f10084500341516890b4209007080140402d296514400070884149001c2c000058603569030304115040e480240c10500a0700244195590360210b030000b95403100d0000c0010022815600f0391844030340c4028180315000480d0303450840e82c445050f00f0380c3c100d41c4140f4801150390083c40100004030712018010851801c02c40440034032500c81d0780342c2003001400079000342c1d20340c4000ba400768070034000c840c0c614001512110940c64080b0400d014040f050244640340582c82d50342114500d1441003030012211500c281c00341414401da01160207800460b0140b104440350142e4007415001da0004e8075000c0d000710000a5940850f04240c5442195031203043d098280400c4500d102e8240160300c0e07465407150b941d25a594200c00109840300f4041c1c0c0e4000b4242d035191128600d94004105042 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 624156969 1250 624155719 624155729
    0x210b010311040c11120a051318060e01030b07051303241529040b0304051c110303060d02130c050c0706110a0b0c090402070308390304020303071209 65
    0x1000f0302e0038800e809840c502051000c1071402d6014000d980484d1101c14020101c1c1041031800c0360900c038180c000017040420340d8000314020031440421201e1800c45204080003402d2100480d010707545140c495080c4003078040c014800700140042c01d0400e84045882d000011940140402c1100620501049007200685007844c4584d04103c504503900351503005444c19a0916100322100010000c80c14980d008102055411442d01303000c0012a50301e190f000d14816805079001c2c240805401242e2086c201000104c08103004142c0101c103d004000016aa40208196800d580800042c000119500d00c15807400740a60704128155080660010280007175404443c200d80310a0b444241c02d59a03c100348421054507442562071030082020001d00640145410340c91900c0d013207101c1c020800340d80c401101a00814040300030b000c40b0041c01040106524400c80446403070001700b1604400700c41c55404c91034200a0044040b5040d56028030403100003983c090030323100034980400005007200221b0f100c2e17 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 624158219 1250 624156969 624156971
    0xd0611160b040c0e10330c0302011107030e04020702151602120706172d1501030605060d020703020f010e0708060a0203070210020c19080405130213210b01031104 71
    0x8009008641c55040c0390280040c1501220b079a818003888504d048102600f503049500d44d01000d0040f142c0c030848100401b5550790b60510004000c0c200a425926145a00c41c056082041403d0110b07500082026859004a402681daa552400040c0c210382007a44410050a000190400d10b100a4620051014800c0e1031020803110101e86854039102c1d41d00c102d90110360a002071a11080c0605034040d8070102c5c4624420044266201d1407688104c03c4407200724000d07400c020b00c08100c41d21003614131580024601031244504000c0071030304600914800c1d294007900480c0c40d0b002c041c002e01c0586064030076240204403640180700c81590300c3d0320b54800c075041d42c050b0b02c001c203800b039115000310780c0b1a4246400a250046d041060440254018501c0c813103a0b01401d588000300120740d02c11050414002d0030190340710b41c05c00c0c0030044462045400091041e204105019107251108106000c89030052001840381c01c070f43c3e80035034508000920041c117000d0034500200810044c1d905059101c007007650 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 624159469 1250 624158219 624158243
    0x6030d030506030a02100c050d090303091e060302030907030803090d03060b0a0e091b070b0910020a0c080304020109120b0f0601050304030c121404090509010e0102090d0611160b04 79
    0x15055088803000e81d0043c0d00368002d4400a0301504061032040b88640541c507021290f00c4031511040c0c2010403070580040000d403d0034040042c5a0b11500350006001c00346034040b0040510780003001d04019510800003450b401100046103482c0134070010004640004085a90340340a49840f40c959082e4802c000c003007850310b00041100d010700c1c0300303984500714545c80b00910881c9072400c03c0100c1e200200201701c0b4441548042c200d40d05000060001140314070202d88940c2031108400d07041525941201c1241803060003131103500c0358003002d654541c50700520a03c0e9292628001214881c80b80c2c1c200c40c60320303480702103030720208100b005100e4807441d4000800d030895100d90004448134441a03501900260f00c007814080490082002d2820040c15401c143c400e103640c80c00312882c030350400c0d80080f94807580c030010080f18400a0240e0460410308600031441e000d84040050104445070700c01810700e543e1240011030045481c2c08840f00f1048034150a0f51802c06460003000f144d1007100c0c12100800d80c14 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 624160719 1250 624159469 624159493
    0x515041a030402090f100b0d05070809120d051504021308010b0607120f0c060c0e0f0402040b0a081008010213090b0d08030a0b2b1205090a1202030c031002030603 71
    0xc00392801643d00a000200e140c40710100e0002c5410054140014040e04010000e420080d080007800c4141840d00045030616085902500c000ba0007044480c071a0050010031581c10070b03880498200c10089040050b05840780d0700d160b80c4c405135255000f60468030005000c0f103103c0415503410201c40d000802401500a42070602c0224017400300300604810007200340002840c003d900c013000030302d5249040f040e0066281ca03404c0c29104080300a60100d007130a0505034850610344440408c4d01c0d800d95056261920380780040e8070a115001100c020000081c0224100000442e050401030001100039034440a0b04400b00c1641d42c0a403180c120b42d6460250307500520f080095450098a4200117a075041da07440a441602402d08815142d511003400407000d485448040101a201185100c2c02c41c01c400f81c91500d0810341840c406800140001031007c04030b01d0b90351420241c2070702c0d41c1240c0b041c800380151011910b0084918507843e031600901000c01c0032551154042c5210b8001103045500802c811 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 624161969 1250 624160719 624160769
    0x305120a091a040f020a1e082a060d0903020d030c0f270e0412110f0705150c061819020105030417121306060e07120507020106051504 59
    0x40c002014a00700b101d1149882c000b06106907401070192580b0280b11000d5400542800c6003600442c01c02d240c0c64112091000d070783e90849007c0c0810724020403c00c40c4444445000c9480800c46498602c904582482c054844105441c880715146038140500d490b681313006522001003941c810b00007490500360a002c50701c030308240703100d04c0344940752a043c00c0c0c081c0b140925401d00489090710f8610308070000048030b0351400c80301845240104050440b420341d89000618910282c0b0320003030140d1201d50750001010006c00e568044030b82c1140c0e0f0f500944540d64058081d0302440c0c614210a00072031040005240704604100f0140410030107440c0c90080c81c504881e000c10510788003900040080c40010000781030340f041751181844c9030b55514104915003000704041442191f91261800d5245030300c0040080e24010140901042c0c500209646000d140003040c2e101110150456039444101050405001303501070805000050012440c4059102014009500604c0b802c2c0b00003103031a41c8401c82c4016 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 624163219 1250 624161969 624161981
    0x3050f01120b06010201020c0d0206040213060b1804150602010c0f02031c050903040806040309180b130515090c270607030c050c030618061513090f0b040305120a 71
    0x21008950125548070340b124405103100902d041d0541d903013080082040303c010014910310102c16802007116141500c180a41580c68030b074259040ca041c68014440c48269a041d203500740e0145030600d407140301040005001c0c01151544c21611810700c40301084040d0306400a40e03000b09107880d40e1300c0ca0340403070b41c3c2243c0d81d115440d039910944503c2d103195030094204d034002540158085040f0390400380c40b0a4207905042e001d0f90100c01280c40c10100300f242d075021540e021050040396000300621005400400d1034200c20703c2d05810410b50f5000002c95161006181c003850210140450500d40b407c4103508040b0343c4a0319820801c0c03a81480700e560505000406200840d001a00041c02c0c029590340036940141482d0b0b04a515000e0301030114501d49081219a11a442500d80f6801640317613506101d0030b0400141085011008003036501d50309840302d629a01610008840015000c90390741000520a1100f001c000c10441c4004140003e050307000c0042c00790008280c030010907035121000e6074001c40700 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 624164469 1250 624163219 624163229
    0x50301051305030928060201060e01060309080a270303120e01020918070c080c0105040317070f08090307080708030703050106110a02040203042a030c08070e01050607050c03150703050f01 82
    0x100821844c64242807121102c1103140340140101090b4000c6001c400f8554210703004540140c0d51800c0030486141289030380c80c01020141000c0045100e680c46034205840345142400910648410489070582e821148091509110384a02e181c0c139200d00d001020903142c13082e00342034241003045240f29141d0606c00c481409400502c520441c1160004108031a00e00804050a220b156000c600100d031a420041c00c0e2600800c0c000120303454540380183c5012401070560444001c444200506d0310b4112038030342c040c2080c03400d04840b107603501c0c1c603103038074510501200404464000c40c2c89400c220012000d50701a9210b9141840709a88503242142c44201c9407c0d080e00c0e07075001c24007110150a255004582050052024020300207583c1c1070b2250101107042404004001d42508100740031000d01080c1c050b008020103820428540106104040410700609201c1d150002e40001000300421001c0a4210042d040d135042d0f415441000d24601001c948100c0800c0c02c04002400300e0520383d04e0903050794 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 624165719 1250 624164469 624164473
    0x10b03010c11100b1c1a0109022d0c07030c030209180730030203090301050a0506010203071103031207050414150d051e280603050a03080c04030c090501050301051305 73
    0x4400041e01001030300c10307030045541291808040c400b09102e64004c5d040d01c213009555a43c612102240300044990b016808450a20320510032605c451198a6080e4422410f0100408194101c0c0c5a0381006124225408080341324825000080050020008040700c0c001c603051012651082c0006981e010440d15612598208030b07420301c40d02c800088030710141c2c4244c140078105800071680b800d01816407ca0142c02503840401c11401501e024010303650720440c0d5680c140042c1c1001400070f9503a01039070300018140c1c0c40c0c8901b4070350103840800540b29805140200a90203040c0204060400c0d40320f4040d0038400116a01803034140c0c213104000025043e209001146009041c445283c018407020708650240309402103010354400300400c08601138600204105940310640381400c0c403103c50154011702a60900034100042034022605e00c0010390141810744980d6200445145c00d8450b68000410b000710841c80450760b03041c1da502042c142c580c194020060782c0c8030184001200420310000038499 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 624166969 1250 624165719 624165733
    0x71a0a02030f0703140d02030108061806070c0f050d0e03071e03081803060405010e01060f15050705030408030301030f1101051e090a26061003050703080315040905010b03010c11 78
    0x40c0e00c1070801010450f0117841d2405c0e45280c074a0518031158010032500482d0398001c801404110760601100d03070440440390024542e1000d07404900d494040061405003801900503185090190001d40095403941c41f605680000e52007140c0581814040100503010740305075071000c00d1303041102ca130882c11002007006210786540756a4803040180d00130007692100c0b05d5800483c5046850800a0324040d6102d41e00200e000c800401015085841c030364025804503080c000d04101d11000710842c1d0f14524102c2c034103a5039811150419078030314411035200c034610b44000070001042c000d000c1d1800b03015030300c5201d060134025010300045409001321038560714411007404060060741408401041e0301c0d94082c0209542569480d165034000a002018969006d0b50102d102c8202d1003d0041680c001000b07076a56440a0a60b10b51542e90078060000500001c000001704075541d252040411268200030010302c1128281d00c1e185018044010302c6a00a41c20005040040c03030040b5038083d0b060345501700078016 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 624168219 1250 624166969 624166987
    0xf050d140106112a040f090309050f0f0d080a170106020d03050f06061902010b0402040b0c0f07061b0215040303020a170406170a0906090c0806060d030c020d05150108071a0a0203 78
    0x440d00010413190780306a0310400240842d04502031100342d64040e8031460061450001401126214007100c2e912a902034040f042c1c1c0340e66603103100e100190700481e03e0b6031030b0480e10006858050450f5120820f00740e10000004003694006998032a03240b00e990305218030f0301c07030a80800480300c041d910607070b110030240b02c05050304a41c6503900c00c0075401d910001c0760030740712040800c040364003641080840c2440000e0018040d00c1c00c0100d004071000d2080180207640c60040000c2000c140c070f0305e8140003101078221140a565a04003032688000741d9840c840c1d6666524500617644c0c24003848222020b0b0380500c44087d0500c603074419036040b550f1035161048141000900c141103158020700030030315a1703550407141c0003140b110701c00c81c808544182450300e240d6080c6804a8502880142a02d00c607400141d0345500007640501d1070341c41d465050b2580341c0307140d0851802d1402e2002c4403801088000e81d4500004500c8030000300c6200729500009090380544074213051034840e10070903000d0b0340981e00130408041 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 624169469 1250 624168219 624168283
    0x4050117040302011118010e060309070506341506030209010513020c030706270812090a0b0702060a0e06010b1206030a0c0b130504090b04030f050d14010611 69
    0x2520074820f100009400c84030320b1204003c0e4000e050f40e4844046800c000807465604288529034a0404842e00780c00c40c0b4140031240d41e655018020b80c2c0c0958008561000c207081d442c1c02c0c3c072602c001401007208034044144105220024000c506480003c80c5204002c14a1054801c00c0f060b241c0107000480140e0900d028007848010300d100220b1401c1e4200244410614103101804c28030741314032030124039030522455002600c40c11040c12070715400c80d940c142e0000f503040310841e1103031b03a40241300360b26541c0e9040c81f06080c00b1807200040c0034044050104401c0e550b011504521600c0701c11020020110780380b80719642e40c1000d00640f2100d210410002e021008109101035202000800b15010b681c1d040d030f144016070b4655409010081004559003140b90b4034440c000c00540b50968080000341c5154407040e400d5400580050240300811103911003003442401118946d10888d0010301c003a501e201140c800100303091080a00040d07081c0c000c580481c4010690043d040007401c2900899403a58036451 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 624170719 1250 624169469 624169471
    0x30509030a1a0402040c050309060703110f0d0504060e0a03320c030a030605010309080702040f0b0a080a0606090b06031b07020a15091e18152904050117 67
    0x503a05114a0030980c0014190040c084503102a080c00300c001c0d802d0501c1400b0980d1890100c0074140241441007180000d0005a601d60100880c03402041407000c0c00325080c10b030b20030380800400403800040c0303e0708a0241508200c3c015440384404008110507041c100340c966203c100c0040010726040c400d0300d001c0c00d00d21801d0b0031103005403c2602641c100c00c200d04416a0003483e0142c0c00d6000030400801c526007511503240104000c0c01c0a00c45400c86a441c2e1445100d81031009104e180c1e50226444103007116800011114409494041c54680b030b8040541d454000d8242190300504120b008a041d1420740a107441400000e4007440c1113445520501c1000846800000312a03e018051000581d8846034110700a00b29003456202e440c1008400a080c842c054200c2ca824500302100280006440501001210f00c040c3d1607090012410880d88098144482240760207803000b038010425044800d4801c0b910220a2003103200c00e1407007120004540100d21a050120380301e0800069040c21040c503032 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 624171969 1250 624170719 624170737
    0x22b060b1201050106111501180213090606050c010b0a0e1303030b040507050405042f090409050a030206060109090501030203120a031b02060105011103040b1b03070c0e10090e0a0305 80
    0x15000e5168041c040d0308451090b44100e0004400301c10740b00348205d0a110800b00a4907031a004071556041585420116440c5010034003082d50020305003d810b1900711030003014140d01038013841400d03650f1500510a420482c4008955460101002c0f050724200d908803044a0950f2620003660341c5405400c0000f50720190240c0c20326885080c2c404e440d6855200b10380c442d01c507035180d05894508010500c41120b0b6040f40c0900d014000701480c60f440901d2000034490650900d443c0d0369565548400303c2c0140140c007a0040891250b600a54101900820494800d03582030f40c43d103891640d01e01901040d11021310000e0b42580004500e00900b410540c01400250114140807400395111880c14401c03010f103d11100041e0005001444550b81c131411110b107900c4880d0045003020b051000200040c440d40504400c01101042c0c0d80807524000c0c02510440ca8000348040e14003a07969109150240c0121689440b030140303054007050869840c41480d168068040c010f124030365081c0c0c4c064170103900502003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 624173219 1250 624171969 624171979
    0x5100506130905280903020a0b1f030b07080606071520220914150a0302060a050d0b011d0118050d0606080606040516050702210307022b060b 62
    0xc50956038a014080c055000d0302000c40c01030884081e03100c10050f00300e13800c0325010b04080c2a00b02090340042c0320100a50404042c0f5400d0b11480d1884540e00c1e41002c404116240410000092040b20468170b48680290f843e40011951030004000980c4501140204151508041d011700141654000302c0201c501030b014001c8003135440c942c40c0707070303a00034076010058550403551031000f00c40c0c2004100000c1c4080b810034081c0c000c5100505107034000080c2041c21300f852080d1800100c0e82d410061000943c7c025140d1595420b0b500e400411035400045140051410101c2952180d44600e02d040c1046482c42200319408403150011640b03040f00c400b03107070000c2209003404511542d0300304040f9034441c13080341c000948030700c0e20343c5142c04c090340101014031491901041012889641e42d480c410800140791180c0e484a091000560ba0b100001340100c085450070302080c10514000000e1254134001c807281030100c2c1012441c1603d100c40c54182e900307035401200a0400103140f94110301c1021000500d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 624174469 1250 624173219 624173257
    0x903091710091b291c110d0b100c151d030c011103060a031205070f0f0b060a03051c02031209010b090a0501150c1b03050d020706020105100506 63
    0x35000306407500a9420780f024940d20403140c44034403401c03045100409407000c0074545441442ca03101e540030070410314080440400210146403140d07542001c0030000e60000e0410080004854516464100d1040c6c0c03200f20346043c14600443c0340c00351501c03800c200b1030b13541c8550b10002651030500c4000f00b101d0001300e494403008503032180444108a4001815003034010340d00c030b5180140090035075259240f0102031034010801e0100d9511030141c0c803000d40c2d80000c4046000b4100b8201156244101031000e48071540c8201030a04008682c00400300d903034001e820105440e240c0c1010010703005501d100c001c04540c45169101101c01c40001c90351803100c81d50050302d040c01d905e080e160041480803203182e0000c0c2d41d0303401c0130071152800c00440e035044080b54500b040158181002c082e1034440c01c600490074880740710420300400941017540d081d012400104408040d5580c5803040c0d0701d86280800e10058041c04a011070b49500c14462244240c0708046004d40c20741c0340400317020380340d0301541042d9008040b0344 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 624175719 1250 624174469 624174493
    0x312020a0506220b1603061a0702010e011809051519060e0307080f0c030d0f0f08040c170d1d031207061508031306030501061d04020c07030602090a0909030917 70
    0x2500600c98022480b4101034460b00b40e00060440e501e23904001c00f4408042c2510000d60540ca00740c0e4202c0d542030908101d4000daa10060712043e12105040c40c48250310318012420341215000980178072526081c00910800d444108144503c03142844951408421030070410389100350104049048042d042d24001902c4a80c040d0900040000421480d405000300c40d0486c201040075500203107543c0341c652281486040000c0941040002c400c00f0040d01c04003040902186908260040410300040c1c0c400054292005460780c800d00080400319804030151980510580da06100c8914000c010b007910341c40340c00003100d0700d4024010688005985003034625400100400d894003810000c0000c540380c03641d01082d920605010f41203c0c04050911004108081d006241d95802e4102c401d0014005070072403000c0703002130081c4080303d00a031241c1c80e800402c3c4840c682c018004408161801e403c1e990b12407500d4010780b000680000c0002e902c1a20400020310040c401240310462141030b60030526080d = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 624176969 1250 624175719 624175733
    0x50d1112030703020c10052a120d0f050a15030308271b100f030e01200d0b06070c0302120703060c05030108010c180501050c0a0204050a060312020a050622 68
    0xb801d08a0140c1e0191034445250301d80140c0703411a074407252500d0340c6402c2081038004200110321004900115150000010f903002c14000c1c4907100840310502612030641498400180c045110548006403400b00840c42e0300d07100780501c01c110300c0e060800c44419440e580c6e080758800c000400f40c50080c0707048015001010300044003492550350410040c40704044250740421050030110305184640b281e5280070900c50b8100c05201e901c2c0005040004981c0800c1c480c45001d000c0100e003080c050320040055441c0445840e016000b003001111040103480540b0050100b02c1c851040e0203401004c20401c02c0005180a14402413100d42c104142c900e150f40e05d40d10f0308284e650800a000115030007000600c03c1c580309105940c1c4198180c601a0810320b0719203800c3c2607030305180c0030b05810483e00203045001043c1c01c001c131b568034070f5001e0404c210500d03208030020000c065074002109c0f8000d00d02c0804808903c00118018055000380280c6110340f81c45004a280e03429a060001e2402006d00d5610040380300 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 624178219 1250 624176969 624176977
    0xf0112060f2102011b080c0604081902010209030a02040b01050c010e01021206032a220c1103040605120a090b070201150f0e04300207030219050d111203 67
    0x305880c1e4101c210300780003000d40d00001c410100041150028120400b60ba480f100041100c0d4825060700d00900513400c0581003481400d04804107841080c05000800040d00c000b804c040c41e1800d1074402000440c079049007030744a08a903c0e40d16030721040001000d4601580f0003408841c050411610b0006500c42660075a054401ca1080507540071900c046450380c40342d240c0e684042d040303001d843c0394011030140d1419011041803082040c402e4203804071054440307c2c1c0007004080034142d030184c0a603a034000e040140c08076031031840010b81002e91342d0703c11000001c1a2402d0302c00320386407a4108044010047c80c44203000704150314450316404000049020f020b0614007c40403540041004251a41650500310203540605101d2030700e40c404000444212126030b4109078000440401040d0094071006010603020041c2444404000900761240c0c00181c0320044078401e56070341d0030034024100001210301c1688206504035150034200400104c4065501c10501001061640781e246124901451070700 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 624179469 1250 624178219 624178229
    0x10509030d0807170c030a33211205030a020d06030503031f060e0d02032d0127020d050114010f0509101a0310080607030f050a0507020c0f011206 64
    0x40c00c1408491984a840d0450b400440354000c004d90130482140e40203440006c2076414455a503104034060449200804051108000342144205d01c0d21112480e0040291107900811400e040045002551500090a40903000059010101e000c030b00b042da0294402030a084500354204403111243c89113200f0031000c0d42c0580e00454603803038140c502007205040d03103000100301103103c0e40c00c02c21030754001202d00020304181d6200c28220104d1010034070706000d2000c03c400840288007188d081902e00d00c90011001d00c000e000b07010719050707201d05121801c80340c62421000f03a4803013008009402c000a200c0d540c1481070000055040e0403a18000b85070100381c00001d001640d1603005c00681c43c2081245400041c01c0b100c1040462410000f03410701014180c2007100a6804400117400c006890180c03001442407001b030b03031058074003200001e000b010140c101007946460000802d0b1220001d1141c103114007900d4009103420441c1c4070401c80f0321130061716694104180104a110380492500a21000381 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 624180719 1250 624179469 624179477
    0xe060a0e040c020c100507060204031203050402090a1808030712060b0d0b040e070509040830152d0a030501060611280c0305030a120518030304060506010509030d 71
    0x1280c100c200415180107650401c11540009003041d11a91590038011000741d403410001d64500180c074200000e80125400640b03110701401d981c096071a05a00b109100b1442112140e2103903460b13100c3e0f102290150003030b21f0040746c0783e001d400c000038118a00650b0011458141264074032244c1c07040d04203440194002410003035010805030400e034000d00409207400800c440601ca405a035000695403070220f1b101c0c051045c02e21002040c1805110f0781180c0400140c2c501e032101c0000424030b40d107159507120940d810005030380000968100c07507408441c00803d5005050307800c40002e00300c5030850150034190380b0315031045138043c201041e950264240000e6100d0350011910529101e00a8480c00c0e02c00c03059011504644024248030381d503194040b50b032021483c0c0d803901a40c66400c004004c0302c0c0e0398000a1180c440043e20302c1210740c0019410321002140d1000b40282c0d03a9508604030f28004861000c06590f100b4400f040001d12141c106552000701858558200069040000c0c43e002600500002203 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 624181969 1250 624180719 624180737
    0x270409030c02150c060a0518061f14180a060f0e06120105220c031a180f0d11121909050409030909181407060801050910060f0e060a 58
    0x5042568003c807141040c0e450359818207050205040d10f4900080805107020f03a07440009030780c4082400300c9401c00640300200e070918034000c0088100f80b00f03130040550060300442e4000441107107000321060303d51001303003240e24044012513943c00850006441c0b50a00d0b900c3e6407000c50103e0b6000b400c03c0061088001d0407005091003400c2c02840084280041c40c282d0600c0b04001400c08060344c0c000c55a00c0b0000c40e424401c01504041c0100070450304010094074580442038141d81c150030740f035401962106919260002c2207039141d0307503030100104046000e4001006880405010346c02d80916248814160350400707001410b408a1980043c4544c0200480c0c07490b44114260301003600030141c802901c08101004130f64074083d043c6640391007903a6601d5203030034130212800307a4680b90940c1c140e880202240048800f11502d0f03141ca80c1801203400040d0795100015080c40d08840c0c1c1401907201c2100c050070541840c9080345c41148070707132000d02070010903a209080d54a402008100303021441d62076081c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 624183219 1250 624181969 624181973
    0xb1021111804141602070305060f19050405120d060b040e070813051c1701090c020c2d031207200f0907111207050102030702071a270409030c 62
    0x520306064035014019841e040442091040c040b0300f0f0fa403c610020728a580c404481501240713088503540005017a03020700001c1c04a086000c01c0c14500800c44101c03000c0c2002041c2d0070b20f80c200c90080324007419561200311101600c8444200420504208030f101142407a180c000d00061680164008021162a90108035489500130101a0808044402d6020001040c1c0740c1d04d03690f4000f035030107805003001d00c110000b05901030300d2003843c280d0b5855041540ba41c1d4808115005019000d0510054092041ea05c0002e1400c107641c40989021004000c043c02c101200e0482c0d120041c2c6400e94062181e6801800184c840d1400b4000030b51242c89401039480302d0b050b0600307884911008460040564541501320380d565480010383c481a84d181000c0075400c00c1101904d003803101034520107035070800281c05050010640041d44a2642a021100020fa40ea0b4031348a072510800c4c581c0c0e0704003005101c03041014003e5120030b0001503000c1d1150100e10094800141205e00c3c940301140070911803011041 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 624184469 1250 624183219 624183247
    0xc040302040506151c0f150504150b0f0d0b0a1205010c05090d0204050a062c1305070311130f15080607020d0c1e0c090b03010b102111 59
    0x1030301c1107041d1a072618402c0004c1032410507010b0039410f5040110f001c14490045255680001c41801d00d440d0184141c1000e1156010703403000c0307030180b83c1c0500d00b40300c0b030808242d05095581080b11010030059241c0860000d902c1d0980e0000c015080a49856038240841c541e2805d8104c030182101c2041c0100e201298a815400c507482d101a034000e0050500410100b0790703441aa0420441d015280807906650300c0501d040100180c0d000383c081c104001150307442c40c10006a01c45c03c06042a40c601c8410b4840d000c1d0940080070300c2800614940c0446c60502c006409426905044940545060a20300e82005282d0039100440c0d40501d00701c2c1d55005034480035140e070b01070740010070703820000e08101d05003440c000b903c0d65014104601400343c1c14014204200e04071114885c40112414000b004040314034182c4860121407044150031800c09041c502d00d85418820241c1201c0003e002820240103c0c6083d1001b03d883c554840a030b111301601080032031218000ca14245003a210010340d91121588040 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 624185719 1250 624184469 624184471
    0x5010b0c01060f060e010c0203010e100c020705030105040b0c07080c120a0219020112200a09060f051c050a09060e0c040606050702030a022e0c0b0601111c020304050303030c0403020405 81
    0x200190f240c25042080a41002990030048002e1030400d414aa040c0042405410325820000b0644a4208800900c4016520583e030b120100e9080d240451340d1901050700361781064078080c1c00b00c060500030030400501d5000030154280711301265410104007c1005040144c011031078401548009015840c00e07a06000c5c0050b0300210000d0301c0c0f10228a50002000404084050500d01e07648803a013103052401c08c50480d18a07002145042da9030842418003c20307980303440c0300e00804180040c207002c110078081c005450150340240200603008100303075100c102500c4c0140203030b030300c2d40da4500d1550301049803070141002c2420a00c0c01003503040003d60602045034101c3d03004204000c002e1254800681e8042004901e0980403070700110b070440406803c040114284409c084101c6850744042404d540040509859500842a22100d03076107250040d1a0404004045a1590070075044a06461103040c21264814002d00c1100d0074581c542c40440e18552058821407000000814100308500e8280241 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 624186969 1250 624185719 624185729
    0xe0c040f020a0e1005040503010207110f0303030910020721031e0c090905041a1306050109110901111207032a020a0306050c0d02030f041a1611030d05010b0c0106 71
    0x7146828a035250080c681c1a040340d40c0d5203d81018088044101c3c4282c05aa010b003100034021541c40d41d0910b400c40c2485019160300b4001c0302c4001d007004e01454040256842844070700c0c00391070041c0380312103480001e504c00b102c21145c20324400300c2e01d9011908018402c41c60034194800003622041800c4503444d1154415400c0e40c03030781c1081c000300d4000c0d500c40c85801c01ca0385204404143c1e84c072503150001c60361030102001074200580380204a82e149406000c11051070040c04100456601c0d43d83c001c0c10f48800c5486146044420800190306501c55840001d000501c48140c0b6030b4803500400c0200c41e1350203580e00384e00041c00401940c0303c0c254005800100480c2c0c4064004070305007590b001c00c044070158070001c1e2000750755000056500ca00700b812240c40c0c16851000315a20700d0301510048041c078050b2015203000c190b0300b29000c104054002024019042102803810103040101c040754000c440b541e0012450000b0b01465901302841e0240034047c1480b207101503121403010841c542110510341c40 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 624188219 1250 624186969 624186971
    0x3060606111e07031421070b07020102030c0711030f030a0f031a090403050d06030804062a0c0902070305070209041110020105070e06180306070905010e0609030d050304020d060e0c040f 81
    0x200c4410300c280041c5200c11a135012118409041c5c2d5500c0035801c10204854500c0503500700e1041c17116071240100100802c51042c100c1607850b03216428101c2c03c0340000c0321403001e840707403c00c0118003140306a00d1510266134000c049030280c40b4081046800c40c1c000541000c08281c0150321418072607018040c81c1074114406416820b0b0254500000c1c4074040090009014090006102d142900d1680c00110145401440442e41d403a900e00d0024400441e0305c0c562504c0c025034010600c0401c10803584807140c140c1081c041d0f0001c80c1001e0001000f0f62122000320280101001400b005803a0b80310301c03612543c0900301030b20103481d0200520015a0700c0c2500302d07085902d40420804d100381c0002c000510f510040c0d034010307200d90500750401e0f42ea60954800c9075140c8034050402074000c0d884070100040d600700b030342c80d404450031003401e00c03000b40a001500c030380c550040000e55800f241f040010f150b006000030054030101400b51a181e00703c070006580c149081c0c0280e00c00a00604180c041c003100c1000c1450 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 624189469 1250 624188219 624188263
    0x20c071d0402010309030903080c2a01021b0d021309033908120405010515010302040503061f0b0708040311010914090603010f02040b0315240903070306060611 70
    0x989000c1400288020b05050343c40039210181841075401001960b030049609643d504090541d81e510000205842e0003400b920741e1202c4000314102e213010056106030024001c8698002030f070351824102c1c11105800c05556130102c800350740e41d800c00040030b0b8001031001800d10400c1c00c00034650441c80c0201c5065880b41c2c404099600a4490321004402400548044607062407500d80030750f2045003401c142010f00001800103004d41980840c1c020001d1003c0c1d03901a00941c001541680501e10071298035800c140001125180303414141c00354001c1c54070a040320300c0d0f01c80009102d035800001d41031303484078004030342481007002c0a1419482c125007400c01740b5016240400c030b412042c0565071014014507101001c01c1c280e44094001048030141c0450039507d40d80c0352a01c100f11f9030012119016034088800010304542800783c003517209007130030404100ca54006070490704034560107011a16014421402c0001c04686d451003003a0182001e03680c3d00e9030f901414001946010b000682540c40000340d41 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 624190719 1250 624189469 624189509
    0x31615020d0e1507080c0307170f0603061b070b060609120d080c070f0303020912010606020a020310090302070605070f0204060608010302190e0115030204082e060f120809040f020c07 80
    0x1000c038690100c90705011b9552aa19103104441d002650721800c035011134a40300740b10303002c03a044000e240304d9401642122000d0340d662a054071540714a5103138100d0358070104030ba800031440f2200c2c0540e00c1f41e809001c80c0c0c60100703440c02040100c42c040d82d4440781c03a004020b803c0c010350352100100f6000007030340450600380304454888075200000304a000b41896400140202982c98003811607103203031480030003000703010f544400c0a9110000b9440480c030902820600d10b8044a00d4426003021540643c0100b6404d41050320503a6254001807042d81c1200c0718040180042e9614060300d406000700380d0b56083c0d25491807060140340103071210301d502c035840a02820b114110310500d00a04450a10f002101207a6114030203800a101d641c100401a00846e8020000c150512900ca2030b40300a1010441500e28600c8051040301c005025004881c44005d204100003c02a407201200c540560b25427450049280002411100100424440c2940114900300000c1c1c0600102d0024130f4100408510301c907180c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 624191969 1250 624190719 624190727
    0xf1501080f0c040b0102100e07060e01030203040803040f08041a0a082d060a090510051512070c020109080607090503070504020f040512010213120b150102031615020d0e1507 76
    0x820360b0385004a40d141c1051200c0c1e0310030042500710300c081400400c02030082d034426a8854420b0301805000c942441384900180d48a13200300e80c4541d810a00c1c203421600ca50f624802e0001441f0419583ca0100340008039505001540303013254203941041c6169200100c10000c3c0c15024020128003040c805440ea0032403034481c9420301101c504990b03a08100e02c2e42c40340001128910541c0020207003078900350800030a940c80b01604130070348204036409500c0072515212110503100f0103401c1103104000f040810700441c0502d0031202e00034030504042114985134860146040001c46401d0002005080208001d0805124030406400b0a44055103403005101918101d4800c40c0b051f91b02450016511100c00d80c002e60598103400008000c0555040c0e035002c014a000301c1c3e0038030a41d000c0c6800c1c008110b4602c042451164031880680181d03040003d896500031524990728002d850043c105641c074100256184020088045100f20018a009c001d42055107450052102040742e912a4001e0220250704 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 624193219 1250 624191969 624191983
    0x30b16050d050a023c04050a1502120a170c0316120917030a050901061a070c05040e0a0303140c09063001140a030b0c0a0903050f1501080f 61
    0x1e000c0007241c10340b62403540000a10407682004d08801d0110b131182040c40109600d8149074a00f0340820280c5882105518260b100b80d102c2e10794050036885081008070726001c0c1c032100124090055840048805804c075101d07030f02082018000802843c036008808041d00d40d1550001144606203040d41345c034241701c165440c1420107000c14000100c5401100d0125500100c5415074804400560f0a00b411402000d5400a8130081e000c01c1c00c1c1400500201414840c1c0401c171034444030744460f2011100c0700562250b10191050303524551812011501c0c5d192406980c0a180e00b00b4014205034045050050841c2c1c144202c16656180303560621070400c0d0800180d07a0aa02c0c2180c006544031503104a004030a44401800038440003003003d03138240c024402c0780c624100c445802e40910b010380039000b04284042c4030300004120b0b40345040803035403182840300901011015820801e94540c0c0340c2c5c617000c0c6030a40031505660f46074820300001a00085113000a0b004082050081000111040c425a00e41803 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 624194469 1250 624193219 624193237
    0x308073e0a02011d060c070e06030601150f0507150603150b09250504090f02131509062a060504141209220e1501050a0f090c051909030b1605 62
    0x80307000c0f00e20216076624401c803646400d1b032804440c03500e40d5a420048044504031078462080c01b81030f000040304800b100c60a0401c8106e0303550404c04080c0880181c1d030301d4200c0c03401036940340721403004150b221080d071190701c3c00b9600840c402083c009684010340240c42080001c01e00446802c400c0c40014a004182d41c2c54900100c000010500040c001c205e0f5280900e034800c0d81e4090600d004c00d040300769954000c01e10800e0002d149503c0c5501c400551641c101c58442e03503400120a04401c00006100c0e61800c400803502004200700081c01c014a03050060840005580079a610b00610003000618205134041e4800d6401920075840008007488140c0a04400d00303000380700b00c0101601c0c03c540035004460040c1024000c021400144404030b83e1420400c8400541c19840c01c0081698a00010b940003142c0c3e0050845416904146103100641058808a13050210910649841c104840c8245481d041b050760360001040c503500701002c40500240046810035070140703004182c507520a00300c40c0075038 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 624195719 1250 624194469 624194507
    0x5030105060a1a07020d1506210b070e04020d020a032c0601060305070306050d0308100b0c0714030a0f08131a031f030c090f11090d0308073e0a0201 65
    0x8100340c00400e81c0c4051540300140404a102c0c2035000090941d4880b000b6640081b84000405548001c80000522700d24400b610185030704001404003441218600750101015001604201c400304548050b40c01404010300030a0b02d07a20740344144070b4a2004000710080c1d040b1251700c02c0920100154645130103000c0c50341019242d0300094010303802034100c0c60041c40c001c3d094041c0c40a0504000b000254203990b050903500b4850400202c440ca03500540d1899621b017409811210b14011109a0555611000ea5094020b044103900800c0c3e020b0160382280c0e015050f0b003652101c49000c207040c16030f06c0e078019500790014002d00d568040118000e807544624030710b07400d00e401690200c05000351000c1c2d601c010714903007088101089072112900150a404407041003400015403152450761280030b43d0b5041030b0030106826211380441d204030021031f005405800d0a40451140d1000c56888170174022400d04200b8000726403540840440e020724102888580c00f401040c0703940e90008000d020140044e040d00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 624196969 1250 624195719 624195727
    0x1c021f090201090312170705070b100501090605071a0112120302041409090f011d10060803030705071704061806051e0f0c060f04020a050109150315050607050705030105060a1a 77
    0xe008125608220f401c00d0f15a07406c0385071800340284180d000300c40440300c411048010800b924030703e802100940700142c4954500310b0030700740c040314103030048a41611081044501609940c008a03840d0780a4071010f81794100c04003032400c00707a002010301d81c4410201071041108001401c0800ca000c1040002110a503440e511840b000f00d107400c01c40708500e01c07694a003144080030201d0701100b0000c0950480140e60404501c00e06038000c64941d0b2085d510359402c10000505a01d03c988020b02080b4070030302ca40d401c5500f80002c115203a4010750086000310390585281c0c280781800148540c0101543c0c81c01914000a10f0400c8404045c00950f08408010200792200c040c001001611149101c4100300e40c0d00b4501b440b40748182010a0b201030f03000d441c81d40000302c0c0c44e501c01d51100017a540c03000e408007103c4400e141b04500501e4111038141c0501050500400d1030380e00c5100030b08038035004000403c5c149062004240c00c4802c0680020700c1802d002a0030000c12118450403950210854010394903 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 624198219 1250 624196969 624197003
    0x306040302120f09030613021f02030702040f1808030a06140d11120312010509010b070b0f130c4a1905011511030a080f06031c021f0902010903 63
    0x20302540e032086506001b80420403000407040034190b04800e000300d40200708001d150052403d59609100d40d0340c0160030810403040035041a410030700b80c9240c0880c00107000c80b00000705020258440c07804960b0300d00c1c00028400035024500a0034003611006100c9100500a180011641001c54000030f100804c145a01841d91f590b050800150a01d0b80f41a00e980e5040128140c1c00d41d102409007601c1051100008202010040242e0302566405000f0341c1c8a274407200c080f2030389040d00030881c084a41038217001e900054145000c11004010f041c0800f03810300448011316020f074000c04035505101d032020401d0940134800f066451a8121040b0f0885215190048040709100004611803501400c02000250341142010b404000c440c203641c8070200c0e820078603125500c3e8410340030b15100050714180070420840c01a602c00790040760040c110380b2505920706100404003140510040981c20001c0624580040b080c0e107208414a0381c0c0c010840c0d0f80e49540040c05a8140380804ae00510300360002c2c0c0c1e1 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 624199469 1250 624198219 624198247
    0x21b0906100f0c080307021e030f0a0c1401020f0712110303010b0a030608070618060201150302120a050a0308091207020a030b13050a20010e2103070804080f0705030604030212 77
    0x244c00c401c50b25900c0c03600713880181d500e40481ca100e40c00a01404c5030071801200102c01c1d01c00380b2403180c4620b803601810340e00031140302c00742490a8038035500146250780064004d00c001e060603a2138103100381c0c44100a0805803c0039820349200814003165500e0074100b4a404011039041d074242c42600354980b003503260100c00410315608220505c0c4600e0501160241d0000151251000780e503018520094451800b2030a9510740604c4901c500c690391030030301c014504050f8842940b001581101d22803070701501c1d924a412550241607000c640c031002804219501807048422601c48040c00310711b440400d41c0800c03540880e92101030000d54010002c928208481c1c10b03070201042d0840d0454246641c14200800320700e050440c2c5101e244080e641e00300007540169074115010707000409240d54103100d081e0b000403880b92134810b2411800104030031800100e9502c054005402c02c517000b48905145e084c580c502c0d0202c10740006120340e001d80b0401000903030020390810031080691056854001c0000104 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 624200719 1250 624199469 624199487
    0x50907030311030a0207061404051806030d021515011218020f01020705090a09020d15020c1501030503090f1c14070e090307120c0f050f100b060708090609040606021b0906100f 77
    0x10760003010030180c131111001c000c540502034cc60840684a09011030b240c01c0e03a42d403903c1c0c084075000b141084005140c03401501202c07604400c040c145024002c2c4208251030440e940c03030081129000600c410a019070030800c0c006544100f081c001807614908000c00200640001051082c12a40f21040201191203860340000e80c503a01c40444803840ea154001100a9080409180001c3c441c030500c07250420760700442d0a0486c1d410101840c5407107d40c106010a0f81c00340110701d5040000c42400c0c1415070601d000181040d40104068551380c88030301b45c024100001580103ca044440c0c60034007006002c0031040725001c99100c5540255200c1442041e00c1c402c410100c0030300400300808200050003000b0508503404003c0760180e94007006905488812907a2805030f003604042c0c14098840083c080310010071240500900c114201000d150000f07068650f40d804c1040141c1080c01041d104103481c0c529083d10100031100000c240c5081030200e00b601c403641e03200302c0801c500c0007121240c2500458000d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 624201969 1250 624200719 624200729
    0xf030c070203060708040b090a0b01090509010e060a14060d080f0a11010f0914060708010b0f13120203060f060d03050d090c031b08030c07151101050907030311030a0207061404 77
    0xd10034519150402800368001201c080c3c551f00c02d5140060342500b0081010460182d000300d0440d05a402e024464004240086c0401500d42d03a03a0554000d00c00100403040c0f1911039802e02041d59441141802410000034146500038542034001c1000a80c001c0705a8400d48086141217884102c0d03058212081442903040c01d5242d403801a650f25850003580114103010700400e00180700801541d01170ba0380d503800700c841a0005000000500c2900130060082c0340600381c515902d030070908520b425810507078560b0301200b12266170840000071400e09004003030f030004502d200c1388281c0c649040400c1d0802c160050041c20841c2c00984c00290300704543c4104001600040705501c2d06469240c511740348034010041084d0610700340c1d40010a008000111114140030300080c003000c078070344510346d041002c0c481d410100b4402c0c680c85541d5400360074800e2a124403070741c0008107181480c600340a4040069906085c1c0071381c10800241c060b040d000595070044508903d051900002e0112080110740200c1e041 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 624203219 1250 624201969 624201973
    0x3030d090c1e0306060e0601200f031303050c1005090d02060412060515060c1009030509060f040603060b09030d0c02060912030405040b06090a12081b011b0201020a050f030c070203 79
    0xa11804400790702c0384081528455a0104189621441d25800c00d00088038110700043e25001c02102113211080701181d8441c45000301d48008281c20f10b07580c11a0440c04241010b114481d00c00c0043c071000b00088081b010007660b20f5400190342da100207003103102c0c21308498080e100102c1380004648070103080b00c000b80400ca080c90003411462a26501429080d1190103003000095450300051500d08100e030082000742004122012910030903030050003604000382c00740101803003c0202030f01c030b4800411072002c610118695035400e1080160440f102c0da0460141070b2420310074180700d6140026103851880b4a41044000c0040500c0003681c2c0744655114142c01111940da62960340c40000050400c0d150101c509000e440384401c180728190040b50f48482d0b10801810b02000740840302035000900340d01503042285418107540f0b03048802840b60a40c004542e41d11040b40140807564407c524150602d44000e51600c503400c030b0014828000e1048840e0501f00020201d140710810764125000550301a007 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 624204469 1250 624203219 624203249
    0x10030507122d050d020613021314040318120305180a0f060905030606041b2114150409030f0e0102071706071115040b06190b2703030d090c 61
    0xe020080c00200300c021035544c4643c90714560b103d400400e41d244107400144c04014680134580802c544503150100e01454503a4500c41140d01a108105040c030841c001c1c1c4034402044c5052a0f400800c4504da0b200b10000c2c03005184090000b94448102d80075403425800d80360f0011403d00002e0003414043c5d02017800034104080c00901940c0050740982121012810b6071940d64400c800d01083d2503074164a08181d10080090031001070190000140d540442e000c0010040c0310003c9000840e205105c2c601407110914003000321290783c03161840710720f1505490600000d9070590b4058646108180d240c002c0c40150402481144d00c2008108000e1080245528001001b0910681c0f1417100303485407800074a500c041c4515109001400f500c0c3c584100010100301e41d1252501d00380b03110302500840c0c2c49039001c891405180582c0350480003401b0580e0280755a140d42e280a00c610301d111010100602c1111200c54503155008001d64030302d0790f0306880109100340d0510b04602592125000316100b401000 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 624205719 1250 624204469 624204533
    0x30d11030910021e070602010c1112031e0405011407020319110a021504060e010908071e05060a0909053105150c090f0603060d150e12030f1003050712 66
    0x55101704903105a0003c102d8000d5601d02103a00c028843c0041101d41e003c0c1090a480840a800540c1d00403200b1002d02c7d0358048500381c21148100a44040e90142c0d142c0543d00e8110030051a80c94002e48075000561802c165030003000c881ca660113181c802030060240c104049071405102034020181d00615000c560001400c03050f0480e04507002da2000078091141000d0075501412941080c0c511202c018040c0c589030031542c0e031854820142c1c040241c02400c2c000245034440030050640301040e5218070500030704156100044904c01000c0c008450480c5190040c1000249080e681010408100041c0b01ca40c9040072860701c1454564070340802508001c10005103401ca000d881918000c0b5200141a00200100182400140d560030703840758801e03401500085030b8070488207a0900d580350200b4999200e40c20a810401e603c10f000707101030400010080d0801001021561102c400d800c450a03650850b182e856840c5880e01440c2d0258a6640d504424070280c6003890841d41942c0129240c0c0100070 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 624206969 1250 624205719 624205723
    0x21c05070b07031701060c03080103080315040207242304050a051c080a02030c12060a08030f04030c0506040308030105102d17090c010e010c1a06030d11030910021e 72
    0x4030600491380c26040020801c24070031055802c01680542e00d600c070baa400c47d287d4503501e501c080c0c039060700e0806030785007002251034500183c00b0769401841030340c5080a26100384124100300c05213040c8824900300c040054071100040203064100f40714211409a46d80b450410320b441d09601e40602540710f54045684490707054070b01d0f6040c0d011107507200903482e1910b810fa44c050303003c10b07519450002e1007800a000b0788404270b0300490340b00b00003c0140c1446940c0384070850545d40400d02c090118400003509009001040c08a0700c0100707400d846203442d01d0300d0340e10383c52280d010600407540b06060130103400c5e4280744903a400101c120030303804224071b411000c0b0112403000400d00d00540b01084009030003402000c25284005d11543c190800740049601c0030700111140740c810700050341403003a944122804a28103c03510a03002c003400003415101e04094003010302e061424403140c4104454205e075448401c0005c8140e072024842910b182003519109007080c1c0c2414002075034008250380c000180e01c40701c000 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 624208219 1250 624206969 624206987
    0x2220b12160e0405070515090a0b03180a0c09022206120b0102010e060402062d031f06020d03050402130e0604020f1002190303110d0213060903021c05070b0703 70
    0x4400c154414582c1c1c1d0509140d40e0b603048801801d03030b4104c158100f00c01c0c18220b1810b4140710300b00c10401d01e003401c0744001440c60b2213aa081104420404002c000c100310081001e010007152810013000d43d0300d110b0783e5003803110040c0d000f000c4180d50003159509401185441100d40156080340103503021741c44100041041490421414070076040945e0184194010b2164410380c0c0103c8015011039680e47d001d0100c01e174499a00e070704840003410056421346a0710401e07038620305103080b0380ca9640d041c032004540000c46144100d40c102200320b1030800407641c00040c0301c1b109020a003000b007242c0da9180002000c200300f002000540c1820140280f0f14500045869031080d031081706c40a80a201036030510250390501c41c82540561b00251074904101d0741c4e500f5400c00184249004181205001048243c580010315030003945c41d00442d402d002c401c50007005201408161500600b02403640d00000c2c0814480c40203501c055006160340c205006052082002a00b4007641c03681c1c2d514581d107001800742d06 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 624209469 1250 624208219 624208243
    0x1d0a03020a05010b0103060b1902030c0304080c030d05031905131e021203030603100506033c010203070f030911091302210c100c0b01090606180302220b12 68
    0x4a000ca90991380c0d030113445078000f075420003040e141c00c1c56030206507881e020500003801c00552000780300c041c2c0320750303810802007000c0d2010201410311810368074145850161410208814001d0920422003510139040800031b11285480b00850b40f80c07256916107405201d0301001400c945800b0306418101440064403191851081d00c031030903d0b030070104e881a22804250f40745a41500280c1600310466620f4010340c0d004800102500c00750801d0104008400c3e001841440c912582c44001960326a4205501c10b203162520000394070314540040000d04200901d8644800d06544030040401c1c48410442c01c085598098860112428415061621031582c2503040f4444d15034040c2c180d1800807003101104c40300e0842c400500044450100300036004850007244d104000b0190035080100307034605c60845c000c29000400141386802c1c49801840703140045000310b42d04607900410001a00d5595069008010512000c8555148080c450014224070380e0b40603400000b020281100450200d080307060b1003 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 624210719 1250 624209469 624209471
    0x14150c151f060806100306141e03070303030e06090f12030c1b01051014060d0e030d050f0601030c3605060d0c0912080f1c0e010903030e0703050304091d0a03020a0501 73
    0x491708542113081d10f01038082d099034000d240450a4403800e1540407900300c42803000c003c0b15440980004a0300d04aa10391040e0006030b02d911582c10054001d00000f40c1001c0920050032060904c80f1620fa90360b400c0ca20041c6481c40c0000004240d0102c1d9001d85400f6528075142c505810710b8002d00c0c9001e0982074442107846c000c0b2000006d150130071a006132042900c01b800a0741071900d0107031440018044a05245500c0c002009810442c4505129103032168010340f0120310981080c3c40014200c0e030307048429500b840003050304100c89004c04451140c50348941d0f80c0840c9180555281054404850b601690b080203011600b81c0584c14590410000f0460302c0e40c403801c9090780e038900f42d40c010700d024002506101082000c03c003481c1c041d200420400e2200c1250034036001c0d5042c0c0c10307030884223100d01c440d445075918200e0a08059150144201c1d0285100090081c281035071a06134032842a1300c41c403107507195600c01503140c554540440140318204001134602c05070650078041c2d2200c0a40100301c5441d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 624211969 1250 624210719 624210739
    0xc02070e0a060609050906030c06040801051f140d0212070806010e0708070f140412060e1b033a0c0b01091503020d020312030114150c151f060806 64
    0x1d4040d104240444040c2d90b01c684d0541d01e000c00b44a12050007505030381e01806801003104c91911110014401001c41c04000110391501d074140f20070003001081c41003034400e0607100030801d03840710300105201048101c0e81c9450903c2c0d10320010342d0101e141c030070244042c0140c0350000740c41040481d4050484140354090b0350f040d6152802111503001c01c858010100ba1081480c07400306100b0310202c5101c00c0ea410300c00d0b2510340c590303111600b07014100c0300866402e621501032019001003031051004081120540003c44071b01880020745030f030440c0b50035507d43c04404402c00c02c3c001d211044d24814450309070f0b00c2c03440f11601510003050b00010f100251800b118a8000086401c1c01e4407420440703616451181c510241154200308500c009544140d91521541d81d2660703602c01c000000714020301203000d0b2920a0039401c0280282400f035040d14500400060286500c5980c0114501c91401020540c415080e580e1070780c03c0a51039030b034088100307a0001102c4003007040307a0000749440c01000201c5054000d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 624213219 1250 624211969 624211981
    0x1210210110f0118030c0501020705120711030c10030f0b060304030c2009041415150a09020313081b011a0406270c030f090b1501090e011511010c02070e 67
    0x9880d064018144c00ca40e07000034403000703c0e21580720101c07200c2c071070400075140000304d4460500d0f1001c1a00a1800d000b00000d03108200420001c0201000c281600540041e194460006903211002103012041c5525140042030f140e106a02007071003014020041034072070401d42002800c1d000c00700401c84001401c030307500c03804805500c41c460008000040c5240340c16500c1c0d56803000802c440405081c0a031040918403411400519500b5221740e088161102807103108504000204029a02040d45548104140200c130100d107030503100840e03005108984c5e500c8200c5004114480e00c554446055441d00310401402d8403d034441c0d0fa03002800300c6c8c0500001c0d0702c07100b0002280e9011100058044038580441080c0100e40d048111511000d00300051700c0301ca503048030020340781c5c030000445003400c075001044035a032200065415914028a00303103598905111441810b01418091203d0440500d94400302c070300c7c0702d12003911a5150ba00b00a01104811350702c06980c84540340100e910241070b400000c3d003 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 624214469 1250 624213219 624213221
    0x20409110c030403080f09030a1505010b130b0912100f05010504020f0d090311030d0f0c080714030a0f02120907050f010e0103090c0504092a05010801210210110f01 72
    0x44294030107549814510340c5c80002d242d00444c1c4030b1481e400c1c24000070907607540074003100f108107009d00e0300900900b00401c00c400031240d058100840070081403101c041c0507040c1d040300c001034a410030304103540e83c0390a40010f1226940c0c10740d5401e06200381c811800c1c0071903003a0032611000199280c14007140c0d0701e81c0108010303402920114108803400b400b008202e240580c200c00718460290600422030704110407801c0c107642c80203903800c8056444050111522905103e0161800e0143c036140038603081a07900104800085000d41814401c0400803919560041c0c2c8218080c0c103105c9000c661351141247c02212400c411242103075030f4000c003540001e01d41013401c041461458143d40d4801120135030780040d0000d08901074103541c1c0144102020405855602c44c0000e5540206001004403102c40b045801c1010461042c40c001c08110b8000c00050341c0048501d07040d03d100c59251090580025171400d400e59541102039403003110611000030258012004688100041003600c1d0480c211042c414 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 624215719 1250 624214469 624214477
    0xe1f0c020606010807080424090b06030a08090d06150f030203010e0105010608180f1009020316030c0314010f060b0c071217030601050c0312270705011d090a02040911 73
    0x3808102d006000502c0700340708498a40d4000e1023451004030b03c024010314041e1103507080050006ca45c3d52000304070706010041450980c4a941200117006c50303403c565271165280143e01c1c0541c06003040b08021000c01800c2d801200521482c0300032003102c59902d20b00a42c440e29244400d901a500e410b010040120701070140905a03082c603200c242c15600c1e0402c5003411500c188003990418090041131401ca10030030b01803010041151756000c1078800c0710340109810100ea061800d4002400c7e454200001405400c040085a400140300315400c0117802000340980401010346010b14501080400d10035288006001c00c807440d601103404658a605500103841122080541860000f000e010103107049800203552000e41072404509012000711101d146801403031f180341084041c5410001201210403e40c1d0340e421480880040803a404407040e91a043c1c280101410461000c48180004420b611078031900740015040c5101840c3c901d07000e500a421a0040343c0ba031504002c40c1034010b202040503a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 624216969 1250 624215719 624215731
    0xb0c091315140301020702030613060606051801121103090d030c0e06040b1303020a080705090a0c0f031119020c1212160c030f140606010810030b0a0e1f0c0206 70
    0x44411410b0015808240a80d030746440d901d59000c100080c016101484803600400e58000e40904040c028940070040e503089804c10010031000780300c00c0d07449494084400950300030030300300780120900004030b441c0605404400948071040001c1440f143d0700d000601d0741d0813602c1c40d85d420000c0e0440005c0c21614683c0e841341081e4400c0c01403000b80b14803c0b100004241c550310685808071001d0b982d5002c202c440720300e60f1048841d82c10200c010015801c142e0042540000c20000811541100700f0b0090465007041180b00100f60781c4160b0307241b40620040803209089046e102c100d520b40c404d485d0095980ca6100d1f100c900503811000c110b02d8803078000450203c0f440802c2e400908090303821400305110f16480d54141d907581101a000000b203580c500000d120701d8021402d00c15075140c100841d900c0d0403005450541000b940008104003003006407480c40550740d0000162041f622945584c20180030701c4600070a241c041c1da0100c4240d2500c1d403600040c2054055010300130285d07646800e90701c2d50310403110 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 624218219 1250 624216969 624217001
    0x506091c050406141201030c142e0306050909010b03150405031902070b0f0a0807090b03130f0b071806020718020307200c130203040809040908070b0c0913 68
    0xd1040780d020310a10035140c1e0f200f8135181e007003a2036203404610380e00081c0e005643c4107002c200300703010310104440304401c15030f01520342122501d07041450148030501507540184024040b100d46046034400c0e000580145401403d1889605008400d18020031984100c607100b071081c2106070030302c41d840f04502441142c00a0103075003002034442e80214001c502c80d810f803085000c1c00c0b0000c00c004040a006e881401c00038504607880c1c81c14010094800b61001d8809021300025040c100300034090b2004480c0d1000356803400c40000340d145d00d0489648c0100c0500108020740c12410000910b5024003443e00b44204000007880b500e580703070300a83c1c07982c070b1600a0b442a48141c08890450041c580c0081d03030008201d15111060721460015903811412500441c45950000d4004800c2850120040c00000f988148114034608143c1c3e1003010511401408030b002d142c80714401d00502500d642903802d5a5000300694401749009101d1044603403212010610485914003017990440c014030801d0550700c0c04403d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 624219469 1250 624218219 624218227
    0xe010b030715080618090717160b0a030b09090c180c040e1305030c0d1412220f060605041b0206060f060f0d050603120f180312070506091c05 62
    0x7012105210004e11598218181c0d1100483e00844400c4a510402c160300251034040d003084103030142d10620501d00385656000810000c03803c84065079440c129101d0420072940c0749940d0074150043c141501c100703036210269408214034072001003a08844060102d0f201d01e9826552510240c0d080d03020f0702d28032000e001c00d02040c0217982d000303040d00c3c0c0c00c10b90009840039030345500c0e65a949181d00981c01c00260b90031001407076043c0f40c1c002e070b08140c00300007074110307242441d81c002583c02d4641002031240503241c0d605c0c80412030518040804040342600507140d03044501c06420414085c14291182500031880c085158a648503a220a484c0035003482d03010b4203041d102d84080000502e880c05046038842002c004007859004903000804401d4032101c008612490300d80c0806080c46244080c0e04a083c8041100503810f0741180102e40300f0461100c02d1030ba100c400344001c01e141c11405040d006100318000340c00000e21400140a81c810280c900c101c03020102c103000112488802466210301054042c0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 624220719 1250 624219469 624219509
    0x6060309030c060f11030a0b100203090d031206050312030106020c0904020d0b0a0f020309070302011403040b180708011a040e0c10110a0f0c0302011101021602060711130e010b0307 79
    0xb0308141182030208134049240300000c10110344507401a5107404909030394a051101c1c0782441007102c1903030302d55400650b0900d1204000b1510b000241c500c0181000031101800c0f0b01460300d50303c0030780600405800ca802444907240141040e50081c05a8005442144440740c41490005400c0d48640d502904440408400b0781d1240c3c91001c018000800b00c684a00c40000340540314130203944100d00c3c0100511b003c80c03171800050082c03441044070a1517248100200800b00f50310034809604100078200d15068545009a42428a0002d030052a21f6500300540d8100164804403245c8031031604540800007094000c1102e5911444040e44070f803c400e2046032502c1c401d002c0e94507aa060710851043e2040c4455a03030394540c03524800141203540b89080b60080c829943e12151704d466501c90384000b140f42c0b604041c41d213580c4d2211a00b000384180e0000034101e040100c0d40105281c400c40160042e101c20120b06100c1000d003240009200c0a58604400c1c100d1500d000502907003200c420031240b040643c180 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 624221969 1250 624220719 624220721
    0x71701020c3307032415020a020307060c08040e0108030909010618060e010318060c0807090608010e1801050702010c0f02070e010909170a18050a080d0807030b040c090906060309030c06 81
    0x3071402061503510004003c194842c09100c070104401c5400e041720032424481510b0b080301a041000c030444d801110340c2c50060f1070005000068030451b0500324040c40251800750002e20498101c603080403582000000c0040c0c0000c00703000488003c5400c450240c3c1c81c0c12003110702c101d04140c01c0a161841400070030009014258492401406240104094011412071030303800260705011514a56500044800107611818203500f000403490700300c0f4102e2910344004d1001906000e145480340b0204089150108905668043c0c100048001d000625045401078000e120340c9103000c0101e01c8803440d94032802d10204070b6200369401e2540700e4403540d00b0316410320020140150100c3c0c4a40c40c0d04c1070314075109005c901612502c0300135552500c52802d600a240310700c24159001e2030003800040b000344511030b00814031083c10b520a01d0070300880d60700c0178011400381c400c20f90540d41140c03901d02c400b8002c65001d9a04400c0e5107a4203003e20100c0c1d6260022021500f0940303001d40020fa0074040310f4001202 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 624223219 1250 624221969 624221971
    0xf03070b0a2318010e12040f090203010807330f080105101d1201060806150603060109030803060a03060c121b080705070305070204060b0d0b040b061b071701020c33 72
    0x3c1c403c0001707012161a0507007032600507491a149070031000407078100031408110b12200041c000c01c1c0400e41c11545402c8405584009601030f16032074903106c0c81464000c0600d4134032121045210800340201400103040905000700d002580310006642000105d40b07401d244154603c82440b550b03a22140d5841282103140c441440e15901c0e6100080d810084503a075402d010326000707440b03808054201420132038012038040c00c0320880c06000725030600420070160b0300045054226600701c0e4480340e03a9030701c01c0d001640c15165500010900c5141240c007061480e405294a507100f014080704208108004955030720780f40282c00364900050340400015000c610460242c404c10b446418814200501c0340d0010b4141c5519400a0b841c005000c5800020780f0700d1401903034505a030585080040040384400710b40244241c0d40e20504441003d07152200b01d110070404c100060911850040a080036050301d14043c0d4403001c1d01c0c2100b88280203413091a6920b5108030800c030003c8820300b00d598003e2682c0c0350440c000c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 624224469 1250 624223219 624223261
    0x30a0b010e0a0909032708060106020c130203150a080606040b0109080a030c0807050d0507120e03100b0a0b03090a02040c0206130b04080405031c0906020d1409030f03070b0a23 77
    0x751428840800d141b0004d000c00301c07410701545d1802040c02c1014140ca843c5d0141d0240045601c03445594920381c458002c501ca040940c241d0142c0c0e20758519001894940780900c0107600400c5141000803200e40106541c0d010394411a0b06220b070b0311038880111100d41c204e0003000e05070b4100e0206000068020241055400d210300c1026042004985601d0708003103940d103a09010076000101c440800c040e000056146180c50304140e89092100400310382d9410704001d00d84019941c50000d00c185544450383c08006002000300d19a1700d1030308103011b540390201610128002c03801c0072840300c01d043c008100a403141600760000c041c04041a00c03003440b008006041078654600400c0003094649052002c1010620a2514010f00c00d542100040165000e40d0143d0f08641000d0003042410b90702590442c440c403030300c803110b50700c414003000000d090040004079628148000540c4030100244201200e125880c000710800540c210400c1041c074640086a030818554181e0700003500342e25030441030b841501 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 624225719 1250 624224469 624224477
    0x2c0d02030c090f06011404082e09050102070212011806020d1d03030f0703060503030f0c01110307270b07030813020a0602030d0f020403030c0f08090a0b030a0b010e0a090903 76
    0xc1141c60206046000a451504000b10410304210455070051000504030307403943d0341d1714907080ca030008150311401c4540d0f80c541c40780072544091f0004612a000b81c21902850364041010101e1440e21034000d500c400c500320301803044039031000400c1b40103104003900009081d0100c1d03a0310b2070a94a00e0020342c0300d21101e0802d256103581d412401d403e694407901c1c08290344030042d996824500c00148030703280e0007000c0ca001c050600e00248901c0d00c01100790f820391681e07201810f8950410140d0980500403490031101801030100c20003078070307951104d83c40103080b488031160315042c02c2c28008551200c806000d007010f6004204002c00c0024480c10070345034840080e281400046440c3d500184001e5107a0b4004c200591011030b869102c06c80038411001c1e40400881d00318502490f42c0d8015140f40b003520030241c462000a00c81c00309005c1448226601d60000408402285480f07030011815a00181c4084000a1811b103100549500403504a40d040c0c0b4002c0255400a2520402c00c000d0641035504074200 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 624226969 1250 624225719 624225733
    0x406020f041404050a09170702040f1a181302090c120a0203060f0108010302031507050c030406021f0b090a0b060d020c01020309010507080f0106030203070903021e012c0d0203 77
    0xc0140c0402400c003901110303400d41e0741c0c0e1404070200000d031380c1d000c0d00800700030b4505080c0d500010326007079288a6a4510300a06070300c0e8109800041d0041030285946076169003040003030152040145400188400129800c0341d4403220381032000380d030120840d450000c01e483c0c00115809480e00070021039100300001420703481c00d083d9040f020480c18040c0c9070040e5094000c8144640352500512000003040b00303180071500380d0315680000396101c1e01604078107890301c494004120361621a800310b07100400d000003240d13034071a61450029030725941c1000c8156240e010b00c0401a0703404250203001000038005240c00070a440b01c080c003030000d08903051321031303071081082201c10340043c55400540780d86001d40000684a2420140c21400d440c0010440740801c400c8a0800215101002c1074605489203850010703100d995094058403024900d400c043e5018204100150f403400038419042c0e440301c001c0c0d03034a0010101000030a80016518119095107082c280b000416a06104620322840783c00101150f01c9 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 624228219 1250 624226969 624226987
    0x30f09070e19360c120b0f04030c020306090604061109060a0e040e01092001030612030f21150503030301080330090601060207061715030c1e030717070608040602 71
    0x41e01c514224103d110b000310910000074400d803c00c4c4e41004203c080360040f40407032981d84180040b980102850810040b20700401c0a0500c0b46554451840d03000c0c08880c21383c20823040d081d50b20041120201d41c201e0400c0f1224007031100c036105031004100d02800e42410180300503420b07101304c80c030945080c2d0440e42d52403103109082d0b400d008800d07016004000c8148d101a4070400814543d507000e2290b070504d418601c0421440d60131200380c444503500340c6815504401242000c540c0e2034000d0342c81100d48200d01100c1c60164000d81d121240c1c0070808030300b0012140e070358014181c43e400240b00c1c5910130717081880000a101d2003280000d507489943d400401c4582d20f01a900d0b80c0b24071041c0e84015403580840010b0207096010401a0082d2160f810030142c140c89480500354100e000a000c00300784d0400a040e0100d64604100c2d20781d0803000208000d40800c0b02508641082d04071444d114824483c50344002200c60081d14244648840c1c4000b81020500704042900c1108010b0811110385038200480c8030 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 624229469 1250 624228219 624228281
    0xf0d050d030b120d090b1c05181603120311130f051c0b01030213020706111305150a032408150106030b030c1e06030f09070e19 56
    0x1528004507100000e07000360703140c1031048480480690144a50294000c412080c1e0080704000495400c0328030103607114003c8440000300381182c107545040c981403e0900c0320348a0030415240c02002c00b6400c940d8034002403400718443c91203a00c00078226800035045141500c0c80780d001200c240d45600102e901d000c00c000c21201c1380784a1035000701400d0b0050714080c0300500d08401503aa440d042c003050448803042d02d44034031042e54018400244207900c1c182c6000d056800c0d40e0159203980e9040328040154403d6402180d40030343c803c042d0101840c808407000b040300c1c50140020303c00c07021401003940c18258603010940082c030040844041b0310030003443c8914060780e03100410020b0880c1c60003429115495021074003c000301a04410241818949400d1803500c00082128901100310764154800d42201141410a07024009458010000008008021100420280c025440b410840310440d81e1800070b080031171415074910300300400d9000c8602c2c60f5550392300300d149040340c601c407a141d17400d8203181c5a0b0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 624230719 1250 624229469 624229483
    0x2404090c230d11011103040f090c0c0b13060516050d150503031306030f0e0d0c0201120603110901331e0201050a110a090501050f0c01090506010911040e060f0d05 71
    0x251000e50720700f900703481540d00550b481155400304d40111300301070900c01504400400d6029040c1c103542e03191140c0c1d154900c03c0303010b03025060300428008003038141005d050382d5103118200d0950b03140d0300341404640c07044565078400b5203d1486a58103420904e680c1c0c4e0034400303850062003400c0c003203007180b001241d151307401c2c0014028003000420740004586480b2001d029125294040070401e4038200b07405941c10700102e00c00114140910f8840002e041b58030050303d1164040060903100c504d010000b1040104d284125104108126071a4829a076501400820402c2c2e18007284014400c8103c00142854040700300742051450341400400d201991519020083c01c0314440e1005070b45800034000c1d001004e103c0c010714040800742d040d03d02250341c88017826103e0b00b40b0405040050014400080300c82220683d884514194000d0103c0361803414601e955280c00e0241c0d45049141842030355400c100d40d02150210340500e40c8401040d541c01d01008181c004c040e12558101107101007035000558140028 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 624231969 1250 624230719 624230723
    0x122505120c0307050d02121c0e010f06060e0301061d070905101e080130050f1f020c06040807050a05250902070809090408040308032404090c230d 64
    0xe58036800c0a0a00c0c45c6031070300d5000540e085d0f400000388040140e041d001100c8105903001078000284148001c020001c001c45004c50720154a0805403500381c4060f0f0b000a000c6825603a6a44100115081014200c403c00e100d8076003000395404020303d0404030000e4560340a1107505044000c2c980e100040343e5400c1008031400c1c00642c400d207020f102050709406040e0303080d41c10302d800100380d810712070b4542a0300d040800300300f41184541c0d501d0840481030300e01e9580595024003030307421300d10300380c10039a81d960251601c020f02810510a04d52015030981f080c1e40300c0950407002000c41e5112910b0b0768140742e0001005417501c2c041c186c148800f040080103204074216005a0341c0b55800c070038144410f1911030503004101c01600405c003035000314042e501a183c0d640400c03100c03000303240c903503103086d034294811075000034030101001c410845400300990040c0901120b484507000c10040741c208000488183c04070003010740c6060241070000c100100c089100029901200310f401c0300d4000001083c0d010742002c1 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 624233219 1250 624231969 624231973
    0xd060609150c120e030a14030a0e03160501030b040f0216172a0718021903060b0703030c050913020405041803020a1502040308030f09122505120c 64
    0x10020240807000c0c555440301c8518148510b00416503601c9241c802240c88070082000da083c414103250340038050029620b602641d403031400c400c0e100143d03440350010800100450400f401d0010f450502158414020354000c010507441c0e03040c80015401842079240751a045a27440043e034501c004a840240074003c0f881c00038104442441c6045c0300e91048001403200c03c500c050101d00b2001d0f49282c40c41c428500706442c4140d010b451403003840d1070021164402c15088c0d012901c98507076044150700402c0b1440d140c009a2914400d1094150140d604504ca40841e03240c0810503e40400d2080e4082c40c0d2020251070100d2500c101c2000281d4014804454400b207568005030401041c41c0a1190b400041c0520120060390485510080d40341c14844d5000f41c000300c0c1c9031103000b075102d1036541214055030f4801401d5132070742014007102d02a1041110406200c3c8034400b854803201ca86031040d1985900d444003808404913410b2055200c450380f8100844161041142e00c0070030380058405805205803001c0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 624234469 1250 624233219 624233237
    0x6130312020a2001064704080c06030112080c0115090c02070e100501080a0f140f0f04110d0203010b03030c060f010b180603090c03070b0d110310030f03050d0606 71
    0x6000219881101803d41c2c103030702d48401048415a40b40040c600138820711044e6044441c946a0384680040d21840c420344d0070342a251602d80301460402401c03c1d00d18900c00c44028003400380620a1500c802e01400000d141901c0b007034030000d00d004004080c444101800419840c01412016403400102c1d000311403496210000c583c3e04640c10410b200c0100362181c8000c0b454200491a010940030601803d4108041000051244080b50f0081074201080d010200075075009100420740440068480d042214074010100b000810760101150045400c800403254000803982002001c44819070121707055500d8888a104603501840a0700c030300410280500001d140200c0082d0b011141608004914a01400096904e084003500c0040d0070301e0a90b0010390303c1c3c840343d901074500583c80e8042c0c0d6061040a00100b05003503460054090240c0c80351051124040248000b00640012104021404070144007000440c882d88100007986000c3c5c209a4503062500300524203450460b0030000129007100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 624235719 1250 624234469 624234497
    0x2090708011d0c0912071205060f070e03060a15050604080c1918020a0e040504050d031a03120901050c06010b070309050103020304051e07050406090f0b01020703020306130312020a 79
    0x4095948100c120503101c0c2c2140b60941c5002c640d4010145a00d00404a03500d0030008a80108a058080c0029400c0c001d01d41c1d80c41d140050340c07602c0407140307d484000c028004c58122030140c0c82c02501032000402030100d40d0b0750481c5a8008010220701541d604003514030008043d1581d00041c4080c04501c0003030825444c0b4030050229027a80c45694045d0b261443c10104000000d043d00c034201c0d16503420b40541c1d582c1d00500200c40d121020000c3c654000e14103018030040001c0050381d00480c0d04182c8041c0440f58030110410842400311340181d416422181c003210011240788000d014075801411f21a080c000304410036440d260342600301c05040c10000403d0001e0641106400c001880c0920307041d491481c0640d40c05450750f403502000c00c11071a90054001c040d450038480c2d18041c01d07002e00b0030031441c0d030b9810b0070401500c1e84207000c61070213140402c0d50303109510114030f240640b5000380040c02c0c43d4440740c49510600355040400d03020000c0d85040d01c01e5000c618002007191280507500c05809600c58 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 624236969 1250 624235719 624235739
    0x8060f04200903071409011a090a1202010306091107020d0503121315110f070609060f1a1c0210171518010608060d170325030203010308180d0209070801 67
    0x35030491a28407482c0e000317821265440a418505651006c011002d003c03809601c0040d13507005210480798044002c21000c101c0c036a040010300c51440c000d0760305001959840544100310f4110000c24108070408000d684007500b041680c56240f50301c80c80441e80784c864070f0004010998000d941350300c880402880d170a814002400105150040855810040003d485d50740c07142070300c04d45008115120f03002c10200d00b4000c0070ba0203ca240d0b500003606200700741c0303240001c600a240101111500c03104480840030103088c6903c445110001203050f00713030520300310703000c0240408151001d41d04000140d0030300701c01240c2d2000c003240200300d000c2007601180300b09010004080c01d0b02c0300034062403101200402c240303540030140030b42010003a10301d460541807a007407054288801c6410f000c07443c240082444004040411030044c00c0b5071000010031000c000760070441c103922007031002919102d030500440b01d001600d602d0030f45827038400500205a200066000c668111411036000003c203218800411480c000 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 624238219 1250 624236969 624236983
    0x10f0b0306030a02010c080d1a040f090b04030315080a150c0315031118100807050d0512030a021606090506070f12020304080c06011502070b0a08060f04200903 70
    0x24054000d065103480340220750350f10030361080a0704000744000c004051005950071201300646d0301d40c0600c02150000500d101c00c40380541c085029500d0801402c01e4040280305a180c6135601c15041519601d50fa2030807005081c407440c102504031448240040c201d0005c0188a004c9446146101c10f04188112950304070740b83c4019000034581411128201407a8420042c4280c0360b000075141d0080d45180c01059806410009000c40303c0324050501162202c2e06501d881150300b408211001682c4075010f2259680d0f1841d0014415400080010350360f9004401840d40000708203001402e0030000340c0c01442400f4940d42c140c965559480b0040c09000040c090180d206075035081c1402c17402105140201056050300f9174502696010022900304121003084498602030041214120350b11280f01002c40e041141440015100d8000000303018190441a900351010503100c0140d107a89800c1031140369030a601d02154050f0740c0d89203940000c1c0184050102d1360b44205403031383c4c9030342c148010306141c404 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 624239469 1250 624238219 624238229
    0x2707060309110d080726070302061f063c0302121f0306240b0c010e120912070306060b0903060903090906010513050310050403230a0c0201020c04050906010f 69
    0x18149002004150030781d08450b0084e903c80b03140346d510b000001d814a5614400e56a6500f00703400020341c0d42c2071682c001140c1b40940e25040b1881c85401c03201c444c8010b0303403180348907100204060408418509107003902d205854410401c400b00c0e6540c4018480040080001c03404001c2a0301043c0744000800810070268402854010b8600d0066820700440f003031070461100400d51a00c07009155540080300031400c100d0900b06541c1d189007034032180340c1c10041d0440f05100142e90700c0c20303000c1c0101100000e55030402c420071110361031805030300c45d06105840380400440c0400d4844c42d00e000001900522030340000700304205c1c1c102d84554150040504200300540490031030760003030008100f255950a00260001000d0800da942c9d81c481700d01c06640125103a000c0c59042c00b90f02140c02c60b10307040d90040c034401c0303203c1c0c5e460b0340910701d134101c0305400414400b02e481c2d48100d05000c1c0a004500034000c4603a11703401401203450b403040400001742901c40844011260390032240c010040b0900400340000030f0030f = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 624240719 1250 624239469 624239479
    0x4060c0f0914100c12050405011815080601110d0503070f020111030601081e0c0d0c030504230106090513050c15220312110f070e270706030911 63
    0x500c1c00d402003445000d582e18052044024059018030a80100a620340c0b0b140d024140b1040c05c2081c1c9005440c40d0890300c645400b042d1445410805080900001c00a440f481d015280f2000e99210317080f00c1c0c0c09401400c460501a415104070302d4a00e00b04039424490400340e07110b540d64034100300c004101034070302d040314801d5a05102e40c0c0c8884445250079294031001c00e19290f5541d0351a0085011518100001127100c8801c1b0340078003500c90030200040c480582d00400611504158200031000c803201210f014020308181105484078811000170681612800000468070076100d940d541c0450341c1c2518901c00d0304008211a900b003107814004055998000c0b00d00f410312045210b124500c51240b81c0b5043c90136004150101e039940850140117010f160090048007a81545034030280a072500c60b403445402e132262551420600d007001448030300340d0f41c0c40c0001003615120402c00c0b030017119000d0300320388407601044018150040d08111040041105503408078950040d0304100c0800d200803048a0f0080c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 624241969 1250 624240719 624240737
    0x1031202031c02160b010905011a1c0f06080111040e090f03040603022803090b010f0617060f0904030c03120c0e090a0908030c04060201142710020304060c0f 69
    0x110115088140320a444900035a44e0380c808a00d100e04c01d9114880241000c0d4800e0000c074045d81203621032030503602d140040701502c2945107089503090080460b582c4568a140c1c0d00981280d080c0d400c01003203d1000d0101284c070740d03240c40f0060b080d01c442c4190b075410200040341c100b150b03c031007040c0c15800103104006090100298078001e0348a01c82c601a20b41032540008045401551030340610503502107041d0036200b811010035004029001b00b403000c2d11303406c11031000810904000b11401c401c0318030580301e00442d240c1c00b0b4070461040d1001402913510501ca4100130304140ca8411400d803154ac40707a91403100900c060b00d005072042d0f558854014010f0729001e80d504400d41c00c8250030032000d2080b41c030049142d40d10403548001d00381141e0020300185020080c0801c2e0400b240290082c4e601c0740e0024400c1e11492000c03185103481c1100c001d244409244410500380c40501c3c075480c0c2203d60b2074141c46409503645c201c18140d0744245c6044603020356402e4007040b81641b0000c03001006003140b50034403103 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 624243219 1250 624241969 624241987
    0xf03031d121c0b1c0c0e0c0405040f0b030d0e131a10030c05030f090f0708010b011713081e0a0e011409030706110c030f060901050f0c030a0906020906070b0103120203 73
    0x1580491900300c090710700138041d036007007030040c0c075901c00c0010400c40c10160002e1030001c448955a800510405002c1c07400c0401030130301c40d842c0380181051440050001d0000e10b01d000d0003200e203400c1500503103812051041d00c403030001e4490701890381c0e1500002103102e28942c90b00f007030000c000d011a8010040500d00100700d140c40364000122500034104880180090305c0d001c80440c1030094805070032030300344580400001c6a04041d004591802005d132540100b00c004040d4a2070001e200701d840760b06c500d00d0445814001038040b000751150b801400703200a120049c24010011a40c00090300e00082003030081170008a603400101c40f48800c0080e0595800c0035004404a40d0b48c00c1c4a015a0043c07025150f2541100d02c4100303c64041640700400310303107803850f00d45000b40e2161410398000d4010b50038527000a00c0c039011100744a01900301c1d01760240ca10340e5008100b10013000c54a40440f1069002c200640c400d60301c5070b0242041078020b9a5481482d40b5500d04000009043c0c0743c05011341d001407081200c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 624244469 1250 624243219 624243229
    0x9010b040f030f11090f01090c0906080c0f0702130b0406090903080402130e07121203020708071101090f260609030d110f0c0f0c030a0f03031d121c0b 66
    0xc0320f603c000703500140c44031441c1001c40d10344101c04035a0402c0d403803400c104030034250111481c102d135020b0208000d0040f0400e0300f1102c01009025990200c1d504002061400c01240c0003840001c101801e9241816005e60014000f203c100c02c031307414101c4d10303200500280e10346445841d0041c4982041006036000a580103008860002d1010380318100d807070003c4413501e11640280030300380411016520f086403103002c072a0f03a0410f9590243d41c002c10440001131098000d200303c0f0221070b004460740d8204072840d900d40e5448680041c2c0329041243c24000000d020002044407805400325940c42680e20820700341038600d81e10000e10b020440e600c200107000075424084110340d00c8200e600d40200d24900041072488152007420b0464461480000f14400d1800c00424030144030030540055075030528400381010b03547d01c140c08000e84010007440441c400a402544916448280300c00c60040c4000500d40310b03410031011410120f031114001405d003010792009840b20401c102048400c01051524102042c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 624245719 1250 624244469 624244499
    0xf16030f21050402030f03030c12090c0906060c0c100c060b0405070504120507050907020102030702061e01091a0d080d0c03050129070506040f03090509070e01140405061809010b04 79
    0x30014950342c03004a4203544060207028001d044034801c8907a80d01f0031002e1504d450b4030030b444000881a40c0e002217590003030f0201d821041100c008004083c2503d0b403808200d102d90104204845600c19001c071400340d51500603046210302c410740c45003014401c55091100a0791582030103144a2844d01040160480d0840c0541c0d00f50780801850752a0030740f49140052504c480e9400240e4400c0c01d00041001c04c40e815001184546003541c2034400c95240c19030310386020340740c54401410042e604401031200382c60b181d10011f403031140b000041259184e801d010522000000100b0340385003500050440c0c170074850340110303513040c006417504204d158505070218030005080d85103120000e00031402041c0c0d9001c4001503608150300801541c100c0c0c01d046c0303455400181201411008640d8013940019281b401000c0184215102c2d1519108010380400444030144205500c3c242c00c1801e0202050580707a00c03014003124000100140c440003006010400040016401417024810400040c800c10a16407045 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 624246969 1250 624245719 624245777
    0x30b0c1617040807141206070e06130302120105090705010c020121090b0a15090207120e241e070c03060207080f0d0218030c0a1a0f16030f 61
    0x2041e4040001400454407403503000d03511501c0340c46404502d40c440b41c11107955086003103d05042c10a4007800040d1150340484403080032448044001c001c504003940186001c141400358401c659460350300140c400142d1240d50002603664034100140c0010403c40c07900600001d003003842d5820101d138002441e4094081c2501c08000d00c0140c0b015007211550041e41d00d843d4400b02d0701c0503134034110f034203000100045090b5030318144040c80000b640158a101f1151202e030031407000703002c400d45040700395070041900000ca80c001040c030100900f40690302c0d010101241150455550b12030204e0b12090308200101c4051400040801c035907800a560f280b40842203a61204000d80c503803003941031100260180803101070254400050941c2c1c5840141e00619032080c45d860200f0081da5081b040c1a82d07001042c0304680c000c10034540900c245141900d0b40040c8074444042c841c942203a040005189820185041542c4d01000e2804010190000c0c40e40c0c2d642d900901e0098a400800d034900161404000f000c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 624248219 1250 624246969 624246983
    0x30c01030e070b03011d01060518060702031e16050f0a18090609120815060a0c020301020d020a081e0f0a1a0a150e06030f06121c09030b0c16 62
    0xc1d0703400c5901071060000a0030020b207140d85a41c0d5034800c1e80c05049035044c1c40882000300500202c1e4180c00b900a03100d8410138000190000040b42c014407205a214010903649803140b55580034408002ca00000320700c103c401d02520114910007180c1112400079040184541d80c10020401a6101c4d21813001c100d405608908801c002c40d18800d5000b0421004044c01017400c1450b50801c2c80f0b004031006004038519a512496070f07039030800ca03405102c0042c203919813102041144901081c0308841a01ca001e00080c0010702e401c00324803000d812648942151000310f42daa400b00843e520381541d1002d10045e0803003075501540303400600c82d441d12800401c1c1c0406103940f07180031501042c2d04840784c02c100c0d0014020b11442c0d0f803120105c03000c6200117003032100040c10442c0424a40c0c20f21a054038004d00b281100310740e0644400c01041020b2816803141c054600c60511107403091103d1003107207854011251204181a420340c02c02c1881c201c00207108e1b903840ca6040126843c0e8541240c04c404a280c1c00102c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 624249469 1250 624248219 624248231
    0xc091d100c18060c030e03031c020a051308070e07050a050904110c06250314220b130b100806060d0303020426010c0206100308160210030c031a030c0103 67
    0x1009581400c8182800340044841c442c000c6800342d000f010801805009072034103c04035411008060b41c03446040d01000c03078115656142c600b4803c01e60041c06618100b410402d0400c1d07030034511305480440c141d0018015a0003007208000c09802e401002d5085810361034450310b05560180c01400500c130303d600850181d40d99400200c0c0300380740c07c410380350419211019629182410101a009010101c00304c056110070700001c590400c0c040e1091170f00c4981c02c22010320f0f0b5640c948041083c0c00302c40d0b4800c01c0c029100c107400b01c0d0028800096880c410074840d5103002d102c6107203092502080380300800e444000c840c081024000d0120004503147d00480450340610380003903a140441c040d01460b0312210f507100c01c00903400c900041810007020048402d80003003040030b000082c200c0c6c0d951030507212584010648001880441c40719030051039405442d0f01e06130002c01c010b601148600741e054411000080e544c1001c00740003641405203da20740c00c441c00f0b00d51007180307401c00203450302100d0110505043d5245 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 624250719 1250 624249469 624249491
    0x50f030a0605130b0a080309030706030e01060306110a091d0a02090d02120a0515040c050111030c03070312140708060118050406030b100603020f030402130e0a0c091d10 74
    0x41c121070003a00019000f6120303a009405080064158090024480c141041005c41c1051000042c2c5c2c40c011801401841d400b8a052800e07801440300b410602400c2d521101c011012511074005d0003401b08180c680259140b590b000c1c020460007081e00440c00007440d00300c03d00c041c1c00e080500789401c075071043c0005903540195000100c0c102603003c1c0c02904202540703c000f03c6c042000c070386040a54014005c1c4d0340a48940724100204583c12039000b864800e00c0c042c04d0000307501c84d10800364440c445c541181d1821045200991440d000401e04400042c001d540c031a0401c42035024000a09805040218441c14003201c003174410130340244411b04105041504001c040082c6d101c0f40003c000150040100c00d80700c0c1090310f92100c0c112000040d8052284001920510034401c0320040c888019103181151665400c20038401018080a100107440b9203001e041e5902c2440101809440340104c0350490303183c0618241680d41040640350700010601c4d142c1c0d041070780807070b0080841600c120001803000340c1c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 624251969 1250 624250719 624250721
    0x10b0a0f08060a061a032815050906030703030e01170f070e0d02010e04020901030b0a0b070b1608010b0d021b010c09080c010801030609050f1b1819090c080a0503070204050601090303050f030a 84
    0x4410402c80c10102d43c11f03028410392450b8091400d00b40c1c0205884d0300e207a116020300a0700002076802e560582e01c1294204007081c071410030710450000501d0b1405040b1122a06051181801d468540c0b400d00c04006200b031281e0010110101d290f025654804180c1007900041d04502c4101d0106004071303000150790034103a1103a440106054001041007441640300c0300c041031907070481c40c8212540300001011410141740b01c021040e00441a94460040d40e080100a004541010800d9007030f590f000e101c10707064216080394444650b2280000025250840f14004080c1041584030380e50b150000c5400140382c1c1d070301040c0780c1d040d642c000c18085a288107503d80f851900c8584144a5401e0040c0a141660348035210860703107540b041100d0b2440b1f0020021140f902c8540152440c04408804c26503e44060a158120006040c0101c01c030940495450004a0915a0101003115280c2000900d1400c51800b403042036000042032800500080c00d43ea0003400501c0f4bc0310080b00380344800720010303540300c0711 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 624253219 1250 624251969 624252001
    0x1b120e060703020f07060503090d03230112020901092903030906041d090303061c0309080609071d361516020c060f0c010b0a0f08060a061a03 62
    0x50503660303a668160070000d489012069015880c0d014140000451034822001c0e01d02803240c100140001c0c8480032410f0300140041054840d880d000a00e96a000c24040d91070b107802454450b0041112103458410000300003c1608200b03001854028403042d60303504c5084501e0441901d1001d91004104240002d15500445800a620000015001c0f03020f40711800c650782099140b40b070a00d8151500d000c000d450703000480300281c200c070200d60b90318032041400f030040e0b05803402810804410cd03154501c082c1010400c8480c0c5417035034010f070403c02c180c00f08000191a0029003214042c0c0606004619002c05004070001c51a41250800e6201c0980c103c114500c030f81030300c541c1c21150800712400c05210400c20407500c1c1d00040c40c24003945c401d00350000c212132400205c02440d041c034103442d40900e0442904540748a8031190741c0c40032801d40a031151501c12020b800a82d100440c40d61401441ca46013050003080e045000382003030740401411a040d1009a58481d188000907160360b14610300c05103000c1 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 624254469 1250 624253219 624253247
    0x902030f07030606150e0102060703320106110307120e060d0c02060402010f081b030a09060f0e1e06040204230a0b090106020a0308012309190c1b12 65
    0xa04070001040000030384c0710703d0484211070348110280c02c649000303440950b1070500d801e026070000e000261f40244243d110106d2100c4819485564a004109903209022003620b4134140c0ac54090050001a030801c20b10130721210300c880294581280740e074440c03a60040c20102d4600380320160445c016140e441009445c00c22035900020130681440001c02903079402d06480990104140052014200d446446201c0c4913001402d02c02c101212030300c2c0c02c1056640000c044e10700580d034a84604000038803d0080081ca0b00c1070000104200c088401120700340040c994081d0052841e5401c0560910b10209101d9840764040710000ba0442d822041c07400305c01c503181d61881c00d000c2d11404209012002d03a01001d56100250348115140e030300e070141aa5104480031001d000304803c640100603003000300002100b40d003001d21602030349054080110b00f0343c0c401541d0024a41002e0606142401e14500c50a904c80030380c1c2c500300c20904441c1c60020042212250060b10020064440721003440c0030b5003e003034100c8 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 624255719 1250 624254469 624254473
    0x41202090903070f0c0e0a06081b01091502010f05060d0203060a05040203150726060f0d110411041505041a030a09080f0a0306050a060905060a14040e0702100c020705040902030f 78
    0x1103841c185d000c0300814000c40d102c214217500440c03061151886040240c0d00b2040040014900c01c4042c0a138280003c40824100b2405201c00300758103850680d483c205040c00d0300045011404140200c0c2541c1d8000d02d481d0040c04805e411501580d40011480d4100c1d035488400901c1c0d494500100341070500c8014501880b42034082030190503079200340e40e03002107040d2031203498030010346004141140e074007650300030f600c090042c01d0751229251140c80d200300144103013886900905944d0104060b142c038070100e01685900440d0801011890503540c3c3d40310b240d240b51083ca0035040c10038010941e90000d08200384001c01100244050010303034400c03105950020000da4403580a200740544650141c08007800007424480001150b0500500300001d5a4964407240e91103070a00301030003460303000148100c082103489111162000c01c0c60f070081010340311400d036521152a0480e40a4a000c05500006065620b40740c5400341040c1d001c24411300303450040301c000c1810001030002a19000e0030b411203003224 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 624256969 1250 624255719 624255743
    0x3040c0306060626280f0515011202030601021207060212010806190506030c01050f0417071403060403080417040b120108010e0f0304060f0507120c0605060604120209090307 76
    0x8a81c00104081303040d825001c2c04078050031101641a01441c09462000001d20403200b172590502c1108400ca010000040c0c000464840c0b41403044240e87d010f03106220010b0442c102c0c6030080d42c1c0000d0304030864035030200551650a200300001c1d030f500a60035542c00d58180c0402c90204002c0260116213044440403000300072542c4a161003500c60806542c0000100303015041c0111019040c003805120b01001030140010341104401500d80e6807000a030802085820400414000d40000c1c00c03214103c503010040214074103100120000f4049403c616203e0b9201e0b1f01004002644207921a5109501191302036040715201e0201140780110f400a545210f80800c990543c2000d40c0752040c101e0700544020710281000001c2240c4940590000c17620b1504200000e0280c180900e210b5040d615440c601240b621900392298401d844c10007901d00c00154540c0060020f210041c0581a00305900f00c0380c42c0d15092a201001c0c50004e0320040089c0142045030000f05c82680600581d08c285400182240e02 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 624258219 1250 624256969 624256979
    0x10912030917010606050301051023030402040f02030c0313020406090f091b0513050916030515091f05040606051c0b010902090603061c050f010e1b0a050603040c030606 74
    0x140304103030140e44041e40100b00c404545500502130030046034010788071185180d00301800c0c4014812131203006014419031000b00304000c91440748142d517910745011240d4507421300b44100815110b401540d070070400d0041c81800550040300003203c0e002041001240b064100c2840886c01600c0550f0007003200380d14003203840700c1d40503c580044102c1c6216070221080050900401b4910f00e400b03000b055007081220b084801202e41300e1744001e4101c44d594048644c0000640c03140c8200e00780680040300d80307402c00005208450244c0c800c5030740184000018006900b07480045211400c1c4046c2c040e0045620f80700032905004095002101610003c0c0014001d00300c0341c49030300803500c10300e102110303248001070001694502c0c40c42510001700f4001c041a01d15140c0c0000c00c112401c0a00050840301e00c0f108005000880400464880c14810000414444884460036041148411070700044911b8185920496a02c080f01d000603680200d410070380305e45030307401c11011800c40381d00010a03451600c08003141c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 624259469 1250 624258219 624258227
    0x20111160305010b1f050c0304080601091e0605130c090b0a020c010f0804020906060a02150411100504051f02100e03040e0c27130609150803070812040201091203 71
    0x1a24001c00003030011508980600800070700d401c040c0801011752000a80b0400d108000410b815001c1b00d04890810b034a03002c9031420400e007a845120000d82d602c104168080030040036800c40d0200402c200002d0740b80001040b5100ea0304000406a140e0f102c2080d040540200d684901414440e104c0740d03203030075420750003030740e00d41c4682c40b15408503a420440310180b510508845100740d0340588403805039103c00c0c09000141c0c11065206044d801007144030095061106055882180115412103420441d101031100c2e0f0031081c1003650400074100810b201a0712a551440d0740c0c00e41c00350a007084081c020300100e0800f0035040080c0c0c0b84509000214000c0c45001010304140c0c1c1c071102c1490402d490790608000240304031400e20040841514508004141000b5045c08140b000361445000b00310201100b01261203581160201681d42d613004a164154203011802600f4024002d600e009081d03141c005450040120700d801c5880c460000a086920588170100140482d4118007140c024624010b0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 624260719 1250 624259469 624259513
    0x9010207170406081b19090803030f15031209060703110f0313090603110103050c04260105060102032a03040f030602091002190809040b0303040611060a0504030806010804020111 78
    0x900003071041404a101000b800c08415843e902594000d8a840306c3c42285c0e0203a0400e00c0320980500943e120001a8140184021881500406801d0758503103020300e0400e01c2c460303820341072074040d5014a0394640c04001316002c46028030402c564140c0c0b00e009903c0c0484034800d80640d41901d40c001c00c002c003460094000007a060075550550700c038402e1070f140c030701c8001140c1302d51102800003818240900c14650003640000e80000c1c51740d200c1e520b416280c00d0011550741c03000d091a01010710000c00b1003040e103001e1242c613400c4034003480514603100f00074540000203540d000001d55179030306105c0e01c006c2131001002154018010310300783c829220b03602d05040d4000c0d002800024094400312614449141c40030540001c4800d40710362517513044140d0b45034100543c00001d80c1d030303030095612809618a550108050300c000d2a5035507442c040620351000321801c03e03c024000078040c0b8104001c0c000080d410940069011600386001002543c0754001281d64150307410390143c040c06080b80c805c0380442004881 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 624261969 1250 624260719 624260729
    0x204200a0305130209042003010e1e0316080c070504090605040209060f220207020a031b21031119110a0608240d05070801060306051501080f090102071704 68
    0x10882da5039191400c46860384160700095100c02c1403070029000a070040f810700d9803000d44103640202c2c82088004a42140c00d4082d00702c030320380e1095800881d4030035500560741c9158400d402450030001e02d035048120424040c1c03001041000003242c03040407110201314003002404000c1c4140111141801d00e003008204c00d950990242e04c82030000350030b608000503c08984840681031048002035903040001034945000090420341d020001100545d079405103003001b440c05006100a02e0142c030b15480086596a445122640540c1c200814008154103411407402e41509240d881100594001410403181441d014400c1000700b03140802d000444009018918003030b20006c02c42519041e045d1814001211340201702c001561440c00703160300814040109541c060004141e10050b42c0d189414060241c05c58201030799554020424072005001da02e420108100c2072049050049000070280c800c001c104606520300701010912800c0254101d4800780d4016a1205154618810503a0154094410 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 624263219 1250 624261969 624261971
    0x406030609062705070903051005100f2108042103091a03180c1206090c040b030a0b07121a030f01020c0a14030d0c020a02040608030301050f0d0204200a03 68
    0xc0880c1c12003100008103541208500c40343c0079500001146405001c0c020046810407500724070000003d182004220013600090310081024608454060140c040a40c0030700200e11220204002d0804400440544219603600ca0782c1442100c2c10714488030301c5181d111001d11011106004d40c04280d07071546200300740c8a680da04a4540d0f0313075041d01945d401001907c10360040704002140f40044034000301e43e880fa000703100f600c284440e4480010313001000e00c031003201c2c5504590100440c008040c0f002d02d45001045504010344496000820741c0e41c0c20840005011681c4003012a1009000c0c00354100150500b041c2801000342c00300c5884000403034155081d01912800701103402c00c0b40e040c02600c42100440c40282800481c3c0d03240ca0f01000383c0045003900c0e0380802c00ca1100340e600c090003440c0311040703641c00401c0380e031000d4418041121416800105242c20500042c0900d0742c8050000c403100c507084600e646580142d000080042c00d4248040c400103200340b004288814885c0c000d450310040700d80b0 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 624264469 1250 624263219 624263231
    0x60f0c010c0504050a0b0705010b030d050a1b0305030f06010905060a020d0305013609020301090303051e09030927040c05400e1f200d0902030a080406030609 69
    0x4015100340c051401219846505e041090040b14400d40250031420b000320f0022035455941c601090401c04120003000c000354000615440c4103401a6070b03003500141c205c0d040100c0d500f0544004102e404050000c0c12009600340105595070b11035491000504002041f507951191f000c000a5a1402801d2165010906010001414802008004900809554554801000d000500100c4c5001603d5151481e07a9516074030300036880034465011454440d071000109402d040d00348241100000703850703041c0720250902300100404040f080d2401c1070410351314248400b82c02d2100904420060101c801d03c158068200820b1142540600040303400a40e80c02c8810043e9010041c0050b038011025500200d0143d03100c9a000f01c80b240c0c1c89444800c4140c0003a076600c5280c451420040079115401020f07220581401c2103807140d02c20750b42e10160101c2080904032202511100300d002c1c1c8510115078640d0350011400395102030101000440e40701c11400c1d078481e01d803100a0300820080c01004080c1713150803 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 624265719 1250 624264469 624264491
    0x2010c050405130b030a0602040b1c1506030c05160b100501170c0f0c0f0a02030f0102090d0803060a0b0318100207020607170d020f18011707050a0e060f0c01 69
    0x6421581a00d002412690f014190000903c0c094941035503140d0b01441401c8000c004258140301900181c000804a00d9036000028030481d036061030812800425450060b01c0c03100c0359042440c11044521a0502142d0040008030607501806641d070b400464041032200c4c04100b000008002d4400c00c64251624030f40c42c0c40302c0045617480c949002120140c02060081140c600c2401c01500386e84002040480c138112420050324108400c02510700c0c8954803005524085180a02282d01040307242c80003142050900c10005030748107100360024195840000214400f5110320098102404c050340a00355241482901e0001d10384800101c2c030600e014010010003005414001c0300c0510f81c000345214208034043e210903030588080224070300403042c20030071885441c9941c00036240806895002646840540c007204100d244040242d41c100595241c01400c3c117601500d806410900c10700d030143c4c481072019800e42c2c5038003907000c00c650310100201301d065001080d0401020001741417070090010341d1400c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 624266969 1250 624265719 624265727
    0x102041d010503120904020f0a0c060c030b0319023f0a0c0e070e130204140406050a0e040c03020a030b063f2406030d0804050307151d03040602010c 65
    0xb030184a034140c014148154028200300060a03020760010401442c0038103400c055112680040c0168000c12114a00340b0280000c40c80758000105050406004d94503000001070f4a548100c1120443c181003010300300d09648400e0304444010080b5491101c841c0101c1d90310f84e19280d8884110f01c03084580b082c1c14130048401103500d0748065804a40b00350505e08104000103501c0c4024841400c1141c0890406000c1e5a1000b680a40c6038041c030005076106c1c00c1009000c5d5000f0041080c83c002c900703091041056860348035001003150a46000031000d920785182c00796030b0300c13070b141d00180d070200c14840048244010704600c40e019420480714040080158054601c424004003e1241144612604110b0b2045000c0c00c20010142510a41d4a80c01c003020400103912000c0104021450420382040b281e802c08010b80e900c403003aa418001e017640703032603922aa40d07807040c150000d20aa81c80c800d007804112003034200c520100600b0780c08800c681c06252601e69640c00901c0303030038010343c00c1601c2001d2035130203 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 624268219 1250 624266969 624266971
    0x80106080712110f01020a020d0803090c18011509080105040303050f070c020a0308031b04470702040902100f02010b0a0503070e070e1c05010f0212060906041d0102041d 74
    0x40401518250304a0030301300005100350000c03503815409903410200059803103001c400e640604c2850740e640c607420903c0303149250001068101b0b02480150347c1c0d03149405880340c012811107609400c00344120b03066031070444042c11a075010a03065800c0c02e06110405801d5009248102ca03148007482e9650382c0c0c981e086a400c1c4a0716000b80d0081c42c46082400403a08610045a0240e4600f01811140c051002c103c00b042e40a980300c01140e6a070003000e1443c4e03145001003403000c0840008084d01e2032008540c4001c0b0f0141c82c00c01d10001000c00603200c4210345641d00041045900206800c0e2444807002000d44000b0a1420041c0154030780440c05c049450030100ca04240d600c05001072184270b0802c4146c5401510141c203a000740103803140d88502d199140301d000303402c00d02814182d850a5440f490b0180c00c0d50710010b1407006c003d006010b580129401c5002e2150300200844141d103403a12480701140051100181103403480c02e1011001042c0c000c150000c00480d1908210144802c2c0c25411104603000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 624269469 1250 624268219 624268223
    0x71a090c06040b09090604270212030301030b010e0702010b04090b06011707050412080c01180326160c0501050a1e05042f0913030e0d0c090e0115080106080712 70
    0x1400e01510003542080c4000341d0b88600d02501c0050b441c04403444105804603602340c26030b10080500b04180c2103050100c440c20406051000550640d4115562413242d8001400350720322941c0114002141207100b500641c2038880050010442402d060804d101c5500d001c0315a14042040d41e40c2000f11029640d0351140302d640c4980e2890300f02420304600460b001c80d01c81058131540d0052204000b007280a118141d07804a008078141d030304908528003d040b00408030f040c0b50031142c000104001c0ca11800031038071350120191007190001b407a00007040d1524080b8001c090404e40c030701010811401c1c556482121903c42844c0d00c0400c0c02c00c1ea80081c007d640084030020f00f1484440c2c2341c1244914441c1c41002350b44d41e0b2800350b001c0300361040d0204002d07080460301400b00e4040c2c0c1541d4001e060300310420621004003903416a000c400710f43c0361100300748040c1c4148004265141560060740d4000e611440c44104441405c1441f29981d0412502801e5a4000d110442c0114032000031751a0b0414204101c0c0c44d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 624270719 1250 624269469 624269489
    0x801080c0307061d01030209060c030a081303080c0d150b0c1002071a0c0403061103060a05030a111e1c050d0516060f0e0a0302070f120b0417071a090c0604 68
    0x444030304005130340006130011441c140b40e000c5c000c062007962244003403c0300c45090300080d5291142c1050080048402400d9455075083e1040190003299000c07041d15440142d0700c401e0f96668002801c20402442e09800c0b090740f40550b44000b050b608a020300500c8036a8444003100e2040f019081494201c0c81107040c010a10350701143c451140a2046e64030540c0038502e25071107404c02c1e41d2034032a00203840ca220790b1070004000000030400035181c48048030010f0601500101075010217544c07043c860441c880d50701481007444c8a48492007078050483c800d400240030b4a40b80d81c00300140e8110b40020400d50040390319004400c0ca40745098860b03000c0d14050700c01000b00301e06610950711058000c02d1901c00d521181d42e01e0b0b41e028195007008110181c03100d0320a6004010b0b540c40c00007006810386017500442907143c0c040903413001003292184c540d90010741214428140c40c50000c42d50f1300902c00c1d500003d20f000940701d40620380d0240300c07002138490041e41302903480c246101010020548030740c1c01401760318 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 624271969 1250 624270719 624270737
    0x40b060a090c081503011b09180603030f030b12070f03060f050609180a080f030906151e0d14030c0c030706052203172a06130c030605070801080c030706 67
    0x501340721125400c8010b400380000401c0110355603c40031003040414100b01284049204100711807515406240085e00108100035031421994020b1000c140a426442010f88070840e50b10f01d903480b0110000004440c004486446075200c0007400c500c909484140c500c0342c41c108100a01c0b01035802203a104001c010542100340c0e0324004440041400c2000c402001c0c400c41c071529001800d024000c2c00a642074007225038503807030a400000c0c64940002e10364a4480310401d13102c02d5585035400103000c1100d031103500a2001d04004041140120090703005402d0000c901007041766000040000c02922000c1c4050311000f44080080c150381b52554030400c0001801084891003e82c80401040700035003000714015800d650300d03100e80355a40c3e80c000040b40d104070001807148200c5940c0000700302c10341a4aa000942d01c05034640c85071500d030024414a000700642e0380302000c02850810840c007855000340300f0400c906100b079009007080024000d045a41c810341c8050f00103441e00151303020881e034090b0303541607103 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 624273219 1250 624271969 624271981
    0x9010504260f0a0801170f030430061b0206091507051201090209120604020a050d050f0d030204030209010e04050d0e0a0515030603012009060708070b040b060a090c08 73
    0x7001400741100c2000c02814000e04807818003000003820060070640c0c07000d84950420b107558001014501480710b20b5400340000e41400c0201000390307402c9610b18000c00205c0b1591810130a8180d0021001415480101c0040c07000c01649902c00000301c40c000c9542034081410103010b903514481510300c01041c2e80614400030000703e14407400395111540d0310788903041c90044403c410300741800780c101c49182500401d00315000c2c2090b0121780d0720000300400904075420a900440c005050a0294a0049001020140030701100b0090842e02030710380411100d0f6030070750690080003034000303020407071050f1080000041c80b040510031a50080d0b81050103481c2c40b001c00c80060b0b411010040446da0040000c12002960b03a03107803103823074a81e40d8840302c02030784c4ca1500c2001c05017100c0c00c200301828a109051f84070708501c009070040d01c01050301a505d032a51151281050186030180d014010300140a5000f04001c01030b4441413240205000d0f24502e4401c2c0d210702a04003601d8081c201800051142c0e000212 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 624274469 1250 624273219 624273263
    0x90e030319020f160c3f03170406020409110c030a1d06040b0d060e100e100e090a0c091802010c02190f0806060301110414010915030e010509010504 65
    0x8542070394101c80f6290500480c03880000c071012032419a070380d1200401c01c014507042c84482c080c59242c920400104180041c01c03081000c092880701a50a002a441c03000815000704451982030712507954801940c5400e1070300c10003070350207402040300309800c00442c08040040c55040e00c11428040c2c01440c103003a500c2d0f0003262100c225505034461101514880c00d01d0762261401000600800b840c081d40d545802c15000c0281c401550060380d00c4501c02d010084000184041c400954078203540e404050f403174100001454466035000706042449030000e002c400d1100017140d05229126121000c14207549011120031140140c40141d00c1040c80501000158070a01280300c01c24401409803010f0300e51180c0809214201d038028241c003c0120700c0600003101d040040c154024012002480a0071a189080c01540a603228040a815040d8a4451070f0f030300440d603140c0030700700700c0c64003120001078030200802801500e541141c003035113400046421860103010f028400d039049403103c8a0741c40d10502030f01c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 624275719 1250 624274469 624274477
    0x307090512070e070e03010522082d04060f020d0504090b0307030501051305071512020306040e0109030201050601030f050103050703030e01020a0f1a010915090f0609020c0304090e03031902 83
    0x4550b070286500c0400c081500b030103c00d008280580d00c00f040754049905060031182c0c00341c40010796088500d103045c4146003c100e491002d070b41c0039190301c0c0c41e02069411810b000c1082d001c2c20f50007560350b504000407400504080e004030b81031540c4111030800307c1074003070303840b070092031000c0000607010030003071009181e070360000950204043c04175080c41d692030316040d084480603290785070012500140c500c20b0120400c03014010b0441c68040d101544095003000d8646082140030308031540e004400250599121751088020509400003480350035000e01d8001c0c0208001c613040307404030380b6000c540d102d080c425104490584c1e5101d40103015071411a24180d43e134030f8070450b46c0c13070440c0b01c3ea028250006001e2a41c1b800700c60b20030480029a00c2110b032340281c51f450705030007590b4880d00c3c0000e80076807150386000150031600c460b100020b600c8900b6020401a12058001e6080f0038000034813500000700010044c42102c50910040015513a0200c00ca612480152041d03500c2c41c0c0701d0948413045429940c014 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 624276969 1250 624275719 624275749
    0x207060e030703020621010b16020f010c021903030f0516020d0503090d060603060c0512070c080d0c050301050a080a08030c030619080307020405060118061803170304061103070905 79
    0x680b800340c1d503a8009111944460708080034007018040c07030200440d0422059001d020740420390707410b2003041582550384c2003115001a10800b0f590f1203154081c0d0081c4d0769114555000b801d0442c6c10700e0140400b94401c1450321048000a0008650041e924860400c0c1c07003803241039008060f06072140d9001c11203002e042e03580c16503080c0000c0142c828203640d01c0e803000d4000c502c21000400c0e204d01e142803000c102c3e0740c59000e00c014008100700c4920301014a2403426031150b02d41c2401a2074010b0b50030411404d005544149041c2440d1400303040741d850700000558103c90040700e2021036940c0706e103a403e4850307941c400010a944018004070b0f982446ea1400713154003000c05001c9c8500d10284001000c401300c11035100c02d559800002d0042d0075400c09005d082e0340503400382002d400340e910048041c0d4001402d446107504119008a00c400300c2d0381c519888000441d0480d40c0c2106542c0c00ca04400f04640c010380381260050700d041e40e625004007000f03091702d220301055110030400038541024090220110240 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 624278219 1250 624276969 624276973
    0xd091d0c04090203090a05010b030c0a05060d0f1d0c0d210509190513060803030a0b0d060e3009151209030a1103090607020f12010515010f050a0207060e03 68
    0x860303080e0b00782c0b019612802c1c01c0d00041c035100c1d000703041180c2124001980d40b4000d8106241c401255240e102c0d001c1c0454105944043d42c9581d9010740000403e409a40041d0317260825054954444507107109007000c40c041c40564400c4c12410702004400032200030000c00ca20082114000348000e800c4404040c1e1002e410803501c4e151511000580d03e421805601000c0900b040c4240b101d8103100580080c2c652050318100285410041115900d000040004465075185c003010411520341c500b0700c141c220b601c00e034140301d00940d01400725210003200c2c10036010000140880348029107002e402c0c1002604200341c040c6482109414401c20099000c1d40c1d4140c900204014143d10802001c014803500c0202d001c1c0d502c0300b0080b0001002030610441d081c10b280c0c000d20101040340d4a0394212055143e04a540385070700300c2c81602144a0082020703800b5046d510741810000c0c1c1c000135002c003008101090384e5468500e00c4550003501d440c01101410380042c0c1c0142c0003400105e0145940100380000102 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 624279469 1250 624278219 624278227
    0x1303083a15121209122001020303062818050a321305030a030c0e040e1203070c0803071e0f0c0b09070803180a0e070c30030c020d091d0c 60
    0x100340e1706910101c003044070041e0031520510300030200001204031200f0248042c502c2c0d0300b068000110344425803685205078203c0c00c0070081e862000141042c0c010113805064000ca0a040840316000340383c00c9691003161030600c0705000510140a0b00c00c201108102405480d01128174074515030750000400c01d10103041000c0032a80401d004201614000d003103983d011911184940c0001c01e0403002c00d0b00755019a041c00e14041c04910040b0300d11984202c903407510b50f143d503110607045808465151000d42120800014030070525440004c0c030b229801065090700c560851741c032046035950310b80e13000c40000400d1a40c0c0c010004000380c0d6440d4000d106103044901c095110329050342180c0c80021303e00d0f007101c1092081a03d40c00c1c581c0188000304407401d00742c1c07601d160201014080e49405100208103e441549401400d11104460501e41e10303803c0d4a11408800307040094010b01c00ca00ba0000584522106071095074402c0d681311098402e51215482a03505403a090070701128040c01c10381501e90284 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 624280575 1106 624279469 624279479
    0xd2906090d0303020c01110a0207080705010503061c05010f0c09060801171509070e010f032307050f04021b060f0108031303083a15121209 61
    0x1007405a5035034818601d06005040308401a40281c2010507200548c0b9030001c1e000080d90300134800c85898941b1400156228002147d41560007401c58101800c40b41c542c0400c00b180724400d0b0000f003500c4840c031201d003060740c4013036492000065142030100591544410039078010008a40b2522040d452001100d840703001c842c80c03207e0640c2c58080403846100d010448078000382469030001c1d0791075840b2041d01048904c6844244c0c1d82000c5680c0c9011082e59818100c1450507402000385203035880c00c014420032140000b90142e00035401c1c4035400320840c6d0441411012605000a0701071850b0100303184403080010781095801c1d502c00c4c4240780d136680d010081d05007540d4100c0386685e110350f00c01d24912650910018521041d2031006a84100021b81014a8031b410301d19400c24840c201031000c1d05a0400300364410800a00700750509040482e0501d0144103d6801c1c0b4a410140c8a40f62 = true := by decide +kernel

theorem cover : BRFrame.Cov 624100719 624280575 := by
  have h0 := BRFrame.cov_init 624100719
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 624100719 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 624100719 ≤ n) (h2 : n < 624280575) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
