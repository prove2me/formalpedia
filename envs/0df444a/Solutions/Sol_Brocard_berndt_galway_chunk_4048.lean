-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4048
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:25:20.68771+00:00
-- url     : https://prove2.me/submissions/ffc7ba1a-aadc-4577-9afe-ecbe28e9ca4c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 727877697 ≤ n < 728057553 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 727878947 1250 727877697 727877743
    0x51006091d01050f060d02010c0b0a05040506100b120903190905010e040608030a0c02030316030305010f050603100605030714040f030c0b1608090604090e15070f08130302 75
    0x2a10005005410301078009403440d000c00102041c06100345800780c0800309a001080d80c41d00140314030010846012410043c86080c003030041840580003d014142d0210089801d08050410b02c3c0340c880c000d49454000003521004000282446c8200d070b0319800701d41400c000d65958144902c1c01c5002e0300e9546031103c0014604050f5095100d210b5205881098a482c50490340c40c80c244005c0340c8241c012003401c0d9204003c103908180c050380c81030321101d04c01000c41e0302c0c0c043d0750f010303200c1180341008046000c251a000140142e6070309030051000342005649590941c0340c0b152424403c40e10702d1041c603003070ac0400000f0035241403054a13880c244118003050710366519030741c2102c01c21101e03140c1f2080d40c0d00208641e01040c8a0341d420110355409071030013400e19081c8059110740d81d082c0d0003000e195610034000c120001c0c0000c0300c0c2c050316180c200000080c058140b16905501c0300302c0c10042c04001040f030791501c400c02594001c851560080c4150300c02411080745480c041c1d113803c41c50b2a140410040702c80d1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 727880197 1250 727878947 727878959
    0xb04110d03080108100209131a120601150302030f040f0c0504020f1b07050d060f1805010c020d05040501210e010e060702010f06051302030a090c0b0901110a020616051006 75
    0x8602e0b040321403100403902c11180b610700e184100e0140d480402da100c035250051085810440d002808460030000103a004050070000241105101c000010043e0700050010030a02d0103e0900723412408583c1404d515514000c0802d10210b0300040004242011401d60030b4240145a0410009084003070802c654030005031141030300642000182e44103450f82c2620b40207400402041203000c55002800c80080200d00796a41d801804030044145400b9030384444e5680f101c02d5075a1a0004036014400004982618a20090070010f50203100310178000108010801c86e41e0140c0c1d08100003072209140800d16980043d40005490000b002d8251507003032a0240e034910344d000c501c05000b08100c0d0001c02068111001850a40e54207204883e030000345000441c6041226800659001c84140b800040b503500e290b698038100062900402c2d6802c0d0003140c01901075030418540d0020000e90001025500025400100c2e24418514005002500e0480303a03030410508100310165201ca1003424004192203074 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 727881447 1250 727880197 727880207
    0x9010323070816031103030408120313050106030309051309080405130902030d030b0108010905010f05010f05070c03050d120912050c07031202030304030f170711030d090614070f0c0b04110d03 84
    0x400306854034201070441c401700e0315001080314200c0744100040d0030200380c04040b65000e40c00040130f4960002c40c040351200065020300c14074020b0351113600c9190905e42041c09000c902c50326506d034041003030b2802c92140e02148035002590100d8000b252203218044540c165500540303450328000350580f03d800783c482c0c2c1c000c0d0541c21010725803103381d89408242e0b903100344920584601380b00d0030100861842040c4515403144100b001d888182d402e240e89030188550722404c41c41540d034800e4545802104010201a41c00241d8400c450036103901886103001c075448403091250441d50710340602000180c031648900c801d00840d001541c120043d41c944241d0798401948990044130700b14005041008040d5405005144149aa10307458070031104c282d803003c42c191681e610704400880c0903c0240301d020319440443c003a04420f40e01c500f00105900c03074913500220300f03010060601c00511041520304015160b000c0101018940c00c0400142c0700d8559051010180780306180c0c0c81e812201094035442490303002 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 727882697 1250 727881447 727881449
    0x30f040e15010203030f01090b010504150807020f0111030105040b010908060405060f06060c19080c070609051305060d030e0d0f1103070602010e150c250303050609010323070816 78
    0x1d01d00c00c006403500004903180d110844101d810082d080005005198183c0c4c48000012011b0608501d0140c5408805100c801003400741c50024460034100445103034184400c58012410f0f5000b4420403028800c0001d00d40014000e05000b150380d40c0601046070f200d00c3d840c4c4000c00080f01511101d0600342000c40d00e40710203c6174601d812a45501154041c02c01d441250101e41540700a000c0140d10703ca508103a00c080320000340c4086a0a004800c01c544050011308024090740d1101050985407109000c2c8006283c131805030010f2801041100030707120515590322003681480e02e607131420b002a000404682c42103001500d06400d8038070100810020103030b4200c02da07100b2011a080315540302030403130a0340d000300c6200c04940c12407072140320341d5001c50840702d8101c200348201c24104a186441c1540080106410f215a00d42c500140c4040c1501441010380200d0700b41c90a458642c195107170800803801540150200045608049644110074031568005d0104401a290403220344910001e40c4081 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 727883947 1250 727882697 727882711
    0x120c010f020a091e0b040b0702010e090901060f0f060219060f020a091d090c0f0a05040e0307120504080601050d080c0601030818010203032e0f2402010b0f06090102030f040e 76
    0x100800440140e00381c4004d10032581d02403017241c9810b003000030220040e08035550403418010026036520b40342d40c8600403148203801d03540c0002140c91403c1ca040d8224074065208054070780040364140100365001c02c003c02034002116400c1000c0400c1d2504000416000f1203010103c1d01c0810a4410154000c600a0031181e0500307034040b105c0c68244540d0701400b015a01c07260b55504c6990501341604200f9542c2201c0c11004040c201c44550ba480450700740c468402221a1640000a144042003180c60000c0055505860014146424000411b56402041c050300d480344401e4a1990304100341070003181c203401d60000035600355594a281940b815040000c1202d214843c40300c0840040d4400010780e071103404822041a1901d11024141880e505070821a0b8440e822001c00802c020511003251402007080d42d0241c003219011960000498035101d84041c03c5906001120140e50b60780190b09401c003d00701c804966a00408006038070b0362258010f0118003041c0401c2c000ba180380351002d600e1040030 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 727885197 1250 727883947 727883969
    0x120115091a130f020f070b01051008160818030a022a0a1a070210021501050a0b0304062a051e040b03040b0a0b3f120c010f020a09 57
    0x3100e840040d07589180e420106402c6202441000b95261880d004501c128030100001803030041103060031821680111010769000b82d5280040200742404030f01c124200101e440c001c5000c1c10000c0e0700700d040c2c940b0600c2010801450380c010807006902c84000c120400300e081c0442c0c3d600c0da01108003a4940e0020700e40700c045c40880d10f41d034002c0c02c0d00d100c081004d00c0320300030040e000150070600443c1c4c3c0701007500c0707011400480030700031040181c1f60002e01d004a05242c3d0018400d480510f00000c544141c1600300502403400c0e0038082180703410841c00e40c0d400590185000c41c541e40040ca8004101441c407000c80701c81680c901d1072102881e00301004041880c5081109030070000b01500c5034115109510641008510810005000c070341c00c402450703041800442c001c0385210301100014a440114500090070030386008508001c28800c416804c1000b0755510342c44031f0001410390a40d12114810017a003e00e050000c3c0c484c45000080d400402e04000c4a00d0443d114002d210004202c40142d028020a080c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 727886447 1250 727885197 727885211
    0x50402120708151002061f14061e070c03060b0f0604061d09131502130302150c15060909071a0a031e090308010603060b0a1119120e04091203050612011509 68
    0x147c0403019001900d0511602d0a5503102c1d404c24054a40d010190816510220100c050002d8550300000c24015020b00c448510060139401c1c40340869542a850900c103080c01203a124081d2280343c2560111102810541c10341c5002e0025030005010040c10b01da403100d040e0080108006d103e081d41950640211030014124050034450012486036040320381100408080800040c0340c0141c1c0ca040001d240d1120b0343c103000030404203e2900c101204500c8a26200c2c100b0043d51342443e040c0264071400d40001050143e18181d0001d60751000200c20780350188000481d92101c1d806500121702080d1500c900c0d88000c03080c08120390041c03042e0b510803800940034000000f14140b0900a0406030307465030014500c0c01c800034006039101c11703c010614602e0300078010303061003002c01e06220501d04c9002c3c040403003b052207007000900c000048031100d40310b2490101c4100c0840c28090f001200410181030000300e5840300b4000035030f03007000d01018400540c01c1403d00b000b0000905604802c0341e4020a06201c44 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 727887697 1250 727886447 727886491
    0x30504061407110f03030c060702011e1b1101141f0e0f0606070c080307031701120309122102030a140901020a12030b0301020409021305040212070815100206 69
    0x944680300001e0b001c0f818556103808180b601d6024508101d0000b0122840d1030f103131a00c0360341444012140f001c0580d41d584150340107200c0324190b209e408080c8142c1000040c803410f1807403552002100300c400400c41507100703121004400b54800c05480140745501a1103107803481d44030b00c031503280b001840d0712407441800018500498018880c050b40d007140e0140c1699030383c9814402d00b41c00603002990b00442805e00004c1000b030a00c02000700138000d95654032148454102000c4c0028180e100c0b038041502001208046a4000e0b841415903c3c000402e90258800342410744c1c502c500c07401035960640f114108007051540020080c98003100361340b60482c00030700c82c0781401c0f907501425078070342c1c0988c11078801080054140001107115407800c0c00e00040349078450340800d00b2078105801030750070f40d540084c143c0c41264000c1c0c072100003072004680c2503107441010313107042d440070901820b10320600c0126004128005203040e07240325200310241516074041c044142c002d43d60407090301c0c3c0205070841e9840403016 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 727888947 1250 727887697 727887737
    0xf0c080102090109120f0215090108070801051c110307060507060501080a150b030a171e030c071202010612110907111e0705030106030c0501180f03020405130f03050406 74
    0xb91800585035071801500d481c5da020402c0140b904201c1d9002c490701c901c4c400694074007540c581c9942d2402901a00d940700c844c005000c41d04054640c1043c400050010001660703450207001131202502c00050b900d00c954549140e80180310079130590305000c0c184022a5060f808006484401e02a500a0202d660384581032912960300303410241c2002540e600078002c1c0e40aa0304904e034164406000c486140e03407240c8071141c02d00c24107141c2c50142540010340800c2c8200d00c1d886a01180c4001143c180741d03080031221610741d403182e080018000f000043d10035003414002c3d40140010181d07003006600d02d242c1450155041081520218812003040c00404d41542c070030041a8000e1081c40d00900400c103002c44020004c58100b0b403003078050704c03541c01c01140b507482c00e000f1600214400c00e1110030781410000090000e00030780c05815510b22501c08100f010f04007a400315011039406440002e0252118400c0703d102030320b080c40140ca2080040384070803c055101c2c0060040310080d5035004010038030b8142c0500 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 727890197 1250 727888947 727888957
    0x81f2003091009170708130b21091e1f15060f0e040209030c120a03020c010206160f1b0318050d0506010e270708071703191b0f0c080102 60
    0x101c1c241803d13072510005080d0004200070350241424500b4501d1401113640740b01c0c410342090407808d20118031640301ca0a108540950050441032038482c2d07240080d85c1c0c0e680c600203114450900c0d40c00e03450310003041a0a001e4050901c0440c0c0341600c8806600c0d2f12240680725042001038000022034000030341d20321a100c102d06040c034580c1c4852060244404020103900201d560342d038103010f00e4200720000d50710b49800f030281000100250014050906002e0301300900145124195000901000020081d134000010b500b0380f241041a01000400001c4840c0d041e20080c7e500e094031008000b90515400c58040e1020b800c42d81500c41c1c0650b1a40c0a00c005001f81c0240203043d607104a0051141c51101d0340407070791200d80c9164118140c03071070301205400002d03040790b840115000700800b4003e02c10140b04407000781c00080b50780080810030108103030340c91041c1c45c668403000302c40500003031001344545002e150400300c0700b904210b810b901d4200021031640441085400a8820000141c4200706000381d030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 727891447 1250 727890197 727890203
    0x1e010210050c090f031f050f16050f0a031503050627070308071106041706060f18180d05040503070801090305040303181a07050105060901081f2003091009 68
    0x641483ea0b41d40c2408001140e01035a9a41400f0b1201d8850b010b00c1d42084a00c101510410041518241100380711403110000d010301000045580060810b203420404031031404000d0100e0305d9071021000780480050052180c0b000c4400d40c0c190002040c070200003101401081402c84074010071540b030aa40300c855951501c032a843d90419481080400d14810141044074007404d4046807000c48040040d444d0f903c660001070f0159001100c20185030380401c0115442607084e900032050601400009800c098000411200da100b42000180c0120416910390034621414084449801c00020080c166811500486000303220304000011826414055501c4098040d1156442c045c20364604450241e9042c4021980052a0000040110304080c40401a00c0e020782d007692520798910b401420750300d0141000f84101c003190f0051241e440041514000c02044d0b401d040c0c80c4804440100e4054014030030b40340701c0700101c00e03210303000688242c0046100301664800e03034201c140403814034812155010405 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 727892697 1250 727891447 727891471
    0x908070f0b1005150d020909010603090c06020c010e04020a030b0405070f0311070f0b0c0f0a0503010f0501081605030a0e06090705150414042a1d101d010e1e01021005 73
    0x7000d402902540117009158107044054900f030120300101d1403290081c1e0210000981d83c904000034040386540c04006842a440642103803804000024600510681c1803485540e00068490140340254002d0382c02c02c41c0604144140d2810304030207030240d030b0044140e00c0402e003428403080d0441080c0c02102d88082d03001c015041c06845640310100c0d800b034000c00c42401144104040d08140802501418407240c10340ea51070f503a50b0501c41c002c403586000341d110b01c2c1030005084c140401c0280011051a1501d4146401500d9a5540504001602041c1c401c02801c1c0200c00a109070a0008920041a00c4050366440c3c40031076074241c010503900c1588641c09140c40c0c1c0f060703032040b60b2070260003460011712070704900920000b40040c0c0e07102d0014500d040c000451281e801489500f40140c01181002d40c017240c0080071a260008050601518051076146441600070344038020783c00781c21072040014000c0d1514141014075408042440d840f000c04030302521540b04d070011032892070300559100ba000e081d58 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 727893947 1250 727892697 727892719
    0x60b04060f0b071518060c0e0d11010c0615170105010509220302071d180d092d1503110711010c0201030f0c02070303030f05150904060908070f0b1005 66
    0x2021a4000d0b071441c03181c0803503202da505d5408400c0c0c0c41201c070078131402888001050711100001070481c40114040783d009428106084011036648180b030420501d080c00d045140300e1143ca4004000e010140c000c81c801c11200740041900480041d00d100740c43c000200800990740c0303d00400100000c1210041c0d48559020b915100b8198403a0001d038096100e401200e030703241d840300310512441c10100c41c03064101040c1c0c2c00f00021800003100c00e080e410300c0c06000d09030fa00d104450040c00340e00b060107505030303024065640030901100c10f0000364040000c0c0d1400a006a103a10b0185948260140d0303542c002414488070404d03502da40011261116800800700c540c0021140066506604101041e810f1681d60704480c0c1402c076103401010320b4405c156020703040e40d40c20340c90017404036440e94120f03040301c5191a040040100d04007200c0102c065003103a440d001507550f880c101010b089141e10041004001041c42e004116080380500c100b80d00c91072890505945d209600000b1818038403400750b124560b105 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 727895197 1250 727893947 727893953
    0x3050c0f041a160b040209061206010b0c100e030a0f2d0c06051f0603050c040e0603030c0a050109020906060c0703031404120c061e020a020f010306080109060b04060f0b07 75
    0x10302c1031003000c05851400e0601606010420000241c0001580c2c140508820001189040300025a1001c811203c070041d003142e0200d000d9581d0130501072803503140340000362940ca401d8100300c1011403d40d043d8085c08042c001d110010380b03c1c3c000c1d070490008104e0361500c04000300c1c00b946260000d85680c550102c42c40109112400b19002c02050860038040030713010f40004501c060080510403401128655101c0e416001c2d8200018502e90181007094a4181404503c1046104440488042140c5206075454040c0000e04520900c06504c820b40b00d50040700d0b0410106402ca2090b00b03000300d0b51488555136010901203136201c0c400444c2c082e50002074040c070009000321b0381c00407a007401d000c0e07c1d4105030302c03801888044200d502c429680060201010490103034407a5250000068548164000340710314031000e503881c0e0038600004d100d6030f102000c1c2c2096034400c1c0e11202c01040700100901021810341407541c0241140b824440c0158100302000c1aa24a134610703200450f91312511552030034026407 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 727896447 1250 727895197 727895219
    0xc120503040c030f050109020f0301110304200d051b100e040c09080d09080c12151e0f1602061e130f0320070f03030309030e031c03050c0f04 62
    0xc1c811030300c0001c0c254010010072000514180b41c68464400003800d001c0c94010403283e004103a41c030314403aa040120200750f410066041d00d400a074002061075400102d0840d0403584505500c0f496004118180300d68140301c000150140203c16003d12010807031420401d0019400160341c0c203001080c20360307000d03207020f0600354403012901a25103062f107856511001d080d810301d1005007050b00000c08103442807000341810312021407500f40c119191907500c80e21603130301c0782c44040f201d201a03802092400029612143d11a21000034841c4080c0319009107416080744042c0c0d80309450440a07070030b075018440f001070300004009008404004000341c055007044514611040000c0c0a64101e00300403041c10f00041c0390540c068405846a15038143c80250740001450206d00781c40400360950103075070100b0104840c0325602058070f0701890003050000d89424142c0b11050b1804900b50144200d076240461140c0b000c60a090800c9070781d4081c41207840310585880a805220021042030504003c02c200800d459 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 727897697 1250 727896447 727896451
    0xe06030c040c05070c0e060a150e09240901032a031403120a021801110f12091504050609010c050f060c04091d0a150905060a021305010c120503 63
    0x40465041034564400308065440b00382181001c22008034a81d0300b0401c001560b500904042d001c1210300740f82007800a890f4292601c1002c100326043c000416020340300d0810111008030190441c2420300b81240241c0008040c90000307a0b6202c0680c400942500d040c1141e54120703900300076050f070807403551550829041001041110720200301000040042d40401c81134410a11040141d0b0300c651171a814040500c400519811403d481048101003600e100050101e4007442803030043c030307901005050301e40307010101c080d0000144682c0c01800c103c0724603c001042c4512040d540c644850111240c55140c1c0e00681c015294000824400c00145500c41e2003066025406041124800410690903e040440c29103c0c81020f040000d01801142c0c40c50045c3c3c060300c0d05074000c5c030f120054007a40e2152102c50404005100721310703911414074045910381008850b00c1d0020250b034014100b0000c0c00d0001d50012024942d4070204d041700240543c01502a80d44464000d808941070107031300a17040340d1030303400 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 727898947 1250 727897697 727897699
    0x4060506010e0d121103210c091f1806080c030912030a150b0702010507060b03120c010b03060702190318090612020a0b1804090203010e01020f03010e1f0e06 69
    0x1c008040200d03a950181c248426401001e00d00010720038440000c0105400701741020065000b00500094a5141458a01c0d20085040d0300409034072600d411714214880c200c0500d5000c8400f1721890798208600e009140c50821545681d031031003080c582c44d00300c015020b2041c00d010a8140e0002420948140025584900c0c0b03e0191048007104258400d1681c1054270030b52141da990b12045d42d5040444d1480d940034100d4241d900341400e80030740c0020181d12076070100801c00768807003000300b4858804022140480300c1c01011151a0411003940c03600802500000070b204e48501e00114104d5400480d5460588c0410350080c0010342c0580c50030703901d40103003030600c840303840d02c0c100d0000c1c08031980d104500c081d03c55504c594a020b1080c1c01004180030050304035a80c11031081216074030030203003e40c405d10b2112055a0110384030025000080c010169a80110450f500001c1d42d40350070100d240095058800e00e4100c5c0c4420340301d1810311228240d043c1c02c07681e48400c891000707102600c240495260b20440c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 727900197 1250 727898947 727898957
    0x129011101020910021c36030209070c020405060a1208070822080d020c01050901120f050408031006080603100e1f0c09050904020a03030e01020a0c0b070201031a01080406050601 78
    0x1c2001c184184a1320301c03404016044115528400309005d40d02c9101c50340c4614010080814400d2060307400c6003000d00e094560012203040b82400b03566903400f07100440d0000e0240781035240143c0c000c1c065490814003248228a070100050486c6401c11400c07003684e0a021043d07100000030b0b968203080390b020340030039a8841070600c028a020180c2d150700201002c04e4006a2595a01c1d100c4020302e410309842e401400e41d0010110185240da028080e03560000092070202d4403494010700d1080107282c0714090402031410442000244007180000310700a1071031001a09030319540760801c817504d0304165042940350b000250354460940d80d0750803204107005c13440c0503100c1c2c0c1c0c90185440f01d10b40d89007140d480d0455403240c000c4401d107604400200014513007500c4040040c90a0ba0010350130540070300006040c4900c024486600c0c2e4420801d400e610750f0f00c0000790080c0c9484541020707090b04030300c0c81280001d003041d0445079401000b0510100341d58040c0c45000c1c09846665404000c1d260080003581002 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 727901447 1250 727900197 727900207
    0x1a0d0c030204180602040f06080901020306180a140901020712021f11190e01030608070602120a18030f1502040e06040b03010f1103010e100b1b0a020604080f012901110102 75
    0x904d00388000c20040c0f400e003001d1030303240d4a404400786c00e250008219850b180d00c140204206500c07038561401380c54881c0110321100f036603040c0c100b00c01050034a41d00809007184800304800600158003c1000f1402010b800120260782c5100b00c3e41d80618030890010a081040070310a1652160407071003407a01000203103030504c2c54042d2000c4240071079081300e500040703107226031b01c0e940e58041c401d40c0d01610640e0b001d06402e90030404003a6480c2124620900340550018413040050320402d810504079100e00c4518907000d981307041c00c0b414100308080a840816207825220329012443c400c8504a407070411181e50f00b99588801c102c02404680030040c0c03d5500c40c0703038120000701503104c0d1000d030105082200d500c075410061140c0040c00700400344403224140b030b40144a10442082550068504503201c41442809560401e0410405610094000f40d001c580131960080110701d00c50300001400080040018a5003090700081c0d1108007480d5080c0018008512544031703012001040303138600f00240c508 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 727902697 1250 727901447 727901453
    0x8120a0c020d060f06050405130816050d18080105010e07030c210e06090c1810051005040305100603031215171501090c0215040203100606031a0d0c03020418 69
    0x11800b0034011aa15a500c996624000034940b1411024001c2030303a080003585800202d40060701b0799014007a0454001007000e581c1c1c0005022034000392a406825141c0105c00444060007139043c4141d0458200c490700404108140d05200707082c126203000783c550641d600d803254146c0003020409914020003400600904400103410495042401c0d1610700044a40c481822241048006400201c2d660405021310341c0c030b541c441c1e48140545030490041c0040d51604c104202d400102a0310081c0c000d85000750100c0301d5a0400090400c0364052030030346041c92507051401040fa0814003001740412031800d006400f061140e4081c040d484031000d45602c440380c03a10704d0205902d181e0b0700b4940c02540060281c00e402c1c0340701d10040e401040e848400b48000403690f080a501c5500ca01020855401801c0020342559020041c540c425045050b0030030201e500d44000070043e208210344501f6221191407900c3e1181000c01d4400c8801740c101c04100b24160a5034200302c09894000c0103101c607500d1421908001c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 727903947 1250 727902697 727902709
    0x207052e02060108160806010509101a0703031a030d030c0e0301050a020d0b0109060903151b171308070602130317040e01050108060f0f060f0d0e12030108120a0c02 72
    0x205a40580082c422507140c481d0007454080001e050b000303001010542000a00000104141541d1040b5a04506e9603183d10102440b0682a4424030740741240302ca00e8600300317100ba802404041d01031394051000003840c4112030070301c071442140320382c165021900001d00756100354440d06440c0e016103060300103c40c81000007404e45905541600690741d00241c6d90145207020300c61a6003144083c2029954540703003100280c000340140c0300c0030703151400b8480c034580561465408540b42c5541c0d40d03800f580405c00c21034010030b90300c045984048482c0702e0001040c3c00a224005004031303150300c1300100f842c1c841c2030790b04c03c006500702c0440d1984006944001000244031000035050846c0120201c0780c40310300c0d00300c004003001c4041c0c1c8070506000c034080030b10000e61540504e888030680241c6114104100190208000d80305035000c141e00c11a022030b800302c4102040e000649010342e80b800721101c40351200e2a04c0f07002c4c0310030301c41d06040b54007c808444002a0000c00f0380000d403081e082c613000e580d84036004140 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 727905197 1250 727903947 727904029
    0x7210b0108070e0f190806070e0d12020114010e160813021c0503030f09010605010e2b020a1401020c040b09060909120a09080d03111e040b12040b090d020705 69
    0x60b49030312817402400700c038208103d085e43c080542e140c60b0b10390080603c089040140b412401410032080e1070444401113000b5040840c0a031460410b101083d03a40d200e5030700c2c00050a03186c04181c840c0365007a424103184540002801081c405102c4010ba428a50030400303030b0900078190289030211000a00c000c940240041d6100d201d018515030080d01d010059a403c481e80303504070506100c800c071242c54594031007402031020030b204d0003101010140d0584d221001c004001030b0080d880410414045440b00b03002e86422841e480c01e800f102c2c10960082c0800c000c0e80d010424407600300d01040001441c44c50030a060300d810864000c00d0b21075481d4134804450b0715600240c80e00c4003007901070310100604402048000668121440d040004403c031001c80a618441d000034a1034103170040100e000d041e20200d00700d800034003040008503a2103030725118081e14000122020380d0510000c40010b82200b1010860000280e2903a014108440c1090200302100008200c050703a00803100c0034400615048036401c00d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 727906447 1250 727905197 727905229
    0x20d02073210080730020a051201081b0405041707031103070c031e0c06050c0c03070e0a050606040803040504020f070213090b0603030703050318120307210b0108070e0f 74
    0x30601e001000a4000c40c0101000841303500030038a17101c60519040804040b54a0007080075940d54481d010403926800350816510210ba481c6000040720500000c118180c8052b4040d000110600c1c801000100c481c1110302404128411011580a81d0140c0003025024402e0034400701c5035800c2c1c41160303c0c0d41c10014003120000e90200c1c0034818405044642da448114000180242000a03640d1920190a500c200000d1110125460b40d1a083c1400407010004000c1c0403910080da8030a2401508041034079400041860680070076102d040400881e0140c5003090015490245004140700007035011412041180c05e080c04058010381d14403d1920000442c3ca001103080e9015042000540b800a00f83c0c51081e841040582d002035001407c1c0c2707a01800b158940024041d80c081518180005100d0b00d45415800004000c3c10f15040008030040240c9880c1c81032250240044031400c0381c809001c810301107041e1900207212a40b140340c154401c034201415041c451060940425000311041800c4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 727907697 1250 727906447 727906457
    0x60f0705121305162904150f03112a0303070c110a05120105060108061c11030f01060f0e0105030d0c0b040f02061309050606030708060d03230307020d02073210 70
    0x2451401003500d11110340c50002a00081c40c0c80d00d8203075220046868000324000303000c6488c01ca9010345009a015151303041c0d80d0401180d40d48603d415070030300c010a1400507150580c80d052550078224000090300d200e0784294a422000700c006407549482c01c10f19031902c0364807294440000c10302d911200940032512402c0300012465040c207d0015261440c000c12886c05903034400c00231900c06048451210340365400c8140303007550142002c00300c0d040400403000d6000300d600342000050082031541310706084038540d402c0303510b19076203550030140c890241c1c448400004090f0b41625010403d500c0e4040d81041c818448a40712899540c00704113107401c6903004081d60085007104200c560600d000d46503000404482c440c5c59440d00d4072001d0901100030b00131038010f40c9042410350406000304079a140a03401c00102005140184a4041c0660f104030b661030f005018010480e45c980f80005a9103059420600c0c0300c08400c0d0f01070b03801c0254909560b80c80308109502107079100ca0350310350303400001d02804030343c2c1d407 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 727908947 1250 727907697 727907729
    0x30d0c09060f0f05030a0926030609151e010c1a010602010f0605090f06011403041b0605031b030a09060203040c050406150207060f03020705010c02060f070512130516 73
    0xb80444280700c400d0000e010f903401d0210740b8564001c0480e503000880c43c0e40000e07284000d082c03040e264880185550000000c042c4050324003034000c8099480b42c01c040b5000d0055558140b04180360760b4000300d01a420892400c902400100e5038003100001c4001031500d0480080307a030f22400401b469815040030304104000c0148115a03082c090720100b01ca88a009000075442e00c00440d4060030020301940c040416034009c2140703a842864006449081a0710080d113074201820078602d0f641400107001e0141c0c042c50703c0050b4031400780c401c1d01e02c103000e090510040d00d030b0744044542d4507500041500a62950700d5000c180010a5403000d9409a405000c003556110708050510003100e807260090649154000c40d4000711950000f80c24050740c065140945440c210321805902a0141c64001000d0703500f080840c210065001a58078840c06040340403c500e602c44040c1500d4510030355500318181581c2400103901320405043c180e2440344100c04560346140450320b144000d0003580c0203145a1380e080c1d10 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 727910197 1250 727908947 727908959
    0x12062d010c291008011a0d0206090603150108131e03050d06080106140d0803011809021305071814010806120f07080c0301050c07061a04050a0b040614030a14030d0c09 73
    0x41ea00c0241103194002c000501d131000e0050100301d0350610047c49049820940d200715141c3e40240d0b8406000034050035207d04248044884490243c0707009070000344200002611201940088603480390090f004004d01401c00e0701c0030f014100c20603000d03418044100020a00840c262040400a00c03403600006459814040a0503000506800181c402d400700c01a120104088100712811036001d86c0c400207440b820604880003420161034040e40c840707007100d46016400c04542000e449405250f45520110140d6460081d5070300d07242c052450f14911f0f84003011502e500401c086d80c1c114200526451000e2181c00707056140c540c4040300764040c2d402c001c3d02000700e603a0030804d458035080b00310000c0c42a407a01c2134501000740180301c0043c20780e40d10f8058111440b120700c5000e0241000240040c4041d00e4068161009403c8001146005a00c1e02400041010081050401c2e003140140070303006461458030b88000f0035100b00040301003400704101001c1080300398070138000260010340701c80002c0c40c6060 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 727911447 1250 727910197 727910221
    0x140f10060806072705031b130501030804090e03072a06030501031a070309021329030a0f0305160f02120f06070f090b12062d010c29 58
    0x7601c001000d500800c1403198041c0c200b00c840c80d4050542d541c01c424808076a00000c50403d00340e01150b09802142e810013a03c010b03070011442402c00650788244184009001401101c81c03d21000c0c1141006200c10f00c00350000d40c0202e41c4184848003120305161054848120141e4008641c1c022201303c1c1006002c01c0c010300075688000c003807500b0200035940c919103800d6902c03e02c99000d00d5040d44020001780c883e03800303075102c4030b00c25401418048204110740c442400038100780c8814405040b40b46414400f4002e140074402c0c50390b4000d070203090b0311800c0380d0310105140400c010450901000348840082807c8900a1001031409081c001511003114018880074000c908401d1280e82c0100d0944000e20034001a6150440180d07e8409054001110f04483e81d1032141c0200c0804d13880000e50b41103804007d042e15008900450f01c101180003506140c1c190b08415440184080059500d10960366000b5580740103d10b0281c1c180c0c0700201c1d18001c18210940d400468512141c8511045c07141702c141e03030 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 727912697 1250 727911447 727911449
    0x90504060e030c0d080601140c1b0a0b090402030c040b03040f02040b011b030c0203011509060f06080907030809031203131209180207080405040203091b100813140f1006 74
    0x358019620300000012004c0d21102c00c1252503041c0f101c214042245a403089003555820802c0d861800e49445802c41c800b600c8094420f842c01c242150410038990516011443c0012030f0222410a031130009880203000180d0001042c0f0741300858140b01c0010380344801030095111318032400380c1d803e4a1007107104000071a54224507070303810072400d14000d20b2140c0a044142d0a1a034060070f090600101e107100090141689901224842d0380140c2c001401c40015046081030390031404818074040e44503a01160810303c1140c00c1c3e40954040101000030500904c0149101c403006070903900c1860301c03040001e8250b4010383d4104a8a06540402820f11081d01c0708403118000a203030014206151a640010015549201c0f00c0115400502c581c00c101244080b03030001c041c09081991a86800001d880d2108198003600e985c5a544010a141c3c503e4094009501d2108076101c0d1403142d02d901040f03d62a1f03080360021034050b41c031341d1342202d0450800c010b61048040c4100c0142030780c1301c050094000380d503e1f03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 727913947 1250 727912697 727912721
    0x2130f020712020616030b2809200403030e40020f0f0a0201021219050603070e0106030c0c0204061e0819060f092a170c09061c0303020703030c020c0a031707080409050406 75
    0x418020381043e00c0cac50340b0850301107c0d0107242900b00009420001014048100035207000c095103024001038011302c0c1c20201c13821403803c490b4220f03c50b030900a00c001307030320900d0700041080c2010002c5040000d032100c050500d01402c0e02c0014105460041d038954441c3e0300b52949070209034031101c0b1101e404864091507a008100f6005008802d140c840e00002c0c208060050b4001e00d5122b80304904170f28850b22040081d103800900a02c402a034610f140401662242810a0745260503030001ca000a0002a10305000c0700422540703008101c1512040c00401c0f4074400600c41940b00d20800000c107103a406c003c10320030a0180214409420f0200c55281400568802c121000d104051819050004185024051030a590400855683c40d0018950345515410204940101c034208000d050b40f40d03025200032403007910304110000c070f0300000340c1e40c5208420741c681c0d020310744400500015000d5240130500d145203c6690b41484110741e0340b0744054226030816002ca690304c2c4100018059907009641c25410 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 727915197 1250 727913947 727913981
    0xf12080124020d080a0213030f050609030a1707030e0f101b09180b03060a0509100504050303070f12020c160b04030f060902130f020712020616030b2809 67
    0x41900001e5183d800c44000300080c4880b00d00003441841503a01118241c1414102c00f0744042d0b107a1030603100078504a5000c0d90907200e0070340003a030b255100204071a15900640c8401c004025a546401c0ba900780081205e42015200d507a100c502003c00c00c031411058100c0c4000d4103d8080b1320044004481410300c10311002c440c0010407640144d04a4942d5003540d01882040208440e00c044583c0601800c1d500c06806114040401c16000075540c0218050321080302510f0f40003c02e220740c0b00c2920740641c5e01506580040000c074602074021121510310f00030f03038140f600c030390070303290710100102d030000c81e28120300e6080824203519842e20410000d0103441043d1041e8102419034031921842d45d85003100800141c0d03202034000c15951444c401039403c000119052040c1442245524080c2d04200e034211590104075030000380f003500100e00c051060303003c0b0584a08501034440100c0c090020640030a411901a01c425243c501031a0030800011071841105400c00c0d107815801d6040b04c84c84e400e010340d054 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 727916447 1250 727915197 727915259
    0x706050a050c1608030418060f0b09120f150a06080307080a0318030908011b08061c050f031b1209010e01180e090d05160605040f120801 60
    0x2904601914200185490415100ca03007110380d0516000d00303801d1910881d8807811000540b02c800100a01c244c0b440151a030a01102c0600e907001a20035600074030007814803040c02440007019034000360121000007800c240b0351280c0741546d181402d10103850440660404040d0420344582c080e074054120721640000c002080c5402400c50700c138050900000c4c00e142c00000c1103901c051194200d958510b43c800380c0e0f080030006915024007651118840c01c602542401520001600c001c1d6506c4144415030b1104000e594a0b0f8007040459600842403000300020b46042c00d000c40e2040004401e450005e200840c0d0ba10140030185142c1e00c03003000d10034003c3d8130a1500c40c0e01200713094141e9400c000c081c2050700401c40214010b036a0b80800e403c0319001058200d40005500c044a8902401403103c0001d03070f10403814003101141d05120f51800d03420380c0c4102100103c00515182d201c0d0380c0c0b1900a03031005100050341c0c0d031840105007003c4500e80016070034000500011030300a003036400c10401c0c020155007030 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 727917697 1250 727916447 727916459
    0xc0c08011b02161502240601120902180a02041d0907230121050907031707020d1202120703030506010905060a120f060b0d1b0c0f06090317070201050f0907 68
    0x1c3c0b586015020a60480154102c441030003048082c80f01a5134044504070000018455140402c00320f66050003d00120408814260301d40f003109020798014002c0c0700010102120f601030400e01401c0301c01555401c00c0300248100e04900d1a10f80c864118100781d0860a05420700c0340b910445800000c1c2107402c0010418032048580ca940e19006003c1c00d002c85103150001d095002885400d080b01c96450a18040200c6844085201d2007641d200e065802d61030303038000810074a640201d10b0000e42200500448801007041c807400200054554030494241d44041d5a405c0040c2e04003070340880100e034940051140035030300982a00d000d49401d45002d4104444554000d101100403120001040d80d18041840c80d00c0040c0c21000181003c02c0030300e955800a00d04c00e000904504c0c5660701142d000042c0c0640c1e0510070202c00d124903400008c80000c49851740c5541009010486044082c44056100c0340c01c400b01ca1139442d4820510790300000b50f545003070303883e403582518003e00548281c6c20142e028008 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 727918947 1250 727917697 727917733
    0x402091c2613080303011809060b15120a0207080a030b010c050303011e080a030507080f09150d05070309200a03020402030901050105100c1703070c0c08011b02 70
    0x520194035090854812241040326001210880c0c00c60591012054039420070291001025081c2d12038000070700c010350700c03d0042d48a0200307004e801a860041003924114104582140c02c0c128045d01c40060f07554511030004513400c011010040c40d0640100c1c078186032483c40002e50b540301c01040000d40c580502650b03a0759041c800c10003240289951400031400c242d2041c400e9107541e0fa4007004480d52561070704e1003442011918450074139030128108002c2042280812402d18a66164407801e08110b010741d41c007030050b000b51092020103001402994160f54400b4003240f40801080c04045da40e5000e480d50b142900d20082c406002d040c14114402d00241042d9031215024805c0040b41504c0c0e04842c001401180295001035803041c004820300a1071001135200d18102e810440b000a03031f05080a0041d00c40356402900039080c0500f0964040d82e040c0d16100031a407104161400e68080c4100e40e5a8840790149504640400c2c4c2d50740c101c0082e082c45008000e024070761140018401501302c1c48000c00 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 727920197 1250 727918947 727918969
    0xf020f030909181b0f01030b03120f1c1b03093810060206090a0c0905061309050f070f080309130e0d020d17010305150711071d0105040209 61
    0x7026070201c40006030740c00c00604002d1140b80e0f8860580d440d180c0210035503016840070041142c0318096100c80c41916600030310403c04144000740160003070341c0e01021505425000085840c46002d42008142c00852580710701c110704140f4818002040452030704608482030100c110369050500d46501600030820314403034860321150300309004084610140001650305c1810340d0600304428401c041c404900d00611016050721001d50850303203241d88807800540e95441e100c80123017419020410038007400340c660308001e601c1040a400501c0c07012455604c101101d0341c10f0070656480d04140d16102c8152818885c202c024800800c0c0300c0034907401d242e0a580c8900c20810010311075a41045102255505904900b40190148080e100c010b4003403a80a91220a40381c20140000d00c2803c550700c0d410780e000e280d107041c2ca03002401060749006078062282c8060001c1d0551043c44000a02c04003200801c015402c0a02032038400c48000c3d003c001e00241203243d041e00024440e42c0140030108081e22041d074a24 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 727921447 1250 727920197 727920199
    0x6040b0709230f03010c0306080f01020f18030a02090103061406090705040621091203110315091f0f210f2301020d050f0a0516050c0106090e0a02010f020f0309 70
    0x30000d0026000408403c440c03030015815500700360065072181d0309544641c00b101d03043d006445080d0f4801040310300700c0c130a840105a0303600d0148400d108108040c040300c0c24440002d01124018042a000201000826030048602c82e407180031096642c03d05e034007080d0308101f00355034503000c50501d0040541540603502910082040441128011942803181c3c0410000300c108100a02800360410003140c1c0e1006d9a80000320b801d00c0f100d000d580c6021000c40348515029040400418080c00412145403001760100c10070440c04240203904180c504040340c02070044000040400303160040c0d24680342c030b440207070001c543e403011840310200741c1c00008030564950100740300300e482407944004480c141541c9880d2050350301c0450590741400141e800617010318034203e0004c038031ba65550300c60420390720100c0d4101d0001c145030209802407030040c005454240980b5002042c49a1911489011039105240181d65a803100110100303550700700c855a401807241c1c0c4080c01885202c0144298ad030f202d2001c0322 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 727922697 1250 727921447 727921499
    0x40308070c110607030c020316061715040e01020901032307050a05130b071104020304021e120a0501090b09030a021b0406090e10051e13140f06040b0709 67
    0x410100842d1401c140990b0200805640d161032090030006c1a4014184040740a4410a0000c80c1ca010000d0026000c46010b640e480080c02140c0015194814014054100325441e80800b840e44d0365490142201c501f0303c00c0001030710703100010001000e0750307011141503a644501c0c2c4c9485100f200d01c100d00c00c0c6e0024850070480c0c0c1d50508000225007a2090114020803003403241404241108018002c009450180042040052510042204a12003610003c0d4000010403118200c5810b641c0c041c184240b00034422540303001c455054904014480340200e4a59664100303660821640f80c05441d04104140300441c1081070000c00a952035204550404c241040d01c80c2e5482c1d55621030304044040c1141030014407541542040890352805048051070f805403d2000152603590b0b03010210580f0341048046040c25110320341000c2c0130804c102d5082e18401c490517042d20323040c0000c014520001040400a101a1504d03051080ca218400740c10765003040b0940c1c0c1c0802410101b0b0742c141c0d003000542d002d8 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 727923947 1250 727922697 727922717
    0x302060d0203130813030302060a023a1104031a07020703060e030915090307052413030b24040c0807050903010f0e07081204061407060f061403100504030807 69
    0x9a402d60440400d0040550078002403010b8441c0041151380c00711b900c640c086940c07035150080700380c0a0380a544400c8001c1c0103035503202030000350b501d2900b0194101158040105281f41c03a4014240e8500071103480c0444400201001000708907841e2030070344811000002d6890800311070003034a80c4003a2201500050b202c501c60b2010080910884510300703401030901490000f03034102c02c080343d08940d10322441784c018040d00150904012010142a505205d0318648a540c03188611041f0380007072510007075052002d000440081d044182c02d6009800140e14605618000c095034030448007074428603809603013042c003040e402d15003000140360003006600f07282d80c85842d2200402d005010000d030110380503040200b500c0c2c20080110358941174400030740580c1ca007030f41052161540703407080f4400d20000a010030400144400010050b0003014450740d4080390742c00700c0403004802e0301d104d908801302200b46115100c500d890208019808080c1c0c03054107010502d020340313010b1702e0034034018010b409004003105 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 727925197 1250 727923947 727923961
    0xc04050d0209090c0d03030603030e0f03060a0c030207060906090c240f170a05090f0f1005190c050904050f070c1101020313121a01080607051e1c0609060302060d0203 73
    0x120030650313150701405a018245942c10018090407091100f40c0100e400c80d0300400245c100111200040d1801400a28075a12030388064401031044c42c1c24002015070900c2401c000941c02d002c0c130a02507000380f00110721800d0508008a080c40e107079009d0a004000240035a030fa9100c04000c1a9801c1b920b400d0084000444510076100148461468214801850100450742c43c150b8015070113003200404880c10010340704040740d40c5d0351f105111059254003203c090542c1e24201d810155000c2540d56502c1c0001d0050703028013007a00d030701d581c2a01c041100451001c1e4a410315101c4c16030b00140c5010310f0074544c2060078001e0200d0041c480c01504070034440d00c052266074020412601035040500300c210b0728950324114081405d40480d004c072014146001c0350300740c0da940006101d0590700e5900190103603444680e41590f8a41c04090312445006440d641c001091a40350064462034804208400044000601c0d2004481c03040d0418084a03241400520158030b5035800d8580428485d8401a40c0b40c903400 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 727926447 1250 727925197 727925203
    0x601062313050916030e030903063111040b060a0e0d0303021b070302040e0102040f0b0a0932011409090a06050301060b190201061505070309050613030302060c04050d020909 76
    0x2d00701a4002c4031050a10504490240c0e04040c1914150390820401c04404e0105480707216008207e6030662010001c20001040102e61007000d070119402c03440920144440580340c103140340407c0e164440d139440a010f60742001c2c000c5100a040440754540341c12240307030340603101043c80d0a14600540e00840b0140415000340d046680803200040312091500da441003450b82d500190008034001c906008650884020500a41c3d05075402d01100c3c58003e0700348201c80c0141e8005201510070030500174400503150710304040c400c1410980c80d041c0304071045031503035040c00701c01c9414086042200d04204c00900c12040f074250ba8507040110340d250000e48400c08100d0141100350440c99040d4640000040d200c44030100800345800c000060360031204a000050f800c035082842940804540001520003051150004000c064401e003031500c401034807140811015080481854400821a5424018503404020481c1e004c41401a2145040d007001d010500c080e071414030080c040c14001c008a013000000b8 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 727927697 1250 727926447 727926449
    0x20f0601060c03111f020705070509040b04170d0f0501031b08121b010f020901170906070311120106080714042904091401050f120d1b0804090204080601062313 70
    0x1040c00355880c242c5c0040e01d4009603c43c603002c8465205024000075641007102d2400d1245401041104507655640ca81c6415480c8038941d165003040c081002002403885071203403c0001072610400030382503055160205600d540c0700390102098140c19000c12403070100203000c000d1851b24240312500c50403000d99541400d1048075403031a29508080c083c0301200350f25406840704540c04d80e1441c10000d48807100740e2500405035420110b9800100c00624014000d4024007076581d0301910a61500398403036111a21100c2c00c0e00b00e100000e40708020b000550b40d2011102e0081c10020038424605071620001c000c0d954005802c4182441a031441600c03004950030655005040c1408141702d50801c451114407000024021584510707a1454920304ea414060706c0c0c0c2044841c418000c04407442c008005842c0040520101c400c0d070419403c848001410520141006100750500941c40e541003421203800c014050700070300700700306080400b21440d845032148000c1f0010800100d0713a031100305844400c90030000b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 727928947 1250 727927697 727927723
    0x22b02040204180518031e090607030c0b0903090a03150204030b1603140c07110301110c01090506070309050604120e04020f1c060b04050f0a05040c020706020f0601060c0311 76
    0x800300d000190290f4556800848a070508000c01c4981c0d603140802e034074444412081c0320680c0c800d01807007028115801a0b2041c8550040c8600d061441c1c00300003d5142c1e00407102140000c0e024403110341008030144069811021210103182418114004075400301110701c0054103400003505850401e00f81941214007a541003484601d0a1801d25130184540d80b28040b414006032806e40e07003103401e00701140800d002c0c90b40b00840924010031a1521620f001801103131302c5c0d1556a84016140c0d900c0307403400904249602c8000810312030110304040342001c0c0010044410304d03040c100d010000420100b1140d5120741d06c24043c01481c40d20fa401183e0a1154401e1117070028800145215005008005483d010288041ca205c240c070740b007981c20054600318461040d90750703401d01090006180580320300c0c02210024080c5c0303101664980000b018bd610001e44000560000b80e01400495814400358442ca400d10f0020300311075250520003041d9041415000d0100403c0d61002c58038900140080292189 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 727930197 1250 727928947 727928951
    0x30302070317092e180c2903061f090611030c0c10030b0913050610050109090209180c030610030b0906010305071b03051803060903070201030b06040e0411010318022b0204 75
    0xa07842e0840000403110315170960f0400b10552001806a40074400c1d4082222141031080c5012000c0240031003603003000d401d003075010350710f160b51040c240c0030014800c130ba003405a0f961f000c6145c036025016207183d00e5a80f82503401d8008100d010302d0f8502c0050170b0002c0343c07015034504008402c8858114024030001d035070142e1014500040c45500d4191100701404540030b081a1401c54880d41494513078407002c1d00c64980402d04079082041032040a41c00760290403006800b40380c02002c180168008644102c52110340d04a0100511800f800c188800039131903507090800304040300c5e0f01d1002031800c0000620450400d030300e0b500080c06031407080311390140000c041608401c9030035840c40d010f044c90304211020900c030345000454051600e40024030710f004008a40140d403401005800440c050100c103114260480d10400000840459151070a4401e900410340003908000c000300043c2510424100c01400c0c4003004c41e21405a943d15111310000f220341ca1045210802c0001012010141c00c80082d522034 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 727931447 1250 727930197 727930211
    0x31707021305011401030b0306070c02010e01020a3503040b01120f0f050604141209040504080c07060314060f2d10030510050121150b07030302070317092e 68
    0x4138842d00d400c200d04000b44c905126510800c020b0542e10042220140c0000c1c1c1c1e010204405540150780020016106106580d5000c2154503160100d01141c9544d1240c2c91003c503400e2251140054042c43e03800c001039400e455400c051f00c4481e80880107000700305112070341c1e800513004c1080c990180004503500c065241d078030804600300140c41c0c00040f18182c030201a0b40c00032201088d40400e2541d0313003406c4081d0342401c00c030b00744080c80010200100100c07030840081094080e000010400e0100034811550007044410800b2082e442c40d4401410702801518103081c00c0b00181d9a0304c1c00601189401c0302c03061400c100301c1d46035107124005058015085a191140c907100c00f54541c01843c4540c0c605550b41c881d083e40c2c0d100444d1282048544010001c1003400d10000c00c54540c1c11111400714600c0b2006030749034a4016014595000d16003c8021075400142d04003090340181007940329074002e561003070103460110150340c3c0341e40e40e002220040807034178041900c082c40030080c07990011000b81010403400c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 727932697 1250 727931447 727931459
    0xc010605130f0e190f060b1c0516230d0615051c0809091510031407080c1c061230020c100c061119050403170702130501 53
    0x202071545120b100c29061200c0c0c00300c4100005490441c80011050710b440b0f000b0140c0341e00312050400041111384540b940e4a90f40c1541d44c80c0d01c0c500d0604c1d24407216031402203562803c00c0c5440c100441c0001800e4801d0b03c00c12600800e58000541d4410107a221802e034002c80000403070718145090700620480c9090400d04412a80c054920240c0b10182c50040c85182b8801c8200d802141510004000d280204221003440c1800308003160000c20940000c0400200e08000070040301c0003c044200203640c80003e10500b04000880c513070003060505000800741406480706600703218085000e900c480702d02010318540310391070340544001d01144048a00800d05071820741c0170350240c50704034120f507480760641c4181c480c203ea0180c501d044941d0000e09000952000344540000f6181104052046030305840000c5000b50240742e0501225502c040e544420348010800010031002501041010500c010b01c001460301c4104242c03168042d16160f120045031002400f01c0c01a10b01a582580c1070000018031 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 727933947 1250 727932697 727932701
    0x6190f050f010503071202031207050a0c0e15040e101a0a080d180b030103120c05030712020d02030705030f09060717190c080a031d0f240c030a020c01060513 69
    0x103943c412001d0740c03815643e8001c15403960404c4c00000e54950045021100e10070300000c0184071661240c130a650440d5182c4d1506807020380c0303e502030f440405000e020456010070a07940907000f00300440302005200505480e169480000c800000e450568440c0c072144c0b14145010340d00d00c0300b40300426003a40c0700d4584040b50f40721403141d2403c80100d030340d040c817a00b04600c5111000059494500c0903d003180c0ca1901c40c0280c03007038000c000c2028003207240390900104000340f0041998900038243c03001c100815400c028944182c10600c00c01f107401c04d03c44040006d20200456501004491b103950702d07024140c00240151041c0b0000401c40304040ea503a02a9040790006046031144009544c036240004800a6a01c006038520040c0004010040104581c0c003075403100102006a40079280c0303190224a00c60316041c030018614640b944440200300b0400140b80303c60041512110749004541002d1154001c1400701610125070942c012800c0340500d00b003544084000c02d00148400024048080301e400 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 727935197 1250 727933947 727933949
    0x51504030204050a0c05180a0b030c0306180702103b10020403030e011d061803010f18030c110307030c05010806040902060f18060a0905120a020306190f050f01 70
    0x1009600384000036040c4c982e5803203841c1c00c2c259652225490010362081c403000ba03100304256192306c90b42c505000700d14000c0342e0380514030a403030031103040c0d0340c90400c002001001f6000c0e100f00c0310040c400100300200194041450b161446000b640841c07031400c000300b6401c0013607140e14241088050090900c1c20b03410203c0807100c5c013079041001c0e0b91240441682c07034001d87c070031404080c01203800002e0710441c95104955000c17860b07010301000c51500b5a144002020340e801001c1c1190140b0098528141c0d5103002e10907880b0b0038a03440c10420150f0380d6007020000030311004101a05001044503000144520302095822294000302980c0d006512071501140546080c00b41e02e0009442000055040c01e0600c50f85651a4004040c80c1c100204203201c00032076031048101800942c2c3d203844c0a04151954000340003c01426213588641509100902140003c07a0040707507002c0d48105d40d81d10150301d010810540189202c82d0400c203a498003807500c2e01804d40144880e00251801d420800c184444214070740c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 727936447 1250 727935197 727935199
    0x1030216080a180e090303042a03050706181a09010c15060905092a03030903030d050402012706081b223201090b0a080132010e01090515040302 63
    0x85480c94070303166132140030ba01c02c03030390a2202d45c4200081008540d0b0306200d0b0f03424002400c01d00303107150107000250b00c41100950017100c2d540d000310400c0c88140e0308121480182090b04000700e42d41841e006500c9000c3c4040040c2c59512800050848440d03403044415009154021014240001980c03020310700070140d511174001018581404038443c98004146802c00c444030481124000e131800c0d4081000c00c1d080706240703038144020480040e441d101880505a040341c80c1c41c0020312460580005000141c5501016140159103010012500200c040c00d00680b00503280050269907034070100c0201440c03030b105d031a885403c041002107081e0035400c007072004550581440350309555180740e50008490040d000080c0a003042c8000c40b2000e6141040c03819005051400888043d40e40090043d5940a0403d0400164001005001c005c10400020405504d0142e01d50300080a8220742c00182c189a01054108580d0b80c5400c84142c0c450b00d00c28000c2e020090003001c0601d14441c226800e988107120413 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 727937697 1250 727936447 727936487
    0xf08120609070e130b041803020f061303050f09060f070f120f0207031b0b0304050d0f0e0d022106090d0e090106020c0607031e0f270501030216080a 65
    0xd202a849a050f100c10104042c15041c055120206990094001000307001d81203641c1e405074060201003200c0b44210b25029402402048074102c02c840d0900030000c2181102e0180c0c503202400080e0300c501150b01340800000d03102c0d120301002000480c00d1246450003a20108003281d00c1003404803007940300c424940b040501c500c103050300d00740c15124208840001005a00540b0b0100045048034105411014100020004168480301c40d40503c0d0010780d41942c580d4003141d50807044c0e50300000402c805003000c1c20700140d22210300c2c0014000500e1441c000340203204045500c2840380355090074105070413210003078489604d050910550394000d8809008009918944125031500701610080d06a4206a014081d8074000e0005c0c8240d81d4085c0703000314101300442d40c80f00103048103090172941043d0305660b42c43d20051035110060501d0440941c10310921440100c080c8600c2e85100103004803182803c015880c4c00d00203078070002e9146a101c01903c3e088001a1000d0455480790075281d4890407400b0f4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 727938947 1250 727937697 727937701
    0x100602010b15030c070c1508060108010608040213020c0c041e0606080402030d030b06190e0f19060e0303160f0209010806040b040f0c030203010c020f010c0e1c0f08120609 75
    0x2c00102c200b85100304140c005040001c039032440300d002e0060800310300502a6038000c9680d0a44002006603032400440014000c1c41800035560340881c03410300400d09450b180416080c650001100c44420541104580b40d001447c1d01c640c8009100307004500c40010b2040245907840000c14260888020b07030070402500c2c1000100305d60307000f114007500554001d0000c01c001003c084003035004010507600d00b075100c00309021412070340704c207081c1e218030744021580c81940d100614424040c02199000466200c1d400c9803800705034000d0700750826012119940b078040002c0109001007819031181c4041d0783c1507141170210210078420003000c3c0b103100e58800e0310012001e80e03903401c3c2292901c1096400030800392074100401c0118002a1161811038000c07100b842c40e5603640d50004c0d084a00c041019005a00100442c05044d5230a11441c20410101d00f0210b0504010034001442928042c1701001d1b00303007968025405000c0900c2562064a9100000554522101006607408036007101c0b0070384101c802c000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 727940197 1250 727938947 727938949
    0x141e01020c0c060c070e01030c03060b060f07030311090a030515070f020d0f03060e16110c180a020f161407180b03010923060a0b1503070302040806100602010b 70
    0x1084460840d18180580b6601002c1000c10403a5800b021000102e4451360202240b0040f04480c003038000c502c24040340003c20b1561600b482a00e100180741c6100359030901581440d40e0003501200d1542da030514000601d50810003200d001800707450000c40d0448118000032040240000714480103c800203055059552440022104100c58640030380044c0c100400f052400b0780aa50348406400090801080441e00d481c3c50510349174044070044100c4a08460780c00074180c1210003143c1031003440c0080d1800700801e40c0803a1510307845a4851001507030080c000703844a00c82e03130b0646214aa502806a5a030607040060b080702c2e40104101b520300841c02032b408080c800c8000b440f01c00f100d000340f096960845501210314010211020260341554994070114001348103013103007103851009201405840e1164402c003a03e0160014441c1006c10301c0c00004201d9550b600303030f1206480d0f046403080d90b502d17551004110041c1c06160f1003076040d8444c410910500d8408681d0000940b55940c0c02002000c80240c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 727941447 1250 727940197 727940201
    0x30a02011802060406050310090903210b0f240406090312020d08070c030c06060803210408040515070c0305100509010b0d23062d040515040f141e01 65
    0x140081d4490f50401c02080700714080c2000c0c1d6440025010b40e2003046599900d0030382076620b1040c003180040c10349109003009030315000e4a08885120a0070801071425810003140031112408483c1d841190050700c100040300500b1803d1100203040a40541c989a8401001d0480c0303031a408111030140480e200c0c09040b901c0000d403490001100d50b1056803545455500344d80c411101501a010001300100710800300320a40620340c02412104011980d40542c1c48140440728404002498050309040a1001003020603003901c0956008440c48242d40c001401c0100c001e200c0e4240007080c1c44d110003c0002445004540c1d080d0344140803a09014540d2002102c608032605098402d42c41002c0c029044003140d07110224007040000180e64000e0107078030b80c2403c1e02d800c01c00c03510f1040041d080341451401ea12915030703100803924955200c1602d420159651500c030314050840302020a00040054148448540b032108e049801c0340109a05034104801c0d907403684201001d0b040c00004104269003401014 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 727942697 1250 727941447 727941491
    0x180402070c05041d0712020117150f01112d300a0f1101021e070c0b030708071209060207080909010e060d03050c071a0c0c010c0b0c0313050609030a0201 67
    0x5403028181c4603084c440703991006c00d42c50400f64100500c0c00c0542661602120a043c05801119022207103071515500700040d005254044a041101c40030360f145100c000051007401d85110203101c0034200706240710701c001d07180038000c5c034031b800303120305101c00d091140c101d40d03c01e00014407508002405512500314040c548683d82c0f5450004182d02a100401032007403460807205e94084001500d484c038200c6102e1508900c4e1032000c4001040011301204200d90190b0103030003070030702550700c070708514000d5400703403009074020000320070321518100c204203410940d4070a01500c1d80c801c000b1904c03880b03181403000c403070340008205038010750310100042401503d1410b03240c0300c0c680041404030090103907941190a83c01109280f65503104055002c11030045001d41640c0a640811200351a510400c00e038501c1c0003c3c29403085e051140941401c07010610701040140d02015001405580b51603100c2c41c6120a4a02c0c000a060b6001d4078080c00720300307036011000b4803013054030780e009000d20000c80a0b929008a0311f = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 727943947 1250 727942697 727942751
    0x50a021602061612031a0d0b0106080403110102120a0b03120306040207032c0a0f0f170a1502040f0e0108030d092d031b0c030206180402070c0504 64
    0x10921400d801864204014480003c0400b460099a00700b980c03001c1d0304076031903040400070a855180d1007000a144101c0f0048001d000c1750304110300380c3c194442060442040c0201c40c10810140000f50038103000300d01c45514502058021542d400c1e01d200030104514050354034070f405a060280c0c01c82103180004a4010290745561040e02c1d548650301044000d41c8461412428002030480d0300c03107216404c800c200b0521142102c4050100300715810002001401c0d040754104030182941403114002d02110307803098840c0e80001c0202042d08800711841c0120120b00140070843e420310064101c071030394025108440c0c1100c1180780054503a124a5580182402480784548c000d00c44114104050b80200d00410300680b005461841c090600487c642c4140d00071030102c540d06045001007640c0302c04c0c0c10b41c41481c20b001844403801c9543c0d500c1c00031a0a484082d10800340440c80c07c40307140c00090221500c00005204640da001c040c600652a420184660352269142442100c0380b06551a1b40c1401022 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 727945197 1250 727943947 727943977
    0x82503021b0f090405030705010e030309070e040602070b16030b0111101104030f0803060a1a0703080a02040b040923060648010c020321090f190501050a02 68
    0x12008000c194a07403a18440950000310000050b006031a0101900d0081303010304042c5503611080d080c42804d449149032118043e90040007001881d12012452100f030310b2040380c050803a501c450504001038000c2040c0500289201400c0c07005907106440c800c001c04080d524180144206980152019840d000d039613807164001c050b100c03c001d482c41d440070386900c0c10b03621124240b60300d94641d0228240c07010011654003200000b4010300c1d15086403841c4c01046c03040c04205030038280a00000b00c0d0700075160004c0c2880030240118190b0380e09030b010794001c1e0094207000f1b6100c1e40c0d41c043d080060014420350701d0b10550307120b512220034940c20000600c100000342c14a85840c614131102c4800d07110a0a01c52080790240c0d12802a00d2190090006408241e40c041e00303403046611389035400c41c0c45506100081d940304100e0301444480c11180c000701130f26a00303800107950b41d441403000c1c1022911440c50340e241c004d100110304c0400c1c42c110180c28041c09413000b0082d5980d0640740c032089205071810104140 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 727946447 1250 727945197 727945213
    0x30b03060105011e140c030c10050c040b0403060207061d07050109140622030b041a0702010501060f03090309050909011d070812030c1215240304020d020a030f08250302 74
    0x130303004405a100c0c000300c0b800b203a46449012011581035411400d20318089800a032044c61600ca500d005641d0070039050080c0030319007441c02d001600d0138440c601c8002c2400303802040c50000c3c0601c943c40440c0850000400c014600403480310691200c006001e454045007203007401152100c00401d2003852080050105d5160100c08800d044100f90380040a10240040c91b4010000400320709503280558840d01903085140501000c0300107455004001b0f100710380c544401000349945c4030112600a4443c1e0600080c020754905089070380100d56000320717800c0b00e0010203120780500305500c9411710344147c280f8107010404050510b912441c2c02c3c410062140d0100310014003d9825400440d0002015610980343c0451056500d4020300c044401100a040c8680480400e0802e50b004404031800c00b04c1141032058440d41050b2180000323000a801071040740c0b401001c5441c5c0700b440101554000380d1401c002da90700e10300080c6542c0314001c2c0240c920032400400d9401d8040300d424400032a4550090318141c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 727947697 1250 727946447 727946507
    0x30d0512071b08040e0a0e060402090402191d04020103060501081521060403090f060504030b0411010504080a1b06080c030a0c05040513140c030910050415020a030b0306010501 77
    0x3240403503000e001000c0301c4400d10000503c07181d0041004110000b90402140703024408913048443c40b400303c0429170002c00820006aa8150a1507407007981110300503114540011a802d001266401112081e2201150340d019940b01142c6603105a100740c0e03041c007015880c0d0004540074007040e42c25580d12a05d071034046840d440c1500b0009299070054400c507159112000c0c0d0540741040a6906a0101e41d00d2101404010702e0b42030f8041c05005203040051a1900d5507031026581d51009002504070032408140071003981c400c400b203d00070b04c094003c803200c82002c3c3c1407030700305041d50300c005008030105220002009401440382d00d200d080341c004c2a900b507998181c3d07010090405100c0702020041c0410010490340d480e010f400c14944920b0b540092101c21005800702e0303144014016098080050040200c4c1c241c0c0044c101003201c00c41e4070007103642d4640f0714000f030403141d49040060722540046074880d2010340c998045010141c1c100e0071143c1d0b503680c03039005441d80001804005400134100c0300c100341d5 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 727948947 1250 727947697 727947707
    0x30a12050405010b150304030f0201050903090103020c0a17040927110d08040902070b180d0f03060e01140108070314060d080910111c0f0807030e070e0105030d051207 73
    0x1025009000105000d5840000244089485c2d6160410003002000348014980d0112010b0740c2120b290000b0007503800c040045558034020781e00700604040d00020304000410003488000c008a03480090080301c000308561060640c0c0107801103030012482c013000b030415030f130f980717904031064cd62030401c9018800300e6501d800c00c00d8852404181c1e08602d55003000000a0640750081005203559030700162121801e151200080201a00320814200c00022240e00c119002c01c00d070441e01403608001e42a03450101046e0050070460b480f00e81c03881c044c3c100014150010a107241ca2040e000d0381e030b0464070782d161030042e03003107520340f01d901d0f80320329200303000608a42406401c0a034054081c2d003101e07041080c000b000035261606000c907040042c011807407403440f032074082014001505511142111400c0100c00080004440134031000400403554041800b0070301aa01007003450300107100ba2502d060320b071034180002c64420b00c50306d03001c0d01c03640d070228041c544543c0035140031005546803443d082d1101038040315 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 727950197 1250 727948947 727948951
    0xd0c090c121a041a0d12020d11061f080304030303020a03060617010b13050603100302040516050a0f09090f05070206010902130b0c1203090105040302060106170601111011040e09030a1205 82
    0xf030040c4040307100d40280c0d900c41c01c40c0100716100d01c0009100c621b0301d130300090400c50440940c0c0700b880408500c07070001180115103190b1000307052003807411342c0d40340000018045000b603101071700c103000020f40030040c143e050300144060700c0700da01c007800116a1444212114100001c0c00303014000d0502c01840400b609400034030300002400d001c821015201c01c00110660301c180c4018603040c4100d0410811420b050107800c0c0d00c907840400760015031610900190181c0b042e00240820403015981c1e0003011406546043c000c2d00e0400020400020003502800040c8001e84a11000d44100300001464000078022a40042171000302d035400549040314075042034204019800840c0950b0101c000c2e1b0420480c0034601c1000480c002081c0c500701400d003e420560b041ccc02201c2040400c240329031101c601c4040f660b03001842803034540d03104d05c80c4d503141c1810003100c60b0003422842d04000c41c1344180360680f409002038643c7c0160420440e26460342c419901d1082001c00c4002c160b03201003c040d0303a0b14590200e9 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 727951447 1250 727950197 727950221
    0x2040c030204080106060504080106060905010f080a18050f010501050909070308131208031009050c040e090a080a1d1c03080408070506040c140328020d0c090c121a04 73
    0x94205034950f6442c5081d6400741c0c01c072100007400400c08000d16a802d00402000f48803070f080501b602030070440002c0030f0802e0300314490b061002e0b10010524452855010040c50840340130800c1d903203080340c07410507101d080303046580380036608003000803034940342c54450030b8000c010700700003070103501d00e1581c40c2c604039004110301c40005294000d0001c0c542e050a00000e50180c8100380d0b00d0b40d06d00e4459a800e41b104890b4104401b001d20305801c101c1c010504c0350855041e01d841c5210f01c3e0072a990305039044d24066030314000404841012658501250700102d4041004020030b4482403065602428002102d807041080f905240c2c5021207040401c0c0a511025081030042c0d01c00c1d4a0846a600c61914002c0256000c5403c0c01d15203808000000203041c1002d00c001d0124064840c80c135107840c034401803e2080b00365111407440c03041207034110342d10912900c1da415808000300440a990300d6405d0700402400000c64046000c4800d03240034500759100d00d581050720b000d08200c0c560804011310004003031900f141 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 727952697 1250 727951447 727951451
    0x181009080c0601060504050306010b1e0711042c06090a08161208311e020d0f0b090d05040605030a111602010e030a1112160602101406030a02040c03 65
    0x21001c01d00140806800b81c4440d843e03ca603510320701030525103070210580c003030f45001e0400c0c0a00c0c500c500c4d0041c0e00501700d1402000a03601c036041410036000300e404040c0050b5000e032900c0c5000c081c012a0301c84a20212100202010707881d130321910390603100c1c02c4c120ba290415400000a070000280703404040c040343d9044130000c0b0680c1000c3e544241201c400d055140300031601400030024043c85d84c410f010840000b07280e48000e402c039040400004041c0500380207080b000988144100001c0c00e0070113a100a07001407000240e0316107030030729201a600c220700590701c0c0c01e0340d0800198000000602c0700da03440200c2d0740e140d262034503121044503590409031111043c40d446520300681240d400d000303400b103880b640c0340e10b9503049100c1c40050007020060031a203000342c0100e07041c08081045039141c1c603080002a280842c010305400099428950150a14040b01d2000c400216405500058825540700c400104010f00c6c1d0440c4c0c40361049640448000740d01d98813108500b801410903030841c1400c44414280 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 727953947 1250 727952697 727952707
    0x22140f032515080a050703020901210b040f050f0105031f0b0a030c0605120901061206020708040e04050a0b090303042d0507140a05090115230f0304020918100908 71
    0x10002d5501e04094042c000180b005050090340070592142e00d4120420b4101145403811910020307000005804101480d07040c03540280005100039040742a04100041007005000b035840070308001001c3c15038080501101c004000f1a00d800c00003500040c803118581c801d00480b41c8920260040c00b00708076000e42000da40140040003030a4001510007a100d540c680546500d5010305c04440880001d009482c10380c10220104882348119a1324154190081c10140c0d650b08141071100d02446294045000d01d9500e80401003030000100cae138a1307141e0340304035100906620741d1303807909540f40802d0741d014000c21000b0054440951807808c54004a050f002c0480e0380a81079500c81a081a03080d50010030002425002401140707131200010300502400c0725140560350504404540c1422480016011300c401800040d51200602c1a1400c1003005a00700e503a5a842c0510a49260380040d40c080740a4803003040400c0d00342881a10840e003110402004004008180300f800001e4005840c00307682107182000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 727955197 1250 727953947 727953959
    0x51506070507050d080d510303020607230301050d02040b1003150e0f0c09120a11040609140a2309070509090d0806010c0822140f0325 59
    0x8016501c06000f01c03001612406c02c0c180139401d80303600042c0e2040b8101600c2c0e00d807550020398007648803481036243d00c01d401c00c89030320035280f07495600c00c80401c00110311a1002040660000706184100f0f500d5503181d8140d510f80c2200f04044e4141d400074240301d1020f10040c010f5041075403181046500091000c6281d0902c00089517030304090f8035210300001d48480c1d41e0280c86c170b8400e0f8114028114118400008e2400380310020300000040c04103407102c0400108000180c2d235000358161250915410f8801d40c0003540b5084880314030800c40c140c01282840000a143c6041e481050040c55507004080e0036503564804420041003042d14900c1c1c50605091031078075100c517030400e0b21722808900b00203100c000e00748000c0040100c3e0041c541c041c20b50101c0301c5000c0003a03102c1586a040f90083c00c0c50400d4038540d14000e0b260307000e1081030601f4000241210f072582c02403140c028003111840c1c0081e0681200000038400901940c0341c819406502240801c3c042072a40c800410b4061125841079401d942c8441b = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 727956447 1250 727955197 727955209
    0xc090f040b09090f0f0c030c0d1112010203010f0b25020112020403061a03010e0a080a1707080a2414060d110705190f150e030408010213050405150607050705 69
    0x10b21401a5681302d40810121801c0400450b1401c100704401415140b0004000941e02c00d00b130000d41d4020301c143c03c58602080f401e010160000c0320002e2090100315140151103001b5042403040c14486030309404002015002a42200e400c0c448055078224a2244a689034601c5d090a072000c0341080024895008a02d04510190020714030035000030400e07011001c0514144242004114440c1c0d00d000410b400c0c151001a0000d100d903071018050ba00c0f6226000c0544d01e1000d0100d004008050307074000c1114003544000035078800d502192042000c0c03c01819040c0c06015510030304a50200d2030101406044071018110300d04410042001d86042e218445450130344000d440c56034215400416a0b0707003006428402c84050b180007035401015401251134105000c05280d801610f01509140c440c0700c0c03024243c1083d04440150402c582e51950364840703160003907000c4516161450103001011880c0d14190050500234152100c40c225140072000821200da805808210340038450300300d00041ca51503403 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 727957697 1250 727956447 727956451
    0x1c0207140105070c290a2d090c090e0c0d05010209031504030206071d0112060305031603110f03030c0315090108030a030f0203010f06030c110d2105060904060c0201060305060a061d0c090f040b09 85
    0x9940042405d08c01480d061140680c0d64020f691020305240c034410301e40b08001200c03281500708890104407240182820b41c024843c0b1014160140145511441d0002190000341e0080e4800d40c01c45105d80d8480c1030469038240c0501600c0240b141ca4000e4001c40c0d84542c662800c02241780800040b030703a55035568030385954440410200700560000f0b4843c185904109004a4030307005002405142c0108020f494503484002c00d90040910040045078441103601c4030004080c40180c00b8545c1561102842030780d941001030380c0c1000a00b0007001c8040c001850082d0703412507070511740328854a070902c0400e5002c1c200c0303049000d0800007200c040c1040c18004106683c0038043e15110000c1300c03d6032101c410359140c25030000c005100e0400d014040e440d19407000043e80250032450004080c09440c00482c0035040c260300190640c4144014850b000d02030340d200d8811180c0204a120020400f10520383e001c0c0004c503000f1a900905009603034450800b0403a0600c2280700900009090400f000080c40c45902 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 727958947 1250 727957697 727957781
    0x7090906031101090602071202100318061b03021206060a0203070507090c020d0908060f090c040c08060406050a0e0c0d020417160503031c0207140105070c290a 70
    0x88a0b10031091542c101e0fa03000c0161140b840135240080c10f082408166602040000380512003134082420094421342c420705c0452035003000515010150304050000c2d01030740c2c001d40c000e2105e1405001c2c24601a100326003d50700c0211004643e5a90081000210b401a4402000354042046180c001034401e011050103003294170000a01c1114500c0c00a2502035002c59840520008100611415100150281c0d2241401012250903a00c50744414107145041290070380213400e2548001c2c2c099000881d052017200c00784c1d0100403151b80d40c1d0411001180a1048451a8ac0b0f02000f20700b035583c40c513006007180480d031000545010b81da1140d4608042d10510750520075007240004450706140900f8050050204070b0046041c0748158440b101c00b05041d414001e40c1c1540041c0c0102085541003171445600d8000c0c00800c11850034150280c003a0503501002c0340c00143e40030b402c2c1d0411070035890941c0210441b0300954066690385802030000c0601da8401e04040c21031f0007107007203118102c140781c140981d8 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 727960197 1250 727958947 727958963
    0x2070c03030f020706050427110f09041a180a14131a070504060e0f031e1501080604080c0f0a06020c0c0f030c01082706101d0604050709090603 63
    0xc1c0b01802802e002c40c0d80c002d9803c01c10100010403480e1f031043c445c03c001e0488550007042c41c1060380111001044051480c0f44400000700384a50040000e8019205444050b01c00340200016102b01c0000780104440a80d40b1907d1441d45400c1260041011580252800303c0008c564240191564035040e08682180c00d003101c44e41a9000c2010820303801060140b0308411407081e08292001500368092801860200b002c0070040322469078400d8030f0035440038805000c2e0f80d041058070701045400307030034007614404134403905000385003156000706001d049a042d10068501e5413119038848a403984000ba000202d40314080c10704486103000e010050015100d4000166984c0c0e004212608000c4083c80207885405000d50581c3d90342c5000c6469800c900003481c04e10940e9655425805006031118a00c110010144041201000300029450f0088401c0071140f0700655480e1441ea081c1c0440080308155070b178a003008640c09080c05d401003904001c05040070104241c440032035400f03e82d502e90064802d40 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 727961447 1250 727960197 727960217
    0x10e1807031203140708040b07020106090501092a090302040908070204020309100506010f091517190b0f0d0b1012050703111f180b0d05060a05040e190602070c0303 72
    0x20b40c040c42a11038084e1000580700d050b00d40020054a8404014009002a054000041e0182d4801c2d4005e0300503100148013003095584801c1164000c0c450030068003440b00e01e64070580442c880402c000c0d030255080b0350710036180905540c2031001500b03000c4000c07613603541c003448094016550340c00a184140072a000401105814180c03041c01d0ba01e015080c20f040c00388041d827014038150302c034200b4005d40e9106410300e103501d014040203d50414540d60286240380b404d03c14069411610b0f10000c4980034000414001c0030099020005105c1d0300c1240e80c2d40c0444940c0e040c4000a0328500d000f540b00c240c0d200300d00230309546c8814100030700f50052401ca80765008104140100840000300e4011414241c4102066019280c40c045030513000000c2c0700d0501101d00961103410350304010700e20140010300c0400340c031606c0b200b280c034000c1c0c4415584a0301c940340403103022406041c0b0748034014070030400d02c00805450010000058170201444000d5640c640c0070000c0b070000c00d82c00404c82004522907624840f4078 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 727962697 1250 727961447 727961483
    0xd02070507182a09051504120305030906010e060604150921020a090908030601110c130e010c0e0f0d031704050303070207080109080904050c0903011401060f0c0209010e180703 77
    0x10050074010711044071641c058a0350f20319403000c42c20055403c00c0d608180f0961804111001c41d00650b4800940b07900710341282c200f00b50740314028602801a91086a0040c0d8071841440030841c001c864407600004207000400041080c1400c4400004490800c0781a1030344030102c15448040408006060030b0300070341040118240820042c0052010010412250031320355240340880c44040e141504010401c5000018154144012143d00304000c4c04050440b03001c0202601814014800c89400d5103099842c260b1540146403c41c5580300003044d0300c405090580030401031010300d51098042140031809403480409400400f0b0045005000468403460142c6c40245007244079001555603905005044002030800e40c142c42c96030000b1180801c09a66218000c4158011101c00b5981503092032903070a4011520218207045e1800b81d59024006c0414a105031100160303043c1c003d4000840b500100b000000300701106800c90100019440c0014401d003840e803401109070030503030740d03041403c0748a019 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 727963947 1250 727962697 727962731
    0x20d140c070801380909120412150b0a0611190609060e0321060d080d050402120d0504031b080a030201051501030612060504021f0e1002120d0207050718 67
    0xd0402c80104280702c21940c05150a0f95841c0d410105000c1c0411710701088004105120084625141c502d03241d07112591403aa914030105951340907202600d440e81060031000c0f00740140540910060320b8000f80320710300f03041240e003800c80d000d1389812409420700c3c0ca1a4880e0400c00c8842845c058800803d0003c2c4d9400c203182101c030003407240c00c2c0c039510400c020101b00300d810400152941c07040d440700906a031581c0c04900c100c40d600600400e4404000b0b1261090310040e804280640e0003562000c00300c0c9450014947d55005900002011170b10070b0104100160002c2d003a03102180403603810310340180ea04c007140c5241040150341100035075103030000c00c0016523040c219581280f81c24603040c0030356450400c0049400c9030b0520060300080c1c840d03001070309548035600d40560110504600400300040c3c010000c00708008100c5c4540328a4620071400c10715480090020031140200d45814903140400d00e187c0e0080d40075010460385800fa08400041180d1910300341c0e8040c0084500128003c8401c40c62668 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 727965197 1250 727963947 727963991
    0xd050f150f070c0f02271501022a092401050306011b0c03080f04092003060d030903020907030203010620030a03091b0305010905100606020d140c070801 67
    0x80d0098903041002000c0c12003506071600b158450920000c621490b060070700c42d01c25044006500015004004040815140e00200703802c100d4407440002c503201c0c19042240030301c4074005940140e005508501c542d0407440c0744107001300c0c3c01422207030501400c1008540700d81c13030803a8617401e4900c242036000c0340c1d030005141ca030340a0442481e29514501e060000a0001c2140700c0580010421503099981040b412000751000365402002058541602c03020305140c580c002c1c0070343d444181c285542c014a07000001d220b151001074021060741550741c0c00080c010504940300040e0104000c012000001d80c81e03060045000c0d10040ea400340c2d41e0740c141080a0444003001003650000b9084c0848101c00740008002d541c11a0342a1502003419401c2c2e08102d14200e540580f1205041e0942100104100e015480420124401c0042c1c9401d01118081001120035502c224030143c1c200701c151104462060120007010800040d24030305040d00000c90b030b8946222604481c1d0b90740e640e0801108048031075100d0755 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 727966447 1250 727965197 727965223
    0x703060c050703120506030a080715050a0f06090207023312070818120d0209030304090501090c05120103060b0103021624090503341505130f1106090d050f 68
    0x200150806d207011030740d00c0c03404200252007008003182c0c00003000717a0300b11398806050176004140440d060100c9400010010f181741103201c81e1501c0c100140f8050ba138000d80c1c96254004007030036006050104820030301c82100420600c640d03c0044032171740000104c1c000d041c240f0444070740f529262520359005440c03044040c00071009207005030b915600015000079002e012505991640c0d441c0d51908001c00041d0089507810795046c0008980451144d85e20307404281204c24003070f0280648410b00b41306803102d110341d9800c800c601c1580801407020400719002190505418900145014103102c10200d0550419504a40c400071107004010500d126085040303a01405072020000c02c4800c0d41c546542c1d00c101420044c0088000305038800105d00c2c0e06c2c02441c3c6580d00c0d0010800c030482494015813003200c200015044500c1e06000ca07400c0400441440849640105180708500303807901e90389099031410701c00c994000c50030801005e65468135039074180c1c480e115600404400c10015411400e00d00600641 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 727967697 1250 727966447 727966451
    0x1917070e1e06190207080a0308090d05030c04140a0902030112050f030f16110d03180f050d03080402041b02030406030f09170c0f0706050903100e1b030703060c05070312 74
    0x880642d66070603003202c000d100c4902c0035100a6450050582c00c294140d4400485801106248401c0c940c0080090380305032099000e940c2001400101030f1030360301042c1d490140d0300302c040c001070090002949924023402d000a022036000c60362002144203a90003604070b40102798040d426201049000c01a000301c22501401a600b00303500900c8130202c03805650b51510008080c05003040512842c5a00c240c8240409803d44200c0344032402c0140c298854090704010501200000043c00c0d0038200c000750a5420051204452250301d48045a900c0c00180003681d0003641d541407910601c64910030310040300607a030040e5445a01d0401c001d02160813501c1c80c2078040d03040950200028402c0708681d141101050021502c8880180b141482c04601d19981d0f0381d00c0c400d10402007810780d0400003501e4154001c4040380c0f281d85041014009940c000c000c4584070307600c121000c40d000004000040340080b4060304071084260b9070f0302d9802c1910009502c40c0041400041d001c4140741e400617207028480030040d41 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 727968947 1250 727967697 727967749
    0x80405070506190f080f06040b0d060509071505040302010206071d0d050d030609090803040212151f090e1e03070605241005041401090806090f070603111917070e 71
    0x41060380d0400201f03080d1007030340c0d141042c09041d030354540c90861240c1c021108026900d44034030138640c1c0315524042e07030031405400020001040e00c250129010b41e54103034003402041e00d441c101541c2204191204001281da003100c0c0c1d4843d52a03a00440c040c007030052000f040340040b2002d00ac2d0484071590405d486450804a5120100d40484226a04940c1c151032440c0d03c031046600c43c908000104031002c045071512410300c5003a490725980c030355040d800400301120107599a41c2d00b00880b11038407170200e0b150b0080189503c000c4010400190000000c106807858294966a0700c81110030845440d0300d010250451062901c900c0000244e51800a0720045005010141c0152041c003c0b07100e4180c20000400b180101a40b0840440c00104901c40440e2000d0610003500354858410005100d1141300310400050b07003501c04d004544800000c40040c0e032401d843c1c000c24074002540e89402d0000d1018013414001c81200d50015980702d051140d5a264403504200100031007241c41401211255032200d038 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 727970197 1250 727968947 727968961
    0x6080304150e1f080a0903121e06090f0e070b0717130b0c100b180408040317030405070b0901050f070f080c0d17010e040201080405070506190f08 64
    0x800c80342607503240c1012034000c60400300200d82c00c4040901a0f42c101c0240500030800e09a408048040504140c555010607528500b14108640710034001400055028403d062010b05c80c0c1c2c040680500c070520081070b41800f002c662410303124582c0c4072110056598040321180826407054040c444a44006040b41602d0060344410b280150000501500340680d2401000c1d0307400d408448101388684800c0c0c1d081c550780e10b1810100c2e041900d034041640102810282d01c01004d10900f042080010283c40c510803e880e0b4403452000e00802c111a190802c020201c04680202c4013010b09a50841c0d5403941c031318207460441c1c10700c4050f0b400340350074280511504559070b0304801551201482c091103d0385416150400c20503164030002c0140030500d0003d0b10004903000440d4159000b00151140802c10200149580216200b403146200200c8003002090040d0301c5100c0c140e070007038019000c6494075a101c000182d81c540c400481410031014450400e04c01580108103240c24078020b0038a40213074640030b0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 727971447 1250 727970197 727970203
    0x31303080c090612070e030d0e101707030e0a02060d1509150e040819050301050418050c040203090f071401091401020a11011814030106080304060507030c020f270a0608 74
    0x3d0144c140c448411130008074001d01c03410004111490007021602c0030071220202500310700c0070b242e8003030107183d0b543c4601e61668043c918003000f4003c0c03280b2000d40380e80c44460480080000700001000e50103115114000750342c5d410040d110030f13241035500003400e26502907d0059541d03550721502166080115055452550143d0441100d81c41110744805580f94134140300c00d072040c0108051521845103013905216400800386041c1c0300c1c05e036000c20912255400546e0120315a44004105500c05004848541480d401030368008100d501110346d10f1810b15082401d00e072040d00500d10414110030009001d40e48840d1030700c001c08085c81d01981140d0007100003500d9100120002e0070255442c0003440c120f03480b81306401c0a06d00b945003101040c1b5107410075503d54900010081d4031a40c00c00e0340100d0305607804000c07501150380d0740d1030301450b081c0d10780c0d02074500c1e80002100366807020619041c01c040d503c03801900c007201328580803080711044c4413000040e840304020704601012403511200f44480c00c000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 727972697 1250 727971447 727971457
    0x2040509180c0d240b0a06030e0604020607030c081207020c0108010608161206060216050402030f071103040509010801090b0a0606200708030c0709050903030f0a09020114031303080c0906 82
    0x2914809211412421300c5107801c18103500c041980321940340d0728000a50f05030311842189900320b800601e5184c0c0c0d01001c8065841d130040200f80d980141e004a001031824000a103844e0b40701c1c2c10941c20024440c0c46903900d07031b00a0260900b50700d14100c100454903038144102400300304c00b400d01d00125410820000d01c6104001c010300005170511031801800307409140d009000385814881801501d4460000075150036070b084080c010b2480c140004162440d00c0d0003528482c140c0008940380d56a1210f004460040300d500c0c020311203000800000c41c00d071302c4a507402030103080c00400200f41a142844d01d14801c600c020180200c07545482010b00910b03500060311180c8040d048d041c0c240e04c07000e00e00240c1c01c140c860341c00032685100015422543e010f02144010403211380110400080d81d8107401c454592004844240c64a076940d0002241903040d80e02c02c010322401894401c1d000512814034102e01c0d8800d0340e482111200d0202480109039000030100da00440c0306d480b003800c1520482c0450814090 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 727973947 1250 727972697 727972699
    0x3151b050304150213081e0312070512040c0302090a0e060612240403080907180e0319090f14060a0318050d030f060e190b0d02060c0102040509180c 65
    0x7010400f80714100c0004190501d030903a045654125079480b0110383e0700103100d0604107024004c0c01e005980c2441c581f0000d200100c00c040c500e0489800e080705040d0b5001810b041c288141840201c2500d01e50307081003885240302d402c83ca91400d040d0300400150b034000801c1441c1c1c01c2e06282210100c5640860081d4200006540d01c103012400d41c200c00d82000d085c0301c80c00300401d8004a290004051200303800f40118000d8903655902c0d2588040c494a80110340540d408110729544d610800d2007095001108000d90182980d0600f0b950304a1280014100c0c2c0120340000d03800035081c4401039514030740d003004190018401015205e00c80110348070f405203505550030300d617541003030031041400c2d40360405a140d4440180c4801d200040c4018005040580502c20320614001020904216014040d4050382c4415144132480c2e503808401c0303010b40a849480d503041421101c03440016194640030381a00030311400050780740c40c145018010120f2008180d444020401c0982e024021804101c00c042d20340 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 727975197 1250 727973947 727973957
    0xc09080d1d010903151b0c0b0103030509120f1011040e0c0f070f060c0f111f0b060f1b0604020a030f030e090a02090306280f0e010608030403151b 64
    0x44100c0068840f268a40e0020340241c50801075502c000c489a8000d5107403502d00c1901241405131480103c0742c20b014004000c0600c1503900050003c2402200586866040203101e54105e401c014032076810640d440d40600e040da0701c40302d40c01c0718910060241c15205103003690030606041ca000c44200707086001404400e802d003800102e002c0f21288100840d1131240d04440a031915002c1890104002c11100d40c01d9000603158202c803104007881a240e0045261036400103224001210350031060704c4000848044034603965010007000c60700ca0f90050030440c1d501c0d8495940341d8800f05150110901c09404190311608031004001c01a81c50244403c1600c1e0000d81d00d1195084524003500c5481c403812a0950088800d0200640c8d0070b0b4039002400c984405409039810380d00c6042e8884444050a801d105160340322542d101001c8074103034015448016400c20220301405d038890401e084031019041018540c0000506100b03000d10241840307030014401e1010404000030541140950700440c251204004d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 727976447 1250 727975197 727975247
    0xa0e0906220519060b0d051006050334050702190b031902070602030a020d0f06060e041a091006080c0403050a0f0221070f05060f04092d0c09080d 64
    0x600400b00c0f00d0004920007004007a0311040e2820700742d080203160841d001c2c1801d000600004815144504440054907141d0441c1c440c446a81045034803080300004010030807522696003c00008040c1001c01c603074485640e2a1207500500003240380240d05480c250f000d80404003c0420f0b50821242e00084141032088240d9120310040e0281c410b02001607d1680040103028001c8110750051181007000c03441080001301d003c007040142d800605c140700c042000031303603194282d080030380092203000020703010b0800c001e20100c005003521000b540d40c8581160f0b202c80a22038243c10800a40d0042442c50950382040d10f50b5544c01e4ad01d0b00e10f084005d1401c0420740c07464045460341200c0e104c08402c61740510b00020024030145540f4012031242c08280c00704480001442d04001d411101c018078260a01480c003030408031303e44082c0c402c1c150505c0c1d000060000c1e5010602c801ca00c41407907072400ca40301003501c0440400080c2041d81030b0308042c8107500f10683e00505144c001d280c03550803015a030200f180f01 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 727977697 1250 727976447 727976461
    0x2004051f1205102d14130f0e06060a15050a09090f09050d03020901080f040507050d06020c120a210e01060801060e010f0506030103060905120a0e09062205 68
    0x6045000040307140070341881e0500c65440e10307400681c0150b440d01c42d0504104140c900c6101610b0b0107120140c2c041160021043c000101201e00c0300700f8016010f0481c13600c04c0d50161507501158100c1c00040481c0769506580c041540003405480c1d00a42d040310700a01c05802c0c60000092441e10b0600e107001d1200020b80c98000c40d00400b1507031f00514500d04100301c0d00306421012400fa02c4441c030115028081d402c59800382601038429a6140841a0745029041d6610240740101c00d401a10607152031292110000e01d941d91400b00314211482104d0150b2280c04050b0403170328080c01c0100c020803107403051291f01e0b406d50340944140c001803038040c842c0850808240e04007004040400124804c0e508200300829035540c150002d400725140c05001c555503a9980b112030a00b115075020780d80d80004100010030100b0020382240396214003c0041e0ba12800081c0c920218542c480c08584011803800c52184003240307890f0002c15401002a190309144800052211041842c950703490045255030304089125 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 727978947 1250 727977697 727977707
    0x30108030307122a0201050703020c0c04090f06240806040b06010507060608032a0f1905120417011404030801091a150c0d140f0d0f060303032004051f 66
    0x90038a451010440e000c1c909144030181d0181301c10241d002d582400301141c01c0031f1080c800c6030030540d11540a41700c03a4185104000103040e448005554813105200703e200401e1492044134660340c980841e00740c00d00000020360081c900181c3c4038020b280c0240c1c0800c000328142c1da0405034070800c2407070f059640f28a289003210081500c0e400540b464070000c030301034007800f107415540e40b90b003000d101c015007440d44801101030303643c160345004000135001010282c0074081c483c0000c6114510503000d4480b10030300244e00030071980069000c03084400d8900c20170310f0382d01030070320440d45419180c401d80442c2c1e00e800d440142890034103101ea0f152081d5a0442480151146100342a802130014000e0007120380845103546a90440e080442960281c0740d08482000d000d44100d10107107003802901800c10000041c56241c58211303011003180b4075250042190311850b41d12858010b0751094500283c2081c0010720560031030003080000c480c03084d0030041031001c0e9413050000041005220040500d0100d1010200e0b4 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 727980197 1250 727978947 727978961
    0x3040b0415060608060f0406031101081b0f040509070e01090312030f0f050a0b010801080a111f020106031707080d1107020a030b06130c050d05062b020a090203010803030712 76
    0x2070440c1c60140042100f561103101603009140488542c0d40000e595400c2000b11000c2c3d101c000c11a041720104541c1650007800050342c8981e07213040401101c006c2003015070782684412a83c48800d50001800c2c0100c0c580314016580020b00351a1603044e066690303001800d80081400040d00f81d40c0c6829400200e81d1194100f4840400000818042d06c030a10a415000e0303c403d803208948079007010007000070340d40f141d08124101e0781c60200400e042d45040d00c45452514503c0c0c00e040c0c0008086019031400d501d184810380c000308036680005811403541c144080c503071001060481e040c140400890010410305025202000180d4400107020313001c02c0c0101c001407143e44802900b210100c2000424000b81d05c0300c4511821082d141414403003540d522001c11600340141d9100031a105000501042202e6800f040e440301c2c0150a0094400500b003071a05d00b1120020a807200c000d107600c1078011030901c0392201000300f8400c6410341c00c0d54100b5409a0701c1c1c0c00014020000c004464050300e11041250300890 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 727981447 1250 727980197 727980233
    0x50d1d0a031e0c0b040b04110913031205100e0c2a0c0301020f03150102250501030f0209101b0f080c0609150115121406030d0306050603040b04 63
    0x240100310349107400340100c004020400c0c501d50241595110883c00f074030440207065030142e0782e5100381e5159580c041601ca4094001e440300d40003024005215100e40701c0440c00b07060003090908415180c1c1ca401007030701c0181004c505244c1d08000034400035007442014001075481001008500ea640c03540c58407441d00580b2504c960305006440c240d9252005c0c45081c003520301c0003030700360345e03150303004205042c2030b032041010381a206001000010310034486c0c05111100742005105481c0490440b03040c001814402d000510701540a0b101708100c0d6681511501011048001003507080280060008001440301080003090107030a07842e0000440d900c11412000c1907000c0c084405c07503400e80c00c007444550032641c0c0b032040b03a1045101040711140001070149100c1900600c40c030140c3e003094284100c02d490701c400c02007031111000000b035440006018510000c40c886902a00a203054030030585002010004682411b1400d8002c0c0000d032215011240d00c81c4d045545059561560300d00f80c2c00040c42d4011072 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 727982697 1250 727981447 727981453
    0x70f0f050d110c101434030822020301050703050a2d112701030506061810030b120a020108280203062806083102061e03040b16050d1d 59
    0x203c040307a1480c840501b1031b080d07104018021040d103040c41980090401d03024020610381c400040c104103030361520030075400d0b001d4005807025026034046400e451058070b00c032000c01c0e1100c00f002940c0c807280c400c6000d01c41070368601a02e59005000541c06011032480008403403520380600d544c44200c20001c50303d458440c3c5000e001070742d9003414010b0f84002002c00d600d0000342840003141071443d108041d582d68007041d042140c2c0b4003031550108440f201c0e11203403420600d911401802c00d80da4804d06500d55100c02c4401800e0b030822188001416000700808140084409a205a4030742c214014000c8201c2c0c0d40190059480e21180d0004910390030072401501948180310301d5056500c00c40f11044102d401ca03880d0310a0b161117000001041e89024010010b00f00c3d10800140342e4003111304d00c0301200c54005886146081c6240d1301754005009541d0060120800000034030042100549072a40e00440c2c0383d12810388258942d00c010302c40d01c0307901740030080c50b9200c85030719105401c01034400324205003103411 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 727983947 1250 727982697 727982707
    0x80313150504050c0a081509010f0608010f0c0f020a0308070e04051609080c10080402041d0604032a240507030f1404030e06030c070f0f050d110c1014 66
    0x1a200c01c48040f6281d0041208107100340c1040d000e4003050b100540050710020b03100c200300c04101c0000410b003010a6480b07001c5035401c1c900c988190005040c001001207001740001c1005c4060340c5071441e600c81005000d40e22030450700d03070215210609941c07503d0f0040b800d0310340030b00c100d91402e0300c1c0d09603560251500d800d00504031000c800d5440460095110f1a9160b6910700419468100c2c2149154000f0001e00c00641c00b0f42c401c090030341e0b2117031005100007020113071030345503c032952800c00041c4030540c860700c140400e0503009091040c4085030308040c44421900801d410750303002c0c01c0a01c020102c0c020311010300455640031901c24562040304404001d14501480014003511400e2540d131581480c01c83d908403542c40d071034000751246805440d0012125104400e100050b84020403224000805200000000c5d0040380c0c088190340c0140944014040c0504002d41001e0349240c6502c01e000c448840a20405000700c1c80e40e4440c2d60880360004c0b1504006800e50381c1303010401c0605400d44001507 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 727985197 1250 727983947 727983983
    0x140a0e030d0806010e0909340308073f0201090203060403030501140628180902040515072a09050118140702030d09060f0207030818070b07080313 64
    0x114074416442660b40c41703192040340091200348103060300c2498040c0c018404a0040303d850742005195505800300100c03160707400383d4802c2c0302001d10f07400443e0b0300d8600107595014440403542034000c1c4480d204e4521200d080100380701038480c0c3c4454180104000c1d0206424066000307510900241c1d801030283c540b24a441d180080c01003009028242c10f07100d070394581c480c4138140304e400d45060f200035043c4400c0350f402c40750303d00040200c140219010011941d1000c520184050000801007010b040301503240c03400d001c20000049400c1002250a613818080c90707020074100000c40741d00140711a520141254609610114107460f41c00c02c2545904183c00050680c0700240f0302c290350b81c8030582c10840640035101529105e44155241401644188040038032800d00b544214039091040c0d400150580c1030070105000c0c0d8101101c15004208050200301d055000007a17003821030f4040c1000381c0540c034200351482c16180907100c000b4011140100c0044c1100320801410740078503800c0401084869641c2c0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 727986447 1250 727985197 727985207
    0xa0908061e0a0f0921111b06070f2f0904121806080103120f08010e07090e0a090201090609230402040e1602100b2d0a06020109050f0607140a0e030d 65
    0xa2801294402801d000c445c14502c01c102407503000c5412805050390a0743c1c1c2c09442418410503e80e580d0090301003000b100051210014242c6251056a148000b00081c0e40401d5140500381c22401d5090000042d200d03140c2e41c3c00450942c0b003948000c115451240b13a100c102da960901814034402900349031804035501e0f8009034000d04903482841192804d401050f4121113540c103103c08080440d0700c0d10014000d1781c1c1c0c0780945591120b2a85003221030960313070301941c031100f40d01650084005a9290400002d6591005981d03002e0039050401c0c020030b0740380022644d03c80d00140b141c0008101843c900a0856403181c0440b8018180a0729000320750504c5182c010705648000d000e0405841048000495020a0f00072180d502c0c5004011460030500250182005e6601d04060035148078103001c1c4200d07964880c105000505410f038000640000513142542c0707403015030840030f8007039130011040140443c0c0c0007004010f41010300e40e030291140c0c4901820780e40a9030304030105500d8021a5040b40d8240d40c41 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 727987697 1250 727986447 727986473
    0x324270b060609150c12120106021507090501050a0203090303071b17030403020409151509060b0906030601050c122101050405190218030f030a0908061e0a0f09 70
    0x40d4041640549031001045918403039203503980d07044850010021308a840e000041d011060403401541c0410302c00c000021aa503001c240080c144012040062014039410842100b64041703012002d81941050f600150900c1c0c0c0c14410f103070420200064082c0c0b803620900640302540703000f40071661a0149450314070040c54a014800b00d0400031064005942c022095040d2407041c0490003843c9080d0450f020b000240c03403a24070aa0b40c0455034000032119140d203209400302000c11341002c00000c3e0425908170240c0c0c0c110303070145483c25018010141c082e0340b40000c49800030000d00300b041c0d0f698088a9170034184159110b4050504c40085070aa4a000352880000c00d0103441d244c80c1d042903a2103504210442e40142c9160713060301075844420101d4085640145406031495052584004004000a14180f00b80c40b04801c2c0d504040740380d0020f6904018900c0141c00007101901d45403402d00448000803000c03055415040703118801080f940345050380204d65100e180ca01c01e1041d24814100003035070400d1 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 727988947 1250 727987697 727987703
    0x30f1803010b100509090414060a06050f06040302031e01110c030c1911041a042d06060c240903020d09080d090e061216140a032427 58
    0x1c20344240500c0ca041d15543c6089140b40d02c859060029820602c040c4404c000e1007203407011502c100404114a08010151103002d5444003c9101070820050041d00032001102900a10042c4070600060380c000c99043c0d10f502c0301310071b1001c404800310038550141840c0714a0580e0420002003c1c41c180b0000f000400546083c801140d00028180c1c0313a41c0251105d41e240070300250130521100c0d14a1805420400002c6c00200c80071840c00142c030002012510741c0c004403501032500440e0042e0b00c0050506118240c40c8146080003281d00c1c19501a00e100760381c1c44018001d031404000342a8403555050712003450340c4071410070841d15920b0f103000395980318400c090f140030038000e440001d032000b000078070020658800e6075211061464400c03002c02c4100d0283c5116402240e1840c170412004007000400b01180748501891500d920f0301c50315921090141e012980105000b550501c003103001c890310900240c2c50141d058060240d6491000b000b800200301000301401c04603500300b0449a94502031f00380c540 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 727990197 1250 727988947 727988951
    0x92a020d020712082208010c0c11040506030a03080c0705070b070317070f030f020405060d090b010602010b0f1c0f0b16081005060703050f0c0106030c0603020a0c14030f180301 77
    0x1403919100015032415080080c10352800708a41d10a0000c241700700c65588114400000e070301034880d0142420744155450800024010b000b4440c144103d035901603e1100c030a40d01044241001804240c481c818032030081c080c010154045407003150004120354101d034110b812b40351200d8171250038200b1075002d088241c00081c421142582400030620400e80600c00644400d045107815401c20790240845942200906500740700c0019140c4441c002070100411030400010f0243c1c2c1d500c0e010041d000706070844400c40e803406c2865007032911201489004950202c038609544803072041ca2500407808070b10010100e1010410960408ca580e0000900442d451141042d5440d4a140112040c0350110f03091010800c0390041000744c1e091210080038020b010746800d919203456031b01c40540301c0e40074500c031404a80d9160801c005200c1e036010b000000c3e0550b46070640c541311404000034880202ca11002d40b640055409a4100182c10405c90300d1003024009080e844101e0710000a02062410800381d000754 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 727991447 1250 727990197 727990199
    0xc06040b0708031e01241707300b040c17150a180b091503150702031911070504020325051b150c120411010201060306060b0c0d08060a092a020d0207 65
    0x6c0c2c0100071140e035018440c00c00f02415510180100c030036503a8001440054030906d4122142d007607104400000e000309030840800d44640250034441150307607002d010801c100e507002850b49500001008a5000340c5280c44121080c00c1080c0041c00d50107079035000119100708803040794130071030054000305200d020031134031408a075491124025550081442c05a45a00800d0311f00400c2c0001055450308501148110790800c201141c0030017600d00d4150840001c2840a10b50040d8035404001070005400c0584055045042003181b56000c138210a2081c440c1d00c1400104000c25440341065500480307241d05c10410383c412441041381c0b15400402d03180400d80c1c002001410b1514203600f01d6a100d000c0d048805995076454403401c50300002000e410b811952108070001c0421402e0251001510100e64210368a82c03002007014500740b60b2250400c01c1c0000e1004200c1c9603504c9071104400c840132094080780c0c00031101c50841c00d500303030400c10b02c41540a48440180441e40081e1940f11030780a81c003151529 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 727992697 1250 727991447 727991519
    0xc140c0a0201140408030403030305150901080f0609030f090409030e03030d02040e0f04080a08040c0509010e0114030601080c0d0615120510020f04050114071505090c06040b0708031e01 81
    0x540700d9806003000c61b50080004000007032090380703c50f90000c50400d901ca10807201000241c10301d54280e00c00c00040d8000016810610707403d0003c280c003e030450000f58641105961918030900032501e6061080740e407010340c5001c0c90700448600740c4105004041c0d9948001c0214403e0094105000c0c85009608040c00125540b02d845d6849000329001049141441c0d4400c008503100c0c100104116a03114112800141e15115450194007805107004540341960401030301e00745038003481013054481e600102c0100045403000c14100040c103002c0d5007510840c0100e06081000c0c0c800b08441802d0300f625007000040003e04098900703100d038810000c2c0d0b040c00d40a03113030100c00e9000c0d03109480c68100c010801001158002e1a29042002d8901041e6040c0308080e29840b4920070000c0f00448101d482d10100480034a082c0b190032182c00301150300504043c10705400c40307820300400c00d00408000000021404100e601184030500e1480b05030b20f908c040d070315083d030703290708580c2c541040c0c0000380752078044060 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 727993947 1250 727992697 727992737
    0x1d033901170a05100b03090c120a0201170709050607150606020703030e09180f0a02120d052203080c150c030105060a12020f07050a0203060c04030c090c140c0a0201 72
    0x403112880308400d8041c0c807100b54400c01008003504200108603482400500070304100c0203140b2a4000601800000c000e031400e0080b241e103d0001c4851540100401c1c80c0143c1c1c000c1c03601070604031038002c214400e5032101420340d0324504641020b40c1c40311001c87d060040140861102c064506032620501c16160794913400d0f03a455090780401008078070b10021500d1035040214003240e20540000516441c101200081f900700700d081c0c10b03402141c0d0490070f088001d5040c6800300c8105061504001c100210203843c0c0102240102d41e0000d5108848240b04840c409541b002000655000070803070f035803031040700f11240d6944102c2c890311100e50391348000100045403420590f4100d6401400052a080c02c0d010121051820b10802c410b000d5070030f00548082001d81d5028205d4144600c005100154550041509c2c24100528200003c2010881400014540d20340d040407079480e91004035440b00340c01030690350b8440b0441d00e6650f00c0302c0400c00442c4402c0c00100d4022080c000e881e440c550044500310544 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 727995197 1250 727993947 727993967
    0x11040f0e01050315190216020d060207110609030c0103020d110a12051b09040b0a0b0d0605030c120a0f0311121909030305031326210103031d033901 65
    0x3913415002130307000300c03c021660024001d03040d0404800a4103401540010309c60031070104140c941c01da012034200100480141245030700c030030842c0c00d242440c16800000f5a6501900c00d401e04150300451810302c11090783e0054110001c2d4100304644602407014002d041c501031510f00382e080e90900001c01d540201200c240f8a1107410394803c21310700304d81107041c40040c110102185800600c1408002100e50200d0060b000311401c00101241840c038090406181c03118107200903204d024000480c50340c22100203080705207142d01888111401c3c1843c241030f1541d425007001d02c061405002d8020181c0c454a100038100c2504800b41c03540040c0858000f1505900030f400018040743c0200046450103050301d07064245c07a8881c015019003504161000466240144480400010045603040e06281900c1e9035080b10180310703001c04603640c50b42d10010145079140410310011540014451603030789040c8032080001160548400000070004900c070007030071115508507c940044c200a0742c5961060104070 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 727996447 1250 727995197 727995211
    0x1115040203100518060a0c02070501020601230109030b1501090e330409060e0606091603050612031206100f120c17010b030426030a11040f0e01050315 66
    0x9a0b4501d804400005120141000d155a000010189500381d41000341c50f11581da809004255891041006440d0200eaa00820b0554000500510040c42e842e444034104420500329414182e21240040c1e607050600d40000c1c0c042200b400070449001141d400325200354201303a035040d11081e6a040c41c148011016182c1e00c50400f5a510015900d0b501c400000c505100041032612200d2400400a8101c800d80300c01140e40700d880d020b420708420002c0c080c15901c40e40c1134402c00c00f589420b0280d000440030503030704441490340e00c8003c40e4454603940009114a08a03c0c1100d40e100850409200b1140c81143c441d44114500311109040398070410161081118684401d0f1180c0c900e4001880500386480001040100007003803101039044940c800e50007413200d944582e9990503c2d040801e002114201d0000c018892490301043c1c400203041103940c8223200c2c10000546191500c040d66041c032a0343c0c008503028034402008126442c84005041c1210300450841c0c10011030204442d4a41c0b5040f1401 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 727997697 1250 727996447 727996453
    0x2132303060a1b0804032f1b03120a030207021201150803090604051e1005120109091208130503191d0d230106061d0d02030607110f06071115040203 65
    0x36400071301800c08642c000d40700f400c1054181060030725411010f5031860100d000c0810700361050418120a0207800340e88440d40100358a070103070080200c2e50311105c81c440f002032000005442c1219511a50680b006154014003006445038614241806010744180810060811060001d001c4400004541c040d41001e00014101840c25042084070442000140180c0c08032111822860350391500c3c000c9002090340307501c2d80707401065200840900f0141c008040541c43c1c50750000c049031400340c18051000041c40c0121080d520174420015603a802da90041c5148070110356203000c9100007030840081e10007543c45080c0c1d208004085a4990f0003412000e0b0007034240346c46080420300110340140c9068440c05d24020704032202e80c41743c0c210360060f805400060441003669103040030009003018414011505944500d00039000603490310405410302d810f20a00f2400e1441e2480180003098039500741d4415582c0703a26185a000d050a040380750315420502400441c0c5014500c6a501079008a40207001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 727998947 1250 727997697 727997741
    0x60a060f09091403070803160203030106050403060b03160e0a0b0d12050903030712031407050c1e0a0c0e10050a03050a06020703030212041a2802132303060a 69
    0x44008180c011000d803040d0070300d000f20141402040004014443c450f0300c074513550b881c1131060700e141032100d40c03004d10454100700010400294802e05071425a60001c500145038042100001d1034010049030040c43c4200030403000070044404050311b440f40750100d80c1804140d112908002c0710b030000c0107004005106194008030004d22820142032842c80107002c40340b03040081c0e141c100c0100003508070f54001036158000a6803200302003000b80d07082161814860300f0201d0042e0803c4c0c80e599010a860122050f1041c21050410100450903015411400340c0c1021600c8241e0040e038000125039100740035141003030004481c100f0405401c03c40e0382100c040c014015895845802a501545d01a402c1503000e12500c102005c650400d00d00461194200a222611740c0251629448008054038002c04111040701c2400021088081d1480411f88005030f581c403d075021020b0302246500f103400700c084550100c3c845400d02c031242054895089040740c03441e0f6506104c01d020b5414202d000c961643c05a0704e = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 728000197 1250 727998947 727998959
    0xa02130c03020417010912110303040f020a12081e0a0c060b010e060406110606010e0102150402031c050301031b0506090d1401050a15050a05013f020a02060a060f 71
    0x3005454214480c5009460b2a036135003502e8410683d8080d500302c850755070704002c80402215400241280d403182c2003c50340a0082120340380c03a80002000549000400c00d02d0000715600e20042001034002c410000d00c02d61100e042c1658070350050144204e0380400d5042da01d800c5074020317083e54115003040d507405541c0183c0307544001c0948000e1110505112034025100c400f5680c81c400f40c00506081d42c1d0b802e500900c2c0780c1c03030703540f402700701528541c1070011000084480340d81c042040c0c4400610400300c1ca01700c0d1102d201080c50941e600001600e0340c0c040c3c42c1d4541c10594048001c5040340c0c011604000b10700200c41000000150754882d0301d9202d4810001c0d0310550400302046003d03a80941040c00c41520041410b80c01d4400071945440400c2d81d03000311004420f003c040c180041c0c80e040d6003c104c414206400130f8500c945041a42100050404440042401030322081000302c000169001208503c112003d019410103480f21016000700380000b49014014410101224504202d07030444038503010f = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 728001447 1250 728000197 728000201
    0x915060a0f02070801140702010507080f060609013f05070503150f031213230103180501110301030c0b2a0a0c1e0e0f0a230a060602070501020a0213 65
    0x10703120074250301980e540091038244c288a0a1440300460100f124940744c0500000c0c21500001e20541c00e019800c400d22944100381ca0300d450f880300040d204160703110344503c0142c40e06405610f1070364070481d000c1181058840001110b500803100c032000c2401c0c81d441c2d08070798801c0c1ca80403a10407001800600c0016080d440205c10160089405084500c41003080d0000c070f400d0840440b800307065031800081c07050f00003000c0a0258010038a00010000c08010005511800d0440821280c100354031401d5140b5070a41d03604100c00143d5000e4000c1180e90403800be164550380091000341d030304421045000464505071411076035040310341550007900141411485541c4032601d46149803c0c41a400000c2c0058072036094000541119542d404590680e410b10040704c0d14a6001a40500000c0d400d00240c80d940810107a0007442505011400f40c2c4100b00c0c030070342e64180c2c6607507004660690083c408001443e0740410255241542039400040c1c65000690b039035440e20100030342205403200086249500c075 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 728002697 1250 728001447 728001467
    0x9010815040f03140c2107020d080708040f0f060305070306060215190f050103060b03010603051209060d0603031701080c06070222050103051e0a030804080307020703060e0c0915060a 80
    0x80d081074500200080350f003032104d8001c00f0075100d45500c81e80c2c00c6e002e10241034091380c010a10841081d40781228540c0801c054404600c0f000b4140903000c0380040c10004000d0a9a02800e5540d0b40310118640c1d1382884100c2c07401522491340030920745004540341c1c61007400749000b6214a90002c240110088500078102e0301c004140c41010149506003080c46201b6014150b541d04240c1804182541035080c00c1088a10091800c4c2c420383c5850000c00000701c001ca45c1410480051072000c0d11011640c011442d54810500204a035038a003082c0442055000705ca580c0381c401101d201c9000503070725020380c91b82c3c0ea9409030340168011800c6c80203d00515006401401c00d0a80c0391030605c44400308a40d05041d11803e820840c0da0f030b0440010f51010061090552400003c80c03c018500b0b034110340c5019280250280c00030b030002c01c1c000300103200315000308400e41c0107590008040210207499801148c595030081c0d2407611458211010503d0128811904444908001c00e9289450307824003098585c80c0007 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 728003947 1250 728002697 728002703
    0x103020d020d050304170f0318010f05191709010501031e050109020a0308282003090306040b09211803070b0a080403140a0906030c020709110909010815040f 69
    0x1201c4081c5001920038405031004050b21034070f80602d009076400046c10080e02c440903041907401404100c2210707101000f03040340a102800c0c842f00450940c03030111614071890203200c6940307003411200012079500186401c40540200f030b0240e20354561100607820f841c42031002030480c1007400c0d10603145440e51050181c00a00ca4070002400040607808529440c5c210f074019201d0b0750f400300d0f030302924840070210030282d83d42c1003401c46e038070017030b41c0002804184804074410313a08a05048034103140c0350208201e0b0801030000702203034403030314251901100310401212000c44900030803170f003c0c051586440b006200503460082030f40c100360350030007511300840d040031555a0520a5000005040306150018244000700e40e9640c82e21303107040d080141c42c070005ea2403240c04c0043e0801801003019401000310f005d640c1c071403801042c00c00c401da200724604071480c2c10510115160030740c0480399080740790050040b104107949480f002da0343c8066003501c541c114844100f6001c0b0043c0014005180070360794544043c4 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 728005197 1250 728003947 728003959
    0x2010e0406031514070c0506070c060e0f010606020d0314010e06030114040303022a152a091201050c0d050408042105062805060406120803040c09060b030103020d02 72
    0x1640ba11925034100f02d2a076121040da558203e940c2c03114680d405499444089802c0c9a2052481079440994034107004002d41e04010300c0304486410081c9a420900c07032445004121051080c0c440c440c0c2e03000b40010310556016100d45035045082c14000c0c00b030301456481569200c1626071070000440f141c0807005200c0e9a03d9562804041c0f403807165410201e01072070003075800607114410700204c0980010703418010703110381c4503c08000324505400100c810300000d500307041250744c0c0c84420f00e280500d00c3c0648610801d508081c2403ca10014843c0900071519089031000c2e2915402c07905907080f100141d0b44c1548000c0c04102100a24900303400c01500144181c180c2c3e441c00ba0b80d07500003004035a9a1080d101c10100405e404414000308002241d0010010801d1407040c207464006010551144002400000d49980010341c041e5240d074480001411610124000407516260160113135000f00c070100c031440100b04e404609070500348a10780c1500c0c0c200d221185140d00b150200120b20341d03a050300701d070300c04 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 728006447 1250 728005197 728005199
    0x60304051006030c03140c09042a15080109050624090a0e0a450b07090608071409152205011d0a05210105090d080105041802010e0406 59
    0x880c800c2c000114010304002910074150319145250041e12106065150f200d50001c165596844095139002940014400030004020159a10140c1c0700030719214540318101c40000c8a043c04242400d41c03100958600d4810f03a00e07004044102d810a95046400c0801d401c01982c1007100050381e10f4540c90644074090422824000103840c01905400410b4501200001e2145800042c06200d540000d80d03150000b4111441d81c0b04800803850682c5010708001811034503213100802d941c042680740e0402203e140340c0c13500d0700029003242524491803001030b81da58001210940301e00d0914204402d540d0400b0718120003042009039140605501411542d0200548800008420349520001407008481606103140000240c00900c1d01071002c0080309001c0b6651403103640d94006607040d02c40407a1400c7c408800c4030311204609802c8800324100c0d40c40d19003403244060000421032040f10705a500c070044c1d80e0300e880030301082c2c03850810340120100001d25034000641c0030340607015100401910004400f = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 728007697 1250 728006447 728006473
    0x1020726071e02010f02030c06070513090509030c0601210b0411040f0f060906050f0d03020111030c0d0b0a08150a1503030905030706030e0601140f130c0215090c06030405 75
    0x14110502c030b03010149403810581d00b1560403402144120800c0e0001d1820460701c80741c5543c03216030090180d030400c03800241c1d4050b00c65111070514054582d4900400041c50078010155407580b140001c26220f1040e0b03000002e5805401000180c210070104d2109070402440d40e814203044d101800444100c0411496250309803102d20519051062113a030104030802c203110514101c40d940c1d0442071039035040c908140301580307515400540d80030007918800500e02160070100d0040082d4003030380541240c00000e10842c03a1640001d00440f1070303080780400618a4140c20001031030402d00c5541c003250010300990158500d0021038582c80b00031000c1c08101c4056412040900010340e0b00100c01096500405000f181010030000d8041c14490800700407100b90320401c5036591030140300d1508903001080d003080300c5072216082d1202071400074100c4211b043c0c1103072412002d424050030355401440380403111a00c0070480503d0300e020303c030214040c00c20140f0003c181310090388024015074044c030038181d046603e = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 728008947 1250 728007697 728007713
    0x30318030b04050a15063203060c0d060f05010e040203150303030c0c162610020d0504060b03060601082202060301091d010c2109170306030f0102072607 67
    0x2045114101900f0018020b142802041110208011100c0d24046c81441506032480205a5114410140e4400304640c0c1c1864810289400b90f02c60b054045e1800b032240c0e41500070040c02030034100a07002d201c416190001c18548a056100c0d1031300183d0300e68401e80c02c40c10141e00941c1c000f020805842d201100c06c9010910355030050302c442d1051440042e050130042410301041850b444c1c2810580380140c64400d180c09100d50716501c4000d200c2c494034060003012001c00c0b40e002003203d241e90664440442402410040a0882c0d081e0740c0326051203004c46561502040081c803400058403941400d0302c070401601c50b407041c000740814601020003100009691083c4c080d5008084140c40843c4a080c80c80407030482456161284600d6030511102070803580d08001c88042602e054548000d01c110184565000360005042c041c1401c1001c60310007800d001001c00841c480d041c25011543d02c8203500218500b03e01c100d03d0050003512844042541d1041e6020104008102ca581c89904020a45e221001 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 728010197 1250 728008947 728008951
    0x140c031e0103230f0319171905070206070909020904021605010501030c2c06040216060b0a06050708090f12061303140a1b240501050a1e030318030b 65
    0x140c48810300a51912504060280000816448044d009004103012003590700e020f83e05c00091348000c0c100c030b015003452055a000d4884241f044040030a0304000e0642000e54103403a030940ca00b01d04240000711400d0000543c0c6004220079a03c901d034040c6001c1c0703208001c1d0400e07050164000e80800504189450040d0441440c0f4011000007550354554680001e240d200c65020b440b40110006106900f6160051200d0940c070540301403c03031550301c80c030000303009204181d80b5264403805103003240140300980d4401400358105030f50100a03151500b0055a4a00807440f00a010900421140c101800e02002402e000b0303c1c041d01e00e045c0d0b8a452042141007420844d08003440249845080e024103511240c900340694140e0070091900701d090034020401148029011600098880c0da40104050206240c0c0e813640c00c0d00441c10784c404100c1c03c82000c3c240a101d45841130b1648607000c00c042244240d00451265100c00305a9818550343d81942d00d2840b401c3c0000c07101b018044004042619815818 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 728011447 1250 728010197 728010203
    0x50307030b09010c0e0612150a150f08190906090b1602071a03070320030c0c060c2b020408121b0c0a06050c030f0a0e13140c031e0103 59
    0x1181c54540318010900b1201c0c014040801c02c02d1205a895090300c80e1030440788842000300307401d0220781d20090071884200440c44c1035500003c03421000200909c5060040594013401e580d000c4045a03041421103108509680c00d041200e00e90b0040e642c01081a403205001c03d10485000c02c2c5c42501d51100c244403101110558a1038002490155809605004901c060714106c0d8a9401d500c1c44500c181905010007402e031802d1503525810001e0f0064845000c140c4d0300010f51209079070745400400b000c0c043e0000b80540156219200120f0803171401c80c020b480010183c42c22845a00d4200752236042c0446040080130801c075420017000c2650003081c4034004690301c12091465072021442400e01c1001d00b90a80c0d48c1741500502141219039a550b8032000458080b45060b507103d60307110440c9070451090280b229840c2c04002200343c1d26a4102c0824040a00e08480d20781048241d042c10f031054407250603a51400040d001d002840980d07440380615004041040046400c0a907240d0444d48a802a0415 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 728012697 1250 728011447 728011463
    0xb270a380c130801110904050a090506040305090f010c212102070b06010c02090403050a17010e090601080d090b07030e060a02060f010803040501120b280510030c050901110705030703 80
    0x340d00a0524001c0520003482c052000708143d10080041c10214046c0c4490742d07204a0703e40010815490198004006031600801602c2c0716041a00c0c015115a1110098601801c89900c20040a6001d03801c482c6105d030b008200c00043c10441d203030100591038903404070014000c038410210b005000040b44104498844480103039100700900b860084007000400b4107042044d18400e030030068a5444440d41c01640c1411314544a80d58202c0c1515001a0040404d495110a10002072400404070fa9180140c4c2c9a1080d10b2450340c8450b411b1351124140030208000c031760b20000820509950300e00038000c0c4da0091038070b50060002c000c0028182e034032103108140140d0104043c410740d109034440050040010340011131500e498030700007a02070181d5503002e2510703275036541440082e0b440b031400c001494196400115240381541a007140043e10782d002c1c2e18000c01e00e0180a2002500911501c040070039643c841f141000401401160028144a1009a5409a118000b4503510104030580140d4031400e11 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 728013947 1250 728012697 728012707
    0x30a060f060b0d1a1f080c0d0f06090f0e0703120207090f0203100602032508070210050703030e010203060906060921010c020c06030408070f0f0b270a380c 68
    0x51a840d04d0260100d4415000c0c103000060804540418285a40441c104001180c0e5178000781c00003070040811100e2524140080c81009290a92000042d16411803041007207121201c3d0400486e40b6070700000750030f5070003032200f44007158080c1c0c0c94041c1500700d88110703250303540c6823005076013601d00007550130442c2e507000310502025038031002c455009806503200940c14006549000c0d002c02c8152007000b851820150110070070b0104c140111002c2c9500540800c0483c001510300426942c0191800d40000b45020301c00f0b15010b1040c000c43c1c0c09540014591100380d20b80000700140c0e43e10854501d41d00c14454ac0903100b001e19801c403440e220769081d80001442022003240a410012003c60341489175808004003c005a17108094500b010340020a010092409103401007030309016100143c41e030b083c11810040944d410060034a12030002d49400e403900302070241d0381039840360381c070400130005180406801c030a21058004c0302442a102640c4c0180300c0341c08111350090071030550720380c2044400052 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 728015197 1250 728013947 728013971
    0xa2f060f04080d2f06070318061401030203060114100807020a0609120909050405030d0b0a03150618050403020601180609180219080d030c09030204150e0a0209030a060f060b0d 77
    0x10680b4100b0070503800c404c3c0c802207040d01142d240c1c1c000400c03034030034140d44000180414900500030104254401020440b40c05151181c655103c0d09100c220f10034860702c0e0012400d118425032007905040090042c03000084960001c6d102d00034020301c8102184644403620010600320700030701c04118098401d920160f960000010080702282d08044001c9041005000000b00000b007140e034162401907000821f422246d00188110f0255803001c2d082d0300500c0d140f1403058003140d101c4811500c26440e440c84e1810150510800c0e20021240580580c110500400c0101141e40c120f9801c0d4801442c0000c2a80d01c80002e03000b01c451441c620b80b000c0519240307040850421001035207105181c0c1260005080c80c0000b040d9a42c001440318008040d202e41c1080881406107542002555008100740008040900000c2001c1040e1042c4000300c510ba4002c2081c500552027100c0d85080058040c2c4051071650b20b6007400341844911803810155510030019803205000050100b1580036040400d0700c10391a2 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 728016447 1250 728015197 728015237
    0x60504060c0c0206120405160602030409063c150302070b07090305070612020d14100906051e0607080a200c010906081009020a020a2f060f04080d 64
    0x54100d20901451090390005039554130161008260380c0f1001c45419921880c0440c02d141c00d200101d4080c2d082290082007494000c00540207584e0229020800c03960743c1c0c0c1d145030701d00243c034900040d08401e0400c9070221480503440d0308600300002e40303041200d0355180d0001c3c25481500054400103a8085008010001510b02e0503030000d1003841d160042c0d90543c0c441c162244050300c030703c00c20300024280400350501540c0543d180c003452a8020020301701c0025010506041c12103480c0c0c40704821311808a08204148a800213554019040e01418500440404440070319500ca01d50b20440a1100000203000340000703108000e07035640c0b1402141850301e24038040428446c02d00d01942c010104035191039030f1103000340702150240e02e03000d529232f11070382206c0e00c10303075015000122141e00000703003c9460380e000144803039801c0c4144045d015000e4510808081c09406003003081941102040f2289280b9200016041d0310784400509854241d4401e06180707800000760701c40000c1040c131844120900010 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 728017697 1250 728016447 728016461
    0x2040612020309190f0c0e060108060d0503090d02010c0209070302070c080102031e070e040e06060109060504050f210703230a02010f110c03190c060203040803040909031b06050406 79
    0x280039030542c14003c900580701c03031a801e07085501c00c2c5800c10500a02400d05614842180c10151120005031140d8000b8070020040356651f0114254001256844c10082050346885400c10080c0d814040c0050812004030b400000503410000720100f50405a0f039030030000c3d4000c0000740c0b40180c0d903540078606010107070702d45d501c41038069105200300040c03444a01441301183c0c1c0d80c201124120b40c0d9100301a034002d40d46414083c1c019141c000e02180d44000080c203e40030702d0003600c0781902d456407994121090710850160f0303900034282100d00d0015061008840d529050743c0000d0004205e006210980341001c1c0e1f40c002e44038911b0203071902d0351045c0081880680261b686010382111403180c0c001a2030300015424007020070030207003510b484110081c04201c0e041c0300d000b42501c2d107032001c40894440c101d40840d010b0712601882240007900e1400002102c080b00c01c5003000e07504090ad0034012000a10304154141c0a02c120b8000b0a0440500d4951140955220780c01c00515404c107414807401711055 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 728018947 1250 728017697 728017727
    0x50a0b150c1209060f0c0604020f1e060313170901120c17090f070b030a0506030c03070902130e0118110a0c0f06180b1803091003020d1e020406 63
    0x30800800c1060310380482d091080070000b41105540300020400724441c0d2140f00300c110030500340410b01d00d0306c4d0703070020550a0085000301c440300c14101c072900402c51144201030308400c140c185800c049865007001b00146603c0420195411011034003912912400244548801624640001c0c407071019a040581c643d0070024004c41041404610003010f40700800346540c1c1c4142044250000703601c20420030041042002e48400c0c3d4603c00da40d8800000b840d0410349490448a0415001800d0b6090000d60240707000c100900602100785000130301402548012501e800c002c11019020900244146009000b0300c43e100c0f14030840049103000d501158924010f00031450700070000360542030f030322040410b24182c000440e04e440c601c3c18a13215000780a4510900c0c044070020b40f0711410b1241c00e4041501c10a82c2d940003213030421119111039204d2140c046016409040c070200e00c0c001500ca40c0c0a4000c11100001c00140e0150040042900300000e281d00c2c03000380d40000e018400300313500c9103c1e4812900 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 728020197 1250 728018947 728018989
    0x90307060f18211b08010c110a1214090d2111030d0f0e0a06050618060114070311070905150915011b0606081e0c21070306050a0b 57
    0x1090a0150f0321118104035645400c0354480303200400e114a846074049003084e00140b24820315510070305540a4410b000780d10380801c0a80c101d200064201141440480f540f005440840100c40300044e00c0e207241892114524210602c1090351036200e9000900384140900ea13920b42c075280703204003a0720040043c0c1c1c022081258041044200103800400c0e83c003020850000442e903000860355610007822000010306603440788400d03500034000360768011380c0a40380503540c001d820914100c10a84065090700c83e5030018400364002203081401c207000d070440f18481d240010700001e041c2a40d520b010784d1360700903d19079030b615800d0000707061805440351303883c4406880140e414580242c109000801c4582c4160500429004600551801c21046180c07143d0084c01041010f0303c1ba10219a6022001c100c0b408403048200c00361164480054a50080c0500800340e034100c040c0c600c01c0d0094024501c43c0388c0018441c0080c08000030395580551032140040810000d0455040c0c820001681402624010401 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 728021447 1250 728020197 728020199
    0x10629160c0801231e01060e03010906050c130518071218051507020a0b0117010605031615050702060d1a0607060203040c0b0406080106140f16030201111602040f02090307060f18 78
    0x6110440785c904441c12401c082820054900200e40074268950b00140300341d10300400c02c0342020035000038290552001040f0040303036480d03400740210042c803071008482d6000d0042c0012a1103220329070681c3d20061200011842410110304449c403042d440008035419044a80650089452a9941c07513101c2034a2000340345015582c0c5490b501118180692880c0c00c104200174103842c0c101350000402810050300b182c141110884510242403a24095014070f00034684d102c07800c00c1c1c03258080c0c44405030000c001c945010401c4c0540b000401c540301c004403028541c0d080340b41050760303030300c0250411500074000540e691030b0500c0c2c0040d402c0c1150304905140032043c081809503540c0803c0c8581903542e1030400304148011514548403901807414808840709001461040c2908480400e031a9140700b600203000c2e00d00702009440c6107008020f107a4140390f02c2c1c00c00c02c801500e8507810003200c0f14082100180381c03901450120342800d821303800c40c03004215140c1c0c130017455a620030f00c000c0c00c05550709003030b900c91 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 728022697 1250 728021447 728021491
    0x1a0910050a051c0f080a0809060105090c1c050a0603050c03030c031b0f03040b180a2d0b040e0f0109090b1b090a0602010629160c080123 60
    0x325060700a082c042c00d02c0d051484203c03580c0340710544000350020510f0078540d03014901081154000c0da2220000781ca02400321310440c40000fa8141600c03401481740c210759448040a41c01608852141e1100b55121109032209131014071030b45008070351752400880e0080c10b6060041c9840c0002d903101740a5071042081c1d5204000100541c1d4028200510070350100a81c20419842d20040c81c02510f628000003400003a118801002000042d00405074500c0b5009600c0401a0003091441042c03803440d9518420b038403121540302e00081c440040c4e5140b020032030710307181d80160b6504070760404650110010705114203205082001c0d40108001441440f03945184d5407180760540d005042002081c80050b202c045017404035040c0c40c1070100c060007000443c2d43e6400028080e240784d100303920645c44540030901602c500f881854804043c50000c4c0e0349440d00117102d0f0181e01c103242806503003c003074100012034844400c0c01032a48018036024640d42c40c0014000320104000040e0282001c0c0b801c480b10f030060 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 728023947 1250 728022697 728022709
    0xc031b010b120313210515060a0801090f030302030903040e04140f070308070209040206040b032a0906040b03100b04030b040c0e0f040f060b0301091b0f030b0114010306091a091005 79
    0x660318482e007041503145ca401c40b081d0700e601031154020304a001da0741220424212003c0e08031b1207030358101d42d0520039607543d0018a00700c0e8103c02c0040c000080010000d030200703020350010350f001403d1500701c07450541ea606007003d500c1026601229040310700205042daa40b81000460445640036019003000b0f4590382d101c1050b03108501000b4040c60080d8002010341da0356805880c002c020080e00303a03030340385058107102c21588102c13026000270b00807503040d01c2c072041440008da52a41c1c00280c01c8500d4241000d001100940004000e4000c410070404085400780a20000d00020352080600d9202810580b900005250598002c071040010302400c000c114129031400e280c1141d08482c01a000d10040e0078003401410b007030a1541d41560070041c400042141c2100c00651042e0244014030340d003501d81010300984000d03031002a2004000c0401400003016403a441c2c1e140c403005040004440e540c403039202040d41c0c800c0c48803e4810030300024101e140d00f0481c03a41c40d07000d013001c251408440d084c400042c3d0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 728025197 1250 728023947 728023949
    0x230712050a1d0301020f0a0e0a0605030c0d0e0a05030c1005070e061602030c27060906060a0807050c0d050405091003020307090903050903070b0c15070f050c031b010b120313 76
    0x4002c44000e2000000d45081d41258030242c8104182a9241580c80000d00f50b0a0154005801280b800c0400030300140300301c0c141ca0240d07440424091820160001f0300016050842003003a05005810740800020001c1004040e000c2a11000e020501c066582410403100014040024081c03000d65040c86640e6800803903403440c0382c2003441540c044681c000301e4a010f03044104250880c03403034606600000398a40055888010341d11003510f09558030000e02002c1c1006a503201d42085040c803e60400038010800d044d80204649401810000341900d140d203400540f500410220b10f001509000b503090005010707500c5120b8403c2000e4107480d60780030a0380e0790703d1440303a13001c600e980714001810540304404480c1040002011260382c552230b501c2c481c8540d8410300c0101400d20500000301341b0b965900107028450034540d100c000d030705050300720155071551140b03521000c01e010400902d180448003130f03100e040780c01800000186c0c0c280c628040c056236103e00c140c10100c95000707004100314404603090b030324 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 728026447 1250 728025197 728025227
    0x1030c14250302010b09072f16090e1b1e03210703270311210115061d0915030109030e030f010618090203031b0c0f04091203090201230712050a 63
    0x20342148c0c6540c032564100001a01d01c844510950240064220043d8100210542c503507000e4a00500e2600440720040148080041e006603404040c2c410360b442c0f031404e8a40000c0c02909075520b5000700c0700c43c5c0c13808088030015050302010201d28103007070507441000c0c806411820790840d5080c846006404a03c0c401510000b0410007c10350041c1c0d09403120003c9000001c00c002d100c2d110f1a40d500e0b0b10034083c1c40c100d4200f048005849400181080c0700e031010390200304d00c80e91610100b503990300500c82d6103a070050a001151104040e661643c0c7c07400d01c1007110890003036444010795501c9c081018181244926142d809070704105043c003114401e45140c455002c4e10703150004a600191010034114056005001000c4400b4800c10600300008108200350382801c5840c812a640003100b088226124990b019066202459080c00710354002d03070000100c240141040f401421041e9400c150a000608048424003000b0800008000d2406030031144980070703050035802c085900d00000c1c103642600c4211 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 728027697 1250 728026447 728026517
    0x603040218060f131a1f0f031d0a12020313060c0510090b07030b03011407030f110307090603050c0427140106050c0c01030c14250302010b0907 63
    0x3082c45a5120a10040209000b60101101e100e40e80030380c00c0144a403018504004041c0c0000c080c00f0b00d04115072040c10725801d0407102c03c0404605040701e8098002c4112818155503902003036001000c1d4011110301d182040080c0342c400078a00e00348510400b80e002100c103540c81444120b01a05030a040340c0c0545001e80b4040004a601e0f0138000c0c0b80080c130085000b1075a1804c1e6070303002400000c80c19944540000d4905001c03424149080c5801c941c1d01c0350403181c0d503008071380c04a100d092107038108564400500c000411082c21649152419a10544025000c43e080003420008541c042c010b80b58040c05140005003001d240c80004190f0500110180603442c54495030143c54a81640c0b0252207100d601d04064100d41e12440c1c083c0c415401502004503030710070b0180b48065988a8000c88a40b0300c45a5075400c03000c403586480c4040d98000e1400c16819407942841c900011703284c1c1c42c0d8544820b000e507002061305681b00003401100000036080f00100100c60131012203500350340100190030480d003825 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 728028947 1250 728027697 728027701
    0x21020d0c0f02150a15090c02011b0e1f0507021503010501030f05010308070605090f06091605030f0d03020f070203371a15100c031e021207020612010303050304110603040218 76
    0x210000303880446e0003604043d49007074050702e1800da0544c08002411150044019160f10044040e00c50024016610f98410001c141c0400309481c50307045101c07145010709006040c04031030380c0040c92024003c0380601c210340010004101c00d6a06005445401400f514100101e5045403078a0909110f404d4000c0c0c1460780f50004611103039010444035441c881a040ee0311454202880798175224002109440031140d080200480d107490041045a10344c0c06920041010390000c000560203900800c10001d00e6880900c404c801585080c0115000b401e0350180040c040f100b00180707a4110b003211207403200054036040070000065450000d0083c4000240651702c2c407036440d020890121100d018041e41c0204400c8200001290402a8104254880d44070350303403001c4025802001151140442000690001d811900782002400c014050305001402041c508500c0d9100a46c0040d8203074000c40001e0f000200b00400e0240d066801c2d106814100c1700586941000c1c2c0000741207169500c6021420114800 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 728030197 1250 728028947 728028971
    0xb010f0807030b101e090f1a120f0f030d0c0203090306011413020a120e1b2403130c050303040308030f150411071b03080a21020d0c0f02150a 62
    0xb800c4c2e00801d034400514415201814216411011a22801100e94240900c4054090850241400b0000c2c1c8002c00b45c2211402010031644011250340741540740110040c400c0103207418403401c02608000d2008542d644454100d070700c03c41300361b800880115041070118000c140d8020a5050455150a58510946400780c001a015074810300741d004407a40300042d1b0358600758102180843c4a010310100b0001e070794252064640791b141c0041046d0b0380e11480d042503989490520300300c000742e601d81c1000e200c0c42036224280035100c0e481503500720324406e4084013901c2003200c502804805043d00307401035401e052641d40d400b84140809000346040c05c40c09400101c8001c0540250051260000c106200c20405151a2a07195121803426655403850441603032451000c45201d400b16944580d0040c0340c1664250101c0301d880c20110181e203400c20340c1e52489840140d5002406094990354800503411546050203000d03003036a850003a0035504150306a03096020066641a441101d0302c00108a10201403 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 728031447 1250 728030197 728030221
    0x903081005011e0e04060e01060810240203070501020301080a02030f010c08060904060e0115090f09080901050f0c07150f02060f1801090c03060f0606020304080a0201051b0a030305040b010f0807030b 87
    0x1303000a4010345040390004a00940c1c0840074100c1e5110f0301c44d20703101e03241c804a900f4400628000c605070b00b43c2c0e69001c54100d42c1902c40d10f041200701c44c41074904008a0790754550aaa00a03800783c0e030b140e840450180198542400886480c1c070b9184002c00140c40e504002400c107120040201b07125159100000b801d000094100c050450011070003040182c11041c8995807061144c010450214074004d41c0c07044c80c3c1031522908200070b810103050303401c24050000440e00d980c02a048010b901c90700303106010041804103d080098148041340c0880c012590303200074501e420340c204a908640c1f00c0414422110a0030320f04640003d8080048840102c0c1060f40c18094400f2140082580c022841c0c00400c0c006190b10410002c506144e007805203955409040b0380c0c81c015802440c072142c00c0b405a010066015030300600d42d02c0c410003410b140649502015a0804510075803e80111b510b07581048100404210f2080c05054084004c0a9150a0406a69440072a0b0000410166104000c51411f00c80d030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 728032697 1250 728031447 728031467
    0xb090d020f240c0c0303100f080703050307080d02070506010f090510030b16030219050304110108160c110603130302070602010c0903030815100c0605010503030304170a0e03010c030903081005011e 86
    0x200d0459580e41002c0407102441841482008c581501895010816800102e01c110031250090015818601aa1607200e502c2e4409020700088075402c00403078000410520600340286034042c40141d84514048007181541d0000b049144860710400051000401c0910481e8001c103812400b06818100303590700b50002d200e003913078a6141c40c185030380304401c40354441c0c029031140d44900700d80c075800c2d0600401914045810b0324100d02d0306001d40803054040e48a8103071440c03803501235480c10550b0300d00080403d80c40c2c0c0c800d03900012814089202c40e0300340741e01001104002d29040c03001f007124a4144400500c0c141141c00000c040082034400b00740c02c024a07080651a02800406201c04080146401362180c02039100481d00c140c10030f80001140c2c40c010056034416070304182c0da0b000c0518060305030307032503603010f0484031007445181c07a440030113a1424410b102007542d0039203000800415904001d005008001d0021461201c00c1d10305000590b480446c0066002c0001110b15064040340d000759922129 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 728033947 1250 728032697 728032717
    0x1090627030f051902090a241418090304180b100c021e1c08040801051608010801020f03012106050403030e190f020d03140a1e050306010e090a090b090d020f240c 71
    0x10148040f90071a45209c0b4581c03000411036070043c0c8411040743e80051003004640660140e002031104214401042c196000c145111990006d1401d00c95000100309415403000c00c0001b03a074410360782085081501906a4600291440000000d50503001603002c0109052503091220500301000411a9103826035010f020054028041c525201c581d10500b445a114a0000641d103600001041b050600c01c45056090b1000c84ca403950b828405110104c21201840c06802400c007003200c800703d0114404c013401680320f036070086000200c030a04079280120000c080c60220084241c02c10004809100d5001915070544605035401803900303040c0d940f2000c41151480300c7c640041e1069219900c420180312a550341c0c100c0824585858404072241e0104031195800b01700180000700040c60100c0100d07038401c000282c007107110300440c1e407501c0c01d14400340d8a0301c21351782c800c1ba0354480c07850301800384c54003205101c401003221340c48000a43c1d42100100c0381000009000c0700206025030f060b2411070741c0ba880 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 728035197 1250 728033947 728034011
    0xc0509130f06031e0501110a0905010e0a1e050109052b2607030912020612280204170102030709030602030903160803071d01090627030f051902090a 65
    0xc1d40101340d18000590b02049400c0d520b0310000ca0000541c810036140002d40e1990b80240490070600150b40101e000882071717500c80c202031000190440c00e16019141c0c07542102490304034503d0003001412000c12a004144545030411504180a1180c51210031080184030f149003c01c9144c2401000d030040e440d28a02d2400900384c40310f11102000d8000c06505100355505491103030344080c5400006079001001b035000104101b1100b0094410f4002a04031110110421200140302202501118891178610703185401141c20491700381e81008400a03a80150001c0d480e51800007402442c1e106d541c04000e151aa0201c085501200d0130400d440f804120040100b031a41ca441c00c01d4480750704200c41800010350b0031003503110404886016544400f0068640161050800409450301c07e0741c00c500d215504917041066100c3d030100707001c090040d0f02403064880c1000c801d0038820f0514400032000965600802c040c0b00042e104c034155140d02a08103100050104441140c0208910354002500c01c419 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 728036447 1250 728035197 728035223
    0x201110f1b1507090e0402060a0513090e0706121814120307030203180a200301091b08060c0403050c091f081c02011b08040807080c100c0509130f0603 66
    0x14608900d050080c03c1c40c0c0c841d890b05540d2046492104031045600075001070040c0004c0c0c640c0360003807025181500e448006d410a01c0e40751800182203401c0c1042010250740511810000f407900195400d50094403171200380070401d03820000825081c0902e50051422020034900b580c10401800344994440075007007a1580e03400c101078018060f41050f03e00d400c11241c01007042003e62070028000b1169a440f01c00c00c02c040c03910501c219840900d2880d01034065480d018880001070301c00c0420110054150550b5040d241003821003403130490000c201320189a810801440400d00000c0e111590139002c4400680e55a03034048420306140303080360f40740000d6042500101e880740008c00c00081020741c6400c14008854519000c03400d0f0303024000c44075092898441004101403040c0d00041c1d0003401014110714000e441e660f600903544c42088106030315007100540d4464200140100f550a0800d454805d0074000d54400080103a003c00e2030307800c0171076500c00352103043c14000d030000c000464001c14a88104 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 728037697 1250 728036447 728036473
    0x903070e060a0b0d3309150b040905071e12090c0905041412120f0a0204030b0a06061b020303180f0d03030b0f120723090103110a060201110f1b 63
    0x540380c1710166504202031803403802010a0f0008401c10100584650900e0041c84c0504200c010402c040200c072a4840c0841d010a50000303070001003008110001002980f850304c003800410b03c0341c1c03000240040160501000201076845141c0301006a07591100054240942c509402c061765070340e0010003407500700b50400007400818144062903000c094166600c9541048903000b55208c1c0340020391700d004000f00403415120118840650046640000500c2d250300c80d1180522004100e401000701c50b05d076801480059400000b080c0c9800b48005207450410041d03000a8480c002c0304081d4203101c0c14501c8140e00356480a140f5406000f000d004c02d40311002c0c604004020700503484c0418020350101c10004018204941c010f82c0d1071b482400036000050400e810145624400120700c42c090803080d2041c045030f0385280303400d4020f5104020f079440503003240050021050b85a0f1107403080da403509d50000755040c55001241d10316048a0881960f400380c8204c015403039400ca08170741d049441078008070724403 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 728038947 1250 728037697 728037701
    0x180c0b040833090f0607030b010504260732010e040506010e0a09140f0106020a0209090102070b01140f15030703110403061a12030f0d09080904050703050117030903070e060a0b0d 78
    0x10842013002525074503540e80300160252034280c41e40500280e0100030800514200302c05050540c414802507031503062002c40c0052034252143c0144007040164007071114003455090030b064180c0318980400c030094003a41c5c0003900c04525208054015a2640006046603200c0c100780400d500004004000782600c40c90040c008251450b0a100c070380c1c0009020a0002030080c043c070781200c0243c0d00505500103143c0c2401501c4602800c82d91003503400303005141c002501446807a0181010810000d8024904020007035103542102c1007502030260103c0c00d080d03040c04182140da01021a0034045600c0d40b06411041d072601c9154800b500c1c452070172010800041c40c011000200c0b030411514451417111075003020340c8920030b20b038407902c00243c10004c00c2010310072a004401003500481900d030a0680d000003003030565030106d9800000a9440e401407204105003807005030b20400c401c0c02907040070540808280d4880392030080200d405c00c034000042e04d96407800e1410028054071026651110b40000c0d0f00e40c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 728040197 1250 728038947 728038963
    0x40b03060c031608010302030c15040b041d01090c140903070503010203090114061906120b12010c030f092409050d170c072112180c0b04083309 63
    0x21103004100c400802c0a12507081c242c11307030f60008e0160034034482800810800c009a88030645a2400511000035a00d0701c0102400040c034261130400c419041083e407100d601c2405800101501d4540451407401e9075000210604010800d00c40640c0c1f0303404800000e28061150b03104030b0307256000001300204000190014001482c041c110500d45444207010442c03440981940158030034201541048814810140081058140703840080e00140c42e8011600481c1c0d01d03045030b26569101c0c0e0310041d0283d8103110390300c0101004001001151060703500c103a0f26000d00d1100c1502c002e170344446241840056800816120b83c445d00b12008490f03400301c050140750f10380030002d04410030b01000a000e410070200f100d019076803210007028410984e03038603640c9178558000000300700700e1000c50b00302400c0d18a220f101d5540440840360202c2c84070350318041c142c254685d0803441100c8000d1004208081e00001d00440c0380058404541e4108411220840c00e078501d506400d071202000010300c04030500100b8045 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 728041447 1250 728040197 728040211
    0x90602070b06030a0210030b040605090f090c01050414060d020f03040b04031d0d02091902180a050402040501350f012c0c0c15010801020901200a060b040b03060c03 72
    0x20182c0d030b8480030581c0301d045100300690424200556180202e1090b4002e6900042c001c0000500c983c48801094140c082101d50740404002e010910103620010040804004024a84071b03103072605084034170f0901207606559030b00540d400320380c181c0051440d070140c03800074070038038100307522464641010895144190b03000d8010a0700e8417207541c1c0c0c07807031590095800303a04c020308001201c8165500340310903554020104000344001001d041c0e80f020312030000742903512100070309060401b508010068041d020358070691007507104100c03c00c0b03140d821482c0d1007801b00300000341d03801010001860854400018980125200d101000c001c5200c2d41146014113940c0c00d514103104040c088483c110b10411500a0290000c150200140f00c0141700402400c4040c405002e4038545625030f408030a04401c04e07004003415940204442005581c4848600c02451003900d2940c044d0a0307640f52240c0320294031001600700d5444274641511a2a10381010a00040c007508a805514040704043c502d508252412 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 728042697 1250 728041447 728041463
    0x6120507031403040e010e1816050114030f0c03070909090b010e0c070515061318020f1906030b01140c10050a090309150c0c3b0403180909060207 64
    0x102d8042000001e070b030142e0307a492a102d15180d082c180401012540203044152442c02d08001e54000300c800d0181c22040c04031150701c55030407802c2000141ca8641002901d8403404030a10820600c26000342005d9044011595041d640e03841c0c004080351106155003210a54900381032442040242c000320003412103226000720401c0340ca0f12440d05415100baa4800f8107258402c0b00c900c0c10000f240700034560448401008003034061864804001038030304c480032040e90589030468407019414401ca89030810300080728400300c04c076a034280701d0110b41001d00902e400c25a88130300350b1070240d000f0f10002210490041c081d5480b909040900d41e0b4490300c00185c41c80326170519000c00e441c0541c070b014a4905980c181c8072106102d0810303c3c0d80304203800f0501044100042000d032000403590200380c8502030144250003806071311201c00903100e034100d1100d105041440b002d1421904030030205004d5001036062503d02d16130203610119141682894110024144c070b030902d00350030030a29500401d502032080201c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 728043947 1250 728042697 728042723
    0x9070f06020f060c071a1009090c090b040e1c1404030b06010e03030405030d1202042c22020d03091701020703020106150207030f061806020904050f0114060703030612050703 76
    0xb4801c094017038070b0401018420500445200b10480400c0c869011040f00c500980095807400520300313031011000e040c1c64480da02c4070240302d403480e6402a860002c0c030036501400f28000307440d56655035036004d014140c12100f000c201040564440c0f405000020890f1145940390b50702e038240851288400e441c0c59011812000d0b20041c1d5043c080103580840d00011f010300180c402c910300580d0040225070412640c142e0801011420303220041540400515041505094080b02d0407240032088014298050400b08606800c4103050b601c0040d001c2d25505035214423a218043c502a074214200341c0181c0c3c1c221580050038200040158081c206041c00790f03009201c003991302c00107004488021182c440050300101c0c001e00100d217046070b0b5481c0940c45100001480c001d00c0c2410031030403840500c02c580702030300050101d42918141c083d00e9004552a0b02d2082d540d4074240741441092003113034036a40a800c010408409140c000d900440080810f038031083c2108840340b4000340c031101c9038007080b2003000d00001 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 728045197 1250 728043947 728043961
    0x607060b041103061f052203120201060e0a090809011110050124050f19051902030301030c1508010504050c090307031a0f0c07030c020d05031206130e1509070f06020f06 74
    0x812042042a03a15058640f81041c142406420012081e0a18507c10160000b0000c0c890042c071010840140e80002031032402d2020040c0342e520302500c480700035030602c4182c0b00030442050032a2540c030b0003428804240f545011015080a4151001e11191460f00c00001207800c000356103608070840a056003480c0b00603020090390b144c0038903062185081014041041840c1c0110b000d400019840c0c00d1050404070040304680c07807003071060200801600003100400c04c001da00320705100580b2000b2038290031180000c0d0010283c0d58148122485551201d01103101100c4130001c0b0350301050080c0c2540d0444d51a824450002d03040342030340500f0190848009040c010712000d4007030003084000e252074548800e80d00c0440c2c094814070020b90f03014600401050029008000070300c0c451a840029803e0341c80c00004000243c031a4081003e02603043c2081421211000301d04805c07401d040c8008040f65072074410086151608503000f442100d800308070042007040d00011030f0200100c0b80421200070b9641d000e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 728046447 1250 728045197 728045239
    0x6090920010201151419061806030b010203030f07110a05061503062403070e13060c0503160c06060504060303050316020a0c0920040b180a0302010e0607060b04110306 73
    0x1c840081d07100544d203020f22503400c40050000c031414004010920944000c2c1c0884014441070b0320110104000100e40c5030050b0201034404020020b80c1000c000341e1800b080007030740ba8032004001c3d503500d180f8030300000c40c8103000c0c40d1544008a034060456006020614210340e035100180d51450900040b0104a6250f180c0014201c0c03258201d0300030241c10304800c41000083c0251400d0855241c02584800b00b044c40858241501c07402107001411341242540c00d082c1c049810300001381040000c10010002c3c014000d0000180040040c6459a141c00b0b0600b040e10041c10180c0195921600f4100004241680a400f81d80104901001d03400c2400084205983e10b0344100001881880201c2003040b6000c0c80e9840400c200b00305108403440c24145903901000781c0d00c660011881c0fa1400328070780d100c62869007250305144006540e2800b403581140c0011341794200624100d48200c0000800c00c00304100b80d00114009003004e0005e112044545580e800c0310f41007264035074003455130108074180c1c2c0a820 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 728047697 1250 728046447 728046461
    0x1403070b040b040801110412140a02031902010e0103110315040b061237050c09091f08010e03030c07030908100209090708061320030f010303020c0306100e070306090920010201 77
    0x261071036003010b204603600c149482c0c0760209c090f1000d01030100c0300d00c0503031424003075003d000390303030600700c010301000b40c80094104803402d00440c0c101351400d540c0a000040c0c24080f00d4010550542c007042d24074a990020317001d805542d980b01c0c6c00000120b04400c56a007400d51130750040402d04420118120038403428602d000b054a102140d1105004500010070540e501c09600128121b03c981d1030b210400005c543e031007001b581c0352407400d4607050b1504642c080d00700396240036000746c000030b0204140d450383d0ba6559000c05440551590b4000804004050140700d0202c000e00180003520501c072503000c0c82800942004001e14003c070004400500b40500c1150030301e200700001050b4110308403440c000b59009041d00404a40c4050761000400d50000440c0e002e03501c2a210790200d20302d00e40c1140f81c0281410b9001098038065131000d014807298070041c16259003500d40040c1c03120704c595182e44003100501519841a50703038a00c1c0043c02003e00900100143e0301401002d01c0400c2c403007d00004a080340c000c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 728048947 1250 728047697 728047709
    0xd05070f0f0803160807060b040e0d020d02010e0a1205070507090f1104080d0c0c050a1404150b04090c020304170d0207080607050d180b070c0c060c08041403070b040b0408011104 78
    0x60703030400009150f0380302070031046001d803600180324230240010400b200d00006040f0004d41c8040d5003980c52940c10040140111a9840280850304450715010b45d56010154014502032030074008554403449802500c000c650800119044550386141c8503000b4080300c07900d890304038282050303008404440001c540c100d800200c020001d03140c810500700c820740075240d411606100300400019184e03841c40d06e050050485211200310007040703c020082100c03809002102d81d160340c614100000f1621205560450741500d0011620300c0700442c3c01c0342503104540103a19500740590514440c1c1c0700008418014081c0e0b41c007115100c68494801350703610f91003151540d001039801c10854400100541044003900041075200600902c140d452101d0201c0841d403100000e413417a0613440910400b681044010a00750501d6401292140c0380e0409620460040707041c40448240c07612182e403070410564000307007101100182c5943e102d0450707001d95405486460425802d04aca12910111550122003c03245 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 728050197 1250 728048947 728048977
    0x1e06050a121a100e130b180c0909100b0406080601030f111005120a0506100e0f062115030303040209040f050a0b0a060902210402210303160c0c03060b0d05070f0f0803 73
    0x6902c03100321f01503640d0241c6c0c2d007000b40112000c02c0359540714900140c0c02901004090189000840039440454014981c15840341c1c1c109482002840004140681901c0e006140f008a820150606011604d40821031a4001c1290a00352aa456011014050714405190003500540750501140180ca2003507840540c0a20040c0d0440103d50140616064454010300320425554000c00055255001008080d07944c100c0f1800211f1504008000954401400c1118100c40c02d210000300340d607400001c0c0001d008007107400100b0284070520b84030940700c581c401b045a03840c00403464140b0604406031046040c050600c1004074940000d070007500c10005407201c011702201440d0140035500c00340680282c0c1c214107200102c040f4509030a10080d00220b6040c015652401c000c2041c0e1a1580483c030301e10100300700407808400050480e0010000c03250055008641103500c2c10004180101c540c100900324443c8410005041c501d006148040326003102546045603914801c2c25101e1081c036900419001c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 728051447 1250 728050197 728050201
    0x20a0e0603060d08030c0322050a03120f0504060c201f060b0a02030901120501050105091002030c1e010c05120a1a0406091e06050a121a100e130b 64
    0x800c2440c041e6600c140024203005145480d40c42c2c1c0080d0354002d6800d10f10f04c80b400000c0041110701c01a444c1c111152003842d40111b9402d548400f91600f11100000301005051452142007001c00e070080100071000700002c01c16800d2619000004104000d07060011a1500b210204503000c1c1c002680045410030000c0c0a000c07880c914403040c85044100700c1c00c1010340e608008900100d1400103010303003901c02d400540d42e07034000b040094044150302e1641c0700b0007814000140035699200040e00c1e40c810081d580d1300c400c0c0640903400da04500452003032001030320400150782c490021038201002c2d078210741e0780200b01300c90150b0000c448920604c005c6000f807070500310108030428100d51103504580c4500c60004c03107a84003100042c007669480d50088802c50b03290302d819211003c00310440c5a228415a000f0402c00303182c1740c0800d400090510825239030100f101402424052600d81c3d42003010840c80003000e0f07520708003a401c1041d00711806490134240fa40ac001614050350340c4035103000d0b2070300680f900c0241c0d = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 728052697 1250 728051447 728051449
    0xd0605120c010c1a07020709051b0a050d0b060d020702040b0301090b0c0a09080706081e0603121303080d050f010909111c05072414090f180106091503020a0e 69
    0x49145004640c86580da1900600140f03507404c0d028090603ea5020700002c234509500c0000391074001d000da003a540c040c5c80240e0048000700d4110ba14012950520039281c1d660510b28100400c20b107180c094100d00001784c41040c42266600400d1035074401c4078108880ea0030300090508071000345a0003410862800301241c851692040945031018441c980903440980b111040f0f070501c0c2495005401286901007400031841101c0007841207186070000b101a140361280000e41e881c040c403640505106000a10382640e03c400c140d01a01841e00440301668824801074210000d141c1103d00c0700024050344000304041e0914000c4034242504894107201e0713503140f0b400304035100c207050080f01c55000b010f000d0b04001410911005000f400786010024044500784c04d5840328030001c0300075100700404040c2141d0081c4688050710780312002034031300c20000e01040c03000c14a0f20268014081c41d46215000018016602154540c00d58540c2c0e585a950728a003044194141c2c020108100045643c50b10b101c446 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 728053947 1250 728052697 728052707
    0x3030405060702060f0409020d050901050f04060f021b030403030809070f090203060f04051302010e03070e0a0c03091a0a0b27190606180806040302120309010204090c03020d0605120c01 81
    0x1d00007484c0d1464840030010040484e4025485445016000b040c0b000341c2d00c881e40304041d4041200c0340213004518200ca0848811600140001c000a03a241c2d94503100701c074558103940041c603207480300d02404540f244825981e500a44400c40004100e80001400c4800c08240c080446100340d410506407810910301c0806500300606450b0003400710080150380f03503a0340c000c0c00c1c0a02081411004041c0490000611200204a4883c040e50150204000102804400d5503000c4030461001800121142d000c83c00f0740500c050103480c5225101c00007001ca081c002da1280241490b03001044120b5801082c8403c5840000202c2c541c00600300c52951a440c0700904158060325100d140e40c80503070030b140780c40121519600300100050051000d1003517080c401e1075242c05070510f80014400362609503002903959002c551881911907011010a4a00009406903409005c1103003041c0300c1001c4111b002402508868540103211303040010025403802c1108207001850000c0001c1c0c82921040001920 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 728055197 1250 728053947 728053957
    0x3050703020309040504110a15140d0603020315010810060b0a0804030311030c09120102030f0115050903030d020d1803020705100e1503191b0c081b060a0f06050303040506 75
    0x10a50008003c2e03000b1680c0d6a201c1c2901c00e0f07100708070701e103003080207401400070b2048070303400c010011140b00c40035600c1d842d0060700b95402c40100c0008140d0b90044158542c001c4c0a072a40000c0d0144140c07052007030001211482103041c0c41c080701c2100d40c0c844407000d4103015124a40314400307483d0004c00840008034402d88090740c0c458041d0074040341c44100140140e0041c0d0003111458a007060209005a8524204442c0d0220311229002036040d824440111400504103100d49181d079450045412140c2d80070388240d8507c1039000341500d4a40131242c010f50040d42c06013584108880c60203c100350780d100039103010290f1a42603401450035a04100034005400d40701c041480078031011180c800c500356a4030b021f00600e00e5000a015880341402042604190110f0401009486c01c1a00882410b4070703504800880803450724000110100c1d60500300160702c00c0c144240c2c0d20020180050400c0440060214041c1d48070240400110020b0084241283c80314098158140c10421003004a4a0b28a020304 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 728056447 1250 728055197 728055203
    0x3131512090f060504110d1514040215030403020f030309010c030b031915060512010207030305100b0f280306030b13050c0909011806061e0303020d03052a07140c0904030507 76
    0x240c1c00d031b81200080c2400070001ca04403202009181702092a010a000380d400300459000082c0807420a40e00150a82010040d1840c41c02c00100004080c14800c0201608004a070801d07a562800c081e107200d4084c00ba21010031011031b0501c08912a58207000030008540801e9509400c5018103941d41e5800d06003030b0816801e651a101c0401040540c1c074511070310b8022084000059540e14a0701e0080c05480008040c864007641200d0f0812480304207404886600e610311040d141d41d450000c2c60780c0d403240d0641120795040c1d092a039003450035942680c0b100c5c0c1524010010b658a0350b4601d0320345041c0426240000700303142c00065071709089040000e03649030403403034210001c1024080f8454210303e01203051026200c2644642003000032200c43c07458000c03c0c50fa01d4103010091815074501950b40d5000308502400c0640d6400001c03c051600d044010424201d030406c403030210741030020341d203d9421040d0301751010001041d046540c5400001c614842a4001e800c81840382e5a944064481c0d401c00c0d2426 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 728057553 1106 728056447 728056463
    0x40b01060504080717030d050c0a1e020309090907080f1501080109020a14040605040606020309090a02090904080304061407120f0506010504050d0503131512090f060504 74
    0x108094821044607045170041100302c5500c2e45c8030340c0140b001d880c1d1502050140340aa650000d06810b62185c1d00d403c140640701461001e203103940c20500000d03030f1081041c100241060260954170800d00b03003d45140554500803541804034070402d440e8190401e00c3c41007400c000c1186131a02400880b0000c101001440e4049031500c0e141d07020340e2801050004002c00203a5454011001412001c1c100b40701e242c1c0e407001e010359640c00c4070f0503203071203401c0ca840042c1900f1030b680309482800c031000b0030fa00c5183c0c6494441e05181e90010b0810f888060b1513580c50419082c0c101d2806002c0c1c48039607260380034503000360a0301c0b085415001c05c00c10390340d00304010320615a92081c1590f040d42e0044a04801851503403400c03914522500000901030b10740740714005411180b40ca620b000305d000fa6190740503450440d910b0601120003c1e4002040c810340d03003800402240c0b01e5403056a0061082c80c5c8 = true := by decide +kernel

theorem cover : BRFrame.Cov 727877697 728057553 := by
  have h0 := BRFrame.cov_init 727877697
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 727877697 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 727877697 ≤ n) (h2 : n < 728057553) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
