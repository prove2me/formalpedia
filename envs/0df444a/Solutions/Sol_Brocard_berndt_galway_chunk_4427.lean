-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4427
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:34:52.276983+00:00
-- url     : https://prove2.me/submissions/9e33a801-1fcd-4b29-80d0-aa1f768f0681

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 796043165 ≤ n < 796223021 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 796044415 1250 796043165 796043191
    0x1b0403020d0519051e03160b04030c080f1b03030601090e0601210c0306060c05121804050a05150d151d0601030602070201031107051506040f06170114 66
    0x80103040103241112268011820399a203250a000015480d020684003101c443d00504001c00e4000314608151402d17981410040d42411550340c007080d00300884990140031003440300000340c1018450010740000c5503000340425140c0d0414456102290440300e01e007019010206a41c122003840003003602e10610050b582c2590052415940404129010300664100f220340c0900346800118003152491120700310a001034900b140410040855070f064008400f001400c513010404104001280b14900301303c0c07171002c0e03038a145100c0880f5104005a11154101e410b21b4100000c43d03800d0740c0514419070041c0c6440364400d001004105000319200d02c010f20071410107503040314040b62588004003074180801110722031003020300d18515054090344100c90682c1c0008034101103590601a9030030141d031801c040c81c14109107a5605486a40140480c9403040501002039010307034130307500551140b460a68041203200d45070703586000c0c04256502400d40f41c1d82000c169650522100441c0d13071203850450202 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 796045665 1250 796044415 796044419
    0x12030408120301080106060c240b0604030302031903050408040e06130f0209031002130e0c0705030c0f0d03020703090504150b04080703030201050f0609040f06230a0e0d05030c0d140c030f1b04 84
    0x21a41c0800c0c1c0300081030714075652b032080810a4403080000c0003c4c500a030015074a5a0050280f4810111030907803180c10542440140000509900240d6003540c40340d503048031081c1d80d107102042c10100d181204a40c010300300888075140403c9039009042c0008142c094504018841006005a100d41380b9041c6148030358560070031000681c0c50341282c120000c40b03070451800165440b41840c40c0c00100d2001c4164001e80c03401c20390000c0800c40207104201c01d040550506d5121b031800782c02070310309226540c09507444440704a034101a0400d41c074050045410000c0c1c5035034032100306650741c0400380822009503107030034082114590103512462285200510501a941e10b603595140c01c642d21003000c40b0650b403540d1080c0c0e50780a40290310f02010040c5a050070380f0b4070308130400c070042d580030f80c00941c12500700e43c0f080e0401907401000c1302c0e80038000300c07401c43e83d42a280c81d401d8002c02c0c0c01803050094105e07071030074840080110750007140540c08910801d01c03561a1000c4072080b81c0d1540150b2105d400c0c0030001 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 796046915 1250 796045665 796045703
    0x6010f050a030f11061306410c060c0901090f15030203070201150305030c0c040213031118090a0b0609240303070f0f0b01050a0e0714041d01030b071d12030408120301080106060c 78
    0x41c1d407450515234950713904002042d03c402c0e29080c81038645450311000803620070b29a5034086d000b4401491500da6050605140c5100c05000700c801d02084c0c4c042640020000f180036000750052484a140f80c0c0408080c20754904005860350002410798586010f0800480c003030786854002d5540c546003000703072050000c0c40c0d983c03945490901002d0745500a00500184441c9140d5101e26510030000840076080081d03a503d80311103240320080401d84905840030502241d601c120042250118042d0f044008000c4101d000924600480c5e40082c0074460240e0780004212030445400d111600c42c580c00c030b1150741c075102000010b0b501030090758603590aaa000410140c41441102c08055000d56206d00c1c20740c40b50404203240021480104c00c603d16070004004001e203400e44c0661114092424078a001d002199a00540c00c1604030035101c0e5881501d04020858280100c80041629000301d03804042095000b01007034000748940c91032940703082c6001680c00e00444081d0b40042c0d0151403540c0e5807402c051 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 796048165 1250 796046915 796047017
    0x3090b090103110d0e060a090f0b07021c03020409060902070b1609120f020306390408070608040314090604030b04060b030303010605090306010f050a030f11061306 72
    0x3040504041d2250301462610100200502e0001300811000c6a4501d004070900d18005001e820a4110340c030b07003c41c03440441c200c6610302c0c180541c0702c03c80c4403554555120892901501303501840241c6c0744c2000f0480040d800d54024000c030340c10340c803061001564810001c41280101980a4620000c0800003070318081245400c002c90407850401880b0380e80c070f40750032004240020750300f01d910960a000c04010751804001c45940030144081d01c04807000704031a01e2801e0b400d05424042103030b0450b545800b94541c00010b45001d003461104070f41c1100c3d0354241c010000481510f09030b000c14076a1103900034040d940303021550390440203041d003450585540c0e11070341e0621008000350344282d40d07a403600500396010302c02103008080c0d6075a01ea0321000da94041504080060340029049856404100516190710425104690304560814020030351814440c28004542d0426544404e002403058042280c15049405a40c03c40d13440c0c0d226078641008081c2007506008521011014840c3d0302c82c200304401c8 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 796049415 1250 796048165 796048177
    0x5030307140c010903030f14090304060e03010e01020c07170f030f070213090b1008060105030c1c06090f1a0907051306050d11100801150e1c0b2203090b 67
    0x40c078041c0c40d1209405855085458001c0c2c01c40c00680c031814040b170f0351820760149420356035000c41315800c9401e081000700d80e0b81c4202c3c403440052003d640c0c0310000aa5080d0701548075000c0410082d5500c5601000075a00e56145020b100710128141140c2c543c4007100290040d050750780721000318940542c001480340b15821800c0100c3c0d00110881c60348107001158022820f0700b40c4110740f260480d050a00752200a884650848641c95110b080100119640040c2c001e6000390161240904941456604802519480d4000c0d004074142000c000c00c02c410540841c43c01d80c02089400310180c016a10032030824425922100e8a40c0700450900c91850081c04072401c800c0e07a0180000c0c082d56403404100498584c19050f100c00340b28510300d031031074200300310f903424084040d01e03100c03071550305040034200c00e00914040c00c000c10000e00c1070310705640c44142c800c11690104c0b82c0e0106500f4410f1070042c41c0700c501141c40c01d111444140781d48500c2603820445400059140d03c170585802c3c2030140c43c841e190040 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 796050665 1250 796049415 796049447
    0xc080d0516020f0d05060114010c030e0f0f0d0c05040f06060e10120e03071407030b07050c0c09131a0c0409111312120905011d0d1b0f050d05030307 65
    0xa60200c3c0700303550ba15006030740284c8110302401c0d07698507040784400e9601c6080d043ca414042005400c000080c0e0090889000e10f0040b240700b8501044800801c401c0442035403c690000c5800a10030240106440307201d003103440c02c07142800051001100082650490701c140b90100300000e030928403614054021146a80c03131482c000001e004024292010b40d030045401d410960070001302030341448a10301d8002440c000140c010301043c1c5c0342d540d5160aa4900808040070803001080e001d103100c0f800e1090060854004107624014109544541e4050083c0c9804403000005c903000790a541c040d0000a0380700b8a094a001420a0724102c60a009014101c01c034240c0d60108000750000c2c40c901d10b80c924080d181c815512130740742181d468039501c0d48100c440c1280030302c44503e8042109a80c406211803001000d4075854910350b501e47d002c03901003005048014611121100f500a030842000d42c3d2200b21420001e0308811940e40e102072140e02d621585025000350070400c0040d460741d005040c441c01400d030b1 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 796051915 1250 796050665 796050679
    0x11030f0d0b371a1e04140a080307050d050f040509070504090b030604021c050309040c020606011101180206180904240608030f030402012006010905090d09060806010504031a040c080d051602 83
    0x303250411400b40d105400844203882d60070446d1455050200603200600032030401549082a0b0741c035400c1d5910b1000d003a8030200400007036051078030300340c08081e41c006050240a18900f400c04580252194100703000d02e0070440c0c0b5184050003107140000300d0a0045402070b0242440d0007441411076600313486520709460622040003840500d46540c490309101040b0342e400780c98603041c280001040e0460008040780700ba81070000c0c03d031603144e00740ea200c442e548d4100d8000c0c1d40c1e00004101000c19011b0340c010558000c0100040009100e800c1c1407034003039040440c0565410b041c2c44540304c0111041d501500740c941d803003400403400040405000b560001d0050400d0302d06080030b001d02d110401f0415940c50002d030005401000064224028150045a14000351000000000d802410ba2249120f08001c0145850100307406074000d070b040340c02075500310744261620180e211a180384243d099808032841c880600f030000d402e19011404c00400d10043c0d8030030749003818003581120841085502a130b40414 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 796053165 1250 796051915 796051957
    0x3030306170c0a060347270a06080d0914180c030c090a0308190e1c0303060503011802090606070312110d09050607020d11030f0d0b371a 60
    0xd0380380b04200444585c0301c070306d40100c1c1d803041c1c010f080c00c030040c0d000350080c42a840030382208148502c0300405540015409822039481c00c2414010717203502d5010710307024041e60703030011079942d40b000c00a0150354080d8200446100e182c01489841d004d40589460583c0c0300c03d02090010300d03248002c6401420804485050203004000211850941ea20403181070b540001e06c910513080c006440b0303000410301d05001c8483d96100d40400c8005904046114a04078401051400c01d030007903002034050701d8050001c000e004046016203412021780d8606902c111034a0002030f4440c034241044620880d41551801900c504903c2002c001d4070301a00c11a100c0b0700c1c1070002c0c5201000d14898281e840b80130780003e05c46400d2520000c1d007080ca2100302d4204200504004010398480001200d50b90245c5011190f46c5285541c0400014915101e4071603009440d501400d8013a40348c0c0c00281017407003009685024100c044001c1d442030200c13522642034140c0b042101c04205540e004003030301042e8000d03c070546140c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 796054415 1250 796053165 796053221
    0xd0603060204060f1d0109050108091006062f0c01050c0a15020d0f0902090c07020a03080a050a0908010c02100207110d06050a1d07032a03030306170c0a0603 69
    0x1030069007200d000100c92414110009500090400d03040b02a0400001c4d405c101800003400500940203190600c5180d002080800700c041001d640c1c8000c28143c00c1002c0380c0c0b0f40380001c10030300c4480d14100c101d402c0b09120b001003c1030340017004c50f9604001e0080c10340e204035500640301500b0000c9440c1840c006c51101c0310110340340103540c0004d52000100180d980f442e40c0040408c551043d40009903d501d8481d00000607218a0300c4c040c4c01c4825041d4094842d481440061005509900020811000402d80f030007850340140251049510a884403e01161101102801c8403040c12079200140e00200700e01e501d10101754010700c0d44a0080217104001c0313500f00d01080c0380d41e1845d5412a100c0e5981c00030481c107046503101e4814552400324024403200b03c0110015a038161a00010303000c0141c41c000801c0401031550f0010369101084141c940c1282c1c0c1e03040290080a0511a2044e8640495003c424000c00891080c40e0140d000f01120005070030034038201c006003107952490511800321003150a502c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 796055665 1250 796054415 796054417
    0x1b081305010c0c20030a1407080703051e0609210c030a02101b05090906031e070f0f0b19030b0d051c1407151401031b080d0905060d06030602 62
    0x507412544605030300e040e0928268030704d050b0504400d4041c61400000d21081e03640456189503141c1c001c003203191501454817a181c248800c41d4400021841076141c0082080000705a0602c0e9060310100200c8180e2542c4d151500c0303107000c03a52581c0c41c1c0c20103007074440e00340c5429a03412911041c204507a403c040904825924542c080c20001000d680086145c001c111b4881c001c00018103120544c1803e01c070540384000d0124043d0044480c071030001080050710035103040180c14120b00c0b4074585280191110808036465000c1c50143d60000070940e2408254500300c40c0c20a000c4030801c039080c5207818080410000c04180000010341015111554980345a03a400107010000c0d0155000c1c081111040c20b06c1c0365121920b90f110350074407116404513000b038220b00c015101e1aa4100f036000761501c00c4252001c00502218003100900d0000c01c0c004003d00c414250010007528200c81c90709617554499001030b81d17070341041560301d0004a140600340318505040d8090480c1114448021460b0f5840e130f5940810707 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 796056915 1250 796055665 796055681
    0x6020a080d09060c020f010e030c0a0201110109120c120e0105030610030b03060a020d0b040c140f0403061a1e0a051c020a0b090a15080a0902011205010b0c101b08130501 74
    0x5034040488805508001c8c4100319070224600021442c18001141b003030f031a08212200a81848402451000c0c400001c0d04a01503440d0f100d1240c8a0074148418094070031001d0903019903420305040d1095502038021901d0180a82d4141c4a4604540c0e5100030407500504146019041649030121000680c504025840c001d603400c502c0580c480c41c800d0540412aa0b040300118812400c03d2840304a2a0700415140c0c240350008520359992215503241c0d002601c555400146031030320702000640d1181d111480404519000c132503000504003a541141030ba99170542d1101c0c1d020459420030131040ca0917501050446003c801c0215000d2001d0300060310910b10f60b8170000d0003800001d04600b040c5460045000079203821100c040c4031405c4900300412a480050140171919602c0b0a03110541e8007456401c04d101e030503030100748040d6868464070440341d0082c10740c3c1701e21480742003040c518511250040043d2803500c1c0c00c16580110650100b01c0d06100050800f0310042900300f00400451800c2c0a4008 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 796058165 1250 796056915 796056917
    0xd050601091b0806060405060c19030306090507210209030c19060207050109081f1b0c020f061813090f0506090624090c04120b0f06030706020a080d09060c 68
    0x285881c180392101d00d82003000c20b07410104003180d0200107290f580c000555045e14030a8401507220b80c85008824038000700e00403001641030107410040f040541c560054016503088d50300900c9540c0b2807510540d00e480d40c075180d166240306050f4206603c50074650140000e040e0040403680c00710801804220140c940d400901040c0810764003d01c103841e0104540c100404003031820a03640343ca4103024548800481030035a446800900c0004068410742c1c01c03081044a805481d00312501003c0800303480e00b090160f04034081c5015210807061031400c40309880c800380107402044529402c0d41d08202d172994480401c3c8c0c0c070a613911300c610070100d0518900c1122083c4a03d0044c01e040c14a0b0071501e01d0000000d2100b42c1c071400c0d02c0034070303003400141c0e000b0418641d80951300c00343e064803041d140814a0140b50407500c604034580100109022613255801c0c0240180b41c8a072016807034000500d522020240120340c01343e0310506903400082d44c80c50060031030300c0d10104000f540c803ca640d521001c1d600e000030701c40 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 796059415 1250 796058165 796058171
    0x20301030204061203140a030605060c0d1d060702042003040b010f150e040b01090302030d050d050109141b071a07020d0305040c1403030408030a110d210b0d05060109 73
    0x2104504091143c00c0c00b4000d030084182c8a64580da40c01070001001076044d84000c3c06c0450f1400340c080c0260000d9010b420b0041115881c0c0f0b0a00c5103130365891515090ba200003c001d540c46d40401c0144e8103482540340c802900d03161501c0c1040e028040500042660041103a050340ea800c1c404200d00c40103580182d108a0a408e081d51415003400c0348044541c1080b4400205510005060340e0004204190301c04280c8000c0365480400300141c0d000a00c99202a405005410000060581c05002803500d0704000b0010401c0e80d0f03c462182040f11402c202e801060303070100e404100c003026485005104c0c0594900040d241c0000340e5508424024401d0782d26201c40108401e01245540500c02c26102c0141850b041201e440c0c1603d4840b99040380d8420000c5146180703e41e8503498500b401210058008a000c03a9034440c50458011321411410000d0822400346410302401288241c0031911480000e090310228070b494489810002e0018408040e03101007425610342c00103406004950080c21401c07000 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 796060665 1250 796059415 796059419
    0x11090406060c15060513051302130c140705060c030613060e010509060904050a1214040f151d100516032102040e0412021504080a122d11070303020301 66
    0x883d0003500b1011031098210700b4128144607503211480c0425550206500c0450a034550a10860b40381001c2c1001a40040c002040c04980c00d05076000050880035503554400392503100240c0d4903070383c007070488024226000b0002107985245201d02a40d00710b01c1c014402d0590743c002802c20381c101ca0107984035820f07100031600104024a007105005501c4103040e20400560321306a0390303280e105e42000400408103d4969101507038684031340401d2101c4400ca040c1107558684681103841140d000d48180c4a0481d0a070b0b1030945030920601c4200e200315071f801c06880281e8a171004100d0103003902a00c02c03040100c01e22483e000d1031503031120001118000c1c1c03a8954aa104400241110b160040207469002c0c0104400c12120940d6010b90b0391150700a00c1f4a241c070012220100e040040b100c411044c0e101c3c402c41803000f4442084002c001c5c5c46c1081d140c00024100c4c045120099904072001b2101ca807684102440400e492481550103000140c0c800041180c1852064169a041100d055002945c04001 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 796061915 1250 796060665 796060673
    0x100f030f0b060103021908100b040e01032607120507060207060507030e010204150e180405061608130b13050106172a120a02060a050a1808070911090406060c 69
    0x1c06500608203280079840e0916008150a101d25a000040e04101c608000039100c1150342807404050032240c3e1b00159120742d1070554186484003030200762000c05544030025030954000706184040d84640f0030742410080c6603200d040042d0796040c1220f00f4404208541400a081c620060203258440d450005242c10504d0000341103c4805100360101d0303104000c1445020043d04c00094480450710705408464001404200c1381019000741070344482215050100300580811110712525000340018028440144121510201070350b5241c41d042c000c0c01c0c0b190101e9280042140d012001421680803101a5581ea508440707095210140218500c2914044030000340004081c1440c1c035040e01000c09070114480c59000903440081e44075030540e200207040c04405108402025400030062a1501c51959024103140d00041d00d0800140700707510080c020850f440800c2d4250f403a144c00030b0554600b07000c503000c0107082509529401240920007405646e031240110000341480d41d8488400d50070380d00d8 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 796063165 1250 796061915 796061933
    0x4050a0c030e0f030f090604050411030103290105131409210711060703180323150103060b06090301050108030a020706080f041203090b100e010605090f09100f030f 72
    0x5400708064000010005001c0d100005491505c030a090f0704c43c0d40c80c0301440000307407244110f9000d030341c100d418444003900a11060340614101c03801240d050781031643c018203100d58425030840c401c085240e0040184114201500c02c403100303a29200b40042d499405480c888510340702100d00c0f181da60300402d01011480a13991003a000e003072a010130541020115511030114445461019000b2640810001c00b403511441c0c1d42202a1090a051414aa10313401d1420081140c500c1c2c01d4940c8034200240d1140700000a09001a4030540c1d43c03e00059085681d03e5024041050083da8864014880d4001a41d4288a080e00070507620f00116982d484000002c0e092100d182e01070300921070742c40c042100da155a1126160b10a5110100049203960768206030300901d1900c9024007046041003c100482da50849140c096038958140140c0b00e07a81c42c0300032a43c9110b140080c17034020348040c141d084682800006150803084140b2942d64440d11801000c0814109a0040d291b1030407003a5500280a040c0c1 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 796064415 1250 796063165 796063181
    0x20915190905120703020f0a030b0907080d0c020108240a0b0c01110a1d150d090320100b030a1712060d0803010302060c0f030408071a0a0e10030b04050a0c03 69
    0x10f201a20f6000c0032032516902d0b01d03000e00c0080d0042c05480c000342e215a8400005034040d50b4050320b8040c907030406550042e0f5554160150400900c1840400d5607103500440d020350b021035059540c0c0d029a9200b001862841041540f148245851500d47c26026504c610400d0040e0044400180c0c0f614011303503c050035034520344032000c04610f0400102d001c01c6c0e40a100b0941104002e2144580302c1e1f17a02010814440c0341c05800300e50345034040340500f28421685c200705880c1e8002d945003a4028141c020102400c4070000c03201c1420b5200c4410701c0a407203e84d4001c52a0400010180c42c85000282c5801c0130b0380360b403036010035503c6400141c154070781e8400c90005600140300f40c0c1c0350300c1824000d0b076a108040c4410f001c068441c0401084441c01e80004002c1803c210401005030b80d21141d48004141d5203510a01404913084c0a0a03100c194100350681562030641e0540e95070151102c01d41d0501101c05000078002081507203400d040700d4162218021240036500081d400202c043c081040182162210 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 796065665 1250 796064415 796064419
    0x5032e090f09261e07150605011107060503150f0a06020c0a080109120806030c0d0b0a0c080603030d0b060c03030c18010c030f0f020a150501140303041206020915190905 74
    0x1070700401964200d207105a41d20400d621500d0703200c205004c0c075a403181e0b005007400104644401e0b15080d00c2c80149801c0030342124400c2c1caa046520000b030303070280c0e298140703802840c002031000e00002d15800c0351300300116103885001e001c00440c00198000706020486540012000d42e100340d00a00e01401c000520710020030191008206400e510f50381c0b040d441c1650300400040104000c04500c05039414131060b00d008400406001d600e10144c5030080c0d804404461490880d481c0c003d04c1c00600e80100c2d10076108040044c043d514051800c0304c6000108500907846070050070512012990301d800300000e40c02100780c4440d59880d0b2206200b1400f402500c40e403841d040144112100700004d401007191400c29803241050038104459450032468150406005001c0d20f0411540740f000d02c125a200a06803185800901011018401456a24030451240794003211140705040040791269025000500004100400d982540784d40c11401d030304070b80e110714040702da4030805a88072034010322404010802 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 796066915 1250 796065665 796065713
    0xd0e010204053a0c0801050a0e0609032805120f0603101407030f0b0319050606030a02010206130809131506021605060705031207020d03060605032e090f09 68
    0x544043c0000a12807020b0440c484040310703201049588000c100c003400d01038000304224900070b042900a0000b404508086000d1a030128014100102c201c13082c0c1000d13070b000d4410120700e490401c20307000d0701400d411717080000c14000c03825040745070701c101401002c103c0b030700c000b560a0003010141090140e81844079040d1404500d49000780031000541d0740b100700b6041c005420f1000080903005410200a07140e814020f80d081004a011284180b2030b18a0068080360403a580b40d00034969035241070000a400f42e448003000811001c000c010100010340301c1e034006414101d9410115141100d1403030400100c1c0e890f2106c240c2031008402d000703401084544000c062240001422034440d000c00d0003214000c40d0009912000d22204000b260350402d480d10983c0c030180742241c8000c0d114043e85000c400044d051140024101d842801528007070290807640c4100e00c0030341e801c00d04400498940040c14403e40f0503001446003103a11030181c06078016840402ca4082901d070a103c0641100d070000c00104c9 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 796068165 1250 796066915 796066969
    0x100503060a060e15371e0201090c090c030506040c0905060711030105040804090e010c08221211101109060901110a05012c07030611040b220605090f150d0e01020405 72
    0x113404440072006d1090404142c400c06c1c24960200d02600086102600b103400403c070000e4980290744c429500031a40c2c0d6800c000540f920002c00080e18104214540001c0c00588180803624111008202592103400ca4411000104e000300c1c0c00d441d81190250b420030004a010003a82c0f03014091260040341c6080200300d40364820f803002d80400c0c400351483c0441c020703038050244040b90854101d17924641010715100c00c050300c07803402400d01c0b4030074400d81000d0003200c00c9010390075111b0140c3c0c0070000201c40114140041c0d4428415260031070035240c1c2c100106c0b916003100e141018040b00d0002c60080002251900401d001803c12000b1700000c4a520406410305800690b40400e56205880c0c0c0100d000c41c03887c40a0052102030b01603034100d10080e1000040304d00080e02c244c08a040316510704000da4254980d170b441c00f941c46000f01e18246030801d0f40c012010810f49000403407910400180c4100c0360402869040c418101c441d89a40d2540310380d40094207001524000a14022030005843c407503203044 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 796069415 1250 796068165 796068167
    0xe13060c0f022e020d02030115050c030a18050618040b0111070e10080f0d140304021c020103060b0a0905030708160e100b0f0702100503060a060e1537 66
    0x21490300842c0b540442080c6200203c030b10b0401140404400c02c210641d210019146070400075402841611010000380b482607807058000e4040e41c9250120303a0203941060902036040c2d40391800107003400e0304c00d0300010340800c4542d10358001e0032a07a0384501d0140b00882a0406000448a182075450305100c42d041c1e04408141c400903800099030f089040f2149540ca4000103511003c0d2650000101c034081d00624507010f40c2d000501002d0641c82d6910540740c583c200c10a40b0b0944405d035400381d00415105484442c1d001901c620018441c030614001032003070b03510489412a40c00800d40350001070a8104208880d1030200004000303032010a02030403a00440300300000fa92841885a102c003d640072000900c01c81540b1801402028841c1805503966017106200d5115440707207104034440e80d0480007180c0007620501c2501c0c890440a44455001c0742006010f5915182c000f04066000350100304081078200c2000c040c0000a00342c5007100b01000d0400904001e000d4031070300454200e40b0703003003401d4512 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 796070665 1250 796069415 796069423
    0x1050d0f0f020301141605040b030705091f0c050606040b06122206050717070f030e0111070506010602070e2502030d150611120703180e13060c0f02 65
    0x11a40311a000d104000c00c0c0c0780c107880090810401a5040d485c0c2030000d028000c10300042441501c555210141c0f04c181d104c8140c5083c010350203007a205034006d0000441c2280540020201d01c0b800400304000c2c0c41c204c00c14610840349403081103000841c2800c00f0002c0000800540b504408210307018041a450230020034201e015a035a006c10008440020618182800f5081540302c41c1c88500081d080c481c908200300542819180d80300000c24103165a0031016a4410850080500740d8800c0000800008220041e0850721807004d0555a9040d143d8100c0120030001d002880c440d00207040158909a001303400d0050961103811a940b042080226a114132280b080340b00b40e00303510700c40c21958416800c80c1f440c0141d0a4081d07801d0b26001c80f002c800503d030310700042101c581c0d90300d0741d1010190014040d01c407003081d180a90700310000d00021000900a490b90340311040c0000c900c1144950700c122038620f843e801d03140342c403941d00d043c03a48005111207800390f40a0134440c0c0c20071401010710800c000b591 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 796071915 1250 796070665 796070689
    0x91203120a022b022116030507090b160203370309181b0c02061213120302030a05131115160516120b01120503070b0a0b0a0b030105 58
    0x41c0c40e4005000710001900c1c0911481d03100300c803000f000c0360040201e00c0d2802075020306524407803540001c8178004510b1010b10307254450346c0520007118140203525415000f90601030001e5003072024101c0007145594030500a4950f0144140300b00452000c503005150500100701400c06100450b589401951400380008035144503150540c00c400310100e00707044800b24400c0d04403034040c1c3c440008004a083c1213802031060300280c040130300303d00c0c1400c0400b5244c0301201c8034000d4210800748069000b40c800360a01a5120315276500c0c1c00845195a9141201550841132200109a02005001d900113039440745a501030a443d02c003018943e104e4845102c840c1f00e070f0f03e54a106040001880c4482d90013001628900425072101200f0013900f40b401c1d684a100001e04201d02110282000800403001c2910200280d0000707500b080036401d00c240000841445030040e9014402080710500058010348124490b110602c0d0002d01100030320204840720401d54440741c00c00d001840103000c15640d144807041 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 796073165 1250 796071915 796071931
    0x801050d140304030c180c0201061202040f110c0f01060f180209010909110c10020906070b090705031608060601030b010210021e07030c03020d030501030c120305130b09120312 77
    0x1035601050301c50034610300c2641c20041c0554044600000c408490341541c50302900d205100740a0000000340481c220340c05403007071181d59084152100c0140c01c0981c05450b00100c43c41011401c0284140d10260550000105241070342c805d00c00c5681c602000e10815029109030409144c4140c80d003404002c4000e01040c1c0104040d03800600e401c411386c00303448c4170b40082079203540604c13109083c41710030340d0340f80c1185141803664010501c01072200d02451088542c440390080005040c40c0c400e8036400200741c401020140e80d4070614a0204081e5820021000b101c6004d4060701d2003103040420035402c1003000340c80309040c141000075000c0d183e0b80101e080b05441d010140c0060315400c54aa000d9203502000c20105c1a000340051020103040c8d220403140c40180c0250229084103441c800e0842c111a024800034240711280102805031110464010701d04602920f800c5081c148048196400d40019500440149900240303d6940e410300501c1440381c15440c201860a1003d00c047c400d8141500500d050 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 796074415 1250 796073165 796073183
    0x3040b03090c10030b0307060315090b030a0f050303010f0608060a030b070e1e01180e0a0b01030f0203071107151209030203040b0f0702011e020a150f1a100801050d 72
    0x2400060308000d0360805070b000070800c501211903484082c00404900358001d001c0c0c001c002000c21500c0c06401051461220441c42d10b0989141420100003001e00c5500d03240d00d40990181d01002c01d6110207c01c5146006201442c0d83c2e514015011641000d581e000c44207100c1000b04106681d1703a40034003170381241d40000c1d1030b1a50750b441910450340c030b0048803501d641c0068a10740c8d046074061075440c1c0c444000000c3e02d540c911800b0f400030349a2810142d00c10100086500d030700040210980303130490f50a40c0e10605010507003440898018041e60811141040000d0101842c959040020003d0200515000072a40048940900d0062021405070400141c003900c0d22552010988200100c0c1d00401101c01ca15440b01d00007400180c49621841d01640064405004d0403d07601c0e030f80041d41d11401858008000003005d995940c4490002107000c440703810fa44c2c0340c0303080d100c2d520b6010707480700500d1000c01c15510300c42c2c0c08208800310049410300000c00444100600183e15070b0111800250b421000c1c2c0 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 796075665 1250 796074415 796074421
    0x7050a03120f11070b03090f06091b03030f07060902010e1c030e240a030f060e040f0c080609070e090309010806092d0603010f0c08011806030605010806040b1803040b03 74
    0x81c2d550f024030050200d2a07214020780001d5a0010310043c0d030203802060151213580e600200500d07940c02041e200010243c0056401c00040c0c20004000a650031001d400e480c00c20300c0d68143c0d025a500f04040c181c81c3c4940701c400d102e0466a01c200007002505003110006690001c000e01c039550241d00d05001401d000740054528015030310310148041903d0072801c50b110a1807007095003011604180c3d800e41c042400d1141880e402a243e004940c10b4401440703206100342e4a5851b0078856805580741a83d2110385900c0100d0100e40600c8107134411501c840051805501d401c0c40c15080c0b1100400c18800368005008021080c0e0744800e01e16045501120704c1c84882c0c84200114079900312500400000c0c88000c2180c02c1350444a410351882080700310020845042d90403203039815030724001c0c0c000740068094001800090358110700307590310755031070000050de82d80c40760740d81d204848003070300061016440b80c0100710030000101007241e400f105100030b00c410010140300c03aa6032800b82d400b441c0c100e40008000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 796076915 1250 796075665 796075667
    0xb0d030c05010f3c051321080c300114090603070302010305091c0906090608040c0b0a0203040314031b0f0a0b06011b0c050111030c07052e1107050a03120f 68
    0x101d4200036141350010003103818508040c90100c1079010040700d10390108111300081c804e680c1c03085061141d032902c070039010740d0310601c02c01100d620500c140148265140c905c091411402c8040d0204d44011606156044d410008079118049100302c01e00e2062502d2000c100c85a28007146031f00460b5421700303010500c0c2d1106680c0c2401c0c0720300f08901e01d081800d042159401180d12942c020116816a200c0d40c082d40d823076207011241c003001101c000c0c10301d51500c942041408045c1c001094100028030659003459203907902d56003500c061400440e5682d10100300700249544240c1140300c9170412100506000f0300c51180c0715141e61015601508403a21200040d9142e40030380410411040d01d21598490381d9101d01e80030380c01a406004141c00501010045ca41501d00001190801d40c4540011b0440619090420040042e80d4014000109021449100340010641003880340300150f215a5004800785c858145040b8035030b4000d078400c140c954801c001141d05028201111030707040c50b00c00c10809072460 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 796078165 1250 796076915 796077011
    0xb0609061b190f03091a0a08180706050c0d050c0d0503060a0b030901020c0616140702031c27060509130e06010602011a030705061c0b0d030c05010f 65
    0x2d000d42280d4a20034201c82041482d4004540700e0b8801c2c2c49120503e91101d007030b090006414566015920020001011083e0191013281c0d07000900e01424507010b00c2c000745650400a541c1d003d08080703040410a01c1c00858144844161301001d442c09604002442e1051070361043c5000d90701c024400300001040d80c03915103004400182080d41c030f009603030f410401642c43c002c2d440300ea040c00c06400b829001c00c42d808030742001c480000a0310340e1003400c1042452a050400c1c4e000d0982240c0c14071138918284403503125140996141c00d03068840d02c0245407200002d0444405000c9031703403008408140c09201658000c000c0e6054560103552101b0081015207590000b440120764042c44c500c68a000016a41d42c150400c150045601d5801820b540524041c140c0d200b041d4010164840418045d4074000400343c2c0c0c00c02c0e003402039094041032010301800860004100d403181540012404401d840500109019144c002c03252664100075564488045500c0392044520f038400c040b00b1046011280322a0324 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 796079415 1250 796078165 796078183
    0x904021f020316030801030201120b03120d0b040e070e2d04150e010f150b0d0c0c060608060a050c19050f0408061519230d1b090b0609061b 61
    0x4020f041d82207019040c042c00c0c00c403092202301e000071650804180b404116010b03035102c0782d901600401380000442c0c80e4201c250085250080c00b140e8940c00307240c1039030740c9000d4406040c0b03039a00501519030920b0448517900100800e007a800703030039080458520400d01c1e0030412001c4c4000e000c4409503159440e0880d846595034010542d0303d030a0140000d0151010362101040f019040c038104951001209101c403941c541d0721409039510f4050007601c9920410360050480c2c9001c501e0301d1680d0310290b6031240304581403500310009550124040140c00a02441100d80000c1c07803030340540c10600719490ac481c1a9403c0441403007084004a0302505801050f002e40e000b0f4a04d05050351f84515152a00c00140007415503524410000f2440f000d0072028008800001e44a06034801007000524450010003000e0001c00b0030703040189804540e010509105c04160001d20b510480300c089450980c120b4182c4c7d1280403002c1c86800204100303801943c6100840d1000044000640f259200c180c51240c00d0101c06 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 796080665 1250 796079415 796079437
    0x910050c1b060a1b0518040b1309020f01090320010306080106061214070203040e060a03060e0c030c0a05030706140d1d010c0806131802130b010e0904021f0203 70
    0x4140707441225100031950b644190f541c4042004100310092007008542405150180800c208000101113040008101020341d540a0008192030110034045034107000311500d840c10f0140e031059400308500e42015001c00d95042480c0c500d64031401c0d619600407403800e510503803800d0400100d02c0d001d282d000b80c10040007002d40600800c01c440d941d43c0050600601c1c00380c0560624501518207c0010b84441c0715030159010f64021402d0030f08216002c1c0e271122011304115070080203031f80008001010350084110241c2c0c20405413405500000c2814500680001114410000c0c0ea100b0302094900003a810221130441c0b5081e51070316040340b0700030302e248107200000403070b030742089070101c0840d80e21149110350811220007040046c2e0498411240d44406580f240e0344000f0303405681c05e94041d136810404e0482112500031150030500d45c009040d0018011550701c0a644410004c2280d6821a50318500d8440665440c140303450240e000030180c620400d084090310340320920f0800c40c1071082003618820844 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 796081915 1250 796080665 796080697
    0x3210d1a0603222108060303072118090207022409010c02130903020a02030706030606210209180901111612021207150b030d120f0212011701140910050c 67
    0x200318503911304451816425000c51102000710f0224203002044680b020340000014a04100200903030350403000b000c40300304c100841006c010013050140300c00100100224100140c5d940e80c24418400c42c0e13a008c0012408000d4840340c2c4000050440c01298448042442d0000302c0b01c2051001070240e20240c80030200e41890080d00400301a00001c0c200240c5000718100c4083c5941c81000700c054a882d4042d0000040d203007403882c410510100760301d480b4921a45405420022110080b4601d0b40d403003128004525403400603c11440028400c00e4040c601c41e0710110700d840503042540464012140009202102c80c4041d488080d20a2184241079800e016480360344450a04144c420503c1045803c04401c2c6800c102c4280341c900010f8602c118565600d0301810410b12110800c001e11441140c40312003502042103060302e90311390b002d80340a04000c548050741c140c1030504407821240509000d0100e51380100602440e000001145161301c040c601c0d000c100c547c1c4e403000c41d04060040101c00301308204 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 796083165 1250 796081915 796081943
    0x150901090605031b03010f05090c03090c1c2111010903090b09030715080402090f0601080610140d060f12080d0b061b0f0d0801060c1103210d1a060322 66
    0x124815030102200c06c01c407510300107511212210308151200b330b07840340c4039035001006900141c00c110a0003444003c1c815a50b00c0b031061551241c1c0406610418920b4035142c0c081d441e052025048002c0c08100f00e016002000079610755a00030740800d5080c000d281ea102c2010440c11091303a402c00141c4082c0a480450380d0302d0882e0307000042d00d040c00c00e035003c0344201403641c0081e42c66400c6840c03036031142d5016526403e164455805004041e00d4920301001000715060486050008000c02003117084035525001540c0d918000c80540301500d01d4000d405040103904032000800c5040c0d003074504003041c41800049442c20750b000240d540c0300d1159070039000c42c0103480c00c40d0040404030703c04070782c20840750a550f03400140f20f0040340d040302d0034003401021590b0111000c000c502e0044400c400b801016040b640c224245504081040c0800d03c95002c00b1000042d595080021038090740840c4610881e50148038031f4001b0000c2c2c0c03640070050150040024505602084030320010070b00d20b105800000111041c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 796084415 1250 796083165 796083179
    0x3071b2a090b04050712090609050706050a0206010b0901230405030709140a0509100b0103090c0e040302100c020a030c020102250f050f0618030708061005150901090605031b0301 78
    0xc032407050a01d142e203080303094041d506041c0100d610031682c40e40d45501590f58681408018030b1121030580d0b1700390792180144c000400400c07162014041640710640c5501350828001d1400b03805030050440d8042c18017140d022030340c00c001d50707089003100d501d21580080d2480382d01d180c05011b55440503a0502c6170040c00100040580d001c850620340560076001540e0700d400740b45043d00c606903030320f98013540159008070480500360310800c01070310145008213919503152111480341c040c0d90024560354440b80180010590100100c5444c1c030b0749480107104070424800080d450f84180c3c5005800e010500812204580c8203205a1a0860443c40c500401110261010304070102034003032251121804400841d852400340b14000389100c00501d40c510381081f40ea201d24211348c060480700d405205000000c00e1941084c001c0a1048480b41016401c242c07900081021034412407190740c40150b81088081c1c1640d81c44001002174039610705100d66240c4803066400001d490406803c090143c010001017580 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 796085665 1250 796084415 796084493
    0x1306031716052a01030c020604030e06040b0417070609032a1716080c0619090e0403080a0507170f060a090c032405061b1203010e040201021203071b 65
    0x301040c83d180041101000c005400b1203c450842101513442180010002441180c0350400c01c08081c084604143e40c03241c0000c095041a04448000300c81b00500b00200301041148800a11a91030119200d51035510f4a8643c910f078259416440c030202040070140b54aa11101c200910440500001c4805944003840d281c0400700b00700713a44d10130078000002d007840707000410308620500140010b140402caa0641520f640e0600072841c244610500001441340e02d2682e10b07442030340651266075507894502c0d0445d0407540001c1030a010301500480304028a06025190780d0f00024503003149020b500c5210019019012a40c4080809030030003150780555036050f00040340c00b00355402944080300408818a40610440c040c103130300082c1c02c1c0842600e1010944440d08583d02030020740d0001030b94114042c1040d03109030008603d4800030b00a120440d40d04110008180e808985202d0550819801c001c0a000c0e030403007290009102c0740480e200b032010003000b01900c54400d1b04618840103901c2d41e00c0ea91 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 796086915 1250 796085665 796085713
    0x1303050a0c06020127050f0601060809010b0103141801111308060c0c2a13021207020f0d140d02030916290a2606130603171605 56
    0xd0754501800159403401409003100c940491002c80e040d81940f0348100c2c103801c801c210151042c0c81003001c1110305460034000203011b010942c2e2441003500c0c160762198250b800441101e810907280c0b441d80c5014107000c051113500a844803100ca0b021880441256016001d190744003000402c001442e50380e8004084004400c9070090400e5503034556030102d407003146008202001400782c120380c80140c0100c5d003e092844107000d400400061200090020030f0555054680013040281d0000d005c1e68000f510042d002e500000620060180c414131034186070302c40c0b41c4d02078500103000d20421194010100c21094851805142d0821912031822090041c0e980e104032424042e0b42c60b64200104080c030000a0300c0d40000640092003008107129101451280d0280001804021800c50407070070394000100c041d1010040384c04a00e840d420712004109140e54807a810006092030000d08000142080d804444030b0000b4140868541c12a01043c282c00c0c107442074001d180d805080e8006412115820003942 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 796088165 1250 796086915 796086923
    0xc1406090d18050901090908040b0408070518070e060a031103040b0f070203040b39060712090c03200a0e042603060405060103061d0402040e030906040e0406021303050a 74
    0x41d20b0030101ea04291042402074542051802d00140110200b903040b04404074810412280703025924006480250025000401541c12140c0d081015244c814041d40c5040784292103210b031403d21160207001030914a10032801140042034080d0314034003c1e441036051840c2f0740c1c03d0540c1e0b89032502e0140202041124a6015602d0410100c1d002c10310000595017940c0040401e9460810403024484010050410580c4201100c4104000384c440d48240300e02d000341f2040061013241051700c400307800800d01c007441010803442c1c03004c8940804c0311441c00703604898000108007d4000001480062070084400c00c54100014050000c1d501840d0151144581d0042d00d161514030b80c82c240322103407080118420380e1107850074408142c452030039600c100e412503014100007400030fa4039080d0b207411041685000c0b14000400781004150b0600b401100d0380c0141100245180450603000070303407a030081d80a5008440107180029040115540c12549030381101010003266660302d2800f82e94031a4409400c417 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 796089415 1250 796088165 796088177
    0xa09151505150f1b0a0f03021b010518011805040501180b0303070b04031b17040e0114010206220204050a050a0f0501050a060509012309150304020102030a0c1406090d 73
    0x582c6407282c1e10143c41c10f8800500026140100c8661070484a0904004a40c502d008080c4541e000600c1c600800c440a4840c0d009803010b01700403c80d007508000b1401010b03060040c00c01441c18181e60412420310082000d091490030300144401100d0f1043e52034000c55005490100041a12150202005025110307200180f100483c0ca01c20300d6200c1c01007103402080e00907100049000070b801000b41146012040700c80e9032071300503d9240c80c2e48044284048280503a0001030174040013507400d0b0002e02400003c81c9000c1242078142c0002c2d602c21008001d6a1002c1d82942131824801c040d1a105d110541c00070700510642c200120b803000240019580d40d904076191080f002e60ba080346015080c103c0e50005c0c030520310355150880c02da68a81c4800311250401c42c0200c1422500c1d502200718140c40500900b4407a10b489901003400f0308030103400c0d002d007000c0009004101c0140c1e800021140240400d290009491181d072911041c14410405403038000e004480400507681000580c803a440c40140d03031a0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 796090665 1250 796089415 796089439
    0xf05041b090603020d02041a10030c09050f15030c0f0703021605040e1b1c06060314070b0a031104211b181109120a0213060605030a09151505 62
    0x12804030b07032181c40002e4100c2502c1111001600e4107600c10a6210004204801001100d10000b8041c0d800034041c080802d076101264201580c2c80003014000d03200940d0b010754064410800110b08107041036550401100000000301002000800e03030341c03c600702e00b0019858010600e4040c1d15504103000c1c081000d00c1e01040000c9500d400e024003520035a951001e4007000140008000e0031600c0c0604a40c1c102d51851510502e40c0403000c00708211901440c800544a803d52030541e1401c0c544040300500f91303200c000b060140d40c03c40011a1401d01c85400e0014400c0903240305211540100d03403002026100b024207100c0b40c9000f0603424403a880c454829000071609021100840403128014012048442044510400c0b07503540001000da81900c40709081001910000d4070450071b02e492001e45401110703411045003000502409603803012681406074a04000340100b281c0001001000c0694580c0b0325041031020444a200400700d01c41000d0185119030030341811108142e104003030081d0b00210103 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 796091915 1250 796090665 796090679
    0x30309061311010c053405090c0301090c0c02041b021606090b0708090d150b04020304111c05100c090801020708031305100216030e03010c0f11010f05041b 68
    0x680ca5090742d10600c030840030440200111071640e035004080301c0368410200403c841a12280070340c0c020301c5180002000d025003c0780e4031101e66025070300c01d03400f9114180510407903a80c1c0b0000c0da03055170b40803000041c02501c101003c82d00040010341c040d410a1410001c3ca440504420642d60500d1641c1c0850b806071b01c0031181d50354a12007500c03600d000940500d0040c05000c3d4140c008100c064055802c2500345400c1c200003641490200030226250b515001c0024010b04070360042e540f01c580300b150114190703c7c290300c900b1036a443d45803030180b080510a003104401c0c551040401d8059404c6030031982410043c141150041881c00d4028000c80d5240700c0c006101c003014000c90b81503590200c8a00d06545070135071202440c000300074003129940944440648064082c0c03000d045010b020400701000e03210941005090030320075512081c000c0e4188500100d05c80d80101940740021158686181010b10810006005046034112000e01d60304010520003840000d04c4940b4440780c200d40030401e49503032303086 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 796093165 1250 796091915 796091941
    0x30a0e060907050a0b0f0906040914070305040c050105160c060818060126120d06170d0c1103150c03070f09060f03090807051f060902070302100504050f0d0203030906 73
    0x109995001068130024012206000d01420001c0045001142000f05250020714641c1081c2c015181e0140c0e2011508100c41c41000d2894010206041c108441d09081c3c41d03142900e00540540da040c800c001448010100b030280120103000d1308090318801007926000014107100c4141d800b200328a2111038180c07201c0c0400301d051030480749021645a0450b0003241080c841030f01d403803041421800f944c0c000401080e44440241140c4041600c00905941040550341058071903199000160b4861504014059001240c1151190304036503070003550a0010700007486c020350710402600d40303400001403100701e040d1140518051b0031907450704000c0d450b06510454a0b5441d43c400c4c00001003081c0400c0c112030b4002d6101e108000d0141003054070341200c5031145c0d403a04240c0700a0804128502c2009040c1b154140304041c040e0800030815442c100300e40e10000c0d900c020f000482e880c601d40d0391000c5400c00c42c0810600942c8400c52050341d480b2a026a0080d40366002114420340d1402004e0002c1c2110799821 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 796094415 1250 796093165 796093169
    0x1030c05010212070f0c0503031308010606110c090c0d06030501020403111f05030a110412031409030c09090f1203090105010603091e0611040b092b14010b06030a0e060907 75
    0x400c60f5410b02e000340c1c9450304960040700c070a4070903480b80d000104181e14240020250740405c8030b0407007025440d102e0074500311003d580c082070800140628480d03034004c1c04a0314180d4a2401c0780ea400d5940ca510740300e044c1e2441144840c150603440c1c15000810008190090411a4081e000d01d0541340720400c18010407506c04c9400907142d0307441640307807169903000d43c028581007048464000f604541080d86003169a015400611080c25021040000c01d5402140d01d138035030001c485640e08080c42c83c80483d54661140c510148108400800101e420604000072201e03424408210340300000000c51100c800d900a5902c211254200400450402d004c2d000b11a14181d000146200d402c4031900d900301402c00403181283d6803500c880c01c1c0110704c0c5005000d00040c11000c01200d680f020f5440401000d0702d04400305190726851840d00301d00308111003440e070051903040b11180a11a4100850500424148214030b41c800340100612040066035809032048003c000110340140d10340000d0265030310313024 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 796095665 1250 796094415 796094443
    0x409080708030c1215120703030206061e03060a200304030804120c020904050c01031a03100903020a080304150c031a0609010908120d152301050409021201030c050102 73
    0x40000c000050850390040d0750000380c0c0841941072401070301c0880924902a034100f4001003140d4000d21841c039102100440504840d0010704006103580c1d03020751205001084180300ba240c81840441c0356030009502d5581c81401010754240d4607014803940000d000240149401d0186502d20f103e4084646040345d00a039059203e84446948655a481c1ea80b40034820002c01c008040e00084012388070b0b00441400382d4803d8002d070045004a60006046607500c2c040441c04c0580c8139810801618081004c043c050142070000c21150071505050349880e5201a00402110f40002080184031007602e90000715001c0c10350501130549181130031016120010008101d51300145254000d52819100515103924181023002d80141c8da4089241041d007100c2018070642000034040c0c0040ca00f9115140c144120100c80e03070003441c200440e14144480728819010141c4241c00000180d83c000c0e0140c80040140d00000d650310380c100340302a000601e0a120407944216030b0740010a44d5030000c20391108007240 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 796096915 1250 796095665 796095667
    0x70f090e0a0f020307020f0115120b04080c070b0703020d050c0c091032090c030406110f0c150a0c050715090f1a060901050108010315270b06040908 65
    0x30312150380d5a591000d06550400c0e41e9800322900150b4050002d144110b05540141904451590006003501c04803450415444c14410307050200003e6008554807558116004440d140d6441c40c2c08001c9204100c4018010701c201e40f40015008034000040040398441c0d1b0a44038161824607003680c941c01a20711810745a0000f0014504c01d041640145501c40b200c0201003500b81c0d40c40c2505807584444a140018880000740582d010032080c03100031003d0794040d10846401e01d0311201c1c00c402400045c0005002948072030007012050340d400151074a80050000c4d2a41c3c404d003607d201c90f62061611102e002e20074005000506144092180740000e01141c0c681901d0407001c0c0c0c0e40d85807050303482a182100c2c156031b0f8548101241070316030081902c0740318801f821806c2c50320300000d0640344401049607200d0074580c0c00501050744d00281041c1140d0780694124060700328200007001400560810340c6a048002001d900100c45204850748042c0c0601c4103c5210345508003070005450303004802620000b0 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 796098165 1250 796096915 796096919
    0x509041203090201031407050d060f0503150403050c06070f020d02011406010e04090803180f010c02030a0f0225090e062707120f02090703020a0906030515040e0105070206070f09 78
    0x4002d0300481410391051400050303450401e0501000a141a80c202c07001039004900d1070079100d02449450094002c90034440561860100003a559031160792514103140303c200b0124003094010010f698101920400b6100310386040200142803200040d00c03040144165280c080c44207006110344691140c802c5144102581c60a00640e24842418609a0031681c0c031541da50104103a400518000d480c281c0710b16142055410b500b510b001040035201c2d020b80d03d4a040700c02075540000c11101408054100103c40120003081a42010f44500c855500c40550303400c01c0600004000605041d00d6441004100644125846581d506030856000c5d008541d07080400d0038401480b100d80c0b486000c000d0446600c207072541e440c1074203d149102e0071a507440396510000114a4907118090707010249240441c20a2903511000300040e01d40d10540c02070607a684085403001c1580c00d94640065005130091040c050301440300d82c000c10302250314000500407240451041c0b40b1900861031855400d0b51201d083c54 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 796099415 1250 796098165 796098167
    0x230a03020105042901032415050f10020d03110d020c011d0a0b042015070501111215011b050c1e0907030e0304030606080d080601050319020d27030905090412 69
    0x81180c102040850a80441030141101c15004003135448206007211700d48e0324075000c10300405031141c0052511581c0303147d141150750707507000602140943c100d01e00030400300e00748840104039125400500b600980000741d0310034005015044003500e01034120001c9107001c0582003107501c50a03a2680242001030361004640400c011905080440d03a070032005161003a2241d0000b0a40c0400038071080e050200414200305201b004c1c400e143d8056050402c0518140c03844050340d0f2500c0b0010070380d80c800b0a80c000301034210b911440101c400302d0440101a40481c0a5040907940d0700f28080040c0c0c030445110030b02c040d98030f103441030030100003001130030441032506c81140c254040e0244414403405480207110000204405028600080402c60003a040f00500540010078880d8002c001034103220b420000d01104445801c95a00c00344440d01c80141c0b00d21602100300c02800b0b405400b507048405180f010200c1d00600524915064820f86039200555510002d00c103200c20100c0f00509a1603003101019101 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 796100665 1250 796099415 796099433
    0x6030c0d03080c13060c05070608060f0402071703070c0219030f02360f07030501030804090e0c0d060c0f0309050604030305060f0a06080702100e0703230a0302010504290103 76
    0x202c00795031101d0500000b00d07004c90302001c040c4d000000040250582c0403e108043c0f10043c003401d91032400303115034509500401ea02e03035080315045002c0d541c0002c04900b44040d0496110f00c0c00e03034540d0400e03500d0801400080001d070307411030705070b100c0c988104081294180d4a0504004c50390700035039000142c0419000c20210040d44080800804820040b224440307c240c0e2a625051074250034400f01c0c0e040842020940c24001001c001c1030510b405c00600c049080802035404580384800c010441c0b032000d1411078100260000c805401840d40a06003082100c190004a2608001d680e5100607410540088055803075148004d0301c1a0004cad004100400d100c0e40100da840303000a404080f07400300f01d07404074051061070307409400001c0e80c510a12040c96818400850b0f00300c0001c0051081104246078035403102454403006043c540c1024607a107c0a844c4140d0400c0c1c0304504080e2a01040305003006400392000300d5045403024005403100e001ca62145039000195000500340c1100d036070840c0e50b40264 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 796101915 1250 796100665 796100671
    0xb0a030f050411191d041e0f022709010225081903060e0a060305010b03030c0717162706081e010216051b0103020c19020a09051e06030c0d0308 63
    0x2c801c0d680b0101080085217403101e04120034030711429418520b05403c04020007005205040c110038030048601012907901344462000d280c040380d1080e0403501c1a2a1440d80c00340c1e4206292103007413004104001c400c0103602412a244000400491817a14030301841c0802c1281ca200034030840d41070017070b500c0001e8082d09246c2112494280011441d450348102c6894040441c3c4403c101901c43c0c5051003000402c0c040c03114180030903401541441d601c4004640c4425a40c0602c030f14030b08416408405042003007001109600003d07444140305034945002c0c1b807111610f02da0070070b500e00f1440c03d4505800141d22036042251080005404c40c020039a815000201d400c3d40e00b1000b664080c4142403001c132100d415102d809210300001c00300501d80c0d00181d00208106240070b41451700c184441014203101040c018040300e9641c0016458070040c0c0300081284040c3d4009099040c507040411a13501034001c03554520324401070303001000c3d0365043d0800d40d68540d0b1a4000d500510170080d0480001d01038070032150 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 796103165 1250 796101915 796101949
    0x1006090b0603161b060e0708010b0f0112060506121012020a0621050c090a08010504032010060b0901181404020d090b090106031a0106091203050d060b0a030f050411 72
    0x82020001001c030200301001413000d851080d500d1001110249080000c200100342c3d43c0d00038000155204001240e07503400800c0e075414494a03089a8071404140d42c03100028003801840d1649866070b124000300808000ca400c2018040ea4032004114070300041031090405a00425004c502c0c2e041c96400c130f034105030070400c0342200d540c00a021507001c440c0780176442c421088038000540380c035040c84c10020803c0f0550b011308550b914260034000401c3e07114103082c034000088031018400b2035200510529209480c03550020051424201107030265856004002c1500c5c00d80e940300618841020704a0741240b20b03c58103086803409001719400b03040030b801801402202090005440301507440b4010354a10445104610340d41d6003400307004018400c144418541c8442e84503942035070400c1c00192000c502d50041c40030f401800c0c0c03424401c06110345c080b41c48180c00e114040c0089541e56001c04850b800c09100440800c0c00d10030350403c080091f200d594401c0d41c205200c4a03202d0b00d500240102c0c3e03e07020020607 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 796104415 1250 796103165 796103177
    0x3030b2809020a03200c01060e01030804171516030b030606090103170f1306020111030f07050306060f0a0c0308010617010e150a03150b0a03050a140715021006090b060316 75
    0x400314071200805020102e4110740560742d034006c250050b0031104103030043c80100460400500115030380c0015107003580c0c1d01440c1a030b0700c2034500703485c5840c182098502c2072603e4034440400c2002407a2048444071100070340c4041c0103248002c4101030b00d800040703811540200181c401040410b0740001000c0714149a004a80c0c0782c212200016501c95101d02c6081032074042c4100c0802c5890b41c2485070102c0d05e004440c42c2c50550800e20b2841c01030f940d02800a03410040c020022030001c0d55840b0032580b13001203040b000742d80c0c0c500b01d0001030503000d1282e03c00c1c3e0120f5100c0000040b010700612000c080000310a9203801960300306201701c0104d80c070207040500040d41604516a06032916102140514090380c0c08400717442012442c041a07812682e41071307028100c916010000187c0010b003412525a00c040d500404080769400f60385000d146501c0400880325008490700c0b0581c001c00e5141138141c054105205094640f680c41003a6000d51420340e40045042000a0b120300c40c2e0100014181601c1c5810 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 796105665 1250 796104415 796104431
    0x40f050603060f092a04290a0e19140a060f0e0111070f0e101e090c0c06020a0e0102011521030309050105070306090b0118060e06040509010303030b2809020a03 70
    0x4603112610f0701460903605100006c09004502001072000c0f00041810310a035440c2d400245801050700400c0001024045030002c02402da964010209001404080c3c1d024a441d80d546031180020326559440c90080070098000700c1e402d84540700d10b44540c2c016884110300303058480c00440307030920400700305a258014841c0c0414295103c144541c01004014450b200605000200503504121940a1240038400925064004411508401c112150040001001003002a05947d001200c0e40010001440051241d482a030806550310112000307038020040714480a204052100c8107009003030300b171481c1403c40c1c0e141d6900d400b48404001e100345008150041c0307959500307094407420740c0c18801082d10f4410500c4113004a100f880c40000d02440e244c07020341d03410010784044000a010b29400c02865284007011a2284000c460060001038140501c640c0d44e424003d004101102000d4422507503884101500740084d4003a2407008204880000210301d0300720311000070740c842210f040905803101e000d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 796106915 1250 796105665 796105711
    0x804050f0f040237021002030903070c09270b040204020309120a020a17180f060f0705070f0e0705190e030f0c01080a0e0a061d0a0602040f050603060f09 67
    0x1d4280600c101a030200c4d4603201003804441d072a100d200700c2001018200510b94510ba00050090342d40a5602006030707a620303503080b024150f1184142c00740c00c1c0755041c00001502c9207107a010901b060707001e018140900044d0711488020020054000d0b00e007a0300714000c03501501d800d500540e0440030301744c11903009407942d50700701c90907420a01c1d901c805a085a41d00c0003d0010044820b1007034980e10084501e8944043c8150040d03482c500c81d0070f40140c0c403000341d032500c60310b03400116510104c42c03d600d1a00c2e03480302d01d451651082c0a008134911090150400036004000c40010340c0100b1690303c03190304125075281e000d00c1c0b081d00c0e0382c0200b082015000d04c4003007a4034280240303460329070402c0c06410007269040014100c010b0240a029181d03190070069a95000c01113545d12001e0b40c04030300440d03034000c1d1400c0c1c611108101c01014215010706509001001304c5640200201c41d04404144046a03079441001742c01c0c0012100306421005c004440541ea19180407950350140c41e00344400400035140740f0b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 796108165 1250 796106915 796106917
    0x80a0504120c0602010c211a030307110a060f0c06020d0612121d100e1f0525020a0501050d060803160302070e041e1e0c0e10030804050f0f0402 63
    0x1501c01402c0c80c04140245682070080180b004141e052024074010203650440200b400c4017081c0c8415a90b07140c4171000459241c030890749960000f800c803615090b65041506001d07800601c0035202d0400850001501c50080000f080070b07590035200c440002071240c4500d0042e46c061400c08001c03030340d101e60109020038198108482c2c94082c03080c90321141c100074409080550a4540d6080030000c529440c0352917651110041c030554260301d8240c0c2c583c003071100811f401c8143c3c08010300c0c050204007444100300394414058400951880d001110001c0c4158a5542542101c0e002035000802840d091021794010740040c04141c8115000044090f610382c18207046401420000c0c1204612480300c60505030704000788006000c000814042c1400e1a0382d80f1f50000107040c840d11403020703185000c0001d000b5034001480d0308110710081c8120381c800c00d190070818100e070f0340034104c4500d4881d40032580c01e401e40403400d0256903202e050365192900700001c01004520005c002540b18620400752161501d0301c2c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 796109415 1250 796108165 796108199
    0x40b04060c020103180503040b0f0f041d0109020415110a0b040c05040e06131e0b100303080f0f010512071206050103020307170327030307050a030e010509030703080a0504 75
    0x70750340115014035440010700307550403482096408205000d4130070205c1e10200c1101c084941914113a940c485000d0302e84510b60290000c507003107000f00032030001030522680c03901c281124040040a03172241c2c0c86000703030003c9006d2030040c08d500303c0e515204048418060b028110745001c044084074541d003100d41c1d410700071520441e821552540d84103c10002070419003d03003801038000c0005480c5038a0880f13124401c801d0008000b502d40340343c8844084004203100a42008143c00103004085803412000075070034034021303110440004007140300141010b40c0d40d85907030b80900c16400120805901c0c20040041030100030ba00d580e01c3d406035000004092075002901c68150303100d4070340404d40758950300415060074044e5210399061021074102903e0074001004680581c40b0003030720140035507880c0090704000c111854100b0381610000895505200c00080c41182c02d0b0b01c02d9482030035018502e401142d080c000c0841803601588201000d10000d802031000e040120a5031800ca401d0964914140f0b031044540 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 796110665 1250 796109415 796109417
    0x5031c0f05190f0e01022109040902130c08060609091b13260c130915050408030411040e03070303020d0e070609170105011d040302010f0c03020c150c120a02040b0406 73
    0x42005101034942001e83c580004d0380174005041070a090000e2041201d40b09900452032210000c2c56180341d03522940288005600a020a4142085151008010f0164050013030101e40c085d0b0010394549400c10468030180340144c06400607844810150210f1200a220441c802c801440a000c40010301c80d1000010200e011080b580b0480301c0050843c07070340c40c000d602c004581044501560750740380c4420b81c0820010700030000940d24518188002c3d001800343c40c251400341800d09203c01e10802e40083c501885c052520300300d003a80700b441004110790942da0521103030f810a00414001c20300a90241c4005100c1140102c3c1d42c0e40e031708189a041c10220340050000c078040c41814000d442c02510500310750310704680208420750400300e007903649943c82407a103401100e01c04000340030135100307412007404104010b4080c00411050240a0301941022500b140940b10b45d40400104a13020200c180c0900d6007944824a0309441203002d00440500408144902d0340800c000907940c42075000030301c002e007a5 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 796111915 1250 796110665 796110677
    0xc12140d0e13021201061808071202040b042013030506010b0c060108060105030705060711102006040b0403030921180803031006050306041d0708060105031c0f0519 72
    0x410307000c0185a00050901c12440b07841440401d02c0c0c0caa03002d91444c103580b0141800c03104a4203e803661480300f80541c120400f5401080d4000595038900880c4845040c801c0f5000c0c0440120301041c08212280740d40c2c0542c2da104503c140c1002402500c009180d0110300402a074155503e9803240e501c0c00e81c080e80b04200e000e40024460030400c0050100c1c9024040311400740c070081d454000043d0346da2005005080c425080007510f0301c10000414403e103418400504080d4600c07120101c05003106031003510f0b8001207100301c414150a030a02140661155520010010b202c0e1219101100284420a011103555804450000103540c0782d039801032894095980f03d80d00d88a84650000308403c079a80596801d91051003444030180d142c0f01300c601030324075600c0c02c240c5a0341c42c40b00050260000188851610103200c5084017038540201c0d2100580700b0950403100b141e6a0390040c980d844a41c0d280c6802078411065200802c244070352400c1c0f000d4180b0340740541c10205094440100002e60481e00b4000c104 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 796113165 1250 796111915 796111937
    0x80615031306140912090619030f0c140d021303020303030115090501091d07021603060207110303091c02030c101d0f0a0608090106080a1a0a05040c12140d 68
    0xa243c0c080c403103815281c03000310303405030404004c940e40d03c5000703c4950b0941d01000c0350301c0c005902c459084e40c0d581d2002507224507419000c000c01030010491002545d08842c1484900758426000d641501140c0d08040d044a06d42003040f1805d100070740000290004041111030000b01503a4100080d41c0a40941e0185502803503050030041c00a10381e070740c0928107001c40c800d41000011400e0484956040c005441d0b00302503a40d802d401c0b03051880d41c81928030f4484600001009121a036405022b999200c0d81c400044000c214080581d0f0b4042c550b1025800701e070044040c1030060b00b0f0490740c4509480981200d410502513000283d0748529248a03100060035403545a076501c01c00c0b000d52086502c160b940b01801001000402c00e00d015078001c0d5018000f100c1c001c1240080d00354050001042d542003580c400b03c1e46850040c00009124074807017882425003021074204c0d01140318880c01a988803d042101510700398028251f10380e800410340340c001e10180d10b10094001444111005003099855100a074 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 796114415 1250 796113165 796113173
    0x203040e0a0504080f070c08011805100b0a060c0512031e0709050306070513030f08070b0f0115120f0f0501210f24020f0325020703030806150313 64
    0x2440c02803440c0206800c102c20700000c15850800c4460382000816881d940f003070241003030120340805600000d405c0d03203002081120f00ca0070035601d8002c644550240c80d94071110119001c1500c1d6110715082e8440c28821042000b2401605130f408003e202d01c058860320010044140c4207900103c0d04054855842c11003104c031604c583d03026a13400f081c94103200621504000c0803130b546800043c90380050040004481c03c3d1600c66490300801964040086c1b414201c1e0783c80c25a1040d00001404c540c1c0d0141c580c04951303180e003010703005810303036052a074036000a41d80340d2421100a0360010205107819640c03075009032800d030703a40207100034059000c20101c0c095140135403820300040c1d00700071541844040360f044400100c8941100000580101811105504e00d41c44910741ca0028100e20810300d1000640354511200c62001e9445844200d041c50701148008443e491610441002c42c03005821003001800000d0040000b660007401c041c5c041440703880513500c95103140d03100b62a1160b030446609603030b03c208 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 796115665 1250 796114415 796114439
    0x6050a050103110303160813080a0f061515050706060b0d0b030706020a030504030210030e03030f010806010e010303020a03080c04090906090b0c041d06031c0e090105030105100905060f040606020304 87
    0xd032030284e004502e400c90511641c0c0d0520001c92000341203550009002212149849161025281c004265010034503a0f1502070194400780f0400c95221381408049844001d21200d0141151a07000c155200c401d0b81c1042160f856204040888110b1354440b00414031b50308420180c01d44da121800001048400b0200705490030041d40e005004641c0900c008800280c0e125050b10112981a40c00d000414031480c801d5000c0c6c403400103078044d544004400c0010390024125464100c1e0018815038003da40c81d00030040c1414024000031b03001d64400c030810360001c0e11441100c0d502c4441400303400c0c06d10307840301b0040d01611100d580c00e07151203454013440d80600c055a940c40707402864034486945002c2c41e02c21407400c802c2e20140303800009a007040000b19035880c10b1000b4030030240c0039007251510051480010300711723140c1d0b03115150049400c00c0003c955420148070b00c1d40203240010070840400d2a12200760081c200c020143c13038000440d00c1e41130410f0344850190b4005801250082e6413503d09007150181304c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 796116915 1250 796115665 796115693
    0x301050c16030c02040e01050f0406060803071a040c030507080307110a08120d06050603160e040903021b1512060127030818030d0201050702010b04020c0d0c0c0306050a050103 77
    0x51080104100d10403496401020203000c0d80c50f00b0410920211400044c0040041c41c2645ca669424130702004506440d40311102d00c141e104190402c556030b21801c0766913490249500051911851000916454141040da81c0d8414400c0d4500b84c50345441e0f640303d6040000b1a03114207050b80c004140c0c0310403c00c0400e8100c42001c0706565502c1010b103400040b81c0c1d6844042400c04014000054447c0b203240c0a801c2070000d0030340070b4021079403402e250f105c0446014444a40b14001b900700f80980340c00c0c0ca00b50041c08409600b5500030031407103592511140c01a2138940700254001074107104000f0001c0c07030802403c81c60300340c82030722300c440d00d020000540700c04180044510080101c016003d912042d81c501d005c181e031b8200ca500c0e0744840c40b100d00c0782c0344914100780d03066052250361032000049a0541001d480744400b41e0081c80a28815010b11050340511514032441d40c110b110201800780c8070f10500c1a406000741b07004a4080c3da41c1d16440c04444080d14198803441e02d96006200741716151054100e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 796118165 1250 796116915 796116931
    0xb0c0106140a0501140d0e07050f03010911040e0a1506031101081029160302010c090b0306060c031303030e030d0c050303070c06020918040b010e04020d080307021c0e030105 76
    0x10a0341e9400050401c4499005031814040d800b5801e4888030300c18803c0c1c40a102201d14100300944002000980c1e070f5415100d090301c1108082c03102d00240c2818000c503503059921041d500b81003450741081101600a0203140310281c8151750090340810f0f4141104481a00465000154a81141040d04030110540059410700c08190b050195219030b40c8145800c48280302203644003200c43e0b0003c054818442010f01002d0b01c00825004400402d00c1c0042000e036200360020008240c446000761040e4040e44a1360008a100784006a0302d81000e1004200391884541928604242c0c40d250201100d01500190300080e030721809071000c0c0c1410041001c0d07211032070030101d00112043d9204c507038074071004001d4010814003d0f18482004840c0e0166200f1040013001645000300e140420241902d0071241621490405000022140149078400b8081c0c0d4000d042001c0782c44031b41e1201c00c1d443d4400360180c011071140c1003440882460744400308182500e259521a1032456030400c140c01d55002400c100 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 796119415 1250 796118165 796118189
    0x3040b0a05070f030903032d051f03020114090d050f10021204060b0120010f0b0f0906090c04181a0316120305040b0d020a090605090901060e040e070b0c0106 69
    0x1c40c0403900310407801c01d0403c41c0d03c0c000c00c1215440c0307407c50144c040c070710103000c3d14280e00d0302d400380c41301160007040280890141c0070022503560320101d4503801d100d08851003480c00300c0706042c4059442000c0c2d000030034050405281c90710310080082148540d8941090796035800c40c50900c02d801c1c0d42440303110700340640340c44c056003001402804604000400740c002451156940c2410829900400c409599844106032098048001c050254007070000c880055000a26098001c512403805040c1100c500c24041c160884960707170b038814007800590160401090032070501001600e00e0702d40c50170803000034981724042480508884048a104d80c1030164030b00c81d4000c821a480c1c01c9626641041c2100c058150280310400d55041c20b030b801c0d1155400071802c1d9200003d00d002000c170306400521180f241130351607a03129030343c0d440d080790386000d101c0f25607a00149142c0108600c610803121920403442c010300025455900744203c82c9400415801460940d0011440511b1a902817190000610b80c0084e40 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 796120665 1250 796119415 796119421
    0x6200915030601210b10020313062d0e010305152b0b0103120906050a05041217070c050a08010902090a0c02010e070f03120f02031603020f030a0503040b0a05 69
    0x2910990940100c50890800070001440e80e80c401c01d51048104203800c20184c00e401c5091a03407020300303140d040c550701809a80c9941c0203498400030841d4a810394034101000c0e05800c01c002100d082290400e502c0916940c008244908950381d00b00346d0400c05203440303504109042800150903564004c010480c14800c815014581e61070742c50300c0d55203141881c1140d0301c0e954074070111500c240b109950040c10004412001204100c0300101098960200b51621138140e65919002c448520600c40c0350800540284000c2113134010b29118210100e1040c50900842c7c54130728107120b07842d04a1281a0382e00c000e01c0318100020705144110381302a0440000038040468960081001c03108050000c14440b56548240c20b1a14400c1d403100550508003429200c09070368800c40c0340c2c0c50040a01098500c86c1d1102508044680101c640b810841e859801440c2043c2454244410704442c02d042602540140680e0662a0748140700410f44001103894454032800e15013005100ca1400500c002400d610300014 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 796121915 1250 796120665 796120669
    0xf041a090a0311030f120907050306190903050f0c01020325050f16020405090f010b01051e070f06021303200604030b091c030e0d030b09180f060103062009 68
    0x207002145500760910000c0700c442c000d0100d1452103034508540c0300704030205134400f410004500300c1c0c1c01080f283c011680800d4a4078201602c91038107a920b009041480d680740c8004403075980181418600074101a030030800b084c1d4403031005e45d100706902d80170b81c1d600104206c98441c508000c5022015807024064004051020103040c0b4490384d028917540e00000306080c101c070400c50700046249507000d8410b100382e04003048619a42c51080907160781c01d5003406803c40a65101d001a13404810398400c1c82c0c4484060200007482607071000400b5202c801d500d8412201090a500060641660b900040c03600d041c5103082ca11500f02644141c9858071541b003c00d05001e03510582500c09407a00022604240e0320f400c00100c3c541010031400b0307910340303c2c910348500b0441e80681c881c150180668080c7c4011280110040303089401e58140140c2c45609903001c143c54000340745068580001d101c04640043c05500e600b2450f100090b401103919a40341c0c045600481d00b14000d401c110f40103100d0361070034003c00c100 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 796123165 1250 796121915 796121923
    0x31a0403120b12030d020a020706171302121c090501170a0b060d05090d110c011d010e0a03110a08120f07080909070306050a0f0b0921060f041a09 64
    0x707403100081d10703540c84100d80e41c1c5906084540c110101d04881e610307040755840c0d40103900405030500c058003c030722000540078050b0700c0c1c440c90214105003000b1382d40d60b112041c2c0440700d12003109a0300940111100120381c40100441d140040c1c0036600c21038070313109140d0000c240ca10b00c1d402903030400540c0d60106511900303843c507154201d0701c0c841c40800c9582044000c25500d00940005042c81b50509040c04504034011030901c1d01d00c94a5501e6041c2802c50041c42d80d695400c00c18281e00140b0b5000b0201400710703903440d011019190524009000324000b100180369070303640e0340081d22450108141c3c0c0102d40b41c039042000040002d5000b60422480c0c5603200041030040103c8488101c6002070b1000801030b40c1c0084401c25031004010034094144800018024015809114042d0940c2030021072035002012201089418028006150106260900c00c041c03140b2100540721500407a002d2590440a0189620483e00d14040c0261840c040c14240320200300d903040030180b089100d081c0a0b800394081 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 796124415 1250 796123165 796123187
    0x80d0b12010c1704050a0506190507090e270102040b0d1407090312022103100e01050f21010504080a02010c08102606130501110301120f0c0b0310031a0403 68
    0x203808502160380d85d050090030511040d800030035501400e004c10072030154104e00c6601d041102c0c8010001e550b0b811400356142040790007080025400c61001071050760803501e64021443d120b40c0200711380f054100b20542640c1081d0003000c0c2e1080702060300c00c5419414454048030b20b80107942e0a00b02d040c6018090441134080c0006402c0f689510001c040480c003c110514402c490b8505101401510701c0351411182c00aa520f0810320f00b60140009141003c2d1040d07505030340d0300030f01d0860b034000854100005180d0002100e002e04040070741e60703605201c0c00e1182d80c0c4a140036001859841c41c10b00802400c642e0702d14446400c0c401c40780180164045034519130025500b941d02c5001034045107032048416003010071071481c2c062044800f084490800190146200380c030800091200a10040b02c07513040b40030034000c2c0003020800b58510385c00314501000000f020741c0200300b90500b490700e4140140c46540120b0360f20042100320941002000b42240720004c2c00084880b0001141c209a6002002c5000103 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 796125665 1250 796124415 796124447
    0x40f030c03030e0d0c050f0d080703091505010605030106170106080c0315040e0304090e0f1209011e1706011e081005060d1a22051003080d0b12010c 65
    0x1003825542050300952004001c404204200c620800110038010094000d039001280e942c0180e600c150030390400024400b142481c1a140c8007499030710140b0440040c03040c06025190600410740b1509500d8492144501078607081d0342d826500e605061015100e00450700904080d00e06150040043c5071340414481d40006155801903645d4450500048a11130100e86596001c4d2924442c242d500e0350000007030048501114092204040c0302d00040e4907410340c46407101c0340e900400122801c840c0214010410036030141841c081d10403101c400c50490a0350304510304003296090f100101c44407140461954800800d00c5c204c040c6800e4400c4290b0480402d003418400c0c0250701011031214a000024200079280282105840342090111900500300c40c000c0100070040d030050f03229080c00e1a011703203c041d01440710f12207603500041c1e100e0300007442e00a109a1100c140a0008000034151000074140c0091100001c1002200d11040161802d02d038071090030a82e2425803041102d0b900901d0b02c403004414 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 796126915 1250 796125665 796125677
    0x1a061005040602030d091403270301020a080114041b03090302120f070b0603010b101d0109030b010317040b0a03020a0305090712260304030c06050903030f010e07020715121103040f03 80
    0x168585500044415008801c05000c00304142801a109e402c00e403900320844180034010070b0b0070300d0901d0f00700e1040308c2220001640c104014421b000444103000c142440103040002c603080301041d0328001d403003088807480c0001e454100b00018540d0401c2840004580509610701d803001b4080203034118802c0c60001810840b9040028406680c00c0d84140203c6a02800c0b03070161040070130000b0f0580041b44001d401d8004030110b0b8007200c1d446040340405481e44034042c0d0619900b10340ba4034010b1509003041801040f4100004111411848081d22003180152005030b19110b440c10042c0075504001d209503865402440c0801810f41060355441c13000d030b00b03e44141031054004c89030510315044c017203149134185400000e02040543c030000d14900e603401904200407a44920011644074030040c3d4612149143c6000103202e010314203214290403020900403900c1055441d80001909940d5a840c2c8020541070035014501c003803940114505ca00c2c2a20320140b80d0716081d510740d400300e03041250103010418 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 796128165 1250 796126915 796126931
    0x90234030e0402040f1413020a0e011701120206070516030c0801050703200a1b112128050616030f0e10020702060d05010e0106030c03020c070915031a061005040602030d 74
    0x540d0b00070500344031f80300c80e0f084d9914400a08040c10010030017035882d00140140c907501c21140403059541d8160b6070812800c19100c14140c08106e41900201c4094a5500860010595051000e00c10074015071180c00084113840c6020b80c4c1c0c034210b82e401044401403509182c42d401c040c5620105816a200320181c540c2d464072a101030440e00c0651282002000144107440c203010300c0566400d0b04646441100d94240300405802c01c0c4000001094074075180b136109403040055040d29100d4044000405d500300f0200b032420303031500c501d8600b0640f403c0d000d0469a0031030742051903240c06030a0450030450424041c842c60280140c1d9940c08050240c2400d81d80031410a04550300c0310200c03070100d103007010f0610440d42c44416003004000e0038400c440100b8a03041907921054002c0c000c3c2c1d1689040200984002d41c41c08090b0009007000001a1041c560036140210002d81108034a43c001d00200c48104140d02d42507080c48001c0c505d13203602e6000d012080c40700b0404203030700000f1140e00002a03040414418 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 796129415 1250 796128165 796128169
    0x308070f050720191a0304080d0914010e0c0f041109030d02150a0501050904020409061b051b060103050307120c06060308030603010f0204050a090234030e0402040f14 73
    0xc011004000c1c0340a840d200f58004110040c803e9450600d03003100c1940100c03001003202102c0364614440c41c103048003804410424481c680c4080d5502c28010151240303002c0e0551062804c03940340010446000300119003a8002803800d20800d400b03070701070b0401000c0c2c40c80c0240000e4105410390350418852501e61124100c480c1c00201641c0c1c1c13154000e011100b900d030544002a450f4840300c40690441c01c5030000142008441e4010380d41200d0004e450b0345c10545454091001500744068151001030f25090222181c80c01e02c5100383e401949a42c82d981c4032001c01541e207064069201480340f0640c00a40180027151021040340e02082d8082e410682c1c00d01c1205080e1044044550007400984c5003810020030300c0540c00003188154005c03002000300d02d10341010f41080740502e024113500000b001e8400d02c901410342c1c0c000c01000f44c070012000c01401496800d0032405651481d8003010000304040042019004044462050011a01582004d003081c0c6031580010492182c554820000d0b15111029 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 796130665 1250 796129415 796129417
    0x90c030c0b1e03010b0d0f0b0a0f05130203010803030621120c060603010c0e1003020d02160c06050316031d160f0812040306050c120f0103120c0308070f05 68
    0x215808996920a241e458510148581160b02c007420000003480c100c0389188111021641070354100c10940c0d090080549140000b00111080101165521142c004080d661040010001c150461541c1e10890504090103921980ea80c0780b641020b0060005001214012042d21f6001c1000d45450241580d0b0340314010100036139041050940c0125050100c00040e48030042001c5a40350b0104c48551f252002810300b00d0340200c511000040101d2801002e40c9840305005264541c0ea1902508010102e001300d4220381c41201050b00070f60b0f000b500365080205007610300e80140050300f001419442d00192904816003030514480c10141d13980b481c015681c3c1005c140100049e145002c44064a2005c0ea444034034800c14040c404600790300f003000007400c0780c00060840043d405070111030b05092031a0740d81c40203840050010303c0e1101060000c40c1e40d440c0d60b00741c0107210f1030103410000303d0f41d40b66040c180c2c480e080043c0c8004c104040190264082504608180e8204040780740c81e02602241450850755 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 796131915 1250 796130665 796130669
    0xe060f031c03020306010807020a0c0b1b120c0c180c0703260a050c0c0a080d060b0f030a180209060907030b0d05160e0f130606030803010305060a0b150409090c 70
    0x1105801c40c081019961540c00b4603c100c100b03880b40d00003034607220011307640d070310070003c1c0200340c45e520a4061040f1411200a440340502d441c0a607202211800d031528280040d8011030200580c001c00c101c25803200400004203d0315060320345441c505a15180c20040080040c480408420000f4600082622400d50284040c50000d0901b50300940c09000040324003040e00e00e805d600d428000403a844c46d034488211000a480c81000300030b80052660b07421815081b00340000c40340e0f0703a103001c00035428003960300500b06103902d514005e9036450030300c03528000c0f41c86103506211180310244420340140c0703604d60001c1d04984125420246944c600d9021070103001c10054058000ca0320120800420100080b02c41074942c07501e905610158444603d100782c43c0049411500600b00740011a40c00c9140c4080c0d903000600030f003c041025a140d445110407584282d10894440c3d000c0010840050201e01c18540071507000c4400b0009880c04484a004c0c1d80120702512140342c4e0354104000403c0226000c50300 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 796133165 1250 796131915 796131943
    0xe0a030b0117010608063c070906020d0311090f04110c0f1504050a020925120b0a0b0406050d18050a1a040c0303111e0f010c0206010e060f03 62
    0x40568490950740218102c1240010070b942c00e0681c00b042109003c1901403088a044003a1104426000829448100c01503900d940e074a10300e803d1200b1040d07820a10501c070309540e0b20740b42221031030150300a02e4250420850010903180241003000402030108940500034110b072186081000303400000c0050152071111848400c00080e2200718030700100c0d44106079040c24003036464141c02145170100d80d40c400c0320014002d4103c1ca80c550300528050f00c200b9008002042040c2c11030403030300f00100050008183c50004200d1305c41c402e4500d040540140802003605469009040c0c1c58000601d1441c09030380140024010049000e0245102c1c1d94000c1d03580090982d00d44507881c8142c10556190840c1d10415a031901d030805881209403113801c0802c0c040c0303520403c11862076286480440e160681740c500e4030701070302480350305c3d0a0650500044181410142001d0b00c041c03403050030801c0c00c40e88030414100541d084200104403620404440c0c1c0e501040c00d0310004221803000000a003410000d07e0155 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 796134415 1250 796133165 796133183
    0x1050402031e0907150305010302280305062a161101020c1e1804080307050f120f091e10050901110a020102120a0902032104090c020a06150b0a0e0a03 66
    0xd43c6900051a0f1088030910f00e240ca54a0803d010100d0a42d80f0901000e90484607000807d05050740c4044203280a405480c91510543d450396901c0b0700303103272094a504941d001c0040c09154880318902003d281082d401440b9031038911040140000b12119483c05440c01f0302e441d00c0034826034000d019501700400c00802400c45c1100d00b440200c000320b45004031502036600f02c80c8015034800451042401950443c1c0e1240c210b80d41d695044842d41e00407505a0b80d0040c040c42100710300b0607800e0056001c0d6032a0003040304285071090015103000d406078201000d0f45103000e03600c40c40b02d0010400403921406804081480c0d40d8407107541c5d015124400d5403011003a00024081001581076014114184803540300e080d007a101e0040c5a02500c2403001c0195154111520281c07030440c4900c0700d2182d0343c0030050014145640c4403010340c03c03a1080d8421401603003010160104000751032040c01c00000c00101c100310114100350498040f801600c414005201c015030040000b980c4034001c0d4402103902210784 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 796135665 1250 796134415 796134421
    0xc110f100306030b0c0c120319021c1b230f1b0606030c0105090f010e03070605120a0c080106050a03020c120901020f0706050a0c0c09090627030801050402031e 70
    0x40060030b080c80705035008043d82c0301042c1401e50483c112444801124010304d6032144c40c41002c00c01c3e80c009802a100d0103101020b03000d24140900141c00028612b602c1c501d00401d08000d444240d0f02d82041c248485061260700d80881ca401580c0d802e1a844200e0400580e5228801c806525110ba4881c1c04209980400c2c02040d03070840401034a051050141078442da03403030350404e143c0d07540c90192102d40401c0c400d100e02825030502096000404405140642c208104000440d051107840d8100e00006400015081c504491200803690801103102040040310342c035450050400f141800b512007003000001c0e5030301005119405a4810052000c01ea800c545a40c410400c1e0f564401c40045026008840a001c0c44000215030b01007120320070b458040c50003032001d8044660346078011049405d010b0604000c10050320901c40c00100ea8820980041d007200700300e20900d104800100103500903030b50410b65100190f80448800c0c11500c0640e000340e1aa01c50705418880e02c1844004c98800604100030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 796136915 1250 796135665 796135667
    0xb0d0b0a1205011d03090105190302161209060e06160302160e100611100b04060e0411181302150c190201080a0c05090607030224061504060c110f10 65
    0x11080c0540c030703507080c4481c000d200f43c1c011301c0e2207001c0c00700340b540410070920941483c1000241d80d03d031000000e2400510707011000388011305494004606850607000c0c1c12031041e00035003000a840c054141801c010381c1c42c03004440014454820a100184442e00c11469081014020007041d058070044001500140e502c54850185880d4121081c0c040f02c0305168001902600542020714280e224801a00b050300a28103000c0241884080c410342003a50744800049120501d02c8141c041c601c144210881d0ba80808200000b44402c1c0030094041e040310f100380034128400300709146800d075050b40e01e045402c2c3c401e00e402403180180c8001c0d20780c80c0501090405488545070340c2501c940e00c00d8035100b41a841d1400c00f0700440c4d01c0303645800f01203041001181c41d203242c0f40c0054074000340301c3c1c411224001500c4032a4070401030060030820303a42174450244401842d01c2c001205220b24507a025034246880d103e0000c1c0300c2081c107040a80a811031029550480e120500b000034048005030a00034031509043c0 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 796138165 1250 796136915 796136921
    0x10306020a030c0807050d09020f030d08180c031f02040b0a0e090907141507051c0f1403070e0f09070507050105010503070807050108090106080a080403120206010b0d0b0a120501 78
    0x7000030002407404840360708040c01407003158020f01e290b40e210390824841c4121200100200e03501a80c0c001c604410041d0700e56001c000c052000050b80e40c6044149c1051010300c8400c1102081c1c01c03889400c0f524400c903071610001100310b00341a5a40720002000c8d040c0c0541030080c466034204240078000002c00e04091500031805000c6842d00741c8030018a6641c04484c25183c04140c01003034030070400006400010310f40058a00880608102d41515255041c1d450514001d4403200c40c0d60800718203c030190002da0894030300c42e240141800c2c40051410156141070396480001c2c110300a012904c1d410707896039200c40c1420340e800000900000546d0801c1000a44103400c55201111503609000020810f4207000c68002c0845407032000078594281490300541d9a520b0041402e0b280c0d40d80d4810005180f0010410401079602600b801c44d41e450031030a020a0905001072070b20305560100004200c0b540a1000b214505c580b081d400184018038000091810300360750b80001c05844000c01d03220207200d0194 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 796139415 1250 796138165 796138177
    0xa05181f0e0405011a0c030d15081903080a09082217120403080309150f0609070e0f0f01090f030809040c0c0308130314190f110c12070e01030602 64
    0x244544240c14400c200b00300603030340240540b040c0c1800d00d1540b818000c56100240c0702e40040340c1c0540c1c1c20310b0005410314003150890010200d454800d070f0410008900280181d4850308240c3c1030f1180000035545014019400160070aa04560f42d440c01c0002e10103002c0589403551078148405400041003000704005440ca8042d0002110100d240d201d111800016203092000130003c49034282403560311541c60640000300101c1d0300d405244025a4040084441148944c0076040d0000c2c0b1f90502c01c0a02c0112800208004140310107109001d905584982c0351980d044402c490003090b141007100104ca008545510035944903c11010120410103001d000e1300d400f05d002d0700c0411003d01018412181c00c060604040c01145400c0c01103014540c1d5800c1c85240c41c1d01a007800e005114888080101903841150060303000c0c6040070044040d01e6105074844440105441c000000514055040f51181c0300080810710400d5038140642a2160600034000100303ca9012407915603580d083c0000039502c10 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 796140665 1250 796139415 796139417
    0x100801060c39050a0509011511030712030c05120f040203071502010b0f04090b0f06040204030c060804050c040e12030411040c020d020d0f0c060e0f1209030609030a050a05181f 77
    0xb458000c181401c0c1034034104111440100507030300b40c0e403070309a0480c0b02140c2d0540351000c116621b1000b58003201b08100920190f8412902200c05280441c0020100d8090100600421404001014a002c1100341580d045144003a03224225144c610010b85040070139032140e40143c698003603010629806600c100c0719550305403401e9904040090801045842162008000e640b24030081070400e2600c00015500c40d801500c01460951039850f0004103070803590201380021030b44802c01c0200407080c050b4260548c801e40b0f0900c0541d0342c0f500080c0e00d0304488024080b6151002c00040d0a006260500f490b401c074014004102c0070a0000000792113080c0765071032001510945118085041c85590368061100440d9601070104607550f44079400b824030411160424070520b0b41c0002c000b00103010642060412040e070a699912400c1414184400145007130382c41c1e0014800071412641000c1180c07144411858903541c0e41100c0ca803410304034070084510a0300440020780743e44108403d06507a040b00021 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 796141915 1250 796140665 796140773
    0x90e0115050a0503100f03060209180c091c0615081509030901030c440c09010807020708060c040e06060304050c0f0a0314070303030b100801060c 64
    0x2a146030010400380d6a0510000803030801502c0c1d0154800c0c406550090003003520b00340700c1551200e49a1140b10380d50400d075031044e40000c078003415241001c0110081005d8540420807850024920900340c012800000e01610f0342040d0380f41d689081850407060030340c0c0128100811007004000d84650034050040c000c240c400c811201005104d02d14500388540b100da402186000e13082d1004401900305e00380c40304144844550345140102508030340741c03500c54000100c0720150300411031881600c60300301400c040455010040c040c006404004980c01444207091140980e202e024041746861407a902c040901c1c001c444c28442e280714100010401c032804c0074050704054580c3e00802441e4841a10000c0c2564004007031418903041491807000303001e00c000e20341034000f503803030f1125000c06080440100d800c1c0c000040a00030940c15120344040b25009540542554080c1c2d07034041d0514a041c0540070502006465000403c0340601041d0a04070320050a0810502044041d1780c1e050007228000b0b080d104 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 796143165 1250 796141915 796141919
    0x18030f030e030a0f1101031d10112d04080a0b0402030d031b030528020d0e010b090a020903070909110a1a0a05030c0d151d0606040303030b01020a02090106090e01 71
    0x82c00003218150690400405440c0100715503130140c0e0304410440310780c10716031694070318103100365130084d01c0807400380000c0600f452081d000145000c03100455460840e00f0001d010a94148040d200b030312201c00c11440200e01964180e03848500346001e5070303100d04690b100301d20f503000411655016083c0201d100b03900301d0394113513071541c03041e4180e40b9621091410b500c41c0d0340000400d00c0c800d411094201504800914030100c07202c0d203a01c2c40b41c403402e4140744000d800045d00c039400703403040c40740701407405142008001c40b883c2c42001400c1d218015151040703041d004160305c0c100e581c080c800b2800070700810300304005508440c645009005000c880c40d84c03080308000000506076020f03800e410b00031400c905900d89441003044041c4c6098001a0038007040c5c0d0010300a0002311095071003902c010384000440c0d58015480d04903041c460124845002c040e64a0b050240070458440c0410789068982c10304010400c0348203480106c2c9085410000654040220000050b100d600300d44501c1c2500c3c00d803150341410703a07 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 796144415 1250 796143165 796143169
    0xb07090f0b040e0a0b0d050105280614061c05010314011b0212300f07230919170c0603060a0303080601021c09170d1e18030f030e 57
    0x100540c411080040243c0c0f00058006403294084291803200404840d01098140c03200d40c2180c0d0202c904071925a004032070503001c101260003080d603003103032864244001810701d84e00030728101e054203e042c080c8202240d074650369101001d01000a40c0048401c101c40e69490802c88000458000107202d42d5103001d559403441034000704d41014460a40d0014481c05803ea060302d14264068050381210340003070907250080000000c410005c40c05041407030880d0b414520280114241c2c0138109600740655146041c035900d15941c50410030007460881c1c5d6450302041000303c1c00c55801090840c0886440310804a0146e42a803007540880028a007152581001038080c001b8511040c0d03034648c2d1080060f8400c20000b481066640d51102c2c040c8140c1d0381d0319000c10f0300f003c0306c101c2c513044d208081000311005102d090340c2c604280710716061260041c940159441c0b0041c01115490700b401501e0b80b565034000341050702501024442c121882d124081031075a9007444241862800c00840000b4141c0341510024 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 796145665 1250 796144415 796144417
    0x50f0a1e050a0209060d02030f03030a14011a07240903030f1a0613030f03020124061e180602070e0a110a0f0212040905070f08010b04051504030b07090f0b 68
    0xd90301c00001c0802c8011602000250b8000403c9598410f040f1144031005860038091003100911403001161a030501c20162401d032000100804103c1269000400405506142407210000004100380d40c0d10a0b608101000d9250311a0000307110860a0311120002e00e40d611042d9054002c1e901000b400e0344442182069440301c1a403403640d4590014013005c3780c9400c0c0000d0000100b404601c0300c82075920340d20642c12212064060740541d546200c21001e1441c0c469940401c0c0714207520b000d14541c1081005080071040c030b07928500c1d1003911912403880c5400b80c0048540c50f4600c08047c0200c40d0f540400030350b52034050081c201002003c0c00400c8201a050183c111710420710342000d420030302602b0f0f0450312003c0701074a0030110301c03c0c5510384a046124a00410240c05500c201003018503201a002d400300000c4c440c007904208500004110381d41d1a03070b094500b0303075400b240e041d841c40d10350000e044024011900094400c0f100001805406070300040e0380400c6800096100388607555905445227a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 796146915 1250 796145665 796145723
    0xd0c3903050903010209192c0a2d0f1103100308180405010e160c030503060f030a0209010605041503090206120c0706062c060a030b0c07050f0a 63
    0x4028460545040000e004001030006418054001810821140001404803801d0621410725805549040c040c10000001504564240d0010041e50040a42107103884440c0101301c4c00e01e140d83c410000044c039a10740e00340f81c0103102140b40b40c0c0c010340c104207803c002012080d200d07225152400740d9014065051406503445550400d55584540d46540c17030354001640480d00e0204080300101800c403181d40da80c0319440c040d21148041500e186055181840a0300c0340040072820b00c15003503000c10020361300504403980003d0948501102c520a40086881c010030500000c1d8003144040012606561200280080f9003100b540b482d521040b0030b0060381181d0080c600a90450400c10004d001c02405c10443c0c0c0c0c110142c040702c01e03d800241d44030081100c083da041500c040b42d036030f0301945a801d2114061021004000055042e80c00c200b0005a010465071100402035561000001c2c0302c11005420382d0842c40d040015155101002c443d0503449240700c900031a441d004001d40b15001c1e082c281491302c4 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 796148165 1250 796146915 796147007
    0x2120c0a0f051c05150c0414010c0c05040f0914010b18091b012d020d05210c0f0301030501060315050408030612030c0703080301170d091a0d0c 63
    0x4401d440f050119030500061401d49443c494031144103d00142040d0039441000681001c5440301c0c10501c42014400d03500c01168100880d82440c0c1c0049801850300000b1140304aa0000c0c04a61200e981c2024100b0a207014084148642d05146009070640059142d000100e40020720048904021031810b00c0c16030320b6039860742c0070407001c0b10000c1c1d0b02400081e5400050410070100603800300c1420301c1c00c0580c1031040c2e107180d11002802029404004502c0e10715043d08000e424900612000c0c4405542c28400c003d04030f010b030b408101140e1466045174100301c1004041c070307503960b100d080c2907018220314841218001030b1030083d000c4101c100d109250145600c0030b01c803440d607103811040144031401d90744014000e000c100f1004c0481d0004211800056100b2841a9183d40c58489902c1c4207058003403105807a600156200c0c106d0387e900524020950f04003150500f109200010491107a0058648110200340b42139042000950480222114014200ca880c860280b81c40a42101d00c82480281c40d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 796149415 1250 796148165 796148179
    0x181a0903030406020c01090b0103030c11040c0c0813030c0314281b080304080f19080f0a0905030a060203041202070509070c06020d020a0903020102070f060503040209090a02120c0a0f05 81
    0xa4005195038004043c205c68040c004a031000080d200c1034481242a40103c02042c0700310800c0701080000c0401c56a110343c105d408105000c94003102821945899100401c00b041c00100c0048040b41200c2e400f01071500700a00c1c545554591400501e2410b01e0303140805107104110700c40d50700035804079010071010018003d80d20104078a0741c488408108031050354842004801c004a4440303020000b41005040c02c500078586141e01047c46414030351910051404040c401d90002c000c00c03007100403500d1407040c01c40055610140d02c00304407500c80990300b140e5454000c14a0351014440281c001d14040c40c024a81c085e04220300500981c0d9501c003c1c030500d5000000762002940f854058000d0b0103e90b405800090b29024890106004a9200c20405404100c800105106550f81000140082d141020b20710900504022000d41503010041000b8400c024003400a102100180800302c0c41c99070180ca081a0325500c110b001d03444409507000caa01451005400203036118646031040100d5201900007 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 796150665 1250 796149415 796149421
    0x10606091401030e060405101104030c1a072f091905061207091a010c083007020a06110715111b0d02100605031c12181a090303 56
    0x44005a011000748505040d55041300020103c01444007a204a108601403c00c191540c69044100c3d449555030321080002804140000754a00c403c00d030075989414518000d08003904c0c0c000707203148100c0b500101002c41c00c00c0c070881d030041401a441d210444d4400c8980e1040380d02424041a51021076442c3c164032701c010390741e00011281d58805500004c003e003400300c0b1492281401ca160040c140e01c0409a151388402c00c8030825200c400102c0340241c00d00e00000c80d42c03150749860300c031070180f084100c41c40106028012580100d108082c240168000c5060009240400340a512404c140c0020f13030b0f2207428110103031400c03046001280c07082d9502c0341c00380036a40180111403004200c01c0d02582c140b150200001c0c04018010481300b4000815000240006c1c085144005c4c1005040c083e81c01205041582c1801b4035074021a04510300301018091035107030400900300710b034840d000d0350b41c455855291145d2049100e840075105084a40601d000180301900c410642c4484a4122070b403800380c0c3c00a00c08 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 796151915 1250 796150665 796150679
    0x8070507020909121c06080c0a060e1f110c0a051c0809061c0e061b0a02010f020c010b04110c061902070b312a0b21010801060609 57
    0x8002d4101ca00d070822114100318002030b0440c42d500074650040000910411110140c1c01760244902425202e0301038103611034243d000c1103900da02d0740244014810090005101e81d240e90510070900107200c1a088422101c0d6003014080c0703080d9104100440c050840308000c1c500305640783c4400c03144c0152030390101c52045010350280d071000038422107884008211440e290b540e0b00c00034007001c030b150001d4030030030f0109010304008480d509440e26401342c0104081181400c1119201014501e117400c0240c0e495043c010b089004042404500da0301920214040340e6100b0154003036001d201040d40c0400c1050703d4200038072041c1c0101d0020100e99800040040c030942d500103600300c00c4c11217512026003002002d0f0380d04445100201c0c1c141500300b00250100042e200c410200c441d841200296103080074080ba1107440385082e2442d000c01810035600078440c0101d15000c0c280000300b500d4400c03140c442c0413440c40d8010001e00b100080c944c500c088000460003440600c42e040484629895203031900d0718100f2 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 796153165 1250 796151915 796151929
    0x601020d0822080a0314011a0406140702040c08090c011d010e1210051014030a0201051b0601080a1407230a0915031b032312120709060807050702 64
    0x1022100000542c8400e0005000000030b081c0e50204d0ba01c0120f261000048086185e010591104c8554074003562003001d02000c4100312000d40f01c0324030340a072040401c1c0424000610650000035000340c0350648103e50307243d111100d80c0c0101406403e4030808020340c00111018480015100450710060041344a10742c00381c0f41c1c04000941c041c10304540f070003100d16560704040c1a201c400040c25190400c01c00e0211002000c0005860a44428034409080340046656070200040c003d041c071100180d24888001090050740c000c00700001141c0e0707a50303150a00c42d40c60720100d00c01180c0010440164059418011030840c09071410001202032a80c001189800f2459185600c250009041032001c1003007412070043c290750361850708070f600945196180c00310b10308200c003442e1129141e081d0011320001c0e00c0800c10b100100c4c000c001d0f00b01e000d055124168104002e445168000850026030403085587c003044452060a1030303114030b000280ea0707c2c029600f40c001240d10a0018004012180040c60010 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 796154415 1250 796153165 796153201
    0x8070c110d050718050106021e031204140d0302120708040f380402190b0403020904050106050a0e0f070201060f061110110408011803140c03071505010303080601020d08 74
    0x34100d44103070340d4914181c03203aa1500904c03401c1458032000144210764041040f01d54840040e03aa00c4076041c40d8111035500c0780a071500b080b0310b200b003010224040c00004100400d030306402d0030565200b03c0c80c4407806002580300e28951000b0210000005040f64052441248150340050051800080e00e5071002e8013020300042d015040b6a0035481030742c012648442c8900f005490307980d4103001381028010002c00c803500304100001c0e01c111001c1808007900c41c2d820740742103a42c1665101e10a07100c43c0703001800752219410242c0c01001c440800107000c0c1e0b180861600039214001d00c1e031262b485800c1c00f20b003601d0740750085c0d01d60729840100800000d403007000600c81c260030000a54860b09000d4504005403900c0c407030055030310100824140300c802402c0c41229401c441d01011300c207110704141d501518400c1c03200c0d00c1511901011a0f00200c0ba0414002c032040306500503450011260354030721680040000f8001600011900350000b0f0155000007001610725405440350030f0a9592801c0000c2900004 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 796155665 1250 796154415 796154423
    0xf0f03110904050a08030412020f010e030a031d0f03030103021306150f20030a0908010b0f0f011e050319140402040b0f0d0503040602061f0603020d0b090f0708070c110d 74
    0x2c04c141d50041180c074805540a00d2182c1d2070a40d8810003414020320b800040f01d2080c8450745070800c43c0c0f02d41e140c00011603450340300c2d604010a81840c01842e42c4490360000201048a0199840842840c02d000c80218185c034821108038074010303004010082214071a0054040c0c0c003034842e00c010030b668003642ca032071040b681600c0e02400d0402900e28119900201204c034002c107600c003103024a80c05400001c0100540314200082001e001030380c2c00100142c041c005050f00501a049441006910400c002c121b141400100101e0700015100c0042c03c0798012501c10f585001400450100e04000d4011028143c2c901400f101c0030340c8494080000410007884011fa2100850401d03840039104ca48404c2a4207000d000916217951900501a04010004220f07000c45c0c299050520002200002e100003a0b422074680181c50300c007010300076030050280088941d40800c0003410010781d40002c1000c07034031411403503940100a4442a070191651454044001e009810002c5841118200840c100700300c1401 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 796156915 1250 796155665 796155673
    0x414060405060d0c020d0e030a08030603010e0313031a01180b060913090203010c0e0109060309260a0306091107080904200a030501050d2406050a08070f0f0311090405 73
    0x600c0001030744960142d08000302c03240c4c0354000d208203580c0503c00c28100d0001405c140d00103030003c030000380c0ca44840390300c01041c0c5100400810540d460951101c2000325041c0308486d560641808041e030028138500c81119004071014603082140d140320140b0741210415090303207004842030313802480030380220075044d03805c038600780300c55411951050282e02010901410008049503180141425606010714a4007030282c1903220848a9034000e903a8070449006140004200c0040c6c07505c032201c8460b801c10055201801c601e1203480b40701c140c0081c082151292400c0012640c2c4000085c03e807210b07085050811582071001101055100b802003d5040d0300410000d0144a13540d0340c0c410702000050388c404070380004a00d11001a815120b00e9003d002c046851400000883d41c4035000b10314500100a891944e5940c0d98040c08800d800a502030072006004d2060700f52201c50165640c15107104107000000c568400203182c895401e02038090b6600168105650701464050104001010b00110392900c070b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 796158165 1250 796156915 796156919
    0x51b0411160615120b09030c03070209130606030308060910060909020c16030605010e090c090c0c1f0c090906180c2a0309080f0a0b0c07020a09020415110304140604 72
    0x640070002c1c2101312000d00303902406050010031000c000703044003002da00801c56102d400c1400025600009c0d412170b02d1443e00e581e8860282c100034101203004202c5401e04c503000c41016001001140704020640d04580c1598605a03034090004c1d03107224041c08510400301c21700226550750018810040d0300030072910004096040314218204552041c3c40003565640188590611003030225000300d0135100800003000300360001410340001811030185040000340c440340c0c215045c0154040202155105d50301c1865402004004d000749403000030000780c020350701203000c130203621840080d203081009081d08414400a45401000711102c00400e002d00c1455011500c5071a803041d498072100105101541c280901e006080c00c403c60b0031101954020800f005640c1030b0004280400f80d4020140352425121000100214496200069040b11400b4000b041c000c00c1c6400420031151254040b5448261000c01252340001641c20300c03034a034000b0401008204413400345440510310045c50300f032800d9 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 796159415 1250 796158165 796158191
    0x1140a170f100503031207031e1d100e031611190501030c080403081902092e0e011d0102010204051002011401090209211009051b04111606 61
    0xa0045901c24030589121040044200703804254a00a0800b03030011401c3c4028000481081e24004041508142d0b40d4032104402d50940c1c0d0200c5141030240da820031800c0c1c0c50f40a4230704410344030101300105120700d241e1244c020a06104000140302454040d50074807083c80d0142d41c0c20300001c00c0603a03c0c1d028541c0002c0e0255a070b43c0c0c40c0c42500c11350040101c8000d00d494000b5041e030301902c0e5a442802500e50411000ca6084140c00798010145825610305070645481d43d402405204c1e001034214030a911400c00302200c880a000010601075014880300000c02011202c2c102c83d8024540000d080c01d510951001d0466400411300d03805000160929032604041600c002c0d040941c000180c0d100c45000484032900c00d1014050015030006501e00b1080001141c800141100194550304003c020b044d0820000c1c04010300c5400a40303000e000007141802d0160342d68482c200d03d0321140000105a0425150601c44c928280e50004021410301c80907610f00c3c040e80308404000d640c07558032007034508441 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 796160665 1250 796159415 796159457
    0x20304080d060e042a050d0501061e18020c030a1b0f21092403060308041d0a02032511101b0c0f021c0606120b0c070201140a 55
    0x80e00302111200f01510303050030300f030000780324141010181c2c00c0359103411417940c40821010019100142d41410120641c0e1800e10700401480c2c0c000040c0f0858081c110030403210014039402140c090f10040c20011b4000700300a4200e1248a85069036640200074200000d40200c0e07031003000c035122104028089281d6103426582e080c0c1c00d042154401c881206186026101f95000c070841142485d0811659051502ca401c0300b0350207001d0a142800048031450025100344c1008d005140c0c40900b05454a0f5160110714148080001c01c40034802d43e0400915482114400d8a11690a142c00030401200b400c4440c05200d19103494481000f205050182003444100501300320040c501400085903550801040c403078a40d80c100600412001c0b90211000c11064994080c00b1501100c100c1c486d5a480c2341c000100349060b40004000b40e0070300380005075503806004006109400ba200c900415601c100c40c003500d51003103240007400b08840410044004196201500d4010301d04c4c18040801c921850404043c = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 796161915 1250 796160665 796160669
    0xa060c05160312120e0d032d0c0806030313050402030a09060c09140a060210020a020c0d0b060f0a150804020f03030c0a050f0102070c18060b0d0b090c0319020304080d06 74
    0x41103240b64038442802e038403022107942240304c14410044c00d282481c8180d10b03084100c0b92072007016100d04084031015510b00f080c83c070404548402111341c0008400c103e011340129001070001c1411800012054103001c81103907002c40702031405510003404c02c02048000d401c050603080308140c1e6a1650f2000941510411b04001c016072504072445142c10030340d0110405100800d406035400d880300700041600050050300d11a50000d0150301e82c080d010040b40340c6030001464075840040c0b100c00606000303c42c036041d8002d620546424021201250074061302c2e0000744104101900c1a100504100303116440c10b0350401e100402e00c03484544403c0001c0d04d550002c4514141c02d4010401607000c01800b045012106900342d4000d40c01d01c0c10684510a9140c0c05201b46202a0908905403241007010ba00040c050180e103a0400e071290b80b60b00760302c0000c0072030750205400b803155100891090017100701503a00c1144417030125000d2400d1308100c00003941016000f120010428080144c80780f1940c019100 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 796163165 1250 796161915 796161923
    0xf0103031d0d11030c060a0e0f0f030d050310080705010906030c03110301080d030f0b0907080c040801110306040b03121603030204030203060109021c051302220507020d1d0a060c051603 81
    0x8051002014240440c1038880c5d417007982d04200e0101000d4102060599800045680801c40d05070b60012554000e800c2c1c03010b9900d8060b141688402c41e4014000d140251110904158500e4480241036925034850050601140f61040c0c20048188a40c109655400d11450301040f4203504d071082480030340007038000400c00e400a21030b25030869450307c9941c400008000f01881000c09042c003040030200007030040e008201c3d0181c0081e00c00f2003484100ca004080100080103041c1d010034a1070080d410503034845115a0070808049604e2900240b000001107402302002d00c0c00c440700115180c012490300089080c19001e1000001581e420700c413481c001c1a58140c0507a54141008029100c80c00002003a5101d9141c44140154505540005003c6640c140c070060400440e20402a024242c0d500c50300b140c003414042041000ca5011691020b03d40460301c071605a200c400c0720003100450080c2c5800d8000c089090100500f0b80f0034107039450139900910580fa2041140f002c00301c41c1c1042600150707 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 796164415 1250 796163165 796163183
    0x6222102010606170c03040b07091a0307080601170c092d0a061b151b02010b030c04060806060d08070213140a060b03130206040923010e0f0103031d0d 66
    0x20f00741c1c01074807051440d80b641000c0c1080d4945031801501038040644007400e200c2e00d4100048090b4007441c0500301070142c00080d021980452403036903440d075000701c0b5048001b030041d0780468031550088101840020703407000c619071607988000107941c00d5000819080d03070100039021001600911503030440d0344414210345107540c540b00e00d0b0501941e4000796001f0320810412142080c800300d90301c0030740d420309940300c7c01c0a003001e4050595072025181c200201401d8800a40010134081d40540c400c81403210194199130805031500704000889003d03204800350b9800601c001182840d08080340101540b00d82200ca041ca100ea07004038070074290300a000c00b816595509140b00c0d0401038405154440c0c0800024003403103003440403c400030f005c01382002d03074aa0500e00c41001159100c00941e00904010f400402659011854100d4001c0aa102140c2c9070a000c85c000b0402207044500c0f1480b900444804000d580d1030769904584400d004444100b84005201d01c4601940d00c80310300e4a0403030b010355125 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 796165665 1250 796164415 796164419
    0xe1905010e010c0c0f0305031e09010b01111c032c060a0f2013080d1205101d0703141302010f020d02060a09060b0a061709062221020106 60
    0xc542114002039181050040520311500043c4485c00d460b000980d040c907010341c40307840d06600080f035509070405500440800c07030200425458154031030744201c1c50990340c0300c00c0b103490760001c10b40340c07686451006940d440810360980064003075080f14500000080c0d1801030003000300950014410201c0340389280d5004041840103c01c558051a8048120796030204511f15a4a04809280803004c2900e00c40d50404111044000710481c5148010035855065a252402032080213108500700030143c0d00305842d140100300380138040d0b01d01400f5109841041805911406952a41310000801290425803600700c0c0048080900e4201c0e80644405001014103548910000d4030b444401e0507881d045601c4059400b90072540003841c1500300114280002c0d010b030745400c00c507008d072560400e035542044004600140c072590104c40c0d55503507034454a6002030380e10ba01450a0320b82000350340d1500c0d24417822195403558031003d442e40400718030030419031441500d15014500803050900b0b1010140c0d543e0241 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 796166915 1250 796165665 796165691
    0x12060a14011a070308061903050303060102010c090f121b12020f0402070b160207030b0c04030209010b0c0a0803060414190f060803250203121305060304020105030402040e190501 78
    0x85405030000342c000440c02010401d55400c0303802406400360070002a200411020f44480c85045000102c0f6085490115100e081841d62a8000c0c5c98040c0158a00700b40008028465440c5c041030b20b901c00091520a4a0b20b8040440000c581e942070f2002e402d00800312080300740b000d10400c0204040041403406101c24010040d05000501d070f03850103280100240d00000d0004060b40e0707442426940b4083e0305010b52001245131044c26040100452101418050b42808600141040328421102d00a00341e80310300c4440d0290141d0070b1052907a902050000d070004000d10043c503444907000d800041c001c00c0103a07442d01d00c220151051301c000700d8200050910f40d9a2405250601c0f0312041d8284401442c0000d07080c1c0c4c0f03200f5256940501504103541040302c1e281d00c003400c3d032180d400802b2111000000c103000340c9071b0352101981204d585551140000c40e41010b0701604e220b41c0e01612942d0442d9210740034000078140d07003801c0c0c2410b40609a002024407c8640e490f50040b4012400012401c42c9021 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 796168165 1250 796166915 796166951
    0x150b16020d05012909060414070c05030f04032a06090308071b03031707050307090303050d0f05010611010e0109030507142a0102061509071413060512060114160212060a 74
    0x1031809181804188d091050403402d16907040040c038a40101c1c92401070a185007103014100c000c070a8070790300107400014818070007900007600d1001041ca401c072403840d10740d00b140d45000748620404588444000c01c0420142c1c17015102190007158140900e81078014104c0c28403102d9017044002c10310070403840740344c000b0038403003140c0c41f2699007025440e500300420040c1030310205210003420000005030045002c00d80b0340200c2c51144c51031000b8060303542c6403078014001071203c0b500880e03698a40015684004014021300340201d4068860034503212054680c0d5541810b51030b59406d480c800c0d1141fa0794002d008182d5082040890b02c14021101c3c0c04400087c20300030094a02d080480454030050313079980c0c491030401c0d00086182841c803603241c0000c101002a020b042c440700d0a5950b5040001801d54008004014030200003c0d02c0b0178075914000190f403400c801200000c66001d0601c000070241410101c2261a00e000500b00c1d94102c00d030b50312403460000111511200c66450b01401c4500d000610 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 796169415 1250 796168165 796168171
    0x51312050c0108060f04090203010f0504051e0a081c1b03060518010803040905070c0c031211060708071d0d1b060206150d032001150b16020d05012909 66
    0x118251110f0300b015000145c0c0d4480481c6854481c0ba40d68484004540c0c0940c45400d810b44007880030712142c0f401c0d080203901c5080c1030050341c40400700794840c5040721201003004403800d0ba00c240c40c54200121846c01e0081c00700d00b0f0604644550340c800494241d40c41d110302c0c500d00794407595000300d000f900380b00501800c40380b006c245e040c52900910040c008080080143c40c256104c000c2c00103416600d0031002c07a18005441005000845030400100a0041c030210f100e4181003181c40d00180100c1c0104203030740d20603013140e00e00006a0000301040d215403080ca20241c001c00e8500d01c0c4c079042c080c2c48000828034001c5550403202d8102c1d54048030403e403503210b0310034002c203242d0010b81550300d405507405130b4104520710420b2046038410a4101054080c0140c406402694107640c040b990222000ba802041c0c00c3c4541e002c904600c090001e00003030000100c42500b5640038440e904005103030700784644140f020400b2100381d5207603a010f46131424260840003110f9201840d82c088a0111018003945250203 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 796170665 1250 796169415 796169417
    0x6091a1906050a03050c09060a030c0603140f0609070f020106150e030705010509060403260409020d0e010b06161e050d090902160b04111917030903060412051312050c01 74
    0xf0900f0000f00d800441c0104d0b000303a0aa03108200c41d5035980c00100382c000300d60002440f8a50506012552545c540d00070f1510000d00910803610751611040c94450840072101c05600184800001e00280c2c40750041030340202140c0004510541c541089142008100289100140c440090410b10341780422043c4c000300402e0a1403450f043c20440032a9661049000141c40303400780514600c2d05003030141102c40c268200a1107181c17640d880e074034448040d500168681c6400303401c00c0030104103600c06114a180d11070000f0802d40c034020300c021b004560900d40010940c0e10038101c0001e000c6a8001e40f2010140510907006400e003180d0074070b0003405001280d08044d00c0c0c5441400000e2403184425620346850741c10401c0079259640e90b00d4203042031404801026004010422030460002003c00e041043d81c420101480f00d404c00b82120907030380d000e0740425945c1a4052800300d408980080c06030a0070350f07806d00c0c0c2540b070594008c090381072205503079000100c0b2400c41e80039241441024003d1103030350142 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 796171915 1250 796170665 796170679
    0x91505040e011d0a170c07050618060d0f0e300403120c021305010e010b0f07062f07080f070c151d03010905070302040b011b0b0601020f0a0f06091a190605 68
    0x6d94049a80e0786d41e250154901480d0001140c0c0c0906443c0040c0c510b0790400200b00540d20f511011041c0043c0074840101e4603010f041c1070390080101c101180c0d050039000d40c5480e00c80c03986207001c5030307a00e41c20006583c0702103a5410000070010960300c008916045040340c40b400d2000650384184100298503400c9c0c01c2c1c107940b8020040c481c0c070090030318090468000900d02a00c400118905003101e10030b215000b00307280e00d402d20718469150451100c01036a400d8017800c00c10040070b01059541480350f00c400500c0e4084c100180740d21405400042c05102d030240011a981e1601c80380188000c0144441a0020070740c940002002c09411600c00724400038258000d100243e01c80c0d440d165030b40c805000c003c0c41a902c03000004226403140710390300204a00c40c4a201036000e581c9c00d0082c10400241d4090f07006004900c0d680300c903014006103c00c00564000c580403a016419141c44c00200b40c110300440b054441781340400e10301800740c18414001c2407043c202d08040c40329128680c003110307000e90145010b011 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 796173165 1250 796171915 796171927
    0x402011107290408012f09031515030609012405030c0d0302030d0207030512010501050a2106050d110427060b03070503030a0513091505040e011d0a17 66
    0x201c840e00320340d1040c20b100e81410307001e0030041503625000d15007001c1040d61a01160b00381c82060641710046011050000c1d08105441c01c44242e514880e240f42c4c1505039000d40c10781561000742c0c0c0b084541c060203480c0b8489901c408900024100b000a03542d40015a46481e03140c0001510b030030340030004010713041e1581500781c50000400d40310003075440c01d288070b0030481c042c0005160080c41222a440c1503244115a101601e24002e81150808111003a801c511030001103540c1d4081c2c401c45405e03480d2500da105099516038610b0015441448640281c1034503500d0000303064840c09010306107948103800c8218043d1448091008540d92541d80c445001410041c1500c031100f1b80c03a09098a98012802080100c0c84001281c036108069100c1c9406100000f4080d803425444009091504c500100408115540f40c400d001503842040da02d459000300c041080107985020752141c40da446030080081500100780084000108041c8508261a04407038134803010883d10a500c46985560704c0901c0d41060 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 796174415 1250 796173165 796173179
    0x512070b061f030f0b1005041e0608061c081b0105070e0603060f0102011b1707030506180a0b0d05030903010c03050405060612030714030d05060f0d030e04060e0c030402011107 77
    0xb01c281c522000c03c1c0340e510011000a25525082020480c00c080c0c01c292201c40300b0840101769902030720a600c400520030511003c060f5260b00d902d800c42d41165900300150300d9080421100034617003040105617442040f0741100190280c805000d403c1c41c0c0e0900701c01d800110034481425510b0003000350082040300c01c6110321742e90340c1d0410381e600843d003550b010072885814070042c1d00428000c58220388540031440e800f030903036600200491120070700d228021302136201c090045e416030318143e03652a401624030440314603804140600c1030380060098804150300c036094000c12201460040b080c2c030660400a000341d00c50800b4001c0f02e0324508680340c1004246072039100d082d203034100548407603c20494a003540e04690400c1095940e11600104082103400c614030a42c1e40d0b07039000139a10f02040e03040c04001a194940080100e03c0090003620100b85416265400c0f184c4d207480c240403aa100d070f41e885000c904c1d5114482c0711803003444040f140954908050002500c2c110b90f00c5a03600c099440508140711907 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 796175665 1250 796174415 796174459
    0x3040f0605090102040e010b0a03060e1b030c190e0f10050d0b0a0b0a030e071a180109082e0b060f0304060f050f06010e040615050f04030512070b06 65
    0x8990804000111030b01c0d10341450340a40300e00c2e4004048080c000001140059006005107980c54240e2000c101d96541c405040d000d4980031620140c010a40c11000110400d5100041d40e0043d0f8441c0d42a16024118404041041804c0c58070f4000600c2c100700d0403d20b080c02a15541c0c081d0089918107840060b600000f0901c4c1701302440d001c61203899040c0080e540d29158061001391102d40406500d0b80c450a1004008004030240703440d613442041c40009249c00c081494000034411407401c14030b0600103003c8124596550714159040000e4810b0014203080c040c4582008081c000000400d40311404480e6401c0070b18200410400e2440e20414071b03101c0d43c03440b00303c4010750354000803180c803559641080b0b00200540d80c40b010780c2508107400c00181210002c0300302d115030000d80710260011980414001219418091a1004200841209201801000502002d83c2e41d210510f2500391695905800c0c8100940103500d00c61003c41c4d03203400c209620380316961090701550110800b0181d40e10400341 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 796176915 1250 796175665 796175693
    0xd03020f0d020f2d1f15030308060d0c0f32030727090c03061a031902300d0e0d0605040f05061510030e060c030907030c090b150304 58
    0x4c46903440409844600c00c501002c2418001203064400381440c11013600e003c6100400b18007600d5141100382032070340710181c030300105698160399000b1440e500d11043c000c4011200300c0503115060420b400048422042441c00003400305071003e0391402211104c0d921440304140b80d005503465403004150841d450001d02441100c1c2c415000201001c000c031284003031420344207540302000b0300307241d00c07007060040c070801040c1203a115a00c10460583d0100948801d1060803030419032582082030f100c4104100307480007009841c0018030301c0c07a1481081900603c504e881c01c8501500178410540e01017020001e0105070f810402a00749090303010090340014a02c500075000050081d0f64550102d402e008038203160400c1d81d90300c402282c0c1c41d801c1441c8582e1440d610500750304d2280c401203007848101803180c0505410008880300426003602d400f2551039a40e0001004805184900000040454581c0110400030708841c840011603032034050500207184100400415004010014003000940422000300 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 796178165 1250 796176915 796176943
    0x213080f061f0b27101e020c03030d0f0510030b220212010509061806191533322b0905150408090d03020f0d020f 50
    0x1e0341403508042840b60829030340103402d03401400300b945840e003903080c1c141141008041ca94054850420420018402c0000c006140003580f0020b078030a20103005503082c5048002070064802203201c1001081c50340d0020306a00340c0d900c2e00c580d0248d4400000340f044a412181c03c402c181602400c607201c40c845804090003010050184002c80b0510750030307101c5503c00e00c0ba8007d081039075101d400308280d400f822003500c0c112454066000402c2c140149a89203580204078072001d0201a0b84014407005492084a000120b003619000610005a00400308001611140d280388850401e81040f10800c080c1480040640725121b03d0288902c1d500880f1840540c4440242004410030640b503601c3c111105a5107100440000318000c0c544030003603401c81100703c50900720300304001480c0408205844841c48090700e00c2c2c0010780c1000c13198140f941c950390b00602544034070b442c011136500030031140c0d4a40ea40550050304445258211100c3c28045001c650107148000c02a101100c94465110341407006811 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 796179415 1250 796178165 796178191
    0x90905160203271302030916060e0d05070e010e100b070b0109091b15080c12010e041407090605010305060307031707050f0105010608090d02030301060c020103111c0213080f06 77
    0x12a282006100840502070140078030030f040d11140c02a138003079081521130325003d0051210010b07140740f5055200040315819541c00340072400010a10400c106509010f50300b0b4000c0700307004154041d6811849000b022002c18440691422240b01c500c42105030b0811814540204518004140e5140f0440c3c1911801c42c0c000400344100d151a5503206c5030b01415240030b01260100158030001c00381c90308a410360030b4992081556038503900d01002d02c20b0803001101074024030010301100d914080190b601c14492010b15000c0c149100c04180b81844550201101d6910343e5418010f40d6414003c1e02c0c0c00c0300c000d40003814514290350300d001004280301c2501402c6007001c00d10b9420b20000300700c0034000d140b16500810203940c6034400200910000c0300d910f0843e02c02c0030220807000344000211f90496009a0381c0000c1e50403242c5c011406044450f140d81e900320003c0c0702074480c2114245c140c0400301500c42c00140e68107014880d00e03013500d6299118240540025001e103110f0b1001140c0c103580445075480c81 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 796180665 1250 796179415 796179457
    0x418121419020a02090709080c010203030f0c0c0a1a0105010f0806211203100602070b030408090f150c0d08010524030907120c0503060f090d1419090905160203 70
    0x40f0302d02448101c010754070111a40600940c10340241119056842c01c0c000c0d43c8058042000583e074034807041d160600c4000e121800140007804402c09850f41c41c089000780c4050302c0c1c0c1516003400b4043d5882c5000c1114204200410066800c0b084c502c4000a06040100c164500000014080d0405294000489828180000480c0702c00c5c090b0f00603d400b103004060316070070060b15a10b0f103150103000b8400944076410700819007208840a1f2803265034440490780c0340124807818440e000242003419900002140d0f080220000f040c006070021704480b00003400510803498000b08800c0041e0700c42c0b402042e0624042c640e02c08005980702022080701d01d01076072510748880e032502e401c00c140d10040d05215080c108100b005070000800040b240700b2000c881c5161608100c0e409001415210700324254040c1c802c1d220082e025040225240054440090807d001d24503c0685140c000b0355110015003003803c00e100141c0c062042030340015030400d038800380f416000c0d03019503a803260f41226203074a103545081e = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 796181915 1250 796180665 796180667
    0x14010e06070e330d020d0b04090f260714060105041b03150305031b011406010f0804020a09020307021023010b03090a120c110d050c06180418121419 65
    0x10000f2482c0a0680c0d0380d43d00b8980c00500e00a400201042d0314260501c01010700a00d454056040b105030170000305910010301380e82d4038180c1d801400049905104041d0b405402d100395401030040c041c010107400c1d00e815a0b00e011681001e0050304080c1c1700e20700d1b01c180a10003e4a54401405042c501d017000a10310411903a000011500d41c0d100a0403440000b442022507944c0c2c23003480034458501c030000c0c0706c0508494000c16240c1c00480e00c46000800d00700d061506140304089454020f80050000c1d0890380c0c4a0200740140e910484007038000d644001d02360081d842240c8105141050102620701c1c039010014030305451404113218240940030040f0100300140024070100790a035078804200d2030940443c010140680f00481000e4400c01c00701041903051342070140311401910f9000303004d4031041d8140000c1101507004140c00ca040ca8102c110741480980f16072081d002e103c038608c032806094010360b03c5c000c1105800104000100f0400c0c030680c20302e400071901079841c058441011050610101a4 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 796183165 1250 796181915 796181989
    0x91222050d060615210218040606031b0504030819021203010e07110a0b01060302030a0b090112020306010807060e041805030a0c0209070512040605090a14010e06070e 73
    0x1049074000c454011003800c0101590118048a002c5550050305194520050310010000042c892030b01241848201e040d0080b50300030a00c043c0c1c1d03801000c0640c80c0c030b0000f06003140c1c5203030002da001c40c0d601c090600e0900700458407001d00c46042d00e0400d180c0703805c1d40d03600900d90081038400b007108841d80382080d860340d009101c41c8268020301e5a0302e030303141e694415241011110954808c00481c101a2654030784e240c000c94280d01041c2c1104a41c1060392900380c0480095000400900c000d03175446440382c849540c0c00144500078075619001f10022010780c0101410428181e2042c5901d61000c00100305158121202580c0d49004843c009214100341c11151070804a40c1c0c0024258040018501605d50b005005080703410b00a076440c00c09a44c030000c2c00e5800707208603400400940c2c0714600040024400f600001c1d8040c00d9078096840c01c561030380d240c0c6111095803450298513510703003a451b40e480c0810040c1c02e5001c040740c601104822400c0010460250324481d104640040700c2d032807480411603c80e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 796184415 1250 796183165 796183169
    0x207030605071b060f060906080c010c03030e150105031204081f090602042d060903080711041b030c020a020d0f1a1311030105040b01150c020301050c0d05091222 71
    0x1c92021008514a0700c04010b0000d170407154815071400c40003181c60182c2d4450301c4180d480040081450300840780c010f50b180001c1520031030402d40c40f014600750914090003800e0364108402140101035050904040c106038450203849401c041c01e0200300055840001d4030380005040e00700c4510b840002c05691000380c145010080c1c00b041c00064001201c18164204000f0206c2942c6c10082401104003441500e140c81e10079040003551851044c404a5008c200030170a281c410340c0c6841c440307601c0784086002d07105103d200080403000ca40200d50000d41600a581d0f00f400d041c07010b0100e078034003a4001b98400441550140a24603a4a1000c1c00c01052900a5401c0d4403806920301443c50880c4070208031110841c1c0442e4075002001c10105603090500445000310345c00842e840e942c1c0c0c03c0002000c000c80951504204008442103040e01684081c1300d81e9018265900c0700c4e03070b5100c4075034030a84180c9101610b0219150b010703040407500301410b0001d8a00032022007880b0894017940b403960f024a56055 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 796185665 1250 796184415 796184447
    0x306150c070e041407080c0112021b07030b09010c0f0e0418050607123c020a08101202030a110a050a0f060201050f0903070807020a091e1803020703060507 68
    0x1101c020a0380c9141288243c8503500c20200b840c242c50a030911103440d603038544541242d591000c4044041d5600074000464144c0c0311100050a1000d039082505a00d0410545c05003d6000340c601070092000c02500ca139032224080d0000d00503c55816070043c11000c801d5841c034200b01c080008011a545c80350400900080380100308034941c0003070308106881d44415160003010801150711940588004d0040614013500856052160608408410310b40c86046210b211068801c81080c01d200c00948098002400d5a0b6110700c3c00307151203200004050340356009840078103501154400140d40c00501c00342056444540480e41c041118003040c03d80010ba0000e9600030518800404c520b042d00c51b40c41c0488006600030700168036001d4044c03e9485040d200b40359290000c008103c085110100101191480509801d040300e90310350304841202c100c08250780942100c01d91420000e8841e02652512059106d400421600156806981c400461100030091031300c4200040b60343d401001079044481c21 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 796186915 1250 796185665 796185673
    0x70b070c150f020d0f0813021503180709140703090606050a0603050609252d0519050313020d020402070b07050c06010803270f040e01060501120e030306150c 69
    0x286a01601400003200d0090051181c0c013034000e0b80d00e203d0003c0504401954031811080d4403805c24040d90f50010b00720580e00312196070000c40790a04d00b10300035031141d028410304000600d0711403096400c006c0964402d480c0d040c10040a280b190ba0340d14062138124203142000541070f01e4614081d40a40440d9100300e62100803807400080c06501a00194860602150852655515034040340c1c0f038404411581c500c1078000440840c04a4058440c858105c103c45090030011280d03a0000e200385400340c400d500c00100e0104040203082085028102c02c001c1d00d060107421441d203803c80800b9810514006845024804442d9041d511258100c409450704800511000e02d05094050034aa100c40b8a80e4601d1056900000345101d002c8195103071081103a1070b440d210446450741c00030498001800d035074841801c1514500d503035518840ca8201381d04600010808274588400502a12408100f00f01f01c2d50070500c0c5450720071800f00440e5808442100c0590b00060080b0341d1080c0350103060151401031103 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 796188165 1250 796186915 796186949
    0x5120307030212181c1101050c0a02100b091603060b04030c1d0105030a020120060a060603110f0f0a02070e130c0909050606010e0f060d0b011b05070b070c 68
    0x40d054004200b03e4070581c01442c19900c54070540d00500400710a5460703c0c1e00000078940031100c0c03481c0e145d0130700c10203071400d400d07005910702d102c034216103080e80c503040351810004082c11003a80501c1041ea4141140008100318207410011800c030030300c000c2130501310105804100d02e025010b98091406810080314a5441c0c23500e03460011007000542c05048032580008507000c04060340458440d0507150040e0251011250560042d2552012409072030041618814400511401084940d00c201890100421090303d8000c0c040c0c03c4503a15274504101c0300302005081107001400040b01e040702001c074000d41c4d82c0c41c50303024101c1c140030140c1c111007450100b00050044568400d00315420321400741050380d8289580f5900d0000316800000c004106411040005200e580030b22280050044003800a6400b03290f603600003209070344403400b0824003a681c0e002041640d40d2151650401107840800c030144011141c851642e500c1c0030348216500d4210028002c0c04021641c540c62000b001e0005400c000302d0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 796189415 1250 796188165 796188167
    0xe0a020408160f0e010311010516060903030b041512290406090203010f020a2007090f0e060609090303010320130f0506090105060f030c0f1b2406010c05120307 70
    0x1c0b1851058402c1120030200100741603002c02e10050480341e1261068411a011000542d000e4010450403140c1c18070407402080414070901450740568441e9400244044050003080101d5000e10382600c03600c061041c041c041030080d00170170b03100250010321009403c41c0c0601c03179114964540301e10741f22544501d0140010048607403c8180c020b40308030024008554071036107020880c00b81e00d400800083d07101001031102507580034480205114402940c144136191480d2000750303849480341c00f0055588071001c05a800042c825541c0202045810545504022001c20764900040c080600500400034648205004080c002043c559001d003450406040344560b54000b442d042d0500d04a1500b4400050440d182000ca0141a100000e0045051410030798080c01e490b0401086c02216050400c04088054003180141c500c584211070b500104800002c82503041c1704a02e4599059401140c14113504500343d041c00c0f65014100303103007041103601c03d030610354541003041450004904c4000103000b10700d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 796190665 1250 796189415 796189453
    0x906130b2d0702060c1309090f02091515033102090a1b1e050702030a020604030804080d0503040309060c1e03021c0e03151e010803070314130e0a020408 67
    0x42c91254080d92181e50b20201d000742284645000103000701034040e02030010440a0780000b807214004c0002c00400205035002c07402e4030805680c01c0da185282d13110320780d001c0c0c6010358483d01c401d945529681e06508101d80028804c2e0441d82c42c0e0f100381c0703011b120981071880c1f454041e103c0854009008042d5410100d00c1040213001a07100781c401c070308e581c41e200d0000c68000c0103608035071a0454903e00c00c070f414071030045503d034001200803685406508481c90140e50f0f0070000e40b024500035403206a56610b400a0140742032485902c1c40301f40301043c000c2002094000150304103c03140d9051940841d881440e113002c110822048900741c81400444120903d540081d0f81028001c00c4411002c1400080600741c1ea038085466440b40e159002b06465802024040317801500022001080359090441146d0814202c41c00d81025801d0342c4003092560a26070b01c000100d40500c10405004d1030a0f0380f4403580a180e11990180c031110003254404248038139101e40c100d5008001c2001903d034094441a049098 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 796191915 1250 796190665 796190671
    0xd1b052401080105072001110c01020a030c0f0c061107080d090309050a05060d1104030c120203101404060b0102031303060506090106140301151202040603140906130b2d 74
    0x440d01030020915050510440b4010803694541031300c442d242c00e907242d02d064018510800c0300d5481d503100c0c1d001d8081d01c1c405810300078002070001d600c400000c0710003411641c40c070101c00304111603190640ca0301a08030825044072500000041444250b40680d0801d41c46240e50041510380d00050b02d6080c006140c1c41504810322030b56602e03250b640da07001042a862110300034640d20000030012000c41c1e0b16507510002000e40c1c0340c00c5007803c00d55652185c42035402c241c0d00c002d84c9002c100c40400218030741403003030200034402c055080084071810290340c842c60000402c010036495441e14001e189078000c20a4828000c01c01b515040d219031a4035100c809041c096905a000d50442c10012401a004003204451002d4448080d4203503868003004002480c008a018024007003403005422541c81140000c00c05072a1903180401c42c2c1a06404055614800500700103064200b4004c0c0468100d203000184466130300a1194407441e02c8000c01c1171070441d4a007210300c071200d90403105a022410024400b41c4 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 796193165 1250 796191915 796191973
    0x5032506050105031c11120c0f0d091401050919080703050c030a0f17040f0303050a020c190519092d150e0403110f030c010606050c0d1b05 61
    0x81a40d0f40c0f0002d1603a00c00d8200f210060160b40324002c1041d2510a0044030503001106040b91072000072403040050603403000084600c5038000c3c0c510821800d104004c3c02c8414451860003d60440c6002e0340c801c03c141c1001c0f0194104500000d0361500340e65081c003107032046035a8050310710605d0342d240f06403503039405244401c8425024506584e0743e07501d004100c078180541c101810310030040c640e80e60015640441000c50740000340074040400c01403440c038007940241d0300c6502c50903031358502524040d140a403410609440790b0351080c50044102d10268911088640960b0f0140300585006e0b40e09142e081c140d00a025020b01e030442c24a49010080c0d00c12500402034001031000807000f00039030b0140d500d610308400c0400076042c0204820b00e81e072101c00d54000d00031314204507130032039262010f0300b803500c0100311405551010450343d041020a02c0380800030492804c19030314004900d01c1c2282c40b54414101035061084481e00143c607010b01d602c0c22150154040196011313a00c1d040e60400d8002c89c9824019 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 796194415 1250 796193165 796193171
    0x141810180803160605070210020705010c0908030c15151e040b12071a16060b0a05060a02070b030901090203060a0c0318020d0204110d0e0c09070e01080c0705032506 72
    0x85560700031044540355000a95031050044003916888003410018181204500c66038840c11100c3c1841d1000c0c02c0c00f280708000103c2c0d14141040010048103c0350080e44864008022103d2586130000c0e42d040c080582c0c0c00344003610743d03424110501e10a01d000c03541d900301c1d00c043c0d208c9040d0215040300070881c81085808000141005007805600c031803012142119a0040b1014842040c0c070b114030706001c07518140e01519002c00640e003082c1450002e401203541b1510b801d6440c2c1c19150060300e03000902001e03203085050909420000350b81c2c51a500c60005903101c0000401d902280c29007025600703507009800c4a5550a2004505005010500d44100042e1501608030442d101c8003241800c040d030010546190700071b007502004002c05d81c0e40c00c0410020001c2025810b810f506001d20011000c0a00140604200e40700c00d10035502801000d0008100c40400016a03c3c0e8204030f032907070809903502c101a15040b05162a030301e1071141101101c01e008079008500d000c07400c003590140425200d04001c1c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 796195665 1250 796194415 796194419
    0x409060f0b160b06040207170a03050c2115030d050309010e071a1305040509070501020c060307140d0212130201030c09150c0f0b0a0203040c0f050114181018 69
    0x11489a00030058401102c410030503801021902c24415240c0248008100600d000c4640d602c415100c109182d402410100129090400035094400c40e036000c44040c6d5102d180c05401c0121803001820308038000d20340ca252402003180303800d003840400040140507080724120541500c0103040d503002191241299801c042902c1c26032400411004211a0003102101c40c2c09116004010035070050003050b994a980f450b03001516644e1800380c82d001e8200d5902404c4940d0803d000282043c102c8004107008802c204141b000c03140d40034099041600300514916115002100400c000c0c0c481c121200b510380b0021014406400403410540c00c051340300340ca0030090341740c81040550341940329100d1225280343c4150340504260080400240c114480e100841c0710713245c680d0342e003020454195800b5408660100405c0204481110381c20081c140c4907a480c242c9a1038480000d10200c0800002c949a0001003413401101d0765526800000303072802881c8056405180d03000401a040301c800e01c480b000c05410740 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 796196915 1250 796195665 796195679
    0x30d020909070f140d090501091401320603191a0105090709090b0105070213090212160b210910051006120e0304080d08161407060902150409060f 64
    0x8807143e034240c40d11000c01084051314000c0740ca800c8000c4040c0c0b1a0746807400600040c500384200c0002510070414854034210004106085a118044801c0164200c01d01c214000103200c00180000f44403801408584c5e40340c80c04241010684040c2a0300321004500b50f50400c901c508006a000703d01e01c01041d03081c1c3e82d030340400240c1d66007691034601040a00c0e105000502140d00207490303611040c108030746070408540c04141c3c0100744010560405503a114040c0844c80d20b00c041d131413056443c400604080b034148410030035807600c910074a03031090305c00141803550003c42e03501c0800308400503003507000134540743d0500c9881c0c180035503001c140e0600d007000140011540080c4402a94815601d403541000700070742c0707071006011406405a0b9403005001c00520303048100105036900d02543d9440d001420300c00703ca4014104100c0e420030900c0034034001e01c9600e10000042d559481e4000501117203041d01400840d0f10f854180c0c0007161084000500807400780010707002401156840c20503802202c0c1c1d00c401d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 796198165 1250 796196915 796196927
    0x3120c0109170a0c02041109100201020c060a09021e040b090406020306011403011d090a0516060909020405060313170c0d120b09070507030306150f0f080c040b0d020903030d02090907 80
    0x2903c01c020034100c101c103c0150426520895620040114852402441b0000210920800700c88030006031740000c3c2d14414000203100c01500304440c4001030102440d40e9000440c10007120120860b0303c40c1074000100ca0f0768881d08210320940c000b6198940500b402c0c01c02c44d000e5030007203441c030b0b0202d14050301d003011000d031440859040300c0c080c40b1200c004201641d600c41811401a07c4050a48203106000740414024001251a460420006c24419103080400740008200d80d11490450307205000401103500c640085030791046e800440c90032100d44034034005e0340d520012403044174007900201c0d1030b581c1034200080420100b41076840348030310945201c1281e415514690005900300c613211012964580c0100050315005220f4100030500c140c847c0d4045210110801c80c3d03c00061038a00741d00b02e5903420041c0f01e0007440d650b190074141494119540e000030f2050f845940102100000e800e090040c007603040d0350070014001e05032580c615240c0000d0020f9000108120700c23400e005400300f040907020768 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 796199415 1250 796198165 796198177
    0x815030613030c120320030c030612010e0d02010213090e0c09061c08030406061403070308090d06050a0504060605031519180b0709050409020105120603120c010917 72
    0x400904666403445900031210407861411070600c9031480c0e080c40096509030707a01e15401095580011001c01e40301c0034203c6210350300501c510b03000c010014410303052401002c0729803003c41510b064031084800000c4a00504042800c00c50500403880c91015255041d001400b884c4076014a00510700e032100501401c468008048409070380c441031007035074242001c0c44c24940c011002421550030014441c1ca041400d0314903103044030b20070360000400041003203500c14400603016010060350041103001c08280c0e6400240000b0782408004128421655548500825050307444001482503061400d840d00181c1001c1d84c0403035034142000c1c000f103020300340001c0e4848800a403580300b2400d0389558950b0080c103110003500541031511100c011401000c40d052102e03075940f040312003550510303222400034400d40407038229074460383c10625950f0250703070f1000a44c0e10030000406200320302d880c1c0c3e5000a107040d40c1025140042080440c14240116040d80034451440c00ba084071200300200f0044046244214 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 796200665 1250 796199415 796199419
    0xb010515090d061d0d02012901080f1b1b0c150304030c0c031205070308011502070504151a1b0d090b0705100f0f151a0c031c09030815 59
    0xa070440010440580103004c0a140c60b20a141002d02100349540c100707005940c00c40c0141c1e440782c04000007002040562007007000013000c45011800d241c40000c09260340030304255a008400008600d4205006441e0a01c61408680135580d4000c1d8800840540281100079402030240f500d48550b5401d0001d2884166101800e649140d0b0ba04c0e0345e001c0d18802c00d4400e00b0794101824035800301c0090072888002401401c02e4507031a40742c0c1342c00e1400070041481600405510441510a0100d1640010f00072080e600c0032140071602260480034420001080d5001082c40701071070f0401c05000505100402d020744561501c0920041d880e07080341d0b0f490751132900c41c4001990b918010020b58842002400d4410310600588168030f02949900003511100820500d030700c1d549030429a0108464031030503600c001d031000070000c0941b404588641e06548114000390301e110004008810b0603080c011030b01070320010680300c20400d0881c20304200402c40f5140403804210450081032420317485568000c108040 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 796201915 1250 796200665 796200679
    0x20f010e0c010c0303020d1e0b030a23011506090f060306080618010b19090b0103060b1602030a0c03050d080708090d0f0c0b0f15012d090b03040b01051509 68
    0x1e4180115400c59106006904141d0f0a0205a40740000c50046000d00e540ca0b032070303844c0211010841d0a003103d40394000030f8840d50200e00d8260008188800144240304201030801c010b20310311480034050001828001c0452501d200e000c01d1081e044801582a2080c200c400030021382c40352000c7d0300f2a5454001d2035081e0380a000001c1c0e141c00c0a20395180302400e004008503643d103210011540d002d4004080b024080007042060103160400c0c441c1c20026a403d00e0207014003854806941034a11a08100381c024000d032040c030388159203081090f420000c1d03202032958070450381c9003000ca840306010b4007103400146507107006c03070a010300c01c103034a03801056008003404a90400300001c2e103404002c804a0800c1c0f040ca09410350110709003020282c8903003601c1440d80320501c2c254000181440c080c1d080d0605100c1140e5113640d0251608140448410304140403403810715200b1015192504103074004001400700001f000100807402031801d04a600c142d58689001c0c042c08910b01903400782c0c201507500405 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 796203165 1250 796201915 796201933
    0x151206011e2405221701150b0702150d0509010617030a08090c1302040509070903030512280c0e0f0607060b19120309120b0105090a1401120201020f010e 67
    0x1260401c510000041401c10b03614000201c2030000c0001000401030303081c3c41316580c0400006140340380c845c801c031a483c0e008100d102c1c070700503030000c40501c0b500800e103c020010992000b19100e95581188a05040c1003050712050003ca1100244c501214100100e50800318000780c16003031100341e48a6800c03a00082c604280c1d074050100c1d00f540001f45171103118450728003040321945411046020920003580702507511400c200505c4070307070000980b1135000c110a000382000441d90000c2500d800050f601e07400543d94403000c801c030710001072290808200516010030604946100c2d80714080c03003c2103455840d41c4554800400208105d25001d0f03a400000c10450103000031010b51121456a500a0584a901c030241081e0380d8007a2403900f14041c0901440f030301e00c040c5500140d0fa40010b0941460a03920300134251341e00ca0400106104290245510b00045480b01d40107400c0180940c4005840402035a9501800d0100a031030940523405401402100380c110300d418014140c840d0750120081100c10 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 796204415 1250 796203165 796203209
    0x403201005070b0624130b030603030418060513090219060e011116081509030f04140f04092006130608070903151d0312040308151206011e 61
    0x20000c0076036502015a4201500d01c241c1c8441d003080203840316100b10b0302c9020310501d000000206d50440d4040d82400d004000c010b03030380081101d095a5504406c840b24145404443c00907103000d4010503070205400342840041c0d01187d101101c1603000f218440642c507005080b41a0601c581d0050a0002d0b800081c08001340d401851071400f202900e408a50441c00352300b05609143c00b040c1c20428083d00b0001050a803086040000c1d908160890041c1d460800080e105041500c15449880d461302113150800381640d4641141d40c482032405071051242000c0ca15241c6170f010192280c10459001c8083c130020320f03003404001c0d00d04002c0403c18100560b03050120540c0c001c0307001015901003220118000c000110320081d0055205004000030441d212540313800b00710802119002c0c21198414861030038250401d02c00e50342c22a815043c03a00d07071503c64040182441c046641941e4100c2000a181441c488000400d00e048030003800d07400304c42d245c1407000405440702c184190b14800c000c101c0402012 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 796205665 1250 796204415 796204433
    0xc03020903070b1305030a050c091b03070c03090b1306080709180f06181401121208060609060c06010905070816030b0d06091406070201061a070f08040320100507 71
    0x103c1407800900a40c1c9a84d44001b9242c685100c01c21140c0e60070031b2000c0d45460403e0b071006030700078442c1c84100f903402c080305850400c40d020013403030b420400c40340e1061201854000c4107030720007400d62800000c0c0d90381159820401400d00c5489000700103003034034000610359441075113400243c076081036440c030b6041000c01494000e080c0420380300905c036681d20310004100c02c00d082d152589080c20600411480c8625140307a00c00c100503030201440003087e0b002640001c14501900171440c0b0382d414070141540350740000c00c1c03a9000d030700c0c0d00507000700000500709568400068031604a030b655480c280100d54440c0d00881d50300c14107640500e0400410400c1c4101c144c060f8106100c10380000d00b10b032007c20410b03107480b0b050300c0d40000309a0f84040403000c5124080c030306002103075015010b40001d100492a0018441070b260119400c4141903101082040400c0780c1201008846a08500a507480e581c403070030108503121680c03034440c6000c007215400440c94100b500701c0b14002d00480d00e449050242030344951001e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 796206915 1250 796205665 796205677
    0x6170c1804110409060e04170403030e040e070b0409090516030c15051c0207110d080d0b01090b0f030106230f1b100b010212090d020d0f0c0e0a0c03020903070b 70
    0x1210041c040440c0000302171003000d00802c1422090f0b101400c0504101039204075002c446105520f0420081c0701294208003c0c080b401802d680001c0d00712188480c3c0c0b42002c600d50052800c1c4500047c00240d03091190b000302000da40501e09980c4a40d100c02c0410200040c1ca1000601003072a1810801c0b4810f0103150401c01c204007820018500000701c840c032190810700e00c00c56000e0b103601081740b074280306da80c1071188000d100c00d83e040c3c6160112030b20381070000c0c02400074503041c00b43c45048a2006910814042d0004d261f080c0740310340c903010003102e10600c6410034083c600c0002c00c002468680c4070000d107640d16801000c14645c0340341446100008040b41d01120201c1c00300d0185403280c0500e440100910320500c8009203002070140b04000c00203042c000b171a007000100b07500c107000e030071069540c401509194950403901030446c2c203030741e14000403481c0704244050814041114006924104542c1091081d401040100401e450b181415012030045000c02034140e0700c4981e052140528603401404 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 796208165 1250 796206915 796206941
    0xd09090605090c13150309170715201303020f03070f0e0c09030f06010510210c0309050d09051f08130201020f071d0a14070c080904050106170c1804 65
    0x84e100e44507000d41000c1c8042a00c03600c0043d64540c0114280841c5440344400c40f02081c100e60b20313054168407038141c1c007070025440c46e01c03a80d5220400704070340046a840c00030301c05405801c0c03500c4086105001c08521250310040e800345003d02c03849102407601140d15007d44141e81d5410080c542400d4a40c185030900405208461900f0042d001d1290340800c1a21002611750004140e20760424050025009220b1381c400f06101320040030003020761080150383c8401015100000d104c100080e003c40203060f0304080a00107016104000d24107940c401c601d074064440c15281200d82034000d441e4100ea02d80d1484110300046c08602c041000c103440500f20408590051040350014905040b601e818015241d2001d480814810510b1150030304103550039620500c0c04404128400403803020780e05050008242e8020031111042c04410803044070103542280401802c10402580c4522019020040398000c001004030b5410006940602e040c0440340d041c1e9500e1480700c12010075906100152012104200c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 796209415 1250 796208165 796208197
    0x60b01030b09010b0a0f0f050a03020304062d050601021203150d02060d1505030c060715140a050160021606020c0901030206071e03020d09090605090c 66
    0x71400d6403460348540c0684a1030365a1342d40c801c1940005040c403409024003000744018092020306103038100c02501d40480d024180540da9656a140a100a10401514040000c40001c01145804184801c400e542d1100c020400241d03c0c0c0400690350b405042c0f00250000301d00300002002c008605100920b2140050800c1818a400d07500084168005481103070741c4e165501c920004100120381010000c0400390054a0305000c0040425514030407600302030038070741c455809100f00401d0340e8003c01d9001200440079405050400b844405808203106408003c504a02c6a40100040c03820318040d00c0c1c4420090b01085042d2014003865458801110840041c2c1000c0004202e00e11440d10f50041c1d1543c0c040c0900c065050111a0000005e4200d54115401395480c00ca840e1038840807a030541e501215413540780c42c2a480c001c0180690118a4412958401c011004040d000140c00b9010040381e180d0b0001c0685031039a007401c455480c4141e980c016070581c08115058140d000910540c0098400b070 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 796210665 1250 796209415 796209431
    0xc05090909030306040c090302090c0c160e07030c05120610050c0a0c0302010809071d04060b060a0e0f040e03040329011e061b02280311090a0204050d060b0103 70
    0xa990820101c41c0281e49030400400c1041610707251007003c1d100304441c148105514210340219036203170001458000e00c400001011064808104010318983c00704582c00c801803900c800300034501250544405003c40d0411502c4c91074140203100380e80215820006c20482a0b03502010010440f505e0314a400c10f20a08112030320201e1404d100718080c81c1d0064805030700f603600d144001030580c40020b0414805400000042c084600100c3c41100301d2007407480010303140c2c0c4035800c4c500010400840d0040d03000c03000080070301e0500d41190310403111610490344c55449031042c00901041c0eaa0000701010150010003050000500800d074405151000c1094a114500000035070031526400381c0065449000002d4002c9624140b45203e0010b4400351602c2c900a1443d00e81c503080308238180c0390003841105a02a100c460f12000c08082d4600c85243c40314a034026540d00380100c0e6084030301400c0f8080e0305501d0004410054a00841d0129200600510714184003500c40600412036980d00c41d0400d070705da01d84 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 796211915 1250 796210665 796210669
    0x10e0d02220e030c0d050f040311150c06060a0501020f0a0206130506040e04060e190b0415021801021501080d0c05030c070b0307020609010c050a141b1524040c0509 72
    0x14582c01001958011503030b40072101d1100e0f20b1304403106090401c1280c00c000d01c1c50710390300360f000359030489501000001c82803c0c0000041c101210344c205403442c1038804070b0001c226000000790a40281e0003524180e03126919000120385820400c20469003a5101a00c61001410540018140c40714001c02829525880c0e000150095020342d200c1401c1a030020b0a21050145620030078141c020004c00808000c52004507148421f482003001400c0c1e56102c0c00001d0a020f00801d030301198801900046580b810f020f90002c0040d06015402030045c80b07803850202e14030b03000b07030301581c10f803040c01d801400f048900180032500300050307100071141d9020522001829a50422062000d400062107141d200e1520500091600e04002d000110aa0400c2016020641c20004550f400241850043d480c505075810f01c1c0440c0c401e0302a0802081e0803045200000341001c41c007800a80d902401c204419101d40704200781c041c0942007501c1203400030301c00b103000c0c51903d948041c480d58030508010f400c10a400700 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 796213165 1250 796211915 796211921
    0xf02011112041506030f020d0317100f090501030c171005010608252a0b1306060f0b040b090f06030f091608281704080606010e0d0222 59
    0x5403000208021410702c010461588944107401c40c00c10810003801c2d140d0b488060480c0c05c48140a4000c2c0d869051b01000d16104040d40310114040c600d450f810390030310f031200007501141407084d6584d40b1601d901c0810300080c1401014100c0f5000a4410955410542d042811070b2540c20750f10017500c55940c184000c903807140941c034020f05090301d80e41c6031440e0260082000c030140303440b400702103803200141d003910310f4100c50080000200c00c000101c440c0c0d01c000c0a11444101d0200241500e8085400c00800e501d00780c2180c007402c0e114040600c11144e07191102405410390307008142e602042880b080c040070b09010701a00d10002e005103d0f054640c0340c04086001544103a40c90700342d01030104100400410100708041202d0b240c0062209003d141c103260b50344801d90f604030724840700b4400954407504601034130a24600307900440c58a01c00c080030721660f50558004d1158503841d015210004980b503014040d0481d44210207401d04a0b20350301d40c1d00700090442c4071440b0124403444c5800700161900e00788 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 796214415 1250 796213165 796213177
    0x90a0b010c050a081e0403030f030c05160c0311101d040f06142e0e060d060b2107050d0c200115050d020609131b080105090f06100f020111 61
    0x15104c0d035031004041402c80021013041404005807400300001c00000e503000d04001019072481c6000254110509401c0b107492003980344040052855200c640c081c0909416a501280e124401001004014100f4410030040402c207000201c3d0194416000900240c0110078400780000d0001a031480c41e50f952408441e890340194840c0c4018112a02c0d560070407801925044c1c1c4031003014924660a4216407103400424030000e000c2207015816400d080e210750b4161008442c81c04000d01803107444007564500358002c222001c024801d032014044a00c0c403290f480d58060303000350365000d281c100010745820107007a00d03030445000c000511442e0003841800411450540c030b50507001141180035410b00b5228440e864000f2031154080803a180c0050707450f04110342030303154180c414554440d8003280a400801c010518503d5245450300d00074603050b4401c0445040e00c0e0211071001850f2681030801494102c11201ca50300100341f4098050720b80d008080000c07944100b0b200108061454201c400c002d60095 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 796215665 1250 796214415 796214423
    0xa0902061308060a0e100218090412120b0d060e1606080a1109030a02100210090b0f010b07021e04150815070f0f0807120e0c030f010902090a0b010c050a 67
    0x101c1014401e88000740510354000a6240c400d11654000102541c2c507040300500e05c41c2e00c00c3d40016402040b00ca2016410400200100030f04102d16003420211450402085048000307001c9000800c0e01c0c50151081c4162418003800d05d0765503000c181d80e80d400412101d42201980d100b295840b60b201d0003034078408409001c0d15641c1d10802d00300280c0700d006503002c001001454007010301c152811501d0000e082010b2540403500c06a1088061030242e0800c945146c010003043d051062100910102041aa00400700e0703c141c0c8005a90b140d001c0b41c400c1c040e00c01d0007540580c500d000c01c2154188142c5040032084014000581d00749441d8030104642680d81c4200c1294100000d50302c0350303244651500da0b01558608081c41c001c80c80300002804501c4040303002003400300040100380712911070504c034442c680000108025080f4a03140c1696140429030f2521712900c200c0c1880c6000701c0e41030140032016640a4010f4095807941c0b0100c8001e8042d8142141c10080c1c01c00301c07400401c0742009012000c41c05 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 796216915 1250 796215665 796215697
    0x20109090507091a0a211512050d0518040f0f0204082a10030e070f1806050102011e0504050a05240f0402130c02160602072c0f0a090206 60
    0x1814030308000d600422188842c2d2140d0610444080780d800c007140302c980314100d1b81007950401ca010418401000c2076001142d400850303081c08140c48000d0040e15110302d000304226000c071400820122018450b084900b8a1000840840c480c80e0626401c58942c11039035800c0851b032000d920a406003241c2150380301c8c8a80e42d0200280c0644030040c44c028102c00302d0b0451020b9074101104001c15000081100384104041e621002e080030701d2070a005d4400030b40307800401100c00681e40d40c1d82144014020814000c054031b441c6001449600500c2030641450960440000182001ca511401000d004006035810f004005010000038010f024002c825040507280740c116068001404010103c005c204d035010710050024032001d82c2d1094900226900d6015001c0b400c0c00c1fa1180803400c03c0e4054050700507980c1d04007004120281c020a501c011f0f0352203198410504614211104040d20303650781400008080c2c00d0102c0c0800703d14102e2154406220070000c90560b2143d408100e446d40914002c450540c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 796218165 1250 796216915 796216919
    0xc0423131104030c0b1303080304060605030d0507061d0d030b0d02040507090315060605091c020a2d121b17060105010906020a150e070b0d0203060a0b0a080403050702010909050709 79
    0x64600c92004c081c0804103541800d1221054250900d140f003800084c241d000084001000c02c585504181d026001c0034054803980b45c04030700701504640082800700c44c0541010030344468105400100c20603071001c00b00420300101001c100f60000d040c4464007035080b01031216150b0242c0c031280141800341c00142e503040d0715107145080040382c11080401c45800b0301e05003101080401d5010f41074034060002154a0308800c100100e040740e2405410000941021640000280540700d00150147c1c200301c0391b0000c02d0140019102000300d991a000d440301c04045e01c10f5020109141315005101d00802e8115170442c0c64030b4800400710302140ca80c0043c141e40c0604018001c0d07580c00382d032144c010003032400100840c244640d64000e0b403290380e158018103c0d40d10180f0032100c84080000500400721401c0441c1d40c1c0014120400107580300311030a80c040c1d10308a50000d9200202c004403a1241030b66501c0130007940303039541c08480c181c3c0840b03402c1c2d0404c0180e4a000c600c60540d44036442c090455138840c14003082c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 796219415 1250 796218165 796218173
    0xa091707260c0909061b041503050a05091504060f060522111219020927070c0f0803090c0411070b010515040603050402030f01090f03080c042313110403 67
    0xa046203141d40c00f9104540034050802400150140c0040c4c1c45400f0240d503102c039071503200060045a020810008076000c2c5c1c56400782d01603004a018000c80c46050000f50ba81c400a03d996a0741c1200c2c1ca006500300f40b000502203810740d803180c0e860030003002000c10400d9a0310b00050f14064402e0400e80304101501d00b0150480282c45844010418100c900342000519142c0c00201c91004104076100f040c00f5036031044c540d00c01ea044a01001004140001c00107214240d213a80915603840d1102980d05e02e40407508250154048001040c0d110892210741c00c6690f456001d039805c0034060388418480c0380054109642c4d94010811007541d0030608648600203420402003803076060744054010090328100f2903040518a0849060322302d90f003008103d030344680c0b01103441c0c082440c100039419407a2480d004104265001141d481c64020364850480361075041c80c0d41014825403141ca41900322a40c04604d08034003255980d074151400400710707550179071034500401c15180341c1400700140741030005040c0108 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 796220665 1250 796219415 796219423
    0x8100f0e090d030501060c0201050a2f120702030a1209030c03030c050d0806030712171209100203091009030216030503030106020d03060e31110f060a09170726 70
    0xb2405241c10301c0745514007180a80214400d490180c104000020418071043c003580241d4070740d440301040621020305c40c0d000303150703d102e83c0e201001850041c86403078584040c60505070390045400502a10740150559104415a040100e40c0c0040c400d9401002010580d00d81244000303501030f4803060152031142c074105040c29514060b0740e007032186400a010300354400040719400c0e200c1600c8009983e001c141401c0585400c40c0c2108103440c0c20005d103a035010001e07007440b5400b540c41401261454070b00b43c0301c05426804101c07101941c80e0701807450201c0e03107105078100c8804130b1301031300640346c081481c840d500094010a8100359000c1e07100000400616a04200c1481e690160b032900b0131900d410401021503884002c0c00e07201d040500041c0704044400d83d451050b600c0b1070a8030650310a4242494500b4038040180c00e424413031981155002c02500348a03007101d08103400e41da11032540394204040d4640c1c0c8810b0810040c404d106214021448813400840303451000c02140040c080c003004c0d914075610f4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 796221915 1250 796220665 796220683
    0x2150c03071202060f0402040e030d02030408070c1a030408032701090318030b011a13230103060803090d170d06050f1009150507060534050a08100f0e09 67
    0x1191303c01030070018400940110319400c5641101c01140c00040c0e544501d00d54024406c9652a940c4004280410005540014441288208074205045503222080811503504034000c2c154140d0030400140002e241c04011344c1d000000d4031261203200d2175148118120442055001031982d5110b6446042c160840307841902c0105185100103481d00310b41c1d8100c074156062180c44036000e195441c034803600c101182500d20105144180f01c0c40a170f40c641c1c42c2c01c00f40603125001c081c1c01200c15032002c804d5100740070b1272054402c0075000b140340103d00000c0c00940e10f15110151401502c004040c44a20039140c0241400c4407886404200d0505101c20080348020300d650322031140d04007503034508015030844848400c44005994a40c1d041d21482e4054880d8822148000e00395440c100401040b420020400a01c3d611035407070201d075542101a180ca0340c440c010703c48c1808a103042c0b0141c81141c1c4102034141d400a9004010300c00c03d82d941d20b459013a07032503036000103a004080904000d0b0203042048200340c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 796223021 1106 796221915 796221917
    0xc0a0513150215060303130e0406110f040e0f0402100c1b0906172109011707020606030f0a0b0c0a0c152007051902150c030712 56
    0x91200700443d00706203180c111401103aa1400c00100351074090080c8000c10014904180802c129020014030890740e940d166000907140a1004000d013408545c0a6180c0340c0307403820540091114500108426a0740c02c1d031073704000142c3d0710144513100c401540e0510070569507041c00e0810304d140e00000d00303500c40c400c03003480000c044c2813503405000ec403800603480c1d046080701d4101d2103848442a40003031002140c07218010355152408001030001c500c0506042d002408048018141d50710211142c00c0503801c80410070100742400d2207481c5182d0020781c00307010482600d96580e041502c0141101d03840040100300c506400e4003841c3d5003022a9042410b4490545202e40700380083c02c10031807420018014140c66024220001c030556442551020240c02ca07105400c0003c3d107600500f410980c1d000420403075a1040001c00030040107100c40c240040c3d66a01501d04000c108000082c1c1484 = true := by decide +kernel

theorem cover : BRFrame.Cov 796043165 796223021 := by
  have h0 := BRFrame.cov_init 796043165
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 796043165 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 796043165 ≤ n) (h2 : n < 796223021) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
