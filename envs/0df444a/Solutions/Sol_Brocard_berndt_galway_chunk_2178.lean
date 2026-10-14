-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2178
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:53:55.335058+00:00
-- url     : https://prove2.me/submissions/30391e50-db12-4361-b7ba-0afb5515032c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 391546762 ≤ n < 391726618 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 391548012 1250 391546762 391546787
    0x612020906070b0403031103040b06010c0f0c08010b03100e060f0403230714010504020f040b0f0a03140601091103010314011401090219080402030c101b150c0f09090b01 74
    0x40c1c60799403805081070007103c2c80a41e07084001038070780407044c0c400c03144010075079008981c0041c40c4051515404011212511400c0c420f4515052140030301c0c0001c0e2801c43c07413100030724440b0000314400984904241c100682c40c092000c0075820202064225800881c0350341e40803000ca50f03007840e9629a801d0845104039a206000d007100c4900400202000010000d0256070b8424090481d80c0740c04902e0150988030b0950700250001070700703c3d078204a0301c0d003030300202151100500071101e10102e03e8005041e10311641e006407200d051604542091090600003580034081d00700040c4229000044140c0051005100c080c1140c0400144004a00020341010740710744c20343e800110760b65840325000d0f4020742c0050b21740c2c0c03030b885204d0311004c002a00440400b031090b9001406060a00b0030141484840d43c000500e1104000545d10030040594030341981c41c1900d4020003561640c6041001c2110480340c401041a06124410040c180280e510121460540da140305021407461403280068a032100c0410 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 391549262 1250 391548012 391548019
    0x9150c140408010501090606050a020c0405131506060807230a030e010e0c01030b01030b1e0607020d0501090b06181f051005180402070f1709120312010501021606120209 74
    0x6000a5140b105410103416100051790804c1281e03607a40b0160350501c81e4444900150b0090140107001e0314055201550100250282820180b0196200304410b9201086840030a580350400e108103640410303a55444202d0b41031242c0c0c1c203103402000854241c80200162604031000490481592181e041400c190420750024060307a014601510f454600d0f045e036a0380002d141c00074403006980301e4016102d0502001e450007004140e9250351228038202a80c00c9600700a04028402c0140c58407415034103054002d500008010800d441d000450450151039a40318482081125540030314900500e80c00c65000c1d0420040e03501540030000c031801d003903404a64002a44805030510507040802448803d0303200d10310b10200034200c0304103c02ca00541d070020340130050b0103001e1400a03080c03140c400d880c400104d44050030300d0807200028403140015801e0001035000480c4211481c200c400031540035037001d0003c2c2c5400d60f031070910480300710781034400d603000c002d006107801304844142c0c1d048030790030f42018 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 391550512 1250 391549262 391549267
    0x1e26130f060e0c1014090a05181e01060e0d030210061e08060f01051003090f140c04051909031103031315020304020d17090405010e180109150c14 64
    0x7414914010403040040c18054059000300c1c0646103403d4030042ea043c00291106544045840c460100d075400c882c0700b607900314150010106066aa4009800e10000501c480031201c3c6813020083e610040d000d5082140554007400501440d078101181c2508a2429102c0d403c0d508a03608080307240075081c09040100b0b514100011038007070341301d80202a010380705003118032a0550303a60450366100720032200e04040410203001400146003003458600803000c80c0c5004107403211580c4032000c04c010300180407241000500c01c00c402c0f0080900c020910079004642c00c01c0903107050744092060014403441b00320020794807550f8030304240c0136040201d10b26540800301e07a00c03468419021914070f4901c42040d200783d00b02460b1610711304128022a44195409418410406003039502d030320002c4800c0501c2440060700b40030084968580d8841c44d402050510401d03840c07420302c9029040b06405802034003e4a904080c0101c000c60b01030407080000004038400010b4500c44018102c90b40d4444015061101000 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 391551762 1250 391550512 391550543
    0x30c060d180c1403030304172206050406030b030109020d140102040308121f0f030f03050405040507022104030c0515040506030a0c1805100809100207031e2613 70
    0x180345080300340c1c3d0140c0c0d07090440229150805543e4003040768010442c114045c4000b0128001d903020f40031410103a5100004d01081880c028441c107941d400520001c0c1000c182000b4583d4035000b240c40c040d600344d000b00300c0902c0c0fa40100b4003c014007140540038100308140109411800d604540040d904401150385072041c003203c0c00c1101209496216240c4600e503407400204003140e90702c0e0f0855403201d07c05007016295a4403035034110120b01054003400b03800c0c4800900b07038485000c0c241c41401c0070360141001550b07031448030180000314120310381c01c030005000a00015256030b02140955004071081481548400117001240c40f5070b4006940240d008810300c45015026040405c480c2d920b0345410f20700c0d40c1c00302c01074030101216204030b9a1002c460004418120300402e6255040300f6010240c0c1c90002c03a07803084400f42d034401d80c003c40000301c11840c50954041c02c0c0c10300c0c855211040c540301001c8580c0400f440f4601030300241084490a90401180b0b0502c4044480307000e1950000340d13154103810 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 391553012 1250 391551762 391551773
    0x30102040f03020406080c01020a060b03010b120a060608071811040801090803160311070818090106180509061005220f03030f021501150c0b040804050a080c030c060d18 74
    0x1071807108038055418901c0105001e00045190210184107038010300c0b1511981d01e80a0150000c01003c0340c040d5039a101540391a196030f03140c40d8a961500c402001d0740005458000200d8000e540300600c0c03500034840a211401d081c16102c08921081c1e540410880000700c40d0070a50300c0f6561114000d5031070320800c0300800401034041c500c02e1601e0781110001c80f681c104160240d502c0308020030606902003214100080542015000340e440d08100742000318580c43c045601024280c1000b804104480b49203032042c1000d440607000342c101542c0c0d0030001c0c1840390210f09100c440c100284244000441c00808a5180701d5450120a4178070340c6801d006503898561100540260200b41d00190141e050380b00c0382400007840740b1070003210302c6d1520030980c80d0081103d0100801420741080084540320000031070700b0000c980780030300e003d020056910b034904420071848910340d90140c040c07034000400320b00c015038003c02c1285202d882030700c3c895501d54865007042c000701410312076030943c890722641500034000e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 391554262 1250 391553012 391553039
    0x91a09040609140405101b12090611030603070522110c0d0f0809030324030705030114160824060702180a150503060c1803030304030e09070309031d0f03010204 70
    0x3402802500c150031181c504c0c0c039040ea0914031704a10070001a041f028086480744450828025404900040c52021a81c03038400b40d5149045000440c0d04c04010300846141c1804080c00500044444200d440c0045550502044a1650001806658506100105081104590000100c80240d8000700340e01c05010303180281d2030781c042000401c0100020b1030601c0001c01c490045034502040540c2c02100003603003220250300c550458260166140c009482d413004d0041b22503004168070b4a14441c41c25001400c010a031140f0900100201c1c1411311102040c10b1443d04000c03603146400c1c0000404082c04510184503c2074001d41007107900061050003a4036081c11402445082024085800d04a0b44034100004070f00680b81c0c150000008600e440c0d456200501400a4801240400f0b1162000203425604100e82c107401050410710361411502c0e1000c074455200c401030604008601c41038a0042131550350031041c00d000020502d02030050745e126045150f182000400a540c0e40707455190904091 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 391555512 1250 391554262 391554271
    0x309020a18060f12110103020f13090c051939060b030705010509060d0b04150602190b18161d06030312043804050d091a0904060914 58
    0x41c90400301146800d400d030f11090845801c001183d80b40702c00c507102da04c0c840c400f201c00700b1305141e0b0800c01706000380008405005030650300d00180d1403c525124684080c0c0d041010003008001c1d013081480050298007400c20222045450981005d80002403102000d0070260107518001c0325a25581c0c2680c0c4103e0b840c000c103180308003802d002d00c0c041d002c00e042d46e609141c01141e0101c0d0301800861b400341010b401501150100f00700c0442c4480c40c02000c9801c8586040303030040d41c00000c902c14068260100042c0d05c228a602c00c1e15185c1c00140d40310000341342c4c40a4544e05075440d403d10f10241d42c41c401c100000311079100001c03404805540744c0e00c03000615003658081da0500b0f54000060b11074603000c800d03030300d0082c003841400800c0d030349a64414507071104225202d070f106546011181002c40c410390b01082003005440400c1c3c1c5500701030401c54507104960580c0c10070810484802c0c412002c8900d10742e8180800303038103800d4441c484000054003410040e04401807440c0303070244010f00c100301d00407420b000c5c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 391556762 1250 391555512 391555559
    0xb04060b010c05030913021c09120f081303030b04150f060e0321040308070602090a0e15040b120105100303140c060708070e09040303141f0506030402010309020a 71
    0x10350340ea0801500d151080d040301508a40060140f03000a00b84aa240854440841d00c014540742030550000c0b0300020080c180345e6044c0c0c0c2c0d002c402d0200b08403803910320484041814054103800c43e140d8020801c1e13070014241500c5080c800342c044100f5000741c008010550000f8424082443c0044c15519185090301c039004084109407000180706006080300e0364a0f500140140060b154900c4280c455682940950080b0000800c07000000c10345140151582d98428240036980741080004c100104e242c5800820bd41c1d00ca40050108420114010520100003601d020072030700c00c0f46d000100551000e1041b03400b81c1d400d003000c000d5400d1414074404152032090b00e44c1111505120601000740c014802c66902d1540810702041c11b20f4002d00516503c40c00c2e80c0b400e9058030520b14081600f100c81541c089010036181c043d0892000044044a0707072000e042071a4007160f02d8000f042d450120082e118190150200201203801c1da4800d0700070300002900980001c1d001f0fa600c9001c840c42c84118210301c1d01 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 391558012 1250 391556762 391556771
    0x30060312040501050304081e0d02040602061006120509160e010f0b0a08150f1002010f061403030729070f020c0906091501090e0709031a09030f0d090503070b0406 71
    0x4440a000190740c1920410ba40301c605507640c03a95804101d51113902c20560042e0100441d45901440340d00030803061580781805601c59281c140082d25049015204e902c0c1003008210500c032b21644040015801c091080b0f000c00e01c3d1b215094072a081000801503900c020000d80004100d0f2400e07265402d04079440c3d9010042d1903965510542c2c5180100d009203030016048001007041ca02901d59080000400148040d005110b040c00250a8024401c0f035480941d450f0300140103605514070461004000c5c044816104c01c0c035245c0042d450344100180240000d01040100c2140107a080b00103c1c00d0002e080b4007452070070030b40d03400703040a07032034181e40f00041c030562880c1c1056081c0848814003801c80a1300c0307190503494582d44000c0308104203030360703030b0400c46014000101d407181044000c0c0140100c1d240d81c00000d085040510b04844101440da0107101c24409115003071100008440c910390301c800c4131030384820180c0540070280030b0318880a000f501c800300b4014244180000f030107001d03a126460401 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 391559262 1250 391558012 391558033
    0x13050f040c0c24020d230405100e0106120c08121e0a051207180e010e15060d0f060f0801140403030203130b090a030807080108030f300603 61
    0x306552086001c00d000500c16982d480004840036a1a20581e08070b000002c050000b0001c0d00c0105d811911366409840e48942c80e1219040301c1c1000c0c00081d0a1498031740c0725600d01500c9443d0f45001d0720021a070000c0d0307a500c29542d514000e41c442000340c040c0c61301809222800303042c040020241409944114003900803c40c4000070144203c44071640e220503c017941c0d51181c99420380c580c0260608070706220040001000c0e0b140b400302804d21034940c80d160030380114550300c54503052074050782012012144800c014041c0c0124000e42c0343d48086902804074240c50101d01240440c011742109540d0a42412218011741c0407030b8100340265203c0c0c03022108400e030360316007540c280c84a0308030601c04d41c0d00c2e60f00070a01081c0700303800641e8010b00d9280c000000a103540d07155200030001300c4c2d20800e1504001109010180e000041d582c100c42036143c00c6800e035040c0b00219480c2d1040303002d808003c4000041032051071440c0c001840402a103485075468200c00413281c03503c2104102c0c5c141e44a4094400d10f076 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 391560512 1250 391559262 391559269
    0x30f03021501030c060c030c0f240b030a0b4804030b070c110a09060e063109080a020f0d180611030706052d060105030403121113050f 59
    0x40d4100c9404c203d00d103031a83c1c9031078030641c4c9202003001c05400b0010105074540c08120761015022100e8410300700c84503111050702d02d4191002c1628210700c07116040c00c018500342d9070001550f12400c0e8010154140d9a10307030020030402140d52181244a56406200540c2c2001170321000c6480d01d0329603a0306540e809090400400d1901c80c44c0001070040a20101054101d03100380d5182c03412502c100c031180c954800c0e00002a0184d085940000d0340725483d044140501407540c03405070703000340096a880c0807200f00c4540203400c0380d6154545090401c6040c40418144023141c00c00d01c0500d030040031059803001101d900a468458266038203943d482500358200043d03101c1c14130a22a002c00c111031981d090704092088178844251324160800d0f201c00e04c10007011420303901c5103d000b1090101d0b20828051030810024100b012100756030410321101007000117507608034045039132060749458150418264100524003d02c2d0018008444c200003061010f00300d000c2034a4401030320012a01140d986202d4000c0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 391561762 1250 391560512 391560553
    0x6090103020d0b09070302040204090207110d050703030f170f06190e06010c0503040503010e010b1804030509010e061209030d1a03120901090b0d15060314061315030f0302 75
    0x940292507441c250000c6201800f900b500440d000003511180382d030f243c001900341c0e00103411088905a0000b20701c8100302080184aa0310f903420740f0145a144070303580702c40b9101d414a110207010b00010312601050725110368003403481742c1c182c500070560781e040c14583c1c040c240e0070444104e4040c40c0c10a080715214400030203220100c2e04801d00b8504a0356804004640303000e12454101d503144410f01c0046401d981c01c0c00f035901d0410800340006444c0722890100b040300b107481c24142c541d0207002c40c02e007c0869400000c545041c5800e00f00041d0018950000c5040e0b4420340103c0120044201c0600150040101c010b042c83c003403a107414001c2d4000c1c6e004104c0c64448011640798036034400d031a03100b51400518054841e4600505003100007603a034441035200c55208085841207a5525030b044198240c2030140100501228036040000c1322080d65901500702c400b404682c4509503000000c0517905a64010020000009440c481216074a10340800681d0810b401100980199071200c00c2481160f940c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 391563012 1250 391561762 391561769
    0x602071b14101808030403050c0319051c050706020304060509010b0a0609170f070b0901031a03060402120c0303070303290604091e110d0f020a090506030c04080d08010e060901 77
    0x20028152200010542c0d0703d001260941d0300d10a0349020014445905001a01c02180123002410031054000201800e0043c080784000c2ca1841d0b50002034086880000c000f101401c0b071724840c007200790351050280c07400c3c0202540100070305e00000810040080b1a00450b000d1004c440081c8004507220040041030b0245024860001c0e8444801304641000e480d1220683c84806050b10f1820244c4c8900900300400c5411402060000294050003541d25120f0300984240d00c2c2211104404140c00003500d030f82020b000a4480c5000d060810f100d00014400015401d1004089035078402a80c500074015041c580400007141c6128491240621200f078640007000400070030b02442c05017403078502402000c0c403484810a030482d91511210281b02485a4072659841e070210648560031001e6a00c282e610024002e1181401444403081d2542c01903803400a4550480d55a500e07a959602e02c0c1000b8015a0720105041c410f40d10f20310080340e0000e46540c140c1c2c0038003080c40b88a5071031606020141c0021f03c03 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 391564262 1250 391563012 391563019
    0x210061a030c0c0a120e04020a080109050a150f0501030b040903020a031202040333060e160203091309120212180f100908070807150e0d0602071b14 65
    0x1884080141101002142d01c20b10002d4100d0400b50556030b01d503e40800d414040b00c2d4400240e4281800680041d828040c0c040304440942c0b0b084244280200a580188030341500c0030344880216030300c0303081c1e50400c1d8200000030300414a510355844030a400d114062185d1400309107400c0d15003055041c6401040941a00754004007005005a030301211507a56009070b1a0660740e00740800b20010720f0f02d244a1f88c040801003a0301141d0341041e0642c070042c050019090f0107140c5040c4003004800d80b5031014540c0308840003548240080034039070580c110700c2241e11840c0e00a2050340000102c2c0419440300343c1e0301e8010500c04820700c1b40b51074241d0b40e500000641010b0010180102c00718031120202c030074902d441c0508410303004841940480c0d0030403080c803404004138a88542c1489a03101c00c020400041c11004010608180b520381d224210061001d0040308001100c0d03c800c20940b555115458030540c001c004542e1803165041505085111341c0e0030084416040a0020398a0180d901d80001524000c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 391565512 1250 391564262 391564289
    0x40c050d1a0a0f0f1e080109081e0712053130060b040f0203092a1c0c050a08010e060c0708090d020f03010e0f010c0206070c120c08070305070201021006 67
    0x44c02c103245d0321140700c1c1d404104010f0700002054030300e02802021801d034407690009485140448c0f640408007480130714541d41102c248040004240c0c44a100c0440b0725080c00c007241d0700c2c09403101034003040700c1d05a0544da1a202001e0300c0103800c5100a50041201c614000707030016426145840100080b01900c0b40ca000800b805d0514046103061340005c03005d04c001040041c580d00d0011000069801c120756a81607508510180741c1c000b610007148140e0000ca14541000110b41d105c001845641c0080880400403140c6103031000300300c0c0000c4444003510b0002c001e204010f50307560307203a400790020b045840c4403070207901c012481c403000e1102980c60203903001150030300b400024820310080c1642c80c101030741e1041c94450400c04548086c425140004070305c1001e001c002c48100c080b42e0949900186010841d4080f80401c0440c0341d02100c0c0e4074895a0043c0000003003401e13041c04584440740180084c0a01c0f00000301c6400b09070f0400014207002c0c1c030070303002d540010301e0007220101150058460481c81c82c500 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 391566762 1250 391565512 391565519
    0xa02150f090717010603020405070507030306141c110901080609120a0f0e010c02040507050904050c0c250e01060518030703020307090902060d06030803010515070f02040c050d1a0a0f0f 81
    0x110000c2c4001a0410f00000544503580e40000d02039800c00c0c3c990001190f00010000d0900d90315000340070107085079000c01d0722848032400104c8d90061821207240c880700301c0050140208040c2040700d0b502c1d0030b001805c155582d42c4a207030703540e150f22003510214618860740e040301d52100010790503101d401210b611a4006011440001e8401c2c07100090100c0c104202a10f603200141c0e251b1007141e004480d10380d00c07192107001300b40c00d000c02c44d807028005002c42682442902807649000680b02403102021034013070181c1000343c0807000d45c0a50764000381507440440001251082e800340141240c44000442a5100c2c0d010302c091585490340c17030101a415800c49481801410001e4109454040c40541034070314020320240d040c0300b1a411303500210b51014000004000d82c0c0303400031120310b421445070101c80c60102030b80d50f0f48400d01c15414000380a251114904d000d03c1c0c2c0540306840208a03c00c40034410101e80e101c003000d020404220140c4a0b034500c10020803003689400d103403000d8070360000345112072505 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 391568012 1250 391566762 391566779
    0x507090606022a100c0c0603020901030e06011404200304080a12140105060331020f030601180f1806050406201b0f0f070905060607050d11010f020a02150f0907 70
    0x51340303010101440485803c80e03000a00c80c00d400401850543e60058407803501c0c1c000182030b9030746010740340481c1d0302440041c03040c408215184100d80030216070000794050180702825550170311100e030b100044000b0007000140030b600c0000f041546056585c4030660101225175000f00c0c3e40c0d400080608034041c100510280c00e1041c020350b0000081480e200000d47d120424030b22840d0104074103021a00301d01d5007141141040c5540781c02c221400c401600c040e604241307003c0621440039440c081c0780e0743c544004c10b4903140d0700d40c091440d2b403000420b000d00040c5a418140080c0c40b040e00c08071007491818440c6c061000510084880a441401f206442e200c5485111900105091190080d9004001e0415000360302000100c44044c01940070300451882d1415450071182c004000798091281000007030300083c404105544a0342c03003420105178145405c0413050051101062910b81d1030301c0051076101341c40e000241c0c0400300401a01c5c01d08281c2c0e40c010840c0c907030581030b00c030020268081c20302400050b0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 391569262 1250 391568012 391568029
    0x90b04020d0201120606020f070902160f113613031d0a030516090902010509040513060501140f030a080301030b090a080307031e0903080105040b0d0507090606022a 72
    0x2d00500d880d9201c400c03c070314204101c9a06500070b1000d81d100c000312490320881480b03180c3c0107040d4000214140340c11403651805100d10003c0003032400710149629405c208240d2440841800050000f81c040300704886a246002180b28000540b00c1500b0034582d901e050350302c40035100c0d0242d01d540302011402c55805540030244040310104400f1b02d1913400f4580d0701c07000091002180582c0040c480b5401240303024440341415003000100508001c8a0b00240c0d8000d02114640003007910009900d65070f8988191041111900003812142040000912400c1e00e01607400d908000701c0b8042406010507081581d902071a040c014109038007840104041038090500a60040341d0009071480c150303035684c03040100e0344112100d60101e5901c046400d0b00402110a414040701040d00801c00f142d6540c03800307400c0348014880ca0b4825a01c640850446482d040c80a441c1150710000b200c80480d200c60724000500100e02a0600601c9800403004407499880d007a22003500800040042d015860000c2c0680a03 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 391570512 1250 391569262 391569289
    0x60a2c030a140c03030403020c1905060304080c0f0604060b0f0f0d11011e022a010801030b0601050702130605030c011e23070b01050f06040608012303060103030c020112090b0402 78
    0xb81e2050040740c00140c001d0000350720807072180d0b001d09104a0140c04008409881250a40030805910001d0140e515000c04403900030b034008484640711000340000c14a42100c03010030b07403400e000d840180810005150010042c0c0e40c41101e0452400f2071002c140241c9026041e81d0304d80c80b41c14048a9004102c0c9600144003016041c17401a91424130407900c5150a0700d580c080c0c000503442040710be1107500408940001526203546019a00c581c0640020724002d0180030140c201036002020441aa00603811118003c4d800340602045028500c07800d0020a030300c0c0b103824001e00441c1150f1841d507101d51000c0c0b02501ca14190481080308501d8204e5103032442201000c404070469200100040c00d0310040c0224034800c1e000000303190304010a100d40e0000d4208006e000b610140000e00c0040d0f00806120305403005170200041c02041004101c1407107140400181e054040c410020080c50707400202c020030305000303032600142c4402c02d2190404451440c0005051811500c010400500c0d160210981a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 391571762 1250 391570512 391570547
    0x2a030a1808040314010507090e07111623100c060b0109120501050601020c030102030915040c030807030923010507061a09090c0909010e07060c0302010608060a2c030a 73
    0x251411a501d00c2169480343e0800c1c2c1e80c030001040f0401d0900b000b4007030300d54040c0c4070b0300e091007513540303841402a031a2038003908440a114480c4c0c21841c5080040091003013a145007000040340765550741c801c0c1810b01550205945001940c0104d03001800c4c2070400350130b5a50281c1d1091815286916030b5001094001c190038100070b840c0c00700290002c1114504401d45008000000341420103400292410790958030041c002e90044c42044001074021445100d8010303491001a400c0e039440c94050103002d95a00001e04081c0086041820b055001036460140d07040c0c5900080010282140c4045005402d8007843c00100308020190004145410407110803c0304103040800ca0080307000039405120865041e0401c4d48100c54061040c03610b0740c42c840e00400d110000700218582440d110b40c980341140109014050205140e01c1018400d601803002480381d40180c2d9031606000385864050100c903036420300403001e00300803a910b90715090b0070803142c2c1401d0802035182456080b0103481455100d0000c584 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 391573012 1250 391571762 391571801
    0x20a06050a03180303020c0f2a0102030d02070803070f0c0b07030b010c1406091902100305060d06050405061503011407110f010e031210120204050a090204090b2a030a 73
    0xc00c075030321120f004011842038074050307100d40e00424018038008024003140c24640c002042520501d01c020051041802c034401819078280c1a1030050346075204100811196502c000340d000c00388400b80001c0c42c00340065070f603040351a40d019102107800d80d17001d0798041d02e011000350108603400c0c00703a071100c0442c64060520001420250b11041e07028907004070a400150000c0041210102051100e03181d03803a8484204401080c4030b0b000b10381012038403030903039040c103942d940821020f5413816100c03201c2e0340e17004400744000c1ca0545401c9880300ca00703494100300a207130305800a45601c1c06001c6c0c00d164910400b000d1595544008040707c88441d1414000d04901441803242010304080c06040c400c56410f000035665070f4881224184842c0c40200703034101420500c0c01c1840304202c00500101580e4040720f0214540d120406120010644010020350041c039004184041200c0707003990601c945c0a501c8041d8108413541e18031006038000c000d0b2010070200401c000351b40401158070410101d0001c590900 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 391574262 1250 391573012 391573031
    0x10e0a02071a090d1418040b0402040b0c0a17070213051801020a021e0d0212070c0e040303090b151503180d0c060b0a030c0b0717030a0207020901050d020a06050a03 72
    0xb5000c1c5415030349402030380c0007080044506a007041c2c0e400503031360008003c41d01d0700f203944102c02a20b500d540300c102c6c81103031103868100c00c070f5407240c0503100601700e80c0c00020b546040c9100c00c0703a600c181190040300d15903105240f91404004050076540c0f034507000382c00f0283c4912103400d814000d29004100100c44c0c80c0045803620f10403001d1014003012a01034009024510185064103950030840081000a038440c141c4001001d602081c1512456075003c2000e40740c1b1709070302e0042c10044098000a505c00015420003081c154550004c020b0340340185a171400c0340e111401140000b4410340080c40d009209115240b04001d4001c008682c0f12001c40780b0288021120a506820001c0c0680b0b45000140012421710a10505114803141c3c2c2e803080700c08800d03031442c5a0b076024a0704d1140c850440c1c40080030803100c0a05c9140e0511609400c00040702c5541c034230741051148029000100140d008540201c0003103000c0c2440d00c0741500c3c65400808204c1c2c000d14010702150070b940150b4846003010340341c85406 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 391575512 1250 391574262 391574303
    0x11030f0f070302030610060c080c010b130f2016060b03060103050a020a06020f100b12010528060b091002030408120a0305070203181002030702060301030b10060503010e0a0207 77
    0x480c5803034003a03800381c000c1c946580109444c142d409030488010900b0800308200c01a0031010300384200b507201c0c4507a500d03001414805030041c1002544150005019600949900e54582c00101000940d1a0404c003000c90b050003c40c50340c100242842c660402000002403810714411070034141d520404000c2100c101c01c4000c02c0c1006400c1c0d104448030b5101944080461402c0280c1d2409000984001d081c01001a840b00c3d50301c074411822000e10b103540708600811074940d0300507030420084110085c890741c10800034900900000f00b120410780055038010100c890900c4c06400111000140180c1c14503100c0d204000050517104070b42010361104220000d460501846078110551400c0b031416100d543c65540541070b500d008000c241150000c00100c4540504c4a41909402e02c003600c0301a885012140c1c103924500c134007034010350320900c0880000104040c1c40c070307100c0c8218089800f46004a92380c9100362000d0001b07000d08800410350000058484e40030364090f210482c0511054020707810b80d050b51 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 391576762 1250 391575512 391575523
    0x21051303021509180106030506190504050c090d15061d060402090406030f0804080c090426040801320105030d0305041b030308151507020909030c12211311030f 70
    0x404d180490301801003203015010300c00c4a503c110145e0310200d03180b0401c0303035007084a0305d1802030038492030b6070740c0205505549400903a10740e401c2c0076110203000348090400c40b90001c503058110285500b4400d0110b1499404088103a0262400813414a07945800e030812011b500007104840c1c20640e281400004604600a40041c5d12702031014160707101e040c100d4190400304010b5142d8040c0d9100400c6c0000140c01860039880700700f1010191224048001c0e80344418429980491a13542c240000592001178118175000c5c80e10310b108046001e200118562606940240301c1d05074550054084025110700079001941e00c50b1040c4e04084c00d510041c42500180c43d155082600051000001c01c0042c8282c00e5641c1c1c14042d04581b52524801c2801004500340318054000740252042004503883d040b0403c251840d100c000d5040d58010300d0f070081000f110303410081c000c10b0354012310204404000700c02c1d02c52601401c03450903074640c58202d0b606d41a131301020440c1126014401c1c101603150600d8103116 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 391578012 1250 391576762 391576789
    0x2030a03180606030803150f060d0f0f0608010e10050106020601050111120304030e0405091612030203091c05060114010507030309051507030e2103060409140a21051303021509 77
    0x82916802d0090011f140d5100150b0002e011f8684030f4000c0d1000c5ea00d6105850450180c0e6101240814000244101404044139022002402e20602150030031048d000180c0e079000030b0301156550521481c0344000e8030b20a00c07a00002d83c20120051203594401d02d5a40200d0b2421000c84084980441148280b507004460070380c000340185910b00100e20381402101e4201005100629407440c50240ca2217010840323100b00d00c4e042d440d0106c1441094028810303a2400e0f040100415142800f2a60141c6101011907048549000d914004201340041d015100d40c24501030396024241100b96405038000c3c00502c40c1582d0030b104100c0391034178002c1e1a0a00c0c61048031203980c085074480c410f0180070b10304103080c1407a2041e41d103a80300c041c059901ea0401c2e03036804181100c1c045640e1042d814030410203026010300c401c040c052402d40c0d0080c0401e02800413480302c0186100582c2c6102000700f240e1b00c0c002c400c40ea0f190103210620400261814070601d41c1c001521040152610a00c0c800240e07241c40d6080 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 391579262 1250 391578012 391578023
    0x40509210a0e01020a0302060115140f0d180f080310170c010f030c3c180e06030307061d0703110f060a1709100e0c0405010b04050102030a0318060603 66
    0xd00c0500e400c2d840000c07403500c4102030004000403020b0342c0d0080c1d00c0c3c070300500070181c90b42d40e08801c0c1031354039104884184001200a2420b9035a80c5030580b0161680c0c400c40b0303030310942c0742480d131100e4043c800e814a0300701141d0009550003516281355101e1398191f10103041280745d01d802c020085030314480b5100b44001e0000e041c0003055800c141c0800586104103010038a82407500e13140881001e5500488440c1d0743d044046c0100340f00c5100701d040d09013a411a40d420616281031002c0c00c1800c6500400c03100c10003400c46500d40c04280c1d0ba2400104112012994250150400d100310400204e068210105200d502c03501020382c84058904e683ca08004c0e40d005840c0003101c40040340c40c0b0700740000301880d0b400050340d490f0300e8482c1411025006842d40c00201904a24480020b103d8610900c4451304c2407481c2a410f00c001c1c07240d0120f69a07144c09120340c07184210b18104c0000b8107201c600c02141c08031001038001d5810000034120503001018034549207540d1a00030300740700f40000e1051084030043c40c030a1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 391580512 1250 391579262 391579267
    0xc12050a020913050c0105032202130e06152202090f040c12050c0301050a0513090609030c1a090d030c02070509010e0f090a050c040b0d0605010b04081908030604050921 74
    0x1811301c03a28024505201505010b410420701181008411040d402d40c0344060002c28142c2e4144007045007910201c1402c4100d600d0851401100200403900c60301a20320000e00915120904c400c100541c0c4585061140d40283d5034138000300d625841d0090310700303184005c0c00609892654000f2070165000003001e44009140a614400d02003858400c00350003a19401003a0308540c1004040b800d10003a900032f052191010b025000c000c18565040b8030001688a0810710680d6800c0c40c002d0407140c0c1d285000c60300f6105003a07401c140880401a4680b0400012006110000c01c0c12400c1e0020000c1513084c0086008204002c2800d80301c0300045402040040301e8080e09181c050039229081001400d0f84106800584003600440c1c00020181c06110007120000b4445808800080361800c0c0003000410042c1480c0c000516043c880018008030b41c840e00076181186c9044480f244000d801d400018450300040c004121681840c1c1c0c8401d5002100c07104580518600008208207141001c1c00d820f0781c074400 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 391581762 1250 391580512 391580551
    0x20c0a03081b0c06040206031f0e0711030304200a031e2604150509030a0c060e0303250206070203032d0c0d1404050a08010b04180c12050a0209 63
    0x10041000e0360b145094140d0f0514003680c4203941c40c0c05010308080e100760800300101d403880056020b0b03000720b1951980d10785482071f582d00000a465108644041c041540359030303d08880d03032003c0104d0f1320407980952507086250002c031101c62000b0301c2c40d051980002003010b0100c00034054482c0040501100c1b0201c04800a441c582a10b51505805460180141c032000d040080210701050300c041d60701c482d8600b203403022400e10455590040c9c0c1d400c1a40351140c0c5261006006c7c64014450039110290740e421030f4200306c2c5007851790740e00c00e82c48a2901030034902888042c031800342c018840514801484d082c074110035500024510f4200c001c4404841140c01aa600b42c8581c2c03030002010b001c01c040310142010a19198161940541c1030000d0038840c0800308111000107000486015000081a5504080c0c648940d540200a001c0c4485d00840c0340c0300c003400084400600c030400182e03100c54520a424281240c0f2011600c5440c02150544501c4400000681d90280542c2c0304603040c030741d8180d94054 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 391583012 1250 391581762 391581781
    0x40302040b060a05040303030209030a0c0e0601020607080907090905030c060403051201140d020120061f0b16021e091302041803051e16050607090602071413020c0a0308 74
    0x1090784891040c0d00c00c01c00d0390020394200c400e0303904a030b815041c016143e00d01a40428200925120003d0441080c0980401e0f901002008503004031310030313401c2380e105554010060390300520583e80b9100b9a13201500c10050400540c102d0100e440c8181d0070359041001d004030a41c0303001e2050b0340c118086400441d15541d29480c550703130240107141c00c148451000c214040460503007055040068100601000112100308207804010410889842101c11528100b0003a2015800d4400e01c0d258414003440005070401030035068402803040301c0d003051074904c2281e00704540d46400e109003103c4079846910708000e5036100364040e4421114280d002c3c6991801d41b04010440d10100c51390509000b00079505808a40c0c0181076610050742005080c0e8500031801501d54940200304000c11088002c1c1d03d010204a00400c4060003040b0716152045625140d82c7c0a81c1c69601070302a841041c0811607400c4294904122941400801001d00614103001c00601c107042507031020040c1c000c41e0521051048414 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 391584262 1250 391583012 391583021
    0xc22080105070f0309081602030f1e0d02070b042c0405030403020103180f02130212040602040603050906010e0714040510180504111b1c09030b060108010b16080906070302010204030204 81
    0x80c03904c0c08110501040c0c0e10034405005000500c50f0060084c9204821503d003081b00c1080a0b2490048804905499002e05851800410303131044d540550783d102d4100a00005012050322440254241030504185c4113003407014442d100c065020300c2a04482480d80311148400e405103000e07030701466841c9d056000240030381d90341c3e1800120f06140c2c501c800000c610158100c40c03c2582c11203141001041c1d00c0f0042010740540a269a207695181081c081003018070750060040750300b82d45042c0040d503220500c0c82c0d1904801d00c58074030f4a24905001600d2144110a03900c04080484c2c886414103440c0c401090303000e581c03041c2d400b020505c004844200100d02d25a010003d00d030880d410f10904901c2058908503001c1e1181ca400c262400348241c20384010107214202e603c4110701030000d4103518121006007400290f00c8143d540c28581000701d807195114081d081e061321050b00b083d529045138441486681d05a00000340c2c1d042d5814041000142d0f6400b00429031036009600168070b460441c0100400c65 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 391585512 1250 391584262 391584287
    0xc142b050d0503090d110c150702030c030a02011215270501050913020112110f04030c060509010c1b0503031908010801230a02040e010909050c0405010e0c2208010507 73
    0x1c0010f00804c841004000381900443c0b0309494401c141d40c003180291843e08000d1404690b000d25840140e09910b02004085d0201e58000c60807500030b91104c0c401d01d500c403620b170100603002592404981c042d440040c0c10070800ca000d40120000010b0703032000020660f0280d020102c1541055100714400450300d800342c14054001100d1140c0581001e401b9040304c08928040241803280704a201d49400802da400000076007046086240c0d9003040001e405141c2c0c1c046e010807103d0041010340820000d2040341035842403141a1500c101c0d442c040e4840302ca02200740002c0048144005201151589044c40684000344103151030031640d061181024120840580080101303078900140c07000c04a541c400c03540000d10b03040946240c0c58540b49030b0328020b40305980164156208031800041c0007025580204401800703030050750302d00c201027810003058070802c2c4031b40340124001a0201e1f0a400c40d05d4014208011120040c0d42c0001d42075000507800900c40e440403074281d41d10400c2200464201d0350440b00c8 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 391586762 1250 391585512 391585517
    0x11180915040501060f110f251503020703090609030209011a1b06070e0306060307030809030f011503060b092802071a06010206070908150a0605060d270c142b050d 71
    0x6494041004036920041c2c142c005107946c600f0807101c23605480558600d0b0140180100c2440260740705400078001c1d41c0b1111080700040c0680c000041d0040c843c000f1181503070341c02885038035980d00c0e0504202449075007007410603003024104108014500e154112010803c1304170050311503440c000c0c0740136114212100b4000d000c5d400140c2000501d50b000f00356001500d45c42036031301d40c40f4010343d00880d1070300c0c5d00c003a0f00d41e0b902c1d03281102486000e0030503040300e401c4a2040303006100395140a41400b8004000703443c603501a80600b00004d0051142e0490302e0105400f4600050500030b541d1541111040e501021800c216480300900a00d075234148603682d4000c07098100100d2140c941021117a85800c0d0401c080304049652021030103441280c0c01490061500030201515040c103800d030a0010b00e8902441600910325155030001d216202000c101c5150b0040340c801c0c6010701e42000550095160528a0f5200d11b02d864540e940189071110400701c80c0325050145420b81443c5817542c544a840c103c0e0a05 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 391588012 1250 391586762 391586773
    0x60a14070201060b030f070e0303070312060504020f0a080702121615020c07060c0203030d0c051909050d0206070f062904050112020f0d0503040803090411180915040501060f11 77
    0x70213019204482e080100b203080389815170780b0403801300e80d075003410040c069141c0030000d402024168084c0080c5c0c4140482181007003c0e81e99101000220700c5144022002010140800d071401801903214030740c41025801655030040c074240f08200141d00c500c1d5900c07009042d01c0911402e000b403492440403d180040c1b4110300e07054511082c65a2040284603c0c0b00f0000650100c9013151014010b54040c006442424008140e4210000e0882c0d080785a03807140c1d800014000c9007806206040c07500881e007000c2c10040c036041d003640030b00040d90311510040d02c0c06480d09251100041d52072150350001e40c0c81d4080202a91b140a4954184042007410244074608100c01400381400c10104d4440c06681201d0b451a904180c07000300c0d40410303c00da03015101c0c4c000400c001480050100041142002c1220200b020034000ca08801031805550448000081020000e0b01c050510803c2c582d0000b02c2150012092030142d40040c044c0c2c4c500b40c1000f000209503210005405400040c11485100c00c10b02900d03 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 391589262 1250 391588012 391588019
    0xe16021903080c0f0415030501030618030503070f0e3309130504020d02090a15060315120201120c0201020d06231003091a040b010e0f1b0408060a1407020106 69
    0xb001e600700500904081c03000080c00d036419003028000c403002040309404046180d094190064000c11f0300b407005817500c9080c030180424405140080d4207459500d81c4035141140c0301c020080710b074298118901c4090003010801a01c2c2603803075082c18a0f445034180081c1000f4980300c508009a80c0340d807400151480d000340105003180d034802c660f51103c280c01940c001400e5032640002038102541200280d04605c0c07000c24071120701010740000c042c502c040d00d503103d24203079140c2e011412101001000050720448103810310190031f1194040d4a2280149020201c084c00e61441c00115038000041d031026030343c005100081c1d484240104002064503000074a448080400d09240b141c0300700440702d2003645070080070348841e070181e4008404141c0203081d40d9101810220100c0c01403030140c0b8147da0301c860302000000e500d0034010301c082c451301502070302d814251214074603580c0c0e0680e0b094911a000206010226880030100444ea1140c0700c40031000ca601a902c0c10070105049003d8846000c690402f501407 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 391590512 1250 391589262 391589267
    0x20106060c0314130315061703091806031507020309030d05040e0417130e040203060f060a15142b020a0f1407060c120f151e0e16021903 60
    0x1003d5242c000310a1580c8180c0100c1ca034030801c80c19000141354a80e0b50001c03441d00140703503010a0076580140c600864544810f00250ba8a00644035950750049000002d039880c5070308540c00b2a0030403800790840d0542d49550f00c02c000058811207051006071f0011414605910b402c015006001950b4209545058144807002c41c01400041c406003401c07503145c088030000500e040c1214826000180080c9405444010a000d0402c040da0284e2003072140b0400300e0102d66408400e2030058400030070900d0381c140346c0007030075000d044100c1072502070004e224080b40c00340c00080e004140303c8044480134161081481d1803c0000da44941c40c00d0201d41c410300c41065241d03000900360080080c5400d107001c1019000d600c030764685c45196001440c55052a59900801c0d070000b903190300f5110602002d0090b1000600700104507102010068903081410b80100002200d06402d020002c0d241c400c0001415169443c94030b411106803250420340c03e2450036034016941c1030000b01c1d40060004007100b034541c402e8a00 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 391591762 1250 391590512 391590527
    0x4030c0320060406050c0114060306130615060c050d08040b06040e01020405060703051b010510120203160e06040623010e0310050109050411060703122408060403020106060c03 77
    0x20000454a486030340d000e90075034070020180324020701d810f40d41c607241e00c8001d1040e0030039919580c96600b0201c0303400202c0326200c0810b108601c00740091105658503500300580406941090310040d0b0b80b041140f01040c2c40705a664050259925404483c90301031616510b80340103103401004001517441400000383c3e402081c2c43d00400100c2e004030700680841c05080c020b118a62200394418400a40b0404041d0444080d208810703584c0c2d8840d248410140d40982030303900031903070341682001c0d140e8240282d41c213102c021700c065030010b400c1301c1c0580b89559071f84ac0c414030180c000c0c43c0480f8215007041010f00e098001c9c980580b012401440d01c001200c01142007001c0210451810712268101003038070798904000400b0344d0f041c0903809000c41c0d41e58001ca0b00c020f040644041d290400c0000401c8200c4c184001183c000c190706544c1c2290740030700c144240000f4800000100103003441d82071400c01c2c0345107442185010f05041c1010781030a041601d0082d003118103a0f80100c0500160403010b801082c1c01452 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 391593012 1250 391591762 391591769
    0x1801080d1202070b0105010f20100e0a080304060c110102032703070201090e0c250c0609061d120f0c0f0a03080706020d0209040507020102070b0603011e0b031207200604030c 76
    0x8c11a02055142c1c4056074501001481807030320b00581c1d0520540410002402c141500248004003d01c00d214081281c503200d980318041c100541c1000450001803403a03201403030108140c0340ca05158095404210b003668030688250038207061820002c180600e0704400c01600240340b07001540340048542c00a03011000da84100d01000c000307100003504103100c178412541d0004202020f0300140a85040301d02d075a0b00c18040a0307841e0421142d002c20920300403092102075800c56151002212070555603118074401c1000c610742c03c90003c110040d00c916040003004040c40004014003104090351080c089141800b5009500c90000b002040010401e230004860f403541e002071380541e6071706004c00c60001038072429458640040c039041c10080495419400380c0110341c0310b0500540d640e20399500300f42c00ea074005090500e05842c03035600408101403603401340c4503200d00501034981040913102c0c41c002581040b2400e5491103491a141107034400a50785850340c4140841d041c500701401c54032464802c240340e01 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 391594262 1250 391593012 391593017
    0x7090b0a03031b0f30090915270b03030f03010308070507030c030c090f06080601051003180b0f0a1b0302030403110a031d0409020f0f1801080d1202070b010501 70
    0x1078030380c002003249604400e258011007100d848465626240044079070200c07003030170120071500e0a03810401e0040d8444204a65a45c3d03020061340c10f102d00b8030002d1810944080c190b0b0340c14440010001c2c030800c1c0300c2041007810030100300c0100d0401804401d407045407105a11a0300f0400400e800612842c0030b1780d0550340c008400780c0c1c40749410301c0c1851030881c0541018007104c01c0603030000f0070000388040d180140d6084030740a00840c030790740240341d05031209405a4800b54010000600960800c0b450400d4821528034012940c10a680ca41d604400308c585c000750b5044007443c08103e1a02d07000024140c02410000d0f041080c6400400c03d40119101c0b80c000404164000011900745031090840440f142505c41c2a504015002e140c080c1c64034820245500382c00010b080c900016151520504e4092600075101140725045001003103820508403404640c00182c0c0e42200c074240000d0386d642030107001140010302c003e164645014108916450003d05403a00401107000020300c050703181e504607442070 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 391595512 1250 391594262 391594277
    0xb0409080a080403140f03041109040f02010f0903060609020409060b041a07061b0c020906040905070b0c011503060b1903031e031e020301030b0f04050d140f0d09030207090b0a0303 79
    0x20311301200d0f078180d2880d02c0d400000d00461030300c506201c1b0b00001e5010310310070200400131035061001d01211180c22070f00a000d4001c054420009035019420210754074100e0302d45413030400d803a981e071101100c095030003a10300701e40e01080900c0000a10302c1114040c03e01e0035051400c0a140082040e03c40c9140b01c070802c1c1d4a940420400d04105407a0012510103840600003503501480c24402440c200301000241c2c81a0345400114105013024800c000300d0b02e40140140a08a0900d5040c4103181e020724030b0031406658504910032000d00702200c21015500c151008900c41a002040045451594400034066010304904200198111050701040e625080d8500858010038106500400c40184941a00c1e83e08941d2038403441c0c0107900941c140e912486c40c06003251511030002d0700700c0f90300315001486588015110521035001e800456032081c41000042c1c64118800d00b00001c0b500307c1580c4908085d140c4000504041d01440501d014000400d800c1140a5481c00021610306840c40082c0c1800101c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 391596762 1250 391595512 391595521
    0x270102070e0103050607091a0a0c0f0501090f03030f0b1e010e090a06030c08060412120605220e0a120c0203100e07030b010e060102030306040c11120c010b0409080a08 73
    0x90140c040105200c0030300640710b40c0e50b030501c0e43c0c130303008121000c4d40000c0064a000c158403a803640480780c4804001c1c00039092a107007040595494440d00c0043d5560900303103001d513000501c00d02903500c680784034290300d10101407980f43c00b03016101402010780c2d90a081c00c40038203140d1030303211101442264140a440750b9902500040c2d44140c400c240c0035420400000030040c4441154201000700c03445201c42904480c0ea17100301a407079100580c3c000b0000c250155030911790368071425140742a400c0c00000050b0550751803002070a0500c01821011142c5180021110926800c5c45450030744003100021345a203240e55541c40000c81302e00e81803103082c80320f004060015914104803120140034007070790400441000214039550f651441c07008840b104182c00c00416000c400d01c540d68010401a001181562600d10401016140e040c00003c208615099210044101041803000c0760707603014038140e40d80311002011429540400c0c01603028508001700c4000140f8240b0440b00320083e1484c00d0a400d458 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 391598012 1250 391596762 391596767
    0x4020906010c1703010f0506090f090c190e0901080615101b081216121e021204020306010b07020307030602130f0602160603090f11060904090b1009022701 68
    0x124200c02503c60401c44000f403070402076040040d810303503520340c1c0c020007440d90300c80c00c03c0700600c03660750040c3c1c010302d110071401500c0c2003040340c00b03410038a18090a41801c56001d80100c1c01d12180380408006480384010040740d0400c50f0314079015101e1503025003c0c038a03100c4190543c200d007038048640030340040d040b8000214480e00500c8003540d0810580c0001000c40d082c040311a401c2031380c401300d5181e602c4000c61400840c0c000e580d10004459212007080700d4003402c1c1c02c0000c1404025698004004c2c1101d0341c0205145d100918030301c0041d462a00c9181001c1c01414500b24050700020985041000140056980041c10908680d4001c00c0941e441070a00000011250258441502d9400041300814080c4d001724002845480682210400b580d0b1800100c00795806000c0282569030300c11a80c0f001710706629403514200d940a00720621300003001e0046021925806410303151501ca40f802d0110b1134080c5c407200002003614510560404220421221204840c104003550380054004209510790 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 391599262 1250 391598012 391598027
    0x4060f2d0f060608040b011520070302040504060207150618150b04180507090f0b2a0703052b0804050a0506151f120914010e0f1b03060402090601 64
    0x9080741070074411681d441e000a48105001c1d00c045030300074a0385c1c0000c40c60301601c25100b50240300e42d82c0d84560400101c600f8090a00c030481410030a030089940210141c4c98502070306014030f1040c03000613618000c40c200640e44052075405170700500c0c05c1110401407986441100250700c03951b0000051246140a02003464003003a90220700905404180052102c1c140b1429a03002c101e1a8001e001d43d81d9610340c11180b4604501030140d003d1010241402803400010140641035a01c005503483d010882034036001c5948048451541ca522421040c420040c081c064296030b01e020704070261843c030300482601c1880300500d8488040140f40e00015003881000c00c540f000543c0c00000340c481905004050f15030358a032008145004010318036045901d4504d4007660b080001d425a929400d082542440310040c00d4141c0051320020000802100c000b102881002c28510030328000f40102d0420710303e07141c01c045100c0c02218852442c02c010740b4040c4c9003c10740d00c0e80142e04071810b9030207560340801602c411 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 391600512 1250 391599262 391599281
    0xc020601060e0f090a15091b0807110105090c030d03140c030915040f030e0105070f060c050903071415040305030a0f03140708040c05032d0f0f0604060f2d 68
    0xc08180244a10031401d540b03e01d19108003a0040d200c50fa407502c00a0041c5e90a01da50107400740a040c01e8500f075203205140c2140c0214041c9810546044be050005081d50b000760f41d100307000d4000c101d0400031032808221558151501e130500b8403400000d0140b200011400404030306280ca00003000036061401801810006d001c0d00303000d01c6840c14a07050868901d091700c0c1080740440d00040340b102540d0b0264007a16205076000192500500040c1d07039090107450100d0b002c0d000c0c01800d0020344429501488954050102c80100400f540c03518000c00c8084001c1a1040400c000204001e0000c00c2c800b2084500301040f40c1414042d22910840840040407548000da070625005400e1150143c0c1c0010282e001d40e0144410741e0443e600d5804040d2900d242c0610300d004142c0d58400050704c01000e08214404907a00d900341c0300e14484803980380b8142210041c5c0503149800040401080045a10541450405030381e4200b00f0940d00103c0112401e0710f285d000301b464030424003506143c11050b003201d140ea = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 391601762 1250 391600512 391600519
    0x6220f02120a0602041406030105031f0b060d0f05130c0b1303060603080912030a09031103032122080306061602060409090213020702031203191503150c020601060e0f 73
    0x107070141006002900b06008900101c040c5d411000702c146401c8003924181c450040c040d206003030007101c44043c010cd0260420850300d490388082c209a6440b030020f060b449007001e0010030045107200303501c0308840c0000c00c4242c20701c6910182c400414183c80860081e80c1020b0313030640c0c0d6440b0764049900c41c2001d80e40000c04190a2682c04400c014442000c8c00101741c2c19600c40c0528510f003501e841d00d038020b00b808a000501841010000f091860f034415101c40e00150a0381e02c2c050990103101301d5449184103015080d4181000d210407a0554820001c020f410160351b100034220b207a98141c202c0c400545200d02c116800700b18071880c4c3d18013a0b120308100f0350080681d0f81c0d940d6569040809445068030907482016107070100c904030302c0d490088a88d1103a0050242440c10a0705011181c550406840d400c81483e0500b1600c52130700c100d03c219090315903941c428070701070307031541c6840e18100c44030341b2010300d2aa081c1031721a0a0316800041242c151042400c02d880f0103a44200071480002d1141c008560 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 391603012 1250 391601762 391601773
    0x191a010909060e0f1506041d060a14130e0607081b120a0f0f0e0d090e0402090a0c0512091f0c0801060305070311071b0b07030c08030601090e040b0906220f0212 70
    0x1d1102e606c1500190000110b036104070b152703440390200040303030811380710305070401c03045a522922518000141f0314510551000015990420b0040e43e4940b0001f2103614000c2481e4030240b00e07041d0340f0f2440005458075100c016504e403102401c0380204001c00502281c42840e2112440039151806410001a00d0103101041044400c5101030940c0c41080e1901000890301008000c118810981c0104c0e12480d006040383c03030562184014240207000c030705020000c0203001e211440d48000300c0615103014400c00002081481070b0801425450031040031140e040c540382c00f44c107000042d04002600c2c11140c4c1802c0c0020b00d5900c282c015030240c100101000c10201000596004020102e80030110704c400c003c030803040c03e40d180c841e540d01510a02c01c004c0c0100c1d848000000016065000460340f101042c508054019514019915024004c8c0c0342100d140d1002402c102c08024100041c59102611803620095a001c06104141c406048a000760445841d185050195115264044805110030702200ca = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 391604262 1250 391603012 391603019
    0x60403030c110f0304030209090a1b05210c01110c04140f0c0702060418060b0a02030703020f0120091816020f0d08060108191a010909060e0f150604 65
    0x300280100062440800c0c854922080601e00c00100015041c5400e00114580760868081242c440402000b408031445078001c4500004c85512100101100441c20300c20164107140400402d255440810080801001c910344035030740b400030b8010003c12084c200900c42c0143c0040741810141e110071183e40040c00c0501c404125940c403a00c80d4130a4a03291035620054603401310996040c41480c0b40a0740c845401d110a00034a030f2140c80c000386100300c0590004e1065651440f02007a030304010540b4016800114000007416018400c1805490924008110f09000f8002e6801c0304070b002c00e002010048082030340016a11100904660310503420004285407074100144c0d01404503581c011001030150304846281c4000010f00305a20143c40d4984000a41d00c0c0e81c0116030300c03000141b080c00c9107060040c40402d1502280f00d80b02090840c4035481d412144220009002003102c0c3c0c0c049038220f8030701042007200500c0031414a0700041d40c501d51034466151a801d0082000801507503e80c45440000c001 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 391605512 1250 391604262 391604267
    0x2c090a1a150a020c030c01020d0f051303060506031905060c091306090504020a3003050d06060306171204030b090f0f0d080a0b010917210702030c0a0315050a0608060403 74
    0x8101030040d0f9400c039a80d8250501c1490b403035032941c2e11020f0140e44840b0b54818010f0040b81c044500440c103180c41d41c00c02c048030965401c2032480e64819544143d42c0c03003e00240b0305040c00741c00001c0040030f102403146040c40eaa5a9036800c4c000b403004003040c07004212400d041e519655555004404280b06000c07180d210004a0002c141c02d5070304a214144002001800c102980102041c00b41c084409181411400300018824041840e0850402804000c40d0100d20401d00c101000352549980c001405c0e070811500407244161111140043c2c0c0c0a26410b80e8800003010444003681d0340070b801c00c02c4544806500600d0003a02c00c000c00494040c2c18022043e100d07000558501c000007503520b0481548450b04034800b1113500300714441c00541c00010600c40041841444450002500111501c4100c090544102050032112110306600002442d0055103010840c410b00424100c83c40d41da12407659071400741c034518000044140c1c41d107171000210340c2c0140e03502c0b0400601a04064078100d20302440e00 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 391606762 1250 391605512 391605517
    0x9070302070b0103050d0e090903070209040c030803042f090a0c0c0803180d0f020d0e030f01020f220b030112061d0d0807080c160501060b0a2c090a1a15 67
    0x8071000071825103071f8030b6103450000c0700140a04840d00155140c000b42d5000d2000c811002801a180003048190010001d04220001d501c6640140400c071018510310704001c2001001d40d4144030329030103402d88686140da884903415002041c0d002e0008400c6080542510410a40034000e0700c944008020420300c0010101520050381014041e201c5104080405a4078001c0c6188204010380c4402c031000605400381503010b0b0030b104010300b1a40503040708548a03003a68412541d411107214045103078215a90302d0221298110310400340280c5440c140041520180414070500311a000b09211900600a4507030000703068448d010201200b80603601034403a52644a89108400507040c807000800c036501c2500c1c15401000e500d07114a03d024200303809041c0301035441c2c41c00c0da40c035503a41c407001a00c01c0840700100518292505d034000c034440c03280d0700490f02c2000402c401203c4100e0042c0305c00c0c00d0381c4a480040d40108201400101910711820041000200310720391500220076400480d84a88500c01 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 391608012 1250 391606762 391606783
    0x40606090306061a0a0806150c150f0403081906050306071d0d110105090a081b0a0602010c05030408071b060e03010c0c2d0c0308041d07090509070302070b010305 71
    0x601c1483e90f40d11a010a001520441c50303042081440781d04085480340c080b8541020009165594542329440c0b08402c0b43d200b80102070395540003030400b07480c0550703200c1d02c079078800c0078170700c0d4030510349055103010340001402400420b1750702c0504002d20340c16006a009178090b12001c0e0845041c2d02d420903000e0421000220032215003042d10414212500c2d2145140781070f16800a180c006032503408005503402c1e0032a0030184d52103807851030007007050f100030400b0381c050000c000d610240765031190f01489183d050680003641164104a85d108950b038128003100d40065024081c660303221042d06040000c3c0544864621005040d2680003c0e01640007012010864084001f001180e415090584080c05034210041410b400c00d4804420404c80504903403007840c402c0e18a010064441d42e54032800601508116001d140203c0d0178412482c2e091203d230000307850a9203883c00da007001c2c0005441050140708a91054a0080c001a05680300307805951860350300600c00052946c491428075102d00000c079 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 391609262 1250 391608012 391608023
    0xa050105060715020d0f0516110604050a0308100b0a030912050406021509190b09061006081b1b031809071b050c0d0503030f07051e030a0b0406060903 66
    0x140046641d00d480c004485501c0c0d403020003181e035401c08941e00d50107500010050b010181e0780300c44400c0302002c9401424030a515085100221405058024194402d0100c045c8120b602600c01c000c002000003951034030403905428a01d681369034030784a00344008401d400c822000f0002082c2d8014082c0c1503044290300c64494103000c90b0303030f420840049a850060784190f00060384101c02030f203801070b0f103200444d0304155a80b0584600c40c4042c203994004a00a14040340c2ca80319a03800c01089801c1442600c0d0040410a4a1072100f490040d00400350100580f850f01c0103c6441c1c2801a011130301e40482e042c450900482100c1100b1514031151a500890040041c40d101084020042d1a01d0f0341d18070302c00da11949455074000e0141e1503440c0060800c1c1d2048035540716130100140c60380c1d40c200c84d4600c0c41c1d20440042d81c1c0e9162401000c960454041c21030000d1000034005550190200c0c680d0311070341ca51071043c06031203a65080812001c0d000301060301707400901d424004540c5a50142d44442924000c1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 391610512 1250 391609262 391609271
    0x1810020105042307330206071206150e120f07030201080114061b0123041a0c03130314070501020c06090616050706090c1806090b10080c12010303080a 66
    0x10320380812400d68802155a000310b0307810320480861820305d900d00e6003611780328a4041c0004882403000e0031103840100140e44040c041000142c0e01c0a016415503a000109129091174104559205141d078040030381400310034a030001e07050700c641c1500108000300504039101040d21011040e100c0c0f0842c0010f031f0004110000220f0201c42c2c40e000e10308000005030030b83d460706030340c05d10540180c801c001804416540f070700c42c80c20f02a403500f02080d51a040300303400084141464640460021040140515004490002c100d007100d110b4090300ea015680141075112040140b5049840300301a003c480b111000208010050110550103804100c10460480c0c04a48072a0703082c6687d100102c8030f200504180d0010840c4080c82880a840294031031b0784045280b14040d038560700e045695400c007000300d0034000005102e01070180900c00050012070002c1025003041400300701003110346481d5100b8001190040f980007200e80c01154507100c5400391049095171240303002005c03140251a20190103007007 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 391611762 1250 391610512 391610543
    0x81b0304030f0215070804060518030a0c09020c010f02030a021b1203161707020a02030106120f0f0507080a0b060a0b0f12070311070302010915060f0b181002010504 72
    0x10840301940e41050304800a020079038208071034424051aa802c540806001c00c4001500300b03800b40025003c2c5440d41a190203103c0007805d51401c85400300e074404c0d40a00d40320300104200100300025036240700000350340c40c014001c880780500054002415968800401c10590240303603409811818130a03001d8416880300110003a41d43d0103400303140c4d00045000c101248142500c1d4909518501c410300344a20f1403000c0c48040341c1c8041040b0340703410141c0c01006600d0114902031085070064102044414002c0d025500c0345c2240850000300207107400d11803545c60b01844810001c0c0402442010100c0315100040c0c81c040c0c1d8481c4003540c1590142185850111b12105a40c0c141c6110007580d100240c20191107050307c03000900e001d0460070526039a1507102ca00714104000030420300d40a034002144c9240c41d442e0410300c03c0000d407001349500340b07031038800c2c4840f0307010301c1a0408444a452030140c54114245820302c040c800c1d035829582c003944840c80b04580503010741180384964040d010700c4105550 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 391613012 1250 391611762 391611817
    0x70b06041401060507021807020c131e0f090606030c1703071205030601030e060108030a08010519050909011e0b01230a11070906030606081002070f17130308 69
    0x4551500d01c0000104100500c041807141002c1c04c0c1d00d0b40010080b0281c0c50031442c00e201e801c00250703242001608651042c60340390800b01d000d007401001d0000e0400c09020341101b2203400380003071490340603000d071113081094508005410050b0380310307044501041074541e80d260000300b0441c0e80c400c140503040144e04140079040c0210076604400e42007256041d00c1c8200c1e0204880c26032006000905140e0f548120141101003000b20310302900c058002542e4942d550032010305140e0050f4003162150103203040c0290003000d80540074044600a861085a9841e00b03803105001d405020286400c0d101d41211480801c226608010905e007030a0700d800820341115203001d01140251482d0801d8030f4030402c8101d0205125807a5043d070711441d00140d4020586403031400d0190340d0298002d980e0303140c0b034140510101d007042c8902a0040000d050441c50b011699942034210000850041e0402c0209039400c01703c0007980084075026104240c048611603101d03c0c2c0748540d6000f01c920150b46541c6510340c442e1200 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 391614262 1250 391613012 391613021
    0xa18140a080102130b2d1c27030504090e0703020108070c0b042003030f0315010206010f061b0812010911070b0a051305060907050f0607080a1416030302070b0604 71
    0x8002c401d964109080905d1820a90b1104c000350450004c1e2903d10649000c1601c1c1303440741100e4a200c51507454450381c55910345007011800c05c8040c10700d44050100b8a04085940800b00d0100c0303107194860040760304050303d41c0c1c0150740c007102500d402c007030132000f4503140031070f0300019203100340c80f9181c541c1c03a954800c5803248050103006190508100200d404220356100da4400b2000c5070844605c0d010410011a0071500804400440504080140102d030113a42801000c584001c0c4002c3c51907600d82071122004074454800d003424000c4942e0301c00b070b07082d90b018030040302c581d001200b55582e41000051004060001d1040070b1450345880b64171040500307030004807242290400d12040040d111401403000408000c2e146c4504010b50015840002d042800414450140080600122441c3c2400c2c0143c4050701444148030304003c02240e00003030744203000d403074152a552412094000300407054107514854078846011300070000060708205a803540042c02018460201060213488007801d10040e603 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 391615512 1250 391614262 391614277
    0x1b03061116170408120d140708070c060612050604061506090e0a0603060608030403120807171008100e011a0a03121211031609030b06060a18140a080102 67
    0x1500544503000441d0303455442001c5031000344901460180d031030500c0307840c0040750310a41e190004003041c40d951400072845007e90a9121225042c403a141494000b841e50000420359000d2099076202681441071039400382003d48988002c0c1526150316042195480308211801c03a46503040c4813090405c01d01d9000300c0c030100c0721591100f0310034900f011481100c0b480c001b44500701942d51114004049200d03070240400031b017510806550359604605014219013002c2a00c00b00f40407410301405002a401291840705800ca903500401c1030703c8116603014581002d9001c3c200c03911801c81600a0310000758008a07050742814000c01000200d0b00c0c07048a00c1800030509030f88101c4441d0300b0400700310340341c075a50101e8405141680b4001d039000500d50440316000c040070400c04c0d011003080300082c1c0044003107440c0045405c00e01c4d0094903603034a064101500611040c0501804100c1e000020300a09500500e643c541540d05843ca40301d0740d40d2150030549000e01c0f480750554030340002d001041032003140c160 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 391616762 1250 391615512 391615537
    0x9100b090a09052d060c09150d0b130b0f0904170903190605100b070507140f0604080a020a1203091202130504060504030806061c09030306031b030611 66
    0x107944854019008000c040000d40f034a0240441548510b400a21800c038001e031005818103d40402254180c9403440050010580000070400c0b082c0955030120800c3c420151100040c0e81c83c003443d00d02c1409445801c4550790025000d888418844040741c120380d030104025078030904101040b00800170100002d540181181c42c41c5107442c01032501c144010100940d02800712002141d400c156036103a5001c40c88252500b59551062158000d1001c001704000c140042115041410544946880392402e200310008040c041482150036104e40d0b180a4003020010185521a47d59144903a29504c00c6c4500302d04c5040c2401010030b070039080c80306081200d90950348440b00d01e0700f421904001e540309840305030391104c50050091031141950090070b01c618403580303001c500c9041616010340000006428248240024480300d8140e901c160110a44140700700804110504c140c20145c0003040e141e00050315940b41459501540d00c0401410b004aa1254030b081165090b51024910300780500a0707004070 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 391618012 1250 391616762 391616779
    0xb040f0605090c0a180329041109070e0a0306020c010e060f0711030d020307050d0b0402090114070c09110403110307060903030f12150f0803070209010302090a060308030f09100b 78
    0xc0f4541031000c1e044014460603d2101045075205120f8130061310b60084510080e262100d9100f03510a030425010401c4244035031400c2d0a243c1e0314050441c1c006100c95000e6025980010700d154890400c0f03100c0320b980034050310350650b200d0412102035808291580707215030074010114202d540c00104540304003403101061400d80c0b0b451303104540f15069410703a110b0314441400300c500c4a501a100441c010100d82e202c1c65514503002498100780d80600240c40d1082e481031008909a07600402c205a04140b05489280d803500c880c0303421010715032503400480d20180740042e114995030201c1c00910540303000d54117824000e803a1204055031141075004000c0000d010360001c00009001d80c41c550311710303003150804400c2008038031144001ca030001650365811500d111010000d104d100d05075480640300b002c0145113010219000310303603541010300c00240a12094000240d016200340d0020f0060740c4d0005200b940c90070400405c2000d604181d41c840898001e8807225401d410061045101c1514007505041 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 391619262 1250 391618012 391618021
    0x10c080a050702060d0603051510060e1315031502070f0201140d090620041a0a020f0d0305270601170c12030c12040f12150c030b040f060509 62
    0x1915a0414200310080c03280600c076440059842601800c00c00c15424400140b0034039600703201d842c10b84032450a442840304031052040350700042d0090302c26584642031900c031925680020ad05070170940c1092245a51a001d05003801c00c20419030802103034024640040044001c0690004a10070b80200500c610680c0310b44030019402011468840001c81c0e80742c5042440707140402040d5614a44100c61042e510340001c09400781038030911140444e0302001600306402d10aa0300414402075113003070140503003c190348440c0340c03007005400d000925003030a480b0094903510016018200c141d9861100c11400e039030301c01c20712805c00e100d00100c201e40c1d0020445a440d0014444e004520b001500d501030203001c04000395070b220304030781c00c88025000e40150740d158480c803845420704100001c051520201000708024900b04400c114040e034030500c456080e200d4692a002d0010321141c003421541c142812406103000d50035510403140003000340d1701030100c201003c00c1142180e5a41c010709501428040105 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 391620512 1250 391619262 391619273
    0x1060906090504090f060e0c12030906220f060f0e061c0504020a0b0406020f01050c09030d0809150109020d06060f05270a03051c091202040f0b04050a15080c010c 71
    0x104c0000c2d0080b03c40108807101500c910040e1196a4400304865000c940c3c8428a801d00c500ca4074403c4880502850a129840000414610511001c400402a944265600c20071644110001403042c0d018942c541c5a5450024002c42e8160b004803010810b22a1500e005040050403103510408104039400d903001010744600040c20094403c1c0e0b0000306001e4007160008a080080000cac00c10354004200c640020b0043d1429120700070a43c001d4a5021710901483d900d0015074000c40350502e040215490351400416841c019000c04502490540c01c0d0000030b00c050030781e00a02c188440c444007844010345468064400c0b08401d0102c2d80010b0040010070004034250006d2130b060f031040b40b10407480b030b200d806c0050317142d0186810599554214522640307150070310b0640f10844051030b080c400d0845181201141b402da1601030081c1c0100e0719240741160f11002c680c41100d18120042c0100083d081510811000701203241c0c41d0411405604008500b81100161074040014169520b500380000e07542c40 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 391621762 1250 391620512 391620521
    0xc072d0b0a021015050a12020a03032a1208060108070203041a070c0602030301180b0a060f030216080306040f02090306040204113007030c0c1211070902030f01060906090504 76
    0x890214012000c52843c282c00c0c50080ca00d6004090301919411030070482004038005680d4403106800d50070b503180c00b0050b200e09118400312078040c10050a002e600072040d1b103224009280c5501c1042007040411300300000c03034258844c3d801c0d00d6903a0445c1c1d80e03035482c0191001d02055901c02c0c00f5070b04c10320040010349080da86240401c00c04002203400e106c51603503a840c812115400100c00342e003010005015480c1d8542a4010540c5c1d4403d01380905050807000c1790b178400c4140184420810355104030301046010350104c1d080c7d5035070401e081c1e41c00600c0b414425015001640c40910441c1890540d94200000380241c41d003852000b0041c10461b1143c0c0d0800c00104109003824400080500011340c07911543d1000703024902d001d825070000c00700b00d40c0080c03944840062162041c103181075400d0185681c050f4850b0000c03a40311022050800450b40d003074550704108660800180700cbc2950220740d408141d0051130003039010704002c03d1540d0b00d5940550302034481c0e00907500041c1041c0c600300007030316181d0070 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 391623012 1250 391621762 391621777
    0x2003070c12111b0f0324151e0102010e0d0207120f1b30021201060b0a030f0b0f030d26130209010501080615030603120c072d0b 56
    0x1403041042080124040c1041c54628400305a88690568004242480321804c5a8a44114080c10f03404c02c811101d0001405506c100d40300c0c483c540400501524500100084c0071840200030b40001400702c00c0c0c0c1060748140164041c015428125103016544000440400b20295030300038107580d906000c52440110f10001054440314100103007800030031861710700c060f01c06803000743c030003021340c18203d540c04810002c59103c440341c1d07111041c0c0303465120114400d020242c0e048401c010600c50303101260740034185541103804a54000216042025059841003804a8500109108019521041081c0b8605026134944c064000c101842303042486000b1080d002088044888012010201d11440001048031024800303064203644400354035000182a005003402d1070210850700e01070010504803410000c0f40c0c00380c9600131010840a81d004c0c00500d0020301da18000a031100c00400c0841e61742c01142c402c00c1362504c030700811803015401802120001084800001e071007185440e4211209600812 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 391624262 1250 391623012 391623017
    0xf09010e03030f130305060603060705090909010906020c0709150e0610050d15030308150109090c03090b0a05040b1503030a0e180c0307021506030c040c120f2003070c12 74
    0x407400d40c80104005044c00340c0c0281e03039090004d401d610b4078601c0c150340503251511a41c0f004040001700b0707a0100464090950a0301d407403036170340c85501002e40034020021009014500100b041503603454000b986e44100c0d00d0701e202c240070b441d920001d010410040c0340070b008003414461000405500701b503a0700e05010000c914000c1d14141350500f41c0c8040780e00c0c9041010020304003540410034958000603080d0481003040810504011103030003e404109240704a50070580c48040c0b103c00507000b0745c0034070003050300883c4031030740d07803801304e03a114000c1a00310740440d50102000c0200e140d0780c0015508443c00000540250715244880300107855041445190660040644520751282d1070000701c15409541141c044c2138903420511400790908280a40058a035644c010400026990015a61000c05400d8070002449401e5810483d402e041c541c8451928900302401700751101e1244d030000780340e01c0d91410071500c0e0441c500612109031000380d50240014003400c101c90023045501c020604801d0250 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 391625512 1250 391624262 391624267
    0x2091c260c190605060609030715170c040503010608060114130605030f010c0807030902030309061308126d0519030b07030f06030f050c150f09010e0303 67
    0x1507003a545441c281400d00c0302e80c5548100b02000308010742c00b646421100c221151030820312003e010a9440074584244015902d044042000540c02014110b922440804140e405498079803608141c03548184210741c0079600e00000068548004509203040e1450742607005c1c4001040400c000c1036455021401003056a00e507000580390398104103003008046044000300c1d0100928001508440b4000c11201c10f15040c064070500681d03000c000c403588100220b50032130310341112010038819203030300da0060903481c812241d901510241240140c800e001e1001494111521000302d50303182da01f010504201e1707c0c0b07038007000481c01000550095001c0c44184031000380840d44042c20f0030000d001c0d6041c9981854109600380002e0030a0702e02c2d1400c101030f041e15500b01c0c9207135541e490351001d00180842c0426079208601c50800c095900328400440d008400701c10418180e00300140c84d51105030f19184503580110a60518140101c1610300c620491a0b00a06180302400191401c0c0094903c4a6060008 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 391626762 1250 391625512 391625527
    0x1020309071505130306090b06030616110307051f05100e0a020d0b0303040b0409060503011418071508150a0303090b13030b0c030402010207060215060f01050c070902091c26 76
    0x5036041c000082d40111b40100361401a42804a810071014000a0003500034804000d4070308902c15552010440e2407030500300704114002c859003580503d00008002e401401540701440d4001080e85a071030066010420441d115840943e616a281e07120360742c03001c0c00f10000a00384051641c050104011407140c08151458403200090460b80301703802030403102001180232310008119118510140c1000e4000704440c1040311881c0c0c08854005000941611001c500e11100074404e0185d40c0040507031000302129881000790181c00b0240444017000119000740c0e8242c5540f4081d40b24000301c6c2d0f05a100c4094860030000c4c2c0310003a600400781e1030712400100ca00000000c00003042070344544120f104131500c3c0e042c42d200090609019034407480440d8800300e144103490681c4102030f40c10803022103d488606400310016540741c019580c0c048618004d00d0030009402d2080d03001441040e0040301d40225002c104011400042c82145014080c074080880b84c00c00c1003085c00001c12260702100300c403400c0408 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 391628012 1250 391626762 391626787
    0x60f0414010f150206060a050f120303010e07030e1c030e03120c0408192012010f06030606320102120a210212040b0402011e03050f01060201020309071505 68
    0x1c2e0301229220303080c008100510843c0b05580f0701030011900c082c1070241460030024003400d41c513014040c810325901007407440e60b40e1084103410200a490095a40301c1d0703174506030031841c0041140e034900403a09202c450380190501144c4c03440d1540450b035402002500114045000b003850501811962100b00601c03421001840300151051280403c0700d1b9650f42029540713420402c0b4010b0210304082d0350710280000400c0440c20500d17620040740406201c42580c8001207015500001d4002c05520b80000c01000720482d03001002030324010b000a100e941c0e92940401d440040301c3c001000443c83d035490400200c8100450040c15810505c116140800030361010380042e03000420781c4000c103018030b806151034101015030300c0486240c1d44045043c80d40202c8414144940107000502d41d002890004086a0054888500b021008c01003080c0280350071401030014402a00d0389881c103140c8034000280316105000300c0c1d00c0390940c1c034064004245000f00c07413a112250340841c9400d1000c180801e94070f552 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 391629262 1250 391628012 391628051
    0x1110a0807020a091e0f0f0606032c1f090b0711060901090215090406030b01080a051e070e1e0c0318070609121412120703060e060f04 59
    0x180a20100d59540340c00d4410044011000d6011003240d500301086281c0e020140d0888114500b01643d0120303100c6070580c9240c006002401504804600d80000440d6103941584843c0f88400c0c85032800d8010714800b45c1c14461413894111002c0168402d500c1c0496128158001c1d034030103152000080b0b04900f10741c2c1d9025020b40112905000a17981e0414040d40c00740c2080015080080c10b00200203000b46500843c0d0070b841c800300500c0d4003070300c00900061a5190369103c0e000440d040003e135070403540c481c0b20341b40e290740418800b41c0f024820500c5050038405c2580020714034540d0b8000410425203040c008000d0f074000181301da241c1080b04a9280003038803807006154807a4850401059481c54250441d00c0030040c8841641c0c4113030700c084c000780610754100c110340c8141c03140720701300d03020030001d9245c80d042e200b160200c218980e00070044241001e0f40003101400b00040e41008001c010307070700c100f4200d08455540c45240d216014003c0481c0c00307070500e06c003107041030440030b000817a03101420010307105943c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 391630512 1250 391629262 391629283
    0x21518060d0219090303021203090c03010f0b011d090612100218090f04020a0b0f040b2106061c0203060d0f030806091003050c27160e040b18060111 65
    0x6900050f0a103c0104828400b4503a0b841c5401c02210a60031501c000355201c025804e04070001c000040071480481d801c0101d0395001900500a01555829820503405404080c2102c0c0c04101075014042c1d5a61a040c2d00b620b42180151103c20140e69035820031610700c1c4950f981c0103c0d4000c082a564241d10705000601c180c4800d00b070078031080320f402c03803d00c4001036004108954010082040c0001665520100707030440d900c0d280d0710f0391514002d80300805940315650000840c42d0001072959440c50300c8500c1600c043c0d141e80240d014276030300c0d00c003400030a02c140c00e00100e0b000384045468042540c941e003d540c0181c00503044203000c07407860340d80f000042001c50060f00414104420480d00b86030246c1203650000030300401c8440320389559a510b548032403444080d81300306c40b00b2031460040702807104950140600c0d020311841908020301040451000c42c40c01c2030000322010b01120b80c2d4241400f82c0c0c0920600600003a15103960407907a01c00112016110604009180500c42c03c4203408209523000c0 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 391631762 1250 391630512 391630537
    0x705030708070c0b0304030f11010e07080a110301020405030a030c0515090a110f1e131103070201181205130305071d0f0106200a0506010e01061101050402151806 71
    0x102c600300d040500c1040b490707500c02050304000b00104070000341d204007070a400240718144490454112000f0b68003401c0034000c0b071a124880d6150020703081000040035003503140100c01519121704d00c5030030b00d4280d125901586426903c100d0241c030000344640c070503000717483c0981c0680d032480c04141c3d040c41c035446007030340c90a41d2035000800e448144000c400e001c004583c000c88105180d1303400720b0082508d40042800400b484108201030080c01e4032001f0810840c550481e004000491400844800a400a0f42c4100040d8680b0961620403800080c1e407070b41d61508540c0c0c4503924078145c5411200f9610002c103a05000601ca54000b0001e0401c002d1380d0080e0081d071028901c08140e1180c884461003006007200c00c00000d2000401141e07800c003d200e1035995034480c152103000700d40c170398075407070318400281c010b065105910001511a214044580c1651890b6407542c035126a012951800da45040e58041d500403800c122803103045140310003c3c45800d104c200c1098042880000140241d040091100072 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 391633012 1250 391631762 391631767
    0x4020315010f03140115030f11120708190f1508030903010c031512051501030605180a0b15030a0503070503090109171228021c1706150705030708 64
    0x1650b030000d61590100c00d451404200b80c0401c3d00005080140601c9602e0395a54106404d542c2c0e24880d0b085091000000002848100500c43c5d5642c3c80e5403040d040403d14100210106580c50310445190f80a80500b000a10248200d100100b0003005c200b0880000180d403941208070b0101c1204100c00100f03052000b654881d01078500f03060a494060814408041c0327040c4e1b9070703030348842c8d640f0309642510264540d90303902440134508149044c032181840c1c062006000700000801c1000d400052051800c1d8091412420410070890703078440181000070000414000040d141901d0b0300c00e41003000390020204e03048003010303450726130a40e40402800e41c0c1a8000007848011560044d40c0e200c0140646940c4801084144400c662200c0340070110b1800442c00240c04200c44a00303103a034501d6404040701c640c0b203000900700007a50303815094100b44003d0225040740f04d002401060220003841200000c02056543c0d141000b04501511004401c01e03941030183c1e00100740d0407c0a00712181c45108800d5 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 391634262 1250 391633012 391633051
    0x604030c120e0102100b1512190902030a14190302030424090e0601030b04140a0b04020901210204150f020705041104030b090f0f01090b090a11060f09040203 69
    0x468035100c100c1940280b050050741010580d0340010400c640400e80c0701d0001d0820fa6050008450100e4564006e2140134082a85041180c014083c0c40c0582e01441c0c00e4098500010741000545d4190400a036040c3c03c00700e00034001c40d4095031070701c41c7c070341c1d495060341c902103041da4200442960440041d00182d0010600b4080c10615900c11070824141501030000000424070040820900703000711180b01c07401e40f02092241c0d0080d0014a114000204148414000007005112a00e0100c5400040300e00f010590a03050038203100301c452088069440500b500000001c540440a940c07600c0115030f81d081000240303040c00d1701106529480107940c0c9050143c5c0ea1800249001c0050f0402440340b4601401040c1c03071070b0040200d804507030344100e012507159156000a420859000b58140b0700d80210800d9004421040d44405240391058900c10040c0d00c3c1c0c0e02080382ea0750740c050302c002e02d01c00c02c09690b110240303440c00c041c001c1490140ca1903885c00f607000c0080360584e0425203920a00b42200700380c04 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 391635512 1250 391634262 391634273
    0x20d0615020708071a041a040902040b09010219051e1f0605090a1103011502150109061d1005041104090c09030212151f0807030f06380f030604030c 65
    0x500405e801c4503007082c0d102c0b0150300c00031070380f117944100305002400031002c16080d203610054400a0100d06411912141d0f140f031038000360340c007143d1a03034014090403042e024090400300310720f4000c079080001401c62400807107074814151030721441d000c0e6a03c0364811805002d026001e0442e032840e0801c034003094640c949018014034100c05003100030030905041e55071a0540b01c1a0541c1d0440301031046907048200700000607070801c000200e10208004004001042c207603d6500114200c0d02911181c0e0f441c4d00a100700000f0910003941c0600e0780c6120070000708900e140940001e170740c0c1c4560044140c581580cae0400c850403198640340c0f84000c1084a002002580740c01c1e02c507481581000f0019141d00a50441c40d00b0340c0700300061183c003c003640c458a81b03110007409450f04024041d04400c644800342c890034203446816400e2002c0740c0140c14100101d05244007868641000c1982040303c01d851100d01c1e010f1102c1c0b5501089183c1c105c0b04100104001e41d50170409a070207503000c0c1d22a412910920f0800 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 391636762 1250 391635512 391635523
    0x18090f0b15030c070308060a120c0f0b04050a1505160b06030d0e0906090924091002070203030a051606051501170606070209040501150305030a0f0c0b0406020d0615020708 75
    0x1024001d0740620822500581020844031525403518000744540c0e980400a142c903503007900322424102c1204004810010b0300c0321040c3c152060030b030210204075921641190248143e002d0250480d4000804000c070000e151120000310100d41441800c2603044541000200500c01003519418081000d02c0005c0c01e06010200c500380303092501640c2c07000c803980460300c050382c05021709002e25855030000709101c0c0c040c0050408510203171030490f40d403800c030000b034021742e5800d56811030903000705031100b129440e4510840b20307201e602501550078450704407020b54440d081043c404881058110348007000cd441803141901c40d41018040b6a02d460b01140018001c816250855a00c100428107101560b900d42042d5903400c0d03070480d05070007555241e1424a026045500c4070688458025002004104011000d0a100d42c2075035191340c07031a048840210381c1d412040c480503006152100114011420300c1c1c000702003221083d240030502c55a00c031490205240501080310041c3c01941003480170031800e002 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 391638012 1250 391636762 391636789
    0xc0b01050114030f090f190c090c0806062b05010e0a1509020702030319090503060702031e07050a0210110c09040b2a0c01020315060a0f18090f0b 64
    0x2010301030408150b91008140c44041e0042902a0601c0b000401031001003040c10b5441400800380c07080d040b01c00e688200c122038001401c503911b00e25200042101c110340c0c800c83c5501800e036610000262560006e008542d44036001d010050500860130090354044010000607002e030504001980d5890041050103005000d00280703501e50030110002e2020f0f170100e22800c20399010340c80c0181d580c2e115100203865441042059820000d0b070f8142c10b90301035000107240044036001d9023a10340942c0c8002c42280c0364400c00c0d40666200000c0040340300c00f4113500e8081c02500d4850812140000740c00d4001440c5110900413440015040f151241c41440041c4001c0490710405d071102826800d090ba21803842800050920b9035055141e18031554141e98a1018410340e80c40106541da19004040700c24041d6104443c1c08130324a000c41304a1015040076002c541c00d80c20170743d0ba9046180040c0c1800c80f209002241e030804070a0300c9882c0810304140c14400c0450458035400e0000d075442c202402d007c0358401268 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 391639262 1250 391638012 391638017
    0x80316030c0219150b0a03050606041104061e053a0b0d0b09150405010f05070e01051b010b03010e03070606050901180b040612080306041d030d051008010c0c0b010501 73
    0x4002c14169040100c103058980d51080500028450b0000004005e00c4110130a90f0b0203140500c0000a100020036110f01881060b101442480311402d00901c41c0c0c4a6071203141d002440400c0703100c040262000140744092090300c1d00500d02040b64100e421104c9241404415075100b008080c1002c1440040e50500200e1141e0180030540e84d00001449090000d107000c0c3c443c00500001540490051001010085034026255124241410f000e4000d00e00b054034441000d00d013001160025008600006508405030f4075030740341c805840c0c80303900c00394440c1015404642d2954130441310b503038003802502d1080400000031504c2d604a400e01c602a00c2d400d62110340203100b1000148882504204890841224004045000040300d00410010074056011000501c03826005800b0800c016004501680381214107010300c0000c02004080d036481070940b02041c0e4010800b65420040c43d4000b036038020202c2d124603070642d03134841116007034565000031440090217500c550350030000242c2d0035901501e000c1c03 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 391640512 1250 391639262 391639273
    0x20619111606050c16060206071b0b06040e0a060c35041e05060424050106020c040902030a02060a0215180a0f08070c030c0f09050c030103120c080316030c02 69
    0x401e62005040ca60003802c04100c0f001a92901e01c200801040c0041c00e05070000014459030307184000d450b5030059542d078000414040d050001c1c44806802945000c0d002401108a03840307040403c001840c00c0110481a0300503401d161000c50342e544600752812005490708503020000c10501c440342205c000c80360000c0d0f810103044d00130800e0020300c415030203640400c00c0c3c114101d0040c40c01001001c0090010400c1c403030502013200b0048009181c00d0381c40411502c0715200c00750600800c054400034000c920059002032035800300744c54103030070441c1d80782c0c00942642ca1001705600850350781da20441ca070a025034058103654840320b4510281c00c3d0f0205a05201ca080307ca45072040c25207030000441c015102c1d042c4140480c007444010400c6070401644006004c0b81030740e882c50070f031021180520565002c1d0103c40d0002441400e540a4280b01e00880c1d01c045266a0075965140d0440014520050421042c224620005001000154042d07661904a02980c0c40102c20060a54003103010010031508907 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 391641762 1250 391640512 391640533
    0x40e010204030c140a03080408010218040c080703150f17060906070c1b08160503060a060b0d0c110604080c0c220507120c0c020406141f02030702061911 67
    0x8a590b0f0900343c44404d50002c6007844a81d00158130003a1a8101a0032440c0000e8005081c0340c0540c0100340100c2450f402221200350b4008000481e589125040c0100705000000b6105e503101e6442100303201d1070310b1041c41025407600c1c900482d5031210703001201e80502d100d1101d16903684c10041c0c00d40c04608040141300f50f10704244020302000060400030b1041c1500301c5d101e80f48030010284500944a244211010f600a050349014400c3c520f01c1228024020b90340407860b0a603083c0140c20598200750350580c503250160031a6402840000441c0c8100120310708000103103801480b85500403070040510a03120400382740c90324145a910582140300d22b2450080740701d03c0c0c01501e01680c0e9003000340d034005102c2e910440203860722500304051140d858a055103c0414940064200e948180203680400c4001d884444030b12902c9840c81768194040d195820000c0340948044a0840100941c41a00c1c2003114580c080b5a01d41c05c010740c0044030b03420b41c804410300c41c0d5101c543d102002030a0700080221900 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 391643012 1250 391641762 391641773
    0x6040b0a09020a0509150a0912060f1a1503010503072309040c030614040201120905120a021605090702120309011104090b0111060f06010c0f080c01050907170606092a09040e01020403 80
    0x803d2050b00a9026827a103150709000d002d40c02081c0c80a000a02070000c4191550258000720100d88814883d255103014549400c0c0060150380c1a0b41c0d0240041a43da030a090303030518129050075002078040d81a0b2a030214070344401c41c50a000300c0c800c05041c60540e05600e4044281c8204100201018010004000250380e0051444441c2c107030000c4005040415810001d007840c410b0300449510920001d2052a85603000130548c02c400340d5468040f40a40c0c481041103108141036130014010b9000704100c40d00c0e651f81800031600103548400006148080d54210b0003250040d510420b20180c0d40d000384109035800a8036800784003902c0005c2c100506c0d1088104012020107030500d0704019040340c210040081000b0030450039504441082e0b2540214003d15010344001c5501002a00031140700003080f419100c550644005c1c0b04000e85150742e0792005002000000a0400300340ba4000c3c903181d030011134514000c12407036860f240c2941d60780d80902c00307100c00d40e0089406202c103030703104000400c04501c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 391644262 1250 391643012 391643027
    0x908010903080403120b10050a09050315010303032c011b020307150513061a100c050703080d1803091511100c050918010305061e06040b0a09020a0509150a 68
    0xb039041c00c05071030038141c0380724482c02050480d1b2401e40184000c0001d940c03541e00007001e000d000c0c009582c0d07030f141c0981740c41c2415140d010001c0c000f0120103000c401840080d001e42c12006070400e40480e00141c1402c1d024031400c0c5000c86426a0042d6555a0820038800ca09030a40514030180e6000451a0412030f54514140c40108010385a042da500c0000c10101004c0c01a1150700e00d0308260284900e00e58a00b90803404002c02c9000da100743e07180c04807401e119000744a8103405070703003000c0900052440c44e2582c01c0c13550301880c01c05072902d940303400850001d448113405410250207551020f0143d810202144180c680b0712400d074052114901c1102e80500d400524000d00100e1000d0100e810062a401034a2500070302c0e0800e5804900c500e0f04500800080300c80130304890003501117803410744418080060510f95a08044012950700d400600e075420180c0066551010290244089a41e81c0740084100d800a10451000910004180c4003030324001d4021000e800f04000c07241e2410000c2c280240151 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 391645512 1250 391644262 391644271
    0x1020f120309011a011e02030c011104050a0504060302060a052a160b04050604090e0111030f0403081302131a03070b0c011a010507021504050a0e0a0507020d0e0d0203030c1c090801090308 82
    0x1081c1081c40e444102c7c402d0041d502c1410040c0002d01c00700d81001e2042c80382e60071500880d0b02544105500181d41c0c51305000c0c2200f1290094074051802c3d5000703004880b25030056542086e03840010206a03408034500c90b01151000c82a0098405021440c0341c3c0b162400031a841a100320030b0a0005018582e02c9008403130031101d6206000560111003c0001e01511450b00d031540500404000c009034100550129440386102c0d640c1c4c00d41c244e817660b45803c28080c5000020703401000c03c5006c500b01142680c4003039800340d0400081c1c44825084000a480d2a11039000380c002000701250041104900f4083c0c00d0190340840c0803007114180b0b40b07000a209000b5004041c4c864072003603e080585421400850700640405841d0418042e1130351100940080140d400c61292881c4c000060b107400c0c8007003083d01c0c55110a541d0725100418020401510603841101641c1c0341c0010021a440e03007400b0440040000c400c48201c4103950f540300c03800380c150940d5501207485039042028440020341d01c888041d510 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 391646762 1250 391645512 391645547
    0x13050702120a0306182301030f2301052505030103201f0c02130b090604021c1b0207060c050d0c0c170c040b0a05061801020f120309011a01 61
    0x90b030401040890141503d58014001d2002d4000010084041c6401ca92a5040010490020709a0204919080e443c007440017901340c1c121000107900007081e205483c603011107844010001c000c41c007c14942116000d44150108101c400074800c894155207030b5101c459182070400c14115072554451070394600b07140440205111210b05048016560710381a504644c0b4003044200b091119008007900105101c001030784110f00a00c010400113402c6e0091030980c1390302604160a54a5000620002e900445c002504843e02c000680c0032045062150a2125065000d103200a2a11000213030071f01e6225000002001034403000c18001c40c0001409069403401c502d00903142c00c2c00b5091000848909030800200d010482c480c003004901d00140465442508450401804110b50104000c1c501075104084c0c1280003800305006450b0f62a0600350b40d0101801035a40b100e41210400d400c202c10304c2c40c2c103071800700040103020500741d09101e090806070540d070742c402500c180e02c00040c00c1280c242174105107 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 391648012 1250 391646762 391646767
    0x170a031d0f1914030a0f030f0b0f0d020120030415020102030c0a14070210110c031f050a02040b040b12241c060501121401060b0405130b06181305070212 67
    0x7080f41e42400d0300c2c00c0d414036100392030701e4840f00840105640300030703000e0200003410200d001c08070708031901c50380c0000780008180400100040f424840c80d107800300e20590501100d040104403003190b001c107500c50750556901075030790340e030071324220f4010002d28110100c21603105004110f565211740c1c084034407a10a60502441031041005050790500c03035000000e402080c0d4001802d034903500109460020413143c1c0a84d58940380100625a072000d0348038001d00a105000030400702c0c37803407644c4081d401102c819030152400e034407088900b0195002d036105480540c00042c0803500441e84050705500549181440c1404024040c2c4000c5c0620310203003240e102c1c07003018460301000d18242c4101c01000c0ea2080c010b03c05580c0d0b851402c50001c2c0c2c1d00c0d0064a0391034210f803007482e211006100b10000d46810200a609003400d0009124a542c44240500252079490481a0302652500d000c2c000202c0d880c20301481c28000c8005206085030540d041000c2103050000348547c2d00e1b0042609032201d075040c0315094 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 391649262 1250 391648012 391648063
    0x303090b070f0501020a0302071a0402030607110102160b0912070206030403050d0b030628020c060c0708040b03090a0c12120f0306030209010308030a0c020304120807170a031d0f 78
    0x204480c90b03903000030b040e50710020704802c3c0b10750035401a01c030b001d000341155819201204c400c3c648013001204c0007581a080040061130090041170310551144070b00d0001030038050080d0740401251510f1505841d06210a0104001144100208031007188810881030030b08185601095141c000074100034148000030030f4008003000c159000141c64800282101c92904103205025020040d207059184021800301d24401c010440b8002c0b200e005020310000e20055488844c44c003040d400407a0100c4000008000c00503024902c41d02540c040c61101c0007500e64100c0030b240140109402e42e0040f0410040c220402e00406d003400800900e0607200e08004c103000350720301800c40c02000c86da08002d62058403c800070080c401c080010754031443d940c1e002000386141da81c0041e0703503070b01491140268208210004200044066028050092141e4800d0641d10141e10744200b01e50042465800041c1c0c1e0303000382d1a0611104001c107416025030750060b00700708a51100d01510361503961419101d91120710f4016 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 391650512 1250 391649262 391649273
    0x6011b080702010507081b070b0702010507060e07030503040306020306030d0e061210050d200a0e160903060c051306080105012307051f0501081902040510091104050111070303090b07 80
    0x102c0e001c0e548480c0c1c41e980c84002d040342d51f5040285c1480d260035481450f4010a031550034504488031540c0586503181022a02d9948902504202280e51881c1c00364130f00000005004001410185108020250310307807a00c001807501d006011700144003000002c4201ca42d16881d0340741100d03450105040000b00d5690384150484449050b6884179805c41c1810003c041071040b6041020040c480000c0d640c216072508400300681c0c2c0340b040c02400c03400300119001c10500300345505680b000d03180f07a041500c111a03980e21540e04450001c07841030045000007501504e2041c1842c1514080c14090030503c2c0554141340000700070301c41c1c1400002c042412850300e00003000c04030042e2070559038000116204030300d210941c2502c0c0568242e089120504001c004a50b030080810035000708410741420391401c4000c0d80801020780009006c00300746100001d40802c00c503445000d520703000c00d06a040c4036600c81c0b6010005040b600801d142082039044018144002640a0100000c95103410442034036040035041c00e = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 391651762 1250 391650512 391650517
    0x30507110d05071a090d05032814060d15020702010c120f0809060c0322020d08301b0d0204030b0f090c01020a0212070816080606011b0807020105 64
    0x810722503a03404145a80d4008000c2c1807003485601c00b001d0741d41000248042d0684192044203140d044501070184072440782c03028603442000c44150040035003603d40d08a6900c480c03000559881510b40f0400070340d13100c80c00340380c60704510b041e81c840301400241d440e5941d090074940503802d20650000348003c15a807044182c808500e40260900c1e680d52441030300600880141680c0301e0101b100c040c00510180d2020030341c244103103811001c1c0c41c0303550355040d400c0c2180012040c007651044464007a031030240e25203c0c4c3d061482c5205103052a640d40e5906001d440c0e09005480100d0f440c207404030180ba41002040b499600800e030090700c07901c2200301c07014900301e50140d400282d400034408540041440042d081e1607014000c1d220600c403954a0b2031140f542c8503c91005414090390000001e00010300300381c0481c40303c0140c031000341c940300354032100200d0500c0c0e400200841480c2d0710180502c6140014892280c00a2007400c1c54030308080d1400e0f80010303844a504003e084040041200780559005004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 391653012 1250 391651762 391651787
    0xf0509040e0c0f0d120e120f060106030e0703050a150227040b0a030816050f011109040f050f19020f03040f050609030a09050d06060e130b10050a06030507 68
    0x34081e4410021107182c1c2c64401e681581d220f01844800001c031410030a2130014220b40002c03202c88840c48868065404e14412215a60452106022007055103000c2c842048880c8107140506000e51404000806030b03582c008290a9a0b08001ca00b000011000680c41c032003030740d001303400002c0500a1140e1a000b8011403c0c014000702158210809180c3c0b4440060b8400104641c10013098460000740146040180002450310308100b0032110045c21407003000c07803060700c508216802d0080f0344051a094449507040301d0314410012950608a141c0b41c01140e0b10350070300d004200034619114401c03816500d400f4010704003c500381c2070810510860b64045800c0d810031089980d589003024500883c06a01d14441a0b0383c1d4000c070000714116000c04401c0305c6250049550305036046050104101e50360501c01001c0381c0842d41c4010000d00115900c01c014400c1c0003602149107295440d04041c03440782401800401c51014080050050f542d400c440f65042d2099440c0004081d0f0b1440c03000d8034400400d08 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 391654262 1250 391653012 391653019
    0x6231302070803041b08150c16080a210207030203030415020403060606090509090c0a0b16051e0607020d021c0318060c090902340f050a0201031a010f0f0509 69
    0x810402800344074a00c00c0201d04080b05d0805003207a070381c1801c688910f02c00e170300c500070310340010701282c1c1d00305259010700b42d9070501d03102580c3e0342191a560350302c10f60300030301840012a4007074015000304482ea8502c080315003c005411b41c50521607580094982c8001400181524002a04c82104a600e070341a0383c0039503407100d8200305094039004050f18003600c85c401da074891642c0c180010252800452907009880c809094140214108906908107410002410302d400c0314441e6408085182000900031080c1500c0c000000700901410f16424040700070000005e540c013040c005820998000b83c84507105000002d01c6c1c403010582a03089026040c0908012400c008205803101400f00076405084401101d446014211b5980c50901e01640a030340e84250260b4907000101103583c0070280d02c0701103203070749211415802d05035a82d01d00e03076520001d50956455010040007030440d6094843c81c0d034204007595052121160382000200380003541440384c4100008001d4280a50380100c1c06d40c2c00181004 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 391655512 1250 391654262 391654267
    0x302010309240501140607050c010e060d0212010305010b03151311040f141b0403020907050f0a050705010b04050112060b010e040f0b030c120a031b020a08030c01062313020708 77
    0x18180b0140000380110040100211901d00b99481e12104640c6882c1d0300c6009009004511401500c82004802c885600144100040307414016903200a113411265030004020130350540c10a50b08460340f09030400d00075407021251105480c00101c0c0d081c0d20605410460030320950600d05401d50411041e102600181840c2446414050f0750b000030644000e08046650242d66402184403418410250015480300420090001d800c0500d1404d52159046c00d040f450107081d0f84d440c00c070a0303001064200000e1800301d1b4181c100982802144c40e4031408450a010719410a00706021600075244024002ca60b6120941c400340d00915007801c2148004008200b8041611100005007a24242051080c0106a0210224070341644061414401100101280c02055905603030075040c2040c50703040b0014600c0084010380c0e07803007144006451040c000c3c6440d040011811401c1d2049500305011446001841c9207517400612150362100f0400c80d10352415802140801000748148007000d00f110000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 391656762 1250 391655512 391655573
    0x50d020705103204020415080a0303060617070c03020703060c1d0303030c070201180e0c04030b090a0503160f0c080304080f190b06031f1a040908040302010309 70
    0x41030800c03241401c2482401001c40103a4040c59040c0748800207200b00a0392401c2a03d62002010000e038094800307000050349080e1101800505162030f031000b0501d0b44207841c907408041e414003e00c0014400c90516441100c2940301c440d00804c07006142c00100242444941c09043c42084004011034210340100b03c10303036500074001c0031703058030444104604241c0300c945041070030300004030f070301c195410401182046002d500442c4d55005852404002005181c40440c89406980007617016441940080396500c1c41c2d407900c40c10341c200c0217054000c241c0000102c0d002041c404070031106203c0c4482e090f003007910b000780340101180c1316140c0c000d40790000e4082c2c04651820000010030641e41550101c855000300d0f00502c55681d0000c2000e020480703004c3c410300d000603192104031500540014150743e80c0300f144140000710261042400703a500c5403034803041c26403500303400030000040704141c50a100e21380107901c9044113481280301c02410507035103d0b003040500010b0100003516a405600078010b0941c0c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 391658012 1250 391656762 391656773
    0x91507020d140408030f160605010605070c0e040201090b0307020712080c2806020a03020c01091208010f03020306010e15060c0606090c030f04110111070806040c0905040c090c050d0207 81
    0xc85072891020410520324401100ca024043e50100c808a01c02903240c580d412807210783c1500101000c5915000c6240e0407000141140501c41c082c0c407055640c0c0d031702c811181c10288d000104640c001d4040402c003005000140c1d03071146030001542c00400714550790313881d032000403850007410360700c9298400440310346030b010000580003d16529805800303c0710f22584420382c2c950f420f81050780803050102c400050b1800600c0e241c004c0d080e141718a0800604012940210b6822748404c00012909415094101251a0740008480d809400e0b40c4001e58202ca040d82e010940d6814103010700040e040407030000502e09030f04103650b02a000000351189483c1c01015294565501c82940d065204d1080c2d28000b425020100c025240b08000314030001350035807900e44414003011094402c450400030741c484003109080e0100702c07610050000384014281840e242c10481c1c090744403508410855418030040c0030110b40426204400c0e203c2c039400c001100300c0780010a48540c815046039001070303800401e8a005002 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 391659262 1250 391658012 391658023
    0x506070f0c171f050601020d0c050c0d030302120906070c03050315030703050a060c020c10030203130803010f050906090f0612033007020f030a051b07090204060f03150e09150702 78
    0x41140c0b112590458078110080f007034603822107089005030f0144950381000c0c1e1151103036091150080c801c0d20200c02e18800811500c400c8500700786d010a80000d9028021942102030982c0302055034007400c414141000300501001c0441e00207402c00201101042500d0501303040c1c00000300c001012282515501d00d05942c0743c2141e01c0051307400c00c1c50180101030b1240040b82d96548084000d01c500442201194160000e400203041950700d024608041d0f4009426100254003034001001d1101c01d19107480100030505d2001020346004080d2078041c810356102c800101c5410a0049424802e0400a00c814601e140545114090340d02c20744469148460424800301a5466070650804555a2044020b90341d94000c80303214005036108001c0030164070300c40e82c045c24100d051004000c00d074580600381e0038504103c84e000282d401e54001420018550040d5482c1280b412908090001072031240d4500c000d0300741e91240c40b405a490b80d00280b0740388424002e0403a03038900c0d900100715900704403000940d5070 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 391660512 1250 391659262 391659283
    0x216030909090203060a050a0e06240102030f070b061219030801120c140609030304080d080f0c033c06192706170a0605100506070f0c17 60
    0x1000311402040082440c002e40c041507401500410460701c2d6090780308010709000301111443d95032950f40450751102030000500868880c58542c0c40031141038800c0c017140b8910109141550700401c5030b0b01c9225590820b6981c0b1030b410560340307000c0d076540c1008129505103016884802c0d0003000c402d00700b020610011040e83c18020703a510350766031380c80d030100c0515031044030304c050074801c161001000403a5076551703020444d1a014041e9400c1c0b030001c00120749107810036000001a80c010303010090613590b1140c1c542c1d511000340704102e4000d04000120903000e120140000c00500b00d00740b260f0341e044001400c03004095403403d58185081c41e0000300c04445071815140c0f5849042c4499034884000c070715040201c01d4031441c5207620604c4409840802c4140b00b034418005a04e500c0e01070005203244442d0200b003403030742070320f0103000e800e08986400c2085a60040c4a050a41c0360040d09204541384c6000342e5005e01e0380207440800703015040c02c0402e2040030650120039030005940681020301c90200316240308 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 391661762 1250 391660512 391660517
    0x12304090c031404020910050d0b190603021e06040e0103110108091f180203010204030305040e06060703140a090503010c0504081219051e0a0309120c0816080d021603 73
    0x15070980200b02c054900e000414261241c1e1000440c001d4540044540d82081d0b42c200e200411940d180085510080300800541d058480e06007000004040c8041c0340d15007001c0c45104200003401d5500081e02c04030b61501b400f901861502e842c02c070a4446908803009018843c084031025a92494140b0034090985040b0380017440840200303230000000911885412540c0c40c124503168111010f444c0144010000d400122100c0e200fa2000b5860a00c0140080c60090365400c1e51241000b00080382c2d044050030030390003510200000700c040381e0f1001501c189143d40708680c9503504603080003100d0b01c5c1c0381c03a008581d15500c0c101004c1c03481030b00200200f00312032191090b201d90b0234402032078040300e00941c0c2001c12480502101c000030903210b40f00401d00c08410034821401900f0f42841180180c00c00b42c6031101181e41c03420b4000c203219200840007021503562808200004603036490814500520080849242d0f01300f04020400c00d00b4000c1da104402039844c02c5442e034608082c016066214110103902 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 391663012 1250 391661762 391661771
    0x304050c040203270d050f0c010b1002070f0b03090d050f190906030b04050114091e070207030b06120c060a03110c1e070b0712270501030c050412080901230409 70
    0x803100400c3d5179585103200c1d240c242c01c00030845005c4200394800003041500e5540e601003064280ea94540c289016446980280543c0d42000704442e500c00698105611041080c0104042c0050015030000312100394580300e0f40710581c1c41c214116900480040008041e80d04141802960707210b04c418046468541e000d2106d1031341d901c28401207a50a01581410b6030075402c03045da03242045c02c44590011100e10300c81b440700c8050030701c0c1d032010701040d600c2d4401038000c0c1c40c1c2001404200c00b2001e40112080354800208107240c07020381c0da40c001c88000180550701c0400ca81143c01e0007940500204110120405da40709030911010b500e0303107555030812042a0307130036060107240030340000e0210954180762046480c04805480c0c0e010200784071044a420020580000700e158010002070120000d4100c00c81c000c1e0500744130000d0280d6400300120810402c0c2400100020781007200b20403013068010784c1d0151364403540d0380100c602c8044007207a281c070312505403e03040c1e000d20400000c1089542c400003c00 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 391664262 1250 391663012 391663081
    0x20105100501090302060702010e180402010207050108090309190f180c03060b0d110702040f0207110306060d15111b0705180402010e0f091f08150c0304050c040203 72
    0x8080000c03a00070030340001e0300e011044c001810100c00404401c0d00506054004610b84030001d5074001d020700100301c649108905000840d6010001e000242c0710908007181d03a464107010307090796405101b4906200f8001010030304501d841a9000c000940701c0c070a032010750b03591500d810000e015140100042d410b4500340d85900803610910900d000c0c0d440a0034590f113403000410802d0003038403800c2c071a4040074200b04440c800680d500d20031240201420040940c803401c0d2400c040c8443ca03480702e9058003a4101e0001c001ea01d03a1018441082c0e95808040304003c404c3d02d5040e10000c1c1135103c507107401c0150029544880300403050010f000030207024115440c46885105000501100701440080c200c8640007160040d80150042800c00b680502010f03011200d0600003140390100365401c61082201c94900a1400c0380d480400001d0460900202043d2680a84c1c090400c90300401d80e0942210102c0800c08100c8244600c0600700c2c8000c000795140e00b401e11080c0d800410594030041da450780361403c034 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 391665512 1250 391664262 391664281
    0x5010e0d0216150f02030405030a0c061710061103390f100f0216080a09120c030303050624030f0f0906010501030e03120103060608010c021c200607030507020105 71
    0x9941c1400c00e10081c503c005a01581c04156168444040d400184000701c0d00c1d490030042d40203c02c0c0101320f0a40321030300d0498080d045648102a02050042c44000c03c039480c1c0050301914121100fa290a10f4810401070000342540034a10310049004004014054089031b10615012180d4000000305455144500407541d2124680410300c0180c1004201000c041c4082d4408152140000700252801d401515071409028402d102117071016400b140b0240440d0340241010301900440d4240658051a5240d0b04000085844010308041c1c407180020001d4442498203004d40500710341d03a05921185202c141d44039041160008151240b007000070328010f4848595a00a5030000047d20840e42000011030242c6440c0c85010000d1008100c0841c40350100121a4020741c00340310000740c95410100d096003540d03400d06207038045601440c000c030145003030000910282c03102418014401d0a580e607101c8410b541c1c0603d822418040c480400032100d03055000302d403080c000c0c0c2d03001f0401c41d030360722188 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 391666762 1250 391665512 391665553
    0x2120c041413023007060e01050906040b0f0c03070b010603110306010c0f0602040f0b07020f010921051e01050a1b020c040522080a030b1e1c05010e0d02 67
    0xc104001d4860001540542803442d02a00701314007182d001c0a1140000070010b01c58200194501155440300c40104400d550202c05440c010000b46407040c9416a0765001484900580c001c1320b216240002e07103086d8054504086036506c0403400300b580e40700c1076141070141040700d003480303040b0100e810004900360765044002100d204010503101d0514151540c0c549400c0c0a03004481128015400c00c804035648901c650f0040c01030040c003040640d10f0301c091050003a190b4880705001d051000a8070140014150105e0141500385070003900500110141400742c640550341100c81d10074200035032070660090064114138841c8030010818802055464a004104000c41200e030303005800104040c3d031280f4140c2c105070f8110554203143c00e0700d8a0700039503423548100301c00c20484892000003070321844160503020b0382c1d611400803110f41c40146508078490f036025082d0440c0e14490071702c411400342d1314010052608081038001e0020001c45d1200100c00e540c4910446070346000d48a88103486414900b00d503407 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 391668012 1250 391666762 391666771
    0x204080f0609070f0f034d0a030b0f0a09020a0605040302040e0a110418120f140f07081b01110306040b04360b07081015020a0b090a02120c0414 63
    0x294161102d1664031004101f4503078800c1d170014840c81400500c214206403543c890354a40000700c6203481d00c1040300341c40b28014450240c3e8000c84046408202084140e5251540412103201926080d5542201c4000501041b1002036014008007408a0905d07400300180064078420781c4c040001402e551540c9580340c03090074008100c000c41003603006050400ea00a881c3c0022205989094583e0944e904a050180c0b11340070000542c641088149266019004102d00c11400e05141c1c501150011000d81d50b00c02c08001820007140050107004107003c980e10135001c007800700020400f000b203820480d4942c1c4c0c07095449501c11801c20700d081141d4941441031200107030b003069107030141d170607000380b10b00c0b4581000001407501c06131220101c2c085200007000c1480348640e55260707120361403c0ea500034000d140e170b0f030018074403e210a0b8424170314980000b802024980c21480311030441c2d072100300c1940341c2000000020f402919102c46045940c2c40000c941c10f42d040c08a4050242d01e00c00c41b04010301440448 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 391669262 1250 391668012 391668029
    0x61808011b0f050c030415031506140a120e0a0312020c0304050f0d0206040e07020601060c23010f1a2404090b01090509070804060b0a18020d0204080f0609070f 70
    0x2a1020754060254501680b81041c40c10b107282496824907070a42140c100d5031242c145200004036003903640c1c2c0d02d07100b542036144400040d070380c9907030406500500c2d11040f42d102c0130b030714640045c0c403236000d60085485000f41144140180420340c03030503062544864454000700d021a03450f840120706004d0a0003a10104407040d801103003094a004100704042c888452900d4005046160580141c0c0300c0c40000c001800074500a102d1500f0a940004d01c1d00380d050b40450100181540f0b03071800913459443c00015040484a0700300c3d03a003240803d0b64018511943c520404914203da80e01110040c10240498081c5c2299194500000114002d600e811347c400c00d03003a0840100300c00c1c4600c0c1d01540c006000c0790300c1032410b203034021b484c0e101180034400d0035a118000b05410004110411802e0300408650b0002690001401464800313950f0000180b40c0700443c200d40c0204422200c2011941950001c082600031600b40d07800c0c1003040d0b80c48000a807115001c0d401500c40200d4040d07610000c0c4412280d150 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 391670512 1250 391669262 391669301
    0x2307050d0915090b1e0f01030303050601020705030d0e0114191d03060f0f070e10030b120a080304210c0f051f05010819050c100210050106180801 64
    0x5034414004114484040710a03080d180081035140b0414480c8a09082c40380442c402d0704e08140e990200b0505201012014019014081144082c050310007070741100e5040c2004103207519600c0060b8100300041d040350f5003610403c90801c0b01160b020900940142003038030b9a22954010029072140c9110342c440a1442140307610b805403d852050300c02c03c080307049840506a0700a580c0d00043e050000640d15400b46420130b50a0040d048541601250040c601c0d05000501d400850040313816001400c50180c14140d4a0400807815261560b603e454850060261890304a00d4600141150000c0d10143c0701c40c4111844041c0990b280c1c10341000921031130704d600c01c01c0541350b5181d803030340b21455004a80324020760016601250600019003145014808007180960410a0305494441038084421601c4100300071000841c00200301c045c29100240e5000c1a080803600c0180e1400100c99421528075103410000240706610403200000081d9000c08068280c1d51446540e09948041540a440c010740 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 391671762 1250 391670512 391670527
    0x9190b120a020d030212040906230315091e03030403080907141003110d0b1f170c04030f0f030806060c031209010623040c090f0b0a0e0a09230705 64
    0x8059090303c01d403003441220196100780131144d81076001a03000340c040315120a42404400d40c540011248082502c038000c400316034031b000287e40c40b5945610802074400b16004501454014841d4030340ca00316041c3d0141855103090800c0343c1d2503004440541c00142040041804400041101022941803c10320001d0170a0031041002001b1003a1026083c036a0300d030340032040034810344058941c8000c1200c0008041d1102c0c0184080c010702a000500c15070f4442c1d02240b4940d4001c0b000342d0680301c0c1c605003c06296500c3c40c0c00d40340752286400141c807020070b0360605d07001c005602c42a14400c5e446551441800c0e103450b024011203002c0d80001d00003982060060040c10500303c03003070540c030402c003200115980350380300302640c010f8019250039039101942c1115043ca50500e070040180d81105450903c4a007441d100b41d4a0040045018616000d0b00014480342c1c1144201d0700d441b48a90014403210800743d4901d141c000401d030130706040180c0e0981c01c008080400300c07148064411251611214070f030004 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 391673012 1250 391671762 391671769
    0xe1c052107020a1505190806040609021608090409080708220b162a03110a050a0b03040510110d05060d0209010501030c050c030a020102091c0510180209190b120a02 72
    0x98504c2c650104a000d00c02074501c01600b500245a004070f0380c0368540582409028881a260030313801c1030ba10503004000d084034040441a00481480c0c020b441a520382c0d44400018002e041d0842000e800350300045404070a1100910041505008990061a4500d0740c3c0c101c803492200c481c0b084850000c4140b001d0206d41c1365045c07140000c1d501c9100d040c40013a401162400300800080c11f40d0300a040740d0f4a0034010130038003005507121058101c1d00c0b5142780d860400011030b441c00d603001d2a055508084086010890b0407c48800d007420070303800074008001e100c0101d110f140c001c6510000441d0030311020900300e0810000c1103901d150064107100d0583c5c01d050054002c0c1c00c806c4400c00130810304005507042c0400038070242c440700407298000b690390300d5684100050403404016003001c01d81009241c40000d4000661000701c441040300c04585449940c410000050074440082d420903c090200826074642c408800a0400c09601c10000848620107208890b0301140319105240d00c0b1310103881c003500c0c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 391674262 1250 391673012 391673039
    0x11190206070504170307060f0e100509030327010c0c0309060e09011401050c0f0a0b0105010f0903061505030f0d0909090519080f0d0507020c1002030a0e1c052107020a 73
    0x201c03440105ca180c09030715aa041c003102e00007031000072140d41e10360120b81c0001044c8199010712041c001e09200300d0600e48a1a501c91102030091000c01120950620011045500c101080d6030000c0003042204e440e400c000d850100c03208000c0340022040400880c010780240c0706102c20711400f41442e4200da00340304c00780c1701c6200c3ca4107241d814020300f0b215419a00c0c2c800c0060501458030280680010b00c401d2034800103021068000c01c1c1030155411801d08550380c001e240004598000313402048503200214000540e0300035400981e0103000b0007180391007169000401942c0c180240d911050450340d6401c040c400c80700d082800a013140c10801c00000140d106129101140f03004540300c034604050b00002c240290320401d800c40e00b40f80c545041190054060010000c810400c1c0c620300311080180500079101d101c0d1148120901443c10780485254135074140d014020181008420060992403c09036540d07083c1660010a00d0841c0c0c0e401e2843c0e444034170598401644c050120f40c461810b140c440a40c05 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 391675512 1250 391674262 391674299
    0x50406090e1302040c021908040e0601050f07060507031e02030f07030527070504021606060602030f0306090415020a030b1c03050909150d0b090d08010302010e0f0103090611190206070504 82
    0x1841403c01401c0000415007032080c161381b048c95010341c1c5500d040c1015010110080c0403505000052101e054895071510440b4980caa10602c001139980e100d00c003e80007060303e03504040c200c554100d50b01c0024050b42d8019402000350483d01c090a60711050201c00765041101c401c600c0c28a41c040c021040c0d81d6042082d051203240100361400b07661180701040490300514000a0200c0540814500f800024418140a02000d02c081d5181201c0900340030241e10001d018180940031100000d0140083d030307050111042e1002d0710a540c3c8001007a00280940010a120340c490000039480301b400c070341014050700d0b5041d41500c4060600d06075004000c40300700005c11504841d03121119400b03160790392079000b020003413044103070100c0c9091100003580343c2108503c014050060b50401030025070f0f000340e1081c0c6c0741d4001b1680700400c0314102004030003803e6110b200920aa05014405d140c0d58545409018002c00c00b84c1010f40000162008a0b65023505941403804a84200414800e218160f20b548088 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 391676762 1250 391675512 391675517
    0x40b0a03060503030d0603351b0a05010204060201060807030b07030e03130e07030606031a0609010e040e0d020d02061e1b0a02010605040e010606120c020a0b07050406090e1302040c 79
    0x1c00c0da07500100e4216400031580c0c00132190f91b02424410084c0b6402441082c2054061614a8500da400c510130f40540207030100b11140d001181e5943c845480811010094031088280d402c107041c2442d10300c2c040d4200b0302030344001d942822400b0880050006664003100d420000d40303040c070b0b00d4500b0268000e19640741c141e04140000c1000c040106600030030140100704402c2048903e00d4034850081c100c58440d08000d04140c2488021058417404009617050a002120820f54540f09031006854140004a40e84d0300513080c45030030455504081182006058a03400380c075030148014000320303207070741040302c803c00003107a03e0012070381010880325201e0b48610600000e544007101c030741d00600560802e400030710051791501c2d01400f0070308242c001c081501e41040c0081c0002400c008002e0400c12803180021000d035038440e14101114420030255400c9504006029083c0c01c00b403c0080280d407040c015400071500711840017a00d021103044c0740e0b11545070a40144201800c95080101030401181c10008 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 391678012 1250 391676762 391676771
    0x1020a1413050d120e01050c030702040b0a1703040801050f06060415020304030f05030a030e01061503090c0e0106050a02010e0705090f04020120010c09080109050316140102040e040203010f050c040b0a03 89
    0xc4a0300c0b504861100580a2030302c0800c1141e072030720000c5c811040b0a031068100b020031f06c90100c41349000002d60308040d034122004185055204046100000194001c2c094613880c081c0b80c600c100c0d0040010400c1d1000030000340250341d155038801c00614826500960401001c1008000c03484c1008100c40001e074440c41038030301e0b0a80e20f8480c010207003100c0100390b030b00360800510b01c40180c2c0c1620400d0995086400207022803440c2000c01800d08084980304c2c03090603200c0f139140c000c000031054000042c0070303420b91441c110350b150000101107070800142030b80076619050401020400004500c0110380c801428500e4583c1c0f822980086030788060b00403030612000c074010301040014420390f40c180001d11070000800d031100c240010200d01240d840101107900d0f141d2098040740000c011583e00303546e41020240402098900780800040310b40300c001307165201103000301c1d2007034121000c01d02482c002c40007800a40c2c000350307040c0101c0fa01501c00901d0220100820030070310555001600d03a51641d410f0008 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 391679262 1250 391678012 391678019
    0x90f06030705040b0f04050f0306011a130f03050c091b0316050904090605060315100e090703060606030b040b0f030a02100306030614090f120319060312090801060801020a1413 77
    0x132203070000320f900030030b080d0f01280c01d0010341400848806200c1c4c04400500065150141c0b000001d0410355856140c074600003404014020030072480c000030305d80c00d074140b140169039003802c980b1502100314080c4070700e00c0200400c05212410340b003482d216190405446ca1a111003d2014803000055450021f0050134000300b145942e90f03208880c03100b80548408119480e0200406042400100f03000b03100e00035071414001030982510000f01681c0e54192018525255a0540c524010059000501c00c45c18050301144035503164018101c0c00394151818401d401d1180d04008840148104254142d84100d00f46000352a10ba94402c0841c4440c0c20002540c4d52662540300c1594094a54130300005c0015090014882c4100440140208820064001d18040c1110341140c1d02c800751080d03118244070760308281c5000065010350700540d800000f0503540074410788080e24120300d502c140c6003030f03518000c0001400b440c10f00071624042d4207582d030142c1400b10402440c100781c016001014142002e00c80c0072 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 391680512 1250 391679262 391679279
    0x901180905131103010207030e0d050f071701060609060e010c03140c07030203060c210a021b1f110403030305040f0b070c0b0a0c0c060221150102070b090f0603070504 73
    0x80d0282c02d00260400414205050590400c100c54400038000d81c410410040805c3d849019050340303800c11140c800c41052030f070030254540b0340d01488444090040d505c000074001c004011500d5144010b1000780703c016034400c0f09441c03000d050320951001c02c548405200f074540c0b007101420166842400c01080032600c1c1039855005401c038150803006a072200c031f401c0c82035180401810f41d00c0004003d549107800210a41d90b40010700101441071f001d900000071404581d81a019a41402c0002c40715107a043d0504005990301c190384030a4205901d0b102d4043e0304010100c0c02411149540706a00347d26161860b40c04a0060000070001c0e10008510902d400001e0b40700e0a0841c0110500c3d41c0765a108522400e042080801c094411144c07149001c1c01c6000946d00b000005603169000701b00140c46513500f145030303000d03400404100c8200d00c0c810000c000002c4a601c600d499804400c0c0c1c00c640c0c14540711000d0b5445807140c110055804011648441c1c101d00d0301d82d0046600c80d00c0ca1400070b04203903840700f01c1c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 391681762 1250 391680512 391680521
    0xe1e0a0e01021815090303091c0615170d090b070c0b030a020406080a140a050415090b09011103010e0112080d0c030902181303030209010e09090f0d020f0309011809 72
    0x10b03e10405220810b01081d02d404030f011000d120089203c03074988001c000000751b4911a41100b02d008250b012031950284841200495501e600b0050520070754500c41c8481d1045950390088000742004800e1903020500b0001d900404030f2110b440b4a420141080b0780100981c001490450310040f6a5602091446005011b54080c2c807000a003d0f880d40c0c101030010f031074110020180e2030307a00d20b0302440e80c844818988816820005900f800152a21542090705071440d185400c2205d242c200f0010b00208001300584034490b20021008114246030401c500c000d074803082c4164024180c103070005111440402601e503d0241c03248000368600380c015010802a25101801d040109076940c0048003941000034205000c200c2145500d00240382c4503406ca09040d014100145c1010381c0861801d1083e4080d803508050710b40000d000c202c1510b084810305945c3c040c10220700320789004194112080f2400056142100200d490240d8140b00f40d031001102c070b545070b0300201c207035509446800040c0401c00303204 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 391683012 1250 391681762 391681777
    0x30a050a360c091406060a0519050f0705060609060d0512090a03050f2104030201080f0a0e0a1b0e090703031107050d0f1b38220e1e0a0e0102 62
    0x4012541d02030303140004d0407840004200301e000e03c104102007100390b40d000d000ca03801c07501ca850b900c00340c42c0429101290140a04c10a04c0c01c906c4000911605000001401600c1210100c070304443d1640c1c5c5900744140d511210b41c000349154000f0f0128203d80c0e05217405401c82401c054100b900c0035541e43c9a691601b40d01101003580d541100c09901e200068143c00105c10624111006262030b256030b0000b001140024410084442c5903004a0899001604102d48a4a0000c01c43d130a954242c204083c250259181302c801e08142401c0004181101c101c855109080110150044501c2c60310b0a541482c51585100101c0c014080041032541e58541e410084500a0904400d440c181e8900b0101d24561815400f072400c0c00904100800f554540805055091503802e210340400c901c0341c400017000000c136080105101c08226030000000810092a00f0b2003406204034240e6955803000e040d4940aa513441c40321084580300840810840e0845900320f0703040c0300c0c002121003402c20380c0343c04ca0700200d6 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 391684262 1250 391683012 391683029
    0xa080f160807091a0a0e150303120c18060f040e010503062206021603090510020616110c044b05070c051203090d080c0409050408040f0b030a050a360c 66
    0x4240003802161204c00000c401f4254015842c0010704c1c1180d0340c65100040001840720400249019240d01c0d0b80f200c1210b40c00050701c00c54030344d000c040c20201290424011801030000d00303400050f15180000c1d00c280121507401c40070380c0c02c82c69142c0b84000100c00300025a00b541d02040280c02c414000314014407600d000f5551280b02505043c10005d21415043c3c900c0219030042080c0720150071441c0f4407400d07003500c0c0e04240c0b405480c003520141c200115118142d44c000d00d0000e419030f03050b000305212290222030085c20008081300c170b40c041c081200540603242246c51078202c108080744056200d03a0b00b1030b40c242040072107143c5503503605181404041400380c0000d00401400341d428070403c4030000c0c0502d0390034804594a00020008040e01403441400d20041d142c0000c10244040d040841b0b0140541100120380d950311070011515560007914800c0e40d03c0d141000080d80322074284508055020f103444020801c0421440740b28070390201140f0064104a0451082c0008a00501d030400415140707 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 391685512 1250 391684262 391684289
    0x307030f0f05030f0c0307030908120105010e06120f0c04090203042a0303050712031e0204061209021c11030f01060905010e01050d170403020a080f160807091a0a 71
    0x2110090140c48680d040301d081c41420700c184044d50812402c01540300c0d036080e60140e04d03907445000c1200940803480024240c000009002d892560407034610381d041c5c5900ba01c414010b82442800e121a62203400c01c45000c1d2001140861901072204007980d41020303010099508041c0c441300c0c0b01e8200d0340255000c691424890224800131242c89407103a100b5003085c40f14080040c595140900184240040146007151000c14a40000c0c083d51100160289e03004c0041441300c0c22a003454000d40c003d004400c0402d40c1d80c5d40901000c0070030f024600d03590707602803d02496141c410b00110313108160000100d810288076200c0a02c00c0c1c80810258812150100011994601d8051808119030060b040035010405283c018407164640c0c010b103040d0581e0090608004107501030000c000f50140e07401c003d501c2484a4000551a00c00181c2c80c44074945500a907903211001049940c100c100310300c9407124580052208000a004030b6008000c5070441442d842480c0c0c4403c1c000801034011034200741800d41c0c01 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 391686762 1250 391685512 391685537
    0x11070329060603010602030d110d06120510150302010f030f0f02120f070e1002190f05010f06060e04150302151c020c03040323070e07230d1508030703 66
    0x10303000115003206056407824619414108020340f64420440c140c102281c07917825210f05134200c00216441d18840c1030040001a031600010790864407408002d88040c0300741a81800c03c002d65101d8004848413076006403520b04c0c40c5a0042d5210f1550460700e03000c3c965514100303180000b4602602100e00351154005903909854020660300703070740c05044a5a03a400702c3c5d00b005003150f00700283e9928000221804107015840c41000ca140010909500d044485440203100402c07403101c0d183d01d1080e2162009022409480c00480704450070b9202c0c5000040b01705d01e00c0e03406410309610100c1da481c0c1c00109165015141d4011540300e006c00f03801e80c6011840068a08003503680e011210081030b88400c8290300d04200410410b583c0d00481c000070305002c403092402c0c091210000c1c17100007011220380075101d1103962105c034141032050445a030004111032400304114031448214000000b02400360440c00d2008051031b20b0020300403841009070148030304c6000705044800300041c200782e5119541e0304c51344606 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 391688012 1250 391686762 391686833
    0xf040506091c0e060d0f0b1203090d03030921031e0c0e1201021608040e0c2d040509090c10020a0221010e07140103180803070309170d0b0a0807080607110703 69
    0x59418242d0809d0300140700030307112a42d59082c004031003038052401241d5081c5509041c0c0c07440d440e5000b24008000700d80e041e03000311a0075400101d400503480040b0103030b680348418040c0a0302d00e0022840000340f551166250540307444000c040c9200450000107051a0805109100040c4088001e44a608020504108100150054603800b25103c42d00c141040f0b292a1145055400c0c90440d00c80702410f103500c8040841e5241c152001000c00508039219401c10111264440038030582d01070150040c40102c1081d0340c0006030301201c0e644d01070000a411103845151140341c0c03c00b4041c52001d952110b1125114440400c64080a0004960513a44029412002500f01e406c200d103140256959001c220000c129013105803a44072107242004940c000c0e5a1610700c11406000c0c0481c5043c60022801101502003a07000e00041002601e000d1800c44d01d502070300340d030764010784602c803c40c0c1e10085c0080c0f5220300c15880356108440c1e210440e0b075216146d0b17548102c0807c960568840c039020380300b1785540350072 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 391689262 1250 391688012 391688029
    0x804050c0d44070f1a1503010614060d060f031406060f06071e0204020c010b04051f052205010e0f13030f0e13050f040506091c0e060d0f0b 61
    0x70768481400b2040507000d01282c00c25864510140100c000400c003041444100c50b0f030724403100c0c1d03c03d03006100b840d181640704502c180103807a004404400d20ba514412800c0511500080e5410000c7c50200c0a41004c00c2200d90340c03100c98a51995500c407403000076071840310150003004ccc61088091200301240866042d00e0240c005004600c90401c00c01d6a6015494040484940c030790007107415409004240300550b0135200c82e440080d041480096240740184043d84070015107841190148426201c0d5003040001e101c40d85940e0350407608020041100345426004800714002c59004e0b240704103240200388085603800d030700002d02d082d9071b0000c0210080c1b880000030303840701c200e0012200c801c0280d24014104a8103156000c10b1150030400803605950b1840311030707000351080c84180300c9490888105001c02806860440305445018013280c1d01c0780700822905030080300c0592411451080c040e04441b03200c81445441d1300400c00f040041060744540c02510188805000e010032000c81c210b0074003807041d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 391690512 1250 391689262 391689323
    0x70305030c0a1b030b01050402030c120a2004030206090904053918010b030a2009010924080402040906050f160c1e081c0b01030f060e070804050c0d 65
    0x2101c092004e00009550664090546c1c40940e4010b0326551401202001803203140040c894002e404030030031030034211035080000c4a11036880e002d80c01c2c4010500e440c2c3c403800350f800029444038081c862100c15042a003c250340c0306006104803040e116244544054600c4014240316000f0003040846600ca030240341d00c03511707440055a8002030107020240780040300206004003800c550b0008040b601c0e461203500224400280c0701d44120b8050300451000b03035030303a128000960104d01028400680d500d0002c004542c1c090340844030740b17000d43c03013403c0c00c03110b0540041003264000d969049881c00710b920b9104607841642d54004a01aa0601c00040c2d40310741043c160200400c21509041000a10019803e031034010b298100c1e050700b0500c41c544445180240004003402401c540c42d2541c400d0801c2d0402c004041007030301c00f000401c05420100041d1240e40c0264003480d004140130070030681c0325200035a80580074030700343c1c2e10034007030000000c1c62041001425034562026800000c1050349a04100303da5 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 391691762 1250 391690512 391690553
    0xe060c0309150402030c0a061e0203030601090b0d0603080c010b040e0606061206280f080703030c020121061202010806180106050a12020d09060b0a0f050f03070305030c0a 75
    0x114030700740022aa81d82c0740c049210b0705190700034001c42c04540701000522000d0b000107180d00305640c4c9400000301000409080c010743c408035200010655400030040b00c1c0070340c0040c0c0d5a8801c1c1c80c1042790070801e9510414401c0c0c50560345240c00000301c2c008030043d0154107001f4002003128101c2c4410032082d2001e41c4281085508018248040d56903100111886001500c003240c41540d02d0800051408030035410304d0701e034015940e14480900c404498820b06175442c094810000b00d0b101c003e0155078400c0c40c00700030042001600c41001540c0101c8400742007142460507518040440d002c08000e60783c050b80082900f0800050220031581c01c80c640503403180041c0c034868817013403108050965020042c842c4c80300b07101c070004e240188144a24020744040281400c02d41d500c808161100e030050401e40d00986146150034291000c40c600750702040e00f1600d40921251034107040c40e0420152084041030341e507061146030400000510207001800962101c00040c280b043e03850b052064500c0c003000801e862 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 391693012 1250 391691762 391691767
    0x4030e060f0a081501051603030b040906200307140d090212160605030c0d0c050705030c070e0901090510020901050d0e1b0303030708040f02010903061b2307020d061e0e060c 76
    0x80c966480000d4465160b90f00c040c007440d0020608089c0c0c0180401005a50020700b0200c0400500c01035070030011022030b507035440f80d4200740c840d410744110340000c1e218140003845c149003c100741c0b030000019003103400b051080010704014503800130715041b106000889803a00035208001c2e1801002c0490f400410305410043e00c1c514044005800038885c00030816022a620703070030b42c0039082c440c130241d03000282e00001702d950307644000010681e0380201f0304ca100d000135946800621080b006006aaa485510000804d080d08242c1c020401039040302c0801c50410006206142c14804603008508180080102604c800c0b208003002825152640441c4c50003580104140018258001081940190082c0c101c0d04c0c044503d100407600c109581d407001d4601818a500c01c07100c600740741d965418807000d54036001c01040d00000100d1515030b04241c1722100d140700307100080c0036081184070f010401d40701d00000120881a40032800c040900301d5110030103280e603650202d02c4041700304401ca400082031003a890 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 391694262 1250 391693012 391693051
    0xb0f09120409020d09020a03050109210e0108060f03010f020405090c0c060a090f08041410030c0905060c0313080601181401091d07230a0605070b04030e060f0a08 71
    0x94a11a51181041403a070019003c403140c0d11310781c4201c28080d402803250003041d541c1d0400310301800e5141029117400e41c040c0200f43d6410310511034800042c800e42c84a5003000c0d820b1005540003040182107542040e014540220766030740c01c3c400e030001c410b41d00310300685a1b4140418020315040c010011045d00008106510688000240d03c5510198200010407101803034a071010a41603c200000c0a502022501041c2c49402c03601c42030109505603443d0340600342d040011010f03140d52064190100b40d120009118505203a8000c0185104076411286040b100044034444180e0036804490183c00650050001414012441450b030411401c103002e21048410b1013510b07040d06100b41d5a00941c0c454560000314030008256118401c03500549490541d030383c40c41c6161500d10040304a240c9030300f07200d06409180c01d44004050340ca00756541d5007052001e03036819102e503a02a10503018000d4901000c0c0c019914a4005d110400c200c070780007030702c4e40d0303a407280a488608081c0c04010002c03070661204 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 391695512 1250 391694262 391694293
    0xe0c03030304150605030a0308040218010b0a0e0409080d0b01021e1b030a140105060f04020c0303040f0c0806070507060501091b050d0b040510080607050c0c0405060f0303070b0f09 79
    0x101d0300b0070341154411400740c20f14403240c0300401e51940072541501440b460301040c10342001416200b01e00941d08202c03460100811b84290302800d01480603e80c2c01400b00c48640c03440381d024901d4401c0060000100d030402034550110640040740103041098543e1456001940e0520418164403150344090403451000443d00303844110303804e111007400002d440c20140c5c1e5601000382182080e04101014207000e00102400e000e00f40880e4554000c2c603081c03600085034102031080b580304203200000b660a544070369031a030f119251008000d0b038441003e50004100c0d400c0520409004076841c4c0c9a2980c2c0d0701452411000b60340c4168050030b00d80c1d203002030848880b0002c40406c0811005461320780d031385520710000e0304010440703800d0154200d4580b000704891a040141e0800940c0d250728200c0e52103a075842c10449680c86510300f41602c1d034000c2d102d040c0407404c168002c00d4101d44c0041c076400b08410a04082817841e009510262500505201484290918004025001080c01003c0e040b40e410130401c0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 391696762 1250 391695512 391695517
    0x302060112030905040c0e1005070b130c0e01080606030d0c030815220504020a09022b020f0703020610060801060c081e04030c14030a02011d01030f020d020703030e0c0303 75
    0x800d604071580e08048010540b04403891005040028020020030310703600f01c0240310382d6161203018060043e003103004550314090002e44000c10392288074101140d40350b140004419481a204039070049410b0800301c2e140c16011025406040744e580140028600201010b2070407c0144001007400043e4500e10007180c0d01a100650220201d1042012480d001c0b01203241d080c0910005421515040402c4910b00c0741a045940124000c403141801c00f6101c400c40300c00c078807a99100d0000d01020020f00c03141c14840528050780300d88009001805c04d00c03185a40d2502d41d0083c1000c80040c0c00007010001c0c44022191450301404603843d10070034540c10000c0c090310f0881c2110020785403030707000301c0c1324148294000414a0000300e404a815161552850141c8a013010341c09505050440090742c001d5a040000f02c0003452a0140e690708030409600f108000034400002181e03040548600300d10790240491300051014403c00c4c0340042e6545030504008040310b031500303401001508000119241a9030000a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 391698012 1250 391696762 391696769
    0x1b04051305040f0213060e0a02030c03011a21250207140a120b0115210b04180c08070b040b0a260406091103011b050f090406030f021c03020601 63
    0x3040d480b0350801a0340382030441c0000b580614140600c2c101c482c055080f880840d42d448491612607100c201001044e40412242444c09010a100402941034144142c5090078660070125280080554141007100c015040e03c00a00002d801807005010b641040d800184203c81c141e44c0006001810094a4030568451501a40350b200c4c123000003a42d418200d0310003410901c0d0b0450140e5a83d00d800c4802034400d2041d81216035100c0c862405c0305020721002e0719095580d103207100004110380340940c0180546c90115410990314804180904190300212000030300400200b00300c1403a003001d5030302d4050365030001c0d11100c00038007041010074010420f03110b80f1007a43c240140c050781e1003101c032140301c020440c8404000c084007051105000c6030798424060f00d800b40e00c200344149400010301d400c1c2c0f944103401b060351140756400d40021a224a000e06804d40421040c94680002c001c0001c0554516030001c1d82c40d190303068845c40c1113240c0040104921190103204008400ba50f440c003030348a00e014031 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 391699262 1250 391698012 391698049
    0x709050301200a12020d09030f024c0f0c02070b04120515131109010612150f2304090f0b0a0f110d0e060622061a031b0405 54
    0x81c5643c0594043c0125000c801050b030700454440c0030b0200800050400000182c0c0400c000b40da85580540c404104c3c0ea5403051501c0c441d581c1e0410451081400e4100183e0302c070710201c099034071008001c2e0411503110700c04500282c0856a1901000340000300ca5980e203c090035035120304c208100b03000c1c508007950121560180145000e02060911a0915061110b2140510b18000402000340f00c0c40c000c50b48420f00400781c4080035070009041c42000c038428010754021481031403400341000641d03000b104d00742e1a60810140c000e5641d40d8440282c203125040f001640545641c803003e040c03150060f001da503507400c44051050840c40e03154140d5400d0714090240c01e41c2c0130000040c007120071035000040c400007451401c0003200d035880b00100381038211320022a601c5003400d0545a00e8000007680038001c010040207000c581010170404111043c003607000c20040382d00c440d0002038180421f02940c02c0d021100c20065540e00d0411000c0c51000242481a01c10340410b00042c0001d4807019185c3c4110340a00c2e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 391700512 1250 391699262 391699267
    0x906181205010212090a06050a02130e09070509180f060c07080c0703050307231f20030901061811090d0602090a0b19030218150f030108010203070905030120 69
    0x1d0801e940644a0080c3e0f41a040019400740560300e0300000d40c440089000d1300c0208101d48510a075103043c0e105140100b500b82c6242c0e403060000600000045402c501c01008540e0500d0707480c40491440441110700702c1411103c40040003640c0c000f4031034001c040000c8009403c4501d88ac20003c82a40141c1c440075041007800b191180d1030100c2000000040e6420a0459441e0b01c0140740c142c3c1100c086030790800a80410310000040f80e00001030703883d4802e08074104004075584540c0b03d0380040003034009918100e1401c20b04040d802c5080d10096000713803891000464818100401c2014068203045031482d0070303281c41c01002e85c5050040a48031038603012101c000c01c0641508050380640507401400d50b01034800c0100043c01c4d07001a00800c812840700b20b50942412541c041a0124000d0420003074041c565800a05414070707044c9100d442144421603013904240e411410039646030801d0704061160780d400024041c419401c070310160000d080c200c000303000030700b040380389080d46039004000b204008201 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 391701762 1250 391700512 391700549
    0x14011a03041407080307031b050a140c0a080c120607090e190c030b040606090e010902090604030f030201020901140313030e0a1a030406060504090f080306060f07050d090618 76
    0xc1ca0382d80310044208801c5503426a21001d006849034802802280030800c0010725102c49141e048d01082c1e1030341c00c400a0b250071001525904140d4441403102d0913140074049110556030744401c0188040d104030303001450399042a0b414007d050008858289142c0d1014040203001c42e80300e040d00003034400c0000013044603159848003c00305c42546003100001402c04101144290741a4031410a04000322024000b49607155400e68144065014500450840030f005011008094009204410018203500d1403c0e40da510707500384207500c48004500507500050031841d150781c000f205014058007040307140d00e581400e2040c44568240460001d0610078402e480390001d070f03a640395510040550a459500004044000820b42c1d8130881d01180d90a1814001168504252052450079503001c80e4807a2a051103072204201a040141030a80c81070040200c0c030101c5610704080c0c10301d03501c600018400c915041c0d070042c010086075008802000344108407a500301c1001c02040341100c1d80042c114502440 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 391703012 1250 391701762 391701773
    0x30c070302030702120c0109210f11181801062709051c02060f040206270a030602180f09011203090803070c15020102090105030606030a0b090c0a020114011a0304 71
    0x10300f00000c1d5010341012040d0010702d80102c3e2544070304000341da840032400e80ba14070a100c0d80d104e94105214120705e01264078001000303500c95420285c011800012641001c0b400500312050b840b000c2600c18001100b44000380341c0f514200c3e00426182d47c024415681003280c4013003019548014458600305030f007880780c4001040d910443d4001d0300079041d20310700ca80181103510449100e50100d80144526000a503000b010322203d6401194014040d07442c00d04118041e04200c4d800e07813000c800700001c5800c00092941c4149407903005512444026071203241d128148800584860300c001d0240042015003012a40ca458034541518041c0102c9914281d039400e0854041100e60010381e2544000502d14040c0084d800c030183c2150062010600841c8032094202c0c284c0c080d4100450124900784049141864032102455101c031203d40d0004802400700c00284884100b9103041108000029800c604694280601084030340301e0320144489515004c0c8070007000581071a90540f40002101040412a = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 391704262 1250 391703012 391703017
    0x50c011b0c0806070905040501030f03030903051303050a0b060f150d060306020319061502032502040f091506080c1005120f0621030a14040f0b04030b06030105010506030c07030203 79
    0x1e8220003010140c64a4010140c0c0c2c4071004c1c0e0b070700404102e80602c0000d203460a03029a07810380740d01554840c401a510341c2c00790094600d0f42070803010b04c0000e000c0400010700f03a10964004501480003004a2103641c02c01d0304005e180a40306a005010404064a050b114840c83c01c03100c00c0f1042ca00c540d1b440300d80303860000400f51500700806285c000014054409040600d01c8680300e0000c0040110640e10740182070001050680c103009a0010300c0543c006510350070340d100c0c94042505441c1420724042d40041c040701c100c001c40c0d00c80d507551100300030203102e840c4903010195414110300300040b50610540d00e648445204015100d59240c250400c00c0c14868419541d4101005042c00250b04007083d00d01012241125420701940880c0661510003a84c8411840f40340246405180381203000c400c11101004e00b5400c02600400070000060788070400d216540050409000058890f4210700c1c040e1040600642a40d100340e0500d4010b2220f0383c0c0d420203d0340c012614030b4040e540c4510601d016810350 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 391705512 1250 391704262 391704317
    0xd121a0f060409020f0d06170a080a0905220b092202130207050706030b06090a0620033705091012050f09060a0608120d021b0109050d0507050c01 64
    0x11030011445c0580e941c1c1c094090101070000c0f007401d00105880d42640300f43c841041010303031200d50024100c80f0100c2e010030014400c0410500e400d5034000d849201140b10030901c405480b50104031181c0480d814003e6114030032494504890124180c2402c1c003d4400d00000c01186035407404c4001d100d14210f40d640002c0100103605000b00355102c42c20703806c0c02d0f5103a01d138921512011a0400030300308020300e404421500b0801d4001c003020300981c14140d0845a940c000d00030140c0300307000300c841d030360501d60200050911807801e4506007070424403400e0308000804503000500068454414520007598019003502c0c60301c04152105220070b22891412503e501250500611007440e09091080b40d426214403280302d8441d2400f254107030344844680004486132881224880d401508030301c041c0c18014002080698007450015041000f04000c644e00391403d18000d600741ea42d0341c40300c5810068280102c01d60700b011400c0950800c140ca44aa61300d542c401d42c042410420844244545030b051240701d80c2c0701 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 391706762 1250 391705512 391705529
    0x106080105130b490b060d0b2d0402030a03050f070c0605070b01050f13050a0e0313140a0b030f06130c170c09011b030302070506090d121a0f0604 64
    0x2d1101543c9941024100d1042d00310301000313110102407060701c02c1340d44444055800d801141c00c03c0700c1a10341080002c0b0281402d80d004411036205400f054000000c00d004804c0030302c840515000241c0300b240d20b0700e044405100d101009030200710140e9004102402c403140c150400c90303076070903120300011036a00c28140024003c1d03200540100c3e1496109024121561040c441e0300280d98884080000f00711082c5d54403640030402c9011106040401d0b00400d8008005200c08125a004005075900310381004008807814503200500700605c0d0030800c1c90300f8100f1410341c1c040d0b03000c44c10b00c0001c41a03444001e02c0d81c900e0640344d0001c1442926100706170300c00c040070100b00b0484150440801024061460050b1904600d0078001c5001326407040111007003c85c05171991000108000401000404000d8090382815070071f001000c080b84007800b40f548118802800703008091800b180240411081a41c0d11207218605154011284c1c842d11f0480072844049a03440c1d218440440002c0861250341c03c04420b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 391708012 1250 391706762 391706779
    0x90901140a052e030b18030a0e04110706090c06030b030d0f020309100206060f040b06090123040b0309370204060f0b09040b04090b04080d0204211401050106080105130b 74
    0x83c0c9038008034401c00b640c0c450007402071591140b5008495644000e100380034a5081080940c02d01401a07882d070390803c1c4081c0c8046400b46002810709059003100c0c005071030203a1141900c03003c010b00412a5005131401d82410000e60500304086aa0780703608540c0d00060101c91900406204e0080058650200300208180c1940c4440c14009440c1c84094a0290089254807141a110702d405e008606168202800803030801f8910001154444028402c414080340319540c0c402c0e202d112800240060885030880e1956400c01165980ca44800c606c001c0f03101515400c000f5119900d20300000d03c030300e40555001c06201042d800064020546070b40300b4a40a809020001140520030340a072101003c11101000744030580001d02041e00c0c090701000b090341a0350700003e0b000a044801412201c601c8840050503d600c03000078a20038602e808004801408031180c280810080313a40011109102d04024040c65140c900094201b82d0180251441813243c2860707030082c40900d80c1b2104400d44001e24450 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 391709262 1250 391708012 391708081
    0x1030803090c09100e15030d140403120c0302060a0b1005070201020c040f0c090815010605160503030a05100801090f02010807020a020301060b0301240806060703170a0506090901140a05 81
    0x12060f03418483d404d0060f00100004080700308840400307041031b40150140140e040200d100700d490301640030882d1089041403001001080d055070703503200018000e4440c4058142e443c06d0291030103400a1040258905101b0082215100c0032070707030141d4407181d0030070507120b071494401030303003040045280c094015223000b5540801410710f4128102140ea03545070418526181c1c0b5820b03440300c8001b43d03a042c50910342401008500e2182d001880c2a42d0300e0901c5415501845c0d03910b40c1903174016a070940704a0b8940b814014603813400031864000f000440003c1000022035640d1460340804944045d0502c00300d070780081c84180c001c1c04694074056004000304840e64952030942116002802500400c1c072038818900c1c03031824030246d81100000755480340c038860b6880004003c5503510041c0100c0c10040540b1486018030320705014103010f0011028040351600d4500d0502042c041c004040100300e82c1040c0c3c24034280c84003001e035075400074006000412556100c56010010101919622110710200901130 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 391710512 1250 391709262 391709281
    0x20904021603030b0103020703201908040915051003050703060b070507090b091b1608121501050a0905040527030c010b0301150902071104020a0f02060f010e01030803090c09 76
    0x2001c007a20a0b2000c0043d1140b4034011001c90255410040c003043d1001108145940c0ca802c45d001180c02500c2140c81d08090111601c40e8a000b1450440d6148008202480100301c1c2c2d004511481f4003c0c507d11020030300d800700060040f008030071a070060680e81d0f404149074902c0303034008c1c40141120740309030766807401d0500d00aa900c0c1204c0c410251058074200a001c3c80d0314203c52124007035150805401d025060394180000c0661000258600c0e04825041070800510620090a940340c8c010800302490301e0030584440e000920854898100982044140402504845200e0035030b8820f940005455888040e43c1a100307030010709517448200c400d03220107401c9070b00100400003030032884001d00c0521201b000b4903003030b07414101c81d01f5810290140c2c10320480e001d0703501030034a0b103002d6294081805142d4001c10b04980c00001c62400007140c2e03406a6445540400c40990494040007851010358540418002c03030040602005000c00740c00004905461002c208004403601c001700070300c2d940c1c10030320a039 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 391711762 1250 391710512 391710547
    0x344060d2015040b1c0f060f0e090a0804061101060308040305010603140708060f07180602030d0c08060d1b0b03010e0a06060305071e260405010e030304030e0f010302090402 76
    0x21074071800c90196010b070107401c2ca00a0318100c41510081c50704142010400030403045114088440d5259542d080b0107908030706024000040c40311400602600c1d00b400780b00707500f0b03010082250409611814591300002c3c128800c417000c4401c1850071002c81904181254050401e0340d10150882801140c04400e04c0340642c000000c13230348218000c005140001c118142c07940c0852090100700c1d007144001904a400018400343d002040786410b01040003040e040c0c10358525075400060050380003180000d0001607031b2181e000c1110090600440c2d921740200050b56099201380018001c001480780b101c141607020503808080c040c42d4500c29180d68551069070b00b481c9080310720301540d5040c5240000c00354041d11030140140384d981d54000c800b801491f03940384801c1601c07002104106840c410540720a1306042d10280c0c0d044070043e02c0071581894101a401c0d102c50300c0b2b40041d25002042072000103504440c1008007400c065038507014904000c00180c00a000300c081060f0002c0c000100107948141c2580c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 391713012 1250 391711762 391711823
    0xc05090307090b0a170a080d14090c090705090312070813060c03031103010b07060b0a050303070609050601141c1b0602010b01020f070605090f060c0a0344060d 70
    0x2130400c0c0c0e840d500ca1002020700545040150756800088290000c1240035004149900c0d50f48404203102902c80e0b001036081c542183c0b403100c0c0750000d008001042c074040501e56007000b00340c580b45080454250001c2e4039a000c44000c1543c0d2800000c4807400c01c9a0401078565074400409030400c9141c0d124800b904e0000c045100f200001e18080620302140030b010240e9060b5141040c0a608101c019a134000007015028240d56020f0004d90000600da50100000c0480912400000c0b841114031700e0302c3c0d443c1c824182c200704044840004010540c2d12007407000414000d40c0d440146042036079013000380090f80003585051559034005004194944c0540201040a03070a90880d40c3d4120725203440754556506024640000d0407c01403491280b41840c44440e1005000300b043d132034004200e0304181750125441c81203003c02d2180a0240c1c00d40e01800ca074128200e445404000b480a20384900e80c0c0075804c01b482c80c0950300d50240410040d03210609400d4000368010312001c40d002440b880b05100030034115 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 391714262 1250 391713012 391713019
    0x618050c03070e0105041a09070324060e0d062301081e0d0e0613030b01050a09060b07020d11150c19050c0d0305071b03020a12050d030c05090307090b 66
    0x10262156040002e0508212600c064038000340c0d17400d00741040054020b502d0300180d140c900d000300a043c4d035121503005008003195100002c10000022401d5996a402040840c036031141c030400300111500301040368144903084403020b0584ca003070301e00f030070003045c0c4100002c02000b0103089680070106103812480c16581c07150201c5030668480020760f60180c0010b01101d0a582104402c490050300039540d00315003280c000c007101d0502850524280344421207520683e001919800100914100060918084c141d02103041c07107200d0408940d0900e512446078000e0164040219440a112011041d5a46e038070009040041c54038800104607001e801581c602c000d1400380204110031081d00c103d83c038030f000d64820050014894132a040004050785410240d0070310404000407070018612402055858580f014000916800c0d8010f000c00ca296035000148990040b42654010400010380740b985c0307881310314003c6400c0c0307411442100c10b40030f040890703034040c0b05102d0080707849201c90304100421001035 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 391715512 1250 391714262 391714273
    0x5130801200a09030318031703010501111b010507061d010b040f091106030a0204150c1209120f02010203041e2310030c09032312040b04170a061805 65
    0x8031100741c514414200740c6004030703080d070800f000043d000d102040150340300c580482c401d1568a0b160048111102403040c4546140000103100700d68000c2e848840b0f80a54400130851200c183c0d42d40d0a101c08802d82081c148080440e03030b08100401500301c428013102d590b0764103032008030705076029002c4c04807148000d104a05201d614100d0786013a10030001c82640001400c120408258184074040e80050030341ca4100360208408600088a00314220080c03009641c0c4501900e407a04040814030240340c4010104824000d00700960b0482034040381c01103820450980690b0640e01c0142d20314480c80d0300041c110718003030192441106844840104559604030b002e8041d00c4141e0f10350542c020b02c13442c11684001c04020811076980f103584400d02d42c94160400ca01d5180e140d2325a80da80101ca0405040c4c44880b4603a0300607205000c2c010b0080c640950b4a00c035041a04120040d01940500c0c0038100300c0b14880040c0903650700c810000d00414540162007041070401c46040b580c070140d00c2c110305860703605c500c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 391716762 1250 391715512 391715561
    0x120a030306080606361f09060f0b090f031006030c290a0e09040602030a0b0904020604090c030b1206060916080604050405100509010c110a020603010e060105130801 72
    0x2080c2248110f000800c080080306440070070011803017a428a00641100c0d070041902c2203100741000700d02030f5800100c002c3e490100442894000201908a0f4901c9414480300304800f4580d80e1520042d110041c41d060344654a41c0040756a8100020b401a03062040c0c1c11a80c05202c0c2a61240090340e01800c5119844c81d111190a12104154401d80c45098550051141c81a02d040d026005907289403030800380c540d49100004220304002c0e201500e11540c00418012120018810303003114400549481540e031401da00014020300451040e100095140c508000d600b61081d4000741103d0750080c08040341115403c4501da45110445001b1302a1103508007207100a1100f8902c1e184802d03141c3e030b4035042030340c1e01d1023400041c0030041d1040b10036200d01001044090198020144111003040000400c0c41807010020400c000c6194201072582191720001c0140c0c5461040700d06551804000ea001500c45000483c1d0314414650859002d07a40d110000c141c010064002c3d00c0c1c0601000d900d40144480c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 391718012 1250 391716762 391716779
    0x904050a06050a1e0b090403230f030a0f05040b0604150e0405160501020304030b0112030c060e06090d0c02090c0a0c05070306050a05100e04030f120e0106031e031b0203010b120a030306 81
    0x64800006e5110900c0750015000a1241c081c500d100440708680d031a00c0d00c00c2500c244282c0d000803100c4030041801104014031035282e407081e02c04e80c4e204030200b0700580c20f040d2200e50011201801e424084c5484007a02e0002c1040c07060100001c00c10480540301c185440e04025844046003401a02c9002112400190641c40003040c0c4d410350750440320422859282c030744400f02045401e50704070140410a0100c10200f0080e00c5480400d1408101400da140fa0000060303080030000300d0300d40f01b880030182c12140980c4a51000319880029040c001d5503071304054505441c49064000014110b20440d032011041020740d4210f0350080f03c8210301401140c60341306000c035280c9002d010388601c040720500094042445403039020700010f0360f420509101506d6140b54415140700c0011401540c3d140e8204104005070360302c0d111a021a40c0c1102c4454070040d5070010416030f10b00310f000b141d99400d0a6410b042d941c0a41c4011b2601c40d0060080e021040700784241a16101d05040980200c1d280001c0011000d8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 391719262 1250 391718012 391718021
    0x705070b1903090609060606050d0f0501060c0605060f1c110108041208130b090703151b080c04080303070905011101060e131416320904050a06050a1e 66
    0x19407121154580e09a500040b030007412801001c1d144183c5882011010517124840e010140c50790741d403005d0741c1e0fa4068050030b06440c121106600204e141a0041003c0c543c0046400b20181e4800f001250300d440f0200003d115038030624540d60300c001040b085001d41184841e10100c1d40c1c0c412001c20190072130742c0005441c1883c040b01e01602440d110105159414400d480c41540a014010207045c0d125882d12031140070f040480e544003543d0700017107050080c400154403107170007551760582c1800f5081c19500700300c00703050b008507c120504c014007022900034040c0389c3c113480217000e0003804ca0f900c0c0c0c5010107000340911010710407280811400d0450f2951504c1c180281e20a9131403d810b10f83c51070b2200b0176010b400301d41500058071401c1c000c01c0f09402580c0c0a1007000c000d140402c1c40d0010890904200092209191340440f25080941000c0e51041d61040b091802d642c10440e24800c0c03941da1810040e013804901e0340001d000a160804009803007003240d0014400d1803004d045080e6440155880780b0458 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 391720512 1250 391719262 391719277
    0x305031b0709051003170c160602072304090804080a030203071a06010917010e0307120905010c11060f0f070c150521040809090103030e15071101030f200705070b 71
    0x1400c4d5110a101142c3c07901050340d035400c14403009500d00070001c201c50b41080500c140f200c40c086801c00c07042080c581e04201740d001a2150180408107180100074003c0300503480c0c0c5403640110741711001a010311240c0d20566006026036015501040f601d864025225440b2003411140440b80480701c8280821007014a03100342410b0b1a03801115060200a41443e2107404105510f0340d00ca0a00d0842e0780410700c00b410425114902e0343c4034600c02004081c00f8440c0a400540c100b0210000e4600400c001d08402c1081400c140c40c4c840d034030030048007100803501c01d0003c0c4409029001800c50100112411217108603018080400070011020a04840c80d105a5580d0b204c91441d07043c100036822680200a074010340310b6803e461511050901140502c00240c2c015400b00302440030651541c01c0c10f08450030b0000f240f004c180c0c42d100c2c403507031001a42c09003280c000d410540c0c0d658203500816510303402500e51010a05d1a4404002c140c003501c6059032040c00102d5803800b86040000d041841300041d18401e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 391721762 1250 391720512 391720531
    0x30203160903020904030e0a26070806041e030315140f03030c0a17040f0f06020c10050a05130509090a02011d010c021002070b1306030c1d0103090c0305031b070905 72
    0x30f4407691822547d42d4405081d048d400b1054203000242c622554154501c504500300c0e000d54140300c105040c504200300d079407044045410000401c00059180d1510300c00c203105203900c030160103010f130a08500804414009100c03210301958046000200f0440000d040c40c0120f406c404c1401e03901081c15182c3c010311820850b154090072440c00040c0c1c1d550341960034140d06179a013600f8240d45130f800300c0c2156a1039115002e07900d00d0325014002c0903410301a400d40000107036110704d45e290f00e0040040c078920454058204200011810000062110107190002e1100030080380713860411440990711842c4c2a43c080b40401c030011100b181380c0401c0320380b1300020b16058490144481141e0280b11180001000030300440c02120404181c1e41c407080e024082c0c5200100f030314814141000f1001e4119080c64409100340680e442c010551189450b0000400a0342807801080603032051404062100a030380000b031050202150710030108a14464041070060403408454089540349003c000701c940590340d04a4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 391723012 1250 391721762 391721779
    0x21090501180b1902120f04050f12040605030a0213030501020d0b0904080a0f050d05071d04020304150b0a170604061503080717070501090b060a091e090201090e0703020316090302 78
    0x92001440741d070011030883d20799001d898101c4604a01140c0c1108443c00f40e07841d5256428001800402c010030254013003444000c0903d42a40307a40160180141d100d03100030003030000300048410701140c0654800702d55001c07140ca1b22640b01c3c03070480c1c040d4102c00701c80e41d03615180a20714001481c4c809520f90041d80c00000b0341d8541040300108807040c403204618a414400c0030440040503010301d01c00c1a03c18022a6110140340c0c040c0c00030134210880c440e0b8803078412170042c0207010108144c8400b407410000c04c18800a4219910b02c007243c00500703103038000c00364102c3c1000911150600440e409225900c03c410801c042005181c42056071880b6020182992a040c00842c00181e194010101d01d24a00c81c11a0b0411245039205402e542c0b030f00c10b046800d902c0407018001c5600b800006240074104074032081c0010013541d03000c810640c0003841c1039030700c89407284000000d40e40202e0740300002e0301e40e00741281c3e4546050700024019503c03e441d0413403080d41007286900403a03c91803144082d298000e28281 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 391724262 1250 391723012 391723021
    0x60102030a091419081506010e01050a1d030a080903160b030a0f11030414010e0105130f021203132301080f0a0b090a09020301060e1b0a21090501180b 66
    0x809044241401a401c2004121002c01021079041c0c4000104458401007220254006c40b42c0d1301034002401660500c10b820301303000441c0e81c115060b9804600c0070311f0842c05002d1414000031140808a5036280c06024030400501489686001030141070170076401ca03005090302044014042c031152080c40c0e2030040605c04202c80030303190b406c0013580340002c450107c0c0103c00802d2501c5a507005031012101018010b00e50314103c04203002e6103d0b4201090001c100c2407070142000e00c0c0000c00308000410042c07a01c20780c1c00442d03540c3d0070280b400c1d02549003201d480d10541032652000c00407a0050700303c622040d45e050106035078039180c040400441030b540da800603141c0c00140410301c400580300c5070581d9258001c0300c1c165101d640416200d40c00d001c0000c21004814010315084895581003424600e8060040101111000000319292645100000d544058407182114a041100928041581b8002c507021300d469071600620300003030041e00204003070f00760120a110007410b16200103107075420800014 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 391725512 1250 391724262 391724279
    0x18120309170a050d05040806060910120302010f1a12010504050d051803011a0112050c030105062a100f0509121605010501030c081501060e060a091e0e060102030a09 72
    0x101c031411101c02281d200e40c0050355842d04007003030305a20300f0009001280400508000300a03d98200304291143c01c407a00f440c03124602d40b002240941c0d40c40701d41c86d41100d41014400d40c80390414100000d000c009080800071006c00b6240240710a5105903941c00d04602e2076503062140500827a4058001e000034241c4040c00e0704d16800844200c98075903c2d24030301c004d0984003070140056041540e41c2c40315481c2055000944180e590f0311408601c1880c103000c100d105000902200d0555908a81c074645620104030300400140d003142c180b18402180712a07041020000054003103828a00c5081440709808803078001c41220710868400c0c0072035106c8400103040040441c010091a40c5101038070035080310741d446590a442d4281c0c000c03514848000001c00421400307000003a0118054150074005524100000b0110211103120a224480010780b00a81c6070281d01040004c000d482d00c4c0c01d14502c0f80019006501701240300c1d01d100300f500c48000601c3d542c03012044400c1e0a16a4403401092410150031 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 391726618 1106 391725512 391725539
    0xa0f0c05090a0509130c03030305040302011416080702010e010c02031902031306030b0307090e0604061b02030d02070c12080d0b0402180f04060b030718120309 70
    0x44000716550101800b08070b90307003200e584c1c4180e1190289103c0d100d0401c0703002401e014140a00004141e01034103c10311550003600204200c2a0721009140c040c2012181c01c05080d00100c240340f2020700901d484c0f50091018030000898040e03500100303085800301c0041e140940d1000c03e0b40480685074419503000d441143c4042c509008210318146642441801150b007810f850320341c400d60075182040380c540240900700081c44000ea096503030369222003090760143c8a0900304882d4400041d40184181861005a8000d51818016800003c002c2d00310380c6003103504201034000060030b8285160800c0c1c4650246010307503500c441c8104001c0c201e51802c02140d010302d0040c014110130306040c0c001c4440c2d5150640c0c110b0080d18181000500605081d00081c41c25079000c400e203d80c042e03015405940c007201c1d516000d80c1d826240c03d108041c1d42041c0e030000780000c0720541d05000819440c402c = true := by decide +kernel

theorem cover : BRFrame.Cov 391546762 391726618 := by
  have h0 := BRFrame.cov_init 391546762
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 391546762 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 391546762 ≤ n) (h2 : n < 391726618) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
