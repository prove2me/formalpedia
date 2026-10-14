-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3715
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:28:09.002083+00:00
-- url     : https://prove2.me/submissions/a1169150-26cb-4404-93f2-bdf6e1bed92f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 667985611 ≤ n < 668165467 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 667986861 1250 667985611 667985629
    0x120a090b070318060b0a0e090d1b030c02040b0402040b1305010e0301090308060d050a1406010807090614040b01050d0e1f0e0a1101021e0105041119090f0605060307050711 75
    0x1c0403043c0b150084480e5103070940541301c25000715070802030070b4000040d03c040b00c800c007500030000b0001a0241d070428400c000c0848120700f1110203030260300741d9440d000076003110f1880656035060781c0c049148003030a4002402130143c0c0c0d201181003100010b08805600940c514807003910000d803a03100707203504a401814200c170110440100401c809401080e0f06142000d041070380c80d807007003080344c402a220382d0b1414906a101c0120101a520440061045030000d00c41030024002d4118200130315441c00c80180c90440002c215280900c0d1742d44150715103039104508540c0380c454541400d00c5488005003e10795291f03407682035400c0c2d0b241000c1c01d8410100c0b40c0d000d94481c051181004001030042d6444a122170842201c0850540c82840b0b41c161402c80c010142601c03c18542c000010146060704080ba1074030044149144501c100889011040c2903000407007003039640000000900c82c91504a02c001003009402c5103920250110030400b10320f52240040c65441d11a40c21940c207207803504240f0154035 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 667988111 1250 667986861 667986881
    0xb13020c0727050a061d01060f0e0901090b0f0307060c050c0604052115070806030c03060912070809040603290103081b0a320f0304030f0305120a090b0703 68
    0x1011580d81da5000d0340b0039049207030031628400000503101d54070050140b100e0300607000c031340c40c0c01449801004400c2e041598440c01840301d090000448601030006804006d0500804080d150b6035a8a1404e0f42c03500c1111401e0b245000d0103c03904280c1b101005031a02024042c12202442440b5600d107841c107041c07042d10200e0340050081e01070740b20300e084e80e1454070382e10060100356031140c000e82c0001c51580390103190165884d5200c08070942080001d041c10469440649800b0b54420030500080d503000082c0500410466184540c8507071561500040038443c841519501c00d040000220611030124540e240b1400d041c41074614030741e1805451205498241b10180c07002ea020301c4014500202844003200b000e20203001c2d110b01780e01c0f41d520201e11003083c038104480c0a090780c413120b01d10706824044080340105c000c02800303031040c6524010755034801c500006014000820203402018000c4056a601010070000e5204074900340c21008010808a042520300c07050b90808120036500a114881c051 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 667989361 1250 667988111 667988159
    0x10150b0403060c050d2a03020c30040b03071107030b070302030a18110405070302131a070803090a0309090203070c0f0222050a0c020f0a0b0a0b13020c07 67
    0x20500c0c649400d0000d01d820140107003805810404501685d945100e841c0100c94001030005580707560307059000c40c0c482440100701c1810f00c10810720000c0c0c0000600142c19407048581d1180151038101101800d1502c0c00b003a0b244540081004500003e018002d50f20480c80c40d95244609100d040700356680b0a554032020300346805030310104a203184281c004640c03080b0010b101249501c201c0304642e2003140d00c1d003004d90300700401c82d40300f007841e280a028480d0003115518044d03090203201000404c40500c60300c03e0030701b4400036083c45000c0c001f1820a0314102500800550307240e2501c0300f94182c4900d071141044000480010020500c00c3c035920a4900903019a034030210521126030310803184020030743c01640d0020640442a000910b80190707800c648854100100c0c240c00d19041120984140c01108410340d04040050204003800040c00400ba541041240d4000d4071607220000090800b40049a041107000c0c815003d4400386400a0140e110602d00701c0380c090396220742c41021503e520014001e0b07 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 667990611 1250 667989361 667989367
    0x201021e190c0807030e0109050a0602060f06010302030c1204050a0f030206010e0604112d270904030507080a120c050408060714030105060a09080102041e080102040b0a0809150910150b 81
    0x11074881c6c03401020000060420012207511a40041d4103010158059030041e0710250402c06500d1a101202d50414003e08043d4218109001114064058405004411a4014000f400b400020041c04002c0ca8202c0ca8008804c985414029100c001c24000c0100a281c020003140c0b440c02c042c89101a80c00c00000020304000e840e034021042c070380d003081038200c0c803007061501020000d030802d00600051f90076100f011034190700701030f040031035102a2200d075200d039407024208808240c10208682c0042d5002144903525011490140e464841c0d0034502024240391140031003219801c100140141c500c450111009a950310b41c003250100c40b038082c05030b0488000c0c00100407901b80100034003103000d546d040104510361510041ca01b260080d502007051901c40d41d4500c01302001f28081e00016110490095140c907003400000300c900e100c0d0508003410003c1c802d001560304001449028a160742038040d000081c00d1107030300280c4c0c44580403648420607140220300c00200d0b1460034224111107d40c900c00b07003 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 667991861 1250 667990611 667990613
    0x1b090b0c070e0415050117012a0305060a030b0f0f0c03091e07230f0901140f04270b060102190b09030910090e0606160f030201021e190c0807 62
    0xa408001c0c0080301c825008203180701070035113140142800b90041e6403450200c0b15a80c4c0525094483d00000400c0c0d15402e003d503104410411401c9189030002c9027804542c61300c1c0d80c40414042400ca5001510f101c1d220011320102c00d07400d00c00240625000c0c1040c51240c1c90341104094284800d403068801a4054a40c00207844600d21a020714800e144040d00c00315940c0b00380000c5000303503000c0c1c080744030300c80b01050240500d4101c00681504d04103407a48212981000d1140c01d05004100c40310f4451071302c1c0f2320980ba4550b540d4005a00810482a02030a8501280d45801c1c298080b150210381c01a200030000b50694400100c80700b503e001c500341149911120744070001d130800003a084e0010740c0000c0102840d80d4031007140c0000f00c0003050745c80c0d600c45450161182d02456019240031310440c1c040020040442c1810348103100960007440709003c42000b45016030081c802c940484080310100c07002602d030380d05000301500b5454902d001507030703850002c1d4000b103902c440e400070020b09811003404500 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 667993111 1250 667991861 667991879
    0x51b04060e0117011202100e0607031e092108130b0a0e030606030d1d03071509080706124101050f2209051903110a08090d03050d1b090b0c07 62
    0x4281f1400c14141813442003012400300d202036206403425004074410404001c50504800c0036910110010f240c108a000d0410341c4d0081e0b504052110005c7c207075407840c503190038004c8030800c803202040c2030b201d20b00b410b6946a400441c2e42d0070142903d0003240c4951444070441c02c005c540c00348280c80040240403114070030401540e10b40b0003180551020b1000100000c1180c86c20050344000d40b000c3e00603a000364406a8005000d044543c2007442d213904064000c211140d0000503606200d001c41c2d81c0442d034030146502021003040170110b01c0f03009180b80c41c89840900b0540c0e00603150b100817400072a00f141e8a600c00d02c54174840300b012054004000c0500c1450ba41d1000c0d03055500c4004010340455212240d8880500c0d003081c84544500070002003540c10109500100101c0140c500800500f4690b41180c46181c0c05020b1510898000c100d4058103800301403103001114840410301408001122817800890340c895044800d40e0045800b06030b01040e410442c0040c0c40080c7c489400078074407582400116 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 667994361 1250 667993111 667993129
    0x91605011b02060403030801170a0512030712290d080403062004031518020102070303081e090a14070f15090e0a050906150105040306051b04060e0117011202 69
    0x7150740070003210a5140182d40d071030300400080d030180d5035400041d4144986e40300c5070031040507550320550000d0f5040c07002a00204e510001e08004807500c6440e9035548600f030742c6620244800076076061501a0240c0c80d1400038955541d6043c001c40d05001d100c490f6424000417442d52031014001d030505100400014106400c12101090820200c2e010080c00080500560704550801c44407000f040d14061003060451240b04805440100403070100981900040c0d180d0740c42d408080c0400480c5400079001c00c010029078012403550801d000c909203880304010b9203445c0e142800310380201100f040145060f500180344230517640c100446120f0389140c203228103038a0580c44000d0060202076100010805d0a0040e4244100140200403c082c50704081c2c240c10310038028610200c03008040d01c2e051a0b640d0110607541038075401000040c1ea80c0b200852000540a1042c20300b80c01200060b022030700310341c09034006510700c0d801e03200c0100e203805655088032800024000c10b0005ca040f00c1c19503016192144103 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 667995611 1250 667994361 667994387
    0xb01051203090603040c061412070309060b12100c170a1a0d03120608010c020d1803020303340f06020a0324050f030c090f0c09131409160501 62
    0xc4a19058414000c12107613041198241c0343c2d52010b074001c2003041c5d040b44004001506400080d4034044c0310b86c00b000c08544014103103030b02301030740c3e42c50000400082d6809094109002090002c21100920780c2da030350b80d0000b9003130005c183d003000c0c108a2507034090308103017020012074400384a007555000d002900078820000d1410001c0c4075540100116299584407007001802560740076081001c451035034056a1840d8011070340b582c50311403400e61040d070100711808410462301d0f055524500c141d640da03d03d510b10342c002a5050200003030951007803140c410a03070580f03102500555102c50002050707114541503e070002d0103010a0800c03490008180794018600e94800c0c0c02c0005016180000005560708040b4121000d100c5403c8180300500e0b00c000841e055100490040c00c1c0000d00c0e401140364a032000d8081c2c0158034422002c03407008480141a41c1052802034048800e141c4810540c00c0544615154002003098500c007150044102090024414110304030f5180715a00d02401128011081e0340 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 667996861 1250 667995611 667995613
    0xc090e04060f110d0c0804080a1115010801021c090302031c021b010b0406141c0c090207051c0c05120a0203040909050c09010f0819210807080a090b010512 68
    0x561051424440c803d40303403205040c40000740c07116a0b4041d09021500041800307000d102800b000c200010341c850b001c032580890741d45004543d506d503c01041e4907004c2540504600300392450000b15a20a055001c0c2140c0c205034010000705202050405003151b03064000540182c00400c41c85e58410080d044a1134006000d400041c5401f8005e014070310310030350045101e0426510b403007401e003191506001c1c3d031025040001c00e074095121040c0009d916000890101c1000f02074415010050248101c1c0c580010b003c2840c055585400034507080761503070144841000300244040e24490414885c4c06404203042c0c0c81002000d44401580ca84a2035805c580d07140300440c4020000030070b4140c502e0003494100e500c81c40050100500607810080340c450142c2003240f8400701528100130f0414000b43c01030040301a8215102004601d080c050000c08502c170380e000101c071040300341988003580318110340e1181041d66601951a00c5900310308044d01c10014015254072642c00042c022460a03000c14190014084 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 667998111 1250 667996861 667996871
    0x1c0b0d02030604050a051b09060f0402040302030718110c03030f041e0303092001020318030106091a131a04050c040825050307060903060b04090203030c07180c090e0406 74
    0x2600203440c061040f50102e925030049503007542003160400909410051450b284009020110082034200c00000c0100b0710506030102680019200d580c1204d015580290640e1580e030344070002080043d01003800d401d1070600c4c141d000f00155142c1e81c261010400754501942c0f540d180d0700141c0c071a00901a000352400800b040307888140b60540c00310044090300c2130b2030110303121450341083c15560f0744e100c1d002c1010501001c44180141c1c1d0220840309000f450362085042003505002080c01015103400c40074000d8074000d62011413111400b00c0400c0380400300c8511780c4441a030611541034812000039100840e85c403014028462809800c21035001610038040d42c201940c1740b406034500300115078038038841ca03003030a24030a07904d44044200014001c00d40062601a2600300010115a06407101a040c5590b50f400d004043e511034109800300760f001812283c80d8141c8184403a2692150303c190f840c0b014800040540f280014003801e1602c6045440303d4821614041c8a501f45020050080351425590 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 667999361 1250 667998111 667998113
    0x903030c0807140d0f020618060105010c0809100c02040e0106031104020a1e0905011115010b0c160609090606080c090f0315040f03090801290103020909011e05061c0b0d 74
    0x8014461a0019a0340c1d000c5d0022108240a414104084c00e2451011010700043c03160305d00010340141190702c01e2078500101680e504081007240191840f40d94420440103107a04015880404140070034000c507010000c0000010300309003200e0091000800e41003105400001c540b915a0141002c448103090580032800b0382e95440d10407664042503030007c548000c10920095030b21a940c5200b620b0503500900010030036020f205190a0148180f1f00d45050002e030780b0346d42c041c0038845e0388911041d603a001c80f609925103201901c550a01d00400040e14074000d0300180c0d152050344c0d03a40c010303401501d40914040b6018284038600100c5844c035601846851007001c081104091841d100d0b50185040180101043c54014191112030b4004240e13030381000406000386010500322007098051228911081d0525001600a401354031a0319610115910002503010714480c5908480a50400c00c0d204094450080124600070741509001d946200032032803070344000c164080100c4090040c090390318000a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 668000611 1250 667999361 667999363
    0x30a0611071a01030605060603091b0a170105090d02030928050909010c080109050405060a09020a080304030b0a0606031b18030c03050a0203010c02010b181f0f14010903030c080714 79
    0x2211802501d0703510400c01013050000910506404c00c00c204d130785502d1800c168140f281d840c5001d000704812107202c451819a280c0d1085100401061a420300340c0508044944c51030080c8402c82e540e000a004500404200c01d10100441e220840000c0c0850100360b41d05000b40291194461501001011001b01140301e503510100a445521002d0010030440c001c580c4c010440031060303021040e0b4506020500c40050070228490f54405801c6000103980d8030640000749420341c80354441800e90100003808024010b0101d0410710400180909000113942c0300e00440c129507400024403807902640350540c0b603a0b8400c0312034100c842c440c0b42d01080082c0d10303278464480f901d410303601c01c036981d03070102c2414421402c00b800356080070a07550008001c0c81d800c860101e90441d0350070340085c002c86810000540280311505885440b2182490040384203600d4151280d41180341d402a984c1c101c1d181c0708400c0180d84200d0780c003c2507942c507a90f03149001441d9510303100300303400801c4222030180100343d11112203d0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 668001861 1250 668000611 668000633
    0x1e050c1614190c06020307030c02060903010915092a03030f02011b12151503020a12061203110109030207090b0607020d0309180218102304030c060e030a061107 70
    0x9444080084282c40c58407490f405110740c080d2066420621403280801d411512174030f160354040c0d0b01c0591390242440068010480084010034500c503107400008940020b510042c0c90300d201e00c4040c00080f81d0495041d0030503c11050109007001134410500000313109080170013003c0b03143d00011a6900070400c0d004800d4101550b2400010302d2006090303402400343c01104445a825040006201d04100401d038046d614500303880107168001403c0f011440c03242a294043c8104102c0c1001044c0d00d446c04011003200e80c11065000403411403201c00846018400d0881d01541070300209030192910030740c41c2c082e11604203402da001c03006001080160300c5100032284034512941c1c518581c10b003400d9891202e01880200e035550144103103c106422410b00d40500c034080d8044500780c240c104020000c50700200d810745041c48440c400b40d840c0d10a1600b007409001070b02d106140900c0665100c079400c8a2400140d60300903030591000c0d20707000100c1d43c5644912540311841070358a250100d551a0208666 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 668003111 1250 668001861 668001883
    0x40b070f020d080705011a06031b13031a0403201b15221202060f0d02090a090605010206220b0a0e070f03050c0d0f080c07030c091e050c1614 62
    0x6512211084140e0509400740300d041f050443e02c0070709505200540500e040d0450150303680442c00012050441250508208010341d845031000200c903003030a5010440900c196000c4022a04400540c02c0ca02c504d013000070207020b00030008050307189000420790340980e001300d0243c5d01f1410b035010050701c080c281c4000b0801031000c0161010f210021901c2558441c0030f035888041e20200340880c510040c0c0d520400c441c100e0000f07d442c3d60310b0340d000100440003481884030481d446484032b10300084e03100950b044402264001d80aa038415540d99107a001c0404202d103d0042030810002450f0004540c84411900100d020030000388001d05084602e181024641104645c0410507004004101c01000010401780b4180d550840d40000707a0f03124000132a484500420006001c038007400c0f161020444030000f0b541000e142c48940ba40c81560900a18280c00c1e20100c419400c4040b84003000f45000391806000094bc00b18a4080e02c20304104903c150001c0c100c5900c10403a031411031125003004945128 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 668004361 1250 668003111 668003113
    0x1051603050c0c0f060f180d050a0c1d0601050a170114031204030b0f041a0c030f15010815180103050610091a010c0809030111040503070902040b070f020d080705 71
    0x40b21190700c2e0515000804800c0e40c8144241010390f10780b92030304820350300480c000300c545030748540303222080c0c0301c1441040c40040d8210f070550300d03450207000002480c8a09a401118580c810076240d40e00c101c54030348140b0303031985a100500b02041007541310360001d290902c031501e4803c20b490300c80c480001e041c070f2007079201000c0300848140c410340310728003404000072429001c1c03407041c641491035984201c0746000400002c0e5007030740c810004d010301220000717007083c0c083d02552025082c541412484420340045d1100d800e00300205001900c600298049e04410620503194621a075840c0000c03140c00c4034151300c0141e00462071401c04082e0320004008503019511810181c0030324501072400b080b8041c01340d40b2180040303003842c1a510481c507108850b5801d101d130a1030b00d0500d4044504100e20fa51003090031283d0903610302212407407010880c40107001075440403010b840c80c0b10340d6007402d202a401140a000303501281000400006012200302809280c8082c10400060340d09032078071310030740d04010425111 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 668005611 1250 668004361 668004367
    0xe040809090f2e17070e10061d0a1815030803090f0d0914040e030a020c010f0906080a0207020f15030712231009060f051e1e0105160305 60
    0x700c484240d40d207005510340c00c8240311072916110940101d102140b150a03000300501c60819500c0c4c07424400100a0421010403840d241040000c1610b04c2c0d444d440b81000041403c03100111000714040ca05081c050024140c0c1c85203401c2c2603000c00c1c0b00e03c1c51140c0111780f079550029a5041841e000d40f0500841c043c3c09182c2d22450140902c0e41000d9a10060460603081241081d03d1540c0149030b0b9002c0d10452425040071100d1240403500070551900105014400421348209141d40061038040840081c1d880303041320f0101c6030081d100346146004e001c0210f005000010b030b507241181c0c05412200c1c0010541450143d81001003070495000321026095104d0010401042a0700f1204210020342c164904000d0507c90700a00045206861140c000c541c0140b0b0110f0407030100f0100550142140e00c0c420002150360300d00d00c00b680c03001e07480707128003030f0b485200f00c42c50000310030f2041003241001800310404150903402020315083c40c680c00354103114050000114080e40508a0781c01244a602d0b030310740d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 668006861 1250 668005611 668005621
    0x4050d08030402040f0504150e010f0f23160507081306050403030824011809150e01350703060204090e0c030706050d09060e0a0b0f0c03060105040e040809090f 70
    0x581c1e170711041441d10f40d405c00e018007000603400211100203004d4104000b421407183d1211030301500e160001800340700e040030080303044180298040f01170076000440442c07101c0c00e41507008621250844881001d41080304030340e46c03840d00a2009040c140d00c510811850420a8581d88035890343c541c201500144012030103008058204c00d0068204440809480c1410b010f1801c0c0001441c903040d01c40e04105414403c1e400c0ea150606455014180312003092000300d0400314030902d130404c0b03031180182c4500d001000103101c503d424699110f0041088180d04c80e607511180291000f6a080310000e598817412000001281640c40500050440d03c107000c030703203089120355240c9840703000c0860b03078407a4108000030845140c1002c229903e803141e144000c50700452500b071040003070a10301a9a41c05000e61042102000001441d0600c01c175116001100a501c5444090304180801c603030440c08100c0410041c4800d0500c104020740c8644500092442c0644803400f01d440454203031005000c265815080c44 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 668008111 1250 668006861 668006869
    0x60c021c06050f0703060f090b0402070c08060916051f050c0607020307110405150f0607020301060902031f08070b1c0c03150b0906040311010c200109050105070b0f07020304050d08030402 82
    0x6500015186010300804e421f00b180443c0c0c1d1305441c466014400d594015400710b07901d070754054400306034111a0180000e0b5070741d0310241d02c81c6000c4541c29980c0c02040d80c40340c05030b00c004c4074000070340b1310103080d00400710201c07403610300102d21104020052100c18010020030b80001c1101901ca2039855014648807a4245058880c50303503000071491117541488100500d50508540c20585040100d403841c60b0542c02c500480d81070f01ca181000381d0594245900826071521907002140a0400b00070008907184400c503803080025100c2c05002e039030383c0141c441041910780c500040c10030f00c0c1c0341c40ca12a0500c0880d01c0600b0880e42d860301c240d00880c5e00d40190080350b01300000c1840040c00b1103142286002c02c140c00203005441030f03000042c00502d941406442e0390b4070458041800c640d100700c41c0362030041414541058220f411004a0001da103449010519501c02d406540700c1c3c42d400b04100d1041d032160205020f0300c250040c50642184000d01000886640d03884041c2d030002c2c00354240030358900b4540144 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 668009361 1250 668008111 668008141
    0x10c031e051b13051804030503060409030912030c0b01080607050403110310240e01060c030507050c0a0f14060412120216060f020c0306040c120c0905040b06040c1701060c021c0605 79
    0x402d1440e045c0808010102e60010101c0707900000845000542041c40e19041c0c3d004001c682001003150807000080081640048a080d6418011220040c2c20f0b031740e0740e00c05617480000701d810398000345061004200051454090a10b0218000d0039510303030350301c0e5a02d134404669541c00c0c5007202c0203c014044114200c12164070001e01402c40e0b9110182d03041c0038001c0c080251203000241040070009801045c08001d10213202c410744014018078550341c0c2c6400703400707000b00c02e4013500e14281108030b40c00b085880d20400f15000c5610080541700d042c05562640540319142c803102d90154000c900c2c41052000d060a01c40e00900b600c0d41760310400c4a86244020b14101c1c813008103034043c0e8411030170b00c404a8845c0d0200c108940720185140c0c925120341c90300100c410b005a0103440d040e81000140300411410400d0188562007c2da0100b090042d0300343c045a10f2008400b200107603035080350051000302c1c82903d8201940d40040c06804400364111815421802028000e81d2010390300c0050000380180c001318 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 668010611 1250 668009361 668009389
    0x6160602161505060f1c080f0a110105130305071401050f100f05030a261c0b0103050f0f0901020906190906090b0d02090d02100c05010c031e051b1305 66
    0x800c000303600c4e090011820080945060a1140324032100d50055091084901c2070582c1e400f1059030b440c1e000301481e5030700c15000702103248c0200e403601903040444401440749900c240707031103440705807080c10300c3d181030340c0369400400103450304028020fa44c0001d200c24003030107003c1c01040600303514130710b40049110781440707130f94000585045101c1c00401c03403030794001403d204203030f0404c0050303010702021184801001e140b0034003610554804111840b0990603c025881c0304100b0803001c0c46039a007800011412103c0488402403600031001c085040702d280c1c21001980011454001468905680000350542d0003440b841001c0301032110380720040746e50003404c0340000c00c030303e05241c0700340c0342060303007505c694000d03505040c24040e800700d80348485030b0340c49050703521040d005046044a5158a48010a100c445190035907003982460443c40409109208114403100c03056a41104504c980342e150010309000740034441c1d07007000d80c156410380c802a40014403207921443c0d80b840c02a031810091243c90b4200000c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 668011861 1250 668010611 668010653
    0x507180204030c170c0a03080c010c0f050d0c0201020d1415010e09070509030c12370b090307080c0303011503090201050421080d020d0e011a0616060216 67
    0x41000031942120482a5400c0c051a404940001d034130407850041000c000039070201c200034000061040501c010451ba026207c02800008103121082c0ca000320680301d074a0000714200000541c800807030740004107040f25803001500c0c007600d4410090560303084481250b5800101821302c490070401c5103c0c150244800e003021319585101a000600c9504001c03d8030342800030004000d05195024403a070030508034020032442107002020003080c0d0704c0345071007403000c0780700078180e6010b60351a0780d02c0b2801e2103508600c40081c24022596607585903205c0c0541145100c4c8400c0c041c090018a0010182c41c0c00200100111703100c0d8545044800d00509614106090501e082045c0000d40d0b800b5088405940c0580f090483c0d41c1e08054580041400d8050041c14446000c20100d4118509800420310180102c170107000a000922845080f680c8540f24819000e0310b4014085080c10410050009031502d042948004115034880030142c1e170001b00322481122461002d0410403d039031000501078400c0300 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 668013111 1250 668011861 668011867
    0x40501050a030803040804030f0b150d0b070c0c150c1505010308041401050d050c1e03010e04060c02031e03070311120105040b150d0e190812070c06050405071802 71
    0x800428401c1c0414000a45080d500000240c18809540d04440003560303c1840040000c05500344030358100b00503110b5200c56002c00c01095128500043c80c201c150350000c10b501ca1503124940183c425000c94030040f5143c14000c0310000c1e06443c5d00800624404094441c42007030b1440780f81c4a10031480e41a00212020301c1c020041c0701041c4a00140c4080d0b0710305811041102d00c001c030060754140500d10f10301614a007400c003000541b10b89080907103092032209801c0c0c0b0160a1920491485000901171844000c1d801e90008000c00c0072030b0883c82d86045240140c80c60000880081c200040204040354a200300002c280301140b030f41445500034404081407914101200341c9040303c0c0318207040c800d03e44101d40301c802401c80e0303648000b14141c2c01c2c02115203980d030b9a04041d1903d40130381034195031460103014560f014024500e40ca80c810000d642c0c00406c051505400800502038080c029198074104940b4031004400101c06110703c1c0d000f14081c100130300009180c884e0700c4008211b92402548598014 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 668014361 1250 668013111 668013119
    0x1507050a090b090109080307030903020307080d050d0f0e0304120308060109033c061a1005030a0e100c0305150609180a1103040b0901050f011d09010e0303070518040501 74
    0x31944500b03440192540781d54404100c0012590300c0900e400040ea10300000654000b01078000070101e00b282c2c4242c0039640025615031900d51619403084c1d41c9004101c04003c0001b0103103113a03005d001040f0b0902000581051034150441c03071a000b40d0840c1a0303460079041113005250300310245961118003481e040401a0071a40c4041881c209010b0446600c2c0704402e411020120b00c01c0159904401c00b200f80780d4030307411400c04d00c0141a02d50800445101800c100f40282d003807601c3d861640d0001515100d1a42c1c950806400040c0440c0100100b1030044401c00e20807107046008a1180300c00540c1c0109180c207049100c16180f09074011203d1003001c080241c03150706d88424070b0141816011380483d004650f220302c806d00c007508110000c1e078902c1c6400001c100401c00c0016145014003540b80c000c100a5841c100c01e2121480c00380108220030301a00b0207017611490000340d59a00400c0400080380a084a01d500345c503542060301c4100206801084020000c92100307011410850100c800748001d5140c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 668015611 1250 668014361 668014367
    0xf060709090612080c0705090709051804240908070f0210092402031b0102041518030f03110a05011a04050c030105090403050c120409140403020d110703020d051507050a 74
    0x10008120040200e20140c91410a019502c02807d014207004240e14101d0002003c0c0c4143c1d000d060301c240a46030310074100003999200b991140c1c4c0e02c600c0c0142e04a9079090700001a50040007040907103a100c07103440002448801c060a2418850070031008910001c1c410091415040f10f125001c00c0340000d030811012031a10044e00d006005403807100900180ca64040b030443c45900c0c07540404d800806918105c0410550045c03041341c1048104400804401318100c0d030f407010f0502051451441e41e10144089900c05a8042c6c20038420b061610001a0b9100d880d0706205840a00b91030710f035942c0e8440c020001c0c1128424407180c200311403c10180c80d000e05a80c0e4640818011540a13410f000f000404060142003242d400001c1c500c12640d8030100e40c0a0340c540d07540f10303004e44040107090412141c816461217001c54090340e07164026140f004441e0204842441294007503401398401c0100000140c1c95000c001c400440c05880a00b030080d041048601d210072020b8181c01c1005010000304034000d0b4 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 668016861 1250 668015611 668015639
    0x100b180603060a0b1c0804140132091801050108010b0702060301090903210623130f0f0608030405030d0e01081603020714010c1404051318050f0607090906 68
    0x3650000004440b450340c40171508045415000e88540c402200001c01440f400300080e204503045200030140c4140a103004407039103084291907c45085030089102e10030003076500305aa42d0482c5011650400710602c0000e54000030150112910291140042c4401e50b072101a040c0945007010400380b074070100342d021413900d200500ca0840310903501c4010078100343c0301e481204500002007a13003510513654804c01c0f01c01400284181100b10000141c0d20000c03201c04840c05800d003000400300300350b00071025aa03601805002510741d2600796180748210405599103c0c03076024104200056848a003804181843c01142a03159404c4c014120300c2541c007030381e02280b00350b40802c11f4102180c40300342d0001c0580c06400f50766401800a020f0502d481d13510f90b01548400316580060791001c00e150003401c64000284240d0040582221017481103610400300c1e60421805080303100044446039066446d1682006044181d04465401407400e008030b40c0c1e4440b14003005480518000c1082700d00c0c00703c030701c080311f9 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 668018111 1250 668016861 668016871
    0x150b09010c1103010e060403082a03160e0a0b0705120c030418020d09030806010e010f2f01020d050403120b0307050d081e130806061c080c100b18060306 67
    0xd41d20024200b0180c9080d0808140c4400340411101c02e42450b24001d400904100c503241c035100c16000c1035414050b40301c450005000040301082c1c1c55070720382c071440f6420500c1d040070000500030001d049034829106c900080000740112941d0035202c190318079000b0704103c004001841000d2090100c0312144401004070f034105d6582c840b070900c16484140440340a4041d2001d001e072120700e0300c04070b003080c103402040fa140304140983c0c0e0031000c1d01071000103485418861a03000005a2090f02c48079003610b02841c1005410750560581c109400e005201509a0780311034000c1c52025202c406000030103030042c4011207034944001d401d004068501c80426658800c61044034441c0c03000b850100b01340442c41c805c070780d86503844291a4000c04040280c4580c1540654407007036138803481d8080003800c45d501003501030164400501248000401c1d1452240d210700884003916102802c00203890ba0350b408000000c05040c0c0c4d284080f80c0110748208110041800c1456058807040e0035041000c00c0e5000b21781c0c1d507440 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 668019361 1250 668018111 668018123
    0x40605101b080c0106060306060201090c360222030b0c03040f020904030c0b0606090a14041407020a1a010b0702090c0d0c0203070c050a03050a24050109150b09010c 72
    0xa502640410300c00300d9100c409070a9034000541c0f042201010b400500588242d81c600b0f10000f80c4e00c1404908072107066401030f00c045a03010041c480901000003603085251007601c819440242c200310215420303040a1291250740d4009070f0a000c1d0341d0702c004920400345d014502c50014920315240c070b0f10b060000520103015103c002000801304462000001c1c11642c0191881c0c06a00c2c1c140341c00303131800d100340405030307801c54641d400100c280c900315084a99042e130250103104280e1508000c1700400c010341141c5548107403203101c0180c5200ca0002804c0c0b2600e00c5a006105000c00c86c14241c1c82c484129035081d0180c90520014840d80e040ca008a13503899034180c9148211b5901c1c039019501c140100c00c8215800b0781000c3e03028040719400401340c09164001c0c0700694400d5a0740042200035020345c80000d00c0c58019a081c0700c089444106c3c651481c0c0c5034020000c0c0000080b016038002c44009030403400c6103a40c0c50b003001e0b11120042d14102c001d050f0f5540101c2ca49400f00c80043c2c003565180c0030040c21 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 668020611 1250 668019361 668019377
    0xd0e060406081003060e030d0b061303080c1c090f06051201140109050913030305010801050702060c0304050f191b060e0f300d05030123010c05070e07090504060510 72
    0x4405a81500303d0096070061010041e809440740042d440b80c1c4110f414001440c240500d10a2508e032110841301c44084461180d0141891030f039038610680c10400481c0107501455101d03559182e0340c6c14000c1000c000541d42d00c60002c0c2000b145503503410064000d0801c0040034801203c02d45901000b0a041d00c030381d1012055001c0300e04004958240f01508015001700202c024032200078260401003071030728400d803420310a0360380360040c40382290011144030b40140d0202001c01c00b070006450044d90040d01460a8238136005480240da49080c800e103400d40700d100002c480440900149490619100302006007041ca400c0c0b40c000000d0650f41d407103400314441c05d41900ea01d0b00a543d900c1c21011180042c14401800440700c0302451754000040590071124003030190600441031084d000c480c140e40203619034002ca00c58a860180c5010000c66445042c000a5030900022800070042c0c04000c20045e0300a580a103040200281500125403016000d142065018403003650399070015082c3c0d01d007034172300303e00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 668021861 1250 668020611 668020621
    0x5090a05100e010e030702030c010f0c0602030403120e0303060d0209100815061008100915080303040b0402040c0306030b24060d0c0305060609130f0608120c0d0e06040608 75
    0x105000000400400078071074246481144241a080b0140602040c0d008012203070351040030f40c2d1039120791034000303505800c104040b8a80398080c07401d00c0b030803103150300c1c000b034040c455030b550401240d00a8409401081c1c194040000c3c45801d8010151980800c0d0055400d606000d03010403040310b59000020301c58a140c0c00010102d01e003000301d4400a00180045600490f81d040403a094500150792070340c0a450342c0311050207120b0049982da40556201c000004c0310519001c9140c0c01801202c003e11412007140e000003913f01c4040011b140124011800e01145051900c108002c403084000075500781400d2600c04c10206984000456202c002c10082d00310300d11031014500c0052001c209126400580071401c903c8540a55001c0070380c240c51030703d0070442502c407041007041a02413502c4030b0ba0f1044000c1401804070585810560f0b1000c284480440c1a54880c4103441c1403940004016098150225600e414241e040006207007284060800350144107021001c00d00f01d104078081c0400b40800400400c1c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 668023111 1250 668021861 668021863
    0x3010c090e04031d1806090604050412030e0304050a0810050a060b0f091807020d0210050613150f090b0301153b01121208010f0603111309060e0f190509 67
    0x318030840085c60520b00e04188000c1c54006082520f5940c06800f1080c0080c200d41012700c1940d0049401c9003040d4a54900716404801801c64000e500e0038900061200160a8503400b22020207041c0003805040c814900f212040c040f60300041003148442e04049007080f40c0d4803501c007100c55012018442d00d0f80da554200c0820684142c00703030f200d00105000010032420981c04186c000003115541d090304e0f41c00344c04410401c01e035001918515401071401640c0c000c00100707680210240d484030007044011a5490003040d03560f0000354040714003182c450f60300f520645001e20403000c2d0201c14241c041d08042c288210028289110140407041c00260b50202c50ba9030fa000245807190f4609103e505019a110802410382110b2582e0448002c518401180311942c001c210050603100300c0c200449409161000c110042c04041c403c60900050810404124200166402019025075280422464503100c410443d44000910f2481040701c08400c1c014250780e026907508404004007408a803513121a0072035 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 668024361 1250 668023111 668023157
    0x2301050f061308010203091002180d210915090803041215091a0a0c02060c0d0612140f12040e100503030a110f030f121012030c0203010c090e0403 64
    0x41039800c00a240000301002c3c150025446100a070041e9400c40f458039000f481680900302002d00300607075012800c98503040c0004803501390760007060345145020040741a0102c2c6020108154001a0303c42030034000e401c1c400700701400c003a141380b510000c1d0502d01200541c403401b0340d014050156042001003000e00130610380c09920f021080d802000300d2081d03450051841044015030351108010308002607498405449240c48280d96500546a01d6640100f9a0050351141158198207503a4202c0420116003840214510790300c07035038200d0844c44090411502d0003183c0441901c00368007060080510044060946044074030041e4142d0b00c64817080c600094a00c09034010b141c25100104101304025031100004000031003640598038441c1000a01940301d20645130010b50808040016400700100c20340410303800014117021888442d25001905038078070400d0811f07000280c80040c0c0b0020b43c41c003032042001c0e20900f82042403005150400303109590800600c05402c4c000801100d040380c540500320 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 668025611 1250 668024361 668024377
    0x201050405030327120604030818010905160b03010b1b0106030b0c0d0f020c030f03040f020619020d020604030e060c0703021f0809060f2403061005042301050f06 71
    0x3542d403101d0000e00c801a2103184140d44413442410b0b0114a45942410440140f90900e1140a0703c2aa40c80c1e48060710144405417000c090341030324101c0140400000c0c4200c0802c2c41c80b807000382c880d20780c1003654500b441d0010f17004230fa00804208010007114020f00226040010003030002c900440c00020300ca401000c03544e0014001e40d60101c10400800804001018007030f100720004c010f880720380100070049000303050992045500812071500425906005036910030712690500011213590b030b012905a820801c21041a20002a520720900c0d405100300b461945140c8002c01c201c1c41d10740c40041c513501c141e0ac65940154000a500c202c8014280b1504e409950060400382101216a4106440c8100540c05000081c0003002248480801041c5640281411a0341e82001d484004e8518034100c02d041d54916492880311101a03152018850780e4480c00011100d030640d507240900740019940302040c00c0400c0040981701c0030351180c058105905550702915a4080c0b50702ca00d0100b0168820f00310 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 668026861 1250 668025611 668025613
    0x607120f270311030f04081902090601120902041103090714010c020904060b0a0b09040c050301030c05060c031908041a070c11040209120703050d050715020319050f090c1516020105040503 82
    0x79003400c2e401710943c0107008683c4418106d4803031070b03c4000c00300900090860000d510420200106403a988030f0b51404580340c2c00800001040c3c81d00b603001400b01c0d1003081e1003004200c1e0200400c19510f20910060008000b11030059804201ca0b0000929664180c000288103a520a011500348010780e0700005d040f60000d0306107003540f42c030b8102004441e0800c0e240588914240151101107520810a4904a0790700c0044c0420441c10801005000e0300200c243d00c032036110502c000c50a09401c40c0c0404c0c07517030000d42c890a055013080c0c1030041c150b034074000d40e4030040203284081c000b206034400c0030b80360020303001808036400e82020700001d0003910501600550001081c801004e4619011072018102ca100300105d5003e55146602511680540c1078090300d500e00100000c1d0a0361400d070020b55200503001c000c0709289a11000b0300080340c2090b1802068040000100320520b0b10400502d40110b000310f880d40840e0489001361525441003c0c1c3c82c40f00040c0d5124104116405601503c014142c020 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 668028111 1250 668026861 668026867
    0xb060a0e090c1204230f120d020903060c1c020702060d0921180806041505060d02041b0806010513030618020306041b12080904050403110607120f27031103 68
    0x10030080c0240454400c0742165051700000c1c65080f03200004c0200c449180140a000307008111111211660480200c0c48103040d001c1022841070341d01406a42e1080440d0500291581d1309407034400d02802016940705526441003109602680c2c407203003503c4030366000c080040b60b941c510f4540303140f442110142d03968440d2000040303100e115821242648141c0c80c5450408080c2d90380e032124964400d42920040e21164031481c13048058105070300125840b000180901140c00001d42c00b14003112903203501c18507444180e84000c0201e175030140101d60010401d01e081401c2591100d400712442519101c018600c036901e005854910304a50700003000560001c0c295002460130b42085192410a945000ca1300d214112010410800014040380001e0b00100454188800300c1c09000c000d00001c3e1040c0c09010000d262000f81032000c03c44288285000d503150f001591580768248140d5040825568441d03080107092102c0300f031440c03070784210a82d52000407204e0440f2400c0035a9452000448008540000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 668029361 1250 668028111 668028113
    0x307080d05070506060a0b0405010804050f06010b12061e06181225030b0115120f020910050705030d0903121b0e041b12020d09050d030b060a0e090c1204 67
    0x20241c80d55030b00910640380c4c40e80e290010041c1688180c094035071100d105010620a0794400c0c80c06952140c82041210b000d1170301030b5245403604c10241c0c0b00d42c02460000685030414844002d131581c101501303444216030620003d81d10200c0e0111a41d0840c080c3d40e01103504039072603150510095021101500c24110b00094291030ad48a0100850703802150f48680360ba0b51948106044260860360496404041a420002011010010003c0340d408000102c3d1010484407003500c10142c91402d42ca0006a907142c00905004203100c1c100e901c8010b0240602c02400410b1000c02141c9416104800c00114880c0520f420340369000c0000294080070324100c60f00407100090000c44081401c1030716115506118041001305450901241d810680075a8203c1d842da1401287c84c50511042401e000d800e04090081104c2200c0140d4002e582e079502c00c03134621203500c2d0580300d049603011054688524000041d076026000c042c00c01c0f29a40a486800c0014121154141c107842e101c4c40d0f007030180c001038105 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 668030611 1250 668029361 668029367
    0x40c090216060e01091703011509060203160204111603030b010c0c03020906031e010603060b040209011e02070801020d1406100c0f0804030f0305030a1409071815080d030b01050f180307080d 83
    0xc24009d00080d40000100d88032464022181041101c3e82d50307000710320780500301500c205d4200d5010350890700941c6543c0c15039540510b001c05071010900002e0408584080f5040c020140c4242ea071015041c13150078000d05020071078038404030b81500e405441155a649a0310042440c01e040045002490810b0242c18200254107410400032240039240901590f5064001c01c001c0744a4130042901040c003035807803e1081c0300281e60240111ba094016688034030740c0c4042d902d080ea0301260000d1003c0d5034541d9151400c00c2d05400060300220103564400020003009000b8040403034402c00079003030303030003007604001006182c0c4200d4000d1588a0b51803206001a0300d00a4260b4009441c4c440c1d1407424032058100300311903080c690344540c034840b00503d059890701c122503010011082d094031400f03844409000843e10200201c10003080d02100074135004400d614010100c90078200002d041003003c02014070301d00e501c0000c1d0b681d1030b1644082c4020700500c00002070b25000690340214014041d20b8040d040c4650 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 668031861 1250 668030611 668030617
    0x30507030309060e0117060d0b0c0702090f0402063c210603100b042c150411040b010c050d0e01030e0708070303181706040c090216060e010917 63
    0x1c400e0b2980c441240c2c0310001504c046409402c0d43c0e0001d0b140c4003610450200c110756180d0818006010214030304c4264880301c095a0084a010420b020300048000031428412203080d070200e507a084506250410b0790001c1c845104091010b0310b5492800e01055040e81fa400d00318002d60320f040820000c0e1030b202c0c1380c1081160012004803800754078012030880c4042c0c55005080c46250024041c1c121840380b0403c0340c004015281d10717160441e5990009004a200d0306801a07054500203200b00000c0761160344039441c103403150b060000c1c482480c1c2c062000040b00501d2081200320116400b14810b2500c42c01260318000301e00001d410740c4901000700c2e0006d600005040000d40081e601488100447d21840d60780e410144600101c0c0c4c0d000c0c3c501000824894034000541d05c10344101c80da152681c594200760041c0030324500340c01540200c0144410054211400d400400e842d100035401c11518141c5006646407401c13000e820382d510f598070b8150850017035028a20135a440440111a2003480004a40ea50 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 668033111 1250 668031861 668031863
    0x90f0315010f030605070507030c020603100b0705010e0c030a0b060405041712060411070803010308030705070b0408040518012301090b0d1a03120301091a0907020f0d082a0d0603050703 81
    0x1e21705008030311110b12600c100c949242e01600c9a220000c81642880000d9200401d1007401698614000c00c2c4800d46038006c0c1180b0b800f4030700115819101c151900d081524111016210342e100d890b032440007410001c0f41680c4008100d03000541d580d95030030200da01c001d854070002c03815000041d40200e1405088502801500151010044129041020102c0b403140c0940a000110b060004000050300703100110307031080907880d086061003040c1d42c1e8100d0694080e070f02200c001002180c140420b05000361500010b01a03664250003c1d450039403074440002400100180012a581c1d8852599010380b81100040281c5035945a41c0c02d00d1180c0c00c00140700d04060400e44003140050703403100f031a00041079080c0000f038040d1a861640b030310b20040d001303240c502402c80b41103162144542843d0f465a1802c0c2c8240701540103020642c01c100b48040c140910743c0c0d61307070341884109414048481c852080c141d503820101380c4410625040d1007512800b80c003071010203521081c1403a00220400c840401c00400322 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 668034361 1250 668033111 668033123
    0x22415061207020d0f17130804030c08100b0f090a0e030d14090f12031503010c0305070e0328030905030109050d0f050436050a02040518010506090f0315010f03 70
    0x3011010800f107403901800040100040d190303240383d40c510040c50440f607070001f01c0c114034201c0c0014540d480c1c1c0c005410580c02690300035510442003082c00d0003400103001ca02c00e901810480c8144100c00140c000140c08030041c0503108400c0010b180b0b0810358000e203500d01c07000c012a91184c0720844070780080d002243c06a00100300380c01c045084400002290702c11820301070060104441c0361040c103445500700805c8150b01580314803460034192800e00c0b412040218a80e0b01180034904900c0250046d902c0940d500e0103503010300c0d217200191584110008080e214140b2140c0e48607200e0508031503a00541d04015410351800d03014000700322000581c541614245d4a41d007a5440c0705101c181d8803401140700300054281d140408000d042c1110110b482c0b003000c81904d0816039221100d088049902c00c84414890302d500040c02d0015191688426a1360303990245d616801c1d6050202060b41806150040c500a03542e00c20981d01e581e41c02c0c01130348080c00720f03207400d40b459681d030b56400300080c0701b80d110503111 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 668035611 1250 668034361 668034373
    0xb031b061e1c0209060409110f04030506060a17060a0221130209070203030f07262e062001090819030b0103050903190207050a0906050306060102241506120702 70
    0x2080d220750084d502280d500178a09401d01c1d1500c8510f0f80544103440c100740c0022000c101617084611341d000a000614020300051031140f418809008080c42c00c2d402400f01c82030403100541407038000151082e40b1003480c3d807025071103c465800c14100c80342a205a803030401d004008000885200801c144e80003402100c8601490f1580070050381c5900c015107451841e0149100068042800740c805008080d030454002d5031044c00b18000d4004a007420381c0c0301d0181c40602608800d400050821295000c3d6000b11903801c03461402901921030108905001078a509051034002c40f08001e50005912503008044141d545002c0e89002c0140707c04142070380c0100c0d103812410400e9511034402c0b00d100d10300c8140103626019050002e44125803090144008502c1307040404074107910341c98030b801c0040c2a401c001155007801c080803d030411400800b11411035010310000800104c3d900c504030301d20885c09042108a8403040c1100080c0500c0b850f200d03070001c00004045102c80072542c440c41c488c1344544e00303a0340 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 668036861 1250 668035611 668035657
    0x140309120102090f0910060309080d0c0e010206010b0c07061103040306091a01120b0117010e1209090c0f042120131a300105070906030b031b061e 64
    0x3c4403520640b100e9481ba03032050014400e4600961040c0d0400c2c3c0640001e90501c052450000180e0b51646858000142c0c500c40000441d6010480b050250907a1004d15080140c0904241d541e00310500c512070070011008681c0e0003e0509104550103150000300520801c816070074a00c0a00d1002d401083c80403030040000290704405010300c00c1090f40c4001491086d0346441e800d0303030b14154a088000c0326950b80e80e0345070743c0310f00d01041011903509920041e40d84500c0448104402c0b01c00061080901c800b0400541e140300300561f040b9000d441383d07102c1504180401d080c40c10041d40c14900000c0c03254882d00081110ba084107100d04c129450201c4040e01100c201121340801d84030380c0741f0780844880c3e000805c80014501030350440e0b018038031910b109945824100f050004450710b1814446641d54074000c1c0246594450440340203040542802d12512440001182d1f80704020b1500b071203c0c100c4600721520300d540f0281258610320740d08013008a00c44100300000250f51060049145036010310311114 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 668038111 1250 668036861 668036869
    0x60207030302220812280801060e03010e0d1b08130f080309010906140c0307150c0f0c030302031e240d08071106281b0b04140309120102090f 62
    0x40152152000648681e030404c80030f2040b1500159040311004d081c1290b06082440051b06010341c05050b0f68840d006940352190242201200400da030703000c1d0341003012005810303000080103199002c039450514000c10181c1e291945601030f005000705100750010b00051046494a0080240c0358010301200a4030b070b0b640011981c9110b51074100d070200305603020801180f8050041c0145607142e89d40e00a10301000710b85928210391000c2001c5030384403803d15108801002a21500f140206c043c100742c01a084d14000c064840070040070020308140d000030000301083c043e00712144440814800099090606101e0041e142142500d100d034014038540e0007800320310f07200101000140d00300c1a0b4900c0c0c0406a120760a40b14800b4800fa07030407441c100107d0816805004620001141c02c0c0c130760b610500c80515006150f02041e100c031000300b650b11807040012a004040c01d0341c100d9400404164060864000c040c1503000703901c41c180d0711852a200764085101e040d001440304007400c0b241000e00715107540c200 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 668039361 1250 668038111 668038177
    0xd12090603021c050c0f0a02100b040c051c0f0e0d140306280e0f0103120e2d0a0602160906060c1b090f020711030f1902010c060207030302 61
    0x3c000c030b030f401203600a40780d40d40340c1d404a07411a809940c0c0a24052991503102c5060344984001e100603070200485407040c0d07030140309141201e1801c44041c00301030000003008250380034151514078040c0500b21141c800c144140c0c4101e5200300501410b0145030710050703180b03454240e180310701c0010841181400e0390701d13403e443c102e07803266030000e142c00c1080d50301d0400041038100d586010990f01006810105c0c0b07144207014810301c05c1901440d40b504542c11072030550b034209804161902401442d1280c6c01c4640e440c03d1100e40c658140e4030781004104044942c01000c80101030b034003034006a00e2180800c00c9540460384050458400c000595600d548180c50821110f0700c0c41501d00050103490400c001524040d0540c0320030b103030103020601c05510f40c41c3c5103080381c0114501500700ea0740000c24808006c691600b410350007030308501800803003013640c8603140c1300d0250030340168090034011401c50840e806170f0a49045280c00c08030444d00d600b11441d01400079480407280307014190713002a684600e01050360384 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 668040611 1250 668039361 668039377
    0xd2a210303230c0a02030d060b0406140901050904020f130608090f1b01081f0609030308070305061302030c0705030f031f030804260a05060613230a0b0d1209060302 72
    0x50302d8856407000030700d10301500300310210821400100300a00382034105c0d0044134050816080c005940c1d514100c0c0280c000c00707460684c84a190300a00580540740c0c0c002c0252080c200e4140d81c0036903624450a4004494410a1054500d000c0407400c003241e00313907004180700c0c807801102085031480d0a00003e400c2c0d4841d400e6610b0002801c0407500504554070030100260805551041074420f40002c82c0b1055400c2c02c207812102c0010040300d810000c1c03607489040e060700718200d401c0810a0381002c5020420f40340c514081e61040c0e58000000c9288002070f1303021200c402d81c0010070307071380ca0f0491090030788003071781c002c0e524030000380d1054540c1820000a1607811084a5004440c1413402c2d15050388601045000b2202e80000b661840810700c0648060040400c03440c4900080c0489113050802c2151481e4040350303104809107412040a00c249560395014011180394071041030b19550003160f18054104103c0c51030b0042c000721502c40030000c2c07c01d2103058115043d19803c80d40b0b61100f0088080b4042c00311 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 668041861 1250 668040611 668040671
    0x5040e030412060c090510020d03050c09031b0f0a090501090606080702030304030e04062c0f370212010f050f0a050d030c0602190306050d2a210303 65
    0x20b14100015019800f4039030001c000c0c28000e028559600010309079040030340d51100940c102020390584944d041c400c00e03170f01442d503030130b102e003403c00d540e01203540c462035840e2444e03100142000b207844580d5803080201200100500120304182c0350f0002ca40a45402e205200905050441c082046030007060414410742c5507500850440c0e9541c0c0302100c8110072204040c0e0400d56807840410a260000d011000d8084013030050010541e1350402002242c030300030459000036501c81c050198514181484150b204561040105c030b2600280c2040c142921804017489814030004100744411090f00c2103904940a80c190360182c50341d9423060107040c02c034038800154850220702090045180100103040d01502a1510f0200c40410380d49040c101d901080702c05e4030101c0540051719140fa4540520b0002d040103940500b481c2225540e840340c5016020f81070f1040001e0b4150003a40708180210f440300800c13460710081b40c001d000c1442c005035034207800b0003a0002800c00b101807a102c0c100c4ac64141c030440600b2 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 668043111 1250 668041861 668041889
    0xc06091b081c08280504060915050405060109090c0b0304051608010506060301051003020909090309190302060a030b0d0c1e0b180f06070822080d0203120601120e010605040e0304 78
    0x20040c2c04485200007002c1c001c1040035072050703204134528880c60344078900c2244005040a03007418400c8a1041c0140c814810a09002c1000002540890020704686003e070300814500c8041c07410389000001034000008a00e804410041070140c00600c1800003503150307007141900d54652843c81d0903958101c03440741d0040c01c2000108140e04140c00f54100d000c4140c0f50050500b120b4000051502d141500c8405165001141c03541e0705290650340c0c041d07106a0b2107542280585150b022461070b01425182109150b5a0040c14003d40c0b103800d681c0380700b540d0005208001c20340b03a40c900c00da03c1141c485400003102c0640c0d00070494035440412107101900e00f0b010110300810311800c1203803901d0030a900b00e401c03000520040001810801c0940600c000301070b5852040f001e001428880307403030140c0c414511030384100080c10000b50084201e406401c0c500c200300b0500e0350342c18010b0b9515460b083c84c101486d807401c0f040d1903030600194890019140d08aa05100e402800102c5a959003d280a5031026604070 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 668044361 1250 668043111 668043121
    0x10e010b091e060d0b13091e1a0f01030b130f0f0611070f05011107030f03050c120c0307020c0a14010c150e071401080709060c06091b081c08 62
    0x241002c03140e05400d08641210041444011900300d4002d40c08250200c1d8440784501c05a00c1d0550178000400c034410020070401005844d10044003001c40100011003900c02d0500301401510350001c04030f07028051071450342d0b003003815201071031440c2444146c07081c04826002ca0580400e201b401000305811034041d04c511005a2660107040c40301800c2200e215940f8154004c024a1031809050350a001c1c0a0200224410341800c9081d54a03141000207400000c100390310010740c200c81c4401880c01145400900c590310100504041c1c0f20340300c1052004080341040022004000000710311916103642500c108500040c1400070400f40c9004a00708981425043c0c2500d51040740282c04960003031942e030350071906007410329040300e200d01c6248929400007542446440404190a25542d03020300e80045140b411300c0d4000c0c68248d5a0040000304007400c02c41409020b0282c100819181d0010009204d40002d2240c90358041141c0c0318400c1c6c54090040d030211012000c0302080040c0da500c0d1202e00f45e42c6e80f1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 668045611 1250 668044361 668044369
    0xd0507030f09081f0e0c0a0e100902030c0405030c0f030d05160f050c2b02060c100c090614180907120203010f0905090604031403070203250b010e010b09 67
    0x501254000c114000c180003c40d2141086040640390440da8416544040382d50302200381c4e4050007002d00541c0c070030f505500c05510f0380d040c001d0803903550320002307409a1103041001d0308181c029440708880700d0010041c04140060000200220751089003200c00300c6114100348100c0c0c086505403180d040d0401b030030389800c0314040c0008040c0300000e00c04a58108a855a4004c1d4195803510259226801001c1d20b58090414894944184c0b071218100c1d40c900089284401080ea51180024000c1c1c1d408644070300602c0d410000d14040001540090103004007120703006060581c2403081c480084e02e1080810b941071418012140d141c0351030701c185041603140500380010144064803d0041145001c50350108281c0ca101a6010304058282c2608192400c0c00100943c2c201410003000b64001c06c0501c00040d410030201510080103000b84c40e100d940e9504281d045028522031140d40141180780c41900146160081c08402c0c821260440640d0b283e403012002a070090082c00e2495100700400181c030b00e8 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 668046861 1250 668045611 668045627
    0xf13050a031b05060117010c110c0d0c27061703070f0c1a0c010c090b0a080c0d092301020403030c0b060402040902040e07170c1b030409180b0105030d050703 69
    0x80d4002e0b0004007000d940301440d1000036031004045900301c0d62942150341c2c0a00500c5200181c034940000030052003003485071207200d0080328a1082000030b08103010094510541030050021610180d541441868083c43c0e80318442c00c01941d1a1400718003061100c1856102400d01036008000c40c03c041c0f25548104804460346030540c0c43c2d602200f0300113800c407a0b2016410340480350800325511503821105481c00c0d5544407510358203104d9114018080c036650201650080c0d40303d807603d03c907180c0390313034550302c0d214812810f4002148d4100241d60f014425600030001504500e43e2080800d54a100b0403039080740190f010060004034404004004192600300c25030b04140d004100500d0140d1310711390681240d21662060b14800380303440030080007580000c080e0340fa50319410015009490203020041d424801e15109600702c4001d4003400030841010001d40c0c000c0c0c007585108120783d00d02aa50342c4094240100121103060401c0000f01c0e0343e0a0200b03a0098840068441c0c508006282c0e03001e8074211 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 668048111 1250 668046861 668046887
    0x506040b0a084609050a05060f0105130b0409020303040f03176303011506050f0912150a0603030207090b1807180e060901090c02030d060603050f13050a03 68
    0x35000310f0202da106070711840b61440da0b500c2440140002c4025244c404e041400040c0803030304070000c0c08010085611503032500c0240e80b07482c80f0001230464242000800a12407418080d416103c0880c0c089800e4900d03126210070b0724021400307001c00c0c1541405000f09440751a4803041001d8503865121170b01994001c2c4851050200c440c1c200303d594100c1244c03000503080c844521503451070345c501000800ca030621850140c0c41c080e0b0090103414803204030541141442c0c0f00c0e2004101c0e00090304980301464200b59a07070000c00400702101400c494410990310403995400c0d9240d0120a130214000030308611a200490f41d040d0082e1020f039191820300c0000700f040c1103099801803050b00b0310840407540c42c10319910440e203e40301e84206400010311842d4807001500a124a8043d003024418140c1d00c962045046500006020644c1d16001da022411800741c030030700c110086c0c103009001c10042d406821847c030802100c02c2e41b2100750703503584a001070454407032400752258100500c00004070b8480c45461041c6 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 668049361 1250 668048111 668048221
    0x703111509010906061202031507050409090507050102070b040e040f14010c030f0f020408070b09030a0c06080a0f0b060703031a0d080304021918150506040b0a08 71
    0x111100028100326110032114580c0595540e905901040300c3e82c800c1034050207030811500c1800c0860341c0420390b22505070400032042000700340003840c610301c00c0c41210041c248030b80301403007440c0651a1080d91500680540303405402607080124601080c54251002c6510a00c2c900780e19450300d480780421464007260a8036560001e0581619609003405511032507800342d9000103004440c0f220160072101d08203e021311060040104020700e0b100001e1640a6810314512a9582d07190700e800280340c450030342e030010400741a50b80001150358200b4003003489004801d0b82401002d001840310400c443c03100d2a0b080d4403034814444900860700c00c0d40301c80c1d4030311056030303108100310b50010000c4c1c1e01c0c805414086030300d43d000008000440c148100d0390128603440d5520070038101c0c03c126405844400b840c0a820810b90743d28440b0401c034480b641c007040140b0018142682c1c2d80e84440a0741c000f070740442d610001103180603011641c0c20582c4401e0341ca03034171007483c13070748444d054504200382009418814002c08 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 668050611 1250 668049361 668049373
    0x60c0d061a03060f040605060a083411010c0f0806040b3a030c02060f0403060912020f150127110c0f03030c03040201030905010e0a0506010f080f03070311 68
    0x42101c0140c1180505080340040d80d12440d02030100040c41c207980c1840750145007080e50800071034481c50266001341c031003070900d20070a50310030419040e15000d68800380302e02c842c2070101001e26404403500704803076601995800719010040c40180e081e02c4005c4480c20020b8003512410b01401e12071003031540c00040050010961480e030764000390340c1025050940100c0148100120340648072804004441000400704038407000352a28040c01d40001c204010780516000111908042200e8080b90f000c1c0da0b201000300031618490421401c2c40e10b0451a81d00503110301445800907407400104600906080d8032a0411a030810450401e40480c810030303010046400101d4250710303d05401011034206542d50f0315501c0d00d40300407195181c1801c0c3c8141c041d5541040040c0200e1134022012640e0054086c07d002c00e00c2100340c9041801404104804449402030303850348000c01002280d21412580d0901c4465001c030f896090542d2100c0c0e601c0c07400301c0c05503c00c01c40a00044e00420440703807080000c1080d900 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 668051861 1250 668050611 668050619
    0x6050402030c040f051005030a0b1b0d111b150601050c16090203060f0a1802131203020f06090705030604151806090c0b040e06300a0b0105030f060c0d06 67
    0x400c0c0c070f1001e1300e6030100c580c03600304009401c080702014030700410045004003d841541c2c0c0700d40ca070020b0046d2124010705021400c664040a0a10440d003420781015000c1150401078a00341c10250011011100c907210b60711701e440c00c1034000207100c513002c030014840e01c020380c2c5622005603110741c03000300b4841850140c0b40d00319048141140d1808024407d440c4003603520700e000310402c001e100ea4a04e80034800d9406020a1180e028003080301a4045580c3e640140c3d101d41c0c1c9030088090595982c000d2145004a41c00700042540c0070545442e41d00d03411040320450307124086010388a101038000d9681680c841c800150211b05e440d0f00304900d000c01d025002544a0384544040081c00e0b000c4416501c098841d031001e000c0210942442000341152220301e401c1030300b0501c14a1145002501c40c0c2e101c2c074003030343e040384030003105002e8082810500d040d28400c4010720010b080c0c03500c525030420f642000401000003418107012413a04d007406800d401034401d40c3c0e11a5090341d440d800042e402410309940d248081 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 668053111 1250 668051861 668051869
    0x809010c05340605030f182e0608030405130f0f050f090601091103070302181309260f220f0305060a0902031c05130f0e16090306050402030c 62
    0x1950b2072918100181c1012164580c07400b0b80300540c0164200309042081181c50401c0318034181e040b60654002e207000d410600503a6241000042000700f250540d20710b0110031010454109599248800d401e00842d641c0c0c07140c140c0c0b40c3c041c40c4181600603100c0e40c02411820450740c402c1d800181c0e11240080d060030315100900440f102211000b14200b42c0505025908ac41006858010709280400340210055046d103509a0f0201411000c1459008503d004110762112101031000c4005048201d100c100707440200060103191200b650402c030b0020550710005e01e2419002c078206110b400f260324000721052400e101c0c2c1e110344181c211581c2c1c8040a041b069004440c804002d101a450380304480e425030401c181020070107405420304624080312000103071004241030101c0c604040384240b21104040080c1e40740e10900b24503070490000090040394481c0c12441541c1520340841a112480e034610011203a440d850388800000b151181a003000000d6607a04000d42c40f038400360660781c000c00b00758045 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 668054361 1250 668053111 668053153
    0xe010302130b13170109051506040207050607031b0503010803040e0907030f0b0a0f0506030a122a0606060206040c03061107050a0b04030f0f05030109020c0c03030f03070e010801030809010c05 84
    0x10090000b9007020070001c0d4040740c04c0b4909001d6511000b04103031501960380700e5890404628060035424400d000504503036459065481090308013040d40c2e051714080100800078500a8540d403441c0c90b0803540d4003881c034480ca0680381a0703403084004518003810102000c4515100920000b118880c4540200006050400031a4002c0c890a8000010300780082044143e603c080c9044000790701e080200051650300180082481e80c10030316050880281c201c0c1101c0c1150600001020300045a54802c00c020b405c1c80c3d410b100b00d0244104110316505c45008076140c250a41d0090000304424006001080c0c050740403a0200700c0340e0415604c0c02d40e20340d031601d0070555102c8040e01c104a1000800c0249038200001083e0081c05140c8500b0700c400c2040c020f082404103010b0f8a0f0507a03800714180c45601005c00100d95081e0004089030344842d00075401d481983e1007241c0c4040080c2640441e0711040d40a90b4549068a81c88591a4101892240112140c0c89c01c0c00d010b40c4c45110f442e00e6600450500851 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 668055611 1250 668054361 668054377
    0x10509130210081b0a0e01081f030b040b090d090320040c0509090f0105062502061303030f05042d030209090c0f0d0203070509090a0204020a030c0e01020c010e010302130b 75
    0x40e55028900500f00800c2488005000d0303131070711410003100e800c450f03000c1c901c03410b542d4003400c20210780d071070300d1500303401001140c45c0324111404050000710510500140f403500c910311569125100341e07100c641468071103100c8484140419410744051001451076000c4070500c0100100f510100d4032840d000400b80c0d00900c0340300022950024481c08241403520001e50b1241312a038030348640303500d0840450383c1841010307094101140d0070b4490074510320054200c001b11640091000b5201c4401c2c00c45100d100f43e807880f089001c40e54090703242d03900c0c038062020794081b50b0081e44c1052409860003000d14070004050b2500d6004045084d000c00145c2d81c5100907409250048002c0c094844214103021500f01d80c02c48080c4100e002240c100010f9030000781400a49a0a130b90700e0180782c03541c003070941c54103a0440c0000d40c054008103400ca070b8154503070310102d179140d2075507201038021160380016629000701003207407400a2010341c20032a080d400b1750002c00c01811201400c454881d540e40010469401501f0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 668056861 1250 668055611 668055617
    0x711070609080f15060d0633090c0c20030d030f06080102030c07140f0f0309010e06030f0127020408030409110c0607030b1503040b061017010509130210 67
    0x5024003000000304032066520800e02c004103035a1101131006007200714010412032250180d048000100101030700300203c1105003041e07050407405100d5803a540c3c02c0c54192590803100e400d050000c1c80c0d00040c05040c1c0000402c0c0c541c1d032643c508513151522002d10340d00c81c2c04005130024a140003c0c2d241004500303e03000b690759001441140d00082c01e003c1d80c140e54070040c1035a0052090044001545045070241580400824140101803040c2810144d1018511340140a0400d005001440c01b000402641c0c000741d0322005900c005008000b103d00080d611103000310710540c0107200c0070040c1100d62041c0718003960714000c0d8000240340001aa400b913084a00701d078002080400a448450280502c12001d4030803186c02c1259031070f1b07c0c0b5524100100007800301074540c41c2100b9592600808051038020744008199645801d080801d03d001084d40c950b80a414020b8220120902c9000c41820100300d008c0304040d641d1800041004022000d8800c500000341000500c0060b921410a00781e201d01c1c0f51 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 668058111 1250 668056861 668056877
    0xf0b04051c032a020a0c0e0f0609070512040606050a0305070305070b03010602030a03020304020402090915010f1e0e1203071202071a03060607140d051803070f0e07110706 75
    0x81001e0340481e40c0c4103000c805260510032010298407015074400c0501648407403000c80c4142e4084124a0204042809080c81100036400300d0120510100c5510a18583c0b004050717644804040c40401d880498968001400920a03174031031207203130010640c0080c002c0700040752960703e17400001c04140c1158812540c1c0e5211250410402034207011042c020b26401141d00c0c00c640c500707000a5280c2c880c07401000c0405500100103811075031664151070710000080c0c80c501062400100c13003510910101f54003800705020401400f945131152580c03082442070030114800e4595054030540380140034540c1c3c540e001d1503030490b101041c841040a002e059010740081108000302140c040d08020341034000c00038902c004200c07a05504202000c40350054000c0d18415524002c0d800d00c0e0318601c040c08411078990043d040500300955002018100d03464010400701c8600c1580e07010035075142813070300c158002408069810480800d1704010b6507803201e4541003140c2201070a0190070b013441000d42081000c90084 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 668059361 1250 668058111 668058133
    0x1e06051602030d0314090d050306060d0e0703080406020f0109030e101101180b09060105030601030b1312080910060302100c05030c01150609150e061305091501030b0d0305070f0f0b0405 81
    0x641c580394006e1001c0026059550501000a100d407000400190140c20001002d10f101e071031a43c4419070366005501a01d4002d5242c2c901302c01c1a51042c41008018403604c0c6128030b100c0018816002081d9158540d5064440001d050201010b09000050705000d07268a0181c032119081c0510009802c010340100c002c540c0c0c0c0e14003440c540343d01800254042d404000140041c5d1800201241500e420814490056480b511108225524254024882c0540d011890001070300504007a000780c05d403000760703560b13444c0a0411a08442582c4400303540501800c600d030350014000e0100d40001070041b4140c80c60039072080001420350701c26811042c8407045032001080300c40d0380550001301500c8502c0c90f469000c1d01903480180414140a40940b1032140082d042c129010340c044603500800f0003030980c2c0709614010080c03007000c16008400c58003003800c10b40405010318013091040d61240e03050304c03440d041c020b03240c0b50b04296500710a81160308a101401010100b410100100d1007144a9802002d5090306 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 668060611 1250 668059361 668059391
    0x1118040606150804080a051303050a1505090316080901180e07030b060a0e0118080f030d0f090203190201030f020d0207111914030a0b07181e06051602030d03 69
    0x7141140da42000300480a104c0065107110071503052201c3d43c078040e501c401009500c82c1c1341c01c555070b00080c2140300f40c1080200300304000381803400100c09542d0170450740e07940018031a128491100341c9080f000c014000d170400100c400d405042e07100700601d01410200780640001084003585e0b0007201e02c0c0020079041003c40c80c2c0c1801082003584058440c5400c203c20f81c2c501500140c00314280d07a040c002454285007a00710020b040000520f0080112040055004041d580b0b1313038080c0300150410380c00c100c04d640b1001c442e405440c0c1140d501400400e100c0700724800381c6101550945003241055100d035500c490954550020380b01980c0c52902c01691202c00d46001180c8070305031203206018040a01900421030322641c0c260003140d1280e40c4403590503001780006801c08840440007032501c2250f009220704150700804038681c40d0b040003a4041582c1c0c81c3c001020303401e420f0384000d900c8855080d000740b020611a1000d010102016403c042d0000001d40c00242442455507007440002d540707084040580403 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 668061861 1250 668060611 668060639
    0x8010507171f05090a1103070302040801201b030c01020a030506010f14091e0d05010501050a0e0c030604020f070506040506071701030803182406100315031118040606 73
    0x1e84002d00c1809020000408103841e4442c0c1445076610100040141403182c12040328506881c0300c61f6540d107041d0364054001d41060007804059860440b0440b17099840e400c4403090388a0035102c040c14203c1c4e445142828035054181c440c281c0c00103224002d24501d09001a211480017510041028030f020f1000410707880100c0458010401310010400000704090200c07248041d0a803240051130189100802c016101d040ca01500031300500070352428420306503c10b9040e00c10403164504801e503141905c13800040203596140c0400810404640f140ca45540201481c40d00b40030458103084c00750300e40301d0606100303c40a0300c07241c02c070302e081010107030b44405140d00c41543d8244c4e0610550540d10303403007800d010050100c46007503117207078400009c868200603459440016a07080ca0100041d10407443c0100c0c02075601c036024010500d56005628024000d40c4044092500f42202c8280f80d611007000b80e4610542c072581240410320300c0c0290030000c03641e891149000c0c2001042051401d1001c4803980 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 668063111 1250 668061861 668061871
    0xf0106150e010f0f0201020f070605010f0512030405010807140a170901150b0304080c120702030c0d020117190c02030912030307081306060f08061005030609070306150801050717 78
    0x20310020580c9241c3e003002c10300303207815000d2030711020f02501920164020701c5840c0f0200d0751104042094420405aa00400d058cc0d1440d621007081c555607401b8426140340074402d419168005102c2480154412007910b50311003040d18041c5035542101c45015400e07402145881d00091692180b0455446051483e40d04840440000c2082c082c01c8510480c641115006448513172100201040c18080c0140a581903003200c0c005440300141c4203064180325a2108008a0080c05000d11008461812803102500d0b42c1d010b84a1821303250102d452041c400d4802005502a0b00e02d503000b206602d03401d0f1060b903116040c950015652540744504110200b024000d0f1651079038001c100700f01c002c1e81c0c4541d0301504800607601c45844d5481500d03100e4017510b40c6030805180d01e00311040004400c1c0001a890340603241000d8890388241c0c585091540701c080c22102c0d043c5d150b12690080002920360b80c04620140c1004007502c00b0705460721401030a4032805d941050004142c4196880403010401c2e0b080c0e000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 668064361 1250 668063111 668063117
    0x1513030f0501050601141e18060a0c1a0f060d1502040828032106081c030f0603080405060702010201140c0a081e16030b0d081309020f07020d020307080f010615 70
    0x880f1000784c850740c0e00315030081e09047e200d5010403a0b40d01c0f0a0300305014502c0120051480340c07034034400c03d401000c600c0301e42d41c141e0f1180f500e400302c40940d5000494582c051b00d0301c044101415030712042803100148010b64125401c542200c81d1a80c45c1c0b01503c0070b40080c041d4180900101040302d905001900115040a4080f045c00843c1100094012142d590034023a0300200c11404041c03040c480b0000c0c0346035440309420740501103007440c0603520340504241403d410b84082003050410000d8004981007404020007081e010442130129241c0880a4040c0c11304c1480045000001c45207512072440b03082d00d40d00c00006000c10200c000ea900708240303992080b40f0500c92400180e8400c0303811540b280140c60721440401c0d941b00402554865007006000c0f64003c1e0110554540030705c0d2030320a5511180c9941420500610081880d14a90003269100c0460113281410180c039a000c11861024010040764107120740e080010b4030001c18444201030b0410280001007075441d106950350b40c0222034032030702c0c10 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 668065611 1250 668064361 668064367
    0x4180f05061e0f071107031a06130b01120f0b18010608070f020615010903080c0601061d0f0618100215010e010501020604030f020c04022208010b1513030f050105060114 74
    0x50850800d103c50b404806031070604902100b03080c00381e0600c1d40031341000c0c0001d84c100c0ca18502500024041500400c8245d4072101500d941000030005c9602e030a16190010304151400000908250072150704142da404000494450038800298050030300d0001702d0201c1c40300c0c001007262640014100354405101d090203102c2d14a2008002c0d20b07003800904d0f00500600061003094103911461404015640c408101c41c0e40303005030381d5210307580e00e003d220344000107402d1001c0d00000e500c81e950112200e1409050820020304a004022107504000781c0c8042d22030010303500142d140c1c3c45414980e481c00003074010345441403e964003a07065001c140c02618a00080740010000360360700041455001346c042c5040016000c0011040381010f01207190f042d440740c0086808041da0304401c510416105002d4a1040762569a041c11403c8e202c600a03030550003084078040c1f644030482603004100103040c551003d0025500c0350740b0180450100f0390103070b405a6442e8100035042d600040602904044401510300f = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 668066861 1250 668065611 668065621
    0x6040213060e0a020a031107060e0f030c07061b1a010f080109080f07300923060f04090f09060e0606130c1103070b04050610060504030204180f05061e 66
    0x44007000d40f240e41c0300c40c2c0c001443c5030707418131039440214400e00402c5c000341d07503a105041c2035005d00981ea0703180080b401006807580364240c0c000300f01c40808021354050003074586456000d40e1503e400ba600b810000000c06d2494001804100f141089880c164400e0011541401034140000507260001200c5030b141c0a0500d000c104402c0a4413101068100305690340c5501e4a8114600400a402e0301141541814452900c40a0740d40d0102c500e103032070b82ca051002e03035920244409501d480342d01c0c800400310140c0140c01401e207000141145428030140e14502a543c41054003102c0705456150601d48d80c0d40c0c4028208440c41c0102d1501c40c180000404003814004000780300c0c4040d000910744403982c0e801c1500c6070240580c450700004514401075980314495070404494032803045030304a401c0d026020011f03164807803078207543c0c080d200340d59107040c1820f0941d404e110042001021000c0d41c10700d2813603a00d000483c1c044428500911a01c0506014141030000c40c0c0342203049a400107a00c0030403402c120b = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 668068111 1250 668066861 668066879
    0x20610081225060614011106011d0402310b0303070210050d0f0501120c0f1508071202071208060a050d1b17031206010512040b0702010f0e0604021306 66
    0x1901d41c54203400b52010b480c0312440b4010040104000080c4000d0601100095000304060f0a461001d000e0b202da55115200103030703454589409002c1c1320803100300c0c001180a000c100d02d900701c1d0300c288064411359051050004040d410942c420080103035409c240b5402c90000b08501980300c86010940082d400d081499000940b00030b12254400d041042c04512070a0000139034210301140d111000d420130803540c4901c01aa012100c1000a40b242900264001072104040010008607510054598424000c58500b242c09030405400f0004001212031030054603115480286612445800d0641c00300039400e1000d40509002814580704081c1300e072040203207031140c6551034000703948100842d6152055221080c0ba0704403d4101c015094813962141481c04000001814a44910000c106840d45d0b1540116100e106540309103030400c120402180c0000c041c50080e40d00708400d400081030310040c0c000620120703890702c5162640d030361102c0c0a02c030550418804403080140303940c0cec0038445036041203115 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 668069361 1250 668068111 668068117
    0x70503042309071d0a12110411030702060a0b060403141c09060903080c010f1103010911090f01080723070c0503010504081b101a0f04270809100206100812 68
    0x20100a014200d0502043d90380303017081030180030442e241c2d002001160034040000074080003401c0c0128a000c9940c0c54a500c281c080d28881c10381603000300540e56488036060041c1ca20204865000030042c4008000108030480355050b1074018001002007951412000042e1000c001189042c00f20b07144d41800510360100501c4140ca42160710b0743d984981c1c0f602a2030040105405d44000c0034a0b04c0d40b100914610100118101c50400030309214800350049090001e1052404542d030180046c062143c0710350003808800e6001c00107042280c10614011040012000d902c0817490480400091b2a0100454080d4010107484240c008000515040e0781d4200540700e00649815034043c43d03207030340c200c0c4602000030305019005c00c6000d21200903150300020401d1200384030745114806949424500b07040602c100215200000c051505000700c01d45454031600540101b510f990750b0030410011103894440b600102224558000c01c003a01d40114520b004082031b40181c9100d801200720034800da9251400c3d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 668070611 1250 668069361 668069387
    0x21b10110a06050705040602070f1d04060f061502160b030403200f01060e06030307020d0204020a020f03130306050907030c061805030d08160507020a17010207050304230907 76
    0x61644514401009180541e50140242080e0a2004100d00164003401800482d68140c007281c0c1c116807100080420700410380140c6d0291409507540b803203841c0c0c0256206d030700280075040000c1c1440007003d0080944240d034004d181003500d4281c107405031550410090266140d501c00304d10b11103003000321a0030349100c05000601000044180300b4180c4082c1000041c40c2940d000480313000301c01f100b442d98080c00c000e200c2c00c1800e82500e00010603c0c00c0100442c0c03801e0b68000c003009841320460303081100942101d240f144c1184952400c1d0015900104002e140000c1c0c0d0104200303e103840c5190640642e20000c003000325941040030104005288a180b017800e4405601f49000c1c240c0660410081006032940880c0e41481002c07000c00401e904424514021301101384001c010014034081500d540c894034a00075040300d0180010400a120030b0001582c92181500141c80c04105481e103610703640040d00f00052800000c4000107a6030b810842c0b180789441c0aa498110a10700f18001801c0380018100e = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 668071861 1250 668070611 668070617
    0x3150504030215091011040620010b2206090623010c0803013201020c1903020a0b0c07050f0d060b12031c06051905010f030e071203021b10 61
    0x1000c2000c05009004019080c2e040b5203082c0201c0c648105a41d5441c2c1c00c000c2c03c8451646040303036200c0e1014160f011541502d01b030742c459400700103284c0c0001140c94412580342c4103e558402400f4821303611004144a40026140c4610f6801419001c2c0000c03600540d0240a016290000810402d02d110070160760181c002d48072400c5071100c0e41c00594244000c0c600003052040000004030304115810182040841007444c0c43d5451000c0c05040c4d0907068800c0d00c610b0160340801000c408901d014100f294902c1c61a8040c5445c00e992980841c0c01c0003040c0e0807890005e000496901140c840c108400002810102c032012401800c1c3d01c0420120000810003818030f03500d91500300c40c941c4803030708a01e04515068040781d66811230498981e082d181000c0401e802c480c1400310024061034050803415212980003111494145481c0055840540080b000400d0584410800c10403100500a01c4010141140300034104004ca283c02400c1505151128851455002030115651500c1412180703042480c1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 668073111 1250 668071861 668071871
    0x30705060708070b1303080a0603080f07080d0e0309031c14070201020f0d09081506060409150b1801140c0a0303021c0614011e0509010e04020c0f0a15060315 69
    0x209190002e4400c90101401d07a1030510180022034810b155402185801382d030319604581c591140d440c05840341c0d48005804980180a20400d41c0c40382c070001c00d5490311030304d26103240108403800641a0743c0e88000d407080c95040812010b00500341400101410040d08030400440090b0440140c070350301c54011080d003d464040b0311001164000c00224010300c3c0b40d14201e6000e9921040010304007281409410440d0140081c0c203226044030700000703401150010031a40c14542068090002000404901c00480022070b10000e0403182c0c4e0f0005200500d01da62040702c01c0c0354003c00142113505022005100e0320310820a0002011002c03403100c409503411b00d8096038440320040941ba0b8a000b996075588136601d4100001000104450400d20603030003070b01d451809481d100c0305070040b072404586c0c1c0c1003c250f0402c00c0c0c0a081d8481c000245183c10014030050814480854140c508042520400002d520406902040c01020301030249203605c0000300b84845400c1d6900c05062040021650b01226103807 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 668074361 1250 668073111 668073113
    0xa0902010c0b100f0b2503020c06070c140901050f0111030d021b150708070c050a1a09010509030a02120d0609090b401403030703020c0712020307050607 67
    0x507003100640c0c80e030042e4201c0e00505004022091840b028400e4150210b4071950006007020408180c07140800f003101c5945084100c0c2007419032603c28003c0440c114082c0b8032038580f0a0356000042c00e911801000380f194004c2c00c240b4541604003070b0341400c91003600c0d2000100880d80d59182d042030200d03000e10b00314068420342c41555146019a80c80c944d01d0324000b00301800c0041c51042000c641005000840c0c10f50015a100e09080000549500300011613010005054900a00c41001c82c244100110b4842e89502e4036100b0b05000d491811054800e4881c0c18021451400d02940380c000303200201551510901b14000b940c2c132030704000c500d0036908000c138285646600a41c0468014042d001003400140322b1803400640b89001240c1c803040d03000c080281504900100340508001c94500a4113001898030700c009503505e01001141282c1c00f4540c0d40006640c503109002a5015121540b00540c8442051070980c1c00c01d00e07140c0101f001021807040d9000940d800207540412110103a4a281d034800e11 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 668075611 1250 668074361 668074367
    0x1a0f0c0708010c21060e0105120a060c0e101106071d0a0303020c0a0603091505060d050f010b011704150e0a08190e0306131202070819020916080a090201 67
    0x156034807210540d440e1425844046070801e1903005071410030884038461041114809048440e6401040a10480e01c00180058203241e070364680e001d515036041f102150010b90310641518589004500060100e120481d11401c1110310141c00b202907091a01d443da010604850340c442008050034204055070342c141860f020524081d944544005d800c00c20b0240e100d080c0070759100e00c0ca10341c60380145401d000010f00e2910a101d44607071650300032464220ba1401044100c040c010241419a00095a113983d0300020010440103020105101c00801c442c90100d00241000142c4074078212a01014400c0200041d100a4901a0311540d51000a400e2800d2000246041c3e2041c1008180d00c4000038111140d119035100644a00c80c1541c903003494501c05828562203ca042d22080207030080740183c01e000840c1081096240325992040706c0440d035407210b00f1881c200d08009080300d0901125100000d6041c40d4100d1580071100c0d04800c4640220b4050082200305e000f4154424650340e00035040441e0300c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 668076861 1250 668075611 668075623
    0xc0b010501050702150a0e0a0902030702060f010f291201050a120b0a0c0504050a03140106170d14160602040302030d0305040b0c0d0204030c180c030605030a060203090f06090d091a0f0c 81
    0x43c094075141583c9d0b200c0c600d0030025442507568201600c41c2e0000a00555000111141a235500d40102070300149029112982e600c006d03624428856100d1030001c0714615940041c01142040d68002c0480394503107014040000640c0e0080c00300c40001d500e01c00301043c500041150002603a000003c0e107190340000c00c07a054000c82d04825030054240380004184091861801250300100c00208000b81c0d4031038113034425281c422000030143d04500a50258640913241040700c01380c0c0311281c10301c1c01010081103080c40d41e0b500c50444044e5404a005e10640c1400c0001003038080a6003010042e0f81825221044600300042c04011004400180840c010400381c05840c01954088403542809071940c0740590b003641c146105000c441d16085080280710300c640220801c0380e4003d005044c0042040d00c81c40042d43c40100114000e114158844a84040030070209115070350000144c108100d1758507000f42146400d5001100c000c0185e040180a1450300c8100c40c83e064400301a16a600b030000c104c0307800d00d2 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 668078111 1250 668076861 668076887
    0xd06051210050601080103021315031b092003010522140702210906070204060509010305011d010c021009022709070902030f13030c0c060c0b010501050702150a 70
    0x109803006100c1094000003001810000180310900003641c524004440700f0609210195012020501620f015a0300e580058051800b0200c00c1c1c51880e22034650100d1380140d21038039118042062410000d2186500c00d54950b41c0d8002000314007441c0e04a01d6440c14041805071034440c1e100001c41c80c4040000c100300000740c0002c00c1050107100c00340d03000c2100141d02100c44c0c0c80540901c140d076030500d01803043c22296540260a84034109200c840078425640c102034422604a82c2d108004581c50f030340d48146a00851054002103a181c10b20780007030405800f803051008071a03040240f0010004d8010400000890059070001601d0b00c09000107200d00c0321014085049088030041030841c244580001c80c8100703019005c6540f442d6407240c400040340320032036192241e00b003d040410741c650010707260120f11038024549064000130a4031039078007141080d40301e0008540c007805110100311060500900408007401d0050804125401140d2003000032a02e09801850004038031168502a420301c038104 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 668079361 1250 668078111 668078119
    0x9081e040f030f0201090603050906150303040503030f180a0b030a050a0b090703050a0e03070c0b0a1806030507030f0612060506062a010b030c1311040e16080705030112080d0605 78
    0x425603e0511140c1040c895505900180e607400020035014042d00a80780224150b1009044940e80d1940594003540440d102d1a414002000009290380c0c2c204003400c4040700450301c0301e554030724000311030400f0311140c1142800384c0003c040c1082185102c10941c1e501904c1d51102055690b2600c602c18010803a44a5695024100700c00b4070072074079456408540b041c0c06c22402084030b4044030007140ea9a002d0300350028a5000445010310540000e1070141c400e4030114102580107400c0384490440c650407603000300340000c2d902d9040011090f03060150311480c05100400304000c0342480c1c60301c4411076142c10080c0005460354041040c80d01c400f001c4803082404078030f80001c4455452000705404150020090300d940c20040303441307510f180c00302e80041c2c0c3c1c08004180c800d40d041c850100314094090154503014051080c80000355a5424981891080b0006d82030305030800c41c446809400d50b8005804802048424001400090440c202c3c1c0442d0310f0300801c9890b2240c3e04480684040c02030350b0407850308 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 668080611 1250 668079361 668079389
    0xf0d0b0f09030904063807030e0f0a030b1e0103030906111f1d06060109151115090d0206010612181e23060f090a0209010602100b010309081e04 63
    0x2d01e11b001c45010010725050041c20390345000b40a0030603d07141103410300d0000450410241c00041d00a803644d529091001d001462951010000501000c1075070703100346d4124603d0002c000040701016030400b45c2c9950150304540d40d50450318010550043c60143c2c0040c04101e0803040038026080000c0c6e24484d91410111091034050310b402c0019100c14542d8103841c4010480b55a106603001c80c0c2540700e01c6042e03550144048c901543c101e203c040e00021001800403071030404050000921181803424502d0605402d542400c035400f0303140c128054601d9045403c008018480c1c0341d840420800c0030460301d040400c4010401d0000c1c60101c84a140042500c4c0c034641c003a102c5038bc41d07160f030040d40d6030103441d0b24244103c481401b401c0c052000241c40c40581c1050300001d0342400d4004e200394118220b002102e0314030a0550209507140000c2e003200b400b69118019000d8003401034022500b1055081c601480355080c40c0d6111201c1d0701800389201c0070f0404801000078070201e0001500e000f040b4401800d51 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 668081861 1250 668080611 668080619
    0x151e040302100b010507080316051b0d081303020601060f0207170609150919060e0604110f01091a1e0301120203071d04060504031b030306050f0d0b0f0903090406 71
    0x25a8480348842d0100450500c620394006602417401d5030401d0790040d0f0100c0c519650f61199100050803600403105010080c0500042800b907807541c4110002c04500410b8180581d240250201d14002c020001c2e4009024039040001d60100303038541112072905040c11100b1030360b242039092001c10b8100310b01441003840040020100002d5060190210384203840302084000340341407140c0ca04481e1420513a01094644414443d5a0780000049008800029a64005e079070010305080058900b40d84500d88540c403006503240c008210000c4d440f003402e0802916280040d1852041c0c900d040300384d1980c002080d03035038544001c40d495100d20031507040202c2d03980d82c40d401d000410700d407502c40c02c1e0301a2007407030380200e40740c500e800c070031404490340c010102c0c5c0c107541d213a40c0c10000e400014400c40400144802205031381d840302d0040c0c1700040c444d07100401c141d42003000b4029080c1900e02414800c450560a03a40131403c0d41c213800fa003041c281c0d14400302c0303a961040064954850204520342052410300c0010b = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 668083111 1250 668081861 668081863
    0xf030c120705150703051b120c0307150c0903020411040f030302071a031312140406030b18070804020904030212031305060f101202010c020a030804050310090302151e040302 76
    0x18292007080300c00c0484a184405144444d005010b001004924100b14400e082c4540715443c55100d403541080741d03803009a01c40404d90f950000303040400355500104072041088803c05582c44512500c000400000405050043c40115a4072010303000381c0d52401059104030030303881118050403c0c19500c40d41e1503513030b20b0f00a503a40c140c1e2280c03202c43d28280c1c241e1003010110200302c07070040100100d8500c0341002070301c8040c80d40711907903551070038800c080c3c80b10803030300d28107101500080c052901d000a411102c001800302240d21000546a8032916408002107a50461a1076812503016180d60859a03100d181c142e1410000f1b201444104d0008000c106000300080c0540c5440340c45841540c0c210344400b020b44818600c1607511954014080005014402d012450205a140145044440d102158003c161042203d40040d40c400b100043d0511842c241089030182d0100d010904200b02003032601c0003500d410000a415151681040201e0081035101c6041c00001c800704600100c1c41c10545006 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 668084361 1250 668083111 668083123
    0xa061404030b011401110607020d050a02100c08091b030d0c02151c060806060a0b220b0c0115030c151e080f0115120b0a15090311040504020d020f030c12 67
    0x132a001a08034003074841c4401010406500844041c1c005185000000c0019a10b5030005c0e1801d9045214203000c1d441e0340c5c10039024403842c1d16025116800d10303040084070b10b404e00507800017280403480c080715001984c3e180000d007261a1012031400072408443c900c00500401b820603400040350a010540d080071441c1808150b24800c03d58800704803095039115040c0d204c2c1001c981943d4044052413007048841400346c0100034000780200800d01801c01c08128181204441d0403003500b482001c80e41d440720798000d205107803a0b0840501c00c24102807039541c0f04400c901d203900075800e000d000c103608500d616019003131000e42e0f02480f20040c07803201c2c4036050080081030200c0c0d43c4c103800c043c104c000048120618892411104c2070303668491841d00341d44200c10103456841040b50b000310589000003070992002258504030401d6580d05d8020904e90b09061743c034240781c2004a8401e91a010900005039908034041d008158180c0750303030312103c041c000020304040707420300c100da08105002400e4400440220b11 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 668085611 1250 668084361 668084399
    0x41d10060605031947030d03090c05040903080108070602060f0a090f060504080304060506010e060708130f0b0309060604020306060d0c092301080a0207020307031e0f030e120c0a061404030b01 84
    0x104c5015941d4503200c0701c00c0c985d01400c400b5007640108210321087c0b8444c1d00040ca4540c083c1440780001075880022034206c2d60006819000503d01800500660368140001e900400640c0f00030310081c2807111000700c030040040e14582c401d55483da90841042801c2101c0d14069030405000c000ca4945400c0911081c1c0c82150101c840f5840c001c00070340789601070310000c030a50342d01809050801d240383e91105400d6000c0110100d45c052031410008540f454a007449002c1e041c4940c803140c81e81000d1241c14a07000c0701515452085005004001d403d4503000c00781c5032101800c7d0000301e00045c4144080c2c030703003040680000b90345c0090031380c0140d0074010312100c0c209003540a0360b903101941e0742d45c44184128028028004c1d0300d83c21040f0f003040426809001c4601816400d0000e84031805980d0f1564240c00d00c00c4803c41c0440c15038442e070201462b080048462001000b00030302100300388100000c07110702c8140181c50512101840c1100c83c600c001041c0c401841c1e00000c004083c1d43c442070030000310b05200003 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 668086861 1250 668085611 668085701
    0x80414100c0f0206070504050103180b160f030e0607080c12090304050a1d04060c0203160b150607230c1203090420040b0a0c02041d100606050319 64
    0xc0300103002c510006078103114004550b03903035007040d0810b001100585401020000c3d078203150300c1c00a000c1000c0d160340a0254030208035103100340a100c4000381a00407800c0c0e0f200281464070503d00c0c1d81d00008160139a201f4287d213007840035540e0b0410410000e015440c3c002540e101c0b81010040580000802081a100e0444d10300d0192550b880300c0556014400c16140c040b101c1da20003260004d00d2035007150343d009950f0300540c1c0c18076915143c0fa030700c0f400c42d00d003040e40c07501144030600440d9200840b120107a00015507903e032a000d101d44035202da408014890a0040e0344131619098403150034004100100c00042120381404001031503150b503900107898441c4224a00b50303641c1ca1010303600007a0b8441100c2c0c0080c00f802d081c80c203498201e2036000700e110340c03060100c0c1e848c408006036114446c20b0381c0301d0000f01034104940d041000032780c5401e19500c00d84041d42e14200d018006550001c0c1980e034000040341c10580703001c904082c60300c05802d0b40d610301100d078210384c4161040b041000d41025140b0240c06 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 668088111 1250 668086861 668086877
    0x14011815020a0c1203020c030a0824030d0c02040b130504120306030203070b090f090406050f07020303130f0f0203070803041703120109021b03040f0e09030304030807080414100c 78
    0x300ca030012880b07840102e0340440e108001c600002010b03041503802580b01400e00501b4100d480c119242940d028000c4e040005d035840c000c100c44c0c082600040010f036094410f00d41203101603440841d13030b030308071004407001030000d110001021542c803038100610b4014041c10701086000b0601414010301000d0310b040740c80008209040f400d0510905c104400c40e50020006c2c4072092070030b400c030301007503000407031154004400000281043d25408105030240c5d00c0b0f01000151468900100c000c01c100180000b02150400c100b030009024003001d800907003903001040d16091008074070340204409205000290180500703c6d00044246021010344129406440d0600513007200100346903e034800c55a40c50218120400144181e841d20343c09070040c0111a00d0824505041800e02440c2d40c1056000108185200801f401010341d51039015400880880085007581410395000c0c101010041a40c0c0400c806d940028051008400c2952401c0741c0302002d48203481841d4403a000070f40607403115140450320301 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 668089361 1250 668088111 668088143
    0x140f1914060708010b030a0b030a0c03060c090b1b0f120301150c03140c0f0a05010b0f010c021f1e03060e06010224090a06020f03150604030b0a0207140118 68
    0xc501d241c8075007982d5841180c00ea0915003050311580018000007540d0f641d540b0300ca07140341c801f0456140c0750740c059060311104a14503c0c000c030944240800302010405e07800c0c000c000f031049840c260394940061150341241c21007142506403911645406040c00351181d40075000034554094000c505842c11078980300d10041c1240404d40e0501c0c040c020040004100715090704509003a50040c0021044800980e40400401c1181e9071411002e64404d403202e9554484030251490449070000c180032017801d012500d804075400040040804c0c440c05240d030749170740c4035048050303108252824a403a2010768003010b140071140010014100c50151085441004010411640c000118840340c8032007180038882c0014042540140100090400d00342441424802000101d090010789080010b0020035602c070300d456090300c01020b51842035a80904001c00c402e101240c10303250400da100040d50405a41d031840f0380360410700808503011080b40c951030002401101c0c001880e07103904050048592030441d01803 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 668090611 1250 668089361 668089363
    0x40234050706110606061809090d080703060b071b030f08030103230d230703181202130203060d0209010303080405060609060120010f020a0207090c020a0f140f1914 72
    0x2d002c80f0b10b00301e9404031000950034641003001340000e80c0b5108240c4d803107800e40404201c0c15034054480c43c0c6181c108804107031003c1da0045450368000041d1409200d101c0c07500144c60207500c1066000350041e401085c0040384010400700d0340d002143d01058003640d090b9075040031803258000f07002c1104c03c58a40780c2c1480421900702040704c00e030882c00010304251380e103c2e038040e1044131b44800452061581c070192202c0720303001c01d80030308211800794807115a410707415074240c94003100c1508a41100501705640b2000750b100c8250310841c04a0761800103960391110400200c01d4039030408000c5d40102180004420946c0c440c0c0158000c45c071640460b011901c8000c10014000700440305503001131254604440419004540d14901c12105000015010342c918030450582c4c0c000c01c0400e0141e40200410800d4051500c00d400d0806140d10181441d905a5641c0180354554441c0117002840070020303011041c1c00500c070203441c4c03840b604121905d0951302c1440038441d10480390140c1700c0011540360400c10040c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 668091861 1250 668090611 668090627
    0xa270506150f100e120c010809030f030c0a0c0c0909050105130803160c05070909031107031a041a01090c091409012106050c0405270105040234050706 66
    0x3401420702c129120044140300001c400703422000b04001d0443e041601588542e15000c0100d10315902608071000440b0000d000a24050805611a401002800340c44590380d02500c2d04400c07a9031113a40d4072010140c04a0702100c0e40d46020b040100040f400088880079075001e030204621460003485196103880300b60140d0003038040060030150007040061650b440c03440b14418900342c1e40c10300700070a503003e4895038600078481e049000c14a543c1c845c6078041c90b4000c0310103d00c00c900308000b0400542076944450781040070080220302000403001040030460401c81a09550395003014039580340da510504c0c003024215104400011840420020444418424244440b1440a41b440283c0c5c1d2920194041140449403661103906003030ac41000020038601445010b10300c4001c6445d00d9030705200030029842e9406400e8207010105040030301401070880b40316411140708072401a158100801002040c0c80e2801c581c001429583c510210031800c480e032013a890070302841c1100c245031340307419040d12115 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 668093111 1250 668091861 668091901
    0xd0803070513091a090a11030117010b10020a2d060f060f030b0c1b0a0c0501120b010f0c031206090f06080303271f0e0d1d090a270506 59
    0x311040740c140f01035040040900b9009280b146c00003850712441240420a500203070440c002c0074038021074000c0c40343c109008942e00c0c44001c4805100085403680065680c000508000340384802d010100021000300900d0003045464000d00d40b4010112460aa4000c001282c4049a650300c0c016010940c24881c10221050329031111004001da110011518119004003003480300009018459619095041c081d40207a07d00c00e001502425080c00c1c0090001c0306400d0034284001d1411071082d910303070707030208251001c001d150502545444090500305c900b00405900b81c1406130038400c0004820440d907124407044201a00100f0003640c640c03803a00d8907880152003824440303020000021210f02003510444103c1400ca0445500c90000e2581e103500f0981080c0c2121480d82d225000c40c0c20340810b014060054030342d494018041c074401007801c1c2000460710001400795114100095100690344e004c002c0c21294840304072050505540d50031403180c142c1200712030f2401100c0103d1030344c04041040f880b0344 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 668094361 1250 668093111 668093141
    0x203060f062d04060b070312090b010e06011e0c0203060a02030106020c0910030219031e030f21150303020f0c10112104150908030d0b0d080307051309 66
    0x10000e50a0340c00e07401d50324490700400400da40b60150580e80ea91165200801c000c09040e900d5031000c0c1400742017400e8000c0224802800d240801002541d0601c0d007505460500c95001410b843d407000482d0038280c1d1004089001c0803603851224040c1c0c00c071600649040c0700700d04031445651414039840a9010070710035107005da440001200c41c2894921300c090340c048007045001442c196281c002402d0001d42804034200b08002f544240240040b0f44a04048a01c002400c94028501903800411302c2e0540e01c4c113401007055180c3c692040070f1031802c0c03415220b103007042c1c140801900ca00b04905000c0c114070003180076101c0c1070303440d12b100200407e04650a0100404410b03420340d140390305503911300d030308409200d49000310070b405400341c100140e82c041c0072003200d20215203580c10481c2e2100c403d40c46040a5042c40120302c410001c00301c0000494100315050000420044480d43c042002124503100061200c1c0002c01040409580070000d094120b0122440c100c0782c40c0d40e401c4440c200da026564038440 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 668095611 1250 668094361 668094379
    0x50f060412080c01050406050f070518240403080909071b03140712110d030207050c131806050a050f060f090705090613050f01092402120d090203060f06 67
    0x502a8140074540c10140a0b4070182c0c6840c03c40340b4000e084450403201150403c0d0341e14140071911040201d07040c3e1188090900614105070b50354818410744a200d101d601c6486004800c2020101120914010307001380c26800b5102e41c1c0f41c2c5485100c0c1d0b041809201d002c0ea4019001a024611032295008800050a141c10300030303040b0b45040725103071090b45401d11800c40c1000700304001004540d8100001c4e5903903966071a45d00e448203241b030a258000780900c08240c010b1183c8004620040b42072138035850200e9071320b040b0070302100059014151800d0403000da00302c400c003800305010141d04843d11614520320b0400c95a5260301340e81e10782150581e2040d420400206010700e65041840703030150460720300d09005e400c0c000490001021988200010800b21400180070042802c1514020b03440c2034090030701810340f50420004201e4a0320f82c1c0303000401c02d44144038243e0070a00901104100303070030100d07a60395904200d00e0040042c081c80c900c2280a48982000200c1903404c0003442c600a030401000461 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 668096861 1250 668095611 668095619
    0x8061e01030b040519141c0918060906032006030408040308070f06110d0f050f072003070b1510021207170d050403080702030a02070b0f130816050f0604 67
    0xc1c2d41d500400442c0d10788903581d64002800700380c01d4024104c6104400c442002440e55545a040000305030410060001d1000240318180d000034a41094451500151001c2140440007802425180e8068030445e8070740200803040c8038010740d42e10100400e085c0500d01004540c41400460720013120054039040f8240010b20000c2c4c40040141441c90103202e404c0200b082c50348030a02224503142140a2401780000d103055424101d02076a0200d0f50880c40401c41072422031010080c007200104158100b215080114442c54802040140c0d20f01014080741e803038100c10701e09540304040994580e42e861007c1c0030009081d103015843c0250381401a800b50040a600380013110302e40d00105411a201d0414846510703140c0c0760b00c0040c0c860801840004112410142800380803a117018201c5001c40d0010408480c07007e23000500c100c115800b190b00d0941d03404403252102e005020f034418103e10503034500b10000d0300e1200001c1d1120551110000072400591310410440c504800184003130b0001d0040c40100 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 668098111 1250 668096861 668096873
    0x319030207081e1b010e0306180f030304020a060e150a02060601110102071a0c0405120a03030c08010b04050105071104050411030106050117150102070b030a020a0f2f0f011508061e0103 81
    0x1613100b80181801c00340743d550000000d0400004447c0c1c9801c07400d40d1036080c007600004000020403205a503010354614105900450700b022058040c03002800102c10345540345403100d403903000c40300710482e52203a1110480e0100070345489041e240310340014412040842c40b100c0601c2100d10155000311080d100c003403100007484c0705207801007001800104c14080001c1e01c0d12400050500100c400000c0d045c10381c01454003500b04e58049030001c040020403801407141c2240300c0300321000e8540034209262110110316000214410b0704984036000350a21041c4420490000f44940002c0e804800922840e510ba47c0115035559481d07a1a000c01c08400340424021a22400a801c0500061040e2a40c4540361004080c03d41d00075500070300002c0d40020b49071092507100802e0b031034542040c500250143ca01d1034402d0381c140f4600d0240790709140c0b000051750700300d130040011130304a195000090103c0b80018a01c440d260829225907100c0717000d940c0001741003440103038590048504a061618859003942c0ba01 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 668099361 1250 668098111 668098153
    0x2120a0e0106050a060c0b01090c090303030504020d060c050a140f09040b040e07030c0f06080705032e061101050f0402180403051201090e0c010228020319030207081e 73
    0x200181d56a600001c02c054458a4414000c0d012a0b12450140595890700340c00d00c0e04140d20803441d0524082e40410000d910224200840e034061402240342c3d1154000a42c5a0005503001030095161070040300007150050040e049655950701c9005003034450300364200291040f038200125060041020700c0c61031800b6803210081c4400640009a0541c111854a20300310b0340e03030010781c0c290800e1a41000030502e200c0c8100e002e8030051800c2c400f04d0038050005481030001602e541d420040d0041e0a18401d26010701c50648426001d4514120607550700c0041c12034407250501c1400b80d400c06002880c2c1542044885008607400352148403480000721035282d0b0454003510072420054204a0a0420314103001a180a03003000311000907940701c00b41c0c4141c0b500e12403080c264155046010702c904c0000b006130380303003110045640703000c81c80c5081480060305058885a4028002c80c00c0d0490005041e800030340181a20144022a805200c465203030f0300c890391f00ca182a810b00da01c131015601001c0070319050 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 668100611 1250 668099361 668099381
    0x1401110307050303130203071215050c070f060b0103061409070f11060103050d0905040b0108040209220f030f02030301350102120906010b0f0d02030711191502120a 72
    0x603241007034031541d52541541c2c020b941041d01900c1c000e01c401c013540750a00410000782898480d20410300442d54a0303581200c00344090812855079800084c2c500c905120840e9002c6034000b00b2010305500b184ac1000c01002000502400207241c00c00120383d5410241d040300007128001e21002469440181c2110000020000c01040195030f40c074012142208000b1640030310b01c54009055090580440180030a960340d1040c4e00c9103040c0f4007c1010f80c2d030440070441c0c1150301904c0c200490b9640ca5031260454203e590035114600d0548040c0e4180141241480809440b80e41c651403107001e10030041740e40c3d00082c041c02030610000039400702d1850919400641000f00d404501701e000000f00402401c80e00700f4040c0b10001c419100821013050814003106000d880ca61340d9040c1041d140d10f85a2020307000d88800701d4101c6d036001010038250341c094024411035110500403a01102c40c0b00e1b4411210000c0ca040845052400bc003500c910301c0d83c01d000303485901d03060489041680d911046244090201149 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 668101861 1250 668100611 668100613
    0x50a0b0f0c06090c03120a0e01030b0114070b0406060503070e07030209030109170d0605090c160f240f02030f0601081b03150f0d02330a0f02060709140111 68
    0x100307150311110240040391054280c40d0103810795801e41c400345400d0803841071504400070b0f0200200e0700001c1d0000ca00c0001c4e0403007840e00042c0041c014005803040002c2d03602d007015034400414a1402c1000f02050307207104900c54002400019a00d0b0281503072141d241c002ca4268540d088001140180310758050020000c0c000e00104109619031241c448060b52416040c3c203050b800501c0c80381c4d2403c2c034003651005110a07580d182d07151500d02240c20707041c0210610743c02900d032001d1800040c07001d0035a100d900d56801040200549645100401e01c5d06074402003400c11500b848550b510700b4a461094034843d0100c402000640e40c2d400c0c00459544100801d8240403050710040592210f2490010350312a5a689407c84986000007041001070115034403200e106681e883c55210060702c030801790000c51f111007001c2c900000c3c6240b00e202c2559001c0000e0140c441c00200792691601d50009205645d202e2540075200c82d51a0220102d403600d0380e40c09401e0b0f840c1480f0b00424415442000741d1414035101c88 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 668103111 1250 668101861 668101867
    0x12030c0304051002190806010c02030c2709161e090903020a0f0b0604110c0d031d1606030605011e3603020f190e060a0806240a050a0b0f 60
    0x10b52004a8101000d00c0301780010300d2042101030b6420120460b0492000d09150045240940c00070707075135a440c500103900138130141ca403810007450444604180b80301c0e0003030344010a18100308165601d0b00071811825403058006030001c1c244044810f00600101100b507480c14490410000c0c0016002c0d1000450451040d07120030710100d5200000e45c0b442c580302d48440406030034400c040001380d4008601c10a9020401c002c50042048005844090032000c0d01f00800c0340103100e000300020b042c0c00c60010065004d96142e1001221248503188140c40150720104005a182c800440d0084840d0103561f20f00c51420400207500d500510786c411494050500c84070103180760402a0040481a9070341d60100040d0384018411842c0010b60440c0e00b4006440c1c6c0c0a41540c0142c24044800207032084501004602c000b10b051a100e280c810005000381008464450801c141d2001010f052203540a0300540c0000c0c410049142010380d0b801254001020500071504024040415034480785040589490070 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 668104361 1250 668103111 668103133
    0x5010b0910171b0d0c030603020307170604060b0307120b0a05070e010f0c0c050406180f18030c0c0509040503030603010b03012906070203010c02060403180f1e08060907080f12030c030405 82
    0x41c003502c0e80c09000303030703a0114107d4035601c18036150900781e400065a42d10092a68600c00710000b40003980540c011801082d100a22000b19003812115004030140300302400c80d003010300c241f1110880c05010070590810007a950014103c078440c05e040da030240011440b00c28221020b10550700c03861501d014400c0d8001240e504d0002038100c44481e480031f81d44459403034000d1130504e0184580010348403050410b20002c10012400010707140c03036440c02814800903142a00521584003d12b102600020300544030505250611031361700e0304101c403d03600c40d60030009071380b400f810103000b1020340c407100711600000b010010090360302c0b8030314005280740c2050041c003140000d40d400340a454054011900a05090b0410f0700300285040c846403010700321038803240001c2001c411046002403c4034001082c0302d00b0740d01078054040c0e414050340d2000c9054804e40091112002c804242c3c0c00480d607601d800c60302110b01c09248151a80280743c9803c2030210140006103490319140003c5600c41c4c481d5003607464029075 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 668105611 1250 668104361 668104387
    0x20c04020406090306200915090907110f070f1401030f090303060819080702040903050d090b1608040503030c0708070c030b150924030c0405010b0910171b 68
    0x1d0b88150002400c10204100b8440f0700e10501e815844e5000701d000b806d88007014040f1440c0700340f0070001e000360f90800c01c0481624000301540d060350801404200d940c00d20300b600618449a418034103850b40903aa005043d0207600190200c11a40d154a6840100340f402104401c000c55540c0c085052540380d90601448034034510845d2607261180c1c0300021a141002c692610742401070400010842081d203004000c140e44000b82c908035a070445c1e020881041902d004c4545008001101e80369030b0400c141a03080040e80265148a02904c1c0b011a5503071043c400c007100c00c62400e0314050120b07002040400c055546020044c010342c4c1c054040c4514100035962514041e50b01030748191081d04206040c040f038141c0040003207086201c02c170788004850410340c2440301084030a85000c04222141d154184568806000151003103100402c1003000350b9441d4040c091542c00030002903c20034510b0fa0624403580240c01d4480a0078031039440c2da80c0d80d641c02200004c400c51548044500700428444021640b00f = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 668106861 1250 668105611 668105617
    0x1509021f1b051005060604032a0e09010603110d0209041e020a0e07021603110103052a090f01031b080c07240b04060b070809040b18091504030c080a020c0402 69
    0x31042d001000452881c0d207600080361000340449100d41020081040440c2c0d0701d44440055000a2101c00d200b20f843e065581d1311003e444d401800c804040400b00160b590040d0301501c1240d00448116000a03034980402482030f85041c00298400c9880010401151a0705a800c503c01000200005401959000107408045580c800f081040380e010800c03421039814083c41124921701d000702c0903443d0540c4c2d2144c803910750320380c04075040541e02d000003001400c900741d01002030112555100e820100c540d00400c802e52207400f1681c0602c0e158032032102154400d201d0311000c50020311503101c0c00702e55000e081b6841d40000e018000744007010f00c0f030792010a0711003952000b150341200581e40061100710700070b0152000c60320500c0c400c900e040410040c50280d4000c4610f900d90000d040c41d036a48080c0001401014007107026500701540c503110304a00410307516841e000705080300455840e070380102411040c0c2c08040b540200044c1807258440001085000580585e1280740156042c2103008000700b022a0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 668108111 1250 668106861 668106863
    0x60d05040b01090608030901051210090e03091813290124090e150409060515011b020a0509090a060e0334020609060c03070f1509021f1b 60
    0x20018070041114004511515000300041d201031070501d0b00a03400604940500c0000014450305440000c40d142d0303061480802811140808000782000c40001540d240c02109a41b4010301c58610200c20b40e007a868140e501c03034145001c1c541480c841c10759400803403200305007007048200ca83e90501030400d000b6014103400381c0000c03010311161008000c400303000d146404843c1e1091102004040c00300034280c0f4040c9512512502c80005114609004a00180210000030b0b042c9840c0009004615200d414109040c480c240e8aa42010192105543c803840c503000c0025031082c05803c0c101315500305002c4035072340700d24004162940c507042d940300d24054a44949941046400000c2c0c4407020f84550454110341c41d48001e03050b01160341030b941c01040c2480d44803020707100c1e00012a5549155071160100d508044003001502d881e01124901001e40031600102182d540c110030186602150040c4641601960010440a1080102071241e211800c140d00c140d0100140310b1501c0c007100c002c00d000fa603011 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 668109361 1250 668108111 668108123
    0x705031c020738130303030b0d0b0f070906110a02090604060806070207030201080903041208030402031c05031b091e040b030109140f0d050415051603020a020405091603060b060d0504 80
    0x41c41e083c0880b018550307940707001c085120005000074010a921050700c4002e480d071506001907200fa41800181c80c0c0740c0b08074402007540d5416410809050841404035000d012161140200103441e403406a43c00301d02e4000c1c03109250704c82e00a2401515003460321039007066004e0800a00103460b074403140e0070f0103401c41d80280964031280d410411568054001640941c3d0400034504140c00c1422101620600000c0036203410340201c085810365134207008000e4081d40d0039081c40c1c01800c03210301c00380032504102c07002840741c4c4001d034131044c40c40d00c2601102c228180051110325890850200c00c0c0051080c0020290071585d20021480e0546003449082c18050017006546581d003e2200040d1600e590140c84e681c06801004040069a80080c240c0d13040d00d40445210b480c842c0007180c111080d0240b0303600c0c40300c992003813140402455000300d03148804034001c3c0d83c14003c80d40c035091070039aa8028001d0b4080c00746a211000c1000c641554003200724040b00803c1c00340707010310b02c1c050391054440944043e209 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 668110611 1250 668109361 668109419
    0x7030b0d080a170105150309152502010908030a1a0603100314070b191710091425090503010203180609060c0a050c011d01150501020705031c0207 64
    0x1182c2d030404a0101ca2030b6482031510785075070614012840d220102402a4118800030000c10540e84060000c00c4040101c10b051160360710304211a40d81c0d011410410038200d44100c1c00b00070481e48180207a001d220b4124051074a940ca0b26003403d401007c00702c042441444800d01d01c0a40c6582e4078004500a201c0304111403d118110308080000380300740b40380100341e60300c10401000030b07000f1041542c000c10041d00800d400c400490009688104540f800e451419071b03203108200300701281d50034241c196480074404014540c45003080c6011804140c80050380180c070594140d5410400c140c120340003002505e4101201c5a5403000709003a60010380700d10300309403030f02e6180c0884140104440c82e440500d03503005203c80d05182c05001c2e014270692524a08200000414803400e650941129015030f400700e080102020301d000100c1c0c002d0450b0301c803140d8001050f031800a025840003414905403000180030740701010f503140590043daa2420407800950040e08000514841484900010038202d141d6100d0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 668111861 1250 668110611 668110627
    0x7170711010c05070c0e0402240301090e031206060912070e06030f06010609060e1c030c0507050f01121a120f010513030c0b04060b041e0608070803070b07030b0d08 72
    0x3003034442d18401c80b41000418840400480e0900345141d040361500810501240c80310700203c1c0c150140c21104084400a460043c4804100040154105e82d0428002c00c0030008680884da101d10851124101d01034807100403540030716142c0f00a103036407040185000c000601c80180c840c14900285e01a600c005041c0e01089000e0500b800030545141491019180b11f60400c0c4003e03002d0400350103010100002e03e0f12040140e112056142603924203110101c11110061900400205045208a8084c0581a00041d841c10001a0200300090503190001d81c0b580f442d5203c401001440030308810721143c02606099034881900e800310b4040303036102400c3c200329007000036402e695000e40702c060043d40c0e0410041c0840d0780242e4400c041544840f51100c179488602300040076148280c0000e60240c50040d071b01d0101011380b021840780c503e2040c030501c101d81e900c20368103846101038468010550020007007800003a06805145500981078103002031910b0b001c070082a007032041c1400031945550005110b407 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 668113111 1250 668111861 668111863
    0x1e030f01060305060c0a02100e070b27151e130308040806010f15050d06090216020307080d0c03111920030109030906050901021014180307051507170711 67
    0x291780541c01141c1c040c0ba1002e520002543e880c100c1c401c15580f241e40f011401c1292000340075902c0140144080e20340c40e00c1c0c911100007105142d10008800840c803410030303100d0f981040c0400c0514800204921400c1c00304903901051080b02030b00d21200c4100317041144e09003200a148003034001d140101c035640d4440d401c1c0300316603181003030681000ca910104080204080c14070441c0f0106241010b00e0581c0c1c44010b85658440944016004580c000c0d00201d08441101c0341031700d41c980214001c808440d48140d6413881c058841c4600c0d1030010001d1410280140841d02440380056030b59039480c11140344a5508091810b59905e5000440b0520b034005030306030141401d200c1400000c04e08070000c008011050b038002d0081902031052400784800810310300c0c03041e0b00a100c0c1c003070325541c2d05c181800902441d8140b1155110212070303004419481410b152003040c0b000083d140b80c2c40c0d10000405805143c81d0120100d40790003040c0504010301d1030480c60324016998500d9000e85016103c2d4444024880903031 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 668114361 1250 668113111 668113123
    0x103090b01270902150904021e1323011803050d02100518100e100e0c18010e01140402040302060a0c03260f0702120c060a0c09080604021e030f01060305 67
    0x3020300d030707410f0050b0341000d6a680b402c1203a0080a800f01117590740001c00100d0061b002d60a000c054141404d043d40c1c04820750305d4001d14002040d04546441c0607165051071001111043c031040132006c201c0032034042075000b02451410104560260060940d680e40d4540c030381003094405400680250301e42048102071401966000001120754141c24001010001e648a03460613803c8802e43e1149180007900202340484c41d0700703608040090100c5941480c00355640c2c4c9128103000d02030840f12451940080b407102940e8140c40541d0302800a81c3d02e01907000301ea00940c408090f07400f03582008000010398404004003440452622403040380c0c5014100a0511000c006103c4209046031703250140c3c8034481c259031079005101c900c1d030140a8541c100d0486c42e0011110139070700e04802c0010300400310100041c4591050031491400e04c4454550481114007402e01d1107503c0c0a5030142021034018070305940001c1c440101d000003000c402d42a60b0000785065010341440380540d569000c140140f080078440 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 668115611 1250 668114361 668114429
    0x1090e1e210c0c0f010e120309240a030b03030409061d0c0a02030909130506070207030b1b0d0c1403010b040929150c06040819090311010e0103090b01 66
    0xc030b401d081d4002800c94680d16142d0302e940c030400040e0403100306603000350100158004040c1044014018000c4401e542e90f00886c596407081000210107080442c441c861004111300104255050240b50081640078042400c00f86d54940030511010680165500c15040200b8a10203001360401c000c4001c091620000b0301320a400c5c12003004004280c54000003101d40c54a02a80c00000c503584d164001a00d0182040c8014614054401409280c55002a004c030589028a6665200d0340300c17a0300a042d1403002c005803c442a10502c40e40300b02810780c0e44040e4800c41d950600c4d4140500c50f64003401550300c02d8011403842c11006c00d05201c1071500d0b200d42c1e84814024645414005501942c0304504050f00d076a40e8400c100d003983c0c10000321441801d0700d1401600380101d5101d802c1c2490075082e9600300d101c00500c0c0c02c8420b5150000e15100e1510030040f07a8000c03800c2c1a071045480011540003030f1842c4228107168991034a040000c0466544600904684165000c40d4110b0801c2002165401e60 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 668116861 1250 668115611 668115673
    0x804020f03060621030702030d110727020703020f2b080c03010306020306130f0507030b030313060e04110408030316080f06011b050105090f07091401090e1e 69
    0x20820191191001500c8a000070f50940c4d070115803c90f1001c0c41e41c072038450300035014061004d0349958990041a0000203050030800d803107440b611032084d0115103441405d2241049030a0b82440483d611a500411000c1e00a105840301811300c1001640b81060301809040340c2e07015404203403e40d42c3c0b00c121420f0900c01c14074140005040598844049002c10b0201804866000005c101c907503071500740d0010300b078400c08014403103c40403031a04002810f044071550080b900702210100a442c01104031100e0089580c10384003c0c0303007040c1048034114420303003455030030039520700070152000d07102400380c0000c0500c02c00650ba02d01d000103805c0300111401d0000020310201c0820310800103240014294404001c0c80c1940c01c56a041c803090345005c0c291074001d0115480c020501c41d001201142d4003141c002c00b901184d002c141d03500c01d80401c1320007031f210a6650501c9800180079059240c0c000003404038207101240c01d000403800003c0c00118100140761380c43e0b4484056205860a0000032a20391b5000c48 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 668118111 1250 668116861 668116873
    0x606050f0f0d0608150624340b090d090303090603020309070509011e060807050702120f06010f2d06030903091a070302100903170709090c0804020f03 66
    0x102041245004051905450401c0441d91142c041e41541c090801010b020049600c0740c1d0300104035141d0b048058030458002c0000b0307250748010032190042d00303c4503400034442c01e24210303404001c10107410041c41c000809908144682e002c000c69017400440450080c08a0340f410f0508085052400c8040755500041c416410810004250051107110840c1c0140c140035940c1e90f00c0ca6030040c10141c041e04050391100c5110004241100c81c002c40001d01800c204840d1a400e4603410141e40c0d8042c01c80d03850300003400c10070048005092211198002d0b014803821110040307903031142c031401d0030720981107c207c244008404004035030f400445c00100f4138001c4d4003080c01509540300c548542446001e280c00741078680303040e101014440c0109000a060307240d8400301c062100c1061584071707805120260014401c00303406e00380341c00d681d00c214080c456054030799100300d00925080700143c0320018001c4d01401900382000503c1c150900079101500101d0340c0f28110b45c0b4062040209648544d248140070364031030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 668119361 1250 668118111 668118127
    0x1a090106090e0c0f0a110f010501032d020301091a0f090307200a030b010f050406120605130506040b010509090f0d050c0f12040311091b0a091512060605 67
    0xc4100035080d509000c1c8a07040390b59030800043c1d01ca01c44c5405200220380c002030701e085855841300400c600a1082c1c0c3c01e40744400d014100141c00d071082030101800c0e0302c0000b100c4a803208541861000004030b100041c0c0340044142d00001d08460000d5002d0314110f000034074101c1d8171100c0c20b0f00300f98007001c40c1281015038148883d085a5078044c4001c010074500c1501d00e0980400c0d51100f021800a4004100306a50364403460328515000c0d080c030400c0b180d5602800041403500d45409450160350419136492440c00035a11a8005498082e05211810b964041110301081041c42440d2050f4050058229294908024030005040041c440d28140d0091811582c2c02c0d403010a0b002011841858015100c8010300d40003400c1020342d1150808a10581003c0d5070044d12101c0135000b01e0303000385c0021003200801c1c0244840203000f161315000c0f840c07045403034040f544402030207810110014036041382c520361681c400c118401c15103811704001c1a4400c050700510840c500500c0080c02032807609904244003 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 668120611 1250 668119361 668119367
    0x5030a0b040609140a21091d15090c13050609100e010e0303041e150503010b071703010b0306090907050f090415060e1b0a080601030e0c030d02011a090106 68
    0x4080c000400243c0c64041d100244400d107941810810002020703601d4110107071400441c2154140e0401540d0b054022021b42c0c164052038400f4219540e038082c0424404441107001c102c5170000b004446411006141d08031152500c000141c45268030400c1c1c1c6a840c05a0700b9202c140100c2d550029101b0002004050041c4c0c60790301c00d100e0140d401c4d060074008000c09800503900e1014020074130b41c152001040014224001c02a05032200c08402c50784a80e0a44405071020050f4148901d54041101000100043c881400c018000c0f24003401d14a82c002d41c250a10314101d500aa01c507025485010041c0500c91801c0d801054000d980b4000810301d441c039120203d0200c184040c40c0034864161000000e0500c411003500490800380150100301c42e6071180b410919894040e00c2600a205000c008250180800c1c803c07100d04600d19102c403900c43e9694001100a44010480c9800a02480c0420740780342d2400c00403441c2c1c40362290000300d0400320b000ba04104240c1d41c0d542803031190384203d00412000760 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 668121861 1250 668120611 668120633
    0x50406060e04021305271003050d051e0417060f010f050d0f02030106170f0d0801090507030e0615010e04050606090d08120906010e0c1e0a09031b08010605030a 70
    0x41d06030307005603e51510058002d40b41e0855403010750420072a1503101e070360072070305003407110a941b020b1500c9a503511103400003940c0903807600001341aa8003e907982c45010380034101030002500c40c2e41d800000505070440841c46900150300c03905d48000c1400b0f48942540b414469181d0000f041c90b0190b00d06c0d80345c03a60208040c1c01600c10603005244655403030040c0111020300e41c4080b42c001d4000e1000070341e2650749800e881e0000c1c4815506014400e100040105d001c01e9a82d003090f10350383c601e1480d0b420040007000418000e0310020034959191880c2c001c0117020b0100781d100c1c04042c400c100b03044580b0000500945200000e2600c507610740710402c0b030a5501d4105a9003205070a66002e480900c0718031700b1000780c1c415540c4c0106040051402c128102a000515905030b80803401d8411490300c801050300c102d03010b06c28413408002000d04158442c403210001070600c000355450044089980c980340d026081c3c001c114410300300c103010741050005a00900034640100310550040c003c90003661180d4103014 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 668123111 1250 668121861 668121887
    0xc0201030f0f05010b12060303030c074d0a080a0b0408091c0516030b0708040c090609050108160b0a050f120c0703020d0206090703030c05030d020301080a0c05040606 73
    0x2558407101c40c1600c03000342d44812465480c0b00c50402803540c6030158080c00e5080711981c0316040e001c107000a0900d050102c283c0740a15202503503d0f0406805030345003001a241041c02802450301d400003001580c4040116a01240c1c056003051100035000203049440c0402807031303083c000c0c02240c504012400300010000034007034100300e40c0b0800707448620b40a41140704160b907090b804055180c0705010007041945c81d009141c4500d00711059001409104610304080d0310004d44100d03451070010301c1450040c1556035200780f0130250003e103076403200c10640484100d900a10380c283da0380c5006004281d41007000305050750358103c4e894000c40c44d020140b061482858286400c0040c00324295103c919003106640502450268121803447c1180c1078800603041050184c00500c10071442480d02800807400c07030300420a01c4082e0000c1402c40c0ca00355401400e48800326000d01c0104640f40700071000d403010b5406444000084e0a024480c0d050034406a038081c0c210612651a004003000a0360304000400c03400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 668124361 1250 668123111 668123117
    0xa0305060306130311100c020706081005090601030903030e010c030c02070b0c0607050a0909050a0b090f09030f0a0203040819150c050a0c0f02031f060f0312030203060a15020106031a0402010c0201 86
    0x1d51700748070b82e5040c15200c40f00701003403e00700140400f6840d000b283c11401e8a40d02c0e034903500a6903503540d201d14818140c0c403c242d04500103502003030701948250040d540e22030107800c02140126000e00b4160850791101213207000203a03900700d900c03400c40e418000d420007003020b503030304505260840b600947c8500300034102100b40900000c0400c0440e0240302110002c0a44075010000c51900c40300e180040c010000e0480d100315050380c00540303002c40741c0340d0041c01380150070002d41c1041050700d503d501c194081000c0e101580720a100001d00700e1300400003d00070303907400c5220200604039840d04440d440c003400c00920403103080084040c001540700e000c0d80ea200141d450030750280115400c210f0080d406112010790940550078060342202c50340b00310b2400c3d07414080780030403003a66101001d2540c100d59000003400e40118000b8070b0076141c86034003c0e40d040b810060104494560390b8911075443c0507126011405070751100340800a0019002031000003541c80c4030010035078981a40020200c016803034009041c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 668125611 1250 668124361 668124377
    0x9020c011401030c080c150306120a0c08060f0601050c1c090302030f0c0423060f040f1b120c120506061303030c1101170f0901151805010b07020d060515090a020a03050603061303 78
    0x1c5152b081010396600b0750030402c082480c50f110400f403604c60204503810078221140b44041901c5521800484c0e042003144806004140e10304020b09001c80580d00c00e00d000c10282c0b450104c05603405009007103008000000500c410f40e03010061009480544450780f00f6040508031140f800059240d000354850070450313041da00c603451030002900902600c046410f0641c54201510006225040d090a40b60040d0704d07182901d00504c1120301c1a51055018080010086051a02801c01e180c1200e504204003c000508210103000b56602d405000d61083d00007480381091101840103401034040c0c0c0920a1801c0d41c1c07188080c000e403019140b0054080e200c1040c52500040940303c0a41c401112103503810080c3c0c240f945d69040303110400a07040f02c0269814500000040e2003681e0004950340703d98083c2c050b0029000c682c0784c19009000c01072100079138500c294540c12440c0c1e0b4000d0303054820a0f41101c01030300d40c400c070030008049a07001440f9600940c0f07c0014000d440b40b0b084449170805900d03141003d9 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 668126861 1250 668125611 668125639
    0x4110708040303033210051906030525180e0c071b090c09030b091b0d03020c09010303030509010f052202030c0a060302120703060f09020c011401030c080c150306 71
    0x1301c00e5030302d02108003542c1001d81784203a0840c206600360160172603900b402402c58442c03007004203c0c03100d000242d4000f400e00b402000b0060003038118651183c2c40000300c3c15583d40000e80c800507584406040800520080001883c80f00e0280c604400343c90074136202c03205032811214540301c0c0c0c4107161010305004200b1858202d44101244000c2c090480c80b00103103e00311544030090889802e6000c125084111840003404014000038406e80c800601c1c24401c40039112481401304680040006900314042d42e1040001a11420102030096100703540c00121840e08810244c01c460b0782c81000f140482c1844184200f104d219894901040d0032458648061029407002a240030180812a900300049a0001510710f4243c2e002d00501e0680d2a042c0b2600e80e02d251048044403032074000d9440d2402c1c40e800501c6000c6440e4050030f03140c0001070002402010f0f40041d10a6200c00344d1088445907061401489598018490740d00250000c2d41c044000c5000b111040681e804001c004038051117161403001 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 668128111 1250 668126861 668126891
    0xe04141e0309011d120d110102030f2d01081f09030e091e090616230703090e131202010c0801140402070807050c0306010b0909070806030102130909020411070804030303 74
    0x240d0a008005c1060b050004070b00340c51501c2ea0103110610010500e000e00007a030320720042c02168403c0c0740030554902e49598040881d8416005d003585201c142080c220b540e00c10504d43c40b500e602826084009100209601e842900c900d40850220000e1900f07003040c0c0400250010100782c1d08180498050280755905824a00f506e140c035070843c0140c20040342440380070240841c60f18003491040d115800c4164103101c0c265810046210041001045140481d00701244030000d000424464179001d00d032503075184240112504262101c007000b00041c1e0703440b010442c203c0c518060015190000b07001c00c0782204070103401028140320b00000030400740000794980e80c4030340c12206110381c4105d5588e2140407d041a40e0b0712030030026514080d01c40d810001c00c9408000c0b0680700d14210051408501e42d035810011180040040d0403d03405640900c400d6440389203101d901000740000c418005040c980c3d9004001c10345001c1d4403540105e020801043c00443c0240341200c050360f80500b008204070329140020303 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 668129361 1250 668128111 668128157
    0x91101050f0306150d14042108010603022d09130b0307062001110417011103180a150c02120903070e041104090f0204140921040e04141e030901 63
    0x102d02414038050245800003e06c1c20214061802001c40030820041fa2400f00c1c0610a43c4070800080340186c00104074042c42500100894a52084102d03e030603034883c00780848003031013000c4204c2c030f220128840000e81800d00c0e4103003e50041071402c1c494080d48002003503c4903800e02902c030400c0f00021001401e5007110001000091018008001101c50001d60140b03a810074044c0140c041500781030002c8040c4140510318245558000f103500c0d41e103501988280080804070811482c0c000c101e42d0b000800c01042c020180501c0c0d000010401c02031011000781856010050b507100030201340840358842d140080c9441c25182c0b000c01980031038455090800403c02e581c1b860750b40c840d0400b4080e01c20441580381d55090f05100b81c0b0280000141c00c107aa03004500215245441ca030701c2000182c04d41c0021598013000e9101424109140c03903143d00e8a00c0c2c08113170883c0c054031150300c07203d480000802d04001d4110404540701c40c40020041d40314101c3d499210741800d281c1004004c007076031424030300200743c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 668130611 1250 668129361 668129377
    0x15061305160c03170a090201170907050d1506180e0a0f0305210109320c0a050706020c060f06091006051b1501090b04060302090c0304050c0d0501091101050f030615 72
    0x44d446603141009600014140220702240010f100594140c513010329a5980e074002c0c100070b8098a4140d04190234041c02c03082c10f00c020b0313070110b500b0602106000f40d20702c5010050104c2904c2a6031003804100e01074140c1d401c98440c2041c90348600c08600100d10380271480c6034582d07494904940d940d2820840201600c4c2480445040710820b2400002e00b25410340c070403500c0750452600b89000785400f0a08998109425154079168540b80780050f803100441c5008102112013414424100030503a00c03524100d03040304c003040364180d00c004203002d401d40d00346403032662203001100e90000a181000500034001018816582400310210344c40c542c0f81d201c4025556030302c80c260101c0fa180c10840880d216210000c0c0b050a01562a1143c3e00c6400d0615000310380903207402a00e00f40e015120310810804580c0024026211801030b8441811140c1d90600005000c900a02c0080b822908605066016040b0142c0c3c0e507051000400c0041040d040071401e480d0b1000e001c48210b400d684c036028140c1164420140c3c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 668131861 1250 668130611 668130647
    0x140a090e0703060302180709090b010e0d05101514060705120c011b0309030314071d06071b1802070209040b060d0c0603020c070f06051606090515061305160c03 70
    0x107403d51400e00b2648402d2003211f9076a180401e85554424034002ca5204096483c0000c01d0080040c18034144410380c00340480c460340c01c4660a160212001c400c585008034880f19204080c40100500b60030032040300c120260890ba00da02c2e122656031410b0356a0585050b088240b00e0104100078820000e42c03200080070341c2e100c0c0800c010443c6881c010010a234686d001c9000c0f9150000d090042404805651305c900c8803600c55052602c0350307100000364085103035081680000204060380c00584008001081d83d41d5070700442d03007002c0c1460500718481d86003480701210148148680c101603651040c0082c0c000b0340091000c0d41c00d482e00000b04403500f204980242ca04059807400181c8964540d0062030200741d01429606480d071281492803c01e00c0b0f620501d00010320034005003480c41903203210545810300c178000c00601c404c420390321b035410100c03e0b5582610b5003440e101017200c1810805540001075030302d03040c200128504074040c0d40d42d40303a04e982a4401c01554210080130140150100d03820124001 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 668133111 1250 668131861 668131879
    0xa0e09100504060c0f09050112110d0c0c03110a02061b01090f030e0406062f031c06060f2d14040e180f120d0b06030f0601140a090e0703060302 63
    0x3c03c004024000c81d002220024905401c801240303440390410900b644c1050b5610451403030011303051030103400580c000c07400c294020402100915a188580380810003503490761100b904079410080c08a20308a8050910781d04a014a540141e4034941101c803000c1e03014008c6440385000c00b81d00742c01001d142c00000c0c40300d90140000014035420811051004100729000d11010f0b8807014100c43c806850040c2000031545050500d0301f00b4200c8096551150341c590480c3c4c01e00510310300710b465840c3e24000000b030a07941c07403000b441f05a901c5054a8503908c104d0624103501d1020041d400c0ca002e1481c412014140120030316254040d00c102307082c841411001860640b11a120000180d81c2c81c815203030003861940d40340c171415a00780086401513000344444003038642040d07403840f84074440c2d000003110910709940b003030002c0c0a035a0f10b02c090340c05001502844000c1e80b402200242c64001200341840311880144070044d0080e9200b140a02079421000c0346a0700c586450740150054a12600300941c804900c3c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 668134361 1250 668133111 668133113
    0x7061b030902100c0209040f050a0206070b0a05010501051809070203040b121012022b080301080606122a0f0409080c01051323160b180a050a0e09100504 67
    0x40c1c200554141c000c90700d0419505001c007040d564410082030094000703c00b0390000300800c5024074845007280c01407003511044c00a640c0012810b17489890100c68002c3c40304140710100d0014801d480c00b4000c01c0c2481454036002000780150513800180d080c0c070400100b0002021240300f881a42d00900c414a81c1d43e445a180015244aa09048079030078007240e02003000082001c4411b04006000740c010b4240c50103040d04440c0d950f44140d41c10919070390303001c201c0f0083d400190120015802001910081c214500700780041120a4a0030729141c1401d074402da0251954803e210b440340c0540144502402c842142d4101081c1c3d0213050041155003d403908000344c051017078010040640e040002c0c0200300b6039446980b03242c054540f40c00c002d0025070500841440c0c24143d0b05010300803001c01021078254404911030005c501c2041c2e0071605c0c0c5094085007012001c2194044880b620a0441d03502c000181000c020500000e403a02ca00601c3d20390381c6001c52051079003480b500d40d00c12564070b0305020500d85 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 668135611 1250 668134361 668134367
    0x3020d030338040209061902010b100c020102150601050a030f23060118030503030406020f0913150f03150506121c12020c150c04050306090d0f08130807061b 69
    0xc2d5800000c28401050142d100030700c0c052080780c000e03000050400d410505018010301d6901c01c43c40c801c0c0709544daa520307000c2d0969100400301ca08035030303990b80d10b0f444070340140b000a04040ca5407150a1204030f00c82d0070701c80f8680e040b070141c5070b107054146400240e0701407405000000e02840301c0000701558012000c010003c0915000f944501000e0b2105040e90303031405040c10f4682842e21025006400178008980000d44507001001e4007409110076509108082c00011040d001805071954844d43e00c03180c0982040640714040c0050a2958008010b03625686a8583d001d890700c800c0800c156403000000c0b0307035541d9007214022818940084072140300460381440c580c00c41145500d004188004900360031050303d03000f120303040d41284000d0480340c11000801c1d01c21307075000781c000241541c080c000428070b6102004450321400d5940010b0004503a0700f04040c194824484a8000b08482c560400c0b501e603665120301121941d1008800342d884115003801c000800850110b10040c002030680c0d98800c3d98 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 668136861 1250 668135611 668135681
    0x3010305010e07180504020a180609060801140f18030406030606080a0b010516150f0221070206130c0e090606040c0f09051c02090c0304050120030103020d0303 70
    0x44560000c02c080c01620034065541d1040340704220400ba48000c921100840c0c94100740c4c1c010b440948250707003e03621034a50800711020002c0e49003559986920801c81d182d400e00409004000c200020415030820825091b00210000d0441208180101c0072402c800400100b03001c0c4484000182da448a4032110000c02070712451141000141c02c0384c01040c074002d01c500c0391a01c0c2c03200507160240f4140f660110401c800300c48450941c1c2403003040c1010b403981039440c0640d41500340c1500c2d0050b035483d00d80e01c00424040308483c40301004000c07441004241c036000101c0c541c00c40d0780204441c04c0700d811480d14042410440c1c00500721010181c007030010702d05002400307034018941118184025008040100c0749101300c2d1100348002103840a01700510708140280d12021560300031410007080c050f0300400c51101050f5143e6942c0c00b80001004103004081c80740c0c4c68064001c910a0f0403044075014988058001030001034842c0c030071601c059003094000e0340328140c103802d4400f000010707498070141d803d1404 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 668138111 1250 668136861 668136863
    0x90b1e0d0b0403020d080108070609031401060302190e0a020306060f030c0c07090501080c0108150114040801050115080c07020d02060309010207020d050c030709060e070e031009110f010c200a1a030103 88
    0x203c01b100040794104020a03a00161a05076840903040c2d86903484004400c601c840044407a55a03400f00400580c40d0120a000140e105581c0802c10500d031820018010328003c0c11030040901c140b00784010740da02c0302d0498400d0102d4803070b56501e986550103910780c02e00c0b40c41400700242c45060760009161449400c0b040c12600e406041e107a00002c13800c0191101c100c21550348051000c0c262000d200381d030050400c0703410b00b41a45001402c058440c0002d80c210f8000f0303001000610001d202c2802c1096000e80200e5001590854003824000a0303400300e040f03002040d0001384910f00110002d40c03200400d50555402c40d80003040c1c05030242d060b003801c0c0d0300c070301c1200b0502d402030040310008502d0070740c540a04000ca84190030144001e540301001243c4409041072882d61600403c441564400514020120801c1c003c5000f05014049401042071f1000042081410b000d0948000c001144115900b00d0302d02014114440d51040d416001450030f45e900e0300b100e00e800121941c200c0240d030b102c50245040e6 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 668139361 1250 668138111 668138117
    0x60117041a150117190e07170a080f070807020301181209050f0d02060c07090501052106040609050f030f07060b010216060c0614070c0309090b1e0d0b0403020d 70
    0x5459000518481d42c4566815038003203000c08000184130b481000241d94483d40590258140d10300190900096580303134420000d4075440b0507010b003d40b211801000c5151003d1740b009100c088074560300d20300d0b03501501003001c25840c00400c141e400d200c54202100c4000e58010002c1040380c07018080b084950076151000c0e00c503000303c801c1c4610150300408800c0159400105a94007860b80a4200700012101c04c4040b40c002d04240b040e0042d00200b0407011000e442130b0907010440c0d60402045c861401402c00c0c07008100e2076000c10a111400c0e0215078030b5006504801c0110712107006d030602074a01550066026001c0c800010030361001a00b50300600141441031070240724a0360441c0c01281d44000003c001c400400c940306041020a0149081021162080c0c00100c1d00082e101d0b5030040d000c0d0100d030303802d01266020403030302c081503409402e00d009020386000400000100301d010030042e414165061010341c1e04101002d600b07036203280301c103014560f11031229811481c052034000d440da008e0031026004 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 668140611 1250 668139361 668139413
    0x3040209041e022d062d0d090b1816061b02220e010b0109061110060b0c0609011505041a0402030411031c08060423012d03020307050906011704 63
    0x1605e800001c80703c012007a4003e010001d19005603048040600314103400041008010b1a6020003441c00781038000b80c003584071440c607841c1120211100882421440510b078004440311500b10010b03103c108141e4001d45086200c07a40e43c0001c1c0c01149125601c042c0d07020b1018446541c08180712001c0480032080c040003440002108004182682c49241d0b03180e0100300c80c800240101e52140510541c0341c12903c08a0f0704c5070000f04040d800b00c450f95006510705142c0001d440040300b00402c803c54005040340000c03c550074140d6010708100c003a81c000c1c50300c00d940350b03c0b404480c8441d132840610500310081003150b880c10940340407044945840c1c2c1da40c0c00ba00524608000c0300c00b02d02200720b0644480e80b5134040955480c0200710003032403600540444100c07a80c07040403200b1040150f9501030903241900301058101c0c80000307030704001240100314611681302c0c000e20050b03e0201d4183c5c00c4507810785009a20703490b084010717101c19003502c070303551703034645140c0c0401050080c0314400c040740c41d02c9041c40e807070 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 668141861 1250 668140611 668140699
    0x10e0c040f020c030724050a0b010e01020607090e0601031d01150803030c0405060706020c01090b060a0515073003020a170f060d020102030d0e071a03040209041e02 72
    0x8160f020340010340c8003a0300180807103404a44180462850f41c400030206011b00c11080346400d0442d40d05807008440715030381d904c500100b0358000c5005d61300e800090000308842c2c900b12900400c0d000382400307032000c07512900010034456400b98110f6a4844a9128408d11000030300c40c66a009051162180c01031440c0400001108000442168041c03061007210501d00340c00c000504c09103900021007113407404d90801c090a00d40d0002c0c81588085031050030b10704820700b071203410860b903850030b41c11041c45800c4540c05d008036100c800003290100c1e98440c00000031448000003811240450783c61030740800071b40d1980c0481c00355055004081c400c1581d2100114414010008900d08500b100c1141c1008840c001041d030728501400c403450380c1c81c81481101c0c681405640700300c2c00e032110002140801d80c4502000e225010780b004580490b840c0841d212070031442c150300000e01001c4c001d0300c00b508a80719255107055844d0500e43d0641003a401609100304105000e200d001c0710b50544054401618954021030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 668143111 1250 668141861 668141891
    0x3110714060a110a0503040c03080f0706051506040e042105070c0b09010503130606031e020301060e131b0e0f0411030f030a0e010c0c1706090609060708090f010e0c04 73
    0x4030440b0f058400b4141090488441a00e060780041c0096a40110742d0b0340003c0010241c070001c00f5070b0b00d000104e441e221200c40c80e1003400e481016280102c01012140b0300724040e1119000d5174211083c0c0700304210580c50340e050010690f0b62a400a206190f407140c0d45003c166000b100030310712070340b203000c00c108099500c9410f28103034010420b42d10300140702007000c121003489601041030703d2801040006910340d41d981e00d03055501c003920a101005c0b01900c2c0101305520302841107100409a1011f280042d2a0610407801d40d00f4000000920030004500004110040151508054806441c50f410a420304240e004550b180880d0101c071300228140031910141070120f03507a0780058403000190304001c2c5171369064580c180c5245415040112288105000c9801e03900303280000c141e100501c0f00b0700c0780c1e0801a2420a14014a0264290320480a1180110000454030703404001480c02ca0742d183c031041d25403810300a07501000c803078039820030400d03003442100030400c2450342c481110300300300d22040c2028003 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 668144361 1250 668143111 668143121
    0x50a02030f1510140c070f080f3408120d05160e130b040603140105011203080105130608060a05060906101409191d100b030406090303110714060a 64
    0x110b07007100c410311841c59500e00810f1130004000c00c2c3e02e05503080050b861140ca281243d0f030f074002c40d100303042c0c441e08200440c2d003030002c000701c00d1000005e00308486024094003c081501c40700d40100b01849000c4514042ca001c80c000003a1450703409443c0e044005048000c00d07900403518a618003031514021800c500e142c02e0101d031054079181c40f25000110b807041040342c98005280e5140555443d02c14500080c0e40714032402004d90710544055a042c010700650343e084a50580100c4000c5141007411001319030449091030444134111011050b981e081c01c81000505016440443d89101e05024420784000c5600074500c102c0c0141d030425041e035a180204400000e116080201180b80c44900b90f8003210f400740100b41450300030b0007240420580b80c90281c8010443d0b80264075283c481c0b1480c0340c03a4031050716020f400840c11111031079843e09000011010344000350006100c155207440b8141014080d400a2015442e80c4140319141c4403c0c0c1421401c081502050203401c0c01454009811401c29104d8 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 668145611 1250 668144361 668144401
    0xf030703090b060f0f19120c1a0c120d02092d100f08090109020613060305240105030a242d0e09071a04140d11040903030e01050a02030f 60
    0x41c643d854916405000c5020f1980006c00e0300d407038030402c01146e42c8a5982403087c00d01d1158003c01c1c561441d040b007100a501200c0b6809480180402a035032070080700280d00310f800f081080407941c0c0c400641d06070400038490054501d130040301c4031044003038034500c0310564a018041c10307000b00d00000c404e08c02c0001e00a04004400080360104440503205445000090750085203000001105005900010a5500450700f81000c038184200d00b401401d50502403260000d611890303010400100c801c4031401e105203441284c0c100140400020040300454003c4007071300d0a001c917410507140b884180c80c194034080f40141a1040c030304d510701d01c000124a103180b016540e1405ca0052819040507043c1c0d00d01c42024013040301a206000300421034080701044200300c42c140d6454030340e0b5103143c8051002c40307410070180c2a21480c0e209151102042644840444441c0101c6000070084141e190907801070000c0d80000119611b000100b0007035800940c011401440e1411140030f10b581c5200000c081c44000e028 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 668146861 1250 668145611 668145619
    0x50d061505090f04050408041202060d0e1f150510180303030c0f08100306091703070302091c12050c0a1e03031104080a110402070f230f031e0f030703090b060f 70
    0x4100312700103603008010007403005054918003a00d00403a28103444841410703450035000355100d03012101132040184088600c40e00c05106d40e5681c2440e0104003e0180b02d41400342c41c14a4072088080d102d030042e030825014600d4080782050301c0e03050080007002d6420855001c24111540c0100f500c0c002d005141c0700f59200d42c909001c1c24219582c91018100220f0103d41d0582445807001c00484a20040d41c4a441c03a6500143c4450042c82006008080780d000075034004140c52442c004035461400f103403840c1000c4d081c00356882d40d40011803441e01f000840044c140d5a400020301c11403041d410102600d460090342c007800713030418800d4400903a05c2644038180c0254400c4084000203201501e41c0004954020801400c1c5800d40d1200c080078294403004a8038104440101c541c1c2402c0480e107083e4a0a1440c01000c4149032500d0702c44d0740f0b101c4d00c490005612140c01d00c0b003038a6001d4808898038102045100e03034482c100300310003a020300610001129495000350001c0e90714108000402d48c80d0600030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 668148111 1250 668146861 668146867
    0x4020a0f08060a020c160b0702030c1f2d0507051005010f060e010504030c0e0406051b042112110118020d030509042c060f060a0303050d061505090f04050408 69
    0x2140300009600a000341192405800c444c5042d401b510803c0600408111000388da6455491042500344030404140c10700c1031190480302e1001100072040c08000c4070490812608a01540907040150f862080d0517440001c00d64001000e09035221000e4040c0340d00c90f408444800840c920b07010103a0350700f401075003e929004a01004081c2c407407605200c8031071060420526054507920f407000c92185640009048020900902c0200b00c100d1203159840b248801010001d059218a503410034408c91003017201d000e5a8131100c080d104000841387e1030705030b4081e01740551051f21031009804500090300310140795203011803031680600c0301c10400503055402002401d00c2803656500392407542201e0320881d003007603030342a02c0500e403a041c08001051850380041100185031544076a0301e000b0000f40204081c4c8295170501820751902c07914032003565814100241c44145103643c900050015034403408841e00d10071140350005030040b00421450700d05513000c00741040003209000c1a0380007501c0090002a0130 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 668149361 1250 668148111 668148121
    0xa091d190b040c20060c030a0c12231e0109020f0d151a0903100b15040609050a0e040b010b0c0a02040504080a03060e01060c11130e0604020a0f0806 65
    0xe96401800340c40550300025100c400e11010400300d030315500c0c4400c04036400c1e000b00e607048003440158642d0700070880f004261501c0c1015401080f0700015080c0e0152a80b0341001100c9240145428190502020000c000d5010300380841d4915860310743d043d8850700b9542d07011500e00005203082d004400f60f00c0d03105000c140d01c0c1191000c0294401100c04140301000e1000b0403005486010f840c214140e459600002c0300e00740380025080506080054208060400c0790700d8040e10003081c410015448503000090280950001c1003e443c8170008550f0407510008020410035002042c0a05484040d206a100b00703465550710307d030100c019207000c0c03e0f04070a0001081440000c4009001b000941015507407000d010343e01040c295141070b40c04680d4440081840c0004a0340342c8201802001c8031381e0234440951601101814181c0164005880c11403d02e0f05066541c50b0384005010303e44019508006070221f001100381c84c1c0c1000d68080348a001103807000540344099404150589000030b0240c4180d8840d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 668150611 1250 668149361 668149381
    0x4031a011a0d0905190b28020f090901171507080f04020a0510020c09070f0c110a050604170c0a050312130305060108070311010c08030403110708070b0a091d 69
    0x1408020034aa44071402940061824440c06000d17500d60000049155100d1400b58040803006040507100c0b020b98454000842c589020341840e0580000d005940c1c00c40c0001c240c94600c20041500d80040a1400003d05940c0c048140e82400074410151402032074072580042e03e8074800c1d685c41000440140c04174002c11010303900650040d00c02000701c40c085d41d83d2004101c001e00e0403038000000d6040780000741214104000d28030780c08085844c148e00c42d2220044040c2c0013517800c00014150f410440c000502c99191040c0d544080c007001820183c40742c0e1f682d40b24100d00f072180c401e4911f041c0030b03140742d880442c1400c8000b00241c0301d00401504914041d0300300b0351500d4001c550503415030320f0000f60000105205200c1980030b0442e68024011090950074414000d0140c154042d04103c001c000e0741020800540036641c0003981407034564850020254440d240051036004982c46015000380090417181d014001d100c1c00135a6110300309415903480424100201c0341c01c04010300c400c580002040451 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 668151861 1250 668150611 668150617
    0x27120e01090302092a040509010e01030f170c07030b070e04060b030115020c0d050c10090614030411030f07061b08030a050c04030b1608090f0c1c1704031a011a 70
    0x11003054015080d02d0755410200e18260410740003000b17400700150510aa082c54400c1e41d0151410b04c00c4070441c2d504d161b0703e039400800c2446c1d01400c06c1d600342019158580c0480222601e8004c0c2030121010503441e81420310603000190340d04000305107500c900c00c0050409008400c115168001001c1c1940c0c41c1c449800030071500341087c0c8045000e030f210480781d299140c80050308104e01800007000180031507070501001c00b0f40400d510042c00a80c1c0c0c0b00701301d142c0c2c2c424003001c0149101003215032262100d1400100070000d0900c80c0f40c2c14010741ca24000b1708030001411100b102c14540c1d03510281c591544080c1c241071000e58018051280c1040011041c03411070f0049500070054400a41c40c1c19600d884a418101d81580c4088440c00c52034a081519540b04c3d4200d6000b4540501606000500c5285695503580840703141d4001c0440f074404111030050801d8101e4501e4106140060f401101c0f04a80050361107404101d070184403001c01d603007400c50700c4610f0a041e9008800e86120903080404007102c290 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 668153111 1250 668151861 668151871
    0x310170a11031f05070e090c0403060b180f070f0e0603041b1a190815150c0d0302190509030703031805120a030201061a0d020d27120e0109030209 64
    0x4030400f148001c100115041c040403025606000048038246010700410000030455828440c941910a000464001e4411201100d40c00440091143d0604000c1441245c07161034100301507010604104a1959000c891445800141d41c0c01c2d5820a1021003034454150802555401c101e00f0710000300010f114550014003100403119045031960358001201360360014002c00a003004e00811403604084a500c4848245800c80c00c2060b940c1c0f614600418501c2066141e0078072800504044203000700c603500407501048910000d40e4108084500c016021354825182a26200201d006440400b4401c1054600c8050014003400c140ea242d038900321111607114021001c40c02010100180a56a80e011080c901500e00301601c031400301800c010703085414035404444107040040e1510300e001101c2d01141c1709004144401616001c815048070010406408255220391018083d070040b5981146820f40c5c03c3e110384501d040803101104204c0b81280711120407400300e178034030000340010302c1d0404a0075808 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 668154361 1250 668153111 668153113
    0x706030f0906020406092c040816080406090f0b030702030313150f0f0f050603250801090f17120a09020d0c092c250312050310170a1103 60
    0x4412180c0b0707010200e82c801e40c00715004c980c1944007005488411800f040c50f010724164198902c0c0c0300407910900e54480104010460140010444800160f040d8840346141d0046c03086a01ca91b00c80d10090030300308207406a042d9040030140d002601e10540e0003128400c0301c603580a9815030301c0d00c904da0000003181d03010480b81d401a11030030700e21802c00c40c4503400f040504002c0110f425040c52840d002250003078a2410f40c0142450204840c54800103000701012010700c2040301c2600c0307194040c040560103600520425402c00c0f480b1018401c40b58800304d809406600c1c1e600b9101e070050303103440c420303c01c0481110418411100041c0100002c1d4803400c030280c00500016000581982c0d00e501c8980c55070450b40840e40d4036000b015134046201c0c18500007008241c81605205503101c000c82e41ca144105049003600d4a030301e080106072800009010040d07a0040c500000240000d0000d01250070032605c003100754440d400c0000307101d043e1441c140001100d910141c1000555510b0303001c50412070f00354583d01 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 668155611 1250 668154361 668154371
    0x80403020a06050c040501080c13051e1503060306060907210f050f09101512050c0d032d0503040201030c0525020916050d09050c0909010c0e030f0706030f 68
    0x4590316010b12880f40302850f51300341d516030400700050f000c0003020341260748040040c845a450822000451810354404032035525040010310a69410382001c0f40d451074001203124000c10700442404003941c0152406c1b81a01c2d610341d504004d110710300e441207030100e0004440d01c50502e2511103c802c909110040c0c40d030701080c400300301130300b810a80300240e808140d00f6080104100b6008002d02c40b2240c1075800c0c43c000d100003462828409280312407030081e1510003800008880400c0001c00c1010351207031000d80940c90b803c155090142003810341d07241004200914900c4120703810404100030b403003004a07482e00d9040d0303107850300110300070801240d190050200400c00f010208481d420048010840503001c0040800707580305200820308042c0400a000005e401c0f8001120b401a041e104086600c08001620020030f007015031401c4420309640342c1140c0c4d40d40c00c2c8440309e41c040d001508403904a4860403624010070080c16619520224041450f40001505100c0d440c400c0c3c1000c0d049040019010078 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 668156861 1250 668155611 668155613
    0x307061b06140f10180218301603060e0a02090c040f09060501080412020a0221161a07030e090a1415010c110105160c0f0806060f01080403020a 63
    0x41162607405645040000b2501088001031a141c202d652125950300c41c0c00d5000d2421031004900c14003a5203c04513181c003c00c8501e47c00e15040f00c0350540c92001000303588055030700b44040544066a41014500b840c040d01206010702c000510510710451071030610342c8140c6180ca99900509001c2c004111070300903110010701690b184941d0340d0180c190312811680d21490881c0d61005050b040d8400031025040c50001c10071aa040480950b115400034003a0101e2061003200b01d007813503100d14000b54040784460000007094514100701c0844255601142d0101c580384004070702403183c912400c0034000203100c01c40080340c0000302418180d44640ed02003410403007000016a1080111030040c00513582d038517000c0c84500030300341080c0c00a2001c000703c3c000c1c646c1d16000230281c0c03080d0180605050459040403a85921980465a00c0803041ca008886a1414a8181440341e03661103440080b011911000c290524003050190090340c00030f01d04560040ea000043d110cc82c0e004009a05500408200b28 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 668158111 1250 668156861 668156873
    0xf0a0603081606140a052e0b1b070915170a080d1d0a111915140703230f2d0307020d02071a03040605060f0d03050d060605090307061b 59
    0x540240c4c01c04e0305c007142074a85900c500000c1e400b0301c00c86160301c00c0c944440d40d2450b4641c3c83e42800b44c1f80305040b9140d8030410031012913620010b8107203161091090100004002e503566001070148008004040c3341942c0e103013030300e001c1e64441c5a00b030310143c0c20900651b000240405c0040c8525041610042141c030f00c1c5810000c054802c0400c100c1c1c4e03580040c110b01f000c00410709031094000d4011078440da03200c0c40f15800401040341d1405052100c07415050080c25040c0074803125141c07000800090742e03403080d00f460010004010304450301c2c120902d003401504100405020303503488a4540041900b032000c1b60042a0180c2c150000b180043c05e00d00d4020505c100c0072400031803040101d600103140c41011a040246018007da004800d0040c4c4501c0807a80800e00b03108907600580c0100c004600c1d0784550000402d01190128025171012540d0340303250800d07070444040c18070111200c0080280725560300043c2c91078820302a07419415007003000d00f400201e0180d000400320b100c03403500350355040c40641c2c5e80d4 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 668159361 1250 668158111 668158151
    0x20108161b02120f011a03060403170a02041211010f0503090c190806011d010501080f041101030b0603240a1203050705210d0c0309080d0905030702040606080f0a0603081606 76
    0x1e0b04c441c0e51100242c0000f400c00954002c45541c2c1540140828a03282e00c008003850900621054a1844100400c102c001340e5011740703014003291038480381401c440c1d141174002051a40700150200b80e0032030078032600502401c1079910400155002e40007041842c402c000303c0007100f031400b181903031610201240d10f000c10000e89010308140b20109840701c4004a1400c1003501c164400ca0410090a041141c800000d4821f1030300194402c00300c818100b81940140c024200b40d99415410510110030003050300d090023a0385c0e613455444500520300940007414000750342d10b54003810000c0c124186004000900c500700412070203005109403190401813105a0b1000e0400d262400d0700d480c0d01290280312001503200780c0e5040d05140c00d0030040307441150303203010242c01340c1c00b24a8000c07556000100c0c18480103004036100294018000c004983e10b610020b040d40743e00b56140000c0444c8d99002a40e00300c03049c46a203090301e811601d12801c0c4038090f00703511252401c008086445680394204140344821910907 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 668160611 1250 668159361 668159383
    0x306010b0d11130602120403020319053d050c1603092318070903060c11011812050a08010e25020706080705070804051e031009020108161b0212 63
    0xf055512850450001d1501440f5020302e1106101000304000607070740080c01c8248510084001c000c280702504140303090914082171900103022008040003d0004446a0340c0300c032a0100301407040c3c040a4069800320b5900705e600ba81540000c1003440c071180d1401c02d00051180c0300349000340c1d4060b12054000e880c1d4600e005c0780780d55004020a400610300d011041915024115103840c6203920f01808000c00c84080d83c80081d000030b40d1090b80e079020714070402140040c0c01c0444001c0c01a0000f42115407c4124072002c00d940c4080c2c50a000500f2071310400450714007400c19642c01186909201c860394190300302034441c1d8045103005845a0043c140110a407141d010540c02800007a0300e01600900301860041c029070410804001d9100010174050540b0151041a01d40c81d07010b6010400c041040c1c80c1e0f045032282e15100307012140000084940010907a180300b030740c801d05288c40700904134080440d407130101c001040d0100019070400022100c1c8181d82c50005105c0d401420042c5245c50034140c007045 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 668161861 1250 668160611 668160637
    0xc0c03071404110c032b02041403060c0403051c0c0b07030510060e010909020c10020310080d1d0f13020c01021e040605030f0a0603081204020f0d020306010b0d11 71
    0x48101d0142c98944a070b441d041e00c11115051500c45201c001680b0b0348542000b030041c28890740741060107401029100c010700c28100c1d034115640c40c1c451086407480f10b0301c000d040c0d11034818140083c0344010b120050b602200d03030010003081d5078415608164000e01c1c04002078410413035004001004a2044081340340500300540b070018103402c1400c00b0384a41e012a420100511002ca184500581d134091012002c42c4d02c040c00c0107031904180b11605040035100041d1703040c00d038004003e0144580c3c15000c240100c0d0005022502c011003140e9042d1130014881e03400b460f00124544001d0040e0900001440c1d178507030010a1880e11000400001d400c030b8100c0050080d00d1b03907010885001c10362910004c0a076030708090240d03a04061034444010114400104189907406035840843c010402c103820075800b5545c030484061303d8483d41000d811034032400302da099119000413030303620166003400c8515100a68010f8060541a030800802074001c0d400080080e510716030b034810200449290f03402a241c8025040 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 668163111 1250 668161861 668161889
    0x70f020108070e0102070b070c081b010207060206040b0a0c030f2a0203070822210303050f0f01050909101802032406011d040c02070303031506090302060c0c0307 71
    0x40001420003600038400030a21080030b0f0f0104403030b030700028036608580840d40030642e2500c05103030002c00082c1581c4000c4162003071010b50740c49617066445d1205c04072402c1e822161242d50742d281c120703034485050310302600c180c1509011540003000c642044000e4141420080b44d400c024929007070407103c10056000002361000c81108101c1380c0076034039021182c0d46200542c00d00446031078025240c860742025002c40312080868104c800c5503100040010300704203400c80d001001102da130642800004004400003868000094091141c9046240c000c40381c0c00003007280f50f82080309204048030081d00150491042150b201401d0301540224030f01200d41c00034801c41c40845205041c03030f000030440304032486000e130703500700000c0e0886040c810ba00c40801d180c0300010080381c028504880c030084070032540160429102c0c14000c2d40001d18082101e00c00da4040006403d0074400707180088090081c0b10014820715410001b40c40c0c910050140c80c1520803c3d51001030030240007038070341191a132013044800e10714 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 668164361 1250 668163111 668163113
    0x506030601060203040e0a24080304060905040207080d0c0e0402070c03050105010503010e25030f121d0d0f0809061b19020a12050106090f09060b1806011b0206070f 72
    0x601280e801400b0a000960030982840c5150384600401030084d100ca42e0340320351700c0441c0b184204c100c40109400320102c808031900c9021281d1264481d000f4100400d001d41400101c81c10705208803180f160304402d0190500c56915252005091030044050070841104105401c0307554500c002c1c98007501c181d16001840c0e00c2c42c90700500b56031059100ba88640d24104460102c071101199840c400b0303102c01062203481e24016810140e01440f0f0f0000b0b0020719080104504010607c0040b50074000e0a407070f207840c042060445440346100340c0700501c1c2c00c14400e83d01c4200013001c03941c050080e14840e50102d410001c05002144c069000800c54011604100715603422504080c4403030781c43c82406211070029041300341c01107a103882e060f1003000603003d808189103042c803500398807150140030f50580070f01c9840c40303055900c00542040700094605900e04288408249002103101d104003000c1030340b07840f20b5603c901c01952503149000006044a00143e800c00060790f8017030042144c4d9200300c20341c100348140713 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 668165467 1106 668164361 668164363
    0xa05071e12030f050f040210030f0204150e1306080a021309050a0c0501020c040501030506060609060409020c03030f15090f070509040929100b1806030a050603 70
    0x100d4103020344602d502d50001c000d6141d00c0034060040c0c0c2c03140880f00c98032000030b6030001d6110003034052150085010342c01c01000189602d00050a2642e5a00304840c420301d2503607044000b030b01840c41100e0350b144c40f01d03040c2c130880d0f00400c04218941c14025a0350b55058010000303031007089010005a10308499400030441a85e00c10196611b500036883c100249203a2030080d94003500983d00420303200e080601c921412070b50444010642521f8000c14440b15034010f20f43c02e60000410400807507060a103000810741c0e200c64900442c3d40b8a0844805000380001505450f40000903076a13601030381d5a1141301c19002a0000b02c500040c0e00c4805003681d0f036100d03041000c0c0c2c0050a000610050149a4244015000a641603070b941c00c1c05034505450011003c9406003414503a295060042e40c41c91405081e40714951f00501042c2e43c0030300c0c005031b240d8104403882d00009448504008407410 = true := by decide +kernel

theorem cover : BRFrame.Cov 667985611 668165467 := by
  have h0 := BRFrame.cov_init 667985611
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 667985611 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 667985611 ≤ n) (h2 : n < 668165467) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
