-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0086
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:45:21.068984+00:00
-- url     : https://prove2.me/submissions/51ec3980-b3ba-4409-8743-aa5738bea972

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 15287776 ≤ n < 15467632 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 15289026 1250 15287776 15287809
    0x90602120712060e010e0403020f0f070e0a05040b040f02010306050301020d090209060906010503040303020c16060806040506061c020705010f0513030905010c12030f0b040501060201061a030912030a090209010f05 93
    0x1400800c001c0c44e0680700c903039411100700c17404c815410745545c20200d0415000004d000c60b80d2246030301041c0011000140403013120b1070a50f6004035501c0d0140e00c2030550b40705650140501044401050100f00002801c03c0880d00c14100000d059a45030302080c01da0b0003800b60362466a075a0410801503040a9510701c2d440b0404841174140307443d10000191041c00082d002804155000c902199524401c0140f40421000107446400315075032020000c0c8015022101c50340910f04240103d249400d00405480c013240c64a100c2000f4070044100000003034000c8402a601d941d21055151809407291081d240189040c58964120401605020b480300c0c41aa00c043e040064400d40c1d40040f86003c04441c01900c1075103004942c14000c2c6542d417016110701c2c03019a52251524000040b40c68055000d0b00450381803080701c4018035014000031041c0d01040f0b603410072070781001382d07141c0c14100d10400540c3d11000d0a00000340b00746458012922481e026001510054503010050006281504924150b142d0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 15290276 1250 15289026 15289031
    0x31507050703050c0109050a140f010c0e06090f0603010314060c070309030b0414010f020a0e1f180e01060504061403072001060306020c030403031808031804090602120712 75
    0x142848018814400c40c0c0001d4100072020032800b9000d0380a42198500c0340c0c224045801454403410101c200d03581c01c010010311441034210640c059141800707061031050003a110003202c04a00b0050004235400b8003030444d8010b048058402555070303507102440c06140100d000103012586a040145000300281c42034180c40d2091024800180d0f00c0380e00482543c0d48515403a40540310ba01c1c1c00c40e0194403003400c1d203210354200030010b19002c51507805001c030306417690f4070340480d5031054040c021700401c00700088138194130440c61200390b54052307101d140e1441c0c80f20b40d04040b0180c0e1500030b01c21400081e0000b03000903400003401c1000076030040e000401030000c5410540780d030903e10301c047c0018118014190a00c8040e0802d41c8909400390b001900454029100f9541c41d52901d06c49900c0b03a0060100310081505004444041c041614000d010b40d95001c000314540302409c0310340d446090003204e40f0756001d038036417003041c0004009001030701701416540c2911956041801d0080c002000d03d00c80b4011962 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 15291526 1250 15290276 15290281
    0xb04030b01030807020103020d0203041103061b070605060303040503100e0d0504080c1509030115170d080a050a06030807060903030f0b031513062d0b01141303120e0315 74
    0x11200a6001d04490340410070544d90096440107070040e000708814428600e20110421061114442c0c1c184084001201600c00a540f07a80d4010521240450b801d07403102d505105260004105600172034014078002c1c200c0b4249955140042e19180701e050f091083c0c641c5400c484c1030203a0303080024407940c0600d82801400c0034145a41e0540d03500607501c200b845505440d0329080d0940d915401c41300441000b600910030246c4006d418055881030b803040b00b01d484402d04c0c00728011500414525070710b50690386c840036030b46ca50600b410007401001d4079811015907103400c00000907091000400007244940d40105000e9110300300034040b108440e1112004038200100c074070072540d01041c140b152110202c8200e0320b94031656a00e40070441d441800800d81c40c980701d0050140860883c05200c005c10100141515081e0700540a050300c9600c0d10f4107012600400520b5074580c0c115001e01a010a0340c24810075095407502d03a205850002c200020105008038000f01c06d6090602035108190fa0070910308041c0d0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 15292776 1250 15291526 15291533
    0x605040902011407030315170c040c08011e09090b06030c0a050a0b0f1e04080607020c03060c030402010309150b0111010b0a03060e0f0102040308090f0d1101030213090501031505010b0403 82
    0x9900b4a00ba0074401c1c0d0f8005611410540250311000d040720701c042140c43d5890326081a0402d00a060201c2c461a01c1420094122391070140111005102244e88556003a4a05540d03156415a900c8060b820139494117000300d1005114031605c25094041c21524485050010a1600344403000c0903a6014030001c1c0024866502c42581d0722044a120282981d41c070701d00c01c03225a0043c02240c6011441c0e10b9070700119000303280e250700075209442c0c85006448058032030140907681d814095002e150950000400200a100c60b03d0240d90711a00604000c5040071003542d4051500140c44c42c110001503440c0e080c210107580c0f00400b040d5403000a00200180d1200e040040d05404140c4001004580c507208909513003e01880307102c080c465420029900ea907100d06d8000380317940182548600410303c2c5880040e03a803401c400201e400703d4001d81c2140fa0028200700440c060740c085040c5034141e550b000000207845086e8441d8500850140032058a0300b24881002025210103070f00c03030018513105000c02d0010 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 15294026 1250 15292776 15292787
    0x906010c0c06050903030403020301021201090b010c05060c0307110105160207061106061e100201090201120605060319061203020a1502030f0c070501110a05090406090203010605090409060b060c10060504090201 92
    0x20b6a400303042070b035100c1c818000082c4c0b85208a0304025055400841d461000102610b046070582e07407170440a0016100400045030819550b8101400b140d10117004103d801c82044000d41d044422445d00292017444d081009081d1441562200c244100c03424000341d41e5075041c002c00024050f10700c1d01c80066040c0300340d40e550f10507014220303038803540d0500c40d0000b07601e108172000d042841000d40000b000c09001d0901a00030404484164086495001600303029500da101d03902c15102d00410407400c0d03845039441e01283c01c0318a22815541c0360381c1e6001040081180d64074044040c0300b5802054410801e00d03104050080b42d640c205021401402881422413a0000e0745501003846144d458035164241801400340007141400c00e6a0400041d030400d8040c1c0c84070003010400e86c151424000d05590b2040c176001c80c4400d1066400045007445110b2540c41d1a40021400c140141000700710803020310006449a8002451410f80c0c2e84091100c0c0c1e00c000d081e0084100911046800300901162900081c00 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 15295276 1250 15294026 15294029
    0x1902090f090c0c01090c080d0203090d030807030e010e030406111606050c1c03050411030601030b070c020f0a09020903150705121906090f0b060f070809030a0f050604020906010c0c 79
    0x2103680d80c08001521407650b4810740d241012000d00a028085060820000320b0825005030101f500411043c05041400041105c402c002c014180041030051902d045804817000f030300440800d900d41840e0101d260b02400b501c1122950039014580c0c5600e0000050b04144c00742d50040e1564101d1003c1901000b84003130030b5412101d050800540d40c1c249c0d4032440741011442e000c100c0301c10310310780e001c0798201d541907000d144203e210b0713070701c00911302080c90030181d6a4501340b1004141d2600300001408282c8124000e40d1410300c06490300e0f00e203e141744009034400c402504a0342c40c443e03004c10b00c1c84180c0340401016603000700302044544681014040240140b1030100c141c000216610003041285202c800725200040d001401004003e4540c20401e02401c40c40789005001410b0051110351441c01204480f6030801c8400c0f4146006110340d1001095003055a00c41ea040c0624103507240410150242c06203aa4450009408249050b00c1007100050307000c0c0038681081501e1400701d0010b84000503000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 15296526 1250 15295276 15295279
    0x8010b0a03020a0c081206010806040203040c0b0f090303030a0221090c040510030b0f0604050106030204050a1203020c190905100b030f060a0f0303120b0603040312020a05040b040308031902090f 85
    0x140c3e039101c0002e042d6902d980c1144020a02e04c0006946082801000c2010340900b400b41d0f1041842e8445000300406e80c0420307603018044c0240241e00b00100d0030349500810704130710740303040960030301c0d850388006801c3d07401c01c841486902e0b400062150313400100100ca00100b01d2111014006c0e07042c03101059a03a881041aaa03005075074800101b489600840300410040d0744c0a1001c0340c0b03d19244480c00c4143c0e00940380c082c0a80e090400100e1000d00a0080d901030303030400741000f1a0780740b925080402100c10a07600380c0c294003e0b2554050241c0780d00e52801c80d184a500c080c081c0c62441c240802d02120b0740101090803600080205000c2c2010301003c9075045401070716444e004c0d0311440005810031035540d101a000301e07111b107000001c0603080040e003030004101400402c800c0c050f900501200c1c0c402120300600140608a0f800e910891076805440c01c00d513540f07400d0f41400c2e1521825907155006800c00d90754414040308002d00c441501e110304901c0c02e07940d0002d6091003011004182020780308215107 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 15297776 1250 15296526 15296531
    0x301020f03040b251d090105010c0b040206070c0609031208070909050a0b0402031e0a050402060714120708190315050d06020903033103020a06030e010209040c0806010f08010b0a03 79
    0xc0a42d202d40004c00c50300360100c5000010603e01c504c3c043e00c0425603551380030700b0312880c0310040ea176440c01c444603d0407660180c589000c90000c0b0350724250340b6400280102d9200c00c09206900100d8114041e040c080c7c0703540d071076184441c1d085017054000807500310803074401c21141d0801c106040754002c104400329001080f010425807289900384014090210780c02d40c210384040208501c00081c01a540c0c401c031265013603a0381c180c0b1010b21490980e03508440203500b1810401007030000448004401c0c00144102c0103a81100c0c0c600c1ca49112945d02200c0c0a880303d000c00309404c01e0203540720001101541442c142040111741c0a490842c10841c2c0c3d102c2d45100f4105106540d05000070354040f101100c6000b0140c80d9910f0202158008102d01c4040d120b0844101c2c3d005010b0b080b05c00380800c0166a001002202c045d8a40141100035001038980030b0360075502406282c1c03aa44441c056044840704580b1200d80342d241420004106400d0740c08001c04100041c40100480b8800004030b840e001c90f070b032802 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 15299026 1250 15297776 15297781
    0xd0506040905010f060f090204050d02090702070f0e040201090b1206060d020f030a060801060e041e17070302010501030512070c0302101701180b040c020312100f060809010b0301020f03040b 83
    0x1400070205164007074070350750070314240b8002c540700c0340d00020507104446207200391140c40300c91000c1240241d000d01c0e41c21080c41c01600001d86406002140e0200b040c6c8100c0300800c2e142d2000064003074550f80480010544082840210340e000002d407005800d0404000781020781d940c00740e036401000500183c0c050000064814001591a01105c000761300d58490f00780d8034108025140024840741c07241200300d510b04035002c00c4c000e80100600340a1a00b02e80b800c141c405840850130b0781e00050f17000450f81c8001082a6184079000b800181c031035240030b6000000c03698518105075041c0141c8006150300c2c41010400f0b000000c95820300b030015241c05031004e403001c041d2290150341c1101c18242a80c02c41ca2407400011b01003a00401270301e50001d01000503c40401c003603091200743c1d03d8050400300507803c184400b44068203135030422640102190030000255644808810461440f900174600003540c4808200590800340603000038284203400841c545506605041340600001d0802020350442501 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 15300276 1250 15299026 15299029
    0x40201020c120715020708010608010203090a03050310090e030318010c050a051c0204080715090b0409050402030a0210051b0303040206030103030f030902040f06031104151403120c0706021509030d0506 88
    0x268000b44c0031070183e010b089405207101969a011510860f2038540c01c04202003080b14040c0250303030156071020024640d401890743c059480b0b030001042102440203807400042c1c020218000c2820b01500d000103140d0741e0034401d0044d000e0740c0c60380101d0b4085070704003c032038581d040e03105040f54071101e010318003540c0302d840d600c4821188400a22808580030300120340460110004244c8108403403001072445040710500000b81c0300c50080f40315088202c0c0d400d001c1008900749981059602610080984100c80d405030700144048100c0c2c01d90900164002c00c0703115201c05c00c680f550049007580c0008600f14905503001441354031050000408210824138903020300c2d40030f0f4010f0a45603900a10038007845440c00004001401130303100503614000303500014a460700b07082c070842040e00340d000c0d164842070381080712941071044c1c0006141e400d4410b6081414170700895402800c0e07101060006480c405107000703002494280012004e4075814800001e0000125000040f2003110700c2c008804140d940d1042d0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 15301526 1250 15300276 15300283
    0x30607051602180405030408070f0608010302040e0f0607050310050a0b0a03150f1206050723090a180b010201060e0708040201200109150507020a02010215180304080703020414040201020c12 83
    0xba50031043c0300c540b001c2c001000340204c00303070064503034900407034040070764074640440541ca06214540202e402c50005101504140e001640c86108560449210f8504d5404580c80c00c801101d004001800100500c0546e0f41e1504a9600403c401c4a540214500b040d4102c10540302d0072411106066840f5501100300b40285401d4000313103805c5406d1480f0b1541c400034800d95200c5402c046403880e2a15000541e16401280c5000301e0002c5080d04d1950f0b141030300a1f070641a4007803a003003603108100040020b0002d43c44d111000c0041c2000707a000c200209100006802d40c2d804d5042402c0c02c1200400f044041c03644250100d9105409280c4a00c000900840c1e1052008040c40c1e169040e500b080400c400f40a800441142c030f4440e40001080140e540100c1240c6408082500030300682102c5248481c0071441641d080c0c000003030480d1146d41c2c40303840c6c210501c1c5034020303800001c1d25004100100309514007403207004000394162001041614155000030b40300d03055414054890390080004460100d03040 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 15302776 1250 15301526 15301549
    0x30a0203150603040b04050705040908030a0c03060503120702041b120218040c0c050d090602070e06040209040207050609060105040209060f0d0905030c010608060a1112090c0904030c11030607051602 87
    0x5000c2d15584e081a06044c8083c0c0c0c021034081d203c0d84108d8100094904181c802d00001c0d81e04070074000e046840318141900030b4451498420201070700d403440403038242d4080c000724400402174485c0390780e50025841032100742c0c0c650940c50040c4d800c041c40000e11807500003d51120840300c4d6200140c1d03c2c01400f240040b404003043c4119082403601c0c08081c10290040c0140c880c0c180100d04460061210342e500f100c4d00b0080e40510741c01a0809030701000f00c0e00760311b010250003000041c00941000300c0c11000c0360898012900c02d444992001e014800c443d0780c00d1112a000d84003d540a51602100b00c000c02c41901c12034540d03242584000900400351f80107644480303c0c0c0f0764410300780c03035542ca064084035020704124020341603a03018400110760140e0079403103001f010480b6180c515050106103210038044040040407448a406034a8220219644a45149106600c41d0310f82902544181c10100c1c01404003045081c002e0b8414030038091025000070540f08001402c3d0040340280901e84081100840311 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 15304026 1250 15302776 15302779
    0x10209011e12020a0c1401090203120a091d0103030801060221210115110105060904030e0102030d060f0e06060703171305010216020f01020a1109040311030a0306090b010306050303030a020315 84
    0x8a0340f9141c1303d034009940d1100ca40150401204400004400303801c90b0201c0360003c2d4141e05c881c004520b02c15407200a0012143c0d00c0c11322400d101e50300e0500c06d00d203d65020100d110381a1100041c01015000000d007405002c161000703000c00107043c040141e01c44034100b50300d454007074042400910800080c40c0c40003500c5440b8030ba50303c0b82d41e480c00c0c00c0507012840102400400da003151031600a140511495100300e0000380015016100c0340c0301030310040228150f00e411408100075421030003004e070060301700800040d28200d18181c03800d910300b410280060425840307850f00f080b90002181d80b001003081580a0f8088408094540c44103d40d0780e002c1250005109500200b21010044030846042007032a000303444000c40007079004d004a8440c131480000400c000351021155a907410204107280d80244039007081208000d0009074075255030080ca841038002502e4901c00d109d851a24007a00710720810a08007403004505002c0080c0e01c80c0401002c04c840d0982c01710000341da00d200e0010280d21020b0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 15305276 1250 15304026 15304031
    0x3030c1112010b03010f020f0702040e0106170309010e060c0a0b06030115090b09100305060f06040207060624030e030d020f0d050c030703290f041d0c0909010209011e12 74
    0x1101c6000d40648a5203400e0f5200b54a406601c5490749114000c80d05500b80c3c00018500e008083c1d0b0811000b4921041000001e40d80d40e0001704400b4010030405021540e40f030000d685a1510704c0004040b01d502d03013011030203004240948600c00c400011403249240d03114290300020b980382000b0900410908552600c0400360010004140c4401d070f02210000e0b801f510b12403100c2e03540d0b01110b007210025101c020042da01c1040040d00f02040800c1c0b0507080040104058900822a00c40c20107541e015044201003101640340f0f00c0e540038140500902c2c3c90b52030b0401348110691910b50303a40701e0064451148240b5000a2050040b50300307941100c84a800081d420809414003c0c8054a180c1048451101081c42c0c900702c480d6515014418030f0100040d1b19103200102541000e02500c192010b8245402546502c80c40c0520062202d80349000300b000341c020003900c07982ea0b041100e010005056040513920400c01e122490341e0103410071041c140b1070012119400840e070000c0329484005c00700121440d1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 15306526 1250 15305276 15305299
    0x50a0c0507060909050906071403070201020403230c010c030206060f030a08030109020c060a02070c050103020d140a0b0117010e06060306010215011514030f0103020103050c0403060e0607260103030c11 88
    0xf03410507240e2043e5805090204107a545820702155651001d85000c4045030f0454054040400400011135104890384000741c2441d0b66561034424410b03203400f00200850041e9040252054104041842540b0910702480340c410140c0b4080e4560341e02600c2d0501070a454140c01c1c81d00d4030100300c0c0c40e107000e501503520740d602d6a65182c1007000790007259035003070349008041c045a07a54205000780d42c00d170743d001214120a10701c0c2400541c025030100007013508194613441c5240e0750751840010701c3d01c01d4000348130128125a0000c0018070754844035000f001445110001803000c80c84601c41241e21100c00e540c410394903120080140d01c1d101c51100400c0032a000f4a0001c580003980e484020031107c1035841c0d0500740b41079018118141c0c04119148001031044000400266229030031003604040d01183c05d9180c00e03125110360040d030701030401c1c40d4102d502010601c1a1a03500081071001201040c1801203104090344c100440c4500c103100c064200405044103c040c03000101c0c7c1340300b40200c010300215008 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 15307776 1250 15306526 15306539
    0x201061802070c0b04030302061521060402040c05040e01090914070602070501021908030604050c090406031a0a05010302010503011404020d0c0c060e06070e041104050303120f01050f0d03050a0c0507 87
    0x258407142c401c41d411003110000213620000602980c01381c960540181013030703030b0b29081c0c50741d0030b0344401d030710141d03c45035040b198821130300200d04001c00f60b191100a04032a1070075006103c107640295079141d0800000700820084a5900720070345065448044011405000904201c012040080e03002c1c4158041d900700020266000210441168403e07000e954001440244200c2e500800c140080c0010004000045451800b42d10a59118903048030140c14001e070b010208080b80c007240c104645248405c00c9050080074200020356000315890303814022503045600080281c04103100f1410424441c040200d00b99456030151401508070010801a52405490091840c6080e000a841c03151404d103da203000b00d0017040e01c0344240c0e91500d0b014064060b0605010041ca0803154410803080c0c00c2c000440c460790300340002c00c00602030910580c124104180d110320605c5046e0b105c10300c07030519068500d24075158201c420b206640c041c203009032a001c4488090ba02c0140d1407200030710754001c000c00071600307 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 15309026 1250 15307776 15307781
    0x612051027060e040c03060518070b0405030c03010b01170406060302040504030917210918010801020301031a010509010302010c080d060605030a0606080408161b0801020d0513111002010618 83
    0x45001c0704040c0419556904007840d03402c01940c01901c0503400071410710210700c450300a903420080c402c0b4040082009607800a051103029040800e582c0070009040200385410000071300110400c078000c1025440201c000b0341200c1c0840f04014410310f012001030b0a014850b44114021500540140003d1601d482d000b09010b0203070003004c0000041ca14482901a00003640384004020030340709005814000011018030b41010030702990014600240c614070151040c2c90a000380141000940c80354190f10703051920303185107c80c2251080e80440100b049640d68040d40341143d8081c03c0c85489081a4203080c9800d1013440822105281043d500141e02d030b9210000350701c1030003211000c00c04c954a4000468130850181d501901284c1e0500080050b44506014500c0e21481411f491801c02c00b8150200e401625603440181c40b45d60100b20764803c020507010300d56000c0c14148150304400d43c9030361046800020305103414041c4038054a0810800d000358403860103041c6111200203805c0320b043e1450003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 15310276 1250 15309026 15309089
    0x30f07050d0903021f0e06010b0d020705030d0603020907050f0f0f0405030303160e0d030203030f130f1505070e1c020a050409080d0b01020304150c030201140f1f06120510 75
    0x9804581c0c1c0c5c1004483d000c148100210720101c00d02411860b441c0c141c2c00c0f01070f03400c10149114030329400c1080c2000030300c0400007003902e8000070201140592031401005a10000200041d040c04010821070000151030000c03540090454030703d0a031600c00306258800c003070043da0085501444001f0070321103864050741c00c003808095550395601c8600c01d00001c0c488104405003004000d64002d01c0230032150700d40341c00995400350744100080103c0c0000c0d20307401d044030f0745c40106a401100e002d10001e01c401f01401400e5200000c3e061040b14481c0e400c0104509082115510340a0492040ca05045598882d1380c84028003000b8000d01614800d410807458581c4810b400300640d030310b4400345403115400071042c0e070116240d40210390110920840c003618020984141103046540c1c40b05242d00c468031400850780186a803d2071100249429007040c000c04032a001306c2d2001c000320741000c1208540c00090890100c9054401051075100c0c0d035580c0003042c0e400c0e0002846440464038410003840324480e90103 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 15311526 1250 15310276 15310303
    0xe01090b090c0a050a05090d0b0106110c0901030f0f02040e100b0f0d020f1507020406032111030306100302040e04050307031202040f0306021602030d0206011401020f03030f07050d090302 82
    0x5580b078035000d0503410a84225100d84010550a1003508101401803011300704007400075203120398031903032940c07400e5808409801141c0410a02d464003140a00100400030308031034296000d0f06035504648800d10126201c9600420b98103059030345100b15243c5800c10a1694080c03070071a40c2c3c008034004030304090f2910141c2e4130300441000ca02040d0900d04400d0068100c0c1d000740113080d00d4003c84040c070460004241052403c11000c000c000c3c016140d510400e0011802815001e03841d551076030308604d00c81d80d80c180c0b8004002d038a1260111b46040441101e411850440311540010005102503010340102d9000b2440003070340004000501c0408002010340300e2103030351a800344000e0780034488200d000da4050350a0b40b503c440c1c018030000301d00da4010807a40021600600d4804c0c22940046d05d06480040030f880103070414801000210442041d01c0103d01003400035011550101d005c15650303000042055140c0340000c008165203502450454070990070f640002c2c08194060308011b9500e40d08840200c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 15312776 1250 15311526 15311539
    0x3030501060215100b030601020f0304030309030b0606030906070e010c0203011d012403080904111803010501090c05031515030703020c070906052d0d050615010c020310050408040e01090b 82
    0x11020803c46501d1940306845004602035458248050903100c6d4200410f26419071003807022000d09288108050b0001f140301e6520000c203641103140140f0000e5014251500407038040c41030103019003000c1101c0d54810140d140060300320020f2401203440d0ba007003400103505546400c104066514414a00b03001381e41d450402404145101c40b040304580ac0408141c0d92070388103039001880041e01d142c1c01010107100c01000402c0d0611886080030f49580300e0102100075501035450350080b03040030700602e4010b065800d001c228200700001c002e4000e200040c040399a101c072040e030001c0782d5961400c04180100c2240781403074603450714010150003580b006502013942d01c90034000140d4000b09008041c1a01c01c060289140311a8102100205049078422210070001c05028010709444852041242c0390191008080d10308010781c482d0948208400b40c00e041080b071000c2600543c0b00054481305030364400c3c000081e01e90b101c2c02c1c0440c050069410442840032130400000e00705942c0c0e00001c10174102110030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 15314026 1250 15312776 15312793
    0xb0c030c010b06030105031e01021903090201030c020615040506060403050a03020a0605010e0105010519020f060a0c09150512040302120d05010302180105010906030e120f03010f0f2301021603030305010602 90
    0x411003c1e00091141942c1980100c410010789080030490903044a0f04500260400c24218020074003400030521110000e40d403051100c003907683c540101e082404950001d402d8604044444905000240380c03001d0103141c48501045c00d81d11039000321001940c10006a03002d031081841c00a458a0301102d068a2060074a000403400001e00d10450341200c205840740c6107070112250b4086840c00000c80c404040d8007440402c80042e6900303003d4584244d803240400101b803840c1300009011901140c01c2592138000d2000075280203900b117800c50310740420405003000da0780c0d130303c1c6070403860481d44c000405040754011075400c90f041160b4010700d042e68030031140b9154664185c110762401c12424030640b40090595102004924000c0d48040c18444001d0150fa0710a00c610017540900d500400d0341100e8004004010480c0160300c00000028014141c1c050884920308002c90340102c40e00241001c01842550141c40c26030300070003c5540c0b0316003001703003458285d6481c200a002004248146009170007062031 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 15315276 1250 15314026 15314029
    0x1815030b072106050102030a080402040e070f06030608010605060414031f1d060613021305061201030302070602030c031c0b04140103050c01030b0d0605040807020603010b031005010c030e010c0305040b0c030c010b 93
    0x81c00044d200c1c10380c01035007881c110340800c443e9028058010f0f60041d0ba2580e814070b07200000c0c004003005d00001201040413031f2078408002c08070303500b6512042e4164542101441583e468804070342c222100003041c60301200c0c0c40c03c0040d0030320003900d6081402030004007e841500e4616000050304200040800104014146240b0b45500b421107501e40c0c44070b2482c95190203412158040c0c5507401c5541619800d43d51110007150340b030341c001402000c0c07800340750b40100308256041002d08040c00c0700b032010314107001c0700a000380c1d0b40e03000ea410a083d401002c9104601900703019440031404040003081882040001003208070703140428002a14240562240007203035500074010030002050241c0b50490440c9070b5201e03080103040140040750958400c03c030300b5002da0b07543d00c080c5000c2c158103c103c2e03540781441d40714920f1410650340030506001c140340c68207010a4120106601310310085c2041d00403a1000d2504645920950b084003841c1301c0c000c5100e200442c03000002e0a0380c000e040c002002140e040c01c0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 15316526 1250 15315276 15315281
    0x9020a0e0601021e100e01090204050615041206020d090602070501050604020310050405040807050a03090608090c06030a052802090306010f0b09011b0b070309020102060604061815030b0721 83
    0x290082d025a0100d454000003103a80308910540303003200070a40340d02260741204d04003590080901100642e444204040c1503203024402c0b40e0704003104a800c02019294142c0022841c042e5100e04441020102c2c80d500501c03440342c0483d40c8070000420100b010074400d1a1240c025000b50000b0740c3d9561070400040d4107030400744201d030b01a0300c00c104213400e02e500d0b100c1044040e02c4010320460700c0e820705002d03680001d2400c01032000064400e8459a1846007003480080145800407e8403c450f44000c0310301c4001e0b03c03103e085030740140c0100c0c07001c22647d9854180030b002c85010700c0340110400d070302001d0203420a41540901170000048095981503681c503084105001e016010755078800c031303041044400c150300035480b0b10641c41d4000701c80301ca003180030b440304244400d040b50b669000c0303500e0380c500c94110f69051211a0388a2000c4804006031410108100c40004940951080c804d0382c818200c0020b0b80051017413802194000d032003200c0c034134010700c00402044000c0b10381c04c664502180c020b164a032160 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 15317776 1250 15316526 15316531
    0xb13030807030501050307150507060204121b0b0a030902010c0b0f09070b041409040203150c0403030905011e0f0c080304140606011d06030a060b070308010e0c0c0703021002011104060309020a0e 85
    0x4006004490801221341920f140b00b602328810301c4003c0280c00001060b50000e480140366107900c282c1c400005050841c2040c0d40e001010a500444201c240984030101094425002c064a400600c010341c42c801a51084401c0340050a901c0d401001c20010305074000c0340038481d40c2c4100555004030307a55242e10400d40190302590945d018515041c0600e030616085403a80a80001c5c1154440c40050b081404070400c2980c03820700000300060700740140b50304840c02100034442803030401c804401d8102d14500109072006a4420001782c406402c064510640b54a0303600c43e0071040c207650b02e04040c80d00482070b5400c8807014802d40907a000151581d030040040c510b01042014a121030b5450081c1040483e50000740100030380c543d01c0320301081000500015004451203a2560341c0d055040c002c060525507401059462102000c21030941e18130f5001c82c0c050100c07070b07068400c00c0c002040030b10141e001d00812211030000003000f1a0006506138140c01140c04540207803140e1410945812aa083d0181d08 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 15319026 1250 15317776 15317779
    0x3030813060b0d06021905030402010c060c020c03120408012004030b0a11040902070b0f01081504060b04050f010f0f030b0c030a0b0306070207030c090506100f0203070b1303080703050105 82
    0x11000040d844000603100520154400d8500050100004000481c900c8859009840c09a40401c20801ca4003030000856405009030818904500e481e0740020104e0b410310900420060700c406441014900030406001c0c5020001c003a0340040c0c065040c042c0454115100740d603980e6091226204440b808046440c0c441c00300304c040b581c54541582c445202d00b450160901c814140d840084100710309031035024002a05104101582d03611044c20b00c0c009009001c0c0002d07d48510001c01002410750018035035007130704680110381d00b1075601d03410210000c01346090b1039900581040300300b21482035007810301410b80b244043d02040d025198a4224070081c1240401400540c51801140c00d0354022405142e03c00802c84000c12558903d4010a0401d101916080007507442480300b0310411448440f103038040e111f035540c01c0185103054000038041844075041e0409201c0701c0440052401d1003801150b524070703000a1501d00310706010140301805c040101c0142c00080c0b880c0007140c522071090140c503048a00 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 15320276 1250 15319026 15319037
    0x427030c03090b0418050619091112090a051b06090904080912030901030b03030c03030f040f05010903020c0f090402090606090406090509010204170a030203030703050a0e01180203070503070303 85
    0x41664003915002420403058082c040001c0000071500c030301c08010009003214942c00c0380c0301005d1005140c140c80c0094541c0c0d22651a001d56814544561010b0100310758451034049944010181c0c0e0300514494008040b078404410410441c024500040000c0010312031000c0700d5145004581540e090308803086499407213041000103c00a1a0000145400034094008207180c107903d0000502c100d180d900b9013030815000403850034100d45c2c061043c5050524180c02030740c0380c0a07542c0141c42c0c4a01c00104002800e8400e00c0c00700b0203210000d49010280c0b03a000000704140c2c041401e010f5030381c503c00ba022521541080e1a00f02c0c084c104810340d02c0c001d0b80e0181c4000c00b281c95850400c490358001c00806a0810f80d159000074048001380180d0307000c0c0c60104001642c0b10b08052401843d0310301014025a240c1c0803180e40e10010b0b90000440e68018001e14001425032076070390742ca002500102084000310360030000c200b52460203400d545820540308508644030f080d03484003815140d907140d00c0b0240c085113 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 15321526 1250 15320276 15320351
    0x9060408090d0204020f0304150b010e0a0314070810050a0b0d02060d0b03030d0c080108060901060b04090507030f02040602010b0a080118030c020402040321020d0509090103080711060f070204 84
    0x410b809040a202e00c028409420501001e10002a94104440940b01e000790001040a8020148140d640907902860040307807107a5200c01080807078140e0320008190000d02110704040d10424800304001c3d203480c00569040c031101c2c00000f00617240a8031090311540c5011443c0c4658500000d002d0f90459001d4030103424034540300c5101000304500030509405003c100008000c1b242c95108582a4071000d880310f00465040003200d600d4120000d0540074580e1401c41c0a111038182681520300b140c03001c2101217001d07078408030100e003e007440c024500c00350b50011502081c182d4040d0060b203030502c0250344466016650303095a50036661840c2005542d0b0a070017a184000c00e108601110b44180040e10143c585941c0341d40710420102042c0c0c0950ba900c201502c200001941488020382450a03468010300b881c410380c00090182606120060030307420000703184030400004400b1000e080394000c20a03502c030607004e080d01c401030f0301c4204100e21603460a4064100041070309680d9100e40c581c0c120040450 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 15322776 1250 15321526 15321529
    0x20910030507090b0408010903110118140a0204060e09010506040b0f04020a0509130203010503060c03090606101719060603050114040203130606080d1e0210020a091208070b0906040809 81
    0x40402816000c00c0000e14980401c20300d5240d4002c00c018061040000340032300460800034940307842482c010350241d0500d1062120341c288210118507041c0c004c100e01e0b00360310007200584e1900c000a13500a400c41d00307002000541040401c1181e1041d51820000e001075a02c0208010490b0186591503030720200d0800046401d04007907000d450310441500702549403140380c0d000101c2040c1c1c4a82c81601050f00080144841d040600615405c42203002c41c4505605140981075241c1d2402004607002d01400079259003464420380d103142541d10b1501c808106403d000c48844100901060f064040c40d060103c00920b003446885210304807400031030040a1400007504100c06544040e040d0400300301c10016060105295104401c01040071034010300c2030b420510380140140c481011041e035540750010503c044039401140c6c1e014169202000160303100c806807010303281c1c41c070350b40c100001e0029074602841c100a4810000e0010034051404070780d141d91184c0a442d9070b11011100103040081c14082c00000c0d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 15324026 1250 15322776 15322781
    0x1020601140a050a0f0807060503010f03060c050f03090106030219031a04050a0c09050601030501050405010509040b180d02030309120a05161e20010e0d030e03011b1701080102091003 80
    0x4180280b003458490340d0340c3c00003503141e0303d240c0010f21407038902ca00402c560981000000c0081c8106e0510130300315850301e00c154060134658440644034949034120400701610800071520b900c81421001512414003111050003404d04e8042240154590111440d00116000c00030702102e030f00070a0705c1311414505820084d21040604111101d116180003000000d20104010024154042e400261882c000c0e000400b91201a400075000f2854180144066141d03440c4080c0d0080c3c01451481107600c03040140f070300d13192083c4010645802400320680304241c4c00b00045009603801400c5a51043d5040540d001c40e20601b4884404034004114046030810744912115415008194040c0019440041c0651030301c50b00004541501150051a550300703080ca49003861034900786000302d10340010340b0100c2c1035401030080180511160504000255074250000011100031010020345128400e401602082c0c008282a400516010002c1a0802c05200740c4e8041c03600104685c1143c54004402d400 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 15325276 1250 15324026 15324059
    0xb0c03091b0303041e0b07080309060a060b090603100902040f03060f0e0a0f140d050307030c0f02060106230a05070b0711030d020a110601060e01020705030105060d060b010215090106090e060601020601 88
    0x10342140c6202c0001c3d000d0004c2000d40307d02ea015182d56656440c2c040303042d0342000c030001c018019151a01400f4002030340a042a1164841b060320042d030b69466030581040150382940c4039208003800064081103403c05e0300102e00840344a4042032107610083e40c81c1d48149e0310501c02c00c040d113a004141c6600403038940d107000d03190203000300000c00c0082000c0c1c140508141c0450350601c0410400800e200d01254940b0450a9501151038907540c04110b03440c009448030b00c103200e46020001a082c000c41c150b000f100300c411200800c042ca01e555074481200c040e02c1030304940e07001e031188090500000c40182c060520b1707042c100241400b42d80b4120208a4000003504021414420001c400d101b03083d0a04c410010207000e000517407900002096101c1c00285030044640103107005c4d074180001d00404da1540800d0b6403034180d2019012a1101c01076004038500318039020305201c541040414060a1807041d0b0240c01601c01481d0140140f085042c0c4460b5902c0f81980c003180144d00040040010306010502c008 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 15326526 1250 15325276 15325319
    0xa05060d0605070801050a06030c12050604060e0a060f0509090a02060a030603060507170c09010c0206090d020a030c1a030f060d020418050303090607020c06040b07030c0b0c03091b030304 82
    0x40000050721400111542140d4401c0070400d00ea0042c4400c0c5407155140c0700031b0455140c00d20100615080085c1030580c1c4c610305140d12500c45011412983da590843c030040d0a00011000d01460010161006003082e44034020303c10b41c0718180801d01c1d0a041c0c0b005449021003400612004107140d0a220050340280800c00816039500d101200258040c0580d1f40240312590b07800c04030220f04410140c0407400a0210384041008000b02051079803c903c6a00c0c2d0fa40d01202c40e80d8440070040081001c021400714000d600c070100c1080801003210a10303088041c0ca450385520f0503203d240a040c1040c03803105a03030010364034203100000344552516544d0401d444e440604017089090300c0220110100280394401c032010340001c010012440020411a603100419100501180780c4603404a0300b00c0c400c50091a0031400c000500384117060141d141340311401c1c2c1c4a00480b40ad85405141c20100d41c000780d5964030f01d0300640c4100c9615203103c10011a000c44001c0245252615184e0780394038010151503100c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 15327776 1250 15326526 15326539
    0x1107030f02180112060b010f0905090a060806010e07020c04050103030c060905010b0913020f0a061b170409140a0504020a140d02120102040f0602061603020f07050f010605010e0108010e0a0506 84
    0x2840100b42440c950003070040c404030380c0100000b4a0301d1410313951105413060400220a41d280d440c0c9610588000484505450143c260389409048402800c0c99400c51740300340c4292000082d40900501400780b00b803440b542030344c1c10141300e20204000d8400030700c400b07400200700803520741c08214140e011603801c2d071040000042c40f0b0103030804108142e1045a40c0e42019007010044815400c1c000ca542944000c100c5801c00f01509016024005c030f10234503440300744130319000380780801c0103c000f00c6209207000700c83d0165102d90361011b048010700001d0015903180f10350000410064050381c0900c0340200d500411200280342841005840c0030300035550154000300c0104d802025031502d6207c1c04591b02d500c4000f41e074490400c00e64001c68407a036401b00e011548130600704403420090740701c0d000c0745554500e00940c0d201140c80d5825100d015180018040e0701540341c81109074501540a241150002e80f01c4001c0750b03424000540706140240304e02c1c880000c4000010310022039940c04580d1102005242 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 15329026 1250 15327776 15327799
    0x2100c0803011a071403040504060801060b040b0304031206080d0f050a0f050a0e0a030f0b090d022508031b0c031f0c02031e040603060902070206090d0201092706061107030f02 77
    0x110b54004080e1751040405401c0001d05000b0384c00c00f400b81d0405803140390001c2c40b01918140c1211124882e0340b040b803032440c00c088045020036110700b03140040310300160741c140191502d80c44d02c00d0b16507901012160100d4200d80142140c0340c040e40031f0b41e2406280c2c0d02ca001d4000303e4080240c0322540201c0641e000c102e00003613440d41c04d40d0384100c04805140541e20005c0c0703000292400d041106400740c90016240e100ca055403d6040e80088c0a840c14824040d0300910041030b0b490500c403126003504680b1071350001240580460074424080740c5200ca10404944080d00c04005041d11820b0700c8a1801d4144881d00b42001d07a602c0d03640056445400702d00c103e034948400d0300070b00c0c10110b040d034030100701b003920004041003110b40c140201c00181180d4001180340030b200e6400942c3c50320400344000d000b0f0544821000c03d682c021201c032002002d01e00a090f54110100c10325804501d0440d1003210300515014020404e28031a5803400c0705241c1201c020020700d07065840b0206030241c84801240c3c4028071074503 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 15330276 1250 15329026 15329033
    0x31404030c230f010e010510060e030c040507080609010906120204021b0102070302070303081005010c0605101701020409060e010b0708030a09050a030806130b1f1101090f02100c0803011a07 83
    0xc0903014800b10041c109076401212110700b590390b03d01788062540e0410091042c9000fa4568080c102d540d1810003200b11503545012034204403c60081560152615040140043c2c109003004d20610b0215450861a038880d00c071361003194a54000c5c00e080720b0140c00f0140041c10f055008201d00c0d114024515120440c80c1412400c2e0307800528100c0042c2c200c00000c004064105803c184c100d0280d10712a080c0b541400002000d10200c250302600e019111801700b0346058442c4401d10180880d50400302c600c650020400d4080c2d0711912805414034903116000030325079503802d000c84c1a100d01d1444130740350400c2512065203a400c0a001c290a6540c0c80c0301d0036000400801c802541a4466107950550349422400c101c600b6225500060700d25040c505007103481da982d02204044150340189210105181d484210f4244005c10b0032480d03158078142c001c5007132108040900b26018030880e9414622a010079084a81c0c0001c44001003480313805100610440810b14103002104c80d01a20300d6082c003c0301c0d00c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 15331526 1250 15330276 15330323
    0x705070e04080702011d0108070e040b030d09051c05060402011107080703030c1101020c030709050901110f0904050711060f130f060b030106080102070f0b0703060512030306040507031404030c 84
    0x100e080702c1070300e8006011411540c2021482e1070317189401e40201e4480c1094000a00f03c000c00400540c00c0110b03030040c68074035980790307480611610005821140018010407000d03007285074a01440340b04481c6140501360345066041440307902d90f8003001074503a6484980c0151400c0d0204590f040b03141c00b440070045034001041102c2c00007113001e59035007441c42c005030800040e0041c8050b03400d41190005842001581c034001040011100504000115a688e0307803903040c0101080c000d4100b804000281d0480c000c581c840c0640300c0c00b1000c0f6010001c41d10780035810758034407195200d52001d07034124000144180b145103009592042400e000186500000ea8031400320f004041d10845409035a00e40d142400d080900c00c0380c02601c0444000c510301162602c940140400200f00240f01c00c5c03500e40000d1055100c0d400c407200420014103000040c0b9007081c90b140e1690800c84415004602d840c002440d0a84280105881104050700003401500d03280c4003168114a2910700307031a661180c40c4c1c42014941003c = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 15332776 1250 15331526 15331531
    0x18120a02150a0e04060608060907090f030f0c0b030f010e09030f160302070b03010b07060f0608160e0f0402060a030c0c02060a030c080a05150d05010f090803190908030109020705070e 80
    0x10000d050307841d010040003034a03c0366021000ca029070b01d01181402001c1c1c204507450f0708440c0c22134291485540c1d038402210440c1e415003080b01000440c0c4000410008070759901c90070103110326100c05885458404070f500600044030200c0c0551102c400410a405c200522039411207072040980380340c0100d00709884131642c406181d4100705212001240e007410341c103110280180031510041440d40d40b4001c4140b4190180300c002820702030b655201d411202e0341540c0300c0c0004001c504c080e1104240c40c1000b04050361011310036800e12100007400600d002880d0042244a980d0003010142030281c0c80100310014032000d0140c005200c442c00307014000d03a9400004c0c0488015541e0040752000c01c3c000d004110000280ca46806107040005100a500421000c5001203d05541a0081c00c440307080c0b0300d000d006506610002189080c4500d41070040c808011446101189040d01e055400041040102c8007040d801038844070041c8018080b000b401d800401e1304e42e00030000c0300c0c440e80c3c0341c1901040c81e1206 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 15334026 1250 15332776 15332809
    0x102070c0f1503110a030e0a0f030206041406010b0a0305040809040e06071d1809030403140102090f030d09030305090a0e0901050103060c09060e010e01090308121b18120a02 76
    0x544810003070b10414000030800d00c042843c090100e280350003c40c0d0058010f0304140000e00d80c48000c040d0780c5c2c600420420503030710740082d110800d00429080c06900c41c0c0d0103603410388005920000284e40c0c00c2c40001c5c0300703040f200b034800c0c0c036850f081039503108400400b0054030854504c18100300341c80c0f95a4443c016690350300002d901a021508012030050102a11030810300ca000d200c0a02c51200c9565081c401c03540d501c540c0018808955403942064110710558000610b90452056003c3c0041c10544c040c004108003a5854014401e45004040d0f607601e0410550700018110581400020310520250980070006449402c0664a540800704484422540742640c0c0e03550740010024095076024040701c610181c20300c0c0040e5820084018680d0701048030040c10720a04941610113a41302d108040000c0d03400c00000d41d01c0c3c0c0002c1c80d4405440d0403d27111458040c00400c1150260807082c021141d8100d8a2062900b02c884004107020040641000100d414003946441c0f0300507846150b50510303802c0a = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 15335276 1250 15334026 15334049
    0x7030f0504060e0706030b09130804180603020301060b03092d0f010b04060504020c0a03050f0909070e090c0c210c010501060f08010f030b0601080405161401090b0a0804020607050102070c 82
    0x1400c583d5403404d14107a00007000c060074100001190345801e003500341c208000c1e10ba580740c480460b080000082c4159806203000b40d003444a44491001c10340d01c008281c078400c030000e00c00d55903a280c40d00014001a907440507907400c00d00102d0031300700302e9124a10341d4142442040c40d58201084080d804c00c04000c030b08000d180d4484280038903601c1c0230702c5014003408045508604160b0360140082e51043c03000c80042c2884800030300d5003030502ca94810303101d100b28010904011403402610080c4212502c00c00d4500424001c40400e210a40220a4500329111000188103031011180c0000d40008102201d10300190b0070041d001c41300c1d07401e00030180a01400c0c0c0760f0301501d410295000b000d582059111100a4140200510009908541050b0400f409103045141500d540c00c0560800c404000c070320100c0f013240c900000e0116040304c2c0d003411140007621030b0340c103407a66200c80901c2442007801034800900400d0000d801481c1c08805054035030300420005040107944e030b5a80c4c005481d00d401800201c0c6 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 15336526 1250 15335276 15335291
    0x260a08030a0606080c040b19020a0f060903021506130b0a050306010906050a0602030903030301060302030703020c070806010501110604022803050102040b03060f0105070201020601060318020301050f090c15070201030507030f050406 101
    0x94105031041c5d0004542c0e901c01d0b15080c03800714803d40300d009100540394407800d4641b04400c43c6208004442c800c5800c00b490110301c1ca0340303141a0004020f064806c03000343c0130302034151a0401449000707500c01c10001d044a915070f03102c204000001c10760888010750062000c1c0340442c05031820040b0314060510036600099a40c1480104007000f01d11740d0098003154010000501203490200949044035500d080c050f889072500c000c00d802901503811240082c0c403a0060010f01c040c40044c1d400c2c101c83d420f0302d43c0840700c0300301018503843e05411107010350000f62181524850705401c3c0b61603c14000c28000da5a0322030340700c0d03a0f03040c2039a00a0f0f003d81180d0401105108003450010f2200d00c42c1d079002d09045181c07108a1b070020352501c4051241c00c092503071710030068a000c40d90150040a1550080c000c01c204d140a0994014911050f94000c0640c032482d07954240341e00340440389000325a0100442400c00c015680114050300c40241303920308041d11340301003000496041c007882e809144109808603968 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 15337776 1250 15336526 15336539
    0x7090315020f181801061d010e130906060b0c03030c0309241603020406020c0d061b05070b1f030602090a0909030c020108070e06072d0803090c010306260a08030a06 72
    0xc02c0ea8000e0144030b10300c1c04010000c1540004800034840391f030700c05c01c8066a0051005a984031240000703607030024560780d03001020720001d5004481e402d104600410209407660b0702000103005035a84420303264402c2021403002600740028650000c2c041d800c0b1103855002101803504034808000107018101c1c001c083c8040d1840a41240c100503c071881c0441c1460b20f0700500942c0c8a0f5645c00307460041d80703a80070301c00c2844165040824507010042000c09150400a4010001e51103041d09517030540d000f1000c18030b1602d6180011241e4046081130561540c11174403680c0c020f5210b0450b1641c0040b2004000403400c03120302900910328006e4076102d00d0110f40340005010340c13030014010401c22404146001070f613a2641e084c0e03104c043e001460312009100c5105090401002c00204a42d01c200c03103000c0d07200700700c1c4400083d4400c252444c01d652030402e01c1c00055013501d105008440008801021400100242d008250340c1d0082120844000454030f4840c501103901c1550041d50594498100748a034 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 15339026 1250 15337776 15337789
    0x30a080c07090e0c060d180b0705090108010503011503020105160f08090405060f03070611010e1509070909030503150f040f020a0f021902090405030d15090b010807090315020f18 78
    0x3c160340b540242400220681c0040c002c0d124030f10040d8500c60381d42440c0aa4031001302414510245d0048640490b030a02400c0030b0440d4102c2e10260740003542e204004200b43c1410b015505000e070002618002e50750440e401590b4580007008102c078202c440035100004504040106e00e0810701440e02c9030758030001001400240c038001481a40074416141500995440000307822085800515140d20400c2207010200e0142c8210480c05540d445072030f00010b04404142c00481c0203101c03035006c90b03080a60303070805882a601481e1000c0c006ca4800c0c00099402c0f614490300d100358920003403c00890218000014044804000d482c1c40c4540c1d003c1034200d14590402a130001c01d111a000818044c0c081610116100d0320a1074003e0080c0c90107000b040402c14100301f9506007070282c20044c080c0707102d58a1180c0543c101c910074611b10b1800c082091400c0d5007d00215801541940e0341c1c41e00c003508680342c410300000f40040300380c942d036802c001e245001d0170440e0103804010f2583c0c0078501c40f0454101017205 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 15340276 1250 15339026 15339041
    0x31a01050910090c030f0608060f0106020f0d12060305030703020c0411040f0b0f0403020d050f1006080c040c05090d0f15020a0c0b0406060506040305010207030f030203010609090902030a080c0709 86
    0x10301a1a4240140240480c24000850740382034004546400e113510210060850242190a92030503c0300c0801d8506c004242d0741d200c0c4540001141c1c89070ba0b2804c04036601da00807076a003051500010000590f06100f111055a030340c8050501140709942e81d90303010b02d5039002d00010343c01600801d003060413616180c040c060940805492080c1010b06111010440494034401e140c40e413840000d206141e1240340080e42c0c011a0010304509959584e400c000e0744600d2594801e0300c0c580981308240e00c03030841c2403040006451a410042c500a0a2001440014010380c0c480f08207000062259600070364038030180c02c05c0648110384800402c00103180c00c080500c00d640c6075413103031801440144142c6920942c850702a503004001e04223685c071a03003842801884503810068102c07600050107c00d0000540090580c28440c0d030f1040701003240441c0c214100c1c0428054440082c1c2141020818284260421205140003c0c00d5031030f00f0416944032174180d444020100080c0d008540104481000e501c180344 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 15341526 1250 15340276 15340279
    0x4080a14090a0501120e03040303020708010b0301060608070f020a061d010f02041a3403080601090302030717070b0711011404050108040204050903121807050a1802030601120204031a0105 82
    0x41c24207140300e0010300c240910b40907540c100051041030302c07900800381d00286554110001940d0b42e41c1c0d00c030b0030029140c410a00800d00c540d070070907101e586241414840d06086603003665603016540c80da49011201c4a641d420030b4006c521828443c03e02144c114868401c61020304c8001c00b0042541506aa094842c40d95501c0742a80c814001000301ca00740e0a5456055280340100b13958801032041c0701501d01c0c6071401040861086480d58020101c5c00502c61f00d0480c1c001e4651203d140d4515004541880c0c09000c001d4054001c0c107420400c000b030b41c000341081e44a0701000c0d580001d450380c1c00360241d0b402c0305030143c510414500c4410640e5800070142c60411100c54060b620382803c0c030001a001c80c6025000a0140d581c0d4400503503186010b0050715000e8008000703c96503070a14513090342c0c40112132101d0b8880ca0050700030004603498590514002c50340d851928403408c15034403003140000d41004241a0622030040d034100c591008a100a02c059403045030754900f0411030704807044641074143c0009 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 15342776 1250 15341526 15341567
    0x61011030301050d03050705030a03020a120b0d030e0d0b090a03030507020f06070f0e04090c080d050a020a080306040608060403030e0606040902030307120e060d0b0915061801020304050904080a 85
    0x255001004012281551025510100100454641142c5510600c1009040f9000100f08164100d600d07400a01101c1d9887d50740f50080300078500e105048402488100d50322801101c45038002a00628001080000050000d001c0355041d03119901d40840407a032008176900206c400301c003019014407a0b07581100181c4000c00050014901d4142e68610241044003405152217005103558820074200c0301415000e80f09114044042ca001798030440580070382c1a4034056010034400e860b12410a4034003128140e80100b110462030741701c2011307540c0040c2c007098119884440200f110001040494001c3d4441d0760300052180300302012a0070002c024028612071802c001d441005641c0000c143d44480341c02c1404416040000401074030001c0c00701b1103603504541d02068030b182c245d101d0352051070f00325030507500b0b912a42c1d100c2c034103031701a180760340582d0361b000c28140907000c4046c62101400b914024107004880c074054031100052002ca204540c22500841c0000710791440300d0703001c541c22213103203820503c0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 15344026 1250 15342776 15342797
    0xe10060314010504120e19120c060302031603050405100518010f0605010806010f0e090c0a03050603010204030209040b07230901020c0a0305101e06030f02010206010f08060a0506060705070e0610 85
    0x402009032180c0e103c00042042c56100d10b1b08580d00c6650b005032a88244180c40c02d450782d07458a5803030011900100f0348100b00d03481c200140300c40c001d000b128890b51400200c1190b0410b6054250003d08002c0c0041e00e50788140610712030b505006201c3c8a0243c1300c40141c00b1003044032180d844d800c1d00c0b4032481c21528141400c00811450b6041214660400301c2420100c0c42c03114840001c90741036506040d41f0ba800109803050100b2088000000d00380c040761980d0a128540c1d0360740c141804d0344101e02c4001c0d088084100040e004c40c03401509290040071a1801800400043d17030000b408012a082c10034141c00e0024007002d403503070100825040f41c0e00668072500305500d0b6445490300c954040c4448c02e2140d0701d41c2c0304140b0900c100d1541000085a510003005529103d082101c14000100c2d000ca015129583c000711701c5a40d030107880300c21600054000c2810f07a480114090140c04040e20a5400c030006100e0f900c0081c0042c0580006170072240e529001510b8000704014001510140000c14013040500b07 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 15345276 1250 15344026 15344033
    0x1030f020a081b100e0d080301050a060503060a03020411070b040b01050a090c0c02040509010e0703050601061803050703020f0f04051e061203180a050901060201050105090105150a0f030e10060314010504 89
    0xa040d104603003c45100c10a03004044c029125074418404c4160704c503110710b21800811000c48041c6058501c181c13100498035454150590340e511080e0740040d40117511180c10401494290045c40301c1041420f1000c0c00c04506030f80d2445a1007050380c0464003a6903c5005100340e0911900d24002000c1084051080388403810004e0a10300344030001a020b1521000095401c6100350802c2c07a0044071402160151a41c0741456070303c48100380111320000d0071480103000002c03600c1d0074500c256a084000b07410381d00d265a02704915004559003a03078000702010209035440d640d42c843e180c403c0d40c102c0c1a031034032500c514109181d044c0740104114400d03401600142009400001030f0780d0021180c42990005d40720760310020340c124400b0b50016600840540000c110180d064002e40e04992080e242500740c0e9817250204417007010303100001005090280f1406c034220b0300ca680ca9903030601d46400d0001d00c2a40056516041540312811075264640f100810030401010960b82e1030391680c120f00810080c2131568 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 15346526 1250 15345276 15345313
    0x11701180b03031c05160804171e0a02010c020601150905090603010603051e0c010905100509040e03041403060a05010b040b1e04090501030308060904050607110a060501030f020a08 79
    0x58800c01400d98402400900751010070481d221520085840f04104140e200c2c084083c007011200e441c640c1040c9007208001d40d004d81c038540c1c002c9a200d00d840b075400604000c400c180d03402c00c05a180d0404140c4284c0310484044800402c0c844040f90b0011809200d9918044d15040040e4004910b14640c101c0078403c035540460842c05890084441116985400780060f01600c002c0d0405090303801600801d10800003a83d203000c41240000c03041c0d60980e8502d80040d10b0f850141d115103a0044104c05012114902c0303140206114540200700064214154010a1a40d0026080000c44040300d04049042d0b103020001207500c806806030611054ac14100150300a00440c461110440004640014802080c80400d6080ca05141d0b5940d101e90783c0d1003c0c040602028401600031590f000003107100c506020300324604c01d0350071078001e0189031a4482d040f11140300145030820300c1e00541b10844001049802503500135401a402580b03141310714010440f0b000042d40c0103c0c00c65010240302130b12680c0c07c4 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 15347776 1250 15346526 15346559
    0x7060504060e010311030c03010302100e0112020a0309051005090705040603020d0201110a06090615080303040f0b090c04091101020c06070302061504090204050405010f0c0c020102070e0903070c080606011701 91
    0xd1405001d14a40b00e801600540141040c0c101203003004410815464480d10145040b01d000302c542800c880031506003500c03240b03aa18042400a9030b40c5031182030010403034005000c40002c0d8600042c840303d19031981030901010680b40603110382c0310030601c08400010010240a0b0a040310300b007011901d0750f03001540c000840c403402410300490444821003c941030110504282c1c12840c1030100303520303a01c2d10308028610b030031400001e40a007a1011421050020580e0301c40c6504c03c2d2030f202c2c410040d444164036000b0060a4007414400c0100d02c12454031180540b1444503c51500c0b2011314130b1020019080642183c10103020300c109200c4e03680400c0e400602281c205040741d80e076400b01d01004001c42c1c040c0c0084d03c000307034000381088148001c002c0158012a40d081802004225a1030f0340d00085495040c8a4400782c01a40312200c14080000042415a005004c0804036454242556079060b04003825500561107904032904001d86560014203500039041125800c0c0b8207503051480c0003850b800c20 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 15349026 1250 15347776 15347789
    0x20d080c0d0e10050904050403030e0307030903020406060f0c111210020c01050609040b0103060b01020a02060403030e0415050a03140c0325050307030b010603091a090309040b0d030804080d0f050408031807060504 93
    0xf40c0c7c0104080c140654000291184000140c0382c0d100c50905029000c40207a100490240707281000c002002d500c105440303c085180d964803246c1003405501e400401400c3c0c0643c03694840309450b41c105d00b20008224032118905600409030325455480a00c03421518001d01450048020408105c0006c041c0308425040d254414400101340040000407403a018400c40c0c000e41080c1d0000c0c000c4241600003082c200d12800c121814800c900d0219004292044648500c5802c44100e0005100284920b01040001000782c0120b50546c01c10400003860000300d42c06803007a414200c003e007000d0040c4c1c50720700700140000754002e18405107181d0342c55500d24014440c0d001090340e585a20000c01c841d5170070000c070800c0084074010090820702040c94880e800b625400d84205e03e8598140c9160405101c0f02040d550540c445111640c1c0d40d4952110641c0404040019159158442c0000f03450903c03940d8020790055080646925041c1c1284042503120514904542d0002104010704c680c000100e8003580c14 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 15350276 1250 15349026 15349031
    0x18050606010f03090c030803010905070c0816110d0f0b0f07050a0e03030904050115030e010b0d0605040215030702030403060c0804170a030e0304080d090e010b03040f020d080c0d0e10050904 83
    0x71001c50041041d404d005080c2c3c0c0b02c00c030000003488010005075051700e0070003004011b0b54444400546e285808808024041801800300c60000c8542c0c171040f40780740340107103070f1110303603080001c00035000c88803600c400ca42c551003e040312003d000132100b505a00008080e601065400c10750030240560040d400e400041180c0d91207090b01e43e45080c400d40b100d00b0400361041c441540c4a010401000c00d0001c00301001929065002a000c0014003c0311410103015121801400f100e440f24000f40000a00c1645c001d01e041c42461480340c0700340000c2d48200c4840d805103880f40d0a5140c01d40944107544047c1d0304000103c0e00b80b1000c1002d4182d000d0785054185107842d511102104190080c0c0f080310100c02d028000882c0c0001e131910007250f03141c00005660b8a1104103502c031007074411050b200307004a50313968800307000240c0080c5440d13080e058524002000e081c01028036607211130540d0300c00484010340341c11030004100b070150032003918400d42d1801c0381e42141801a500004006000d186100c520030354 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 15351526 1250 15350276 15350297
    0x30a080112021305070f020613081206030f030a02010605090f0411040b040e0102070c05090f0405061603090c03080d0609060614070c080a031e081009020a2c03011805060601 76
    0x1540c07610f07a01420003844405010074541958007910f4402e07190150b40c058020a0005164541d6590008008941c45142c0d035080500c02d5030003015100d40200240c2d05440b55a9540624000801c0030b0140194194000700d80705003443c05000c6900702c050003025041c44814144800940b0740b84001c00f0105003a01d0006501c81200c0008016028140032052075500c002051000d0104024103501070350820794050716203465441c24080030308400c07180030700107800c0b1001040802c02100d0129070340c00c1c568640400d42000c551500c8500c0754060340122507410001440c500c01c0d42c1c072405081e000f01040d01e802c000085c907218000d000881c0050380001042d40000710b042c104021790025502400c1c14038211468404d0034038002c1e121010b824128106078400d20240a01503200305221032068413506d007006450340c41c01c0d084101035000070820006011001160302c0417048481015400170890945d10145949544241800c5442110180d001400682044030110782d0001d1960b4200c8001e280610030503 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 15352776 1250 15351526 15351529
    0x712140417070f1509140a030f110a06030203010501020f010603080d0b01091805010501110601060f0e01050c011109240f0708071406040309080d020a0201050a02070503070305030406030e030a08011202 88
    0xb007854101ca0500d1080300d80209400304600d406005094254844100968540c80b128007000542e400c41544020380c03a1060000a9541c5080c0c14894400d0400b03a001070350050018aa054158110f08006135010004010781d6078100610108040450300801038030f0701710b40f80c2140d148902030144040645034500e11540b64032032515100140514218221480e0380350f880500900001c2c421180011009680c01c49040e001240c0b29048815607180e1402600e0b4800064628034503030b0490a040c49000c2c490100070410038020301117928440c036219503480d400d400401c1018184c2032400705543c412401240701034285003040b6028000b03103201d19074841343e080c580103410340f1410400601c0740901001984510200262090151b44247c0b14000b102d500e6100307081d40d820004003038000503440040b030300340507500840c01800340c0c000c1d034410744020035201c1d00424607000040c0d01c01c132420f91002030304015850b8184121416038402c0741c0034614007024003100400004042c003608503c074200d0507140e81103 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 15354026 1250 15352776 15352783
    0x11a0403020d060203011409090d0311090603070c0219030b0604020d020418050a0b06030c031f050a06050316020606030a030f020109061a0a0905160503040204060f0305030712140417 80
    0x850780188610003107440c529001004c0c1d0000c3c880d14825514140080003186820742c0e2130f41c40f030b0402c54020441c0c02c0c0044400c4004d000380d540b104450030f074200500ba0781c0d0f460704002940306d482140c179000d8030b80203203105002c13408045035455035036010044010300c001060120b200341c00400c00c03640540c40d180c3e0104004000d02c116884584001c6c80054494005c044a41060b0302c1000d294400f00400ba40da6024440703035105c00c603844001c03503004000081c91802060100074029079491300d00110b190b11000800c1018040380c20031804608044200003501410f0180f6540d40d055901c050280c508160010941d1442c3d02c0b00001c040c0318140c2d91150310140700354010a400c940080007804021216560340b158000c81400030360054210440200c0c0141307880c09100d004c0d4609882c44031304811414402c4503e9000540100c0c0e01549803c000036a8901a08102c03024500420103150f0f5007890307160808610f83c0703400c042004d000e1114803150440301010700ba10200c814140d20510124003041c3e881d0704 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 15355276 1250 15354026 15354029
    0x50f0a08040c0909050d0f050405090109020d06030b0109020405090a06080c0909030d02040b03160905030706030f09020303030106110d0c0c0501030e010b03010c1107060201060b0708130308030c0904180b011a04 92
    0x110349071131052814040300203a180f03070015044d100d5588103519688112078a00c514001d00e80c0290101c401006007a1240d4010700c102900410000340782c0e5160340d07440c1000c0c9001c0e4091032406402107414030030381c41e20b41180368001651100c1000040d107414012621117501c00502e511404c6990001000c01500740100c0d40e040e6420f0030b04640e160380b80c0d12841b08581003922049101d0f1240082c3c5111940035000403010707680b005004203145444d000c0110003401c4014005146079441c7c000140c0180c4040020710f02900c07480e01c42250441c005041e052504101000340810086160b0321f00010429807150381c0e080d10070070721300403643d6107640750394901614030721552030741562800184202856200c0740150784a00210241c4000540d03420b001c90030b80c0d10b14050b05072007034401c00c8900002141c0388000c0007030b05080044880d81a9603030300c0c0d449030340d081110107241c00300c00000c00724010301d414801c14280049840d0604081d00050700c0b200a8064140180480d4000741a00c0c00840780d0040151780 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 15356526 1250 15355276 15355289
    0x30714060d022b14150a05060409050601081b0403031409090f0103020901060f05040510140708030906010e070c020f030f0709060905060a150309020f12010e0706050f0a08040c 77
    0x40d954942085214400d005422030002014012100616501000e01606004d00ea52070448030298444421100c10140001d41c100d034000701a0000264680752040604010141640c001800d45004000074180d500c2c0140048142801000f20130045000007003502e05076509460300d044144940704180d500e5104000241da0b01c0b170812000c00c031030460311054460607244280e40c0548548d036521400e44016502d1030042003c98024002400541001c1c00c1e40066440c15140c124100790a48401c0144c03507010b55411750700d000000040020b02e110030031640f80100908241c0d030030640780c6070000610341c90a20800130701c42c1e6217141c00a4642d507010402e48200044070780070b49425039503681c02c02c401480c0f075118003012242810001441460029100c400315101000720400c00c140b103120031402030034000c804076400550328000e8000740e10340100c90581140e040b0300020390f08000e6007185203000c010360f001d2000c001d000c0028464074404603065840100700303400c00c0384058442d842e02000c1e13060b540e0403a8 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 15357776 1250 15356526 15356531
    0xb0a0905090108100e0601061704020a03060203010605070c060c020105030106120b10020c03010e19140f0a060c0305060d020f0d020103091403030708070c02091503031905040f06030b030714060d 85
    0x40f84507070f80869035a000d200c2e00c5070200103007400c14030341548400c4248240700200d944140d00d100404154221240c1c428802040307030741066103035520704089800c20b8206038005280802c0b40c8040140c0300b00f07810080c01303603820700c03802005899000030120b10050054a0400c0804145881c041e40190403007020260014007070000910b601200a541c1c400b8a000f1511030f60920341c0c0c40d41c84440101e4803000704805d2041c920b10b6401c054850030010780c841c42d0791001610907045c41d81c01b1001e051012010142c4150b4001c265801c1469000301920f0000c4d00040c40340180c0d008100c016518004c500c2401701e002d40301ea6484c1d003410300060f402040e4107440540f000000e0b40c0d41254403000032000314413440341034541d00380c580c4071104115003c081c00702c0300a40000c00c1c440800d4140740401c113002071101004040341d1800c13480464000200d21400e0f5210041600860700b031220803034800d442d5011301518903080068400040010f942c07412103106003104400c6240c403840068984908072000d03481001e109 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 15359026 1250 15357776 15357779
    0xf0d02031f060902041203080705070501150501030c0201050601090504110715051b040315050a1e05040b180c0405040302011401030506040204050604090305071101050d0c05030f0a090201090b0a09050901 89
    0x40a0801d10480202020318908100410004014400d130307020f070b0b0740c01e0083d540c1001681e030301650a00d0000d0014400d201c0305000900000700d090050614000c1c401d505586881c1c504030014043c1e86000168800b5a4100380410050b664469a10300440d941110086020f10b180c015070202c5208002d40541f10b00c0c6134a09000c00e0215541050f40101460321441d00c0540210042854a0041d400004c001d090300c00d82c1401442c429401240d00281c1c00c1000180a0743e00b0030420b50158200f080d619000c40c2c9800800c420701c003c08001c00c3d480f04071001d114045540c4070381980d131126545110140b00e00d917908041400d051003584004000d6061900e51421940c50342841a136496044070100e100d81d04007400204c05007442d000d610340141c0c0c95120b941c01c0025075659508062040d80c64070781040010300c40c07089464414018150341c00025100c141c1c1d24144261420b62401000300080203083c14810800c0042c2d80c0210b00c4021030740092100c585800041800b00c468035095402681d000201900 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 15360276 1250 15359026 15359053
    0xc011103041b08030d0e0309040903030e01050603160b070c120f051002070c03020607050a0204050a090201020705100212030c041503020c06060901030c0909110a030605010509010e010e060f0d0203 86
    0x441c000e5004600d0700042c42c80c00031910003050070034000d8502d41d40080c00792242d28180e0b60052200108a0826a4248000c44001c0f5040350342c40041600001d8403030310888483c0d1804e1007899088401a40a041c1300b04004040194102c450320800c080e0b090002801004c5c4030f1800903103400b501c05505100312a02e040e0900540320011508241e55034012400d048136613224910881d001150300002d0004d49a14580030004203400c80082520940101814400142d54a1141501c90050604001a5100240002485c0182c2d0b50840d42c019201d00350301c2a52150001020039400084107006980c2c1d55409481c3c3c0102d02495101c403002c0701c501c10034200c0e0300360544c0151103810f524600312141952844104000c82000303101c09004024485006c3c0010103075038000f00b0f00d280c060145822050b400d000400e0300b480d0f46a0044c2c860f503030b0310310040c44030381f0f03041d000b11703005042d120706071485541080341800381e404010744030034418031200b1007480090700c40302c8420041c15001020364400007010b04 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 15361526 1250 15360276 15360311
    0xc0a060903050301080d0e0a12030e1305090c03120306060304030903050d090311041e0c0201090b090601060806030a0803060405070c0f05010605040c03091e0305040509011d07030603050d0807050c01 87
    0x8170b02d50390040c5114180e0452240718800c0c0f80c10350081001240908d000c102801c44019400243c04000380508210850703140c1c40c00009050420020015a900e070030034401b424a00040c0a40f4842d03040103070011404a9640e0640750083e0089821aa5036201c5142c2601d0074181544003e110b80100040d054109401c44010401c40b0300404a0202e4908803808000440703000b0040381d20341038000919148814502d40c01014580704a000000d22410b40f92a201110481180e041c02942e00c59001804120390180300e441d0040c0c8140d0080944241036a2907144502009049500540d91400003901c0140f0038030070700080907007100c181480101c0768240a07010300054002d6601940c20300e0203085c40d0034880d00c14140303031035000840c0c0300c2604100d07400750300c40c80c3e1400000d41c10000240004501c658484800b0380c002c3c51022543c2031341204c080107070f100c2020000c0004080c0740c5029000c00100702e0200d10429070388100d181c010a65580c024042d9424040c0521100d1198a4902c1204401a525 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 15362776 1250 15361526 15361529
    0x30f140102120406091e0305120c09030708010614010206010e0a0507021005090c01110c010c0b09011508070608070302040b030610031d0a23030901050307090504090b01030b0612030f0c0a060903050301 88
    0x198040c00b140080c076886d010035110252002000902d080081041404078821200e401105045d40d044c509480840001c0c5001c0d0702d90032080081c1d648002c200b01c4001d0451001100311002c0c0050036003503251010884000b1401032011103525101da0004405510920044520014400c1d08001ca410a0900c15a4030130704c992a080c0829181c60b0b1500c94000c0c00544640d1510051750340c079501508c2c950759010009406800d02815641341c20721000190300b03640215010381a910010f02c045460214000c21141d006003d000034584104000d0081200d50003c4030751000c01a20140111020300c3c40860080c420680b0841400107000b50003500100302080940c0c003240118a45070010b1401e4500d4604002c903024a44815441080140069400f68020303540c4441c850411100042d61a00841c06841103100111030325501400140b08019460302c00b03a41100059613824820315101145507620320801030512003048001c078a2a080c0e034000c10184e0300d401c0d4400300a200b410b09524016000d40c10030b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 15364026 1250 15362776 15362783
    0x501080607030b030d0c0c030b09030a120504080702010e0609090a0c02100b10080c120106030506040f090201080402040b0409082d0703090501050906040b0a020c03010b0a030f14010212040609 84
    0x6a0010603040c0b4480e0050200004009001d0700d034141025000b074996122040c4103d8240440e41d030000301280308184428411030524010b1607880341c0300c14004082d5140500c9103401c0c28540018403010420003801d6aa87c69070a007010705084403004000b518038010712a016a008111008020340c2c0c1206811004a07240141c0803204d1882c00c8000420035a20560300068001c000302d500804a42d108420907504000c0006043d071810b4110440c030fa00c009801d0b00720001283c0c0701d109110060800b13104080d2203003180da400f00044805580000c01842c00503002a00c6280c41d103400fa04036940d03941c0a848120f03481454582c5d85d01d081c01845800045111000100361940100381051141c1d4104a07030000c0e900d580d8100c42182454019030f520740200c0d41c8035400101c10702001c220702c6000c1d0b0040c0010112a001010325202d450109802d41c0d090742502406026500340420005014a148400715584a250210030b0080705203400e00902075089902d950b00a100107001c00d1000350303405440421300 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 15365276 1250 15364026 15364033
    0xb03010b01030209090c03060a0b0304121407050a0308060310020a170601050f0304060504030c12082e0504021605010c090f0902030106140304020a0e010803040612150b1b060703050108 81
    0x34000300540490040600310f80c0c018044c0d400149907001d180c00110f503c0b0200802c5070740c040d526100000c9139070300215000c680d190141c050a4003242c1d000071000e400394903043c1c0703050f1401d44a40d03106911400c1c81c850003020b003d4614082a4540e40501c0360103540015400215121444050018080c8000290032000c151290000c11420351044c4c0803258a000c640348901e155854640c2c540004010040c0254200300b04401c507035000850601225048140640d5040c9071402e11140103058402041d40d0542070700060301c49005120b02070006441220320494005842e903480c410035903036920707050b040200f00d07501c2c22201e404580c0d0004072510648030078a11104a0b91b840302c00b002c1c1244800c0c060315000c500b101541d1680c0030031003801540e0051014042c601c00039628402c6414081003a0852000d07a0004942032280030781c0460004009821100b0a220b006100c121a15441103503003c3d83d4101d03880052028400004507840000542d40c0404440d400d1a00d43c0f00100100000c0c0aa01e05500 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 15366526 1250 15365276 15365291
    0x7030305060d0c05061e040b0a1b02130b03030403060c0305010f0603020c280f081e031b0310180501031103010b0901050f0d060207050102070c0e1521030d0b0301 71
    0x140515070540c42c5038802400800a82403904100b10b0b60002800920920030511070340b140c0b82e2104020b000284004048640c0741e01c094000500080c21280d090308000940b02c0c00c2201681d51010030a0501d0b20000002501171502404641188201c0c1c0001d800341c0d0515902002035949584102d040743c072060881404a907c48034202c0591040750344002c242c1d0b00800d007201840003000c6800c2c00040d1810413000d008041070343c59202c0a012000c0c01ea6450030042012903d0200c5100d801000280400c940c070320b1450010031508404100041c0301c1030b2248048005820940030031020400b41c00d50010209a80c1c0c01c1c0485030020705403d0004883d640c0c041852078000f401c05025000703e80b040249404416070820302400450054110316561103550b420000307010409904c024032000e80110009603840c0350605100c100c2d2160b80d030010102421080800078500400441200d04030700c11103032134a00e4001494140060200103240c05d03070030300002400e01d031000019800507400f4803040d07000b4015032 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 15367776 1250 15366526 15366529
    0x103060b040b040308131d0703050a0209090a0902030109021e01020c0d080a0e03010204050604080309090f0903030a0b04090b1e01060305090304030201030b0409050d05120105030a020d0f0c1a0703030506 89
    0x74000d40c41558184002403005200040825015110301d4403400721601116665481d450300140c07040540301080b0704904103108605502d0700601d80d2002d142401949082d055030702140810000914803102c02d96103464960841d5402c0d0448158190024245442e14001c40d4000034017050b04660a030251007440f1003003030b56080c1481e05604807a08200810b0508501540c140d400344840d0040d1036141d5030070400426203136544809000544941e0b0021501d856502041c41780c1900c01602c11510220650108000c1074030000469500410015000c80ca00800c40003040240241100c01000170410100b0000445c0d80150741200740a0300f21484211030b66107503070540450300c0540e510481604100024070141d4000c1c0c10424840001410002e11880f45803645801c0040040404001690001788007880b904142c1d001805480110f025000b24641640055040147e9100042850031604148810300601c80d16050013000d2415a801a03c541c20004031116440305604402103850070000c03e655 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 15369026 1250 15367776 15367799
    0x40e010f0518101a010e010c05010e071a0414130908040308190305040201140a02070f0e06030f010c05030a09140109050f0f070e0601050714010204030819170c1c02030408030402010306 81
    0x11110100f46135001844000045440e965100004c5050000c202008000a42c00740301e2503030072607454000342c10b445047c60788440020308010000021070105000070f11403000c07048084030310601c1c202d0307107084003040428014016005840016141ca07401007030000900c0310400040030040c00e1240501c190034440f00d03099080314015623001e800502c2d00c0300801c5182072200000c18030003582d40100c880440d0380340485101d501c0745404c030210a0080700103210240c24100150540403c108000b4070400090400c0144240401040b1041c00c3c1d464030b0340381050100681402603022042c80c0284040d94650400d10703900c040b015040c41c0d8134854060b03c4021b108020850406907840481f480c1c1381501c0701001141c0304d8204400603030b4603404030300c00072840c03000900c0140000e40c070035104aa00c8848954440c1c040758000c41d419424044030520406008502c0c610080d404600c06014a841d2046041412101c080c40c41c1d107800154070000500003401100f101441c07103680300342c0e018015103071a00f010000 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 15370276 1250 15369026 15369041
    0x406080f0412030209031614030609150c25110f03010603020d1719080a1d032b06060903060e0a023d050a1d0a0302040e010f051810 58
    0x10344840c5080720403140380f081e00101003d5400404403081551034017105182e904503940000210325919501800604043c0f054940c040d01840c041c0642c514180303181510080024503a515280c4c00003070031001501e0a0040c20f5004c19150205004021149000203e010401c02e28074407490111069040ca450140103140941e0741c06099061540d0b010354551070840700710300d030301c0010010070721944203500340700c090022801c007103580c1c0d4511500b403542e100400c84002e515801168911030000c0c40780004000200c60402c407180d01106140d030f80742c80301e0142195003401c65024550500b00001560341c0c1c8094024280c130f0050204004407209018116038840007082c0094101c044500f50b40040c0c4580390078001071005001e662101c40185124202d4019416000d00012a10100380d5240b00c0f0381c44403000724a9a01803920800e0081303c540068100340151000a114a44608001e140d050702900800d041d10307003007003041c0901d060031030380101c8001c51800c0d16800e42c03062190084840c000381c0a00b00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 15371526 1250 15370276 15370283
    0xb0a0608070b090d06090f0f030e030a0308070c060e01020c0f0705031c110703080d0207140105010e010512030909070917060f04140f06090106050102010b01170117070b0f0406080f04 80
    0x7454048281c3c144260110b00d00d00580b24076030340d01e4640001c64828800400d50910070700b40190307101003510b8068151640000264001d602c003014400001c0d030001c0d2480d400034160708141c14100168030309140600b030300c0d0032001003550020954221100300011003401501c02e10044d205180d403107405240e50b0312143d480c070001e402e40810040291501880083d4100d050407000c0e80c1496481703442c3c0c0c0500d80c3c408809000d40350f0340022070340309000017929070110301921a40240241e514104107885082410b020740340c40b90740301c1245c00c003441e08104125803041d00e000d000a0382c9860030f00c0d0b000c0e056080c0c03881081c0800c900d01c01c0b256003140340400c3c00f81c03080d40c1994800c02161a503445019041d618034045050314032405c54016180c440c03c10035144a1741c0c0f03020003c609130341010002030a49454040d6a4103003c000800706100134910f0b02e140b810359036034040c164103410942c850b552908283d58080c1c50003040015003404003c00724802003064581580f15114141c407054100900c000c400c41e0083c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 15372776 1250 15371526 15371549
    0x30105040507050d14010e0a050402010804031214040b040203060c0a081302010507020904060e0106090606050304080c190308040302070605070201050d090c05120106080709020a080f040804030605040b0a060807 92
    0x188110315166115035004000352030058203050700402c0e140c007150348103403010781415500c1d401040743c00d260a81055001600003800d0000c0c1c20503600192070248080c10043c144120704c403055000015650143c03680880c0c2728136208041c2840c3c02c14003603081c02030354264060b002d2031000880e144004011140740d80b000e6035a51003103540742641d10821502e141b40803070410070204070000260703031803920842c0540d00408000a420031680c09107801c45e5100d5100c000100d0900350704000c50742d081400d0744e40c0640c2044020b0b039202c162a045500704411442500e0980311140110401c0c9135112114501c0740e88aa02200c960070f84071030007603946002c0c0c100000d002505c1004002d03400c0ca1141c1040700b151f071003205440790264880d400104070000e00380551000da9590a420800014108540d03c0248103c88045140400f8810003c01c00000207207080c25000781d040121701000104401c950056820550800103814240782c62240d07030034143d548082c02d03400c0050100340d074070000c0ba1101c02c41e1400140c4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 15374026 1250 15372776 15372779
    0x2c040b04030509060d0f020315010306050109030212161d07080411010309031101050a020711180f090304090903030203091e030301060f021c03020903060c0903100f02070606030516080109080301 85
    0xb00c81030343c07114208030b42214040c001d0004c0313540f86008240b1410750480c400b503201d01d8076001c1066035007416100c07141090709190041100c2e0b6003000440050b240c050341c00102618100c0d044070b2500c1d4201e00301c403105076008440012281045801410120070710b101490250702c544030100d54a110030768004c1c150000d0403145001d0f56006c0c1d88070135100c038400d0a200030301c0380408510b41d08440088460080c0603800061000400540e859414a4540122100d2006107c0d0700c2e00360003103803001040140243c8000e008200001c00c100180c400400280030113001c80036070740c50001c000e0b420075601c80e1420320034000a000700351205901c072401c00000000440c110b07845c2043c201e820345c1c545a8028258000c00ea00003800e407081442078000d06070b16031400b60baa640c0540901d0316142d4000c10a440042c0140410b4429690210740c2018012180201065030701038100000020322442c03e00070016403924500200300140411540400c0342c2d05a004402a559081100e00b6108002402403411004100 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 15375276 1250 15374026 15374033
    0xb190f0b0307020c04091b0b1c020705100f090b090607080a180503040b0301031a010b07021003060506030901290306010302090705070203070b18012109030e06042c040b04 75
    0x5180e020348544104d0300c20a05040c04101194207040341a501e90b07051032100c01500e228096804000c1203c3c0290030f1034a85600e4500c0613101194919403003a60300001c403031060003001c00c042c40100c1080c50003000814101c0106900510b0b00070400c6460107803800c001440e400c4049456445a90310703488021290381e071005c14400070b02e1900c1410a19021004005000c540704001810140c009030032075a82d0795045092031801c1006c0d080c3c01442e41460040103201401c48002a280c0d61907050303540140045a402c420303405810f5035081940c01081c044200600c2c10015004101c12000640260001020312030492403100d0504002c15050341c0031000420040c249000115800078441c50458180035940c0d0029082c080b42c0e0703003c12105074002c20414841c0c104c04403907031448802400d0600350024045607005c03000075184034035100295101d9001003410301940c1c00410030107004060a41c5c903030301c61400040000038400e4060000745003148a5403c00360354581e0f11f009941010324028903984a64 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 15376526 1250 15375276 15375299
    0xb01110c12030f07030e12010c0f08100e0903071505060105090d06060b0a020303040605070503070c06050604060b04060302041d060a05220216120f05030a02090a180b190f 75
    0x30074000c1580710402144040c4000305000d02011031203075444000c0d080e03901d000c0003d19904685d40c02c105914280c409460203800900e80500603440c5d081400403607175043c6042129020b194048018a035003c420008082c00220040040c00d02c00c0560000b00d440c2c000c2c01e0f5085940481d0f14a000c500704102001c814604050110308003403144001240c0151503848603240c9800400421000d40e20100500c0b081004501a65511501a03d0003a085180096004183c51440ca2000d0324171070b030701d00100751191030340d40055000c0d1000501660b5502c1d61180000c0c020340c05482045900404242d15103002c05500d03680c00d000d07010040851001d58107000800c913601081c02c11041814015011503103c4a207180041c2040c46101c0703c01c403185580b241071a0070003c00880d090410016a550144549034018080e070342c001c14416001a1549100004568145a113400250031a41018500341010341d49400c00e21082e08182c503003454440011260855100e03a81c010520301021001080c0200c81114 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 15377776 1250 15376526 15376549
    0xc0e030f070b0a0e0406030f0309150201050411010c03020a021906030b060711040c09090603051e19060e0a0f0b06010207051503010e07090306020703080a050705040e0c0304031e050c010b01110c 85
    0x1000010b031617176280c5d14034108810083c8c04070042007030200c013003011019802e0440340c21740b03007400248090303d050740d90258004031384c15005040c8009031030503c1c2418070030403240864036800390180680c5101c8141c012005c0065102c4c40f00000e040c4330b00004035050060036584402c1d0b00002101c5200c84850401010388194148001002480b080004d034620880c011400250b02510281140721116040c1d04a19000c10096006540c41044104180b1041990703e40005400440000b400c0d020f240d000783c207010540784050191104000e8210a01c10221030320340c040c4600f6002c030f0342ca044d968420b002c40080314103181e13a2002002e10041050084624101b17602c0507480c0303009007001c0e8681d0744001c101c2e0000c12080d00002c2e4144100100403520b03104081e040400790400600307191030f0882500002e480148142a00030020020804250044c0c910085901441443c00003110424100400581055001c44499802d0007641000d9500415000307602e40300d6000a081c29130101000e00c08045680c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 15379026 1250 15377776 15377779
    0x100203040611030a0605010201060e010509060d0809030a081201060207050303070303022a031c02030603030d0908070203010204080d080105100509090403020718061403030412021309060c0e030f070b0a0e 89
    0x6803035020014010b014001d610a201041000800b01d050900081c216036a9400113401c03251050010301250b40c07022840f82d4060000c0b190400200da442c540a0054024803080507011300c80c011900c801c120340403000d442660071240d80c1500d10ba03a03c43d42207a82d00e4003481880e0b00b58204001c03440c082132283c0c005100c61031047d840840c00540341d0460907504001140216810317000412203150b03003042021305884940307585c002903041d8204000003d803680300e480c0d05014000d60355401041000003960568100b00d0700240210f44840d507810780180c4650a14003040c00165041c80045803a00e03004200003524241039961608041c0c4d18814801410005402a002c1d40315501001800d07030440f9140c20725032003090b44040b0b80c084c60100c518140401085d501d910a0b0403c2c00140072500700500c40311405074045440086100c05494180020302180c0c001800070350902c45513003009900000624039400c415001c4407031605e228940e20f61074400c07501810100150801802401c0c603c9625401c3c100c110 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 15380276 1250 15379026 15379031
    0x60917030f070f0c080a0b040510050103030203090607051204080604050d14030423072d0b0a0507030c0c0306090b06010e0109050f0307180b040612030509060d0b18060a060207081002030406 83
    0x21103088041c07415020f5001103c1f03521404080104010040c8200c49013000e00a1040c00035504580d0041c0d103a000703001446c3d000c0c0700302140320401d2100c104196910412205501ea84d0f99882d05460390f00c0d580d0854041d01d42e481180034002d0008e1044101100e040d4403941e856056444560b0741504240407601005c5800e05191042400b50a007480610000c00d81301103001c0712581503495085502c038880d440d413030b00380c201c03c0c0041100810420864048020b9846c0c0103031b9400c4545010703a13100031840342c0900315990300744e8080100095948040802d600031280c411103135541e03600454542a0341ea00d15400128103560400c40303400c220002203d400c8008040d40d0913542c844400c000302440000260403c11780321a071038103050a240c82080090581040f85803034441d00b944002c1c1681c465034010600038007001078200008030040d40001da080c1801800102511080e003054144c10360700780c4007184180013019000400c01d000142d20021500070102501010031900075181c020b400040080e12a41d4 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 15381526 1250 15380276 15380279
    0xf0604080d0207030501050603030a09090c1e0206060301110f0a0f1214010e060d051203070203130e0a050906130b130203071710050609010909020d050106060917030f070f0c 76
    0x180e051007410440321039a801403150340e1450405609544010341018007a400070059900705550041c818400e540c88404049480c0324511002c80d8014000e000c002031445014903c4c1c902e142c0d0105e0400e0107024120001d01000140c0103000c511486545840311060200304035003002c041c011031a42c01c00382c10b20b04000820320703074110013070b400e030b078000c8540d018410150001404240040740400d0b40001041e960254003220342d544035640d07217000c13404c1b06403904000300016003928402c1040b64401101c0181c8003e0305551400960b210240c10344840c2c0c40182080e0008000c4c54000a80314030603280800142007074a42a211210010300180c440e4508034000e100c205d000d81c40c01c11100005060458140307d03009000f0788800d00b0052202d41c074410003410b001c10301c412944c4840d4054150340030b240002540c480d441c80010b040003401ca000500f55401c0c00000616280c0001c07003003045840d500802d8903500c40d84541a612881650414100c85a05010f01004644941d03004c2e19514844d518600700103 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 15382776 1250 15381526 15381539
    0x80c0607030c0507110102100e01200c06130c05030d080106030e010b030304150509040c08011502011b1101240501030e030f030411061b0109060c0309050c10020c061818040c050f0604 80
    0x40320000e1040d28580c2d11040a0094407040c0c0041c40c0006042f00403540c140361454164a0700c1d400045d10501010f1400003020061188001741c0034002c01d4002c0131924525003803640903191080034403558002c43d01d001e030380c580d10a506000d036801d0a10024080c5203040d0901c910902e2801c1700c0e07500c03281000b106002c59040b94641744a0490090a292502c0c11250301d03003800f032007010514198002c11a414860441d0f00d007036031318a12070020140d03030170004054030042d601d2b240100754840034018a07a50712071020342d00409142c028016240e0a0b07078148044406410055503034820305242c0c200580b0704000140120780c451001d10000d040040000e80ba101c081c102c5007900f0a40b0351602d8103103942d41d035000405c02441c0e10075424410a20b040030f00c80514940c64240c0c40e440c210201c14000c1110046030b02103d4828030425109180040c025619942400c04201c0c0c1c003140191003600403814180c5101d007580038001c200b0f2080d98444100000703241040140007811807019031481e003200d000d02004c60305 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 15384026 1250 15382776 15382781
    0x41b05060705010501080706110a110f09040c05100201140109020c0307021503011806080c010e03010e071d0a0b060d0207050304030f0303020c060a0209010c060207050a0b0103080c0607030c050711010210 89
    0x107450007800040342e55410b01140034140081d9601c420144120031440e10300f040700109900c6186070300076000d50203ea5090001c55980e07244445041c0c0c0c0304103210304010404c0700f6406040e00350f0310190b89144d408607a40740c05034202c518035181c4424500c1d0705001042000088d07001040d0b04052442030720b062212603070118080044040c035035010088040018845a0202905d06100844040c1c06000003480c200049440d400820301039410003d070109004c000340c41c00d4011002e9421014101d500742955444428208012200b00804451905011404000c1203000b91018080001c00c458601060404600000c0d03000d43c000300c92901091000002048142c120341c0803840c02514056070740d10030b4040c55801c044d0000c162800030380c418000302040780d038001152868240d10080c01aa0303a122400c14a16002c10580700070603c07404031001104200b640800340c201c02108804540341e5884200068041d20b92900280002031024031940300810703152101c0e036440b210706005503089008200810f005 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 15385276 1250 15384026 15384037
    0xf050904051003081306020c1e04050414030a090501170106021509161401031b0206060409020f03011b0206010905061005280f020d020303010e01030b04031205040b040c0b0a08041b0506 81
    0x15141074185d0704202c400d405200104020324120740d10904500400364081d004032111207028040d5070340f0740c0020701304030303045151117003400410342100c1c1c4803800d10348010314134041401010300150100601070110340103015080e05075010741c0c011740a07403a1150306011510f10000c151040e540701e41400d20880900400000c4060844244107185620031940050b080da015640c05814441c2d440600c201070542c0468a40d41042c0201c901060121040c00025100b030b01c546000c0f60b05501e45400009801e80e6240c6807641c04070a41c080d518070341c0e41c07101d03040200c42040b01d01030b0300804c0d03666000794818440e41c02001501040c0710300c462550714105400c0021030107007072048040380699800d40c070480c2d010029445080d110348015495581410038000c0c142c98103203c001c044d600c0f04004541054000c155000700b41d00c000004202615050038503c15100c02903034191142172542401040d060904030444001144548034000c0d107843d656109030510840c0790380710b001440321900101e140c8e540c42c0000e08 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 15386526 1250 15385276 15385297
    0x8071407030f080108060412080907050301050c092106060d08160f03090902040b09060f090303120a060911180102010b060408010f0b09060d03051617030411010f05090405100308 78
    0x94426011480140503030fa4180c0003124640e00500c2080005091030481da04041c0680c035081c08152075400c54a49000040e42085501d54242001c0100742c5580300051300c440c6904071611504003001e0920141c64507c0d05004014981100000840c0c50420012500c4040c0c032174090580f0b00003046220b0107a00607041011075074903403564200000e02da07100340c1d00e4000e08400c003021842e252510f00c12800da4031611601034003c0c03401045a480d9511818243d40f40020040c042c2c958540c502003150f0400748084411a8240d440e0090104200300ca40c07060351028804001c1d05403414800d804d40e4520a150318651030b0440d92a9252414542c41d1440074000926100001040c105051400003080d0f421252626014080746010003945941e0018000043d40d010b0400d070340d94500701c0c10f032401d50740c0c00600050322180d850020044158440c1000f14826401201080d0351501d900c8011100040103000500010b0b0052043c0c00c40f524180d40107036005803071000440e941c1640d075502c00752260080b40c5c074078 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 15387776 1250 15386526 15386537
    0x150606020307050f0c012001020409060b0301090c05040311060711120f1902090103080304060209060301030804030302100618110d05040501020702030d020a0b07030c020c0a08060114040203040506070807140703 92
    0x40c020000e041020301400071301500503012407060400000c00b00540000340000602c81002d03c2c005540017907046501074040c1c014240b00c8076480781048441540300307100c3e11a1240c60030300071003507592140007a503041e01e5000c040b40d680c20302c0103c00c1040e55007005c00141d030180c43c00303401544155a50145e82c1e404050300e50207000c4104000000c14141961700c800d082d00c00c7d80d60b52803400103a44511120f81074940c044051380d200c1d115400c0500c0240201e060707494100360008008400e01442201070310842c2d11940c00c9078640604400c4080c03d0344d4a0380b1a10030800e66151981c0d10600035174211035280c07005100c5185c1004030300b03035940302510030654051390346960000303d44082d41010720280300c06944034001024800e10742d83d100009040020b05900401d0350307407480040010300c01c0c442d081000c00020720210350941c070758130076540f00c0740c0a20407405031052120001e2241d0400c1e0080e03a00c500e410070040d100c1c0740e8503c1801e581c00c410092804c030401c03400c142d46289617144180909211030180e9a05d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 15389026 1250 15387776 15387787
    0xe0301141504110904090311010e0307062403060c050f0403061a060a020d081b07060c0801080123070c0206030c0406080105040504051b0307050301020a0e030601060c05070605071506060203 83
    0x203a4011024140305500660801e403c201e21403000c40f084420701c40007610001201e41d100d0404580c04003446981c1103080d420700d00b00340d144c040c00002400d101c0c1d00031101002512040c62111100d000800b080d200038256130711042000c5400c0390b001040ca001603080c22071400c5401c0701c4143c0c0350751064004965507650b510341004c91f142d54001c400318a0340e0a4616520313041c04030f00c02950701c200d0720300c90008100c0003a00080d0f400344402c000404034070a81040d180c8818261070f140000e091035540400c005a101d100002d60360105024500300c80e0024105101c840244680514211000805685c01d2141e100c440d03400603103901c0020741c8540d5001d281651540d0a0400003808601d060703011500c19400c11b0700b8880441c001040340c20403210300c0c890048017000354202290511b0802c0d408607070305520228100d0441500400c0d21b4841d0f0004170305903002d0740c2c0c8a01080e2284458204040d1890707100c1d500070f0095500800080007044e0080b1001c0e0313404e0454192030bd054940703641040006800c080381 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 15390276 1250 15389026 15389041
    0x30c010606030e100510030803280606090302060705070f031505061909020313050105180f030a080106120603020303071518020f0f010507050102031003120302030108060c0702010e030114 82
    0x40c00080d0450307240038003d400c00f070f503030140d0b42c2caa2442c07003c510f0980c1c1c0c1010a002c5010f03000100010341d40482d03a5505d07460808802c0b03e0400f0491318410350f1138140311035003d5a00301ca02c945420345080b070f11038a00070390a41e000d001d1240c012440803201031298440102c0c5c0c0c0b102200c85c4138001e5202d0501d01900c01629a074070410b441000d061103004410702c0c040300140c001b03c4196881031b100d9603000143c490f07490406801d0040c88660000d0119481e103014411507034515503002d007502c2414021106407a1185c0a21540d912440d4121030000311000010300a46100d100800140c00642c0000721712a500d03500003c2c00e66008c1d400895101c0e0071040300301c840402c2401035000c02c540001180c1d0311701102ea00400d101441d0b11440900c138403900b52200c13030b41703a008206844015800c480219201c6c501000c450282458900096400003040310000e400b441c864000c81e4140d4030b864000e042c07207448480c084030013900310800880c1401080c40180060740c500340700c2d20009103da0201c80b0458200307079a = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 15391526 1250 15390276 15390281
    0x2041a03040c060f0807050702030102070b010b032a031501110d03090c0905100b03100e0405010204081203070504090911090907051201090201091503110a031a090105090708040201050c010c02030c01 87
    0x1030000d001d100038081c40c0f44c1076076045070075640d1003c0c00b410610368810003480040c1c028403480b0360041c040007802c400421045280e4010314810040e041c541b061000c2c603000041002c008180340d070321004104000081c640f10f181e51041b514020103041c1211401c140c0c1d1900350070803002c0070320400003c0c0d5420f410f909104148449000500c100d180802440c28a5003503222100c020303010712101d41d00008080b549051842e0f0780403005102c0540c0030610750400b85001400703948244500c0e40c95218801004030b5003c20300d0120790041c205c0b034403039600e49031034500306c44081c11388c551007038500742c1115a50a1050300c40c105907500ca03045180c017504005080c1030400c48240780080d500281680b62204090040c0d82000c20386c1e01350741c9080402c040703042c04072408602400710781d60038005003a0702040c02c0351003139056003044030f03c004842c00701d604040290341440803103003007441141d50103c1020040748006005260154004c3e00601d05189054401d480b00b500b0b461a8048606c01640005201254101d003071 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 15392776 1250 15391526 15391529
    0x70201080f0112170d0c020102190f0912030201020d051305010c021606030213080106080d0207050402090d0f060b0604081f09032a120804060e06100909020402041a03040c 75
    0x200041c18455040c060400755003c0708803001085007038000004950802000c0a0300c00c814002081480720b0380b0500c0303000b4040d4200284a4440000c9604609407050082e880402008515514401c406182011103269070500c0601602955400c006d0b500c4140d10724001c40d84581c400c0c407107000300b8a401e40703802c0d8216004c1d04241011500810058201d0003c40e03080d1104070b130300d207103005a101d40469900160704d181c0c0364045120340d071030702800091001010810404030348040d02500d40855442e0b00b07001c03c2e40b0030f01c071940d6400f4a1010303410f0000f031080c103d904000c40c02031000003400b402810104416034041c3e000340340d895000321040c1c035510401c10310b0403800350100304040c0400304072aa005032864806c10b1000d1a030a510080300c0c01313105030640450070019000390381d0b6125185101e074040c04a07103066405551441c101b010b2003822520000c1c109000b18058200541814548000e0b400280450b4008a0b409a001c002c0003681101c20f00300d40d5208403403001c403141e40e030030107203480000c00000307 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 15394026 1250 15392776 15392791
    0x120504050f01030e060606070302070b220608060a06050f13030b060312070c030b090a05060415050c1303021309050f060106020f06011401081e0f011802040803160c0305030f07020108 80
    0x800c4030342c41c54480b01054440c0c06c840c00340c86554035100c4170700c0c0690030000141c00007104580040350b00c0c4221b161034003080c00d2007501035042071030780e54884804a9801408403412600907d4004040080c02d120320001c140c24448001441d04096101e11006501c00e00e551003510306105400510016140c18090171700400da607401d40c5460401c0c0c42d5207401007180710b84406050511254001038090006210030010180d21409444c1c40f480c19190081d0701e01e102103c1d4095071071801001818a52440003110841d94035403104080c85840c641c00c010480302041e003205230141c1c071000480002a0200540c80f6503c141030301400c10b642c10490000e14190f001007070340f01603a00500c0100008010203591120080b02803031701c100656500f807800100a082c403200e0302c0b10082080100a51000325041880c180c402c6100c3d02000d01d078440301d00300e09900850181034070a03041002004042c804920091000c14410040d000c00d03156070780c8400f81142c1043d0070328264050300003000011580c0c4840c05c0303540b0420 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 15395276 1250 15394026 15394031
    0x905240105041a0903121603020d05070f060506060d0207050102040504050a020f03040b04050309061204020909160611240106030e01060b0702090402030109120c0b090c0303071e120504050f0103 85
    0x80d100c0c11420407600c407241440300d83d80008444559032400d00402c030080c9140080e140d0780703c1800c007008104002c2d0500a40041c01407801c005a09480340046500003070708498030700850030440d1680030052502038155a0f000c0c100f00140c21140b06240090910135001d9400140c0799403070b01061205070ba50003044501e0607841000b5628000c01441d09030381e08030340c00270104461561180340c41e902d54480c2945455001c50003045005035110890b414a11540c400d941603501911464082a900c646070008100000702e0020248401440b0380d81c0c0c082c10251a4040b1161185807200f00c25100c94542f410520032103001d80140710141e0076000b03c483c0c001103c8020460b552520007606104c1c000c0d03c400038810842d100c04141135503001d400400c1902d4001d01086100d041c98031f4041e0042000e4074044800b0002c84000820110000ca07aa561400c00903029514145a641d00c01e0090082c1d613440d414a070a5a60582010410681d41e4010b521b0702a1a085e03910750800e000c120320750400e945864109070 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 15396526 1250 15395276 15395279
    0x50a0515070305090616020f030f10090302070f090c020f0307120f0e040e010203070e041506140403060c03020405040e03090109090506040204030b040f03080610021504060204090524010504 83
    0xc44103900e1030300140880000d980c540016140468141c80741c100c1040d88088007151007a070030000800c603040107074400c44520480e05840400c5c19100d003842c0c0800e1400382c0020070b030300305804100d030130002040b80309206030b580301501d038042c102e052102500101e52040d034985402690940420003084c0d4580340b40b004500b4400566104207584c1907402d104010000010b9400c503caa01983d4042da00c080000c1013401a2400d89901b24000d400440704e54000030300c2d039001101d0780c0c01c10344141e103a80e40d103032189020020300b00003040d140300f02c0719081c00300d140d5010000040400c1c040c0c807508507203080ba81d4015035154500401c1109854025410500700d070402c010180c42c503a0003111440c11981c641c280851142d54a90014000f402280e0003d81404400402c000030401055800b05601d03110b81c403003c00c2c58a8640500c81411003112100d40964000d004624800308846070700c56026200e40b10252030a41c0f030700100e0301a15829650820716100084040301c8503802d0509a2507524420300c0c0c03243c00d06 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 15397776 1250 15396526 15396529
    0x604080307110d05010e060613060e06060703140d0e06060909030d0507030b0a0306060504060b0901080c070c0312020f0105180307020d020613120507080111121305071e050a05 77
    0x2442000402402d0025082005a054440040340f07039010350010000c11610340488401c0ea120075040307440b588a0600300340c1d00c0c24030741403074460701e0b05460010314a5011075803072000340016588000020323024407a016006049400c40c0030018403807408848c1d404580740c1e8440d103440f0b2410a0140156208210310010000400c2002055440b01c280100e404035079500c4031003050b001080d05030065600130000802c04424050150000d008407882a502084090366910b41021240908641580001c0f50f51020405045010001d00a003902580c109403141d50b40360383d4a40c50029130189070007d038000c1801d0340181802842620360208210a0740341da5045003412058691281d80d01c020702c148200150901951213245c11b8802a00c200c80240400303685901441c0c0c080000703403008070744603c83c0102c04200014103006a40096201662950a0107040c054031208200c3c020071441118421102030400f00c1c40801c10100200703124101c40611552807010400c0d40e414030b802c4180503c0c070070101001113 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 15399026 1250 15397776 15397783
    0x20d080c0a030b0a03022110020f0a080c0909010f0e060a05011b1406100503120702060d0207050f120d0f0e03070308100f060e010f080f040b060f0603100302030c060408 74
    0x6081d103516002074040e0503080041e407440225000603400c004101c0071403a1981c031020032904e00400600440700c04800e01c61000c01a4850905040211842444100103032030050703030b40030b42010300e884580b400c140c002004101144002d0344110b4207254401c0d03082000b10346030810960000c0d41a00e55200160404002030100704500c2c02c04402210842110b030103100740d510710f007079038510b110099804500b090010b03049050840d0040c0ea05c02c0c00744030074141003d000d003003c80b034900d07070701070003503030810051240c40d078000c0d0085101540c0c0ca00400c04c000300f585509003c0220311802c032110305515070626044803801c07250202c19001d00340d03180c1032600102d1178000054641481e81454240300d01d585444d12121000b07202c0e413081c05a00c0300500b022400300e401c040040d945110a0f82c48502101c4084004c40d807a0209030b03401e000220a100114010074880100c0340d50102000d01700212a0617180041902ca85c0200c5009090300b402d0300c0140b04510b0709001070303041b031031044400c981864140f03e45a500c = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 15400276 1250 15399026 15399037
    0x1b0507020901061407020a080703021807021207020411070c0608011e0504090f0b09150a0605010f1101020405030313080c0406030206030a050a090b010902071a01062304050904050d020d080c 83
    0x240141454604c42d0300d189501280c1013598094603030701075140e952803100c0d0780b9200e07804124403c11148580402000704040082e114151aa0040c50b0b09411102481c2d4a940250310036a0401d40b2038415220000d100001041d0481c840d80100c0c591501e4251700034118481a0005607825840c12110180c1e00318003500141a10700c11140024155600e1a1882d05c243c0e90b404000c0c18588544100480c1c2c000104001e1792800740065a805035a45648011084a40c10f010f001e010800e820859804c0f00e02c928040082141688001807605d601c0c2e0000a1031038001e1000c0c042c102070a42c00a100c980820b10a84100746003c1d1002e005c03280c01d540c006082030000a056010b200e5544000440544558105482c61078100c54211000c0d6151601782d4042e60000005a410910700070000f0f42e04c6003850001412103403d651101080032885862104812000d1080d07505040d041c44040340c1c4e41e48443d4014040c1d4494402050750403100f200190500d5108000041848050b4003000f8000300c400048a1 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 15401526 1250 15400276 15400289
    0xb010e01051e07020d0b161b080306010207030602030c090f09010b160606090207030c02030c090105150a02030d1112100f030f02010c0f080d0b0a0315020f07151b0507020901 76
    0x20b101d22091484040b041c020054043d60040b48030901c1d03010b0056160303031140108042e031041042030107510015100c080070542100310b400b680054240100e4211030217940c01060503c1aa445242eaa44907007046c1e030000e075002444a140010309d01d0b803500d0800b240c00500c0d003042c1d80311a040c7d80f5102c0010541d000d8880402d04500c07445080c581000358590111010b0205540c0c00c40d1100380c2030500030400040b20804034040c0c070400301c017800545400c244c020304071071008110b05100e07101e0300c1600d0010782211003c00103600c414000c0794554041805125070380e03000c0701005610b4042a15110030400c034040c0c0152510380441c0001d1044054681c400c405036134000c2944030b9908901d02c0101e42e00965004068800d03260803540b1030070840714400401c10b40b141c0358024060580d2400800c2502101c1d8400204181c8885004045007403071500500358800c1c0c000502d82c10b092043d266984000300603a540c083c8d566403260550341001242c4a45c00c00d40380b00313262480c1003122a90201d50644018050103 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 15402776 1250 15401526 15401557
    0x60c0a11030f120a0318050706020d08010504020c100e031608070204140108070504110f0a03060305060907050319170301030804030c09020304080a0c0501021605060402090108030a2c0406031101030b010e0105 91
    0x2007401e586c42ea40c0c0a070401c0e4070001b21266295526402911244040080d1000614960000510f4034090080e58044002c0e2800b1b01001e0460020300f20052800400d0304140780001d0002050911801036690000c0d40202d0040350307164218810001101c0342c52000b40030450031100103000403c800110348068a100390f81c00200068010a103011901074012000c40e524000101548660340c59000101228411002c0310501c0d101e8041d52507c070cc2d102d0040980640c4204200282041110404c0031042d01900203100e0b47c110805542c10141c1c8240c10942c1d40000006040080016002200c030080009110450450a01341d484d081e16100d003003900400c1004821051040c04000e41c1141d101c05800a450f50000e40646011501c0300000ca8003a841220440b0000900d1400481200c03005c144c4c40d07032001c10030280070401c0d51302e80c0c201c000420800440301894031201d4880748140c001850003101c612000d050700000040649038034150440c10006100d000805036604117041c3c61104401c241c40 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 15404026 1250 15402776 15402791
    0x20a0f020109090f0b010f110c06030a06030807031106010e010303080711010e0303160e0301060501050301050d080c1207060507020d21020705011b020d080606090906060c0a11030f120a03 82
    0x101c80c1402d464001000d25072424081d188111030743da04c0401032550a80b00ca0340e0b0b882901c94140c44001c0c0e62242d00c040c5410014420700b0500c0c2002c01154800001d00c0000303001d548940b60700c1c00e5500588021004102011204040340e102040744034010102036800c4400c940c15994000c044610240000040c026014a40003a440c07081d0841d8114881010869440380780050210601501e4110704401188408417280309508040c0140026500181c44003490340c0d10706024000000c001c0f10054810910510107880c84c90410302c088818100801c03440e039110302040c103000c02200c0c00a0704030030555100000d949512a0003010066400c0400100300310080c03031001e070840c064070a04600900551800a0310711019500701881c9481e00060b03421210950390040060701d071500300351141940f00405105c03000740d41c0380410815a0164014000600340041d0f8164645805040501120759004106652000741000c10603408141102c0d0001c00070070740413503500e207064890801680308040d22440f5 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 15405276 1250 15404026 15404029
    0x30905010e01120515040c0203040803030403051c020304030302070c0605070f06050702160b0a0206010509151309150b03101e050c0c06010306020a0216050303031513020403030c0213020307020a0f02 87
    0x156a035030400010040c046454201001c5c82c0124021a21502c03c1c1c2c50708145400c410300c0003081c6d4041d22541c0004505e1626140c0b4140c0341078000780040a010341884508403440003050000d94040c500ca5107000da2515000c3c900441c11450540010040100a204010114034044204048150055000503640e210598100d00303152a92803501c1c5010502034000942d4100c48004024112170ba03426a080c81e6296010400e54580980b0003017102c05e01081c00700c10514000c28042d01194a480001030101801d5441d000d14501c4524814200c654401104401d410140200128210920810040f014018416010200c1e100c80140c4000b42c2d07540014150001c900c04807001c111100c01107031015039403450700401a48c091101c050050140c11400190004040c020342e00f5940f00401441c2147c1e280303610b0350505490307005410f510049021100210304018402800558000ea452001d500100d006200c4030340d20409080344558410010820b003264080f0b61910300300d501445980c0390032103600 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 15406526 1250 15405276 15405287
    0x6060405150604060215060f0d03050d021b0c091501140705030f1c0b190605090f130f0b09040c0e09030903060112031815030b030106150503070813030905010e01 71
    0x3418290000b40008020568507000103a0a40d00b20100c4c05016003a9952402d2200d0142c0180c01103810410810718180000d0141c4094171080380110b20042c2003c2d0041454078007070001110508464011a03010309050901c2820307903905c5450070344203080d017515410000784074142c50b440183c0c0001010460b6000c000003801100d2402070703003031000d545422442c1e600000039454003a03100e008a2800c40f00c15210b0801d030703040b404251225102a003c440c50f00500303503556401640041d5000d106010144d440e80d8400003015440c1814840014409038596034003401c4603c509a00f504c81d002030010000040c056007081c4d41a034220310100c01807a02c0e482562813071401035241855242c02040000700d88a403000760172040f0b0f54001d42e28450900300182500324200c2041c0100f09214585441010b28a40280c00c60101c8080160002034002c1d40c55400741d030311007221061a0000303030000090094040d846080c05400c000c0450707a1403075041d030710b0b83c000d000d0140c1b51281505100e05140d070100f150317000343c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 15407776 1250 15406526 15406561
    0xf0e0d140a06021201060905010203030408030411090103060c030605030f0c150706090809010e0402070317060a0801020301080105070908071202040f0e011b0201151412031903020403020a051206060405 88
    0x203008a805400c220300c1c1440203074129258003021116004000141144900280012100f06130040e40c50f540700d5440f01800ca500081090303e04007040001c04085883c1d051466000354002c00700000e134070078a100000c0c16509035034000c2e8820f80c4910b000f0002c0d02d0020554048a81040343c080058101e07110000009000d048005404d4610b4410a6002e126a0800400d01d900c02640c5040c4074054240030082203008249003c0c001864091028006594282016800c034000411400003203503100951820390b4001d81007903100c0e0351102c090080054005039003c02030680e14020f01103081c140180b506000400c3d200c040d1250340c840c1208105a050b2350700455860320940004c0c48100221905580401c1c1e0041c0c40d503005620b81490440c2184c0c1600303041094480e07510446090700070300c3c1e00b00944017290188009080c001041407140010f20340040c0f0010320060740703025849920314010000c10703118139070015010340d01859401d003d1745804600729600036003c031000103e50310784e00101c40080088 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 15409026 1250 15407776 15407813
    0x302010e07051e0625060b0108010905011206110408010c0519020601050102060a0b040609020c0c011202040f06120e0a0b01060206090d05040e150907050403020901050409080403030f0509040501150f0f0e0d 90
    0x15038040109004898101e41003070707c8203807685081a40c2c2c880c01101140c0e001d12a04100321038502c4d100300010420b1300040c00102c03041008a0420351607651090031560002c51383c101040b00084d002c030480010450b00900985c84e4009806207614103030010352221001003c050240b95280e2064440d59204c1d40101c01809451034215203800007043c0b00c50350350441031140c9012030b0340c2c4124004003003840c0c0225030942e03c0c2030946055051802c50181c82e400c035405402407003980c40b100c400e0020701040001d1301d00180200381d05481175242810103810800058522005904400c500c580b100e50444c00300c0342200d1008486604c2c90751041c10748407102484181c1035078050962000c2c041a1076020340940252802150411000e036621030400046918002c0010995a8280400c1021078003030407138040303460140c0c2000c3c0c2c43c00c03040c0400101128402d81095000c504000f05000c502503000c02059203000b0242400c03040c041020402074401002d548000344078400c0d051400c410000d490400c00f58012a = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 15410276 1250 15409026 15409087
    0x12070312050703030b0a051c02040b0607060212010602030a080103140c130501081207050a1e05100504030e06070309051002030d020d0911010215010b18030a0302010e07051e06 77
    0x20903090003009a4030200e4107400103030503c039100ca483d1402c210081d04a41c1c0041c440c000310a050300489001d54400384041c0c2c0d100740d41c0c1d114911581c40d03200080c8a21846500016a1003003442d0142d05010b02c1030300b00c40c045603c18407010b822641c000c5441c82c1500c0d0024244803030b130840e4946441c40d00302c0c3d0b00f03d01074220705608500e24a4031403035004103040e02e95140581e08480213030440c107220fa004002c0007500540c0900c41210108004054005200e40022242c03260f00c912078403494070b002c0043c844234500c156501e0130401070580c04400888101400ca40c083c0c684155903c0040a40e40c56000e094400d07512074002c01c80d610300070021100b4690346500f00355141e03039400c64a00004c0908080c2a51240041c002100407580b01041814190030810180c40b40d0740d003402c05070b4085410481d803035984140035810301300d05594204081c4030b64a120364004510040b200c40301c1420702c0b1160744424000c3c032261045200010b07003e0450607840d08191905901c9400362140c020401554511050404c0d4 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 15411526 1250 15410276 15410303
    0x605041103011506020708150c03070c0519020307091a1011010606080108070503060c0a1103040308030c2214010804020d0b0108030406091505090105071b06090807080a0b0402120703 80
    0x403d819020390403141c5035000d44004aa49060090711401001011003000d200748001031b8a06c1d404501860700700b0b00740d18084c4603049241d0382d610310300000202c50751f81c0070881000700e80031864200035242c040c16492a0a12500c4d900f0030203c8044c02c150a0410b11030110040036aa02c40d116192107038200103007200902c5030b00c1c2d035100060300343c907800e00803110f0500410401007454180000d84074041d01e850021a450503003682030480300d54542070040500d42c04108000400314801502450164031a0403c669030b407000b50002520f40c007035032040d1040c4610680000c228000c00c590207a81004400c4c02c01c4001c0360364900c00590391131007820000308000002e030000f090301e260000240003626130300d46540020035103c0018400da035a6904001000440c2040400c8d5203500c914064000e80340b14001191108440307070449601da03c80c541184000070710310982085816004c122102c0204103200103400b0760203280d2a0700e840340100901c0a801030070703d11031b0080d4045007000400700841d00003030100d401c1e1 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 15412776 1250 15411526 15411551
    0x60f1104030b0105030d0806150c12030a0507110601090b0d0204060b04031208010302090c21010b03070201060b0906180a0b03070e0f01020d02060105010f0909050108030403050d08010b0304060504110301 89
    0x240c019000650700e46401400200e0f090500080f5041ea001182d168040507603204401c202811070b00007100440648180000c00a03000e003005a500805d02c400141c549a02d01103041401321280182410204155000d070010400000304416041d140c52000c0420b00001c0c4402290070303400b800d10000d402501d813500014092018501400507248a82c2e084203480301c0169080b14a0b4400b80000b0398024508000310340c8070b00f184001001c0002c2d40b4840c245504a04401451040704240d00043c00c01c0000410018507550a1041c9406003c03d540300f81c1c02c00384042c0204807180600742d52001c0d60303801c07502e001031141e0781c0710001d0009203440c0ca0b10b0313562031034a0300006042254450450703010b80e40036540c4400b19800841c00501c899076590050045a10b0140115102038082c40c0c05400c4c09090040400d80404600880d40a0071104000359541c0d031851502920b001400c0480204001d1070b00014000002100f00302d94029030429008203c070380356401c01044110b5400c02103035156180c0140030800 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 15414026 1250 15412776 15412811
    0x20a09050f0705031014011407031e02010204081203060102070b0408011a0414071d210607170a0903021c080612010b030a08031e07020307060b01090302010c020607060f 74
    0x14001d54014491140c0b201401907503180402d460300c40b00c08513060014460500728500c08042140145403082c1d6800f84000440c0840e48150000c0d80001d144140d58024510701074015140a81248021890289405800703620fa40c443e11042040c88000070202d80c05a20801c8038002810290128950b9035030364160181c000e01c0d500e00f0641420108031243c078283d1506108000c0c2e50f003182c0120888540c2c58071800c4602481798001d0400452402d0b040840b19110f00130082c05503c44405608811034414102616105008288900300f00550245a03040380c6110440364000c1c0c0c81000118031507100340f400340e0526001080c0b414820009032580c0c990154801c10060156409540005260f4a880c07074150076180102c00690305136118060843c00140b81303400551f0301844400100048000c0078071009104401a500000185d10105081007070100c04d20807141c0aa80900b001c0448901d1036001030640804450080d120300340c003007012000e11101e60000c403042e650b01181040084694081d0720f05 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 15415276 1250 15414026 15414031
    0x30f0111030a060603020403030c0305031807060504050316080a0f1401020a200705010203161103010203090604020a0909020306010603020c1e0f07060203041406070804030b0a020301030209070219120507020a0905 93
    0x1c090409000007013080c0244204c0f015a601540c400c480400207032426581a807001c1d0014003c2c903405d01030011151001d10036000507000c29642c640d529031a010425251108810a203104480001c508000c840320020301c9020b01980079890a208000300c0c01c011005010703042152400354000100c03a9030083d8041c01042c0400c40401c1d9a020f20745940b411140d903843c01d405000c0c096842006016400b031071841d00806020310801642101418000c0400d0a81e00180c946021650020052108500d401da01200c090041e404003041132001c0707500001d98511062003404d041c03690000d0b40c150500000c1c01610343c80c0c3d482c46c0601c3d801d45610381e080ca643e4050500040d88602071000045083d600c0403013240d080300e44403003030071407600508401c104450740401c108541c440d0080100000283d01000814480c40e062080107841e5851801030088000700200080e0841d08031f00c0f03150303103051030100d400d80c495500011102254034415005030f92500c19a40007940c032803009800000c4000070380d0016071 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 15416526 1250 15415276 15415291
    0x1c02030c0f061b0715050603240403080f04080403031d030d080703110c0a11010e0d0f020301050606030702030a0e041116150c21020d0207120908121602030f011103 72
    0x100003010f0500e6220070780107018000b00b070301d03002400c4040c815041d504007981000000303007501c0113a4400e804842102e1100180c0062031100c4404001c207141d00710b400c031540103607a543c11010034605666031070200c2c4a140001024030908103d405507542c84084074882d107880c090220b41c00d08582040182200c04122078460005c1d04005103841880005815680001c02190003441401c10903505d5070700304000381c40c40c10b04000f4079421115140e03940e0031a40340058080c081c14949100030740185401c6d80c60080545025160420501c41060b60000440c2e246440d0381c07400e4610040e10100090142001074082e0f00d6160002c14000c02c00c00002074040c424600c83e80500500d001440c040f4015259282c5000000c143c0c030305c040c030030b60a0341000481c41da129440b00052411007019803040c00c0b0b070007040b010399450b04204a40c4031200d4001d804030b4007130440f100c000c040200310507031442c820740b190303850f020b03100d524500400d42151410400328031150401c900a03c004034000703c80e664107420844020 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 15417776 1250 15416526 15416551
    0x9030702090601110c010509040905030301060c050111040302090403030b1302030a020c0105090c0d0210090513020c010f0506061603030b060705010504050607050703050708090d05070e06030d030204081c02030c0f06 94
    0x2810b40d03028062034a40b075a016005014250084001901d03590001038000d50001c6d150111000042d00510046000e40f0712501c500c0080c030002d05165003142d81c003c44c11500707035800300300610250360382c2c03511b0680c806d90510340403a09000c0d00c0c0c0401d1101e80300300078040e0040e0000c022f0001001c5243c0252200c051400e00801090b5180700055540b22142c1010360740148480e1900409828a46c0c2400f07a071104038288080c80c6552580400c0481c102004c44881a80e0301291040c5103071800e01400c1c001c0645044240418103203000060b180380324241e83c0007a2032155584e100c00705070194105a11001c00240318a464030068100240a44800c40e07044989005180000384d920740150103968110f6090b6039014201141036850f960380d980039016440d0b214440c40f01c1170000901c200710000281202c003154a40c80d040007030905148c1040c2041c030409140c0140400e0100400010b09148d080e116004920510416424241c0c01c41c840c19a20500070b0043c4400418040c0d00003401c03500856100481 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 15419026 1250 15417776 15417781
    0x105010b03071803170c0a3008090c010f0e09040c09060b03010b2505030705010905070b090f060d11030108030301030201090e0906070c0c05041e0501060f0807050304030909050903070209 82
    0x250340f0300d0071035020080c07201844d010b01381e01c040b51501c090080f40302014200c501c502e581d5107610019007140c1c10305000d000841194110340c600c10040c400341c160b03014104441e0741d0501d80c0d0510740381c4002ca00900e0400070091408030419115103400034a007000542100407a0030141000d600501150181c200c0302800d00c400090825001411241210b80400403141032103450022400d240402a1005071056018102c4001050090008041c010321413800042c0442440c40d0070790900c00070741e0001400550900c800c145a807141526161768650807241d69540c0c40c0030707801d000010b240e000c01c202c040c41c8001c0300210b00e1142c00401107040e01d000742c071101d011a995282880303170b52800316020303182904900c01141701a400740306160100380c440c0003580c0c16141c4030300c00b0038103c5440e1405142c65042a490b5803c14080f00c0c403820780903000a282c07800030728048050181064a0260200040090002c0081e0901d48504032880140922080900035818a9420103a4036005098141d1285056001 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 15420276 1250 15419026 15419057
    0x501150905031005040c050405010602010c020c03060601020d032408030c0c0f010905040513021903170703020a080f04050301110703030515090109020702030115060201050403020f030a080c0c0a050105010b0307 92
    0x4158080301d0300100240107842d000b0764680f01a1501600c01c54021484e42c0340841e4035a25402100c0c0a0000340d400001d0307100d4200c000a2070551421007031030090700701406003c2281da020403007100503e1181008903081ca641d400403040e040801c2d0110440c0c0305a07107408907040034044009c00c140e600140495400a148400704404402d030042098081030303107004d0402050905030000365021841401c6841000616004603401c90800c0404102064080100740204031001c09102200740101c80c40034101140d0f560040c0d6540c3d030b584006070180741d000c12940d101c0b0b1003280443e0007415000c2d000740490315002d1041481608481c0d001c0b000b080c1031900103190b00301d810b00341d40c0448800070400d0309282d1800754518006d6004403000d0342c2554075444005c4001c039182448000604d2140e000056900e801e040c002c2c02c25400c0d10804a254104001480301d850f4880d0440d038000d00e000c40c0f82a80c5640e03850445280444005001b0b042d035003003400000702200000051807088250351038400d500300c441c48 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 15421526 1250 15420276 15420287
    0x1060602030703140c06010f1502030301050d030c02120706020105040c09020309100e0a06050c0903060c030c0304020f0607050a1b060f080109020702040b1207080c0904050a0b0406110d050115 84
    0x115001607009010501c04648660610500003c0380810980b4201000c031806044c044260044101d04950301e00c20410540c410000010501c11440030354219414000000c1d040c5550520180800c02001800b400b9035554103061a0309402102c06c0b900d4055850381c0107806014105c4050700d502080c00400101034040d4000c40740b1940210700034050040101c2c224100926605d140c0820601c1424000c1000608601c111805a03041150702d64071404104101890800d001b424203020020500c2804410348623082900e4100d0741c1180d5600784001d942e004201a80078405000c0c0091090146030814424200d0443d03c00c076a20300b880d414a152106400d4940c240640480400036807158010820f580056018140480c030040011806201040015000004103400c0c0700345600441c80412280004100700e04101d1800d6454107803900e040d81f20203803038000340c101c00392246c2c5041002a04001080e4031408000e030803408903644031200212380b5801018240204280352543d4a5921071040c05035 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 15422776 1250 15421526 15421529
    0xf190f09180509031306090e0106030c05030c030c2a010b0108011505090a08030c07061d0f010806210109020a1208030c070807050d050304020f0f010207150c0c03050a03110106 77
    0x2104004000392000d2441d000905008210b12228002406200a22244500302c00010000c40c1e4601c103006060050803480d21206910070340030701d8076003450060b00729005410b407640162145400c6850341c0c2c500030342525a01c21000042002d03600b0711110300250604034565456040010000c014904085006403074406080c005c40d24907103842d450076486244504000c00c0a003102030521003610355110031440c0f40da0808540038403203800c440f10a10000d82d01480003450102196091907580300058003080000f81ea03036000c14104041d0301d0001e070b4241c451005e14907941044981100c0007580b500d4505001b0840d02400b2442a0382550300000c1e0800600c41d010344564114005078a951a0911684407035840741004030b5080c0018848000131071320910084500b104241c9940b552031130a03104000c000c5011f0905140301e190554012401a680000c200054030031011243c0d411030490142a41c0124821000070309074600700b58007000300440032076510842072090f22418022060801d056090b1140b6 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 15424026 1250 15422776 15422789
    0x6080f01050f0a0207020109050a06210506060a030507030b0a08030309010e06090c01030c120203010801050f0105040231050301061823160504080f010c0e010f0c02150f190f09 77
    0xd41010440703d818680c0201180f51050400414a99541000c12a2480d03d940520081505d4505009040402d8942522002c801d020300708554034000c0005402401404000d004259807400050710f410b000e80c0c0600601c0c00001d00d4003003e2036455216580c0c2c0c1d80203c41c62044d80d424410350709008840003810300d0040b40c418025024503250440110000e00c2d808642c1402c0251444508140740d04504c0110301070700040c0004142440c086402660019040c0d01c1300d40034501c100440c1c0c40c01d00c05011010030200c0000c0c4102207807941340503060b40610f15500322075410f503e06200010352000092000c001207060440600c41244c4d070503e480098680c00c5c0c2100480c100303000001e0301b158610303844e408015900382001d5052640342c102003440c159420803121000d0b99100c18654009070060341c001c1400360f0929207040c1c40030f9690002403d2070b0310710f10028058111203444030440040328050300c2404524044407071311111010717011441c0c000d078841014046000201c50461803072240d403001042d1100c = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 15425276 1250 15424026 15424051
    0x90501090b03060607050712080306100801080d0e011101110910090503030d0207050109080307080720030d1a04090c14030a020901060807020a050105070c0201020708150718120606080f0105 83
    0x100e0030180701c0ca5512200b022100c500070741030301023000c52a448507003103c280180d600d541c80b85400000c1c007955802000412051017501c8004000300d80340010340408c01030766803030240002525500141e07004810780780500400d5003414015210710b554000500a4440c080724181c0b94208914070981c1e07044094040c0c1c030b81507001040307070074030b2500740c0e8004046952150f000001c034415103440d603061a400a0701d0250008121200340111103a100c8000091486401030303100001c242040d1013683c0e485000c2d010320f41c840e12020440c2c40c0c400c1c03070031034101e012002501c00d000010040c0782244001185001d1007080c501d0400000190342400246d122000758091301c040000c2e400c05070140c8010b000244403104600c01c81e20a1310019800b80074031401110240c81d94a02d2514520000e400d00c406600003c00b180e1043d40c0e400e601000502c40541c012540b07050010580d22220318030b07107960455810540d4040b880d10031500800042d41d00090803600440d00380c80c14061a803240d42d00b03854040e100ca2800e4103 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 15426526 1250 15425276 15425281
    0x301050a050d050c090a0609050a140105190b0a02010c020601080a020d02040209040b0a030311011805070506070f080a0503060a0b090f09090709091202010b0d0519080c060412090501090b03 83
    0x5007210300c0c491460003001110b012044c580c00140d103070941141e050340c0c05c40d1039640802550809010340d070b8106032501e1080c000c89040302e0040342008414400c161044160115824100c0c1c907400341da0000d82044180c1c180e40306480c03400640030300b0383c6011160051081800016441c44040781c1130340103d9005007003081542d00398007000040c0d0490f040a6901956402040500d992051350384030013180300743c03600307009414200210b03402c6443c4055000380c0414003242903000280081280010344404488454503940316003042e0f6000884441c00030881840090f050603055000030144d07111b0740301240c9400049849202c041c03920b00a04c234809802464010600c00710345071a805155000c0c40c490211100340d50740d00102030944c3c0401405661420b800950401c6040d4280685a40454240c075442c541488507501e4690700c040c548100119202c048913100100290384003243c900d014408226500d6003000d040501550031084181f00c0814001c00700080c895015100820440308145502030566 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 15427776 1250 15426526 15426529
    0x108010605130905150310062108040b0a0201021606060e0c0a020309040902120106030303140c0306100e030102160b09070e0105060d02070203010b06070f1205040e070309140715140301050a05 84
    0x1000e0262004a50442000700c141254401f04004840d4042041c0041001890600080000401196030400d0205040f010b20041a42481200c1c02c550354070914503a199102c10003240240140000141d00c0f11008840c2014401170745c11040c00ea07041c03603014407403c0e203038848150160b11401c840e09026030028001c0c0c9105180030b03070240c08058000b1b0300401c041084032071040e00315512030b00205c02095a03400b04a0303a00c045940500d901101c0e881199155013000c0002a4901c0034100c0003004004101c803400b0142e880a4040e01d01d07400401996011403011880c0040480b5800c03140000c0b184160f01f0001501211145040c1c1250805032400307144c040744c15100c074041d6102050aa81540d21754219000030f45659000b08045801103141166542c99440c0c10040c036043c281a02d01005418802808134010201040344c212000e4100010710890610340461150340c00000b400450280920001b000101d00405116000807551050f403842c4902c9100d850500080c0151504098201c100b44901d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 15429026 1250 15427776 15427781
    0x13080301030506043f0c06050c0a02010609020f090d17030103030906020d020a031b020d05030f03190203040c050409050a060609021809010e04030305040c08060c070b0a02121f0503061501080106051309 88
    0xe07920f11b1500c1000441552079001c1a24410303540e1201d140700008500700c0907030f03080c400c68010701180101585800020540b00c1100c0c010203000c0342c464800700c034038081084040c12500325502e664038100341d181d607520700f005011091f40713114000150042100340404030b807010a281c3d0001d5032603142c01c80c10b0900b01d083c550941c8401d0b00b00701d0f040300c00091610040780f801c00c0907001c440100c508150b56490402e10300c41100c0380e107801890005006005010006041b445202c061324403c0d01d00154601490070a03502d0b200540030090b0006140440108005080b9001080b000c1400711340d003d087e0700c4030800d02c00b90030400d120300040d2841507804180024460741001d908140a400b4460103191201e00303050920300d0548154421120008841041107900685594081d01c50a4114140011b4050106102c0780080100200036030b002c640880d0961204c0005000d031002504840d454641003846c20f0002040d04511404184c030000006040f520610413a424207000e010340b01c20742e528180c2c00f00007 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 15430276 1250 15429026 15429143
    0x30509010c050f0a1103070e0604020d14070906180308030c090a030c0803040305061012020411190c0209061518010201060509040303020a110f0706081308030103050604 74
    0x400c07140300d40c5900032070b200700603d0f82000c03030500c0909000d4000b480c00400b17120103507007041d000e5001101c01304100005240d541354408000e50300940c0c0ca11041c101903005012500c1c10601201c0c10406100f41c2e50303400180700060b6000d03500c0c0c1c4c80c500603c1e09094200c02002d07110082c5030b9441080020745440200001e0060080e02500d4119025260750300c0300861210fa401411a0740e102050400074400100a440d0b00b00042ea5008280507051a0b4090690100810040e010b10b0301c66441c0d410681414040394200500074880015014030381070002c0c410582c07010181d103c4d40107000880c0007486c00c40c10088041000c220070510b0210000c3c45503425814203240c890555580c1d960010302d648a05804620a51195600513074070003440502a0082e4800c100c641d080760711440101c8000000014000159a45030420007e641e440c1c00d56910310081e181c900070f0040740088000400c204c400208140258403800b40c0c0c200c9500b0000140c25501040c4890702c41445800c90440700e0310880122140 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 15431526 1250 15430276 15430279
    0x1b0303040306110c0102030108030a1e080c0304020a170d0e03010203060109030b0c0405060313031803020f1e030304060207030c06080402010c0212010902040516140405130c1803050c0901090e060103030509 90
    0x2420113800c00f48083c220b800c242c0c420f14407500000f40c8800d03501e81c001c03800e010030075aa05000071119502400188501402401c0001c110340001c0840c1c20f5594000340c2a00824140100c0111520040a42034440d03810b20740f40c802046407600d0100c1d032440e060096900c01d60069550220b01031860319003000c1c922000d0a007880c01142048041800c0d2980e4004511071041148070b20310300007584c03034010056218503030600640460722400b0b00050740c600611031442c40c41221021240c50080c1c680038010110091519418440011b0004006801148210441c0d0245042000fa00e5941c10251401307141210000d0009281750300c1d00c0014030b40a000c0d000b0303140202000040728030b100e50114084034010707140c4614406020004291880e40700c802905281c00103086070f801c1c141703000007103408a60034101060500d612815106641c511802101c90040c1c0d140852100482c0c0d641803041e11452102b280ea0b015030248000450065441d004141560403103000074000c4d0ba20755101103400d5040444e809 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 15432776 1250 15431526 15431561
    0x1030b0720030c060601080603061302090712090c05030106061707050714010504150506010509030613050a051903080109090807020f04110f0316080402010c030c0804120b07021b0303040306 83
    0x1c5840d2007082015007070312104440109124280a4000352100000070851807084c1c0c8040204101c1e0310034030404403541035040e2410070780c548601400742ca4000c01181c04030121480e20280c2401d00c201c1d6a403c1003100c1c01076000304041d589594044401070381d10040c0d10076420780c41007c05c00d4a481030340200700c01d84c0650740c400303c80341c2e0294403282556016142614580210002707206884582d12a490300200c1c00d007003e9107840015004a40ca41c3e00041c43c03082c0750030b005100c000c2032110030b00807401c100b0f6000090700c0f100c80008505c12429009507000f90b00090038007001007801d013000c0c86012061034201d0304a508040550f400c0000b400020803400d03070000d44800c02500750f2540840904020b0b01004003550301c81c0381100080c42c5c00744007400d0410421031a0400c2c8009030741c00136400c0c1039441d05498000080d4005090035202440b031076000d4007400d0306c500308040c1404680382d1414044e001550990707064688100201070746c5192544184da158004000030000901c050780999100081101107 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 15434026 1250 15432776 15432827
    0x10504091a0102070915120813080312071b060221070c150b0108010302061308030a0908060f010303050a0e01020a0c030602040f0e220317040606050a0b0301030b07 72
    0x10340c03080d580364595209000340180e1810145680602010b00078141541040140320300c1070640c598004400d100e220908810f1030440c0c8280801c0c9002c5403200c2000444a81082d5604c25149560380d116880b052041e5180c2c00114202038413584402c01c142e655003c4104446a040c0c854600a501c980e2100c0c581c0500c141e17010802c4d40010b00c0070b41c030030001a01c03042c100d008103041c1900d491100450011020317184c00102c0d60283e80203070016042d03d1701074070903d4a9043e40000b0720000d40306608100c180c4c0c80049111100c0d264454007250655101c2c5050360407a4440403001c034035183c000e0100402143c1d081c401503002621403880b08240c1c800501c11a00510200d440340f280d10041c44e001566150b80024040c030900e0140c1880350010040c40341100142d02d858965000f207c00230202c50b403100c0e4200c1103c10141445201c14030301e182c0070350b9001500c0342081e2034504024401841040d01030342140708002101110442a2412650091001d043e150790b020b008540700310082003142c4590b28400031 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 15435276 1250 15434026 15434039
    0x2030318030702150a0909110f0906040b070606030c060305090a0305090a0e01170616090909020607061410060e030334030801050102070b07020f010c021201020a020102030609060a03030804030e010504 88
    0x2d04072000c4ca0b60741045036849200c004001c0c0034089540010750715031b08054400060b01070b06012103c0d04048442126250b86008002900903c20f60b030100369048030120301c400500002d9400182207030712607002246003540e10b01c8141e05a600458812a19401110400c00070234000e800400125100802c0e0400d02c1c0d2b01c0d900c05040380c020a170003042502da640069090000004c22040d030700000360034403d401c00514000b008102149c1c5015030f8003041e859410342c03001c41d06c03990180c4da8950b91140091028000084102c01d100c60100c0c1d030340c0d480c40006c0200050781401080300340419a0040d019610384001d5000b00c40c0c0c19070481010034885810100351003010030840006404143c8248d44030903065142c503000a14040ea43d802c1240051410860200143d0b10f40c503080c11a500c00303080403100e200341400029803483d0100e4403000c6550000030743c00881036040d0700540c41007804442e1010316031654800d000c4070f0002ca010040109440c2c4010030042801103041000d46403051401ea807410b51a0003 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 15436526 1250 15435276 15435289
    0x150106051c1d1c03090b040f0c0b03010303050903060a020a0c08091c050303010320090a0f0f02040803040603050a1407140c0106090c0f0f02030306060906070803090303040b010b040602030318030702 87
    0x10b40100315400020072400a01d41449540b90700c50041d150900840c440c035201e80c41c0d002005040280419220a1280c00b00520031034001d0081030350161541e10703582d4a00340076205038481d4070a58481d004840001d020f1603c01d1082d02c44460150340c0f9460307030744d0460b070b51061298054643e01e540b0240c1c1d0410100400c400352030b400407140c030500c00382d5201c0d451440c01488040300c880e8514240c604c00720190325284ca8081c0b48550160031007002241e0b030f07806003210328010400c280707415124900010b0046000f041c004000e004075465070b07038204100d0362074041e883c08840e4500d8610741c1007281640407810385403091040c07031002c8980b000b640d860040361040f0582161030590010a0058070340c054103541a41004502018541c2410507210310081c0c404025103038031006108511504000c2028091625007409450300681c0c002030050340c905000b40e01c140c0c5c0750402c4408440c210255030003c101850080152821100343c6e0b001142152034482c40c000600c0010082c0d503009100601840c005640c405 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 15437776 1250 15436526 15436571
    0x70501020301060504031502030103030507061d070e090f12090402030403050d0501080604030e0d030e24040b030a06080f370609110109050d0f08040305031b150106051c 74
    0xf44c0b145541c0d070346549050150403205060b0900d850f4810300c010004a034019003101c1c41030b544418001400880d00c0f1801e0312000142c0c4110002d0711942201241d240100c6004902501d9010125456141c140c50055662203131602001d4180005020011242c01c058000d150020b00c242411420451008140c0b400c540e026405040150721603000c0c0b00505401c00350883e0341000c240e034031000902c4a901c000d0a40c40c0c0441c2c03040d0040d54034280000e90500c0034003a05002041d0000f049a445a58007900c0a0300d8100350380b0484003030303d012000141d4040004054424440140c040c1c80102143d01c0040b80b100d5042201785490310510740380c03181c41141d913215101901d119140000745400c6500b04488070391001a5010305000d201d6005004c40e54803402a401e0301580421004072001d0540350049060049601c010940d100c00700301c0e101c1c0d00c903007181c20f14200101c0000300c07000c014503640101c04a00c4280b040c1000b20750700b00320b03908042105070307003034002c11103d0a4042040507400c1d407502c000c1a0b10 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 15439026 1250 15437776 15437789
    0x210f030a0207240503190b030d020109020405010609050a140d060204030f030e0a12080708430b06090a090c06050a0801090e0c090411100507021002060106090506090303070501020301 80
    0x20742c01800018000c0081d10b07055503590760660b1450904001c0030b0070a04c4040c2c403175954031242c1c0714031841c5194584c00a00d00400040c0a0342e0100da02c00c1e1300070b4080d02c4840c4080b03118a05000c0007040d501e1040c1c130300104031000140150612480c0a2410351000c5a00d144190015040030f05200483c070180024801136200380703118058880c20381001000d042000b6005441840c92800411600c0b042c0000e19440c1c030703041140c0356514081450850000c3c13140d26541d4020684000b103d60854405a144440e002c1d807045541c0701c4000151041340324108400e0004190500d000e0104c3d41074144042a10741c003842d4181d0000d15510241c03590b034502c050340d030310260004500091105c003007584682c03158014180000107001d03c40d10320a085442d5095414160f000e045510000760611480c150142001080902180c051000381600141b00307511005040c0d008100402c0c15041043c40042c0c524101c4c0c035941d499000b880c1c1407804026050b406005500e038540300c00d01030000859801c0c40114000d008 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 15440276 1250 15439026 15439033
    0x307110304180b0109030c09020c070f0e06090108010b0a151803120e01030e0309040207021903030f110a0209061302040b040f0302030c0604030302030d0203040606080a05010b01030506040605210f030a02 89
    0x541071800ba05656800c80b1160401c040d4070002c00001d032860b00c128080d02e50249000d07071503035180e445080c0b80490355480700030020064440001e02109401541740a046c0540303138038a442e038036009041e0070b0b201e00c5050301c5d8106400361410450380e5103a0560525001b001e00d4400361341e00e454103002d051350f00ea9410035103010007620001003507590040c90341c84402c002800e090103030145503000213448c0d01401460b20b005680008501c8215a613244640b0100d003820f10404046580f207040043c42041c814610341d002c920070000d02c1302601000205491829802481c81ea580e58941082c000600740c00f01c03030110742c035030248401704a881040d000b0300058200c3c00070600c0c60500e940101407078446000800c50094504100601c0842e9010003115004582c1040150356501e0703900d041c90040c069540460b600d40219120307082004819004100b008209030f07001d01880e11484200800c8882c1c610801d0341c0616404048a4450441e40e01c4001c07142150301900c3c0d02014026446085501c00301c03d100c0180c2 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 15441526 1250 15440276 15440309
    0xf060906120703060b060c0a060e06010e06100f050c0102040e100e010602030d0506030c090a05040204050f070e12240702060a020f030612010609020f1209060601020606060307110304 80
    0x104a02100d52000c41140c101501ca481d081401e034840525000241009448088003d5151101c404580700d45c200c4c0400c5034100059402d04100400a040200343c0c280a10000080c0180f00f0043d640c0c01101c0040418034800803511060341c1e20b0410100701e9090042c207100310181c44d1b2003031000d071005019590851340c403031902000e0700310080480d4000060103454000140f0641d5800410744031100b007121400222a211000040d14251a0b90308580d80095140308100e01c0d02042d0f000700740a035100352001d001648803c2010482400d08880610000350017002c080c03014602140c070408a050201e05407024282c2642e943c1c40040500c1070404d50a01c040024000c03003680c100201d43d44090f41407821414952a80080f552602c805850144140300d441e0b4000080802944450028a42800115a501e50b0350701000800d812041c00b14004108000c0016411000807403a140b003480141d025000a607100c10412540740c01c0500741a00304825070014003030000c0c0c1040184080c10206400d1072035a0f = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 15442776 1250 15441526 15441529
    0x603020901090b04050609040503030115120c0914030a02010e150c0312160503010e06010507021f021f110714070308070501050a05010611070e0c0906030a02040302042d0b04020409050f06 82
    0x110317405458075024100240030840072502c08002c3d03d0540c2e10004e0030312a800c24950084070700000e40240d103d5010314124107a803540c2d80110982080300c1d41d10102010102c0a1170802d503c0e604000340180c0800e410b20000c840c1c07850b10800701e007044468400b41e1414030542e00c2480386180c001058540b00300d1085030920455000d0750028009040c01c3c3d1400b14603640c1481c080b4006504c0283c40c0328107210010540404558a048030b403c000c044800c0d00500100400c00029501c240303000080a4000d4074100e00d032041c200c917000705200860608003071072038060f082c4c4e941030324880702100003002d034000c11030301000050442c4010700b100c41c0aa00041400c2c10030302d07130b42d2046880686c8045e080c00b8481003d2800b054010030154200c0c1c120043e5514640e07128140b80c44580300300340695900440000c20042401b85550150003624026074042003d01e080fa030702002200c600d007850184040c100f03410280c8480c2250407048041300f020b0005405d155580c0701030000e4410558500079140008400c001c0203 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 15444026 1250 15442776 15442781
    0x30702060f1302041e0f0519090507051309080301060302090103110c0c0d03021905030c10020903071203030204090507050306040b03120a030f060509130c05030303060f01120603020901090b04 84
    0x120680304040031070034511019120320101020080c01079803a1700001e01e148561001803000c409031100d0502411410082c00c40081604032014081e81c070f046d040d61610055284075050030640c3c03007802018003500313103010401040a440a5011641e032120030350b10020305043d0103503008003c2610056220048580050300f901c20b1290300c1c0d02c0261041c41251282c0c1c10014010040d00c0056504049001f0141000c9041071041100445d0034070041062604000002000b0500e9049100a8501900c10616140142d116500c021580355100340000e21442c00c407560000d0800388281401440e184d40c0e0f940c8041600c2c002c81c1e443d000f0540100070040981020700516881500441c007030000d204000503414068000e10141808065607071080035041505940100e010f003c004000d0b5546240111408600903103c0b40c00704d824501c4100c1c0042c0a04001080d40c1c06164000c00e0220030b003480c1c0d001140d040d0003603d02c046410b6214a80000982c80d075084950182c044100086415100e81052005 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 15445276 1250 15444026 15444031
    0xc0227010f05010c02010509130e030c030a14030105031518010516030b09070f12061706090d02010e07030609080d0606020c030f0c0a050f06040e07050307030501060c050703060b0109030f05010203070206 89
    0x42c800905001030040c2c0c1d000003155000d23142254680c1501c000a5044001040304041c0940c0c03c3c840000c4240b919038000001d4406400103940c0e1300b8031360b0700207000003180f0b0100388a01501584039200620342c0f58511030095170b1101c11801034422280d2103201c1207082d1039003641c6a200c0700303040c030b04040341240c0e25005d0760650b42c5044e1080b030302c1e605000700010429041c4410000400c0071200303c10071800d60701d030001c4c0000c055001407042c802801121994545000340d954088500c030300b407914299203006018240e41000c0380c00151080910707680b1220040c0c41e011300c003103400d1724081092090010181c46860098461030340205019142181414603080d540e030f0040310350340d20000340307680159521185007094400c06c1c3c50705034101c2d9200740402c420340160f402c540d0700e100c040410801d0345603111000d903100364040e0f40c042c0302030b982e03560055501c4c01071100040c0c002d81003d02d00f400491480d80140a000308180360801eaa5550303500e9140c68017480f828121140c3e50004240410691b04200c40798 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 15446526 1250 15445276 15445279
    0x160807020307030f050d060b040e180609030d020904060302030105091c03060b030610030902130905060c0705190507050a03030207080705100f1803020612040203010e010c0504060c0227010f05 84
    0x10300d40b000c0303a10090088109034403030030200540003e011000c0d981640140004021951145468940b10860300300308500868681102003070031080d005a890000071550b01412030034001c3c6107030102c1c1c200130318041d43c44400304940103031700c8120020040c0ca003446168400d0340346001900d413404403400c1001c408500e00030550105400d01d8000e0262403041c10841c1c0c1c00c62422107000c0b0040100b40320907000303081800d8002e58003c0008080100e100010741110b001320f482441520a107680e1060020443e004031640130740164003000121450242000307400c10b10034020021a02d00950b10300c001120f8001541040700180c000e9802000050420084074002d401d040741e0001c6c08600300080205a5140d0b62841000c1150b030100208002039140c112001075a00901299580c10103100e58044030103082d5003c9020390700e00b0004080610042c461101080400e07910b041c60146009802c68030502d4212041c0da000c1103107454064515403811100720300400141ca5071180d98900500f0300c103458116840036 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 15447776 1250 15446526 15446533
    0x3030e180c030a0c0e030d21060b0406020708070b1b0106180209031603080f1c060308090102060f06090c09040e0a03030516080108101d0708100b010e0303030106210516080702 77
    0x80c645c90740c0c01f1450b18a100220300d0b141c61081c1e15044440302001e040c40101145e14604903011400c841644014025a11107400b2199005c0e6600a1160340c0c0f461489a1a0003500500014014000300c2c4014000d861219002185194550310a448a039a804d2803403103100c1d0740014500c142d802e0034094440700c40c20802d590a821491a2075001c40d85c89950b40e0b510311824005080032650201661950007034800303103020442c40d0344a00d07048010740c1c41408854050312510300068640002e5420f080d105402c064840452501c2d184050410703034201451741c40c0d00507116030001050350b03c100810362400340650b402040c2030034214640b2031840c800c072401c9400c114594006010515001501d4038040b29000c0300003a44403a0002181012842e1525410a0707000c2c1c10f200140a2070006540f15081144403404c00c03556120b60019105100718980381900350b0401e000400542c0c3c000c3c0c900b00e0f498100c03e803107a02d248181c40305044c2224411103541d40c043c00710340040e4540651100c07010b0b0340920f050008 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 15449026 1250 15447776 15447797
    0x9030d021006140a05040209031c12050c0a020c12030c03070b04121704110d12020607020705030703020a1802070f12030b010804050a2d06020c1b01080103030e180c030a0c 75
    0x421500499170007000e00454000511403290340381040ba841032200a80c0820b5a0320701d07101c00061518004074580142542003201140c03280307490508071041184c6503001050200c0000302802604140440da040b014041400100000601071004044a40c411b0030080441d241500e0700508116069071346008001c10125030782d2900540300e101c0f076041a08800080351100d0010b00090285504000080052051030700d5212403540024820380203030a150217540442c5c3d12035003419903520503480080d41c44041d03600f0800083d414103c624140d019400005031414100c3d4940c4010b03044501d100712a0110380c40840301400d581071107900e00141c424603142585040c15295a503544030343d81c102a008280c1c0d45606101907010f200613890402c0c1140fa8100760014074284a4000d410001d04041c05000d08030b000780c100e81c0b01301070188448105860b0340311241d00316282150b5401881e09901e401c01c40c100b512401500324550b040b842035a10000d03140e502d02e4500608400c0e102005100d00a1104a540 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 15450276 1250 15449026 15449029
    0x30d09050f0703080d0203040602040306020a020309010f03050601050d020309210a0305010801060f05060d060305120414100c1401090602070b071206030203100209040b06211006020d030209040209030d02100614 92
    0x40b01c45440070305c10b0150b140c0c0c40f6400c00000902c41d0754001841a03100294011103240c010016000c010000d07203480540940c841826000e84400311707500360000e0010410426a4151740d1f0281d40c115845108070303100302000c0380304c1c41180e103400d02c83c900341d01c1d0002c40c1e90001160b05020744c2e0f0141c106c3c0310091203d90310700030005161045070b01400788240e40c04200043c1520403540320a0003140c12400702c0b10740c8284120180f040f94801c6c00f40700b203000440e00032000541020240150641c40c640c0c3c540d07620006d03d448491044203ca02403555554940c2c100c04041080c0f800507111460140c41d40900500b040400035020400148170034541074145501040540d50120340daa419940031100907944204001c000b400400007040800da006001042c1c85150340d40c0c0000301012460b02c0340c4124021b0b02d075000003a407500030740e00c5a040140c0c0082c000c1200107110703170060700707640034041c002509010307100000a04140140518000681c815203410352150300324018180104610a60710050001c42070 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 15451526 1250 15450276 15450293
    0xe0405060a0608030d090204021210082b081e040302010c0e010206060f060c0a020603040b041e0506040f08121602010c030b06070b1e010303050a030506040b0d0f0311030d09050f0703 80
    0x101d442c0b07081c1b03603034410140954480d501201d121020341c070914907040c60000000b0314001c13228001e0811a10500000803801900083c0d007294514071040111114010703900c0446419900800c1040e4000c0d8041108114420000c201da0042d44260004104e5174802d040081c100c5000c4410641154000c100780100354803103402c038080348901654842d56503031b201c1d01c01c2c0e4a803403a01b110007074020400004000901540c448240d00540c8070b8040e20002e102e070ba10300d060351500d11034000707401604034601150005074008a00c07020302c1d2040a03214148042000210f40d60342c011504038008084da650b030f43c6101542071050041410711814100544440c0501140960254610041100304418040b4426103844200b40c2000400c001544510350703100e00d001000303508008507a8010900b0f01010a031280780030700450360b01c01701c050a00a13a03458140c036694080240c40700c0075010300a0400e802000c0e19810320040070490400c0101040060b00c914040d450a00f4058034540030303400482007400081c0108 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 15452776 1250 15451526 15451537
    0xa02040c0e010507060c03060f0303020c04140601090902070312110c010c0206070c0b060303090604060c0b01060c0f03030203040219080a11030307030f0f030209030a0f1a07090909110405010e0405060a060803 91
    0x580000382244031b01409400030541900b080c250406000030010405a00003482d0390318040548043c01202414500801c4810b41544d949001ca02d8040341031085038481d42c041d2200d603010f4641030030707081031198a85040360480440203401050009000131924401d001d14135103459a840100700074a8290401004031192400003403003000139002281069500304251040e01c9001008a075441740d8481c0e000d000c0e034850000440d03100b03440c60000075045000f1a55030014030f4001d00c80a14203007032660118000e500040c000c9038040c0078a240c200010400403240c0300640481c900409c03000748581090360a213000d07081c10340c3c880d5104011050020394008009072050741c190070482d108a804102c10380290040c00451a054845c3e8035a2034107000f5903c0080c0c00042c01101421190381d500303404003100c50f004840040104803111000c01c0703003883d00c2c1c3c45801d04500074903d11101280c00d03070004050740c800b170b071000c00450100010710003884410300c444c64015070003c004004592800443c01d84a0081 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 15454026 1250 15452776 15452783
    0x8010b0306040b0a03080406050c0d020a030e060a20060105040f050402060714030403080705060105090a0c0903021005040806010b0301170607020a0201200102031801060902040e0f04020d05030703020a02040c0e010507 95
    0x56000d5420182c4404201340095a40011455156500da980090254100102c80003e074403450846021183c0040f4203480c0f440c0d0180e4580b442e205a50b02032103859400911040204080034880c0155030700c01d45034000b4180306000240c0490b5140800f0403090781c8640f035a0702d00d1a840d000900005035960411903800d141d101000440c592206101c1c18103601450740090300810001a215082100120b403280c107958048842d0111030300d500202e20100c4040070460f80211b0300c980000c0c0f0240c40c1405034844940000d00d0b00300d180507250801942001d038203911240d440c80010005100d07040d039048000304603c04000c000e09044c0307014070000355100400340000e0f0510044202c18075260303144036802d001b0803540100a6560b4145401206540c00e8050203004480d46004800b0138440e216000300c4085491880c444400d039140c10340c4080e90840c01034002c0740e0146001e0003101c0021001d01c05090301c0c501a03000303002031342124010300c0155041e04000c201007044a030241d00440c2c2e0070005803030310700c1e42 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 15455276 1250 15454026 15454031
    0x6040b030a02090a0203040201080c0301050904030e031606090e010b120c0c030d0207030c0b010e0709060e030f0d0c06050a02120109020a0903050f070810020316051305060f0d0c08010b030604 84
    0x86410110741000e200041c040c0d0000600001c004503a041c035002540524400e90b030704a025550714440b2145800207000e00d40e400300c0303048049070201c0d125034420035103480d0083c02e44103800d8903c2c811390050030056102c00d0201d00c2c4d412040041001c0d401050740100740c0810001c2c81c00012065840c5c110600600344000c158000c43d01c0500d844040068804080300013808540d02c00c01030078050038840c0490380407900b600340030002241000e01380c510940115501c0d150300c40f15505000d000c2e6071000300103030301680502c00d82240d0143c19208000810141040c6d80301c0f140303c0e101a04002d019198014125804c690041210740700d0403446c115064115080b0110060720366110407012a404282540041d16511807004909400c000110fa80022644800b04031015090300034503074002d900088400203076140003080711a40703003030196009103903aa031100007a44030140c4402c00920f0541000d00301d130355290000304485ca0104410b200f140030281050030512455031604583c03102c0c41c400284150302894 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 15456526 1250 15455276 15455291
    0xb0306060d0f0503070f0602090f030c01080106030b031207110102060a0b0105030c09010507020a0e090c0301050603330f01030c1d060103021602090903030603011803120c0e030a0f0210020d05030604 87
    0x180a2084d205e0603544031003a6a004401e90800307030302079044281000d105100d100c10000c200d140001c1d40c022080d4068598980f968a04103095004000b200d800903050f003d82444044003641c0d0100800c0381364030800d09445110350100009142480007007202029600d007001c0c0744002e84e088011381c0e91189801c8140c60352a01d00d0401220030340107140d0006d4005040c103501040c07050680302010300c9603d0002c2111650962142010700f626001c0e0780541d00354200704c1e9250a14801911507045107003c1e0300305199081415008011650340444401d0803400c03044005004010700f84181c2030003001d0f82500c803c07204031a1054203824a6000c1c0200f8181a40003428094082800212040c95a0010414541d624081072419120343c0704940c0c46110f54030300740066444d11507002501d2500340c3c05030b640801410079164a50000e107584808013061000380140140c8903601000340c01101d621400110280743d01c64418032081c02d107407401c00700c00c0d50040300c0704801403584031086d01d9000c40202d50110300030 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 15457776 1250 15456526 15456533
    0x80601140d0210030504150207020a030b07030207080c0f12030702060f04150e0703141203150303090a030f032a030e0a03080a0c0c0f0e06120f030307020a03030b0306060d0f 76
    0x1c00d0209000350010070510200e280e00d901640100d102e02e00070320804072032182c15980304040b4440d030a0001e5010b001c1741c805102265100d41c6541e4040041d040042c9011030644504d00c640d00701201c001c080b54001000c03101e50300d40500007a18401096548182141440c0300081d482e20350052210068662100c0010140060342d440070700c1c9103600c0c150821503140d50144150315401c0304d010070345120800d0003014401d010000784a0b09440755903403505003941c45040d00c805c5858103030714055600d4030090000c60581c2d078a0446d0080118419041a00d0402c3d062601600d08cc18515044540301c403402110540100f140890009180c0d161800080c182003040000300514859040540040c1c004154820999001015000824007500280403416030302d295110001d072480c014084600c03050008203c0c0703800c203515203c40001103a02910801c207108101c83e440c3d40c0003111904016440301e4070031010305070144a81443c0750000c0d80502124030b010400f08100c241b100c80020180d800240070340051 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 15459026 1250 15457776 15457789
    0x604050d150e01060e0907030512130e13030201050708070806010c0f080409051b0a0c0201120e0d1e0e09010e0403050d050703060e010501031406090703020409050f0a0e0708060114 79
    0x111400703994104034000810400364001e003920300620090304000e1012400d1030f41c0000b9650f044952100081c141c40400710307100070f041c2d04508100116028011400b242248041804c24864800841242c2511145040003401e50b00054138041c1801400b0b81800181036100c5039050f4031078004e0030300d00803806107031616000203140c0c2c2e5000340c45440d0104e0049482c1802d0b03040175020b039900b0b50601c1d101750400221030b102e5200d280410804140c0c41e4070f5110055010300c0706c45043c0d80c1e6141000442d4107410003080d04100c100000180000d1003180c042011091950030f2290005952034140403902021021542c0600d060269000803901c80000608052080080b200c15a0001c28140000d080503803025015200601405100034981c42c000318995100f40315503e8076144105034452180c03522028408402e80c007070321007401c041c1c08100210780e01711280901030140d1103048071400a86408415101155508004800030ba08402020001d0040000d14a415540c0200b02d401c00001e40c9000560f6 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 15460276 1250 15459026 15459053
    0x2030705010f05010303090501140301060e010905060d0f1104050603130602090a060206010315050606090f04020f041d0702030702010c080c010605131b020f070b030402040f240902090604050d 84
    0x21640c00c00d9400c040b000c0140c2c0245048a109807205480305031200300550300c403102e413915500000010303c01048003900c90309142e005990181030509143e603d90340402c49503448407000c0302c4045d40b118074100000c60130303110b1801c2c00144150001d06044c02c00000810a110260038ac1d0f5403410000c41078820700c10690b0480e0740d101001006406000d80d00d4a010352030350003d11040e294402803c042050b28070560007400d00ca240020013652800744840304211030b1018200701181c11a9007813009402144200008201400842080700110090004842c60070003009014008540082c000b800060f40c001088a41c03841d40214040c1c0c407260b000e820140181150340c0010b42c8080081214143c6226662100000611007504420740855490041c1c0e42d4080041c42e28640d0780c48000d04019400302c90014540082c801080401d42c2600c05505c401603440b500311a10b0030904580760f0110340700c0d04070040c0008102500095047c602e400c4005100d0340a50310407030340030b11082d68070501040120100c1d001c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 15461526 1250 15460276 15460283
    0x303030405060f0906010e0118060e130c1508012303060c07060b101209030207081204080d0305040308060f01030207060905101503020a09150801060806070305150d060b01020307 78
    0x25140d00c0d050800680d107050683e0703071410162820003c1505030740c0104003241038603d440500c518592038010207003000400280d26000c1e942d81d903880840d01c0d0900b40ea05c0c2e8059007800790000e9500107941030400280300542e2154446042c03030f100c107070413598000344c5d507038112040350003507001c1c003844800c2c155403810030048030940c5409801c00304981d00009502429505000c0d9404104900149003841540c05065100301e0124582c1c000740030194806400020645100b17105641003d80c2d0b030760805c0e141406580c02e11011150200e800d106a500030404030f010503002e443c051186080c2520b003e8078440b80680658042c0011075205045a4080c3c3c0489201c0f6600031010499000c850800b1503c0d80c20b00300c40349013400d0a0110111001400c02c20750410350350002d0000d011146410600c10041068942004600c4050840011280c100307116103c02451004003802452400d40c03c01822101d00401500700182002c80018090310cea0311200301c03499201000140c51605080142d246002e1848000c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 15462776 1250 15461526 15461533
    0xf1701170f010e010f0506030604020a14030102090a0803030402090702030a050403020616050d090801050a0204050303090616080d0203091903050d1e090501020405130e0307030c08090a03050102090f120307080f0903 94
    0x622903c03105600c00f0100503104841041107884a9003015200c203c161006036101404401c00d00c114040c900c00544503140040c001840d01c200880401c068980796030202d035403508048200001e601303120790850350056840c07002e90b251062404c409070860003607002c041c0c09103402207401591042c00c550410a0290400d003141c60040c4100c400900b5800103004d103404950810001ca401c10049009480076070b40002d020b58100001c003c1800119004903c45415a040240880002c00c101c2d034010035441c00101405607030f070300e8040c4015146c80340d0500b420080d000c0030103030900840c2e070010640c0e110a0b01ea0001195900300310031205101c0c03000344081c10703500d07190500c11002c1140541c010400c88009503081568030440c0035200e4100c80c04800e40e0380b02c1e0340007046502c0009204101300c1520a1080c4c081e1400e00d6044000f29801c175410740c004440c0383c0c1d800900903030645080f020802c200c083c1218040708035001d0701c00e110344034000d100c0300508a0f1800b2a04d121903000c4601611003155028045 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 15464026 1250 15462776 15462791
    0x3050a020a060e0f0f03042102062503020106080a080409090c050603010602030d11040e010b030417030a06060e190603020901020304090f050402011b02180601170907060f1701170f01 80
    0x5075525041c0400044c0c43c288983d100c003011401010003603800300d8034810201640c4102040704005038040950003203034400d404104000584200303117640520400000c01c00410410149006421590107400c42d40362980300c404000001500d0404a034143c9000510125a6002030314245402e249290030181d80314001000102d10f0320340c0040502080c0000c1c000902c00300020454162403417050b13004880e0010b50741c10050103074000140056412a10404d00e50040c02800c03125440383d07400c00e54a0084880c0c45240402010307601088180ca10070302222052500300d56074207400881e03509413084006241d004a1454000c0c0e0090065134014000340405002602c901e01c0004028202250124003050013981954202d05e2900c40c01040d2590252822082c3c81b0006004001e803140142418100300001d01503000d80d201041d03445000300080001400d44500b015805082607020321203400030040d101c10502c0c1192030316880e10341101c82c220100c0064000c2104100d00741802c1c6210b401e010341c00c03c000c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 15465276 1250 15464026 15464051
    0xb09011707060509030a06090302030c0703060501090f0e0a030e040b030616090b030106050f0306060708120109060603091505040809030d050a0f05040501020a151806020702040b030706020a03050a020a06 89
    0x1014040304203948266240c65803030702c100303540d2805511015038142d40030302540000512540e019141d481d0003030040f2800c0c00e00c9001030074031706400c0e6041144e400d500c4400403c040c0e10180503480304100c6003a000c1c091038040e400d60550f40c0410340e10203004c100000340740c5841e64444d07500060b8002400340c19564185048508460840c58403400382000414607000010814003c0b410f50703040c1c030340d0381d07403564944502c00e43c0d1512560809802c0d01e510000420500780015122002458110b040b802c11001e2989810940c404480d80d50340200300b03240c00c08541200040210015030010284000001541c1c7c8890811103ca030044140241d014071074100c11508064100e0040c0040019669480441d085004401c80c0c950090388a003501580c8680703c1d9100085c82c0551103101a10030481c0000c140018a000c08408030310800d040d110b01c1e500054544c00e60034540074640300704400360001c0908506d88070009658444030b89015041290100b0541c90151003401800000c540292043c098480e2105 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 15466526 1250 15465276 15465299
    0x204080a0209011205070b030405030f070f0c0905060a031401020904020a090305010b030a0b04030f0c02100309050105100f0509090114040b0f060103060b1c020c06040b1909050a11040b0901 83
    0x3006900c520710410000903658000b00c20703210041e03442409171502504e0080d0311107094001400807262070100784031003100d2642209c06840180e003d10349c100407a17082800d10140d55866500294440340c20113040020584030702110004899000c0341c02c90810760b440c661140203000d40d1070707a96445400043c0226185600c13404080030b403030141d4002c0001804450402d5a5080074150042910162100141c00f00380642c0c03020b404103203241480c04000d031030f81c0d001440c0030643c0716400020941d5811680113010302445503503030154079103074110302c118100600c0c208503100901c24144500c80748000505425020340124074040860f442c1d0301d100d030900e8030f4030388191002114480c0c0007202c04400103c4642c8a40203a0040b00c802440346850144645011841100810102c0140e01e4003044442c1c5c0d01c40c801c00007030340b080c0d004503081d04140c201a0141c0724034280340ca2100c1421418800a030000c9040403070348910a640c0b241400b000c500420700850094029400d1361640141c4100002aa039407a10703 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 15467632 1106 15466526 15466543
    0x90303090203070609090e0a020f0d0c030f080909090a1101080c13180507020d0504090510120b0402120f1906090c090c0306060305090a11060904020408 67
    0x2500840d01c3c0101036440b4100180c1c0c0b01c801008100c00b503110350440030042402403c0003040035000100061100c1c2101842030700d00c91420010040c0c12048100110f51040b5a41c0c6218102c0c10300d485281c0041540602454040c1c0009100001c00300d4050a165031046900240050103001101c000d50014604149600100909007000302c9001c0c42e84002d00e60300c642e4a561210b000d200000303645010300349500355803140070f030302c0d0005401c00c0545040d03c0c2c10200c00129540c40c1e500345a03002c3c140d68801404030185448207400d00c01c3d0f07a14010f214078000e0b5909021044181e0302e890752a545a81280d155030012401d02d9861540c01842e883c01c10f000303450211303c0d0a46a00c403150307a010950321680609943e0b01d1603038051601030291b10300a2105003020800d0f40b801540c05a120640908000d11813200410510442d5948400fa60710341c15004d4411511983c442c2040307941c0b1100c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 15287776 15467632 := by
  have h0 := BRFrame.cov_init 15287776
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 15287776 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 15287776 ≤ n) (h2 : n < 15467632) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
