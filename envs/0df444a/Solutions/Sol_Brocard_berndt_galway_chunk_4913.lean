-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4913
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:08:16.78367+00:00
-- url     : https://prove2.me/submissions/96046caf-a14c-43ae-926c-d3fc726eca7f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 883453237 ≤ n < 883633093 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 883454487 1250 883453237 883453243
    0x80601150e151903140411010e2103030a0c141e0d020a08090606040204030f0b0a140a050114010c230f030729090316030905040903030b0a0605040614090a17 69
    0x100c043c0c0c0064540f0744003200c11218801c030940260f42c000e1184081c01e58400044620701040302d203107540b015510302c0c2c02615802c01409902840240d41c0036580b40e2405154010071100400a00c030180008512511030f20351704002100e426a541c1c03c06030341400c48100903801280036a05061503800d10015180c4003454100e1a03491180d00c000e02110041e94400c000c2c07000303a0141d44030090500042c0101680040c452040071a8040015080090301c162040341840440700c0c01d42d10091115514401807040140d00f400503880c000d400e0900d04c40500407a61043d1f620703034003148000703101d0310400d50402d0445030611507a00a01a240122a160307140e50601b1009524071680140c0709460110a40c0c40071480022064852803034000030314200510110300314024050060105e00300000841d001c201a41c1e01e00c03801110034029500082d2400516060000442d00c07500680e00303000051104010641d070043e019480381c249000c1c007503142c3c00c054000c218200da485d003010303591849040c0d102403448800 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 883455737 1250 883454487 883454527
    0x8070309150e01200904110d151a030c0a030203151e0405010801090209061c020301181202061611011401140901210305070534080601150e15 62
    0x110b40200320524580c200c420b521010401802414202030001500c00c0c41c1c80d52020b50b06903002d11600c0c0c60b14000100c80411941802e8003001c01d260198401d024200044100e4510420f800d040d251450911954042050040b600c044040580000000c0ca0384000540034114650014025144c2c0219003c0b00c40d0219100ca9205d602036441e02c00002404c580500908040580182500e003613a00c6400a008003080e02c1c207080d20480e64500701140040e10240302d0360386007a0580400c100d0a5103c0d00d050704003894002540c0045500440c28448880c0c6000c420000140c4a400c0c54422a1f2030b00c80070728007406032510f0381013240030504d000081c9003550407030b03141030180100c5144600c2e03a211844c00c030304400701405560354131110071404000240110010a6024047e500f114180151043c182c8404c84000740008006400c08100c1c0c42003034000a850000351400703070058030b090340c1840c1d9540801d4031004a2035042109020b12200780b6110414107268010300c010780c040e510010550740b403583c10f0035 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 883456987 1250 883455737 883455761
    0x8150411041e090303050a2a180807180b0315010e060a08030d0209150406020c0409060f05130204061703070807030311070516062f010608031204050601060903080a0807030915 77
    0x8040a200023544101c0001944a800b4601100c030100501000c41e48040b0906107400b00c400c0c3d40d040803ca070601000f42400510b42481c0a10606910314901e8060740c110f0303049103020b58494103001983c0700400c204039055694450b0241c1c09a51460b0000c0d0300c00b2015032000c04940000101c2c2940784040381c0050022010584a0207004036101d005511140b143d4444c1714016000004454500e181c290010a043e0f4041c060204000c5981031b923507000c40d40240c032148460341020000c0d07411400c01d03001d50720007000e0000c28101501c2e81d0001c030a88034441c00800800200f00040d014041602a51000e40c030201d0b21180e0940741d040628125556100c90400368502e01e4400c5000a03490b40b0070448102880010380d000b4640080d030380b5400700206a04503203c2d0f05552954001309401c9010006003001360108d24105060303042c50300b001030822006070000820440c80b8403061020400801c00c0350601d0801d440c1c51041a51003000440040c20000002050510440d080c090040003540200307440c550 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 883458237 1250 883456987 883456991
    0x30315030c290a050309010b10080f1b07060506190b121f050d051f0204140a1a0a0c0812040b070e010e0d030c081308150411041e090303050a 62
    0xc5840001c0d10301d400c00382c0840000c0080101d5002c240c85100503603000703080d001c000b28a9209140c0080d42c07003180d0390030004c002030340d03141048003504a03c443c4a0704108200b004020000078041100d00d50302c501c40340a400a6210000309206484424500c02220401c04056001c552141c86140081d841628289440c26004011906c1c0750800c0b00b64145951104045000c124030b40803c1c07100c5c580010f0b00c146c585000740820038200c041201483c0488100c1d601d0b005035654104800c40000d08400c03110780303000380e01484042c4900908103607200b000c2c000c608910f03034440c07003000c01c1103880b00074081005242d010041900c10340b0304031000d0524000c510805802281d540c4d8214101e5a1824409140f400a449082c0e2100241050b10400034464060320f012070000009032140c0103140e01c040d0005902c2c0d84014410440268184000c07a00128808034012190400740c884104800f428a0804d109540c0c50f84c105807810000b80e4440042e0310b051034140212661420090002d0500300d6100744154 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 883459487 1250 883458237 883458269
    0x90702070e0a020405030601050d020414150a09061d04050a0c1d0919080d020c0303041506080a0b010b0912061005031b0d1b120503040302041118010c030315030c 71
    0x5158004c2e00c00740c07800a00180503da10f00410040d640301c03440c2d0140d800503510726103c00780503040804140f00364044281c90b40d10b9100030717080c001c580c0e013aa404902403d14154007805a1200c4048607140c3c0500003540b03203040d0b25181000c0e41449902c007001000385080340760000381e80c1041ea5264505002d60f00340740000740e50302d64084c0e4944580810980c20540030304141400520240041e05644071034070001806c0180c0380e07183c1c51031944141d42c1518062204040c400610340b0318040c0c0005455410702901508406a444440985040c00390001c12240030803030100306d481e842c800510011990b000c941e043c1c240084840110714407401180e029025501224071401880e001d000340c011005060f040b80300381c15860b1807420720802e010784030214000b070800140006c6000d130448038882c0070720040c5546515510400040320000402800615000d010030048813440e040003403640d220078248013140c1c0d40e0340e1400701d00800012240c400d01c009050008424403001070142016100050407000880c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 883460737 1250 883459487 883459501
    0xc0b030f06090c0a080718231207080d0e03010b0405010e24151308030a11010608011109061602120304060905120d0c05100504060c0f09031205090f090702070e 70
    0x1a00c50790b803510001c10303940e60114803003900c604d009016159007246115045c1d621885400710008e0000d05025200c200c910983c0d134039150800c088000c401c108002844005d18019801e92110303104021603050052145104800d500c00390021090200c00030400c100e5983c4468502001c1d9170140c03018049003104608656050030600d0b1194a008402800160550317548800c85426521054186190b004454400142c500082001d00460030480e16400ca181c201d1610060844056501001480e818168040030007020841116401d04050f0f80c007e030307158943d50004460100c10303d402900400039401501406201202400c1580c40603615040001d550710f04210039484c011900404035048201c2d80711150b80148a0140714510a50542d03140c9500300e0b003a5030071500e0032103007901c6807912503203100340441d840070541c9004052800c0c030024040c00c50b02c851001e00784d0910a001400800070b80c0700c0032603403485440b943c0c200c0010f00b081424a0440c10013034407048148181c004400b0030300081901 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 883461987 1250 883460737 883460761
    0xf0a14010f050d080c0a032601050901050108071e0201020c1002120a0b0307030614040201171e0907170a02012a1e060e010509240604090c0b030f0609 66
    0x40300d41c444110405141050b0800419140c001030841d8920004c00c179010200c00b003030001031200c6000f901c482c0c050109502d13031002041e01c814400509001c8c902c00521060703964170400350556100f8640401c15940b148000e85400f86180844030079044c0b51030803601c0156054000b000513410083c00e41c0e2450f0039081c0107105a01690b0000c80440844000041c1a031a2613400741905031401000c440e9842d036251184403c1340c0c6501c9000711010050701c200001d43d60080003d0301c44440e440601400f625004c4240b02443e486445804400314450f0045180c000c41004034502400c007448044111030310484089995062001c022404210692a0b11005a400c50290310780b20304508401c0d0000c4074036548010740358103000003182c520701900590340041605031140400400c2000300000f000c0c109200070500c4c0c140e441c000110803a442c1024a980440701800068111030107071004aa101068a0f0010b903085064100c562078502c0881004406050542c6c0076004060680d000c00c2d858550060f4940 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 883463237 1250 883461987 883461989
    0x4091112070f14010e1005070c140d020d060e0f16080102131701021308010e06090d050a110304030f0b161b02010e0a0510030b120f0703080a02070801050f0a1401 71
    0x180351a6181040f00c541100075050700c0600500d060440c1403490800140074280350392000002400100b0141d0170071000c502204060300c0b00204603201d501c1d02c40002403500d58200b50090065450140060400846412524418003e081a180002481903006a56600381ca400f50400080d11a002405103018421a03440700020044030300881c2c1000300e404490003100103090003566007040004090b0000034428000750640ca0000301d500701c41c810202d4038080000c1c010751101d070404402c20b00301540210072520b070f03100a82444064070102c0840c482c10b5000741e0780054850341c0c03629026410000c092035150711030840030bd9101800c00001e4411160009440458102210f83c1000c0d82c1c007642c0a2071811861083c014000b2801070f80311401b1650660b4007030700d00800300342c42e054100c0451800c18249154800303540001c020076010058516a6800c1510025168880016881442a01c24008980a0705403a0002c3c402c0307041101424042d2081112140c003020b02d00080f070100c08001080c014 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 883464487 1250 883463237 883463249
    0x6090b01021e0d1d0d111f0e100903020301050a050711122703011b0212120105040504140724021516030e010e030a0806030f060a0f0b0409111207 64
    0x26070030384240001e40380c0b200744540c006041e41c441c408078200ca580f80c0700b04122480c8601c0b511006c2c0441001448030381428420300c001d01e09042c601030044a94804061051050102d17218490500a03450a0b60410f1207504003035059404c1c80708100c8035503959000383c4c1c0103009a03550310701403420044016031220035041ca03a8040c1c0394208000c0f80030a144c10080341d144a084015801e00d8521600081e0850305050300943e554081c1c0c440104910341c050101c40300641d240c0348018980070036407003c4d18084205004840c800e0703680b000813074107000d0b4024214505140542c101c80c0441e1b214540765404503550503071080c00c41e41040c0c031a4425071001c1102c5c5002d030f032034417804070703060f10f07182074038880701820907514004c06030307150b800c24500306d001d00500030320309403010107150b607401c0000e001401d030400108001e000c4c1e44000b8114005200c0005c10b03d43c00000000e0001b074420400c07007500064407001c1711095000d03040070111010710817951500030f8003442c00c03a0143c1020203a41019034440802d8880c0c5 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 883465737 1250 883464487 883464493
    0x41401080c09100e0d060c09060e010c152702130b011d0102100c0809010e03040b0706020a0924020f0c0f0d020406031211160b0a0e1306090b01021e 65
    0x8803018100540180c0c40280e503414003c0c468541103000c211480c801902c140c6c1d02d95180c030300210100e500030140101a1031580b500350100345c018000640080b5915000130300108a132a80358141e1350882d4030039409400c400c2c0b0801d031120000e00c0182c60900030b4100c1a031040c2107400d20f201c01d095041c4100740307903240d041c4c4404001c62150140c0510328000401a141540a0f502c0841c03a800e03001d1081c100da515460302d0341c1081d82421141c0d9802c481c001001801160700800050108001450a4840b00313684250b01581e1102e40000440e0502503a610000c00017200d03039240710207100403003201d501070302e416422078032070303042221009503115a05c480554000c8a0610307104a039003000007608010382d00240010607110358907502c06d61445a44454000002e500008007000c408080c080c401c0d069076051001070556041c40380759800b0b07208102c4500b05001d02089000c20544070300d0040d400303c14844100f084240e43d99141c0c08098034024800c280103005d150303010b8180c4001d1400d101d03020b039405402 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 883466987 1250 883465737 883465747
    0x115030f0c08061902030411190311031923010f0906050604060b09120c0603130c06050c031c0b090405031e13170a051603171602100c0c0308041401080c 67
    0x2d1340207510242081d42d0325020600041c1c001d44481c90b480c4e0a480c044844e03801805d28500f0305201c2041c40046052003a00320403440000526180d070406c07003013a04074019003450703240910400104004800e00190650a20b04440812042a03103c07070a61030041c6c10030301080d61401e041000301c03412406504601c95051000c00602e081480450442c9030403581203904804008000440c260000c440258507015040d00c4002004001c00d042c0c402049903042590810f41d9410109803640103000034015400c40812120104a115270402c84c102207010b03284000506182c1000c988070390100642000c6004d410645540412000c0116002d140c406408680c03a681801c1000d02004c4e003111aa882502c5a9100840858414030070742d4401e074020203909401910318a000581280b008003159400e00d020b100a400074000b45d04400d0000b503048503480c1c40030144420a40710705982c40005020b10070955000700801c0300c0440100300b070b03600c191070691850b02e51900442d0116812148c54003003140600c4 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 883468237 1250 883466987 883467031
    0x40f06050127110403060203010b03041a040b010e060604050918010b0114030c031f080606010315061d030f0d111002030702190f080c0c0109091b110115030f0c0806 72
    0x4840c0741603d00380b00400d80781596079103603c400d83e002a041103c07410000000d01c02003100589a0f4404a400a0303c0c0780c00b186016218440100c03c14130505005040000015882380da0f510119406410000c004001d0340c00c11100c00b008242130a83ca5081a41c81c00500341c19542c0a100808a402d9400c450740749907a40d201c0c208030a81e00060401442e08898030030490400010043c000c020309a9640201168078110b000141515011080308400c001a00790501016034001e803c0c1c00e0840c861502032032504000c1000c6460003503080f0307040c3c00300d00a01094030006a0b0064040f01e51000707031070440d940b003108d1000d49412840191070100159100e10841400d07041450010100746018135a500c1b14460181c651911035030160003188890780203001d0407421580c100f615140a40040001000982c03650018400b000682d1200c94003030011100c0d40c062626025003005c403881d1290700d26002255500e180068801c1451041103864031191600481c1948002446600c585030f02003801c041e01e00400 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 883469487 1250 883468237 883468241
    0x10c0e030718090f03110c0f06090907110303130201350a1e05010e0a2c1603030c02150c0303070c0809030105010b03011a070f29040f06050127 63
    0x10040c51540381d02c0f002c105000c1202003851408a034000e071210407400351000d002034103294170107040341c2c031607441c01c144400709868020548a1844061b295207400b91111201590704821910351600c2901c00001040a000941c01c280b010840c0300382c0b200f05000882c5125511103600c0c004510111550981e0340c00f07108115060001e0300034107000e00c00502c0810000041c07a0280d8011500303181c0e5502c4000400540d0900c1400a900410107a0200b04010030130324072162800c40000e806801d002c006d007548081c81d10500202c141c030390000801228443c1c2e40d250140c02444003150980c03203000c0800407200007910310f4044910364111400503500c5c654440c0400ea980f6030a00d80c00307841000052010601c181c800b4442c250107000314100076603c0398902108000460400d04103403d403498240441000a40011041142c266008016400b0480c00d922545003140c10b4255003151a00c0ba2414402440349190101c582c0c42d000368014007140e0f884242c84045504403a1004030244402100c4e17860000140d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 883470737 1250 883469487 883469519
    0x30606020c18190204081501090b0d020423131202060702060112060e010c110c0f01230f1216080c03040f03050d1509050601080105011409010507080a020105040302010c0e0307 77
    0x55030003045400f0f51800303034012600542c0206809a03c454000101700e00040b00e0540144407020342408200311b82400303d411801004002030080e512001d0440c00340c000303130259000441161700c0e01c802e1480c09007007240c0201d000381000e50b00203085600c941c5180d8404212030b80314240c590010507040c2d00c0c0001486206d4440b00d400e0310790640d1068003d046090a0080400718021036507900745040c207489055080c003624503c4507210b900d0030356030380080c3e907004040001000744a0400640940c88695200091700c039030000306444160000f0404084d07000714103058059010030803250501108400d0591f01d03100701f540c2c2c1800e252030602c0001e00045034000200c1201d4880e01d0300a01340000d10700c100069945158072143c1840a01f2418000044a817150030741c44002441c4c010101d502d00000600f03242c120446d92441d040c00020000c0c0301d44d000380201e90400b640400300307a540e41c2020364024002c01c01a20120015400c0825003424a441490031548101300180903024a0f4589170000000c01c000c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 883471987 1250 883470737 883470751
    0x1803071403070b090c0f040204061403090312010308071103010c0801030803190606170a0c0503011e0305030a09090f050105010e0f030c1302032e0b160c080d030606020c18 75
    0x20811540020308612800b07014038180801030040401220802500c6d0030381422103030240d4418401000204d900000d60701413803850701a0a0303a00c2c3c0b01d5586c032a08511500181021003000d02000008124100c002032001e603014503c103401c0d150b00401018280c0c1e2060380c00d0000540750390014404108440000c1d50844001810109024201c1e4591401c1c2c8045a01ca03801103100c46200202038030501040d160311406000003049209132a8002a10340c0c001030080e40d1502410703146041500d001982400b002e10b030850b04894440501108c020a202e07600d000e60b6500601302403400201c0081030007081c2c16154141c455803500c981d40b809004442c2503506011381d1601c00e0341d9058601d511501c444660030025075602503070700d140010408031000c4444880e41da00c407006011701c11580d00440c1c003541c25108090740c403a9491401400746012800a004040d118000c0c840001580840004400c01d2010440d1000c0c0403403503546509030b844079000710650f50805890941d03030414540d1401c0040d48500 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 883473237 1250 883471987 883471993
    0x1401050a050d091a071d1e0a090f0516050901270f03110916020601061d03030a0c031b020a0b0a050f12010f150c060b0a05040c1718030714 61
    0x19540390980300c03480d06a0012070401320380b81405107056000e018604000004041d03a0203503800c400104010350401003080c21828021681c420403503a924041c000200742c0f0040c180255009100b818000788400e0b00ca00700c1e5101c108410208250041055584001d0140c495624090b030081d403030704401c440f182c0c00480783d034045180491030700b0806c1c020b1006117004218501c9843c801d0f03410721410400180c08503250b00340c0d2940c801c0401e540000c501b81541d03410b1a11080404251404200140358a951954103000100e9039411340c0da80100b14130740c0107000350740c0c00e0704103080901ca60b60000f24100001c1c0d08828a142c0a0122140d40c1000b010080c240e46000c3d07103041d004117641c260b40d411404107006407400b1030004002000390460010050013903014640d01c0e4403070303000380603145102c0004024101070f1903c0044940e17581c1d807000c1030003c10303001e0420b229446040070020203010503d28a1059014000003091201145840507800c9800c0c0c2d600852510f2016203d140d00c10882c43c003490000c2c8 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 883474487 1250 883473237 883473251
    0xc03081f09020d020403060b0904120c031e0507021e13020c070308070b1e06060304062c0f010e0303090c01080405012304050c041505120c090405030903071401050a050d 74
    0x20a00c2e00c01008000182c4100585a074151301c0c0c10426944c03245d410a1041c80800280008139807400070301c110a1200d410040c128050b1031400395101c50082070440210341015104c8032040c0d402c140204802442102e45004450003000d0300381102d400c142c65160800c404405035030411220b58001e00f5402c881c4800c441e001e6907299104c81c2254001d1204869000f200d2050011031500b8220004400d9444442410903140c03540100f022804000c1c805040349844401d0510a600700f254640720604103180031070007645540300110380e91324001d0f8014215601c1c2008900c0c6810010098a000d4140800038048000507840110b4011030b0161003915195a5110303510702c481207510300ca40c04000d584444402c1450941000da04010341090b0150140781002c0c51000c900c6914051802500c00827584900c982c000001050302d1f2040001e401078022519105102c240203000003d44410f1008074112150243c0351021801802480d40d40903011a9041c0100802d05004102910165072105c00002d060 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 883475737 1250 883474487 883474499
    0x90302070510020325031205010e071209020406090c021006030c0501140f071118040f0b0c0c1212011a070b130f06140a020408060f1f090c0801060c03081f 68
    0x200d075605100c01c031704907042c2800c0416400a00030022041104400c02043d850410300406020b80180800104034120f0880681003403541d0110300f851f07030041e00c00c0000c5520b03041e483e4003c01d422410034001d1b21030031880c0130181c1414003480707080c0c940c407924400c2c3d11480c0400545082000c40108280d2203030078014040ba6100d00c8024002841c01001c50041922603402401185120040e20f05401c0c0c070035108000c049400c0151620900e5441010b41c46d0f942e8843c4180449400745050140141c040d907103101e6034501c2c184001d04184000e2030840700523641e07520035440c00380074a401da081c03088409010000200310450300041e0b00c02051540007406200345e030b5422400303410842084401c3d60392001a2140500b90341c5ca0194410b03903400c0c045250030f080020003691000002c3c60040b504890341c1c00190030246441c1c0c20511030030840040b4807001e490f950034001500011940c03c002500d420700024a4a21400141e804160035403118505038650884240106d001500581682100b40000083c4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 883476987 1250 883475737 883475767
    0x2007020402042301080f06100c050712030309060b1c0308090712150e070b040b0f0d0207080315013b1e0102190b0127110a030e010903020705100203 65
    0x1002642c10011403110f4040c900241c500c101c080c1604a612080e80c1c20400340c3d88440d44100001c1c142800e01000e0400c191a2840c81d010107500300ca09400540882c120806801d0303001103850074804c01c420b008460000d801c1c0500d1018441601804281c01c150308000300f0301681c01f064001030403105903030000c4d4551001d801204e03102c4008a6041e02d9101f0084100c41e110b100b40b810403422070700501201441c091b12003d180c001c5001d4611503150000da00220404000d0440e0740c403c030811015034560826040005803034008442528001410031010501d562154040d04901a014122443c412290201201c4855001003820b20012514039542811f956070140291300350f20074071802c0340c0b0422500002803c00c10b13503400c1120400101d961040004000000d083e0640d45070041d03860403a807412440c40c0041010001e0580301c0c9150040c001c0c3c2c4510404000c0c001c10303855407024412550411421401c8407041c2c40d0160050300704c240140b10310b2901d106400101070036481101e05141141020300d02c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 883478237 1250 883476987 883477019
    0xc02280605030f0a05010b0d0c050c0106030c0612050402180702031e030702010b060715050601050708160303060e06101209050618060705040308030a09081909050a0504200702040204 80
    0x310310044200700504a480f101c0561018000c01c050002c0e51500d4880c140c240180c0320b580100347c1d114030b0040c0c000c03031250701640c0707013210720310000d00c11a5641c0c10030548000d446d002c0c0c1800075101c250146106030450203584d000d00d5002e400220400c46200710003240580c01340c03007a41140820000748000320042c03010200402046100295242400040a400c541c070050080303025200a10000c07010900c1e58102400c0035070400780128035076445200484407480b0703031000201205404590114103413680010300b40303107601ca03481c104455919076421519102080f00c41c00e601040c4000300700c4180307108803804000c500350b8400101d00490596a01401c001040b500c0d17038526200024000b015460820039950404ca260624515003411512840640d00c0010440e503000d94a43d42903008100c4441e045402c003864010361000d1002c25104000c0c0084034503c42c0c0b03840340740000008141032800e8401d0500c1d05140003d00e03403007541c440d800e005907130704001401d0341c0c096420322001502d002c00d00382c102 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 883479487 1250 883478237 883478249
    0xf030908070203101e1a060c16030804031a01030807030c05030906070506150d03020601061404150807080703410c07051504021503040213020408030417010203070c0228 74
    0x402c984182d0f5030054a10302a9105542d02d55044c031307008061541c0030301c400c400e843d00c09547d07066940c100c180c2000d1404098a0200d02000c0543c00c0c00005d22400d40081c0051f244600c44400e0098a410f450203000c0c0400e01004e080c0b04410841040024050700d00030403e01d2007407041c1c0c2d040108401c00280320750846801642c1c03640044040040384c8441d404c040d06558021600c00c10003034102e4500a6662505024000902040707007a1a501040700c2e2080e038004040302070007d030b058034001c100240302103416151007001c00c058101054110303000e400f0b8100444c0280184107607181c2c501e0006c9080c40c00c10b40c0000606a041080e080c40c0c0e80a210342c45114410100d01c2ca961410035282c000d1510800e00002103680c00c12800340401030b5210007000900c0c201040c0c3c281d450f038955000050740582041c4007001254030014002901800210140c0200c0e8108468113031030040d4486418282d00c4211034600001c1c100d5108000185014108011001104000a2018018064060080360b500d40140c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 883480737 1250 883479487 883479491
    0x7120c090602010b1504120c090207030f03140610050f0903030c0705101106190b040f05091219051c0e030301030c1205060a02160b1302150a0f03090807020310 70
    0x34441c80e0b40901606011a6040d07903100c2401e41e410700c00c0700c213a004601480081c028520060002d000410780c3c101c000c1c04214070f0840d602c011514018042103a1200480c0110b410a80c20060041611240ca0305c41c80c4090010030081d01c01c1002150141d00c1140b03011507038403040c001d010540d20308001030310100407081c008016941c101400c01034004800e010000410800d100300742601000400c0c240d40bc150f0750400c00440390004200c01014000920040750044c0c82c00722121010880c1d074100d14040d141402c20741d040303032500100f220302d0782c803420100344c8900e400c0d1a00340d15928802e000a0890a080303102c80d00c0d288000b01210350555042c249c01403859030000c40140203000c0110302000003020b64400000400308290b0780c2e6900e41c00c0040a0140c19580030a001c4001c08501e581c01c8201503010b100c0240c0c074903007190b40c14401d5400c094164000d03462001d440403a80c003a013049070342c807440d10b40b034914001c40c0c03203182180a802d9081c0c04071881c51082c014600141c0b0300f007142400c84080c1d1703880 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 883481987 1250 883480737 883480739
    0xa1515021b03070b04030b220515042d0b0105030d020c1c0b09030307030f02041d10080a080d4508030108030a0e04060506184501150807120c09 63
    0x90323408400c00b40106500301da8185100384000804c001040303200e003411a11072454a42c0d55003840219000004070b100e035112008454400501d85945407001480e01c211141d413000d98031030003456130f41c00000c001100540c3c00004400b003a0302c0e24051a0416501340100c1480f920700507920701d02c05135029219070392143d0010040c01001a0140940d800849030f003402181440e1811010381802d09412444003501048500032070341908495850302d025100b01320031654489058070b45089180d004583e00140700b40380542050201c00c4440c00c8040c410a181980240000010b1002e040c0c94580e6010615054441d1500400603040c10701841c0280f010328003454440002c114040c180510050406200f80d00d001814805035841c0426103000c001c01d4003032a40c078a0300040c0460704540c160b11029a00101c8148030140c1940a10040e854038031044840c1c440481000e005245e8458081c01805415600e40107050511440f59254a9022000c0e20f130100000d490f4070309110440b5188203014000801001c4 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 883483237 1250 883481987 883482001
    0x20304080d1d12090105070b07020c0a0f0f05152502090a05011e080303070513050612180d020607030507031b0206062d0d0311060a1515021b03070b04030b 68
    0x403091000b01c2800f515503242c1040500004c0c160321452400409141c0041c010801c564403c0280004204015100003071680d200d00b105503249995114150300f0b100035410120311800c082c0001c00f6020184104941001c02c0180246c00b00c400c18900030588a01c0316aaa0001d03aa50a20b014010540c0c00f5001a10b9410b0004600c01041070001d410f10208103201e040088035000800c4a07031080c06881c000740c803800c1141821143c0034141c1d00050744050b0100343c8501c010340011190340191040024898540503d50300705865559585002d005600044000f410007070003604140c1d031007040361900207291034890940348400c04240c0d02040069201c04100102c60502c01001442207c00010900e1506000700031040310798842407115020700c030a81003240425028646000e0041d0303013202556000e01e80360b5491310050192014035403500352891000154002c4040844106110947c083c09400c800181105034140a455015804d84500e040004814941c940a00040c52003031803004a43d085c440 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 883484487 1250 883483237 883483243
    0x5100c02131134021002030c01110a032703120906021801030e15041e0b011205100e2508070e24060d050a4205010e04020304080d1d 58
    0x5403824a402d41e06202c980c40c4000c00b041460f40d11903044910300134459000c60202e0950003000c0310719409600b800610a0f4400c40350000c1c00c0381c1030441d60100f00724070880d414001c070380e00c0b440d41840f4011481804403000c01d2141403190051481000003262500ba155941d40407a4000c1d400709801c2d8030ba00c0c01a069560b4103008290302102100f000f0401d100a881c844c4c007071281c0103400100f03030482d00c1c0c110390000d0f201c3d190b0f148a0103801081c450003960799a405c0d0401001800011141750040d000c098025100c1407003900ca441c51442c000340107040c1441c1d01c040c02a900c14500340322803103c0c03042c0040c0038881049072002a20204207140a5800d050450309900714805441a03030600490401c5030f811303102c0c01c00361085e814090001003010b445a07801c400040158401052681240940034002613880c80301000041012400c04140290b415104800241d46c0780211800140007001c144514034043c1c001c1c2d50400e0090b20302c9450f28100e0a5040120303a501901c01d03111324624140c20342902024 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 883485737 1250 883484487 883484527
    0x40305150609010f210c0602060907060815060705010e0f100f061202060322030f0f03140105040c0201150608180604150c0c0b01031b05030705100c021311 68
    0x256000a03540d410f00702c0342480d04c4401d0140c0c00201c040074007481c006400707100f150150150003111980304140c680100030345504049480b00e10368415041c0003c2c510f0b104040d11407060030000511420348400804204156000c01d00a482540d221910800c0c51030303060003900c0a02c0400700041ca008402441d40d00107444045292541591070070750304201510038119407801480e030448510360b580e9140f2650450090640380e1801c4941502543c0d282050381041c0e400382c0b01d01d0aa1250340c40c4a0001000b14103460980c4010900c1c0c40300b40004011904294100880e10622400003044036014103004030341c40b4819500c010000351200c0144001843c2c06211048a2501d440113840c00f49003d4441001c1030b500181c0e031a03d07039a9610040c00060740308200d5100510b42c0000c0c188811759403420441c140100604480b90903a07000c040004423446c00180300011140040c0c00416010000001960f203034190b00010380e08029155421111103c1c40c1c415048005818010380c1d840320a218042081441c1c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 883486987 1250 883485737 883485739
    0x40e0c040e032a100504030516050105040b06041514040908120604140411060906070609030f0206070309030c140c090a0f1811100207121406130b070e01020309060403051506 76
    0x9090070b0900002d502003441645580d04c103030049116100c40ca421601c07441170300817100c0c074840d416102d0030801006400032070050b4001c4080d21015181c8004000403500203a03a00c14901c00c2e020010081c441c2072004000010000810018402080e070f21a6191a0b02ca1894a81180004410004640703072921032b002c10b0f0403620603611180c1c9000d954102d8003108482140d885a840800c0105072581e940c0c00f110002a4080428811000c0318900540054170514001025008c0e2900240916210f40300d188185070b010713507a4064280443d2980944101c0c40b42041105004407070903d00310b030300c481c610b95010701111400018080d0070003454504403240d14888500e01b0448550f00300101c0c8108200c1d41c2004400c6031069a0041b050710207a181c4400e690014400c0000c2102060a206800c010b8040b401568826101c182d82e80d000814458403040000a260043d020041804244544a1814440011300447e0f103491103000003341543c00680c0100c880343c2c014500d6400090b44504010703005a0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 883488237 1250 883486987 883487047
    0xf051b03040b01140604050a09050f0108010e0a020405040812041a0a110307050c1f020706150b1b01060b04030f03111b010302090a180623010509040e0c040e03 70
    0x500d5540e0701c1282d070041c0f10f07282240070303c030b148000302d03598000445006140c024404900c0790358034001031000d003008940d0030003001200320002400f0507060080e0b21240b01c0d58401740031445543d0342000020034019105481101051001007000c02c0203034402d600840c041c800030300c18114506000c04600c14020500507105040c90601e011041c2e828007600d8018209090280c0c4134031904607114076000c207100a419107100141d01039041c001e0340d80e000f04030044c0180341c20700503030b031307001c600003030362408611a4091035602004a00c0e42c186005000d14042e01040001240c196034030b050614803a04140c005551111042d103d1800f050303040702c003440e460a1404017600c6880710400c0b03c80c402c000c1c0b403903001d818181c0007c2c075143d080e0754204250001e03180040c042c04c081c1501c03103250b100030942401f950000c0707245004a07028481c2179044050841005035030b40c91400002c40c061001070034421681109500c180c175480d030601c1c0da95024200d009900b01c0c000f55115204490943c804004150b05000028 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 883489487 1250 883488237 883488241
    0x1180e1b100201200a170c041a12010b0c0304031a0a06060305090c121906021902031305040c1209030816050702060409150b040308360d02030c03010f051b03 69
    0x200582c0caa0502c1c404803140c2942d15068a880c06441c1c900d55220886d056032a2081080103214180015006550110403081e0300400d180384007003024412008030b0003403041d5030001040728040307080040907084003140561b81015a0780d60340b40b0a58043c00007030241c00c05072104005d124082031040d00001c000f145401e01031820444003003521081100741302d0f8040c04d410030f203100440d402000b2203004204001003251320144241003000081d04a0180000c40071000c128260466100100b40d41040704401c0c5c0c8110468505010403000307000e200b2401d000d2080380d0180500f00500c2d48103c0944070f0080d01d4021261411804140c840b0701000009402d10805011110150311079800b9030701915210240002c030a80c600e005995400103540c40f001209400090201c2000381400140c8000d01e03d098101c1200340c07490502200c4080c540b0315001c82d901034002210010301d4042015540c10b13002400380c88841c1c1c407507000302e0b09550351000c4841c06503440d00f0a100c240c4c101020001c00a0074529a0700e4118 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 883490737 1250 883489487 883489511
    0x601090218061804091b06082d0c0d0f020f03040510020f070b0a09020604030503070606050102190803100905150102060f060102060403080c190314060d030801180e1b100201 76
    0xd140f5030001140120740d1084030a08000e01404101964501d2000c0384011565480004007221021a090408004c555003180031095070803495a02c4040390a0040c000b80d603504681124541100003110082c3e5241c81050340c40601d1b600c018160588001c404543c3c0f481c0c01d052003441c00124a03508200c2e18130410500783e1702075041040d10302543d4002c200a21039100d03104288064118030002943c0900b00280000c02c200c4001b008103552882030006012090fa034100580e01c81203031a580c0c2030420600c2c40801c000940140040d5072150005800581c06501d40c5c881d4800c40b001243ea440001c845008420300560301001415404400e100c0e803000030340b0384500000d40b5030801400040600041401041803550380200b81c2e00b4203203041c070000d040766007003a80003400f800412050042d01143c24010401d6400c4c404810001c840c0c06440381040c070303460640464084403d007080558407503610340800403071800911145414154052a01c10500b0740c1008202c6041e00107580c2c6010341e0b142c16509410 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 883491987 1250 883490737 883490767
    0x30040e061809060c0708040b0412020108090c03030405120f07150e060304110d020a1a07121718030f0706060311013e0f0a120201090c050907020a0203060109021806 72
    0x20144c03180c5030b016150076252502c03030054011a040300756405408540811040030f01a1210310041c001d07a40c040013922003c1c180c03900d988008041c039815400070402030042e0b04050450001c01d240344000c031207d022003030800e10f0900081d0b8001012500e00d4a0108a510381d01641e0340200c080215445882d41c201640c90b2403403011b181ca0040d00038031054043c14195541c2d24901c0004105810000c0286050b010351401d442d03005040803990981841c001381c0c412445403004410707010400201c0803094407a07400c840080007000c05000a60b10080240c0e100071485140645245172140c1e0b004100f0758110701d03010700c81c9114410f07810304102c55411251005405e4541c2e000340000744e280c1001e803004158208141400000d81c45841d588035001d0300a8001c14002102c030b101902900300c02d841b58407120340481c01e031208804007030b041007824002481240f808021168005200d401252200400ca0b40440d090100c01d038480c1030b403680d01041800310a202c1030744400c07e20034112681482e040c0d001c900611 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 883493237 1250 883491987 883491991
    0xc1e09090d08160c140a050303010605070b0f060105030609040c0f08031e1c020c070506075f01050702030a180e160e090a020c010e0f30040e06180906 66
    0x805a44070701700310011039050141a00300c80d040020f0340c1c0d8942c0c40740000340840c0c0c001c59084521902e8080092011b210351102c1a010f03c005a503407030310b55210a410810310b024080c01c10758003840412030000e42c0d5010448818010200d0101454503800917100340f105070041e9901c4002c9030710b07040010f9a070540c2c01441c8181a0600da150068841800110722840c114860304865049100041c00341c003484070681d0191a00c01040c440840d0010100c8c0c42410fa0384c1e048004044140306116030000c40018200301052108030050b085c04180d0400c003501400d48005a03421030158000251040c62564000d01035400301801c0036000740c5062130070140c0c3d0350700c0400030040040d0001d413050050000d48100981120510002d1001e40942003800e0050002c2d80100d0315071555600e445c61000d940c02d00030582d40c1d81d04250801070942009030341050411101507030800d100442c00c012038019461141d1002d0005448061150700203880c00605005441c0c800f044941c800e14480410052600d0000445603 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 883494487 1250 883493237 883493243
    0x20406082103070905040204061d03070303050412140d051201080304030c03061d0d020729160212030c01090308090a12030b06070f1515080c1e09090d08160c 69
    0x75503d030f4034540c1c12910b00f4226045a80d0044c000900042c00703682c07100c2d118070003400317074010925212080010582d46810f03610005000c20014402041781ca10001046400d1502944580d42b4040304015001c0c10580021000000f2800c0840d00d03a00032100a86418090b10b2064010f501c0d040c115180c40f0381c100e4091000130000c6403684240c420b0403191004980481c9204002c030348030440c950314060b4035540203004501d4001130b00b50704a444200411282c00102e08a01522031510107101c1481a80c0302003060142d80040300030140b02c15a5204000501180320b80ea000025822103074a0000c1c01c005000c1c02c1d83d080c942c029650000443c5041c001c442802e590703801c0008032158132102290f06801150b20240c0191041c09021044c4944000ca00c001c554110a0130800302038004565504060300780280342059001d4008542503041510700e4044c00c0c200e10f086a8011006200010b8034048201c2d4600e8054114010700c212843e040400c580d0014a40c0a2111304451050402440c0c10300c2c1c80409 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 883495737 1250 883494487 883494553
    0xa020711090702060f060105090f040c050f0d2702060901200102130e01060329012307031d0d020d08070c0b0a171306020d1b0c02040608 60
    0x29408014001111140118000d01101c210b071401c0c0340040d441c1c0c0c5046401500d001d0044000440031741c49007044584240b80141070801c45100e540501008140c00d24080d014000100045451070725034001030000c1d4005c0360030215015100c28940c400140c0048030707210722907040840000040c0ea44401707a40510500303181000150607041a003902e4a654803200346d1455100203580407191010080c00c00640d44141d0074000a40d80e25007049007100c83c0650108140f08441c00d14000741c100d01407840000c0c0105141095071800003490a41c00400c0080d0348551100c1c001508404042c2c01c03041c1007903842c5984418880a21442010400d650040c00009101c2d070702030540c10f03081084584c1035400c404d401c1502141c03800d880300408205035121054610201c0c0078000038180003409c1422040c40b0b60078111a200e20000556100d5010303402c10301403841000e480381d0b10a1000c0c184600d48501c0425141d50709184482c47d40148070481e06503410111054010500c4860320782c0380800c0307100000031100340d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 883496987 1250 883495737 883495747
    0xc180109021305130f0e0724030e070e2a0a0f14031305060a060f18020904110405120303090a0b1015050a09090c12020f0405090408070c05060708030a02 67
    0x1410b48400a150400d03544150001240e08949a04d603200980c1d825507480e041014024441c0244d030703541c502d0701c03502d600c44100041c01e0408413a034120f120134a140e28200854100c030309c11081c1d0b04015080d00592401c501000030040f0303042a12400000410301a00041d001c11283c1d100c0700258861041c03c0018060301d2011460020320452524a000c000d0158094503030801c0611401000c030740c0300b800d071400d104100c04106810a10301c83c6008581c00d0360101542e139440d011001c05403411846014070305980c20301c01c1a0365a181c0b4041d0007280c0007000d81c01952181004c081041a21180307011045c1d544c8203204100c0280c400144249000d50000d40418680d0764101d1600c072080401c0d0406000703405503240c004142038200c00030382a0b507130b40794443c160790700d445100c41e100302d03542d0a100720006098141e40c07084852160380100040950610715520301038540010402c0190103440456031441c00040b09800c3c1b00c080c01c61140a001c0403960640790101c161030740919400003404400780a640021 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 883498237 1250 883496987 883497007
    0x8012c0907050a0305160503030f0706050c0c0d08010611011a04051b04062303220825150b010512090705040903031a01090f17101506020c18010902 65
    0x407140c40208001002000900c3d00da20f852501c4404240e5007080d081502440441c2614001c03040e03134172944d0158407a905101c440c6e2070300c41c0a400007601c0f170201d49204101100a030003003440b0b5883c1851580e100d00c2c246502d403c000420ac3d000301c02284130305914014105580c200054600710041804031000314003602c902c25104541d14105282076920309001800164464200d4407017601c85130029100f0808241c0342d5082d143c01c0c407080f030300782c491444810f4240780c0c488850364841810703a010f500c0d818242006c0c62080380c10b040d50900708007030b0741c0b087d203040008100551402042c240d207821420301c01003102c0c200180c6140110002e0b40d2003106070f031000401022003002990002c000007001444101c41c0c9042c042c0003000f0700314000000340034610307900d9001d5006803d144119003880c804a481d4500c1c10251081040b046440c07030101d0300800340c12020040e00c03030140e03103500185004401421480d10b00064901000e4a5036607000785010345010122200242003503044a034071000259541841003 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 883499487 1250 883498237 883498243
    0x20c0f0123090a1e0f150503040f0204020307110c040608030a120b06070c03061802150d060503150f0a1802010e0607120905030709050c030c0901090b0304080a08012c09 74
    0x19420350450b101c4072000500c40e80020300742d04e4403655484070a18554441e9000d41c0c00e101c0342d01030070440190a070201c0a000784603c000310fa015010310360f01103080c450383d40060107903802a501400003684034082c1c10000c0c4000d10080c07045682c2240d0070400030f031804c10580d4072401031007180703000d00c550f01c80a18100d9006800540d601c06000b0b0030550f0b2440e8a1800e40e8040340c0c0f42c04142c50180c0341c04221302c20021094039400e2001c2e0010120b400f03000c8148045d80d013980c00341040444003500d909002a003514200224410441148010129840c0104074003429160082c4900b421509049080d0749580101240e024a03d03020302e00003490720508004101c6134880c0541c02001040300c110050212a4802d2000c4151801101034a404031f590341a10b905442050320095803019040021071442d140020040243d00b0060405081d22540c5075600301c130b01e4204031000c0d01c4081c00006e0012855600c8030722507015106920034280703110f14103440000e0300700541c4010300b11000746001040301c0103410 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 883500737 1250 883499487 883499497
    0x150c0d1b0b100f0605030a0b0d030206010306021c0609060302040506030a121422080c041505310504060c0f050a080405010209030f01062417071e030c020c0f0123 71
    0x10114031080c50382e1340030024004ea104072907010282e031610100d0a154500500340e10b1005801da80140131503401d5480750f030003d5004000d001403003003105401d41d074441028001d036030003800c0903200019a246580180000c1d500c004043c184a0381191102100051210310b8448a500f03051170803a841190310700c040901c5d8403902021048013000310f44604049402519880c040d0741d030607020380708044529424042642c41e00715050944c030070324040a000a04001400c000250000c2e03080c541c13942c03600e0719140840c40d00c01c2c0b07000284039220402c02080c884513010714030185000b846c01e0521704030300340001410b034001e90506c042000516408541800342c25016a0b14142c4000e007940d10043c01c40c2c8005000b02800d101d400c3d88201800300301d085107500030002016422803a1288054130507510a51401a68001d000205118401c6405801c071015180c01d90201e19240e100020b11240d43c0d040685407000d600c0f003180c8a00007205810f56640d9000a080424050031000c1d08100e01003148104414010 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 883501987 1250 883500737 883500749
    0x105090a090b180a2a050a03020d021204030207060305012405161b0f0905010b0708070302121c051005100e01030912200303011d04030e150c0d1b0b10 66
    0x185506001003030200d17600510021600c44100d00400e40000b032924444a0765180220214106010781c5d4182d80c02a0006c0095000d0200300501d00040424409000c000544065005030f000e90740c148001d41c6c2500c034580c05030482d4030749450008499080d428220040f10492000c0001c00b096121119801c10304210450390300c10b0051402249603c000b45079441c85228800b27100600e084005040c00c0603100300b42c180c0d61003a441a1418035242c03946a4558400a821000c500c10541788a40c0303111070101910385070030302084486503200c0903c075000035203102822405403031109280800c100d03a2741040d4071400707440d0381c2040207005001a0058000741a08840a420b245201d4a80a105a800b084580c520a00e80344400500c040d40301c070031503a80c082409221408400122903c803400066000e26034807510a00d00000d80e1310150f40820090400310310b03103982d290800306401c161a0400e02180441d5003a52400e4460b40c024400c0625103600d40c010050301100048001c07880440c81c1d02c5613240a810 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 883503237 1250 883501987 883502029
    0x20f0f0a0306020d1104030c031e060204090b0a0b210a09080412050f0601030f230f07170c0121020702061b060106171605270901050105090a090b 64
    0x1d668140000079500510b2208000c4e850101182100c040310000e54003540c1d04055800c1343d55003580d031218103111800c03401880c81c2c0a41d03070400e030005095000810107041c031020b010030001c2c695014400d00100c550481c80c3c4083c000e114102003499641c02d070940f0030314034400c00308c46c5489200d440c20080041e24400f5095040000b404118416005000000a0320400803aa0701c0000c04403496141e100c2070200812151b203081d0903102040c2c6078400c403903064210451103403181c3c1d1299105450546062102c44841c0c200c244100600c1262021030026070f13440201801c011280b500c0000c288107000080c7c0c10a6035011417a106158040344e050b21511540a05a02d96a402004d03080750180d1540780141420300c00d0200214269114500e441180300c10442108e056440300d144111138012034207011410004184000503102d07090244400c521101341e15103500b020040401c0c003002c2c020582046040c45420000750b0003580b200c0034240704031a5a240d0019007815407200152103e20071442c586c05da56 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 883504487 1250 883503237 883503239
    0x2120a050601140d022a0304090209011b1a0f15041e1103190207080304020f0103091e1b0302010e0d031803060209040f050402010801170309030114010e01090e030403020f0f0a 77
    0x360315078002e014056021b515206820103204454a1060050000c90b03c6c03a04113110410400c0f980e5006400848030504006201c100580c06c031004290360040c00740c1e2198400f44407407843c04031802c50b144c0c1060360403400072490715003c28840d21801401d80d419004564409080c015071043c0016451443c41c5410b0070b0004161207403444049400941e0401c81001620403013a5921a40307200b00c585165100880320f0556480e034003000041ca42008026041c140c60700041c00008000688201d840300c0540c81807501030809003070012616405004905088143c0681400075070b810030701c160b25050341140c0140d1004654901110b03911144610200e407108d00d13034004020029241c0213007508140a4400700031203019208584181c441c2503e000c0d0110304039100500070140c400c0034450744c030300700035007168500480d01c0086421101d0540000c020402c0002c010301c0750b600c2403200305004141202d17051040d10321320712400d9107a00c180d2100078820b14100011050b26250060030000a40c1c000300159912 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 883505737 1250 883504487 883504507
    0x30e121b07080a0212150702100e0c060403080c19060c080f0708060f06070803160219170a0e04020c15060d0f1205280e0402120a05060114 61
    0x9410450620041003500c10810390346038000a4040d0844400c50020542000d0607020311040100d84140700c170003405603181c1c018a641c08112568080d09281e8003c0050b113184428000c200c80c0300f510080c40ca41c00c50050040550b0b9940195000e03250000502039075800482d01d400d18149a003189940351030380004198081c04050b44c00106080d400392640344007551025098041c51038121118404900140082016400e0603440070000e0b680c090300c1e141c17a2003019103811006410441c4c00c0311942500c1c5018144a5a051000301d0801d64080b4000304d03c04455560b5400f1142c2c5d0003e4840350303500104800c54000c1c46080f40708011030f00070744219900c0305161001c1c2d484040400700c1d411000041004200e20b42800384824010641040490420406680e40c1121000741d05105000300070040c02801810781494800c9604100149001c42c0209200207010340030000c80321226106070b00c1804a5801d01c2c400b035040ca0303440074178140d00160039521400180c03030f1050038510f1140740003004a054040 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 883506987 1250 883505737 883505773
    0xc0703050706030f0b01081f05060d020d0e0106180f1103090604030e03120f030408040f15080705030f0402100c150b090c0c03071b0506030709060e0109150e01030e 72
    0x9072035041d5014001114165440d84c151040800c2c440d00269500002030b060b0341e402c4200000e040b16001201039159941da0010f040d9401240303a042403d6030004045221940c24031511107418040002404280e02d8003240001038080c11000c0768a50b6182c082c1100300c17081962210f48204004003d40fa181d0500c1c4002c4d03542c9030411102200495070403403c829503850b002034803c0c0c416a20028035071500141140308005504013500440c1c48080c140000b156490030010000041e205100c4c400e21030071302501c8000e000000c082e05220902504009003d845100310002030b500c160180e615032103540c0e0f1201c1c220f4060f040000081c0c6544406035809a10464035004076182c2101101e00030400d440300c00d862003607440350103005040c69000b04800780c0062281a0b00440032401c00e0b404524450ba07400c003161035640300b1240c410005003524000c1c000c0c1da400003207080c0040000c0c609010383d02e0030841c8a2542c00f0900314a0f00a00a01480f41010341e8441c0d0441a4020700d1322055910300f981120f040ca8ac = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 883508237 1250 883506987 883506989
    0x1b0903010c122405061e0c0a03080a0624210204052e0825021018020d060513060212071709031e070b15040b0d24020c07030507 56
    0x46080e080000f01c034881164128103454110080c6180d190440c80c00040201643c031980200b2040543c2030303550640130500d5000391074007980460150008d5107403481d005101040040c2000d0a00d483c001d0180030b0180712007040f9803054800646441d1188210100352400b08100c9180b1080c482818000046540d868014004850069881d8010a507290b00c0304000c260f40301820001c40d40c0241d414545151050070700c0c58200075500000d00c21000a21403528981d5001c43c440009680544c0501c442d030302131403280704d480d4401041070042030505940010140300311140098425501c03000421070f14207a480301e9550541e4421030465455208105030243e5040440b4050089050001d402c1080f01c3c1484a40f8810711080000c0c0d0302d000600840910300040d0903c45114541e4140000340016041d0a03020b0f0040955480320038101c0c07413070300810040d03030388444034980107094104d150070006181200b226070100241446401d11480ca0709030000038018806041c1c0c1522910703030004180301d40842e800c4 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 883509487 1250 883508237 883508267
    0x4050703060f08070b22120819090518041b080c030f0d021e0705280510020703030509041b0c0b06010e010927020c010b031b091b0903010c 61
    0x7180c007030303480c1c3d082c0c2c1d2280e100d84141203544a0801c41085d0740341008682c1c010300b01d102c0d1918040c1a0312640340c00d00594844070100c1e0b20b503c00041101661401ca00e51740107046141c0303801d070500d0781400041040003686050f2402100810313404501002041030b14032031448103100444082035610703161540e9a204101040d8000e0081040d11101110080382a04100541d90010903950720040a107002c24969000c5405550042060210703031030f03032102010004a20322007884047c0700b4200440710810007a551085201c1c9061000e00d649441d004122a0f00701d0b9007605102c1d44901054000c40c000d41116080700c1002201c1200c440c41040d0492420403181e400f80482d45100d0f69440c005688105940c54607502080b03c0c0b05003041801e0310502c50702e40049480c081c649420400707040b08010b90b0054200702e002a5140d1188003460704080000d0021500c06075400f100ba8403d2002044e240305010b0928031030070310100d4402d080304544c00200d65191a000c0e000300004116040d0042c1101d80c14071203a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 883510737 1250 883509487 883509509
    0x80d0905150f12040819050a0216051e030a140610170a110d0f0b18070b1902030f1201051302090f04020a020c0409051c020312040314090405070306 65
    0x150407a032515409981103458030340b428a14051480d0420b5052070b00090049404500c10081c40a07aa41d03900091000d8542030b40700c01c1d4580702d810380b0190400e620400c840b118607101c0c036010400740c4d56407104448003484182d201003282c49030101080c00c01005000c050649111642600c2c20b40800080c92031240d81d412000040301602c0702c807000b0601580e0340001070300781e11246213500401c18885100407607140080c031041c03041369565100140d05d4942e210503610010114200f02e054105410011410ba128a016244160405070300740d00e240244001c406140500300c43c1405624000c104440d60302c00101d83d11525030300b41c1130150510080c2402514010f14064100d28400d40b228000e490b101c840c0140f549030202a2601840029080301c2c030103a0442c4500455007407941c50302c0c812008001d0041e409414040e07012140418840d0309402c152045620401c450810f440380e0f01142900541d041c2303080e03a03e251003500d1420450140b090f2039a44245030909010000b90158044002c441c101c40341 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 883511987 1250 883510737 883510759
    0x8041a07030c080d021b010504020103052d04050f0f100b041103061e0d0503070210090312050306130c0210060602011802131b0507030e040902010903080310080d0905 73
    0x511400360410040205032852014000a001000a0011005030700801401d2004940900e10000d11035900103003241d41d10780500041d035a25000381d40d0302012200b02c05001500d191014441d400c03480c044991b0551050011a0070860103220ba840d0b003660160031903120900b00e0861544412991003460fa0b103c1c503103c1202241d041600500741c2d0440c502180506640e501424010344a8614010302d06600d0720049420b60b5949041000c81c409004800440d100c4a09206010300b20380c1c0c00450720140a0744020030030020309503c540e41c04441e8603260458403a1a103201040503c41c0440c2103484041c00c0c4404801d00c50740c0018415800382881c0d0091204d1652070500b0303403c859502c4401544405108441400750078022030006844030082400140b88014446801c86401405851000510b00140c481c05144c0e0200c041c07051240100c508201d240c0d9207a00180c4100e0841c800204000404400198808888141200109406820b031000c4400c000001000d00070716005062280000f421 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 883513237 1250 883511987 883512029
    0xc01300504211b03030e072607050402041202120a050a0308060127060e06070206160b0c0c213109050c04032604030305030612010b0f0103020901110a0804 68
    0x103d08140d001482510480070b00741d1003c40103010004000060b9100d681e0b0001400d5908000b4070780204010820305060070102c50030907080c10030541c046ca10550041c031080c0b141d6440c0b1090408034ac6e43c1110413403c0c0601b2814001c2c1040c0302c03860041c1441c0a1002620280341d000035107a84900800d07078540c05401c064140702d808852094003a0b030030007000c01d00c0178000c0500490013038281003002012941029010f50004a9560000404042c01084e0500010400175890348031504000c803031800905000042103c036a82d2001c02c20750307030165285120710002e800c0680701160244920395a011170550490003c01d05841d4a10303da1809498040b24002400c0c44030384030300c42c003402000400d18501451512002d03101e0350b20300100400c401048208084c16000c0c0c80003480190f12075114940c69103481c0040004800c0303440c0f80004a64107100e054003896840c0c941c0c0808050090900585401b2045c0048404440201103641e0b540310f96004c180c18454410080d20842e95000002ca10003002c480c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 883514487 1250 883513237 883513247
    0xc030f0c120d0c080108010e0d081909060204051f020a1704031203060806100815060a0f080606041104180906021c05101d0c0a0e041a040b01020c0130050421 69
    0x6145023810f0b0b0008080c0200c42842100b0103030b04070048a1228440d0003982c1003e0080700c00143d0201c52690b40090708006504203120003050a1044004501041e40b4000010303440e00c2e07591000400350b80c00a841c0300e18004040c82602c0181d0303049020048022001c1d03001400070030050040c1c49180c880c0100044941040080807003e450304e00d400b0300406221501040e1b00c41c10050b00301b03540f283c4512400324404244d010b01000804090b00180035a090680074042102c07691001680c00040400c01440515490304040028007402c400008651003503042942c001d000c0c02c1110800d02800c4000c40b150119141c00c0103004490490003101c8096171002d281283c03580d001c4844450328800c800040307006030303c6009031610021a0808865050103d030000702114030500000c920580b10030f003a02e00e5030415102d2690f00b500e0a00041401c40c0440d40040c100d11951a64101c1e0840c116514404072a0b8812528100b01c044007410300443c1094a020301c0c884007200f9000c1111500c400300c006880f4860 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 883515737 1250 883514487 883514501
    0x6050a06031e0507020d0806060a0905100c0204020d02040f050306130b1f06050d0c082203120606090e07020703080304030c21020303011a0c030f0c120d0c08010801 72
    0x208160402032406100341c0181c90303000300e000e1086000d5416030400d40c02600441d481039800341d024080c2c1100000024040200240c5a940184024040c51f010303540c100210f031055800c212000105039802810031140c3d40941c0300000e42107400801d0350400c445050300500190303480c104040c000c813501c4605143d9942011100300c03203c2e01c075601c5c000000c41c0700403121640128541c28030b50055000903000303500c1d080c041d0340710030005130001944804010440c8a00410344442d03282684141c1480112031000300c480c040c03011a64404043d0120030580100011280e8410581e0244900c81d81c039000900000c0e8a4410094850090000101200d10208148090300d43c0914641e0443d00d854904440a21910381d040b03070310241c1d17809003002038000f0b03685805121006034000d540e6581031080400d8103801e111810b0280c00d41c280b00c0e4011450000c03040e038032030a1911034125140e00050f2040c602c1c0280070341c844242306c100010100c03501d044d182c008002d442040e4881d1022030366600704060807136501e = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 883516987 1250 883515737 883515739
    0x13605031009200a0f0b040501120b010905010f03020d0617010b1009091107081801021009020603190b0a06050702010e0114070f1403130812070803040b130f0609060f0605 75
    0x10015500101032401244420354083c083c005043c0310380c032642c1c8807858005c0c3d500141564040442c040107250ba2051240b2940000d0040c144a0520200000f03446003025020322410300440211036000d40744a42e05542131a402030400340009650340b10102100c2c0d65454801722254200903000182d401d05206050360101190b490b4520503103080480c0000701480c08500300030303882c100103030720101d40c000c00603200d140546810f0b08007071092140064908a104001110300c50f05100e541e001690b540410740703a2040014084188115020346164014410000d420754001c0480002103081c84e07000d006444020310030b80703c8a244900130030064400c084500032902d0511000c02042d0002503101c13030010704030f51051050304844040760380418216084a0582c1c1c00c180c810100c10081d29400f0032a0000f40234003030400030704d042040d03115800303a4480100080c02c110945804191415003028072580e645404c00000d4082c080d40c0d00d08900609000d00094039581d0500540618002c8940b10707a10440d50 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 883518237 1250 883516987 883517003
    0x50c010201060b040e060310060603290105040302120304031a04051612110312030a021e071713081207140721020d0b0907050307060e0609013605031009 67
    0x854079060144c0603200410710358060080005a13000000c0500274a00508a641c50125100c0d1013844004a11a207440d400034030000b900e42c0794107403640c105044134152501950303030140c049414090700703145101c2c1d5400184a0980c40c00c1c441d29009010032030034003407440780c0140c6007101d058502092000d6914007a04003e101888840f500082c0110240b01180d10090306840c00f03071640801140030380e081100c240b65180e4001415822101c3c00380715446800070150300c07290400c1003980714901e07a8152924510020900080d421640703190000c161401462050104d8000c511020a210501c0c1c104082c01c40da41100107548e100c5050002c985001030340c2c0c44462b01104040038604018040c10420b00c01e980040171908540045035015204074420f06560004258862803c0289032802c14954422003c00c10002000116030303940c1c000b100d0303551700c00b40703003089000300c0c440780c000019001038000c8484c100c0d00d41c046203e50501d00603c3c50840c0c40403025203400300d29074460001615565000209020 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 883519487 1250 883518237 883518239
    0x507170601210f0c03020a11060c040302210f03070b0114090f0718031b0b120c0304170c06100611062202130204090506010306120605280504050c010201060b04 70
    0x110142c21550880744500000306095100c41940c07002c0701c00c241e045000282e000102007006580000040020200c00d00091026181c2100c0e00794590150b1f01009104e60741d0700300c60f60210b03181740c40c490030b05151000541c0c40302c3c05810300c40340ea25404501e00300c601d0a4840d0000943c0320300074282c13411641019200c480c155642800000f10190014503e00c24040140103850702041d00000754001f85100d905c04500417807000c054664050013941c417801d0042c008208684030242d1000c0d260f0707000100182a0380e1243c5440c98410300c40141036000003031804011441941d490800913059000d43e416800c1180b000e500c50004030340c21050f224100901e82e202c0000305d01885000801c01c1c0070001c00030010616000642e0001d08001e0365148095000c40e00480c040c081024907100302c0b6005002401c08008452038902030228086800303802401c03a40d9a01c0001780b86456802e606540ca203050788260014221109510008000c1554166258480c007072860b4034550052264400781c40e1072200da80d08103 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 883520737 1250 883519487 883519517
    0x90f03050607141e040f08030c1e030d090f0614162f030a020601080610180902220f0203060f10090305060c04051e010801360507170601 60
    0x411036050030701d07003c0402042503c03100e000c6140c80108540240307000aa85038a440d01c0b600c010011900407034116002004400320301d00700010b5075220044042c0324031b00d101e40c011103001d00b0741c09800c0300800000d081c51034100030080030084203101c8030b00c541e5042003441840d008644880c2c80482d001030f240e07440124034801040c0034a1442420b8080b10511560004144000c0e00200000d0a00c0714007540c00800d80e5011203070144056030141084c4002000c861820080ea00300a002c140300700d24108100c0900d02d42c4000d800d40055140c550050300268640d480620340c010181300300c050040071541380c4007040403055024001c45c0d01802c0c1c020300170030305006180104a801c110300302c03007074090010040c00040080d0041c85241e1280f401c422440e9140c40c179000a10000c40711407022082060700b44001040320b6a0048119030540b205081000807800388903d1103031040d00c2c05403160101c1d09403061380105480c2c4c9900414820005550b03040550400d11903180321851054030100c3c04980001c00c0d0860f1 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 883521987 1250 883520737 883520747
    0x30705060705031e0709061215090c020607030b0306010e07110601080d18050f090c0d0f0209040b1210180203100e070e150d03120e06040c0b0408030405090703110406050307090f03050607 82
    0x15230946071800181140c000402e008400c1450b0f002080547d2114060b140f859018050b8a40c490340d00d08003488203003141c000203070300d5010500500c0060602a00820051885104e00b00845c4034510219116035031030b2a6043d548040d00110705002a01404500a2025041a8000456102402000780529a0b40401c0b861001c002d01045840c00c06101090070104140201c00942120b0a40166101d140b4014001a81c40c00030302c450084010a4901944c02c2000602d140d110b66034000020300d08100c9040d1240074031021030081d6241c800d40418442d65170f03443d4400311042e9401001c0710940382c0d44030f40c8900000340c11200c4054045401c5000c49560410f048841c0343c2d20700c00d150003000c1c0c60300d21b1400400c60b0410260b00c0000e611034400c200400440283c2c10340549030901c1c0c000c3c1001c2c6031141e0240d0380d10550180c28000c05142011034000303802504994100500c2827980350710f0340e4842000a00ca9041107427150000781d0b0035240040c492441c601047c0603260060040c0141d50340f8840c05580d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 883523237 1250 883521987 883522007
    0xc06070f05011830121d030f03010f0603050709030b0406140a020712210b030a0507060807030f0b090f06010905060a09060e03011b0c05030705060705031e070906 71
    0x25142d501d8000e026804101d603808500010301c258906003001208a01344018050300301010b00e050b00d2098000c0030f0080d0000c5643c100041022030220f14038408691500c405a085022007150b071101041014000441030f000e54142e0f003004848005861303880c002102a00e100381c1b050b1000c03c202020034004201c81010700c0d0b0f071050090602048825100c1c1d18039140580844554502d030303601250310030400100000315002c0c1d52407807520044d89034100b5508200d01f19400c04c10301c900b95840024941580b801d000348485960043d0684211590700d050140c042074003101c0107400a0325240ca200100d005c18490303101c16442c003405080d0240c2d2003414100c201c4da80074102a050181514000600307980e0346004140c00d174000d075a5601c090749029005800d1218101030540b03e40d05068640000d1074001c1e000304010300c0b2a18264820b03c406017007040c00c5101e040c43c040e01c1030050008204060740c1081c015801042a03c0801c5500f01003900d002d141d2003420f981880000f035802e041017100f6803181890708 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 883524487 1250 883523237 883523243
    0xb13050d0e0f04090b04330b01170606091306230907050a2c0d11011205090a020d02061324020a15111215040e070b0306010305070903050a030905090106020c06070f 72
    0xc0282d801042c11f681d0020040407448400c0d440d94215505568004000792002020b28159011824000b00081c5240200590709025031492002242c01c600b103900528010062558100441041c8010140c03c1012000c20b20380942c004501140780284110211000c1031110f41d240003090300307031900500c9040c84110000c0e17162420000c1840c001e80d42c24400e140200e1042221011000b8800000350500112017003200f20f83d4a05001c00070b10880110300324400e50b5048800b0000100e0500c0024442e009280c80ba0071a80c12a900114502c29012a040395041425140d0041589207840c00c80e0b41d111101801080b10745100e13008548114980c0050111040010505003042c0014052000110040792a80c90001080d0324860240c1010b220350b2001c4940e42014010180c1044a03240d06840301828130383c109030380c503000a80c01d68810321850010b5584241035456034541d50400801144181c0640c500c034094800000642c0b600010300e100b00d800003d0a03a0b400c003001d5803a507032031000b0310382e0040d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 883525737 1250 883524487 883524533
    0x303040b060d0b070c05010b0f1e2b021e060a030c09090e06060907090f031205190503040b150312030a02040815220c030b13050d0e0f04090b04 63
    0x7440012001801c8612902c070755034800f0303034401707650414a0a43c1c081c604000c0c0160704200100030561075083c0700c010718505a086c90a5448094008541480900c6420002c0c00f981800c01c402903101c884800341c0c41c030b802250f088400b10b07803281d000f030f0101d10309101841d80800c0c00c016501d09540a41c102c050a4134080c1081039000e9a102121020b82d40d554148001710703002102001070311315107c0f016580100651400098180c20968010f0b05544280000341440c01c000702950400c601c00e404503107814062000059481283c103c014003a038101b07035000c03610039052000240c0f11101e0100341c2140c140005008000310700d10900d0f170103016800980070002d0141c00f0400400c00a0b000c2001711220764644502c0c103454074100d14448030036034603000d8010780801400408000b00782c0b13403030101007580d400021034a030300e44400e50b040f150300252120091280c025941c214521503040b24008a44003010380308031219600f20000c000c2141d0041000600c4083c4817008100071a150075900c0214070010955 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 883526987 1250 883525737 883525759
    0x3010509041406090a0615050303030c0c0c0a062f03160609061d06090109080a032708041e030b04170c010603111806010e0f04060302130f0e030301080303040b06 71
    0x111410f00d84120b074404042c1d0720104032a0100202c1c1d01c1012249455040c03c0400f40d41400c00180d01d82c4000341c0f051004007400300d01c5080c10031050101c444040d1004028031384240e980c000c0600b10754650410500249660709014510b4034400241142d100001800b440c82c101004940d001e0400d82c482c0c0c03d440c416a219805e000160591003003811045081401c99941100354907900e00d4040d000b4000b10f000c1c0d0401c140d03400041c200a0035298502d40c00d050108510b610b001c004044003901750700407075991031020340c1c82007071200c400007d005661a02c0642c8aa8045642002080c840c051000420502d0504002800316041c1010f118801110601c254036003440d400c2c0c000d007074550640083d103251101880320000c0c0e19005000ba0710040300d110180c03240d85805400038002c8100c180c80e0302e0064041100c00c05c0c1503036840c2d000f00043c40c2e004282e0461a00c0009581000f4100b101140780c8052804102002900c000415203048070b010100962440d6120341e142c40c0f00b00ca000e02425007107051249 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 883528237 1250 883526987 883527023
    0x3060d032a050f0601122111010213060906020106050105091003060b04230a03020f0907053105031203041113020d020a0f0905012727050a110301050904 67
    0x10040c0d4006000b50001c1045200b0301004a081100607440f240e2191103265000f0000b07155000002510b210140380ca507528080c000342980c40305641001034207103500c00104907620945040101054440f1039540240154881005908075070903402414042142808100e4081c03400d4500c8002c0d0301c2c42da103000b00c0c03660368411082515820903000404a160000441040c4461004400184072030031658449081e1030358000c5071404c65505600390160042200080503d40130f00111000d500900007500019030f00c200c1c049091501c01e201c0007284d8000100b0000e81480c0000c1c046810704a0912210b203941c565641e0040000c800241c1036800454002c0424030b41d1005201030811102c0001c0c0251340d074400910b00600c281e0250703078030109224071924180002e9030301500c100002c0c22446421060080d5511003003002c060300c1d40c031212141c840848464640041d80038061080701307c1407070030b0019072100c1d500c08040d80c030010080c6121034410301c0104464901048080d40060040c00c4409080318540303 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 883529487 1250 883528237 883528307
    0x10c02010b1917010b032b4b0221180d060906290a0315020c1006061106070305060f0f06070203060403230403080d1517060f010b03060d03 61
    0xc4100c5441d40c0035400c0c070104030341c60000c1e0f0300d0804413031b1038083c01403c607a9a20495084410310a06401800d501c88c4400d4203900072403003000085004103140b81c60407103040c0256103a50764540c0040c0c0180100b5200144014241601c40720300070b840100c00140c4042c01440314a24070075400b51103440e1540c0103a004250903100e4a041d0510b204081d40041e0244444801d102c001c00e000c0d240501496a010001b080032000c8001c000158100c000da0380f84880c0101d80e10f095030314070101d8141c5152000010700750303400421000300e50001c50103690301903541d65010340031102d0403220a03800984901e00a5a81c6c546100000c51102d00101002e0402c0700d0b03900407900e01307502200c08030f0204441c6490010014114800d6642420020b8006880c203400d50b503030f100150040c02e4048004d583c0381c0c1484084078190845010203071144001d1a00d1000720300001d40c1d039400c0c0684030714900784940400450720303031001d40031a8402e0743c024001034580c001580c0c0c11560248004652000c02c2030340062108000034070 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 883530737 1250 883529487 883529503
    0x1c090f0803070504051018031707080408070806060a120809010311120411061305060f0f030c0d06060806061b030418091101080403140306041d010c02010b1917010b03 73
    0x30350b2043e44032810305c8103101e41010807084440522070000c81c03d4518200740ea41c00c4e42900d51200ca82c0c8403001c1d05801702c074010f000d840d00c000c007188000301e07000c01c20a00014614048031a00d108580386501e8003c28403403007800c1805003041100c42c07005000003150820004210302c12062400080005c1404484512500301604001846118201f44010700c00c540702169081171040358000d02e440083c84410055242c28072441d0701400e0301046400d5079120450640303110f0742c2105010ba07502d141403101504503900c400c1a800b045440d01002191461240d41c1c074522a442c054211458031141c0c0082021041614200d04028802004003081010001804e4220601c610700c021074218038528040901100e4140000d040155420030800801e41c0118074440c64000420300d25620780302c1c0004a40a4501ca000f8104a444005c441448441c2c05520203003040140d54000c000d6036401c2410440140c4001034107843e11a20300e00140002c49141c005507101d02c42182c0001108801302d00464142029 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 883531987 1250 883530737 883530751
    0xc12020d090b0a170a090c150809030a05030c07020f0411210c0406050f0c07061d03070b0306011d0a030516090905031803210406030b061c090f0803 65
    0x41540c00c80e909682244a14000d0020b441e40340303003804404440140540c0444841c005002d1414000c1500000141e105100d13085c0c200000042a646a07650700210a00c0140c09000082692000560030400402665030320416079550754510340340c40300c0c00c96543c1c01c83c00c82070764802000e40000e101c581d201e100703c0b402c40b046240c1b003030746580501c1c3c0302c84a42d10303001c071000321007180342c008021929807035504690680b0301c1c0f82170460300d50100182c41111402031443d42c4110b40310f000c1e0701043d99500110803100e195004a00c8000c13200741c3c082490380b12801885000c80001c03050004c80c1d20342d805000302c02900200c0c00c1985100300700c0140000c51032121644207a4250300804071a2a0301c034500700501d005444075030002e10000342103a40e01583c82c811020010250300b03030a032100110340e03003c0c040c0e00b40422103e80342200c200c0c141d0f200031100741d0003031241e207021910788108101c007410f04100382d8410b401e00e081040c90036130602c0c0c281006401840c0c01101c2c0041c41d561004001041d0001440c01000 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 883533237 1250 883531987 883531993
    0x5150d0e060f01050f0d0f03271e051e06180307140108131703041110030b010e030a170a0c0503030906010f0e090d3e010f110a030c0c1202 61
    0x45080d040c07052030b200170741c852400f40340c10b5218203011456034540c052099903d40b40c84007180d802c0f58911005074410a00c8000c0d80314116000242c40c174008040d4a000080801070500c80541c0c45081107e00f02c0c4881c0300040301716244446444600c1c00101510080c61018180c4044982d410700282c18010541c2040489121030101c800b60341d68040082c81e03105401c0040312161070311a40740c00c6605c081c88950b100300d0b400c0000000d010441c1070450701d9100007024043d03503079a00034a900a000b07800703021480b80c0016102d2921044030314000030008100c640194160100c403034180b0b039001e4103034411800001400b881008000000d441007008600c641d4090340601099418200901d050074203592001000310320400500003003100c00700320882c03014078a040100c451002c4e1000901c1554004441622911409600e6050411005101400302c88200c000f0002c1c14180d25400c011118004400314800c01c05114007001c0d54041e91052841c40d96904280e00018056a075201d00c0740b20441110300160 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 883534487 1250 883533237 883533239
    0x120d05040b01080705090a0c02010b090f04020114041a0d0605031617071503020a0905031905121602120106091b0206090d1d12030a02011d0705150d0e060f01 69
    0x102402000724054020701e00a040320328a4403000616140029040c50f41d840d98650041241c1c038000d40c4480061040544078020601d442e0f0f801289600f011281a0b000c6110305513a0006000741104071800c0e22814510303002886864202c1d40c941350090300d20000c0c0b156403034a001c100c076503081184c1c00302214496440c400321410300f005c61100301218410050250b120f040180080ca141840d40510030a4278a001600c44c9a0300c1030032640c101303250703100c6901800b0b0a56000e10100b440d15410542501490440b4074102c26161401600c0c81a11030b10449030700080c80810061520710002d440d003d14050002c41d8654a40c0c555038110760a00d207a00500910029052210300e405000d05a8060104000707007c0a80c0404809000c600070300c004140c1201c243c0c601c8a940341d072070000100310580b0103c21640c5030341d80c0c4c001c0640203096204004030b068401510b0814050750004442b81542c4d8060210008d155005038084c2494020f030015064240d121172240002075001c001d00e45c8180d2541c91080215 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 883535737 1250 883534487 883534493
    0x21e01021c20040305060f0a09200406080a0809120708010e0a2d08090a0b0711210d0f0311070506042d020907050702030304030f02090a0519090302120d0504 69
    0x1c1d0240400044801000f804104042030700403c00755444440a0080c0c070940d690b00d941800100344121005000c90b000c241d81cac060304440a10f2a000c01002910700300111601d80c0d42060740c9181c2c90500500240b810803103890681404094410701a00e944225443c040e280d030882d030b095035108260204140c2c010790940d0107228580c185001c1181c1b4a000003000c03c05424109181100d1000d07001e45202d40c0000d1501040e21155551002015001c4415840b044507241441107102d445144070300c6800c4d1400c1c50154084084400c3c00d4605c40d66004141c4003040c00740544949640380c00f55414555a68510305030204103038010140c843c400c40140a01d45020300d00054010700418286c8481c0c69000b00220000340c00403a0142c104d501240c91801c0741d595140704413050b110f41d45000790580808680001004119040041914422204400365540342e04482e402c49408603004120406004565a00504a0703404000003a0207481941c0c1808140803007003030a40e0100422075401a9210200428 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 883536987 1250 883535737 883535771
    0x180b060103061d060d05031606060503010b031516031506110106152007050a0b0d050606070807020f031e030a1101090b1b12040b010302091501021e01021c 68
    0x94401c00c0215094540c00c6500341c600c0f910001c02c0940115401140801400010000e075504e01d00304000e048034076181482c0c004041c02051217824029070810901d00d00525000c543c0009041c240f1102da0310707559600b503540c1d6106a03200b41200c2456070f42c09224108141c1c2c204910003410540d20350340c8144002034201c0b030031100a0f0303114405008001c052042000d9122414061095000c00302c0c024544040c11a581040e44c10740c821544611403010010b00b03c0d240101800c03d1000e001c104001c01d55461003440103a06c01c40000526240d41004018014a0071003001000300c6005401c4400c00d000e491030030103800c40100041c411310740c400b184d0500c0c0e02d82d02800130012400118000e00c00a903e17655403480001000e4682c24034050038003900400f2045000035600b030b120f8000304031800d41c1082e0601841e51002808240e0280c138107100090244a20a01098461581a80100101841100080b1114140440c00c44195400b0801c01c1d03402c40c400e0300c4410082c14042c2c400500c034624a95a492 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 883538237 1250 883536987 883536989
    0x51c0207120e0a0e130303110a031b020606010c0605090309040c020105012606151c060204060e270a090203100c1e050a0507060603020607030e0112090503040306020706180b06010306 80
    0x32040c081e088003131080c940040c0b84c00d40c0201a0700031180c104041490140c2c0582405940381c040264042050f00b82154190000c11401e1038411020701070504101080741c0750b8804441c9070b408074440b04401c200103a0740d0f500050703101204006490504c02c650b4001000c0d01d102070709800041c0c0d1110014008481102801080c0036048144103c60301040050240c4640c2d004204004402140440240d1901d640300515080c030003a128000c2003036240d103402d40c02074000d4010308001804c1c140e12440181030800ca1031058019044689041070725101c007150000d2001070000d00079036112107400006031800c01208503c80d14009011a4424039050000d01d00b40780c0c07068034201c040c2103455021404d50080c0c2100c10010044c64059950019800c00742c01030b02090784029004000003070b904003495408480d140e42c0b40b000366606290386011004080540b15148400b910725041084100b000840350390050040610501010621880500e0012101d652600040d80c40e6051071040010540e41481003c1c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 883539487 1250 883538237 883538239
    0x1f03050d03052202010c020f0a0f0303020f0c0406061710350606090f070e10050a031b05040e0a0b0d0c03050111030f280204170709050601050a051c0207120e 69
    0x100004513070300003d00540c44c0c1c0001902803c28150889407070b8075200d2071035001c1c0081030350004000340e43c0d280095683d003800c007034000f00e406860b03a48032643c5860b000b40401c5500d2035941f42c040c00000845156030301c00240174034081942d8500300013815160031148008801d40c100d45485028020512620b0740c01c03c0352240e13016904040c042003015501c480d2095005103012101d154aa901c500c0c09990b0800a41031983e480b0078404a422001684a002000081100d40c0c003440a02d03071b503041040241680c1409000810701c01e00007409082c042c43c50890b1b01c00c4031058040789511004000c111842c44046068600440b007280501c02c2c09005d009403203110031803150143c618900001140d201c010003500f6601992042000d01c0900d012114203202002c103011000c41d52180d5804120020200708072050000d405900000914002d2a2244034403440b03040c2c480d01e29040100808640da540011421001000b101c0e4040f4584403651000c0c00391980301d42d415010701d0000110103444103601d00d62403 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 883540737 1250 883539487 883539541
    0x30b15040c0e1503061f11010f1a0118091a06120108060c03010312050a11011a100315060e060d05090309010311130303030203090a1406010611070803031f03050d0305 73
    0x1010f070540350300c41c45c903031141c104001c054140d00406c0d504480e00704a07040080313010b41c203110720000480050380c0482d900920302c443d00e00800103500b00541d954003d80040c102800d040c010100074441064018a4850f5003491310f18081d03162071030025400303403c84800c003c079100f190341c010701201c1070800409801c1842520460b08661460ba10303903002e680b110442170200540804c07000310050084140300c0040000c94001e119140000079031646009881200c2881690044e10304c0d02c4650080c46109007001000c1031040c103103403d0042c107940c5078120040313a5400640811000101254502c11a400707656100c0c040c55035102c00400060548152280541406604002818000c1c0350b0600a004403030b030504000d600c9a4404807440e00300241500f01616102440104504c0e03103d0200d9040c2c140c400a4441120b414284100030303030758080e90700900200e0784c0104003044041080d50000300808071070248200c041500e031b543d80390070300040700340d208042620355060040b89240e103501455000006552 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 883541987 1250 883540737 883540741
    0x30c05010206010b0d02090d0218150f21030415050a1d0f04150801020705010207021305012102240702102c0d08030106170a0c09030b15040c0e1503 65
    0x104e641548654220a151180d0005000050740c5410036615010754004044508040c403120144490381c03400c5507028551180525008200c4c03404007185110324001030310184c0d00903070301c244003001ca0105102c0d0802da0b10050200144000e404140e030060f9015a07a206622115040c0d0068018040030300c4045118589071409001925010845803c10030222004a0801410781042c0140b07180c40d040780c0501e5000041480034894150000c02c0118400d44c0c104108072098074242003104c0d000e000f8041c442419241d0f11506c4840403035000d4245000034400412100100d40e0b54903101c444113400484100089035020540c80d00c0840354880c44040e06101000c0303214640c800080ba035451075021651079030410358400b1b981341d0000e0f02e0304080d44002c40c6940da585910001c0c00d240c3c0c003840d02c010f010482c140005e85031340c2d8a00620b105402d4a0325440040c0f4290b0b503990070783c2c1c2c80041020194070b040400c0d440459849000c0c07050b1a4080762103900c0ca55031140244a04c000e040401d0421350001081 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 883543237 1250 883541987 883541999
    0x3100b0c0313050f131e020c03040303080a06030506042a030309150908070504020a1b051e03090a050603130204050c2208190f0602030109053408090c03030301080601030c0501020601 80
    0x400980c45d1090080014100e0034030b2449040308484080f84240580301040c0840c003640000000c00581c1d000e5102c0d4a256130341c504421003550100c2c04010000d4100f080403030000351904560900c6e050100c10403209040056000c0400003805a100b42c00042000400300451047c1c240c1001503004070340782c0380d00e40d00c0c14880703501ea42d5580361254030301681e40010b071001614495418401c51100c0200029000c0186040c06c1d66100c00080306060588103000c0640350412000080710900c140150035540c24a01e082c080003d203410080601c010308031048401001a0f0b0f0b079103c1c1c1c40c0b0601e0300c3e140b040c0c0c0742c009240c0300003180c0815117200e0101c2c2483e03007001d102050000600001104540c0102c451070050f40c44c0c103442c5401d284400030030503400400041a40402e54020314840e0144000d4101c4003c01c000000003290301041e41c3c034452481802102c002c0c0c0c0d21a0004a510070180400c60300b00c02c6481c4c0c0403901d950310991105841c1d03009000144204614082c000d80103000920051485506180e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 883544487 1250 883543237 883543249
    0x115080115020f0a06060501030501051e01350103060b062d0705030d0905010f0204260705060c0c122805070e09010209090f010f03020603100b0c0313050f 68
    0x2000c0c950301d01220312016403901e0310030011101c0340005102990b202282c40c0c54601c3c05440300e40a840e010904140021074141010310704004942e042403400180214032f400191900846440c0f00d0520040c0c0c4083c404070003580300c2800018034828034009001e5851030a014080b10320542d15203204000400190701858a0080c00380701d140d152030022498100c0c2524505084d01c10351340c008080e400040365070044198203038012000755021f131009011000c5503a40905c02c0384114040e010841442c1c90309041705540c40b51402203019042011178000300d0301d9000040c2e09070010381c040701c85540700112049443c102900a40c0c100601c9030000c026090340d1325502580e000382c40190510811800d400c01003480001c10055008020b44480139202d802d00b0320b00b0714040c3d403068105034082d07603c60000c03503d000d513001e41040c104c40a4001c02c0d05094219401c1001ca03610203020790300c1090a415000ca02c14a581009004410102c0c000b140e5500c8505908007070340009500591144403100f8410900362180 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 883545737 1250 883544487 883544489
    0x8040e09011d121c05010f06090609061b03020708060a1a03060112020d0c030b0f0a2d091a130203061b030612190c09060519060c02011b0b060901150801 67
    0x41c01d52207071961440001c5250340d1094090844e100c0c0c4c00c1100003e005c0c1454046041611000da88101e4540e460318001e03945500c0718800d11000851943c10041c000c1c5000600840301807180c81600c00c4282c0c5d49000500c2d041050300c005082903a2003180c0307a80d180c01ca4007c480c0c00c64003030b00682980c0d0b02d0503440c1c9040d8628540d010380103074400007020303081105248101010359480405407a060500c0c03118510050412035040300e425181c094503164920390001458140038800014044219044803060081c2150310401c80786251003e08111604003440406c80c415003001552003811002d40c0105807426a01034010394600500e03450001e40c0790b208000300e9a000e0390a80303d2002000d00035481e98902540a5095095a40750503240d0040203031407980c20044a07441d0a090201c50313241c60400821403641641d003000101c0d60a0100a001e0048a60484c804e0050500d82c003120207402c407010324110060400c513020b1440e141008060310381001000c0c090001c0444900c1400c0074910050106581 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 883546987 1250 883545737 883545763
    0x1091e09020604142209060b011b0201200609011a0a080705040b0a0801050f0f0106090608062404090204150503040822050d21020610140d08040e09011d 67
    0x144c05039203000354580410f8a0301103031030003804c540708401004442d401420040b208450701d604010904403250f2040c0d00c00c1c5407600e40c100c0c0e5000c1d1080d196005540c00300b40c4900d2000e600189402200a041043c401c5510540d1440e00204e0301c407050a104030810904000218420344007480c00384150a000640c80003500d801390340001d03014142000081d0344a1080d80001e0b440d60900c401c01040d0100d5200290141a240900e03562030790701c03900199400030f060300510001410f400d00040040c070f441d241d07204030000140c1c04000f041c03140b00109101c40e0700c076070400a00035400207020414607a56044141441c2a507203012815400d1980d11039682d881000007941e074010450a038101b2000801602c0001404014086200404180380c05002c03589014040413443c0355042500030454008a0000e1144038203854950340541000407400e8500704441c00160400c01200001000414090050015002c82c0e011034000d460600d00340380c2540c0825100c180c0c41a00d0001d601031032403000509400e1955 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 883548237 1250 883546987 883547009
    0x40603020a0e0a06030b0108010e0c070f060204050a030804080d02030301050f010c03021f200a08060112090506130b13020a122d020901060314060906120601091e09020604 75
    0x51000e604842d201400341901c2d50011482c0c00014469070180d10240030140300b0388549003a40e07681c1400d02e8004508840c4c01c00300540c20011323400081c1740142e4080f0642d00c2850014181501c40d0080760031003013560012910b6040004007846001400c00001d81c0113aa00e10040d0300e1036041501184081d148840c04038140a24198100304140c001d2011201418402698200200b4065802d1019001c0c01804081c00c0294a80720001c58200c0c03401c503007441c0c1c51510768960a07180d0034011907100320155101d69805a5800c05040043d0040c081c3c3c1d40140d02c141c101d107000800030f0030a00324070440038140040702c034001382d08003005849003154a001c451001440300e0b10400d10b81050300c21078002020203200d00789101c410613001c50318110303180d600c81c1c002d40300001c2a070b89880080d82201c400a03d46405d60000100040043ca800c01d400360f48107601404240c0d1142c400076000b480c220302a04480c082d26100c05c6040c00d0310203410324138072803030700810000e20210006802041903803140740140300e1505c1d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 883549487 1250 883548237 883548247
    0xb010323280807060c03020d0e03040b04050d0f05030a0f030f0902030a060203072307030f0207140f041b0f080c1227150106020d0507021c0201020c06041d1006020304060302 76
    0x1012050a603070509410040500580c005188024000d5028a00024101e490048003c9c00741d4000400d490541d41c518117102c0c038203400c1c1401c000a012030001c084540c00400744050b03000840c06e00282c040344a00351203062800d9140400a020faa56106410180750702e0049181c016a030300043d080300c026001500141c0d130740c4070f032401201d1a9854000800303403400212800404045a44014006103001e0b58440808410400c004ca88644030340c0701d00101d80001a0035403c551400407404c40c070510008200042060f90752411140400c800e414150101d000d60000e4001c207500003880c203600c003800c001141d140007601064082a0203003e031640d0204200f40344444200704c1861820611444120126018060f448a018084074003d00a00d401402000d0f000e43d034050082d4284c400583d4002d28100850080c000e560240400c40e01040c1c0c1117100320601c601483c0c54560040025151440701a01c2d0070815450312110003901400b182184d6003405400c010095001c401d80e019101c40346000b696074 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 883550737 1250 883549487 883549493
    0x7050a270308071a06060a0e04020712080603010b1c1b1716050306070c120e1e0a14030d080c0403150f050703060e0619030b01032328 59
    0xe010a12504440c00c012041c4103100000d407600921030480b588030714101c9003803080341c1c4006583d0560005024000e0f032010728050000c412134064003910050a20390035490f8200d9011344800c25601098501080c03060504080c012400d0045041d074200c1054103410806210111002c24041c01d08045400c0c1d1240d0240301c101038000401180e2500d484802c0d0b54040c49403503001c50440d107035440b00c08010000d45402c1c04100b0300e1295905854281c00d155990b20360001c6640382c211864200440c414120011b942d83c0001c8081d10300510804003584c18041041c0258901796030000712880c090191a0565a03600041000c06000b99143c0000aa00e40445c00101c0d40950703000100401200c4503415110002d6902098003159821014070094075941401c1d421503085001d03a10040c041d80001411605040745c02440039418130810002d41542c9446961542c4402e8204031601000801030181001680248a5405e240c90380948504040c03c8403113048005074100a20080f40b0404c0200f0078 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 883551987 1250 883550737 883550777
    0xc0b0c0f07050f0f071502070905040302011d0709111e1c05130c0537050411030114010813030c1707051516090512030c0a03051e0307050a 61
    0x94580d02404441104100701c078115201c2c800d884d0465102d01c102034000810010240314074800300ca083d00500b0500381004281d0018100092083e03080d0343d00c030420031a00c01c2000c0400c2482c606500003030301d07086080c03900310341c29900e01c1e840744050342c18203000f03051b104404c45d09108621040c11441c55540e0302030b10740c11514890303c0744400384683d160400f041210018200e100d00f40d00d01c50799800c480151210200841042049030300003d642c8a407817080e9002242c4000500c050b0400015032080c1591100050140c40c244011031104800c04401000010131410056003400c0090900e100a80b42c01d25290f980e1160311301d0042d041080c0c1c40c14103420300c0340d40b139001d00b01c0441304030ba207503610007240c100700395100400d803c4030003840016000584c0e101c40703400e201d1f00c241c8000c4e650400030f01d152a0802044038102c1580c508240004c016268540004116511070203209071502d81e1a510020200d881d001c2c44401c10700f0300c400c002c0041054440e07010b0201c50200c92507040070360480d1038820031005 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 883553237 1250 883551987 883551997
    0x100504060e0d021206040f05061602060f0a1b0c060b0d021f030207021e030705031903030e03040b030f0f012403150308030c0408060a1503031101020c030a030e0c010c0b0c0f 76
    0x31203010300011b00c010321005056140d40c89000c0c0044074015240c1c1c08254821907607036240301e00160800408074100703041c00342c40103810284c00c4401084e04075228003c20820100c0c1a404008181311401071010404503000c0d17000000381c2243d10100b0b055140d008070780141442d0700341c0140d404030180b510714018040d074185d629040d005030540e0300307034010308034805485c7c043c0780c4009100c1c1c81684400210751500160005040450024091000f2046d0703a0070380141100c080916010301081c400800d400168401440c0f04c1c034000303002008039061406080c032148206820051050f000b081c03080d80714400420040744060701c9031900040a0a1a010448403007505820040c0012400428080701051100160054940c0c040c00c7c0c4216807038020410040b14002078840345190751110b01000440d00804c0b0720440210340310005481c029800b401c003421f5601c1010880c1c04240d0321036140068100800010301300071001e00381b500c0303d400c0a886409c0c0c0e0b0b80c8020070300445020001750010304501c643c0e09580c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 883554487 1250 883553237 883553269
    0x14100b0301201c060909030e03010618020c031c20030f0705030901091505010f17070510112b0305091f09050102070c0e060d0b0112141506100504060e0d02 68
    0x1007801c0c5c9590f0380c0d0015003080041500080c880700300a4445280602c1500c08550207140400f400c0801c00903154040e407c10160350600f40000c2c81103981021034051480320304885c0b610000b401050f0000d980c6c3c421101e15203039036048201482004184101c101d0b0858003e0301905010340c99a541c10a40c5001d403014030070041c03683e01034502c107200d40079454010034143c600315481e4901d056100c400c010801162120010038a50245504000303a080900341c00c282040140b400b2020440303000342892030512550003a2201700074800902110f81e068125083c0350300c40c61320b004d00a504051119954603001d031400040002060b4410041c02c0710154030140c40349600c03100954450607141030100c02c1510500c1003a01608a6100080191800401c4010708a0f400041c1802c00d0b4245918803800143e905003c403403d01021000d014610f0301007116021040080e181d00c4500c3c0b03810814081e5084e40b8400c4401440f83c14081448400e42007003410941c4482501c0d10b625101050000400c030b154103030003030 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 883555737 1250 883554487 883554491
    0xe3718051006090b0d08040509060105070b15030106140d0b0601090f0e0f010603020a081308131214190f061508100b0102070509180a14100b0301201c 66
    0x39803070209908402c046503071115082080740344a60074444441c0c035000006141c1d0004000900c0140b60294050f504070030185804c604190960307880315401c02d4282d0f0200c040019001d200a0700380744c00d014140c02340c100e581d540c000c002c5001000c588441e212002c001e21002d440000544140d104010840041816510411009030764404180b0300105c180c581c2070300300c4d01c002d00101b0600d00074000c0300c40302c0720b00c2da580f03c85680d5100088a02442800d008842c0b015040101a034143d1005210790007a217281403907103405808925202c032360040f940100c959550007016001508501e2040d01154603034001507400108061458440300410f0701b201200030195480780c0109140700c00040b42408011400c1042111000c484011b982d965001e1283c0e03640443c845c0d0000f16404d18169003403000c0f80a42045408550040d0785000c680032100b40700c0e018079407007105400001c0311031b401001130040d0148e00070090700550240004909622110000140c0d000050040c07c3c19001c00090011184840c02 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 883556987 1250 883555737 883555753
    0xb0603010e0d0e0301140f0c0a0c0f141005062d10210926070b040b0a06051e0d02060d05010f0609061107150311040e371805 55
    0x2024140104183d803103802507280121040c1c41102448840d4000c6840404021041d039640c201d101c2075511400300340040140e245400301c00101a9001c10940380d20030141c00784258451003400d480d20244c02e070b400004c1070902c000c1c0305150701c0b04601c40d84d842280581c1000102d5484601c0d11001022a21030382e00807001c03c20010865a01607404586030020300480149180c142c01454152213010700007a250740301c4030101c40b44581d81c0c0300b4414110300d6081c1580d030500d4444d032991445020102c41c141c4030b050f41f000030400100e07107500c282170162408a0b024007074a441030313040a94410454072401c0c0101c0c5065034920a5540e403406407089105029004d00c01036841d80b1090040da00284910b0010840182d00802da40c0d0040c1488091107800300c00500d510f5140400c0900002148040901415600c1c89113000c10360880d001440503000780704050b2240c0c288039134059040e08820307400c1b504d0440801c4d41c062001c1c01030440300c1c00c030100502d00032840c50030b104c4041343d2482c0a840c0c001d019100d400a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 883558237 1250 883556987 883557013
    0x1110f0903010e160e07090b070b0108120408100c110706020a0605070503060d022214011e0315020306041506030c0e01020d050a0c111005190c0206070b0603010e 71
    0x4018014108181d0080c00030242420324030b6641d0b20807644030f1807004000074007400050080342019070f00909500e0608801036880200d030f545503105c3c080035140d13400c45c0c0f00180040001042007460400e003140d0302c245424945030301e2545824440a1804449403076007000c80200e44180b4030040c1e00000441910748007035451a0295650750500d600726003040c1060001a41e95000798181c0388070b0840500700718000d010340d60070012103600a00b1843d1940c1542c0c1c9081561a80b103101c0d9040089050b11490895414140c42c0414462024440080c080c4244018000102c18405605508513440c00142c0c0f81c0c1c8030b4400080144c00c4900c0410b80c000300480c00051070581c5504481d4240750740c0d0f101c00c100841c0c7c5200490312040c08400c0980030800c100302c1030000380d208140c444001406140c803042c28503010340c0056008140310b4411000138202081c1110304420115010031840c1550030281c10310225030f804903034203004c0c84001410782e072041400078550392000e400030780c1180c0b54001580d01c9401c0c261 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 883559487 1250 883558237 883558267
    0xd0209041121040b042405131103010509070b1b0607030b0909010506010f1d030d0f0f0806030601090c0309050706050408070b0301050d06090203150f07030e1f0b01020111 75
    0x3001110b6010052580c100107060750701e08107000d590030950300245540d44e6144c00e5845007110051090070f00c80b031401031503602518400e86000b110030000c10100d0014504001e042610b0400c0554440c2e40340505100d0034110005030300d4102c60020044a4403079124065030041c07122485044038035030080008024000354140d101408604040301d90322416129143c07101c0c01c0320b80861301d140c041603c5007050154140222105000a8043c0b40d00b541402580e0740402e080801090394030000c58007248036a8007250300034401d00c84800d41494803c0c1e0500e08040080c0d0b840b801071290a800a558001d2840803030b02c250803020503e81c2080848808039a1f07000300901c41d030701c61321070b021103401030072800700f1403c030740504813812204000d002d1080310802d51030b0100201070b40d090803a41440380b80c1c584c1c0d80000300200041d104100000301e440080c58103440240980baa03017082c5021f10780241121078a11440c940c0c003500e0503515541c001603555079030070041c0e0042c42040d1154104290210740142c01d00d40780 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 883560737 1250 883559487 883559497
    0x9160609230d0b0a0204180b0102010507020d0813170a08060a080d141b0609060403030c0819090c09060b070501141314150c0d150503120d02090411 65
    0x507107030300e4011103054035201c0300c5911100381c0e40251403801e6030300031031000503603a900901c40d02d50062410f0b5503032448403140c0f0b4400001d0840e090300c52112126540e020320402c1d60101d068005080c0401d040c0d0001131542d40000c0418150203143c680e11003c0c0641255180e00024101082550300c201c60080a04401011611540700c0e0b0340d00f80021901c0000464941b0400c9503545a04800445500214006401c40c0400d5540140b5042e03204100ca01c08000d41c42c0200c0f0600301a01850078503041c024180c480d03078230980303050112a00900c44d04400744152780000004040000a560703296107404245103842d07034044050075040c510003090104424009046543c4610001c221046017a82d0004140c3d40c00c9035040261184c0754141c80c04103603110810301201e408282582c00005070054514203400d42603070007002ca128080b03000100320b40c0c94414a9022121100a010201e15103800241e0f00c50100c4014288942c0104204450307040e143c05641010600900c1440000c3c84403400d10901d4001c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 883561987 1250 883560737 883560749
    0x191203050c0102090405150907180e0901180c0303080c0a080105120f34080a0222062301080c090d050715050325090e13200f011404030b09160609 64
    0x1c0c80032542c41e500540cac4030107020f0308030345080c0212490003030003d21007480141788d402a5501c03150034255005407160441c546e20705c00d102c1005a9819030030014124031004154600c000303000c1228800700c580120910741118030031502c40c0440c08028400e03500700446000f00b84c01f03501c603101c1610941c003001e9040c0e80d20700313030740c03078126500107820804001101185100700c08864200700c00c1e41026050208400b0081103c0c2c0b01d102c1c1c0c5007140c0302070080450701c2c507600011000c00600b108141d00740510070701c00002c0000f441d0200b514282813405070b20611541d040c02c0c1c407400390040c056040041c00d200e83d20041c4018055828441c81034000981603034022565420ba0300d00341115002c1003c50079285103460410f1303595182030340d400c0000703182c903035000645490503102081c00c0c6000080c1c400402e410000307264520801c204200a410b120f804102056000e040c070652544024114601e002503804407034108030b48604645481070701c0c50400308011884034040314240400f040494200e80030070110744d4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 883563237 1250 883561987 883561999
    0x3090b01091e140c09190b040f0602030a0f0806120303090a061503080a031d0d32031518180d0e0d170d06090605191203050c010209040515 61
    0x226202c01001c031900105208141d20046002c900c0100000c03010b40f15a050240440380e05412003440407242c00c286600c0060382440019080c0400048404258000c003141d00046041c034242d0200900102e0405040e4400c00c4200400681d256542162818003900114290b90b940d04190100f180c545601c010150f03851030a281016112114135403005d400c80c0e4000c92203c0c00c06622031021000381003114080d205d8040d614902c0080f030141031042d10968031719500d4010007005d00701c4806004503140e004800c00742c0d002c0c040c00c1c5c0d02c2052040c00c40c1d900c05c6011001e0039050780c60100041a03445250086a040d4640d1001c12034892083c9108134010003150040b51015542d005003103031215154a003491300080c00144020000b021410054040461444090300b8056010448012140300ba8440501207441d007004010354101005815810302590b10010780c000e0070044c1e60003150603c0500282004400034a0008406d420350564049c1d41000b881480b040c10451504c01c00c181800d1030a40c0300340 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 883564487 1250 883563237 883563281
    0xe090703420503060408030709050a1205060a0c02121b010c11120306010c0b0a110307020a14030301080a0215070b04080c370318060203130b270103090b0109 69
    0xa4800200d01c045540c0240204420b5850b90b85602c4642c0015118205101d4100e902040c1b0b941c4180c03455000d410740e1b00004811040380d00b002c42c580900a05168203140c60203802d18249a400700e40910b0022900c65529590341568030380745075050401c1d0075280103500c0c00310000706043d44001800c406a02c01421130307a00c2c003104401601c01e840140c4409000c111201c800c480000d2580c14929840314404c000043d400e4010110351000e54812a042c0c4c0c0180c0080103030004200784004024404440c92005505640c1800300c40c03940c3d0011004040e10400040d8030f80742c907100303581046409043d4482e035551414101032034481617580162040182500803103c5231142c0700c0c8692080b42501550341c0c0c0b00c2a0844001010034818443c5800589c2044505400c98443c88100744c1610001d1060794011980c0b0303808450394442d440705582001020b002d0410503000c0031680041e80c00550403503810303808818081640140d00514071100020401ca0403100000b82c1140d46a0025680c1e44d201c40100d00d00d8 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 883565737 1250 883564487 883564601
    0xb160f0e01171e3d03140f01060f09060801050609061003200a0f140a030506012c01121401030b090307080705010e1c0e090703 56
    0x9415000912400030b08070105000c0326442c101903464001c403c83c50348010b03818600030071624408003255a08030300014040c080e8400c4d100883d03114042c50324041000c00748103520a503015000d003184806000ca07084800700c1001040c0c24446420464a050020410f10b960b4090381480d2518610481c8085407030507400141d040c0341030003154450344009041000c9540d031074003044070b00d0b5540e000e41c10805507600100040c1c40341640180d03c09640e01c00b80c0b90340380d030544980148005200310300c1404020341c084101a40c0c0703070300c0425507500f0398080c02c0c0400e00341c2d0307841c0040300c0e00301d014003c400c3c00000c00049614403444040c015982d10354280c0e260031550304010002c40aa41d005403002c000c00e01700000400c0465414070040e500450740905491524040e40c540179a207821108064907d80d41d1884540c0c0610420440081050344111050500b5241d006015190f20740020400f4003a4201000180c80188298444600c446014182030b14a099800c2c407a41d2042c0404c080c02c00000c1e0a410141d02 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 883566987 1250 883565737 883565747
    0x1050106050a0c39090b060406050a050a020c150309010b0405100905060a2c0906061e030c040c020304060809280c03080d0f1a010f0e0303070b160f 65
    0x2c0403107030740314501a0311907959481c82080038034050f45032108503500040c913460001581e00903061102c5540b0800213017010108000c03180014546ca1282108000c10881260403809a03102503001d81442c544030305c3c401d80103038204010399251a50040f04218100d26000015011354016511072000700050868403090000711003080d1000c103050804040d041100342c40c280c01c0300358030003000760030585401d40d03c0c010b119020305140810401403500c50001c1d40c03500c071050642c41d8491000c2c40107040e54145003002c640b0034059074000c1640d8400c10301e04c0003030300e48081107012910300c3e0150040000c0d240440009460350014000c000000703aa07400400c0c1e003000c0000d101988034102c210b0109185028080141c581601c4840444000c0103000000011030f40c050042e0034007807036454003c907030003001c800602c048030012501032141e83c06152401c801c99a00c0304003103000c0c862600b0b01c14035505503000000e18500030001c0040503c02c41c0c1d4100320040703800d1a2500060b440c03607210110445030280007074034 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 883568237 1250 883566987 883566997
    0x81816090c120b0a2907061b0c0f060c110d02010e2b03020318010608030909070c050c091807091d06150405060a120c0f05030102070b2716080105010605 67
    0x190044540c0c0052000c802d50b05e11020001d00e039040307465408001028242180d4021540a0300d81c02c0c1c1e00c02000ca06000024070501013400546001e402541286d0346031802035606030360107051940d603401c605031024000e290103066880d0280440d942188081402806441203d41042c62402030707188508040b814611322441070b40c0303d60000c8c600e455100004900a4000404c1403034180c55000000800c5102840350002506034040955981d203942c40034044401c5000c1e100c401013000320040c0c0e801141011480e0580302c0000c45000105807164448030754406c0115510030042d02455500041828035544044965680036407000e1450000706401f0b504d4000c2203441c8610b10005803c10311451805520195200703400601480c1100d40b9000100b01c019002001140c3c5c2e000825818084d6001603118000102021030095141080c01c1d60742036800400a015503e01031401000a091244e07100341e00e000ca10007841c122030391f0101032540400c03082558030030303540700b035192800210784203100e401120 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 883569487 1250 883568237 883568239
    0x110702220608031204330204151b0303050a1d03280903170d0518010608010b060d1a0d03020717010212040206030618070509011202030403081816090c120b 68
    0x10850340e17864a540903207511744c0120f0007045003c4026808602c0d5a01c81e45410703000740b048010703140c40c20000403010b000f07038660000003030040c505802c0484141035030364022040c0d410700d03000c14603403201140c100c040d0901c1692014140b040b80002508948000046c1c20050b2904d200400328010807042c00c10101c508805080001d40e094038280085007800011301c016060354000585001030341c03c1c0071421030b8030541c2c980d10400245030f608a4014000d000b071780041c01000c40200025120500040da40344a20800c82d1042600e40c08210b00030f081c03907520301076401805000407070481c2031032074001e4640c0a940107500e92072041c0d54030010142014400d4414008130400d5225003600d6070740800803d40c0004103000d5100c0c140711851581d00241d41c94407070007001c05403140350300ca88082e17001600300c50300d160b4415072503031041c000c00011070741c0075030304540007012204400c2d10b81e034072a40040e0801c404124441d1241e00c1040d0b0004403812942d05c030441c00ca03071030b0755030110400c032403581141520341e000005 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 883570737 1250 883569487 883569517
    0x607150f0c2c0604150e18060909060105061c0204080f0303190623030102130915060302070503030708041e081312021008070507050714210604030311070222060803 72
    0x500c0525030070310a104405e200c84c1018840c0301c449000040d030b10400698800006115031040c4045400d001d040e42d604a81c040000e031446604010208869000f0b0b021700c0c460b00103c61402011101041e0f04482c060a03100054840710f4002500c160358030350084c0d42c02e02400013a00748490b140c541e24400c010613548034001c0031000c903152080007440d281140d4034065065500b00300604511022003000740007003000000c086040d0004400001103041594800d00a2500400141c0005500841201e9200b41c2c0c50511204944807420500ca06140040c6401102c4421660700420b000d02040a08494402c414815003056110701503842001c81c1d981009400410b8454600c0c0150700403400590702442918140d0b04000d100e44039207203130450300d51084440c03003101b418000315030900101100b5111071a460302c1c884111300d24002540c400c4001d03c05001c040e92110b00c002c040c0e0502c0200e44040750006c06280c03403c0c03c0100c404088030280740000001c20b140a01c00500345001105903030900080d5041 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 883571987 1250 883570737 883570739
    0x9120b0106020c09240f0d0606081c08010e09030c070e160e01050a12021303030c1712010b0f070b0a020a020f120a230a020f1005060607150f0c2c0604 66
    0xb217404204161070000d60002c450b8946284c01d8444030002004c0c3c500413040414030310f250030300446c20308646104280740e05038080c84c1c0c1c0b82036a8000060340d044035810105900a5034074031103003904500500380e4507010390084d45c000140c440440c50010b0f0040644028401510310120030035203050b51f0644400f03001c15400e00a103003c0900400010300c0042d2112005032030f04c04111145151280c058204401264540310800141321520f084140c0e01e51079501c820b03191604944c9a000001014400d2002c00000040c00d481444d6000003602c500c41d034402c03a0100c031400c2c6100303194042e41107070500c040184192082a440c00c580040c012804d001e050055034601032070020111760302500a500e0460613074240d60014820302c0b404000300108502507000d01541d034079811006080440b484484902c03240dc1c10709018072a515071080780c10302a0302040400c04070000360044005022101c5540c0d21a51a20b19072081c4a5040f003095440c0d0131508078000d045001501e2601001c0103c602c031150031600c1400 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 883573237 1250 883571987 883572031
    0x506131b0f09020306030f160f09020c0712140a120e0108040818010306050a0b0a0912030e040c020a020a06080a060b19051b100b040501080a0b07050a09120b0106020c09 74
    0x100035508805c024040d83d011422130803c05140c207000700e006400072506070301c08100c1040380501d010041e1083c50019031800380003400f90f81e59041140582d070103e13100c3c0c0400c40200104483d2507410042c2c11415503200308624100b02e085408804008800300b111501c842c0c010f03601c1105d00c01e10456104480c82e0400c008601050381b4090400c3c5d909041c15034968001c00d0341e603510710707104000341540c961007a075980b00800c00a02e8101541d1082842c6824034000c10002500b000d010080440280ea0000d41e0400006040b451319100b0321020307403c000042000316120f503110913810f114130b80612050040381e5560310603000500c10a1819429a1004010019042c0c070400050180c100300d050083c0384000da00e20410b0500c50501501c1404a5465103c42070b2804e043c001d25004107021400707001c21160380e44501610316801450300d07042040002ea9484068050040040601064002c800f00100d080c0340030005040f003070003488054410081920007a10300165501d100340d05a810011402c50080 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 883574487 1250 883573237 883573241
    0x907210c0b070b01210501020c01050601030c0c0809091015090e130b0f0405010207080c0102030a0b1c11032d011a01020a03080705040e0406020d06060509061b07030506131b0f09 78
    0x4100385c0200401103a9400114609001404130038001c03034000600b60138203000140c21281a00d03480f00c28001c04139825004551040c0c10b4688502c41030728102d08940c3d6038941c1551155464200041207001c9040d022800b5500c0405601940c2e055210000b0a807221108982ca074145110000c1c49a0243c0c000100c502d0240341039039070002e02c00c100240c200240c503a03d07528544c00c0907045800720ba6000c0204164000240030342060094142d071941e407484017160503285040f40010025080802c1003001c0401900d040040c0b90300824001114640400070024409188140404c1100f5640c00c200e410b42152001d503000c1d0105510580051100098640d000e842400b0b0051888080c04001d01c070000d040f0300100d02052040d0301c00d210060340c8403484c80d50b0b08204c40658100404000301401b460a5607100c1d2800c5814a134440c1c400035140c01c1020b01c0080c64540b45400c0204a0b00840c01405a025442141441000c0c41402c50030112020b910071048100d88920800c0f20021003841e04000c080565 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 883575737 1250 883574487 883574519
    0x3010606050f0904020f1b0d080a060e130516081b150a0f170c041502060f010b0904090206070f020a0905190c023c010e0705090907210c0b070b01 64
    0x1078002414500414001000e54009101f00c031900d8002d41d2500c40103603401815030794014007080082182c203040c60503940603443c0081c0124000d18040281a0502404116a131401500311b031101e542c440c0ca9888007502c401c0c54421560082400c07003200540d034500103464001c41405454034034103010445200f2600e12040011580a001e100c034009100c242051165034881d020801d6210b07555450411040340c1c4d24048030503d81150070000c00d005200040c09070640c110750071034100c10f44076800040003400a107050701c00258041000540202040f403014603201103180201c1e007020206640e03a0500040c2d9008880c0c00407031180c4d8030440e04c81c2d00e06e41d0344a07103900d06852040310002052600c18105900d0781c102d11119a111031203001d079100c55040400c1d504030200c00c0080c44603a0200f42c102e030b959000707409058800e50040e8005526003604000410003010030702c4c50600030b0b04114030082c4410900340c1c4140c8504007407010209100c8001d00440700c040da401400010385a03c3c10038504903035800 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 883576987 1250 883575737 883575757
    0x5040e0f071103040803120c0a0c081e040906080d181e0503060a0506190302030a0807081603090e0f070e2b03053a0f150902070203010606050f090402 66
    0x100310040c82d90704000f0800780002d403884a00960383c8410508510b40030000091504541160402c00034000940c05007055043e590300507551525405912040780d480f5000d80000300c114280400c000460001a0f0001001c858035030040e60170504009104599003444440416a8010030742c030204a00c810321540d001c0000e940c400300c80c600d213840d80e00181c2008000d40d40c4002c0a510b94040c84100d00d08000d05414a03421502100401d51559010a0300c521494030f000d05102c1e0f0102d60a000e0281e50700850b51b51200e00030720445c1410081c94080c2c05110603010324484417140c1d00010b0086480004018000c1d01d441d290b00c0d042e0200581000070000040105a01c00f041d600041000c001c103c40005041c10310075110305813200701100700f1070740d410035210403000c0480e81c10a00c00c001000c154240c0700210200d1802250103480011900050992070000c60400036180c207001421007582e40c0502010391003100244810360b9103c50444141c000c0340c19000e04203030f0400114401345001c0d8010004202 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 883578237 1250 883576987 883576997
    0x807081c140a020105060a0e13170c01051008121e0a09031b080c0a0b0702100c0f06060608060109060509010e0a0506030f010f170606010e01021507020c010f05040e0f07 74
    0x112601c0c010115400410101e40035070344031001d015803840d00038218005094050040410352030000d59074401e0802c05100506144c03845000d6205513400c50f000c03100c5400300400244940d05000c91000c400c1c0c4201e204245036401f84420010300c04c403003d821510215450513007070b11041c00e00030340402140d000044580c140541d03600004002200d501c150407541008002003d44240b92401c142e00307007045e0308200c0b0321a5100302018040300004506440d041038065900f00c0844019000c2500c120b418032034043c2440ea5080e44040c1000b102d508900c5c291071082d56159803545640006480c509694007480f80896001e021900455202d060390280884c0004d280e5130810346d648010503920750054035101c0c0c02e240c42d0001440071220662402c4010b1402100a54840300107800803525004040d103864100100040d445100e83e108105004018890a90043c8142098a400303507036012100e03082c0b80821038803480000318901a005640c215194001103114680d031b041320103880604001d0200342809 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 883579487 1250 883578237 883578257
    0x9020a0509191103060a0e040c09052701021c0b010906050d020d050c0c010c0207060c0618200a05030d08010306020a0201020f041409220209190c180807081c 69
    0xb106401078141032065040d1181c0d8900b0036805001804106812500341103400009100004100d04004c0c021078482c001c001485403258a080c0540d0440700c402e40300c00c1d550200c00c20070350f444194010500ca4050b10902010783d24082900820340d5a203c0102c1e0110350501070400000c0e014200074501155101c100610300490710844100b124404d0380c0d4901e01081c086120103007508240700d940560042c03400100303509860040001d040c7d0f035201100820103601d810b452070004070903e0404880c640c0c809032404100c0c00305091003040d44d00c40701a81d48100c3c172014001680d130401148080d00310240e503940f00c0d201c4e800c42d200d040180d840103004204542d0300300015080f00d41c1c00805003010340a0403045c0c90341c1c0c0304c041e03081100c864805030801402440900841015141441110321070036410b4401000790742c0c1e1400b6842d0320f446040101a01c82d81041c15200d2690b03448190301c5014a2202c02c0316115030744650400d5039542050080071003070340c0100084280c606210916210b25041458012491 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 883580737 1250 883579487 883579531
    0xb0307200c120c0d03021f0b09040303091716060c0905060f1303020603011d010b16020d062a1e230405060d0c020607021b0d020f041b110109020a0509 66
    0x181c0c403448040d80107070007007062400d600107207c02c40820020001400d00005181d0400658508000380c4014141a9038000f030108009400d02244d4200c1ca1031160143c07621403503010450100e141710001c0361080e24100b00300441d24010303185101542d1000c1c0403a03052102d40060300c03500c0c1e13000d811140030102c101600000160380b41401180a840700008035980007008c6114140540410380116183c000240400680b607414001854420303a0100c9040300d02d0078031810060002c105940310f12aa0408400c4080c865001000380700d03000001e03d9039001d86190070300c0d81890306042941404e000203451100c1e070000801581d404074411040361484a41381c10303611000652aa07014415100c400b588036144101200c3c4c040c400264000194005400610b80b4031004034074548002144d90300c5080880c00740c90954440300810390103942c01600411400e03021b41940400c003480c1c5812100007071400300b0080483c09041c0501075540780d0103810f036150582407800300110704000078248a007032880080c0c00707049 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 883581987 1250 883580737 883580749
    0xb0c0136020a0f260d02030f1c0e1e0a080910051b01060f0b030f0f1012050313050111061603090b0406090b061002060a0b04150b0307200c120c 63
    0x1440d42c54204c21103a416a20600104c007114501c54040b904000d1900d40040e401000b12242003a00e040101d59414070101e410011064406400c41e0161a10385c00706042d03000041c6040a08841850017002c1c4480d061140d5a1900744220040030402c06004008803818000001d50811807281005030034200d003040b803084800f0f03900e54056190ba445000410400c40d84595440c094007040c4412842c61501107543c2c12851400740c0801c21504ad10400242c40c19403075400c03400500401040100c2c3d0050508042e0b540342c0214104010742c032003161000589601808542c15200c40d44c0000d400700d03079225013002900400700303074400b030500d61210040000036440310b404900c12445010005010402070034100c1d50084014440c1d402242e84481012910f50001420b070340c440c40f41030001c00d22076150b20101d0040e000d011036075800d181c1d41d0320000c01c000410b24080c502c1002e1a50350310040c072048a524a00300e0811000e0011305030002c50001550342000e428504071003020340d0072503070307021110001300c5e039 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 883583237 1250 883581987 883581989
    0x60103050c180d061b051206040b06090f12121e04030c061b320d09050d0c12080a1101110306040c09081e060603010603050c09130803010b0c0136020a0f 67
    0x1700150300010b05e20ba5005030001c000d9000380094034208118810b007008503d10344500d440143c4aa0300d084140501c83d5244000808c025041c003080d900a0010611144495088030f40610504135040050f021000a00015501101d0308901025056803404030107440c0410740108000c003110315618490040340e0042095a58501d280c181030340c0305a80d9031198121640e1f08440c24009070050341c132020704554809018000d07075104496800307062101d8070704994001c28035403141c005004200342c5035083c00f4061010340028007480d155030b014000007500e050300301c0d1003603941f0303840700c4c0c5c0184049007c0342084d60144442c0f40300ba0418030b42554582000501e45401c0d00b050b40c01607020260881805c080070301803160044000d40080c8019800c43d5a00c03511a04040300860103071020304001107012001414040303000307030041481c0d40c1e01d50310396090721815841281c01e551a5801c01089040a8040c050300101090010b4043c1c4694682c1c0d03848810034000c0307100c042e6406184120007250070416803401c60 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 883584487 1250 883583237 883583291
    0xf0904060b07031206180e0a020409060914030306060304080d0b121b090906010b09180907240f140705031614160e07170f060103050c180d06 62
    0x651a000c003894002d1140f030840c4d41c54403032107040490421401c2d07020a030f070400c01c0740b001c1c0c8045800d6100c041000d141c181e444501035402810303e01140240640b40d845003407281c0c050031098142990201042d0f542c2c3c0300603110940c201c0c60420029010071071380405001d00503441c40000c17070918170080000343d892820440000003034221a02185040c010300b10400700c3d921003500c5520052504056031034442205214050281900041341a800da030781030440c5c842c0c90200c401c005001c0c10400c103034076070b141003601940048103012503a0a012040c55586440b68031142e40d200e803e440e100120856101703c655074404203d40c03051140400040040c000b4011004250080107035118103801d2003400c0b8101d99102c01099007140100d010088060278005d0184d403500c4800d8034143e10703100d01c11034071600710071061f8a40034202c600307000078080400c016a014003001d076007d204d242c8505403451918852400030012280000f1a28800fa061041b450780545005900c001682c01c2d200403030b03900d0402c8582140c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 883585737 1250 883584487 883584509
    0xa0303050108010c0906050f030c090a0b0a0f1103031f15111209010503010e04020109150e01031406011b080403080f07060f0605181005030f100f1b050f090406 70
    0x14041582c0c01d100d030200034802031401d1018a45000400350081c45012850402c5400010010f03080000800c1200c20040303002d081d0761903496648095642c5600281c042d8400503000c545d5180845104010344500f218261015518680300c086074520040907076420030001540c80d0b00d0020703400242890b11f5080c240b16490fa00b60110400350301a0608001c11505203804c40148480583c690307010065034150303801545901d03156100ca0005131030103041d50744800e81c1c200d003180c1ca1800c06603005000c112030000c00c0c0c23002d00c400800da4451610f074050032910796000480c0a207008070030750b41000c1c185a81c1ca008092440c5011388a0f01c0e040030f0765100c000201000b100005111703007003100300d22666404078060101007007114285400034104004000d2801e42c140c03900400314400b0b481070403003c00200801404c0310081d81010b258940c440310644081c281d103d02c0e14800c94812442c500070b14000b4040d2484201400241e50010340d0a5000759108294145050048003001d03121071040001410705070481d = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 883586987 1250 883585737 883585739
    0x501140a0c18080601060807052b15142808071e080303070f1e0905040f0506030c0910030b1905090f120c0a0b180d140f0307110a03030501 61
    0xa4000c0e58104011428294610020403c0d10004903e0700d06451305860300100380e0700c4120086406004500143e07151072846508452031103641d040241c801c20b4a11424000c5148030500041c8003c480d10903440015126029800340d0724004082d24107180402c00495510010245000300800b51900207440b01d502c46c00003402480ba410424503110b20030b2020001c0c1d007a007072103a05034803030102038013034130501804011a0703120302e00980d8a40e800a11a64050700010300c000f600800600311032051034083c42c81c0a51b201403800307990290b0340c03003400c024000300243d403a080280020b14000a002001c2d42941000200009099185290060b0484242110600d1021030f42508441028040126640c4203002d1054018400328411503202042c180041c4c4401d4940041401d100c00ea0000a0232000000100054006e80c0c4040054a140300b4088070340304401c05c002079444801c082d0b4120b207082d10a100014102003100019075004025140c850490880f10000c68034040b102c0e0f804038042074450b40 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 883588237 1250 883586987 883587011
    0xa060501030602030a290f1807020717010207050c1509031f140402030d120f1d1b010212070c050a1215050c04030305031806010f0806010f031e0501140a 67
    0x149a40340009101d54050039201c2004405201060406c05000d03400d03e40708021140c0da04200301480d0002502c41410390302d04214001e441b0780e468054054070b82c40640310091a24014429030f035032194007000410050b0410781c2002050312400301d01821202d000c000030b28081d10140b040107181e00d419042100401d1040c0c42c544107a90101804640207407900040001507a0000796031a03000c0d4241c200018540c044005181c090860701240c41242030420b0a80440380803460704502180391414141c80040c440300c0149411805d58414007401648004481c69824040b140140600361007020065200e5075640007040f1b07140b082d44d0295114640207007920061101801c0351400f80b0060380020040e5140026040340e05000d980809000c12801200050502c0d42c006810008000c04800f02c642a6a680c90b42c0300d040b080502407661a40a404000a020a8000b0340202584d6001c0e000941c3c030740c0d00b90080e0400424424096481c1c3d92240c2c001c00300311001e000014007940c1c20503000704045c1c8800b2 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 883589487 1250 883588237 883588241
    0x70206070806060f0c0f010e0a0c09230a0f05072705010503070e0a0f0305160b090603130206130b0417030702100818160e0106030e0d050901020a060501030602030a 72
    0x406820078081c00034204107056035a201143c1c02c80c00590341554030307410301000031460701810356619046507103001c450350303401840011789240c2144950000170005440f051210301742c0307403a010901d8040c0c040b101202600825400c1d030a030300441e516000281e5250115449040c0c400a0313403110b000c54180190340740500002039030702203c00c05032803500300304500d0480001e1440c4401800e1008100c660300d2180004e940c7c0b0304454008000854107401000d481742401922040039100e09126031140000000304c145081b01a24101c020007055113080d80c0e9286000012160f40100490340981e0410055019103860100040904000ea401507103903810001d0a90701d2000701c1e8440310240c2d0051000f0030050790b4961002284840d1880c11580e03a4840c1c40590304121100b20301151640940305c5400042d4880d0444801121a80403a20b034650340d039004140c048030195407100d08140c214211081078a4010340040c101c402c0180304480705d40700503071145401c543c02030f0400c81d60759030000107000003204a8 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 883590737 1250 883589487 883589491
    0x7080406080601031a22061e140901080c060a11060a0b0112270503040302120102071b240207091e0b091e0c04030b07030516090f0b03090703060204030308070206 71
    0x1c00f00f61400e42d42c0e41c1d0002e01c0314402d1140045106c0d158100200c40300f109600302070001d0a008188488019141c091851444240d004011a070703c2109071403121b61400c11500c504a90f0703d4030180c05001151803e003c26584085504800d02c1012031800540c0601007248170310914001c400021400080030004010030f1450a1445006050501d14124034401150b4042010100c984440c10901280340541c01e60040e40d102943c414006403105a0810040d0018030303001b88218100c0c1c0a180000f00302d250264140e00504e000398091000020850700d81c40c410101d03c075568011104e62035951740c150420f80d4087c420110080000075410100c2d45014040c03d04041700c104c580110618150b1300e083c50108600d02d141408899650204141501070411100510b070880d1481e292490462006409000700f030700c0040003400c801c203800c1107091142c6085401e44224403203a82205240460b10342c03850700044d081984600401d1400000650648001c200071880b80c0c640f0342c44c500d00b411010b401c04c480 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 883591987 1250 883590737 883590761
    0x304110307050126100812030a110f0a0507020a0e10030303060f05300604080309060f0114040b010314010303020d0f0219080d021303060605030d030b0a090c050708040608060103 78
    0x2821101078031058584440401180914031340000350742e00d100d020340c0112002d51040b607003805074920a00c03d40c010b46e00114454540690140080d05440d4206000c610071a4041204000c05010020345988100002c0c00c00d24001841c202c10641c13548458240c050042d5a001801440100f0030002c054040c010b06c1c1c000c00349141d0f40c040152811000c96055142c48041101c0030101c86210350b10001c407c8148140d00f500c100448890385881d213440c0810303503c1a41e0320106841181c002a50441c0d28184d514169211030b042680110140070500000e030100d01001d605042d10f03180d5070390600b008200c003d80250300940c02064070594038140076186019030b0b09483c00319000002035420401ea001c1000740490761000c2d00c40c0e80c800213290088002c0c0142d204100c403a13640110000281715003a01f043c0d007903c0c000c805582c42d06101d004280e0444500b9400303d33400441d0710310200184981a880b40421307111904180385440040c2e0b550807090b5205400100120b204881445400d59240c4148500d41d06 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 883593237 1250 883591987 883591997
    0x150605030a240314070305060a0225050709020c0a06110d060e0709050d060b0409050f121204020d0303091a040506011205030d0518010906020c0c0922061103041103070501 75
    0x5126500d100c01c10b08280400b80030b0091028025220785020055030000f1a00700050312694245141124080d6004081005414030a00182005490390000010b009503002000300101840c1c00058806500003852401d50303401140340100100c0c60768090290b5076403462011640e500d020010a02c1143c0003500040340e0501a40f0400c807000740c0240d00308080d0b83c0304456100c010b81891174031601410418100d40d42050030300c21028100903000840c10b141d115104140d413011480903c024155000d505e800b1010a03400d072000c20701504011107200da44501a19010039140d40d00d807501e418240140752a10f40110401c010001409420321901d80508083c05c0c001c0101d03005600c41036500e02844511040d61640c4001003842080303042c401120544058000307010a000e0b074180381c0000d4101341c1e200910742c000e1010301c080030301d07101d45214070400c807003803d9465150507100380c0450028104400c82c0e10903030340c10303d0704211407004001d144150700c42c041100018454400781820300c41c1c0c5074420f50500c2 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 883594487 1250 883593237 883593281
    0x12061109060d05091c0503060a0806060f062101120c0b040e06010e01110f0f0606060703090b0a030207060207062a021c3e07120204020d150605030a 65
    0x1540e51400c0b5400390200200108098a03240c0e540ea00707004030041d03038004085d0040e00f07071003035141c1105c003951169004840340c212480c2c1d144200c3c2e89640f02260b59942c014454141c4640c0c40c6804005494060220500100150841020181324500a0700034045460016005004020018150402411003d07032600d04003803500c801c00711140710140c103041c107100510b11040c00c640d00c2400820203507811102151084808061004e07111140d0343d1800f5944d00441000902074200003044400d040c0d41503440d28001481d200b651050b07508003100742d0040580802001001c00c0190024080e010b000d100c0003e802c9040070541c048141140c84106d070800d03007100051803c6600440c00c9199031409060095031008c0c0513808541d0402d810141e00b055005140280344103004011040031207405000d90b008045052a1183d603548400d4030503200542c0300d0180c0f03200141840d03000703031048020b640c0001c00c0310008044501c0f01c28134242c01400000d600132041000c285218054802e01c0305001c8010500c0e0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 883595737 1250 883594487 883594489
    0x110a0926030d0e0c092401090308030a1d0f0c09160c061a03011b020c0105070804060311090310090501050c0403020307141c12080c041d100503030412061109 69
    0x2e0040e1140c142d00203544907040040c030401800300603e030500041c02084240b9040c6a0884243c2001d070b0800e260702046840c00f0040d50048030f80c5401d51f608600c2c15410b55850718a084040d15582c03081d900b080303800c0e030480300070700e20204078607000e001c00d03030f4081d10450030100b0600544031001040c00f11700d14107034030b080c1007043d030011600c181e629000308020175201c0e1601031910044003800310482d015031074046004554a44408015000e0702c4c141d0070340c1c0344d080710380004442c1c40c040c0301006010307050104010000c681c043d6120002d00d10501c4526400c051707904001905141c170032400c1d200c0b441d4a810390031082200a20519034881d07800300d074150600d421a00030a130f031002c29000340b80704802141d510744c1d102d40d904800c000c07107400c400c10301003240b03600da20307000e2007413214040c1000200300c3d0140400c803115004016201070b10030700128500c0b952440e007920944c549000d09009404c04041c103010030340340c03001d0005202070305d002207260507000c81614260003205d9040d1025020280280480402 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 883596987 1250 883595737 883595743
    0x3100501050907030906061e0e0108010c02031b07031202060f0906070e0105030c040b03011e0e041e02120f01061802090d030507030e04060e09150601020619110a0926 73
    0x80f20340c0d0315001800e0755951a002005013810341094500c0180c8841909504040d041e1200648200610050a50b641d9840e010300740d614800c0c0f0740c809600107011142910807003290701c05190b56a04100c5a85a40c1c0b42ca441c520003004041a6005130040410031509045400c03c04c0c1c0c00c280080c2c010803140c603082000402c4003045044480c10814004046155164084250b50140480d1081682c1c0c07075a503a00c112100d503007a190808000801e46034002014103141c42190301c2590850301c500610170f111004244a00300c82c03030381280d00c20705c0071f0039002c4003c0c0708103d10440891088000030700d10b400d00560300076a841418090300c0003401004400303101d8440024001c0b496500d4200b060f142d011070316054418404a20718260070620f00600010364440c6010340e107011300e10900541c0c400140081c44404485411141117000d644000c000c100440c41540039066840c00e8200300168a60100045804591104520000007140e00b00140070b610f59480d074000941c0021040c0f8007039a910901440e031 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 883598237 1250 883596987 883596991
    0x607021009060b120d020f0a0c1208070b070306050a120203070b0a3011030402150a051b1b030601210204061203020706030b03070b04140f0d050309031005010509 71
    0x1400c191194141020850240c0010000b80300c001d040c000c50b60a45403140ba03485612071481401445807240210410b00d01180c0000280c1d00810503828050414103c0c8034244c920120445d00c6000801000f00032030003041c0c07801d01610940d50302007a035503d01130802090086135001101940e0585042600580d0000340d106e045070320f03800040b80c6801d040c240c2522000c8904004040b422030b10342030804500715001a000340000601c20422641e040c40c51301780721a0208850003500300e50f01c00702000c1c00b50f8511010f00400c00746454082d1030102000c480781010900ea00840c6140c0c0e20181200100f98030301c1ca01c03110000c03416001000b2641c07401d02000100e1041c003000c4000c0403020701c20442551915008400a4544c0d640741d05007a02580c175000399100c2240c851680041c1c90580325641e51300c1e0101c3c180d81120107083c0318134202070400050742e0380209000d011950180c402c1c0414607072a1510440c490b05240903002840c3c60700700c1c8400341802c00c494003a652900c0da00d007800500c103580e900c030340b004c0d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 883599487 1250 883598237 883598263
    0x306060609031b01030902091f0b04061704060b1518030307080724020f0a03060b0a09090b18070c1205070b16090b1c1404051504060b150a0201050702060702 69
    0x182e4001d0f03480141c00810b01c0d060041c0d0800a04c80410060140d090140300e4020078066501495035540c806c06421401035009520018181c90080a120745e0411352694016010f850005034600300500010340b5910185212021030b8030100300c2005089842c3c0001070184019805145010708681d101c407668407a03241c008000ca0341007504031001c4540d1a05801149289000031503071200c001c0760501c035940010303000c030000905014001c60800e840800781d806040e2240c40f00540341c0d00706100d11001d80005400c1c02c0c0c010550340c102c00000006680b0307442c00340c80740361601c100d0200310b03080085004a450448074103104003004406c0006005034100c40d4401c544c0306000b010b0200740602100d1034011032344013058541c404500d050701e500c3c8441d0303030941240449808000e002800d050080c42401d08807030107085038110444031b9400d58410402154000e1044a000405415001c00208a44d038050900d2100d50b101041240a0301c0c1c0900c1000d40110319400100744034900044001e6444541d01520 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 883600737 1250 883599487 883599523
    0xb04080c0a12080a0c0216141903032304080618030d050a0e160f0b130b030a050402180f070521150103060e160e010c0203011802030606060903 63
    0xc10805820300a2049259002c040d00050542005004004a0b0192080c5030f14034031742410090054000940480c2c83d0a00c920392000c0303503207400c044002d05164400000d404c51b2401d500044001440902d450103580b1988440040982d0a02c5e038601098a407070348504503c40402081c001118006134560b8000b070100c4034050040109040c041c1140905a5480402810002440303005605e94200c000c1c1c401104086407810014021202c4101e01d9501c10441440619442403101c0075022004154402c00741020720100c5030307100c5010b2450340c41114511920765841061208515007011540480b50a0301c10b4180c5506003802c00b18084040942410107008001602c1c40e0a4852814030b40c10f82c0c0d0401401152a10b03010152030101000d0340041400203107400d00108555110312070250291480c1807130703101e4145401c2c03400d8640b1141c1d5010a13052184410303200006a40034020703070b4440d000303e10301a003030711301d051043c14607014028042900c600c1040c4408269a00c00084416143d8520303910 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 883601987 1250 883600737 883600747
    0xf03170703050d05090f010c020c01090905060d230c040c0512060a0f03030302180306090a0b0a02190c030e030601060c0b150d050a0b0a05010608040209040c08030c16080303040b0408 80
    0x98a4a10800c3e2032500010304101c10000620004104000110140c0c80244182e0301449412621440340c0d00d580b50104503102c000303203e011901d80c0f2040d071001c40505007010207a1b41c1d40700c50740d01d143c0b2509542e000702d0b0340c94104804d401c82445400c4040205840a22101e8100701c3e01419078082c41d5030b0350300880c03030310300001d0302603a9400b8035100240080a5030341c5c80c081e01c904009000c1e40c00840800c550800b50480580c0e5402d00180030780c0f0941031007002c0c01c0c0044499840c901590320242c80d40a181c0d03000c2c00218681e1038104c031255528010b588039000d142e6180c0c40d002d000c003502001d50906c642c104100400035a0b40121841d20709070340c0550614a01d41d9620102c528001041000542001c44c400c5c2c4942080000034038255624000d0600c0300d201e90b101d01030501540c109024250014403004c011500604141c101150083d200d507045155458032085000d24540010812107a25800710b04d8082480179000750000140038084003070f504e58601030315081d08103070740507000600b103c1000036 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 883603237 1250 883601987 883601993
    0xb0d0b04092d0c2306160c120c2d141003060f050d1502030c2107020309060a030902030f03031006020f03030114030a060213170c030a0b1003140f0105010f031707 71
    0x1243d24131031a0010900c0e41c0b1811045115040b40392160821503409402c8900418202107450b5603081030359005409124050400344150806540402d4070440985058014a0074a0030500c071070703010f408049010f0b2903a01c130480c104100100b001c604102030600d080c03014001080a031014000744e40c0d064801c0c80b031650f56880c2001c100007010b2544100c061020091140e5044094000d01222011101c03882403801d41508034040507105882120140e801000724145906140c400380103007a66034140003515070b1f41030300840d0804081f42e022442d1500300000300700300c009151040402900c418401820b100800c1400c0590300e00c4180100f0a48038140c1d21400080c0d5000c121200e0480d40c003107000c3d5281c00c0d0500c44150804071038000c0c05400c40b107100040e5111140007400b100500802001050900d40c5902c0302100c0321005050601d9140100d0008408102e01751306c01c0c002c5034094401015102d9a600b103090031114103130403151351800c520904102041ca00b030300f41d00c941d4810712801950b5200d245 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 883604487 1250 883603237 883603289
    0xf030a0b0d0b0615160c0806160203030403080415050f0403140a081906180b040f1103040b1f062f030f030a0f052a130b0d0b04092d0c 59
    0x1290310460a1011030800041086c600d01060440703c001c012141241c03150400251404034044510006034410700000300881d11070030032a9081070080941e03070003021004031b440041e1001213481c200b6102c0f0201c00e21041543c003100c90002900aa40d5030f03410603580e01c0c0c1c002c00001003c0c00090b155101042004003881c2d40d903108000070114100d4901c032241d002c120203006005804040340c400d902d40204802e94880d58007410707800100c0320b20f5091466a40344d032000d1007034002606400034424641211004101d100401d480a41107a440d0f0028002c2078030061007054000b0400c081d041c544210080000c080000305582c140d000445c4a55100d607038032110b0304010503001c00002c024500f0f220610000c074884900380c02000604091012007940d0000744038038544500303124051100d10712201001940140800780800301542d19000c180c0558450004064a0b03503482c00340c0d02007100c54ed206610303442040e1440d03611514141d20101410180d201c8000014442c420f0300b5100d200c00d11010300b40f031140c0d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 883605737 1250 883604487 883604497
    0x6050c1e0f0a030809060a060b2b050a02130b040609120816030801080f06060102030904020901020109080307031b0e0607020d1b060824330f030a0b0d0b0615 69
    0x100781120003606440c10000e0035184180e44c3c2c01a6400b03000042a80d54155005401c1030b2a071580c613041c41c0460303d118144681c200b5503a005030f0764001038a00303000301802e4000e5902a24040f940940c40341219a40541c01c0d400ca688020b2007000104020010b00360080107480032600d5001040c0f045070316905140b202c0d8031904d05d805615840030800d510030142c000150506840c002c00c00c83c2e01c9800c00d8580165190816240940981d00600c04940c8600e8280c00a041c081d106100100b0488c445a640042503002500c80070301080c1c0b1140300d00c1404140b802c005644602d60300d4400315003500320300851003511030310f1000b901038840162154140411600c0b0a9441c0800700021701d81c0301c0d9603c80040880c402510410b090414030075910090000f0600304020120300200032245e00030b40b8400b00407100342060b4241007400c0304c1800032000a210748010b00040704609003116980e10308800c03c0c108032660150079034421204811040c0116005103030123580b1003010384040743c00c031025100d01b54540c020 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 883606987 1250 883605737 883605763
    0x405090a091e031e05030f1909050f030306010f02030406080406150b031323030d020c010e0f0a0b060a12020d020a05121006060906020303041707080c0102120106050c1e 74
    0x2031050404140c0e01241c02107030101e103105080c45448210400b02ca50717210541e45c1f4041c50800d080415110004840240c0d00c00ea507610000030aa800d950750385060845031840c3c55002e400101c1000860350304400958240807081c800b42d0320f05420814082c0c940c0030041c0c40502020f9440140410141000e14844080d200d1903117201d40f640340440012a10746107011007100e01d4404444413603050f0725040800303c02555520080c50901268903034240c025042003406103415900d511f8100c0203690240500c0d1030280341034005c1c1083e00c02500309480300b00400f8040900881038070f002084000842801181c81d04c0c2c0c11990b0516101c1d13607000140e101001038004561119050111286041f800580a29004007a241c10301ca406d6a90304181c4d4601024030600c809608100700040c0003c05602c40e6509803591180c11504000c80c940300c0c1e00301e94010703070100c0c05c0301e0b940001d5030790749542e8000c0154010700e1689405031502c00e030300b00351a40381c1c09407081c018110f005008035200181c900f4800790b44a080 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 883608237 1250 883606987 883607033
    0xd080106052208030a170112140c04060b040905090d09060e0f030d0e090a06050102120d14010b2503231b0105040b01060309030c020f01050d0f0615050405090a09 71
    0x81c44001d21500e83d8070142e80c06001c40c540790b10715061000000e0100e812603e100504442c3c0032600e403215801649c0740c113030f42d00da580034045803403500350303554481c0802900c000306929480c1d03801d000d8844c04681d070140060806030302441c150f909107a8008602d0065034928074140801a07420000300c1c1c080300e6400c4001d40e26002c6c4c940541c0c0502da104800c2c4040340000c81d80160140c685078010300442e0401e028890050304000450304150340000000d15216208101c0041c84908100d003070314a0310000c4c3c02c180407191000403041500b01c1e102000d03100720b00d50700201164118150b500a0b1200c504400140c06803980550001c01d42c00066081c0c80320400183c22200414402d440a14024002140e00700c1d848000e28002289440c880e00c85d00d98201da141c0c49074440307005240c0030403a402c040710070403504001c800c00081440c2c03030043c050702c401c1c6c040547c40810403a040400b42c40c0605000c413000c0b0204442403100304001c0e0f8401400d1a0480d010030000035058943c2c0c140702c0421507501d084442844 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 883609487 1250 883608237 883608239
    0xc090105012d020d0f0507080d150b03040b06040605090609060909010e0a050106051503011a070606230a050f130c05040503031b0d0507050a060f15260d0801060522 72
    0x80d004951420f04c4807040e0744d0340c9005100765405440501034000d010b403400c1c0040c056015400101d500c0158000d2244400201f21540c4401c1d5044682c0300300c0d821100c0c41040010b000140c2018098500a400112103805091510a02141034000010500c91040c1607081c00f00d0f01d0b0510030f50040d00c40303403550340c1901c0580700c2e41d007803590203481c40703108541c01381004528030844039218000f501d050300d88041140050307074141d050944098200d240305840240da1040b000032181030144240090b80c07680c003010500005110300304111752141380c0c00076001d52401c2c010a44240d84000b0958288030071000d00296200755400100d4040c0200d0700100d40501c80010415204143d081c04d140a68403179108940f4007040002003180e9a000d180c00080465102d01203140004103da0000000361104034000214080861007001e11415268040307501c84840342c11800340c0504c411201c4c80c0118811000b40219009864004c1400c641482800704000001c40c0145110116154040105c41031a0111f5021 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 883610737 1250 883609487 883609577
    0x103030e012d0216140904030309030302120a1508030414011206031e06060f05060706020304020f040f020703021203070921080406110c0a060509040c050d150312020c09010501 77
    0x58001450b10130000c078075002c000641010221400501c5a201422040480d240d51364150301a0065243c11424141c0074000181c0004518034003e219100d05200070504850a2982c42c00c040e0030380e0420201030b04208001e1144041245685141007020f02c3c03d101c41c000c654407030400604003900002c1690103244210700420000100c40c00c00103006070702c100400c41e0f039082814083c1c1c889114042d000042441018041640340d0b001d1603005002800c1001c0c080303400c6000404958410705103807509a80131480da03041c50307810040403104020354403a0314a50305000b03c2c081d0001d40749104440400005031010261028150740d61019154000142921113443d120094000c6808400e480ca5038498007882a04610301804054101c0e04030391601c1e490070100c5824440038000e202110360600c50f04015048480e40d281c0300301c000d00c0012141c030481d8a0705500d0110030b01d0100911030b000b15840715170b041003d5903075401540d044070710900300740d02e0529000308070b0401c815150f69041ca0182c0c03200711041a07 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 883611987 1250 883610737 883610743
    0x170c06030a0b09090607021f18061d07030b160908030706020d24090e07080f151e0a0f09080c01050106020d090e010902090d050f0714090103030e012d02 67
    0x2c6200455001100d96030302603001c0e6981208544010042e8070010b203440c20400c40c01e914042e00480d40c1c2000c9a44689040c101802400c00442169060340d269801c0803442c51002104103032020b904042e000d650300d546c0751081d003004082c00e0003440d014640b07440c58809001c0c2840e18024000002540d072124402d06095000303400060000541a003003111880c241c90340ba5405d45a030f02000400611500e040002410040c001003803201e495106400300481c0030003080081218003041d19008200b44402d211140e004190098415000510764400100c2d40d01d208925031faa000f0403000000844078021a21500a020a420302806104001802d08440041034012505940300c070780031140c0e40c03140700500322409681d620a520400402e20010b0081d0300194005040024004000c0004600151180381c01c00900903101281039001550030041c500c5c21405902a56104884000d8150300d5900c02800d0000c01500c902d0411030007440318903c0240c40300d40c0380039000d14000001c043c55148900a55 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 883613237 1250 883611987 883612001
    0x3170405040f02040503030720060d02041a0708042124050c130909110324220b04020a08061302040b0603160807110d0c11030601050307170c06030a 65
    0x3028608104003800c0940180c000c640440c1e0006e4000c5151001d507440b001c2151900c03181142036251403c140080742c2d640d04000d0301100d00101001a52107260400b46240003041c10808000702c0001e0010002050180054904540c501051076400b840ca40b13000e602d400301801e2004140742c1d030040b117044000c0401070b000c1c18400034042c4100032135194007840a0003030140450300320072080780340700901464006810048026114034051820680e00c040024144942d44819031201481d0070002282528441e9525810030310800d500c900c6001d08210f5400d48040d0317040042c01294842c804102191600200c020040c1414001d0700c1480c109180a003800501802c0281d10032030806400860300d00d40754003200d0003400112200801800e00d40c1040d280c00c900100640240240490811700b100803c4c04110709102c40c655a0684e44100340c0b5200301001c0c00301d0303102c0e4042d5204a0061003941c4002542030146c4091680701c1d02c0c400107000c00c01e0b1170544902c00e0345811420100074404a6550b90f080f0302 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 883614487 1250 883613237 883613239
    0xf03040f060e0108270c120f0601150c03030209030a120906020d03060f0e190207030305060a0e070e150405030304030507090b0d050607080705071e120f050711010903170405 76
    0x5038107641d2000111402d0360300380c03040c0030b5104200c01c1d103141003000c543c0b100c20301c101740105440030140d0b10b000140800780c5203905d1030800e8110514100111000340260343c090851141702c42c8519404007801040c40700201001000e05900042c0030211743d800b0060440182e0340302080c116050600f06004001d405548141c0000d44206501e80300c010340030b402180151400c03480008407841c64690689128940a8802e00034500008210034030004140001c1011130300039203010a00b410014148014411290700501e14100342c04144000c590344410038003442001120f00d610781c50a0170341a202c0620803a4400c41e4144400203000040020208141c001c442007110f08000800004d010b0201000c414440101342d5000f00c00020b181500441c1745907040003480c5450b5042c200143d440301d090922400e158070007183c100895800700880e1010b40f0000108607d855405254813260103007050081000040441382e03003940001c4664461900c0b0001903030000c031000c000d240078210100866010b4002c1d1 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 883615737 1250 883614487 883614497
    0x6091305030703170c090609060a090b0d0e061501022a1314090d09030f03090302060c0109121e0e030a060606120b0607020a0e04110604060e040b03150105120f03040f06 74
    0x286017180010a54403805000b51410340303880c4901c0100070541c1d201207401e801b07014522001150027902c50f0040c00c000841c0b903d000030900442041289080d07002040301d80902c194054032851640d000c50351445010400c001c102140300440061500c411104042d250845907042001c0c14088560304000600c21048192070190303221165400e1b1a00c40310200d2101040504000f000001c1c681c0c01000011802403801c04d00058032603000039281e40c8071070005203190b074543d9022018040c07000800f40302d21826092998407858504d00056201783c101280c8000c1c840a4401c80760191410b1240d403206a5221904000c42c90f29803c001c0c1440640b000086561403801c00d2140b06c0d130500070100c8140a40086c040310145190440c0c00c00b0f4604020412986042d0285035415151242c0b0064000381c101a1180074607a05910184022a651080c1c0103200364407a2401202101040210707505580c0c00392180030070094803c1045161228580301d4021520002030002800b80d010b4009200f070310419511 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 883616987 1250 883615737 883615741
    0xd0c090b0a02210901210f3303020306061002010906060815090105010f0e04110301050a0f1107170a02070317070311060906161b0c080706170609130503070317 70
    0x24040c1c1d540150b50130240032500e90003694031040211042c20480c6052400e02042d02c60b0032035001c80690f1581e041c070b451100114502c2c0380759109080e0308855a10300380c0310855207092a640002c3d5865201801a501980d000030301c40501e039101b03400902845400c8101800400e64659015070383d04501c1c26152072400e0408040f9400340760600072035049614003d10304022354104a0301c0e01041e034000e0001c480181681130584840d48080c05aa8400d00c28160001003001100400c20191003e00c20900c40c841c02c108204070001d18580c280481c0704c01c118942c90f0720742c2c00d0780e4802d0b8074142a907080901450405a0440841c0c1e03040001040064402d5642c000e80d90245044a942d800c4140c0b04000c040d04068000303800010100e8850030f0401d002e1030420301c00e1a00300207840000c40d21440999000101d50800e001c072070b804016803402415145000f01d008140440f94100c0000050a2540310b8916100810302012160340710141064121080e41c0d42c5080d10300d0042c0c8012031504601c0c40320040800 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 883618237 1250 883616987 883617043
    0x2040f09060501150306082a061204030e0a060f080c07060b0310051603050105100f140a03052203052502060309030c0d020706050702040906022b0e0705060d0c090b0a02 74
    0x180b2401e461040c05d0005c00301d062004d401c180c0b048c111061154112009008a1a244a02d280901c0c015406034607542034600c0001c0c24004c0403951a00480240200300408000b65580304445950005554645548a05661408101500030900015403600c40c040610800011a5001600070400080c00d040c10101105040d810349209100b030a80c0118240b49050b072207030140310181d9850006e0b00d40b01080c9003200c440c0661503008402c2c004000b940d182c00b0848540b00618046801d0300031504100c000180a5500404030700c100456071094140030450f0820210740d80300e001c7c0d10258011700103030f10307407a0401c2e141ea40d81d0044041081d00d4801c011503111100e00201c2c0d00c0c0e05503182c665540e8580314a40d028000509803d28040394010f6003044084032942d103e070694414020100f4000500004820141003a07820300e0800003030382c0d00300103000c200c0d031b5230354404030361070aa85a040410340e908000002c0c1c80c824015405524054000201e0b040816408034030407440001090030b0495410700c9103 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 883619487 1250 883618237 883618243
    0x90e271c0e090a23010909020109080303043903030e091302011409030f01090c050a0e1006030c03091220070e06010309051c05180306100302040f0906050115030608 72
    0x3100a42018590003c191821542e4001c000d0b21000d031025503120f04950600648683e2007640b100103101e41d42e590000441da4041800402810928011400c0d030401d600d80000800c41880747c180703414005440e03041c510f1600c1a45000341116007040002d0150f49050203010000c0c03404582e4458003003040000e023102508601c080007181c042c2c1d10f071408520f81c4117040c9695030200e1102c039410320816203d00e111080074000c159406201d0440c45403614a007100303000418060740c20040b05214010100712810f0281c241c03083c121003583c07501040c1c0e0504001d0503002000c40714005840d5002c1208003408258000c490392648030741d1180c94114080000403620f880c1c40300c0340692050307010a000030440540c440d41040c40414001e0069404081140f607001d40a0b501e0a407180e40850b40100c0c007100000c0b03484840040001e42540a461146411054190b090aa9000091040d03584503d44103d40d00160306c040e0240750700030800c010b2540c642c0010310f0302e4001c10100381c000170f0a011700410850404 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 883620737 1250 883619487 883619507
    0x6010e030d020c060a230a02010e0604170906220302010e04200702060c03040923010506030a0f020f0d09060c050f070611090d0305090117010501090e271c 68
    0x6a0b0107000100100e404001a03a0b101180c64010410b2048002c040906008140d00d030b85422001c4061380c41c00c1d590806804e5441180c910b4083d41c10280400002c10a110005200340010940366582c400c40440003c0090040d5450720318a2a24400070102604044c40c240040e24000d8858403c280003120800041d1002c0442d424000c2f603059000321034582002c4054440544024031441c20000b803001c3c844e180d900b190340b1140c0015202e03d0481040042900a088010b81c2d814492440d58100404580c003840090400018036581e0207070980120080d174103840800307543d10301c041d5607000780c1c0125038080d01201506480852811810b810114014000c5403502c0c03200758041c0707040040580b5100e000300001000e6506104007001180100e40d28420b0182d0058400c0e115251904c070400c0004020040406031072251401038001444960b0704040050101e48079a400d140455580200da00a040441a091095000002c3e01d8100d40000420419805c071444501c4001520390305174211a01040 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 883621987 1250 883620737 883620763
    0x106080f09010606051e070b0c07140316080307031415120106050d08070f2405070c050c0607030c02061218030306010c2d060213050609060d1d030403030806010e03 72
    0xc0198445e0001840034009151a586e200070741400e80b19100c4545070711088034011402d01e0001040c030100481301c8107069030026082c006504103040c1c0312581c1c0c14528100c0015040100200c0001d0000d44660405600014151208156402d00040600369401c04441051080641ca000070b000302070144076031004c49030020012241c52646889402083c1d000b11801c0d0340400151003540040303a64040c01c01c6210071503200580411311622080801c0702c001800c6901048108982040854000a11f0400c0444201d51269598600d85425104a007214100a4214002140c8100034001c0e0106c2c207445590304a000700314450300a403509880f440100da01303902166040c4011404200c42091071011003064a43c03015042c0e03003426410311303d501107140840d88140c0000d00c41002c107069801c014024241500e65504240701d00c0c002a0160054103140390300c05a81e404540d081620460000c0c0c40000d0032802da940d501c1c0c40741001450b095080702c01070f001c43da490110320710368280000c25550000e1 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 883623237 1250 883621987 883621997
    0x130b0f03150c070f08161419110d0605040602090f090c04062a11040c020d0c060e1c050304020405060d0803070324060210050f1b03070210050106080f09010606 70
    0x42c640200194541002c1000e641d203581e00c00126000070440740080c43c001700d9580040401709010b10341503143e4007521401e101c030307038102c215000b0f08600c13a941c0000090350720040d1221980a03034008554950050352003d44a242031005001c28401241d00030b1201c000305980802c0d86400340b00c10700540640c1075070040c1c44000c04102c1040110311030100c21038240502420b82441425032604103070001c06880098500214a801540c00d43c50680b181b904018120b00140001c0800c1d004d0240080c20359201c050300381074841440c0c581410b000d100900d81400e0005030700100d1510090010450780040f82c08a01852501000c10381d907240c50003413000190341c40010186981c1c0c9490b030482c05068524018414001d00c0540584400d10914060780605240d40c014901c000000000d08169030b0003621144003e04902c1c24400540030340403c0005101c1e01514542c1d41c0d03264100700301d141c08820702d031111440e46000000f049180d031051a803030145801038071a176003c0d15000c40840c201d500c0b0b40320708404a9 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 883624487 1250 883623237 883623241
    0xb031906090c0e01140406060e0319110406121403190f170a14011a09060f04030206030c07050f060f070e01110102030a05090601060518090a0b130b0f0315 68
    0x51554104620301ca10410070b040c261030340c415950000c95000e810980c80e24462038203000f82810244100d000070403451600b429403120507004139881c6c04066100207200c440300c0d16048288650301800c08070320b483c050800c00c8066510040180c5661072181d044403846810741400e40c0049000065580e0945500c4151b0011000044240e4845e000c468140c81803180e442007003842d6074002c666140c803030b0040c2540030400302c41a00310444004070580141d00b203842d80103400002a14000d095542010094546a5582000001c520360785e000d90780c002940003400000300720b80d441d000f80152403468492000c544900004a100c252515401c44401e41500d51502c000340c801c510803001e203014000103061038039603050f540f5001800c1e07030700450b0995071090301c41c018000038040030045a03004241500d845420400070302c1c0d21050036050100a203100b41001c4010910340d58141c0c0c0640070400e030003054454000c5c0500f6400001d4400f86c4100c174802d2826230754542c094100851101d8400110a98600c820713 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 883625737 1250 883624487 883624493
    0x203070f15200d0e030c190911041e03060e2418120a1106090709021b0d0c0620030a0207140706111207320a08030a0b0319 54
    0xa45810b20400c0c5204a4019080705504010700c007401c03c1a50650f1022950299001410b15110661242c54003034400c10503100b02c5024004417020a43c0c159070b402003201000071076117000d030380036076040500d075800d050406d081017107100f00384402102d04c286000c2c00380a8075520182c0d210803581000e2028039880030110000d034410001040e5003c680c48216280140c41c04910328075048800680070074540b0300262210703009070851038106054550000a02c1c00d40b50003000079481c0e089a00c80c4040302500810721081020308007007070580140b504003c80d402500750900052845510ba0001d880443c6402c240d5118074415441140101c10720403600313851501c407100c03000c0081d40402003d5030040c0704900341c10400d4006001c071400600d8513076100e2200f403040c0b88403981003017a0140c03500200402081003000083c1701c80795103d80a400c000b405955404200c3c0d5a000c4103c0780c8210721628020901150200950f410146000d088055002c00124100c6e00906989981850801c02103440c41c0c1804000 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 883626987 1250 883625737 883625747
    0x7051503091902120d0905120d0f0c031704030810080d0e121204171911010c050f10020409060f0e0c031302040f14061e010507060e12070203070f15 65
    0x51020b84501c9040c0104c81c000c50906030140030300d030300050008400304980d2806c92800700c00c106409015151803109600003a0103042409104414041308041c42020301d40120103103018101c810032001564680741ca40100400000c032480c25030514034910100b001d40300002c088054403500e4482402c10f007080410440301c40c0310241803101c0752151006030081c8151b404050300c01000458410001e103502e40c0103585c1000c3c0b010b00441002c580c071100071404240c81c03024000a184003801d003a0460415400c001c0d003016005c070704a080c184921030440004c00c0d400d900600c00c5980c10241000703407079140c812024000220380701c1c81d2000c04000c00410089000c02c8020342c0c01c100d80d280c2c22502c8510aa02150907182d000c0c0c24004416a00c03808820102002c1114a070f00050486d14001c111000340306003400c4407a100c02d4581002800302d01c4004008081d4007040110b0101c0303081314442c03c008400050140c2c4000c40483c0203020340c030400980724610000060682d03010a1035a204403a01c0e103022030b0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 883628237 1250 883626987 883627033
    0x603061d0604082209020a051201090b01050d020702060c0d02070503010e150a050c160302060105150313030305090a08070c030c0f03050d1223040b060618130e0607020705150309 78
    0x500d40c0c04c1c480700000e04403407603c000d129560454842549500c0c048034001082d1038140e01c420482414030700e044100340e90210803590f241070840382c01603c44030030380046185401225600606d83c4240c1020098081e0001201c06c00c40c0c000f10002e02c5181345446000c1d89412903904065450301380350022442e9481d043c0c000d071794021010035040e800c010204c44480c00003d010102a805600200c0042c801d6080070200e074240390210301143e03441c608200b95a992041d258102c0079080517980c001145a1000600900301c0c2c89821018094980082e8200303108007606030f210481e803051425400007003589041966908594006014212403000fa400c01d0301c01d04042021004076590320104a05802242001d0754103035010650a400d0503e40340c90461031461002d000103100341c03000d0115800a01001110418420050780d04500d808021054174025149000c1c4401c8640958800c01c498644e000400004a030421079034020108a6004850300c0c0e44401c0e900611541c101d02c5a0050400d070304a1303025 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 883629487 1250 883628237 883628287
    0x20703020a0f0605010306060f08030d0b010203040518091b0306130510020c0606010e0a08030403060f060906060518010305270718021804020c0a030c050703060603061d060408 77
    0x44940d1110b0b650441e52400b500c90494441d50b448005009010703081c400c1034041d000e5081c011035a50708003903100e45c0c1c90203207200c0503ca4944070224010581d2007802902c0c018000074100341922061416020240002102c890340c89104134116a42c4480381d0910b0030750f06020280103020561280c14150003d044024419034a038400ca980200e005000e034030040011420840c09020070b401d200300010034400301c2002c802d02c03c01000c50700b032010f1f00f00402120b0403250702c01030000301041802011400351032194080903d8503c0c02500003034841d0444018512074468000c450007005002c1c005504030303041519404100540701040e012036041c41e20741e4465241c3e02d141140e10b1265503c080f4254200304107070030a0380d0750700420540d040c0c0807034071100303489076204460960500c1c03c00d1a45a94500c250f6130003170b0402c042007801d94280841841000040c1d60080c3e0184002901da04000b4094100e0343d200c0864004c4200c00c0d40071100c3d003c078105010b290322003641442e00710741114281071901c2500c451 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 883630737 1250 883629487 883629493
    0x201050618012c25172e06030e06011d0103060b03011d0c0a06020a050d05131d010303080c193f0e0601150311091801080c03070501080a02070302 64
    0x200c0c940403c400103052040b4060103a01c1d001100c0103030702840d4103c000f14080c0a000207100705122144295024541c40065885200c1c8a590007640004a034640c4101004211446040100b061980358111003070031110242183d4031640d0700c02078580303009904490600320f0682c0500620000780141c01030703c0c2c4840c00078008100e26020007600d07180da1108010080c4907500440c29503d01d42800399222006240c10300241454070308035203809449500d0a0251400c02800086c00d00040d5201141c3c0d201401900c40b4080224035a401802d0002000780010307408a03042d000000d2400980d44c084881000340c1c07080c03d407015112180f0030345d01c402540d0300728150480040d450302400300e144596006892070707484100d000032141030390751030840d60b12030b0340006207030060300041c4040c035500c5a07180b0440003585800a185101e040040b20517010b00700f1000e50120880161000a082c50b507030032410780b406442a2a540402d050405a0312680d0388241400f10300031100162076080701ea800703010301a0081c019 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 883631987 1250 883630737 883630799
    0x60f1903060504020d050a050c07020108150117041a010902090612040204113412050309070905180c030102031608040206040302030312040c090b010504090e01060f1203020105061801 80
    0xf0107980003041c0180c4815a00d508100b00c6c3c20083c0a41070b0040c0409113403e141c02180d4000070b0003480c00501840c8100031300018000641d20806251080e03410020b20b5070001d0900c1d1420031003508105480c0038150318401d001040400b128800c890039104000c12943c9072415000f101d44010750002c109030307400b9070348059500d80c031400303840207000c015440949000361240040220714201c0d8250707243c2100345070a02e80b5400080c41140718201491040c101a61250748001000e483e00c241c42c1c21009041d070911f4288043c0424101c0043c0265203103030255060525a00c2c2803500301d000455468840590401b5002000b901030080e003500640081c10040c501602c1c0c4d0080b91441d4440c102c204140b1b0101e204003c180005116042701402f05080203000110000340000c000f0b000b180240c0814683d07618402020034002d52241c0000d01d401d01524520340ea030742900c0c00c5e003038146030000e40c09542004c000641d64030780307110040322641c04107144042603401c003041700c0d101144a103468100707070541e5a4 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 883633093 1106 883631987 883631989
    0xd140106091422060b1e090f090705010c0f06090b18060103020102070302150d0e031e041a0a05040f0b0310120f03030c0905090103050102040f05060f19030605 70
    0x20b04000c0e03c01400c090000744902c0e071510f5409220000305104981080b2821079a108040f286041aa52032100c0d081620320704407208021a089840f0038801580519540e11040e801014411040c4030241d9540c021580c0280f42902c40c2240c080401030a40310800c4815a50818000600302c15403440d030020390fa5041c00c4c00001e2043c5000880c14502c141d5242c240c41500c0c1c1c2d010b40c1400401800800c880d1a944968018400d10b18005000d581081501007100d08a400c242c608040c0070715808403a09042c0c0040b8002820420b08120000b070800b14402c0b030780b02516075680b1240d503904107615480c0d4040480e500010109150707590040100d0001e65511b41c41a0700f50278042058020104125a60540c981065a100003600004028090150f02034000d545903142e500001e01c0d1903904114080c003440801c840c10300b4041041032003034040e00049468401507400e001c50600d84503c = true := by decide +kernel

theorem cover : BRFrame.Cov 883453237 883633093 := by
  have h0 := BRFrame.cov_init 883453237
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 883453237 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 883453237 ≤ n) (h2 : n < 883633093) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
