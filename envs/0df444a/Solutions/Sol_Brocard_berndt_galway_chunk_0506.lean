-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0506
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:09:50.979768+00:00
-- url     : https://prove2.me/submissions/ca18b14f-dd8f-4b76-ac88-4b65c7c3a075

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 90827338 ≤ n < 91007194 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 90828588 1250 90827338 90827369
    0x71206080615010507120e13051008010c0203070503030a0e070e0a020c0c01030507020303180c040e01020d06050109050d12030617030a1d012f0106031406060612270601 74
    0x64264182c10444403241802020001c10b0006011480c8060715001c860030512510100803000c55500000d0100344400303945000c04210002e513100091100f621440d90080164503042390050f82daa00c1002c2c40036100390300c140001030440e03919801400300300814000b03894202c1c0d640d0b035044450082c2950109200c540101e060071544030104032000170741d4402d1a00303106030304140b4006034a910001e080c441c0c0e91011841440c0c55294100000340d00103202500800035032041c0b4083e14004d4022101480340581400b03800580ea61148450600b543c00042440c1d0350100590f40d58407842070602144e5003410741312800001c11909404191400b45503d40246a0710490940c009028810303030401c0c0030080c1c0c02d074041c6207540d0b43c1c848941000b041030030384090f1000c55600c4032075035074007508051074002e90b00f0300c100842005140c1500340080001101101c40d151a90800c00040d4001c0307001d00b0f000046030900081b50540600001c560799a0000400c090f0343e55030301e44150502400b60440d44010700c0070007 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 90829838 1250 90828588 90828601
    0xd02090c0a03050901020f03221202072d060f090e01060305090d1e03090c0503100204081b100c020105090a08060709090203040b010302010c0203070902040e160c030e0103050712060806 81
    0x356691040208000710b18001544100c40c07d04d0001610507071010741071901c01700d00c400c050207040c025985c200c15444d600d0000888029910707180c600420221a010306221005102e04d030b0080d407021004604441e450509005c0c2c110f07080f900c9031080a081000c03060700051441e07424408030b40030b00000c2e03501060700c0c41c21002007490b1203119002e0f0f10800c40c40d14900150f1110080c074544802a02d8900403442042a042002c0300c0302d441d400456050040d0180210f440f0007da0003001141c0c0f64505855040c60b08000c0c45044801410640e80c02c1011020b071800c0940c4990b500000d41481410300c1401c02c2240030224800c42d034190024540342d4812030a212445030811401c00007000d01100039403551a0580c0d40002411040c8402030511684010306811540c00344066005000041411501d46076520001c40c0d1481c070a0f5518288a040b625039000800d1280d603042c0c581a4064850805840310500110001c040083c0301300100090f4402000050102e4000c000041206000501c800c2c02c103074 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 90831088 1250 90829838 90829841
    0x6260a08030f0618070e0f0402040503013b15070302040902071b12170901030e060a020706060b07051f020d1e14040c17010f0e0105071101050c04140d02090c0a03 71
    0x5031303c84002000400100441c00f41e1018210106040c20b4426280e0960004042006406203030070450b455420080d0380030b0031960441c140380306004054141d600f20315181c009000811040b00400b08076070840c6040703071231310080c038002e180d0080c86518006251075511260402242c00592084400074500390307045210b5001f0342070103400761080c8201c10480703401941d580f100814200015410b4590085043c03a501d0780030760310103c0415040310035500e0303518000070000000d5105190031a00701d842d0002c0402d0705420a8240c44982e9401001000b01d070180c3d0007001c1070445210801300c01241c0801c5000c4090702c0314091060850070314001d00034000c11a00c1400d05889079503481e000c154407804208004680840500c0040300c06803201000d4000ca000d04c0035003d840d20740d00201205081016068080b101548101c0c423a806076a109030148000301e10150030380e8001d5035000030014082c401070101d54624455a05610340080103403c8195a650106000709811140550b00c22000300e2204502130b0075 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 90832338 1250 90831088 90831109
    0x105010b0406020a020409020d1a16030b0f0607050705060a030e010b1e3304030b1501091505040f0f0e150a0b0702011101140601030c0306260a08030f06 67
    0x2018050501d030a01100035a100810b2001078400c60700d4418150544d01c0d184100600143c01c86c10003d002c40480289001d265002d480d140030306032a40c0300c1c22031514170a01c1000e1641070300500911144d8007080812465800c00d900550f82400f0300c0c080021181c0d500002000d13142450745011840c02000d420300390845003a00030440c06149492502c0100f03c0b10b80c0180c07620840104da0340e034500d003004000c0c080c0000c51a001d0a03004a0111040c910621044c0064421288944500768807955200710742c084034021400c80c1e0f4007149484409000601185900009424041c68000d08060390780d044810025074503400ae0000c2c0c03900560500c880050848219400440c00706c0030401c80d24402c000c00c034002c03000d00c220001d0a201003804c4086a1154800914140d502d000910461284180c4440084000d440060110303103801d00c01210680240100021142030382400895000e1403421030300d00149070100780501c0d0087c0c0382030750300042c01e42010358014111280008810f00e0484c00348030a4154 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 90833588 1250 90832338 90832349
    0x501050a06050315131406090312090312240603100306060608090a03030203060f0d03030c03060f0311130b0a030c050348040905100b0d020109090b01020a020d050609010501 76
    0x18121440031100c808650010002c01110a2140300c600340138000000140d86d80ca003a010b00c0090103060780d0300102030040360182180600c3d094841110455591203480450030490841c1070014070b0040c01404100038503040041c0201d02d41d07040c030001840580c000c448411200d082d540c6d091042c1308041c400e000280c400c50900e24440c1c141640d20325507900307244000508164000000030b00c1f47c0c8800c49a00405e410180910b00d05a9140c900a005012655030320b000007881c0841c00500d80c8203e105a4007143c0e0002c0e80000421820024010245a02d0070031203840d03a01c0311103615041d110645042d00560089005504180c2010b041505040f13183c0341e9070343c034079408491741d88418505049640b00b0200d811580d0710545100c0c59000001050103c126600130310700f00b401024040003003038010f2403849402042260034030b00700c100b0070b18104658020340058900002485401e00c0d45d030040c600c00ca230500480307000010715400207007540e507140b1044034507810460604c400c03207809028581c05441f = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 90834838 1250 90833588 90833593
    0x907060806010816090b0403031710060e06070215030c0d0b04020a0f0c0c03021f0305130308070c0f08030a06030b0604090308130c030507060906020f01020309060a05040206160501050a060503 84
    0x40541c0028030986010340756103060142c07500f600c251a801280070030001c01d203544800d500e840d80c0341009440609025000c14185904034005401e0302e4620310340c02c041d18025140c1c144001661000c1c8101c642021600303d80003852901014a02079404e0083e5220318803c0400991710380040d4030120640d00742180d9203000728010310903002c51395007003000c401141e50980391098400311941401d554038065684069041807041c643d00c2d491103d4955110800000d64406000a07101e00c003242102c1c00c24070030301800182810b00031840c224485d119060109004040c5d9843c028a162295207084c0e20a072000401c2c2030380e45c0e10810403c03074440081607000d142110100721700b84d01c540300540204002442c120214480a901000700040c60590300055a002000c039041d650311000050400c0c40c80b03010b408050300c15803071100a200b60500072203100341e0114020b444981c50364807031240030302000b90003282d10910603c40c01041503c1e01140e5150a07000e1400403c5a007460003501e41210701c6d9410841c0640c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 90836088 1250 90834838 90834841
    0x51609060501050702060307031d0309030106060503010305120a020325110103020306180901091b0608060d030f21050406090b0901090804031b0807060c0c0e0f160e0d080309070608 79
    0x280e030080113959032250107903a165601d5991000844c010b146420001d415800c070202410140d0100101800c0d24200030390081000c6030305c1d200c065440780800d06c8020010b80c040480348004e00980d50107004401c0709401140d08010004171a07000300a110b040c03902007840d4204c0300c101400100f4070f403260b164a0a00301146076040410204990488034402c400715202550085840071509501407070300143c001c00810100384102d03602c0c9220181500c510000119030102061491504211102c840c0343d040e1140c2120506180c400d988010645c000420013030182c040140614410f4061548120300c2034000140301230303461800140b50701c07029000c010260700d0040300000140603c000c0f2000e9030b40140086640104024403520302000c25002840d96004a8600003034080d000800c00e4012481070b4048031189444940720020b804040701c0c03100d0f61200e80700101c0c0740c1c0040003e44e0700009585180844840c1c52020210704003100360703d0f089546220010412038000802d210b504090f291600d8092000e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 90837338 1250 90836088 90836099
    0x809030901030c050f12010f050f03030a0804050307210201150602070e04080403020a170c0613140427061103070c080d0e01050106050706140714070302030c010905160906 75
    0x9a00500551a06040ea00c0038160720a0b40280155984103079541c140d941c0d50390200600a00c2c20400784550b68070300c1c4c111130011a0f41d01c0d01080746111004060000c6081c051000e000700c82143c0e01610540c3c0700d0100b0842c1102084040054402c1071030201c1c8141c0050703d000703a000b4210343e401c980c0076244003481a8144403042e80450b0b490112100010520042d0b26207003802561841103a10007948816098400035000036004519648400704038140d400408541040c0841403064510500040790b104c07009101c640d21718032100b405508043c1c40012030a800301012120a14024140000051110300d0b400801815008a152100300d06159a056040034140600030b981e6001005024140c0070410b1501d44500d0f0b408400ba00c0c038413100030f0100d960340750300280c034990021006603081400c06000c4441d101842c14000d000b0740d8140e6801030914440420500f81703401003c4120114042080104c00c0507409000d20b0b40c1e80c40c0100d0186c04038055000000c0d14a031043d901140320107060502c00c002 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 90838588 1250 90837338 90837343
    0x2130302180606030c0d0b030114070207060908070e1302120c10020a1a041a07081005031f0213080609030406081006020a02010e060904050a0b040b010306050f060703030e07090f0506010809 83
    0x104004416204d51b1a8400b00082202510880d03212540541c07909030412561213140c903095010b12900e4003550000342d1503103800c41c0c0400e55806803560b00c2d4003070b1034104850384188440d00d5001942c41d01700202c200440d030004003040c10018a1001c00e510030f2656040c1403400d150400d0b03000c1880e00040101010700e50301c2000d80303c42401c0710783d190010400081c0c240004440e1070f49603201c4030604800030380303003090019100340415100300c0100c2504940203e100d01b0001501c00150034800c801e0101c0031882109100a075004418400951605c1c2400203084a801c004150041c4070305009181c0301c0d810a02d008040c118010030034043d01c410401c0c104483c0d5004140c00c2e0b0080e40a00e4840406c1540d00f001c10360b030f4820030340229041403504003000800c502c9540001d502100440d03091042c5c4111600443c00e0302c440380900c6502c0464035500307032014540304000748030320751282c1401302d0700f0011065220705295440d441a0407464544001185030fa100707100c0c49601c1542420f00b0030040c1801c21410740d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 90839838 1250 90838588 90838591
    0x1020705100c0b0106080a0b040b0d06090809030d0201061a0721021507111501060230030103051f060b0403021003110a0c0311060c0702060703030b03010213030218060603 75
    0x1d000d2a00480750508440c801d030030440ca0740c0d810190071882c5594800c401059428101c0d0340c40d01c0e43d4a803250400c0986014002d071108000010030315042c032081a202e440040014042c100c40c83c86003006080400e441c24448100842d1182e000050039a1510791000d8400450700700104d5242020841000004d90703440040c410a050510342c0ca8520852040607840c110f05000901c0104680c04100329001d6442100c2100c4040203c0030f0740c444138250f00003012091020301446000d41c008028800d02c035120310215a0765540c420b000441c042102c2c9459405a6100781c00644080d000025880500209010b400341c26204ca8482040030519040702c80440780914040207101d0010081d00d528501e11a401c6200c0101d00075404543e26694048054214a4048003c801240c006010f085420030041080380c03241c2151110340349003601ca907080100c550b0010b10200c091643d0380c101006039480034800341150307028000702c240d0524107500411945806080043c000d00740c0b0b100400003180c40e0407040d02d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 90841088 1250 90839838 90839849
    0x902090a05090a1e21020c0901060503160903020402070c0f0807080307020f0303070b151002010212010312050415120b0303190e01030905030310240203040e040201200606010815010207 81
    0x510080c0201d19450034400d8411401401040c0e01d885d4a09080500308000803000d1706a4080b61543d0440809200c0d51001c00d21442010840910004000e0384505030031913130410302e514000740025201c0d80020205d07001410300796108400c004080c00241c2c2201c008102400d402801003a0662901700015524810110024019a0803000000c4551820400c0d10038030750307200c0d89403c1245000c06030345012104210303c06200c2c00d0b404504010050040c82260512401d44400201c660f0071030300c1d045100c041542070b003020480c04100004007004948501080c0030710360b66452080c492201640340c00c0d60700000d400f51103600200040c5041c1d040d202009980d541c17040c14503140b284c0c02e00c40180c00034141264058007600001041020700030403103a81000f0f8030303d05c204040319a500801c0300e460822302030680d0340160703000b044148100405e4800c85544244145440241c60b010300310000c901e000d0520070b001c0180c0c4140b050040540c0c2017190280c2c0804080411011300f401900000d544004074800d0 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 90842338 1250 90841088 90841103
    0x102070804060f140a2d0c050c04140408090307030803010f050a090507080612120403080c0d11030d1e060602011a0102060c0904020705072403050f040f0b1503100902090a05090a 78
    0x71081c40c5040400e040b13051b041ca11409600b80320280d51701030040c019442c01103d46015000b00e0020300e00e018802c802c1307608000420040e656440790386010880e480121040c0d0f040c400e4402c00030014200702e0080d03010f4404007140054061034001406003180064101100440c00d050401414a0344103030361a91001c4116500c850402042a20a044c2602030024400c590800a400310500110900420910700f44a0454442280548007180c00b003603816100340c000c0d041040328050160458004041d5a091000d200004c00d014010803c201e401e03580c00b904c0582d449001d059078402c0901404000c0481c2070019103a9844e1140310f426081c0704c0d49146903c02c3d54041540b0013031003800c114030405022044004108070180313460f05d42d8182039610745140001c3c00e2400151080c940840c409000782e500c40580880c003801170b52080700101c0c0090446401c1451013140641c1035800f0020a10410f115950020340441c030f81c0180101c840b00200b100c0303a076030f09040501400e0640040c00d0140281c12480 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 90843588 1250 90842338 90842357
    0xa0c050c0312160c08010f06050a0e06010f0507050309032d0610090915180209090109031e210e01110f090f060409020408030d050106180314030403050102070804060f140a 75
    0x20401c0926138150042c40c15903103041d120a44c441002e41c440800e9401c2226030705100c80d5548a50030081004582590001c2e0202001402490103080a440c5031031182d402d07079040982450100b890a03640a50800c0c0c0400d01e000c440703200c08421030300c0b044820700000c0a03022524008171a90302c4408035124602245a6424000b03051002d040c81100c0c04000c680014412580031a01509040e084010160310503c0c0e00000301b60300310014402e0175034090349a00c070900d840007013a8a841c0c15500d0804860103000f40c211003001240c1c102c032421a44900e8034100000d400c1c81c0f00130f009085981881648c140c180040180046880315002913031301e07440084032521695100e04010864901542c0d001902c002c0c008540407079980c2000c00134020b042d80e4600e04002e0b981e80c0d9141214804041d034009000c8440651052020603e40010f6195074904c800450b8a07003940ca41c1d41030300f243c1c81824144c1c0c003200d011038184005503220607004031b072181502d040c00e110380e0f8a004039006032155000640078060f1426 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 90844838 1250 90843588 90843593
    0x90a0f0b100801050a06050a06020303100302010e0a03021c05010c031a09070905030d020f01051e0f04021c030c060e031c05070c1203050a0b0118050105090409080a0c050c031216 78
    0x40354003002e851103000a1107981041c4003580d01803c60b600505109800d03800001c51814800002ea92041d030722182c2c041e620515540066440706904118980c01400c5404040b025890300c007204482d1941c14400e4080c1d6040a050850844008404010805040c001c0c8002c540f1400b11443c2d03103c4600b10340e4640140c481b020203854151845d4041a0180141c03018040450380219801c60b002d95054000d101d16a109404005024414650040d040b4a1280440d036102c4125543d107030f10034809000c10b17103010140030001440c10384222040300001c0c00c8400c0581006643d00540c000d10416600450400003080c3c251180c6081e5003d4910402d6559000103400601c503230703c11210203422104050b02c4440c0402c009005d85000c50b94124141c0c10001ca4208651041070841130500e44580b20045050a0400440d0741d0f5005400e2070358415114030760b00d00030800d02c1c030082c0b5200c0c0481e2100c49803803016250050500c1c4044803194800c2e0000400c40040c079421008491680c00307849041d8006284a1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 90846088 1250 90844838 90844861
    0x10b060904051306090308100807060504063204050315040b16021204090203070305100807150c0803090105041505130f150e0705010e030106140114040b0304050d08090a0f0b 76
    0x200c040c1c051405c0c80380d0791060541101905000e0015640e0740c0f2800d58540380f03035a0b65014a44103007400510100010001d00c1d110300424840c030714490720242082c00c480c068062440c000c401d03020b1200800050300b000319280170040c0640c0100100620b10b02d41c946521a044600c1d0000c044980049122605041d42d900c01c3c06a40c9110040042c4d0544039911a603001009400841d40c500c0030901c1d08000c90110700c840d06924045800e0380006080f918104400c00311004882d920b10024050309048480000b11084051441111010000240d614040c14603204e41000034494050240c905401e0128000c05a2500c0c0a000d810a444000c0c2c2000d03032602546c404c9500d01c200f00d90b42d2805101c05103915010503414100c4000340d9039134403075103c0c0001b01400c80da042d2044100b01064190301c400300354007a500600c0055104000c143c1843d503100e4802115500c01c480482c0c081c2c011815060716250484d00d400c1d0008500340040100500719550540f008011810240004004100041c07480480c0c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 90847338 1250 90846088 90846121
    0x120b0a39031814030f070f060f05060a090c020f100c03050606070b04020d140607080109230114041b0c0203150103080a03050414161502030c1005060315011203090503010b06090405 79
    0x1074171603580d14021810206200c1c0c00d800c0d41150710174100025141500018010207014203001442500068a0004050b0085c64009454019801141c41c0620306d09800e1001c06080400349001048500c12041e0040489078010300c290711030703201400301c90f0124108041166019a040d20808040c001a050038001001030b048807941c1031103800100008907510014a40c102c2d0480b070000c0c08140365a44403104806081c80c07907036140c14925401003080002100340c80d80c03e10005000000d0503200b114000c0d0074103050050b59404980032090314421810708101c0304002074240a1050810350650381ca98426100b0410031030100740d200c0c0003050a2000707070828005510131403801c490f40b0005c00601404041643d200c0d4030201005062540c18050001c0101c90b43c890442c3e014090303400f45500d141008100203081250548507210b44820880b00c1d1000e01400b802c1901030680d4080c42620f00203007800700301e4014a00990400154440716200c00042d1805503000302c90105442c0d031142c1c1d0080c98000c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 90848588 1250 90847338 90847357
    0x90f0c091a0405060a270506071104181a010b04050a05011115161706011b03020a06050f06090a06030b01061214010b070209070306120b0a3903181403 66
    0x200160400305e150f0000c4118140340e04000f6100008454a290300180710b00510615400002c100407450006021540046025030300a000050100b0201c1c07540401007100501110014000a83d03002c5401c24070f0001e070b00421541c0340b00c0340303031604080105184c200a4400c10b4148000d003c1c000a543d81d0500420010401851182c15a850300c0c13551000c09408641e10180411024a91200c41075410100103100c0c22041c1c45008100e00d0003054031042012038102a421030058040c5100011010b00849000b100789144808150800b10300300040880c01030180c14181e0b142500400003d182200e1181c112040b500301889080c002040030000f0b0812070441e801d40000c00400070803002c85800140c481c0d14000c0c0e500c40c02558078018140c086423400e0180401f40d500f448040350000307001c0d048240d0b1000300641e000c80d600c0b40010b00218111000103035002e07d4584000b20802441c4d07034140f441c1d01c500e0741d0725044c003007126400c43c80300c41d40080400207031045444114820414038100100c1d01000d0 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 90849838 1250 90848588 90848599
    0xd0b040c03020a0f03150509070507050f07030309080a0521070f0b01030615290f12010806071706130b060f0307030f02070305090d14070609090f0c091a0405 69
    0x5401000080083d440b02400b8004581e464424440c1184640b003aa104d800c898200c0107410b0307040c201049905100284410308000d81044141c002500602400c4241c0c2880c07070060001d24110314001d0032034800c07508030b013582c1c0d4408004000420703c002440703038090344041c403034204200001c01100814440d4102c060211007401d2202c0d4100007884411504981c01030004020301f5142d805424200709091250400031701d8140c0d605200d10210031082c0c01c00c5074290380054a84000d40c22134080c81c0c1c224052030300003d45a0740c01000900020310400764001c03000e26105008654039040070b45580f6001c0c000c0e41c0560520b0723100482e01c1115520101032480d000b801d02d6141d11071003403011002e9004030b885000203410300d400d07000e19180318001e441030298941ca9207070606400f40284450411503010541d480c9009442070f08540b041845440f0141c58541e47d0f05040328140003020703040d1110314001049161402081e401d1030b03580440c81106842c011511804881d40c11407020185004030703046140d01c00d = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 90851088 1250 90849838 90849851
    0xc07110f0a0609090506030c030d14040f09150b0c0709050408040806010312031514040c0e1203041e050a0b07050f07090e0c0d0c05060c0a0b0109020a12050c0f0d0b04 73
    0x260700806a0411266803010900c240c1c2d440030181601c801342e5070280c80d0590b020ae2600035205004002000285501c1e201150070700765111002410b81c40340368424001306540d0300040b080c6011148003000500b122006651501c10b0b0300c65030a40e904454800c41d070001d41d41e02d01140401200404075001803452104440c000e5860b410300c0714051171917107480f6000c203292881c540204502c1d1034a01c1c4c21a104201c4003411030451005110180c1a10038910042010803000440180d58002e124540c02c81000000c50321282442001c0401c01f01e42100c01c0e102c0341d5010700401a03960b4409864081c2c503c5850381c0da031a1702541c58881d2034a4100d4101c480039005102010030b540880382c1c800840600c00c0f9044500818803c4240300c2004000500600035031800340050040c3e040000c01400c09090307000c1141c80700c0603103455090f000003013078000342c61b21500058210101e070b038007060138051095000010050742c01c040b07861015601c50031000a141c084085954210750110340e000d0100900702920900c5030 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 90852338 1250 90851088 90851099
    0x1c0209070f021c020319020109120e0103060504142725090504030f0509060c01320903070204090206041d06120106300516030213050c07110f0a 63
    0x11840350111200510500700c10300c4841100f640721004440c2180c01075407900e80d00c141074202c020303044c5400030190364032444014002241c140329440003980d01d81c1c4a10740b021541c0b0004081d200ca03a0702241c0301da810309025100c40444801202d4225850b404540da000e000d1140c1c00c120044822030040c0316000d0b118241203d9001c030f4074140311652007000304036085911f45a030321044410540e80540014080141c1121240c0640010f16104600402c9141041d01000c2400d003558210403129038910100c40e41300e1101d090300820024001e040c20309525041c80c00d0016150b40740504c18011f4441e580700d003050001d640354002210054001c41044021480c422130500349003220580c5c840d40a1040d95050b10121003041c440c00d41a03030841c0c003504004132040b8044107105072040341c0031220b014207180c4441c001041003004003038103509554620b8609103140100300000360702148603281d290400040280e60390002c0e040300c00d0300781c2c84000e41004c0442000401d89003420018144d42045803100e01061 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 90853588 1250 90852338 90852347
    0x4180b180a0606080f090c01141303210509130203060a0312030902030c030105160e0411040608010807050607030507021309080334050a050a0e0306070f030506041a1c020907 76
    0x43e9945600c03a40416159220f841004160880c0d100100f42c0000000392007541c41240c0d8038001c038000c04071650400342682075030f0f03070740040650081310300d0031001061408203410511528004d0f215414044e04040422020941c0c4000c0f2444800044e640040010b502c2d0351910041c802a64018805800c40890410007400404001805038864859011070f0742d5a464140940380c840d2100740340b00400000040002d40d01807018110443e07106444246200400303c4d400040c0c0f00910440c1e0310520154903003441039080c041c2c00d80015000d85820014a40866000002c03206000c0c0e0558400441191a0081c180184007800c0d000b04045800414001904032841c81880b01006070305180d004544c60b0040d890100e00c02c005d1890100c2c00600c0300907285400307403019040071020f50070240390000000300081d081640031210600407400c180d4003104825031511401d940001c1c1070303c04004140760783d40348408401e580101503100d0a520110304004180b0030b80754403c55a40507114000ba403e10400190 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 90854838 1250 90853588 90853601
    0x1206020a020c09062b1b030b07030c0206070e061204150f09020a050603060102030d05011d2a090d02031501050312031326070302010c09060504180b180a 67
    0x6104041801e8801e00e8403483d2103000e02d200406100c00620f0100d508403112410410b011819141c45c21200041100e407441d4450050052014100c42811858800089031024081350209843d040c45410000d0300000c60356008005420040d11591040300000c01911410480216041a10042c4130402610b110084690307901d00d10144100030000200c4021541c03003000c0654000140c00c010001820810002c542051040c4182ca00d410f07101c04129040c0d903000e83c002d5607c8014617420001c500510244103804c0300c641e400d04110140e080e07420b140c03c0000448803110762500050001c4565403a500140e4007580c0c0070301035901c44442038030b41d40081c0600f44522806030080702540c00c1550f240404681c030074002e00080000c80417940d2105049442d0030f001c0910720082003030300344034031302e54a1000d030000902c01c0e400801c15004140c03008125203103952110051207800c3c00180400090060604141204da61001641c80c001000081218152403440c854032001801131084402c95a041340 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 90856088 1250 90854838 90854857
    0xf060d020d151b030b0904060c0e03030f0703020d05090117100f060206060a0906030201050304080705160b090f01020616050c030904060f080d05130e1003120203091203092404120602 80
    0x40f82d00e800f0b00002036058800c0300c1e1038280d02801100024001841582c0100b42e802d13150720700b2103040410000801e140da4400000360503181d402181e15000c040e81088050f940c5081440d000d0304048164002070710107501590301c8401101304030006140a0499299080200103450b00e050019903144c00c065210941681c00354050040f0000200b8100b4150050404407076041c2d44032031645d44d0b541c45020164000031012aa1406103110a03200b126000044e0b9026204203a43c0721744e40d0b540c43e01044180016440024103642020003005080c0e4040e1084030350301c0b00c0030b0500540c1d40c401000d03454214450390147c0756110b8540940420340001581485094031001c8080f00c00c07503005800c09031001d000c1c1c51205000607036080000c2c0295a04408015080743c0030403603c1c0320707554490f6203500c4d12440401c0d01c60016480491011001d140c04032072506803106070340145141c007060001040003052810114803d0185458060071800e40280460f030003805104402c6807a0b88a51034140060352001920 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 90857338 1250 90856088 90856121
    0x90f0706030b0f04060b040519030b0f06010e040501080d0302070f0f03020d080702010614010e01022410121104050718030c180203090c011110110c070e0f060d020d15 73
    0x1991114213141c8903140681c0d4402c403220f41050b182100b00140e00d00c0060800341803185408000000964400c840c60090324440c0800d06585072000004001c13400303100340a07114034100401008040e40200d0203040c1c0011a10700980d03183d600f82810140d5a02c0d810004002001c60300c9140280750b4003044180100a0655500d0b820782c54820040307003030320114091a1032142d00ba48400c0025030140d909000e103510180186c50300711103007001c645004030001c001204049465802c0003042800b09420b400682012408540c0e0000745880c0d5400e200d0205c05c0c214040c560f01c0003c5070b075150084a0700c428015000c420810515103d18001840c9012031080903568042ca00411a0b080683c0c000e4034400d80c5110010a04684000c0044900083c288103041160298819041611100c0d008824002298081240e078654000643d503161007244c0d840051440c1203581400030100001000a4001404581e23040c1044000c0c0005041d00c0020200240054064074480d5881c2c846600b000c0554000ca010 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 90858588 1250 90857338 90857359
    0x10513090510051e0907050904060f020c0f0f0106083406030c0206060108040f0201031e020703050c120715020d060909050f060601090518090a050a0305040315090b04030305090f0706030b 82
    0x41104a2440980e600005c54221403003c5c0010f0070903504840e8414081c03480401c151205c130300180103c0c1d1000d10312003001d40244039000c0940c8420000380d040d104c2c1c000c0080015503c0c011200e1784030810008601d04600d008404545498003494035000c4208001c0c400d0740e8519a02d00003e801403803400e00070000b50081d040000c1381d540c05903058501c83c50b080f480404106140c1d5004500400c5542c540b0700d079240d412060300d032020b0170610160150038480c0d21403c0d51180b00440040c502902c0c03010b070144c1c4080411038040000d0301c001041c810503900040258558059940304000780400fa0014404103280c00840c00608c02c0c0011740031085145c40090307035850340f260401100c00c050280150340e004601440c1d0414245a0105e80e02d9000e42d00c801071702c032070407030a40d0f50a0400c0c00250341500000c40c04a0244144000070b0a08111000c424504003c0003d4a964843c40d440f4004c0c00074080c19074942c00202910024408001c040754200c081e1903c640d00c503400074005169201605019900024 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 90859838 1250 90858588 90858631
    0x10612020405060304080703030f06180f0c05090d030504080d0e0f0a0806071b121e0201020301080a0f050c0a0b030a0e0c030a020f19080105011a1201051309051005 72
    0x1007200c040d030790080e190798690740c1d07682c4036400c4c2548210011800c241e076035825822040c4e002d10810024100c0040045081c10500b0003190958081045500a50f0702d0901010340268103c000ca41500c001940c9880c1c00110380c0c01c06551074000c640c0907940354050a107041c403446074000040741071007000311a030000d00790b6000f0922103c44c03030b03902030200703a0f138071001c0031400c0303280031715078001c003455500043c5c840c01c002e9552101c0d0410881d45803d0041030380b2164010b020a000c240c0048411120f1000b18110341c0b600224581d100002100504084000034800090060506c48051007080103040010000c0d5903001c806440d6004680c07503009541781c42c0140300349660218880d00c040d8401401454262201c1e000c0019214102c42ca0f9135200d0b0602007080801e440322907414005103c000000241c940c948106240e912981010010400f4010411004000c41220185040d150240c50003522000500f05401c01058202c1e40640b4a04c200f882848001406070400c82c4117544181301c113041320420300c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 90861088 1250 90859838 90859841
    0x70906030f0c0c060b0f12010207050c01020d0804021e121c210e0a1a0901050c04080307031101020d1401031a090a0303110712020a05070b2a0a0501050f010612 70
    0x24019a0005143c0b9401d1a0201d001c0f41c0108880000040444031301070b407040300286069150040b01040350350003080300b5042c0f140911004920640038005040342c400350000090038004c000b40000d01c00c0702001101c4911501c40d0450f1211003001410180012018400e01740ea26144103802c0030382d00a586c150b01c6d10903881000c0400c0f06091804031b240414645c0ea405901070484a604090584696415407001c02e00310412a038864198071035400e0031b4141011401c1c203480d402008030080d444200300c100702c4210f00208a9270341d15014030780a1945102c5400590181c80b80c0300d0296002800c1148481040c03102507140d038120313446800850040b1080001000c1445803c41d01b210294002001c100d010038041d8002c1e440d0b4446007032915251401950340e2660540b1481d0a1400580c0100000c1c0100a020043c80f0003a0824030459400c04503038410514010894000c940920031100070110002c8900f08500d04c1b186600800034002854074071040b14801c0024450100010591817441220412a = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 90862338 1250 90861088 90861101
    0x80304050a050f0d0501091b0e19050601020703050609031803010507050703050d090b040c03030f020f0606040b0312040b091e010507030309081303030504050f0a23010c0605070906030f 81
    0x2600750392801c0d1608041000c1014a20841500f013149014a2030010b5002e202d4012002e00c65541c4801d80c7e400131018502c032011380d130050500c0a01e1081031005055403000d02030a070100c10100458903540d031500403410804190302c0100540b0904090214180f0044090031440c44d4220540202610440415099490903941c0ca40854030800820000c0782c8100001c1c0013052213054086004807980d994004d20340012242900c00c503400381014000c0541c040e0401044001900c020f000c06c0440098a913102c25002d8601c91040f03a840340e00030800d86041c803490f0001d1407448941511280d03542504e05440c1d20405900d0f20680d506110360301d012983c141e514100c14030694441c0c4c20004543e40a400400f0000f0058a400206102900d04031008190200266100c0d60f96680c94624000500c00f050800400c001d102c6c0c05404000d102c40c20001c8900310750605010304600908a10340c0040c1c403040c4040304090710941c1400208620260410100380807504280d6040008500f40785050703044504 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 90863588 1250 90862338 90862349
    0x3210090b0c03040c0b070501060603050a0506090c0d0605040504060b01090608040b01030b0c160303090203011a0609060f0c0316030801150e040b04020912010501030b0a020405240409051807080304 86
    0x140200455010701101c0302440c1d00c00c1c49811020701c81c644954820b40303181c00c11401180d82d40c0d11030400b0300c0640d61502071759400208042c1c052001e070810400080200300700030101c5100210124030122500116080a4010715000e803081020741494200103014110a00c81180400c81603480003070317218030400340e0314071464101c600b50341d469085aa0705208400c000c0c00034280c0b44d005000c1c00c1c4850f00700001c50480ca901c2501c0004180d180341c03040c1802c0d204044070451010301c240082005585030031003260140402141d8540d990501540f48920700e0140b082030115910004c00c501c5141800031551589240c025101d000c5d42e6a640d11000c031001b0040c0c0314050001d82c4a1034100000c1c20540c00280b0001401000542880824808600c0c0390442d0509010140e44403030040041c44440a02d41e034111070390700d405500c1c0a0810011030001c4103204a60001240c0955819851061840c07d0314041c103d9240240f20504100200c01d200914800da100c140e40101a40024040c200004176421035a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 90864838 1250 90863588 90863603
    0x1090e040b0402150f0d0506030c010c0204020d020d0e0d0305061c02090405070503060a200703080f0c070209180f0106080d0e041103090105090d0c02130504321009 72
    0xa840d99229a012480603108076000b082c85070180003c002d1040242581130f400e55002c60322032010241c01c005413040070b420130b0301a42004014181380c0c1d038003005510300310f5015a03000d80d0b0f031032610301c0b07480003403190340d10942c00c06150401c1483d4115020611600c1c0f1074460b03034140850f803903180402c0200d4140001c0036401115414880006050200f04258824094400d48401c3c550701d40110381041000c50b0349410f46561108010b850340014881c81c00b200b01c05046190901281e03940c0904200805064944800301c4d03c80010f4182a03400c08582c82c10354050564011821300d0b4803890703804c03041c18030300d18081e0007014200303c40c1c8101403107128201ca1440c0024450454110001c1e81d83c0c900f602d0b2000e80140c2c85011413085402410000d501030034034080000303014680740702028200700b10300050030204010002c062016946520b03116003100d010100000c2c030368445140501c001c0700103010411400e000c0c0b40010380c28400e900e40740c5070b45e81d40d10400e803800c162103e4825011211306440050442 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 90866088 1250 90864838 90864841
    0x90a06050a090b040e011b18030b041103210403020901140a050f042a0e010503010f060f0903051006180207020d0809030109020a330c0204090c0b0d0b0306010501090e 73
    0x2c85580e000f01d400802d0142001030440e044907801800c0d18011125180f826020000001d1341c0c4d0b03884003010210110400031107541a00710350f80d0702c0c051940544040c000c400301710f100c003066a806200c40c401c0244460511a49003c42040ca06055042032005a10440d00074000007980543d600e0111242100107021090260502040010707a0356070202c406d03005542d403050ba84140342c40d102a142e14000610324000d6481d80b040c40203022440342d0b0100307810040c0c00c4c4010404440030280740400da850300d00307210940c1d40b90100200c0e00400c46900203000c922801c645200c5280c15580b141d000c0d01d9210320461007441c00140c000c410f0b4414680025000801c071000c403008a50b02c00c0181445201c000c0010a40c00784176000902c414030301360043e01410300d0071004440040419000c00c6507003081c00c0d55034147030309901c02d0300a800d40d2505000070b4003494036003c00ca0b042007040b0910328040c080b091106600c0340720b007c006100402241e84014060712402001091560207000c510045818034204a00039 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 90867338 1250 90866088 90866099
    0x90105031903050f040320010c080a0e060d0501031101090b0a0e010513080604151407080c1b06010803040906170303010611010207050703080c06070c020906060f0d0f020702090a06050a 81
    0x1070003600410760802c40d040c40549004114800284010350003550702190f0005106c4c041514100c603454214107004100070320340001500302e0183c0c1c0080ca450b003801c005500c0000b0200f14240f0650440326a80c9180c0390001c0108207201402c1610020281d0342d110240361100c01c800b0080c4a1a00b5110218800c1546041c681d032048004116600841c3c2868865650310172549242c0714040d00c040700c21101c0c82c01460181206449850380010403d252804603041c030030700c0600030210261583d9925a4009038140410240980342c0a40100c2d100031601c556070350380300c100d40741c0d00180035458841c0d041402c00200c0700c503e080840010314010b40a10b2541c0d00c0c02c00c00340d4120b501e8003981e800954091144d000403580c1030080300005c600403079902d65502d00c0b4030000c41c2085001410b8070140303c4400400800b40e15001406507002100703032051641c0f500c245030941001c1c0918040c442049007418141038421600d0380103065034600c01d441003031b11030b1511400031781034600900031903820000e020010003a = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 90868588 1250 90867338 90867373
    0x40201090b090114040f030318120b090f0604030306080f03030121140f030405120d02150601020a022707110c04090c0308070b011410080606091c06051509010503 71
    0x10302d000c141440030101d41900444e00c5640c2240d88150702621a04404000b8150404602d9200094840401c00c82c0c50409001c8a01855400c20150a010705c0000064001c14100401640342c0390f00c10403540036180c10f10300100542207501901c200d0f8000d452062020300c5000091f2410703aa0005825003001c54403441d4100c090480340c0040da40750301c010140c100c9495090201c04a26200700d005581c1c1d643c102810b104400c0d000101d0b030105039104411030f8040170703408a6000c40e00084c0c54041c81c030319214003004038503100580802952041d684405007000f038020f9110202080c000110300d528542d00c000e01600c1000a0030016240d5070003440400c0d100386803c1e84484200e07403084034040c20040d22901c0c2c1a40c160400001111031010000040c031840b0b40154103d107485004035500c259148e100c800050000c00701401c414011030010406c10070907550114001d14150000c100702c0d840240358100040907010039501e0000d28a100042c5a110303003031460340a810703520050700500c10900d48440340d92 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 90869838 1250 90868588 90868597
    0x1270b061b241302031218011803080d09031107090515040903090312091503051803090a090207060902120a060c08070503040b1b1b06011e050607111507060c0206040201090b 76
    0x90340341c00748400b46d4003100808006001c0a0303400383c0381d10920302c0c030301b000250101c0307038201000340e105412100c01c00c0080d10503403c84560310304009020070008090f1030103591610388800158100e0054950210b12a6031683c0110b20660340c2c904400d4002031380e10180004c6820119010700024002c11051000c51403c00e6800701d10045031402c202d6896035581c04658442c00b401407440040d455900b400100003401c1c03000480c580900e000755142041213000140c07000c5091007901c0b0b41c2034001c1001410f006841d4800305980d500070f0400d04e28060038040e80742d100e035200c900443d40140b81281f001d103418801d6200e240b0030851616410700d90f849944845940031001400740d0358a03000d4568040c8100e92aa0161001c21900c2088c03552004034003512500341175058015240600314049019580c03040c0202c00d1f02120741c190703500c5542e203040c1d0410b500d084090301462600b1004d03141130410148903600003080c5083c0a1902007141e10302800381280c645c1d4050742e010740050141c60091141181007401030 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 90871088 1250 90869838 90869843
    0xf0703050f070501060e06030c0a14010c03050d02040902091302030f060409060b030708030903100b0a060e01120515090601020109050c0f010306050d06090501060e01270b061b2413 79
    0x11402c09801d6a0352a003900c03801c0c0c00c903420440c01c1105101d02030030100030009040740102d0346000c0c41e50030012500414001285441d04200194102405050294040319040341c441034080d5541c0da01c850950000e98041c0c68694083c40c3c030011607200d02c130b1313041c82941d0103080b000c42c0030440c80d00d84008200140c1061102507500c0341d9a08901c87d802d82e01003040c00002c02d0b0300c1c0061600c901074001010308040740c03040f08086486c00c064005496683e00a551400d0781d200341042d28002c00c0347c60048401044081101c000c5520703100074032170008100c100030200c40c881112060038594504004909a91007400002e0103540500c52011b010701e0400504100c584044c58002032040e0303642c00042190b4543d41045d07038515a40c4c2c804500380701c802c6c0943c0e4080c00041d00380300d0055240c264902d40e04c5c030404a0040c1211008921151540ba41d508030309100b50380101000c0d01c5d20f10002d02c1d84400d0452400010051013060340651702140c1340d00540c845079922601007000c503a0b801103a030041c1c000a0004 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 90872338 1250 90871088 90871117
    0x103120807020a0b06040908090301090b0421170408130602030c070605120403120b03100b04060906360e031902010501060c0b040c08010e0714010804020d14100606030c140f070305 79
    0x8a04270703900c0920075001c14038003400305083ca500b810300b000900e0350302c084800312116600400440c4400c0d007207079142501e2910262400072941d980c0c00d1091a44c007420034110059a0301da80001545540040a0400110800103903107600c2c0c1d9910341900c00e845840d01c3c2c042004c00c4a000034002c640500c0c61365980364080035010984424000c000390030030b002542d043c080c0300da80e000048558203082c42208050310303a2403020020141448803444200080703042800e100c10001d4007030710300010403807204c0c082414034002c244081c100c88041e15489030401d50380703445204541411089468130500035281216016180c000c026603080d240d6440480b001030041d58255950480080d5881003407242c0001c039846d44c0080c1c0249400c00080118100100c41402c0c1007020700414030015a81d03200c629008240c1c001d560040121000e4a03903424503400141c00f02c2c0c0d00c0c0c40c2ca407000032103d401d900134480e90100c0c0c1d035886007041c0c500c10b01a440d41c01815042d07507102d0801c1c44034200180c054401040c600541154 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 90873588 1250 90872338 90872347
    0x8040f06050108030a090b03010b1204110a030804151e0f0203130b04151706010c030c0b09030408010b0a080a0b04080d050901090b06040507020a061109090103120807020a0b06040908 80
    0x16804141d41e000c0e0f015003010760000841404a640c85040710001e010702c4007030985076514040c82c9036954061003007512282e0304103c020604002c031102d070b0340070310b86006400103d02d0ba1fa603003403407203058200d4411805c8032509400021800c0d07214928501d03c003006030080380e0300c41d50800ca00f1150410000599419448100440c08101088119007001804403280440c0e0b030390f003080140d07030550b60400840720a02010902000031080341c00c2109034014020300c0c081102e0201410115100041c5030000f814407001c000900400a030040000c1041c0c03651280248200c0005409003d0710240078452402c460700481c0440c40001c0d18610404c0d0418010030456092101018541c0210f9400303940400441e07641da4039100030810100402039000e14100c604200518013400301070f40781c6081d600000e0a640c1e07190076004140224109a403141400a400d03000705685a10b0a0900140c1103c540c40c041001600003440151000803111007140e40610b0700e100c15150f640c1400302038040107030101c5604c9010700 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 90874838 1250 90873588 90873593
    0x106090e07080705190501081306090b180c0306040602030406060b1303020a0f050603062101090303200a05180301060302040e0a0b1f050f0609030303160912030801050108040f 77
    0xd9091501024001d041c0091400c44414680180d5038005070180004081d07410701e039002c1c103180d07004403082828060417039a1403407a036048495035100020034052034089030070103014102d510948220130700201d41c1e0052003944a0305540341d10300010f41e540766000000140c00149160090340d0014410306002c40d1040d101e034a02e900e02e0300103440d440c02c1d10764000382c10400e62a010301020001c29006540c0b403201824000460400c6c8401062180180c100d5203420b001c000c4040c031034602008192000700090b034000d15000740a8201001c1c603581e0681031310842c010051000f81250702906040d100c051400701c48888800c0400d1000c42d40076410356a95200101680700c0b4040c24144200e5240642401c108501d400c40c0d42d400d024101000300c0c00c0005098042850200040d0103484080701c009034000449400107031a4030035070f00607580501000c400d200c078151641004900140d030070345496109684428100480b4644404040c0018085c1001080f00754041d081c52a0414081c01d44425503003143d4 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 90876088 1250 90874838 90874841
    0x1b0303120711070603020a0c0609020112051f15020c090403020f190506090f19050c06040f050102190c0501031109031230150604120302061510081503010609 69
    0x21210031001c500c0001202d1241d11040c4110009805541011401c042c48080d0003040ca40712114010032155840c4024010f683c01944080c8405030030203802e100c3e514000720058150b05020b5040c0703500002c4110040381c19000000d10b440302d05c100750b0044c01da4404920403c1038000c070181c400d07000d501855100201c9214144103d14000c40240d00e14900e451a62800303603d0828010008646c54020713800300300001d08045890605098044070040100c0c0b8681007080c01d000003488060380c00300c400030380040c2143c0103503120b400325a000d8081c9d40ca20200e6540010307505450100040c1240c036220000c0c08198002d03444800f130540c0310401d8504242c280c50210346040d544915643d1100c0340441c1c0e85400343e00d02030302a00c040320340f84002814100320308001030b042000030702007111604150b460940c440d1102c10981e070003004102e1003001000707954140070b0345441096070304031041c90030301030f588a80c1d041230000d00f000d10741c2d660b9480000c4c0c1d482c0850380f8401480700128642c55521420006280e0b69103 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 90877338 1250 90876088 90876091
    0x204091e12090e06130507140309070e01081f020703030204170a020f0a0303020616031509091101080105031509030c0d091502070e0109020304020d020907031a060c1b030312 76
    0x20780040c1c040c4089090042e04450072540311010982044080113026102c00403403c00b450701d40300005c40c45031612041691108259440b103c0e030150007200300500391340002810401c462904035200c039143d072144100c64036521100c9903075005151072440c00304400c0281d4000d0600324007070b00d8018242602c584080701090400ca41d9241da43e4494214102035103005410400110822500f000c0740c1440d581c2d0180d20f40d81d00070884080c405c0d03607205005519001e03800964040b000409040307403450710f40200c1d1000300310200f0241c1c1c0c884e04851804005501601ca654140c3d10300400602407041d1f451400e500194000700b98030303990f0100340440d410305d0108120780a0300c15010f0310340004803030409a4118024241005a60444d4002442040044140c5020034156400041d000d0380d20fa85900114000c3c41403084001d41000f084010444410750591000d400f1101c1c0d20480640030440004015940c00749004800c01508058038584040902c400d851301d0f88a030290a5034180440b0a100e105084030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 90878588 1250 90877338 90877343
    0xf0c1205190f0f120b060408030403150b010e04230a0b010816090618050307030c05190b0901030b150c1507111f09050f0102090a060801050306040204091e 68
    0x40400c904040401c81510766404000a1038180729140e440300b0020540c1900940b40d00134007a5454403c41c4200481d00144800d43c4040c0c821aa25076592010641e80d03400f41c8400c0d11440122110081500091700071003049170030507552080d00c2800d2004010091004a0702c817050780f9061500461100a440d210900c00c04401d440026070b81010030002d050100010030308000740050507003428185400190040079a012460030302d04403202c0d062114150900e0340c21080d450300c0307140c40010411174241c10100a03100c0030345004007644420b684101d800c0c1054001c000c481d00043c0720000c001d5102e40c0c4620070000b030060214105408811022580d40d010b0303606061990030500340409040880180942c10644078504000451840355141d40c50384074800c18960a43e081148002240449030410301610390064180d5054102c0100020300075882054200c0c043d0303400d0803001034098001c807003890495202070f000e00702c43e40e034035801c00000349000f0030110b8144004020707100d032801119404206152 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 90879838 1250 90878588 90878597
    0x72009090c010e0114030c03040503040e090c01030b030606130b040b060d0b010318050d03020a03021207030509060603031e09120d09060306090c0e0d02031011070c06030507020d0f0c12 81
    0x1e006074001410300c03440d0070b101c5041c0602019510a4041544c040341c0c0d101c003141c1078583e12501c0f10700c2c0250940c40b5039400411031603c89014004100404601c040c01488244c804000c0e594099040c152079805c1101c0390303980003440700388401e0506c2985d04600c010000c02040001ca000482001030901e03000704292512890b55101c0d01155560144244c0017245000d0244c40101800356584580c0c4903218064201050f802160805509000b5010ba0714400b03c01e4203c510a880d0a2800400030001160300340885c0c071408021641608004c011140480a10541649014503042024041d54025044140c1042901c0401407103080c043c0030b0f03807104001c0c0d65114000c40d441d0603401801d82d51150408610f4610301698010b2254200d4403103202c0700c030291070082c0402c00c140000303800c00d4664500c55140c51f0400da8920003610001c402402007a21600031002c0d229100d22040302202c104031400f40c05039029030309a070001070085c2032811403100140f81002d0341c440943d503a0610110321240050109 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 90881088 1250 90879838 90879853
    0xa0506061b070b04061101061406071e0c03080705150c0406110a080703090e010f060c060f09051b040f0203010602070302060f0f0d020a0e0d0c0512030d02030906040201200307200909 80
    0x11080c09108000c100700c2d1099554001f003180003902900c9050bc000341503c00905010f0315500d200f0302d801c04c10f40d411401c032800480c2e0307030304101d21142d010b80001ca501c0e020700758100304240c20105040d400b4801c05400a42080e08080096504865054100130144520406030001805006c000c0842034840c0d40c41201a510b001c41010144806070000c20542d001c81605010082d804030701e515505030007110100d00402810f0100000380340b61003001e070544c016420300c602e101c900e001049180e00c00070740d810044d03506d602c03040300104c0c0402e000f54401a00718100800252414101400880719040e80c0680340001c0f086c4c418281d81d0241403403508664021071040719050b0000c0d80f8200390001036404440c1010540d864403200101c40c05000d110312075044080c0c5c840075040041d42c42810180c03608554904080c9080c03596103200700c0d070482c00508070f940044c0780c00e4070b180480104005240001e600b003000c60307503498220207001290654108110440c0010560315008401d00400140d005402071 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 90882338 1250 90881088 90881117
    0x1f15032a080d02030a05031314030a020c06090907050c10020a0306180903080a050c0c030403050a11030a1a0408071e060c0e0310020c070b07060609050a0506061b070b0406 75
    0x20360105510407403032038120544141c80a50040115038032202c9500d45255295110102c1c200c007c4d0541101402c0b02c240998201a1554000003d040440094007141d829031640c500300a0544504032019411600c0f0070302140030180504060419510400309032038103a06d10300740c038100301d030080c1110100207500c80e1010028022541c0c518045650030f0785081c841c00c0b41944000d010a28045d0140c03400950f0348000a55440016056405100492041d070f580e80d540c0c0d0604558950822106403050340e031300c01c420030840c900040c403140c4496224100700c0483c05610700c456207014000348113a41c8c04608008240020b01d042078484175264180524460342d1507a400c2c91001c40e4400d0319800d05000900c028404150740000d9403149000e00c251016940c0e0308280880703410038031280c0c84480101d0000c1050004c004240e0084401c2d80d9070000104501d95891440b6810380b48140c40d41c641058040240a041e40c01000c466158442c1034012aa40d6559824580342d2070350099200f2000140190480c44c0b1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 90883588 1250 90882338 90882413
    0x2061605100c050c06060f01141309060605130303050706090b040308041202030a14070c03061419060f0311030c060301090f0501050d02100807030e011107030305091f1503 75
    0xc20482c075190031802c0c000300090741030f528440a40001c0c414130b90184c5441840e8070403014415003075440c1088031344485c000314404481340c104d0700512818609110780031800754030900070350b4590751019400045031451600d040c1c81582c041d150035500d490f01d809008011540c90600907010300c0c86607981c246a8030b840e0408003645d494614004046410801452620030790041c01021440081c000190b5600000d1425000301e2002d6030005050505280b001e401400001c0e802d90300c200c040c0d0580d06a0601c0f8802e42000700c2d1840c2c061200c091040b400b0a0003c0348014801818403040a02141c403119141000120079800981c403007081c0c1c40e00c480c1144a002500e00486004001c281c50302c2c208904194000360030820103003020720802c410340c000103250f03d10030780000d00990b44c0310000300b002c6450104032465952103e4810340c080307400c02e004036000707901c0002d4071400401e0400100a100c01040601001303003901202c1403d08400044002c000300c1e0b0700b1080e42c4103903070b051320744145158000806001e = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 90884838 1250 90883588 90883601
    0x6150801140c19020a020907170109050910180204090c1a030402030303010e130f0b07260402010e03030919090606050c0a080703091d01030c050406210206160510 71
    0x40340c03000303001d0100000010301501d044440f01c2d04840c41020300b5034000c0749000400800a5404044032080c0f256140e040056100e092420a06154240c1e0300c40c0c2054050f984140c9045546074040d10515803407480b144d0007032413146813000c8614088075a640000707060f5240c1100503a410041c40740100038294241070700c41c072521409a0018194901900000e40703e000500c2420000d482c848002854541d1101c0c641d035540d94400219038105e103250030300580b076002c120b40c9100410000114240c01400c00d0400100284d401c0303820083c19921a80115424080c80b44050340500c42031044000c159070b40048107034031091840c640300b9172604d404011020348080e42d104206028040045943c181e501184010704190448012070751001340745022030740c9560f268060300d203244402100282d50032900c00c0c07940c1260b0080c1040d403034a41e210405c10040b41c00b9072250410600350541d80490740400b03800345900c03550000388102d0400082d0a114646031014103002c03074503030b041048000c1c4805164030420703 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 90886088 1250 90884838 90884861
    0x16271a0f03011406060306010e03030403030206040201120504050604232b05040b160206090406180509011104030212150705070b0702010b21010f020a02030d1b02030f030903040306150801 82
    0x20f0060034090101000705900c0030b0211801503c0010018900e6405500c144d0082d0074081c080701d9403151780b410000d45822041e030701280018811f00d04110f94102d03502459001f19003000141c041030300d5590303078000050802c102020b12900d614a41d07c0380d0b4002400b90a19042907c0880f0a1402014080d070034801c030741075103910501105200a0250107000b42c150b82c01800815000c030040007082c00010744c64001c02801650083c244a0080303480325031001165041c081d107500034089512001001801d8882c000c503114031040c003c0c0300400161a01c000170710303580760707110041c0e41d100c40100401c80301111046845d40041400040c088040150230b8881562104480c4000c01540380114001520300030b88004840300f03884c80707200e114130038682075224a451714041d100c00c40d0b42d411164030181d1650810b606400e60b0f00d241c8010400c8880c3c58051200d1490895405940381c031408135100307c0541c00140c06030050b0302c03050001200080c05482003600c1c8000ba0141d50251038500660720742511210542d0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 90887338 1250 90886088 90886091
    0x20d110a02010608061806070c03030b030102030411010e040e06070513080a0804050109080106080d110f06010303031505030109050322030b01030f0c06030e0c01080702010b0a14040b0316271a0f0301 87
    0x1c8611b0010105005402501501e000c40d80400755040803409000d0681c5a9503255100005200c10000812107204081c0703000e0301d84200400000f400c010031204d00c00350a4459800202c00074211328855030040030114840302d01c5428150f1201c000c0f40c9072882da5842180d50510000e01884650f0704a52170200800d817400090007039130b052400b155161590b080085050249500c440741c0904010301c0082000000703041210350940e0749080040250100d58480506001c1c0300e400880c00b81410b00801c8680e81d0442c1c0210300c1c2c004048044c04400700103940380320401d2034a43c80480081ca01d520350a0080d40140c81c1190b0b442401d00f44811185229408401454586211a0398620010400c48a110000d0070600380c3c0c1d13500e1003c00d074054201c0351070083d88500c12990100301080110500b2100c03440a6070108241041c5605065a81e400039001c280c80446c101d008100090340c04001591a140c0312503003d900c0000e9030907003410b403520400c115407040d414542ea08964208a0f100e2819542c04800 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 90888588 1250 90887338 90887371
    0x10f020309150115050912030a0f120207031403060d0f0302060a05010f0303080f0a0216050106090e061e09010b04090f02010f08240d0c08071d19020d110a0201060806 73
    0x348031581128401140c24005c0100740c1108940d149030f0701184902121301501d03a0780007280b030004c110303483c0801100082029400000703120441c0d03200380c940e0345070301d92900b10031041000078030782d42078100806c4c0560241a800c5a000002c9100500c07540d02c9203e42c00406a500308218000e0558605800007039840314100c408002107584181d4054001c990750044400b83c0d207600015401078820340300004c1d12030714050f00d003900b00b00c01540100c044490f5100300304004500740d001283c0b50b44d002d55081e048000c0c03c042c1400e0b6504104807558100c4c142c40700014281c0f0b5242c0224081d00c100785401d503060399100c100a01075582218680d900c0300e543d480d0402052402c000d2480800b03800301c04282e00e40b00e94185100f01500c80004000f109a04441d01c6549155980815036460300c0703e003d03805c1540800680b000c450640001c80038050445090740704070055011769014000c1d00420314000c0080e842d84255404100090024000440d1650010408505100c1500c0c945100a40b03c1c4048000486 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 90889838 1250 90888588 90888599
    0x3050610150903060209030a0c0b09011103090a0501121815051305030307030207030c3008280207060e010501080705010c081803030f0409150501020d08040b060103020c010f0203091501 81
    0x90107034003507039401310005031a1800480840d280c6011003100410810001c013000c603803004154003800b10008240e03900380015204c8a01180c40740141c0310542d8012140c08824130081d030150409000c0207414240000b262a0010300b110350116140e203090703804100381810440c0003840c500846034080c00300821140c113001c02c3c1e41c5407941e03480018603220400d40e000c00d03005c0405210705218024150021340300f41c165011000c2850f69a543c1c20b19600c0401c0c080b075103a151590203048a14030a00c410003c0601200b81c4913000c4000300500000315000c59800c000d5100024514491a04a003038540d00000e541c1d8100f000551924000b038100d07134141302d951031200002890301d0046a10100500d2084421440c00c18082807860040510011031004e0110340813a10755500e900c1003036a0707548801c003100c1803540c0f000103a0311010102c181000040d0200002030104007440c251039040788042c5001890007540304011402c58480b4642010701e00d80010500c42200c03003c000702c6080da110741d1150a520751500 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 90891088 1250 90889838 90889847
    0x1312030207031b03210306050a060f030c090b07050d02100b1c0206040b031504050705030106020307170c030d0e060109020910030903050909011d091f0b060f040305061015 75
    0xc0c400100b0b030000040b0021603d45421411100440e03005240c0d00f034006084a0b05a030070200f51002000003490084000303240c1c50400d4141d401c41e00980c96040600340e01c00012000761421015603014081d40080018103400703103034014000140138030041d10841d4030b4010001d00f81013504058540d82814181c52080c1c40c0c2c0e58400040395a1140c840040300c5180c01d00c08911140280d1b0300601c500743c00401000300203019a01c0c00f1203201e00c06c40f020400d40d551840b080e2343d503010038050344005134020300403040000d40301410002c860708240f03d40c038100840b0206407407030340e40210510040b042e2680c14040d00003100300000e0b8054003010030103506209002d404149a0800f07699080c04040c0c4580d443c10525006008a48900c0b02c00392500b0290b41e12070f081e1900b14100e03280d1070728449840c240040c00f110340104a120300c154000e000769007200f021120143c081c0c404407a41503801907040010115055940703000700300842c80740000d84460320f48801c0c004c2c614807040c0d010801454481c2000b00469a10 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 90892338 1250 90891088 90891103
    0x90b131406090705010e1804080c0106050108010308090603060a05030708030418020a0c0f060b040207060b01080a050601050405041e0911030f0a020108011a0c07030c091d1504081e13120302 83
    0x80c60b100b00c41340350140001e504c51f611a22005500074010060105022610006001d402e036060024800300359a84011a06054240b00142445405114100075450444c004513080b52004096840486e01c900c006420310b94a640840c60030b40c000078082100381406102c03c80402020721703007141014000344000d440c0b001c04100050031000090031200400a10364081085114041c0c021500e541c41c0f490118020301c001c06645001c9600c440c0003c59901260041c0d6100d6041a95800e003818940020b00000d450a402c449494220810281c039840d0028414003089078054494540c015685070f040c941098000700d100c0409800c60000100540d03040368000341140e40600d400c4030141c0d12030400f034a00d8050340700030742c2d018000c080b000011302c40030000301c0c415141421010370101c4800a0131409001c3c0310070711080d035034001c603450303030300001050a10b1540240100e00a502e8464442c00401d21403e1175244403140a8012500d090300d2000850381101400205590403c0c0c4061360710041e607941c54 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 90893588 1250 90892338 90892349
    0x20906220213171c0203120405070e010e1504020c0c0303030901020703270b030a020f0a02010b09130f1e0b0a0504030e01081e06031009060f0515010f12090b1314060907 74
    0x5452021401c0c170300c01c0084490b00c1864008006003820289442c58445809204030043c074009100040b0310504204030381341c040c180c0f8a030190b030480c017603009003c0690040f580040050041041d1038466450500003548510503003400141e95585524010740041150851070042c110b21242c040c950340e00d000c0d210810f80780c45495039510707551080c00b000080e00c80d41000b81c003c8000850250092501508078103540032089609036070540d2683c031803040c030500901c40503040c612090241d002043c00c18a106580c114848444d0340010142e4550083c400d00948200c2009a601c0c01000141540402400d98240091070042102c2c02d25000103284e04400110034154820841c02003890303941c0410409101e458884020310940b034840c03c02d20020554200c02144042c04e00001540404030b5400300313195000c05031100b4004c0031030118115000c0082d40072641030a9628114200821003044c0454840c0854038004d810307001c40d40c904603100c607180601d0300007075900031020302420040c0440d00394152503 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 90894838 1250 90893588 90893623
    0x20a080a02100522080d0314070203070206070c0e0c030106030f020702060a0e010c140f2104120f02090c07031101060509010612020403120c020a1a040302090622021317 74
    0x5426a808540101c00d01544090040d0400c4001400e0705c00401c1c4a9000003158400300803d00644c1408141107a0807214480141c00c00c1003c0c1005251030b1000c0d043d8140a640d4008080703480e0035003040042c509403160101410048010440c0c10340c10b00911015078040308081d402d182c02c5902240143c01104402401d2101c504250740140e482811056849601b10008040c0d0100360f151642c0c60f50100070045502c1d0050840b4000d22945601002c801e04000f0f01d10340785002c0c80c050950b084c3c103240d09400c80300720500da2402d00c05661510b000c0d42c0514641a41d0644c0c403140f40c40c004d000403010040b5107895904280d404c000036550803403402d0440d202e03400e1001ea018200c04044000344980e40005142078040748002800d95481444071024a00c03c1d035811000715115130006c4540d5501c0e42104104460410041c801805c0089400b60480405040405020b020600112603440780340c01ea080e0223540030442181c0f032001c00549400a00c102048112469910924a41c450702944103040b1001c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 90896088 1250 90894838 90894847
    0x70506040b030c120420030f1203181204090501050d0f02060306040f090c080d08040b1611030706050a0f1401090c090e070801090c03020a020d1d030a080403020a080a021005 76
    0x3d0000c1c0c0704698081c0c0c4024003040715880d2a2600358075030305000e03c1010880c01e8000140040c2c1c00d0014400d001c01400c400204a0801e039078640c2021a84000c04030715001500c42003440358a9010001500c00280305920503890300e0511020004680050380030b1442003603200c50103801f04802e00d0750303004503580641d85d0b19620303070383d10000c1005422541284100903107081002c0051000c2c8c0698034003614417003010340740c400c0c00d445000c481c0c3d0081900c000d09000010300c04500c0b0714810300c058581c41651070801902541400782d040f070558005050640368a82c44004102d8900154482c0c1054107001c0700c41006500b000c0014102107000c1406030f000300550300c41c1e10074100750043e4440720080001d41101d1800c0e02c3c00703000003090b0710428032840308011b0402c0c480000c828040d00a94403030581c1c03980142902000e9840460300d069a08505404014140001181e90f417020300c07032108424065101a9600c6240d032041c001c0214081e400040c5036003001001e940140d840016040700340103689003640d2135 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 90897338 1250 90896088 90896101
    0xf1407020f091f0308040315020304080a030504020f2d0a18050a020d02030103050706020c0a03121b08040602031305032d030c010c0c02010e0f06030109020d0b06030901020c06010602070506040b03 86
    0x20710180400200c10044104000020032445d800100242c03442140540d01c000c40405251050380002d0b00c005120150038071030503c143e846540005ea020780002c0c0160042d440031004151002d044019118071282403140c50300b540c0c2054604955560001d0300c0f50111140f4000c400c0300c00402d901100703900c1a0f22100441d1a22121b90103a40c800e81204104540c0ca5a403032410700d40e2441c69210713203409030140b0701e10001d013460490854021640c10854000404810300c0040350449020004207041000007551075003c9000d010207000900000e80003150f03204910001400c20314070741d901440c840c1e4080310014408441c00d1005003200703070203601c00c5402054825165401c50040c908000c1180d0700c1c11740e1900c0c100794020444001e2500030307201c4403135441400050201924125440035006802080108410200c550040c80d1120101c1d0000a0212a45001a46580c0180c6e80010a40c1d0081811048103c05004090041c412800107006480c980700c0031807104e0155100d8124000b6010002600 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 90898588 1250 90897338 90897361
    0x4061d071512020a05090310020c1b0105070b04051e0f07051002031b010213150c02120705090903121018021308060717060111060406090302010b09070f1407020f09 72
    0x1c802e040000b003551106103d2000030025004000e00510034880d1030003c00803200144225030340b01c0001000350014803a00d0b202c0c01c3d004041c0700c29980c10010204030007004100c04c1061240101d11500c0900058400070403064250b10508020030000d0300b10022200411000062400844805690004034000385020503800c6008032000780410800b100c1259100c00c1040d40284490081c45042d9a0070715290450380703401c00001c00c103050101d2403003080d5001600d000c1c0c528014890070f40d001c45555035225000710701e6603c0c065950203d2a84040b9240f0b141c0040d014007564040060320072f10704943c0ca403410248150f0882d84540907c00d0340000d1740307040c80510b1402a805842500c04841480c1080b00e8000d00c2c01882021400b0110410300125400358400c81c96038610864400017042c0c0d54940e6110b1f98001c0c1041201141590b5980388000c0141e261812464400d910a40b41c41015008034078010389202400c03150100c004004208800069132440051500c5180c180d85000c603d40d6103c14400d07 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 90899838 1250 90898588 90898607
    0x1103070b1506070b010e0a0204030b0703050a020c030c061501081e04020307030822060e0109090f020403061d0106081903271404060806040201090b0d020f030f04061d0715 75
    0x10b4121000144a81c103200d0564010f90403644c8980003551960356103140e5034201c0c0183c1c0001030101003a03501203948640703c1d03006690050280e00006180c1440e103417610f8507640c01100b881c002a00420104400c680d194000c4c1c108000b030a003007a1140c1c1c50140d0007028414001d11000300310f12980800b117825920200300c81800381d9880070b1065074030100582d41d0f00ca403840300c1038000c243c60031010f000b188851040300d000f20802010b03110610a14184030914001e8060364090343c0c10240d0a02000001c6920b5004006400c40304048074800c43c071501c0102c0782500c1ea1a0440d0030660b01003600d100b28a100218441203803034051900c142c80d80c00d102c200243d82c005d10320f200c51003840c00d100c0100d80c15905604c8000c0f8558221410001d4036900c66109131154421100680820201602000303103070014002092900c6a0341c1c0f0042c900ba08100701c0700308640064a4800000e2451410071007002401e10801041d0382124224100400030075000c80d41e0b680321809200d00300d46404443d0070034a030080403500c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 90901088 1250 90899838 90899881
    0x3030414272707120212010908090402070503070611070209010902030106050702090c1e040504060806060a171002030f190203270703020d06020703020d0c03020309221a01030c1103070b 81
    0x4940556507045200c000d1011814217a03c1400443ca0a8803005414400d602c0b25036405074005040c00581000c00000b50040d10301903c250104103e0540090307002d128911110840e05000307174480c88680144200f220058201a0b2641e20400051050715080070681d5240356045407107400f65560054802002c0c011907200c51405186d801c403000000d0804005081078034001d403010013034196141c000c9990756005481c01e07908036400700018005803c2c0b00c95042e241014100441e0a0900281040300c120f0b4011520000f0703603007040c400d000081c41001c050751996800d07980150308600304150120603034829848018100131440c040e000c44010f05105140007182c000303241c2112641d081c282400a0340c0000021001402502480701116014a80c0d0b6482550180c3c011800c094101050000e0503021044003420112110188486d5110a00070201c040b00c09000e0980d040003002c1c005404d98201088040c1404003c400618514038000300b03503108281c01800000480d110b0f0744944503c4070780a07505 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 90902338 1250 90901088 90901093
    0x403150b03010f0c020111070b06090717090d0210020a0806010305091018120c0c03030507050106050a060203070611030618190203040f12020613060218030304142727 73
    0x7400d24060907640000484826034009212162450130350302c07007610450f0b000429441d041c0007c40c209040032020b66334403482509200a5180d1019460f8082030021911941700d64404112040c03420340c1440a03070300364103078200151b05001e008100540094001009541055a18400038582000c01c01602c0078000502804111040507047c10601d1420b14040581c1d82c921140001400b16105495000e103480d080301e0001589815aa003c031030320360000c401990599240c0302c007c186035841000d0700c8000d0140d80c0096a48589500d0b206043d9038580321043c02280302802002400e442e107988501102940902e61240f030350340c04c0e03000c000300c121055090481c00d10100820040000303607280c0e01d10450246503003c80107090410226038480c001c50b40281d41d5100290b001000824980203407290910400c0405808116070000c0791568105e94024100341055042581c81b82c02d00143c100440b1001e9116128004107c0c20394903080d6201501c80c881e00444040c5261108216080001541e0513600a = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 90903588 1250 90902338 90902351
    0x2090a030c1503051f180b1e010f0905030706030e01060b070b190902030d030209210601090b06040302150f040b03091e06060a0e13060e0f0d05040b0403150b0301 71
    0x2154051000c4400000b000b11340f81c0000b0946040080c0620030240c005031a0340d0100070b040205800b1105019403082e40b6040c3c8441c110703110390f40c0344608480c0b4041302020390706030440d0b28400181100f0190550405004800c0401d120503200454810161101800c01052042c0b0442c100750042916030301c40c0c5105440418008100204c5022860003004100c00c402d000410b014032060440c0d40d40c0c500250700d603010300442c0340346902a4002c0c226150000b404101340308800903400000700380c0005182c3d4503800c2400180695030241c820446400401e4910904240c215804a14010068486001c400a01068800320202c4520841c1c02519400c4550303522418011861a602c41e007001d0703211015100030f03d951000344800541507100e02002000182602c1c9403c06185103078074040c140000c1103031016612004240e0300e006010318040c0000040c4103600c1060051800e11140b40301a204000e01044100540400c0780256015a9005001001d918591400800041040a80d0190154203050b07 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 90904838 1250 90903588 90903599
    0x903060501090c0e060a0c0b04060207020603041a07020c0102070506030a06050613030302012720060a08150a0e040803270604020f1f0c02030a050a0f1a07050d02090a030c 75
    0x30041e45945207141c8414284c0c1e4000410030402c0d004122081000945d00141140070452508001c0e40150041000510304501500850040e9008550640d1111003a220419122440342c0b0358903070000c0144058049213880d100002d40b101c101348601441100c021001c11942250f03644400c0003424000d000c190750350580020045002241d100c281d02651074041031188041c0f0318661042002084030040d43c003101c082d680d034854448254070641400441d07090f400442c0d25610010107150b02b40c3c1e1a0107a0601d8007804020000c40908100d80c01021092810026070b2641ca07410307600075a21610041e100e9a03801c00d0000b0b901001c4c0c40f0070034050b501c011220900346010a43d603016034003e844060010203440188a40d00d0004075000c1c000100f16440121101c3c4107101c1c00344d49030310080c113a8288103510b46443c1e203800c82c0e0f0102035030100749070345c054030400c555052082070551950350060310a2404080242041c050b20050b42d20081d00000d81e400260346000708080519444045400941e441d034 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 90906088 1250 90904838 90904841
    0x2032a0607020a05010609140c1608040f08160311060c190f0b07020a0201021b0402120a050723040303030908070c0f080c01030209030a02040b060705010507171e0412090306050109 79
    0x742d2044c0d4895103080d501060b0540300b8002c80c4a4643d110f00510815120320311000210f60001040010b1041c9950352400041d51543c01040102540719964000a0600b09414100710080ca44012900358080003040000d1011144401d444000c884181d110040000c4060901903030311400f0240090044d0400c1c1008081c0c0c0c64182c1a07805040d42801980e202c4100ba80c4d9034070300d8000079001d6072014601c1800c0c04000381c0c1c1c0c4021418003a1000d801d0400c0142c03103404440040d0b6802d00d81941f10001c025405a101c21241c3c019091868080c0602c044910b00100c14030444c040541015219100300080c05840d100f2910320382e40c0021440985556240f00320310006a50013510414012085061060340c42030003552401c000050141580907856400c03c002082200c10641d007000091101d5400710702c0c2031180e548a607410340c0b580c94100740a10800c030103a0500030080031000000d105065198032208030b000c2d60140e4081c0c2c094200c1010484143c4180e6125440205440d08280004c070710400076 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 90907338 1250 90906088 90906103
    0x20102030a0e0f0a020907110703060f1410030b0c09090405060405060112050601181508070f09050c030411010e100905090106090303080c0a05091201051008030a02032a060702 77
    0x1ca6080201a008411482c0c440b1500d503048a4a42e02c20a494400f51038940c41940d084919400c20b0300c800c25110781480d090140c3c1c0e9000307481309a039407140c00d41c254840d4018180b40304140c0035141c3700d030b00d0540001d042c45427a500014203a5491071001130175061362501124003400c4010403400103407502e490310075030701d0008803002c4a990044400001c0d081503000c1041c00020707841000742c44a030b03003002950f4000641124040c0c1e5000c0d110398029403006000c1c065040500407142c00f51502c90704020520610789403503446010204e1800080201038050001903940080d44081c1410a442e81c003070040361440d80031003091354400384890010301c010341c2018110342100e80540351003d4580c2c1e145d00c180c0f4011046d2101502041c0c0c0407001030130701d40d4030000800440c0141d00f000c0e03051440400c0410754040c08411845807a81d0f6403024040c40c0711340e04242c41d00416100d0020752810003c001c4c002e480e805603d860500010143c040441010702005a45034003d00030b2084910710326000b1402940c9261 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 90908588 1250 90907338 90907351
    0xd051c091a1807180b0a030206030103054801031509060303110f033103110f04110a0f0905090a050105090f060f0607080c0706020304051813020906150a02010203 71
    0x999540e0741c1c6298001248200c100c480003020002c65200c4c40400704058040e40800c07541c0303c0440d02d40400169200000345000c0c1d8020401010420a042140c003041001c8290a008102e2415104c00c11041e4640601c2c158144001c0d80804a1035190700590241c2010070314050107940d041008241c555443c0d00001c100ca0003656641c058009803405151180898000c5007005c0e0820040c40c0c0070001040954200d0a01c15404441131701321004401d08040203e803c1112107040c241d001410760b141020005000d034000311006c00a102200f541e42220f48141c00c085c50a1117080d035410900203000c0c0c0d0384c1e0801010068014510740c076064000100426007401594451300d418000f140303a040040000500c19100544001c030081800d404201c2c0541116008071a40c0f902002074804199041c00300d04014942ca400039905d81d41007004200c03210030000c1c0103503515882c9200f000510b0009035150800c482e0150340b82d001c580c60b48404900040740c60804000400c00014400d0020359055000b144201d5 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 90909838 1250 90908588 90908611
    0x909010209012a1407030b0406020a0f020c09010e070e0409052d03030f0a021b0708070503120f030604060806010e24090a0b0f04180506090d051c091a 66
    0x2d0f6100b2080e000ca010350101218680b210b5145000051502c1c0c0241184c46000c00032a030b070b0f0964940d22046e00583c101c40c2151001e4012411280d80d541000c0307420640b0300140060300d000c080c108003080740d1200520545084100200200f001c45020f0764100701e4012001e0000e105004090501555888190024054031440d003450070301800407601c0c41e0f601c030b001900091451600c94100f2902542405070405900c45c0c1c1c20082d02d6008030446101caa58140403401405009180030701c00c0c0d0400700f86501450098203c81025000c880e41c0808a0b80401c5903042c0d401d8403a111400840d0040138240c111210302e10682001042e003003180e81c030240c841c1450b4101414540704011020584d004500c40c225000010080403d07240803d640081980203400303007854011011141c0080c0c1a2010440714449201801c0c00007010300400b486459405100d400062000d490200c81c020143c0c4921903d1020800b0802450700c424502d81c0c0000b02265000b80c4003148603285805e04c601110341c00e0b5001d002d2030 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 90911088 1250 90909838 90909857
    0x1e03160e06040203010b0409021e070605100b16060905030c0a0302070911090a03020f13050a0603140706140307090305100b0f01030c0e061303020405070206160c0209061e090901020901 81
    0x10b01c0d150007240c0c1a1680d0120040c1010315001200d000b9410000748103400c0e407000b0710034480745000c06002d031400c1d502400011800c0c0c03c0c10404403403401c1898100143c0712208100d241981211a00c50007500707580107074002036905442c01c043d421030140c02c0c00180c8a018401039081419800510041611302e0094200240401086100320511898900c142c001c0d494a008002519022101d292800b9010b4400481e8041c100441c0c401ca420456041d008140d03100d60038414480728403804030700802c6180c000c0800700e06100340a0044ca00002c4c030b41e002e42e000040050500d1307220f40080e10003036a21004030345c00609800211b902030054000c40d64003543c42da41d964840b640c4240078001a10425446210400c1c01101c14450a60301c10a01040c04940d991000001a00d8a01c81c0a104e00d040d40d014040c0340c02c20503d195018901c056003e0104412005207402580d111000580c000c681124a054103082e10011403170481207e4200d1548038070304808120042106400030016080242c0c1c503006d82 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 90912338 1250 90911088 90911101
    0x60906160c030807030f0e1c03060e0f0105060c030d0203040c14010302210702070308130306061707050603040618030e0406091a04240b040503120304020f1e03160e 72
    0x440314050160002e80c503200401c1d021400380c1d0010410081203c40401c1c1c81070180e003041d180140c0f00c0d0b4080841c80c48c500101c59819814403580015081d91007910840c4e0078501401d880a03503060043c58818440020640c2200030b08204540e5801319982b4159281d26081c1003403200e00c030b803074400c03040040f4003c1c00341c181540c424400c0303a03d40c00c2501e02800654000502a0b010000d0051448080d4402c907540070010841c00d1020745030fa0341c141030407001014154075080090394025841074920a441c411004802c40d404607a00e020358000307885d89900c0360f81d07a0801c20050001302c040d60b103180e005400e804091541c403046400c81100c080e83d06000665a400084d01180c941d21000203101c40007503145949413034a6085a420249810034011041c403060201c2082000180c4c4103592104c03000a0400007400c0c28400b0600402d4840e89950561800c4c3d004104003440348643e00b441850702c1030021105550500310508078100180850380000c90f030002002500d012406680300c60110300000911 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 90913588 1250 90912338 90912347
    0xb0c0702090105090f04170913240308070b07031103040302030901020c010518060706060915080708060f07030f15120c0e01080312040c080307150c0e01141b06090616 73
    0x245505000e404400e40e1b40303403100c001000c581090f40000c050100100030840e1f07035030203400417900c00120001456030074441005440c44070401540070b8502505604101048190b0140c030701068202454404940d20031030220002c2c00380c600d41d0801503030048148001e00d1340c00806088081020303000c0b1900b0306074400064405014842e8000d50103804444c040e5014100303a03018001180c03140e80c021800a84480526007a06c10900b03008155118142081054810410140b4020704039030340030780f41500b420124040a01c0d00142203606040c0c5481051031f0b200344603486000f54514082200303000d075460b4400c0303c18584190809440804079a4400f140588010a00340c0c100c0d05d1f070200861508030f8402c0320982c03100c4010015901903c42d140300103919038052004212203441010000042c030b441104000491300744c840500c1c100800c02c13010742d640313981010460302582c0c204c2e06181d44465141d40c408401c41000703000342456000d100c0500903d10000507185000d62074018901d05c408103120750456 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 90914838 1250 90913588 90913591
    0x605090114040b01060309080903010617070911190e040609050a140c03010504050402030f010515120d090603110405040609020304050f0a15050601030e06040b090601080d0203070b130b0c070209010509 88
    0x5003e080640b0040011500039808228181d200340002070919681c2c00000c1e084690543c0480080071154201600c11042803104c00050691400200510301c400049010140152440440880112039010702d2640c01008010a48140181b041c0080c1d0346076500900a4041a503640207480e082c88803010583c040078149078071401d81c060303c00341541c2c40c2008103c05081c000c0c0090f43c00d40548042d41100503000c2c052039120701c00140c83c030044000300605000300344840c1e89900200d0741205101c00d4996a10003611011907a4500e00801c501003084d21140043c41a9407040c0da215207004400240341d6640d8000e140306602900035280d040c3e440c41d070011307120810b404005107807aa5070012188280a6944000d82101d0107245c00520f00608080031032400d40b0070754003030f20516842010441c034903404005940c00742800e403014003110101c29130041d599004055004116440940c001192260913003140d124047d00016013440d01c1c2000800c00750150321140c41a40150103c1001158034144014500e = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 90916088 1250 90914838 90914843
    0x1b010507020114130302030f0102030702100c020a020d03030f020a020106031208010302090106030f110a021605011b0b040809060a090614030601090306020a0e04050a0204060305060a030807121407060509011404 92
    0x200c1c5240c4035407100300b64560044c600940da45103141004405600c0400c0400101101300000507524209124046e180846680c090b000c95410a0640c0b070a00ba404a180302805030305550710040b107082032506034003a2004032038030709a4034804144091010b5054000c94101c0340504011002e0b40c01c070210407100300800b404060341100041004104580c82a4171082d010000303400c002490305059200108560b110307031040070041c0e003c600e01c40701160001046d04001e03c6d003400c0100070256085c001ca54144202c600142c18103c0f02d80c00038003030140980489211020050003a80c0e01c0d150320502078000780160040600003401518401e50740b110050850307010b480d058441038507241c07850391384001a40c06240840d041000c6000c1a5550703403114000c041c0520000070015031624181500141180d03070060040748245403543d01040801d652001302c8071003a8000c0c03038044640307098901c02d4911000305103a07002c0f2240000749110a0003215809280a4000b010081c0a4174007000071101c240d80c2c003914003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 90917338 1250 90916088 90916097
    0x3030203030f0403110307030305011d15040e0102070b010e09071703090d0f0c230108010b12060a030804080601140103150b0c12030103111518011407020d051b0105070201 75
    0x3040881001601c550b034010311030b2a02c91001040785d81618199048a10304602080d1100010f20120160519100d560300907401d07c2a09841c05550141f03024400b0000725004982d2400100704424081d01194000340d08035000d040703296905d401102c0001d508840381c82c9280200000802c07074012102028403009545d80003035080c00012400c20a2020791303064102e17000641d40c250030001583c006a117000130602d044040702802c090a44010300740081c07000d05410400380f01c00500201c01c0d05d406852100f081c081c10071030b1968454020468500c030300c0d000a40700311804070340010008000540e140c1a180300700c038400c0c0c0115a4100640c15146071040060340062010014440c0706007203c00790145c000140101c1c0c1d540d4414401181c9564002c1e0000d490b414124000310003681800030710724a015120581c07252170074802203815000740b0012103000c1d042042c40700001c406658041d09840c50141c00402d00b05d952481481c01540d107a50f0f40040e890aa4002081c1c01030943c0904152000d080c0c040c2c40c1c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 90918588 1250 90917338 90917341
    0x4050c06030c0d0c030509010c02030703090b0702040212041401061a0313030e0d050f010501080a0c15090911090306071809050a020d0606051c0207020a05040507140d1409070303020303 81
    0x10805603420007003400e0003655040c010602c03000110b0150713820403c0c1946000a0604200c2c01103825545601d01e05e0055510400002c80001d6000f0021811507a070100d94036240ca2403840060080c0c491580070041d002c100c0c0080c0300900150710f41800941d21070f603000304000c82e95403548041c10040f54240c0e484120040c400a031340007881103061550f181c0700b8501491740250100004110706141c00058030720f544101c00741050058244543c6014041040041c02d06900030b03521a40c089100f401040c803480c1080140040041c060403a8002824484c1001e105840c102210884560400502d0364428420200400c080c80c0c0501104100100c40c40000480c0b941020400800780c0b41c050184c241d030990070016041031040718400d10014042e103584150707450035901c0c030080b0203100c407444805040e4030421100006a0b22001c0c14000c0301c40507100030030769945184082c0d46609401010301e03220240000c07140300440a991001c1a883c0e8060035081c810740b00c03003082550720041c45c000200961300400 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 90919838 1250 90918588 90918613
    0xb0a11060705090d030201090501050c07020a09061a070602070b0c0705010b040c0e0d02031c021606020601120303091a0c0c07090b0d0308040c080a050c090105040903080a020a110703150c05030405 86
    0x4c4100c100f10380640008111034015503a03090845d032044a81c2d9034150408940d0004501e00102048000e0101d41e000b40f0085080c01c5910304a06088500300f0558080018402c080184540540b0991500020491050310340408030a02c1680281011652946800e00c09032042c50706208108480081d07941c3e07040007a000406110200d072200c04140ea041c4150340038480450000e100c1e0240949a0b41c0c058080c01b24078002007550501c1c0b42c0c000c04195044000103120720000148140201da406142c01f00c0c91080d41e05003001d00c02c0d0381d959882c4851106a0402003071241d0000203128410304002100d40b960b0b600c14260003102d140d19903407030740320711547e0340c200100744240141c54010b4002d01c012444582c0d55111185000d8420a04031002c1c0c02c414060325079894068031080c0140b000791018031131041160382c02484d0f10700051102000302e17408503103010181d01c83d56801c4451040c1e0340c100c03141d0641b2820401c003d680086c10560a507030a000780800161712840c1544d000310b500c04000d288909598 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 90921088 1250 90919838 90919849
    0x807090b01170a050907030803090109120230040504020a0c0209060114070803040203010209030610050a0b0346090605070e03030d0c05090402070609050705060f09040e01150b0a1106070509 83
    0x43d0501017035110b58440400801d49400080d80204c0c461000012103407998a0641c1c12503903217248100c203541094040b81185090420012003a10300c01040701800e2035101552200b0b8060f070380046400600c007140e1181c816400201d1110500d0007103600c0d54156403160f00450740105801c0d0700304001207052040c440003481c2480079640280c4001d00150400214002283c600f0354111501c403c1e03083e90601c100300d0307070419061480c05040390300d590070310714500011107291100101c50442420000c5540201c2e4950000241c05211050354001000c0d088403120303840c0c040c1010310380a8403900e143c1808a8940ca003d140c28020a12018002d1801d103c08a000d010052510380146414802d081000c2420741c0c1d00c2c1e100414200703108402c0002c00f00450701380a4038007512904103078001c5404102c20148002c00341d064a0032100116000701d1202c058030001805091000740c611510115800c0216089104034090210390741d607075550044211401c00899940c0d0410364440300459000c00c1410011f0402 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 90922338 1250 90921088 90921091
    0x9011802011206050414011403010c3c02030d06140d1e0804030b04031e0801170309041a090a060e040b04140a121101020702030606280807090b01170a05 67
    0x210b003002070000d54402c0410140c1d003000d040f24090a00300310040c0b1925503400d1190301c1d10b5009500800c040c0810384005401c2500102041d080292600d411410040260003c080079135446d81e82d075100c0d2282c0c41c0c1c010b96203400c10642240b1842c10000042000c104a226a2141c000010700310080d040f5182c5898144800a0007842d45d240a6030b540070003c11710120041006503c2100e60300c00a26140c01d00418128980007908848510311001390316055100d0700c1141952902001d5007107521030504a6860b5115580b2070350b42107810501d0368020b131030501c40840d107207420030703036024800e9a145600399080315420700030030015024200c0400e011600b110b05441e4050700c20032a0748080b0044e084058074020b041c603030481d029418146644801c2c0e5006030214a0040440700039410300c403c1b0b5000a444100042070f450081031901c0d0380c81944c400410000803150300c4019850180c40c0c90b29181030301c0c2c000601800b40c07003d0070700039080940e52003060310324000d103210200c0315000d03229010700c540070303140 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 90923588 1250 90922338 90922367
    0x110301090c09150c0201030b030d0c0809130f06060f0c0c03120918050a0614060304060c020a0b04141912030f020c0d03060302040e060906010b07030513080a0303050901180201 77
    0x160101c082a080904a020860700440d900d84182d0a00517100040645205480c114000d410a6802480e05600310542c512825485103041c7d498051200100d10211710051144030f4140c10014155000f05141c0e0021003036a03101d030355440911082d40d40684008035a034400400c183c02444c0108003060300d80b60002224401898240b10180e070702c0203800f42a01c8410b101c0e94071503641d40c09103d07543c5980d104d003000500f030300c0b41640000d0000400060160000410241c1200d03190042e80300828401e00400d202d041d44503d1048041c1440d0034507103000b0403465a050b0491083e01010800c0c000303902e002d12099648504590190300340900c04802400c01c403d40c02c0740c0f40d5000d00603404211014841408110929580014203a10b18010042540c0c481c0703481540b950052024000361342c0d07000c5507050540d56200040f60351050145812101403041030300420600e403540c440441d449202040c042c03000c0707001382d5041c001621390030342d49402c0316008e60700c80401300802c0f1082c42c010f50080000104008 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 90924838 1250 90923588 90923597
    0xa050618070809070501030e030708130e1311010219030e0f040203010623040815070e100302040603150e0601120e0706020105041b06020303010b03041509030201020a030c03110301090c 81
    0x5612000001091509903800c0011807030450800043c0b510400064000785024030b403e00c422881110380303c4d103e10400300068942c80c0000386201e0005030040b5030744001c04030300e503001c020b03407904400d03200416842c56003c0700c4180410040788800d42c4001136a40c42c4003103884511100030b029a400b51440c01051035200d4010005980343c1c205540c45e84082e60003000b498940810644201180c0380c042e4140d400011030306602070109200c03075100000c0c5440010748a00d419209a111100301f40d0f140ca000705d441d160b100384a01540d44620754103801600031030306075403028403510140c06032010142c00180101c001c002c1c007603070001c1d00ca980715200700f507000b01c1c2d070741c0b800540601c40b88410742c10f1004075001100580e454405010030002604c04c6031958060b80d28012001c40e081003402916440103118520009130044013090a104e10000d6200c041420040100703c004920314000e40030750003800400300820300e41011680164024051009944040740416186038203003500400202601030300d010400 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 90926088 1250 90924838 90924859
    0x90916020c0306040b090d020604150c0504080a030e0a06031b050d11031e06062104020103020c03070c0e09010207020609040203090106030c1413020f090d0305091804020f12060a0506 80
    0x5841c103100c4540600d0240b43c4617040c03490030106041c50003504a03e00e404640c4004100b2010481042400d039a451500d41c01050601200030110b41a02417600a031500740a01e00844d4205a00108030008448c02a283d05c004d499680009804490424815110007030500c1c8102c00b1040c41130000303041c50a00203a00013420326a503080c1c0c8403240c1080312040c5000e1000f0304040c0b544404040ca00f548004c003111403a143c4261100100e9016070410140d0f01d910309990045811a800780d0151159007003050102d030744890303503401d04e86040070042c414030410080d000301040e180700060007102c1e64240c000d40158035041c41d000c20f000c004e5100038542c0d0515586c8100220014046050000050410b03100714a40e820f005410007510b00070341040a09090301c10044107011500c1c42e419107a00b40b1003241c4103810070145003001d072130070700c10400800d40c8050764030f2008841801c00344000e0301031802968940c5e4101c001350309108044000c0d20403407816920030800100c4043c848d400296204201074101c5524 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 90927338 1250 90926088 90926113
    0x601090b0708090f0d0201120e030702180a0608010612030c11040203010f0e0a0212180114010b0403060f090503040513020f0a0806011106010b040b0703030b03030c07170309091602 79
    0x8641090710122088036000034805501d10348415544c02c000c0c8222074180032404030b6400a050003030900d4845202d1a12647d6180d844c00081c0161031240c0d8010f000ca11980c0384d800b0348070450000403500010014904800070480c24014452081918002c101200a0300099101550301240c3c550742103c4400050000c001d090f255030000e14020722081c1900c902c543cbc240b140140b041e50000f0904880f41744180002c5801c0c4514603809030b000030000403030744011000410f059024110315100801284030a8000041403201400100101d900400040207000c0000500a083d0b420500c00900503900501040c00725250040f0180c80d5034418444c010714040d59100041c00a8200c0e0b050341c004503010302c04200041d42c000301c03501621682e00001e841e817507050040b074415a001e80d026445400d41e000c0381c1c000405000e0390141424201c02022a51203501c18046950307210b42c140217108510940358030010154600200740d40203504020a110f20366030340c0e42c144001312462004190110705c82c2c141c2d2481c2 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 90928588 1250 90927338 90927359
    0x71d030705031504120302090604030201030b030a060c0905030d1701050f0a0e0403020102031806060d061802120303040c0b03010807061d192c040f17030115080106080103110405060109 81
    0x3c0c212280c0401c5450b050502800081181d490380c814140100481c0f4500d41d100401c41d401d0300da0908000503099a17040c0820700d010301203840101840d2426840e191615086020314003164011002c0795100d00090f40c2c211454821580c1d400052551074005001600d48500c100e0541c42010b441e11400d5580c400c0500304922098809501503503002041c4514001108240c80e10215a000144101c3c184100841e103410414007002d4400d61744c031000380345100002c0702010017140e001040014030203080e07414540c8903402501c04481003002c400e400210302c118041500d040740c02e41009800340b50700e880019500c06408190052110383c000d403010841395100c44042000869105030b200c222800c002d41d410031040005c2d20180d14100f01c40c0d406512052010340603500035440042180d0100c071514209070b540c41500000043c075080440042018100881d03c010002d04980c0ca5007056641e98000381c41c043d0b8203000251007a28407038820480d03404d01744c200903007020040c5000798606a6443c200b55 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 90929838 1250 90928588 90928603
    0x3020f01021912020c120a1104060b04090b090609060913050a0804120c0801020c07050d0c0b030c0d06050108060a0603020703021c030b0102060a0b0d1b03060207030e040e06071d03070503 82
    0x19520003035480c45030f510b035604218a80c00c0510645038410303a09144503d82d47d450560440081100d407200e901524141c440340c00c044010494403510980b2a51285101c1e0b0146c0390720030f003450260030b4940000b08180b600041d44c03806010064500c8059484101e0b100e1070a030300c000c100391240e210303441030322001444220082c4000d0480300740b0b20f41d42500c0ea01d00889105d0f105d910440082e80103201111003214041949001c45038222401740c140d000b10719201e9549426230b48000700140d0080204444040810001c0c0008803030824100811601c400055607251400e54840350081c0e40b41c1d07000c1c000c140c001e900902580c3d000e40115a121004615650448150300d551100000d864240e2000c1c1560100281034100081c00010b01190040002040ca4000944800f41c032040c41703c0241440e1000840030400610f0308a90150341e61030040c1400703444440c1d0b00511501803490032010000300b610106110740030f444256126261801d0403252034804090051526501d030098001c00a1341d5036040000030b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 90931088 1250 90929838 90929843
    0x415110a0c1109010b0313020a0302030105070818011119030b040e0309040f050903090103020f07080d1b02030a0206150103062408130804061412090c030706020307080403020f010219 80
    0x76440c042540c40c05800d1031102e59482402422440c0041c410581a4401d6982c00303608546403260301c1d9410b00002c0e600f0040c50744080d405500c0e10b0140040264001d404600c28203a00c80403442e0702503c111000c0c01c8422007400c641000b1030a00c2507118282c415005d0030234641c054034000c5401d044680000d0100e0301d44403550b07042035000113003021441c2014090880e820041d81d50422042c600100b406840c3d00c85c041e0418101035000640400009012042d1414907400040d2203031106001003404008001e003043d01c0071854201640d10782c0c250b01c004204c502100050707010b00340f152034800078a0096107040c1c100905250701d515000c20b000c040e40f0121488145007080c001c90300d10a0010140c2100350151960303010034864031380f40b008215500212000c8844514128488450750051201d540c001e5143d15200501902c043c030002c85c2c000510103060394812401d03244c4803951039006a0750b070301ca41c04001309040c00c18401000545401031104001900c180141c861004d21180e45074240e0b280700e03404 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 90932338 1250 90931088 90931097
    0x9120705030607050a090e0405070e010f080114010302030a03080402040609180c0501030606020a03080907090e031309051e090a0b040507031703060a090507020715030609230415110a 80
    0x204150300d000c0100355003018040c2045407070a00b0710030000b082c21b0158014084607000c200e01040800500300304030801802e41d08030303100f500e50b141d900c0300c3c0c000ba40074400c1041c107600b00142d203184040da4004c0706048940c000d0050200000380d9406494402d40100140d03441030340c1301c20008490b00540a513441c2c29046000e0341c807a1710f1241c0381210611040c0c2c1c20031410140751034030070f000031600004c00030b50b15501428030f4002070b03940c030100d20302d001030541049000f00d003000001003107842c001000c0c004501c1240b0314800000c0d202d26031002103850403582800c920549600030b210b41c044110384107410041d000b0941b120b400040e26000e944100a450030ad07400d60024508009201d4400d8034402007040b0807c000b1b00e50308044000444500f240d008010100c3c0d0340b07002048041c0d000300038503001080c880704120380405883c4d50160003402203202e1120580e0070890100300d00304104104c8110340014104c8030183c2d40329030300e9900200b03400045804055a03927101100e001d55038000501514002a501c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 90933588 1250 90932338 90932353
    0x5030607050703030609020f03071b020a0312080906071b0c03080a08040b130f02010e0420180108010b07030f0207090911041404030804120e040203090f060123150912 73
    0x30000c040b244940d01041c0070031f03c14000e0300711100d0341d90304407a0402001c2c0b0b0b00c074540820b2542494414040c28000a51110006200200300100c0a141d60018042034440c0005c41d9140170f011034031180c0856241d0001041c0f040040c01c40c54414406031a400d004074032252041e03407242d0303406409174410740e041c0020a100d002000304202055461aa112b854100c0b02c6c0c0703049405503110503859400e254000e041c09188900ea48480d245d5500c411814282684100d100c0145c13150341c080e6541c40600c00081d90060103000c1000c03940150805412503401d450003520b0001c450300c0849540d00c840780c1020460266200c000303040e050718010360000d54014101003e001a407a0100f10031220001040e00e00c1016150400c0046600024040d62050b0400711000300c815084508660306030702ca0101552143c03002c014071542420003d4a801e0004202d070032500aa40c076007501c6843c07444440240c20861130311002c03400701070070842044043c4c44c009611700ca0408510740002800481d4110101c19154440c14 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 90934838 1250 90933588 90933593
    0xc0102030c03180703030e01050904140f06091302090103020607080405030f030901020d0f210b1909050105120d05090109051e010e090112080c10020c0d0e09010b090415050306070507 80
    0x400341006803c041004100b541d1550b41c1c0903050031500046a41440070200b80d040c0e0741d443d650400130b5280503060040390b04e8034045a2607c80c0c0201607904901910b1034100042c1c509143d60b07055190284c00900c418070310fa18541c200903031580105404c84106000348000119a1010004008102007002c045c41d213941c0900e0009242c0a141c078400d200f0001164001510746400c403840c0d10101140c800484d056a0100e00428003078108400c000e50007480d03400d000702040d103510307009409440a08606000d140d07612070400210406441c5050069088409000c020340c0c043d4004154141d01810244905a80d4800042d01800c00030400e08856000e040e058100d0341c2d0000c1d01a120340030858005280f0f5051001d000355561a803900140f448038001000420b60320204054010644418019907442a0391050242c079000d0790302d03032070000c624043c6001501d4542140b1060607180c204442a04050070322013000080c0c030160034910300f80301d002840032801d52414040640300741299101c007541c40c0007a1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 90936088 1250 90934838 90934861
    0x25030908060c030c0d02070f051207060b06040e0606071e03050403060b0a031509020319111003090f0230070618050a141201050112110f03070303140c0102030c03 71
    0x40600b9010041001000041910201503c04000a0b0080141c0350300d81071800c03041034404210060104e100340ca40702a81c0034071241c010040c0600c9170000340103039129201400498001d901600e690700b1404800503910f41022405800685e0089402c0c011500c0b42e00d1704041c00e4800400103400051002a0900900405015103e4900341c10303904200600d180d611200120002181c400c52680e40350901c81095640400442010005a1101e900c0c03044161600312800070880d07445600031070a52521014080c0203200300039603550842c0300615840000d500300701260354010075001726215003006254014000a062600b484c1281e0300520703400e42000400351450f0b10702d5080403200d2400007001e01aa840d04010001210200c000c8802240c0d4824005041003c0c2c1d0340a05444d0741c0717004000107174070880001030310080b406420403568010120081c0804955600340c6036825502880c01040001c1c0b007468a440d10112102490b4182042c8161030303804d90780196449120102c0210600412a0f0304 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 90937338 1250 90936088 90936091
    0x3020d02060d231302010905151e040302090603030f0301030605060a08010c030e07080d200a020d03020606040c050f0304020907020c0414010e0f04050714030c060d14091f022503090806 81
    0x142e1050700310056181e0000301f18241501485019100c0d003002c101c40c0841070707802c0e118800860601d00f0700d4142c286458000caa00184070981c0300300520340104600d4140481161485000aa00607196a0031074950001600f0060304d4107800c05600c030f0000410160038030628a601c2000c1da00414403405244946103041003035003025010760440c46c2d1849007650881c0c4c0c101159031110410400c21b2540d24211400c10070545006500140003d80c442c040560109903c0e00c01d034070813a070811000e8401c1c201111303a8000d044225800a8080020602600d0314085c0164071030b10610442d07240c00c5443c0041026101c070081c0c00c40c1c0801c0020014090050070382d408941c40740702175401000714900342e25140d40d1124248202100c0120240e00d40380c581d2020b00180e11900c1000c1c005641d2408509020b40c0106aaa0f0400c401c0341a0000410030380307003000c59142d03180c00c4002401c29800184141650081d441303140010111840444040c82c4c01b440c5902120000d030103502d6120003185072821a50a0120 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 90938588 1250 90937338 90937351
    0x90504061a060702090a0902030a030503070212090a030b040f060e01090209090d08130c050409030519181a0403060e0604050f060714030c0714250305030403020d02060d23 75
    0x14044446a0a601c0d6881070b00c0d03003a80c04940481c45c076290090402e0042c80000350113501401001e00c2c00050507001801180100c0941d03007202c030182c8980d010050280640100070f544100313010001c1020818000406420074018a04180d403540b0b43d65600b800c0312032003c50076080d651103124403019450400e40b403541c820080740282911010000d001450480300528130164400c200002c42d00f8001801802c42c041c2001400412000586080180698100241244101241d004c03002c0c6414400e80080d105410b00d061a10030842c1469000a0401d0070540d01190540c0103100000100c0d8150060f8141003603840d02502031303420681001030030807101400801941c0d2082e8184840603901c00c3c681c00610050201c0c258036602c8040b4291040d101d1004060120440c0000d00011000c0114040300c01810300070302e40a15000600b50388114082e10f210140c201d41044c0000c1001d82800303a40c03281c84a200400349403a001e1080d248004031403020001c0b01d120500300c6144070702e00c440d100010341c1145 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 90939838 1250 90938588 90938621
    0x1401030b09060a030209040f050a0b0a060b09180703020706060b0301050f0109080303041e0f0c0509090a11040b0301020f0703050304020f040605060a030b030304120503210106050a0509031609050406 87
    0x7502c003000c120501928030009001d0040000000c0501601512451010b41d000080e03d10307025840c14030b040044815510310f07603c640742c0320002880326040c504892845070050103003510399402401d546000000108a4018103800300720100009142e03100d00400340c540a21110345a50629081c000380480310040e45060068451091001c0003002050320340c03017644120103814816685220000c6125400c200518201c0c034241100104004034109100b80d0390705a4490001d6a174852415030350b0030084c60080c1c80d21320285400c4005082c650060040078402a00143c07510f040da244c0354400368008242600000c0b030110502045151010204000110484041c0880e600340400a02984101d80440d401d03d540e41c8100c00c05a03c06105a4ac0100340c105210844048603041250f100d52150528441c80106900030201500005602c02d050301c80310755815041c40022841a1110384c0185001a498801c0350f0980903014a9884080083c25140c1800300300741c00d081c41c0050a454010b07804c0c007000c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 90941088 1250 90939838 90939841
    0x80a0b01090e120d0902010e0901080a03020d02010c0507060510170d03050705040e010e060a05030d1d1906080c0c031902010e010e120708040306020a030e070e070c0314090301061401030b09 83
    0x710380e040a0707900182201328000340300310752840140c0b650002d4100664001139074100000e100c99000c54000840c50003a000d840020241a00490807036480c4441c00001c59804d100c02c0c00410760580c03180d40c0c04443c2e41d0600800c41e40b100e84289041e000303609403981603030100c12440212545409180d0304400303a814070fa81018100b5014000d0f41905000c0c50380e07000340c1d440002d901a40c40d25208002482301030103883c00c00641c2c030f600520003003005000c3c0c1c66410760b894441c0442c1c240307946501d911442089450355618105a4100d5030101c0107400d03031480d4a41407146210b600e00900081044140c4403400707410342490400c0c017a081d240040c1c508145a450604441d2001d80d002c1542c1508030001000140c1d10505403400c50914000c540006d818248041425100300740c155010342c09440c2c1440072910060340d200c20302e000c42e100440c0c255002400140385480024003829003005200c61003c2401d0510580c034003c03e0031221194400c01c0e0b9504010029081540c252207503607260541510421610b = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 90942338 1250 90941088 90941113
    0x1b0b01031a0613020c2a041107020f060f070b01060f0801060c0317060310020c0102030709080706050f09060d05130c0605040b160302010213060503010f050609010807030c0306080a0b01090e 83
    0x503d08041d40c92001e01303800260b00040303600700f800350300c2d1450880c152100b05210348403440d80082825010081c020b5240107607003a0030f10580e40c20750b00e1072a0300901c2540301010031003e104147e0400c032444130614201b4010440098201c0352600d01801d1650b46119000101c2c0c1002050076806a0001007031008906003000840c0c0d1204071340c80085c00c1d44001e04c16a0305c0e41000b103480d00394907904441d0410b00c041074018030320324103400850042135180d07203800b21651140201c0307440b088a8450300c0c0120360304010807040c640030840078010310180100604d043c144010940c9d8141c0314121140010008028494001c008490300480050070f02407400c542800e040108111007889282c18851001c2c9400c55032004243c030035011203e903030080c0110b04040c65510400a012034000780114074007800d09038004201402e0420544140900581d14182c00381c613280c1080c0c0082060384c60240401d5210880131400a40800907002c90521500c22446a503151a0700a012a16601c41c0000c0c260050668040d0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 90943588 1250 90942338 90942349
    0xe06031e0c09010f030506010504080d02060105041b02070e0406110c01020a080a200c03070501020a12060603021903020c1c05090f030a03050406050c0c09040c0806060d0804151b0b01031a06 83
    0x4460151700f40018103072103520050740c40b80150303800b00701039210348a215002d5940c04030b241412594181c4081c4182101610046011b440d40c102000060340039590400025041c00b4000e900f00e030084100241c46901c1c200000e0040c2e03c15208a05280c0d00002d0b40488c85901503502980319140240c20007140b1440c0038264241c01400d040303810054404914080016814000ca41a29500000071076641140040c040c104042c44c84180c0c5460303140c0580050600e00078000c90300900603042100368070600220b003c8d4000e40181d0000350f610300c54482c0c03e00d801c41c0e860f03096030520f50380c40c0c54864460701100d04020422000b441030700c1c0203400031580c59000a4110b420740381521745500b45144c41e003650780901c910b0154109410780d88107528000340418441100040c80035507205005444842e55078009012011ba07480070000d018000400003000007864421000c104d0912a2030a60f100c10341d030000d80a10041d240d141030b60b5044544004204102e0401e24600404249030082811450070400048 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 90944838 1250 90943588 90943607
    0xa0b0603070c020301181109130305090d050c0a060201051005060715051819120203030603060402010f03020903012301050319030f111603030201060812040b07030e06031e0c0901 78
    0x141072140341e881c84021940c00303410116041d00c582c2c1080c0112481420488034042c041401c1234012032590011030115a070300071034048499016120300c2d00c0c0120305402d01600344407010040d5074a000d990300d45080c50380d41410728002041c940c2d0000c2500d04181c0020b106c07a00203640320902c10360381005420002000482c400c1c485100390180094581da98a880125902c0350414060720350040c1059440c0b40a144412803150901991510901c150f000074140d0740c0344000d48a840e85940103000040c015885001541c40900440ca0007509011103640801d007520b9510b0010940e01c108460b03192514102003c0031801008103c0052482110b1907080f45624400850040c081203150010303100500d00036102040103500000c00c45040158007004c081801100740400c8005500305940003a0000000a0301040b050300007070010319040c42d092a00380d85c0d9002c0c0e2404c40230301203800000b030220307035445000e107104110790011784075031201d81c0502c5041440e0003050f5004208040c04103550b240da0000c0d104 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 90946088 1250 90944838 90944851
    0x70504020901030204030c0b0304050d2607110f06041b0303080121081b0706020c01020309010c1b23010201020a08040b0a0908180a0e252303010e0a0b0603 68
    0x50341d4072420700048029100e140c0000c5d08214141c00c000900c08426030045100364040d4050f12151030b070640c0122840344003283c0c401058440391048080a008031128150040d001e4240400e400385166107081c103003c0307504400e01c2107070803003c200400d00030f130803048175100ca9000e000d02c03407403500b151740203403608406000da5480c1c0c0c6060b01c841e6917203101c80c80d8000c0c40740fa0481c00c0a43c958000c2440d001072144054648680c500481d00700142850001882c0c000c00324051b0059410090b03083c0c01100c60072003062058400c8041000d400d082e000300c036001c400140c00d00c2c0e80040b800b800c440340ea452450900701c0301281103a104200c29289590300c40c2e1035503041688606883d002e40c49000f001d2018040c0e1301c202506d1500005100f101814884c2003180c0c262a00750307405034215035034055403a01580704543c0482600843c0080031241d5024402070100d4500c503040400c11410540002040c1d030080518119064900100502ca2450070100041d4007140b9044144550451000400d45c40c0c0400307401c1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 90947338 1250 90946088 90946091
    0x908121909050301022a070303020709021c0501030803070206010e070801030633050a0812030a020c070f03050d09080f210d0906060905071805010c020d02060705061008010608070504 80
    0x3a422651260414000618000b0000c0d91191028203d10f040030100090081951900c455088010000071a0b900101c1e074041e009054241d141100c07400182d400540340e00c401c8020542e0507000d400136440703500e010398000e2146680380c1c82d00b410064600704041c0c0040c1304540b140c0c0100800180e0020b4500c0c19280d01c0030340861031035900f0a030707070301600740c40785000800400b0342900450a41c01c1c03451050403180701302d03016040d4a83d00c2e4585901d45031280c4110052407010400140c181c42aa00284000304103601140c0c0380719560844812443e41d1508111703034a40040c010b000c400744d80446010060b064182c09080707054424041c0c242c2e2000417900310b650301010306a040380608850001c2d00c503001c4090f00b00340324091a900e41000140124000d103c1518508008110b2140c4190000c110401c04504503d0443e400c14005448000a8050890748900940d07407460051311942c0c0501a8244180000c01c502e09103007010400040143d0800c80107030b07141010402000380001540c404590b02940c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 90948588 1250 90947338 90947377
    0xc060712050a0507060507080a0b06311d0a0515010219030315060309060c02070e150a0909060b100203090303040e060f0d08040e0114090c03130c06020d090812 70
    0x802c0d035a030b01600344064080d510300801c20447d150804c1d2514891000401e04011a1080004104440c00b0380c1c4034201c000c0c404400f15546400903c07810014820890024100c03960b55500f60100c440c0c40180007810345008101070103202c0d905402080d41000340d03990001c641c4044640003d54075242800e00b041090721000f2040e0a240c002e500c90b14040d010120955122626140c0103009011300342c4044419070701e042194080c0c02c0c4086821800d540b5095540c49441c0c0351150303500040b20462241ca540014800d80004081a292003080710440c440c05000c40e03222212400c1029215080c6610001c0d034208002104403640c1c04001c0700c0544035030103c007801a40f540004a011040303118074490308a040514443c003408101d0002d0002c81c1c20f1042111081d80e200c188461001105401c0f42d60809a84008140444030000155034004080c207c12081260319484661060300c640c0d010102580003145941c1b901d5500c104480b01030312103000101043c1941c42c01c0c00c0d100c7d1041e03d4449800070700455 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 90949838 1250 90948588 90948607
    0x20906270702070614090102060402011101021903091506050603070c0615091e020403020d031416080306030f0109020319170c0309010906030902180a020403080408010606020c06071205 81
    0x1009100600030600203042880c01000196450890703026620116080303450036100303042c0f1507040b1800108182e01402d11903c5550056440d14120000d9081c2950240710100035150701898000138200340b40c0d00482d01c1c0035282064248111981c80040305642001700511aa449060072690407190f2480d004d4615002401e2640040400741101c1414244004d00054895020341001d0800783c80400401000c0c03100303500d140103d00c1240301c001d4001c295684000d0101e405045a0510829000c0005103480ca01000524506001803800c6800300004004d01080f402e04016001c02d02c22418020014201d45400080e0742d086210340050700b80d01c08001c250100501e84040c8003c034090084065140e418030b540051b01c0b608410181400110300c00c0700000d816110380210314285801400b1144143d00c82d82d0410160080107000c0f04040341c00304000000594014000c00041086800010303046040640c020306000e005a20300c0d02c40c860900c00f101c04104141000007120240303003002d9a80e1003c07003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 90951088 1250 90949838 90949879
    0x60303040b1206030d1b0b0c041206091704030c030609061d0304141008070e190603090501240603050603010902060d15080106080706030b120706020d1b020906 70
    0x41d0072440e09200085446200c0380c40192885016000031070517191140090714049030051460045a8864038200b9188008104601851508080103041c80761515840c3d1080000b4914203040c12240035590b0f5412105002403690182040c040317440c40145081e145407645402e004080c040500516510b01c0c2c41c10401c0000c0d030102c814141452090600c3e45420361321181c80350494400e00400e0320000c0c1401e00149850360300150003400c1da0b01e03000c406031142c500803200844458889504011581b1a002840413015202d41c002c10a581c0c000c00d56903100c2c902142500c034083e20f00041000004800165203021a202a040d10030f5490000b400e5038500e00064050445079401a4000c0c400040f5002088415044a5240704072143c00318013056607690f0090807034050f44501d844540084800740f003158031036004504c1e203150040c204100b44180212007420b04529512400240c4d2101d0318274a0020741008140400441c28400000703040c0700c80c0c0210301818002444584680b036004050704110905 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 90952338 1250 90951088 90951097
    0x9040e01050709090e03040302090c0a0e22060506040605070305130b030c030703140c180315070504060810031113021603050307020f16050d02030709111b010b010f08060303 76
    0x2500000e1065040c00c8401508224950141e940b000e030400710b5500c0125000400c8034102d07a40940554410764544000521a400c8100c0040400c80b40103256440c40d070300c160441031007840d00000c10019840080280080312415800140104001c0c081000b0040c4c21005035031481e45c25040560fa0350115643d02c89481d005900701d00b00d40440030042c4610311000502940c4906900d4404102800001070403c0081c1d00840741028006800c2191050542d8869100340745004c0140c12151034040844140014000c1210b81c40300003003003c9020820154000c804c650001500c0e0082e00700c16003161200c44051014026050040020816011400322142d0440701d804d001d210140003a40001d01d002407403a03105440d4079006100b000c1c003840c4c5000011506034a84452110f107250914601002c1c4040045407200a90785805884e00000b00c06203d401404501091030910654408403580205202404402d41981176032401000c40c000b80d07082000d80c0025244c07418600300070341c0c482c5d0009203188107 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 90953588 1250 90952338 90952361
    0xa0615090906060311030c0d11060715020d0c0c0515070c080a18050406240309140a151a2404060210060803030408040e060102070e010305030c0601090c090b0904 71
    0x14106181041c802d00d540b2000c20307a4815000728112007000c10400d5035440b1032400e5180d00c0f0311101c06036000102c40ea840d542c601500a407403030b4101185615015400d00c12a50320f041a030ba000503100041440c58442e805c06681c05003415a410011a20740035541d4041c884802c202c420800041003480d4005c1141684c4c040d400f00100f6601e102e0703044000c1c00c1005085504110200d19507011a01c1d181a002c2c9206662035240d1820207100281650000e0f06038070380c800c0c414180e4805d21840822030348030f141e842175480200140140c600603e0314a080c45102c90f04207110301d14000c803003071005002480040c2080f504075000d8041c041e0b0b00c40d501801d441c4400441681c1a400500040c90301c1c3c0200f200030424019a00c00c01c042ca64a0300d0a684178441244d00520b04082080144064000903480c17540044e81071049902c515194a80c41c106c40200381c009076015800030075040c020107002c00203103000d045944024054ae102d2003001400011381c1d0300070714001400202e490403181c0c4030795001421411 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 90954838 1250 90953588 90953591
    0x5070207150f0201060b030c0f070206040509041a06030a0c0e1810060801180201090509040804050a030602090405070906080106050f0705060a0905160501050d020f090315061206090a061509 83
    0x488040103000742072240d00a4025500b1700c4800200310030351809580c442c600c000710151400c5000802481c80350703c040c1c4120303803242061001184030b444400031144294425410010030851400c0514407080005000fa4842e501071074100700007981160038035041f6000520000301e591100c03000fa003008030111406c00b42074412203860b0040811150400c1c003c443d4814002c221181c0c4481140880c1d011843d4007a0100720f0603d4100540d040c555050303507005008401d8582841e84400002d0031403140c0c0d038020f480d0282c0104441c08503107007510070241c01400c0350420f2000b15180c407502400300101403041d90140440850002081201c08c0c080b42e00d10b40c1e002090350300615000e07800f8402428048000e4495100300e40c5200b468a10302c8507071409891058407014101040182044080c1d803002903007507040f80d024081c00e0a1a142000000444240d4019106d020701d030040510003031503107d0f480905140c0c404810700808a02c003288002055410000c08218000e503460345a050701748960252009a = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 90956088 1250 90954838 90954869
    0x2010309050d0f090b040f03080a0c0c06030b04141504020307020c030109050d0923040504031403040b01030201030b040605061e0915030106080708151905100305060a08070b0d05070207 81
    0x49600000f924915a030310384a005100e900c07070130349207601d0085005014800e0140001840850185d00c081c166010861400624002103a900e601c1841d010380c0c4100046034481c15201958541802680c6100e03d030001d8141061911509078841c14003001d00b01405168004040b0708414400e000007801e07444007400910000798180703040769941c2002c590320320010720740f6a8041441600d240c1c280da032400300f0301e240000c4480c0d008100001000d001d48124188145e15045c1903102c03c0301c0e070103580b00d9405007100c4901585140000b50030b4648451040384150700d014418011546c4102c2036403141202c0822401d98001c031642d000c09984604000d1a6100156603041c521044440c4010f5058802e6683c0303000d00c503140c1800954080100390b41e560003901d4521415241814009504106000040801103149030398402003494050b10038003400003e502c910400c1071604000c0e0243d402000040c0041a50385d01d00410560300c0d000c2d040d0134450807a29a00800c00f4244208062800351014440d940010b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 90957338 1250 90956088 90956113
    0xf07080301030b0105010305042640080304090504150e0d0f1e080601200d0e09040b07210c0302190e010504050402130e09010b090a020403030512040201030905 70
    0x190002d11044031402c0d41e4000201e070551103400f9403405183d100582e04141c80c0a2117004009420011800e01c100c48240145d4110001c01100c000342e40c500f001413104050311024400445c207211580c0304000c0c01401d001048840c1000080754115401000c0001e02030316075103090b8200e0512003000440d128180503c8005142c40480d05074100b05850b101e041e02c0342150710007555003c1001c3d40480c0001031182d10724151030b00540e0180d0703000c00145000c00b0402030001e40889640042c0c0503511546c4d1080210828864114410f40a20503003200c03017010307902d0180d441602a480080c451030410031034004019203901d140090a0100d600c4c0034060040d0b0500c81c0c40100213400001400709046050105030039198010804521100c406a603158580b905013014407000e0f5000400c00c0121500d40700b000540300c4080e0070b800303010307440c40c4002003184c180e1101000050580940200040340c410041000040d402604480d031841030340040701d400d0380d41e50005900501110b035014040340540744180c0c01 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 90958588 1250 90957338 90957353
    0x319030201140f06090403140c0607020c03070902120a090503070c03050a0201080109090309061103070b01030f030305011e092a1e0c02090a1a0303070804030b06040c050702040c050f07 81
    0x8008070101109030141e903240f032034080e00c030000c0d07450b1504080701c140820b0110b8451708514841c9034015040301d01c0c0c201c2c40c2404034640341040307855000507080406207540a00d401d100610003070100383c8040d4204074841c1c040e08a140000f504044c80307103980700700c9402040001e000307039014682c00902c103004039035981c100903072154610041240014040d00010551000c90310418141607059901d106815042c114269104032240f4a20302c214407003409031200240c01c582a880c0694881d003003080c4602c00d2898050244c920680008044100e80035104100b10a01e990810481702c60b280b01040080c0c0d40c0c640100115072030035002003203001c100942c2c0d942e190803096060030140e481e04144845181d000c0704440614064134001c1d845134055000c502d001115402c0b141c000c42c100c001c5512802409070009140d9400f47d00d0442e0441800314040081c0300b0041c0c81503502190a9405200404040c41c0017405881000d07002846a03988602c1004130500c500151a1443d452840b480e036104040c2c01c2c983c8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 90959838 1250 90958588 90958601
    0x20a170307031b0828110702030c01170c09060f030115110102030603031209010b030109120201050a05040f03050304110a0906030b060303090a0b0c1c03020403061404050d0e0319030201 81
    0x2003400d01030302403e02d508124900700c80030716a84d02d032000c0d501c0f81c107000d03030201d20b004a1034020110070708019640b81010303104002c0803040c039074121036840480d44145410010008a41418400302a14030143d800316207103201c1d441405000c41070398841c10007001824a00035a02d9141441c01e01000210b003460308880c01800d450059150070030109207601d040d500740d00c001c58006406070802d000c1c4541500c94400d100750041c20020020138080040d001007170842d44450015115100c0f20004130a203540c082c484c82d0381219040c5c0c0d0510003450162220782d1021a01d000040c00c2180000008090020b50708200000348001007120040e00c0e500c1c600034001c0c1ca004e00044d18182400b4000c030304945000012030b44802d6000d0440760001d40f42c9000300003d40c0200602c010139010300c0c19101d00d1101a113800d00c501ea601c41d18010707282c609508041003180c0074000600c1084c40c01b4818840401c000003000b0000356550700d802d1000c90000c0f80401d05081c40039074040311070203007075681c641010703010b40008 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 90961088 1250 90959838 90959851
    0x271f0c0f08271914010203041d0402120604110105091305010803030712050f0105010c0804031a0f010504090f14121b0c03070303051c02041706090106050f0f0907020a1703 75
    0x201100c00702d040c100b00c00d403002a41c4511500400c403c007040381000f2050a4103403040140180c034141942e030000d000c1c00702c00d121004522050710701d081004520301281000300d4050004e000308075510b400d55808010300c4000d4000e80c103000c0081000c414540d02d501959924a242d40300c03e101d25691191071650703a400070b0300c0400c04a0040c20701d000c0070f80346510038180b01c1c0d20344c10342c10049a4039240045d20840ba03242d10982d05900c04110201c04140304032154072a0004e180c450390201d242030510030f4080740b0181c0040744203500f03101150011520b4401c00fa0445504541c00ea850030310040381080c50700c0a0050319400100380441c440054103941508400903071044020303030700b284104108040c4c03680101d000041c0829818804151004542c036055101d01040000c0145481d0302c45d03000481480222481c81d84aa200e0741c10804031032000e01404000b440b040d2450384201ea50400050395806e41c4a003c18082e2000f500010150340c070030000d07246565003100050821050819a00c40c59500480d0b41 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 90962338 1250 90961088 90961147
    0x5061c0f050a050a0c02061f080f030d0f0b030d1110060b0d0507080606030a090305090901030501090c06030216020d0606030602130603061a0403150e03271f0c0f08 72
    0x1340710607207600400030a04d1284c2d000e40040ea460b880840310032680440c191000f42c45854002c01c1c40e030000c1203219403040900c802140c5818051440d0030640d0780d00f00318100401d04005005015880000304015910780350b0811003180141c10f03800074a0401451103d80585040c00e07000551080090010060b0600c902001d001a96032940f040e41ca00000740c40c05038103c401000055104030656110f020301030320900c1c0c8984ac190741240004d4283c90283c20955407650b5441d80d02c0d04010a10910100501050805600b0814003170b110b008400b00c0080045c1c0030b003028507906000c101041d8800009554806011511410b40340c05480d02005540a04000b0900d0b005010660b8260503010001c1d00a54901540c50103086640301c00201c805000b07200300070340e00d41c0144840d881080c070152803a00300300d0752151083d492550031505040703200107002c1e01407180d41e002440103044021020720550b5a03030a008044070240d107070020b02c401030300d032000d40b42040c0454070f030441040300302080d03100b0400c2e10342 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 90963588 1250 90962338 90962341
    0x60714120d0609060621020c0601171b06090d0f02030307061d0714060a1106160f080103021f090306060b09010e03011a0f0f09040b0a20030105061c0f050a05 69
    0xf1440110340c16800307105e01141c04040301640c105143d01030f124140d000003a016050240c0812100d1405100b0b0b0051000d031111750382c0500000c2c204000c403100d51100309890004000d4484007040e098802c4404241c000d49010f0b00b9401444082d0110090031940a01125a96482d5080c0703c0d00600151081d50f450314101011600c0c0c1b100c00048540c142e038000007005100021210402034191300200a6200384044180ca14503448400c0c4112032150520000682910a81c014000c0c50791f201805501d06202c4950014801360721941120032840b0200030f500d1301c01448084050354041510740c402040c25050400114903141128054045000e0a8a49035402c002c11803c050995800140301088490542c0201e84940f5050040d2001d81c00f01130000d501911241012070f0729480300300e40c140c4231004403905118140c0341a11030300061444030341e80b914080890601d4004d29200c18480c2d23a10601000c5400c4000d88640d85103100c2130254900b040020030031411404015000445401e035403540f03800f0 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 90964838 1250 90963588 90963599
    0x5040201031506022e0515031014041b0803130806060a032006160c080c0f03061f0b0c0d020105070e0303040501210c18051e060714120d06 61
    0x14404040d01c43d5500a4800c1e942400810600402c09210070422410013070803003500001d1520400e80a4914003084000d03c0320454245807070300c01c030307102c0d400c0c20140b0381100340800c0c01802c0d0a050304168072201640c2420004900144c80e40025046220316010003c0c180350200842c540340b50407105407078103881480d9030b20800c100894115201c090b0030410072400442081c030f200040c48248420040015040c0000700300400c1c01800d40b50800c40340c3c6494000148116202005210108036040710354452203011900401d40754180908482c2c2408040c4518505046003a0003800141c201c0b10191901e5252010160b55100b8a600003040503500e00302c085662a8850480081c80110103001589482c1c03a1800444040c01c0b81603c0c20b0107400d005a4030381100c4c0540c003440030441d00b607543e5108002c803e248044810030035680318a01c940003224002950901850352001005400c681030b94860080d420079202c98040460141818003c09125010303d120190290043c0c10310300404001c4241c503503 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 90966088 1250 90964838 90964871
    0x3090609060807050c0a0b0a0e12030c161406040308070e04150b0f0904110c100b010c060b1c0b0a0c020f10150308030705041403340f08010504020103 66
    0xc1c003512000a5121001641c858003500052075100c030b6800845042a602d5220000540d03010345411802945401110f04003040c104800324034020300c0464645142000255190303684035424000c0802d01c1909108014040e0710101c0342c11400800c800c0e16410b10f054a002072a82d40c040300d126003ca40e60810700c3d281824140b0584402e200aa45005812070030b14200c5901c41c2c00000c05000790090410400c80203450320300a8030114001d0f0420301e6200c54010105600346150040d0340c802c55031a060700c0b111a03a03444490360305a00c0d001500090011081e40100303c10058040c85840c80202e01c215207020495007040380340c4540c188100400c000a40e0210803a203070184030418200a902c041c2d120318000100d40c1c0000348040500c0d44015210303a80b541c840001e50801c1f62214007080d4045030070448000700f00000a40c110341140a000281005c3c0a01c201c00d5640005004401021903440d800141842d50b0000203418070451242115585400c001d0282a0444e400c90000341005101c40030515078 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 90967338 1250 90966088 90966107
    0x18090f07020703020402180d060e15130f060f0c0807030507020304050303030f060a0f0603020304020a05060421060f02070b01030c0b030f07081504060e060a14010c14010225030906 79
    0xc035030190142c10301c2c2d44c08102c081e42000501a65001b01e0b50a580c00950710b82424118840c840c55010880d1000a03071110304040070301451303003a8480d695080150f6403031450400300e0b82c0e941c0803104c48420610f43c10a20010108071000c1d403041803500c0700d40451103400c0668980b0805803503406009503500c182d03089869028030320625401d54400c2c0302081c0d0081160911603448580079180c0100a07503100c0f400e009440c180d52040740407943c00024030040d41000103010000e042c00303541c540c0ca05450a844d80d0103030390038040d401c410540040c901404011040d00001508015a0025511010282000640010203200882e0b0280d00c101001884110a90980780701c1c2c0c140d404441c542e03655084042d030340760b20001c08000444c10416800c072840e598501c6000003500750b8803c030000321710b008806d00240c0740d60741e000f40640508048447c12030380e13800f1001103140c0364800700940561300d0a00106000e80906451481b503c448001c2c20303c112070031140049000742c040e9030b84010403a035589060381c45405 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 90968588 1250 90967338 90967351
    0x6050c0106080f0c01080a0b0604030b0a050f04030c1103010908041d09010b09010510050d09081209120405010309030c0c030308041709010f05070218090f011505130510080318090f 79
    0x704c800410744139801a104181e203d5644140414805405400143e055000340c104440b0b12007940e0900c064000c891103101d43c0b215000daa50440c90a054a019100ca00e030301d0001040c110944034816003540702900f003545d880e0747c08650a6201e075251030b04804030102d08003150005510709800148941014050760302005005400007000740d00b01801e0040d00b0750904d01100501c00b0810104290801510400d901a4092502c0070b45501616200405c1d800b0041c1c550000c0c0c0e0700610704082c200000d04c045500302c031400d090024200d00309140c00e66140106510250505030114000401e02d0b400c141c6441c803451150b000703800c00d5034502d8900e00d81400740e4003680380010410404400c000b070140c8014141c09000500c0b05a80d2111203d9540031240704485901080e00514641c42a4a209008000402070701d2100c209206007824081024000c0741d100c1c841100c0d80b02c0020a4100300401c13500e90107000100113503a600c02a024911043d4010480036070b01804080f00015407250100303081c14040d85 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 90969838 1250 90968588 90968593
    0x60e030d02010618020c0a0503030a05040201090e04030801061d0a09090c0b0f0409091106030a0c0f030e1f0204050303030901090317010b0a031a1806030d21020c0c06030106050c0106080f 82
    0xe803544c1e010340007500150701250b1244515519400400e001b00040d5108602d5220041890700d400d2000600c4d880c119409800081c010006120010390010101410340c0c00314540b1050001c50a0521001c81c00364810003a00002d1110021a4018084c2c20200c00d150180080d2404640e60b00080a02486441400942c4440901003031144810704d410104407140612072000c00ba07400c0100140342648251090102c540c6d9600e9044961500045c105c00b0016a9007800c000c0e401c000408603031600080030442911102c500800742d03881400390b06440c05000041c003140d440345400d040c41da0081004407819408504402e50714000f00d13550010042c144c840d0f0740d02da14200a0300407400c0c1c0113410021203440064108000880d8992203040da1840c28280421181c03207681020340c181b6040860710445a410800c0c1b4402002042c2c04400720075950300044a001a551000c040b4400d040c9150030020703070390002c0000b000068866004d40a042042460700003001015a2840700c00c4d80d40c00c000e0309110554 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 90971088 1250 90969838 90969869
    0x7090c050915160605010b09031b03100b0604030501020403030203040e0a020906071b0e0c04091b09121703070c15060501020c130e030301171e07090e03090a060e030d020106 76
    0x203010b50340141540b12081290071000c01c40d560340b024141c41098101011490010038100c4e09882c08000041051000c1c100d02c880c0505000b01080d140c0010703900c007402e4151588080441c40d1950001c880085400200840d21583c036450002c1d2a03034003e110300b1580e40c0b100c00c04295410905c0c0300300d59410600401709850f0940c3c941e074013403030480320a042540740c00c3d020400140e4001101102c82c0b09400d0140d103ea901c90400718114200e0342a05004100c0341c80c224480b602860700b042030708041d0790350205003161030001807070f003106c66078142400c80760315181c00700c1400003864024040d9441e0b64401d00355058000a100b0b4264100c806a11419005900100d408811400c060010056000f09840042440d0300c1031400d140c0b4640c0286c6c02072a51001031440d090702c082090002200c0054481c44041c1d0360469411004e5a5610718091502161765458452101103010411034080f200041c2c1684280c690340c06e0050a4144201e20182c0a4007540d11100f04851041c82080151424540c20603402c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 90972338 1250 90971088 90971119
    0x50f090d09171609050106180506070305090316030b01150513090b0411030103050a0317010e07030209040902030a03020a150e0a17040e100305011508030909060f0a060207090c0509 79
    0xb204a414120b08040c007940d9030520340c03c2541407041016010001d0017140b9035140150081020b140002009602c3c0e084440510140c1e44034001c507440b0f40d82500d041510307401c80c400064208045e04ca00440d20f207071400c0b400820041e0301521107040340d003402845500880d4001041c1d0f2544a014910181c0e20a421400d001562240e0b00000e4040e170003910000310300301c1d1f9140b010700b41e0b402a00300b07485a138070a0040404051b03104801d03550280c1c1c00d601e044030300d5142c00a091403140300030f04014103064022440f0301041d02e45620100380e080d00242261510505400e0194a8683c1c03200e05664415001c00401010b294078024020007101070001000c0340701701360303d40e4130403158100095060020308010003c0d00c820b09803e858012138130f04a80740c442e24a1071400608560b0326a901c6a50500c0c0f1030000c014100021082e10708016041c3c410020390342c0c0e910001078407055082021503100c90a6800407901c1507002a1380c0b002c2c2d800e17074901008860407580055845010b50030313010b0b601402d03a6410800307 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 90973588 1250 90972338 90972359
    0x40b0f040503040b0a020c0f03010605130b01050d02030c1b010c02210712020d0e010311070209060307030209070201150503150c0703090504020d0c0342031203050f090d09 75
    0xc0c014000c40660b810103880703141040d0030340d019a042c00016030200301e0314152841d002880304a1614210000c100184c81c000106803030f540d00c000801000c0b6540da4816074207901440403243c8002c0007000855491030940940f04007600100043c6050349141c040a13079402005100700c01c0c19070030680003041040e80d005c042d10340105204500c2d0300302d8a0700744071500c0040d110814110000e0419005010440c82e1004010094101d84211a0405007040c00c05104100307504100c07a69a03405640b64980359640c80c012a1600000e85d200a400848400c100425154103500201d031b82e503600009a80c80d207558204040e51516180030078100800a034000c607030b1480422000b488000e11030b007012898070390b480c00080c0c121781000700100e44154564031001700d00b980c584955045d0051902007500c0701000c0c4c520840e00710704084580c4403040440c200c190f842e54010014440117641c070103d484100051200e005000d0001034691100d000c1c2e02e040480c0c1c8070440890300b501082d0455850440340b0b40b509400b801d = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 90974838 1250 90973588 90973591
    0x3030a091b030506010e0c070308011715010e060f18011e0e0903040906240e01110102040b1e0c060c03040f02030a0b090c0f0a1a041e0303120203040b0f 67
    0x101c509481c0d0115600a40040c8600401107020b0b0b00900703159850b00d40f1030104101c0092048280e60000c010040010303410003207650540310444243c0030168000604249000110b115000700907044c00c00000c1c5142202c00154400c82041e03440c1500d0350f040e40240074105800412401418503164014001100e021030000000100340030b4079a01c0f140e40f10a2042248000d840c0d52905400008040c40800268000d14004110a122807149130300f01ca81070170700aa250f4003290f000c0001c0d81803401e40d03583c816400140ca0b4004a0001c40d9a0ba270342d0250010643e100c0e5103158179010302c1c042440750010030442075032404054040986a10740d210100e1003c00e0384010001c84030074804030050409a1010800340000a114020b00d04480c103001241d10b03e0401000d001c2440b41141142214040d280c00f45000100c40e805d01c0c4050817007940301d940c403a0303600a1342c2003658401110602521380304030716001801100d0017074440d1030040e40c3e0300d02c5100583c4000c5030042c10600d215404a110348294050a030b = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 90976088 1250 90974838 90974843
    0x90103060b040e010312050a0e0904080c151501020303070f110114070807090e06011209150e030d0e0a0f110103060816050102060f040506010b0a050d0f06030302010b1203030a09 78
    0x1800c6844071105009504280c03c140b01d803002a00041c42004003400c4c0321a03071030035503062481c00c15800c40700080160100048507801420000045402c0117032000030f943d0388a0815098503a92450342110405081046900c4171959401400314411940003008a0b8000e00f2159035607011f401209100b0b640100b44860580c40340d40daaa06000c1c90b4041140d03000b40114401d54843c10b0b541401000280f4000141d00300401500055050080c50381e08284211247c11011134040703a40105404c00703504013a00101d4170090503040501e040c594030804801032200000d0b2250400c52604010492940c1e02d45d0312900130b0101c01c4800880005c948039100b04e4802e008145008122141c84200c014200800d2a00b003104850f1051001d124660301880215400101c8801070085441c264680c90390701c41c0103104035607482e4030000790a203101340324030104c4500c1761070303000b007817040c6030440c04620000e011504c030540040d4a0070f44011118681035106614405090000f03604503111917018000410021908 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 90977338 1250 90976088 90976091
    0x1e09060405010b2a0a29100924030809090703060503100e0f011a130e06060f01090f06090e01080a2301021605030414060c0d0e0120011a0a050307030602090103 70
    0x40c0304c2e8408100c50340c801442810003c03801104980740c40006210409000c0741c00b4101700070085440303403261596045805071070b0f021800030388503030b244000c54111007401c000100c2500e20100c1030140360b83c02402a6002a070303030020160f480d07200840845041d40640e65040c0c102007032521128206811070300c16401308100b0f9581c104501880d0900b11100d000071f4407012101e01850001628007400820f900c0750145509100c2c1000400d0056201d213402004d8601c81c2da15140c201c20582d1050a176000500307041031000c103c0c1034944c0409060702c4040c2c070039400165103040020031070090206120403034035803140c08900362000e070000701754260a1080340006259401d0088075040b0a030790411541701802640619501c45c1081d8a15001b040034000050007142d00300603ca0003114001a03400c0c041c003140c034003151140402d0b00126585508061b820310b142050300c0c02c1c0e8030904010742c440305000d0140a00022100100d0040c40030081c0e00303208490341a00005801c0000c508030f0340041ca11108145070 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 90978588 1250 90977338 90977407
    0x160608070c030504171b0402090d20130b0a090b030a12050c10020405090109090305040902070203030417061e010605040905090a12050301290412050c1e09060405010b 73
    0x7503485140745c140643c0000c542c4603445000903240f0310180d030003040d60180e81c15840d104040d00416203d0300114002002100040c0c000308800501e080342c201e03081030007009500031010001d22100a0030880b03c2c2144151259600080c1410342441501e6600c41c015000d440d00d5165920f401290101c60242c500520004201ea4000380c40e09110000d00b90210b600c005031038500380001c0c03180c0c80a05030040c2d03040f07034901a44d28000c2600401038804a9a4141015960b030800384082400d41c011680000d50b07201c0d0a500030041e1504c045129440b4049901c41e4280302c0501c4504620010400c0c4604000308a041000f4001807031540c00842d80311681104440b9844a19510150702c11052901c01c2c0008a01200501202801004500720000c2a150422595880301000090707841a4440c0d4600103403928040010840240310481010100170100a07542022442d003c070035460380b5081500c1420000300154861616100c0e00b8182c50b483c03151035050242d42c041e068032061898403000c0502c081c100 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 90979838 1250 90978588 90978599
    0x903030e010c02030c15010614070609150b03010c0e061b0703050a080310080a02031506010e180601020c18040209190603060b151c020a14070b0405160608070c030504 73
    0x25060064901d0f50055580f11480c0340391a0400000e81c4038421000f40d10f500400c40141e00c000102960615413414039512069490600c00500c07082c50000d2015404503902030036840f20350712080b080c2c0010340003400b0301c40b00d5140c01c030f4646050201ca2940140c1c1806100c01605a090080b00c4a2011a007186e01e01c9899845152602070b018400300c4003000000704000c008000482c41400412484004126008059000a031118000f80c2e09010880c1040c001940581c41640362441c109000b41008807141d00c100c07002036050400722015400340c41079540071000c03814448240075020002c003441c1401903c0c1d507420086d84020143c000c4103a2061085080c0b10709440d48a0a0300a40c410700340003840052505c140152521900096014098144004500b00b4032080700c016107102c0c2c50100507550140313032030155010b2058400c494031069011601e0005c000740c1325031060199014000f01e480c0040703d018000380c506410b01819000401e03001c0400c11080c01242e4140540f80300307080c038074205074846 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 90981088 1250 90979838 90979841
    0x10b03100b0d1b09030f0813170a020102010e070e0f0702010b1002070f06080906181f02070c0b092209021f08060102030a090608060a03020306041203060b04050d060903030e01 77
    0xca10900d507403192101040f658a4a40c0c0003032524034100460103078515140c9070322404003120007820641001450380e0542c002288d82d880544886900d52103445600400c003036403403a00d0030b8102e0256203040400d01000c2e070001768010880e00c048026010716528803104189040c400350403a400e40d03407601d90215a699501c04c2c401d0780f02e2030703641c000c0c5801d0b4607001d0100e4108007141e1202c0140701c022804d0200c02c10000c100c2650140c040074238580380c880c0e0089010319000341c4000e55040d1031202c03020380a9000217a0010101c0034040c103281500c0c1030300c410541e0010700c1500301490380110401e9400500d28400340c0514442040b448001034048015004035020309c40101c80640002c180905005000ea0803001c22a00328000388021400c2c50403090f00a00011080c0c00f448050101d4540010116038442d0b6544015603409010303544c05007001c0c54100c02c1c00180d100301c1c0300800c0c103112012404103103c03400e48045400c01041c1c0002c488180d02c6450003400e2850017a42056145d0b41c81000c009002d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 90982338 1250 90981088 90981097
    0x6030804060c170304081207020f060108010c020606040209010f0c0c050d0f0302210901030b0604080106030606060207140f0405130507080705040c0c0c0e07180801020306011103030906010b03100b 86
    0x1a0b01d80c12640381c840e01d440c0d0b14501c0d10200303080c41d40d0804e1080c800480c840c0015240e00458429286100d0f403260304003a0316014800605050500c0392000214000704113420a03044502160215407550300c1e4242008107a024912803540012614080348a88031320072021080c59500030300c40240640e48036030208580c408600001d07a043c0045400d5401003590401106186174140010303c61201005c526080c080e210345030005040544985003011b04c5d5441e40d044400a05011000700328181d030788d29192020341f20900c03070100907028003100000c1d4110440c1070451606801040c401883d40a80104802400c01420a0480706454021b0a0001d0760800005001d00902802416000e290104010607142074550003400c2141203141c440020340c1d0301010b030040d40c0c61205800a9a44c504600f00d82030100a00c40a0140c1214000080c1001066004602031102031f62211492213180c400c087e6a07110a0b03d1007141c5901c007100410103002540b01650700f04480010242c80595074009140c0c40340c10 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 90983588 1250 90982338 90982349
    0x24020309010b0109060e0a03020906031e0a0209010506030c0d150506070c1a1c0c05120a05070e01031b0e010e0d03020c040b03070503060a0c1e0c061413080d06030804 73
    0x664000c2e44903550f802c540c0c03d03030040100f403401500c2c881c0c094001c18200c114902c0000c0c001d8505002181166400f03200304540148440741802400c481e04203103a9448182807801e0f80504500340002c19542440d40c2100d105455000849240403414040680201950b40081c2440d10140c1c40200f0a6910030005080c1c09000b581002405420200304040c13040c1c0300050f205440c03504109081e16020750441c85c071140080000001040800500155040d202c2e031025500151203074030030031103903041950005011b0300c15955000407207001c2e84015011120302d26030001d0520038a400010440b80701d0a00c07904051410702d88030900302d40d0030001ca110180d0681044001d07030407071420100d0904040c4a07001c04044110f004040345840c0c503001c2a03c1d4200a007041c0ba89645540802115500034040240c1c55198011030885101704884020402c0800001c21a0613905120b019003400701c8a0403420f00910620f00145208840b40c4c1e903a00b100d42c400741c01821100d85074080003000c149020080c0c0010031 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 90984838 1250 90983588 90983591
    0x50a0626043002010510050102190519050325080403200301020a05221a030c04030804060c29060f0d08030a150602060709030818040608011a040b0303072402030901 72
    0x200c01d10040d0070340742c000b40b007000001d503101c0c400c007c240e0340002e20b4a41804d55004548400c84070741000f03070400e11900c1415080740e0725000d00000b0028004001c1c9000c1404980c02c03400b1001402819031260303203240c2e011300744038810320041c00030400c1d2000c440d414030180080118042c2042c0046426600201000f202040c800300e070725900c160300300c07452140b82407801801c01005802c1c80303421400030364200c44595042901100062150f94114100d030081c5411030443d503183c1d17585580040c0a1440d4072022101c0003107071503150081d41d00c42c088e01160503040408803c5140e44110034481100701d10380d03905602c010240200400b20b20035400440c001c0040141c08940c1403032420100c4032051076640110115444401003040140e80580e11500350303503008550720355800e82440d2000c401e43c0b1304001968030520741b010000342d246056205a00503140d14141c1240c075032844080100f1207000303501c007a405400401c0180c0010303100c6107a03d9034800080500307114096a80798104100e804c102c0d5280050fa = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 90986088 1250 90984838 90984923
    0x16050c01090b070206040b0306062104060f1e0b0105070b0901051602060c030c0f0712030c09081501090b010c0c120308100501050a110111070804050a062604 69
    0x55030300c0505640640080b5108501e440c010f0b038080f50491080c1d01c201c43c5080d0340400481d000f507440701d04a40104c0c82405038030358510491000c85200940a8404030f03206850001c120143c00d82ca13004880809081c0c05802d101e8081d030891180140410195003410030500b0018100007414050407103000d04088400020f103460860125607661050481c050103540c4070000300a903d4004104803035000400c02c0708180c481e005110215060300420780f0003084400c4d204e0750204900d0303242d400769840d10700702d03034a8007a07490382c1c1d40805844120a20401c8c403002d034500b006012444050f0404441c508d01850f0580b155241038841c0e40101c00d00c1c0d0001c402e40d4004800321000d05900c078980f9a080524203114034046490a00060014441ca00940050141c11401302445100030f5000181d900b100c5018181d8400d0303903140c8904140e00900030180704504121001c60020311400742c0741041c104403803500200c841c4241075504400002001150550740002001080480792001c0060911140a07a410b40 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 90987338 1250 90986088 90986113
    0x190903020d21020c060f150303160f06110309011a0a090504022e02010507020303060904140f160f0b0a020601061404092307020c1c11040507090e010f0521031605 71
    0x480e1b502a090202400742010888403e540200403540900c2074911a21701c004110300c0c0c03c81c0d001410381000b820480c42c1140080c00ca081703100046208000c2c0174000c00c109202104075905024900041c41d820520f03841c0b040c826160581d01058000d40014071012941c4484840c0c2c800d030000c40c00389084c0c2070218100c002d40c0540c090050a41190b4980055411482c0070700224101d10401080500f0841140c10484c00d409070901805001d00c080304181d4030318101310071160480c80140c0c4a2031124130316008000400030100070640780e800b1102c1e400351013180d1818030b0407107500d0300281031050f005104202c0002c5120f280d10810200210055602c0c0501c10000030700701c01003000510450654000c01100402ca548011000d1103030160b6016820109400d420b082416214a0044e1a001840c040510410941011a150880d01d01e84c10700b0060340e0301e40c4210300b0201254824190001038044ca0549003840280381240c907070520104603406d00c0e00824100141030b140a200392030b180c100b452101d48 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 90988588 1250 90987338 90987361
    0xe0a1403060c0c061306020702030109051e01020f0427061401030e010c080c0f09150c070f08030306040f0b0306070810060e09060d050c090906190903020d21020c06 72
    0x2480662809400d007803081e0707040030f60b850340e40007804601042d083c40c80c030310700f00003155060300c00075500600208070705030123440c0c125641d5504001c6941d00c20b03d162101602040b05000700e41402000003000c40c145880d020041e0103c081802001d14200b13410b902c451a8401c1c184108002030002803580c131181c00320400094120703440580b40701d6550341840307072024481e90000300740c6400c0f0030302111240ea80d042600404d1581d0044414187d03000c104a841130485c805d40002030300c034404a4600766034085907120004550816648214500c507001400000d4071498560f202c444041c0c0340140204148800b540000c0c100704044980100cc00e0080042c80b001014040c6500040c08a40c10144d221107461717000a10303070580041c4141e101c0c803a541450810040c0501c280060068050004100340c2000b160071916000700b1035448050b980f4401d107030440d01d101c03401500140d54140e0081c0850b004445401ca590703801410680d903004560124901e20b01c00c180c402050004c061402419160030080710181 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 90989838 1250 90988588 90988591
    0x10912050318060a0f0e060c0d0206010503280f050307150903032007060506030a0b010602060a0e1c0305090114090d09091406240a0c0221060a0c0e0a140306 69
    0x24002e4800f881131841003a000b02900003144014240301e241444803800003080c030b1142c0c4662402d2030051402003140361f900014490306848044094502030841200c8504014200f4400b003051040000b0441000c50924800c00c50411301034000d480c42c055440d110341c0131400ca1003100380034031a500d40307100080c10340c1482081150032544081d9811900c0005000c1a175004448010701034950710303401720302260b80810103818001d0340085008003e41c0d4450000c0d4403844101c074120685401c00411a10300c1c1000b1540810480b0b2a00d00d821103d203c100089004000042007210150b5030707100d007000180000a0300c1446490000c0052180d4400200003c1c840c00003540079400380307400c0800c880c203041c10400d0003581c850408e4902c107038514074111904105144221528038035000005000049592021140c04114000d64002c042060a202141a80004810740035800c2d0404004505503518a03004046031500c1450501c2c0414440000220041c505500c640804c0e61f1102454519040030f000c2e06 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 90991088 1250 90989838 90989887
    0x4091a070206040b010603020f1e0a080907030c06030509030d0504080a030f02090a0501050c03040f0605070c050612040602090d0510200a170c0d02070b0709050402090303090d020109120503 83
    0x6200500300f5585220750710806005503828150041004a40d02c2d00c00c03001d5800c0146024048800003130301030800c01c60355020900320300c0015080000034180202c0014460106e981c0a40e07180bc0f10392601d00300b100184000780106405000410942040480034061b2a0260b07004911480d80e881441002404866040364084510f500500c0b2440d02d581e40c40310940100c850030b00300241d8a203042003203c2d045224035044201240703c0401c006c2030403036000c0d000c1c03c40244594160720707a140e210070810840340280e4003514298a40340d030020b00000c501b5009451071441c050580200d030585d03699554240803002c20652146d5607030b6030b0044005211000364000d144001e0380e106182c1505a40001c1c007029030341200510079008480456650505c402c1151082ca4014404544480c0549031070518500190b03850b50005601040c082641d280902c201c5045110080c001c0d803400f007500301409480200140143d0601001040c0020b2100240307a20f10003191160020b142e5810104e4502030100c041d03d940f1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 90992338 1250 90991088 90991093
    0x12030b0907090f03020909012301030215070809040b0a0801021c061509030b04033b04060f0306050604090206072108010e0f25090302011b02030319020a0204091a0702 73
    0x400890008400d0041641c5d0155030b0b4103130070f5480c0e10b5201c0c05001c400c107940391303610500e02c200d040c0c404400750070074107883c800c40c1d5010030001d260045800c1c0307002d50800900240713010801c21940d4503003a070148225400141441440c01d513105004e030f00b26003103c009514401c00d410b20100c80c1c44c8645c45480003804454441c1400701480c00b0b0002e000e03403030760b000082981c3c9128000c00d0a140c0a41000d14504216842c0741000b40001d000c003075051040d818002c046044210112000c52500e0300039034045c1c88400720348180d100c3c6141c680401514000c0d00941d00907a840c4140c602585510740280041c9005000d51011018180d02c0180c000b105001b0140c104000300c4010322401140c071007000e40200c048900f0308203039200ea40801d04942d540011002d0118a003030210403602d40c0104902c0c0c100d9000362901080781d420641e00c114291621400258107800c208008001078458920b07e030341d43c882e9481124150b080543c041070481d282c2910075101018081e003030f03490401881a0080c0d00c4440c5202 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 90993588 1250 90992338 90992357
    0x14060c04031a090304050108040606050307060c021f021b0402070f060204030b09060103033e010c0207050a0f030206220b0d0b011e081f1d07020d090b031312030b0907 73
    0x3c1d1503100c0c00786009041c100a613440128040c001c91f034004102038007008081e1070310141e84440107883c4103e01c41049001d0a000c0c1d40c60005005a0903c580d01e24280d40c0107031221540b110490b016a184502c1d03141c2c0e025509000880204081103524000c26100f07070380059450f03065044c842c00100004215525035402342005200081d8070040350704101102220040301c481e0000b1010080d031800803a5207551448050620041c80d205400500d2910956001d0391000c5840b4402c0c00144800d81c0030303103501d48003048000c00041c10040e0052420440d403206d0110a0a00380f10b0350440310020307501500c4a00c2c170224440404510074419102205400d007096400e69005a4003640f9445100c034800003401084000a03090010600080014400030390b00b01070102c2e1a209034090840c070781c01800340c1d4208641c0004031a9800000c3c2241c0031012502c0344500c40d031074401c008400c0e601c010f203100d5510391b00c4c0420000145c640103500c04180819200840e01c0584081440f6050500804440401628a5 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 90994838 1250 90993588 90993601
    0x602010e060403020d0315050904050606040f0b0607021e060d06061202120a0b0f0607030302030a0606020304051e0d0c0909020f010e1309050c03062503090b0c030414060c04031a 78
    0x90404005e02c2c1c0f82c1004680c0164140e010043c1003403d9000581000e42d40c41000700700000403407801d100c1e05040b02e0030040790042401d00021201c0d5840c010740c000d601046090054036098500c04110704001104c44e040e000f00760007081040e000b16041c6090251100c4041c000c9582000f01c02c5028a4840804c40c1010450030191848401c0a400e08070300c00e0782c1711380d50784554a43d103482941176030000d45526600d03000da2400a000354030840d2800500e918100d80072911b0b61001c0201c80850704c00818070703500c4003110107007250f804540c4002d880c0d218924004a4001400300180b20000b00b40b22140090546d09600510091f680c0c1c0860300350401025991444141c1c0e94240c4462417040d150304000f511940d81c1c41c249181500190038641d0520802c020858844d8205101607a5011030f0082c3d40c00b41e001f0303060300390705807100d10400a00700c0c41d110000500301548035016661242c02140c011611000412101d0308021003914260155440054184244125045148849020701812110b00c0c038000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 90996088 1250 90994838 90994843
    0xc05061e070e0d050102040f030b060306010501020a03050a0c0203060c0c100e030d1a0d0501150603020306010504171603031806020a0b010909020d1209090c0507030906050a030221010602010e06040302 88
    0x81c10542409898140b000c40b030b440e040b5540100e960b000c1c0c021540c5a440720030080300b03824244402c58810303d0481c00a40d0034180450210304071401a00188450ba500350740c10707212074210620003402c22444008480241c0d0b0100840360103020000c015070f6554140c1e20303045051040342c1b10995541802c0c0107142800c85030020450b04100303010b50001801800700c0c010001c05205503d0b116070301080c030390680020302c00d040d800100c0e5100c0c0143e0083c1820b0343c400701a802e03400121451070100e6002d00040006a84c025141d00c58664490141c4208141c440304458000d240c0f07801c290001a0782d4007020f0b02d6949140d2100307000d460b9900040080c0c40d903980e5200103a0005008105201e07440700280c00840d00d841d60340d00380c03d951058072420040d85111005120000c1032107880202410700255815481c044c804660b40103400d555508240750030301d001519140e211101c03640405608211407460080b08407041d400c82151502e4011095150580017400c2d84c0c600c02c3ca40c0d80980100c0e042c400000d800 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 90997338 1250 90996088 90996091
    0x40f1203052811040306150f0b1204080c1c0917061501020307050f1501051e040504020303090a080f06010b03090706080408130603051b0c0a02042a0c05061e 69
    0x2180500d144280c4042201c0002d042c48002c01a045200440c022080206c681c00255804040742c0380d41580c40d66995120f141410507214202c0e5407403082003611413000b510808a644940150126842d01584010203480c0403c0800082c1c00c040e240c2d50340602c00c0c0da12204560080040c00f00e4514000190340c0302d10348440000d401c000354010100d07450b650a90083c0305a43c0380399000341c199500600700c5101c2c1074507444ca820011780c902284400114441c50240b20075565240c02e030a041c01c10040d0841400024600648144d0f0b040c0300c1440016002d503901140807000d4919400541100680041e42174a44201a00301e603e4032401401085448080010290101d40c003624014901d40c5032030a001c01035201d002c034012002c0e1101000030507041c0e0585c00c25800b03091502030f144034036102d00007980c00300c4c0200b600001c075a4010415030405407809420955208e484d003440003901000980301e080303480c00007402040100e00b0b405405414007609106442d88061b40c1410071f8501c00d880c03030500581400 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 90998588 1250 90997338 90997381
    0xb03030c030a0507050c100f0f02060c090609220b011403090a02150f0409060612060501052a0607030b03060703090c1205100509160605090604030809060f03040f120305 74
    0x41510024400c0c2004408040032028102680f1040141f10082444100140e900045035a526015015620009507a0b12544100207100d082100d90350400c0f2640d48248041c50780000c0500e82d2003a1058500805800251413001c005121082d0308000341c900b00340390484d100400000d100300410410007140341344895074101da510400c41c1c030002c2440c01d00d000b81c08503004016400b14000c100d00083d507210905446460f00c0d40c1100403200f9400d40150382050181a0000d002404a8402c00a0401401041004048070410010301c42444c8500d0880115203410009884030078000003400d051003a9a00680544ad060200320350980700c140c10b051242c8100b450152036140c44106000b0300b4445040b40c42c1c2641000e000134100b011140d507880c0c601460380d25025040d104002480c5000c0c00440e0000080a4421814070f880c54940740c41d103400c01090150048005c09c80110b0402099004504c2a0311908803124011001c1c01c004155400d81e080d04000d242c81c02050140d1a070007002c000c0403058 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 90999838 1250 90998588 90998597
    0x60306061814041122032307091508030c010c08011d0115050712020705030d050703120c090b120106031503030c110112060b070b09150412260402040b03030c030a 71
    0x4e40c610142c031014072a107400304080d041c08881c580104071602889200303c0f400366401d00b081c152200903141203940e46070b825003942d0344181000c1103034100d2900700381e45c0aa0105106210380340d440ca45a8115808032400620995495142c00f02180c0c02110082c0902440e00c110143e00c482d92844080420040c05042c45000b0840013030328006112f0f10845601039032008200b4182c82c0080d101035507608141c01568401d020300b90b200c500d182e12031340a480324190141d94a140c41c82902603113000400d6086040810050321100200301c05020100810003021411007560700e540c035042c00141110b210f10401d1a0f540708403001003020952145880307a5071604004149440d025440042e16600340c400654440c141c240907002452900130381c0908002401030711040019030780d0482890312030031070200301e201640800000c9004101040c0c403010544a09040c0700c85031039290584010444402002c0781c00007400d600c100000c40c02c00c5c0c0240c4d101420203400544c10611000c4119840f405a800e0150411 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 91001088 1250 90999838 90999851
    0x903060e03091e0901080f071a0c06100f06030902010e060901030b190303020c1009180e011107050c04050412140f0703030504290f0c090a06030606181404 68
    0x801060049a5220100030688a0489100c1070303503a83c45045a0328051055444400008017281c0101da50070080c2281c0000d4100c0c903042c1132038190381b620b11007501080d0f00000e001000020000b00040703802810b20b00e604845c85403a007210501c0c2d01645802507420107040c030b0a4900140d0b0000a11804041d0880782e96407940070f04401240108005207070780c0e03071140c03400d441e00b519070055900b0032003549d02075030035141012260800d0101c2e403603081401100180782c40000304040c40e181e02440380405120a400300300300c5200140b0500755020032042d4450361070002441800c2080c1007111412a9005407401c0c00186015101c841d4000704044904050204601c00d840c80c02600780c1c01c4a6070000c1503403205803100240d081c0100100803c5500b00c0b441d800340140345001a001c04110184c804803021601d0542d5039940f50504c0f0700401421201c0c03c0d000901075035009130b8400710064080c0c6615900002c6285c1380900c010503032524048030384044100c480043c890240b040c0044554000c040c2c501251300c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 91002338 1250 91001088 91001111
    0x5060c0702010507111f090f06030608060601050c030d15211109070c0605090a0b01050a030b0601030b040e0607082509051905150418110307030c0e06070812090607090306 75
    0x890f0141004050043d50000d203400c1039000300c0c041048c0d0707828000c1e030744186407215020780c11a80c05000f000d90070303400140020443c0d88203400404408a205040c2d034149421040d43c10103559460444500240940d1414400d824801000c00c4031124040341540c0c11540756115940d6444004540c1400b4038040b100003032540703004005a904482d03020404114910303200c0c0c0829210954001e08803140a0b0a20001030585014600002a83d802040c180c40c0350f100c0390015401003100c03140840c6c10540f9150409003400c8180f201903ca080320b038540b11102d18258400c1c025500352441c804800d10849012000c0302c0740d2003164182520000e440c84030562400d00503060318500690b2041e54041c510890503885181080007a00484a80360b070740040300308420403070b00196400c042c01030941e090180001004544650481c451009050808044203103003000481e4095100d003400b940e03000b5001883c810342040c0282003e92044448010303040364101250003c0041c09540300c0580349a481d14011603e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 91003588 1250 91002338 91002349
    0xf060d0c05030f0106050319020102030a05131211030f030c07030803090f010c050a0e0405130609020a030605071d0d170717070c18050408041211040203070c05060c070201050711 78
    0x18100040855083c0b143c2401010702070199800f44070701034060544840108072000c104045120303230580242d4148041c6003011245500320250001c040f502e1200300155a01e40c1d101d800394260301805131481c0001c110000c0c18135004c0c0102140e001075008221401d444000420040c0c150303503121714007542e80d07160804000c5c6441d50054443d91654601408100043e800c00020044100d080d140ea8041d90340350b504000c101c940441e034698107410415104000912503038403045c0c0e02440200303110203e9403203071201d0040f903904135140f0000c01c0c00340d030100c034529172034088880d07401740110303411900c3e10059520640700348050403a06907500400f040e44020801c1e001684a05408559055500c46600341003000c41034825104402d0001d50a800b00b1490440d00d015481c441c1d80c0002503a132419290251080350548088400e440c90130340007a140388680d98a0000318003407021651039501820250070824100140a040e11a910300100319000050760884203071410746801041e85050000707001c01244 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 91004838 1250 91003588 91003613
    0xd02091002010b01021606170a14150f030109050703080702030f01090f0605070216150908030720030706020d05070212060703060602010605030d0c0204110702061314090f060d 77
    0x39809100031548421455055200c203070a12400d0703088403520944200c3d002142821406960002105c844295422044444010f40c026841500c000b501e41c20782c110080310010151140007050018a0340404546849817601c08582d004900030404e490840d9921a40d4003081e10009014450210f400401e650701888149004a00d0301c0090040946a240c00028058111811207900b0300d001c010038000d901c001000c41d65420001c001c208454181b131141030500e201c2c0741d6000c00b041240d002c041007440701440a064440d2048003a800110b100c214043c94880c41c0c8040300c3d0080e80451001c104099001944029052160400300d85d9600d550010800314080c0f100025030a10440080c8105154954004401c850b01503000304041506c0d04101030312016020248000600c550050001610b0550b01030240d004030b0314441c52501c0c04a40c0403035050380220b108004121060081041424500b2141c820002c1c0d040318084403614040f01040742c55400a082c2502917550a44003a00b0444001c01030b2 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 91006088 1250 91004838 91004857
    0x1022704060b0706020a08070329041d010203040c0e0c0f030a1107030c0302060a05071709030903010908040609090504020108150d05010203100906050901031a090a0215040302030d110607050d02 85
    0xc0d0fa030741c0c0d104c0c2030036400380d80110030407000204800002110140719111b0380d44c06401d0300b80782d511080821200c3d29a1001100c000682c019510804d94030070105080141862129040015813245428100396002034400e5100480b1a40700c44100501c000041044a12115280b0640381d103e80743e4401e01e10081c04803460020201c0c0000540c0000d02d03810600c0039003424802d50841d40c0740d543d9180008151401540c0d400d010030115040707a0703600f610480c44190300071040b2048a0800c400380000a00791005480305540300c1c100020f040c00382c50390101d11403025241e1900140a9400e05a0000308040c0004220000d54881040501c41555034100e200d5041d0350003c000703540300d0412071000d07400d44041d0310030014040d140100006207802e103400d185049980111070700b5044020000c0464040c68003c1c0310000703902412030500c005907075400d403032070b52200002c1c015501c4900b103206043c58425075508000920010104041c600030b000507035960300844c0340c500399860300c03440282c0348007038040c12508 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 91007194 1106 91006088 91006109
    0x80909061e0d02030a1a0910020c060a0f021e030108010b0103060806070e030708070e04110d0c03080c0102040e041406070507030f0e010c050a03090503060106020102270406 76
    0x10102c6001400b0703a000364003259160701650102540003040d40002d0014020b400c14204140c4202443c05481185002d091074103880d0b40d4100100060592500d40144c1000f803851074050740d12070141c0701c001003124405056429502d03002405951501d6180c9100620950f109010709021151040b024010a03110b0b41c00496521600790382c40740c2c1611503640006088801000440010b01c0ea1074010741c51402c081c83c200d180c0a07441c40c50148181e90342510607021810140076441200d40c8003150750795400010105a0180c0941c2d80051702c850031440410081c00541c42911481c0500202540c015a0340d40341c0540341c9007e041e001030300140c10113451f00c100038010721401e18200014108500030352040e42e152032801e25000300490000b50801400c1007141000c1001c41d0150100b030009504160080501c0e58081000c0f00187c1002440c1d2030000c150354840e64000c5c00a440e40069 = true := by decide +kernel

theorem cover : BRFrame.Cov 90827338 91007194 := by
  have h0 := BRFrame.cov_init 90827338
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 90827338 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 90827338 ≤ n) (h2 : n < 91007194) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
