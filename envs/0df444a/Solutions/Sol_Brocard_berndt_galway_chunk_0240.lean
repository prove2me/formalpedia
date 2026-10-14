-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0240
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T18:40:32.742737+00:00
-- url     : https://prove2.me/submissions/7f8ac589-5397-4614-9824-633776045906

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 42985616 ≤ n < 43165472 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 42986866 1250 42985616 42985637
    0x1002091c030e010207080307050c0f010c0b0a05061903020604030f1a0903070209071e120204090f0b03010608060705090d0c08030c0f0624060306190f0311040b01020c040507 76
    0x140054080040c400741c0000e2491901c0240700c1d82c1c14000386000700007450040d400d0060640f611510b6142142c01c03d4400d8100c03108c0d40d4080c0c0d0061420246050704a0002941894050b11403000b41070b080b034146104040d644540c19074240c2010507041a03036005000b07a42000d055540702d180d0600200300a0700d100a424041070f00d810310802c840780c45042290b02850319140640f05014075506c000c2e1001c01486018180600000720124000414039150f1415014500b04150640005d00c42c40c1c01550429003448000c048004d0f854020703e01c1100150001c000040e9164030080d10388009590b6040011010040b544040c40c1404003404024040c1c5211000203949030b21092850f4410105003940390001c01c0321482d900030034800190b114444c2490400900c1d0300040110205500c140e1103441668044007050031031700e074880b020740d0f001480c44030b81c0100b90b1122800e03201c040040c40f08944654000354160380d80d0409005098502c503040c1c009003000c20b0500d04000141500401500400102041 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 42988116 1250 42986866 42986899
    0x602030c120702070303030c030b011b14010c080405071a04090207020a0905011503061e0b07050102090a0303050c010e03040e060904111c0605010f0608011a090a03080d0b12100209 79
    0x1e5090244110781c000700b910300c2c074524000d01660740311001c000505207032a03a161560b0360816034980c042001ca4441e03080300c40007460304500c00e001c625000d400070341c80c2411100c0c0c4c6035041920700307010300e000b1011100b05503540c03881c200f4546001c0c0f18085070801c090008101d07400044c0c0103054064802040100c215440f0144002100c0c001da202d250304407144052070070341ba5054415400504a11713900d84107143c250403030f001d60101c0e05d03104940480200082e90007d101d0294141c030f068100c010400040180d907030400800c0e9400001d407210480d442c10191800b5600000100c1d8200c6039a806c183c0d0280c2c0e241410406101d00040c030a8075080303165110303003810703544110000c5c2c200000c10110166400c06803c0c440122481600460408022801c0902203503401460742411552400889241e500301c01c03070900014000e0b8001d50780c028100b618003000f00030040b400340c01060203011041000c0e4540c481000020303140c240c1c0001a503000070b90148506078060b0020410301c100039004400400181c0c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 42989366 1250 42988116 42988147
    0x304030c02060304030e010e040e0606122107030206010e06010806010509010e04140a060801050405060c070c0b0f1e03070e1201061d0105030d020318010c030c060c180503070b04030602030c 83
    0x12005c40002d0030980d1030704c40b207682003a020f04000e0800d8604000358112001030680d07620004d08090311854680100c0f0610388810021007510841c0c0d486000c2158403940e19000c0d66400c03003401180940100c100210741030100308042841400d05941e641c40ca6241d01005440710f034000140c0314100300c429910f001c5252030710f00a641d030111410101070998a40000342c3d01c00ca5009400045c682e074100000e0202007000000e2003600026030b806419610401c030f15080402003132648c04403540c4000070410100104102c1c000d0300000c808022020220f44090440300ca040c4000c0322988040b0300329590344002d5081002c2070400100d800c0e0000140181c5882c07046e02c804e0b40c0340307500c4141d4400100045c0420700b020720030301d031415015000443c01d10b0610f0011221000000d81d9541c1081100f60b490320030b1520410640e000705810900c10003040c60340120040c6030000e642011600e140f104900003415003000246a07084035001ea80c0c07141003d086030b80e80006980040d10b815188002400030f08508a0b114 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 42990616 1250 42989366 42989371
    0x3023702060d0510030311030f0d0506040b0a030b071803020303030a0507110f031902060705031303021005040308060f06090607080f0d0615021603080912010905033108120304030c020603 82
    0x1080d900c0ca18505d14034000b0002c84a036010241550010f021400034180d60105076010300405c2c1501145c80d80d01e10022500a180207141d0681c4105001800820321071440c0d0303501c1c0201140e640301004a030041080d12501d481038480250198400c2000500d0380b80c0960005030070850300e1900c1d03840081d09140031440c020f0400340008142e0000103540b031010f07260780099905c610040c00a4152481d0500c80981280801000503007104016101d84040510901208101c0300c041c14003044a41000d080c0100b04801c1100c3e170ba40034a04510030080c2a203410003d59a42c0000185000d140055540d10f0f82c0b01a0040000c4080b03c480c14400b0a02c50706843c0a4240940312003001c0c01c440c101103a070020f20b810500302081144c0301c0300503020301c086035a1b40c085034500345040c1e4200002900e00900a401002450009005800081384060201d010f2001240e41e030b41140040030030500d84598414840b64140c42011090307840141104900c441440145500ca40a81818403a9140640101d0101e5004 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 42991866 1250 42990616 42990631
    0x1030b040b100908060a05060303040b071a040b040b06030c03030d02070c080a0b19020310060309020105090a0b090312090d03030c021006140901090b10030b060405040905030703023702060d05 84
    0x1c0000a1141d00c104110146c1d0041d4021018802410300502203612482580220302c1d140c00009400401e0001114038545481c00b0100071001c6850b00b81042e0a10810945048909100440200d942c4d441c0000751200c454500030051440d0100280c005402940442c200b00c0321540462000100f0442c280010b0490717178040c0352900380500d442094032010003204031407041242d10500a214002c403c05100c5400d60300c1c00c0c00e0010780c41c006800160b4a03401218841c5038008104013022070410400405025100015000c80e491000a545000c07090b006680c141500b0005c0c0000c00c90200744281c01c10b454140d424019910f00702c469100900696181c1c1d00100302809004000c3d210310300b4080426401480d4250007041040c5800c000644581d40054803603007003549a8800080642c0e51b00201d90080000030400c000900c010701c2e04c03a460b40c00c20708003600907016500c404403c0e00000b82c468a81c040c9c91060006201c401e2800302c0042c5184403c059030812002d0040340d140c803440d403003500d008014 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 42993116 1250 42991866 42991877
    0x30f04030201050105030601030312020a140c16050303040e060607031106180606010c1505090c0a030c1401030506060f07061104080115080304060906030504051c09090e01110901030b040b10 83
    0x102800d0190039590107912050103603006900400209500030340d294180841410096516082040c085a03060b0045d0542480c0c1030700001c50130288000000e0066034001c403420703585403156481d0201034403402544555540d202e040400039900b4034020004040756031090500e060020900302e180ca00c0c2041c1211502c0310b8094143d40d0f036a4442c0c00b08009030303100d030003460507901000c240e540781040d032408550400229074551010a440c0341c020700038249401c0014100252241c1d80341006860480035208180003504180f003500425446806a2885201c01034171182c540303240c0344444c9500b81c0c003075082514801d684442903129601200014801005c00d80c2c0007064902d86080c201441d44040e40c49005280c1c400c0004021140c0c100b0f100341c044a03200d003070003e451303919406d185050000318504030915000e401d24201646400181039015601c408600b00b10050781d580e1410708a40e42c01030510040350007405103224540c0300e03800c115109080a071020401040990100710400000e00032035000ca071 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 42994366 1250 42993116 42993121
    0x5070c120c030b13080a030c0c02090a09060b15070803090a1a07020c030109030f0e0d06090501020c060109141504020c010f0506040b04140402060c03070b160906081017070902030f 79
    0x68103403801c40c1c2044031042c134900c0d0b00c00d5554a030801c0d4480d21a02205064030b07201c0c4620b489004401e080c40c8150041d108807038078500032075050000c000c680000c42d940c40c600003840d80907042440c8503404c00c01070108801d142194a480300841d9070002020400c2501c070b00300380071002544202c0c240c009426045074601e041d00740018042d042142a50322203010380c2c9084110004650f0010688180e001142031002440b042d07800418260503044101805503401d001070101080b4055000b04000b0107003500b50303420b0f0b0740c80c2c58010f419503a80c001aa120f0221040c04101c44aa9203864460349000040006190604011300345080d07075207809080c0c15540e512800c128150401c0e005101450074222400c01004021029080f8a90320152000c0d01901c0085154030841c1003c004940c11290441d107101d400e854003248284031105c880034001c00182000000141042c011444240201e0101182c8e040340341c106100c0904607012041c1c42510740c400e0b800700241c44072161005500a0555001ca00101e1 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 42995616 1250 42994366 42994373
    0xf09121305090106050711040506120a140618070308090f1c0204050c09090a0207020f090a0c1407050318010201020d06090207020a0806071706040b120d1202031605070c120c03 77
    0x42c142d2000081c008100060703000510700040094104004440c0020151034100c00700e41c0701c0c00801c0e450340d414445d040c80d0600348015148443c00c90000041100c80c260717280c0c040c404417841c403403141d580d0a610910080c000a400c0a001c3c08503030b10060b00030002906d0400020380c2e24a90b90308881200003081c42d20034154103003130050580c03014001c610a860300c2c1c040c80104121400061142c8486640425410115501c41c0c7c000c4801c4d0310018000d001d1030910f0180d0100078522045418040707800c41640480d4004030005031122150824050343c2003088680944580c070b01c4d48001c4504655081103000c43ca07040303501c240301c081c0039803581c0140c030ba01c07052040c840c42c0d5029811a010702c1e403051040003507860740450076034035442480300c030340c0865202e032000708010384650807070385d9404203a01d00303040680749002440c0140107246994903130603010b240d481102288400e0302d2050581100704100b0341c0d0280980c000b024018864407800744103c0e654403106070000440342c4100d507140052002001031 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 42996866 1250 42995616 42995629
    0xa12030f0c08070903020f041503080c01050609070504090513020a17160803030c0d09020402070f050c010c02090610020a080409060312170105010c1115190e06030f09121305 76
    0x7140203909001ea07003410048405419452603102c024071400d01102c5107000c0e9221a0030014001840d00d07018951030341c0340e140c40d82c82e50308046e1104841d5846d0100180c81e07071420081550290180d80c5840e0703d0107091013940300207000f006008480d0690078054103001621079015000061055400702094038001450107414403541201c0c860180108007801d1001c84000b02c2140c0d0010758a0610030b5a0b45074143c0560060104a20040d51151001c03510809000901d142d10030101c0c4540b007542c0c0d03001012401903030704c3d4132000ea020b0341180400c0000b0341c80f41040340c9421400c20150041300e0402003159130704050750303200e0b8010b507184c541c840c1410000c200c81504c5040d01c80055061004400c0300008001c1014001446503904110341c000380902070207101c103200c00c2d128001410041d04840200c00040c050340c07283c140c41c00700c9a4010280a0120700c998420308040200410680c919180c007000c405c20004007411030900c40c001e000c5900c031946000d5000b004803100715010100c4c001c3c40c0c04100b228 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 42998116 1250 42996866 42996881
    0x3020609011503080f280203030403080606130509060d05010504050708060603030a0f0309060902040c0806240912070e010e010503070906080a0f0809030706120f09080313050a12030f 80
    0x51030042c004082c00020868000e581c591340d80e942e901d5440f60001c42d83d4a1150020110f10071942d01074102001c0000d90220043d0311582c081d03250450f460f2035a2090158a00c214403ca68036108043c40610252a2200849400c94801040031881c0d00c416110300382100c0096400325000e610100301045200d8050000c6503204408070043d5007400c2156501900302c1c15100d45942c20948d03035103903400410000341d02070103060ba0098002c00004c201082c2c0504819010340c4c18601c00c00c9010108903895041520389203490745110700f414201241201801035049070051001c4441c01f13000030118000340642c00e014001c01c85044803100d994508010f25044c13003115080402d04505012061243c80c0f4000707094140300381c0c010400e03600d000d56810a943c10380aa61041035041c010040000b8035150710107011440c14417518801c00c43d100181442304c00f1101c1700d803070080ca0340300c06100080b02c1000081c17035200c0c442d0181307068401d036941969070000100c41d0103240c07038040f80c2d542202c0668015248a5082d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 42999366 1250 42998116 42998141
    0x50603040203060a090201050f03190501050406080a23010c02031c05011a09030106080304080706200a0b1801050403030219030b0a090e010b120304080d09060e150c0a0302060901 78
    0x1491420550003180d00c6040041c00c4e62034064030358504008591150049a268035003080c00c05489041295034030030088003c00c1d0b0140e6072810308c0008105841d140c4110b41c1102c0d4581c00922440f00c03156246104000e0003500030b8410950021030220b6081c4c00e00400e06c1d00c011503400f55503a0708800306c010b0b44602020781d001c4401c5190000520005034217940100701d480c64844400d80319002e0100280c09402d403070300259120302001c11300184160700000c20030240c0e040d90700c513112002540ca00411080c0144031400d2404d074031048144000c1040701503090381140c0004c85e1034100f0200c80c84070500b520800d94088000039070000b18118050034100900c441c0d81d209207024020303d5942c0000961800441c0144080259604011000581c09510019464102800e62017880c20b4590002c0d450b900144a009900c1c040c101701c26884d940300321615011307118551070303086142c2c0081c81484902c451800101e400d2500070005804241c0341045907003500e901c2903008042910b0240034a5094854024642 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 43000616 1250 42999366 42999379
    0x41503050405070905130f050c031e0d0c02030715021005060306090709020d0204080609030301060915020d0c060f1505030d0c0302030702100c1407030b100602100905030912070f05 79
    0x700010707501007200412a00809030100d810f848814020403521140c0200501000c0081c00107010400007045200715400102c00341c0d000d2041c9620064000a05100a100c881d007100039081d44490094521080707041c006402c984001da00c0d00d40e250b1039500040408005681f100c10002c01c044401d008295101c4010307400b40202e4180310100a07500c240d2405068031068000c2070869142c2c98035410f6034002c005d07800407244141000c48030355807282e10a00071040012213814001c04c10344004882ca5484444590091035030400f50b400071285090070a108503a400d8442ea41c02440d142c582c003e01035600b600e0010b604507249071408040c6460500b000480034058a81410780c00f003500802a2030043c0e80503035802c001501c3c031180440d0400c51140c0000c01c50300d20340421500f03030310001507401d0a4921842d031000305600d4104c401c1c010303140a40b04100050340300010601300c5030703072540100415500c03076811a82808204400200c1110200c2805412603200a804000c07000304400b10b00d004110a5503032 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 43001866 1250 43000616 43000621
    0x30306081204120201120e010903090314071511031e03100501020706090603090c08060115021006050a0611070b04060e0301050a0606080424110318161703040902040b04150305 77
    0x1030f15028101e0300340c060b06001c0754803034030310615100b41c01a480466101008101283c1280b4000d800e0140d680819603140004481051440400240803805d44040120f20b031072040c59040d0031122048203001c0042c4070f00041c4200003125581e0700413a82135170301001165440e403038000c59a040d4100319610403411503014003010050a0b13003000c00c86d0143c0d50070745800316041206080412a44216600402c1180b08500001401e8003080d0314246000d04c195007a1066505100d0440040e61224041e042e8013800340e003001c2000900a040301400c1c49107920559400640c2c2e2400c540a68100c0c1d4000c1c4080303082c4442034012440c00b845102c0d4842000d1008100700d41c00c03d10000c054413401880280f1082c4000c41c0910020006120074515001040081c030007a01d0b00e41705008035800c2503c2072010104480440040343d070000c2070070211000c0700704d141d19406241c501c0e2179481d5507495018400e42c1c0801c02010482981600041000e814011091940c407841c0c000c0100f6114120441102058a00402d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 43003116 1250 43001866 43001879
    0x1508040305030a0e162904030206091e040908040f0e0906010311060c0601030809150c1b04090506090607020c0d0302070608060414041a01091104050904031407030306081204 76
    0x6581e08403c20b2440014112088040507280c0584041069001191500b0004601e01c10507400c0e081d4148074402d5107510740e10f40c030400e580c0d80514000207501110030311030064103080044070061070188209e203011910f10484042005c9910640701510409000901801401d0050300f0b0b800c01400120300104103464000d03132450b103605060200a0104080c42d0401100703aa802d01a01e8401000340196662965070b0f03e4220341943c0a040e180d40640a04858006461506410f803010100b20304090031400120950095840008020407644030790740e4108240030072010440d43d480b136142c2400030304060070190340203490f080d021079182e4801c0c0c440103004400030303902103200400c5444904180d08070b902e80500140c00380140000c042d00007401d803c03c000512010750200e14140b8000701520b40b003070343c89004000c150354152405285015040100300443e003001d00b5500d0384103000b8a086040259906290103e81d4055442500000e45a03007081c482c00c40180a40a170300444205400d241901d04030 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 43004366 1250 43003116 43003127
    0x90806011503020c07121707051506190305030903010f050601090303050307030f0207050c0414010501091208071707120215011e08030408070e061e0603040813090615080403 76
    0x103002500300d10089028401c0e802901520405603450080e50b04007604e800703c0c990b5030310710718100b520a040e019000360070b040c403d4011640d1194111024015101c0d080c450020180000342c0700a40008210f802c1c61480a64042c0a81c051486100a9903444425004050a681c40944d80c0c500040c03614050106c1a030300b00301180200c03a030508106480b5540d280c0181d0040250401c00c684403800010b80700200700c0c0c0407680342014038003142e0400c42540450240181c101003409031602003100030000703103d11240800036104203031040c0381461401c0c1865407802e00ca00b580022880c0910701c0810201d0410240c0d02ea8002c2c0c0164520080800c0b0f2810f0722010a21300c0180705401101c42078610500121b02292070303083c09000200112943c65070389101259441c00d543c418510750070900380c04115a0310f00300403920103110045a003109040d54041c20000150b00c080c0044a07081002c03c02c0311100d8026010702c0b40180218640024054030b861013606200c10201101400c010006e010040003035000f0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 43005616 1250 43004366 43004369
    0xb01090b0406022a180420010f05070807080d140a020711090601020c150a090512120906070605010810050702010c02061b0714010608071a04060302031e1006080709080601 75
    0x4001d020480c5200c13548400305064114458000384c40450f006242d0310b9000d580b03806188641c19115800d4041d0240d0a03503034155848840c001840841e0002c40e19104901500e03100b40500b2101d46040340503600c0301700c15803203d0501e99a0580751641440101c0c1c1c01840654080e050160030740c5081540c1e03403640800140041d04511501c0854081502a4402c000c0300c0c00e0150090140b40c5185441000c01c03480d504080740040000340b1003000854a8101000c1c003508151034903008007174180302441048490340006a0103908000e0500840002c10790398044c0500a2105802800031101c0059030b80054940c002e00c0350055a04041e0007401e40c1c0d0340000c040d81e2100c2c150103943c01c24803090181401e40c0c440d490014110b0b0b1a452121082010194010822560000100c1c3c000503a0741482d0201c074401c811000864a509010411140b8025001140e1002d414000c0301000c0b182e07021b119506030015200258400907d52090016507040328006821940909045a00038030306100d4079170b0340105 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 43006866 1250 43005616 43005643
    0x2070f1401031505090f0f06190b0d020c030d0903090e060603040204091118100501020703020a0b0c0a0c030303020a0f05270d050303070206040515040804092d0b01090b040602 77
    0x12880c000748450411129240038002c018941d400e00d00f8000303106044980c0a031f0300315581c241c000010034040d18101e030003004030554400b00200c2d12880c1900400090300010b03216642180c0030440c401101078240010207a0081d2650002a8020035003401455030445030031803581d01305c0310004c0c00065528181a20361295046402080e0b40c582e038034000c240000340280c1e50360800051050b945990415100d003d201e09480003000c01140e66031401242c0e0380c1424070029400540e074560038072401800100600390244100112041e150341c0da600d40c00049001c3c0d20a0700020b030302188500b02c0030b5224050300c0025810f0320f400c0781031a40b546a100c203001c60b0b420300a9040b1036640301c9a081038440c2e881d155481034001c426684c6a10b0401800382d1106c82c00c40f402c44240c0102c603581c001e042103042d419401035801822050a2a050414640c01030001c2c0003140398082110b0b0301502c040003000c114aa0101110304045032103c0700c8c40c009030402071380c2e130081e0f8a18402840140100c96001441080e807208 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 43008116 1250 43006866 43006871
    0xa050712021005072015040b071b06050f0f01060f030b0321090108070c03021c0e0d05010b0307051e0609270402130b01081807080609060103020102070f140103 70
    0x6042050307103044040c0a00302d00140c10201005002608122810b14400b070300c00018225840d030030303010341e282c2100c56214921104070708003050114803070100c000c1d4031218900b032585003560944100c0d8120b038949030b01202c006859034104010300c801c849019802082440110b00554141040501b10040081440040503900c0101c58001c0e0380802580f20f6400c5100c8841d401c454480c2c0c8090a03a40c400d010580c00b2505071804034200a108501c9541050b4240d80600715030700b480701d640300040c0c402c4240c100800c1102c660448542c0e56000b4140047e92041c400060344a805405050401601c0e52041d8070a0b0b04003d80718007003201c507000d09481004101d500030350341c64040c0300085410700c2a03d4124080207116004c0b6003002000c40d40d040c0100c2c02207444c9500102d40d1b488090941d142040b44038006402c01d00490744160000441d13014122404050364221601c40064500d010002c80709000c1c1540000010810b6580600c140d401811090340101007003030800800b0801d082085200030304155 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 43009366 1250 43008116 43008143
    0x6010e060117090703060f1503061a0108010324061d0105010f23090607080a020105010807050a0308070b041103030d05160305070914030c09040f0312020405030d080408070f0b09060c0a0507 83
    0x720f0319230002c40c010240c0c1c0b0301000140d80f2814544000c0400e103035050700304029517207444002d6014078a003904a940c849c502c01da1603e1a1003600020007805c904490149484039400310f42c2c042d8504030307610b4051140302c8600031503140c98001000c240d080320fa01024816943d86140f070304051401801000700300700e0328265880e856100031407447e10500801519400022078403184140d419000941214480300840e900c15807180c042151103c0340c3e1000805010003040707042d00050404007496071060182c1801c180708000d80c00801c0c1564000810141c809544004000c600480320039074205900962504100034500010003070140700c1ca41c000e805c042040ac0042440507501085006c0d50f149011703011401c1070a091401a1100701b14000460100301096240043c207006403091342c1c02c98200800900680000b13603029501d00c080134005484a03e010041007000c0780f11035640d01c928038410b03100c840395841c00d42d420074101440505400780480b0300b00031300528541e0040548034140d8000e86000300f841c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 43010616 1250 43009366 43009391
    0xf060603090521090d1a0408070302010e0303070f030c020c0613051201090b0105120307170307080601030b1c020f0301020a0f0f0504050d081b16090c020106080601090e0f06010e06011709070306 85
    0x38450000070344030b04850b040411023042600b81c0070b048810f100760000d20054040c0140151030b80412203001002807011852002c031240301c3d803c03412000f4000d006580710311484002007286544010010503c1c028105420842414100c00701175050710817200070460404580d84076540704c00e040c410356108030710904140800500900803100752560040c456901c01c2d89400c01e42035103400c1111450301041c1c020300050455406402103d1280c04020f094a0074405200c0762242604140c42c400d9070415540700d2182c0c09501e00b44005c1135628100d45603a821180c00c2500200102000000901001002c1c84100714640f101c40d20002c00691081a1503114031256030580400501c0b0400024035203d680f03410380c20030345802e45400958002020500060541d4a0240c0c20303158144511100e550103440100f01954455008525040310f43c41a41d903083c4107000c40768039008081e00804401d51015040c0410b030741e00102051503c001e078049410641c60034400e99900c2e6840340c070003d4495501c410700040f00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 43011866 1250 43010616 43010633
    0x506130902070501050f160c06020a090b0c0703020a051e0d0822140a03030e06090604030c03030306050a0e0705160312060620060603030d0f0f060603090521090d 71
    0x141a011a007103496800909000307010f440180c170700300002c040c25404030359032000c03469000040c845141c6071160b8219140d5a02c1009611106641040140300000070030740308100c81c020907604503802d005059107411070041203214103a6520403882143c1c5043c2071201c0e98101018150b034400d04860780d0154150508110b0740900c030b001046490f15807025117010000715002c46010039500242c00001d40702d01c0c50404e104044180b404080e0105002111a914a1070108010150410040e0085040560b80c0d603e08940d0704486d0021000f09407541018851030401c5580714004010342404c8005d94107140202810318030032013581881030401d84107400306060013001c5c0301400381c04c0e4500401c03000788d07600c20080024401c02007070241e9031304010f09001c04a500140141c010707040180954074018001c2c0640e0010300341c0711030342825903850701820815441b0520980006081d00d45003c102e400c00e80c0343c128180b040b11841901003210080c0c02640095a24050741d200a50a40d40c074041c1d01400d0610014 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 43013116 1250 43011866 43011869
    0x302031201080607020622060b0a030b04030f0210060303050a0e0a050907020a02041a100f0309150b040b040c080105010c060b0d12020609150601050f0d0c0f0f1404050613 75
    0x10031021500c0002a90480003c44602c141096401d42d10103885601c0501090045500882c0d1107800c1c010000d00400c4d1154860045104000d02032000303140d49507030b07a15019500700d80940100f0090904c403640c4580602001c19410f1101c10100a414115500645a4000c50140000700a81142d02c1320060701c45c900840040c00300105100e00b40c1c50407200007561030b000c00ca0120f0140e410020140c0031440d10017a6070004a070002c02c000608803c84404a03a83c19026030503404050f252134000011401ea91000c414004220f04041280366246041c441660b80420b40140907030328011007280d10f41d602568050540e43d00b46403201c450384460411340080c1c00101040b80d80811107410201c10801d170b86941e00001d240316001d0b00c0b2503503500341c2e2007601c42000714800d540101118000a242e1762040c07000b0f0403140c2c000420281003601700070a02084846144001000c5940c452038071800c503410001c4000107007064030701b40d2815441d90341820141d01070391241340e00807130010422855000b1180d80b91070 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 43014366 1250 43013116 43013137
    0x10050703090515070f0c050c010c031205070c11030a0b180c03010203010b03040b0c0301030c05010c140105090a060e07060203041401050705031201031e0b0f041103030424020303010f0b0304030203 86
    0x7441d15000c0043d000d2445010344996000ca0481da0382189081d014080f010412900071000d081ca41c46140010754104900d03640031070401c0189400710040d080c0c1031080501528065442c46120011890f00d000450101e0400310f210354080301c6030700006501040320552240343c00c0556401442c80401243c90016161182a0f140d4000b2001192100500c80610320442c0951001981c0b901c44483c5c0840c64030003800040c20000040300c1c14007407540613444211119205441150307555114506441c03c4031002d41c2c0395100340d00035000040511010b40a1003800a182402a05030700340381600c06581d0707120350f20a28050160589020b0410fa010300144c0c0d08075504601640da844032285001c0c04e5140c02400126001150008800400c2c090b804640310860f41c451135800464517644a8412070383c1340100f084030210046150030000e6242803010f00010404281c9642803000d404110034501303010b11040e8000c5600034401000340d2045452010116050f240c4880e5480e200c07800c089095104000c80e24 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 43015616 1250 43014366 43014373
    0x1005040f0806090c0a060206010308030c09060403051c020304080a15020403380402060a0507020d0203010c170f09120a09272414040b0405040f1202030408100507030905 74
    0x503240d10106140340f007040303a20b00340d50321982c1c41420008240118010000180e01c401c00500014507440d00864021544400d641c0c204507420002840952054204441301e400801614a5038404540459480c0e507180c0099402d003070a01301c0d46a515800d06c0c0015000f02801c20504484881ca0b50484010b181c02000c046440b04903800030950116816500d049200e0f224400c6080350141d61303011900944c0e0003032943e45040c00da4401102c0507000f01c00300743e07030101c0d000042c840103079003d100d0b6502d0342085440b90089640d0a1292942e80240101142c00324105901003184990000c640841c4911080a1540e2504585c181c115038000454115004550210001c82d103426507070004185d040c043c1c02c106210420801c00303092194072682100400c0c07110410402d010124400328600f050202c0a00000345030620030000609139401664261540ca070000a0181407002e248115025103000c3d0000b5442d10f8a4020a02da548052103100c0b0711081c0d44202086040d44a41c1001a515401c00f049 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 43016866 1250 43015616 43015619
    0x91709030c0f3a060c02070603050106090e0601030212010807090e010519050c040914040b07050c10020f0c07030b0a0b030703030e01030216150c030605031b0904030207180e06010518061005040f 85
    0x3100080c00d868100c44091f00c250003001407160f10034001c3d941a58201d42d54881c16a2800141030b0304214090301c0b89040c50340a10180e9000044268014000c007008401094954035041e140d4040b03030b41150040500b42d04020400c2100a042c85100030501c400710030016803581e9140c110032490140707801005910b4184038110012201032201c0b60b015501600800c0000e44500200307032281d1080110301c00b91134005c841e03218440001c0b503001e4100d2109110041d4070300a01c41580d075041c40c0079a00119540700b1400140101008103129184180400b41c00030048681140c40142422801000081c10103400084102c01401000c3c008071459902c850407281000c1e10441c0320300500703d03590340700b400249001400151460000342103207140108619640b52074054606200c007081740240180e05610840d50b001591000e00002c150321083e01d10300002e1111f2203c041d075070402c0b81c180e01c0f00e44a0000c640e0303154a84c6e643c229196400031300c110341c1c00309241103400055034240541d61001c09003500b200f90 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 43018116 1250 43016866 43016873
    0x50d030e03060c030403300c0206010f0807030201080c0705031308100c0e1c17040f0905100324110a030923150a091709030c0f3a 57
    0x4408580c0001181921080e6030750008640403030208440180c000340e00ca00300000b82102c0c90320500c80c902c3d010f404001c440c0583c0c401031810f4030824a80000144d101e50010070003200f220302503002400450020300400391030352300000c0071150040c1c06444032070800141241000f80400440c1c10134a00402d420040a80d2520141d45502c0c1c40030700060168100888404601d100e035081c0842403400034000a03a21b411000d074203580902d400310480d1000c0c244060080b01000c0c00d03001d0701c020020b00145001081c00c00c041081903c801400c6500c01c001c0c000c1082c03000511807101da030580389039154060240141410444003034018a00304c2d55500400103100706606515030080c01240e4011481b89a103520820050b403003605100c051000540c100042e040341a2940801c40c503001500807001041d290a16104e07500182d0b009840d82251800010b650301c5541018042c041c2030b80403c40e4501c2c698020000403d4243c082d6103011800d1024500c4018000203c10301c0c1451040103400402c0c44102da90718 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 43019366 1250 43018116 43018127
    0x3130c090b09090105040b0109020a1701030b090d0302090d03050f070209070905030c03070305030702041d070902070308010909030207060e06040e010b04050a1e050f0a080f061008010b010801050d0606050d03 91
    0x1c00203070040c21244002888504140600e500444c1c0c08456100940c3c40e26110f140250014030101c01001403001000c4202c10580d49042e019500414000c0b049043c85080a86000c1001d048402494010311030010030303640d84d08401a986406080ca00e59519600c09108028451000b0080d4402031060900030b0160303012031000191a01901100d020b0991441050ba4904041c48004c0a0758010440c5100506003034026004420204054000308100d014101f828401e07682c101814003a404140d5070241540020114010600d100c02044020395545000352502501e02950080c080400003056080d10741504072802450300c44580d1100f035071200d02c204841d600500c0380341d1082902c84400b0619442c0c200e01050016030084554a0031854801400087c981d40c0070000d510410710180014020b6080c04038960450000001d881d140c42c010b92030020028a903005a60700303070304d00300280c00e1698020400c98151801207510311000880340c40d0003405441d40303400082d001440c00141c3d0702015000b9 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 43020616 1250 43019366 43019381
    0xd050a05010503010605040917160206030a0903021b0907230a020109060e060606190201090209041103010606020705030d0509040f020a020f01062102100c0b1806010f03080f03130c09 80
    0x200d00174455181e480301044141c81d0340340d43c0505a51400e0f061110030a611000418a10040ca1a2410000c0c3c854000030600d0b04100d0b10901020340f1000c43c21f00301a41402030f00c132a08090b2446a00344107212002c81d1420000038411420300415249a140e032001c140d20380b6580c030521244442d5645155032b8028003a22484504490302420314201088900e0080744061040c00d0140c2401e040c2851906d04040c01540018030700d041d5581c030104100035898400d0f0440c4114041d0f0a140120a1800180350071075046a111104540100d8414000f99901040300801e00302146805a2155500400280242081500d110f082480000e005804680105940d1aa03064000c020881c966035041d07a03040c4503081008170b40010422900e03000061a082d009100c040503141f81c8482948890303a0717149540a8103803810303944c100100081e440164020050a0701400e1179007040700d8000d01d103941710a094010200c0c01a0802004800600903403c4441c10f44201500400c0090350280d0b18401d420007040f51 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 43021866 1250 43020616 43020619
    0x605040501060e120316020613030206032e0501021902040b030304030c03150b060409020a030212040b060a050d050606010c020d06241d0714070213020d1413020906060d050a050105 79
    0x1410b8003540300b0f8501005860210540c1c540e40c000100051f8200001940600340824030b07000f00041c00b0000d0780398200690300c560100c0d0030441c0c081118480c0e00300c0d085100d01018a003800c003030300c0910490340e0106080014019200c4c5200d280c2007280b000801030804c490129400d403002041c008140480f1a81c0c1000b26070169085150b0038002150120560382c503514030030b0308290100000c0114140b168018030f41811642780c014140040d0f65015480d46009540035030f18201e10001340855490008001f00060100321801e42d03000c2400c0d0b49154807244010030b41c9040c8941d00361104150f44aa11200c0906540304c08100300c0c42c01660304219401484000340c1b11920b00c14400426030451304e0316030001520a8480d11030b0aa950344404840c00120b1200c2e6045841061040000607144e040324591804c420000240e100c00c850791240045851802070942080041018410555028a8027958540d01a20102495a07500011802c2e500c948101c000102d0f24010422001820950001c3c8c181d410 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 43023116 1250 43021866 43021879
    0x20f040f180609060b030d0906080403091203030c14041208181903050d050307080a050c04050402040305151510080a110c06060108011a0f071103060106230a080a0509010605040501060e 81
    0x4178802415640c0d503210034940701045640c0828040e0902a80803954450310070300d0500301c105c1d11800c1e4512204000e040c12800b01c1d03102c24484140f250410440d11145ca0035051150500c0c1c42d16041102e60703d04140041e0614500140307400f445010307444030014803140030340b0100c52503841c1c00030341c3d10003180c0b84001d49041c0900304452005510600c11a40220400d03528a1030984a2105401c01040054804060300504000016064445001400040d40190058450f43c80030803010025824000d03c3d2a0b22921340f04001c40c00d6036244d465000c9003422514004185955581d2240c008100280c3c00c080b9005002c68201404440010032920070002070382d40000a0740d8a42030b882c00d00540c0d410311288044140841e0078840c0800c00901022130003005100c00d640c400501203401d002e8282c20a0300080e4061680c2d4003a03650004181c002c0d4186454214038080400350300600c200360182915041589640100302201341c00d422440107004020300030003403541d4410014055510f0308028500801 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 43024366 1250 43023116 43023131
    0x1b03060b030703080306040c021e0a0c05091003170409060b04050f0102062502070b03090d020601150e060703120c050301090b010503010305120309030c03040f0f0b07020f040f18060906 81
    0x5001ca02c440450350300081640c00c40d150baa00f008060719801c6882d60451041052150314018100202e114010401c000f41c4441c50f0349003071500d0705a00e260081030050688209020260701e0780355000040741c1d0800c5190120241000984c171061003141e004038525070170f21030302150902444000f4011200d003100e812510924403c0107907110705089803648030340b040f1200c81050340a8009106014080a4419102c0c4252241e403442c045400944940d078081c0d00c03200d4211016901040203902502d050f4480d02d440d1800301c40001c0c100d10402c3c0301240a480301103004020580500082008a128044140729041c404040140349420910801031140d00f0420800d5155010700120303030589400c4006800450008810b5403440d502c060401030241c4010890705951081c28800342c030242c21900042c402c0b803860701a81d201902c2c0180c1016441c4131042110380c00595566a0703c1034181000d54010800c0c50391114000002c1c03940c11043e40320707040700714881401c010340c40d40036031b00c110300c201c500f007100c01c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 43025616 1250 43024366 43024369
    0xf01030903080615120a150b0309071e0b0a120b060c03030c0313050f0607170108031603020c040606020601051c030807050d1503050a0209090c030304030305090301091b03060b 77
    0x48000326000341c042280b00001c2400390074100b92440d9200302c0000440c4c540b0303514a20842165004440c2c079424150b560740640304104031031940301d0003040821205400c0d424200c803001d44680c42807050581c2803281409001219030101c40d1003004041c03440000d034451200c0c030f0000d0482c043c50002016103d290a12030051841e000060352440d540c1d00b0b009604550321808082083e60010740050400080c0c12455400642d04002030298038550001401290504103805044040070f940024507100c1d4400062001107070000c00d0f0745c0ad2041e12070600a918541c0e08081c0c1c140288200195040740c1000d8010400c01e400040f1507049501c01c0d103140c95441c101690103004003904401c024005440e0320046035a440c854000f510440c0200000000d0399034224079608184145a40112144d400a25103001545040c150340f542c01200703074001c0c2002c0088800002d80740c2c03081f0301000f010711074007040c0c0900c0c94a09600c0b1f40c24182d0310132105805407084001381007a1030490322046514070f0800c078801819 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 43026866 1250 43025616 43025621
    0x7021c140f07150c1a040c170c0d0605040c0503030d1e0e06040f030e040524010207050306011a071218080309090c091909020901020f010603050d18090f02090f0103 72
    0x100c82032a000c00050300107842e01104e104440b541d042d519510011480f4613511108503405019a105210549840d45041d5210102c07131410a08000190810654045541c031541c10401805a211000142c950340c1d0780341078000f140068000f1038252001242c4162030030390640c0030030048a01042501144034030068200299a009401020031b500005c0104000590850040c21241d109003403101d12a07806101003402c44da01221504a401d08035402c6141505804040c82156282031001e45400d03820400829a1a00c040c801c0304088099290f05605217820141a520134542c44507050340c0e04900100b0040c910001c100c0e101d00c0e001c0c0241c0e0009401d1030004202d50070000040d0000e04256180d00b900d560907008000f065800a042c444403628022082d0754003030141810b01c00040e04e45290f440024501001002140c003d40c0c0b40c1003090022a60000d41074081d40c010349000c200340107080307081c0e8241400e941c1c81100388904094038a144007100b50041d141c0507105a0300c195482240c44011001d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 43028116 1250 43026866 43026869
    0x3010f120c17030403170d11161101020f0102120103020108100e060103020a1b0f03031a090a0c0c0c06020606090a05060d02012d03020318010204030201050d0207021c140f07 76
    0x1d80030103a40e040000c507010349600b40300c81e1803940c01d0b24186952a1903409008008054480001704009501071010115118030b1030348141c000c56090610101d04001582c00041ca8400740444000e4041c20b45980c0c0300f0440a00d5946072000251344075507404400000c80202030100302e01040c84400007595031111128000c00301e07901518034040c0c903118840150000d60002100008010b42000c4030484801a540c86200140c4160340881e004146418002c08880102c00f807289180c110072003110490ba500610143c014000c824002120b92018005680050800c075008180403c0c14100240b071680208070b6030702c02c00040d2540c5c07c940d500d07080440201c030012252998052903038412400903512442d07001e91074040b40e454045440b0410510f81c6c64081d006000100029000420841c4040d07250880030b103500101ca00a40c10141194006001c60181501c0320000f030740c0c04100c41c420740d618454006140c00c50106514200d04290030100c0c500b00d400800030841d4821040910902036000804a0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 43029366 1250 43028116 43028123
    0x8010506030a06090305070215030a05060406050a0303180306050c03090609010b100f0207180f06080604172d0705011407210204050301020a0e03060a06030f0609030c050a050303010f12 81
    0x7410407502d603900d43c000c28104200350700f0030909020110040e00d07544880d501035841404035030b44a02c0c2c210041c03000d03078000a0000b4055400d1860801440d11600f407294241c9a00d030500601e9200408140030201040743e001400c4682802c0900c80c88900d807000440c042c2c141001560040da40750311170142a140490442501700b035140034071283c004d11039850503080f18039920544542564604c843c04d803450410041a40340c5580e1056070401c110a0300c00e0000502c665005445285480e403507000283d00f0300c00e03134221984000180c80d4103d0800d80c1c00320b60540c2d18600e0010302401c0f46011001c0307540004200b240e1701e600e003a604517840c80a0380300c128450581c2da55100b99071419500d0049540c2c070510690f6207125000e21000ca0310756428000b070320281c0c19550300d03c41c1c1c07400040101482d05c500a00303600106480c050041c804a810b544e00c001001d9000703100401c20381807507c0c0484003141000d0024209004113a1b0380402c01002200450484040380507030f4004c0c640714544003c54000150008 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 43030616 1250 43029366 43029373
    0x9050c0d0f02190801050307080f10051b070c030c05031c030209030c03010e030307020d050301120201050a11150f1e0a05040203011103070906090f12060f240e010801050603 76
    0x41051540c011005540361a880541001d0030040c00e00080003507200f40101181134000140000d017070410000b4020000e150080c410407203460403094840a030b406c1e2880e4882c4c0c43c0e0380002d11990030074000c0041103010307802c19a07039010035080101221035140411074580c8aa4a000503461500180e1400c0b00d020003a401385850f80001c130150003d41c0300d0085160140101e40000405580a01c90080700d007049802071035882c908000002c1c01d1a0b004104581840024001800925041d5140d03420240c0e080c05d090b9134540d0001c0040e80c4402c00d100159940380b18129104411320301680c0020301851450405140725296007001c9031444c100e000c50b0269040d00c40002850000c441d400050300700c0d0000e000014114280c1401d40901d52049980d034002c2040841c1c00c105050344500450010141d114940b420b82e07041000c1459960000710000e400b013611080400b01034507199000f848002e5190f41d40058820071007885040b44011403180e0700740040050000144404180200362003490000c015 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 43031866 1250 43030616 43030627
    0x3060501050d09060b03010e010f140103030813050307080301060c05010c08060d0f020d06020a0f0f1701030f03031104091d0102090a031205070206070303050103060b031f020901021c03051009050c 86
    0x400c0010011070f60b0a6441c9501c550501680b502e0038881e07400312207540e000214a809501450500f80c0d10f02d0300d00c810724059110010400319900c03c40c4140c0007100290902040509800d10620f50300410401405c202c00002c00000c0e00764001d01e0007200c1a110724004e01a52100380c800391103000e01110300c190000e150310705000001e0118207280840920090011441c088d0320303111038040f40c100c50001804680c202c1e511004280c2c010300001d800c080d0503d0021250103d600c44c00e80408010302c001407859102d81c2160307040500070781004200944040255480d1962050345501401000c0c1580512641e4001030813131146043c0220b0b41070316809410061554559900c45102040f0500d22404106082c094280169900300003050407600a43d00880c83d035055050007001ca0b058071180c02e02c260301c0020170400500381d6001410a40342e020314010b17212504140141c0c1004041d8800c00c3d41c0724842004840711541641c4005d014a40301c41c000495940c0301c1403110b08070340d82913903010302c0e8a40601c403 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 43033116 1250 43031866 43031887
    0x112110415050c070b030105120c010c020103090f1a100b030f070f120603060f05150f0f030c06040806151e04020307030603080d09030e03030a081305070b1902010605010306050105 79
    0x74080064801c91074080d2400c101181e8440c00c14029421200c10448000010000e9103445280541a0303074014020b045504606000a0300f0a800d05400a05041e00c83c00d450003130168a504480ca40790300070405072000110740702d000041c800103d4900c03454a1840802244000d507480503640b00e002180d0040d1215218004282c440c845007145a808108a107480d108501440e406034000840c440c020106000e880301168105460000382900d80c08010a0034510695541e04000c564804095544020682c1d02401090410018000081d0060342c006400511042c001403035030300c25100300a450b00c1c40f900c0d003c10042d0b1003d02c0803d40701500c1010072880458900740d401950000706504002514540c0e940e00c2036040d42005041c0540c1031b070b40e021001c0500d6004a56151901c0048014601e4500070090140c0000d102525448001120803204410040f0800169028003810121141c40e001d06181c2c501a0044800e241c80055080030800951540a4062401918016181d07075080144c0303602c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 43034366 1250 43033116 43033139
    0xe030c0904050a0c090204030309050609030309090402060c010c1707170403030f1d030c06060603010609030605130501020c0703050d0212030a05070c1202100b1801030305031b160201121104 83
    0x80042e0390030b02070800444001841a807040c4000d00b010138000d0b80311440c0d81005015600140e002034003c4100300540300c10f5580100448404290441c1d0001c1d40c4c0e2694004524a4012154000038561a1003820a221078220745000105601e003000b44043e585d410108448154101c80b0039203040507860701040010380a50809501d40660200000350349801c00032801c020f4613107209080e4281c100180404085805014846e40014141c0d005451035140030303401000d6500f144400b500656465010524040e01c100d034990140307070018000d54440f00c808401c42e442c1c484503c811140e501c00d0723241104c03a00d40046504481c04280c40c059a0469842d4000b84000d13105c020405d604002c01c1c204d0350000128103505d050f480302200d60060030704004c0d07042418100c68031550308602c524045101f09012500e0044c9490550b981031400948989648028034580d2010410040050300081056203642c242a0034000c8094003d984070006400c1ca45001412650343c26001d01d4038040c1000240801045d55 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 43035616 1250 43034366 43034371
    0x9060b0402040506091507060501060e1008070203190507020d0b060a12051e0a1b15050301050d060c05070f060203060103050a02070506010302040b030c030a050106060801170601120c15020d02010c0e030c09 90
    0x80b0b981c11f181c041c80e5600c42049403400d822120100b5098841c4200d01d0800380710100b98440c56090076401800d0050000c0e40da030240c40042114038012403000b0000070710480542c0c14035a405442044500c0451600c80d40148040319224000d50380ea40e800101e0b05980c1d0701d0049070a030010040c05011030841405000142241c00000c00381c03043c40c0c1c0300c81c00104c0c1d00d0400c066881241500700f079410b0411041c085000e00040b901801c1140600040c440d65441800031491203034060790011f0302008401050301e090281c10301c09095003604e000c07a4010b10403e40c004610410302660200b0041d5140c4203844228092440040c10584c001801800141060380c0030321000c000003001c54680d1035000c40002d18190b510801160b10f80d45a40e401c0000d02c6d001400d490151214001a8880c480682d04c05a61510148500915012440510300c1440b503019074032005844443c5034006000c6905001039941c44400351400700661a100105058501c580004403503000010050304080c1407180401107001c601 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 43036866 1250 43035616 43035649
    0x10090308180d080304050105180a080f030912040303020102040f0f060e1003020f0c210901050f28170106081314010f09030c11010503070e0d0606090c0309060b040204050609 76
    0x70b10022000c1402c8001440c801c2e44103c0002c43c1d5880c0188925a10480420b01b007101903000d0480c40300084c0e45081502c40307400182011035101e070f07502c0450501d00303002c28034600d0703004030009808000d040c1d06400502c25a0048255214407035542c19111512006500c99400082c04400c107200c00341c070703290548075615002481e0241c00d007558035004803441e0b8080320200e9880e50041c0513075030101c24140302080f0074101942000341080880c400107846071243c00720015001c1000601040060b0a009450305034546003111032081c80c581c2000504030213400d944800304c030454140006060f521401200e80300307040c804500c0c101354200d980c0e81e982c6040c42e415015010b54071307554807002c900c001d44500c82c1040c2c020782d03c8800c02d2446042540b5800c00089000c1d04112081042100c3c2a400444c1c66044800950742505070040d40c0c1800001003029802c03205109080c403110401641d4180c00c80c43d8058000c0c442003000340c1d83e041c2004120311032072044540140742404005000c1c50a8054644090344 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 43038116 1250 43036866 43036879
    0x106050c01060e070e030709020906091002071d01060806030d2003270111030306030a0b06030307060509010b0f1903020d030507080a0302030a05070315140d061a1009030818 76
    0xc80f10480c01895204482d402c000588020440c155071508001920041482c00c000310f01d07050600001c500304d0301c12880d006018190000441034024420856800141503401d4040074407203802c0b4440c2c0c4400b03020f124840000d0707000c6001c00c0c000d10700460807028100745a01d803d0b01000b800f030341c0c4080817440030101e0b22140c007050103040e60880c0d4006404160b05c00700340d0f01c0d420408043c00050b100c0407a8110062180c1d205004000c40742c0c8000440d001c4090300b00706440b005a0303500d40080c0c0b941c45003010080c91a81007509000c2404030540100e42045812245542c4120001092000c03610441040410b009030400d010000f5040034102d0500c071601906c2d04c80e2334244a512600b5456002881980009a0000800403c01600e00c5401e07009000c0b443e062020714420682140f0040f40c40c021084107030071680504040f55a01209120200e600a1003400a030906051590100741e5040200340100c000072418180b103441003001905496002e0020340c00c010b002210300d84212000c0440c00d40050 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 43039366 1250 43038116 43038119
    0x6060602010c2309040e070602011b1713020301140108070b090303071709120a0c0b030108060a0b271915060c02010905040e03030601090f0f03020111010204050405010308071b0e0106050c0106 84
    0x49036805170206c0300d0f0194005140352841d10b40700070300b11180700006840075001c69a00500482d800300e40301c092014000520525038036811004c2e0303064803855000962547ca8030b071600f2041480594000c0c101e81206040d25003540c1d0307940a50703125216207802031354103030000c1150100003407404c0c0c0c0e556600b80034440041d0410300007401003004040c101c1c44190a540c884141a4108502c001c00d21020303104510003c2c1c159450310000301d9841001070305042520761982c0b60010562540b22107201e14003884c5d00140c148070fa004031500302c0700070251a00c910300340b44102c180c00341c0402400340c01e070481039411034444c8061070208205e030034118055080341007041600c4002140d80e502d0040c0070143c41c0d5070020756a40d003040300000d40024521703480f092641c540f030070003000013548030b13003131003003100c1d02828400003500c003650392503009105541080364402d19000010082c041c90304045c094143c03140002d001e921441404c86c102030b900f0b6108114900c0c030b103440103002d480e200388003030706d4585200307000031900700e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 43040616 1250 43039366 43039369
    0x9090405160303022119030203060d020405150306060d021809070e0c19020f0318010306030c0b071205031003030e0102150a0f18050604030c0c0317030406060602010c2309 75
    0xd095503000f43c0040e4800709400c1c00800d80b00b490798804141e03180c175941c50b10580c1042584071a180404031414168080002030941c0c543c0700900318001d900810401c41c510b084880250010450f041d024024030940c4c00081c0d103800d0a078004580140c00800680215501c1c000b5444040d600809280050048681c0007c110ba140300c0b4460140144c403204645480c541811510002e12030161541154001e2000c0b21754020041304480d210000650007850f0720200e60f0050300a4099940000c014100c041c50000c0c41481c1c2c500a001582e00c01c0040303a4170b0311070b85001190303523020030703550710707200c8003443c0410070010740a140c2443c4000b0040c015100281c2e43e5108030b0014500807641d1061158481c2d09036849400c0034410150f05021706452003400840325210385a503803100030401000c1c80300d02980c0303070300703000700045014010760340300700c0010903800e851b4014602c0e50404c2d142281d86506000d404902c241c018000c41d494450241e0303c032000035003131204407554806d6040903241800340c20090a1010b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 43041866 1250 43040616 43040653
    0x6020307170901020a0f02060f070503060307080a0f0605010e04050c04180203060f160504060905090403030b03060108030403030806181314190c09050c03040303020c07090204030b040501051b09090405 88
    0x3580d0242c001600e074841000040c001300d003100c0039503085402441c02c000501d40070541b2683c100321035281080e100c3d075454020070316155180d00700101d00c0c4960f03850201000000b16200d880300e0b1264006102590b039030140032601c0d10013030b100102550080f030540c0301c26003820351028071900e0078240c1c0100544c0498001c00d090002c182c5506100711803101c20445000d5800c0c0c0c45080110703040c6880d618091802900405200003401014800d24200000c01c0c181071003900010000b840040641c2c20390b594400d0410b980313910610044001c900c40500282040c6407000321322650000c0301c1803128003a40e940d202ca001028009074215502d4810251403c3d41e14000c00034505a5498211000004140c1e0701b44043d289400d54420304204d418103041010700d100000c02d40e81c00c1036142c1400358882c0c5c0d000c0401c508002c082d40003280214070104e0300105010812400e980280d0158000700b00c2525045002c0da00301e00343c000400600e0408202d200e0180c18060500759101d4061030540d21a40684e0003c80d04 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 43043116 1250 43041866 43041871
    0x30601030b1807020d080601121d160f1505041e08070b04180c02150a06090f0507030c080705030106050906070204060803250209060d1a07110106050103020304020d0602030717 77
    0x2a207040b503041200c42601003250750341010050070000b0042c5028800200041e01c503690700182c0b00e48480c2c11040200c1e40c1c1e280040701d80e0460702a0b03141c2c0d42030320300560b440320782c01d114140c000310382c824000840340f00403200c03002c00d912207a548510f02401c280007040181c0c88002c80724044c0003240c1c400a08008140701c200080c084034140d017661146070142d43d602d856000c2850352103140c44c113408004107980000781d40c0003030b41455520b41c6107503480c0c00f4141d000348283e42c0a001c00302d0810994524081c2150700080c0700d58070750b440410000240c1e56003169080000c03214180425000c0005001503400340c8054a50440e00602041c0703480c21303c3c0d001c40d0540780c00350300056540e0f101007401441141004042c14185a001803586079058158000400c021409418a802024110304140174800d401160322902034800750440c22070300302a00010042a145108415030754a0b02e14041001d43c130030f0084074080c0b07400800d0401e54030b03c40d441d400002e40c8003415000900050700d140c42a500f203a05520762 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 43044366 1250 43043116 43043149
    0xb190e1306090b0103020f0a030b0d0c030f0b07021c1101090c080a031e0c0303180f030e090106090608040236011401030e100902040b06040f170601031205030601030b 73
    0x1982901c0e00d00b040d415203283e1501681850b005100c0720a8041003041650b608115515005c80e007111010b01089a60201e03800140c81040b1011010080c411005d0420840314441e012188a954402004a88800d4502d40b07101c80c40c0503030103807507046078424010f000d16440f07800c0c000a40803d0558400ea070b00d0080d41d1000303441740c1221901009064200004800e0b19088000483c42c07041c00d81c000401590700382e80700605040c1c6d01c20040b0b14480c22140030301003444e4084141c910318003a509001d400e0026000b00c0510444142c00041805441111004129509502c88407080c0e11a0350802021700740c0403003c02c8a1208900065489810781d040885002005551208495042c0218064070030742c803044140c11b01d070600d030041040c9100001c000059841e85078001401c0b4220b4800940a05500c0c081507520010224001c03850000e054680e00403591012000315400301d0551515840740720901c0080c0540030031004c2403c2450050005681c0541c051400081000c40500040d204980d031840f8003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 43045616 1250 43044366 43044371
    0x108090705030d030b03070504020403150f0b0a0303050714030901020d110f0d1e02010203041709040f0c030f140705070209090705040504120f0206010e06150d020304060b03060f010b190e13 83
    0xf2030171400e043c01200f01400042d42c056140900b50384139040384028043c0161211b942d036640110501004d60b01c048041c4100400b034003641a940d080c000c1441d00200410b40c0d60403000c105012040000000f1a0345101d412303000380040d04040e00081c6c07a52101e001154442d40210b08034244c03507200500c941c0391090600e0301c4140354015800e1002592040501489041d6031040080c403001c6000e6114107142d019441c002180d0724184000031030003401c008111a10316a05248090200c00e800d50007000780c0e0f0304025403c01c02004a03c6007040100e00030340301c41011890400071400941001480326501614000846044076a1303480400c0071988100d40940311091024001c008031713503000c140c48007900e000b07100410071941460660440c250300a4145c602c1b5420311059040d80d15100816500e044401000440d00e914241c10b0850181c040380e58014420b0081d140081c06420000d208a07040e1404440c61504040c1101d42295008103080880c200340480140040e8590fa92012019400b05039200003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 43046866 1250 43045616 43045631
    0x1020f0601151215050f013e0303040206030112031e05210f18070504060b0c0606030f030306060a030e06160f03060302060702060901030915091505060f0108090705030d03 75
    0xc203603c00e4040707084812800d0401c03955840700c40410820950700111000d4124451840050361a0741000c01c0b840c079040b9904d4070401c11145032061440040007440c140850b207242034040c8035245d00c0202c500940c406000c5c00140a848040b031403580c2041d1103400c1000000695542e04010030300143c81140006000080310768096080603040402005661012817103414000c001d0000e048004040250010a00c60310107213070002041090700034000604100115522070f0302c03014669200348114502407003140003051490400181c00c451010007400610b0442e1501400c100e240da0240c41c1c810205501c4a46041c2c40f0a001d000e198000d0f0300120310b000840007000c8000c0e221501910100f0281031820100b00096100d0b41c00302da1855504440c500d50b644c1d4174400681c01030041400181c11350341e009134006c0d214443d651140560740e02034900355113644240808081520700890b80107400c0074032441a003003503500554107180c101a03841c0543d04000e4031240880d1414110b640e1080010391500740 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 43048116 1250 43046866 43046909
    0xa060c031404080408011a010e0910090c02010509070605040e01092a030507020606120c01030e070902031303120209130b0d1712010f0f06120204050d08031611060a090201020f0601 79
    0xc031802142d80c00900c04840d10840300181505080100c094043c1c480e0ad000101c0101c8038410060107440110400c021034605043d009000b054100d070021524803c0f10b002060041c000e1080e0b904903200c403414561160b0070004110060405600309000340034001d486140705803510014081c05114594000801c0d2a204030000d15141e005800c29000d000089a81955444007040c1c2c03a9003102c00b0b00f40811418030984065160581c0c941c4481607251001c410b011040303200d02c00da007002c68001da480c002103600041080c001c17441100302040e403100507480001c4042c503160b0060903410310300400c0c1c01160601c41c0c4401000100b19000c03640740303650015080a1025039880c00e44d000d8864500241e00e0681401c00401e0005194001d000500c80d0442d0800ea0300c410940403103000c0c20000d01203040c0c1008a141050141c0c009071001d00103011040046c50754035114101031180e03043c0100041c1341540b14415080e00900d50080705a045015240140d500d03006d04001c1c0c03900a104a082101940b4070890 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 43049366 1250 43048116 43048121
    0x2306030115030513031e020304050d0b010302180603062d07030605180618060a0f08010603060f150b16080f040807150905041104080a050d0f050c0a060c03140408040801 74
    0x1400d1a100342620121800405d030f2110314031803100401b4803464500084104141e255000c0c551091b548041c81b0000c21040014820b42c0c141200c2c4240da00d80426401100c04408406080312015010307880900001d01c201d4034011283c152406840b2103081d0707118030440381c06081000700c984401098540c00c00304001d04101c10380701d0303441980342c21083c0c0340d00b40840050980c0d88891940341c50f1001710740c003141460741e908010900800103604103084142d0784a4081e0302070011403000f5265140b812200700c10112447c010707083ca858100c03065590441c02d020b805012504107200d4016082d0080c03500c0000961568000d11001e0310000c403054071a031070710a40918103146504110075464003440c8900e241074024034001c1c140c1e0021103000c5000140f013019a4580e01480e444829280718045080d41406008101c0030084403240e80c6e07859000d032802205650034407030800b0303081e110b034003215a0001250050784107100003c042c2c038010510141c05002e4110182003604e041e5010613000504115050092 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 43050616 1250 43049366 43049371
    0x6030507050d0b0a0f140405010e010c0c020603070f03060909050a0203010605030304050a090203060607120f020c01141b030408070b0310141813050105010f06081e0123060301150305 80
    0x840c0c0c0030b410040150f031034054210025003c00c0206855803d4202ca403452500034185601130a40031004a28241c201903003e40030400512050b9403074218200ea80510450611528980240c0414a0368070382480031500781040c0c0c101e0f407080641d141c0010800c40791030701640e140140284020010aa03140c0109400c5545562103a03100b42d10821007000641c881d00720640072a407114100585a80e01d5402051b1944500407008141c4188081101005600040c085110030941c0d42240c00c07451980e0019503816151500c0d028560781d0a10145a1498003459044a080b880e401581d040c56514214980b0707000c22504407080c0482e02008100010742030701800c000804100c0c00c2500d00361618001301d507101003c105044110b4542c8400a0311031400d201d840e03070b038640d4850009c00403903968200c040f0003c0c1d05805031600040c042d40210300c02030207940002c000036190200e4440d55918015414038649000d030b04a49041c281d00c00759201c2030740c40d68003840c0206516070100c0510303192450010308440b0f00 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 43051866 1250 43050616 43050619
    0x702010f0c0c03020714030c01210903050c10110d0906061703040315060b040e07020c131e1509051306090b06010f0f0c110a0801020301080109022706060a170702010603050705 77
    0x9400c0d040c080c50342c001808e2005d102083c00d20b01400c102c01681245005c00c0c0f0038440003101d082c84001e008140c0c2c000c00900d202603590041c0c403030310010428010180c1c0e41c12403034101407100c240311956903000c072640080f803000d01c91107000521941d6000641246210205c5000254101040810505c4608641e80080506200003007060500780301501d105030080d4007030300025040030340004801500070000d000700c007040141111041c02132440c0e03402c0a8140b10040c0d0401a40c2a81050702d2411180030f00700000f2400e145501c5583c2c02c1c68054002000c00a1222400105005450340820740d0791180b50740450249172070002d1072401030009000403130307100c0500c07041019130801401101c1d48210504184da41c0400c4008401c200140007611110b0a0380000905501c008000600380e0015803007110100d201f51034110743c440390602113554514a565015403a241028001000c0c4c1c034010006208072011418000e0f09004274214003003658004480d102d0160b95100c0091051020410411009100 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 43053116 1250 43051866 43051889
    0x70b0c0a090e0f07031104171f0b09060d080403080703020a0605130503180312040b09030c1203070303020d1401030609050c03030319020c0c09070503010e09061005090702010f0c0c030207 82
    0x914241e603d03001000206030004265031100da04e0035a0400008440003400c824090300004180264111344901c00c0140c0040210320f4401c0889400701d050048080e12900100003000360703500c1d00140f00c64108080400c540c0044200008800180714902810000303020b68000c20399003c107440e00e581100c0000c2d040c0c0099880906402c80010400411907520008540100c840c1d000e202001c00d1420408820368000404089801300c1c111315a01d001d4014a5821021a085215940d051100c000d030340c03002080c0907800421203440468001d400800300f510480f000092190181020300e0705a60087e003040707071000e440d10722450a01c04100145d98042070102d001e5440d5040201c08030042e100c2c060a80e444080c2c0120f140140c40c20b0074400c030018440301a005144600d082e41004020780d209004d0309031985150004103a80c08c40024501d88500f2184d10514402420b0001700864520020440c100715900c80603800703138800550081d2100c210898803003405005442c6006400c00507036400c060036200 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 43054366 1250 43053116 43053121
    0x804050610051507062d050604061505030705090d080a031406060301051908030a050306010f090303050d0906090c08010c111606080403110102040b07020a050102030909040215070b0c0a090e 83
    0x152110300f001c5150400c511856a205801d161450290600507a041500220307001200403203400051156111400001c0400403550f03020200021510320340220110b610403e2a80d0309900d0080008580001076030408e181443c00c1e16000940c51020300c44100d84000b40415030341107880d01030190740000202e20108100c2842d00c500400c03d540014491684518550074202030070310030f50842c0c0707130150000c81c059a6881c0c0c101c0001500740d91041d10f1a80c005000d5001d01d5641500c240e80e01002d42c0e42c10323649c04c3c0c5031240340d064903805424019030a8038600da9900400e00010305a6250200070080c50b4000f0440b9441910003500e44080b07550240078682001148203400d000400e0300b0b00640b081803c0500c10350715242001c0b01c6600e10100c01d901c90303610004002c15400f1030800a440a107100311400788c1c40d107032500012622401501c032199007000c19040480c006151541d1050070703c2d040e0000050420900e9114030740310792000e0300c2500d00350701d001030b403561000c1e8400d400d0000350061060006090 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 43055616 1250 43054366 43054369
    0x90604020306011e032301030b100f151209030e0103051003230102070f0c0e1003050d081909060605090604090201050d020c15070216060f0210021303080703080405061005 75
    0x10311058680004c0300c240c3c59468401e130700a0b845902c400100c007250b4220342d00001c90102c0d00c50b03400c0c0410b035440c000b0000001c4c088860003c82d2026220580d801c100000e180034518804000c0c003e0106003440317100b820f4400402294131a081c0b066002e542c1e00d0401410440000d011524080c00c0c000150259180900125210904c1c0841600c00c9050b005034051a0105550081c09036400041100c940c8508080500c280346c603001061703402041c00801c02d80c0320013650003540d068501c0010910303001107400c3d10009006150440d4005d45006008450341c0044c0d02130b40c1110403920f412919259101814085820890605903001c2c2c4141d5040003404a50340000c2d003280101c0d030076a426940c00003040d070040d04007030040480000381ca00c0c18a510741448907019403645940842c0700d800700e03400180000e0041c8a46c0166681c1601a009400c44000011054001e540641488400040210400000200d03513400501c29103001e41e84001440c01e05160181c101703080541806802042550188a036 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 43056866 1250 43055616 43055627
    0x1020d0f0c06180510050601020102030f06010c0c080102030108030418020c0c0907090b07030309060e070f0501052802030c0d080108030324030d180905090601260604080909060402030601 82
    0x40031658109030350015841e140c024064082c0b250741c1c94078400e80034110341c100140081e01e076408036400e0382c05024642c1c3e43c4004a080380403c90301c40e114154054086200b65004400030031005014003044c580c4107848643d0380c2d007640c0c003c0c0e01012050740001820095810300b0600c41884502c12035056180c240102d2440e03655100d10710205104210031004220034900440c44900103010209a4940341c3c405c40c00e0180080c40752502c143c58040c1090300d040840c080101d00e13071081e614520040c0000d1400c110045955821034403090701281d14036025004003c85158040b00c622520368021582e6455001d02c1c2400d0241e41d0400e0000e024180700140410702c0c0210a0725071100b031508101c01416401d56030f0382075030721650908903050b001d00681005050f52140700c6650444082d0a41c07002e45079102c01c04001c803681264a0030704c2d900035000510601094410355200204107600c10842940043d11190900390281c03011070755040e00261098442c14902412030f4070210448046040d4074206001820 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 43058116 1250 43056866 43056887
    0x2090d141e0c0a060e011209030c0c06080613020c0c03010e070f0e01060203040e04080f1305090c0c190201200c04110906071203020f1c06050906220603140a0b0601020d 74
    0x14040c03504405c12030350344160b034655001c10f4a00e41c1480300600e68103024001c0c0340f9001090710021142080401c07801d002c0c40b020344c082c84010701040da00c800c0790350440c0002c0d00b040d01c0643c624000c2c203104103020360b000d0150b5a4200b4005018044192030032801c4c141e40350071640302c2c401005d016001080b5042d008010740d012100151105081035545103883c0d6280d11400c1c81c41c002841c408078003509a018602c1e01e2005581041d0340c0750355140c0302c0d142c10180500903003441240d143e20843c0b84075011030030318050360002403040c103201c038070204080c6450f03101052170303288200c06602801460640345400c2c010400016000800c482ca0b212050f80401d14600c90154003410012501c044181c540e40300c0ea0440d00d40c840c0004400d034482988240c006414510318101555680c1003a5010505180110307041d07000f50340050240d0f816041204c440b0041c80001450740c02c540ea0346003000070114000c0a10343d41e0000c0000041c06084c500d9150000f0140fa025010303904541c01035840d1000150003094940 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 43059366 1250 43058116 43058129
    0x70c081801020307021e090114030c010e060409110705010b0604030b0c0702010c05011109011701060819060801060b1209060709121b03061b020105040309030602090d141e0c0a 77
    0x103040050280060b480e601c54584003d4000e80400800d2038160102503c110741c081044480002a982e1407091040400c05585182d616401c11207600c0201d41c0114056a070a800152a5505041d5200c100b1003c03660024603409410303200044d8002001800e21070a9170100003252040c3c101402d54440e581c0f2039000034240c000f0140001410800d584c040c880380e8002680c804000d20040c0c41503100c0b08407a8018000e01340c081010305e00444040707103940394024103a8249507204e0009903905041440310302081244007070816990f802c0461410000c1c001c00f405028902c000d1640d401c00c0541000c08180002c000b038031b80381c01c07003401d10442e140d0210165085a4030108000c1410f211818181d02040300400122401c5001f1680041080001d800040c1c0d00166000c2da07050300c0041c40001d034242c41c0210703070040000728060310500016419902410f50139038050300307035200c0d1840c659a071036180c1401d000c4506030740c0c440c00f141c5411010341c088010320440a43c000d484801e0013040400c3c0080568001c01 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 43060616 1250 43059366 43059397
    0x9050c090d08090316080706080103050c010302030601090801020304110f0d0c0311010512010e04030f08010b04060311040b03040b060a1a1801170a09060b01080106050a080417120f070c08 82
    0x150500400b10103886440030024142c03204d40b800240a584600441d00c6410301d140a0040005029400b81c2c0b0b940d030407241c000340a80411603005004500948c0010304c0b02d070502601200101e00c0302c400344091407083c0d04c00c0070401001202d00d01080180d100081c030441c03103081c0c4e51214400007440000b1410480b0307480000c0200d80888140162018054081045841c080c0f100c00090600d41c21803d40d409207001e0384030b0120102000c0c1040700c428009016071450040108000c004540c0b203544040c90000001410904068a9800390211540159416036440c0e9182e01800568074084101d1801400c414074026010034030b1034108211030240b143c28400c0e8442c0e0710440440381e40036003244642c3c0d0310403510480b82403920100c0b0900402c900d0809030f402c1d40c6419801c000c0f0794058410281a20415203c071802c0c81c404810844804600503c216a041c200c98180601000c40c000501200d100c400c4c039009442c5850a00e03075020b094010b01020801c0044036201022920400c129900795a000880 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 43061866 1250 43060616 43060639
    0x160213020d0207030302180301020910050d02070c08010209010e01030c0c0605040503070203030c0a150c0e0d03031d070e100518040c08030f03040210020d02030d0b010c0c0303020703050709050c09 86
    0x400001c0c0034500d0650300040c00000d6100c00c140c1d0550042400c083d0b03034001208148251800d01d4200c6c0143c00c00540c0000502c1c0d1074610090140c4060110307801910409031034041305940380001032100c1d6011040ea82e4001c28203504568025100c0c0e000f42d06d00380b030104407211041c0401061080348001c0542981ea4501c0418203005060040707a205640145c200d83c1d0b1001c2002c00f8035568001507200f035a1006001c021200100300e42d014000c0984500d41e58038540e03404003810080c0398200a00102d0030315580f030780200a80040218441c04ca62001009002c40c60b1400840c060520b80090030003c10f448808014007050340c40b01c00416400700704041c1c0103403541c1c8500d8201141ea8554000310060301c00410400100d40000006511840c0309440c1c2c2c460401c40144142d0303881020100d000b01581051000e011041d0050b40303c0068003505240c00044a50a41c951080b40310a0744c10580050300908818007d120003000300a009068201c800c0107280790613048080039000e16010b0328400c0500b6201c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 43063116 1250 43061866 43061899
    0x10605090a030503160213110406110a0606030b01050a081f1d03030f01090b06070201080c030a09020a03050609120f04030204181a1503011a090705072102010506061602 74
    0x1e144000d981c0c8903088996844540d2800010205000d4080f44038407400161000602d0b500e002c1c203490880b20100391805c003800e2a400741c4448500c142000a10b108410002e40854403500a01c0d0041d4041c86440519504000500c01c9890194101460a40c40102840c00c0580b2001c018521840d0203d40054101c0c0e402020030514a001c2c08040042d10002c024001e00d801c8502140381240c0500384100075003022041840801d0103101030290109010b40700040540034031100440d80501700c03803000564040290700240880409400945817030b0f10420401441d0301e02000765640011052030340e1800c02c1c1c0810720394180c038415800300034061070303d50503122220391500e0287c0020551050204203540c41c0000d40d8121580300300d4040e860442e000415526500b03061003100e0b01103400c00c24032045c940204040c071680e12001390984080240401010f404a02c4544100603090300c00c10f44210419040c40000b400c1d10800750005124000800440d903082c01910300d0540320300da0640300c1540481145c403 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 43064366 1250 43063116 43063129
    0x6060e060904060b0a020606031c080601120b10050c060105010e060a1103090901090c030c1b081303080a020d0201051e011401230406090f050603130f050d030b0f01020d0801060509 79
    0x148403c01500000ca09174070181c2e004240c00e84240000e80c1120310b4621900714040300e01c08044a00008258107401107000e5510900200c00d81c044140c0d400715101d600e0102150481c0050208940025000301d0040c5094106002c231a0041c030007441d103807000e10b000c00c0020b003252103000702d080e06001501041c8406218140b044e5090800b00506800c51503070754000b220040c1441d013010070002840e00548805582c0607213000c04180181c007241c0e1300746030141d03503d4005a6200c02102e201410084c0c1c0300000060400c0c0003007008601da41d02520340340301030b041c1c040e082d201c0203802c200030200d810210201686192843d103046800d4046100d0b0f26a6134030006075070b140e01c4604001130b40645a50310007003131b03e9070800900403294555107050300159202d110401c10115402001d1b400b00703041020492840010099146141c0188100070230140f00356519803900200c185c0240201391038240d070240610f4038440f159070080080c00642090380700440300a00040050040500f4000007140c07110302c589400 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 43065616 1250 43064366 43064369
    0x6120f010501030807030f090e060d0f1712090d0203030a02031e09010e100902060d02130b040f030c060309050a021207030b09010e0106060507030206070516020405070806030d0306060e06090406 85
    0x440007080a56103d040c09540750f44100d80170760100350154101001c0030310a10441084440e000c0324071141e910703401c0070400c0d150a0400103444070700b1101a064041600101c244a2803070034010643e54810510900844103000200079203000d400c850300681f52107070003200300c0e0340c0305218140050f81c0350b44003030000985035244264440248201c10401c074803110154007800c1d00900040c100e0b4001245418001e06545400000a400c258140300789450403401c0d07000760614502d84415240815254001c03007120360040c0d07100c0507200f841d6040c10000d0000459110001d01024a02885010740e11785a40b0764440d140d99000f8002c2407149040e0035000400c1c410300c0061507000f040c00040d814036140003030185c2400c40b041000341d441c0407000030750315000c0e0046582403a815000b814544e41c0351784099070150010500b1144280039410920010b991314803809226400c1b40c4c44040084c1842c0c03091600e002000f142503000c1c9403030007006004060300921201440c2c84c0441b101503072081e140c1c01082c0900317034a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 43066866 1250 43065616 43065643
    0xd0804080403150b010e0f1f03240e0a020304031b061808070606120309030605060a0506040e0f01141e03030c0a030819020f0d02090f0a0b0a0909090305030612 70
    0x4640d4205600c02c01c3e50000d02d080c4078260385800d400c040c95420001428800440300303511052400d24628440500c1c0340000c0e9001d100e080000f020010302a21640400003c3c1c0c20051b0715140c1e01040c041544201400ca4002c21120402c600390b1910f542c0203414000c0c005a0b41c444110411180b40c10480d00350080d40d0901c05910f40c50540c2141c070714024065410600701102c0c0c07281011008698aa4244584482950036640e103842c80b03865a12003000414000e012079400010440b00450030380c4030180200010450440d880400e840c11140441e10004182c104041c1d00203000203c400c40d0350740058480403410184c0340a08641c4036100060300c0d52190540300152801040300750810f0503041141c407441920407a0740c0702140e51560143e01d04074407881d80309071260403042c0500f15502250354090600340901501400c810742114001848040865110074010b05000500c20321065100c0d61690003804510018050049595000340142c0002400c0074014181d01c40f00c0c0009940402604916084 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 43068116 1250 43066866 43066883
    0x4050603060618060a030e06060306060d08130806010e07020d0e0112150e16021203130f030c0506040b0601030b01020c030c062a0706030e0d08150312030c0703090e0103050d0804080403 81
    0x24002c05c0540a4100005400303118051039000585609011a029108000040c2100d40885156075041095000b544040300664121840411000710400480340a01800c00134144545448440285171030411001041007100f502c0c071460450740c0101040046102102c00030400c270304600b500244c043c04680c44a0380450045081c0b0240121554103a500d041c5151b0966440c1d155182c281010341c4010742e03100d1220034074200f00401081e544801c400c9000d00c685001854070741e964940c51b2902400396010344070015507a042c07005668061155000d481428000303007082d241500c0000e526805503d440780d00900300040c13407081a00c016030048050b0700141081d000f2414448041c596200f049020700000302e440e1840c140c0c0303014800600d280001d00c165071842101e13950a026140c00d12002020a50140b04005032000744070031100245208c0c2000c000003540701e80d1503090040113407120b98003500056402c4401400420350201b80321241401500303060f44140c40e2403501c001d05210301d5101800c0b811 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 43069366 1250 43068116 43068127
    0x50901020f07061a030a0f08070f0b07021e0705030714030c0a06020a020a060e0303070204271a010e0c12100b03010e040c0b04050102030d05130501060305070801050901020405060306061806 83
    0x9404d901081003800d1921940c08000c2010003459a0f50303990b0303c4080d011980c15410100020b07080002000d0305842101c55400c280c01903074031071901600650303000000d40c0154100241c50260522045001500c044c01003012a2403d408039468200d54010783c0a6030500114001700c54804010201000001400d01110184c0e213070070081d00d5540c0030130220701c107126074200000e14501c01c40381c81020b494010050341c603000b41b0380d0810005040000c07840a0001f00c000c061680940340b01c44030002c080c050344c0316a00c06805107038091100c02c0140c0001d5142445602840040d0300d494090340c888400506003805640c40e10300d8440b1b01c0861070341c01011072040010000c540181c2c400c101c0c500461190710500c40c01c03500c84c2c0140c1c140d80558001c1a0040c0d00600448180702d445800a0b608401c0104201d95840340c240c03210781c29680d840c0c0041d103d40e81712500c02c01c0b9100342403141543c4180c0000003142407a00f8040000e58030701c0007411043c03240c03c0c0850545108001c4031000c028000d0010696981e40 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 43070616 1250 43069366 43069373
    0xa0e0f090105060402071a04110402030a0212090607020a030c110618030d0e0102060a150905041103161d04020415080f0c030303010807030b04080c01020a1809140604050901020f07 79
    0x142412262a54154201408909581824000d032171046a000c0d4401c0341100d81907a81c001c09540040051b5032207454120f0110035030f2550310045000b41c041100c0507a03514103403d10010711031000340c85a25903074080d20402c18144d80c00b0074045011030341441c1440c005800340c10124041071000040700e42c4002e00054046000402c1420381a031007405505a507021038002c003003a07901e28108190240503030881000100003e055920819900707404c24010b11509071184810003c072603080320300b19040c00503150f006015103000c0200c02041c080300d824088138241404003c3c06404102e1000710700c0d040c0c80d07d0200c0e045555680045084071b440c4050341e501c0c2551031241c6640c0d84040c03250041980030f4000d44d580d560602108070b03410703180064010109a0f2640c0c0c0c8006228500402c00e5421031003d0001600d03c4400780020800700000e59140c1c021030043c1c000a01100055034080040d80c1d01e0704801101d69400d8a0303415030300000480b800501555442d040502900c030700f9040d000a030400085c40400c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 43071866 1250 43070616 43070641
    0xd020a0803031005121614030106090906020a170c04050603070c06050f0117070323010605060403030e090604050403020a0609021c1b0905010807030807031202030a1a09010b0901030b0a0e 82
    0x2160011500c54202400c138400c0144c81d00110074070381b00c0c519208682406610400c070200b1003640340240c0001509a51000b21000b203075042c100841b032254000514600055014007008140d840308440c0c5401c0d82810304048800744a14070419000b110040000340d03155004850310100c09400034424007881c0b410000120a400c2e090141d107030803003000324140c6a0800006440c1055950002440b180103d041d81302c504e01c00c3c28203031000b11395901c0d008041180d440b8140a44001d600c02e4459441005009c0104494100000c1c100350141c0c0c6400100408a940095000c01507600b01800061550f482c0c008254141e100b4024000f6219640c20b4010400c82d272a40c6010900d0304400e400356200e40c98500c10002d99100303209509550740203600620200705080010f0102d0b5129041103050031801c04844c00c141c0e002194065211070355044010561004000e5060844200311400c80566040c0b1025501d24003c2d220903030304250741c44d1401104d6450f0340d00039501912502031201401d192a00b094180d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 43073116 1250 43071866 43071869
    0x30c1b120b0c03060f0d080409240501021507180f0803040602060a02031006050c01140c030405011503120513030b01170d090608040201121509150f030803060d020a08030310 76
    0x40c0610350600065400c840b020580e80a95001030070820108001010040124142c003400d44540b501040002181405489080b2100c4415428005403076403031424100c40c2041540000d0564100b80259040c05981644042e44801c4500b001c4200e511051843c81000c482900a00088402e025010403450740010190013183c42c558200c981aa40b80c2c020b01069000a43e403892042a4100c0b0622000d4014400740210050583c0005244441055100c18605040c0c0700040e0000e0000309120500c00280102060041590300030301c01e1928603070758000c60025906546003004804100403240328644c20f40354000b1070b04511081c005584440100c4040e40b40d080c038a600e284103040d5001b84590045450404032105521400419992600152081d034109840031880d00d6a0305601980009100f40e140e0140540000000d01c2c2513090407106d18001240e0805401c1011088007000080c1e185000c8944c00300060303400c0e51482010b440415a25015034104424501000c010800442c5200b05c1100 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 43074366 1250 43073116 43073123
    0x204110408010f0912030b01170f062706090a06080708010209040e0715030908040e2802130909020d1203090501050105010306031e110312040e06060901020a030c1b12 73
    0x120650392403c950f000c07504451001000c44100c071090410050280d0b00442c50b80006040200c00040258080b240301d00b0216016058a4080e40601445081c042c1071584001c04043d10b03603030040d5200c01620080345000b81854828503080300060800b54440c1c100500a01c42d26085503221500c4408a90107500548410707401580b9142c0c180d4072007039000400c0300884022141e015901a00004114083e003503007202901c048008000004007003540c010780038807501311103001e6401a0809009848a40304001e5031200090040c000d001054001450310400c40310780d80c000041d0481244086040040c604902412441041000c000d455415820041c892881203008111301d03a25400158221140d900010b400c00b0f1581c422148511110b100d11901e44d80138101000c3c40368056400a450310b00e41200300c8172652000700d010041e00100170003280e0030010440b0110b0801a040c40000d642e1003603c50040c0400100c4000181400010132109440042c021407a4010b180c481007200200f2125503000c4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 43075616 1250 43074366 43074371
    0x1b0606051c020a03060b010516080a030c020d140d0f0c08150406030c0b03040f020604090f0b03070b030705030c0d02190224130507051e0109060c020307150309020411040801 76
    0x446900001c80307080a0350781d03070040044500e5825601c0704802010b41c00c40540c10700808102182c0c0c2c0364440b2141c40100c52090ba1110f43d00c2d440b50200500b5165900030728000c0d54060300700d41030190f0b004090240d88080c142c40141c0c5403020a1400d1014102e680c2c9030b001c07802d01c0c050f10a500c550744480003c0c80351065200c40d00021400e03100340300c11943c0c00d100103401c100302c08100744000c5031008001c40d0014002c5d5071402240d61240c00107400c0350f010340e00400c3c5903980da002c088808035450040301c1070b100040b409070009a2604000420600c00201141d00304800080010490044407051b41d408285409045444817942c0c1c0c840010a0a5101888003510444032581c201281e280c04182c2c40340035584c0320300c106803652034030046491a41364045803030f406408070101c0c0e1038030740d0102004884184140c4004040054002601c440103d400500030070000c4026400940c4000a150040310800c00041000509260b021002852400340c000d6001c0c1c1400142401c1c111100080e0050300c9021008 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 43076866 1250 43075616 43075639
    0xb040501140901060f17040602070b07050d0e030313080702030a0501061202040f020c0c010e030f06040623010303020a110f0909060108061f03021005040b04030c081507020a0b06011b060605 83
    0x64500001c217104001c0080c6940003c292031810070a0981d40040c410080503081c22400d0392100300000007221002e00041000c2030741e03807102c0c40e01e025014088110300060362450408500840000d04e4204024100c003000142307000864508105000c000c1c1d0300107008000725500c1d1141c42caa06111300314180d1241c0d0501d10030b4020443d282c0308031141100e8642c01402c02c600030500541d03822100454543e81406040410081402d05000d00c1e40300341d2242d04000780c1d508041d040c8203440c1800300c0840041850450050002a40000b102242c854100280c4c8a81c040d100d000035103003220381d090ba83d42186110703040c0402e0590026071175050f0b41401c401c1e0f0720170ba99680180c45800300c1059107058041d24080042000d81000204d9000c0741c0168035085107030a4641820104a41c440c0d4012190242c0501003003003690400c0c0040c513100c8400045003401d07820201402542c0750183c40001d0315050302d200200c3c1d260f03800f960491900b03409000b001041400b05040c00c40040140e0310a440c051200280b5 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 43078116 1250 43076866 43076879
    0xd08070201080a06060e1210110c0d0306030f0b0402040f0f05040308010602120d02070503090909030a020d09050117091e010603110d05030f0c0c0d060603050c010801080d0507020102010b040501140901 88
    0x207100039a641540c51800c80c145c1d07002084810824100c0c0800c0c240203640d00c1c620044070b540601408a278200c00801d0ba030740d00840b080c5160045104801c0105881c1500034000a010001d60501c240e42201208d0351301e40f203600016005004120445000031301d4164565035000598000750321590203902c90521507a0303596400d82c0c036491030f00700740d022402c010005e01003045005c0c0c3c040d00b1190300407001c4038203190080d03001c10308401083d10103500035440031481d80b1181c3d034100400300c00d50a0a20309040d42c140f400c80064003410441c90a82c0d44030720041c1c00244644c60401c010b103d8034184140c0d50807444d5040d4480b60007401940010b80f244600f004008000781800a07403a82001d521800443c50024996041001c0d90050061903000340194024000030380d9401c0c50725844207016146c0014203500c3c42c5031003454072444c1c0f9507243c1444195001006501130201d441040710fa500c1c01c0046d565913251004138014110012425803051a01c3e001048005001d41c10b00b1000106540800c05039803141c8 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 43079366 1250 43078116 43078121
    0x8060f030607050313080405042409020405011b0501140a0b10020a080703110a0b01060201020310090b01020703151805070302040b06030c030a11041d09010614060306060a050403020d08070201080a 86
    0xb101200400c9080000c260f03c4044d000081494038054000700b810951a10000b9007601d10600318031102d0300d14213034140c9900e00c0d08032444000b0a4055011843c143c0b4020010305901c0202006900b9545104546800c0c00b0083d04000407900c3c05120718220740c642819032200802400c0102805a40b030380c1d810f050351a0001400c00780d219007044129052900c566000c0300c1d14031009421122a01031807400a001601d20700c1240e0203003010307030000740c1c03289000420040140b8141d400a110705d8105260031076240d801043d07020960b600912803409168001848001426626448800316046111041c06004011648505403031084805000d5450321408020142c0400c0ea09071304004410008102c0001c03072903200c40f004030b002d041282c1c1420f03900d81d400406600c000c038617450703d0307031024080110301c00d000c3c40341c40094100c01806484801004010036000d01000b0821401820001000c0240c140500d00b0354001f1b41c0d0040c142c0091075141d142000140d0416203040b400f103204600801d20034180350 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 43080616 1250 43079366 43079371
    0x70b04080a080304050f0d0201020d1503030c030f050c03130503010b0f060d151502030a0306060915050906040302040603030c0318120204050a0b040c02010603050601051807050309011103040308060f0306 89
    0x8180c0c80555445141240d4406041217443d03100c3d00d040b0310901c0000b4460f0140009064000507110314090003102e0580700069006da5101a0021050000a41252012454581628000700c0e003003d00a81940c03e841100341f514403d100c04114150301c0c00d541b07240142610030590082c46041400c000384070010300c00c070750f49562044061244143c41c0901d50f00510003035009040c10710302d490741c98054001e20b00b44254580e00581000450390b607a0703a0580a4040101681e00c0c000c01910710b40a55440303c06081c0c81032004201001030090034543e0b80005aa01075900100104010795907864060b0091892200c12004507024100090080c2034410400c0100d85400c0d0b5000d07032021045c2d003080010b100040c0020240c1e03a4545c01c0c0310b555110b0703100704803003c0c1c912380002804504504041d131400c04140d101c184a04013807840700da40b0b02d41a000e126001011810080d490b522403039400d0b409011034000f02014481c0100030482859031041b4024020750b0140e80d40250040325034213164681408 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 43081866 1250 43080616 43080629
    0x105130311120f0a051e0919030201020c0103090614070c0c0b03041a04030201180606140d0f020d1e0501020406080c09090103120e03031303021206070c08090607081605070b04 77
    0x600904100c490040b0040c6013808482ca0042c1c500004214110718905030204002c8000750003080090050410a0b05102211060307403040680c1403450340000c0da100060b41805041540382d51600c010405150040700364020328500c1c0d002140341100300102031950900b07091780c000300075007400103080d44101d00300c0b8081d0f40c008640c4155504a0314a00c800228042c1c4204d0841d03582d0072003200e142c06a5040c00807220310505001c2005803400d100c1d1200201107070b180398803500e0010b00b007000080c445e02010403aa03a040d241c034003003e8102e00300385808110208032100c2c8400303002100410010198020001d40358262035540003900e031410307411124011100003a8201c2080c0005001140410100c1e207026000e502e030450200e0118004281035401ca1501b039042001380c41020700461501051030398011000700014038540c545100003d1007d941814040d2200c1340020f025020740d200d19040b24449a00b00c40303510364440c0e0403055809041710207007095480b40191800030510201400407541100d10 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 43083116 1250 43081866 43081903
    0x71704020103021c02070c05030708070609090504020a030b040308010503150702030a0e040e0708060105030601140916030b0405070f02070b0301061d060903070308070c0801060302090109020a0c050105130311 91
    0x4440c0e00560096000a0310301155003107024007400d00540e18001404840d100e101c403080c40c2032071f1100b030514200c981c0c0c200256517000b50400388801a4406100400c03100d44010201303142d04d440c004070750076008540019011240c0c48080009050300008014100e640660445111468044101c0e01c04070307050740d0a50040e0408c1155000c0140304803a03000702d08400900015074a000440080d02d00840b0342c1c040d1403550003c42c0100700c2450140700c15401040f03032500d228031858805001850f0000c0040c075444100303d4050f003003182a486a4041d80c004000075008000038280082c010f0444211648198014400d5240c0402c01d02d4004041c0c3e4100e0b0220b840c0c00c50001e80c0507081903a00034448240a822402c140604541540d0400140c4003d5002c0d4000c13541d42c0b1500e040003400c11a0b0381c0c000407201c0e0b0400320100016210070806034112005040c0050311460b101400303c40101c18240040d0480d0309090a01203464100c40025454500c0381e141e00403542d0715695040e4480000302c40380c03d00602c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 43084366 1250 43083116 43083121
    0xf040b06011e080901110d060e0c09100c03090902030f0405010b10120c11070312090801110d02071e1110080103110111030d05070203040311041806020c03040b040306020c060717 78
    0xb801040c1c0b058004d0030080010909010546100e443c640251343d4506034503132601d4081003c40415401c0903080300f40007481d2881e180d0608041000c4160058415003003081060140b81031501ca40401c40c00750100a1080d076036402e141e860800c0c5880300740d0741541c00d07528058000085107030128601d120404652106400c00d030006400200801002c101c40307040c0320410342401030000b010300050014503c5034105e03541104440c54003c100d0350007908001d086d40c2c0b40012002441e010282500c450f06103004016035100c1e41fa14220244c036400140c40c800a00710403041c10f08014600c2c0122000e60403c1d1852108a58150811108550300784030160103903c0e0100d0092095100300a404c0d0404d000c03a00303c9251242128200b03041303c900301c403c2e00041c1c0000c00c0a2080003c610301544007003104072030034840c3c0d40c00264528030844080400034002a8000b1f035100c5140d00502c141c170b0082c041c600c191b6460310398a062140c040d600181c400680e501070031000030080b9000f810003c801d40d0842010000c030307a = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 43085616 1250 43084366 43084427
    0xe0d0f03141f0e1e090a0305070b150607060902011d061b010b0a0611070b07080901030e01060503010c03060e0a141f030b150301050a0203070c03050906040302090f040b0601 76
    0x109208114100700c0c9500d020b0116014009101c40e50098149004403000310201c1c1d0b5000c0000103028210980d030ba0046800b400100e648201038818468000380d03490105e0310f555101d80503401e0305407405600034070003041c81d1b0140601d6601404c41d460007030725105807180c02d5a0224894880c42c00581e83c0c803c800340700240d103840c01c040410b0a0700b02100000550880345200154030007140b40d000c2c00c00100315000c0e412078000305000000003850f25100d0380d41002100e0f42e07030101d28080c110203541010350314401700d011200f003508061f0041c0320180080241c0600c2010042c0502114040e1403445651940403501da500035106031040411103410f5a042900c41c00e15008030040042c1c9040c510030700070000407010a4181082900414150010015030713500c5c40700307150030b40c0c00007000600401d1060040000c402c0d0045007002540d581403500d01d980340c820744005881c0b4061600080e41040041003042000c505c940501d40c00349008a0015070150780f080d0044a400c0bc180490300f108003916a0b079220134 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 43086866 1250 43085616 43085641
    0x1107060c030305100e010e040501060506070201081501090b04060203040e01080a0b16090b0d05010e1005010801050d03020304080f030310090c02070b0714100f0c0e0a030209040c08010e0d0f0314 85
    0x404034480040150305d40d218600d000d18142070704a80f02d00210032040c0010030909101c0d14008260a840c6141822000c0d000a0044078000b8502400c130b2030921000d0f12560f104601181c058400c0b10510350700c4070b403540002981c942041c020345500758560710010800301c0303002610003007541d480142030707680c0e558007203004120b98500c0c1e00034030a0150352000480c2d4040c044016024011000d100001d0a6143c4000000c00a2001c3c12055403005d10180c140070b1641c1c0981043c2c15100d056403202035002d1503240c00c03403a62296a0041c10380d802914404200f07001c0c0030009502950032403060b0034006031034041d041d0403995655200c00c0568030001003048203241000180445d0390081c0c0c80300c030b07515441c040102e0619803590b00b84086559603038103201c0c0e002c0d0fa52182c49940b0303540d803404600429001d03010581803461800003034032641045001404000b4a00b072000d000d480504028000300c80360b03800c40c95032072138403410660108000b028070a4806119100e28481c1801514003e452601c680c07001d00c05 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 43088116 1250 43086866 43086871
    0x103060209120a0501090b0f0f0a050702030d14090c0901080c010c1104020315011d0102060105062208070503060a0b09060d1b060801050301050a020301030b0a0221010b03071107060c030305 83
    0x10456041d12211100802c1408040c10380d070b0065001203026a0f0f24070300804080300c001c0501c0008450481448403181005c910b880d840003035103030700051070341300c020099295006131400044841d003425104107800c5511242d45001c0d0181104841100b83c6440c10080d58480c01d001d110300540c060200c1002e998881e20709184400c0c01082c200e5880441c0d0401300d026030f070080b94108440c4440320a08000795178011009034400101203009a4241070010000f500d4240c18407074a03100784408200c0ca01c50a40b08540700c4140750309821440320096544456036100d007458410103100f400380c0f20000d4480d000d103010303441c0b01150081c00d10303141d5602c290812964030403171041540c030181003a04560303014224414400180c07445803940c100c203614000c101820f45070010075142c1a240103000401c00140091101030300070203074181c0581c40e80c01044502c518090510741c510300d21a5094000104113501100450151b909652403400c00d00078010100d6039005d40d445010000b9041298280102c1d01c81c0c2d21040c0c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 43089366 1250 43088116 43088119
    0x20304050325080a020318010203040b0d32010e0906040b040b091015090e07080307020111010207020a0e0f07030504240f020c0f070f031104050a0e010f1b020303010803030103060209 80
    0x1468003a56450314121504039210350300259000045001f5854006144078008117824801185403a041103182640781c0519911035a076642c817000d201c040105110308510040e0710312070614080c24055014019101400e105442c801c8040401003a045003001c03c0071842550810219550f680703840c0d45031048081d00030420b03003035801110158070710f0b144103004189244101003882140ba82c14000c00307104440c54103980441d2a48985406c0083d000040242c0791100c0e02404d1100200190208a0303019202c2e40b07000139031082070290007240d800d11404c00c440c051005110010a2a0f441c544150100d40b01600e010b010422078242415600088003204159146240c0303003c96020840360035001a43c01c03401000c036094001040c058400041003080c2c80003090324281451810345185c07078040001c200320940c903000d141c503440001e50091064001c00000900c0c138008004108031120154000d02c1e13850707400c00f80502c466104602c0c503440001a0b90582d10b28130095031860b407865480a000b54040d84195 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 43090616 1250 43089366 43089427
    0x2060901050c1507121506031e02031018020a080406180c0e06030607170105010c1e1b050105040501050f090109080604081207050304110904060b0402160b01050102010203040503 78
    0xb01d140342024030000106403030582180003141050080900002900050942101c4c034041c14404d8040300c05050204980e602d0600044c004d41d020078200319201503401c03400449000005024101d018482000100c99110480585212450741080282e100f414210710016100d01d0200f400b09140b0760088500c1500b40740c00e40d50040b4241ea4140d500b61140e17124103210788500e002c01143c1d04040c03141d1030740843c45241082c1c0903240c203e030700c00102c903041c0611410001001002d404000e981600a0050a4950040e406200f03561404111580c0c18a102c91000c0d04104000a1154040c60581e02600d8050f110b080c2405160841101190088004141041014440003a00b02024401a03004600640c81e00f5500d59645607011644180a080601000010020000404c4420394061303a102400c0b02c00b500582c90781d08000004c0d10701c982503541d101e0310000c0c01901c2c442e070f00940d045010748101215080c1d40c0e40d600c01a4200d0000300c4014125030000c02000c507214070a91490030b0000490031a6 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 43091866 1250 43090616 43090627
    0xf110609030d020703120f080103080a20060a06060503150607081608030403020607020c01050409051503011112060303030f04080f070b0403080601180303090b180301090c0501090902070f0206090105 87
    0x40c0c40d002d100c0a1820250b00403070424414030141c020030354543c0300181400240d10310b1440c0c0082103898148005040c4c000b001c100d500e0703007a100360101500c1d68041d017404030340b0924540b030198035408240c0d0910481461300070006030280c01081964412240310b203407040c0180a550501c403950703000c4601140e55000800850035800f02c14444000000d028065803502ca15281c80c4c06031412202410714415503008454481460703074042c088800b42c0310707892004221511510310742d0748003419495002d9859402d02c94415103006640e00940000c1d5044c840c481266200d42d0b0034142c81e4401940c14600601c0c0c418002004500d142b00140710300003802e84154504112510707043d40d0000c1c141c40480000e140c40c4248001507a01c41c030b406041c0e010507410050303410726583c1d011f846916503118280c01241c01007042c3c411a0280200a041158054020300504895182c81020348165000312404034104900200307000031315109603298240d0012540ca01420f00d17800704510f98211441c0b050400804028 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 43093116 1250 43091866 43091869
    0xc18090b010b120c03040f0204020901030e07060503071808060601050f0403060501120c060503070804110a05090f180d091a2208010b01050a0203031803040503030f0307030c09030f110609 82
    0x501500800340d020307081e5260f400ca94411118480060f041e40c01c00e803001d1003804040380000255060321a0704440069454041d1401a4050500d1241051250003448000030300940c0000003188200680da4a5020700a40392007598590401400780d020700350b200d1800140603500603001010390380075240150341030a959a0f110416588241c000300954480c403103c0a08025800000101500160a149040d450462001001807a0042014092206401c110355446e25030002040203024090111607181c6090101440904001e0301c0c0412549180104203004201c08039014800c200c0a0780d5244843c0e15110003100c62840440508040c0d80c01007000743c45908180c00784c0c41807411301805c804c42d65890502c403c0d00f11071041640300d050240400c80e43c4030803135004c03007107070743c0022504041d080306c990a4441628500403900410b4043c0301c000b0b40c0e00036400c440c4000d1489200d00740e43c280320301e441d8640121344103585440000c003c2805200400c002810303420b8080d0a010000c0c000d541410907a00 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 43094366 1250 43093116 43093133
    0x40b0a0207050715020d08010b0a1d03120c1b0a1e09091112030f0d1812020a050705010c030804060509010b030313050301110f03180102120a0506010f0305040c1809 72
    0x24003130b2a81c84400d8101402940d018851203022142a0900701e00c00d61400159100b40c0c0b00720b0364040c04024020201c24901e00b540340310000300c014050211007103500d100080943c0c980c450100c102091141d14500d5901d09181440c0010840c400340480703c0191524000c01451b092040441d60614580c001c040b810000b20b01c0744443c0d03107001d4425880c181b8180b1041c046c1030f904ca650303202d100e60800c0001b071400108040440d101e007200d100c0001081c01007481c441d804200280f00080c0002d000d144019042540010940c0c80d10340288207440c0a969030f10300549444010b4100140828030041c00140800c119501c8594090004c20000c80d01030303090780c0000d04551201c0816124480e5042042c04141424480c10f10381e072095001da50301d40250141900643d0200500f800c03943c4241d000d00c4d4028000070740540c1c0ca00f41160780c04004500b0300720900e20240c0421105180001c1d020301034202c0c064806e0040b60300554006410b180d1003410a900d002d01c030a00824800c00342521251210001081113 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 43095616 1250 43094366 43094369
    0xf0e070306081903081b09010c030302040801110c06070f0c0807110a030b07030e03070218060307030803040c03060c0315030611090303040b0318030403050c060a0e0904050109030e040c08040b0a02070507 89
    0xb003529180c2c2883c24640030b0074050002e00082c5224a0090004004142000c00c6a5205009081002c00058a850308034085e1042d0341003441c03036508292a078a079220681e80686078a420060598406035100001102c1c2051200801b41c00500d08040b5003010031440401498558064030001c0c0404c07800d50046282c1c5402907100b142c000303e0310410004460b600d4400c0c1140d8042000140d0b141211903000902003202e902004055a00c003074000c110656001c001201c0250340c82001248c0300d15103820800c100211910040e5001810109006a00d5101e8030403440c03101c0c210b080c03c1d80d0090079520340400400745270012402c400e0003003181d5085607400b0409480101000c45056559117407443c15440803065000da4901154000e100910000d00003080034040c0c990152610f9823141c52010b01183d0315000910019041203a1905000c00d100064107e180b0b07a6009442d110b03050007440d42444116020300903886c0015014501080010310340c402100e400445007400541011000d89400e410110325 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 43096866 1250 43095616 43095643
    0x60806070f02010c090803030f0901061701150605070f11011101090609050c060f0a050c01020d0204080a05060f090318060c15040b0105061c0b03010914010204031b0f0e07030608 78
    0xc41d4200c0c1c99103a424090344040100030300d003d804c114580b9500075964040600031400d03141c200c000203001030009521050080200f1010b0702d2201c2c18220f0317094002d0103003201f1140c0040b00044040f82c001e005104035580ca81d400510030b80c03e001c0700d8845041d000d0300e021100e0f0400c0f003c901d284403011401d005a004445c02960700056131001468024a04000004806c0c00f0b504103000ca01e03580000e800a8490320151820042e955400007507141c0c0c028420020754200c0c5501c04903020561000000342c0d0b249061007042101c816460b640c03006007042c0d0782212000c9007a8020802d8a0030425084001d088607000035000c20b003001000305800d41062509005501c1d250040410001031121066056005100940d58503181000000c4414000031603440c9a00c0d00ca80c403040141d0141d2000d60001f48180d4204144282d10241f546201d4080d51080c40249c6643e0b40300c403041d491011141d040c1000302c40c181000d54000c00d00d4002d03420f02c84c002c0103000b0300504da0386200003e4190420301008071800318 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 43098116 1250 43096866 43096877
    0x201020a080310050f100509091003050706050c01050601020714010c0c030f0803041707050303131509051608010b030c040b0d1b0510021b13091e0c0b030906040f020406080607 77
    0x800342800b86000c442140341b8401c0d2081072a45142d507400c1011642c00300d00c1070346c240344160f0b034050306052510315a0348001e0061086542c00128103030310502030040c01004c04000e0021303850f10401203a403140c0e44d0280182d40a00110100700d607600130b000843c2814070440d2141d011036500d8881340e450b00c0d001c0d001940c2c9400000304100c01c01c0044107a0300000c03c1d070071450504000d050380700d080d81ca01004041d0640703040403140d00c0e0103110801d8410040d107190244148401240341c41c280391651450041005682114030000c600540b06001d589000c1d1400790050190a030007900300301c05408041074281c0c0001c03050042c100030a1b034035001c01c0e0b11881ca800a21201c0ca1621080c040c45e00c1881d0106011500a00d00700f2284d911501e07a003c43c002422a08541403294050f2144000d080421005100d071808940340c5da07140c10107115400d102806900001400707983d400c640000303848100c44024154111a0000d80000c00c00b5071020a8140094000941c06446541151820000303469040100c1e5 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 43099366 1250 43098116 43098119
    0x1f03060e2502060c04030f030507060c11011d0a11010905100f08010b0c06040b0403110f010b0a081f0c021603080d0e0c0109050d022404030b07020c1302070201020a080310 75
    0x7441c0da00920250345144024480f070301d0030354a81a028001d85c000108240c441c01e103201e003030501c2981960103064105c40d0822404120030310140105800c41101e4045500348030500c0c42a0280e03001c648030200d2290080d00c0b07454401c1e9121195428204801818011021000b065603100c80080b4200700156803501c1e502000f200f5030241000c40141d1005c090342c0d8081186c00309002d00807035290f4000da0320142090311500d07075140a0f07540904a52240c1154494a419080001d2054002c0021000281c030507081d1284c40d1000607803655528404501d0000d40b41000e51680c0c0010703880f440002c2ea0751f105841c03000d40342d041d600d5005805035005850764a00032605419820312482940d407160003004c010003000a040c00040d041100b1072150394892031112889030706640b03a4078400030b98045001e2500d0b01c0481540a8051a50014082650802c0f10000062000f42c00010400c941510051001d41c5103500c0c0c80c0b241c4060342c0700d910304038114040d0490301c07800a02c03004061806807008a5000c071005 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 43100616 1250 43099366 43099411
    0x4020409080406051c060f060507030c0b090c04050a020901020d081b0403060b03060901060f14010e0604090c020d0507020102070e0403020102071202100c02010501050f010c0c03150f0b0d021f03060e 87
    0x102c40105c3d401498004100407625a800000b01200c00e1424a6500e503102410103070348048114502600031580c1d50100310046c1000704019022403011901000780d81c840c0d8000008901441d2455409079000e80001c034201401201410351040140c1b5040d0301200d59001c44074a50f400a07401280c2054a40310352841c68030382400b2080e030004000c4001c0284030320380441c510400300e00b4401c50742c200081c0c8003159a940d11807040c221080402809103036030f95941c0d00c2504c0081585500c034000500503960080000391050089921440c0c059005182c440c2c20407004500c00031000c5c1049081d99401c02540c400103100c0d890540014400d50090700703001071084280c5003070390300100b40e040c1164074040042c000fa80d2100046480c5140a00c0d11092406651078100489070160700050043c94008140007126283c030b0300425105580e4100038045064608103001c0e8203140004003c2d40b205110258101d42e0411030080b079201351035440d0206100755114080324413184160341b03043e481c000c6175260a295 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 43101866 1250 43100616 43100647
    0x5030901031406100f110a08030f0c03040804030305160f05070608010b0c0601090504052b1b050c04090606050a03050601050a0f0803030a1503080a03050402100201060503150402040908040605 84
    0x941001c50340190b18500b03030300000d1110742c14000580510100d4030f0300b80b0700c05100301e060042c00440c040c103d41488429040c941ea443d00300300c44810701d07480c0c000b00090901110101340d90043c1c0e80103004905040c15035a040d54503400a41240305103800c01c0c514000071415044503200c82d240110040c4c6011404c040340107241400580045040c0b1100b08038001880800080d0315044880e031503c009540d4036a0f181c5242803e031103009030700d50031460910303003100c40e01c004801010a01c01078454603200b200280d80c02c0c8200c02c5030356000d41641c02c0b945404146040580000380607920030307140000c0c010341b10400100e0000840e04191400d40c06800140040e04220b009240a00300d000700d0b1140b21454003194a54070f06c00213150019098440c20036400200000d8400c40c05503a02c0001c041c0c9854985000a000381011601a44191040c0e03440440941c018810407090742d5000c1c0161140b60202d04240010086c043d00c200d820950300e025030727000f00e000480a0406490300d5560380755030b051400351003503e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 43103116 1250 43101866 43101881
    0x90604090c03063002030c030114100609050a0303030b130c020a060e01090b0402150f160201031d06070e0a0f03050a150506010801031203021611010f05040b0912190503090103 77
    0x1c084d850b00012103882000c045a80c2c08034244941141159101e40c4042401c0c180c0d103502c03168144d820005c540f809840c06040941c400c61100c800c030200c0760b5907400100e90201e01845030b50f0704010229400d102003842a00440541c14000d800e04034006120b09504003158000e0560000582105c00c030340b41004509e000b00710000034584000d00c1005426120f00d580e001014000a00c1400d0394330214592214600c207035090140340c5d8451940721058484500751048040800b2030009103080c40b1141101241c454011440140300000c00180c0d03940d0030103445240070f080a007a0b00000710704000441c001054151030185110310301901801c0c1184c81c1030000c900d0344204402d0460300300300c100500b690748111074904594002c6130303020203c4e65405040d4000e12680900710407122051040c001800325812082c20481000e90b5420048140e81e9070840d002d000d07602500703542900801510081d0302d41109109024210b003401c0d04d00c4039521421540d5101e6846504541035000465444ca4540e01072003440c0 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 43104366 1250 43103116 43103129
    0x50106050a052e12092607050d050a03112109070b07030c0303060e090d120606080118060503030a030506030705010c0206032a0406110d05070f110303090604090c0306 73
    0x1e02542c000100d48052100f40071120340300403007543d165280c1c14418600c40c1c0d86840300400c10401d01c81207080425481040c0f040140d41036a04002c503100c4800c500e4111600a0307007280c05001e40403080b200c1124654030405420302019100e1400614910001d002400c2241c03091416000d901c498408458100d100100402d01c04d4002e41002c200d00c100f100c0c100c41402c2d41c10f14207541113031000e10381a0020001500710130071301c046400402c9609040040c0702440c3c2c00060300c0e6100c0000d0781403860416240e0341d00414001a071480f00420107401c6442180c802c2c1c640e449000304400b80c94101103445c42d003100038503000280d100c0741440714908003444002d000e044286002240034450b900422440c0c070001c0c207050010031121a00717045043c800040c01d5500d0101011a903612680c0c4d440042c400f00500241c41c00502940c0010b2401720b0003181240c4906030b0002c40200400002d45071624040c031032804940c3c05020030000251540d8a007001000544030140d00054070301c0f0340741c0340141207420365040762 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 43105616 1250 43104366 43104379
    0x30f01090201050f090a09020403080a08090304050a05091306020307021b0603040206070f050c0616020306090114010b030c1c0606020d0c232404030f0c0b180316050106050a05 77
    0x38030150340e003c011640350341d1110480c03540e2900c0160118580301d45540c02119a54030206000c820004c14400808001c0e69590364604142c65106140d0303201d205500c41d0035804012044100500d003454001d15920141000d824503034600e80303440d0301059910803100c02c001070f001071071401284c0504a000011001051700c0e407c1c1140b6003070303011400911401c48040c054080520403c402c01a00704085085804003034000d640703c08a01c0e03203551900c1c0c0c0a941c220300c00d002d84000a0300e80801403241390501050b001d81c400b59640380c03000300c01d0f107540050000700c1031880400100c0000c5044c541c0500e10302c02c0c0d40d04001b038500d24010300203060a81c815002c03410000c3e42c503034800108941480c075041941c9200b022082a29040f9180c0e440d00381078804200c81108181c00c0c8152036a07004d0381c003c3c411400b0361141ca03420424118100c4001c4114540100078902c0d410100d91100340001d0540003d020340021240380c003030203400b142071000110302d080b00d40d0b0391136440a20150803d004680010b0000390f0b6203 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 43106866 1250 43105616 43105631
    0x30207080105010312030e1603120311030402090601051c050106020703030f1706040b010e0d08030103061409030d180203060a060810060503190602040e0a0b0103061a18010216090605030f01 83
    0x11744c00d91a81500c0c0c410b04046d100c142c0e080c0303402c01c18800e6116424415a81c43d01099592414169051a1400c2100443d04d011a42c600480d0100206d07031046600400c61044d40d581c0382c1c01990a60400c03c283c80540708500e0480c2d1140c040d41c0310b803c3c081c000b40e0b001000403610b1450b0080c080b81c4024042801c01031844031a400c00030b40381204540050007280d011500c031000300012641900b446004e254401c20410300002130000840003076058a0280324140550525110050302a0030b043da0482c00c0d41d801045941003107000c6070300032054a01c0f56094078840040d10380001f4a00030f800c1e1600c54405507940000c201e060810010000b600e41b1061043c40130703510303200000c2e03240c804504902c108109400710440400c1070540c100d0780940f1a040e061510b81c28062000c10080c04c992703107070601084c036103640496611010f29200015411424201345040070590000c2c1c2c0c8151040c94850642c880c0d40d10b200100d440900184010306421000010068a048100740c42c0c44540c109840d00c0380d150928 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 43108116 1250 43106866 43106873
    0x1080c0a12020f2815020c0a090506030309060301060302131a07020103021b0313060306091103040f060e01022d0703080408030711101b0315060c080f0301120302070801050103 77
    0x1e08500954044910300d8401500c0800b04005500c03414440000703940459150300b134080b1a615240a440b01e08440041c405440c1c0800e0303030b503618268580da500510b941c2c0d04100307851061b080036a002c1d4014064034100420100801c032590400c0c0c0041d400f2a0700410343e40400422244440e0050070304030007080c4c9112010058200c1c3d03101b011806410141c0000321014440301c40309410103000144422681d07030b07140200c01400001d071980074040000342002e01c0022000500d00440d02c024a00d490001d283d501c0da540c4040b50a0401103040394080d80350309101e40008000e10251410b514221001040c41d00610709020100004641482101030240400f2005c2039218807429445540540050381d80e07190759000b03032520f2640c9481c10f5200d2282041640910081d41c0003441d450310382a24410280e1800c010950964803900c0408580f624070390300130429207210b4602d654403030340150119403a00580b101b101e0480d0348241c0244a041902003010300030180c1c100009001070803808002c1006504543c2c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 43109366 1250 43108116 43108139
    0xc0501030e0109111203070b0c070b010e10180b09010e090d0504031203020703110607021515010c060203060103110f0304050c01050307021504080405030a03020105060f0a050102070513090206070b01080c0a 90
    0x150103018052800f4180c40000c4104111107c0603001281c44005141044146019038004c98080381d030420400000030704500660513090041c400144440f600e80d09201032080c0e070303150242482c1b203c9900c4a5070300c070759a02d03414600c5000c2c001c40010701c070321450076072403403860001850350900030008200401c1010807080b200c8004142010b140159840d040c07400c040341d0100802c40e0031500c0707004d1013090190342034000400c8800c000207141c5024040c0e40d04904480201014480a808a0351204803000091019030065520070414100083d03040660340f1484000d801081540c803e8140010600c01404030402199072241001d207452803540c41c200200030344650900c190f010003a0480c078040741c104951841a2006800054106d0b082c07400306090080c080c1400351340c1c00d401644400340300140d40c1440c42071001a2401078009126081c54074007884800c407601184070b16040c2c0c2d07400c00d03080103a44d10b01c010505540038440404055041404207810941445441881018004401c01c410101784 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 43110616 1250 43109366 43109393
    0x3071d030c010203030c071a13020102100c050d09030315030c0302090c1e070c09140a06050a0501050406110304080a2904120c020f030d0c030816020303010b070f02030304030c0501030e0109 83
    0x445440c7c4076251442c004c05403078012192030501c1480c441c100704408441c0c0b50484a41c500076403c6450002545400307108486008a03000005481042607040d402495000040c0140c46881e0010701008410901400c82600c2d800441e4450700100c0c5c1003041d40b400015198200c000041c0b03662030150a40201d440640154403006404880402c20409204400c04050000c00344010140300c10b400d01e030740111031a0021103486208038a80100030481e4100b8030072240540d401a19010300d0181070a605951409000c00022580c0c0700400c004100003406102c150300700c601c02c05003465072030024420305200701490021204d0301c40c00785080001180c00030400020007000c0303060031787c85880b40d40085580310110044154252040109200040d544442c05a00b914040e0b1f0b9540401c0d10b0f0348504000d074019004d02480168414401070140d01220170041c600e451040300381800d0501680d001c241550820303807040d5246090304508120550300350094202c8646004000c1003580081c5e620303103284002d40c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 43111866 1250 43110616 43110631
    0x90306010302010c0809060412021201110a05091507051c0e1003020708070c030503042c010509060d06090501021b030a02060708061215060301110406092903071d030c01020303 77
    0x130414000602005804699042c1c801a080c00e0742da5450703080302d001c0f201417424100d001d609580f02810403014103106c1c40056030311101d81c640c54001401d60869458118010306a403040080c0d040c8034082c440130005164040c403074005011003200140403286041050003021060200d0800c519140d660f0b00035040302c20325640d00300140c0b14006030a0541960054a00060040c0d14110001c4141701000000d0400c48070743c001400b83c07800c0d005e855000284031030041d40c4c4562a6410061119150880029601c490040c3c40080c400d0260307101c010035220340200580d4a6580002d800801c2c0c40301e884600102e4081a00540c40d040d002d141c020b54664000f07007501c042004240210700a941d40d01c40415a004142003128000c3c0040c40c0e0081003004150b0b1450f120798602400c580b0301e07121041c01e0b9001c54201e0784800b150300e49800743e00c121000c2d1440c000c41d4180402507d00e50301501e4440914091202e130385d1009492030440359002c550100c0c0502080c80303548182410724143c0c0c0e00204807a0700c0030f00c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 43113116 1250 43111866 43111877
    0x9060305070e030609010905070504020f09041a060a050c06181f0f06080106080606190b030403030209130b0a0806190209120f100b0604140103090203210a031109030601030201 77
    0x1a071090031294001c42081441d41405200c041c04003014054202c00c205c20700070001d0f505841c1d0f445081008034841c034129006c000105000c00900361420341e01c641807003e108080102c0c038248800001d02298401020300d80461004590748a00c160204442c982c0505046030f0079004080000e20141d075009400d02d50141d414050100c000440c805410810b8100358851041c0300032a02e0301c41d040d020345102d01804001d4810040068407a15010146458442041c800e0301e1182d03080480c1c032002c507440140180c081c150200000744894a80742151880810090303000101e40120004011540c80c2c1c55022410ba940b0040500c5032000000107000e81c111031064005a4030b1040c880440d0300900102c4041440b40104d49600022901c0866940031001146038108401c0d9003c4040105502450003410521101d041c100501540070794406042c0b41d0004040781d00d4084000c5131400c400d5a11a60040c0e01c26000c40c0c1c0c06449034240c050b281c0c032400b444400c103040805501c0425620001440060304000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 43114366 1250 43113116 43113121
    0x6060d15030507060f14040b0415052808240d020310090b061203040e0103150905070b0c120405030d230309010207110d050c040506060c032101080d09060305 69
    0x404040500008682c418151100030741c4c0c90030081e02841600300240085030b000354404141d0081d14003100e0a03510a865002e0501e400c144010300d40036204005d41d000c1c0303d010488080200c1480e111406041025020441514001c440082200401525540d0524007502601c208502c1c8810b4051280f8816519000a8001800002e151901c00301c55168054038180f5517000f8011619102031141c2820b0340c4402100900c1d40206a40b40b08921130302d80000f800b400180009480112008082e0111500100700283c10761030740350800e8080d50000c03442c003400207844926600d00780500b11101c0103655a00d801d2500c0d050202c1d840d615011783c60000c0000d03a900348851f2603c040104816240300d8400d03140c507441c5c0510501c1c004c1d40541d40923150720040440e4440c040c40e00c5082c26450701e0f4004090704001c020401404040c01014150503440041400f0304c03106002d082000d480301106c50840c40c0c003003600c44102a282008182c2054507142c00940784103e01c2d5801c4142c4008403041454001400e5 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 43115616 1250 43114366 43114391
    0x8010b13030b0405010606020606120a060f0603080c1005060103091a061c030206070905040603030e09070201060b0a0503010f0b0a020d05030903070b0705030a1505030c0f030708060103080c010608030306060d 91
    0xe40550001492580020244000c2c0701341588184c2c1501c00070340840d0181d0710780500700210303000c0c0c480c41c11100d80d105841030000180960013104040303207950404194076807650340f102c0440c2c2280b40c488519030300038640c94409040c107004d0540c2101c000c1c2404c100d24011034070f42070f0200f9002c1c0c0c07000c0a24620300020403038a4a030002c40000e034910f001e010403541c810034507001b0344940b0b00780c0301400080d680e46004a44c0d49001e20540045a0b41a22a080c5062009060081220009003503400755580c40d00001484180385004050040b03072644c3d007564941c1083c1780e042c10425180c20403880c642d02032000300002900059800005241814000e0322130b0b50f00c02c0302514511070104010500300b088024802856001006035011b41034241f010f11000d04a081000a401c5582c0f040a5166000c220495010700f01745130343c41c08004016042c2c81394107886a02c021703d0700c04217920444000c403001503a40c040150a20414018054410156266088c500e00040342c40c05021460951507a0303a8851140780c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 43116866 1250 43115616 43115647
    0x50a0509060f06040b1801030506090a09020114030a0605091b030601230729040c06050c01020c031305031905071703070c081b0306160809030c0118020f010302030708010b 75
    0x442e0008001c80e5844d611012405600c2c0c01c960390f01c48500390341c1c0454500642c003c0c00390511606025212071805c1d03a0b0448850041d02c64568164144181951114880d4890b0401140f1504145402080184c906018021103007401000d00d0060745011942e01039070381d02030040300c0e0402402d107001c0d5502580e058081a814035440e61600005000064150402112000481e4111040c41100500c1e61042d051030740d4400044074024500d81003410207018060155005d04240c54501c4001400c0a0140910038510b070300c401600072a00f9608041002107140410040d141c40d9400102600919004e80c0d441e40d81d0390180c00303048103400800e045400542c1c0108140d429298000018820150395020001d8403042080c0b5071285a0a181440700103900340002ca2030b000d40d56980b1155036010200710700b11400316000c2d02c5509580002c201140766002c00f4020107002d00c030860940740d846000b910401c00c407005400f001d103060500600810106a40003120241110311040d1941d0f503482580030107154 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 43118116 1250 43116866 43116889
    0x20a020f060c030c1b0f01090c0605070218150a030605040c050a06140d09082208010603110405090102160809010f090605090d03020c04020d020706050a0204080a060c090317071506050a050906 84
    0x44030f2213400c0c6d08190080054100301e00a9000301d6003440d0081d1554001c440521030500081d4000c202c202c1360386410340140401541c0a40d0520144900712114800151611866070054422544800a11081c401c004403010001d2104450880a080c5840e40242039951803414100701000c0220342c0c1082521780350803440c0819030109140e07980780d00c81800f125824400090444000c1e040a4003c15514814494101a20340041004058034000420000a414002d00e00c40d042d540078860b901500b88100740c40350105100340f40b2240c50f0501c0e00b00040ca0b00c00c495411108026081c401040581c2d00303c000c59800400035074112400352142d0405038940060005460782052000400341540841a405050796910841040c4105d441c2c003085c883c10b038019030107001107541003210714800240d030f15802904007400301c1c1001c2d01840c0d0340b40c88007001c441d0122545081c550f4006807100800080c03029003a491049414100300d6582094040341e0816420b00585e4010680e40d40402c16a6032440803504 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 43119366 1250 43118116 43118167
    0x90711030d061d070203041404110415050c0d09030b0c031b03100303020c0303041d2503050702150907270c0315140d060b04140a020a020f060c030c 65
    0x103100d0362100c81030303104001c0400b02840c1c09021004204c2d01c61003c0112402c40d86580030104a4210034410800144140001030611400400000410741c2800411402440442d140c0c543c544525101c00e41c2840400c600a2042154150003840007540a071440b981118078105655140da481c50071550f6a070420303003030f0200104004030801640400484402098a11950a55000304440c03000d0559900503030082004001c041d00c01502c0c038200c40c14016078000340c4002ca440705404000c0440c2c402d08505460300300041e486804000718140c0410900c1c030420503441c8030304424075007014100e8440d20b09000340e5020581c200f5000706401c50154100b002e002c0d00c07440800c02240d1004000d002003500c0c100c40040b542c1c101400088244c107104009400d014041c2010150302d040399507003c0200b00b0001d940380d0190f601c4803240c82101d240300c4414401c01450351300503a81d402c09030001c1d14085030081e0740505580840200003403101c40e00c0540b60041046580a602ca048001d00385541001c0e0a0021 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 43120616 1250 43119366 43119371
    0x30e04021b010515040905030405010f05040b0c0a022e0e0103020909010f060f02030a02060106050f040915030611091c0c050d0303090c06050a0215092107110d02090711030d 76
    0x80a07480c410741c400350098442d40000407104907540140b00c00c0d90b00c0c08101801c184c10501040000394011002c0d407080074003c0c5401031800e0f8a986002c000303a0003811316000c40c0e070300079005401103042c80e03908001f03030404040d9000400f149100c0019004201c050940c1d0804c02c900141c20741e2030740a42c0541d0b110f51002010443d441d07031181c684004002e0607206960000b440542050740850020044070303030482c5ca9a001e040f02d6070800e1010303201030f8080034407129800c1d010003000450005620501c40521242c600c001240352450a01d0415242d81c6411600d040404200c1210203664450030a4a90000030400d1240b024090901041900903540903607004070064100f0b00c03c060707240d0300030000c0178415040394120680b582da0840d04d5004100c0c8100160b44801c00c024006020450f440e64000840300071152080200350802d4805441c2030103d100a40010440f80300300071101404224000082e10382c0307040d074900340e000030301e009401030000d80a001a108203449071040a0044802007224071406 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 43121866 1250 43120616 43120657
    0x902060c010c02030903060a06030c060804020109231e0102030d1d010204120515040c050909010e030c030901092c0703090f0b010e0708062206080706020105040b0a0e0a030e0402 78
    0x380d12617101c80d11062280c050100082e04141c1103208185c2502c2d000320b044205641081000d0b6034018001d0300590500024200001d00e07203070380800c4030040b01892040708032011580001e00c02035018001d480e5a8000c1440c0340024140d0780007040d0b80b40c0107065074000c10403180c1381ea0000802d0500144c0d0361495400000c0116004990b40c00454540b8450012100d0310414803a032100a0b50007030b10003c11002d2840010812490140103140c0c001d40c202c80005521941d5001c1c4a103503610080c14a41c02e030b000890302d03180942c0c00c0712000000306a6865104400042c1e213911040845103e0102d6084c02e680c44045081d280c840d9014244141d0300860f140c1c034402003800c0c15011010240b24101c600b094140005075150b10424015006031000f9214112002210b0043c2d82c43e010301307843c0000d140341c0c0d50b000041c81c44000c209403c0285620307000000c00381480c0c1000c02440c0c20060003550050300307105082612490000b02d1500342d0b505458504040221000010f020384103020b6000c05c81940040d2 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 43123116 1250 43121866 43121891
    0x90501020a0e18010302010f03022808070201140108031b0304030f080706050c0903060c0d1113080c030a1a1009050411100c0201020a0f030c050f060a05070915030902060c01 76
    0x445504614040ba03d12031140455603402101c1c80090100900003083c83d19550801130182d00600070300700f801043c0103203854812540641564076020b6640020b0458014052103a4080c4989042c0c0b111580c0003194035810712002d641e881c8075007c418445424007180f50090700b070742402510059540000c0b03e110007035580c00e10402a800540c0c0540384c0034a0a800704404440150480d00020170142c0904000c3d680c0e240c0c504101d802c2903003809515511400907580c01c50108006041f503100320204510510701700342c641c1d0b24012407a13800c0c1e40a0362042c41e445000c03824a125442501441d20f2034420280d54039009544601c540d0f50101030214184400e000c00c200101382c1000c540e2006440104000c1040d000407161101c2050000e405a0040140034020906400c10710310b145000c1d0030500b401f00c603a5030707070546400210715500129030004030038851906058090306030018058a420100c8500344050340d0307a0b0114494451341816079074111382045403142001e9500c0320800d1802000001e50551 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 43124366 1250 43123116 43123127
    0x90601080c040501060e01030e01060510021c0801050d0803090304050604030609050105090c1509041404050f010e0309061207020a02060d060e0606030112020d060f0c0e21100b0103090501020a 84
    0x240300641d001d2880d2840081c24a032003540e040721583d0744da00766441c01c2003006400400b11ba800000b255502c840c008219034a07840307004107807040254002d1014100080d00b070307d07200f0903510440d01040090b01c0104070310794500d00e43d81401c1e0b4200043d00d40c1ca81380e450400745540f003550f100e9504044041000810b2102542c442c0784868003540003800703284c0c1c9041d9100e84943c4030801441d0300500c44400c0340d0000c000340340608100c0708064400100c0c0f04c418840d072141c03080215030442d5a6401074001e203295003802e00400007105003200080d070a107080d400010b5110701070345010f41110350551000031000d910800c5030309031283e000303000d29559403140c201c07038000380c81d1034020502c82e100030318081405428000c044074102e4107001b01c1c0000d9501a90700700301294100d03901c140c1b0065103900800b022002184502444c0034426240e0041014100c001e10024030301c00b50441c130007180301c02da0441021601181800c0010152040054059024030050b801031209000c003411962000c9140b03004150000c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 43125616 1250 43124366 43124369
    0x10b030604031e0e091302030309030a08041508010b07020f041b0f030b0a0506040306110f03090a12051315020a0501050c030703150602030a0309020a031a1503070303090b0703050f03090601 83
    0x3180b01e5140d48101c80c43c280d07940495840300d242c1020b109000511307001440fa44113403100344014262450b211800740000c2c0b50075241c1c08251281e40340042c0800028545a03990740e8545450300340003c4541c548600c0b0030403030140744000780c01012581070000380b56803540e001d043c2808025011040d0500700c0100242080c811030040c5010a00e0034448416914081103084110380e0014402444c0c81c1c10f40c0c0c2e030302005d400e10b0035040c007030084284501c1840114030f40245d03208041c80001014852214240500000301142400c01401380400001c20440d540c01900003d944103200c1040590544182c00c030f241c540901ca02400c0d80d4617000034001d904007040025402100315944c00e00c880d042c4800c99031058200c80c403410015900030400451030074002e800c181c1c1d46a0005001d0081c5607900c0e01c078078044650301303460341010280036003c028034682940da01c80010f0105a004000e554190340c1c000d031a4040078000c040c906071010a081081500c148105c0d448200c2031003200c7d491382090411140d440400b03 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 43126866 1250 43125616 43125647
    0x41d030a0f020d022803020f0f010e0114010509180705040e010605030607050a080f1003140102030604050a06050a060302070203010b120d0e18150d05010c050a0e0306060a17010b03060403 82
    0xb564003046405100285d0041e440202035507015250103105051300301c1e4440103108409501886104d019003a8003031101514000c0c0c0300e000482c48140200c061070849048140070118081848014095900d4042c0b1242c1d012020403031030001120040842460040706902166000c0e06000e07407500841c10640000d030468034280c00f00d80554499140a031004d0040070b2680c0002605040040d0844d0041924990007581c541003025405403a07407034810342c41d50300005070155a0b4000060201a081030300c19944c1c405c40b900400c205071800d140c0010260040c034803500c8100364010030218103654003035128500c03c003001401c9811140c850902c85864aa0001942c008501900b24040081c00d1801022040c90303074806590300b140e034500d0550b04000c45c4030000281c00c080075506802c0020402d00c0741400300c400c0c3e92640342d2540e030b40301002082c002140302410b01a0300300b81c0600540c1d4584000e80001c0d1241c00c0341203140c00990350115401032004d409040c3c0d0501c41c50003800241340d080360710384c41070300751 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 43128116 1250 43126866 43126873
    0x3050723030604030c02011b051c020606010c0203030a0e040b0414061e0303030402041a0405040c05040f1e0908070804030c09050606070b0c090102030c010615020d110705041d030a0f02 81
    0x41080030582c5907901294060041080003441d40010b40c40740b42c00c030701c0382140041c0d030900f0085240c449519000c401424129a403585030740004055404004641c1e2041e02460001c2d071086091380070a407203000302804007090003407554011a0a50350782d04170341c0300c285018000704806e840d140312a8038a500184c48260181e00c4070052460b40211a20f00c000340c1410150042d40f85454036401d00004001d1140365498003078040110054541c0c8600072540500d0096140950840c10441080219800080c070820024906800403407a03d01c0d00100702c03c01505401d001800450a003030007100c41c499044c00500c45000094003000b040018608201030310413890041041d592441d00b84607440c442e1200162003e001800050b00e4141e20340700500c016401031050340d0401d81c080b4140c03401d55000d5009845061400c21030800720740d6042244001d40020b600c0d21b00000d61350500030701d803200141d0050b07074061611107400340545160320141300c4070b00c01d400c02180d540e401d070180010151540d0740302c90382c010b01 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 43129366 1250 43128116 43128179
    0x50a030f02150f0402040b0402030a050105190807030b1b1b06010b032202011404170f011e0504170712030b03010203011505031f0b07050105010e010b09060a09030507 73
    0x14400a400303818010071078900070b0b0301d4031a54200410514014002c9a000752105001051a21580003560040400010100c7d141d410719080200b5400d580c1c105c45027030705025100f0000c2290000c1e030441140e401081300440c603207441c0489000700c0e515841c00d107241080054041c1329030382210001c2243d00040004d58040e0b90b25120051034070700c01134843d1070000750480194040038019009044c0c845205040002c003075100780c0e030f8000d882d40180d4003c9800d240c405246403100d00050041ca1918107440d0300130840d142d01c40102d03410301a580440d40003080d58481c00101044221511440411109241680c40d20b40501c0e001c2a120011041000024140440b00c2c1143c01c050090701d050f0b8425140e120f21807a030750303070023101c4e075410007420070a00c5400d0402588142040300038000141480b2190301c0c1d079403109820514291041079000090034074001004001a02026054411241080300d88640d1406d04d500119594500707034202401600915030000381d440801c00c0c1d44512080e082400f0a20302 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 43130616 1250 43129366 43129397
    0x12060503010216110a051306060801151707051c0501091503080904020f04031505072601060c0317011412010902060702040207080d02070b04020108060f0102070b25050a03 75
    0x7406001c02640d5200307540300d00308001074130002c6241c80382d100c00703040b954080c1d68490004002400d5881d4513903a072a580c0409003d441d40c0031040a0240110040700f520b40c0714940001490126000b03030080c01100391002040440d07100303004560f10f0145500070708078945860b10b00500100020311809144616201c0300506981c1d040151400700c0b90401d003018201500a814040030350300107800c540009100b00030110007d8002d4500d0703000e441e00c0620000340c9144c25036025081e41d42000202c0450b424240f91074040c9a1b41e490a00c0c1950290301d048080b122141c40e0a452442e4020f100c1202c0528000000c9440000d00040d0320036030000701c801203440000702484600301d9003d100043c3d01f1a100b00881409414981c00a0980038469041030b89030080004011049030448102250054441401e103c11b642e440040150031001c1100c0c680740d0f15002e00000f0707544040602c2a1541ea40c0c000c01e010800e9000003100300c28215440d0700085109075a0b20b072407601d039017201c282100801c5010304014280d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 43131866 1250 43130616 43130621
    0x6030b01021f0209030c030709020d06050a08030d020a030e0f0a0510060602150c1b1b0a081b01030f0603050304051201020316030207020d020a060e13050c070f0f050307031206050301 80
    0x201c0d42079004070003121101c260b440c0040d510124a0350b4062103a0343c082c44440d10b00b04286402030075902d80040e1200180126141a2103899221030312403200c440781844074100100441d10700f0301d003407040180d41340070580d000d4029280150205c40240294500b054042c1d00120340c10071464401c030306840340d900c030000f50002121100d008010050307020b1100c101c03c0c4c0001c0721205400c00c040403621820212907051440441826640191603508040c0407907200d6811807000d9151040201e50f400289030800140a54401c21040b00780f00074064100d501c03480303074085c1d40200b07004110420305200594030707800c0c01d540e0386c1e02900c1040d01414006c03d265100c0e40040c0300f900c1c0168240d500c58102c0c041e942000700e010b500000b805a0344a00b50800040050303440740004002844581c03200d6122444070410848000100c82c4e01c184003905183c1041f015400c60011290010f610882c0d03110320341f000c2c0c01c1240010846141c01402440009614820705800126015108420b48400c8c4225503d48050509 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 43133116 1250 43131866 43131883
    0x7064506110705120a0503030405030408070503010b1e0103110301080102090f04091e051218010f0f080105010c0609020303030408120108070303021005070314071d010504050603010909081e0406030b0102 89
    0x1c00d811501007805a858418480711003411524201c030044403d13600c0c3c107811940b0a560844442e40005400c00000b04180074a00c0200821402000361042c61008100b0440d03480c41e545041b1f803d1500c003007201e0303070203648180c0710030b000003452a40b02e68450b0141c0f0b0003540001c400701d05c2680544660290b5140501403031801d41e60100e0601c40034800c420a8000c102c240e00c000301ca19000d00415140e0084403a0007401b07a101e02c01989903110800100050010300c181c0d0380c400d042044621403a01800e40000d00241165820320b059510850b484c18058001c0459980087d031600001091106120500000d4a012902800a01110b90341d03921030507a20f401c144002405600030f80e0200841c080b140d0b100c00e5006101d420041241060000c0c09407200d641112068040740202190549601c4410a08c00d0000030a007041ca1800c0d091030000b0344640014818000e8080d1603a41d90740421405406407400c901d071150416403409005640351900d60000d000348000a842d000e03151455600c0002c0048 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 43134366 1250 43133116 43133147
    0x5040b0409020a050108040201050c030313021003051506030a060801020304050304050108090a05190809090702060406050115050304020d05030f0703030e100203070c020409020307080d05040305010b0d0507064506 93
    0xca0f00c510b001c005407808580104140c0c10700c5001c1c85089804041032008622482c48044032005c0302c28688101b04048800240250030140f403c0200711405807030307080d810240c04048078615100e5540741c2d81d28018125a4120059a50010003400200f200010192040c0d8009032107442080e907076404200d59030150190003a10036071200e0800440850b1150809400c2805230b842d0501c3c2102c10004205107100a40d2803400607032080341000244042807040038090303e0b1003003c2d0681c80d5288034008005000161019100c0c460382800e80b8200f082c100200c91001102d40d804980782d00203420081d00070082c1900c40342c030324003c1a0b2a0456a01e091088a00c5106070341c480e00305c001c0254090100030691508202c0c3c03d40300d242400300e64a04100705a003001e019a640c1c40e56103505514009003034440140c000740c0114041000d240015038007003600c200790f6259107840440d0300c00841d004401c0e100080541132465090401da039696401070500745018078402580d000800341e0750b0038101c0f80c415141e101d84 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 43135616 1250 43134366 43134379
    0x120f0c02060c0a14031501020c06091e041512030906020d05071b050301062303010603020d0b040503040b030a1b140f0703110319080c19031d0708060105040b040902 72
    0xc69100300b0701d001e0509800245006010305601d420703c0d0034541c2c400c0d80d03030b2000496002d103400d00640c0c0c100000560310b0b0b41a0340550170700c00e403030000c2684038801d00312000040e06440e101003102d0321030368025460030020305141c424040c1e07507003240d00e0704801c0c2d1031042d00022510301000c80c6041c0001042d211820080c0e850b9483e183d00364440d0b1940c224040d105900d07004420320b0015295a0900a46000c2c218000c016417801c280140016200300e0010b010074000d90402d5000c00241c0d941100041760b0581200001e10240d40342d01c1e00c00d0452286811152402101000f80f0019101940c4558416001c08004085001010200751081c0c2000a01641225010005000700c1002040a401c4940c420b08209411145140b4a5810b542064017040400c0a00c034407401e9401d40d02468403074119600e24034603403401c40300c04801054070303030203440400a0649506050040c0c0100341224181401d8031019114220707150903c3c1c948404083c41414400c03070400501840c0c2d4038061007080400ba6000b81003 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 43136866 1250 43135616 43135621
    0x1505120703110d050a0c0e040e0a030f05070f050d08180604080a0905060f0310050d0f0813080a03021011040803043b0a0c0c050c0d1e03120f0c0206 65
    0x403000b41140c048074081d404818805084454036500410f8080c40e81528003081140042c0002040b13002d1112420b48a1401e00010b0b202c0c80d5404200e03003410540518000f400410b9103034069071030b8441d4203401001003003000420818000081010780115401d90f80c0d0100b01e480e01441012600c08000a441e02d6403c20400f103400141c040740105074003181800c08206550380c0c0e0780011004d4201c183c80c45100100002000200c1d112440b0302400303010102c0380300c2038080442e09c079076092030101e4400405103000017462010342c007908c0100200403c21441140c20140040ca8000c1d10b0b034886e25160741a0702d0a00130544411003228040e10b041c0c4800da0300860a0a15010413003034480000450303060380482c80b480c0c9918800350720700c0b43c00d04400d070300a02030080e00306108200b084480c000005001c003c1100809400280b0108442040003011921840e911507a401c00c0ca4110010380000710216400c00d408508158004090400b081154131080081c54040c103580002d80b550500c0010040c0c020000 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 43138116 1250 43136866 43136881
    0xe06070804020a18050901060909030801060e040b04050a0e0705010807050d02030c0d0501120b01150c110f060318070f031a09010b0409060603120306030b0c18030604030801150512 79
    0x9000d40c1c824002021251119034031816000c861001000b00030300e080d01c0d40f0800185410034005c250081150310400c011a02c102d8132b00924418060043c41c3c10007410307940c2d2803074654568008400c1000c0c000c00401082c100b1098078070082c00092100d942c0303400b03421b00c005030540c0038451403481001c0940b141841c0162a01004000b940000c20040c0c4601d024401d501c0e040c16540f10706406045035140b550000c195034180701307420120590041c001d00c281d07010f204442561081d00000f02c254402c0207003112880d5400000e030307030202c9011155002140802000b00b0030b410607a419020340390b14000e0714440c1d6180c5490042100c0d0707500014103002004416040306c124140403041e0b000da001000050840e02490000e0103071800d001050302c0741030b1034140901c01c1c04642c88901001c01c0340ca0808002079840e642c3c0f0300c50305a0000f0500b02d0045404918148412300060300f48042e004000e0640d1031600d030514000d0800c0d0801e008140044c8503c1c5d41b03e128550203101122201002e1000003d0142d48085 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 43139366 1250 43138116 43138127
    0x30f121b0405060d02120c0c1b030717030d0c0e040b0102150402060304030c0b0a0203010e160f0f050403020a0816230d0809060d0b010f0c0209010b030406061707030203100e0607 78
    0x460901340543d0030000b115141d4010241c1a0003208241a041d41e58100040e929240040c5412600811391180c0c000c00701039500000e0400032601a88000c41c02249104842400c0d409030300140700c2081c1c01c0900d8440c07016484400401c040c20201c4d4100007001800c0d004a9944045070038103e00f0b0406d440200380540380200184d50f0040c42840c050351046159611280c1014065a064041540201c014402c9030741403095140e1104428a007645010328440780288040a945a1038041c022182450751309248180d0031100a50b03006044540826503c0a50f155204d11b000403541c217220512501144000003445c400d440044010198185152100100404031020403812189540108483d140c103440c0c0340003400b9014030285001410109803000074100802d0707000440c1c03c00103101004001a9501e031490744c113680d801c6007465240cac0d80328682400200a00e40013045060120580c0340d0380d010b0005140c0081c1c82c42542a108012940030340d0307000307503409100d0340c503a503400813400500f5152060 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 43140616 1250 43139366 43139377
    0x804120c080f0f0913020904180308040b0405010612150b030109020d1103240601020c150d05090304090e031905130501030e0109080c250e060603070207030203030f121b040506 77
    0xd0780c1261400b041000005d1414082d03c49201500783c011800b020f0529140c842e01070a035109031612040040c207a90020800e480003040203000150140109090102c00d6110b5006401089540440c0c03109a040c855880c0c070389100401c0c8401d040000a04150606000c2c1d64030947d0f02400201c000702182e035454800b810480b45040c0c2602c40c9504108140000b28566030104686100c070000c1070034601c00082c2440070858070103024054100110341c10311480070840708001a20390001880c0e8940805080c19803081d41e001c0107400c0e040c8180e0240f02c01012006090b8200c520044403080c0c6402403003a80c882c0114144941c1045070f01100300300c1940a5084400c100110000005694205540316901038204000c0c21400c0d50000303500907403404903514243c2624140b0800000e1035071921845002d10040203002d41d0166402001180d040d0340200036500c09158000e083c0ca4807814002c01c6d6003803a8000040400d8070079103910200e403140136004400542c181c441400240b90504040501c10140d004 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 43141866 1250 43140616 43140637
    0x3120706090203100e010e0d0f030207061508010509061b09060c010f050c04080d021603020f01170412080105060c0703021011060103080301090b030601120312020c0d0804120c080f 79
    0x84841d4107005960134458869038840d900f2000801003420074240d400c59400341103145903070f03001041c1c4003112500b050502822010038900541c0d03940713452a09070050000b0f8541640031141000000c15050f5042d04a01d100e001100c0844440780c1e1000421660018950344e800e40c18401008138a1040c00c11000811207000703480c001003a180820f103007800c21070f90216078013030940c100441c0030f100f0715009028403500714190744020310b450b07090f082403540800f1880c03000920070095462009490390080302000c44c00300a04500c03e1271840d03d400c2c084d41034aa0320690000241d01f010000c2807614200c020b9036410000c0000409032503045600744026182c5002503803040c8100401c80c22001082001954003a510442c11135403607500d00350402d402c0d66182d8071050301c242c1007400107006004624100e07840841e02b603e400101b032208100e204c8000d03c02c0d0742e1426994000c02c00010b40d06504a554240103600c130740000d5401c0040700c0022200c03040200e0004120200c200442042c1030540c801400c10ba258 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 43143116 1250 43141866 43141871
    0x607030306180b120c0108010e1005090412140327210d0b04020301080604062016030e060a02030f072d0b0c1602100207031704030203010f020903120706 67
    0x480700c0800381c0045040200412080d12190020b210303081442102c40800310100041030140c105d0800039081c2c2030705020751922240640c0000d0400802c58005000400001e030640c2d40e24180340c10300400c1c0000500d64000442c084030031111940b640d042c00c486c411410003046490180c1c0f9610420500b0015040d10380903403260804902140c03d4500160500c00c8107080003540d031b0100c008988041c0d60000c0d4400e03114510500040054000118003158816406a0001814104070382901040741c841d41040c200ca410200c1c0c00640440304003400b0402c0c0740280c4440d180121100c0410231584501e0091200580060082020b44200075014140303080c416000031000d4404001001e0313030740c030316007181109690040c54082d082c011144d1200b0b8100d02e2288203540380c2414003001040041c10003500a0007103038441c107003010b010300c00c1c0040b81c00341d944910225582800d960005074980c1040c00107a10030351a000c0d01c1450000b043c0300300d84407807a000e00585101110154942c2580d0414003090f02d03080d4 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 43144366 1250 43143116 43143119
    0x110904060b1005040807080307030504060807120906050f0f07051605100903090f060f1d1f11100e0c0910150203030103060c080702060c1605010603050d080f04110607030306 76
    0x181c42c040141c10a00c82c0c0c2e41d440303864514024a00346810340d00d50060b12140c0041100702d0229a11204403001c0d40c5031402c16164a03100c58008075540000c115591291303a280c50403040411580e13410980c0580e000030345200300c9407901ca40d0fa10345d01800340d481c50040f410421110f1f005072818400849418000c03000d03241d0b80d045000c4d0460580b44003d20480014484240500c143e40101e61100080d003007503d07041c012140d20300000351030b000040580072400c4186040018850740d13203840301035040c1c03142010214103101c1c42c41c0c01ba101d950100c030740410703900030400b1205183c880c074802e290b12042804002c025015680c000e01142500161200c4c9071001c2090700498440c02c104c40b4070016842a40c000c558940c9541804000c507201c01c02540c0802002e036050084065000030169006090001115507440c0e100b40d104100605c6030500a0031542003900020a1107800300b0107074800c007607a80350b4415580d220b074648151385c42c049500402180d03100c0c42c0c2c03a0441c02e052000d0641035209040014516 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 43145616 1250 43144366 43144369
    0x302130b0607110a0b0f0a030209060706090c081209060d05071707020d080f0412030509030412060f0b0901030210030506010203120c03040507060206071209050c09011811030103110904060b 83
    0x354400704041c0c43c21141000c01c0d00300c50409050380c400800b181300b4038900f06008151224560b105000782c00003010380100d100100350740c2d041c0c116000c40340c0c030400030009802c49103007141100700e86100c0c0e41c0c124020000303e610605020320480d06c0d045001400e0300c2c60400c180030365000804015000c00b041083d80c07015200102c1002005d60701810080e001004442c4420600030044403008000d80d11207a400700501000a0000154a00a540314100070076581e5410b03140500d103001c1d0b40e020030014290031401000780311840e07005030103c10300d0748000d000d059131000600661060038400250003011400310342c41c80a20a078000368000c02e052041c1c91030410305000c0c10613422000d40f20194551000800c3c442082401c000d8200100300c1800908014070380480e000c3c004000080741000c00c00d0300ca452600400c0fa0600c040d03c0d240d240141998410b507100c000841107540c200819000da54036200c13240e06081c0842064a0407a50301c0044039100c0c01015007800300c1d01c2d2029104440c82c5454000ba503489 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 43146866 1250 43145616 43145629
    0xd060504140109050a0b01090e13060c0e01081308040302130b0a06050307030f09030807120e01020c06010f08010504050303060607050307020405040b07090911031305030c0f01090b01050301150302130b 88
    0x4081001c02500140d41409a80c000300d560240c00c0010051800031100c0c000d0344c03c000ea1134100c4984017100b0041781c0c0d030364101d48001266000020401403070158410f020700d40108190614280a981c5d140c01641d41e020110803171180c885010b05022000c0c0010401454888280c4e182e00b0000c100c0824032404150104140b042644c00c1500410000720070002c440d6030520440e80e280c5d598450030b04c050101514040c0440304041e04000030000581804400b000003900700c12202807060000315030301c09400740b40031f846090a024900302500d40d214001550707101401800d0207550401c001d94507584604040000c9940700310811070b518001440701c1005a81c0b1440b81520580c018080e03d00b0324035040500428021042e04190001841d004440141c800c40d4400da0340d20613030500403400c40c402d95080103071030340c01051800c4220740700710310b08007a0380301040d0072420f6a00c1c4503021080d82642c032481018241e4851180c0108015201e44080001d8030700505600003008101500086a4a280021402 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 43148116 1250 43146866 43146881
    0xf030f010509011d06130828030b180f040201080703090c0f0806010501110c010c0f050105070e2103030103020405100509070c06050c04080a23030703050301080f0f03030c0a090b04030501050a060f1404020d060504 93
    0x100355919005600c5040c020395a805001c41560310002600e00072803020703334680d4054000703410401390384000344040d0701a92000510740d4000320140012903454000b613440303100c180100d1000d070182000000c0c481d40154146000180698068000300030b0100044031506a031a00a9900c2c003840d40828010940030311a05006002a64421800c4601401800300c03204941400c152400b440542c0080c01040c044180c8c3d0540782d041b01c0110b82603c070907400d414074035804d411890f40710482c0f4041c808095001503a03280002e114180030300090b6103240400015000394402d04503160022181400010710303000e030851000010440c0b8100c5017403140c882e1843d580000d2011804144000014801c2c80d4080004542c2d103d914001400400500c00003e522804050140000160086881c0d08018020b000c2c0703001801c0c0014100303032140d031f81e4107002d400703800141c03401400c0724600300d03000c181150019103010136a20f000041240102c0e40d503003404025407082c0c20200f09989e5612010500d542c4d50f009488 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 43149366 1250 43148116 43148197
    0x20309010f050106110705010c02040b04050f190b0904120306080708030903010e03040b0f13051f0806090609070f0918020903070806040f020f030f010509011d061308 73
    0x5481d8810740c0200112081a000320040c82400600c0c005180400201c1405842007031074110b203203c0140c03000c01c014042c0c0c0c4650b035502c1800c0c00200450b0840204056210703600340d101c4100c5085044150801301d40b003458010b600420340700c0001e00403034a060680003a0720003900d0006a00380d81d078005282007103800d40083e5610740000400d050245000d0250b210000c24803030255190500c0d0030f60400c054460118000c0941134041218204004040500c000400021701107200e030031a045110390a9085800307101000c0740d200c402003038050a081040c54403508000c1c184103100d480e2120182c070200c0c140d10707034a010840c4050340841c41d44179110719865281c45255015855440c144205401c0941c5904112000d5115008000100c0d46c03030400b40f1146a01a0303400c180c0c0300451004070707080900088601c01d0a6080c40144240071005504c020079100d0040828032800d1104035601d91511130903511402d40c40d03449055203001c0741c0000b001b01080e404440140d6002510b1824480d00703460801e001c0d2 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 43150616 1250 43149366 43149371
    0x1e081201031b09050c03150105040801020d050a051302010c02010813020d111f080a02180301090b01030203010c141c0e0a050a050105060604210204020f0c010b0a090b0a060e0d0602030901 82
    0xa6090b18100040040a02420790082c480c4d032403c0581400b041c0401000c26452000040000e48180d0040003110040d1118034002e40d030b10010303100000c0240106951140015241000281c8030751340d40740015030901e40c16540c80ca0754090302e400441c2c0444010f042c01500c81110800d03480141d0707071200081c0040780306048001400c6100020081100541c1110444503200c1341030810f922176100301b120754081d2095030700580b5900c1c0304412000c90030100e40d40d41c0e0590310b4003008006019491060300c0c103ea201301d000380905182e060045505001c0c8803110200307528248a00b1902e47d00740400c0c000480c50b0782d0000100c1500c040b07009450840c48074015107241e0802c040000c01d210085c01180c1d0b10040c1070701c0c40d91405180078017494003042204407101d0206003050921b41190f6440c0c04440c0b0358100030ba200d40d182e050440780c890003130800b40000b80c8965803807074000503540090701448158080050400b604d1500e8480103544246088070001e0344070107203640c1040007854a1020f10b010f66401c0000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 43151866 1250 43150616 43150643
    0x3090c1d0405010513030807050c120f032a040302010e030f120703080f070801031b0f080f060a05041a100302040c0527130e12040b0715091e08120103 66
    0x26084400180c0300c0c0c115112105d04640200360041156508100c00d80782680d07580100903202400c040c5090040e11201200181e80b204c4404400c0181d40211140d80d030540041000d10341044400c03154440c041c118020521040001d036020f80454450048083c082d190511088502c2c03608082c00010950380980c008242e0030141a071000d041d55005042501e210541c0c04c1640b00500420414400148000c05229440a8892000d081e8100404019001940d0b66480c2d5080a486140c150044d4080348204400110240814003590f8015a0050344100e490f05000324807059442c8010300070401d40100c500004010384580c89041c0c074103806590341315201c80c192070001100c03440b45500d02c10030060054848841d0341d00c405d0031011402480e84005001d030351602035203007800e40c04100100096000f040004040d94840b008019440c418055001580610b4035000221003030080e0152110041d201c402e8032070340c4850200340d0240c1c040c203161400c244451109040104d0260421604142410784 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 43153116 1250 43151866 43151873
    0x1009030c141f0606050301090c110f0706020d021207020f01111002040e0609090d18170a0b010609081b06070b09010b0a06022a1503041212020c0d03090c1d04 69
    0x1002c105920b040c28040070303140400042c11804103000d1400b05c10750f500a41040b40b80621380032800004604242c03001e119079124800c0c0c5884072441a007016010340000d021545101040070800f100c0b424111a051407081c6e0207001320340390089102030510480785481084000208421180000381140169a80e81040c000c4003204102030100c2c0d0144d075a40e03003030201c2c1e0380d404039048914900500d8034816044000100000354141c541c0281920b005c0401c8068020b0000b01d141d000e27a6000d064006040c1c5d9071650200e9094030180b1800d016034021004689003a2000800c910021500802c1c0c01d040c14a60307102c10f03030040c405441413101d036035503a000900396007095020700000b082070340003820701c1070404400140100311644807000940e8100444003803558501c0221341d145030f00744c1c0d41291246030500d004000f1042d09401007004c01d002003c00d000c916410f0086030708a28944001d0315a29404280070b40280181d0902100c0250f603803080800c4c0c0740a407010704182d080c00058002c030982031606 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 43154366 1250 43153116 43153153
    0x3050705040504020315061c051606090806040b0c090406091b02031e0d0e0a05030c01050c0403020d12091509053f030c01090f02090601111009030c14 66
    0x1403200780a181400700300400750f5404070f1014040401c48002c17012695480340024039502c0412064541910082000402c5c0321000650b01c24280c58954070424450303ca01080d86c0c042030500c034151496000b5000180014003903014280c00c50210fa40311030410174440001000c2d51040d800c024541980e618201c1034a10340c86e040d85000d02940d00280d49000b4240f15003e07034040c0c820340349940e10f42d0300180200d4424150303440880c01c080340c4815940000c226207031107901c1e9400095070071025804c00e0f01290030ba82030703002200c08680c0c0c0281900c0541d03c0c07942d124884450001d20b04028456240000500740b0020050200415030035a07440c0d10590400303040000c0e021100300d1050090050016180b190f44e00c0c1042c0c24a004000301c0c0d030324682c035030310200c2515512420010320525401e00c00c1c8281080503401303199028a01c21219a0010fa40da4001100c0f025101c030310050300c941c02034040c03054180320743e4021403400d07010703181c54103802815455180810940101c1d00032541e000d10755008550700c040 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 43155616 1250 43154366 43154369
    0x70911270a0501030b010e0904030509090115080f060301180b01060201140c07020f190306020d0e0a03090608090a0605010b0405010206250813060507090501020c0a060206010b0a090b0d0501030507 86
    0x90001100e200d0118148070614001d2034185552110b000c05260b0188a18018900f0020607820030303840d01e1f1400030065044001c189014a16210010550400c490141c07079600c000750381c1d8034400b0344e01c2180501d6004405000c054155598554950310700c00c1c541d1b1150038140c00ec04c00e075074040d450100d0081c21501c424401c0803559848400b801400a80c4500300c5000c01c2d012113906038922110800540006e03011101d20640742c04420b00082000034035000f90441d84042c4500300150a64070329400d41710a1391400050008840e11028031003e0701a525080d00120080100e0b00a8000c1e03503910001c50b8402e0300950b480745404a0300304100c0d0b074100202035014010b400b80c00b980c0d61041c3c0e680c0c0741400301c81b0f5a19042c400c0000c00900c56880400a506201390408003e1149040c4081c01801103d0140211070050241e14100c00c0383d4180b211001045886607801404903a1a046000c4200d80005802d2800c10a262a001581204100c058040c00c16008000141940740d0300c1c02d5803500456 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 43156866 1250 43155616 43155667
    0x1202060906240405040c0e011202130b010c060c03020910080108060709080a03081504020d020304050c06040b070602090f0d05070e09071503090303090b0106090306051b03010314070911 81
    0x600800b1600500840251115a000750b401044603200c03803070001da00810a07007000301155070f4100009800c0700800b580d405a54001d0311810110000303c0743c41d81c281e030701c1c2647d064007043c0e5401410001400544c812821030501d844c0040c00d100c07008002070b100181044103500054801001402007000038002190020b62030700f44500d00615203151141c590706044809414030100301d000808410281c2d8480d82c2c0d10b40010000c65803241010310341c030025081034030150f0781482190b61000346070800004680c195058055140d0500806030384120181d8800c840f640c0e046030000310343c800345840d03480301d00004038030420203070002c14208803009109550007030032800c0a030320009042100038010f8000c100500003038a800303d0702e080b0504043d0081c24112100500354241c0d40700006001e5070280d00101521b11814007440b99072105d40e00d0b08038484000380451a000c108000410014a40031300380b02d00100c0d001c05440300305584040410884548549030703103012000080900b071007500820baa41c01e0340c46 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 43158116 1250 43156866 43156891
    0xa020c01060b0903120c0109150911030c01090b07020301020702040e060f0a0c080609070203090a060f02100603020f190806011d0901020c0a0b0c0705010f0603030f0903030503060108040f1202060906 87
    0x410703000017980e44144a0300312200140004449103100400c0d000a0115034200046d04401e0302c11464040c018030661001b038500c4210340340d402041c0d140c00f00f01081002416540c2a00f600e00344000e03208542d112442c00ca81c19075003004004010303126401140c1040002c48050521490050180a21080000c0c8107003a050328113001d40c0d84031034000040d582c002206860a100b07075500c003101a480c0d44204804541d010310070403c001030280d0700c0883e194640101c0d07801d1320f003040045080e6070165034160000a620550310300003c280b0f4209121503800c911042c141090540b503a07640001d04151080c0c11a00e45d6400c100346000710278010031701e520742021000c0b00031454000d07041441034503001002c600800c05100140030603010007002e800d40d1081908503008015050000301140300070708aa210032400305010304401c5c90503d0007070a030041120782640b103a0385142d665030011591203030000d000b00c0780c4c4140303c0300d480d01180c00d0107210448030303032a42c00a244a050001e401da01c0c1c80310040100380b00c0709 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 43159366 1250 43158116 43158127
    0x304030903080a05120f0702010c050903120307030b0a0810050c0301050d02040c021c0305010f0807030b01060309080f0a12050c0f0901030207020303090301050403051c02030609010b090a030602030a020c01060b 92
    0x2a440000d880440350045682074a507540c4034000ca496220f1509000e50700c584550034030440c1480031341d8090240440b5002000601080c010545248c05011000795040c1c00c14141014092005001507a10074441d03d00002d1185090001822040c1181c01400b0660300455030950784503002c0c42225084104006041d095615000000341c2078084410b009004544440311409080e00030480385070150064108011444544100100200f0b824400c00341031f080340788400510040081a844207480e0404c4500550b40e003080401c1d406441181c03003ca500d50810010300d6201c00050b000307003140ea5115a1210f51405660f55031406440d00900b5820111800b0003a40d24140091801c55002903001c0c2000b6807a601d050000a080d030044030800c54042d401c0c28100820540d110008103c441000d40b400b01c4400c0004402004a00040340e086030820040c400600401c8040805000318a200500485840340c030386e81c1d20010b0340c0094645410203034001c02c0c40701010744203024060290082e2802c8900f0034 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 43160616 1250 43159366 43159373
    0x6031f09051603090302010b0405090c010306120812040f06050c1c1104091104080303010905041709010c150905010e0d0905030a0206090904020d060203010602160501030b1315080a0f0b06060304 85
    0x7082c01069a00b410396a2042e0f00806001f0340100e2030810f0028401c00c803034907207040282d03107c211100303005002078600640440c003210b04003258944242c00029450802006000c00d40e120000035206031292900c400b50000080d446001d81c40c46401d000012036280c2500c407504035003042090307590120580c1403801c12500b88400409032011144c01c0c3e44042100c4c40c03030006001c200e00c00c80c2c00241141c0000000410704401c1904820f024921a554080c40988a1201140300f40100d80282c0c1c0061107558444000c03d100a5068224050b00d69000509a0460b038500d4215001032810a4954100d4885c9013021038101a80c0c0e0005c0c04140c0103010031454680c00104548141d0b080e0360b11074640200820b00355110710b842c08848540c0320354110340c0e03540c540002940d5154600c1c03804006250100c004201948203004855515001406d0000f16a116084000250802034004014a0038034000061051000c101450713196010341c2d8480c094485070300300040c00100040c00305011381020018007001 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 43161866 1250 43160616 43160641
    0x1401020f060a020904020d06080303061c08040509072a0b07031104090f090f0804090516080601080705130f0906080304054213050103060b07020f0f06031f0905 70
    0x1c102c00c0300c0016030741c03121400050000d0181740c10000c0b0041c13a1400206100c40000000c50003050211407101c4810002125080381400041c001818244140010401801c03c101710540110060a02c8504544040c44060b504900c0040071705a1030800341c22501480b501c00c803c242c228401c4c0c5010300a60030407035a03080480c465807086148855444004800c8401241e0001032140c1e4001c4140180c1c0d08907080c2040160014018200004d00d80303008500c07040d6042d01200c0c80010f4139220701182d03642e2003006486034040101040c0900c0b02c10480c1541c3d40010f1203141015000c420340e126202030604a004c0c00310f607015008120160300404c818041c550b29907001800000c0030304070b0043c0d05150f071000f01d0040c1d1600c1d0400e0b1580300d9180700c080315409601c0007600054a00c10410040e03103a8400046081d03a0040c070980d940348000b00149405401c02d401600348034031020b44440002c600c9a80454240c0c0c1c0210f46811301502500c10721801c0007a004080d80c010441e420043c4240c1c1004540080c8 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 43163116 1250 43161866 43161871
    0x5060c03070f020a0308040303020601180209010804020108060d05100c030f020304030c08030903040905010f050f0907080a021810020a05060108060f071d03120405010306060503040b040602090102071a041401020f06 94
    0x202c210600384001c40d503400410f100139550080380036441d01e03924900a541e402d42070140c1240780300d0b8651003260000552098403411041652804580d407119001990b1480d07000e41541d03001514411428045202041445001440c0c4d05000401142d00200107044032904002652214010000d100c04207500120305560301ea000640141c1e240ca8048007036103036114680c410050305050100016500554950800c2160015110040c15444060821010f140121004000b142d0150041008070300141d0251142c203465400c0d00d50203450f03200000d600c107004603000000590040c83d40404000cae06210540c0103010700130052825017030080721004e1005008002c0070400c5543d004000c000782000706d2941c1c2c040303006400d440c114461621507510341d91141c0201e0f40030074100f02002555a202360202c0740f01b0354000110710781d55103e0f60b035542c010b0352028540c681107201d20f010210301c10b0078030110401c00c20782d10b072400f070303079661420081f00340d0945101006c506640040407100c40c0024041201ca5 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 43164366 1250 43163116 43163123
    0x605070503030c03072a12030c12020a0c0f050a02011407050a030e010504031a010609060905010203030103080706022a010605010503010b1801020f100609060905090a0f151107030905060c0307 84
    0x54a9a985da402240c0f03842d01c0010f941c190040c080d281d092485020313851160032600803124020686041c0790198151028445207000145450140c0170308000540c2c0503094040d040d2900e09070301000e035280d0f201d44500d5281c3c1624990070003c0d08004560304450f410041289a0f2400750519005842e016103030304e40d460000c2d0912861030a070800b50f80c465401c82e0059980003c03003405540d491042051000d800b405204041381b0a1440032660700d02601d0400c0031038105034019031540c0c1c215920000382e0340141e4004c0300c40c1038090101d00c0c05060840a02d510580006024800c2948803259007800d5812aa0080d410301c44200010f01c50146844211404600214146058500e440004078500525040a40014020003241c0e00c00c010300394111b1000c4951036203042c0a502d0b21a121001280d0054410440c564440f00030f1000007060b25510012041c0925113840c04900c801c0c1c171180680c0e8103d00740701030080000070007100305900072288002030700d0300350740d0f650070518401000c80d540d221741c0310046c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 43165472 1106 43164366 43164391
    0x906030705030a020f03030f030c0a02101b030b120304060507110f0307030215040b040b0c060709030b0109090c2c1e07080603010b0a06110106060507050303 69
    0x14001c0e100e0040107040500d285600700170403410803190481e0103000c244a08641d00307520401841c03060003040c66541e550300040030000d00700b010070303a580f41d00369142c1158001100c0c0174642000044559080000d00d1600940000d940e01d86a59600c0459110006011803205c0e8480040e0480910910b84c0d91040072020302000f411000003694650544e00140040015107000b0811540440380102c1141c80e140d1074044007007650313001d80c001c520f04040001c1c04240d101020410b80d03500c5005032814440c05d0341075580c0e83d2081e28040c0300d007000080d1941a0007086c0b1400351070240040640c1d001d0240e030b0445182503800160701c450000c0f030a04504100050214240c85030964110704803580b0340e8510703640c00c00c0944001c040a00469019941c0303459246140e02c0c1e101100000e0320241c1c03904103003c1010103d00742562025085182080000d10295000501c008280d1350015402d40e0003 = true := by decide +kernel

theorem cover : BRFrame.Cov 42985616 43165472 := by
  have h0 := BRFrame.cov_init 42985616
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 42985616 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 42985616 ≤ n) (h2 : n < 43165472) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
