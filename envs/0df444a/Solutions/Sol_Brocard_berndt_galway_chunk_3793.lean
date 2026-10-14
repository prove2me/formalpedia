-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3793
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:41:10.702849+00:00
-- url     : https://prove2.me/submissions/94f4f377-e5f5-45ce-9e04-9052b6144d47

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 682014388 ≤ n < 682194244 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 682015638 1250 682014388 682014413
    0x109020a051c05010612060e0a0b0705090307091e0c1803030c06060513090606090608030d0c17150f0609060304020d031101020d23010501021f09021e0109061b 70
    0x1810b071040c15114400295081c0b1600c40501200f1400c85004401424080102d87e44801e251055900c111030501c0459000032020b0360100300341c604540d8603000320700482c0c2894884e52000c03901d981020f07020a25000d58984544030420080c00801c01c100010008440c1c1d20b43c003080d03c0c01380044190341840070a00c112072550000f40079040124030259034034041f441e07102083d803180141e183e0341e440581c20030005020340c3c4010a055034045c08100e0501320315584a202c0c03e02c0907110380d42d0301c0c0344480440303014002c10107660416010385a00c9140c0f81098002c080e8915514074070404010f400042e4525182e001d0f9051102c0c00352249045603150342c01d100c02d040d103803402641442208005002c5644003400104074081d040507002c102580000189501c0c505110780180c0491007481c0180312503680090103c4000300c405004000420a1130b04800040030391001c080e4101d020000c450f00e2440041e18240b52030f0b1000c0c0d0b1100e103e07540d100000c42e82c24044010310039050000e10039420110310801103c0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 682016888 1250 682015638 682015669
    0x503010b0f07020409080403061a0f060d0e010e06010303081f06050d0b03011509021c02040303020303040209180607050a1b031d18090c0a0e060a032904030e10020109020a05 76
    0x42c0d05200c3d604c0e41e0026401980c41110f03241e89503000707459001c9941c60032b0008550156224511284844001412800381c00002c90b006a6148605414402c0035004055052680815a10340b5612410000d155000465107d01f0340c6c4000c2c481c1800c40307040441210100c80b030aa40d12030416007080d0030413014100751340c540e035415900d40701c20f60190000c02082d00000d04149030016901c1100140c0e05c0b01e1800c40380034051500b4418002000440d4021046079882681262403074503941e520a4501e65800040f02010003910800040015958005005002200b01515100620b207451038414404001510006000406002e02169a1950100741c3d4004802c01010f45582e81481d100e102840442201c24a0042e03000483e918554140118010058982c51640040e685840000700700f0a84c0c0754400200b94480400c80400c00343c0c04208034000d00b8a0404041d0b42d00e0070603003002404003400ca2015841032881052560819005201d10b884a5502174142d202461410007040203404240566 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 682018138 1250 682016888 682016891
    0xc02030a0c0611010c020a080d020f0c031206040b190314120d02041401180b090f120106030204110721050f0406080405060f0f0a05070e032b0503010b0f070204 70
    0x90000003404000709402401c100d41c0c4070441141d00d10042e81c02e40786450144015500000340160100c0c0110080301c2c94040c0e28140941d694200000c10720345845110007210b4103000103c3c1a1844050854085002c0e07070303003100d05204440c00d480c20010340c0301035141c40d0100b520700c00c0c204000003030300703143c00c42103408501042d11590b400024050b521a404a404c07581d66507400a420720440740003070b0090070341141c00e107031040c0c60315000710b5128010300b00da0062640c014000310b52035085565074810042e0718107010b04a00c14031104080640c1c084e0840340030480c4102e040076111040d07140f054094440850308045601420203807400350340d145c103252014680800030100065400a4183e80c0100001c1c0200e9507030785064540741c10711600b0518080e0000c0b40d072b135452100b440040c0310340b070b03000e541c00841403000000c203074940b002c0a5800c6650100c40c3c0b500340c05201e06000750340115030f144070444103525080309880f907140c01e0212010302c007d00a42c401c03540f00348107801d000302e41d010140034860f02c080e20 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 682019388 1250 682018138 682018153
    0xf080a0615170a0218070207170a0816020a05060c0c0112090c030f1505010521150a020d1803170702120d05010503160b0301091802060d29010903030c0203 68
    0x8541c00740e40c1000c038907946030f6440054000c1c11424510003861914411801c01d03501c0c3c1c01c25807802501c2e10401c1c45410048007124250004004013440b1810300e036540071b55480e68404035445501e00d00c0c800c0403410380c403401c860000010a4103001c001c64000d8a803c00c09480385440110040d1004800d10000d11030495851034000c0c00a4511300700c40002e18054200841c900b099460580c07215040728070064020790904004006c00d40324484002448141610002d110340e803180307049860310703c908420f218210840c0042c4a5010b02c1a402002403828509052040c05444006512000008107000b000914010564820040c8200c1d1060300301050b841601e02100e265400d40c60143c000c22296081183d0780c00041095240410500b0400600d090402807824903200740c070317001800140700e61039005407249400c0b00294014152004c035194000c0105844040e03903c1c01b4001011860850b004c0780411551008503922071180f94800104169a02440300c2d0039a5401c44000c1c0070344004907018400c208 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 682020638 1250 682019388 682019399
    0x2f0c030d09051905040921090b03070503041b0314070f030807240207210806090f06030307020402070c030c1e150302072a06090f0b090a0b03090d0305010f080a0615 72
    0x75001c0414001c00841c01912040700d03007400034500d41c03000b035014488e4022003000003180d0003051701d81c030170070360300b00a9100da03241d0410f5421082040c1c91341982c4000318502008014102c2511821500784804485a031a102c080901511400b40000f038503403401441542d00081003800000110300e2554101741c04243e224072194140e0704610422290134400d41c0f2011030b008500d1340c2261108800b0318010f00241803410106049070b001408120102554000046254400700308031155550301610455035090035003010703080f10b030540c00304a42104000c0e000184051030203401c00c0750910a501c0c0e4051f05860200000c4613403000e80214014507409008c5403010925030510412444002d25040d070180c0407040d060b1080043c107811030300510010b0801400004462004002031700e200c20701150340c488081c00050308035011035000020240d000404c21224101c085001c1c0c07040d00341504c042c0403030398031800f0300c2500305400e01602040350f01c000c5500c4d0104240d074001a0b280c03009400d03441c5100d0f4941 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 682021888 1250 682020638 682020641
    0xc090a050303040306020c0c0108061e042d050901050702030a0e0109030803010b0711091302010c17270d11101709030c15040309060f2f0c030d0905190504 68
    0x284d109483d119400b15070b00f100d0200910120742621401d103031030313100c3d031401c5000a07076411a83c00851110740d001c111842070303e498130740c40b100d400861406403d16860182e070902c1c0c6600c0c05c0080500311a41040081030101d001409601d000301c211360040d508254010340c0c03c0310004010303c03c8504010744901c1c00404203640360000c501808019645a50f80c2c80d15007030642032101e00000c15070043c7d00507810442c0c88160381e1500c810b46982480c0152805e80142410105820b401d001c03aa580140007a0642140740c0c2c2d1480984240030b00c1080710320083c1540d00700700001e245801d010b803071081c8150510f2018036159940b44034051240c01c1c082c81c02070f040c442403044954119061074271a48001841038040d00200280301d84c80303400305038204986c40c02da41c00601e80141813040c18103004010ba4002c46141c021240d01c40c1d9455500761440502c415030103080308030400c03204104e03c28001c448070394030325040c0402e502080b048151503001440b0310b40800e100100030241c00129140d001c410011520b555207 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 682023138 1250 682021888 682021897
    0x80f1e010b040617010b01082809050607020d11060106090b0307020f120c07141005030403051b010b0f01052802070306020d0c08060d0b01090b0a080604050601030303230c090a050303 80
    0x95607003d0312403135040c030094212144030f040c10307040c0700e200e1042200d100e080c605100c0300c03491400360b03c1c94605180da04510203410b4002004140380070b6101041005e50b80052440d035200b041d80d88115004100d80c401644400c402c1c0600c00005104000500661201d200210b4002c07580380704032410000525450b03410080701100d40d1000c2940001c41024100e401c0082c0c2010b0b046000c4088034856015001582041c4001101418020040006014140075030183c40032074516003e8401c0c0c040241052500030182074440c28442c01c005240c455440d4441c0701541d05080d80076100c2e4540b03882140fa0510a5016980340b58118894041c0200c000b03512400903005a10121307034041210001258054082c0c04001e08843c0920820030711840441c040c5a80b880c1114071a010014012904c0303004105584032580009041e03200306010b0104001001402ca41224020b5400304050000310600c215840100e8507841e220041110115149081c1e1000a05602d100240b607403140e0b40e5581c1c00300742141c10 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 682024388 1250 682023138 682023149
    0x6010b1e18131b030e030702040506181602061e0403032f040e071b062a020f0c030c03070501050c10060e0a06050f1003020903071802090307080f1e010b0406 69
    0x840d959034598481c000c012100f51245241002e104020241c1c130b080e81e40740126580a81302c1c5481d000407651541301e5811584a03030703114103070900340c80c1f619145042a071840400d000b0018401c103c001030b01d268240d00c0d8a014140000b2504a4980301c0d40c5085000c4e1218518040c2d14460440d0007180d00403005078a04c0c002484404619100d0f442c0c0f15510400d244010700590521022161340c4164075003041c0c85055a9600000000300c00442c145180d00107040f9003462210f55406110b500807580d0001000001500c0d01030444807664081d0302499260340360300041e81d4042c2c0c004a014000b070740c042e202610700c0d441c4080481c0c0c485030032003d801c01511450b134091000941c03400140f04010701e4ac1d0295034058442035800c1d000e003061000205140ba2040300b102c20406034042841030031981c052088000030b010700f0005802d51086100031000961009884500ca88103410300002c4050001c541200d404400201034940344041c008040c02040da180d640340f0b40c5543e00c0b500c2910700d60750351086030061324 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 682025638 1250 682024388 682024391
    0x3240315070f180302030a2a0902091908030316021207030305061309050d081305011506030f0515100516080a031a0f060f072306010b1e1813 62
    0x10140a0404008070086183c3d1440250062001d41c6000601c4809550311050703402940380608203051110904241071002030300c3e0120300180d60202c54024003200c00341180c00201c0e01c003a070f0795151900344d40e5101316806904103000040b414018600c00c40320b42c00580c01903c6400d985082181c000c0e52101c036003200030a907200d043c80041d0412460002070704521110400803900c4079102c40d503aa001401e04c07002008440c100045002c000c0d00413211740740b0382c0003000f841040441314880316054494021800040d180c0514181c0808850040e02e000b01e400117141a00c0480f500c00b880280c40c10181c10b00107100b020002150380200764145214607502810f100750b11080f04180050513600c0c40d00d064001c100c0c041040b401d1554a01b2a90b00181c4011030704c595940c041e040c0c0c070035018090700704090a0700d0820110780414022248140400500d00400e0b100141c3e00d03501e40c00740c20301500e401e102845003440d001101884600e8020521001042c1000707040f0140540000d40340003080c11030720101c0e03 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 682026888 1250 682025638 682025657
    0x1020f0339070f0212010c1e050a0801090213030b1303141219110a02030301290304031b200a0e070e240c0708060105060324031507 58
    0x12020100304500d0007854149600741c82401014242060094400180025520300441e804640e0751242c610840d05201000703018800b85418003070140c50201d00c40042d00c006d001020030304544248100e4a10409070307100e503071159081011000080d0040c4e10303122480f100312040807020503540e00c1c0703051003002da01280750480d000500d8028502081c3d41c1e041000403000b1710103551404045000940c0c40900000c10000c0c01c42c0c4020510301800c0d0101003031040510028811181a60100080d41030341c0068203841c0c1d0441000422400c200c0c00e198003038104980034000314000a02c05d071010242c5440300c4000e8050542680c5404514050001040d1071100d21703120030a03c1821700d943c5020040c5013030f450f01e41c018940807a025001401c80c083c007038071816480c42c800c5409805e161402c007001d07402119154403041f107002c51a03600c0c99240200300c4244070b0700000240e240303030020440b0302c12130303561064030b800803c405142603500c6444100c0907810700441110302c1c0e04580a20000b8450b107070740c0c6d071003a600 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 682028138 1250 682026888 682026931
    0x1806040807060215060a03120315060c0b16080c28030f0b0904051009050a06151e060f0e040f0f061508011202010e0d08040603050f0c0306010c02010f0201020f03 71
    0xd00c000180b0f404c192282020800006540e0200f240c0c080700c4e041004413646401001c012001061034840c480d0700a0321440020425542c01070f0810301c180d118803244061601c1d030162a80c04010522044d80c0010740a80000d00803520352000740c182c1588610b00c1c3c40300241c42205404441120080190000380d803003401c9500e0f0300c8a40150345041c1e20544a105050030a511256151980045084186900c8078188010008108009100b4071b400c804100507400c0461000d1140d480c0c14407a203400350795040140100c44581c04180800c0b110b1a0701d540000d410b14000c1a10b01c0102a0b802d198815644e220341010360b040c0d40074440600d124500c00040042c181400d9460340301108074488108220792005110000400541d407010300d4090070407a074001504400030360803c60702c1200a0103038202040014005405400842c002d410558050404d0354900a009516003c203c1d2020700042074218600c003d5409024204000b01e06d070710002d45804c94400b5030001c0d943c010f983e900798502859402811 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 682029388 1250 682028138 682028143
    0x9090a170d24120b0402040b0f1f0f0512010e101710060f060c080c1207060504030306090903080609040303020d090f0c0803040b0715060e0906071d1518060408070602 73
    0xa0200003c580c00340e0358140e226070300103110081000340500e41d9040c03000f10b260388008038400c0050001f0702c1100c0c4034441c8009110800801c0d454800810303c1e082108000718041c030181c50718032400701e00346813241e031a00710145e004002c081c0c0380b241c000c1996030020840008980c0c21071240541c10000707212a001007200c1001711074041d44200d95000c44100284903803a400303450324943d03a80100381c003030720b4023448904c690902d0001062039800020018486040180d00d8101e42d204074040e031030810009541e14480401c1d20000c1000500013071030540042c21a01e025140e1070f03005030192500500309199411120300b203844612080d5082c1000300e024034200f1401d000c0090252a40b02c01841c2420710307244112400b03004001c0014800c807804100e04002050b80d610041c01440b2141e054141d6013403070340c03040d922281c094a00c00001800000012120b4500300c02d40303c035150300544450050410b21405010300d400241c4050b044c80600750801c600303565900c016101400364000640380c1c0d90301d0600c000c1e2 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 682030638 1250 682029388 682029461
    0xf040c05060a02070608220309170309060f07030e030d0c05100c05160f050316140a051e0c03070618060f1403040206120c030601030b09090a170d 64
    0x1407007160108066480340d40e0110300001111018144203d160302e1b202e81607120514000480c54041411400203424158481e0800040f1009a40c034000b00c104042030343c50b128400e0000c140c3c0c00c254108541c3c0c80a2a01b000108041c502916150b05004500c00009040295120000002426a0700c0c0704040c0402840441288900060200050031a0b0780703002e8510301485241086121500e0b0f280c006102035400700302c0410340d110054a903070b9208440052120b05032180103854001031aa549903a02000080080040317400c50700429011300340c00c1080c5016803010400e42200d005000510100d42c50400c4201d003d40550740b04e00030800044007003912104842d512000c00c0140c0284d481d50215081a02d1103401805800419502c0c0c2e1035002054407440349101c0107000b0181a4200803144a0210145029403400d0380d00340701d80030401003001450f05003603980b1340d06500301c845800d0000e0402a1205a12442ea624071810000031003990b8080350200c1d500340b6004007840b40c0200d003000d0042e4125 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 682031888 1250 682030638 682030649
    0x312140406060915080c0907180801021b032a010204030606170610030305270d061d0a0321110f040e1003080a080709090f14070801050d060b180f040c 66
    0x3c116920701002d840d0354021b0a40024014029080420341c09846401300303600e0348180490501200d56a00d264500035400544551130011000382c40403807024000c4200c4250145c809558048082d01140ca9850305050103601d0441d507508000010002c2c4150140f9001456540e4080b8408101c0b0034145051a4000b418105081c2041c3c4040c030019410000340c13a0551b120341c0c002d542401103012000d0a101d40c0d11101c0340c2c001d0340514074000f004070a400c05007100d040d41507881807070303800e90460540e01c950f2103000401044064028000000500c01c0f0010440c1c1c0401021800410040b4100b20592006040380d02c9100001420312a00d103400205130b4000c000c0c481d15442c03280c82c503103500701b16001e020501070400c903505c008107814520034403003c030281ca40c0a40030029003107180b01d500010304038800a038036580440400035241d40d01480e0014101c0341b010b00001e004800ca40ea445000b40210890b09a03c1019003007a04d0380e04008442c0301c2e1054103031540d030508508140c1821032280c1c5441c0d102 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 682033138 1250 682031888 682031921
    0x20a080102090102210904110a02011401050f04090203010f05180c0303040e060103020a1701081b1903030f0c0812180c0a090905030c010903031b0302090105040303121404060609 78
    0x5408050340e00068104251171005810b04201c0d80d0008041e807588603404046600c02c0c201207048201e2100c10004102d072040070740081195103030040b90200c3c645401d20600f81e1041c214040c004140c20b05d50000c880c02c5100400004000b03103004ca0040850340203840c480d44110004500c032050a1041000c11402c240c11001181030524114055007a140e00601d050304040c0c01240c54100c03607000d014845903841d84900707035080340c1d82c60300c810035902c803201c5c806a00070304030455004005061801c05814165184d200104290342188c80544042050008020800900291180c00305401c04050045041700e00c40548072418041205082c0584074041e04034103803c5001d00001643d104a600805c58011441c0403a8a05550130304504500480c0e507070240550820144004065040c0d0294000c0000c400d421821070342c0c090000c500302d010302801140400c0c0200000d00229010329002d04040300003800114049a980c440c2c51808041030700c04840c12902d407101445800054040e0301c0750804900c14 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 682034388 1250 682033138 682033147
    0x30302100b0f0d021c0b0a0f05010e040204091412120702060f151309050312070906120216060c0e0102070605090a0e070c0203030307080105031002030420040b0406080109020a080102 80
    0x16210008042d030181c0f10343c85401e034100c115100c00000030190803480040d0000341809003448540080d003184d404d80d0b1503282c5900b41210140318032649040e19059100c00f80e1559072907091100400002209a035845a1489002d00d001410032220b013200d0a0301d900e05031140b1900303c04400d08080036083c4d01c02d64105000300000c81041240466000074440040505200400c0c0400c0640002892200d20541410f160038144a00000240100c8460840304a074680e1040c00483d0141280d01840c00050a1300c06002145001a0090b181a60610380180240300140da10702080703d032061400310100c8da920641160380d40c2c06014001c000c00040c1003581ca000305210001710850f1039070103804816486440458401c51080311202d42455000d02240d643c0e041c00f280260040c0024890fa501c00c0c401d000c0036450300d95440c025a4041d5610013030300b1781c5409000c0e404500080d4a0920140c0156941c41040d603a42c1d0380d40200390041051000000b220350850040c02522122030b08a440c0c260700401 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 682035638 1250 682034388 682034411
    0x21080a020309100b01111b030601050f010f051e04081b0901140114040f0314010b1e0405090a1b0e0c090607030804080d020f1803070501440103030210 66
    0x228014000040700c0f0000340455890010381da450240380d1110703842d1080c0580101004901c0280c8203040e5401c408440d1660703659010400c100d41100d41807800a5000d1013981840c600402c050078200e00c0408412404011510043d00d440e0090780c0440f006070300807141c0808646000c4020000d828090f6052002076050440c18280202e610b042e10317042020210302030310503103050001e83e0054085003000b161100e959091a0041510804a6842552a0955500540c80d0000800100b01890b10314000340000d050b0400c0010300c4028100d214034005d108a00c0005100f00039242240511180032020003403c02e02162100c110040c0080e920610400034108944c0d40d03d020380782039560514005289581c1e514002049029516011030300a0020802c52181a4007401401d0146160351001d0b0b0604941002c2503502c0c0d00e0391095601203000c890300c03800c030842c142e003e1002d02560600c0c00d000d1580541c4c2d180a00d000b0070100c1c10000e441c500d0050003016414403003810300d040d0241c0180310b1000403d = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 682036888 1250 682035638 682035643
    0x30a0c020c150a02070e04080910022a03030705010e030c0f0604080403120c1a040201080708100e0901090c0f0e06060406020303070e1c0f020a0b070c050d03020a21080a020309 77
    0xa450941c10b40d200402e0b0240c07030520810a61014114000c0e40c0c1c200c034106842c000c402c0ea0040c0362003d20450f20500712580080c4001840b00100c545218121102c1c50305454441003480c1c0c1494017500b44c0420001480815424090559490741000c000c65403281d500412505202110b4140302c21074210b1002d00010807850011707581aa03421014802c0307a044044c9040e80c03c4280e040008202c0d101d80c9450703426030360718030304441d01c40c90003038030340710025070b6100d808481840c0200c40c518000620904140540c0910b02041a80540c07200c000050280894407800d1030700300030303a2229403080103416050003192030001c602c64001e0400c0e6042c07030500c2c0c101940a9102c0c00010118402c0140d00c60f80d45440f0307964100e003a41440e100340c80b00c080c3c062541c14031031309007484c0400aa0045070580780001d801000d81089462b031641019240c200d00c0d04000170400d000e50349110503421032042c04500000f140700418803400503840060045903240701c139000070f84201c10003002d084e0450703c11700070000480b101 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 682038138 1250 682036888 682036909
    0x9020f060a03090c1508060901051c03031503060204090b19030b0408130603050610020d020a081e0c0a031404030c0311210a03090e0402180c0f03040305030a0c020c 72
    0x403190a521140c160300210003c2c0955800a40704410041c0001107280b030741707500b0071402100c41d07540c11016614a4107000071081700b849042d80080c09030402c91560a400c0c0c2d0910380c618402c0c600401d0300c0101c180034028808640d0002e90340c1640c0020f0810a00d6260b1043c40920007050b0f0380006501203181001410900f50311016100b03104210008040080701012114428241c5954100c9281c54000c010020a02246d00e40d0240d0580c07001e10018900010300031b030810500f070380104000c0703005581d44202c9030032207811100c41840012502c0c01d80c1d4513100c090f0105880100c0100b02d041c1c854100100103074805070f078140890404110500c04580341d0017501050302d8100c8460200f6441c080c003c1103440441e1002d080c0682800e0f00c041d00c600708085803642c1401e0080c0c1d200741c4d4007034a5080322824039030300707540095106640c00d11402c150099130300d00e290321201d9500114141704015006010076803041703404a0018100108129818200d8841c482e44007030b46100400c00039480c00003080100c802c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 682039388 1250 682038138 682038169
    0x60c093524090102070602130503010506190605090103021905090a1707170307021002010b030c0a0b04050108180102070501060f12050615061b060105032a06090411070b0402040b040902 81
    0x1220000e402140c09404540c81a98031200455980c23996000c0101c000b9081e0182602c0b9508103400714000f803030b04000300814000040d5040c03c0951400d1400e40300b55000d034408170b06142c1c09115550140d54010380030701d41c0381d109894860f1350300b10f0032042040e81c01154000000d40010801e00b030768801710008600007954bd0141c4c0c3c52020700650502a031640c040d8010096112419032900c1d98440c1d070641142d6503803070082d17040310702c071407009410040c2520841c016145110002e00c010092076120704241c40d0045d482d42110082d80141c1c42c9102c0c00c0e82c0c80a0000e482c2c40e034580c042007003107070f450703100b80d0300204198400700d01c0c12001c2e030f5100c41d107454000c0c1c202c8080c0c403221716109030703903070380e19000c403046052030007a6021883e104c0f03140b10352505024401c2602c00e01910140702d0808041441500380b0151030b4945115402002c0c0c02c01890ba00304a00e05904641c2c1d46030070b0000d0011410080c044140100e814290b180340500c108800e035215080d070b032400341d0b04000394140161a00024800c0120 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 682040638 1250 682039388 682039453
    0x1903050409090609210e10170c0f19080709080303070e0f060417010c03150e09010914010203041202121606090c0b1222060c0935 57
    0xe040f0705154000c0c000c01c03031000c4c003002252415506000c11808808a04403542d031252003189403804200410742d085510400e01084421402c00d41c200f582e103080640c40241502000d04001800e8002105504000d060180c0e183c8100f08807686590071090580e030100103450700c4615942808034050312800003510802c280159218501c00300c2c0d850b0155072031100d1024203540c3e140e40e070f100301c000071903a12554203461079484d0600315880c9030700c00d008029885c0c41d51f185400314185046c040c016241c030000c042c00d0f0716568440c5030900042089450030f4400f50000c001586a091a0800c0b034580300704a0294000e55110440c03c0740c501105070f0684000d00300c035291000380b009c80da05005001d040c111100030400c041c182c1c0e000c10b03015030b020060818210341030751100751991803041607846244420540440407051031040d000140090708201ea400a00d450001e81285d600c0306116180e0b041c01400c916003d05d202207419488903580300c0101d03a0111702e801003408281d10200f100541042250522211 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 682041888 1250 682040638 682040651
    0xb011d19020c100c030212010914180f01020720041b0309110a0821041404110c010606052d0933210601082e0312021903050409 56
    0x1000c00d12090080003d54007051110700d0208000400a51100700124240208003001280049051107110000d2201844900d2030b9100d848160740c41d2a40350441e00c10301d00c0b0f85034910b62641c1003800580040f0f4270440f02c0d4101c4414440d031004090421303000701d902682c5030546040150701000306d40c3d4100d003003a082c001542c0059042c403010040c00072100640024080c500003450342c1001449154030b4180080c48148044200c0e03510540740300e03c0c03003400d0544500308001c4c0202d10f01a405034600c1c020003482145890580c000b4a42591544e42c40600400c1d00419440c000340c50032500c0364213104501c45824100b0541030320b0450b0a0048608007070041c100f82604030031080d02014400174440540950b40c00710718041d001c082d0a980291414078070b0b50030368000100901520014140030700416121509542c0d100f001040407001c0da411540d901401807a210000303586611204006140517000754219507008440c040d180601c03c4400440d503d100840410100340d01c501550203581c1c02c40c00201c0c66 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 682043138 1250 682041888 682041907
    0xb09090d08010614221a07050715050c010c030606020d0527042004140f0f040911040603050a20090c0c0c060a0e010e0411071e06090b011d1902 63
    0x980036098800070000c590f41e400c440c175003030240d115208880c0d5030307503e006030581562110300b03a80c010403c00818903030207405c041c080e41201140040100038185022410240214040b9082d02c0b40b1400b160042982e42c441440362941c14490189a561035041c0b00d031030700082c042d07451554810354904116041040c1c038546541e503a56044000e80e9008145006451414500080103075032081c42641841191003407040310303a0420a21407410044010500102150f5000070712020f041c442c14200d5104c55580320141e090341c1c940c81814007942c083d6004020021403881c2c40d10300c200880070700048455000480c040c0c03658420310080e900180450241e03485540401c0241c2c45c29001c3d41074940d003d000840e540d0b8100f6800422102c400380300766541440c0e20100014402114a0b001a410403a00108140d1011894103a054410024100010390400005844031022240b01c1c400c01c650b04142c0100404c000b01c045c0c800c510000c000b44101111170f0402c0c00c0003804107003143c000ba00c40716402280ca42c50 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 682044388 1250 682043138 682043177
    0x20412060911030a051b0414010b0c0106050406080c01031104030209240d11090a060503030a03020c0c0a0f0f0803031e0a0914100c14090411070c03060b09090d080106 73
    0x14007030b0301400b192150200c80c60116252001d5614010b11180750110782813051401e8040c04620340d0345003c0c0c1c4800c607401c0421602c100e0340115040c3c0c1480d0748a4400080b180ca840c4510300061551501805000b003141c0c0004083e100c40e40148020034400740414400751380c5001c4901c1d0010700488000384c0001c00c50006000780d9800101b0984c1c8000481d08800a1103e015445203c01104031042c46c901e0313a0790a0194201e94032801400c0d0950300030b20003541c4007030080e4000c00300e00c0350741c4044802c40d510900c001500440c50790022010556030075020840441080c42d982c01401651002e1811440d0519140c0c44203070040c8180811841c0100204e103110300c01c4c0c0d010304107054004e0280b06011034411241170307a54032681c100400b102c1c80d10082d40240c501c100310015607014100c9201e454440c140c0308220150090804840c00d90000304440c50000310402101d1004621030784000c2508800202040300701c0c1c40c000d000c440e25411844104c442150302c15901819214141041c0320b5500101ea030048 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 682045638 1250 682044388 682044413
    0x30a29210610031103011811130609020a020712050a2301020a0e0a080d02071e050d06060503060f0127020c0f0606150423031906050f0a0204120609 65
    0x329024203410b12640001520303540d8256400340c03100700104000f1000f41801c03200f031401660011044c86440000180984450704c0243d00c1c001c1c40095108a0302c010035049444641c008000d4540c00980c10a40305d070103200b03820041405601191a41a01d40c03a000c0c2c1b0740355442001001c60820001d5001c040c11011209401030140c0e000131501c8004201d0050103540440002d54814a102c540c0094007501c001103982581500e0390145c07407614a089410010400c000001104160318602e010944e611803005460000380039010100c3d0191403c0145030900c04060030400c045440c400040c0001d00720007080750480f0b1800f0070020346130031a68507141e0084c051981d03200840c0c003414200601002000039020b025800480303104e0314440b40c2203070008192040d44100010b94040d1840f04002d042c5240600c01c401f0005000c5e91208c00407104242c44803241d04000310354442d030f01d90900c051b4181c00b50819070300840ca0700085207020f040a245404005080700c00500081d200ea0380c82b000c0248030b10004 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 682046888 1250 682045638 682045699
    0x10320010327030806060a0f030908250c0e130f0312060b1b071202091513060303030b0904110f01021006170f010209010e090403020a050a08030a29 65
    0x20100c0b5030024101006000112010750000303840d600070a42c90310300401211080d002d29101c414a41000640079005444400004e950000050040030804282c07404400c0a12001c00c0104c60210348070325006805046a401c4800e506601404200d84603e412125031b80f09030b000780946802c00d40740e160480311000a032014480c61810014002402d101c0540580700c031003601c400c1510403562900605a9608280c49410702c11088021240058201419040d070001d143c02c0c0c0c200d5100c848800803c08e40c61407440381204282d0b0341d000400a150303262050010708501202c10280700d051503110603000c05a02100c0501c14883d0103107485040c1c5c000c10000c0000201001e0520195544a228849010380c2d105060b0840c040c011130519400d80620845024002c16140e41884403003820074091412001001142944505080d50317010a004001c102d0200d40300b029030701daa82c50b114148105503812000c0e1025010101a0320399218051414a010341c91416541c20203811030f90420f42c1c0b803001080188 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 682048138 1250 682046888 682046921
    0x105010e030f0d020c01030e030c031e0c0706020606010306050118051002071a04052716030908030f04021c050303041209050a06110105180309012f010e070e0103200103 74
    0x43c95051038020880441201c3c09807800c02213500401e40440d128800e21082502542040145105500480003c00f8005801c3c0700d1150600c42c01c502401e11b011016000200960301c600300700b008030b6a05001c0e0402034402840e12080d1400444030030b2100d801640126407146401301100d6002510800c558002401400c9400030039051b03810f90200e50342c0c042d00804d0702641400041c109641901020300b200d604103241091000e940706c114103055048110313158410141ca501c10b550100d4010703406180908103500407032a590500744100a0001520210740006160004d4160702058010003507a6200341c020800c0e101900031318904840810703145d04141c0c0d010301c40000101e9107581c0211480303410f00f0564000c018540320104019555215201c2503021580308100100c0c8952080c903400c0e10681d07554102800c0340039001c5140c1c0614460240800890395034074443c007500314007003000c1c1008281c0d50001d05501d50464548111461b000d200e02540686150b510340c1c0c050741b03c3da0120500d01480300c003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 682049388 1250 682048138 682048153
    0x180c020f0d0c0506011d07030c0207090c030509010b0f130203060409331803210f0905060a0c1707091211130c08130c03021305071d01080105010e030f 66
    0x10700580014901581c492140d075002007034035076942c0340131441418451b0840926a4500100700c0180903414a010118018404006540e014502a10022044e5910080380c90b152050401d0b00315003080328964070032040301070020981d446140e01c080c0000031401001d40e0720342c0c409003c80d001e0701d0a00c030002c00d1030414012440100f001030175a044003400d021a40e03c08451501d0709502a61601e41110300c1c142c1c4c0400d03030240001d0055080d481601030702d0000b080c640c0d100b0041a4200e82c001c4039a508003c2d1a0303000384013000300600c00c09620010000c0104443c07440319078010b01c8210480080d03012441d0650205031010f0141f0307403a80081c00364094082c1d04201d107180041c410155680c015000e4801024440700030006c60150390600800c4d41d844081c2e41c0d5903c030700c9103c880400c4505851503000c1d01c00c04405038807262a00604010306030400300f42402c010300010080406805500d51400d4444035140140e030f0f005034414116602403078280803007401c4200083c1000c84e030408400c001d216241 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 682050638 1250 682049388 682049413
    0x11209020a080d020d090e012111031b10140d050603250302010807050702180606130f05030c0d1106030408090303070506091c0806041a100512010f180c020f 69
    0x105140e545289549050346d02d80c0e11180c4022205c000e0040000440d074651240900a107004c1c102103000340200c00f1105c4014039940805d082ca4901180140071000d18400c160392410140246016040e1034604002070440503103262216000c0c80d4000c1382e4040d00d4002041c1159410852041d0305a0708015148146144284009804070301c0c1c0310480c082402d0000140041c0d018006a503d0240c0184c0950002074906281200441005024030b50100c420b11002038011100c80e501c401400c2c07200c452110b054201000c240ca40102e03c00707502d02c90b500a2a107400018603044041c0414101501e101b078603500c0d80d140a1010b8080d02c130819030507200118a51041c4000040d1a5000d20130040a9444407885607541103001007032001100081518400450202e003060391002c482e41d0380402005080c02950030004030010300c02009000094001301c0c1c0d0047c5451034001050042c040750041c0c1220034500801e03521140110340204071142d0383d55080305052402406400c0034400a1380580b5801025034 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 682051888 1250 682050638 682050643
    0x280b040b090409062306100e1c031107031505090f100203060f06030a05040c14031509030f03190f14070f090305101a04020304030228120807170402011209020a080d02 73
    0x1103400500c510807a031144803100340103808c0c0c41005600540b05007641603030103080000090000808504010181c0e00010444100307000100166104603c413128960389114102c0c00e45002a042006039006260740c84486040003441d0b150100302ca41000da103d903a4840044c60300328080c1136240c1c0100000042001e45007151f800180b06178418004100025101d81d2080c3c20700f010f010303e441d010b070300880810400301100c5102c2680400b000c4222480d00c1d005455106441c0c20941e01110083c41c40c01c03140440c0012401b40c4400d4196a040401c031012240d401102c1c051405001c0609000c00c04003400052442054084051a000310843d82d403094844065001000081802e910308100503c00d40258a014000c0b0390089406500074007400d1180e4000c005035604040a600162243d02d0404002602c000000c104205881d19003e11500d04050040c0800c18803080f04d0303000d642607408210051780c01c484907034440c280c072240020b044030040c40815410042a001200144103411269042d40d600 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 682053138 1250 682051888 682051891
    0x140c0d060e0616081306020c01020f0403120203070506070815120304061202130504020f12130b01060f1e03020d150311030a03050a140405280b040b0904090623 70
    0x2084102d45181d40d814004122440040d0000d030000f40e484008100c12503074031910414070074015400180307880b4100d00451308a0744090891200310030086000c005001898224006d0000b01d80084d500d030810359074034151591402041d010138084840007240c12030510316030f000c100d0710001c0c00641c0c043c0c5508104941e20b42082c41054005040100d2403c200681402607541d5802c4803ca19118281414100806500700e00c007040c52910040c007074000300480c0c8942e01806102d059003003c8043c4100d0600e060320301416003284080c070001303912106a2660100d0415480c61a10002d10244518030304110007902c41c1c0c0d4040d017034141c02c1000100e1350710046d411070702c202e070f02c240307851603800d4144028075445164010024000c100d0074041c400e4074500034050580018626079072079140a45540000d400c0e4011840b2001070715810480d0792800c046a21030300e6003d099030b601c1060405203408030101481c424100d1403030281c0c0e00c0d42c18140400901e03411650089084490400310200700d1880829103960 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 682054388 1250 682053138 682053161
    0x909060a02160b07031505010509030c0904020f1305010315050402031b03070902040303050c1b15131d1503060603190501020f03070503070e0a030f1b08030313030e0307060804140c0d06 81
    0x14806c00000c2c040d806242180c422602c0076002e0111f083d814010810484002030041ea04950009c84000c05036035040303213060318503550302400101035046080611100741c80040d075442c82403801d002c0c440903a800040b804400c03414401c0c03c064010198001c20f082507501d0303110f0fa24040c008035001c4201900316004e0490464800211000aa407842c05441c85100d4102c586400031300c00d90401242440000040030000304a03110307000380326500d03001180440010710b1300c1c144005000091000a10105420b464403800c210002e100c94100100080d44464040301d1000d21420500c0c548010000d00b901941c5415801440e41e58807441e11500c00b82c02035004403102c0b0300040420313075008020b2612248010940f50418150183d0480304e03900c2440704524141c44011900b0501d00000f014002000214464070f070048501000c3c9015190140c039841e05401000c1c4030b1380082c1400d11883d41d1004240d5480780e0024450205c0004400c131071030820041b51011500506203490300010311504e45c0001074400e6 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 682055638 1250 682054388 682054421
    0xf0b0703201806120412030902060a050c06070c020306060d0f06020d0e152202120d0201020d060503011a010305180105040c0501110613030e0316230909060a02160b0703 74
    0x1d00c02c200b10780c03445500b4282ca40304541d00702090110b030001907440c1034281c1e64100012040300503000600b82340c00c00c030341000001b04001107241001c4018081d81d50840100c2c18001e0340c0c10650790000351100d000500060050651040b01010320510340c088403036440d0009002c40d912008520000060020507890280e180302d080c1201d07881100280c5600d21032303028a20b109000061080e250000e044c0c0209050340c1c400184a0307140030b01401806040d00011658000598520a5000a17000d550311a484644642d2410b03014050041880611494424007440e0006055840450804203c0e00d9441d41c0403042d881c250030801000980007044094900981750302c2d504042c016811a42c86000300c600c440313000d503403006020000f4000d1104d1044410010241e07012020521180412120594425803a50b507e404a2042030168507406140b01c05090ba408000381ca0124003156481d0805840e61080580c00100228120402400340e08200c1e402031030800c05081c0000300501034112880c8055006 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 682056888 1250 682055638 682055677
    0x501020304031e0909050424051504020a0e191802030402031228050d0e0703120201020a1b020a05130207030809010605030706110f030a0f0801050a030f0b070320 71
    0xb000051140700301c066076030314000f82d10700386880f0901409015008a6130480311014140300ca41415032310521180c8072501c0025a8a8044c0f26207130b406030450076043c0541e01c1040007409040d0300c030982000300344043e207a02c500e201e000b0341c00900d40d00741944910110010284000d29200c0c05800850056000324111004400e414100340a1445450038915040c00302c0261010350400942110551030414200542481c500e0300420060318030318840d001803a0407a0764140104080d5091140d440c0015100031802d20385000809400b400340c070301e240b42a0350b4007a4102c1d005c42d035499000201501010307000a420120440204d00a508211000c401040740807000603c2d0000c1403141000b1500001e0040015515044069400007021445100d19000c5e25030880701c020303000c10041980300f03940d42d00c1e9a0403041141d802802040d041e080741c1c1c4104001c0314200045480f12166581998100035256015112104168010300c0070301c044041e1a210002c8030020149154050692480075050a1840 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 682058138 1250 682056888 682056917
    0xf0a03030507140904180507080d14030405061f09090b180f07050d03020102040305010c0c02010210200c03270f030a0503030a0209032b1106042f0402030103050102030403 75
    0x41c1d54151035004201d0001d01121980789881d800082d80c4010840740c61152444548405d030078008541c0018489c1da11070405401d041d54400d00191045c00c1e8134200030f042d03040580d80d42d03480b110301411601071840c40600e14046021185014070044c91210f004009002a40c904a1a90441142c4074002c00802c515103a25901000c40c42c02440394441000c0d00c003050400c420010401b00000080d000c540d800d10002c00050380034450800c0080207070301d89286400c124400203191011010401d05990304000f41c003074580d18101102d040e40b9240c2d2003240d0300c031003409103240d25601a010310f030502200c1e003a42c02c90103604d02001c1c201c08000103603003025207415040f0516595108196005007294410400541802440c0c1c2c0035028184000781640d040c0342015080c100b0300b400d4000c44402201c4103101580405400245805a00e03040c240602140d00c1e0a8848a444a60580c28130b80030305d884010300d110b01d0460010b0703600c03801401001103480e0b50312810318078009d400c2154118040342500005964 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 682059388 1250 682058138 682058147
    0x18030d050711010e0a0b07211a011b02060306060712080108010c0c030203310306140a05040822090608070306060602060f13030e060a0807020705060a02100515030f0a03030507 77
    0x1d080c030000004000c5c1d03086a6450401c08407000f0103131400c2000001764001504144003c0178615800080049103079100c0c00301520110115030030060511070655196101a56080d9920740542d4040328070030f480741c0d940c80103d4840c0c440c210004042080d1328483ca80210741184805060300c450000801501c2107154003a980102c0001000d8003690080c80200740c188030f03503010b01110840c184000080240e6142c988441200c058204440483d111185922004a9110401d521044620080c0301d035013060740343c10a162251985008045400c508841c1d40f04098111410003005214010462a5a121060754641c121400110b0b101400d015000520030300c00075000c0c0c0101c1c0304070844815a100d960003107102c04200b4004400340109254804240e40c0c0760005850b82c6800c50312070103024034100301d0007404c2040c142c0180b44500810303c03030612501d42c00585030303086030407080001a00380c07940350980503591450021a81c3c03500c100c002d104030b07240b004100a4a0903201e44c80600080d1281c101c10365 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 682060638 1250 682059388 682059401
    0xe10050a0c1e12020f040e1303180f0302010e031c02070503070f0f06050c07180b03010c0c03021b36070c03020c0d0f02090405030316030b061218030d05071101 70
    0xc000580c940d02c9140f0b03400041c1e000785404c0c103014454929207aa1901030f07010a02089a08150b5520305038080c2c02495004882c014a401904250884450a04800030b0000100340406410440030001c07418458608000c15041105401495000159511070080d035429080c0103060280c02521000a0546603040181c4c00780c4548003604000e29042c0801250a600049504481031045030400a201492212400e4488043c1803011030b01d13a80342000d040c296400a5030500800090111643c0440e501041c80c0540e20700da40384200c0b5416040300041c1441003901005041e43d4143c0402680b0310310480040b0210590190003100700b50303280e403006e075002103a4400290160300f2040203c1d481c0d28103603600171002403146034018020784460300450710081044030210f4a6078000002d00c030000720144605100052180b0b801d00c11815010007003a070383d01440070308401c150181c0001c90b5404118083c488400c0354100704580d102c80858075080080d0006035034020120f442203104181006041c00342c070 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 682061888 1250 682060638 682060697
    0x403020306041e171305060903100209032e0c080c073e0109090b06040302040b060c060c040321050315061902070312110a03030e10050a0c 61
    0x80040355076684807001440120b0303c821021600903141000091402d525400c1c000300d9600c03120391a5a0303029000c5040e491940c01c02445010300340b1072103100740e40009514019620b42e2201684544011001c02d141c6840d080000e4140c0f0001e0420010342c01c0300403400c4901d111215424000c00c5544a002d4070070000c151454440744900b0041100030619401c41503105a404192070100750890b0816001c0c0380b5140030720f520009884515240c0305681c0030010350040e2242410030404030000c14009420b622452000030b0007640c0350940500c0d640d80f070b001a00c0c0d205010005841951402c0d522001981e03003e800308403400604017809038482054844806815a21900c4180c0303580c8480021403008554202c915038002010482c0c2c540d080d84030440c1c000350a80d1500100710031411841c00210800c41e0148540030443c1131a40d540c080c441c00a000c04804c2c0d0541400104804003070800e6041042110600320401d003404203000d07070b00320305911255101485950f214000912001c0510040d002e58120 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 682063138 1250 682061888 682061893
    0x302011a19060e0a09060b0912010608030d1e05100905130201080a0506030c100302270d2006030f0a14090325020d030e13021c02030c0c151b04030203 66
    0x240442e034000c2c00f0f408540c480c0141940212541e800c0080259451038200020059011440281c43d080c000340541001c04960000d01c0b840e4145080035607a030042009600b42c544d12014130f5010f0400c0200700380038070f04101d44144040e15000120743c0c0c9800444c8110406246001e000407803203852801d9818586605030341b403d4180c0c96103407601001e00b1001c1e144546c14007480741010306076654485044043c0c1590b45002d42c440c51258050080100781c035010104c190710a11061001395074000f11031610a60056600100306c42d0118003000f04000400c069400c032000100f80501d18008000491103000058014000407a154900d5488603005035601201c6a10501501c040035004a4400c0720ba112000914140905180c00107500b088044000b40c0200741021810030050a0840c2c403014a01c120440552800107500f001400d00c81460303000b0040e5a40c08004030750303000c454904845c12442a801240c0245000302d000c140c002030300f901c1081660f072540c09110816403418080d6000c40707070024007 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 682064388 1250 682063138 682063189
    0x2b0e0105040302090603160608071b080d0e120304150b01020a1a1302060f0304022704060c090512072615070c0c08010b1305220501060f030302011a 65
    0x34000c101c4c0b00a00040e506003e000200004440c1106210006000c190399615141c14800005403038041443d813148030b240e22822041000c1070315201140c0d50b0f40b01c01c1100140403550b1145190070116020740004141e180002170109012109500061440c422a01041824603110059a42d4480500000c206030550b441e0807a024504007d215484200c24080026080d9194000340e00d075032260501d901e80803808000d010030350500c03800303900b0390b0410f610415100c0740c1d00110000c103190005000404584c1c5514141a455128060001c010315001e081c86610104400006032200700034080ca0043e180c50301108160041c0c440861004d10b03840b08003901411904203a1500c000d04010b24010900c0800b070500d4002415190a6500400714070000154a1400d10200031042a089481c0b865240c200010f0011403034000030504800903a04440c2038036201d403440c0150240c541e96014584040076080c0000c14550103403c500300c180720341e0620340c00c100014801c000c00604d03d4600445041c079440d8 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 682065638 1250 682064388 682064393
    0x10206190b040c110114010513150308030901050f090c0d0201180b0412030806191e0305030a02010213080a0f121413050405071e050901112b0e01050403 67
    0x14544100034402550128400744000042001d8070404900c0400044844c05000309100c804c0c42281d03900040c0042800c45135152000255104811300700308030015075111440031000d507003100381600460b4450a01ca85a160840c0f82c00c1c02000200c030071309980012580007441148001c10249003000000b00404164202d50f00119039820344c45d440d429084501410200780c1d01c0c031140c090001021280300151a003441454010300919002d060180039a480c108000c04040000d4030312000e503260070241206581004490301e071070103101e0380082c00c540000030341c003200c0e2035064000f08818080c550405600c0d5981d442846c1e03496421002c058034421403000500001500c039001d1500000541c50058400400b05400341c40d20f41c0201c0d03101241452513401001310703040500030117a00009504103102219460850520250080500e000420000286c2500c4581c000c021003299031101c0d0303040350704c01c8a44070140e44110703003043c00d490700705154089864003183c40341c0044405e169069450601b800d1455 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 682066888 1250 682065638 682065661
    0x1e090f0403021f140103060903260c0c0319030203181f0b281518060e0d080d0e070b2b0f020a0f0806030307110913120207091a010206 59
    0xb4558145076945582030100c2c400880d000b000d000e1801f0b61000101d900c110315000d88400310103e000002460110000c1c00300c10090780840b948006645101d0755903403000a005c43c2188100c0c1600500840700314810381040e070b41507000e1841405400c0f82061041000f040341582d0749020000c6204144812414602419540e0056510300c900607041c0c07201c81090000108c0f40d80c44081c0390540001e0944800c201e00181003074611105041410100b165019101d82d5901c50480b50259030140401054140c7c190703107404800d04207142d00402d0450f1503054500c24440605200100301c1014400c4880204030094444d0849641c1c60840d940c4880f0780276148103810101c089031034034444031070b99142c0001c40d001d001d00041c4100c2d00540e4502e060316201c424090044680600002e02980c018060f0b1400071320043c1c0c80c0015840c003195044119034541e035441200d01c0b0980c400815112082a03c400c5443d0005641d005549100c1010b0041c40042c1072602c0c000083d028015006070302c054007007201196070 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 682068138 1250 682066888 682066933
    0x31002120a020c0c0607060e010c0804020f0d1127090d0c0f0813031203110c3a120f0b09160903060e0706030b0a06090e151e090f040302 60
    0x200d00351340100c60050300252241e04106010f4466948074003c100d4040d00038448e006850481d810700640030b040c82e07004100106107250340030740106120f2140c031050000c03d01c1c0002caa0180140101090707850300551501220080041d66402103c80010841103140850300c1d01916201e5900c0101043c5551621101c500d48030906540c6040100b00041001c03007015841c3c1e0285000f4103c4100c9901003800050403140c102004205131181804a0301c0f5040e40411190412110b0000c10110a008910280300580441d1a126880b01c010046050469040480e02e00000c0040d20204106800c005c542010745424040259002104400196820020354480341c0300c11b00900d407102d801d545a580d000c0480f18401704d0b02c0e0302d60344403c204200c502e903d40594038008030142c818054007490000c010f880200d240c0034003d03802c0d04541c0010441803410341e01c003c40c80e0004180f40c000504140c0d40240c0e404808441502404550340003800e81d07511304081c1402141c2c541d00801c21070840800c80543d0620 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 682069388 1250 682068138 682068157
    0x90114031e0c1b121903060b0a090305060a020f03070305070c1b1a07080307111f062c070f020106032103140f0c1c050a0b031002120a02 60
    0x65064a03103021081081c01034458000c00480e00e90300e812010702c40c10740c6001c408070000c0c10380c0800f66125401140c182515401c810003803030030080041c1c4440036800340030150400c00f094500070070010589540301480c4c0080300d00440c20380e5083d4403104295010381c4a2451061000202000405c41c454030941c021584810b0718900102444159550300804030f800805a002c04600000140201e164224110308035415581c0035628107104c4d41d41c3d424680c00000d00c4401800454034a2071407801c01809010350144000c000031071001f0012803904000c2442e4090b1407841c10b10420a241c03c0c142100800410500340383d4441c0140c5d54686084502c5a011000304086540798a000400500000150720484101c0941481010a00a0010103c4101c0d06800102e585c0003402d0221010a180c451900300100040d0150350b40d25442e04009000c800340500c5520928080410261034250792000e007401500b1025038241e9283d00c0c0f032000c2a8040c0000c82c0340d29551180109a000f4a203500404a00700d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 682070638 1250 682069388 682069411
    0x3070b13060f0c0323120a050405010513021813020a0303050a02011d030904270317130b070807090f0b0d0c030227030f0d0203120702070e010302010f0e10030e1209011403 75
    0xc0d0b040140d006e8418003643c010300c20548503024841046401e010f007903804042c2d58140803c0004c181c0014205a10140d0041e51211940c07001c20704041d02000b03960030058001e000b00fa001560b0f45001403070f036804461904015440c000c04890101820341c0740c00040f00e691001141044011030800008100d15401e60f0310124040d0b46142c1c0b0840c02500344403029001e07032222b081e2007205041c4002089401010294180004140107000071000090141c10042c0c80c40c18171110b944110742940c08904a410500c8010a0380c08001781c850f0207c4010012030044010038802c0e03101325007003a020fa00400100b0005c4046204a000e00c3c60385001d840d0f480341000030104c624060210038480c0c1420b03a0103035003e0050b04002152200351074040c180f690001c010f44011710340a0f142c4401014904018000241044620390590700c8440c865008030b82072010040050303d0304400c1c094058000d00c801520500380740500000c51003003500800560345540d0060715941d80c0d082d40e0584c0703182d07158402820740c4e11a0 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 682071888 1250 682070638 682070647
    0x3030909070f02011b0c0209060406080a17090a0f170a05060117150c0304020909060105060906071506081e070f2601020708070209090c010c080903070b13060f0c0323 73
    0x2804481c401701045d4846070203078417a60041c001c01480082030300780920308040007000048e500050700c52199401c1001d801e1106603d00b0079000d00cbc4202c4c4101e81d40302110403c0480c4e44001e103101081101c0300e9a0b00e10441c1141d1541c860740f29410f100c4083e000d1b40100c00100540c62501c040100441d404400b81c400300d050304e44184401e080b003074441d04547c5030007008000460400403a0141c04c450081300411340f075850a00054900c3c480c0c9464180501000f26601c010421116509440283c01401c240586900c030085142d540b2800384145c0c0a60b103441d40000c0c0e59007800b2403280199040458125000c6040091180a903100040d56100d04980e0002909a0260a01c00b0300f06a80c801c0000503500c40701d50040108004000d01444599003002004008c141e0700107000f4540940d02c2000c0c07944411000b03001904010b001c2d80000110000060440401c904444c400301c0ad485950301d0b071800c018098202180c508a0b145001070215450135142c960040c1e40803516941c0c1348040100a141 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 682073138 1250 682071888 682071911
    0x150302100e03030c01050901110c0a0206070201030e0d11160e270601080a030e0406051e030f120904060e010302010801060c06110d020a0f050306060d0902030703050105041a0603030909070f0201 85
    0x45502c4944c6400700b60b55244240b1880800038000d0050500c0011411800e1039800e044054641e00340480080c4104000900c207000c6900076008207004480300c000341c854111450002030700c1440c5594100069000d02010710030f541540c2c000c0002a10030360340c5814a00d03a01c0c500c0854016034194864a00c9545004103901c084e00c0400415029006000250000c42c0c030030b150203171400782c52000c01885681450b00510054840000c80c0d280881c880d030010541001d0b2a0100e4106030584603540080d015036150003120807001002020309d00001c1d642041201d9440d9410500c0a03801c1c04028000350a0100400c5801d108904100f001070165100180c00c10001d104142c003903010004030061281c0100d4444d10050704515803507042121814040d00c0c500d000ca001994900c90301207a9150190754520410964030200020000340d644000200414142404d2244500c40440c11102200c21103a0001e115400c001c429514440000752003021251034001c0159202c680401002d0110765943c803c6212 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 682074388 1250 682073138 682073143
    0x40e1f120f050c0d2306160503070c050118021906080402010503042f0103050a1103180712060203100801060812090d020901090203100e060d060513060204080102040f09150302100e03 80
    0x45c4220100d13005440720303a000c65071042000b034482e60070750440e100f0013408118005441841c0d013002d2a00d1952aa544a02522094210880130748158a030107002543c120403150b1903003009008441d0505109500300c0083d441500c54052a400a003224000c140154010750166030003d02c180400004615a0190140d02c4c3d100003d403803a00c800340d0310072841a96014071666410a4410405001c1580c0392454070384248005000394071411801c0d052103007041402d0041c0c0b0701a1030f01c5000203400038075504280c4040d42055a545d6200514810005034081c014451001201c0100000d0f082d0000a03412006154202c505000d030098500740e414001079484500c900d01070081c0342c1e401626400c0c00e1f2041c0c00d6903021500b24842c051042007c0c00b00c0d0380e442d0110345541e258040300114055a41c2c5000030300545240c0d5009164600100d40490b0f00c00040d006801610541c04038401c0896440341c0344815a000451a0702d8190411041031003d410405410110341a080c10507820030852440031a1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 682075638 1250 682074388 682074409
    0x60b3403050706050c07050c011b1b050a0e090d0302070606170609190b1f0b1b011503150b0307081006053120040e1f120f050c 56
    0xc00203a000100d0307800b004100d01ca0a40c0200c1029041800d05403141d4840e036643c19044241c5060142104950a2285100301c1d075002c0f071035100c003051100441d65014280561441e0142d10b200b4082d0100c0403c203d032400d00b14900c1603440c540146040c14204500790000d602010007626030549038400480c548100501d80a0307134468400041400d80780541c07855040c09041c901082e0000c01c407014000100e0100c0c410560040718000304801c225648900c026500e900c0d90384001c0d07441001007002469180d40800f0301d00300101d03402c001e12039220100256032180c00140001050a120034003142c021401541c010a5030781c2e406802c50700b031507486401c46843c4c40c601c184a0700707401c2d4a0740b90030b00c06070510a80e0312041082d440300110651603052440180344035040da01d00586561502c2803491111784401c1c0c1d80c01407514502155981e9180c02126a06403402c41d070070301003145944c08803001c9113a15200383d411a81c10420640e810641035880140075048060255030510400c0c0d01113103165281c0700c540 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 682076888 1250 682075638 682075643
    0x301060c0c030602041401080c190e1c08030f1b030112141e0c04090317070224040b061e060f0d060828050d0f0512090102040f09060b34 60
    0x600a00c0000070004089030783c0100103a102c9d64080c003030414118031108010700c88000e241480940400c3c42da02048030010094401000e10348412000c0b001e1000d4940114040c50280110b0241c540d07801080030786204548650843c4880c0c00c20040015641800e01e80c0e00c0c0a108883c20641030280842040c941140044210010051001d0300d15640b03c040154000084007134906101c0e81c04140c9001e02190405c950090701c060360a00003800c200e1003070244810343c4491980d03545840300d0504601d9070080c2c04890882d103101c8420041100b5103440300d103244110b1030700400041e40204540c04e00001350040c145007240d40005001141580205001c0c000c0034000020040031000c142840d141840022280c04040c8014100748002c045000440c89810701102c900b08819070440420088900d1700c906007100e00d40000000c180805107a064000b030007241c80069460200c95240d412001c2203405a03c55040004000c002c0d400d140c504000d0324600c4030b202c2611b1018641652803c840b600d00b00030404 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 682078138 1250 682076888 682076909
    0x6011202120f060717010513090c03050109110a091503080c1609020a02250506310602070803161b0807080109030912080306010e04020c0709050103020a090903050301060c0c03060204 80
    0x100065958000d0001012600302175804645501d0400410102040b0600b00003689455245100600c180c07800720500440c3d02000800040342c45081c000720901e0b81608861040c0161000043d1010b001d005109840e00c292000d10820b034a1952040c24039030040d400b5003d20b000b1141903954100041e52048000c1004100140c0d84102c5044000c1c102003080c0c400ca26503428842c0b0401a14190104050603110180d804a5454500140400401d01490f00c1c0e080d150804070440148101d400120608860190702210030498981b040f150b20b0f40a0070980c0d00e40740d94000d102d0400f02e1540790401d2481012601c25a0080380c840400310b040c9201d5400600d01030b034407414040201680003411034010110b40203140d1542c1551742e141912440043c080d181004421130070303c440c540e1654126005549c081c0704581c40c1d90b1755030441401600c82440140e20a81590303900043c01c1d0818081d8210f200c1d459078901c0d1441c1c3c200101038a900c941418240d0f00a00300110200024000348020006403503240b04 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 682079388 1250 682078138 682078141
    0x1c0521030405061803070f060204032427020d0c0f0b19020606130506180a0614041503030c0f0c0612052503022503030b030d0e0306011202120f06 64
    0x1c0c00c51400c2e81c05002440301503502504403220701130100a885115610120544442e0414205000607020300d0304040c00d0130f0040002500002501c5189000541c000807050141c0d503425444a03d95856a200100002607100b45181c01840c201c0c40514805100c0d81c02c03007514a8a500c003148581c00c0d242c201c1802c50400084103880c034020312059440f001c46910007040146402c0f0f001c250445031001041c1c009903120030205100d991521841f8424a04e0252116054a0030000f180040c1c18070b4030840d04541e40380401030520b401e0a000d402c00035000c41a401c04e840d45140e400300d0381c6208007241590403240c0034581d040050040580e0400030845036a0700d520030490181c503c0300f2204007500842490010040720000a594810307086040401c1e03081c01070310f0b40035030031003d0903a110003040d003244011420240003c06426070b001a107401025000c035040d882000340191144600c1d2060aa81913002600401c881d4820081282455102602c0c02c00e080702c40c146000e1030003910300d6074000d00ea00503c0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 682080638 1250 682079388 682079393
    0xb0d050402031e0c0105030a1e0f0c051201050910080109030e01080105180c0f0906070f030f0903110d0f021806090a09150e030403020607060618050103021c05210304 73
    0x80103806100b08420b03900c2c602010b2085540d0342290036910303814042d020001810500d130302e500c2700341160202e00310821000440c0820100508805c2c1d400c2c07120924210440220381d00c40c0050b500c1c55048210300310400e9080108100485500601e02100040f842c40040b400070300030b00400d002c19100b61580c2d10144040c0002408080d0140c100c503000301c03034100400c01d00e041e41d00d1185400c10f41014180c0c7e5038060392402c51909205a82e112a00101300080c910204000002c4445441d80650b64a503040c00c0059004c0f58219070600c0094000813040301c1c8025240340010400000d140308182c00f04111800d03a0208086420000c04000303009411020021182000603030030b940044414000c1054902da542c903814507000c51032006014075618440088058020400c41c0c020715001000c090301c40c50280342031405040c0c240540c0c800541b2a880909800c6010b010b02c0e4180c80e07000b045940701c913100204031443d11440510a460500c80c54034241041c26104568503240981042c8060740c81c07400c4d0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 682081888 1250 682080638 682080643
    0xf020301200d05011502151f030c08070506090a03120e18090606090702030414061b06070315120f020f1504060e030a0c031b08010513020111010b060f090301060b0d05040203 76
    0x164442040c00d50a005d40351000f90740440c488060f510890b40304800d41e2030701c904428030441000f809150802d218040801404540c030070610480361403200321070140351034070244030484c014400c0c0300382c124010380780030b0002542d040d0048089840a2405024890310b0030009800d042e001e00c1c60125800004081c0409000d05000e01030f84004165229600c90500f0781009540348524402c49024690305d54010409550303001c2151107014101107660340000c501402d01d51622015070f00ca0010a10348142c6000c541c2142015000f1655001d014151082440c4c4845440903c1c41004aa00c484103810001c401d91701c0c084044a116800c3c65201e8440e81400406070081200d921454469808003500000040d1a42c14080c02c0c5c0b0b40c8084000a0389441c00c0d01c03242c0c03500154000b1000e55080c90100300d00e02e85041008841c05000f6a51700d081c020020002c0b9003200d11207a070117070308000304001c880c01886401b0024502c42001a00000345a503441c0b0810303209400c10685c1c6d84e902a140c400344800d61508 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 682083138 1250 682081888 682081891
    0x51203160e0103060609120614100f06020d20011b020c01140301032105192d020d03050709050909060411030d1704031e1809020f070f020301200d05 65
    0x7803c040240b141002000b40c2018124850321080c0f0031858002c404000c55a0844000d400c03a40f02d2a40e01401c0c00700001d1040c1c03840e4040c54054242280002030072600c00a41c1318418031898591034441c8c60301501c0c20a8046803e2921105903484140f00803200848614100002c44198003414004401c240014250340c0d894185680d07940307061005001280e0504840152449030413511360b410080640d00342c4e00380c01014004801d07554001c5411000079009112011084c80a21410342000410892403002440358007120300181e1103105031042d002e0090780080e03045041820003410803544d07880041c0007000c040300c00029a03042442800200198100c035110210740460180c841094801d9008203451a00007801030149070f210042820326000e05005c6a42119000c0380c144a81c0c100c00c0098890090124004401c030f541050001b2820740c0c910907a8402c50388000c4d010300d42000ca407100645540e002c1410303a40341d5600d042030211a888440030501e05c404540b442d41d01c0d142c900707008a0403200c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 682084388 1250 682083138 682083167
    0x3081504110405040906090f08070507090c08042406170105010909021804020f040203070201090308070e01020a2303032505090f130f020c1506030c030d0c05120316 72
    0x41048981d0308052240641c0d0079603009890002d101ca4950501c04091f000010002e002509225261018445200c004010b0740b030082d000c85008554a080003002c03641c08070102c000145400b0042400036203951142a622441c030903110b078990308030b14407200464001d0f60280310200c0d08a1350380c9030461000e008060040c410030b4001c00c5055180d40200304080720070b080303644d0080c800000080440d40c1e00e000500d405400030308115240d01d030445020303008105691007a0049621500003404051260080149880040e4040e0031036001075514040b0360061690035420500403100543c0c40300c5d9080026520030000075002d10900020341d401000203505a0302e0010410030300b000004440d441310400030103004815114919032b808404088001042c1580d10b800c20f4900010f92280140030009803c1c0072403100f2202c8043c0c607240c15040503500c0804a0746070740c05410a030071114a550081d20241c0300c0a00800075650800521040d801e2180c0c030443c0c0c09440d0350080d03c100700700380742e2140000340442c2 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 682085638 1250 682084388 682084391
    0x90509070503120a0e0d030c230a0f3f0c080a2028080c1b010e240304030c050a0f12020f0a1b030209040c150c21030e0a03081504 57
    0x146d47c80040c0508440700000c4d0208240c840352241208051100d6500920050107544035551189003082d041d10314548140c07a0325812a0001ca0060189401950200d000e100e016040700400101c0100034908100108144211a030441012038079a80083c8900c00b43c66440124294a0f10b41d0300c5915505034200b2400e41d840346103200d0000310200008280c0502010f01d100c400c02d0185420150b910030a610403016019002d0018a0084105240318802d002600d0b10048502c1032000d101810030b4203800010042110b1044400d0104000d0003541c1142c040d180018000c41c040d280c452a200d16010229856075406444000384006140310503089250740c40581101d480000660b5541d03030510401030415680c0c050400d03031944040e40e0040007954054005003d9150500b04082c030443c6c2c610030441c441d0800e81d401400c683c0700e0203041c00003d511a20442c1020001540c0d101c001d140701ca0390000b45a615000350203440001c101e2800907a21a5442119503d0700c000e00140c3c2c1204400c0d00c0f401903 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 682086888 1250 682085638 682085659
    0x50706020d0f18050d0b07030b1008012310080103110609030c131e0f0c05040b030103080d06050405040f02010207090b060715060b07050a05010c05030c04090509070503120a0e 77
    0x200d90102d4103442e030a00e58a008800d650305031401c150380b6141a4065030f8040d0300321144408101ca5104558030912140d14100407440188051081103070023014003000040d1070b2070043c03081103841e140e0080c090504102485044a030384001c070310386141e045110800702d00c0b81401041003109181d8400f02055064643e2401d0990032001f1903683c052007942688100002d80c2c1c44560740300742d5031011222084074010008282c80448105005105210444550b942000305040e0058001d07001c40d000c6aa030341010342c0c0f4503881c50302c0f0300302c0581101c44006101e0f031f220480043c2980c1d40d802294041d0340180d84103180d0180034400a460521640d008200b21410032010400c4c40e41c40b801510030382600154003513480910b0503882c500500c840e41203001c11400104d420410301000096004082c1d00c01c10080056802d0070320251440d0000300c40d000942c500801c018440702045400568204003d0000ca4021540b83d0b0002404c2100214020581c030700040350b1101c10750382c0325900981030402541d0340a01c8 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 682088138 1250 682086888 682086913
    0xa1107090c23181c050106060c030206010806070504060f050705340501051c0b03160509010f0f0b0714060c0d0b0a03020303030f0601140c0714120d11071a0705070602 73
    0x41910080301c040c840c948030468101130043e0061600700781c0d98050003c104076a22154040d0619640e40700950062003068008145507100084d00f0b40500700760b40301c20b030509103030490071030340d101340e8030858010010140501d0002070010001c003051003030040014450280032a02c0c00c40c01d80300c13541c0024990f50100b0420000307a6003020454080707098a050000c000302c5480f151002400c080b0b80b08682510400003d08050000e016800042e208200c480341101e903a146400c01003c206030161010780160b002c010001f00c0c090324020315000c0d100341944c2059188084c406030400008030340c0c1c05c6071a080041d0140304c3c4400c52050400c12003003120303044151802c54002c42d5480c04000c101105e103405c0c650224869a004020a5641c04481c50710355684106810340030781c41e0b0300300c2c0c8200010b980710415400a1842c0002e000180c4050040003401c800e000a041200d980c07403052030444481c00b03282d002280c02601403042080c0ba141c3c0400c0c00355907044501d050352a184450f40708904540211240c3c1c0b66 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 682089388 1250 682088138 682088167
    0xa05010501111c2003070b09060f0412051c0e0a031b05060c090609030a080d0f0b06120a0605040f140703061a030924060102150c0a1107090c23 63
    0x2018401d191200d50132014000b00c0c0c8880e080401e82c0c0c215444007103100380070001047e081e035202d03c021406990490300c4220780c1082200098a0041c000403501c2d141c0b001d901e2080c000360004001d80d4118400c1091000b00080c1212401e0498614542001c5240c0d414036403c0031f001d4080003c001035208104401c2e40316070303488680140056070705c0701c0c0010346c8031401d030340d14000e641c1102c1d4001c2c16180d9a011915003c641580518401c0781c8042c180205540d1420310361244c01380700078002e40400d182c4401c494900c14008002880c018040d507403844042140d803114414480140103801000a1440748206100c0040600401900401d0b04001c424401d104c80d45c80c01101c0e50a042d80320a0710b0b526008001414420450400065104c4c04001421050032490303000b40241030a03001d4490001c1000e624030010030085641081c030039400c008103003c0d9441038081080340720b48281034843d2503480d400700a080e076000b18000c00c0000c2d4a081e0042c00d44900284040041094490b03861900c8031001d030185 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 682090638 1250 682089388 682089433
    0x1020c010207061709010e120d050c0f0d2c2104060e060c0106030204150e06090103050d0e010c080703050703140403050c06030c0d1b02010b0103181e0b0a0501050111 73
    0xc800314613000c0403842d03196094000f50b98811514003aa114000d60b8050000550030142d400e080c8681854040303054100351000716122a920000020b1601d03070926596009000303d01070328461421300d04928100040d1034155440390009c0310003e4001d5066042c5034440d1348640306a11611404100000c003c401e800c5a80000100410f4403010b4503281d544005d2401000b02c0d07400690054101312038105004007800320401601c507c030062010325200e40c002e10003c074809010040c11940180d000e54881c40c003d04521a202c2014900124060100d55801c415600000012070100f10701181c00010035800070f1140c0450340c80d15003070904140c07035910b4055031074811410050141d24000082120026103008684640c4600c5005009402a44c8220070300502c107425050015440e0011505e15984203020f25091900c1c642682440f0b101c2d10348078030b48103501405400561004c0400d00c4400140c4500d21140f00e0000e102000800b9890038001425224180e00081ca4a81210012144a10201c8400b0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 682091888 1250 682090638 682090667
    0xd081303080402031609061802090a03080c0f0a06020a081b030c0721120b0d080702060d1d03030703050f16110f07091505040506180c070204050a0b01020c01020706 72
    0x1e544984560001c41c0c14500f4018040380407a0703030001c0100d49241c642d00094100d401c2085410410307101840c460013207014407100c40380d00c0000c4840400100700f403500900801c0d11084203032a101c00703100b080c1520b0f0100b031100450b020354012803042140c0360000441540000c3d0002d8504074181504a00d0700301d440010580654150b0120720748040c4214281004002502ca400c4000f42c1840e004010300070004c82500655618181401c6003007504000441c0742d8040da01803a0700e418120141c0c01c00c40590004a03000801c2c03561480444209815044104903c204003800381d0768034101010020706482008080088000c070720760600190f0083e030b042c20f41d076414151405000919480301501d05180c07050003203d0403845294008241d0b001c05600c01007a00c1e101055182805548005010980340f0444210340e010138415030202001d414484034a6003c8144500036162080c1c0d0741c00102183c0085d0381c1c401d44541c0c0c1c1e500c80899541c042048001e40c9602b40001c1121619040b8000c04045448415 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 682093138 1250 682091888 682091897
    0x509070b0a03021908101535010303080108120403030e06090a0e0a0e0f21030903090d0602030402040b041407031508010e010b01020d030204061d0d0204060305010209030d081303 78
    0x1c100c01500c0b81e81552200c3d00c11500352400c10a0030480144803900580f070f40180850f120714001000462106840c04003003030303900c802c3e07001c41c1451600001405000b4000420054450401b4044107065102c0b602070b52080d110745441d0750401c06d00d140303404048050018205c20400003440030070f40180704a6941c460440f5031070382d940b600d04042055449954404551244808140203034528039802244102e00356408451000d0444008242c0e1074000400c21010700c40d50b00300d40041c0c2ca40880046030b1101e480400ca9152034401c03000302d60306040c08841a80c12581c04402d0004500c3d05001b032010702c580031201882211590720707105990300c2c805001da0301030603507a811205101000d841e4100c014070501000b00443e07051012101d000c0d000b4289503500500841c001d962000e030003032003070b0740642d0b000c0c0e07039a2483c030fa04150342100c03084004140e0070780c000301d031240c0c200c016511400b034400034511900c000341e147c03038042c028513141a84444850050040540030049043c1220320404504ca405141 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 682094388 1250 682093138 682093147
    0x3060904020d0203122d0a050a022b090522051806100f0807060525050f0d0f09050306040605040f020d030305070212190305100503011a090a0509070b 66
    0x180d0000304108004c0d0540070312204100c00f0301e00e0501070000c0a0b4251a4481400818442c3d02c0848540c0c100c021648102070184281c6d05100302c000d407c1219950044601501d0404d40c510364038642c90550701d1640601e040610b0b921a8008503560050500360f40001101202d155040b22601d0590340700c806840e610000101c04030040c00c8500d01d900c1ca1401a2000c50501c030025101c0310610340240110302680100019029400142c10412100b2507502d140c10020817031103504101119021a50085291000d400b0200f0b005000b0300707040c10f80800041c0090504418060015040f01d01050288010b0b4030702040359440101e15954019400301d0002660f940b0f6146c044e40d8000c00202c0690417501d010700c043c080580581c00140900c6c025001c5810040304046880614828043c1c0c92802e100c400b9401c0c01040c1c001c4d0402e513080b00d00b06040d038107074689a03070203e4215401241d0242c0c01014000c01c0c85030600300240200e420460b103031001c0c046880c0a0b20029a103081318800d14001100c0001c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 682095638 1250 682094388 682094393
    0x203480409050c0d0c15020f0d03050603071809050f0d050a0503090a06050c0c071e03140c040c030212060d020604061409041e051003120c0c0e0916060206090303060904 74
    0x1c0c4000110000c084c42d0240280c0d0601012040b214090814101c1012070070134800340c0002100800036001c44020261200c842104030007601d009002d56400d885a15401300d00c4922080e4020302c040340207000001d0308100c0e804c102d071900c55680341168140d00850780c240020f030390000854202c2c11040c00c0c1580c0d2601c4283d10700f4a00b00407080094030701450714051060340500c400040001c030031500100c0c0e0441c0c2d2039802400e0180196950300088450400341000020249403078284482c0d941c2e415070f21001400d4011400f5105020030b54400039500140c005482e4244009141c1c21a40c00c0d225002507100e0303076022501c1440b4501900007844091214a1400341c00d07103040700c0c082c5001520a1001e8200303940107100000000c500d0700c80f440e050000203022a00300f920ba22040300d0304010003600000d40c0e00015100c0c4e040b05401a1800e0800403000308002c20035002042c050304445c4001c0000c0d035400c200c0030001080b950400c004540100003840103286d0000156074101d14100d55071811503c807403 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 682096888 1250 682095638 682095643
    0x50607080906030903041d2802160b07032004140a0f06030b10080402130b010e092d090607050315040f06030c0807050108040b13020348040905 63
    0x1032401d158000d0001080091002020015001312101e21101c0c0140e101c9504603050100800c43d144482ca0310041c50031001c410030070400e6052000141c00040c50700e03062060b5100075140312041580c00010741c5061000c0b26516100781c0d04000360030000d1442c107071000340b1450710354400c03445a03003aa20020707184001d060780c4110351240200340d4940000306465075401c025000e0000800e42038400c2c0e00a0165091503409000400e1091f540100300c4c6084e001c0e10b1750104020482500f50b141004484035000140c2d464541009019401d102141711201018100400b24000d810240e940c2c605001424006420030001d5950780224450030a80d0f2130f540c43c82d000c801410100308401e54030034109925a17081d086242e0110342600d0140d07a4000105407200c902c41e82d17401e224031411340001c2602c0b00150104200000301c5da0070201200504c8090306d00c0b600000c1c40c1462144943d001800b814464a54815551a46411011030f1610501000302e441c501c5c410050210703204903000e103403076021301c3e1308100b000d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 682098138 1250 682096888 682096897
    0x3060510020f10020403020d0b040c0f030f060c0309051903050706021809090c0d06050c09090c0a0806030105060a06260907260705210a0312050a0b030705060708 71
    0x680811010851094002c0da51a02c00a010309036000305a64400305a1607402140c0a880d000391281c0c01c41802c660300c1643d10000100107450f0f0081c10800803820b82c4c58101d21100440c00390800e550407401071308241c0304481080c11a40281460000c2440000314041110400403010094801d020103103410117a545104000004200e10b10000e100c411090350300e1602030b4513a400b5206043d039542c0380041e0680d0344104940c1a03500110040c01000000c000f90030080d4003401c0740d5021400c003086c1c040414040842a104e00c1014040415002403160340710a000d40c0c4504220b00a210600b0000301280210700c0d90300458040094510040c5401c0e8413501c0c00b61441c1854504804040c40d1000c011742d210120303030151b02c2e8049926940c1c40015101000c1d6200b41000f10390140640b0b41c03901041052030014011348000c17141c0c2030103006c0302c43d070030900503007082d1400380d1208441c1d000120440c008544008005003070151074101107141903180002d041040c5e50b819200c045d95a5014107050849019 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 682099388 1250 682098138 682098149
    0x1e07050708030a05040e0f1b0f09130b010f05030c03060607110d0c080f0f0c22092009100608130b010308070b01240f0c060c1107090b01050f0a0306 65
    0x15840300d1890784400140220b032540780e011801907e0302c02c01c1e84c1d0100320940d444190301803480007903400c1d280410020321030048507201c020715215080c000306149401c00a0104495560f03501050001e503007145014107010024500340b45580f03090203500425000103080b850165102003070f014100018001d00c80f40e6100020a80071035a40b103031a2107541402c00d07014081240c005d04010702112400040c0716440c1e0b20204003c1c003504e803881010700000290170386c0201004240b01014495005261080800550080c03541e4014000c5a42020120180c801c00c058055030101d010803450440d40030507003003654080d02d0032034102d4491050390380c50710746030762006051140313070354000420002424020000188100d0350102c640e0381e1500c58052680b0035000701d508415003e9106203010340b1503c01541280010304154910504540700c4004480440d000031010a80c15511a8800341080190f0f170010311050f01e00303100f8945504002801030285c0e01840b0b0410f2801f0518a00c0c035402504140040d16 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 682100638 1250 682099388 682099393
    0x30b0d0507030c06020a0b0a15050d03022b050a140c030c07080d0e15030408070b0106030b030c030706050904090203030910020d080907031a0a14130c05061e07050708 73
    0x546900300540c5801840c40100c603603c2d020321000844500119011a1403500842e000005d56903070b444942c06440c00004d00c0212151000c0040350a903a004d54840110307020354000d084070142c81c45880090192587c440c01c01002c8250401601c651007008c4400d801080c0c5045440700320142c60701e00c42402240e8100741e840c0000b16003504082800940d41003114911000ca600e002500c080a41b910072400e0103071030300a80311250000c01c442c075220080d6040b0f485140c1080c5401c0503501d42208069082c1c00450000346c540106540c5441c04106001c0100d404030040c2407014900000600640309103045503000310317111018501503690500c25a010040d001c1e2594101d102e000034002e448180f00d60620000c9050100444c100d81c00019984050740c0c1d000c00208482a078260300514491030003081165200d4484103000725003545448024060107844107811844843ca1501500c0d8201a8000301c1c001c040521801c0080510000c0030401d403070b0b2204103a0350f24105c6060090030880d19402c0b419552 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 682101888 1250 682100638 682100659
    0xc0a0501110901080a0e15150307060305180f1009170f07031106040314161b0602100e06070f05131404060e090a0201032f0301030308010e010605041401030b 69
    0x301c0590028001d40750240c0e620400c85d52109424002c54800d421841002e03032060f5810014000008111500414581d80ea000c615200a002034685102908075000113a103c0080c000c9203441e400c1c0b08208400c0304070150005000001c0415501c0140900c00001143c840082400303000704204032a41201d41c01141d20303039800c03610748601001d1b0f10980c001c40008040b03920b0100b6465000c104a80034690540d10b84142d81500160503045411049680c00e00072420200352000030b0942c0364100e044007104051521052505101900308100081c910340041c0c01d00740d4120100e00e0110301c4a074808094200002c0213248001c040f27500d802000071141c400784e02d003070740859540001f000343c58024004540078003c2c0354540022142c5a03030240d41040c13050b4440400580150f010390400e40010f08660042c0b00d05400d002021a001c042940d904600048000010300525502204a50141c02111080c5609524005e4014074a116601c203a81d030403021101008103a030322941040501c0d190092280e541e1 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 682103138 1250 682101888 682101911
    0xe09040c0618030f03050d060504020d0603020f030321100e07090812070b041401180b0f010f1d07091511070f050f040203060f031501030c0f0f03080c0a0501 69
    0x10400c24050500410003124001c0c0000540072046800c3c1c80d404010851140941d45d0181c40e503811010001c80e60a03111603011a41303845a1002d45038070040c00202041803031450060017601e18003d0703404d40c0290010003c0e1580c4a4940714900030142c3c12941640c0556903420b00410301001d0f075080000404200c0c010702020f203a005486005070f0705481c090791030803100300740480341c00d02c0381d100000c00300f80c030342400513021541d52004c0740b07842c421000021407440348014130301220850b0366100322007050144007800440141804141d0150100601f060111400c0000b40000c0340d840e02070010880d003540000500740d52180c00301301d0080004039000d0040410409001c2d02c1602e070304603501101e208090b400114242c410145808589014100700000e400c040280406544014000f03070f0040b490f40022500b54508202880c4443c01c000350300a450b50540c03805019000c0258082c90303100e40624004e104440351294170b802241d90020145a8429131170a10310308000c100c0030003820a51034040701c08503 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 682104388 1250 682103138 682103153
    0xf020f1c02191b062c010207030801050f1807090e0f01120b0c1e070605150a090c0201090f03030501030b070e0f09070e090403080702010f02041409040201050d0e010903080112030e100e0904 83
    0x212207070b05c0f40c0010103550701c00d03031014202d0043c6a405000100d468004121034100700d9028070403d100542200840512a60908030200e0243c40c443c00051007030004110701e2042d0724210b604109008101c8006500d00f0540c540100c1d12a8400b40070706420300041000c90a0344e1003124081c445140080403c607045400c80149070700601300035030f4181e0420002440e007180402078048020402041c02542e2420410075400514502e00d0100566580340c8890021601c0c08400c50f030741d9482503030003290707542c103500d0002503001c00a440b01003070004107183c045180c1e4601c142085000010341c0c124015503141c1d18101c50509131240b0081d00089460103201c01e0640c45040b680c454841e0303400038000303100400f008804034400d501c916031110410414041d024a40200a5900039005252282c20441c0c240c82c44821140540718440090b0741d00ca84000070103400c000031342c0c0182440751510030528480e440103007a21002010710362051032444568801103002c0d0800210014000e40380c81a2454503151840 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 682105638 1250 682104388 682104431
    0x110109090911041109010c0b0604020d110d060806040b15150a030e1b01050403081b06011401020d030203060913080d090f060e06090a06020c010f020f1c02191b06 71
    0x24022410100308138825400b00c803c8841d0380406039201942d00384c1075180c1d00a8944081c0c201c9038400e408110340306e00c03194a80201500030400014440e611014030010740100d5810b5403018030286c1140c01040003203080032241c940c2c050a401d007600724640c2e522002072050f1040596100e4103400108807480f10740c2e4950f01c840c00360380d04207040f03410403039161000c40d910840980d0840d00044040000303000044207513010340071780c2040010644400400107403060501200b60011380c200540411203d24640e4100301040d0021042d060442c0b45d8205007001c0303001554010940456484440000c508001a01c3c0403100003030700e0365004001c1c130412840c1c202d11034110100d042e5461400c3c10a008480c0700c001c500c8500070051400184480c40c1c06564100183d0000060140c040d5030300d09403401011618001040700d4500445101c0c0d484542c15849480448140f051281162041c8910344c800d0701e18084403041000182403043d6104500010b568114002501c010807460511b030030303022201c401c030b100351 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 682106888 1250 682105638 682105673
    0x6061b05190524060f12241b0414010507050c0a0902070501110a05031f030b0c030a1b0f0c0f06090503190c03020703020103180b04051c09030209041101090909 70
    0x141d02046002d070700b65010f0b802c2665440d80c01100c0c141140d0491a002c0c1240d14a10403034810b94401262203800107a42000914a10b1081141102080208040092150286420b58810508090410010a80d031000380c0940358140304c0000b8166081c00b50820404504050080140201c65200c0491074060b4201c508122050345c00c19401030b0b40c0d00900c500340c440c04c4003217549071800d5036603d040c5039060800c151240c81c80281031140100c0884c503200b602c01d1292102c40302e0302e650307810003010407030444424807003403400603203076800a0095550144c0c200200c0300309490816440e0030706003000b841403202c03075000030001440c2c0240541000701c0031014281358003c0486030105501401e4056524400c03042c070060040e0021002400158003a62204410076686e003980d1080000340d0b41d400d60010f100355801d403401d034404001c56181ca0000001c100c045481440c110180c2807440c3d0218480c81000f030310003481104402c0d1026450391042c1c0200c8002c00c0c206101b070001800c5c03414041200920391811 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 682108138 1250 682106888 682106923
    0xf04050f01290a0b03041e0503030c07210e0909010b1c021002151b0403080a020f0c0303040e0103170918010807170a0f021302040303110601080106061b051905 70
    0x5540745071401d03d021000b12a800140b0300d181d503480e956200d806213441084409081c00c1c807044e00c0003003002000558400c1c0e44241c0780c15650341d8241088800c441c1c1111007040810440200e4110b072071b40c03103201c20401480070340b0007054589a480c41d59001d04203005016401c40284080e42403003503640c09000c407180e40292110380d080003020710100d8954403240e85619030070b015040131450820104100785455000383e00d0303583c245900c950380c030392855014820000050b8040d01503080008014003080c15251402c400a601d85441d0100b04205203005100c043e00b190481941d42c14102d6010003210741c24a0020711032041005140c00229800c4028010358116115104010813040c0c500e1a081d001c50101000030610002c1a580304c080301e050b4800d040781c100f10721842c010311a02080c005400a10702c2900c8146900c58030310012450610140c0c00505036030f041ca02c0810a01c0d810504441403488001044181c5803040d00b040da1501800a19a449203d032503090b05081c0100400c056200c403075001d61 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 682109388 1250 682108138 682108211
    0xe06312c0f0106020d0f020a12080f15030c0d06060803040312030e121204020a05060c0d17040b22020303030a0f0c090e0a18020a0602030703260f04050f01 68
    0x20000c8800d03109001d403001617031001e1400030880340a02e0321a552014144121081024a41e07200504500c41d10b09040110382018148486034800008040c0e000c90b4076010340c1201448080040e41d2844190a124001c000c1c040c60030062003c03d42145c1c0282c04000300300c9a8880c0d0300e1507c011000d40300d5000f42c000a180000c580348138a000304042c003480501010b19403d000442101d1000020003070012a4040c1020200083c1d079207448001d0801400301c2c4016241c60510640050070510744400000c2509420704100702c000f6540d4503090f0742008425205848034000b00c05102414003c80d8170207581407201104001c0c003040c968201c00d500390442001404903294805066400c51018000c03000041c84050024440910544c0800101115414280071000c5540c01042d0300c03400c339800610040c0c00019402d070074160801c910404210815028501140c05240340060f00a80034142f206d1092542d0301180600c90200041004415604003c2003048170084081c0c3c0700810100c14506a002c1c80071 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 682110638 1250 682109388 682109401
    0x30f020c0d08060907020706050a0f03021902031b19080703020f030309061b030601140a120207080307030c090803030402090717070e0f1012110f13060e06312c 70
    0x91000c200e42c02038482d282010300204003a0b41d450f0310bd25801e81016130912103000c0102688004102062203a0051039840a402001000758940c48000c41c0c0207030f000da00911408001f1040c0d280940f5049100261035000c649030032801c00321741030b45400f164840841030140016000c0b07400d500904024060304401d115510105580d4041140c21501243c280503845594401400c000c260028040c903000070303900c00c01e2280408036002560706949142c004000c00880c15098422030388140c00d981410a4000c0c50200d00303075540d110050000b8020a40c65002c10078041c0a4017010202e919044440c1e1441d10780004010000c0b1607090200b4440c5442107001c20241c18014040940c3c0c040d07070381e5000460b01d44100010023030241212030304148002000140031a00094010740109440d4086281446107001401000e14205040d018850304081080840000c0300300101c540c000d01c1940201e9064508000c0f81042c5005d039400072f40c007000710210050034240000383c0401001c01c04210302c1d2541d00c619 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 682111888 1250 682110638 682110643
    0x30d030c02030304060518070324090c17031318050106030203150d080d0c18081203160e1903020310060812130b040603060302040c080c0a030f020c0d0806090702 71
    0x1642400c000d80c00400c0490042a09500440d40c003c058803440b22090400c1d200f2035143c80c03490361042d6240318280707030018562110014403040c0c880e8407070018400080144c68040c81c40d109031040001000369242094104401441650445100240d1404409645400481c540301d03040e80d031002068074040c00840c505001e48242ca0244110024003200c100c50101803195010a0303190948581109201c900c0151241c0e014000041c1e41e147d4814180d80c4041014007103084c400c0d0018036070f5400c4491000c56403042c40d41981c0c1c0c003a803014044180c6000074001928401034400d500b942020111541d0502c40600e0041c0381c0840b4401d4007118004034900454004951960189610780d03046011104000c3c1c441101928402610800c4c4000d8070b9030341c2407001c5007580705a12582c042a00c1e0311041040d80ba143c42400110b820380d0406101ca0301d050042046540f1800615105159590380003107102081a8185c528101c441003c64043e05100900034000000860b00c039481901c0042c00100f60a201 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 682113138 1250 682111888 682111901
    0xc020123160207080d0e010822060b19060305011a03090c042d0501170a03021c030605031002090a08030a08040f0206070204051f0603021317010e070f05030d03 70
    0x122003000350305840e0000240003425586141c0c0702144516640841c0c204414001c94114030b0090715840c006050072400034141050041542040301043c1d40403c44500b020406181c0c0a64040030003d0041101c030002024880e40341001d0f08020300300900031034060b8041d03100309d058511404400c52120710411031000c851100f260a440b4a8004c1d007883d40c20350130035070400006000b12040e41200c1612031082c01907071003500d001c6500302a0701c40c0010040c064034611490140341c42c0c1c0001d800c0340d44054901a68855040302d0490b40c40c903000c0d14941d4154420340c0040702901c402400e440300302c4a0a0056000783d001044004c0c07141c00e24200c00141180300100315414810315840312480c2c0c0e5a1510781c5003030400e1080f802c3c0d0300f040c01003016000603a51480b031148202c02d2000d0480c62000203100380e41c40c0381c08540042c0d040c1407040110b2041c00c6d80e0120700790202d9081400c551869440304110074050904015001d280d88100340000c1414441c00340c0b01d60075910180c0032581c8040300140110140c2c1c20 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 682114388 1250 682113138 682113191
    0x6030807030f031d030f0d061802130905090309010815030f0c030601050a06020a060506130507020303090606060a1706030f120406020f031c02030907030b0c12090a020a0b1c0606030c0201 82
    0x4200c0507400544130000f50042d11000a8005402036484c100780c4034450b40327881e142003039039400903801c5145003001c1a00380140c4070582c0c04110038644504070382c0e80c1e8829144400c0c1030007100d0780060700391504064066500c240143c01d5070b03030322014080070315a106900e020880c400e0180100128050901800c1c03d011194658000c0120040c162140d1000b040080d140d00d403c0403414605002d070304d0507802014003c2045900030f6a8a18109001c80d0030184080c102504c82c0108004000d00b00b68400d0100d410012810046055500e0308070000c0d20381400070b0100d20040c042d94400440340106c0b6000f600464600c1d40903503000e41464079404d0b44034410025030918088017000a050406144d5028643c0301030703c0f030b04880d041500c1b80c640c42008401240d1030710b50418001a1030030069010100e6130f801110760300003822542025030000c1d0514000d4090030510042c04200820034200c00b01c1c801d580100d81d440c023000001e0712540014040d1419240c040055170801110006041c810b42c07a4400604 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 682115638 1250 682114388 682114393
    0x807050a1d15370f12020c03040b0304022d040f02250b0a0e0607050c240a0f02070519031205070504031a06030705011b150f0506011b0f0606030807030f031d 69
    0x12220304d825200900509480e0085c00d0b4240440019080108000c00141c5030580c416a00c0c1e14040c4108440b07564202618115030000841c01000700d01c8480e1000181c11085070003040c8207141c4882c40d0700030b0240340a45072000b0526101e0f6000103031031050804046014080714401540d603a0080c0c800d49507142c021401c558021b10000c0c007224400c5001e03014660b6440146c481629811020080c2c0c007101d404030701d0300c0346414400c2c8041e6150500ca1015100c540e0340d0b09604100b140d48800b500c9039840c091005d02c0380082441340701014414105090340540b0342c5c034100000c1c10000340c000d01c1908540011a25075240cbd040005110080c40c49480c4103803002070080a5150500740115424901000311f12001140700a952001400c4e50012107402e030780e2460006008442841054103540300500326030b050000c59201c0fa9202180c444091501030f82080d04510045820b02d800c0c00102259030000c0c01c406c2d8081a00c20805620003c00860700c0c0b41564240b0407401c081d10b80d080a644004284100e95 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 682116888 1250 682115638 682115657
    0x10b06030405191505150306150a14010c140319032a02030c070e0a1505280f0e07020d02120405091008011b0807050a1d1537 55
    0xe180d010856403007141300c3c80c1e0503405040e030301c002c907800c1d5034003a07a8918104035000390524641c06c1c108a800e0303000c03580500ba548110304200c08201b4000c914028070f010000d1080b6a2491640200c8902544a920114028002030700b440780d59100c1e001100b0948503504a40120526240300b802401e031960340c8640402840702c41c5000412a020480c20080c003540418000b06461403020300c5008000e00e051089000e17186011010901201c07080d020700d139002203014006004c0e545800345c003498100c01070280039407a80001d01d003590240710207a01940500030703103890104200d214590418090070b001d4007180c150100003c0c0a0f601ea444150300d83e41940001c1c4003c010300d01e49010000d801040a00c0d01c0705849441d0f01340319095650281441c4128480b00703211088056129500ba584406c16140c600d0611345074100081c00007841a10480e95200d45203500a1740b42e0f01c45402d0708840000c10161561407401800028108060008001560504500d610680c40c0382085086909039143d40c1c03030086 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 682118138 1250 682116888 682116913
    0x60501140f0a200a0524340c03030509010e120d0b0a0623090310020703030e0d080615030c120709030c03030c140a121d0d0c030302010b06030405 64
    0x6030704169084001c10903a03c0b4442c00420010206201400d14030002e0940142581081032601800c02098620724903140c10651600001c410f5840d007017102d83c0015408120216122690f25805041000c504690030100280c6690481c1c40712802078803a480034020740da00c01880c18202d03082074602551031340007601c04c001021928002050400d103403680000381100b1180100f0b05600d90341e0450700206036400c1d107103041282500c0d244100312018000081c40c250841c00807d44881d4040c0c0f98100254000c901c54040501942024a400402038203e41d0b1030507240c00000c01c440c1058a10501501142c50100d21071710704141168814140c0290007403403d040090700741d040040043c0b8100400c4210340020000035515549400258000e40d0341c410395080c2390400e02010252404585143d13030204003500005001d040055441d1032050610802d40e0100320b072810401c07805180c0041d44002709545100403c26000c02d20025240a640200b0010911034140300140c482917a001d802076001317040c0d4210 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 682119388 1250 682118138 682118167
    0x30e150a050c040e0c070203010e210313120c020f010306060507020906040e060c1908040f0201030c02010b060c07031109040312050601050405040f02030915010f0e0621030a0306050114 81
    0x400400c48a50b01c0d2074555203000840d079008050360f20510f803240014103041585000d004800c0011200c0d0094804d05020300e816044910a030014074201c65401300000b807036145001620031905070840c2c04500c1c2020784001c0100f4400d800ca100b00d124420321400a01c5951091040c6010384075540c8078039143c5013441d02000076415005000035800340d102c0c44c0c4841c05000600c03405008a486548a43d100d040145084186140904200d020030003040708000108070042406102181c080c00c2c0013880d001c1809049026200c19903200b500910b0014020329407800000c3c6ca6012240103c03078880e42d2040c150100b1600110648000d030015203c2100c28030100d00355405581c001740c05040451034a943c543c045000e0782c84054003c40119404020000002c40038003011008501052141d46c080d07040c810719400355006030044441045280380000d0340c58450748032440d1030455202c40d121201e030008030300f42e999a0000c1c03031580c0000e09150001400e540907040804031056030303c81d81c50400aa00d8402d18 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 682120638 1250 682119388 682119391
    0x90303150103020f0c010e060f061801090e070f0b0a030f140c0c0118110907080103080f090307030f05031306031e090206070c030602041d040b1f0e010e0601030e150a05 74
    0x14044c6000c00c030032440103034248140100d501d002030140185180a542c4200342c007100900150041d5052003001450010400045042d11080318000442c10807860b90701d440e205490b00048030242d410f0b10080b443d481090b0103000541e50540d018402d00b11410001800e8841848080c8419000a03002c142c0c230081e480040e18030801c07400000a002c0c20400200c184111410300c0070782d0768031000301c1c903407450342440e400c019803000c034601b03121041d5451982e8507205841217601a0000c40000f10f00e13500d00b40d0b020f103d1140203540007110b56801c1c029a003026512640003003000e038580f0700f110200192083c080d000b0350b000c00c0000c00c05201c542403807502c441d01401150200300c0e8050341c20003c0800117020040d07881d016600a0b00d0050f1500c0c01c008845001d5003404a40c41144a05e00d810000003e15900380582e00c030385ca03004032064106010220524141701074005584e940064400840c100f940389103114860300090b6424080030f43c29415694843c0c007c0d8410040300381402002071103400d066003005 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 682121888 1250 682120638 682120657
    0xf3005130303201b01030c0206090709050a0b060c010f0c11060601050703050c06130209060103021c1a13240305100e0316060203090106140907030c030b040c110609030315010302 78
    0x440c5501070b0701642c40c10603510b0f035107a100c0a00c074044130001c80d5902d4890002c101c00140010803041c00c0608000f561003440384181903c2e15260000202900c0c56500000900c0c071000d1300302501c071011000c105010b00011400d180301c1d54584030701c0810f00d9100d002c0c0d0740c404588800c00b4000f04d48501e001180c00794807004094084c0302041013159403100041103014070408640a04110044491040000941e4081c1c01c0702d04040c01441a12110340b06034075180d16105860000194021108010040071941005440c2c1e0103484c60102d000703803020380d810044403548250802e011441c08082c00080382402d50001410f5a13000c03030b010b103441101c194809042d285883e02103e0400c4105000001e07070428848044072070030303004010700c110a1024010407002c1c02c6a8010040303492540c01c0803a003401c0b03000f0840f10825860381416000c4601940c041c40c000c0324050000c0c825034000590150040d610007070044901c0c421900025581200882a2030040d1087c4104100c2c603443c1c000118080d4011105a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 682123138 1250 682121888 682121927
    0x90d050f090a050d0f030906091419050a06120f0218040203070e0603070f02010b030a03020c150403080403120f080c1801050c0610080d02190f0f3005130303 69
    0x2103034564509103949075662180340310910000d4145002880040703c1d5000318280041e00704207001040001550512b0f003001606c048508407000c41303508040725183d070700842e085400628003284042c4d11070401c42d00f2080f1070805020880300d4100f0007041784944400c942c9000a4000d03207071203900c0d16400640c1c000c07181b858540c600ca100381c4001103443d0f105542010104100d4202c010320b064081c051283d08131411805030a08070340c40c2d100651511105001c051240c0d24640c02c6c0c0d144405088261009181c10001441c2c46548030b01d02045003d2801300d0410200b801c41d0500740b07901d84245480d62040d1840e8510a0500d001d0340011000c0000900c016070501505000c42c80d500601040054428a0101002170225142060080c28103003400d09800840d00000c2060240c04000c00150500b00d038452000018000076045c104420303101e10b50014036907a80140d038007407081100388510402045080d0b1920031608000001c0c5e40e40e10030a0712140c0e0240b4200b0080010178081c5481503040c000c030031030 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 682124388 1250 682123138 682123159
    0x40b030a1202030c01060e1303050c0304090606050a080903070f15060306050a140105120d0f140c0d180f030b090a0f0606030c09050114040506030c040c0e09090d050f09 74
    0x4070800360710300d8910608010b82c40411002d240c00c00074000e00c2c0042403000041005030070014454500c81c032009801600303000f00014003160702d140c1002183e00a0440e82d0f000c003d040e844d034400400031b50180300214001040007010441c10320000c400c4a80d8603500c24001008402150b031011845000d445414a030035540703000000c003051a60054512508a06000064400b40c00340300c0340c204041a00003034044d00d164413000400c3c4200282c007010f44100703170074504c52036100f10104607030b55038000d40aa0004000802c000002500c000303000002c031174031600c4800b0101d900020f80704544035a841500040b001640c410404a80500e41d02d64001c40546c054804200d65038a94071146400c011084940980d1154200140320118600202a01e034040060020303500d86050303000b1110300c903881320784569030720700100700c1650341000040003000c0e0103001400f4402c49a080503160480412080f80100c00b080e001a4924001065203104000e464480900301141407041c101107810868180750130621418 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 682125638 1250 682124388 682124393
    0x16020d11130506030609071d04050c0a230301051003111507050601030b0105060306060304023d0905150f072a080d0906021e100f090314090a05040b030a 67
    0x11004072026403404001c01e0904181e070034146403440c005d081200540200e03005200007020040c01c00c180c42c11a20201c400342c3c032642055410080c10000c8990700c14842c040c0080c2400e1079280b0f442e0300c21040107043d00138156190a240c2030700e000f10303107042c0043d28034041400000c9290b01d4210384140050310022120b03a401c030044543d03500c01e907000d840d0755020100420070006d08a0a60780500019651141903007041000706402d030001030002441007c1c0034600743c110002401000e00a004950512100400c43e030101036203990b01d05000350002000c2c51001b03e05810001102c880001c455071000d031a080d6400044001900090030881d0140c81c0705c82c0d80c41003240300e00e00b08407130100040300a5032544e01c0c0248140c64410050b05040074080d441404002894001c42d04d485c0003030340340c079005420324945c51006040081040c0c3c80064149460107684003075029a10540c00c203442521004419081200041914091041c02c5036200c0c115180a012a061507000419000009000c5442c60022076 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 682126888 1250 682125638 682125649
    0x50d15020409021306030c090b09012c03010b061e0a050403080a030633030216020306040b01170f06070c02151606050a0c0804110a0305070b13090216020d11 69
    0x141d00000c042a0089202d24070940303070404130402440c0c0d504080200300c2c12100042c0c1006014420340300c0e4280c022034000300301e0340500f258a805580c1c115200c0c218041c1c01d4041c4002c034040c140d0081c000d6180200c0c03811740741001d01c101c51034241440b007000c500245445903481d459006225100070003000b4440040041d2901001e042143c00ea5100030a0050404000103c2c0c00400c40700340003984ca800c80251407212014002d10304001c01d5180269544da90811070081500500710003d4241c481c01040105003c0c004003448d041c1d070709400d0308040601c40b00c14119030b038000e40842c00c4a96080b420210701d1060180700c1510110303101801c10302d00329003ca02d0602480e044011b018002d403111007840010444607100341540601c0c1413108000c4000322150080c0240300c000c0008080c881a18110302c900da0b158940741000310303401422901c2d240d131114001004c5070088404454840d5061302d010481000e103009492500421500759064100703a48c08210300742c0800301050b5403810001c508040c968558 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 682128138 1250 682126888 682126897
    0x3130c030305040e060a120201120213030602040e060d03050d1e0c020d3504060b060406120e190b060a030605130201110f03030601080a020412060b1809030301050d1502 74
    0x3949030b203034941e481c25001c030004d110000c0c540d922450100f0020712104c5506404804950780a180c413040b084240103c20000748280d550610310348100010000820102e07030000d10070b480b400000b10b0b1080d2282420301000c440e044400601103081030140c2100c0c440c640e405100054640b000030700001507000c60503412104ca0303802042c01a0401c06000000540200232500c900400c07181080201c0c1e03004550705510040c902c17035115903c501c00f01280038040113801948403194000c05076030340d039a60ba40b0050100d50241400c082406d0908242480c681f00100301d41c481c50302802c2c0c013080365414035541c001c51028004c002590100a40c1c801002003000d522034130b4401c444405503a460107100b4000904071840c8032186c004145c7c45002d00700c1440c80c010050365080034081c20002c11544800056002900580c0c1258548028040012080c00500d8201e000c06100079900f0180401c03400b03007400903000342250136023216401080100003508050001015080c01030f0103200c120203d54440c48241d900 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 682129388 1250 682128138 682128143
    0xc04050a06061b020619050403081207021e030702100216140f040e03040b0901140c060a11070b04031b050a0c08060c0a02070b25060e06070203040501080c03130c03 72
    0x69808050180303d401c181e0100c0796001151803081c00100d10390005c1c00c07501c22104143d190304510000c92244a0060301681c01441d03000c50400e8403682c2800f540207800300708842c190300503c202c480c80d44050120b03010b926503e40034170020350700c0e00b0300640034400781004c80c01e40101103108003c01a45040c9902076154080e01505400d5601078038610200800b2050107209148a03900e4150350107408030340001140d0455200f0301300c041c0c0b600c9841c0300603510408411701c0c595a44c00e0000300030301c401501150302480b40e0300c0c0314401c02091000303103c90b6009000b900d10052a02c05d00340c01040109000d40c03402000c009481c0071040c1f520020765122400c10643c90030480e10380081c030a0034451000b05110700c0341e118450038412820725045083c000c4d920f0820388100c011540d4005028103d00702041c11001d0205096480c520000342c80303140660040141d080802c100707024260104d006988080111012540c05a4880b8105d40f02c0000030602c5031b2001d4403d44c410414203011000044958076440c00860 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 682130638 1250 682129388 682129391
    0x513060305120903070e040212060426040503030319150b09030f030a020604110a09020318160605040603110c0106030b25080f102417070905120c04050a 67
    0x24a1072800034680780007942c520724008024021030001d5100010303e00205d51a88801c1e124985407030000c11601c1c9425506000350380107540401c02408840404100d00040040b0078040c680c8803694440b40a00a80c02003a030b16130010004202086400401c2031003003214400c001a101080040e044a680342503070280d07503010310214112203a80740c107000080d0406158406580707000140c41000b522104000c100500301c1001141040194840304d5400001c1d19034810700b10340d070342442d5603103c00010b0f40c2007480d00381c2d1240300420102c141100c1d43e00310407180c0039210301d030030a820300d0320070303070240a800c7d10b895003803242031081071200642401a80003d50007807044c040c0c0c9007030141415141c03584d1a550070f0303010851140b07110042503001da615603002c08850341544d1251030701420110703210b03040c1e4001280324014900c4201c4801c41c464808188015589500c140c441e090030407408010001c65600c40403440c0d0140c1085a030420b00d1061644402d040c003541c2030854610005811114151140c90000303 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 682131888 1250 682130638 682130651
    0x5040e0a030930030c1e140706050307230a0e0112060308070209040203030d060803032a030c07050a120302090f0315060609031e010e19030507020103150513 69
    0x41c0c01c900c0841c060b041c0001c005410300d03802403d1600031000c0060440301c1c400c49100c014289031013440d00311400760f440010b141a14056004241c020510305030300303075003506100603501050000040c1d140100c40583e12041c0c150f94841c0d07010b484051030f40c0035034802241c1714062120b005614400070b1202d189251249600c0c5400030380010800011029181c5226103404002c0c804180c03004103803141c4642c111a04034103540c1d00d1000c00e0a50180c1030070040f0745070074460701080020010015500c95440090002161600c00044e01101c18401100c070918003c00c00102d0701c0b1140390002001c15a014800703c652042080d13030703030540c00850400c1c1c410001394040f610001a25000c2084141200300700c00074601d54a20501c40d00500e840644aa131081c08000f500b1001340e10180a8a0b600e13051301e001f011780c60f1440d00f13015800380804d041c3d0700079640200d0003600c45800c2c03228807048100760585d40f41c40c100455640103600810381d961501c205200c1c3d010000910b999040200b5000d40c03441807000c04d60 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 682133138 1250 682131888 682131893
    0x20112050915040828090b09120607030c030e1603020f0d0b10030510090b13051207061d070b030c03090102120a0c0e0306060612061c1b050d02100806030705040e0a 72
    0x501c60010501075a003054000170500a83c48501d0302c0130b48a1100703000c1d40c0e41a8010002d5a0080c10141600303d86c002c080400404d2070f050792190075000e855031428040c4180c2149091388074044201d519032010019001407001d81850380020360030320406064030350180c03120b45900003440011590712002d9240f02c2d505000700202880101c0150185034400d000b0100316a0700c40c61014402825a0501c080760415034040c40b40800800040c241d4500141e82e40f841c1a05021001d0240140004142c1200a81c180070425002075000c040320b02850f622410341d154030f02103020316400a81940070564090101040c02107500060074000c0030040c90010301607801c003801818401c10364001c00d11070f412080402038103450b008112040307588c40940d40550359aa0b540022070083c00d0761a82e940c0184400e298070100210150741c40385c2c800c031008202c20301594460400c800e550f5180030080d00311518001600000b0300801b4591342121000b410303503884580300c0c000315089880c140214080c6a1100824405 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 682134388 1250 682133138 682133167
    0x3070c150f02120d0207030c0602040f030614010b03041e02150301090c140412031101060611060a0506030a02060a030b15030a0b0307080d140f120a14040201120509150408 75
    0x1051481d400a0004210000c12902850048801010415400050810400d88030301c2c403101c01d0550002045403615101e100710b841902c11800102d03211032503d124040720699039a14681292103e03011649145e031265500950b0240702381001c0c00498145405000581c0c43c21800240281c0c8199541d850b58900403003e01618204110107051040c10143c2074090460344044505a0f1050041c1c08603552951034210340c455940d07030300a0b8042d46400404642c00758001c0001ca403841c2103904407111074070343d100140111981598456419444a00d41000504080000e0300502a003410006800e03070700000032414090309501da20027525400400c02807007100b02e1080c650501c10984c0148503440c2007000c4250341b0701c2000c15500c2480400002c02c1008078441040f1078541d09402440c0780c482043c500c450202d08016100707501c0090a100348403c1c844e807041754041c802c0303405940d509c0700040030840740c00007010b0260020009025112805241c1c0801c0c0d80801d024034440d03c107a1742d032004403900703154 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 682135638 1250 682134388 682134407
    0x1305070c060c0804031403070917070305010b03191115031612060b0d24030f050118030e211524010210020f071211101b080903070c15 59
    0x2e05101e034203024480802d910460849441000292031544c2ea101c45000380c5003803c0300e40c04102503050005100071001c00c0821400200c0c3c0c0310300f000348481400d100806444010201d410f09503541940c00b0500840c096013000e10424401601200f44013400000b506825881210603000c04609581800345c0a039005003680790540040000300070190410b0421051841101c0032a075045480d0030500340d140f0f2000d200191550307024603034501542d9891400340c86043d6004000c3c0c5055192125021000030f540c0011840d055140d44d41c591704510008c00c01c502d41c078940c000000c68407a44001d1000c1c45008000d07010944c040c510000481d450300709584400020b8120b07a9241c4001c02c1507180c04103036000038031204651101000943c5820b40460b01075a18090304a01410514190300d039001e4a50f084007501d20046404030550304100c480b050304c10196040222803031541003402142c01c1141c1d1040c0000d60300451880180ca2414a140c0c82d5104c44002c590498902c0551100c01e100301d041d080f46442 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 682136888 1250 682135638 682135661
    0x12060605090a0b0f0702300a060c0206010b0a0c1b091505030318090a0b10030e0d0815040f0902060315030601080d0912021f020c012006070e1305070c06 67
    0x83d40340101502051806002d00d0100901410100c819034a00d034204141800030300c44c040180d6441010901c10155a49038019003d4900603e0400f0b0304002602c041600b505076040201c2c9180313499075224044038803030b28040302513651259480304e9640c40c1c45000480c0c401011a42c2000c50800580901603c03011490381c4070034482c3d03100f0000b45125030403144002181010407964400b05a40c0c010078107003d0a4a480300d580d00013248140480c7c0c40c1d4040d800b468a60380f40004644c110015100181da920341c05440c4550310b00307087c1030f071084c03245840d810038018450105004201c800707855000c00e140c3d82050b07454060072201940300030000d00302040320500610710030b001803003071007250403018090103558054030941c01e1460544009548940e005400002180c401400182e00003079802511182890322203800520540c1d03021400202980d0342192901c0c041000d40328a072101c8009850848030400d0980d081201d101c8030390ac000d0024892a40b007410781d134580c0004950a032805200300c0348414803c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 682138138 1250 682136888 682136909
    0x322060e060c0c09060307150c0c0518010302090c0d05040c030b070c080405060d060512010501170a020307170712110301060905130b1504020d1d07081002070312060605090a 76
    0x211102d81c6000106a044840103a91803082502c541000c82c0c2002100e40001c80100025190351405562101a03128683d0040388071155003501c8400b0480751180981d01ca00c50400e1090040c005032500002d000d800c840ea1480442c0780020f00c0c0701c0350302541c0b0102c0b0207607131600411074204203100d2641000c0350700010f00e00c0c1403090f104c610f07600d000311030040c0d01400d03005450101c6c032003202001c01d41c40140139110007005040700c5810352404501030030090065240080080c00d47c0c03040200c1c0081c2201415600502900900d41005580230105103100514005480ba4080000b02c10192140003200f450098100e4442c0240b50701c141420340700140c3c0407132986031400c1c040241e01b58042d440c82c68440c0d809040d504054891510742c13031800200c0429658807910014400e003204170b099002c0901142e040743c94507010b131b00301e000e243c1d110000c03441030310781580001150747d0380c0c0c21ba2a402003003168402d04260906c585d48180d20012a42144c00007801f06500041c3c100383c0b0b151941032100140581c0c101d = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 682139388 1250 682138138 682138147
    0x1060201110307050a030b040204140a090c140d0b0d080c161a07030309021228020d020114130303110c030f0c01050a2604120801050306180322060e06 66
    0x10207401031000034260810800c02180364904180f1a810030312807541c00500564075107031104441d08060844030103007407148030a20300c0001c40e032401d07000d48010550310743c44000300460b600f5145c407003651100022651059481d807007070b80e96503078003400400f03050302031007510341c96044074820b080c034140f0602d44007014440303034810810828a5410401d400400b030700d11001e44911691400b07070080c05003660300940c4a030100054540b4100c00140b0964100e21500b80c030f6801e40440488101e41500d0340d20301079000900380c41d0a001650003a022110210101040c0740d19003140700408181d81d01c1c25400480018980c01c1c4aa10042e4081085842000c000c602074011200c010300305d90380e11041c2000d800c1c14080c4c08140003207030030300503143c3c0b014003140103043e43c02c224800c3c149106a01000c0710200c03452030b140303a011481684030b2072095060b01d001400402143c0c03030300807c407030103007a0342801d14174684802c100c1520030f680800b0803100080c00f00c4140d685074500306000a010311802c2049540a000c4c10320 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 682140638 1250 682139388 682139411
    0x30219080606030c0a020c0306150a12080d0b060d0e0a0b0105031c030b0a050301140702061b4503330a0209030604031d092a190206090601060201 64
    0x1c00f2a41c0181c200c5142c10f54400c0b10300c600707a06110300d031815030344e26000d2002000074204030a15610022042165400303072040e00c4450030503a564082d1405403145901b4403034076220088541c04000003400040249081004810008068036404100d1105d01d40001600e041009030000c6c0c180d01415040b40600329030f40c5054480f01c641c201c4180c0d04c0c000c040d00e0b044145265218a00018081c2c6130150080c40b00d16001c83c0b16000750340040e0340f0040144500c80c0061041a204200d0103405801c0409a502d0701e104042e400c9040c008d00c84211845c04080524104400100c80030300da280c020001d01403250812010030142800170000d04201000b01f14020003083d000403448a40c80d0110365484100c05883d156001c000034090040b441d80c252041c0810b0005051700002da81024141e100c44070800742c2119018004000710079585108441407220f03e8402402900032180f03110040d0042460510042c103540e0007828844007900805600309900f40310b0702d08410311650340034280f180000c5c0900d80703c2e034 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 682141888 1250 682140638 682140649
    0xd0c0201050a080a1d1f020906040e0a1d010e06160c03110a0b04031710030f081803010203010b27090103030c0309180e0c010e03060c070602040909030302190806 71
    0x42401508102090000442000f00e550208070031541c0496660031070035060700d8003561694103081280b000324806d801400d5481040c001ca5150b0b2102819190800b85070103440b90b406003003c1c0c000c0d40f04684034100c43e4140c21114005030066601c1400110fa510ba214400b02c0c10180003601e6100004085130115a4990700072410344070fa990b162801c441400100a082404c1100c041d100030404e0a22409000a040c0d00c207081504880c010306846200342c0750781c1e120f43e40003855031200411881007030001c82c0119198901a001d1201601c0d103100d05551441c00203401c90344260016214184081a040e10b10003401400e00c03440034030780d0001c0c132050b10700f01e00180260405100090401c039603a030442c07040610484458004000b600c0c4003400058540c0c0c500006044070003201d0403a4410100f0010242d03100d0036001141500c054054400d0b5120769001c0c05c429884510299102070b0200000503079650f983c887c03004150700a40d4010b886a60151495090104900c418010481e407441844030641e02c1 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 682143138 1250 682141888 682141897
    0xa090510090b03150a18050f0702030a0c0b06030123090d080103050a171903060611063c040b0a0b0613050405180a050705010908010213170703051006080d0c020105 72
    0x8001c035500e03600084c1ca0005901400503000040e203d0130b10140c01c81a00d01640003d07000e6914029404426a0b90a008036543c0c00354030500c07800510104c8685c0c020840c20701c1d1042d000354014002241c40b070501600030841107100203116000b24008030400141d1607081c4181c0c103621a40d07280200c09075146032a500da6500300650302421882b400380c03006403081d0091003185c4402d8a0803604c01d0354900c0b10314000e4000c2103180304090100d581c0000740c5c01c004501040c42882444104080c490700204088100030399002c0c001c4941c56014070011001e0074481818074184550f110708403030101340c80c0c900c1150382a00e5a100e4000d014403801e00c0340ea4004441b80341c10f00b040e9401543c3c005090390750340d40420801d040301c507800410703070103900a400140000890000151032081c0c84030700b211641c070140320b4202d00c1050408540307500d001038103000070200400c45083c004480300440b4202500d03522002c0c02e081d450170700c100006036542d10400c8181c205214405507450726090900162000da00080d10a00c40d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 682144388 1250 682143138 682143151
    0x60506100212090406030c03080d06090203160c0804050301060b1b010207020907300903030c1d0d0219060903060605010f0c15060312050d0b0f1012110a090510090b03 73
    0xc041100c840f141c9660307010384000d5403c280721600c10365490402100300d41c442c80b9000f089904001e004503500155008403405014a403e80302c01e0340c60700c00000c03250071190300c4049401c2007042200140c207030740074042d15001e0701c49038180d2596146464201a5000100c00405c401a40180b00c0b0300c025035a40e8004643c01102400c0c240188180351104014510318002140c1e280c0700c0000c01c00c0030001c802c1d031000030b12034840e0314104004560749006903079039080010403080c00d61070321900c2500b5003404908620303401d202030300c940c0c83d482e1501d2800c62140c400b5086540000c00303000c82042401400d001d00317070043c0801c5c01e282507900f01403200209511540c80002c0d0240200105089041c07910340c0c49100150f81180400e8214032080000034056400700c006100c05030708120303842d105450181140c0040b00002414000c0400201000795030041d50007100c06185903640c0400c01c0705441741802071103000b119696808030b82d070030541002482041200e80804112201d2420312035800541c0880b9004072 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 682145638 1250 682144388 682144423
    0xa08061314070320040f05091009080d090b09070b0703080c22030c06090e0f0601031d0601030c15030c09061b05010f14010b0307020312072a0605061002 67
    0x40c1901c040c28940401944020300c0d14040100031540c0000b0350748540b4080b0000c035000e00c4210708010360241a81c0c4141e130050156080309200400404c5641e11608a045c4202e040b141020701100d003100449194403410b4442d4a041000c128080030107009103006000340300026810071031140c900070700142c4010100c075000034001401c804c03813040595001101040400c010680a603d030300e022182200c651184002099403d400414400214100e842c480e80c10000321600b10b64400004502a04602c0040d0801c1001d80c006298440340a01025000c0c500130038000342054a02603081031151200480b2804061508107995032042d400704158040741e06600e490580380c00c6480341060300024441d00101198a8504012a9107940c0d40051350140b02d5440c0d41501a030f40c1d0302c0ca00c43e07203100c100d0364030005170010888060707154001c80c28241c0004152402050300c035101d10f07503020186c449400c41100d24107580d803031364200a0140102c0740d0011065482c500300d04079103107020703554080389090140e214 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 682146888 1250 682145638 682145663
    0x50d030e030105090c0316052407080a030b100c030e090c1c0f0e160e040602040e01060c02030136050f032212030c0f0201020a080c0304050a080613 65
    0x510034212080d040c0c500030020006810b1507580103a851024440d1140a4001c04000e01180c04410040000700c5030b000e080003180fa40d0141803107400007500c1810422030b540900c400300119a8080103000b88410f113840020f04181900104804500c00d210031030104030002c001c1c0400130764030040c403010310b280c250380301c40540d22204601840c6000ba05040f0412450a4a1340e0300c28913400c2d000400c188450000c10450481090051ba031544040400da034001100003808100076140484010360050003480c0043c1070031703107882042101d03003400e070702000000e003119441909514082c42030f44154a40b031132814030791919401c002e107002e4042014044200c40c20300204001d018046c0a40c1442c11050f109480d038491040b581c484081192480030740b90117003500000306031303451424486401c036078140e00c1c1d60408040f40e84d1000c0801100030012411400364480c02c10000300407a000d82404864800690b403103504090038021102c1281e400700032954406402d02c580c80e450b416508809507000000003010 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 682148138 1250 682146888 682146893
    0x9020f071509051b120f030405061b030706060311030f0c0d030203122e1a0c0339010219050a020717070f060c02130e0c06030408030702010612050601050d 68
    0x20300c5a03600c094001d0103402d01314000c0b055401c0c00c0030544402103481289070300c20100325940c2c880d00a42a021903034010441805240b410314090005c80710090b0704c917526911143c60b203a0550b00504002c48a55486001c14802c00c61074298129404905078000d1100041c030000d00350340d42c8568941c40d4000c003400d070201018140709004071101c4d2040a40441400e007441c03000b40b20442d60040c10440300b074525418446501c03885809110072602c5810880e540c10810136448009544011406601440100112003800e02d4012034a132401d290440c280700899102c126000d000224800c602c2556441088205448000c03500c0058601039140740290b1035240780d1030203034135007941030300244841c00d42411050b0038100700042c0c0c0015079121046070f845103a62040180c9811000c0080203601c0401c05d1001d415403106540320103035180c034440032a0100d103500004258183d00680d01540c2c0c1110010800140c0c98090203410003c0807501c15078180e07943c00d503d9283c0c5500040c000c0510900344c14000809 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 682149388 1250 682148138 682148141
    0xc16052b021011031201060f080708150607060515040e03070305180609090a0207030f0c02010e01080a021308010e1c140a02031e07020f06040510030b0604170f010609020f0715 77
    0x80001e2030400f00ca641d0300709070460825800d400d2103a0000211548c1e010460240306035903603809401c0035140c190040e1036501e54114104c10190070a9040141401307440041203103402124002d80d076000d04005240c0c0e056080c0b00640d41c000d4044140d40c0d208005000010380e20104507407259640d4498420010300d0400001d445100e00800d00b03501200190a1182c0b4580c29401000610b2180e161103000c180b5a09040e2010a02c000010b4049002140c10642c81d5005e2040582d1280c0380d81e82c0140303000c001050340000811540c000c1c0e01c42e60355038540c0d140300b040208800c2a50240c0003505144c590605000180003240481c00d4201450300800c04040c1c07203000b0410707185818034840d004400085200b10441c0e10307400c5020164810403141142c0b1140342031a1040310144c403406002c50324804100002a40903000304a0655003140080000180069002410b40c0f042100300d4081e0a618814503403050945440b900000750851040080704290201881280c0506500590415150f07014081100 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 682150638 1250 682149388 682149407
    0x9060a050303070c060305061c0201050a02010f0c0f090b12040f050705030d0309021f1b1403030408030108120903030a030b061201030b011d040b01030f080c16052b0210 74
    0x750107100c08500001040420408035007541d650381d5040110750303680d40c00c02c4207104420b410306481041100450f00554454402403005402600000c50400f41388459841181d056104510004650018031000070b41e20202e000b0003000354034415814400c03805070040d100100948010000a0f203030035507008000c42404410000c2400600b07031550316103d684040d01030a04040d00728850303103607003081c031501c164124484160601c083d40e6000e600101c201d800f4100038840c2000f516100c0440c9004200360400300b0017107126510078a1030755143e500d04802c1c24905540c1c1424000840f60a020040d1503440000036142e058a81d490042a410408000300710f491060000500c00b0b81041c00010051109060700326040301d0000220a04002c0c9102c5492515003003598000d0440c04000010008240005482c030511802400800d103404682c2070b000703140c000840004601c240c2d65120030802d82ca00200b5604072508070024000750700600b504c03a134517581c64800d4003c1c442e4a0500058011030310400080 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 682151888 1250 682150638 682150649
    0xe012c13140f01060504060b03040f0b060316031b0608010e0a090c051c020f2e200604020a050a05030619020d0630080f0d110a0c2a0509060a 62
    0x880c0341c1904090300b240038180c00d00034240a00e082120018980035214204c910542c1c0041044205003565580c1164540c4003410741c41c2d1601c42c400e164107504442e1103c00d002107104c0e2903000c520788004003070341c2c01640040e0b00420510202000403c41032a1600500382d10a0b10340800060300c1c0e5003480c082d0407291841e00200c0c0c2098440124454404100100c903d040b4000c4505034406081803003004107003c2c08140343c52011141d4400207100d41c0852120382000030684c203241110446842c00400e04e45c0031041480d455a000c401404150b0078180c90007006054191880711016040c0030101c2d5031171502400c07a500016143c00c140310700036450340c1610f4211032310403001e00480b80d95800007140b82c0c00700000601000d10440030000741401c049040c0c0c030000d6102c0380090410410000342c2406401071000300380c1c0207842d010100b41c2181020002d04185040341c9400c81110003506007040420300103000d01540c25103064100504100e20f0813500101c58080315003101c20381d84c10020507100385507503200 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 682153138 1250 682151888 682151893
    0xa0b06160b09101109060c0304051005030114010c030c030e010c050d0f020f01150b03090a0609080307020d030b0a091509090b240d020409110a0e012c1314 68
    0x10030820000225039405542960308843e002900c0c884074100f1503003041d005400c0d000b0100325100d0241817100181000700b014905503411b1583c2d035000303c0c0182c44030a51000010b91300000501030604070f0030240302007060030305e0050003141c030300d98010b090440480b87c041c052042ca00d18a46440e0700c200300000c151a030003802d8981900c981c0901415484451020201501070080c21161b402814450000075051003880e45c486035140070344a4080d5840035049074144e01400c0c0d511800700e10b0600800c0800c1e4803d205d801d0341e910780564005c4c20041500394003420182407281400d807aa441e20b10000076a0599080050404120720f00c01608900c0c9a20001146003030000da5824018800c620320f00c100c0b001d00d14001c0082c980d03000340c0040b060140340390303621070701c0c015401026042c294492084980320704030b250f00c59078110002562250300340d0711500d800300380000140a030081305115164404d00300c42c008045102c045000c20311400b4001c107071142800b00c9118000600c200b003491440312407511012b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 682154388 1250 682153138 682153177
    0x60207120216080f060a050405030f0705070f08011404020906010e090406060311060406020d0e061b0601090605060906031504180309053a05071505070b0f09060a0b06 73
    0x40181d207a00300ca80014180b01da41901c00a18028041800b007201244400a01200d66441004c0b00060001420661b4248010b00011401000420041c041b882c0104018401d451500e910207aa8910075040344a071030341403446440c241c021040102e40c0155048a1030201d603994800129a0300c14400745195000a03444107004c01e012040d80f109064034012400000c01d01d01e507405000c1c0510a030b01c80e107001a4404d5410f01c1031144140350295030303510000c09071864420802c1d810000702001400140403908502c1c010010005144100c8005000507a2030506040d0000002401c074000101030307049461a080000d141aa103c0d4042c10040f8808001c3c101401c01500b802880300415024850082c220b16041502d10040c0c07401c00d05010f801910078040702d0f80c0400d002d180f0b800d04082b003101c0c42d105d141404500d49105680c13030f1501c65929030b511034840e02d09040856161001600d04403508a048081c880c1091003c40c12550229814801149802880b4080b40f0240705a0f00490300301400c000 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 682155638 1250 682154388 682154423
    0xc0607030305040605070c24060f090f05010e010f0605070c030803010e0f01050103050c0d0903090f14040b060c062a0304030e10032a0c0605010f18090507030f060207 73
    0x18005400746001d10030400c01ca03591b080b07045c1c60458031050060118100e8240400c032280e103464140700c11005221000c180b42c0d0b61481c00c0302903146150800b502580c0c464500c5403e840b07a074410b507801000e441d8003072042545000004914184580074060400800003a0b0340309015041c0c039610300444e40b1a14850f92507941d0b28540040613070580340d000580381804000182d540c824011980a8a401c200d810724000300884804000e19400030100c05001209000062003562064107400410040030102c442100300ca007003008032080c1d004000d100e80010b000d000240c800010380c40d641308250b03810981007420780c241c000c5003140031804010300a4600004020425603c0840309011110030703241604028a440c0c426010b032a282a144000340d12005c1c8092510b400421581c40b11030381c14104808007540c96102c060644030260004225030400c1842000182040c6000000340319500204010ae8400d9076035240d1503600b54840a0595640c0401c030700188101903040b00c0d8030070760040c040d03801d803050b04 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 682156888 1250 682155638 682155641
    0x4050d11030f0d0212071518050d0e0103180b07030203060d081c05131101031107061a010f020a08090d020f04150e16090302090a1b09030b1501021c020c06070303 71
    0x50240c01030007000b444c3d00c01e02d00000d003038034901b641c81200e4452480240410b00003e00d0459429a1460b01c01e000310804202e007030181414200e09a0754000814500746d0015081c0d501a005042e0015110b60070000460421044590403140c03610f00035a0725201c10000840348608003102070300031540041d180c10402030100c403070039141a03001400d0180b9074810000c2e40b480d0070010300144c5a0380341c0303611744407030b030b41c442d5100c1c01e0041424104203082500d185c0320301e41250b03520081070180558a119070780c100d43e008440c07030843c10003e200500812082d80ea810542e402007028440c0a1429800988119682c0601c03100d01908080c00410010038003101d61007040c8201c1c4284000c80740034034045150011000e445803c4d149071342e211190b0751441d550030300a04650042140144c150b40e8000c49410364501d02044c20f03145003d6491703407030305419818003d1005402030300d00c22068481d4169400340d41d80205100307820444800342d8007821900d4460a1f401c0890041910760301c002c3c000703421802c145d0036 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 682158138 1250 682156888 682156903
    0x12080306150d0c090501030e19030207181406090601200a0b0708072727110a02010c031503080d090803010f14092208041d040b15010504050d11030f 65
    0xb81c1d5200110315a40c5c000540448811044014031500b00c2c802900c0d04000f4a1221121248688120748a0359075441c2f00703030342d290340011458916646404507030f5007110a562902c0d412880c21a450001c0f4240600003800d080344080140103079012150070300900820070f0102900c040e410240c2c0001620340100300a003812021201c1c40701144c0c0f51500484201d48111444c010760268035403040840e030401d072188069204d920740003c0546110044c03079148243c14000d0401400354400715a07180c1c210f4590290a542d00254403104142c6401005a85149258003400071070740c000982c50356400255280c080507046080000c1d00700c983c000000945001035a41d07140480710055403902001507c50100a020501510301d80010108800711042c5000c00450090625100e448954600b17565a002c030b0044181801a0255043c0094100020b004c02c0000c0940d102005440101c4004081c1002903c00c2c0103c0c05a5405036501c21114403c10810f481c950140c0200182201c034449401185550b580c400d = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 682159388 1250 682158138 682158161
    0x3181c0807021b060a031a13020c1b06070204020901170103110112060e070810030b010e061509030a060f0207050714040e060f0106030c1b03090e060a12080306150d 72
    0x108400c508140c804034900503003c03140100502c0c98030300481e80c21806014032040c200100040ea410740c41040d0b9a03400480a09501481c02507143c50901e540142480c0401c0c00c1c0011061194202411030368502e0225600154102e40c0140c072600d80c040101e82201108404000d903400c04000841808251048440b441c4026a0341c1804134440c04032010643d0002c0c855125031410b5080440c4406001e0007100380c0c07003010320141d44526a517031b0b01d0344542d00d1000ea022141d080329100034003405080142a140e00d051544081c64909280d91000c02d0b40c4c3c025400d00036140b140e507411915800001d0740c0498090a4100382180c00c0903440d10100481981d440c80e40b94860351400708024803049002c560b4a21410400c01104942d80c6042400d501070b014110540041020f51080140315001d050402810180070323aa882a103241489030415101401410881c481c424056007001040c04840c0f101c0312041c0c0c010003844e1641c036030074042148004013040141c542100822107250013502e03035000451514 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 682160638 1250 682159388 682159393
    0x1202070f0c21020d23120904060b090310090201120c021f060f0e0403140d09030e03162310021005060f09060d1703070309030908070b03181c080702 65
    0x11100c040c1501c1942d01080000c2d00003425050640c0442c44400303c0c2407001101a50500550414002e00e90604100e0b40c8a0b082045010031a01240c1c205841624082c00384800c419251001c0c002c0000e540b0500d6509014016440340d031800c04592044030034141c990300c0100280280750947c2000303034451541d059031030070340c80c803250b1041070010203800703001c085a002c001e8030b025031800c000150f115140020400e03410700c4020b0b14480c882e005000c00520351f070a50841c0016031000785140083c080b01e41500414070a07449401101183c007041f923041c0040f00d0b220440e40708001d550402442c2905440f49070300754004011201c1030038180d00404c032a54840c180c1d00080290740c0e42c210411240f007030103c05058012521100040490030560b070000c4840c0e000342c070001d1142281190f40e400c0ca034022501240041d4403003030120700301a040001c2c000a048144040e1071001e0820b00e110040b0700008040c00c2c440360881032100e1107248148002013031001b292102011402c10b1020240a403034080d1581401072 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 682161888 1250 682160638 682160669
    0x10091107110406030f12020f0a201008010b0a0221041e060c030804141b03010c080f13030c17070215091509011107231e011202070f0c 59
    0x245460f114400a49a10920301011030301c654451004078580441ca0106522030300d450004a0002013020400b080d11480411820458116148440421511107203004124880d410300c40c4942060b42181500c6540c0035030380c1c48210380300c8124500402d01622401440e000700e070b22003001008500038030549501403414100c0342f041c5602184004000c0c410b0700300052140c0300070300010b031259000f26000350080002c07c14040700c200f0240d00781400316064000703840d4001c241000d00c0c1020700844500c181941400c40c0586041c10007856640340050401600384ca4202c181e200701801400005c0c1c1c519042000911344803050448144070703500100c4160310810426141030100210842243c007843c901070a2a051142d09031844c4419030803804c8082d050001984152000440410000f00107000b001e5240d5080030040f20041905450711480b2401044440001004210b2050300c41e400d509080c41c00300d10b0000a00c048c18028002c460005001d003004041200c28012840c0070702c0183d852011a100b140c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 682163138 1250 682161888 682161923
    0x50405071409010f091502010e0d09120b0c04030c080c03010614010f080a020f1809070206071b050c0904080a1d0d08090a0b03040503040305010c02070b03010e10091107 74
    0xc84258a4685045400402142c0d441d5445054034404041305803c2c0300b100652942c0e42e40d00180e024802c0310005071f40d5003c0200900f4010841c0d80000116805c008041d80e0511440001120103010050013040300e14001c03510580c105e20031140299005808038080a80f10340c4042c0e01d9442c00c1c00d00e680f0a600b4044040360b0300e1030810703205089840507124941503c4035080141c0706003100078031190305254284050f0007220310000007001c200381c8076540b240a01d049401040039803000901441c00b1507229908000d111a08003000907001e0401203000c40454209240c020314141042c0c2086030007401503401c0c0401c002185010b80f41e0200c158441c41d403802240b81d22401440c071703158440c40c1d010302541203a002150340000207120b1400040d0100950301e4903440c1c580e1503540300355012030312540009410014020f0a108100113201c0c0c40c409002c445103442d400d005113001c18003400c0d1105824030082214203040440e094004c0c204070409210f8000c04001561498111901c261024540c0d00c101c81c0740b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 682164388 1250 682163138 682163147
    0xa050f061b0a1b0b13020a1e030206030a060f060c1a0f0105010e0301090611071a010e190b12010c0905030316030521040602090f011b0b060a090204080705040507 71
    0x14079250824a142440703200d2004542441d04024640895040c40d0b000d40049641c084096214851040090620001500c14480c0100039a030180300890120340982c0d8119201d4030101003182c0d012203080c0d80300d850b890300d800c000301115800210780d00441000012a16001058245214010408441582c0c0c01c488040306a4a0071181e080c0c040b18044018403196010300141c039460440070b800021200c4032070782c803e41122410440000420008a104400c11000b003a01134500c09110080c1c241c5949850310307154420a01508200c403c4021503848590b001080d44600401280200104845405040c03018000c4c4010600d8000007501c0305030200da0f80c10300104440d109207840c00c030f40003200314548044995402854003a0100c0600c1000561500030803000c0b14041c40c001d4030011b0786d921200e801c010944901d20040c0e4144610491000000b042c0c1b400580b29480d041242c9100380e544500002d50380818036008440c4051001c40d0105041c000025110150b803420b60303081016846400090310f = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 682165638 1250 682164388 682164421
    0x150516050c1c11090702120f0405040c021b01080a111216021906020f090901171606050d0b0609060d02070c05090c030a020d02270a0b0903070905180a050f06 69
    0x43c55a0107048108410b42040b0f4281580300d400391054840c0c08080306100c0074a90f1100500a540720070110b400d0103a8075140c4100302c1e0b00c40e0540001d050601401c2c0c8004c1d00c074600c81400905011b8003800065661403940c10829042222402046c0c3d0303012046220202c408050340c01100c1c0490031041240b544c3e000107025507041540c03065001c0450880d03558400130794071208040e9070304042840700c030025448810400e4060014002d6088071100144195803070030707410b1501c56007034100200040241d2504042141c091106080340400c417440c040e400304130700d44280c500103500004001003c01c4607600c282c0c041c0400c40e02c2038468075529555001044508a810398001c0d035004001c0010601490456000b00702801c080c04d03001d800c0c00030207100c44143c04504e41c03941e082c550155202240e41d1900c1c0040e41c1c003900d14040300300c0c140000c04d000710750b5549040c05400125990381020031031000728074a034070503d400400201d541b10b0240d45041b584803014641840301c43d1083c0c901044150002c0712485 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 682166888 1250 682165638 682165643
    0x10020a0b1803120603010b040905100e2e0e07060e120705031f09021008220302030406030902030a020411090315090606300c01020c01030e07150516050c1c 68
    0x6504040c0c5040b08045980800b13801e07950f0641d43c60000a00684580c0039010140e0301a00c0030744400d016100c212825510036450a11468000c0140c915151444075406e885512a031020f5411003048000740784005c041c00700b4982424410100c00141556001c2d5101c0110002540d060380c2c038410144003a50340f01707218064240e060300040c405807000550f01d0b100d080c041d100b02c40d01040c0044a9000725040c0012240d00900040c035510400503071907003482c980b1141502003102f0003005001510000c1d240d0059000351000c164a40c40c0c2c080039540c0804c00e020b862078000300304000800c0d130000c82c0106a8002c1404900a003e02441a425000c400311901c1c828240c1c0e101514080d55501d040103d000141074944002644003102d0851000c180c04d064001c002181005048200b0300800280c5406901900340c4d041504040c84c0452002010850354212120144100d40602c40010192142d000b19402c042031f2490300c00c13403038013400300028610f807218000f80c2d54588080e00f0300200040203102181d01 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 682168138 1250 682166888 682166893
    0x91c08060d0b04080f040806070e03060603062e0b0406030e03040605090907110f060714070309092f070c0506120708090c060a020606030606012309060910020a0b18 72
    0x900780494000e00600da40544181203e92500c14032090395405900150000e65456100c40f0070440c0c0e9680124140711043c400301c004129515040002a6076028000c2002e40106800c9074040d501c0941c614040d17079004c0ea40951443d200f0344610400c00150014810240024100400201144004021a815500c5c0b40e942c0914240c1034506001c09101d01038504000c006100702d282101e036500340039450701158690007030b00706400c00640080058154503482150300c5410020000020340100c407400c03c540140401151488421907400a002c004080c503003a448180030100d04004000c800600c00d651240035000002520f03801844002d0107144001441180c0c542d0208068034006c0121690203a405000c445100035440e02050281c0c000074030b49000741c6e0090041c81520701d01400000d030302801c00c1c07a00f010009290408044c68401c200c406480044000941c107070b19868600031034030480c101070b0100641340c400000017503035080d40c0e0a068900e40450804641c0500b071a400070800c41c580d8500 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 682169388 1250 682168138 682168159
    0x60901030f020612040f06060e0118090f05030c030c010509030f070201030b040f180b0138040e27070506040911041e030b0921090414091c0806 63
    0x71800035445041100b664442418030011a1108061803442d21840c40380720003101d2400603281400964025820056110380814014030000b0f2100070008103001407110b004c503039814242844041440c400ca0068040e0100003000380b8112000030060030300080d09002003080f0303035442c0d07002c5442e409070400b410400403007041841d000d076110781c01c82c4042c40d0000b0000a0b5200078140000d04840b03003584c01030f042e20840180702e0184800c6181050041c444100001c5043c003003014049601003811810120602c540301c800d04202a264040d24007508901c11a0945400d0006140040043e060300c14418829640050300c1030090105040040f50030152050341458207004d00c0c1c5010307140384140141c05980500c00083e030003880c40d00700e44004042c1e1014113000760450401d01500c200080040019034072540c0c4607000c3c01280059000b04030500d948840d10343c0c28140001c3c0203400c22500da0342d24044101e09005c1c013007002042003540c5040303840504000c00500801541c4005003224450780c012901d58 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 682170638 1250 682169388 682169393
    0xd020a0204020c0c0306091b09010b0d020309030706090c0905010510080403080601021609090c170303040b0402040e0a05011a1e04051b0c0303010501080a1103130c1214011406090103 80
    0x20040c0c000f5500c50f00994480c06014008207103060003c0f10500709070341c080300010040101c004800c6001c1401516801c509604050440c82188550090780700d02942c00000204000c90600130f403081c5550094042c0404103160070310440d2140c0034000d80c80901d24280001429282030301004001f07080a41780e03040a9611a01c0540e00321800904042c10b5006450911003020289015030001d00f000c1c1000040e0480d50341041940c1d007101d43c1080c0118809000001040240001a26406a8003000c00d820381d0b511031000c54060700c00c101c640400e900c11588014100401904a00d00c100302c082c843c0c81d141944041000040c61140442d03111030441d0721031024090405800c05580a800c114076919003100c0801103034003550142111a201c1d03000440140701c25a8050302c5c41da041200510240304030f100c5482500401e00c006403904620064444952040040046802c0011712002d40c0c0051516130504000a010030b0220900320f040d4648001d010390ad55854099900a1901070309242c1268210b0303 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 682171888 1250 682170638 682170641
    0x1031a040b07082e031202060606070f031b111f0c17120106050a0e0d020a0509041109010603021206091e07120c09140a030b0c0d0e10020c0d020d020a0204 68
    0x75010080f101413050f01240d0500000c42041001d620b1074441162440c6581002d0301b0080da284441d10454101d60140510780e41c5800990704d0058100c100400d50643c14942078806a120f103030310380721001b01c035100c1000b4440c40564580311284180d610b07a02e15050783c0b0f65000c850113140426000308903456040f0700030604240304904c0b01a000400c00307150010880755201f10143c01d91001c00000d0001614051156002842c44c0d000700040e10305410004042c0e0015040030800e00465000e500408002014003030071000510641d00e004e40b40350b03515610351000030003030b40c0003041002c0000c2024002c291242024030b6014030501000c0d0300c0c85044070a40c20041d00101c009800c4034200503801c09000414000341c46035401c003d0070b6441c0c101e0304500e0800305201806840d42d0b003d100303413100c0b482000071801c21501300703500411a042c266501c2019101101c02002244d05c4c05609206804441280c401164003d120307260b038000440358441072149003240d6510398500b004005030040c480c480010b080a = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 682173138 1250 682171888 682171891
    0x106120c2307020f1c021206070c060b1f09050411031524030708040b1602060c0306032e110703122307080a0c0212160503190801031a040b0708 63
    0x280341111401d000c03070000d2071903006688400c01700151500c03543d0461414080011081c1100c1c400360403981381c400b20180c00c4012146001c0c007400d407681d6040c04180d46041084034814502141c1300a10380038050010070074241c3d03014080c06075141c02d02d100390f041208001c0c1c030b06c03450754180c0d008851524001032221801051110390100e034071092142d140300707007907001851181c1241c6e90f9083e074516090034403520702100a80701400c210030108940309071030360200f4901d90050f400d005107552500e80c000401d240500d4650040301c0001c1c0e155214600480c800c5021a450212102c240950300b240c503800a8288a456402000f050011400c042a00003603000403003c0200c0c0a0340041402c0c80c2242101c02d00f50448094001482041c20844030320b05034440e81e02e0740780e201e10040045940381c0301810301074800c81f0041031402001c00305440401c50100221b0741c0c18180d010400c4084070310000f020f050440b082c0411227001c2c54624400f44042800448280f103960401d018010700c2d100d101c403d40c0c1c1d0040 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 682174388 1250 682173138 682173143
    0x7060b04020708041712160b040c0f0e0a0c020102040501020601120c15020c21070302091008070f03050705030a020604030803180123010e070f20060106120c2307 71
    0x400740405008030300360b2070291005044031010746540d80400d001e95424031440007070603000c10b039040c81f0101c1048040c4985c070040ca6805191580c15499a00741540b0744034840d40300d02c0315021071001c04105c10048950144c051030761060140701f110b1081c074041e4241e00840c001e46005a11a80040010103c00b18103903a81a001c0d0340889a85600c071800c00483d0314020b1a803001580c0407d40344d02041c18484901d004c4807003242c2824440b602c1c0034ac02c2c40c1e214001884042d2042c02c016011490b8008000d404600900c4010300306e0307002550f28428015200002d00c13081d51a8054408002078a0401155910185500401d1a0714043c1180e40b000540e402c040c1902400b0614640005444c0d81c091003200300342004800c1d80d84040640c500c2415041e20f0513005551319920541c203001126030451255000d03034907107060071a4110300308107003100031406181382d5402c10b218080001032070b103070020417501014240103824441300d0b8510805813541424400d0b07100381840b10712040c41c0c4851407040507000756031 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 682175638 1250 682174388 682174391
    0x140f0d120b060d06060e24071106040f030b010b040f0e09030702031501090e210c1006030b0703050a0c0e10020f030d0605040b030604030c06050a0905032a0106030807060b04 76
    0x1418400890354a40120f01c2c0f0305120750b81ea140c140326880c2c121641e030a4a420846580c44051a500310b11014180d2a59201d14034510100c2d1180c200b10000610044010001d4031441c1c4565482030b60410903c001c0c442a01c40084040002c00e40000741001c650a544036540101e2840b807808080c590381e40700007002122203000610074400160350502c5400d08110f01400001155410001101e08482e6030480c1c005043c3e00c0011400c8100340508006112028296003440d1505102404c2c2070030219001082801c01d490003501008100a00140ea030190500d55070400107507451420400c12642a0080d07840860b07035491036110036103007082070001c0400c4184140c0341244a400103491554100101110419496030340c240100e08142c81a0011250210010841400c09072006000345a12400180850f5110300020300c0d039865039049118015441400c4079540d031080014284408000c0c01c0650a14194143d041080a414001c0c1001d90f90040809441d12079241d031410020320541303c0140d00305 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 682176888 1250 682175638 682175651
    0x301030f140f0106050a0b0c1507140c010906050a050112110a17031b0d05031f030b040308041104110f1308010501081509060106080a02090414090a140f0d12 69
    0x1428280700c440b8400d030b030b1100003145081c1480c080206000450b0060007460509100380b42d01c002e8005440310410f01401e08540c091740f200d0740708861001c02510301c010701c1d00d030000d11550b5141c01548240c40b410302031001000283c55084060055400030710a428802d0307a0400003101060b144480d1008010b4010031100d02d440d034039900201154441c2c01a0f040c4d070340004c80c0a0405410401c2004d1084410780007501a030741000b5400381c540d01000d8180c000c000e40c050980000f030700c3c41d4039041c030203540c2010600e00c551803d490b00512034030040b2012903804c0581c0c589070010342803601802110703040c070b02030450808a4400e1816065000103100e0080c1040001000400081c213104540c00307070044a0140104138401002c881e02540c01908422465000b880100080380c1e00a607030f1504608080307000350780e0314003e000041c0504202c00100503140f07061420b2055842c80040c4958a0300d00c55401d003041d40d01e400e120280c881030805076100e41038200866440319644240c4444a00300100480080e01 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 682178138 1250 682176888 682176923
    0x30b06090a0f1811090106051b0a080f04090f050c030a02210103080702090709270906110310080304180e190807030e09040309030b07022a1f02030301030f 68
    0x2980d03908003105a0003d00303800041d040c02100702e400c3d0011081518052015450907100601511400c9007414118400c081005d903607200a002220740242c10a90351916100090a40301c00c0c0d038800d216030340c1400d00c2c215140560350b5480c01050b01c114501000300c0e0550340ca40b09107070040d50080040d00c82503d44032800c02240c45001414501840c0103015035a111400c41c41440030707040f8046c00d44420311660140401c035002c1d680c910300318101c18001425024000c41000c001c040c10790001c0c014045810140000f515241120146101d00c0c07a1400740711010390340b02d0b022520303441a8021030480700b014420000103100307513400c00301e1004042c07412a00d00108002c000346211071a00002c5440000009107001071552003000031034151404c5460b4440303410950b07009007640c0c40c584801032154070348800103001540203200d02d091201700d17a0409280c40d081c65803004070041d481c0c1c0645100300301c8c580f910380c110004031102d80b49009040c0c00440c91642561a25403541d540203900b1103806284004a0340c1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 682179388 1250 682178138 682178141
    0x501110d0f091a0705010e160510050d0c030c09050d0f1b050a060c02010f080c161403130503070e040c14060906120f0f06010917070b070f06060e01030b06090a0f 71
    0x89065510b4109600ca4503d445c150342035910b000c0414071941e208d003080e0380070f4417006c51081040360411a110000700c0b9002c801600c071030180e0b9000c4800149803541c144806501a000b15000060307550310b801d00c0319211801c0240f020014040a01542503c2c01c00000042e01c0911400d201480701d0030421056940340e000440d40b281d50782040f00003032182d0460f50215600016899000201801c03c2040c0e23250104c0c86101d507003e600400805804030507003d40600415819012900308801d06581e5039200b4010007038501041481614020311484d080043e01d07141003580140610340c41700b070312072405181c44e184810491501c401107a0003002007040d049035984040081c0500008142091610319004130301680c50400141080d10b024008002c001d216a0701a9000302a40c8400304040315500c040ca40161409200f90080501e4100009028007400f48041c5079280c40c0e40310340300602c00c140d290042c0c4c080b050300078800117010b01900d81c04140b06280078007045034052039004d80040e107640001c1b00f050 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 682180638 1250 682179388 682179419
    0x10e1540240501030b040204050601030603020a0f1703040806191b0e09090d050319060b0c06100609180218151b0606030a021002191b0501110d0f09 65
    0x295499108007101c180202151600300c01d0206000040009614644440816140041009225581d141d00180f001ea000f41e0000e0041c42d000f0382210515602d607001c40d01790310402c0c000d80414292540c024080c603038000045070700755550780003d0900c0c0c0c0c5078400401d8a409140400100b0ba64480302010a4080c1c40c06584103071900b1a0359941215800009000306503001508480440e040554000401030300304084079040507074000390a8041d00c40c103459000428803a08203204440000400c518103907c00292140140c1d40c550100c081a9900e1500b0303144400c0a10a0101d4242d9070000c2b801250400c0d405001a411141404030f0803403034280c00100e0b540f4824100751000400840c2d21202c40a0921101000b4030900c80240707198100500060391b642e1141000a12520000e4800c00c2c4191085c010540c00030100c07881303200d01c1c450307901d02204502020241c500e10340169107070000321907100d85844059903405402900007800915000c81f00d02801d4809542407200b15600002e0300e0b0290000034 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 682181888 1250 682180638 682180643
    0x12230601051c050a14030d0501080a291609270c1b120c12030c030b01090b0d2705030d0b0d05030a030209130c02010e1540 54
    0x9100540c189400c0192803805a940da4149016200c01c81c2e0002c1c600080e00000180c0010048404001007441c4500d548140182041075604150001805140000f2044105441000001c90100039485a110384030482c405c078441800d4030001062492590718042e1030030384403a1511350301c115194903182421401c0d04640261301200c01040e9102105075200707000e042d80b00742c0341c16581100307040da0a09e01107a81c000007524220f5140c2401c1605401001c07150991580180c00340d6220240010103001081b00c107019a003c6030a0041c0441d540d0301c11803050f030035124040ca10504207180b456451000740b03420b04c80c040032508e03402c2d1010140b240707006907086601e205d100116503c04e0032900807001d41382c0030300d002d038026800c40001800044021003517a45960003440c0068440880800241c0c0300311421035221103180c5031008403910a681904280e0308907404070100c4030b9840314518945100d07034044400001050000010f1814000102c403408816100c00c0091a81c100d0706800800da0301410b403404 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 682183138 1250 682181888 682181893
    0x19050d1b030e0615041503290604050f130501090506190b091005060f040e010f15020c0319030e09010618080d02030703030906021c02180303131223 65
    0x300c6403541d03240c01414260715201c0080c3c015424020b03003c0780c000f200a2481440342e52100000b4410320340700714105006580020200394901c040244003078000f55022902c2c943c00d420500080c17881e040c00d0040354050b15001c0344e20000d55803005d294030302250b0804030448843d52100c00900119000308800e50285008082841d002384a2810344c1c070449180d80c10841c01507006108001540e01c0c8020780d04221a010345119035140400010050b40d40f140340c0141c00c40d012510300206800788134918060a132104407110860403c030511080c0c0e0742d9490342d504103034942d01c40031240040d402c1384244060105d01c641080010400c2c10000074103840400d8100c0c40000b040d282c0000c0c2c51507081101e4030020a049009400d80442d40d260081d26031050802c00707411705032110a46e00802046604590051034411020344d01c80c940007008401a611410084148440b08209448146008011903a00c414100481c3c003d0501e46100c2c039013054250002940d8904801600003181c00c02661a842c410b030b01b9801 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 682184388 1250 682183138 682183181
    0x9090c16050a1407080f0d03020a02341202090105060a0c020d11011701032d02130c09060e130b040e0303040605042306070809071a0d0f05040819050d 66
    0x11140c07a00c0b04d0b5500c5100e4650026000f07400354100420541064003480ca40541e071000314400680c5004200e600c4090521180d9204c0410032075501c0d00020b080114013002c0f4042a5109507489001c030840e2030180d0300244550042104d407a0500c0200403150b40d508089200882035000103c90340080c060588000e1801c0c5400c1001c1c1d0382c480300c200224000054850281c1d410368a5074299810898042c01a09015001903144d50f14803c0d041c00c1c445a004080d05010002c1c1c20804000e0100d00400c0c10200d040c80e4404a20a8003030b1805a2015001900c01d601700041c2003031401c06800300b00c1455420681d212141c05601c00140025032295001d5100401d1034103103894040d0625046001d240008600c0741c0030505560780c0410103070b4001c03110f0700e84101541c5560000da0301300140b50740034401d00e0058850b02c041b01c503140800f030300101c5484002080440340720010792040e5242200c009100c4e1208003ca0b40c905680c483c0713091550303816072824509080d000409901168500c12010314040329851 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 682185638 1250 682184388 682184423
    0x16020a090204140a0b16060504030e0a060f030e1908030415020304081e0f0301060309030e0415080105092b0504090501090e1009030819110301091b020309090c16050a 73
    0x148030030010702100440c1031421b450041c0d01114481d000c0b030010700094582003c42d0a0621540307901480400041c6000891a5601d5024210070a40c200704008a42401d000d8402c80501140c00407030041c00d820520140070a0307036108801940001c0003107850400c0d81c2841014176459201451259206411450f40c401283e10515501c0707102ca00e1200c5100402c10079150042c51410550741111001d003400b00d082e5403140f0b0266400c0060204103a00180b41005a0010000c00208901210640c1d0000c21082c0c031501c409903211880d02041d01ba00101949400b03600c09103440c5240640c00d12031801504081d201d410000a845080c2c3c41442519100c1c481e180c41c000701800959070400c6401c1003000300e0002680d01070a103d10080c003040000300810010890b1460940083c1e4062188810035540e80d038407a44010010000304840828003403c000004004500000881c0c1c02040024100700c007550302c29110804036444040041300f03c01c08140c0010014104016108045100b000c191002c141c1c42c8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 682186888 1250 682185638 682185649
    0x31b0317010b070215030121060e16170a020604140a2c1312030c0324080708030304080f0f160f021e09010909060e06070c1703070516020a09020414 65
    0x145c22031804100c02c0004029850b0380c510240040398070f40000c9002420542000030045ca1020310703000742805240307240041c104030701c0701940c1a18a0881024115210400e44076551914104001e4209900b00010f200d1030000e0300c13108040d64402040c010071940c880f8030041030180040b00344440d54081c22440301611682580c0150311130103501d11410401000d4542c0706171550141c0a40c014503968510344002070344a90001ca240c00c8420f04004004171301101e01041c00c030314506c248801800350700004900754202208590103181c00c071012608050140c0748405450b8000c4034104401f90003000003014103ca15a010380705640100c1c640e406041c010b00500191500901000a0a140100103a80ca40d615411003e0664030394083c001420049440c003003004083d06501641c2604c10303002000703401e9034031030580d160580c416840d0483c800ca08202982044c0130079100711010840900c4070740e2401074102c1005003014002062038100aa03100038600c12603109402c4400e101070a101d2004150400 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 682188138 1250 682186888 682186909
    0x20c1e0a090906051303051801021015140405160e0d0c1805060a050a09050a0b030106181404030e1002070b1c06050307030c0302060d0603050129030604031b0317010b0702 75
    0x802c00320300110941d646c010585c0c4030342040401e03010710b952030344442c2c0c0e4820852a652079005c04420881024120040460001ccd60f01c46c110303a920801082500f9400c2c20b003d0a805105104200011003038220b00549540018503200c503081404510242c01046001c1d280c04000c00005640098240c9000e01241c1907441c02021503000c4c0d4a500d404000a454504200f4111280100001075540790800700401406004014a41c95801c000c004146000304414038184914080d0742001152078641c80d513141c0c80021540603001c1692040b0010b00c50038803052040c0c2d1014140b050383e4505890340c217010a503400200c0c494250720103202c0f0b0800003030102d214503409000205e004001c5103195a81c0d824010805001c001d0040e000071a00c20f0320554540c105802a5602c44c00a2001541c0806d25186084441c64840c1c450660b940b840185410041041c81c0160340640d1a12100d4408250754800001940030403070400c04900101100d035001661b50034081c0c104020340c80e50301c10580c0108803507400e4 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 682189388 1250 682188138 682188151
    0x30b09040203060a02131503020a021908040909150905160b030f27071d060603040c0306150f0e06030106080601150309140a0b0f070207030201020c1e0a09090605 71
    0x1060400c0c403000d40c0e80054210791103111090050b0b520451126215601d0b01719501c00310711081c40540300c80f004c64154000c0d0114500d20750840d101030400000003003000da0042c0025108100400060015031441d0b004401118040d5075441c204c4100a003008044501e80303c0e0503075498121075141003071070103d90a0700c1c005002c000700c95421030601e186030032006200505042009480d261a109602410400440800d05504184d42146941e02c511030f03810f05182d42034601c0c580511000444624010b030603640240d030404511a046070031913481100030320511070f2400042c01080400180240c018a000b80034040e0309584020328100b200506084da680340d041480b00341c01203001030000c030b1800840c41c540281c5501d00442c00c8845810000c0746c0c0b80b44c980f80c406860088000c1e01d021b1000c01c9130030ba40203031503000c5010503664402c0b17001c03a2100c07071900000b40103810a0900508510f40144020382580f14458005213044444001031550091035205650300364031b0b0b461a4080c07000c81d04c50a0303804074 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 682190638 1250 682189388 682189399
    0x50105181605120a02190504270312111c0c0c02091527150105030112151d0a050106090b15030406060b0a18080706051204080c0319030b 60
    0x800c0880700191254010b81d800380100619014098608001e81c416085d000391203090015100340180d040c4200d540604e038020307070503c2e0528548400c1140f110b00e110620040c540400741d03150340c040f500403800040a6548039291707600401c07213014440c010041120195001c0c2e64a0030300032110300039903a505071440e00b881416042c0c40301584800078429803148642d40c491043c070003981c0c00100207400960392560103000746000340000750643c0c0d1000d4051400700c080120b44900e03800044405200c00d021f5551034602003800b24002800100c91348204d0b5000740b07030116800c0c0c02120003007a403170b0907000b152009603c203580420500400b0300c0789002070316051301d00b8010f01e65440003103650440507000d11340b5031500002c0043c0a00c02e550780726a000e0150000300ca41d07100c8443c000240021059102e9059000411500142c02600000c00d8811602e8603250b0500307062a450310340003404001001641e4404003007002490302c00c8148002c01542c200c0200e500180d10450741c1c02402c170f810f00e0f800c050055 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 682191888 1250 682190638 682190653
    0xc091715060922060f1517120a0f12020c01021c0501060203040509070e03160f1d0a0b01090e0a1407170c2b1410211e05010518 56
    0x31411450310400c070303005421204401807407501360020003803400024002441c000e107560040d2110f20300681202c984502c90180500103009003900da0480708903015060000700002180c1500030300c46400407056604120620b4000c003001d11040c1d80c00042110303140e035400101a00c2c00d03594511060714286900000300000e40c14200c02a40e603209a000365071140da400310008846501c100e520b1081a04040d081e240c103401c074440010351940d21401180316003012010041070346000f103014000001842015899261261186174000300303100c00d4624108090b031070010442c86070b0008020702848022400050200e5101804016070101415000821844d4a1b1120600b51028441c41d00141e150000560700c540f140c1e41c8481010049020880480c01560f000e0584d01d95a4420307080c0b079801071540b036915030310302c0c044c00c1c0482a00e014541008118041c4c00b01400c2d80030091402107842406207210300b680d0750450214010860008482c0ca0f0746810030418103140c01005104196007040007007240d03 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 682193138 1250 682191888 682191901
    0x71109010b120f040809030a0633050d051c2318010e190308030603150f180309120c03010e070605040e0603070314100b0105070f060c0917150609 64
    0xd0307031019001846116254004c40c0621000c00b04480740110b008046501c0c030146072400401030660385400444124501200c00404280d000da4901007001c46c0c80c0644035107040200b08007a91500000c159124803c1224041d4452056068002c0700400703500c3c3d80c00380341144034060070400301c80c50280c1d40e4030780148014a5214410304c8070103010042420601c00c01d002c2e0300041080320f1181c00f8540c1d40d4ac100c0500020512000e2402180a8034055055522090100f0129801d0f40001c0d116941e85a01120008800c00c21203082c0b69100690401682c3c6414800000941000746c030702007400441c1c0064032000040d107000d210320054034a0fa98041c2407100d1601001622500407403103248410320601d40094040d0354188a480c1c0510f0340145104030582d507444241350788508800a41c889035240840804803903005e0000ea0305070302e41c040d82080d0801c45942d940c401138001001c0c00d8051040180004c1341c8100c040c51107040944500005042001040e0307100e0320341c2e02001d80800e0003085c0d02c109010301d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 682194244 1106 682193138 682193167
    0x51e03100c1814100210090320060f150409290c1206063007030b010c051b030a14061005040b031015030602071109010b 53
    0x4082d2240c800322503105940303004070b5880350404402014245400c441502c1482c19910503503011181c2c5402c01000e8a05548080740800c00909001d07805407114070310a580d0305003200c0140a035081210521101c840301070039045404680d4154a5000d0b1182d4105440b80d5a00c00306a01600c884102c104519060010302c043c1509014804641118038942c00e403000e0081c03910180d0500c4e10341a003089100e500c8a000071120a2110400103280c032076206004d0108050301041c0b00131403411030340050840311505030306810720210314505008604001400e60051500100c05036884401c00c0009103004003802000344294035180c44003140e1840443d481d0301480300da44c00b00314610380319010172064501d40c241058160380842e100380207003c4141c00203032803030881c00c07240d8103041e40b0703522120241c0e4008141501c950010301c10411079821f000030b4003070040404144140c1003082d807961100 = true := by decide +kernel

theorem cover : BRFrame.Cov 682014388 682194244 := by
  have h0 := BRFrame.cov_init 682014388
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 682014388 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 682014388 ≤ n) (h2 : n < 682194244) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
