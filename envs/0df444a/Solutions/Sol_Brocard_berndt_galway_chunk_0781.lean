-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0781
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:44:51.134417+00:00
-- url     : https://prove2.me/submissions/7ebdd66d-5622-4e36-bdf8-7458124175ce

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 140287769 ≤ n < 140467625 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 140289019 1250 140287769 140287783
    0xa060e060f0301061e1d0112170f030a1d070302060d0c02010e030d0603030f050c030f0a02010b130e0c0f1008130506041b05030f1b010311130323150a0e011d 69
    0x204045100c0c640d030500401c1ca14100140001800500c0f250007a1a088800c849c202d075143c01e1114841506c1b450a64030810190102d01480c1d02c41400d0032035a41d820340c2c000211a800e49500030403060500741c071403650303800800e9078803030346c100b190749895030503184030343c14030040000d403040040c085011820740c00e02400b040d4460041000b003002c1048a0b190010000c0203540407106000c40055849070100d50403805003000e11070095000400c00052012100654803440c000c24105007514001e0100e10308011035104240c4800350410f042102e100511071107400700c035600c20901d0182a030064010f032102482e09004403421501030b00815111108924440c0a4400514045000701141c50f0088109501c851001c3d030440304084540e01d040c02584e000b81c0115407035050103004c064551515619401d0701c0d80c074038841072700c1640010211000c0803240320150006d0f0b0380c00300000c01d401e01e1210400d210103d40100001da11030b940305126460510300b800380b0611aa13249018080010134419450f051417a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 140290269 1250 140289019 140289059
    0x7021518010f050307030207170d060f080123130818030105010b030705071101030209040228030501031a0403020c10080412081501110307290a060e060f0301061e 71
    0x15101e80341c40782e40c503440411a6806500740c6005170b215815841c03d10701001c440c880a104170580481c03542d4801b00036034803080480740040714542803250364000b43c0e802c80301c21101080c4d0082d0565046d0b21007005100505400440c541e000403542c02064881203016085606404982c41ca01c1c4190b88280c0340034065940541b00200f10326181d400c2146d000741551249120042030100c13003020305c0d10641e000790305484852802038401d40d652465a0450100e9a400420158411469172882001c1600c01c0c4520ba06a0f80c1c4212403000300d01e0301c4400d501410350001c0044085225103190708881c2d460304503a9590000150b1207110184c1014a00031540000014501042211840c1042550301503441404508030081c24441020540007459604510401401500b144208070030f03271000d50444040102c49110121904801b0b40350b41c01c1d00410385c0c82d10300c02d12030100e03120000f00e10f040c5090014000407150040000440b01d41e42e603440c0074040103917000c50514030815141048419400c1403042d60170700e = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 140291519 1250 140290269 140290277
    0x908030916120210020a02091306060b0304030903080315041802030606030f0d110f06010807060813050d0e0d060509010f0e0109050d0806010c0501060801020414030109020a0e0603030702151801 85
    0x20b07090220304003030400516000b80c461800c81d034044c12168000c0c4807000c1065005806001305203402d06509030042c0044004903542864240300041d49003508042d24000c035419552090118599154800340c1c0d000a404443d840c00d1400c4000700f02e80d038911400a0880f004c480c01c117001801401007504021009000500030f410600b480e1524010118614002d00b1407401c2100c3d03400c0d1300541d4245000400102001c04c2c1c81280e002040e61200005c902c0c5c2200ca0950740c41700c060369000345400c0450789107a001000c9030300074812120068003d00d80e1511f148002b074030f008004002901c603101500d2050f2001005c59554420202c00040203011349858001e940000f800001240da88241d911002c4100c8a0104200c4d1004503440d60700c01e850264040da0000000d001c169207941090303000758030510680c507410f14071600040d96402c042c010050026002007503039a01920f0b000415201400050145900d8041001a000141c2e2010008001c8072402d102d032a88030100a168074005900941c00c80e8140 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 140292769 1250 140291519 140291563
    0x20406050d02010c0813080102130806071707081302030a0b0702120f03060409020105070c17150c03150a080a1a010504090804090c031803050c07060302040501021e070909080309 78
    0x260360416140301d07980707610090385c5a40c0c10b00c4210b0071030210600d0300010b020307500014103844895544071002040d680c3d46019031b10700d512040c40a59002c0d08101b1040b0040d101440000c941d54000d42103141e000881d84104800241c507a0300003410321540314400c42d01c8207510000c1c03084072541001110f175400403800c1c0c61490246500510030207400010200ca10950301c5401a0b0f045900c54016500581e6000202c810095101d429101d40b0f5041450b510700903111310485454400d142140050182d03203180341117803030340d25040d54078114542184a400c0e00a80c40800c002a0b0070001c0106a01c0c950242c04807040e0400800d51030342c002c40d8180c0c01240f10724240700d0f000c004114101308890484039206400507031105011000c1d400303403505444452072100c086400b1000c0c03680101c002c00300e400f0b41105540000d9240c0200760100e008500070680142d0064100b2800c4581b0080c030b001c0301980700000c4800c010307555500c2c2000d0700c04143c0201e40d80c034008014041404000c1021040c00d8400d03180344251 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 140294019 1250 140292769 140292773
    0x151701050901081e0c060c0304090c0509210a020307060e01110307020a050607030309150f05070201090c050f011707020a1505010810020d0b090c1903091a090f01020412020406050d 79
    0x2582c13042e54454190040280d01240f511001003221800807070001d8502910b49130f9030440a41c032500309100d8581118101051050701034030800c101c40e180c03d4010603142248030460006070080b4203104400565100d60003a001c056a010001c038402010aa5100040364055800041803ea021003501165500502110b40181d031000666015143c0c02ea030020b850301000c2c10103c015141407180500304149250390558440490b40000b40c01c1c1e4001141409540c584000803402c0302d44100e00548402048103052109142c048040e60700104149880041030414414000c880e41e4182c5013900582e01a90021003000310003007544410003252a410802c0b903141064241c0c90b1040a14400c4810384d000500111b01d1140758420358240740060300040c642e00e070a0345c000f00e29500041c034205440c825040003a83c00c0e03129001d40c0c8205075014002c3d03200510064098041079401500800d154012108103d0b8101f8003440031b4170003484030043c80020b55203940144001c5409541040d80103055507050140 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 140295269 1250 140294019 140294023
    0xf0a05060a0e01050d06080a0308061c0204230a0510080a1703070507051b0405010f080a020402030705070203150115050a0e12071a090415030308040809030715170105090108 76
    0x2000d144a0b08018408001401c0101c540d40314a49003518039a16004001c0341c0c3d0040081c84507503151081c2c0361480c00b0f0711903004109040b4003c4010101d4174a894000300300606068114042d8201095080c40081d55054078800c02940d0448254200903999001c01403440c480098501c010132100014007070040c09910b44019150407007001151418000010a04d0280b03c1e00881d41c42541041c03d460000c00c0c1a030800c8100c80c0070b05080c6114508007070010840415a0005204480a54000b4070310342c541a420300c4060b400003050001400024081c0c0030141e142070041c1001c0055803030210071150b0400e43ca540807004460101801c001c411301c1012000354004020340b40b00131048550000c40102d400803a85800c10750b8010078240b24840b19009074046084d0050310b62180c00703c0c0e09010303c030742c040c040f88904240303440301500003880302d004a070110b014a402881c0e201000380c1550035680e2150114020f80441081120010b12007120b03404210300301403112805003600300c41c00c1c40f80e941350181d81b079 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 140296519 1250 140295269 140295277
    0x1b04090503030a0519060b0d0510080c0d06060e07050c010f0227040e01020c010606090e1005060d0207060c0e10080f180f0a03200d090308070206070b04110f0a0506 72
    0x182d0300d81e66080800c005114043d482d004100b05c40900b80318803600c9007440711040e00400c03055407000b41044041048000701e46040e070182d60100004002802c0340c0420040c2c0b46421000580b400f48c2da821012840c842403078041c2d841525152695507562102404a0b821a08100e064140551060102002c0c2c1e800740f40107480c091240c101d04146a0500100003002022100c3c1c410708503600c0090214412030040d00404200c0340d03d0385030132200c3d03540e900e43c1c0034503d1021500414414500c80041c0954076140002d000d4943c41040c00500303006a940c0d81c1021036400c5603032030000c1240d03002d204805160440e1420704650503403928070428101080d400d9551780010703009400304041101040040300382040314032050102401203803a19040c80c01d0182680305403c100960f52811520f404008040001c1e44011b0603040307039105010103145031541c8400e0742241c4401c90741701c3c404001c0c00000c41e8280d000b49001d1401103402035014a20182005a24000040064025095842d04100c556105001c0d0303 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 140297769 1250 140296519 140296531
    0x6121a0a0603050a060f0f05010f051206041101050f0c07090f050604090b040209070509150405031507020a03050a0309080a030b030f0114040b04030e032a010905060d110d020c1b0409050303 83
    0x4111021071b400454060030030b6169a101c202d151100010f00b100044224408030389064038510812050030030000d444040c00c58002d00030603036840b0030301c10782e512950041041c0f02c1c21101c2c240c101100c0d034200c1420000180d206840d00b80d298a00304440440d41d20400d41c204800316410098021980d40f168200000100042e120340d50100001d407140f4003400450f800404000c1c0003040e10b070141408480319400a0181d64042d00c600040e111809100a4105010302019001441c2c58000c1c2d640845095010b1040c810415403511400b200041506024000351400c41d01c0101d2408907050034185040b20130301000c9400d03810000002241d06040c80001d82298100041e000c1f10f91700d9003004d8800440340e1200310780510a00641011504900300c1c203200c07018000c50030440d01030084c401100c0c080c606000301c981c41041042011003100e000d6001e1080e44850750421424645080030241c12a048510203030155004101c52540c9a0403802506180740b10441e0b04202c020038540318260389000007840c0c = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 140299019 1250 140297769 140297771
    0xe060a0f06050319050f0a170f040b04080123060a03060905030708030408071b06080601050a022a01110303010b090d03020f01090309030b10081002090406121a0a0603050a06 76
    0xd0440800d040741c00c007070080c003005412542088100c58140e440c540343c4242c01d9503940161405007640303243c0807401c500342c10f8004c180415000c0e26060701c43c0c1594030150000c081010204000102074150350f000c4e04c0142000000011103180740514160222500641c1403120500c000c01c102080e500e210b03600083d2500054000341c4860b0519065182d4410f03400050312007100401004200045140141a054810304900d4208000442404031140c000e00904000c114100001481544218040c094904140c812249004c2c400001c2c2001c05401c01d00382c5c800710034844249191940c014100304120b074403881c000c0d8507644c900914a5081d001d4988000d200341d1000b01000705061003086103054034200070740201b220b4240ca01d005051180280b01c00c0740d4074400c400001d1007008809800030308032164040580144100300c00d078440254000402903034010381e10b01e8045100031301c003215043d040c0d10940e01c0307145000c012800c1040c2410b0040600710601c0c1003003401d2000030b030045800050964410703c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 140300269 1250 140299019 140299031
    0x9091c0302040509040b18030a05030402091e04050705042a030b1807050316080405101d151005060310180b0405040c2903130c030804030b0a0506040e060a 68
    0x18048010344079603030100e54011041300501090044840c10580203c06a402403043c0c52041426545c0303c4c058490040d01040c0140001000b50030300c0c03821140c2c068183c0141c2040d550780c14907482007480b81070f00e040c1c92541c4840818841424244200185a20390100300f00c100c0d03140b0541d10000c10f02400c0d42d9002c154550000d84c4194442c861081c684481480012541785018007000308560000c683c420104483c10308450030450098504030300035a04440070701034010380164410094050280c2c0006401481e02a0a81c0000c05001c2c1d4000022001141c4400d81480b420707800b4428156000180320b200100148141008403240a40454000585590902014400183c01450f8003601d45801509100403c020407410f0040c54017a40e448036030410701c2c600034003042c40c0081e01c0c0c6070024103201002c1001c034402c40700170301d10180d50510444a481213281c49980b07640d4990450340c000c48070501c0420a008203010036029503584581c0940d0104081e61026a41d82d80d00c0001070403c1c202e050344c0320 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 140301519 1250 140300269 140300323
    0xc03090b06150f0c01050a0b0d02090a3b0c030607021507090506071505070503100b0717070503040e090c0d1509051b01030506060304020a15031503030c110909 70
    0x66074921040384000fa5100d0800030382c0d06000e0035048500900c0c0c980307030821868040c681902d0700c02100360060310a580300c0d503960000304020401c2c0d0785d0251740c04110f01c0310111030003a0700c0c5003400210010f204804408004281d01860f1075006080e0038403a40102c010071805541c002512090344404004c1e40c846611400420b688010142d005560050f1000035010184103200c01c036020070f002e0820007000070383d80e042c600b143c1c240019a100b00741242828010020018410050102c0030300900c141c070440d006e40440056181e1010744200d405400200d002c00880c00150340d0786601c17854180c0903182120f4414000b440391042d44ea00140040038040c844005c04605600c0400301580c82011140d412144030814050300d07089022160002e4240700002e4003a01f02002541d0085902402c00c0414a040c80b4a21342a618520144010550b50304075008065980b1060200103501a882d90303501603829003414100d080380440158001e004000910140031400511005030104441e50701d5a461284 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 140302769 1250 140301519 140301559
    0x80a06030b0403080105091501021c0e0d1a0114060a05031512010f060807121403130f0e010803090f09090a02060d06050405060a0803040312050c0a0b0a0c03090b06 72
    0x10340014000c1604401080201a04008114161601201c1000d03072a6200a9803c003d10715010406006812500342d40520840342800c500e400209400c209450300071000225440381c205540a440c9210311b003c0044c01480c504203680e0142005201122034621000e021649522400d011501000303000000200c21000c01c840c11083c3d0f280c0100101c070b811034900a03040c06070104001c100c60031490070000160350000001ca0310112014013081c24032520702c0ea1211905504005100003130b41c0030400100721240305000010014080c0105011011420203a403840a668140c021041552003003209400070b503190030908440403002c4400b006943d481c0d8109604042e62480005e40009011680e1440018560440400c0d1001680d0800c00c40c2e45150800414005610540d000ea8000308024000304041620306440380200c1d040462401030703200d208518204111030180c51096902d402c0c0b0411952502440d08103100b145030620200031207490302906450043c03d110300c0b4088000b5014006020 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 140304019 1250 140302769 140302781
    0x923040c08071b02031e0f0607050a080c040501050304060903020102041226120109022209020307120b030d081b0c070f0906030b24030106120606090e0a03080a 70
    0x250003841000402500540308403000d841010200380c283c03240f55a5404120203e000c0e07a42c005004102d0f80118801c82020100114440340300b5000c0c41e407410051100130800c41d40200d22035030328590f032584140750092500e503002d031120742200c104000400060303038000c0589800a4100c034000035003120624060380284602e40c004651425410081c0f82170140c0060740ba05040c10040e40742c01e85170500100e02c07400b44510000920110700314801409400503d601421944800c0b070306d42240d144402d5070b0503c020074aa80314a030380c250000200002640e200981c01180642d00c01e081c0044e6191000003601c904a112480080200d80c0c40003034401c4030050351403044d00e500e40320f002d540c44c00c240e94210348500040c0100122220301c08000106120144210381c03c490b041003400c0f980e5240d4035000941d25404446c42c1000c40102c003484910b5035420711449004080344501d038072900b5100d181c950155030055111603c440c1c6054500500c0d200045aaa5103003a403600d8108107070344d1155072481c01018 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 140305269 1250 140304019 140304089
    0xf08010b03060f0d12050403050114091e121314030d0509060a0c170304141b1c1208220b07030b0d0605090d030e190b07020f120306040c0203030709 65
    0x11440084401646c000d8020420340e8000c3c4000e01480040040e041d00c440002d41d28455113334401054040c4201485443c05c0a100c4035005540c484058800c5d071910703e03005078841998000202c1000c0015982c03540030300e030307903100d00368007030544400c104401500c4c1c0d0248000560040c9000906107900c0d500c00c150030420941d00105044049100781c038dc0120390b41085604a883c10942102803440c14400950b4920fa155013445200c10112007000307004201603401743c1c28030000103601d151000601c41c1c890201151495550b004c103c0d203818403451040414061504c00c0c03100ca40c81402c004208110304195006081c2c0c02d000c0f43e1400c03185c02040d8171002200d009024146000b0501981450215088280309002e5806020640c001105039882c0c4d075080c120200c584603d04c0d41100043c2c03210800d26400341650068030b00040c5800c842e5414000180001c041c4848000104002c1d0f00d800e1055a440d5420b5100860541ca1308030300241c8103a00b00d0107414a0041e00e68040c1a01d40005c806081c800c00c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 140306519 1250 140305269 140305283
    0x2d09190504050d0908070b04090f090b040506070305070507020105030c0903070807060309150204150c05010b0409030306030b0c120106030e0a0213050601120c12020304060207210f08010b03060f0d 86
    0x86080c2c02c0c0035440d00c09020038240000d254180000300b440d000640e10040e500d815440794603003031030180b50100078a08031401403142500c1d5528100402e4001000d10302c214050740c0a0002071429400040444030011308030000d0000c10300c02d020260740e202e02940d07070144021543c00c5d60f402614001074030701000c0b5805851203204400e400b14a00d079241d0084910b407071150007400280c0e0012183c0314143c2c00b4a004400b149900c0982e052030252007450100303100c5001d0000051f1f510b000c0004030f004d6408891060300400c0e21400101308200d075118402d07a00c4000c0904050501e500141034203d80401071041d001059110501d0001921040c84a000881c3e402044407180540900520b00685000c07035015020981e0810700711359602007402079900c0902245d980741c803a031a0100507c8001c0d00040c100b5100c45509125a00004e145e001028035402c0d00c001d404602010026001812141107003038a50405c400d00004121602c0d0180c01c0d03d400c0340d02140d00c00d680d9540c98002c00c42d0880700d07020180000c = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 140307769 1250 140306519 140306521
    0x90e12160c081e0304060e04020304020d0804080309030c040b030606010c03270e07020d0f050714070902030103140c0f06070218240402090303030109050408070506040602092d091905 80
    0x250300080f4110200f03402c0c0d07040c980500f03042185980b41c0c0520710940000c901200c481d0300f00c6180035402075070b100b440100004100c0000d178503000c0c1140c1158003c12003d0b80002000c400707a24040084401001c030803141403040c2d075519400309448100182c2090306010070811300800701400b170300c1c0c2102c900031400d02000d0900c000e1a4547c5041c4828410070100314200008608039920103e80303142035060325240e40706200c01082040300d003503103e2203080e600c5000100492a83d40382c01e01c496001041104000b603280c2d41141010013403813a03240c1001100741e01c00380c4c440215031203048041c1c1e42844202c4074175884011a0003c5020210186c2c0040e5000c03a40f0310401c0f0a10380030055002400200071a00428075524106100c100e101d40001590300d80d00501c01080044450303042030380c0c0288142c03106070400200d503031445c1ca800d106981c211000307034000c1942d0545042c40d15091034400300303007811310280300c95035035400d0030310850018600c1c06004241c0000b06404054803510039481e81740c82041100e = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 140309019 1250 140307769 140307779
    0x402030c0714030702010816091a0c010e01090501140112060b0d0602030f0f070c080301090f020403050316110a0501050a0305040804080a0c05100e03030a0c0213020a1206090e12160c 80
    0x2280e01a680c200d002c1001040070800700e10000c22314000b80c11182d01c4440e8054180a22007091540d07910200000b00300400c0313410202c0b04c00f0301030100c04000315070011840500300d10308142503540306007502a50307505200040051075a810030a020b8140c04c00f80c00100c0a560314041000030780c103418042d00c0640004203000c42201c22066480c403a48050403104840d869801003100d40710f03c1064042c01c031001c1800144080c44540d4880c40405000304801403134159280e5480c0c0c11900401d054144241e82070601200b44a43e0480c40c041c03408044440381e1015017031500103451b1340109981001059503d00002d002c1000c03143c12100940464130880e80138092910344080001954002d03e0302400080321803a40c494055400c002c1c3c020b000034055420300b009568100d8a80f01c0a0707405a0b808500c0740c04c0f90b00d5104491008100ca2004c0c2c1da108409459460150310540d18070f58481c3e40410b20f410740d50756100c40041000c1c0e4852007510031071aa0740210a00300c80e1082e0401a000e00803e14101000070 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 140310269 1250 140309019 140309023
    0x30412050a02040b040203060d0201081305010e0706090504020f07060b15030901090201020f0c09180a0c0906090b090702030d150b0307020a03110a020306070807050d0e01290f0402030c0714 83
    0x400e82c8215002e010042e014020b00051740002d6420503000700003502180010342c020440c0304c6d03000060301d00301c5004003070545800d17007521200d000c40103040c2c11902c000d00c15181c0c00525a400341a0948040d4501500880040c00740d200f1490083c7c0791035914150017800b9520340503400001400e045100d502c900300303110454020042000102e000d07200301c295040004d14040344291112400900c242d8880d580d101045400c03d20f00ca05100341d80c041c2c182d102d0005017821304484042c1071010b03000900281040170b2407049984c00343d206071142c40c40c4400c218290794000121024028413882c045004691824550703504909904141401c030000300810542130340c0012190880c501903a258000f4400d0002143d403034400281b0081e4060300070000003000507015078181600076001d85080c51920040e40d02510440e90301e1900030303100340d45841d0f03410000e4030540700c444ca412a042000304950500440058011200202c80500030368000c00042e001c54480c109840a9540141c045182088a00a016 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 140311519 1250 140310269 140310283
    0x20f0f0609100e07050f01021c03140a0203041515050402040e0604140412031d1608010501090c0c2d0b04020a0902040b070204150803040f03170906041703041205 71
    0x800e581c0b10308140c01c0341001d01401402000c0c1c0c2d9510103030100c0c1d400c20050100f4089140c01240c190710403031100f8505c0f458a080c0c0c2c044641013a540c005440a44860308500200000d802e1007000d50041c003c0c0004200c4441041c140c2610440000980543c406107a584110b642c2d8081c44d482440450009072039552042e10902c240001c8404106a400c0c554070140c02000542e00540356282c3c5100d0000700c0750080e4088420f8580701c8210300070516080560503c0c0c64150360142901190020003009031810900420340074000441c001d00c4101c95000e0010101400c6c200050030040304032a030340000c8100b140f00c0181d00c00c51501d00741c0010b501810400701d1440165812400b07559000b9000441203558420350b419103100c031100d14079121294080202030492009036068502c003020000604e180c042008000a154210b40c010042e0b1650070905843d1a00341d821556802c800c1290032080c0d41d03444d040f0340035594500207200c4000601c0c1c0c165403450049800102c468060740025a06101e0005225 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 140312769 1250 140311519 140311531
    0x50c0a08010506030f0a0c060305100308040602010c021e0d0e0d17071103030a05031f0b0309100b03010606020607050a1704110f010f08060f0102010f0203040b01150801051e01020f0f06 81
    0x22201d08198810650391074110074400b9061f904114410702c1035520940040740c000d8001c40709000616169103404106034055400400907070766511080c403040790141710008a48012050000003200c011a840307403640524070122003040b04e840060b0034695245420120500d80111880c4070103507a0054900349030307101d8a4155190030341650380348420302d0008111500f150350f41d41c4060a41e10b4595032100045608400b03d6000f411080d000b207400502403010354400c1071400d004203180143e104240003203441205880b03010782d0502405118541c0c000030703051f410020602c0d016644000e1030b2000c442c03550100314800c1340918100180002e0103011005c500358020116403c0c1030596880c1c005403668107a5220a0340401c80c1100012618940981c0c082d0100364103000114400560340e40800c200d0f4401c42c0e003203615120440051207001070304902e8105071212418000c0c07185d410b081c00906400400d2a581c02c01c10803001100740c160744240b064901080e985030403619081d0884200c5c5440301002c03544 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 140314019 1250 140312769 140312773
    0x9050709090204080712060b09090c15040f050906030f0604081306030c0807050c010902060d050405060c070b0402060304021512070e0a03081222120e120d0804050c0a0801050603 78
    0x1040001e01c610880b800ca80c01c2c81c00030304072985060f4807140505068001594000d9941402d04426150302c94014814007948001d84aa80000000c10080c010706048546402806010070b0014944030311801d826608110b4089186540f10303000a45001850520017881d801210240001c0008950203415400b0390342c0940402036484490880c00c5841509040c4005200703100800c00c507900480081c8004005140045201203068020800d2644281c068850190341ca038100000e224040c00903d4002c81c80c513200740d1516101d40c81c0d0351910746c409040684039280000c04074045640301280015581000a0440e458241c2c205416040f0441102c0020101d40312824401c4240340500003801600d134030050103801c1c2241d40440021002d030041030880c581441d00500c1d002c5030401e10f0354803030661080082d070844200604009150003d80341085000d04542c0000803152030001c1420142d007449480c2c80103244d03035181032a61130b000720424800d4005101480c003140078401074000034440c40050302 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 140315269 1250 140314019 140314037
    0xf190b0d0c0806030a0b07020f010606050d0f0203040308040809130603060902040501051c08070809030a0c080d080705040e1023040b0a0506190504031a0411040501030b01120302011104090507 84
    0x1076442c1142228100e9040d009040c02800003030b82c4540c4580c1007549403040700c0402900d031102c5400c4440d6074110001280c1c000c50060300d205174602541032040f45040d403d60035410684c1e0054140c0e0f0000d0002040c244001c03c05030025155201d80174004842d806050101954130b0420800608001c07405174092810000003191a0034000007002a0840554207d0032888660b01d400c0ca450f0013821003100e20b180c08010190180da400c10030300c003030140900c80c041d1a0500c0c154000b850320311400c2d5850f00b440401810406080c0d000300030344040320f001d40c051002640c0e0301c005103803002c0000d8101680880000d503441c00382040ca01c0c41341145100617501005403940c00c9003004030a44840c4a01940020200802d05840e480c041c00203081c00101e0030401e080c40c3d02ca946801d64001d0100081030718580107030402040c4488191281101c1c0e1080e103040101754119101c0000035441400340080405059800c0b8082500c00d6000307071010005a4445600d0741c0d2a44141d0b0301408041c0c032440c00040d080301c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 140316519 1250 140315269 140315291
    0xf0307061d06041203110d0603120215010b030a090206310b0c030f0a090e131a070207050411120f04020307060216150c080c070e0901060503060103020f190b0d 70
    0x82c034140a190070040090800e40c5441048000c5e03c003803095800c040e10140101c0d510700c3d006002d10380c041c51003010a4080c0522050000340303402c1d0302a11850400a4a00040126528820407a070304032820340804242000d490020909c0d034806c414102640d0404d0700c06880c10728000c50320300c16160b400e12622a11696076402d4003669800785644004113034208015044459071828020008000350b401d042d07542603a00e1480200d240000c403110150f606200072070400b040010780980710080f0041c44c00040078242a000250741c0c400728011540241d0745c031244015410300d85815581c2842410329000c1d414680240010100542610100d002c0d00c5141c0c0c001c6181800880c078458610344603c070201d0054a40800801d4402081040905020310481d807080030556a400900610002c2c8008020241c5008064144103100428901060b490924180410303500401c03101d0440c0c2d0104c0304400040c0400c0e00140d09001907040001d10391082e0140010706111000282130100030840c0c00700b14042100c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 140317769 1250 140316519 140316523
    0x6050111030720030109020a0803070c09050f1803090d03020a060c0912060c030209060a0f020607021903181d0108010c050711010c050a0813050a050d0c05120f0307061d 74
    0xe80300410508643c855045a44182c1882c03402c80d4500400110707210513550007058050f10103400004c26908002001014440d03000e216400030000044100324030701d44911402070a02001c3c008840c00040104076070761480d01002954180040101030ba0103081c89494080e5541c10417900440b0302d1810520369070b40b01c90182d08903204664580c130702c6110208540c1d80307410090240c84c03024400e0503400d10400300c1948038034000d800c0c1c82407151034407048420100006490801c0041401c0c0440d404500c11207031100d001004803039905d03414101900300585121142c414141c0981000001d91a00104001d8000c54500e0b070354100c408580080142c012004d00032100e5115072607024040031158414088039502c1180180380321800340c419a080708540c0c2e503442600c1d81c000c0021903812171041c9000c0c0441c2c07506007180303002086c04803040e805400306659910070200140c45194415044100a110310301000c0c00003151120140094a40d60b0000d890404010001c041281000c2904078105620030900 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 140319019 1250 140317769 140317777
    0x90708030307051e04030b04021806010509040b01140309032101150c030216080d090b0c060a090c03060504030201020307030608030a0e0910030b09030301060806100c330605011103 79
    0x406028500d50354035018280c5083d4040360784c4001428444d80c000c0100030703500014001847c03056400702001d0a15004000c106030502800301041c000120500030300381c0c1c000303088414507641500c010510035600e40060740c0b10f00d01070008061203900041001810301c404401000d0294a00c0c80d80904041c0c08501442e002d00700f40908030030140884040c0d40b60354003c00001d00c8140c401e1048840407911072440d5400d0f81a20fa002d18031030b40c00001450300080c0c0124801002d8034240c2001410044019100c0e0303075540b80504542039480e603c51983e000d0000490484002d1a0030680910071030409180082c000c1d070046a5080000385002000304483c10302104603407019005a4070307a26107960768010012104000f0b0000d903c0e03010a0300d00000018150107000380b1034500079002c1d648035171401101524140d0020982c610490612590150b0a070708601320b404416080219240b803411140692a1504000d44c400c6401c50580c00b40541e4000307a640062083c2c4100b07071385420300708a030820050340d2402 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 140320269 1250 140319019 140319029
    0x1504020903070315200f181002070f051e13110f0403060b0f090406110c011107060b060403080301030605070e0a030b0601020f0303070f08150411121e0414100501060c03080907 77
    0x80104030300306d060f40050001d030208006d00d4082d403030503082503000a542c0c0210408403401580110340100700c8011044101e1008007410348030244d201500b20304e42d00e02c071400360483d20300c6048a40302c8001e0058442c0e00500c43c501c100001155038090200820750241c00c05e200071210242090101c2141d802c001040d0715003404040e101c4003aa0700d4640e00d0201074007400388591100b1006018803610200d00340141600f008100d04000c2d0b55207080c2c10407400351002040003502850040204000090702081143d0440750803010004054540680c2101d62400300c6080c3c0d44e109030095000700c2885052200140602e80903022916a8840141642e8032804221084404180d03652030450403603000701e002c3c1e80d00005a414070000f2440090014003207640c8501c4001103200b0104407013001e41c4246503283d0700309200684100007072000084460010300020401003010342081e010342d0282508101c0410015190002030004d9a11402e0040141aa2140941c0055140008290404008039900c41650 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 140321519 1250 140320269 140320331
    0x804060e0c10080a09020303131404090c0303051602040f0c2c01031e110a08010b130b0714070803180f1005031008030a031b02030a02061504020903070315 68
    0x582c0c90341007030b9040c40c0020002040c09484d11940c90041c0e400b8002040c2d00d903030a140700e83e182809c010b601d0214003d03480f19036004514008640d0007180a4100315021281d05103070643e502e041c6080305890048610748004c2d0001c2c1020706000f880034080d0000c05000070160b4031100c2da90f401c040d2401b0000c10340341300c900300e131500c0c15121491544260001101a5000e00e031213841e40c017129a51904444589500b210000c00100b403c90403940e2200e00b01c0d00401d049a403040c05e050038580909144a580c0c0301d4040506000a021410401d0a01032400c201d13075403005072051701d0790725081c0681342d502001c020303003010b424102001c1c128602a2850110303c4070281c0b1445101703036601c605a503e5070000c1e000065480c0740440c0051440350800081c402c03c025030340e003c00c060034400801c8080b00004a070044c09e64005004260140c0e0b400a803240d0309c010516451944914507070003240c001d104204180f5054051b1078404001d0008003101d6000059031410204044035095080010f0440080f007510240 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 140322769 1250 140321519 140321539
    0x9050108150a1e0203060103090503030903040510020604030504090b04290906151801201f0515010807110102160c080c031f0f180c0f060e0409050102070b070804060e0c 74
    0x4001c3c56030203140c0c00071060400154100c2c185d10b645140d40c004581c0c803482ca5100040034481c07414060752001c14420280010005410640e84c05803d501540c0a148500da0b502c008c1140a5542c5410104005150002d40001d04480a20140c00409040c903054001d045080200c0c00c03a00300720164101d402c81100b0305030b0800041c03100401c0e280c0c03e200201410060b052500c20170212020070381c0c082c0e00d1403240040503c0000d140d144044004405112401903240c01d04026008030105030400700c03030741c007403900300203e994016090701d500d6101c9940c603519600c00b0440000300403060740c0e0310007624018a1035094035642c03960415611580800b07219015085006144c085450507821201504840b103808100d1605210031103040711911401404001c0c80c040c9600d0034454643e0110001e880303240110340c24035040030406002a101e10051a00880d9503e01c900c0510000b0350558000c25480801d1403898142031000600c241015502550120310f00082c1c1d040340400000c08818004000d0512100 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 140324019 1250 140322769 140322821
    0xc01020c010e040e010f02130e070305160f0215151f02120d0207050a03050a080a0b010e100504030516081203072f060106030c1205220c09050108150a 66
    0x24200081c0340341599900d854940c017a5400d9400a414417100c005803c08101d858000341d82c002741d00203010001414072f024148a85412041c1140d50380941c0d03407c0140208402140492601d0040c03485400340d801840140181c0045003400c1c01803003282202e100704036610a004a40b1000410034403540540d2140d20150b034428004806041c10b0020000018240061511154240400c903001100050700008007a1001038005c90100e402200c400020020b03c00b0400018060f001c0318415103101e070708182000c10190744039034100c801659104c001e940341002c103100052214007048c09211001d000d15194007000603200d009884c4110740c42c0e503400d20482c400c0840c84105004507410510421403071190a203000c2c108000490080100303540005a00708000001403584200b00706954402d0b0608040c405422040a0040f00361014040d0105100100d0318002d1a1034550758410200315042ca80001450400403844c4c44509001034a0159180e461011040890350f500d00c000c22462030b10511041 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 140325269 1250 140324019 140324021
    0x303060901090e0f1b010801090b090705030a090602070c050f09040503220801021c05010f060e0906040e0a030c03120204270b0402040b1801020c01050f030603011103010303020604050c01020c010e04 87
    0x1101031007004d46510102900101e414402d1034410306130000e0444054440340d5a01212160040000c00c2d07080024007100f2001500c6c10801410403810082c00bc0041501100607a000c411141d0b404401190f50720cc0314582803123200710300d10416204081039960790400d8109000f030345228662201c040d620b001000c2403040c0641d41003030020127203014845400705181e1000d100401c01c2008940c21181000d00001d003201c16220141c10440d400c41c0000c50421015420044213001e14900701c40034000c0d0b40e102c10206000f001e03412041d045522030203800300d0a154010030315598480c00380d91039044618480e031100060388504d118230039480503038803100c01240f18000c2c0805a4003072038120102d1103030700000002d4240e81094100010880000031681d4030030b01c030b00c0050003804c202030015001003040342c0c0028010340103091095150510020000d0320550702944484101601210300c151256113a0030001c4d9100c904031000c07603040c8503c00400410358000588a541c000050791000082500b50007400 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 140326519 1250 140325269 140325281
    0x7020102210409060e0a05010b19142a060f060d0b0403020708101a040606020309010c0804030b01060e04050915131a0106020a02102d050c0a1103010e030306090109 72
    0x51000d10307060002180c01145402640d0082440c0c02c0c0507405801c01c000c4802c12100182c0c031940003a2400c010b120b42d49501c0741d800034001911400c0c0742d0380c800041459010548a549008104030000041e0f420003219500c1800543c083c2201c100d40d00d65451385c1e0035002c500d800303032003055000100340005000a104510b001c3d501c43d11030702c183ea686c1d59990088500c0c04c800822544007a079256220320940c5501955807000e40e80d8103c03801d00c902450400080e40780d20856807072504024008150100748800708049500440e030000c0903803040d6a6614005145440100509104a0604c400f15181c03860004482c082403450b80a00000c41e01e802c5901a004650704100302c0d10007044c3c4000800f4241c80c050458000c100d00d402805102d01e03184100045400d0410701c020500035203006511281700d00e19844090460041501804c15803004001d03252802a0100c1d2a818400c3c80c803410308100341c10380302c032020304d0007940240900d640d030b0f508154a81c0411170720303250030510301c038010058101c0c0c070f8100c5 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 140327769 1250 140326519 140326573
    0x3010609091a0a020c060115030227010e0102030319111c06051305040201090603020a030605042408070e0a020714031602030610030b13020f181603110d050601050d1503021507020102 80
    0x5103001d0315606101c2078240e010520383d44c080003007001c1d0b0f10bc95030411400a64903c092016500e10310342000c8014440b8000c1d6480303103035103a4407824150403440c920200d0f400b480b1740c4c040805240c0c080d140d40c0c0c000341095001d5540107044804550041080b80d000d8680681e505848904002c1d0404200b01c0007074000c00c0c601c80070507032111340029a039200c5100d8480d410300c910030a0302e01c102465424407480ba20f1540820042d0780521410041ea40386540420b810402810300503944102a04140070000f4043c091038400380070014400ca2a900c03242004141c4501c01e40503aa210f42d102ca100101e800c96600c800780080c102100002c0c0700b15020144600d1086c401003000d11544062404100c240a440710401e10101c9424280b11091080f1000400d42040301d1605000170381404040a460b40030343c0c40d0b0700000c01d03200e90105426a011380d0684645908141040080811041000303000c42018802a40107d442c0880d540c3c2d0010803a049559a40d01a0010940b074594924448845030300d4144c0e0f = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 140329019 1250 140327769 140327771
    0xd02030307020f19060207031202070324090614090706050c0a02061b010e0a110d171c0e01020d05010b0307050301150201060b03160f090e01090b03010609091a0a020c06011503 77
    0x12001310000c624002c00064089640205405415480e10f80c541c0c007107040359a800e545c044c1c4800c1000031440203203183c04420301101d402d41c00c86165070348401b0f0105948024401802e118070440301d0750429000c42e200752600012100d80c1031303641c0d6040d50b07280b04a024550b0329400038035080d4050300703001f0020f003c06507038a25182400080b100485084503107071031645140360003059401081c40110311004007914001c0303403c4d000303560080c1e5402c0d02a2031416030140c007103900401c0122a900300c0706204118034000d04401d0140200301c0c489203000b90301c8038015404e66880c041c0041240454081960b11688554642e1451340c0d080101030340700c1d81707d2043c040e021507403104008030703036080c000c0e014502810b07640ea003a5100402d02c103800303021090071212079002c01038000e1041010350400c454880c110380313000c0360008040d5070084c00b190160120f90401001c55042590080403c5070040117125030b00c00500e0030103c0c58583c03000750410781c422043c40ca141c41c0d10450052082003a4190514049607660070 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 140330269 1250 140329019 140329039
    0x103090c050306070818010c090501030b040213140312090d020f0307031205210906070827151b09010f051210050103050108030702090f13150e0c0d02030307020f 71
    0x40e14181e004c407540400508080107010004440c3c1841d80da1190780b500084c0000101004000c0501903680304507810592150f00c138211580781d55040703a400f21090925284420784490742d100008800515090180c817a81500c0003c80141c0b10540c0c2c981880144108081100c540800c042d005a40840b03503854000e09c4800000a07050307200b60310080010780c0b90652540c0d408000c3c4040c104c504540618141c03140c50800c40109004641e00d0f0307000407103080104007520740c9108462006056181840c80002a80004142540000d42c070000802404003201d1a5540c035245440300c1c9040903000c445c010424070105034658082d50200010f07405030310700f0700c0c280694010002000e43c41520500d00800d8403810030720282d45d0500801380075207543c030025840c180180c0c0c003040d07070010000d107910720744040030000c248a40c074080103100800d600300030070f010030382c51103079034840206401002e80103544601c0c0703002c66007400d01c110038a0080d90001e000d5410544c1039000d01c0300b5000b4140c0f240d81d100c07075000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 140331519 1250 140330269 140330279
    0x50d0e0a05100203040b1c0f05010501120f110d0902040501084303150e190204111605070807150801030b250f08010e040b06060c010b0301090b0402010813030504050103090c 76
    0xa400c0c0a91f00202d1b400842074290414801c1310071500c0450300c02e606144c01846540d8008404c0b03001c040032400001012603581d00180020107405440030824440051202d41036000b0f50040005140200c60801c0142da03a42c10182c2e0300e55800503a030080a464201032020070300c0c10a90707680000441c04114403440308a08010b4651900f0b60002c4400c8141080f0201046806220300a405010074009004101d400c3c505000d8041001030000d00c95030700c6907141a02e00e54210150340c0b41250441014000203a10b1400688426050289110314410b9400003d0f08018050500d03103003c9040d1a106056400c5440d80245190b000f01902d40b0360503001d44889092009860310b000d141c4150342d03020503004444100038501e80040e8010360401f8001d10501004c42c03490340185070448811140e0550729000c4141c0c1c18007400c1d400100d01d0303055182c64076030380620001d4401d5902c103d100342e0700c0070200da907403004880c0310112908004c0c0c0040e0003413005101e194000c3e4003010b200382c000c032250b10b42d83c0e0359a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 140332769 1250 140331519 140331539
    0x3051602040504150c080603030414060408060720010203070509060304030c0210120605010801240917011a030f2508060a1505010906081303090801051003050d0e0a0510020304 77
    0xf641d0031621103c85030042d080c0e4803034510403407a0304452490441c40720b007840d00010b03680c0d000d9030050801895402024051561701d0b001111300610140c4151002d52504510181908840000600030380a0704841e081e03510b176040c401c0300d03c2045161501c60802c1414024881f50303400c0100101d040c0f10010503c4000741e0340700c2900011040140d034508032041b20303115103131054444952240f81401801e400511400c402514010780440f004c4041210038000f165049441c460780d46d210300000100d00b03c214043d100306421034494409292000200d210341c03401803591310522a0b100000e1034002d420b140c6840014402942201d220f6050185a03ca07221218a4200541643c0d200e542698070301c1d422543d140d8403180000140002d091540d6414900385016014140041c10400380701c10000502d02094002e15551014044031002001545800a50b014004c0310902043c2c40034841d0814060400348036001070b090036900600348002013444e000908c4000b00b4a040c0d0901940004d1001240035006 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 140334019 1250 140332769 140332771
    0x11040f2102120c10030c050f071109010b0c0c0105030106051204060209130b09060303040303080f0a061a091315050904080f0a080f01092d0b09010602070905010807030c03030516020405 81
    0x181c5014100034a043c408100b103a500074a03001c010305003020014000140c104003510084207004800b15940c0c03e075840d00001e00c0896040881e444a000c80000c1207140c0204017030554400860212001000b9003001034420780024403a04000a004101c5d510300e0440b40018960481d201e15800760408240d1320000741400d01c41203a4050042e62143c40c5061440e01e5002e042d00701406a0144d03103080c2c19600c00601c0120004e1555954000d120007081000c20198001f200500140b2109254015051001e66040d448016100d104442c4488441c3e000d01d098407408111041001c200486181707404180504004028015500c81c4014071082011003058402481c002c4455034501e4040e20300325100b5001c810301078106c81c05480c42d00000c0520110b03440b412041001400c08100714509143c0b8030070001d0300300301841ca500314030711400010b01281c00140c03903030a0341e459200c18011682c80d4042165904d00520000c0e01c1c0041098040001c20300034002440440d200715400441a00c00d9000318040d900 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 140335269 1250 140334019 140334049
    0x6080615220f0e0c06070206121e010303030c020c03010c120e031c060501080901021201030b0c0913050a0e0a0206090402030c0d060f050f030312070e01030905120306010311040f2102 80
    0x5254030050000d080c1c140301520a55130b08842c11810404190049142c902914070025146070200b00461114213a04030501e0602511303825460b490341e181c2c80c000300a004245221009403040710707101310a03403406000d04100c801ca43e0380e03082c1c00f00052012410150640c50700da10110b0100300400c3c4d030b02c0b4645040d5400c0014404001140351071601c4001011404020240d01c0c0d00c7c1d1043c410700c64041d40007440a0f0440b0341150080003580c49120a10010f4401c1c20b22082d0301a414011324250103c81390040d074402c1c95030b2a0100881c54507040b4550701d4804500c002507100e03404001080c0c1c249007a03800340d0b40202201134007508100d84a0361640c2110180d03080401c20b507001250404c40e51615105c4102d01c55001c0c1c014501b4103208030100410254041c00800621004c0000220315074841d510100c00190030404503842e800481107051a61307481651250f0000b0308001c000900080300b1030840e81203a05e66000054200e203040c8010305100d5061007008441e01d05501480050f030798851414007018 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 140336519 1250 140335269 140335271
    0x6030c02151e0108240c04050d060f0c0c1e0f26040602030403060b121507020c031902030d03140708060103061706150301060f0b0d09020307080304060306080615220f 73
    0x2007001c042900c45015001d1701003510040841000417003a81082954100c400070344401c50309020904d0894060680d29980f4084a403038001d40d01e000c240c0c02002202114000d065201000000000c031505442180b44003030030036123400300c1030000607198110044240321920ba43c1c2403200d101803003511b1558003030382c0042c0050307102140c02e00600c4024424812075034401c680b890048007803291240c2e11400c00110108241c0010b00000714004d00a2081040e00c420080a403100c49003102130440000c0b050902c00d81c001d1007241c603244040780c040d02ca0b100e641045024841540c0d40e032840c0803950b620005007080d040685844c400203c0703084854022800d050014042c00351450031b140c2040c200d007598a00c161082e810310708200074030301301d241c80031f010340e00400380d2203a5440100440c00060042e03100e000703400d0b1080c640f000030720440100103001518603d5505020665482c0002c1d40d46031030a990072a022002c02103442c00c01c1ca040015500d641d2405100c290b800740f004254201159081a221413002e = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 140337769 1250 140336519 140336533
    0x21005040801060e1005040902010c0c18060e090a0209040c180b03102702040603020604060e09070207150509011e090510080c0703270305010f050106030c02151e0108 73
    0x946028050100541500e89130f41015140030300b200c3c5400c0d020b41c42070502483e41c46080100b1341e446115101740c6990000348000c0d0607030303540070100e00641c450944088203a01d4100b001c10103545900413207001d03501c005c000b40311144150702002031340d0a011308110b42500d01c0100010f40380c3c00702c424004503d140d0313100000304522584141420024030440f0100594034101c1e0014401284034030420340e40688011020030540741d4030114004007400e13000658051004900062250380c414128020741c1c9007a254003015885000c0180d030303594261f0141503074003144d030a10261000d02c1180548440801490325030030071460142c2180c000c602203e008030000d01c2000080c041410500701a02c0540c0f000d18050441b80f401c5007038002d060060000080400003910200c40e0081b0040d030714010f0907003010b0000c9880b07079030705d01d40b99000309901c0910808007414000002119402489942090305c81c54029102248407a2a0004840001418114603403440181c805001c80301c801201e006c4c009001c020209 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 140339019 1250 140337769 140337779
    0x110f0102030a050f0702071701020c0a06020304020f1503040609080d020315010f020304060203190e1206010504060b1903051009060626060109090b06120403080615090f09060d02100504 81
    0x1a108002c2400961981340b0041c0a40c0d5a80000c081c0c1c2101c0c0b981d24080090064441c0700750281c400c2c00c1d44810300d849140102c1d81403010340c1d401140510710131540600e171040c25030305000c122a80f854800307418100520002e0049289a001401c0c020320403e0a80d2038440c40c205440103e80050b604540c070721a50b803984110035608030f890880346034410300085081619110000b5501c1c1f007603207000c0c00450f50001c0b0504045003d2203480700c1800d00201ba102400c60302c030007102d91b00d180902c1a14420b41c2030140004003a105403045038450080ca02c101a065041084190040c0070007034030b00c0342d03003e510300c0c800200070350240f1403030b0007a244681d500c0c14420200c0d8820103c03585104103c01c0948a02028400681c1e040300c590703000c4445004021460041c00400a211401500c0241c810a20120104800c15a0041100e445810100d8003403045568a440000090290107203c64200020407480c801714030b0850f44266119600074001921112140c2c04103d074024080c0341c0401041c004517003071103 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 140340269 1250 140339019 140339021
    0x10e060f0c04090e031303150c05040f03020105070c030b09031206061612230d0c080105060417030d06170601121101080711060103080a030b0a05150a110f0102030a 72
    0x50480c0050004030060304090051100710301c101e12808219550760410b4400603c0180203507000001c204516010881d43c070b084c251040015420302070101443c001203962001d0065050760f0503502e50038021510a4216401500d0030f900c03500c000e841803410800c00000080e03420084c5d501c4ad0780c81e60040d41d15034800c10440b050012003d444980318410501c41e5420070b01482c40c0941c0d00c01d8004941d4003040740008820382c0d11030b10b009001e00c8c203d0a0402d0b00d62140030312800402c81c01e281d0f0a810801500f0304c003030490701e0700d8083c0502944818100420050350782007807500c00700a40e81c0070640f407a040c0807112040866545511150811501c0d88117045242e00501125004002d9010801000541e682e44c20024400308842241484920004221001d00c00e0140f5445000300000f250382c00d507141d050a28841d0488181800003a0520240c1495410200002c3c4200e91026000074024540c02c0350700c40c06c6801410000c010071440780010405240c04012942c1d40d00c13004130005070b0701e040041d0258 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 140341519 1250 140340269 140340271
    0x9060c090f0311010302031e041a2805090f0f0703020f0a060c0623270f07050607110d0809040f0b030c1207080a0b01080616050a030513020a0305010e06 67
    0x81c0c1c4510454010804a0b02501020750400d40900c0c0050f030700e584910341c00c001d52004161a48103015510104020001c600e030151480b4040c0c0e099010255880108112480c4041c05401c1c0c0d04031071a1081c602104400c0c0c200c1d542041090302640d01307084011007c1442c120100ca06500309038451a0200103504003c20056540340041e160a2041818a0320103000c206000c180104920703034a41c0754045501c44000004041a00c616020b207080c184045941044018517511440740c60904001d000180c400007802e04402c02450b01400d0214580420001070303030810b000540c2d003031300b00203003a420b42d030340f56407000e00807900c2440c24540707524035141030100f19030201000c2055107207043e02141c1c0564000030f05074582a01108c0414000c00b200014606285041d48030446611403190210200122006494140c400010403181c03c0d035590100c4010390355510591001164080140d60b032000c0c407e8024651062080c1444003a19046901143c4403800c1c0c0c0e0b00983d25039641d5012216880410b101007 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 140342769 1250 140341519 140341529
    0x31203061509060f07060209131b08100509061512010315090c05120703120302070b0f0609010e04061401060c0b0609040803010909021804030c050d0503010807060809010209030109060c09 82
    0x100b410901e900c40450014881c0e01c0312a0301c4200080b90300e104010b040d804851070413101038400490094100d940b10090907442680406001c001c00e803407a0304510665a05104a40d105840b404962030f101c20310100d09009002e264000d0803680030120711001603002000b102d901c904241c5125891410015580042421440c2c1d245050420001c00309907010b612500340c030022660022038112a018140c64100e9035400242428035101c0d400c01750540507406080c2c15400354007880c6c455504d00c08150100003003210710542c80300c01c180040c000ca0502e004000d41c002c0c481c05000170f06100031900795aa49909901601c0040d900e4400142000514102950800d406035411542030034107507501c42285c041405842c0303806684001203429581c41171441d8541d0008000e1601003800c1c00c2c1002030030002100700584180c031840803254891440ba604403812103142102800b112400d085040320340e818040e080200c00d640a01140c1060741d001c0c42003c1245105200000c0c0340869410041c280824a50007 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 140344019 1250 140342769 140342809
    0x1205070f060e01030218040e01020418050609040807050f0601030c1a0307080121061d0c030f0a0f2a06030e030a120905070e0c040f05121902010e03120306 68
    0x82000016042076006400b10030900f0090385424214a044030410101d1004075845400c220f42d4251040066005200342c5140040020320804c0d811403c2013590b000755200758000d80c00c01d0010780400c081c00060710000d8411010707140d481404164407460048203030021741703040000410070481d43d01421001100141c02d50340840c11840c0020303000c0c20203e4148500080d0170300030099410020454034175800066807050007000340c41040c111003400c07141940b00e410030328496007190118500d80019200200b0402c04001c1014106e1035864121310355948400300c6174080240e042c400070325401d00b413070501d402e00602e090000c10318008000b0182c440000c403904168004010b0582d2690740100c0421481d54540d2020400139564901546081d6103940912800b284030000d104090000d4001041158250540100e81c40e46400c10050402d00301c80700500c080e809504041c211031003100014000a0050502c40d040745a03450119003016050101a902918008200405480e002001c0e20f00f40207400780c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 140345269 1250 140344019 140344049
    0x302030a060f1d19030504090e01020d060501020a05060c090d0b07020109031215061805030d270f05100c021906021603170f0f0d050106020618030406050a0c060501120507 75
    0x30b605520b941220152041c801400e590344e030141800740046800801206408000e103112180b80103000b500100c0c503804980c0c0c20024002001e40c40020201084c94101010704441c0e290f000800300f545d400701e6000c64119001d00c0c0b940011520382c081052041c0e080343c0012504000502e0020501ca0007007100c0c2c01c41d140341c2001e4198a8603080145825a640c07420101048c4440508014075601d441d440b85a05210311000c4c0800194494150080d031a50003000484411501e084201e0200b940d0240760450396a03440100f1082c6003450003d100d198003820404100480c0f0740202d40d44a182d09000240c80d076410030b0400609a040060303601013041000081510747c116500c013049e44410300a07c03888120040b90b1840600d07003c804480401015002459a4010140d40e200140009202e0040503008100000f4945007007203a00b5610130480002a40c40c203410904242d0b080d0300300a580c0000c0106445460300010070700d1140c28003802094414400d549240d1078440d10b40315858010b4035030b10303030701c00 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 140346519 1250 140345269 140345321
    0x120109051c0207080106031b08030c06060f04140c031506040e060d0302070b0a03090b01050303090f01111207080c0106060f09030b0c070f061a06121306060302030a060f 74
    0x10981c190021541d9440c4182400711800c00ca00e01070498200002c5540307007020000c10004040900d211103901140100300e078554860001c0c0c1c40f1700440804581580100c00080e5452804002c402d4900000610020b881c2229440786080341c00200d40c0041807100020030300c142040c262a182400142c126101468a800c00039000c141207000b40140f80200ea000a48404244c024050b10015000c6d99660710b442d91320141009010300640c013019030f90341642200104090602004a82c10050040d2640110706d004100441e42502e00801c0611107000c0c00010380302c8429078100428002d030203031840c1510b0b0f0700700d2401c8030b0071250b5540c017800902480034048a1106c0e080300c0c00b00b040b40d07005075100100d6515100203060750300c00c00100812406580b0345075000c107c001c0d8009090816500014152044002c00340403d030700c50300000001c084c0191001644024500908a4803180300b804082101c1c0d0347da0380400e140480c1804100c03252034035144840c0c401c0c00c3c1c42c03141043d83c03118120300c0341c8554000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 140347769 1250 140346519 140346523
    0x1b0303050d0506030102041203021f06050108040b04140a06140f13110303040504020a031d0304050d081c1b12060e0a0906110d0e070803030c1207090f06050912010905 73
    0x12030141d400c196210700010300a90760a60540d4010403c607c138014620030b40345002134403041e5415484805440880d04000c0b04506031080c0000d5401c180c40e03207981038031a601c83d200c550000030000c4440e0621410a243d48141c180319060351305104a10200c0d40f2a410010400007500c0202102000d0084e10200000c5ca000320104100d400d4106008801c81d1824a021a04521030b68200d076810500024117840382d2585030317008100d243c107040600194148641105501d074890382c0710741070b17201002002040104900d80001d0003181061098005d034041d61991b02002d5411008925007400c40503020041c101d504044c03442040e80c5020301c1044114241002081c034110050a01c8900d19940d10000d410085658010303010107041c2c201c150748404c0d8203494600600191a821030160040400001e80e511002080e6801031019000c03280c240201020000080316008094000304221036400080850708038011201030035039035075900d0f514a0340405014071003110bc0088602c60389002d0102010400c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 140349019 1250 140347769 140347777
    0x30306080c1507080403020a140415060e0f03150a020705060c03060a0603020a0e120c0f03011407030b0102030403120914120c04020918090706030c08070c1e080307020106031b030305 80
    0xb0380708400740c4070354140c2840d031214016a08000c0d08058000c5c40481c03c054186103043d18800308503428041e02404012901855045121b5400801e031004c2d140c0c00c2030710b40803010303802e000d401a0840d014840c076011b28042654013602d111016941c0001c4407401d208050191030360082c22034411f07501e54240680890301c0b0051610521042690103e0039a03a950311444a10342c0100006086821020010322041d4641d1107101d1001d02c0b40d1a03c405d0414541018050861040000010908a0303136480800741c015055034002a4110f020802012000030008174494081d4a459a1603903401c07410b05078500704101440c035405114030f20000c4118000000056800807100f000e4401588a0017424042442d81480e0200b46094107580c1042100c107040000e0040211a0baa80d404d200030742500303806407003481d015904007001401c8031444c40007240385140b2040c442d030300160900c04c120380240c941920540090314a0310050351506820405d015014a54000008020382002140d500e10f0384c0c040c240e0b00c1 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 140350269 1250 140349019 140349049
    0x1512050c01050a120e0c030d1d0d1e0b04020f150a032409150b030108070905061c0b07080f10170f0601060504062a06020919060c030306080c 62
    0x10005001483e59210f600c410041d54422442441101c3c1c09503503040d2030760840030303c0600a1082444a80d07815108805514005c800394244d124690100000c0c00020f21103200151444a54580c4c83c0e030f10200d6036078101002501071020888281080d10400001c1d0b480030f404680304407604401171003141c451380125824509581000103c0341ea1079000c103070a2908000c5480350b0086191f4000500004541105174010302e03230541240020344507200510507010038002c00324698480c0d1410300802c6000e0388200d0700050010803440ea40700c40c440c110341c4483c1c1102400c0b104901c50701c05020380303076412841581c0c1040c0f2009075404a413921000e00c00240c0d5440c4103101d95040c926070a4000000d080c0417104003600f440c400c0e100c0c10768541c100641140c0c828072407000005e0709510000703c01e400005a07144101040000380b2451609522048081d401c0a0f5070241e12083d410b000741d25150b4400000002000580c42d440503400e81824060122081a40b10241c0c54005003100319056a0350b46020010740 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 140351519 1250 140350269 140350277
    0x50309010c260615040f080c0406060f0f02031e0a0f140a03090c0302040905010b0a090b030c1302160b09010c030216030516060606081b0c06041e080d1512050c01 71
    0x10b500e0b100002e00c03c5028203201c03614084001404600c18040d00804420755407c8030494620350310031818401211094840c020000340740302c40500c501845258243d00d6500c051040b2810080d01c03a001810f20b001d59550b40000c2c81c40085c0f09078003607401c0f849209204519042c1801030b5507500c0b1141045104030340b410000c06942d115088104000329400303602541c0c0145c8108441c0302d603454854004d01d00c2c00344030307841006580c200292480107805a0038040102038040d100c041150030501000d40f200391500d9540c0c039001d0161420301e50f001078a890285020f200b401da107504001c0d40c501d003195600c402030350815004014501e028240614a11211a4035203070480e034540d10b82e00203014018051000030311050901c0300000e502036000c40c04d240507a030f0081c2c62080203464242c074240c01d03202e580c4040142d500b04000113800710319802050b83e9813108201c502d65190741c0c1643c442d40594400e40e81580c13804c0d40ea59100c1103e541c0b401c0c0c50700150801081c01d03a01001c4940711940c0c0c2d1017855480358100 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 140352769 1250 140351519 140351521
    0x80c030a020f130305060c030903040e071b060606200307150e1014070f02060f0612070824071403130f05030904050c0a0c171207050309010c26 63
    0x60340ca90780c112080b81d40032602c5203442d02844020300004543c148801e641d180710791070200740503001000c2124016240b84009500d020b2611100481c85c68005281c0c106000070080d034032918a820040d040c400c00d00c500b80008a81d420203602600b280c2c8203c0b140e541d00700100c00304a000d00800402c0300e050340d402000104027404082a284c01030558540c6171103040c011061802e2560300c464120502d000010a5087c000c2d43d0342c040200c80081c3c800144000503400600400d44141820034010f804c00c002910000d0039881c0709a582c6d15041e004e9101c1c02c0c255000e190055000ba8040181410785900c01d0440c6c2d12600b8992402404480001c1c00440001c000001003044403103495403032440e40741d01c003481c40020605070601580303940100111f1801142044009a580d5030103804413103540410b81c070744018980558645d03d03a0080001200c3e254034070f081008070511821201c41030311580f590703500e550b43ca2400820385801c0d070348142c00c00810701034821011201c1d0701c1d418400200508021b480700082d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 140354019 1250 140352769 140352781
    0x4030605101d0114010c02210c04020a0e010813080a080a0b030a060c030506030109051e0312180708060c040909050a17030a0c090305061303050d151410080c03 70
    0x14404855020030104201c0c0120701441c0707911102c1681c1255070410155002c0c45508005507a14191840029480340c658400000090310040c0c1300b21304441520100d810841c02d420110b01240e114206850200f0080f1044003440d6034400d40b0f01d80d1003903210682c242e8017000d5a94070080d130b008540c004002d1000000028040b40015800032080c10700c001c00701da05c00b044506001e40103082d9140c0c1680001e00f0030300000d1315814140507000601e90302000411490054119610304944601d03c0b1410718001045000042d07402e54240e94050303840202c40410007034601c01041e00d0721280d50b101d100c40741c201004103c0181c0c2c05000f55012180211000714808880f40b07807050800e00710074030090001d0030307140e10241201c005902862140c00985010001c240a8501c142d501001c1440010300c01e61007440020703604005232052007020751183c00d0484c10495540502c1c81542d1010b400590b480046036000c00000c05480c001000e200d40640b038400304440340c0c40009220308002003800800507000404110 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 140355269 1250 140354019 140354041
    0x218040905100e071a1b1009150e0706030506061314010905150d110f070302060403120e0309040903050712080f1501020a03030b01020705030a0803091006051e030114131b05010504030605 82
    0x400c41d2200c905a0340d008140341207e03001020030080607038030312a92540004aa0131180303e00c1c0c850300c5441004104e8a407800104034094500241040e801c8002032240c600c200030007005042c0a01461101410440c055038001401e101c4682d0141d4441c82e680480015081308a030100d482e580c1c41c25001003003d0310040d945010303a10600050040110000075882e05040c1c0c041680e81c0981d100340e0726049203032841c0410006985901d000e80c402c0e070f0400c100c20070043c603140d070020740c901c3d21030b0800c01c1c1059159120003611003415103003400825030103c20468586c01010740240c0c40307200c1c2e44a0242a01880c40000d5840d8950031000303061541c0e8201040c0d290f8001c101090090000070111560550146000401c1c0d410940d00842a8404d555248640211902940d415100090309101d00f1820341d180519440d2520b585058055503519090f0501c00100720794903110f00c1404802c2c04104007245001701083e101c502660401e0b0b10b2001003444107a0303006044408a0750001c2000c03689450b0140601 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 140356519 1250 140355269 140355307
    0x304020d201002010b090c1318140106080412021c080603280201090504050105030a030804290603060f061f110105010f0501140f07060218040905100e071a 68
    0x1560024488840d041c5083c0d05400c1003449400541d40c0114545940c16092020f0044000b4044185000441409102c07140c0680e00c05c074078200b000115120b903400d000d408104a081c0c011100150440c4100824044500000000c81d90b6a1006003003c40070016410404001102c1034010020024007240c82e40c3e4080000305242604000000048000d00c02150703511071944404901155a1810004562419104460403100003401400050080c0c1e0f0b41141c030580014812600d0f015004e0114040d03100c0300803200700f01442400341c5142d604004041500e020070081035403a03101209c03010040240c6030001305094054210000800b0404040d4081e16090309240c54074005628003000044d80007071010b543c00803104280c0b80d268052407403407a16a024442e81622000041d000c000d0b1500241040e03009000118480c160210300408580005003038500e4050291011b0380650700391030a642444c8901d4507a40a07040081c1a52171510f450070180d40554403120003218004540824403115019a031 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 140357769 1250 140356519 140356583
    0x10510210608010e100603050316020105070b01030b0604061212050a030902090f0601080903030f04110112140402120a020d02040b0a0b0307020a030e09150d060605040f06090e030304020d 82
    0x601a0300e4460400c14000c00c85903896004d02c0c8074410248005880911440040ea40c010001e1450808a400080c01003030b8082c00481c10010100191804202803036200c9000e0b610490008002e800d1940411054440350341000d55081020455580010b40d01118080b106140d030070040d44910030030704254000e024024019401100203010000d4411880780024491042622155215124080e0865507400119550040386c904130011602081e500c1c1d4107107400400c1407400c0740b1b20b11032400307240c0c00f907072440b010702001511400305120851422030000b05030106060003e06c42a040b640000c1c02d10603225001a004030350740d80d45c0140c01d031650407030b441c0035040c10145580e8a00700100005d64880490509070f0000720840c10b00c00c1180341c12000d0754014061958140684842d203410829100540300085039490b588103030005a9841d02d0140380c2c04485076560000c3c0c01072a081290064030141440075407e50010070030800103984203078100d401c480c0c018040708500f00c81c140300d030b000002d8051a0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 140359019 1250 140357769 140357771
    0x6090b040b19091505120c031006050906040f120302010c1404031e060501030f050d020a0c03030f0909050108010b1201060608011e090f09021009060801090209130908090102120301051021 82
    0x40400c0680010050107006c60031401034078146d403070482c00d00c00f80c041500c006501404a8508104603489880a030107040c40080c05145816540c100c2604440303d2a44a4449400b19981e001306240c1c0a10480204101c1030800b4802400c10041211451282d40001000320039200e418040f00c6c18000700201900380c1c00f1004000550b120306114603000201142182d1510030700d50390102c6c1c1840410300b01c00c250780c00780e14074010b281196025070b115900b8050010800004920001d00e0683c03d0060a000b40aa4000010040e4034942400742d803a071902c038a4800ca03030510300c08220241d403010300181140c280c09000d0000b890441d0410800000c5607200107a001e0501c80708200c1400198800c00c844c0780300725240d1901825a0301c040d150008a0320441c03000c60b511000402200b00c3c15002000500c01c014080c09020b2140c440c44001c0300c44402d015644000042612065941c04012044d12142c2070540d180c115032402001442042c031000a036801c10024100c1c1e030400b03c1507261942030003118640 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 140360269 1250 140359019 140359049
    0x906020f0429030604050a0b03070b0a090b0906030109020c0a08120a06060c051002090411040f030302060105010503150d060623090c090d140f03040b030106090b040b1909 75
    0x36a48503150001d001d1a20450606480094004050001c2080039010001e465045a5542c410080100401021807400c50b803101307903110851380d061000802904451030070359122015164000c204c0e0715290040e20340c071142001009040e80e900c0e800d0300d0440c0c40a032005a81c5050400e00702d810911403840040c6040c1001c10300da95000c1c404400e4500c600311241c1304014407941c40c0411110a0522800600181c02041a8440c800f500c1c2d0001d240c43c80c4054004070781c160202080c91900e42c040ea00c40c01c042c4012902c244101941440804c1c0181024a40300303085040117078621008101a140641c0b04408020920703040003000e400810041132520706060302203031f5802448003e401030f8800540300e1100b980010381810482020349008000240041d4000c2800e581c8180324851000f40c10f1009118075864102c12410030802480607280042189071294500760001e4040ca030990000c4030310002c00d21080c01004a4141903952190f2a15040e226660041e20203032901e0036140c00c00d072050f6400e04c0d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 140361519 1250 140360269 140360287
    0x26040602070617042a180e070603091e030e060d02090111011109060d02070f0302030408010501080631062405040504020a230603010e040b0603070e071101090602 71
    0x49907040c110788490720380200707844081a07070040015040b2001441084c1c45501c2030440e42485843c405003841c910201c00c10b807500c0751200791044c080f00c1d8064109944035a010207080c1400d00c0114010071103400c0603c0420520b0383c90720780004100300750310403403641c0600e0402810700c640a0100c40b1000500300316030b540c0074448580003a41c000030070f45010501c01c0c51240c58001c01485400a000e20031442c10303040455910401c0704690201407001e486039003d1003e40c0101e1044c3c00d00844140c820b800075079680303191000c0c460940304140d01480c00d41d002141045a40c1d006020354005812150070b0814a2280c0100c0c8040b40300c40c101000b81103985821030003087d04800340d825500103500441c4204040b031b0b80e501048241d542c200e5000350001041442003010303503a00c008003074050305000501d491003024400800c0254200340d1020b030034044040306020500800009458102d00b00b0ba000e401320700d050040540203580080c0c100401c100341385c0071a4480b80020350110640640c0000305640da25061 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 140362769 1250 140361519 140361523
    0xc09010e0402010221030c0706090614091e06070507240c02100204080c0405060a0e090114010b130302090612010906060501020d0207060903020d02041404060f0c09080a26040602 78
    0x4890407030151103108520008805d80c5031100720300c0e4101c1c204081c907581e2a40c3c2c05483c20f8000c0013045035596158201c40002030014003a152180c20444010034141ca82003050611300018501c0481056450203c20b515024020641d02c0c0d01140c9418450385d251340c1d600e4584508481452414080340b49118030361300f000403d8002c0f0b07810501e141d0032580f0403803201e241d200032441039110303506195000c400000721a040c0b5400c00703507001800504000850f5501c1003090100c2c0b000b02c0e44c041280c0d540d800d07c41002884080002d001d4030040c0d648504003071504005c28840681400080d21400c400d00c00036400766101c0c0c0e0140002c0c104400284100b10305440c102d801303042d55002e900c0c054062480c44a12440c07000030f43d40304459441c1d40c2c111301d1500e03540a1051542c3c100f0383c00d07a04551169038500c17122508101c010f0046110f11000207510b00b8005484d03003141c001c0301d51142007180c1281c0c1042128400a00c5000190700300321100e00d6a051064601d07441c1c118086d85a25034400410006411500 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 140364019 1250 140362769 140362771
    0xa2007020423070329211509010207030909020f0306150d020f04050a0515040b0307030b0a1706010501111b040f29030706120b12010515040e0703020a0312020c09010e 73
    0x44c1170040f4050700f1412203608080c80507005a801182c000502c42d4010441c0001028459040d0145d03150b070350041d007001801c070300d08540c5540240c3d0001401c0c010191320041d4100144840181181404005400121144800f03840507125900e9812030103210f00c090b030119074400500707000865440310101141c4956401a10500384a01d00c241170001d4141488040499030042e00745809240a040041011041e000900300e602095a41c0700c05402984031040030314080e1582d400254408000c0f00300f620310f8140143c102c203040001c0c00954050b40d403000206810f03a144500f40f002da41c0d04400f00824000e001c044448403046050101c2c66038074455005c40302d10000b40308041c00103015110002c0c15602d1070144075403000500034458003083e00b0b4003544001c2202400611f0041c902070580c0030642940e20640c0c5141d0000440e0400030f5061405101c1c0c4602502544041c2810601e5500040c6502815110281c110b608034510b284905200b0b101038515624014025421541c490b06110720340e01c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 140365269 1250 140364019 140364041
    0x40e010b190503120405030d0f0315090501151e050a0c171903020304050601030f0f0b07020105101a0d02030709091a040b03011a10050705060901050a20070204230703 73
    0x142d510204c0450018404039420b855019006000491491100301c600c001d40206c3c8108141e0354511550696544003a150028250340b8808105541001d01c00b0018456802e450801d1010254010410b0664256a403a01a401d8140607844443c0310070151401c540b20781d8001e00d104000c28030b0241903810780000e088508440d03001c4500000604d1405c1d03003203201c142d8020786154040360041000528130050400c5003446649440c5455420b0350741d0941d211402e43e1410007503510342c0100924009412181d0f07008020714502d0200405241d44111036031f2050340000c101050700080082e032114000c00b5114002c0c030102d28100058400b00100060080e0910411441141442d64034041c41c501402180085000b02d03003c00340b1007003450204418008a0000700d0203010040c010030021550900c107151007000c3c0070001149e10300e0580b2415003125040c03004140504030001e10032520810701c0095a400c00ea040d1000100070445103417685c0c42481c40000c95060110140820694940c0341d0000c0840350 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 140366519 1250 140365269 140365273
    0x60c02010507050711091902160516062007030c0312020c0a14040b011b0b090607020703050d030f020702040227100203090f06070c0605030717010f05040e010b190503 73
    0x74036070550843d9240b0846002510304028410700e1201c2d49003540c8850f800924000c3c580c001e01014071060000d80c1c021490f10100d41c0c240da43c4860600500740518240050341d000c1c1c0315820380c1400300150048034206855801012174086107032034602c0411025000d10f40142d004800140d41b881e00134a4a86d800ca41103005002e006900d8001d420000080b00907134400c0044620102040300c00d000040030041281030400c1015a1031410760910b41c44488040703401001803980b00d10f01030549629008018014400715031111200f00046280880c040b000e4040c00c0c500451048035148520010303014100f40a50701a00c00103080303106184190002000312059500035402003900402c05c00c01d203424400150251300100303c0d604142c6000c1311000440c00c8010030503401c103c0035848102d00d51403540c1160020500c00028010443d4110a04c10310007450011400400d60600c8500c008140c00c80c440e03076004588400390703201031001c00e4203c002108000b0300740c030322000c0c84a0300c50407140340070344100ba02038 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 140367769 1250 140366519 140366521
    0x31305010306060f030f141003031b0804030209070203040317030a0c1d0f120d270620030705060910060e0c030117030c0109060507030b030a1121010207060c020105 72
    0x5035029004101c00c440b0192190300b90384480000a401400b80300700d415454071b503141d420031a015003003020b082c001d22a00c2c8481240504600c1e0250402e40e0003803180e1040b40b0900a90000140040708aa050382da040c4c078010116211203d0076441c5014030340000b070100190000910412145501440c840c00c0c81c240240281e049294080d100099070406c1c105410f00300124031605030078101c80005032400c02400030900d41944405140c14002c10010307034070000382c2d145010b8100382d00b6203203280650400c0c2c4d00100302c458903005001c0c2c01e0880994010791510701141d03030301151200034020754000769081800e035541454216541501c1d400f001d624529282c1c5850f41c04a1220041c406c8548034425591085256074201840c107101c51076000648080c0380f004200d00702900b070b1300780a0f00d000c0034807800c40403506080404c1d01400f95402401a00d0280d13102c8001c01c404100100030304d9a46130300a5442207003040d030642d04543c4e11041c84e030814590b580000340520801850340c2c00300401e0303003c503802080f207 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 140369019 1250 140367769 140367779
    0x2031e06010c03020a0b07120204170d080c04180212040317011e170708030705012007021c03032301030c08060105010206220609031809020f12090712050313 69
    0x80c1050b10b46003c1c005a00a0350001c0014070003010a0380c2040c45030409180c600e0201c071500050741e100740c208003d502481d04149411140421006511a070708d810207044910345440c1401c001e024030300c104e85c008441411090000c070415811101e01c6800d401c0c0e1120680b0b4941406440d46801c40d040c514241400f000006000360191007511940d007850352801c030002d140c162400004a166240d040450081950002e07031000108002d000103840b4070004520310003180302002c12070440b01000b2100d00420410300d00140e07546804100e280e281409100264007140c10102c004000801d080742030000909000b1181c00c1141c14028100c0e80f14100c401c0d001509d480701544c80352401e21810b400342e4071540100b250007208103500c0066815852032003140600ca038542005075541c003032059003c100b0402e4111100c88204140310082c0040038000d40c54402e05070a960000c0c402d00039100902d94500000c2400b200c000d1084000a001d0607420850703d40e85800c015880303038002140c14160b0034400d080068 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 140370269 1250 140369019 140369027
    0x3070f290403080c0c0d0e0609030d1d03160b160b070309020909010b0d08071401020d02090f09010312030e030d05092409030d020c031b0705010201060812041703070602031e0601 78
    0x5640f100d00544084c1c0d1ba40c840030b0303800002d00001542e000c0400d0141d0000c981341040180343c0b82e00f0035520302c0150f814401000c00080008028a4001d0700003000880602c40ba0082040803a209458259600d80504040c05410140c60000a010103403200078070241ca5411742041c0b01c0c0500880b10384107240c40300d0b074907a803c9889207200b164122664010600108428201a001d818000c15450b00c0300c14468642c14220703803200182400c2241c0c00f140c52007103420842c1d00d0009003c02920b44184c10b5040d900e4001e8000113075800d140416440c0d000e00a0098428816115102090f080034805402c00100e40b0b0b1b118140201c103081d6013410048224041c10103010410700441d10407000d1460650810321541c0a544000c05c0e001c0d45110030443c009000b2070081c01071082d407070341c030014101e03250600d0002401e41b00c1503071000106a12203c220310b00082107100b1542103821755100d501c000f076800d01c94641540074420b0054101340c07002c07082010040e40c4203807105548140e240346480c00e40e2000c0c0152 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 140371519 1250 140370269 140370277
    0x1503020304020d02060309030d141e0f01150203090319060b0303070c090510050d110a0f1a0a110703031206060f0c03030510050307060306080d0302030903070f290403080c 75
    0x180d48441030070f405101605001c030003503030000e40c03c8007902c0c03400411280c404140c3e016600ea0b507291500d04c000b0050518510714880042c201001900021400d04048095406a041c060200a26424801d000c90036000f00100c500103180034003501c403810030b0811071480707040b41281d050b5000c0d4105640300002c0e281c08000c031112603500c545004661350034541003c0007040010290320408840702408583e0f65100f407080c03034415203d40000c0c5003410100c01400303001c000941c042c08482c0c018400900825241d59441d082c0c4060541c0902d03102c140c6004215201c4100c2c41d8110224050f01070084103055103c8214940000c0c2d0b0b60341030140070740c1d420084407501052001c440000d1a49202030380006c0c40b90700901d800030080008041059151000241081115801480400d90f01c0008001400b0140046204100b0b14242141076103454940c140c0c0364820040010020740d1824095070030840309192140c2e854200041d6080d507040e1000240b0500c07081075509501040200002800710798041c0219 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 140372769 1250 140371519 140371523
    0x30405132a0906050d061205030304110307050a06080a0f060602210412030e0307080d12061401080105090712020409090302010e01050c16020a0308180118050603070f0c140303011503020304 83
    0x20300000d40f80500488131900419101c180440e2604d4001410700d5660032000030040c01000030b103a0b68105440d00c0d04000d4030483e8660b00941149508004503a61000030304103ca190341044401c90b500c82c00d100c1c008010345032411101529020000c10700356400140d208034150300c0c1c50078000407103801a0a040c280500d1103101101c091001d44000024402e448400d1541006002c0f580f8403525400d696040c03418100e40c100c00920000200c20010400740103020041040d00007201d540e00700100000d01180050150500520285c40444c00042c4980c1c0440780e41d030300f000b87c11500c0f1903d402000014240460040c3d00540c04c00310040c040c5c02040c8105405010b0414040e071400310801e003110810317081100140c0c3e00c694207540002c04140504010002d81329051442215a1202000900301c00c49030b0100c40e03140d08142000340240e440c2d660860741c0140960601c114528200041282c4490700148001e0200c8107140f00b03036070307000c10001c09035042c1c0c1c00388410102000114401102207000890700 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 140374019 1250 140372769 140372777
    0x70c15110102070c090c031404030503190b0a0b2a07051f0c03030e0a0803131a0c03190608030703030f0e01110403080f09090f01061704050c12030405132a 68
    0x30003030f40380540d2000e0030740321b418100400c01240c0d01400c490079000480b002e07004950000100102400415152006c0f010030b051704000c0003010f9400301d0b4880703480c4c0c02041080040082c1d555619011041d00c440d45010104c8841c0485e0009000203403540d2440c0b2409005031540e00141d500c0707040c21106d81e070018249680d4800d0035002c40c0c5084018052882c2101028040c3c1e0003c0000f250940b030041d031180d541d05901880018040c9000c18140d03001d960454200c2d8441000c0c40407507122602200d4010500440242444000803410340081103254840a0980b00c0051410700300750b01608080741c034001c4c03020100001150072191a080e00c0d2011005540b541080009000040041001d0000d00e400319900760309020100010850300c1d081a508520380001c110010403075a544581804000c60980c1002c000604042d0b543d40c2e52079100e2410a032042c94031804001d20f03c101002a10020f00008210001c08034042e540b1100902c04510103680c2948000d50044407440503a0321030720742d90040c0c1d403 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 140375269 1250 140374019 140374043
    0x304031b030302130f051f080c0f0405060403120e030f03041a121e070c080403020904030e06180910030b01030312060306020708040501030b0a15050a0203070c1511010207 75
    0x40340c0d2080c03280031044041c99401d1107682d60740b100c40404940500103104002c0030380f50a050810901c040f6044000041d0940e454610700b5683d03100010541100300c070845651941d40c420206d000c00d00407508819000600400c0000602201e11884452650380741c461507070302100b0009150f21108212900084c5500820040106030340130000100d0342040c004466040034803140c80d4004840c13042d1010071002d00f10354070000103000b2035621150099a20700701038581000f41e6841d1034081c0500d10003c3e100d000314500003428140134441c1d040c5032180051103555285884030074080c004040c21590750044000b000020300c88032034403c0d90015650440c1f1301c402280e19664003100c0700a02082440c0303800791520000800603105002801c82c052154201985030b03420000010226082c9a1090744075140c1d88a08000d040001c916003400c081003450480e60341e0030440c200340c1c614032444d00e00404502c100c280005802c0c00c0c09225003c2071003541d6034018140c013000401400c0c0e01605002a0000300300d04 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 140376519 1250 140375269 140375297
    0x405040f060308220906061e0201020a090521060c0c1506031903020a0b0906011d060d0209060f0d050709110a0f08040c030501020703020f0d03020c0309060d0b030d0e03010f02030403 80
    0x1c0c075500c050f80040003003013980645586450003690a6a030080c0c0104440801510700002401c050300c0745502584000c506103520358070021700000c42441410702807002c52103800c404002d075030500402512170804070340b1241040c48044003a0f0748002080582c40c007814410006a4400d82005401864020b0091107001d41041540701001500d10044007588540703008040000ca102c0301a80c0725511a034082c2001e5171418034182c45180700c00c00320030150b050040c00c000607940e454076400710054041d1110300c801c1c0e49020208809500c42030800754408000c0252108124002911b5015205c6040c030a01c00c060301040c8051650051440800c0455800180d07031412170320803044203501c940503503020302c0b18550301d0700e07180d00f244d004420541c01a0884005070065180c01c1111701c0c1c01903518a400c500c0e01e400d007004540c0768040d804e14244a1880043d070045a0a141d400050280070020242c68441c0d22018024104803102004280254284104042007192501c01c3c0c920039601901c404c003603006c1d01 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 140377769 1250 140376519 140376547
    0x3060803030f0a0204080601271e050403110a080d1103042f12010207021827010b030304080f0c15030403050d110a090f0e07051204050c0d03050405040f060308 70
    0x1000340032165805d1200107040d68042042d18002d00d54803034460320196606540701540b01380410038059090512510900b030010881d010100140c030380d040056140c0ba01d1034100c038030030034031100c00441e44245c1e0b076240b050010b1403000742108110039008001ca901c514031035060b10f00003250082c0c0300c042542c41c65090764495404003002003403509174440d0700302d4818002580e940c0e2400e01c81c030311503035001c2580302c11410180b1607041c0ba80740502c01031246140c209600701203400e42104211001060500d6140c443e4425007110020160040c140ca48031515196500d9503410b501162134a60700c01d026080f14903091141206450710701e0311002925541e525201a103207980032042440c202d540d22111012a0b0078070740050451058030303644070907031a8035000c01e00100780c00c6a0006420b1205000500000f0b81c1c01504650f90942c19840c140015a101d0601d1400e1544d00002e06821560002c0c09108056105000f00282d8004590802036034640160311801c0702d61030301001348881d104000b052082410 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 140379019 1250 140377769 140377771
    0xd0e010501240c080d0501261c1e180603050402100e18010e161409010309080c060a14070c050606090a09170a030b0105070f02010509010302040308160309050103060803030f 76
    0xd20f06103201c940c520382d036542c22240d201d500703240803080d0385000602c0718414032000c0210101e10442c0d425406071080c501d8036118070440c150301c0780a8542c40070401da658001c1c01c1c0340b481c441c2211840c0c070058480c5580540154042d140c207003204a101035020038054001d100341401141c001d42510b008401c12101540e4410101114507030003034000a00310101142142a58080d0409407084042401c2c40021030400c5406030004009202045130518480c59407030081d50341d00c1109181c0440d4035500341c141074035144100d8410001c18003d000812050744e1054100740032a400d044000b0f00c081d07070b41c03003c2204d00700300c0300340010600d40014010414030300c0c1051185e60088844140042e0054061303561a11081e52150301448004001c075003521003079010721600000003002e0901510300001580c9001e00b1a0480340020f060040125030524186d10a0b815100a0b55000b80c03419581c40308080c2105da02c02054408a00003000c0d248085000e52090250038100c8109000450440d10355031104120160 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 140380269 1250 140379019 140379089
    0xd2c070504050c120717060d0b060603040f08030907030c150c0b101701050402280603180b0103030e090711031c02090303130603050906010f060c020a050907050d0e010501 75
    0x302801340c1400c0d0180c03050542c1c0148800e840322100c0c43d40c02ca0301c400c00c3c44401042c0e24442c9000c022100c0100310341c10011540300404861150ba66a41d9140c2100f040030401c1001e4030004012080200c424000110740094178010404040b0300c076502c000000392134070145210f500081c00148a8000600d43c020310ba03030400ca00d00da600110a03120080c0003840c2000c1004024681c0d1140144019401d060840b0342c04d5050781070840020f26603c590b001e08281c1c2c07500c10103081545d11001c42d402c00f40120885c0c0f040701d40c8054605680d5940e418000c181c554012103c40c42074403814040785600d800345114070600c003081406035080c4180d07a00e59541900440b0740c108046a000c010405150745e05100a05020109000d5142a1820910001c0841e18010114121907000800521443c030301d0b8004442210610728100c0301c140254400f003080c112031613202c580c1122621062182c401d400c10044c0c14455160603081115a1401801c00c1c02e80e5030a101e00c031400f040720340c011000b900c900030031301070398003 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 140381519 1250 140380269 140380291
    0x206070605041109070504030c050f010212070303020412060506130e0c19091506110a0f0f03030f06090204060e010203070c0303050901110d020a0c080309130b12030d2c07050405 78
    0x9a5000101d884e01004440711400034400107010f1040201200ea208042d04e030665001444101e030900207952236030700701481d01c1c64600101c1c1640416100350100c4010f0500e01c10000190f51440c0b4000024210645045201b031240910380d24080f4800d00c11041c40140c000010005408108140200c10396205000b2801c0c0e450480c01103440543d600035107041c2a80784403400d82030f41c541000100305801c0c141015486400c04200d510102d980c881d0303072408441c0c20508160103180d1900d0300f500140054041002018204240064a0400c0754013070021108503490340c008148400c4012030312449900401001c2d51481c032030a1002c40d00c25000340041c400d040c10103408000c0c80301c101d50304d4400c80c1420b00006174403109800040001842d106401007211100071400c05a045001132a445e102104003003c180d603c1891044070342d20340400c2c0640071048000daa60715080c081c1007402405082c40c1c412150004241103802080080040300c900c01030010161900074241010030001d04001740c4a03020340 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 140382769 1250 140381519 140381543
    0x20108011e0b0318010605010813060b04060510020109050106090204050901121103061f0603020a1d0301180609021e0105040605130302040507200d051c09060914010605030604020607060504 83
    0xa59400c0b001580030f000403000c0c030145482c0c0c1503c105d00b55989a013009040012000c24040c140d04d5100c683e00300e09500c1180400d4462203200400d000b01040e40c013403603001700340440d21080c190301940400c0c00380d4014002130090a884209580681c825403040702c0e00a0080c038010443c05211454800240344158690300e4000301020000b07140510944800000b8180c1000094040d84420f00c2d250042006060075400e1a0358403c000c1c1021030100500070b001a066038032101c0c1a40d083d0700030141044080c401d44400001818400028222014102e000d10710811946100303030410541040031000c1650b8103490182084412038058000c8400311502d206c002c04d010005075180c4c010b10707104091603651104000c0166666018aa0350240307403103076a400141c401a2441d40c40703000c88205001020f69220140016100c404c010302e0419005040d0706d280c101203904100074041e81c1c2d00c400100000034000307242c841d810192a45403e80d0000e60001d81088030000060715500300b554820b00405520f062 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 140384019 1250 140382769 140382779
    0x1b0f080408070f0503030712110909070905030105070e091003020904020613030c240c050606060f0408010c050901021b0d02090a02070c0905091005040506010b07170a02150c07020108011e 82
    0x11090804044400e500044100101140d01003201401c8d850188014800544441e10008440c03080414041c003c0701403134006240c0c24003031039400c0c0082c00060020003040c6403980300105010f500b480094402c0d800000810003066010340a601170340e80040c02c40c40c1c56200c55003000031a0703215a0006d5105e414518001001c517400e00c180e0300091034105035a208020f960811490300c1501003004400341301001d01294041880001c11a61104040d2841550307002400c02a010300d009075401240c9941c00d000e09510115806409040304450030303022100079000400d040e420003000c40c0f412680046510391880701614110300c666412023140740c1d005242007666120364800501030b4100048035911002403124010b000c00103400d094202c0325040100c2d0a1907602e00d03484540604c112803030b211012802805000b1070840d001d44202d58041d105642d106000d001a4039514031030300c10303a280f0401d40c000a5000c66800219415258169034059440c1e00788111240c0c002c1d61500d04504c000e803002c40c0810 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 140385269 1250 140384019 140384033
    0x901091812080703060b13061b0209100303080106140d02070309030f0309210302060609070201150303080603010f1107030f0e03070909060b011b030e03150a02030702011b0f08040807 80
    0x1000c00307075901c03055545484140502929403039400110004010440900d841051052004c103032030041c681001840209009260784c01d0080001a611200e060b00707100850301980c500c0412a48030340c1340c03070440da81d841300140c07441d02e5000015003045904025500c000521540202003452080c01c0400c4895107980350600c01954407141140030a1540c0802d103c0007040e20200b1144484040c0500d07000421079400035100c00010304160301945a40d400700710130314000c3d00724003603078009005004049a0360b828000c2c40f8540903280103001e946042d80b59200c81d4120300550328001c5a070b022451a00d0750a0707404403031110000d41081c0422000400c580c6041d64144801c1d0000c07d80c3c0940458412514100041280e4208504606008105103900c045100d80028483c10580609007100c44660880100341030003413800c102c04c0b0309628102004180703c1254051401900598003c020300c02075841a601c0740701c51a83d40c1404960520f105007425440340800d0390b8018441d240e40340c2400a240d440d88 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 140386519 1250 140385269 140385293
    0x605040b011e140c0c01021c020a1e020402070b07080603030a080f04030306080706050901090905070807140409020f030711060405190c050607060209010f0c02010c0609031e1d030c09010918 83
    0x420f04c0c5c0c020b286043d4042d81d0400c11084550184510a403895000c0f0b400655190041a0001c00040c05040742410b002055841340e10300c10380241080d0768a00c500d1400800070b0004440c4100454022404121a4180001a194500c2d01ca8450520f5030f1a80d0300320301d4200c1c40c0200304070105a01e501c00440c9580003800550000c0c40d168039071603164207960380003400940c1c2a41042000d58a083e040103401c1e03502401c829000945414040101041410704803042e2069400041400b4000155680c500c000301006521901c2160703078a002003054400b49545038072043c1d6010b401c950088015900e100c0f103c42d940d0703041602ca8400120840d54410200c0d80e21b03040710310145d40b4103501090342c107005d58001541030b002000a1030104030001082e400a810340c145800c014000b269624020300c1014041c0c2880d90b0087c10303005071490f82802c501d10081840401d40c6041024070051001aa100d08001075946101c0314014800b019903800c11003500020405d240d40d1401c1102100c00900104403181000b03 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 140387769 1250 140386519 140386537
    0x4021314090709021201050f060f070b1b0a02060f100f030b01060f08090d0e0d0b190e070302031203131a010305060f040f110f13020d0605040b011e14 66
    0x5803245031011005060000c0381c1d1140c025280108452042400c0c000d080e00d054640460300101f0b120195400300c0c0040c003500740c43d07000020300029240d081c040806802449100c4280c0141c4901c4961070350501e160040e12214000741e4060004079080d52000704095606c81c4180d00308980b290743c2d5202c0b1624410325a401521900588030040c0020b66201300c03151644100c030700f003001c00ca05103411a0741c1c1d2244810043d40411240c0d5a00d02100d40d903c030228040385800550358407aa042041c6803c0c0040929a41041214507003210780015140c041041c1c07040340e4000740982005886190060b5103a40300800e24000540e205080c0000a140000c828002d141c03c000c0070070040d0704514095180180151065803d041104c0410002401a007002518030760b01604001e80c0d0102c40c0c0100b440c9404013544103611002410043e807140c11706901410300c4204440c0e061051035901e800388000c944100202ea80080c00c00e0201521902c58046840340114051030891111541c5100400c11908442e4503 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 140389019 1250 140387769 140387801
    0x4081b27090c01110604030c0303060b0c0c030c090903070807080705030c0f0d08060d0311010b060d0b03100b0a0b0c070e0c04060f0206091f02090406080601061421040213 75
    0x610041110400aa550025080c20f1041150203e600c2d802d45d02d0038001c100038204043e4000d8030003010301c25006103008055001d000740d111030700c241c101e0b9115031009106038000e205449a4072186d2420b4041e20b401108924040c5d40b50842c143c03031b072508a81c4901815950404100041c00002d4401c20083c0001c8211201030b09608003291043c174200245495031204200c036000030710145584201400c0e5849a06052544622001154a5000d03140e4013020030b51010001c209014000e11a4101c1100500200c2c280c0321440b041ca402e00f8103c500214069412510300d41d000d001d482200b03c002c2080300c9496080320150355031107160185001d021101c0c440d4650000c13030308101d5030b50402c0c0c1680c56036030940050005440c1440d482540c80003214245084100d2a019200c00000d03e541101c0400d41c026205101c802d07111854941d441ca002c0c0311311400114506103403441503091307409035510000c20120400d0311401901c0d101c001101c01070400c0c1c1c1d201c589200e1480c50003440d4480c0200524a4a01d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 140390269 1250 140389019 140389021
    0x1e08030612150f101202011209230c0a0e0f041e060501140a06020102090906060313051207032d0804060f1a091302030a020d0512040b180604081b27 65
    0x44800c4940780981c0081d96085c02c140c000d0b001030f81c011002c02d26040b00b260002031401c81a00301b0300005a280b4804041d009040c3c540c2c00710503c80480c0420424106603840d42005a07180054541c0060456048003220b5513100418000303922040b98050807010700003c0c1e03004094075104c2000710346081c1d000040940b20710900c52120b0810091040c001c01050008505015007100450b507a01c10081c031591150f000000014044540580f005404540080c01c6039000c0c8528000c0380d0859118500a401045d40c02c1c110724032121002c07040504418510b040b051031400070010548070b0180260088801c1e503128408800c0f0500d551042e4160140b0b280342d542240c507848070034010001005405d07103030f0b00390214015401580303000611040d040c0c2d05036541e01074103511b030420604001c00c0c524940c440140014000a60038040806800ba00202000017000905901d081003564402c40c1324000d030070303041100385403541e0f40c400401480f403a40c05045425141c030600220307601c0c140f49202844c3c0c1c55007100 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 140391519 1250 140390269 140390281
    0x80a0309050109050306131502180f091012081c0b090a180f02030a0f0803070206090601061d041b090f090902090412050c06040b041e08030612150f 65
    0xa25030000388420300f03000c0001400c0c04007291b2034410003072070700980c000c0750412441000000d529800c4003c0b07007142d0854885400800010b244928000386a204500182100142e032030550307145070050603070700c202c011a20f10300018250050003034107040e1801c3c0401d10156860300d600e82c1d9000c0d4104801c440018103145503104001503050054202d41c0c58501c1d10488010400a044155580b580c2040e1204c07c1454603100081c0ba201003520300901441001c1581020881400091409880c15809440040d070b0341d0f806881e070ba00400d204100000c4c180021320005098041036469605202400201d00102281241c00100b551070340050300242c59240204044000c0701c55410103803e000609001403015500005c0c5298000362000e000c0715000d2001424180c042c100310b43c011092a400d40b407051402c0e00b44810842021101036500306070011295290503500500f010304c07a5403000c044d50645d1039403400e0040c2c0000c0c14111034030a21401c00b0a250514510000c1c5100c0c10461389041c034203207809 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 140392769 1250 140391519 140391527
    0xc0d0612022112070606080d090806130503070605151f0e03060903040e100e01080703060605011b060510080709062409090218040212042109050d02060c030301080a03 73
    0x41003003000300b410400c4031221036140201e0000d102a4038041043e0710740c94103040440c0280074650042c101403151400c030348030710b0383c001c040b440444554000303488499454850582007641a090020701d66001041001c0010750345620160300980c0030b503070056801c151400840c0d0b400018100b0081c40d020800541c00351242c1c0b041042040d1413081d40036142c0b50801290345666805140100c88500040d1310016054152104211b00113001701d1440c9041075a40b111510b49030b00c014001030300d189040172400702d1154007443c0219201100002c00850141003901e5550007800007811003100031008800c009061401085284050310b6800e6000a6213440d12180c8500401c402d401461920350510381c011144ea0815010002c9540e11f03007001d40d032107200707a0540501819403100381313034024408581c10710096040030701e03036101c1e0744555011141c03601c040d500034103402c00114108002410001e03007071040342840e0a4902c0c2080c8040e081070704103801c584c407140c2550402d0b044003480340d02159180b400c0c142c1c0 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 140394019 1250 140392769 140392789
    0x1303050a030e0316060816030e2a0a03020117040203030d020703051b07080304032d0f120e0f0d170c0619060b04051924030b0901060203030402090c0d061202 69
    0x6130000d0046980b51640107070034075070014641440d00c00c030500308050260186d04a041400c03c0c900035101c02e070400701e202100f1502200d2180100a4141808548a0401111301c50030703a50141c580c0780b010181804081c3e0031175001071049030903010502076032110120034009410708034401c1d00c603aa11401e00300c4031425040030107041c00000b948015003c10103417101200704d50907260014250000d18a0514400d0344510499880908641800100c1014000101c0210100074460b20f9074010180d0550401c60b2190b1080740c20a0740404040b41000052070480070308244d0f50310034141440080d000ea0750321040c1e508914580401c0c2e412803420401c40101040c1602925190313a2400c00440d0308121030b50034a405a4000c2c507010355000501404129400c09080004101c100c0c600301307a0103000c220345048814000c4410020034100031000c082c130702e8500c0135281030f81c4060740110b0841e034450302046a250005001d000784108100300d03852002d8110b0117084090440845a040c058900e44184500150 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 140395269 1250 140394019 140394043
    0x2041a070f0212070806010609140a0807170a0b0901020301030203070b070b070e010e1005090f06070b280c02030702010807020115350604020a080a03080c1303050a030e03 75
    0x50204428000203440406451a0a030141c500003407014043c51007500d401c0854000100b140700d03000000481981c4046c000c420b55130100c0c03484102140d03400c103120080d491801a0645034012030014021504400041c1080c0c0002c0400c54076a201103484600d0440000d41e03a1449994001005000f582002c01131480106003a090852524101d61a100101c040c094244010007008000c0d45107107030320a88007003400500003004280b90a01c0b142001c1d0042d030103080d00354080c4645500300255890003001303813800c1941108000340c15560701d54520604061440384903d04214034036009140408901c122027014019400955030383d2103500025180e984000c0606046a0401901c00d12100094030408221010f180c451806d290b054641d80d100020105260b03107280c850b2405061040e030380080c0c0d950049000341c41d050892520b03090103030b071a8001d11401401003805000031a44180141000b0403007a0b16901d0b02404035510b87d52441d0034215a0402600041c0c1c004132141c07000d00c0c06005195500c4 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 140396519 1250 140395269 140395319
    0xc040b1606110a0c020402030606040905101a0406080a020c01090c0801060305010b1f030515040905071d0c031306060b030c09130203070f18080a1209091103180c040f0204 75
    0x1c3c50103403006040000300c1d01c00074001c41d00070000c1121070316003005460103494642e1040c40b03c1d19058032280350100c5144110030202d14441784040381401039204840036104241e0340c4075913603541e040d40c0384042e60204a2908884d1361b1a40e60402088001e030110018090030400032454a00c3c5080150940741c14440075480303004041070b80d40c04100c945245824407401c60402150300d960361091800721641d81480d00d6001411b004500d4108100481c669042e10010030f420a850009410340f068141c00c00c80e000c1c000c0d02c10410100d24901580d1018084103485000007180e6280c03074100030b0100da0000e840074050b013a008245510149001340e80e483c08031401d44030031421031810500080102600b004400207106103c1258a0b0804c200740d04140640750080880d44041d1880c80c00c0490030540c1c044100014541203c08a6006914010021030b10601c8070b04a0035a2078034194000c011503080d404800c0780c0700f160f1030301d031300703500c8900138025020a29400142c0b15460300c00d400f80d01c1000400040514 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 140397769 1250 140396519 140396527
    0x2060907050a05040f1d0309010909090f030c05030d0f0212060d030503010b0d0b1207170303100b0a030e0f0309181308160605010806041e03080f0c040b160611 70
    0xa030b120540000101c483c210340104001201001a00c02441e80c1020044800d0010303e6080701705c031000004051004081e41c0c1c90400355a54482c90080303c828180c0180540c060004a502082c854a40c42920030b0050064070f1a00b101418104115901c2d0403000042c15000b242c8003200400e003020351355004a040d1884454010303a66070080c820310050045d40800d04000c6018040c44e82654003d141100010b80007080c00c20700350110b199a404280300d103e000840641040034002c13000f00550740034038400e0036010410350610b0f048140b59000034456008040e920410381c101c80d039041091404004245018542c0c60040748280701501d05084074036100040e1503030601500101e08041070940ca07070043c0829440e0a83c056810b20a11407074400500200d04002c0081034001d008030340d8502840c0314121500341c0e1300e102a07100e1494011140d000c1c021920010014002c0103000103180c3c3d00c4009c1406036850a0b0303d80e0803110710358012007000c5c2c1e0004961800002040303010b104212141080100341414 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 140399019 1250 140397769 140397779
    0xa050108040512130f1e1a040504020f16120806030a05061302011403100501030f060e060405040204020c0703050f010c030e190c0510050c060a050115030209030c06030705070302060907 81
    0x628040d40390282007034100007454403041440d0700402c101806620702100103955030f446c0030451881042d5100540d08065403400210304002e011703021411031f0303e10821402c0525100030400290007650b0b1800c4c240301c007044880154140382214002051045820b0000707a031400800920740c8100400071400b0b68000d14102012600000e03050354001480c0a403000310740c51610040320002107840c10a5928036002c801e02c4860b2130380b140b0a90903548207903030400020402d07240400aa07140703842240f402c2c169240200b010b908158010a6100b070010b8005032803c2c002a0b42d080ca00020384e801500c4c1900981e50501d0910020301071051645004e1400380305a0201038002ca495242400c0c400d416400c0314201d0604001108600c2e8008100c01445011201c0507124081d00707980c440c4051052034064040010300c004568403a460680714041c000e116001010300041e0029400380180c160b06118402100505a4480008611444146c0d6429460700c1503032501170311b0800098449107094200083c1401 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 140400269 1250 140399019 140399023
    0x60e0f010b030d02210904020403140606030a0201050a05090d0203060108030a030e01060806061306030605070f0e18070c020a03080a020f0f01050f0c2805041403012f040b070308060a0501080405 85
    0x808480c0352140d008036526005c1d2096040c0c8034405040d43c0040c00450008140000030241010b4100c400050703891560700c1c40205512100e810b08000e0210300180a4819510b00c204058000e101b00a0b00f040380f00074a50700081c0c44c10509034400c1b09150700003d8001405d50b803502a209000c00300703800a002d810304042c00b03d9286c500c0201814041c520340030301d100314890717240c020300c00860304890100b089087c00ea500a018280c01d051940109038180c840081f079007091020ba407000d00e4120010180c0741c032944400c841ca045410010782c0d1241d10007c01102041505004218411442d0010184503050121840c180700c031084002c0c41691600e4101b00f8504072280d03489500c02e000c3c2c1030003a940c50218400c0d000919110080f42e490280d68140039090903008401041a01c43c2d98030290310342e41e8007900b014241c074580c184000c0d4036026504403242da00c42c3c0060642418114065a42c14661114040e0440f900640800c0d00060061000d001207070601c11f0811018040030710301660580751039103c5603 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 140401519 1250 140400269 140400283
    0x204030b01270606020a1202030a0210050a0905030c03090901080f12070f0b0f04210c020d02060418050a060902030c0a08061c0f110910030b060409060e0f010b030d02 73
    0xb9060140001c0c514408901c194852420401c03801040080d4070340c00003c0d42c0700c140c40e80499180c2c28140a540003117000005451030a1010b80c000d10b81102c2200f401d10251001400556030070343c03a60b183e000011410710251070b5400a0300001e54803000100200a03840d241030303020301115008032882060b092000714801e00d034514540764080e038900395440d04080582008c5000f425442580042c0318502e854008490702131400390042800c00c4c840380c40307101c0507803012420301004038440c0281c0d4401420b090542c0c0040c00e000900d100d082c599501d01d40c075910072504403c1414240e0b0361b4200004580f00d44149400343c01c04040c11411440c0072041e08009200e0740e03450f4428451407000151060381d6404040c00340601503c00c0f041040c00714038008a514203440300448000740180658911400c1109800c1e100789241030b01b1030807a514541701d10f580390f00d010344015006522390a12101281680c001c0c480c000901d00002e180714503006070101e08444144100b036200c2d1f00441044032805500140350 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 140402769 1250 140401519 140401529
    0x10020f0d051b041e0b0a030e011b020c01140409020f0c0d0206060d0305030603010b0a0b0903010b030d020d141e0702010809070501051804020405031b03060106080f040320012d0204030b01 82
    0x813000d5851a4040240d500c01035102c140306240000303805192030342c56040800c848a00c4030088c46407034890109100118410840c413001a0b0081110705100d611480c0000c4911b558010341503c4e040d2540c0c030140c280d9011046424541000140a12030740d10b00f0407000707140810501c0035100504003440010b1841c840d516000d010042e010000c01c060b13990031742c400a0308030001080b402585035120713050318054100c403959500c6546040f051140601307010800640f00303500d52340500940f400c0c402050706d2108a80185003000403040c05142c4c60b80750300c0080140c1500e00030f82207907210302c000c0c4001401100010816a03294202c2d000400c056600002540c030800e92480c400800c1d800180045402401541d0040c0c6e8140f0070760301d0003040002d10914510031600c0030303801d403880c5a80b250007c0c0e0300840281c50b1490000110700014021910580302010640034410a07440c0e403170920300102e801d5170824445204c11500c409454500e284010b400750306100d000080c11744c180340c50341c0c90303034400d032030701440f603 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 140404019 1250 140402769 140402789
    0x120a0e10020114101d040312140717010f05010f0c0b070203040504060605090d06020c030c0a0b01030209010b0f0f09151207020712200604030b0c040914090604060e10020f0d051b04 79
    0x8901054003d0308d001112800c400b20805c11604000784100c1010416511100400c0c02003000e03400641c0256041030584202c5480310340200c3c9403100449490060781020340401c00100070f040700280301c3d111214094182a4000c40d20f4a0515040004039000ca038411001d112040010b40b00d10348803d54188103858002c040140c81d41c0004000364114441c2c050022013501942c5e0300c83c03082200300741c0240d06980c02075034480c681c0c0e030300c40b2106041803080c41c84040d4030060501ca4000c00001c590300400030a9405800c1c1c020000900c03d0815440d040280740e035501682000801c07086a504120b21401040e0110104440035440c1c0c5075020280004442c03140c13403000c01c24402c071941d00d8610172100119441580c0c1e4141c2c4c6045080000c594000d40510792405050a41c448009000c1c0704d806809580d21502802585d2251396400f4014041c0486600060140300b40c1d0012500540c4050501d0105c031340c180c140d1360501e200c3c0e20b908446000700b100107281007100b088244a503408013072702e0a940d21050 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 140405269 1250 140404019 140404021
    0x7050f04090b073e0c0103090f06090203010b04020a050901020115060f03021e03011e05010807080c13051026011a0c0a050304090e1b03120a0e10020114101d 69
    0x8880001680450130034500d910314940c61071400c16802c404aa01c003c003900f0358602a201c2c0d801102680c46040025141500d20410840819901da003c428070610003000002c0c4400280d0100c0c0690300089800704c080b41004c070780901c0c00e50302070003680725880c08038154905060400c00084c1ca2828a05034440400d9404182c0802184040b12503089221010100340c1e100c5d0f0b540d40240301c00d80710900340f9001c50040749100042c0c550050203000c0c016896510388051555600c0c4442e661b5410180b54070720302e00251400041d10b0740b04c003405900c50102940d80d0030b90a00041c0846000008440c010300340ca9191038004000100c40d102002c00c1c841040c100d41d40e40c400c415000c091510401310300c0075149000c0068001185c2c0b030a540000c402c80748110036501d190310740060002c0a02c5881c081c540d0141c00c003061021100c591000201084180b50401581c28a4568045000d1a0000369100d001d070390341e51340b08a520301c66200c281e640311202480540c14241820f88410030640044150b00503010304034 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 140406519 1250 140405269 140405297
    0xf0a090b060706151701050c030c0906093a05060a09031110140108011509111b0604031103030702070302041109030105040507061202070305071502160507050f04090b07 74
    0x901180c025582103601842201c40f0031002006070301c913a10580c0144010001088038444041c0500c0c1e114001c01c402160844d0349102d030491960348040707a0b140c0d00c80720030018010a607856402011150200b2400d1070340c60951441e654105044070360b28040f600034001c00d0b0300005200052040d80c40b42c500e480100d550082c1d441c0540e52107100c80c1820443d03009941c0524440102c0303500403c3c0c1d80e00c00e1030308090b081e41ea484030356080310341e00c0e01203202c0c0030040e51050001c20f80c541c00c4940171440c1030300b2176031400c40302c2c00c0d40301025044002540740640000c41800306265100106560f1000220003035032543c00e000c1c0740a50b881003103210082c015030315084209194039101007617840117840034000340802e02e8117103003140c0c0b18029806940c000c9080c080d2540718501540c801d8429150341a10766514000484c0c03101c04245403041802810607408100c1064104010000894910721404c02040e2642c2040304200ca0312a0069030381b402fa0746071500b40c00208003055141a0408a18104019000503413 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 140407769 1250 140406519 140406529
    0x110105070b0f07140c07050d17070501020712030b0303030f100b0403080408070504022802010f090506180f150606090406030b0a0501090216030c210903030207050607030e13021207030b010e0f0a090b 87
    0x340c89c282440000700c0c04800340f10041d00100145440b9800500020091820940441c0c1c0310b6541250194800c0c8002031520001401c83e90304120103d5a03e075415a0310390180200342d026420403a0b2205000c50200f001d00c104101c40d030060442101c0a50400710320321409a500c020a180c0300102a141c5601403034510300030f601155555565030028800c0614508245d40c4d01c400070f40744444d543c0044220118084404161680d5011180000d0031802c04c40030940b00c242e4102034801c550090341003040040760b50380d0340300b680d00541c4075002c00b01e103600d410701c01e0404481050f485203175a10300400110341d50b00001400940b91660600340b04120000e40d04040c140003081e000f00742070706803040035410302e041c1c2c1200146003203911a500703d45030717161600d050003414061584002c0210303010b01005c5800b031800c0d00000c075038512050f50050030120203108001d0803000130f07030b80f28011941e28202c0c54150b50f40030700c00041800059170391400035840c2c03c01051007490980b1031407290030350780d9040078110707954 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 140409019 1250 140407769 140407793
    0x105070305070c06050c1c120c18290301080c1c0f05030405042702040c02100f0c0809010c0c02190801050915070903030804110105070b0f07140c07050d 67
    0x20400368602240c491130007810301d60101c2ca0515251251200c181c0c8101e450282d11056000b1a94580381c515848440d0400a80344105400e01409400c8040b408420f840c0e02c900300041c82a0703684090081510a90080c10346071190b03815410340010001800100c00019010030003800c1a10380c1c00000d5003882c8103c00021440200a00d40c1a03034507028401d00000002030400d0b070300104c404025840c8451a481c1c0036481141a201c0b40686408010001d8a02030307001c2c103060420360040d901680002c507501000c480600c03d190645c580c0c0d410319840007a50141038140c1c8111000020403615444180181100c40f0525009104070f01c0c1c3c046001050401d4124440100201c0d0f00901250034014041c90311040111850700c00c00d06c0360000510344902c200402800c0383e426440e02c04036629030391038090f500700e40c02c14140d0510204000100c0003540c404541440b0f5442c000a607516402c0c0001e00500742000071002c2c00d140340c2c6c1401200255030b00420064202ca07000c4503552108007243c90000e9030810 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 140410269 1250 140409019 140409023
    0xf090503030309010603060506030c0a091a0312070515010b07111203040e011d10030605040516090915020a1b02031011030106321b0d05040302130b0d02010507030507 73
    0x1c040140507608205420000a40f44290814082d5076211703014995108184170300251300041d2403808002d1840c03583d2000c1ea0314007251011007103ca883c0c1002c245031224901d50280c1e440303000900c120500609020188a802d0003001c0c00c8059454280c813000c0c0c0b400b5050000e840849481c9100203290b491445142d401c80916043d682c6840d80c5100101040e01c09220700d55041103119204016000340c0c00d010b070720030f0190320b880c120342030306648500c001040000c1c07044896110703c950640040518a009500901a10002040c1e01c02e1518040041c0024000c480c11703050700520590759402c0e046948204515844040408806030600020380b412080750104203465241c48882d2101c0d510590080d0b050319200d449079a003d00e04150902c20ba480c3d908045e60015005a210400110001004200d0343d00140080e000068a0f40401400d01c0c01c04e507248001b040b8002020011420401100d83c3c000310035000c2041404444004200c505440d808002d04001d00007a0b1542010300500984a07115 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 140411519 1250 140410269 140410273
    0x60f050a0c0b0c13080a050703081c06030602090f01080f15010903020604060f0f0e09010902070f0b0711010e0601030b040201050c070e0f010611010b010c081b0f2b050a0f090503 78
    0x30034407030208100c550011144110200010b10041707a03c42d00007440015075980320008068152954841d000260020b000400b43c6a103101c1210383c00d00d1032070041401540c01100010703640c43c001c2040014021030400b410341484218002c100c5942c401d00340d0164810030030019214150340a0004841018050b00020f611040c04640821321541c403400010291856483e0040c510244220607240d0f11084034550394401d2030040140309031803a07030300505480361145c0b0003916000c000ba03440280400c001c0702c0e40c9000981c44220000c004400b40103402c60207001c4d4025080950558aa1101a040c02040a414840009003940511108001d640b000b4a00c05134242010b040008910189000a00ca014001500610024811030040c40b481c0c1d1154816100c000d8581119603840b155034001110090b111b10060301519056035090010030314002c500e43c0036011000c881060300d205100c0c4104102c030800030754400707500007030f0b0410201d564101c00340c201351001c801241c0e801c40d0382c3c0c10a904556018 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 140412769 1250 140411519 140411521
    0x30406020a2d1407022d1207030b06011b0f1106040605030a0b03010209181803161527030f030c05090f03010b09181204060f050a0c0b 59
    0x11094550180200320301d556035151803015400c60740d45440c0310031100507960034016101940764500440f21601c4540ea1052010306108481d0000b0340100201c80242c2d601c502c40c0c2d2449044615015003001d0010002c48000c05101a8503103c1c0740d5510182c00b000301a030601c04007050443e03006100d111803810440c10240c049403042c1c41c01ca1607014004c40121103403030250040340d0852510310301b07560a403100c40c0d40312411341c0e42c0d100e114400707401c4101e80950595400c0107040155100c0e4030900311284c540c600d1100c0a410b100750130090717030144090001384075001808822404070400c0d15101c120754008030054160140600b454004003c1015406880d2009540e10b8840e440900c04d0040c0c07140c025166102044060203082c0d0a460040342c1c40320000b2410000e2205134508a4281c245140c2c0160000a0038110980030070566001507e14200c0c070390114034580c10525080103d500c160000c2c0300c50b2424149802070180c0701c1c815aa00d0318050082c08a4040d004c03512899502d04045c0c1c006040c0152 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 140414019 1250 140412769 140412773
    0x606051c0302070e06090a0902180a0e0f010b06120a020408031c1407020715022503020a0b0f04032d06020c070603060803071b09060603021b190b07140304 68
    0x40300c40045401c801601610f00c00140b81c0c0001c4040d0784c400c10020384140d0944d40c1d4906460000d105118040780e2212500036150091140003107241c0c13080030a80c00010712000c100349102c0c90701031480e080c1ca410368104010407a01e600c850301541c1a0410481c1c24a41640300d0043c034034040e000b56000424075101c0403038004040603015807201141c00c4250400c02442640101c0c03810f04050849114025a0041da010080300300486000113a00c10b403841510701d11004000c00202e44000201c11103061610020140190701d171203080c400c024210b081c0541d18006004480c0023a80c0180e03c4040c046104481c01e00703070782003401945c095460007558100a1500c1c003516040d0020b42161896003080d1082040200380d850291041005032210b0708021418208250ba600c3c1e08140001840d0700c141b959100009014212800303604003800036601c0158440850b01038241c80f440140b15900307882e50090724803800b86802260304e03018140d04544503111a42c2c0d0000180c0d00d1600000c00611400000020001 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 140415269 1250 140414019 140414059
    0x30711030f0a0312050114031b0301090206071208010b071208150301140a05010f08030403150605121c0e1f0315140307141c05070302060403080a230a0c060605 70
    0x1513131101007034104074998a4803c0151601205800940c00d40e00400b820300900c501d5100060030040c008001050b801e07196404103080390000030301250400c041c041001c445039000128207015004ca400400d00388081500c0b000007216201c056102401559004103002c03602c811980e80514401134024040007a00c00016001c0c00d81c12128000118542000800d0f00d03142d21400c1001c54500c44000e504190560b150000740d025582c0c41c0051706a0384500024161711503c01c0d50032641d040300054102c19015803055609103001d244003804202e05e407000c45640c1d5403011429101e21004c0d02e04054000d00010040e001000b40220080001d0301d5028006000300c4030300027100b50050b065081d03030110341d40c2d0b100c165119211515460343c0100717072107001d0b01c0109504001c030b60a02c0c081d40444034a1030b138a8000c5400c69006e504250340d58480021082c0216804c1100c00c0b94201245100f11120212044103a80500421109104214000d4400c105024458000c2009040020204011002125a910 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 140416519 1250 140415269 140415287
    0x51303030810140d020114070506040302060a18020a12050709150602010e060103120810030210080a14060a0b070501060510110601091401050603062808070512030711030f0a03 77
    0xc0e2140e601c9507004150700340e1203c000403040f03101034407488039107a0395401511440c190786100c800c501024400d00b00850700820645021b14041e4000c1c02c840d007080440c20055400d5200001c0009203040e44480058031900e84501c04c907400043c0e541020502071828508109043c1d0040030000e04140c1030b040074142550004e0111040764000b00311087c142a5260f884100074440600b55000082910b4041c074000d09049500201c94601c0b07003c1182c90781d0009110b25206e00360320000684c3c100412101d0640c40c442d1400b904041e10718154989400400500c1e50612801107248200001c074000d41040b0b8250010b60280600808411090000c02d40040c02911180c42c0e1210130b1050000000c1c22204c240b003175282e40c04080500c3d541c20f03030800c014000c042c0d201600312504101d10b100c0c5803404440f424040611641c2c2c4c0f00b0000d41051030001741da0f19080b51904000d106139860a147c8041d030400200700c1d81d10341c2e03200070b015506070481c8001908100200c07150b202a409411008800c140e0311035016 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 140417769 1250 140416519 140416531
    0xf060501090b0109170c010e060403060501060201020d0605060304020d1410050c092b0204090309080d0e0307270b0409022707030903051e04091e0506010f090e04030513030308 77
    0x710302c0c40d681c0d0305e08031921102c416404810359040445481c81c90351081d1070282d803100c00905900c0c50503550369581c83c1120780907441200180d5011580d0001200c3e140200401444100c0740380307096080c2900001c07848540e80d48010318000e400300000351445410f01c4000c0c084503107140704100c0e46c64080c00030308a95100b13800e014451003452031280080b10b0b40242d03a04000050400d6959001996403e0000503da030714000c1e0180b044000c3d00148110041003006420342a5680351402c100c101c105051800b03d56030800006c04006003003449900b1401a0720b90003408158101140c2102c21001150080000c080040e400521120401034203c1d11f030403140896210540c0b5880305a581d148040b82242d602501c0100000d04c02c103c465841c00882c9280e01e9072a032007800d8285059900c014407421142641847c4c03804a41c90100003510205c42c0c0300315503001e0740c00c0c20070810141c0c01000c0144424000d010742400c0c6000080800d080c144120161520800ca4010821640d070b1681000b0b0480b03071080f151 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 140419019 1250 140417769 140417777
    0x506070e120102042402010531060c02010b030c09090307020d0206090306071806030b01080c030a060803030a0e15040b010b1806070605090d02150106050a1b0305070c060302070b0402010c0f060501090b01 89
    0x140c03a030440c814402c480c820401603460500c000290010b07000d8409027110390150080070326001c100030801901c50043e8038040358000240c0d0654041c28107050180100459100b900f000d404c0115101d8003004840020340d044071401c031000e280d0320004d81a070140b04180c0381c00d03108030020404c0d07089e088201082d5482e5000c078680103440c2d8400080301074410a001c0e80380000c1c00c1d500400c420030044000f40d508002c4007800840d0080c0c6030840039285800440f080701605450340c500800800c0203019030482c1c1000c500c0342c0505e5180075100c0510115040c4116000440001404031403030080c60002d074400440204a50f5444510f03003030450180c5002c1e51802c02901070710100c0c01c1c6150002a185446689003520380703400740e10b040c03425609078010710880414040030079445005810382044012a0f10700c00e0310307010707159425400c01c012a55110307007146052520400803031012601030003682d0f5005609180c452002801d505e000b40030b0203280000100302c582000004508040395400c081c6060300300703a80b = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 140420269 1250 140419019 140419079
    0xf0b0612010603020105040e2a030a0c11071401140a031505060316030203060409050f030a0212070c030206031e1503010509160909020a1203090905010f030506070e12010204 76
    0x11010782254a180300003408108200010420700c2010560740d503004412003007104018079401000c6c90744044504032031661100010400c04480c00c2440386100004141c0341c2042e941100141d130300d41e81d0f0042d0207440380350395082c580d104c4680c1c421408000d10942504140f62100c145400280140445c0354840f07071070540007403012445040c010150303840703140f2104103a0120003440c0000d50096002174001e0b03801c1504c4610300d04c007140342003011000b2103041e0002542e4031503540a0003801e1070142c01c03403580840c81c200480e002083d001000d900540360100c07103070380d560344802c0351940e1607a042824500040202d401000305050304500d204001c4442540240041d41d04e4008543c0c80380543c0040c1c807440818241e017030060a0704e650200314400c0c8003a01441c0b80c10349464086002d01d144031011030004148900900c440c140c640111801406040710ba542c1013400e50341c5480d01d440c0001e1801c8108481c03d2014a078513076035044a8424516104c000f15520f5442d04603150280b80140072003000804400 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 140421519 1250 140420269 140420299
    0x1e03060b0603280209060f09040c02010905210909091605011b1e0611040807050102060609160c06110c2b050d09051b030f0a0c050114070f0b06 63
    0x40102ca100d5001c01940603491070202a000d4000014141e100e4a880d40c2840b5a007815200c5038000c02900d40c0d07004109445071044170030003003a185041c1070b0508590510580c1000904000340b070841300d0f500390004010b81501c030360602c000c40c018924429030040c8054140b16404102007404a21070f03141001c07a220306a151001501c0c8481040c241c03484040e030011403034000c40e42050581c034520481341d2614945e0303102c64407071205607100c50201c140e100e40700040800c049a4200002ca00525080c0040c0c5014136028002804010b8010010a0b103a20840d003031111092242070828001a8488d408110308200c000a80070190000300790356526100318060303141c0702c3e00380c0780ca0980101c0c1803910782c010000b80c00340b017290180c05c070781000c4958640710114180000c03401e001c81200c104100f0609810344c01702808043c50300482504601540d08040c00b103001003101e068002040e5103082c01d018050128500b0a034480d4840d600780507098074885107610341013100d01c2050a01070203045030b4100a20041d1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 140422769 1250 140421519 140421529
    0x302030f010e060118060905040b090706080f04020609210f120306060403080a0203040b07080901031b2a020a030605060a050a0e04110d0b09061807210c1e03060b 71
    0x8071082e0307021548080700420500d04d01c0b51182c0380130030450384040b40300342e070300c200078030070785005039800c032500d440c82800c0141540c01040341c24014015441d001e5000d00b064100c043c40b441d40580b01034040c100c0001e07008425140d80304801c826907a044151352492403010303070030b80c3c0f21014540c04036014050081d035010905c080303c00f41c0e40504401403d641c6402d10b10394441c1c1e5542d03c0301c0d0a110941c00103000000310741c00310308082d004540c0240042a905c81080c0300040c1100c5441e8106644043d0300b070146421644c0c820842c4124299800340b129840c0c0441201c4041103d41c2d100007940840740d11004000c10800c1d4000c907000e4001901e058070042d445404000d02515036000b158000305041e00040c021545c064440c030001e60001d400d00518851170b8980302002c0b0f10440f02618a60300620900c480710800b0701d40701c01151409405409941d0400f506428580b841020401c03458121500c0101800505000c0e600188460803074008103400c1d0745042161400c080c803003962502d2620955008600304 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 140424019 1250 140422769 140422781
    0xf0506090d0216180b1905190b091219030507110105030108120313120e031b1302070206370207031502130806010906090b06070b010b070f0605010e010302030f01 71
    0x20707542001c0380e21414a10003503400c0701d000c402c52184030380310010b01c4119101c01c07109a80100c1b070111507036030060a08080c42120070600554514291804800700500000507007642c118100444450700800c60200c2d0315407600c150b000c00d103c041c1e000b0031652001c0681000c0140122485000c400d10100c007913030015103650200f441268821341099103090301e8144981c000b141d200c001d5202e6152100d08603190003840d02c481d020ba54010401070050b40456250800c0700a2030242e0341004d241c1c40c04602800305030880c03200f00c000364034641c000c90010119581c50b4280d0b07240c03c020312104d1001300e50000300100301c03a044104c1d42054464400030400207074030104070b4000741c1c0d4104c015044038900f500071107070007580120291354100303100b8140400e1a82040c840b003030007001804404a03403e81040c4409044540c00250f45129107401c100090000341c50000043c11101040300c413585401142c00c000800e4000c401009003401e00d0100082103092038aa0503d068034001c0c0c0403181101030b103100f12422a44 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 140425269 1250 140424019 140424043
    0x30115050f0328060e060c0d0e0105010513090503091207030c060e010806010f0c020907020d020c041b0c03050409020d020d240b0a0302070b091b091905040c030f0506090d02 76
    0x5401c1c001c50b03c82c0107509400110070b48030348400620388817091241e500b030200581e00c580a407800028154007401050180e85140c3d42d500e8001c12040d450040016001401e440b0101b8115440d02880010303c18140301b6101060b401600c403d10312158030704840d490745036902040714040e41d400004200c0358482c0c1a000c80084041e105d1515585600005403001d000d6408903a003081116040d42c2c006844140c3c0d8280520f59540041c01d400c803107140060b00b00070101519a008501d81040b0f420030729803403030200003106001d052899030044141021221440766030407498400780000707007509485016500800007510a0740003008142e107801006900c2c070101c0f034010300500c64103031004e0200340740c401d0041c5001e0710203082c0107190003a00e0f42c860010020448030341c51181c00086884107601d040c001403604011013180c00b00c000c0d2800f108400c1090b0010744d00c400c10300d60341d14005000c01c080420301402070350f0803e0903400d030301c043c0e881c0c4183c0c3c407941120150f0003400744100070380e825800000d600c54150 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 140426519 1250 140425269 140425303
    0x90f1b1308030a301e020a0306030c060c080d0c0c08040e10060926031b0a02090a020403031407020d020406080124050f0d061404120206011e180b030115050f03 70
    0x34280014100c05801091031384080106508441c001c2200b840c0f00038103244c0052340b4042207091031070500d03202540c05036002c001408264280840001c552104a4100d410003540c0018003002d141411150342500c110002c28203940010041980441e91200500c5000160b549043d0151540d0080b1038001c2c944c4140280c0d0901101c240d4206c80780c1c8243d0b4407610401d541100e081603085119000c4035003000700312507941c3c0c00800315001941404880950301c00300d031400a6241030718564000303000d40030302c4140411003140400c94a013155505140c418010350000d00601201d41c075041418021b14452841400d041c01d41100c8100101141c0681030403140300410795942c0d0700c140404e000403c21034072400c444c0710f030361610800e00034280c10038800d0085009000300c2d000041a100c01902d4903106030410402d01e07200e907014502410030200324030b0035503207464158180d41c840d01c80761202402104801030381c55420140c114042c01890600d00040310b4080300c40312401d442080516803030302d0451107011020 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 140427769 1250 140426519 140426597
    0x5010e120a0509040b0613030b06060906090d050703170405120a050709090303060902130501020d0503100314030c060f0703060905040807060209030a060207050a0b06090f1b1308030a 80
    0x81c0e001c2c001410010101074004118000c981000134103a60100b640c0070000e070f108090600502500d4120160710040c00e0f2151480c00ea45d80002071298010041e000d885240d42140d80d40c200241400f4000082d035200421440304040901320781d006400c03600900e03010782c071405c024051940b00042c420140c0307900030001e800d01501740fa8110b00508200c440940615071102c03000111204244004c0c41005500d44e031800e03015052400080c181050381c2c1e40303501000000c1c8240f050b80707040c90b0300c280304680c0e00511000d4010740001c00d06080d0701a001c0c4201c61405004100300407040c003003140a101e5011940c0402c8500e80f1a91024100e91090343c020300492800c0c0194400148198020440d00303100404460f1032076039956503130069078003164049449411061896080100c2c8164150300000304680d800340b2841d00c1020300c44a000c0040001d40704050960401588841200440700020407650542208036100e0282580c0c0394402440000000d04c044000880310061624120300e105000e6281450 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 140429019 1250 140427769 140427787
    0x70f060518030d0501031115030604090f14060403140c031b07030f0804050f04050702030901030b04060815191b0c0c0b070320060603100e010605060a0c05010e12 71
    0x1820014901c945407040c007041120700c03500400c060a02416014400328840d0b04526102c0050381c050800c42d8020b04074044030300c4c50000c15206603070b070180060302c2c0042c542100b4280b0303034409250711b000a02820310554209002e2040421020b1156000fa2a909116005e00f03000d286584108920010660000d01c0301240b080c484038540c000300c04101c4e01310351a01d0380743c0e10390602d0050413210480d509000040c0070013003030403c00d1458804c410203e804000314608004045d4880c803900c4401e5040590b214203228843d034032980484050028030080301d17150050111074025405007628640e9002c04454094030b10301c1c1490165107103078100c1041200200200e4107040e202241810000c42e030441d1120b41c0800e1040f02d407400f402071680290340c3c1d9440d0052640328047d0101c90510012103581006040111a40b00056984013800f901040010200580384502c0d004081c141c1000e03a01890004074980b401d50b0145c1e5440c42e80c1d00844c0200b140000c540c80880d43d40d844944612204201800b82260f = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 140430269 1250 140429019 140429021
    0x6140a110c0909030d230c03190c020a03030b040204291210031506150516020a08030702031903080402010c0503130801020d0e010b0f09040c03050a050a110303070f06 73
    0x124000004807068880c07070900146855a0072600d10b5941d034400b24102034601c60a00407000300c685000c0035100d40030404841b00d070340040e0060000850403400400701c4c445103004a040484401040f000b08104402070034025101c414030301c42600081c1c1440200c013200c0c50070b8404c40c1d04541c000b400c2e814810881d406804254a0706510a0500c410241f14007080782100101c0f242c46006148201206581035150015041d003c0b1010504204d1501d071040c8034030854402259021502428459100d440d41e242c203540c10340c4c141c84025003001d800040007600078000008ac2c82114400c40503075550f021014080340c0b1050f001d05001c0d0000b906a40414003550003005a46c1401d07000300f05a07480c28000a026009044043e401180d60f6940000c108900000d580300300c5040070306000003807019449030b400042c0003001c1110707803a1060407040041401c0158031380f01c0400540e40182651003007442814026203c03040c1c05000d641410984511600601c0d001c0111400107034400300f8018078844c03a0301c0d058 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 140431519 1250 140430269 140430287
    0x301050f1002100e0c0916140309010b06041409010509091c0e030a0c03030207060e0a090b0a1e1e0302010816031d0f010609020304021005030604020d0f0b090106140a 73
    0x100c10350003000c03c500c01003640c1c0d005a94850300b006005100c141301c0c0909000702030500504c0e0862001c8040f0185040c01d5010200c4c060080c160540a0789949030900308034010726940000755403200700060009062200401d00c0c02a081c0c0807280034415aa0710303020702085080840343e0000c40e8118420700d0f841400f207070003810b05003841c81c42c045044e1841c40e40404c1c82c04420351000e41c2c0c0d080f03043c101001003550401928002c0c213510f2420808100300341c008641041907a014590542ea1101580c50b0742e0b448200041c00186030b4108919040c0041a40340c130000d95050003084503525101403c080201009825501140c0d410780da615425500c1000c0001111040780c00c500405485202e20741c3c009a4005000d102054034074045c000710155184da003421200564815401c040c014410000541da41d056800c0f1080382d5420902e50326558000050002d21951a2100049103000e943e40300702000c1364403131840c2250a4a96141a036211074081e900d0041035803012003881070402c03c5400d81e0784079070070039 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 140432769 1250 140431519 140431549
    0x706030c2a0c060203030a1b0905090a0219080412020102211801020c0d081509130311060a0f0b0109050f0f0d120804200105040918050111040f0b0301050f 68
    0x70010503810b5072030403584410741e48480d0040c0d2003c010b020041c11a8400c88030841169054810035450300800606018924450f842c451b4640e02c0c00604041010f8049846600d15040d40c413100621940f03010f001007009603820740c4c51031540c040b660b034880c0c0144200c0d50f0300c00989100c0c14000d0048400b048182c0e03c010080c10466a040c01003188188003400502122443d4030054024002c1040c8010314204c80107028140b00f078940f10400507581c60350400160400342980940d403480b16982000d503040304210080c00b865201d40c404010310603844ea842100d48807000e410a00080001400444000e090350040650180f4505840f210a1510340c00c20000b170000504480700b4501982c0302c0c0000e4070b154440010100709001c040108102d00c00c00303105018807100102013642110080024040d010354000c1c11801c41d5038050380340d400340400c0ac240d0191039002d0000d0144024109010149810070310507501c002d01c06440101d0070355901c2098a060743c0300175080c855101d08060030800110801d20b18 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 140434019 1250 140432769 140432837
    0x60e150301090c060201020a12110405012609070509071106060103200f04090b03070e04020f180403021501060c02010210050a090b040b010e01050d02030307030e06130e090706030c 79
    0x54080040c064903d0b070b40040645030001030300c0d14452200903043d4108281d8602e070861515081104556160b0281d0302690350a180c4003001440b51803881c41c8842581da010703c44022840100885908000f0301e0030b0a80d84240e072985a540c88000c01641c2d20b65145c2c001c104542c00000008003107501ca43e00850914540c004028000c5031002e101c0c1e911a440400a141c19400010f801d1005c0444c80c0210f000c030100540060103298030303250b0103803214a40540000e110341d403a9280c4000c61303980e000000d0f0545900e42100000c0341000d140c007035603030001c0030000800c803000300000280b103501408141d47c42d580c0680180c00c40390404818500145401003041c0c1d90b5940da6079400010610070303481d040c40b8a00c1061700502c80d5041581074a0644016446940300318200c108481c0140c03400300c140c4c1c2031140d25090820b8401e00c0d240000b042030040340300060f106c0c50a00030000300c03540540f9210340990b20101c16516080c0e04c442017101510b40d031200364004144a00560308203500d09440d01c075690000d440b4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 140435269 1250 140434019 140434031
    0x4080f06041506060215040201021212100509010312030915020a0c030906030b0310090c0e07020a0303052a0913050c09040b09040807080d06091407180f05061605030301030c18060e150301 82
    0x1e845060b33800854a0001ca00340107001c0140704540016100b024141c2107905002d20340c955a64084c07100302440100007010307200c805507010040c4010601101c1c0d2010341096490384c1c0702c140010b0811004180690000c2c1a003040001c059009100d51840244081c0203441d14580e6000602e000d480096800c5030091002c42000a0307503201403020b00d010710b01c59400b07000c01c009030f810001c0070740d10042d10103c01100586242c4c1d0212507030a000424002c5040609520f40382d5401c0001e010000210308100d101c3d007013a0400c81e104d04240004c04010f007080f0341c100070054004082c02440303101190004d041150800110b000716a1401c040c0114080d110781c0030a44644859506095800d00450294000385290a10010036040700001180642c0070318a01c4446190070584042038243e4410180141c000141840c08402c10f06020358280c3c1e08282140d1342d07540d6a1601c000e40160382c0c401d03c1300110b40030341040032603000c40c01048200c4182090ba5496521540512066200c04031001e41c0e06650f100 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 140436519 1250 140435269 140435293
    0x712020609090c030603070602030a1e031415040e0303010e130f051f0b06071101111203090f1515040c09120c06030c0306060203160201030204080f0604150606021504020102 76
    0xb0003492240c06140380343c688034201038080c180b5020260300300c1003c4d9001400700c1d1401fa540001d41110b10004482480f0004141e60b600787c1c02060201c041c641f01c401c0c000d0401618812461a103262108295420001c1e8907807407210355102d000038000c21400b6600034021920311080d40c4000030049004002e0000e04540c00c0d41e501d85001240348000d040107141c084c1c40080c0142912030805d0f038107420b036001842d00009507035100150944501c4141480602028101040001c200007035200c8560422241e0700e08000450039560f0010801404180c031a030300c140200742e42e5150781e550140b40303c40440c106442c0c40d1400c0101402e543c0b54003001b004502c0400154034a00c0c004201c00203400798040303551150502c2802429602d00e101e100003810b080c140d0401140c1d07800021034400280350400310840d42d005200403400b900c0b544d80106c0982c865560420410ba201240340c9000b0b911640031441114070021040090b19410701c50750015802241080d8500c000020300140c1c894030501c1582c200020103 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 140437769 1250 140436519 140436529
    0x90f060d1d0a02010206010f180e0c030a030e0406080304031e0305070b15040c050a020d032703020f011503020a0501030507111608060f04082b090b0a050f07020712020609 75
    0x1000c07100050788407510040c01d55030144416400b60120601c041403050a046461201e0310590700c040302103a50307840c1c5c0c00b1400d507011b210008454030028141c80b1074808505006003401ca000c000355201d03030f180400c0051500c03000002c4404980d80314201110b20070588a0341c0d40340400401081d818040c003044180000b990740d01c500e500ca0417140790740401604245083c801151110311400701070050410496030100d800251190800d42701345800b1a41c4003600000b081c0c41001486502a03002c1410f8064081540214108000c0c800810003005050302e0803241400032107492102a402600c0300506011952181d00183d50216180c14442240c4160410140c905a00024454005c0c01c45810503c02217006000340d541140c0720010302640c500782912012950f01c82c0c030800a400030b010300340444000075884400d582000348120104501c0c600380c10804040d20040fa0040400c6290000041c10010148a02c0380150350550080c5403072802c085a07104503008500f0300b030703034829030501ca081555274034 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 140439019 1250 140437769 140437811
    0x16020c03150405060702010b0105180d0206070501020a120216020d031709011a030619090201090305070905060108090d02060105010509010909020301030804060f0903050c1005040810150b090f060d 86
    0x126070740d00c0e01c0d9440d040c01c1c41402c0840282201d811a41899034032011a0707403100030f8030a08042e0031301a400c454080f00000310f0000d0b81c00e0000b07401c0706010401e00144113042d8040c20544469131074102d0b80081c0650094100d1059400410b115224155080094240b8103020ba0b0214030900f4084210742e4040400d041141d000c03943c0d040c00340e440d8801501c40c0100361800407000c8009400070003032400c1c0f100c0391083c0340c00e100a5043c040c6030349068240541e0311590b24000117640000586210307e407114070342d50142100312495404103000001048611000180010b280400307a40030340040e908000c0116070340d500c42140e40d0304000c0010305c0414a0706561008600851250742455030303641c60141301078203803010240e4040c180700030080108081080420181d030008e1081312034028104500304151100e0040341c025000302d205a003c410141d007003d92250001c2d13843d0610281e503c50340d44862043d54403900401c2600050001c10402050030003902420f271001c0795010114080003031200d1a00c0c0808 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 140440269 1250 140439019 140439043
    0x1180303080a111315180e0a06030b04050d090b090117060415060203030402040b04050c1813020328020c07170304080109050303070315030f08090f0a08030409060b09010816020c03 79
    0x500741040441d248050342e1148078071504203084070796042114003221140341c3c4507c0d0891031885001803c4c004a1794070110245500400d041820700306410718590f1030364011500c0d0041003000c100400c414590a00350350f05080141d440ca0f164150341c415030b80a0710710103030040e5009038454100f51202c290410700c2202800c5242c3c01507459140c00c0c01040140d80d07411408a00031450001401101054130080701d41c508202e91181c148401c205001c51000200d0384100c880c030510110074041000d03d41036244078008100103454bd1002c9121080c50101e204020f0b4030503075588203840801401400080e5110141007120030380e4140b9030742d9044242528040c0004640d160000010818441e825101d2402d102840408480a40b415a914070b006c4220461001d80a01400700340450180e072505000d40100502034411001c0c603079500b2a203566134200c4c0c01030054443c00d1100104180710300d401a100340503c140d40c0e488481c0c8500e000901c4001c03c40c41c050003107018840100200740c41c10024000815 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 140441519 1250 140440269 140440297
    0xb0c01090308131a0415020708041d070905040905120d0203010501020d031503020904080d0e010b030123040f050a0b09060103020f04090c0e0604060e0f0603070501180303080a11 78
    0x3003585001807407400c005203540e154205051900000c40c01481c081c68024944501038015a2240d01300945032425610030000b80a00000d003450401032404051f03c01c444a12032080c078400c49540004c1c8030b07018200d8250000540c00c07941040f8516040e0040c01d8140e014100340d0744254034040307180c4041c6c0c2c00344a0405691350000010800b1703580c10000b54400b1409880c00b0440ca00d8050810b00380f240c150302c0f02900c2042c24501180603c001a02101c40400c0d141d44108403010029901b54060025030010034441d520308189290080004900e80c0d0012560492400007962141c0c0e07200c0307204008410a0fa22882290035131307000191000f0101c2d0140905030000c16541d8510b20401800c107480d948021f005908012018000580e4141c640303060321280091454a80e1b9843d020400a190961002ca564801c423401c4c084031200040d40eaa01804007581640c0256803200015245503800082406c81e21460160410100f0310414486401c42c00d400400b00d00c0b0074680300d501e4115003025525250107 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 140442769 1250 140441519 140441531
    0x1c0e0106060801080d02060403050a03020408100509010501230405040f0213061e080303060906030124230114180904050d030614060706110708040e041109060f06090a0b0c01 76
    0x800c2e00214041d004092a40003400880c0089200a40381c3c40040e1000b400c0c8500496020301e003d0181d010388010704840d404480c18405000303103003400f5250954040c44294600400450012025030310121581040e0405406001c141e105020043c60010001e0300e0080314001c0920069448940c0540c4d0060001c00124100d814481030b222003103514041400d0121001d00e00700600200072042e25030290b0121a680c00c155150000311b80901207086c2e0490100c1580b107111007402d100f02d00a03034113445422080d0078007049804411008060090700740e81c003042c40100300000220f000c0004051a0104203042c40d208180c1e0700108072441d500f901c0456a079003103c900c4d060308543c14031644004180b40603042040c4940440420701500c41c60070090603091701caa208c44510b9000c18100c1d00166031000004e0b9603642d80362040000c40d98251000c40b0858070110395402d29140003200d550007504000c00b0b510014200804200c80da40c401d15244e03030010107266000802949400203000700305030080000ca94 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 140444019 1250 140442769 140442779
    0x3040b1b0705100801090c020a0813091d0309060304030905150c0d1e05090a030803130210050301030b0a05040f0210020115090608100e07080a03050a030b090f04081c0e0106 76
    0x1800790340c1e00114082c0c22031084500d04640d101e6096030441d401d81100186020381da46049041c0060300c8405440d000d40024040d8600212082100413560240307070070040700e0325070b030030800c008101c0e02040b10b900e40c003e201a03007641c9840e0008640062013410841255981e4501041e040d5800091b0f00c04001300100340d0b03800e0b0701010700420b03601003140e1400002d44501c0300707a0f482140c01c1c282640f400b0400c0110308250a0b460f00601000690b03006034243e0f0300c0703141c90759800c0760032900c4000c12400780c1106654010300c20f001d24160b030b0503039a200c03407179025030b50b607003403e140040c08010000c1c0d501c112141c0000002d82c80d2070703c038160348180e681c3c004282d131140a20421554a03450b44500c0b400c03450a0000c0240a0780810a010183c841031340120741094401e000f01d190801c25080041d1070302400c20040c0c01c054200340100041d0586450521111354180200215010110345004800b030350b00002400180a0b407006011481c4011101441c028003845c0b64021115503451300920380e9034a14040c3300e = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 140445269 1250 140444019 140444023
    0x15090313030804060f1e0f03020c1501060224060103110d020d061e0302180a0b12031c020f07030c0302190602040305100b060a18050d0f0b060102010e0a080c03040b1b 73
    0x20301500305041280382d40c00801b06071014a50030822203000c10843e1405481c10780e00c41c0e0115540f070300c440d008a40801d40d13800100d40e0003d03020312030200544110204141c10742040c5580c1002d94501750014082552503200641c082d0030341280c8607000400401c540d01603000d1900c0030b09905042c542c8001001410040354184200c085814400c05568079007040006030b0754661225070003c080c0300c0502c80f503240d41c282c1001030101032080320b40c440d2080701c010040020020107001c42a0001c0d2540300e5041001c40e88030201d1144c1c080d00c8164210030400f40012074064910016080d101e4030444c1c00b5145410701800d03c0c48409842192000e0300050b080082c06001c114100a85450303000c104500c150311800079841d4450607040d0f00600c1240c07000204d28400c03030040b017001002c015281294005140ca000300d04014501c00031680c0c50202c601040300b035403051082030404200b91000b00f10901c00c945030541d03241c00c0a444030115200070040401c03052034650181c191140707141c107070209a11007004814 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 140446519 1250 140445269 140445287
    0x909010801110711360a090308060d020d0813081c0905010c0f02040c0822080f0711060d06051005031014030a0f15110c1509031303080406 61
    0x2003056810140d24032203070703030030740b400c50361140e50103c1c10401e942d4000c40800d2005403d20344031050710f0724070300c0f0600b400e03501070616810726102900c0b490140e98030200014201c540039400680001d103007800060a5040c20a65801040d0004001d018a2181995000000e84c091000e07001e00c00c04601e000c0101940030040071910848003207a6542c0507080100003040e405091080c10704100d10100d03403038240502e42009150b82500980305128000a50b8070140000d801540e1b00359000340d990618070050305042c000b40e03c6865010b200180b41020b40030000c401c0707801c519000c1e00c01000c9001c010445584900043c41c00017142d141c00b05409103002c08001c610700803c0641d0341404070800c208460125550f81d00d00c15104603801d040044890348000c60300e0301408003c003c00001064113041c1c20321000c0c400024200c0855801803001580481d0074403043d0050b625000d02c6944003540355004c80084411580e8000b00b40b204490400c0808148560114065441903480d400001803d00c00168082949 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 140447769 1250 140446519 140446529
    0x10c0e010201021e0a110d0203090a051c0b0603010f0e1c080f01050d0f020409030306050405070c03080c09180a0911010f17060a090f0b120a020130060b090901 70
    0x31418104043ea0013500041c581029510400b80001d511841901441029007210301d400e040b106c0a60181c94080c2d940d070700c83c1918038403e0890800014441c501003011031401c110400d046030400c402130317850340702e6079a01509859141d502c89003615a052203500c1040b0410329000014504090302c40d2492681c61070302c03041c48080040700000c000d44040b015403114115003054ae01d01c034400b540b50038800b840841c120402540301d418004144145941a04800c0641d102150100a00d843e422016211349810b060700070040790351000007030701b120701c5a009807000f44009810000c0315020081001215082110441661b0f5550313072011040c000110300321030603400203007814001d00c0c03a00000540000080c10015840d018444005072507522800d09900081c080308400703000c40d101c9100c5101c040c100c88103c560084603130440703091400c07000003114039080e501a110201640a170100c41a10008107000d0f8240c4002e00030040800d50803e07105400040c07020b0078811b51500b4400c82001040340c81030f482 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 140449019 1250 140447769 140447771
    0x1c080f010b0a0c06020f0306010e031903030207110603190c020601061707020c2d040515101e0f0e0307061409130603080712080c03010501270305010c0e010201 70
    0x10412521208180181540c8014031129103458220704100d5250703540000043c000c41c0007145000306080203201070360007035500340c03100c800c03c0d6110380c14180c1d01c980410302080748003444c1400d000424040e90003080720768003070081d035600c404003000030a43d154026580c1e5120000807032403000306400c4074400c035000d1003003620141c0029450154028100340300d020710305903021401800305843d103008121072034444402500c2c40b5084e050110195070000c0500111a206081d0300128511600d014480c071840345016a441a60801c040402e001c0750002c202591000d0056001090002c0c8a00e10a42044410a95580000c40c07801c084000c02061800f2007030ba0080e0311a01e000d100313143e08200362031441c0540781a519241c055010014010460070f500801c10f0b00e00e045c0c0f002c01408281e04c010009240514032140c212115070344100c42200c01210310301059142400144030b1076124680410303500d03c0e406440e503006c81040c1c80e0004901080c1c0d00c1152144c0d9900f203416106a0440040000d030842400 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 140450269 1250 140449019 140449021
    0xa080307020a05060a0201020d0e0304060f090b1b0703060501032d0b06191802030912031006120902040e150a09381603050a06150f1b051c08 62
    0x40450b90001450140520851012601e90724840c400d40c192100c0000c402d00511150b200f00010680320380c480d0041100141c2c0c0603040c04001d0340a12111000c03a10408140d41c07034207040300200c9222960400c001c40503405a041e0020100d402400340741d0103507000340100b8034003841c1030740225840f88032148420007041c0080401c0d40481c85a120055200c202551041c480d8215510302c0142e5400e280c110034065120350b0b000c1d00813007100350702451203500070341c04650300c1a81011300102d103800700b1180321071050740b2420309228041c0301d10694901c0300d00020000c00c40006d1030b070000782541c900381c1c00141c5582c4070b80b81242102103071100080e04008105030401c07111005803666194048004210595200007206410002c075070072041c00000c000650340000f05090a07d01c604e45c0291924803400081c0c2031802203402d03084244038001c00c40e00f0380b02094007002110078007600c039210a400b85801340034901140505440c400ca5140c0c1c0541e01c5000540403076035540400c8561a0801c00c110000c0001d030078 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 140451519 1250 140450269 140450273
    0xf0904020d020405040204110c03070b13051e0709020408010b0906010306060c060203090f01180b0c0406050a18030203030a053106051b010f0507082a07060e0307080403020a080307 79
    0xa2407221071540c055a000c60035564500206000d000d0101d01c1d04501c0600140f0200c080d14080050081948120f08030b03480f944800c1c5c126030070b42c840c040014003141c000c0302c8420303d9094100c1801101c910b101050340d5a00da0303501403590480e0070582c41805165100c003601c051a10300750740e54a034003100900381049098141000140300d00c0d8030441c014107050340040442c4003840f0812003441c54401c5a8000e0001501001008c00940c480310780441e070b0552031001080405044a06690a40300781e40d6405007480507520088030034003469041016640145040030001d600d0270300c001c0103220480d890b1580d03940159640f040004075941c41068103519050070240001307009000e90011a6064549140c80e0020800034101d103020412041008d5803810310302030355100050308601c0c422100e03601e0b0003003903946590f105060701c07807202d180c2d2040c0040702a4010840c0202c9025200c440c1c00398800080580e480800e6503d1648011002d4590b40004642001185031030600c680251000f00c000c0e42c00d050240d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 140452769 1250 140451519 140451529
    0x1b060c0506280908040b030103030e09091902010c0f02033301140103020f0f0c0703060b10020d1103090307261906020703050720010e04020a0e1c1b050f090402 70
    0x41d00480100d070341c0f01c1203403005010340d20041da00980308002c94a81d50313503500d26029003240002e441c0315018440c40f0000603070006010680050b2540040c1c050940100c90354011a101c040551007290301540c1501c460000da102003080b444a428103000140003c205051103901402c48281d000c101640000010311404010050624014200f0300300980c485c2c1c1580c10b502003038040d0204883c200c400115020700e001e200028944101c03030040d03000b0481a00c00906001908400880c1000540d00c50f803100740103070303204000744901c40500350241d90802c005007001900f001440d034803a460380080f2a070311184041b02403e00070070309000340005210481c048402c900c41084480005094194003240200615000e44e08031603c0d141c0c0910207004810180500b90204060301600600007141c00c1009165400c0a1084a10000d141d03100c0c0b1900c4041c000c1000303042c56103942c825a0803600c020040d400145800d0316080b4002c00c88110304150703814841404030400d40b40c40c041e4443c04490045c480582c83e1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 140454019 1250 140452769 140452831
    0x106030809060d02120a0b01030f02030f18010204080a0308040b100e0c0c0307140109030305010509060d0f0f0501050709030314070308010e04050114070c06061e050d1b060c0506 78
    0x1041d110241c464110800c580f00074020f051030561601c0c05a4108440710a4541c801003c3d034009880c01c01020864041c03110481c002150540c0ca851004800b08038001e0301e40c20411541d83ca004000744c42c01d5160072031141002c954002c110b0104000105101c1007010309201d0562107d4104107420441d4a442c05181d6030800290180d0402c200c001001d5031981d10038000c5030812030704070b80c82da0b24160001c1a2240204120713202a40024a001e0000c6110f2801d0303007810f03010309001000d021044610752100c256481901385c0844411401480b4100042c60031300403244101031a484012a1030714505014011140d008800b102c0710701c007000407200103a000401141919400e0a0b040c0499446181641c01004100700c40d840c900021800c0046103548040810880f6102e4041440069030780d2450809409583c62841200d10200805000c58284100f040501e280240070390700c103080b840810700c00710280f02e0300800001500e001c43c0405000c0c0421400e600300500c0100118140381c9075100ca900c90034 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 140455269 1250 140454019 140454037
    0x50a0905060c1b120c10061a1303021504030201140c030304030e19030c0f08070302031207020114030403030917030709030b07090f090c02151501350906010801060308 73
    0x103010404182803100da1050442044100c4100c643c0d013101c5440905454100096541c000d200d11211900c1041550003450101c4084500100244080300319054268200201c0205003102c98100000541d0302c0080c103118649003011555a1513081d40001402c84162801025540c00304012080740c940001003200e9000c0e0309480c001c103a074006d410018410214076050a00307000004000807080c0454400224215200480462116903481c00002e450300b01c0c9220196050b0002c807409502d003111407000300b0034141b0514040b80a07800210017000d01d0340003a00c0c207030700090b41c03280034808010090400c440780c4865203403064118078152000401c6a0642d0100810100345180410b250318040c80e41d110103002c40d00d43e0401119120500040180002d07510000148541071440750303c00d00002625028039002a41c20b036066907801d006595141c00d068200013251a040c41c8501c0103150700c203950485454001801d545810040405850080b060300710031003076494a4400c1000601c0c100c222000c0803 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 140456519 1250 140455269 140455291
    0xb0d140d020a200f190f0812040308030606090a0f0303020d0e060a03090201020c060a11060106050a050d05060612010b0306040608060115030f0902040c021005010e010f09020c0f030a0c06050a090506 87
    0x85202e80c049a522240340070390f99001015401d0414020000d4049201031b07680d42c070781a0782c403280c0d2495a2a0368102000d070324140818104006d1021a8403e0015648448041e01032032070108002e0214026640b02da0190201c9200f6410038001c15505021002c0200740e245400204107800d0030005685109802100301810ba8581c8140116402808240c40c00503004184645503903401c4405401408903a28032001c6004100000c1002c030301407015280c0710354103940c0b141d0410940d01d4620004000261140d070344494140080e41404200004a03400303440d1340b8480e9612030030071109120548006400448440c0c000400602c905825a601041603480034540854040c3d0301c600c504c402080032a03006500641480c43d0411101c0d00050300005202401c1070401c4a60b036911603601405400707014081600051880820003092076402502603822203000392408039201003000da20350303840006c0e0107000c00d21040901c2c082c44440d120342944251542410306c00e4240e01e641e19502c1c2c10740180280194 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 140457769 1250 140456519 140456573
    0x20109031715040e031e0307050304200d060c1107030308071b05070609150e0d020111150f1602010b06030a1d0303010e040c050102010b010e0111010b0d140d020a 71
    0x6034042e49007542c414030001d002004000c40034102d180d2660300c8000c00c1000524140e1280442424800490b0300c928040e135180b50464a50b50380b5044110308045240780d401c0d060070700010655640024000d0420720864000980108800d406445e640c1025081c03109500070301c0040001ca5000340d02198803042c0c0341b13008542004480784803c921150500c0142c19031249810119581d13030400143c405846903488044400c0303201c6181155138001000e040c03600043d481001100650117500c081c20115000c500769901c000100a4110a42100b03c414241c0c1c00304050600c07000440d03a072894507101e01c9a100034022605442c000c0b07141884007814003580c5582d510700440c03089208100503441d203818241500d5803565039a24a4407486020341c3e003501e9a0090010000302903005110b0342d459000c060715581e40c0d1050034001502d025120b0203006455540301c60050205980c0c0f80c3d030f0718205911945016600040c0100139a14008285103c10155402402c80c0404100f0603881c0d0203106841200752040 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 140459019 1250 140457769 140457781
    0x3010e0609060a0611030f04120204180f080702220507201b0a0f03030216090b01080406050c130618080f072c010909060c05091513081c08070201090317 67
    0x181d0710520301040300000300454045403080c10327a59801c0c07042e80201e405000d040b028602844d4000811035000300325a00c83c40c001c900103540b403009005258001001c400d6084c3c203450581580301d21217107042c81a07a50b54010403181d42d8000c03100300c1401c81400c6441101140d103101e032135500d82e209000c0b2141510302d60350b10010f80d960084484054003101d40c1c1071450541d64600655a84500154416543c241840c04111058544201e09040312b05030369110301902c49482d40341c014100074041d11000b80b0200066031080e0200b80362880203202558502102210101702e203003280b85182c0042c0102e401042004200e401c002078804140ca03142460207520f0107043d24041e22881050070b05a4403815507030300020701483e40364001c00701503002c0c3d81e090002d80e03c440c2080b2050b1140008407684000408602d528085002016051128440c0d16680586884501e01403805416004414400742001d20900d10958840b0102c2e41003243d60000340505c1101d039801400c00840c100c060803c08480c6000a0f013 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 140460269 1250 140459019 140459023
    0x270303070210080a0b010c171c0e07090b0906010f14040f1403010b03010c14071a040b10170a03050307170c1908100b0304020111030f03010e0609060a0611 68
    0x502990007041142d200e00007030310240105000b11149080140340c41d0715034403194000c0d00311080307007a88905840380b0041001c8140707007590850050b031091240404d20071000441d462141c1248103840000a04440d441c02c04c00f601650120311015004000342400e10415903084141500c4007205414103100146580a200005004585c030005501c0c0071500e000501902c00d291405004405800a000b200d548805040c02c0e2421807081100080306081d034100c0e0000b00c44090514140b01e001450701c0000d4150381e0316140c0d141070380c041c2c90b184020018005448886041d140c010040000c90100c10b51040380c0e101e441c2c00031110058144840000000d5110b4459050300007581e0350f0700c10440d03084c100001c07184043c0d04180040c4030304800c140b19992040d8050207100d403040c1030410f0303104210b904024070480d003030300060001c034144002610601810300050014090040030305a005890350725041c1070360300070701e00a0a1180198280c1d020720102e6101c0303070700c00c9003510f003241008a03030109440c018034 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 140461519 1250 140460269 140460277
    0x50402060f040312080108061e0601030f09050d090509040f060c0504050918071a0f07050106030b011403151501030b031f020304140601210c0e0109090611270303 71
    0x40800000b402000700400300c0300f81319014603540c1e91010300d6a01e400103071341e480c402a00d2007038201c03036400c00c182d0202a14445059104506140100701240c6410219081c0c4014003030485442c3c002d94a2161101d41c4044003400400d400c903080001401c194a40e40c011094100010f040152100c1d40c03002c00d680500115001440090280456854808600200c5202c4d0381030703500d418003440400142800102d040000480040b0040e203260400e0114060866031115800320740c00e54032280000302044c40c030440c0b64002c1c11790f02500c10310720000c042010300f841400802c00f050a641030b170502003880700c085030388000810203084c00105150800e00207440c040c1010109142d0714011030424401c9410754000d103000c1c41c03246203000540540c81d45266269003090150b506d404c40e822804186a010100c0482c014600510b104c0b00340a88030303c003180800c1001d03000392110701c1e1202d603403400f00140c40c8611000c440c407800020381480c08000d5117400329080340c3c865045e035881d044521032159800340122 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 140462769 1250 140461519 140461537
    0x151009120305070c120b090303011406091207060203030403030e12040306090c030c1401030e1203040b040606210b0601020c1f0203160506041b0303050a030c02011b030e070501050c030d05040206 85
    0x1159060345e07640e001206601d4200c41c1240e5090741c0d4004150705460020980c0d040c4c486600c070003403000403440144141508242d00195210325021602c54111105000d0880507200c0c1e64041c1d607503880c00e800c0240c00c1d11200c00e094081544807018900010030721000b82c07015a60711000108680050f0706102040107608c1e04003415241c25218000f0f0030500c1034501300300d109002e80741440f5011805c05056160200015000c21484080000600180c00815400c0c0c1c414862038000440790f840e61446070b4041012030580f48144003945954062000d180607103548030900b403004222510344400819821a008601c400c445040302e2000d003039075402403050311900c0150400c0150100c0b40c40c00d006581f108152026695000b80a260400050300d51003081c0a03250980c41e1075242c540e105800721b00500040c0c040d0740c21556604001e0340c0c11404810b9039205030710320b980c010852410880c1e41c203003004900e521035814000100031080302c800b0040144c0b401201c1721f620021742640c0724004540306208841341 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 140464019 1250 140462769 140462783
    0x160c020405010801061706040f030c0c08060c0406090e060a0605090102101104031101050f120a0e06040506040c05040920060403080403200d021305060a0f0b0315100912030507 77
    0xca083c010540c00441240e000c418881d0300b206041130600d031503602c1500c1c090300603080e50a1280c0440d0042c0c0300c41c08118411034001d100349964003030f11410b04a0603078420700201000035041090a901c104808060580500c0800a50a0400000d0103808480c0308040901c01d01144200003a0700a01c1610f03041d2454034000e001d10300c141c104491407544035002c02c862002402c110f4031281d5110720b041d58207121100480925207184072080d00703c01d40005143c0100582c48410301440b5280c14040e480c011131051004000c00d050914180007a801580c02c514041c278649251500440c0c2170f1841c01d8905081d40f000002001c0034074000c41d50610881c0c0005d041c01400040000402403080c001807000d144504110320311050b040f08000d00c03845403080c00303980700403115400795410000368000d941060300100313000b04041d903401c04070182da0510f6200d40c039000c00200402240200400440c03070590f8049440c818901c0c021400030b0b100581901034030720600328043e02c490405001d10300301d4844a4000d03c0c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 140465269 1250 140464019 140464021
    0xb0402040f0c051c06050306071d0d050f0d0206100314070e01060203070c0807050108241c1403030424090203030f030405011409030a030f140103050c09070503070503160c020405 78
    0x50007074604c0d840b05203070009211800300c2e880c8180450380300c1d480a56400401516254444110403a03030f580e00050510701d0041c0c0407540c1d11041d0380b02440c8824651152001d86101c00005a0340c5040c101020f54071010364001904121300e094101c1220001d9951040405520040305200c161030405a60084048000208000309890350000094810761303205246800c401074403520030302c2c5c036114544a00c0f80480c20351004519618208107001c000281ca00c0c4036200c0c2c42404200003071000d0f90312031110000140e0f1140c64028000e240c040f50131785440a0f00114990f087c15540c154130041d450b0010180410004440b032859012a00403110581d001030480b07440b0180501d00b0005540146c2e001c807001d41c0b80c4010020b00e4503900410740e214042031005942020103812040d000b920001002180360743d0394141803c071481515a9241c043c0d07000b20003c200c2040c0d20b005000544c1d6020704800140082402009142036000b81129882f0202c0050360100c2d9001d003406541c210840e00c0020751282c2000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 140466519 1250 140465269 140465291
    0x1002010204261c0f1409041e060b03040803040b07022407030516020c010819050a0504050d02031206011b02100e0a0506090904020f0a0b030a24080a0b0402040f 70
    0x81801c02c200002e5800b03888544050310700054040c0328465046000c500d41c12400b61980e80199880f078519a40350458502d45440100001c00b206c5c04015244c0000940d00c1040b51000d6a034410034000c0c01d0030003222441d50074240c4030712000d4040100700500d0340042c0c800049480b4800d00c001483d024030600004403420314500d100c10005d00403500d00000034038020010300c0d01c0004010400440c1c556801400c40494401c00448181300d0050000070401c184e02403000025285100d02441600c401000080038106441e11605040110803c20110b50040c8810114041811107285d0030410900f09101808080c40302069140c00c140c60196010f1585034030301090746e40219181040c3e0200700d03419499252104100b08080c000c02c00040e40158403400014014204002140380500004000880d107a076107811441c07055100300d61602806440d940d01244c01200c2101d103103140c2090f9103d1803445400c240703520360b991909140242408101c840440e0541d1106e0b4044c01000c40b000900380190301d044 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 140467625 1106 140466519 140466569
    0x150903030723070f03211a06040501080112030306090e0604030f09081213080a030210060b120705030a0b0619090b0a08071d04140a0f0c020304051002010204 69
    0x180450a2551002008075034454001c0d00011174141e01f80c0150280350080c86480600403041840103024507a00303c08101d05480c1042008282281d00342800c80103003413664080e8007494501407414055010109441d4403481c06900e0b40142501c140034111013055191103142000c1e0441b46049040e06a280e00425180610b514060f4100da140d204903401c141030707180103d002d40c0c0a00c2148840f64400d0242c0d2000b0150840d602d800c0032442d0814400307000b40107028404000b030020010340c100c1e603194050000102d0203005161109111844104030307900302e0004a0200d00c0e050400241056440101c1d0500c640c90380c1d6502164603040029584900d4803081c80c603011520000034807498407544507030711001d030500310080094146000d00b002228400100c50409034180010700d0070890f0000708450840b0b60685418a6001148004070b009000399000840b8002264106050000348 = true := by decide +kernel

theorem cover : BRFrame.Cov 140287769 140467625 := by
  have h0 := BRFrame.cov_init 140287769
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 140287769 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 140287769 ≤ n) (h2 : n < 140467625) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
