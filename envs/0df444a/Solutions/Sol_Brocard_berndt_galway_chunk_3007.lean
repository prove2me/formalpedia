-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3007
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:23:12.218351+00:00
-- url     : https://prove2.me/submissions/f9d71a2f-90c9-4793-a7f1-1932d7425a8a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 540647482 ≤ n < 540827338 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 540648732 1250 540647482 540647507
    0x62203151b1d060a170403051e030c0f0306041812030b0f030616090308070302030a0f110a0209061507080403060b060c061605070501050f06030f0114060d05120304060b040c 76
    0x14001c0d14444030034240903c0d03901512204080280c0b264400d1504524441340b1400f96103e0b5440c2c554403e540200b010364450b2891072034509480400074081c0300140c01044445031000f00101c0e986030340c0d40d82c0000d401880c000b29440c66003c018034918081040810b505801c180c50340e04e04200e00c807106414480050780390808582c0680c00030012803214078062128501c081040e1400b620740039203a44d6101c940360003180d001c0b00035a00102d00030b0070680c0c002400034032601e41d5180803954410b81d20400d0381d94806044020b4021200c21011903403e440b90702586504c0c20001034056a1160301d4130b084101c0c1e40c02440207648007858011088403038900304044815a501c8680140ba25450b00342c2000c8180006030841d10902c9020400d02c00003034021f01074144a04103440c2502c540345400d4043c58181040782c00d501c1b010340d1511440c40f5502102c0241141c01c183c0503140300e00b110440e45030042c80c20008044034940444040100070402c8459000000441c0c003c0d1000d01410031320800035504104401c1 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 540649982 1250 540648732 540648767
    0x302010f020109240b1c020405010501110a0605060102120403050a111206010b1c1805070b040b0f0c030d09151109010801051215010b070c14062203151b 67
    0x1811909050082002c1c22044d0345181d0009030000d094000583c40a2403119542503205203121716a00350b190610440d40100000c0c02c04080c90748510465680340d0001c02c100070003c9985002203421030b482003000340c20941c6030009040c0d480c1d40340e0803d01c0e80c0e6a045141102c8041410301817020a09010750906600403004e80140b00b584d00784101e010380fa030001000404d05500d980000300b0103030514001d860449550036252404c056130303400c00b02c1c20301203507030050224032404000c20451041c0044c00c403001034000310000d50301c8140c0ca0054a0451140d00702c1030002c503060401010038800400a5401914020041001421081a4960000d00844014902007010240104050f04001901c12041540d51086d9103c0490544400700503c0b001e0700031003442000400c007503040000e044251000780100303058150000980348001030251040141c2c222041c2118159030490301101030720140616409050001080e030041f00c01401881c2444400c817003c42803032a00050503010b90714500040d968030 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 540651232 1250 540649982 540650003
    0x603050f161a09062214010806010f092102030d0f020f0c2407021f0e1e01200106090f0609020a021b0d08030a1406030d020706120b030303100302010f020109 69
    0xb0010800750350000c03003500c842170f04100c0b8a503084480a600341c0c80509040c030801124100888001001000f00901540c180404840b4101842e9041410320f0111000350000e00c0101d07030808084401486440b02c029090311861010342e0810390491071003807406500703508840b11030808000da60741d1038400c1004980c0014064811420390341111215610320001262040d140c9150350b40854070616540d80c01910924035030214003074041d441000c41822010407640164595038901c8001e04000d5041d80351410b20050b4001035000c10b01c411200700820b56048020070405030381c3d60050f0090200004484025441c020001c02d0841c002e1007941e16030301040d4000c20441c560b4660403007514050003511030b48070100b0900c1e00000f811010065105030101040455584080e00c4040515803004c1d004600ca03030454000520a10340c009440011a070641ca0f0101030003000d140349000612041c105103406001c0041048103000c503060a04080320701c00c1e66041548a9103840c103d00300d488000b8001c2041c1c040 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 540652482 1250 540651232 540651247
    0xb0406050610090e07030216050d030606090b12070e03100507020c0901080d0c050118031d030106032a2c0f07020a020f060c0607120b010314040f060603050f161a 71
    0x4e001c030ba102c2100d003401454201e60b15104048423045000480b6103901003950b51010a41c0350144000422003802d1415555017803074941003050144500e00044007a03410005805540b09000d131950344031024003031700d070030012140d000c0018003400c45241000d4820458243c2d201d08140030b0441c12030b081340303000d03001e0300403601002c8a440300320401c140c81c40d640320f00c0a1750060f0402d441500c80d141c0700c1c0d00c483c220b0610945541c08889003c9800e5442649085c00410100711089046101c5103c0300f0701d800c00600d068909982c4803400c60b0050a80b800d1143c007000d0a0142814181094000c00d0090745981e6a888548100b0188112034400060301f026040200608044001003c00c9100070409410642d142c40500c1c64540c040303d9201c001003003600031128001c07441c4255110310031700b842c01740006849080b0296000300003400c010305250240c588241403105540c03201c8050743d0701c9001e4a007188990400307141d40c1c1508221040f80a10104800501001c40005d000c0300010324220b002e041504 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 540653732 1250 540652482 540652499
    0xd080606180d06020f0c0c06040803090d06020c060403031a030f120a030608060f2a0403030c02040b0904060c02072315160c091b2a08070b040605061009 67
    0xd25070303074003608850744000800002c0c0c3e8500142441c01022003d00c0c0d101c642c200240b43c41c0c00a4031100d83d0081004020501500707902100726020580709075038030030700084c1501c2c0080080c800e1000180041c00346406000404d903150704105416440c0d11184050705034103c2c200340d1204070106c0d00031000d51080c3d402311410b4000d400908540d100e24140000c3c126682c001250402d1340c2215038000601c4c000c401c06c0f20342c020410503d400a50b00d0082c1401682e40c45401200d1403149010141c00d00a030100f400045585c2e80d0440b10280d040031b014244641020b141c820040d000b084961000360064007000300700100e1006900c0841c00980e00f100101003050000d12200d00c0074011400ac002004114050340ca840c41c4001a0603148030f62064004149050800c40840d030311503400310134510440b50860016540035101c03545108112501d420222400130713010300701550311900200101b90100d508020701c89034508151040b8000c88080c0030a03070f01ca000300700441005c2d8251401250283e40244030200 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 540654982 1250 540653732 540653767
    0x170403290f06010e030f0d0f020d0801050f0f04020c1f11071707140a020103060b04080d030e0c04150f0f050607150b090406021309061208090622080d080606 69
    0x202c040c180880728036100b0020908001000d2010b04241e0310084003000d82680c00043c50b102d11420b44007816000c007103610300a1240c1c0041c402c071407040700508a450955995045201004c5400a20441d6507c50116960352581c4924800d040c000182c00204200402c90340501c418605006140c14540581a070713030000c520000820070f4090030070500242000070039000700000c0050003180240000c0041d4130005040e2031454101d103070f400301e0500081050b40c00000d502e23605104541404030703406411480a618040e0b400c41c44d03039030040c1050150380b0300c0707480300c90030a00b540c142004403090540c480c500d080c0c0d0702d140c49c403406401c00300802140c4041496420301003002900800003085110200000910360b440c10f82d400c2c0c602a500054055038414140f02036002412001010322035249442d0b00b90100d1505450041c0816000042882d01e1759901001c9510b0044014402c41d41900182e83c0c00c00c10326882d029078219440340c04d4000000c540110034132031280c1da009113680d1901d603108146004a8 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 540656232 1250 540654982 540654991
    0xc07091109030a0c140d0c030b060d0618050106050d08030f280509010e01050103052e090302010b0102071215020d0212070f1b080316020307170403290f 67
    0x44280041d404981d024440d86040c10300500a144030f80d410035004601c0c031180341c1d918a00c600340000c00c003000203410820b0070341201d42011700c80401d6900c0c40c01142c040345c15034034010003261522403554400d81d1713000825130290b406440200322082e210018041040c08081c4090041e140510014400c024190b154545c02a0700c81c4415140700c00488140d568000ca15007890348454543e4104450070782c00748113988610355204002d201030b500d59100c145d00e4805040703c00b4205079101e0950b80342c10329000c0d003401e95a04054400c104071001401c00074001c20031001c00038018022018001002080c0b03108100301c40d900155501d50b40409110000000d50104607145010340c4c091107240300c0e410101134410f12030b984641300c9260240e09083c00828190185168860301642c0c1b40200e0045901030054960144040800c4400d000c0c40540580c650f01070600010608d000d81c02c6d150b0040c503a550003400031607201c2d108002000a8082600c1d103001e45041524403a98001400243c004000e41c0440e50007 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 540657482 1250 540656232 540656261
    0x901030c0b0c10060609090b220c03180f050105090f0c0402210a06141002030304060c03061509180507020d031505131a01030203070f18090c021c050c0709 68
    0x310503e9607031120590381c00e0351100010642c002d004025051460007443c2c91101c044a41507505901c841034401b18102c0425a0118a5940d401d520400707402a030004440c15039181602e800e1000c00e24014281d000100c00407640c0707508041c08034201080002d03c0301c50106242c2c02070030084d1024000c0c0b00c000c0d000400300d07a44081340703c100702403071804058586000c0d0f8500c03200807036040c0c00c0c128582080b03012998118050440004400a2640d01000f82d9070069400517004ca405c4030301c41002c401400c1540c0100145408503004186425080710201e0300700c039002c40600e08142d40c1082803104645080700c0744070140e045201884500d40c4a680701c40b41d2405a440001c41103a142c00c00308008024045031807580b556125086069035000345100c82070803209107800c0d403951030806001015400c1001500307003400340c428040e514082c88521000042c3c0540d00d810030540f041203900954a40e408014041d2588002d402c8500c0103204808072500141013000410b002441c04101e01c0c020009000f50096 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 540658732 1250 540657482 540657493
    0x11d1c1407080d0902031b01020703020f0604090c0210051b03041202100204060c14010203040c030f0303060b030f061c0209010b0d0603060e06040b0f1302040506030a06050a0c09050901030c0b0c 85
    0x180342c03100900001030b9001c03000503001c2d4551040c5450040342d17080d00c943c408441900c800b02aa400240901903d40c140c0310380d41640741401c0450090b00980d04041003250030f25151074060340d40060b503905441601e240030b2155444140d1002c41100141020004150041000034003107940b250b45180b8264035881111011081171850320101e03085074008900140c0e40300400e400b4010b00e10300884018001d00001c61039800c15640750084580540b01c002e0030306000d24401c6042c1800381d4007860080440c4040241d4925003400d10346540388088606a102c0d23014130413000324101d5040204540d03a580906221102d900b4a400c1c0076107500003924011840e40c81e1540880001c06030300030007510120210041c641402d0514000c404040010190000d40404c1d074200501070a12843d2441d491b9010341d000140d58032550b0100341464040400036041030f04150031b10003550025440410088441e81d62600001d45034410842180403e102c051300c25003902c0000d1000484410080003884044c804541 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 540659982 1250 540658732 540658747
    0x303020a0b04141605010212030603100e101a0a0e130303020912120304030e06160609031709062505040e06220b0306150102030307030b01030e010905011d1c14 70
    0x80c6032a4501300010903109903d5001c11103560100030b411652041114080d0451420402095890a420724514900d0b501c0e0700030144212410301441c0c0d4810b42c44141030103001c40074003500804601c003002c103d010b8121202c0018074500288811805020101303088025150079460440103500507420b0542d03c54010304004144007402c20040104428000c0280d031246414200034200d1006a4011360180d401003110700901012038960f41c01032036120708000742d4450759040c110342c1c040344000308564041442c41400700001002a0542c8070307159840704034144c10760b1070381d00c2a01014080c11042c080b44c0c05000a120900c0300c0340c0c5d0b070380c0c1c80784c0301a008004440003034001c1d070151000311f44001483e0fa1744a450200904040c490558407070100c06107058040c0300440001c1d901c0c40020a1001050396503003030795516a200781c01840305c4a8800c4005d10042600303041160003050f4400ba50700c07203502000181074200d00b010900f410070410f100004401d43e07502c4d03902514409049001040c00c1c1004100c0c49 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 540661232 1250 540659982 540660023
    0xf080a020d060e040209060301060303120c0210061d01060207060504030b06060c16170c0603010308030603010f0e0705090a060b04170a05160e180601050f010c0606030303051b040303020a0b04 84
    0x25008008040e10034443e41010700600416040c0a0b04107070090341040e9060001c20b0f004012802003c69034400000c03203041d5028200e003008440a10741140a05107400003607405800e842503403407000c8540c1c08800700d0b40c1c1c8107803d9076190007d10590011850902041011480c0542c1c4164400c8000d08424a8a401c040500703050580126039405c03e8a0200d00c1403010403c1e0f403010f03252281140005007000d048150016440e40030510005240e2080040003801a1b2000e40215121a001c0c80080c003003030b281040150b4980e500b41c0503142c0107a1814000501440c0d540c045d80d01125000c0601c9845c080c20904400500d4444000140c164803a9a505a0005008100d9a110000d01c14881d910380c1e420419804544000504000e80d060000910324150340404540581140d800322510b40a02c08130000685406911107000342c101850841c0005c207040d055001107100b06d550154001c1c0c04809050007400300d0155001c0980160300c111414000a002440c130540c01602602569000380040f80d501c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 540662482 1250 540661232 540661241
    0x30209060f07030513090c051c14010e15040b0a0605030405030f18090a0905070608070c02030303190617120a140d090213062d080303010807150504060f080a020d 71
    0x110f000600001c2c0183d4040301c40001e00d0007030010440140211168468010030038001c030000d180103401c00034604a00c00980c0d42c0003008210390004c0704003496944000a592074031044425080e07400c1060300c0c100440c54244101407010600805400c2c4150501c1c00855a03a0001007040f507492204001580c21321021300c026046000302044081c0c1c03090412814004045070240c07401c09100d00788007424000131004510003058454521b00b05510703a032114800c44427a40006400b0390180800004d10025588218154900000c1e2990074030084d43c3d40c1d180078904004116841d034483e00b01c61140b0100312228030040031200b02ca403800507d81003003041c0765605a40580103003003031580e0326148841141040c5051744003112560301c0c2001500d00c0c00c0d544148a0044005d2000c000c0100c1c2c28008142100140798030191640c1000c8949075a109c0d9202903a8440a018030041c1e01e100020003243d01c1e10941c100d4042d10225591039220148081d8151003404018251501c01074081c09010007512580c0b08 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 540663732 1250 540662482 540662497
    0x807090204060207090614040b1f180503030a0c080d0b0a09050603060c181c0c0305061f140d0c03021309020414012603120f06030609070f06030209060f 67
    0x100141d4641c035046019203030850301e138810440d40d820004200581e05060960700810b82c01610086a40d0b40c1c20f8002034041b20082c2c0d0b59410800b0b403003101840c0340d03a0021a00c1d01307030b0403036a02c04a1441c0c0c90741c04140d501d002b1245000e0020b0900c0398030500042400001c0c00036602c421a0116a408000f0300160080c03c0f00e80180603107507641c0040100520341080019003107030700780301c0191901c081055522020418840c6d0f4600458144140d08001d010003200a10b035540c020540711078040c0c0380d2610544854003521000010074840040c50302800e0385403107040840305522403204041c030181d001c0c0188180f032800c055940d00c00c3c060340000561140030500c2c2001030046400203c200791807040104035900c2a0445441a1000c40140f0000c4c2c50b0008007010138806400012080000c3c02000340380d440348000e400656410318040c0312080c0120071407580102ca00701c0a0340ca26940e0004296076500740d42c400c07252002e070713525010400b60380a54002c210424010b400300340342c0f4808400d02e071000da03c01e0700e = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 540664982 1250 540663732 540663749
    0x203120a09030b070c1a160c030c08040e0402120102090a03120221030108011a06030109051812070b090309090c13090e100606020d020a03030f0e0604060507030c030e03030a0c090807 80
    0x7038030103080040b9410407a0f1420310a03044081142803401f500b0342108214400002409640390319001814000c1c1c14603400203600496403a6280d44a000b164074524003520203c1c000c000003181d1030700d5501c06000340c50070280e029080c201c0300d600c1c50712585c1942811200300c42c08e50080010b910803500519580c40708011000d0f00d1156694940340c1c015003104c00202d002140401101e000d40d11581e40c02c0100da0440e01c9020b400314507503c1e01c9a1224603d098400204454405e00d03604440c0300030302601402c1420302482c9003296569541ca0b03082e481e03204800c4180d40c00b6a600c0002a041342080015140c101c01c0071f014203032116154003c960440d0000b1309900300e20343c4030002c4c16100184501400000e03000300d00c06801a082d4010002c0d54800e00814014245500d40d2254000310710154030150303070065010115401030416090006c010a802c1d01c2c0d0780f00090030b0600a03440503029000781080810300318029071940d528079030003000400c1c4509403001008010340000a4254007081402c3c080d25280 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 540666232 1250 540664982 540664997
    0x1713020618190303050304060c03020c150907061b060f0209060a030608060703060608070804051504030f030617150604060f0602031c050c0706020901030605030d09080c09040203120a09030b07 84
    0x82001c1c02c0c1c00040c51120909034400c040c00040c0c2c0c008140d030303085544421b0100b03543d2040c08060300607001e2542c683d88144284040d44104035190305260303005062940a4400c0c0320f41302d01c001c0302d401c50070000d20858810301c5000940002c9481c0c0c4001155001c080c801401c1400e4040000e40a0703100b0700c0d000303000a480340d01c01e004603003090122070b030008290709040061500d06800980076241c0100a00c041c0401640001c00b03101c02030240f160703060718200a611689c601858003030080311595002c01d0000340342c0100801c28895007041c24503002d02c0d19004054043c0d4014400108500041149411540f070300d1001501c400502d01203406410560080d54030380358600407900302c8450745050004c580e03040c0414081c0c016101c80444900700e402c030001603a034400843c01030300a000d40c1d61006030548104010303858159404560f0f0f800b920302d0300041c1c41c035038080c0f02c0030040800300983e80654590001200e6411000c00c900c001d0864401504100e00741d80da40c0d0b19034200322002160000c0104548 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 540667482 1250 540666232 540666277
    0x604080114060603040c0302220609020406110a02060d020f04090203151507031b051e0c0307080304050901141309030507032006010b03100512010b041b17130206 71
    0x1007500040c1c0c0315205881150962809840d80c0224004512001c1d004090300c0c6014944a900d0480314099400000310901019a980c0010002540148a1100010074050005c1d4640b440411030b001da06400801840c24051000c10000003075000c014000270451040200250030300e000e00155204034175055413660701c81d030309005000c00076000001100450341c1c20090300300000e810035005201000c03041960040d00701c0500e4034a10b0010b01c0c9001c40c591541210240403068000900b02c1050385083d030660700107039076032681e0558a010b58003501e60f200030048018410401d080c400020a20401051a0048402c403858007007100c42c1c501060b0700150300021000706254211900b0280e2400407040000c00058204170079031102c0781030044041c0110b0000c040303201040a42146070140000504d004004c0700d10b000070500a1038100c885500a600302b00c4c110940d409040300e080d030300c1340951b100c80906c0380a01c004400721a0307004100609407141844002c026031901e402411035000aa07041002030308a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 540668732 1250 540667482 540667511
    0x40f0b06040914070627090203130f050d140a051902010204030f080403021503150f01030e070b03010f0f151206150503040605090106081018020d2003010c1d030c06040801 75
    0x341b03460050255208210f550441503c20f0725010440720300c0100140c42c0d80b074000388005202103050000d13007042c541c805001e0610501081d69015010ba41e00d83ca05400341e41c4200507105d002d140d0340788020071014000d52440032a40300340c485c012031080c80014909612030341c60500415003040c2c107441640c0c000c182407045081c64995003500031250380049085251080100c001074110300f0103030380905080b424501f202e03406900f010162126031000e880d40d841d150701c40d07100c3c150401d1240c80c2c060310400c20005101e00c051800d44054445000f0601c921005412050f18460991007e16054a50759000001d00c40c0e0b011070150882803d6036600ad999040504200382510f074090709044169140076003c11800b032000404810320720404601007641024542a050b88000064002c5d400020000c5600204261804008000208458003d0702d621006061600300c0c1c1314410081c0200f5603210b5070611030701e900c80620320003a00041c05c5071200682e807030229050b40c20540c00300790560744400c00002c0214 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 540669982 1250 540668732 540668747
    0x91d0f03030a05240f0a180c02061503062a04060309031e0206070e150307080906130c170f0f011b0201051b0717190305060603040f0b060409140706 65
    0xb41c0d240400c4070049442480ca41d0f148600e1030481c0e108170a42c00c1408038503152001d01c8801004030841d0204030004041284c40a880c0c14030203403005000e000d00042c40101d120400000c0d0500180080500b50340d4900d0018085510944050560740320000c8220484625002007015000658000c05c40c4195072a021b4410014400c041c850408003201950b603296001510641c071142a1408600b03545040011032400c1d0040c0020b64403401001040100c01d079004217065002d9a401c030100d8459030748582e01c02c03241460041d801040c100340040c04218161428607030402c5a10040191440d800c001c00526141480035201148640d44132860741203445038940840c2780c0340c03500d4002441a0b14060400b0b04001e0722500690600560200d6800103100b11040c180c0c03880c4400b100019591001c0c000b04428000d5010210700c0001c1c20280041e50508295065138000d550056150300c1840d920750b43c0740e005600050035075070003650f21014840410814004046401d845201800d411400c1c084014107e0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 540671232 1250 540669982 540669991
    0x7060c0f05210c04030b13110d030206010e0403030b03060414070b040524040b031e100302030613260d0b060403081b0309130203060405011e091d0f03030a05 69
    0x4030741402003100e009031030b20380300250028205042d40a6600c140ea200c2050245400150000b0b43c0709040102c208014200151010700501340007201c0f0601600700000c0d45204000140142c021070010401c028400300700ca60408d10034280410f076521544042407070210200c0b02501d082100409a5801e1403050107060060800050307141d10340b5041c01d0129605d00c5803088a0101c0e401300300a001141c14940043c0e5010701402031300da50b564102103003101c01000b400c25070760f003656904c0b40114040c184021521002c032540500a00300d5552a080d01300041d941c180416074101030148a01d10000310320580c007480859440004907203400381103008a08884480071424001c1000f048203001050034002030301c004482000c09262402140e00e07000b4114042c0240302e58100070f0303038108100d0b0400290065441907006540400103a070340c42d0340c105039201e8982948201d8030010182480825841e42000203030071040191078400b0104180454905803034a04010700580021040c00050105c1c0e0040c0f0740c00 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 540672482 1250 540671232 540671237
    0x90a110901050a0b030c041e09180314030a060f060521010e0f0403110102070f11030606130b0303041e060207140102061501030e0a1202120705030403060c1407060c0f 73
    0x441d030501001c1180c00d0400d00070303014205004400140c0050240c412a07000e04040400c0e1001005441424500076100c0c0c007a000c0040d0a003c0044240700c880b440480449803d50340315820903181c4020441a50300240031900b0964880c00085810003920300c16078001e0030a50b0740c2c255500842e80a0f030564400c0402c3c041082c40b040001000bc0c40d84072048250890095074100240d40c465180c141c5a410075004403003000d5001140000c2440760481090760814001d4020102501e0503504154035104101c0d1499440340001d19012404005644204001e00c0c0144c122881c190312040305e04440304a0b810b076003208050702e00007405084d505020b460018000c0111b4250700008c0c200000c0d443d0080202109660580002a030380b00f40c2c403907003006061142040580303400d00c0003410604001459142c00d00302520a5403001c00030203500100b1560415008009541094155603a41c400b03406000140020005507815801d1007603d403000801c00c8a2080000040b02156403601816040400b1410b105 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 540673732 1250 540672482 540672499
    0x10f090524010203040e090a12030507090311190e011401020a0807031803080d06060807020d120c031d060f1509070c03050f22090b031f0b0603090a11 66
    0x820a1007246030380d03030980d2400e1039100c042000c0d40100d14500840e484203842da2246c800703125071340c007004c6400e825050050303034100e0030b5008460703069042c0d9806403038640c00640200001c10104a0000303c19550020080240c0019614481d03003410902d5650003c42c0c105002100411040e4004403001c000001c003070014007e003a80365120680d0030f0140c01c10217400c0c03200b00c9013501c200c460100159005150300414003900ca00000c01881c0c0284200d00604020603014800710b20254000034415607260f52580e1450200e80031405100d02a00510030402c0a150b101d0428040f00710116550700a41c01ca104020059881c2c25000c03c120114050450341c5905c586400504554444045840c0c1c400c82d5410801c032101c105103004c454601c901c1e050f071200c038200851284400528090720801c1c00c0d101c0500f024030952905245401c1701c6030a210168554020018a007046040203410203038460b44840003c1d52581002c003050080d031040300c4015247c0c120342e500b0420002880c0010003005000e0f11180c2 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 540674982 1250 540673732 540673741
    0xc0102130602120f07050c040507020307030e010e060409022203050a1505060a0b1303020402030c0405090907150f11010c051213020f04020c0a020d2603040c090203072006010f0905 79
    0xd807079200d007100400004c500002c0410501c00c04009000d00600e01400400c814a01040001d44a070080031085000561f0f440c0b04602c0c940c40b031040ba03a131ba00801840c0601c1e291400032404000d5128100b00c00b4240b2010000d00da0220000301044d00450240c03000d41000d844030b01d01441281c94410070350072514a003009100711902c503595245d0035981c0b0301c7c0c0c4c07c60303880300741c808803401c0032496030310080d030280c000800c2004401c410406001162416140c1001607166903950715115a968090525202482c0132040c80c040d108185c2c80a0b0900701e814a80422030818010500307403840100b100f00030442c00185404d0001400111641c8010f2500c00724062030034540c0064a40f0080ca000e07030788141c0d00418120072020080c0084c500250b4010300303404d40d078071407850001d51030700d828460150348130760840342803515079611400c59205a0f44409029055401d0000744802900040d001004010105403078400001c00300c50404204c42c0088014102e642c94000c0b1001d03448215048009034605007018803 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 540676232 1250 540674982 540675013
    0x30612010c0905060d0b210d050909130f0f03081b0304170319061806150e0d150e1f021e07020103110a0819061d0402060f0c0102130602 60
    0x1e0b00303030707041141d40d0f40d618110721030b106014268022580798045001c10b400d50488801500b0004000700e22000c3e038800c80c048140698003070080c030750603a03042a0020006255044c11520048220380710395821120080300e40c03600d034481c810b00325040300400e80c08020310145845140b0750310844080d0000442c9540ba0070340d1011900a61030202d00050132003c400b2a080212180b1086081407921200b005240d907642e06040107144500326100030749103000f2001c600d500e0424960540d2070b00c0b03a180d00403a002c0c03c2c81448400c10318020182c4410803070031a94080030403d0300403d00d0b4050030700001c20b50004401c1c0704c810380509881e80c140155104000d010802d803084003e5285071041c051070740307440d88080c1c00140d01511052043e8500703988000b820614260300050064090501440b041e003500300303070030000710841d035050248510b02e140002d48000305202e2040c00c558082c1c0f003d0141c4e030410741d21040111240c0c000f1f110004d4aa500407868666604041d20200c00070915440189420401340006 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 540677482 1250 540676232 540676247
    0xf110a0c02090a181203020c030c0304090b03030406090e1e040302010b01110d21020f160c06050f07080d090602030108010b030c09010e0f09011134020901050d2105030612010c 77
    0x300203005178410380c501c0302d010394162003001510394180d942c1d0342075204485481e540207008071807845243c051015111b0070004155000c0c1c4001740c5035202c4080c00c08244da4000b19008008141c90103a0301d131512075402320349000c1c90141c0d2080e00081140140140003500b0f91000924040340c81d400740100184065020644e00029084903c41a0780050f4000140010b807046410340700800500160710750221640c1c0316180e07006da000d030410003401c07070710b4400480d5507100f070000755010003400703001850100d01d0240007440030404920000591810f1030780e684040c0d80090f840b03035400d41d540d11340200705c6007000e1001c111448022100c4401560401c4001400628050100383c9850780160018404800c250f00c81e880741c030708544002d40c4410f85001040c10000305c0503500d0f95011080ea1944110b00034400a85c0440740d8000d0043c1c09a81c00c0106200300c10079510015245083d1200d81c82c50842281c070209141030026984499807890144180001c9940c016840c1400e6858860740380f142d07990002c40c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 540678732 1250 540677482 540677531
    0xb060a030b040e0f030304030212031005090c07020d140c0414070e1203030f060a0803070201080615090d1202150411060d06081c0201180f060f110a0c02090a 69
    0x10001811140d80001c6001440c1083d100e00035803003140c03003d00c030003903000006d50710480c030a9081340c120700d07048807035543d050009031000c40c00c180400006010618002d980d4942c00035034252100e04003000341d000502c1c0074131120710a440c0900b03449800d020b810020300065003030050943e0305000c0640c81100781c00d90313260010081420451251040500d0366264589a4a44230700c41e41180d440f82042c0300d80c001202000d4949034850301e1818030000b81040d0200540d1401034058441100c01e943d10000d00c10400a0f450007010061020006d0f1211a40ca520221000c28003e11540266400b080000703481d00e580003d412001080110800c00042c803400610031410b0700039510a5203130141380b02944090311281e0403044050050003d0000c180c0f0303440701101840c10981d4001d1000b614845d000c11540d00000001422602041d9020808135180e60004010900e548500141d0395480101121958119942c0d441c0003c0c81c4290303131819882d14641440c2c00003d003160030480a00085201b510b813180352075 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 540679982 1250 540678732 540678737
    0x18120c0b0d060302100e0109060c0f0b091f09051213090c030b0915011211040515040503031c140105130f061e03060501090209030c061606060e090c040b060a 69
    0x7000c25182201e900000700566010f0481c42480c80c16100c054186000d0002890010310f50040c0060341c20310900441c1003e64110080c1500d540301a240c03c134002900078026002440b90784010310300c40c11510646807096600c0c0c14005601c0e90743d854528100f00d140705601000180a009120344a4007c60750b82045441003e80051340300d1010f1016400b61401c0c4030500d50240040c4200210313025403034030000b42030b102666a42009244a141d01040303600d82e07202107505000510043c0218105030741c83c50442c0d415458018101561200000c0c5554400030700c10030f012502e040d9102000903640900d02020748440721030800c0b03604000c0811a502c140c0c3c80d2603603015440700d98042c03107011103a00c640003420401d8403a2207884d40d4504091052015880120759607890200001070b4903600d80301ba0b0b80c000b00c0040141018002e04410031106800c4544040605648c15411324002001c0f44107000c014440d08e01c41c0c1e000703441c1a200080c10640d1821a16000d00c1c240b5400e80d003103a5405003200da5050090 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 540681232 1250 540679982 540679987
    0x12010e12070501060e07023012010e06030109030909090c03021005040e011203021c1e09170c0a03030c15020d050417070f170c03030414071e0302040504080c030a18120c0b 75
    0x240400d0715000c40808e1300c00780300e4000540c0c0380d160701a032130505060391001c0184000d0b54550780241402c03103000031406400960b0500313003030202c1c200700e40100c51a6801020403504003903c98000a0340602805070350404194000303005c102010388019002e004104211303121800030340703548001e52101514003d003c0c000b0720000001514038001d5483c0c5098403c403854172250b4115031440030300401032500449d0344800900200e07035128080041c0600701004090302500130185141c1c4d041d2282c286a03c801c59806018804034003400000d48090b04800c20b200c6004502d03400c007420240500c044124a4190110040101c100801d4440d040c854500c0d0303114110914900c0b902816008a01903a44014a035010010601c0308cc04900c1c404201864082d10968261583e52a1103100380c1d01c10400c0c4140e9000340c2c14040015144c0b69000647c094004e040b8030b45010001c028180c107503072003c40440042a9007295940c004405d00c5040c0e800313400310703980000b07800b03003203480d004503904c01c2c4c2c8640079000100 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 540682482 1250 540681232 540681283
    0x11180c090a090c020f16030503041203020f030a0206040312051509180a2a051c0812070c060507020d0507080d14100801050c031512010e12070501060e0702 68
    0x403040203070001c1800d4042000700340b0b201d8000949480c6101c1c80b142e00b40c415031031041030661032602032000300c9a01900035841c10f807900c0500c0058041c1d4072400c2d410350081d00f00100040005000401130f000c010340c00360005150500e00500181e80c0c401d11401240d24240030000090200c0d401800642070480da10201591580c0d44000601245003c0000c54020f0500c0f80c010002c0c411940c0e811201078007807914451011700c0e00c03800341168500c40c80d5804114241c05408d80d001c100b0f0052503080c09440020318246c1e150f070880400702c1d415941840040c1844954000b800b01074890141c0110552000e40710745000a00d0041080c01003a401030410400001c0314942202264888004154085101010f5207032030b580c030040c1d04546201d249607039424000050f401a482c2c0045030301c030311040b60503005d4071050041400a100d0003982112040e42d83e40f801502d04101c100003160221050004441e603c4817640b8200382554015804082c4841c81d04040c40348054000c0b0b420b11402c1500c00c000d4500021 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 540683732 1250 540682482 540682489
    0x403021c300204080c031b0a03030507030516030905120d0206280c030b011e0516020609030a050c0307080a08030601050f0d050403020a020a05090411061614010911180c09 75
    0x20807014026407840080c00003a40007010808040741c020450980700110307282e2000c405044c0f180c00c1c0d601c0c1d220141c1030041c030019014038081c00c895406841c0c564142144598607001c860b165900c19000300d040b0346020401807030702829542a01e44000080c1c00010160300c8040e503a803602a217100d59101e01d81c142c0648850540000400d118002d10b42400a01c55542000c1e00904900d0b101d41d000550602c000203100e2002d004100000350241c1c0c4052504060300c030400701c14090404200e80c0710804104401d0a5541040a5503180380560081e000c09400307c42094a4101280d00c0801c03503400511024010440c040241c2c6d500c40002e082c8959100c124580420f250300c90b01036010b072841d15250602c01811360005403c1d1782c26200340d030541100340e290300c00c1204c0c80100707c1c0c00900010814401240310f05001020307010110182480659411641d9038035503a80000c407214400c569076640186080c072540707202d40d54881c04e09884c84502d41c103aa1004e404000001010382d00e80705000600014180c9 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 540684982 1250 540683732 540683807
    0x60e060d090f1406010f0b0a1106040b010f1e150e0d0309090501090e0a1103160b0c0c10080c0c0a080d0e06010512100b13140403021c 59
    0xc104800402405295240031114180b00b07070025a41184603002640c2d00d41c1c03000603414107076031200c5c284910300c038500315180c006680072054850402080300420049000100809401f07680720710036150256051600040707051100e036000201c3c0000103a001e680256000c00550300b0303078000183d8545510710014081d50303019030100394240c20400c80219070f024154400504000e550b1000000d100c07036640c030301c4108141c1d4608400d4810300e40202c00b00200040220f03040c0020301c1d0000d400c0d40c0602540c04a4440d403803006505c285040140020145641042404821145a170031208400e040940000090010000400c151844080040c84005251040003000d00e15617100c021950303500034030700c00c080140c218103002d401c051182e0400820540380c80006250107c0c1304000134210701c405040e0090182c24003028070358024100d2000032080d00240d000790303055400040d1803054a800c0c1450020b1034015400174455042d000146000107895114000300d016041200340103c1c110703062905082d100 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 540686232 1250 540684982 540684997
    0x402040506270d0503040e06060304021f090b0a020d020c04061413020d0f1a010314070c0c0f0306020a080108061332010e0f0c0607060c0504080304140f011107060e06 73
    0x6203410f051000c0040001c020030688415041d06599a00c6540501156000580b002907101c1d202e05802c0c0001011100449070716042c1c3c1c500f0790f003000e54030401c2c64683d42c041c07072882d00180c00061910002d960100b20700d80c00d490041d1420422281303408210401c108810706075500c115000360303808200c002d03030b5010350740b0169802c0780c00c10203452840111030042001d102402851780c40c2c40400750301da43c000c1c8147c505003400c10703691144550711000210340c4d91118000c212002190f0240c04130b00c000d542d0355440c005d584240e500503640d480a45001c1c124440c1607111000070307030100703081004041c3c06980c07510103039610403500121084481c504803512071548200803081a03242c03481c040f21a4054008200c012450b03010f031044007080d041400e071120074000c4042d0300001704000040000d40e00c0d506c0302c034240c03d0300c0c0b030141c3c14079845440280c20340d48580d01c180e04440368400a11075905d400c0c1030100c101c000c00d081c00240c1c9440f07103124a8842c0c03040d00c20300303091007201c054520542c3c030b510b412100d00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 540687482 1250 540686232 540686239
    0x30b060d020f040501110f0709110705060c03100b0a140906070b040c0915030503270a03050105100b071113110f03010f0501020d121806020c0c0f040204050627 70
    0x94a01a60500e03915030450700c07070140020741c2220109034802007c503c980d00b03041d005016140d0036040042c45000b41c00c00b07642d803860010b008c1002902044091103964082d6205654a943d0390400b640020329041c80c40d00080c0000e50104a41c20443c0d411240c580d968441e822505a2500c41c5040060940c3c028004003600070341400c01040100041d0502880540307031304040802c40543d4086458480e030400780001492940100184110170082d40d10a00200143c0c01c2d02802d864246004100e03080b8540c3d00407038060303440e80148032101c48074076040740240c08054080d6040a000c0d8469505550318000d480d4094500c0550400610a058000c0e5000c0c48420b15441c2d074641d031944a07010198424422003050280041c4041350942c0b000c80c00d01114001030b950506045002c03081600101000c0340f8111410b51004040f100040d0b807400a48415200c980103030204030100011f0bc000c010804d80304512480c41048280181c1d590031007550940c41c010900c0741c1c11804c0341000702c4645240031410a0780f = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 540688732 1250 540687482 540687487
    0xc03050424020f06070507081305060705030a0305011508340c03090801020301030c030b070e040f1a09100b0a020f01110a021501081203041e0506220c06030b060d02 72
    0x1089120540c0407100c0c00d2540c210f4480c02981810035888003420b80341d142c0000c03020400310010941100c041d06040c0303000d507680000940c0e5180056903a912601044841d41c2011411101c020b40600c51035004003000786a05045e8210714074002d0072004001c0510050f04802c580c2c0190302c03440d1021603800c0c03405001000c142400f0702d807400340a06c1a000c000f280004c09081020a040d94103009580c1200d0b4050390105d070307040c00c1da940c80b00800b400070700010412002d8000c0c41480d5460380aa0036490b000302c000010191010781d5024040c0c1c2c4080002401000e5a409111160400b09c82c06c9003168101070141ea01e890f0070b985e080f0b00380700b480b101c0b0002942c20111200030f1030203803e00030518a191030f000c81d0702c460070141002003003c10901c11000301d500004001c0442841c00e400942d0b210384145d002402d4100380c1040103080e00410314090701e02d680004100131141c484143d0380100b10f81d07040491a40c200066440101c000c4240c0036074000c00d900c820f07a0b80d60f6900d40b9010b440d11000740180a54 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 540689982 1250 540688732 540688769
    0xc16050a0f2f06030a020f0f04090603020f030c03060703020a0905060301081e0a0c0501080411090f090721021e1e010206060105280905060a0908010b0613060c030504 73
    0x75010408040301e00d00100001942c01c9440e88000d404010201c8081c14040c1141d54651031031009402c07448461002c03050800c03a1011842c0400700a201901c1e0800000500d903085006114140700c0850919000703510503a440e2203550780014802d0351140452a001da60b0781d00c01d403012920803202d68015500310a01100101c0c6003403011407861881c00100e90f620000c501c0c3e00070500e81c0e1350208080907010980800c410b0001754407031600c5981c4075004403404801001c000004c108841e42c01c440c0d0300b42c00021081440343d0181c0900c8031400500600b404840c09900b982101100d1080c0f80c0780091080728009060440074403d18085040d44400038003844003844c800511a01040e009200c40340107000c0d58001982c550b0007002550360704016868041e005800782241e041000000420031800e20804001c001001d079960801070500c1c1c5032640e55040c0251801c000780b0300f59815175604031710a03070040c4505103440b055001e114007103c43d240340101c1d200d030a508040e02c443c8141e8108800f000c00a985d8035 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 540691232 1250 540689982 540689993
    0x411040216060b04200a050a0306180e0601080705010e060c0109020d031205070810090c0903080c01021e03040803040b04110319030215040b2703030a0603020a08060c16050a0f 77
    0xc100f611410f440a1264480008903c0d21449210414070302c1c401042c012058002e204038040c0886103a2818000350464454880100f13030b048210380d1010080c1c0b2041692280b6006001190050840a0007849842e04040010300200401c10740d043c0521004600644440001d4121001c03a64002d00083c00034611800c0040140c0801e20807024035034100800318019030302c5044483d124107214000c0b070207494200001980038003560103c082c10095080004030205241c20020030000e15540001640d4035100c0341403074526069101e006c080805c042c0b00708004590110100c940c0568003000942540d40d99180c501c00c0380b941201d03090b401d845140e089030b440300420040301100300c1c003035001c444c40884940201031540400b2100242010b9140c2c1c04a10607000c41880c582510110022203042c1d040e001c1901491074004440d0341c002c1a8680f4001c00c15428a2f004940c087c280c0803010341007624180041198911039200309130711070390420080c07034207110051160221251744000315000308046030404 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 540692482 1250 540691232 540691241
    0x81b040b0607140d0e06090103020a030905060c030901060f050f0f011808011508030a0f030b1203131e030308071d040c090e0a2f130b0403170909041104021606 70
    0x84600a00c60071442d0304c811401120100e207901402040f00d8a4100788a004401940104403c202803548800c40000003500038804507200e038820b100d0722500c902e030209089080d40c500b40d0010012030b2800e50309010a444000803520682015641100001d100030b0040b1505c0135400304204031034540b40d9010400c40810b42202180400c06d01c0003081e000d44424000392a80304044101011072616030400c3d0525010b50804540910014609400c4000c0c140c070882c1180c2c014848011804c00c1400180b01c405051505c60500e0300301c2598070058241541d50260400030094140c03801e0101e02041550500b000020b4801441030281082c0090b0b42a084c2c05401d6001c0e501809101144282c006140200b084c403480000c8111140310104c0b06449807210480410807443c102001a010491a101450000b070418020141011281d54507460760a01c60312000c504a803501844a04002c01602552030a6031a0b410070340011019a42040800000c1c1c000d110358260743c2e4100c00c45194030340501074035502 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 540693732 1250 540692482 540692513
    0xd06031101030605012309040c0801030b160206150a03080d0207022803060f0f1503030f0207060503070305071e1d030a051e030403021905010315081b040b0607 70
    0x54040042940019001c0c0e43d0507006150000c0c42c035a20600d1440c141d80002d039245481e01ea103281c81c01000d10042400d50382c4542024012030b051b240100100001d0100320f961004100007045007086902000a444900c040c00d500349030281c0030300c0001c1658030100544d000b1a0311401065a8812207810030b00a508550000d86c85414240c0c90810b8000c0581040b20f402e000ca2051940e121b0b0441c0d4034800100a0010a01c1d2b0503a036582c2000c128180340e100d4088086009504811100d10b5071400526038885020000300b1900121810000c194100c000e4981100040c10b002c03c00b41c3d10002d00700eaa01021a001d5400c02124504440d00319410894810f51002c485c1c41425043c2c43c248140b41e56100440c60082c21035101d007080d268004481181d00c0160f28205050743d02e881d81d80e40000d0350b4401c00c001080c01c4000038a504129a681504c80c80021140c050404e1003141d280103010354644544c04590401c54065024004407aa1030745d01101c02c50400400158071608503051034038048040c2ea2 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 540694982 1250 540693732 540693743
    0xc0e0f01060f1103040b070f0605090307050709090c0501030e150c0a0905040b0603040303021e04030804052706120a050102120604060803030108060112140d020c010207050a0f05040507140d0603 85
    0xc2c502c4501074031881642486860320300c004d5280501e0041350450310740c42072030141d03080c011003944640019010b01030a401102c000005680740d403091709209050420643c071903044185051070940002e900801c000080712400d080001ea0b15072814511424015410381101c00748000c101040040c0b03040c00301811400e650b0784d41d4a5031094650007031004030f0b81403d10f407640c0040c003480042c0010f0f12a03001011a15800300301c0030f010304005900070026800c07540045849030000b040c00d001e107051514090804000e404116052140d104c2c0200320916009400b031406001c4800d05810002c000b0811205e032141e000008642e64078000742000540752045c0d41c0340307200c0d41c02d1003c00aa40d400000a9a0680350703010041c0c907090346420100c05040c0d0000c0b000311074844c50301441c224094030502107840303403070443e80145c400e11644800082c01d018094100d42c0c4208103600050010404c580c0951059a01c191000a0241c44005050b80e00e00102c100d0080300200014510980c041e0642200048a1054 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 540696232 1250 540694982 540694997
    0x50a0b06030c010c0602180d060e0c06092215030303050912040f0e09100c02060708090f0c040b04020910200606010c15060b0a09051c050a0206070c0e0f0106 69
    0x1401050b4451681414450006110b2403050001ca0802d500800940b80c20000c0f003507484000901203003540340044802d6030110f507104080c8102c1c1c0814020780900003c1144c00701d01d800e8029001682c0800d0704080341420b08040d0b24040d0040c12260f100e500881070458030f411400303590f032500801401c0115010326450080300581e20080e5101004c0e40d054403400c0349043c10301070a1220800b0030010080400c2e215100d1821100390441c02d038440c440800341c0d294003500e66440c0c02c2601910b00207000d4003504190f400100310041048001ca040d2040321801c66001ca40c802d2a900000d0280c042d2560342a40503e0f41030180e950150030000d01303c0103448003841c1c1101c03140c007001044d8441604842e00d40c0401d2014800c1e03000520850721440502189000001e0681d0702d807403a90502e904125001c2c004500c1d040d409000524128003444e41c41c00d0311400358a9101c107140d03980c6841d0480780b54000c2c0200404105a010048101500d40240140a00f2032410386090080340302e40309000e1081c0d00108850 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 540697482 1250 540696232 540696241
    0xa26090309120613120509130f0c020d141803010e0c01120606020a08031e19060b0306060a032a0309060617070302012006150102240402040c0c050307050a0b 69
    0x401d24078400c10304184c00c002c20315815160103540d40302810f4030710b040000821541d0748558400500600810400c0c0c40054002c0780c04007900101c0d0300d580e0780c800c2903610003d18400120340c0101c03160801c1d00001d0708613031100e081141d5800c0c0d845404500e43e0b41542800c481d020078a01c001401c1101030800d81c0d03000b010030400121001186c0c81c0b070007a0001078000710620b001140d0700314000c3d900014050181078a07044c04495520100d01c09070f03020181804003c42411165103240980700c040c1c0740305c03241c1c80d01d141044000100184241c00c009000c1c140c0311030525008106458000840d1403007069080703580401c8010040041841900c1112043c0c945640400c04c0d038145c07941021200280c00080c4941c9040d600150751034649001d8035034030781e5088000206440e400303001e002d0103058802e450340203d1200c000017a0034900d01100307469110050208402514605240c20382d0041c0d01903a002a0421a8540844800442ca01c000e069888001119000c0000000e0303514411030141d0880700d01902c2e0b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 540698732 1250 540697482 540697519
    0xa020a050109181109030f060103120f020613051603060207061118010e04022101050a080c060f0c0a02060a05070b0c160b0a0b0a0e0106110d050a26090309 68
    0x1640c0125100f402d0602c000780801c04003680000f40c84407504035154280404080002e18084143c6004009038200000420402010844035455150241405200200c41e840000e40d0f4070382c01420200d070107900381c464906111092007502001c600c00d000c50114180c881c14070901030b40c050b50044420501c0e045081012015401c144c0d01510503841400c12045180401102c070f00700c0300c07464039078445d0f82000646681c0780d581c1050840e080c864949503942e58508400c1000018a50b0721a6119402ca44600120703551160110307980c0154140d080c40d15440c074550000d04d85020b060000350000c50010b4510061034211001d0078031640701c0c00c00e101140e91900e680e219140620303901c41100001341c440b0f000005080305001513001803c0394000400a18190008820040907846218140550801400700560040d516071440311490020724401c1048103006201c0d10982d5548010002c509417030341d100c00c0b04001d40f18541e5040b005400528189401c800391651300c1602e044d440b41c80d94082c00c030010742 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 540699982 1250 540698732 540698747
    0x190b01050c2d1507180e01060f140301060e0103111e03130813050f0f0102101a091e0f040f03080a02090301150603180b0f0403050d05090607030513121107050a080a020a0501 76
    0xc4030081070007040d0f40380001c10741e00c03100f22703400b440240000b4100384502d00505902440c001c140c0c903548c141154100c1e50005d8115098142c100301c010a04106143c4011071a007100e66000c40c035100c60a50f00d0f5a19000081c4603924a040100440400507410003114090001c01040d40c07800c03900034080f1207040080050b01035200c9049400740e0082c10b00b240c05e10110340c0c0804541c0c903012070000b02d00c1c01c50200080aa100c1100d04804020b1001f01d20307080c4407400003019900c034081842c00440c07400d040d19000b2010214160007010824084002000020b464041d40c3c014807025009200b00c85c03140d43c1411040081e40102d00009103080e40c10040110700f00c1e003144e089500500d0199490b240c2144103001c1800007441a402d102040100c04040030300ca200c1c961107522131001078081428250030040a54101404104440110310800c0001c120031841c00705004441c0e0806002d020741a500703207803d02d51154800c0e9802404510009a11078002c82d920401d54400c0395010b02058680e401551610b = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 540701232 1250 540699982 540699989
    0x7020705090a06090609200319050403030b0d0506090d1701050d0c082b03020f03130314120a05013206040e190b01050c2d150718 57
    0x1644001010010350400d070350602d0b0016024880071030810380319114242601c0c13959102c10103095440007100042c0b204001d1102e1826002d5001616508003540244d81e070080b607400d45d03d8001d9461004c5010103006e1b0340441e21625010b4080a148072060030b1080d1150405c485413000d80c01160b81d04c2c2c006074890a498504520404414000c0d0703401c0009100600e00d540c2c40807907585007220b1011170080070030030003407000d0130602c2c4005a10f051034241102d24807020380c40d1101850b005000e0030281c10b10710700540f03038031003084182403502c09032a05086804030041050310003810b0000918000004491801c01d1088000400501c12743e43d0b2503100000f1a600c180503155884580c00303440400142c1d900c0900c0f5030742070007040340c0e061a48401d900c15000c0c4041e9280025524007090b045056100d502550046000900345a8200b403150800d013512440808084542c14500401455a01c40207121084481c01c0d00c000b240c001030208803000500000540b001c40216001401040c5c03425001c00ba4202034 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 540702482 1250 540701232 540701237
    0x5101506080903360a030c050d0203280209090a170d140703060611151b0c03031f0e04171c0905010605040c09080c01110f0303100f09020307 62
    0x45290a10480d84224040d0203194030b40401c02612096103665044d030031581d401d00c1d64a40c1240d4595405032045550004d186010b160240340c204045a243c2400c031044820654200c060350b0382600c002420700718000305009800c03800c42c43c940c03051004498204010b1f44255096111502c8001071165245400b520051031030052150310700b403441804c00540219850080003041e0b210317019101a45200c004c86104000076902c070010400294090040940c02d240350000d00402c1c02080c02040c0c40000017818550110301c5442e00c0c10120004008903034225030b83d030054a403203050080d80c04c0c18038401140020092030a20f040840e0b034000c83c0c08030034020766200c100140100c031543d00ea140e058001c0640a500001d40300301540400c801402070020003407080000107071840c10001088111401210140c040201d1a0800d000d5510b0016007004020000d00303168914624903940c6500d07044c01d408030441703d400044180a02e40320951030140c00d40c1c0c01b481c02d20f841c194030369100701c04900044480070700 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 540703732 1250 540702482 540702521
    0x1f0905010e011205031b0c18061e1810170d050703030b010c020d030c0b090c0604090905190804030309060c030509010c0206160818101202090f04050903070510 70
    0x80ea580e00007980310340d144031307100f42d038103060b000d00d40d00c20444500001c60b80c1c0d50b04000e50147c802d1400c0d00c0050040c1100e000e403120320781005004034000380c5018000d480500c4201078900d005035560315100c145d58030700100b00403140c034000d0300040840ca0359114a002c4548028050f150302c0c0c0c00810400c421000a681d12400c1450b1034804602803e001007180b414490a1413010000d07890302940c0c00003050203503c64848040c030529041d5411071004003c00b25503001810554213580d60f2900b00c40450f0708103000842c811000d030611504200105180c1d040035401c03e1105010050218007400460f0b00035203a4103507543d507540050380c24222013800140080d1040112482e9580500c8900e014140094111030800c09101c0c40100c40110240c4d0944040001041d01c03402c00b2030701c0e490a100080183d40c4420b444440c0927000c0c15182d941514401d5858000c1240007140d101c1542101d090b0400502c144440d0805803031a6490f40e2101c81c0a0741c0314060b11107280c010036410b00401c44046030300340180a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 540704982 1250 540703732 540703739
    0x270f01080609070c080706060e07091403121308010501060f09050402040b0d05040f121206120c170109120908061008190302031b0c090108010c0206070c0212061f0905010e01 76
    0x41e000c42d441038044440300406e01101c80031031510f04c80c01025120b400340e103204500304048003402c8559a0740c031481c0601c17200005245252004100300d0714884481140343d440706000e00b00e07a685d640c0785800c00d156a41c07821000084c4503a101341e12410f50071003601c030811101c0e00c0d00d080c0001d0b8070031400707107811080d820071043d400791405500c10360f8010701a070070350321740354450755514802d5006042c1c4540000d031038034a60000761b1882d0f209050042506405400240c8a42d0340d903100022544d00c00c156103101016400f540800d402c2d00034007155523004824100035520307440003030048010780c001c2c50030314800c41d000601079490100e00101034074288070043c4036403d40451a03442c00c0003110000c0b0704600051144404023b90343d0403480340b41c0c0c1c1160203420207001a505100c03c0c418141e204c1c50302613061110b134890075a00441c603650407580d5840d041d9424480c60021600e8544081c182c46001c0c8555010005803c43e040d0010040c3e00e118158582d40c0355440f00d400c0c0036200c0c01c1c0118040d01c040f020040 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 540706232 1250 540704982 540704987
    0x11030a08011208070c09060518060906061b0a050a120c0f12050d1b032003070e0d08270420031003140601030203151608060303270f0108060907 63
    0xd02c0500c541a42458962140c4c1d0350940c00351242d001821513a00d51009104924110321030a0f45d00c0074440b6903055500d0080001550032001500c40c60003003071b0018002c80030190b0344e642c1c95a58480e40049038a80685440c2030740d84c0b001051020744000050800e09003030782d41303d4020440c1040c0c010710703102c8450701c0c01e480f003030b80b280f002e5007010003404000c100409221219004004031f884004044580b101031000002c0d041e02c42c00c0c1010a08420244e400500b106102419a50048500d28007808454520b20201c0d01041035180c0107000b03480041900901e81d00485c40070680c0008001300311a0b81080784050005466141850005065921510400030310b110320103035a0140005142000860b925244d59051580c50616984103820803401032003941001c1001008264094070032020740d18003401d0301d006e0b000030420800c0402c4000fa01051040e40c0400035100034a6200d1000703007221510844c00d00d00c0385102c580c00c2d40614076282c28240658000c103a11845a44c01810180c0617a5401404 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 540707482 1250 540706232 540706259
    0x3070503131202130e161205060109141603020f0d0b031b060a1b06020c0307030e06120a09140d020a03110a080f0c03070506071d0f01200c040c09050111030a0801 71
    0x86108001504002241851100c4010b040700100d5400c2c031f03012406d0150070840160032240180c2c0c2400c4003a4407890080c440c2c00e81c0648003086006810800c000d04601030b110b0080031541e07905010404901c01006617100c00b142c2c8a0840c101d440b40d40450100356030058000b00705552041061150200301da000307000841800041080a2401440c0c503620300303040740c0050508200f070750b20100d441404c050304100e802d008050700700c4203c1d0400121528032222004003c1c03050b00402d032241c0601081002148100a80c440281e00369004c465080c040203540310b0028400381c0008200f000304908613080451030401070381e04041920318042c0b10b000040c0e141c0d44091a80c88207031100301f00c0c0a000c0303402402003e001d00da40c1c1d5600c1c2504024440c174441d40107500b456a40c46038003201c10f00d0600d607800c0011900344004110b40401070700c04104c80d41c0d00b42030785420440d410604241c402801c41354030905208c15a03400341c0304c0c1503062652100c0036a40340a0040c107800800c540c480140303c0704060752003 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 540708732 1250 540707482 540707501
    0x20d0507020a15090f0905010b0d020904140c13060c05030a0e1c05060627061c0f1415040b011217130501020f0a030804061505030307050313120213 65
    0x101820b1681d10b4400c01e140070b041c8449500041c01c290802c1c456501c084a02c0c80040074410780612065050140b041c0041c45030501c1e29000603400580b444103520380b9040140b450822500034204d514023140208065409581c0504007040282408a0018002c02145041e550007200450030800d43c3c08051320403100344100581d02800b800d803104a041d107080104811584224050415070400006005403e04007040c1503030029100c519980a8039020031509500c403000b100e8440701000c1c00350012a030110610405021024000c000d04280116881c825807414041012203c42000046241000241c02d4074010044200007004000c0348440220f480321039800741c240d459414a401c203040c8803a602a400401e0132090030700b01000349613018454401c0c1e030a003410203010f14014a950003030003404002c0c001868196101c0190701c80f011071840c0c034000b074107010b03084a80c1d60354241855640d90708290f00d10103955110007008181486240314245403240c0c05001021801c1040504001030000b420 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 540709982 1250 540708732 540708739
    0x18080703150c0e130b153a020c06061e242104020a090501150503040f05190b1b0a050306041410031b0602071a0f070602030114030d020d050702 63
    0x190080c1c8503500c4c100c41a0410a011400042090351002031020036446001c4e108045071007801212070352140b1850b4201c0300240c4041a0003540451090000c20802140c80c0c001c0043c8003140300e480c8081c2c0012090b010311002c42c2c2542d40c08200c10140000c2c42380c403225950308044902c58089045502240100d20f50030b00d1841d05081110038600510320301840c115000e2150311120902c820350409402c0200036000f082400d005941c10001c41040301d07006101e03038208000b800000241030101c42c0c2c0c44d060006034020291820202c4201c41d85030038800116050360b030403000e40302080d44400551510020043c0c0380c6c083c43d00f001c0900b081503440f500000c0030aa08291110800e5035034080c0e100c60b061040c140d07004409020740c1542003061521348103401d1060550020798080c003800380c0004040301100c03000135a503010001c3c40c402400040c007030700e0101d0308254800b103802c0f000c0080d150042c5050f910f44e03881540c45125a8000c1580c1c55400000203005038201d841104002c0f4410b100403c1c0160015 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 540711232 1250 540709982 540709997
    0x5070b06100e010f0c0b0406020706050906040203071a040302040510061803021804060209030105040b1f140609030a0b07051b03090d030302160819020d2a060b040c18080703150c 78
    0x68440e1b00006d602101e04507055070380000c510041007035038400c047c0c00c103011100411081ca4107501080e40c4010f10701030b004002c0a015115000441e203001120301965001d8001d01150070400e51031401c903031440c025003002c201c0d240b402c014400d0108680d882141e40040868800c3c44083c0c11402030120007820640d0038580030041080039403403d01405000e81d2040154104901c1d200c0c4001e460141a01715087c1d81c9158003e04112003c40d4500240d074100303040329103558489007100000e03c0c1c081b41d41c800070040d18401c1c0030000b01940001c05440c0c41100015440390032500c86110507181e2090341b5000742c1c48504002c50101291090307028140042d8094681d1460a60f41c2c1c0301d0035601c2d08043c0c0001070385150304860014a43d814002c90b55903618508003000321200c01c02c500e46103403080d555104103440b1072002003018024140c1209070445806042003140840255005202181032544901c1c42842014001000d2000092500c21a0b8010354085a40401b041c0c850003d030459030b80040800049 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 540712482 1250 540711232 540711257
    0xc0621051306150810060e0f0604020c2a0a06120c0201020d1103180307051513020409080318060108101808030c07110d11041d0d05070b06100e010f 65
    0x30744624001940f44401c03800503145801d2400e4a81188420044410390425608000070381203170040b06d400000c2201c1c41800750b44c605010500034051071090028510500c665000354900c801001709003807078a200054240c1c65000c0034014200380a03c103080028039a8122040d81d4906035002c1211280ca61001515020825580d5020342e51011000302c041403001040c44500c82c00703000c2c603410704058813011b54180f403030544038141c40c2e44400051110300303114880040c2e084040060540b001c0745c1e00520400040c0701c503047c421080d800888003a008510092030200741c1280001d01c3c6412110354000426000b40c0700d09113070b400b03000f000c48040719100c5a0324208001800542c040c1d03101e038040100258031101c2c01e00b092441c8049002c441800f403102c0c0141036010402c1c21a4200958030261800f10700f1074541b0202103698502c45071741c042e2a0251101d00200e882e0300030020903a49000c0e007500025030312040308000420103a94081030100341845c4000d03030554003079007280c109520b090070403808142c00b = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 540713732 1250 540712482 540712493
    0x801050c090406050a0302031903030b060a0c0303150f050d051005010b070218011202041109030a050c03151003021002030d0c02100e03090f04050c090d0804030c06210513 75
    0xa0a4402404919000c1030400860401c0e100320302c0140001c548568a003441c0da0086a00c0300ca50b21100350126680500010915009401090529601400250b40c7c2d00e59108000c1200c0380314201200000c1c14005c6032140c18601c42c1800b02612010710704030901034601410889004a0312500700c442d0b020b02e600004035070312540320361402401581106a036540c400d02c10410405c1c40b9a0342529006800c07001030000701401101814210350646000424200303041d810f22a40c00b901c8013140d0b051240000c10800c200012600d0b010818003a0100c0c0d6040c2c0c904c11a0100440003101c0c44900b91680760300410141c501724201b00061b00603801540c1c0ba00741018074a909a03040d60401c3d9001d039000d9941c000300a02d207442141001500d0902460603c0e0503580061104410703070f180203101e00d444501254000d20705508a078103003038000b084204440304a10700180709401600c401d8441e40c03c402c8001a10500440d030313000c08190040e188070b1940040071030101c01001c01070300d030548040c0745181d034800244 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 540714982 1250 540713732 540713741
    0x9061e040e0703021f0e0d0212100b0906040c0503041104020c120c1c0c020d0501061206140106050301081005070e0a0303021006050f03030f0d090206040e010f060c080706150801 78
    0xc07008018001060950060041c00804142100208001e0040d5408140e42c000d80790801c41c10101c030350400e07000443c00040e00c0300340c080c0352044003400381c0098090580f8455000050b0f00398281d44204103595007000300401c6500b00d40905010075030400c00500000e15000351001a000e00070001420f00000e143e4141ca0126603000202185c0000120426100010040304048200c1035240300c03956032010304028851468488024018400c3e512400f0802100703404c01b001030035480140c0312203a0558240785026040d642032a0315100c48031000414240e1240080741c0c10b0315240d9005040d000e581000c80781c01014014002400c100d038036242c4001598507030640300c0c0118086d90040080300c4980c6516422a00c1c5d95001d80c0c4180045484000d4544000c0196004640c1c40403203c0d44545c59600f04002409900e003000b5404840054080b9840340c03010790040c143c0d581000c0201480391940015500c804030b0400181c6044814401200014a0f075000440d40e0b101c1000c4989130316581e07191150130768 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 540716232 1250 540714982 540715001
    0x506062508120c0d1a0a052e02071707060e1c020d0602030a05070801060909020f0d0509010c0801090504170703031803050a020d020a021305100f03051c080609061e04 73
    0x101800078058600b0402409944000f210103020390903403442c0d05001954410b4039109250023001020b034031100c0c100c042e24594000030000504501c211060350002500c40300240104002a20588480b4510324000100b00381030b0f03855a15104100c0960701d00304031144044101210494240300041ca005803204107030200c030b09214010150300c03030803c9440f0300c09891005010704100003010717004114266215070b80700206c5030120703001039860030b0380141c20860f40314218002812078104030501100100561288140e110503541d00000d0781d0b00c2d00c40d2041911815200900016403180052214401c1c19004000782d40c4281000619030103070803007241800b0070a68003680818404500d503503402e9010700012400600d01e101601c2c00440d16400103454003084070301c400c409682c400005904003e10a94000034083c1ca600070109260780f80f41640e035544a0740c000400c405220320010009500911000c0e020b1400204180e07900d54034801030121024803040341c5041a114000107114a403564810034011 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 540717482 1250 540716232 540716251
    0x1407080c0d03060503011a1903050105010b03090d0f020a03030c11010f09120f14030603010e120c01060e01060c031206090212040c1d0103030f020709051504050606250812 75
    0x2141c00301c0502218015400207000c0c3e4103080c400b001410603c060304110410890b1125845c00c4248048603030024150001000740d032a1400214034000001c01441c40394032000c0858100035070084048409201100c01500964081c001c8600000d00070b0308aa2004101403800d110300d410116603031800e4504061020001642c1c50300540140850f0440b141000344103070070081c18024400c0300c014801581c00c20504481034002c0b0120f4541d90303085d0005801406442e0454001a52031010308080b03a201d007002808540c03070309800044005800255a0403901c0301c0d00d485122500c00c2c4c50a8403500905c41e95051540c1c0d50305004910750f07541c0d1005c1c2c015207c40507405250703032902e0318202d0381461594011081000118100d8041181200f06c454117496052800700001d40b2081c005034508051a045519040d05290130442518203103ca8084506000c44041c0413507243d01d02842410f1080480d0702d4510308031204004409051041c5030311143d032062854514000c0041d040c0c00741018162220440d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 540718732 1250 540717482 540717493
    0x1020f1b13180201020d1d01030e0f01090317010609050f06030921040501030b0301021201050d060b150a0e0a151b15020a0216120f05150a0c090914071407080c 70
    0x655078104844102c1b40e0f51420240c40744180b420200c030394214401411410940c40302007100d200c49003480601c00084207203000740481c210a190140407051046400d442900150000145581c4600c0d08281111005001400001540c42c00c0c05007542c8020302c81340041c0705107040d1201d15a10710200c405d544280f5003441d80c896042000040940c0c1801d4100752003a8010700004440f054012055030450710202c4004035490118941a40544000070700550312000500d8415056552038006209040da15621441107503000c202300302203058140104541132100240e01c40e0401d00459281340254003010078902200780300d0742d80c020005a07458901c50002d40100d1002d03030300754040164a4403050701c0b10009030a50708000071072942116040700540525648242d5509000003030102d40e0704601d01e030707500500901d44140050082c1c0740017a0541d00191040400040480d0305102da12440c1080c141d0101d4507860b4003500f162178102140ea0100c4040702006084002400100140400d8510324082c10 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 540719982 1250 540718732 540718781
    0xe190602010e010203062b2004062c07020f0f070303080112030e010e0a0e04050a020a1703300403030b0405070e010e010804150e01091101020f1b13 65
    0xa0949403003042d10701003a8014030511182c2e681d184e00019400d060301601e80d2425050494001000d20100320140800500c04800720401d4001c601e0f0b20250744003540c050000a540c0e00c01c0d00c003681450f139454010143c1300e040f88030a0090007058141c00008610464088100c20b108050800400e2103407100c566018410030010550464445401003540e612107246410702034130003520300361015100314100041c8003152400c075900c0d90200805800b850764040795616052038600e6490433484000d901c510391003800010f5001110b24003d0403c2c0c4e004010350705214480c042d80c00f03170f800105401d2524020b040000c3d40341c03842240d40d0700e10403402643c004c50800c1000043c4021904080c00070420083c5001e5881e00e5660009a1846810000c1c0b07000595a5604c0c00c1a00c4130341c2d95900001d03951804c207201c1a10641054000182103030158403180c41014622005998a580300040c800254020a400c86241c403501d850b0302c10611000360468101e079581060071421074002103501c0b9070300250b20302e02c1e0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 540721232 1250 540719982 540719987
    0x61302031c27060f1119030c02181302130b100801090b0d1703190c020313050f0a03080d1e05010e060d03050f071403040e01030209130308010e070e1906 67
    0x3100d011800b809582049040003401481c2c0d104d0303080d014050010540c08200301400c104010b06460184203003528a81c1c8051034010900700180c08107034450000204030841074404015100c0c0501900d2515806003d410303828040c5400d403240981d0001c542c0c0d03007184003580e102c68842000300c8c0d202c1d0707030382c200a0f604006031541121840301090f4024034002a6190000f03c400d984103543c511314100a50f00d9030344c1d6400307140080c0d4090b040c00f038005090100c0d1003042e503000805403441104401003072940f00c0e2143c05106404250000c070030340c4480310200420114100000801c02d4201c440e001188004000020680650900c528000c015660f0401000300300e10490042d5000081124801c5a010094900030542d004d04a01c14400c02d1000541178208090b0741091030341e5004440a49803245d60303032410090003010034841030307024040041c00100d00070600c582081000e03501d03480f8407001e40d0900c401e030340a61200415107414040d00c00140303001a03591045e0a164003082500c454403040c10039400 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 540722482 1250 540721232 540721277
    0x30e03180a090606120b0d020d0501021801030e0705040c18030c0f09020a0e10051204082203080327060f07030f09021e041d0102090f01080405061302031c 68
    0x2c0721824502403080c0145039000c030110690500c0705401060440e24030001680100200c0b0000758004001110358003000410340207441c085441c03141100c246900c2c000150181e8150b5034800071580c02c40c1c00107120500d030550007052804454900150301c1210b0000c1d0380c0601032607070030a44a4144c1014100300c4000c000f882100a00600801581004400c040290007105500c0b0b0180c0b0800030301c240710345550f2103075090f9410400601c0c1104001c5c10320742004801c581c0007500844070303da152650710f8010540ea144520880ea44a0179080c60740e6511043c80c0c0c501c1e2800180500c4031000c0041900c1d4065040051500610110404c0e92040c00c00d040040c0850b106041c1c5040c000d42844100c8001d0795600d902d05240d042c2c41064004114506400100204200d40300701001c1072002407a491082c42c154041c208015050340c2c1050410a0307040151880c05003160300424952241e40000e49510312480c2c001000d620240c111010218249c0110fa00850700809070382c0002e040041d1502280400c004 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 540723732 1250 540722482 540722489
    0xc1009020a05060f1b0c04151a121b0d09050c030d0315030305371107030b010b1c02220f03021809030d1d0f0d1e030e03180a 55
    0x3c89a01d407100b4682c2c62030781c07070140c10030340010303517036600010294001c5c14484660f450f44020720070807100f207010030f01050f40081030181000e401d2404104001c080849130898106e0b08510b4400c02855645061135010201010b42c15818641e0901c0403942c100564024906114400c101610703ea5100c40145480d180ca038814040c01c1508141d111003440007840c03102c00a4903003624055a41e000701040640c2030f8286c400d400300ca000b000c00c00001c44207610945007100d0011680d01c1d0320038690801001da9460a1b6400301800c000035080040281400c000b00401204680346082e400f0001840800c2c0c04907000100c202e0040e0112a425074401c108206104010380f030724039030030482d03641140c010500e60000c00f08101c500811003000303d141c8517400c0056801c501125003090050f04581c14107903104c4030004850403100c0c41b0b03885452424440201f418503070045c141d42c40c40000885110aa0300c0034801480f034006141d540c3e03e402d0f2082200b070000300051208000e04042d80e00305c1e9400d0000d034404031361 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 540724982 1250 540723732 540723739
    0x30a0f0b0d1104090512030115110c060301060327030801090606050c070905040201140f0405090c0a21060801110a0f0206070e091b0714010501210f06020c1009020a05 73
    0x8103240c0090424240300342e0444054400250540c1c051800320b2a14500c08444440e101c0080000035002c100c0204c030109504141d40c80307002c0d201c00141902c0d80c0710940d4140d19800a003d1006000f8148030364480450001800b046024104240c0200300c20900c090341c007900050b28641c014417010b9503074094440104010b00c3c103180b9288100d404244c0f14811070045030040345e1140d01003802e5a1007405542040c0741d051600d03d50302d50260711704200c5a8418810750b8003509841000807107420440099609820541c0c40d0728141d860f038002802c43c440440c2e8503030a42d2a6032a20041500842481501400280c400346c503540d4103e0305001404001203404054210b40c0000c0170414503c4d485a03c0302003040c010b8030703017200b181c440b180002100c2040306d05818452002040d00302c20f01450580110303031004144020000e698841c92214001058546d1400900c0c00c5880707080c00045040f2442400c881c019000142040c01d1300c1081ca0511003079051504205444a2010040d0318005d15604000c1c902103 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 540726232 1250 540724982 540724999
    0x203150406080705061218100b01030506040b03150a020c0f1e0109051c09030b090d030605090106050702010e04141e0c0301260a060c170a0501030f0209100b030a0f0b 73
    0x52101d1140c00c0f0030282c0681600c012030050000c291f4030f00b000c00542c60135119021060440131000304540d40c8114000780c1481d011442508251241a02c01d480c0a0050420664856a00304901901070800d440e415802c00805060040500c61000e420f11070201a010bc1040c0503178070f290110301a078002e6120b07490904050700151001412280700c903030001c694031a00b408024251209207036940040c055078440810000b03505c00221750b64000401b1510300300262510b40080c4a0240c10900035070b40818001c0210b9009503005110300001e89000400110f2159039109404c0310002e802e8415966801482c0b110f840401c1072139104c01e91142d900c0a500707003190300d40b1a200980f0390001502150100110b02007801d0391409001d00c0108075080314047c041c03000c07074000041640103a107908401000c5040d010960541490081034104c3e1342014641054000b80d800308080d10034007900400740700175140d0340040c071030040a0255202d0264900001100c0e403250b54081e060b1000c1e000c8042c8a08000c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 540727482 1250 540726232 540726239
    0x10020c0a0303230105120c060f0307030c0f020c1905040603230d0c03050c2409010b030a02211009050a11041e2f091009030b0a050a02040902031504060807 68
    0x140381c00c6046030300c22241800c021200039204c501f009025840c06401901c00a034442269008000440c0180c00b20b603030811094504a400b2607403102c480d00d1020050f00100140030f141c1c40c25451303010580600c1001182d15680e00c01c00501110000c1c1e10440f06841102c08460803c419182400300142079400607006448000c0802403003909002001801d0080c041082403503100204403030003480342c441e5034440d8150100c00700003820341000c4580d51601d600340607035140d6505020030800c40e010350150410403e0380d280055100120140d1950400e1807080da8040705100c4424010965140c1c010b4010b07080130703c018107003145814005a05a40681d05000e0725500982804199120110b805031380015100c0308100300500c3d100003011181051441082a01ca46c80c1c0c0010050000240c22100d4100d40300ca00402039800070454030000c1c0c1039081e0000000c0d100000c50b00b10b181c1c03244070020018646521611503904030b03003098900300c0c002c2030181212030031402e03e4494100581520b00050040d24907 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 540728732 1250 540727482 540727541
    0x708090a020114070605040606031403040810020313080307030209010801090b010f0c23160602010c0c06020702040618020306040c0219140f0703030f020601060810030303050910020c0a0303 83
    0x14400c0000d04028000c00511060907400041d2030440740d000300184080e050500380071000e08a14002595110321001c461590f40790000103c4044032103002c051f0024282c0d8144403c02500700400110514001001c070f4000140080000c0d4400c41040d1401612000e05d40001001c640058120b0442e9510b00303000128070307a070880c41d0030071200c4262a02150003440d604c0c00420300100e460f2080e5108102c020b0101076904042050202c7d0324030300e651482c403d80c0c0d44a089099444001c48000441d4140c2c00c40c50105106400519a0700c0c0042c00c042407039a503607101c2005000c2d886100f2414590302000380041c0746040d02482e5002c1c4118030007424a8100d201424031400c0740c1e0140180682000182c10311340d040203125488105640d101983c401070b40d40d040145c0038642c41c5c400c010060080c1000860400d010b0012240100d50030000c00c140b1900b07542d0158001c0c0405850124948500303e54407105525500080a5034a040c2c0040c145404462402034207498041c1641d00c1aa510b040d035a40c5540e0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 540729982 1250 540728732 540728743
    0x50d06061d100e09010821040f050105031003080a0305060f040b01082430010c0f0f0e0a0308040503010b0901352b0f0212090a0b0c0607020105070809 66
    0x40c00b00c52900e2940320300d080554100310b280c640c050300040c00c1c100014000304d000c82d0051b00801410810342003c20408907100e442e12a5018810340703d040300c0c00901c080c2d4450009540c0c0281c0b1100008007040c0c50361524142d42d0824040000007036280c800f04426070038000400c100007072003503909200407420440040d01c002d0004240074008000320010a10748101c580b0141c26082c0c2c0503114058210308003140ba09905124a07403424202c00c50710415810200503c680319900c1d503030703542c0d00c00348501c0100110340e50901d030100e10080040501080e106c5584070540400114032550a843d0384134030302410305081d102c00f10b030194801c0d8070301d000400030440d21104031400e07184070303170507511114107c900101c00240380c03c0c0e40038080748201d00303c420540010758489a18203180b00e07030301c07440b80e89221411581e070f524541d0b003d001070300300340103a5643d6482c404c05041036003c01400340c0e0102d0303168a00559141c02c446c825140f40e07840441804a40b030780a10449810440741c3c0b51000071884c114011550300c0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 540731232 1250 540729982 540730037
    0x1020f07060302160803040533010504020a0905120606190602250305100b090a0b06160c1203020105010e1503070e13151d0c010c03260106050d0606 65
    0x15070000b8070055600100d42841045075170040c1c4c401d40b85c0c00d1904240d03035945041460300e402087c1c0490b40581e0b200303850000400000c5001c95802461f800c020034080030f900101c051314213000d50004041540c0c0d03905148007000b542040000c210601e400d000b0452001c4480c1c144690a050725001407103650350104d103d83c44605001040025828180f90070354848050b588090031500451410161021541d003103032120013411a4902c1441d10f402d080601207446000145500ca1000c00c896401d0a100741e28044d142405540f28908169a5080d180c03140825540200c0050359200010b01000050540c01a0001500100310708044150b0001c6959400e541c024410307681c803000d0000b24403012006170780c080140d01035030f030440c02d600414140e40038048419034054a0000341d00040c1c05030100103801180220165182d05180c0460384041e10303c240800b119041941039094481800484090310a000709020740d681c0741c1c0c40c0910b0b4955402c840c82c85d0080010441130f03080e048e0100380b074800c0c00540d0703 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 540732482 1250 540731232 540731237
    0x21611150a0c1b0b0f0705120a05070b091516030f0e0c120c130b0f09060a120c030218040201081506030c0a02031608031504020403150c1803050d0e01020f0706 70
    0x3c0240740d540640141003640c401c15643c9400240301864002c00f10150807581e100304200c500340741c3c80c1050401d15000c0c4000701030000c0c80c10302c8002d020608818000d030300900f0010940c1c002d01f08030f981511030b85600325100c40906400c414144261039051151250004019000304880010003010075142c006840c1180d124074034044480032058801e00592041001c020101440004070300307050000340c81001d0506104110404412946083c072145061013903c1c020600203107603040041c040e5030341000e982c0644a0340e55a40001c80141c84030444030007250f001706ca240c0503900c0c1030310004195840051034130705441c059441400709070315540141da402518040d00c40c1d03140c0c42200012482c50207400c900359080f040c081c6101041c00303400401513000f1040303c100c1513240302c500400e01003688603a100040c0018005060040342210503800303044050000d01d0810606201003000d928032440325001078510b900b1480320b22191075048034040405500a0015000c0076243c4455561200c42d42d1061900303 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 540733732 1250 540732482 540732503
    0x1e090c010c030203191e0e090406020a0e0406090509072c0406110706140109150e0604151401030f050c03131104021b060c04030510090303021611150a0c 67
    0x815000340151031701404c60340c05568250302c1c0c41000a1000c0000d429031400b5400070304880342128882c000d102e00052000c2d01b188242d4865646110082d4064800a01003002110041985076601d004a000400c41d0680220701e6091401e003960501714560b114092078100c02070708229802e001441d003160000340f0300c01c0c041e140c0d40c2e40c1001c401510507101e1915001c00002044400c00115502601d9000031078003a5141c182c1c1c0350340700c00341101c46401e01010309258103c4100910103401410307c2c0d108101410120b041004010603c802d0031035074011001e150048401c8010559040c0700325030325201448404d110504028000e0321031444007500a04001409000180078002007a0b080000244013400c2150703240f1200032508548000c00c4400e0255026100202d86012903c4060b42c090300c3c0c0050280448107207044c510001011004412400c0c983c0a000906c1020720200d4013000f854095014521800c10940c200a2071603034608242a188005005250702183d1240d003015000c0d500101c07144 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 540734982 1250 540733732 540733757
    0x503060a09021608090a0b0d0207050c0a060e060d0b150d0b060301030305090409050a152003090d200712050606040504082b0921050408060c0a11070b031e090c01 71
    0x10803a41c6c0a82004072061000103280e903414a2540c0104100f6020b54155815041c00303108010006069104520025103003400703030240c9141c070200802454403403040c001210380c00000031910541d10484034110380d640105008000368003900404a90307920480306580340d5815582c000e0a24003900f5400c80c002c0d43e544078407500300300d0100311100d001c54001e030710003100c607054081e00000380440020310701c03954140350000705988860f0415607004200c140c010f045180c1101c28112544007a0004080d42d400c3c840885550f003510034000c1170b001e031800100d5502c10503010304255140450140c0842c0c0514503010401021800c0c44003034400411442c00140c06140156454403d00d28120340c4010000d40760410b1030003044015088114080d111000740d8011201d400015103490081d4070030070f03206401080009852040b00350052070410400c0c20086400310650b206030b450811203402c1000e850100009000110b800300413107403114142c1c010741e204180752000d00345072940c96215490b41031080c50b88160 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 540736232 1250 540734982 540734989
    0x5030a0f1b0f1b0e06040b0f060d09051e0106060e0319030e0a210212060903031b0c01021306020c040e1b04110c010902040f0b0f010e0118060503060a0902160809 71
    0x4804141e00302500c40d081a0311113544802e4050141c0e41203210702d24090035042107003400e0303c40c101d40d0003005050506155040054801400d002c580031100ca000d40510440342c0700110511952054610f00002191401e064001c2c00c40f403600d001e001c2c07007584000105c0b030103ca01501d140c10090303070601c0c2010800d051a00451047c800d10703008485980c50440c03090307080509409440d09210300031503081c1d0390704507003819440e02e40c807007554444013907042000010a0008a5400d5200c2a0700180c1410714294096803031600726003081104501c40c114440003045603950400440600d0302c41100d01300203c841e40a026680c1e01d4000d0a400c0e0708860460440016a8a0b40d2000b04c0c800f8101c0d0483d5134444002401d6402011000405c078031540c90180d40c00038414192184040c50303640542540746a00900e801500c0c40d2545180241c10443c2c10440c40300e2002060010000802c125140c440c1c6a0812204101070240c50350410310440d4814070140c90120401013140d808590414009a900c1c0d1501c03020 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 540737482 1250 540736232 540736253
    0x14031f020f0705030c19030903080306010e06030a0510050109060f140706020a090815060d080315060a0f0813031b030302070b040807060e010606080601110708060405030a0f1b0f 78
    0x152010304020440c64140800400142417060041042c0c4076124201180940030006000700a00000d282d000c0a0000410b6600190b4200205041590051000c0d0300043c0141d8402c50ba8000c400740c40301b050006400f1405075130b1000e014242818000b260a00300002c003201c164100c2d880400a581004603200304426044401e81a0015000d666481e038079500507104c4403591141d028903204c1c000310503c0101075140180e005082c0186141c21903c40342d101c1680c6a0000350030b410680607070341503035480c566441004120f04103054585140034030314900090443c5000a15945440000c41d001100091348002d10310040c044441054080f10380381c0c1003c400038000c2da02d0040044000c04184000e00c034410010f44410f0b4801ca10a210a071405010305080e1001031007000040f44058005c144190300400b5521405601c110485054a6951301000c0c98505c0c2a03406862507080040d0200e01c881c0c0c0240000f681c01185d040c4140381c0000f071600c242c00002aa00050200646810400200a42c2200 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 540738732 1250 540737482 540737497
    0xc031202010b0108340f0908010c0519030b09040507140904020a121e0606170d0e040b040905150601140c0a030f090806090606130612020607060209130b01030614031f02 74
    0x1104007505d003c130500941811071010340302c03012940f14500051405414040c414101d1010740d40c440c20320310324440b00c810300145404480281916200e00c103895480340e00001e4030850041004008992030030b80d2240d490300405d40914044c0501e24104000758461130410300864014040d9030094030414140a10301c0300c03060004844d010180c070b075440244980340d000501912507099404d00981c41047c0b0b21a40c84070304030040800300b940048041e45a02d800e6001c03031040300010784042134880d01d0b0740d541401c2911b03a00c00c800d10302e0f203a4410312400d541d0000d4410140110224060714003890140350303e1350b035991800e00170204003400d50800c2e050f500c22150440140100400c5074083e003401e40401e52030b00340840b940d5001d5810083c40250180a6008000031100184c81500303403101c0e1502800305980c0080000d0703030125000c10018859803a02c03c800464807100361400108400c56030001400d0f541e069011200203401040108400e540100306407007250880c141081c41004074030b1164001e802000f0703 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 540739982 1250 540738732 540738811
    0x302030903121908040201170901060b040905100609030804210b0f040b0f1501030b030c030a050a060f05040804060f03090c080a06200f0c030f070c031202010b0108 72
    0xb40e68558011940504411203071821485003031440b00310112030318001260702900162400d80404c40c4a45610342013174000c03080b400045155a110079030201950b000d0343c0700048503a600d204000c0c80581c0401450007400d140e28003400b0052441d1240d120a000d20302030001a031718071a0301c02d1031108501c0c85000710254001c00c464403616280c00e03084410001100d05440640d620400649007182c8041d10718415091024000f10b01003407000114002e10240303c21030380611070440c2d00c4035a42c4d4100000070005d807258000b440d0b0406286400700940c0e083c1c900d2441ea41d4201424000040d00060580d0244c7e40c59203043c03091506484011000f42003a200c001d001c05403404004107040d0804070304615151302580041c000f060505845039103486414419500c40001442804904030142d4000d02005031040112800c0c07140c000302c5900c0c04d5201d4082111b44408000081081241501c4080c000c15000d0008020454019002070109540101b1550903c441d070501ca00c074480b5141b03070307142401e030040 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 540741232 1250 540739982 540739993
    0xf090c011206120807051e0714030304030f061b0e060d2a020102180a081e0304150302030610030b090619030b040807050c1012020d0e01051003031e05030f040302030903 74
    0xa04080c244d40c2e1003d00186c070140511480c42e1065a0003140c4803003c01e46010040903c18645034204100e40d181002542d4140020400080402c6030180e544107218010b001c00a1381d0202c0e6100b0281c0c410305104040c0034401401c046048543d1018240d907070604100c20045009140e58411382002c0d07111000c800007618803100c11006450707055010f0040c41807001c010620b58480c05080186084a901c6040702941c000031080c401d000d141518040c15079015402c032810304e51900300c17007941d0020412560001a44c04401c019080ca00b100c90910a003811b03040810200c1021000b0400b0341800400d40c1f03002c0c441040300d420820088142e04001140c01400d04c250a05003442c0030283d660200d80c0544252086503001ea0451134070205d010a00c01140c0c40344656184540802c10203500180d41d0b1079800d60f40e0300040a4207010a006e440d111346800c00f002c41d10b16003117103400b620300d0983c240032a02c0c901101246211701a00001102c0d00300352402043c1003a96914a402c03840c44c4195402c5503050b0084 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 540742482 1250 540741232 540741269
    0x1701060e0406031406191e0902030f0303040318092a0e0a0306060302040614010804031115010803090102060114060d09050c04060f0306140c03070c050a0c0803120f090c011206 77
    0x71999600484801081e120b00005040011003940c1100725801c6c0004041d40c0030a03444403440c2d0000d17230b00c10320150076903402c1c14001c0300d0542541c0007120290007145103889480000004011883c0282180960400c05110900c1310910142d80720725003a541d0200d504401400d0307030b00504c40240c3d0780e5002003405103001e480c2e02d003081c0508480e2108a020f0350500c0000324201120b40d10780c82005006035154100d507130799502c0484006030b041032a61010301030280d01c18240101c0600c8140a0200b00c00156516540000024a8018144d004000364489140005000ea4510b412602d40d0f500c0f01d0004152500d560070005e0800c00c1c0e118803c1c3d8054a007110000707080307502c0c401910480740210390401001010a0449003c84811510b242180c5801c000080420340698400003041c1d0064085401810940da65100c981d0b1843e00305545550001c200e60f1065004005040e07804445201c4079441818441e040350342e40c08400d8080c41c1400034280908804141e00e034030150040c0342d500e2000c030f07140c0c0c917 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 540743732 1250 540742482 540742523
    0x10315050f0f041d100912051b010507090e0f06150702060409050a0510120201020307030c080d0c2703050a0221240903120a050703021c0b01020d1701060e040603 71
    0x400c3c80130094070300034544c48444140d001d03c250506690814800c00708000603c0080310568030030306900e9440560b00c0e01003e98100240300b078900c40c480d9a119502e03440c0c1007803c0d034004804010260118100d095042004507210310012a00c194007404410391110000c0c40003800f140115003000c0342c440d01c1c1c4000c210540c071050300003601411240c200c0150540c1c0340d01586100c2005001d000e4007603803081080c400003034030815602503440d0052400e02d0401d00c00140c10303c00e8a68203440341c40010442d01d03001318062a8940071074002c1240d840c0784c2c80380174503654899803030314040d16001e4460088042411050466640d07003848110411060710b05040010040c200b1001d0401c00c001802482c0c036002807000d24000086900c0403c0841a55801e591840c81c102c02510b8010300c5003040503004d2242d04145060040c1c1220103141b800004920301d04904002481c252411032282c042296403411050103400da030001d0340c150382e02c624000010b02e06400102e4040c04031a41b00803c07011840009050081 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 540744982 1250 540743732 540743771
    0xf09020907020a05060c071515091b0210050a060e0103050303070909110d1a04090c18050420010215040803190506031203100306140f06010315050f0f04 67
    0x92003191600c00316107442004036030300c6021840003131003580440080780050b2851000351011900c544c04544071000d6003601c40d815036201080c80c03002e030080150180a2013480340104003035040b555030000c0c119030b08400029074860b000c03a08189000e5a4402094940c0c182da008600a450484502201941d40b807a003513969600c100c45540000e075001d100400c600b1290300841c12038089003100c1506040746aa004030007410400a0482c101c1d101c56041e400c50388580c028540894010b1024084252400c4950540c060800c800d0094452620301008001250002d032101a49020f0300e41d04490520480182e140241d61066a10502d600c1003c000801a440b0000c52141c400700b91480300402c120304031002603c00680f4415403503040035a6020f01500c440c1d0156a001d0303035402d50400c225030342e500c0b4401150f01010303200c24035042d42003c01c5400d000440d01140c00920a2a0821a20340c155409038910b49860140c54460820001900003654a00010351810709000b002003106105511221180d80c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 540746232 1250 540744982 540745001
    0x201080606040b0310231806181018090f03080a060503070e090c031605130f02040801020705070f0501080f0601020307021201050912040e010e0613060e1b0c07060f0e03010f 76
    0x4806d120680e003400c001c010304403840d5201a20700406119030808540407e0f5000b4a8103400c11108002d41c0035044a001740140604683c00e07035480745070305080c0c4400e65115401004441542407010f17100004031a1000c6e01d4905070186801030841c3c0703610000401820b22540029454403620b003001c20380180070180c6078010900203044500c045c0d00a000e064690942d00f101020180c0f0b100401c120340d0500c080d40c80001e00c1c2d00000040e03100b50641142c0304903001900450366680d404076103c401c0050810803000a09203080410346001d103000d00090271500010f1030b4201d8000e0540110b40d86900070015204030560007440c101200744a40319190007803008441c1e01100c3d10501c0440466500d02e40126019600d2030201200c141c0e00b0001c11080c40c28001d010f86401c01c0307607402c07a210131010741c4c414480548100360560282d0705100f0300070304a080112501e540951001c000d00b001c42c1034002a8281100c810703082034402c10001e42c5090b202c4528180e0295055420700c0c0c0c01c4844100d4070303486588071 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 540747482 1250 540746232 540746249
    0x102030f01090c08041112070b030907061103040603021b15160c23190b040303050a0608100c05090a0801020c120306010507111c030e0109050312070201080606040b0310 74
    0x241c2c1e624034082040d280d001c0706500110f4030440100700030030350003114030703242d0f40000d8000040d0341c00314a60145010882e80c0001c0c3d2550020080c4500e0250501c8014014545890700d41344d4500c405200940324801c5109200900d035000031452900486140f40a4403151004203494280b400d410b0301c3c800d40c94089983c6018200b502d41340c079001c503004074103040c0080d81042d0841e07809502030f00380c4e1040c820422044800d512a550122209042e02894102c24503c50303418000c060605240180a82d24041d00001c0c50604040c0700780803680300026607094a106010001c0303200316542100b0346a03031040408054015000344804510303110150014034510664030102c0d4807200c3c1a9080c40140d000035140c2c980040c60400c00b4101080c1d80000361a41884010103a00d440801039509025a15a03a6000c501250010741744401540e04020030342c008000c1034000d00500c180110b00c81c0c21501c6005070080c140444500800c049865020940f000b500d03d0360003096a90a040f59042103044003480390560 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 540748732 1250 540747482 540747511
    0x309030c080f0f0d09050904020307034d01080406060504020c0a0507050a2402190f0b10060918060902040305010e06010f03051b0414430e130c02010203 67
    0x180e100000c14400c03141d0907958030105e0504110410444070740180c0143d90601c500034001c8081480003e523124120030300c0b2000da2003600120303603401718184426004400700300180b1040c1440103440310a02154542443c00700781c15551807800b10028905134100350b401920100b020003030701c500003420304c0381c4901510460b10a01c9d900c41c200003840300325004075841d4050035007040d0705000d4610a07040302d00895006030750b43c165030000c1082540c07880001c150303100b03d41ca4401034144200b82068940221144e108550070a041c4003019101d26014454020003000c4429440c81c1c042a9911840190003408420355549550b8203115018004940150009004250000800d00d6641c050340e81180e13481800390a5820b400c03184280352072042c404d01034000e51940d03a00c4202e0b08400c10802c6c82008590101080145088003402c00802c07a0040e21001c8404491154090021809090845000f5140c12152600544007268103400411301c95a90f071800e215104120940640242d8071a4002e2468041c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 540749982 1250 540748732 540748753
    0x4021f08071403010b090d08070f0c030c0b0306030d0810180501030303050105220506010c0f0609050c04020f04050d051c121a0d030305070e060406080a0e0102070c0e040309030c080f 80
    0x40030b200c20312400071040c1003080507002034202007d101c4000c1c4e00a407030b003c0c10580d203501c918444c2d1005940455504034060f00074803c200380c50641e02c01400510441c80d0562a040001c039940741842e144100c10300ca100e4002800d00028940e004c0c000c0c3c9080b0020ba15424003105100b03001d82820300086010905107000402c003402d18580701c8001c1303800e202c109019600e002c00110000c020207421941009820308000c404201811080950580300f1580016100c1701402d2007400c080c01100d030036108900401c0f01340e541d070350079034140d600f40c0340700f15440c140d80d41d1545481d070300e8441c810711880998180303e10700d14205a001380c040d5518920002007030005c0c01045000356502c8026015055002c0b5a10883c2c030003081c400e520240d4001d2072414042c446008903000608640c11076032200e00080c08090410030414121701411102d03000d808000c1d420f20003165180036401105004003844d203030340407001405052213580854000d681148090301d2040c2c846107a5522003a130440c0003100d87c0f00e000080c5 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 540751232 1250 540749982 540750017
    0x90209040f0509060118150803090a0f1202130914100e030405010f0f0e031b0102010f180b04060f0203040b07110f1009020d151e0902060901030504021f0807 69
    0x40e2080390128081e01c010b0f0b081510001d1034011629586e845c540d035031200502e030000400f0b0311001404225004640300c444400400204119903003109603509010501040052011088904583c3c1c2c1181c5040d070903030308240c1e40c1004040c02d803406802e442c1c480d100c82c1c0600c0800b00742580c4c4c0108640307060000724082d82c2e80c241c0d030307216a2140b140021018852100f001d40700d0222980c40404a03c0c0c030b0007451030340b40c0010707261070048543c1805100040010100300d6170248280498202504030501801c00f2110840807e0355000501034005000c4a00003010480325038000e45690350b08070011926070030141032019000e241200c0b5003002c6903101044c04409400025800c0d000c0b0b4188000f4103440c80c02e40041c0f4003904208800f01e8201809013036400c000390101079004400301049100182034650000040403ca2040d0120f40519280c103010701c025072103a000f100e034483c0e000e0a012810303446510200b020003c04081450041013000702c070011840e030008007140500ca5907a16a0944d00b001c549a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 540752482 1250 540751232 540751241
    0x40626030306060d0b030c120d09060809120901050d09050307020f0306040b01051c1712131110091211121516140412050129210106090209040f 63
    0x5602400c1800600010501034100103900c3c5c10103015106105a0300010600c1444044220a215000301d0640f00400383d02c460890000c04041c5407038449821300781c4850381c03111001c0300c07548640b900000c0c41580507409082111850020144200071000c020f082540e12a040800c04920036140da043c9140399141c0012198020354105c1200e108030703481c0504005074004c0c2052800b051a220110803404130308081e4580e041940030002e559600c1d54001d01c54140800010b0078908100105040b840c082900d200000700d09070010303109050446285070043d03441c1c59250380150700010301a10b800007000003c0c4541408840305882c00c003414aa82d02030307551600d040340340302212a00081d00083c1c403504071a61030741028030681015290000c4d86200d118060f0700c00e8100e40c804214603000341007084401d02c0703203082e500c0d401144a10f400c0101e4458001c01c510312451300d88034a500303000b451103082d5159100989074454800030000f5503176030007004000e0340084d42018812842d212040300f495840d03004 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 540753732 1250 540752482 540752491
    0x41a0715050c0d0e0c100314181e030d060810050106080c161e2001030c050409020318071203080a02090d0209180105010308030a2d0b0d020406260303 66
    0x9400c3d0500e0751001c0c0120041803491515080d600c21415140c4042d00c030380c0c0c10041c02c21150341d0302080421342c00c480600303441c1d006030040c4030840d030614458481c4100030500900740210f001e0380c00102101941c10b18518011640c441e0300711850404000352950000817140d0404050910910003603030380d221f0558101e20125034a005d41c0b01c1c100a180c542000c0340142c0d13009148141100b607400d1000c147c5400980700040d4048400c18001c82c1a84031205051003401410042480c0510020700c02600080c2103010b24440d0b80146c54010002c46c0c80324400040016020a07118203d0f83d92540c0c0300031200405030301c044198045040c802c0826641d09a600840e42c1f003036000340980d40c3d02c559960078002c0041000340130b888a400824410000c185013809228000c6000314840ea4490424900b200101d07500c032003400900034005480060459048948481e0580e0125400918040c05401007010907258a40003548140780140100340e002000000020f8540e01042400c510301828111555a100645 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 540754982 1250 540753732 540753751
    0xe130501180201050d0b0409150501181a0d020d150b01030b030c0d30031b02010912080a110c030406090e010305031c021c050402100c02010806040c0203041a071505 72
    0x105101442109401102518102420004419900d42c5590302705004092a0f20a0642c440004100160070060405024800d0020410140390715011000c40d984100c0c5a15014182d07030024002555988166822030326007222030040c51206101003080100940c03048280401c0c40e244081c043d5050015000c404810054054105000300e0f4462001c1e200882d1214400c240d9422012104034010514011901b60300380c0700490010b004040309040d00440e02c240004580c500b90080c00404c04082185e00090300a08091202d5110041d060010301400391220482c40c000050113a194203000000380110b441a5076524941c540b40d03c0d51022612081c032020340b0710360041c000000d20746012940701081d8107440c00014500702141225a092a10380b05500318501e0346d1340204801d60500d200402c80000c960b18100b06902555400a445d100c03000d41114000c82c0c0e21a0100034040c003c2044501804440021184041040e140461240d1003294120f07082411744010300344c05251406241d0240354440c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 540756232 1250 540754982 540754987
    0x61d030601171e0c040f050f04020f030102090a140909072d030c0e0604050a0203010605041707030b0c0d15230307090f020408060105100c080307090e13050118020105 73
    0x1580c0b500484021071100d100d0f400b5140d2001c4408514000036a01d003420000a0444ca94181c004c000480d02e034000c880f00c10724140400c0064030081d0001190703200c1c0e81115011180d0f1100000304e402402592881a00151540000310b211040f001c40c00300345050413910320f04199614403841c1e4a0300141c2c440c02c403a580146a0307441801c40c0aa44444041c00484040e152040d03694807403101c203403004d90045684501490a00040c1d0925004241e0310003103804055144d9450700000800620940c8140714154544040c17650609200784002c00045030400300c250514105128550000c1d804001c01640007490080400113034017500d5006d0381181d550200ca0140071407850001440c04405458580e454020058041150203880c0300c1d00c641c0345012103006854504000c1070518005040e04042c0c030490881c0c038104401c65000e943c2201030b590040e5003549980350003000766480311070360300524520b480003010031904045540c076100d0b40c140908000d00c40d036050400004116484010042d0006a04 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 540757482 1250 540756232 540756239
    0x1e0f1109120c040203010e250915230408190c1a07060c02010608010f11030a090c080601060804062a1d03010213141e0f040b1801061d030601 62
    0xa140c451211041d01c00580e2461500e48002074100e0380700b60082d10340d00f0858401d01240707403c5143c4900b40010120a0076100c40c41c4205e002d0f11101c4244141d4841004c1d503651440e40b903200b1100c0d1500407100d981140d4a040704a12030b0485c6030414003803035100780300d501031003038010800b481c00300c2c3c20540121140c4ca800b0700340320703140e000c201d0180901343d02104100300140005440344540e4031080450380c0002401070038031a54030300751540314100902ca64107004106074000707080001c99070000d5025400044020b101d250915880c8100c0d0310030070480c001e0000000d0b003582c005440702d00c43c80c4103400c00c02c10452540914a0fa1080300740c404000c0c40032580180031018014004041d2031003034682e0040e24804880d00080c266481107014000105414004020f40084241c0b0021104000c65440740c80308598840c2104800c1e5020340c4500c60301c0000440011901d541e0711030740c10420b01404202043d000c0e480c15800700d902c284034000c00140459541840300d9a00700b481d000514008001d40816440c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 540758732 1250 540757482 540757489
    0x3020d140d11070b0915010b0406140306180108240106021b0a0503070308070204060f0509160c0204090303091202010218010818030c0607020c030c06070f060603061e0f1109 76
    0x2201066800c2c00142084143c021502060343c1901c1014210001c100d80d540d501c2151401d15011303480102240004d1100340510790700700388002161246100368076140e0350380a000400c038a00c00d500300000c44450b080046044a070200e40070942d0411003200c5212240d40f8003815202d0b004c2481818010f80246581e00c19a6880031540c20b07240000528031881d06443d000081d051070070300d1b84120f0300031000103044070841c2094010000100035180c0d003040d0007803401c0d021450380d00d00140010629242d840504002900074031085c0304c050380151081026003210700d000740082200c42003e030f503061405c1c00c810b180d42d8414021140c2d0001c801c1103450000c00310310010344a01d84040c144180e104d141c042840e019003000c2010340b0500c9007080c010006414130810107420b0812200c00390b8001d402900d03280c00c9503200e03036049500e01640009594007003003190078260000d000e90f8100402d51800e10300041d141d4114480403c1d80d0160008040000c21004119002280c000c0000c000e003001c0240010100b82c0fa = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 540759982 1250 540758732 540758741
    0x5040b0d0b0411040602060610090528140f10200307060c020d2304150210050a0f0f0902151c150e150321070f0b0403020d140d 56
    0x9000c100459102000400502030320310566000812500100d020840d880c1e04205280c0c10507010344141010310003281c401801050140219801542d440d11407030103803800b05469042c1c050304c100b1340c007c801e0345510702d0013840628006110301c140c00b040e4490b030301c52504c030790048918821a00d94906c400d00f140c454541018283d0b0190b0f06500080c482a000b241160003007410310342d101e60142245121803d0003419840d0281d0100000c190100c0f0080c000d0080d513802c0f1000d9800c81e44a1029554180004a02c0c2c001000c0e82640c0950400051113900d56040e0803d0004081e200c2c414008041c26002a0049070048040070358041d0407a589042031400080043c895685201d0003800b0602c10742208005480c2282240d41c00118518030400c400120442c50340c0c2c11002200382031050b2420a00000d41e82c084140b04c01d4412190300b46603001c8100d0410485103c03070752000328404181007a040501180004850a4015010350705108041503c1192580140002e0240031070030b00c50104a42402031 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 540761232 1250 540759982 540759997
    0x9060609060307050a031505091f0b06190c12020c1f17071106063c120109060605121b0429010320040e090a06050103030f03150605040b 60
    0x501035800013003401d032038119019000d14002e2200c04101060100c150046030001020480d680c1c02c000d9401e001d0385994080c5101000346400d0204400c0c880c1000101c0074440d000a0703416202140c02c0802e102d0783c1003d03a105e4001d001c2c0c4020140050f05500c141e0303ca00c0c80807107046c1d00030044011401e0b40042e144401ca449405858a401200c001c0b0a030b00024000641d120380110328001500c404800d820403280364800300c251202844c00b05850812526000482d403483e242d2030907200c460601040780001202c42c080f0050050f00a60b481c002442e000b003140074003d071440360030300802250500f02149607000c24441d0308018640034000c41082e4264440b442c29859025444942d4004030020311000034601107002c1c0c07410355442400c0000502260201842c00c8030039035035a003209101001c02030694044540381d1900342003aa44a40c0040d05040401c1c80082c07445107454000320500d81c0c4110385884810b803645040043c0b01c1c1400f400c110b8141c04c0c2c03203103c0001358200818070900124402503c80e1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 540762482 1250 540761232 540761239
    0x10020a0e011209081611030a02060301091802060d0f06050d02010804030f020c0a060e01030c08040b1617070203070b0f0108060411010c061b2c0d1502070b0601170906060906 76
    0x4207036403002540d82c040c45804100c0210301d00d5490502c003600d0b4006c1307a10300c8124024030340318910b40d002c11001e0005104078566259900c02d44400030303900503071402c1440e40c010b01c0c3c141d0314109043c1210041250003511184e191130701402086a0a050340504105a0140c44003512595984c1d0115040b216000c003410450054228a0416840309a5010701805032501d9044204803420001000c9500001d400310801c4031903070070301000c51408990690040050f1000310304481a109040c3d0b00e62900789201088030954400300060b442d400310190100354801c0464060a03101c025404052010038083c6030446c4d0000c0c400701d0009189500b00b40a0034106060807440b200e41c40d01c80d10225001e44110760324049514503010400c1d9030211086081816590300c41007104030142645c0d03155100b004600e409112010035580901c4081100c0481d081180d00c0190340e1a1080c0c5441c144160050f6010f03804601c1c2c00740348285030082c0d481020702c03401c0c18000602580ea50340e410440000c202900881c0c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 540763732 1250 540762482 540762491
    0x90f0c2303100c090e010e0105043e09091003021507030f12141305010b061c020d0b15070c060804050c0103050402241210030c09050402061b010b010210020a0e0112 72
    0x307000744504000c0703000740903891912000750309d41400d10090760383c03281c002c03140300e00b1070140340340044001035507148500e40c05003401d04aa1101c4c440c00941e8414880d4082d40003a03040d0410841c0d250510300041500d209588180c602d0700c00350319031151405130002c018040f6502c0041049420300c01c6003181c401c206070300808100c41ea89079020b40c040030307000d0321001e41840c0044a5102444001d024400084105032501c628003264401c02d043e94651074514448400c0d0002040803d437203243d0041c4080402c020100e054440e480319007600d540d4000305044800d01080e401c001032007801410020322840d0098080c0c40c00c007118000440003020010800c0b81d120005070000d2122000055499081845110190745c0d121765074100e080105200404100b0f50540d12001030002070f00b60440001120f4000c81c0c0881c0c280c985100160380c40c01960709003130901c1c01280e4805640e55054000d000b0000c000c0e000d540e040140c1090f60003d9100b40005c00010030121007030003445520860741118001d031075050004 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 540764982 1250 540763732 540763739
    0x108031b03040306050118140603211b0a0b07020c06030105060903100f0e1203070c030f02010f0c08072613031e110d0215011206090f0c2303100c09 65
    0x4c040f82d0007030704800301c1c0c0780345030345003409801661013144c89680020010170124900400000c0d40c86442c100c1c840fa94080554000301c9145d10360094650280e044030352a83c2e0110031011041ea902d03290181924420540701c081070703150b40081089000f112000d40744610356800c0c001403200a900002ea295054803c000c401c00d841180c038800e489600c0451100418100d440c00211840e11030103000c4142e42e82010814041c8564002178217408050345810030000b01d0004110a9005241500007141c1150800d0242c06006a111003100c0c441e480c0d07a1118004041c0441541c0b1910200d41c3d03544034009008008034100968204000390000d02c24642030351003014801c036003814540b0030310409010400401413004840d0b024490406101c07010b200400c6241590301d0003185104040c803403a00c52564400c100014404150001c00d0015003125402c102c1d0b0b40203140115120740103100301000c05400750b40c4400c4074a511850054446001002802c1d8110a40303901c3c8003c00b4034600003000d110540ca03000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 540766232 1250 540764982 540764993
    0x51c02090103030915020c06090405060d080304050102030f070c050705011413031a07051305100504090c02060601080a0b0105090f01180305010207060b0405093d090203010b0303030108031b030403 86
    0x100c1c0a54429a200c00d001031400e41d9100c14002d103044150150b40240e9184c1c501c60302c50030213480084e80111004542600c942e00410000303980b01c60702600c004000401c00041c040150025070013440803106440080e950001c0454200c591001c00400c0c64009000c108031a61054840c003451a100c804800e285c001018014510500a503004980a039400701e48603856181940030305034400e07004d0509510307005030486180031103c503a000c0d040c42100c01c2100400784510403030994016040030b4004001d02d8441e244041d560b881c00b240c055000455090004405d42c03c0c501035001c0c400380603142d10f07003810b03000300c2000b03401c400140800341000000c111101c0c01841c07845003040114091000103a50301c44c0341c20104140c85440d0034640c069400c000a0142d030040c0050500641160b49004100789080301c00940301c3d1011082103403400000481078018513100c03950014a0051003100200300c0c0f190b03c90300341030f1240824850f909040d0002d002c48030b0004405503401110038070030010349260585913a04c1 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 540767482 1250 540766232 540766249
    0x30f0714070c0806060409020d1b150e031213091116030909060605030622140a0c1e05040608040501180803062e0c050304030506010b0913050f01051c02 67
    0x40d2041c141a4a00b041664000d0013445e070407603020795060014035099000f0544071001038138020b000c500f403403151480541c1043c901c03802401d09039454221260b0500e00c02408401d1240310300d8801e0150791000f81e01140c036601100c140d100020b800e0404546404098402040da25191200a100c03c020584602c1074805400b401c0f81d10a4451010b8a8102a110011504240c01070030600c80c0400520400d55201481c01d40c055601c1c0d00d51030b8281c0700103840c1c0ca0141004902d2140880d6100051044031640c0d07400a9040003019550100c5007160f0540c90084401400700d4500461020013091250a100311843c940c8180650008100403d0b400e078901014606118161801400803040c880a0314000c0e03e821107107203103100721019414101492000d00c0b80c03900c5034030052110020400040100c14820f95005640041c291b588942c5e54500d181c0031644450301d003c2c030900d59201e0a103840405842030038007818001e00303207071920380c01c1c102400342d0070259400000f9043e141100c80c1d0010394440700c4 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 540768732 1250 540767482 540767497
    0x50702061504140106110f06060a0902030a09170a23030f06010903050313090c1d012609030a020d05160b0a09240e1504020607020a030b0a020a1e05030f0714 69
    0x1c40744030a05086e54a68103010b6048400c0301d441d0044420b0215565924610720140c440007000165281c844198500041640303010050080900040c1407042d00341103405060540215151251459880120b07502c3c0222252a4100000030510104119282003011079a1298060500c51346141e10b98a400345140c105036940e81d8100c54140c020300402606025803558401942003140e55981c203c0b0030010b501c100e10b5441c1d4100b113603041d0031302c0c900300200c982050303088080d00801c00d950602e40d2085490760b000e5022007001d0700c9021104034805108a00b10b4207840401d08003001082d02d1680e030103601490140101e80d8035038580d404017000c10850041550703100482002d5003482d00c0c078148003205a0744c3c205546082ca0f000503203900ca80702c00150f0629440f60341191940e507103603540d03c0029072049a80d000580f55086900400181001660081407005019211758070206141720700700240c10341f441c100302c00041c400c1c00841c00c40b81c903a0042e2600003a00c0c1c2080d140300c49a2519840329900300d83c5 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 540769982 1250 540768732 540768737
    0x609010b040b10021509071d010e07090b0307030c1823030609030f0c010f050112110d1703040201030603170409051501020319180e19050702061504140106 68
    0x411180c4280341c584111200c000c0240d50180007038008800194881c50802580300380542030b00c0000360f00d20820302c811005020b41c0c41e4070f218a461041003541d00360200f40980300d13103149280c01080400780034070050012110541107181c40c55507000c108a01410340408040280100b81c0312045440303005100c03031000341010342041c3e81c4c1c0c217581580e006480f00d00d05007103038040c2e0403e005005a041000c4203d610401003030f85081c1d0350381c850041c410f006000600c0f107a0f00d900d06d02800482c003040c0101800003140d01503207040150f81030305020071105480403070009041e0100e400082035240c0700c07103001e90340c800d0050500142e8250341c5d440d094001d491002c0d030041070000004052050602c0c6105150300560000095a00708005d00000303540e03031007109412206050002403c0c050f4901c01e48030803540204010701c00f41c0c8aa69007100c07244c0d0703c400741c81c0415003100d046000200d00c2660300c1107070f204841d80c0d40100556201c801240b1004079910409642003070b1201295407a40030b00c17000c01802003419a = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 540771232 1250 540769982 540769991
    0x8270a1404231308040308040602011509140106080a020c1506100e0a0605071b15031112040201231206030c0315011e05031c0201060b0403030c0b1503060901 69
    0x1030400088075203180340d94620890b1903540c20b11855666100710b41c030030700182c2454005440c2d810485018021a4002082c400c0d0014001c2111641900080ca1008100b14182d0505480d1208542592843e403048034a10150000410050f0721901420741c0001058900514180501d47d40a040071381c0c001103090440c8404d014010f90741404480300110070035034a4210400302e00500080c160361090310501c420000007040300014050001b08048410b410b0840b140d00d00c583d10145ca1144c1c0ea0444415400f003450043c11000b0110a0001c5482010b018401078100d544d869006541c00301c20003603028070040410f00440d8100701d1107030050003000071050240c00e40303250040406280245503086c00d806600b00e0b910346070400c00311001040c10340d140200c508141c001d0340c0400c40715441441d4407042e410300c0345103120043c44c42c80030f00c045103000e02c0d03a00038400380d51a4000490315100d14031004000454002007100450160401103402814981d0103c49240130000003924280c1e00b078940301c4069548 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 540772482 1250 540771232 540771269
    0x1205010c0923040b0414240402030c03060d060f06031112030a080a0b06270109170c13020f21070305240d080307020706081308270a 58
    0xc82400c4000301070307109034900155100010110950b0700030700c445001c2e0340c540850384525901e82d00014113030345511402a9403890800300c0c11854002d02d40d000b080d005a044518000d50900707008691064000d0b607149403950b10b0f480d0a021403054100400c2d907070207a0f150f109900c02449070041303900031030017550032403a48040c40c81001180c081d90807103003a150744100140c0c6051900030404a03030100078440d00040514145020503d031740301d201c00c006200321042c4c500c40c02c100540048a4004982a610021901e031144802640c85185800b4150258068029800035203007144003941c00080a910140c1400c1042c40b0b1201e580c0c0250303142145410503440c07540035400c40254402c3e0300000318503046c801c80c206103a03c03d400c41500108803814414500724075515440d0b58001030b200941c08400180c1d130313281010300203485c2e03025800380303200262156001c103030350041955020072059008030701d042c50180002c040c0715555400c405910200140301d040f10166a45d840d0903240104001140151a03503134 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 540773732 1250 540772482 540772487
    0x9081002220f0b0a0908120c0606010305040512220f0302010f02030412080919140a06030506150a140315040507231b1f050702120a050a03061205010c 66
    0x41003402000000c040d1a081000201503074410086404008683e56183d5540100704c070203c806030811020f51007890713298101c0301050390051051408450580c0c0640d1104030044003034800969000c1c0066000f05441002d0782203d400510b80480040c5071000060540300d0b0070380b610741342e6601445041000785da042040d540c010644010f03910751031010f14500307802c122000402c00002c020141c0144170100341c60f2100d46404180803241010408045d102640d204000c10201040021940c0116008203000840314041d0084a0241034010241200310140c1d081940b0a07401405100b02005810031580400c004c9000055020348000303009005003407114424001968005044881000849118100c0912441044101510442620359514140f10540406840c0d50034075581250040003070b418007601c1007203e50303924070711034410074412a66000c1c420390302d40c0000e0150340c0003880304211442c241e174843c0c0c0080c00812040c1c02c00043e200d4503209940d80394642c50b40229040e0b955024040324068 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 540774982 1250 540773732 540773767
    0x140d020d14070f0f0905070509041a04061e0b0901020c0d0b0a110316110c04020d0911010207080a0b0a060b0f07060b1c03031a040e0607090905160f09081002 69
    0x18100300d450f81d9032460b20a00b80c849040380c1c4160f40c031203030b500c00c0414100e40c8208101d64508000600510032800c0540307a00445400130070445101c0c81c0b91070340c0019803218184101e40301c2a1070403041c0105500c1d01030140b07903591041c00c0042c11406540b008060310364031542d1080f00716024907401460303443e000c9030140c1204e40701080513107a550140104001c490020600e000300708114504800302840c46031645250101170b6040e6981305001140c1503100c09003c0d803107500a280650000d00c10700d4010001641c50b1100c0380529a11504580b482c17201040507410059040280c034603002501c01d07501d40313814000d0f42202a100c0f8864900054030300c14848203000d510f400c1d4404813910000c0c120780c4807000607030f920b01c95402414076880d07400a80302c24040c10b20240b042c10002e801800b1712042d48515903280c24080b0b03100e201182d61000b000c2003400b41886160700c204070420f88000c128007043c8054601c0c0c1c0c070301c60b06142085054140445d43c800240f00311445032a403081e000d6283d4400c05240220007 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 540776232 1250 540774982 540774989
    0xa020418081209100b09070c0302100e0a0303060e0c09060313060603060f290d060204051e010206070c03050d0207110d0501020a1106060a09020a1e05030a11090a140d020d1407 77
    0x13507080c0b041540240d40d8281140e90041401d050802d50014a482c081e410005420000c0d20040d00d07004a040a041d400700b910001a48207680030000b040e01c40322042044901a114484801c0003400b1800c1c160416400540c1c200c034031400d00ca1a040a0383e40c610b8256200d03a00102c41a13a10780b41414490080f5004601c2c95894030000032803003a0a11492041030840b080c80329218111518490090141c21703412907010b043c000d046990000528800030302c2c0b80c40398100c054010300c225000a40e00510880c51800d4445d07040c4c0c0c6151404070030743c04030300294200300000d44403012207a1440d00c140d03603031a4042e1034040c4074800158640610303040241c0f2034145446103c2040c1c1101d0b04212040d69100d8000041c1e80d052032005845a610200c100c40f10301042810204001d41d0343d1203a60340c25041000756200700da0400092092a11107515140c560140326042a00103e4a440034003c0c826810b46e004550640a041ba4140307600301d400203110a0a0a8019100c8051580d40280407100502c11003024 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 540777482 1250 540776232 540776263
    0x50f010519050108010b0d0809060d0e070305150106140a172809050a1b1e14060a050715110d0207120206040f03030b030c040203040b06100f020a020418081209 70
    0x7440f10b51b002080c01030740c030480003c007988000184026035035070300e034181c84410000c01000c00c100b02001102079036a100c58002540c451244d0190440d0500d070481e4101e0680d4142d90741d002000d0320000300100d15800035030100092103003030030340010481c001601c01e0384074161079543c251044040c54003080c80044c810b5000546c0354101003024000c550001005421a60722454a80c02403100e01c4400054440d1038020645003075001c0300a10305032240452903000d6402d407419091b0358451107820810507100702c0b040100410b10600c086808581c03800b00c8910400f0010601040100034001d801038294001c40641c060940c2c04550ba405000080354104180051400204258201600c641c0d60114281d0002402c05880e043d07483c010ba2001d2000803110003019000399243d00345403928123060344040311051f0048040d20882c1d65814460020341030783c00c1c52900070f48015591502400050803070041c9c80003860090a4601d400900048000d190030301705800a402103082001420b810034031000346d240306 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 540778732 1250 540777482 540777491
    0x90a0f0312050a05190b01090501120209030a080304030306060323090705030601090c1202090627100309030f020d08190e0a080a1709070905040615060206060a0e010e070309050f01051905010801 85
    0x248d8004881d00142c03007013406c000403400c10700170010001c0d00c1003450094050085408100404c20b0f117501450185110381c4050004503260001203049481e0406030381e281d14003c080b4801444205e15045402000c0a0281c4100c00c3d140c4021070f1a0200a078006506540d5402c99400c0156000014043c4c80e4030005003585404407910010300c1f0b90003a080003100d4a0101c2c810800c00c1c48100c801c81561381000750255001c581803280160041030750701c0e01640413585640f0b9241c0030610114400000f0105c540301e005494039140e40000c111150000f006076043c0d603c244030548a0410400300f400b4a225451031541c86416000041c20b403600e04042c40c24600c00d0000744558000086841e9050320304000001420b030351380d42070002c007030240307103481814003801d0500201c0e1250f40070074000d00c42d0320191920509107541d0b011116180e1024420800400c490602068080d8031070307000010b085000b0030448140c018508405c0f400c484d03013030310040f648030110b00c440e503e16042ca00401e801006010000c10 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 540779982 1250 540778732 540778751
    0xc0801180209060316020708010606030203220b0f1e010902070507050607051504030e090a06030c1202010519050c1b03010605100e0409240b1503090a0f0312050a0519 73
    0x3c0321400040d188a1a180440c12012041071003040000000c2c1800e4009026569403000d02078020343c800d03a449009843d1042d504903d0394047c1c22400d000aa00000d120b01a0303542d903403803140450000d0200703d0a1151881185038449042e0103140c080c096103240141d0703445151400c1441c1c441503501c001e014032021311602c1301045012030403581032801049003403a241d0395031404468041c0d84904482d03005840c0d0080c40440c400c7c3d5403000c000c0d07034401e24003509119280c44004400c1320084078000e0020707204001c92018081884049062000740707051143c10130b0444000242044801030303488a2a0050107200506450240100c000800041d00e00801d820800c3c8401040000c21925031401503445a00001c10096910036241c50020100c0b0035055130070745501840d0291210803007080c0300301d500b001d1220b1001e111000b12405500144020141c0e8811503507254548001150700358140a40d41e6240e1750b515989006a500c138100c04100010103203045c2c84c6900c50150011820343c02a4035020055 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 540781232 1250 540779982 540779989
    0x1060801030309030f170a02100b060306150d0b0d0506090120030a0506030f0f01020403050c0a050906011103130306050105030d18211e03080127020a120c0801180209 73
    0x900580340c21684116801703059090035040242500007042075840002891211150f0200d1052108401c6100c10311100002c06c0800109001c140c40302c540c0201d80c000040c40402c1f02000605089540c5500407984407028070009801c40c048a6050729941c02910800c0903d980a11500303030f0062944080128001c05020001191f01000305001803040d500c1c00454260b80c1d042100455200281e030032a0255800501542c0c041d411074401264a4403555001e44e02900d80600d00c042511009040710a031a510403004503080c1da12000600c0d6140002c00c05507844500311403141024500a200120b413551400040c546001051030038481000806440c0b01003003079140400d601110411426801400340b00000e500e041c118003d0000c290020300c4201070035080c031040004d85614025110111180c0ea90112400d80d000c0b0a04034000a01d10304040600040260703001c2c00c504010ba1400502c24500d01ca180801c88212071801404241004010045440701a416000400da2400150300b003000c0140407 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 540782482 1250 540781232 540781247
    0x12012d0612030c05250f080307020d0f0c030b0a020414030a0203060403271e05010f08070c0602040302060307120b04020705060118020f040b1801030603030e010804020604120305090405010608010303 87
    0x20b04008409418000f031200c1000381131403003400868060750040f142134090b200034034a80b144070201c2c110b01500040030f60b404015103800ca90044d154603640095580c4140445020410868a07156440da0100108140300300d5070b0310890a2080040e551810b08030840300e00000d9019a62203503010705040c00040e20040ba4464101c0c2d07050400014a0713a00740001074a0350000b01c11040c4000d030f12100040d50006102c4020f04c54070301d054103180325a4941c4011520704a059200c1e10210b642980031030b11a502c503214034003042e8001c410060805490b0b40c00250f580c1d10135900400003071106000c401c0151550310641c070703d00b401160110b1901075985c0e21680c8401c0c3c14400c03c00030000c200c0c0400d00340005c980440d60205000740d03d041e0f0300d40c1c42d10b440ca84540c104480c54040514448407006071b80d4020700c10003094039010f40343c2410b040084401192002c000034412038000105000024005e00c034044004d1030180701e5100c01d45c90308005000e01c811104140d02030010080040010400319810294 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 540783732 1250 540782482 540782519
    0xc090f080c3a030e03030a090911030c03040b100504110307030f02181e0627030105040308010e130203060703060315140106110a0203061905160e010e12012d06 70
    0x20600c4a403400c0f414190f803e458540c494603014080095514030b201d5204d0308940a5600c03035101007000011046140815010403a1320b01d00c4840f0400201d0081103011408680c4a03092900b00300c2011385901c04941a108001450300510401005005a0039054000d00d0300401c2c00340350841c1081000005140e0040442e0b804a004415440441d000303880744d031a2014101c0006007642e59a028030341c3c021080104440ea00903000030303030180c0700c01440c42c1c18040e9030300454040e44da0100c283d0802c0606a40480090540d00b01455419041d500584080c4401c0e0302c6045142c900007001c51450511030380804030564010003092a00b4400f0511030020704c036840c1503407600e00d050700c1c2d58000a40d03080d1424080c83c070080d40c144540c8080100a02c0440010130305800110310038403c070b88841c2c44c420803004417085c3c4a0301180c404030141d18603501c60850746854210061000d010481d909542d00d0031030318004041401c1c09042504c108003442c600314000c842c00b8510b4410031207140b138010103014020301c1c0039 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 540784982 1250 540783732 540783829
    0x1d090c0306070e0f032a030d020a020f120a020a06030f18021503060a08030c01020d0e0105150609220902040c2c04020d14180a030e040c090f080c 64
    0x21000c1840d171003c00c440c84418040010842ca841c2c8010f00341d035120021800024407a03c0341c028403c0a0900c04143c40c900a0341c06017294810b5840d2004200c00d00c1000090f005981c8502c0c09441d001da91501041001841143c80000e1200320007100d540c180e0740f002614400e01030260341950010b803501c041d0f03c0700c150420a80c141d225100c002c00030300c084071644c0c80442c10f0301c004100700340d01c40c4040d8018488032158480c200500441b41c07410382d003607a5048810801110501d4a561242d04090340140362445c0024281d2a21111200c0002607a07030381410010001070f80d400420b0110f0078140b080c500305201e01d04114603151048164103d45004140301000b14100c0c1c200448100d48840d0151811000820010302040d11a0303405a60055030440d144000c0c48041c03001041149404144c040c0100e8041e91050021103060003070102800b100d0080104009215100103184500c982180001d402500f000c0c00d060020101000f42260b40741040f5038080048009080d282080302112a00030003845 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 540786232 1250 540784982 540784999
    0x20a051e0109020a0803040510080c03041403091017070c0b01061d151206060c03040308031e0709030506090628090c09140a050f0408070c1d090c0306070e 68
    0x900c024058041504000d400583c1c03840049032070800071002d0029100213680c00c000c1107000b41d074110b844000035605002d27040410404900452402200c0e1010601e021085910b0a02c02c0f001050003111220750160020f91084001d16644070607440c0302c3e0304020741c0d1803c8401d80b0714a4030380700301222040c0f28000c01e21090388955420703110052824580160014150000a0840490b0035481c1e40109204004441564001a40e030f1a000c4182d60038040850300460425055640d0b201050f4405014a4000c2c100010709442502003520150310038205562611241407451420302c3ca091b80192450038150820800c0102c4c229140410441440d441d0005a10460780c8417020b40082100c404090702d0b021401c4004108941e45800c0900761080740760080c0c00c59903401355000203d81054407010440f040c2c20740854082500c000103032102d14060114541e1007550741c08041044843c4614030079a40520804102a0a0080c03040644d24142940588014601044010300d000703400046c0300d200b440340 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 540787482 1250 540786232 540786283
    0x80a0305030f07020f07030c05330702040e0a060204031e020913020d060609021e0910081b0304050a0201120924060e13050c0102160b0304081213030f020a05 69
    0x30408034401440071011b940520f5124200180c020402d07010f0903004800700610a114018100d104a041c100540c1429182070003000d1604080c0d805584c041c1c0e4442d07229016000d1803502480fa0141c4240b180c0c0005a484d4510b107488505a440c40090600ca00003c2904502584071200f541d80d119480c8401c43c0e5016004d480080d91307002214401900d65442c0c10382c04500d842c0c0070f034000d003111034403804080007003001000d030107215100341ca80740c540080040c0c00c40c1140c507018a014541012410b8511581e84d034400b002c00505400c216403c0d40e150f07001141120955800695408c52219003074014880c0080030f8848200d05a59440f041000c803030451030410a5106e00d82c0181c2c06446004a50324003800c0c107001800304030322410001c0d40e0314026404141280e41c000907048102040140240130702c1c0b0f26080810085400003401074a0061007041000d0714600301c2d80c1d0b002d03c82d40080420401c4e030b01070350900806960382c00a000003598042c01d00740c004604006800d5500540300c1409080501d031 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 540788732 1250 540787482 540787487
    0x160204050c0c01050403170105030313120206041701020306011808061305010e160801060e2503060f170601081b19050a08100c081005120111041e080a0305030f07 71
    0x42c072100c1c503100b54a40f0040c0400c15921241894002c41500210204c030b98950b005c040e22481107c2d1000c0c00039a0300b0b00c007042500c61a10440080900003400300d410b040da1001800d00e00303500078800316101c6c1d41c004204034081d13030072a45048003c904e0010b8080c150341070008059407a5400380c602440003e940380f4071010007600350083c90320304014501b982c0c4480c14080b42e202c42040d860081860550801c8404600c40300c00010b031074411002c0300da4030804c040c5440341880c6042040407901041640790712011595211000e1f1890040c40814840f4140b43c01e100259070030104107030084c0a00e50024580c4c2c10781207c1000010700034800403910020a03044003510340904610342d44c0055045503a8500c002084000421080485e94407a00c3c18408142140012a40d00d0f804444030710000626800501150a006168180500420b40009440c07103111440d0503013500240c0c0f007640a4920006411500f02c017a810b000c0003840408010491030301e031a85c02514a00008102c18031a030000000905800d1 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 540789982 1250 540788732 540788737
    0x230f04111e01080a0b030a1707080310140102010b031209061306050a02061e07030c0509040e010e191a0910050a06170c13050705040308180411160204050c 68
    0x1a40201001c04030501c2281c0300008041d0024900d012880c0075002440424490080d40704030036008021b4800b21107640e440403219651070045500300d0f48140801800581d9140086004001e03406942e21041e107480d01c0d2805101d03840c1b541504590600a0901044e03c1c0006c00e108103081c00c8000302d84400d51140407880a010361300c0d040d0f01d00c000300040020078941000007071000d5412a42590484c2d80c07214090f01030320a0380d1007401c00d00b076041000508054441d5000b00820b09692501b5803130045440001000e031b616600342c007100303230355160207011001d4000c014800a00760902a00009e5021503110040e0f8507180c29403811440b8031341000503108031014045119260340342e003400c104c0c40c28051001c1c00140201d00558501d2001c104520300100300c00200a01d50307140081c025501c001200e00c42202078030002d008401844418003010000500c0d50000e0a802a419620702c4c540c001c8030310420060b10340c82c0b4074106441c03d042014205190504050000c010740640e00070403a074464401e003480c01d1 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 540791232 1250 540789982 540790013
    0x1d060a0e061809042d03020a02010e0d050607080f011a19030603050a0c140103020405280513140714040b03190603050102090f04050705090409020604050406060f03230f04 75
    0x2e1624100410808901448040380d210170f1180030361041c07040c81001821003e02c0001d00940d000c1d203c18030042d031156551101c06c50010309011044a607543d240c600e4021b0941d078520108175240300b000401481004d299004101e07800300f8031100503800311120518410101c4c02a0307100c043c1c0c002101d0950103900b000d0300a41c1e01c1001c641002c01582031001e542c1c81c2a006408219540c1c5500e450750358800d00a035002e44070002e0a15036482825001c000d010325000005d06051010035600040d290b480e10042501032901440108080c16014001c0c525004020102d03010b100444001e480b01091540a8805031248299a140e40f525042100381303950a150496050503801c0403c08010482c4c190007800c00c042050314008102181d000403c42a03850031644107001580500c10000b040c545500180b10140c0090141803030552a003001c82c0654145030009004260110441d130a110751620a000c800d0951184403110440421280451a5400f400112841c4400301c08902030014154440c41030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 540792482 1250 540791232 540791239
    0x60604050d08090409080c06090c0f0a17010609020a170f07020c01080a060b0a171509061c050a0b100b0a08074b03020403050a0b0903120103031d060a0e0618 69
    0x59034203070345203159900406c45001020f0b020360090ad03081c60404180e40860f12200805403502582000c0042403110f0302c004071064550b48030880051101a54801400003031882e58440040c1c481c1d07100d07031607143c03040500401c040004000400003401d80c046102c0041c90030034a1f0007000d40c0c94040d5030002500c0c554010400c0c1d5070300059000d4140780c0090304c1580c440ca0210300d00740d465544105d00c1c0c0e040c82c0725214035070300b180701140003400030b01d01f4802106a4162908418118030180d481c0c86142281c009004c4031449050401c3c0605c400030070861000038100754504030b181035a0464014807045d4060503980034007002e00000148095003c1425400381c82c107030480c01c50b03221034104011005125860b58920400300d5107942800d14413034000c8034245e0303822400030305c031b071100682c0c80c4411802c0007401c10768640814800b04100e5145981460300850082d40c0705101285041a107031307545210700d98840c0c4904410040c120543d5004050a0400e0303608494154071100002c021054045c6c60040c00c6a0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 540793732 1250 540792482 540792487
    0x91b070b0c0a091d0118090b0c0306031e120d06030f050d0917030f09030a080c0105161e0f0905030d020715030623060706020a0309030305060604050d0809040908 71
    0x54007841507028220150150f034880d46055a940b0118600020709480901c1103a0140300501c40c694034440d150201e601100380001d0205c826031588462035000b51303803aa00f903c1c0d00005010091508000e22403200140c41c05d5404c1900b055414280e444540185807c1c41d05408604c0c0144d500c480d9000074015034000241d01d180c0011031400a40301e410b20050b042c00311b00f01d508080340440050403c0401055103074015032804250382150a255000445280d81c14869003107404005182100540700c200007000020072141070040c4c650030004030780b015603c00c004400d820b1118001d550140c010a040031410850ba50380590704080f01c6a076101c0d00019018451500b42840c42c684c00100f207011200003060080c58034988000440940d81103200c1c00140c9440000c07405007507910303142ca90002403001081c213480d041103a59841c080e60442450300300420f40d110000745c14990507000301ca6104800311016483c2900380740025101540414018241605c00b007030640454542d41d0003118000d41202c3c10300e8 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 540794982 1250 540793732 540793741
    0xf0b030402030d08090d051305041806061202060f0924070308010e01030803010b03070e0d0c0302101806030209280f060305070815040b0a081006080c091b070b 70
    0x194015503040740284145030b84a000d180c492072150f030003001040050003103610065411611764104d842084110004243c0024040d665445540d0698030700c12400028280541400411110a584035481240c406101c2c5001680d401c001c40d0101250300701c0c610f4480c006078002c96060240100200150074404d003002410446010140400a00c2551158200c2c0e80300c942803003030000d0030700c00201000810300040c80310200340e502440d0720544c1c52420700155402c2d40e00244903101e21210a0b10312005440d400e009504107042c1c00b0361440100c1c10440c07403201411030741035a807014a2062004160340410101d85541e215140481c00003210040600c554102000b00030381d031b540030f10a071009400028000203846c1e0003401003610405180d211102983c2e6400700e404580d4241031941684140d4500b48140255240d10039103001e498400010414a24101240001c0780d01e250070004070b80e0f00040c84007800b1790b640750006501c00c030920415007081411818902d01401101340007443d007101e990810 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 540796232 1250 540794982 540794999
    0x301031e23160e070c050a080a0f08010b0c1c050906040f2d090b12100c0f0903021302070f050607030903021501031e02130e062d011e0f 60
    0xc030520104016140c00c1d00324400d4403240c442e1584206a1049140c10004000c240600c460100302070103042038079200e020566605442d5840a504400811861200509100d50140c002409081151710403031030312000400c0d540d641d62000d6150329890300c150304d8069805100d40c058540c121400f030400340d1142e88070026113801001a01503801a64003542420b510307200c10b4200d070b800b44680e1a40031604030781040c0450014242c0400115001400071a030252048010440007480c40003a910004242c003040100802e9007003109642c00802c81c5a401c28405a600d00c58091075031403480d600145c0d1040c2034644980c400700e01145c05030482c0102c804209080384c045d00b00c003003100d01c0707a42600d10a54601141012245083c000580203590307007202c2d000d20846407074a041d810b500080682800d2840140220160342c01100e0701c02654011809101c03181c2030040b40c5081385010551200404a40d80041120f0100d052007051aa06111000010b2084a2078018030252203601c80744940103444400c00d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 540797482 1250 540796232 540796283
    0x1030b190e030a120507020c010c0602030c1207021b010206010825050307080a05011821021e0c090c04060203092214180705090612030d15030c08030c030301031e 71
    0x144d020840c02c180004055920100c1c0c04240b80300c05031541c1d14202885c0c0c4804000f900300428401d91f07180f00700310303c8054060407003805100e01d025500422200d17204000207020020810600c9040d50b0000e8018000302d40d01140803c1c02d14650600146c0ca1600619540b080107110391001d50503015411011940120216070b543c000c5000b5802402100144c1103820380280b20740030080d020011031080411002c1420b042100c194049104032101c0b0288841c0302d190b0b90030407800100696108540168090500150700780e880000410002d080030729004029490784207071410381e40710b42c0401c5000d407101c00c0340c200811081c40c800c4108010b1041354145009503040141e80c038020300c280e2010601c0d966200011040150f07139000d0103c0b0241d48038841030040f404181c1da40c1900300d0106021000355103529101e04042c0182c0920115000d0349541008032614a0580042060390010024100d41c5000001101c1c11681d0000c0080d030804005c4d0343d0350842d01400d0750300900040307400f00c11140703c0c2002d052 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 540798732 1250 540797482 540797507
    0x2090319050106170a1205031314031b010b0a05090c120a02040e010503010209010c110402120c09010e1912170c010f270f1b150f0801030b190e030a 65
    0x182c01c241c40a240c0c40140c3d41c1c8409881c000d00d2046d07201c3e5820f94182c440c1d0091030300040d01800f5090000c50079a1510810700250100104690012071600c209100540041400700c0381400200800c6000b01f010030005a0603005290080b2001c0010440c0c00c0700450407299804000381072107003141840d00d004006940720f48101c10f409070002c80085102c4c6010710803103551180503111491014125500c1566000b400d81b162079001c1d40c00d12107100304400c0c04540070701c200406120b10396901c58401c0051b28410150300d5050040f401c0c0c11006403406c0342a100d0740151181706041109281d22403900b4a515030150740e10503065a008210400c400e181508008280f00300740d0b04c00c4c40040e85081010042c60420491000d5180090381100d010450140414000740d0080d038814031940c506c500c0a80c0640b2141d032007605074400e80d0501c400f94070350202c00c81041d80b00c0f80c83d00030300c1545140c6505c0c60240014101202ea6141c64071200c4528016510004000c260301042e281c0301c404c0468084c00300c4c1e43d03105 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 540799982 1250 540798732 540798749
    0x170903060106050f07061a060a030b27150f0d0b0709061107140f03070b1e0304080f0d0605030d090504061502120f0706020d0902030f0d08070302090319050106 70
    0x120b0864042d0341500c504e094400c205a081c00d901d038496802820050020441d60901c1103d072001c2611003000030003c0d07210a440100701c4669103c01c1c0510014600c21041400c0003881c2c100113041001c1c1c500a0700f2804800c6a00b01800000307001030005c11890f1640c543c40420702d2440c6040200321007850f44138400b59141c0f1040b1aa0b600001e0f14114034100b00700080b60810382050005400039000120b403900007804003001544075201007440e00c0101d8001c00c54052000c01d19a01d112001c20211013484110040d207411800c041e81ca44009002d00350507042c24140101d0000880c803030030343c411030041a005040740d88800308280054800321460241c580103506144d00030544944405a0020304003a5a00800c0b0310b8820b0f041d06001a009030040181c2c140b401c000b020b011a1050010b0310407403145d03490001340e4584c14410103282c90320f50341140700300d41c000c3c1046030780b46500508816402000780c00d015940d020001d0001e410103860007021104060040954018414150320072001c0e00c4000 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 540801232 1250 540799982 540799993
    0x2130b06041403100c270f032a050d022101091101120615230c06011706061806030111180f01020f0c040c0e12010f050a020703050d090f170903 63
    0xf454080183c1d4407005c1e00780046041c04075507406049040340310303103510b4841680424440361243d4095032aa86d4a0f441030b80c1d110181c6903984003000d1400b90002203c043c4012406c001c81c82c01000c104202c16554000e846041030003606004000300310121000fa5140b0402000806039a25120950003056001140000c00841b40a00410650301c90241036070050038102c0c0d0030f1035960004590744003200b1f404034a4010720845008240840c4005172448059010180245605080b9461580c0240d02d022040310346c842d00c24010642c992075243c14080b40300e6092000c0350383d1000003081c09003241c0000d0354481c400009031800c194405007040c01850408641c1d0818038031148004981c1c5920640f9100003e0b006107484545c149025400707a80d81c2c4503d8140303644800c0e44800095108a610007210750165160341d48488000014460554042507504c0114203210190710003d0407400348054110340c00f940c41180005000804064011407588071103520540040c0c84440c14440c1c2101c150310b4000d1050 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 540802482 1250 540801232 540801253
    0xc0f080604090803040609060209030d020c09070807080619050d0302070e0a1b11010b0d030807110d0f110703050607050c07050306060f04020d0b0918100903020a02130b06041403 78
    0x640981014160040440d50130b64a450b11000c0c0180b5040c003084441c113508000c010900d4a05200b0f40c0c98216141d00509290f030f000c0018061903000040c00d20f820000254100414260049a100d4200f4815118194a40450f003203290040c17071582c01c0345900c954140c8400c41010703400a901380550300a594001c0c10358460786ca05c0d006881890714440004424030100300c440a00c44e1284001c294180000841e42d4440d440200b0b4018900f21030590004032003104000c5419000b1502051018203c00144554007050078003e110690310054a000c0040e03004443c0c000d12000c0100c480656001004ea6003d8100a017025090307a100c0d2000b030919020760a40081c0b01e06e00800d10910078074002d88811901e44108003000300075842501c103500c007651b807040b0359091134a40c0c0e0b108600c69000d41466041e040490a690340c07030300c0784000070660303c1800c1003410380000e80d012880c105110750603140ea0201d00d05034907194010304560544550810300c0424001003454920507008501241075042c2c4908841 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 540803732 1250 540802482 540802489
    0x302070302220f090506041209031b0501080601020f0d0e0a0f06050c1e030a050c01140115090e040203121e030a060e0c031005060c030405060c0705100f020601140d02040c0f0806 78
    0x2c074400013411719002400014082501400704080100151800031107080c0c581e50740f01c0250700d2980c911900740000220501c510758010441d650480310900007400209914803141e42c2d01ca10620440e01001880f01001c50346448042000e4058039400c0c42c0d424841703440d000c0080103504180c0044a41d4450722094201641e59884c40f00e01c50500e10000d14900300b4602030560f5654043d41752982203642c0c406900403150220311003135010b17015400700000044100d100c0240300d44401e130019254038820f20203200041e82d0004040b0342881002400380d03241c00881300c15580a0840d6450100611070020070050180e00561004c0d0030707120110410b40041e00c0c0c0c01d40da40114001181c1c0b1074040070b00c122040c8150b14001000c0d00a070010a000c50345131645850100c0c501d034101440d202d60950145406006614102ca900400f00f420b40c542a84001034004c8000d545610600c1000d0001e1030718201540c1c40e440c1e40c050443c1d4150050300600849200d02c1000380b19552600d107243c0028151004034000e4603 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 540804982 1250 540803732 540803741
    0x10914160b0f1806070602120a0f14160c0b040b0901150b03061306080d0c050c04050c0d020711310204080a030e030307060501031209300302070302220f 67
    0xb014140a609019010303224500c4080d4140605502500902068000400d41c0c001841041a66080d561f40350a19000340303400ea2701d481080051160074441c0c1c00401315882c144082c1e0080c8411090070f04440c5085040d02c00150701030014200c1f501000803c030038040f4000e111800344c200c240c002c1004000048082804890074065120000e404002249040c5051300101954510280c0001141d96403145074910f0031303503074003240008104540a10340920400703002091401cce0342038406111038600b104245180384100620015066804034801013403041c034204950030518085c002500c01400d100c2c01c0b085144101c802034903122000118203c1ba200e480c001e035000c50301444000c000fa03001316902039a000b10200c40c0300b5014031081c0407040c041040350082d18000e6004503680d1058281502c401041d402543e007200e4207950390b8100220700f030052045c20500300011200304940416103440e08070705188c40ca03480a07600129882150071243d825030240c041007101444200260b0240903003103010745 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 540806232 1250 540804982 540804997
    0x1e030301030b0c0702121b010905040501050d0212030c0a08120a110f07080910110d0e0a030f020402070b0f060f1206150d0804060306050a230111010914160b 69
    0x1500440218100c503c3c81005002c401e440100400402100d0f0300c07403989841c0c200c14200002d1045080e1218482d600171580741d02814050340c05001543c1444046004c02c02c0180b130080c0115440071612403400030a00903551207101da40709a50810040d824401d1543c1c001900d002c4c038018980b008640d250400b072040842c3d00420411480c00e08040307001c00b17001c940181006a41e9440200003446242c0e44058052001c00d40c151201950524442c502e2440c105403022401c003884085520031080c4e542c0c4c810034500f144d5008804d42003514039880824064054200c006088142c1c40c0e05014800751242100e40c801c00065413254020010101007000202c0310400300d000d0341d00500c0c01304043d0035000c402c4503c64613010340f900e070400866070f4903c20341d54055401140000da458406010382e161480440001f803207507240101181c5070414617000000207a884460511864148000d0304800c290803c00210703822494003c1004441c855207a140d54183d880d022044a9008020a21140c0c103015900013 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 540807482 1250 540806232 540806243
    0x7050d080415060e04060621030f120509070e09070b07060b06090402130338040204060806010b0a0f03020a1205101d0109050c190804030c15020901180605070308180307051e03030103 80
    0x60f00841d40341541c01410403882d4ac070030000c900e0483c424031142070040b14000c1c03481d04010301010f0f01d0107111440e400409000d1139000c2e00070010401000d843c4605444049401400000e0040e2860000500c0f40c4940900b02c0c0d00300d4000b081e4165151007450a003070444e0f0003081c2400045c62900b114040c400e00702412903c40a01c2410030000030b01b10030386c1480d8458030141002940726110428549444402d902c0210320090000d481020664004402c001c3c204d90340c2800c2d420b0401c880c0000d4102d98007529244100c55032040040c3c96039103d03810302c3d00100b03545001c0c68082501103908200c429802d00607002614181008110121a40011100c9050f500421f41a441e548205c04442840c80a4420f4003006403940c2d507032011a4211f0100014040d043c00c00694403000740d00050103d103140d000e802e02d07180404901300065900b0100b01c504950307151400b20000e64980f0490101c25007059842038051002007090420454001440040a010b80c1e0080d07240500c100c4c0311035620700c402d000c0100b0 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 540808732 1250 540807482 540807539
    0x503070b030405070e04080c1519150b1909080303100312090918050d0801050306010b09040908040303180b04080c041e0c0f0f02010207050d080415060e040606 70
    0x22060203502a5400c103101e00207484289035074002401c42c420342030300d054841500000e81c4051f04002000300300c400748610007024103070341b5000b10501042119282100811601d5480c03032907410992001700030142886805054680f0a0400c145080c08544404070001c200205e901107501d840020581e449000790502d116031240c103558a13203003814021602c101c20310101c1030020038400440e0246c0c001880601146091101a604104d803418034286401014041114014802514085461410740d2a450343c9a035a99a60310003090003025110406081980007242c04410136611450018401e010704080c0015540c4841104c100d40c0300341d10900c0c945034401171103402182402c1d0006052390907400d20b441c01c7c0901008a076400d031214420a2000208a000080c40c000c0c0c10130000064144240f008505015085d036903d55200c94141e40304050081100000f01041002410f00c4908281c40e602802000e54a40f074907c01203205032401c81c3c6090500f0800b00744400644e00a043d0b1007188001d03510b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 540809982 1250 540808732 540808739
    0x1e0d020313060c02060c01060303030b041404020d0b0915041a0f0c070213091401060312030e0a020f06041d060301180b061e0a120204110c07031704091404031107050307 74
    0x103d405603110700480c1c0145050048008044085c811540114081d440c00300d00035000000300021544440000204000e00c0014440940c5445100510007580040c80300010b499a0a48500d0328501449100c0903008400c100410028130300c250340b800b59a092501c10050319000380303030340c50781404859400c001c50060100401502e0b000285518080359050001502420340c0c440b82e5110080b0850500d00340c3d181c1100300f041001c6440e04500c0c000c4540740403c42000c992005584818100c074003c5d10404030f10300302440903614401228001e042956410501480c2c100c4154507170201140c0f2a44207510341030790341c00c20320b104100074507240780d00c140e428002e40d407000100031b2180000e140d01104142d4201071700501d51100e00489010f4403020070010307020000361040006444500301700b0825088181701100a551000410350181c070341c07042400004c107446207a1146a4010ba9029120050a00000b082421843e075802c80c0241d01a41e144c4111088164001d6614191417140c56010340c800c40040 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 540811232 1250 540809982 540809987
    0x12030302070602160503071203020a05090f0f0616031409012a02041e0f0e0309012019050d090f0909060b0915120a0c050909030702031e0d02031306 65
    0x10030007540302c0c01c00103082210103115120983d180300380c116816440001c0000070711001c1c071081420500103240940c40c040c0c1300140103102d4014440c0f01d80c010a20140807064566074030262825112014007820307141c2c15240c03020103c00311041c00c1900031030001d00f49060078505c000c0850b00032140684542d400303606454005503001d80b04a800301c1c0448041c98403c001640c50b4082c1c01e4011008000040d48010140008070840344d60204640700c00e49003012000f6001404170a0b81c9001e21300742400605600601d500018a0280b1410301200e4000c4130018130581e03521540685c60140039008440c1e80180f0640192803164103402155080c5405a0080100c0b481e0b9400801d107640c030a81c000325404442ca00411950320301a03542c4800c2d0b4620a0001400b81480c0d900d07921884c1c118002400c4d60b040341c0d12400071f8000a401024040c2c0f00003000180c14071701c10406c8130305d160f034040d00302c40f071a050750481c1510b10803400c10082a00c6c01148040844180700005454004e4448400c4e8402c0a1410401b07 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 540812482 1250 540811232 540811237
    0xc03090c08030c03120a1d030c07061b0308060a0b1309110304020d02090c1308030a0807020a0c0b03281b020c090f0601090f06030504211704142a0a12030302 69
    0x8003d00d02c1d031100031a5450500c00100350b0385c3d01e0547c400440c1c1790b039640340041d41080b405801100401c96000750031000c64803650104105150142442016510ba001c0030071030300354054100013070b041d200054641d04040d8002c8200d0450304101d10400c401e00121020107103912059a0203035008a00a500760058909100d8150b0045441e0000f10301e401c03800c0038840280c05045d4000900c0790008100c0c03449090f001034004c1d078005000c5c8064030583d02e00341c1d180700c0c0e07000c52130083c48240b1001000041c1a404d040c07007180f2251103c4010112146411030030080a424000c0401d40002da4507241072100c40e0000440907880d4900030402c1682c0c0d81c0d180d0650440581c010142e43c1040300d0030307000103040b4034610b00e10380c003034141ca5601060f0b034505030420000388070f100f01a800400f140000200b400c9540050a201c031132003400840d0005803121b04103207140c840030320030401c401d0051403440405111005e01c40305840c4259803000c221480d070b0702e0400c01ea001c154400c0e1503410141186500029100c0d500 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 540813732 1250 540812482 540812491
    0x309220605090444090f090c070311120c2a0d080705030904061203090e0106050a27060207051801061e2703020315010602071211040c03090c08030c0312 67
    0x2840800c5002c1e80d01070599228048981314958800904100035052100c08114200010350720314260b41001c42e0b040c1030b60321a0440181c200a2070780c01c0303c00e890000f8040c000e87c40c8c0c3e51ba44055100d600c1025095102c0c0720b4002024031070344000c0e40e40504028001c214405211004040482e9001c0c10b4984603500c0e40b10b103900302e40e280400c01081249907035522a00000d0b109040180303c4000040ca0701604032040c5810000340710341c2e81c400412080d43d01c001203032413a100714609440410301074040302d86001d240c861200207144c0c2e04031010038456030000f510310440e0021910959214986025090711a40c20b0003680c001802120b51803440711140f480c1c10380c61b444e041c81d060a42e00c40c4032220f0000004080140c1c80c5a03065582e04000b507160070030000803000342c2c00145602a524003c006075450019205404041c2d50a045081c1231001c0c1800003018000c1c060b00601c81d0780c40c1020004d005000c4005c0842da0f00a4690001c00d4080000050b03501c41101107000303506d0f1070b00449189500c1c00c4000c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 540814982 1250 540813732 540813803
    0x70f0e0604120f0b1510170703090212012d020702030714180903071202010c0903170d051f060915030b060c0a051006081f0e03092206050904 62
    0x3030b83e5100289100b180c2500ca0300c110603044100c03000300740c1008103202051010f40e0401000c0745011a260340480b642c00c1e044901c9040002d0b50500a101103100c01c80468880460b651a101c1c1c024120440514048034012804d1014a01c2d094480800001ca005015019415910500040c09080da808407002000c81c401041d95401c1c0d401021104001030045441842d00d82020807841b0030085071400e07c1140d403544d4002840081c04200700102016040d10000d800312070007240b1421030002000c100c0c0c6c02c20190590600191038130b40121003d4292210380080e039400e01c40c40c0014803c0c4a55549010f889101c5084210010200c5045001c0c08410f00c41d981d0000c0100032690030346a0400c00c000526208501500254482c1003145c0308556855100d1041034002c031084a50210005441040403034010b0340c0040c80c568602039052650080303402094100e10031140c0289604000c002a480f100700e110b101703025064450051042c1500c090390014040d0083d00900140b07214111401c2d241d0f2070114 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 540816232 1250 540814982 540815003
    0xf010207230406180e07050f06030a11160f0209060409030801090b0301020f1206040515030709051330020304061407050c090112021207240908060106030203070f0e060412 75
    0x40f02c04144d40d100301001d6514180d074844841c094040305110030001070a08030741894020031644042050780c0700c02803001c6c1400b44c1e65091202c041e44110240c0e00b6150000717100ba00c81c08001c0c94601d03110301050000341e10805100f0000350b803501e4103008452039142d1580c0c46c80c0f0964039044d0100090142146001d9043d502804030038402401003015100c0b000d04200048454140082480221080509000c0500349500d4011501ea2000581ba004a41c2007140000d0300382c0d0356070486000d05c4240c0700002c000e010a04055044811904405180035001404003003107002d00303900c16a81d1384150311580f40400c102c210950341c6240004003404815000ea801d0b03c0d0a600d4544c006405402c0917000b5145203040c003100c0384103504010603910001c001e000010840c0c1030402e4aa080c0c0100c3d800e00c80503440642d80d01d60903000f4400c4400c06c008007c0c031000c40e03846503150480034000c2d41040310b50000045032849140e40052241c1c6040100a90280007a0f2405080c0600310349044041c000580300c40f840c8 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 540817482 1250 540816232 540816239
    0x3090d0807090e0a0507030e1b010c030309020d06060302031203100b030910050718080c240d1a04050a051312030608031b01050106090b0904050403090503010c020105060f010207230406 81
    0x1908540707210300801c13400000c0740e1511031809400c948814001c6035165100e2611002d8480849802180710002403d1407806c0c0320240c6030440141c42c10110094000c4241c8030390f5403c10019400c50000c1e01e03c05c40940300386450075003103c440e5010032590741c08417075203100d030800c0340600301c1d40110b0704402040d007524100300040d0903101c10b681041e1a18800102004500701050441e5103582c0080d0400c0f038090300045040c00006403000d00d0000a07100b00c2c80004500b00000c0400390226040c3c520308290501402e885010b0780080400024941030069042400180c00d2099500c0b8041c030900d02607598222070181380e118a500c040e0040d102c01d0916598000c04989424200080d24100080b6905503903405041c201036801d48406078855000c0c0300c2c11032001c0c88807148210a4818030807043d240050150750380d08040310320800d1503002540551a00c1007041031141d06401041c440c000507208501c901807410700490356001d50f41f00356a01c0c1c5a0103229481d8118102c3c158041d003c10080000c41c1035600c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 540818732 1250 540817482 540817499
    0x50c0609040e1e1e0705100207030f050a02040501050409031e0302090a0803091503090624150d050601051801082a180102030304110603040317010b09040e010203090d080709 76
    0x9203203c401c0386050550f15104803203682001404c3c80c041000c450741648000380c03400241d940c3d0b0f407401411f2241c42005101d1003014420040d040c021500842e014880100508016450b000c80000c10f0b40502d0070500042141d00303060240c42945581030b0365004800d654940700301c0c00d036502c1341c09500c2095020409a143e17961611020300140000e0030180d9551440101046200341d007041c1d40e42e6002d4000c0c0100a00c0000c0072841c20781c0440003400401c00c8034883d0f46003025820004040c0781c4e10210050003541d881c1c640c04041d00081e81c05400400190f100c900043d03d45000d0707041d507606400111283c0c002d59502c03030001e0b540c01104460440c8c09050141c25205c040c4075443c4410001321601161148421000030302c01e01d40400d003030015504e141015100c110014000a00a03402141d000011904251081c203ca08440c1d911460361219940c45401d403001c42c0d441a403c4d50b21036420241c00c811701101c10700c201c0713016a044000030310345103407a400181c0781010000c00280500c619000000303440034 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 540819982 1250 540818732 540818743
    0x20a1205070f02061006081929030f15060f03030d050f04030f080c0403030c150f021c1104150504082d03070f1b0902190813050c0609040e 61
    0x82c1e102c40301e94884401000b0701d800b60081503100740d181e00103801c101c11038104400c903800500f4008908000b0140301043c034007501c1141503034401460741c541c1ca03098644002c901404690022000d0b10764003a06001c800d0f0780d51100309203030700d184802e076000f2903080e20340f07041c1c5040200c0000d02a00d040c012840f072005c08a61080383c2d1124404e6045080108043d8001600805050181480c6150b410114003000207030181c2d000050030b202c610004401809000b824144152080300400c3c13004182d00448140170b50400c214406501d59000c0c0600b401034100e008000d04d801d0b000d1003007801d10b80342c081d4405440841c0402c450a0060400010813010014031004055183c11480c40d2a10b0400b2100da1a2910035140c000c0b030030f9082449040001112076a0380c00d07030395800031414041810802901556038140c1c0d0b10954840e480020703400440107030004102c81214503031301c500341d1694600d400c450f1100d11100004081c0d811070784600740b1782d00d00400940003100300500001760b801c910700c41b01481e11 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 540821232 1250 540819982 540819991
    0x1080f0c0f0316141908030a050310080a050c09150f040c05070203030a03050f060f1c1b062a0c091a09241903140f03070b010f0603140a020a1205 64
    0x80500301c0d100c0302d0400c14260448202e00c100c5c0d200c200b51400c00c0c1940ca900901100b04208079000020490340a2030490344c07009071030048280c1e52403000f607203040da0303139110300c1900d080c098404d010001d140c404c404c4050500d8004003411381d0315807151000801c80240030340401074003400401d004420143c0c800f00f010f0071543c5c11544000480e800c0800800541240c001d2038a41328040440c0d6200c8903481e403040c1d0880d20f00c5e4450311090000d01a10304200851041c1d508103205e03280785240000c07801da2040110f1100326260540c2e000e82d40d004603d134100c512032820b010b4000c00510004002c64481681f0420100f80d0702c83c00301030440018800210303215401da904c000e81c00340b449809001c07050180307050350140c1e00458030305155618962003030b00c24940d00d10002c2c110744a07444101543e0304041c85440c002180000c25030307070b9801640c58080c00b9400280a408049003d14074007003020390082c402c00010310410750650340e4950360740840b40007a5000903111810840c0c8900940030b022164024907014 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 540822482 1250 540821232 540821249
    0x6111902030c0d0c05070e1816030f08030a1b02010903170105030c01180f03030905040509070302460608010602120f0c0f120a0e0405160f1103030a05040b01080f0c0f0316 75
    0x14012300794081c42d05c41e03079042014000c0c542d40e1040001a442c140c41d00b04065000d01d40310703207a580e44802540205000a1070145692800c0c22210000d50b041d840942c138a0b100e91510207039039000340f1000c18423000c01d004850b0107602c00c050b203c000c2e40c040c440d41c0345040740001501030110340f503c80700c000880c01540200c020403101b03070050110b0300d0300307000f0907078805000002040d00302c1c9542c00050720390050a80d21100c840d02010003001c00000d2408000e0303050540b080302950151104507060b603071a200d00c02d041c00140100000b1807041d01c0416030000e020165204142003010b444415982030b40540141290f0b40300e05050000150700c10b03c4940109202d280c1120b44892070460060154805001068866072401d4100301601134514007005890000f071411040e40360072120151034404040c0440c01c171f240300c003104020a010f05c5401485c4114030404c0801201e0344d80b0f012281e511400e40301d000e2596004600c066045040040131100240d90050031a144c0390f45c40c65110f180c05c40c0c1604401407 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 540823732 1250 540822482 540822511
    0x170405040f0507020706030b0d0f111507030c061505100f0e03030703122004080105070e0907022109100203030a0507051207030207080706111902030c0d0c05070e 71
    0x20518140c0300e00406101d101030305114070b2400540c000d4640d1818002c05040c103980d82c15000042e05e5103c00100d001d50300c0510441412030605000442802084040f07110f0080d1030010b1960181c41c009032954164142c984901030403040d07440740c019100244040300070036a040400070b450303900c010404920600c1901c4da0f0051992008000b4a182d0340850080c2c000d070301c10009940001c0c0e2105001107905111040000c0c40e81144038000c0c802941d000c10350104600c0410082800c18042d44224040c048549580011381502c80502443e560110307003590160300800b040b1300c45400c0902d804c030710045036900103c0c60721001c00700240c0003100041d055401644080f0030420400c1980c80b400381c000125080c19801c202c441039414841c079030014000420560046404400c001e821801d0fa10000d5205400b0700c4500303d820161110340d000040d01300224004109003440b8103001008564101600c5809002e42008503103094441d50341c01d03d821106882213100005d0f180c501884150700400c0082d45808 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 540824982 1250 540823732 540823739
    0x30504050106050405011203180519060e0102060c04090b0a0b0310030b06030307080a2d0518010306050f21030703020d02071502070e1f030b060a09060f211704 70
    0x508482d10368004074050307031134000184000509000103244890385031600b61200b0aa846d00c01e4041540c42d80810703044a0058105100c20340101041130680b6415030326030325034069081c012a521003098a1449031584100014450424650020841908090003880c20303d03645043c02c1806500885a80b551401c810700c0500c02c01c160681d8054100303074220001c5041401d41d48520301070b48500c400d0380342405070208002070f0102c1c2d58400c0c101c1c171800c02129603444032035203000980143c0c000b00d00750b4441c407044010108290300034400d06c003d035500a0302600d40610200e0521414914203200150030600100510044440c204001d001d194403c0c6d025144020203618068036080c603540040d04240702c11a144a4007503400500c42c41124440d1811703521549441000c8040711030000c1d07828a030543d03c0e4402206110007040018000c02d4107403903d59809517160321070806c590003070080c950701c0c2452204c200f0080b0094101078481070110017103208240e60540d40d01c041d80c00324045011200002040c00c0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 540826232 1250 540824982 540824993
    0x3190e06070305011a0f120912040b1c05040f061a04020f2511011d06120f06041e0507050918041e030c1506090608210c060403230703030504 62
    0x901d249108082d0280c10044124034602c0c10380504100347c42208080000034401080400c400000c101c80b082e400d5503030340d8448a4204132540000e03202804c0a240c01d00d03070031034000e140c481da80c41a80c000015114004540c2e40f41c0000e0007402003000c400684070018102c0c030f0341d52440100b13001c2240040f840d40d9402560b11907001404030b0329642910044001c0c1e2480030a43c2562203141c07404c402d01c0c0c03868604510000d161501d9030500980b94001e000807459a041c0103800d086c1500499130064135a81e155103080c104000c0c0e4003440c424000144c24240c50840300152604400e070010b8480c20070500300400301011449400800c0b07004040d01c08124280400c0c0250308840c8030900c80410444000380030300e920094910164150002c02404841d001c00e1100a810b0340420050080c00b8014410b00d542d0300d110656507483c00c200c0c008004101441030070668801000c481035510704001038029a81c0715142505c2e00d0540036285c0f40110030300c140301e10080b90740360001c0186138403a450000351400e290600 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 540827338 1106 540826232 540826259
    0x80c090d080c010902040e0304080a032a260304020a2d09060302090916052b06020711031f09060209040903111005070503190e0607030501 61
    0x10b0740300c581040d04411034903802281c0130302c503200d40b441419407a48114403035014107503c2081e981001a0003061204c800c4500d483c00e1501d0703450b403204500d6412030500ea044172a60b40410f41070301c40304042495180f00314483c840c91307820b610b800d5000c10014100c90240d403862075414800d80030107003420440c2c1c6100c070141003a00e030b0306140d5801c0368501403c0c141c01308038429848900003c5100c0070001b07040001c00703402e60344c040c1ca451070081402845411881c80c0808101d010020030100c002d941c98200f0140e01c1140c00581d100310504050041690f032466580c40303034010201401c20b125030355044401c00380c001c060001d51640c482c83d01c100248120103403241c01c582465040d10500d40c00031600758540c0003400035203101c5540c0901c05c50496001b1241c034008514148040340007024406060140c03c82120300004400f8a01e03003c651800d90300312110070010780c982c0014099201c48144 = true := by decide +kernel

theorem cover : BRFrame.Cov 540647482 540827338 := by
  have h0 := BRFrame.cov_init 540647482
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540647482 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 540647482 ≤ n) (h2 : n < 540827338) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
