-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3006
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:23:10.782593+00:00
-- url     : https://prove2.me/submissions/81d8ff59-51f7-4ff0-ae83-b51240a31ae9

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 540467625 ≤ n < 540647482 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 540468875 1250 540467625 540467657
    0x20a030507060e030f010606050306130e0102040308030105041401081902030c0603040807030f02030901020307030c02210105010825090e031902070f0501020a151a0406080307021f020d0c03 83
    0x3403200810b050380d81d4110300c0040c001498186160302854a9160307051000174005160802c040d00e621140590340c046030b044880c0e000401030100d5041500c040d5200140100074403c20070011810fa410030744007405048000500c88075910001d1241d07412030313000303050450030001040350b00408280c00141210040d802c24030000360607604c1600c08540a010018a801c101600060070b0441d100060015604041c03140700081e4880c814810000c08002c015400c010441d624442c040c0d041c0e800b02c0fa841418200c80c1a00a8003c003420f009404076480344010312100c21448003d1811024080e0110441c00752a200110002c6c00c00186994201e000510084e540d0b2407286081d21042c0030680c0c0205011850455440310740b482c0780cbc100074110740000341a500812881a4420352004a0100008a0b0f0780580c50040c1c202074080303101a8030609161001554100000162503024002c880002e540c00c01d40d0507084110200d480c03082d015800c0400055006809120010b030228004e0429a0f070b01a00848 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 540470125 1250 540468875 540468883
    0x270b0601081e09030705280b0c0f0a03090c080a030c140102120406050f150303071b1208072a090504030314071808030a050f030603070e04080d0f050103110d020a0305 73
    0x1e180031031581301040d0f81d024810100264240144d090885500b0001e0702d500788130b0501c41d0160050070400c808000f00301407012800803551a48a00c82c526911091080b00040241031000c030251010707500c8401c0401d01c2c00b404150940416419155103402c55069070754586d0100e41c550f4444c815540c00e00ca6282d0040c903000b800c0e8031452182e400090349140c0500c10600d6104050081c3c850800130b65001c000030b45000045074201e54015107a081322034400040790202602c0e50b0400c01d005c2152042480c1040070440260441d40d200e4100ea0b21f0b94001000801914418010034032100c403207004003080b96008550055402031700a150110700c100c41e0080e61041000182c0b002c80010baa00075aa260413003d0750280e40c050050103001d50700d0600f402200a00c42d008000c0c00c0030b0003000000108885030380801c40740000300781d0000610160f1805051110030f035040004411501c904140003e0b8080c10f543c440c441c181c03030340200c2d91070072000e01106125140c0e9004800f00d0700180019404030129901300 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 540471375 1250 540470125 540470131
    0xf09180512070b07020d120b040608030a0306080601050d0203030a08090a0b0408040303081503072d030b070906020304030506040f030302070f111e0d1704090609270b0601081e 77
    0x412079444445140488040400500b81c01c11500260441040580d001d8618140111f958402092040780741001078003c00c1142d018412520002403004051605600280103c640c02c0b000da814607030b81c42c4240081c809120342c000b58140c00401191140034087d40c49585c0100c4070400700c90006a442d80d421801650030341d02038511074800b080410803d41d1000059902000d000015030000d4070040c00f1990b50505030080d2480302103220346c0501d540418034148503161140c00340d801021650b900b0049000501515a40c0c0003508100012450f20b00020440d01240d40c400004d0580b0740c2e17a500c42c407070502d180c2c141c100c00701038082103800c01180b072209a210741e250141d44100800842c140410425085900300440c0324142c68100960a80e14800c600c03900b44d8102c041c0d2b8460b00c01d1005400503078070541c1c00c41c0c038040d4502200820f00042c0c2da401604a403806c2034079245940b481500c0d01640501030500240440320b8500007031415440b5208454000d5905100310340028640000e0250340c0b1412 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 540472625 1250 540471375 540471403
    0x2090f10082407020307020901030b06010c050319020c0a150f0c081207200a0611090303041e0b03041e03140f130b04061b020d1406040201080106090f091805 69
    0x30400389040440562411604014075000442ca0850706c4c7d804940d03d054140700140807094110001283e590184584404256100c2c09a0340d42d280ba9280c194102109072070110010301c00c000d008501d034102102c03081c082e40c0d222601d8010003941c50008507104203016103100100240782c000c0100090140d40170386404850a42c02005070f00d801d80b030040540d2451600320741c4c4111500d03054603a403100070518046c3c0036040a00881c1d8a090400702c01e00300d1180742002505031000040000c3c4ac0398480945017a24011405c8000d02d65a440310501c00501054901800c1c000d1150f8070705041840806006000034800e007072005d500c03040948120042d402844514070031640002da52005541c441550a0250030b4041c401400c003414503000a2000c494810300e4508800902e404178195038940c8090404a50700c4000720501c101036000c0700340c40e413400765000c90101c1d00070000460450f000b602850151010656070800042c5013011910280a5030300f094294507260111070000f107142031240d60a00080 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 540473875 1250 540472625 540472663
    0xc09040b06070b0a0f0614010e06071a090d050f03070c1112010c02010501080712080f0d020a210506330307020322050102030306010e0414011701150302090f1008 71
    0x1481303d541503d0a00d0001204a0f20b042c00a008040307035010002803900081c0303040c01810900c480410450311888401406202100c2e101880c401041000b80388102000c10584030744802c6d01605851a01484c559000c0300c100a000107401103110f400b58080a600954403880704011807400f14180607408540c80c0c100342d4442c103c03007003100e8090207890b004040d4080140402454603010200c100d2114000400a0300d000031074100c10303004070f001d4403900302d14810704644e1000014000790081c4500107035030080c040c1000c038008101106118692141d0301c050000b11189400a024080d07041b5180d04c0c049040e8111960809400d0b0300c040910300c01c5140707030020365546407070304007820030010700c0d294841c1240610002444180d03408016650090428205030410400d01e000150281020744443c400c016944000042d149180382d40764080c650781113000304521400e800040c00d401c000341c00082d410210140100c0c48034912070b402d035640411a401140c5607241c0701e01d1543d0501c084c1c03422001c0040d01e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 540475125 1250 540473875 540473881
    0x1507060e0610060c0503030a15031e0201091d16020a0c0305060103030e150f0d09080d14060319020d02011814010f0801050f040e0309131e11030c09040b06070b 70
    0xb0070381c4005006418181000e5200d90030b0b90f65090b1b52071000618050b02c50b0740b6078903040b4100340480002d40245601c00444c0b01000010070500000404070241a40040d400e094009055001c1021900282d9009812014960354030035028003101041d0544404601c22502c8075000f1075550305c1e0390307000f07144258068401d5515500b0020b0071f400c2480b51b10380c030a240000c0e8540c0c03c5802003040306c4080c0f0ba00070070030362a1400c64070420020300c0228000380020300009a0070440d0790183d4400c0c603c1052b50021881140c0b40d180c1403503994900440c640c0300c0e001c81d2520345005444c003910242c1080d441403610404c001d4040000485400329540141d03040f100d584040c585075030304510618600b006a1038403101540c5080f00148044900c02e29003070081c1da44508495a491060049900e21840500320340c0b148051540385500a10010f084c1045858100030b640141d40011300078007039820a092903403030440e10f0f00c0402080603031040c14225889650b0383d8010714607490704409460990f001303c1080c11289 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 540476375 1250 540475125 540475141
    0x40b070c050a0b0c0615011e030b01140c0a0219090207050d0f0215060d150c05040602190f08030a060e0112032d03020f04180c09060f050403021507060e06 68
    0x810940061148420038460411040350002c2c5c03245c0c1c0a0501c4400a5903040a5401a5401d1086d03140d000c2c4030181c7e034030014800e1505900250940e290a07a5040c40560400d0142d28244c000c56003498425040b00d02d031034016103018400391a00c038132141e150108036952107525100702e83c0800003c5440ba00a030880c010f1040c0c00c4075400a110741e040c00a4881440d00c0b0a8600044c003005000ba0322644003050f00c1c80600c030310400c80d114510521300c41003100c1c40100030007409507007152040000501c1212071120100b900c1425a10003c0e034011496555001c042e0341c0c42c1000d0300006c0c1844040d80c0e80b46400200148140e48a5000340004038100030744c0305640c10000c105000b0780190a1508200b8600300d0301d1031012250602d503203501c034a001a120301c2c2d0f0f00010b800724800c0f5800401c0040c45455440035611300343d0310600c000b0742036803a150001c45cbe80c0d01e41031310190114100c480214106201c1000076040586d240c2c131042800c581044d140c01984d99520013140e41c80b020401391580400b040080b28 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 540477625 1250 540476375 540476389
    0xf2112040806091b0f010804050f07090510121104090311070b0717120a0b030a06050903040e10080607050d02040e04030c021002070b0f07020103110714010b04050105030d0c08040b070c05 82
    0x329100c41c14000d2138500c40804640341185480c20241000300e0400050b06005083c04400700c80c40c03251045c0c48805036a0344107400a440c05031035034004030588810024003401405a0b44002c540d2041c0165403400ca40002c110081c0190710040d01480300201c00f0600094050241c000174115030018603440e2103041c18240100044281c401c811848208a62038624039080c0c103a81d4465071241020807454050b0001c28280300c2c09030380040940f0304150038072103110000b00141c410f40c0e000640d2101590386021003a41c10040d2841403d03902d8004101040d1a0703403050f0007d129802100f0405403610b0fa03070707008121900d002181e080e000980003420080441c60310400b41220402148024880c1904205510005110300c2140460000e0005520000c42e4001d400561203070401a8001c0c4d221601c500380500124509400800300354078001010a161030240314181c181c0b0701c064028a16680ba200c01500c0303e50f101c4505a6490740305020020705500c2081c014442130b071066001038280c514010a000c68 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 540478875 1250 540477625 540477643
    0x503040f0801060504020a3e030d050c030103020d0b1e01081c0905060d0203041b0810140f04020613091d0115030305090d110d0b010806060f211204080609 68
    0x104074010491200d02540c04686141c070000c810000e040d140c004c05404023500d00303250f0040e05c000815910383c0e07051510080060b00095550308002d1100d5902c050081d18540b00074000250300005d80034522000c100b0701481e85600c9801d2484201c03003074a59240501d6188001d038002d00380c42c0d000307078191400b440108260140c120104e081030b131756007401c1c036001440a000e02c14413001000c0c1c1c0800020300b40a0401e25007110301075489aa4410941c95044640e220462115400710041c10300c9a031400155100044a100c1e0108140010303007a00c0d50360030400e43c0c0e40030800000c8003013114000410724134130501c12509644100181e00404010008040303095926a81702800c01201c440ca0400202c2d8005084070150401111000054061440c00f6403c1110300040c258000710343c1c0c90500c040110041e54941a24030506c100c616550301c0c10104220b86440f10080e61704103d00d150442c002c07265642d004c2c505545604140c504807041e03404c0c45c1481e80c0080d030103100740d0351006c01400f81d07400302032081b500 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 540480125 1250 540478875 540478879
    0x40b1509090606130b040905030901110f15061f021c021f020702120304030605010512011a0108181f06050105040b0a0807051b06010e06010302070308011703070503040f08010605 78
    0xd145400492161604001401107001e0080b0380e041c0c20015815034010f510699004008014081140c28003030b0fa06d400c080c0c4001c1c00f14028a01c1070031b11403000030300781121002d44001007218213903070211801e1042001d0550354100c405142101140302c500f11280220920942c010030f1106282601d40d0131a200380801041950464001c0d8600c090010310218454910300c0c60160f1388000394030200b800984140703600d01107400041000303c04c00209400103070482e841204c0c2006241c282040c8076080b10701051010516407040002440c0d9540540301c0e007a44001c00484400d0034100e2120440e04064222224203807540050400d0400203c00c0d10641c3c001d003000b0b01c0c00e01e08241c1454110241ca100700e8583c0c0301403107048400a40414030030000c560324503101c40e003808050076034204020b41e681800c0c000c4541c900c40b03540000302c29510034400d5800c041c0d019036800303180f88d00e0326038444d100d4090710390140d15600041200e1804600d042004000030041050001d0070b0500c0c1002690840d41140c01c598 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 540481375 1250 540480125 540480139
    0x30b060406080417121306110301140118150809070f03030207090e0709110a080702030f09040f060504090b0a0e21310315090f1415040b15 61
    0x801402c0c0c1c012000e40d48580e00c440c598041c06010082c000445c00382e4002c103200b800c10001044005400340300d900070146c0c45020180081c0f00f01c02c070f050009000074040c00d040c41115003108503045d0b10500d1281010803009460321042074480c1c00524103040703a40300d4070f80864030440901c070700301d4800c1004a00606070349240d92510360171540c0094a03108180310384800c040d12400e24150002050000200802400c01e040003400089004207400c3e400c0030828a02040490000505c00c60000c0700f200c0030018a02405841c0c40300c80302c10030008200d0b040c6030386c2210b540e902d004101a01c50b48607280d80d40c4e00400402c0128540040394405a52005c1100045508401400d0042034100f100c0064140403020340e00303444003044540c001154007011955528000c1e01c0e0481d80f000c030780c1c1e9044807090341c1c0035000d12a201503414401000b9107244003c01000d041c504041d00c800305108000501c9003038140810b54002840f095100c0d4800c01084c0c609071000d148120a02110003000d41144030500e03425a010 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 540482625 1250 540481375 540481379
    0x90605090403120e0601060f020607080f06040c02070509070e0a090e1b0f130c020f030f0f030402010c0c0906140306041a09070305071502010b120c010e0a08010c020d030b0604 77
    0x1164514038040c01c01001d2008420204040b0442a00b010a642d00914201c9104c0e40e0341e00001003d007010070040d00054024480410340c1c4902c9000880d01c140400345e141d071443e460b000c06010080c021500c213002107015040000c40d25640303162843d070084186036140212812014200b2614540c194000840c5600e404803040c4d02e03400c0801c1e43d81001c0300c0741e95500302c8002c043c008103500c0d00c000050594049040700601341c0441095200d00c620300c031070358200c89580e05032040c000ea0f20b20500303006004807201400140104941000119842841803400c05542c9880d80d03a0107480c81c0301a0403040209445070018492407034880c00c0b460031704408900821184c10140c5854070302c044810400d481800224000a10711401000b24000540d4808119141141d8500010140e901d2980d01d5400650074050044ac19103030006061401c6506407000d442207100807001510a056080d41c4107410802446d0005078446e4203204110480300f050300030301030303c90089000130700322034810098901ca030400b4002 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 540483875 1250 540482625 540482629
    0x7090e1e07030f170304140105130f02241b010c172715040c05010203030103020114160f03020a03020d030608120705010219090e09060708070f030f05130c090605 71
    0x114608990300f103801075800c2e07086410803a0039091050342d0400070010001c144410851103c01d42600c42c070b41c00c4000c0003161122044041401c800c01401342580050755444000362407c1e07010307550f0545074040c14040344a129040c4004e031340c100c6c2401100300d4410103040c0301c44100a0041038001c404e94502000a414001c0003080c00150242420159104100081800021000c1070590820740d1200722048000d11036030201281d20308035000c413020005440000ae55500000580303058a078140c40e4001d0b51200c056040328544c10650f0400224200c072134108000c074503c211036000d401d0207607018160304c2d200c81c10040d140c14145401c0c2c50400d444d0520400c020000802c40e5180d550700240344071b41c0c03141a03080441c00790285121100e00840a0b90803500c9090304510014100da40e042814070307480d40e8550000e030f210a001c6807174078040f486150010310f80d01d110303810100360802c550400080050900215500f00d0b0412a11416051000d151100a11410302e000340001c207203980e803d121950821300 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 540485125 1250 540483875 540483883
    0x70f090c020d09030809040b031626150406180c064517010b010206010905070f0e0d06060b03061519080402240405090a02070b01150201060807090e1e 66
    0x4c0058640a004106401250780c0c44d0804000c2c100c005045525900001d9201072110480c2e00c5140c4801c01ca003801c0c0c10a038000c01c42003408030500750b00035011448201c01c1c07030480c0000080c0304640c000c0c0d4440886802d5001c2c40c40b0501900d002d10705829546042c03200c0a01181030314080c80c8401c9110003200703280e40f502000b031101141d8000e903401d24121121b400c10b41d112819904580c5808143c006c12000000c0158482c842c425026401c843d60390742d0714480402140c009072a600000764a07489090030f010700982074604a0700000d811028100c0c103030f80b40c0408a940c942c02c0a90f0421001061080e580b610305c00050b5050880d204540c60510721510221030740101d024000d0500a01500290540d502c16081c1003084050740220321500c0d1601c0700b2014154014020b00f8440d811400c041801d55030284240d844150380500074100a0b420f100c440008003162a0310441190340b21100840c0304c07041404031200a10302224003040c44040361188604127072401203240701030f4403031200844411070002 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 540486375 1250 540485125 540485129
    0xe0a06030e0d030f0212090109060507170a0218040c09170d05032a0705010618111e300a02030906190b120a0b180703170c070f090c020d09 61
    0x3c10005080845000d180019010302028030386a00300141c2004203040c0190401714469125000c100120b075901e0700207072410594038807442d0348150392100042c50780250f603000300200c1030b000390012807116101c400a0700359080640081c00051101408019400c04240003107030100c02d240c003410090f110030390010b100e400001c202000c10725202007000c00d0384940130032402840c1c0904161658030219410014040c280610446525400d80035040704d80800b01d104500b5460b070030022246c039080c6c120462501401c03c000c400500310100f007000803c076a542c100310034070705800886507003008008081c03080c40a1314001d080c14a118010010030541c010701103070990f800804501c04115110f00b40c8010340c0140806030310b4941080b00c400a0707141030b0000003401e44295200da031000d40c150f519164440d40203001403407220059070281405100051103000801c10300c9250940751814100c60351080d82c507141071a480302d921044001401c2c01800d00724050000c0c01748042c0020980500108401882c6603218 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 540487625 1250 540486375 540486377
    0xf1606020c100209100e190e040b011e091a090114030106092a0e10210b01050f09040f02030106030b030d050a0804020906060d050f013f0c03120e0a06030e0d 69
    0x46054050a56030b00c000c040c200e20041c541c102041c075210040030307569610555094ae05204000000103807040e001044201801c00c248102c0e41140c40c0102c407401400341200881c2005010280c40c004039110902c0450080440c030300c41000c5410304c18241405c460b440d420031081c62b13080c180a80059074011140225100b50070a10b40c02c6501c2600f01155100d40700c503111a4401084441040c0c410351180c0400b00ba09020f628240c145000f40b02e040701120f103070713840c800d0220720700b401100480c0f226000500403090f005400850400410f241d014105e0b07000760814030219507035000190850900b04a6079a14040078101a8907060040307402602980e030050009115982d0a0700084042d216001903507010b40700044144024204117403080f408180034003130314580425082d511421400c40c2030060326151000105007003924805c005d44103040700142d90946201d0009840000051100810480c5450a17642c1d011003404510040141c0c10b41542d1120b410036041c40c42200a0110200b0662000649 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 540488875 1250 540487625 540487637
    0x5150403030b0f011b170c0303070504030b0603030901091503060801020c060709051e09060f0306070e120a170a0c080a080601030f090519021309050307050d080c0409020f1606020c10020910 83
    0x1d20080101b0a10442840221030301004c000e01012980007409032068034030646240099a40d17050502d030340c1e4054881c550380051044101002424502c030781026440140f494040342c12a2210788490999000c0056084030b0361218040101d074990000440b8060982194000c40361a0308400000200d90300d01d049600c203071040750110301c01c0d9a61000c50146428003a0586000d40b900b080003801d10081c4141180c01460008081402c9510109848259952102c0030840078580042848100e403c03000c101c006100b0300056050101d805040540b0b01c00c04c4a644048052404d04001401d071900500c00710042814000f0400c0044c0c4041611a60352a82d100c0d030702c03a10710070360001a400d1110014590030030f61070040e1000a102c4040010040e140c02482254842241e0101c11200c0306001c036008040d460b0181b20603c1000103d070000d005041548070840d04280d01c0503071040c0c803410160030132544036a00150f102410041032040e43c40074054800c046003400303070390008a0743d0315004003076400c20444 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 540490125 1250 540488875 540488903
    0x4050d11070f0b0306010f052a0a0204090b150a140618040c0309060b0607050a03120207060f02042d050d0213060602010b0111010501050a0303080405150403030b0f011b 74
    0x300070400c4000812501c00750500140d0381d40035070091036005699940c002a8450840500c4a000d0021140c6c402c07444d03080256409619454440e418614940181ca140501c5141d240580ea0310b016005e903090085d51649807500300038042039101324005140d54004d0502e240100b00317174990351040702a500015181a5030310003815406a01c88003040b00d060354418a4180c0d071414031036142d4089202c991040c0002c100e1745141c1e004003d524010a5802807440e44030041450009200f500f110021450a0070090b0a00719160780e240d065030f030320b4415100403d038049001c01c8100d00b080b19841c2d03114048c09416482403503100c401c00103040c10b07009640c0140c00f042003090440d1034619685403c000308510412015495003c001c0c041e00d03c01600600085101808001c03515040c86000d04980000705290002c511703580d801c1e500721000a0042e145802000e2948005540390111180b00c2c03886940c000990380124001c00600340d01940314241001003032145441130b40e0f1800e52144802d41c0018484403551 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 540491375 1250 540490125 540490157
    0x9180b3006181002032215060f030b0a0b1201020d140708041a060f1306030605180307030318050105041a09011104031e05030715050705090906240f0316030504050d 72
    0x40a1046c8075503050f00c40589805010f6024143c982004031080b05115182d69040329a00441032800003904401145012403806699a4050003500c05c0140081085480b261076590880c3c21107a0180f00303858031503980490311141402c405600c40e900e400c2290141c03c00d43c4840070650040c110004115441074003045599841003006202c0e0f420042a02c82d082c9107c20301040030701051f00c012100c1c14102404941d0b505800d1b048041c0c000c0d4940025030800f0080d440482c060f02003003030340301345205071540301ca800710b04c080c000c039840349000d01c0a000345040b80c5c1c8861401c0c00760050982549901d405692001810301c201140d04480d004645000101c1e03c80c0c0d030f46c401405001000501c0c0344130019414081080661981c90418103c070020803a540d5040400d8800380300d41344500d60300887c40c100081151402480c54030342845038440100104045028440b456403100c80350036a214804020021455950f800c083c000d89c0340d615091000d410540e0f10741e40e940090a08000c180f0590304c4003083c0311 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 540492625 1250 540491375 540491401
    0x60603091903110a03110712030804030507031b0807110102010c1b1406090d030b19050d150204080114060d030f12020c100902010f09180b300618100203 67
    0x1400c1c0101c184c404100382442c0c064034054440204015a00940e000010360303140021840468030380507101c00240d41c0da00d40d422030b440e5008941c200c080c068070a401d0603d1819100814000b80e2040c03122513500c141324200b24101e90807554040c0c0c116810302119444c442e90041e00303405c004060021140c0b01c07080e00d1802c44c1050b0b142c0310040348030384100c0c810464205400a800096911581c904000d040200403c0c01441d2000c6a24070110f0451064104902c0c00c1c0803040ed401980134100b860001c0c1270000205050f40d200d90321080c010b039154020074440707813541d007001c60708298211030350400c0d5004c6540140901c044881d088003130064070400721258180540403248a000c040051f2541c1c1e45046c00010014510010b05030300048010a030003040500039403920059401d000c4d004102c1c504661080300c0030f03011100c082600103180400d071200000c00700c0607400403c0525498801c500702800781c442d10f0030000600b014040b031100d000031606804081220075844400383c02c0581e5036a01c5200796181 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 540493875 1250 540492625 540492647
    0xc0a030512071109040c030c0e04050c060a05070605070e010e030a12051b01050103050a0309170a06021803060124092106060308070b0103060c030e0309060705071703040e060603091903 81
    0x10280400300800c000791901b0110039603100e4004a00400d40301c6c00c80702110002220002c206038848502c0c00303001c0c5800e2000c1c00188500d49016490a0460354981064440940b40301000c1289203070241520f41e00100282c0c642c0c003041e001040744a00a46403220440c034030f02036010900a00041c000c81c2091200b40011f0503543c000024001d6580d246032050341c5805156040e80054882d510100c0c0c00251203542d01340101c4514003c2061441c642c0f1500c3c004c1d4804806907244203000e07510900c284e241401058000c0c03203100320a841c44010031030a41003800c0d0b426840c4007001480c3d0000e02c6020060403140035400164054175480140c1071501038010281604081c26803130000c2600c104024400ca80e490680388100c00c00e00c540f10b110f0030140d06841030300242201d40e40003030007030b80e50906240c4080c1c01c035a80120200c0d10465503654006468401d0700b5101581c41d00001404c3c80f0f092250601c039504014150b403944c3c55171034910640d644851104a1842d40088021860020b1510540000c07036 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 540495125 1250 540493875 540493879
    0x1b08030103120c120207031709010e0f190b04091505030607110307060f0b0109060306080d0c2303070501062304090f02040213060314040201050304030503280c020c0a0305120711 78
    0x42514280c01c40690360b41e51b03511044030101010825040e5428116050f02c2d600d81c0184c49004100ca950410802c444c0400d25020350020043c1a98000103e40301e2601c5005207407504103c1d59540c01c103030030441a200300f110101e642d4540c0070800c20654070005034180c1d10030218030f030030780115405091090461003001c1024022034204002c810600c40b2a0340800920b60003620703141c034207907a2404140c013958079921500300243c014684500485029011038501580b10318502d00c0c0528200912101150f94505482e100c0d51001c14442c003000030920841c230141411882e000c42c01100c7c0c42061050f0440445076600540d11859a4001c20050210800080d68001d20030340d100c4016130744140200c0414403030b00c00000e0400800c0044283c0b0403003141d000302d030180d58ac21710b16526a10240e5490344007806240c01203480d4ac080122424407a8001040304442d20408108043c00e407000910708444c08c074005114800c407610420000700c0000d103241d001020a50302544590a600b81021400030014500b9 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 540496375 1250 540495125 540495143
    0x1d09120a0e01080f07080a0c110a030c26091e0409261801030b01110f0102031602240622050f090a03050306090c07061b1b08030103120c 60
    0x4554020300241c0c6020001e9880240996440c030345018012825070795039010445040100d0350502850304485500f8403a41030a680750203090700710525041500c070094000070340203481c0c3c0c010401c1e802c405070890444200e130a40c03901c60440b610f031200d2055a0429104034411055540400c085080320904008001c4c8108030500c4141404003c6a0802035010110711401c0800d81500c0d17004025500c0d160124140031411200f00c00042d000ac10380c00700d00358140034810700c2c008070365503081103201c0c00707850098000340e102e0920703103880d947d880c02164482d400d64220840d640d8121480e11416007a404568081d0f002d541c945070049020500c5002d1048030b8075007440064020002c2c00c0c3c02841c024031119008400c25624102902e23103800c3d5001c4024000b50040021941600d083c90525030001d81903011146411007540c0c0703080889039020702844090029024441030150003004083c6900c0074031102024010482e50b81c1c03811031205000c001c1032941130902e01c0340d080d8072032041c803006030358414401 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 540497625 1250 540496375 540496387
    0x16052805092d090c01090b040e100510020d0f0f170c1605030408070e01120807060b060d05102715151809060f030b06010c200310061d0912 61
    0x2e412030b4100d840e15207134410001951101d500c106c0307080e02244d1841052900b031500300b804601e032005020b05102019000c8540100d07040d07850841c0c000c6106450340080c0740b08040104040c180c41c9140c0880c07000c2c4125044160361a036044203160454a6000c200d0034050b90761741d40b4400c0b0341d01a00c0c42011400300e51198a00030400e001004205554000c800c13201c1d40d030781d10701a00d231819000740181c03845940862120b00c00500d0075400307042d41d14032440303010440741d1001c000b1075800d801c8041c46e0204c1d2500c40d414003901071119401307240503200c03404d00c100324030049142e0810010f01d648084001d09544490344444484039030000ba000d80001440400c4072000e50100401046219100d02601c07030041e440041c8000451060b0300449107906c130f40602c1c4514640310051004001050207060140c1e94103602d00040c1c1d03041d503250300402d071200d421200c00412414933280210070003080b0905490400d00303000484034403000c1e000c101c40d1400030f1000c554981d14841c1c10111040744404a419000c601 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 540498875 1250 540497625 540497701
    0x160309150c050d14010f05010f1b0c05040b0108271e03030403090b0903070302040f020d060816050306040203060a0c0c060e010506100c0b0103020f010309051605280509 74
    0x501c0f840154820502c401a24264a1003c0680a1103958008120444104195400b0301c4142183c141036040c501d02e036464411881010b120707005000c03501c1d08040c507802d11040c035041c864811030880c02e103000d4405141004c03c0c2e03803206030100031030403100d084000c1070780032010200b0200300030b001c40707044400807880440c040301c0d030ba0740041e40d04038042401d95102140e030030320310b200360b510303803480100100941451502030000401003030341c0024101d0740030040701a2682d090f0007000002c0403204c1c018081d100c0c84c0301d80c0c401c10424035080315100b50007400500002d41e8000031259001290404d000400c0741c0c5401c0245e90a4042c2d050040c4498240302040c0b0102e00c0640c8003501c110800d840e0300d44c001d03a044504560002d45020300900c1d4404240051025040c00501d000380d0034030604001640e0380194a03030501d0140301ea0600034400394003000500141c108001850b030038138402da81008a0840c20369020000c40c070140140c9000d45416400982c4490700d44481c5014010034450741010103003003a007 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 540500125 1250 540498875 540498877
    0x6071b140a050f0604050c010f030b03010905070806010b0f0301030803061c030f031805031b030405030102070602071b0b0406031a0d060905060f1009090812090d1403160309150c05 79
    0x4400d94860083d0b181003848a00302141451259030b11001501888a1200055810443c408001400c0581d035103064421902c0034499a02121701500040188901d841c4803079160403416000407202050520080c1407040d412001d80c1c2c1500e90040c1019240e544080100d01c0d50003200492100ca01004401181415041a0f1143c86400c0c43d640511144d99040c1d2000b4440c030a060303000b03095134801c100011468145075030090745000c4803c15a46403a41c1c0c2c40029007a40c0101c90b049c1d5081d54006028010041c100450b803483e200d09248040810340f0b4400915071500546c0700c0c0b0402c0c9034403650064240b403110107034040310380e000500c0a4003070159428440b00070140342000712040d02c14040400d0700d000000c240c1621130740703210f40b010350407608280703ca10240003040d900b02d881003400d00c1000340c3c016043c411184142d00600040c62241c1800c1c8000304090308107030021803008402c20600c60020a180e41e401c1c00c4885038100403454030715038501620304960010008142c549001580801c07950f01074 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 540501375 1250 540500125 540500143
    0x314190305040906061b02060901030e0601080f010f1a060a030b0613030521041e0801020304120914030c0607110d050d12060f141302360306071b14 65
    0x15804014403526441c00703880031ba100d0032100d40c004111010320001031405c0350080000301c4041c0b60206140c0344069a10749482ea080c0c00c0700035107421000902196076401d20810300b0009032608148442003014410902084403001200d02901c400500c14078118002d420942c824580a0901a5039180702e51140000c0c002a00085509000c0c496084000800302c140514421050300314203850f16150100b0a04510300003000076484448102e000603c0041c02e101940c0b08034025090f80091040f2424002d00000741900001c00300240c4030f4070083d041d103000a0f040e065904c10f9500680d01e98a80c14130a5045224203c0b00d82e1020b000140181002800714401c10034056544039200040c0410300c204069a2603030142000c86014103c040001c0098007411045102014200b02000011000307140280c1c0e000c003947d80c2c01102e481c520b002c00c485e4030304900d404140d46038921011451420700020307222078015200d42d04100c00402000001c0d40c01002004031241c1c4042e440404102e884034941c0c50340a58 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 540502625 1250 540501375 540501389
    0x82806061106190e01060b0f0d05090304030803011a0403140106030203010b040e060c07110d120e0111030909060103020f0406021b1002071701060312020c04110a09031419030504 78
    0x1414600d200d03000000740550083c1c826018007030740800f070303400071800401074032a2003031156486850004100350a440241502042443e038150750786400181c0405952029061b0f0800c3c1c0d1080004002182c240016241911030041040204040c0480ba103400d5000310f07000a450b50a91070724a400070740d01580450b007160720960003404100f4908080104442d490800b070702d42030300001c00107504118080700411006218601c00d04103110380314049184860340140440f01d44107004180800c0740e030080c00c071452200007444d10b0640340c100d5503901901c9003d01007070240200c0039100481c000f0307800780c0c042e201e009504a0b29941c440e41e4540703000395117035414595030444503001c00d4000b540e41010107400d1010101a002003120341c1c9815980e02e20503808100c00c400c2956030f40c0001c400a01c600403a144044d00960040c85044c0c1d15004120490f426800104000c010030044a0360a030380146102044a03080060561707000d00000741903041c01d550f0485001d41098034040441055009800340c400d403941 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 540503875 1250 540502625 540502637
    0xf0a0602033109050c120c0a08010b070f0f050717160518011802040f090e01050a0932250b04060e09060f040e010b010f09051008280606 60
    0x1000800c038209034036080d941244028440410f10591031690013850704a1441642e8918000c00f203a560f0004a605888000f4403c4001400029140e404149140580100c1e04118a041020380c0c5840040c0452480102607500c0c0c0507061062110074000c5400618841c0300c142403044450b0b90164480c0e014540148501006070804141410b0014880c018800b1365215450164208a0300e803524074ac005016007540c07a0208400704820a2a621b900c000700030a1030003003200840112010700b5214014684842145090310503000710b0341003940c1c8c45011603240c4110007100e00d0800020b41000031504840801d216004569250b0602d10415401102a140d000760100d41c44003812810742c4524400ca10000780111900b079030350b10300303605030580068000b0910520044000e0224065400492440080e0395481481d50700e9540c0000040d0000c0a46152091000d81072000081203001c10707d100b1410080320500213a00c04010b0505148600c41c168100310101c01c03d00c0140000e460706029120020781 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 540505125 1250 540503875 540503917
    0x9070c0f08030a20070605090f0a08030f0c0325020f0312060a0806011a0a110d08101d01090509070e010f2301120c090902040906031703041707020f0a060203 69
    0x141c0314a219030380b012501403174480241c40311070250001603c3e25449004120551250010421900c0300f064801e44e00142c9914003001007503020680140b0342c000c4130742c0820400040d1348180c0280070b0f000034105075200348000b0f420746c22440d00f00010400825031100061411550b60354841c028030070724048802074280b0740c40340d00c455207a0b071080c400d00c1c485001c28040e04829400300350103803500300c107140781244849818003105440c00560403682004a4100703014130020382002d03851b2001600051050002190442c1c00d00301c415a814400c0705a415a17036000704484040c1400050024280c281042da03482d616005402d902540c00c1c0f0650032024240c1c43c07184800320b80c0e00883c007081c0c130058480340200304038260481c01030965003401030100030000c0000706840c038040c8054809042065000248181145003002c0d01000c1d444000ca48450203000b0403000402524400c410004051030315078407102c1d01d10108241503101c1c280590711007480d0703030081601607000014159840d002c44404003546 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 540506375 1250 540505125 540505151
    0x306050c12040f08211f1203210207080a03050703140705030915090307050c030c06070201111603060b09070e061b100204030f0b10050d0209070c0f08030a 68
    0x44511004602110789110000d00418080d1102c10070741400f03134469904d005004d005400076240595032104142c40c1200603c1001210315403031010441130341d00a24900c9081c105003e4910006038801402c00000c15050210092128600c1c541550504020341d20352105190000b596002032070103400183c40c203c0000d0b401c80c1300380035290000d0b040c140c80048507143c0041c00c484c03507803000300820001e02c181c20002c000070903e880418401d00c4040b001d55190074aa1508a080001c0503003941d110b917000f21014a00380e500c4108880c192942402c003007548612034848a801c0c079940803180c0038080a03510000007840160b0300300403000303141280c80c10890350744ca0400f6110038103000606d98000b001400075249400020015121840014013190300d010b203035282c9102030760320039041180d0303804101d00300c4010800829280c41e00066122400804203040001080542c00c1c00c940203441000c842010852103800303a0024a60b003034000001c1c940c003114505015a40d94000d54100291510700b10a0b80440 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 540507625 1250 540506375 540506377
    0x302011425050c0307093201120f0501110d060902120a0f0f1d0f030301060210180219080f0a030c1101020f03030708040c0b0301031208040c0513060306050c 69
    0xc040140c4400034501402400303400c086011901c22542d0b4881e03221811182e5808010003c020b20b40110046210380303103400c0040060906900007000b0b804016880650f03180c44008603030640c0e030240010349022001c1e080000e03401080c1f0b48040c06a5180002440505039010000c0050f002c201d43d0074400c607562107510030101d20418001c070800c4403000020900751aa160000e00d00d032000c40c840440d25100c00540f842c110360703412051160b420040300181c214800300780007800f03605492a0103036081d980b4158000c4c3d03c40000e00000302c1c81503507407449401c8041c1e4540b84c0e80c400380d0700031b0074080e40c3c1200c0800002c8418110701960001e4400c440400c032210f8400201300c00b1603a81640d40054201a43e076031070045052031003800741940102c540015205034104042d40c41204150303602680d41c1403600b040c01c20403400350081001614100018000308812040c81008419a03103045507095070f450401000c0e0009a40046a1144891a0450259500e5081001540c1c000e800802c225220318170b045280e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 540508875 1250 540507625 540507637
    0x321090f011e030b0103150e0412090302090117030f041502011b0906080402030715050a083111060a020a171e07110607080c0d022b050705010f0603020114 68
    0x10034114940b02507081c42a002220039132010f040100b0900348500c0381c03540d00c6c249500801001000d80c420402484002e03141c4c01c1c044000344c105024000e080d07401007420f141e03050059a00d1042d817242120703c2e540c0100102d41a50380c8070b01d080350700d0315114280c044614000321415001907003004280000c064504410480d480c0c0030b501e44030f40942c90140d007681c407164010700c1139138140500c400000d0000d0302c0840c1030401056a0351140d940300c441c1d01c0c2c06082640081d0204c02c0c0740c0424819802074085006001c6001242d450356010500c41601e010a030345c0c3c15042d6019003102d0301003000c0046c250005a1b12040a100f0204c00400c5450303c081900c09005414510003000000d8501c1c081d00c400d141c1c0180503090260040380001c404c2e403404650a5400010103d40402e030000301958080400d0041001495040c4098541c002240d002014400c9908810b0750515090710915101ca5028070201c8440507802402801101c0c5200340c148010101c6100a134040307045040c1e0701d003da02e0b0507030881e42 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 540510125 1250 540508875 540508907
    0x20a0915110c01030c031d06010501090e01030f030804080714060615090d02010f0504031e0b06030a0302152205100b010819090c091b02071a09040b0321090f01 70
    0x400140b0b0000110041c1c4040c8540c0e4041c16980c1860020b422005c158500c0001c1000c002001d843d45042c000421030304017a44804100090039006100041c403010340303040c4150301850480c0d0551107508200001d03100700100142061000304180d203c0c040c020461074801c480c00c46005004443c1d010316a0700c24811060b100b0b0380881c027550007100540c011200003c80d0320039071501c0b60520307441c0d43d20301d2001c46041001c131b201c9038101007450301002101c81c2040d611410a40c0030f4441100260790207581c400381c40e01284040c544190008004603003c8410b00c940324486007040415001c241801034846540c04120000541000300a42d1654001e03c101c1d4054480c10882240e1007a41c3c10452004240040b01244c900461030000198180c0310b0144c010706252014458110900920b40a4a03112030f03940710a01c100900c0007001042507410b015240146016100845d0910342d40002a051401d028188103010413080b07551910015040003614180d041541c039011034084400054900c1c520303840e0018 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 540511375 1250 540510125 540510133
    0x1140f0c04051c0f141c030c0804140115091407020610230607061d0105130f2a09060608100902130b0d0905010b0d170f0904020a091511 60
    0xc0c00740d8440e80f9410b880c0380500030300407901900e591120785000c0310b07414403c40d0f5070045034280c9182008050803140c900c258101007200b254070400c007138117800c40200b01501e41914001c3c02c3c8a000c00030b40243d550319070451825001540c4850340c540003041e0f10b06c60b03249c140402c000000c2d106030001812601a950103001e1038507951074070b4040c1e02d0b4510042c00924541060212984194641030090710509200f6200810300790071403080441d0700c2d45002054030075681040203110390b542c0b84030000080c1c20b4128503d820100d0301402d203000c420180480341c001ca80c0007034141c0a448519900c520742658405601407050554074041242d0074201541c1058256810410403c600080b580c010320017180303100100da0005540300030080b036940041c207031b000000c0e032105601000c01000f841880d00c400c030116036420001807551031380008154240d00c0005e201788002080c400c501450f105945104400600941da24044c046004241d4440391280c0700450b0160803c0c2001c00b03004600d9101d002002038014 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 540512625 1250 540511375 540511399
    0x604030b0103150207210f08060108010b160b0711060c09100f0c0b010602060106030e01290316090b130902131a120c1c0302070e0c090301140f0c0405 66
    0x85401d03c2030110020501d5803c000c0c0000003015420900b42000c04598503002d0700014110140c0706001d25452107013080b00107020001c00c3c1e070300411114151149040485d40303a2458103030125080c0150346001c1d0800120b0000c204050303030300c41243c84107035820302c0503242d031500c8504149402d8000d05000307a5100c0740d40031502c05024071800024001000600c0c00c40340c80c2200742c54802003140c003a00402c0043c1c10100040c80003a415001e426450b41804000300404026400848151a0310802c03030b4001c401d9010b0040c2599608104c03920b02d03244400c40ba642c40d69528110f550090003000003050180710700a86041c00c8910500c01c0d0040305802500c2c03103420170303001038111004182030903229210b030b0f604034000e442d0750300c07a500001c9102c0340410013003a81e004080104109456001440030b0040f081c041040b0021386d01045144c01c40301801c020000c00e4503001181c1c00c071030080109540c0c1562900300c210320011031182c011405984802c8021704140c551100014032440341e4083c10b40c00071000450 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 540513875 1250 540512625 540512633
    0x7150b12031e090a05090f1f180c050f0406110c010e09041221020d050603070b0406030b010e1807090f08030a210c0801060206060117070503132f0604030b0103 70
    0x600344110300130143c40c08961074134000341d0900011b0362120740700b0302a4800c10505101200302d80380c02c05880640190b80300c5c50f00d1015030f0100c805014003281140c50780d5219414038051400d4070189410200b0341601c0c9d503260703d401045440800c3c4c440203039204104200d54154060034008030b1104028100c0441552245c030f03507194900310a02000b041183c10000b0504400b00035442d10f03503c0ca04040c001da0364501d800209130550340007401d182d10030b030005081002a1611030302164112690f0f400c1c045031003542180141ca8000d144084207400c200f400c1204040025503c005910500c0c09848144580e134840c0b0001c042a5110b0190440da0340c410040b01d08a1402849144190310b0986d42041007010250600d0094451110700c0b03001144124006000c0590180081c540c81002803800700e070400d21900000c00b0b10780015052a060180c0080891f00c111007001d000914035170050344060802204004080611041443d484a20641001c01e0f0000e40b5004044504694004c00c03821b08036402c45d1030b = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 540515125 1250 540513875 540513877
    0x70f09050901050d0c0302091515121911031e0702010c09060e150c010c080901050402180403230a030c02150a0b18090106050117090a030e040207150b12031e 69
    0x1d017a114010720860000050382c6010002e40304402110b8002000c031108000d001d003c0f40841d001031964a000d00000101c8079140217020782c80442a07100c803010030340d850f9041005042524643d0341303407400001088900b0345081d21008140819800c02c070b80917950042c0407403c80d140c685c6090002810344204002d41d40c8580ea0010f17045070000c20701250f8602c2100f0180307960340301c1c0d0411343c005e946800b080701402d50410050355100080303000a1250f0f18081e170000d2180d10718440f07800c0188407031002150a0500c146082204811030210240c1100720546002402e070b0002c034032090021703042207840300b4110301c0413400c110703a50364200e1840c8194442d505550003402c5280500350300519460034240c1c911030306d2948203010f020840300000b107240c242030006026120110401406840c1881400400200040d00e148d106405186c425611400c900c0001c01a101d0b0035009001e090b04100b4040e0440425400280804000c0711002daa00184445040e01c90248404404c07550348203003820010310200c80 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 540516375 1250 540515125 540515149
    0x1416080405061f0b040906050405060d0b010b0f07060e0f060907181a0d0804030501050f0f0a1e0f0e0d020703051e0a060f020717040b0f0d0204051008070f0905090105 73
    0x4148080f551100c84190454205074040002140c41d03441c100401d0030329200e0305400030010b892500d0101040e0f203c442c140c0030107100e0b841e1104030010751104074464440660b251320741d01610030b02c61003c0e1040015a1000c2e009400c10080c0200c901040041c40b0000b040c2084951076008100c0240512074404024403034a5415000f141590400b0b840701d980d6001150307550740c404c002d4035407a83c2c1581050b030308440c40100300c846062014000d01035000c2c0001c0b603041e0700020f408000f00700400c0d00c50710011304034401d401c3c1c0040c150512800d240135100c0c9400c19030480f0152011a07a01c100750800481c0ea40304030b444064640e0304029000841b9100351901c01201800c1c40e4112203844649a0b900c2e002ca03a88503c0e0890310f01da0120f9150200005804500c514032442c000d00c40c1801d003090400c4515101e1500014008540001c202c854040a07405440040c100100b0022080461001c0a13100a00440c0c90400113180314410315082405980f031141a0741001d48071600707076030030702c4240703c244c3c0051 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 540517625 1250 540516375 540516421
    0x5030d030b0a080a0308090f03070c0302090718260d090611070b040e01051207051309030c1401020913090b070c02010c1407090b010809031608070501141608040506 72
    0x2e400d01290220781041480f003514420355898040d460506c045504110340720310407142c160410040d40b0046070200d80d03100107482d0111880b850540701c00600340e0380e18446101d01c4a01d0701703503040f00050341007148800b003000562072a0110006004202803c0c0c441161258420201e44100300911260f0320480c1d440006501040c00c955466486500000302c64100ba1701502031004400010300250030011802000c0c200d040c0001d102050078600050030720303020420000b03081c0e681d038005031050610a254034412aa00300e01c49015160355000d8940c003179400680514060403129161101108541c4035030828560000d1101c48a52110981156034504602e000d90411103c400da000114400d00f02000941c54584000d104681c41c20030070400751041e07041c00c5414002c0c108200450100048200d402c000c608843d1510710130301500e0005214014218041c040750304c0c113034054445008600c41c03540584421107035542200c205081c01c489030b81040790002c00c950042008201402017003a9404200c0d452 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 540518875 1250 540517625 540517639
    0x209031b0a1a0c0609101a10140d06030c05191d0408121f1a0d0f02040f0b0307030b04050910050402031c0203130b0f1803030702060d020d05060102030405030d030b 72
    0x11072221407a1600644040050750019003912125806507c203413912a000300c0d4448400c07a01c078900156400c03c540f82d004050120903000030005841c0704c4100c990890003000c007003100036220304016a00c120345000c0c1c20f006050703804002c0080d02c4a40c2401040f1603011079001e0b42c0e04031314034940241d104003170021504424144845031070141c0d030a01c00c5d40b140104c10203001903103090031250180000c60754080c002240c42400301c4054070b0b0b103420032100300a010321404681c1000814401c0300a106d16445030028254004c0041130854007040218090b1205030303028800c023113480040004886007633400c140260700c905589608000c050304856403250005040da6a00d5404039122a0580e80020804005800c005070743c44400a01c1c1c00340c81e000e00f001250090030401968004072044c400d80c1c651000f84d20804a0300007080d5800c00484400c203034003070192510781c0301100b0628083d400213000200f56509007800588a944004142c90440c1c030014010240070b1107001d0164014203600c0f54103900901 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 540520125 1250 540518875 540518887
    0x11d070311131419111b0705040e0615030d1d040e100b01080a0c020a080304151103151203031915080d180e040305030702011409010209031b0a1a 64
    0x203480c07140f480309544078000740100d49002c0d4a009070118500d20000c0e140c03860100303511521050380341910007800190401061011200b500c00e8a41000d5611080d481380c140b400782c03a00720001003003003402498050314408612202c181059100c04020040070000382814291611421644000040c4004007500000700f20b92400050350600301d444080481c019103900c2400c06e43e5900100c1c10f03030b0000680740100000031810200075107400482c80c001e01004c4012011405010794901300800180940d00304220606d440c10700b1540359001110500d040030a04141e507802401d05600b220700c0200c021018520799551160321103032042061841420b1181e5520a09034801c0201081d40e000e8140c1c44014901050400b40003810f54500072a030300800c24400c002004000a00d85050740c000c0da15040c070340c1e00c0b9501c4200c01c038010840341510300302c81c010023400d00c900d403030066000704001c04080d8103441d0041c010340340003064040c0c80065a5000166410100700f41700e00c2d40104500c0ca6050424145054 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 540521375 1250 540520125 540520159
    0x150a110c010c051e030c03011401110303070206011a0315100c02030604080301051c031403060414040c150207140d06020f0d050105030c0a05090402040f2c011d070311 73
    0xe07060100180100e90009540340094400004c1c8404c020301d804483e518624082500300442d0006109440c1e54140240c0d0700302050303001d9254207101289110880f6120700d000100255100400c0c0700301445c88a036440700000c008442c0f02100d1151403442d40034440e00c0402010f02400045100800081120001c5400c0c01681d0610405010b580241007141c0c9a5040c101005000e01e014070001d00041034140c024400603801c403940b14a0088200034554a0b071780c50502041c0600403050f86400c044a124080000b0001141c050b101668000010066004500001070369100501c1c02003060b1100b500348000030f1442c1050700041e01a00c140e902504140380c3d2040c064094002c80d200c680c40ca500e40006000c3c03401c2c01c01c04604103240440c0e0f60500c41d440c2030040b450032000580003901443e00c0341c05071081c900a5401902e612046545400c00201d01d505c0c400c4c800385010342d4030204039401c0400000c11407446442c1c01c007040000700e001c1d0440f14075559461805101800350b440d0045c956100d01d0700c900c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 540522625 1250 540521375 540521381
    0xd0f1110030b0405061002101a090c0c0c0303031b0c100606021b04140c090409170901090f030503090d1119080d1805100504030519050f150a110c01 65
    0xd550580c41c04100c2c250342004110544100919082c0200000000100400d900085003400c0d08803d6400007080071080800401000040951a801c9500e05040c00a0a020743d0020103890030010300f507900c6907010504040e241d00c425203402d03424055540801c41480344401c010100c151081e0100d03070350401c0ca044454240d40c0300d036201e0405038200c200f043c04814803819034a002e4510455041242c1c140803210440181c00242900d402042c01181485042d12964426040d06e030304003003080f16260030074440c010303990f100b0f02503280050540c03200000c502c00032248480949900101940c1000070341e2041c00405190030b0800d07070f85c80c07500038401e0205854600502c0803081c006a009810390b800c0210040c034007400d0f03c1e07904040202d140880f5200d07000780e07200c40c41510b03011617244680c3c0d044100d08079010301642d00054403a0040c0b0f40048030003440c4030000390788644036804ac1d40f42c01010440c0140c80d2501c5d00b110115142d805000143c0044403903100e180300000c000c4c080360404075603200090031 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 540523875 1250 540522625 540522649
    0xb0102011b0c02010f0212030c03070c02092d04050601051210060e010504050c18012106090b1009060c02091e0906190605010c02060d02070212010c030513020d0f11 72
    0x12a4140b4101002d5580c8020401030880d03c60004001c00d90100700c04413424800205888407641000c00456411446203c4403c1c1482d00202840f4241c00d1504403105101f00b00e42c1c0c2411022150301c0891030001440859620480d088005000a80e10b001e05100e4043c2a01c801000140075050701040002c0051050358081d100366007000e0314030743c108410301c411a540900714000840c02800807402c6568400c120180300c00c021b20340400d04040000302c0d1006000c8030f24505503200d09004000c6080000c2e6030000310b0703c68007250020320303426495909032000c803078a004075000984d2403c0d1440260501225072a00420000f581c11700325190580303001071000382a604a2400e030040c2c002e01c46440400344490890b101e0700c5808100e424a0311001034041c1c004404000e00501001c5813180354140983e042d500c05d960050b001c8001031b407601009500910466491502003468400440c00185090054120581d4042e00c003056407001c6844070340103155030b1081110b1040d00d8401400f01a100c02c041c81c09 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 540525125 1250 540523875 540523877
    0x280903031e0b01030b010305061f020f010c11070603050105090c130b1b060901111c0615090810020304020f040207051c03020a0305010e0906010605160503070807022706040b0102011b 80
    0x94202c0b00d890005094965900d209410142400b00b0b2003220350300d60310081c86070b403007488000c840010448800c0e030074601004101505075184c000094001a0480003c41c0001e17610820340d03104946800e0103504503a000c0c040d0a070040c0986000a080c1420203000302030422904510724070030380ea685200300003944038000c07201c0004040c2c181d2403090303070f42000020741040d20b000090120b618005030b103000134014500c1031100c0300d0503a403070404480d2980c0c0c08480a82100150035134903081c0a040038086e01418411441944148002d150303c1304010320031f60740280e600400580040c03a4010800c40650081002680c00703004d09000e20400340400b6200b56510010303070f14050380310142c40030090200c0300c059101482c0640900d0402514403070110345c143c190b50b00307030078250b07111510507a480b03050059041d4010030f50f200024a280c10b0001000107016060303c2151005094011040881c0c04c081e801903003600e0130412080030440510303047d00135404020703040c40000380e03003040c406491782c482443e140100 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 540526375 1250 540525125 540525131
    0x60503100807090f230c280509030609062a1c150807080d050714030f0d0606030b011d0d060f050105090f0705030610050d021b0105280903031e 63
    0x512148018000d4041103528840c80c0c051038507840d8811102d40b04000c0c51400c5209002481e00c183c030100096040c9002c8528887c0c002100000e4000f40c45a0702c6012214400c2c0b00c1c10b40000c0340440006074240c170542c09a03eaa5512003d03000540f803c00c0003481b050440e0441c140319449009042c01c03242040e0540c0c0081c08142003402005011a0134aa81c0220415401c0f419003803040c01d1001400303820f040450306d040c580d2040d49007030803101e45d103c1e60303480e03007060200203024141d41c00e081e07019040c204034040c0d007000107540c0e40030280c00300d0745060700517808504401c0348000c1211031107000b0980d01002030042c010644035551624100d40104900b401c1555454006200908000d408558040e610030904096420a0100038020f0701000304101d1096075040c08509200303119a0603100d400104510940d00da0108003039208405444a90f03030301c25903180c20000346845540300b600e450003459040850a0440511800c00003a01d400c1c1c2056040c981c5446100c441d45a07580546410301d07040c12000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 540527625 1250 540526375 540526391
    0x20c0106061107050f120a08040b0d0b04090b16050910050c0d0212030a02070602041205010203040b0907050a090b120d11060f1014010c021002010b0906061306050310080709 76
    0x1c2c0804456182407038140c1e10001c0c0600c900e80790130141c81c00f041c00860741107002d07442c01e00d4098030f024406900106440c80101f40000d0741c1800340043e10003188550002e1280301e5045050204a44800780050440b030341d03520202d482c4c00c2c40480000100406494042c0c0340c105104007185910310480d00e480001000040d20314681c0324203218005504c40103101604500303400c0000004140406090210170507070016070350040080640c100e40c002c3c4030104020349a2512400c0c050f000350411034056503c20140c400241108a010550b001036800040c0310210341401e08001d20020319000101c550406408000500401710400c52504060065a106c4000c90340001742c0d6400e002c40034202961729410441406601c800c4140200f09075250900380da8140031407007004880c0c2181d002c00184d003210584840a0303009506400103a045d02050301d0251154582c0d4051000d20301c00c00d00482a09007640c0810702000784204000c64100038004101c3c0e04803a2140c040c2810580c1e164040d2900603501c00744 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 540528875 1250 540527625 540527627
    0xc0705030d09091406060405120106030b0c03010e060109180906110f1b06100902071b0e07020c030307050d03090c030c060f080c07050d03111308070603050919150f020c010606 77
    0xa6a4404c0440c0c82c080110342c101800132aa180c000ca0107900e01c9410a1682d2074004002544810010350f0401da04c064142447c5016095503402801a6060f0b0340500c3e00260340c070b500500d40b0004444103101c898854040b03400c420b90080510034400c07564251203032242811040c00d0b1028208001041c00303da42d6403903044034140e82081c14443c140040381c1280003040b284694082280045034000c1c500035984620501d032501c0c3d40074448841d940c450710341280c080380e05526240414032451484d000c0710711400c40d52041555078001c01e0302c0103095601c0b0030840c0c0750301c0b4072a41101040900c0342c1d24400006443c1e54680030349034a650005400900740340c4500804c1d41d0302c00c48140c3c224984030360103403401601c1d41f5801d4681c41c59010760021305032280011402e840040707080350040b8070719504070300301e01e070702c0788103240e142c0c05540316900001741044003040844201140b0101401580c1c2007604850301c0300d9442c0947d51440d1000080c580d0350f10715900f5043c1d030b00d03400204000b11130100000f40d07440c14944 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 540530125 1250 540528875 540528881
    0x51b03010c091208311a180f0f03030a0e1c03121d0307060902030c040b091605070218040b090601080c010503042a030309091b050c0705030d0909 64
    0x2920000c11454542c00c000c5061420040107a55402c4680196600b00482d01464021003030040510442c3d9928801300a504001c50f040c419249070042054006089410120883c0a550200b610303c1104206102280c03910001003a01c40c00042d00c0c0b841285920300c0020b00715000980e040e00071030240d41000780c0900d0815400345c071350002002c9000c0c00e42c020f07850051a40700c0026580d504199583c024010301c8180da00006400100b14040701e036190850b10f0800081c02032070000300c0c02481400c0c8299101d240500500a01003000b82c090a25aa1940c000100c404004e150400c10301008004400242e110250000014107000a45a00d00c3c02c0501d445810f2000051106215412103030040c0b103d00310100317050390341c40004d103091901c070b0725582401000c00015101c00b5440d2001d0110b409004a1040e01e20403c0380e0203500e401500c5a9295030080c1910340f00010385200042d00c010340001b032400b174030213410626070120440d140a52200c000ca07183c001c00c6003000c008220340c1502004a441180 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 540531375 1250 540530125 540530141
    0x80114010f0f18090f0b0c1e091804030e041811010c030e150c0f0705091605030403140d0f02040519030b012105060c030414060405100b0a03051b0301 66
    0x90200c100b0a45807001c54500800100d284000d21503c2e90100f01c2405400800400300d150807074800800c40c2829180450075500040320324402c509022541c904d002c01c1f02c0203031180007001800e2400c80f00c0000c0c4c4200802080280101c052140101484d48984c85a104040c0b11010401c0034407411282c50419250340030000e041981004130b8010301e64006940948848088841502c06007a40e44000c950300265001d001240401803003441e01a261500340012400d0890b0010b4503004115241e031030031716844051100c180000318200b013011030000b070f00c548418a030200000c89441e060541000444041d105104601060329401140500040c50f14105030441000b0341d0f0000103415265a50b00c00d80c1d408140304031041d101518250071b04c485401500c6610a40c0c0c0242503031010300e40440c1c5059690425941503808004440d4404400b41c03000580c00e008a800400804085803845820005403040048140c0c20140080d00040061800c0046a441484001710004c4003001c0d00d05040c00c40e002d0f0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 540532625 1250 540531375 540531389
    0x3020f030606010903020f031f05010e010e101406272106180f030409060602070e22170a09030b0a02030f0a0207060212070e010305100b0f070c080114010f 68
    0x1101c18094540c0e00f00031814112941650804c545130854000203040c40504508100005c424800c244030711881c43d481581070320b0344c1c100706241c2e80c6d80365030f00d400024030200c840c503400002000c41407001c83e030248441c09421070000c020030b151060114140101490080c0c9440420800c803d01000d140b426184030851201c2c0007035104a00540601890f950f044090b051500d1604150601c5400907001d000100780c07c0714030300449030344aa03680342b52002801039201d020014002c0e60f501081d000c82800714240141e6a1458072515890100301170200f000e9141d80803190241148140f65500301404041e1040c1c42d095203900350510301c0c40c14030500314940107100f40c0c25580b04204000050301400281ea42110b80e0388001601c50f01c035441c201d13000784070703418110b40c1185c15041040700003035200080c800030351420b0340c0c14442910b40790103000f00712903039029076090362006109140949056001803e2820b0282c1d8038991216551400942180c4141190040d084d800380e0042c422103e038000580700070008 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 540533875 1250 540532625 540532633
    0xe21030a0f080705071b0b040308030412050703050d05090c0a0f170106060219030e060f03040317010e010b071b0b0a0207060f0f050d1407020d02070603050f0a021b0307080403020f03 80
    0x43c143c002e01074481e40c080240070404000c03c03001107207008201c01c0e0140c21520841b5603201c0c0c5070304203100240c20858041700c40c806040c8000c00c00750300c1001650009a450707100c2600340b858440100000e40300041262049115044001c201707580c42c1181c07200104811080c00c11007504010507406a0074080c80482c04a80c1041070070844641e0010348441104160080e05035074030720307524007100c1008145020982c404004502c13030b071001c1c40e0500158082c61003516030403035010a4043c80200705400b441030052900b140e0004100c000b08410040520b9442050400b101150b00d03590b40301d5020f0f068116800e0350740e0100c1c2205015404000b500041d0129081150b1480501d410040c00c2c0d012189608042100100f0505900c051540040110b00001d04070700009181c00c51000307541312105c146003001441004000200e59000c0c0c07107094001c00c0034400d03a01e81669003507840c801950091240c1c0100711840081034446071824405000c290b403180c680d03207584a01c0c600400010030081801280300b40c04c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 540535125 1250 540533875 540533881
    0x31d0f090a05070e1f1112040905150f090c1b16082b03090204090203030a020607030501150c06020c0705100203090907051215060d11030402030115050607030e21030a0f08 75
    0x4240140b00506030f001b4a02089000c0502c0a42820704c1c180800c1828403500110700402c030003e0b5a04054071400c50900700036048202d40042251030042c4883c0e05800c040140d0200d01010f2261004200d00442e078031181c41b00c0c18060404500e041601c00c07100b802e034000400e05200c800001e016000c042107111118450f0800d588500b200301d040e00762119002d0661340c3c1a02411910b1365082400019002400d0380d40707501d1140406911a0400c81300980041e1a0500108000c0300c070800300d40b004506603480c03c44030743c540e80d1940001d60000a240d0180d01c91101c0000e820b03911281004102e41165000d59201d000e121305010341a000981264140034040c01440500c041c10f040300c90b030003421401c4002000561402090052040e041e01044807070500c10494035400411000354050f51082d0004c200d0156081004c2c00c03900d81c04e000b11a80801c0821611022910501d03811500c190000c0401c040202010101e040c0c8200b0107804e6202c0e07030400700b42da560442d04002d070780400b030f40c0c6800c004009107 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 540536375 1250 540535125 540535159
    0x903020d030e07050a140405060301020a02070303030213080f070e0c0301054b030705042d0f09060b01120e071a0c070906170109031d0f090a05070e 65
    0xc008a51520400d582c0382c0581d12544410840e400060101130200c40e44030f0b85a1907200c0700d01c8035007007026001e141480082a070a040c1482100c120364180d40c0076041050855400710041d5011042d00d0b10700b00b41e10341c404902040140080d1001c4186c0c00020450750b0300c2d0400031041c445005005040c45202480104856191700305024102c00c1010f1020034001c141181d00b000c10200712821440c1010401b040c110261424a500000620301b141120120750b0f860b8104426600a42c0704005801c1d00d00301910300c4010f4130390242c075888503400404942c0d09140002c00701220343c1d0b190140c81072a00c804903000707256080014841440c240ca01c09220301a40741d1840380c0c3e00d40051150030710201306642036070500142107050701c210701c0340030040c2c0300b4a56840c500d01018140500070642080e12140c22001140814400c030b503507281e07141c0c0718035203080243c0c40c1c000c4050700340070070f1035420204500c60402d59075298529203100b030b04088000941c81c24804c20082c0100390603446280503a1078004500c0c003a07 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 540537625 1250 540536375 540536383
    0xc1710080304060e011b061a030a05030409020702030307080334080415021b03090102120406020a0f0317070c110d02010e13060f170c040501051804030203130e01050310090302 77
    0x900d00a080c4181c0007a41c40740102d034903c1c0b001b8040000040d000245108206a54001501080c00203012002134250302040603190700e0941d50081c0b15602c1000204264003d54015062150005080d01d04000041d1218a8158400c450300c031b0841c1d500940c80340e241c4695092107804018004020800000c60781c00240c2008405800034181c0102c8018003448030700700f0703011261020145010040040540b41c02160703039800100e40325000d03008840410b410240d04409440c22100a0f0780105600156911451010008400258200403d151000101c070120394240e90050440383d5440038201101c2c20300c0045046000c0e500740c03040c00c4c50019640941c5e13014855003442c203412140035402150a001d024000e154640c0195842c644540d0000f80f041aa03992190a070212a000c0d10781c42c0c102d020410044500134001c442c0d03c40109d8801c05602002c00f00808c1d030051103030044a160140b041da00000380b04046d800f015504850b800140514201400310f00703a840b641520a0100b41c01d15517010f034071 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 540538875 1250 540537625 540537629
    0x30207120305060a0801181101030207050d0c051c081f0501020c01120e0a030c050c1503010b031503070807030309151407030203070f150b010c05060c18040c1710080304 74
    0xc15480e10080b4810742d6881343c000d4000c2480d03100030045914055141541e100c10b206050b518507884000c0c55941d075010740215490198010301802c00880c00c1e00058940401041c0195014801d40d04c051046448407506880c80c402e0607140e800341403901c00f5030980d184403004504c40b01c075019a4000c10036660000307001c2c1a003600c24200600002c6040c6071050080845242c0e0301954801c5400403c14981c00414090b007803801601500e002190401c14481e54031082400c170340c0d0083c0d04000402c448400c141c007035a04404c0d1300d00c0d0004260360081c0024585034198029980e55007000a0410815402014030402001c2d03820001044c01c05502000d4048a000500c04604420025069042510030b1003242c031310300d9021034844d0a0001508084001120100c80460100d18000301c0740f405600601c803100e52168044010440b5507038200c1e0801203500b000a80014072460640f06a07050f130381d640503101d00304a0710382d11100082c5600d6a1102c3c6004007400c0d140100c0303032200c6c092014010110448003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 540540125 1250 540538875 540538877
    0xa0c1b030b0a02071104060e250f030b120a0b01260303040f08070803010b1c051303030c030e060405010231050d0206040e04060f0c050f18030309031506090703020712 73
    0x10315030006041400351440561740503a031062030001e0114242c0000d55035140148511002150310508000b80403072050410f81c50310000ca2030300310b003031120203109400c0034540000c040c140301d0202d04d024620030310f45800074508030703941c01e45c04005020780d21100041880e030302011109c54010009246119443e484080c0c4060200305013501c0c0308050101c1042103482d03407648038200341d40d03a40e511410007440c0d400010100d48800ca0044c0000c000d1445401028005c42d40b50026256400303003a50f00360024100111480c00b8107495030003190788031405010346889280541e0001d6a50307444848074201041e1041c0b1540c505819101c080000c01440c81e180c035017a20800d81d00c0480401142c000100c213802564081d0300d0441c0540108800c11110350019002401c0815081c010050f140c00700307484501400048507100402805a40b8945400140b102ea1084d0041c1c1524605510100071a04044006e4600381c2030910040c140040d80c1411904564031051618046080402c2641c42144801c15030007000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 540541375 1250 540540125 540540127
    0x5010c11030102041d0108010b1806121c0203031503071a03090106090513050105010b0a0512060616080c07080a0c03120909380f0d14030a0c1b030b0a02 67
    0x200c003a4500758116000750043d0201d01c0240908506001c03241d110034005c0100550070601c8070100303410910728110070444141007404166942509001c94a00791004002e02441061144d02d91105014515a05416a0b9014659078034010b03601c0c1241c500034248a0340281d0218004100081e01400000d05c02183c403c042a41d079114810302078007511032504840f140ba8503120034404402190509903070414414002440305aa842c03082101c140a02084031010820070031039802181000041194810b900504040c28441803420002504040090842e09540009005181040200140344c0140b11a50003045070340520f0340e031a01490518400104106003000f51203482c00c0c000c04076a80901a001420040043d03010081209800150000e031b12030030210709c0c3c0e000c80d502140e64000d8140b00150a054407049001c007800781c420051141552050b4122034104416070051008114910306690f400e0306640c014180a00d10303503809a03030000c0142142c8020000034122030b80980d44525244001 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 540542625 1250 540541375 540541403
    0x303040e04060209090115030509010e06060d03021513021e0d021e030d031a010c11010c0503120f01030309050405150f21030301080c0a0b0711010c12120b0a05010c 72
    0x420701a000d0131031030030303888a54400040340e20201418400c02c1900259800d0180d41c4030186003074200c80700405140140d81000e800503d441c1400120050194400e20448000d4480900c2136071342c50300d09544010703050705180c20b00d006514102900d80300b040c1c01040d000c5101d808c51070010f9811521010005c2c0201c502c031854852000682000d000d410320040c0c103442d40c04215140090041ca02c1228144d40c0b9800f00c1e510a860354400d03045044150782c411203941c40c1c140000015210034004020844141c0b00c00c0000c2e20f0800d160310300b880c0c020025000c03d00304550542c40c0c00360200400390030050007580b400f810015440b00c210500e092102003540d51800d408080c0c0045142007402c08500c011081400310700c14010321000005604031400c2c034007039400200704d1004000003c0c2c600d12903060400d20500408020030240c500d85080d5950504103c8004829941c0d81c6042090015508000c61100b4912040e09041c0d0300a11001182c200c41c1e490360380d0709003030020b46002e5114102811241c071603104 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 540543875 1250 540542625 540542633
    0xf0d09050d022d01020106120c09110c1609050a09020904140f0a0507050910080709020a03090222060b09060418020f0c07140105070809090a060e01090b01030e06060303040e04 77
    0x500764810300e0300340b00b000007003901009403e03202150b680d1500661030207000003103242c403c10382c245407543d0000311180d41b24603241c0410041c0410180f0b084681000304540804d00d0400c1149501000429040e1540285000c2c0703101c08541e80100b8031090181000d170390000507591031455650050307000c501d084404210040d441d01c0c1010580100060703214120b03041081c00000166941250021202e100082e0f0700c220224206004078450400305034488401440345880d142c000d050040d0551500007a01120381c2c000811180703c1c9000b04e007450a0200210072603101c80d00a420140590000d60751401e203031000410740901c541d20070000180200c3c015182c900b9083d40458450007402d181c1c3c01e8546d40a40e00031512030400b4810703003065141582855031994000e5003034958054002c1980c0b401d101003042403141d60300f0008d1074110340b16641d01000c0342044003030109034060300b40e0060008500755600c001404840c03101a00c803007140d01c103104004c0c0d280d07400400c4030141c0720304c1f8255100a4442d860 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 540545125 1250 540543875 540543889
    0x81302120f060c04030213110306060d0b061c0515130c02070306050405070608010e070c0605040201110703050601090c17040206160803070e010f030b010215090a060f020c0f0d09050d02 81
    0x88040700c034040c0780144000c0114a102510075a4000c803040c00e190715401c03400748101c50b182091400300700428000682285456405030030704000d16180801d8248100300020340302d6000107415142518032960700c80c43c900700e03442034560051030303141c20308050703824400000d202e01c20f85405049907c2d00d900100040b40d00c02d018032401143d00040501560605280407602c0343c00900076580005d2640f00009082c00a10001a006180b19103c11046848540b5400040c007001041030b0b040c01060350504048000400c800e400031030149010701803c0d418030a900050700c8882c040e50b02003104280503900300c80d0f990804690010b50481d001c5030f49060380101c4101018403803102070b100c9403002c010450865004007040c0c03c124400d070f0b6050881085150182c0132900301794090350059000d4210340c044d41042c80002a0011015002c9802c00400e82e42c6050907980f18102066215070003160300300d000f4500f0424100c00c451074a0152012a50910000300000c0951181a200d009108000025511540 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 540546375 1250 540545125 540545143
    0x6010b0c0c03030c070303021216170f12040c080d0225180905010605060301140f0102010e030c010b09060a031505070e04020309010c140a0903060506040e1c090608130212 75
    0xa41500e0320340044402040e05c4401610007540580200002c08502c44042d900320380703130f580043c62a00c1c810b02654660000100e280c1d400c1c4d02d2aa1020800d030440c07811100040d20018000307000100280c9080c2c54404104103040c0c2c070295a0f80d00020020030641c3d004070b1845c10080c0b2304e4917040c42d00c08004100c2c440481c810340c0b00e140e4000281040c4000c51800d5046804200d000300000c0c002c8603518002d012013407200b40300d81ea187c4a20308060f030400b440c02c07884403c40f0385c0c0c05200102d4801d0403044044c0c250b40c40a904000240c2d550a001082c5040495143d40d1160080b1455114140b8580b5004134043e0680d03480350565030b4131000590240e000e007031040e4001c00f01800842d12460805400d50003007a6035549040030900d41140400d0800c41041211059035259403404a86480c40ea51200a040c028003056803240c0c4503100c02c0d00e807a00401810402c21000c2d007403400c2c4240d0104000d40700b2907180d009031082024010800c02801c480c4a403041d031250307064821118550b114a00c0c1c0f800e101200e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 540547625 1250 540546375 540546379
    0x60902060f0a0201050c030c070210031e06090609090302030a0f09151d03011b0302070f0f05011b080402150f0d0606110d020a0506060411120708040b06040b0306010b0c0c 75
    0x8201c00c8284018600074201206958000b0800d64440724485043c40c0022162503030085410011036006052200c40040104064103000c00d0460559009844d00e03084c004003000c00c142d888004101020301070046900500155408101a12880d24000d4503486441800d00501c4030108900703044c0e030b20403222107008041441d244071601c0c42c40c4100034400350a60368004076454440251002d58a01071140701c8040145c1031365585a442886000d4010350001e0700c040d0f83c081c3e11540b0b00c002107a40508640c0003203104030700020701e5130001408110840044c42107141001501030070000180c458112232080d1000c2004a82d8542410072946102480340415940c3c4960400200040094004110030703054011103050b0340d14071034051000c03a601e90b1401e50192540d44108041802410190b001031102492040042c0c03910010030380c20203120780d09482040005107050308000a03c03820405950f04201c0171502441003007490000607586850600455102d446c0010b0948084401001002030010700 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 540548875 1250 540547625 540547627
    0x4030b042402070209010e0f0403110f01060e1f1d060d0206071113140a0f02070b0f040b0a0902130b01090807030c0f0f06050712051204080319020c1906090206 70
    0x7400000602940004104034014018500041100340d54880810320a80c041101285580e48a442c2212070b10f50700780e0315401601800300030000f5078600f8040c20f0007a00d400030441403d810a40c00d101c6c0039002c44072508a141c4030a035001e01905107051a60b03040c010381440381b400280c695400080407158604802540704d00700185410030401001c411810200f4202c03141400c2181152082065174580304220320062854000500d00015591041d110008510b0b801410000c03140d585e540b5216066401d43c841d50b40d4881000308011004440c03e512000e01c4205100000e0964003140e4442460000c11341055150b0f071a10300640d02c00d8400c10001d020000459640d265203050848000030705001d0a49094117405011403139590041600044030034030f580e950300e00310490f102d0b00420600c6050300001c01c0002c2219404980010b04624002c81c0a400b01c141d81e4207001c10916181d034200d914440c1c58034018040000c1c2e4480104070020454210124000c0428062612000034540100002e40c03002d0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 540550125 1250 540548875 540548933
    0x40905042d0b0601021024061d150706090818060a1418060319050903031b030702011b080106020c0f030c010c02130203090303070f110607030905010b0307031b05060f04030b04 77
    0x30240c1c0c0203610808481d0007e010541d00d0390405c44400715100c0a4034602c0c80303078681d808030500305070304458070032000849070a050514170364400c1c003a5a500d04054944580200344070050345444d0079101800b8000325840c624081d0445009000c400e01d40c40d580608441c00f1403024026016000d030f003001c20000800803940c0345030814070344400e0540004003406c424640800a510703501d000040368051088400c50031100314481c001520705920042906003155281d500c003601c40080300c400c111000b1169150f040044d81031501c0203181110035412070707108820b005801d01c481e0310003007082c0240800038030300062045142c2c00851440032008843d40d00e003520000c2009811003012001c0c1d4041e4089584480e9428490502102c205401002038401c94200001042082c1c1c0030b540100d400510840000c1480c5141c200002e0406034580d006442d804500d002c1c03030301074921100041c0090f11080360740b64100318160b0b1030815640928080200034000100100d020320203846603003030210300001a007840740c035 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 540551375 1250 540550125 540550151
    0x303051b0a14010f0b093408040b07020d080f100305030708130b0a05040506030a06031b0e10180b030a020a1e0608072c06040905042d0b06010210 64
    0xb0940008582035282c50340c0c6040309001800740f201540c50050040107507031603103050382000d80e40a4940752006100d6850084524a00b105002e02c0e0700101e884002142c9030608155800640c0203001408642100022422007030304440e210390022860703a0305220744d540d001070702c030200105904043d1031884003040310020002c03400f00624000d5141510144169910f0112030007a005090780c20000c1041880280300908200014641c000303100040400c010740d49440f54850000e000091080d800017030301c130a1041818500c8515000000c10355848000b41c40c140000c000303284100f1079042095194200c950056030104924054141c0082042030180c0d9075035090406411015404103003914070400c001460381c09614000c1c071a204540b0b0752030b0714440072a51007104500081441c080c03014488032403040790700c881c009003001c1e1130030201c002894202030404a9002c01c00e141e04204210400c000100710a814408068400da4080c1e44441e564659400503400c00d24080e02031040c80b1700d8414007103840 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 540552625 1250 540551375 540551393
    0x30f0c0705130b0a1806090207050309011823030a060c110c030303040209012c130b01081917160303060e0a09110d081b0721020a0303051b0a 62
    0x750021038111000092901100041e91030810b081540a650840d04104491801440c6060140b9560f000110552204004001c0742c0064005540b079a002044108181d42c215020b800446403031307540c840c0801e10701a4510980442204031007140d080495001d01e9030780341041100d111503400b00003484200c40b0ba0600a00c03c0d508000c0c40500740c420004140260b050110480b40107540103050160740d80e0801001000c40e880039903484240508020a010b032810500b020203000d500c9004055554091500f80b42500d4603068005a601c0d030820030342d0813001200d5900341203c507903001e01a01892a0030100b094158040d1407010926502035055000406d503041d8030040a0700c242d601480215121039171144125012510002d01e410b150804441e403e03d00006c2501045100c0c0340502c1c5840300d000050f00e020318000f180380030305c1c0d40013410078050420340f1075568202c034603006101e000d05280e580004400b000180f0002c0d05005000a00fa20103900442d64844005031100840d01d52004a1404540f1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 540553875 1250 540552625 540552629
    0x130203130b0703230612060406050117120a111501080a0b070305190e01110d060f061106040b040c050d030f03060501030c020705040c03180f0605150306040311030f0c07 74
    0x2201e0075071000107440a001e40301e00322100e40640c550399043c1d0b0300c400d0321022020003c0c0085602c8900b036520b10384c0e90f4604002240c803481c49540081565454080c5031500b0801c001100c90181d0480211141090384400039100d512079689000020b014100700e0310f03400c00a40c03041841e00c0c0c1c0341810000c0b842c500b0008540e142d20740309616406050743c1d0b81a0440885406842c0d030101011444203845801c08250002c0d49460b08540c0009050341000740c04956640c4402c94203000b0f15104c0e8000c1180c04c14901500b4000d00242c00c2820006520000494856100400c0104519111804102802200f80c2c800f07000d4407000d880c4551007009420040c001181c00712215000900b011404120b41d4801d0040b0000754426400030240141804100b0010340702e41c1d401c181c1059910480d00304403441c00300b4040090303405003000c40000105400c1060985000424034001d0400c11174000300681c80005041c3c2d4055058a80b40341c002c00012141070461040d01e2284000c000003142c00700d02c2d00030100300141 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 540555125 1250 540553875 540553883
    0xc090907030506031b090f0c0d0e011e0209060a1d04060602010f0b0a0b090d08090901030f0303110a120e0723031605090414030403020411030f0609010305190213020313 74
    0x69042c0904100360083c0702e081401d642014944c0c01003807e113403265403078541001d81c03c2011401c0666080500d000c4507520302c8a0307015691240c0101c8102c0c14484054120340c8041e040c00c3d403801e41c0c00e074041135041c450032840360100b049028060a805c1b9981c88030080210005000307101f09031b5907190080c06024410200102c1c186406484050381c9080340180c03007140d8415040340e081004a03010440c244034603000c140c540385004c00c000c108950300c0032546400f9500c035040082a0fa101410b0060485070b11141040020340d003009a211025045201d1040c90174408501003106070301c008110b824211950310460520380100f451103808441c0000c0c0d41c190010507403c40701030b483c0b1015880c1103800315100d200d41006c9207501003808104081c05ca9050124450202d034a850380c2d035030105048882800d907800c6c120340044144a21800d80b1a40541c01c03483c12203560b400b80d41542c03101621402c01005050301144c0e4a14440110b40792101003882560407902c04544030725040c0d446522804440c40300325 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 540556375 1250 540555125 540555133
    0x90513020c12180901080c060708090406060f12020906030a091b0b0d110403390f141017100f0308190c05030301062a050c011d01080c030c09090703050603 68
    0x900300382040c6040d1342c121488a8001d0031100703901414440b0541c8542d005840c4200100a2a9055211401008014a101e40d6420b06c51482044010403c0b2409901040300c00e00400c442c0d15944c0d182000d8a42040d071002c8005410062441d00299a0b190f8004211003015046400240181100c0c05000c40710303041c000c1071007604805406264588614080200034208500010080d030842d004105010002203d030300203003009540c1620150315081d8031848844921003c14007a03140c500c0c01480002e4030645140140300d15014002d4050380780e04503041d034645040c4001130b22000044000b030000b00102004108400e440c0d0034001d145038043d61501036048079075003042250900c1400003680704c90304036001d54210707400d000b001c80d072a0b02c00c040d04400c9070444400c01c861030a00b48913410070261083c4000c3c144851604000340c441c0e00c010407004400b15181800d202540d0f0400c1220381d1101003044c540780d8030382d560508a12580100e454260300400310104101da000d0b00360740070138000d4004074211 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 540557625 1250 540556375 540556417
    0x90604020a090b151321051005010b03040b040303020d1e0b0906060d0b010509060a0f020f03030106021e0a0f120206130c06030e0f010221010803040303090513020c12 73
    0x82d40603142d007054026008244000c10b2050075413214050440e0304615030008000e0b940d2220790f044042200e40d0f11480d11b002d689049001c00a08010b4581101c7e0f4442092007290300d0448941c0d2140030041c0702401e6200c1e1000001e0406202e40c0c103c80b502e0305c540c00304006400c07003140d00b070075580c6180f11110481d61600000ca4068a0052a07041c400c0000400007894028149504405010300c0301400781480300034085042940d603428051302407440c09640b03280c80c42058880082c607084000c2c4018465410800062041039408030b0044d05034840350044400590650850381d00d4490580700140801da84c4c1100e0904100e200071152030722032010350031240a40c50302400b41000c4900b20304010524201c0103000c101c0710303000f6086070940d04c44100946a121440b13541d0607080e40e0022070b04001c2c00c0761010302c50682a08a828060151104800860034503080d90b0b0003900e81495030040d644180c60708011f40340a2107054044908500080054815510201e020381601f074206600601315100c07a4068 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 540558875 1250 540557625 540557639
    0x806100e01210f060e060c120f0103030206060427080a080f010b16060b12030c100506180612010c1e020f0c100c0b0903070b070f0e010f0306030b090604020a 69
    0x20009800b030b08002150909400d03541c40d50800007801070b007200c98544501225501080620280780b10f68840ba800d0703540e408201903410702d248002006042401300000041c4003181e400a03034150b10040a4030001006a41101d03003a00c110400351002c0c001112009002040000020217444000204d46410030640c584000f83c9400d883c0074041d03100550340a2101c030503400e045400e0100001e015001c006040c02c26040880c03211052100048500e40c00001c1440604500300b0030b81d83d10f425240307401c001c10b0800d04002504c8c005409078150350300b40a03901107012680c80981c0c203804c13642080c0080007001c00d0f040c0041c200308111045140a44298080c00755010f00110740d58010342503080c050301000301283d041108a010016000741004004d03108440010302041c4454014a415401141c07610301ca490a01324a5070014485400c22084c110503070007d68002c0b840b01006042424480043c51445008a0003055a9440540190700c140c060001d03c100210300240114002e84a80142c00c0c0c42c1c0072 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 540560125 1250 540558875 540558899
    0x91a0405210d021f0c171501110c09010312170a0525051e04170708010c09080312131a060111030414040209031024050d02010e06090a0806100e01 64
    0xc19150350407113407a00c03280045000e44c07003000003070303541d007001d0034801d01e10083d48901810440d0300f0310a0300c40341c0303034200101c4d0307040806080c2c1858000001c01041c07140d0004036a0303c1d401031100810320000c0c94031841c40b0328060021145000e0b070440c00401c5514220740640044d0205480b11254400900c1c0d21030740051644402c0ca40d040c0864554a14040351441d008409845456034021560820f00010405100940c5080152525607004044190800c02e51908503000f2940450521850101c1004003000100a03540d503042c07412050405951000340c4000ca0341407401c001414242024005080d62101e00b0903503000301400c0e41c1c4c2c8042c46032420450b40c0c1d6485180200e40d1006403801803501c5520300398000786200d41000d401e0310b0030040814601030070341300320792694000b4618403411150300080e0320840d800184400c651007000a9915000a00200c5a00c501e4034050140040c1c1d40310280c07122050340740200091412507a15241002c1c0c842c0f0520303207500451803c502203038000a4401010b039 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 540561375 1250 540560125 540560143
    0x309090f050c030f041a09160b18010c050106090212011706090303060d050a05150601020d090f03082d0903010b032107030903080d0605150703091a0405210d02 70
    0x802d1051542d1603032100303080c07800001031040742c25030944d40400c0750524424800038050134000d001807580404481f20100c01c0303003407500300d1000c4c0d000502c40440540c4840400c0707018184282046204502103092003800350125801450445000003070034001055041041c60403140d11060948841d0109115a0344a1a058601c01159402480030034610703d408444500854881d40444181a00030b40c0d500341440540c00d81e041c54200b50a0402c19156014059207001107aa850445103e82c240300c00a5481e090314000501140d0700800d500e030301410300403101d0440a00c44940e0301d05208400016002541c403604000b8003c2d400c05600018604000070003a02407a003503070358901d20606840103252207400c203280907400c204e0318060000200300300000a02c464030440901254507424281030000180f0390940f0007001e00800c008813070200f58801c0790101900d1030400702494002c05500702c003155018a4001e00c0e4441c8004080c1940740d50308184292080880390162500f060007040141d131961200 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 540562625 1250 540561375 540561391
    0xa0c0606270c030225030e09070f030507030902120106090b01030e15070e0a1401090e010b03071220071a090a0b0402180106020606040f0c0210021c090309090f05 71
    0x7030418000014498024001e000610b15006060588103410107541400400d209810107299910f0203091692004c4c00e820004819580308150b070408150051140c24840c0e61041019a01d1000c46d40592180d00320008658000380b501d803a00402c1c2c5109070003803d440c41507895852400b03551512a501074015018a0641d600190007640d81403403004d83e030345800600d040100302540c01500016a40c5415400152405445480e601c240590001d00281c1c0303290042810116002d00403c40074169204480c0d0203d001c0c0381482d0001000f0384540050110201d02c0b903a81c01403284d07501840840307900540a0107009000d100303003a54904200880c296003da9014181d90884003803400400c41050485401900c060040c21001111ba0803815a00c4170a17000000185c000070306005075850280584901d5907002c400401550020700c002943d15001c5103484404290045954610855150208810a0305070300040c002081c0301d03d8020601466802400100e620341610308104261903c130380d070301c41e1500d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 540563875 1250 540562625 540562679
    0x15150e0123040308070b010e040f02041d0318091006020712151503031101061511010603060608030a020f0703030c0605092a0f01020a050d03150b0a0c0606 68
    0x658004403000d00c4001c0030400410341d4210021034440c500030061004600078591305880711110304d00403d00380c00c182d02c0701c401c110189081c000801c201c119540c0001c0d40c1181c00258450a100100621004040701010b03180400705800c91030303160000d5440c6031804203d500400e5503540c0d00400c05129014002c000050340315080900000101400b50300505018094401314090109049401d4031000011011240034030b100c20030402d6045061007290b0a10000207000850074040030800201015000070100145c1c0b01054504850030760241f0701540e041041401703999154085c0175a6036001c150254010b02c40c0c1e01c26a494100003182d03050981e90300d0b40c1c900032071081340d49402c0d02800c3e014000080a002e00b019100c9015605110b840d44008a40b81d0603042018030320400c080c420440c00202d06542103080b090000400c003151760a40e480305810009001c004040004002c0d0980350040444d0608c002444412641c021080142251048a06200f55511003000104480c5008084214404 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 540565125 1250 540563875 540563897
    0x50f1201050703020d2307030c050c070308090a051c0312090f05010b01140c06070c0614090d090f030201020604060906091403120c0909071103090607080702030f1203040807030c0c091515 82
    0x8425041189e1150080c41c3c25801c0c645803c2215040c0f00540d030040300c80c2c080c001042401c03410041c0c0f03290010074045401e0350800201240340000d5444031280201005080c0c03405c00b4842629511400030b460308101e02d0b85002c01c05240603030003802100c2d4100d0200b6104548036031326a41100803505003840340c001401d1035803a008001e0394144488001180e4054848214013511001c1c2c56000d031151400b5001045215101c0034043c10868140e006822824840c100510241c0d800181454100c1e038098400509540e2030306160b402040c0c01c010052107284003050503190300000001801c400e2040e801405050b840c4c3c1742c00082d0350f00c244104a608880c8100004003a1030007035031150322000700e0343c05480c40c0c0014840000c00a5018030021924504042006070550400300089084080b4030707001088c0c078041034072420800b400020300080030034800281200416229600305401030742d012003410f0381e0036203586400c3c0203080701e000510a445210b00c00012404070700c640c0104592450389404402803 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 540566375 1250 540565125 540565127
    0x60618100e040c0e070f0306090b030a080318030a050a020f010501060804150f0e010f0f06080c0603130804061106100b040b0a0e03030a030b090f0106050301050f1201050703020d2307 80
    0x203400a2060f100c000d042c2400181c0c1070001e2400740d100300c4003036642c4090320400c00c1c0c000d01103031260340000310300318030b00010203600341c80002d00020b0503604451002d07143d5070740e00041e49000c80d400100314114000400d00d07618070b13504000035104442258080c3c400101143c801542200c1c0d0910400300020040300100d00414600c072412050490300c90408506034075400c528005440100d0300540300c903035595400b0643e410642c03080780340514441401348143e0703141000d82e0796a00c1c840e401ca144200c81c000b0108011140514030700e00c046610030080c5403200d41d69000504000c44005c00c6c0d66060207250300040c0d20b900c6420070807007510920f004590030a0b060800446860700640d00700000e202d0740d0700d04901d20f0382d01080a410050120740c0c01050317013021030052008890005c0c15850741e0303c5c078a07401440255001016030b41541c105031005000c0726034203000214018100e000c00c00c0300d5468042444000b66141e0010a800f0780540c03001d000c0303400c200058200500708484003100302c11281e404030b4003c07 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 540567625 1250 540566375 540566399
    0x120305301504020c25060c0b0703020a05040306050103061a030102090a18020d140a24060c390f050904080702040603020a170601090204060512061c0506061810 70
    0x110700090001400c0100124499144ca21002000402018032844094454210842c420302401391850840108002966181010356024140009154000c200104103074800c0341506c00554220205000c1c0d540d40781015001040514601c200807000d06560844609050007140c1c01080c000d810184800d00d00b2840d40c10f0009441c003008805a0200100030582145020300d84048003520402c01c5c89042501d00341048410241041d00c80340d0900460710402c5010182140484d484c90910b03550b0320b1028500b24980c01290500c0301800783d0340118000080030307101840ca1014003d2541500c600da01c40d01e048080e01000d11a65902210f9200098002252640903001082c8080c00200c0c641d601c82e400074050a009401ca00c02c0d1036520305000c082150304024460041c4582d00b8114505030401030010001d104641508008011002c04140c040c2c03560b10841c2d040188900d001d0302c90642038a001500c0da0815104144500360041801030300c45032803001140651045c15840c22120300c1c2c84905051 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 540568875 1250 540567625 540567661
    0xe0102012702041d0d0503061306030b07120204030c080318040203092107141b010306180c02070504050a0906050603030f0712050403080304150e06040804091512030530 74
    0x6091000e0410b2541ca03c0c080040c85030300881c40d06d4084e22840c1c00c000740248082a40c4803419100e0400004001042e00756200d40d40103080c13441d0840740c1400c04100200230713200d5503200420091484c400061400304c088043d010514803961000f810013003460030032040c0d0000352040751094001352245030104000a8648000301100407500d03060103415114002c84902191540d2a241c00c259440c6804030340d4081d514174580f2090034204101c5041204500c5020f000303010200800d0ba81c2d10b540c10703106008001c4007006040043c0244240c2c9820181c41014040c4490115800ea04100100e030f401d140100c1036030000d03a801c50115003450001c1d150300414203803c0187c070052060401c000710101c0c0c0380c4c900441c1700380e025003640c920031801d10314141d0850360f402c4c108506c503420841c14000001c410354106c0c1d0407103030305040100b01c01a1062009040c04025400180c094175952035110805030000080c00c0c0c042e02180030301890254800c04006803d000c120f152100540440020300c407040030b103400b904 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 540570125 1250 540568875 540568901
    0x1b0c03080912090f0f15070201080a0603030e010806031903020304080706021207030e131a09011401021203090c3f07050607061d0f0601060507050c0d050a120e010201270204 76
    0xc0c0c000a0074002c0751b0102d001300703010040b006c8000350030070646d6001445183c000030070b40c03000c0100900d1034600602401358051114100102080890102d0740c042000c12070740b010300c942030b03581039080b0315019643e81d116225041a900031407c00080300390000c01e2548000c41d540e00700a140170142d80c4d08944441c02d0050b80b0358004456403840e0040c0e00d1500c00c44043c2640b100000c481900c000040000080b0141e10400b008940d0300b2076540566404100110169500700b40b40e6181c2d10390b42c546504100c004400a07422100400e025040722140c0d0480a282900c0c00100c2e07000500d14880000300f8151940000d0742a40c8000750030809810990014592107000301c00000d0480400c00346100c0043c070404a10b2190345c003082000b860907401b030181c0c5005141a04085190103010707600c854886003003500d01e520580401c0f01d0203041c04818400c0c802969800510003c41200116014281c07070401030460b80150b02c6d190903444540c004411280035070150050480d4001c9481c0d082202408984000380 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 540571375 1250 540570125 540570139
    0x3090509060a08060f011e030506190e030c0106030507090204060527030f010b0a0503010504030c080d1e090212031c02090402040801020a050d0507080f0f0910020c0a06140c040302060a031b0c03080912090f 90
    0x2a0103280dd01c007800c0c1c15042a4000721f00e061940c2405454020b25820a000003441007104100160708502220341004c59070b030420501c01176401c103210440250301c41583d0580151405020801411f60114403140030031241e030000b0b5078540c0181401c8039412200140820756421185001c2460600035000014000b0070100742801440f089880b0f00090002d00d0320304907201c8200c4002c51401608048070480808011810030403144000c101c05140e01c0401d1000980c001910160b51706d031601110003400e02c84000390740e50584a80004c2280d8040c02681c40602e1404c000302d514244260300d524000c09001070764280c183c60701202d414420700040d007400c0c2c03503129081c1c89e0707429646140050909402040003a0980c688107040000a64401e031f5400000b00c01d46500300483c041c40d071810341c2e00350303034050300c07102c3c2ca8401c00c079020b0740185580d015440c0703201c0c542d2210a5200e984031082c050018400c0d40e4940f40c4d51289440141e842056047c002811503003448000c1071030408040901480c40024015 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 540572625 1250 540571375 540571391
    0x5090d0c0801091110021203010915050415080709020414120a1208010807080c280b1602040e0118170d0e0d03050601020a03090509060a08060f011e03050619 69
    0x185003110710f408412582125143c613014030618021410442091041c005480280074402c4103071528401400b6808015564500264038801100295000b400b030161081240b03107054001c468000300c80f40700e41c81c01ea01c18050041190304c52402a030701104c2c0400300c00c40c041c109940400c107416555001583d200e02c90000320344049130110740b00942134642a01d8130b403003550426120500301041500045044d40c8900412800d0751a03180031503d960700100d1014240200d02c00410b40e0b4008681e021040c00c000220301d00c1c0201c94040d001c0198a4402c81d41003200c0d01c43c0c00090340c01d036152000d003030401a03003942080300030450311211f04480b00105119140342029044102c0115110300798005080c0d80710249098a080e014030131103401240900040c4449409960010301803c083c0c01074500484c6900301041c11515050030746005091400c0030755840f40750043d205d07800c1c4a001d11a401c1105681c44034841c100ca046100102a645c003c0013030052540c03a41c0f695600004041d5243c01010b0307480b618 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 540573875 1250 540572625 540572639
    0xa120803040f210e040b0102010e151e0c0c01150b09240c060f250e1302040b121b07141510030c052d030a02040f0222050105090d0c 58
    0x14101c0c104009450710200113030320009101c1211400b0070100d055a02d080300542d0f000000164428560303000c1d4100e05000d0360781c06410b80d41d0b24034803164030000415410a0107100143c410160074003a2030103008012000e45102004114200c500c9a03421503d0104062885401c02402094002c810f08205400c509100480040f00e40c1c8564080c2c90540c000c842440700b401c1c5410904c1307030810040701d00d480d01010310040300070320035000003004014801040721015098403021a843d07007070300038001d046403101d94030886001c0c03580c01602030010244c407000000f903680e08d174850034a504400e2404c01303030b007402076503550480c240a1000300c000651040c8020040c441144a13169489880c041280c941d4851840c54091480d00e01e0350412485603669812481e800000c80c21052015010540702006001204c00800e0a02c036940324065003240c201982c2107079000040d00240711469083c1c404000380c0824003110704040f41c42d409101d00250040140812a1512a035130b184414062915805681c1d9039850f = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 540575125 1250 540573875 540573923
    0x31602150a0f050c030417221d0a060602071206020403022709011116080d0c030b0a05010e0612100807030312050c0309210d050f060a120803040f 64
    0x610800958a400e200301c08a81c4074010745401000b01d14080e811424180d0342c00c016680c003080b484001c030401043d224081071407844180e44a10800210030100c6032113000a005868800c049e2801a803244008280f0311981d41c844c01044486981c00740080c582041c0030520202a0220261450754081c0408405071356812150264220628940c1201740c48100c90302511075030040540400c2d0f4940700381d50300251001000c43d805003d0700175107900b45460340c1c038008509024400f07100103640d00c0c1034003543c40f06030151b101198900301103e200300044c0e541e80c0110342103444202c90540040d0144404010800381c101c0c003d80040c0a0b41c410b01c01e240d02c408209107414460707413041e80062106041454030305610b100c2c40b608000d40d40e031600e245290013004940d941c5600024000b0041005682c0aa00701c40c140c01c0ea508614643c1090003142040c400007120302074280c40c4c4610880c0301c4080084e95030503c404501106a003c1461400c1d551141c40701340084407600b0781961005009e840c1411f141d14106 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 540576375 1250 540575125 540575131
    0x6031e0c030f070807080d0828090b09070f0503210906160c0906030209070c051015080607030e3f0307140c0703020d08040512060f090309010503160215 67
    0x10300c1e00d0f0340f9003480d151500403c1c0c2c0c003080803a007049510094852307100802c035902001c0760b903c0b41d041310505409128a00200b2a440e1a42440d0480c1001003000f269562401a5a000125100d041e21040c1040800e03556124055055120b03640540304c114040008440c1c1c662100e4a15003001c00007008118240e120041c02512143d801c0b60140420401a13144000b4000e280803c1245a05581c04204040405001c0900b4015944014070800900708841d0340380b1f028440f4144111520703002c18040441d007a00031090140100030006200c64400d2040c0d20b51007640c00300500c860702003841c0c00c601502964074000ca110780710020381c60111138062440a102e2848020b45030382c82c90141002400b58603820034010b07a0355400c100c80c0d030700740c04009201401e582e012107507542a0050781c5030038042031099a104d44d030000c2c020440c94121840100d50544946400705001c40c0700d83d10340300c602d82c4070b10981c070160340402e13410b0000c9100040a00704140400e034081c01200d0702c0300144120000c86603822 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 540577625 1250 540576375 540576403
    0x170603150403052d07030e0409081912021206090c0903010504080307020f1204051320041820092d0a0905060d11130c02101406031e0c03 60
    0x61590798145096031050741501d400313910f030b810000564003200140c07081e000301034200110b00c822002c41d5a100e5009828041d40312030074030f41e1100c28010030b01414908010038400b02d6a180ca04e810882180d0003210841022221882800e039141e03004c11000c4000a4580e05003400140820750841d2001d12030320f4001d82c00b03000241c0d00c1c0d240ca100003d18021000c8880c4565401c40440c4d0241e42d0548026103007036900407aa00d45003115440318420003030550503080074110034540141040d920f4860014804d40d90b2107680b5290120446000d10103480441a500507402c20042c400d0105840c000064403000c24014400c88a20082610220f104e51035030344014100d81c400c0c5103804651034001c13207403802002500c409111601d07100000503542c081190002e442c0408000000700656114180b01c80c00d0010030380e00700002c2400c03c0e0001c0d542c603074030716490826600e031945030300406800400d42441080300500a0451800c1301c090441104400e502540592145c00c090b0201c40d6400d100355032049a039 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 540578875 1250 540577625 540577627
    0xa0e0402060c5811010b060f04060212030c03070c020f03060403030c080a0c0206010b0d11070309050a05040e25091e05180a060e070b030a0209030c1017060315040305 73
    0x48102007114070300d184a020400f414100054242c000b0020030204490b03005030810301400c0c50318294050240c074030011100c2d030180000404201e07910f80e0070007900603520103908a482000b030010390250184000c1d00c0c0545504030a00026035428401c10030f0401c02c91018203218201040c4501092411000383c80c103e001c26140c20086031610307440031000b075104480d803605003d40e00030b6110194030740c24180104900d0304400545040d032000c0c103802024130b911841d038106698095908005181007414050544501c000900000b030620b4039010f400440e0010300040c089100d00005004268003841710b0003814807007030b0310340080ca00c01c40e80f08240714204012101c0d8000000c1c0403c1c54100d94000f00040790210600a1a160719840020761034006a07021900241c1d101c40705024a24140240e0f00141ea6000b00000708070301e94290741c003d07040300032081c0e00300da000e0301100f0f013041050740b11401110009004041d2070302112214075031054001ca8050306036036402c40042c401c1c54051008403410b8008c100 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 540580125 1250 540578875 540578953
    0x71106032406030c07060e03040f0b0a030609060e070c0317070203071a070806061b010615021b0603060105160b0903071e050c0d1509110406050a0e0402060c 69
    0x104148403a200041c0c01c465080c41c6240c00a4100801e0140d50783c09081d041d522440300184101c1002104e01504050a50741c0d080341c0d9032110700c6000e900600000c40001c0c1085c80c002000c0740e2a0207a00151428989180602c0c0d0f140201214002421081541004a29040d400e9120b00540300c85008049a60186a9448150034000c42080300c0d5590420880404010000101d40c400c42c41c0380c0000d001c95842c3d1b41c03600d242480020b0011404a000115440c01400080300c00807a000c544690201da02502c2121000b20401000c00d00d5040c0020380041040000a42540c03055008115100405a10320340b2070420303171500ba4800e030040362900025480001d0744414000c400e183d0703020302080300308040c0703e0358510303030f141c94440281880180c0940c2c5403200304001c000c80703500e40d40d100b100c1c1c040081100000504203c05144010f600d440d0089248c0400480d150802d07540741c2042e9418602d00000546036603080c405180e100410012450040c03013001f500c1080000344a08001607010380c0140f06030 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 540581375 1250 540580125 540580171
    0x2010501080111030103050a02060304030c2108010821090310022a06010b0405010c020a0302100207030b07031109132409060b0c10050601022d07050306010f090207110603 75
    0x1c3e4100264842d802d0003400108002080003800f4217003280c2c140d4146032682c5462905407030040c1e042100912110340440f024030b018042d43c00550a00c2e40655480c01c0d143d0342c541000b034992400e10401c80c18101070781280204140120000c00c45d41d0006030864042103070024500040740c02102d1085400e000444000340800031031504011b0304140c4202419039540340159188551041e880f07010305020340110000250b43d1003441c11401150050b009840b4040e0021002703490721128001181c0b4079200c1400700b908144a8410004050368200f90b962802442d802001108420108402c60003601c13541e0340040c984003003100842c01041d800c1001001030501d100c0406540c031344d130070140c41680d0501108002d60000600c01891240030b840000da00e44031080102e003803000150f09401d00001c141d54070b0007070341024916010744a1110003070321403e50702c130010161120750a00c00c4d00c80201d82d070401844003080325401010500d1003030711450201c0300c0c01c40220f09240c004032400240b801c03500c03a01407010 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 540582625 1250 540581375 540581381
    0x3031c06090b01020319200d0f30060b1b0f16062007080a110927011e0605120111030c0c0f010203040602070c120201120c02011506020105010801 64
    0x1420842074107100241181e00000c0da00c1c0101c0e4892401e50f11110000100c01d801091021884024100030440b10011403c04580e50040f40b400d4100040865043c034030103900c500000019904142c001c0b10343c86450600c01c60703940701c0e240c0043c0c0641d07548140002da03542242e0018400012081c185000c0c244a84004500b02502181e40100300d0b0008101c0e10b039a852042d0300d41c019654582080303880c050f2903c02c00c0480300303601086001184526480840e5007280040c2280c181489807821a40501c00b50041c852118800d5841d480c0d0400400c5d2502865070303126042601d031004171000050b40b10000384241e115408060012031703010303035145024480d0341040300304092000345c580000d0041600e0b40b10b03850b226200061040034110303400b0072101034000c0280201903101800600035520fa04050424000950007002c1c110381806c4101e0340007400400c3d0200610440350140c40b4070034280c10a0b9481300c003404890000000719540d0389503000d09038201c0c2440a02514007540000340641c11f280c246821 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 540583875 1250 540582625 540582629
    0x60902030f0a0809010c060e0709020301091802060d23042102030310060e0f06030c030a05180c040f06030b0a1a0a03020a1a090a081b04050408030f0c040503031c06 72
    0x10940040ba001c0000c10503103030483e143c4240070710300280003a10608000005003c40d4403886154010a400088d1588150300030398140c03506007204200e10309007101c502100450058000f90040e03818045c42e05811601d07030014044114044808110b07400746032101a0580303040703500303c03100c041c050082c91501c1070303560541c480c9000b24002140386080c02c011940038410607100349010440c000001c940d4030345500b110b21070340e040094075030354881c00d00da06062b529400c01c5845008a51410000541c0c3c19042c00b408a1580302e0103014141038400801480041d190780a06d0304103591701c50b01d000000030001ca500ca849000c0d60741b00002c2c80c80d03813410404411a40a18040c0c030652006100b1720241e55202041c0b821210b401281414200420009202c4d0303000715140581d21104240000a400d500403075910010401e486608901a60400422040707400a0710054682c4400f0310006100301100410250040075614049050541d1040028510781c0144d41e10041e141552030750b003030005075602503440 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 540585125 1250 540583875 540583903
    0xb04060503160507050a0b090f030d050a0c02070515092b02010905041b0c14030712030506010207060c0f020307091505030615150f040f0906080d031e0e030c060406090203 75
    0x840c1031360503280c1c40d03524110703c0006001400002d010403c0c5201c01c0054901d0900c03c7c50a4a4940080300c070310390014007084484210145c00d01c5c0d0401000351010501d00261840200800301c1104244c218005c5500b20042107030300a00d400d103000950b03444402043c1c881480781c5000090b0650a4400142442c9440c2d0105020754103042ba04000d10618213141014075405140c080c90000c3c482c100380c803118a90000000301030100055200910200318004181e0202680741440b00d80c844e40f004995aa41c80e21030400000d10303000b601000140700240324215240001c4c1210300480c0c035500310108840010f03060300c1002c40300318410405400c0a01c0100d9004603007520807101220039501062103046440408828400000380e900480b12100c000d89000d4500f003103031400c0d4151520001d130b008003507a025000d028403035020f02c82c003028070901070b03090804804142400c0d070405107100b40f00500b01d031102204072400140b100d500c041c1010000244204c1c020400420700482ca8014141040080f81c1c4642d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 540586375 1250 540585125 540585127
    0x6010b2104080f180a0e040b0f0c0403080702030f0601090213080615091e0901050414011b0806060702090405010b18070f080c04030212100509030c070b0d060b040605031605 76
    0x840c46400c20f4541181030154040c0d501d0480c0710b1002c1d500d101c400c0c1c04690019a40e50081b85910100c1c0c1d0f8148910702c80d0008041503101c2c4d05900e103094500315850ba0644c8e10810081c4005203560019014682c4050700302c0320300c010380f800300c0c40c02c00c80c7c00d800c0101c285a0110f05107030070702224848800140801005400d6070f043c00440703c1d821400910086001e9514140030400d082c45c1d042c2110114401090034903400c0c1000003110340a000140d400384d03400c88105648004451043c0715402c0c02c00c0754000c2c04411003410304419161001e005103641d5001405100a002603221408602c0c030035403040340002a00e9022400b08100415030007c44070618040c6800c002a2b2a00031900043c40b151038145142c0503503035080c4050141c4240d800080d008403c044200c014074000050324210000c035494144400d680b044070304c9941e8003487c415a4440e9000002c2004131025050061900030101031011a105484280c0a1456807259110038001140081000306c42240319180c54603c0c042482c100d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 540587625 1250 540586375 540586381
    0x2010c020c010c030228120e01020d0f020327040f090b13021509030304030f0b090706022a0409060606020d12060e06060d0e07090c0e03030f0301060c05030c06010b21 73
    0x2560b408110304806030b00040040c940c80001c1d41c6c4400c0c00c843c6a44010b112948100b201c0e001400f41d1140094107000d480b98181e00d9101d64066001d003504134035030303900640c10072620f10541c4102d1100010107101038032107101c900030300c0c0d180c601402034214245d59011a5107500d070b18103c000c92400030000141c482d09003440e94016a600130410130382540c2c0c0070005450321003501c0003e00350300c9650b000406000710050843c040010760840300d80b0907100305003900c0141d80d4440d010fa0b11101c588070444403542500d412000005601140860814030241c00000c0b20b04c2581d95060807604190040c41c0035900104070200390681c40000f006112098113010b1100c145032030794281600101410081c0316007000b1509804044042d8407529400d0303024821103002503a10144038006001000d40d60000580720000d0307900a04000003269002e0780542103181c616840e05100312042d9000440072203980c0400c11100100500800c1307142d020b401d880b08202d50711041c500c003820020b6110201c003c0c11848503820 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 540588875 1250 540587625 540587627
    0x190c0e0601020c060a02010b040c03060e06010809030d2403052104140906041e02030601120207110405100317090a050d120806060c06040c080111180f040609020a02010c020c010c03 79
    0x2100e0041c1400307892141d1180d0401001787c3c0034210241c105038000380380841c40c500090b8580c10075001c0702c05204102c00d0940350f000c0116400c40d0100d80e1115291320800821140401560048400141c1101c4a0b600c280c3c50003810140347c8569401950383c0e61044160919a19588403104150305009010600d480c0c504110030b00d110040c00c032154868032090001841c1e0781c036250080101c1c4c0c582003a003407076002e14404105000350400e550960021382440403548003043c3d24402c40d6401a0000c003808004000d090400000c0d10000340261008210107400000140d50020050790750b00f01040c5294813400b0340300511608410742e0707102d50b206040150740d000200e400742540303041c4070700c039407a11110950310321001c284188200e600f000d9161007604200000d2084602507a8262100c100082c403401d9900b80c00c90302c2c02d009030101d420503031200040344101071402040481d403003500640b021440a59400340f150803a0000341c440b0340944d454032408130805606115407041c041d800d003060500d06d840783d20 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 540590125 1250 540588875 540588883
    0x902120601141909020a09080f280606120f02040c0804030507032712060506010c150b01140304030309020312030c041e080a080a14090d1112190c0e060102 68
    0x80308070300444040c0d114040d02c801120040014211403013041d591503000040c020140e0340c40e07100d89800341c02142c1d40d0f03901352940800c1d811032090001d4182184020f101300d9882e40c81b0280103040300c07620b0341c40300001071200b4181e408a401902855001c001c031000c90042c0415201900d000c18200a00c050810000940100a40d0b0000350949064095403c046070101c0b0303840e5006000078030040014070001650280841c039402e450f0710500040c065030716000010740d0003041e40140148190010701206060801c2680190f01014051601185010070305054410317a5205840a50010351280080820340c1001c1080210402403c80c083d0f140d4a07010440441a020342e0007070102c18100c404482d8a42c0c00682d082030041d0072458180c51042c24a0710705602e591b0710410000340400c00007582410681416015200200e0014040c80c0782000c8039900da1800394000014182e0010942c01c0d4032030b03069010031021050b01400e42555944020394204000000b100398414900250f00782e040103803d0341c0c085 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 540591375 1250 540590125 540590159
    0x11040302130e07030b09070f1202060405060d060e04081207021b010c0c0503030d06050306130308070e1305010b1c0203100312020f10020703110312040818030a060902120601 76
    0x1c90014509901401a81c100003481c1d0010309403110200c01e115180c5800b00d0f001c41181c07100460030700105d940c2e8a05450740d02002c600654401e100784020001420300000030210854201c50000b07485840c0d40c00c00e400703204203480544d0002e6010820000707040c01460225000034041c00100002c400c00042c0161903804442c6090401c401400d01d2001c00c0702d80d41140020705402402d5980300c2c3c40201c0b1002c02051588038007880ba00c100408a2008a0400364a540890705941c900007141c0c2c400d207050707a04c20101c2134ad145d0400041180200c20413034601c038042c040d144800c0355698400316040c12460000d4401d00e245a124810000d0000c80c1d14a20140380850358002c000e02e00c6204816001c1c4d080034101c81180b03129000b40422240602995030061005920985030b6181180881601c95035034040c2d4962050070100d5007000ca00820070172400340c60340980c2541c0f640c1c0b488070b03043d001c06d04000f003003c41203403116103c030720f00011031802e03048400c2001e01000007003480350b00d00185020052180 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 540592625 1250 540591375 540591409
    0x40f0201120b1e1215040c05091e19021c06140d0b060303190e090f16080919150609050f0103030e030304091b1e0905010e0f1504080111040302 63
    0x71030f0f020b158070f843c00d000c041d041c081000e0704c07450030f1042d00319140ca840c1241d00310b80b80800030b00302086e03d1904000740c50007032556680c0101c2c9424070140301d510700400585841c0c0800e0105040c150000c00d9400140b03c01c1c003817111503244a0720f024180d8800c1d100395400903184035104c01c501104a0322540500915690000903002d11900d540c07000c42d06600c64280784130031851941c1d01e070060301c582048240c04034038000c2d900584980d50344100c0305070f50503007508e044d44480b00c02c980c150500c0b4429401941c101200c20159024040400036154900725225421240036074584c0340c0000c20b04252281034002c00345050f080c45030340740c034010040180d201404014244520640040321a44080040d140078104030541040b6030540c0c00d182c2501c0800c0440720200141d500c440c02580c40003c1000c810a00d051510f40300c00e0316041000560750904004203054014070201c0c0940d20a50302e1030380d0701825440e4004540d40d1030f8107002d135040c2542c9108103d160f00640c03c000c10001a200c0b521800703044009 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 540593875 1250 540592625 540592669
    0x120305091207020a050603101a070c12050c220b03030406140d150e0406180309150302070c060816090806180c03010c021c0e030d050a1403040f0201120b 67
    0x40c40041c0c60300d00680c004e0383c0c0010007c070401c10903004800c11603055074031043d164050040c0651110015215001d0001c0c00350b03800d080100300c02e03414002103096451003070060701c421019040c0800c1c100300d03194161540c400b001d008503401c240d0062060304956001500610326081c1010006484c401940410b00060500040d168010501c3c9600500c4481410780f000c1c07084940d0b0b020a8180ca0800345c8041e2000b80c5005000c42c840c0c40c5030f1114401903989034540160b054034221310441c0b4a04581181018140c003048550002120305002070b0203080152a42201c03030030486000000c110501c5500400d000d040001404841400180b141d403040c4103400146503884520a0380f4280100351b07800c182c1560803c40c400458a40215203840e50503002107240c42c6a4540801c1201c103c40c5003402540c05400a01081c1007240c4240000c00401d031481c104103102d06151000240721342c0c800c6600360348032503080d0f00e032000315a440341001720300030000f40b024032040c9140b80001e500001031145100314980 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 540595125 1250 540593875 540593887
    0xb0c031003060603150507030b0901030303020903031317070b07030210021303050f0c0f0d020f090903070506040b160801080d03090302070807092012041b0b040b071203050912 77
    0x111030601400303141d00c07a030309000d900e9032460094491210000a2201203040500190a40d0310030b01c11151048402400f015151f441d49d20300740c00a601c42e4428a8043c0400c1003075049440440320408005d11950801000d03d20040c440309007400540d81021036240820418500801e9000502c0041e03200390581c010381e18079030742103034031000201540000c129001d00c190001c14224080ba40d0300a041d026601003429105d03100405c2040341c0c0d101d0b4000d60241c048000c04029080941560340d00111000032031307240c6541c68445c2441e005040310100c03048a011401c04c00c0c614107201402c0b0450310141050320217541044030142c0c0b15200b518800040550319541d0720241031003085402d008010036015503209581b16044d0304080c046000110080c80b891840044800039490101e0b8006c0208005640854075181c0e1041e402c10f494419401c0c28524845010682101d030360020002096001d03c0e4666822151400952100b04040d80300e051500c0c1408218040601107003102020252581503079441e2 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 540596375 1250 540595125 540595141
    0xc07080d360302040c020c01020c0402092407021f1205070c0b071e03090c0806040321020d0606050702010324181113181a0409050a060e0d0e030a0b0c03 67
    0x50b40c8065030060501301c51007540340d008150050307004c200b1790030b8602d1103d00c50240070680c410420103c0e0401d001c0941c81220014002d011038010110b010710b249040c146030000b40c20220030000f080103084006824404042c0c0003002005402189041804240b8043c8005440301c41890310107840300d42c25000141c0400d1050303049144801070414603020a00d00b41e0390080040c422444102c0e00c0707070020b44010900c4400011820f12841e41580d4143c20465001040305403030450903190b402c401d409210038440c0c14610b000c0d90014160035901c4681b18080303800014150f81e8508104021041990b06410381020700041540a0310b0032018464000340094220100401040200c40701d40d6001040107600c0e00c40c2d40440e030084a001041102e15400b009a03007d003116040c1c4801051b0300900100e103040d905058104881e218000c1d004d49003854038584800c000e50b100107801207010b400560141000c1a0041c910001d030000c00d50050000e00c60a55803030b006504050702c06074800078040300080c4d0711 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 540597625 1250 540596375 540596477
    0xc0207051017044d01020102030415110708030108061e043c14010606090608060f01171003021201110708090a05100c060605220b150c07080d 62
    0x15184250b07492050240d039065104200c110741031080134844820681081661050080e2401607030005107404020550303600502c010068456030700048441448607c0208905501171344c0244803c1010b00b01c2840c051505250000b020180d02c0080f90303084041c0008a00844821810504045070070103403000880c7ea500032031a5134800014080444074120420040d00072484c06540c8482e000a000c42e584070401035441031068010040000d51540020702c170b51a00080c0490210301c1814400c6008403030490b004100308045842c000085d107041d0f02001103042c058006048104101d00811010440400d100030922130308101078113455011a0907507543e075030840d02c2c1000f00001070040282121201c00544125903000c005c1d521185000d100040e6414030130280a03960725049150b0383c400f510450310340001c2c610342d01e4140d00007083d0f03501c0d10b1054410000516040744164010184c6a02e0b00b000145404da07025203000810810b14806800104240000d0298009101034403d142032039030000070b04 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 540598875 1250 540597625 540597683
    0x6051201090618091509030207050f01050c1504081314030c01051801030906020f0403050d03150b0714070f23030114010308031810050a0c0801060f1101020d0c020705101704 76
    0x117080d2801b01300c001010307000110801100d400f07603074220381e400c40300006607001e00030158120903d03003110303603000740b08880050b845600500c694a2175050a0600300402d45481103900042d00b01034080008604520341000748500c101e81c246003042c9040c2070750090f42200d0031440041c07418162070b03203034020030826030b0340566241840381059980c80b03e07aa41450f80c1d83c1e240c40040e000120380760110341c14840032314a10000a42d41c0002d2010700e04049940d500107000085107641e4494010701e10040740e0741402514810007400304183d400303844856a90b07511400a001e1000034840d80c50a020403458006902e041411290850f02d078a8503507940c0070107864400007200b0b20902038010810791900c040120b50015000351014241004442008901035414080a000760000b10b4145882055a03600c41c04580e030000740040005824082e0710544ca50599852034900409604040024000e50915145205408216282110420f0b000d03d14028407010b016101a100c0081c038a0481803610002c500405 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 540600125 1250 540598875 540598913
    0x211509030c02180717130308040201120603030513170a03050a18031a070206040b0411040605060d09170301060c060b012606030106050612010e090a0b010605120109061809 75
    0x300c5001d20281c03c184580440d0550003050f0601d5a0904030400400020f01c100c0c1200000d004150503a14141c0b80070900920480c10440024450f8000c00e55074021080110f10a48450791a8207440410600c1c411142d000f03440342c241900e882244032200041c0031107a503a01030400654841d5007030001c0325280328410b9841500c00400300b0001c1008281d0b21041152900c01c1003484039a16808000c070389901d000d881c0070f85007100d00300201d0702050001c0d4541a45450003400007555660320008202c40d500240300789120f140d41c84a40000380610b0580c0700d14050240041c5502c1c560401303c0242c44ca80c150000a050a079444140408590042280816800d0b40414112034074899201e045002078046500c0380c0039500b401000251030400c102540da030b41c18502c00d902030790707800c0450a05070103100a20b10b0070644500152040801c00c1104202d01030f1100b990303041e03582c891455400380c000d03070306900405105142039020022440848402d40750301d0419200821845520300740204c3c4512141ca44034 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 540601375 1250 540600125 540600139
    0x91e04020f030f16050909041b0503150405010b12070e04081c0c030b030d090b0c100e0d1404030803070e0109031403090405060a0f1725211509030c02 66
    0xc080d12140f014548203040314003121a060310521001c490a000b003e212035084440c08001c500028004404201440e2030585861100303543da0000030319001e864040305c141803000d4014401880f0007800f5030041c0d81426200500704407440d41032036580c1c6c4043d101d66500840c1a07c0450304010403e002c07a500c40300b105d09a101015005180ba1000704001c5444401107403130700c50280a1420041195041c648141d2503041d445850325448041550020408021a0151000d03400094102c0d2080b12507400206004203090107003500040c01488051504900061060100b000090035407022607501c4255840d00c64041900e40c801650f1b00680c580000317044290103904401c0c070301400401b60114001c00c440c280525110340c014448a0b0300315004c0e4035a551a100404c0c0040c02244002051800c0c0712011155104080d88901721224040c404009111041c110304115160720810703100e10b07804104d1a4100b40d21040da5400008001d1140d80b612901c0d1030f140d0141c28107001d000c041400c2c9401810301 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 540602625 1250 540601375 540601381
    0xc13020d09080c0609010b0a27180b1311042301062f1e0a0c0f060806010f0c03110703083f01050105132102030d0302091e04020f03 58
    0x110307064120115007849485440001405054140039240031f18401421320003600e402c01c9448940442c084451800d59000350300c81801c0d900440c0f2030396400d4060b84100e580c181149107003606100ba405028501c41c5e2000b00d400c42c001c103000b480c455035190350443c3c0000d0361807268004441e2200f040c2003642c0b00102c806000003003040c3c0100b810600400078000401c040d407520301910b502000341c41c0c00681d040d840600d44514081f01d8088076501c1420b001c084444c041d50943e40e0341034501c0706030494000c00011b04010081507030000d4440d80c102030b09081100300c40d00d58400090000c62200c401030b041183c0c12861176a0316405014150107140c00c84803a5543c1d11050107400840360094000869003001c42605c100c3c0082842c20301e00700d00b4071240320843c081c0d18001c01154503030400500e12641c040340c03001c001045040002c902d140c24188141e8498010064010503040001107030900b4103140c01085a0a8155035000b840d602d0140426040500d450b40720300458028010700c030307054034441e60000038 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 540603875 1250 540602625 540602633
    0x1104030b0705070f080a03050901050115052712010e010612021f0e030d05130b0307020304090507050424080106030b0a061412130506090706090527010b0a1d030c13020d09 75
    0x4668840c9d50020001e21031a66103c043e0000c4a0745a0301d2113001403014000d03088060085944c141d0454402801d4602c1c600710540024215030390140d1142e40f983d5503025100103504e080c0110001081d12000d00b1282c1c1c00c158010400f40b031001c4c60185a01c1010541282c00640160401d80c3c290401500f26081b400100c14003034080d40c031812403240100100341e00000d1102c00f580440c0d200c0c0d122503010f941400e15100c0d08078080c3c880685007a052010500c00407418004519a98200b15241040ca1003400c1c04040050000001070b0080020103043c5050700b0302c541c4070344980300212951403915040003108062000400c1c0554031441c9600c404000c248901c400400782d002c1c0007540103c007a94150345411018a03a144158800d220204007009420046480e0080c210180c41907442044004403a025041d1104210248c00985520380041410011241d001203500c4410750170b4101c4030020188800081da840312900c0c040d500c1402c180440d100116020780640c0c50030030003420b0038440e503051868 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 540605125 1250 540603875 540603881
    0x50105100e0609011202060d0e0d0906120c3504050c0109090c090e270d020708070b04210807080301150302031b09121f1104030b0705070f080a03 64
    0x10507841d0054540d0003041c01840c00c0740c1101e04a9040c10b244d07400290240d0701b807100981241101d1401030380ea0b58800da40902c42485009441e41711940c0d985805802c101c40940300750b0521203001743c06498922009050364000071140000c040da481140c1d03140504c1d8408841d114000104034181001010900c010048002603009050800740c0742c4007600b03078072800d0a50440d100020351100280480d1070810409031a4070344e158220004922070714408041d00214803d550401e001c04206e035108d10503c1d1800703039050240102a02500c80500140d0346010400d2001e030080d030082040f90304841e00c01c6c100c1501c401e203086441c564020b101070703140c0b04030741420341d41070b002407113410314111846d030785034030103504ca03100300c920650b0450648005035130004426121600092121900720000b0400c2050301642000119000400e400f40f9905071883c54020005444004039101032400d030922082c400502c88000069100d001490880d0300d442013400d056112100c0e1007000f82042c2c0c0c0016003c00b0003a4550 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 540606375 1250 540605125 540605129
    0x8091e030915070c150c0212060a050915010306020327010b1305090d030b130e010603120201020304030512062115060a08120c0307050114090f12030a0b040905010510 73
    0x19007004118404030380c1c2c1d510522034510000d01001240d802441500480044007a0010a41c540940c4221007540032803a03c182810a01c0e0b020351100082100541c080d00540e0380c00040d0102602040c800319504421200c4180001451030740c0200020b1000c030011580d0f200501c0310300c80c0300e5100303040d0007d80751300038141700b2202805140d2244404030360801c3ca00581780140c03125001050010b070a130000310000c0c0341e055001c60b84220300c074041e10004580c602500042c1ca1680d4000500300d481c61500e02c00c03000c0d840d42d40c8410340e40103208010100b070704a8103440700181d4030035007010039503902c20008140040a248002914800c000b01d501ca02c100090141d044d42c508002e040d501d51500b0301006010070303440c482c40e11aa03101c016035602c1c50130584003070415400c0352411281048050741c1c0f403600b500d891109643d80100e40000704440c05d01d081007481c0c5803e09800c007410701c11403070050010241c48000c1c0344840a50f140e080d2413000740c41d60f03844a0f00c4140c02c14000c101d1400d000001c00160580c83c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 540607625 1250 540606375 540606379
    0x1106160b0702010c0c1203140c04180515010f0504080a1101020607090510050a0903060f0c080708010e01060807051308010c0e12102a030c031404030c020108091e0309 73
    0x400091009030051080d13070311040881c1c48041014a0507920750502c3c0403044030b004101611140c0c80c8a4022000079850301a13800c007030405440f28100101e840c1a00e000c0714000705102d082c2020b0015071000030180710380d0390000303180c00d100c50052180c05a0785485541d009500c2c6108100d800c205000004180da00540400da0070369901d52500300003190402c8071405069400510044042e0509000c1d400410503074445090200c0f485940b40c40740001c88a0942d0507840303c5071900340900010f94003164603580304d8000d04164640f54100509120241d0f01402154184201130012602c802d0007041521665800b410f810f90009032504207050207001404c0b42500498220b03d03043c05603180c11055039001c502014000e10340059a02d0700980a040c050b051412841d2840304d4182c41907140c40030092a600341031f100030802c550744d100c0c000c007195181078104000f41000018071000035405000b00b546c0c0341e02440d001034292900800c1c00d0400440b440c0361a207070351041210b40d108007000700141400801c1 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 540608875 1250 540607625 540607643
    0x2062a060a06360507090815010503150907150309060203101802180609010309080c0d0813110d02061303150e0718020f070609031701080106050319110616 68
    0x4200702060a207002c1e120400f00080310084901c200e188a5200340e50002662401c49840c556a66549041a030214011080b5200c0c03440148620b0174200140080801040404401c0c0c0c44c0c03000042c1c0d20350185020324070251208040c20340300288207410090b5040d40000c030465580c00c140b4110340c20340490f031240f1007000b10041090b5041002c0c1f482581c3d41c031000300640e2405002c0000402000d6401b0901650505644010b50004554404e014002c3d003013150740185040310b156500902003c0c001003860040281e28014200052501c803440342c150070381594066402041d610005810b80034030f144020035106a01c00c000240319403c1c4407161914441e09007081040d0250030300c0c0b40c803020349004810780c3c134000c09048858481039500504405024030704481c00e042a81d5110403d880c007000013a40001c4000e601c00074002030881170540101008402000716a15180c00f00e6152801c0014004080140355424070a0080007003103010384000c000c0039182d440703400d0013811304842c600013000c1d150800 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 540610125 1250 540608875 540608909
    0xd09020a061b0f230d02281101140d0b04051e010b0c030418020301051804030e0411070209090d11070f03141507050a020d090302062a060a06 62
    0x1014582c481400303040030a550340700c540c0340d4482121402001404441a04103440c90410a0120415860b54903001001504920f0300c030300300003441c00d40501c491039101850644840075140b505c0840340d030015403148408650401e00c40040c0c80c8121010000c07611403100040c1d000c900d002e0b80d1b000c0b0380300f0305049800704140c1d212140340c6254642230640441c0e20100a2006011800c0810040c00500483e0811607150680f9048285900d4502152500703155401100600c15407809100c04840c017460700d201d25603140303020745000704032400003002d07207005540d00d01e40b01c00002e031402c0407607103003680180c65540749090004541d5a076058041c207190001d900c03940590162180441c081c0203c0f0086440a8103141c255100c9140079104800007c2852080c141c02c030217464030103482c09100f00080d44840b41c40d0030202c000a401c02e018414031104000000405000681e01d50081d9601581a0030030003041c032480809000c0a000483e0240b0080e210300002c2014030812600a0f000340c421441092900c01 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 540611375 1250 540610125 540610127
    0x1050301060f0b0a03020705100e0d0801080a0c23040e0a03030e060403050702040b060c0f061602030c030403170903060a020d0605040204182c061005090403140703050f0d09020a06 79
    0xc6040e003d52100300e0410420000454841d4004d0001980680c1c152020748581281107811100345080034180b9401485080d0304658104000b680148409000381c05103000039070f980750b501c2016010355009a4884d0007003031000360450880c2d8003c10700180c010030800c6004d071500350b5520360301d5030101c00180c104840045100d00c02f04901f80569810345620341004c0050342040003414881b001c25400aa09003c038181d41c4200b00420310781084a60b0180450b0b06003010015001e01140023080299402005188000e100001c201d4085a4000584400d50a503100c81f24001d0320030f01100580c0b601c50001480502c19075a0700030400e85103c000200b002036a18001c1c0000d0f40214440c4268254020b00c50382c052041d981c0004840340858804800011a114000b078008070f0080c2003038046a00240c10001c5038401c0f010800040d21045403007240f90b18256a000b8044c00008520b4081c003070700130070a40704060245081d074401c041525000e0f074941c0072002d08203004140401080e40f203400c4610001800d1 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 540612625 1250 540611375 540611399
    0x10080a0c050702010909110706111c0507210f060b03010807140a090b0312030a0b010908010b03190309090603080901120b060f07290402010f0e031c0e040606080105030106 75
    0x1283d4180c44140e5110f2511700d110000300180b03014000030000810920000600a11442c841e00711000c240ca902c8110610045440103a01d60250320407620381400e000c219500410301100c0100c041040303002191105c3e907650064810060302410761410039002150103d2028042c60680f40104215000195107880818040090005864002c1c608900500c600c00041c1c106040d1507001a040381c04490403095030f0341e401d9004071080307000310340d0ba150010074a6070b200010000038040f40009002100b031040c0003a03220151200501c0000c4081ca00d9030341014000d400a83c02046089800c0180a5032400c05400940c482c640860025441c00d001c0c44a003640391240721401d40c40540940c0c00c1c0b0905000007219940301003c151050300c02d00c00800300c6d02c080c21200700015140c4910840160401c0c0c07002600301802d04240d032080c414404140e1115440000d11000c4e400340300e4181260b070600c100300603100c10000c02c80c0380b50020b00b0720f10301040060700224071b24100d030410b500801c00315644003810441 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 540613875 1250 540612625 540612637
    0x150602011b210c0c0c030c050a0512031603020f0609060126120c010906181a010b0d05060a0b070b0f01170703020402030601090509040609022d120c10080a0c05 70
    0x250301d100d850640b003a0425511880340b880090510b0790f46994103480d81c58201c1413580c01202e104694070003d01079400c100c40188001c007000d613200480c2030004121161240209000214403070700d00c59084042c1842040340c449800740100075030b45541000005141c4459090203982c81020000040c81c06216030415800e43c0c035a075501c045d285a011110100c1c1d4154400c10300000507640304c2d110000414001c0c440c8804078000d104101e001100c0320710b40360343ca007481c404110110445602c01002004000800c49103c0080001c001409607940c40000300112407542220721125804502c140030415203040c0305003d4048580c0d0105035030f070ba0750454401403407020002d000c1c2d07420001c4100010300703080c0c0103540c000c0814100050542d80315400318164400469099661326111401c0e2000e6003402c6d00c80340c4038800001040600032102c404491342005d400003107107009606c3e00d203203448028403d020b050314054004100311881c0c810380c0c6004050400a851860b00e051400c3c000384c02c810300407811524 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 540615125 1250 540613875 540613907
    0xc04050607050c040c09081c02030c010c05090f030316080705030d0218010e0a06050f0d06080d051c02090d0b04050c10020106140306010509041b0816261207020301150602011b 77
    0x25648e88144499a5450f1507800c001e81540b00600c030a1300c4405081c00b40e40c4102007150354450f111565407040003128510744001d103003e81c104010404032901005021641a40c100a0261340c1d035015107080392851041a0542d5119031010500003050780c10100b221018220990b581e5401c103031040e0403c2401c1d0864412100490401c00c0018800509003003d0800001240c0f0002559907807110005e007040d4000400c24006007000440ca10b280081c0e1019400f0303032440d05411400c0141190101d0b2003103c241c1002307070a41c4400400a410440108088120b1410141c18200318031101d20700030b0f01802d0b585c0120b269202204210440d0303030400003503a034100e600c014504000760302c1e00c3d150450940c48080011001c0940400b001c9a4240c0403c98100c80c1034082c00b0050845142540310f4040348249512120300301183c100e49815040c0019907240b040e0720340e41d0b101d582d802c902e20009005003000c202c110080c2c5101717500001d10baa010b40c404c112410000024079640c2084541c201c9401401c03d100c04 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 540616375 1250 540615125 540615133
    0xa11010b01051b0a021207050307060f02072105070303031517061f0308040303020709060e04050c1002010b04050f09060c25110603090105090106080a030806090c04050607050c040c0908 81
    0x10000240d10414003c1d03115600107582c0704403910313000b00c0c04000c001d0000a0305139100941c03c100c6414100110f00040003d0f00c2c140851020700c050083d1a01d05a04c1400c1e11101481c4804412007440c0304545038090f440021601c4103940c0c0d00d8040e01410404940d40649444203d0003c0d03608040700c50120300340ca124010f085a581e0721401c1c1e110a8050050600703020910000c04000103c100000300059400f030780080540f14540519242a10f000b50450b20003824220148000200c1c00602c0340184031040fa0b030032259099906080303006164140c4080d500500305010b01c4142c01c102c50140740102804400d40b07080d50f4070200401403510444840440075007000e40c2c0307070b04142b840c0c80f800a605445140d0030340070004114002051a0800d03228014140d54030418030030392a000344a204024035140d0f029185c440303403030345005c2d0445400602d194050100403000544140d005421500a00b4005000301e4030303405181400d50782d440c0c0401409003c2d41c50541d44520181c001c0340780130201c50071f001c024 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 540617625 1250 540616375 540616387
    0x50f011112030a061706093d0e100e01051b120405030904020f0c0114271603080d06091b05071103030d0c02060c032203021c050a11010b0105 62
    0x20003815403000742020f810035950344011840300c1081420080000c041030080c8841e05043c0c190a081510380d2300c00e886009401d1050810050680d03514018042c104002c026481d00100d80c0799019018014810099028400807008100703003d0340905902c02446008020941d01d081d4110004000c18080c261004000d0140041354080c1d07150f040c0e070003031140c0c06032800d001032132000c101640c2015001910746200482d4030f6580c00000d108800c5801c0307096030310100d1801e1507803032691b20b04811040c00c00300c400d05008010301e40300e081080da15070500b41e00e2a40411640c03030a0003102c940041103011100b50411500040107607240c020070403240000a0340c09015101110151482d038030014048841c0440e40f44003030195502030010b0180000318510200c0c4c00840b0740c00c001e003000c0d00181964240102401445101c0307131409010b0382c0f443e0648a845000000a00702613162280e090b244525960840d42356005855010018115902d00c5850388010f203482d0f001c1c21400c1ea6405000207001501c203001c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 540618875 1250 540617625 540617653
    0x803030106080412140301060507050d0305010b09120a0803070903201008040312060305010f0e012703020f030a03060f2102090c0403050114011706090c010c021315050f0111 76
    0x4032410003102c07030170505140e0310314a65102c41500241d00080c00300f0303004106c00d02449401d100000812840d40380401c210340c18061403008501030342c40301c1c07401687ca40f9032881340e00908002e840000c0c0d41055005843e403401060080503140300e0b01044076200003000607541d06845403404280c60881c000c02e140040c20181000f01d84e40300000380b080d030800800ba001c0070903400152240b06e014501441c00441c0d103404400316001551035150303980c210b50b850100b583c403032516029007010301400c0030008125001c03040d050807403a01c400038000e05c102c4d020006a004a09405502010484000e60a042211036403100f10709415048200d40d10014840c403003c1000510300344c1000c41d8401100b80d03800d410540c0f21744955085448000d10615040d41050040c000c5010181965103c1c00c0742d400188442d10384500d0040d1510750042e109418400d51944800440d07444031400d0300c541181364410405002500008d00c0308080030b128940c01400b050444980701c1d40324902700c03068020401e00601400080d128 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 540620125 1250 540618875 540618893
    0x30d0c0903030c170904150302010201150f0b0310030209070f020601120b040615090207080301081b0a030f0f1e0c0e07050912030903030705160f060f0807090305011d0708030301060804 81
    0x7520b5403c44ca002c1003080126503c6104136402600030018416940b400d41c4000ba0868005410610010400c14020403089503030050070001e0b1204061202d403a6198200701005411168000941c4040754004202003294011102c41104100e030307003200c8107666144840320076441600d10103003208000c24002000b00e4140d41151400c1503890490314061555025488100e030050403040700c41c0d0400100402603071604100340e00c00d6603802010000070304019000071726110303003d2000501d0341c1079a44103d41802850849117060540114511302c8040e60705080e0364401c83d920304216440c5d4034058010440104605000c3e10401080d11051f04e4100a2800c1000c601071100381a4003a100c00c01031002a61420300107001c0042c415002850744c0c0017884208000b441850700150441d40307417a00b04010196110252040308640c2e41002c00c60340d2510310007194054083d40002e080d660074203d41c07100c45801e4000ca25504070700181580c4c007860b21003400a45a110031f00c0780c2c0c1c00280d10b0b8000f050100d40503139 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 540621375 1250 540620125 540620153
    0x3070f11150a050a02160906060e0f060a0c2d030f0f0503010911072003120a02030703120b0909061609080a021203071202070906080105190f0905030408030d0c0903030c 74
    0x200403200c603219006c006115160581e00320315a40c03501d586080184580015000e045000100c428400c81d02106002c54024012071903000100500b50092606006940d8803030b0120190300d102c400c0c3c4a9004078500501389420b850220005400302e201590000c2c40740c115441c000450b580d41c107145074a0040703040c000d4403086a4143c0a50020016000040c1002c0f50006810364000d10003090301c440c0400300b40c102900084503680302d039800c00c1120801503004c0b0407918070300d5060402480030100071001d58010103c8190864010308010140441900001003142c4281d070004400080c40302c407050100c82c0c0c9021403150840d141d220071364080041c5440749031308a001e03921100316070030300d07115031900002d83d90020544070258001903802c1c0144482400740700302902e07421000f0311860030035280c2210003240c000400071220340e40d1901e004042c0b0840d0003030482240c000302240d440c0d945822842c1c0d200e9010085d002d00b050f15154120320101d026440c802d00300c98264031042d0000c80c031900da40391214844 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 540622625 1250 540621375 540621377
    0x82224080c09030f0105090f190c031203020c25050607020604150e0a0617100308180301020906040e1f031511070b01080f01050c041215020c03070f11150a050a 70
    0x80344c0101c01e9440c0034861144100010001010255055040c060400c14903050741c6e91004004500300e400310b1003941002003142d0b030005401e640e989103488220000d0096150682c02c07270003600c42c4c005403001034901c4080011030300d940100c01d0542d5034081084c82d00c6000c40003500010148410440550100003040402c00c0a040c4000008600c00000303070041124ac20610101300070300340003907180761f8451a1941c001102c85140d1211f03030464a03203d0b40c901411101c584814023072203824146032001c1d0181c0741d2940e00941640c0e125502c40c582000c0c8620b00300d400d050004181c7c5ca00b0104501a00062403c40344c01950600d40e1122485030b810117008152040c090005080242c1030004402004903402060444041c24440b280304045070f0945501403c0610204024007081c01809501ca20460b6056481800c10600d1030388580c81901038000e5843e51501400003040401c10b010700c0d0364850702c115201e03034004000548100c01708070741803120814820003540184103500429016200600c924205 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 540623875 1250 540622625 540622633
    0x3150f18060b0d0602130602010b030d0806041505030d110c0d030813062a03180c05060c1218011206181a030607020c100c0f080304082224080c0903 65
    0x654481c4000d913070282d0148840c40003000c8040047e640d080c401d00781d144904030041d210580e01c120b001498508041c2a4a1185940d543e00c298a2044d6070b5110009103030150680303820f5681464050890f07002d094020713455001e2031942505c24580142114220b6030725494520041e2141c9000700448512030b00b044424903601c0c1940c144c28030b200c030284c071603030000035012501c00c03080d41000409a84010040c8203842d1301d83e040d800c00199008840b40251401030300c0e555110940b9030b039002d03d00600070300701d00040040022210140010178114600798407007a203801d482d059200480750121503180c4074040c00507910740c60440c0d06200f260000d640c1d128001002d103d00c0b40041000900b400c0d01540c205008da404003d00c5201410541116900041c403400c03c6901d102c16034503110354900c060340009102600001c0054100f040180a41d094502a6081c08650107d41046907031510101e004005a0503032000043c1000b2075912188000381010369203425560712540c9502c0a04d800c0345540c2507160003 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 540625125 1250 540623875 540623899
    0xd05040b0a14070822120209040201030203130602030a0603020a050315150d0203151b0a09050402090103180803011d071b050c04230105010203070f030c02010309080403150f18060b 79
    0x51514050005442d034040004c0426244a418030324080b043d51041b0f40000c0388000e42d20160b40d0380c50603141c5c00307034080c00c0150340ca07038602d80d20359842d00300c1440062919201000f4004403c02c19404002601c0c42661b660364240c1d101c108059440d45101501c00c45240300500060400c5004100896010390140c410501d03081e640d4000b9003007000203c00b54042112200401c076121400400c0404410781c8407406518028410700c00904054203070180c1c43c0a2038000035680102e9210346d01c503907890720040d261034440c85001c0c5065260b42d40207209800c100d4602e81c180201c40d621119071140202126107992007464040c07200320301c089905200a45a0340544400d66010b52513a004201500c2110f01c0d1039866021071800c0041d040e403060700300e45d0440d8828081c1d03030001b580c000d1013071801035010704041c04e01110501c0100e024209100f40149080c102140000030401c100c0b204049070950560140250104111800122000448000e400c804040c00400c08209164400c00c040c44001e001000041 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 540626375 1250 540625125 540625133
    0x1c02060f0c0d030510050612040c0e0403050c0c06030105180709350a1e0c1d04020f010305041707050102040806011d0f040f061a090709080d05040b0a1407 68
    0x140281c4800103507a0090b011280e00d480d81807240c030b80e000c4084850f11014508010110b500703401000001100c00d80c0c11008181803203040c03d8028000c04000301450703030601d010b2078001c2c52500f2400c1055002d206103000c03007141c1c1c84d040080c0ca05941c009071080c00c00c420014240724003d03c000d401c03c414031900503008540f40c107510742c6400315510328040c006100c5e0815400f4946c400c500c2d8203030f401ca603007056a140300020b1102201100e6029994031a94861030742d4184a951a8407a80c02030300700011281031021a000d2949107140b250303000b201c3d00e405404901c0c0041d0260b8034216402131412515802e41c05015015101400e09540240001414952100e611502e810404c3e00460106c1260000c101c500108490711550300005442000710282001e5a40c462000e0400900901a94507003600010070014444080100076000f8234450080c2041107024048000901407042e96018111030781c900300c0d004038111303030071603581c070381258034010740c1e10000c85180b01e40c8814500c1c180e4040002c0400700f = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 540627625 1250 540626375 540626377
    0xc0c0a0f1e1410030213091a031605010309020112020703020c09090105070f1b0b0c0403050d02031e07020616030c020a09201605060106030203071d0607030c05011509090c0608061c02060f 82
    0xd40342026000942c48005804626201408035046109e640240d40314800c0d10b0840c014001191001c0c24080380354032181c40141c544803036100b800c0316003034404241201403650020390720915000c01c4d07420030480d803103c410f45404d8038030882c0c443c0c3c00f0800d070b0b280e411091031040301040d9400190001d9418030400c0b1b40e131081c1e0400b40989100454035008641401400018041a0344a10007030004504e454101e0340070b150000c08441401038a4007001c80c00d1015511000d00b160300e04010060344030b07051040c0f0718000e00840f460800a138018580c5040200300b00310988511b103014411210450261f1101d0b00c00307e409684241c1c0d0f07030b080140140b08140005541040410701803c256240941c49103008034000b40341c01807103182c41451050b800140501d13074444004964076190149000441d2a0b5103003031850252200403a460064400000002084001035001e02416485044a8600541d562004803078820058030ba1541c800b800c01040303510003550b1112444040e1014081509084002003c8052 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 540628875 1250 540627625 540627629
    0xd022206060c050c030c09070f09030b0702061506090a050603040206070503072102010506090408030a060b0a020d03180308010b03040c18050703050702070803040b0c0c0a0f1e1410030213 82
    0x42003004481204109003441300c01308640094008140b01c03031442c030000f007141501800c15424041070307000c0085042d2048003881c000d1900880d034000c5508204500135620310040350103040c0341034452450f1500c7d141600844221740002003107500d4581c00c180800c001a030028004a9010741e003002000c00140e024409888002c4c051403074040300c130100b0254a90804c2d5000107003802c59150130100b0074183c0d20162519005908480d40e5920303685c643c11800024a1142c2124200d080d020442404252b4002450000d001d16607030203100d000c40300f41c450303150b480302030720000c01240000300140800103c09001c0e40d8080e015100320207100e070741c3c0d07000394203c1c800381c42e405d40703100f03448000700014140c150180300e410504500c01421020700c3c3c2070246880c0d000710b000c0c0c090007800000b5080c3c00c1d00d008205540e84a10b0051580018a641ea103000ca0454042e20400790b0f201045643c5d01071010910001008030350b6514500e1251816900c03c1064070006100c0c00f00515900303200510041300d444020700c3c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 540630125 1250 540628875 540628877
    0x30c030e07060801030b0109090b01030605040f05072d1412071d04230a02090a0605060c0106090c051305090a020f07050703170a0509040c020f0f030d06140d02220606 73
    0x40554103505001c102a64148c00141230242000003402c00038003243c0c0c1e0141101e4010b80700083e50703169490000d60f040341c0524080c1241c0304041c00454078004034040205000d9003400c007c000c0714142e0645031152800d52080c4803001440c01c03404012410f0000c000d1312074032400d400362180700b40c542e221111030b03103c60000b4011024507102000100844220142c241000c09419644421403820110b0b61391038000100a000e8000300c408291040b809070081c1c0080e0900074003da40310100450128002c01c11071141980a6007804002884540a0390890780a1610300418501b90741c180814086c0021001d03224a4015608115400d44000d410000c0c1c89001e11a82c0503003481c0d459424031001c40e1460018090446800f044540c0348280c002044031110b0307030140c42c00b2600800c010710680c10070b04402110b80f02c90140c8039150b00a14000700080031041200b9000f00807240d00e580d58000d40200300b603a650b401030491489000540703452080e04611000c4a20000549004035031904180d86459100c04 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 540631375 1250 540630125 540630137
    0x70b070c0e010807091413030e1c05100506040c08073c0305011a070209040804030b090601031704030c06030f09080c0d140f09100210020310030b0610050a030c030e0706 74
    0x80145c0b00b0a01503003c400d0300d01091090369091402e0003079100110350380300034107001071200700075102c0d00d410900801c108c0e8010803000c07484085052803601c8444030310100465034903003030005002c1c2c5000d100380700f880b660558441181c1d588a0100750b9245803868005400001030780c40c01080b46288030411681c05075002d00004904150410103001d0761b030103802001010446c1a15210321104071002d45040c250111400751807034a4030300341450648603640000d40340702c0e00842006203011001900b41c1c1203d110f5940420190b030345011418481c0140c2c08000c3c02c8030b0301d00303000b00f107007601c03a40042c20b080300355941c005150416503031801100d40c49045001d10603040740b541596600c0e0007411100e285008040700d03a03d810b1121841e07904910a81c011144103505107100414814820403901c408524510320071581c0703051603410b00d405d0070b1480c40200d8091000e0740015400e41008180200395000b651180741c24080502803c0d0060248900014100f40d640c54500c20556401c01000c002010991540 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 540632625 1250 540631375 540631379
    0x1180f062009010507060e2e09020303070204050919150627020c0a17040509010602010e06011517010f06020c100906051b0a0b0a1a03070b070c0e010807 67
    0x110107840c100380703078071010740c0440081c2507940d2120012078144040034a030496a4000a01e031007001400521040200c520500306074035031a401e401d080540d100d9802e12105500e00e40400070905031141d002009405400030700150005003400d410540d041480d140c00e4035414201c900d480140c1800f40d11040d41c103e10103000c501601d59a07407240f040a0140030003108a103040151016400091000003c0c00e5964005400c0304030010078001c000c101c03070f0310880c030040d01d03407540d0380c0345c141c83e0403a014052048180c10000281d250052040c0c854034070015000e040c1036032070078840c0c4c0600345031120308805014a40511800c4c6944085096001c3c1c043c0208050000c0d04102e8020301d001303c603c00345030040f20103000764182250080584ca0880740c0c2c07880c042d03541d4490001484034803101800018800c2c0f0982180c1e00c10801182003031031098480c21000c00885442c070010314071104c0ca0b059682d4064100a0341800028a02030050030718600a51540d50403c2e80c41a4118102c10f09a110a1071600320503c1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 540633875 1250 540632625 540632633
    0x41806020a1e030c0503040212120c01090b010b07030e0f0301110a02010203010e0c0a020a1e0614091612060209061204030c17040b0306010c060b0406180b031b010c0501180f 76
    0x1204542c24207450100310001d80c1c00405003141c0b0010f00003a10401d412181c9908128080051000c2c9030200a251611025960003043c060a030701d903003c8071034600c010008540294418140c13509150183c3c2c444884800a81c01d000b0601040b10a031501952184041880502c6100090101c400d040e03000507038962500032400906640076100f181404d404020780ca0150b07900084420710315401c06072125030143d00e1003184c070040114031802480d080c10302d80a018005605501c031172043c04c41e0825914216a075000711120300b82a8010000400d45c6c0ca045040072444550140040340780241c902450300100303403501112041d040710100c0024018280b00d4040083d100402011600f8080b465401c0c0780c10611003030032501004102604024044100710700b0300045400650141c18058010480117480340445461250401d1072000c807242802c55842c2581000904000c6000004421801d4001c05c240111800720b20030340b0a84880d903c40011508080e5480042805a840340c0f0b44116050540e00e8 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 540635125 1250 540633875 540633917
    0x60b13050402040312050d140c0309010b090103120e040b1201020c120a170903160c051c0f0b0c0c16051503090705150f0408060414030f0405041806020a 67
    0x30900070360041c001000041e025084d401d0842c0601c0c102291541c00403080764009004641c10412203d03250750074441c2d81020f50340114040c1d19080020300030b0300100c0d01030108105c42880020500c0e6211488a91114418405000c8021008101294440e03000c0c0004442155481a280740b5950024031418581400c12850005105c038020303103410140061800380c41e03800d02c0300b030412071228080005051248280100c0794030008030450849009424107014100d105a8040c3c5402038800001c40340070030742000408000b4550002d00d9891315502d03665034440011000d001d20141c1c0d20140b1407101000c00a11003240e00791481128200e00524100400c1090480d800c28150449000c100784841110049a003800361003003900d0075001e400c01c41c2000040c5225401390b4035644023021801055187c000302c0d007140180c1c0603100ca00284070425800584a224000d0107501d040700030013041180d4145900001d400320425010120800441c1c1c56500503030f405540000d000070355007030031801e06e071034165 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 540636375 1250 540635125 540635129
    0x3a080117190c320907090527070918020a0c02061b150c0d090314070302161a041e090204140a080607020a0b06040e07060c0c061b11030f01060b13 64
    0x4861035400484901c001903c40f546030031a103009090b0304c80001c078018002d031801380050001410a88410205054400d82c605100020f410040304090120b4000c0d4070851222003038800c03d4003592642403801c40144001c1d8880b100500600c400c900c000b001590f00c000c094040b40d011071141810341c2d2014000f29081018008040c0301c030204c0f240a11a48046ca0001d41e0386c41921294001107400481c1004e6500d21144084030700ca00d003000a4550406502280d92411050701c0744224003015151400c1407903840503045090be484000740030801007916460203405045c1c003c01a808441b980700d20291040ea0b006400c15002c1d0300f214040c409003401e201c00040d00500300d01001c0c010505008000944034074480700045c1809031540c0c0030a0300c075911070340030b030003892003610440d034145649205c081c00c144141c91098801194034100081e003240180c4052410310b061030420440300003296904028012003021454145c45410b40740c0d007904100344110390241108100141d02d607046e03000140a840f10507 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 540637625 1250 540636375 540636419
    0x40f05040c050f030603100609090506130201050a08100e07080f1b090d060e070603060608130c12032003090a050301140a020702123a080117190c 64
    0x111890503101035000b025200744403415400c140ea2502d669000a1510003054544102c0c14074280000610307940c140e0000c100c0303034480c0c2c041c0d54035903980354034041c050303011082e010f804544100400c80845124001c001e50044160244050700b07510342105210002c0100d03090004151030a0034800b22504000b03071140e0015840318621150106041a51002d000701d1518030300421a090219003000040e8014090010212049070310080d0b45000043c040c0842e0312400002c5200e0388085a2214054088400010b070407500f410301c8145000b00d180501200200240c0030005c0d00c0e00c045188011070411602c00390a24001503840315800c2c0100901ea40240d40701610a0707162880d540c007045c50041c4120361006244000507100c04841c00803c1495005030402049401410b2990200c0300c0007290362100280e503481c204c2c0c4000c0740c0c0c0410324003180404c040340000c00c401d00c004100180d1110042070304e00a50205444030001c000c2c0003040c100d00100320850f1510741000090110220b02c400307501e242210 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 540638875 1250 540637625 540637631
    0x3050903090114090604050d080307080f04170d0b09070c0309050303040303080109050c0c03070507090f020405090a11090d0f0620070305070305070b0109050a0f0501080d0e1c08040f0504 82
    0x8801c002810a01c640903007000f0190700030036200455580c01c82030350014800a040000200c040b840c0014540d401203039a0030202e00060045141d000c000b440e01886143c0c030800c020f00308132444400121542108078a0042d59132a001000b0198a0b1000114000c21064440b004040354fd0b00c0c003e402c2038405c0d0440c80c000d0f03005205c1000400d900c0030700c050442c0c003418030010b03554a894103400c0c001e02c40c1150a40c140c0c440000e140042041c00540c1c042200c116810410407907a010750740c0d0060344124030a281e8444415004100e0b000030940c070081c82e04140e0340c00303149041144001304070a002842d00640d28010030340030140620016001d02c5c18030000050741c0003014000c1100b0304906018080c0301604102d4003182c0710042600500880c1c05054102034002802c2d80d441018601400c02168001130060174079002503240b4065000b0703641a20540f40203408040b6041c0d00480d071000014001d10382c850050311a80c043c0e512b203103071608403890049a165540b00e0805507807410a940d194011409145 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 540640125 1250 540638875 540638887
    0x228080603150c040302030303180610030b07080601120e1e0307020307060f12060f030618020f15090d03051b07050604030206071b2d0b12220b060103050903 69
    0x41d02151030031801021070000c1c04203486100c200c00c60f9000d103400c001c1d0948000418000c0e1012414200c000f4509000e007164440e80c2c4000c240c80c9130080d079100007800141e504011406290281c0140755200c0d4061402c150300342141c0ca0f1407019200ca83c001c2040980010280240d0203076100c2c00c10101c1c0078940021407400c0001d5001c03c0c0d0320b4034a8890241046100201007059a1043d074015015880740c107030074442245c49100c80c440e0140544802c96100c0e24040340745020040c0e2007410324001d07400030102c0d40d06031449000d210f41c100102c0744035412340008010400390390b900d650703101c100d2a000359519500d0722285a020000c03801c1c0c035100208594842c0b035040146603582801c4805803981030320040d44800e40c80c5054a02c6196007986d000d400b03501840046003849800f08036840c01c40300303410007503000252a03101c28405801405101c11043d01085031602d0541c41c000010f0300002c010000b80d160124181c0d00080b51940c0b060211005640300d01805020360303050003420f40100148d0051841d040c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 540641375 1250 540640125 540640129
    0xc05040b060c03040902031314010b120f1b01090f030525030b071202090301051503011a090105041805030711040f0b220608240709030f080706090602280806 69
    0x80100d05c0b407010b46940000008040d0f011400344c02003050303805803108040d00040e88405010f040c02e203442c9809040b0400302d018035800d0000701e5061951041c0050186208212044002c2c2d4034202919030512200350700028010300b10300319003001107015501801800c03100c010071001e400c06420f81c0c00c004002c03503d030900108040c52989034025480e42083c1c0a503010703011000c0089d009080407144e040d4a010108601d40a00c1c440119842c0300c03c4000708030704192604220b00c0e1304240020750341c10264000040c89541420340c4a10540200707013089400c550b0640c0e681502d954086401100e841820540c0350b28141400c0c000d0712003509000f03c081c0800e4000d88040b501d100c81802004120f060998440310001d0540d13400480540120404c1d40c841040000703a04000308504800500e0780542c000018070032500c512880c2c03042e40c0e1b00014941e090085a202e0551681000500b5101c1c00d50b101004000609148014421505603401310100542d2021041c2001040d4020200604c141901000381030307 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 540642625 1250 540641375 540641377
    0x1502010e0304141807170702010c020d0c020607120906030c0c030f0305041a0903092b0206030c0f040f0306050f0c030a090c150203030405330c0c0106030c05040b060c03 74
    0x140300300400c55500350307a010002484c0840c01d00f002040e44420641800340641d80b200358101c4003560100e10081d66100c0890803402c88010380381c2240142c100c01e1990700658400d803c481e00b014002490203080401c240c540089141c000031a002c04103d10100030080140c060003011041c08590410000400c49600c010b400908440000350800d9580d03000202000915205607000c2c03c5882500e004034a450a0307040d0b034076400074013064441c2035030261400074030311103680c4d01c0820655080c081d020b040d5982c0c28480e15401c0075082e50a070308403c1c080d074400b2103015005080106440304204c0e4180303242d41481c1c41103880107020309031071103409001c0244421103001240e4015480d410001a010f803907042090081007541c1085000059540184035401c3c1e00101844c0200c2c010341c2507030b0082e0b205216009200140203846850084132042c036000600280f800d4941c408010104d05c0d20305200310080c5801c41d081504102c0f514040c0000078441c074101441042d903a2241682e4051412100c0d0f8900c3d50340e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 540643875 1250 540642625 540642629
    0x209090105071b15060b041404022503022104030c1d061504080102130915061d012703110604140427470414030408071502010e0304 58
    0x907216100c1490f07410401e126880c0c0e04c0e90703041d0000c1000a140c8071005445650b110b40305046044460044506192416100300c81c461090144007084c640710540b05924000041b450580030741c003c415801007900b10220f00d0481e2074040b194074035940c4d41140fa02c40c0312103120780c10545c0e980d4212600151401f4400b40240d030050000c8134501c51881d034014400d241342c4900d07000001f0550000c118624400100603080b000da0784001000e10404042945002e220381c072502c42c40c4000b4a01041e078044460700c0c0701c540100154103241111250028011464201350144070103807241810030020410303c400c0f208455403110049a010f0300c0d05242c40008180c1c040c7d083e200501c01c99580c1e00030194036000c0c150048904125802c20241c034034140c104060005c1001e04201c20001c06410221000c0717200921a01c004608000040c925842c2940040c032000d10080080350201312900701020400001c102400040000c8001060340380e04141402c11040e001c1d030003600541e0b050005408d40c9681c04001d03102 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 540645125 1250 540643875 540643907
    0xc04080d0806060d0c030f140709090504020303040302060c0307050115050d06052509060f03090305030a1d01180c0b09031e10020d05060301051510110c1c020909010507 74
    0xe10b625100c00250862240000100000d450000341000b400d401da0440005000061400c001c0707540c0d01c914101180f00111991800130328061303000d00c0090303c0d580c441904180060110ba003400d071641d01150840c1d1040001e06916807021910b0020041700340158440e1a0b880394103a109075203044c000c03c982c84401d1000405076500c2d100086c00000f10300410800ca41c4421040d07000da110346c00d802074000c100c6404dc04c0009620030110914080c002e0140688160b410740d80c2610b103a865910100080c007546600b41a5192142a6442887c409001e1100d4038068030f000f14801407060710b0115001203c03030b4041d209200d400d214640ea07a9030045a07d80303402110607440f01d50300154140361402d00c1034000202002030700c00300b00880d00b0700c0700364441071046406900800441d01e0703d8880030810980d00c0e490580c040c079550442c02040b44180c2e141c9145c140c0e41030884003610704ea0400182c040c54202c44015418000e03510480c00d61138200d456603001300721340008101905012070f00800c0c101c02584016 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 540646375 1250 540645125 540645137
    0x90a020319020303091005120108011b120902131b02120904090203070b040b2a1c0e040203240d200f041a04060801021602150705190b0c04080d 63
    0x1005544040c0300701c1700c42070001801003040102d0848064107942140c5110070741032020f5030011071001c1052159a0405482105c03140d140e1802900c1100c14a03407207002240ca10740c6a0145a0058840103d07218018a10702c90200b24404c50380c52900307250303500030b00c044210750103103090080c3c0d500d007402121079101080d20082049240c50001c82d20307044d1583e20031032030102d0004000a20100b2000600a0b041401c819174041681090002c15104810410000244c018140f000c09100052481005452250a00135100022140094102e80044880c00da81c0004108004108460340010303105820040302e03c103854840e41c3d11540954100000c01c4644030120160420050b03031005002108540001e106020280c10712700c1489001e6540c0d100140640e040c00310118000c1c0d818004e80d4240b0018a04920002105408200402080e203039190440c620410a01000c240705001c2e5039003940d83c1d5060100200d07180d28004140300f00040400322409003c6c04280302080000c140e2414600b0545088 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 540647482 1107 540646375 540646423
    0x60b040c0f0509131b030603120302070c18061a0c012a0e0d060e15010f030804060507150e07030c120b0118020f071a090a0203 56
    0x207070300441c038184483c0001d400c0c09200ba503c82d039050280440d040c054006000c20754000300311004000b90f03c894042c401d124840c03505081c5003245107011450700802c3c0e204e600440c0441e0260642107042a05074055a160540110024110b0813602c1d118040c601101c00c0920360011120301c1c0d03c0e50903c0d1260342190b066440e580c0c0e540c0401c5c0c00c15041030100703403002c5408502c1c00a1040d0710240703410300301d00402e8091082164842380480149004403107135903054101a03050380500701c90400000d083c000145040165805c40c3c0240c18a01d4888019140c650001c480c1c401155101d00c0c50503004130b1a500c8001500307000c90f40a0130365003c1c0e481d162040d9840402005802070403042003800100000380f030300c28407021006000302e001410540000307161889540f007010203039014100f0205564582da00d00852a4101c1d070564020a4540401c1d40802c2d156600c03500c690b040032040c0121 = true := by decide +kernel

theorem cover : BRFrame.Cov 540467625 540647482 := by
  have h0 := BRFrame.cov_init 540467625
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 540467625 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 540467625 ≤ n) (h2 : n < 540647482) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
