-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4249
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:00:33.828305+00:00
-- url     : https://prove2.me/submissions/f217f875-cb0d-4344-9af3-059f7af44737

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 764028776 ≤ n < 764208633 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 764030026 1250 764028776 764028781
    0x1b0610050907032c0d110607140f07060f05010e0411130b1c050708060106050d0507030e010e0a02100905060d02030703060f0e10060c050d0f1101290102010507080c0703120203 77
    0x60400035078004c50b88014510841000d85045446119030414041210000c4c00c03403520340702c0f8200d8800034122603074141c0c900c080c0544000050300b60001c1554901c188000254952009a101d05035901603000314440340707544081001244000f4004402541c044a10b00b8003400901c41103001080c4500155030004004900c00240481c0854606010350003041140c024598030031201e43c0d00e45090056500152050000b10364030f02a507003245410a00030f040c089180201c41441c6421206110100012503024070210740035410603000c940c0c900781032890300d0a0198101000302c0d0f00d91065000c0f440d10741e9070020018880c544a50b01c40c1000e0302c664521085503e554080d18401c007007080e80c101015031a01c4034001802030003000c1c200180e5031321001400e01119074001c140c601500002c90f04080c019190b043c08142c540078411800811050300c1029415000034242250074002d0301041410b5a141006002c2c5198100c511154000c64542c00d090741c402d014901190701d0b00007042a01c891900100a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 764031276 1250 764030026 764030081
    0x1b010f06030807020415061d042913020f09010c0c0302030a1407060201090c0519030213020406020c0402033309010e0a0513260c030406051b061005090703 68
    0x34014580201c0b000d00244214020b130340e40906c43c62003200081004c441400d8182d12440c400f094940760000c06c0052012621402402e00112140743c1290b040b9046041403c1441c14460032030141714010011814108071032141103840c0300b80c03142c03603052009036000141003110402403400170f15805015102910365501e049201c0c109000d1140c55a4044c101012451030b1051084081e00c03500a0a0140c0144c6440c0a01c00b0715850a00641c001e403248174004000342c0c03284e040015011907040d000581e160326210000f4182400b40505510a43c010030500005071051400180508000c1e00210050f074105a41c0c04ca0440350390307001c5170b00700d40d0f1032000090000000300b2a62084190b420b040c007a540d42d18005040d020100403005003013200740e40304041e26920101c90400d00803404030380c6a283ca0507000d5031910f550059400364001800000b034403500f002403c0080c042c07c08820f40240703243d00f01142c5020240a090003414014040c3c06c00042c1c0040c440d41011029440d000311074035644074000e4 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 764032526 1250 764031276 764031293
    0x1104030f020907020d02030405151b03270a030b060112090b07030c0e030a2a080c0414010e011a090607121116090b180f01030b01140102031b010f0603 66
    0x390903481240c03000000758019001280e0100018005d50186152908040c200b00b00748201d00071921102c1424040b10b1000444210302d941505d901e100203513201c00c1ca4071001003104021120385a071580744880c15803401c0d02d604110304181d9501020300509903940c600100e0f4400c0542007940507081c1400c0e001801d01904c0c0112034012400340c1c0e411300c4050034080701513802c004c44800d42c9805510052010020910706107620300244540050b43e55102500002000c15501d6504005038980044040038024a801d1296602c1002c0702c0151141c598504210010301032814450940000c0e500100d85005410380e200301d9004180c0200120f80b102da07903082000c0740780c018074140e202203060409075102102001691705144242a5180f20b03505061103081d4002d050b003c2109a0441d903e001c034241410030703000485104404c6001d0401e603561640c28061081281030340031591208c1044031000300703a40d0201c2229403031505d0304244085400404205c0b401014900700030455107140c035001208000c03451 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 764033776 1250 764032526 764032553
    0x901050f1b07090e062a0d050a0c081006050a0e2e0e032a030f030d050105010f0903060504030e0907030b030f030909220b1821030613110403 62
    0x18402c4a08964640e0b140e1003c840c01c10680c01c44e20b9000000040080740c030200059034507801c030b80341011400c46208084080c1d40001140d5043c8035120b10030480018401c0c40b992600314510315000059040140c203905800c0b4503030184808000d03000030030000c19805454a0200448042e000c221011a50607690300142e00b41007095154085540585461034413551068008a0300140a0001030f140d081d220240250b281c11403414007554287e460820756014080780112003c110040c0d030340d03440c081c890081180c005812441c10300c6098000e41484950208020781520781c0050001141c1c2c80e540ac0a44080000306100340e8800300100400c40c10680c150001000501c0903000c072a02540c802c1d480c3c075101d0007070001d035503040030301d40001130090315460301424500c100c0e410031070f0805c07900394036010040d1390f013126035034049413008c0d030035107803030380041180c1d0100704900c69022110007001031020b4014400608854484c1100c070362050f49d0040541e00824032038080b000d10b16511507492404400a0150 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 764035026 1250 764033776 764033827
    0x4080607030209130605010519031407030e0d090f0905090f0a05010e1b060a03090213020a08060109080f07062007150e0d0c091a040c120c02010e120901050f 69
    0xc10100c0b854103071320300500083e110161181403c03c100f4079440101007015000040806d5156090314900b6035a00d450580504a40d50f800b01d401c941440500f0b02d001c508900440402010140c100103418580107800142c88414501003a0360301d80c02c104a00e081051403400d2024012136000008208056020456040c81e0310182c5030f6407500d81c1040b01c0b0200040a45e075030410001c001c00901c3d00d100c1d500c8180107500c010114503441c000601500100d8201c0800c0348007191840080c0039940d030304010094010300e40200240f940000c0406426111540c074409e04040c13105003140003812007841c02d1fa0f0940004918103e07a2000e0342e800840301c9100000740803001048000d155040c180c2441644071508136002841c5030441c07072406000d24010012282d241040070340620b00034005699034043c1e0544490543d40d450321038401800c0c1007080f54100b81824095a1412400c00c00c0e50f240816202800000799948540300d9801e40c0050342c0c507100e40344450804c01400600d451400340340100551030400c4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 764036276 1250 764035026 764035039
    0xb0d05340e010903020d020f0303040f030609030935030f120a060503010e07060c061d101103090d0e0a0305030a020d1103040e010e180615121506010c0804080607030209 74
    0x304403005481d003c0740382c00041e4018694070018005401d100c101002e013107038094126841c065403002c242c600d02a8a030030454281d03444001040074103a10520a4028148030703521510082e803a1203499040c12139402102c15a02141101484601c6003030044d281c2c040c00504180b9903446203107505d455100800c60b02814040d00e08074000c035040c181441440404020800100051810441d054035180d200c01c20407102d091b01da182c0040e0454100d01524100c034850402410113014810310441554502e042c05d030203400b01441009508040000c0407501c811136130401e0000388420602085808586030800303041403100044007031604c0e9000a408003107100a599581e01c0607c6548820b4032807180c2d200c2c078200d90044c4001448605d0248818642007030b60030080c2d0001003500c1d00c20a0406804440f0a00392010243e108042401c20002c10485184420060a039814410412038400d080141c0744504000180300b504007042080741c1150080c02e4580e08941081c6006880100a0742c413481c1582e000e0b0b803 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 764037526 1250 764036276 764036297
    0x603070908071e062001060f05031b0f010c020411030106020f0d050a08010501050d02070204050a020d2406110a140327090604020f070b0103080301090b0306010b0d0534 74
    0xd0f12080d1041840394070000c994a4140350800865089182d60b0001e40d2240f0081035454245000341300317280c01003104100c232541c02840c0401305420004091100d4076031040000840416503902e034200344419009080040b540302d5a400031400916a04200c00c40d800c10010010585680001d40d801c02582e000f000c8485000031002e048401b801441c0e00781c0c01280803140184440e6010740d000d00007020f2091001410080d083d000101950402d0b1803401c2d83c0c80c2d0014281d580b0341c5490007940020000030403e52075903e401194409094250700c11401003102880780b034040c0210038807000c0599504490b040041c2c00f419071495490f60b010381242004802d854041d414540f07040104040190001400100d8950b02c0009001c040c0d48055103907201000100850700001e0f4020044501941c06034105035101c1d0306018044c001c80c2d000d0615076111b0b44c401001003150121010480700e0300b941d10b0340049007540720441c0411858152900c071012070b01c0c898040e4100f01c0344038407102d03880307460a9441050f1031 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 764038776 1250 764037526 764037539
    0x307080726070503070b04021f170907060203070b071e02240618040819082a04060309020d140d030b010305090a17130807090b060f03011211060307090807 68
    0x14420b209000b00750750030500c0710002081b070320a800b81d0710600180c40d0807820914268104191049441900c0c089001031150040e40178030300f11016448103172840100051414004003035a02e0003025070081c030582c107500004003010f00c00c00b2044880c8114074001d00b400d015900300079441d0b00c01485406030400042d44c1d1501002e40c100d14450023204050310126a85411010406440c003000f441922000000c111080769030140040315100310485590300c0100d1304011000105501110120481e0b8501c03210300352280c030964508071030441d03149042c0003c01220174800308061864201014246031407a00d102991440d021440c0744807d14699420800181020300550443c0c40c2500c100d482d6601000d000000203d24a80909400d481840c603036082c001d41030081e8824040903000b50a56410400c002c014048890242c004d41c80350440b8a54104004903040c0c00c41400144079003000d04500b1041d88080c07111844260980b843e003d8045035591a00c40f40c050040c0045101c0c00740da500c150348000485 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 764040026 1250 764038776 764038853
    0x60603030a0c2015030415091e11100c1421070c092c01050903030a0908090406120c060201020c06070c031125050d05060f06011803030c060c0206190e03070807 70
    0xd154001000c449145019161081d0581c940074105c0786060a401b5000ad00e030350710007181321041c1007581d07204804c80843c0b03032580540019082e0404a948801006002060700030355003800c18000347d02d045d85074155410225403003440c40c0c0c0203110342441c1107080204440d1500402d03480e00c01980c0c20703040d000341d010020b608031007088840d01500c0e04148003113416000260001040e180c050340440303050102d0840050216000703036200180c0e0784503500501d010821228038000003007000c0e0000310304001800c401242c80c0e0702c00a04110070802c100480004044c0031301c01d01c0707002003c10000c541000c20840344015a41400c0e602070508401100e60025103403402d88940798100c0d03400800b8040342d80700c000000c020180f000c2c0415051000d03000c05001e202000c2500c14008500076030703030305048071703080d040c503000f202d5034401c0103411504190100041d00368006640e00da005c15100c000202c07142003031803542c290300401000034086007000800c0c0c2c0c1849031300030490b800c80341c1c00d082ca034410142c84400e0048 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 764041276 1250 764040026 764040041
    0x90a0f0c0e0606120601140708031006020c06070b010e070c12020a2a0509040501140906060a0e06060316110a1b0906050a0b030712020c030c060603030a0c2015030415 73
    0x1d15241040c0096003075449810304c1d13103d011b47c50040718100708055a0303a9880b50400c851a502444c000da1040012950403c904200305c0340c01d48950b07181880607100c403404214140500800c180c210b42c0400c1400e4418003401b03450b250072000507441038480082c004c2d118070701044162000034603804841c401400e1545c0160010080c0b07104408610701e0a000e1082c0007500a00c280d0b015507030742080070b5142c140e40600368804d14001c0007400c1d0300e140000030480440c03506d4202c2c11401030f9040400105490b07101c201c2f40c100712641240c2820040c2c8110454440d104440410042e00902500710100500e24500202c0d91410901e44200701751103402c200d0482e45944141540034020403002c01c0070400881c002c60f000074940c130301101074a03ca62441002e03a4000d802d0300400c0e82c0700003000c620341d00c81807100f41d4000c1001c601640c904405040000c02d030621100300940040307005e0514bd00c40e040e0700c50034101600700c0504850000030307c101c9980c8041d0002c680c00e80f030841404402d61000c0c507407480f0b4100e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 764042526 1250 764041276 764041297
    0xc02010e0604061205060402070503043f02090a06230120031b07051504030203010b0f2119030302040303110d0512090c131b26090a0f0c0e0606 63
    0x30020800390300760b0000d403901038406d5401036070030054000452804e0009201400ea00d08054805001c860031064407421060101c401c4880000c8109111a01e035810504810f60119500d007447c0d1a402842e500906265001548134003007002502031688c142100110701c030714240c0f01d800d951042c00c005041c0b01c2c0340749264050160170400082c4080c1035102c00688403000b80c281220f207a2a1603201240c1041100d140b01d800600002c50200110301d0709024012403100240c0e04802c0d0000380202003141d580a80540110b500310003403e002e40c100d41000100216034000c4a41c1c0d10300a07103030601500a49c4540400e500050b010707c800484500f000600004020746a0750b05840d001c5032a070070148003c0050302c5d011aa01912401c101540c0e90705d500810042c40401c3c000855401c0d180780c201e072410445680000707024860400015200703050040014420134100d6081030380d1f5070321042e142005403c500051030b8204c5021000240b1400038a044191101105001c1c1ca580700d0030f04101f1b4500502d110034 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 764043776 1250 764042526 764042537
    0xb030c060408190c0e0a0902040b01050702010e0616020913050d1b021306122121150512060a050618070e010504082a09010b070809030a02040c0c02010e060406 70
    0x120f007110180804402d441c01030a0040781d054880050304d10401064611010654903050100150310702480790116808003401e10030310300b0f022130380040c00ca1100d52501d14414079001c54078101b00301c907143c80c0e03c1c400360b4028204103841c070345820301200a00d00c1c0b9105075951710641800c0c1902e0390194038500c40d44440c2990502c03250a80350708101001d1009c0000c80c00c180c2e2184000a101d5035806808101d5902c603160014903048011aa240b004c044145031341d00300101603007000095030b80c260150800002032003011605c0c1d04404000c0e00d91415640c00030b60000282030700d24403d14400309290307003e180030090500c407a485001c10410f00d41040000d202c031262030322001c01c0303c0342d01030400a10068410b06000d410b250703803801c240b424004a034032903080d80307226804808511041a00c0480303141600300c501c4e91080d414003500b00341718000c840c030040c0a07850000b0b0941081e6020407034203180701e9008000780040e0345120300017003a410481004901162103052003c95030f11300081920309540a56461 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 764045026 1250 764043776 764043793
    0x20a02061e04030c0803090a02040908030610031104030602090d0b0f0f060105040621060b0412150c02030405060703021f02040503010c080910090c081b0907020109050d0c23010b030c060408 83
    0x11790450b50310190001c03106106441c82840181c82d113008000f81a8082c02050b51a8036180e010b005a030580803241404152400075644551648042502e00b501c1e00b02000584a030000f2020681c504407051010308100a502c01700407444a00c0c080700da100b4001c440300d100d4540ca4140c0150380500650103a40042042026105840c01d2040500b00076000807281c045205a0307541c40c0c140007030380160480d620343d10018181c03d05011400580d4071480c3c2d00322074101b11003441048020b44038040c40c01107500c610000111607050510811441c2098040d0036455003110011241600081d032191158074000e509106a40d4592030082004600c5140c100c07001d403103100030300c0140e58002c203004441100c0c4500b2410700822605005c10603a04220803082c04420b590307110004001d40210018504411681070039a1750300007920119508904001c00e0030902540602464030403250101d680d0391080d01348c11400b18a64448054001042ca88030540540d2100121503040c04400c1c8258000d80c21540e021401 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 764046276 1250 764045026 764045033
    0x703020a0306230403030b03010b011b0602031f080703150902151e120126120f0f07030207050a33031b03051f14040e030d020a02061e04030c 62
    0x31144071840c10034410383c004040841c2a1004250740c10740000382e8604140029090074404c1380d41c10302090a203422010340569400c40c04a0307480c0002404141c010000c102c0031415100b5111f00080c02ca81440a46610b50f0707003461b0784d40c0d01440159030481002ca55082d402c0f00c2e51048080158000d00100303c054020307e50b406e1283e0240000143c01170450780403601c03040910018002841c03032b685011960707500d400070600c20b00310042c0f07143d0101c8a0350700b074071201180000760122081c040410800c0e110303804031921414502551804c80240d0b00b00081da4810036501040840580705d088803491180c607110850340c2c2008815000003015411412600b90085004130600004c00f402d0346404242c0042c5034a010750342408600791400400e1711202400300c90440c0c8040d04078040508188141c00a1419014851007050103090f90301842d40c490b46070a1540050048407503400c4810801c0d5515605103d0095030f940d0221982c3c1403810b1440a160140c1542d030252a0145800d40d0355400340764190385 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 764047526 1250 764046276 764046281
    0x1e0a02030304021905040c0e0a061412072001020304050706020c0604050d110d24180311070801060b090a080307050a020616020415092313021503100510020703020a0306 74
    0xb030130800c4218100f000040c0b160744038001c5642184141e82d407541c4040031581030108507000303a0020310501a903014440508400030013950300b980d61184001d02c032500c460109885824031202034000340314800240480800b015002507005902c554120ba10b06980c43c0000c984805120040300d51008080104009910300b00e4084420540034000b815528620301c00041d020308020170048902c05000188045250151694140b40e0420440103003c052403903052043c410808180082c184501e912202d190b900040195078054a40c01e0b0080200c251503d2107103003941c00480320f852244645440119019074040103507040c0542c040c00070a9404140d13400c110703145c0c11107146500d40407070440c640005030b6600d0040c1c01c0c02c0d102d031203150a17155051680900c1959002c1195060000c9074000390b42d880f0302036503065030384070080c0c90340340710502c1580c4005a081d1400701e030701419140b4040180064101c00d080140101d070001c46115009000c211000c0e40c80d5280d07480302940c054100d031001c201090a58 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 764048776 1250 764047526 764047549
    0x90607050c031603030210090b0f040510050f0612071211030a060f0510170604120201020f180111070b0d0908071401150906080303130c0f08031e0a0203030402 70
    0x3003058070300711007002000c00e01e4851506141c3e2000c40480008000741340d01403060032168141d0840a01c620b01e44c545442091404c09800c030b80c942240600010181b20b0300340019550004c40c1d80301400182483c81a40403080030079500e8038400d500b606282c40c5415000500c030f01c219091415401502d13000d80d2102c000740d1340c180d0015a050701903441d0001c0010054801d036100368442c00340001385070400c401180461803458001e03041100030501c0d900c6141c50005040c3d64400c1c0d2001e1014500c0c08140c504030301a000743c4210f00d45000300441d6a1181000780c0820340c080ea8401e03071f03811080d800304001c07555031804a403060f11103c4008121801c0d0049407030304003c09050084c00c040e0300d801c0d100e81e1040340340c1e00c1c161000d0390b00d6552000d212800d070500103c010010110040e05110f02824411100e40701d05c0064071400d80200160301c60740400240c103003040d00070881d442c0d09803850fa56900034185c83e9400b00f8610889201d4048000c450144072009448941a041d4019819544d459080c404403c190 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 764050026 1250 764048776 764048783
    0x1606050903070b06040b04060512011a04111c02040b1b010c030c0914061605010e0609011a06090d0206040f1e26010e060c0a02010605030d020604020132031504060506090607 76
    0x8504011840751100c00ac0d81ca2449841c030b00018800460200d2080c4d1500742c02c000c513220300d00344000c003030b075081c4400240d94003403501500900103902c0c02d407902c60003445582d02c00e0110b1000810650942e03414180e541074074000c800f00038800484410030480480c0e540c1d503080c102091001e58244515001c0c180d001c03070600c5000c0d16a41c40d021429641902052030250304075096910303454060407881e010b2050315004170058009001c00e0a82d54141c09009032075040c1640a15804a1028255130342c1e0040f88003581d402810703441d0b0b5035032500d0f03c4000c11541d40c0a008007006250314420604250010800c1c21036512a042001b81900307040d4000c551041840306000c42d640347c404200c0640c0e41030115500540380156030380c0da6420208400780c250b54503079204603c41c0e00030000c00d00c43d903600840c8180e0711642c24600701003140c849048465020340d401c0320000003000381c1c2050301a880280c200030341c000c117070381c0c862044440c00d40ca04100076103000e401042d401040c2400480c0d401d0038048040d2072000e20 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 764051276 1250 764050026 764050031
    0x1305030903010504060b01030e0a02030622020409140d23091f0306080d030213060c0503070c15110c0f120f01050f04021801060203040620031606050903070b06040b04 73
    0x1000041c2c2516410345050700d00ca81e5501c0410519a05407003a109001405000390414840d181c0000b5120403004080c400314110040100007c400c400b00c8698526600400c100005125801c00c0102d41403801e80c3c8100c1c61051a403c10140350003445034542c040d8440c3daa00c200c0e48071010051034180c0101c00320381e4005c084811035001d02800d400910f68186100c1e81c00003038841c41c103150540b034040d0b020042e8060510410061005003502d078105801e41d00c060510400b81c6100e0720304031745944186074019114102c1c40c4d1010540c14400b85142d041600c0c180d039076140804420402c5038075007500b220010b82c48622081544018100503040340c8002c0071070429166415030701071519080d180201c5803a189046550b08010861030030303210040c505014407210101e50340c14014040c0d601d205a0144a080c08900c0302107409401c0c0c0b000104200001080580307490f4034900010606105095400b191030b20309041c001402480000240c0303603074540141c03048196840711018880146218200c440c1c000c0e4 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 764052526 1250 764051276 764051287
    0x6071e0f0807050c03010f0b011704020111030f09030706094a0420031506030a060e0313090e030702060f160f050601060c020d060f060801061e09090b130503 69
    0x1070302000600b104600800180441c00c4121042508540402440e1715141e403401022440590780300f2400c010204c1014980318031074035180016900300001c90a0031300342c0d110014146405035a00805814012419411101800c2c2c454030107540341c9040f402580346180c250020546d000b403040216542d08680c950802c40f020b4800a03030800710320303c600c5542c019092510144000c0001807045030021800c03c220301d803500683c640c00640c81e0a800f80303c03c556040380c0c0c40842c0d0b55a0b418002e001e00796a00980c20040790b80601403040d107a80005030300429070b07512500e001410244c64000c1c4440041d584010754a05081c071b82c02c008403a0401e80003420246c4052000c045410001800c55050502601e03c44182810514025240c400141c101c0350170800841103c07001a110008080c520582c40035011407004034035100000200480c4c1e011842c0c1c2d40c04d00300000341c9640c5c02001e01503018070007600c44280645035200d510aa51004000a0285918000050320307050301e140401e400c144218240c84c80d00 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 764053776 1250 764052526 764052533
    0x304030822050a360c0504030b0606040b031603110310031109090d030c12020a3524031e010606051204030c020d061e0605040515091017070305070506071e0f 69
    0x60341c0e17500b003800100b04005070600512145040480d40110201d9000c3d10303140c01c107446900c5502000d04600d90000a0b0117180c400d1034060b40000c1c60084070540500d1700c03464400c00501c483c0c4510312040d28003155840030945682000c0300142e03ca0b600100040c00400d903e403c040780103190a040407030410200401d00c0299a4190004004d5a020782d41c4206110260000004800604407052003481c1072400c8038007141081042183d13880300c8180510b192540d0000d1440150200044501c0e526009a1009801040d007200c0c010b94200c1d02070000704000398591317074192944e10809071020b00c80b54a07440081e00080c81a0752540015101a10300e04c25a8030643e209015076a10103405403a5440521441c03c610000c1e00c1000000c1500f15824080c2c0c1c104408030301d105000c0754080c54000c0300d442c400501e0002e112640c1c200240701c00d250040d40703131410101441c0c0f1740b800780c00b04492314041c0c14000516440c0003402e0381c403c16017200d60790561001400d4203c41010a03000c0445050540100c2080072 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 764055026 1250 764053776 764053781
    0x60d0b01080c04050618040807020105040803071208130317040501140114130b01080a0b041e020d0e0f030d020c150702240c1206030304030822050a36 66
    0x2826150024800702c00340e0b02c1004113403000201042d01404440e4461b1620220104503241c0068110440640d20b8004d400100c92910460300000024440051600100060400d00700e400c100d1550310003400e40c070780c201450113581c42501c002e80001c0c20b48100c107401e130000026041c1c10900c50350000440c0c031912140c3c2404003009900c01940d0310f1490022102038102800048500f0032400740030449050104000781c03c1c0341e4047d184106103030fa985030032080358480340c1c015245024020b003c906850000141f40c4083e5102c3c15045001a0030041c0306810300500040001c4003819110245091034065400c200007900024a120011701c0340d40a644c071248103400401d40a81e2003640900500c0100d0100d101a05188604c40d10025200c103040040c41d00d80c400664020308164144c0404a403a0b0070002403a5004581025040440000c0c00c000084500582c08284104840802030f1340d03a56001040301450080c40742c00a803074a14018030344401e101c0c131545a002034190901c1e001344000c01203510704 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 764056276 1250 764055026 764055029
    0xa1118120a2009041203090f0602220906030803070503090c1f020f1f02091f080108060c09010c0303270311071403070b090105040b190806040c0f08060d0b01 69
    0x5001c042008104a0b5001d800d4400015a009482080d49803c16a8031030400607506031910742059034540741c01c41041400049203a6250300201c0c2551151505103940051a40d56481c07030b044185821400138411103035010b10000c82c1d4100360b89a0865440b814282e400760300040140c61680900c01c109900c640e80c4c40c0b0401015210b55844403502c4400303110283c50001d00d6040c0402d0340d401a119103642485e0512503400c00d0112850250700d40d01000f01190040c605c14418080404141d8030a90900d0b5004c1c1d03210303040b142d092085644685400003103907614403901600c07034005907061b481d80c0d0109000e6040508400c04040b81e018010325010301401100f4400c0b001240001c9840800c0700540c2006c001d030300081c00d01c11320551044c489180010340d90300c5039441040a0520040341401c020782c047d0041e00c0007000e009100998499903a021501d1050401000f0f502052001e000702c0ca50342401e100e030741d910030305a45608240c01d19400081d20387c100b0041c01c1d41d90085044245200207203040c0203650 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 764057526 1250 764056276 764056283
    0x140402060708120108011a010507020a05060a050c070e09190308071404080307200a050a03060e15040c030302070e2404060b130302030111031e0718030f03080a1118120a 74
    0x1440707c100301e452091407988120080c0c10807034280300c4440580d0316014040c088a50071198590f40340800704054504e800390080a20076402142c00000c1c41c040c0b8804020320560544003a61599156060702850080710444d021707001811036000501c40f540200140d0800100e114509810550707107003084c503d0355001c40c00880300503092090401e110790398552224032108045821904840c01c01e0007183c00485c00c6e11016040030748580502101d03180074044a0a1140c0b80a1340780c1461400b4100041030303212a00c400c50041c46107104c00298503211450450003088641b1000e4a9a003500d082d400090528110165000369a02c6000a440c42d1910007410b514086003881240740d450b50040500310740f408515207105400400070403c1d2400070308609078001005661807181c540300e00c07104661842201c0e5242612007c043c00c0401031011300202a95802c2c0309541e00442a511950004107031092220400e009020501c4074507401e400000d5400000710026181c640101024a8440e250a40780641503 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 764058776 1250 764057526 764057531
    0x20a0c0803131b06141b06101503020315271005040e070305031c0b09190506040b031b0d06020d020309101e05150405010605030601110114040206070812010801 70
    0x21010002e8501490304405040b01c01180841c0c50520301a2641782404109541c940d0300281050900588034211110b10080c603044808919100d5551000da0103103000c0c0035460012191705402c007a20900071248506010600c0c44059501d03070042c03209129158211318410302c640300d01c601c00d07100880041c0344540001c84519140519090600040743c40300c601541d0719400264060004c220f00000319014a691701d18014490308008180e94018001507400c00d80c480d0b034402c00d0014120a1010a8410118004040055460b01000c0000311888084902d8060b000341c0c10703e01c4441d070248500d4003481006030500c1c04824295032648200d91014002070207455000c410300402800410070310920603408581003001c0c07072400c004440000703402c4105500d0b003519400040d01e44240c004024415280c0600103100950311200c02504035042190014001075001c0e440414900301405120509071b402050108542c031a0340911405038445007003035509082c1080303264506141c4840b990700804100000 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 764060026 1250 764058776 764058811
    0xc050306040b060f0703230406021b0d0507090e030d0504060204080c0613031b080f011b14030a05070e1306050f04020f0d0f0b040e0f0606010c15020a0c0803 69
    0x40000b220344070340740b9034040c010600c4540c1541d80341c0c5088078983c07501410b000c03001201000340100460503914048207030074001f19001440b1a0009840d0340102c02103070712179140140c42e2052001c801d0340c12802400c142d00c040c2c410003600460b5800741c400d01d03c0400551f407500070004001d40075900142c4040b1802580001e042001009c248491100c0d19003c5414501d00760041c2c4c4100080038403400301920150340060f402a541d00e00c0c0181e407000b0000c44065489189144040c0360003080701269601d8007401c040240044244104424226118080340340c1e030441d290b40c0c10300002458001c001e68148080e039041c0211540d00c0501c01038500c03d0b600004141142801f0178020081c6c1204150790080b03005000d6071203002620410354548100c00b000000315005180c00030000381c10410406900186050110074003098003044802e003c0311008102c450540310380d401114580c801c2040030b032556903c60322504105c03039150000c0080311100e00c1c10745500c03851500c8400540e0300aa600031700e1100009030 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 764061276 1250 764060026 764060029
    0x702010f03051504090b090f0607120b040213090f0605010908030a030b0411040803030406060501020705180a060306050903090f060306090103020907021002030c0a080a0b0303164106060a1202010c05010c050306 92
    0x540400234100c0001e4001d40c04c00100160011407440030091640c0c3e161425603650352500c1d0305880141003400106100d0307950f54041c0d40300a0a68523200301c1d0181c00c100c00030a555005120410031651048019423a0030000c1c0821001041603044899215455100c07205d988105400500301130038010300915501e080c40d140c140f040303500319032107141507401090040106a941c180442000f00d1129080155580d6040c0c22600401e459040113041e18035000601c42001800070190801480649031611030a0207142048500e0004403482a40902a540140014203000700700e5a084189401202c90708481c1d444050241c1c0c00848900c656a070340480e0000c081d079405030b0400d4200311100320400803001840c0100391640704e4414852010811000350104212804400c1ca03144400840c40e07820a010101c87c829940d4021400d8400e030035a440c14805c2001c1d13021916070b000b414018002d52f40c4510b40b4040e82100e40e034840081c1d05100140f10b00c100404e50a010303091418040b0340d5200d941e40741c03400 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 764062526 1250 764061276 764061283
    0xe0412080106020a0b040b0a18110a0515041e030f050a02040c0503040c1e030804090e0105010e090309010e1f0c05070603060e0c0906041e09110702010f03051504090b09 74
    0x81c4a01c04540c131200c0d200c1d012031040320001c0d400c207410501851403955000035085c003410030303110200300140403080c455090001a8007903004c000011103e540045a0700e07002c100b00d00403240e50910601500300410040c11400ba0340c61280021880020446280d4075142c444180b501041c00340c0b1903810003030f60401185414403801800090604009003541059215640580828061881d402c03880d01c0d031541e442c10b40b8407500e000440d403060f0038036039994440c100c06000c1e203078204400100790f080800200300b075411707071400b07505c03401143e00110704241c0e40d03030011180840c0034020290001d80030045203207030600940304402030409075161142d0800041c58864682b030305a0344510209494068140480303a000d104690b00711000086090702c56100c540019001d2185510400c03d8440f80c901d010300e8521a60302e644100c03140b14000f00403460054410896510a008000740080c02100c001c0f04075500a0b4005c0d501301524034102d054584038400803030b0440b032109000340e840d4400d00b01000140031040 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 764063776 1250 764062526 764062529
    0x8070905091e0c01121517060604020705030d0c050904020d0e15060f120c0a0e01061202091c23010e16060c08070302101401170c01020c12070e04120801 67
    0x1104000340348900710054951a802800504020f9035540031702c1c1903100e41c0c014450680c1c40c5008848034540d91032800d158024003100594140c06000c00140180c0750034070075211000d80100245181021800c0090001c140d103403034520601c1b00c1402070007050746691002c0c10503c0c105400c0042c2105e01160f09034946442610030740700c083d00800401c14291a54586e85004540c00c2c0e422080700c040c842e0200381040382c64195590061030751034000407107001400580d4100d800c9a180c4d03041101d00840000c040e03109060281da040001d100f85180104282c040340040d0501880c448982030300c071007142511a000200010300507139141c807000004074070107000304a2202464015902d00300e00d8074101400103ca0010050301402c008a034031000d260080c001c2404103000c01d00208085526601910300540083c060807004412800850722045000600040c0340b00c1c05030020000031810b0302c01c00c0070600c020048a800e80c0100361000540041c0842c016019034840d00c000b111324250b501c0001c1000005 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 764065026 1250 764063776 764063803
    0x9060b0703022518020702100c02011d010c030815031203010f090203010f030201201516110715051b21160b060109030219050a090605091303090807090509 68
    0x1200407443c0243c0102c841c2408035803141c55034101e41030114030900c009005a03d8060340202020312040c94183d4801c10790002a4801d0725011200d4001c181c24580941d2264600c0340490a00c3c01604017081c082c81007140d201c00180ba02c121001c00301008207003010500c20030030602e0800400103114485020942001900f41003004504540c509410391801c544203220203414400c119000a2017040003141d40c0e0134030650a408c9918158010b446000100c0045400385500d0181c00c1610034268403803030f00c01940350703a12002802c0550405803517003611600c550795042808020491f00106000e58140d80e00041028000b41a41100070300084400a50052106d00c0c03554040080c410f42c3c2c41580d00c1014129001800c0711110ba0300e00740183d803000129040a903000400e861803d100da40c14601da681a10000e95420320487d5641882c18180c4160f40244d81c2e01100000008a80680d450400c081c242e001c2d10b0701c0e0b101c4940d01c8041c03900b0980b954004240140e110303c00c21a1b817210402100707503014003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 764066276 1250 764065026 764065063
    0x100b03010c14030c16050a12050f181f092102030a0303020a14041206110a02071206020d051906060503280e0709090b09010902030a020603070909060b070302 69
    0x307245200404500c031400816025040c0440841c5900c160341065031009056200115032040403414a19910516041c0c00c8030f441d8400e42c600d82625100e40c0544c2c2d00321031915800390600d0740c5a00f500304103040c07501c00d241d000900044000381800f40e1740a2610098481c1d201e150001e81000e04184ac0c1000300c0700c441e40c01d98a181c00c03000041c2c03030000d4810f968a030140b60040e1610303d2550100d410807a100401c142d10722000c180412810003202455000c0d52040a040150500903400f8840b45d0050f840d050300940c0000000700410301c040c5020140c068801d0000602e05450008110b086071400e80311002c002d070000f620249403800a10606000d08002e0074854114903080764540b8454000042c010920f03410f52a64440c80c04036900144a640d0580c0103a411840d00d4002c2c8100030010450b040d54411240344c00320380c000c5410300c10f4080d06500030f40908001d40407a000c0c00084d910160000c010030030300300400504c40344148152400b80004100d0182d560780c3e01d003002454000041d50704080c05d034 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 764067526 1250 764066276 764066291
    0x230d140d0e15120f0a020721081b04150c02130507090b0414010c1509110f0d0f0f02030f0f0304030c0e190b0f0d0c0f060207030305161112100b0301 65
    0x90841400c681d1204c0380880000300c95681c841045c01a002d07c0760b004141301154880307004c44003101c2d0310303200c03840400c2d03030300e0400d0307996030244810750131402c0c10000319910800c001c1030101c001c084814620b400e80d1824035145219580e030100e026140b10307200a101d400e0f40d5100b8441c2403079010821000806459144500b00b034281141680200c1004403031a0620aa0303030303154000c00ca00c007800541184141d850400180410b03050000e040901100305a1090000c4010700489103840407407c2070781030308003100220119031a900c00346e038440100000c2c0c0c0e00d4840d280741e11403002c030100040c40c2c5641d00207000d503468500d1890300080c2e400313540d000540c14000304800c01c00650816003445402525100002c28150b0b04400491018180e4180b0203402c00d0011940a00707001c40c802041c0100d078030000040c000c142c3d0707860080b42ca0310b400e80801000500c00f006100b086400741f501c011409405a103140c08201d00c1c1d0400100f4420320942640900e030409a040750981c0c030700d0300c980f10003100705030001c0c040e12 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 764068776 1250 764067526 764067547
    0xd02031204031b0302060603070911031611030a0c0201080703050106020628060f050f030a03080a0b150d1a03011b032c0a0606230d140d0e15 62
    0x9024a10100d90808500000102810700c11002400341d421012072000b5445a80c0c10029203680e82210018001e2285144c0001c104566100d81c90000b0071440046065403908150400c030903065803030800401c4002c0100303510803441403006207107890303940d29480f9002c03200b440050040d51000b4803034414149072200400480340c02196942e4807804006406e250a400c3c80c0c41030141c0040381d01d03100c0046150100c0401d500e89400494802d0340c0f805c40301c0c8102c4504000c02c05603103800c41040100014440c2000c100720200c1c0d60410024410014042c0c41a01440c1d8014240c0d03801032000c0359500f60f210075507400040c01100d8155032000013603009000543c81000d240c44840c1032604400c003003603a982c1e020428035140e0061307074414a42003c178a031902d0320900e000075512001d80348103417031240c54280d0009040000300e500106100b0071840e0021400b09030070400c640700022010544203580341c0c2514120502042c48500038518094882540c04490441800b000d4680550f00100c00318041040c140e10 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 764070026 1250 764068776 764068783
    0x130803130e010e060607150f1e05041205030c120a0207060f0603031e030207120504051002070510030c1719110915031e0a1d06060d021009030c0321020d02 68
    0x1250050b17600c155940500e01d1300d01350300301c10320340d5071041a440c084400c1c8551025401c40d038070a003e0b8070300c00d4040350307030310500c82c01152020303a00100900d100c0c0000c0304000f07000304043c6602c0f0141c00d10281c1007502141c0f403580309540851b003a0700613944c0042e825042050710f201c0d501302c003004e00380304109060440d5806002e00e41040c0354050380707401c0305a054004500c40c0e0122118581c0c00a201400c104c074007030300a06560010301075148a0b41071060403086d028400940c000480f040240011a200500c04040d40100540c503290400c0182c1c0010309040c1c81003056070306000300000e075607810200c0091b00c05102210001600500300050412400701281e84020703403405120003840b800c596035190600720b000c5100c10b030f6500b08a40d46000081110341650760f4030900d42001203840d0246280000034400d9110001211101e510070b4041003814058105520a800b00100c2d600313010b064141c813a2103420031200c00c2d501c200d444201008070f200c0030482c42d1042c082402c1642c0000c05e4101d1081c90302948 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 764071276 1250 764070026 764070031
    0x5010b21150c090307080d020c120d12020c060f0405100b010c08030a020403021e130c0507031218050708010b10080a050601021c020c0111072603130803130e010e 71
    0x14195545000300e0281002c840c100c4500440c01812510f17120740d030344101600d0b41031420b90b03070015002e121200b00640c109405600d58428503500038181280c0711180c240c40151030000e2098052b9424440c04186100410025000d21084610034481303140501c1d102e8603029040442c140c1240c24075190314a180d8100010784440d035131100036a03460703a5800700c11400900460b807000c0e612000308039404408001c2102920030201d001c2d12040104c50744029500c080d9142c1410090004004020b404c001c43d10811003164890202140421255200300260303200e001910810340d25134200d110200820103007485044402041642c69104113810000d028048d240700500700340301d85481d180080c0e8076070f00c01e0000c00d0740405022401146405000002503a42e104c11031101d0208900551020f14204001015421a15603494600c1c00c825403102c0c01020312030304181e04a039480140b10003c1e4450440d15540040c00c0c8140c02503858020406440a141088d07910100c440815600140080d60b400745600340e = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 764072526 1250 764071276 764071303
    0x90109020408370f060f1e0b0d05070b0a090e100b131214060f010e07050c120409022203081603050d1401080c0f031506011b05010b21 59
    0x4001e01903007803640d01401100e008403d000c0800020241000201e8205030a82801044100308803c0101c0b5902e0071640c0f844601380c0e1078400c9001100f61501240c000004030b031006480019000060b03900c8a162142503088601300d2803021420001c1c0329402180703c002401749091800c001d0521003c0701c8158030f00c41c000d0f417040c2840020505030f40106601004014030590880c0413080e00d5030b013081c2134454017180d4008050b00442c00882e0b1180084025541030314526884404251214541a070300740c0d1107060760084c280601c2c40d69402c61800040030340000c040d03401c80541d543e0940c01c480034100045001c8031121031040710091020501d0401503070440c1e4002098111071400505080d6410b001c0e85900401590801203452400140302071236038101c9143c0e5044410104070f902c02c11040d00d14498506030540d011400e00e80d2020003941001d07401c07540606103418a04c54540c60004c043c00d03c11400d9034a40e4558216003450306100c03030100c03492590b8820900140b0540b60140d41c48107000c10f0b040 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 764073776 1250 764072526 764072563
    0x60611061509060303130e07120504111c06050109020304050610080c04051005060307020c0906040207200a0b030903073014090d050c10051c050919050c090109020408 73
    0x20f4001c0e203041044174251800c5001820304ca41d5601707003080004104407103010011b902003c55004400b800d01425008503407143d4000d80c1c6021010a0080756462080511f0b4080030305080d80c030100d80c0c0c030300c41c80d4060b2213030140259580c50b141c10721500e822000b80210203410301c0d080040107083c40100d50191214000c0380c000c50755486825060b07540403619004560b10103c000203001c0226000140804820b0b401d40b0600340503610042000100e01a08101505175031603d103031041014075103000e48800440050505000075203d490201c03043d04101d070903035040e50000400d0300501c0966444802c00104102d184e4010110072006c908151500d1006001032241c9043e01359090391001003606c600160182120a1a58050038000c1e0360788030030042e1038000d40004000038512445007044403c00003440316001981201981a00000c100081441c1e50314080c0404c1804810205250100103600640c000c10f602a03010307041144034441a0b0083c1071a6204101c2080b540e0404541500c0440541111 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 764075026 1250 764073776 764073781
    0x61125050102120f040311030301120f0f062301080c1005070c03021201360314091815041509110f070503040807060203270607021201060611061509 65
    0x12501a024110032a40d0920f02441000302134011103c030548124002e0f43c03640101400e942a07680c6900c0b01b80031782c0b55024161a219004201d008448403107186c4101007004c0c4070b006540398101118107250300403030794025003070612513aa40d00c100000d001d04501d01c080c04c0d0030b0356504002221b203124164001c0a04c84d0115018091000a04004004640103440b070700582c4503c466a42c003c0207080b2081b06400414400540b40400144c00b0707000041400591820b100000e4400b90782c0d60b4140d450b084440141080a03070425140d082c4404111001c0004680d01360038020300001500012214a40c01280751001c00c14000419104080c2200c01c003803000541100d2142810186200e120240c00000c80000340c101e00b080400402001200c5150058409240d1509400c80e26441040181070445903045049140f00c5035171032405810043c020100ca02c0e00a099001c03600c41d010004441ca01d69544000802c1140d410820304200e0405140c00b80c211340c13034400310340b028000781082000d0141100b81c00 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 764076276 1250 764075026 764075033
    0x150d02030327190f030209040c082e09020a090b0a030501110a090b070b0703020a0306090e1f09020d0f02270105010927090309180504061125 62
    0x1c44a549007400c25030300b2001c0d06100d03446403011203000428010808007007652606034041e00c0003000c2d18504180030309014596000c20806e0080a00709540100e80070600107500e0300c4c20000080302801c0d016071a8280140c1c00c0980340198829424010110700704004000182c3d18604848241c2d15400740000b10b01d20b0750790110b00012507640009000350728128411601c10b0404010300782c002019640c850b10140c8038075200b1014010024003c2c404840c04000c14401ca000743c0241c00032072510f160000314079a44601040a84414440140d030a4009040740e01100c03001c2517a48030b042c403c1d100c0c1804a9052540810142c140305403010300340e140b2042000085590707080e440b2030507035002068000d200c1110a00145404428071800c0c3c00b2039020a40007402200280c0c60007480e00a00d4081c0e05004002840d81d030143c001403a084081002440700070401824240d001c1c40c80021035200080c3ca89800d107000310440d101c1501c4e17000c0d403480501540f4800d20b0042040d601d002c51100c60700c1824100c078035 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 764077526 1250 764076276 764076283
    0x160806070f120c0905041b05191812060e030a09050405060d0227090a0b04060513020a08010c02010b030c0f010f1e0503160810060f0908030c0c0a0b03150d0203 70
    0x40028000b40c00c180b03d4040240c1d210328a6415103008440030005005003440d01ca0351401006000d001040c02440366000036840345c2c40410864034541050015010741d03a61081c7c1000c455004400d042000340c0708442440280d209107081e00300450011481c04081d003801800001b258451540b2880e19640061516100c0e1550080080e074040c000c4a8a07402040f802c0c82800081000b24022941e143e00160304988001240c1e00c1c02c41c0c0000782e0030a207446a03203c40002d004000c0142200c1c0b807040c500400181c070313034440c50340042200d030000150200c40860000e00b5603c0c0352041601c0713603000c0d6000b0b41c1c4a03501c2080604a070386003424841b905106100c0291420300702500e0a06020340c01c2c4121044158005000310320400c00d040210548074918401955000720a40e110311402c0440c100610840b40075003500000010fa034107001392140c0d41c0d01102441d41d803040380c4400030b0b80c025050001090400e82034000c060702d40204907605602e0000415007900d40c0d901780e054814401c0505a605544092 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 764078776 1250 764077526 764077547
    0x312090c050406080a051002090a0e0c090306071d03060f0127060605070627120309020a0305070f0e0c22031a010314010603081902032208160806070f 66
    0x40d10512440c1d694184003511461400000d4680b03000303161040d0206046c03842100da407040012b24103ca01800c0c441400c0510b10020800d442900e010070440c0e80031f56040088600c5481181d464135000d945071040c00c80c0c1c0c0c0cbc0c00552404d010381d000b54244960605886001d0341541c0240890300d2020f0b0414202500c901040091450302a103014070206186a02c039000b40a85030041b103060001180c10f6802002d4004044e0403491ba40050f01003010003d80c4503c101e003140c001520300032412a030150005940040e04ea402107640303601c012010401410f22000c844000d044003e0305480526258641d0400c900c01c001400945840c85540d000c1000c0d03000704160301968000184035400c0310088021005041c0a00050320180250014810b000205004440c140d90344508002c5c100004003900c40800c01e0101c0507a81540001d01c0124225000ca25000440202c1450018921454074840c5070401d0f0002109e289030340e220200a000000d8000b0300035801001e01d2600c0300c0c4804032178504503483e0018 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 764080026 1250 764078776 764078779
    0x2120131e09240203090c01453209181c020102030708060301111206040b18041202030406081305120c0c030111210907090f0222030312090c05 62
    0x103100300080003007503002d18460725000040f00c80c2021b0703030030040d10100a0401c130004000d00c0700003c241c0225107201c3c2d10304404107641d640102ca604007010000c0030f5086420214032038080342e480d0703e00c41c2104204010400108610f584020040c0c00211355038070b800402c03817404000c00241d2503180c40710802c2841cad0a0f04901d0b282480070303088228002e01035801a200100043d40350400f040b058134061103402e80d06626401c8484c6090a400e001e8035040400070710700c603070160741c5550003146521641e0300f068602c1101c038502011032410340303048031446150300344e02c108541c4207001c180a229003240784c80c0c0e000440a0080c2c1c680702d0852400c10311307018035202c18440990001c14641c3d130700c100010354507400311400c071f0080c4803600e40b0341020b0b07281d4001c403c00140400f0820442c91310601641d0b42e126040b0f10544140e5032110740340c0b942403080c5ca05018013507501c95030005100740380d80c070310200c1e02c4458540c11501d11700491450302c0c002c0c1100003107084050100c4c0e945042030200040780a50764001c040 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 764081276 1250 764080026 764080073
    0x80c071d01030320071a0c07030605041a0c090f12070602010608071d070804031b0807170a0804020603090102070b04050709050c132120131e09 63
    0x62080e0403805600d0078031045000c42e01508484a040541503049100910365400801d809440c0000241e0444517094480b50b40d5201040b802c82c191109000c1e400195020b05008600342c106440c042d80b0580270b104441700b4020b190400d104140d00b841c0d040b543d104008075001811440c0d218002288419258034540d00f0b4861801c001582c40d4064204d45d0455900006889619640d10ba1312201005100c451004590041e00007418450081503a190002d010303141003460b03007001c112079408003280300c101680c1810300030071001e0400202e4950301c120320803221201800c0516014020307158010103400240300d6070340400003c0d80700c0400d5050342c480c1ba0f0021554000703401c085c203019890704c4842c09600c8140d030800000902e0307800604119804205248001e000c2c2d149006100010440600b001076020403200b244a40802d000361000071014003480303440403070f0303c50160800005414600d6030740000f0b81040d80c20107941c016600340e40d601c41d5161070085541c500c41d10302040d04001e80503040d1441b66 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 764082526 1250 764081276 764081309
    0x140a061b0c050429030102090906100e1504150302210414030706020304050d0305010312050c0a0c0b0d1a030d0c1e150c080c0301030210020f1f0b041107080c07 70
    0x881c2003c0c406040100d15075200c501844d0000e1500383d1180e000041d030000c0e240c07400308203181858424210b161519162840720340707011000045220241030306c80706c0142c80c045414014980d040002d0110400729007811440c00c8500c92180d0f82c0c03001d0035192161304c01c0c1803000113010701c850700060b6200e0885000940e60b5454541c5400b074000d400a407016074941c41030440b50407803603020303105650599403c000070203c807100e40442124980e109030401d01d11401904110000244101074140181c00d050680300d841d0f515803000041280d558070200c2d103041810803645007454802007504008107409190040f80c0380349504181451a40b41d0304c032508000f503801092003d2041d01a4903c92401042d8020700040c407611204440e00b840c140c0307001d0740540040004000510b010540a2009001c07401990218807407212580c0c203140d038010620f00401c0c0c8c100800f1020458500c1005012181207400300020b065901a51510740a1400f000b41503c07000200020b07010030801040c1c005002e102e098001d0030 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 764083776 1250 764082526 764082551
    0x120203070909060b07030e0d02030616030e0303070e0f0904110609010c0f0524060306070503040f1a0702011d060a09030504030605010b0d0c020d0e13090f0b01140a061b0c0504 77
    0x15170040c20706400054407450a41258070300b00c1c0c20b1b9540c80da0010000c0005441e1219081031010a01d01c204050554845201d04042001d00107140700d007603551100c584d0900b80030f06020910051440c0d06100344a8401004001404843c15001d640e0040d20f0544d21510b0040c0161058440c840018003a255941da070702041080001e1480480d60703226030038405036a411115140d40b0001566000d40c141c0060000a401610541c00f840e8490300584603200b10140381e840b510000a5800d1055036241b031b0746010440b03101d03024021920001d540e075240580e220a002840c030380791b290107841111140d4032102c1b03240915200700141c0b005103800c40320400c4656598690f0f83c203d680308141d80400503050449212a95001150110000001e03031500b0f0039a404280400c03018a00d984204143e150782e50003444003090301d2441c080c0300b40b4490807000c1c050354100320042c10025401c4050f90321865018034140100c0e58004030844500c0f1030512403d8070442e151074081d24000c115008290010b29222160440b13 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 764085026 1250 764083776 764083799
    0x10110903034005012a0b010302040e0339030310051503040f1124030a050109050c0433020d030e0303071d030106030812010f08030a12020307090906 65
    0x9108081807000d004001c5491441c2c030203001081c48424481c0c0d8590401c55075010303551100da0766010380b20010111950500d002c044c0945518141c0b01a01c05400500450529128030359205031268000c1d03080504504085440000c40003120340b82500301e0701036210341004c852454403050024426a074403803501415012031f12425129040c480c1480ca9880f521031803090041b40c3c011500315090651112035500e9812100c07400040d002d82061171180c070011150f81c6c1c00c400d2807888400413407950392410b24402050949038180c01000c0c0052401c0180050780700075008550844500402d0030416105010590200c69100581d00d200708291041400c2c1c22a030201d118096006c0f0f9072010807901151000e0340b941e07800f040b9083d4002c907001c10b54040d6680452100c504010038018004a006921b95442d054150089000710100100a0780140002d411210401c0040c04a00b0000e40c10494850002806007904150308900d441d80000401c2000348500c244002924036820103000382c1d969403407910300 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 764086276 1250 764085026 764085067
    0x50418080c0a1703070516050718020a080a05060a05010c03050c0105010e011d09030a030e030403120816050c0604230601031407060302030c0a050a09171c030b01021011090303 77
    0x1003c42201a0300c00a041203901582e000344003565445007048120b203025646c01580c600169001d119a46000801c005048520450b00018900260315031b1f241c410050310145001d01128006030904040008940b183d64110b401c0b59001d00c1c00c0c40c003070301041c201a036081c07050b103028110039424140045100c003403500d1001c0c101c44000c0310300c07007803004031070204c0c050300000b47c0c0c6c481001c0e04100181c00004e0700c213400c0281046040401d9a25190fa00d07075940c240b088511411a01082c0840100075140e9044200860110110304201e45012102e03401c40e51185070040000f0300508428406000032016407610f86010000c0d10215891541c582c01c108034107841c0721180f901d452196031004035495200c0e0003035034002d950313158036103040c2036030100c2c10781e5030760491810702c0100802c6140018002500342008100518200058046074506018a403802e4440a50030300505040803c140c4560f40c1c00141d8a0b507048600794002511011074200500611512041c9075252101091140020700c01190014 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 764087526 1250 764086276 764086283
    0x150509010e0d02010c02060334180e0406021602040906091b05060d020307051207260f0631050f060d170d0f0c030213060806030304050418080c0a 64
    0x18003508074401040080c2200110090000d02c81d0351510b00142440380181d42c0000341d00c03843c25510264000b030781c201a40025203d10b007440347c032200d000f0710039001032030050b00580710780d03501c90601d040800050b80301c0400381c0011b114650010f031100c0b446c40b200e200508500d500900038070980032035081c0791001c0c2561020545a4030541550200c400813481d0400b0200c40d40900080e040003510f140010007504010400302c02e00070100941c00291180351000341c812010f54071a503480000d030312078080300c250740380001d5202003840e1801d00001c2d001c80364180f9801001114000c4400b81c10070b6404640c50450310f21b85140c91105801c0e6106540070780c004604c1113005048100141d943c0d00d0410420041041c0050300e500c0203200503140350000300d80140240092800003250490186507513100301c0d01000241c40020b6404503011840c807440307c0c82c034001000715213046241811300701d0010f03403070344101e104041c0b10340d540320780c1d40c00e114a000d0b0400f03054039084400c05d07440b200100d2003141c450600306000c8 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 764088776 1250 764087526 764087537
    0x18060a030903031d0c011101060503010507080f1f030807020103150f0e101d040609050a030302040806060301060f1205241008030c0613230f010e0a0b0406110415050901 74
    0x10b48030303141ca01550381300c58540d100400c3c8600c17810005503081501c203003400c1d21030354886901082c5610240620350161980d0703980e08160303203802683c84038282005058144144030710301d11104110f5003c4d00000580b5040270245540340c84520050303000b0a580300b9400c06895040d600012010650070b454000c95021007038455a60b5903200d40b81e50b440e00540aa8280111082c1c100c00e09800c1c06400250f00510652000580b031a02c0d4a41e1442e003407200f2000c40c00a5000501440225803e204007038102c0781c00e5000340541c500701880c6100c182c2c00360088544480240ba0359806111080100c40d030034010000c0042101c030019681d80649010407205880c111004000000b890780b0000200e0340441102e802400058840c1c1c02e1455508c008104e080d900750080491000700c920381403030450f400006000003003040e00742c208417082c251802d4080031480750304040c2a038800b281d24499200c1c0e12603400040050403038018080005580260340082c1310000400082400781900300c002400507040980341c0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 764090026 1250 764088776 764088791
    0x5100e0d02010e0d21110a1704030f031a0402040815060108040305030105100c051e01060501090b04140a180b040b0a050d030309020102030f0d1a060406080c18060a03090303 76
    0x240d00743c1d112286800c220b0f60000c60809040b80c843d50820b040031a008108802c81c0c01c0b104824820b07101c00c4442621a1000020044202c903008800d503040582d1031802440c484c50f044d2400750100040410070424180c6425010788502c00c1d00051500101004000b1511161a40540ca59650110b051040d107e01e92101140d0301350b0003203203414421a4580e6640d80f0b103a0030803050146515602142c03d0511040c000180e0000e07a0600c0b990008a028002902841049005080c00c0d101c1907441070341844075450f41031151081d050f04441c207540c0d82c1c282240c640c6900002255440324180d00c0258443c02c8035030401320108054200f2003001b9402c0f1014041041140100040040e19108260303225180000ca200001d0180d0808500f450050060b0b0b8100a00000d81d00b600750300200625030400d07074400b40100f20759201c1d82c000c1e402e0101601c0c007908290901501904158000d009041e020074082001c0c40d104118885c5a050900d0252090b0b44400c1e00381c3c00a000741c07001d90030880100e801e0030074 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 764091276 1250 764090026 764090053
    0xd020303090f010501080a1502040b040308091519031503050712050f1209011d09011706010e040206030615160303020a03051b090d030c0618031b05120a03020705100e 73
    0x213a41d0582d5a1440542140c0d9030a68030f02c00d80c200c001810120064007440300186050b05a400b900086020341901643d860705401000340200d940700c0704189001c030611071042c1c610603a203c1d503a1121110301b00000c1e00d40c06a2220b01d1100b181d0340c001080d030311402001180282c14040215901445403040b60302c12003000800503280c0042c50b03000d80860800f1b1100c1040d07980f01d4072040300c03080c407504c0b901540d5043c42004290442800d800505002c80c030040e041c590307102c041210b21300400709091402042e04060f8001040c0e444085d00d00b911440e00006601c107082000e4003143c80c1d4600554031614036032454038014000c1c0d0409401c81e4042840c01c0001801141200b03051001c0c1100c1a888034501001ea10030441400558482941003103072152003d00005d00d2803007641480030341003006110410061034004d140b210640c0c0c1d0700345002c003010042000600001514142d000c3c0c50080c60f5101c0e451a0f504400900407030101034503510410040c4280703a9099070013000c4000d0803000351009844000c8 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 764092526 1250 764091276 764091281
    0x705150106030c120504060e070807061211090f060412260306030a0b070e0402130e010f030c03060b280810020715020a0905060414210615120d020303090f01 69
    0xc91401040841c07003801c00104055000c80d46c814458180021003c0218014038039002003a00300c0400c90f4800c42d000c2c0226600280002c11041130200c042c8010044448040b0380f601a43c5425401750f0f01d162102401a81c681c41a03501601c1c540348840c500b580c050800030b45006007a990420034811102801041c480c142040b01d2082c1c0010300204422803660703a43c01a9030f1002080082003109902941800d65900e0008202c1820300410701d500321424034142411028040c3d000004005e528101040095541450322048030f8000c98005402a5003a01049002c0b0100c5824400c441e030221003075040100c1408810140c5400c0411100002c50807140d060491040d440003500c0300c002c2040f0021030821540040c11070f20b18a2030300c2d40405554401003074458006400c803140c010281c03020700f0b07154140b0161007008c0000c102e8100003a45424800652103440141c6060700142c040c2511580d1604c403a003100412580d454200c90f026100c03401e0082d240c1d0401d40e0b00c60001d00604031035030050701c0c050 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 764093776 1250 764092526 764092541
    0x1302040f0c080f07090b0a2105040321020f0708030a0c1b02040b06040b041503050903180d020411030108010e0f06010e0105010f03060b0a080402010e0301050c0a1b08070515010603 79
    0x50b142c50103141c0b02c000d941e00340c0314001000a0100301c24202c01182400c072403405170072080c03c41d4954554003a91501000c01000805540000180c5880204400b0903404000e0041540c0c2d10700d80d49040c007070b40300810070180c0303d0103100000824000441c8000c101d0703450002c40c0f05012204081000c008030410840d25000710071200e00b440400260340034007504d0300d03610a8000c0400107002a14040d41e441c0d100b4196005503025a486100c0d800300d00720a15098003440745d2000445020703510340a1244043e1070038419000015009010f20a0400c085403140d41c82160b04072030800504d40c5175a503818000b07010b414110005030740f40c01107082c0049041400200c16059481c5404020401c0e800d041c0115808415940306008260b154000081c107004030034000d112403801031b0380304034144c501030001522140e048001c0d107010b40e140404000560440b802652802c0074145404500705400e0f80380c11000805103040a0f20050000940c00d041003070006c1c24a1042407030140c0110a80c2c2d945034180c00300c8180c0c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 764095026 1250 764093776 764093801
    0x711030106300c051e03010504030c03020d050a140d0f0e010b19080309090c0f0703020a030e190501110c0303030108160e04120302030c1207124a03031302040f 70
    0x201d08140060329000b02c1c0741a94041c441c3c8a26910844517000900352a01943c05a0101705815004418140d060080c000820010b051407460301c941c6010050102d244101a100010004100210301d88015000100c410981c1401802400c1094845500815444030f8403442440148200900640041e4040084850036800f5608242c4810140581d0301e000a00ca01003801041003030107032407400300c03002d0f20a65002e640245820f41c510325019100d074001e101003a1152070410900d010740b110405001056038020f1800c10030440c0c1c603840e03132407800d81c82804681d03141c00301200214000d44002034416918641041607080b09030759107100240d8804c00d070342c044c249031040317900107220500980045800c29041100c1c1403908420483e910309160080d55044001aa03800125100b0182406203210b080c03010450180304a0221034002e0001c2d0711440d62013807032245019103898160640c004400d100c1402021b490fa030380741007041c1e4100c821140e00200c0c0710310315000c80c0e00d50401c8a4814400003038507 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 764096276 1250 764095026 764095043
    0x30e0f070504050702031b0102090f0909101508150901060501030c1202030c0702151e0412030c060e011b02010e0a02090408030a270b09010b090705071103010630 71
    0x10710080c0000741c50018155025844104408081e0001c00840400161003100005072140204c1040010010307540d14900e1140b000c0740300340020300c240440c00c03050180d8080d0300013800c04050407010060407015404168180a01b040400030701c45800c055511400d07100c402048a079460b18015821108103064160001d183c03500907040c503d0700c80e0300541c1c02004801c2040d04200c450b034002080da0042d058590201038010448501c4050034540c032841c9035010030a100d040c203050a0360150010240c4401800700590442c0c50000e01500c1d600c00703403030141100000c0c05a0a150304200c0c0c1051070041c00100190b2a001a459081c200032449102040c1c5c020081640c07030315552100042d0f9040600100003590387d42807001d101da01c41e900d400c8942031680700d04000e0795140f070030700d219800320050000c1c1459040040c0642d0300d9681e1010340c1d0780858a0b04003181c407008a03041a1482c1106c00d40319941561900d030000c0340d43e1610300c8624084049400c484224a151103007440030500c403c3d040200342c000b = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 764097526 1250 764096276 764096279
    0x40b10090617070c14120d0b0913020625060504050105041b0605090915091603140f040624080c0a0915090b030a1505010801140403080610111c030e0f07 67
    0x30314280740b80d8114102407044442c4400e002c1b5a6000c0b6600011000640e150340d07030607210705810001c062981c0880c882620000324160f40d004124248503845055490642096070008581003032041a01450303003040042000b807410b4036056001380700a80b0705846400d1200c1d4882c03000c0c042c0048010075501c1d16560103042c00541424040d5508016102440403100a841002c0c1d0392070f5a6007192190080e04040c2040d41d10901026044400c8501400144080301003000080d04814402640060b8440c10000e03040c402403412004081c448040e03e4030008500703000003601d020004020b060200110381440071195240c1d8030000f00c40801944903004581290100000004c80d40020031130840a01660100d090640c1c400d83e60f00100b4010540c8199240d0041c012001d00344642c1c0680c01c5604e80c0d145c0ca50910b52806420301c0c03001883c003407050307412504202215116020640003181004101ca081500d1386035000f40e00100c4020000001e4541030090180c10f03c0054102c3c40d81071913401414585 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 764098776 1250 764097526 764097533
    0xf021e06060901320a0b07110901060c030221040806040501020403060515010e010c060213080106031707020d0803091c0e0f011e080c0c031303122309040b10090617070c 74
    0x1c070f80c4c40f01c620750148003080b00007140291807005201d15480790000e4004071021804100300400d0681144040140044001d00082c0c0c00003a810010460107101600d4181c1c00d2204840c03610541c0c00001050056a0612003007041c150050800d480c415a414849607a420100c40c460700d042051260005034801519070003540100041c0d090280035980141c5130424000d0100210802a84000c4203690749000c20000d00010f01401400c890310030015615040407900021000d01c0801009803864a002002c1002d2a40400411000e8142841c070320081404444c1c024200c08036064146024110b6610049c0d4598420101600d00303494084080c0c64600d60b41c5021143e03440c1c010310301c4075003210800c4a0496200100007402c0c115000702a017030341e6103003180344c8503019020380250b0348244164224110300d2408285070403569510b600d42050345039822000001e001c0c0c440e054842e600484206903105841d684941c1100030f403019511048044071100220101881040711040c001039825000030000 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 764100026 1250 764098776 764098859
    0x1806061b0f030215070906180b03071803021306090e01140114030717060403090b09010e0f0103450807021011030d1b18060f021e06060901 61
    0x64043d02c1241c90481e046580f1106600d0140c4000012481400007005000e80c0300e00288040000c0d05000d03507105d4a001d010021030b0101400520500501c20100140351030041010780003540c00030240e00d01c142d03801540c1c178000c048078080c64800905103d002d000b9044140689040340180e43c649140680ca0000c4403d0650b481c00441d0b903040c0034404002541d9112071042042d40b002c180090704031410640f9001c1d011640c1c962207a800502c0c144100d8080746e03000f12058032082001d450141c5218405c40049004011000c02c2c0c10a074030040c5418415442c41c48816002c0b122114000c840300305054030031240c60404641d000708540010010400113041c00b0708452a40d0009080c203e115004c644426825900880342c00c4d000d80d41d403501e0610401c0f003000e4180b00203215030f0030902c148060300d015084000d034040c064101406059010401c10038801c000007440b003094030703540001c00c0f803600b080e07152109402c0d0344d803a10403e42c92002148081500c1c0d03804111280d03c404001488440d020b07031025 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 764101276 1250 764100026 764100053
    0x516020a170d0608010516090e04080304060e0303070210060803120a0b040603020612100614190212130e060103110304060c0c0b04050c18010b041701020c0102041806061b 75
    0x107550900c645107054909000301d01c0508140d000100342c520f803125040841140b11414902000210700081000d8582081042d8100350410b400b60303603a54071382c10010058040d030116400c07a03100000800500c1640807660740c001500d42081484000d030342c1d43c040c581e280115035494034084a200042000d0403031951011221302070160000c035140da5240c0014510782c004020038800c0b85020000c008940b8801e40b051400b90602d81055011114181174044003405820342d0002d030348600d0030425051900800040710348443c40300005603500b12400d103e40c100080c5104041117044181d0200d00598001e006600301c10032280d1000742195140e40340c160107001c20515480038050301e02010004030794600c1040d44110b000d44c004000d1038601c00c080c0211500c4a03198200a501003000501a115000c4211802c0714907458901c0c104041002c2c0c924020321590210781520b604c0000c00017070015802c0011140c440307a0070320402100355203000560301603003411060700e164504200c0840004803416203851 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 764102526 1250 764101276 764101313
    0x470309100e030a110a030f1121071a070c081605190b06030a05030d0207050c060a0201060305160810020a03020706090c0807061704020d0f080307120516020a 69
    0x300e440400550300d400716031800d6030440403034100003a0140160381000034800c04061000040c403030020b440c0c40091072004803a031f41c04100480c0d06c0c48008840410008100e403c03506e418419a0903182e04444c0c10141d03c1564100c031442070036490f940c0c215a0300e10885200f0381c101e40319422040816a2180c0090780300c0b5050714035195003920f40002241041000b00c40c1c00f035440e40741024140e1942840c45c00c581d4014480780c4258081c1d500766000a1011003910640c43c500540540c403413045141144c100036000c2030a9801100115001005a0341500020100e90194090360002105d07059a640c00c0d0b0028000c0c2500742c1d0000b203051503d007150307074000c2c090003060b8a0700504005603541c40c2000d80340c0800080d42c29030125103007804503203401d010141c020145400c0a640603440300300c6115201070002d001038030400304c2d000d0501c00c0c0083c155001080c26440207000b0369134540160080c110b020040d4003958200d14180c0054590044801d4012511b0015002080c03400301a94545e0404503402043c80d = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 764103776 1250 764102526 764102533
    0x1203050a0c14070906080309010f03150b0706020714060c2a010f0c08070f08010315270501050112150b0307050a0e0f0a090f1202030f04470309 63
    0x12691982088848a1100000c1c100355032404c180101a901e41d07400c020701e00e400420004969a8110840800c0e061f202e0401117000d282c48801207115540356804414840400144401040902d90091540900c0344805e50810400b0134525540c4442c106c0719000d103d8001c0041403d511441d854544d012001c40b01c042ca480c2d401c00c42c000d0700b03465800103981003050b1110742c4109866002a0001d500105620744200400c28400c0002c141403810700c40607040190044107201c0c44400394011002c000341d800300000410b00c440eaa6600e940310160b000392155443d2400200720415038159001e034a0750005e1110500c590000f48410040c141c0ca0003480e03152040c56800591600c0da034403a00010301e05600d000c0035a140000002242d10300040001c0c0e42c4510703003155000007c221070044122a50090f06e00500c0929042d0180c1c0755200b501144018440d010800007018942180880840c551000d012900c4262400c40032880c92000c0040d00305040b0402502142d11031000040c59020041c00d048 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 764105026 1250 764103776 764103797
    0x80a0b0f0103080a18210b070806030c130b090118061401081602070503060a0e0c06090a03080f040b04030c140315010911070611092b060c050c01060e0114030105011203050a 76
    0x140c0700700c2036404107994007485031b2102c003105125802c6074440c3c1c040e0407418612030508c0e20000003501c170601c84032100c1c4a581150039066404039240c1c000f45000b0b50260111000e945c407000c000d403d44442d1000100380d1801c1a1022911100409002d190820182c441b4442d0346c507100d10303407044500401540000c62040e80000100c81e80c0130800e05006861006000810807444503950f41022000300040740100000c014030f6556480e0320a4070300c2201c0d081080940c4454a03e801d00d240c130312855022039030341140401d0100c180010f40e41d00c002115002450524441c44440a01d03880b01d04001401c102c8010b51001081480226081002c505800c049210b2038482140d8441080303861016a005180101107403402c0a414040e5108071888814040003109424141411030b070307403c90000c018140758640c0c03142c50400d4051030659844010010003400b84540314010b10384441d60074802d0b486554800e1002c07032010700341813080f41d0680c1c444030454a19041e840c0c40503142036102210900070040300b90381 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 764106276 1250 764105026 764105039
    0x405030705040b130f0b0f0a050d020103020c031308030901110a150203060a05060f031602060c030406020901091203230412080309031303030c12031e050604060906080a0b0f0103080a18 81
    0x80d0005080d44043c0000d4440001014000441e1050440034020341c023011080c045641c0f00030001c030701191b0920300507a4176520002d8650841c0142ca880c2500908030140215038005c0c01700151041503401e90b42e04500c80a410130040e5102400700c40070344010044074219504031450b07001580c2c810030190009c0d903034a0342c0c2c80104016900500c8603c0000c00d0120510814501d01e108420001009100404041c00e1061600c152444040d00090000c1c6c2e000494003026402084510300a211003c5680300d08003403405e01074030b402c0e0b454520451169601c1031103480d41500005641c16506120745408207174015907165840c562020700b402050748401c0c0031500d080340000300032001440c829524150700079041c0c41c0402c20148400301600c145410108401080302c000f80c101054002c1e15071000c07a094403400c01140c01489190802d00e4010706220b07020850100c001031000324584a00c43d500c4203a510040001c081c1607084c0001809003504100c06068035111305140103d40004401032010150b4407079 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 764107526 1250 764106276 764106281
    0x120609081615050a05041509020103060b030a0e0106091b0e0612040507181e09300e0a0509010e0714031302030d020109050619090b0c041a0405030705040b13 69
    0xd0040703860306006642c41d54a070009004031500b100212a0911140c240343d603c1106080d40b0b0b0101a0003075542c1d0803000156032180d040400104903c291241d038900b803c00d10701016020100360400b04d503007011000140500544105900703408003a00d5951031103601d80342280d0304400c140503994820400d00885540002c0d41100c940114402c900a01160785403011110386250760000e142c4105241880c0c10901089081d50103e440c40c1702c4500007885c140c94501784114002d01c1031040403d040b40080980800e18403804126182c64540b1007617916040304003049100c1000d8000d00f90044600c9004200d054030345040136420a405040c02142c008a0a024041980044400e05941040e4414000035070805000b0020002d116100900c284c02d42522810fa45d0b24003c0c0c0f0f00d039403041c15450030070600c1c941030340300e402c00e140d0004041501d82861400003003190828010351602001c0c0b943e2200030144501c040710203c0d68040c024005c0c1600e0401000000c00300400780a801002c82c0742214010300503072 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 764108776 1250 764107526 764107567
    0x305061602031c0b10020105070c020d05100c03020405031603080d0b01020f030c07210b01051c05011407090617130f02130606031b171003050a030905040f020412060908 74
    0x9400000f132000400c2d0800500703004101c202c07000d40e45030005021900343c0c806417602003990152400715007503606291546c6031858074074007541514030742310f0b440b00e4080e4982c0060040350811422245948202900450b07000942e200c000e0664070100001c0402403402d402001c400c48050050744c00045440910b1400e5038070032609100242c001e004d040c454586c0c0340004590980c440d00326081c0076a115501c0b001c00800600a10b8401c4040e0f01c500c800c0181d01004250071960701c00d009100c0503040d0b440a1a0f01c09080d0f0705040411422000800c9091007449086407044660003075803c0c80c0c891f1507401c01e0010000300d0075984004218070413005600c6001c11218070300144100025000e1400000900300c92803180400744600408540e00c05040c1e01001800c24040101d0100466840e44c1019049100642d88010480d02540140741e09042d0072512140031030b00c0944080c0155820300f90103100700d104a002e002c82c000e6040031508003203450740d800302c00c065104080b40e03807030008100a00900b00c03110 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 764110026 1250 764108776 764108827
    0x170f0a06030206040f2918150d06030c24030c021002040312020609160e0c0910020601030b100609140a170127030c0215090a0905040615030506160203 66
    0xc03070404001c4007000038010051100c146c6000102d01c10641c14104d0389104501444152401c14007564203150303684401842d0424a1141c04c0350f03905a101560b20290500b84400e80fa02e2143c00700018491010300034001c880c040a22140c40d50200b0f80e00294020704071440709204520402a048507200314900c001c101560080400750104024403100926180b0018441ca0554201c515020040c4010440351b40035591404402d101543d540c0403004030328014105010b42c0140c45548090080c0d03004580c0c1070581c4d01456070441d0030b03a50704201003c070142d148182d400140c0c0c462003c2261900c2007080c0c141d1a0070081940c0c11850b500ca80c80c0100d41030381d40030004140d641d004101c0d0750814000d0381064100702611403200c1c18404c1d803005046d2655002000c4c0c021494001540d2802070a0000c4564061001704040c220b15200c0030160006c080464040725018549011980e191004a10f9002126031140050046640d00c822609040d03030b0001c4a4025803001b40000b00c40d2107588000381805940 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 764111276 1250 764110026 764110049
    0x1c080f0a050c01110d05091f0209030c0604030807020108010f05060d09060f0c021f050408090108060d06020a020601050909031206041503020d050c010921061a0904150b01170f0a0603020604 83
    0x203000101c408564002c0c2500400343d0007108d0340c5101407445c441000003540d481c400140c48172041c002190505d18210582c0394030030b0000a001c010840614090040030b4001e0340c2d0000c0036a2101c0700071034110507500601d42c1c4440c0c103104810030280306403c440c41d0603100f2030f40440c40581c034001c00001d035880040c540e0301581100c24030350a03400c0c04e420180300c00d00074200180280c0c1040e4440e0380d814403400311030904000800300003502684581c420341b01c1207a07106108541d0b034000301c00001d449110a00500f849084510080b072a2450004256082e440c1c100855101645901042100500a4405002a06408032000405681c502900301000c50154000d440c021310701e60001800e60134280c0007141100c01a0034685007aa007102844600d80307510560018843c1002c4201004c95149160030390b40c03001c00f040400042040440c580c08124004140070300502c0e01000054403860780341203265070590302d240000380a81c0c1c1c00b48030040d040526224002a05520f80c3c000c03481552040d0440da95844 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 764112526 1250 764111276 764111287
    0x204020d06060f051612020f0604050c130603151d1e010b09090604030c03090e011e08060717180111070b1608060d170d06051c080f0a050c0111 63
    0x240c01c601c00c07883d0364a640c0307041e6140c60055001d41001440141001e41011910303484c0b00003490003041141c8201d480e100c221001443c0c103240c00d03a5500072100b8a5801b5400020382c1b060002c50707602900003544e0340100a100408000d034580d50050003c8405c002c421342c244c2d41c2c118a024001e000d16000c4100700002c100b182009214144d00f905e84800c100b50007107800b00c00b00017491a02091040d0031581c9454051003400d040d090843c0c2880468015055049c808000010000c5441c1502d5004240d07002410400e5503682c4d1005440341d60469001000c12800c080c108503002c81003500550094580e0300ba07000c0e951900c1107590071502403100703d190300000003410100780a09c4983c079543c41211140ca160311001d01c850005c086c110f0113040b840c01754501c014044200000c60300340400c540d42c0c00603515240d070040ea1509015000510620340160507802e04007021500401000300120307000038001c1e00e040000c00c00d00c00070b0b9102c108203e0401806000d1240e810360280120300c20443d0041c0c5064072103 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 764113776 1250 764112526 764112539
    0x3030305010518070c150c0c02180c0a0509060d0603050c12060103020f0405060103020721030e0303010e040201110a290601050c060c1602130501030302010e240a090204020d06 77
    0x1980181c0050b481010f002816500d07100824041c60ba010f48030385003045a4890b80d2030424103241c00c1404a40070a4240703402290000d034051385213401c1c180202c60b1003000c013540c8880300c030310b0500582c3c00d0703200104200500000140100c000300100000641030600c0c0205200c10301c2e003101d04a0b0412203054001c0301c0764810320b19000c92031150030706521020305010b5145d54000344440c50004845401181c0740c000140c03c0703030301030790680d01d00680000409660248080b122080410343e056428080791922018071810349001050301c0c144c5412140c0c0140c140c0703641d00151254818503195042c60301c0f074140c0c4400007035140507062100d801a804500c4010300b2001054150031001410281009000d0007440c40d603401c0042c252b03810103410912195030364881c1c0d80343d0550701006500030317420544103281c041d141c0c0210750105040306d0103a4000c00014004188143d1501002031100315454100c46e10103a4880f06120b125403c072260725000a1004040c0e40450140c1e00403c072001c10307540d51010100324a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 764115026 1250 764113776 764113781
    0xc040b061216031b050301060c0f020301180b090a02011d2407170903030307181a0d06060206070203070605091e01140702071206050a14040f050706020c0a17071707030303 75
    0x8040c0b02054803105036000d000085c880c1c00b0500c203010400a01c40a00c8007032040e02c0c00e00d030112a40180082c05002a002d80e6248211030900c07044032038061701070029030510f201007820b00200703a059495400c0361180522505034100e002040c268480c0c2c98107101c10b100c01106154819440c4949103494036050307a400c040e0001c08840108084401c0c040018440c0307913a012080703c8d80000c941c1000e600354a0b49400c40d0f0041c12080d005040740c6001c174404000961032450281040a007600c0081c040281c442504a8907903d055421b900540e100b2301000c400102546c00c5568131410b58000c43c0c1550034000303ca00b003100401075401c28540d5480103442400d0b19270301440d913803020190004004461130072401d002a561003000140c42e5503540c00105041601c00d800990110550040700e0300c142c00c00b0708210381c292098003c1140e4520030b96400090840c00400c249440f0740c070050000040c1c030b10746503442d416824107115103603082c042c0240210b0150300103802d01d04c03404103100052440307c1c21071902404 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 764116276 1250 764115026 764115041
    0x2071a07020a0b1608190609290a031a191401051819090510050a050f010e060d02010c0302150f01061d100c1b030501090c0b0c0c040b06121603 63
    0x715150010071484040c5e411001d041e0704001e40521544210480c0b00500c0010403d54000c5000d05041101154030402c40c40000d0340ba600301c2010540603074450070204010b0b0126480000c003d40042800e1803030107414648959440240c49042100d0400c00180c41001c460429212580c0d154000c0014025410448070036400d0754541038402d01720703052046542d41c0710103140000d01000c80c0c40c0d85480c001c01c8800d00031107a200c1d8942c0414810ba04100d14648081c040860700704840c0b001c8240001901ca6101100c02e0260304082c0441c1d00615194004459902210005805511407452158030310076803001d10710b01c10703050a03001c1c2159505201d0000e1a43c00c14905140c2c2d035120032020301145a45000c0f540c01c441c4000e003851021541e0074a04816901e849042450285419130000003c0c0503041d004107a00c544110052005d0310389901d01400180201600501c2c103501484154001d82041d5020030000c920080c1301904140c1d03050084e440325a4115000d00c030000446040389003882c0c2600400c0e5 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 764117526 1250 764116276 764116291
    0xa0c080403150b09091c020a150516021605060906040e040f02240d1a0d080403030306050108011d041e0309091a010804260f0c060a061802071a07020a0b 67
    0x404c00d00f04507041c03c0c0e580c05c2c02200c86409802030701040113028001c0005150345980030440b2112088103003418002041d044414800c5000500e40c200c00b807903c007045842410030142400d603503060401042c001d464004070180f68000e2020030000c070700802c101c41d6040c440e80c80742e041800403d01303520602c130082002c081203684950b144401c1d070b407070448120140c4401259110000071004e203064a041d180c5c0140d164001d130002c55005000c020300c84400c0092069038081c0c0c030140100e0340d0f54001111452424404c0341221502c070f4107500e1500e00115201d40c3c001e402010540b0340d8454000c10849085a0441c04601040340a6801c00a030034450054508a07075203c8501e111142034900060005003008000510440411004000002c060b00c0c071034070a040d40203d0503491b014036801800b00c540c001d06841420340708d100d0008050a10380d004940980350240c075690358241910780350310069000210112280082142078200d062061160301d440303610300394020500c045103420920039510307019015070f = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 764118776 1250 764117526 764117539
    0x120d0609050406021c180f0c09050403091505040e1305010e030f13051e12120301090504150b0f19031a07080901090206120403120c0908011d0c060a0c080403150b 71
    0x104103c030301c2400e4080c403640000300304d95601405d1402203100c4234980c110740e640528102c00c0c081455403005440c0181c803003100e0f4a0900d64410502513485d0b01445c0310b00b803440341d040300009410781a80c2d00c044003224400c0c40003050818130f010501e81150080d07480820f0b200008120b180250124120901c0244015a00c90f484a040480c003251891000f402041c0202d084903203800370381004004d15400c1c1c101c141e1529449503125000318000d8001520160740102645c1190000d580041c440d20f0081400203000980b80c440c3e005c103100e0b5001c5440e40c20b016080000c1000004200300c50340312140c8926007144282d181c980004c015100020103015000160326002da51001a1111001c0759000d403034940e2220314a0396140350881d44c90540c0845200d07800c1c202000442c405400030907000c00e0f00c0c60398000303000b05410998842e844d0725074440042c0c0c1582c0700400c24091810100000c04100700c0d20301d400d0232054500d07252141c059000c1d41c01228406070b00080c205c0040600c2c40b8100b465039044400 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 764120026 1250 764118776 764118791
    0x20d0c1101111314060d060605030402130e06010e101a130803070308190e030703020d0806030c15030c04050303070c0f090b03060a0b2d0a120302120d0609050406021c 73
    0x1121543c440b402608a0441025070100305995418250b0301101514072051043e1505c0b501d005140350016241240181030100200d21585418050304c00d01c90380100003020030341c1c45c04038102041c0c6030140909000c02d9040300041445401120702144401100905680d549003c00529980805561298405400501001c40001e92080d0b04d16041343c0e4010310740c034080107038124a800030485802011014840055903804140d00400d4040c810207254403800880d5440409040c0c070340c001ea441d9641d200440b204080c0407281c807900590f0b00300b00080821420251124003007072441c1c0c0801f8094a4991030300208220200da031400200140c4807511040c0b00e410724000100ea510880907000d4007406494064040c0c141d280e41c003412104003c2503800c20a00500180d45136102000400032500503c10b180010171100048202e040f109507144c0d00600d00d01c00301d04841c0285401a0801400164030780c000000d4000c05030080900950141400513034850b10400c10311108000501024007040c1007440 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 764121276 1250 764120026 764120047
    0x181202030310090c050f0304030c140c03031b0a051509010b060a0905010e0f150a1103030702030415110d0e031e0613141207050631020301020d0c110111 67
    0x101c4500f2140c40b8040402e5042c4050303415601c81c0203048401d03890070804001c03c0306255002211040300e0340560201b0b9160640d150440e6100c921a9801c103406901c1080613409207400e540510b00031100d45410b40b41a40301c03075603c403406c04418200b20000d04640310b0a104003a4401e204403090f5400c11200145815400c0c2005000c480d00c0344074860600c074003000d038208184c4598140881050004102600c104002782480030f10b0381014105034000b81c162821075030030309000001c5a0140d04980c0080d400d0038680017003101c0d100196203030344d020861085001151800d08110054864030f80380c0701e8a142502090070f062030700b00c403050b004548034100e07120801c540c080403980e581c0040c51551007501e940398034140032031041015a2199040d10610300f13002d82d0301a2030000b8200d150b00c60010785600351540301e0560541c43c80f042a400c00040081015204030f01c030060300d408000d1000d400035007003107060013603e01154140c2c0040c1c0085803060700313034044c060b1080c0304603c0c1d03c00c09001d1250502000c40b9 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 764122526 1250 764121276 764121301
    0x1602070509070c062a0e01090b09091902030f2401080109020307020313080c01030c08250c140c09011d060f030102070803090d0801050a06051606020405041812020303 73
    0x101502c0a0102d9900c2007014008250000082c1c540c500c0840349048001c0704440d200d03907018501e00c0c40040d0104d685400558440d08403081121040242c09041603251b00800c01d40301005007072040b040705014507c0690f52041e001071071145000c241418240e01c1c5c19402085481418020011070300702c0d00801401c01d80e0012092415100090001030301c03641d43d810164a54841c00040000428490130300040d41c0d9030000340b0070030030102030360148010300d0020ba06880b861030a4a5041007002528031603c0b406000e51000386580b00c10740b0300088000d00d142c94440c1140100e0695141581024054551a0401d9108180140740204a94007452217031103800b00e03084400b0b40380c68403030039082c40c4507405950250141e0b04590782101000c2d50306e0508407091381e40c89601c5c2c2e00240100e110480000b80398901411a0012911289c44592614000c40b418a014481c40d980c111081d990074080803409885510840e120310407111003041c03040446043c80c1441d19100c5414504560040040240081581 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 764123776 1250 764122526 764122531
    0xc0b041806231216030510020406120b03150c030406140709050f180108030a08100e070509150301090e160f0e090a0605070c291902090a0303081602070509 68
    0x115220b10b011a0014005a0310300c60b9043c030603080d80320710345003248120714124013030088900c24011100003d040d164028140d010318030607000442c060380b01e5070100300c040390001c08510f40011306444400144580b0305658500c20340345411059004802c00040100b13030720a0303165840800280c40b0051400e8a1700030070002c014041c0038095403140140107100d031100b01210440020b10100c00d80d040d07840300361803550b0f07410450f900400034032840302013000905034145000942c2c800441c030344803c3e0f440a00568407136018008480d0001950105d0140240c4420302071800f0302110880801c08161040300c0b941b51803040450325140ca030a00c070701000303124080f407514011546581c2a03100c035642c910755282c1c1452191039019107803600302010881c055500403920540c042c4a000f000c881030648048290b54008482c1540c0300c0c40c2a0b4002080c504002245d40c2c03e001c00b43e045001d0b1070042c02c8004190072510036841140400c0c00300080c805c28001c5840303840c01e0302d20301d480100400740c5840001802654007 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 764125026 1250 764123776 764123819
    0x111c0b0a050f150d140709120b04080f09030a0302100c090e0f070c15050610110c06032a130806070c080f04080109030f030c0207050d12020a0c0b041806 67
    0x1540340740940090f000da440d104040e00c410055402c104100071468901128542c00181e00c0004c04901404100d110f0049540c010036200c106036900d0703551462590002012254148040c091032400b66020403030f60324082c1c800c1c3d014200c1e42d06101d0b9554207550814100e1000c0c401858014031000301c1a81c0050b03400708600e1004441600c41c2c4074281e44166100d103014102580303480380030a50410a8220602500040d20011030420f80f90350105e9000c00014030000a50b08544901c041c00d10b090006190030200c050050303615003207215002d03a41d10141841d0304004400115002103a01516011240240f00400140c1000d20b40032000520811440d000142036100c00f041d09941c0c207100d00e05131f030050b01d85031001304030030881801c002e0644501055210006801c00ca0203241a510104402080700d03006010380c405840170755a1240343c200d001c6401130031441414a80c0c0089190511302c0c1004140c0c051380c0955460070704845a4400019000e1141c01707d0504400b0003124840d145113400d0001e8 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 764126276 1250 764125026 764125039
    0x40905030d090f021302042c04200307090b13060e0a20030f060f0f030d3218030a0b07050903070810150f0302030d1101111c0b0a050f 59
    0x2c00346441074010780d40c200c000e50000000d603200c040c0e044059009006950441c8420190030001500507482202c0c1d4580e007080110713928000c207001442d10315164200320a0f03040509050851503001c0b034030b03126881e4040d4034426200c442201507428100c8280031601181c000620186081c0226039a500070050010004680da60714891031502005c50720441852100d1040381c1e0380e050036410781100b000300395051803044121903003148062808180f407102d0070360040c01074800d00604401c00e4408556600038541640345080d00001003404141807410b0640b01e032070100d5100d00c2070b4090718000070039240c40c0c02e00a901002d502408200c69903222540030702c4500c1c003540d5902044012a00b00f102c15880102284184040320140d0f0303074181c0080c6200982990a140000d60319a10803070905002e120103901a081420908802403083e9100f020300528000042034481c92801c0a00b03483d80a45003c190140f65101da4071158085806102800082150400e40603802c0c180016007040310980003d00ca0300 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 764127526 1250 764126276 764126291
    0xb03040c0b0a0201022203051504020915120d030608250e070c02030f0c011103131e0e070519020c151b0102161101020703080d02130b0a120b040905030d 67
    0x103100750102c1e0800b50980e0301908541c2001941b000c00c41c81c0e6400221060300032410074100703500010407140c1c4100c3e0001c203001282d4a1ba1181f02400c04241481190000350284907240395610422047c00b419403543c2e40064694030f000036190404007021511b408140d4150006004c9503003031000c50064404000d201c041c5500c034810181c800b40703607611000790180039500041e11210070208000c0103083e003e0b03c079140c100302c07100403094407449074800d10700c1001070185040c403207080902e200c41c5840400307c20407040746883d401d0309682ea00c402c65240000450001300c03d442891500901844500140001d04009445000040400d00c40ca5000d81542c4004241440ea5030000307008540308003058802159681030260b150800100f6080c829510512000390400047d440040d00e1002c40343c004030355500b014481034000001e544031190320380c41d0b40848000401d4400700b440040c16041082d41b50b200c20b002e4000324407001d40361422122481103141100c0c440104502008940c940c84203640002803a8 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 764128776 1250 764127526 764127547
    0x7080a110a330e01050106140a2c09090a061802030c0909070f06091406120c0c0a14010e011d0c060c0102040e0129071505041115070c0b03040c0b 64
    0x40c511008003241900f451030f03030707050312006500c114140c4000b5034560f001d55422004014591003449101c0c0c0026240402c0410001c2c3c1c021100f032142c4407034030b01c5508502500400074110b6001038500b543c403078204441200030071000307100700f40c058440c00306900b205206a400007a00c41c0858011a4000c19034400010704401d014050300c405000b107002000301c86c6443d141e00400307000c201c0c000d59000c0d40720052400201d15041e020f950203400500b11561a560b500c088402e01904000380c118818400c241900000a03c3d0081400120000b080001030028100101070b0170354040002d424520701d0f140540004610000c24890803047c016035030169030b0b10f0aa404c4500a01c510ba22180e080f690302d90000c100e03e04082503050a214410005040481c0c640310b0f075022500c00e00f00010000d403841000c0e456048259008039038054050320100050000c0038010804400c10301c0d0402e00031080000e00d5a0070030202144841c09007180410950451801d6900c54000408c54058116284808114070100 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 764130026 1250 764128776 764128853
    0x18050414160314100e01051203040501050a030f110901080a050c090f01090e0108060405160f030210031503031e09030203102a0903030809010506030c0f010e0607080a110a 75
    0xa002c0407000d00401d070304e041c407901030704184d2501800015100507000003541d8a08001440c20130b8920001462409142100540b19680810140d4003410740b42d03442d590400d8003502c10616000348402c00796982c0c0b034400c00018510600141031035042440c1c0002e0041c81e5a4403010381e905c110094426210b03d4920000603208854589c2c00201682002400841e00d0720b80403072200d000f18490412148182c0b01000342801215107406038210060030100d00300f0140c6003421007041041d0300e901740090440620305122011038525001980032501104105020138414002c9400c1d4140314900316208608560000c0d40321030074202c510440707607258403440d0500c102d0f00010000c4002d0300d410700d400c02010a1070180207890544070940100741034000094982c1018001c9a200310001005800c1442080040003841b002422420b410054014a54101c40c0c0300c1600030001c1c1c3d809a540c0503220441140010080d062000c840780342904907144080028010000340450415410050b0003e02d0440d043d42c0c01 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 764131276 1250 764130026 764130041
    0xe0a020c010f0b041401030f0b0a020706020d05040203070b041d09010204120302100c030c05030a0e03090a0611101e0203090a06021602090c0a05070b0c0f0406180504141603 76
    0x4607518007400d0b545402da4a40c003001d407007403040d5014000b428018405480c0003000b4400030342460101210080012454007501e54007030180d0500504000c4561100301c2282c10404003510842c0d40c4a041c04150301c1c5c01c001c4480146070b141c804900c0c0c00e04103181012105d90244590707070041050000b0840703950080d01524041c015040c14503900c04c2d41401d0003560b51410843c030310070130b41c544161852014424021003d155131030741c5a00d0301d55140d0000140080652a5113105140020701000c0d00e550b903130303802d0703d4000d003500e41d580321241c06461041828001d1714203d0403080e0b46800c032501c90403070010a0700c402410128000607140e41d601503405040542c0b401d8000c00107840024401e018603444803d010a8038001d48441d0081c0d0f40e02034040030170744110041e12010072424010307000083d9018007880da2100c04028514106090707803c0b405001c0d0000d4000301e02054104641d4a6089450700d0300350010315080305d040c40a10030800011026200c05044c500841c0450690790106034002d402141 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 764132526 1250 764131276 764131297
    0xb0d0519020c030d050f2502010f0615090b090906151e0c061503120703090302060d09051c0903030f020c09040c05040b090f06040b24040501030b01020a03090e0a02 72
    0x1542c402c190030100d0703225400392040070440b6103041c0c04580300c0b0306501030307181c8589483c0c1030000b80c0c4001c400c0c6101d4045e01a146a108541d21501003802164060080100414054518a0720b00e05000006481180e46030020302d1200c2007801000d50300c0d615510802c0d000301d4141ca0421030a01030748158017641c0b0900030380300b0b000b060030040b0070100301c4444001c208510f041030a0f83e5250711759030784000c03040c4444200d4591541c003194099558180305002418002d20a0601c052010f5482d80490368070381104100e0805540e881442e10103104040c0040c4480d00074444400e400f0300341001024020311801c3c000502044241d003240d0034441d008210b0782040c0000141141c2d620320b0039252034803200010b401218003d90400c241c4181d1420140c06440c0944588001035031180e42d100b0a00001f400348842c0f007a480004644070501c00c10f100c1050082d071403107401ca83c580d01d07401e100024054074cd006008504550203a01c01302d0129031700a0400c4140c40c0484c1c0e4180d41c035101c080942000c1e025100940 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 764133776 1250 764132526 764132531
    0x100806010e01111b0604090c08010302121b190905010305061e13030807030e010f0605132901020a0f051c09060c421406060301090e03190206040c08070b0d0519 70
    0x151223140d000580c030350480e8822516081031190055005403202000d04601704182030300c6c0c0c00c01e10341d45480039155980c59240006411020b40e10031040d8141c45080e031064509411080034030444c4403007c0d03880220380020010000d140e06120701c41032000241e1240c041d003085500f001088450780f00c0d8120041d0500220b000340301122901403500e00920b52880360500c6654100001021800e490044640b0780140c075400406490a0001c2038608400300c40c410340c1103008400b4130b980001c02c8215000c0b800c074081c41c0200441025000b002080e9250002d0300e07420f00150030002c21210364007860002c01254005094041031080e205810142c4506403408204010070180303144803001c1380c05000f1842807448000b4400241c0c0c2490101c20200c0581c0d8041e00a80200018480a40c0d2604045051650b142c21a441d08055565000140301c0007074442c001030300044280010300c00c1607a0f216000d4243d25020b8000d16140600400341c80c40b03400182e1260b15110000541d841c00701907402548200e02c40000d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 764135026 1250 764133776 764133791
    0x91104090b0a06080c0109061d0907080406050c03040f0f050109080307050a081012030513090204090614030607020309010f0e040501300b04061a100806010e01111b060409 75
    0x20703240e1081c1161070803440d500e440c6000503e41c400107085000ca90040c1c65444841303040000c2250325091141c1b4560a4241d025600101c035141c07220210700c1a022681c0710321280c10316141c01030036201c000d0b12032103000c9410300c01e00002c11405108080f1240d40400e1030541c10115180590150010075406407006c2800310400628035001001081c0b007069075a5451869a196510560941c9d1940141c60002c880000400d00103400341001380710020780c856448038025a00c11402c01603900941042c901079849040c100150740c40b02e560400c45450443c0501b100b0720f00450000e41d00d0107600001c604009010003840c0312180225401c256041d0007400a10081d0303110f505021042d00c103001e03514180c5d4070408810b032482841c1500c01d8440da5011841184076196502d40304e01600c0c601d007901254903900240c40c1341c1036a0721100c00218085a407a01589850b004002500c1e1001d260b1419040c010134a9518040050116000d60a0030703003e01c280010303004882c080b8103c0c3c01203800544485141004 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 764136276 1250 764135026 764135033
    0x31203090a0c06080612070e0604020a0203041a040e070503062808010f02031609080a0b1537050303040b0f0f210606251103100b0a1401021009110409 66
    0x409038850417040c1c41820000518101d46980e480c200e108900804084c04c0105840f850f00d03030001e00e0340c91041d00c1200d0900d0b0b00c80702c0c0c0c0c0b00d02c0d4003204412120240f0000701003143c07824051420340c0c000c95506201c0c0c19450440c0216505183c0909402081c40d01c0840d410301079101d644081000c2c1001500801221840e251980b009500c02d580c807071040d001030f038440302e2228810600d07002038600d280c0141000c0c2c01d01d50741e4180d00c44405048003406d0540800110340c2900e89085151800a00c40580f58000008820308120068000a882031003a00030500f4005030720004101c608654140e4519079640161003e1080d2030701420081d0408041700117810050b0b5009031403010000400034071540703040e4031641e0800906103c2c5640308034010003900a2020075400c0d00d8000c0340c01d1070180301c2999400441c000002d0401c00980f074010354166071218040500d08000c0d14003400380001107020400c0c40c90000001c0d694100c9010071542a98458105504025032200f1000c4410006441440000e04a15 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 764137526 1250 764136276 764136287
    0x308010f080106060c4806142205120601030b0f16110a060f06080f03071713120807141618060e070c05070f05031203090a0c06 56
    0x114004820950500c003060400040c4104000c81c2c18a8031207a9444141d61765800c09903603600e0f080b45590081c805440f007a0568080c0c104612a601d9a690310401034607296809240c81e035400441c200302e40c810452004039240e03000c40c0c990f0b40d04665165039000041920510321185500300580000706046a410300000005002d4141c134428650a5a070356541d13000240c079007004981705241451000c0850360340500070b0b20780c0040710403800191900346805880307020585940c070360724071003803a41c0700d02c1000824070500031800b100f003440016518009454039a022a00398112440120000001d0046031071150300203048010403e01e0b5100205e00940e0400004c6901f20005c20750390b00c030740560b40b201119008140461030342109007110603011700f8100c9030800300e03a0200888181ca03079960b071b002c5000b0007082d1000d403003401d8507a90b42040c014986000ea04040c0c0e681e01014902c6004041440155800b05040307a1aa000c0f4281039100e58070720880c04e2420066100151000080079008509598402e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 764138776 1250 764137526 764137529
    0x10b030f010b3c0301090b07091401020a050304031112010e0a0b0606072003030d05100f0f0b340614090304030803040b06060c060f092407121107030801 67
    0x40b1104842c02d584000c0081c488008a5121103d0522906007008072a101c0b0740840a08a8041c0002030540910741d540031890720156401d40c00700b1401e1401f01b151480c160b022020f0800300788007800c541c034207564886030340740550b00001b418800303500b0689002d03481d0f0061654418440000901440083c074071840d44030303010744006032582c132060000502d6604215040321030250340803c4007400c1c4807080d4a061108144034042c03581c507010401c5452607100d003d0140da0700500c000400080483c1c900015081c40007034a620500983c03100781790421a01001c10180d0320751741d61004031a80ea1001e10840070002c850248484000d60312440c8081003440210b501050750802400c0005250352101c283d29a9a170059120003880c82c4004c00004001a10080c0f0098100401411036400c0060b54000c3c82d082c010102c54502c991044081000ba054804002c40940c4c151101d494501c54010000c0c03802c02e001000b40b501043c8401d080c06860481002e5012440700a07028809685500c1c89141c0200700200a = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 764140026 1250 764138776 764138779
    0x240d03181502150702010b060f120106020109030f03050702031315030f180201030b0604050405160201050604050609130c0b0a050403050106091103190b030109062a02100e010b030f010b 81
    0xa040d8041050004800c10803006005034008150320003202100b0503035400b000b002c0724115521150030001d6030f2561800781160321011410580c80f10f20303024a5003450f140c1603104008681c1010507040c042600000310801c0c9151034a408103540d0356040050303107103100e1030318060317408800386a000420303c0c030103517200031141c50f03c1c0d4050002c440190022010741d694101031140c01d44803500c5100041d0b0003640508581d0f0710141c40c00303040681c0e4000003022100c0c22140340003210003924481c0b000c0390307080c80791f01d521107021a003c10040c24103402241c0c410800600e00c294100ca4610400305004805c8084401001107902a0381e5414000c04002c106070020b110445040d82130590202d000c0301d050041d6210384060380c080604581d00c031410155202c40d06107049848507543c012044043d1028020301c9401e901076a00130441c4514142c078202d0144520b0148000c4111140d10f60400950104e07040340001d07081c00002c512601c422094900401140007000d51510810075800010700064102c828040300 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 764141276 1250 764140026 764140067
    0x5030606010816180f030c1809050c0103110c0d032c15060112090c1404020c0a060b01020c090f09160e160c06090b180307030503240d03 60
    0x4034080155418842900c83e034510035482000b5076000c620840701144070550140c240b0445a42d00d030b0882602c0c03440340c0c0094583c030340c2c94442801140d200410200c3c00211300c0d90100110b40f01e42d114180c4804c501103841e8101902c0381003080b0071400c4030017552014402d400a0b22504080044090014080385e482e0100e48001c91041018200e0280b820007090007070a0080c24201205407a40c80300c600c0000d20150500201400540da9440d4520030f400d407a41c030421030304800d40d080c21503141c912802116014891801000f85c4500c450000c11100011a84264080380c001c100c2d00050b13080034800000b040d00403130104100b081c05603400c40c941b03010320007803170603101402e645030175511854225000e92400440f403400400c101d1501d407240740c0a0f180c2c032403601c010541d030182c0d5120305480d01d908095401c410301c0300070b104003c4080c0304942062075a4a0041d460f0450941d03000d400c80c080207003c1c2400b0206071a011201818888813242ca50310003c00c005a02031880c50f02404c0c0d0405900e0034000742a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 764142526 1250 764141276 764141281
    0x41d010e07060216120203030403080711090109020c0a02040f1e0501030212010513080a02012306010f2a020d0b0903030a0608070303050d0903030b0a08150c030f0105151e04050306 79
    0x2e0002c0b0b24190b00c4c01c102c0c80c80c240c0c0c040c01c00c2114030324420714179002c03a0140700070400000407075401c4001d403562b184240c1000403001c4000081040101060304000c482c1380c4100669580080c00249145a00e0740c10356000c1254008848490300900c00646050b0790004d820b8042c01e4517010551101d4140e92003201c9802d0340b0b5454a51160032558110b1711080060645401000490100005840c01c000c041c800400c3d0f5000104c09990015a01c4442140d01c071548000e1210320742e000070044851160503d0724180d140c412030b401b06100010034000300c400e4101e0610800554660754a9100c074540c1160040c05c0509000b20015901c2d817048030001d603102d180180c08100700c0c0c008200802201e4269607054100209030803040001c1100352401c03000d040c2d41c0c100e9008180c651882d02001003111401908440c2c00d10411101d03818801081d03089440d000304108170a05548080301415600140d65415010403550b0600c017040c414070009110360300515540c124501c21060040c000c1e40e81c01c0d03050f6142e58 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 764143776 1250 764142526 764142539
    0x908160e090a080406181703030f040f05030a032304051f06090606021f020c060606252a080d141324030209010f030c032a0305060a03150b041d010e07 66
    0x87c2081030200d00c0340d8100b0070204406105a0628640083c000c0f00e849211445544e54945903034410103848001c03a0700c3d260011000c0400014a0352251084c01e0105440c0ca07140e0b94a94480a540042020051004000600340a1240d0000000c2c06515200f00021a00c520300695a41b03045d43e11442c7d2030401a00d4007a06540d1030090b511592120802442e2036117400007049030f070390000482144c0b00314000f00030aa00081e8501c940396450300544840c003042c030011031603c00d00515103640000320940d40c08100110500013810520b9600c0c5480e01c150900610181c145280c4241e590200341c144000340d01051080b840070b1745030b8142030a01040207618485a0068040e03000307454a050100c1c240301d84600b40603010390045001c3c04210300c0d001a0307945418034003000d80342084414036840c2d01e000300342206194040c821141c0020044403c01c43c81d5286d6038604510381102c202c00708505486002d46d89a03500e41e1b0f00b024075007498a4280d441c004114000d4603000b4595640b241d20140301e0b811000402 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 764145026 1250 764143776 764143799
    0xb0619030305030402042a17100e0c0906071506080705010e1008061516120c15090c0e0705120c0f040b030615070506070908160e090a08040618 63
    0x11607034036440d100c0c29691182c00700402082c0c46441c107903d0f89204d00700502d0040d0745061419224140303031101d1008026411a0000104000308016a06400d0070020b00c102c810048890382c5c8110002c80c515603400e00000860000e002d4850b000b4040c40314840d21550690054010000351803100d000c84044071745e9440111800c140c0c8802040c0c0110350303c8640503035a80305581c05548840050030448600c88610801e050307903031110404040c00032105071214100100014419603581c0d035894850000501d90703c60715000980c19040003045030b518a40d0b80c04001000341d141004103c1e12003019003e1034017003c0601079a1110140b01007840c0310000080d2400c0021007941c40340003440301d005041905040f8070910350340c4013a00c0302c4da102c08401c8040b403e4460000081071541c0c85003003c0c0041d400c1440001d440004180c208901c036800603069040c80342d101080c48812a140b0700381245c1d90ba201d0007842814481d0002c000741c1240d10001d0041101900100790105005048089802c0d80e40d90b000d04144 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 764146276 1250 764145026 764145029
    0x61306020f0105011508070c050f0706030605060310060809070e0112141b010f030609050a0902310902041506050301140a0f0e040302120c0a02090903031006030e0a0f0b0619 76
    0x1400301800e0010246d02c03d5031640e503c41d0f000e0500754140340d07403034440341c1c5060300e100b5420611ba80715540c20301c101a454041c1030010442503031002e046041000401c0c0d0300c0d032740b24007a0008020392400002e45602c0100507000042503e0303183d5060b21b50b100c0d601d01452642c1e06c203003500c102d4070f1203940c8400180000b9000d0782d08094030713031007a075050b2443d0011110010040751040070142c49100c0814900c2c901c1c41068080e40b050303d0009505001c0780b0500c0002c410f008081e401516084941850800c88000320300c0d2002c20101d00015100424800600117100140302c0d58003001249e00041505a040001107041c0c0703100180ca00c1030071039090304018121900340244003a0b60700c0c0c02001c00014411031003c540080c07003801980c803600030b01c0f84511030982142c240000254410398400b0154109290a950030400d048051465450400f06100d900724040c80b54100301070303a840406a5106060160080301a8041d0114001841034100074104140c00d0f0b0f83d0a104900142d2022100c03001d8a29400 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 764147526 1250 764146276 764146289
    0x10e07140a08360a050c030a030206011a040305010906050709090b0616080405090412090b040501170405210d11070f060218040c1706040e0a0b090a02061306020f010501 74
    0x248070b0381c600c8003806628203004402c964800207984640103e9880c1600154000e0074140180010303805420800c0c60000c0e644802c90003030b00103044130b034082a07020450a06646081180038105100700c200001c0601c03803640b02901b15468107018204018958200781c0c0075401503520710318600d890380750020440c0c2104400301c0e40458104901c680f20301000840d01e40850261840c1c42c201039441e004030300b0b105400c6400b00d542c031340740c002001c0f810390300032000601802e8107442203400c15003440c0028054080b1000859a0140ba14000804000c001c000d03103610b151941c0d00e0030585905580c004030080e00626403140e2081d05190f40d0358264001501541c13074168006410049102081d20b540000707611a103070000310005180944855501c8078024170b03c20100710790f20050422140c01003d0040440a0540b038441c0d4205450004040800078a5141e02e9070403189420307070340d11902e050915207140080c0003500400c0c0468200d0803071054001400481e10103809481590301450000d600300c80c002d01411 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 764148776 1250 764147526 764147537
    0xf06080712151506080103050706140901030e07091d0c060f0f070c030c030b0f1503100c0201060306060906051806030a03080402121609060504090c0311011403010e07140a 75
    0x1007002c5907640040e20320410100038000b6003000d040c400802d00d00d42c1d030742041d004038040b68010070400008000080c000c041500d04086a10450302d60340c070080c843d40c1c11301d604040d220f000c800b160440a00001008024103d0100002542c20710031110720600411041c2c11406007012291040c24802c0c1140d0009040c0c0c2039480c5400d40c42404030919411840080d504121054408070008500700700000145000d10410f040903d407402c2c000408041c024030001c4515120314480415450000b041014600500300101d440b082165040740181440d0703002030821418184001741404850303000d84290307070042d6580b038105802e5440405003801d0642d40f10f90540d1201c5a940c0210340b040c0354480d0440d100800304520142e0001d4554940084500844078201c3c1000f01007003245000c0c42048020402038038140601300c400d488110f503c0000b840b010305507000030001000c440e0302c1651090401080201656103d507100e60501005d803600321000702c0800d8240c4450305c0c02003030780740c140d603000c00c0c50396a40c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 764150026 1250 764148776 764148809
    0x61a0310090908040320090112050c101716020708070605030f150d1202060115020a0809300d0503040819120608150c04060927020703030f060807 64
    0xb4100c0c0401034803084400d1101000151071403140c4640c20207905114078000c0551400c02140c02c0c0183c0c010316407504405070500004402091006110b10100c9080c842c000c0340740c1c42591300e0280c0c040f40c44140e50401c0d00300001104965101005c12807158201e40001c1c0c2c44000c40f541d079a60500445002c10b40500000d4a521880001c4c00d034031122a0150041d400c1000340400c040c000c80c002c04603407140c01100b052405c283c3c100201ca00500c2e05100202942c0ca03440406034446501c28009408520005100102c41c0c840c000540da908913140342c1001c0c43c6010303960000c1c0510404c90602e042d80070f003c54210b03e192240c3c0c240c0340074580105040340340c2125502d00103000080100e03220b0910041511038109445a40b0405c03008280d80d502074503921885601c5070755900320080c4041e00805083c0428480154480c130800c040da0102c1c0b41030031110801220202d003070514038030858001e90002503040308069140d0000000720720310fa5010301c002c0741c846c2205500c034051406495426030b0745c00300 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 764151276 1250 764150026 764150039
    0x50601062307060b100509030d05090d032a080c060105010323060f0a180b04050f061002030d09032a05030d02070204020909100e0f040201021f021c061a0310 69
    0x1c0000910403c00011070809083c0480c01c1e100500a45001141c2d01285940203810b0a01c000000b07a6080d142c41c91034404031100041c2c424000b04009410840703000c060152002a1044400c00c07400141580d0100c800203103030a81382ea030300001c01a4400d007d440c0001030554002d004401c450040c40302030803e0702a4110140c20001d200512159005582c003419030441e48444d01c1da0303000352061b2680040c200e103a03000c884080d1135120400501803450f04041064446030070304402c0d0800c41c2140c03840401840d80381c00b04d02d14010300101c6101d00b0300c3d001e0035400301a0408412030703246410b0b1070001304403400d0315440c2040c40c0c40c0c1c0002400d2500100520711100d1125801000440c0c070046c8014207140d81e54000c54004403007268101079800014005004000c0c2c10200c2c07992113005000790758880e140c01d50000391181c5400c0342103003000347d0110a507a03400e90b013501624208940040b14a604c0709032810000c024012070f01c20407607519958001641484855001c0f02d200e00d0041c8a10103a052030141d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 764152526 1250 764151276 764151347
    0x9050d060e1f02040f0e130b09030409020f041406030f0a0b0d06060306020406021216020105030c0d0207060506191d0915070305070e0d051f0608010c090305060106 72
    0x145294001e00524440101c90340c040c2480320030302c454080380181c40e5400d11101e41e071032004540018402400a6040281da142c0c1c0015000c1e4460344641c8180480e11000d00c45403550055400030704019002040107614805a40046d1080310381e441c01d00b42098850702c0c1481010702c015605640000034060025002440540220040b414054803000e1955401c2c1c03103e07400c8445a400441e40d2036000103040100c00d030b042104080e0070640303000c3e0134500320344555a403a04840004009044c08000710004072071608040075650000720440084d943c410351403900c10010b00b42101c0840c414500554003018100100410600b81c83c1810342445000c0b0401d030440d00b00000080800440f4410711040c5071440d0414881280103802689000ca0207091000014020042aa08180c0596890050800410400540b01c003000902e410150114800c40710700c4030243c1320642299640c0c2d82802000209039910151000440f8010425504966280d19040700c010845055485080801d100c20222988001 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 764153776 1250 764152526 764152541
    0x506040902030c2103040602060f0601110a0b061c11090c0c19020a080d05120a020a05071203111b190309030308090a050105070804030e090105010f0309020301020c030408010e0d09050d06 82
    0xc13420030408240c41304c41c5500e554402d41191005820403407d20003020b442162082d040202401c04c0c0c02c21010365407034070b0760b00d00285001a20305107080b4042030240d220b8070300b00740740d080400c40d02d0030b1080002d0a111420001c0ca203401da00a6600200185520b08000d060703681c080c00d1803002c0e0511108a0001d6240310f1111207050b07a00c01d00d0303c0b00004d4420400c00100c074030107000c0e441d9983c0b0b4143d4040e541d600100300034140300403640100f1100c0c1801c0d41c8081280c14040d0b2013148541411401c2c0d17411401009910103088008500088101c025912a1048030284000008030782c1d040707454000c280300c5540880401070100e0400201800082d0142070700716480381ca010201c44502c0d40c151146403e40c0c03019030345600440c8001c4180028154030140340407504405440f00c0e011540750100003004283ea500034402090b41c0c6140c121f00315a401c0d01124145804141141c0d00d6503241c88206000b4801404ca096580c880c0b03840000095000d03640c0301c0b0880c3d4004000c05d6100c01140c88100182c01c10 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 764155026 1250 764153776 764153809
    0x105030c130504020c010e061602030d0c0c050d0806100302070c060f1b06090b01080f0709150305070803090109050907080f041103061003032309100c0c09020d0506040902030c 77
    0x60071004a11038441d4805816031100110000c00c0d1480c50810903401d0640280101e0300f64002c03604600c1314240c001080b5007841c019102e001483c22440d81c1c04642c1307111890001020f6000700c19401c11202d500102080c001d0b07100704e441d4848010b01d5003040d0200c1c4144840180f2440380301404004150280e144c8003031400003400d040034002d40443c040412102901070844095503984410300c184a000d00300d07180540090301c001d00c07908105541d090760b120814400c20040f02d03101c0410744400a51021020001c50b442021180900d4540292540f2074010007042070020310b8104001410740390903000103010700e015031214001038460120204003c10014000d40f03800006140500d180d40341044114401d00b104070505429604500e4004c000c01d07514a00d000c50011500070580d140703400d020880720401d1702100c409401860400b0192010740c0c404101070038242500c0d4000640300d0668006000c0380c2c4400c801088139a80c0c0b0003c00003110080030000e905540402000031603800e10029901c0d01607074 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 764156276 1250 764155026 764155057
    0x6061d131103090a1a0f0a0c180603050603061003030c0b040609120509100206011a1308010e0d111524090118050108010b060a120f0203010906170604020105030c 71
    0x140700301c0c880203030303070042d160a111944480a50010700100e4906024449496025160281000003609074825801391040050f2030783c032045d0020540c011a615800b15240440308114950381c2d81014005160840d0707018024003549001440318103091021700d040d41da240c3c44040c02e0081039296044540c20052003285e1040d501d546400c041044044010352200040e6519941d41141c1010320544000300003008082d5440080103002c1e40c50300ba61610300d54032200e00300c0c584513030b0141c104550682240e800075096500e0110142034125010440e000b0f2000f4503241d4446420780400f403107070f68220202a01ca00c26a60701d021912140f140040041510300003044c901580701c1000002e48444021392001509412402d21480c440d6458080e81d40100002c00007013000c241e0000c0030418900c9514600e1003042002c00034050444010345c0256a002c41e00413085440f90b8454003220001d1900b40901c44a02c21414401210b501000a01038415a41a50b400341180c40c0c0070300c00115600310702900c20b003d28 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 764157526 1250 764156276 764156291
    0x11802032b050f0f040e16090e06130902062101150e1e090a0515090f060603090a12121a010f0e010509061602120d020a080702120a060e0106061d13 65
    0x2403113014001401540e2076401003411b10260ba0703140c00030b50308412000c0c0a280841000603000d040368840c1d000e4010740d01502224184014840140101c0034025840034000c40c40d0200a46050b000c0310038501501c0c40420540d8031194036051440c00c1201d154000b4200105902842c00e1400f90301d101d003010101007035000b100010006050318011100051b54982d6501001225800c10400b009883e00540707003020a818010b900e00d0b04148001c1c40039001d29000000b051325440c0c100b0545441d142c02c0440c1445600301218010f0142503030000d00000c0f54105040d0200c0d111640904609882c0c0507150b03e070100c0e11550b070a0f2001c1c1200008681440028030082c803803515103d00a00c010040b20016104510085c0304000700c041c200f0f038201c101c0f9400300c40c00394a4141c0001780324000640050007551075880620000d0344640c0c0c0c6c00c0e00410075004040d8001c00300401500820f0039400000020f106054480d03504541d4640011380f6100040c500307118410700e5007841744440401e5049001c0125222 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 764158776 1250 764157526 764157547
    0x180515070614090715050d110906070501021801031b14130801021b281b15090801050c2a0a140f01050402150d0e011802032b050f 57
    0x181d0a00281a410103850b80030020a00c40070b102c04806005101501c0940e0031010800034454003403d83c9912001c0e90369030000141004500c25141000c03030083c40903940d14954a0124084d410040c0507604010032046125055070083c003501410b04806001c03080060700040d811105400403c60a0017424401c0061416034a004501c10025102d00c40015a490889101d1070745100c2e10f03e00540c0594000d03081100201441940c0f0584281e028a0003042c0d1f0146800d00318003804004540507280c0c07070004000101101100000320207442c5940301c40c00c40310364801c025800e91300115101100041c04000101e07810100300f046103414100015400c0c0340d00c594410369480c00005140c2600c8a880c0c503051002c820104015500382044808024880c904240d03001c40d0700048050380750295943e000c549041644a0b940c0075003081e2905000a014000c1c105004480d00d104c090011380c00390142029084103100000c400301404c040150005041d1418510100c4103900501216065208100401c1105 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 764160026 1250 764158776 764158781
    0x306150d110a0914030615091e040308011d0f07052101060509090a06060f03020705010b180a180f110117040b0f070309150b0307030209010e0f06011805150706 70
    0x1e02003a03280c401e0f29500b800a1070408440d0110464420741c403010800c04241c1015803024602030b010b40d48820300c2e403504020018040a880c06100e1124110300412041c5540030a160341280c80d043d458140840316010001c01300e110440b0190760010075500851003480c07140c0000c080039110103802c1084100b607894403c102a40c01ea00200015401080c0c0c1400c0d841d250007503c0c0c103c0710344901042000c2c074105020340251038120120f030905078045500c3d81401029044004291070090080c4c2500003004070340a84103d0640d00c4400f15481d150418180401ea03550340c0c0d0179a42c100120707070030f00d181541e181e95440f039035800708604102110410310b064400148055020758410f4580f1209458103824880020200500070002c1509103d41c0d5800f2170226010582200802c0c0808074031007004001080c5011300d01ea000942080c0c022000003285060501c03201d000d40c0840300901499124840111245900091114130003005154104964502050b031900c60241130140d50f1704068064442c03008 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 764161276 1250 764160026 764160037
    0x9070507020405090c18011a0f0c03030a09140703082a0607030f14040b070804030e0d080702100e09130c0b1801030b061309050a060803070c1a0306150d11 68
    0x6185e03c0348202d034285146c400c071145400f19404e68094100e614050312041414240c20213000310701000200d0219903210710003110070075400042140d99030b04000c140e00004240d010b40c240d55004110344143e11010022511a003200d030001c0c40a030a00480b207801c000c00441c0200c8507155410300c14074001e00c00009000981c801c050686000410401d62071003c03094401d00c449003140e1031ba040d0100701c00980e9680d0703440c1d000003662a210b81582e50f607140640d44291400611540020900101e108002d03113000240506442542d15400e0021207001c103460090145050950010500c40040d0508009000140c10580176542c00d490403a40d490b40c0e4402544a40180c400c1400d04490407080c0756014000c0141e00c10741610510301c0e044418240c0c5180c520039004502140d0303111703004a0b500e0501a0400c00c05000480d040e82d540c0e00207450007071180300c0a882100315102050554070760696407041900d01c01c02e0013402181e1204241d100d98085075204540c4001c8107961000100100c00f1200007414 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 764162526 1250 764161276 764161291
    0x7210506030732150f031806090a05100501080703030f1803030e0405070f08130303060512071a0906040e07120e06090c120307170403060213181a09070507020405 71
    0x80f59000c0c060204000c81c06030340d03442c000d6200c612210360700102102212040304686000d29220303142c111052200d0b0950a410150920484050102410700401d908920b18410300c12159142010071010040d54030901c1401000d40000f101000480d0240360741503c1130780d02d442d1000712155081024031903111550000d44c00140d0040c0241384500303103131240b41d0300001c2909224146044082008002003801003120b800980b5564951040500070303000f103406030000400c89107540c00000c40300c40d0703520300604c6182c7c0b0b01d800d000410154449618111144000d029042e0f518050a0600d080306c40b400c081c040004020300c0c190314800f4000184212040014200060b01081c1000110030345070903e1200300c0c0740324140030a541c0c0701a4400000311071301c40b5402415105103001c2d10140349624025544060584d60000414a0004051014080c240d0351201a0441082c0f01100c2d16022901d189614440e001403020440b070542c035294148960003c1c40d498000d20f0a5250342c04035090380c006440c00c1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 764163776 1250 764162526 764162579
    0x311030f1623061803040f090203060405010f060c02041d0d02070311220b121005011d0c120c0f120f01060c080f0306130903020f06072105060307 64
    0x8000b5040c0482c0c4094092000c125115400003180c01e442c0c0e90082c2c0744030300090903180c090000b0002031081c3e900038140e411b080d140d00da0303490718150044c0d4000c44602e4812032a201c0041030f90b024400c404400d40d413a9a50b2141c0300c3c04d056092000030700c9e894101c40c000c80e5a0f07440e0052225002c100308051000c60364041c043c803520310703c2c00c00d8903a88540c403d54454070b5105000c02c00090350000c0360000b4406d001c400300d19640c003400401e460f000c03a42c456680a0040070054030042c031186c0c0117203040701e503c500c4102d1184403c0010882c121003d43d110240300b942088000350049a140c10640c028034040580352400842c0a41f40300030f6480303510704a111000641c100142e020304c0070304042c0141028101090803400d43d50328680c1da4070441000103089100403011410540b180c01d240c07444090400707400c0003c182e003400c010703581d268003401080f287e1080c0c400042040344070301030f5600300e1120910507000c4030002c800054081d0500401c51601446207a10001342809140e0896001d0400380590 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 764165026 1250 764163776 764163817
    0x4050414160b09060d1401030c08120304030509040b01030605190311090603032517270a091d031201080f0a150f0e010f0608010f05090a0311030f 64
    0xe242000404000c464801c9034486041108041c00350446815480840d000d5585030903850902000302405601c10b8a80040304001000300042c2c80c1004040c0d52811045420702000842c11581521040741d0060000e07205018007a00c1d81407540000425800505011820035260008216104c0003856070950485914000700240b191020507240401e500f598800954070749600801c5c1c0d43d05c80c000441c640d601c0c031801d0340c0d015802e0780c081d400074042d0b00146080c849404159841c100c1c1c1c00000c4440541441c0e1032a00c0c080c014089000e411101c03000e000c4001003450005060f0007000005a5030b42d002840e100684804203007400104580c20301c2681c101225410140898034110216649811540c004c41880b00420901c01180c82000b1085074086201450880c13507030050800d12144400c1036090241a00b80e840141c1c11036805c1d036044500070804d02000780c0103413003030750300607074454010743c1000d296240802d00c10800c00d107800d16010112494003029004c400c4141c1c0c44202c40d140c0200081c3c0c031 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 764166276 1250 764165026 764165063
    0x1309090807140127120804080f160b0108011517031b0a1103060903030103080d0b04020c0709290607021503010f05131406010c051204060c06060f06170a0b040504 71
    0x10b10401a000540d0740600304d4030700b0368507030319850103088415052041c024005002c0007880c0044415039803c00111988414030b03034110306141100030700e0071101c1c05104400461000d42c1480380445251121880a41b40d501c0c0201d059182409010b22520b02d003c10065203000c0400310440c0710140d143c54009140350300760b40c10450200388000c500c40c2d1081d003107a01806000c85000058a041d642c10044045c1c0c0c920200c0c02100041041c040800d40042c00400c43c0320b203001022030084200c6850b580203111122428603a051801500308020541503203213240303d58203081000250a000e84090000d4811035602c942001c00340e0001d071b0103020b24241101081c0142d0900040181611507001c105202844030258541c2d02c410006082d41c4c10044810b00e0503051000800101748004007003000181e95507290580105110700030381080d1a9241400340000f03810040752081000c44440d551640c000401e44112081c0001003d084c8060f595142c2c188101d841d610b0f446203900442c41020001e942240f90344 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 764167526 1250 764166276 764166311
    0x4090605120a14012703080f06030d21060321050f090d03020717010b0a0b040f062d0309200f0d14010c0504031713090908071401 57
    0x4110300d024128081c041d0610080001d550040c950f030081c8403a40003001441500d005240181c0901003520820b50705d0458120800f00d400c0025001e0341e034540f401d940b4242d40080340c81d004d83e21141c05500503010700c252a1b00c141e0861001024000079030800c0c480a4a20390103680050700240d03440c01d51690420014002c945007541100f071541041400d29079034800348600d03030058942c940d000e0488000c0c0181054400d02042019200b15484180c14000a030f02180c000e017800076001c0c0c0245032520740840c01d59a200c0a0b1021a0710850112243c141002c50884d501082455100c01d0502040840c40c2c502d81104c0c9a0212481ea40d42c3c0003078004c5640c00e1a44400351402402c4024022a00e0f04c01e10945800445d118452001d41d016500200f0074500000c17154003192090b6029464115510307110356004004004a9000e5640c00a0000c48c013000c001240c030603c1c0610f556240551030801003420641c12111450b40a05141400d2030f000e80c4500000345454907030205565918610410302c000b06030b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 764168776 1250 764167526 764167529
    0x20f070806062b12020609070e06090c1b0a03050304030306120b040b06121617030309030405040f0b03151b0702010e0409020f10120f2c070f0308040906 67
    0x400284110708100d00442e01c40d81c281c400395500f02c0408291450b03446060345400c460590300c1011071000f46032a010003510741e0003d071140c09044c000c0304800100100882400b0b40250f5000f00002e2064070360b00050140d65202c4556070812501102000c1c0350360605100b50201d03030740a9201d8640d6460585801000c0700c200341c1103c145800078943c00d00114a1000f03a01d030f03001d03a01c840803036000e0712488001484040100c010106e20320400928640821140340c00d442140c11491000404518003802c0300d449001c00c5860041c90b44c41400104001d2030590800000c40307491034000a540709510020900703101c4448103900b03202d43e0311800c0c4070300144410800c031002e180f01e0300c0701030030882d080d80005c02c52001e503029071344a5601e50082400b95500c140380c090100900a14502451005c85009004162030020754070409242c10310700d02c0d00c2d83c568012100070303804445a02c2e2a00c21000c1c040700c211107910050b410a84501c4001051010140694802640c040c1c14001e03125860300c00381c8810384019 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 764170026 1250 764168776 764168789
    0xf0f150f0a0f0f0e150418090b07020a05030d090213060602030306100201060602030a35041a1506030a090803010803070203010609020c030901140c030406080a05070806150a0e090403020f07 83
    0x1402010080d060703100e40d01480c44c000c121151000c107050400c00d45194000c541107040b880006001d00380c64000b180d40b041e803001d40324071201c84159955003402c0e0f0712408410070181581c0c00810a40c05080e82d00d610101c55039200800c40035011403000c2c903a504882e1690020030260744000140b280915049824101612851000f807004900b0000e009490380500b0410805115000d0411101d0300a400846400200d01d0451801e00803840000004c92110a8905842d0410000f40100c07202c102c02c0301162045054041940d904006d81040c170030079a2006010a40c0517030303250000300001c1c8101000f14000c060341c03001591101100e00426007194010703403212022502c10807440209450100c1075840d562824203021030f0080b04440150306611818440304181d001c0082c0120f01c990700701101a004042c090b0081041e80e0741d890782901c02103420f440c00c43d0700c4034400014800d2041d0402c000c1404451500e4042581060140800d42000e816035044001da0400c8805159840c001c11108000303206 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 764171276 1250 764170026 764170037
    0x140c0a051902011b050702120a0210210c02071d010509010e040614090601170f0606060f120a02130e130b0603010e01060b1b060f04020438030c0d020f0f150f0a0f 71
    0x1560b2b000400a0400c1d08664060107580010095814100606003010b0241c080051214407425a00251144243c5c06a02ca60703076441c52031646c00c5800c0480b82ca060740c0c1d0103400f040303d59003000101050840300400c02c903170654031051035100c9031302c00204036805270580400500b00d42d4113010503444137840305111540d40b54461292a82c1c0c60303000094042e0091000e403005070b03580030b412456405910032041500c1c0710311000014007020004907401003401860098603000da0640340c800c401458442905d01103629004000c001011445001c031950b0014001400003400c20400e40c502401e488540d030007904e80034004283d2900c040594003145000c41d0404020703151910b00441d05044844001d40040e00581e65469a6801c50004050860303071806054000340c07541c4840d0400c20308141e00b122030a400b901076511041800c0c180104c0341441207078020907a601c106154000d201029500b03440302d65001c1e60303092039160500c48001c02400c00c0050035890aa55503162007014000b030a0300c00e0074134100070 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 764172526 1250 764171276 764171293
    0x2a070b090303180f150d0b040903170705131202120c0a1505210a06150f0507111c0318050105030705070c18140c0a051902011b05070212 60
    0x980100496568481c41d1503041c0941d00e102000c1580400d500310040c0d00b22004a45c242041e041c00c2d000380c4101056143c062014200c0c0c02c041c4000e0760f0350364600802240c080442d206a0a00001c00c0310350141031450054100584034a041c8420000d44e4803c0b0400513411810206504201c41c02507420482d41c0c2c0184014005100130800302e924901c504620703840d1200483d22050310070b004a441070b1062003a1410410041241c6c05a0500d0903039a0440e00342c60f104d000241288480010028001503440340a1340c80c081150649503584a404101e03011a1a5584c108440d607408184500302e94013580c1841c082c07202413402800480c002d8031002d00304050140101b009a0b884011030340c1c000380302d00d000c649411040c5401a010703140e942291102d014a20b00340e43c4100900c0e80034501c071202200c0c200c046511880c60381111391244690400009000300840e001e0441409014504a440c500c00024040d4904101c0b1080841c0048480002500010b424040d8500300180b03640d01d08030000074000c4503 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 764173776 1250 764172526 764172529
    0x30b18130b0703020913062c06010c0507170703020111060108030a1b021810060e03032209020301030605040b09060702060708100e0a05010801110705030d020306062a070b09 76
    0x40c410000102031580708800108802d101340c0603174132054005006050210543c85c0f41c04090070b018065521109030031000680e00c683d00441801c14012211340745080c58403894011120015801c0d01030b07032580704902000901c041403004000b15407501c0405000058118800104100059611018580d00880042c803040c00088111104d0b83c4e03171810222a4035012201d8420140c1003140042d501428080c244001a889401040e10441c3e940d0340e06001903880341d6058804450910329140c0513401070151400c1c50a08a6056019a83d069132100074180d0f9182c40c10141c0c0c0c026002110181d0304c0f18107000030000c81810305c44d00070007048013410951a0503039000b90f88007401030004041002c1d440118410740750304c034040300192224030030700241403410a4822029200a00c900e20f042d41c40d04440e8543c04044000751203003103501c800078614180590810710042d400217040e09600c02000c20400500c402128110701c07610400010691940401044003403c0a0b4150711094444030b0030496017455 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 764175026 1250 764173776 764173801
    0x51615051201091d010f060501030b062502031c030f0630060e100e1c02120c01060f03031101060f210501140925050d081e0406030b18 59
    0x159049200c000419040c1c1100d600c5039104d41c06000c00329946010780c50710380458190401803c0d20020f0b01c2c01d001d034a2064041c0a49481205601040040d05c11000c4c5070f40e10a07031800410840c0010201c404d140c0c07282d4900c030822469503010401080d51b80c0c40410714400c1034081e010041c280d01400120044c1c50102d1100c0e02004502c04200c1c444181c1580003c0000350385c098035840450804441070441d0b44001d00c0c005210300c00400070b0b1740c401c0e103521800d03a90060100515202d82940030300940c1c14180402000c5070050003440da5555200d440100f02e0701c2d59484100c1c0114040d03980c681d0340d510002c40c00c908640054000e12540c0703c02400500602940510320300d03d804240e248129000e1540c14800c2c01810003800030306c2d0704a490000d10016200000c2c00c0408050b5404c003085543d0350f0300c108c03039102603100c0c400d00c1d8103d82900341d414007248803030024005013124045100c24054003003600c18802e40c010340101021070356904190300581820007088070481c400080213a5141000c0d10080340 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 764176276 1250 764175026 764175029
    0x105040209012d08091204030b33120610180605040c050918041e140706020d1803212102030a0b03031314010c051615051201 55
    0xa5038001480100300d03440b440031242c8030f240641c9961480c5101c4014401038018241c60400001c003000c0c0032505242c1c1c040303134484a02c0942032200e842c00e45107036aa400303d030b480206400010140401c00c100040804400010580c036580d004040041500007008401940c0c510066107580c801c0081007084100c624000042e105901d40440034206407000d0710020b450503420198005003010404605036800201a014000741201c103111028015031a540d114942250080c01c0c0036200c041c0800000d0040b00030201c0709008170011612007011592003444c01443d030b407108006a000154000707405034014862001e190008102031401855916101408007446070b00d41c2002d812010000a0300d40500c1c2d0202c40c400400300317000d40840c0703088a00e00094004442d480c61842c20803224040900c1c02000321415402100507080140d03092180c00e2801c0074421907124103016848600e94081001009601c001c030b1008100e048030b11b8241041c4621000c0303004404414400705028840b00e4003d0010a00e0 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 764177526 1250 764176276 764176279
    0xa170f0f070e190f050a050d0308150d06020c0616180e07110601080a05060606210c0405060c0f010b0a03021005031003080c1b09010807090b03010e061321080105 71
    0x82e005901c0800089140c102c00d00242d4020b000c6240000e200c0d29095503074400c4030030807903121041d5507444090049403c14610010005100240000c2001c3da40000910041c0707009000b60707400e0402070b5500022a4803c0258045c141d202d04c0030407001c003091903a2000d070044140b4088002400000982084580314022030f4011040c010000d0039451240040080c81151042100c05559440c3d4019496804001e41a14a80907140c00501340e428107a0488030040307403c0480b00700d200342a06440d06101005032081e00c0f240c0c1c0400000940c0d40e01d0b0800707480310242c40b034040c04441c0741e9014214215924003250b40d002d00d1542c0f10070009680d6005103d000300850341080d035a2681d49021200f2208800c0d0401405c170100421202000400004c40b422280c91810484007024126020040b01c424244901d1103a58004101445a80c00941040411a00141c00411001015000d131801c000301110f00c0142d606002c0083c2051201a690f0500207003c141106a0001c0c0d1021004100c5c0b4014080c0340d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 764178776 1250 764177526 764177537
    0xc09040b040e1e28030807020304050f040b0d0602031e0609060d082101060c0303140c190512040605070807080c0405270403212703050f0a170f0f07 65
    0x1040010b005004c0c2001c010320307106103c0e020241c9420301a07038039440d1110503000104c0c0c1c04005820301d40000201c0e025158002d2610300600354000410003d48100100303c0d412003110541300c000109280090b502030410f071220700344030801c2c42e40451081d040c001d010b83e00c121b01001c00c0c8406512a50303000480580c01c41f42d00740d079904400c85020f881c8512024000f082c105000000151300d9800900060854440d641c14000d590040a204a800c403082c0c0341c10a03c101c0c1040125000514110552107c0240e81000fa00f88400041c20000e1120210707070540d80ca903254000c1140c5035034458a40c682c80800d43c14001d0560403d143d81081a0040f80541c5026002e00f0342c00c4851000031920784100000105c0401c0c2c070784d02c1c00e03140041406014080011a90010250035006024030b409404244159078020188010803802c1045c01d9082082003a0184801040340c160003400b508000c00d607c90f03158a4500d1413640410101c148038070010f103041c0d01c0044000c02d00481d90704104049400014601c0c00 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 764180026 1250 764178776 764178823
    0xe030a1b0b0f041b0305060a140f1602070b0d021b03030c0412150c031401320109081b100c0203030a030522050c09070c03081315050c09040b040e 64
    0x35445842d24074284200041341400004104040040d2a03442900020030030b005045401456004803d400d40d060040c2500d00d40019120002d591102d5030703925468811222801c1d649d60000b08164444001c1c0d0400580000346142d402400b46040c000401110300210700d1403801c0e400b00003160041740540188800741184200038007486145051015040c09801c01c0b4260240001800901d070500038103c5401c8e4a000005420260b14411503024200c0202d82d500c102008200020700c00c0f1900189051282540010408040c00c01ca4980107010640c03101d403160366100f04100c50103180140ca0070811a4031212100140c4003c029500c00041c1c5003404510f40c3c903811801c8000300754020f800583d05070b00d0300d424800e0010014210200d01d10945003210310751119802140d03120341d0054040d003c29202070104104c0109014190395580c0070741064000b00d400788904000755407007500c10301100c02c4007040c00c2180c0d241a10508044034000c43e010003042c00300d46880c540b120f010401ea10b00780c0400299 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 764181276 1250 764180026 764180033
    0x10204150c050705010815120f1c14031302010309032d11030c0705190305150a0b180a2f0a120603020f060309100e030a1b0b0f04 57
    0x54601608a59a8821008501000003080c030310025005a49511404070006a41d500800410b40603001c948128071000c04000280b09080162611803003103845201041d011918052020f400c0c01c00b510005660000b0102e9001840d1241004400d105100c0c10000e000c0601e001321640d06038998282004075940580c4e0805842c25103107a0760049140c00141c403840142d00c050200499151181d40398025100d15200ca2aa81c80c081c1c0301c2240c0041c0c1c0680f00901940c40e1011072468401143e054071202d044c0c89544450401c40c00030a00a0100d6068042c40402ca0b0741d800340003402c3c04207550305c40c50442c0c00c02041020100c041e24204602c0c0e6120402040d51608081740301d101076000d00c0308a00024002036052490317100101c048001100d12009114000780d41c06007034101d9400030600d56902d07136403801b001001d90000d0080c00e01b0340700c0c1c0050712014040741e0040002e20065100130b1501c2da148081c01406003402c241840040750040c0800b800000c00a9840b00e400c980e183c0005034050b0348501d03 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 764182526 1250 764181276 764181281
    0x1050d02210703050c1c020a03171b0a0c0605070203060403030506040b0312030f0f1005040f18121116090f0608031204021e1c030302091008060901151e0201 69
    0x101c140901c0c0c042c41801205125000480d120f012805403100d048021041013003248901c21002d0003944040c00081c100f0209410000f0201e181d8402e20b052450304130508c00159041080d90000151604100b40740340c03d000c2c072080020004c007034504141d031400d50f5076800291210701c0104000d05140e038401c0490090b0719140e000800106000d030880d041d4105280c08000a41c00c00c48005d0321041c4200d0007c1d081102200c00c0c01d0040000b059202c00044c107000c02c01c006400e01c80c1d000a04c550380c0c2c445040825116140c6030350468040e00341c554001011150003400310103983e0940880c2c2e8401c416000d41240c145a01c14200c60404100003225201d170b075154000307091a0391093781148004265400c6100c60a560783c0d00980c4202c803009138840c400c0d00506c1120b0000031804e94450011646c1c14070001003150266801c0c0d200b4600141341107403010001312484041c0d88a00001200d14003048800d0a007181c00ca405889040c500051610305110010060f9140d4040810380c1c14100301643c4c8818000d4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 764183776 1250 764182526 764182579
    0x150e07111f0905060105010f05070f050c1e03121c1505040222090b090c0d0615030903021207050c19030618060f0b030606120a12051b0601050d02 64
    0x8103061910074640d00c46403025140c01c03182035402d070080100000e0a0341c05100c80c2c8010038010380f101824a40c0c1500d0b401c1d02001c600f6019151030040c4c8514010300c4d600d101c40d044c3c14603d000d0f0312141200000c000e262920f20105803019660000b000880c0c140054460801c3c00568a8000810400ba0010241c3c440504650005411a001250310000c40030130019280401c0d0540c0d43d80b100040c5d0300c180c0030060320b40880015800410100104029048800080041464040b80450315554400806100c40ca480300d103540080c0d500d400800416a050000c50002119070040c3c40c20a80e45844250722900300d540018410740010b80d58094078502140c41e00c00a50700400c00b004004240c4100020055015030122026850840380c40001d2a4512845030342060103002400d1a5a4400078018180a0b400c8041c003548144086000000c002d038043c0c0100007142c0d510651a5000f03441801c180d030b03090141580c52600040014401c0d900c810015400244c0c046031410f4194103000503281005000 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 764185026 1250 764183776 764183803
    0x90301020313050d0207060c11030313170c0a1505070f050303010e040201110616050a090513061410020d03020306011707021f0e10020c240109150e0711 67
    0x8420429810a01032086803054082e005031503914004d507108a0301d440b02e50141c100400c003030001329804030f6141d50070100c031200040d045170314100c8408003088641701542d025158100c2c10f0395007095040340600c020780d8030b043c003520207030f081500f81001c000b007050450901404014020412100784162074280300d64040e041400c0e00d51740c0d61141a5014140401c80b42a4085502c0710110150b04000241c0c5500c80c9103c1024520300244480085071194400b018100030010507802c04180c40ea10301e5450709884061290000e5200e18002c0c01c40c000135600c03071500c0c3c45445203988a20002d900480c034654109070700e180040c0e036036990000680f416902c2030944035404111204101e41700303800040100825180e003c60021032481c2e8a001000d8802e240d0303a400b82500144800d0391004082c2d0003034441c07101d050301a505224031000100341030088043d545140350070090010012802e01c2d104081c0004d80b82c1041c407203554104950743d510160050103038800c1050315001c40d04502c4003481032940b035804 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 764186276 1250 764185026 764185031
    0xe090705060f0a0e120d03110903150a0c0e0a060c2103020c0c0901120311150f1501080103080a0503090703120201090501051006091503150306140a0c051806090301 72
    0x1103944480c80c054000983d0000480c09803101503d46282404040d080811148020100410012800c9015110714115000c0c4c0f14000e00600425940600802d1040da103075408105a42c03520b082c0803400c1e190740d062800d00707100607080c80040d2500c0f1003081c5001d840c2c5034100041144981c1c5481e8100d170404101d5842c0d5502100041000e8503416001070041034181c40c1141e4401111100304a603980b42845812000b504521079003001030f00038078043c1c0e0383c402100241d0790408410080070a1030041120381c0790b100720b555400c0054407190030300846480c0704e082c40d004038150704542d0f41e403440e4403441c14070b80103000380800001c0340c4042c200110740280d984141018200c15008a01074003078045003400319559400c100004181030060101c0000f2102250f0b00c00d00150300d070030046699101d004030750b05c007010744890840c8425801c0c16981c2004520411000036103024070ac4a8903030110001e8149501942002407003010994081d0513143c0408682c4000100780b403152000904a22814040c16010350 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 764187526 1250 764186276 764186287
    0xb13030204090c080c0a0f090b0102030d05070905031c0203030f04060b030109080915030c0f03070507051f11181009030213150f030305070b060f120d140f040e09070506 74
    0x3c0c00c2100301003101c0013441120a0840400200a2012514000c1751005411090104030000d01e1fa000002c0340c58060042d81d2500d00d11413081c0040e0384007102da6a01045096200700310320700b420031240b00340a42c0349040105401c5180d60083d00c901c005408000000c4c428400301702404035075231005200200040c004c02c4060500c0c43c1081c0c0e560003040110744600100c0101601180e2a01d0460340720b041542c0002d854130441c80e64400c11034201420103c100702d8140729140005d02c040240c851070300d0b6100d0000b03040301c070940c44c1c100698100800c4100b02c24810b0181000001c641c04400c103044204a03404144a26400300440c2e0001b03095101940c84541c291424404015031340c000513035607141e500024041e61725001144090b5406100040004100300208000300d4020f044550300048020f200c0110400440c000601e10008405210f607241c1041c5100c42c403564002c0c2007031301c404800521b0181004801080030949000798030690700700c3c00030740b0b00040c000d110501c080340c0a400c1c010903898503103 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 764188776 1250 764187526 764187533
    0x40c053a140f0f011107080405042007030914042c0f15010519080604030323010605090a0e0606070204150b13090c0918020711030d0f0e0d08040b1303020409 69
    0x1c0c1140303c2c038040c440d40313007488901c442c8503880110f625458001071300320701e440d03e080e007404000c01c070803880205000419032112200c030358102e00414816000342ea4510140c0e00302001251600980f0083c0c5100c0c40c9081c55021401e10405800402040003058814145407003403a0907080405a443c40500c07030040300c41c401c2d41c1c031403070000b07031810b07034406488081030344440452220b140501405035200c00c2d408040050b000900c603030404c1014140c094140b0303030004080c819400c0c14807400e0f04002e01144006c54a0342540c10242e080000030310b2180c1c0f030b1421a0400c0c1020502c94481d869000c0c1c042d540350301028540010160718280107104050101c4e64602030711041c3d05105005000d030405079420702d520400000d200e0300e03110082d1040c42001c500c5904c1001640402507000c082c1c103d0751a28421071030b601710794060002803c030741410784411028900381d0b00b00400c0721129411b540d01c01c07080500c4040c04035a00300140e900303496001441c20b0340c80b080189200d400302900c2d80f009600904029901040 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 764190026 1250 764188776 764188783
    0x8070314280e1e01022104140706080105040513080306100203091c030f0f080a0e1623060309062d0403050d060b0304050d2105040c053a140f 62
    0x402203c9212000c0c607401d9150441c01d038401c801043d0049603401d02c0003500910b92107800307500107106801000844400100362810030840c1d90001c004a032a081c010816410035001e4181e208812050750a2920f50a90791007803030f0300000e000d460140100c0162500814000c000329100f03582c000b41450b100014002c040e10405c3e9801c2d808034002003540581800c04c43c02200c054000b06a60b40362402d0a5480c154240020b18404040004030302c11a4225045034184030018400b525801300b1002a4440942051a00810741c54180d8014030040042010b10040814a00c1d00b1080c5074400c2d59084011039140c0b4080a4294022202d82c100901400101030300030b1b0084c984950004001d001d03c554684000c2081e0100b203e024005401c030381150113205104559211710032915080740c1c030504440503c25803c666040301d044a0700ca0881d641030000e481c015006042e0304c51601600d96200201700310f00340e0301160004048141c94840f0300c1c010100080d03140e2590034141d503a030444240080b1411155274 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 764191276 1250 764190026 764190043
    0x130e250f0f2304090b060a0c0807150216060606020712080309160e070917030a03050a0f0e010b09060906130e0a0f0308100608071409120a1208070314280e 68
    0x2c050345030031403030205c5040500540d0520042a2500c26100119845100c15a0b2181008407940103030158014910490740c800f4080c007501c2c001e0100321440b024a401d9080390301a401c818190362003c0c001f003081d140000c026040daa1790040000303807a0346860850303528040c84c3d14103101403000050030104150942460103481280150b5514445a40d034500900c0c00c1e01d5001e2000c03902e42c204003e1280ea0318000d40017160005100d82d000a200038040001d00304591600380c100500d039440720800c03601c5243c0401c0c49038206030300f11803405050500100159003850b15106a0440341c0c1c50710f40c1c02c0c076008001c7c00218126a04212914a08042032800405c0d5080c116890b81491401c1003011a07124401e0203400c1c81480151071f04041c022044080c0c00041d00a5140903a0100740140d01100c1000180081c144d40342c410441c007022090050006010f07880d005001e54100352500204161001c0c90352000c5410410700c01d0040004004911905400c0f910030581c1e082081c18400401e00e840800920201c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 764192526 1250 764191276 764191289
    0xf0d02040b180609010c030f1e0c1505090c010f2c030609010908310602010204081504050d0302070501150329160311130e250f0f2304 59
    0x80a20b2100d01000100e028120100e40010413a04402c0002401a40c4002e4088c0d190300f0011480b0900407000d50303903c01d10841200004400302c048108110a0030442140c000030381e4010300c1145043d13110144d4501000041504000b104c50001001c40c1c042c0c280c4001c151545a4159010465500e480c1c3c010044044000e001f8421000069580c10043c4103002c00315610400003480e001c00b201c1d4152214280d00c40d9070a900c2075800d18a40c03092a1041254014503241e0000f5880c3c0346403503841820321b207040ca000d15002e6101010840000c01c0801c260003404054240140c6800e10f5003086401040d00f10040314100e40b40480200510583c00200c40a1589040802032210304100641100c0e81c070544e2400c080d101c0c050280010340d4040d400c4482c01609c804116801d104002e44101d004040b954400b101c142d1120007409030568103000300d525400d00003211142915022000180b0810071001c0703860400a0707440c01000c0301489040300036048100c5822246103018480c24001250b40f052040700c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 764193776 1250 764192526 764192557
    0x170708060109050f0a05150c1911011e08070e3106140d110d06090b060d080a0e1306170c040504080406120906020d0504230d03020f0d02040b 62
    0x62500c2e03c0600c001015501500030500c00380741c94140b0047c4944000a1103e0000c24400000c0400040000c0d100300c0a105032080c143c0001e80c00c2c84040700040c00c8105040000c1c160b032410a0700c070135140c03510b00c0c0b64040c6408009907803200012601c090780440c02d03652041400220000d400c081c034808441c4c0c0c0071002c41a10441c2da5030741600c000c42e009481000d060709a0b030f42c1d58619524150382c40f94281400f8500700007a5507034150024074020001802112410340e079110300c1c002d001c45002c07a65800031055519003025110350305c3d18405809990140b6080107143d4460401c00c4d112404909011a402c078030a10190b40c5819980c1074003c0c0e0362461004030301c10701040302e03514a014001c0703500882c0c001c00c443d45080e052280450f0101500e02510411940745c480e40e200203183d030301c0100240500c00800040341d083c03914203440c003043c3c02d4030405801310a120011f909900042425100c4014500300141e0b01c4020140080150140302c0492040510100c2d0014840900500800403101585045c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 764195026 1250 764193776 764193779
    0xf02010306090e0a23060103080d0c020307030e09090c13091407060c0213110d021c290a0806180601150503061c050a030f110a020d12170708060109 65
    0x40080701d0126501414030750010034421301240b1411803081031003d60142240344092240640c0e45032880a0340101d90b2807000048903c2103c00b05e2041d440c056469201442c07a109060320018541918100ca0f27500c04c0320004086008100100b1501540b00d402501d0440c1c59000051224010000060300b52520706181034070340c980400c080788081c00d0307600c00d895070040f050081c1c00780f01d21300341c0c40f00710b81f090659a40c0140f00320a0101c400f4001501c440340000d07139110707410f50707a0355012201487c2c0d1906150406100c0103c05401c01c400748001902c0c0c002d040c10b05429a000603040e180e195000f200756000305c1040c030030301160070300c220500c2c40100002c0b2810b50b61307203050040304002c24681100002d070043c008100c4a141101c8441c584130380c030315020b40e08000c01d61246800c08240702c904401003207490100c5265250032880c07900748410007034094100790069802040d082170032051300802d41d8003c41d080313000d020700900d5036850381c159201c0241d5951034001e81c0540030b5141a501c1a0205061000 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 764196276 1250 764195026 764195039
    0x10b010315030f0f140f0c04230a11040513060f05011b3c02031e0a06090320060103170403050c040903050c01150f050906090f0a09020d0f02010306 65
    0x8520701183c1e8448150082050680c80c2c0d0140f984220a003211441032080c0400704071101000316625a1144a001c3c200040c1c0a404220882c2c0804e51880300380d20300ba18000303040c0c0c0c5074000c0540e40700300c0c0c21402003202c80822010f00c20358440c0d500b001382d008110701d404840c0c00000341d2044056448507601c0030750319074a4400644103540c221480507000244094600300048004044140d5000f803a4561055451401500c1511405204001000b40d849032404002d501e002c21000d09501c03100c0048a1741d41110382002e6031039680e401c0303018180ba0f40303400c1505d042620400000e4405402004101101044030b00802d80300c210038842607801c030680800782ea514002142c1121b04495102000340794250a09040c040600a0b000d4140d05000d010f000c4064ac4010a0080e90f036039204a0140c44070090070032003924803040382900107030b024a242e442005030701e48840c902a60012166514088a550750601f082c0180290030070094001e07509c46e100208004030741c1e0303202020034401d0f00c040c01441d03203c11 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 764197526 1250 764196276 764196311
    0x111902040b1e100912080702010201060f030b040309051c08031e01030b04050c03031c0c0c08180112020406020a081606110318060402010207060c0206040f080609150c070308091e010b0103 82
    0x1d584851090345c203010b000030300035001016014410300020803100d940d44009000d2001603813007500c140d150704040008250340440f130b14001d0b20044400c0b12a07010903400c02d040800400c000240000d100101040e4201240c1c102102e0300580120038010960b101e15040c0031005081e101150140f2690340a00420f20b0f003c070a8407504114010021410079101440c1c40203400075501503c18000180300c40c80200b100e050013464001800d0710381b2840c40c00c6000c001001c80d806c90200c6020580b040c88107201d0151b000c41d40150060300001d4150700c0c0c4154103000c0400350104280100820702c0c001103103d118040b003006c0e600c260382803000c0c2901080c48840c03a0b48c80e14401c0303c00a0041e0000c2400380700550040016205047c005005142010340720a0362a1605205030042e6420703611060400100d420104088200340d01a400b214100d41005024a41c240c024008010f062060b844009942d14804100320055a5540d0558a40f11051100030354000d10b00c8003091030001b401c0c840700142114611 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 764198776 1250 764197526 764197529
    0x703050109020a09200304080c01110a110712082a060106140306030601180207020402031f0b04030804050906011b200d0203030f070807050a03050c010c111902040b1e1009 75
    0x510704103054103584c0c400c0003159000800071980f500049c071200249010901c110031901d0070001a20340c0c1c2d40b00400c80a444013401c003034074440ca58080342d0b09115035a40781c0c1da601443c0b50300001254a540791108600d04a440e5801c40903c07555601c1200c080d12440018a80e04966190f1035803a034880070040880e542d84402c9030a643c040d4404401000500748880420444c00c074044401800c054899001030300341d80c03054400225006016000038043c14410002500a14001d42081e203440c3c555074a03034450380a180324544c45a503c03040003940f41e0340568a02603030200c250070801811865454181c510382c495249213100800959050704480c1407403001c42c16246c1d001070003141401c42c0f10303115101a070301c0f8480803610b40030b05018030f1000075001c00c080c0341801e100c0d0700c030f0079280d1419260203130071611a580d60108101102410008641c004606e04031035100d41c104801c4038060070300201c0c2c050a000c50300d858028800004180801110b5a515140c601084540020406030080304641c2840035 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 764200026 1250 764198776 764198801
    0x5100302031902030718020d11070b0403080408040f06170a0c02070308030c091206070e06090901050d17041206110c03161a0103080a0807080405060109020a110703050109020a09 78
    0x1840790021040c00b115440c400d544028101d030314080c2c4484544a0750300000001144840e0042422491200203008581d251142c86290909161041d200e2030451035015001138103022213a0003103820f00c41c03000f00b12000b804a126410042c1681d8403402810302541c9400e80040a0092004c100500701d46e009016040c0140d500412a450550300c03282000d5001130700d4802e01c4d00c410455030025488040c404807440c03c042024086030b1821600107000042580d00c0c0a2207500104802c04040c0e07100c0140905481007a202203080152a18010181c4441c440900e00f03851408540002e01d80d000d054442402c0d03206007404c5c081c040722841c2501c1180241e0310320740c0080e0014003c0d6414480428401000207001d01c0c840c42e0303d0340003030b41c10141d480001c2e08203940721807000400c2402682c00000c200c2d04494a490829464586621515181c0406015600c80180c0000c4c9146503180704050212950000e0b1060b5000d4681d2403901c28000d11301905c1c101d001e402601e0002980703200b6482000d035180c00 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 764201276 1250 764200026 764200033
    0x2031003050d080c040b09030309181e0c1207110a060b01180b12190e012702090a050903090a082401060203160213020315041d030706020a2a03030510030203 69
    0x1042246c4820740c101001ca65010301c41031044c03148a981e0300720100c21203180392041c452103003444058480c2c1c1e0100c00c0500c410604256061058901081041f0707442c842c5201e4184242d034440c80341c1165010420034280d403451007001049414444503901131800c0940903220b402214070410540d8804160520507100380303050034040c402829410780d03e03580e8001400c500c0c1113982c20385141d1700d0084420083c5044000da66403644100700701460700d02ea041682d102c2d42c03482581e10413940040c49034a0000d00c10844151100003145818400b0815110501001400c0e0460300741c440c01c155a842c070160295080700d403040c2c08020b20503072503040c085068409540c0910316203000304400e001da40b000e001c0c00301e802958080f00300315500d0f1244013841c02079204a082c580c3c0d140d00c08041000350350910248414035284141910b4000400004072840181d01c00805a00c1344081842691a1101e0001c140e05108140724210001050865031803601c0c1c1c46601c08001c41c0d00c4034241580f01d07030b1b068000290140d0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 764202526 1250 764201276 764201279
    0x1805090f190f020d0f030e091b09010c021201020a0e031c0914032103160e0307290403050d0801081504150f020f09090112020d1e0602031003050d080c04 67
    0x5000001c2c11045500140c420f10980409076994100480101ca06600140f94000002c40c1440e0216074150440b04642604080100030a2015024401c0c003540505001c4412000c400310341b103000d8103200c90940358000b1901d580c0d505101a01c400600034903940b0a002e2110b00741640d541d1403880c0171250046a443c10111400c0000c5001510001240160f1504c140303000c550481c59900c80004150b196210b910703450341040418039013441f01200c0940d0511101816145180d00c00098003411100e21050016040c1142446203c20110b441c1e5100300301000041c02100784440010600e41231015956601c2c6140e99034440d658a03501c1246881141b00044404240400e07041e05844d040e41d000c2032030010f140150070001d00101ea0081910504020b00440c030450342d4075184140c240109090204402c0c2d00b101540000d18100d0049001000820141d1480c281403181e0725000b40c145600c42e0f011952814140088a00c44141d440211513500c03409403c0794400388039050880c00780c081441843e043c036 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 764203776 1250 764202526 764202533
    0x816090609140403050a02161502103c020d02070b0a02120c0c1009030e1201022d040f0306090b0703140f09010b220b1014090402041805090f19 63
    0x294401c0780180114483c8603c0f903440d423034100c1511001000d8a00390b1303c3e02c0c900a4038021b801c10241d01503520545191102e980418103c010b82c0f10f000300c21107070342c04112400e000f403007541c0c4603081000c154030b1620216203038402d0074542c0d0007085c1e00343c09090200c4040d50384040ca00260311910b041180c0798005040400c4c902010103020300039203500700302515110700c2c648407801d0031035403896419400a40c0e10f80d4228202e007000d410350f40308002d10400039480c0003002a080c0781c0810440503441401d042c0e507000d1403403240e1200156409440e0384d0340c008004555a0a210019050700502035803489001c2c008500d42501900c241c003100400b40d07001c07640a541c0e081155110410042413204da88d52229202500390b540c200154588450b071002c0840e03540d40302030101c01198451840f40d0301840c0f024060710700300740d04a120454900715400041d0307a06e10210700403401078000c40e4005516107804650f010903144690b04180d2143d100401100d55803001820000c0d9642003801c41203910028540719100070 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 764205026 1250 764203776 764203787
    0xf03030c0605150301020315091e180106180c140301060c02010818120c16050108010b0703030b0d060e0d050a052203120804060b03070b120702070816090609140403 72
    0x11050306a448001c40c43c00200c0d0a80e4001c031440c0711581c0c1840b00701c8002e032400e003444d26001050300d0130304a11030031149004c800242000d800032580701245040711001100940021000c1c2c075440c1c1407002024200f2035101e001d0043c8444400204920040d00000001d01c141601d04036030a80e0359a481c622010340056038660405040104192254050000440c5080102d02c1c101c0c001c0018041e0b8a035503500d009420040086100c11081c20099420041d0340ea0246e0f4032170558100490b041d030340300414a01500101040503850390418a8207404006000b0390340d2051800c541400250b58a200708a07008a4482c82100c41480c0895028031103010724030008602004d034020842886041c290f160f0720b40c6524841c5131410440001d4241e000c000421440380240d00c0a0b440c00c1e0001e1036000d090080541250142c21104035807202540000b500a0340308100c8074008203810010b0f00c00c0b0601080c8909026580c030b0051030180c81c1070600000d840c4541d440b801c5c1e0310b0100e0510328034980e100c543d000c80d030 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 764206276 1250 764205026 764205031
    0x516050702040609020a050706051302011e11060412030e060c031603060f03060207051203040819021606032414010309081b011508010c170c130e0f010f03030c0605 72
    0x2c0040c1c2d5002c0c0072815403040d00c0140180c0314913444e03041d1904100e24000050320300040a40b035a10f600c0349420300060341c003e0504000d9469a005110081e00701da2400c4031100090800441540300e1401403100b80049020420100305082d50284540c40962500e0382d075a1505440380c010700041000003030039078402e17002c80141402240c41e0201e900340d5940d04c3d46145001030b030402e03910340707034000303644000c1000c1000a149480508523000c0d00b545003030344032821a030042e240707410b504000c107014081c8824420300c05d4011000c0f00b50100480640c48101c02001440a90070700070f140300d5010003402d072215805500f64110340041503081075616035540110301070090701104450504d420300000100241c4079030500c126a038641c0000a80000d01100c0cbe4406540d00c1d442241c00d6417400103c0d034201e56000d0010080c00c4500740146c0ca480e154140305841c03500c01c1c028602c0e18002c0c0a14042440d117001d0001c0c500136405451740040c03c3e41c841105003005c900500c8010003103407800c039078600041c0a6801159 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 764207526 1250 764206276 764206279
    0x70e1011150603100509060106230706020f0d050a0c030506040b0616060b0312090411091f050c1b0907020c06031816080c01080f061507050313170705040516050702 72
    0xd078014900c14131881620070a0701c41640f0380d00400c006000f156800340074184e4030450404840e01d600154084258144100800901001e40000d070130006900305000700c606080a14030100014545881400010490301c000000001d080c40049240e500d0311740140d042c4032600404540c0341c41450907008114001907030f02100c00a4507000c032068955024059a0240c1603c0480341d40e4a1200c1002c0004403a00c14903483c0110324180310f4801141c44241200d04250100c1078a015181006031095420b8000c0c014510070600c070300140e11003000b05400040304c00c0d26058460000d10344410100b640c564060004060700720034140001420340c80003203401030f801511601a0b80b03d1014120301046d1a201d940c1085003140d010600d079001c1941e002c80c09176070001c84c080b01d140c11401d000340000c1c0e901010801c200c84060340401e0400500106004603501031401d445029086590b419071817220340c118400060036800764140c006004d0406000340c91040082c150007140080000b1025607094000c850180e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 764208633 1107 764207526 764207533
    0x20706180303030b190f18060608221a010e07080408042d0e0702151302040c1112130503070e070503130b070e1011150603 54
    0x3038029241c1c9480c0204180b101d88001500c945130008800c10360b001c240344000340030800c95000104441c00c0c42941426612140e03481c608079821813280901103141c11001809071480003030f050b806400c9110b4082d07000e0383c00d0349034189940103c079000c541c1c900500c8010302402c0c28a0524950114551070201d069150a68541c00c241c0198400c01c00c02c000a104110124800702100103030042c40300c10514281e541d500c0396002c40d1001a41c0f02c102602881e0980101c00300303180041d0740304003200a400e45c020081c1e50b0a120050040440960800112240841c0f44031007d00205640c4440c10840c0747e2203400790f850401d42109650b200c00d21030b600000081204500003900e45c0e502101030304115840c0d0352800402c203038414488400800f801c5440c020800020703040b0f103820325400400c2d510f08604004001d03003030b21420007600104010f9030080c030480c0b0b414001d84075000d81c86030015059 = true := by decide +kernel

theorem cover : BRFrame.Cov 764028776 764208633 := by
  have h0 := BRFrame.cov_init 764028776
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 764028776 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 764028776 ≤ n) (h2 : n < 764208633) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
