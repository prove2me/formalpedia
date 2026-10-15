-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4568
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:02:32.836467+00:00
-- url     : https://prove2.me/submissions/62343de0-73d8-46a3-a161-fb9babd2f5f6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 821402877 ≤ n < 821582733 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 821404127 1250 821402877 821402891
    0xf08181605010e03030909012702071208130c0b0a1101020c010c111612060e0703150c0e0603131b0602030a0801080a1a181e0705010207230402040801 66
    0x2000310500c0da81600c0e000da032601c0b06002d0500030199640103107401d46038000c80d0a030040010008403814400ca0200b0302c01d01c0d104807104010030100300c0e00410810384da07080946a51102440c0e00c840015808003040c3d4442d9003901d550b07158008050801d0141c1c0340e41d01c100003031914007103000d0004500c00604c0d04000795078800c202840c050280c0310f07400002000c502800d00f040300c401408103001007404003032a150250140b4113901080b0b03081e8000001d80b02c41d43c2c2d4000483c280d4400f4001280690f005041d82d8981040c2c015001c0d0454004c180c80c4020044c3d40554084035039140f1041300d40207030a54071041d003000d4090a113441c0c02d5204119940700410004400142d49030044040c2c8252a419101d0400c01e03a65402d00c1905d4a0070a003000701072681d0880883d10f1220100c04064003c11101c004030704800014502902d042e07240d5103207071103002c040e51885100c40820403900c0c02402080c40039104144c0b80c140c608583c2c33041d11020640411344040f4050710b03611941c3c1920010042d84000b40000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 821405377 1250 821404127 821404153
    0x1511070801090b181c05071406010f14131d0d08040515012105030d0c0503011e05180a0b0612070306080c0112050a06120b0a0b0d030f0818 61
    0x800085408940f101c1000b40028102c411100400007004a004040c24a02c56131103001d41d4169884450003041c00320a2100b5030105141003c07480102a41000070500d0354180709a000d150342d9194031040b2501840200c2c0030075911954210501b514500002190203400c44d00203c0909901120115080c0314080c401000c4991040c1001d020f507000342d080d0b841c41d07450340b960b00385030410900416408110000b40544e5424400700b00500e450b02070002d90381040a000440750548000140c020300265001c030040c031081d81051a2905801002e18109540c3c038940008a13240e54405a0303454235007a038100008001d20255000302110100c020301817940d4144007021918110350554601e0000f901e0070b040032540200021b10a12501d03016100c81001c0a441210f0700d0203000000c120320380b00c07603e60400241003240e10301d03c84901c1d489516291032078a401040f01040340c03d4540f60038841c09608070400042a0445e620031107000e400d2070458441da072245145002691009880003081c8108400d003064 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 821406627 1250 821405377 821405381
    0x3070f111005031806060a120309081002070311070f0e0a0212011203021e031b0705062a0106140d03051902070f05011412060a03080a0c030f05131511070801 69
    0x1300740c658652045000700354150340d41d070300e0b401120090303000720b60f1050070b2186c4d0403402c90042189210f898511642078861b1103603401c0c4010724102d4014690003003144410140c00c07032039603d54a01c0d090003c1c24900c1c90445004070002240c07090703907144884803001c100d4030213903501103070100e0409441c00c808950351404a2402408890790903001401511440380868000100e801c914150480086082002d0742080300d0000c0790855201c080c500c6800c0c0c00107202d80380c0e68060000c0d44a00b41c03c07000340303140313000c80701c0994802140d140b10035903d4440c0520078120b00ba0070201440b4003e0702e805c01900782d41c0c5030903a140e10034031030301041e01d45410780c2c02460541d000950006440311115521381840d6294015a400301c82e4100040d024001401440e800044000035940e108000401100b086c2ea03984d03c540c2841e5002020f00e40026070200030b04400d050304003600200b0804949401440d00c08032705075886944d550740c002c20b200c54880e140d50310001489450030905140541080c0c90881d542c5d4540701d80 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 821407877 1250 821406627 821406631
    0x304150509010e030f21121501030c23070807020918010c21050a09150c39111e030712030507031b0f0303020c011d03070f11100503 58
    0x400500f903284072140d40d04011901d4a2461600b800800c400036566256860003140c040c0d00c2d200206040c4800c840307400700528050f008844820407482c0d00c4582d8030004050340c00c0950300f601842900440c003041140c03030003c1d054041815665807501c3d0f00c55071606012610889401075031107e00101840824800451011300c0e800c05000200042c842d1408181e800c2d0a40c10308105281c00c200741204192000c9410599001e5070003080081d040202d80e0303417071503d04488903180301202d50365200040c0460b00086003980101c00000b108079078420720072014809100d0203007182802c0d181d50302c6020402c80c0f0005080c58002004100030040c8940184e0b1b0424560a0b645c02c41c42445600c800280040c1048140d181d000e80594400303180104c01d450913074080108518010462540f1680c00e4045800312a69a00e150b11a0341c025036164185000d00d0700703644410780c0300038a81f4005c000c050400000041140c6041c1c3c0d009046118550700c50a00542002e18101102d070851841240f24002a41c8400114 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 821409127 1250 821407877 821407879
    0x301060e071d01030626121b070e19091b120c0510080c0309240f06010e0a090b01120c0c020915090109090f120f1205040b01090e0304150509 62
    0x204042c02e12070011400c0d180544624a40d0b0322045406500704480340301d80f50a24000d600c11104c810700c19043c522040ea202c100d071010b000d40402e11842c00003074103105602c010444600700e0959030500e0380c5458a05610348c55103101c05907648002c07004200c15407508101440081070241a03d42d034410108004003618842201d05110050006c00e2901c0e2110b07414400da4016620802555101a09040e40c0d90002d09480c0382803203064480742c41c00002003540d13241e5070721054420450b030404540c81c252640016190905018400c0902e50564a60711440e1089440c918004240030303207682e0069035501030001910100c0f80c1401000321034140c000e40781032440e034800e69280002d0759643e0081842c88100e1070806074042459001040200182e4200e580c2c0359015080c0201024503a6070b501c00c1c510303441040b05000c5140c0462400040740c0200d824950140035440a004a1070140e40300e00240c803050207800400341d50b540c00f26119190810550340580714031094802a18114000a40f503500000d103d0703 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 821410377 1250 821409127 821409167
    0x60203030118050108030412050f01050114090f0403140a09050904080408120a0203040501050d0b090405060405010b1c060e0705030a060b04110903030d1a060a0302120c0c0d0c020301060e07 83
    0x10b045502807240c94102c82050700550f090904021120700241e2240b041030303d25205500c118000d1500a1188500a01d244145090101b000a0070b000326900003c000000c840c56000401020a0b0401003004c0390104510040e503894039414030075503202c4055080550030040a104000070015218018800d0383d60040031100b0300c1031980c5102c0442d1044203a90700050300284420032031940500094005000380b10408900c80250f0341c08104403d104483c1500c8a03403214042c4000c1c428203101d18031104506486005004210080072120f050103c0c1c00105a075540d9050300800c4c41c1c05004e51406400c00501755040d80d401350034036401404030f10008030310642c03400003400c2503561070100325888554040d01850034411210005001050800c01c00350000b03a01a1100300c45540710002040c0e0030500703840040e02c0d21f03c85030b4050b0a400004018464014003004a440e89400001d14040b680c1901e2a00307a40c0c1801e20b1002c02d01614840e800310308180d280005111f4803d400103100b101c80440f840c91 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 821411627 1250 821410377 821410409
    0x71a1b0f0c0712020a23061602090106030c090b0702030a050d0818072d090e03070c09060b04031401140709061707120c0e06041d0f06090606031f0602030301 69
    0x34a0a4400390b404025440b02004c13900304941b032130484c8134115207201c0c8100013803e80a0038011070025802801c98891101070056000110318117443e15501520300c1d440c080114184100003d0306162450150b0740c4080e2003c2840b03c1107540030480348030b129074040b0681d21100d00039480078200d00002d840d4096000c00c000b00100600500041e040211080d03021100f40c840c00258001d801740020b04035001160150410205a076415402616180400503008643d1045d25040c5010b4100403a0410181075003003030001c01084030750740162000d80b60003c005c500e90a08460003103004008040030f8240500c0481c1c1007200c0140c01596460483d070f01c9440b4100340450b005841c2d5025502101e40034046541c2620960385c0030070a44c4921404041400c0444426000304002003464200340d0001010341c000c103c41009846642000c25081040322091704101d090102c0001c2300079000900840c002d100c08800652206e100343c4c0d901030040d0000b0f95203c1070a86810f002500d0f64424040c0c500e1402580ca0 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 821412877 1250 821411627 821411639
    0x5060d050103260703030905210301150e0303040e27160b16060c111b030f0a12030c2a02041811060a0207081b0f06071a1b0f0c07 57
    0x60ba03c84114031100031442c20b01c09540130350042c1890407080e42c0720302c1000c140e192071506001c0144141001c035140c69840b0740c94a201c21002015007901032003046498460072503181c40000544041c1c8171250020350443d134400861011120021640c07055001c11002250440c51008c900d260158401d401038554403510b9616030754440c03203214000044030180c116258041002c07980030481200301480c001080301c104c03030161072a025604001c5050704501c8a40038056140402c428a0302140b582e01030034946160703888040007030a01c00840410300d5291198108542d2060140000e00c450280c1c10510500300e2040c1c0310200c008a00c4104d001d289000c0e81081c04003094174803405407950064004020020240c203016490f048029020254858070303c01040c2c0c9035042c02948050724140d2181100e012181c02009001c15600070214043d240421a0f6000b01d0582800c0650000302380303040f48120781350501f80c0849007090562605064001082c2c108080403080002c2c440b1000c42012120081d40703d00d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 821414127 1250 821412877 821412923
    0x9062309040b06011b03260c0708090109030204060303030b090f0606040302150909070f022401060804050a0813030c0e070e100903052b02010c0806130605060d050103 73
    0x4414580c814182400200022007129070154401c006140121076000a009030956034004610101d0116070031003506c15414910075246810b0b1002001c000740740307003407030755516500744250f140c0a82860700002d102d80d96a4058582000215400303807041181e2039a130705000300281800c0804a1082c0710440102c7c400e29100c2c0800e0380150402000c051425147d40e0820210360354070f41144440c80018040c4881a07500c800d83c19100c0c000a86401240c3e0068001c0203080a15000802942d20b004d001819035401c0b140d602c050544e12141041031454403942419803901280b040001d0401c00d0002d040459042c01c1250503040303904c00d644913801142c40703200d0a803a4000c100d0700c660003d494110b105003145062029900c000b0755500b0480f080720348940b030f242d0510815500c00302d0407010440c401c640e40c000c1e0041c861034500d094802000085840c490092280790047c2c00640b05034866100320448268513400f00008000c0180f06656a034840d440303200181409100c103542040e10030360700c1092982c0300 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 821415377 1250 821414127 821414189
    0x31306030b01020a11010309030c0b0a0203040506010b03070504030f03020a050d020c010e030a171c0501090b011d01230d050f011505070f23060702010b09060f09040602030711070906 80
    0x40d8035405030301c031795001100100540072041e07082003807501c94200803c80d040046402070a8502016a5a1600e03061540c507001041e0b12100d4450803c1003000310f42070380442924140d1750320400022003109141030403860f0800141004d0b029014030b4541c441c005400043d4441429000c1e20b9480090420000301030b11070400c19800303010812082e100c0010b440702d8400a05ca07000500c80046141132a40d8006411990242c04c41219141e0341c00c2545032540e08000044020041c070007001051440b4440000c0003822880c9400c0c240f100c2619008011511040c182c4030500d008100410461a0841c0b5802c0081407e00c91038007210303c021040c0c0111882441241e20f100d8100c40180c100500c0303a41d440e1640e485c110860302c408000d08500140c011014441700303014450036800071030220600010842031042c0070b4030061180307896980c00c4116440b0441450f500c541c10a1005072a90f590313850076154520b007081c2c103000c28003d45c040415404c540303501c10001e980496a411021943c3c034080403440d0448 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 821416627 1250 821415377 821415383
    0x30203030d1508161d060d0b0c09181005061e0703020309040e030a08090f0a0807110a030c030308010e0c090f12030d02041706040f15060503031306030b01020a 70
    0x200001d080d0400140c205200c102c50b880c0039150341c190786450702c50038803441e0a101c2070100e80e202c104109600101c014031451142c14001d400150a0040015901c40c200010040c401c0501000240301440c4800940c1c0c40e0240c06000714698a01c00c4400c400030040031600301051000c0c1900100b00d6007480400d50308501c680181c66246500c0c0c40e015106542c010a00071003c40c44100034194460320389018052010350b00c04001c43d194090a0740c05080f040300100720071543d9114a41180d604400000e49940f600c0d007000c0c0310b41da40c030030340e04126041070446803038560020b002000c00400c01c006103601c0d03002c890103580c4840d180d90720b81603a660300d1401a180c4500e0100b081c840e80c00246000100301c0e0012a0082c03044a0101c90805e03204c0c190f40140c2c6804040a6011030308000034841958140c0906003854094121854681c0c0c80c0307110041035903000380c0020f03440c0c10501064881580050050000201180d80714006d04004051200d07035400303410000303804d203c15a00760f0350001407601d4840741c0c = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 821417877 1250 821416627 821416633
    0x1311040902120f10030201110c130204080c0d05100c030603020607030906020f030a1e02101b09060806090f061c0f0606060e0a06050309010f110a020c0d030e060a030905010509060a05060a030203 85
    0x417854004607103c25000d401803080e4080c506024203160b40c2c10170700d00c1510801610158a0300c2c980b800d00c2c0e00348602044268050358584d0014000164089488034014100036800141c15030101741c210300420450308000e4024000188103020704d5080040e56044034196400c5411503454003413035540324016030204d4404204e540394502e14412280f010b031074a0b82c10034411101d56801210f9a0001d9030416022245031a8400012000ba154071070602b40241142c0d04103059a42481c40100340c003103d004080c96004c2d100b5901040007035481d013810320100c4407092200c00052205050205e100010b000742210704920341080066040c1c02184020240c0c00014071111980703140500544150340000d03d000316039580e0707004c20300711a40a03102d042488000000c189848032010754003c0c0c5011140c80742c00d84141c0c4100421400241e02190040440740d007500c1d12510f40060407400d41c01340441c01d0004010f9400c1404112111000140b01c03803107404d208000b4083c9448482c140024000180000ba4050f0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 821419127 1250 821417877 821417879
    0x5060601050f041413022701020f070905040219090b0108060d0201080f040201110a151409100c0c230624010305060d0b070203030103050606030c06091311040902120f10 74
    0x100380d2200d200c40136040139003110035840146003080308991001c44440300002c141114144003482c02d1070021020f40080c0002c0c010300c9144c00c0b0a513600c61a034030451100380d40b80c0303001070b046448060710090491581022605041d460b80e10f0a409440300307000c114000782400c00044c2961030003022640381d65230103840700b04864071036200d000c8513808024810780c140554050a480e20b040100030100381203020311722111400d000f0702000000d40b8288402c07001c005070040148540341902082807a0740e4001c110002608000d610820350b070f10b400c686806402005006d458040d081230711405038240b012050262111a0780e0003100884110404505030b40c1c2000c01085400c1c50350181d482139410074001411f144844c1102d559800c10365500f12080720058101200400801c902003001b207800503011030151420682d081301041d81ca010300c3d000240b040c00c4c645204140c4c800f06500003518100032045140ea940d45942009010798031487da481d10000c210380000342c5030f2000380b03030403402044202c800ca0300c01 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 821420377 1250 821419127 821419139
    0x120a020d060305060a0f14040203060106110a1e1506030b1f05120a020a080a0f0f1a04030f0f1701030f1e060c1b0309170c040603060905060601050f04 66
    0x350440030152904960307455010021035800c00c690340c407a04890001180129610807003000f950303403500002c5000c00e43c12007400010394000c5090b9041d100d807407824802c60000300301203d29151740b900014020900800010a44034508048100b0035030007440d580b40d41d00325440620084600510000c0e101071604404600c00031022441c402640c0c07180200d10140c41d40300d00004111501e969002c03181c41c1c5c0000c000744110b0420707078000c20082180b030010302a070080d141c4078956481355803d0006d0001c50b190101d1020422442044505000045061031480c0b0307191402920350100d0400e0301000c1450000000f10451280c0307842c00714840240141d096a906c5c603502e44945910031501141c0c0301a80000148046001100007110f1602a903004251018140b40142010006000050401d611140d1030f10210341c0001400b0102c0d0840c1481041841c250f03040d5508203004000d07040d50190a12400006101032600700d52119400b0750300317585039911010010746281c4a007290300054034070244001c010b0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 821421627 1250 821420377 821420381
    0x20a020f010f140310080102181f020a061d010510030b013212060708061005030f13021507051006060906090e0a0207060e0d030c020303090c0918010c0206071202120a 73
    0x7141c0145070301c4580d1b1100090340c260780003018126850300c02050f05529034a00b645440300704008090ba1107191101e50140251100340c1c95401828498498500f10900350a4000d8842a406074000801540c100000c80400040341440701792072541a03a0004242100358032041c2c0703101d0500c0405501805c40700b040d07649000350b5a22000703502c504040c02901003510148034985c400c4400342d90f591420300e403800030042040d1307140d2540001c22006104010140f00028001a008140105800d0550005200040400f0607840d40042414400700c0c2c1ca1082000c001074028048110010902155449000443c0c0c41503061140320b0004840c00020030010010440301e03600700f040d412000d85048000d0300d030078058811041c27004206510000044d90b0040c0d0520074601a840144080c5165040c410718066403070740881c803014441c16200740400d94002e034841403d2900c1800c5c00082c4011641c2d0200651604400c898480100d515a9480d0754107081034400c445034043d4000c505100c50b26410141c81c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 821422877 1250 821421627 821421631
    0x140f0c0f03030415180807060e040e010e1b120c011b060216030c02090f280e0f03040e07091a0906091e010e0118050909030712020a020f010f1403 64
    0x60140003c000109030000300020000284509440f40b01d00c01c8080210b07654003864591007442240c010315000e100b5160b0203c10702004940407030303004c1031000f68500a10300611451114000f40d106051201440c03007410403141d80c098008840722030b45507204441581d2542540403030b2030300080c1d81050503c900c1491200400c0c603140141c400500304100c0d080c1103140c080c10601c041d004228494441003c5242c88107580381d103d0100003404480d030a0860710300b880d450070501207907000e029240c480c0080d0f0000390b00021a841900c000c94405d0026000e2803030b282e5000d40241008a1040000101c5050280164000f00c5030000c0c00008900b0700a41e1440c1642c02103403007242d0042c405c02501100345c1c0c600324990105864480030140030030003c80058100b000c221031183c180450b00401a00042100f40c0c0102121402e44000a20396211038116055115064000b807240a03180b1003002c407a640011640c02c0300703209407410000c2d404404015101c00407038a0614002070f07185000182d0040785c04001d16 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 821424127 1250 821422877 821422879
    0x7090f050d0b180a1b4103030c03041805090f03030606210a06150f05070f0203120c0a050c0409120f020309030a080d0506010504060503040602180913140f0c0f 70
    0x40c2281c1e40c10780d00d030800e4840817400c000036400000020700c1620100c145005900c1101d544108072451000300d034052000200c03007030040f82403400c3c0303403840300c0c0d10f0901c201c550940c1c01c041a242d54031f03140c2c0310303400300c5100d6840945840b07480c1078001001540c0000c2d4081c8080d848000035419aa03a000400c115640800c0d9244480711500d40b00d1030307561810304003141c0900042c020102c1d0321403c21131003d0a0840400c802e03802c01550110240c0213503001310455039503541003000a9501102c030700229140c00711514404c0360b403040000f030280d40c081c0040f4165110521620035a5440008002080180c81d0801400792a00c2c0d54161900751290294044640381025070041c0c17030810988a001030b007010800803007500c0041000030500d900003803a10a00e6400802420190300b0a0f003803c0d0b00400d1400003d000511481d400201260350101402c5559641c40c801482c43d00c0038030b000340b13080c0301c03e8940880880c1e50455440c40030b10302041c0818889610707000e010040801d001d22208100300f4400c01c1ca0f0305 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 821425377 1250 821424127 821424133
    0x411031501030f0b07210f06080610060f14040b0c120a0c2607081b0a1202010510050603061c02100e09070201020414042307090f050d0b18 61
    0x205200388058200203008600030090040241920304102c041e00300018864810800008003a003441c0929a103410300c40041d0b198005900710600091000620054120000500c10b4000b0000d141c500c06010100380c0f1456580c00d294000205800d840000f031400048c07480c02418017062100881400240c540d1940c1407040310044c0704441842c4409a102c20325100006244600504c00e1101c40460391403000c9041c910581d5074002260542414014101d00910309100003035003140540404c43c40e441402c0c4048150780c4d81d51503034a44000a0952074102e1805942041d000682220301c0c51002320480c0c0020b0b04c140d00e0341c1e50314410400c0d0100d80c0c150303c500d00d8500c1808500961036140307880c1043c840f50303141c00d0f20380d64001c403c000306050010801d00447e8010441842403070072060300b588040d902034502003141ca02250b4581001d401e070040416007a01ca9900300102c7c2680f000c010000ca810740102a4079050310b58017840128816506d0140c0303052003240105032000d80c4000c03903059404410003a = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 821426627 1250 821425377 821425393
    0x7051c02090a060305011719140a05060106080a05060409020d0210090b0c0d0306120f030f300e0a03050405090a02040b070501090210090312140d0e06090115030506041103 75
    0x101c0c1020315400c0783c0002a911001449119200c10740808070b24004001030250318101c0100381400c4a05403001081281c1d0070941e000c800d1000c0154040c1346a0000580b0070540c1c4402c00200131301c0c011200005aa03040c230010540c542401d220704c003030654000d040b00c48040040d40030b01c0340b218111041f1b0410040b40000c000f81c22035896018015200710000901a008080780000b810340c0c110b50000c40c8100300100e441400580400001c9081c983d05041c0228414040c1609039240030080c200801944000700c501051407055659078441230761034850030440c810381d200e00305070794403445007004003c01c40820040c4207501c1c0481c0300540c010200302015261503141c001880050b0801030003240c0e039a450391580d404520b003002d6180c0083e030942ca0f0a4100a00c1d640b40c81c4d64003413110f03003c04288011a904503215170400c0c0c080301d4100c8407007141841002c42000c00c072a40c40f04100c0d0180d00d0f0354038004104004101c903610460850350010018921510780d5101c109000c031607419000e41c90300c15542 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 821427877 1250 821426627 821426629
    0x609110a060519030c0504090c0e1e010f050406120209060403080c03040e0a290f120d021624030e0a08090f1f030902040905010905070302011707051c0209 68
    0x4280300a4051562066101c407820510300c0c07010640c1c0340d0b0040c149420201d04122030342d0b124040d20100c1e0305508000c82c51100340c22055401c040030364401600003049051104840d201e0b01c80700601c0d0700082e618080c0c0404041012249406a402071000261150a00c0040d0b960184c02034910400010f00c05894140d0b203075950400b50317000442d003483c9504040360400030640e1004602d907100c00c10303250511006e06280803d2266030120300100c150105038030002d4134191111080d9015101c2e000d081c0403480000f0140c0c0341d503600740007180700c00113209100a080600340d0500c4008110340102c495500000c1e00601071034281c450800d0428109541c400e4004011041002481141070041224903a140f2042082c483e00c0c0b110701141a0240141801000003045140c006403400211413034000342d9003026100050181915480140c09036007000000340510002040c4503040360b1007603c0c0c841c1c6100701d844030403121000403148100071400510030952403812000c0d01c00c00e00d40505800625112500e0 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 821429127 1250 821427877 821427889
    0x150e070206070f020106080703030503090c04051503100e06161403040c260703060506010c020301090b0619030b0601050a050403150c020d03020f0f070c08030706020a09090504080304060911 83
    0x4518000503400003040c418000e4011040c009106658030080c00b4160501a0711907a99001e4400241000702c00000030f03400c10005d00001a038144014800d02590915540440a5854100d182c80c80b85c0550b070358000b00d241e65842100d000c54031480c0a40900d40c0d90580401d083c551045c8898184132105c108001907084000c01144554400d04111400c0f0382403240d01000181a59044c815554110103052440b040006021f000c890384000045499942c04004030b558007074155000750150300301203001d000c016818640c2031080501717039500300517402e41d240407581250403807002a01003040302001c5002c5520032001000c0301034840c203041d45001c0e0340340d9820600c1c08110560f41026640c42c00c11401c42e0b0f41c18407021540412524056044c6900003c3c01449881a80c5442681650025519080144d002c41001c020030440007a00d845042d1820103001a601150980000403680e10011030204000c1c82054080c0c0e0f00b020f550350859803550703295802051540001c2e107020607440c501d000c0daa030b0f0b80 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 821430377 1250 821429127 821429131
    0x60207080f0c160501082502160806041203110d09022d03060604020c120309070902070c1a13090e150108150a2d0603083118150e 57
    0x70100401c075038010a07038981d81c3c1d18416080141086034043c24026007144910002c034650004c20300c05840603102402c1a80b51a006014854500c00d10aa0006007000003050b0240318034002c01c6400d00d07440c540c1f80120304543d010011281a8402800402c07030507069a40001e94007880078100341e50060ba030b0b031090064035070782078040c2405008182000740e450805120709500600155030650074249005811521038400d0300b0074941300c1d03201000141c41d00504002071001000a0030085545900f80d0400c42c040000340d002d20200700c00c0f986505505094100115440e2020741c9521107404c600b010010b50140c42d0186401d2103501c0390072400f0b0304407144407040c1402400194020000c010303101d0102200300300300412010700b03e0301d01000c0501044d81c072074003840742611142601003c0f10102c0c540e90300820a1ba00081c019240200313004811048680480b18000409481081d80b445502900c18004074603005400f5400b4224490031002001508105d02400c0340540034101c0c00c0d1034070004a00309800b = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 821431627 1250 821430377 821430397
    0x9050a0305031506040b0901031803090515040e090606190e0c0a0e0909060a0c03020403020913080d0219090b0304050c040f021c0c110d0e1e04020c070302040e011503060207080f 78
    0x10300c50310541e01417082c03401c0d091048104800d2b01c607441e10f029040040c14818280283c41c0d2095003900c803440c1d103040f2006007808030405180c40c00c10b244002c2c2e0380c0c0300840380140658400850310b8020401c002c280c5049940030219074000345e4824500007ea134006046c06810311404101c146a246e490302c090501c04c46102006001d00c0c034010742d540c0187c030b010352202000d040c810881400941c80c0c1c0114641d01803801f44803241c410800d441d00d001d2600c10144080d021501c00b141d4188100c4400246400294803076440c1c2c1d20051301c172003003100c1a10056400600c00c0e03009950b03a0b012420603030040c4106030304031900141001c00c0074408003c0e40011905001180741c1c0c5480812100f40c004d9a04401103808038010020040d1044016050fa80300c018407502c10150850308014500b14180110b4807008007420554481c000d15069a6941080740400c9116600701075007520b2214051107071684403000303614409009880d50700c90f04000e50200c1000d40b585c442c1042800203201030f500050680802c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 821432877 1250 821431627 821431649
    0xf060503150910090b04080a1b1103060a1e050405120d060f090c02100b0307090c050304031709030a180f060c0605010906050d02062d04081009050a030503150604 71
    0xd40000c2180c1081916110100454604030040011440c1170742d21030703842030b4030141940d1358100440090754000c03156200659100110003078a8204110307070b01c0c44500b80d10709408a8100362101c40d080c2d8282c8005111103581030055032140304c6101c10582080350002d010740b082da03010003600d01000d00c4c00d90c00243c2044009131596001c00110001240c0e04004143c1504100301e540d80c03d0710300a413601038203055101c50340d48a0748100410360301400440000c1055140400003443c0d900000b503c2034100310340944c0883c0d002000e4a0700e404001c0c10091140d045d0030050340c44c21205060950f41030042202c20082c039034404202203078910b003030440ca001909540e116142100f101d854180140c3d80c1c16001342c00003504040040090f13889140901c1004c903811104641c40c0c080b0849000001410300402c0e42180c0030884604c04101c4e00ca50041c415141c5010582d42d0321030348a80010141c0380620380060250f80401d0000001c24807a001a50304a090407604410401c41c807000100250420b4010912440c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 821434127 1250 821432877 821432881
    0xc0a02070909020906060711060a0309030e1f052b05060a08030f09220c0815090907030209040804170d080114010c0602030a0b0d05070314030f0304060f06050315 71
    0x5501086003600900407448103102c00780095000c03566044025100301d0150700c000c180307030b000c000c09500200b040a80c0500700310b8890041007001070180c41d405005501003400320100b4102414442140c039040e0b0382d41e1207035201409230340b10700325210361080c080c2c000000c0b00035021b000e079143c001c00620445284540b0214441c100002001415101075000344034552081041801c1100d0484c180c81504000301c43c00301000c0d500d5001c881c01d032004000308404051500c5d10030390802d50412032480c001c10a80e401441000f04810500c82455401c0d280d4110ba41c0c0010410030040c40c0281c400d41d84148102980341c04c2076900c0d692202c0324003090200c103500f6000007814a080b1503001e214280104401200300907624a50400070f010440a6140a0706094000000501445094102a01500d000392a803240c0d01d019040036034507001180412906070012400f0103440c02c00020a132181d80c81082c2255180d0f45590343d0311001031001d03050a2050503280e02000401e0340e02484180b101803200c9401c85298 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 821435377 1250 821434127 821434147
    0xb010326040f05010810140d020f040e0d08100e0411010302160c0305120a1b05010204050a0b040f05151926040b09010203010b040513020f0301081f0b0d03030903170c 73
    0x41080101030b2205102064010000b81c0700c48022444600300955208c441d4030141e0004c03441504818509540041c1081401c2d00410000203511700d00640c0380d500c0303406503224841501d0210f02e0a102d03140000c0d0081e80032070080b600410101e5100041410011325011b080032001c0c6c08840452420b450f01c4030703403010400c01c3c080c1c1404070b411556840041d25281c06410b03440984082c580d400c12900c1601c80e01c40d05001c010096045402404d4014400d031400ca503a071a007988035902c680928031003950903e01c005100c0c00c1400340885050441d050060030f2450b00011003484074040090b5004018500c07290a219035100100e071003489151012080440c600b50800214121000e0050320881e8410030040003000001d8042d0f805a81044800a0b800e400715821440030f80690b00b0f81c0c503441f4100000000c1c28000c0090380d1a00c090100d03007800208010b41e081401102d68006031190022548240d55000900c203900c21b000301c41c0b107030400c8502d046640d030250740440412a0201051240050b000340750b = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 821436627 1250 821435377 821435387
    0x12070f030b0609061c0c09111c0603030e09091903050d0c020705092406040801090201110a080319181b080a051c050c0d0215070c0b010326040f0501 65
    0x102c0308041d6050900ca04000d400305403400034542c002811030585120641c104140d000c005801001d10b4002405881042034031020030754072030a80014200c01910480100388840d0050404480c0c158843c5110801702400b4007001c0c190007040c42485010302c0145c100c1d50030041c407200c1d42043c003a507034142d182c01d0f000c0750139000c4460441d400c03001e650040100f00943da807400d020f00e904c480d40b45402400c907814002c50f0441004112901035000c00045000310300c0980540c42640164002d0784ca40769150402100f00b078841040344805001f40703801f000000c8645024a14841d0802070181c400035105a840c0b150000300b003002607044641024000001154841a58402002c0c0c803404000e007100012990f42c050b9244603422070b0030f10101c44440c0b40302525000350140d509030700e516800e0344e202c0c040c86c0c40020345a002681041b1040602c890202d00b6940c0f05840000100f1341c410b140c002d10764250f488402e115510b020903a07804640c454603003004440c04801400c01011007511690a041c103113400500 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 821437877 1250 821436627 821436631
    0x1626040311030a11100e090408090405010f08030a030c12050411030d020f03070b0405120a0210050c070305072406030803011a0c0304140307090e0c0901140d020f12070f030b 76
    0x12103a80f00c030b030201c4040368502a82451044040f1440310310080030504c15160900c010720410350004132901044207120011000303100c91007084808005c01d03030300c40c00711290960a0340a114500e51051100e0900035000394004503101900742040e540610744a6000d0701511000c4500f01d0301c005a07410744040b1400d04000503000f00340d160002d441120216002c03a40d4038000c002c4040e007280300400225060240502461007001c1c001c81c02d0b50760358227003c500a5524445201e55aa8003403810000a000d804e1750002c1d200d02035030607507625180c8290340c1c6601d09800181c1450030091010303440c0343c10300c210071845810011071248590640b00d601d461083c00c0518105125182070300400c02c5500a090004402c0300d040e03d1401410300400004900403070b01e8602e45810035508903203032600500c0150700000e03500030480401c8035002d03096a00e0b107107002c0501d140c4544e910380000300d580d042c1c00149450307000ca02020b007020701000c0c0f0b00750010380700616007280c2e5841889111505101030040c0503000034466 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 821439127 1250 821437877 821437879
    0x1209060c0203210c070b04021801080f0d0804030e190503030418060b39031206041b0210110f1b07140607060e010e2d060405031626040311 61
    0x160b442d1501a540401070303c5a445c3c002c4c1148031300000202107550346220600c1501030040005025a10b03080302d541e646070801d85640e058420034440f588014480d4418900c01d0b0350503078031500708841e401c043c400445e185440e400e1600e4000400815a0340f800c00151005041003030355018400e0100c03410600b2102645c10001140c40d04118120480c1040c055240741c240030b91884100f84c02c4641d801d12061034108010158034000003650905d200650f0001c20b0080034211010003010341c2010420070100352100103840540c1001418031100d9804d688807038500d03106c00f8802032030b04e400302413586c6a9a0001001240c1c902c400d1104c180c0c075600810514000d401d0407580b418115112200140b0507025010300207104039110b2440a050400c00c0d0040c04010904000b280d07841401c00000307003003580d450084e8a1844072240c1350f04190f0000000d181380540e80020145103018441c600040e611241d442058462a4450214080b400300c40c07440d0304030740101a524140c84a0651508a8500d0804409a = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 821440377 1250 821439127 821439187
    0xe1e10091203200106180f200a020a0c0e0a0516301802040506030334080c030405090123040f0f29030a0506071209060c0203 55
    0x280894003940070628901ea4050401d001007414049200408a20014000e0501d500301180020700404403006541d401c0c02e09601401008040010141101c000182516200480c046020058800c6000410800245105130780c0303907402684541c41664031650040441e1548401040310320303007007482025003020460f54010442a0301d141c0044c4032900d4443d560070140c0c214000f11200540d00e1980e0700300c40380040020702810b4400c00d08000029640c80059008609140014215142c003004460141c00340c030445001085002c01c81d00b012100e40c007414242950000d00035000308070140050090541820000c1d651a82042e003403080e070329010380c0141c03030070004c0e101c01c2408906e10182d95411050181e0380000e80721820316146014010f64540301001c0c901d0032525550205100c12081000074040c1c255984d13811487c0281b6503241d5800300c000e032540d0000004141454403880001071200c4540e50040b130300100b50344134034003154203ea105001503440024440d003500d56400e41c9284100d951011 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 821441627 1250 821440377 821440379
    0xa0302030a17121915060512040c080a050303090f03030c1b010b040c030906060b040509190b18070818100b0301060e15011407031409010e1e1009 64
    0x86075446018200c020300c0341c11010000d402501c1d031a002e980c00291400c2030388442d4282503822620308145504000c00e51030900310800039282241510a044403c02d64401e491712124541c201e503200c802030300480c0c070440078410025400c8000c2100340011802400079569070304040003002e16201700407000780c4c80e5030002d008000c4035840301000c1c0c42c0140c0c10094004284081d100c6841d0040045c414850750140c41c06864418040c0c0c5a48407140d1903200c0c0c0d0003003200680f58041c101407802603104882e03000c80e141c2300250340c2020ba0420b03808000300442011880c60611030000b040741d08030580c415282c074100002c1000b1680c2c0082070b9900029590506c03860390742d04401040d107c500e415000c0d44002e4403060040d5041e2000d50010005181c034085030009410300740b01c00c01001032144c10403800a200203100d00301d8010303a0421580c1441d455104c0c8003c00c90204030102454002c4045281800a07420a022603901d039804031030441550003d13100c070000c41d1481081074200d9000704bc40204017030210 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 821442877 1250 821441627 821441629
    0x303082508060d1b0602030c0c0405092e0504060b09130c2102060f0310051e1504030b090606011e083c0402010e0108040506060118050a1806050a0302 66
    0x140b908a0780a9802d40b45900341410021054448140b9070010040c1c103a200050142c0e001c40030341080c412802c00c1d1032080108c002000280d99090320b03500566003143c11081c860308402000343e00c8801446101000400034205440110f403403c40d02540ea035905c6803000c0d034491911840041e4800c580b1b55030b10010041584a40e55030708100c0c00341149200f0f01050f0399842c5680034001803040c07a80109020780d6a40f86403260403040e081980c049807450381204020450b4030b025450359103400306801703804180e03c0c100e10410040c0c40000d086200440740800021010a400e00c882512038a540002001c0398100b01000405404840320381380d00e07506540c41075040555010a10307607003140e0345980c110082d82c102d502422400030005071400544074064032500124550000b113501c41e80c000d0302eaa17074004521b00010342d894142100d000300160040d0000a5842d030150110700342c210040d641c1d481c9240d1716180070544462181c1c004114060b0328403080c4143e032040d8000c0f03102415045c1c03030100c06186142c3c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 821444127 1250 821442877 821442887
    0xb091314031c201b1207030203090f0a08100c031104080a1a1b0315030f06040b1f230901091a0d03020606122d100b0604051c050703030825 61
    0x458211008281210380b01041000c044038101c17044400350340c0c184610303000c1d540380d10a0ba0801e0048810b403440204a1500c4440134080700d01110281c04c0d004294100c01c00280308868043c014580c0e00d82147d00401102c10140c4007401d8550018075000400d0b080106c070a1481503050b2456400744030401800802800c2e1440700340d40c02c42c510030b4a03519101420307281e003254a80f0503a09032140491002d1105000120f65001c0c600403661500c4a464801119070300c270710b01c080c00681810000004004030000d920300980009141e882c074041141c1c002c0d00103002e0410aa04c1086042e0315a8001980072401da003010780c84001c00ca800b04215003041c0d90180d1500d5006102901c660825184690400801d00209466581c40c85981c1d0302c00070018540c481038104004204401c0c850340c20003410002c000d110700089240008c5c2205d051614010030841a81e88d418120341c1c15640c19801c000028004010500144d40300b81c40f1000d891509107507240b040c6280c0d10f0014180300250082c1014640c100c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 821445377 1250 821444127 821444137
    0x611010c120b03010b060c07030b0c0c1911040501060201020a0216150e010c051009060b06090a140d080f0406020f06010b071704120b0a0c030b091314031c20 69
    0x1200045156582c40740040c0c014510340d82c000d034005c140040e24803104c80780880c07c4001d403842800c000c02d254881800303002c03042c0a09044000580d22007405e641c080c11a5151a45495102e0189000d0511154010505642c0283e1100002d80c1d004120400d007250140071402c540421118011451441c100c00789010001d80116941403084284201c090340e441003106c51681500142150303421603482c0703107520003084110425162540b40070140c44040c6080c20854015000042c00241e98905086010503482068250035600c03403000c0740e0300b80004505002521030481039082068071a407400768041d00340340c000e1030184865000500140506070039030050760703402c580285009076031a0141c07803020124481d81c1c1214040c500145500820441c0422070580700302c1c02140248200c040054003a81a1080c0c40419a402841c1e0300c00143d0300c44041c1101480f40c0e010349911000b00494001150460713005003c01d080b01400c1d5a15000307140312070301403580703e40060116049410480c0e19041c0040c011 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 821446627 1250 821445377 821445407
    0x1080a05061c050606130506090601081816140603041502090609060c01151a09190306180c0e010f05060703170705040812180909010e160611010c 64
    0x30354008602652038000003032031000d1407034070074040c4110a0305241d40ea4800884015200d5003a550100c00c003403601c2c0c0203082c0a0380c4013071b115025541301c140064a4025001b0079241c0655a42d400c1d00b80032010400c80840100700044603c56006d04128000809940e1102c1145c0100020000d010004600000385201035004240068a80001c03000007011071040410813a8040745c045440e104858065100c0b180420304465002d144a60701da48208811101d10711724810341005202464060900c280c80c103640034007480c2900603194580d500c0300200d40a40703043c03184001d00343e681c41c410440349868560280c6414500711a0300c1d850282d1902a00310a8000c072401a0030205140741014080c4480d81c21001c540d1038042c41074076008000410f190024882e031180341c0f24140d1416960004482120f162945480c9122100d00c400c1040c40f040c90780c003070032102d106d660302c034060307080d6010034004035040f1450010001400c2e4989100104000c6555403040b866915007541c02010340c1c0c10622401859103 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 821447877 1250 821446627 821446631
    0x61609060c0305040e04030509040b0f0a09020711061b1b091b1e0a0914060a201b0909010c0f08180f030a1e08040f0809120f070501050901080a 63
    0x75091904580d5400303140d1040141c038428805000c101904440a04030f46030080c0d17820400e030880c081c1040414114042226040130341c0c0300c000d10030780c1200d070010031850340191119900d01d4030a00119106a02070010404410709408801c10168800e001d4240003e102d800c40c50100418000044c0d00981d02510358441104054561070b00803000b101600c1001c1ca01ca201580103100d00e06482134580d0001900a00040c441e100109100d201e10160000c201000f038400c1c1d04250485105882d4101c010b603c41d90850300900d401445020204450341021500c00c1c8003500d10341300202403020450000d046102580d0520286100b56a48071680c0d2100c107100b1702c0e11840c1902d4043c01c1030965140c842c0312411501074202c504d02d6051001004007101c050030340d1165a07001440c00360b04041e468090300080010004804140480c46814036403040b1030141120342d141465490018407003c04c40080344410342c1180304149900d003018406000108000e0030300500d003894400000f004140e0003402d04940075 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 821449127 1250 821447877 821447897
    0x509010f090f090f120923040b0d021203043f06020408070b220506030a0f110a0815010525140307080d060803130b0a2a030206160906 59
    0x11029811400300c1940200b0111004040c600781703c240003071010030100201d00b01040009a4100310128003614403110b0700c01e0703010070a00000f004080c26151290350b84c4000d20b0100c101c0544d86014640c014108081c0c000c41c2d85510301190141500500e05845510320007640c69417000c00c855400e02207071101d001c050701c2d030300359440e10308075000307014907000200070b031041c00c002007150240d0030010204041074034503801d10550400c18080c8801401d001d400c0e004402800411240480750b009540c27604003100300426540104a500c00150b007012a203000080c00740070a0260112280000d03103200c038820318181e80b500905a00d0710307070a6040400754026070802c030a8a0000c1c000074035a401c0060000800392551107505040050b0150001c1070303510f0b0b0251034040002030600e800400c48080e02030001e5135100e00351800c0070407201500304100241c24000c0d0b03039980c2e22100d21240c203003500c0c292380790f51908000ca5035800e009103416002403044400c288001e004802c0380d0b80005000301107c4992610081103 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 821450377 1250 821449127 821449151
    0x803040609080315151603050a0201020d14161403190209060f130608070e060a03140702100e010b0d0206090a031410180b0a1805071e0509010f09 64
    0x100760303940e80606000c40201c1807041c2a04001c49049400780f040b161503855025448a945c3c4600c00c1c0406c0c00032000035100c81800080c020b001034a00078103140001428104404404425200000499065441560200082585100c01c59540f030a480d00d446000e06200313000b029120701c030103000d150804e078038408400e42c20803103501210515000034164946400c00300840f9080c40e0446030042800340020f500103d0842c1c81b44490300c1c07081c08070342e49104c13035004c8e54402c2c0066a801040220101512142e10343300407140b10340c1c546c1c011003141d4024440401046000012900c0285010003583d040001075103880e95000d5185500300d40480d4500c2c0d84004081c00241a41e000386d000905920f1501818141c40d0310208042c180520702c01d800b0b11089943c0e4801b02c0ba5503e00e084028150340800010462584150344413560300480d000c07070f0100340042612001d140041540c01081d43c0c4001e40302d1200307a180c1c4000800c004050aa07204141541845003800300c03400075008020080d036442c070b200c1b030f01 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 821451627 1250 821450377 821450381
    0x61215020a2a02060c0703230601030f02040b220509010c0210020c031213020307051008150103110d0204031505040c060815040e0c030105061903031b061103070f03060605040308030406 81
    0x2c05907000b0200c507941d482c680c94990300d8548600c030070b44a480a44800e100551203600315412000b108031301403c4981e00710f07030719034802100201c000e9812581c4c0d0b11070402180c88990310003c2005642c1c0700480c103010700b014050103584000b00240c07096410701c02100e88680d000105032007000092900561200818010329185014070885211940e04582c1805421182ca440c0c10402c14000d0f8161082540c0b204244284400422203080008020500244002c0c084000c0c44088000500d40031400c020185031616660301b100c0080401994005000c100b04001c401c0c00b100280d5140c4001c0c050340c44c1646034400f83e0348891060f601803040600c001200d501c058a030b03074544542c0040c8100075640550210545c3c0d000c4120b40e0750f02940c42c20b000f240191900c0c502c8a2085000004034240e8a4151b5808503034200302d18000694031000000c1c0180014224003c5070202a20a618103442e458903400c02013072054550b480f0000d062600109000941e40302040790f094a41000b11182e0700e40b5140f4081c40 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 821452877 1250 821451627 821451707
    0xa021f09270524040501051008040615080f0f010902030a150e1615081015020f011407081006021506210f2503170d061215020a 56
    0x50700c20315003410000e0000384075614030300324121195820b10501ea04800c0c0800c4640a015442d0711900c0104011300d500d2180214540c003d100d1500402c0098031043c1813040400160480c8043d83c00080c94030799001400c000803031950a0f0340b0003c0c0041940758001c240c40754000000548204907409401030003590703603080515100325807402c81d12281c21180b0b08034040e00150003404d204c050580003250701d040c819003079140980e039904888441540f03416860311114110004000550094081500544101b84200310481c01c1d00e116444652034036074002090031400601803403076688103130018004698000358074218440c2d60044c508450304d4040000e200026044c0400c0380d26101c680d110031002c1e401007800c84521b41c03980101c485400c01c50703215a001c0a9216490081c0d2481042c00300041103096405401040c20a00390720718246004900038241c980c0c17a0400041340480644000070040813110203404041071110850411041c00d0006241608042c5103d0a0dc41c40d40c0d02004980c0403516050 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 821454127 1250 821452877 821452949
    0x1c0e030f070b070201080a0b0906040e010908030c03010905160804030f0c0f051524060a0c08070606140117150310020409060f0602030403030c0308070c0b0106020a021f09 75
    0x58500355442c44460019402084200d0000d0444070111b02d1440c007900544140680003441c2200c0c43d6500c00901c0000c094a1481c43c16541d00c2d0049100411107400086000f518170181941d5298142080038007036079801f500c03c51000a00c0c0440005c001d6001c0680340d0015030500c2d026244500303d0701c0403905402c084070090080c1c0301c01c210010401000056038240354800888003132442d5900b18407090360841e80b1003c2d21640e50500c0c07022107945000c40050404201305d00f04409100c100c2d4680b900c03580c000c40d0b402c440859950b0800c0c01a04540c160381405460240b0b4078034281c004a901c241c400442c090901260380f0020a03044c8900d507000e101190009040c0401152100d58919001d00580510702c039001c50034540070700114100e407000c01240c09680e0181c45d1585800b5003950101c808201c02007130300c01002403143c10711002602d648007540c001c201d03960007000d0340307003540c01040218a0b00c032a80200c41c5580319200b80805404c1800c1d481107907060360702c09007a540f8015480c0e00c04000b400e504 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 821455377 1250 821454127 821454133
    0x3030f041401020d030b010912060e1c030b040218040504021311090f1917032b0b0109080607030c050c0303040308101508060607110d231c0e030f 64
    0x811021225aa110a41d0780240e0882d042202c10020a070100ca61150810780010502c45051040660740c4280c0443c00b8810740b0001070404200d0300007400c081039540c80c0b40c40d44810580000f0315a5041c0195030111904503000c62416648181203403a04100b031071050300031900c2e140041c00703541c0c030b580f40704078000b8804500b8480d0100840e1002c401d684040c10003032041700e014400c207900d42014030b20201c0344e240b00401c0010490a1056883e2140401d0a60100d40c0c03004204640740707005d4681c84140c00c0940400c0c102e03a0803810061140680b20314441060410842902c00c028001000039025000103443c140007440b1218084d0446951049500928030781c80004240400c00d41e124031542e11030006680d00540700c5442d1031400030351403035120b84400050f2940001c02d62601e07108000b03081b0746104008001041c0c3d00d00c00440c4801601881c02c1e40c110189803024200c007002c0c14100000c00c41507602070040d1070a44000b00c541c052414594008202203003c41c00c610351001c0041004c124030319421 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 821456627 1250 821455377 821455379
    0xf110105070e0a0b070206070b0417070501050106140a02070e090709090b040c0b0f1215120c0112090b010315021e0325021f0609020d05061203040f06080603030f04 72
    0x101508041030501ca19002d6880030200084144c18442541d0265034002d007402d00d0f02c071650711031400c42c0402074000d0b01c00d91420103e61001c542010001c04007203201d42c00128242d0300d4214040d00039250080c0f20054100304011602c001917001ca1b80f0000d8520f10b00251805444080e1464a0908550441303049240740450100a001e17204c0307852480744c1d02c500041d00340c15403600120b440310b00a100d01081d1015040c0f00f040b6541c400500d0a6500003205001d40f116000c03001e0000e40d24041d4980c681720729030040b5600074195648030505e00c1a020003000b040c042d641041d0365200308040e05110142c0107000910140002901c2c4d50100d5082548a00c05030410b84050b580191841d801030b04c0b0112000c220340010703100d0f4441d0240180612110750080c0003400d55000000361025a4031010402d004d5840e2408a0046098405465984140300e00042c1c00d280900c01d11401c0500242c40200f2a48180001c001c04000081c01c40140c0d4558075084110703403038003c0400d107540203188900d6201280410 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 821457877 1250 821456627 821456641
    0x602041701020711010224060d0b07120510050a090e01020706060f090507090f03030807031401060f0e0a0819261c0e03190c12020d090f080d0f110105 66
    0x180014502413000d4900c403455003001640c0d80e050340e0701c802d07d4041c07502042d080c0c00c42c0c4038882c20ba4440005800710103030320b40aa503130f41c02c514011219100801d0207141c1b070000a000620426510000c2d8002610446060400040381046244200104607854003c222503c000031740540d901282d20a200340305d0151540528100501907000e2001d0507443c00300041c00b13a0740b043c40205c08442d5001c1500021904545080b518404000d100300189501d03000c0c1c1110f102080010385009020641e0765001180000308000c05030a0340105a81c800e4010050620801d1400724032080d0ba200108030b071411070f1502e4601402c003000340c070496000e0400b03101c2040859106080080650611841031000c0610490710308030215001c5c25031808465206214094501120900c01d8925155604080c454144541d603038940d50b0541d100d40c0401600004200d20b426604a102080540b106d2a006034506040610741c40e0390340d00c03100d40b080401c0202c3c2c3c030b6018954064114421034a021400a20061030001c03 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 821459127 1250 821457877 821457881
    0x503060d020a1d090607050702060403021314090c1008161b0506150a080109150c050f0f090f01021903120e1b0f0a0807052e020105040309050901210602041701 70
    0x545104c0a07000f01000580d62034840e20440c0da085900420140c2028207503020b1011103140c0c4100e00c014555580400e80b00911303c04c1c800352003600f6403070040c030705040d2100502100c0b101c41401442440000070070302c00030b040c614130b00720000c140307078607044400c81d0340380003100c410301404100500703107024580620944013094421101d94003c02d07100d50060555a4401500301c44d12950090075241f08200e1203151802603421000c0700304994607289090802c81c03240c08603190f105201e9001008000070303801845003809910010003c609002800190400c1c41d20440b04a031000f5004082014110510b0002e170540e41c00f240c041003401c0119100e86110401c84000e0039039407043c80b0310420401024100707032302e030001c0690141e4043c00301031320700c55160038240160140784901034003000d011908030310303165006000d01003040902070b4000714060038075080207404110b868110a010307004c0c80c0010b110a10385c040310410401450750030408041c10508040000b07000f1a0010b0000c504c003c3e4215010348015 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 821460377 1250 821459127 821459131
    0x905070b1207090b03040b0f0a06050303040902032215020f07080307020109030e0a260f0105040b04060b060a0804242301091a12070302130207050f0a030503060d020a1d 74
    0x240c440f00c0f0352584500002c01d040c04101c0c3d0046c1240300380400242c0c0a03003600d00c0c0d0740c0c01c030031000b00100d9029140e00c002803d54000360000013070164007004020580304c130140c0302d012640c2e40c2142141e00044549811441001e40c8180782401900010041a02d0214504a9550a81212609880c0d0030039410003400791986d101c041d00000d0f0078200e1203090345000000c010807070300041c85150304000300349210b6030926503000b0310058038040d0008400c5070120a01031180f20314441e0301100c10743e01d8130785049404c03034426070600c0c0e006a2003888040005504000c1c46034000d40c06c00448000801c0d140d241c0c42001b808981d45520701410211401c1000200c220f980c81c6d46060b140009c84039a807104001411185005031171006944100380c030100c54100913600d4000034014509980c816522900895180091a140c9141041e8002441410b110090140055290032940503144403030554a004000d40400790010780306c0d4101c451400219a11113102d40000c145410903102c0c01585500f0400b01040b007 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 821461627 1250 821460377 821460391
    0x80403050609011a010f0504030f14060a1e0203040f060c08011a1206090603150106120b060c070302061c11030603060106090f0306020703050f181c0206040302040905070b12 76
    0x1401c1c0c085184500c1c180501c440007443d042003e0b0380b19902d80d00450300f8480c000d1844007802003c210200c045015034000e0620107004541800c18030340c04d82481072801e10000c1c1804000c91404003600148421600c0e0280e9049010f10056266147c1c2d0034441400900c0300c000030052854101c1019421345c0124009048400390b80d003482002030140607a2190740303d101c100c0903081350440001001c51404403042c913006400a000c5071140c004120200140c0c460071381104021409001c6c5044c4500924058050694000d036416410030100030801a83c2d04610b0000a02c00c800200c1c580840c4a405181043c0c10300d60b0b00300c02e206c202115080028240d0042d2502c601a02594002041c0c2c0c90280719014201d0307075084da03000252403441d01ea0000030f400003c4100c02301f0408000715101383c02d00401030100100c0c644081c8000c048011304005032403071240da43c0b0181030130302142a000340e0384510594044a03015900032545804030f190081c00c0c01007640100b00040c03c04142d1824240031021406e20600c0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 821462877 1250 821461627 821461633
    0x31603022101060f0903080912010207050d0207050f010c050c010c051009061a030102120103030c0609021206061e03120d061e14031908090316090207060b0a0f03031407080708040305 80
    0x4c0c0c00c02c011a0720302c0b81c900003d440300e041044452002c0c204244500c1c5440b04000006040c07134940d0b940c0c030341844915080350b4011303402032006000c0f0b4a400480c0c2c0140c00c009080a8440c0b9078169211a203071440407002070b043c00343c20784041050100a100c40324000324490020400449a4686400204281500c010b00e00040700810740040c1014405c690242903800a080c00503032231594100e81041c0080412644903494001c01d20041e19051030025840e08180040d0540e450850144441030300101134a105031840c03508820010780300464407256060100440315501c500c42c41d01c0314040c100c01e074400403400c014141c00d140109244d183d8403094a40c1414140c40100c500410107944c5c1c5620601e41d000c2d2044508801c001620580042c041c094002d000c1c0e4100c00d440e8902c900166030150301c08200d203900000d281c020007803607100d5800c10007403c480070100c0038107150041d03041500c10b000090a0000d5404c031031410b056010b064403203040e400134286542c2e000605d0124040c1c3c0180c07100f1034941c4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 821464127 1250 821462877 821462897
    0x90a02040e0c090105040e04210e03010f051012210c1a190504021903080a030c02010608030a2604051608030909060603190516140304030503160302210106 68
    0x8140354007140e0710f81c48143d40f501c2c203050414501e40400c02d406003086030035884440d9484040d41400526103140b10700c648690b400c1c00b40302c0007450709482d00c22040b80784072842e0078100071043c0001800c1005907061002440303208182c40c50505040618010941380f02c03042e22540c18030320f60380300c5561402d441c0b15050a80d90031400da80b10b050542d02c1565070714440c0e6018110aa55519154070950307003e800108544d88480c10542c01e101480000d403c2591107080024030062442d0701070050158081c1e240c03001304515440c00d0402c84d168080c8401d00760800880a00c02a6118051a2111400b4221605038083da00300351030310a580e910362000000c0281150003002481c1c40c0b01100380ca00084000e0030300010380c2d035140108207543d0302c01080100000f450703581c0768441d40c0e40303441454420b000d0050300c0d1003611400000500075045240030050044c10800030040000d44c450180c81c0c0010442c02d008120314400c15081d400380c010303038000150f0701c021072200381a2040c840e04214121096511150002 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 821465377 1250 821464127 821464141
    0x5071e12120e1b100f021c05390c0d060f0b1f1205150f0325030506160c0b06041d030a0914030714030a0c231008130f02090a02040e 58
    0xe40b5a070f0030201c0503810000c80c0040c7c03030942c403861040d06480fa141c072900d049114418034903030014140b010b4031201d40d18651440d011601b0403c002540c0b80702c034010300c1c210391454002084600c1030f100003420070340c54017400c00100346a03070490081480018542c20001c2414840300648201c124010030003d40e5801800854080603c2010300035445a20f00d0124140329074240034a59041130200c035018801c2068851040a4004810701400304568504074a1465810090b00c1d10001030842c002882c6152548001c440d0031075170810b00039603c4044101d56580b1340c000180101034a090f001c40c1700280e4000510f0400001c0018030347c00206450307180102e5202c000a4000c200000655501a4807207402407000e00720701c43d601c0c400c81e003004040f290308416940e61007050000a0740103d000c20038034100e030481e1508400c00e40f075200d14141d945041c2c50080103001030207504060800c2d064624041621800c1c070582c0000d140c0705540281144a15041443d164802940075104442c4031810f000041482 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 821466627 1250 821465377 821465387
    0x60b04061202011b050607020a0309050a060206010626040308060112050c0306040914070807030209070e0d06050402061909050f06070807080a0210090305071e12120e1b10 75
    0x203650707041146180d5120198010340701481843c0b0030f4140c25031300d05240b400003442005028480c0485034064a000032182c035026000b144d09411191040316440c00500c1010b500007003490440e4203c0c45c00510f1a1800020020200c4070720160302001e840340410041450340060042c0e000e4102aa038000510320f007600200115102034410400c2940101f0106103180380603004501c43d1400345e0803c200000301280e14501c3c1410981c004101500111010010740c40c1c03010b016980080740e814107124119015001900c0707604e0120005081a950300042015034030b41c04c2c15a5a150002241e4807200098030300050001c0c403161040900c68402c2000d0040e45050400035501c240d98864006420003441c0d96452400d80c100f07490300d03011071103000c20115000c0da0900801c1c81a40c000d44616072348507130342c0c204116100701140341044240d0440d400000091140700710095a80e800d032800c03c03001d00c070141c40080a000141c50b601c541740b049064610000221650a5a403540b0840301c1c1004001115010b5039 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 821467877 1250 821466627 821466629
    0x5040b0a060e0613080a121701091d0d0806190305150405012a1206080309040b01030204051203030a14190c0210020a0807090f05031906020c0f0307060b0406 69
    0x1400c0200c05504000e000d016034101221074400410482c14104201c51480052981d03078804a1941c0c00402000706010602c0b0305000011aa40740c030311519100800e072350411031818880c02c00c00940d21450005000752264009000c80c0f41c581c00d417540ca903030208000741440800d6901510500c0e41d02c529210000368403840701d0460b903006010342800710425680301e040c01401407040d02c01d5500c1e8491b1036401c1e541442c03d954190104c0410301c50300425000b00070841204035070651000c62600710203010001000040d202c41e96000c8a001c1407031303804200100c0180c040c0343d001c3c80e000000c58015801041d0040041c5103e8010460100003021049000e840705610540d0b00d00041c80605180348800300082d00500d0103040140121001d120740145035104982c0482d61350b00005624806100303480f03503c908098002c007510b040b56412681410002911102c0325102e03d40051840c017140e81c2080320b00c0c4c0550303150390401c0064880e00b4000494158880d488000229907051404d121480c1c1442c2c5442000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 821469127 1250 821467877 821467879
    0xe030c01020a20121b0f0a05060304051c0203042102180408280206070924020a021207080d03051006050d0207060609060f12320a031805040b 62
    0x80941035070307501c1e01030340320214000024072500c4100f1001259140d903a0b05590520080008000b444011203901c500b03001c513502c045101e54030701060071290b0b6848941000c140c0e4070880e14141d0300d0b240d0349007017442e11042240c1d0310034440b043c10360801d906401202400450761078003918082195115040c4d840c1d043d600b00025400b0400100030400c81220349003d5502c40d1184003820319110f1001c00c25207503c1d004090a015040504e503182181d02da040c0030b8103401c03a129042140580e804c040d00c041d8080b00c5595102490340c0c80b00c0c00101c4151007005110001074000d840340b50032100705442e141e01d03200180a07820740380c4660000d00029a210f03110741d40c030a05241c0d820350b8815003410340480300d81d1320ac1d117080203800e0b80078000d034800f2803242c2c0f04060041040301400102c042c9800600881070b89641d02000d000c10004c0601c00118105402020000211584031442c011045412203282058118586030a02c120340803c030400d50030407c0050640b96841c1e80307078032590703540c81044243c9206400c01 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 821470377 1250 821469127 821469133
    0xd110705070303024614070e062716030b09010b030f060a03381302030d0c050303061507080310082e270b0f13031b1b12030e030c0102 59
    0x414030300341d0030000d61050900c81c2d08003501000c6000d207003515080341c0b03030402c444985000c400c0c00b80615003129a1050070007080c618119682b40c0e0302201c0d1090030000c01c2e50440b00e8110740c81e032601031300c29405200000d8005000380b1540d610340c644c1c41c00c6074000b1a0102908042070000c6005490080400000c490744055040848020070760908441c40d6207221400d0300c3c5951078009440e01e203800d542c541c82015009214403441507140101440d1140315410b81d4280810a212800800c1000c41160343c041401d49800d0504122307441030031210b1140754409000c2d05004007d010324200e901d03180c0750856180c00c044400030b00c10a84d5400e4900d480d100d40c1003244109042c980301d81d0426800c01c1d84110034420400c18413002c03e080070310301074034100e4044070b48000087c20003015102141c40d0b6508030300740c1c000981002c0e60540c0c0c064101e0003a000b10302d041d007103403800a10401000144240311260944640e0400f80c4c0d80d038060b0700410700c0500c1c0480200e08178000e20101400c000694250304107050b402 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 821471627 1250 821470377 821470483
    0xd081c150b21090d02070911070b0c0702030303130506070e01200a050106140102060a09120c060e010612050d02061012020f0402040b130909080d11070507030302 71
    0x104074000d034840e40725001d0345a40500e01e412000418032101c0e03c1a5a0800902508251100f000b41081c50715000090490b02c1c0640c49400010048150760046501080c01d191507140c440c901c0d8170500440500940c907200000c1007058400c900c00c4205840303407042e42141c00c90749070b000080d00d04155142045001403038510350010840383c032012840d401402c46040d281000346c2600da4900351280364000c050361240d1410640415641008950f034401c4c40300c0c0d010002c04400da41c1c0c240080c2c803902003000c100072210142c40300b401155400200c540e070302a0002c01aa5990302d130010f45800b00207006540354090802440c3d050350000c580e02d0310440c01039400448035801d000c401017160f030360302c1e0042c5c1c0c000c1c0e03281c80701040702d84842c401440030b0503408040c1915030600344001c40e050316a60300120452410245e03c00c0014004d4801d807040c1c101c101da808030303a00c440c0e4041c0071028003401c1e802901c1b51182010000c02d158010601506065888507413130001202d40d2119907400b0034a000300da000b0748800394 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 821472877 1250 821471627 821471639
    0x30307030209010318200a03021e06040b160605010501171b1303051b0d11060702060d0c0306030308070302070f080a1709030903011503050c0d0507050d081c15 70
    0x1c014094102c050600040c803d042c0c01406609400e190022103241001054500000896050040024404807203524440f803c56010841c41da8244c000c248003021703000941d1044e942e400e030542d0040d044019840352a000d82d098040394065001e00305852440c07034103001156551041c1c8000381c0d4400d20013460b04c0c2c03030344a10f030021070785e43d110a4403206030a00a01c13440d5501130f240c407030311401180100010702d0300380c85044a00c2c4542c52030040c1d140c840d2104101e680001924202c502c80c56000803100d00e078640d80540042001031103000d2501402500d003400401031250180c0c44902501e02a984010b0240d6503801d05904034424110007510903000d10000e14009044103005122040d41807400f18002c5080c2c480d4407081c040d0503207409442d03400c0411038203201d06091050525500c02e600344103002d03d01c0d40c0c070b4140d1070f100440000b40c010a010304004046c014100714038001000060851180400c042c10040721b130341c0014400c06a40d4810703041c3c074940c40720780c0d0103298440d26100034560903591600c1c0c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 821474127 1250 821472877 821472881
    0x41103060d050c04140f010501020d0807030e03160501090303060b0c0304140609061b0d030c0504140103090b10030605060423040302010e010606092409090207030509030601030f05070602060903030703 88
    0x8401100e1600c0382d4a4140095250341c0100a0020351002c41711145050140c0800b121314416001181198080108041c1c0103502503100b64025429060004580c00044801c82c254481ca0041080c50900350481d4410050150300141000b0b009039010840c1c00e84403030241c071075849606507800d4640c0c0113000030300c4a0240c3c076410180382240140200d24050790000452200d402104c2a140d00340340d4005400001c2d0014060480d10107002e05c0c0400101c41a00809012400f640c0951203030319400d6051542c0316406907100800303194108066103202d00c2c00c078103640c2c19600e047c08211107030f90520740481c1c9039003010300804641010406d50080043d6030345a442e444100000d10035000c564840d0f65140a42d0710a104d404050f1420f940c40e241c800b800c010480000319800d8200c8009006050b15480000c3c1e0701591000946070061000360707546000e03044c101d0340f0b4050204401d0f4035000f044d000008205696450502182c450001e0f2000580d440805030f0b01c481c1e003203c00815a4100700005400c4030711a13 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 821475377 1250 821474127 821474149
    0x6030d120f0501080d110a02061e0c01411b041a1e0c150901090c080d180303020a020108131208061c02130c030209120102130504110306 60
    0x414000307101c5040d40c02040030750340213030700c604025080300802180e000c2e4801c0c000c514004100300140190742d815404603649104a009518018101c44040085100030701c08441c3c04200ca48024004014103d542e40241c1d0100c20181c2e012550039030090070704c100d4000010100c030208851107803d551b60f52800070802d40d96042d40c4480100d0070800816420031244018507140e01105d12151281e1020041038040c9020590700d00081200f8080c1c4600003c0000380500140f0700d0390004103060b20f480098501400e000d1400908038400600003050b1030000150030010004940d071004504040651046a122024000130740140c2050b03400030090b500079500d0326008542810f03c4165010551514050205907400190026425030203000c201d180c14016000c01c03104c810b03d84051002030713a00050754031048002c214550358641001e071002c2c90280d41500c4000e4006854035070b031030407607c802d103000794400b0019060013135030f08001090a003024030841003003074603501c0043d155443d05000c2280740040 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 821476627 1250 821475377 821475407
    0x5100f03060e070b0712170c1c0b0a060e150301060f0819090f3e03100c020303040b160815030c0a0f05090c03162a030908010e0606030d 60
    0x60040006202d513048802080020b004c0d17080c0500054544000410800b03070f002c0440e0030014801c01380004103031b4040407122010340c020903030b00e5200c4c0e10172007c1d0058002840450b500c00d04001c00010030540103180450411805c40b0002081c0c0c50120311080c0301c2c0001e0046000049c2001d0614158600078025590003500390003200701e4841100940006442800038211400707040d044020742086510400306c2c0e250064001161081400592040740306841808041c048007100381240c1e907180c40501849410704a252400e000d40c6600d107401a5907580300b5501250409204c0000581142d49120000c1c0004503a54070704126032a80e0780740e00581c03155120001c1d410b01501c010000b40c0c3d961031009a0007855405c0300c0104c1c0328501420800c2100300101000d0042d40108104900700780c034031540008504041c00e00c0c0d003d1380c02c402000348014030018200800340e25401202c0c003c3c1034202001100f200d1402009008480312100500c0d104c00083d50f5054260b0b100d152140100c0e0f014401e80c0c407103828 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 821477877 1250 821476627 821476633
    0xc01030b041422080d1a01231804020c030c120702030d08060613141005030903070204110d180c060c0b0402310914030f04092a0e0405100f03060e 64
    0x103da2150860340d802901581d00b050b640d01d5001020300c0c107a035150801403c00b4206900c1040d48031307901024808031420250102040007503c5d02c012000c130340b90312000d0080a0070442d180c00004045a541350300c0502c020325a44560158603c1c40307483c400840e90443d5000d805010001e28100e01504c0e00c038005085194003100603c42d01550040380245d0324010401c468400814652180070b000b1400700c100760413010064204108101d0765000000c80d0141507050703400081c00c0c035011100f00f99502501121410650526454140050a05c5c4e0185591405840301044103503503503000b0364442016450060006084000007405450072861900001150107480440741c4069424004500584040301454503500d40080060103000c8104040d1040984005c52518403141c54a01081c0034074803c480c0050f450701007034100040c10540c00c0c8007400c02c0022a400741c45001c2d90240080c5650f0201038000c615190020741c88850700503603003007283c820401c0d4140403400d54a130800a001d40d4004003d841c8 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 821479127 1250 821477877 821477941
    0x813031b151b060504050a030e04141503030f03010905040209010f03030e130204090c17090625021c03050402090c19030e0a020d050706080a0615050706110c0c01030b0414 75
    0x10218000c15100c5c5105001510342014689005015500d440d5809400b03a071a02c04038400342c1014072521a0040002c035040d98401084100003882d510a110300e070301024102000000700b0b0300840d000a0700651089404441d10b0f030b00c135641e03c4031440f038510002c3d0018140340c04803452410701280c0000c043ea040c2501600e01034580105000782c3d8488109440000c0c0501818070320003110440c140d80143c0c44002a010b20709204080d0160030700742050240b40c000c000d0f00b030190100c0c02000016600c5407640100d101d90f5524007070103401000200c4090340a480c0040026007070003102c90807a0035072200300300c40103030340c000309a811002046281c1d0003400b1807003205500009030b0749010f0111009445000180141800e060008000200c0035001e403c0723032400d154050143d2038811401c008040b14a00c3c1c015210211401c00d07101404c00c802e140300740343d400081e209120340d80200c0c4090399203070280ca06001001081007400121641004024910030900c400b1a40800c0074103a040004101144080c03219 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 821480377 1250 821479127 821479133
    0x70e0301151a0a0801030b13050615040b0d080a0c050a020301061e080f19150906020d0b01050304020d020918060a02030f090d09060305060d0813031b151b 68
    0x681074280d4030450100005030821940d540644602c20070915182000d041c8803807890301806038030381800018800055100090000c000340d900140189402604071021414000c80c020950001c050681d070185050074250b40c1c45d414190440d149640d44881450324200c05030108848102d1041407c41d664054100840c004d82d5090003058080c0c003440d080d0080310a07400d0382000c59032645c3d5100017035640102081102c600004900d00d8110341682d60328100c00e0300203242030320488142070b000c1c1d404a450030361002c0c144003d6030f0150401e1100003c04100c950040301c0152814002100c00a510009009110005040408501d50081082503d1140f03004120342c00e10b060610403102c2c443c0c1240e001c82005200d01541440c81c0d00188040d01074102005c050070010000c43c054091034081c903444a021644944880051400160b00b08101c0da07160302055036250310340d0803144020784001002d10081a45810081d118004880a0240c0c0c4c9501c8000c54009030303500c80710800503003045e058020400b008 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 821481627 1250 821480377 821480381
    0xb030a0501021803070807052e09030302160810020d0603080406051201050109030201021504020a17100c020303090316110405160215100e060a240e060708040e070e0301 74
    0x980d100300000358454076a50102146240408083e0b807083d8061030307040000d1540468031206031841030341c200f890407445480c9081c03601200d981c1940110036000407031000d0b9600c848200c0540e88654255580c08104d4000702c0e14003021402240781c69042180c120305020816402002024507200300828820340d00c0d00c07454201d812075405100131500000302013100740030080002d805001c0c00d0038401c49141c290b8000035600e174514210400e201209901050942d41e400c180d00d001458450f01281c109030180391016100c0000012400c0c1807401c0100103280b40380044141c1c0d00c1030602c43d00542c1460600005030211054584091700c00d111020b11191480c1c4441c05034038800d2030280c54025038442e08800091800c0d0390610103440000e1a00d050007846030914040001300c5180744c10308145511241e0001da05c1d00d119500603d29000c3c111003079010003140303035082000c0440944035041081021b03c01e115413442503e00007040f100c02088244078a18040c0d803480c1d005015071a290f8030b07400c060b0300482e003 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 821482877 1250 821481627 821481643
    0x91701110406091502031801050c0c10020d030e0a1a0417040b0415090b040504111210030b090601031208090a120e040b010c1e081612142a010b03 64
    0x20003c1c200110a1085840089240541100e644000c44c5001c150000d00028400d40c540d00504100d00020460030030b80f0308200c6441b89240040c400c1d42240e501d01800703985c0304c081c0400354000c68100078410141d4100401d8100308185c01c0b09400a582e2030400c00440c000c0c200400840d20340a1445080004550010240010305031b032080c040d903514240510b40400c0c01d082d8000300d04010403240140041c45041041d1000c80e0029034002c0740150f140300d91344055000304032030b41040052030401c1105054040706c00208507406000c000800e13444041101d0703102d001c2400041d040c03d1420180503240d070b100d910041d51101d020400c0e03d680c91215503448001c00343c51810400000d000f840415102d2602d841080240a400d081030800040140d413040701402d410303100711060301d0008515500303010070310003112402d1020f000c03001014060341c40e001805403a41e20300e0200199214004441101448040750000803840710407a001d02503259201161040c0c07403c03070701341e03a5484081006046d182044221 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 821484127 1250 821482877 821482889
    0x130f1d04080d0c08040b0c13140f060f040306110f0316030e0307050105072c0d0f0f0602040801060e070e0d02010509030109051506011e030b2b0201140a0917011104 72
    0x140c1c513401c0c54201703051a144082d20300d02880c0010011514a00c20308a00842200c5501c0c100480c080b032120000b44a21582001c0d25070403a500040c0d204440cc0510700a009991040b00708009004040c0d10003061801054880c0541000400c00b10f40c100d1800000141080447d00d400300d050712044914608542000c40100c0d81d07a910f400c02c1c4000c0f5a0080f1526000c40c204095566100b21804885420030b200c1012417030103841c20300da06078180550380b4074501040c3e400020001c003410203460703c20000c1d0302501c0b0310b001a500c0c146c00800c00c2d100650060f03000c3c5005a070303003801c0019241d04100e0310a03c03951049061103810007075040151130030300030009017030300075409809882c0c0d610784130707858181e8010041c41c100b186014901c0040e201a0142588140603842c000034400d07201c50102c1c03441203416810200c486400c200040e4813038020007161148a10070b030f8852000310000d40401000d0f028800c8048041041d02e0303401c6c03201c01402c4903041d4140c0d01b814000326254100c6840d146640e40260840 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 821485377 1250 821484127 821484137
    0x4090204090f141003080c01060f0305030a08010e0408090906120f0304030c05030c030304210203030f030a14160c03021510050108070f08061e0411130f1d04080d0c 72
    0x192142410b584240b829803a60490b80c064030b03203401c40d005102e542403030000520340c400105101410304401d50010001d0100c140c2030502140d02c038140180c1e03035045030020b4400500d0f694004200084640c42049c011644100d90f5410150b0400030005001c41c01800950040d4034186d0140c1c10200c1040032860000c9090061031b582c600b103090049500c685078114501960100c1000d40c0350380c4002049900304c80c480f0007001000b80d403080100301071000400700a0f6040c407020551100d0300e41e54000035801824000410401e00d100d01e403450104690880302c1c0442c0c044c083e220710040c40d00804003000400c3c03203403040c1c1d1050500450f100300c6100e4240c03a0180c07140c0c0a00428448c03540c0162015400c40c4050900c1c061a03107400c600180041002081c440c000c00490310041240c080c19200780703c04007001031061100c420716900d40e0300260010086400103144030403000030400c81c2c030b070ac0380c1d0f040d50b0541011074001882001d46900c2100c0241080380c1c40e0800b0461035840f0941d51103580002451a41c0e0 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 821486627 1250 821485377 821485391
    0x40b040507050c0c060301210311030c100f05100303050a02190b090c01140d11070206030f0702010606030b060702060f0708030a0e0d08010e15040e0f07051e03070603110409020409 79
    0xa580c54095a51206802a442000103220b07800309084880c8d10880203070041d15401c0c04034502225400d0381c4d8a4064820300c03001c1400052203c01242c0c100c0004846101000509400442801640c100b41c4440c50150304205091001c41d1090f03005280160301c1d4012a00440c92081c40c0744c441d800c920300295a012507000074000c501c5400e100da501015001d00e8400320248410000e04020320483d54400481c507a0340010b50021407140b41a5080590020500340d141d01d8542d40d241c0c00020120f401d84019441c000d400700e0014001d02c40c4c0500d0b500080d01c61420075207282e080c0819940b241c01c6221090409100074000110300070000c52080b40c07032071400300b40e48005407006860b141c0386107140d60900884030010b221a402c00c1c0c501580c4002513282c031482c0300030388401203401445d2040c07001c40c0d6800303020bd04941a680015011045550a5410f08000794200e11b42d60030161040d010540c0c107400c41c44e004c112051080d00500300295400800900e826903d2000c201241d02c035900c41055a510b40f12 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 821487877 1250 821486627 821486647
    0x20313080a06060b03010e0a0e100e0102030405060105010212040603150b0a020321010509070815030304230301111c0f18021c081e091207031b05090411040b04050705 73
    0x62040104080804c090555062000c8000010f100070008640f0680c0c0318848081e40e801040f0b1f034156604003000420a07119020f8209004c0e5204903000d44003440381e1000065654400a41c41d5400c1d10003464080c1090708001c022009000c00640084003281c140304007082c41c0220340018149880d241c1c0045689041c154204042d400c1c41c2200380541d003a14a004120750344612002583c01141c0349070940860b9a00d41014840301806440c00390944000308010441c0301c00c2d01403c2da02d1451402c80010407d1103101054280c2e45000012031104100748120340e003825121b60440d0519021803400301c2c80405840740e5501300d8105464000e0b2102c0c1d800240700030750074060005200c0c1d2104045080102c2180d8440e03e030706114a0740c0741404070308018201c500c0103200c1015601c001c8401403a15407400c101030b1007503584900c240010340e1160102445081c1c044581e900203c225078000d0302001c032a031740d141c55030400c00900801c0b040d04241c03101034ad03110075525031007a00e1040c1c01d50344904d87c803005124 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 821489127 1250 821487877 821487881
    0xe010e06040803210603070905190501030b0601120e15060d201f2703080705030405040b010c05071503060803120a0605040e12160510090b0f010b0a030c020313080a06 73
    0x1100003801560074134107000050b2400f1030010b00386c1e0410040400c40d92614400c00c05140801d5010102091600700040100314011240314041c0030266141e10210001e04541c508036949541040036640c031007070842003001c044160240c2e10000003800c45240600d82e89404000c0c0120304103503050701c00c141031090b00c149480c0b1192401442c500ad0001881c0200c880060300e803402d000d59042c41c0c0410080702d800b00350100340c10a0080c40d4840519515080c180ca407140d0b5035001800382c5440340303052950344061548075500d11500c9980280041205c45d00d86520083c030031004084550400d904c1c1c2a000c02e05e85010002414071020f0400c00500e240b410904a00480b603194001c40e1069082000301c0f0304003900000c0d607031a070f440c07400c8a15940321041d10000e801c4440c0c2650081c0030740201b01c9080300c00781c4181c0c041d81049003d4400884556244509100c100314240030b9443c4040c0107000503d000c2d88698080083c1c0e1010b80116071030000038000800c0241e0650780101d0340c0e030788256a81800c0000c1c034 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 821490377 1250 821489127 821489167
    0x190302012702031f330b1606050a09060608150714180d0c030804140301020703051215040e0708010609020a0c171306030e0f0703030f0e010e06040803 66
    0x41c004424070200740d4002030325542524825098001c4130030325404501c0c1c030356000c0d44405464203016400505034205980c411421002c2c111242403400b000000d00a5000c070072142229032042c0c900b41411803640e61000105005042c081c0078994800b108070024900748500000f80c604d001c01030882c1d210500e420944003030010010000c2050072042e0100e01240c1c18152203554095020603510038400c940440c601805040c4040c20122506000100380705203d00144159581004070000003007a1500789400d03845a844000d0000300c0c2000503041080b10b108000303800024444005c5040c0781507c0004041e2044c813482c151039900900c6080003803075001d2095400520b0640029810700b010807602805031525070801800b007006c0c00164841581500d42240c1d101e0303100c0030048507015202c84004006045821880090b48149a034000020b0000a0b00901300c0b039150ba603669000341e0303580d001c407610008080010305100c80318050325001c0d52030710003410103003400900864548445103071401d008245 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 821491627 1250 821490377 821490431
    0x601150e0d26072604050d020d0204112502060702150702091006030e0703170304030512070f0e010215010618051201091a040c0b0717070f2105090409020319030201 72
    0x146000413000380c03020099404a55081395105007001356030000c034680100120740254000d00d4290901005c00b0414040d009250361110b88076030004400402e070b0b624451480c80650f201c00140200401403170502c4e01c102c101c2500c48200c1e4100a107035400303e00301c1c84c01075490300120714881c0700c24007045500d032081c0074ac00107000006002062460700e803103e42d16511400300021010020003d807e140c024811100010041c412406c220302c3d2055008042902d9040040c00241003a582c02c8880e41c070000302c0800c8070089000343e40c410391074003c05561441d0804d9203100921220100001d44e41e580c1800c00c1131003d502070010560400500c0c221100074448080c1050324100803003408085000c04a50800f40d074400301071a0340d203110390f050004a420504000e131501860002d03540082102c02c10880f00d25a11420b21a0a1022070290400490500000b4070000942c01e00050f803452400e07402ca8104a4009403e689038220f0501c64000360801c540d00c1980903139110b400d1001161200907174184d00002c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 821492877 1250 821491627 821491673
    0x6150a0905101b11031203040c030b131520040f0504320a060909080a030c020c03100906090206070b19020306010516031716020601150e0d2607 63
    0x4075040d000c00e5a0b054070201a080084e03003200143d40b0f403402c201c050741c8400c2c603401d41e940781d261601d0301d400a03600d140001c80340d1001403008140700d09132100c4400d2401e0342c0b045a8070743c00442081000000e000100051134000100a001d00c61480d4a200a0000e00302010b01499150f007044140420303070381203101c5034a4001d0b01d14501890680002030662102c20800115220307a1a115500406048141c000418052070900300d40200260107004040280703054605000003840280242d80300c00360341e10303070303540582004542c43c0825209038840180e0711310a0000107842c80158002c1758050f00002404c030b641c1d4504105008a116086909426190815000794a03502c1d180000038021b00817101d42680c10001001080708241c02102e01101a000401d0420b03424601161503032400092811010050700451001080b0030591050311050304413181c660500d0403c1102c00d10142409a10080d1034a0041e80c0002e910101d038030300b00c840028050f0040513110351560510440402c9061910400740b9 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 821494127 1250 821492877 821492897
    0x3122a110618070303200d0c02010305062407020105070c06031d030708040e0a0b0301090b06211c05041203020d08060102010c20120f0c0c010908070b0306150a090510 73
    0x140c1c000381c41c0c01900d500d0f141c01e507846c0ca504d0b403c801d540d1803149003450440c0107146401c0000b036400a084104117000340d03400d000580b00d94051200802940750301c5003885999142644203e00e5905c020101c00348103260107403078505561510005004207400000001c1d45600442c44030a942c403030101d10030084100614a0310302c6564880c0b1162203284140a000c1c8442c5001a8482e601644072250400002d002442801c9441c0341c00c040c070417030444010b407103906103004405181242c032852000c0c50941100900400b03120710058500b06036000c2603a42082400c01c0f02281c040508580f04000502c690001c004d4105404400f821032240200007a045a2411070031080705070340400a03091002d4a0040070781030074100035200341007a2300380c1100903402c3c4000400384141c848082c02452189001c41c140d81d000d00f108401101c2e00943c7c1d1003881d006910030b610511240118400541d0001802040c2c0020800495007169442e0031540d188404107403244401c00080c1002145500c5988103450501801 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 821495377 1250 821494127 821494171
    0x133c0e070611150613090503070b07080112110d141c17070c02040b06041a040f09020304120315030b0901020c010b090c120a090206070b100603050403122a1106 70
    0x465001800d440c40340c0c45c441080e005d0400c5a5200030310403604902134a0b03480c02c1c1c40c141582800c50644503580096032800000854086009000e031007140c1c8418241c0300e12000c10104442c0e080e025500380c41d80500b83c4012090404104080b081e045400c03440400002800a4081c0114446203d14191241c0c1c0000304090117074005190511140d049034009103481801c00480c07030078000d64221410b01038144040304014809000030304100ca060b800c2100d40181c492454409901080d80d0040800301018810781089000e5000329606081c071508107e9a103541c0d4440b03191002c0241c0388400300e42d500080d20300c0c40d090280505450345030f0036604420241407801d11030640b0301c90340c020a800c3c4500000440c000084541008000319001094143c880c9100d00b071016a0136801d0f103103420301c40301030140016050300901449100703030742540702d18016464801c5c2d1b40c0003411981c040c68030183e445080c8100c14464400801042414075902c1144c49071102c0126132a200c0301810140401341565404900 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 821496627 1250 821495377 821495413
    0x40507210c0e1207091a03190b010b030c1314040b0d05100c0905032b020c0d0b06030c040e03090a08060c0d022a03030402133c0e070611 60
    0x40e01058a501035104580c40405013030280942011484504200301d00503000c0d801c1140c0c080018085060314810560003a11581c01c80d10100e0040c0340e010003e0040241c01d0b0b5a10241d0b501100446c04903207003c0b0040c103030706102001e5800c141400a264803850072941001e10842d106120103480400140c50592981035840c9030b511107140703000e5260041101c5030303031242c1c050000800c006800c8662201c02144a214005046440418610760111b1b0000505200098125040002820341c071241c807041c0d1a00302500300004c01c0b05400d84581016400b183d00c540c42089550803805010b0b40d265018503080060851151b481144590701020910048200480c100c2e00c4142e0341440041e40c0d00b03105d001403c80b500d503061000081081c040d201840320500400114420b5200312840026070f0410f0f4a148204c1d9010280f41c280c074850b0101c1c40742c4424003621380409031072200b104c0f29146403440b1b42c80015600c10328207031406070300440801c01c01d1036001000d14400c0c030444405091207856003620084 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 821497877 1250 821496627 821496647
    0x516060909061d0c0a2a12020d1d1c26071505060f03030705060901050f071b110d06090b060913060b13112a07061d040507210c 56
    0x5803007003001070141e00c0c0c28041c103107201e81100c05e103a485e40707028a1940b182d601d15641803029140d01204480840c0c0a91011803c00c94a03440ca48400c0e5034510b00500e941401002b00f9016508503035819040f501240080c940c81041520605003407000c0150b16018002d4001011083e4190820030f004880004051034441107000a000c7d000050a0b80c94100203008c2000482c03482d50103000001740d41341031200100741540320361240340091009880310018013120201c21901800000d4a4900720b4804c0025a0215800305005145102031400303440005a4141380c4041e007190410b95070900b02041000c03030b88985520550403111307405145401410383c119140d8400b001002c955544d84031050035901d0030342c0e50140004241c0c081203402d18058031201d003680300c0d0741b0038507801c4030101901001007200d4030803501090f4400040c0c46244d03c1e118082d030303c8903541020303541d007440640c6a01d6101c1e00ea61140602c0b5124076501c0441d0340b0204484040d032045071922107130b290380c2400000c2310003c0e04500300398 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 821499127 1250 821497877 821497891
    0x140405101d040501030b09010b0108040b0402011116080c010e090f0c0f070b0709030b1b0a110a1202060f130803040803070c121d0105040810090516060909061d 70
    0x2000180c640001020311807901151554083e14007000801440620050f10b80b0401c40c04000b04185c0422070010342c0d01580849005010807440000100154407420125061040031002c50310b1600d9490050b65500f001c641144880d0b60003102e440c0c8003580c1c4915026000f0b002520090420b0811203140f40380004020051000003c001070702c241c0700030070102242c1c400c0360440701803407480c00c140200510040071480706503201c0c3e41c040045610b039600307040408998210004c181d071820824441c141e550a1100407620200e0140008a502195941c03080a584120f982d025000601d0f0282144105500262009914801c01002100055801d400b20b940068010216548965401c801111429801403004000785c06640c0c0c103100301c0e50845001b60b881000b0388900b80040d04107000448190043c1c1c03007100ca465120030b1040586801940c071500d038440c011000c4d03c0080d40118001d9622074181da1108001442021081100c020907206810250281000a994401d005401c1c5941c00d10060716075 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 821500377 1250 821499127 821499137
    0x61b061f0e0a0902190e10090e060402040e01110409091a010305100203040c091e1802090123060403080a0815180a15080c1002010b010c0803070507080c0d14040510 72
    0xf05003559a04400140455128060b0350f08a43d16950340c05c0e4100410b451b1407110102e94400030a410420380910301c610354041c0002e1403079941d41d40802000d030202109501c0b0a559402c5022a510050301c000c00c0905600c0401140b500781d94a42070b41c003000081e824810030a5040e0042c000520041a10340310315442c040f0258407911f030b60809081c03a5230613903c5140b00a16103045000103a140d016040400c6811000801c02940c04440c4600340d0341f18004000d500c03250703040c014003101a07050503003103c4001103400d80d9800c0c00414049240b5501c140c0055981c1c100100d07072645120b9008000c01d9102c480c0701e40e40c00d803600000d404243d10301c01216810008085590010fa4040d103198028840c407101a0408038106a0b10b0230442c0c3c0340e80c2035141e4540034546c0600d0b0081315030f0050003103204d0140e041c1d46048950405071141d480a4001914442c10850700f08100004100648003800b4402011009460b90209400c4081c0c00c82c401c4c450802c1d19054140400c0006990341d00304000c4820083c282 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 821501627 1250 821500377 821500391
    0x50717060f0c0405060c011a04021323090f0a180c06030c030b0a09060f1e0302060a050c030a031a04050f0105040f06083c0714061b061f0e0a 62
    0xb08000e024542255801003c081050381207408150001e0803100b141c0810680c00d0a1408103120591240003c8034040328000d107020052528a50708102d104281c02208680841c40c40002070140c06068078852201c0c4400c009003c9100309502c5286c101480d640001e050700c42c4d4940d1200300d140740c00d120340340500d0399900740d42c103019019411102c01d401d8000c0c048420580c50f105036100034592805444c2d4007a2094401280000d6011a04080441d241184001d22890341c1e0800c005a0f00021009081200c2400500d10211003003002c0c100d83e07082ca403804581400c01034000e1249070940c400307075407240b030a10080c0054081c890070380b94150703101a60080f4040000c01e0a50340500760640c000c407201e03c03d91800c91403040080c07d0300301160900c4028880c103070705009020b10081d04020002d1440760412201082040586038010048078000b504c69400e210703240c00b0030b030303a121b80340d41180e42c2c03030f0700000104400e0f200e501c1a40000c4a401d180c0d0007001c1402c06a90920600000305100155699021 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 821502877 1250 821501627 821501641
    0xf0f010c020312031504020c0717030f041805070309020d0209070c020d08040f05060a1e11030a0305160201022a0111030703061809050604020904020a09020d09050717060f 75
    0x210204800341c018044030382c0c070071800160051642c01202c203420004541000e540d42071401d0300071506030150141c0144241d9043c4014901036420031540c03500c242c81304001207110114041d0242c401040003609850321748103c03079289001d407080203002d0f800705072420901100580e990814410003940541d0390030b42c144ea801b1010382d0b01c020704c1c55020f50301140c07030310b95a020402e002c0014002d90f60454601044280d403803050189a0083c852160045403c40072101c2000c503480e203100000d8030f19464003424020304a00740f42e0940c2d01c00f0080d000041c1d2248104410303546050300368140b0010320700c02103181c000e4075180302017039944281d03c28200c1051801c0c440102c120940105004e840c808124596038140b2038030280040c4410321a91076003200300f402c403542d06023161242c5032180c0d0b0000d01520309556a41e080100c00352009100302e1740640002c002140c480954406490161030000000a1403000ba052252034040303241e10203075400b1115606034106500110340c044d0007009035050b84d55907440f815 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 821504127 1250 821502877 821502887
    0x4020a0504090c050f010f090b090a150f090b04080714060f0a0804050d030c050a180b03090102042301020d0c050106050d0c061805090c07021201050a0209120a020f0f01 74
    0x40e1100398400e0030704280d6800c0c040e140040c10200ca10880b038002c80c01102c40300544862014001c40400300350606020450000403800810800b0401402e2000040d118240c14003101c818007840340006504507040044290884440809009000c1149040500d08440c1e25a2818980940303550410017041084841d21109d0568160381710a840c00c40e1110f18001009080d05002c86040e14203108004d2a081094040c0c03043e80c610705010f50302d00e403400c211984199003900010300c141d10580c01070b10b400240d4101074005940a00751000000d81d80d50300d05541540c10041d1207902e81041450120942103503a00050350000200d0070f41011400c62081e401c2c028010718469000b1a0040400742e502c20410580303006440036522240c4440c840d00429100d89240b003500c3d40070752034000c08214081007034a00070700083c120541c401009002c010220322022070940b0010303994405c0c141d4010074160300324a020042402c07071411150003070000064039000100c1070101d040702d160041d042d00b03000c3e00c03140e4458 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 821505377 1250 821504127 821504129
    0x1809101e0b01032a140a02100e0f07030c0602010e12040e04150204030602040911030907030b10180c021504050a0f170c0c09010518160302040513020a1205130b04020a 73
    0x12080c813150b4201071003040d100c0450b890f1512000440040c03000d010a0280d0064420704001340d8002c0c6030340e04109174614004c188052365000144a60444030310340200c1044810003651180d40741c001064076221001c1d084d92690340c1a29102c1d080805100c5400000f40207031070844d04210904021038840c4e0030299102c500c580d40380f00740e55000080210a2107110b4000f8800c0710352501041001c14500c1011400600040c0d4030500543c01c489420408200303c0158550442c0c0307a80600c56001d076039060a08004030201c40100b01454503000c568003a9a0148081061200c21032020521481d0960340e146e11618100300040402c11400e0741c240c2801040303449000b0070082042c3c0c181e610310004461541c4c580034041e0980c42030419030008140c505014040151000020030303440d205440d0403a41c0c03048140c9100e4010101a82444001841c3d500c0c0f080c11480c8000c14580140e503040e1002c00144410540c1c18854944c6003454240a07103440300405148070290010f612060360780310703803001070b58042c02 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 821506627 1250 821505377 821505401
    0x2181003021011070e131709130b121c08250c02040b15070803060414133c021305070302120f0403050703110c1809101e0b0103 56
    0x720041c02d42e4480e0000c03403014803a401e0304112100241d4804001650a07001c81d40c001109000ca4440c1c2d0000e030000c0030907c143c5040107007550410788000d0110306000310b08051080450349407401c005250504038100568080504060b013200c88488401040744c040a20700103007005003030000510404003002901003460111420005290715544000303104017450755003617104900e40a54502c0602d05031400f10448001d101004e8201451074440c80d401c2d8000425090700140c580042c3c0c4054005004020b00c038072490040e0440540031801c000e6004609020f0340d00450b40300949003030920146500820601140d800c2d030902c048454804607024010843c0804031304c60818080c400034680507005040b4031090300f5009060355603084440190044240ca015000c241c0030000307800840d02c1004000c0702004000101d8040c4015100801c880d044500c0c0350002640380041072006219080c044a030b0070300014175003441680a40c035182495004003584918910f640e0b081d42d5003040c3d0281d0811200601 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 821507877 1250 821506627 821506639
    0x9010c3603031d031506190815090d020109030903020603130b01090509100204050a050f0303040b0301080105070f02010b0a06080a0b0a0801090b011d06061c0903090e0903070218100302 81
    0x681c03498007910744024044240030907a08041c003420341d0b0400080c0e0424210914009000740d0300e5034000d0228814503010680f014580307200c000308400b07400f00420104020301000d00200c500c0c1912400b800d0420104006085904207100640403aa00a0301d000030780740c0485480b5944d88620804103090400c0540c000d00c0c241a80000041110b4a58000361007903005909480029940c1c0081d0310072071165005071907020039034900512807420502c040c180c55600150440740317000d4813040c4803005900b00f6405155541e4441040107030032907200d00081c52010003070009000c55145000002c20030703151406824100582440020100c8042d0b07006084044000b0f40304881d031685680c0e0103400b8109460081e24054106000010800e43c540200321400900007441c42c140c1d15101c04110707840e803088410100001c01090b00c0e0549034090701c01c144075607200762909a400c83c1303414203c01c07806038000c20004458005004100241c0c49050740740c80c4034801c041d5a502103541d452a0310203603a44641020350806 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 821509127 1250 821507877 821507879
    0x81005150d0b041112031b0109170901030605060c0d030f1b08010306140f010b0a0915080402040501060e0105071b0824090313030204020a0309080d020403020909010c36 74
    0x2c01540320b00c5008030702840e4014902502c020a2000240460682c8886a4020080f80098109070009440b528548400208041e56541c40c0e600c00401d031400b140080180c00188205103607054481c036030061009803021030034000410030706501c0e02414500c01090507211122298501415402032403400583e0301e4250200e04002c4c1d000701701d18000d0204443c0c8900d080010318807009407446003440b64640c912040281c0c0c0c01c12040079811b4000d880d243c400d001504901198402d086014142030305243c3e03a404505190a00400050791410303801441849403800865101d80d910004803410680c00a0b28100c10703601001d0350090100d400d074843c01d402d000e03400840400301d00101c12200d1342d06911400e907a150b103480110644034441d103541411001c8140d5001c100500f415000b038440c00545050001e0861080c0d00c40c044140d01c501100002164001070610440c9085402260408101e40080086c40480d44020300030aa80c140304854000e81c3d0100080401103028528060644904101c0052 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 821510377 1250 821509127 821509133
    0x1030b0d02031036022403160f08040c09021b01060b1b0111190e09040c1e140f0d1401020706060509100311010309051c03050c04081005150d 62
    0x20500c8960364611224a8910744405549010364241c0303000c444d070021160024a03900300045801c015010300183c20700320410050703404040014511844007110801c5880f054100f00502e1300c011081c0390307000d0012a00c1800b0114010304070364419140c2d040d0005a580441c0166103000900302c903594100340d0f00305174012a0100c0028064a00401e50f0444800e441510710b0b1480d0990300c2460301e001e00920b09004510342441110f1500c108280141064290580c03e0408501d49010444d01a111800710b07803805c121003030121070794011403980f25a01c0d0401c1c2c1d0402c1d14801116050400f1070f0300c581003c034082d9116907107c1c0b4044601e42d030301c12400c0c685007400040d214040c2d0892803050318071320b14202e0005201d0814080151050040c001f18803407203401d60342c6da082c640c010b40e881c99042540e40e02216000034010002c0c802800300d600c910428412218500034103868009015110b00803003804204007065000651858061060b98042141d56844c2c4a442030485290326440d80442070f45520000c0c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 821511627 1250 821510377 821510381
    0x8070509040213151707080a05060406083004080601120804121109100324061a1804060b0703110316060c08070810030308061302030c120a140601030b0d020310 70
    0x10048150700c80b000e50040e48055175441220450319140454581c030005a64804a42d05c015440b000081002a4042d101c3e60940d240182d00c43d10020007818002c822452070136121a65407a00c8420b400c0c45223041e00b0514555180d84041c404d03100119041003903c0200038017401940c0142800401c06690840b0a0903c81c421350385640c00140641b16100209005000c0d6950035416a5041070344056402c3c00c03018541d02003000e80c0a80c4201650b03904000c030300c3d040e400801800c0c2508919481380c80350420f0b03400f0340c44080921021481145000810482290740c14243c841854050070844492041005100d046200701201d03105a040c0d107502040400580d031b400400b074645940d50301d07d0651f403680d81c00d13125040241c03000c042c542442030082001038403035030704141c4c032000107004412240e9021094205a80098903411065031022640b00020074407110855884800c1000900c40160503e24081d0389000c050030075410181c03220000041522104803622180340d0180840d5409180a409580 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 821512877 1250 821511627 821511659
    0x60c02030403060e031602010c020d080307050c07050a0f0b1c02040f06030f1e020c0109150b010f020c0a1401110709020307090504090c090207032006040c0e040308070509040213 78
    0x340c007500d00b8045504140000051b03030002501c3c0e400075224a8130540056504290001c0c0403644a5964403003e0005084a00a10700990144d180c41d5103a001b04002c1c6810083c19801081c0500f034100000c10040019002d030a048030161540d084d900c9070030b9141c69682902425040784410700010300094800202164481240d0f800c7d41d081104802c4c0d24110340c00d59046111a072302a1b04000e903404040000c0754000d02e104801c00c030000034a80ca5590b140f0820071810000300080d01da0341c12803203015581003002c0740d08a607507a00c00b070304810480030005509003c0c1400358124800080d000344510fa409508030780d04014040040325205566807501e200a54802c941d48400a90b0039000080c1a00f014040d000955070304c00c542c24891030030f000b501b000035004202c0507030403c070803001a002d200711a64600c6000c04d800401400c03107803516051240b0401c02e02ea02c8000c641c0b1003c0d0801000c268081c04e010303000388261800c030342d680705400001000790248440c1304160004030300000601d9203d11000e60 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 821514127 1250 821512877 821512883
    0x4080a0c050a06111c0c0b0a020d631b030c0b1e030108030d1b0f030c0e03160e0702150a0507090b04090f1401050d020d02030a060c02030403 62
    0x1210325519480104d91a01c908502c090680d0300501c1c512010800000c0c00550040c2c092402442c10000e0f61110118000280c4641c60906e50000b4245103152150154404402e00c03440000038040d03078a940305040803034180b200066185030034240c5052403003d0a400c040c0a442c3c80c0242c03650000040c101c6500e01c0c0004080700d064186003040340600791801e44c2c0f442242d0704100000402c0e46880d040000701c1e800103a514074060f80101203815013800c010007941c00b038a4070000035a00c5e41d0180800c4001c4803903500d4888600d540d5405e200e4203182d8000440d0301c030724403149004118041c046500b900c58940c1c008081d9414001c0d24082c040d03c2c0380300c006100484061004219240d164090305986984409850b40000b45040000410400e9140c121a4220310140350803640d21b03a841a4400d42c40d0065001030701c00b07948a0340070046080030780c010f40c80000180710314a4829450315001881144280030300078040c0418005030025980c092040200980c3c10000610040e02c656500945a034424007080f = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 821515377 1250 821514127 821514139
    0x180406050609180a080d021201030c0f080102070c050f01030f0c02010903140f03011505040801060e040203100501080613080d0c09030308160503070e0d12021b040e03030c0f04080a0c05 81
    0x2034003034001145000820010280540b81320300003502c84411a07802034024622841e003c000d402c20f40600143c00c54000d5000d1035442150300c0c21700030f40354070f6030710181c0c4005442d0703005000100100341e019220001700c400455a101c0e07070740c21110060300038002d40380340202104c0c64805000070f90340d01034200f404110301c240d882000030700c034000c4a42c1c460701414890206e8100107000620003409889880c0c4039a00c60b5041c82420300399682c1c1024290382d0150003059560f400107081c403045017410010034004800348041407040e981006010f564030345008191044602040e00c0c3c40301440605002c40745140e010b040c013400000c64004000e000024280700440000721600005413035004458a80640003510360384540c07030350700d80c0d03481103608116404d04070b0b0703210044084400005132641c403840f42c5409a03802415962021a426240520710f17451700c18000e81c100211003141c110040100c2c2c0e84105064100380c1c450031a120010000e0146420140031449498460001c0c400a038a9140c01c41e0011600 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 821516627 1250 821515377 821515381
    0x70c030c020d0b160c230f06010f1805151509060f090f0628050c01091b060302090102190809090f010806060609010c0f0302010f150305070501020109170702180406050609 75
    0x8100e0309150b0071803000c6d144190800c04003801841070703815600c1d0503001d00700b116017520021f4103035801d2800a07071029580d4106001d0402030b104c030302c0050241e550802c2c0c038200001d1a16001c8404000003550701c4600c102c0800c0c0c1002c00281101c0151015840e01130843c94640e0751142010b10240d010804c990b00c25003805244440c82e24100f81190f81c00d0361803400880e181c1c5002205003088005560340b4405010f0180102442c01000744211544035010308c0c00d1105007501d03540184019105034108008250041050000c00d903000503408014800b003000e9500102c540741040c4480340503410000d580070403007005109040c41128000c0341130b40c1d41c071713004e4a41c542c65000820404e4881c04008501082c04c1e113042d00c001c40d8a230341c0000c0f00ca500034000445c1d40404811710404490804070002c00144010302c0071b10a100d0104640c0300904400e0000308400c00c41070715205c50356140d40069410000000904a045481b101071040c0080380001c400c4116007014030b01840035100c01c4511b90f0042c110000 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 821517877 1250 821516627 821516671
    0x1120e072309010605120a0b120610050a060f1b080a050301090f091106090d0602300405060c0f04091103070e03070e0a09050304030203060c0901020d080f070c030c020d0b 75
    0xb614038100c40a580f43c007850441d1064108400e03100003020b451020350782d0f01c440c41c80c07515440e03a016002e130f0100e405401946042100140c10b01910342105000e0003170410207026184d000700c0c00101404039410302d915204000245208424041000108003030400710701401b140d50400043d44c140d54400c0320030b2180540e84100c1908881c0c45007000303000440024408513003814010010f10410350081d0422244140355181e110a9a000b0101680e08181103c85005140e454840c0c7e5083c80346041c01e480380605042d11200d5841f40d025006610070030f400903810387d10030101d000302d03001024140f50900801100c048821f0283e013044038040c01150b88188144001d03d0040342c07030010b03294454007142003510b507500018001c0444d020100c4591104203c08005a0740400c0118402c850078070078280c1e2800c205000905040002c1204404e0103c003505200d406d542c141081d07075000d405031608502d450b80d03e040454041c001c400000c0d40003150101040207201000703d400340314400140741503081d1181c00d4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 821519127 1250 821517877 821517889
    0x807270209060a030509150c03090106080c3a0507050a21030503060a03021201060302040b100905010c240b040c020a020102060406020c2803030b1e01120e0723 70
    0x8070199806201000001000e034042d0740980d802c407441500325603038030082900c02c05035a4815500705410040220801c9114a400d0081c500580b1070384001e4085140303178902150742035140c0f030501d01d01445039a1420f05052080d104c2c4c0030343d00090200d003120000c105d06000340c41c1c5189004240c003e00e03c00e00081855900c450b04142c1440e000d80402e1400304480d1001c50303158001800d440c4e40003441036400009a526281019030048050b000014003e00e0f6104120407114181c2c0d403140034035a11505004d0507500151450125402820000e0001c001c0b0304c1c1c829144000440d9840e011101d00d13181c624020340c1a8411b40c60500161800c0141c14804081a81c5d240b0017040300900681c005c200080019100d600907068a4140f4021110321480307a0765008025000007016004950030303031080b4400d255050255904c40e800a454149035491441c00700050068580c0c1800c0c184449001100740071021940f102e4820148817096070041903c60b140c40d004030902d00118600501320a90f001e1f41403800c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 821520377 1250 821519127 821519137
    0x2190903060b0105210910020408100501050f100507061103010909120216090b061e030f010b0306090a0e0708071d010806070f14091003140a090302190c08072702 71
    0x40d800182c100b040c1d00d40c5c1360302c0040c401807070280315000302e205610390082140060005840a28060280f80000810102c101d440582c42144a0b0f0000d039040341107034640882a6408298901e0013503950b00392810004090f107580d04848000050000c000100131085a0102094602c10304d441c030304000c43c0740012a0b861944607071602c280c143c6040100a41d4503554851050340c074001c0c05050411080d24154201c0d0070100c0e2941d45100b0000040103d4204000507a6015102c800003003815400d1100103d0b0b070303216000301040e105075514410340391032034810080400106801c60450364065200c2e00162051208400310356a400c0300c00001040c005804104288121b566a4500815402000342200c030891050340c0d20004104c100004146d6484080226900289a440110345902e050140c0401d44d000101042c982600d0300f603071a00040e5002c035040c8584040d10a00750201c0c0741509101c0e200c1040c40c2e00c00004e91003005400140c1c0d0150b04000940700500c00d040d503000e080c225000100768812 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 821521627 1250 821520377 821520397
    0x9010908030612070807060801150201060305031c1d07080d0e150901090807080127050c06090f0a080c03010e0607121d060907081207031b030302190903060b0105 71
    0x1d000142e01814020000c45102c800d120440d00520303540c012103424210b0703d40084000074144001805072550241c110071480102d480200714039490740d15855140d016030404626848400410050810003540140c07541e41504802c10620341d4003500b000d944d452651281c0c4045008610075004054028091380c00b075002d024022800e03030070241c04c882a41e03501011031503044c8080d140c0081840c007810403104002d005914000900000b042c10403025541d83c0e10080031103040904100c400082c001b0030080e4100c0406d070707201510780c8203403070014420a808500c2c0c640c000e4050500083c0c141d80018403211401e00039002003019a0036012905e44507242100c0c603c0c04110284100548c265403030340310758288072001c16000440c01d00c18a01c1820b1000c01e0340e50b400c0784c0d8019138040c070944c1c800f44904200c0704054441c591600c102c50750050070407600c50007014007039510481d513401410b00a4040b2101d41e805c61803040d48034501c0a1014200d00541d0009566080c41c0100040c51540680c0458140d100 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 821522877 1250 821521627 821521643
    0x30d0c0201090618172d0c0d050d0c060e0a0602090405010f05090112030507021008040209090102090a09090501110a0c0c0504060b0d0203060d0b09030c150105010f08100308160308090109 82
    0x2c1417001581d00c000112a401c185480303200001081840d580090310004207000c0b015448160b00c0814407403409211001140c440d610485440c0300180f4000b44849080c56603040481400500d41400801448601c0d01d042e10340c081c5011180030020154010f001c0714504540030001a41c03120354540010005003e8160030188140050188620041006160034400c0c503100345020443c2d808280f4410a4050f20804100007405000461403d04a82a0300c464098021410401d03500c00156421000d44a5022481d585100e8003082c00000c2d00207501c0300040f943c0c00e56a07542041001002d440d108801522a00444c2c4000300c7c0c0713403810340a01421680e02c15000d6041a041070203c000075030021f040e16510039191100c8a00060703020702486d1103040d0540295403250040243ca0b401c0c804004a003a001303265003801807005a80009002040b21a01d2421091a940d1020040020003e68002402110012030b05540050340c403c4410f003079510958480c2c250340c03184a01107090b00d421030340081140c2 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 821524127 1250 821522877 821522879
    0x4080607080417040f0602060604050723040e10210201050703030f0f1e0b0d0b0a09080c0303090703171e0c0a020603041119180c0905030d0c0201090618 67
    0x901c100d04082d0882d0207081600d185003149256100d003680b1680c801d151000c1d00e2041041425014003485a003c5001e4405000505e02520010218a80084130f491580721480a0500c64103040042d60081c208100c581c4405040141000045003000d104600140d2f0070700c0c040320042e240c00b104076282541d068641c9801c14441c6c0d90207a018013251540c45035981e554074400088a02180211900c2c4a07400c1003c41484400303420764030942e414941d50a0003038040d0741441000582d02c00030b060b448900084001091402498040141d21400703440303580c5440081b060040f0400c000c1101d5084034032580c01c1008080d0982e600c555603016121001c081402000340303e804074421030004204103203030841916950b00455001484030b40043d501a0789000012030201c071a801c1c550081e0101c2c005170400d00c6055031902d507449840125803c41302011a0300d40a0780c9007003502403e80c04000e4040101624900801c4407001441c524214100f41d000481101e000280d40e030045800000215840c0d807084545 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 821525377 1250 821524127 821524141
    0x3d260327060d02270f010509213909060d260c0c04060b07141e21031005010c171b0c0402091e210309030f0102040806 52
    0x215905080d140d0000c00c104006038002c4070900c024080034040c0490301c6a1900380c0340300d4444904000040714042c0202e9181e0701c039542e0304a0140c4142c230340201c400079000c502100c45030b008042139804242c400d10800200547c5000525480c0204540d02003246981d5181c452800392100c000c52022608590408081040b074108994a44481c9000d4201a0b18903403403640d01220903000303400c9200107942c0104d0f40705000b20007409000c075003600403101030002c0380c00c009a00405110310000104030480c4540c2081040405000f202d028496150f05030107a681c540c51515151a2050003900745040110101e50345080c450055038014850b00007020000c5003040019501c46104070020b58418400110302c4994084010061140045249402c0c05403c08000381510345440024410301c114014800180c00351500d05006071801c0c002120035001c40c4014006c150b81843d002c007070420040d0070020300500d007240000144001d0308107900b01c504440e0a440180c2c00c03401540130303030403091304200041024 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 821526627 1250 821525377 821525437
    0x3041401030621020a03210e0402090f011d060441010c080c0601140319210e09100512060105060738040c0b033d2603 52
    0xf4500c054001607109840744c5070051701a07160707003440103668030025040c090550f20800c01c200001040c3e80650405c41e1a10000d100c002600c04e034181080030100e41d072440040281f0010030514001352049a81d1a2200300442c120706125086804d24260f10061060b0740c0300c403111101c1c581900c520b590782d0f15020100110f1386041c0d50f500035120b1450610889904041c00c2c05054001c01c0785206003400d6080d001c00303040c14096052002d42d0441c60100000300330680c45004203500134409810300c240d40e00c94800030398035521924500c0e5003141c1610300b0001c65041990041d01542c00494103a103a159900d501c440d6500000d0091300d4100a0074021800019178038480002c1d00b000c0210401c150640007a40f28a0f81c1400b00d01041d600d40c8103205000500c10100080400350084441061540c0307071000381304a55904a9102d0030203800d049003259070305405201c0007090001c1854030040044d03a00d01d00442d0103c03454041d41005081d80500c4050840000122080c1c072062a031a00e190300403c0400e421 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 821527877 1250 821526627 821526689
    0x80403080627150405010e0103032c011808160504050603010b18130503070b011e05031c0905060f12010902070507060c02010917030c0c061309051314030414010306 72
    0x191007504081803560f07550b10760007058042e080861100000e0762560a004203a50ba401c800a0300c1800e222148609006c06504520034a400070b080401c0c3d000c12240c205d502c045801c0e88480d109001340c030000d500700f0740e07448580c104440b01201d052000d0b4071030343d040500320b600821503103034400d0b429070f120310340140c881d409664441c1180ad540d070005491620381505650000c14101e5031600d8540052080c140841c58010090000700b0180c8141c0b030906020a1341c0c1c0382d220790071002c11030142040440c00c61207441d04801400001d4007403034442000b01ca847c5115000010341c4540301c10080000724040f28540b0a42d25915001801800301070b180060903950810440c00590410801000116038606500c2e03030710100c1300c903410043d65a41d820584042c10942e2241045103d4802009802941e841080ca150151503502d24009259140d8032a900341c1c0305c010410040c0000d0341654482d804001c040040d04c00c0380c4031640310b00385902d503174401142142e0541c020781031b030304162032035120408602420000c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 821529127 1250 821527877 821527891
    0x20c0307021516050a05010c090509010303051e160501062c1003052b11070b160f0b041505450105070f030510050904020a0312080403080627 62
    0x903e083c2140318020105040c480094895074007070307485402001024880c00415240d90b01c0c0042d80d05083c0800265180410b110180410801094600b4032154458126588080d0f9106060395168144035035a07c50115890130b507aa03500c0c010700060068401c191150400700d1402d901d0f00c0b1140c0b03099400420842c090801c0b01103059088020000400400c690040002c0d55020002c0503140e1800111441e58030441c10020032001402141450800007811015034082c440002e8035012041c4001807004104100507185084003001c0c401030145400e80d00c0e02890190390181c03005d150300c9168030300703403602956201340c00842d034807506c40403005503203054a07510b0750340f481c40c000c0e1144030902d04400ca1071280b8010032650760300c040c824a2504125241c504015505043c0000e01c4c02a0000c01d1002e030b2440740030302442451000404650711071000c01c002d0740d8000303604035964003071080c01828040221411004111140b010802e6840c0c5580c0d0112500742c0015001c4505401442c0c54200300f001800c0c82d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 821530377 1250 821529127 821529169
    0x6091b07051002040504051e04060c030b09040c0303110f07031b0b030a0510170307330c02010b0d110f010315140915010f0503060a090e0109031101020c030702 70
    0x104000341d424445a00c000b0709040b0090786aa0418080004030344c0003500350700c40c8546596401e080c078103034a00c0b00c50f4000d421442c000780700024000150051701d64540c801c0d900848041c100800c014a5200c008182c80c000c0da126546070800401c03032940c54002140c2c0201c25400151700b0070006010ba04901d55502034214201e1070a0b9503140024542e400c00d4035141d61441e150002c2200281d04400313014000c0022a140e0039004551003105a00c07485142000751950850782080641c00410303900c00080b450400315803003c44048000c065004000d0b1030041c10055082c00c52110b11890700c1828007103515000403819100c03103064410405114100d05040c0c0c10702d5110341c803080781d00e0101c458110040500c9201d450404034607104000240c04010300324078500079101541c2c2c1503a68400b0744440089843d040036584d81d21084000f0350809410f81c401c500003030401d1280c0800907411b402c07541c45140f007512524040903440c1090707800d0b8051101c81c14442d50007844000c0c007620340240803510003100e0b9000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 821531627 1250 821530377 821530387
    0x30f100608130507050409081c050c04031115070b01030c240807090302041113050618090703090f110f0405040314071703010803031017030301050405041e03090501020d050306091b 79
    0x125007950b071000d02c152580c440118129021040d009c4240329540001101080721f490110051245405180400380951240950b10762460f1280d24a40d1348a0103181da06588a040e1403420802040003408103e078004240785000500c0328110101e41032401c0681c828110b184600c3c40700b111031480040080b03042085087c0000b0158442d031140300c03ca0008460301550321200604d0001c0c001d40307540c0c040f0b401048100009180c0016003c641c1c0d1000c101140c01c40d40799281c1c00070890142c00c0c00c0030301409881003450214200000c06142d2881040300b43d68008907807021700c08000894030100d42c080e01041c0c0132075181e000c40607030394018580c0c28030403280d122840056a2140003541c100340c228400c9903000005100100506a0360030006141c00d440001c1c8805840c0e940c940c8034081881072a00440c1c0b1003000c20204843c2c040c031051080100854514103000380e040090030310230b640c41510b0160265030100a01c081c03040c0304584c46484054010281a201c16114562560b060444560050700c00c3c05 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 821532877 1250 821531627 821531629
    0x90c0c0f07031205093c0108090c01080601170a02030406110901082d01080d020633040e01020a1706030114040f0503040b040e040c0b0702090406200f030f10060813050705 75
    0x280d1044c140c2c83c1d500403010425000d040c00b051071b5034001490f0b060065003001c0007890741c00000e0f09002c0d82c5081c0b1700380d0b0340c0e6100c000042e00e072400f003150000e8004460301c040080587c40e03540514452070003144c1c1440001074960020750144501e1040e20300003010b41e40000d90401c0340e9203681e07400102c8610f03d24207048041c00c0510800d030007170b000101550840c0001c40346107607040042c180c00c10450f049103440b04142000c8112400b14400965a0380b18002c8840703105595942e03c17644000c0c1d0110000d41da103407a0000c0003002d0b001d502c0900d01c060601c100201e200390405100d16412000e020110701c0942d2180c0d155594829280c1208035030900c0300700030101c0c1204210303001d0402030511511b6000c0300e061a1901001c611065003043c1071680052100e0310240c0c1e9007030f07681c070740090700010002950601c00b03028061040c00c0710900d4001c1d0200155044c01181000c0046104164011101c08030b6200e0000c4803800003550710454000030000c00119000101101d690300001c0d2040c41124505542c1d07030 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 821534127 1250 821532877 821532919
    0x606070b07091a04090e06090307031407150b03071a0f0c0a0f120e0105070b131a010b130b0306010e01110705031605010f0221070203010b090c0c0f0703120509 70
    0x118800f00c1e01c0001003010410013906001d00385a40c4a003002400c0e20341b40404009a0740c0c040d20340e0141c10051100014801d03400c104048851258002071110b407010120300d03501010f4074408030854084c0c4600c81e0001198030001c4158484500c20143c0c651900e094207404900701d40002075a0007444c0180c0c55400c00140710308101c5800244030350b99003c02c6812100c800781c50180c5a03244079041c000200000000102c542e440c031580040e1356a00043c001082c2d0411458840d554800a41050582c400204446c030403103001c2c14000005070200940c940c0c407180f100311607000580340345000c50102d40e400d460a42c0a0303034070707188020300c40c00c22200181c1d52000020710b00004000e5401100741456410f10103564803c441040c00c1f05d0600013408171203c0050440841c0404004c00c0c540e110000c01c400c0d0842d9001e422150a4440003052000a030414440d58995540482c80c07001262140c50141030501364049002c5080b290040b0b40142280c01600d070603101580311121b0141e00407501c4135a908a01048 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 821535377 1250 821534127 821534159
    0x3050d15050102060109050903030105010f022e060503030c030f03130b0406020d111306050c0a081b0f0703030e150c191b050303030a0e010e0d0201140f0606070b0709 73
    0x1012040c9140ea1612001a051040c10707003004c001e176814041007041e01800002100c1c1182d4081c41c0040c420000f601c1e00722b081100610340c00d22849810400740b41e0740c00503c1c4407012500b030484402c2060940e10f02c1050340d02d10038222255060b8005100e8502c10194070005140c0c07146581d02c140c407081010b41d450b000204800c5070101c9100741d01140c5504505070f60f00c540c520107000340c0211854a0489014680340e070440303128510401c00001803c0c8282203080c070802010546c403e4070151542d41281100c0c841e44211a4455034600c1040c20141c0100d100207448821a901a2112454035041000340301c07800301410340c540c90346e08080094490340c3c90208141301928200d40c84a07428080c2e2841c0809a803115071070444442000c0b4081030140ea58080b04484c6c12a0f16600001021854030040a01420408200405030301418111009058042d000442403452094000f1100d9651003500d0242041c10354523140c0106050003030200080b41600c000d9044000360915004d0303e540e48000c010706400c4 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 821536627 1250 821535377 821535401
    0x120a030306090b0a0e0a0f0f18020f0603220221061806010f0608090c0405070929180307081617060108122101060305010e0a0b1c03050d 60
    0x399510800201d002d40c42890070041e01100e100302e441d40b0741022880640b00190406588035074075200d0300b5405125510001c0c2250101a040c0600d100103400703a14400a2a0005c0e4040c1004c004040c52038a40b042c22244104810020f2000055403d150710710140204802207801c110a400d005081d220281012101500710300300911161824420071b1440403103001c0c440c50650321042c018421141c42d500448140c580340c0ca00441290b9800b000a4941050a41002d402a00e04020300c0701c55540042d03045c2c20395080380f000c50045a1200325020342c0b844c0310845026004414070500700788404692088101d01b400604a0300d0b86034079100310508101d5000c02c139a05481808604005001a03404010305911088024210319850003500360f44031400314010b6441800e00152070a0000e003071090398007101030b481460040030360b1100400741c010442070080000b030030b02810001e15402c100b4010300340c940384080c2c15415125210203d61020219044048083c4942801555401d4002d84511140d0000d = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 821537877 1250 821536627 821536631
    0x40f02030a1506050306010e13230c040812090301092013021303031b0b010306091a06210c1306090b01050f0403110105041503090c0b0a02060411120a0303 68
    0x1c12541d50421104040040402860a40ca0400c00e00f40c100c0141c9901507001c2c00c10f242403105100005001848102030050654984443d006030602800310320032220403142140c7c1120b45400c034800f000ca004c0c0e4032500002d50320081d0104004021017000e02840072006e400400c801c21140c0d40d10013403200d409105000c46807880e00520300b602d84900c020090304082040ac43c0307071008e0311419200c80c00c0c1c0382c040503040c008040030b00d00d03002c0c17401c034081441d5640028903001e8950316481e03c8405081c0d103080542d04860b1000940300c0e825004800d0364080c0718006d203c101c016000500114883c407104140040c03501812020132110785130a1035903041c071120174000003411801d2199503011207104600b891304200b424440709040303110107002c8070180c0790000b1503007004140100040383c4078881c0da0000c41d410650780742e0701c1201c21b801d43c0040118a06c01e0300c44001d0907444072415a1580103450584005a0000f4003103408a00141c00e9404080000346c842d600d40d0040208603440c2028607107048001079 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 821539127 1250 821537877 821537881
    0x1e040f080901030e150f07050715020c0a050601030b071701151d1203190e22020732030306031f1d03120901020906070209101701090317040f140a02040f0203 69
    0x403600c0e08400d034047c042d41080c0e410901241c0303e0705003900e0b4090164209a500203031301c4920a8007040b500d034035642e00c04103c6090f50f850740b801840e5500180c0d00d80c00851020041c000c1c02481c4900068146e40d951642d121496a0300781d4101c0d2001045450040790010546210301103407102140c4a8809060310010350f51132103400f8030540030450a082d0130081026060703d40b00c1e260707200032040001d610601204140c00c030050a1410091052913070090011a089102c014284c8080d00c80d20010012581110080040131981e2602d030300c81240d06690507000754020741166a041a1640005010080c00068040b0088400c01040d41d070210904180d6101140001c20301c290300b00e039103900101e540c000750304140d4098041a81801070703010003032145400c02c00058034001e041003450003d1101d10450700e01c13206803008480c02044140c07020b800040d18019218610200304440900031907001c0d0204007162680c1e1a406a800d20281810170303140940300085015030340d1401101d001d040e100b00e0043e5070b4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 821540377 1250 821539127 821539141
    0x6081e0606120c212a040603030e0411070807080702030d0c0c0909050f0607031e02090f1519051201170607030b12010f051e040f080901030e15 63
    0x10a00401c040d10696006261050301c10010640184028003664038084201c02081100210203200300549003500c183d560402d40345905924140d0301c680c200109a84480c001c80c2800306030351641c000500402c145552001c0c490400fa4007540b01048103400481c14002140d45145140d07201400a8440030004a48281540303028090707070425181600380f05100310500d5807504140c0e2071138070a003c01075945000d001c041c840d082c454a544440640140e8200d0703c2c01d0b840103401803020110285440011140b175865150041c42160302e0f2040091240849001110801c545010b8000c9104444482406840c2e4200840003003d1201d4005444958403241807000c10715400780705910040000e8545540120485004109190003044074540890b41081070b0300800c44100042e280f039211036185c2100720301c1c1c2c41c1099000c036008100714800603032101c03072480e10b0f000c0ba5031040d40c001e000d01070aa012071000810000080a009030103041c00700300007400a220300d08182c0701d1800c460040b10010b00700528 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 821541627 1250 821540377 821540383
    0x906090b0f090a1509061d01050106030204051f05040e0a06081006140d02031c0513080f03040e090c060c0109020f03010c092603070c0806060406051309020406081e 72
    0x10110924401e04681d160000845984421014014111855080b00d02c101c9a071346810a60049800160900443d01482440310306c1d840e6221b100c003555440d2200208071280b0074001c6404448001b810f80300c3e44984800c4410740c180e5919400418000c08200000d190b0303000d180010701c101e14841c0c00298491600c00310504101d1102c0e191942d1030303d03108081c401803c202c009030300c50010542d0b00408041d0b0783e202080c85c00c0140b1090100102002603000b03c1d01c1d41c00f100504090010080b685422070380e071840d1603034034812580d0700190b07a0010b0000b400304540c0308400b250300204543c121031200401030702080b21507004030030309032050b5101d515400540c1400b00c2500c45c001025070080203180d80014000748401c0150059400d2940f0320300708440d510009002c1e03080c0c0101d820007500ea480c4510324044081035094402c103032a40c050b820005000c1e00d4203208280c103d4078060483c002408040000c00020214120100e900903075071000412101c20400168844900c010b82d07101402400c1055245 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 821542877 1250 821541627 821541631
    0x9050f101203051c090203030d0207020a091503082d09090f04030815040e060f1b070f080a051306030204050307050613120311010e28031e02010207060906090b 70
    0x54865585107100081c1c3c0c003008a54241c0398200c0c4070540e102c101284000500480c4401962500c000329240ca00c80460f81d00804405200700e4214103016540e1003071074161500029a0020094070314020008552040024840005840302404c3e00098038051004180c0001c1c0101c200c00c00e005c20344103010305144144d190441408040001c140c50540d030010040320001703181540f0144031481c015041e4696400016001c61a0015503a0034500b01d448210245800c0314082540c0d6603001d41703800058240022943c00c141c05c251030540c848032a40790101250b000c01030000810130100194500112a240170360054078003580d0150f5a1031900040520306141a000944200c0040107034460004c0c801140b441242d6040803440b0107500181030554903500c5506610034079500706400d2801da4000464070a844184d01c0c444d40e00100707891082440d0800804100602007017040176a840119040106003141000070301c0003525050060780c4500030341e202828219451030701c42c0132030010001050380140d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 821544127 1250 821542877 821542889
    0xe0c0915241e0310051009090504062406080a091e12020c031209040b0f061c0c0305040503031f080f011407050a0c11060904051335030604020409050f10 67
    0x5400c601308015014042509032180300d200d03210308004103a510303008190110040c01d400704104820700d0107041c45406000d003003100308600f2410002c101a002d01420030401501c400307a44502482d0b440e0b024a00c000d08003500266101d440e40309510151800c000a4180310a00c510311241000c22900c0002e8500200e20203001d1280d0000e502001d4606508000d03510040822540800c84207040e03404141210880750415820080000e0b66a1200c60072980511742e403d0041c0c42040b481d4a140800c8084a03070a03030b00140301c0c1e0000c10100d80905a5529010803a460095030500c0f040da458a016240068803c41d18406075102c07801004942c2400504640c028440d0400a10381a030f20b010007031103405c8205005040c0c1d0f021102004907078540c4801e6892034000500200b020b828030a200b2643d40c0d04114007145c500c00c04049101355120040381038101c9100402d0a2030141240b03e11180f07007900001c3c010781d0420342c203010009590209004083c015120031a007055142003255940911001030b810030 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 821545377 1250 821544127 821544187
    0x30c010318150b060c0d171510030609180b0c04060c12050403051509010b0f090c0a0c060c031407030606050f07080c06040c090e0c091524 61
    0x44200103050729051108154030040d070312544016888110020f01150600b250004004030309103414950002c0c010781a6034051310380b40c41c05e0503030400b4011200301c2100c3e100c65460003a038070070318241400d07910610000d5450901040a42c0c441c07446208951a5261101d900308445051009002802950075041120040554030303007030038a400942400e07403100d401003902d05410203254040d482001a00c0155500c6015112142c1814100b0120103900ba120101d495103818898070b2645400001d0b82410003020704072400d03c0d5030300700000030a40c00c004045070078804402c0310180003a001d48103292101d466510002840020b0140354086003034002c100d08103041c0f030680240085600b10313054440045e210002c50303030b484165103400c8849000c0c411241d6032500c280d606002c200044090301c8015583d2200c4104140f001c160503056440410300c416507049500d00012504040fa204a0131480390009410f4141048200403c051030080e808460303165008082820404d07442e461082c291040c0d014458 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 821546627 1250 821545377 821545391
    0x5010c0506041e0b1f05042a0c020604080105010e1303020c041104030b0702010e0f010b090c09120706020607170609130606090f0204030204110403080a0c0501020706050106020c030c0103 82
    0x21039540e030a000c1d2010380f034070120500c05243c2d100c003856070481c00c0303600030008652810108110b265048500d0b00f00144c0c3e100d20003000c01c05080c0744c49801300030422400200307601c00310760714802c55034804d880200c410004001e000d40090386072030b4000d100600038003000040760f6151444181c0007080c00760a0390040030f0440c80c0c84000ca0740c0012071580800044900080045801618003464800da5200038620701040c0200001150194071000183d8074160a81b404440300100c3e142c201d40f003100c002540a81c0000c00f08030f00c0b84200c0060522000c014050440401888246915003617440e0b000100692040c000c10011a078004001c0240c4e01c0384120b0311540e800d2060000f400c02d00001e021111205045440d0014014550020703001481c000b0820041c3c44000d0701c0c1c0002079445400103901a90801c0c20500200da21601124112034004050508007100c0c6030044580c1c91a04800f5600c944d002c1c071820b00498024441c0c94002c180d150014251003e00070189070421000c040c24905151a041c2 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 821547877 1250 821546627 821546633
    0x40c0804080d0506031911012714150c0a030e1e04020d151706100b0a1107090218013b010203041a12150109121e0602031005010c 57
    0x1c1551a11151140007144030703919140441d1500c01120030074007004800e0003036030b020300c001c0000c1c0000000080e40c13018180c0609200c0d080101a00e10b0038000300c403e000307000b0405c41815441d001e1000c8402040c00d285088122419041c1e50825042078030680c21243c148410560010404000c210080e02e1404110844905540c0c04440c1030001ea80241d03000074181c041c49446600c60b041d80458014003002542d2a2882d002101034603881c0031261340702c1c15001c01d40740c810149030342045071259407007170380740210804084958250342043d904c946c1c03140860124079140c1d640042c1517800c5180b9807a003a48814040010f0000d203c54070855a05585c0ca00141c3c4021002002e403c0c074004078980505c074104002c00102c0c910702c00c65004200e0b00e400c4184510000d01d010001300036244400e680240c141e160400120704502e0003540340c501007500202c04014050341204900010760084103648000e450000024851404000040315200c0e0700004104424480014070740113810203107090031003c1003540d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 821549127 1250 821547877 821547893
    0x30f2404080d05130b0c0c120c0607030b1203030406020d0c05120c0a54060804060e01021209370804082506030b300d0e040c0804 57
    0x1210510b409807180006080326040340070041400e58495a07400c0799180104208890f0b41024000071003074010501641c9124200c2c1d4151103403c134180c009003144d41c079100800c0d0002c09000e40036035088490709070b507102c00c0d007002c0c0b0145108070301802c4090381c1c801d9030407140c80c22103040200c0001448002c7c44644000c200305d102c00740d4040707980c0310300703950300c2040d1401a42c41341541644400a402046402d9900c0501880305401d0210340000350007030080c108402c810b02c0100c04001d44140708241004001e00d92040079401e4025004210000c4e6240c4008145030036640049007070307109584242c00307000981208002000c001c802040f0101d000d22078207002c00c0c0e46e2500e400340d000c03000c0c010540c8130410300c400642154001d200e103904035a020100c1c000c0348002c1c620031103034652070950480b0700002d26600a020380b2074034607401050700b1000e4aa0302d103013542d0914445a6484105240280004441010041c82c18001400d45544c2c1c10000100c080000f035818218080d01040003030401d100005241c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 821550377 1250 821549127 821549137
    0x3080403030522030302071509023f06040c0f0b04120212060727030f02010c05072c011a04052101230f041113060302030f240408 57
    0x601e0007040c5600c801903004a010310301190449080030340e280c45820150550f0041003650303c41e662070100449000c00a10484649400294215207410320b0038000c0c42c1400a2400c0c2c48884041040e045600d10640102106401b0448210b540c061418802400400710609000704032040f8640c15060500c0040701c0c940c0514481c13004503903c4c05001c2c2e01156603d81c0c05200414081003202c0d00740c5048280100722081d0100d0403042c0d03030320b042070020741d460306100c400c03040e0307a0042c03044840c85c4126801110696580c1409507418001d1180100701c0c1c0c000758041090300ca00c400e28050034a01c4002400c0ca1320b18040c1e0201d0280d04060b80d03407000451000007518211031044031107006080d81903071904804404441035185c00d500c2d01c00d241c4e4500c3c45003a1000036007518240702444076668101070464005050300c0c040c0083c1e80840c02d0a0003441c0100a6a014004400001c40c2403996680428a8039184050b4a4040d400079003507210f02c008440c1a5588081d828103c1501c00c1c10700341c68000c400c0c03044c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 821551627 1250 821550377 821550383
    0x90a0c09090e031b010c0807110307150b0a060f320a0207090e100c300207140a03030e0601180f0204051e0a08031804020304020a0305060a0902040b0d030804 69
    0x39012806101101441610300e420041d0105140040c0c084c0d480c030b4003c2410030a104041035190022441841c49941c060030341010500055241840c192a0a0300030b1082144e96035055172600e6280d07505440b202600b5000b031502c1d0b00ca1075889201c160003c4c10b17000310720504420343c80b6400d0205041407000e8061540e01d488061105036240c00a000032070402d402078010201c00c5e801c0006200b0080c42c0016148038501c011a07040086585d0301004443c030403050018010100000011065041c844005146103c403500500500c1c0640c280e0300c1128510030b00031402c00e030750060304a01c4241a0180030f03c0d50003101e140b01512140d810000148140908092648001a91180c0d0400c0301d246560444001d414010114182540c200846c0e0203102d42400d045070003032030b0480b8000f503c2c17500007080d5000d03910480051142c403205003052100940004005a07071043c0b0001c80000446c4060107501d00645580c400420f2800c4540140030554100c04a11800b820703ca040b001e010075403160343c41d40c001b54 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 821552877 1250 821551627 821551631
    0x8130b010932060109060f05190201180305030118060605031609030b0c190203041a0705010f1e06052e0c0b0703020418020f040308210103060902090a0c0909 69
    0xa0307180d00011003a4401440e0400049600490342c00307031182d003a041440b0f02030980ea13403032007940c80302c604039580c1d8501b04004001c2070050100080040941328104298000d5100008801580d526130074107012140005a00ac00c01c000014400000c0c2d030000d101040400c1807042c0315140c81c024000f06a403100414600c0d65049400d0480603d501c9490b00000030750b0170903503400c02230400202c1007440354070943d1541825108424400c2c8660300220a640c2281c0c0444000e03c083e4074491800c00056115440840d07a0b03560b5540a81d483d8011480b9501622a00a60000c103032483c0c0000802190081c1c1c02140c0b107003a408001c843c400300b41c200b5035074882c400700741c03205040741d1030b00406e507a0f16401140041000003403904000500e581a80648200d80017580c2c2902c848460118010491081c3c01c140b2110007010001403002c941105c0c0101000f4400071240e41c0621005440c0fa10324990a8200b1560b541c0c0300c426143c10740c5409002d0700d03007140311a0030800401c0c072601d00140c06101e0b10300c21340211507 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 821554127 1250 821552877 821552891
    0xd050a060b030606070c030b04080414181b070c060804031b050c0114070f050102180a0b1210080604050304230f130b040207050c091f0b09220c08130b0109 68
    0x8502d090321b050055611184442550800746080324098005000e036404240c0015120211881e009910a454030705d07070343c004442ca40302e002d0000c02d806170205d844c04007a482007043d90009440700c140e18004004c0d6a40c0c0c84158101482d005240b01003203012002e0bc80e600c810f07480c02007000804e802100d0402402c01d8600000d06800d8004203019400c40500300040607031070704040c04019001070034076130009402681524001c0003000080300c400d004006244806100348201001800d0119030004154000a00302a5a400f0b1309454110101ca040321300e508045020442541d410200115550f000e221602801074600013241102c036468007854800d507032a140c1000e0750905035001140c03001d0050300c01d55550420303091465503447c1ca90301a500558401e0009040d506c40e036040d1003402c1a6035507059009030b15242c2403801903084003489503484944240034813104904103c05195100b450030f0085406440a50050044a0018030213098000013250303241c001906018181e040d0761440400140329 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 821555377 1250 821554127 821554133
    0x4060e192d11040c09120f0b0a020a02120906071b030c090c120c121a0f01081314072c0f130602071e080d05090c01050304031d0310020d050a060b03060607 68
    0x400090b031b01030412180041807410900404aa001c05114012100c3c00019115100341c481203210f6401c081005030064280080041c9000c3c0c01400d0365100103150303608051194403450030300343c04505c617010b000309003400c104104507004450f40c2c0285548201004206681100030b061000c002d140440c042c0d96444100485500900408075074400740041005202c240303a00800c5048000410580300d8140f156805c0e903130b076104001c2c80b84510b0110280c036000c2e00c1305540d250103409e1500c0c800c0e8590f0107254004141c08504042036540c2d031019007210b041c05280c61010420900000e400f104200c220b40d800c101c020008001000e1074940c0c40314005039078130081c3c140865903207420021818070750301034041c0205101103030001c0c1802400b0140200a10340320f0700481d955501da0b618805000c40d0382840040c01203030180e00440c0100d4610802c192403020080002814000c1d407a800000c090b034007003041d0858801078802c2551018042c082046581c1c01e000f01402e06000041200340b00e040001818420 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 821556627 1250 821555377 821555387
    0x6091a16022419020c04050103020609151207080412030501050609060c010b0607080406020d0503040f060b06120c0d0c05040308071407080f0601060806061204060e192d11040c 77
    0x1200c1420030351661654240c1d141c0603d1030221540100052181080442031403605100d014100c0c0d5004200900d8040641d0500145011000b201e40050300c003800080602d100c20b600d6984a0902c55440054900d09890282d2124410280c1c0808152074040103004139100c5400b120300a150844016464182c0100030901402803003e0090300040301080c5c081c104603145001c0d0043e1240768007601d0540203c500202c0d00b5010450340603111030604003c0c1008201c3d1369005510010003d04400d140c11100c024044014400350b56461240c00d00040442c880300c4c0c6845002c5a102003480c205241502e580c5682401c0e0003103007805000e408070000407048c0c1e840100102401000700000b0b41704030503151080e59845041c00d104100200304003200051961a0141c200d88010025001d00801a1160703107958004010840301d01d80c0c54810b041d1002840f1140107400e0301110300c510114607512440e001c40d01d40400041809000130710844074185c000406d5400b00c1100c540040d24005001e2258850403a8 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 821557877 1250 821556627 821556679
    0x8030108070f08150c0f07230609060705160c090c090504051b03040219030f060609060506040302012001020f040320040c1d01020a080403080d0b0a14060f090a06091a1602 75
    0x54800b443c448c040d2031040802181201101002a110304c2c1c1e60b8551480c0e00c607041203a0030340024008009580030320a500c11b0600c601402600c11012450715901c0030300840b0360b0122190003041c1a00001c10884c42d1501489074000340b074014586400a0903425814180000b810092050080c507220030720315284094414015a0003000c01421049c840c181140101954000d0212290900e1400314072420a00300f03c2e400c990b410303540c00410707003224065010070306000313481d40307c065400b000f0301041004075502401c055400707519040641d200144802803c4554032940a00a50034a40c0035210540c10244240c440c1030b0300d22240540d103540c80300407400c00b51006002868454049004814803000c0c4015082d5041c06030400c012170741d513030302c00c1024100036807060b03a410301058440c01605d4144507014094403803481440d1350500908400180f241001604214001000380c2820850301340600116501484800009407601d0030410442c010740c0d41da003101900800c01e054014182a4101c0d02d01e40e = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 821559127 1250 821557877 821557883
    0xa02011b060203041505070207051005030907080706050a1214040b0a02040b03071106061203030106051606110703020d0903150c050910020c10180509070c08030108070f08150c0f07 79
    0x150f591500303203007601c8400541c107400d510b200d24140014480b24000110482a40c400428004038031001400c00c40d0390381d0006001c1c10050040b40000201004100041d002914190300c030035858103404803000f00131144480c0c1c0030801c141413081982d050850310b0343c0309800540007820151240e4445681001078030460b80500340d104800801c1007070456010000c07806441002013907801d030f910341c00c08001c801080401800c0441e00104010071041d8000d00c0100300d0202c000041704800c3c2c1072070300e4030012191740c45d10009d82c40d800000c4107010182e0511005081449030304140143c00e0a503150580e03007520091b100150640d0b2801c0b4100341c1c501030810341c0c40c02e290003803e0350090301c4a1180292500140300a06001c2c4040803000c0a42d5401449045c007904210040484014580b500704600d00f00054030640c18080540b04000109031480c006501030a000c40091004901e818040780151500313600480040c0c1254035100040100301005075041182c40e00c5071a00d4407068441054223116810000b = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 821560377 1250 821559127 821559131
    0x909150a03050307110414091e070810020c011b020a15110d0605030d0f020616090509010803030f0114030d1d060705010501030218040b1914191a030a02011b06 70
    0x1401000120340302031a4810040e54140900b0081f541000c0c0645000d07075420420340c008034886500c0c449003810b48210071510b04200d407103540d1750b560180d0074001080142441e19400207035916038031000f40160034030742615007074170282c0340da110030f0003500e608003200002c2820042c03804844017000e40b500710540181d06141380c155110f010b458482c00522051103424020700541e00f000020300d019050110654035150017619160740d840c1d03e501c1c200f1180040c40024030010800200700c64494103042800703860f008000316501c0c01c000c0801d16009505910501010481102c6480e0684021078094808003c034182031381c1213094516412840065041c045410100115800e1f06201c4150400c030b0407030303000b9202520200340e041d901040c0140c0458000d0008420080030803402000c0d4162020310001f0704e20300140500c0403004030024502c00381c6100440010103101032982424902c10420f031221120844541126280e001c6034071601110300281c14800001d40e2251008520500401e4141d404041 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 821561627 1250 821560377 821560387
    0x2318071e140c010e0f030a0e1309050a05060406180c0905070903120f140705030f030a14131101090e06100507050105040b010f0e060d02060d090605100504110909150a030503 76
    0x20ba4000d15200c41c2012091107000340c1401896030100848401c40c40c5a91010000aa00001d100342c00f2403015046081c40c0c0d07160818004603000340558901c03182f066003c0c02c02410141402401d4031029054a600107500c18401000a01070000c5002290006100460a030b65480e2064800710316941c00904031a800149440e002903001c01140d68030030303ca0f251206151100c03003800c1004c0c003907070400504640c410040c03041e600501002544d40682e03600d0000c00d04030070461030107050385c00559085600b241242c08507001c114020104841c1810203180451656144c2000181c2c6044040e001070300a1f5406a507825203203100700200c030350140e04040240f00f1402d140c81d1085210009101c0c40744030322100e01000c04c00362483c0d0780460280000802c7d880518982d81c003000440c5d80300300066900c1c540d07038042e20300c00204a4020107206100380c11000c0529441c20040c07000b0b5484030003000c0c44919003000308113001d686445032180c01c0346405030b86900800c01030000c40c0c054649600050017900c4040340c = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 821562877 1250 821561627 821561647
    0x405030d0f03142e0312080c16050a030f03140103030e0d020909070e101512020c06092803090b030406060e0a020406020d141605072318071e14 63
    0x58400f001010200e03413518102c052800d200b0b651801d00004150304c2030840e446003a90701c5403403000d80001c070843c005450710b900058401142ca10a40c4200d40f250812040c0406154000082110100c03290609000710820024031703040341e0b44140001002c0c064a8102c400443e02c0b04205400b050380d0140445c00b1500f41107111aa5a07440c41c81141c8440f50490000392020070000c918504542500403030400107241780300240d176805403254440e0f40c40ba40c20b000c450810f010800038640a00c111901810b50150501c2081c04407410315540c800c0c070800030b20395410000790311020840440703014000aa07162b450314945000900020340c883c544c14170f40e1605000c25100241d00034411954103408980c4c00301ba003030034103540c032440b02089000700000900c2514160b000503441c41300341d46e21401c00e507480c80351144603d0700c0c0115511040140710381404807406190a080456080d000552480112360703246c200c40081221040150308689a1a82240e00000a020780f000c02126981081441d4449039000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 821564127 1250 821562877 821562901
    0x3070e0705120c041d100f05010c080d11040b0915030c1209120a112a060702040609020406020a0c0915050607081315020d030506100e030c0901030606031202030405030d0f0314 77
    0x70b03910344100c140030000007e484514a0b2540c01711101078440840540440d11050200d40140411008803500c0d0342e9105800c0c40c031600204007034604c400845455004485c10300400d0740b1007458208901200b0010310598003039820550f0840c80720515210600e913100350110382031401d000d140414000e008600300015640024040300e010341c880302114003180a900c0035215940600320002155550b15030080510300744800144501400580b000c218140c1e164008012a13126030b11110050f000b5000c02e17020003003100031510042041d1801441614001d5024410340030452140074410740c0001914020007514000796041c00981c10300c00302e41c041d603c9100c50b41d90f0a4001c0c14074014001c1c1d00c03036a109903010748580c074003a09001d083c0c08884c406070340040d10092000600fa69062203604200e112541e04e40001ca8061032055030b0100b401c51452500103650300804c0c40120035904140814441c546001410245c0d0031264a444600c9404000d0260300415400c00d440c6080c1e1034400070800520115 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 821565377 1250 821564127 821564131
    0xb0901031e1407021917090d11030c0a0302150306011806030c260105090903070605090c150f030606070204060510030504030206060d020307031b0b04030c030203070e0705120c041d 79
    0x30900c48080d0b4511000301d844174003c8402c80a0f260110b04c900c4041405040075100000650301d400b450041070100061460030681c0703088410850042c1d05495604050002c040040c10a1703400c1c5403d0340c21035000072091140d40300110000748003c00004e409a00c070380c42d03c3c3d41d616614003181c1c0d2001d454120003000b9003c50310700315002c240d0341ca070b20100e01c07101c2102840e103035007004480780e0241e4200810000402d40150169080c0c3c4070070f00c1140c0108002e071040600400c9207100501080794045c00340300e50030003108680001a0350500400f4408002c07102140d0740034504807a4159601c505100040c0100386a410050f04554515041b0710311a8040e4051805540650219081d9565210400002c40030b5880c0c02501034004000c200001a0300000c0c490f850b0301d45c0c0d07082c0400d035900d452a01070340760065841981d145402580400a42c102032082c1001b030f00401d103050000d4600343c0d03005005445040e46030800291300c64009624201448250b501070314401e0014080121030009146100c141 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 821566627 1250 821565377 821565401
    0x1704030c030c05210a15110d140a05040302060a0906091a0712050903072904031707050301050a140301140a0f0e0a021f03060e1e090105010803040b0901031e 69
    0x104c80865140034600619110030301840007000080c8455480c1c400c2c1e59202e556000d01c1c1e41c1c6030000040340c02da812000d440131240c4101c0c00200e1400004c1c204a00b0700d800b034080002545802e0902c00403a60100c1d04c0d6604c011411000314080b58a850000020b104100c00541001c8426a44518021000b4400c2c1d00035080d07581c440000d020307070b2800700c8125941a0340540090b030081140d8000140a034940c8848080c002d03605015221000c003640d40b000000315401c0b000503441b201d001c0700101c443e81125412204038900a800e560422000c2100c94045005451043d40c03185103880c5166025003003400d1007844040d44c0300a07421b140c030355000030308000d440d0004201d040500502548a0002e00c0201558004200d2900e141000074100311040c40c80340c61504140e2210701c0820080c00c6406000d0055043c804140c1500c450040314015800c4050301074900c5905003001001000b4000041c0c605481c00d403004142e640f4079110050740189440058180c0e0005008901c0303200c02e146a0010b240108 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 821567877 1250 821566627 821566639
    0x61b0d060b30070c020d080c01240f03080c010222051011121b070e040201030501080a1a07051b0705040b030d1421090a0302010e0d0503041704030c030c05 68
    0x700440c60000310b1411403140c0e01200c4940008400c0d52180c035244a013180042e112000360740b0151641c202c01d0f0311150008445a441ea003004150795204203410441c00c0300500281556406d08040007030211883c40003030710a103004540340b0f48480c001c0d0704032034480145018107400d003200702e0000030908000d071080300d00c5100f012100940072401514510160700e11704001d0050b01d030341d092543d6032a810007195500000c4464141a00f907240c20462000581002c18038000c142c0b03050f01c001001d0741e4058220304402d420500c2c5500000e4480106a2103804c2c95903007a02c5030381c2e030389003040314180545141d002c582480c00c6070700009204086208400e0f135805030360602002c0602c50515036212407411084000400c101250003081503014050003000140080305100c002c202000100c1002042d140d21410b60881140a410184c0910820080e6240e00000d00700b41c2907501700240403400000c05c05054a0b400c0c22640c40d2003a0001c0c2205c0140d50310400103074400707403281020310190045c1c1c007410307010340 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 821569127 1250 821567877 821567917
    0x219020606040207151104080a0812010b04031101080402011803030e150a05031807092a0305070507021215010e010905131104021e0c0c0418020102061b0d060b 70
    0xc2020f0080360303039254000c06031108500c4060102d2005041110042036401010301000c04e4800302481070007061401849155210407001940d04103809c010380c00307501400c0b000c100c01c0002500c0c2c400d030031001c0e844c03d081240c4240d4403800140c548007081ca01384a4003401d407a4011007016081240380e800c2110540e0221503980043c40e00303217118450003807040c010500510015050410101e00c0b0180140c081c001d60300210f0b038034154002078511448000708010700c28140e6000300c0304005d07200f502e5820309142c18409810015170140c050b02c60342c540680680034400d0446c490903001c100003030600c0d1a440d0000910340e950041e5080c2200d080c09000b0840d8144400f15a0f00c208454502120a81044410328070340070860400c00250320003801c00300007000050071244500402c001800d0200c603403e010303000040c3c0d00701c20001116001c2c02c20b49120025207103440c1c0540d900050b180d510002600400c1e040c0c1045520f240c42d240540000d400090b42080c601040c103180c5040a400f0005c00022002c1c620 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 821570377 1250 821569127 821569129
    0xa090603180201021c030e07120201030f0605090109090807050f0f10090c0e19110a0f03050f04020f03070b030a020901090819200d0b01030b070c1a07050c010219020606 74
    0x1d00840000640180c1c81207030404a072407070311061943d01d2041800c0004404014403d030f1820140300d40e1001d030a03414942c0c43c0fa01556094000c2c0780c2500914102004860b0500380021640e41043c0a802031450b52402a0001c20640504846426070050200c5528240c076185090351512141c1e0601c40c580a0f943d69110140d0082c01843c0100390f00c00c2011018500344141c05001c604005c001b1408040601144042c2000070f01c90625a880e1100400342e803440b06000103040c2e0a1185000002c05180400700030f5403400c00100c0729042070b030484004464014000010340341030000d0300100413004000042c403648031b0040c1d000b0000d0010a898000c0321544d9008059218214003040700c59100020404000049241c8076140c0307000d4444258a0030500d005001c5000f50b880110200c80308000a8014014000101d0074280c0c026035034074100a500c249541c1c2c43c1c2c000400b00701141e441ca0550b0000c00e1405000e0415030300243c078408000c40d2101480d411313044080301060101c1026000340d00c045003003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 821571627 1250 821570377 821570411
    0xe04060504020a1502100209041404050d080106112508191205040e0426040905010806090a0512070317040f020405010503010c05120c0f0307080106020d020c010f03020319020a090603 80
    0x1c071307011940103420201a648a200c004c1d6102c01210b43e4017950740d203280004000960031042c00340f0702500c000c05118222080141040c54182c00010038444500b00f624000440001c400824111524000c10780d15001c2e01182c1600e4000d82040f941c07401102c2031071120141c20030b550b80d140c90080c0110021207410303039026a024403850150402100f0310100003004039000003190703039980075080380708940e200440070706c05450341298020414281d282c1c00100407100741005050b400001c510042c0098449550324117a07a54044e841884003214081000401d01d0f0088c15048011070b4403011880a0780f41c00c1c50490300e02c00c080c043c101d103c4e038905000450359040503c9281c0b13000c06651912841e005407242d0700d44005074006c0050b105500108010030f100c0f0520702c0511300a558a4860a00325410071402a05006008002c01c04550065110b003031542c5c1c0c00403540f03c4a210a0500503940e480b03941d2851a9450200082ea002034000a039000c6400c0d80f00d81150200c0380d07540d03403c0008042400403420 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 821572877 1250 821571627 821571659
    0x3041724070c030c0c05040f02130e1e071e09060f08010513090f1403030907080a0c0311031c08090c0604030506011401210c1130040e04060504020a 65
    0x10019442050202c000780c000c40301c005040d0301404104510958400025080d5800b602d03458a080745c0206a1261000c03041183c10003500340e06c0000340c1e262825041030483c91850709850080c880c00480480d450394020260041c03c040f240200320306402e56200701031305800d80e0b07100c0c440c0011118031940c091300b403190304094142e03a0000c1c00305000c00725640c44080940000b09060705e482c3c80202e03d4400107509450b80a400766064809161079150125105003840c4031a40b20351a241c0001000b00002842401420242c03035001480040b442c3c1040007091601074200c803180d1a80d1005230b10a110b030790f0011100742c03090080100316000780d8100c1052204a000300d00c00141241d120100611158512a104848001040c0b40101d0310008246e1580307100e824560a05101b0b07641c43d8000944154041071001034540404000c040600101082801c81c010f840d00102c404444c0200c08143c2009002c101d800400c20404145e90300c2c10103090110041000b43c0c1c04078415041c140c0c0000e0640d8120451340 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 821574127 1250 821572877 821572891
    0x3040f2f1e01020c120f240f0408120a0608060f041209060543060501090207050a020f1f0905100c0f03050a0e0a03030c020102010b01030506031b0303041724 69
    0x44a265100c240079071031038001c12802e241c0c050008280e86c400c0c400c20045a0505180c000404038225071103070401001d402030308024482c0310b050200400700d480003046600a211500102c080b41e940d07083c030035004250740c0e007001a4134054a403e2100038040c0600b00b0340614015100842c010140041c1030b0303012100c92040f00049881072104800034130006660311941007025501b102e5000c0441c122940c06030351040c1c080201c41032220303010203101e014443c06000d031032032140840c90054103443d0a40d81d4498200b0003886208460780054a6844480407104020081310070b0b0a50b0250300807001c0c0c0004c2c030b24002c050007505049140b8030307054414019104140c3e00040143c915039200d4400700c1c2c2a03480100034101f07005028139411100d44507038028000440c003941d01c3c00012140761000909494100f070545040600380300a2003510360340807500320850b5800301400203034604841c2c04641140039036408081002070000d4020310020780820081c0e0781007100741d2021071400a0501d010340c030510503240c003 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 821575377 1250 821574127 821574133
    0x30f030b0906030d080c1201030c0609080c09010b031305100e1903140d1808030402040c0311091318050c131512020d05011a01090e060603040f2f1e0102 67
    0xa0300550003101c5481e04801c4c401c0301e0510303100800c021f00070528400c0c1e00c110740d100048641001aa940041150042c00c910800380c21000718020004401d0302040c041c07110702200000c007140c40c1c1d0040107641031000d648002503410702031070311012200904011074003a546004018069a00b1f4118001c2c03010501d9040d102e0700c2591165500044064001100c503042071540c0b25540f510034111400c140d8030b0f04e4840d400f0240d582c50f01e171040c00300380e440e045401c2040c1424488080070fa1399404068820700380003502e0f030ba0034180507a0108800f500c86507074004031140455013414140000420651011401551180c21080d910310854080301c0c7d10301e41e182c08401344503000b0b00945054801d5400301c43d000801c9030040d2580c81e160030742101c5490600f0340d90081030441d0841e540d600481c4110080c0309461001d0803e14020780405c0d42c601c0f00520040411140c011032408011104442501201c4c7c402e190440c02d840019400000392100c081c50340c45500303684034009440003c552020401c100681c05 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 821576627 1250 821575377 821575393
    0x9060614120d0302210a0c200a0605060103110301150e03030c07050f151306080601051c1119050c0c09040f1209090f021e03091209030316030f030b090603 68
    0x200b10001e40241e800b0680c00440003508100301e0451240150094102d1840041d036200d80d41030151134612381c00d80540d400c41003130f0400e1840403000705411042e0b503007007070001c13a0300d5440000403801020300e00066403c54001000229183c019405080d000c800e180d11814050403007441010759030b00a240c905030081d80038131018085814401d954a202500c054482400d0340b03004c4542d4801e68011740348a0b03105400c92001081016030001c8141e4210b0000e0a28525003007407443c036445584202180c581059850394038141e240400a030440b185148900800140d0301c412030700007842940050040354080c403c9010b5498607251200b800c0d4019039000140040540707540d91484c40c070b44886540c0d9000e00c001881d0000341c080e07080c0030707092520103084401070b038a804002905030683c150034801da00702c0a0038400c010313841000284c204503d40101c40c1c100c1c1c5966440c0c0c0020b00e18411004100d141542481304641090307000b00c83d00a042e0100d40781030003141108024401010b00442d2502e50603806981 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 821577877 1250 821576627 821576653
    0x6010201050112080d1407020309010e2202031b120910060e040f0228030b091c0516021009140405040c1703220f0815070e03010f0906061412 62
    0x8018503105c94820404a109451074281c0741c0000d400b2520f02c000750308005000310303580d80e0260320040b101e40221030490080740c80211142000c8010b0f030381c5001095000010880d00c6e8000c5542d51aa07510141c0410754072509203880c03040b051420359042e4182e2140e2411600000a94020322080c0c4182c58042072107680d450b10783d940f40d5940341b0410398010309409a69054802129000300c28400c01d5803126108610754a050040c3d144014071f514583d41009003001c06107841001c41c0001c1082c6450080d84440096103056100f02d00b07100025440045003644100c03ca0700011504126036880590020400750503043c0001d0b1138046800030250031510b00207221165a5290500c00321408000b20b90403e0b84024042e121812036007020a514560068200310070060356880c44003403d5120003800201d2a20440000b8621000d40781e00b01303006601d10140d4540e00c00f507203c0724040c0101c83c0207101c4100f00d0304001004091030300030400000c20000d1962200e09241c045000100f2018000300001d4105072 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 821579127 1250 821577877 821577893
    0x8010909050a0f0f1a5b0905060f0301092103020f0403210f0905150f1b10060b0409050c090d1505010608060f2803080705010506010201050112 63
    0x7008070b900d8000c204030000850145074003120304888031020091a03090414021800d16004220600c4100c60710000506e2007510f140340100300020120702c5c414480e14a90210b10181420301120046403a130080000da030251a0407040c0135040079a0084641440501810700707a910400c409080050b002c0e940101004405150300452492850010300709852170822501c2d82d8401d40c010364901881740d64a240700601d02d038002030285018248205070410b001006041c00007503200f1203100f03c01507998402c0030300301081201c827010160300c401985c1d840c800a00c90340c440010007840126114182d600754806006104010a4802141405060600e00541840580f000034005004194140592440e5407902940354420301e218107004040c440411340f0780380444205078070a00404c502201800001d48a4424048131504103072081c2d040e8030382c0c00c0080030042d101041c1c840c0c4071032381200001042c0301042015048491003000240301540f10000120b0a0301c2d030030f004804400e9640803110000500c08 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 821580377 1250 821579127 821579153
    0x20409141005061008040b150301111b12040807090b04110408060711010203190e01060915031106040b040605130f06020307050f0303010f051e03030f0d05250f030b120d08010909050a 80
    0x10f00101d40390381d03400bd000b0240d4102a4203030300b600307000d40070f40304450741d081c00400d8010001c25111804d0900e4209410f54921031441050100d0790b85245064850b102c50f001500da041004142c503654980c0c0340c0071726139944002c40320400003408840d40e80039068818000c5a0207401c01c0199151880d01031007803d8001c00b00520000200d40d81c0e150001100d4840d40648504204c10619030740d0018038505040301c900300b04013005407140328200010b110085c0c0c004181d40aa40c07491920382e1b150484648030740702c01d540c0c0b038001c032a5241d0350090001c2c041d2b500100400500340302da8180c48043c0d5900c1c1d046a034a01080c02400003c0e440c101c1c0520507420705102060f00a44111b0a01c0f48490020022900319030140d03a540c03001000000f0f406076403243c0c40c000d068010b040900102f03801042070500303071480c081554a00d41084140751809a44600c01d802c80500480004c100d025906881c40a10707565000c1e152004c1d01044a4400004101c1154800d0f1004190000007400d070582e0140c1da102016154 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 821581627 1250 821580377 821580379
    0x131d0f1f05093d03080706150306050a0f0e070b0a051209060103020f010c0f060203311208010b1c14070c11060f07020409141005061008040b15 63
    0x14020000640399528122a8040d4440300310121011510b0245400e12039800d6a0410019104007043c0342118141d4401e40112500303d0388081c0ca4038040e15103e0080e2080f400d03010340d43c80006601006120340340d80501d00521045800b00124800e80c1104816210341420841b000d07000440c04000c40b4039104c00038a002101450502d103408100b0721008103012054600070f4241e48140014030842c10200b801403c4a0001d0800c01004550b50740c039902c01c610080340042140341c011000c12407296206900f80c810010b00000710000383c040710101c1da114407a00f242500c42d102050380c5001094000e00440b41603031aa11400c3d480c2135a0390032080c618140030350550031a1642d644002d004c10004200284c02a0203540d291200c485080c1409805400000461803150304200201c144c0c0341300700710858441d01e1b0b042c1e5000c140c0c00c10230b041908100304100300c0f0100ca07000f8040c014250150340d9100718170a03001203c20307000c101d880003021034100908860040105010202041040c0da200307000044c0000 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 821582733 1106 821581627 821581681
    0x4050a0210080f0a2a110f0a020f1005040b09030703120f0807020c010c03030e0f03040b030103120305010e0a050405070503070807092418060308131d0f 67
    0x1a00054038164280c4a003c420103603014212506c0580681000c2e90509030310882c030325480b500015001c0344a2894041d10600b145001c020b15424200940c0c2c91505150030700c4010180d82d80014101941072054560000c0000c0b42c845c640b188480d8a603540b884c1e4403101b1440580b01340009000201036410180441d0a540d07400700f5181885505464085840d003414030f481804c206d21000035480502000501049641048000b14101d0307100e00b0018034444444030045048420030b018010300030798034101144481e015500080c0d0807500420503100441d41da0400203140440c00d502c200b080780c2010404104103440352281c001140c031116600515950103181558040000c2e028200043c0200401e02c80d5a20352540f004024650010600d46d03208440b0001420905443c0f082c2c0036140c60b40c982445c0e42640c41c80c00e8074010041c003c8000710548418094029207006d540310822144 = true := by decide +kernel

theorem cover : BRFrame.Cov 821402877 821582733 := by
  have h0 := BRFrame.cov_init 821402877
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 821402877 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 821402877 ≤ n) (h2 : n < 821582733) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
