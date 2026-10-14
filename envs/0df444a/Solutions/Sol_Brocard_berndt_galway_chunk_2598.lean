-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2598
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:11:07.275388+00:00
-- url     : https://prove2.me/submissions/15465933-0d04-4df0-9678-25aea3b9f5cf

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 467086330 ≤ n < 467266187 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 467087580 1250 467086330 467086343
    0x30403080304080f0705160b310911130e0f16030906061217070209190e032107020d120b010212120f0901140606071b0f05010f0504080a 60
    0x2d070a00100c6001d41c0c078515030500403196540c2c114642181c4628041c1c14088054258241c04202c4a05650540d44210b020541d00710442c40d010907a90b4080140c1c041e1400d00105032180842c12803128010240300c4c038170700381401b42c41d00c54541c9007024802060304400a40080001081800014080b0141d040b6103007804064a00300e591004402506000001905541c10310708001081180102c0070f94010340034040014140010203081d00041c46080b2010b544600c0301d0b804600b51003442019581e8041c1000c800180b162681e4400d00d085401c50080102c104c039140154401880c904c4100c154031400c2071024113203d50f00000302801e0072582001c0d2016039036407862190a964000c00c80400c0440402e12200e858441714200190056012503009110802c108003040b04030320140240307004081e48082d105a203a0780e0302e0904c00c03141c00c2102c0540341015004082030b61908075051080140003c7d0b00c00840300707401c160000d03001c0103080f280141008010801000044000710b115018075502c10f2 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 467088830 1250 467087580 467087587
    0x90c060a020a050706020f010b040603050c12070f08030d0e0c01020703031808060a0b0316060822020409030801260a0210020106080f010501050102070b070f031808100e010f050903040308 82
    0x5000300e02d008480c0360010428451110b0116081d9000101c842da40c00b840c0c402802606040300900050310454840100070307034012160319400f0300c1c241035506a040d400008960202e81c0e180c500c1145920f41c1d80c08486160400600c14841c49480d000703a601002003400102144054003000039a120f045100280810120244840190180035a00030040c15030341f0491305e4230308202c049100100302c9508000e109100302e0085005030340440b07800c2004c0700c42c140c6659205954079003090600c2c48404000300400c0b000b0604100040e0799911503074034924040d0703591303204075130401c002d1510a04080c40880407048111032181c40f50355000501c0c259103581034400c00080802602c06a0246c007040e00015980e000e94841c1182407801540100d040b00c4090f400c6510b0030f543d4504616241c03160441c0a045400035240d064042400340f8012a0900d003503880c03240c42103a075030b0551803c018001040042d00d580f0b5100039604003509010307001495459250800c103c0c10900f9041e0365a100b6440010120725020 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 467090080 1250 467088830 467088847
    0x4090305040510022b020a1119090e063303010902090424090c1202030c040c090e10050a1a0c07030308010602011406060405042703030b09010905090c06 67
    0x1041a500109000f03407034000e20a0030054080e48403080c4600007100c4100b40f0280d801c034002c00302c0341080320040301e4018010340e01e41c0740c072071001000382060282c1d0030407541c2c002c4201ca840c500d00f0000061411204c000b505403003908804c0c0c20709102411240d240300e4040305103400c050801c20074102072603030702607203a4610701c000c0007290141010240c0a94031a01c80800c01c0107000b1010316030035407284401c1b64100e03c0c1e0100c0060394100c46c0d00c804c1c041c0c11400350103000d019588440786c400c030289000600f211020440b460000302075580c065213a000240102c64200702206000110340e400003044681a940c01d8140390104103045040e1003540052024882689a0741510740b00b00c44070030100c80242c40800e030301c03400d01800841007031143c40d00640c60146c00000100c500103050340201001003049242c03034549000c0002034044004101d004641a03442c56a2003212441e124600610035280032401e40010f40801034240e005a0000c0d92807810001044000307400070032011468074089900548520ba0b4 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 467091330 1250 467090080 467090087
    0xc02010b03031c0b13020a0207060309080d090f060603121d0f060f04030b011d07020f1f022b0e070b09060f0c061f05010c0503030103020405041a0a020d05070914040903 74
    0x5500c0c2560f00308080d000504120b078906d40003000007407055000c8891503566000110100c1e00443e4010709559018403200304881e00395003103a00c206003e0200d9840c010a1a03c40c48112025a031007151941403480b200c0e40b403d07400940d806060030135407c11204c012042008aa406245400e02d10b105180028404141d00b1400c0d055902030742c4c0002c0303194130941e1a0751400c41070a981180d440c11205100700011801480059076070400c822003009080d01c40c10010101d4a050001c0702d00760030180c0c0a0003941250030917042c2e500342c031f440d91100f032912800750760844504907003440c0586205034106600034403a03242e03108104c54110000391041d543d00c4007405642c0480d4012101c0d5488a40140424422540b0007110001000d02141b0504000590b90300c005446102d00f51100801940080c40100050b20301640415403003400781a41c641098082602c50080000c2200d200d4030856010940f5100b001c03440c03040540c03012450400003070391400c0203001000c040c00711b003640384165110f040c9803041620 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 467092580 1250 467091330 467091341
    0x120a120b0607050a03090501020c0429011101230f010602030a1b08070803060f0418080d0e2b022a0409080f093303130b040b07030c02010b03031c 64
    0x8001044d40c0c2c5540c40761034000c0c07200e50907110b098010700c1900c2490109103484e20581d11031598064140c0c2d00300703205280020003520006101c9050143d15607182c1003800d4207010b164030740130402560b185211900e0031181031508024124040c1c0c1c101c01c00c01803000325000800c03519501a142012080b1021f071700d400c01352241010200030440b00010400f0002c200108e070255006000842e00e000100440f03806006c110b500304c424200d00f109207541583c0104d09214000c0212040340e00d00403480d00c80300c80c03405192907180124031441d641a248000504181e040d6440c244903910310181c1800510016030350780082c403c80031650f02c00b02240c09213080359038640c0403440c4540d1010380b2580380c0d450640f0f40d40c21a08400c0f5411702651111050b41ca80004100c0c0c41d8102c0d0700d0100d0303007c0445d9603956545141d90801003003501c400800e00e40d92004211081c4405104501c0740e02c941d8503074581740000406444071140118156814080c10581e181c0d8044103a490a5414a41e4028150000304001c3c01514 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 467093830 1250 467092580 467092583
    0xb0405030706090602091c02150d15031109090d080c0a0c210905030a020d06021b100b041b0e191208091813020f04020c160503120a120b0607 62
    0x1032403c80d8801c2000610340103005400b01c00c40d54103e8a40f5000d030180e4001c0b00280c07000794410002e40c4070700d0000d600c80c1c1c00380040300890f260000701d54084455019081a03550029103080c8100000703d0580d03e07101400c183c1c000481405007002a5004402815508000c0c0030302c000c3c0c520114405000900c81c442c1040e6480d0080c0301d11100340d100012024800c1492400c0388001090002d0100d10f6090002c4d45048440d030107403541040c4e0310f95848500094104003001e420010380544140d035010030411040d031200724070f9240010b44500e20000c0104a8482500101440b02c032501c841c126560030254007003411005071000200850a01c400c2080d81009803c1040c020440e04070700d4090152040245c0041181641c6d0720242d06074400307000b800b080c800c48285030441d40b0005500700608158940c030200d003501500147c00d02c14005c0d905070616401207a07030001104000d10411407032800704503c0001101d0709403160300d08411194010010407194450851003929010a81c019031144800c80d101076 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 467095080 1250 467093830 467093843
    0x7030b040e160e0c1e070519030e01080a0513020d110a06120e060921120f09100e0a0305030915160e01080105010e010c1b0902040e1e040b04050307 65
    0x40002c40c075200c1e03030145028440d6a00440000211180e444d90112240140c092000090038450031081c1c0d51070740e0100c40c0407070b001e01034068605e66102d2000c0d40c24085901c69280c01030b081084000040c02c46d400204000442401c182c1484107041142106030a40ca0301903448518144681c18105203e408a1b11420f030003600040d000600d440c2d00100444d1100e16121043c0300d4050f21400240d07681d40e040e12100c195400011121000c40418007140500859021810f424020075000001e85040111142031004209034100070107943c007803240c0307041c0045441c810800b1078462403c00340d4401d0b001d04000c0030f0000000105074034a2040105054036103036502001c0d0076141945005c0d1041d1403622400c0c0118400f00c0c0301505542c026040581a5031040c0d681400e42020740004442c00c941e4158161184040c0d00009814000f540c1140400f03000410300c05a9241d00c1d003020f019980500600b000410a118545030f061440c03d9400640c01c1a00f100c1c1595003a12181400d50a5104218000344038 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 467096330 1250 467095080 467095093
    0x30070215030703020915190528050a110604120302090307080a03030c1205090c0103050a02130902090a081204033903030e0111211e032a0307030b040e 66
    0x1010b5064004054000c0103035184140c8204410001c1502e0041201f42c1c01c065640200c480446840344011305480307101e52071586050003103020400c1042c10b019101100040002a4054107560420200b2490302c41503802807070145420f4651240c201490b0341c1c10020550002014400c6980410020014000b40310903949400c00307030f01d0702600620b2903858500c0030a001e00c6801440e0320852107854890911034001d010700148540c0110010080284000b000650070321601c00d240590b411101c5c0030f0603a00d2801652141d00c0300400c4207800f01c0c2e0b0700c40b001c0d40d4402d034049014884aa030030350b401c07240e0001c0c0c80c3d80c080308024901d0810600340300704000310401011100424000700c0603880c048a02941302c42c02240300310401107446183c2030900c0802c540c4903800c104000c2c5800841141581518410641002d02189000c83c0d184241c000791000d401012052203a000400d03484240b0704280030f100b00c4170004a2440195a40c00010403607810325a56108501b01d5464036040741004080344800d0310704 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 467097580 1250 467096330 467096341
    0x302122e0e0102041805061507110a1e0e10141e0310020409140702060f060f121501120327030b010b2113140f0a0b01083007021503 58
    0x50000000408005905182c0410b4088c246043c8200441d510f42203418901091600c5501c40c04240804c1507810030683ca40000308081030041408031000144d02c00c045c440d140110a44120b400541100048100c4190401c20110380c00b800301d280d40030950b00d01403440240425246510f040c810025054000d00c245031450055941c01042601c2103c44208143c0380400030090080b18200e40c8a009a0310000110704620340b8112402c0c2c0c0700a0081484080714210300100f181c0100003034000c04198850b4000c000040d00e0343c01e000740904810000981b84000546000701801e4402d042050781403522111201c01012081350103000d0764201c030b2081c10b60750351000c2c201603507807010504050780c26519000412007211005c4441c00b511b022002c000b01c0710840d403515412440104850900d600c200c0344400044902441030f041614040c0759040f20f250314140d103940c28512403408040d42084004c0041140c40c203601078440001c1c22100d11985c0b1394800d48045081c0742c0c0051000000c42602004118 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 467098830 1250 467097580 467097599
    0x1020c0a0507060305010f060c14030c0312010e091510151e0c11040c1707030e15011802032703090a0609080606060a050d0e0105010302122e0e010204 66
    0x9205032280c0c00310356401d95540012800c440b003e009070700b01c011f0b401000f00030091140f1201c06030705004075900310306007400195061455101004a90301c640000c6609100701d07844d5440d0034010440c0f2860303607005281c20000952141140c0e6900c280012070407022640c040b410031680700103004403100110065000e5035000c0c1482d81481c580100c4200c040103400d80180c8201c5040d60f1071075028000810036001c5100b04000307000c01500c40d404008036081e010103e401a0703846180103102c151000141c5600c800452800c09100e070b08200994450b00d030042119200c000b400c2007007403030200801038807a00d810000901d440e08007031007110300d00a403200e0059404000b00c000c0500d90012200c0d4441c5c20344d514030035188184a44a02070441d0410000030766141000b500508003810b05103000c1e131500054a031a130044480060500c601e0b40c0d500c0c0c0041c0110704216000894400380708009005000711203001032845282076002e40c9808100c04a045188240d5800c1801000503480080d902c6a0329840c450 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 467100080 1250 467098830 467098843
    0xf03030103020a080d080106030c2601081c08060f120f0607030c030c0c0209090a14030301080c060705030336061b0a08010614040902030a090212190f02040e01020c 72
    0x10b80c03141d20800350014070403000007030903000c40889880d140920380c6010300c260001c02075039220030b0034040081d0559001010540c512180700344001c401100c0c550401007030a1a000c10520100c411140c1e00604800d8030f078004001d15404079080f03481e078a68064004c08208000a13802d0810020301c0b85060300f120352940415500e1140f585540c082000c80818030027142031314040d160000100d409040c0303000250500705a6203038040c0e103050803110510001da44001a035400c02102c046290170200041c000789201340314030b000b6407604440c414149038458450035101d1101800551036000038031140b2208006682448420081d58030b041003043c00e00c00b4600340c0300d550072151a00a04000d0b00100c07c2041c180080d16482000c55032804c095038204141a50864055090210441414000011074501a0008620843d500440469140c0940c07040c04041c000e44810b10840ea00400b10721100b5480c3e280e0350407601340d00002018006480f5002080c010400030a0002c3c203540006040b0f01c0c08440001c08 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 467101330 1250 467100080 467100083
    0xf090303090d0f0b06010e01050a11070f060c050d03050f130c05061602150301031a070c060c0908100b060d0b010c1b051f0f0e03010216030f0e03010603080a18080f03030103 76
    0x90304c0c890392503034011561303200b848200c1808500103000a80c107241c803500980020684560855001c643c541c0d100540010103603104c400000c4085030135404100b000d0140151160381800c0910135410003500c0848005001440c6001d000080040c2c901400001c011030740060002401e4290345110520401403900410a400e0380201108411441c8040140044034102d03500851a0280d00140010400780c1800143c0407600300401d654550000c61402d206034082c0c00c0e042c1c1c641c5258a454080b4081c2411281c10791102c0181c541340080da80707a200c000c11107032035825211000a20300b851600507174014038410030280c500710041c0348103d0078031030800000080d55411030f000c024014003001c2013031449200803141d00c00030700c40c6504603240a00480d10076446241c01400541010340300b83d45a81c282012050030750000303404021044505801c501c440c0300b20a0f080d40241300f03840c11910741401501c60344148034200b19109210245079111130700c0c1c00026114410554004208400000b55650020b000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 467102580 1250 467101330 467101343
    0x120a181a10050a140405090a0507081c0503190509010f0f06051f0e190905040b1609030305180616030228051e122a010507050f090303090d0f 62
    0x40100b954580030012030104d842c2c0c1040040c00d1020300b41404090040500382c2c0741180b149042102c000360091001101900c4060002c21034501200808200c5440c00c002a00c1030050400502130402c0612402c50f2841000300d8001c41c00780c642840260040000700c0318074049625003890080028550f41000d02250720403100282250300390590386107050b6413000d0303800100d17012180b9456541401000300a01d010304803845c0d0a2550748d420802c0a4030000c54003142d0100181d020440c641c9104124240c0400003840d21140076801d59070b002d89036100d01e401502030744420909014560740c803c021a104400c0c046039413100c4010342d180182d51007580c021884d404000d10300d80540130340341c004128a0b41070340090062801820300d00302a01c0501484802c010a80030b4290452059481c40c1c00a0000420f01360213a203910703030070300500c41d1340c0185542c4549469042c10309001040b135101c02681c48042072462080d40e1000307181c0010b40b4603c214050941c11003207590300c40003800340b4860043c521501446 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 467103830 1250 467102580 467102611
    0x305061f23041806092d0b011b031e0203041d1f0b13050402120c030702012705060603011a01050f0c2e060302031f06121101110102120a181a 62
    0x540d03001c00f5030b41d50402086c10740718226521892403040d0032042c03007a030041c10045403249491000d103200c0c0c03016850030b81c0804c0d6982212601e881000c28011000072440c405941403030308140500c034030300c550101c2c0ca00c2011141c0001c04d1a1040041048082c4001e900c1105003c581d2900c1460b80c80d0020001002107151409000409050500807228a01c612010b40c4a0a80ea00300507a140ca0300040c0c401c100315982d41c2c4680d01000440a0b0800e0440141480d55181c81d507903280c0300f490500000c08641c0241d05240036282312010000045001250908155840711100a900122801a208041c520b44900a040680e4811140c101114540784183d00542c0f0784014100109a51444c80300035016404402608040700203940211103080b485400070590715540c8030a070380e0344008182c080d1592241d04a039030810390f0700007116031703c142207100c002c0d420b042c5100c40000c4603410081c8240ea6030798641c01e80a01d140c0c0381c6800000c00702c0d4000102002c10101e250551f5941c481120300c84e4441c41c015 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 467105080 1250 467103830 467103851
    0xe01060e070c0c090e030904052d01140409020f010c0203030706060b0a0f1805090723030105011b170a0c1506090f0b030303041119060305061f2304180609 68
    0x1d000c1c50051724007200045290800d140b084c44000d2000601100b021010120441e1521224803e8040304500360030700628154100f88545d040004640010762080789000c190f100162910b812041c8008401d0030b01c0100740c80740d400402d0a5104091000701021310345500400d9140b02c0c080030384024600ca0380d403900d407104160820341d110b6844490107a5541d010f68401c000c42c0c540f010790650301074040d16050b016100294280c0103100007800310b071a20040b0200c014042d5590000521401e08903c0403101100d21081c0c860b884080c09115144483c100b00040f4110128003c0c3e02c01040c143c4e100c0d8016413001f500d9410f6100800d000c0c00b913000281e0400c0801c0041c44040d0041860001000700a1072030742d21241c0d228082c80d60745445040c0c210342c07020304102400c0b2801c10008020724080d103020070f851400804100500b100038464000c3d00c204600b43e070502c244c5c40108809100d030506250044041c2410003450300b03004607803244034020503040c0602c1010f009508101c0840d000340f101402101e521 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 467106330 1250 467105080 467105099
    0xa05010506070222110c03070b1e19021209150109020f0406080604060e010e19020307090b09120d0c05010e0c0d02061309050106050301170604080d0e01060e070c0c 72
    0x145040a903004002021107010070340030030140035813000b07644000039403c4541049951650070100c21809250000308942d000d00a522a0b62075200e001000c1c16040401c40504001c00c00360064104120f281880c030b821403618505504507020300c50002c029440c14a804441540e540034880c4985000a03045c1000290710349040c000c3d00d480145e0200ca02c1d04080c20080103c600041c01000a5032245c1c60340301c002270161079083c4250280c114400341410324034203011450071100c0c0c2008444c00c120310400c1004102c03944031000e04103442014902c140c0c0d4080c0301d000141d030080e40102420090154121380c0006941000303c0400c5d05101c1c3c0000c2c800b50030161055038031031940d40606a04120014082c00040c50080e0080c0f049074041c04c000c0d03d4040d1180846c0b001c0380d0b0260424404648008010302a05100ca10003810901d1401c0081041d460280d03109070203406145030b201e4441e52610021203d403002034003e1030240143c000010b40528007284002e145045102c6c055401c0701e4201c8000c0fa000d0f61 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 467107580 1250 467106330 467106337
    0x812040f0201121a1e300307260d0c0305090d0504050901031112010c0503072d080910020f0a0f0c030c0b07121a120102070308190b12060a05010506 65
    0xc4030100515101d080180030b000c0c8081ca4a102ca041c00141c100c5c0600ea031002c0c13a0340d0038007502460541c0319070404008045c07062070802d032401150740107016070740c00596059106040f52890718942d015407000340d802400309020b40340c40140364504001081502540c1544454401c0b25620100d03818910004015521445036000e46500089880018270109100d140119190311011f040740f035001d0102c0d288142150724144454000440010034007129640c44010006401d507101007458039440e0168a4402e0504002d10080921008030700107140800184000d01c10580204010355540c11030190200c51036008540c072401203184c800080d0741c0c2c1841501007080700c1d649070700e801c09042c41d01e480302016154001c20078000c0010292881104460f64060140074041c8200d14201c1d0a00d04010040720a00910324941580c0c4144090300c0825070242100d0307004103400304007003c0d14004041401c050070060409075000501c1880303010850302c1c000303055440f558000c10100010398840d01048036a10 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 467108830 1250 467107580 467107601
    0x90c0402040f09180507060e01080c041410021f0609380301022b0c0503070917070905070903060e01090f1217011508010504020a050a05070812040f020112 68
    0x80342d503805025008042d8019904001000000350040910341e540034501030042e00480d0015220000109103541c0081c40603800c08031159100342007a040c111b404079402484600288101455407101044034003e1042c0c464030003041e40c0100068500758070030f030060022441070310010741c640507a1013646143d03a880c011451000e10380034512031a031403202408609040c116154155070810001d280381204040301000f016003022001da10700300422440c07084030581d101d645d050050030010060074030b40c000790305001d44000c00c2d102d0181000d440c0e0154609185071308102c00036031605090040998109503210b00b1603118030814007264030001c280c24280e17815414000c040c0e102081e03000700042d034031242d820035800d101e18103210950110304501b130f038100302a172280380708215007401c1000541c2e11020260241030140c03130a40c600902c00da402881441840350303c1e070030044085501e900300000d071800c881540042c090040224101130a00721400400c15030100d000ca0510a403080c082c0905004581625 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 467110080 1250 467108830 467108849
    0xa0b040e0a06050906011404150906020c03010e07152616030e07331d04180201140c01020703120e0d0801051003090503030901151a030a0b0d080c06090c040204 70
    0x42d05e900005403070361a0030072505940e108050002180a00308000888884881c640d902e5101da0310b0a100070703003001078120180e8000e03410726070745a50103900090b1800c2140e100c40020b581070845820300701c0b001e421540405001c01200d42840c4105c0c842c044007903024200d100c0c500b02c45044540c0041d01181c1454000c044e00d0b402c68102081804040071920b004e03400545a090528035800e6062142d400b140441600070072230391160031a50f81105c0a109072064030948041040070240c504c1f25070a030498440003410000c0c1383c100e52121620000640d8000c102540003952540700c40d15014041540b008052902c0d24607022800f0701c07041002844000b0350f0942d03116070502c0e90802c4280030b0b540603030600d442d00307050303c5050410018004100552040a80500000e0f000c6806054119808816840320b0300108408135aa00c1a030f00c2001140d4105009200c005900c122030408611161211700700541201800b04e10719072501c1011803140e214201c1d080070703503001560400400c8101d005034003a07011007 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 467111330 1250 467110080 467110099
    0x3021608060708040201030e0f16080109030c060b18010b0304030206070801050d030e030f0d05070204050907081b04090f050a03080603010606050d0906060f0f090540020a0b040e0a0605 81
    0x40b901401c2e0b5280c1050041c5008640c900ca441c0e810f514008040554250641c42001142070451844010001400042c1d00912028401e80c800809145c10988083c00e210703a6040b201e211507490012500c8290044082201c0303540e036400c1c1d0301603203400468094002d8001d05c400100b80c05c0c402c0c00c0301170588100400d050b01085a5841c115201c1740324401240d054410b41c10003591054041011004103502981c6082e50b410f810f1040c4800c0e41d0000c3c1c0141c4181c0e00111013800940f40100d4850000700d0224601c0c0d0070b88560400160180400b000080d111610200030300041c0800450340e600054042e449041094840406040c22103441c0d00ca0280040d60134464800d51311011f8200c0008640509000b1032004d03120494800c44c01e9255100c900e1000c1005410044002c8901905900c006000701354869901c11000540011000b05c8855941c5c2c00a0701c0700121070034006070a0300700940c0250680d80816143c00302c014482e409405001c0d1580f20400000b80003a515000300c200f601d8000c0c200b10003 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 467112580 1250 467111330 467111341
    0x10810050c160b060a030c0b1c02030f01050909070b0a080f1302060a0c0c0905010803040f0e0c07150f0c0302042d090b120307050105060901170705060a2a0302160806 73
    0x181080044c00b031942c000c0c215107001020483c8164044003500d40c480300705540740c11002100a40e031a480115a0701c150052040041c0a0b00071111941140c2041daaa901c1941d50b03429100d05040507500001540b103404994840c20340d0340030400d18400d00d60310204400c02c1d05c5040b101c0390400310042c8005c0d48151708010383c2225611810310100558400c140c0c060312035807210070b0041551426041004954000f00c0c0800001018500e000001d2102a0108541342001c0034031789028420320801424803d12a0071040c0c91040a9010001c4040480410860140d081310010080d45c01881151007105090598622800e03c5084810072001c8200d040031400c1c0c41e22007128090261140101c0d409482440034011103003003440181500741c0b0410001829240240030004522010303007000040203600100050800800240002a64012507404d07888004e12001120100c00814040010741c00c800c0c8181d000882d501013106003035200341c080d100e0708440c2c1050211070880038401c2d100d66a0152001c42d8 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 467113830 1250 467112580 467112593
    0x1f1d0105130513080c0703140c09240402090f0d111203121f1e031a090d0c0c0b040e06030d031503030f12090305130f08070b03060414010810050c16 65
    0x9140c0c170000041e214116600c2d2682030800303031490300040b40381d04405a6040f507403601a402681c81144c01080c003210200c400482c84035034031082101c40c003840d40010007042c9641ea1b0704620340d40742c00040109001141c245003146000c441640c03600c0c02a03001801c034800840d0f001c015160350700403caa2044603a0348814500e40c130b0b00c0d0700e4aa40741901349030740030100d0050b07070482d0340e0500400c1d20b162001141e0300d54500810140a021048400042c48005100080d100405c008940e50180d26108085030301906002440c2c900603804034200110000b40003400075144c1c0743c5c1d5880b0320411815100e60301441c11054040da503541c0d0b850306510520300001d000084c0907103a0010991150725044100003103103100001281c0c001c980540100300080b0b4900503100251000700017800f412007160303590f00d107401c102e55980c4000b4001c000e4000c4010000420036103440c1d06c5485002030544100009503500c0e2841e0761103c0d0144152140a41400c0002c0c0811400600301d41c0c0032444030b170b205900e5002c6ca458a0 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 467115080 1250 467113830 467113837
    0x1e0f070206070804091112010905010e01030f050c10030b030c090408040e07031e0203060906010908030a11030c16150c0c09050606070204051612141f1d010513051308 73
    0x12a080f070750502c030225801c10316205004154407509072080d41d8504441d0400f08540c0141d011498050401e030040c014200c01407034181c11280e11044480b03510360341c2c0c540706040900303d5454a8200c41c1c281240781c041507050300b140f5880c80e01642910000c04404081c4000c0f1507040350043e104407400c000801030480c441c50920b46c811100c1c07400156200d0b89145032240c0c901d000c21080c000d01e4001c000c0c4200740c5171010006802c402e090a060885903c1c11000a03100e000e100b01c00b0b03050000b50340e03200301c01c1d16060045400101044050720326404d031075849961200124001d45100a03d88082c1d980414000e03480c0098007900320b405074421900d003420403400382c20001c022681110041c444c200c0140c881d401854050400200308000ca0800180000c0a940501105040190410600d80d1914400c00d443c0c0e9001000d8203a001d40d4050054000c81c0c2c0345038a0381c8444502980e000d200e0180c41c0c5040b0007941a80e10403102162005442855501541d00950302400d501400258240001e08400011b = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 467116330 1250 467115080 467115083
    0x21e040e0309090c0a02070b1c06050d051216240e03030118023009010506010c081e1209070509070302090f012012030a0c02071d090a060f021e0f07020607 68
    0x1102c0170103494071048c110316017050b80d80b041d0008005442140383d141c54011040074100a0b02c091199030140d84030203035a80700500e01002503038000600b40c0514005a4292540d240d000b0075000784c00302880d500e010600701c4000218100030b01d0701342000b83c07201d40441224100c4080790407403410b284146100c44000d40c0405000030b1a00a900301b00c1450311202c0d0081c5d141403d0f921880c125070720305041d4a41c00e40b0710060401d810040c031048240c00081c60f203c1030724564801800c80e01c4080c00c50250311407040c41400014a820040c41080000c41da00014a01c419140d00741c40c0144191240300e42135059000d1112495400709034206846995489184001c01080c100f1050080d028010301400d0f06000d04040d07480744410b0300101300240e0554038007914000d11114401051039518003c808910072261034851a904008200428503168080001100064002008004000c980060031000303510409820746116166079220075561041c400343c035a4101030760b01d401e1034140c0c0c030703801c200e000c0c5d005110 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 467117580 1250 467116330 467116333
    0x105040c090509100f0902092a030903090301090804080f0a08030a0f091205070204060b0910050c010e0d0903030f030c050f0714010e06061302040828021e040e0309090c0a02 76
    0x1d9080c1c2c4c0c41a01826078840305001001610850600500c030421000404a4000348180da14441c0d251107455250310001c0361000d001a00c0c0d0311449034090130351064966880c1e056090003d0740c2c041c0001d000040040b103c09900322100c003800c0d0030129885844101010b0910743c400c1c0700141e40c00c22560010b001650701c5040014042e051a0391b5180c010307241c00c1c0e0800000d08089040011405e2512481c4050310b0304114040c02c0c016103400050340b50451191900c10000c01142c08980d240c0e09400410cc80e0041034181d074001c0d013880400400c0001c0c62303c002e60018017007054441116000e403003802400c2c4d0032503076002e03e400301903044003405501005040b1030a08074400001100c180a104030558405100e000d4500344c2020010050301900d4034001c41c89180c41003004026030080002c0c0000c55030010f61440401500040c9003c0000301c1c0b10201035040841c031030503035041090030725103070868000460342004040d2110750320390f59074065440380680207030301c0783d0200d01e004035000c01804901c200d910 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 467118830 1250 467117580 467117593
    0x2113021c05101505090103120c0201022a10172205030c060702070b0f0909100e13050105150f240f0d060e0412120e010c050c0c030105040c090509 64
    0x79191807400070010110540c10ba5101c20b032074150300c088041d03240200004c0320b51058a5040d81c40e4440003a4105440000303028031110790000b1a4002d02081e5031001c0482e9114500e05001280300c502844030402040c0f20300144480150258090150030210034560074140c0e0031a038401c0b52010b0300110510711481e41c8030301d0f8028800014810030040003040046009040581011000a45031038116040401c1d00c400600250101002c0315090b00c00d14001100c2040c80d544a48100803220a41a0000c0488500d440200302940c4c0c060315211000510500003007105541721a0300f602826441540164070542c010a469041d1800ca01001d42da010316a9241b02c2d40d088400304210154007070791110070400310104003c000051180300311401091110340010b4640b80ca55549509058501c00000a001a20f07105166546c007650080c500224450700802034a400450060026040423464441c648034440c07801c1b07282c3c03c040c0074070781c000c690190380c50202605001e1860f02500d0010950794541c4200c1c0d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 467120080 1250 467118830 467118833
    0x14060709061e0e060a092105030304080d06091103060312090319060e0304080a0510090803011707050306130b0a020c15150405040f03030510061407020303090301112113021c 76
    0x41d000781905e0202e03803140c1e0324407460302c400341401d441c1000344001035010711140200442d9020048035405540007050a42d6060602d59140081c00590003603440280362803982d0100ca14540b0040d4002c000440440d400050300c40444180c600c1023003c104d4058104d21031409184c07102c40c9009410b644100c00108550726423400c8240f0b15041540300110035400b01648605000d006e0201e481c03043c0070350f5000d001c8402192a003400d148018814071000c0e40c4140b407001505a01802a40d01030000103090710743c03505120207003400d48000300e04103803140c1c403a07540862400384a5100f220980c100d041d0107800f198907020080c01980100070845203400c45003200f080741e141c2d914468103204510600c92480f50340e02030b05000301103d90081c040c003440d0b088000248403654001050b1220355590200300c1f903507400f00f480403178190302401d0398044d05507003003011440000021101814800c0c4445400c40c0c135250002030610164101642d00a21000300801006c0150030a015020600b02c1100b10b880006200b6 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 467121330 1250 467120080 467120089
    0x1061106061521130b01151b110415050f010908120a09080d09060e180f090a0b0c0702040e160b09040216061e0603110d110a0314060709061e0e 63
    0x8555400d030501295203c44104103039001c04034094050080c07015030b0122107c001501c12040a20003440046c170200042d420480540030340905c0110141044c80001c85144100c10094401c6c043c261249103240100c2641d94400c0e00c1c00c00496940c04002c02c140900341d0b05c9880c0a5001c8601d00003040824500030814140c100885801c540c0c0c260340d03c0b060907180a900800001341071202920543c6a1211295103003201058250400f00c1c00300c400089850ba400018540441c3c440001e00000c015010854540d94203806400c000d030003a2400d011300081a0281e6844a962848981c0e00c10103144051024050200c01f0f0100d0040c00741c030040c40c10640d5000c61014016500044903440d0710741c0d2081c4400d18460040c40ea010580150074003180e810341d82c40d01e6000150448207800f5100032401703882400300340185080005805041c110800b5103034103040d4042031000030407503181d1150202041c140c070b205075603000c2115000d6840c04014100c02d40481031000f54288090108640d403c50100c6c9a80c5d07 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 467122580 1250 467121330 467121397
    0x120c3003131805040210120b18090601120b01090c05040308031338040204090c0e0a110f090d03090f0b12100302030d05030711070e010611060615 64
    0x700c03281140405282480105030061520801c4907858100380501005072900800710750014590b05100c4140e400c0840381c1c4c0010400d184841c1e920180841c541c0203034900890380c450007841640b040d240030380e03210300340350000b10b0780500000c2c41041c0410040007580015030000c503200c04c10385001d52900c1d40e2a2102c1c10190019600403500c1104d05140004016109203d034560102c907054150f03c1c07046031140343da111140300c8821041c4440201c0018119503035588808a660b51000410b100c03144c603100440b6001301e0031124106860325000d2042000300c4402d007607504004c0d801e0038080c50304410f0f509000744804120011014401060404504113000c401070b10040c0c5044400da13601c503030301c520303600d8504207018180f00040b0004440c00d10158401062040000d8000c3c20650707644d46465204807020803c401d80011079005042c0f001c1220034105201c2c41c1250b14036503030005080401d00b102030301ea01e01500c03070603801210809104100400d000c0a00518141880015000803d515202d400d010 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 467123830 1250 467122580 467122597
    0x201021e070b070311100905070902070204060e01151115061c0c090e1002040305031e04180207020f040c1e0210020304110108010609062a0f060902120c3003 69
    0x8140408182694070204203e810005446c0b00c280100749490700d03140c0d110181805030104050b000a03040056442e5500300b1001000c142041c66903039a03403450418400c60804040303030000794914170110b8410b00005451800c0c0d07104142d41c02c03407c4c1c98040800025200820440c41c0014503440c0e5a804030301c001003c80000e116801d0045200140c1540c500d0505941407403c80c006403041c00240089a00001524020075a400880c5034540202c03a80000078019584158800041034001d2000200240c000d0810301d03109036240129181070904001c00e40b110f44142c28002900d10070a4241c0460b502c0020f200900d59005840f00f4840e04485802603034800c54054410762841e511003030842d640050401d00410701d500d4400701c2142070400083c154400900309400404041240914610214659a44661344040341c07051812071464240042c180c50300e400c0e8881d05205480541c00440860300c0c00c4158401007209200440300241a4041d000c444a442c1005080b810100c0780001e0400c010181175 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 467125080 1250 467123830 467123837
    0x10c0f020f0318040c1407030c060f09081c06120c050a0605032401120623040c0c03030504112206270209032a0307120201021e070b0703 60
    0x105488080a40780462201003119598000c12140303103014040c140c0104112022100415054100d1504488940c03000400b51215034002455500705038115003c445060f05c280402d00617511088801400c982c130144018100110030003000c074800b4090035907291600e40b60880050b0791070316098540803411045c0400c49009100e49400d01c124903010102c10000c000c0d03031074442c3c6540360140d41c900300d26940380803450b1146040c0441068503805100070111842c034445080043c207580b034803081301c61103c1001002d507000c4491401c40040c20b15015000f0403848075262080301031b400d5507046005203001807040c2c40040d40055040c1850791046d407051084a42004544a040458034100c0304848182e07000c40e8904c16003200d0141182010884100540c503a44401078881c00312001090a1030785245034244d4088200030200c55141d04e044078140c0040040e0100c81c4416100d101200c80c981810a000e80581d120920b02032500e0070004610480ca0644025144019500d0342d0200c615007003804101c021 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 467126330 1250 467125080 467125097
    0x30603080c0d170402030d0f091a04060f0c022101021b1e010608070b0307110a05070801060e0c0409150e040f0b15150f04120c031a15010e12010c 64
    0x11070f83c1c0481c0c049401c0358a071080440e1404d0560000f545c9080c8000c1400c14003e407803d44502d903c0c090041c01c40203240f17030090b000c2d0484c200050380d501e550140c0035100220b40003e00404031a480740d04088560b9501600c084101da0f0078100c07120f5000f40d00342c81c215081d902086024041c2540c0d44001030201200802082e40855000e0205800142d1800d0085181e00d440c100300400ea40004820003102d0f00c55821641da0784441d0801c07107042000c01d802d00600d2080078880c3e01001400101c100c12610404000c200d82903c80c00003090041c0150780d400c0400e0700c10b0205020340c516981c4400d1a984041020441c2c47c1d03a038161058035180111801c0e18003540194000d028000700e43e0800d83d00058480280c0c0c0d000c4540c5000940108100801051000002c6082c500d040d10b48000c6a000d0111010008a42006403030840d40300e0003a404111841c144494042000a17044140329002d68080c50406801c4020a0011a421540000300d41d03400b02043c42161f03004042846114140d14440d070300c0010 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 467127580 1250 467126330 467126353
    0x6080109020916020a110103060e0411100302040e150d1a0921120601090b0714120403050a080d060909050a14030a17040f0b070207090b06070f12030603080c 69
    0x1414a001041e0403015000240b0f4100c1055011541e200303115401301040703031984e1168004800904490308128440341c0020148414172580622402d110700b400c03580c1051042c1c040c90308405900640c0300340c00c069040c4502203460804411030300d450310b8038090114031030f81c41e003030303c2d41c9151410b0780f800303000c41d45032100a0024203d0300740400b0400341845540d854a0b5101414616403e00c0790b4440690209210303404243c83e6071003400d18000404044100c29103d050030300b80001071000810450002e80f050444014001102105440031a9081009440141d1070303500c030094554031138001507042650780d640200b00d220951081d08032140c0900d00414080985180030142101090442036242d8824008080d4070766200c1c0c0e00d4050303c1c0b0010140119a01e0b189012020904e0107600100000444010040d603213078001400070880b411a01d041c01112030107814403049114591020f0403800b00c040284002c1154588808841105860001511035480c1c8456145802c0350b110b51b400c0350054440d004 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 467128830 1250 467127580 467127589
    0xd080703061a04090506040f1a011d1c03020f0307080a081302090105040e07150f1b050715020c0d0303050105040b0604080606010e1c030e102313090608010902 70
    0x1c01030301a24114500c07503031210351481254042c1c3d1040704461500c4000041e80350320f894020745a801182041448a90301d42c400c020522500007a0581c00520710381d10b4500c0300030103014031001058014004005180e2118680e9284846d190400d8056114500e0629140c400400041240798040c05440e43ca80c0721400004008041c06030031516102e80c038101c4c02000da40d9142907541181d034120350020745620044180d40c03c102503980681d07041858410125816600300e000310381d001d6410b40d41e15880c1c0a21090005003500c560320041c2c132541c0200014000b80c0302d0300c1410311440c4994012950701115110000e1100700303007103c0450000f920f0f00010440d80c146801108920403044400900305810440601e685080080c80c0c1410820340036106202ca8a03030140315140000c4007021003001d2605400c01803e140c1070703020307905c0c00340c6010b43c94610b80354800d410004824500c40c0000d08a072043c0c9081c11065008140031000e02e204a44000034812014440c0c01c004007189400820101054010003 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 467130080 1250 467128830 467128841
    0x80105090109050702060a1a061206040c050406020c010c02011e021011160b0705040506070501140f09060601112e05090c010903031b02120c12030c07030816050d080703 74
    0x401d04500f42000d1210f03d54010031703500d901890300000000c84050f800900d03004014803500d580d410110006841c04500314444000e1301c13441d4165814024445020341c11500d0344200d00c2200c00603000482010b41c07a44c4a9510303194028014503080c00d00200c00c084040c241403081a031040561710000c1948007010705402040b800e00b40c0480501d08010500407a100c10545c8604024210082e0100007404240a082a18050032000d44030b6170700d800c81e1b40f50903402030400d8165482d2040140c40012502c90300c00c62013512541556001e808640c0b10341d0010356100c100c001250500c0e001c0c691424810340c01c542006400c064020b0204040714000c00c00b61403c40720094125039270f07500203030707407518140c0d80080d10001200d41c1440d00340c15207000c0038004602c2e500d541c80c009520500505003010300b80d0001550030501d2400f2541041507282a100c155500d101d011110b07411908490010408034070701078040d040d5150a500d0118110800e560381904080101035103801162440d418009040d0341403184 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 467131330 1250 467130080 467130089
    0xc0a02010f1809020c0f0105010b13090b060d180b070c261c090237051c030309060513031106280b031005190b06031308190801050901 59
    0xb64000318428080040200301c1c500803014960340028503d00007410400400c80020300b420020016561642103105c0c140e03002c2e140f501a94195400c000c1510b010512504216200050515161034182c415040142414000d10060001e6009602012803d218081c1c1c0c483e58203039503034103081324080c600400c0c11450440b28000514080b003101d00d10b149504225083c601440e2086540c034184000504090320400c0002034100c010800c818154440281c20f850f1242e04595188100c0f20040484114108a620549521801e80c0c0101d140101c4600403402e4442d01a00d004160031203e500c2d60020340b01e040d243c203441c4441c052561424180c4c480e00c001440302c0083c018000c8c0341000c1054035040300d8644501400103003003c886911002e044d611000d0700b41c0010b8150f0324500f03c4440300e00010a0f08988a005000980000da0282001c0d40303c0c2c0303e9240f9004140d5415501c462841c10302d4417610034000c680e030ba0340c10014907035034907000326001031002c1242d0f45000c01c3c0c1d8141400e010f000311040c1d20 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 467132580 1250 467131330 467131337
    0x190311030d0503060f04021e0712171003060b060f03040809010801080312010306051e070801060801152f07030507081027080d060f15080603060106050d060302060c0a02010f 76
    0x60095a0342c0781c90817441c801908580240c2c0b41e5103650b80020040c1c010504200d0001000034008003002000003c542c00d41c1613503100e400d02102c1c9030003419101e280803681121104600e80c81400040c5495018890552024000034140406e41000711016031040d2400c3e64680401b190140240d03034440c049a01411025020f1030074086022105601128180002000c07541c41d0400210181070141088084901c0782000400c681800c0c440500403100c2800b1b0400014100710010445d0038504c04d210f014545169034043d1a0081c100381c0e00d0511031240714200c02c000040c0c0c0f185e43c0c1440100103141c0550f0003800505401490a40303000e00c2c11025010507100340b801c0c040f0340103130703404000b1018403208007080d02002da041051402c071010388944502c00f1921803a00501042152143c95a401034810056484050181001c0709459500c02118880c0d49940f20900500045124201030701500110040100701c040e225070015206030400c48101103654070980352042075603032040c070820350320b6554103 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 467133830 1250 467132580 467132587
    0x3010e03041d04030507060203071107060e0102030a05030a0e0106240c02060d020a0c120309050c1e10020a08030a021c0e03030c091f02070e010e090a03030902190311030d05 76
    0x2c150300300040d02039a02942c0030b40c111001405040c003a508036100c2070341c40501150f823031502800180c40b04540d40b1915240d4480c49a020500600a603486128018160011800d02e4a012000c40d21544001c0c03401c28a40e1f1078001a4a040c00700740100c80140400418a00716400310507000d001803140000c08500f0031001642240240e00e441084415210342d0820142e600d2403040c0042e00c000e031000c1c40c001d05000420005954040d81640884902c0e0b220340e094070795122000c0d04100001145070021141385803a144915424900300320b12034030103940b50055480303500250310740103c1030b00b040740c040c1c0c1d0003500010390100305045e2201240c002203052104001c41c11864100c1030faa40030052118083c040d0005014000350348100d075406e00c0420104401180c5241c1d000005e40760141403050041291610300027080366202049030324421a4140000c2440c101251011405002110420307078020070f60303000358942d040c13010394101c000c0c3d406034030046a1540d0110516161602c500609410000d092 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 467135080 1250 467133830 467133839
    0xd0507031209020f0405040203150a0e0d050708030703240311010806100c150e070305030d0c091d04080f03090d1812080c070503060a0c03140705031b040902041403010e0304 76
    0x301311034504060140c40001769540c40d440844c2c0303411070303074042e01e4200c2d14050108801103210b50002c01540c00e040c1d05469441c0300740d01054995003e00c68006090120074800030380710700d1203684004001c58103800b11503811018020b107000ca4082070b40054840c56a050591042560845002c2c2c1c0c022100340e4501c0c2c1c2d14420100300a01d03410a1280043c01500e900c0c254003054083c3d80c000b1440d007017000381500e2005e6070324038040d550385c1d21000e80103994904008502c5136480c050080b100c00c61307500c109901251949219851020a8010012a4900d0341803140c0ca00b950094030244d4890355081006200401010030f0240c580172104c0c1500621510a09003400313a4038241c007221941c41d52140c0e01a884031103000c003050400303065070410b40e01446200f0800c007440304640c00c90008282c41c2d460070420034841c4880d40c3e00007c0e00700d9180f00403443c1000400c07440c03000201030510300101841c203241015102d800d204103030781c8154070100c4500c0b200981c0010310302c2c080c803802429030308081c029031405160 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 467136330 1250 467135080 467135089
    0x12040b03060d200307141e01030b0a090f0522060b011209230111090409060b0405131703060a05060a2705090c1317010603020406090905160b0f0a020f0d050703120902 73
    0x2444d20f00c0703100d08104401f00800e902a800c030402d00200200703c0d503e5581c480e50404010540d620760240c05034104000f02c2c292610300d1500079441465820703036811211051701c503480a0b001c00c100f102d04012a1800485c2c941545208404119204450302c20042c0c2e10340e601d0340d00c0d540d0903e10000c50380c0d02d800440c1c807400102200f140c801d10b1003a50080b460040d03500b005001004001e6a1641241c104400c00c03e003803000007000c0035058480c0314940300c103444035402e201050100325140e030740028860006125500d081e80260404000310725140f0100400101d0406c0d10241d249480c440343d80c44517100f40a18034150302050ba1050000d000c46007040c60010440d01591060301c00c142040000301c1c100a0148401c2d080100030f160042c00074003100e80e9448103100140641042500c06d4000d19011103d6040c001028000b269440115141000c040201d91076281d4440c82016080d0302c2000380e05a03188000303000f070b50b80310f070181d4039401e0b1070360401e0034098000b94462206250b20f51501808000507980c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 467137580 1250 467136330 467136349
    0x2041b020c0f0d0501091115040302090109090809030114180a120e030a05010203150f030316030302161e1e081207050c0303040c03120212040b03060d20030714 70
    0x3011180a045400c02e14080b403910620000d024000d9402d1104840c00e0040e00f090401c21420300307842400d4410711005140182d8025800002c0d8885000b0004006010039504542d8a4a000e41d103018a4142150002030842e0720b502110000030000c3da08000e10322180b182c20044c1551584044c282c64199a554002219041c0301d200050007004c80100f401c41c0ca0420060640039031040003150307a402d240251005608100d80418460008603100c0d40e09030401106442c4030f40340008203904003d400356020b82c00b030b400200c0b9020001e0584203543c00441e0002c1c08014448105011041c40304841e401e1070300d0840464500e8041210040040c000003601d25011110108858540b01c0c04584850404030b03071905c1001d031408400d01c0084180000c0c00f040d0564442100e06c510403038400c06815000a03a141c001118030b200b00600284010400e60b01403074000c41c0c2c003403001010380c0d880050903520802c050161120000d03c0c24011b94402800c4e0030100001000341c241c1d41d03c613440403002400000c1e8104c2 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 467138830 1250 467137580 467137603
    0xb100e01090203270106051c030509090613020a050304020f040c140c031e19090506040303031a030d050408060112080307030c020a080a030f240308070f06061202041b02 74
    0x2c0e80000000d0004044100c5000000c034056020000d10100340c00c0346010f026503000b001e03c14440101d00c5001d0384411072244482980c543c5589003017940000c104003140c0d000621481c0c201a00d0b641c01d131320010b11880100001e40752603ca103034480c04c060050001c000c0e100318070140540e01e005210a0727140e4009102c14401407841a419076980c481e1302c0e02505500070880f074800c00c8014100d22020b6144214090095451000a010003410307810004596075510b0341b00d03068212a0421040c00460311a030003c0500318441c04803000d03109401004245858000b060002c001807002c02c0903c05140180419401403c481440c2141d006032030f04e0340d001603c000303041703002031658562480d044d0764024000c11005542103005941c80d2900d6070300150141c8444050141044c3c90706c403405d0040021446207658400308650448038850950b51210025480707000d0643d8180d51400358803001450b03500034070024221002d8488c48091191050006484d007504510616450006034100415800508082880d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 467140080 1250 467138830 467138849
    0x7030c08090c0a1208070b0703060302040b03070510230406020d110d050a08060d050a080a020f0f0a0212190f033c2c03070509040c1e09020a0c0b100e01 67
    0x89068031308000b81b131080c004000c0981c80c0c603000f000403041e0154840c0e41200c4c0281c03001d00c52840501c007016240c0e046030145950041c1030303054002a29110354940050300922401410b4442c43c06100425650000d50110005034480d1040c15001d41c1d00c10007003019030802134010000c103009000b000c3d110303000b01d80742c0008100d507082c0000d015646200c50044143d422400740c0399002e005003000f002e5540141c00c00c0c00948500c08282c40030340300000703031421992446030140030b81c912240d0802540705224580c640c0240708003003000d864450f0f54481e12101c107125200030880000c162402500d50100c00c1030000d011070303111583d1101d150303c1d6039004030003064801e0400c007403039000c200695040800038003610660f6100704e5500c0d0b1401030142010500d000c101c0482c1d90140d0796804002051400b150010111a50590104010308140201064041d500840ca407910751b00c0d0241e50040380c012141c0c2e000000c0d854186030080c03141c141d02e4603400c200407442c1c0d0000e06040c8144411240300c10301c10720190 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 467141330 1250 467140080 467140109
    0x825120204141603050c0a090b1b150402030709020405011b1e0b04060b0d0816050703240b0420090310021201090b0315130507030b07030c08090c0a 65
    0x2155030395804240901100b003008440b5042542000850400081d60007021900d03001c04901307418031310b4003990703000d190980d04c84e0686818942001c215130015a108107030b1045404001c180f0920a10500c10410301804041e00d013450305004041c82d0804545c02040541c0c410401802542d9214400c52810ba4a14881010a4015240c403400120f038449454010400c804103506c2003260b44910036004a0241400340161f26610007048407502078904000c19505040210007000795004070040086409582542c641c0790740c0381c0b43e2100c804114910101110303061a4005221017030341c0300d441100c80c0c0503581080642c00503e00060f143c20b41d0056400d003400c0c0450304001c9554200404e14005044100c299126941005205c1d01c20b42e0a0050341182410a104400c0500340060203c1e466250041d10303100c2912161004100040000c405031201d01813400d02102107844bc10140d4042d0305150340c00600d078848000d005241202c0940005441c0d08138080064959031120480c00c00c1d18101c0748040030 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 467142580 1250 467141330 467141333
    0x70b060d0c0e04140709020d110a08060904050c150304051005090c040905070b0406050901021018020f130c021b01020a0f080a210f2f1b0f0601082512 66
    0x1c41c01c1e0406409542ca105c3c1040114000c00c0a0300507101c1035112141c188840000c0703039001c103031740d000340541600052080c00c00280c41d4a8040000c1e41c00a01400c250f62401d90480003140d41c2209052050800740c0002080c0010000200b1010500c1030213610200030906080703c0081d20f07140350722012407103145c07604000301c01d00c041403210200070052804101e036a00c1d43d82c00c01a0581d04214440c0d03000d401038032078281d05594903005088020b0301440c00850141c40543c05c00c442c081e4a4040e481d0488603401940381074654902c00c01044000c10780040640d800300c2c9824409035680c50b03940754110340040969400041c1031000d04550b03507920240707040c6c98100c901c10807500b40140403000d4491a5011001034040e000d140d100e80c41c0b40c03811404c1440f144a014000500b014010f01e1051a00103401c1b401003a5905440054000009400902c10490590b48807552030f02e1440220040c0640119004200032201080b890010340200003442c200680da44850f0842543c05208030180c00100003840e40 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 467143830 1250 467142580 467142593
    0xc03060e012316020f07060f0c060203040f06050c041d070e18040302071703121906030b0a0614180916030b06031b0a05040902060915070b060d0c0e04 66
    0x3401d0100c209024141182003103401010078100740c4000880750078451a03c05100e2002c100503152444600040c8191440c2540451b0740b0102c030100b20082282c0c44007040f00044450009601550003907900e40d803040030324100001158001392100741c1c0d50408000030480d0b1060450000c542c02c1c400303000345c205652001c0c4140e03540700780e14103020340c0700182c031b1035100c0480d02480b0014080c50281e4200c6074101c0c0c0300c540c021406000b0004040b0140d20074440d42c00c90070000144907604c01c03154054001d10b9014200b580059622a03041100c83c910311004002c00c1c0101803080c00c0c01841c842030703c64450300840c4003040d10155520030300348040c25030300c0000c0c0007488201301101d140080c0e90303100000c882d1340b41090300310010283ca074244a40130719403040e454402d0040d5100308055004000100241c90101040010404e0035400c90f002202440741241c56642c04980208025442010b07030303039810240c5008000744000420341417103600c0101065010509940301c10042d9081090000b04a0300c0d28200300 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 467145080 1250 467143830 467143841
    0x180e0a060e0106121a091f2612030402060702060d0e0a031e0c0b0c0c0a050a0812010b0c0c09040614040c0f17060c07080d0510060e04090c03060e01 65
    0x1e480003255080009850f40d8410001005112000d40070400e0702d14210340614141101070000c1c0e84031810001007802c0103002c54003280050320040040717a000b40e94200d030070200d40c002c00c40b4403420b4681240c0c0710f242e1807007807004544c141200c814a502e50300d06070740000c00a0240038130290180801003142c030b850b103510340d124181c1d4807000c000310358400708186801440b4070030000c403058800754140d0b030034587e8900402038000a20381c0b00e04520055683c04d800f24a290300301c2d46100e4614420550341c003010170424040d10b91158002d1034655905c13413200000010168040c1d00c060680700041052a040240c0490005a5244100c501d0342c0035840c0c0307082c10009040820003a0100849180a0004000000b404030044800d40345007900f855584003e81501001880c2c50381101da041034002410f0f042a5030024060107115a040d91306140001d40514115102105c1007240a02c08038414084c40b42c221401d07000300031080707405102000c0155079519109990744402882d260f01c42da01d44040107001c0d00030 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 467146330 1250 467145080 467145089
    0x140610050c0a1a01051e0f13061806090612050a0803040c050418050d0219110a0b0309010b09160203071212020c1e06131b0e0106031b180e0a06 63
    0x204100d0f0301d2000c0d00c1001d107800e02c1854882c0584d40105070342010090303529140754000030500d00410302c00c0c50901003500c02d07050f0032840b40c6680d031001180b05500d0034410007508035100c00c0017440a0070310303600004980b00354100011540800135081c00003840004c500f180c50381c0c0084a0380d241c1e00c403481c00c1c00c07080e841500b101e9481410800803070301044800301c184003100d01540031120003d401c000f043e600c03180b840c281086042a21400c590214035060f01c4030030078040c0a0b2800c0c002c155226025205c40d0801d84e03101e201d90b5111030542d0828500214050340110701030040d00c100181d00440650303a03211361600109179110741f030500450300e0b0080e40c1e4081217084002c000c0d5509d407c548212a2541801a517a030340c0030f0044500155a01e00005a10740b18840001c0844800c641d0b41e268500220450180303d240844c070000c010030701c1508201f84500828a41e14082045984102e4042060700b4004100c010001c04019451488545d14840d00456201c0c0e01000c40c207480c0c1320781c244007034000340e0030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 467147580 1250 467146330 467146343
    0x30f0a17010b07060f11070b0405030904050c19090b0d0b0301060305011107030201060906120b040f0c03140c0d0b070302090a03020402030115090e0c0406080c0d0c05030703140610050c0a 82
    0x5a0b50405000400c01144200c504000200715841c092049600c90005580b400c88284840000154000c030590340242c054030840c2d041038118000038040c0c0b0030403078a6104480d170100c1d80042040d00b600d18684060010305240708414100324200301b150050500154030581c84200d40b40094600b07510100180d50014001d0003411541c000300340c03155103c108214010340c40c2500c001010000c0344940c0c070a40d102518803515402c2c1d5a1519800c02601400c1a03500e840400b071414002050560380c84011807150079441464850032159070f007000268048940600b07191000030002a0342c0e281003941c8003070103040050f02c030030072807010425042d141d0b00001e40191001001082890b0907151b21080803900d0750b180c54103107845413031855400100b80c4101718541c00520040c04150b002e010219031082030030b00c40c5410004801d40d450182da4054500384040340f000000c2c410010350500a0364014400c4441c01800c50a104001c900c030040e09110701001c100c400302c0c009513200c1d801d0008100d000d4004c00d = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 467148830 1250 467147580 467147627
    0xd1e1d0306040b160309020d0803070212210f060a051e03030f1209031305060307211a0a0302010917070803120915190e01021c0504060605030f030f0a 66
    0x243c00c60505a0070358a0200303072410402d0264000b48640510180c0c50380c080c0600004803042d942e414020341026100300c0541c081e040321201903151000240400441c2940d0b0483c1394101c0c0745600c14540000f414620000384d041082000580711100e41408583c800e6464800050170351032908458085c58414542c940000100718034010769001c003505003079140544407016510b9003100785680c2c0c07161101e1302421441c0004200410300d0a90040c0d5030200300390801c00404c0c035182c5074400404c5660681d05503c1640e4503544144130b4000c001b1000401d00c1940c035114820700356000038008940fa8891206c20900a0380c10740c1d4218414040384004088180c11240c4030380003102c00541c1c051040711599807500c906038820b910a00d000c1d160030b0203a0b0104c000c00000b00001d0000728050240c04004503402c0d9005c218003204260f4140078660013160300440010241010325052044d51100e41c0124840d5201200b202182c0c0d502104403219a028211000d9a40d14480c03410b07140c009520240122094000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 467150080 1250 467148830 467148833
    0x30c0d050d050106171503011b120623090411120a0b06010c030504151106010807060311040305060106080a060306090b012c06011101090b04030306080d1e1d030604 72
    0x4050420030510340400d001d0b0303130788418048a960400251407540c2c1c6419201086007240c0e442c20b02c59011001800204e401d030f85124951102c0d08000d500b100015000302c01c00c411001d6288140d07405006150400c0c482c610a40f501d014000407031030308580c8106144000f040c200048540703080c1c40194040c01d101c81004a503090ba42d1184400c0d5815a076248896002a0988d0b203e01ca4000f4129810b490315414903040030b001d440c21521705609402804090812403c1d20081041114024681d503401000301d1400c210005040d20034101c61980c20340c0d401d00080c070021794082000c5042d10300b94503080c6440d139100034042000e040c891788090051482d1040002c1030091080100307040e500400048200c820001b24125041c040c03842c0c621110742250300c00f24460398407940c41b8101e0440f1070340c0041424003194680da0300d0110709540890100c2e5440d14100103480c000d1080950035401424000c00321441c02107172080c903a0110f802d141c1080705941038002c5031443c45d01180c0c0e601401504640582c9000e = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 467151330 1250 467150080 467150087
    0x10081905010c141e30070509130b01050706050108100b0103021602190306050a0b010e120d1202040801020412060b150409110f0307020c09240904051f0603110a050f0909030c0d 77
    0x81c0f05405c4400341c01100054840e0740510704540112001400b0410704a07480c1d0b40e01002840b81400365410005c041119401003451400f0746400b80c003540000d0024020b240c03400d01e0848810800e19414180140070300188030341500c1c1c00f00741d01d54050b2200d120b00354081069843c29030141d0001894a0b240c58148001d0394841e07403112000c20802e1701c8040d007070041041013007030f005940d02402c03040b544040812156544101e001015101c00c511015041545a210076420390b0895001140c0410302040c0000c10320440b401055112101900d0034401c0c5490351070003041902c100c0c0a5034032501e4482921101425081e02107031401c600724460280c890621a40080d1200c50900d46d252041c1110404a2b128034414114600b19408058841d21900d214401f4000c00000040084d40c0b0f90113004001030000c000e04081140f040e000f0000040d80b83d0a6141202d041501d140354180100303110b010900c250340f0f50301c1e40710031220411210308a195071043c00152a6100c0d204030b120380ca01400d500782c04603940 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 467152580 1250 467151330 467151397
    0x307050303150906130b030c0a0602010b03070509100b0304020102100f02030f010e010503071e03050a0b0403090b090f040b0a050411070213090b0601050310081905010c141e 76
    0x110015410042d0002c01c20401c8100c0e0980f50300e40d000c02c6116400c00e00705882c0e0b100d450503400190035a200c00d10580c0004103803900030b80c00000543d4450f40100704a00d0180100d10103450112008883e504003442c001c80700503d54017981400da02e000000c141968020042a074502d03603001c100384814969200400003a42090340c45c0c25091007044000f040c503100441299050f1100500145602444d281106072050180404801c15403200340c00880800e400388600b00105024000710811802d06140040c1982c2042c0d2144801120511218181d5592070211100060b0210b40105070714200e00300280c2c0320b0070b8503446903074040d20b4410b226a05081c1c0d00044d00c1d03014001c4400107007418601403d141942e00003040100040071981c0061003940c0904040c41d004110100c008041c10b46a81d6020b02d45142040c042e240e542c03c02800004005c004d0048007008a4507140c805d05003980040f4803d15030080c00c03403c51312254405c0c50004140e041c0b00540311011200d40c0c000c0340c2d000104948129852 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 467153830 1250 467152580 467152591
    0x40504080903011b050f0d060e0108011d0c0d14031326070308031b0c07060c140a0b04200301110c150c0f0306040603060510150f0507110406080307050303 68
    0x5080a028030300013036419842c1c0d00c001c4082c1d2202454a1510020341c05070364001d0b0990f09545941c0c010201d099030881401d240a800e6940001070800c42c045040c5231070182c030201e900c0c1c8940c840c2d0090780c1c070360701c85100340c2c1e081030b5201d0301e00032154485090460860242110502011800f08000103050003008218100d01e020342c980e1001510000c0040358070f51805000c081c000d50003c00205021480c0c3e1075800403a088140c0c40305080c070440340c18140c02c211190f80802c0c0000c080909400a20660741d41200b01c0d421440014000c40c44955a82c29120f48000c101404d1084100130032040401048600c2c0a1600001c00800c42d2203607a40080e201904804c492074158840c803144080b40f030b28101c1c5158000c0d00e44104a80c1400c00f1106045ca00e64001400b142d0002e17100e500010004440d4094540643c3d089200c1000035070034420001e10341c0c68100002001c02a4140304401c46035080001c60309140c0c3c10542e0340c000f1480c04000308010b040140d1205650344400116001800380c00b001550144 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 467155080 1250 467153830 467153833
    0xf0902030a030c111e0904030201180602030103020a0902090d03031a0406180606020601081b0301110d020304110103180f1403130609080715030203062101060f050904050319020a02040504080903 85
    0x4908070f000b0303c50081c141541138441502d03500d0304185d540c07510000f0190320074400d00c00440d81c4c50751084041904003a443d401c40e1400d801000500c00c5160800c5480041c0c64821011824041d0700e41c0060394142012344041c05240d50f0f070242c10360f004400c0303813180f040c040d029100780b06103a0380e03040818020b803042454030801440d003103005c12014030129595048540d80b90040003000c0c11a58400507151120320041da01d59690014640500c41510192040244482e001622454036003444031010b51400d01003410149498030085405280b0b903601c4c1c400c0c6400511180a001940c504004005050501c40500384004194941203011911109058560030743e58101d10070382c2c0b150025600d10b0030340900301c820042c808203c10301c01c0c8070750b004d1a803056005024580069010700008122010089030f44440d075141c100503c0400c030b1507044407004001c00c3da02c0b0401c9280c1a12850380313a005d0405546103081c4070310032072107545208108001d0690303001041041181414500915503501010125009 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 467156330 1250 467155080 467155103
    0x8040807170a0201090e07031b080402180f0106110a060603060510150801050d0302031306110d0e0f061617030f010e04020a0902031308040b0304020120100f0902030a030c 75
    0x22000c00720b107030007120764113031108580e0609002c084480f4450003400c2c54101a034034060281080c100110f10085204286c61300d021a0409006122070030101b0312031050449401d206003e54100750700d460714111038035850542c0d400c00501100074101240d041c40a04503a04041d03000c818001c60358806802003100210025000340d0f2020120008884181d100c070206010724010062400c0001c02c003417400d4841e1041d203182400e100d131248014025034100c0d00018804140c1d0402e0b0301010040801000024108401e003c0d0b034110016075601e8550540e1401608041904132040080041860307046034420040d00c0c4c9106844200e8200da08126012206807400000004500c80c201c002e160040740c000d481e90245904083c000d101030361001d000e0941c110f05a0415002080c403840c003030000b4120348242d865480c101800014203070305207102c01001404411905d1101c0c0302000030000b19090b8030744004190f250347c01c140900103040e208000303074050040050308403c01d80d01a02c6d4502e6184160124104d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 467157580 1250 467156330 467156369
    0x906071b050d030207060f0908060709090c020304050f0d140303191d060601031a060c0609010e16030605090a08120604061a18060c0d08190b0604090b040908040807 72
    0xc140300b00310140158021141c1444030501c160b00c00b00006086042110a446e039490324607162110843d8a6400a482150240901c0600d8041da82c031000d551301c01103051505000009200e4800382c0c02d45031255559003044420816012002e05007065030030141c9440389803064400d06240c00c240e0340149100c1c0b900e80303481c81c5240c20b110102c4a0507100f070b00508407540c031040107600510b140c5d80b240900703a140e42c50081c140e5441400030089143d1100c068901400c0c055802d0382542c011840c0035251380c004d8003a480c82042c051103c02d040f40e4004001040503110300e640e290509000100c050441940011200c42c40c90581596038094034081e42c003004001da65000150155840b98820745943c00104500d00700a40415031607003007004010030141c1b5103105007a84030f01d01004010281d010403611410009030618100707400014040004062000450407030004a49108074024441c003507036540d26030704194031680e002e804441e41c0030842c550341310380300d04056503201c0c40b522401844460310b20504d003 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 467158830 1250 467157580 467157589
    0x117010501030809010c050c06030712061d04030c06020f03150f04090b01121a0906041209030c061d1509130b09060909030d0c0c020a05010201020a08010b0f0906071b05 74
    0x207040360b0b00884404d003890400b02c011100d4180c1840c0c180c0f2248100c3c104500b19a80c0d0600a601075034a54075101c0303119403110001030581da059403007038030024900707112901d0386940130000c1c591142d814513240d20311084502d0040001e0103488200315030f0a2000c030070024402503d102d00e600d401011180c0b52072500343c40040209441c0d0710100100a40c01c1c5600405c00c2c01d04d08540c441000e403080b001000c400c00e030741d40101d204080c120760741e01141e84200c080c84240040e10410b50b009094515001c2c035000e05507201c1000d864a94170458003000340407001035891400c100e81c2200b901c140105000d41461601140c413840c0e8000240c042d00c1106500c85918811684e8400c5400301040642000000d0b0303601070030004001d20080c25100c041c002000107100142c1c0a1260700074810300381d2201e406001c030742d00503c10716400ba030b08081d05580c1704010400c0190340100c0035504660300b400341c2c2d581d125107810100075180210340456801c0080801c0110800c5124a10300480b40c1112070000105a91b880810 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 467160080 1250 467158830 467158841
    0x1b06030509032d070206070f020a0b07110f01091d01060806010216050d030302070c120c1409180309040f020c010e01020406080f1512030306010e03070518040c0b03010e011701 77
    0x103c0749000901030054000a0352004054003c0d08003e1504058007a0081070041e802004125100e540030242d12085292620030100a8205011700d1814880c065035864450080901e03030f07030720030b01800d000102a03030310410300300015015040e41c4d2102804415a00d0141540c00e0082c0004150b000300003900c69480000c1040ba44d0188120349080300f0b14101c1400702c2c00d00081e40540401d9020030520f408101110b60480080c003003100c0c1e0b40190240390804410640301c40d0403141d4560a49000b8144698913401410740144c0700c40118840c00d0200c0c0d0b403180c554400d00f41142c1d001810044d000002d00c902d0790240c044149140024420b100110a01e6401c038440c0f401100041040703031000c1496000c0ea25240360384082502c4240e40402000c1d80090015034110903a00c1c0103900010800140e560300419051003002d0a600900400d0308040010300e10901440c6140302500b2800001801d0003e00074a89000340702800003c0d0381c0e56107494603915020803d0050200004205240b0042200144180e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 467161330 1250 467160080 467160097
    0x14010f1e03091407080706020714010905120f011506021b0d03050a141603270504020a03150609051804150e0a210912050a030804030c1b0603050903 65
    0x44490303a1410142900201400002a01c1180200c000425481820000720010b401010020084985040d6000b46824480c1d0090908014803680048159812007031800640c0c8080700c1d9082c85002e181c1a0500d4441c0c008400b140540c00c1604003464900c412004030191180350707081c0c03000a50035020828503003c1040c1281d400201008104c80440e1052015012001503840c0009982c640840320b442680c004a08010016000c05030480825401c100c0c1c01303107000705071900500c011448603a0500c104519100b0a4080ca400056075a03c1505c00e600c155402e89035224420051500c070030005007800a00d000f0a401540708000c0842c1d011810320000e0300c500c0c0d000215240900300d41c0400c5010381907051802d46c10b441004401b00002e268000204400044800b1001d20682c08190050803400243e1240c05820031400c007040103d0000300300740c0145601800e014840b074031680380488070700882000107002e0044000c180c918410001003240c0c2101d800d036400740082d480365580c40c0e84a114440c003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 467162580 1250 467161330 467161367
    0x51b060402092a0301150e0f010e01030c14130302011b050a031805040e060a1a0d08160206040f060e0405070c12200303011a030115030506150414010f 66
    0x741106401c0350060f500c00e10420b190b02465650601d208515800170782005c3c00103031101d044400c1d0554020301c00051404c0880b0020740103412440080c1804c0c049428440c10152100170440005000724140190011060300d181e036100c010002624441000340812400036015003a4034140a62016101e80003d4200000e445416410f03074080e60b07147c503405400740c401901d020002803650b0b20b5200341540000120040c0c00c2e58500406040122007201c010607114590506c0318481300d403200445c6e1244558807180f00380c1d580d4403040310076a520f00e203030300000e41c0203c0020300032508032008100e900440341c071a101c0c0440d030032a40c2c00704001d8a41c22200c240c002040c1c4030030035010584c039040c442c050219a0810803045400405c05c290700b0418070b0301000e8540e20000c0104000b2990011800300c00c0940c103038041c19941460500206681c0d000c189404142c1c03508041401a9646101c008a00c00083c4031030350703140e0399400f0340804500414890b50101d0309038502c1c80c21a50103140404003e087c5a81c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 467163830 1250 467162580 467162599
    0xb0a050d022104080304060e030307050a1809060f080d09050d150f020c010b2d01050309030c0a030824012307060501080f0706030b010503060d1109010303051b060402 73
    0x58400000c0d0800089070305035840038502c1004114407031018034003443c01000019038070f1030103081040903295000701120480e4010000c0100302c41d0300c002500d085400600d4001c603030007980d01c0d070f0654048940e00013810403850041e001031203000c10704c0d0040480702c1c01400d44116000b000c505440405a07445843d80226110f039003003002850080d8481042001001c00040e00081d20703201204a80110320303075000e1695030f410701c0c03046460031823a0401c92a4a0250211240c0e641c0000f001d0b800400203140f030306000c400300224620040c148182e40c00203800c0e00841e95a0621804e0041007a00251000174041d10490324817042e6191408c1e0400e00301006031201100f4400848115080b902c0c011000c030795141c0c1c2400b19000064860143c2402040120018034042106400c074a0600801c3d5028070141850090100c0141e6000340950794001002c56050070b07c284c2e2820074030351902008003400c0e0300545001c00841055000406080d2803614001a070072040301460b0b14a580746420f84006c1d52100100 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 467165080 1250 467163830 467163847
    0x80f03130b0c1906061a0c1c110a030f0318030c031b0605040b010815373611060d0b13020c010b0d0807032307050c09010b0a05 56
    0x11401030030340b01101c00071150b04a001905509140e02a040100c070855203942e030400040c52800129010410b40170078903450480005107040d9503850303441c1c41d400d841d1100101c0070f0120f03005848080c4007207440c2080c0c0703209c1211423400905107002060600e0100386000d000402c1c1000002010303013980e506440d40806500c094130180d84580b11940351151544641004400190f5103000c1c2a0003107209440301c02a80d410942c98a00303001206903140c8049400c4402c11010411300c0481600c083c9200c2131418808502510034a280c0c0b02003510b0319805414140f0350002d29280003240c4108411104241010120440070b0240001032020040e0490243d080c490007240742010040c00004002c1100050503080c01c00803c9000c000040801d401d5036002c1984640690203000300a44485d0888880c200c0d9005a62100365034040c011018042100b22140281d52010f940d10390000d034013949411070b0b210205890466030301d032954030000f4002c4000704000100c62075400c054580b42d1005171122800c12445 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 467166330 1250 467165080 467165099
    0x23160b04121b0503070815070e03061b07080412020f031c03020310090c090303080610140307030b03071e0e01060507022832031906061d01080f0313 65
    0x1000307004a410350074080c00201030780c08000205c000d1060304060200f00421001d0044000d10003480c2c07000340015005425001da0300440c019510241c062038a05c10800d00114607030700e074060f0240c01480400c00046c00301e0341544901100002d18800c86030107040000c00381c01e040d2124009580b070f100b2000c6047c010403e203030007600078540c071407800c0448d04400399440c8135420a452070250a0310104000311424414142d10807240c5502c14000d0300c01101e02c0341302000081030480014491016140c0c01301c08a448a48280c01c201b03003d01006085812003911000c0c004055002d224072607010003000c04000991042ca8641c941c12034020f034880c00e080c80119003d0151309809040c201c1c0c00f039909400e0301c0b400320f80318101c410050400840c041e01d2032003414140d42c50400070703480e8505002040381e4070001a03645c00161002c21409107188401d1110030791406002809982d08044451045054202e900c200e801c10a141214110b10485034035a0010780400d423244550b080c1007a03001803003841071000001 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 467167580 1250 467166330 467166353
    0x13080105062d010e0402040902120121020904030e04091121061810180309050103090210050c0106080703060b0a0e041101050708190207140109050d0b0423160b0412 72
    0x41030410413080981c0600140803a801030304084183c0703501084622004c001e41d040240904002402c0035075001800c1018001c0c8080c42c0310003031060641070300240405d4410b4104ce0426403000d031041c0681c1c4424580002600300c081441802030510760805000c0740031800f40c1a40d003180d548060169900e9002d41404804640c03a904000740c13054000d00c1207500b44600c10311200c9100000c11480c0d00240745001800702080303a001d00d04050038642c0c442c0141c0d0762054041c0c50460700d42845542c1e40e040720095030240207142c0c481e064034054202c00005124040d0070030100b100049801f100c4007500da89603082c00c243d05032400781c90081030403500c0c052035001d540203044150041d03084600b0716419143c03060520214011260040e00500c84c1001100c0622109104813402400c00b404050f0914003c03030948648614054503a04208021074180b001419800c1401011485502c24040c404014aa030b124545031401e49002506078002440514400c140c4090751800200c4d0b8800c14034903280d02c2441035 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 467168830 1250 467167580 467167669
    0x62d010e04060b0616031b12030f0f0c02160503010c0503010b0a030617100516021906090506071e02010c1403071107170601350c061308010506 63
    0x41c0e40d00f0301c040055450300040d21402421449800c0700000da4a4000c000d901c0164544a9040d4010941000240e01d2103100702c07140014035000402c400e00341402c0000e007603079002030300c4210328140e040a80c80f41e02060b4444007541c03400d140300b0815540d2043c9400c80790003001400c00280144014007808a6000050800200e645000328403203465041c140c0c1c070078168030190107a070380c040004401c1d001c045000f600d034403106070b0240110104101c0303c040e4440040140c00b1000744d00341d006500400a032548030003c2940c200c400c0318500e20b08500094655002001e03030007584003844110012040c81402180036000c0d8559034824030280068044c005a0009000201440102110304102c02801c0000a0040140c1d0b801001c0001002580509240040c2c00c0074071121003004140f0b841d05d4142d0840b21600b140c2d900e01c038007400302203082e55080a84883c81903078410f4001a41d40e80803a083c003130346025150404000c00803500c03010104011428003001d0223242c68954000070907a065081d0140740741e40d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 467170080 1250 467168830 467168843
    0xb0919080c0105031008060f0a18030e0f03160603090c08030a0e15070203123610110d1205090c090f06030709020c01090b0c07052104051002062d010e04 67
    0x10384038481e550400340302322000602441e4000422031488078500807030f4640301403032100002c2c1e204142c800600b03181410b000a80500310070802c1004a840030020120107620b0b40e0a00e050050b10380b0700090140c04c0c80710042d110f00402c4000411038290110845401c40c080351112690500c5100030b01006010070206403400c40c10a002c4100035850510601d2101e040d0100329a948820614000b40107403852070702e100c65150780c5201c50f007040c0140c80081401d500110703003440f180722041c80c0c00c803070504d009858410b80380600c480f207188035034000c0d120f5075800c81c01c04400d100355591140340c25a5202d01c264241d50040c075800124406034150a0271982103030001e01500c1c1616210052002a49e0024030f042103103070341d00d116820a022070000c825402a44001e03e5030315100c20307903d03405c2da00d4009001002c1c4401030314500d803c5141e03400003100c005003400790101c20300b0392a08102039110603086415080c5141020810504c14010642c0003403411012032812821b82d0030304644040c560001002142c10 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 467171330 1250 467170080 467170111
    0x30209030114100911040911040f060e1503070c0f0c080114061c030818070e0a1b02030c071a07060510060908060402060306010f0212040b0919080c010503 68
    0x240d440c02e0050350841800807015040d28203010702d92405014255104025241c5840c20303000040c2541e2085500b01c5132100000b1840c0c910000000541e48200c5c0e1006c400a00b5103900001c0550300709481d42c020303200885546024031409800b140e01d138030044505400080c0401051800100d60801d02c1c40400e0040f04e00301d288075151400182184c5108413000d0755a000b4804000161401c29025501203840e102c0c00041403010b40d401401c40f850103008000b0b4240d04114010480001708031072002041e440023043d10030b04040354030200620310900400c00c0c0d000703003044000510b80000119604464041c1c0200802da01d09105111082020400c000b0110380401c006d10100380c150080c41c1c042c03114843c61101c800c0c9000c40c00341c4841c0043d400b00000d604684100000741e901c0c0d50649a1113442030030012504000407404034100300001d03401c1e000b081c1d400704000c210a0a034074041d0164240565060074604020800388844644600c01c180c05580004101c0c0c1d10b03944607501854000e07480b59000100c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 467172580 1250 467171330 467171347
    0x5070e10031d0a050c0f061c0905010207030e190e010501050a030b0d080c06090601060504030b06030c0927060c030115110109110114090f0f01050c012307020312160302 74
    0x5510020b0701d94144a0303115640380400d0110510404103030300e1045805142d030308640f6021400d02c1c02030a138150201c012003200010505000d03002011000e0307008000310364500c0300d4039024003246a0190320f54010b842c6040540310700711b80c0c3c1c8040780c15904100002080faa1034071004480300e41c0850440403c2540780c0c2815004e9071500c0540407442c40c071441c41c50b42c45044e004001da1910310000c084400b280c3c0f1400042005d00e4008085a00340c9800101107180c654035140030902e481261b400c042d812100d0401045480000c1907000f10b04450145040500401d5030071110344e55010540f5841001481000100300c10030040b101940d51060038240410f102d4001c42d061403c407071020134207079812900c405048500f5a80650040c13903212160a07e14281225980415038510b188d00d101401055281c0100c8aa0380c01001904c2e0504003900080c00074507018816039074240c400159150002c5a18408140c3c20360001c001d407070f00304c411103000f65102c1c2c0c0d07000c0c6030000310261800340d41c0500d03608100d01030 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 467173830 1250 467172580 467172611
    0x40b060d231f060e0607050a06060810200c0f0307060507020d03050919020424080705030c01050322020405090d120b131e05090601031505070e1003 65
    0x14800c040041c0070068002000104003540c040c018120082101406030b01d440c50342c0301402d03140aa40241c40e115407841c60039008990144200e40c805031540c8240080e40c0308100c51500604c0070b441c0c40d60f054603082c080c80c078218016582084400350841500e8030011160a100c580905003151103041290300c0b4003a544101e50850b0b01c00b100503550161900c0030042c045404000c0100e00800614041142d441d00c18280b40d251124844010081f600c1c400e151825075440f5000b4081d401c1c403810300551400d04a28000010201c00d108503540303401034600000b01c610740822010403039031068640500e150340301c002c0c07240380054a0f01104211240c1d84079400142c0c45920a9500c071324950001001592003400c03000d401c401c44d4445d200160340c20070041585640b0740904145800c0740204000c2020f100e074100301502c10082e0701d500d05125240004124a0fa840014040e04032030181a035209000382c80148401964400c035202000b04928680800d05410303c1008400000d441c1c0c0380001d00c01c4c029040d4103 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 467175080 1250 467173830 467173841
    0x13060e21030d0501060813140c0613060806040b151303050a08070b090a0c06030b0d05010c02030423090103020d05030909040311070605040f05041d0303070206010e2202040b060d 78
    0x12040359101052a03903071603007188105800740c441c600300046a494840e0700c206e1240c104c01c000030a02c50784043e0f00b64001408000071441504014901e40c0c0f52421119801311803003003441a00c000403401c02c085407440c28548103c2c0c4d0900c00c050b0041a005510f040d8070f10f481e0340716541207120103800410000210b00103001e117001940c4100d40c01541d801480c1490441e41c60041c1c05910f490300101210b1b030006a086c12907004480d001c3c14041200309000340062012000200c000e00a0750914890590342a40400100140c4021003110f0840140c84200c0b1781c040d0a007508041c0d0009401c6c130042c80940360802d443c2603643d200b00c1c02c1300c1ca0600c0a0001c10a101c0f01500c0440100f0f0450909400480b014007009020700440e2800d24100340c0341c0303c40350917070742480d2041c07900469944414a45041061a84114130780700041100d50301c0c180713200e0080d51000c0134405c040d40002d0360b0300414140d00b00100034000c0700c4100211034803d401c880d000c100003400b0016440707910001c20004484504414000c8 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 467176330 1250 467175080 467175139
    0x6030402150f07110f040209030a060c170109050412020307080a030522050a0203370503040f03080901030605010e130b1f0309140c031f38010513060e 66
    0xd04422800400178080c1e00e044401c0054429401030000083c0ca440020300907501c80e400640104001c0011038080e40c0c1c1c450700d1102c5010b03d1080c0030010680300d016800450242c0d1060400b4102c9020400e000c07a10790103228402080388404118940007944a0340205401900699114400d0f002d480366100e01455050307801c40c1d4940080c28075605514061121001121000c000405030710707000342d000d6441d0018904400c10f0410581e004a003400070410660b0003402656008140303003910307030611203226081451640e0001e81801008a40c0e9403103841d24040b11100900341c1000002d96a22050182c244109000d421440e10401084136020104c64203840450303d8400003072510031404c0c01110a20fa080142d140e075404007141803880c1d180055259143d03805585058160b007002c03001c40009e8851011810480e044022090720b40e1440180625041c180c2030480ca604a0549401510306000308568201c0d403004900e0100f1000c0d00513581d03803024101c01404e072000c16011100c85000f0181d582c00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 467177580 1250 467176330 467176343
    0x42d0909020a09060f032603090f0615150c0a0c0b0d0612120f120507031a090708150a031505041b0b030c0a121b02100203010506030402150f07 63
    0x880605604025881d000500f0100d0f200340041d6040c81d008018040311444000c0075025441d00680d003698040041180000510800c245d41e420000c8071146e6400c54402d030442c00d800f0b10380c040740c0540040700c0042ea1010020f011600808100d800c003280b075420000090126000b60b540d038400107003c01e821500170340200d407040d540319582003001c0011900c0d00e80040001c0c04424800e40041005080b0740c00d60000d00345007d201c3c008030b41c04100c92681c59946280c0044c4d00300700c10310200f650150071800f800e45641c00c00e0500300903444100441d200c000c1d60404041039841c00407038078102e5500074102c45541c0103010030040c60b0f600c0c0e4070700786107500380300c5150101c81d0303140c00b840100480caa080d11029181545817a04080c24560a00e545210162031030140c100006405e04841e070260441040a9510800812000094a000e07200380c0600c600f1030001405008088001414588240d034182c403030141466003190340355420b204039000c0d103116643c2d800c04140100d00140e45824000c1c021944107d4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 467178830 1250 467177580 467177591
    0x1b060f010612020c0a0b04021302070c0e0606071101110a08030a02091f09091d030c0f06090a2a0314010f0b0a0b0307031109060703020c100212042d09 66
    0x101d006003140c41c044114901a401001081c62929002607200005900202d4104081e1910f1000a400d1010440054200c50020801c032052110826280d0200c60840205010301d64038a0100503640c81001c81c0200348030749140019226520403070700c00072494010000c07100b42c01c02c251661040c5800403a0701ca00c03a01c1d0002103140382d41c01c2c80c0e540301c20900000304503407140d5151000040c03c1c581e240c0c001d0503c1d5a03560140c180349140080c442c59014141d040c00d90342e40303040c3c00c02d0326901d1b5440103a100c01c29119500c0403c01c0408000f402d0303401d8a03000746d04900d000d843c5404e0482c3c01e0502c00b500550700511401d000c40420080c01811038020b01c0d04000181c0c620303a00e4680d07000d58128038402e91180380440b60400600ea806800c581e403002091130001104075040c4040125805100b0015404c0364000c100c3d041016000605510069000c40700781d03684009000c0308913502d100e41008854010002d020800120804950392044080515102044d581e07a019840317001c0c4245510000c3d40b0381d1142e = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 467180080 1250 467178830 467178839
    0x8190b1e0a050a06021203090a0c09050420030307060f02120f0417030f1513020d0b012d080403020a020d110907090e0c09060702030a1b090c0c02061b060f01 69
    0xd607581d4000e01050307803031220baa4507000c030294440c011003454800c0e992001001980604040c4903140e50b5903070115252035100e40f075545c0d2100400044504031400b038500f100780d8000901e4106100001c0318020011032030711440e55111300141071185102070b815502440700c4906074030700c8840640714100016002c000d40c61302d420b1100041d41a40d0198400c2c0004109101c0c030729214070201a8420150f00740c2c110800035a40c0400d805842c0d20002c4000b8520205642e4103410207900401c424020990307a146005240060070700408144240e0790700e00c003c4003146d40d1681409001030b154041d02a00540340722311240e401081c188002d0110803540036051901c403480074905020155041001071402180c00c508204200a070b460002e0030051421201044030301090361a2011500300710350180c16900c000c00b840c50000070864100d0310030b80718040d80c854080f50088843c4184aa01b00e40c5686d58407406400360280410360340003900090040f45041d0400e201c0032001c01c00d05003d02d103480311080307441d07150 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 467181330 1250 467180080 467180089
    0x7020a03142a040c0216030507080c01020f0c0405041e05010b040f140c13031a070207171906060803070b07090501020111091005040f140415030308190b1e 68
    0x1456102c1041101c445905509104a00064003128030a450004041e030042d20103a1401c5403a40700104d1903018454080104400807030300d0021180c103041101e20543d500700042e03803100e2615801340d0041e880002030701c01c146070681284e5042402a15501ca407100c040800b000407400c0302c0001c0d03d65a454408011403811320b445030300e051802604003040041071340d591010091001801c9a0a02c28002c292920080c086072401401981c0c0000c007103424100918603180440d20845040780540200107001540c4d800e180c401c20f01701c0e10400c001d400c00c14071004d003424083c52000c0c1d050300e0040c2d42d0a07001c00c54400c100004c022140c0074418004103032400c004024074445181d00400d046904084010015400c1c0005071105004c1c100c80303803030580126044c01c492030f008070b0b40240c00d01c0c0213013403001910346030508900c0c0345020151418032184c5040202207110104c13911000340000d407500d002590815880e07900c00c01c07006151001250101c81d00000400101002806c507110601100c145645881c1 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 467182580 1250 467181330 467181343
    0x606020705090906040303050c09030a03031b02061902030403021c030b09100807061b02040c08040c0f0b0703050a0212040b1c0606020a0f05070812041502070b04051507020a0314 78
    0x41141c040545240862215441c4c0e00040c00041c2459241e03c00300d40c0b5050044161082c0102c003a04554030b044880c10b006006e00b4154281d00301012100921070001803011400b90321072000501d40990810581c0d8030000207600050082d07086015103610401e12000003920001c981800e542d010030401074500c20030100000240c02c80c1c0c502d8291042c2080b540d200800d1540c111859810000003000740c1d03c114803032912611400a5109140a08a94016800c209900c0c051402511100b0600783c9480500010070764901450740c10690a0120f100040d201300300600300c800c803520644d203501e16449400116030f0000c0c6c00020100d50041020301c00340100c41035001007044404009c0c0051442d1410282d198003041d00b01034103030410300301c1d03506c28050b08010741c0000300310b20011200c001001c034403480c0c0c0c0c90301f00d4000d21048c03814420703c20160610029888040d100e64000351840d00c5d14000c00c204030103610303565006000302d0600c02007025075aa642d42c48e00650154002c80d1824600c4000b4904029 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 467183830 1250 467182580 467182589
    0x40b0315010b0708040f03050a12020a020f0603070c062d06050a030611120c120105030a0c060f0314130c1e0e04080403200306010602030f0f0d09020a030606060207 72
    0xd00c09030459145000c00c201640c111110751aa043d52900c040c100002d6522803500010101200c00c08000200200094100d14450013011720010070b01100400300c0c0c4601040d04041c1d440002003441580c140b608500540d085050341c2402801c1440d43ea0b20710f0103555801e0007070b0142c80401420100780d000505890103910021100804c0b0141c1400300040d2925038a001c081c01981d550907140d5100e40b140422164464003040c0301c4042490040f09070000d030b500140030b055007080c810000046e14100021003883e0507500000e540340860410f101102e11081400b41c8400b003649515110221080c1140c048d03028050b00341e809a4000d00314101001d040c40590701400800b010000c250080c14007488010701a16110000c48545843d039060500f907a000d6504050000c0c100c2004074141942800203061030414154195211681d8400c01a62079010b01c010b0208041ca04201104c0245444802007200e00c501c400c00188c0d25011f07401265001d4216002115000d683e917006200003601040b2150050 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 467185080 1250 467183830 467183833
    0x1083414040f120c050a032a051e031e03071208070813030c0b071e0f050d05090f071d091b090604110d0b010305010506030402010c120e0d03030b040b03 67
    0x1460b014280c0c84441c1c5601c00d0701c0340d000740c102c0400c0030441c90911280007024024801e80c032076a142c2c00c0000c41d02c040030301107076502206502803640d0035215122040403144002e0654191030803400000c84480d00040905034180100c00310b6910b5420100711082402c402c042c004c548030005440c018034200f841030f02711024810740380104040e41c0d2f130100d80c81d60300842d40da0f8003441803421440c0c250740c0082c840d0760090000381c4180400c814540d0007044408000d605c60210180e46003110300c142c629000350440d0200041080100300304078103442e040190000c40d0081181c000214101c54141824a55080700b4002d10030b0340101082c94544284181d00041802d0181c9040c42c140401c52800500303204509005011010001e40140d8403a4030000120a01c0468103694540e000200002001300960513804280780000208080c2062020f403803041d58103071644200711070540c60781803890300c03800f070041c0c00c10802160a0f001038079150303204502c045c4291408a050009042000151004a42668041d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 467186330 1250 467185080 467185087
    0x604151e0e040e0f19050f0304171905030f09030703171b010b131a1f02151b09280302150304200604030c030b0405060601080c04030201083414 63
    0x201c002c04254085c001c00164030155031080300d4a807aa05140425501140501020400045c1b541150500c001000045810745118441000007281e9010040001804550003032204040c24084a401002103400040c01c036107111b40d41c1c2e036402e18074100c4544141d080ca8404200c420045072215820030110052000130b00c007040c060350101d601040c04992110449884502070010f40603103091550b410040a0300300d409040d00041c2c01c050503500204684010301c03404040025102c44060818001c1000049519000002c0501b04206411440f011a0700400009620003102c00c03000c83e6000b0300f03a0090010052a10314010400042210165044a103204004010009402c1e180000001008403c86840d00c01e51001240c001d02507608014a164180b40c0c02006000414803d00e20552049040384c8031540c03840011102603800b50348105014005110910066000c1c2c200b80b035129025031078501180c151807521200402c004d03a800c03621183c800780c003068001d03401580744034201c0c0940304c018036 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 467187580 1250 467186330 467186353
    0x115030e071211180f15040e0604140d1b110315010311100509010c060e07080102120a061a181c0b070206070219020d02030115060905010e0604151e0e040e 68
    0x80400c008002c3c240180d110320020b28186c5442e031942c405560041c0c4104101c12100000c6682d85800380c42c2501c2030300288007c0721041c1d0000804000c02c9420703030303201c040303000d03056960200340003c43d00100c5222000c41070b07803407450b00c04100035401511007080c030b6450b40d40b4601784000f110b85141800d900a100c0b0040046405d41c010084890a000a01e0854001c00e050708084000304421071301c00c086409038020024040005402810026000c0e0300d40c2c1c041c540340c0b004000202c50035807181810200507035001003007020300b08001e001e0107094090b400f08051540340c00102d05d510324101e2042030304607004205090043d402151940001310740001c0ca01400c02039800395660000013018038402c0c071143d0f403a10854071100d80c0049500c0d4058024058200742c0300909021450314040e54000900c1e4140010b041e6215040d80b004007a0058030701e500e003030308064032551000c9100d80e00d40c0621200300038402481c0d403240e0070251411600c0d560751a1101d03c01c001c22050312800049100554400b803004038 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 467188830 1250 467187580 467187619
    0x608030301060e0927010c080a0b0a0303050c030f07030c030e03010606050d151701050916030c0303050f0c1006050a301e1a010902120115030e071211 66
    0x6507400c40c115595451555421300500d0580170081c5c0295040700704016181c09120150072000300c0142c0c9880740542d07941c03242101c00449105045450b889160b4510802c0884e0203017000b0600c0303002d1a0140c078034001d82c001466039203601a540450000c0c00c1022490300349507003d0146242c26004800a000f010b1030904010103d0081040d846481a900c0300d6400d680c680c4009030000600e0890b030000c2030300d01c3d6582020300030403049410030310b1802400096540711806e11600010390f6400a802c2c1211415500d080390300ea08103400c0c04d00d6143c010041254241420800800b41104a03640412401d007003400380170502c11543c2c4a0502c001c48400a0340012101c88400b81210090000c51021201981003030b0381da899855500c54207415890400030240b00c1c04813009108401306200341103503a40d888401c40100e10031500b8071404680d616005003c01409200300480c82e62852a01080300c2c1417507100103013040c01ca0352120b4129000c4800803001c0000c10f001203446070000321075a00c1c2c1688a040e422 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 467190080 1250 467188830 467188847
    0x6091c05120105010e0103200d0b0a0b030c03040f140601080d260408070b01120606050609011706060f21060604061205060409080d0e0c06090a030212010f1401030303060803030106 79
    0xc13414440c4080c81c00710241d11a510601018012400b0f800c241140d0703d001d085507a10000c0013020b030908000c080c104600b00f0380064030844070742c1407c0340d181d980c50200c60700c2c56400c080c1c411034440b0006400c0307402041422148020800a500192007554900005507190814156503a010b024005105031030b28041100d007105801040d90300d50702c4a03a550301c0d1081d2144200640101007041900001c500320800140014031a4420042004410346a2041108a0203002122800607107d0782450061100300010f00f60410b0002c0e08140c2050312820450f20250068640345d80038140d0346400780691110411510740090066036002d150030305100300107001d00300111103c0c441c2500d03903012900310344540d8406080d0741c0d0000406a11440c0b00d1000001412401d50b51981c94812610404440d10b400011611048001071000c4000c500e90340c01e000e40d8050014071002c072035590f03a40d0750480d4451401148c04202100d12074652540c10341c940901262070030707007168046500078401400031f6034114610 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 467191330 1250 467190080 467190089
    0x9010801090b3105090a0c0906030b0604020702011101050901020703090b09060a23040b03040302060a110d0b03100f200309190203010902040608060a1410060f09030506091c051201 79
    0x441030070040f480d180f0f24105a0400c42c03040014944400c1224401c00030803c9040c1512030861180c1c1c0030754603184007095a00b940000381c002040c940200e4200d250542c010036000c1d1040c10b180d01c0070100c804c0b1a600311403045820000e02d94000401d481010b511a545001800019600c1b90600400382c000c41c4590040c0c0146d0790500100848003100000c0131000541540700100381c455660b5200c0c11700708125001903a0840151007100007080090b40700d8040c2c696080e5200213a0b81c02c011007140020007400c2d20101e042c0d00360203101300340300701c1c85954060303403101000120000c0f030070012540d900000202c24022250700900e050090008550001c1100088035000341d004040b02d014500000e40100f0400340c0083d84680382203000102007d01243c103a1080341c054000b0040061400b001706603007541114500c5800304100410300c0018068800403200703607964941059495101d690725445d01c5000e40300c800099100ca20090203044210034400c407000c1180c644507003808007801c800509148180107 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 467192580 1250 467191330 467191369
    0x111209010c0215300c0c0f070b0406080906041109070e041d19030c020114041214070504090305070615232d0d0204020f1b100507050304030309021309060209010801090b 74
    0x18841503000d0101f250745218000c0c4420741d0f801956440765950140c1c4144100e502280b0f5040000300903d002080580c4600e40040101690003080d4040100c400002441003040c48068038209016480b103220380481680f00001e100041014045004e1038200094400b2404c0e001c406c3c0c0203800680c0c027010013840d0aa0a0902201031600081190032a00490b0401d020b54080f6130003030310074000121220ba1a004100741aa0040303620349082c40162040d40300042c1c0410010031142002511907402149030052259000071110b480e940e0b9a044061141c03440c02d00717074600401c41c040ea0300d403a50b00c1c0e00d02c0c00c4442842d9070160803030040b40c1c040c0e080f50a00d01407240c880d40c10154259200c50f0101e6070b40e1281c95611641d6030707840941d07500201a8000c200c1001e845007400920190103d031103558010703280b9860309821541c80d540c084001d0001110201e80241c401c265001c0846004d00610f203200d48903c00150b203d80307106e0300050545605900001100d81046600c1800740c48003034075900108081c08 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 467193830 1250 467192580 467192587
    0x1006210302030409020a020a0204062c0a02090d030903200d12020c300a050c1005040810020301090506090403120209030c15030610111209010c0215300c 67
    0x1416402d6000d180d00a900040c00041d0382d44c100c584c041580e01c0d032288211400c00600c0e440310144440e81c1400c294203008212101d481c681e03090040c01007581c2c007411840d405850580180080f4860343c0014000300d021a8001d0818020803000c0c10078110604e030171040d0302c00206104000588a83c003103050140c480302049440000c0a031003880603810119000e0400c104491101c40c1400a81101c058600c07200030101c0300015100c0d0021589420b8950031000600386a900c000401241141540001040c80010800001c0c0002c003488400c12808940100585a614080c00e4a041d40d600605844c42001807404110000741c0007504031b81440c07000c140050320f48032b4480210b45803451141e00035a0240512810010810b503480c002c5104000c1500e10065002c110002600c940040c00885460350f0081c071140c80c40c07005440041d000121051600c2d4002d0290703600480d050150341013056407113030400070314403030441443c0c1d8034150100c841c1c02e095813020f2440b0614060b11000178044980c1c440d0000f = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 467195080 1250 467193830 467193833
    0x6260c0103020d0b0a0305060a06090902091f12050309100201090215030a0204030209090d02150106090e0a090b09060402150f031b07021f1701140409080c031605100621 74
    0x5600840c1c0e10341c1c0103003094600588a0500548d120402c444059416040400206600b501401008102607024103521807039203502004550060890450042e02c0301604000103030340a0340d03102c415650f0b004201840e960440f010910041500104501d0196030501c9803ca00503214103000905003a04200100d449841740e8040720080d200c0c6920107035001c0d02c0401408445040820340401c118103980817105080030b07591126903a901e003442204c01040d50100100910301c8140d000646c40684030b140041d4513007859070303a03144288098621035102d81c040700030041181400352120030344009250126050440c0307203240720f109100082c5100405461103900c90480b07001c0c2d03820348040c5507000301070080c4200c0d201148501d0015008400340000e448021140003010500005410b031407140c2c45580c80401c0040c1804040e048800b001c0701c41c10010814a1180c000a201030002c40728082401006414181881d40c5420b041c00945007a25140090412965000b082e6919440040c070010700c1d030943e5503 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 467196330 1250 467195080 467195107
    0x10c08042301021c0e010b0901030b0c07020f04090f0b01060809100e03090907020303040317040c03020d1a0c0406111912180b032502060c18060c0106260c010302 71
    0x14101307880d21848140710002038503c1c0a8128865403440031000300942507904040040c07940003884050500c0483d00082030901503541c006000c0c04c2e00140078040d641020001090441c4c3c02000c00759000341c2c10014890400c10420384481c0100800c1c60f00d0496402c0c84204580c81369074040a40030000d81c0d40140d10300c00f6000f4019078001c00c2c001004002d4500c0c040d038000e901da900c200d40c2240015004510301e102200d84c0f01d0500e014a170000885003803d1300307581c01d1045012203640d0540b412a690700c034400032044500080d40c0305424940c82251500c1c5000c0d8080c019607204040c1c1045500300d03400c50750000e034034401c5a00070150421030501441d4041101611f1040c0c01403058080044a81f02c080340081c2c01000641c014281c5036022034840003524280720511080c550480010381228002c107040441c160b002d4020b0500c6d43c1202248914554005410b540c0503540808882c1d4491000304520526543e003c140b060728090800782d0700000140e859180c0038001003003410700d5400b182c12900c8024 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 467197580 1250 467196330 467196337
    0x10e0c010f090e090f190807033006060f1d0603061f052109150a0b06070f0203010b0108090c012001051e07051602040203070221070203010c0804230102 67
    0x10b00802c507022401c1c071412640e05c031242c11038100d10a200e1403801a0301e1010f2040c29060081c4c01ca5152800c20100c0c2c0e0f01100e60822000030420018000c04112103034501c407003000700241550182c0003030382c145440405805d03040c0808000040c803003410724000d00c421290000001c5a10704450b00741d0751340d40c1d00e0009150402d017020148401d003002c490b0280400d802c40014206400c2502d50f014a1610300800303401c080398205c1c1c05110341d4020481c00700d010020704a906400c1803010402060340c0d60900049082074020803c2075030340804507030003034041d41401e00c520b280400c000c2c604241e0360f28100820b10743e14102540c18504100011a5180702452800800822070800304028403081c20b140804401d40d5010650071140d049503031000c10080b900072400ca6003a415810030407601483e607502040002c0d00000c001000b9800b50344407149142c49445541d020840d0500d40c000d8407800c080c0141800c4440c014150010312041400b8000410014400382404c1206e00f026140f43c081c0d0807040d98003900 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 467198830 1250 467197580 467197589
    0x306040e031b010506210d20100609060b07020918011413030f050c2503050a03091802031e1302090c070b0f01050f09040c05060403060606030b03010e0c010f09 70
    0x16000c0b00b03035140b407601900a640210000c44056641110f104514003010640640c003242c40e40c0500f840400c2c45009000785e50031181154004100400a5070f440790a02c0302da840d0008140d031361039a0600040d88148901c40141100c1705062b81440c1c1154041260a08060030f9200032104004650283d4032003504103008007904d07080e801d0402e08000400c0780c4504503500d0211b0115900304072028040d0321a0003a29482502c0c04000c0100c144c03c802d99080401c080c03410040640e98070742c004400f00c0d0f02003025142580c401e94a09425900d0801c81000c0c0303420300c1c61000180c6004105202d80d50071494401c4000c0d2041c0707044050340f612107010385006464565002500800180c04010080414901074446640104194407143c4e849040f0070070b07200300074098181d2105070140007034214180703070341e015500038070450a5044442c4c481d00040d40c41c1d040380e0700031a81691175040c140180303680b50280c9451340000340e0092108141c0e594005403640080400305040050000d50302000f01c0c40346e900c000040 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 467200080 1250 467198830 467198857
    0x801050916060c0c05040c2a32030f04061d01080105010e061303030503060f1f081008010f0f0c03050609010509060a03150204050f01090812090409060e01050601120b060306040e03 79
    0x40342c182c43e001e800f071103401014000c405a00748c510311109407104c10400000e940a1580076960004c40b12440c1e815a1400c41801c18510400c6c2ca410b400b4000c00081a62082500e07070a42c6880c541280246910340501058510101003c045280e99070046140c0b81960f80034202041801a4040807c080b0f0181106800400c03031010800414141c02c18001c6018441c242c0705050164005414044c07100d00c15603030038044005102000410398440c0c003000d900080b000d03040200c110303a0703001c8140c296400030b50034200d000d5035003070141d8210701c041c40388020040041c02c090249190374800507a000e4014400d4500078905100001c83c07541d6140102c40107540d1103d4141020322104034460029041401010700418042c40030b10000d6000b5071200044a0250000f07100c07041c103540c03c1d10025000402c030300350480c0e03c0300c03c0e01c400035515002e40e522601d002c0000041d28500040010b00f0140c0002c3c01c500c01510341025100c0c0b40c0c403403004503940040203944c041141225568058a18420301c0100d1696 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 467201330 1250 467200080 467200091
    0x1101031e18021903020306040213060305061f0609050d12140d02091e0603071d06030901090317010f030303090f0c0e0708010506090109031101020c0310060801050916060c0c0504 78
    0x810101440580d00d40281e5946580312070303800f01840207074010700010350b05910020000d001803078544894054084001c4020030700d5561380e0b03038144c5080020344d421350310a50103629400404841030380c20300080540780b4001c107000c0d04d4240440c4203c81c903241ccc05450222005600c08091b03005400408100015206043d501c0f20911010402904451100b5100c1d11000d2030207840a9081403d400c11420001e0042d031441d1104002681e40c0c81c00081c03601c00790140800712220b5a42e580d0040d40c8103142d0707480041245401d40c600100352001e00d1007001c0a5481800c014404030301140d06407001e403545400d0019074100c0d41d00b004c4049401e9030304014401d1072200c20120f110040040510301079070040d2143d000990f03c1d03204203c0d203409940340082c0000c2c000075080000c5101c4442c0b6130f40c1d0f01c8040c01910030819101c2c0102e800c00314019080401c990702d0b07210401c0800400d201d0240c0c40740020014200640f4845520241070700c0910519003000056002034040c40030080d85c680041030020003c012 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 467202580 1250 467201330 467201351
    0x313330203040f0503060106020304170109050102040e060405070305090319051b0f07060804020d0b2802031008060402030a0602090a0b040602070302130207170a020f1b0a0807031101031e 82
    0x1580d0b072081c022580c0151504000045505002503442e05842d810707000b5604060034104450f10854a61007020502d42d21381c295a00440e00a03c014000b0f06560669051540740110074002540c1e006451002058a450100300b000030f0040309440302d048001000c000c1000440d28122124002d01440e00044500e00d004d00011610006d84000540008003d94680596800c0b0546030440b0440e40650409035419421000410720f400c0240d020030b10b024000c1c0c0b4414440074040c1c91101d49222614030340e50000c05c2c010199a0080503000402554004110030f24250740460b45030819100c005042c60f401060311407443d503580b551030015040c03041031551507561300c00000396a400d0511080c0d020301c803100c0c40242aa240c034021900700c5604038807090740005925445002c1d03540003041d100c04601544641448030b580c2804001c802d043c02030038510306c1008003010000303010802c0d030001800b41c0c8660410030000d101c0b002102c00c82d19007400c0000b41a1240d007040d400c2811b8200300607481d00d292245184 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 467203830 1250 467202580 467202583
    0x206160e03011b0810150c082104021c020d0f020409020d0503130905040206090d080f07080403052e0b1f0809010b0102010204061b0f0f0507030b0903133302 69
    0x10200c03ca0f540d80720703a603446420b207840e0100351900400c01c1120301503146001c09030241d618514514841d0300482d02e410303800182285001140c4181903204100a01400b040d440c040b010b82400f100c54500c199150100f540c00078009101c040c600030010401c0c40d01c1c0c03109540c1c89900a074882e5401400081481c211864070725200c1e0701030000e01044c2c0078410320200e602502440380d54422603001e04000d1a01c00d000301001801d40c6100c00c2140c1c410401c2041c42c04030b401c3c1801500c00c052160011a84403415071070170728140400004201c00b800c0b52450b5943e503812201e6031007000b403405030a00050070426580452500c100900200d8035541040106a06803940200c1c0e4501c41c0010a00030003074402404012400c0c3c0c800c40c441d05000030303840040c2521041020715141241c0784281c0c0034004154075540e581d00c40c0741a10700d06032101e070410032040050102c2840f844c2e40c424496006145441c1c61008195141d120038081c1c80c00401040344880103034401e8151001103107281405000011035500c0009 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 467205080 1250 467203830 467203871
    0xc05030403230d170c0309010b031204031502030c070f03020a0203030f0706050f070f030c020709152c0a020a030e070f06020c03010e12130b0307090609080d0206160e0301 75
    0x7402c0c18401d1075140f450b0548150b03202000714409001203081521500e12805403a00b0141000482d95610072544850765410042c44188081050201c0d49491031420422403146816201a1505004100300301c4445903480c02c80341c0f0584e00c650410718040540c28100d207801140c0100940522002404c820701701c0100c40901401403180206120b20798030100c01581007101a07441c00e000c01c2d0408001c2500d1402030700f080d041c020719031048800344d03030f690311884042c0c801816100780c5200cbe680c9801d02102110f03444103102821001d10895840803011314221401600904540e070403603020981c0e2241c00e20940103601c00100240c21219000d441320800104908944582d030098444d040550000b8281801030001006102d405005200d50041500e84542c0c07003a0820400781502c44004141c00b0095005580290707620f94440c034006060180140480885400c00c1d4801c0e031280344c50500c002d0b40000d00c641d0018403801e03250041c0404503016600007024003903440d41135007080645440d411848400 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 467206330 1250 467205080 467205143
    0xf02160e13170d0b0901060c0201081602150a0204031103061b030703060e091b010e010503060405060a0f35030a0c0303060801090503030411040c09150c0812071e020d0c05030403 78
    0xd940c0c21b980c2c0d25000d6804541703004000f800b151101c2e002688070459800c040380c0040d4540103464001d001100031a152400c00c9801201140d4040340c14420f0080e01c20000e00038880a4000b40111b0034480800910440a01003480010200100188209100c2c0e04020001c08441c0b503000c1c2e80741800b040964403109200c0850030740402c000d44411466101c0c00a00c3d40c40034041c1c40e01032a58940b01c040c8009008010b0503160813407082c801c001101c44005201c2d40081060020841d090010b800c036032021510070000e0000104c511441403000c44d00c01100312034a6102034140340c04030312481d14054025001e0340e40540219460104c48a05008001c030003180b0552056003080c0c1d94a0900c801c010071100b0541030840010342c00d080510081d1054040240c2582850900c0461001c003560350120070382c4013541284809201310306000e03402c2d402c0314104005c4546400311600100e141080203640d1000310307400c1420081080c881070300f4007500340f0440d00a1038001051b00040180e40d00000103c2190500c0d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 467207580 1250 467206330 467206339
    0xf030403120b0102030f16080903030f1b0c01090b2a280b010509091005010312081e0a15030c06020303071202070503040608061306060f02160e13170d0b 67
    0x200315983d0f20100860782980754400100341002e44c007940304900e92140e0003003100c80c0d55041206280c290303002c00140110f21084042c11342d503181540145107020440121082450740410409c2d400d50f80c0007448034045d42c56128640780c4540d12202010200403110303001c1880c000da168901c441010000c150b6042209540401e500c00c200c21031010000307207a41140240112a01070b0041c0485e00d004070403560482914011503050fa052070604004444007070303100325031424600400042554101c00360030b030b02a1041c00c002e606003c1340094419041c50052030381746015a030302c260100601c00c4146c85400703140c02442d1f284070541c82e8400a90307654015521103012648154040050302518002c40348116804400b6508040c9070100a0321084c6014292951102502e1049180100c1324455003000784020354942c002c540d004400a400d00c00388040d10340c000400d02c0c4c0184090000a1200f5421010319807800201d58200c0c103203200c0d41100c0000c01090a0000034041c0c01450782c4c4e2b0054403501c94100e8 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 467208830 1250 467207580 467207591
    0x6030b010e10030203090a0b09060115030507200f010e06060411070c0b07080904020d1d160e04020103020c1902030c0108090a1713170115050303030109020a050f03040312 75
    0x40107403041d1589240341d95209014000744070001e4825005142c2242c54101150011141c41e03070750520b650710844804409901c60401000313040c042c000001809182401c082001341030a1000825032980010303140010003000f9418100c8107020400100c0400e03241e0001c103c110740b81c0c21302940720313036065407903a102c3e6080409a888a4070b81004032052694400005d911079850540700300201d030400b81055820100c01c0c0002d102d5a1980d0009022214003d50300080c50070045075484450f0404c05c3c52405160300138a1050722012044c0b0060f03068800701100001d060b600c51004070041d2103001c91407100d41c002e00b03400d0142202202c1080d1040b61086017514107800140f001124144001c89089403240c1c000ea407580003051040d1130380e00c5d0803113488486629001a501e14402101740036840a11111100c40f941c420201382849000b801051044e5100022440c081c0041d80d6400b040c0a04104668002880085203019200b00c80318040b00f2012242c5074907041c14040e01c1c0b13004010340310203001c0c10072 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 467210080 1250 467208830 467208851
    0xf0209060a151101060f060201020a020d1b141c0f09050114030f0612010e28050703021909092f01022505040204260a05370c0603 57
    0x10525541035a044040602040c0401c2c403045800d0b883c02c00300a8803556071a240450800c0c2c2c111100750140034981c00241c1d07103440c8080020715009403140c2110170402c00c5911402419128010072105541000354038044d811070300d0b24203042034103050b020b421140e420005481402d0b0402c081002815154030b07900400b50b642c40054900002d95043c4094000b02000011a092450011503801070030161003c00c070954542c00c40b508641c0303100303114102c99004200c00e00e08034581c02401c4040301d541408000040000f60350740d658824107804001d10891040d20700500300c030789030401c2d0700080c20340321010703c80d040070381c18441d400040007003121000c0b0300d5242ca039160b1841d81e00c021061200041c3e004004520329405240c141420400c402d40b080d4288401c0000e6598a5002600282405000c0c40400804400010740c0004c0b0170303c01000703e80c0010300c0210100d580440c28440d503141201c0da501d80c00020400603410f0483d00b48403201005100c20402c01032003094009242542d40030b8400300300d0700d41e08 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 467211330 1250 467210080 467210089
    0xb040f0e0a0213091a211213140612010e071407110f1332040c03020d020d02100c0618020d02040c030e19030e0603040f0219120f020906 60
    0x15100c4880f094001d02c0c1082009020036444150660301c0c851644402042e50030005081e840085107a03001986013880e0000c582e0340a0100c80c0c2150340030f9465a181c00c500c0f400c54060540301d84245047d80b00386040400294503010101e6003c090101448411503031960040d000468060302c4182c0010084901c0401c090743c0c142c00c480070140c01c104050000c40d24641000941410340b10060b03000300c00d0410020800810f40280a80f100e100100744030b0355000c8180e4075600084c140e4100090803460000c0c80049040b1048003400d41e50152059030b4044554000b0034440014000d0003500715500544510006078018268021a40316100034451240061000162450242c0d03001c0d6104400c0c1403514010b28059124440b03c802c9410045840c490250b41f00741400014a01d00700240d40744010780d070426034010340030007a600c41102d03c1801c505050700e0707070641e440001500070b0041c000307191210140500c81003245c00802c40d402c44c0349a8001c1e03e15003001442c10240d0124010301c0540701041c000c2c6030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 467212580 1250 467211330 467211337
    0x30509010501050607150f180f15021216021212060405010b041a030603150c1306090b04170708030a0302270f10030b0d12020c0d021c03090b040f0e0a02 67
    0x108840b03109036072003104586d03030010400e01402c1120a03a903a4640700303c06812400c01c8030000d0040c0c006020a81c1c0328100031300f01400c480800c0d0820740c4108141084000c91740701322504001d0744903a00001d40340c00c070300c16454100c1d03040702c20900325030124112110100c003500c510b2040f2030070b0f9070a004c0c0d03907aa4261b0813454000c42c05400482c4100c5103440c1c0c9180c800070055948140002c0440d0180850b030303d00c1c13000c00d405c2a51600005100013400c04005903100e104200203005c1407800c5c07011103140140ca041b0720b000d640a1081804050350a901c7c3c96181040f54501809240003525034504181c80041c0080d07100c06070b22846554280311080c05580c0c101c00100c40c11300d0141a262601410904010b1000503a0007490305040d83c1d400080301d940c40d610142110b26129403100c111100782550b0207841c1c1000c1041441c0f0461540c4480b200580b5141d1503e5210f5000c1d220401d00441c0900d01036406850a4206070340308000401c00041902245820030120742c2421410b02480d1901481801a0b20 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 467213830 1250 467212580 467212583
    0x804151109030f0f10150302090703020a020f032a100f0f11070c090203090717060f06030606180703020909090703290c030c0c01150807080f06040803090f0d030509010501050607 78
    0x3004070212010805c81908075148040d180022180540d803031f17030b000528450041ea081c000103076001caa80d59400790104191007002c1c400f10300071800e19807409501c240c0800024030411281c8298586141c068000300840b40c281d20380c8540900c00b0315044480f04000f4661a501580100d0030112403e00d0061400202d6034205c0d0000008081e4508000c0100c019620203010303032070780d80f2800400080385000c00c10f0200321603200d4800303046541840540380520284c003811080c4a50001c00500400d0750320040da92444501b1304a0780400e035030750900140c009002c0c81c450745400588a104000d400c1c800451110240c901c030f0b5065010000c4101d110140401000ca2001c50f000311407404500440f40c01c03000781d43d001c03010401c0c41e0320382032004510700e080d20740b0345c80f4410303c10b984072105201c004c2d01800028082c0001000600340504140c1e24160f59180241018040c12f20000124420720400d10085003032410303100440d0003005c41e518008004180031038100e80b2035460b2100102d82ca140000407603c440d17 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 467215080 1250 467213830 467213833
    0xc0115050d0c0902090319030215010f0b1614070303020a02100206130602070c05040f0b040501050102010507020d0309060b10021b0108070c03110a0c090204060e04050c07030804151109030f0f 84
    0x20b0b400e107501d802c025407141c00d04660521030351070320f0403240701542440056544a07a000c0c2003004009804002c6440042e0003107500360b03000600c00c2c40358410800645011412080d000e40d107082c1c3c2c07410035074000d0908030131200382405070340380102c281500000c83d207021034403e0302c1c11404105164001c03621a10b0940c5c82c00783c011450308084000c90041e8020740500344c00380300440d80c0d00da5200b0010b02150480d04502c4c882d40d03103940c2c0c2c0001d42e19203845240e00509085c00240107901d8141002516000e8a00c4488207140d0382d10b81000510481d640401250301c0040c086440350109210041d6a50f922802c54102110310715424940d6948110041c6006581c1c230344490740030560941d019900202c1540301307685103204182c40d41c0042200f0000f0303880240800c80b001a0340e04d0404000404140d80442031174090380c1044103010b885072501040f6814039426181014103a00c13503140c920090350707203102402e03c03da04104c1101414000b410062101807400ca045030210b091022a45440c0d4100c2000c007000d5 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 467216330 1250 467215080 467215103
    0xf01020a0804141f0b010318022b02040f0504051006050108010603051e071d09010e04020f0a084603120e1507090f080a060b0f04020c0115050d 63
    0x58901c0c0004002c4408032425104c004219801c000090b0240d100b8a4240d29140d804002d0256014802e0010741c0405854a0410381d0702900414020158142002440da284d1116a00d0035003907842c241d5500c41d40100240601446000c41002820301920240c845014511401c0d005440c01e01c01d020440345e041e1143c803503a0b17280450030740c001e000091403601e140300e0701051504103405c0001c4051250409840303034142d8424585000c07030b15040d00c600490203121500014001c2594000d0f04aa1056049420414a0958102194410388103500007059446010403030381d06040844121042c03103404150783c1c0c240c2d0114011994103204884410090881e5421240c1c0c0441c2c0308a0080c0510040c0d80004030700000b82c42034092409480e8006040501c80110034003203041c0d40101e4800081c60107c54403071400381020078180d214069014018030169403007180742141e0b111441e01c9801414000c0086403501310b81c01484c2d010b001c54810b9103200c10380c502c1020805103001a002c03510903402406410701d = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 467217580 1250 467216330 467216333
    0x1030b0a03120c0305190c0b01090c0c110a030f0c050420390102030f160504060f0216091b081014030f0a03090e0c04030206090d1b0b0c0f01020a0804 66
    0x740340548490031350030410104031211040b100c030344002d80c10103e9542ca4024100c801e0400121004040e04002c05082c01d201400160b40e51020320b0104c0c0380c0d0010140701d9072a135500b0010320a51007644c002805110b18502c80010b104981c1021002c0314030903181032000d0344882c4180c015041a100b4501d00d0300b801401103111200d401c21344114038082c3c0100d12100c0194502d00c0c07128810b180c00c00c2c80c0321a90000100040700c40b62140c0075400c00c819130200b040300480c56801601c207010368003c6104104051400b081021700c20003000f0710b5008916107845407140c4510f82c0306c001c6c1000070182c0c00713146d104d0761444160601c504521442080c4d1806a14681400d00c0d002d00e140c2030051440d154103100349801e10750b40325000e001051a1030311a84842181600c0c214500c1c1d810710000384561480c6c18107100420260f100c5a0440d510304c1c80071140f40c03e0b945480e00e07041c1030000d4150b0142e01d0f5403010900202d141143d140c002c3c05d0030210130040302c56548216017018281d1007075000c0400016010b001240 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 467218830 1250 467217580 467217587
    0x30803010e0a0f0509010b031e0d120b1905010e1801090c052101030308090f030f0c0f07030b070e0405160509030f06090a022d0f0303070606120201030b0a0312 70
    0x1078121000490101d403c4940300300d80c409848003503d41c0c0c0000c2e503603550440d0052400b040210105c4035240840c0d6003220708290314540340d20814041c46d082c001e403030460034042c043d280c8c00146c280c2c2d0020038405150072005138240781100c071130090341c2c0441c48035007a4120b90300c1c015020a41c101800e04016403d40c2c06c141a0078081c10210000300140310301400000c20402400d480c810401501d0b400d2406150325500b0020444100505030760740c10b402c003806610066501004503000c1c00d118441966031815041c8100d480c107292107051001d02c1c00f070f01c2c6002c02041907401c2468003070b028a80d80ca082e0b0440f00c108002c106c680c1079814a40c09010300d0080982e060007140a0001964001e09541c50b4119581042c0c1c1000b404440180c2c1d1030b00030300c01d444214680a0340d1b202921103410403110700e000c222050510580c04240711030744130707414082c82c1320fa496600304215203c55a200d103060081c5591400b034403054082c044d5049000c44d042800c000c1c0d0b64145624a803003203e800150f1408880752000007074 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 467220080 1250 467218830 467218859
    0xf0f0105060f04050604030b0a1503210c230106050a0501021903051c020a030f09110411040503150108120901020303040b040c1703030403120204050f061b011b02100603080301 77
    0x18042c1d070078480040c003584c0340c3e00070780025400343e41164124a0322030680b43c102d8038003145502405e0444007040c00030a10f00d5141c000c00703500c41a4400c403910f924040a90340c1030400c1c0002020290002c807030102c4107141c06184a0b5001040000340720082d222420005041002e02815006a101d004031440c40c0c0040040042030038040c0c20030301d02d08178002c50074040311158115207c40803a0001400c8410640c10b10840800c2d200380c90040001c241150350308003a540110401611031919010403030340c9008c0404c02c440c002c2900800719140e00c0c1e640c648110306540b0901c5152005e0040850741001c444a0f001207c1c82d40005030701451541d038950b60f5041a5801c098419141101190307800301c0c2d9070011410790f60004400000844e1645024035000307244007000700725000311030300500080000d9280c480780c0701ca280e4070490321651a030207400c002000880b0704820310701c00c41d801d001c0e0900d1048200824940c43c0c481c035509a40e042c00203405400c090710003602c001004038000b080108205aa07010741e0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 467221330 1250 467220080 467220097
    0x50c0c040204180509071208310e0c031e040302010b04020a0903030e0303030907061b06090303050402040f1b0309050c091602060c0418050c071b06120504080301030204020703090317120f0f010506 86
    0x109200d0030300c02a0020040d0b1040090181106c607601448ac19030400031441d800750801c400646545005800d01513100b01101d8640340692111011504141c002e4100e60350a0001601c1103454a510070703c010551a030034801500418220860a00181004004ca80c4202071107402808003d2402404680c0c80101c0500380070500001131103030001070b03645c0c02454903050195070086064141070042000b00e8036901041c0d9843e62030003584c0e6000000706c01a07d180114203042c0011181054141103003021000721175194490b40740820882c44c0a00425003540d000b05a80c04c6070360640e07420f180c6035684e100d507002e030020103134000394130f82c29808080d000164004051040b290400c211075907000300880700014554650f80032150140810b552251001001e0300b001d890138866070605440d8001944410301000c0d001d15000100301007030600415041000316401240040ca55159900114403508240002c04d1a100d9440c00f00d03030b000c980140319a00a00f0040745100007a41b0381020404107134000d1b000e = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 467222580 1250 467221330 467221357
    0x43203032e090207060506030303060f010e030114040c0f050603090303040b0c0906071101110705060409050c090306101530150b0415080408040303050c0c040204180509071208 77
    0x450360110707000101140c00504020740c0140e103d0788249801825104020401d030300a60082c0104502940c070310805d61354840c000e00748120841c1000000c240589007290301043c500341c038041480704016030602142c1c21181904111800c1544a208002c41448250b4126005920510110b03000c1000e081d260354101c54445107039807509140401041c01c6412800c004d5070b01040001406080e944c0280320092010102000381800c3c904040c0000c00314060b0380103c81c4450382d900d00081007040ba000450b0720002008007112424a03100c0652003500f0325a0161381c84041411026600e00c5002c0c417412a94102c1220341350346541107684625021003011884640e0880e1244d0881d0003142d00388030340d60702829000e10856a102c0c107180c3d0200035043d41c005c10004000d400002c01011814070b030240c400381d9074103141c0140d4840845400c1d03032520369212400b80d072041c070002d4001003101e001c0031f0300140000f881102781300d03070340d1a5249d50f82c40c0e102c14411103040400c030140d00d400046402c001010582070440 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 467223830 1250 467222580 467222641
    0x1e042922030b0a02210106140d0e0a1223030105010e0f0616050708070807120c050402040e06010e100503060112020408010513050708011b110a060504320303 69
    0x440307160011005a580f012515070014450744101c00d58502511039018458000415514292008200024061042d5401e00b400314643c090400a030704001c0400300c1c15000c42d00001110308007907120031118040c131008070722540754507142ca00045450a160440c3c01d21041d06681c070b03000041d00c0b410000701100364000d409840c003070802d990b00d0000d030041051441c42d550400035240781c1180780640300d81254590b0360103401c040040060015000c002d84405460900a542c1d040c601004480301070b07080300b94454004503002c1741521100b010a03121358000d03070300c00040c0d09030041072023030040603103c503000081d030200009480d6501421b004503010384581c6005181c07580c1c4d034030202d08540042d2581d0030508440140881030200170414603005d048460002c01c201c031100c64503003041054540c00c080c107018901a141e0400d50050244c142c1680c1c002800b80300e94941880c240c03d1504030b20f0200c84110314107040e6200c001003600310314600142180015031841d100c1c115552103122004040d1252065601c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 467225080 1250 467223830 467223833
    0x6031a221509051009150c05030f0a0902060c01050103240b09240402180f1c0b060d0b0709030510020a0212030c07140f0c2e051e04292203 61
    0x281302c0c0f803152602440340d0913030540c0c1c0c1d1850b60702620319810f01c0301d08011081c27007885141304108402075013014206a000541c460188003150f068010340842c1c40302c95203094000400d0105a41c9800d40034002004180e511108410101c0d007111100c42000b5081004800092843c1c600d003c0740036001c88000c410f0240c080b130007000050a03030740500d1300d0351316001d1203602011607810b10840c51100d5400031030314080c1300c0350344081d20320011204100c040d2401d002d00d400b01e03081d0344402010f2800590800c190310300a01d05004041c1c50100584030841b014881c00c00070015008161003612020040c035030251004107051650140c540e00080c04041040c0d808004d085c000488810000ea08940c01401500c070a100200070036060032104100031380602628101c0024194410004c03240040d6115042c03040f1240000040311103003c0d01d2007034060304d1002440c40752589042c034050000c880034080617142601202c0030741180c483c8840f04100080034280301c40a000b80d60441881054001610710003400c1307569 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 467226330 1250 467225080 467225113
    0x605060609130f140402101209081603020f1612050705091e091c0f030605221b02072d030605090105070c0201020d0e0406031a22150905 60
    0x1e0302e603900d1100c1d543d0b08601c4408030705010704070b080d1103441300d2000c0c1490544c010408040d0340c050648204056040c450781c1c240800da110310703821500507511a49039203810b004035000d03100c401e0b800d030054460850001d405090000304e0009039842d404421040c00e10380700000903444102401290303240580d5101040d1038880d55507503403051009104560740b4410401c550110394002a01c4000c0701d8209040b5480d0400700000c00021040c0b843c07504440301d2401010440045c2103a4104030b0f40321565480e0512903a014044698002119400401c202d122020016a240058141c4803002d0781182e0800c0101c5800d82103000c20791244050030050a4000c9020000541c20903001200c0543c4d03210144804040e0900c54a46c0c0310945007481003c410301500044d541d8400307845404104450031030b4282d8030307494941001009607400840c0c006410402014200c290034115002009070041c5600300c0a445007824001c1d40c916040403200c485101c090204101400c400802520b49114410000c1300f44c406 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 467227580 1250 467226330 467226349
    0x309150c0a0501060f12080901081503010c230403020307051c05010f061a18060d090605090c04051b0403060207030905030d091a090a0b160503030705040614040b070605060609 77
    0xb040d00001101d6007403110b689104290368002280c400055001100065201c42c01c43c0d500240c01d0811260742d07640c44a40040713001c4c4035040740f80c05500341b54070360b9902900440e007942d041051101c50411403c800d08804464081d5100184d4075034002c2e0810003850400d0002111304a2000714078614840040c0c551078255001650b060307044694542007003101e4405003560004250030340307040501d407540c01c01c1e10400640c429107105120301c038001120202c1c409154001c0020f19407001c02841307a85003603005180c403403c0c1e4111250043c0c2c2403400007809461054060481002c03000095818141142c86003002174124000c100c050000d000c1c4017045a82e81001040c03041000c0c4d83c0c035504c00c0c501741510000d00240b56440021000c20601080302c07281d40d074000c1d01040d01c03403055034641c895024450300140c141e00140f0103040d0303001c00018410381c15031000c020419660319403a19021145500300c10800f86c400d511621003114018010807000810f2600a103801541c0144180d045c1300c00200018005039 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 467228830 1250 467227580 467227583
    0xb0c01110a08100504111c0e240c0a121e0501030503070501110a0509131b1e08010e040b070c050607111b01170c1e030a050a0b030309150c0a 62
    0x450700401c100c2c4014030404000c0207813400751014030006d0754070f201c1c0300c446d070007101c1801a8040d10300844804480080e4440803a019000d070440d85013402400e402001491040078401050f1050380000341d00400303a01c12550204003664440e8441b0039500c800f00028010284000c0391031011040d08511b00b50b50703000b140d002e14081c0300070b1580d801035854441d007100c00803111444400c2052011795040342e0000151001391a0941b00c03000034807840c112942c000e20b805a81004608484209202240e81c400c58000010082c0246c21902003080701c070540d42e10400344141003050141200190004020082d10341e040201ca0510001d04403040c3e85544c00e144013100c104000034402c0e07074542045001004000d0701400e006032520b82c08001b20000070700b00c4038850b0441800030034030310101e0b1940781c070070089030807882141ea000d905843d40c010a00740301c0da0003038540300b4440f41041c0105144481d103104806440800800452070462401c040c8152107211184102ea008010b11021548110501070300980c103 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 467230080 1250 467228830 467228837
    0x806061c05060408090f0a0515070318090902100c111c0c0603050a1d07170715170603010b21070b13030506070503070507031218060f0513020a0b0c01110a 68
    0x41800c80240440b8562440800c7e104601400c0300b00710030744401003c54611071000040340d40e5400c0f50708090f51007041145200d090600300140024403042150f120442c0340c1d2084402c7c9201c0980700400b112021020000608841042c1c20740710903c4c541602c2084101e104210200b0741c04140c1c0e150880384100c1588841c003c0781e190b4041001004c210f11a0941228001c004401c60761525045155609900d0250000c5000b191007a16140301d000c01c03980004120b041004a01c804540000500b0035101000c0505040c0c80e04000c25070514040c000c50f01c44100107411814118404a442c624240c01541c0b2000f80c1e000703039103002c203003d0b55400091448041a0303410307146c450b10b1450601e00e4200e00400c903d01f0044103000f130007100c0e0344c4202120f449a0301071403c11039480d44603020300c00811558003904910030780325402e0020401e158004800c40f203090f41080049a60300600c0441c80c1d003502078002d501c850403c409001a00c8401d014180080c0c0c8034000144001b8000c80740b90a0340e01c8410801d010 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 467231330 1250 467230080 467230087
    0xf0c070b01060e3142080f030403020102070603061410110d0c02100302120a0c090f08010c08010b04050609010809070509010b071541010605040f0506040806061c05060408 75
    0x7030004c0c2c040e04142c0034039402400480d4a0f1050010b803418503420394032204000030a2a060200002c07203a500107820b1820036a541e01d044c840e9040e030703203500510049016000d00321b400201d9501034071403030341200c20081030360003200205c10400400081001c14030041c08621203200354024000c1200c5440c5c483d99450700403d103009401003010340d40c1107400032402c240c010055402c548180e2484660003000381d41001c81e032029542019103103040c442d001019440c4450800041d000c07415046211a40020f880c1e0b6032269880d0101945103210f540940d5411000800c540380d83e075442403946682c022024411340b00070036240d6001441c5100d003a400150320050116490301409181980d408200307420340420030154208003400d4140c1001d0100b0010301c08c02c0c54203034914400102c102c20821540384401ea01035503848140180558000e4040c05c1e460f0704c420720b0042000d040900840302561b04180060580e5a0760b5020000b6041c80000c2100821005000e0403000560400c411070255200348841501d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 467232580 1250 467231330 467231419
    0x16141306120e031b0102040306050f0402040e06060102120d0209130b0114030106081b0903100e0c0303040506190525060b09040f080a170f0f0c070b01060e 68
    0x5400c100d80d2841038146801d603442c0206100004403030050841c0030360b8020b28089907280600a00032940081c02050614040248a4240d004614844c1d403003120104600c54075907440c1703940d4010842e4440c0c0903034410006003500c0c040140c05820b0000b00d07510003503d446030020103e00308014040000000544a005e40b0710f0541c1c201c6507141c12806203100c514219803400174010801d0740c028001c22040200c5140c41004644030b00304032880e0f0036001e4100c076250761281507020002c01e41201402c0d141d008482140700070f0300d000300c1242c080700c000a0000d0b052a43c2100002c80b404400f4000380c050141c20001c440c81480070309084289a0700210030070903441c905040c101c3c103403020740040f244100d0010013084000385e43e00198522954200b4000e40e103c0070580d03000d40ba41844040e001614039903c80802c540ca400061500340f040c55104044199070310341e800000124090118000c0c240c450010040c810030340306507900c44a01400070221810a400403042d11485000940080e0750444106281c05 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 467233830 1250 467232580 467232587
    0x1c050c04081c200c01030911040203040b0906010609261f0906060b04150f031e06170a02030a0f08040306022a071401050904060306020406201516141306 67
    0x2014480d42000da00483e00c98800d420f4941c0103000c2d80030306243e41e48046405000d419030141c4080040504115034078101410413481300c0c0012517954950f44140300011619500c111301ca5400c451642d9109808000f03948421818040e10144440e00c41c860056010f40040003040d0342d08080b83c000c036000401141ea401c260055503056004001740300b0040008009001155121410444461078181056405241c040f400b502082d41c15500c5035101d290300340788100603603000000322100803074001032200f40c048010392109511840a98035030020b014050128044114460b080c62103258500d05d01b5842c3e40d1603200302d801c104030013002c42040c0c0c81c00d044010600c1c140c900c90041c1e110014100545050300085100c926a807409041060119014100b034440e9044800a10761060055485a485420043c070310f0107082180820b00000200ca807c1d500b078081072507420090f118001c4e03030003030b0364420f03000d103800201100f004d0404c01c04460511100b84120040c1c1860316102c0000c0000707a24121004 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 467235080 1250 467233830 467233847
    0xd080c0c0301090308280501140406050d03140a0c080d0204150c12120902040c02280203030909070c0b010303080601110102181009030804291c050c04081c 68
    0x6a010341c3c5019541800b094226450a511a030380000706a070011041c2050100110ba00214100b40f505000004c51036203014842130342400380650702000843d960340100440c0c407000581c0a0041903444d60500c4180550000624203a15941801e00d40c45e00c41d991008240d82c000d4154506150f0301050a03c0905441030b0606201d0b0041e10b081c92410481e521141c004405048000c003d20900b108002e082d140d40c1c2c5c1081c4d0314a50010030400221801820103512605040c000400340c010004000c00d00311140c082d0140690f402a006500b40b0080000784900c141c006005031050001c941d000500241020400702e0103140310b651144211b0a1090000d0700c110f0800544020785d90050004204030104032199010b100d0b012901201c2c451030300d180c1540c000300541c00141441c0c0d00090041844121080759000b8003a1540e1088101c1c0c0e81941c12000c1c1d0b026250048004603100c01840001044640015403c0700e1081e0545145c20341c0c0744000d80c41c10107c40c01820b0303072030340d40b241036840d85800c128030 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 467236330 1250 467235080 467235103
    0xa1701050103140c03090106030507030c08190f0b13060504060b030606010329150301060207061b0f060b0f03010204080a0209060405101a19080a0608030f0405060906090d080c 77
    0x1e001c21240e1940f0800c011600600141c00390601100043d682c00007500b080004540000650b6056a201e0070183d018400902030451180710741b002118000c022001402449034002034520110b0b20755031758401c40124042c15058030103031400600c0c00030690340e05c101401503105590010300215154189420104005c0917681454904040c18070b400110a01400601408030f00c07421420001c14000303450440c1105550520103404400401c1c40b0303400107040300540c1c2082d101ca56102c0c4054410101a1070320507030042c25190781d000d400e00050f5658204024440b0001d281103003402200380400d08980040d440091258451103000c0c055080100c08943c21400075507041c0041e00e4243d1010440034041d00c40d13802000d4060440130100d00301601520540205503d202049814050004001900540e4428201413800b000014544e90010880300031041e007586c400d040928103410014a42c01500d444e0b50130040821480e07540350350b10301108040f14803814005072076088010103c1d2030035400540 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 467237580 1250 467236330 467236337
    0x1428050a0507021302072406050303090a060302131e05010e0406080303060d1b091a0a23210120030c090409020f100906030c14090f030708030a17010501 67
    0x4000d1510303501c00125044180c06031402404020916000002840b450502501c0c0500f00092044050b0002c070f001111803584800501105858204060b01c80c8200c040c225400390030700c102001110b0103034001d0400c0d6680080b6030141e04e603407122542c0720402c00d207042034102150b81209111960b0031281c042c10300d03401510f040000728101040d650b641d00c00508010b209650100b0903074100321106070440b094800081002c0d006036650084240034281d5081145500c107020f10344041b04d400c03c80a80030480f00d4090500ca0710403200d002c8902020070301c1c02055000242460f403040c1451a403035088a025440400004150000107030303220b200075441c003440c0e800e0103080080c40a0340b040c58082e03601e0f00c0822540000c1118103840000c0c007001d903014409030000f042c4a000e1210036040f04c016421505582c03400d2016156511085480001840106c400001c4c10b00405445041c54024031340ca282c000340884c1c12a68a403950300b031a42d0410a84000080c00c608100700d24000340d6000240104400e09 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 467238830 1250 467237580 467237587
    0x901060807120602072d0201110f060708100302151305150d2c0105060f0d0201140c030408030c031c0603020607170d2c0708120a142805 60
    0x251210900e05140d0b2001d490b050300840c0c14400d1108030030080d0840b0040c4001c03075010704164010720f40503840f26070b41a0301089200b103006100c5c0c000800c109841c0c0d8034880280a0554400e50140c2e01d0070303005080c0c00981401e0400210058481c0b0035030100322a10a0300e41c0391601c6002e802c03581c2200081d04000d0107502c030300c0e00b040d0000381c40d842520444000c403a030102f00006000000b000110030f680010688030104008040e4816041d0b00150044034265100c028101112040c0070110341501c0000b8002111071000321007903904d06000e0140c00c61004141d0740342550b100003a030710315000204405095040001e00c0c2c40e44030b014540104056944030300c180041c51071a00001e18074090031601411364010b42c0541182655081c0441b01640310691007042215583d0381c1940f01400042403800d0100150a01111196400940f40f0100d0b0a032000909805000c1c0e100c1442c1c0303070020812380c8180440d2200000c2002e00034009044c00741310f02e000c0c00e281140548041d509040d0501000c0c0103001d401c0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 467240080 1250 467238830 467238839
    0xa03020d06020c03160615090209030304060309080f03010e091c08150102010b0a06050703030e1b1e030a0f060c0e0307120503070515040510110a0e01020a020a06080901060807 77
    0x206600c00c00603801c1800161030f150300c2c0644074158829440410300002c0a00c66010800c02580e010443d030300b12110304071550390345507014181207114500f00244d06610500040103010701c603821081005110314a00790410900d41c1e030480143e0130a8001000c155014010000d014804002d6070309000e09031024490b88485404004c1c0160002405110103000d860b03060041a034000d401480c8000c001416688140c1d42d41d640090440d000381c00c3c220b000905200540307804641c005800c00c900e003001104100201210300130451030260f43d581c20f00042c03000c00071034205e40d601030100c020345900031904503144c2074140ca007079411921505190350500000f00058541d9031000122101910122141815a5a9541403692850060006c005c00c0c0e84a025040040c14446a5203a8080c070311400807690f00d0301042040101343d4a0310a000020850700b8404059030741c2c8500a0b4800d2880c043c0140c8401c0602900818030a103255040400800e0018050000d811024440e0a00802100000e0501e15062 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 467241330 1250 467240080 467240089
    0x210402010c02121f05090c060414060307170403050d0c0f1e0306030606150905090705070219050405040609020f040605030a060c030e0738070210030204080a030305150a0302 76
    0x1200070f40910f0741c00f0b81c80c86000074100214814407115074100090141d0110b03040c8060a030403220401140180310b00c02c0d0b802e05008c03050381c05a03041d0000c0100300b840b0040c01d120700750704020400310400c43c406a84107407403190852034a010358040d549896588104005041c1601e1103103005004001ca81005241046d40c008003a44224500034070690503140d88510450242c007850f040a08158988040011400d01d4000c1004141205840301c0c00801e07962010030803421411500040400d0080102800516000120300c0c4825030100780c034030b06980c48601050446a007220300701d940695441e0030305d0552500c210100444d0700222014410641041d01094031004080d400605c03054a45009485250180e00700d00707000c0c440c41c400c8a00c0710341d85442d02c0c5000721030001043d441c1105c0180c2d04038080310754003500302078121303207880300c3d152040c141d09000c10040b6840302042015402d10020445680500c1800c800c40e009950214503401e10300c60130580c10b07e040300c0d0750740705804408007040143c40c4c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 467242580 1250 467241330 467241347
    0x30e0603060d170c01020a0e120607050a030e100c200606030c0402031e0705071202010605090402060d140c1209011a0d110a0b03040b130c1205010213030821040201 72
    0x18070440d2000f02d10001d890f6200c49010f0301140c1005540041649011a0341c04403048d0003c0d14204c0307555041c00e00e024149501d4540035110200051010049a174643d8060742144100d0031310032044901da40310b88541c400881e00c83e840040b0001d5440c009520009a0b110701d14068600c40070f001d0015810054006a80c0b20042c0441500854010000441c00421250200c50711100d00500e40c8451a241c400105698841c4508444074217040016214544c030510070380c8181c2d0005004a0b195485903020460b007900421261050152200b4020680c000e0150a141c040e10004e00c00e44c0e01e45145400034140c0420050812a00b0b0303141618001500401c8006000c84090591300400c032004141070045620607200c0c14150002c2000c04000313560448800214422400750005280c6a00c46203285050720352103040141210400c810140008074150a0441c4580d114100052912100340e0807445103114503842030384c104001092481e0360750314280744580700103841f2000341500c2c0b800d680003820000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 467243830 1250 467242580 467242583
    0x3070516080c0139050303040302061e01030c050f210309010f17010e040c08060f040b0106020f0d051305130c0f140f07060f05040b06011107060903110d020a03060603030e0603060d 79
    0x4c07102218254503030840b4030101d0a1981090a490342c902e014240a5a40c040964054424801100b160307032900f04c020404a05036648003c0421280345810200240c1d254101c110561204450301a1500120346034a9100c00d8460f071000346403100b80110000d003800d00e041082c94288104030b8448010a408403558505641d41044040c0050b11035091500c150011908444001d105a40601c400f80b920543c04c40d12503846605180940d030789818003241c491212a050703082c581d002139030541c1200e01510152003008240e20180044990311b00020300000354480080c1c8030075641b40d880d01c0c50298040c04111540d40d050900d01925644031113404464424068030501e5508089031a40070000950003d81040290800c2400181442d0a100c441140c055803950301080e03003a03400e600750f504081002000c03140c45495a0b00c4844c9541c44a0040405500100f0b6000e004005204d005903200c1201d14041c50081000088250442c68046c0c01404002c466901c200d00600030052035a0301c8076480810785 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 467245080 1250 467243830 467243897
    0x11060604090314031905220b09160b0c120307020303040f030306050d0303020d0c030618091b06020307030905030c06071e0c080d2d1103070516080c01 66
    0x10401c500742112980002c40d00324422500000c1801008501004075001400703071170a0030026034072541c84407801c01c05e4110300300d05070382c01d0010034401003181c2c0c186240d44155241d085d102c59410703000482e140040c07246c010041d103034004a9011182801008120810000305100a1541c00c11081c041e54034000200000c05550340d01c407103601054402e4110301c0c0200800381011841d00800e160260183d00001c8808030b100e8038149503482c03030f540709020b56801c13200d000b0390080703070885201001c0002c0c02d400d0300b0a440090031060f4011200c100f10907000008c21091f0701a40d152242031030b00620356000c6900183c0700340d0250039460220f944800c00c5039121030344900b00708284064542500c116072000c52002c0c103c100000c02c005180700001c1190190035105940300a50300398004030307842d001401001d0840001c60b80e03a807a50301040c011070000e00d0f11815041280d003062010340d1000d2408001840503c2c050720741c1042001001c4003000002070003c001d0030503450802c0d161f080311041c1c855084048540f0b = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 467246330 1250 467245080 467245091
    0x304031109181c1107050f0d050111040902090a0617070f12050a020d1503080313050304170304060801240e040e1605030c0901030809040b01031e140711060604 70
    0x1038005800b2416840c1d5800070944101c00d40710400b00c680031010b46521800314034a0110b002c0d00c0140804e6620695400419410030f04400c20240a0030f41c43c80c0301c049980759070300c414400e8064800360181005091250026a541c071300c920a020440f12036a01801c02d016401c0d205004a81c82409001c0d0f0110483c03801c00005a0245411680703a00c2a055043e10039103080144040784020b0340003402040f1030f110040c480004007038402101440c1c24840940b4001051000c01c00b0000005185d00e6154011412681081d40302e40380b03a452465032022491701c130f1b8400182080a1504140c2642c0101440e0203601e007014021040c591100c401c0326810360400107400300090556031268800e14810048908403180c0820500780114101110700895109108814503000c4030b1628090140c140e95202c01000d042200f10414440a00030b620310240c145030f22101c182095601d03150ba03c80d030021a085010424001401d0800806c1e00007070500b2041000d688640c09a003600000e65581000080d50b00003031 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 467247580 1250 467246330 467246341
    0x303050f0f0918010f270f020702031b04110712030c14160b0105120709181e060b0102030306060909060d120807090803070f06200309031b0304031109 66
    0x241445505071141d4415501c682d01c402c544400c10001d81a03840f5030b15149416a100c00300751050340300c00e00e81d42515006c9644402c501c00da940d000050300c900714170005030810103141e0002c1d0608a25048198441c925401044414074180c051a45024140c0d01043c0c0b83c19a10f0b103e030300c2d00300c00d4414040103043c1c840c0c2e80390110902c201c0c5035900b42158075024588032130408540c2010068403643c15100b40b0f04103030011480380b500040c140c40c001c110705c0003002007070710b0800010080d1070380325158801d2103510100700c1c0114070f64074001e030023981d80b43e00c4017154400d0921f41101180d03600081c0e541154402e10800416484010880b1510039040300c10000543d00c0340c0004130780d80d86418005040441d035400b154402c40d00001c4080c0507a10989a039890030f501c98140b07558a014403007001c0c002d01d48050014022802540c0400400170032020409803804443d1200355007035109440d151065800080d003250048821800088804200c0c8003841ca07113860360301c80000b80401060341511902d03140300403a4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 467248830 1250 467247580 467247607
    0xc0f0a0603020315100c02130506090115110111090910140d0f17190c080f0a030b15090310060302030c15310e04200f030a060504020a08070303050f 65
    0x35541c0d41300510b14400d640410a0083c403c500a0800f00d029020540445180c000107000c0d103442143c01801c21002d5038a012031004603003010680da40700b4001411086040c8003420b000b9203c004c2c11404400d81c2e1103e2410070f000700f540006140b042c07101c00d110818400d840c00900c01299030301080380c0a88903c0d1041c106004c0c0301641c0d02c0028544050f41b154029400e14503005051003070100e440003c502031900c20b080d82c41d58520035004001040400002c24585551006403070003031154600000d01240c0c0c82c01040030320034070140302da43c4482c002c0350707030f10161a04008075403030f02240d030406000244c6154046951880342c19121032040260b490003035108a845000d03a1044c05004000c18000824648080c030f1034110002c010301045140c1d034011840c04203440615001d01c0e80030100c0c4141134000344007155000310301c0e21080d5203d0040030340521940e604100010400303025001c00200750800340704100385120b480d0f104811940003114208040b0303810405071101c2080540100f581c4400258091 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 467250080 1250 467248830 467248861
    0x9060f030b28050d0506060607030e100201060f080a0f080706020f0f0408012019090f03060609151505091f030504060b040b0a0303050c03040803040e0403020c0f0a06030203 76
    0x190000c100b11441000d448145804007180010040d500c81416198003e002c451101000b02030480e60100010403194109070000305401c5009181c5400b140000c40700182c141d40d42c0002c00f01c0181e444110511500308240351400041040000401c5244d1265481e1410100700100103003001c0c2000c40d42c5070a10030540c04a0b04001c140c109041e50311070001000484030740040c0121070181d8642414500b4030200e0304e2100221a55029115082c09405541c0400f85c2c1c20520500d402c01080345070000c1c0800309002400d000d103100e03000202c2c85904000101d42229000e07401c2c030401c040542d004100300c2e88031020078040340303000e071808a40d598101d02c0452800850610304007410344101c403030703450716651603840a40514456102031202050a10800090390003409a46a00200e2003004100090040000348555031604064138206552903103a1411600701e82c2c00030341a103528408100400d0360500010140002c1143c070500d0003a81d0340040b03a60120300e80110800d0540c0000450a01b0f04282540d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 467251330 1250 467250080 467250101
    0xd0204080f07030b0106020a170702131b03051005090f0c090d03170708061302070f1407060207060807020613060209030601080c12010b181f060806180709060f03 71
    0x2222605038a1042080d668101840113440984180b0b00100707080784003290310040f00340c00081c2110380d030440e00036141c41c0d6444410101d0344000700b45492070044401f80907c401011a19440140c103000c1c3d004064103560000b00b0200070950400000d020950314407a226800c40f007903008003c50355a40c03600e00001d07840f42d80861a0300ca0704c038a019008155001c6003034980c84554800600d880d480d101015908e00d5000d0f65802ea01103200c40107d082c0750440d6025005550045224000c411015150404d414240c101241210341080101b40200303901002a60002c291034600350481d441c0401000b511440d001d0a480420400300b01088140310040d0140d41e861800113082e10407550703403491400ea403000c1d1441241d0242d0b40404c8801d03200b140c1842000c0c80c155010700600c2000c03100216a100321100140b46500c0c1d503140c0340c206035581010300e1144001c0d01c017903150008a402c1c10010000c00b14a011400c11000c000c400410005a81c4000700390100e030a5820490310203084501c00b9406402032661 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 467252580 1250 467251330 467251333
    0x11407111f0501230d02131503051c0c1a0606040302060c070603050106020c030601050d02120604030507110a03050a12110d0801050a090c0f23040605070c1710020d020408 75
    0x1250740780d903115036010314100d40d024950395804261910b8003003032104152003c5940200000445005030804001004c96032a0600c4002003001c03000707400d42030004040c1c000303a415602080f052030000010b103040d059480024200400134200c03580d6030400d41c000003072003c04000080b6021441c20788404090f14051036000388400e844950002c0495030b903030070300c1c41035a000a080c00000074410b800071441c0c0c400060040c01078552030b801d000601100030a500781c120b1304505100c0c4417400c1c143c010700100740150300c243e0303500741d1b220141d00304880e544444080c854800d0418500c1000041c01c00144c10a0181d40b02503041c03d2806480c105075580c4802c2d003140230403801181d00005c400d41e03000c0c0b0030350305807601140c620058944802901040b01e244400781000701340c2042d41e0452007070003140600c058030050240b42e504843c0e80d084c0c01c852a0000e40c0318001044007c0380c10410842c1854500018000c00d0b8019400700c43d003500c51a603124083c1090002c0d46900280000503051a5011500074004820 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 467253830 1250 467252580 467252623
    0x90d15020409023006060f0c1009031106070503240102100c02010605091312120e071805060d0506070507050c0901030b04031709070303030e03070b0106030e0c0301140711 75
    0x1401c1d030107501340c2c10032450b0f110300d00c2e04898094507103114203103400345c2c4000c0e00302410102c1c60000303400e00c2e84c84480c00b0b1000e807241c2c40b0300b042400164024061454806d41e9100e054001012900c0d1500c030f000340c02a01400000d000700010320080d00070010800700c0c010300c40304c00c1504000050b400c02c0ae83e050210740c400d040102070303580c0d41d40540085085904c04d0702c240c2840d9807884100b181c0e6410026001b010500d410668103500c03031040c50503684481d40300c10009a820619001d151910003642d01c845800b40c0f03409031119a00b40140b280c01d074008010b40d1030010464042eaa115241c1c00010164070600c00041101d5050190402c202d005500f0060401d0b59596105d003000207000c00e0844040340007600403032050a40204270806140038205840c02807003024155075080d40900943d0b0740d560007034401070001c840481d495a03812350080c000c07900c00003503940c00e8900990404a4106480380a603060140d06a08641854003c40c1c0c002c1c0c1620300b28085080800c40305041081a2440380b8606c0000b9 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 467255080 1250 467253830 467253847
    0x18060d021218071212030e070807180501060c0b22060501080303011401021504020d14010c0c060b0406050a0302040b19082406030307060f0204050303040305010b09090102090d1502040902 82
    0xd1490307080030055800b107034442d507078aa111320b00c1010010401801c2e00300203401c0c280224026040b4444610a00042c3c81820341c4456000f45000c100364080c240c2d4280c256034948006580f0300c6113a02410352460903a6080d6150384598604040c054018600e541d00103103441c141a4008290600740b0380d010500340b02550f503914034103980c1d0704280101540c03031400b0141003800d90700000300218401e00d03110080c2c0756680c658080080c0340784030070b40641d0041820590034169400c02e102e00701c1d23005280d407102801146181098022a43c090320524000ea1808209014603525031720980102c0364121800314803034481c0400708120190180c40013007403d90004001c100714102042e40f420750780341303071560306940345402c102d20305002001d8940d281c161300200403680214070350340c000c0680ca40e040c503405442d080c1d580001c607103140d01540c01035800303035514001c4200c5072810920f41504192518006e5082180d000001384000b40495402001c0003501c00320440840001c0e01a03900800300074000b1901c82480d03 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 467256330 1250 467255080 467255101
    0x7050a1b09020703050d06060c0510020c2407090f080705040509070e010608041a07080c071b080d0201050a1104051002010b0d080d05090d02060c0702120d0201020703090602010218060d0212 83
    0x41060311300d81c6c0c3c1c20040041002482045420a190b81050017403042d09401c408038002540922000000340c014000400040b0100b120110011891020f02807140d10380814024651300003600005030074910300c54100090480054290b0541b01c08490000f49a220044201d00c2c020059001c1c0c944000040000144140c102003041d01c03d600a04955030b0010241c04034003e4a102210300102065865000c41c031100c22180192207510310540400940c0100880320a07242c0342e041d031000206601c60088424110390a008150304a090614240300b01d90070010256054000d0340a040d0080c900da65003a4041c0313200b5001025007241c050034840d040d007002d013852400ca60044124011080c01c00000c10340c12030307001459000000704ea0b400380220f034039a03000f0402c1e00d03441000242d80c80ac00000c3c994828003014041403035900800d800042c0da44a141c038001d8400c811940c010340a5901c103101100150303901100040365803004803840e1303030f40d0200c0d506140003e004414568100032100c40070030040c62203 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 467257580 1250 467256330 467256337
    0x307030c0f2103140304020d060f06050f040509070e070917010c0311090312180405010909030207050306010e040b040303020c0a0f0212030406140315091e0c07050a1b0902070305 78
    0x10002890401000300c040b40902d00100940002d002490281c408400b00102002942d00a44010201000c840303068907050140c50328041c49d01001560389104000d2407a00b108031718100b480940703051289240c2101102c0e01e90b81039110b00c80c0e0240820700090411841100c01401400c000301c0d5420340c04a00c03d4201d8002d1040c084444007003840e0062800200c8949802d407018201d00500a2480e00f0711894a6100c64100d071031403a001d8082000042c50694490041501815421000040c0000f90b4240245402c0595003c03500035048040140700310703402e54255581c81038100b02100300d182c40d1071500720000d118000c10200c2500404080008000c280180c1d5a6118002c8031380303010194425544170344a100314401c041c0410080510351091026107005103070302c0b20b5040461183d40f000030b400b14401203800c0392440b0309042018020781200c020010101d40125421712094240081903441a5035291032030b002800c00d0625001c0d407008002c04204604c041c0c1440704040d512104130f8135003e0002d40 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 467258830 1250 467257580 467257589
    0xd0c15110f0f0d0306030803070c0302010b0a031a100513090804030f0f0b01140d1103030d060b03041202070302010e1e100c03110102031b0706150b0d14060306070e0307030c0f 77
    0xa80f241909642d07120340100001d881e0411a19440e6441d5420180d502c00070f0075108034155501c0307002c00c0b07495540d143c141e0350045000302843c00341503001c40988400d1403001000982040d46100c01407046440303e600c2440d006240800020f032284660601c40200c3c01140d2009185240381c00840042040540ea0703425468031400f2480d5180e600d0b480d020140390120b51607250091103003000c05c0045031142d00d80942d100000f40903245003c002840103400c0d03a106804c0030312082400818070040000c0d0f820001e510f2841440a07100e03031801c40e40000c000408124519105050304046942c042c2074200094500c03180040000102d107041c9403015064041400055001c2180035144101554040c02220700c140e00031181c01c1852400011090301c503402020041e0740041d5208002e81c40000340c014980d01038032000c07041a86401090202409403121401842c20b01d510700400d002254500003101a08500710342004400280301c0340100e442c162043d07201401044809000040300c4001d4200c010686 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 467260080 1250 467258830 467258833
    0x804081006091503051902040906020f040302150c060f1f080d0e120a02010c0312090c050f0d0b0c0313050a0c080105010f06091e0810050708060d0c15110f0f 69
    0x740d039000f042c1c2800b0609100c0a4456000355403600fa01d1400300710b05500c51440100001081c90340b40d200c0b0310880c2c003e403000300b090300c400280070f105618101d805103400b02050300d074241c0380c031041c580d02c5074440a01801041801d00c801002c41c01030b1801c5607880c102072444102c000c103000e0b55088025500c0c4400c1200202281d0324400a044d9414404e8a4440011000005250025a030760045a580b0b981602c140c0800110f0b100040a442d0740740151089a401000b1100000f424681003103c03a4241c9100c013403140d1101c241c031030b000600c822211984406000001922641c0ba2400c050b0045038006c03008201e40036028041c0c04121070f460160b025103d8244c0208880c1e038a4080010500196003d40008038440880070804e403019880e211084000740c41c400940280c0c0c60002038a0710030308003d480d421544a07002c00c02156440107190368420000c44810a0582042d16148881d0400e0300400062401000f40360150741d000d5214001115002000c1720045485082e5080d1144c0352003030f22003280e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 467261330 1250 467260080 467260091
    0x30307021005062e030204030b0414120a020606011808030406051b0703210311281806030203060d08070c081b21120f0a0806100c0807080408100609 65
    0x183e00f011084e0450003440c9102040a50101034000c040f240d048658440402d5001c010100000c0d800744500ca010721702c07030014041311040c079424042c03c00001030412040d40100b44110310f20b10b50b000030604d802a07000e0a2815221000341c07895080403002c1e80002d003140c4000180000d800b580413000300b021059280c0000301d01c0301300c55202034540500d444041c1c18140b03404018580c03a150805610701c0030400b4180004c8c901c40201c40ca26150300000d020352108070f14410701c29008250f03011120300c1d0500070303d480204120301c0101d01c549498240100000c041c0e010002074400d85440700c003100da441d001159643c071040140b80040d903940b064020f4050a028a942500341014404400e2a071503c0041281880494403007800140022542d51155144035400301d0380e81c050702c5503004084240000340070710394440b144007010b444008040c2901e800380ba03108445082c1035510411741141d040c3d10840040c0e46854906004500d8025a002440740f4020a1502c1ca1000003175030008040b1503007444140103 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 467262580 1250 467261330 467261341
    0xc180503030a0c08030a0608071401110f0601060c05030c03341703070203070b150f0108060a151e050706050114030606270405010504020a0f140d0c0305030307021005 73
    0x1124000c0c000d0800103c0d090754507400010310000055940f00d42903036000241155500d018501c0e04005da44425000c810140c900e20300e6507403000d09200c0840e40d0300f004041d11484550304507560401441110304011115406204120062046918071010081184d0301c401c6403030142900504403800d02615811200d600c082440801100440300c59003002c2c0c0e840721811034002d04162984000c0c40203045010820085000072903544805008280700501b16144c03498000600a11003492000749041c403184104201c1c1c02c0c0d41d106004419284444407410072450000020784551b890072410f40c0c481511503021a640981c4a03024205240c0140028040e9998401c1811014441d030140c603034054000500007801070606d040c1504001000749400c03c401251490036000c3c0c4142503c0496442c0d44800030311007540307880c001e2400504222614031484a280041a001e00d914000710513001d40462204c030780c01d0109020714240250740110075030f640c038070305030b1402900c03403010101002ca00d42c901008101d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 467263830 1250 467262580 467262583
    0x20901230405031c05040902090a03120305011707050609270403022b020322091820090103030c020102150103060e06160f030f0f0914151302010e040f0c180503 70
    0x18584c810f41d890f16860310381400b5400380a036200c44400c1e0f4005200f03000010004801805d042140300281d9000905541012151082d240304400c0f1115a0f81c88128103004a0b501e501c1101c60303d00084034030601500310100c10040c003100e881122002c0c200502d0030402072540100c0c40d804810301d50a21040d054401000f1303141404800014080103034024004c024bd40c2254000340b003119a041140000c5c003d60341d40c18102583c02000306100800011400da00401101903010348140ca50010300448990148020030052141484081e00300000342c41c3c1a001c4da4020700c076550002408540170500d546e101d081210260021041800f007510030400040c0010100d80d4a910040040790f5480d00c6030140350f8000c070090910228600110383d40d1b108400d00c1c101ca03d200b4510310740c0c0319200c202c41517180111201d040c840e02540701c0341500d110a0030481d6409881c50317000001642400c008880d001404003203801011202d0341c00030100e00d050407008031150000303c1c1035800038001e02d000000544640905 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 467265080 1250 467263830 467263873
    0xf0f09030803010302090a0b0411040e0108030f12130210081e0f1503010e0a0b040215030606040b30011505070b01141309030e0405010e070e010302090123040503 71
    0x9010081c060006000615040e4800343c1c00120440003c0f0392190b21000080c101c90301220341c107000c008001401c000c0c1050303627113440b0700400408020f10300340907840e05650154415a1150030f0100310080014003140705801c82c9451042e00548103000304440850090291002644c0d454011442801404842d0040c200714034820082d030148000a501c03080200c0c0140c07040d540a00d64107540355580100c0301c030410807002e00c0d020301540021107241068010310429511203002c000f1503080410400540b52600002ca41c111240c000e0026601d00301e80c100342a92643d02c030013107a02c80c01c903042e01000d0b0040c0b03040c1c07003410b031400c0c50800c8044d1020f801040d40d03a8891940003c0502400034010001d0107852003007035007005006400d030f203114003409080b00c084402c50380d0124041007201c0341065071410144649805080c0c400c5001255080c02d030805049042d25101541c10140c0000704d0390466407003035800345000c6840034401344580e100c05400e202682c002e80501030280c8a001e081941c4c680151084 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 467266187 1107 467265080 467265083
    0xa0b060f090c03150901030807080d06030b0a050709080a0b0f04030e06031006030c0e090a0f0f020705011a0319030c02031606050c0d180501110703080304030f0f0903 73
    0x70f071007044d121140150740582d900100500c0000c1e03a10b8112003c0a800c800883d80f58a06000c560000c2c080c1500000d00711103010b8140301c00e03400c40d904254050390658403518001d0391030b202c00751781d2a00014000b420414030100032820303c0402c0c1e42e00d0b0b50414001c4c0f07405100002054013040c03980d032054414100b42c040e030850411800ba450300c00c0503076051441ca441550030441c14001004c0312005440342407242c1d035420913016250780c0c940c01a241c0c0b40039036005540f254038504100d40200504000c6e445407002d00b18984000c0d01c0c0100b40d820584800300c80644400c41075880456040d2042c40341240c0500c43c403000c544140c00d24540b20001084c4569540303035500002100c141c00d220074a031301d400c244281da0a04124541e40c200d11001907680070300e0700507030701422282900c4c40e06402d580050304e00030001081c00117060344a01031041c04010354590300340103c0018002c54038842507120 = true := by decide +kernel

theorem cover : BRFrame.Cov 467086330 467266187 := by
  have h0 := BRFrame.cov_init 467086330
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 467086330 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 467086330 ≤ n) (h2 : n < 467266187) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
