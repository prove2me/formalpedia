-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3276
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:11:05.465677+00:00
-- url     : https://prove2.me/submissions/d6aca3cd-f0df-49ed-9caa-d7dd55e3e67c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 589028776 ≤ n < 589208633 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 589030026 1250 589028776 589028779
    0x403240e0601060e4c1d0d030201090c080d030e030703141c020d0e0613080901031a030106030302010e0607110606010c1109010311011101090b040206131d070e 70
    0x180c004000d078940c440143c4026000c212040f085c0101126440719441e00704400740b803080e2202007072840220000104500c4000c880345000401d041718500100d0300c01c01c80d944030f603e00c814001740f0102c09040601d03811500500c2400005100c0c10b0716107803240620166072200403168040d14030a014140d01d0700400e01004580c074011070034560700740d0f4043c01340e030510168462001c0c40400e02c21035401c810314801206045211045540d0100207a44001420360040340d02c82d98400c91003c6400301840309004103513160400513140c1458200401100501003a02c0094559114581c80380210b0350288551001103109400000314080000301d01414000020700c00420f115410a02c080010b9001c24044c2e4041001d20300324807854851714040380820070489c021904541c04800101c01c0050851010a5038030f42601c5910840e4181012603090354252080206032800b61380104005007040405007003081c1290510b46002525030ba000ca03030391011840800c141c204aa070900c07c00c940c01c10140c0390250ba0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 589031276 1250 589030026 589030033
    0xf0c0f2109050f150f0d090507090615090902090409080f031510170a02160f0b01090905101a0603070309020f040c1b061b030b09011d0c0901050403240e 67
    0x14040700240c02204444144500350384c0029110000c20050811520b000000c08406c110140e85800e04580d140c40f24001c84194510301040428490006103001d1100b40c2c41c1e986034031207907040c20030900103500072241042d0016103031010f1300d00044854004d048205440e407002c98a0b440c06811043c805c5154004550082131514901c42403960701c01c0c1641f40a5100b20b040f1b002e15260140c1c814001d1051110b5420400302018421080160845210841c0c03070040c000300f6010390301d980d01c46040350303c03200d40180f060b40808405142a142078000303220400d81d110212047c620210003049882d84101c808000181c1d03100300702d500310300c1c01562000b5800340507070b4200035050005d480a06850004050854000d02c2019184104501a00000900544254840c082503000d1002802515500703e907103100d8010400081103012180c40611040781c00012031418a03140c0722481c000079440141114100a8200b0010001c100b5515074120404029007041d401c8140044014007103034605802205180c1 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 589032526 1250 589031276 589031299
    0x17061b0703052203080c1510051309060510030501111606150513140c070b040b040606030501050c03070314070914040f050f0907060e010f0c0f210905 66
    0x4120416a95216810704140741e80760b0b0860400c01c02c0441c400400382d100c200c0080003108211010010f4a60b0107440701c21606c8902d8400d40c0403c00420071140500042c00c00d4808001d249480e002000389280c000d0b4001946200d540c4508054803411900300702018100300d420401c2040c00d121b8210020320b1490100c3c18070380f01005c140000b0041da000502115114071040c190300750100401c070000c080080c0780c2c1d11095171a00310a0050b1890000d41c181c122440800101c900d81600c0840704c045920050414999440c0c1c3d81d400101c100207001a204a5522000400096403d00c02c0d00c1c0134800c45a40300b03440c0d18081d00020240d6000341458030480100c5024410310b6600000b02e142034603440700d07603500a01c8490011a00424006810301d401d0350602e014010204850303019540201c54000540b000b6a48902056601240219001d40010800820b0344040d910405020400f5445400c0200d100d90450b20303042550002140780c0038949403c448104420307500b0040200060009951070034202 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 589033776 1250 589032526 589032571
    0x109020604140414160f05091008100801140f0105010e030d050d09051902030c0a060509010c060e0d02150a0e070905041412040302130b09040f0501151706 68
    0x20700440c40360480d01c01c203480301c02c0c12950380c035008015076550319104002c05151240e003590302810080d11120104d03801e005000102c42c402c04c12150008806480101400d171800c02c01c03103d8001c01414131000d00f09203031001c580b0305403c2c0501c11170f044124003603141509002d95080130121041e8007150520104415405041e02c022070b88401040d000d04215841d443c0c581c03811006002400c00040040c02600251070800080c40240070400b402a000c8405d413030240d00c1403014141c1c0ca4003e11002ca502401500c1d12036206001c0072901c24814040801d000601d5550145030880381c2c8200d20158018424089154080307180d00c0d98006502c0405003c00d0000e9040980c0314020f5008020314070303480b00005000d00050f02c41400680314044202c40c10032260703280e8076034036402c6800100c1c450134941811036000009401502000d10000300b14101c0d80e02c403941e8a0008290b403c90894495486205d004542400031103c00700034090041c010342c144610101e01d40c00c0c040018045070203c0720124006018 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 589035026 1250 589033776 589033789
    0x150303020f011a01021e070515030f0a0509060f0c0403020d080a0f093b0115030513031b0302010f0c02010c030e010e0304052404030305070308070201140a0906021314030f010902 78
    0x2002051b007a0100b5961803010380350410f80d1640100f80c00c08065241c1903012928240154071505c1c2d40b400744c81d010f440780c02501e025190705a13641056070f8044c2c1d0200f0180000a00795540107900f00345220325007a41c030b43c0030071410056160140c1c0e95400124808110a130040e1407072030650014a0229a1541003c091415902104e1911240c2524100d000009403640780b00079110010340300106201c1d50381d1019801c080755286446000060b0410001c035104042480c21348074034562503140d40980c50304610b41104035000404041d405c541d06c609501c183c240c11440f51403072040c969400418585040c80004d0180c4560499641450703142c08044841d1000101c20f86054420840c1c0c04540d000840e1240340300101494409102c40d8000a0f0000c1095001801081540e1007910345250a698101e0186d080b9455005900c1d0507080001c0010385610031070b4400c000345842450010300b4441d004801c410b50a01035008100c1241c04110801060b140c100304c400713a690711423130003441a0f0035198082180c = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 589036276 1250 589035026 589035043
    0x10e0315070e0301060b0c0109023c010302070c0e060f0a0f09050405150703021e03040f060f0204031b0906170d0513080d031b03020c120d150303020f011a0102 70
    0x10003500644410941d50203400940046c950200c045413035041c0c9000c858024684008203d1242c4040e10941000700740c021782220050303001601c00f40010b1040f40c14044404040005241016800c110f51000180c0c0e29888102800405441d514189410030138410070900c0600410f2203a400008100800d0020894210544070600030210705515541703080f5203040034481042e1900c00c0c2c80340420a400b90300d9805040102c0c9240280150084025520080c512080d039007c9e29154075240c030307080403410641101d0b01c4100b0401005281c030b0350f41d885c0c400104038449604880902481410000042c0500881014141c241c02c540c50680f40d9580c81940c1d181403d000c03909104001c1860320340c0305c10342c101ca40014401c04068691007401001d008000f481034213002403903540205091001d081c464800d4a0160034182c3c014180c0c41031040c942d0741c540d084480c0950246840d411100b08000841d07648000a40c86900200000d106000f42c0c80d013943c40040740000803504248002c010340c1c0e40041e9019 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 589037526 1250 589036276 589036291
    0x3010e1501031b031a101a120c0409090f0203060f061c1b060f0306080c0d26070516120209040210020c04061511070b0712020307060c0e010e0315 64
    0x1c0300c420601a00c10283c104070341c40034020040d5801c4450f17881180c40350f01031140381d45402d0103240d5611a02c2020720b00300c02d03c0e004011110f044c42000007150b01c40304c0340d9802612440015080940d144010340039207060311002c45044442d40403550031400d0420042d900945060382c1c80520b03191072000300b01942d814010580845e018101b80e6000c2c03000201281c1010100c51103080762143e1940c0001d0800380544207644002407801c040010008801700340d500040030028082c4510054030749840d003e081c0203049c8111024424810680c1c0f8583c04002001c501e032044002d0549091640804151001550310030306245a85404103030069545800c1164400d03170480340e5105d039900040089203412a40d1881a03000380c602200410031108445262000c003100360342d0003014a41190650b500d46010340302e1140449428080d003c0003036500008140d012101d441142c0c20807400ea10b43c44c041d105e003501c1d200080ba84100d4405142e5a20540303c044002d01078000f8000408074035001054101c00501f06c1d07 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 589038776 1250 589037526 589037543
    0x204030f081602040510180905070b0f0c010504030818070803090d080c011104050a140a14060f0310090c030b1008060d0b0406060602010605010c110906012c03010e150103 75
    0x421442020500402c04641c010307204100c546800d00e000a801500c070301801c00118200b20f8008040d41c4280a840c0516074410050a001442c01c3e80100898100f5211340030001c0c020311071003056890074400d10b40309a0003940c0c1c84503581015885c0c0d41e21402403d001c60141d401c0244284041e010010494100210a42e0071052980c2c082c1071512880c043c2c1c0c2031100844d42005000c06800e407180d000307041034a00440e0076400d00c5590340c40c02c04a111801585e6a0000226203040040225110076038141d440080d240d1494100784444c0242558400c88019850080c0c03104203001c2414144680e1500046d00d00f8100034240c0d00b5800101c0c41c2e40c2d04c00e04603003004400d1000031182e0321007035075038a84950300c00c400300602c0c14245841c2028009500a07100190b1803e000001c8940c464407030040c100340c003c1100609a41c81200b804070b550750040805043c01542503080c505003c01068850034518058400051001407000701400e45a20b4aa0b480300ca0b4494540344421005c8282800c1c1102d074080c108 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 589040026 1250 589038776 589038787
    0x213051203070f12050d14010501031b02070302151308010204080d050c2e09030201020c0c0103050c0324060d1a0919052205160e0c1b100c0509010201050a0204030f08 73
    0x2101d09210b403401b021896030900000030345c60520148400e0698109807020b02c5403100041010707007440700c00081c5000507800500c040000d410410641400ca07000c25040d13500d000054840c1c0c101c00c1e4902e52107441c00d40e5001a0802080400f80b1841c441951186030881c94140301d00505070741c0d1480c503103030120003c41503044072400e03210341c4c1654444008596400d004040440c200a4001d40207034010840d01d014102c0034445942c0319200e1203118074920b800890551f101d11107500c05200c1c01880f00040c1a055448103030603552890b02800c4495002a00450004100c08600c00d043c000703600800c1c02034200720306101d0304040111030a81c154074003030400140c1d5501c0072102c4110700c8660103903003c11810162400e05001010800200030005d40b480d842c40c00e0b54640c0d0762038455000325a5015000820710040038202520205030021445200860340010090700b4200f0440c1c0380316810201040e800141164a0b50b028081c40b5442800341008604161954071001e00d0200340e018007d0010000081c0c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 589041276 1250 589040026 589040063
    0x216051c17040f1409010e07050c0a1217060307180902090403050712050301080c040f1e020a09080c030c010c030215270a030f0e0307030203010213051203070f 70
    0x21101101d40207048001040400c00100000b0340c454000d4001c6241070910215003800514032003506560090003d031891707864100d08001d1060041d1406041003c01c00c903844001c2401c100341c200c03542c05040704083e84014840c003c0c12034802c0e51301843c2c44140724010443d099401040050072191540441401d40030200d03019001803003d40c00003903101401300140001c1c1580600540b4030580304584951105415282c00e0f145c5010910458020742e208050398201400c29802c941c103410080340d004284540300c2650900c2800b0204100d580c0c0542c0801c0c2000c402e640002e0441c000d02c14040549185000075010903142c44254100d14144040c8407540002c042c803c1011000e00c86402c81d450509050800c500c41c0d44680f20303030f5600d00382005140240101c040104071074081c1375041d16001052243c04406568006c8403051507981400744810010250300c081c0005c14040b01c5640c1d01c080130714101420403081d2140c3c03640d6601c1c103520078080e0100050182035008041e941002010000d9000d600 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 589042526 1250 589041276 589041319
    0x4240b090f07111506010e19090911030a14010c21201605070f060509090702010e0f03071b08060a0e0102070c090f0c2604050f0303090f0c01021605 65
    0x750890614130490380c8a40c59020b2002c4140c0c01224241e130781d030010041d088204510340105a5010b01003210840003000005d600c0e41c0190601481350391a0074030000442e001038200034041c0300c2501ea8640e21109800040c038284200e0484401a042a81c00003280b4818080c0c980503199071608032556900b840c41425442031100d600d42e08814400c01c0da07400c5001d001d0b007440c44400c075080710f40340719442e004a00d0004a903440015a07110740d82c0c00d824882e6080411040a8016001d1020b555984100096070f03401400b5100c4107520320402103965a1080c90080040c078488100030045011000c0140900e04002c51aa0f0b0032103042e440200e401d00e01e0010540c0288a850b400611603003152200203007142858006c0140300d40552410072424150384003e47d0b880246030505603984068034851060798014252098000380200e04843c0e102e00f511440514561041d600d8040c0c580c071004202c515504108000c4040310020b202502003a52880c200c0000403031070f8003d45d40718850314031080000300d0402 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 589043776 1250 589042526 589042547
    0x31801031805160905240d020a090f0b030c120a150b0d03120f06030809040e01090c0b07020a1208030a0908070c2706050307030f02130504240b090f07 66
    0x301901d103c89480d030360040c000401c40c45a591501c0c03c0c6800954400da0559011440a200e030140e5940302c4c1d803080c1003000b0103c0d90b180c201c1e0321944241020641135140e10550101d80c035001800280410044201480e201c258010700303220750040101a105070201041d081500b0358003c546160030050401c1e410040c1000d800d82e160010580e040507000c0c507034446500740c24028051001c000600c0e0585142023954510300015001280030403650f509401d2a41c4607242900b000000065080740c9580da900c041d800681c1b04001045000c84c60600354039003c00e40b800141040884440310f2120740c0e031064044d01008001801d400d81e00c049000038860050200c401e42a4460400d001d8262220180d9600307680b5002c1c1004d0700e0510200048005110344071f101c080e18002001000d10354655518500d40210021040360030400204004001e1083d60003040d010300e11441f4812680900f00310400c0080320050080702d40d00e410203803660002e41301c90074a241c002844c2c0e078001c0300075640d02d41e081d149521003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 589045026 1250 589043776 589043783
    0xc0d050c190e04050718030b180f010b09060603011d060406031b06320307180b09040b0d2f18060a050d031227110f030318010318 57
    0x5200360072403075521084084014104440c100b00548600308212502c20900c03d04d8200c0c585580828004140002001640402c00400000f20f051042444a007040088002600b5aa440d1442071855180070760203254020001d039501815903140907070315070041c0c0c504c80401d80410817103c04143c83d612181c00c0380c1c0103160001c0f0305001c02030009420600082c0302d4482c081c0040d020f11403402c0040800140c285145030b0300000403083c80184006036100794006030816061100d45200d038582d00450610b044010111180f90030388454120b402d10080d19110380d400c0f032142c075844040c0400603000004024038804014584210030041c0320313555420b16110108190700540710034801c030f4102da4201d8582e1042d2015a03041030f00030365031030500007480c095540045c081914695035022107001d69101c19503070510307059800c0d081a01c5c45644582c00c02000000d031516410509160380d1820112117080000806400540c80d1417900108001070040d009051410161a00b40c844060540c580303400700038680 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 589046276 1250 589045026 589045057
    0x80f2a0d1127180111091e0306090f0d020105070c080306040605130b0102100b0901060807181d0601090302090a0b010905060c010209100815060d09052e02030c0d050c 73
    0x30001c2040c01e600c0088510f283c00809403006000e6059040c050040c5121807403200d0381c18030384a00104000c030111041e0000f55500c08191044450b44c04100260082610303901400032000da68440c2070900c0c030480c00341820b5a04020034000303402d40c001030f0b10b0445034210054a8036a112040060040e210740d9005560014a0140103690f9101640c072552111509800711039040050301c1410b030a1301c02c83c0c1c030f034541e10440002c01000301c6401180b400350300c0442450001e00c40e558070005041c0c020742c690400070003141002c10315080100101c40c40c0303400c400c00f401d040b0000b9283d640001e10b480401170802c01c40700e440ba403a2002d00d900601000000d071500606007503c50100c0203080d4000d400c00c4181030700c640f941070025000b043c012840b05005d0449058403c1048411200b440f0056102519510b40181d0740c03c1410082030040c017420003804520500140f80d140030403104200995034000742d02034035104105000465110608680304240320728004121682c03040c1c0d64015901880080844488 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 589047526 1250 589046276 589046329
    0x60f010c06150b181c06020703091a1206010c1205160c031202060705030108030f07170c060f0105010f091404150303171b18030304080f2a0d11 63
    0x105a00c0c050018a18407080c045a2140301c6001c01c441c01812610004017000a0307400e41c00800e9040d00280303c418081c1c100715110b03e644d00c0c2c0011386000d8140303400554100106031741c060007000c9075155070080801d213024044072034641c0f00c8020042039200c01e0403e1100c00030301e03958003585103030956416540100f112001c09540317041c4010f040c80c00c3c400c4c0714010701400000900e01070003281924141c0b00100001c0d82020200020031a190384018405c0e0340f2034419100401d040317001c0d00010002501400b02400990500c920840440181a000f09040c410100444820640c1c407001c10001c480b0140f100300001494080400d00810a00c005058101901400031081c1600301d240e0388030006030340390103a0040d40c5040c608811107031303c820041800502000b0380c0c500011f880c1d12a20294400030140c80c50705565068161902000c8400d0f03254941012400541c1c144816068041810728052421003d4117100300083e000c03804d034200103010400c3d840c1c180f001c540f0340c241c1031940c001040e058282c1d80f4 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 589048776 1250 589047526 589047539
    0x30905060f1b0708150c0403080f0c010518031210030803010320030120030a0e0d0306050909010e120a02030705030423010e0a0b0c011503140d0206060f010c0615 71
    0xb940421600c1d030b41114210342544624100164400031070340d240c0007900314001e2103034100f260b210001d4615400c100c41030001201040140380141061180e076101c4a640c0d0307020050360f9094500041c11342880b41070003d14880f40325404401c035a60030301d0100c0c0c00329940c0d03540349610a078110550005080418084008410000b502c128054015035000b010f026241d01b000805084c1d445001c2c0d96403030314841c001c0d201e501d4141c032009941c00c00000c0d80017195241237a210b982c9031034100009400000c3d12403c2c01c00c03c07424101e02c06034110142c1b100a000050000d200e90307a4480c4296040e44894070009071b050403141c42441a5443d10358003509580d0b50b2640e851030b182d142445a022121290b0200390780418942c040c00342c0d04030f11000540384e40700003032421903122119001149845155502c0d204803034140c1034111107000103140f1512802000700001e200c1e6078a40049100d081066600003028058555a506441c0880f01000d2901009021141c0303054409483c14a03098210312040001c0844d10 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 589050026 1250 589048776 589048807
    0xf0609050c0a15050403030e061c0b0a061418030a0c06350c0d0204170607091d01091503050d020a0303110405010e130b030a0b0406050f0106050a030903090506 70
    0xc00030880c1e02d00b441a450b2003803020318900f0480000d01241040200f000001d006e07684900c0610070080100d07040442c624100c041308050900318148031030b91144440c015142003601c49003d42042d10388403070281c059502c0c83c00c1900c82d62000c0d042c038603002c04420311207075810440c0324141540419130032101c0b5602c000280c20b01c1032a08582c9800f101380b69007001c0b800a0300d107159170b25803506040b0000039210141b48088a5101d240706500c1b0076001c006c041102d0b00002c406411003400c0038000c0047e4500002d000f0708a0b40035030085500c1d40c0d03441543c109c0103500e50403500d0565081e00c00001e04918016030034001d00b083c0c0d61008005018140b4100c0e001d40c1c01058401d001c034001d44050010002c460040d40980c451030040b00d000ca40300d1400114241050700d0102d4000f4240b03000003c08060700d400180c03921403140401c071040e0039000100000c1020314041c2c10741190146158803030650400d000035010340500d12a904c10907650719828424940b091805900401e409000c03550345d00c89034100c1000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 589051276 1250 589050026 589050043
    0x1205071a0927070806060d020c060a06150c06020307030b04060801020a020d030e07030f080706050f090d02010b09070e0d0803090102090f0f01020d12140c180405071b0f060905 77
    0x1142101c64100c01d4400101902c04100406018031a02107903100304003a01c0c81c107005851540c01603c28801009414403910081c081e207100c2c0c0c00100300c0d5281003004201640c1007500558000d400203001680300c1600b00350455021544800056181d95a801e8101c0003444801c044641c000e01344600020a02c0042d4001c001611455007600d01804000c502034050340e0021125007101d9025030000c00c0418445101409694071030380c07107245481000c1d290003040da5002d81e0b09900000e1104240a00700381d041141c0d00d2001028002030010b180c41e20001040c11100a0590051201c81440003440781d90341744600e20f000350700c01001e540303900b81803410074005c0d00650480d6000e2074216603201d445117890f03402100882016070042c0700c50b40c141c0344110380401080003250300072900c40728000c0d103034641c2d60300c4603104440b241310301a02d80010854210f5014502940c2d180510310f48010700c1106544410f80031003081090003402d10b240c4107403070800c580d2040280090040740c60b0a000b9003c000740400c81c40c0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 589052526 1250 589051276 589051279
    0x1d1e010b041e0b090105030c0f03160603050709080d0f1b020d11150403020a0618080a1212050702070312021f06140117040b150310060801150605041205071a09 70
    0x500c01e62030130300441c84400e0040c1a810791000c1c50058051078416a0241000c00190a070303554511111890013030040b282c0c0040300030a441d502080403496000c040d0304010100c181c020046101485400383c851102000178104000560461100e202e041d201c009001540c05410070072400c156080180c401c03004038110303600c5058980b0040c2a1000208103540a49400a1203400c03c289019000c1d20b0203900d600b00da008100d4040300c00240d0440500c2800d011038014a520000007a032860014a12030030f82d04032403681031030481441003050303000076644103995100811494640904a00380c1c035003450030907204504c084281060160016a400c44002c03544c41d0504156110308100c0152140100c00e0815031032403d49000080100711070130f681c140c02000f2074130042d80303d040c0c1002107428181007441885a05459140c100704090b400d10528681d44d20b0300714900011800c0c8000100700b07120354400d401c58081608030100c1440030510495004201c001c2240000203000800085070f40c0110034000d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 589053776 1250 589052526 589052531
    0x9180a050c01120e060c030a0e0703050f1c0c0f02060408101d030702010f0c06060306092a0f1a0d0204150e09191a031902041d1e010b041e 61
    0x100b41c29401641302c3c29051001501955540007021403a5400080c900d540c266140d00d48060201c00030f01050014601074005000451000c0840b2443c0c159140c42c4249458508004440c0e4591310114134200e107039001055412648203800050003500854000e60300d03c3c060b140100009070704a910000d45914602c03107015844104145c625181d0050400203800310b04e02120b031305070442c030420012000380d116400000c0c07660740741e80300e0f08116090040c0407107001c100011030001012040c003a10b8a4458038a000c0010039040c40542c0065070418844d107401d90034481d13010300c3d01001e8001501c0c110140440210f44840e900d8001c0007501e88003078080008941c18084409490904040303d43c85500f482d10b0325500ca94003042440c1c0202a80140ea0692400440c4252400d5038184000316115881d8030200c941000240100000c8480c04000c5c0207080c002d0385c1040d26904400305013540200c5442d54007441e030413414134805016118103803038940d1052500d204a500304101c03000380011101c41c43c00c00c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 589055026 1250 589053776 589053797
    0x91e03020613080f130803070309051207060e04020f07050604080318030a051905070204150513090519020319060903080624030a02090a03080406080705071109180a050c01 75
    0x2100b1500c4400b800c05030400004110030380e000c80b1a00f000304240848282d021500390b0365400f0550450b00a180118006140010300f00000e00d0900c13160800f0401c1c000190851901c0d201024020130754446101d40120340224038044d080b0401001d5880d01074004041d507116140c5458140c0c469882220030035001c6141d1404048007200001c2510100440c5803220343c58981c6144a28800d40310408241e010031604101240040c1c0303940c082e461840191410240b185420002040780301c03040007011034002c0d460319550002040c40010701d500141b040c3c0c0620300c00740031540007190800307020900e601610708408012408000342c5030310099041d40a5138420806880311420018401160041c81807800600c024a0310303000d011200a40c0c01c6841c5503001841c04240340b01150404456600a5500b001e01050805c4140c0d00300301c03000c1d0b11483e40d10340a442c003005580c0780b084150102500324004c082c502c0000d2950007a4030600304224981004944002c111032138155915280485450b000501c2e150b407 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 589056276 1250 589055026 589055041
    0x3060c0c0a0b0a0207080d0f110922020403021206040b0a09080306090702100e0715050301030c03240906020702010e010e010f050903070b190824040207030201091e030206 75
    0x2520094404640642008501c50312401c0c28280c000d001c000300d05500300308840004880c14020720342200c8528001c5524103400e10300c001203940c5204400d50355401004601d129695000020120200d402c0d0301c3d80080303600c6080d800c000d004941000750880c8010143ea40440d000140480c410b522400150409030769540c0c1c10b409603411204010540c44051000c22a2840c05100d829440b103d1841103e440301a000e02a0061708d1465014210741d40110800740712180c844151594520340e1030500d1455545076a56113194055039100160034582d6096403401c40304042901100d0708480450180180a0182800c0d0000d60004070100d022800350740c0010325a5010700108580140142c5400c00480380c2a28250303000d42c41324036840d915001e0240081440c91000b07000c0c2455209900c0506084003100401502102c400f405110310090320b00d041e0700705656a0313422100120000d80b00503032941c07007d00c0e059000d01501c42008040c5149401d006002c0c3c05210411f410403030281d403c1b00d081e070b00e0f80c08 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 589057526 1250 589056276 589056301
    0xa080a1b0206220809010305070c2a09050702070b0d060806100503060f090c010e18091c030501080d12090f05030901030605010e09010905040212030d0209310c03110f090306 76
    0x2c10007032008409011880352503001c0d900480e8416107905091f500307401c42d941d995409120949030300010480b01c12f81c000d02406655642e4000d400d5440e130410040c102084082c2d0b50f0103051180d00c00ea440d00003411948959150440e200414100040b070380507090242c1c00c250881124004c1501078030860001804000c42d9100407801422420f010301500300240c0011a001401d226059811803400c04180483c04c14147c41c01e131151540d9005081e2944111820100710010782911104142c05c10006004940c408540d030a480c0d80c041c20408400740c11015040e01a00b840ca0002d0402c2e86c04042107801d2010102c000c1084401c2680c04000903034462005444881100020a030082c9000c801030000709401e0340a20f0b00640001d04400e10642c011018610b9540003184070702035190003045090036030422020101c4400000c001d011508082c415810305030210b402000c1d40015180c5110044060107075008200101880c10760f0307583e41100a801d021280d00000140c0d01910990700050020146c1c1d5 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 589058776 1250 589057526 589057591
    0xb0c0615062a24060325091a0d03031d071a0901051b030c1b010c1106040801020a0302040837020303090409060504030f05040b0a080a1b0206 62
    0x880020019082035082007414144680720410648030711010542d403100b081e003d15549030314100c5100c5062409205041c241008039400c10716403040b01c2801c005000090104c001680c046480004807101c1041c0e03401f400e210307140c00a58004403000c501600f0b040c8c2c5508000280001140098618508030712907036a9443d880c0700c0d55042c4000d030080c031031a551300d6100401c40303804145070940c1800000b0480d64a03034031948011740c80690000441103042c100902942c089420004140384800e08401d0010b000312016400003411240114400300103540e550050b60050f10710390000b15124030354440c0240c000c0d40b16003c1c03510184035000c45801c40000b14a03040d51400d4003907044140c1519880c034448c2e020922180200e9050000b880b0004890300c0ea846180300c0300f4011170700403541c0e043c5802c003d03201c503084030300c10010490100400c2c0107001d400411901e051506150803d0380f036403980c240c24002c0c040152000c9000813014000d10300b59a000900c1405402c038401d40a0345403403010304080081101 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 589060026 1250 589058776 589058797
    0x1e080105030c0111070b04060c150501060503070e12191a131407030204020d06061d0a140a12030206073207020d060e030c010b06030f04110105040b0c061506 69
    0x10b01c0604141d481540341492012848088881541d02c461614046411680000000415801c42350040c85401101440034141d03000c2c0400c819414124000c0480c400102607606100081c44141001e40f640500d80c1c1c0d07106494000e8132185c10100c0b903042100e09010b501500c0c00030b07006007200c007045041c020250048803000030142811185903251520001c01200050260140320000400741e11240000d01000c014403800107240f0f410841c0c0500481d081c2104008080442c20200c0344d1502c90400000c1a680352050051402c241100050501111a007002007034941c0003000034105600040c540d40103844603140d41c074510300091491500c1003128118080120304001c90128414807200c01015094006408810b03003540945401e801d44040300d0860100380e0000030b1411341c0c800207104051080e1400c4607003920314204a0800d02c08164050700103040d8a020894220541e8002d004450040022601154603448403c601c0f0740c40b0581200c100820250601c14807486243c81ca048a840404 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 589061276 1250 589060026 589060033
    0x901121503020d170703020703031b020a0e06121b0f030a05060c0f160507081b060403021315141f020d1d0d05100605030115030813151e08010503 64
    0x41c6400f008107020340f445042c0d940c03280e8040c0820b80510b071080200740c0d5600a80007890420b10b1841e0042210440d1540722040440b44000000140e0316911034000710b44410411074000d8481000180101140e000a086c440c404e243c10112807101010303183d0345036841144ca22640d840341000745510f8007604200141660800000144e14036401c202620100d82c0d03010f500343c1004140750203107500311081c00060b9850f5000c51401c010104c01040341d558046030250003001f29501001c0450418040d90100a22406600d2183c01c0003030159400300c6004c1c1c20200030609010b540c2c2142d40c0809000340015405414030503030480c1c946a44e0070750719440201c82e0b802050924015142118101030038522015060210040c0311026a07845801540e01e41c041c4c800360a1040d02a8040c9007104d0207940310078002d9041600a403c1d0b000c2c24a5030300200ca402c1001c1e0f03640c58041e040d5800d0001d0403038100ca5410b00d9903182d131014555000f603d85500120340c803461220000d80d01015115840700340f24096140e031 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 589062526 1250 589061276 589061279
    0x4050a020301180e0c09070215010b09010c020111010b19060f211e020a0f021b010801180f06180e0106290d0f050405070902040e0402060f12040809011215 68
    0x140d40c020707a103404584c02555260402100080e15076032043d034404005a01807111003050343c140180745801040b40c56803491030800c5020020f80000b0700f00c18060b040c420903001800700b40100790080301d40504010304d070307099681c0342242208113200203008040002342004140b01000303020f2000c98090303600c02290340300640c11100c078100251070710001081030b044111100952a1059001a009808094031003618106003e04000d1a0141c1c14201140e1015914420344259070030400607815100c4d52065180c0ca01c41c901c00080c00380c00ca2540007090245802c600194000c680700452409184040c018840c5114100705a03003643c034540038826000002910000c54104509012082c500d0300d020520700b01492020140c0450750580017030258a5145c2040000708003092100d0780c05020a07030700444c00c040c201310300340c0b13035090000700000d015140010b80201841c1119068400c0d5105d00c1d4a0360007503241603d890000d9400c0719a0450201d000c6d00d01c0e8042c401040c0c0101042d80e00040602070115 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 589063776 1250 589062526 589062569
    0x100903080a021b0105090106090e030f031602031902060105150c0c090703091a160f0801090c03020c060709030c0504092607020d08030928060c030f091104050a020301 73
    0xf54400907000703c2240c5403080c2500e00034020f00404d40f003001d200e000000d4243c5090107103030595039040c00c00201c9410410216404144081c10380381c210046007108410b016020106900d58820700680d0340c050040b03444a05280703540051514140c45042d24651101c0300400c0060b01d0a0040b015441616000095001d08030b0401d594801c0e8000341c2489c011032124843e0b00c54610010300e40d020052125080310412031801c1e164201e01261a08502d400942c0442100c230041c500c50041c0540704580f503c444807071410038400e0701070711003421001047d02c05500386001d002c1d118400c1c900c822550300171118800070711032400e8440e42308106c9d0010500b91001c01440c0515a41c152a04490b000301c080511401c0c01503210071143d40f0203584603403c0d50703030340781803001400c1d01d0083d820081c008551100342800280c04803054200348040c3d4005004100c2c204640f0b002e401819001c0f9008200e54a018061300a01030114001d04c15064180e0742080a610750054120580c0f009001d081c18003991221109800c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 589065026 1250 589063776 589063781
    0xa17070b072019030501050a050601080405210f0a0f02010b0a05030a0312110301060c051501031707240f150e13060608101b0305010501140c100204080f100903080a 72
    0x30200140b60300d403e000c2258000d0501021a001581d1307981d0b645081080c0d890503845029001502400c01c3c1801e4501a903456a84030094444010894090300c6550108410740042e01c117040482011191550340029005141e40014402c4100560070001c0d02003e42c101070341d6260507a10f0180207403c281400c4d84042d13031030f2410700c4405000c03140e64100480c684003c04018501034240c55440a02540090811915002000c0b02140308001244010030018002d520450032070084448100c2c0c48841c503090603582690740e02810a44090307080c1601003084240d41c040c0c009401d0071a0b0400c51400000542ca200280c90b01038411111a01c4001c10002c04070f401244a2032071081d400818081c0d100e00302581000e90b4000c01080c1c680d240d481d0800703024201ea103811410030943c5810002589004002010807840c032403030076410800014030121007101402410045280020305665848d59000700d1075070b409028a40c00340c02d0203550081c25440b03209001c1c08070440e42654600bc2552200c5030070400 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 589066276 1250 589065026 589065083
    0xe041508060c0a0e03030a090e1b04091802090a0b0102210d0203060a03080f13050409170906090a2417070e0111010c1d06071e050106050a17070b07 65
    0x9021a04c003905003681ea0170002400840c1c2d03155241a0103d1a01c200c0035440803002d040c81c403c221f420560042101445400c2d502200e038100000300d8401440e8101c110300045c0400d01039000740360b01040040c00300d410b40010b07000c00400e0342202e204170404514031007a040c40c803000c030718110403c0044240011064010710380020f0005d1002000640e250b4420025074403c4080c5103100070003043c1400a0311590b03120800401042e142400701c41402e68803010041c903407003401d085620700800c40c1c0d0b00e0b540b500c200b078580c0104041c2ca0040400d80302e00c001c4400075080718001c5401600c0c600520a12072241d00462180901c1403500c6d200d984507038400740c6000e80486d1a05e03040007513803895044000780c00d000710301c101c1c0b2040d00c802040384e854403074605e0b80b9040781c1d905030b01400b001c11800c80042c1058540c489056400082c01d0030301d41c41480c0680c098011503106030340c000c4030b168000c28103070361245021251107001c000300d0f09001e540304035040e0786004012000c2c140100b07810441e0080d40e0350340030002 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 589067526 1250 589066276 589066297
    0x220b0412021905061005041a1011030703030f0f060807150203070605180d0525020a09060816050418080c100204060f11340503010c0e041508060c 64
    0x2c608890000c858440e031254038a0030b6806501410500c240c501d158814800500320654090040501c00b0406e0941c5050000c0594001d03610000d4154503140300303180c1c0101d400c1c1d400040d41e40c0e400a41c00e000b07015040c0100392110091a16222038140011885004210390004029181c0782c2e1400122340411074984103580107601041140d10300144013480b03603d2094840e10365045200010b1240f1a103448240c284202c00e00000300500c500b4007080e2100000c0101003011a000c02412500c04101e078640d09501007401c8a050010104000001160b03482c1495102d41c48051401c0d9070780b0070401564214440c00210340701d00d019a4011510000c01080300c44240d80c22101da120350328030103000700c0e4800c0e4880740004640d001c507611756560109281414000c0c110050118400500c800741003600181800000350800203102880410000e0791075005010040c003c101c0138000880242c03d885624801520461601c10507082a89650482c01c007a42d012030010070855130b072403040c840150301000284 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 589068776 1250 589067526 589067533
    0x7080c09030a06050702060a270804050406142407061109120304050a0801200a0c0605010306050114010f020a020108060d020d05010e0c09090d0c030c1a220b041202 72
    0x981e07107007004140001803003400009802d140228000341417810281c51003c4040c01d2040412403d02003528100c45410900c1c0d01ea415080c0760b02e02419188034550003c1e8109043c082c4c000340031200e601c20b00110740b10076200c1080c0322100703200b140e08043c1d10300c52240e010201806040003160856010800783c1500135262071030300085400145100103025144a17081d80002005c0c002810f00a40341402051024002d2240a071a145c41034001a9207801c01c1c600e0310008100e9060851050303003803031180c07a0003034410040e030358690622101928007402694200f10040700c45501c1c55209180e40000340a0583c090b003001c90b100d03030045405103405050740e40d10203c06415100941e95400c20394001c1441500005045980310007114100181d900c0100e02c01e028000070461052001320b60bc0400c413100d0302c0d00340c1080b20f683c03030180c4103041d40c650054003881d16840d012428640da23041c024050060708031340880c40414500e01d85c01c1c070b2aa4003c01461134445901040011344c211040c1101d004960054 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 589070026 1250 589068776 589068787
    0x110714040207050a0c0302100c0506040822080705010f050a050a0e0303191101050105010807091206021315020f0d0905151b0d080c34050f010c090b070b07080c 70
    0x3214070f01244900140ca1140b101c1703000f0400c44c6060301d02c41d0031502441c2080c139410700290f02c03011f4403504000e1021f409039000052040c0600f21070310071220060031025072880965121f41030166500070a020300fa0120b80320002101407580030307a0030b60301e556801d0340c1c4042c40d210700101c044070354468411020707802d48420f2108840c0e503200500c50406100c1240d603030a000e03003040f652640c250351069000c170f81400300034824008025441840f900c10358560000304841700c407543c5020002845000130303042c094050f45a0105008103a40e680091010346a802c81d007000880c14846e580781c07450000f805000c10b060000801150410360000606540409400ea00384504030309001e10400a54035a20020b401403010b080c41c2e46d401c504c0040d002003040071641c1c2480c0105022000a00c0c1c8000a0064418540d012410394914a5000c4c1e0f00d05900c40c0645a01150303071344440b406410700d8150000420404000811304140076810b540c03005030031501403002d6843e01d40040c2d61240d4003416046c01010b04002 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 589071276 1250 589070026 589070033
    0x80f010b37090e010b0901080712140405010c032904060305011113060e03152505030108070902030c070602160c0b040905011d070e0105210a0c110714040207 69
    0x30040c29000500d0a08020031640034002401600c581d0403c3e0340070800b030401440114032103000e450795850207003010714040c0c480c0c47d41a00d210076007001409015050055402c40e82c02d5460f01c5038000c80c4610024048500e0110b402d50070b45010014050741c90b1190580c0030030020040562402c0340d4006813000400c5600c03030315004d0030b49009419200d0008400100940b18000314805100141006d240982c1c0c6d14000c41d0010740c030740040d5001c06900120120200d018086003440c111941c02c46c038507207002006158100a0000c0c0c03c244100c02072802034501c0004c41500500840c0d00c600c40200f030603860f0100c0703031740d805e0000d4100b81d9a003640700b40a080200002914403900202078548500e41071348840c9400c0e070580075108140c00c04038480c5113001c1c02a900c0d1140b03011094102100b81441485550700d200121141d004006404a162031111821075000b138400005078018525242c0901c04d4500c684000d555018050a240034241d11400c01042421140c041c400a055402000540782100a85 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 589072526 1250 589071276 589071337
    0x91503162f0102070302070e040b040b150607030e040b030708030f0714070b0d11360415030b0603030702010807050a1404061e0810030602031e04051606080f010b 71
    0x40c122045070360000d100c0c4e0a0503010040e16000381840070b0b80701c0561400b6980c00c0429100500700404128500740400c0044070340040703070100031001030036140d101c104504005103a41d500a180b180901e28045049110341008030714203003565850030046252074940078851069902c04902070342c00c2d030500341e1180740c00b01060241c84020286000001c2e142c00400592404131500342105211603040ac2146074100d8565212070048500410101e14180c5411458041c881080404042c0e000b46010440402d0360000c00b0b001c0245c85c0a1000c1522595411080c5030703070791065000113400309050400052405114000800360410716103010010304420a84d0082140c0050f004240802e682d01c0c409201d0701c004902240d40140c1d6440d02031030a0500c0c4c403a0080324840c40c00040c00c095000000180d400c4250400300354484034481c1500803d1400f800c18076192003003100380d0110000182030002c2d0052040d41c0032801100540e0000301e2617403030890404d449034050002840800c000c4c01e0508110705244 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 589073776 1250 589072526 589072607
    0x8030a120204270c0905090117010905010c05071103070518040f0215280f05070230100e0318010c050d031a01020712030f09080303090309150316 64
    0x2c50180030144418062101341c40c0e94410540410403007910400c041c0d5100c011550440390b50070410b40b210300e02e110205024018180025282d5803c0a10640c62298007400810001c2e00643c4071a9804884904040d01c6688500ca07881d8082d014400048400010500b03d51300a0f20032101001051040da000c141400c4071050511a01c0b6004510444500c8000c5240b044040b1006141102d060700200d019241c0780c0700c480c09100300b00300880c1480031526010341522040d40c0c0381170207501325100070b00d0307201d10380c010141540c51a00644403015202c807130300c1c01050b0500c013407074015504140c4111219224030948a820382d041003400720401001c1a002d22094040c440c80d0342d4049803e850300d11080342029400c249407811548205401c02040119440150001341d1501d40364410303e0f0b0059003160b50a00766000b02420f40000400d02104600000041440850690300300c80500c0c25285984100c0c00300301c1d071040d04c500041c801c02407428412604082c550307030340340c0012100045062030040c3c00c00342d2 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 589075026 1250 589073776 589073819
    0x613150906121a0601170c0f0c0705191d070912060b0a08070506041a1b0102030621061602030d0603050a050c062503052b050a050108030a120204 64
    0x640001c0801d1010403072029000c110101c800f0809418080c0008040e000300f103562141d82c00f4200c0100b00e800084404450700715954040c513644403040449032a03154103240c0700701c91040713007210001c100f0700350603c099104982405002c201d203000191030341035400400801c501c041100b401c501084070044c070b5441e900010701401740050440e40d84001e000b1a000b0b9500300e107200e0703400004200b181d5030b1220b0840d4103540041406d401d21405015031700d141c0d802030700380380035014030340403403070800e0707000550245106080c00c4480030500c542900e00c140f160303074828008081c46d0b0003280000b40702c5c050500104030980818030440e49001d00c1c0d04e040404503205a0000c5441e5041002d0040912000b08200d1107802c4040710f8031840c160342d100d2071080c0c005804902d80180e0f60000200001c0c5801035065070305102040540d00551031040045000c12040114240c203014039110224480d140703d44141c81c16103105000039442d00c40310350b43c103032580350180c15180395054082001146541c030411031000034220 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 589076276 1250 589075026 589075049
    0xb0117010b03042f0d06150803030411040204061d010c140d020c03030c0c010f020309030a0606150c05340801060312050a1709010e0f0708150613150906 67
    0xb81854441c8141801c42220121030300c5002049404683c2d01c81300c1d030010308040b43d213542182d03d0b5180c07001c09400c3c0f0240010040c010500300003418000130004501c1688140200c00d415250002044120b0040d0b000d400c000985d0b20449071616a001e45465440036014100100120708558550010900f09907a843d41a007015084082c40d0b130b010459550300010440c041c0d41002808518207503501c00743c04040d030411000a4040719543e00078421140c6880024095846480302030411a003c1c084d14810245000e10907081c2c0d090107032040070603044596201000e044508030b01c03c089000fa802111103218525200a4491040ca10400600e001080824004100d9034a14240030103041c2100258400b8090104849034005621a038920b05107003004401d407005440e407070750150051101c004089040c0c45000d0092208400c000b031210200e0700c5070307012a002c105070485401e0101c6d134180c0d002508400000004810b042c820b410004106020b00c401c118a07a0750b0799450b0041d5152680300028100 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 589077526 1250 589076276 589076281
    0x3110601150311070f060b1201050f0106081608010608150d0507060206061e010f03020903010515131e0504030201090c090501061706090402090705210f0106020f030a030b0117010b03 80
    0x40d054002d00c3c81e0503500c0c1c0071090400002e038459141e99008002d000780010794896002c0c1e4955200b050601440c0303401402040a032416840b580c8501e0820f005280c0802c103040001105800c00700d0b05043c50038030035541c00c04140d01e0700906803406040075240039a8650203400d0400d081c0c407011034516503079000d640100000c0d454008080d0a106001d00224010020074403a821000d001c21081800d00e54280f0301a541d004004604400a0050b07e070143e5055081c5010312140124540078120404c00850703c1c1c258000b90145000c00b00c488800e0311107206551601e03105484a034a41c04240e01601038000031a601e40c290b5501c1c091014030760480c4c4815a903400c01032040c0c2e80e0200622148850500a07155507041800000d552104000c0000784200703007800002d10101c5c4a4415124540140d074080140400202c1060100c0d0300115002e90004074200b00019440d8400140180c2803c0c052020b18034008034540114054000760710460b0510100030755440c0402c0003081d005000702003c008040c4c490 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 589078776 1250 589077526 589077569
    0x6032a1915031a031c0e06070602070f1a09070303080402030c03030a05120108070e060f0406050411071a04030e060706060e0708192706090f050607021c1b03110601 72
    0x103052103a40300e406035100104080c5081100c0105c08600ea6107410304001c60140a00061854841d54000400040c00460114104000c4211520342c00344140420a813280c4000c920b000e07150340c2150b9883c519030142d80c0030000301c1d0041d18081d4001e070024090b01c0300c20601d900400e1441e0b00070303100440010340014100f90005001c07030000c3c4c00760110700043c000b064502003019015440c0079209a124010540400303540d40c2c1d865100c00cbc02030070090800d205800701c0f000d0b0005550092042a0345003105220125400c2e51040100f61140754150bc0f0400c0443d4042c05106030b503042810102d43c0e00d6039801d0007042c482d0340e04100c18465451a500c0d03800620702000069048407105860141c6217043ca03030b140c8170310302c8404003410310748035500d0310501640040d00740b08000e094900005403c2e04070001c005070600038042511071007024036408031740c0d0325070318100f0349900d45103000c070b1500001d0f00708214078031340401c1c1c812500307101c900a180c694104846613101504000007a031100280900860002a82 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 589080026 1250 589078776 589078811
    0x207030512011a070303050c0c0f0c1023210a0911180a020c032206031b0507030810050306250905010909020705032106032a191503 58
    0x54005000300c48620200c3c0703001d0070494000d80000400b45500c039070000304c9520082061b43c0c0f2542340e06088600f01031076003603255120100c1d45d1b0107900505000c400382040c6070003204880300c80a01c0b0420000c101c00740c02c4400303006411040240c0c088000703001e005000155020079003800766185c0b41000070340860901d07048203030841000b45540588104001e45040d99903204043e03030321102c140c6c0090386e00c1441140a5042d44190f00c41c580d002070044204540b0302458100100603145140c030200100101c2d8041190204490510800011010442140064401d0010580200c400311100105070f88440c00a8240b007130480d14110b140c00940422205a40040e0646030f17842e4007800c060784410308040000740700800c6402003464142e0009169402c006041007240c100800c62010140d44141e000d854400f900e40c02e0b0780f100c0c40380c4624094600000b800118507030000c10220900d00c40c40c0d084005228100f85800c01c1a642c00360072040000b2500301d0103103c1641c480c40c070b5600082d10501d0001030b504 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 589081276 1250 589080026 589080029
    0x50a060305070203070b100909200102030909150d020a060201050a1113031403190203030702010c032c12030903070302150115080406060b1b0d03050f010b1309020703051201 76
    0x1010304000034007840b15004004c551800d504414840d00580e40c3e131150340c0048075643d00c0704100c82d00d000102000e1280c0f80003032424041d12030300609d4900d2180001241d40c1d0181c240340d154094001804a12042600308122001c01d0300580340380352980311a00026107040603507100d080544d441c1c00401801710301c1403240e024042046080c082c10003002c5c0f044130044c984d00c2c0c0401080031070b4202410800305410800d030381410124202d5824801c035030481c000e4407604240d41c0e0001541c01c0c04056907110f40207001703107003070880031650b1041c2030012040b6900515000c0c40d4040c030399001e0342e400c00ca110801440118030840c80d0100a41d5590014903000f40b174a000110104040e0507400018000718003115402c4e00048d0003454003018a840b00e08141d4000c115039404048040000075044811905100741c002c0181401ca0a44c1c04410055605130b0076101d08a40e4240400c1400d80180b003043c40000140507081000c4001d40c82c4140c4441c803240032a804000300340d0108601198490b080510f0080160 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 589082526 1250 589081276 589081289
    0x210906090302010f1b03020906250b01090603080910030b03011a0a090e0c0d03111501090e0d09051905090a0f0513030203030a0903030b1309110a0506190203160804050a 74
    0x11900c0340c44102c420800d100c12174184101600080c2c074081030703900c1e82c0561305405001c282c0c3c200b09514500c0d01340c80790406400c003107a084000c000005001903403880f424045036000801c0b207182c0f400c9a010041c000307034113480b48410b05544981009050310244640d050030f8080400300f0075029651400c2000b8503c8a034080d041483c205241303c2030180003c80ca2810108040c0c0b0ba25050a00c02e14080e682400b101131102070520401040342454680000030b181250341d801c0003040154070f25080c10b904c51101c24805004251100b10800a83c28101400600c0344a0004011049034030b810020343d004009540d015003060b21458110b103500b0552058a8001c0ba003800300303210b00c2030700380e60287d00c0b40001001414050381e101207060500d4000d4201240b103000040681a040a10321500f40081042d9001510b101507030203c60511030828000c01410b650009150505080e100750110b10345c1d0340b4000c1c003101180000e00c6000400315188030340442861003002001d485908040602c040a0043c0d8000ca = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 589083776 1250 589082526 589082531
    0x90b0609030a08030a0e0303041a06100c23030a050408070e06030604151e0e0c1c08030405010f0617060c04060801090c0e031b15040e0106210906090302010f 69
    0x482190380020b815044030768010036850301c070760705d01000c01c0040014090030005404004108030800242d081e000700c04200d12031f90f1032072a48682080c411001c0100d4602000f00c1d80c45144580418030b80f441d072001c15800b0b0844081600c0c005200d050868100480d85008030300089000d010440051101300050200c070040c0ca5501c0c40c06400084da126400f81000e051012541502c02c80006250000a084001200313a4444020f000011a001388240c0c004080503002e03a000340e048900c1c094055242c50099000510240c0c2c559458501c03003030f44041d1049541c2d660303410200801070030303034020365005140e00071440c10700600174810709040c00d000602220040c50100000e203c01600001c50700d06694444d0400608913140c40001da5003540c0c0240401d915129040141d54104c0c48030420240060082d900300241801a090095441c040c81c081c401184280800603c841031091084000303007160703116000e4920070b00d81c2c4564115001300005548140e140d1000d18107041e02401090018414100704 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 589085026 1250 589083776 589083787
    0x190c230a0503060d08070204021201050f09070f050a0e15190306082d073203030a030b0a0b0309012007050d0e0406050402030108100b100530040c090b06 67
    0x1441440b00904451060040d2904036040c00b113640c01752000241e02500c210b54540040400c0300600748248500b0344180705c008145a968203001c1c1c103d80c02480c80d900c03907810756007010360b080d10386e50005010309080107450021071040c0d030342c0d803640c0e80c4003100080e4403181ea410808500387c4100b8240301c1c90505050a042040100103000207841c0e003c043c548038022103a400300c003802801e154000c21411744a11481402040d1810071818100305940e590001c00c2c0380341d940d0503111018a0503d000326615410034010b070f491260082d0020360845c40c0c0140324500c469141c0c141005140c00c19200062280c5d17541140c8424011141c08000840c80345101250519405a07a078543d9440c40040c0141049030503c0d80b081203031103a40144014000c020401c0d0344941c0c4520011390748203829840c0c1540b15003420a18406810a0031001090795280c0c2d403101e20b065205084404004681e0b81c48100c800311101d040e0f8440128008494015071043c2e04d0100a9850018013030165411002000c0c4922000c002 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 589086276 1250 589085026 589085047
    0x1401030b06060913020a030e0706020a08030406020d020720030d0c02031f0b040e010f05060109051507050c04090302100606080618060a0317030403020d030612020405190c23 76
    0x140c003540204200e40072a03641a0410100c2d2021149504141c4c0e941d001154404502e034140d0065050b0004040480d04807640d1284c040703079983c0341c02201500441c0e041000c507020a00c1da400610b0000d9241d2009031825265580d451304680048001c82c070100c03280c030650215890140440c0c1e62001003841c1c00845064290000b0380c42d1841e00c110066150740d5007100c10108403035a0840200340100800801100301d6903841107020340017280703041c1001031078180090b210f0360044aa620a84002408425a0b1000a600d80019500031401074850303110380c900c1014942e5490040742012442070380030b0708080034041c29003000d484058014105001d01001000020b8941b010046c0c81803100540c81542c0e0344941e4007141d40801d103038001520910804203d800050f403101d000318029482a030880d0840ca101c03140c2102151011701440b111000420a0765015140c960403071034200d0010305202c4160309910714110221821400c803100407600080c8241d001c0240c403000543c4c100c50542072145006000c0e00f = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 589087526 1250 589086276 589086293
    0x50a151e14091807090314012a020a0609030e030615060a030b040e1507091205120c0c0a18140f0103061830050a0801031e15060306140103 61
    0x411406040d02064001480c0d64200c08802c00403803001c010100c80c1410130004009025902080d503440b1801c507400d00000360305105001e20072407802111340300810300700b0303218224241d0f0b48210b00861003288500801315081d4800d0050392803203a1140710540c00c0000038142004002041101360341850290070201b80c580104407180710300d071443c00007108003104000500901200c51280302611809060902e03810103141c1d07143c001d0000d600c0310701301203503070700a4802c0344030780f41c80d008100d50005c0c40da00f440540c070103024003060300d044015103902c00c0705100072800f40780096016440c170072040354411001c019203205030720410302401503141140c80c01f40b007070070030030041884003c12056803480c2102041c403000d07200301c440e00c2d031100119040141400b5602c914400450006100050a62040c11550f01480460744034640644030146143c2c0f86480e5120b02640e150040c020b10f0700640a002d000810310078110300075094110300000c0031802c5091030703011981d550000d03030107450480005001151481 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 589088776 1250 589087526 589087547
    0x109030c0b18150709080f1507120c020a15060b07110f19060305010f0e04120201060b0f070b0c03060a03060c03090b241e09040606050a151e 62
    0xa0080301d154886082540000d55910110005405041c50402601d210000707a9409550241c0c0c400090035220107010f901c400710700c3c00520465020301075481c40443c0c600e09103540b188160805a07031401b442000c000c00c3c0c490b40b4601c600146c2014101c2c0080000391400c15215206c0ea0400300b081501308198071010740310380c000c090202c03e070000d001d4006540c1e0042040749510080e003800c603082458169000e080240e80600c1e40440d0405001041803a401501c490444605c44581c1d0032603140c548903242270340c2008841008654a94101180c0c0f02c0d506001041e2412000c95025543c1c2941e0030400028900604000304c0082d040003440441d9913001e1003e410351b900803030000340c0c55042d60b60a40c001d2440c4507000304140700b900100580e22084000355191344541070980b004841d000c5040000050948442c4070b0f484840c29002d10b82c42c1846401d5035405817080800007000368990000455910f59039003d140311480d641010445a07910600032669410032003248000c0101d40d41000d071000840 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 589090026 1250 589088776 589088783
    0x90c03101e08010c17090a0f06092a06023d06030c12210503071805060c0f07060c120e040216060b011106010807141809011a01020109030c 61
    0x10304100e48144001c10020a000b003000900070488081c034140c0c0640300e050701c506220801d01c0050001340d1118004540d000090394000065015103e19a440c00010501d0900070385114002d18211084540e1003410f801114104095800d80a498418003c0c9822500c800b80c0320780e418221483c00c40b07103d600e401002451038107002580c0d95106443c2d03500041140364809884c56903c10800511451040c100c0c1c1c1e04180540203824001c20900300201c0e41c00d07051030070b040c001901040080c21040c840e00e2000300c6070018035007403102d141e075450005140790401c000b090602e401520b090207401c141081a480101198208450601410b8840d41c031003400c00c2c0c180509003d0720006007000707070340c40381e04488102d180480d209141090605014000b00a26401a404a1109050001411400038403141200c0419000302485400d180f814641a44a510181c0e00024900c0280c03181907a00c40c0b00512400d80940005884200641d0300120b1189110956065900d00428100800c1d17001034980c2c5107540 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 589091276 1250 589090026 589090049
    0x40605090f041a07051c0b01120b04060e040b01060f020607230d0c03050105030714030703060f02130608040209010f030302100b1203040f030b061f11160303080402090c0310 76
    0xb00ea0500f0801100c24060006080710b0742c2c4100000a60080040c000012100c440c00b40d5004118030481e0450305150120360108020b545400308a0f030b260741005500341000f074000720702c15903140c454503031840c020340302103800111100060044980c00544d03240140120710082c0003a041c000c0c8040d00d40ea031609180070b00d42e03003a841c0e801d041e03401050403a800600c400f0800c002e80c6c00c080e40b008000303001c280100b900ca030040c4180001c800180b904000c9100750000c02030030ba05841c1d551004000d149080440d0580b40d000e00400103010688040500200415121031005280c035204000480390140c124040b42c0090742020720201e64000741550582000300c40c0000c0d01d80915000030100c0c0801e940000c82840006400b060036030400195008403441074500c16059102c04040110020604054000448004148101d468482e85d09124880400015500705480860400001000b141c0044d40401e498809110450400000d85984890100300450450821030004030540409100b00c001001c03 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 589092526 1250 589091276 589091281
    0xf0e01020403170903160e04030306051512130209040503030103060605090f01050108040c05040507051209010905030702010f030608150601121a060a020f0105010603060611030306060301030623071d040605090f 92
    0x100c00304407080e08501080400d41c1b040d03555400d4000c100ca42210101c0003e4103020000809003420958402801c4410078103608110007440e151020040060600b0311818a8a9a010241c1c5034210700b507000710b01030740c080c550340d60650412a042c0d0390b407940071600480406082040041c100300b402070640d64240303001c0116440ba4103104990240c50303040306038064a402c0900521030b42001c0149900c484a41d000359065846046082c2203400065002d00b19030400c2150f980191f02c6545006d042c1d0b000c41c200041c1c8151149450f5160000c6c0b0701e0b850781164000f20a00a440da042011300c1030305a040001481086031000d410300e40a1100d02c6040c0c054040880c1c541c54107402400b450701c031404020020445513a584070024054019407141d1000f041c01d14140782d0300701102004591254202900151540c1d01c4d542e1080d0003002007010a10407125040b90348a6092181141d80d801520940d5850007035100e1103108060717032510310031040d104500c0e11804008546802100c103034440b500c0d07040d11020340d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 589093776 1250 589092526 589092529
    0x80f040807050111041a0c06010b1b190b06040911060c19051518150a0f180b1005030714060909011e0e0c09150405130f0e010204031709 60
    0x203000380e5038000e0907942092034686161010b0b81c0904100c0c2c0d0003c2e00503100088552048101c0e00c100c001c06441f0f5049400180419034080c0c001306440342c0c4002c68107200e80504003081d403c04c294200c0c03060904c600044120706000c0c00400c1c054000300111810000c0300342c6580c481580040c080c60141c001d031000326211841d03040c2032001980c9445840b08070400f80000303203072864440c0b1890042240180c46540481e507940c014240103500168041300038030303c001c0036144046402900409429556407100c6010b040017005004031400000030f03440c4016448080e2070481d1101c0001410014085584182009a0b5a000620758111101c0e1080c1c42d001700f007841c01040141c803808141c1600440007030000500c00c001d0b41c1691801d0b00c1c0c040021110300b500c801c41843c841c0c0c02500c0c0392030000c005001d0b4241078501401c0039101c4001074000d51b468a0381d510040740c10001c102c200d6545040d940c00a24010042e94011a9000700612000714a003a045545020b030300030007001c10302c030720080124908030507 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 589095026 1250 589093776 589093793
    0x129041208250c17070f080c01091401093f03031b09060809160609050307050f150c070b030408070302010b180a020d0b0d061d0d080f04 60
    0x5801000400002010541800304203030740901c80150740356410b034042c0520b4407800300e003880480da8001200c1c0740c0301d403a014880918034022003007240305010349040020414901c1c4e090703000410451000d0120400004000360240c50700b584000f0040141d02c0044c006aa0700c140036000340c4414540400c0b000300e4503a0030000c0781c46105c0b0b22078115010362100c50f00318542002e40940b40d03441782da0144103a045190b0440180101314050901060b0049018071215000e00700042d8800700c07500c221400b07510b000b08501014441540f0600104107050301c00c1c8610300381844241c001e0501600d4025203400c0e10004101200b0860700c445403c00804180072030a910700b408070b40002c000eaa491316403a400c1505000105034051001140590728000d804452030410720320320441c2c3d40342d41d0882d4079681c1e20303050036034040c0d4084481c82911070303034520b082001903583c548081d1941e0b0003901c0024a411080050403040307003100f03600741c40592041c028440d01d80e41c030500e500c2d8403520054041d42300d5212894080036 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 589096276 1250 589095026 589095029
    0x21516020409080c190c03080d0e060a05060307080610150504090e0c010e0910051009050306010b0a031d030901050a05070204090b040c1401080c180907110106090203012904 76
    0x10700a05000030380090014210180500b05079140507240c3c1044100c90f4070418205091005154a000c2c1d4010000f08800d98090014940c5112000c1030b10480000a203040100c216800b501e0702d0fa840b01407200c507003002c11160001d000d44034000d2019050048030100034026621a0559018a007581152258403c20664000f000e00311014040580920165621500c090300114001540c989004485240c9400024040d42040741056030141c100801c5c4070021f10150f03400c0081c0070010300c001405480030803281c0c0c000c2401e0640c0d0354403080c545400809661020740d800003060300100040b14412000300841e03454550900f010303903070f90400d10320a031601c0c001c0080103076003c0d1030040c0301d5051089010395144502e22441034450016187d107038524100c0340d030100260004000000060309816011700600d080c07a404101007455102d00340010b442c0000c03c66060000032a60300344001184024060200034011302403056066604045085d200485544c0a605945020710709280000004908460 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 589097526 1250 589096276 589096279
    0xe0409020d0c062a02300f0c15040617100f06050d0b1e01080606120103030522030803070513170312060d0c230301020a0c061802151602 60
    0x901680d9a0384080c0c0303511007600003415040031100d050544c84803029000303010254000c0004103080300081e02440050003000e10a0203008890503080072100c4104400000300b0403140c020200000c81c0c0b4188507840320a1011406015000c0c0402d100da00d400c5564200003001c2c1c0002980c0a81c0ca220b030b811240d070001d5014220040d0041004036909074080300801060340c0000080c4001340c0ca00080c010751140403103148845080e541c95038681907210b41059908640020003150412500700c0b1030618070b16081e40210081540041c19030456105003210b86045c401c840c2c2000d00d0545103031510845440018901070420500150010502a021319982c016000120400320079005501006a49510a00202c0440400417000607164640b0030007459240f503010240c8000189070001840103808031408c4c40aa04104444140302510248042c050440244d07035920100c20541c100501224200c03400420341c5516031a50f0000b5031925224004401c00e2980140d5607610100000d49500500d520001d = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 589098776 1250 589097526 589097543
    0x9130f032706020f070303080105010c0507051e01080f01030c06050a170c0901020f07050310020705070816050f041a010e011403010306051b04120807021c0f0309060c02010e0409020d 80
    0x1400820751a1450760251035064007103403140603405041603507a0407184001070004d048a001030196522412041110a204104031503040d502d4600054460507681586140c81000c444219407a40e031100345d280c2c00030709000501c5044d5045403100391985503a4020541406400160344500a11491281082503450030072500c076410704000789442d552007029040e0041c803403190218a0208040361900072108c0007001003104110140c08507001c2d40046009030f030709000301d50002666860a00411805e00040d440c000441c905141c108141a0540242103000c0d40c50843c20000701c2e011846d01c203030300080909104180d4100c0e1b0300121140717000c40d500b281e10900040000070030080aa0030060085002d60501520f10351940c000348214080d5100d1307040c00c0200c00c8441808540910000c1c0600e90029200c1aa4007280100101041d0031031001202e02c6103407440710105255004038540058240341c0750101144034150002002c221364602000d208036618080c1c8800c40da80d0000120740658004080c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 589100026 1250 589098776 589098827
    0xc0210080103060b10021509070806070206090d030207120c052107060b030d12020d0b040501030f020f01050f1c0e060c0c1216031206090e1b09130f03 66
    0x400c052401e00c011503280341003102c0d44106281c40215800381000a078010450200d148880030701c080c0d00901010218052960082140c0c01c0501c002c034403404d0f46030000c240034107100520501c1d1522581805040510501c00b4500054a241790725402642c82c2c81c18680480301d5003030040c20208070102c64141034000c080100030b404038440190803070324000d140801c180c4985c84149074030b44203840c01c114009640c3c40101101d501c500d9014000e08407100c0c00000c0c80d1290480403e0440d1020f800c00c0d10122509035a020451402103038040f000d00003840c000f801d02903003a000301198003131282c8203038061401d074204101e4000389600c024025203400f803c03108581000130060013154465003603010540901d02021804400500031241c0f00c1e40c17040c1d40f4490800ca1034404664551400d12501c4000d5200e40f4002000d845501603520714440c440f007c0d003011500d84510580440c44207403014040c00d07500c02007004a5814402c0e01d2900c540040f002c02135484149812184030706044610481021504503 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 589101276 1250 589100026 589100059
    0x601180603060e060d020109050d050102070507030c031b0b03130302010e030d020415090b030a1a1201020c0d020a05030901030b032b0905030c130b03070e01090c1e02060c0a0c02 78
    0x71031021214140c2c440d0085132201000d04c0b00d401802e40d07029022482641082043e030402c050b130440d01e41d0080c00018141a039941e10107042c805c2651003034a00302180a0244240710168000340305000a0703c0b04070101d1450700c0103151050200a201501401c3c101c246001418002e4005194030246003040c2ea5403246014450030003900700740511003a81d0f5281030301d1403109000301c2c10001599000c0040c1030850f60344821050103010080c00c0001c0e101218040702c00c03a52103a0076078100040c51600056200c44400d0034041c076002802c0c108004641c050604030b0003150b40030044030011082031034082007490b02440428501a0388210203c803106031001950104190382c0364031030030042d01e80e580160f41542d0f042007603594491a0300c035540c0a40e000c21340006503a031561103001c0b0180060300744c400f083c0d030346c7d652a51201026440540041e0319418bc0c41c000d260700c68800b8802144a080c2e18240021440300256503090040c03180644890009001d61a00e01422011a0841d402014552004402e55 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 589102526 1250 589101276 589101281
    0x604031b0312051e07080d02031303030e0a0c0312050f030406020702031203150d2118061b080d02040315090c1712090d02101d270601180603 62
    0x44140c440d080c1003001e40381c2c414403810803a01071104440344081c0d00b6118100103056544070003402c8070005e81c20412915a48103e0020350302c02c3d0306283c0481c04180282c100078007500c0f10000300c0391842c1c200801f9403001030410090403056a03005600521603814011041e1941d2040d85445005e0003404005c00042000c20307001020060300c04c0d01a0340140e01c5084e040e10003400180c43c0030008002c17520003002c1e203051460442c00154041c0143d80c41c11344401c85030817540344a22102c4c1c400225007022040d01034025603035010041c81149400401480125035810310b030342e150b060042084900040c241c01020003601503a0117180c00024a20000950310580b01c0107051078082114003210402c070025003001c001e501101280c80d07a402034004814040c58003442c0d03512160106034025200c0c0030f02801768840311700e00c041201058442e2444420032101c00800c881e24903141d1f038400e180002c1e03840703118095411030880e000401500e03071101340c40790001a1400d010002c000a54082d69102c006085c03541034 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 589103776 1250 589102526 589102529
    0x140a140601150e01080406092d0b0c031513060f0612150b040b070c0b120613020f0403170c060907180e06010e100b0406021c0c0f110604031b 62
    0x102008036981c12180043d6118403031400a070b030125170b0102c001404101c5076044924114454180c07800c821040030b49910080c0916080161a007050488802c100461410040d8004107010b81050941c500042024601c0c9944840980505031114002d031000000d600058054501c400761a80d16075125400249100c11500207000071034102a80031100314000102c2d407060303070081c0c148030b490a8149a8081600d1380044402c403441201d401c3c0006e208103004002c0c220303a8204a5a9110a0600c0c1d810461401190700f20f000c05581b04001155541c02c0e828100d604890380160303c2a000d8807401c402c0b0b901401500300802c92409403c1c10807480240c04501441520700124440d440c0800481c1881e003160b400351103984a9500240c0180b202d5020090800e80c0714000000ca42c68154546540e01440d8219921080147c3e005030541c0c5140448101e44081901c050328200c0340c00000c4d40c56144150710710400c00790801d240603050783c070789032504021200550b400201c1030b2000801a2064074551249 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 589105026 1250 589103776 589103789
    0x13020406030b0907030513030f021e0304151d040c14120103290c130b0c0102030105091b090103090302160608011d070f0e0a03020a060c061104060903140a140601 71
    0x240c002030142402072246c03074002c2d01d00c41d003003110106066038155009910035608200b584541d102c0f82458480c0d1603d515498180070014584691408890b40040d4000c144180c05020780140ca420f0b0006240c60700408000e412070303011440ea814a60295540d0070700c0c4003003040c200c40001b00007030711b80500581d06040b20310400c8011035450360103610390300c3c0c80c4c440d021141c004a052004100d101403444040e011043c5000d10700c0c640f065803550003e59950180c200c00c4000e07500480100070b1450125000b40d480300010500b021a900c118006902c24070840300e40606040c1e1b10036042091610070400044032020144a00c55940e0b100c0a020f001c044d400d12401c0d003400724181071043c8111400d0701d8140568247d841d007892150080340140c850800e108540c6400c4641d246000015030b503070842980007801d2645941c41d8080c12410300034165050b4211b20300c0f090004020820140b541304400c101100d811038913103040180f001018506140e80f400303000d40f18411018081064a501242144c100d445 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 589106276 1250 589105026 589105039
    0x24040623060f0a030f33061b06020a0e130609050c0901051204030c050604081815030601031109122505010807050a1e030605130207020d1113020406030b 67
    0x20500c10840300e40708450402842c800207200900388280a900150303640b10720304001262121b007124409400441074454080c0792007410240104a1003406510710144c0740c60b160078055004c118501c4400c0368841070000307058075800111001054803401003002c2021006201140c03c015942d03400010740000d0003100b66003482c040200d2424400f51044604066041e1600c904081220b108440002e10082054042c880c015039400d0008009111040c0301d00c0c8070307000346a107500c81e031914401a260301040c464068080e4040708982d4144110940354031079002d00c0c002c2031184840301c0e011110b001c0c1080700764011082d43d0300800c4400d008140070800407002c20309003240d0000c000010602070414440e040c00318040724080750204d03100701d0080c11030383c8103410240c0740c0c2084a0b1184900101114074600040e5682c9028021391400c03841c0310668000c200c005600b029004d1300060301d842a84100146030140c151010f100c2502c42e21003402c400d04000c681151102d58554010340079110540503d0320550 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 589107526 1250 589106276 589106339
    0x27050c1302091201020c0c06090f060f0403050f010501060905032d07050d050307050d05030411010e0d0b04050607080108010c02120a030b0303040e0708010f0305150718142106240406 80
    0x900c02305540c42e0303110040c0204010f50004090203025840000c481c00791034020071001c004280300b00100040c151040000007003661414000800500709500484d201e5000710750b22440e0340340902e102032106a440d03000f21340c88150703e40e1054541503c41c0c0c800d54101110684003824843c001c00074010941c0503606903012606014400c0b1b591f8481103400a003e103e0f0094105c0300d0b54072441350521680405003648008043c1600d98215249085504035a90b61000003000040795110b62042e004280300c80081c880a081590041d4440c40040f9508000e103502183ca24011403083d042000303061405015030356a2030301c52039807580358001181d80c000843c490400005501c0740c5261403400b2a6040800b0341551124403142004444010f041c110030080130050080c0c61001c0c2040500046c48169802c44241402d5003d010b40c6000051400c0c40e180c0c1012280180c0000104945500000f01200800780d40300a00c00a01c8603019180304a4001340760250200303070400e1079a01b20500c401c0c050468400300 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 589108776 1250 589107526 589107529
    0x506011a030702072d24110d0e061e0309010b030a030c02010302090114030c0d0f060e0103020d0602190c1109010803040603020c071827050c1302091201020c0c 70
    0x28401510803900684c4550820010480c44940e813040048103015110f110280c2c4040c04040005542c00400c0c0210907904101c41d403d50340b43c02e200280345a1b0800041e03001c484464243c484120781c0c100e0060101384402501165290421542404070002402038125115620041c0540007120000c0440d880d145450000385000510a4459a455034610f24185e100ea40110040d400c90810310341441041d04011501d000d5442c080c611030503041200a07140c030080071941d42901c1101d11076500851a0403c1800100071407c2003506490301a00d01640e0306245d440d102d4000c0c4982c1c0c0d9009411030801354001d0300a03a1205802c2c2c640c4e809400341c0c03c0f00294010400c20b03103032028803821500e039004120030407496019802800701c0304043c4d001c0d2885182c5d10704007100d01d404001c54a0440c10390720f040700c4e20f10740c500400040b4002e0403c103048200f071070181c1e00e05130307201c148528851046017604044040e00c80c0300e404807047c0c00c00280030009581d48040409001c0d42019015014a000c0d146408409 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 589110026 1250 589108776 589108829
    0x304080a0f020a12030f0b0a06050d0f050417070825020a05030f1f0624030608030f180a030f030c0201121a0d020406030c0b12060f01020a120e030a050601 68
    0x9820a05918405070021801d80081154401314001c1e6512100c00d84459950510417034014270150f2030b02035a032410118441c0465948811480302e0300c2c80e01c424000401ea2561020160706402c142c156a2403499003032201c1c25000d914001d00c078560340714a55900e07104120030340c144558400c0d10708064a6403900101501c6690441070b50909501c04858a414607410072621100005440c500107072043c1c441050001602101d0907046903c004034240120039980340c8181d60061540002550800e00340017000c0d601440398901440500400340d0309401181c2e941c040c1303040110303840b042035095090cc5242c007401c0d6492119060340070945203480c03514900c0c1240200e91403410000186454080d40c241002140b8840d6002640c00598941012002803003140c0070002500b0b80017070580e00c500300d5a9801d01c00c10001003005000e503106140d00012640c0028464000c0c65025000348044045054101c03207160168100d2a81403140000c10001e00102188440c181c135540d840818031962141c0c0038654 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 589111276 1250 589110026 589110043
    0x4091a010c0b060a05040e0303012d0e07090905180c09090c1302130e011814040206031e0a0c0809060603060424091101020606090103170904060504020304080a0f02 72
    0x304841c4600c032070002d4106038001c0c0d8451001041800c1d041d85480120301200c0c503c803002200c5610000041c00481a04888040350541c0c0d0942144d014a14800940e11064140309000b441d01013200800c41c000c1c0500885001341c611030000708814580b4200d10240282e00880c41407540c0118914040c4c00d04010101500c2600c22800400f40c54031388500f80f015001900701c641c0300d4240c0c203208071011243e90f4002c21005119085899000f94102807115003000d0022007180e10075032510103030b01c0410070400050f551268044980c1512552b83e032081c0c511341c1c01d18a90740d0000034801810403810184540c07003000300026950b00c41080e1b944440c01141d880c1d60607078846515500c403074001000948000744001590f00325241900b031042c482e07604501a507a0400c0300700da402c030000241400b5035a04000c00781d44800101d55919440d4516158540b001005001815091800281c6170881c1e8407560001401420003074802c664a18007820004225000761134050700150500340c000400a00c002486036 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 589112526 1250 589111276 589111279
    0xf1303030f1107060e031c090312020f0d0305040201170403031508060c0f030c0c01061d1510031107050712050c0907050322050f0d020105010f0f0504181704091a 71
    0x400b007420907401707980052032255010790512803150009100e042e010007030108407600e5212420b0301411840d1500b0010045403d00c8110350040c414100408000a10042c040045080008542e20b0380d000403508140f5885101e0021100d0009110400d941680b04601030f0910b403000d010180d032074545058494806440104040b442400501c03642e020201c001e540004100440c02e1900e40c0240b04107007560410b0f403041202011191881c2c1014172a13503c0700b41d00241c4104d4240d803102154002544146c180c224040825030380c2c14044445a8040c0d00b114003298020b4100d03141c5070760b1004600c402d00401c2d882119035006503040300e00a82800d001e014024030b81910345504550300c40b282d4800c007072a541c80d04910b03da81fa49640020036020300c51801d8a00309103000c0c008440d030f590001303429120180e12030400c2890f004000c2160500f180b589000383d40c001c940c04a81c0d2006860480d020f48100078010707013189066011005440d0041c40108100e4a04290034400142e80d800c07012a00101f600300a03 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 589113776 1250 589112526 589112533
    0x60501020a12050403050a0609170408060f040303061a090310020406200102070b0f070f020c1003020717041206180c120614072309060418020f1303030f11 68
    0x140042c8040041101420442c83c0c510304103503480d16000d1074080144015190180c1e2071140b0424070108201141186910086040c6014503113502250390700002844450440c003400081400c1610903009a0014406803464054450b02210505015440802c01074400d108816000150441741e00980307049541507200c0305100f05041614040c400e000000c0d0080d255820003090b0001000410310601a00049000041a103020750010f40000401e500034400d56024542c1c00800756168002c20b0086c2c01285030150711568546030401000d10b074103645502d05e080c0030502291400c03891041c00f1003d030142d1420700140d00030200200201502000c003800030302148a05001c0b042c958440034a5107480b9080004a102c1c00c05108410341c4002c1d80d41c10700082405051068000503480b10503540c80d40095658603240d04900011800d2042e0320803070b00001c43e5110341c0302407040907030b041d00c4c0d19040440c0d00b56500d0035091b404902d603040c0c901045010480701076244032010b1040b07110b07010644104000b03 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 589115026 1250 589113776 589113793
    0x250602070f03050c061b120711041401050f1f05090306100e0a1107060906022109030316091701052403100209040b1905011e090302090601090b0318060a06050102 71
    0x500c040744e4044040c90701351410802d0306140c2031b041040b0610b1000c108855180d01d988061500344c0f03d10071089440c92046040040c0500c01c1c0da07114155904440040300c1c1e010b00c0d82c240c900810321040002000b0301c8140651010b20700c1064010000303101c2804114240c4025984425481800000d640507a03070707280303120700002032429640754091076007209166502400c000003079851805030344200004542e048e80108402c503100c0a4402c0c0c00c103104901502400b134a2402070b0900c0da880c00300800300180302e81c0c48004a4a05805800001c000e4800c00c50f50031035101512200301d01800054400000007900c2500d211321031420b540d41a80d0961009002d0865400c82000810281d0403d0172801d910035034407a03024400b07a842648900704980e51700c5550035828940302c000741030300c1345601030100400c8002c0108103e0b590300071600402d0307a504031a11551a260040120b0302d1080b0781e04614000d480c00003c0c00300e100b1040c0e141c1c8006403014021140944e41d079800d608240c0c2c1c020300c00e031400b59101c1c000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 589116276 1250 589115026 589115029
    0x306180a0f02040207060f09020310180f080714011b0c050c09090c03010207060608150c0f0a021e06040506010b09030a03140c011404150204140f03250602070f03050c 73
    0x15214501c40c001003015007130083c3d545419041b207101c4034603442c00e00d95450120007181420310014a80081590b4100070350015800d00c3e88200250f2030004000600101c0b480003042240e40a9840154004406d0070295021002c80e80c02032a9010720800c00f4280a003030080d0842c03142001c0030825038800060a034842003281446074000d40034105100038040c03984821007035182403010780210350107140c01040349032504405605288406540d26100101202007140742014001205d44644020404c0303070380d03410300381412400c000d88580f0000d02c1090240c812080c514002074824020380c01070058560036640d4407200602031242d68200c68054005007035210109010310170901051403048415443d00581d11812400c440010802003c241114000d000901086910360780050796500021407900381040605840c00700020155441100307500554840d41d00c0600a0042c1901c91828181d03868500c80340c19010b225460013400300512031200b0000c0c88500310b02c003603001c81303802c4000317840035659100 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 589117526 1250 589116276 589116293
    0x2408010b21070905120313080c240f0a050c0c010915051b030304080c0d02070803090d050c220c030203041e1b06020d0e011724030609010b0306180a 65
    0x2c01e90000c1c071030703ca000001e00740ca40111600100c510440a16502d01420007a01000f519980240d921a403185c50000b50980355240d16101441c0c058003110606c0d02d6000560b05503208824800b6003508020500c907411a0b04400501454150641030700c04520802e001101d02840341d00c100300d0300100d8407a1030340425014000034924a01480c20000711131f2480c040aa185a00a441c00c8540140002d007114001c00188489000840e07948050400b9921707080041d682c90103407000c1d16115003010300d040b000300402000b000301c0c0e80d200070349180d840e04503400f0400c0b03003c8041d40e0500c1c1e0880c2041d07604a981880f030701c2201d2089030720280070320300d00c2080010000300068603441200c0710750040c0c2c00d013035040700022904801405140d0091074001442c0310000c140100030704115040c019880002e4603600c40c1c0644c020b500c090024000241c207100c051991181c02c5803941660b816001d88024066194019007145140600c180d04403911038648c000745410714810b1264080c0e180d003100300074200045401 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 589118776 1250 589117526 589117531
    0x141201090213110702030703080903060106020f100510090c11060903040308070b06061b2107080d0b0324040b2212050706020d0b0a0f1505090a2408010b21 68
    0x90b10240c1001c501e607006c00e00c0c120700c5070000c0d43e000e100803030701c0c13240f61404104480c0034100714409070901940e282201d581c0c40d400c18502015003602c82000400342c0c000f24032010010310300c00005103d01080d10380064000a01000300001c0d5010310400500b082d0300000444007181d0748080442e1521082e80ca400704804c3c00544201c1d0300510812071071001002000403000c0510300000034002d582150382c0040502c00c1d0100c0c3c80003101e107007800700c1c8021500e000306481d0b09149110340420110713130400000f800c201c2900c2180f641803c0c4c001c10b41c5000e40c40755006601ca58402d0041d0140d03030321018540b2415070302c503050100c0c484001c9800350340020002c1100c02900501420714a0030b02900d55548010b0740c00421440c45000d5581c81001001e25004403440020501070f10300d00a07490404403446242880c0803103003000d0080000d403000e02ca440b442081c1d401481c4400310080001080e10b50980300b040a0500340307000507040800450146006400c03182c40000040841c1c0024680c01a07050064000 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 589120026 1250 589118776 589118801
    0x50c04060c1b0503030304030909050a05040f02210d09031b2103020a1505070f080f07030c090504020a0522150e0f040f021e0313110316141201090213 66
    0x440ba0700107250f8a0410255004510a4032803109540c14190840b044440040540c07007030505000600c4040780035031b0700b2000c68035015950700b242840c0008082c1c4885644100c514040c1c4100c424080d4a950320200c1042a24031801032040700c03082004454054117500e0050406c4140310030b21042c0d9482800c030000070b14500c240103641c070380c8809413103140d245103104140240d160b4a07a410855aa0361007059200e99500c03d082c110000c1c1070031200103004100c01481c9005165840601c4545140201c5070b100080000070300c25581c4640c05174005001d40c0000c88404800116050400d00309202e01d03011105076400603060340f00c0c00150307040071190130041e419400d40107110601c40d180c2e035480c0c0c2e01600c08500070642d00969030351500030020003072080013065180c0d495028001d001c00e04140c20001401c080d0040c103100a11498000082d00740a91a10340500ca0700d9140e000184d80d2402c00c0315242d000c0c104070344d80e00380c40f6280c0d8a6503003a01c81411000b90701004003006060841da0700d40c002801d4044 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 589121276 1250 589120026 589120073
    0x31506050a1101020a0201020a111b0f0d080d0b011e052d1303031b0b06090c090a0305071d0408031602120c0105010e0907030f060c020c09010e0a050c04060c 69
    0x350030002c1e801c80e8072040701c550050b5000039459a4480e0840070303080480a80c5001465880d6810780300e2000060080c100c00d20418280c15807013429629481011b540310303040b41c082e5035a03028107013000c0300415001c00c41d01d0215100301c0c01c2006148280d0340d151450391070f0362200e510f000ca444454169602803095408148421070b03925003142540e003c0a410040441c0d001e4801042c04c6040180032011a0f00224441840080e070710400299060711803600f015064410021076154041c00b000340d4021218155000503003c03200000380000002d1400c21500b1916001004e60b03075901c01d401514100300d401030585001000802c2c5a0817007103000d040034229500c1500d406090191000119a00031481485143e440d04018829002160b84007904050080c00034a40b181c03566132104114180007801600701f41d039490140b5042402803203110800d040c001c041400541e16414401a50709054134054859032405000460212180040310251142c1e5120105c8a10141c1e80e4101498a800100031400c030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 589122526 1250 589121276 589121297
    0x60d08160803070f03050906060604030f020f3a0b070c03021005091b060a020a02091f0303050304061a0a150903050102030c041514090108090a050f010f0c031506050a 73
    0x440d00700c0910700808041e13071074480d00e200c13000d8000c0556001401809690304524140461940d07501d04481c220b0764005200001030740d440c0001081c141c5004003654100120b20400c100ca0b600100201141030a51002c4a0841242d00701c000715215074440014240304e40d1101007240d8074010b003031801410b8400c1c81180c00c04d4004078a8070040d9407081d40c4a07030b100e610100c1c0b040000140e080b02d00c4003510042d69200c2c244162104003d544104030303007002e03000b0507603040801d401c12580c100359000e021106181101c1250760b0715004009604c1200d050740d44c180350001030280007000b508042100c5d6001001a150f003801c003010303801101c0c6d4140900d42446601d10703001000810030f00296114064103490243c0300c0d85002801c01204850224120420510455046002d0044400e07114032010a103040500c0d6664030500030329058845602170914070400ea8800c07003031541504580c2c83c0112800c014890489404800d030155003815038415042010b0120500003e485800509146c030f01c140ba05c4241da2 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 589123776 1250 589122526 589122533
    0x308040b0c011b020105012d0e060a09090c03231c170a1b0203120a0207030e09040507050a0506120103020f0402070c031a0709061e020304090c050309070509060d0816 73
    0x81c500b03003c026075141c4004103c0e08424440c6420112142c01d8140c480f40b50030107841500c900305010303003d400307400c41000c5007480d00e81c10805c0000d0504200104000600380c104000345550314802124048542d41d0302d112141c1d00d0b9520031600f24003113402002e441a402455140403224038003010100200502200da106e0300101400380a10291480059a080100c146031500d01c0c0401c10b84065500c01c0050003098200030103102d5002c4001d010040c0ca40e02c1d289821203501c2c4032156840d13400762100f81400184840810700d01c084450440c0d08004040e81c4038103000c035a0103a505110b0382c0003808030042026080c1100c1105980304001c00040c50050315551380c011503807064005441000d04e02003c0071030010009600c07030700000c032800c1c01c507001c40c507081000348140520400c0328106a0001c00e0103010354020003d0360080c01298100b4040c00c0c0c41031794010099001180d01c2d07580ba02c103044000602e030074506009070007044080c005140c020711507116407007d40d0152105440c0700b00c03e4444040803 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 589125026 1250 589123776 589123811
    0x10311131206060611030d05074505010509010c11030703140f0a0c152003180907020606190f180b030f030306120312040606050909070308040b0c01 65
    0x1038500e2124604020075241080c0c0c080b030300c140e0480020300620750205000c01c41c001083c1d481d0b040034a81c0106150360b4802040f00c0440c2894030003090f401c40001c20b524422019131380e03010307400c21802c2010b1050340e0020440c03d100419104981c045842005501000d502c1446400135040c0141d511240e88060030010a140030000d610946081c00713007401500e01c0d40f4007400804161007242d0020804d405039620750b101e151045100b10000241e140c503081555030f0143d41c061401403640c810080d081c058a0310f1240d12684050139240101c0c00700314000515140c00740e54540504150b50042c8407071358a2409001e80300c00310101d8000543c1c1101e100092100329410054090b1406003208003040382c00203908420780b0500c0d401107105ea001142d144c404e1113400070030f40350312403412280d62400901049085096105c0d0780988996080c000e41080107100d99900306c0011a00240c0741c0c202e4540da01841c017515001d1501009281c03140401c020448544218050715003c03000c50300002d03460b042d034200e03000c6 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 589126276 1250 589125026 589125029
    0x615040e0a021e060f070c0f0b270118090c1101020f030109020901120c020d080c030915060604120f1b140d080d0c08150d02090613110409020c06070c0f0201031113 72
    0xa0441c140c03501413000c2d2080231844401884000340c8641003201120503d41403681c03d0031a00380319008c1c400c8408031607110703481d48208034042800d804266501d5000000c0501074a400102c00715036021460340c64200e0506c21100c40302d03a40080c141c10341c1d007000c1400d00a5440000a1410003003107040445445035184034640500e482d640080044000000703014001c482d000f4686038481d64103104100070146c01040c0c50100844040d04076242d0358801c0000351590040380c0140c03485c0f1000880700d0080040b41e408004c052070180e074020842d507080703184100400d034a5014001c400400300250990074200000010045031249250070b04002c7c060103d4021074134507805260001d28003000b80b01d001b40021001000070042610101c640780c0498000c2450f4602c00350402e8003500040f04042c89000440c0d0082e0301e072015062000e84d549075145a400c0181d041225141c1150050501081615000c0c200c80c84802c0d51100d4484031004a640066004248546100341648010003c6903070200860400f0070 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 589127526 1250 589126276 589126283
    0xe090a11130806070e1c022202040801050405010f05011d040c0b1912061518030503040611010c020706090b0703030b1f090b0909010b0d0e0615040e0a021e060f07 71
    0x2180e1900003030003081410300e0b00c4414080e0072446c0d070310b60849404e4400e51518980644222461007201c0c9000011352094680c1c195104e880450302040402c1c064000e14019400f8400900150900c0000030b012282c080c0b081d01ca003205103031080e903044107088a01c00d51040c0141c0c02e036602503503601700d05040da83c0401c0350710000252184d000c801d841e4000020784201581c00c40b04003d4241001c0344070055150300c4000c10180001c0c801c0d00d80002001d580d0540c09158002c041d251165640c0030040e0054a0b5402051a00c0d420088911003c51000a0240450700c295880c580030714900308482c501c60b40311300415810941c03540c51242985d26025220840155004603029500f0010040208214210703041110811010001e0104655502110328151a0000075060b599403c1032a07000c02060000400703421743c00744c80304001010b000074107100c699043c25281806000c51042100b520b648132100000d52010047e00302038103443d18440381c0c411090001d00002e141c0300f01500780c1201d17904410001c8 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 589128776 1250 589127526 589127533
    0xd0201260411130e1908070c0b0301030c1406030109050a0f05090c01020106140603041101020703120c06051602121806040909050d110c0418081602040c0e090a111308 73
    0x391541003039418282d000d109840d0800890300d0010304103440b0031350310340c1400912001c05145e4040c0403c00e0111031aa0b5444004500c05559540c1800c0064200744010380700b40e991138100146416030b4182103400134900402e950310b16801d1a000e6401003401401454001e030b66101c0c1031405990074855036004440d150002c1185800c41c01c00242540e4590308072039184541d405180c001030721b620050742d0b0060703440f01c041e010700d65100740100d00d001c820390b0025183c403c9004600c1a6150403030309011045006140500041d5541600ba8101003e2403d02c0c00c010b9002d511490404000302028050b00021204246588503008001458035041038000c000d5003584e5801c410b04100081000c400400c41a003080c50241609500070b40d222001c801101d40165107440030850910302c0464074a010300d90024403552580300b180d01c0c03402d14080210089002d145000200503012b402241c40c150b000c900245540555503c031078444e005011a91101d000e0b002090001030010b031403c2e412100030b0400c0d913006 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 589130026 1250 589128776 589128803
    0x103120e0d060b09060330220303031104120609020609061b0c0a03030f0302032502011b03111b07030b0702061605130b031312030f0b040b0d02012604 66
    0x1002180d0710085c080303500c00c0d801450240168420014183c2e4403504e41141e8400e681d07100241550140314440030050501d8030b0030721140365003010f03030485010b0781d0081c0e40800182d000c101041c4018403c1b401100700006064070b500e00011001e4009800181c40078010714288003204001c91956040805000030070400c0d01c0d100400020204200030314070401b100c4100083d444c548002c1d00098224049a0415800100041a641402c1c0c00545101c154141c2e0380c18600c503030440203000b41102c2450b0032100300202031442c0340038841d000c0c0c411a0384101c5444d40c030b03200880d003403a0901c5511074401421070103603020000201e6000107280388074800d160084c001500c1d0034403203180034400e81e0b0000340c1844402d004141600000c00e24140544560245030b070b03a04d032070364003a80c802903424800040600d0140802d0b110300e154142c00001d02d5508043c000d1188030f0140c020031090b604041c02c801d800080700102d07040507610a590f82c040c0e0080000c80084203400058004448103011141600c43d02c071503d80 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 589131276 1250 589130026 589130029
    0x510050909070911040b031602190f060c0806031c021c0c1202030301030503271f0905010809101e090602070c0b130311030c06121b07030203030103120e0d060b 70
    0x300a413048820100500e0f140c145050103100c0e0002400802000707080c00340c8512500c0c001c000c0f41202c00700385050015900030900e007061884400200c02c03202e0310305140c0070001c41c0307010f030758030394018880103010b414011207001904061800003812002140b2502283c08a0f43c4610300c01240245c03203a55800072464260b00308066035440d940c0341081190300400041012410100507550070701c6242407946c1d000307200f041d1404a448a0420981c7c2c0c072403044401a03402501505444581580c0c540310f41c501c0d240d454006658803d01160700c01c2c110b4104085070741c94518154003a90002808203542405400124078500445042c07038030855505900194200c1400f10001503c001081c44503a1755280c4500c4000c0000810302903c001804a001e8410034552650140222500c252000c1d100075224410088500002c000a5864502403ca0f01407076034070f20361415040345ca045800d50001d6140d6461640e8054204110444400401030b400e04c28040903581c14044020281c021040400c00214010 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 589132526 1250 589131276 589131281
    0x1050a080a110f04020f12070210060b030402060705070b070f0506010e040818010201020405190f080c06180a030204020705060601120509070905060607060e160602030301031505100509090709 84
    0x80011100380d00544440e00003459040074241000e400340c0c1c103101d050f50301001103406401420010740140c0004a08011000b5041711120b209000503070840304c41d19800d410140c03c40b90b2901a08403001001c000003000740c285100100480e42c0301d00300700c98120b90396103168a1a07070400001142c04259110741201800000c1103924050001480080355500b0715907120290b5200c0c070111034020444140d1020a660b0003941610020880079181c0100c070745620380d091210304124080c90407501c0c51000b0200380c104000410b0003500001030041850194290045100c42d1003e2442c40e9016078a85c81c04001070300c5600142000b0341c4110300030101400c0c01c000151034140004690002180b60004128000b600020480c0c101c0300b01c2c9030001340503280c150100d05140b141c00400b400030350500c1d5002c4a00d04000441c545ea0900e41c202d0b0607801074403158101d0300c910081c40701400d000c03c0c035820004510300320380c001c3c0c0d046901401607a0981d0ba842011500320b02c070458400425400c0031030104140d013104d0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 589133776 1250 589132526 589132529
    0xd0f140a030c050d0329030a020a0902070204050903070201021e070f0308030f060910052413030308010b3402030703140705040905060a051e0c07030e040b090121080c0601050a 77
    0xd0500340043c2101051b8541c11484c03081c0500d00b42504200010b546071001d100012401e600075108641710b90b180c00d03c440103036000b001c01324001c0e03180400240740014088151205182e0513805050310b540720b41c14400c3d02200b503010503101406072000001c0c4204240b1901c00003140704896081c0c507427400000e109020b0000529460041074000704000c820303600960f1a4064802c02c85652003130720391102c120400740840071503403c15118001030705401000c0001c900000c03203120341c5c0d58100c01d0ba03c0714007420550250001003002042d22200410700e8204c0d145d901040c2141080008006200c240c00003854565903604c1510054202da0002c01c0c0404140708001c058501503034103012402440c4e907040d80da9800203001001180e035a402090941d0700c0c040c456904d04030721302c00e440b120b070410301d0315240a503211101c200e01181040902c0c60f0309007820f00401441000c02442c030100c9a01c3e049a011507010708015200c80c940e246030000700060b40300d4020b440700c2d4000400a04480d81003609201e001d40c4035 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 589135026 1250 589133776 589133803
    0x504020a0b0304060f062c070306091a040b0a12020d0305070524011202010c260a0809010605011707030c12020706050f09010203040b0a0b010e06070609020f0f0d0f140a030c05 77
    0x154007900d4a160000c030280166540040c1002e41fa80c1e0312200c0440c02420302c0d4002014007070078600300c2e48500d0b8182d0300c4d403101c400c2d0803603040180b003030030100308042c8040b03500c05e000418113400d10303000140c40d041110281c05070007810550725004040c5c0d5036a0030010b480d086030114140110191641c8071400701218050030f0411010208410389400103440440c1e0444000d040d40d9034995a07410101c00b420b00018204441419552102c4074031001815580703040350401403075881c003078002a4540c85400c400c0c007690002d1480c4400c5071140a81100035001088503103041c4aa02d100b1001070810300d100500c05940125000201401c1c41060b11185900c054286c8080784e00610a000105442d50350440e0000415040019a51880c0c001600e481c6907107510250701510114098080c8002e6400c81071005100304c402848220402003080241e02c0c103060701c680c10103825065800010034400040b001540241442e100f460900224603180c10f2042c50201c0000726040619010002c0c100b0006c2581d011 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 589136276 1250 589135026 589135049
    0x20c0a030509180a0f1a1e0f1207090e0706093f1109040206190e0604090f0b0427080906040b120705090f01050703260612010e0309040504020a0b0304060f06 69
    0x22a40001200380e0524044c0f9021f07803610408a100517500c120b94040c038054041c148140d5403c011440c0d584501707041c800d5111440c02c1214015502c0c00c0400c1a0003580c41c01c0d00d50048403400c0c50303c1520740c56131583d600d00200c1c200750f003400d00d00b0f1000380c0b16a102551000e068260396071185422295400304007105400b0321500414400140c2d50402a0fa016440031450640140d2501a04032111000e2007000d83c0c100328002004117962a00d50807009000c0e00d41d030781c10700c900c200782814002160001e5850105500c015008604040400b01030310002c2c0740212403090820101c4000030b01160720079480101000000200e100305160402843da52100241c10001d0130080020f0114032444180318400b4108030001800d1070805014520030448090903480b5600c01d5603e22541840421040e0355852240a945000280003c81400b031328541840042c0a1801c101d030b00814030020b4000600202c0e4801200c15004c124003042c42c001e54881e40c016a4086601c0c500c03040081c04685442e00006040302c0c = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 589137526 1250 589136276 589136321
    0xa06060f02120d09290403031b0c0305090402041a0301060f080108150a02160302010c021e1b030a0f050303010303080c03010b03040f0c051206010f09020c0a030509180a0f 75
    0x10082c10642d200c3e02440d81e404908825189052200810703402c280c00d03194800701c12881821000080c00380d2083e40b00343c40800c2060b01d41e18013104da5206140d60280043c00880c3c1e0600003911030400340811880c0034202505007a16102d40303000e801251084e1888259000c401000007944c005481061220703241820f8081c0d5040c0032202e6242c041d07480700e00e81114286030106080810b181d0443c1d0101056446015815800340341c000e0117816800c4a86c4014426803004020b402455028210350055000050031001c540d1102e1600c02030b04003580310352502072144024007180031b030440c550100344500003542c0d0307a40c11858054941c0c1e2001c3c010150101090006212030721821007129005030b0011f1300140080c4951800d803038a40c0035500b180307400600c940801c081003203002611b581601d038800596102d843c1c580a482040b030080102e1b00050740c0c00300c500b40c404a40030300003c00b692a0060440e0030030380102c1c01c5141130104240d50211009980d50403a00b4203048600c228005403000c010f05a1681c03 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 589138776 1250 589137526 589137553
    0x120b0910140a0306020d0b01020d0203032a0403170d110406050a1803150f05060f01090512070e070809010c03050f0712060503061302030f06130f05150a06060f02 71
    0x200c1402003064215074648111000d0b540c0e06002d000075030b032003001503540707200d000b0138200031700400704166015224400ea200c0480d030010040d2803103840d1544440040c1e40340e0310031203d12080300111148810008000201c04115901c0c10300151002100403196200b0a038101041101c0b2144503403000207405010601c0850740c00030894042c501245004036119018000c1c1d41700441da03039400240312384400c0800e00a980c0e515000004015070754041041540d44101c02e105881c222030450a001030495030080c04549003200c2e90010322a05c5030103d0351556140c2d03000c5650b410042d00c0e40404200500300700314140f0003d0240228007080d5140500081c204134805d0459102c018101400b485604000f074818085542d01500c0203043c01400c6035560b045c015411942340c0321901040c5d010b40201d03041c048042e000024041e020350b40f0340c0c0d0301e40c41c4804076449492041032045411585801041144969400d606a0444c0142c6032510300091151a011025140d0502c404180c0155000380c80c5031081e2 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 589140026 1250 589138776 589138801
    0x1f02060408030601020f0a050c21070303081b030915130c06081806010b0a080105030d020d030203100e040c051018030212010b130203010503010c030504110d05071203120b09 76
    0xa03600560241c0c81c0d855043c0140e0820314000100d00951040d0385601c0c092000008904111400c2600c020800724071541044840003550115001c85e58000001000003c0c45070b141683e00c018804030a664140400b0003e440b1680103030381300070140d4445280d62035140361880000c0d800840090364544034248075941e42180150030f02c107070000d11140100046881e0030b032040c0000c485245034180c07403503503031910395529207500807800090009a00d0700c0081803509000500402001c03e54004011584100c107048001c0e40c00100340460041c801e030400038041d12101ca40310700640c85050b4840000b4108801d01c2020792111405104110684000e4141e43c00142e608005803034040d0707541804000b100d5080c5000d0201c650840c2d030046448580004140941d80c042c5042e035404070000e0042460a0f201102034070350175500034180b001c824025030000e292404408100074800c109540209030794050003900e61045250540108080901031303103800038144200d0344107020440e80810076040081d0003680 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 589141276 1250 589140026 589140031
    0x5060d020405090f010e150702161406090603070c0210021923032a03090a05062b140907030c181509090b0f0408090d02010509040f02091f0206 63
    0x6582d00c0300414a0440306000f85600168401c0090013010b4411740119500d040d84038403200034100f80008130741b8a43c07022410a482900903945c0c848442c1c1488140003110405142d181d500080404c412030b659202c07074000d98801c1c40c4645481204185900502400c2c0c1c9440030110704540141c24140d202c1021207000320030403500110000c0c00c0000e5003a003408505400480100b0b07512004c901361080400c0d01c5d626926481108528000c116943c1304036a43d6802405141548900060b40c1071103242040005890780d104100ea0640d14446442ca00d140d4485014010780c1000b03440d513805401c00c400c10070286400c01c820038000c042e164519104c2c107240d0b0741d40f80140c070040e019828401001c51801d8004401861002107000e0100395500e24003001060b1481045400d48100000210021156681c8600c0b40741c001842600c0c205842c400c100030360703400200490502070700b40041426a101d501c5a0700c000c60301600c0042e5640b25441c204600360b22028418000d00481452031000d10364081001c81c0c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 589142526 1250 589141276 589141279
    0xe01050315160c0f0204020313020310020406080f0402180709092009190e090a021318030e0103020f070f0618080d0f090515100605040605120618090c0102010c0305060d02 75
    0x1c0302200c8034a000300384e00101c2d00c40603500a00100c280304815118001d0254180c3c400c400b1906000c3c0d0b400d80e200103a0090344500001b15400c240010b0b030100440c9080359000e440288403c0c5c50000c501c4158040c1403081d142580020614202800700c1072451140441c41c07500c20358064000000f52000742858418107070510302605d02016904d001c4131a0b51000300107040792280a0f030381c0e440d1140740d5656546007940140d114075411115a45004124801c1c00060314007146010b1560f08961401d0b2400e449100ca070504142c0e00b013007010198001d0b0f001400c0e980780315000f540c078041d07001e040c05400d4802c184034440a48201034a0540001c06040c1282d0944152040101381030074540380110082060000242050140c0e412480316207240c84046d504c03c4100801703190065071191011034a42c040c0380281c0010802c100808cc44c4482c4201e8616408a1300824202c0d0550b83d40c40c9010801c0c0e4281c458800b03607400300c4408040d5603028000c03840c0009441c5010085c41c545140052803030300d100d21021303 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 589143776 1250 589142526 589142537
    0x50a2106180f0b07080610170c130b030901110405060a0c020303041d04200604030803090f0d181401050f13031403070b060f0306010e0c0904060e0105031516 69
    0x21003010522058001c011600000e031480d00d96802d0600850440040301c0072000962581c000039a1131800e00c8100017040c0b01c9648036a015921042d00540c180005041100e88200c140180d4044503001e16407030014151403240b05449040c12040242554080122000c004e17009000030304c080e80f0380070161103001c6e0701803406c2c481d50032190004c03908600c12a0403d20441b020004c03c4461000c180c204180900d110740c0544070f0184030078413040314452525564650100d800c01c01000404c1850018542141d1890203650300c000011441510704000441d407200407440d81c03c0c0320a03407080012045002030a0905081100c8920724000810314403a030151281814408121850a03845a00684000d5a80401019501820a8a000c1ea603400403402118800b10000006034030741004000d00400000180050130241d080020b40c3c21104c0000b4980d0700908400d210011345643d60f402844000d00e101311100c034180d41440b003494202060881d000314071055080c140308080c005003810070010b10903860b01 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 589145026 1250 589143776 589143791
    0x30306090c040819030e0409120e04020d2f0c0a030f0e03060f060a09021c0207030c05030307030213060305042105040905010e0105031c170612010f0501050a2106 71
    0x3440c07103005981080416200e99203c6a80c507000f058891601d1034000d84804000308006010001519030b0018010455440010311400c414080d002800c0b682600a1015084c11800c036072810445061403260310070305501420b080041c60704030a03030780c0603188040c402500d8803c2002c652999000c0d109801000c021102464221261240305c110000f2031004066641c241040451086411410b03164684918003408002a0140300713442103c055003020700e6043c401c0b0140c49081070003904908410b6082c0001002d41d0b400050301400254400e02e22902c4c0140c44014102400a403101c3c0ca03040242450326040034003001c1101e4880101401c0300300003142c2e9245610710303401c41d964011580900849414440040b603208000c204c1c042c1a100c06a080318040c003020000071560841088800011810a09401180c0702e5801103456200102030805270140362120415401c60700c20800c10a41d20340e030783c40103008600e051203180000f0300c007400300d804c4490f10305840e0078061aa4104004d200f9a6100d10 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 589146276 1250 589145026 589145041
    0x30f0f14060a0c0210020c07050d14060403050712030b01020a020d060608070f05040f02040302181b0c0a0203160b0d05060f3111090d051213060207051203030609 71
    0x400c02502146a058401c42d051880500340a000e00280300e40150141100c4040c10700410320071f44040c901c0000c014040e0038685000c1c0900c4e07071049402a26181d40140000c00c00302410050f10307019610a03600d0f02c0d03960030319091845804030480b482808240c00c040045519a0b400140758042d03603011152005c2401d46440c000c0d00618041d4031212150140490010307030b1042500140d42103810a07581440181000412034040348110b01009621500c042002d0300e02501410881d54040c7c3e0500303040c0803150001c489001180c100070f150358199800603100d0800c608052000c00c420150107160800d10b00e04224400b8464081c2c45e00060480c1d42d62000100c1e84c3d9503044a00510b81c0c40039001c1f6010088010964010380707070143c0803030520412a002003080300114800c0001010b1400e40ca0f50400f40001c003000007003003003034400b91206d01c40e102488042c40011401050011100526145001d1070b04401034104216684420301c90108403402c000b5480e004811280d01c100c04840003495a0758284 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 589147526 1250 589146276 589146293
    0x12150f0e180f2a0a3f142803021e0616090305120d14010e090d020a080403060506150d0c3002030601030b04140619030f0f 54
    0x789000d0103200364429080040d42c045203401d074007100040e80e0344011601002c481c0e00e2585100d4a282c1046828500300155a01e8041408144501c00992035858801018804601641d40c16460344a0a0380c0301460030080f502944100407600b07240030740041100da060a0f58407080d003241025a09400102a00401d403003400b50308000411220710f0094003074200740307040e41c0c8c00080b6645501d05440e0f20300b42c62a28002c034416801c61764854000e11250010103820801508031400c0790711100d448025800b110002408102d018108265281c4100d10b0455111850000f1b511045401c0d50081c040d0b030340216075008200d905880d085900424143c4903140800c010501074940f0b507400c1e101c040794071010340f20513801481c103001c80b65441b044184035000100f40d0400d210400e021408150035034100715020190061948480141000100f100c10100443d06503404031072071300341003240ca100b040b42619207034107008404001050700d40240307820744e55501141510403e0140000e2000320080d02045100c2 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 589148776 1250 589147526 589147561
    0x7030201211404060509060f13060605030d030c0801050f0d020402030601140a0f030b0f030d030c0201022109070e0f0114060d0204060e15030c12060f0901030312150f0e 74
    0x11007040007610400c54254140b0040e81c08844180c02c00000c241e0000300098614081e059168404549071201c404503503032241c08200440e05e054030b5032000655940c007070201c140700c0656900d01048552000314020022041600203500c42c80324840c6100c41c644400001c0401264140d800695a071900c1e00140d1b0704a5400b5880c0305a014001903691002d540041503100b001d0707054406100500c5c000c01000b040d4072401c006642c1544c40342c0034000c8c0c80c501c681c101c0300d420842400014a05200c200c0c0c120080d20010b0300b03521481080009018190104000c481c4c020100c4089110746400e24411000c600714042c441e00081c2402c0300305655a9544840480c1e042c0400141c0c115070320b0742e6500c4023510800010016522840d009100701e00c100c0d0035501100d110303900405106240040d02003024004010282040e43c104608950180c0c0545a1400d051301a5000e5211484545081703491001961522b411030346500c4001c140400070740801ca502c04050303820321017611400c1c2d034030711681c2401c00740308 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 589150026 1250 589148776 589148837
    0xe15090d1209062424080403030f090819110a03050f0a1803061b020c0109091e240f030c05060a030b0a060e030c030303131103150108010f180507030201 67
    0x35415113203d000740059200c04450358a000c00c040400e0000c0c949407541c4c80c00c2d40500202c0c6140c000280080c8c030039031000581c0c5859a2002480d10442e40b1120038640200312202c0c9141d0403030200008240d0802140e4044d0310345000180300d408441d960040060051011400d44c03800d01241e21044103000320f9540282c0030000600c0f40e40315a403410044050416202204c44100350840c0d4503405501c0404d511403001e43c180c503281001403800701100300801d01045400b00041d0303901c0b0a001c110405008100944207440380b03d82003526031b9003103c035500903280d21004070240c0e40b501c10400500c0418003101101c0046441c503440f46041301c0c0681c0038100c1940e071107a204040443c04a00a500301c1000c0b452810141e08a400801e516818180d0b24442138031110030710302d0f25820641c0000c18030b040d5244403850142c10b8400040c1300e030300e0000e01f10340281c0000305c1603511541c80004115807032243c00125041e20b6002c1e10000703825104c0c0c0b92a40664040603042000e000c0d04603804040c1c02c00c45030b600c1100b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 589151276 1250 589150026 589150061
    0x311030c030f070c05010509090c090d021215010b16150e1c0801051c02040203130515091c122a05130b040302130509100e15090d120906 60
    0x2240415407030554003201c001c5482e1350030500e0202d00c6500c075405650300150082c0200c409038446206104558100040c11a405600508414016291041410383c1401c18100030004095100400c280000050f080b1640642c0b043c00103100d0510710b83d40400441d6044070f114072112580042c00000b9010701d04040b00f161041509005024100080c43c81d110031a9507101800d50340c0303c0301040b00040d4480700c07190107012031400c0e0b1400761421758029500103601c10071300d00d03817049260b541c5170070300192a242d941d102040300100306070044144146030201941e4030480c0100c004c2c00380090100001d6403c00310202c1d50b1502c41d1b680c00f1084082c0b8a000300c06030600e00c8890401480c0051080e4000800c1d080a003400c1d03034001031040708040988d130990398000e0101c01d485c500342888400a00d40200402030b00e103d0766058203008803032813243c0880000b44001400c0705080c40c8288203900c4030041d0141020740d1217100d12a4070710b5400300b080d00c40c034050000045421451400c20b140a040e0b0100c5159030481c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 589152526 1250 589151276 589151287
    0x7050a09030b010806160206010f05041503170406020d0314182a040f0e0c0d110d030309060b0a1a0901170106110f0f030a140c0d0f030605030601030507030311030c03 73
    0x4d0b40010f102c1d203d03410401c041802400e00c540200d80f244428400e241f07201034840c200713024600d42b075040991900000700540302c5883e940d45918009031355001280c5d003030450019050000d558140a030441c1d03082c250070280480001c80300a10b10306500100401583d02c80002030321540201400501c2d0700502503244c0d40c1701c80d00301d03a0581100300c5074551414803540ca45008401289481d020303401105e412103011f0b02c048407110003400020245494100c44582e800c072192005a87d5410040c0503031130180e40c0c001500d40d0f480c80c0039401c80340c1c40241d0910a00059204014a907120500281c400610105051322160442c0040e10300308070810410618401300c1002180e81e95101c280e42c0c0c007808c82c400c100c600035610a060f50b502c3c0c0c8074041e41480e80d80c0003040008000c1b4040c84d00c032001d811408544d9480c185052900600340220401c076400010405a250030249a05000b01c0740585011000f52105514680c0d076036a4800c107520004041c0040c020f01881035010500c15200540044019a42d482 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 589153776 1250 589152526 589152539
    0x3c0607020601081506092a070b2202130209030309040f141308180a091802120102090310090606030f030f031505010e12010e03070803040c0902070203030307050a09030b01 75
    0x241c0702401014402c0c4100c2d046161400607042010b4018400a849000349444d11150007000306a54a51440007144580e405980c244080e0000d244050040c811208103040800c15252044440800c80c4122503290090a000d80d0b102034610310307800d210910060342c43d020710001c07a01714043c040350940e220323140c01c00340401000b01c1d030440041d501012403103101d03503510a031071034240300b45007000501104418081c2c1c0d8040c003016084908a800020003034400943da40c3e07465000d4130030703501071040020300c074010001c00c604210388a4228440401c00030350800600c480460741c1c1e150500d40b5052100c0e1141d9108003403121030b6100e0700c003658004540251918050030041c11000311100e01e40700092a003903d03005000440d07a00b010580310165200c0158081c500c2c10440305800e00581c10784595130710a8030811562040004005141c860180d541e1207207483d0410b044405c15550020f03000c540104812001a036000c4110b0b42d1141c22420181d40781c0400c034100300c2c0c520603a604000c010185690012404 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 589155026 1250 589153776 589153783
    0x203010b150705060c0a090306230411040b0a14040b190b04080c0306060f010807110d12061703070b090c03060c030a200406032003010b040609083c060702 68
    0x441d8014400c135001511860204a001d00c203200741c0c500010703807003081400001d509401003152181c2e08414a14200c4100300244226882a2011a64003108144441090a19000307020410380b0032200580e5003494080b070805a01104401c50b8803d9565160b009841c1c1e4600c15050300100319071103603031100340d03c0e912210102d600c2405404843c0c0f00320310a90410b40742c000307000c0784030351000b0b04240c0c100c0a0301c100543e024640640000e00b401159903103400861010071940459204e81e684098402101601c1c8004a91864010604d1440350600040741c2890000443d840c480e4040324180c01da9903140c618a00f4180e56140d1315a26006500520158401c0300b00039600a00d200b002c10811010150187c070072520320f03802c0c142d6025900340800c2114078045d9200690440781c0723059030074090904021415069000340c0268981e04800714080c80b041754848160000f801c0c0103c01007014900c0b1030401e910f207104003a01d062500c0707001c0c00441c1448002c8068102d551600c1c00031141c09050441c0b02949 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 589156276 1250 589155026 589155037
    0x110a140304051e0d0303020a0c1505010609050d0c050d030908030f031b0310090b030c0d0b040b070221090604050402130801050c0915070c0510030606020d031a04090203010b15 77
    0xc2140007610403c84058842011060260024408014030605030707016806034200076208418090108070050108140008400801c0200240003800c0d60401c4009401c0f540a0b420060081c0044000c6000217010a0140010303140201c9580b062506a8502101c8066854002c6010b5010120b140344d00800c100700514001c50700380d9428081c0b48032952024207140001c850144610407000c80c100001d103082d038010303c2032417005000c1d140d440d0011000f05a0141341128104c881000d014100700a01c554411015000303000f41c4050b00502100190685525206200443d90700a00007841e0400f95148401c50b801000050002c0d520b407944840743c200482107030b00c40d5032191b50801c400620f450364400211924010024803500f185203031204040040d801c1400700b03d44514507804040782c0ca40d1040182e00c80b6400c82c0c0d030003003070680c10010000c1c00c0400250001060504100307450270f1034a82061040d080000c25580000c250b080360000a0240c007003806019000866136040b03c02c2c50100400410 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 589157526 1250 589156276 589156279
    0x409050a0609140a0f020c0706050702090604060e070807090906140315060102120c07030203011b02100603230c0402040810060b12010b0304081e21090706110a14030405 74
    0x102aa075a0314040b07050b07681c0110409202c000200008504072401c2c2c0c003000c01c4020b400d00c01420071520042c060310b8010b6980011012403c04100300d01145001901282d018000365018088c46140c014586001c82000c0e1405050251510004001a105510a4008204581050003099504c5881e01450001050558020300801c20f004004c83c0d80c0e081013078024441a80144038a80c0c46031004015904900080c2125000710100040940d409005c0d0101540128021036064447d2240291401d01c10207061103029040900400110300d500d25140071072001d940e541c403403105e00e5042890134880540c403c1d6a0152001c01d02203041d0300c0004e500b52000500020400a041c0c0b503201c070346424010201040030103602b6a0040c40103005a1005c4d54215100d4000303541800010100883c00d20414003642440130000308600e155042c804070f0710554002c078000380c0009400d258100f81d8a0309080e0054200f80701d00ba080c2101424030800c01045130360b03000030548118a400008081c5c4036400341c031070203 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 589158776 1250 589157526 589157531
    0x20313060f1b0305090d050309060a090f0f0f090209030f0a0c1706011208070317040803240d1101091a0a0f02030f0702150403020405090f06090a030210050402150409050a 75
    0xa00e070100c80b041c22000003907016140c1505141c070500c100900740c4142001101c09000600c81c8800f16152200540001c0c2c2268a5104855082141c0191400c89547c4115070900c2529010044d1741118407450055414045004d03036507680c0503002ca031400e584100c03405403601c10415100300348621140c0801c00d8420f00f030010058032521180d81aa10b6100307000c1c03602c8182142c124140040e002c50010712700c840c801d0820410034000070324001c0b90000e0031501555482000420031000c08401d40303950b942c104100112100241803900032805403140128002c10300004040890b8160303000d6403d0400400500c1c2c2001003031880802000000e070040d40109000c180d01211058030240040160b0390300c1d9042100302420040203401300070040074a080c09034604e410400000c80940c030751303008e0f089c456440c0b0b4000b4408451404111031078a40e00900110b000d4102041010009034089924800f000310302d1008551615280000360b03000300d0034103600c0500c2c0310000300020360300099041b40c1d10030040302008 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 589160026 1250 589158776 589158797
    0x6060915030b1306060806011e0b041203080a0e0a060b120601030f08460912020d060f0e06100e160807030605060a03020c01051503150403020313060f 66
    0x200038602804001e00030302c450400545042c0c901d04203202014080c9402007001d65036010641e007810b1080c0c100d407103c60b00e940c0c44d15203240d640407440c070700900e010903015140c03030300d441303640e05803803d09010007400c01452201064294600ba0401c03194004440305035202c0b4822803802100800f910302c14140541d4400001170042100400d07180d04803a00484030185039641c6581b6404564408002c1190b86910340e200b40e001646c0c0c00104255014010541d42013036460b243c14100c0600024071031004006031003200703114021515030320140259054500c2403000c405071a1003006000c1250003d4843c0e440c080d00e10400301000a41140110702c0300c03401600f4180c585441003a0840210703800500741e0a20902208902e2169155030352020441c42d002503116201c1001035406d600010307241d00042d401103401620801d003842044d8018400300c048072590550400480c0d107550100c40a4400d00038080d000a050500030302c211510345011300c4184194545420000d0445c240059a030310010f00280c9a = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 589161276 1250 589160026 589160051
    0xb060906091215041112070b180a1e170105010602030a0c140d020106210c0302240301030813120f11131a01021c050702040203060a030807060609 64
    0x11280044800340c6041e1800340c1c80400c1c8180c0107090740c01c40c41c140c4112540c0440c04442e42010074003840c450601000c4c0c03103442d94100a18101070070842c20482c3c00410f4100480c550250485280d01c094403c1444680049400501501c030658024840901e40001c541551b840300040081034801100c03000d084000d66080c10780c02c885003405940003581c0208a400440c0c1e00501500080c144185096019200085034441c200003480b010480541e45880c0148218050180c210486004049400b400a00c554843d840c0560311440040e01070700188044640c1451080003501401c2c1c20410601d50325652031038800203e911962104014481420000c40c0318034100248501458000c4610508244942c07100c05005c030650301c545034071420303031400c50b209400c003801b40303000c04c049411141000a2054001a08220214180103842c2019918450f0143d41280c1034440160f0191001a1641d8840e40840c01c4621250406040054049201e20070004a0341003030044e207080d51020300240002c0d02 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 589162526 1250 589161276 589161289
    0x61e0b04060815060f1207030513080304080a05090a0b09010e0604060c02150c0a0c050f0d0b0114010c150f06090b060403060e19050f2b0807090314100b 67
    0x41000041040012440394808459402d0126800a0400385031402170290341500380d0006030b0940c0c80d09100b20030030080302c1d018803516902000b10110012101d85540d21080d80c2e10000300010410b200c0451808144d0f071094040d55982c90000e809032403a5902c4d00342155203900b100511a0015100b07600382640d5090240941e403c5900d40d071200903a0015070380c20094940079100c07406405c0d4809000401c2a080c0410186c0e07601805540c8032003103107080c002800140041040300500985904119000080207101a141116900c51a0400c042d0307901c03004071900c1d94020f20140c100b00c0310300441508140c031640a00051030a945080010039511903184083d104044c4d445035000c2014403007000070034069000180400c504105a5425501d0b6098460713180c240c0340002e580983c484242c18004200422107010214000e141e10601c07449104548450321005851200c2003001040104100e80d000b03000c240d010f51f603c00d91100701c02641d40007803a558070300b1010103015282060150b0a5038100007 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 589163776 1250 589162526 589162529
    0x40615060504050f0f0901060309060b040b09070507050106080d0f0e09060f010f090b030405010506130e030307030b0d02040c051305061204061107120903021305090c0f0102070306061e0b04 83
    0x29100c00b0b007040d1812081004c000e0201601a8001620344403051807540c038010000e001e00300d580c50000e1000da06080907002c85000c8000640035030b00c0c0c003210015581e00c010340160310118038a41260303540b00d14035040b8054005a030181003c0d00c80d0b000303150b010315001080140140d10301e54890310101030050800100308825106907401400b58680b103170195105200c141003880c1380d070818840966907030703030000c5041d8012601a50140d541e00e082c81598a0000d40d03070f040343c1c030240c0800d0000c01e00003104030703840c1d01c40174207140c0074180e545020541d41d848081c50600001d030000d1042101604078040505903501030340c03003480c0b000c46080e070110b03161520b0810303214209100452803040d9900c1d951810010721404180b017034400f0080c020400001c4174a42c00d5100d042140d686c03507482d80c2c55807040c007a1242105d0400440d0700c0c01c110411070610000184068035203411030302130001c1c075072000050381044125000540f82904056002c9080020041f07150600464907010940655842d8061100d9001c1c5 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 589165026 1250 589163776 589163789
    0xc010905150a05070e06031807090e120708180f0d0f060b01020a03120528020405090106090509060f04020c030a03090b07030507050a11010b0a06120f0e1e0c1008040615 74
    0x1010300051801c000000c0c0d92302003014007048560300c2c1e0080c0034038a445c6483d4095407107035403610195801701c0c50910075105407070704d02d65245013041c2203030352100b220380030302011411200c010030026502035a07460641d03014184007418400624050303007015034200701c43d110141c82150801d281c00042d544000b48407904560199a01c0f22005038550320107020f8a07000e891240c00036501504080b4076a450380c240c0203034160071100183e40f0352811080c0940000c1c168480b0080c446000001c00258445094460380b180b0119100700f0304a001750009002805a075000c445503100c00305821308441c1e09507015101c03103030003194200c01c036a4480c0c6c1c00700c059803400c841030400100184040540c903806207045031b0403013400d14004141003030203502048404c3c0d0b01ea4071040004400c0480c0d00c81017001c0c5d100320a95000d800c4410b000303c000c0248100e41d11211500d00c6c2982401c01d45914482a001340300c2c0d0450f03074134010a0680c14480c82c0318000d181840039501690388038a44245040054110800e16086608 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 589166276 1250 589165026 589165037
    0xc170601021903030b120708070e060901050d0807061e0605010e03010b0607330b040c030902100f090b041d090703110f270a0608071802030405030c010905150a0507 72
    0x50720f503401c90180c4200384c2d0650f0800b1003c0083c1811003818001e0314040d00341d2400415406161800d9500780c944040c1c0740a0040341544010f000ca502c170074288009690700040e1041c0da420b400c6c5008070081280d070171032148100e03003502404484a90382c2c200358116542640c9004013500a42c003014200d80f4840100d41d4071840030048000099030b01d0b039000340144007030314481c15502030800040c0040c0303001e00e82e90740caa41d079966051402d915041c4120702d4015868901001401c0325035001c02d503406910034410040c000c41c10388080e5224802c4818501500b00a5407482e1201ea480c40b12208150310b0320041a030803030411001a03030400d0001100340403a0381000e4035561001c0c8940502411110410456801c981c0380c6000f4000240300c0040c4050b800d900398105403207881c00c1c00c01f11044611507000016079410203401002048a030f40d020b245898254031005969490754a0402d1843c4200c50001040c4c0d42004025014420042168541e1a600e40041246a600c01c90920211390701214104007192 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 589167526 1250 589166276 589166323
    0x150c0105070e040c02060c09240a1218030801090b0409021503040501062304180b040b010807050d030e09060315010e041b030503032824061b12030902040c17060102 72
    0x9008208006e4127100c12100411800c110414210740358000d101000100c0d090507040d41001c1d00e5485004190380003421b03520302c02001644c00412901d8117102c0d202c021600d0f1602c0481da0790301c60307014081050b03009000180c94000403040c00309603001145c090b11154607012000038100034400c2d640c50760a90800c1c1e01d1050000e03110400000303003180c2d01c0300d0841c002c01c1420080042c041c506c006010354064801c00c04258540f0340c80514000745500014005d41c0304c41c0e266400690080c004902a442c2210a812503549100c04685070082036500d0f149070088001c000106000c0340841e044c0154007491070558952410380180c10300106601c0000d00c6540b0400028110030702c0318414810004141da8000a2238442c003c0a20035120300640c009046010b45546904c03205d040c003107072802010035003004840900d0390221000c1010f200388003d8203000a512015007030510940c451945182e0080c03040001b000030340002403445003d00c0d003a10f8003240a4007c2010356000081d42c107004400180e0316500807 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 589168776 1250 589167526 589167529
    0x10050403090603051b04090207060b030d0903060e0a2108100308030606090d140106080610060f08070c0b0a060501320c0109080304080705070f03030509150c0105070e040c02060c09 79
    0x901c0002c02c1c074a610800c0c044111780081525000388020701d40b101c0d002d6211001828a801145c1406401501caa0700440625161980011882c004c5036000900010f5400750406218204001c18070000c000c540d151444602d9200c060128a50755087c581d00c10070190b99000051800c0c0b030207070001500c0c1c0308051000505a00e010f20040c000400d001c0c16401e07141440e55100301140000005641240e515198240710400013000721541c425585005107004a18008001d80038400101035041001078002c00504100d00512010406561200742920185082c00c4400011b00e0540a0180001da40030907200c409050740b4030b50410b880c8010780740d80382800304443c14107156002c0c042c20713900c03552203001c0f8402141001028620482c01030306203d07034800d01361a2180c2800034036084207045a01140d014400f1030f43c4202590907440082d034001c0c400c1441c400400c501402100329003c2d1541c2000e041000c000e601010340300e9292030030b840600030704016a5050783c50b0481100d801070708250501c5009544d = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 589170026 1250 589168776 589168781
    0x3030c1101020f0f0105090c09040b04020f150304030309020109060f20010b031b0406080a0512030c04090c0f0f030b06070206071106030c22050907030b0f030d020a0510050403090603 80
    0x11030381401101d2040c60124919410600d4440c001020b9075074560130462034a40900c80880340020840b031034162460541d80306c442480014002030b0240c04105c114400c180c40723031444403440b071201307000c495202e10381450001e000c1d141c1ca1000301d0001c0d1000000003107440c09011a08600045511016406540340480290441400c1c4900300551b484819480c40340e00c0c03d10032104a04031007141082c41500c0c5000380303c140d4000d640900c0303141e8481141c007c042a80400d10715081c22090210759030760748640300b0704280ea0280390842c1081c0d0f45405040e0401d0781e008404060085981c0e2100c61896581442c19801c64180090568002c40100003890051828900401710b1a01c40c1600c040c11104100104410f500115003450342014000340c0c120842800d0501d85420a150a07002250079080c00d010420000001e0240c9041c943c490744442c1c80c2d0b50300c5410101c2d86010150895200201820000399200e584000640c0c4178051250401c86a07606401118807443d0941c5070b83c500680350071800c400 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 589171276 1250 589170026 589170053
    0xe040809040915060f080708030a05030c030601030912020a030807050c07120804170303041106040311040e0a0503210121080705250303320a020304050306090102031f03030c 76
    0x61090240e03e580c06400c00602c20080908005c03a00f00724418200a405464240c15801c0074034035510034001035151550001c12658040110600c641d105e40395103006030050a00c41200804040300340480110b8a6800109501054002c0e80d034195280c81e083c105540c2c510408017099400d8001c001d083c00002c01070520b06102600c2511402d00e0550f40d1444810f104d83c9002a004550704000300303001c148600201c4103401118204d800d00d24080c5165181c2803d00e0807442c403603002c4c80e00c801c81c405080a0522865140c030b6042800e40b6a5040e500310b02078400a0740004440207211043d00101d24100181c0350407122417201483c4800601c03807500d440c0003039007001c502240e01d803090506c2c0b1488100220401000060101020041e01d421032401518100858044045041364045801e1030312040b0510315019400d160369441d5289031491040342144034981103140c0622521082c0088201e05500070340c401c590450038101c0e41c0d441d0000f06090200a0304c000307000a2521507610011440c2d1698040 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 589172526 1250 589171276 589171283
    0x100e180c030a0308060118180f1e0501090e0601030f0803130c0308030106080a05102102040510030c08070b0d0513050f0a0506070c081e040509010b030a060e0408090409 74
    0x8401a40c0200064a00040d440c0c04038001041c080500400d035811a8280f141d400f00e51904401c01810119000c1c00c00881d64001e03c1c011341c48241503a42c040d840e9014490b08462107800009409000401c82c0141c1420310584054034070303015102c080d09501040640c1641e0b400030f0340d248075800c01c1d10703000308076000a403545003102c0c00f1034192000501e0740c080d800000d5103e501e20f19104d41c03600c04060080714000700098882401e103010405a01503000504d4107403003220300f100301104a81d82c00c483c440d141c0d000b13001350424905418450000404104641120310440051034010748130800700361510072510490640d00b80c03d0240703061400c202c0e00705580c002242c220948502c0c400e030321801c0c0303061923000f4551b00f20340052402805028050010a0b070000d02e505018111008a64a204851007008451040c00020941120612420804442c01460f006010080c00d5840d690350003003640c800d032002d03440340c2e1078603c0c00140314401d00e00c2140702d143c10032884d0382004400400c1c400640311014048 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 589173776 1250 589172526 589172533
    0x1020f0414190e0403120c0e010c060e1002030105040e2415090106110d021f0203040c080706021c030504080f090d02060d0b1903080403240c0c030305100e18 69
    0x10a11490380091000803c10b1040001c041e003400c0c203001d04982402008031000504100001a51640040c108000c02e0300a10384444443c0d900d00300300e0001e003032801c480d42c4030380106048000051210380196058480c103c0b400c100c45203010901660f00e1b8072480007071410001c000800c01c020131000c021140d1041d480815520201e240c540015410392090300700e500840da90307500800a00504010700504125203000901800840c04a69080ca02d00134000090322078000001508100c8003208a40003851000122544242c5580c4003030340304c0c0014040c45070201821000c05072014843d0058034003541c0c101001502c1c110070b00400c2001c9a0000780081d81150402c4c241c0e00041c2c484100400b180801c420300003818902407001c0200f92000c0803290356003034080b0001440030664441c00c5034122640100d44084ea0010b510410942500f02800c03a0200c031b14080300c0840040d04202401466446503604000503130310340c03010421420040c0290078980005400082d10035000100c40c4800010540c100c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 589175026 1250 589173776 589173799
    0x309351002030c0301030b31050102070f03081e06060711040b0a03030509040c0203072a030c0b0310080a03200a0c3f06091401020304050610060201020f0414 69
    0x10100740d0340b0a0350b00ea00e480d00000010418049040210317900720303960090640c0c0c03400c074000c0c0c41003c0d280408444120310f403180c2c0c269400c101b02541294802e0f41e1080c255854815141006054800c0c101d82001045540051441c0040441c0c03400a10400740180503174140411038484084550f9407852440e0069905e06141000d5651522003c006502c282d1b1541d694844803c18482034070052180390f0290343c002e0000e00c0008a0070000d1300001412035100c428403400d0b02d00c0d8200900c50650000d010303910b00520210301e43c45480d0003148196005d090056240d591a0241551140d0f401d00c0640010458206204504102049401081c4070f0000322200d41c902603c60003a625601d90281101054032446180050030030560f022440081003074403060341400c211071401c001409000109545c4c0e035140100c040040390009082c0d000c403564000c544038985072901554034035083e10ba03003e0b110244400050503501c1402215a012440c1e400e0034100b610b00a56010b450a282e52401ea1050a8198 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 589176276 1250 589175026 589175053
    0x201050f0d0b041a03100f090b040308090601051e010807031506091514040e2701050a050c0c120c01060504020705030a091a03070f030e030412030935 66
    0x3501400800700c0c0c002548119540400044491a403103014811082c0940c221566402103a82115030107000c0001c1140c1800d440c04400400000304000c05191a810901051551200c20343d40300c5c8402100711101d9036203071070402140b00d4224089602c0340c0c02e9900c0ea0015075202e500b0b103d401003054203011800304000a0301c100c24071b42942003400000d070f000104210102c0c0340340c0301100d0100c07142880450340c800c200950000d4840d50260311000304145c3c0100e41201c9094590189041c0040c9020349140f4003443c03820b020b800e0036907805286c5414640860802004041114490341c081c900900c011100a4414052030f006144121215540d41000040c0c2d03884074001091680c0c400c170040c5540303c02c00741014000181d6600320070181c0003500c001003203a130148011030b0303000301e240c1c00e00c200d003010f400e03100f1130243c403031061900c45500004c600010850b036a000d902d40c99510a0702d07031180c02501c5032500040a003980302e08403001c0103003c41c021090b4100140010841d41e000c400d5940c150380c04031 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 589177526 1250 589176276 589176307
    0x103021c020307050909031e0c0d1b2306060901050105091009080319090605041802031f0902090a050402121b12250e01080402090a15031112030c120304020105 70
    0x42d046e40390f40d04009084401e03181c02d540000020801000c0c0c483c20700b2501c00c4042d41d070700c001c08102001e01201c4072102c2d40c0c4045400040e1070507507114200300f40860100d120745251090300f6002464522524001c84d81d2480c000703d10505a64045e5100c40c2440d04290400c88000140451901072040080300824040d40c24030060003901643c0c11a40650005448020034440c6158000010403005000c140a0b040e4905000700c031000c0090b402685a0700c0e8003085c20100e4050301044a6072010202c40064481031305d8001d040c1d004021a0501601940d075000c1c0010b80c071500c50798003070703040c0a9000615842ca41d04e4030b01d000d210f003040550b0f08000100c44440301d0000180c072040c2071144030040100203c56001c2e003900155842e440c0c04030056410400107005000041d0000348140c01c0381c8001400c0c00d400754002c00e440c1d0000421444615540e042c104c003001c05080015000b2400e0b002010000c000010441e10b1140d0340000406819800750020f581d00d40015000b207041000800030040e80c02c1145 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 589178776 1250 589177526 589177531
    0x120c1e04080c09060111070e0a0e0a050c040c092907051b3606150d0e07171207021f02011a01180b0304080408190311060103021c0203070509 62
    0x40006102e160591402c002070420010002c40c1003006228041c6454030b004602141190601000036600e5240c018150003d0090000d03c28580d00c00c403071600c0148007002504203003000d4159000c00a100f031504080350b4000c414000c2001c0c03165a03003600901071021107544e180a242c0c1c03162a50400441c1d5a402e402c005524000504800352092120380d2481d0607800b1035640301d104915401c0c840060000304000075180b030f80a2190a51000009246072640781301c942061180701d2850782c0d14107a50002000900b400743d401e05051199081c04140070f01042400d80480900300014072140801c10b0024003240e200560803a08841101c0c501c20a0b1042c104c44014100500d030004604518510481e401e0070b002c2486485c10000d2140da0510302d40c00340f0a01c0416212410742c1c09507030380d0f6242041200c81c450790740800180d01c542e8850030b100300090704500201c54481c0e035500c48080d103002032080d600d41080c04003a50080005c2103008040340d9115a070509244064147d13100c0c00c0e5500c002441c140c004 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 589180026 1250 589178776 589178789
    0x30a060207080309060f131101021204090f050c07020a030b130c140405060d0b13020307120302061b0a020d0f110f011a06040e0117070312050405011202120c1e04 71
    0x100612581d01024840b1a601c200c6a4051b2400303468800300c024a180303070041c00940718142d89212803525900c244010208081a54107059485030b644250300020242e031001e506e051803400010807031502640040f24656900204030100050542c2c07185407890801410140c254511880008000350381e01e000303200107281005a224865043c101841309030344004111910540c1425100000250b1485e00250442c0713006038900124000b51000c24500011608081c940708505500d48003090303800070b002c5124000114800e00c1c1c2d0328000825030050302400104c000076030040790380d41010600c60704180034958001d00d403160707141c0440c50345213013042c0d4460b6108480d80d466480c1540d0b00c04840d180e0400d203900994580d45001d140000070039034204103004155051410760b4058101540801c0b0070005143c100c2580340d460410004040e1607644a441098080f81d00c108420041042e86c0c4203654500355040412582c580c0d070311511100300c0d03001421001480550740c588080d07a580000c00f910141a1 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 589181276 1250 589180026 589180043
    0x1203040e09030d050603060403080c03060604080a0f02010f0c150f1b020a110109030b0402091b030a1a0612071218030903060b03060903192c090a1a060702030a060207 73
    0x944900f00002d49500800e002c2c040da11182c1030100203680f180e8207079801540c8144098490720b03101300007147c520480d441702046125a0202a007440a1604c81d900036a00c00d0f02c0d00489800303103941c103039070003d80c00202078040080030f0f44011a800c0c080c2c1158524171a000000039601c170712065849600c084e2032900030010f80c0494498410080d81c0c0c0b00284d51510242088a0018517580e070755031032450002c1000340a007000c40f000c00c0c242c803160010480708441043c810746d180e2800d020004000c0044d034086020801902080c50402d052040844980b000d403404180001ea6610340281d480001aa00d610010743e03503482c840200640401819140d80d22940d5504900ca1450600300c0c1035403040a0054802c3e048482440840e50700001121410090b00b00c0c181e40441900000381c51540500f28118025075507030498000e5400c802d0280140b0403012188141c040d101d012400703045880401d10100c03c588068900051440c00030040c0844907c01030440b02c1070801a03640d07034243d130006502190020b0 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 589182526 1250 589181276 589181287
    0x30f06020a0e03010612021309081b0606150403030e0310020c03040513060506030103230a11011706010e01050d230907080a0321020d0e0c01030b04090506061203040e0903 75
    0x16400b81860b0a4460114000d000c514180107850150002d2054002c0c480c3d440c070810b1030b0780c080c0c003904909846500429541d44404c07505644c0d041000e200e10265425015000000d80185013a0b040e90704140b924114080c10b250841e40e0039210b020f1450400e80c0e05100e490803100e8900e07070500042c001e4071800c0020f59144c0b4549014490140c0d8594602c0359410708080c02403045869882c19241101d400000d010184051440254900001c003201c100d164002ea00764034003400703804221000503040c01e9940c007035007083c01c082502e40d051013622410b000407044034400440d0341c07054026104404c2c18410000e81640381062000350140030b03d501c0071444581c001040403020003803201000409003400980001d00607a50020b010880c0c40940c4400e03a402d881c5030100300d0005074160345405400107010050001503000c9103540d05080380c41640000c0c03c0ca00d08d07a8007030411b806407080d0280d01c0300c01404103440708404c10401c4400000c0221b0030384800c0c8800103210390b0044019014001103006180c0d80c0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 589183776 1250 589182526 589182547
    0x1312060608120a051c020c0a15060501051e0a14041202090708061011010b03010504050106060e0a030c06030c140a0210200d050a09020d0b01031203021c111e0c0f0607080f10030f0602 80
    0x10ac00d241e0106061103400d0240d021000180030225104695124019940349001c20080e50a01000c040d0309001490110300421700480b404410b00c9814000c80c0c06500d190b455a0085541d040110780f03070342c1c1085a100080d00402e01032114141c0402e1010008100c414048011908655040360203860580d101c00e0100b010b550004541000c03904180c640c5000300d825925000288030441c480c420070986d5600448420600c50300c0003811400b81181040e5440c85440e20080d520b001c20035076070130000d140841c2904240141d090303c4424a0090360424201032845d08903200a0000034006a046600c0c0c2d191100165200c4030003030005403180d80000c0c40e550450828420445803075201c0c0080c548108038008c0d544448510145084145280210304061411a0b400590284030712801084c02a650950301900c0100c2c080c04c65035180703004a40d140145400d04a42d074500a0314200040303040c4101050a2910a1039242e601c0002c540c0701001e200e40e02d80e2802640701680b042500c91503404254140d16 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 589185026 1250 589183776 589183781
    0x60f10060c061a1801051503060109120809040903050a08010611191505101703131e0b0a09080c060304082203150e0c030615061312060608120a051c020c0a15 69
    0x400b81c942d687c15080d8035101001a0400382d06004081107003184441800800c03914904031120960064014070101b1170a1802034460f8201c1d40c0e8500c08622210004520f00b845808996001c2c59048000d144030180ca0302181982200020b094440030080c80c206442401607000301ca0060a1400c0b4a5051501d40395001e585801100b1004090f90810880b040c203014580c05107105442c440e03680c203508800200074011030820694060004001c02042d80d14a4a8004c03000c5403c4400701c4042d0303240401070900304641d5100031200104a03042c28001d54003012400e04c001b82140e41c0c3e50500c200c151791291a032210500750340142901c10760b01c44a0400898105200c0c1d000095800d4009000c42e0804005145401054600d07150060001040c4c1d000c05094840380c4030010011341800a000b0366203802c1c0300c4060141070099800901c119030807039400c00c801008031241101c09940d4241400c0d040200c00e40482d041c0c03007001183c2c640a1080350600a006c1c80201204e070701c1140102c20300c1002100d51404d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 589186276 1250 589185026 589185049
    0x120307080a060b030103060b030c0415050114130b0c03040905010311010914090406050619140301110406081909080d1506051213030207080609060f10060c061a180105 73
    0x1c070a4200201081604442c1d0182c0341580d0340000c0c046840106000428070f4400303840406944642040381c1640d0009a80003414181d85084e60f400075a0f0350407d1024800f4451028180c001c07a8444104000c41800306001d05041c090f10070903a032415030f589011409540c2c0a030001d4880c0c07158a101c1100310b40c2c100b242d81e0000c0c142084480c0e03942200320300190643c1001403003c0c10710390711100060210355942413041e00400348502e003031800b1521540030141400ca4188954040d6203030407540032488000b00c090b941240e2050383c071400d0507a07540c682680c031040180310078008542c036140200000381b560701c003800014034007540c00206c0090a5050980c003500d2a0721070300a01008004038a2274005100d40c1035030160b880004100000c456140403858007005502c00b042c14041c2405200e0323171941c01320720507000380d020143d00b0131246c03101980c0a103412b01c54400c5c0008a11100c0c2c0300000a1041d8000100510b16400095810003061002c2062005c00c01001009541030400500c04c03031900344140f84 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 589187526 1250 589186276 589186291
    0x2010b04112d0c340b07021f0c0c0609060507031d0301020307020a031d130509120307020d080108010501050f0915030d110c0d05100b01020f12030708 66
    0x318102641060003a11407104100e411516403154a038080c1c0c1162101004010b09840d07495546a9a1107500d840d034169684d0b00400300f8035480e1302002e840c00c400e10307240040400344140140c1403034401501000e41c41007000300d801c542c0c9030546041c081020100d90032420825250020752415925014a40390a1178205009104464405020a03680803007611025581402c102c240e1180c00028049050b81442c901a0300d036000100b041201c5a0110396851414441c1e1a01c00612045640904988004d10f01e680e810004284810344044001e070001c61700041600240e403e03071340e007a002a2007240c0c01100e510025910402c56500903e52113401e27180148228402007282d9414100040c0140e01d0b5482c0c218414401c030341c0840e81001036211711074900c0d50b0003400c844c9940813800000c2c003500301c1c021100d9668020302800b0580390a1001c2074040c0c65602402410803040c4c03400015005080070b8038018110b01c158881144166401c20400820b4486a2501c0e5117900c1e000c9001007000a0091a04 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 589188776 1250 589187526 589187531
    0x25020105010f050d060e0601090b0109091a060f0c0a03051902071202040207050f0114010e0a09030e1201090209010b070c0f03030e1e1305042003100b03030403080a090602010b04 78
    0x40000c020031500040503035104640604e4458640e06100c8003400d0110010320081c0505000000c1101003503101c0a40d504d005e88a2200440da1010141d00300c621390004c0000481c00144814464a0720030000c0807902100c28200d410204445d420b18a048146541180032800000745c001116458aa084605038800d00c001d040d41c90410464203a0302e030703403c0c0d8000d00032500842d11000b00602800840741030a048002041580b00700940d058290f0020321aa01030403440b600403860410450156220729501620354160042c2d00d1028011892401c0300c070465107560b551110b02c0143d0303c0102c224020030312403000740e458520302d00f003000c03101c00380b81d112071802d00c207071941040000d41041d8486602d820448210040341c0d07071038040c2640e03000c00c000761720fa0081c0c400c1c21202a02e4030720f610081c00703580244c101c1031104800038090381c0301c10300800d4070320b83c181d1084000300d0400c12641c0002c2c160090207810b2303d04044d660b9903041585e800582216012400c681d105100c1a42d09210309401c007541100c05 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 589190026 1250 589188776 589188779
    0x302010e0a230325061b0206030403080c0f2101080109020a060f030204091107030f030621020307170f0c0105120703050a0605030f0f06010e1501262502010501 70
    0x4248807144401d25030009500b101c10302d1006950140042681282e00104003c0030b4800c3c040d5611a103491801404041030560711001c1c00140c6001c0340200c3e1641c081c25240c555200c0d91001c0c2c4195400901541001c401001101c40e011841c4002d400e242c12400b2036681008040650840320010507000b800c050303031400e441040540ea03084402c20864000d4280724a03403426491040b00a48101e400030441607050900001120698100400ca118003c0e030b40c0ea86200404941102034030464412104156035625140700340b5641880030044d2a1301c02811039200c03643c0c8001d01540c0966400c8880b002e41c00c12000000807000038840c1a101c0b240901e4124a48080c100589a420b9005481441015950070000e9000c960f02e6204102624005089038140c1860228259441c4030744501d80b8454001c0c50300000300c04a1003110fa9015608a00304480d440c100f880c011641000050050b04211004246001001010030906401104880e100d500b5000418a101034800c8400405908580c5000c00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 589191276 1250 589190026 589190039
    0xb061309051f0302220501060e03100c02030f0d0902190f0603050c070f0501091b0602010e07030510022a03090405220303051503010501150e1909150801150302010e0a 73
    0x20254207a980c100d17070f0089208407050704c00704014240580c6100a0380b61000203d402d9800100d0342c0d400c40c0c0704804440c950903405ca030a200380e9102000c01000750b0700030f01100001a071184060100615004000580b0200a400091903249150310b10702181c82e20b8001802802c940d0340701107024100700e050900c1075007001c90140800d4400c0180151180101c18040010440f0a422902190740c2000382c0c1c5000b08030480d00a0110358061194001540c41e1003541000d40002069410859802c04080c01d03080d0b0019207004080d6020240440ba80f07460326034080ca40584a51502d1a10b08040700255107a084c40e0041c041210005041c0c1621901c0c05003002030b072000014007000100f50b141c540841c1c252140111060764414841c1a1135140d42018000300350304803a0013020b80c110400d80e50b440410a00d8a05121004100c501c142c906588102c6017440303032400b50f8102d41e03070181c0c540310b600c40c2d0301ea0345600041c02c59400e01081d28105407841c3e810800e641e803000d02108200710460b1061209854110b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 589192526 1250 589191276 589191331
    0x60e01060905130603150b0a0503120904020327030a0f171315020703080901051303050a0f091206021c05430903030215011401120b06130905 62
    0x80b8680c0b0906402459000c400c2c040c3d000304000795440a00c990a598070340140c00080d04802801601889481c8400941880c0005030001c15080c101203a620b4206071000340000b07948000d1000300c8150f0343c500690061a040f104d41c0711181c0f003c102841c0c40307103414180144078400c1c0841c00e04c2003181c0800d0184803407107594070b200c0c0c00c031803640d003c3e8016210900c3c11110071002070800540c1c0c1e6101040102c1416008030b0a07038440d4a4101c020445640c03081414807100400000250004070140f0030000d031035010b0b00f0100ca01c0b02c05410800c0c919942c1d2805001c0e481d4010504075441034010554204070a034100c103110611003400303000d21040c585814801061010350031f0000040415440d0850f042c09442c10813141d0206c4c0f0b1881c4038036640344050207804540944405c40044c498101c001e04000b800b11010b40c16071703509501c08104207124000444104541d0303510300386c0a42d5540c006074100c1d5280b6000b812101070741c0820030304035443c03d541c000494900030507221000302e48103e064020705684 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 589193776 1250 589192526 589192529
    0x11509140118060c05011b080402100e09130506060109050112090609020901030503030609070c0c030204230a0c1101090209040602130801090521070201080402100210020f030a060e010609 82
    0xd400c94250014400300403204410020700201c50400d1400c40420541c1e40500e000d0781043c01100203014000700c1410a405002c1d60b2034914002850f03240100d001071078000c0c41503507070b03007082d10703000700c10303401540020300d10103000e94031010182c8a00714004d082107000d00049034001070034240514620b1500c3e002074081440f110f01e04130300d1a69802110100152a80245040307070f0050503c42056850f4640035541740e00c140e81d414400c10100000842c414442c254203100300c0d51040700320b50703614610303400d01014000c102c80102002c1c01009294079022400078407140300c2c103000c80c0c01042c210380c0010041c01102c0e00e140e140d2102e9040c5134483c400750322074038003017038105500c0440160303602c440384e4070b61402c3eaa2580048010307508119128051040c00601610b4405121440c40c65030b6101c4000906c40b4451401d009010401c0000020007501c0d0046605001032214010344000ca204035074114100da200c2d421441403050040306101e202c4007540b0a060280c104044111415410080041c102c110725 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 589195026 1250 589193776 589193789
    0xd1a040b0d0212191527020d140f150106090605041806030c030302010c1d030c0904060e10050906060103050124230d0b0613050d02030f0708070303020105011509 71
    0x340d00f40b2142602001004402d004070044240452100d1074450109540200c0c0e6524035410118a2600348620b091601e0b40c04201000c074021181c210703400d012031840c40c42d4065901690508042c0c6001c0020f00c460284070012801401c007001901078003000302e04041e00220f04000f41500d003441000d0704001110195401800c0341c1451001e81884a00500020742009080c00c11018000041540541141c00d070803d06031194501008614811100d1300028030009a00d5072141c0502001400d0211025800c240074004c00715482040801c658034001c0c0035451071180380c0e507500c100072404209015113900900300346018040d035458881849c0e483d0002d64104000d0001c070341841c01845016140d01900d42d01c1401184059038902c54a06e103ca070000c02c00800e00c1820007503c03600030714120b0212140304090001c5900e034142403c041c01006200760386c04980501c1204803000f40d4110400c02080103003007842c0244895401d6150090a450060740120942c3d51000e00b401026a0080c150a040d00c00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 589196276 1250 589195026 589195039
    0x903050708030705130e0c0a0309111203130806041e0c03081803280b0c0702090a0218010e030721020405090a0201170403081302010c060f1d120d200d1a040b0d02 71
    0x1414810304903180165013307400640d04484083c0014040301502c0ca040382c0c604806020303503071030000c16110801160f0003006103211541030906003d0b03074005850860302400d4000e02c010f1301d80c1c4d589481503101c45550010b4040c03012601045150070000c01c4090785009400d807010124046c0343c0601d0448140000303054841030000030b070392501d00e602682c10b079540042074012242099003081009510040302144c2280300122513400c154040e8a42c0039210f0400380061844529094140750022600c582c00c071700da902c01c072039401c1c0580e41c0d0b070080a0080748508082c1c101c11703600784000340030146200c040d04e80c098000000c2201103030700001c1003070303110088031440c020702c0503a440101c49080e4074802c001c000d9403400d64203100144a07075101c10350280720985961401900846481e60b1078650070780b80d0b242d07078a08101111440b9007542242c0c80b900d20030504c80c00034160b00b9101410700d8000b050600c8215903283d80451500700c48507800803a00405503410070120100c500072402c44165000068080c00 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 589197526 1250 589196276 589196291
    0xd090e1b07060207060f0e240702031c1b080c03130f0203010504031d04090809120a0209010b22030f1218060203090915010906030903050708030705130e0c0a03 70
    0xe000038111090150700050031941c82c0428504080102003a21448607207a213405441d640c03807640091503103000005410080d4800d030f103003070108801d10340042403041103000501101c017802482510840d80b4500d10000031948484100c113200100820440f600c082201304000c2c0882c840c03544088a130002070b1103841c02101940e60908804811100c50003c2d050740c42c10b02080103050384007896000030b12582c410620700e04e440d50f0030841940d090b00d07000340481008110000c03007440d06043d401d00c1c1e003050609481c8120700300d40000c0d00441e004d03400703d52418000034010420f43c5410102007161103d0083d030000341815919203011310361000c60001c101c0d0800d4002d07480840c0c0548a806522401103100501240d11403400070344035040170508501030f603c0800408ca800032aa158000c8001c010b0399020060b40c500342e011401303803000401c20313003d01c1010846000407480d03030001948100420344540e42c0d1010400b440008021056201540404251050007018a02e41040b1121031416180114116 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 589198776 1250 589197526 589197571
    0x120c02150a020a1403031e0618040c1a0c0f0a0c0e0406060f1412010219140f04141314070509040204050a0905040203100c1707120c0e030d090e 63
    0x40580c0360003401c03204d80000107a031885000401144101e4090124000001d034806100b0010320046e6107003076024102c5400c0091030300d000c500c036944c898054801c0c00003459865000c1e14070451601810000380400188100200e8010020030468400280040001c030246480783c900c03005030b074000c41c18005000d02c0400e0078003a017908003102800c1c1c4243c00d120714560701c220513505221402410340c0500e0603540312505400c4180309840c0401c1400002000701c000b8000221040310a806641c84480b00c02c0c044e07180c8002d600c001820240c0710305210104030465200410a219490781110000b05040c0400d2010500001e400180c014240c0e080c0a0388900754040040c02034095a084180c002010120019112140e034202600407030090702500e0a402003d0a40c205440c950620040030030b1a60040c401498041c1c0107803580003038285041403c0d02d808102400c25070b55008445070000b0105107614a682c40c0034803966064001500308407aa41c0d00d000d00d01080c10100521501e044143ca42c10000700303 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 589200026 1250 589198776 589198783
    0x200301170d12181403090307060804053a0905090a0c020d110a050102070506040311030a0c0b06040e01050405070312181502120310031203050603060411030721120c02150a02 76
    0x583d035204c445000c1100d002c800803950380d0440c001e514400d200d81c800c00115a80110384140c052500070740900400310595074081e9225400413442041c00e8280030802d8030064404050303200407011503840c5800789207844200301840324051301c00c01082d450181c188501c41d400040c00b95681c401420500e50030410b0506090800490701406032065000040680070042c0114030380384903900c43d07166250024010094135903a4020901c50101041160b80c95101141910208a45c003d80080000c201980d0350110b040c295013090b00c04036496480b910052040002035800c5000040181c5022002010040070f4060000d542e0310a1030100c3c040d0781c10110700340c0d1007840410241b1090280b8103070b0302e040400c04180002c1052006441001c611503031105810300c24040d0710301a050060051515480c0c5807242c5e05549551003030303e41c0c275204408000171820303c03600700400b4031101204c50904100140c03c00034030314010849500c040040050300b41c40140d032801c40c41a059031310011441d1316203001c224160b14 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 589201276 1250 589200026 589200071
    0x140102102d0209030d0c0309060305040f0812060315060d08070206041707030c0801180623150108090604030f050706020f0d020405011b210201200301170d12 69
    0x401c00d0354440106014150010003800400741d040328032111000308229034108049500800060045204000c0244a0b40101b6005806080c0204402e05140d580305120340c456a81003510404142c2040700c4e91400740403a0b007036441c90b86821101441c2903000503001d41001c1380000d010000205202080d510780c1c1e001c2d98090301550050221a0f110700940300c6e594000ca210031500c0e00109240420300644c1801004040b500c0d40c929074846100556948000d4000020036150119500003101c18039109002186d0060090340c0c03407803015060840004180120040030f1851550040d414000003a40c000c82c7c0002c3c50180d858090303220882440c00401a2191008060300c209004c514411400e4455000300116034003600c80100c1908410382003580c610b074001014014441e2582600025a1115169054034115200003c1c504907903d0340f0f002c550303034040088020008080014401043d88034a010784012004001f08007035141e10030700400360f0601d8000c1c1a1020f4451002d0030f44040c801d098040c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 589202526 1250 589201276 589201331
    0x6030c0d090602180a0603020705100209030c03100203190e061b04031406070305180a02100201020f03010306091217040303021602060d0509010c180b13030f0f0501050114010210 78
    0x540e96a52a0b02413000c0300c4515001a1007a06080c000060b054005d00c02c40b11070f10b0780b141c00752000b02c4801001d50004d4101c02409a00340c0221401c00307441d135400340b1494100400803540180c503402c011100c0c100007201c4c44566442075142c0402c001c1d180301c001840310781c440000030000041021488002e0a01e006544c80103251414007041c01e02c03c00f1000c90307054450542e41e58100069601c0b00c040300e030800041c030607142e0700c1e401030000c0c1b0340035003405039040c4881070103400094584601d180d800341d01680268800e4890741c5e91000250108959002004465030740343c98095441c08614003424a41407000e80014145940000c0c0161503620740380303034200b18a0300149010346801c0100c0d00c2002420040390407001d03651034400f180840f28040c420f800c4030150310360040e0710070504110b0b0014842c0c1c0800c0c480b071031041d0031400000004211103000c490142c030a0312019180c00c0360789415400c0d45e0068005001148801180180340d90340000c4a00d50140e07920404100b811094640324900f010703540b03020 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 589203776 1250 589202526 589202531
    0x30e06100e070c12080703021b0709140103030210090606030b0c0c060f07090e1f12060c020d050f0313051207030e1503010b1b0106030c0305010f0b06030c0d0906 71
    0x6804104840d044044524001c4401a00c1c0d807020400c480c002c400d03034801041c0844c480e07405102580300c1c8501a43c4001642001454650044800300081112980c0c045d8164000360043c0003202143c0a6143c285181d0724103001c642d41550b9000e503c40800007801c0480b00d87d2949800b080c001d25030046801541c003c10081c00d1420701044062481e400f003004d20301d90344502000700780c11501d4203106510984e00c9549480a050a00c05050f00f00a80a004e203903102402081d0b500901c4040c41c49140184a088a103040e60242442c0503400d680580000409640040460f4041e19401c07404881c8160f0000911581c5c0e41d896440130f43e05a005540f000e0414801c0c045070000e2260030000401000b8003a48428091f500d8443c100040c074000d100381080080300c2032004002035214000503000c2e400d40241d40c404c603003458848503400c5450300d5000b40ca140c040e425040050003028403802203030758040034040c00480918000718007e44070160080807012400541d044111002d40c0c440f0310003d9118030103 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 589205026 1250 589203776 589203781
    0x50717250b0a0207120602090906090702121305031905070617070e010320040f080a17030403270608130f1709040e0d080915070309020d081b190803010b0307030e06 72
    0x94008c0d041403081e03038020050240818498601111403611a0b070841d40107120110740c10b0108400c40e04541440d02c10712086000208155609022914038161000d02d060103034000c03810003914109150b0301c00c0b810b00044c218445004820160199800486ca00302a411504101c00480007041841f840009855145440380c98005002000b0401c440328540c11303445d0941c46140c482d40361003c8200052101c1d20698404008180c0391028543c403d01070f060a090104440a00c00703041c0032000542624540c81000c00d001e0142c0040c12241c01c4142c4c45810070400344143d40340c3c0c017282030301e120148c140010280c035100030015100c22201008000f4009001e40c0d0600c82c0c1451340c40302c0e6100c4010214500400088107003600103842c00b440310701e030b0309429540e869500301603005000f042c0d01aa08008895624004100307040002d09043d020040c3d41030301c1ca001d180701e02e810428040030000311015070500e10000b18845006480c1543c0110002c40e540b030b116400241c0c000d100c001c0c05003503d802842d08 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 589206276 1250 589205026 589205033
    0x305060f010303030609020c030d09050a0803040501051909020934050c010c020613110a03020d0318060203040503100b0316170c0118060e0d050717250b0a020712 71
    0x11041d0480c0d10a0302c0503c0503a4540740b6400c01c1c0d014a01c1d0390704c400e03441404400b1000d005900044e60341e60084040d14441c19650b190321245600441e1305440c1c3c0e039151403d0140150400c1140201100c1c15a020000c602203a4005100544007901200355010808035605503154441d509882094150502c041082000d150181580e0032003181d130318141d464400d500b412030b400418158030803001d0f8a040c0130840c0e41981e9035545615040341c01078204420040100040c3ca40303c6200c80d00a0098483c003480c00c49489039040c004500d41c103c0d40454000f81700801c080d40380090446100924402c01040b941c003d023011901c0c0142c000c011101e03440000d880000c0403c3c41003241c420080141b010303140442503000054031428007044440400e005800410420750b4070400d244014108000c00807528030074a5280e0704e241c404190815401c1b83c042c01034510303840b0010400c590034031041c03210041d101e0103460401c04820216200c4d000c0091400280108424401d00c5800003400120848800d5000c0ba800c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 589207526 1250 589206276 589206301
    0x305091f0c060f06050a05012106030b090c030d02030306060c0c0904030302130e13060b0429100e0f010f020703050106060203090f06090d02040c0504051503061c050d1404030506 78
    0x400035140d551410303d0306481c485140c040d04042c0d860180800c000c842c40c041c0115500445071801032051045032841c401c40b0501805a800214050603007400242400a856810b00904030400c078880d40c0400155106a600801036960000c0c0499400f070b2141d21a0004508205400402c40d60000e07051042000301500742c0d01500350340000c6d18000f00301d2911568601c2e0300000070f541103800c0720f250881c0d050004220390426000340e00c01030408613030800010102020810305038401e0a8030106403284c07400354180f480490300849528500f941c4241400008107080004c1251651704111303c0b4281014441d0007044038a00469000000704031040d0303660341c000c0d2a5000310043d548620070038007040d81646070a00c00e03143c1c1c880008100717269003030856003000003c0c050300c503480c401e0001c01c0c4000a0695201d078000c503c074081c8100b11607541d242c101d04000800c03480c0402d54064078804110203020403c0050102d03807415680c01c0035000420b214901495900960740b0080c010722030201089110401d28 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 589208633 1107 589207526 589207547
    0x1050f190c12050412031a010c14120313031d0306071d040c0207030b1b0711030111180a050102010e15041b03050604140d0504030305091f 61
    0x2000c0c82d0b054030011282980c1004008110070701e42c982600600e1404481c900540e8000400d034800a00104003c25016140e00388441001e04009000c20035070f40d5400030101050b40341c2c40d040ca10041c0400c0307500c13003c80004401102040c0720003604900034411480040c040c0032180d99400f02100c4101c0c6040584681014032500180591640d124180f0802c000340e015150040c1503092249550300090034003040c02d40c42002c00c0034007504d21819030701da50f40d02121700c0c01c8a681d07290000740034240c50010302c40d5442c2d0004001d0300e5014500d6201c4111082964072082030350351207006900b01e44418156070b115070000300e01c808005544121056004c0d10a0034440740031400803405e1080c008850300304440c5a40400c0c01c1c802400380030401e00034030300b0740740e40100305001949400400b0f601807884010148040420645180d0b500c07984003071000c070010390340c448030030108190080c8005c034407 = true := by decide +kernel

theorem cover : BRFrame.Cov 589028776 589208633 := by
  have h0 := BRFrame.cov_init 589028776
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 589028776 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 589028776 ≤ n) (h2 : n < 589208633) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
