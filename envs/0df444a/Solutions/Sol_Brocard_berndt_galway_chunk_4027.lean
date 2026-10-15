-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4027
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:22:07.092249+00:00
-- url     : https://prove2.me/submissions/90156c69-a2e1-4783-912b-0c1754058907

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 724100719 ≤ n < 724280575 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 724101969 1250 724100719 724100747
    0x605090103020d06170a1202010204120f15050f06040b0d0822092c0f0a032601080a1208040b04020906010c0501141906120b060f030607030e0616 64
    0x158a440318040218044c05031030b084144006148503521050381800610340d60303094090403401400c241002000c0c0c0c02c0b44164095003140c119030690401c0400d60400e549424544188017421040703c11004c3c0e142204c40913901c80d090785002c1400d00020749000d000d00340d0f161008641404120f40035940700383c014072914404903003508903500d28a80c10b40c40000c80c503000301006107050000184403000702c2c00e49001c0505600802071110b10059582200164200500c00408002c4c00c00b4100344d202030780c0c0c51590400886882a40f101004881c8002c0f28815000b0a2400d00038681c3c21030f20b20740310320058820429a410440104100408100360f80800d41e0011740607031303d0b04103d1729104e00483d131000032881c0207002903091049103242e41d0a000341051140900744001c00407115508201426100386106084c0059594030305030f800700e040001c0094000c40010314003d00c02c022034001c6800e00e20101d402c3c2001c60782d142200c240315003051041d698071000b41600089440010f107001340526400d4000 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 724103219 1250 724101969 724101971
    0x503071e090509150702030c070e040b0f1b0406020f0d0315030305090f06280302042319030b041401050f070c0303061a0702030f032a0709060e1509010605090103 71
    0x3c11600e00c828004070103141003800c000d10745468110360103540d9500c2044404030900c01c0b4400083c1d000c000210203405190301c680b000050340c80d00c0d03070084490ba0002d40741d040c4420007c0403010304501644020401425541c000c4d01312004880c6145051444504010301850300301102d00880c4110a0381e02e40c2600d0345410020349450892001c1200e443e8650301a90700034030b001603045202d0b413020a02103510600010b110260655070352045040e8000c91203400c807008080c1c81625641e643e91004803281e1038003c0c180f20301d480307280110500c0a92050340141d6412003504280801d201255014100034107041c1d00a011030304044600d030101d044014424810000701c40d4040c0100341c8a0340040000340000b0300001c0100d072100c4402d203001c3e0700a600c04c81c86072080b4642c9000c1c010002c001e0340c6103c0c4404511468034000840c42408103c0f081d010030059000d107180101e0b04050501c07c100181042e4081c46480d4a020340d8404049100032003030324414182d58004110b0294400e04581d07000e002807130 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 724104469 1250 724103219 724103221
    0x3011a090a060b0d0e010c0c11040903050705030301060f2a0818040f050a230c0703090e070309060b04020c060712060314030c061b03280e070503071e0905 68
    0x1103010001d02d103e07001404240b00008052810400e640c00411a00c070080d07000704942c102d55501580c40100c1940003c00041c0c20802c801c9a41c40c0c40c1d4401450f00b8020b05040e4038200d0741c0e54806042d58000d03080344010950590903005250742c04500c80e2499082d98500030780c0c0702d10f042c415550f10390710624001c003450780000e89000e0503c1d000c0c40b10101004c0191040c0840c00501c82d071180500320403035504544614040034040e024011003501000148007480382c0ba059102e000d0400c3c42030f40700180a406001034030b00006810403030018898403030101c554000880e00c0981c40d20009070b450b81104544240d00501c0002c0d081c607404200700d500101c003400c00c613008054507500e001c007800c0f003588050404142402c800b03001c100d01000518084001d8429986183d235500100880b401c4000c905c00001c140500c001031342440554584079020486081c070390210f41c013910101058841c541544d16039500602e5080040c0d00b820840d9030003521507040e4400d41c490f00300840060000c190300c90055580c1c0c40354 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 724105719 1250 724104469 724104481
    0x240c0c170d090f15050714040b090609030d0903030e040c0806040b0418060f0506030a0c0603090602090d150f020405060a1d0603041a0a0504120f0915180503011a09 72
    0xb600004605a108815903400d900714100703a142582000040c00200c2c0c20080040d03078040c400c0d60f80b6a100c00b2640c4220b4105418043d2a04c015000f00d11107542183c0f0801018030160b8042080b41d012440039030780c0c1240c017815441d0081200c2c0d08804042d00450030014100d10464000350f001b0f9015000f80e50000d245a02000014094081403190840c48282c1c0c01c045402c0c4881d03500074400e400309071001401151102400d1582d80c107000100507003540980751040c03000780e220744c00078401c190190307201505140204001503a070854040c0202c0b10800da4032010004002c4034002e902401c000c807081181054501404600c062041c10b001a0401c020140c4029070750a50782a440003c0030080c00c0c090300d80c900751800080c4400580070207151031058100148001101e409203e12895115000301e04d520070300131060b80e102000e1403505083c012420300100e0109804080300d00c0c0900305594039201902d040001110325203c0f50003050007641007291420301c0141c00f005031008982c0c00d54901d1007503a40e20b = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 724106969 1250 724105719 724105721
    0x703110703093302030c07050a05030a1e02060a050c0105060111190201020a080307020d11030c0c010c11030a03050a0f080108070b031e13140a11090702010603240c0c170d 75
    0x24110145550700a800da400d43d499001002d480d00031110300c101c9024030748400411404180601c2000d60581c4150503c00018082880f00c01c166105105503040c44d4600c1d038006009030308041c03070107400100c0208042c1141d140c01d0146c035401a5080c2806c01c0010032040000c0d48804083e41d5040b80d03514042c24800869100704610080c05400080054980c00d221400a407205402c1c810b070000518410808000410301204603490601d00800820b0340d4010f140056950124242065601e007014005040480d00c06001d094401c51090b0303182640d03140a450040d11140000807054100119a00140203500000440405461808900301e071603030b031010203866402042d40e555003903503080c1c00c0c1403243c1c6050744060014280d101c1c1100f8031109080c0e00c0f40e070f66103c941d00f8020f4604001c05100c5c44050908080d8990040d84900c00030628640300c0d12002703e0740c00210900c0501c90015481e1515000440c456403142a03140d25200c44440201d440700400f02c6102e0080007021000081c0c00c240403480c03 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 724108219 1250 724106969 724107029
    0x3060403031a0414160203040f060e060d02131a070c120203010b0a0305060103030207090209092a130f080a05100509151305010c02010b101107030218070311070309 72
    0x2004206011002001c000135030044030070768507a02590f688600c402c030a18008001d0380d0643c3e80382c41654849a1510004807040120980d8058011004000e040342480c4240014040c1c40041140c1d034035031720702d080180740c00c5001c824180d01c035070710090240000003105103072040119034003112160f04800950000038010715203d001e072603101404481c000100b0401041980c100c13406602134420403551404044242d10075100904d50040424001a42c030710f841f4400d501c00a6040c1c0c0c094104510740700b02c004295802200902d171900080307103040201031005e0b0f10100c0944400c2c8007626004026036145981d50055280310850700392280e0000d00c0c0d0070300030041c00b12108038180d03404d00c6a00701074041c00d000c0d03040c001c0281c0b503e509281d1208880c031700501454940c04000361482c058040c050714204c0b940c0b80490344045d681d001d07100000025076a031003010340032916074900015107424039036009411108800356131031400e10144186000700c0d0300402d92108460185000385215000300420f1070311494 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 724109469 1250 724108219 724108271
    0xa12051008012909010311060a0c0c080304090b0d08030420090703020a02010f0506031009061806150f1406071a07020c03070806010b181203070302160b03060306040303 74
    0x71070000f095000160380340c1502c44a042c10319015440b5000300c818030108a00901001e40401c48010000303c040c101000102056841442c042c0140940d640c2c030007485007103580c8041295403012905005200c3c0ca8420300c0c90540c02152604212009030350750705c51900005001070072817007404e078507020a0a241005610f444d54001c3c800c29440c94aa403020f0001e40010318000010761030081c01070b4411032244102805039100800602c201410146000094404030b0400c41705191a03882c1135040400881c5d101c00d0041c4100008942a5a448000240039595511115a6440a0500300141e200ca4190f503100401d0030780e40680c2e41c03011801e080007614440b4005140541344078042001c0780d80c0c0443e070766002800440036142c243e9a10074103113696010038001c068060f0f60401c10030310707101c10310380100411003170103401c80c800760300312030405801c54121050039400f41c0c00001e008a0071138601800070016054580c071035411410150003003940c429004000605040d40e40b0140d4580142c01c54000072040c2c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 724110719 1250 724109469 724109471
    0x20c0a06020406030c1409030a17160804061701060509100504030b1003020306100b030c0915041d0f0403051207031d0a0204060608041a060d0609030809070b0a1205100801 75
    0x2c0e60f802c0010010300c02e41d80c0c03c1000401c001c0c404c90405036140e007103995001000f0020702e03103000c2c02d856010802000340a0203841a404004580c4181c0030305591040050003000016140c40c6000d50141045503550002c0c4403107007501c001806003c0c0c0220541700b60000c2075809804071901080141c54522031500003900101c611010000300080018a500c103581c0f080e01a00c142d6220030700001c20420b814010040082c4003400040c0e00d030b1072403002400200074010115030812080805000e159407043e0402a05c1e50385d80e41c0c1103099200d20b01403107900405d81c1c03040000d1602c0c094800078000e010f0390b001d0f0751148640381301290005100342c001220880c00b001c8503070607140c801d1a01540e124006171049000318100100024081d004400786842150041c0108507008290303400d1510300032004121552002c00030074400c001c034401d0710039028014401c0e00c901c00745050060307104d40703000b60603800702e00082010030042503540d1f4022003803a41e040031078401080d140c4410308000e9180001da00800284c2d = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 724111969 1250 724110719 724110727
    0xc030f1c0513180b030105060a03020d0c0b04060f031407090b130803031503120306010903080a031e0e0c030a0309090e010e2e02070b011203020c030a0605010618031203020c0a0602 79
    0x44160810340c011441c01c0030f4010000802041d060500b40c0314201c403c03991240c6a50f42c10000b500300080e00c00b2205110300c207610003264844d103d11419030000e8011100107800c1500c0840115010711132150004407007441a8850300e404c080040c1403007041c0c0107560f0301c02e401149010300b0b201d070044000080c100b84410343c0e17240d00d005004580c1c2c5150410b0218070034807442404407001c025280407a0b0081d00180c1d40c1c21503007801d584a900c5d080d448500400e08043c0c1e2840c4242010009200e007000b50343d40e100e8085080080600b03261319003c0754204180c030981000b221180040c0e005040b0b00129900d0030f0011a14400049003103006028520400309130340100c0102d800e905c17034001c4d4140c503000b444100c00022600039682d12030890041000060071155104014003941d5010f4010400d03c2c1d200e88100c0340507250000109040069102e07084440750348400040c8401500a003000408407184076160542038615100d6001e1903c102d407411050640c0090000e03465042844940e41241c0c1041044d9a5 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 724113219 1250 724111969 724111979
    0x70614070212131e0b04030b0a11090f0915090a02030a0c0908030405061c230c130509060604030503071110050c0c0f040b040c0309050c030f1c0513 65
    0x4120003151910018000d00044440c0c0001c02c0d401d851503030340b588805810090800052260950a9041c14800d1030300d0302000044200c2040d000348081c40c845c100e000c83c9418044c0c400c20649440d207443d00303c288401d0041c064291985035409090070402c450042482e103500c4001e204c1d0303041e04403c6503008000c080821070904029002940a051102c03820088000307801170440f0203042ca80100c0c0c003680c03c108410080ba242106c05040c3c03030b41c00151420b640c80c1423215010304a81030b812040e958160081c1c1c000750541005803e1a60100000d080c203442e003011000c01440d004000e000b5030388120002d1001c1015500c4440655019640c4081120ba50301d0440c140b55080300100d14030144680c0c1d088100590f5240700350151a20701c00c2a4008169114680040200c01f80040f440150000e5903040302d00607660710382c09519004861500c00048048590800608101c041001e0f41d000f54401005c0c403900100005020700901502e40408020358001c070740803121032003110641d51903180211000300d1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 724114469 1250 724113219 724113251
    0x20f120d080f061503040602030a0615030f0c0905060417031b1e0c010c032706120b0d0c05060703020319091701090804061b12230313080f0706 63
    0x1c01126909000c403010f80d01c160802c82d98110310707a491a5060000d1001c01d0004420b0b40207560003a10340315004c2a00754032046484a6546010440e40009407201a480160342c480c1c41070400e28086031601042503420304001c181c40b03100e14800c0c42c1c4202d8910f954420010401e00503503054892070413550b800188a114041e0781c0d00000b80700181007803515507031401c1c4c54000080b000120941a1581c0d21040d109481c00d4506c514880111019103c0d400e000b044413580ca00e01c031a01070111901e840445100d02c0c20b42c0780c11a543c00404034040c460103038440002c10209091081200c908880003503880255140890540c0203480d40815006002440d06030388070340000c40c0400f5111540c5048540d0601c1202c2c1d6400d0300c0c0702c40b8001e800c1c107804020034403d480c402d0b003040307001004060500c48005521340c3c60031046803c80d80d4900004c0c40031101c0320030301030303115584d03080b0011a00030b15425401c2140da4107002010400c0014034548002403188001c80040058841c03403504480208846401c1400500d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 724115719 1250 724114469 724114471
    0x112052515081909031107091b1b110102030d02120604110a0e0906010504051f08010605070c05010f0e100e09060a0f180617030d0f0612020f120d08 65
    0x200319150024aa040c0d003449021036034072900741040c148000404203d0500010035002000340d04002c882580424124001c000c131800502c110b0900003014842705411f941a050058100c4003040849002103006203002c8114441550b0400540b84664196000503480c51043c7c40050303c03440e00105652540c0d030401c1182d0780c45400301361000d00000245000da02c00c0b5201d90310041001c40c3d11171060468074140050501d9000c503041c1040340c07403e80ca03000080c1d0003650080500300d500701111003a84185034440e031100c0c01070200e4200141030100c01d590b0000740f20b10303074003c050400a013405114241c0d071154105103201103001d440d2280c03101c18680010510590481500d000e00700c0c00c000708541e030800514440840300c8424100200310b0074040310000702c249082c1a014515202c01000c42d408409007060b00d01e01c030041005503500c8200e140070105440801d0703901e52903640b8007001004005400021024003540c100c810451109440b4006070940c0e0311070460005511880c41c50440d025080350302c079 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 724116969 1250 724115719 724115729
    0xf1b0d120219082701080a0f0e0109060510050a05090f0a060f03030c06050f2a07021206010608010e071409010201060f09091b050d0f03110d050405040f050c0301120525 74
    0x20001c130390216182000da000d07103110054005140c1c54002102501594091782c54120342440200300c0c43d0094829131709481c001d0740203441c01c44d5510284200c1a84040481e0010034042d5201c0c2041da14140010701425002446030302541c1d07002001070fa4110442d8081c0b40681002c2a60190458403401c00501c4071240140c00c850305440c010200c0d00066000e000300e481031040e4044090b0803d4500d1400203810034860041e0340303c800500066005076a0392105040c42d0200d100148125803520000038104413042c0d00108085041c402400742d5150701848460b660f5418002d4143d981001e000100d004040e42c1d801203032800034440c004a443d500c55000000784500840c47d580c903400d416942100c0a00d40c0d8030a490f071181080b008000040c9401c0790400c2005d0181c1042d01c05502440300302814003e440d603080002441c002001d2100780303030601c035407010a8245241000710b45400918500948418029450300c08200c440f10010000c0410080e403c09001e126550200000b0b20340c5c18150210030700034 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 724118219 1250 724116969 724116997
    0x60803131e0f060f0507171207030c020303060906034b0d0f26010314012912010e0109021f022a0607050f1b0d12021908 53
    0x81041c1c0c0000d05109403040d01e8001000c4018145000350a940354440003e9410510106002800c003154450a192050030032407551365640701101c600111980000400c520107061810340009080c0350700200703990344628240d170885001c0d01c036800000c0c5443c12030135403c0440403000b88081c081c0c1c64004ca40c0f200403059884005100c0e01400780300008107001070b1840105d9400104440c4840c4d110b0000d21803043d915060200406203c0c0350103890a02c8010062803541514400400400800134000078030004030500070007034800740c0c04203209079a030b4500c00031250044106070b10b84c00b59580304100c281130100038020401640100c02d43c5020340400c3c1d030140e01c500e24451608904541d00308180200c0202d40c3e02406000c003602c003001101d40742c9044e00907000440c50000584a0316003600504940c2d0140d001084004490591140f41c5161101d5040100c3c0301034500c90280e8555409224445901404044210008070700c124500700b4130b401166652040009000d090221500007800d42002400f0 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 724119469 1250 724118219 724118249
    0x60b0304050f071a07320d02120405031b0f0d03020c15070b0a0c0203091512010819081b01061205071509121113020405040b030a0f0308040606080313 66
    0x103070b036050013a59500c407426400c00b049240005107000c1050381c840710140f000340001e410000101c005e0148080c241140c150321551401e000319804200b00c180c244c0c00c580c01903141c10708203004607807a041c00381828203580c1c503290200d51150b42c07890025054004003400004902155040c02076490719201c1d58240100c4480b2482190000090201c0c1c0072540c02969900c180e403191174100e0028181003011600b10f0005001c048115a00c60195103945082900c00a854a142c1c0302440c00580069100902c1540f18840010700c1c40312140b02022400e41201c02c180e203444102c80ca4034005100e00100b0000d030f501c3c02a001c07452022001c030004900703005404a44d0300f140c44141c000c0d01540c503515040c1c041940400b04000001d40310030350140c0c00f44148000040310440d00003082da003e1301041c81000a030340201c2d060199003090f1091080980d011001440540007070780b40c251901c4000d4101500f0041f0742d8002506001541d001031000302400d0044070358039070300c509031142101c3c0d80d0700400d10380b800202 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 724120719 1250 724119469 724119479
    0x150606090e0606091009090204150305060307051c321b01020c0907172505120708040c0e09010f0b030a11060a030b0a08030c0105060105070c0315060b0304050f07 71
    0x2500718482d510140401d0300c0c200c586410005500310030341500041020030b00000c14001c0150015000038120810805412884040040d058400c0180344900039400040100440d80e902045075050005200807a07040340f00c581041a2074003a4140b94070744200e009030410000310301c14041d8401c2022104282c40c00ca4220310007283d0458144400140107070b000043d054800c0c94607200040d000941401d100c007920424000401ea031410840e0384c4020041501403000b003941000d461038010181505c0c0103460122910600d000414000e04081c082080c1c007000241004520800714001c3c1001c001840028a400c10f4464041c000104100e415241089041d402500340000c80115059102761203ea10400c2e84051011982003070b1007803003c06460324420121600e42d540d00401810030040511303651004644110300b51880505014100030040015202040903589010f054991003087e0750a00060840c940c806007000e074103d02c00d108000014402008000600807501917400c0c002d59040aa6039 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 724121969 1250 724120719 724120739
    0x6170105011a0f0a051b010e0616050313110901030804051c0f0201030506132c12030403030209010918021305221d03040803040306060e1501050d0915060609 69
    0xb80140004680c00d0010320b18440c5048080c1641c51514581941071080c484a00c000190395140ea41800344d642d040e141001c51400c0c88640e900117011107003a81d0414040d14004c1c840e03c0001c100220710020390302c1d032130304010346044841303101c0100030070301502561070b17080458055025100384c502c10740300e070303030250140074641030128800d650010038042803907545400650151070010400755000094404c40814404948034400141094000110000356484058050384100321a80c44a941c40980184030341c6000204580c3c1c0f2039490316025031105078603401640e25520035003210020900713a070642c040e210035039400b9040d0003800c241c1c11803e07940d0b00c1d0140840c1c0000320086140c882070180545401020a420008000b060b078010381c0c2c440d109208400303095810079006801d0030f420009080091103030601601c0c2c0501030308103411728036007800042083d5100075040d00314180301001c0b800303003651269035014151582d040310301c1e811201c403a034000400905085c004d1401017010fa21000c281c04600c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 724123219 1250 724121969 724121999
    0x7060216150f0c05100f050c0414270c091017070507020a0305061f060e0105070209150301050103081908010302060d0504050f0a08030604182003010f0617010501 71
    0x2106406140034024a011070740d10b41c070b00e42078005100d0b03008901c10004c0d03410881801407940c100c2000440403100310041c0c2c2941c0000e0700c0c3c80140c81e000c0c041070040130400d082c4142100400c480000c403a5a0940c6c0e1150503402e0307665540c03450280801040481f0052400401071050225030a18003c4051101a03d101c091038000c508225034030340000c2c001c980200e00515046000070405001c0701c3d6603039074292501d038003200e05e5540400d41c3d0152468000828510034094412410803061070f21100c00002c200303000e8684d0291040c3c440e4408108d1410030700c18900c11006012700284515a120304100c1080c0d0b00c40c11b810307030028004807030306641c00b0310034200207060302d5005149a1500040740c00020240c00c0141040d60540a0381c000540305003403c001c80c81c1c2c0e1921662649850f1b142187c100412a0008a0b51204d03032800b68604900207140303043c0b041040c400408280001c1c00758813002c640140300108100c00421f141403070109640f070840042282032005100244242d07038071540b020210b014 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 724124469 1250 724123219 724123229
    0xb0105181b0306010207080a05071d09060718080604030c02190803030a02180d060506030c0a05131508152202061c0906020d090c0b03100519050a0807060216 69
    0x21041d0103074105052100011a00050140304071001e00e0b45444c8090b0900c840103200300d44503405101d00700904044041c400c240d00b0010b22110150b80b4000704450344560005142c0003c00110450701c1c020142280c1d800c00c00b07000700d0350803512245850326005e01044110384007a8801c0d02417001d41054038050368012010f1312540c44c095400d50310390010700006900300c3c0c00b841d100600301c00f10510154541410a440e028012030001c9541d00b004d600740350901d10302c081b40314083d4040040910541c1c0b00c8071240341c80c1c582090300000707201d601d068503030412006503081040c05011306100540303400700c00320005e80114031100540c0d50f02c0142e0307500030300c200409a400a40040041c010741c0d01060310055416144044c0003008120a4950798440040703134003403004031240c590b80d14600300c1400300d01d6103400007030540c10810a1450500851205001c1c12074420700344540f44280a40d0170600145a803d40205405040450160b4403511007903141c03d45801038000603c44c50f4842e20700342c0741013250041207603 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 724125719 1250 724124469 724124491
    0x3010e0601410717042d0b09030a240e0d08130c0f180c020c011b080403081317210c1903030203150f0f0607031206030b010518 56
    0x1058810800b8058031044105082c8900305005180200d224040d0000030781d100004150b54982c10280c02e44c516030410003c05144401104c100040c410000d1b0503002921560000140c517101d610340040e1800000e144002e00700c0047e5110b442140ea40404215002e81e500f00d8240000c514507038010707035913840030804a0005202d0701d001c00c50540081c4c0d581018a4020310b1500521916508980507181441d4030005aa41458010b440e201100c0c3c0704441d1904c81030720240c01c082e41004002413034284032682911580d5005800d010401150a080700c008603404518161140f24004c11041c01c11124420784040c07245030010307450300c80d001180c1c10400000d02248030750720351201d143c540700c02e03089506487c07464410f81c0510140c4d1007042000711300440c822f0b0380140e940e15020b004102c0440403441c2c036500030700e102e050b00d0885039100101401c01840c150750807926201e1504044804000e4185085107181c603201003c82401488034882d41070b900309450903088450750300700041018004603086103500d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 724126969 1250 724125719 724125797
    0x32a12010b150f0d1104030309060302031302132c06131a04061d1e0c0d060213120c050f091e04050705041505090108072102041103010e0601 62
    0x1400c0c0440903200004441600c50b0030700005481030b0088410045c29504c0d085000300d01002056440740c203d0000d0121880e0560443c10b0105061804602c090320003071003050458130f4440e1039050740c0c3c00001541003201101c80c2e00000303c040412083c1d001007002008c1d00594001a81e004d070b0421030020034980c41b1903258490040318030b405420070b074003030400c0b1461910f4200090180e4942034009d1241003900014018079480079031810341305101402d901e031031074004407080c22041daa07120550f040d0b16041000075030b90f81e280f0b00e4600c0c1d1291003a00104c5c241796000c2041414071a44c1c0c1e5801058a4064404044c640070300003c00500000c1111243d503e10f207102d110801c0d003500d420000c0d13006441402280c0b481619100000c0964991180c3d1108154072008100306a2800304203842c01003031103c024050550030540802c410166030790103a000340842e605414210340b110340c4403510f8100c60015140c0c695868261480074040152a07031800601000090401d200f4142080c1000e0603070700b4012041d0b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 724128219 1250 724126969 724126999
    0x7030305070501020426060109050105030a030c0c1e090608010204050d02061e0a0e0906060a140f0405030709240f06210216021f08070e032a12010b 65
    0x465001c0d03003040742c495409100014408040c0c01c5000075642c000c000c0419201c448188180c42d028059202d80c501600f0400100019100480e010142980516001c1d07803b80045c14030400e10741d41d0703034070600041c1d005405152481e0150ba01100c10f40d000d074002402a20b40d0382c0071007800d038021802055808400c65202400515080006100d195100c914401c003450184e1540c1d00c0c581c0005442101240f0b1003c4641c695107820003240c0e9000707408542041c20505c80000c0100741c004950503202280100041c06030483c01c1d0b02050340c3c010b01c80102165109616000810081c0c1652102101c400c1e0608014078806c80d81080300340c0c244d40007902503690f0701d4078051044480c206261380710041491900f0340038a0403405800200940280820584603000711407040c80105015800050b210210003200914407580c07054445401070907a2920f082084d40003000241823040a089486007014039030410034041202130803007026908115941d43c00c108009800500340c6030360901855014800c0001458 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 724129469 1250 724128219 724128227
    0xd0e032b0e010e1e10051c05130f0602070c0b0a0e040203280b010e01110a12090e0702010606020c0f01080f270f0d0306060806130e03040b0309100608070303 69
    0x4480405141036905007010b2404610182e15090410f1a00c603c0b13100180003a003010000c001000e0424540a45483da00c528134100300500318101080700780e1030f4004070b1404000e00501210160b048981020605c07000d2410138020761140c1c1003201d121030600b5000441441e880292480513859880c1c4003104240d800c200402944000d04c106401c400f90720700805040700300f0414004941030703a5070004c2c0c07120b0004005440550540d030805d04000150820401c42c9001281e405100c5e0782c0314440803042590050143e0384425ac941041080300110400c02400b40d0341500503108940c02c0d0f40a03545141907410501040203c1e0f13038000c40c0411280c1020600d01035407044015030011014400d50010703400480d5240d4489c40c07011000d00168407440140c500700009000d800b5503401316041c01c00400307207031250181a03900300410740351051007212101501d0703800580048d08148802e000303072035850342c0320030007032010350401e58030385503070b4800c1e01908030308000d0b5403140c01d0a59010b600241129451650211 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 724130719 1250 724129469 724129487
    0x1305130605092517010606050403170d05090303100614041a04120b0406060617060405040f021009030b06240f0721081f05010c060e0d0e032b 62
    0x74040e02c00d455901c01c4410b250826030f071000212201c1d8100c0e291528007001111440d030210209164034144040003075a80103021902141d0340003003075001c0800d4003501d81d400c0f40242c1c03400b114142d007040c0c10002c07000c20200c0114400d0b40701d503040320040c03511000708481070708981080481c0070008000174010700300f010072403481c410300d40885039184c10344039000d40c094035a80720400c454409100051004001050041c8005030129142000d500c800041005140000c003524150086035648046010301180900c140115600940343d0b40550102040c0144100d00c00d20090300c0512409002c100545001c01e440c10001c0ca1070001444582c00508107640142d1015261001050342040481c0c002058040006981c82100c04104008100d141c0c000c2d141d0b101c0103180e51000fa201034014071200c03039a02035880554000f80f820400e0f2120750300d0301400a1840a000301e10714071416a000c03050070340c88409c010304510107a00b43c8203206120440091200c5900c00d181c5d11200340c0e0b0f4403141030603100315044 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 724131969 1250 724130719 724130731
    0x10060503061503070308041203110c030a03270f15030504080414011e05091003090201092907060509010b121510091b090f05180a09050303070c021305130605 69
    0xe41c513000e40e0303030352800d000d5405a4000144e200c20b00850400703060f044a800d05640c0791003070140015050b110006511388828000050034004c5c9243c2d00b01402041c2c0c0d1015054a88030301a5418440e1201300c0f4124032030252141520b080120051220007900c40c0c01070500603544201c20906181c10425006500c00205451340e040040f01540325a10700b4514440300c00700d12a03034680694903041b002c14840c1000180b0004800e05081c8449400181d07805420507040303942d000c101401c0c400c482d000c000c42154051112186007035002c18084180b150030f0b4041c41c0500c850740000c1003606561720502800240f10f24041120f81c21140e00381c001000384964299000891140c410b94090300e0781140d000720b80c02480c142d5150381c0305008100b1442c0d0413501d820003030300d500007180c0b01c2949410001001c107804500d05000120403d00406c001500b80d41025044a80c0038055030f4903840c00c00001421800fa041d4244e2142c03014400d6101d04030000e10800b4010700b8105003445551040e0349420006e82005004 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 724133219 1250 724131969 724131973
    0x13090b01110d0c0318060f0f0519020106090b1804060207020409060c21060b040603090501020c0312070315260a02041b030f0c08010515160c050310060503061503 71
    0x80d6400e0390005020b144520145030711900801c80d6036090040c40c0785000d1480c4151040400c00902c034650f0022900c40c200344003482c0071024a4030501040b1410f0143c03004c40400a170b0760410781d82800360190400016560244002c12072410365608000010f6203411403100450000b10200340801c005400a140d40d500251000c50b0011595607121b040701d2503e034880c40001d01c00e0188191044520304003185100984405200c41030400f902c140c0306204a226100a06a0f0b80c0003400030040d0a4064910040f40641502e8482c403480644c1610f045080b20360310300003490441607528001c00c80d01b40e40c09132043d0f601c1001551300303002040c82c55505030600008a80c8038011207100142ea49000b070003002c1600000107000c005409202030140c4500b508402166801c1403411420304da80700840c1411550125210324a40b0b0b502810420240318507071280c3d1104081607a540c0c14000b01c19881c10448909404480b074905613140c441e011505540940c0781d00d6040341e0049a8100341c40e107929841020001d007 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 724134469 1250 724133219 724133237
    0x10504021c0f1703010939090519180204030c030206090f1005370804020d1502091c050d0e30250306021308031804050a0213090b01 58
    0x1901c024440351415502c600d80f00001c01804900760314010f41000c00780d51038101d1916110b5880c040c21144034403020300458101c0382c0c02039581c644036108500007418044c2c100404100340f0307900180382da4181d010f060560506840071501c4500742c1c0c82240c080340d400484e2040c0c0d5034103550030040c4550115041c9a4031400d81102c0c0d8405950b0b4109800d10080072b5262280d032044085242041c00504811628101c5490030748020b2001c00c1194202c460711151915464645d181e2001484040f00e403034001d400f50b0644813810085098a44c020000d15100301e82512000203040e1106a90880240000341550410030703807074600c14080c3e50504802e0a00500840d011034148032480e108501e03001c481064140d0a031003445c50440c062000044c4030481c0c80036102040d0350b0355030428102c0a188400ac0400303a0014030038000a10980401019004120980b41d0b202d000c4655203100102c43e1074800d2056151201180d488001882207507448500c1d005644000391414004200520f00170221505001c0c4003d = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 724135719 1250 724134469 724134473
    0x62d2312090c1c0215120906010501080f0c0a110c060c1609090308160201060509010303080a0e030a0e0613050d0803040b0112110d0c05060c03040611010504021c0f 72
    0x5005803a4011044940522038649108502d1601500301c020a008075800b5405411003840741049020032901503da04140314540c101c1d4007450311501080c401e50000900502c440e0f9800402c6060485001366581902602c1e51040d400005105a03115070945000300300c1d603840709004601009040c4000000da0f0405120440480c0f1903621070300340305510f0f40043c86425047c1d07403065000e501800b03102c08100003142550b07074007401e1058003a000c00c81c114402003010340494404d40200000d008003802c90701055030340345400340007804192908540c5030b027002c40e01511044000b0645100c0c680565492080d01c07c09000d0000581c00030003c00c030403106210000c01e4607210040311544142c4a0304130160f5910302800c200e840d9010603002803280c0000440504c0110b00510f80680384c11800b1204001d020303015141250000a066205640146021502000606c0c020003c0d01c107d074010340380c50b03803d1881201607030f003216000c407802503000300700901d140e503111704101d0003485203031180d11110368070700d081c0e = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 724136969 1250 724135719 724135787
    0x7140d140a0c170f01020a0203090118030816030e040527030d0c08010609210b06041803030209041521261801030c08010e15120106062d 60
    0xa41003e0303d03400c000603c00c00101d208000103100720001100840c1400c0c800a4001c4d200d100b08144141042203900c550407818215446441c010350b80a070000340c0e29403907a0003210000e03941c17a8003a40410500602d88526003005d000d003620a1104080014001590082e500d01110001c02041c0141c4030a024842c107100c154131442600880903111000c0561415100800020703150300300c079004000100d010b202410748500d503060f910b5170010056010f5514080424020a40300048170300c80e5501307200080070302da010742c01060f008100b030303c0901c80c07510b09a003500c0b145801032103009030442985540c1d00c0024940e5200740090342c0714654001d4205403c0780c50f03070151080d03040382981220002401118502c0502100d0303855001c20f08041c0854491140c1c00b900302e0784140324101c1024020000145200048480500400c0e4010811303014000400f0415000b8400350198201003828007400d5103652001c2a50140f9580f000b400c0440025501c00040300c20015001480710324400341d1205080b24850 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 724138219 1250 724136969 724136993
    0x2d05090612040507060c21030902043308210405090405150f090a0212070b0d0203100801021c0b01020114040f050105071b08090a05040204150207140d140a 68
    0x58190300307401c142440d0a005040c078141da445601409090f485d840005074003210343d1410700282d4100c0c254082500c0c1030540c0039003078a1100035805486d1080001c81c100c0b00020341204a845c1c81c00400703440c0c0710f03201c2030410141d0030b00945846511080300c0b5101c4224180307c40d1b07a801c3c4242c0d445402e1a076640702091036503000350f13400ca400381c01c404c1d03c0000150010140a90049a0820750344d82400c00c01506500e40144100281c052807a8200101c00c0c8001004068020701400918a0f6201c0010b8440d1000390030030398120300d54a64a0000290807103050080c0c0d82002c0801010034406450300c10281e000782804980113040d5500c5c0c1c030901d0746d8bd041008105100c4e6000c1e0f000700c0f400c400d4518019003101c0c0e0080c509024000310b245506107820300c081c043c0c121158490101c80d501d241c000001903100c0d0095118945c898000034010601c509060f07007046035003034a5001c81d100b068403001e01010380da0f070303070550381d03400140c00704214000c10b521055840011120000ba5003101a940c3c84412100d45 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 724139469 1250 724138219 724138237
    0x8060103060509010234140d02010b1807120905060a0b010f1805010507030e06030c09130b090a02160605040305091801080303010e0711010c020a11012d050906 70
    0x14010030a201440c0030746544038070b0840c001c6140080300a9030280380e109100c2c0074800c00c9034100c1e450342c3d5042d0701694903601541001810301e40300303100001d80b9510b058204042006500303054846000b803c1415581e0000301e500124203465580d84241150305e0309031000706c01303103d03600c45602074041101884030a008102d105d0000c604000e4000025244000001040c2d0400c030007503058000c1d1413040003203602666803d02c2c0a503560030407070030704940140d04012184c1c3e0028001041c030042d9540c05008007004641600d0751052250100003032002c40310781c89582c42c1c115003014009480a1403e070f0080480000c1c20991386070210050315007004440c0225800c401140c0d002411a0172490440414140c0718400110390300f50358100310040307449020600c5481a41070450010490450092601c4242960805c008202414120f00000e648502100054520031360102c1d042e480c55104030816901700b9486440c0c10060720900d05040c0f003100132620113404108091060102990702e0900414001c9 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 724140719 1250 724139469 724139473
    0x10c02180a060608060612070302030604060807080f0106080d2f010906060f05062a0f030d0c140301080a0b06010e060c280b13031b06140115020c041508010608 70
    0xe8100b03d005841d070321010700150700c140750034058104290440d0508560002ea02e180158032500c41c1740200b4060710311034000c0c0f905c40c000e240e030103e414035001410a924120138802404003a42e01c100007a103810381e4415540000d13901b03200740801c11240f82d902c0140702c140035006c465140c0180402c103003140d107800400c17501075440306001c010701300c2d040b03c4810140608481040ca404d00303440c1404048a60500070140754000c1541d8a5099442840003400445048081e255101d45289501008210046024001c50081001401da071008403060701d06981c0c1100060022427a580c8458801c1da00c001e080d03604104012020f28000c1d00c1e000042c0c01c3c071200308001004040200e201c820b444504c107000550001c000000400081443c40a100d9000003859150480400c1c076400c0c1101c05401c1b250b002c40010300c1d207034050410002c20f030340014450400f107551a041640c0301c1c20103441c0311103109144c1e40140c9c0900105c4225142a920510350040180100d100c030a580341090703402e40f2029400a1495 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 724141969 1250 724140719 724140731
    0x312031505101b02040b0604030308070f0320033d0e070e090a06120f0303051e0c0a02030712020d090b0702130c030b04090b0106020709020c030405010c02180a 70
    0x500c40005280e0050802118a4a040c0ba102d100c0180320640d507010822110b00446542800d40d00d0b1035002a40d14480a0040d0b591981c0342d00700a0031000d000d58620b00050720503442841058030a20814840740200807112000e000418030300c1d00243c101078500780c0c8041000c05400150002800d0180c0e00701c1d11011035903440440341d40001200d4407030f0360100e4480d0031207404104a95620900200300d21904803010340d4140c44104c1c0200003040d842d0020b20f5584007204c03001091008021583c000c0718030965060115581b20460620002c40110443c2ea400020401240380880c1550203030040345034030b10489003000c0654131691a802c080303001740d20160304603841d00700034580e00c00740c00405800c010404514210b52507010401180700c1d0701050807807075038452145494600c00d8100c122040303001842070241d440e607810921002c19081c428400507105403d00000c0a50683c020b45241051100c0070310b04007072400d0015030341d40800703a80480c2e0011b2203a503070050710a01105802c1c020100c454000070030f = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 724143219 1250 724141969 724141991
    0x32208010c02010e100e0a17091f0e091e0408032208040506031e16090503120316050702130501051005160f0c050d060506190e07050c07031203 63
    0x2162440c401c5001103906144112007594000990042c80c0c0301400c800041c1d000d480007506003404150701d00200252110001660f5440c0f00c10090405a1002c031120300200c1d5250455a20181c210001000803510308040c1c1002450101d10385a4814214050b02e103078451403d821800744171049504681c10f020100a009091081c610001e50302050307003030502c034040310b48d884611090103a446030f14407500c00000007800c1c41d1185445008207400b94141100c89081055a1191246e10900030000007019003000107441d25000800410381c0445020b4107245480342045440c1026092500c142404410014440180c031001e0700401c00f00c29400002409504000c2000b1100e500700040381c0420106101c0c0d00032143c2066070702180958805e00031a4252028070303013214280a50ba01080e031158410040c0c0051000c10780016100750f8044880d075400d6100c4640ca8110005d80c0c0c0607800e96022080001045140610000c0c0034030300d90201118061580d0b036031204050f035071907203004000a40720f80700f00d61 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 724144469 1250 724143219 724143221
    0x2070503071a010308030a020d0f0c021e0d090b181c0c050316060f021c05070302100513021002011401063c051806040e0609010902090a1703220801 65
    0x1407032100b520441026545952a8001180400342000303005076030005204c8941d28003540910a194000c0000740900340b4200b030080e4503003440ea565070341404500c004012034290040f9143d007104445407144940305007021090082500603248030300700d81e02a140900c0407540d840b4028101226000642d040c14980f62a05286040d0a0352119021740e00c0003c2143c988403c03110b21106030303100b510340b00c12190311002040341f13132403440c2100f00c06030f62880d4040620668010020100940a5000c5600080c0c840e180d160445004503108811035818031320210041c50500c80160007201c151001040d80d0004003120070708984282c0c060340114909104208050880d81c24400300a490188440c480307494500000a1180340c608601042260000d240c4601c41c80b004a880c001000c003074182620341f601c841d41c10301505003e88003e0320548402c00002045201d0b03000300c9480c460003424040c5101d16102c202100c001ca80fa200480d1400b05101414440c81803500e8200301031221020301070101e1808401e18 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 724145719 1250 724144469 724144493
    0x60b03010e0907081c0806033a090b070803060105120907140105130e100e09070906080a38040b0703150e04080a09080d0306060f110a02040b040f0207050307 69
    0x28440c2d0007240145c0e0b4813440742c5131a6000c3e501c49003880b1502c0d40d12000082d080030141c2201c0510310502100d02c0c418484840c2c0000d100380d42c03080310680561121902540c07000300d240319441012800300250701c0025140400303150071400604000d4142909444500c48030401281c03000000d502030350040210000b0180f94007a40d480c2800d0251070100c6608003c000380030346005040c0e804060501065aa035400350a00c0c00a00c010020b400d21401c00d19145500c40311184140c0030100e0402d24089840500820445142e83d0312020741002c070044000c0e0a1000c80e070038030700307000c50740580240003985149921405104500ca002081e08070700d01a4406012283c40440c0c0c2c1d0b91154001c081484003000c140f40c09034215410009051310391444040c2110205480c2e08810728a0281003c1032034800c1d01500840107480c656101c80003626001c0e00201d6801c1e8101c2c000c00e0490388100e141c0d401500700b41d8400c200790340000d072020482e07102403544c0320141c1c3c1c0700d56400c0b44c1d02d602c00600c0405002241040c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 724146969 1250 724145719 724145729
    0xd1109070e010e04020a050706090203030d090506041214070b15370518090316050d0f1403010504330303110703050d0f020a05010c0e1e01051c060b03010e0907 70
    0x442c01c210b80306d00000c0150141c10001440c25586605003410f640d01041540d0010090040c01e000003201440e046849400680302202c000700c000fa0718141040c01044209034050084840720b0601c040342c1c880c101c1d100c0c8081c1c00300c0300a81100a00d0042c54448214404d00f00e02e800340700300e03113220900100c410040e16500030600440c48a020612403542d40a4240c44401e036202e03200301c550384440c2c444034103600c901254a44040702800d00e80302045000302da00582d03804c9a481e003c0f10944030400690340d0f00781800501c00b40307603810001809140350550000744008250300340c03c2007d0031241000c1c00811030038041011802e082c0502002015805001f50900c006010040c20405145650311641c81e0320961420003441440c3d1800c04050b0720802c09c02c1c10040d0850024080884500d0f809030400030006c440ca40500c20480650b80c02d2844c5000c1c4100400b0103075260780c43e0051421403044408440b01035459a192582800074003815800040c50103481c02c0780c05103051b41011581185042525480 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 724148219 1250 724146969 724146971
    0x1005070f0816030908090409230102030609040f030509030f0102091203090904060209061213030f0302090d030e0406030501060b1b060403020304062a060e01050907030209060d1109070e010e04 84
    0x10401c2c0006894203000e800c0486040200d420b14503032821a03143d020702810507401c140780c00c500c5010300c6080079010840810490303001034000101400315081c1e01c0225841600030701d00c500420002603140000010700d5000c3c0c03900600700903481c00040c0c100640400c81c4402c03070390086043c1a4034504070041005261201c402546449031a102148403803800400141419502003840003403621a04110f404c3d2910448041c2034502d841c0711f46118107500c450781038001561a007041c1d56454000e10864800e694010b14007240901103540481d04041c43c82d424a4101c0e0b00d45c140080041c90901850025040c3c2c8aa055251490b0308600302c9a0f0b41140d1641409a0000051201003900882201c0560b0498a0265855642807034002c0d20502c074001d0190900d00504060800e02203e54000c0c0c246810400003070010ba11040c2034103554108a01003e90b2000d58000400c4103484c083c2d8290040d10301c90400620741c03000210004030800030480d00301c800709010350030324a895079101c54600841c4e9803c0724 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 724149469 1250 724148219 724148221
    0x2041e0605060c070b0f0403020a0e220503121f060206040506060312040b070c051203070201111f09050c040504120909050106081f081603021806150d0b031005070f08 73
    0x2140f99862025204259110a0018090142520810440d030281d50007030a00c090a69440c0c016424000d0102d03901450300300e00716210003020141a0984c2012500300d0011750070702d515185c4e13090b4158000307020701c41d200c9201c03c80c00380303a4003801440c240140342c0360f005003031189418200136081041c0102528801c4c2c114041440d14048010181e40c151b41c071460410b5154001850011724982098120640c0900754504000d40da0100000500080c1c2c401e0341d8072030200540242c1c1b55559002e1246101d0341c80ba640001c1e4103040c440c2d0b4805141c1d0b60184041310307440c40c0c41070003003012154241d074142c030f00c281d0a020009a454000c0c8200300201500701c01003160b2361600f0401411a000a44905101e01f585000b40d2260b425030301c1c240014001e55410f58850324403d0303268405042061004a015040410b2016808202c480080c0d209080203000303d0303846007940c0802503542c2d1005a504500d88d0743c4044c1c6100b191410400e510f00d58121500003c3c06043c4084080e009403454005801080300d500 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 724150719 1250 724149469 724149487
    0x15130e0c090906071d031204180b0112090f020a090507080c070f02060f07120503090f01020909131502040b0307030515010e0909031209030a2c0f0d02041e060506 71
    0x743e40e9078001d0207407402000c074403482817a00342e45603810710816a03d07101d1041244141e01c3c4d028010030803a02e1440c0031080210b003400c112030589404100a41c00b0035212080c182d0144416004140719503c25184001080d0b03032540041ca4500c810f03008000000d0303540c3c0c20080c0720350f000b8001c2504140c0382c00d69035081c08903c0d61503050309048108002d02542c00482c48401c1140c4541c182c132205075204506107083d00400c08010140c1c0c00c1240d001d01d1a02c180e2034004260340c4103100b20b403020704000d030010348030b5502e0180030f40c81d0f011003000482e03000c00c20a1400000080038406407024040c0074015603903034204184010180c400141000d250741c2821004210103a80000c080144987e00351382d0317100f80303940e1801d0203400c60080114000c00046400100001e02e03901000421848100e501c034000144d041120444044440c030300d07a002d60050361544004036113001c600a04d58500000d0808070079001560204d000e030f411707085d115600002051030405144099000345006071005031010381c1880c2d141 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 724151969 1250 724150719 724150723
    0x7090207080d38060d1d06010b070804090e03040e090706031406030a1104180309090501090212010b070206211008010c2c0d03050d0e01020708070b15130e0c0909 71
    0x210300c080c1d038801c0701d04010901c0c44e00d408081e9000c882111404000440b8103032804030060a0380295036000340a008008a4003d501c981078580403034120b112141040c1c2008034101c02024a01c0c08081d43d440284800141510441245031044503c0d0020f0010b030740c5009809000d031240001c4000342084801c00b0004503881c0002c00d24405c5130403081c20b241500e48040818010f0107a808010040d100c1290850305143d00f001c42102114008082003206031303650705c0340c070040f8020303600c0803540300c110b10300104400c1d03032004050880280010700c020318001c1001324140c003c600110000340380a500380108800310042100f1030006012030002440701006011004214001c03c18007c1100154070103503101d00410740a81440851002d8446091046107040143c801d41014101c0361881e800c1090210020701e043c0265141682d01c51022803c040700b039030b590070403160014485075044011650f00a825669102e2103e144030140c1d10020b500260a815a400c0c241d030390a1140c001e82440060047c140c0300 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 724153219 1250 724151969 724152041
    0xf130e0f0d0c0b0408030a060b0a0201090b34020304080d030e100c080c0c0f060c031f060212071a04080405040f02030408190504080318010e0f0904060e07090207080d 73
    0x200c00b455a94071f90743c481c0c2101c014002d9411030f03a140f000110305403152580542c4a10340f4980071f248070300e00c140d98400c1945000c104020444407207035003c0d00d600103c41010380d0403407604110b50041c1e034241500c0f081c146282110029802c80085d0325050140b00412081c800f01071074522404091050a41800010344444000740448401280000e0004010b15040c02182c500c40045e00a485ca1030502c400001e070b0940095541541c0c0f0820341c0d100340d01090f85084464111485a00900004000016000c43c960031820f0150784031801020485150150001c109100d40e1142041c503484900b098280801c507580d000d680d02c10a8410018000804c6145090740c0a100040b140a01b401c880754004803090700030f540c080c460900c004507031166001402c5146040c3c40b8000c0e6104580340c0264810082020b03040740700180c100c04100d01107408500544c00c1003103003410350307012180a584c0c0c45030264101d03882920203035032a0f01c0100d1080491041790194900d19088440081503407103040320400e40d4001 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 724154469 1250 724153219 724153223
    0x61407110d0e040b03010218120a0510090f0f0c06080108011103130309080d0309120f0804030c0203070515031504020f0f0702040f0203040506040b01081b0f130e0f0d0c0b04 76
    0xa02c040ca0600555102e030054124801c2c0900290748075144004034003825054252110b104800d024a034000040c00041d18101443d0020000c01707410301d032820351200800c00400b040d50700140402034800031401101320b44030500d100d5071440e0750130703850481c0c020001c00040c1c0144800ba414200300e02076040c018416617400101020b4030301c40362a0f261405071000c1525610150841c05050300d018002030700343d84407109150189148a54001090900321901030701d05291001158001f404100424800d03180c5680e0035202400b216004c40d100c800061341d00d50482c0c5c581d90104c5000013045001c0c4e4004515040400b02560107500700b8034003109103c45409840ea407058100c0d000301c0c07168103540d155006260340340c1c4680c108541e241410700300f01d134452038215003ea44c0c840420000191010000503079400d00110303450003000c111030400400501080050388541c1c01401680201c030174003400e215525942c6c1c1114010040000c40701082d41c01c2407801d1186200748001507001c880420000c0d03a50582c841d07 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 724155719 1250 724154469 724154477
    0x612120c01020c010e03071713030807020d020307091e05280f0504060608010506010e0a0b0a0c050d0e010f08100902090324010f32030a0807061407110d 67
    0x80c1051080034024051598120425801c1102450f6419004401807501a0017214118580c1e1003900003401c00307200d02c01d5100c44802c44d014040000c520315030082e0480c280700900421030742e416900001d2800e0030503004a04420f80d41c1305002103001ca840000c2180700100c15091003d450101c0304024101510200c1ca000c80b00d04919402c160855940003040e104281c1808000d0350400c3d04113840100f050740101c2c2010362a285c0410080d40c000e1055204a55009041d1044282419074840b80381d0040c207201750038010b038440c5410002c0c2046c003a107281c68540fa91121121a2004001081403100c982c03017405107c0c030703c0117008100c03070840c4140d0103441c59210050380c1c03106443c0109180100305e05d1a156142100b202e2998070f18080355413941201c0e02014441d42c002e8032548104850340704041003203522911020340708101852983c811030914402000da43c1d0880d43060b11480096031040b0000c4922582e00c000f2140003101a8000366002180c504d080c103030080d029003034140c1c2c901440c0285d200340 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 724156969 1250 724155719 724155727
    0x30109180c060e120f070302040e120f090319030f03180515090601060e0102030405101407061b030e060f150607030509040c020a02011209030c020a0308090405061212 73
    0x10001109000081e800034100e14602d07540c1c0300080024003030446491042c004803201900c2a000090307844041ca4516014006032071035a0308100c0240007401d5581d05501a481155181503500c0d009080c0a001c1c0d005a00c0e6102040420941010510b440b0195840c0d403010380840405d50100c21190000e0075414002080c080d100c101401c8140041c000070140d00c07480d04040c00040100c1e15a50048401d14100c8030315988a5400303031145204441c40b540160b0044c00f003084280f5201840015450550a00121021003840d907200f0039404100103a5005803544154a0104090450202048654541080f0300c0503108121529a42d0142503440f0380424000442c3c4182d28070540b4101c5800c0040203c0d545141c03074a00540300380c02071102d551065251100182c66a800031592045145d8143d490072076081c810410b143c0104003503102502040401610100181c032991144c1002d140518082c3e520b8811100070003040e20b0008115a000d581070303c030040c0710000001590403003059522641c6880f = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 724158219 1250 724156969 724156991
    0x902030a09020a0321020601050310020f0c160e090601030f150f02031003050c150a080c070204020403030905042901051605011b0f08090d050d02120a051f0506030109 73
    0x1e02850903010350300a090403400400c20201c190014000401c01410105c500c0740300000b80c2e05ca402c2489400d0b0940c000c25180d03401d84007541d004000f8120111041d5090591400e0b2852502c40742c42980d1032200c1c0c0d0901e080c4203080202d03e080c0d82c0b10800400030140ca41c103554409204060085008200d42c0481e40b00e201c04c900079400400e003207009032200715200d1516800099000d5150710040c1c2c0c25004100d007484c01424032100145691a411344020300e031940a400c2250303240030003000040c2c240b88c280328500050f55240010300055010b942c032403e44a043c0000c10080b107010100c80c0b131040114041c425044540070400c000c1051090821030f40760441803140082914040c07000411b15440d00c051203c0324004901c41c5408240b0960b0313100f4004600c40d07000e442441042c0c61b112040d07406601440882d6105400400c000f5a484078058240650306a0101d0192000e581d50b02403142c4034800c04c0b4809001015960005080d16400d064403847c2c0004598203110600424841c1501c40307425401c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 724159469 1250 724158219 724158221
    0xb0604180207051b040c1403060603270d0f030924090b010b0711030d08040b060a030f0b090f03040e0406091b0b0c0d03022b0e0d020c0a0e100902030a 66
    0x2c0380c150044160b907455005116a403140b40d10b40c03071009200c0c9281035401e055003032040210050b5540c0c440d00300f80c615181c400c10400f081e00014410f190641200b04090b050445011010074100c40c3d07400141200d4801060207401d54500403108010145041c08400116074800821100d074014614811038804070f08003410081c0c01240f80140075404100000914000018018030406004140030a408840714041585a0b44041201c0d0000f070040008103011680000803160407500082c1000803440d0340b0342e19915005a107550070f98003800c000341085486001070009009072650840a1880c0a013044180c2c0c455080140029000320b135181c2541080103000c0b001400c45550261000346181d56444110f00690301c000544020790080480c40d606082c02402074850425280002580b1811012121180c0001d44807403c2801e03901c81d024180100c400740036882031903020b03030301a107081c00000051000102459006107103908460f010407010b000c02501017020f5420b40340d8056a00c0c5c6032040d02d64 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 724160719 1250 724159469 724159477
    0xa0f051501110717070f05010302070213020306130e0d1709070b09120307080408010c0e0f0d0303140a2004081e0f030a17060a230a0801060303020307150b06041802 72
    0x102d07a0841c61031076902840002803905e007150060744414807000d03282c0004605034000c1c0400250003d800200000c2d948103203402440d40800083e005084c48030f04500c1d00d8040d24540340910040e90040c601d844c2d80940d001c17a54103002c1249a0152075241001c40e0b003180d5844c0b040c03041564034070f0701144205c1d059850942001c804440b10b400c80b034a900d03082c10070410542c030601c16008658a07041c1104850f074000c401459000800918031101c00701d00d00103100483c00d10810403010103544100d4120504000000340d40902c03a004400184107100703100c210411450301d9180030000c201440100550341000a070850220300c03103554840034660884060389081c801d1300c6000302501001c9056002280c0c0018010512003510800940f1516684180704140840d0702a0003101f646080d008101c215001e9461880380b030024000102c0140c0c0c942044d401c60f9403507081100140c100140442c00d100200d1400f4210f08140002001020342d40300c006903151285100311480c0350200c1c00c4594021b00c0d154151 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 724161969 1250 724160719 724160729
    0xf07080403060b18191a0901170706030b0618010c17090112090c1e0b1206101b0803130b012619030f030603050d080103170a09050f0a120b0a0f0515011107 68
    0x4a287c3d035858101d0142001400302c03800d44075100c0d00d000050a90702c0f9001d04681c805001d408185000301b49540e015803a42d103100c007903050042d1b030b014020000700107400090080003070031106070b240c0454400051139440480d602110190501d80088082703004201d10208450040c2c011044104201419059148175544002d4006101103600f800c480300000406204003011108921080380b01942a10100605c405444803102c8143c2d2000c0040c1911000f141c00c00138540507412440803d03641c252140728244c001e51000e148101e840d9900056010080d602c0041c114041d0845a1000302038080041c40018007800304003801008008803806540110060758009080d1040c1500908002d44406420702c400c480450420399220805d4081c002a0755000416070349580000389807404118401c4880b40c000c660060104800081c1154850a200505880360000e454503150030100201110410a54545810305000812143d64417444106210b12002d00300424008550701d410b40c548a119000 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 724163219 1250 724161969 724161979
    0xb1302040f09180213270302030324030d0e03150103080a0e060d05240102070b04140f0a0617090a02060412110405330d02060f07080403060b18191a 65
    0x20007111701c2c220741021455030b07140c1c00000d48075243c0d40c00290400c008810042c005800c20b0000c40c1c0102c0b039424131910340c20500e07504400a40f4a80c2d0010381061144924503010801c0c0742c0800700e5605040c41003801040074a140c031140c540c9191aa4201c0707103e104240c83c00c02074109080b25140c0d4444041d914060b01c500002c01140ca05441d1050030505005108030444100c00c4035000c0d40d600c0001c3e0078056480c2c00104070f08003440c00300300c01c0d480c0300c40c03108455204094101070b00340d90300e41c41c00e00b000511581d541d01000132040c11039001c4001c009040203005801000c0c1031800f6072100c0040350101d07040d00424100b018401e080400d1880402c003034a9030b10605000600005469148002c2c2c4052610f1703480400342c0c402100e10309403490b04d09503d19009402d502c1120051310340040617000d00451003403e80e281c1a80da0b42e91071081d510079007007100c48030340d1401c80002c2d5051130485003414880c1d41e0080c1e171060401001d100c1150040b003110708072468aa03d0722848102070341045c2618a00c01500c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 724164469 1250 724163219 724163239
    0x515070605161b15060b09120c01020736050f070e1f0c06140603160e0403110307051501092d1e0f020a03180b190b0d05010b1302040f091802 62
    0x290300b58840e40301d14041c034410791303002c6448c40600a0100301c820f030440d03058004140640ca0400b0402082c0214200c1100f10802c90f485849041102c240d03400501c0c480010014480c40c11545005a00780040d05400c10000c1103079525455890340d001c2c01801d802141d0b001421070b240359400320382040b20440d00074425070034000c2d10b03c0d40403000070207075014803000c40c01d0312803c06102302000c5000505200d51142240c100001c035010a00030014880214441000d803454891181c481525001142c074400302040b41d10300041103209181d00c5003031002015003001455104070603441e030584000840e040c0c200e0300e9507001c80540c2d102480c00b0505d4130307202c14401070240402007400000290070486815001c40c0c00c00d000000c2600c0f995031040c104540c0080c0d40002620b4040c00c20b131481c43c03840c000302c180c195103c103080090b50b645141e08842520990011030f040f05a0000e12680b841c41c040e44100c8240148410b0050b2b42c0300403030100c29140790120001c0c0e102c0741240300e140030410060010b034000380000 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 724165719 1250 724164469 724164479
    0xa0e0d080a0201151e170f2434030605030a030804150908040e040201170412020f0705130b0d0b040f200f0f01090515070605161b1506 59
    0x24000940c89100301103921042c4e9641d4128007500035100c0a0894025498801401074205103400ea0034005414400c45200f14000c083c124501003158415440c510076001440d10a840c134005019802440104100206040340c4100c2c0304944040c1c81d0400085c02c0303200180c100c207100b580320b003004040c01411190089503500340a004018280d5040c2c0b0700180315010380700355415901421102d01c0e48511001d15103460038007600030344c18005e8400ca040140d00700800900003c446582030249000e0000007909444a0390040e15003400000b00381ca00343c2000c0e40411031503680c2d491800c005252483c02181c005803540019036041d00301480208038004076400c0c40148000050a000450700c14025401d90300f48030034144800c02e00054460340c0c05000a43d03c5400c5080c840383c2042412410304120325000d40750340c0000e1000d41c0e0041d05030f110707d80100c0d10f40c0501c100c41c007425801410780e02e00800d51507042c00000341514003090450f505010030341000b404020501041210789842d03002d007000369617160 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 724166969 1250 724165719 724165721
    0x7120c0f031a0a03120903020603070e010f030b0307062105010b090112111606020c0f03090a120209010611120d060f090212010905070905120705011709030a0e0d080a0201 75
    0x105258001920b0811041c04142e0100c6502180290082c28605010328556620100c2c034400031191040041020001006032aaa8003860198841d43c40c0c400c41329402400050490140d03e180c0380c10141000e00d8041c49480224504060314481d14010005a00110245010120003414004814034241c000998030514101601c4070303201c26a125030042e410103b2113402c0d40e065104403c0000020440840302e4030b0f4005102c030384584199009810301c60f0302d0350143e0401c1900c000d41d40042d000058059074900e00300d40082c2c080d284a404891000503d90041803860030305015050900202c0e920110f1411820000c6080382080d42c1f5211380c0e22458040c410000e0312a42c030400b00044a400e1010407034243e980241c41c4a41111303444202c2c07a81ca042254405858041d0145003803021244002c501d940340da11400d24090100030040442c40d15142c00100380418444e03900b0b41a041070414800c400c10b021044480c40203c504d0011003105044000804600f48510003c041c0c10340007500421150301 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 724168219 1250 724166969 724166987
    0x200403060b01082419030605190e0f07030602070503130803040306110f0304060b0604080a03090f0e070c0f0317010303080f010f060504230402210a09081207120c 71
    0x20707a214603140d150a44804e010341c01d0542c50740c5428035050104107860900d18802d203040c401150b0442e40003a569210030007200c00640d0310100c1100300f000461901c540034096020748502c150000c01455100588803929822240002004030344c00190322424403404000740c3d800300d00480c01460503950790345490381d81e9900520007150100d04011039034001d02c2c8a10700740d0f40d42100d01e40c47c941c0307540d4440d61a0030042c0103401203a0340c0000c2c240b001040c1a141005001d000d14801c0e10381110780343c02c0c010081d06d40d50480e841030842614007010015802d5110301c40080c00f079881030030500300d124903140583c0c0340a1014840c0250380b130325100000a2582c48a05035020b000601d12038280d81c0d0700c4003a003040c1c09500d4001d40340070604c2080100842500a40c401d2000d0164040720300382401094002000d0f6403102c1c900380d000c4040c0d06003118100304c511407240d801c040f1080c4100941070340c0d03503196004d5004201c0b540700e8040c15600000d00c224015070102d80e00c0c003076210741001481801030f005400d10300 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 724169469 1250 724168219 724168241
    0x1504030b09030702150307090b0406120e0102130b030408090d0303051617070c060209040c050c070801020301050a0e070201140403030f06060c0506040b07050d0c0206010515070c0920040306 83
    0x118240109841d410040111142030b600039181d680c100150400f40d200580c0041c1101042040d0740318001900c044404c05070011f42025526001c00a04400c00e075804c1e500103000c03030840e5900c10030003810380c150b0083c440e004070b074181c00c201900caa69038144070500307000e040d0034917812211032002ca8042680c5035000c0c074410806034240743c01c2640e940300111429190801609109548076021a02c2603009203203a4113480c0c4600c0740945400000c0c000328041d079003c021a2804540082001000c81c08280587e50140417180002c40c1151f142000240402c49c00e8420a0301602d41c0c0804104128401e400c50b801100300b0340c40c4401c140c200382c5002002440c502281c0b250b424031b4080042140c503ca00a0050032942100003007045842d2a06d41c860815000b520007003c0c07000c1004543e511040b5070181d42c10440044c0c002d00007035131506082c400044122203030f55099072010090b000003d00041001402d984c1440300c005924202031010001140a41480800150002c1000020001181c0261031a00 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 724170719 1250 724169469 724169483
    0x40902031f081c1107080f0a020301050702152409070e0a1215050a0e07030b1e131101020111040b030103060e1f0b010203070c1d010501112802150403 66
    0x207940b10181c9407900211000c0100c03120242e0b40c103d103118401d021104194800c2000c2c0d80782180d4504d081d03460801c441407483d165800075030040043d80390038452964001c0b4a4005804c0d54101190228510b8000070418100001c103c1071301c5007140148400c0c40d40c0100003401301082e609125a0107482100d011020ba0701c96110002d0220b40c079003450582a202992019410b00c018200050f00d5001e004004e2010f0300c450ba44115004411400700880340085000b141810400d007010a41540040d08120007036402140303000921001c08140c82a80100c190440c05a048420380c0e070004038003400c8140e529251042d40800e000c905101800001d604032440f8200801050140001c243c2c0c03a8030384204482e517400b0701402076520700d009542001c0c03410074051040e2850080723655550500c0341e80c941c000c070800020140034000520281d07000311340580024203007004942c83c501c44056503120344240110000e4140c2c01ca1900d407010381005034064a03401007800500341e40001409055410520081d0b030340b1 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 724171969 1250 724170719 724170781
    0x50a0602041710060b180f0303070f1a010f030311070801050907050319020105070f080f030a0606030e12030a1e0e0a0302073302030c0a1b060306150f0504090203 71
    0x400414801c2c0011505c0480c0043e091906070f0081105910040c00c6103500400b0b015084c541c155001e0004000c0c1603c611480030b03034843c00d420100c0240301104101c2044000c0f4000502c40f0340000600354044960601e8510403d60b9800d40c16802c15200c4c2e400850f03158209001d100403514046039407001ea0301b06401f2102d59082680000c88400503104c4082d022600c200003540103e901d1034400541d950298685600c3c0504c4088010f26640c403c071402e101d140c0d6101c41c140903d030b906000b54005030400000600b245815801150035510018003078502203940da00103640c56542d003503000e4065880b6403a040100001c508201d5807502043d03d8210010300402c10003042c201c00d80d40741d45c00c0702105071058020300c004160b61428403040c0080c070601540701c180190310040d5010009006414030421101c1842c0d80041200030303060f4042d400c42003e060a22106206801c61110400300030422803a01414248154009035410710450b080114883d00000401c108000e0103050304460440c104251115 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 724173219 1250 724171969 724171993
    0x50144180105010f05040903140a030501210b0609150603010f090b0a06020312060a0b130305060c0a02190318061e0e3a050c03010b030a050a0f050a06020417 69
    0x2c944003400b40c41d1400800c8201807050382005d40c4a113210600c2400c000008000308014402150451105100083c3c1c403203005000900d1030000201020007030b0800d4160700d40b150380c0c4003115008014120380c001d88140c4009411216501800054818050609640c1e03503142e6013201c8140c191405030f022103509001140043d8240300340d01200300c484070303405035060034044c031680b10200401804159220084510102c0e5503a683c00040400580840d014010b8030315500c0c03c03d040c400300420242c1c10a809020300c00119030003041d00804110010302401c042426450140d800c42140590100201ca03e17102c00b15009030041001d0402d01000c12840d0569804500308699000c01d2508442d00a003103100c500c00d980c000f000701660540c44152008041d000341d07090b050a009040c00c5c0a490f03581c0b24505400142c00c080c481c103c09640d050b0013811b4103950310713154103684040910307004000846505108090280901012440302c0c3c2c4414199540c0c2daa6802030903640f2000b1317130b415085006080c12506 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 724174469 1250 724173219 724173221
    0x31303030c1e0c030f151b1101061a0c0f030f0a0e0604050d06020a0905120c0a1217030c27130c080c0702040e15041a010501441801 58
    0x1000c0d540039a00342e40c00b504595400000140c0180102c5554004591041c4a0718107030287c060741c1045c01000200400902c68010140c00b1100401542030340351010520008001b42c003400f8070110030070305075996071500740c43d124a07100c4000801616800f0200706500b410304070278000c0c14030303480d15507500500d4820a420400d25110700e120300d40e4498010b0348550000b4103c5d0f0003920389081c0394213000e00101d54600205d0200c80c00031030219100d40103503541c0015490100c1c12100581000310040b09108095562400007503451003801203481030200014010503030040403a0001405030110b5224400001c7d000c0300081803c6046900c0380d45003034090199050f030f030f20070010344c40003550301d03054151250703205544190700106003a6006616100d14a1035002c0401400c3e01c2c1540e800450030301441c10313045c02c1c050103804c4040e650f007002c044001000240c0c0d000140e8120081145c1040ca2a8002128060b03c0b000091b04901c81c80122180114142c11104600030312480141922985082401d8a868 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 724175719 1250 724174469 724174523
    0x20403030309171602040b011b080c0f0606100305060a030f0c09060b0a0c060e0a0c0b090103150f06030209040207120e040c03060e160908030c0a02030c0406060e0d05031303030c 78
    0x210000384d15001c400035140075001521101011304083e50800e5a40d11090b1045802c00701c00d0b0b42c8200005945664103c0030003455421f8451040a0b008504002e4009941c0c0c50b404010401051b85410206400d655500f0000d401190322240d200402c1d8400d240102c8401d58501c80c4248040c5045400142034441004030303040d440c080d0b0303940f8427808843c2c1d45030001401050070058480c402c03c038000e000540c19a40c280301034140c09d4141502c80706107100050640d1042d44080b125943d00c10010030825440c510030606490b00c0382400760311001c034a40070500030f0084000217800408900288003e1941140c00318002c0d81c1c040d1002d02030011080300940035100c05104255121100000091500c402d00009900d226080d18210b1049591901c41c945583c200e1410400240c00c4404c0b4801140780405c038008000f4404d1700e046c05450b02d051005403810317014001d02c40c0580c0103406040204507041c01114040043d075078900c096552a418010215030800c8411110541039001005003404070040031 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 724176969 1250 724175719 724175737
    0x6040f0303080c030c2a0d02010203270607030e010f11120105120c13110301060906020d21020309010623152805090301330819051002040303030917 65
    0x891a200b0740041454000130107000c2ca80c0000031006c91510785140031b100489010900394000743e01c9040014489112144c0f070480700d5080001045c9200011348041105588000c1a0230300060f010812044039000d440841d1681d91120318005440d40101405000740c01c11008050491740f0740c3c3c0c2c890041c00030070a60100407040700e070700002c81038100d8a03104138000804a000c640202d04180d4065405020340c00c203800100103d550316405008aa504002c030424850091800503100a01002c048407418911742c540601c6540001c001035804009412000081032010350f9140e8440c10708810207500d016283d5100e20900c4c0904580800f03d400b041907400f805030031081140122040242d002140700c600300082c0520000380200700c010b42d02032060000032602840c0791030443d6503088402048041152125010052280080c0031000d8000b560412100540e000316506100038284a842c0c02186204800ca02c1d00024010040650507001514010300c00c5001040c00511803003081120700580e416 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 724178219 1250 724176969 724176991
    0x7080708060919090c050901081c030218040b12100e010e0106030503180114040801050402011103070b0c0f070501060f090b09151509030d080613091a070e06040f0303080c03 76
    0x103e089100c80640c04803404501c907108014003180e440b008604403400176807166515412405071100014940b0405808030710356403504628100e00b4194201c010071407141e0084c002ca03500c840200721038503a000480801f0803c2c1040750b0070f00d82d020b039014020b80351625520300b540d424140d03042070b00c1c030050090409580c7e001d0080c60a044900c000060720f44024a089810840b22080f81e00000103071070014030217020102c00115040c0307030274000035002000b41e8180b4240340d03208205440c0458040c44c030700754000c1710081c461540d4010b03e044c0e035400c900809202030b01c1c65282c41000034030000a00c0382c180844128000c140500d003500402c00100501c100d981078055054000480c02e00c0c40c1960301c50340e00844412440d0704204c1c80070042071402c0b000c0c0d82e60001280c060030620006241943c440c0500d14a04403042c0401005541d40c48959003d944010303241900603408101080e001342c21542500e0805884103403229a01ca1000c05085030728441540841e01d000301090313601010008a07442059162380c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 724179469 1250 724178219 724178251
    0x5010608030c030d0222060507061107050a0312021c05040c09090b0f09070321111f0203060a0312020d14190c020a091d0705120616110303070807080609 67
    0x44c000081e5000300b015507596040820100c8450019010aa0260000d40d843d251200a01d15002049818280da00a5156020311040c40000d07400034408040690600d0198094554101c04902034010000704920340d04071000d00501b295503590010380720314052241046240c3c0d480002c0400c136411004094030203c890000641c4e0039041030420b50300509407038221400b00396291121100c415007a0100c0101a034030a15807043d40c0c1d07012180400b02803001c0064550450384402015900c04011400c100d01d54010001034901d0f07480c40804d034011600a108014007201c1e03914000d444501c942010760220f680c40d501132030300e0030b844410342e00314000401504051001074582503510081c000c100300d038080b4043e50f01207161030040c05005038111035581c0c41d001d80031154645a080a90300d4001c5802030010001e140e09865000440581004c1140c030480007682c502c0030221f90b821014608202144400024400c040d5400070345207201e41c50079502c0007850f80f02e44017040596603041d00c0140030750f08080 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 724180719 1250 724179469 724179487
    0x7050909060610140712080a150513060e070f080c03040209060d261806070c03060b13091505060418030302131e0303170c030c071a0f0405010608030c03 67
    0xc07500c40d0541c00d5003010010313a1349501181d0791a51100b4004c40e500d1035034004081c4c00c83d40002c0f1494000818440a01c03180c0460955903a21560034410300d0310940d040010005030350040c1c0d0214000e0f00d00b0a03150001c901e001c0b40007500d441c251a5050b00000c036a540000c446410620a4038000d5a0003071038810f09803112420803003041d007490030545400060355682860b15030611600320245000c0c040080e15400d608901c7c3e0400c8000044035800703131030100150800100400e1180003507903444440010b010b41c00401051502049010794016913192401490501c8420803c0c1e400c0348445860034002540c0391030620054400c2000402d200d1944d500390480001d022380c0190540496480b1400c5590359100c601044420058841c6201100c0070102401850340c40a9405d44214038800c8400185c02d050050094500c00100001030b51800420f010007001003080b071900166a0a12486000c1d00301100c4060814100390740c121019031910760006840040442600c1c0d0007051280070307508020b40d034 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 724181969 1250 724180719 724180729
    0x91f0603020904021c0c0f030606021c02150405030d0b0a2715060504260307140a02040c030b090703050c072006071202010e0a2a0306021b070509090606 67
    0x2140b00380364000c0d0240040028401c03002d0340c00c0d03d0003080c1d4902052140c10000090a0502002c00b0101010305120701441074030b07000280390100c5070f1035102d03a00044002078000c0382000c1800c2c0c0c00300e4515007888144030500c8000000740c144900004010441c00203a40d0420580310040c1c42600300303814141c8814540c00b084c002421b80c004086600c08581c0454919500c0101d181c2904850081800800c06124920340f1400b030b000c0148400c80d070952109442d803030403552401030b0803005114450701c0b0500b44001e5024444c40583c180d024006000f103140e8490060064042c1c40da505004410782e0001a080e00d100c1c2c06007030b0241e00b03260070151400344c00c1e44841c103082e82801030f29000d2140040c050003480e2140001801881d001d0200320300c1050306c094000b400d45043c5070504006a218020032400b0580e00043c2213030818001076007040144e6807551404040d034160b40064011407001c44c02e81c2001c0e091049206101104500780c03240b40786ca4000300011250207990f00500b0741c0c401d80008146080c2 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 724183219 1250 724181969 724181977
    0x8031c02070f080f0406080a060305151008060f0402010f020c09010902090301090c080d091418150406080304060e06030c04092307120507050c060403050313150209091f060302 77
    0x2520703a028420159190b103c2c1650101c52a5040360707500041c20000c050b40090259045021030301c0c10300c0a01c0c81e603100c0980c1c450980a0003460b42c42d0b400003045140e002001c610005082c08010b6800d01c0c03030920016401744004071000c4e404230765100c400c00c25040c400700d51110303c0c01740149001040d0342030803490402504220340c4184c1540d41e5000313080210342c41d0105000209040c8004150010208100520000c1c080d803110740c04a90b9400a40865038078541c07031039005030f21150400304c0d65680c2c10b58121840802490f0070b4000340741c0b000115074040080001d00551301642c072003000101c104d10600002d4802101c0807142408280818080820306030054402c24000c9014040340c0d41201c0d1000c51050400e482c0700003c10488e0030713a515020f0036030261507844445070030b25500300300c4400031040c0c0b500c000800c02402c0160010002d40303604080b0352007076001a003000c1c2020380c1c00641e1401000035032204891603c0303003c5410005402d00f03500c1c0709021500a13200010a20240b1702902070b0040c1d00 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 724184469 1250 724183219 724183223
    0xf030213090c140f0711060a12020a03020714060703050106051606091113020d0c080105010519110307030c05010b030303040f110f0418060b09060a03110d1b0e0108031c0207 76
    0x22001008800c51071010007800ca01003d80507105e94400e00d6203000e0650010459409000c1c402c14081d80b5a00ba400a01014107174985520260b510043d00008034001d00c51030000a0603100c24620340ca000c0e01c000240c140c40345480340c4040141c2c2e600c400e801c1e180c5004907442020400004000d62000807001e4100729101c500c201e034168003e03e01c00780059011802c8016400540c1d074003044400c404042c030700403020040441d0410f82075a50400700002c2240c0310720803035285030312449070011002600ca82090300c101c01c2160196030304c80440d440c0082000903843c40c00e403229800c003664507046c0c4c0b4011049a000c3d0358840c0000113500b00b1969504031090000b400c2d960f01c0401d0040c0c400c0c4d00e0b160790040d009401ea000f00f941c04905481d00d4080115060070007403600030b100d030004011840d110501c010302901d401c2032444011b084614002032101e141c0c2140102180340e445843c2404085d164649402d5a5181c80c50001c1c507038823000050303580d0007880403405495a15210081000a0650003049101c0c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 724185719 1250 724184469 724184477
    0xf061a0c100608030c070501031b05130305030a0c05060a0c0207061404050405041415240402040305030a0315080d0c0803270309030c0604080c09070c060c0305070f030213090c 77
    0xa00920500301c12508a6803003c0c9003600001040000b401c3d050003410043c000c2401c04000c6015007200120801000b0003c00301480000281c04804004241d80d1741c0c015507120301200c0d6540d002d0a00241400044403040341c8030720415020800c421203d0003509030706d80555008010661811000b2120080301d0035107440c1c071407000c00010820352514000c45101714003468a440c042102c0c0d4a03a6171600780506044001040c0200600c00c40014005101440c551202a0011030300303d400000742c000e02c5070303500090040c8000104c06003442d070590404034015050000d800211503480140c652131f06441c1d9181c600003049444444001500c0c03001031174100310801782007444c0030142c00d03008283d100a00c00d0000c8690021034803403007500c0c4c00c001c07000481001752000c40c140761404180035614030803460b11610469811000800481c440c40324441c0e1960820000e11112820303840107402404103640580010b6514020211400c0c064000c440740350b004040ea9070350052410003c4002000c034000b80034204 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 724186969 1250 724185719 724185733
    0xe0312090a2405031017060609090c0108062202182112130e090a0507170705040e031612031a0108070315080703050304080d0314010b0930010f061a0c 66
    0x15803441d4850074004401b440c000d02540c20000f00300007040c0c800400860140d030080f9241034007660301c000c1c982d401c0b90007038500c1080009181000461000c2508021240d1440451003011420395003280c949000010b5070813440d18088050600f042d044d1024030340c81554000311128040d100d500700101700d040c4940e200a402ca64490710541140b11050b2550411340c1c0c00102040c0c188881031120f43c00400500d8006002191182e0180b03484140038400d4500c00c603a100ca040e45100c02c2032044070001c07a802404520207401c0742c0780507082c5100822106000910f04054282410000c0c8400c2c001d940e016115140955038412045000d0000c00c0413542082000500c0080c60306010000070b00554441d002a5444504000e6030500d0840c10700190f004041c149101a62102082c1da032030f90650b060081003c0e5100c0c0c2d004045000b60b0080d0100e040350014001e503248000382d844520144080c8600000e21a141500d0048815200140100c80c00c2000306102d2030545074082e40140600c20612040d10a1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 724188219 1250 724186969 724186979
    0x120f0606090604090b0a0f06020d0804061b0c0605060d0f0807022404030b060904020108160e0303040b18042702040e030a030b12070e0604020304030e0312090a24050310 74
    0x2141c22552200e001e490700d84240b1046031418807a038001401f07008258003003084c039110f8003e558410b000072070400c1c4005400410b00703001594010301144040132004c80d5554801b4840100484e0701e051007550550b10700404280c2514008110801603a001090140403900544a1454981c4151002c9a02c1211480302545480c0c40c8582100f07034401990070340d5141c44c6141010310030140d006050324403800404081200507a0040001608a854800000d07055a071000b41652540806424107a0504c004600099008614001400030112145078010381c07071441014402601c600a4000d4a05603050303c1c030500c071580c2080e002200c82c1c00280701107501401c90030750b1070550744201c1803900002d49035403c4501a04010290f038004524102c02091072514119042c0c0c0700420281c44148215000401b09092501c00c03c14141e44120041c240e8411941c520704130364032a0320000415004216044001511000004240800038015000d1845403600d41c1c0c001c0300d11768001040d90105002070000810 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 724189469 1250 724188219 724188229
    0xa0804021002241905060d03050c070314060403120209031005070203040905160f020f030d1505060c011a040b06031f0e10060314011d040311010c0810050105120f060609 74
    0x903000d10040b4219000b4144841c64a0401e02d0751318003511501e05103820300000ea202d000c904d181290b094035002c3d031180885071426060076100c0c3e00140c050b200300b1510052a42020803c6401140710b41c60f14815103c0400b00d002c264003484100c240c0c907400104c244030801d40c2c40d402ca80e91040d00341c8141c0340b90580b25503c0c3c804440c01034412242105800b01d80e01c9900d0340011201000149500080c02d4002240e0889640c0b4420000710f5198103880d83c8200740c41c1038041035540d0191a0040590392a0601e42c51024001d140d44e00c00d2512030b80305200c0c074503210b0516120b0110040c1001e0501d61440d520b2180280716010458041c4001e807011f0600080c841c042e4042031406800343c08080c00d209482c0503002420f90f0104040010b4459400004110140c40e4400b00503060503100341882e130941c0d82e4102030381c0415001c100d60b400755080c40315070310700785911079601882096400419114103458100449840c00b07905034245882e001d11001c26400c0c00c00d0009103a004000900b00d42c43e250f00c41020803 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 724190719 1250 724189469 724189513
    0x152208010207030e0a0e190f0603020d030309171914070f0b0106030b0906060703030504060b03030a0f2d05030a0902030709020417012708042310050a0804021002 71
    0x900020320325144e000c200e18003402c0e42c0c001840c0040c216102400e0104906900c2d982d01c422000d6a15038510b0381142500e02c0b07800c002c2c000c6400800c0d210b072900282c00c02401502c003007003088034400102c51900c00a06901720994182d141102c0200044100c0c8120a84660581521070015075205100301400902d10301412210365201e4a00e18542c0d51515501605032424403455130b00c540152020042c1607111881524410398141c90089610344403810901c2c01050310642c1c10740c040c0400144036035010340005504201c080b280e40c81d41040a084101c44890ba4800c000140c0a4081d01100d03000d03080c403440c0996002500c1e4103000031a56199130000c0c0c40c107101c80d840498103a40214040008441121451010844210003032090132141420003100340140401f4000c44446065903206100d54101550302903e001c650402130500b043e10180f51045100d190b0604c9000300000040700d00784101e00b543c1c0c03407103410340702c007900c0761105e40c00c20450740000040c0004610980751208920051480c0070 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 724191969 1250 724190719 724190723
    0x15030f07120b01080a0f060c170901021e180103110d2307020c010e040c0504030203031216020d0f0e0d0803100315021c05060f0d03031406152208010207 67
    0x1a10540d03490075100b410016482500c01c0d40081462a01103403000d503000d92000e80c0100300290000c0c1121098032a40c02080c040c009100c511001c000202d841580102140540c0c01280c156208240003882d0b09842036070740e601d1031100310040b001515402034100c8040704034448000303410710b03a40045034000ca03600140c0410020218622100282049070072003600400360384098803c41c400c80c800a00100803085a1174019681d40e01d03442e18051141f029280030355030043c07e6940e90800c8180c0b01ca0401003c0e140c04a4030007100301560b21050002401d040107000e1900c0e05850580c040000b611403068001c1d5007038200d000994400005070984004501c5403900d5941c1ba0012401e504024060f000203900090583c1d10401400c140705200700c408051540c20600c3c04a0560b6030440810044514024080d40001e80e1000c030344d080503019000f4051441d0a4401c0b44a80d42d500c908000e419020341c98a2a8628000c2002a48043e00320200504102001e190050015a150300c11422a0b10078041 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 724193219 1250 724191969 724191989
    0x1b03040512010504031e0c2d0521031317070204020c0d110714121c091d01060804020d0c0e0c0d060906081216080a0503090115080615030f07 62
    0x2000105a0003429501e070000c0703500f54925982d01c0340c990142c1402d06181e0301818000045034030320200030300c84081602c0c10034045003030b4081d048e0314138090b565001888040914107505201c603001000700031041e00d2054000009850715250141c0320343d20b1b100080740c60102003000030403d040268460340001d02040034520020508100d030000300500c1c805140c5100700386034004400c100218062800080000038084412445209030013030039a1518105002da4001c51925042c00704115412444800032206071312a034007288000551600c249807001d000e0100400c040e480418058244403184800403481801020141900c07003041c2c917022002221440a48100003403883d029040754003c01006054801c010300001e0304200006484400c82e010510201101080225070f03058002007a800312508100003a0340c440070840003c0c0349502c01c94001c01c46608041c9603010303001c41071910340700310b50302d82c0050714690300e900320901008901d10130041d9042c80307800c110b14040c92051107003d000b41031041d8 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 724194469 1250 724193219 724193221
    0x60621020315040503180f03010f0204180b0619111605040b0103091101270b040302121f150b0d0903030506180103080304060f24050a0501051b030405120105 69
    0x1042500d001c6440b070305040440c00007018040061000020b640301010404054240c241003070012420f5203d540341c480d0703411340c2032580842901c8155801482034505101d00000f110580c3c02400341900d01c20700f1401d0708203030708010002910114041c0a40352841c00c1c07070070403081c2820f0700740c240c0741540d0101c0d881d25085080008000034500f510a10071b50802c03c1c24103110305001a10b5002c00440f21030103a50501100021800305810342d600151044040d01c444c8607110b5456041c0301b151070300540801c0b03000c1c01032604881c2040000082e03040e00150408040c80a022110851401400716802103480001e5614800301300e070080381010342400b88090500186031003043c10000d050315005019180510001c0380c04106004800f07410505403904001000e640ba110391034441b004020400c02081c2c104e00c0c2c03d020b1074411a0340c258400d06082e8440002d00543e44941c1017014040c801d101c0c59020a204115440207611018030903001c44603001c0c1900e0800d030380d074404030300801c1000925814a0b59114 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 724195719 1250 724194469 724194473
    0x8070f091d1f080601290c0a02010905042a050c010603062007021305070e27070f0e01030b03011808030f160f030207020301151d090c0303090904060621 67
    0x10075400d803600012003030301840310302e00300c651502e548040c05000d0900c46c1007401c902d0907410061105035004101d1001316529502ca44e100b0b52902e2400303404078005007070b01c3d200041c0c0385054016010b9106038003a041001c000943c81942c55403000e080c4440038040d00380402c0c15030360004c1c8a241c008600035040407418441e0580c0c91040c55401190100300c0c95402e01040c1e001d0b8460340c0300c840030307001d00f5240090651100e510964100090524040d80a0300d080e44005c8001d42d48401841000504045054192107102c02034a4120340c010b00180003448505107443c49600c81d800c011301c540d20181c00014a482c11141403036200c9080d10065582920000510044510f2652081c1d80504150074071240940c0c1084010315080c54601c4103000c1580100e03403401595000e500810700855008420320040e965501400100c001008102078050040d01c0040c4130340d4000320783c803094020010b000e07514042140040181600d0090015074405540c2c0c8000700e82e141c900d03000840411200d45421804122034 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 724196969 1250 724195719 724195741
    0x813050c280f0b0f0304030306030204181104050f162706180e04020625050606031603020d02041508030403061a01020a020904110105160b0114010c0308070f091d 71
    0x541c4400d540d410701c10b408000380c406000c1550340c00f241d542181a0340703403a10309040f000ba2007242c0020394450300d0440490030314400301040d26074181c400c5d44d00092100811040004842003100c0d43c8184996060001e9100340c039038000c0304840a56170405100c501003508292403540c2c00944030f054690034900c0309005468110b8203502c8200b11400408007481c0c01e00c0c0022550440150000307015520206081c8405e88100c0e4032843c080a030741d0310b910740c142c459080aa50f00c00c015034945020340100300103038000c0c0094440342c00545c0c2c0c01919124040a0139400e21005140f122502e090307075540820302040071242800140009c500a910102e1b801d01d00d41c42d0f00901058001c45030f8150f510040c02840182c8643e85150760258010a00489074101e40c801a240c81c843c00144000800c181001c801c1080b40603110641640d94044400d08202d03c02001903a002508420107408076402400207139400740704250f10031101c0c03600d1402120103551201c4440c840d202c02d00e0540728107030743d07841000070945030 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 724198219 1250 724196969 724197049
    0x21002030a200c030909040807080a08011a070206120a06150f0201050a06050102100e0c0d0623070507080a0e060a0305150121050c1204150c0c02010813050c 69
    0x20200d440f883c10100300121680c9100300c1001d50302031065080003505005181013079406c410782020f80580d031810000001482008240100c0c112950050440628443e42c94103035505198043d000398501000486107600c0707010010020f280176600c800b4013080d42340e00c554084000000a440301242e04100c00c2002c0d00351000100054081c1c0c2c900b00040000303030381c0040c40c1950022403201c0014020700000d081414140c02d1f207102d5400003c1e910301001004880d034040310001140001900e01480040417000c0312070003d51300c0c40300041d400d00695001c90b0f00940100001c50f25410030510007080351020071581e8000c1e02004011aa807a000c200310310203003c490300c6c005242460710340c1e248460360382c01c00e010845500307151039040c0d610000100c1a050b400119a03002c06145207a003000d144c14070b44005840d14803006030300d10f5400c00094040391802600104c1c0c545605131900c2515543e83c0c074580c0707094138000740155010322444040d00600e450380401c100390607501c480300380610300080030f034a640000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 724199469 1250 724198219 724198271
    0xa0b0105031005010e0a09110c010e0c0105030402060c07050307270c081b12090a0203073503120c0301060e010903081e041703070c062d021002030a 65
    0x4007041046602e000090b000400c3d1502400d0140359460803401241c010740c1c407a0820203c0311b2600812014407035000002d0f00c01130440d000280b00d030041000b4140d454260450003136010400a00100300140b074900050500200080101c405030744ea1000064948400c6900c188403122182c13003480c2c580043c0340c88065000c141c0754824000c90022142c01010014000e10850f0500308030f4404034541181e507012100700760b50443d040d401508190680584a888290049110b4850b0350340000f90b00034105800c4814010780c0410320b030030700c10420300145104070384040c802450100304620340c2d03609170640c101805145044da00c0c230b440e5810180d01412000d4255001418130010341e600300001038031402201d156082801c03851000e401a05a06140c44c012500084034a403072002c41450034081c004050520303e4050100c2d110925941ca20075100000071074034001501144981d03c4900b2590107161040188441c811a14843c0c041441d80040382c00584401c00d503a61101d1049482c103411080c05180301c5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 724200719 1250 724199469 724199477
    0x7120c140108010311120f07080105250c02120d210e03030408091c2a05030a0212101e06150c030e060d02070501050906252001140a0b01 60
    0x40396000020344a00790501c401442c8038002d0220007015142c4000c5540003818500c102e60680c4285900c031601d0b10607134090b03100e1a40c40c100010350713411110307580302c5241a1007080b00d10780400781c80340c01c88160b950040183d8010300d26a44111b40d900040104840401442d5580100c520101450b1380f0740c0d07903106400c0b616142c18801d40c50480c2002000720f0342c200d54815552603480c03a1110108810584000100c403480100102c00740500c055040c49903040c0e9610086002441141070a400d000340f03050250681562040c611007005081c111210009034041c1e80442d0000309240f10481d017520f441e000d80100310310840c03060032812102800703800b028109003465890382c10720071040248000000e200107404c0003a2544c00311840d455100c100c5407803140d284029035642c011400c20601a08040d10341039160310400780000d2540030440c4000192404114214000d40c80018040f29281e0405054800d14106800c030403010017000d1242d41100001c2c0c402d404c0307030b0307260040c041d4045500c0c0d854654144 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 724201969 1250 724200719 724200749
    0x7030606020309101b120804030e0d0f020405070210150501020c0603130b040f060504060207050d0f0f03020c12040608070f051306120b18150102030408070b1b07120c 73
    0x5a59904008280713020340d454802c42480401c208800342003030a03240076002060010707400581603805120188101d01a45911040c480400c00340700b141c1f903003000d015110030504c0341c55000601e042e4000b650002103510407141ca995405120204660440060001400004c4010021940c05000322040010100c400e0b80c190b141c860031001841d148498000d0a41c021f0800007410803403012500700c80160400c0c000c00c0706113030504e0040001e40c0b01042c1038890303100b43c460b40c010040c86040f907901000707415034647c0e2103452004803ea000e5040504c2d041c091340289810382d80e0b500c10203005440107008035070341d08400d410861400703003040090301c0110301000030400c01160100c14444803141101d119192402041078100046802042c908803101d40c00403800c9001181e200c0901105402031103241149810840030708010782c0e80c4e2140c0d00c15610240c2201c1020046988444090070701e4400050055400c15121a0340b58103200b196000030030090600c071021005d204184402c2c00c0544006c8180e5111 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 724203219 1250 724201969 724201987
    0x1b07060906121103131e0b0417070201020d0e01020712230613030507030e0402180f040b0112091407061d01052104060e03040b0301150215040803070201020f03090105070306060203 79
    0x80d44070043c00c01c0d65202031000034008000ca8500700b4003032141c0300c0e1b4101c6400c240500d0b050b1007031035003030350252502514030040c441c04001c0301040341c1500342c1c16002484d80315121001510302c9400304c4a1541940038510b00080c480000c1008480018070450301c041141400c01510100c14440786850701d40707030740000c1c108182080404400488150103003003843c3c83c1d1000385411994004050012034006002044a43e503503409940e442e84a5030342240c803080005011014881101c250348c0da010300184a01a500c8990940c0341d206200940c007842007140d240e17800a01052421380316500080c0000c101075081c03100e048009940801071102441c0651030806031110044101c1c100440500303440c2800000300302007100e258001115100c02c2c1090341c0d1140d59a012000300c030341003482109020780c18018540c10140c8042031880d0a402015030025507515036481da0b2a0b270380c100410039010740d94200a6104000d000c0d40c0130318440c4c000d500001c6901c2c90050001030550b8203d03800001554024010300039 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 724204469 1250 724203219 724203251
    0xc060a0903050706020d1d0319181703070f0312060503030403020a0311040e100c02070915030b091510050315040c2304020403030503071d0a0b1b0706090612 69
    0x94051300007a001d81c50f012018030f04030040601c00550664041c4400c6004041d0a012001d4640c20b1543e051140a0798503414040e5101100800522260f00e119002030260142138070038001c2000403102128200502c0c0d40c0e403111001c00000d01074010a8000d003000e480d845c1d240c016203018010940166003064510b80c04a4441c100d14007005261301c0300c400d03103443e032078481d540820b8054044400b1611605c501000b00b0004142c4001100014065014041041c1e00f860041c074a80c625034541048920b031a5440d001c0740c40a0140c40100940104c6c0c00c0c90041442c0c2c081a2402034846040040d58203143c0420145821905a07a201c10001001c04000204071800800300881d0011654040003100f58507044d02006075586c1e0a6a0052002c0307404824150b20001a5208910f5920340e50802c0d1200c107000e0751003e05000880d60b020303c0380d500070b0003804034401c0a03201d015121500c03038044e00030420b68107040011a4000740001a2240030410805a024249032050420f01008010340405006260 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 724205719 1250 724204469 724204477
    0xf030203030a0c05010b330705250308030c04090c030e0c100c0203010212010602010c0c0b130c0918030f2d180f0906050f0102030d1e09080c060a090305 67
    0x541486000200ca2052140a4105c00c801c51b400034118500c0d0007070740000c0c0e281e501d541400b9044014003108803030b40d102d030b0403011900d400f60408020300c50034901010440d01045125031140590221040000003e00d40101031801211a03400c115103403030810601100300d4248048080c1054140710011803426030210716112800015641e0140341404500240c03132103101c03214025003540c40015607060544401c01c140e0b05903581603000340301ea4201d00b9012214980d80b080d000c3c00c1180c12034007284400d0f103441f1200c3d6456128203504004940d0780d48440c3c045480c501c440541c05c02020100c2e804144e4814809281f4441c0c5003010800c08650700582420303120f000404107003440d0b04046291403507001d04008402080751880c1460500e855540000038800c00e44101444541440c401085510b04000000300c0301c101a4025402e00698030095400303004200301503071855841c0d01528565054500035410560701841c1c0940d6165048010381d480c00c1d4000303001601d81c41c6005107002c0041d43c002c0c219 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 724206969 1250 724205719 724205737
    0x60a030305090f04061d0402100e1003020c0a14010905060f0108030a26070906020f0303010b09090a090803092b051606180b040302010f1109011404030204140906010f03020303 77
    0x3461043e62100d000c28018070081d003007944041d40e01d40010000076080034409108510a4400c2c84218011607400d9414482410082e03a00542c0c21010b65041446a405400101c800798102c40014040792105144051480c10011040c3d440720199030900004111403900305100401c1d412440d071402c566145c4030f00a01e022401080180042d030080e600b070101c1c844601001d00b03003441c411820030b1180500b20140328030940c2c004d8007400d04140124040407003528101c500f440585850084014208001e1410080810400c0c1ea5280d141c0004260110041d6114100150044c02c01e02c440f030009999111407161101c0000c0b50185640b0600395011082c1e900b008800c04550050340400e1526001a060a940341094040491a41003c1c881d04400341c6018600a40003004a0324941d04600141c90000100071040001000142040d51240e05284086411400507a003020346907400030702038a85007504011007585100910040107003c1c401e1600400b0b054000210f2145582d02181d2070340200c1d00c40b = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 724208219 1250 724206969 724206979
    0x18050705060d0f110301080d0206091b01110a03050a0e0d0c06030902011202070f02090a0b1e03030d0e01060602011b0f081905070c03081005090c1305060403060603020306060a03030509 81
    0x20b1600310500b0f402c01c086104031040d0501800c00120b4140328960001d00c038041c407905c682c8882c406030900102c1c0c010b00542c920005000c881401b10b244075000307140721400c41d04000103500c043d54038078010701002c0310380d901c40e941d116690905442c1c02060403844035902072080514001010016252003031a10440d0542e003001b01e0100381900041e035442c07030030501d4114550700000d100030400440c0142046100e10880c0d60100680319000003008454409410315040141c0d00110242205045804174160100408907842c000da05004002990103042070111660745540050100b6902070040d481c00c8841c1140803210001360034801006201005403100511515070301044074440c2e0310003285400b000c405424050b03070034002d00003409841d050000b60001071740d00703012503004030401c00c01034105c86000345000380c6030702e03642400c01d840d5200c0c00b044048015085c1d80080c441d02c0f004084d05c01503002c1c0c503000800034518018141882c00007415035100e990501d80500000350807105aa0b8402c20540b1 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 724209469 1250 724208219 724208227
    0x312090807120c0258050c0a0b0937120b0c030f01210c180b0603060d0311030405030d020f0d03140103060207020a05090c040f050604081e24010602011805070506 71
    0xd410030203485c510f80b5400340381c1c80d84c180e03c00d102c800a40008844000d4400e02d180340d980e4a00010070380100c90003c1e41c440c004500d5002203108241049600030014004403102000c002843c0003101200e41c4000c540c03074140c103680c005008004c50800e074860400050980b45140c008112041da80c81406003103026a0b03000c0211040505001d0454040b0b0b13440341c01ba0291507280d0344015801129440a400d0b02810070b803440300071b410000182ca02440c005800c011200e000c0c1e58064401540e1503400242601c014400090341da0b40c00c01c9402050101c0b84c01505454034405440341c10100960795000505050100c082001c51b104809141101e420450040c2c0f40e510341e1000902c180312070b83c0480d5000b5100010700c20905000d0004104943d0309210010400fa03440050003094003c1e44103c41c100d4000d2141054400c4407104e843c802507d00000fa184041d440c4a20a1204482010701c6c40d10b4101140042c0000e075024451464000cac00361052581d10304043d564296944580c0c01003500070349001c1 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 724210719 1250 724209469 724209589
    0x903031e090313060314062211070c03210e0a0501081f0905010f09091e0507080f0c0a06021504320d18030312090807120c02 55
    0x3105481d6850002203200c01c3d201c0e60345400034090410a91604212540000481c8003803905d0f1000030308a40344d40700e2803442c4900c2d08462400802c212003400c88040e004100ca200080c45600032000614403d4441d440c40d43c0480e0691003101580880c00c00c18403501605414083d0f45050010040310800d1030b240c000c1d55543c00c59490034018011280b00300c110301c41c02c08034115009401c050b041e01e90b005040c840a076030700e400c0c2200361000030364050310301040140e00b07814110b41810080c0c00380340100102d48489550f000b94902e498002036510b110754104c0d225545480c0340c8224074800401c1d071880203014180d00b043d50056031603c0a440140145e950440300600202440041500155802091540c10180ca10301e01d403a14100c5900000091003102c40c00c00181e4100c81c0030040c1c03a003550342c0545d0061004030240051914201c1070f24520000c1c03200d080001c3c00b0303c41400c000e042075a5009005152441441130168000010440800014004030207042040f410f8030030f82003501e108445040104 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 724211969 1250 724210719 724210723
    0x5130905041103060403110c1801120512030703020a03050a020a051b010605150c0d17010303030207020d0204020304150e06010605070f020406031e11150909072d080903031e09 77
    0x40440b80c0d054003802040200340754000691508000c00c010a44121828200c200141d400a14607911580c500000050040c0000451400e48481c8140d00f112a202080451060180c10803990b880c00242c000a03a03404c020b0b490300a00e0781200f42514154101010444040c0c09802030100310031980d9200c1d160743c0e94800f400d4108000800000c0c010040d254164000d58000e41c0c080d00380c02c3c0307032440341582220b240c502c500390a1000380009000c002c4140d08607501180030b540401400d903440307495407030164056522072004501480c8259401020301382d041ca81c4106030740841c48640b64036004640104400380d000340480b000d09511866150a00c40e8030301c0014010310700c603000500f04000031855070104250508481417200d00402c030300003550313010408000d1810400100c0c500210002e000e1000c0c0e500b009400540c00ca030017409c0c55030b003014030003161507120310040600702456a0101510003103990060401904000c00c40050f40c5903113840320040010044811900d82d58400c60b00002d02e20b0282 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 724213219 1250 724211969 724211993
    0x818030a0822051f020f0f07050108040c08060709090b100206070c0507090e0309180114062110060f08040b0121050105130605070c050726010e0313060513090504 71
    0x4000d01c00e004d40d4010304400c60b003661101c00f882c00980b040031a060301281d000a850341c91a4080d000405000f1309040045440701b0700940120340d00e01a4420101c0c101d441440040d02c1502a80d0f107046001e440c009140341903444040b5054000e0420030350300280c241c1d020940d15406400340c00c210140380b80914203030b4604a12903204105d19842d100d07030b081c0540320202c0104520720044900e02601c1302c441c451460204020700c114500a854540102c0703280c2401c2c03015081c00e01810181700c3c03c0c0310454150301d007174110448a011100382112800c3c484103400c101c00019404d4180b600b603100307150a5551440616040c0510201595000076039507031982140c00d0580c0241c1d000000307100504003000c0c20000c01c50b5414084840500700030002e2102e40c40303400d5010b0529003010080007846e03d001d554000415003c20000000c2e2048050000313465400d000d1201c5052110000796581d01042041d40100b2013076400c40c0c01086820404484201074101c10315068403003016002a403a1114074060b980300d21 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 724214469 1250 724213219 724213229
    0x20f120c011407020904060c0e0303041202090c07062309010606140d02041e0302031b1003050601200715030b180606040302040e010b131104030321090818030a0822 72
    0x1903034004210404c04d580e00304003000d034419160101c60480030420103030be900503400341c1c030900c005c42e841030009490000320490b040001086c0a624100c0c40761070f40000d40310b04020325080401c0d20290318101c60000d48950368000070005c000c0181605010009011926880b402c012140000c190000c500489034100d034014902c0360000c070b4541c4500c64494210484d17a102c164484e016424030040c0000c0c9050002113141c00013801c2c5500c8080c184c0d4141c005017000703040681080101d4400407203006540b09d0039807060742444028043d0038a0b109602021408100c0040c00701414040c058059441c3c0130300905000052011210407903480c0000300d140b6014a80c406944141002d102071710f00030041d4055244403000340e49111501041840c0901984c1d0725040300c09560301c0c1000100082449030050010040f07925080d1840746011071401001c5c0c529551056640910000e9400a1000c14000039040380ea8154041c010f011400e032540065070044156000d40945030280c038400c010604245040a0a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 724215719 1250 724214469 724214479
    0x1a090d02280c0e280606090306151503140612060601081801020a030209032104180b041103010501020f0c09071d10030f060509010302090106030902121504020f120c01140702 76
    0x11401181541d5080c01441c0c07004c0a00d595041c02c490118031a02428080e07442580360402003510b5036031084c00820252141d8400d241c1d0b071703403804078880c01000b48842c0c0200280d900841ca0803201400c288425a0140c059807103604080031805049001255050b80102c0c01d00384560f4556407914528071100144032900d60702d510001d005900309030107a001d0241400d050f8215014841003802e000c4e81087c0700c80b080c084101c414842082955120303085102e80102c0c6020100345a281c60b030100b000c3c0c401460030b008500340044014841542d04000160607508000014140a4001000b0413400c92014109500700589686013003211919803030080300f2604007605150254414100040052801c40220010681065400200c614040310a03e060303d4005006c010b0692929406030003c06184100300c4e001122108120304480050000c86111440f030303a0a803075546813a2041098803040521000d10039103511202c0b00031a1740000d1001003224081c240824951070560005480c1d0062000c006e604c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 724216969 1250 724215719 724215721
    0x603091903080a050c1806180306011212020d0e19081f0b0a06170718030b040c0e0c090d0201050c010f06080609011404030e04091a090d02280c0e 64
    0x96480340d0114851100c90f9800c01054a5019014403140714003281e110326150201c140e20414039024005150b032084130740001c0c08151000000c6030400b10240e0108c1072403a1800140c5051020070462003200e980a4800b8114044100401410401151030300da4022081588a0318000d07841a010001a103c02011608121014214500074603000c5404120036410141140103030f040c44805101540e409448551105034800901d1111220080c4447c040085110315044428000711031200598024001503003e8a00b03070038082c070300020b66405040c01000b401c08008841042c241980d2400c1c0381140d406945d402e40f400120b603103002e00c10035a00c0c25407800300380c1c1d0b020007400d901420440b62404296685a075030001c542d401c80d1428020b01640c4105480014000780c1700f1840c21003240402840091b0500303581d01c1c1c0d01e0200343e0403450442d540c501b18041c010020b100300b04422800010b80300030038280203101b202441480d80c035032410301c2e507402d400404401c00040b0001100904000140350140b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 724218219 1250 724216969 724216973
    0x110a0c0f02040e010906060609140114040512030703110a020d080702030c060f0a1b0302060c160f06091509050c01050a170f040209070305100512100c030507031401120206030919 78
    0x1c02402904540d805d01c7e140c80081c083c0d0143c45400e0840e00e11191070514031100700010b40e284150000e824000ca413080002283e20f5031600c918005401101000790f454bc03410f890080c0142040051320b426640c411402c401c016510801c0c070340e4006a200012070b80760240c0c0d102003403600e6a52402203500030001f0400c489140c01c080007404aa078440c5d80c0d07501c10181d04080e41060600300358409001604031308005818404140300400ca204016a002c1e40800e03e6510b8102c01450b075142c00b12251520381e040c440601c0404001c4d01c0c64620786110410008032140c3e519a81c503510b110742c0314140580072441c0c160040c000c13000d603201c0c000c501e5a00440d500e04510106500b410855040348200c0703040380464852840f91203107521270b20140030a1081c8900780001c009007a050500b08a089108040110600f90180e002d120070009050310042040e01f00224051305031070201d165103c0c041107401c010007921200090903541141c042d0380710355683d01d507400d091341407010840e0030040c1d40d0702d00b91626003 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 724219469 1250 724218219 724218221
    0x10b0c0304182c0c040b06090409020109030804031208010b190e03070e01120b0c070506060f0d0203150f010506130902090f1c171204031215061110110a0c0f02040e01 73
    0x3c840c000100680b001200d0820802c0100e80384e5442d02500f288007480440c001d818541d12508c3d1141c014108603c0281d034039503071101d05d0391090b002260301d02503122440d50b005810115050150804c0120f01e420000e80402410200760040400010400d07001960f0565880c10f0041c8009025180d0500c400781d80c44101b120b03650628200100d8002400d00001400744d46240140d443d01c0381c0c440058902505c80804116411040344103840d84154100e1400e001650100810304004142001c22003603498203e90603182020b059010034040c04003000400d071041d102007001c40684440e402c0042c1c64003106808141d1036002c030134819800401000141040708203602004440911404a0a00c00908041541c0c2c140c02052008040003207180c0202d40000d001c2c18200b03042041c1144002081c06a0041c0280301300800ea00c10404504540ea6a020f0342205100321181d0803489102401507445c1d2000c208454410710f0201402c01c8641c03400c0c0000c211035600ba0840c0150000d0090010700c4910300024 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 724220719 1250 724219469 724219541
    0x5061303050c0307140d03060e04080306030705040c0816050406140d06030813090c0302181e040219020f0a120c08070c0b031504060b1b030904051e010b0c030418 71
    0x280e090302c11b04040d618100e11074002c01007680c4008400c0c511584650382c0d43c0320740380c10141c80e5580c54015003901151a4031280700384a0f04245d50f40d500c181500740050001c401000207003482d0208002000188a4290494514400401d0846030385030340320751016200c8014810342c0c000400c801c0e40001c0c1c9001002003400e19905441640004000d110a024020340480c42041c00c0d40884005003005545149002c121710040c080750022803c1d80c10a915002904992042018281c4c1146024181003e00d90402100c0640304511004007003000158031a13880d41003005110380e00300710125100c4c07000c205040c2d0580d82c055a12000076019103460b005c04c82d14075002103030028404526400340d18900d2400d4003598003100c0f035040030280790040703039030241c41c0032404640d40031002c2c0f03c10481c0c2e00464440c0c0c0300d2039200b80d103c0140f00101d41004c41209030444010381c4903000c0c503c000d122108198101200b00c0d0121200c0c5104002c02d480410041005808000081e80f24015640f510130020329012005c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 724221969 1250 724220719 724220753
    0xa05060a0608150115030c02011d0102040f05120312040f0b07020607080c18011b0c0308070506131a18030d060602300c070509090102121305061303050c0307 69
    0x2d581c030380e10b004905100f01031003403040c030400f442c0c5e4207090a03103103000307900400380c4128610020a03c0d200490f400030b204558a007001034669400201000341d4011072101201810f011225250b01580b00d40000359a800b55a90b803041e60800b0740049070812039007005140481c0e078440c1c00340c1c0c0b05180506010307448010499040b4040740e1840d0000e000302c50720340d04541d0004008540019201d84240044a15240084075080406809000c90000c00c0c2d01c2d0002c01c00462107241000c0e03030b82c0602d2074900c4c10000302800a04500a0310030300000000e4100d60700e000450109000d4208940e1000b080151400c81900c0704180b6000c0015580c1c44c0601d140c021b50241d51241e02281d0704440d2042078144a80424490302c1c50882c0700a0309200b0035010300d40202800d84c2e52104131201503855100003521608161440d0400ea9400503209200142002a203980105109082200c848403511915111300e4002c20240301b03054410f4440d0100741c09203056178039042108040307a440e01c03800d16045c68000d01c1d0b0802 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 724223219 1250 724221969 724221973
    0xb13050109060b070b271501090606030209060307030b030c091e0106050406091701092906030a0213050402130c050904050109020307021c11120d0515210a05060a0608 73
    0x70800f494600202c1d404241d1000f108602c81c0e4030088041d804484000140405d12008446100808001c00040c20034008100524800d94035000760306040b00d20f503070302403414180140180c2c04c6030382c0c421080da940501141004510801080000ba05103060903c041ea40012008103104c0c1c3d0070300010070045140030ba030780b003400aa6200d440c19107060140c1d210710300c00035003041824022001a4220010481001000440c60004960f16080401d113000c918902107132030014503138109044c01b8940b0750407a40c26005801121019001319441c2c04080c200e00107102d40b6840400e0864a0380d811038800c040320705174100002d10b0101001021540034103840e500c26401c02e00049403038500da2003128098104d0390010048a40d81081c020804c1190f4600a004d010b0201c1c5c2c1d00d00041c10901040215120000c407481c0d0b20402c62280004545d0040c2070b40350a100c885060b16803d4940c10190f00c2d034031004c01401d0f10340c500f04000c000d1500780b0280d4000c109005d11010300c04c12541c40d40180c0c0c140c07650602 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 724224469 1250 724223219 724223231
    0xb0c0c011805030405040b060d06030305030f0c0a050f03040f0f080903160e041707060501140103060e0402010207090e030d1404030207080d0219060e24060409170a030b13050109 78
    0x551880c05650301502039042000300b0840c515040c7d2240c1c01c0381c1d1018142d0750900303440209810456605a1043c0c01064000003000007840c105250958445540b810040c10103824200007003d03406007441c0c20780300401c0080481c040c800a618110b002e240d0150390302248200f6490641030325001b08201a01034441e54a030080214078400002d01900c0d03402c5180c0850b42c2e19601d5840c41c540f901041920050800c1180e200480d21600666000c0d0150f00c050818140c0210001400ca59490740038508210500c001c0c000180e80c00708000c0211000f020010410200094000e4154441c4000184804e8641000390145800a080f036901c6a8040d4090301c2c206551020300c03644440c00c602c2c0700d20058001e00c500502d041c0c200c82400030841d01489001035000070218907145024400c0001a00302900c0f040180c0c1c41c42c1c0d51144050303202000365001d20140695680f41c4a07111918509005004000714025203818401d900840e07000c03100914000280d02c200036500010807007805981c0c1642d00f040 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 724225719 1250 724224469 724224491
    0x30f121b070318230a2907030e09090601140604032103020409090b04060f090f060213090903080f0912090402090f040203010e040605070903230f0f030c0709051003030c06090b0c0c01 80
    0x20814803200c4d0b082c2102d6000311b84240001598401c000c110117002da0400681681d489105066108191140082210b03504102e980001d081e102c89805108501c100400d00005080500d498083c401c41c0c032844900340c01d070483c03d034068000d54008050241c034050010381400301310b00300b84c7c6c01940640c804120000401d02d0740d40945000d52409403031020420454800200d2a50003880b40981d800d00c040c400d652116000002c0e80c1d4405819000554420b040c8100740000381e9005820401c40e0004048055040c5013650700d82c022000750611640d40451310300941d440e0416003040b6070500400841d904c0d07031030308182c50311107100380d6003501d2052910700005d0206002d01c0f8a1000e0301c0d003211030b04d40c110b50142000701d110314455039a81c205000c0c480704440c1a070820041558038440f50006175465518501d0900d04c0c0003601e078480c0c0c42c2c840c103101c2070110316280f03504100e0070750f5014030b017880c44540b01c0d04280002c1c180780c0100078600c21701c040401040107034000c050400030411034000c0c45411042 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 724226969 1250 724225719 724225739
    0x5030706090b0a09090c05070b0708160f09170109200306151908030a030e0c06030f04210e0108070f0e09090f030f121b070318230a 58
    0x940503480104455010a1021a00c2000a004940c0c103030300c0c02418960f21103070a08155a000407552012910110b03240c0c041084d6485010307848659441c11a2691a0004a0402d4003040c03012010a10515031400075285104078150380c00b41440384165800e01220f44003450090000c40015a10101000342400f1407500000381e9450f0f0510003001007415485058841c6021080169134580c440e071500003a81a02100e03452541c01072014601868450305410405000e481103030600c003100d5042406032001075581c51043d01d801c0a900c00c500c805a6403145003046602d81b80ba0107100c0d0702c41c0140c107035216445d444400c0b08a107480030faa030103400b612481400d070f500c08840d0030188045520760000940c40c1c00d2061503035500043c0e800c21201410383c07601c0c4460540e4060801c4610f110390015240c01c0c44440c81c0c0001da005a2500c518210140807000d41c21103034081c1f44001820003446184000407014082004400f9164030040e03000584e000042400125903100011805002c030f44900150030041 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 724228219 1250 724226969 724226983
    0xa0e1b0c07050f0a0e1603180c1e030510020705010902031615030501150c170708030a050c070302030f0d14010905090d14040506070f0b0117010609090201120c0c020402030c0406090503 81
    0xc110341ca9440c0c0718000e0302d06c854002c500000d410503944915008524141a18020085008241c400016130600c070a81034040c41d2504003103501d02e03610b00e0800c0051000207079114583c01e2050016195800d503c0c0040c050040f51320041c3d0b052007121011040e50514160840440d88100700000410300045001d50070f4400910070000a21480501c00788400c0c041c6030100403d52180d6087c1400c5440c0c0c0c940401d03145c015484c1526800004000c10184050b2481038640101e51110040e00300440f580c0c1c002e43e030b13100ba96031400040d0804149075110740c80ca504480c441031078660841a40d5030315191200b0090100b1100b18046103e6030040c50340e080c3c013419600f02c55540041e005803420b4180703030901005520900382100d03140000140400800c5a002441d40a02480c41c1c00d0801401246e00b41400c4d03846603000052031a180034040b80041c0e801c00480c035410a28007602013507a00c1c20203000e56042c0d242c0c16000c2e401900000030030014103145001802a684241c030749100441d1103078145035072000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 724229469 1250 724228219 724228229
    0x6151d030d170901060f060903020a050f0f01050c01090507090b01080a140a0c050c070306020a110d050301030204090f05100b18010b04090e07030f0803070e010c020a0e1b0c07050f0a 80
    0x4110742c0c0e114031180386034814507402005a4004106141d84401c91240041c603680202c0001354906401d008600d0320246020042000300c4058050503280000112002843c3e04803a0621000007415030501d4820b41200c0b045a070003509496040c4d83c0e600c50704016009050030399000900d0000000e6100b25140700750059140c00c0420b00d86140d980700c080d0401400700d03400071001c0c403601307028440c00c101003000004003441c40b030b20025840710300502c3c000d450f4840311032000a81e41c000c03004980c21a82c1c03180035130703045a404550104100d07540c0d0402c030402d1a03054101901034000c88404005400468001d4000308005030769001540c0c06007048002420b800303000c0d40000c11030401c400c00c003a2803150001002401590b003038540031656030f81e480310792605011044800f00004000c200009030001c0003100460004e0a0640103036900c0c0d80090100340150154070aa682d2840c00305118a10488262030523145c82840c01c1d42e00d500d04010b50b81d603580a4406c15201d0440040306c2d5119003031564044080f11 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 724230719 1250 724229469 724229477
    0x1030506040203130221070b070209010608090604170c19050c06070b060904030e03060403080a060504020c0d11010b1201061502030f040e0c091f110d05070609020406151d030d 77
    0x285159003000404c0d9115001403458106d41d00070390300d1380d541c18400c01004202132125181c3d1070f005403061140024059020b48184102603013007280801012034403a501c568020710300c20b401c0c080c1404001250040403000790151040d591201d18401000d00122101409070703088030400c18080c0108034051041c00d1001340145800070124800f814641c0f101034200788607080c001d000308401c1d07020174540138080b238041c2c0005001b0740501c441c3c21103a11a200240005560a516151185584c6a03441c14002e200a0400c5052850086601030a40c80003004050082440c018003c01c1d0030034a020300014028117280c13542230712a50070914000000c0f01d0251800703012043c1818a000c0850010b4407005040000e4168108030003136043d0741e45090b02182205800c0813254903800084010010086554030211551101461400c029041419106001d0f405280802c40044920104001c2e02da0740d4015070810f0b20507034007009450f4200b00c048512000d2105800e10504034030007091303591411208148046 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 724231969 1250 724230719 724230751
    0x901090b0904060b161b0b0301030f0c080f070806130f140c030102070c1d04200f0402040b0306010807050f030c0904020c0604050c1201021903020307090812070201030506040203 78
    0x26005080140c8280c1000a00020f40250340c0d01807811680c1c02401d1184c2c9020032004a4000c01c624802400c80034445000700f80151810b1501200762840180409007810312665405020000041c015402030000346058a030342000110307885545420314020400c41e8000c2000181c845010a07082640c1c0d07640090355007050301e150781c607503560081e001c80d246141405040d001c524961424002403007054824440c01c0c801626250001c0c4500300d1001e40d00118030f802e60180000b08450080d40e0341c0f11680012030903098920312000446454180d181c15401a0010900185014008028520403642a2a500025a2003c100b102c03b48221a807800c0c418006201103050b80e24008050644600040c00c0140341c07426543d0114035206003128100c500d944400304050450800300c02e003503000c03d211002581400c459980841800c04c15100c03103810154080b000900091103070f0700c400018840d020030b8641048040c42c03455200c1e07221040681c0420309200200e0a541010302c2102c0c030a6050390892046 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 724233219 1250 724231969 724231979
    0x70305070801241707030c0f030b0a0e0a0b09340f0602100b010302070f050708070506090a0918080f030f010f1206050403051e180a03031b060603060c021e03090109 72
    0x40b04c9a0b084207401900c1220001310014a8015880014000d40c6c0103648010345580f90440349210004c00501c0d01c14200b810560120200081c90129070b94003000040e4a0303a10101490b18016440058200004c0201e01000521449289848504080d10341e1400b03203e07140c01044040815901c602c1c0f0040e4800e200344d90301c400032640280002a8140740c09858a1450f8440307070280b110211007070741c03141c20064003041b007090100b05001c02810103842032814840c155000828151f0540f0801e1a075030703100c080c5144c1c810905101c1e100790300e85c0a0703402d685600d0b4800b81002c9070380080b6407080d5940c001d14008100c040e001c58980c0c2c103c44050007100d40c8003c41e50354000c00b0701400b400440c248a024000c1e91020386845010202880c8403030700054541221100f401119041c00300198082c6c511501d06002081d80019280b8000c12540340d031074041444c0d4a84600240709552024000710310b4428201030441c1d0208206101000342c460007907160240817181e40d12032040000007030114603602c42c2001 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 724234469 1250 724233219 724233239
    0x902130902031f06170f0c0a0506090904050c1c0308090a02150a030e0706030c0201051506030103020d14030a0f0e010206011503110913021b121204050c0307030507080124 75
    0x1490040c101282655651000e10900d105917038444c140d035080b5811918403140b08000450361134404656095009180c0004601c261058040755070042c80c410000406002007048602282c0d5000703018100140c00401c0500c01d903101c500700840c00614980d000c61045800069490a101c3c0c0080034002102084640c60110354030807040b24041c5501e51113000c51144050009100804150320f0104611380303055002421100c0062500701003143d401d42c030019a450360b00aa9054950558540d480603001d420081c1090000c003c0c2c0078214400040c4c5401c025510003200840c0030b10b980c41d04c8252072600401039886042c03d000318940c0c20100d00e2030702c000a100340c100402c080c0e1011083d51a02481c00041441d51158140179601c1c00d80004140d032103103406985c107083c100000ca01501000300c0981d0b010ba424440c4c030481001da10182d1000c01c05012062003c4207880c44000c2c1226443c542c1e0303203800394981c01184540003c95290405095041a203460100358104524540d1001036040c00d0b4100c03 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 724235719 1250 724234469 724234513
    0x5010509130f020d0311211e13091505030c1f0909051f0f0609031511030a0c03050a0c0e1201140a050613090b1302060d020a03090213090203 62
    0x240b07100b442c5007070381e40c00340e03d030503542420042c0aa45c038880c480744080c0e0818031308210054404400405542e101d54002207135000d4440455880080c030043e440788031107101860180228003003c011203003c0005825400d9400b4071041000040c80c0203809076228200341d03c60b0070113a05a40c000c050f108800340000900b8228061140f69410700f40c00c0c1d2341e1111285800c6902c101d643d819042e00c0f01e1024061445410744e1075009000c5c00031962042d0f81040c9000b840d0300400d110040c0400c96407009810302000c190405034400c01c6280406460303142c0f40000601410700f19400b50080707490f10b0041a0003900350700070740c0c14600d0203841b40552959000b050264103062190000c041d0f56030790052160501c8010480ca0255510303031741c0411281410800c001c0c2c2542c0609803007004620384004280000c251101c5564000c0c3c0070148602c0303100c03140c000305119118802c0c0f505101480002c030000200c0e019481980c005000303803014040103404804446c201c0354101c2001c0e503d81d101c0410707003040c159004942c0c = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 724236969 1250 724235719 724235723
    0x3020412151d070306051501050a03050603030d021c0f11040329070207031e030e010e1212070309151e051608030115031a010c03020307050a030305090f010501050913 73
    0x350002030003040d00b0780014010b038240d2194103c00030800078003e80e40100740e00302c0150002501018100c1001902074450b04540100f8147c582000800554090081d1800384001c200103640c3e0720131001c15040344c0e40010040502403441d0003125008000284154116a00441c0c0d020341b9190860708c0b0782d80e9807150504003404a0356520303050b42e841540454094040c0c5441e400801406046140c82501d000700407a004e6124a0040140400310707038090036541c50600d003800d040c0119400c02c0081604080005940d408030320078180c2241901c0c5d03041009040882c0280e031a2080192200c44ca0540ca2581c481d0b40c40019804501c09150720412961002e108882810281e05d010161040b60078001d01b00b0740d09542480c00071004110090420a4000107416a03280802020048401d1071380307050a09450706042042401e0030508041c020012504840d800c0400c441400f00d42d4540200680401c851200c118015002000300e410014000c10b8181c0d00000c180b0061a0f070b40c0082000501050001 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 724238219 1250 724236969 724236971
    0x222606161b0611040f061106040c05040e0a02151c09110105092e030c080f041101020307151b0c2409060903080402042405120f06071d010302041215 65
    0x201d0283c614500042c00244000d10384031540e1807810201074420381001a031114a900b110003003000240f03081d03d039041920740844001519550500c003a43c94100b920034002d40058010ba00f08c0c94503000705010704a0402c1c00d402d244800c40074280349000782c03007907544010211140da0126520940c00351000d0700c4030090207407003610014000340400920700140788d400d40c03102141e5261031a0103585400307010401b6a260070481824101060b016100d0800200080d16000143e00b0313074400c0c0d030b2081c000c440c54190001c0c42050b4114072558404010000c1d0000815076283d50300c46040250b00032039000d01116000b0020344094030f60f21280c1985410900c03485440c1c1642c40708040c000900d5881200d012901076035560321149450f02c1440120f541149420921994030460400d10800d80c00021080d10010b1360b1010401e0260a6214900001a80800624020b220802c4003c81c0e10400c000000307442c070700034010003180200041d0300301d1040b0700690741020071411400000c0740b040b281c1c2c0c216250813120 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 724239469 1250 724238219 724238231
    0x109060f03150e160906030213140402010e04020d15080708010606140306010c080f03100f0b0d02070606170609070b040b030606090d0b07031d060606222606161b06 72
    0x41048904da50b96040030101d60307074802c1309100754241252102d6000328074820400140e42540c9600322480d1b801000241080f1608200b104551200d80507111001503102c82401150142075400315919005c0c002c0403514440c0c07050016041b00c0500a40045440c1a152400907024640d030380c42842d403008006d01d040c06000a0114009088500100b4a4082c100308550303e03400c4c042d41e60390b5403524a6000341c00000da21642401107408520440341d40c1c8964100c0140e0f40c800c90300d4a01d0150085900903150421071a403001801100491a148940102e00a0383c2101e912100b41d010140158000c1d040e00b040c06000060751410020006c1c04d0550000300791130148847e965622000034001c131002d500107a2200c0e02d50440382c1c20704681c1203204440710007400311450040301051480c080c1c1c0d045440401e5404101500c1008150075160281c507130304000541207000c0250030034110800c0388d240c110038440c80c00002e80c02000f02668021100069403a100c0e0700d4480902c400745809070a40949801d95904 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 724240719 1250 724239469 724239493
    0x303142d0702030d0908010b030d050d022104060519020c07060e01050705010501240302040315021e04080312010e07090605030a110301090b01030b0306040804210501140109060f03150e 81
    0x30600161030b044d40d440c42d070b02500741039195094440782504103009a0048507034809854200e0180c03071040d0301c0103100584403184201e403080c108602480c0d160b541c016110500092046580003644a0040426400e00384450803141c01c0891143c00403ca0741500001401d00c42684504140000c00c1d00500d8094102011070300c40d5802c4440a13071022818000c081c031070380035650740c05070101c8070845c05080840c2030a1a54465013090b2080d40003002c2101d600140038088903005a0740d00ea0f08444080d8056103907034482a00a94076403160b101d8001e00d9030b44c90000142909044007081c4503042e1591009441403a082d070584403a080900414642a1100e075202c213807810101c040d500030840c4241c0403c0b80a04640050120360320710a40e5406600f14108120204100c4412541219484507080c407081d80882030031200754003c10801066035003484621000303443c3c101201410307201c1070001046503e6981040040790202440b00a120b90700760128840c052581d90f1082c540d036240c00050b01c00d008140 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 724241969 1250 724240719 724240723
    0x82202060304030e090a1505060f040b0a09240306150f0f0516081b03043602180901080f0a0303150b04060c1202010915090203100e070303142d070203 66
    0x31142d46c03024a5480e2140c5080500d51440b0b00e004000988041c1d10b41101d01ca0304080c944560f000d0000310b20f80015154051500c102c2002d4000d200d06842e504290030071061082001d11400300000010f42030200100b0110911004c5c010740c402a91140c2c88015102103007079900c2c0500301e071600140041804440c001428044004c08400c0c8120086980ca1103055207801a03145601c1226803194400d00c03042c00680c14010161744803803244100b000c09404a4004014080781d04443c6a00440c00800d4181c5440460b04c1150207001d0200d850b41c85031382c0c84042c0190340e01c180d110103200d503500c00c551040200340071f6400003c3c1041248a4054115141c034662401c99105911502c00150207000907414010060301e49500d4041c507200071b0104110a84403940740404054000d00000c0e900c0c0051002c550b01000603240038008601c09018590300317003e4190b142e444521064021410701c4900b90400c90f110b0049400c282103003070780d031918100b51080d140c0b04c00030f40e000b4456103000208a20300241ea01 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 724243219 1250 724241969 724241971
    0x307121d0102040305100e1203040f05070b0301090c020d020d1d0a03030225030804151e0e1017040809130e0109061404020a06080714040902030601082202060304030e09 74
    0x14140000d40d5440c135600e00306141000854082004903c0c04600c480440e2011600e13040781d03508440450740b02c2c1c0310790411250740c0c402004010070b24459441d00146030382070304001c2c50486104600c200b200c0014040c0c01d0742c40b038441c4600b041c0180c02c4460006020b60042055114441e14505e2081c000380c02b45022402004171904250050b07071010030303100c401c1e5010300d9000e892012007801e5482000d146a8680c0d109008034012070340f01d040f0b008007011005202d0000240c400d42ca401990f00061042d640c0034001520080050340a152040c0b00040d0841c090f005040503080b0b00e4511908070340e40e5031100c51081c0c1244200550100c141c0c0645146e80030f0318001c0c8a0a0280d00c0700001c0e0340c10040c1740180407a41c100590122074900c10041001580e602c06d141d0040383c40c1e03410003655943d60004200c903032802c2c0c00a204c0040c0404100498a18142c1d80075503c80c00302a21041d800792140b411520481000700340c03a00d800501784031781000504100c809982c005100742001d20b440040100000c5107504 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 724244469 1250 724243219 724243271
    0xc120f01090807111e0d0f0b130b100b0304080a051c0f050f0f1501020c1003020403170301050604141c0602030f0f0601092309040b101a030712 63
    0xb4046480f10074803800503002442e500d812669000606520b00e82d200402d0a46a10349101d1040c1a1483c001d0040e141c40c13071b0811903802411028546005544404901d1b403081c4240d945082c000000307108000740141c81780c1956200072885041d691585e44046590b44031101e503004015081c0401038103032250b0300c020800f156040001046040f203102e154000c0380d40003802d05004140344030a004a420103181c1054220940d01500481440d4180041c1e25110401000ea500302c120388800e50542ca03450f0703000d44161f03403254400120100510082140340d010038015180e10800422040101110000151403008409050b5075552182070424006108000c001500c10310b400000308070b03000c0c6001c200349a00140e4007801c05181c0c00d14000080005d08180900d103900300244031000050300a2200d130451154009054112a140500d03000804c03640c1603901c0000c100142d940450942640380d88013403040d101d07907803607800c1d555403c6007100c01c03090348040c01107065904c40e8040c02c0071580060407070a081e = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 724245719 1250 724244469 724244483
    0x323030421052b0207080406050c0f01050c120a0908160501062322050c0c190c0510031404050a030f090503030a051b0124050a0308030c09060c0709060321020c120f0109 74
    0xc2006a414204410351280c82d04a900d08410000903683b0380041e9100a00c0d254400c00066a44601c43c10040205d0b08020f010316a01050b064662100b01d0340100045109000a05c001c903514020100a141d000c50310a00c00102020b0417401400c0060400308002040400d00c2c81001c0c00640c50380031980140c6400841003000251b94811407010005460444500040340c2c26035400703906ca49848020a02420b8803400d08407480d801103030f201c0d0308401c0204d1850f50240c1450b06292400b20740d1900e52041c11070110361085484c0300c449004100031000c696000c0c014510301403d1801c00c8030290300c03820f04414209140703c09050012400d1280005c030f034520032044079200700004000344010303400ea8016881008203035028000110042d00740c07070b00150020000d648910119001a096005120034212103220b450000500d10b0520f030410384c1141d001e0a0b01180d0899045000c0030a003801d4110310025a100340000c0555003072041001214024036015200701020769000c0500391494003e05031005 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 724246969 1250 724245719 724245727
    0x6180408090909031206011b021309020906100e100c1203050415060b0f0c01060b07110405160f08270102120a090c030323030421052b020708040605 65
    0x241001e000b03058200009500440c14a0004802c4c6881440300400950401a104c41d070b0095400c45007480c03101c2c05600034024007880081c020004000c00d007251043c1d204000100c04140c4509113001702c51112003042d544c14804808400c14418004400d105000c200b044050b15100803c0c206e0b040360000d211150b40c0800c540c185800c1902500384c07610001c02d4100d02d440ea080203840c0b0f01c0c8044450400c0340b045e4807501c54071b60456940c01042c1c1a88078140c800400103121040004040c0d41303049116007124100015210140c081d000d11507124590008207204882c0407000c02d006640c4564440302c012038002c00805609640c15051166000280c483e0390086142c0001403c1200d00d20b40c802c543c10020072240341d00b900c42c0c820000051101030284600c4240c540c1d100d0b00d461408403529030746441d1a998a081c1031601c0a40c581c85a061400001810145844000e11817000c03039000d0107000550035034100c5019400148503029021006459900b006000b000a01c0350380030b00010819601d0781515 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 724248219 1250 724246969 724246987
    0x40e09030a0f0905030307060e071502030a090b0301050a0b16060c0f110c1503091c080103050c040b0307090c02101401080f01090c06030c0e030714011103090306010303030506180408 80
    0x151480c40d0505003d0004040d4103103d0354800100346d40a01d03402c41c401007048904d80c100241403425907080b90f86003030014440f402d07000d030300080200054080c954a441c11156295104410b60100b8025958060640c450810983c01002c3c0580b62003030742e050034148604000c1e550354007100c2c0d01080c00c0001c034140440344546d9035000640b164a01e180d11015040321800c81000031900010340c010881200008000f00700c03e0031341000702c0d0a008c600c00540251074400100042c1044130709200444881c400c0d0001d800507401c2038000c0405207500500242903003801c020f0b011010f0101d0410703020440c8210010b4040b041d10300e00400078881482900b111255040000351418000c100420001c1c50303060a150b90005035031103900904032602c918000804407070228003140c0307825661024a81c10b1140b41808142941b51142e89011004240c850401000c002c22600740c0780d003d8140f00c13990642280c1c0c010800b2078001d40089520580052485501840d1801c0c0100500003e403400d8410b09800300e91098 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 724249469 1250 724248219 724248227
    0x40231090c090b070b090712031808010e070314010f020d09030e0108091005130f2003070503070e0406150602030306030d050408062a0d0f0f0c050a0311040e09030a 72
    0x441d0341035501e450070750181020b0a2034400c2c8652000101000e005100180721910113005807000b800c0f080c00020170418841c20000c01d02d13068494032144140c0049800620008140702d019600c9804c4805820044d2850310f40050030180c0071148800e03552188048102d10303a01d032006050031420301c030000030020440c0c10018611980e0b0b1070214140709a100a100491100040c12201c1103104000440c0303541c0d0703461200241c40c125400040284101000342010031500e0303208905000b0f1028601c2c065508080e040654036001403003603c0d00b64000410a1012000c034040681d84280101004205594601010301d1100343c103a100304c0050f04044140051480d0601c4404030351401d9203880c0d13081a081201c003e484450240500d0081c804070031260040241c1d0b2540031a0001003d2030031903d440c0c941c0f81c91005480c4034003401c0030341441c16845034100446072266003014500360707990604184186000382d0007819409050400140e0621001a031450510788003441040314201030b503111011540b02070 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 724250719 1250 724249469 724249481
    0x30609110d060e041e02011e02030909060f130e010b030d0f0f0302070b0106030c020a0606081f02040f0614041a1b0a020f1302040906060c030906030b01020c04023109 73
    0x4044903c40c001c0c0800300384000c800c5000b150100000c1c1d170168410b8401a58109141c040301d150f50220003540b10446030b008006480070200030741b02a0410340c0c03400c2c200084641c80351740850b84490702d031403290303501001380d8041038800001400004403031028000091901141d2001640062540f200c0ca0341055840080302801079101c0c2415030910340b050340c4210b041c0e441405000308240e9103142d8058154400c10400082c681c2080c02041407544480300c19496900b0746e030400c84400b0340c07110610f1911819100302ea040360b011017031f1400d6190404008031178006030055120844102070101064040f104240e80c0484814021a00d6850440c00c0d003e201045080d08140180d4001c1c25400000d40c44040300d4903440c19003120181000741d02610000c1c028080c6400c2404020f00d0030313001088003a0002d2070011124000c0d285c2411781e607520360045051781d102c0d00c0e10a0040e00500e511000300e04103034015082802904030b00c00e4650400454503041c00c1c0080304a40552402c481007001115039512401c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 724251969 1250 724250719 724250729
    0x30d021b06070e0d08390a02130c020f0615040b0301020705120d060803030907030b090d0f0f0314070e01030f021e0c0102130e040605070e030c10030609110d06 70
    0x24112034900000040c000c020b070141102e00803c5901003941c10000142d01b2501e032242c442c8601e19440c0395021140400601060003052010404044105a403c0003e62618283d9000302414154402017068001911100c1414801e41c80750025580706070030140202c6107d007402e000740544407185c50703041100344c0c0c07000b0f541940240d10400014000c01d0011a4107a01c100d041e4941e5940d40b1340c04d02d1000b00501c0c6a910410342d900000c0140003100c000841c3c00c0d0101c030301644c281c6442c0c1d190b0322070294580c520782034550045201045440780d800d0060900d0384a480d05420000750604881704100541c2c2c01c101c070311000240020841c00d00c90340c0c140c42455480d400e001421420305004a903040038941601d00c040c0451f900202c1d82400311602501200c035140496071500c00d42e0b03541c2d031160041004066904442c49401c0c10005401c592240340c040d00707208801002080310800340d1b0103100c00c05458448100426441c1c80c070104400360f07107008800300c038100024615500c0c64200c980384112840da4000d = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 724253219 1250 724251969 724251973
    0x8060a02190e060a0e12030406020105041208130b041b06270b04141c1506051503010e060f040e0d021527030d0903050c01050604060602060a0b04090203030d021b 71
    0x320b41a54a600c016124072040714100b03c005481c94000240805444284055044c48000380c045005581034000c18040c6114500302050300010305015aa0480300700d52092041304400309410100340c8074a45c1076042406030301e2103985076120310320b2840c2c160001d402040224016a11040080c0d144900e201521f0404081b00441e903400c001c10554644140d02c100c05443c084075443e9081a5541540d20340c0c1c00410512408c50700d2240d140444845001841c2c0074000c518110380019181001041084840d51061141e4a103a00b4051800401100070b0141500454500302011300c68072280710381c40d82072803d40004e02d003c0c0840d1500901d80090f100e0b003c095420708800f8000d42d020b000c00c1c100248541c1d1411400144002c1c00030601d94002d00d09007071400350501c0c036901c00740340e0054014002454800000d101039175400d010310003641e03802d100300b0005901240024441206d0355024000c51a001400803e012105400080c0b4540100700d0055803998000b44a800c40302d01c40b50210705134010200 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 724254469 1250 724253219 724253237
    0x9090103061d0622020f090414060c070308010302040f0e0d030617011b2d0c060c0203070b0c160b0a1b08090a080724060303090b131701020408060a0219 67
    0x2107100044e503d00d40801a4012032a06842c04666480b209041c5445020b0a84601c3e8134150030130105006508014807803038014500814140c031100c0e405c503580160191980681079186500303120090407202c80c5142c0c20359991000321040e44c03040c003072110a0981554007141d200d050a104d03180042c48003404031b070305a03d0079420154094403080800d41c441c140f414078640030b416403100e880c0c804c1051940b19492110903118403543c1d640011000c11428011a410840442c1c03c01c01a41c1d684200c900140a500c6100c0005103115840402080e61b04184074800901800b140d0f21201801411303548881c0035905c8110405082008292004465040e850203400c5800c4c000500d50b1070303c100c1c0301c018011040019000701440303804a4900e190b003259500004410300307030310751090040407035000840000d000e055002070001c0010040e51403408150004000c01da20b40404c2040100d010b11104a1554003440001040c040c00e02c0002e02c902d40c40d80000d603507450300180101a204500d0820f4051000000c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 724255719 1250 724254469 724254481
    0x1062d1701290901142118030d0b01090510080a0513080d0c0309230111090a05010309020f0a0b04150504270b0a180e010b220209090103061d06 63
    0x184981ca0401ca060400c55618405400101c0d0000360080d40305d602e0a80005020b08400710054050030072040b20000000c20b40c07030302002100340c0f4607100f40120b000c1c2e00c28071081c9070640e8258442c000075407050500860040e41c1da00402c0c9a240c20600c401e000c1400d503000c210151400b402059070100c00d80000042592a6659448050040008010900e50707103074140a51035009a2285008a410030510211000082000d000b00c10020700400030550901030140780d0f02c40d4440c01c0d0303200307158024456081241003c00440081c00f050b501a68001d607401c2d50008a6201c0b024034101400e5046101c85d55030f803c010304000c400d1a09a401405c0040810080200e4400c000c04440940c100b440e00c3d207101d55481071500c024242002c80b11303a00c42d00800d0300140c02161004030098a0b40c0d120310038008078070341c84445030803681d04602044d0000c030388000702803d03203a4080c80000c1c2c3c0c4800380b10060910100101107651172009820460300b06175950308040c409822407100140b216503002c0203241602c2d01c2 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 724256969 1250 724255719 724255769
    0x10c140c030406080c13030b072c061c0f050402100e0a050405060d02040515030d08040803070807111207060501091812030e011e0b1801062d1701 64
    0xba1203601d04010014012448145280045454221280710000c02c22902ca06200808010a84800d004595100101c000c014142c0243d940051800c00c02c00580b070000005108140e1701440901d08400e000d80004104d03900e8511031001e0000380068002135030310f828418852078440c420603403800d11440d00c1009100b5a1061200800d485c0240e8000c40c10380c40d80b001040505400e402c00962040c208420040018080403520300c549000310200d8a203c01c00321801e45035034009441c0940030b080c0402c00030b145540514607060b00b108092034400d6804120241c000e0031f110003010444038010780002d09000303010b61405118003404900d0403c0104509000400c8444020248010200c01e44100300c4111103000764807019400c0d815070000d2000319040d00600c440d0754441c0c145142524a442c54031038003400c203400c040e200707420305121103000d030303400c1007000c2d255001101f088a08800410313450300e884010090000010301101d0301c0340006911200030395614404141c0200c0007607208410840500d07515 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 724258219 1250 724256969 724256977
    0x1b0501020a0c090b010311191e02030d0e0327011d030d271205012f0d0914010e1005090d0810031b0e160504090e070314010c140c03 58
    0x42224006540305004c8016405051a40ca0316076400d0808510041d01021441401407400c4143d510301d80080c02c156284458040045600d8006900c18000fa202d081d038990300c44401c5480035011a42003409141d2825800d401c42e12041d500c044417038030f90f000b240d60010500c8280380c1101128910902e030203801f107a0b86030014502c100820000440603400d603001d481c0e113800c2c6465010340c4125966110f4030002081585c10034211900e40ca003500e0007821840500c0120862440034084400040704007442c1803c0b900040e0812890603a6070f00704800298540b501c4a900c0d108010020270b01c0c02455043e00c0c14440b20f0480038909508000c104554450045451203110100e42061900b42d01c030800c2900d05100d090b0070003044e190051902a00082c00155002e00b12142d11082040d10f40d180e021030b0307011903004846000402c00600c4284800740c07440d00207460403d10a07046400c02d070340d039440790201640307040c4500314665507881c1ca0b0401268012903000c2200b90780302d40145044c83da08182c6a0303a1103 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 724259469 1250 724258219 724258229
    0x90e0c0907180e070e130b0d03140f04091d070f060f0905041113080102040b0d1e09060e150c030403140c030f12280e0c09041b0501020a0c 61
    0x4040203440035101906500c0c42d02810004040b1002460240d402030108815544018403a50307004122182c0e40100340582182c0c0c000160203121104010f9400703581043d504102d181310300a0600c000034145413850b025100400c0c00450100b0303148094000301008000050f41200903805c0903005000b2030214440150480381140313070a0201c0b915110003103811611603041154428100f01c118090000244040c100c4004125100440c20b503941460900300c0c031943c4210380e0103a41c24015441c030300f8015446503000038440000300b500e10b06100c240c8401c03a001000200c403902d5951200b915202e40800c080504c562507440e0303038090744c10b0640310006075000082006007002394011131010324240842c26038240d180d51208882e141e00460020502a4002c1104101080031103800500c40b41c6125140022010f1908642d907050340800500700c02620050101c421903110712410040903440381c0380700d50312590164008400b118001800c0440e4280079a20480c110740c088500b00020401c2000d0ac01c046407 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 724260719 1250 724259469 724259477
    0x3020a08030a02070b010806060a0816060f092d0909050a0206070201090b0f0d0b0105360a08010f0f020703020618070f0314060a02040f0e2e090e0c0907 67
    0x280d0b038803012201911a080004110b41c16060000034a0080015558000c1004403448003010380c60708031031b50b030b500344484c2d1045081d404840108507080c0a013055008000342890a1040d03540c6540b58902c1c61780040764030801404015444420f261100311881c000390100d0320050184440c1903c40983d1407074588000f9114880000d0383e0002c6a000d00703104001462944040c07074484521454040c0650096291503141c203080c0001c04010390b10520840342c1d0460911b44818410094000800100351220343c003150200c2d40d00300038101c42e0b8490004000422180002041c1010b44040d0380d410b50b41d1004e050a585401804001c0009030042001d5038400480e21002e0901084200b94a29181c001c0d480550300050407000402440f014254815400d0152801c8605584800c68048100c0c0f045110300d91150480c1c0300d05000d00007a042965030011000511818940000520415824640509071440d41c20301c4508110b40380340d07801503505078040d200242001258110100d0050003004003118108 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 724261969 1250 724260719 724260721
    0x6080706031113080a05070e060d060207061e0209030f0c0d0209040c05040f0204051827010e151e060f01030b03010e0f39010f020715020a03110a03020a0803 69
    0x20340645400e840120340d9079008100116030310b844c60740d241d100f15201aa6035000c2c901000c2101e01d000480c0c070f401190007800b1020540442d0b00c0f50b0000b500004c1c4110798503510b0f100c40c5045901d9511100c540001101001641c1e1080102050300d4000708040c3c00d1100d4122003021121a5681c1004145080c0c0641d25201103940703518080130254582d130081503000b403805014040078000c40d4042c20071b995066690703c030038003001d00c5d100030b8600b02103d4a078195544c10b4903600c43c1e040014094140e01d24040000310701202583c4850f42010341084400e001054520108821201c0d4050101c003600180c00040f103080c20418081000e800041001034141500c1d01ca100c69191400d600050800700550f050b60210560307141c9554560802d48481400249442108040359443c015120001c00c5051404020601508010340e46c60004240413825030117103070b5002905020390b03122001c801d190740d805032881301c1c000e144c007400d01cec0059200c04804d68032070206100040c1e000140e001c00369400802090722 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 724263219 1250 724261969 724261991
    0x608090304030204180b25021c050d06050a0e04030216032d0b091e030a050915130e010807060c0201170c09040e01020715270302030f032403010608070603 68
    0x5030300c1040c0402000861103204016a0220748800440c41f900c00c09000d0240501078803040f070740c4242169040300010f082d600204d240e41d01801c0100a0200103000100b1042d680c6c10000760361183c01d40c0208200d0030282d0810003055414030803060503001182c43e0311401c90460711000c01110041ca901c0c044041c0c9011010360102c070001c107060b6059440103045150380751032000240c690002402c07429140740e015150903400c00c8003000b56400c100c03840c1d85032802c00fa01402008107003841d00100d041091404c00c03891600040c2045c0d018080c01c6d4002c071400855242c10322841c07402d055607200200300204412000010703a40800170b810b580940e8400001d003a142e04242c4110344c4181510240c0c8540351032440e604400301074010b04045070043c6034040050f01924100426160040c05010180d92822802c89203032420007404020a8013a10449040c01c00c41203190320b240e441524680c4613580d40500c00700c0e41010000040c40c5018081d4003d00c4014605043c0d603030784192901940003172580390031610781 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 724264469 1250 724263219 724263251
    0x4060b19091208092d040207020a0b0705031e1c2414090604090506010e0901230f07140307050714010f0605090129090102191b0608090304030204 64
    0x6002454042c8004610a241582c3e6a60081d409180212040000c04d80c1c81c0c91208035040c9100c0810304010f0310001a02c0401000350300200c000c0703038041c03080d5801165011190700907050492080c0029940c5034003503952010282ca03031902414002004101d40b0203000c00340c400803100000c00c503a01159041c40b107481e202084100c100c034400f2416035143d0020700726411158610031203000b51044129a15180d040c401511141e01d4040c0c0a90321100040240d80c140e400020b6006000c5000010117407132210345040d01108084424115640e00c80501400e507004105545c2c118800c1e0901540c41d43c2511105c1906000091010003171150120f000c4c4240a1280040c10300000004000c00008803060500f500500e0903001d0940a044910008a010a500c074001140080f0741442c0120803c100360600c80c10340c0c0050300003811030291100e90329000b02c80644941a00b0b204043d4285000c203135450950320410558400800c01ca200d400340001e15a000c4100d0341a41c1d0140e80119600c00b520003140 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 724265719 1250 724264469 724264487
    0xb0d080a211e061a07032c010e06070f0210020a05011e0605010f0507020402090a120f020f06040e16021501080706140a0e01030506130e0a1104060b19 66
    0xa81256245654291111180d407045070380707000d428034868010b0010442481107409034040c03604602c02c614200040d0035002005042c03e10320070300e0140d5020701300303c100000380840900c00594a006c003800b81c801e1981c20101d00007030407e007034030546d04204590301c401c519244500b001070700805644a182990501c00e02441e11f02e40d8002d40240540c40300001c004107001d11002c2c14007442c500e44140441c1d40e41c4203641022510030650742d03d0703081100e01d400b00f1000b5488050760a80c8000c1c00388000400072101140c0240c4140107261842c480c48460042c01007611404803038500c1440e0402040c05a205015403a070340140f04180a00a44114080c041e840c00400b48442c0040001000001805003400174000095400b541d54030040c0300d44510481c88140154508030000c550810b100403119413107503200981c81a4000c002100c1c20180303420312000c0301c81912035100a90480304003001448a0b644c0c4420141005403000c1040f00d00c1e09000d000280a48085030351280c05030182c5e05425841200d0030 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 724266969 1250 724265719 724265747
    0x5030901022416020c031905010608031309020d0b10031505060415030f23010807050907120f20090f0f0306070c03020a02030105160809070602030301210f03080f0a0b0d080a 76
    0x80350603107d800804003107000040340031945507003042d0010444580220550b03505031980c03081950b1240c140007600029400c00c00b1100500d03561044044403079a04c40020340d003030a01c82e440004800524441446c8001c0480d00f0090042008010410004051074890407405545184c0040c2c08404000c1110251540700c8000c00c0c800080b4bc003020600000f020a035048421072401c40d1a27042eaa0820f01a0355802240d264010442c000842481e0000d0303a0007143e20043c01200009850301d00c0c0d030884103c102080c2681020b02c1d00454000b0443c01d21030054144407038210380031240c030a6480c0002c0c2d5200c00061101040240e44c0200f1410140200402c020350340d40100240482e1404400072003120910344940c4000a810030041355400300046950000c0e149640d001d503103180e00f0319042104060710340c010307444100700103520345010414580c2911a000d03c40c0c0d6a03803043c2d003002d180e2882041d00140c6142c40003440d2503107070061580c8a802c0940807a6101910300d844101054081e11000b901400c0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 724268219 1250 724266969 724266973
    0xb03071205031b06040804030f050f0109032313052b0807030806180117030f0d06031415061e040507020a0c06170a091b0305030901022416020c03 64
    0xc4040041c080b0181070a0251000681000546240c40307699508003900c000d03000102c200400d10210300007494241c19a4000d20845d0740c18510705c440c1301c0c00c580d1070580607030010708100050b040844070301c81c1515000703850724111030406034518180103022540d071080f01e21400e4030303403074502e55515070781c041840c81001d82e00a1141d28109040c00c05055200280440004140600060452800100342103040c6102c1143d03080e240c0c00d02c4051102c205007250080d941e40310601030714000c107030800010460001003440108a01c0c1c60340c98800001858402d2510860700318a46a1210190601172581d1218044403102c0f1200c60001074036465003050300c2e16540003401c0c0810043c220390001038403071746c2501c68103801501d107950303080803200d412040004120801c0d104021800f10030711070b04208409400b90045040149400c0100b0703110460603401140ca0741c10103d8180b502c0d60301803000980c0b06055a0b01500841c5184030440b03c1108014000824032900b050b110007510300c00c001c0030300c803114042d00b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 724269469 1250 724268219 724268249
    0x9090e0d02060f131205040501090e09060402240d1a030f0d03020d020906070b1e090d110102090306010f0602060705090d0609140d1d06040e040b0a090503030a050703200406030b0307 80
    0xe004000d03a02a022301808160010740004005080001191103038280704007030002910381e5400c10950400c08141b818289004000c0351050800d1b0b03c0c01401610140d080000d4404c210115800c44400c140002c41e20a40084042600d0100045041c00302c1444074500107a0360708540b14040024003541c050650401004208030007007207210003195001d19076818151604012104403071010b00c0781291050240d400012281c0d05140c01005c2d405800319110001504198400c80440d1074036009a000c01c00c034400300c2604100c5607805005254000c042c6140081c904441000410200507030750100600c5140c0c4e035003881d81400f15607079001501ca000c00e000c0d2600811094002445c42c030010541c1c0e042105808070703891451801c981100d003102d400340224465030740c403501c86501e0810700401100e4600d0716a04441c0015406000031445091034083c00220f40c2803c080c002d00301c03894041550104412464220f000f042c00000350350441d042441d011030300d0905c14000c6410b2286a50150726607a0102c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 724270719 1250 724269469 724269503
    0x1e08070603020309100911130b090f070822110613180b0102010203090c011b05010606051206030a260f030405031207021906020901051909090e0d02060f13 68
    0x2c1c00850054031264219800c607503424003a40101c0e1502040103280036141503280c8020705000e80020354028402c20000303420311001003c5030f04420100c0700042c01c141090b08028800760482c010300d8102c8291441c0e00c044074a2031a0910800050030302c05040c03e281d44100030712030b503141e504031118a0504008400c0142d81c070305c2092000c5400c5040000b0f00c0d420940707041d28551051080d2845600014001c0142c4003000c0015100032410320f0140280500320081a400b00d2401d0041500a180c10380e11143e8404480c0c9078042c0f1840060001d91098018400b9400440d00300c1e1704840c54001c406902c0c0c5021804030030320070001c1c40f2f650070350502c005010042005101e00480a044207146008040456956951040f42c0301c40c800302d2603001c4960704c0d00403c004140a0307805000000c80604009140501385c03e80350001498a503080d42c00102070442c00e00030010740b80940c4d4000450200100800c41480b134004e0740341d0034020054081a5000000202d04403076503c0024400c41d001010f00700b403210f0803 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 724271969 1250 724270719 724270721
    0x908121e0a0e1c0b160302160b01030b06100c030e0109090e0a020306090c01050d1a04020d02070203070603020a0507033e07080a0c09020a1710081212011e08070603 72
    0x2102c46114641c40d09156100d844114803d101c41948040000d10594a680030080388400903546081050b6007808100d43c11080b000f1f02c8081c003400f070801c1c42101e61561800d00c2c0f0000e0f0090500b80075007510346d0039082e0301ea000000031a010342c0c142011030340c4504c500300480f8121250b81c0701d01400307030a2180402c3c50071408107003420658000d03406c1c1d1380982c3d00d5081555595441c0c400c9940001e0080105000d410042d83c401e041c0307031b6802c0000a2190629400140c2aa0441c8000c0103081c1da00013070110440c6000c211200043c011401d095003800140d01c0302030114040c010010301806505010f140200e02150030316003040c4000d254000c0e07130601c03000a030344c581c401910070711816104000c4045040e0f1400103030304235404c1d40714110754a0103040140c035801039006004100180190045540580304c0c001d48424401c1402c181c50003645032a14400d5454029503500905144000b0000c404503c4041c101460548000201e807040f86131412401c19105402c6074841080c5019407540882c003a41d01d = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 724273219 1250 724271969 724271987
    0x6090f03030a120e030a090e070201091a01090f0b06041208070803070f08151003020c011506030b0102240112050708192d170c0102070f030f0908121e0a 67
    0x28040401240f81c03001320030f5641c0e00c148a4008049141c1c0701007040b48280b829041d50344215107200105001e100765481020820f01500416860044480140003001072441580707101c030f91014003403101000b9240860050300c5a8014800c1c415120b00c158024404003004442880d0340c002c0303c03560b0340c0c500350400601c160080a0481c1c0010640b00c0842c9030002d00000005840c03000818440c0d0803c03500740300741d00070b6001f0304000746255201c0041e107640f20040c013220001003031a510b01148281c0400d000a05010000c1c4000c0c03003564074112990758840010b05844e05449a10890b443c05d08224180540307804800c0c1c0c05508107100340b1000310603054910720a01006803180324004408001a00c09140b41d40400c0c003104500c02003807840c100401d03800303900001c0117203040021502d003040c5000002c1c2a41c0c0700150645520424245c82010180d000720140819091440d02404e40d90400e64180d0321003200b082d8401d450780380402d0a02d09450a288140301c0b031882d4881c140e0341c0350f96a641c05440708070 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 724274469 1250 724273219 724273247
    0x10603020d081e03010e010b1309050414060709062f030d020706050c03040209040f030306050a031b1a0a080a1d0f0607020105190504050a060e10181106090f03030a 72
    0x803c0044a40000c4040e1095074141c40900038070200740d07802e02000c4a40b54002001c02914800c9040002440305290301c1040e0242c2d000f090032900e0700741c0200c003040c500174026109604001c50240b0401003280c1c08041c06a0b002425441484104070a528460a009054900c402503000001d0128003441d0750368004e0a05a01c2958240038580d04c0002296180c01308076400303500700304454009070000b0080962100401d1181c20005100385d11a0041128418240c00c00c40c0c1070104a040744031110004e042180c01049401840608540445400c4016004808248091111007400305100340015000341d1b8885a8000720100419945844540c0c2ea00b00c0303103800b09984c060000030900051060103084d11070300036400700d16030145441d40d4050007000c1c0203100b0750341c0e8015109103400180c26801005028210700c1c00a1a101d042d13100f42001711001031828042011408510344001240ea250070741e5280c2e42241ca254a030405080490301078940e004000c1d0749400300103090114690003180180d0508 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 724275719 1250 724274469 724274497
    0xf150c1101060e0106142206110105100f180b041518050708150f040c0905010f0908100506030309190f05060c03091c0c030609030f081b0309010603020d08 68
    0x10741e102e40f100e00d0303030800380140c000050850f04c414058105610003000031040c4419038026045c072410414079085a950081400a02000003014102400340102900100310300001a412441e0a8031458124412301c1805004004010303083c550101c19840550382d450081d00a1122040c0001c2c00d1503109194065078400707401a2401582c0320301c1e140306e55807168107582c441c1303049074484d10080b10686482d4101160301c8030300d600010703d01c0c0c0c1b614054000707611056241c2d401003a007020000341103070148107051420800401820400d00c000010341c3e9880c14400440010282c881c440482d085118000300c40d900501104050503440711142c0482041703440a21603207240c603407120b040250600c12850600f150358010b12400d6020305e82030000c0c12462070301c105088101403440e40c41c0300d40f461681c1c0c41915010360782c07000d00c810b00d50070221411a400c040d04c1d2241803031409405034400b012900302208825907011000912140c0d007544020051600180290465406880c0000d030680c4020708181c505 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 724276969 1250 724275719 724275731
    0x509070501031109030604080904020408030d1406030a0503070f020d0b0421030e100c031416030501050906010203070f08040f0e01140102160b0706090204110c010b060a020a0f150c1101 81
    0x400b810405071920490005c1c0500002d4940e0345402d0204d400010b0300380d0348142e082200090004040004112031703d006880800d00c89401d40c185000504010a401d0094020070204d9002840c00700450f1069540300303141801141c02800801c4002807003c400400000515060106114034401307000141c0308c0c1c880910b0b40408c10403200b2400e0b2100c2e80d8201200c0d0707000c48a5043c401d040741d002110443c1e9980380014801c25004a00c4010010688102c40c0b4003001c00c82043c0e4503603040c00703040d024040c207407001411070402c980001d40c1d03840b038104068244801141918200701100b400c6070b0003060031281003120542c4036141e44200c0c200078442c0700d02c1d0145c0003862141650000c2003034000b8110050800c0701d55468000410030366404401d0480d551940c40e00703034100694540c1b080381240d0b08040012b40e16040003600003030845070000a00c0e03114442c10f1112aa016030700181440420f540300c94ad9211104140c0b5042c40e240a42c3d607564040141003e036007409459208070002d40d0303400024028007079 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 724278219 1250 724276969 724276991
    0xa03180c06030e0c012a170301120b0c04140915090a23040c030b09010603080d0906050a0603080d2c0c01020d030203370c05030a0b15120c0c01050907050103 69
    0x42e100921600b0001c6c41000600e0b4410201ca40000c41340c514011040703424404129000401e42d64000d8010202e650325600d04202031210095606034032590340407507280703400d040c41e080c0c485495a20403014420300c06c1200244040700c011100c2401d010000e0b240361400d08100e0b0300003000d440003010714091079079440301c000707000e0701180c545a0080b0742000b103d540da2415912900201a00241904859901d074040003001413420802007481c90900d40000803907281c0d51501e482520741c00b03080c6000103802d01d102840814000000c540c480d040d40040050b074030b4400c2c401c0302c0c98103588401d101e00802c01502102980e410128201003001401d03400e440b0504090442981207002c01e80350082c08500b0811050a0580c48a0303944080001180814803804484103440051750800590400000c1000c402c3c07000405460080c00000c0e0b00c1140c151001007036604008004d40030b141100f9044c80c00f9800440c41071004801104c00149580307000b40100c3c58011001ca5403408035208060009180001c6002 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 724279469 1250 724278219 724278227
    0x504090e0a0f02040e0f0a03021006080606030d1b021201020301061b080301090504080c030c0c01110123040f05060c09010e10230409020a020604020a0902040b0a03180c06030e0c01 79
    0x11a84450382542c10799441e02888010022030b13218240c184a117043e410b1011000704100300e00380388286e00410401d0300c42002c0710141d401e59440b211441e4001c0d024484607560104034140060510300d4800142d40c400010800031011601e0003940083c812a03202c4640704040d002036041ea0400e0b194a12800008040315111000028010746030f00014001404410800e422060300180101090303800c081851190780d040d980103c15201c00c0341c0c08400745012550300b20100100760000c0398020042c6242032500c44054001240014251181c00000141080800a113035040c00c0c0c1c010084840d940741004241d4415409076a00300e01040803820002e8191400541c25074002131250381d03541c032040002000340c207054a0722066001c6003606000109890be800d1001e010001d10b00d5000b0b0800c1d00b4280148a003403035081c0c00c01c140f494010401030004003002411529044400d10740004c2e20100f0542c1200c1c4811404c4e00140021081c14000801c84d03032680059030340d2110102130b1640c4100000043da = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 724280575 1106 724279469 724279483
    0x602250303060b09220f0e060f0109090807110111030a0e0111060f060907030b03100c1107050306160207080601030c1a0a080406180b070504090e 64
    0x802456818003030780340102206010146464041d201040304c04442000c82c081c48651080303c0504a91194450701d442600400200450700700f84240c03584038601610808080e5031a00c002041050042c0304021403580c1c440c24041c506841640c3e056803070003032480a00d050240c000c910019121091004143c00007203541c070244101e02c0300001401070011001d5041c1c0c1d0754010400c00c544458a4103000303800040031907019079030b991011000c801070048080c1042c0c05016240304070700020300e40d40140e58001c070702c7d8455540c0b0044900c1c0c0c59070b8a14031442166455404040459a1407602a041c00d10721181e61054601c0c0c10748071114245481c001fa030048641a44401003004030502c280310700b580704044c6041743c074036010b0b10100c01410254082d00261605a44108940600c4048170a0559099120840e0005482c2804014005802c5031180414407403c250940050010102e411 = true := by decide +kernel

theorem cover : BRFrame.Cov 724100719 724280575 := by
  have h0 := BRFrame.cov_init 724100719
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 724100719 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 724100719 ≤ n) (h2 : n < 724280575) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
