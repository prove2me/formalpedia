-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4990
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:23:07.444007+00:00
-- url     : https://prove2.me/submissions/91e7b2f1-b262-4fe6-9c68-3657e1fb373b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 897302158 ≤ n < 897482014 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 897303408 1250 897302158 897302201
    0x3060f030308010305060901021812011e0f06080307120c290a1b170712020c030408060c0f0415110d0c0605060612040b15031606030b1210 61
    0x8905000400460007941c40c5a4a9415420514102400034081060603072040040032020380d41121901c0c414001164021100288141203c0c05082c184485a1100402000383d074400121036000c11350710b9501d01e404120b010340f580380e8595a8819100b018000340411080380035824400c2c640a00744505c03481c038007201c590b05c2d9042d14848510300c0c1e140d6404143c010003081054070307091081403842000507a80c0003a41c4c07544030300641013940149030000c072801200005600d00303000b00382c65500f0b901192411546c074040040340641b42c2e0043d00903040240103401c045075410000d2000d403504d80740da81d12800d241034030340055142000090501d0760180b0552408007807800b001804420300304c08081d25110030f0743c200d5151010881e14001d01c0580710f51014041448004020460554440d5100304141d10036201c52019101045c0c402c200982d26115061190090031742c4005603100310340b075544040c80403000c03072800c0040e402c000d0820b10205901c14240d6401110003032300134010740c0455040180f00b0 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 897304658 1250 897303408 897303419
    0x60a080a050721020105031303110a0c0e070f2109082205010207082802150a1101060b0904050403140c01270b011203020304050a242d0306 61
    0x8140030440251080e0308403a004100152148086121000d22240c4450341015a5400601070740030180c13610340d03a110302c1c501c0f41003058000e01c0a000221640421140c404540b03161070f000700c0045009002c249142000891036090040c1505210034405854003018400f1140c50f4080c0400744031002d0040c540c807070454102007807910f0001e0401c0c03884a02499210100c3d4290241416000c2c2d10490440d4000b6000300444500442c20005441c64003240190b011460b401d18000740308500f40203540b10721920007201c0c918040500403c00b00e8010f84504114850144404d07003200c1103072080502107181040445141d02e803d6000f654014441d040c2200044014015125241c2119501d0081603641d03c0854101c54207441c0e186030f00700b00f42c45408071241e511741da41400030130301803207894030200c020030501c0704050003401650060f040c06441448126500e081c81404201c156550854206644030510301d542d115035200030502c080c02450b41000c0514241d10069410480d680d1400c042d6200700201d071 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 897305908 1250 897304658 897304663
    0x20d05070807170d1815150509070305071d0a030228090b0a0806010f0302041509020705030301030606060512160302130b0a0201051311130b030316050601090c0206060603060a08 78
    0x20383c81101c1020f40c840034581d40d0041140c2200c2100c035900300c080d110400001d41e007803c41000c588119070700400c044000030004039a10200e6003201e83d01c070714040d04001c07480794144d0255110b40074076528508204c007492000500030101c04800764026003405424005030600243ea02051504201c08d4202001d240c15900c10b00304064002103055501d0300c400380c030703a41381080001d005080287c0103407072654503140707401040c003106100003401541c448004080342c010040e4050028407881100355174a121500e4040e032664001d000403a0054680030380443c215203e18180e850b4041601c0158055868181d0742954891041003100c081580800035680c0302d600f071944400090088654064482c0f041d03d10281c00d42e4001072440d040310b0051042403020800c1d4202c0581031140a58100420320090680c182c05480c00c440e800b600b5200000b00500b09642c0703080381d55540b901420036140e06980301c603000b0003519522412100141e0009021a0b481c3c80c200c07005540003280148040715090361554110f0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 897307158 1250 897305908 897305933
    0xf1b07080703260915010f0e01090c020f150405010c0509061c0b0d0f0501050c090307120303140f070201050108030c1b030a0c151d092a0d02070201020c060406020d05070807 76
    0x20700c98005d20840c0c2d03020800500303000e014181030850403d00c0344c01c181e0345518803d014401c85000c02c1d100d403005040c0d14000e11103240c0c18800441602c4400d02d00341e12810020400f0740e8126a650320740074011509901c10026503469610003032440e4500052010158000494064003d00031542c69201c00840c0d554011914621481406100312240090801c42c0c2151401041d1024458080041c199555030206080c03083d20800d0b465114140e006080c05c5005240100317901e80181c6600f4107200c01404640f05461040d0000d81c002d01403a81c036007880c01c0d100e004070700700d4a855900000502c42c0741c03c417581160034031440107411205692803988900c51038803200e40c0b04060035107640c0c2c010300310541d105508403110240c8a5001400782850404945d0b03040c0002d010740c0c2a6030800c103041e00303201d601c43c130050050903600307071669120b0340642e0700000254030180c1c04a000d4455020588074a043c04d00658080fa84aa006041500203804050301e00351b01120003103a03210400c101d800000754600203401d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 897308408 1250 897307158 897307171
    0x1e0c0d0912030c151b030b040606020a15020408120c010e070b0313141518060403020604110f04090501060f092703050c011814032b0902090f1b0708070326 68
    0x3c00c10345801c04000d0104c4203071079602802507080c001e080c04401c1d00003510301d22080d88044dd0004548803070114100034051034002c150175000f1114140320043e802c90141c00190301c2d880003048456141d0f64090359820f807900c62082c4202d0140000b03107034103c58180d280040c2c1e01840d1007041540c210009a410050348170b0362104109600030034443c4030210201d0000c140b0407024014007641c10213031000b0f503542e40004c1c001005411460094407494a40038800c40e440c00c0090b0060000307041c80c0c50443e018007003034050541070172036003240058071020328091124854a0381105605441246c003106403030b00b034010001c3d0300780301040006e030b050080244540501c070340902010801e815510b1070941441c2180400b001e80560040c410503100008681c0e0601101e1841d009074048401100d4110f0003a0002038406580040e0b1031003008409040300a141d4801d0003aa030740c020742c000c10010059454080d01c01c0140492005100003030000e4061444c0d03201096040d90040c0c08c0a113000a031303907120441203805c0e = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 897309658 1250 897308408 897308441
    0x15140f0d0615081f0515100f0810052b140307060c030911040c2c030601240e06071502090f010f0c15021e0c0d0912030c15 54
    0xb031007007081e18184010280007000040c2101070524074007441600d407000c40c0d16852994882c007091400d9451004560841c0c07018205034141040c562019042c1480c1e03132840004500d00c0c6000522640341d040740001500d200030700300b04000c000131705090031980a24040240c1040e410b50b807071002c20380e034103500100007900ca4000d55440c805445d201003902c140016410a02d414200200c00003030b0642c920702100c01003a1800214861041000c5942c4842601182001020300340c901c2185c003078441080d160b584099085842d40d9a0b646000c41c12049115406280c001c0742e0301c1c1c1c10a4070751244090342d030761490091809050624544841c01509120481c15103130a0340007508281c5070400344100c0d03080080074204000d500034405006041c41b645060001c049e0b6034070009440340100c2c1c41c1e05540301c0726019107a10500ca076100340f0f143d907194402c0c041440507102c1d02c100e090425100c0d001c03540c1950104c600d00300d640440b035030b01902c0607049032904030b805005c1a540c0c1c1140300010b1260f01e519080070b600 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 897310908 1250 897309658 897309671
    0x602090405040813060825021516090509070207062d0c0303050a05041104020c03130306060518090c0103020307122c0c030703140a0f05031c15140f0d06 67
    0xa5105045407542c045002d006c000360801078503c1110706c9452008200c06e02c1e0600b1144500c408a0402048411525600388000240100303040040b01c4244080c1c92901c414030000d41312001c2150202c0100d0301440164404203080c440c89201d04c2c11070895814403684031103150454201203680400c2e590003c4005420f050000003410340c1802840e4100b58588400c100c3e0382040c0d11003035400310f54812140d0145800003150744000388104100c903110307101280c00c10986034591038a00c0107003403184200c07449404040d421592980b2200041030107003100d80c00409071150b9040054002c2c0d0002841c80c0c051204640c1842032032102d6000b020b4922034403200d50701810b1b10ac020428584803d4040324040b079444400e600303825481c00603031842a290401103040c030703001181d503130646404005200141010042d000403800c000c000805031141c00c00400f1030940425000320784c9811500441c42181c1c402c2c00e41441081802c00d150a00504014058040c0700092100000b14200108018084078a65034030303039 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 897312158 1250 897310908 897310927
    0x92a030a050a063507090f0b030d020d1e3c0f09121403040806010e06010c051e01020f1602040b010302040302010f0e0a1a0705011a0a03060906020904050408 69
    0x1c150300250010800030958045111000c101500c040b041d4070f0305142244d0480c6143c0c402c1000714400a0024050600c0880e201d900030a010b4086154143e000b48201c0c030301d100c03441d4000b2a12000e9903201390781e0f07820312903007001c032000c00155500d0b1030703e040c0f0040e800c0c0c41c048040250110352862061854140c85400c40c02038403082d0320519044201007010025440c0302c1f407544040c0d00e030100c1f030300d1500d10300c1c90309000d09005189140328480c103032251000003800281c201001c00c61707030704844845c4180310b03840c0d94a81c01569a0781616500406940044280c030441100c1540c1c0c000009541400050a00140d8801c0c001681c0c000c0800f12220307800002d80008500d03207409603007103299085c6011350610703180d940041c10701c8000912907000d0010202c00301a43d900c0b0383d461080103156840e100040090203260707945076984a402c1c19640340d42000202c0d4400e0401e00b0310145800d01c00362800b03071b100b03103035442c1c0c00c004000008003190388903020041d00340c0ca544c66009060040d4014103186a4500808 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 897313408 1250 897312158 897312161
    0x3130609030c02010932030c1207081002040f05010507050c030d0e0f03070e0c03040510020307030b131118040204030c060f0f020115030204090305071203150504020306092a030a050a 80
    0x42c0d00098602c40441101038001c0703020b403401003200d420386d0b810030254074180d0006820024000034281d00035001c1680d0000e0000001006004c460b11300d01540c50201140849070264460760240c842c0703404120404000c154414002814050b0154080d2000d0408d0800041d0408006107007a2001610890f422052440d182c0d042c0d4168040880040c452107107003100080d0a500018020110f41d503010001a05000040c05a00803900729000c0841d90f0745424800680101002c01509008072113000b000b0250b420a48512001048c1665010741800b484009100103850361900013a0410b170203000020005036100080f9020700b01c5502c94400e0341c007141c00001e01030400c3c00c030042c08681c14104c072085e0b0400040602c60a494054078081030b4161141000e442e24401d43d08001d141011115490a01d690f0591140411404452980350765650303400c10001a4041500c41c5544192600b000c21050041020804e2609000342207101c461100d824400c0a290000c03150a0442602c0350104444d14145 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 897314658 1250 897313408 897313427
    0x190f02010e090f15090f06040b1302070c06080601020109110f0a080f070801152304090b0a090c0b09330301090506010e0418020d03050405060d0b0307050f1503130609030c0201 77
    0x1a608043c0d9440d02241d1b403002000b01405031409241c1d11220001aa00e490b030003110f40b4410343c1c130305540d6204186030a0009024501c40c83c80025081400709032a58410700820a0094000080c8403180305000c0c108041e8021000c050f9510070a2581c0008821506100c0004c8070800314000c0e100d41c80c90503064500b55035510b404100c91501c1101e0a00280119002d0426110f010a48941180310300303602041c020103006c0e00c0a407a560b141c1080180004441c3c1240c0a041c1c80b0f0560803e915a0f0345c8958a42400b80b01205a070100b0300940c0981803554009900c29419169144884074220702c0700340d010390f60700c00e8104801c203a40f19000c0214558001d03040c0e80c44004155000c000510101a0310300c40172000c41d02c000e108091000012045c188a601910301401000f04950799030200924420001c000144503903003e401288000152840c201c01e5001443c20007034910140e8444049480c2c4280e44020207455003101444c2044000c5409442680c0100d0702c0703070b00c1e60302040c4824000540170805 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 897315908 1250 897314658 897314701
    0x706020c09010e1b0306010e0a032102071a0913050118060509100b0d0905011b02012901110106030b0103082701051c0b031518190f02010e090f 63
    0x2143c074140101d08504a550105108040344010b46a403101c0780101e03890790500300d1041d40301503840740210504c0750303005406d007000201d00da10701c48180d60794905030703141c242c40d00c140c4422103c002c00c1111184502c50040140300c0e00204000445103180004408856083e0002030b181010108160703001c150610512025000482d107141071440d003000d540c0041582801350b15900c0f1008140b0400c80c1000750032001489030310030004e10034a0107002514074841c0c17280010f03000540c2000021401030b04800408031414034100b0343c900c02c2407040801555101c0810030200340795940c8540000c04a150841c407140a988212520342d502e01000c0c0c2120345141c800d11050b22010b90410600016a0300481196043d9142c5400504000a1540c0c4000140550191560180030304081400c0340c505030032810f44102020509000a01c0205500503511411010b1082d03030760030014042004a242c0e41240203189105141541280c0c410382d0110340340d02000d40d483e0158483c40018044a8007840e03100028015 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 897317158 1250 897315908 897315929
    0xb030f0313140d020301060e060f090412050703111b0f040203090a061805010e0a12140406121b03060906060c1109090106080d020304061d1809010209030706020c0901 73
    0x224840ca01040c0002103120342840028080311041030350310f40084203c00d058000b0001c0103001c0d81c601740389101886c121400c0d8421320201754a000b851400b40510350082d81c0100d040710040000ca04144c40e01c0d40240415000d11041398892083e151041014006220000c4802031002c0d144200340540302583c03180c0648501e00510410065042c0014002c200340c0d040413000c00c907244510764586003281d1205c0050080c0d400c265903c040b1107000940703040800d109030004050401c180704201c486c5d0040182d1480c49c0c4000700410084180300701415007003034003000e43c0000c04220180c0540d41d81c96004e800600801d840c2c00003001188054401c5000901c0c1905180000f00c00950f9a00c20800158064905c5120301030045001da02e030075807114010784036280445560032180d5001039a650402d02c28180001c0c80c0800f28113100340b506400400f0302c2006004240d41003500021180084c0000382410203566080c4503808242d901000060020284c0760041c0076040071050501c22005016003142c206030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 897318408 1250 897317158 897317167
    0x1507050321180319030f0c02150f27012702040c0201020408190f050706090801150b0706021809071227080d02070209040606064e09060b030f03 63
    0xc20120480c0d503082c0c422150304000c030108a5045d0000c14040d2101c2085515045040f104070340c0010b45190418401120702085a9404083c00b08484086400b4030f1319140c0c03100c0e9059030840707106526038403500460001c01c20b030f8003a02e6002000c13020011200f00030f100c040e42441c1036041511072141c00406901c000d5140a0070b0901300707541c81005070202e03055420298810320602101403044000141d1000c1660200d41e982c400c002c020300300d20b000f0b81000d5440c1c100b04c0148044c0b9081004100e941080b4418240f030940d032180b0300290407503146441d03115000c4040181e580d0f01c0030700e00ca04c50941c40d2100c0d075040828180c4c440c00c513400404180d06030702024960b02c1352540078000d030484880d03015046507901d48011102c10041c0c0160700e4029003251005e000d200c20000e0036004442078071074a41e01c2c0d2080c050082c454401a00d00a0f0f0342150303a83c0804440444010209510010070b01a4125000340c0f041b006540422260300030b00c2a900310780c1d5104108401d2405024ac1048019007d0086040 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 897319658 1250 897318408 897318451
    0x10501030b0711120a09050a06090f050108090a060906230903030f0910020703030f11120105040c0905060c161a19111902040f020c0c1507050321 64
    0x700009002402802046112020710308801c1181500340c42200410316181c0140c048050074400140c080c1c00d02c509000c1602041d0340d07100341501011640c4154140c40708518140c0152034000c002380c80d02c0d20301d0007840701d12404190903000718141c0620035000050320f049a246c02e000742e1468081d152401d40d4001090007200303040001030b40d411140c44250703c9650344482c10f20620b04a030032221007002e01d001244040505070190311407041940d103100c09005814000c030300c1462510818071605001441c2e14014041401c082d80605c26400c540e0400d41d0340a611900011019007100201035144d512901d80d00d150b2047e0302d04804d0003050410512240c9e1403042551022601514226000080409a44503000c40c490402a21427800c61030640c4d4403010624a00d503080040340006900541c100100800b03940c40c1442220071401c1c60b840a40303000040e203800c2044002e40d01aa180880300180404008290188014200c90f8140b0100300708511040804001004005140070f08075030345070200080 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 897320908 1250 897319658 897319673
    0xb0f01150c1101020c0907020d02150f270111040305070503031c0e0a0f1a06030316030305042d050c0f06040314070b0c0708010612080a050f041a190201050103 70
    0x1001c941c006464503104807031100407460001c0e00300d000c5500064810601110f15008600004040d00715825142d8110086140c1005c01c80c00381c80c0c460180c01e141000903424010720744140c03d87d0202160361144111000a414252980b40c244501022800982041000804c00041c00180b4084d0080c50a00b100c034404101240c2500e01201407040d02c03400c440031f03803001c1130013001c0e1601d9126041150700800d03030404003142036450900800248290022800d41c0c58000140c0d48800c55501c40380480c0021980c0031009008094422580102c04201c03507500004140c403416000d0f030072450002d290005131700f005e910742200380071640d0049100d2504c0d01041d07203407201110180c1e90041c00500c81540b031481c0c424a00302c4507a20144c0765482c013260782c0b45105070100c3c0752801c5508000c024170038282c0724108504618204503001304009170400001d045075000750040d000d941401e041003400e00e6920044210340c0b1032400d907056010310000625414039401d44103081340300201813008002d25811650781c0c6c02d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 897322158 1250 897320908 897320927
    0x2101120b0901091502030412170c073002060c03010f050d05100c05270a030b0601050706020d02091e210c1305010e160e011803050a0b0f0115 62
    0x1015041084005a1074070000d4003d1199075521032061443c007078002d90407500035041541c045840320f020560340c9000910403c00000395100da010804040c2d02c84082e000c6040d400746d02d00310380110364980c1c04c9040c10a500c1241055052307840640a403000c1c14030340281041b01c010001100044280018003904010401c0d04054810580304400c003141e41d810a0f500e050841039074680041d041400c80c41e08954814013821a00d004021604405c421000514103200c1015945d42d412803d112410000308010701100740d042481810410b107451120740728542640c0c4484070310840650006146070442c01d240381ca0198590348200c000d41465070350400034840d007045000c90a040024641d00c2159034500740801d4800040c0201502e01c2281034880100181030309110303a8560048403000218003001f841190310814030342c0c1d0f80d510f10841d184001901e0b815090703040c4044c0c1a45601c00072001400400c810420b403402054038400d01d1034090714040022205030004001100c00001310340e000ca4000ea641e0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 897323408 1250 897322158 897322163
    0x20714040c030603150b100219081e07050a0507060c0f06090206220503070b160f031e0216170a0204050604020c0105010b030703110304031b0507030512210112 70
    0x2148003204a1022000703030032150000351440d03c240d0345821502c00e0542c0052001101134454a847d41c0700c0e02000e80c0c880003950442103134640046001000104001c00030600302030510740b20716030b001c1000100c010b02d8200500440d02607210000f44000c0c40820841c042c000c181615082c0081030f420358505524091004000b009591140312410441d5291401e66013161691807000300350841280308682100a544501c0d03019000e2103a0205002d8141c1084940703401020036190f013000d0070b9a45981690482c4102541003000c0c59000c1c40002249000360741d903080c01d0b0f900424100329802ca54048452300b41d40709541d46c200ca010180c1507140041241c02c1044d404550016403030383c4590208010b4403a032503846000e9460b1a002040340003150b0b000d18012842940c00308031101c10340c0540d80c0c03a4030013550050042481141300b0815202100340804200d84036030180d6800a580380e61700791821118480e0180c0d07408020958200032400c004904071125400d800c41c0300c1035494103145100580c0b00d0b6402 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 897324658 1250 897323408 897323411
    0x1006030504050c060a0c03090503060601050412080c1b120c090115031503030302030702060a090c1202010e031501150206010b0a0f0203070c03030c0201030b040c08060118091404060c02071404 84
    0x40c2881801c1c400980f0140e4054802941c0c0c5c22030800041c000400c451044010404100d00850181000030b9602d01c00c0e50184c481710310700b5003010380f000c201949003082107d10070710401a80c900b0784821710400003886550f4814042c904050300070801c03283e00c001e90140c6c0b00d500069503604c05540f107400c0c2c0c0d4111401d048001140070700d01c1504074060010b4000f001004d1140e45000007c01d9415401144502141e40c00e0341d60740c2d00d904980d081900c08603d000340020420f40800e001c00f15103041d031100901c0c0705050075494140d9580c04207003014000606130b146403115070010019000314070070344040c00c241d074030107000c0d0b41d03041003600c2c4150b002d4610074104000301c0501c1074401500030011240f031903410040c1610390743c2e0740c0e280080c982801b10500f01d00107414401909841c2c00d1601985010b034007603456001e050795940004480701880003400884100010b44c0009103440c140c82030010240388402d41c161686014200001901c090000000442d80320500412010601d4000f107540340904440 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 897325908 1250 897324658 897324661
    0x5090d1d03120a0e061602060a170906040201030b040c021b0109170708070b070210081b0f0408240c0903070f0603200f160206040f2c10060305 63
    0x3200040034419629150940710700d08040501d0002500540340a0003da030f148040141d6080c148090350084140b8010403418543c030765401450036201070450816185096041c03a48d0035140c5900074601550900820381048041c001596414000c42000401c151024407031f500c102c5400030354640ca0300621560051031802c850071560300c2841184020100141c0740001c0c00c8011103100c4d2a81220700c1417450780d00c100400001c26610400a4499058004003544101e100741201034456600c010719201c0f40c4003180c4044859031108101400008800c0001d03d62110308180c2a20310f440700b00044403100c019040406002c032800303040d00a40c00f200d02c0417095255400800400d01c3d150060300701d009100e28030040483c03907981c554031030300802802d140901c0c52140280c00d6504a4860808500d4021508010782c0b102c0c842000c1c03a80c2201c03171000c0d00c50352505543d01d142c0e8101300416040680030101d000d107401552200342c6c0004880b80403020b614a01410300076445101c8110031b10446090648400 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 897327158 1250 897325908 897325937
    0x340c02040f180b0114030d0f1817010b030c120316380f0106050a030b0a030c0b04050901080606220f09050c04060807050d06020913020703050405100305090d 69
    0x3082040c036007850204030790040b070340e518200ba10300800340140b103803c5070b500c60900140d140004003280c03180040d071149446040603000c03c86108441080245045c0c403001c1c40080e40004041c05501c0c903060100002500513600340c1054200710f111614144a0580c42108050169001c0116141041c011300e0521301e001c1d6618018030300342800d076207243c11030382c9150b0051114920b4103510901d81642c0d00d0741d141266581c5280701d900ca1000e0085e48001078041c007549032011b01981c412026088014071007800203960340c0d0381c045000c4160300075232103041c80490104418102240b1140c0035020400c060700d01883d181001c03440039485240b50f0300700c4030b01010740c0b490015026402540000d03c1c0c030780103006036200750604507030310541060154015858500c5c00111004081040c80a40300c000702031184003052916413402a4105012499209141c00303201492900d0910013000218400e031030f01622107103090200104200c1f0700c1c1418003414181030410a0007200071404d4004800e807800d05090300030680 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 897328408 1250 897327158 897327161
    0xa020c0c032b181d060301020c0c150f19080606160b07050c0312161704080a210b1314040f1403040602010f050612070303081e340c02040f 61
    0x4004200d00483d0100340424842e18002c81c95a18081074101504503031102c2062600700d110f200384224840e00028001249803408200c1100113070900ea040c103052541004000d0020f500c06000e601d81c10441004028440340c20005250780030004407003490400e101c00c00901c0c4100c14148000740107000c001e0000d0305007405903041c0c0d01c032620310800b100e441d0820206105034041c02501d060036081d07800e2440c01d4480f8030030005030340501c41c541130f58525038441e503450b1500e0ba0840c0b0940300030312451100400200610303002514040b402c460380072506071a80d50905c5103101282c40034036407642c240644075030041c035400906a04960700004011a5080358203040c1c00c548542004541d0a000003d000a2100d50542007060901f01c00c04d0100420303242c84041101041d0030091011082c0c00a03001000440c0c024901c40f40c1c48a008074030800003031204030400903045002c032200c009104504a2250007850340180144040080e44d5400d0350300301c0c80140150810030303071420080c400d40d03d401c0303042d1020009 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 897329658 1250 897328408 897328427
    0x1018171002130b04090c092c0c12041209060503151212030c090f040204050306070c1511030901050703110327010f050103140304270902090a020c0c032b 67
    0x71100142c44e1916100707800d028250108a807000a94403100200708400250b085141c811980340d000701c0c1030061603044000d56000181242c680c0442031103c11065460700c0b2685205501c50322450310075245007100a0500140ca4100d0380c100700051040184d910002c80403140100c000301e51580d29a1001e0380e08902e801c400c1c0c0c045891300d04010041c01000e1031140c001e408403000446a03040404400c5080c00201c1c002c521410b80d141c5c1c001400308480f540185842c4010501400484c0074039080d40c2000019540c2d80c4120800ca00400420408006001c1c41040d420006914003441040810303407a1480d00d00000e000c40d0b04481c08030100c907401421380540600003200000013801114194665440184801d11040d5110310b0b10104803001a0004800c0720b040d10300308440d00e80c6144018002d510907034201d00701c800c481c5594020000141c0c2d58990642d1041031135001c0581d0b07805085150300d00b0b18008600103406940702001010883d007800592007070255031010300010780d105122045171046075 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 897330908 1250 897329658 897329669
    0x803190203180114160303020405040b041a191a0301060807110a0213060f1e08060705030a02070f02041e0b010e15070618080c0d08220201020c101817100213 69
    0x10181700004150b0190040c0040b902d04a40800c0741c04400805e20007524a0f420180d0003000440c241a4060300c2d0a08014802090881141c450315480b50104505503503508400b41540300080010410716512008840d4820003a24146e4908844040416514640140001c0c4640790303000c2c511088030419481040100000e64640485561700d5502192440e056139500554607a00000800c19410014900b03004440d2940e07240d25550300c0580810080d00185021034140a8a180c1030002da52240103a07111101004484102d030303265001c03003008031007144210605000110107000156074031020700051440b848107069584a29038a8007100610f011a040700e4102c1d003548120081c051a000a0160807074001d0484c0c51083c1d5030300c81644d005400701d9110010b0041c5030701202d035501c0c2c0d070740c2c0804220781b042c0111024003a81200282d40340c02000010340004100100c425620705081c860000101460744818042801d60b50f241e588656082e40d440956680000c6e620078a80d00840b0803000621 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 897332158 1250 897330908 897330937
    0x201020913060503150c180301060e090d031413020d0c0e1807082a0a15121d120a0e030607270f120c03020a0803190203180114 56
    0x241c250a6840040c030302c50080710701174030603280e0800c400c0d414684602d001c0c1004441e810305104000400c3c000c50162600701d2038055403111800107104242c2540140600a40c07009001242000e5030002c0464003080211441c13082550180700300002c110f55401030007901602c034600318000c41d05005008042d6540260b0300300301c200e01001461071841044000a0440100b0348130300c2580e64510307640d40c48417600a683c002d08903521504c014442c0491f10030000b0b60103005102c2e07140d50f44051503035071032001c0710020100f164032150015003900e610500925842c0031030a4100c03216803400065641c06c03205000350f00103200007903210f80075015000e070b40d5034400001d04544181c9030908000f403811543c8203022040e520a490100c041c1d040140502c4240d54a4403840000709243c000c445d0300503003211800b034502c10303230040000c1b016894503070010f070140c07002c9801560b1f03c00c00d041d0a2101c00522070b0b40b0700215001484844100b5145011400e06203200b40303001500c140315050310381d134035206034485000c1c00c0c13 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 897333408 1250 897332158 897332179
    0x60b060c0102030601021b03070506071506090e100e03090603130b1303080a0504020904080f0c010e0706110601030305040902070830160503012108120402040501090b03030a080702010209 82
    0x40054004504c100802e070300342c030140854038a4001030303100d4042c03207282d0541100d08d0030b00203030805401038040700740903035a15142084909150412504103400041305145c40c0c00760ba03200260208a041007070401e1170030800503a4881c240081e103a028440d170305840342c04004080b0720140300200e124400c09400001c150041d09040c0c04507410b11006050443c040b505490001d2880891803242c20b1045801408507241c555490355071b440c8640c05032541d519000700078000d4080341c1000344114240003404800511049013040e402030410235481c030380908950b0004005000080c4e10009690072240f00240240e1074030968034100c542400b492401580d00c4402000400880405040d80780d0700d11803040c0c01007900c1d194580c50900b6401c16115060200c0d1080004218901c1030030181c8020002021404102c103a0a42e100000c550040400221241d54041444190720301071140c0c500602d17044800308440c0c404000440d8032401052001d00134010344100040160b4000e4044034800c5a0091034100c40 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 897334658 1250 897333408 897333427
    0xe0f1f0b010903080a0c1106030708040201030c02030c12071505060604120501020f0a05280e09130503031305060f060a12050c09131e03020303060d110604060801090c020c0f0d060b06 80
    0x10300c03120b140c0640d100c0c03661030820401414504201e0740101240c4c0c4e00cbc188160b03125001034002e840d88440307060840c80200062950220140000445041c1040095035207203901d04180e078004140b0003005460320b143c4000d001041e030381c1c1021074045490802c0340d00002d14140c105180280112443c1003040710300051130341011075020b40181500c401c15011224200300c17000c0005107003c00c0d160000d01050324008402000e00c5c200049950220044581e13500310045596250300f141c1003528401320340103c1c0c01c811000c00205101040d4400b51084640005280c548000340075500e4034418410a09040701c2d40c801800310601003241440e901411007401e034200302e030414400368036441040d00d810368410500c400028103400d4142d0360340d0f0154000c5003182c40c0c440070003104030701c9400101d46080000241017580c3e114000580001c0c0b441d61a1080b603589018981d00580720044007450464003c101c0c041c01507035511180024800c000d4900e41c1c42c0c11610b1030020000e01c182050f10794080c90215260b4038 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 897335908 1250 897334658 897334667
    0x70e0403050408160312110d2316120f050a120b0306090c03100504020a170304090c0804030f0c0f03210603120e010503090607030b010509040f0e0f1f0b010903080a 72
    0x11684100298011015888405c59000200d611031011582004500807241440385030403040e8501d00040095145244014270200d40c0d012801ca06624100c1084036400d02482841000c003090580c1440c5003460401500200640300f0390742c4020511202d50030304003900c0101d03030105c002d10001404071100c1b4200001d0003981c4019101ca502c0c0701c2d10401c415111035116a000d594065580900703940c0d0302a04001d484880d5005188070700c00144828400000c0541c424001c0408803c071030380712208241403a00b40107148558081e07c0c4401d1003840320004002a103e0440b02c0da00780d801d40b42103040380c00c1c21711070105c41c800c1d4040d2151a0b141004004000d100300406e01c070300361540540312000e81c00b040c003006440302d0000b11a1200240c12410001700c21902a4220341125601450200e02c3c02c0d41e03400025080300c9280b0321312034805668081085108000b0400e50324102d20b07c9005160080c059080141c041c1203074294908807030b40341c0045012903402145500b0207507a004042d103849110301c160050 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 897337158 1250 897335908 897335953
    0x20912061006020c090c090d0b040609020a0504020a08040f140d031b14120a020d020414030c040e03091210140f06041b0f090e010f0303081503070e0403050408 70
    0x7900040000060854000100300e0780810018006207015a00c0500c2076446800c1003403200d0b08104103100400001300070440e4644a1031080c0c000041c2d45400d40180041c811450300002d00441c41040b48a642c0c2c0c0c0c21012642e032280d0b0100e0514036950051514500080c02268010458498004d00103000c5815070840c0035401d440101e0614100e50802d0225149000056070a06802c810007089210406201728a039000032000c80140c6001849038624040380c0c8076901000801d401e080400c403240c50300b030000d034861f00c1040780c040c0480400514450b440344903015406225401c5c522181c021901c0c280704100480507052030400c400c28107250741e4280c0a10440713103030400b403041c0780c00240e580c42c0c584a002640c07501b4446600e014101108240d4a00c4602e800550070700c0204040014590248402540a0301d80e664910804a02c1c43c580901855409000e59040c481410b2010740d03161000145881281c030707205100c1d21103407542d050a0368688200e404ca4032090054008210840d24084d480f030b03 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 897338408 1250 897337158 897337171
    0x40e0601060f021902060712020106180e010506090f1807030b04030504080d0c031706190f0501030b0612041119030606170f0d05030712060e0f0f090c0108070302091206 74
    0x1c41120020718200d0a603d80003401c001d52008090101c4800b02c1c4230180400442d0000d40000503119031a89404500501c00d44c032010449a00d0360710342450260280034040c0c20004c1034540c44030a0a0140d0150003681c0d00620300c05500303036a80c40701c0d00d0390b98040201900960b005010003c0600b0a8100200305910601511070036115441040d90348074403802c480d120294140d80e038941089406000ca80e940b400140119511084130035156004550304002c1a00038181d5030502c0d1001444c00d4000f5081d00c5405482030300c074040501110261904810081c0c1d8040d40c040e170320003108408580041c00c041f08a031200c4003c01c40d071807004010001d05502450070f0310403644080c24240301003501307a969076000403862034854002c150354207000c500031400b4503003203082424614a8180328491070300898485510903822003e55005200d070a110340c030055500180130060640040c0740c0440141c0d0b44440e140383c07250400000a0001c0c0e01c2520a078107480b26041c004011100f01c0c41199015540e4510071340700c4 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 897339658 1250 897338408 897338413
    0x2210904060e0411060301060507110d0b0901060918050309040b01093602270a181b1e141204060219050405031e1507020a03030c090509010306050402040e0601060f02 73
    0x5a13812450410b003600e048610541d200c6182a80305c2d035440e0500c8180f040c0c2035420009058240000414102516104642c02d4000049a5260850003000e8a15081203031107000807000b0002c002c00e50110845029400036a404110030703050500480d1040c0c5158440d5041c0410b80055600d94842500a00110512840003810b0018840445000ca210346202d0f90f0f11902c840c00135034040c5100d01402d02060720700500c03008409a54945401c180c051382540600c1d401e80c0c8604000301c1d058010002c0303450800da4a444c900c40300410086108004d40100d82d4418010402401c8c803903030710448126001c20510709030345c05541c105403400c0d0300a508003801c0005100c4c054585003605c1841041a0b07422540003d00620503111102140c400c61001c2c0c1511100300c1c081c11049002c80000340310554090021a8020025607441d42001421a00c03101a082c0412024a60400c025551100c03d64192500018000b8658a9a02c0060000c0c122003c545825001d030000000d03d05800005103e90b0583c55000d = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 897340908 1250 897339658 897339683
    0xa0224091e030105190c0302120114010e060c16120807230307080a030b04090b0a0b180405061603060303050306060a05130e06181902070311011e0f0c02210904060e04 73
    0x6c11f90690040740c5007140000c02a500400c1a1405a59031030b0303211006041c040100c2040754040341003688075900301c501c65440804181404040e801c03040c4024444613100b148090741c17a5607030410a22400c180034101214100c00060f00c14481d504040013804a181140d0355000301d03182805481d0009043c2c4004a454841c5c0b031411070030302d070048a4400d544282c10451030b95a01c410780000300081c0280c02e412007854114000c0c004013003c5404e00442c0a00b00034000740c640200f01607080004209807004044c01d25004100194124090f290884022a80b260303d4411a50f000c032500d0145030b18805205030096000100702c90540c0c02c0314000d088c10340b078010b550a403500311107154001c19103004110403490528407003090036550182084c00d10070300d406100c1023102d41c049400d440003528491091181c009051042400e98420016065801e801c140040c0c220920081d46a0035641c07040c1206890100501c01481c44003812103106880050081000701e449a451080d1510110f0b41291028032426 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 897342158 1250 897340908 897340931
    0x140d08010608240402180a0902090406050607200d08130905100b0f07030504050a0303030606083106060f060c060608191b090207050a0224091e03010519 67
    0x3002400300d46a000e21001c203004aa03401d1000079405200c451801d10407190b4904100c2e500c5070031f11801000301c030b170000d81c03280c0e1030340c040000b12400d80e4400c62007030b801049003400003002516107000fa4042c0403031001070209004003148043d0500350f0004d10144001407034840405400106100359810910304101036903c0000401079807660b03000d24070082e0828020504c413210508018440f031032080c5405401c0c181e4810103d806d004d0103400c1207003c00c0c1c444505005166005554580c00214180354039005101202f085446240300c1e065000d0404444d44000244442a007014004005104c07024640340d590340001030102041010444a090a01c0ca00140c02407000035289030101610f40803500765186a96014818908001e01000f02e0440308000a091b840601c041c101d00340c000e1014001e265250b01c10411508001050303100c103404021415040d680511094415500302503802a00540201c10340ca01480704051040760f1641c2894100a599807524045030f440f41c468410500c2000b0060 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 897343408 1250 897342158 897342181
    0xf140a06050912070611091f080a090206041211130e160305030301170a1b38070303060e041a01090506010e01030c050712080612012007140d08010608 66
    0x7080303e200091818040c40c004594039900c030030b0400c56040c070b0f424a011984000324007400d50b401398a07400340300219243c00b6080e80019140d40e1282e82d24804010141e8a80d00007091030042d400761032000e02c141900c080c03c000c59a40c009440301d10080900c1d41c0d0110402d07030007025184a02c0007048a001b0051900e402862540d40402980c0d0300502440c00d603030030460100d24414609201c4000d03032103403d0451011414030400f07040340303200f00c07201d4207003950601503d28030903240c600058074254881301071903036940003454041d030290440c90f8815642c0c07151820210080c00c0190401030012403588240410000ca00360000f40c0c6040810000c02aaaa100407910488904895582c0407034a80201d180c090341c0b0030303442216600721070b05100e405d20143e034680c182d508180300e2544001ca801d0000303010f00307850700c07001518544003410300074130000304040c1a03201070b0140a0000b940c40600400c84108104040400304502441c220880d1034090760003400500a020070310404011894010100d590352500c2d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 897344658 1250 897343408 897343423
    0x1020d0305061305270309041b0c030305060f120303010519140112230403021b0a09050c0f1606060509060f19120c0306060f030b130f140a060509 64
    0x20305a40440100c5a00700002c0c050041070540f42000103114618a1781d12030354928840500b110046d0740710f1030110180400c0300e0114400b010100101509401841e82c0580884400c55040c500420355440b00b201040008012008566011034603405c620180038000001e14100d8400715006030590f110b01c0f0010001500d10b0103142070b01309d14290800b485500070892154078000051000804070454494400030050707141a907031924501c1c0c41880281681003011420101101d01d01500d026075100c00210042032921410200c1d50303e58000985181b100390540b1b008a500d44c0445a4401141c441e05990741015901210054944607000ca01810078418084c07007107001400307030b1803420b142e64100200010a4100140005809034000c101806949940c1580e10310420501e41814294070308103041e038489422041e9182444682000801c45001625130482c0301c10384050710181705414039800c51000500081c1031001c4410000002000c00610881941e015803000c02c140e4896041803501d4040 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 897345908 1250 897344658 897344671
    0x3081908060a0311130c030c09080d09090e0f030301031a2508060f0301060b0403061d03220306060e01090b0a030b0a0b04090b07030207031b080403080a030f050405010b01020d0305 79
    0x160b007414400184607052525030114001c1c071052040e18402402002d69019001c43c200007525214004c10441d0048001c40140c42007401921040480d140002e10103c014428185216140c1000c52900081400400d162f00141e0055039078941c0c49040c00c0201c4a0100d090054000d00400002c03030000210503a0301c606610004035a0300036400f1802110032990142009920200c1d10303101c1006507409104410080c8654a445610b451a5007009411142d1286049620030160080050300c4500442218001402c1a03421400c6500307064400000d4107450b08020403051428001090360200c1603e114100d41440d441403110510110070704c505038031203200c0103000700d4400020800301e5032250403095801030082c20010710705999496840c40309406544400200c1d40c00541007080c15070000d000001001108196180c10099a84040b01072150388000761202d107004c03801c141090300c0f0ba00080107540601b0414002d505150911034000c060310441c0c40d015129680c6041552030203805030324407548 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 897347158 1250 897345908 897345919
    0x100e0306070318082104051b0a080a03050f07080a0c061a011d040b090a05040501060e10030b070306090905150108210904020403020d11010f05090d15150308190806 72
    0x190303648684d00c2d0041201c003000104004951801244001116449140140000c00785044019020315020541242d9580a401201001c1c070044000103202c4021560600d80b085d40d0707122001070017019015042c0c008001c0880024100201a8011208000071340a248104104071000503a001c4898400e02882d02040120003000000540c2c182510581c010140011410910300c8000514105080b903201d0109c65a850a010510101b48100000f415090100074900d041c42456907400040b00e1000821903281c010001e5070440c07098004500500c9025002c0c0b005a0240c500710f0b40f80c408010307000008840d80380000480000000302d221007070001c1c2c824507a000010504001c503c1c3e01070100145c000d5000c02001006840350185044980d0091810720007444021000406144902c10580d04005081c84104070710f641d11000540f04a074400c28035903c0704840301c0320308003070152010317581c142c40b080c10000001d2043d058002e14189001e000304810b100f100500c180c9000005036a23440c2c004 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 897348408 1250 897347158 897347201
    0x30902010e2706060d0e03070b0105030c0603040f0c0f0b0d050f130227010b0d0f06032a050a06050a02010f0e120703030605060d061401080601020d1b02100e03060703 73
    0x180760005000c2e0300158007038451807030041001103030700c01d942184524001e03e0f4000180c2391700780030042500e0b501402044025042c0f41c0050380c0007071490f01000c2c10142c41009200101410404d1074910341000300410bc5900505aa0310b001c01810364002c0c2c0c074400031050810001540e00b10546c0c1c0f82520400308100d202c80e0503280d5030217129409135142031b0024a030019520b5a0a070308116032419009008070403071381d1b0b0385040740303074512040d5106465052007840c10554280000303081d210054000e4903407501c440f1401c10461003102c111088581c40950049440400030843c0c950201c001d141e500510340003400f621401071400c1080349e154403110901c03034011100000d5007031014801081b09501901e4081090b684070b00c002180e991260b048070050560b20041084a00710486610f04004c0d03090030614400d24001703001030340f1121911205020003050810388809031820111030814140c000d07151811a082c000302c09849910a206100c0c801d00c1030301c0000b4100c1d0310900810040c046000c3c1820b094 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 897349658 1250 897348408 897348469
    0xb2b050f1f120326090f010b03070302010c060f0e1006080f0703080f120108030a030b03012903191203240b0a09080a05010506090c180f031c030902010e 67
    0x4410104403c404002c203051340c4480078680aa91180000500c00c0516658202400070500d0300d400d6801c5940130307034149600500d2590b00414040d0840e9020300b0306440418040c500000205002004801d20a18028242c02c038682e000604240b6209001801c002c03083e110840c00d95580c103450710741403da6005000900002c0d01c450054000c5051403a585420070b122816503c1c1c0d411700907040429603500104110740100e50601584001c2e1509a000700109908003d50101c40e001011045204c00088149550740342c0701048401c0380300d03880c44000704040d030315842d0245031040c840042c4030000307040040040308462100041d540c3c940c40da04078500c205262000024683c0c00220b4900b09000300a800003a5400f005c0c0103145d4107030712400000610f49030540812201800c05030022165410900401000d04c103602c031a43c89860b012505402d0180401000038503080382e112070985e8600015a1003948203400d9000703c84202d1007622a1000001d48000b405008000100301303409520001510745c02 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 897350908 1250 897349658 897349679
    0xf2f03010909060e07032411030a090c050d1a0a05010506161b0806100803040f1430010e0115050f030715090f09020406090b2b050f1f 59
    0x2e4410000801e003010507114150074581c00da40107407601c01c0c0078155481003400c920b61041603a1011481000500011448201307180002000c02c0b0815a440c0b82074005d00101d005070030020b04009001031042c407002e2800c90980080100003e0000070341101040b600300c4540504c50586401400f510b09080c10700e00a91241d100522003503c2d0b1030014029468420280d401483c050120780c001409070341852500000100456070102c501508244000d014030380b401e80c1c080c412100011400001c8003080000916072034a80401748403050310107290046001c91900c184102e680c602402000f0782d003408043c1c02d007130f01c140c00564082c9001c1d2000a204074600305400524000e405800c40d5192600c030781c002801610000150404112f44c214100b000700ea41241071700240c101900c0a508191400c98090103400041c003031107941890100301081d5803034070101a840d1038aa42a004803403010050706d04130080200f980c004444490800000301100c1c42c24180450780580700b003800c1c034224540401d541 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 897352158 1250 897350908 897350921
    0x1031109010f14090d1a06030a080901050c03131706010e04021c150c020105010801060b3903041404050c0c07140d08031e0609090601150c060f2f030109 67
    0x86088080c00b1001d1642c441e240f940160703606c5000300816071548003014010403d0003c0505100c1c0e0b000605003000222088181c880d8598282044e50316540d0150803c0d00f1401103041981a52a2039440004c81074480b081103010079401a0596601d66211500d91140501c03c5401941050900c46102e41503652480ea01c0540e5008941c01e00c00c1080c005610b20590303600c0604000180e44410041c48050f00030b03c034105c02030508041b501d151005440c1c40700c1e40700300100300c00248600c07400c450740010a80307045420448003101c01aa56196100c0280c601d000c4a4038500c90b000f141703040002221000803008603488000e4a000030200d940c6800f0742c41c40d1894119000e1a0850070790441800098620006103001d400306080810440f072800c240c015140d20700034600341c4245200d600317000c00c50300042000c60556004003905a118071481c5810340c0c81100001000744002e14040076038920031405d034003010b0916000c190000c7d5100d01c991943c0b4000340c00c043d5078004c81a0400c010046580c996021070b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 897353408 1250 897352158 897352187
    0xd08010b07030c1e052e0504050708061006020d03060501020309120c040920030309090711030f0a030e071e1e080f0f0c0901030f020f010c050105130201031109010f 72
    0x81c2d0301d512050740d4100d050a81202000c00b0f0b605074480b131204020060014400460220020619242806071404a00703859014061038043d6284042030900c030041c00f001c00a0300c0c02e401103654a0400901070301a42480303204080040c0180d10901d19914441c0c05903000300c480580c011820300e1018000c00181c0010038a04008500c16403002c5141521180a5840f600c1d00a02081da1022510303916610300d4002c00c500f03c0d1180e0010090049103039940c0c400a600580b140c0b900d2590806081181891803144004010380041f020a600b0241681604801c110034007440540d054282e0f00c4450104040e0001000e00702800f0119043c401c40a80b10700701018480c0d090400f1001035603c032021403e0046c1c503042400c03150080181c4c0e06503894100002440060700b40c42c009641d43c91a124200c6101036144024400c280c402c002c980e5680c0326010b050343c002c0e000b40082165007003128010000e44810b4500724042400c0242d10707008a52a0301c15502c03513484c1038440c04804035940304212f44ca0100c45040 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 897354658 1250 897353408 897353417
    0x30109021c1e1505012007081614180c090d0f0b0f100e010909020d060501061d0303070b010905191b080606090a170304090515040507020d08010b0703 66
    0x801403a04450040c4125503a0810760303112400000445241950010980b030b440450f40e0800c10040d07a46e0004510780d18209586088103000b101c4051130f8140b0095503c0218188101c01800300002c10f02c3c0301003402c480026083c51800c203652014004a0280f00f01819005042d000005541c082c110006003104000107100909022030381e40c9160719141c00000982e00c2800803420041d0303511141c044142c2021070100e40014040c940110042c0d80314050080c1014682c030381e0900341c1151125945204642e40c0304402b4012507031030784801003008011800610a01d44802c50000c494180402183d07035654010340c0c5480030307038200b1060380d018220113020403810440c1d00300c03004051055842840e05d040d0003d0382100f00d561485034028144280500110b04ca40000c10040c1d2040c4d0b107600c0c22804a5040008079071000d6004072140b401d5000f1980001c02580c207000c1005980b2a550f20035420020086504000580702e00100700d81d51110400c0c65008601d030b01005100c05505400a042e001e80309240 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 897355908 1250 897354658 897354697
    0xd03050105042304033e010c0206011202010302181810170a0b07020708070b13050a150e0f042d0204030507060809030d140a240e0a0e0604030804150b0603010902 71
    0x840800d600c04510303074400c40001b030b01500c1400c0d0b0a00601440d28042c0c03004013001c0d4144804044400c443c0c2d00000d040c141c2c0010740240c1c1e401107984801000c1d200034400c1014036074030b0420802e010405c41d0b0f18071003c4144140440c4410100b900310783c6240c00395008180f08071072980c510080400c00340042c8107501c00e40000148648081100401401042c045161145003140c18200d41d8400e81d0000761054011180070300c9841040301407001c04208070302e40403901e14810b00215480030002049690402d084c00c448100900781c100b440980303d0341c066a4551440e8003880c00d10105d0089000c001c0154001d40401c10005104010083d040380005044e00c0c9409001181c04046400d242c2c40300300304005103000c11220207018440c0c07442a20b41c2c0030380c1400c44010f0500344001c041641c0150700481c1c04041c08608060300781c1c1d012409041c100300840702d113420301c5e040180c0b120204850840e0442e20322800711b46c0c1c1480750b0080f07094104016042c54110307402c1603c00790181d080003d00c1c00c5550003051 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 897357158 1250 897355908 897355967
    0xb0405030921010506011e0e0f120a02150325050909010e010302180103051002070c05040c02010605090108030c070608070509180711061510020a050d0305010504230403 74
    0x102d072100142c40350030700300e10a2950002154203440d402030170f450500079010801d855440480f10010121482860302030711483e483c5002500c0040c0990301c10b40c110400344030b4031111400008071701c21114003c40307801200010002a08160b0b1000311000c088c41d00030340303401c51102410040121404e85407818424107140c0001b02003030315054243e22110612040c80f0040066081c154442040d40e100c54851007815030441d16421780d68480c2d001810304041d40060320303100380300800b80c0c0344001d0500140280948108107100078040c2c01d16001d000d03c11080200002a0b138a0000122140c2c074a040340900541d51400c6003d840a200040104040c018104504100c5548038981c5905804c50702c05244521306145c04c0c01095040d001014010320b1740240c0c284101c0c000300c3ca89880e000724003210f80501e00c00352480220304210760008010018492600c0c2810703850380641260381a42d100380c8003001115200301d180450011f0104080d2600d004082c049000720703201c1c034296106d60b1040c1c41601200d05080 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 897358408 1250 897357158 897357169
    0x4050906031515100305070206010e070905060d0209010906050a091a040510110d020c150c25091a0915031c0513080a1a040c0b0a0210050f0c070b04050309 68
    0x464642c0400b40d060310f1000035514083d00c43c010754000610301002145844040659101e1f018007460040d04034080029412a03c1080c0daa8090030000d05400e884d9954401d00001941161060341d000c03401c01c26011035058072850581c2c124162607030f00c032071406240401c94519110351004841e0032400c100000b041c15221114a110000c03a0703076640001071108c0401031030510350800200300454100c0301c114009503079800362041082d4505030038641c1e1146042441d51078016005842d081807078440c0025401da02c2803281882c1207644400c410b0042050b101d4810a4600d001c940080d80400c08602150740380303001503918014810044c0c100e80e9040c1c400703046620700341402c0203c8000140000f0700e401c2400c4440325181d0040400b0740081040c01000d5661100c41100250b5040400480c0800070b030a0100905c0c90324000c001c24080a80c0e40c1001c1c0740d00070b407249010703210341c982075007000302103407141d0f07140c80d4a6449030014412460405105540e41c100c0600040c2056505102c1881514200d980b413 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 897359658 1250 897358408 897358411
    0x70f03020a0216080f1018032f0a0b0f010303090b090307050a082802010504060503090109060c05190906050904020706090203060a050907090c0c03080702010e061602150c040509060315 81
    0x40300040c10b0b0389880c4041705280c465200311091038a410442601c116924140580e414240e05007000c4510020740b0842010024401c54500f03038503e081074240e56041000b19505003003600034090071516a54112a507030484100f0300c4000c0004800340c5003000b2403181c04001d801c18240090a46000581d07a41c0002c00c184016046410740c0d800100c4035070138001107a46070000071382c0f40011501e83c6800742d80010340640a68401c54040c000008005540004290300080003154004001c100811649400030141e4220080145001c58104415010140603807020412550156641c502e408004024800a0340100204507040b645030049000160f03020310010b44200e000c030b5030024040c83c00400c180e283c6078aa90000b1012490003007480e1001c2d44c003016401a01d5018106159540c0f1a810704a00401d4411503030082c600590702440f041c00794410a22420840740c0c0c1c21600c810308240031070007005000ba103141c95002e130304110410581c00d01244aa600034002003d840320800c3c5040043c0b51200c0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 897360908 1250 897359658 897359669
    0x50d140d080703060518130201050c010603061d03090a0b0c0f0303090d0207052b110306130309091104170c0607120305070c1505060301020d180515070f03020a0216 72
    0x150700410008550500c903410084c041200c0d0310030981d506040d440580c0201038085e00151380800340800c21759005030100e40448542078020012660b0320300305203008000c007284100148641d80da403000e801100000b6202d2590006048051b41c0c3c0ca4149004116842200240f10901814080703482c40201440694030544009000c0c100419040000a0501d0169004648901c140041c09003100e61040346642d448100400c000120b02c2d500d08105514001c01d20000358540300300f0041010101c02d441d81c1d5a45644661240d00c64207807a20040d00a60b41c0040700c03203500e00001d01c400c00002c10081e580c5500e500e80481903801d0121303544041100c40c2e0103400141c42c030315100c4d40100b8101c0c2d81480340c20b47c020084c0c58010806041e990355081c007240c2420030705124030307140d03c082081aa02941250a205d5041804004240d080b0b010802ca180c1148000d549900030100ca42c2950305512102a11440d016a1900381421602c5400d42c02500030002c198214401c925100401124000c0102c01812 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 897362158 1250 897360908 897360917
    0x801060503061602070618030f0f0201120b0312071e081b120313060e010518060105150a0810051507140a0519050a02060d021213020307050d140d 64
    0x50400d818145050006082c00001d6101d2104020200360701140a00c05e44040d4a80740950542d2590110110080358001601282d608403415013009802044009414402e888180b0f185242080c400100c0d01c8041e003503500740c1c1010803010b90180030000201000ca10130344200200a9903402201652703443c00c40c08031103e0b100020007806100402081641e416075070001401141600a40c0480ca404003400e5401000e4142c0251000c00401d60010f2518101c004000c00ca145081c00301c5130b58540c040224000070b40941c90001c42c0c1c1d8101203a04915450141e00e10a1503d411490220f4aa450080c50200c1c170101a400200e03507652240c080c40c80b48184c50700c040c1c1d2039100d5030a00d800291050140382259520a0855000080c0045907034050381d50030001da40c1071884d950501a0030042d680500940c4030700001842d2403451120b41c041c11391904810302611842c0d642001c0101000100e01c00a0760580c80b0120030440c501d800d0026031080f81c890010790712030700525500b00d8a050391428002c00402c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 897363408 1250 897362158 897362171
    0x30d0e0d26031f03020a0b0f1b0706030e12121906120b130c03020103200c0a061104120b1003140607180302180c0c03070311010f050405030909040302160801 69
    0x9001c1402c0303101802c080e07003088803e462440d800569102c250b8803804005180209845d03002c0d018020699070a40b000c0c4580003214500c0c05003031900d54659000d0040821b19018004524880004409000018000300a0300d801e101e03c000018048004021024400c00030030b078a1940e04a070700034640200110725591b81154690319041e10515002810001000101d404140102c0c0c244018402101e4080c03c000031030702d0703032600f164014041c60f5480003a0583c00003805402c00e400007480d42400b80c040e0b82c1c02c01428680000411892180d4070030380c3d200c2210501c40c50007060b601502076030410440d003c010b804a680f541da8402c10803540c02ca44900340c0204080109075078010509283c6032081e80c00c0d003202c06046600003940100d540c11340610492002c0c0004075050101c0e0100c03100c000350b00d000c4131384880c5c1900c1c00402c0071441c00c3d2105251350821518841008050003554001e41d40080a58141100c80d0107001c0c0c1c07400001c005408610400042101191180e03078480c010348811000420704 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 897364658 1250 897363408 897363421
    0xd020a0b13020607020d080409091b090e031905090d03050d0e030a0c060f060308040e0414062404060504021605211b150106110c030d0e0d2603 63
    0x103001000341140600c07041c0110280059960104540c0e146504a5182a20400f00e062032070550042d9080165840d141010442c00e008a0700c51400c0c1e0400c0061500c82195240d1404d20309a8007503445d641140c4c1d005006002e10540074000d01c45402c1450719007181008514400926240907400c8203070b0101d03c001070b001c1400c007124040d0740300c01e4529030025450518a1100105148c414200c081c100701c0c0e5030204d01c4540006038016400860b0056046a00c0320f80702d03c2c902204070300139202100d484154882c2c101080c070020911074403404e80f00c0301405611588008200c806405203840a03070091390b500f00487c080c0d0341e038400b51103c83c00204c49181c00e02c1051811034501240e9904d1400280c14021030550742c81c4600d821284e6444014038035840d00c40c04000c1d441c4c80c204840c403805501c402144004210580d0011030404860344900896150590300b00070b00d42c8074403586610a00140a25503020740c14142669615603e034880c0840310495210700e400c14002d41c40721020020030031400070a2054 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 897365908 1250 897364658 897364673
    0x70c0c2c09070902090604090606020c0909010e06070f02011b0e0a09020f04120201090e160f050c120f0412050706030506061206010c1505090604021017270d020a 71
    0x803688403820356242401d01082559403003555201d880b2425800050303403486603c4440696005100c1d241d07003402801d498200103911505c0700440640620b6070000018406401402101000b0ba101e801400031502d0f14001211404141c40320300c003c0d5900c2e074208200720403510b18441185a02a03807201c012050b08400c002e020074966200541003030043c80300b20001c2054100b190201c40052140390a008464401a40c09044940c40343e80c0d821807141c102302c0408080c1c0600c02050000c0d54070f0b0580c07907a01101c169480c0c060340d00441200e9008401064015528000900b1f021b007031a03441d0343c101a900d640c03010360100d00c0300040700c95801c904820031040b50903006140e0481d01c2165400d0500040540001c284c08000f071501e4100300b0082c0a440030f0259500784500c100307001d50401e004602d4000c1c012039541500740d070b00300d00842411002d500580e00c41c2a6400d0a0400d81c0c14030601511011010b010000d605440c0d240c0c01081d00c1720340c07081c0e200c003040000103026094005d00800a030324101500d = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 897367158 1250 897365908 897365969
    0x12090e0f0f0c0a1209020117010f094205030a05070305010c020102030c0a1b14010903080f13021203040e0403080118110d05100801150e090c0102060f070c0c 69
    0xb03080801c2800300b08500ca4000d40c20f6140504046070005007102d142c00122000420360340c000e90300410a031300204000070401903c4050300d0b100d81d81844080c10500300000100c00e951780071394500f0702e080181042007181c448102049103846058281c0940c131400042e040010404040310542c2c09680c04004101c001c6c065100100558002141549040020600c451103800e00e00020030a8010300512070a203d03090a02c0d602e0703000b07110184980314802455000308010107058002c81c4851000540002c002e0491038418240c03c02c100300400b8083d800d0141505280d880c061190206000100c4d201400140e185d1145009944810280d45004c1d001542c2d040d40094900c0d600d1b007071100c01031018408204941a20b0b40c105000211691490b461800c10102900405203a5003031080301e0f07042c0020896000203a0380100215001a10340309a5280d8402c0304118460241c0c0144000884081c110801c165100c00a8203000d500001c540e584c441045c81140c000c0000051a00d80c4030750b0502200d015034 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 897368408 1250 897367158 897367171
    0x90b0c09120c0306061519030f0e010c1b03021903050a090f0e16030f1118010e0306070507021507061b050c0c0906010512010f091103070c12090e0f0f 66
    0x70940000c02c100400d072140d4004202c18001e004208980808402120450344c0c032000d04a08031205c9041890300a014246400c1110045030400c1d068640c540c6040c03090f0940000640c070342ca0134480d406800c0200010100700140c00b54010039074441d605070002d082a0301550311076583c29640f01d054560190082c41582c10103183d40701700701c03420b116541e40d20103901c0e000541d0643d0340170014a86401100a002040b80c1d81596038144823503041c00f003481c100607103031400a150480840030b0000004440103c20020505d900d03900410200c0e070711901079401000b415001401580d01382e075031180140000c0d405108100d80c03a50360340c0c510041007080da05100894800318030b0101c0c5000c2e1410941d5650f01007008225200b1090300010074500e030301032001c0341d0100c20b42c0c4074240019a990340344d004030070b10244101d840c0c0ca0b081080703490110780729800f140e1184030b01d40c42d14030100c1d2003915055200000d00c0c0001080c002c030985c0c0492801d1007103a0b03c510410a40d41d941e1050300e00b080d03c0042125015180 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 897369658 1250 897368408 897368413
    0x140f1204141b060d061809060501090b1f2f150402010c030806031f14180712020109090509010b1201021905030c04090e0601140307060c080904090b0c0912 68
    0x140c0e040588070b40c981d0002c01c640b52038075440c1400e0034000034000e561042c8507008150701c0a0400010307035040796010070301070281081642c1c0d0710004402074401d1035143c03561020390303200d0000d407503482c920400d03039803503158501380e841c284903144010000c02502d0b540d43da09143d0500101d40501c420402800d40311904c080e182c01600b001e50002c0c151b002041401001d10100a0000b10292001c1100007000000700c0291700100020200443c02130410304111151f002d903d200144540f44004131480c40e03195140001d08516140c0711003009291510a012070401900e020006405429030264a002e5186640002803000c100000c003c5079429044902c2066401032204030410209603034208280d518078145155030380d403074072a40280c912030780d004440e1991130301c03006803001c0c000001c605060303400380549100317000c8000c0205940d0307003158030441d800246480700400008196401074496164060408903140c003003565451400703e8129644a01e02d0408100f0800e60300c0d00d00c40703989840e0b006002 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 897370908 1250 897369658 897369673
    0xa06050c0d14070f02131503030905180115121d160b0f070311070e060307080307050303011401120f020a0e401113080f0706140f120414 60
    0x100001076024091000d020100c1100c0007400f50f46400d40d00d20440c0f00c00d40001c00c2007182001f00d104210321640000d07000151908004125410f0440304005000d495140b0501c4980c41c0c01d030344d440002090860101007210040f541c250740b2021f405601c4e5440c1d0100e94541c81203480480d80340ca0801070500040000801e080200509100801103691001c5000702c003656800c580d0506407271000c241c890014a81c460b2a100041088071024000d0050380d088003940e00e150354880b1026540e0050070800b0300703d070304104010008405c400c030315080740d00c3d0181010b0080c0140c4030000c40486461106150400b42c00180350900c00d980071180140000f4104c5d507041c1c0440c1c5590326140b04a440341000b0440185070700342685d0156114400721784c034000210042c0074054080d680c61219410a5150f00400c0c0e20b10300d00130a4002c00072404003c41c80641c0f0080180b1450b0480c22180d8800c841411941c255040002400c0d034140300b0010b01c5042d054003000180b40c205450700450704104100350100a420092 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 897372158 1250 897370908 897370937
    0x3304120e0102030a1403070201060e010f0608011d07030b0f03030310090c031a1e0603150102011112040f080d020a031505192c07020f0d0f02030a080907050a06050c0d 73
    0x108103040d00002140d4072500c6e035a98600a90041205810211814188000000300f106110202c0d030191a055580c103826642e07540c3e00d030560b03049440812402881144001800144a03a2000780382040082800725015564000320782954010b4411800c4049442c0301403007044100c0c003544003000058602044203062101b070041200e00000b180910a0a00111540241e05006407910540c000203000c40c1d900c0c100f00c90800c802c51007180d800e50265007003030240b41c4058000303000d68140e07840b0a011b48160390b459584100c802c204051049991103014050b080c2140300e1031001c0c0c24407903040c3d00c0c00100d030300e024082511071100d6070340302610840185080c10300010159003030300110396404000b03050240599000c1198002514510303c1072444070001c2145440e4005008085031400109682130804078042c102d4141b9202140302c805030b401088501c500e18030030960994040c4444050b40c03212a00c89000550104055001c200011004651101503410030b10403030005103c9414400881e002e202d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 897373408 1250 897372158 897372167
    0x9011b02030c10021303080a08041506030b0a18080313023d051611040e0d0519030e010501080309031c0804020f0d1212110702033304120e0102030a 65
    0x3c0e00724152a60700402d000c0000c2500b104414041c0d5400313000d45444585083c4000c1c00840e04036010b54140321020000e4203446150b01c5800181c07030b0800c03584441c075a10301e520071000d0862048007040d09411214040c01003141040a1405905881360f1122060210300406c461700c0c10102d0344240d13500488100348080490400c07490400084960400324164026200b602d0030b004426800035100c032038460395010484200105600a8001c58040000340558804155650b10303401e0f521000c108200b2a501e03420421216481c03094400317150114402d8981d010050075030303400384d122010303d038001300704400d180c9410b010200d4084c103441003001e00194801310061001101810180c0140110403803010b95440340000480100d4100f000e101c140310902c1c10040080405080480c24245058840c0e01040300305811240c805400030000c208100c130005003540c25140801001e03c1d80e10007005900c2e040030780424440e101ea406a401d99900780c04c495009003004840020443c1150805c00038216500c5c0c20 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 897374658 1250 897373408 897373423
    0xf020c0604020120060403030204050406091505040f1815110309060610050f19020c0f0d02040e16030b0703050609190c0e030a0f02030c0406270609020309011b02030c 73
    0x240380113907140183c0720740e901d54450040340310080ca00510042005054158000300121001135808005d155502c040d640c04844100002d60b085a143d10810001d038501074020f2444201d8003480000c1c100c030700140c0a104d14014007270460310080b4648826146041074411030b07082240c4000c0031443d519082c4401512500002d04e498030400c20700040e40c0485225030103480754141c951603802d540e0513031241c0f00100b219810b95524014811544040c4180c1041ca0002041c000050038014003903030240d082102601068480c0412446201c000c1d00c0d01222040212000310700411000c03416051810000702500c600034052030040091809104140c1040c42800600401c10030000882c94a510380464050008603c440e62500c03484440d00d007400080c580d50b01d0b020744224101c0304241021422701c400c0d038189200ba1a5042c127031610201414400324400402010500c1002880c1c9031106249001c90700180c8a03050240e664820461055580480300c0d20f8491590004500f40740c6443d203030a546100c2d = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 897375908 1250 897374658 897374663
    0x406141014070602040e1f0b1204060209061306030f090807140a02030d020708061605071403090301181103010501032a0b07030f08010b0a090902160212100f020c0604 73
    0xc0000200c0740c0079401e0140c68600d580a0400d668840e6243c1100f00340700d000390740d2000001c2c0c001041307101c1c49070941c01403021241d0341c0c824241448904022400108030081c81650050340802403a005c0ea540c0303000500d0f2003840c40410440050510000078202d884221030b05d58000e240100746808190908180c403400b546c0101200840c4e0b483c0c00200d8240038034210000d40512900c804072042c0d6401048100a035200c071b508560550341c4044044150118044100b008288204109800b0900011007240f12500703240449180034910710219003103840c0403078000e42d41c07041c03103c44108020354a90400c14505044009003c9541103480b040c80c460f10b40104424841c1d82150303008c26010070a80d000c0010489884407645803805800e02038400b00202220741700103041d08001140d2441d00300c054a10705440c5a41e084070301410a58100000d502c03840340740c004940400c13020b20050b40d4005920030919412009070040045008c24a03054448104200410f031f070050103110344040300080d40700e6000d074 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 897377158 1250 897375908 897375917
    0x1a0a020c1315080c1509090f060a082d010506090601030506030f0118020901290d0f0c02100509070303050319110d090b10060519200c04061410 63
    0x50300008400800344040510b41d004640540015446004500040d801d070065541040300c0072034548901840c881c10130950744c0880b48401044050001100850340250098104906030b51285800d510305480b04a00c004010001c010400c00c40c10b01407d11412004050001d110505110380000d002c112b00030242410035669030f0001c0ca09680420090b0380c800504e4008010042c0401104882000c680900340c0c018214000000303201c0560301c4200c4640003808182c0d003020f880c00158001143d0100c84c20f10b079030b65100c80541c034100300c01d40324a0340c4080390b0760003d0bca03041d040703040c0005440d0020004111034100380f81c20808290004100c079070024951605030050100f5644080090160854024420002045844140d445079100030207043c080d404401c1c150344c3e000d1300d044034401c1a00890340000c60520550807907154101c600c001617021070502c98410056030303441c600c40d01180341c00300c0c00d0369018240503210341c10309200d40000f81402c0c4c44440b55400c540c0c40800e03a10500d8081e07210420 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 897378408 1250 897377158 897377179
    0x20a240c02210703140d080c07111f12050919060608060c120609160806010c050303091b04090f030f0201180602070b0a09050705010e06070605101a0a020c 68
    0x1960390302100740c0b054500580101201d03904598881d598842d03030208642c41c0000e08809040c5850026032400035403915a50003e2645d03621301e05103102c0d0421182101c140ca40d01d141040d8903942d00c230420030088900d1072000c3d041460043c0040c404030a0041958010b0318050a00092690100b04040c165002c0c80030000302c0c90b030700c0c81c1c020000c045039407140e1000e003d1001840450103c2c04000c01245040182000d01620b9510030040d040006481e0311040e603024a402c01d42c0c0c24051002c0d0780c0c0c044e4050414002c00d9a041d00c5060450b8801c803402c10f41604410540f80d0f2441005010303009400d020380e8100035529050780d40700846403845c0e001a003805007a0503003e090a2003500540c2c019210000303444404e10252810138060741000e0411524418040c00103000c800d8030b40300d43c0c840c16800030028155a8607003001501c000b62010102d81d00b0074001c02c40c1d14040b03007950041d5070281540c1501e034490240b9003034a00710040080703000100c0c01c02c4c0800c5101040c1d98001820807031400101d40b4085034 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 897379658 1250 897378408 897378413
    0x17070305070c0e010f08160509190908030610140702060f0d02210702010209010806060f0c0f0601031b0303020a060c03020706090c03030e04110d09020427020a240c 72
    0xa9000c1d581000700104246040442c3d03500c5502c803450b04a410102d02c18503c80e40383c00c42c5507191072090b4490461007090f40401c110525224002d2600103d14240889410b840c841000702583d446800503100f4800010602c180d42c01c0500271040b00c1d000c3c80c0703407551101581c0805008a885001c41c003a20070100440c01d19494030f0410101c070007183c00314004642d1a44e5050b140405540740c1800b03070b010080c43c000003952250060007100e41c0b0140c165a0048180d0382e2000f0069a034101e04022843c002c400d01c41105a50300030041d102d80807620100600066143d480d0490382003401c1e01501e0b900018440c0d040000940010b4a03142c071503800030b0b011451001d6818210001c2c05001c030302800180c10440072509001184580c1c000340c0340240c0c0e031044640b0140c0c1c14032041e01d625010f02d11a00c00c04000e11803040d9025408880300d03901c014400b24820760b40120440079504102604005220404980c0b030442c50280c1007003006180b8008040a04030203203042d80c0328103070300880c5c590900070700080c030008 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 897380908 1250 897379658 897379667
    0xc14240307110f06070210020909040303270c0302030708030406020a08090d0b160f1d130b09011d010603140402010807090302151e090d0813030803010b03070f0903170703 75
    0x1466500008483c80c02d00010030482ea80d69068410001601446c089811106802d008542e6449405840281d0302c0c0c4540d07408030000c184260600100303000620301e4502d4072012800b07030282d140c020300780814640c2c1180105810503080364010300c2140d00401040250310303008207441d8481a000300d802601e582c1090041004a000000d0003000c4103912401c02c81075403040030b43c59101864903510694107444181054500400004001c003a442d0740c02d404200e54940030182071050341d0032401c00f140340c5500d000400c084120a80107150b01e80400103258a401c140e05100d2401000700c0e25084c000603000401d41d034249400070340043d040110400020341c255016a600034021a4003403d0781000300c0b02e00c08014281d4201c104a1404109401252410b48031020b0554003003103c01411044111019981c00c03074903a01080749251512036110300000460843e0001d94024961841c0c0b0590724900400010882210112540d091001001c014030109100e4603440c039007255882c100355916070321401c045e078 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 897382158 1250 897380908 897380927
    0x9090103080d06051f0305060f0307090207060b090a3c05070e031203090f0a08041514040305030a0f110a020402030606070b1021030e060306010306050d0c14240307 72
    0x19000071000c84a40c0200c110200e0b021174048060b60200042e45400c005c02c018208031151071a070640c0082c0303081c031400900d0360040c450203114140015a2000302400301c0d50b0138108640c0a543d590791013030030001c0c00404030f0b500800d80a03e031907422a07a40c107541c401c1c44156040c1c07070920100c560301c00000303143c40d02942c401342400f28024100d4030722400725070040035903078011601002e183c00b503640c0609101200084400a01e82d0101c507150520b420700c1454040c40c001d14203100c04104085051070700f4041920014400f450043c4003035641c4214200d006803240390000f00765400c0001d03066000d61840e60110340d54420660403500582da0351207400026141d03000d03800018004068000c20b101c01014040c400108a40ea205202513150134240401602c0d407404039009004901100c18030703209450300c07000942d44545c050400050007a1501d002c180c10682c840760460308441840800d011000001150011240313045610004071040d86101070b50b41041c00500780172281011001c01c420b10701524662 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 897383408 1250 897382158 897382169
    0x40911030705220e13110301020403020607151103040b01090b0108040510092d0c0602031606050606040b03161206210c170d0f18050108040203010f0c020c1509090103080d06 76
    0xc541410a0099401805d40c1c07050110381d5480b000c2c4803006541070600903a001ca90300104610300302242602e5540e5000d60010f00030036400e50701c140d0f400304040e04030091402640504140c0c1020741c100900d550485400000843c1841803180800000a00004074100d0f20210300d42d0219022403c0c2c9880c2344e6a01070345003100b03d201c02c3c00044041f82e2070301e040c0b1540e9042c05041d0700f0b0070295031040d00766140d10410000b00b0203948001c0e095804200d80d07410140c1c1121026110518003595454000f84540003078458080310103036002d880c10507660160548814040c1e06400b0403c1e07038a0604042d0219a1420b2005548040d03070000a06000d45002860000c00900e9075520f0380c802c12020050700c0d062101c0042c4c003c0344031000050042da03c03480744680300101c0d4070b503141169401c00700191055000100126855900c400780c40c00340c181d0601605d4000741c10790f002050204076910400c40002e0682200329407a031800e00410295943c0d5010203811a038111004550790b00000b8184005040e1603001b1307 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 897384658 1250 897383408 897383429
    0x7030906270c0e04030e0d0c090c030b0f1f121508010c0f0c3c23061015050403080c06060a09090302120a02030d1104091103070522 58
    0x2980240440c8111021901c0d110300c00031016640c98485075030410109580240001e0a4240540360038108002110702c0c0c54000c25500d0041c5a0717400e60b087c00c1c2d4004040e1034001903100d696030700071400c24511484c21504111f902040c108030b00341910b404940410b08000812203021a20b05c442000d41c0c0c0407010300c0c3c55180099484d1621403ea0a02a1141d03101040010700c95102030f4240d903204100200805610084600c7e02e210b5005099680c01c031960900307000c00c00703440011201d0000c0e103031810108510402043d00d5102030011066000c1c641c40440350800d03040300b42000110b000710903560065420005008090203d9542e0031a42c03030050b138200500101d000580801c1c1404006000b0348142c0085810320000c60f100c3c070307403d8150362440d03e0040241c1d01c800c0020b089420842c024010f034001c1441201d04243c40f01050405032048042c02d10101400050b040c03101c07a14a00900e22500c3d00040254910704101c80024800e00c962044242e200c25520580710786c580a0f44000802840c07180350 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 897385908 1250 897384658 897384701
    0x903081f080303240109080d0509060d0f0b0108090102250305131e0909020105160618060e0616020d08060307180507020c030c10030b040b040c0f1d060307030906 71
    0x2c0b68081c04040d08000e22621354550f12141984110544401d82c1c80382405483c031183d40500c01e840b80c0d08080b0210340c1c881010700400c10091807604c240c4151561010300451090074100024000d2140680000c1c51a40100f02040880d003104018914102070085803441841c41414119810701400c1d10b03441007a108900300140b00804204030f507a0100c1481d0304907484503a074148020440c0e0410710300a010890030b07c066000040a040400f000c94050180460030005200c6c844c2c1c002104072004982141d6250b40c003190202c0704104290380b11444108005600800003030117583c0346a94450f40041110010003c1c00984080c070018000b40754281101c0d010020800b084400b07001d04855840c01445070b000d96421070f150020b0710018091002d0100301c211200c0e200100c02801c80c050324950001e49a1107042c2c040d031a94810124500001ea689040401c0d0141c0018012900c100d070700720340c148080c40000030b50b0303a4000807030760400700500300000e881d034091074400c0c050a602404581486003802 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 897387158 1250 897385908 897385921
    0x30d050a05061e12031b120313030e010207030210051e0424030923100606050a0c051e1f0c02030315031504080a0306061b0f08130f090f0903081f080303 67
    0x41c0721414031006c2d4410360b02d0085035070009500c1400111407901d021480b120f807500c00b090056050076040b03401071041e6a06191641c002c2800710b00c028185000051000030f8114107080c00c00341c2c0240c5c1c0e40310b5020040c42c1c82c0c9000f00b1510001203a075081501c2082549072842c845010342e00c001c1c01240d104862015401d0040e00b00b000030550580246054091560400000801445400180c07941ca0f21944d080c000084001c4078140d00c0f03003000b242c40344602002000e801d02803040c04002d00000c44024088000a8020301180c030600501400e14035007030407c2d00d03600c250003005995011220295204040f030703ca00000c0d10313207980c0e04000d94905105806000501c140b90004080032080354405000f4940d896404540850112621000c45403109052000003141c1c3d00c0f00711102070198400b9420806005d580c0e0003c60041d80c402180001c0000040000c59101d01a03641e0f144049402003000c0c1d039580c1c071b018010340c00040288919120381c03c0c0c040500e80c0c08a03103000140030010120382d12454091b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 897388408 1250 897387158 897387187
    0x6031003320c09090d082205120d06080307051203040c0312020a1205070f0b040807150906150b031513020c0a152f041205030d050a05061e1203 63
    0x2140c1401055400c0c005640940000381c6074994508a0707640300c2a84d1f5409040e40700129110f4105500f20140c000c564010990812098100c008030b4a0015a120440881c1c07208039010303540828520703082840795601140c030104502a0b40f44000c41c81569907a514a00304401d08415007000f8140781d00c03045200074403a400110322001900c90401d1001d000071084040d038060180e04c000510800100b110270001810760b00e680381d00f0074414200f2508000071a5107a1000301000300468411550300e040440038814140100c0e12094191260392003034604040300060301e844010100000039104240403006502c4107420340b0b40d40c10600c0380c03c54594602d02c0415845000200c07064501c240411080741d04008103110781d0004070400d0201c01d00c1c202950751141d03042d4403c8110072401001c2803100080708014649406441881203000d90703900e01240020a080780d0307010f000c000400d45040301300314107078886480b903031003190f4248412100c415070880098680382000c4800071090101244100924118 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 897389658 1250 897388408 897388423
    0x6110405040f0e070905060d060f0e030a0216121703060109080616080c030907030f1a0f0420010504090b03030d140420060a03050624180603100332 65
    0x102c0083d04d50340d6507a6a2103505032901038402e81c1d800300d850701030140020b0180e80144e0140100407030126070081349400c1d080c2150130903a249030141c2c010104950180c0c03c0d092119010740200c204e400c0e402100c80c1c507440c10003c00001c40500070200000070440507030040880b4002001200c0840f501c51a20007a1140d8142c0d00d000e904011512200c04900102c03040c5055901c52138070303800108801851501d4040c0c445d1040d1200352180e9000c0409940d03407400d180344d800c6c462290041b81984c0340c117007481c015280451b422800c094803022081038802d260b0780001210100c1e00000c00110f5504d0280340000d04503c0303821900241245800340d02c807050440360698074030881c081c082c203007090324800b600c2c550a10160000035500c40420003e03007000728001cad40b220307400c401d001e07100064401042d450503100401030102d01208200114031021305420b80000384800749400c2ea00701d411810902010408041c26003c01490400100e01c3da400f007004440f500300c04c006500e0071100c030020030f944032079072134014 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 897390908 1250 897389658 897389681
    0x906062b0b010c17091f08061005030f041113021801140310091d0a11030f0d081602122d04061d01030609021309150f0306110405040f 59
    0xc007040480e8660040000d40801c580081e00d08244142100c07500d156030b48502e40352540440368044407640b8000702c0d84c03000c1801205803100750803414168208005151401c0c00351003082401c204102807100d4900b51180c00640c41807200802c44803000c0011030b42c298098151500034404145c18004d00304e014100d2580100a0321960020907130b0b92009d140c10f220445111a00c2d4180141c100072804003544075035030a41140781803003a40b242c90300c1d9079400c1005050003500c043c0c00410b0080440c1c83d00344444a490348088000303000c00910302c6405003c1400040c6500300b4000204490401c680c0280035226a2080c7c07a031145940704000c00811001000c980d90a164000111400441c541640300803034055513a162136024201d984a0a0b00442e501c00c2481103040540350500007a01030035a0010b4107040d030489201100d45410115400100e4214240e910340318005c3c0c0c642000180d031408508001d50b0340110000c5096043c00000d804103200d6030380510b81140ca001c1c20000018043d44c030800726440c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 897392158 1250 897390908 897390911
    0x140102090607051e03120c0a021c030f060b09150f1308061f0e0606160b0c0d15032312131806060f030e010609050f01032a03020906062b 60
    0x2100383c0c51040d581e020703070000040080054800306000e21400806440c200c8509e10403281510504144d6500448031251420f011903100c0c410f18403445684c0c000c4201500b031351040f5905003201c1c0b8001403940303607254404c0201048000340030081c00d0010381c201c0390198005d0000c2170184c0d503605003c9035240d908460f404911150106810610310f103d92105088400c141e00c0b40d54540c1b1004100415980080300600c8214008500e910003e050300403014801c2d8440101261102c2c441c006102c00e9400c107010145442c10808810303c00115145000704400038085110340b280510240304170300d48614001529035100020440c01c80c7c122028050b86d0540d210559a4020f803a03a0f03207089010340d0102d00071400414100000c00031500d100380d12107059240b8120000c100c0a9540f500c2d00126007054800c40341c990031680050040c400d040041406500f01048540301000000112080c1c9100341e0100a1041d802c04021a001e0380e10007040e40c2010120007518602c45da450f141c821151040400a28a00d0303 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 897393408 1250 897392158 897392203
    0x30a080a08070e0f010528200a0510110c010f0b040c021f0509031209030d150b04090513050d0c050705010212070b090102070f030f021b03030714010209060705 70
    0x6034840c3c0c40100e0740000c040e003c024410140001551203802488541d500000e03480c600d0504401c5684050078094455202c03510803000d0600c00740780c0c191081d840142103612206a50002032000150940704881100002451307042e1810303551032912807806504402d40c20122801c0f4504010750180b44444811201040700d40700500c426602d0380410f002804c180400c401001d0700d420000d402071644a02224250382c5080f03d48540d19002140503210507103507600200718900c10421350b1141c000700195150034070b01c0407494846100c9041c41075005074a9032984400100340e041c0c09070428031059551240503100390170055a40209071043c6000d06a40520030820009480d500202d0564902840c0b401d0301d92811100761035009994402a05408030f40d9402c0000402180707031449090302c02c500c20b40c0c0c0d40b40fa00c815544000e10b000007003144402180c85180c805070403070768000300304e68600358008418039a040034000d90702e00a004032014140c1103080003a4440800c02c001c01c0014040c481c5c4003521428 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 897394658 1250 897393408 897393421
    0x315011713060b0136060305280f021804110f0708220303080a050108031c0b0a03020405010b0a14070b0f1302060708090f10022a030a080a08 62
    0x8100302a106050321460001101d00881c54640042ca598081030514084034040c084117645c0c43e0300700307480d9150081084082201d60394010301c924401042d491400740324138104605288081c81c03103d0034103500308440341502d68000b0ba2075006403500540707038002113403504a45452082c508200d000d0842c45245001100d044407131580041c1e0b40050518000e060034207116903254125a408543c2c080742d1400403e203d00d40e1814020704480146220381e0b9820503904002130118280c1b04180c216640eaa00300b0320820a800196503004844e04100e020041480404040803682140703582d000690000d00704800400e00ca1007003402080c44200c1c0341d4071a501305552540c00c1da200c0c05880f4000304051000e0b000f04981400b604a100c0d0000400f8091440c0e400c050742c0001c10a5001400c1121103e0011500004500e001075a481c480c807c20749054107107412145009482c0d664002d03541a01c6203038240d085100c0c000301030980469000140440e00d050040d81081c2c0d5030b64000c510251300203100800090710 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 897395908 1250 897394658 897394697
    0xe04060c080405030406031a060c0d08160206040b150d051e01181b080316021008070c14070302030109050703110a18051b0304140f0304140909030f031501 68
    0x8241e820030051170415042c14000c4001d45200b0a0b91070511401c40e5540d80c10365941e20060071070751000c0000740038006103440064540c84005010481c12440b105c00ea407405034000c603141d64400d511170103c89249d07440782d108a41c45925114116001410340e40c8504c00c000000459581d449401c0c0040084a81c0307030010303d401d8807018103154818108101c080d40000300e144040212058800345e000007180d4540350050b00e16042503c0301509078401580c00c8055003041c07155074601000c0c900c1e00d0901454450809021041d10b214000d01c00d042e8100f49101d03402061210a01a543c018004d02182c900d40c00c06541c2c80100e4042510850706580a02410346003d07420f0304129001e000c1084046203000450350024100204100307420109541c4603401d61150000a6126034805c1915800100101c40b5175840c0007001f0b40741d916943c1c0304100034028440388d1310b4007020562049030000c10701e903501032038141503018080210b03020003804410b11040c2200e42101040041c02a40c450015070543c030f400d000d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 897397158 1250 897395908 897395911
    0x51005150d0602090102010b030a080702100e1f03150617090303014502031008010b131d07240315260304260102030615030a090803010e04060c08 64
    0x9600100000c0c1c1c100c009081074015050032441400001084041c00e00440d0800118503822255000700250f248118988000c02c107043e40941d00d0040350021148003c640c1800101c2c3d03101420300d06a121031081a446608400755901920000320003040c0e030381101401c0121220095801d1036000c1d000210082c00000c152412148140094080d510701d5030741c000102350141c2e400340c8402d5018110304140c2c084165640f0140800640016503a02d000b0b07000c001041341030340100d079190341092181e00e0300d41e60b600c5000a291540d8040050341a65480d40c100d6041d81006000c011030044c481c00050300c08414036281d41802103440da0010302030701c4200c02c904444407850f010350080004e0034248083e40c0a1400300c0c2180e08a0f11042488980c60500145581c200c1d034000403800410364900d200c0c0c4a046c03410400c40005a41c0254150b0401c440010340c9030303000100350f101c16840400000c400c40b5041c0c11811b81507400000c81652940c540450403541d4100300c506440450804c1c1c8010a140d10412215 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 897398408 1250 897397158 897397201
    0x201020118050717010f0c0507020f090c041412300c1b01260a1d060c070318030b060a080307260f040909020103110c03030609130f051005 61
    0x40c02c00f40d0901d4603c007900f071080c07a0402d00130366a8005d1940013860910804100111549506490f112240f041081c00c403038800c034050060000d4810b000d18005001c091768151000c0b200c410502c5442360021580382e51150181ca2000d126003130030340d0a034201141c1031104c00c000e03082141d800004502c1040b4801c0c841c1001c01c6100b0750220b590b608000d9088680554898070515100d0049204100c0300c03c2c0702c0b840604805484d199610510211400500c0307080c031000441088609880c8030f0328079060b1030f00b4000304121405000082c2950826102d410300081c0c00c0e80500482050740e84034100344120308011105ca03030044000020100381c0c038078000309840040d40e000400e5080751300100c503e0703251003140c2c03076511003134020a01003c01018440006400079110401c0d00041c00107043c00014182c50003900900e00d10101005141451000031044a922181c01c1da156101c40e210805501640d80700404060300303d071400180001001004a030788490312141e840f00b0711158498680711440403050034200c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 897399658 1250 897398408 897398413
    0x30423030a080307030b0a0e160210151206060e0907080111091f0509030f010b091b030406020702060d0e06041209150c05030706050106020706030f050106090509060a0504020c0307020102011805 85
    0x10305404d00c030b50132030141001b004c1c0064017055a101c6000c801c110040d9408011904aa60858240c42d0704000b840441c10020206100f4a03500e00441c4210504902900144051800c40c074010701c034458020740028000d49203008600e180c40040c45440b26454000c200c019400c0030006030540004505964034584020861810441901c001140d0740740217074000d1301031040500030f41000f95014081000401810f100200d0210000010001d030300100901d14070b01c186958114292004015042d0399000368030040c0140e64003001c0c00010403500800d0403179003c0700c0c00d11106a120b007c1c0440d07024022881803051954481c202c3ea8113942200c018011003448548004c01c01007460302c1901286c04c050b004500f56883c10b90340ba01c5000907a4401d8000710f015034000403081000d00e07414440c891854030121170801c103a5040c46c1000709003501600c11140319200c11808200b4903950780d6200700040000800440d41c803000d14180075102d402800f8168003652030442a01d0307006040783c0f038000d0040e0b4003a02 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 897400908 1250 897399658 897399661
    0x606080105090405010e0d02030d0510030b0f07020c3604020609211e071205030d0f0e060f0a11130302040c09080d020a060606020c0d03030c03020c030423030a0803 72
    0xb448903080000f001500e0381e6480f41001d0365402024440d0444d01000e070b0b070180d6980c0001060800a460300501004084402030004001090a07100b20f10f8003c1d0703020f81980c0d800e0300c1e00da104915002a4105460f1b20190317800442045880f1110401490380060046400c51905401030000503d82140d000c0d4100c4010400c0c4001498589590307603c40ca160b1101407664041c10185902d0134200010288081c28002c810740c080d1f003400c000384270090141080c843c000311030030703035605171a0301410104103001074503081007205000b00345d00841902005042260046e14240392082014101900c000050300d18041402a80343da28104030748041e805910810211461942131000620b02c14502c00e081040403d404504900d060019000e044036590060103581c106017407000c05c031580ca901c00c03000c0d90700080c0403a406803201c2d54408409505800e002480013508002500a880756a0a18a450000080106198000300c0c16560b25010700304001000c5500d50003414be8640442c0b2f0007411010b030610 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 897402158 1250 897400908 897400919
    0xc0c0c17070306020705160512071415120f09070b0414010c1209090b060a0c030c15110d0e010902060715110723071a070c17030d0606020106060801 65
    0x1100654014112011900360554a443c0c6030100e070080760045030b198205100994601d0071840e891005010200c80000e0345010400041d695135410340304039002540c400c4980c6206668680c0751030b60b076805c0c1d01e99840c0e941580e1100d002a00c40c04070340145040011201058241c00300003824400c3d6060985928a00b0b070521000a11001c0d0402d0041d04018a0010f86800500c428180c4206003c40b43c03203810480c4c0c14484080c05a412003003003940120030602480b85815440001e159000380c0505014400c45d0380f07814400b190812020007211810b0070040c0c2c69500e0b809083c0205260b8454540c100302e610440240036081e0740c15805d02960025091121001003410b15414601c504190680000c901c08020341c040f0240c1c02c04842075807100074042400e450000041c42688000b0500000f40c440107041000c0241384e03200c111410b01c28001c010407600e042102c45080c110242004011030841e0040035003506599900a0007107540300c90401070000ba8550050040d10280c0c2c05d9612841416800c14 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 897403408 1250 897402158 897402179
    0x50604060315020a0801171203150d05070801110708090907030e0d4e02160c0311030606010923120703170901090506070f12030e0c060315060a020f0d0507060c0c0c 72
    0x4ac220401144070112100c8517580e560300c1400e00c0e5407140340600107882c03811240307500f12540803a0815900d6400c211480002e0708007c1220003c441c2126020f00d103842b9031001301c00a1108540c00d0300306100d20700c41507503020303002204d036000d0b5614400407811a42601c2015035008526840c01842654441e10034203005120b03040f000d0390100d4500f00141806082e200c14076864102910070b80b0246602b2400f80244a81805045400d04055000f00300c10b040000000300002ca192040e06611007440307681100e06245080683d540c860010014080e11a4141c420340c0c44690320720088500c26802c40840d110201900190340903000140c546c3e401c01443c043c10b000241d8003e010880305195005d1f0404000b0b0304100c090040e07610140c1e00041c2c24112486d0310342c6032084c1204180e1190340c0a00070401c4680d10040c0121680400740c0f611600c030505401c0580c0350074059003880000d4092a031150400c103a1003000351441600a4100b48501c00780003034191007640500c01c000d00b1107030000a080c031152504 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 897404658 1250 897403408 897403411
    0x11107020f150d020301150e03100f022a0606120a0b04231b0105070c030f0c0f090504051515010f020c1c020a0602060c0d050604060315020a0801171203 67
    0x20701012101c2404688620480c0d0200707000f01c26203540880180203080c00e00c0f4103584040c4690074141d1800403814002540c844064001144494a0720740c16101c405140c1c042d103a400103419401011160b9032401c04108800d001443c002074411400043d0743e602c3c012407070307101c9418034038085c0030509030540f1042d4410074020300540d81c840841d500d460409042006014903030110310090304102c1c84c03505c5210500d900c101800760400c041444000c01003244907052310101e0b0b03440300300310703410001d24074104454034140d40c0304510039070024100040322812604120b101e68440c0040d00c1030004180b184412100d810303100181451100403918080e54010f5034101c10014641c01114414801d0900003a0728100d00d0424099070701c100d200c81811424844c401c40d001d0820750002d45498500900422182d014100b2840f0180e03031034801041264640d54806805150400d012545920350758100e07034041d60111030510000f807000c03000022a40450700b41e20b044865085c0141913074000e081e1444050b07800 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 897405908 1250 897404658 897404689
    0x5190e01020c1c120f050f0705070504050405030301030309050a0b030105040c11011104061101050601050a1409060f280806010c0201030b0d0b0108120c1903170f06030c010201110702 80
    0x44229103680340c0e4403240070502120441d9002c050100c85890800e251404a0381c1d08000d01c0300e41761200f905a0b8000742542c0400202131100c5031581e4150400528003020b42d80200c0d0000d16000600c024080b0200045043e00e0003611899896542e50f018040d1900c82c0d441144162001030005100502d0f142d001034001c2d420518100e14042622403683d0308440740c40c8454403001c6e400181c200842900548010111810700000f0003040c40e002001078000d00c1140500000c00001443e001514142003054958a5101a0405071940304983c59030029910014035044412101c501c011006e0481c1e02080c0c48540583da030701d452685489005441081c46910102c1c1030507203c4100166a8541d00340482c100c07401040d0b200c805501d003884190034070010003001a10004100306041106600007451641b681040030b6006804c00f1a040443c1c529405c901c0b40d5102405d10001d01c550039503202d5000d8022101102039030080c041840c0164204c91691800b8041e88105210300030240c03401412a100605 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 897407158 1250 897405908 897405913
    0x50408040f1a040918060e01060611030c15040503120703050403090e0405100f020706020d020a0906261e041101030b0a0e150301140f0928150b0a06030b1005190e0102 73
    0x10003030340d104000d0300c1fa041100f15241c0c0d910300f030800203964003200c56000c42844a018624251203050407903204c040b013203d48911000441c000c20100002002112041d034200c03071000c449400d00d00c0d0300402820064034260000323400440b003c41c80104c5500182d00039548440101148041051110007600e4500d0411002a500f44440710101d0703500d0005182e0340030001c10040c2d07680141d4034041c20110300c0d44c0101c8100004900c40038030800d0b84500010122a20101d2000c4036a6010b00301c0c07810a61981541000076800d405201c2040403000041c004900240c90034829007035500144809103c09100351140069010049400d00400140034840c503a80500045440700003030384407181d80181580d007628003100c998200702e00b002003849429200301851403801c1c0c41500720480511102143d80e800340501c42c0f40303107040c60942c42d9a4410400070b20702522034150075030786080c007400402003458124041e4130200d005100f960300c10400c50789a84a0144100340e040403035102118500c510300403081c19403 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 897408408 1250 897407158 897407201
    0x20c0d060e0a03020a1403070c0e04060213060509040c080622090804030309080106050904080904020c0718092d120302210915040c0519030204050408040f1a0409 71
    0x468081c001c01000d14044d4004103e0314003075103040000e03003544040840b81c070780042c001e05000804585d44441203400140c0c040c0e4843c0c440381803c800901c200c0706401c42c0e02c4041c04c0f0000d4240c3e00710000d8601d03000e044608016040c2048070542d9002d400321084c42e400b50060800e00310b41304a2a05613078141c000d0210009204d4803580d03c0780103950046e001540450f820f00e1040000700024041c100c0500301c00e40c2c4114460420351350f48180c60203100a103912890700403829030311064003000014014002050341d001d222909140020081070414000c1d506200354000d07441300818110164910401840340c180c0115070f01c3e40300d1b04002d501000403001095000c01800c0302a944d01400000c0c00c126105140c20f403814000c545030310300341002c00d40c0492800030004000110b003000864038100e030701c05c5ea00c200a840606001c0c6000c110a504001c2d401440c00c1e003413000388104100a441070b0380070100c2a280d910340f50040515600d01510091440090070041070260744481d4224541d45002d04d0303403800f4407 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 897409658 1250 897408408 897408431
    0x806091b1e0a020304080f120d110d110a021005090309150d05010303021005090a030c080a030e060a0c0e010c05030a14091e030105010f0302090a0b0d0b040c0e01060807020c0d06 78
    0x607038080c040d0790740107a1012a05012521b81401082c1540704440020702e12450500000c1810b40250302209548681e40c3d008007181b0510101206c0c50010384007000c1040c07011081c006d90345038100201c11401449101048d00c500070840c40b8040c00703141c02c10300541c102078801d0304102c40d032722505a18501c80f0398140601e40d9082114000c0501840c4290040c1032000c3c00c1c0c002800407500003d01ea42942c8c1d10a800d1000480d4100c4c00b00c45445030005030b080c1c0d440343da080066024006500c44e01095118034404c01c04000b1040d0b0100381101403585c1c40e90b55483ca00401118003006001b800b03442d5800420441c1e481c640030300782c9100034504cae821105007808045000140100a0303464802c01491900100d524036203020712a0b00c1c05484038806602200b03045030040340b0280401032803001d845907110020042da546502c074000d80300385e03c501d240a041c600b40c68000b80e4020300e80300b403504003d269000071070030601620000d4440d078200c0d401000e1aa1040040141c01d119828042c2c6003140d42d8440001e5 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 897410908 1250 897409658 897409717
    0xe0a1a062703071e0602012304030e041503030e0f090f071206050904060c080a0509030a0e06070c170c060f07060917131a190c031e09060806091b 64
    0x200d00000116402132454580040c1c2910200d110b00012020016044400052500300040d002900b52070054900c46100010800401200350b41501980341c00030b00004155000b504991180740c00c3d218100245a61814480c0481058468407030002240c0c001400f40c911030301148450010510020594543c1c49012030340000003640d00340c484070b8669503480c41c09a000560182c2002e03821604020b1480c2c03c7c1c114030348078041c0c4400102000120b4800c400c0a540700c1099420041c3c0110900c0b100e5581d4000c0340800b150a40e0703200f0124040c2c40c00c82115441c080003504e80f044000b21031a0b1800301c896030348070300402e01202c00706e50038400c40b00302001c0d412400b00504101c2800031030a0003083d060110608682c0d595901015400001b0840705010070204c0042521550881c01e0501004500c0d1074151840c40412454038500800e41165241303031988905400115016501c1e0319504e503c450040c4800054200d031405c15400c104200d040091059100070100d0200001c1e0810580e5118410b210 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 897412158 1250 897410908 897410939
    0x4150303051e09041a011b0309060c060e0f0a050706030504020d0204052706060f03122d12010906050603090a1e0b01080c0a06020d020d03150e0a1a06270307 69
    0x240744400c61108503055030480110610142c1803100014187d626590050546456015034820007107540303030100401039143c100303031020009001a14000001049032550394035031900180c40d9480355a100141d201c1c003e20640703028607006040e83d012003281da0240001b401c2c01500ea495a003809510304c2da80080303d041c00c40c0c200d8409401900712418083d040004842c05070500c01e10980110b42e040001c00300541c100c40300300601e4008041d035101041c501140e45005010341602905001400310f02c2d501500110f10305880e162403081050700e031210140140c40c08100c0d1051441ea001c8941c800205140c01d5038010202c60111100340918002da03a0310000000170f80c4041000d40c003418044d040d0b487c100100d0300140407a0320041800c1d04005000a41d03030b0036544040e00c00d00d6583e1850401c8108014080b10160032884c1c049481801c1c2907201e140201221200c1c0c60b8842c0101511100602e070402c1165040c040001c500302c00d84a40c614103d07407104209180d80c0d032603c1900b00001d0800c03403444118 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 897413408 1250 897412158 897412181
    0x11090316080c150702040b010905060f0a2c0103090804090e06012d120f06060303050c0708030a090b03060a030b0c071103073c0b04030204150303051e0904 68
    0x4106140340031601850300595003101445482d600d210310f030f2240400c40c180c1d603c5580407540410300040800060b11454616001a40c03c0000003441400d000301400c0203011112050361a01c16042c960146031110301d10006130305165066040d002c509542c4071750000c0e4801340c0540c0c005031800c5d030348030342c0023003191440640e00304039402a100401c05e046000e0b00b40c138036180900039804056220703402a80121909801900c0000041032460018401c49144440c0c0d40f603441807007000020746906000c2c007540c01141c400e082500c190303007012680000101c01d56032020303a140c880249079403e001c0c01906c603410050540c3d410070314503000000801e90b0a04014010036210140568902160920694110010303092070f000307610246040100b8492010058501121580240c03040b24003014a0000c0c0342e289030f101d6482506081000ca060b0300c40c500200100c0f4401c82c0d040005000700c1c0305121070b821091101030003003081842500b4400c40c4280055068207401d001c0c1c1407400c02044009411a580d8842e207 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 897414658 1250 897413408 897413443
    0x41104121a010b1b01110a0207181a0d060b090708090607090521010207050304030c3015023a1b0e1c030e01080c0717090a080604110301050f07020c04110903 69
    0xc00ac406941000c440800317100c23480903c0080d07005400300c0b00b88040d10b00ca03603005190a840100c10300006078007500e1041c40080407c4040d080010004141721810ba502e1800c5016505c0460100b601030001c403811191b01800c2d014025001403209584c1000d1780b19900c8548d5001c11444000400c144024005140300f40e1184400b41d0504031410740f10310715420414001104444424402d030b6030038014404059200749200200c48160780d06e00085c0c050710000c540038404a10000703201409403020805100000290921081c80e6240102e09031400d00e401c200200c84e4203c4040c4055100c4c05802a5000014021800008504420303c507880b08960040c3d0014075440340110196034400c00d000d80107032000c8201070070112541c440c45c01d80700c00d5081e408008400002c2886460f15031030032039802803800c102500d4146c5007034244103a0741d1000b9001c0c02d00c40d511b40400160b202e5070803400c66015011990051a1025101703083c03000a0540030355841020740140060f010342e650801c1103911b0418180031 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 897415908 1250 897414658 897414673
    0x15010c2d140d050403050a02040c03020706150810112706030a020c06100305030910110d02061905041a07023c07051806041104121a010b1b01110a02 65
    0x40503003808064082d45081250401c02000801c0c1c0005120103c42d40440300051041003016054001307100702d64005007400d05001c4503c10070070580d10781034111118a801c0d41c8a20085140c114215502244000300c0d604c42072103800c80321040840586500710144202d9050014840006405600200d688403030103900000d810842010620140341c1003030003201780d070903300e007180d0380c0399102d00460003102d014031a8542200882c1e48103440c410420004074096445899000c5002901c3d03003021a040f407043d409282d11041c3e004e44904c100b611440d040186000310901c6820340d1600f125000c1c02c18811841107810010f00b101c4c0c42c032012280c44603001501c000c0c1e40071502240b20b205c40000c1c0700d482c80d600080c0082240303440d02a403090b182000207044c610143d41e4100020001d04408082941d110030114002c40e20081c0c1016081955005580b1140e03c0c00079104110b0b4442c20074020107600c030b001408804005559800c00c2c00b5210105000812020030041c5482915040301c0c00040041c0e10450 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 897417158 1250 897415908 897415943
    0xb01030c020c0d0b180f0f010c09030b0411030a02190602010b06040509190f0c1e0206011505070311010504230f030d051e0408091011030304120c0f0b010e15010c2d 72
    0x89841148209070400c62812b034516281d1040d070050040001e09010b011746605201a5814001c80e07848507070041044401040084000f01420624028075015600c1c002000c5014a0480c0a4600321040241103007508e03921010b200d400102c2030801010303620f072200f035041001c003e2405000000c1030700b6521070800c15040c02c800906119921489800d43d00f00c070005015656900380c040b0300c0d0804501f4441d954605501c1c0031601310103100e920f07104c01c2d46040c0a1000300310b42c0395110b03511100348480300010940b400070303842c0e04e8480d07204000d905944100070010300c4c55035079048198400c0583e48a1400403114800316980807408450465043c2000118014140350194039022417000602e0a100303c10300e14074803203030360713100180c0090054101050401c940e54421100007586540c080401e01744a1894600794102103028020100503150310f00018040b014910228064a00141e488500341010754a030022046d1000510714414510324444064114542008803501407080c4990140901c006 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 897418408 1250 897417158 897417161
    0x150e03032209020f090f09070e10020a061e0b0307062a0219050102010522171309020c070b0a0f0305150a1e12150c020316060b01030c020c0d0b180f0f01 67
    0x8a0b1b520b100c6c1443c2c0c0e05000e0707855800100d40d025090306441019405001d210b01340d285c5204003800609050400501e2985080034010000c0c680002040900401040d64105501d58107140101c10009000403241070180c01142c190300007940c115406d4441c4111113030041000312442e040b244040001014040003156424030031030358004003d00d114481ca4841303800f010b11003140440302170401a5415280f101c00d103503800403541c01d06061201ca00f80075032b80d0261340c8080c1d004200714604a00503410009240c54508048481c15005a03030742d4000e0244001040d030050902070f014606c0300c2c118044000e125190441c50707901400da01c0380704104501045040c106042a01d401442c0c241d142402400000b444408104040400300400416010f0b1100310072465405080d5540050f8406040c5100238442c07264030880c1011b1080e40c0074089102c11400c00da079103500f03152170150890480d80c41039011644420140c0d400c02c1c0a0030311003003011002c0341c1c0701d45400710b03a03400010b403504080003000e5420002d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 897419658 1250 897418408 897418429
    0x80603070f050f01140d29060315010809010b040203190e01020703020a0210030e1c030c0305010e1603060825060e01050f1803060103050601150e03032209020f09 71
    0x18215180c407007824003001c0341401c0e200c8000d0f0b90510a20072201e1100240a0741990494112210100a14011103105402d070801c40b0140904000d08140360b40020708210003243c0c410480200403030450844000115840c007801002800d055503980c01c2040d86a480c0d0000318000c1501509501101c885880184100e030007110500c0d803203a20400c401000690045107a0052980440780710100301540e0800703501900448600c01c8250103124141c5600c13410103c02c0d23103480c6070f55950401c100c101c1000103404039042802a800c501078644001000000c4080000c00e0401d4140703008640d031a510704c003440c607007001c2c4509011051702450b155858072110002d1080102094600445910080305c00a403661250100c5080d0004000a079910307007080c80e44600e0708014025044400940c0d5a04195449010a0050304035401c080b611001c40030748075181c0302034501c1c4020083c0d4076104c1072801c3c4003e20b4214040700c0010120044000400010707610103001e4020040b280d1650791006441001400c240 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 897420908 1250 897419658 897419669
    0xc1b0703020a05220e010903140307091412341202010309061127010f0206062b030201020406030f060b1c020f0c031b0a02060706150f0608060307 64
    0x881002040035a5500e800c000850301c00303445001000ca00201d001c90100341501d041c20700d450800002d400c10f1201540315480300343c003968031300c0c0f000703c411301e4011107d01c01600c0c00e00004240310814091b004102e041e00c5452180101141d961991403200c40b410b118040c061130f480c941401c4511246103414032804c000407950300d1031440101c0c0c00d0404449000701c1e1198080d04041e510480f403020803103164041c040d040c102c8042c1a8941c50b0b02a01c510170481080d00d410080b01d10405d09916950140c0c0140c0248a9103401801140d694201842070312949042960000c00b2840c8030748420141c00502d102440307020368005603643d030910f0781c0942034598098070034000360300d450410040f01d0b40b02001e8400c01300704901c41e0081041c2030b070605400703406652018000c090f400200c0003d078400000007171000d9003000490718503444004041c1600d40c100200081d40040707007041944006101580240045903014800f407107401d495030303600340181c0c0094001501085213681030046070b10781004170000400 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 897422158 1250 897420908 897420913
    0x7030b01030c080304033302070b1503030301060c14150118050130030e060a0306140301060305120a110a030c03031409030f0a14160311010203070c030e030c090c1b 72
    0x4d1643d991401f00d104100c0b00004541c009050304035500b400490b074558021141ea0b81076441c0e440600300204603074019201404040701c04000d1389041c3c00e0100c01c0da07048a8003a01d0f0141030140c55100d074112032841c8950080b10b4001c050101050450509017103019060410b5240309018003590240704464040c2c21203054515145031016a4004e5804810611141054041c800c0d0401e440d0542e0403484c1c1cdc10700341c0c2c2d00800218980700425030650002040300c80008901418180c2e10040c582290340c9400301414a80005a902c0503a01840c0000c100e1004107182a94451070340c1c94a0f0341c1490000c100440024104056950501d603041c002c0909808103030a03807581d1810001100d03550391040310b00501d030f0790401060064046010302000c107485415280215038030142d2500c000007511804204402041d00c40d000210a80300500c00d40b840b43c84261910404031200751026511008072041442c3e2500c11004c40ca0515110b40e91051300400d404c441440e01ca440c0382c1402c411442052000040fa507 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 897423408 1250 897422158 897422167
    0x304030905090c070b060f010201420b0d0b0307030501062309060d0210050418060603050f0f0105090a0906090b04061a06030f15150903010c0c11010f030e07030b01030c0803 76
    0x5e00c80b2201c207900310404444040042c030607580140d003d050120002036180b00781002004002007451000c214100c809041358103000402104851981c2180c003e50380c4650003840070300480320465101d07646051b0001c08035020640e5035a902401c0d40c0c4107400c2420341009030144441d08164410894030505d0341202c401c1c45c02c0c508400403500300c08c1c000001034880d071136201514410a0040084030060b010035030701c0ca56603500c1140c40c0f0000e4800e910604000902d04800158224003503554217004161244060340c869203828100100c2700c401822035802c059590605400050302032080c03001691050002840500c3e00c9c0c1800412100c081030358031410b03150380340d600d141580c0c0e15003280c0c4d1040e400000c0c0030703a52b10755600c400400000c0401c01c90300207405030301e0b005042015102606101104400911030212400400c41b00c01c400c0d210000c0003004030168804866018050650140c403003841c00140c4588080c20051501070b880d4819541c0c0d00d030840c010710a009030300c80c138480903029480007149030 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 897424658 1250 897423408 897423413
    0x3061f140603060415090903050c0601090c1223012c090d0c050a2a0f050604060c030c1502130801050f011203120c1d10050d021e0304030905090c07 65
    0x11444001e2200d44134940d41d01c1070f051040002e02c0c0340300c05068684c801b04140c0c0f09514010700903074002ca00440161180400025101c03d09014107600340e20300b9a2a0031250110161800c06404c2c01402d10300d06d04c5045044450007101d00c0030007030080c10107022249405d842c001000da4483c3d50300038a0700003009000100000c4800004424994120b00d00e810001c030409410007a04205d00d6090007005809034464000083e0058010340c018140c3c00507103081c02c03c0d520011403019010038403603160441c0c1c090100701310b03460144840b4001d460003802e020341140b500f6079a01e0070b18aa461507404804e680070440000d84003402c0e14050141034424000c0040f810400800d5965510511858404110000e801010544203010789041c40700b80b40002d12416001e036001401101504d0b602c800303404010302d0a408545001580c2d42941403580d01e036285800d548c50440e0020754440701961184001c2d03003c6081416044c08011440b440c017a64954200034180002c10500800140080011030b0060021001 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 897425908 1250 897424658 897424669
    0x19091a0f040c08130807200a06022b020f010e01060f0906050d0f03170a0615020d0c0b15120703030201152114160f080f100209010201090203061f14 65
    0x10094242c00c03103800c06444e1071034015158850024000e10170104910780c1540c41006500c0d20b001101d08403a6452002d49401080382c2d215118030300c49800840031580865414004082c0c401769860794410381c1c03000320110620600f034503000c404506991b99101000c0180d00301d240706000107032003848818080540f500c0001071003850502c201510038180d00340d2001c105402103c04281d500a41c41d11003440c2c0ca840b4003d08028912840b4484a003048c09004a15162010580c05110350140d155026a0741c159114a59003010040c2078208a980500d0041801e50703030b101035003030120004002010700034154900242134800c0320300e005035400c0c0502d40c14044100c04014030a207180d02c0d481046103842003800c0003140c42c1000d4502c10b40074051258550700c859000d201040a8400b00f0705000507642c1e454801036954181442d140c1e0250f0400254601c0740740d00c03500202505941480085081d606a0300064104001541c076681304003c0764800c82003401102e03202000806101f000400c102015201084 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 897427158 1250 897425908 897425911
    0x4080331060509070b04210b040b04021302040503150603011808040f1202130b04020d0501030f05010c0e010e0d0c080f0616050702060a0c020a0b03010b07060513050c19091a0f040c08 80
    0x64401d01f1082484008410120420f00c003103030403118051480c02c06040c0310600b01000c0d64141e0183e164102d180d5840d18140c0201c40464001a0080a43d158101c0c500e1a6001010b000e599140d500c4500508a902817840c2010b5828002c0302e6240c1e5462030060400b80d04030640e40f0640401c1c032208099030151366124000d4200c1c50811380049900d0107080700080c0240715182940710007628040c00401070106c50b1109800d01171180b4020012076015078829240c0b00d02440c210350000744610030000c5c0314180f40d5003640b2550f124070580c0501c3c9854800d100c3c100411201c2c01d103c030358025802c2160700381903400006210f09644c10041c0c509140b50f00132413007910881400e14180b050220040c01107440304050710b00104602500d1603201d58407918800f1941c0e10010042d01d00c7ea00344004140d0202400b00020381c469840320040404400c1c540034070808640281d11074240e800051310004008a40d4001c04940c8011140c140c034001704905c007001751031250000326601039072500300499a41c07904440c1d000d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 897428408 1250 897427158 897427169
    0x30106210b06031906050d03030b0108070305040c1a09040c0c1b12140313060201050106020c120a060e1c0f17042607020d060204210b04080331060509070b04 69
    0x2401002000130104001c0c0c04141d00c210740101c4810000c42c28954140e00c03500000c1c000745da4000444c1c65003401101500c105580180c08145041002c111051b080c0700c0c1c000310f0710700c0c10074058202019640050225904c41000f0700c007140302d8a150204008000c80c0405d00d140c0d0114014080740c2c10800110101046000d0041c01c81c1c00480c2d00350703640c9500f001596806c40f01203032144441da807203000080c00b030074003803144e040544903101704a0390700d161591b4540c0a40e00e03030500804c9001802c0d01e40201030848001214030074003444031801c035091441c12551000d4829910303103442400020710001e00300402e8851829000e4440018807000641400e03010410020200c0160660580010a00c1b407034850814001d44c420450050b0710200140c94001d082101c0c00c0c0c00c0003521400d80e1104000b40507903400c0c4004d0585070711500081c00100070b0340c045c640103500d40d454440024170002601680500304850441c0341884a006181040001e0003410307030201c502406400c0ca18036048410340140202d0042 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 897429658 1250 897428408 897428431
    0xb01050303032e050d06060f1532071209060f080621071e060e0307230411070b060301060f26060c0a0207050301051303050706090602030106210b0603 66
    0x103c09044014034a0100036040041a280541c036003440c3c01d0f00242054440c0c5140303840440c0340081e1a10601d80d0018184104c0d0311032621003091100032688401d8081c035501c0310b0a0385142c07200c03030717806156014242c8144601c83c251319005440380050b000181c1a4021000c01200c0055441d00f1544035021f2600054261162000c0d919050001c2c141c0388403000b440d5001d84618007001038940c503880e0101121a0b841c4011901c00364030341c1d504491440502c0b00c1141c01d41e00c0480e080141015410740c400000b011070a1000d040c000072400241500d124204d65401a10042030725014015104000340c3c0280045008018442c502031040500c041e041c4103c0c503001445e003140402d0041210044422030310104281c9484e45400702c80c50344c01d41c005600c10001031188403004030f05801d05100c0c4070302a00380400f1a00c0c250101d59011940f42c0c1c42164101c0c1c03402d8480c020300c80040c43d540040c5d03000c0c29180d03c800c00d80203600d8180442d40c1800341862071141c3d0600d048140141c03105000c40340c00804000d80c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 897430908 1250 897429658 897429721
    0x12060102070302091311180415060504060e19060e1801110c0a050d0807020319180605180a12080c0304080d02060601080a020c06060105180d08070b0105030303 70
    0x10303400c0119507800690050801010440c2a900d500600c070b003014030075a041c8101c031a00609000d080c00c2c10724082c258429143e00030401003100e40220b5041300c103180c2d40c04119162a01c0108003a52802d6112042600719942801845d240c000d9842c5d602c030840072400c101c2d2914080c04003054940c058a20340d108581e481044046003000c0d0440d0400040c611030140d0380d02d0039503082e5507603070740051029121800b68010060100340314001150058030554029818007000e07000c0311802d12405810300c410700801104259807560310f1940980200f40035140c075500c400e048540b1001ca03004106220f031003100c201c03206110517448500401c0c0d40f150455421034480200360b613143c0c0341d03210f1500109028800d4600e850044da50002d10f55100ba1000e903180903032901e1315420350040c0e0050300c0445015421040005159510490241c81d03601c51118200c0c4d1202113010204a189101c0001501c88450010300030041c0110000c00500410041d80103520314070f0010450700381c0c1251000b001200140410 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 897432158 1250 897430908 897430921
    0xc0a060506040209061606110307080a05070c0516060e01020c06070b0402010504050a12050d0903020f0f06040b0c01020304050d0c1a09030d02030a0207021f050703082203170c070812 80
    0x741a100c1303404016200300e555441890210041c4130024104580d11030a09280311840041c800a40e406002c060315085110f48640b66054041d002c000c0600041240540358900450303010050004200d9004404210442c2025001000c14410490301419944100021030158a42804403449a074001e10160000e40701e610040311148541e41c481c5038804401540442c030000003100c2555100c0c40703082260044c40c8803000c00d41e02c4440901c0084c3d40882144c806c14094100401000014500201030030302d016140d4081038036941040040c1860303a076000c8104000c1090400040710483d0709420042d01c174811030b40d1051030b0070f1182d00100c0b51103c60b80020495204c400c00a68a201140c204150349a01d40040008000d4000341d8060341b05084901c0e072034002207510712000d21000016030f81e451800300d554405039405030300500140c0003103940e454080d0780d01c0ca140c50b288200c0d0384030f9a107030a2402c605201400480300e0142c9107201c04081008840d0005480c04110b0302001018450b82c00603036240c0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 897433408 1250 897432158 897432161
    0xa02030f01142d15030f0127020d150f080f460803150d05190317010e06010f18050f010203121810090f030804140a0818060c0a06050604 60
    0xf424500d070030402400f0f011001c01e2603880614440e005c1c0c03840d004070a80ea036459200035408407501038a005518540702a103200f5080d0018074442c030f00e4000c04603140343c0801d44441900300662102c090020404000e2205500034844a901038444900a1090503007090303411810925802400c0425080441c00b400e1442c030510914031304101c1283c0018148045043c584015401240e5601206640f80428031161400c004a895000c0c1c000008145001c0600701c0200a40901002901400100441c24800000c218402d0b4061700d291a100350590500f50005440407160000b441c0038000401140601005c0c05034040d422200b01300c4603030382c80c1c20806005070304600c180c101040820078074400f0455007102c040e0f81101d0b2000c104044540000924030030100f11100c100c4004e14108400d26202c0101c2c1c840e50b0000c0e0803c0c082e088081c030260182d01014a03205000804680c41c40c40498903280c01e88200c5040360740540252602441c2c11a65030045464070706c6410024031841d41c81c000700d403064945 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 897434658 1250 897433408 897433489
    0x3061e1e0b070b070f051602190801051003050d08010608150d0816050f01060e01031401020c100b01020c1c02010f020f0304030807052e0b0105070b0a02030f0114 71
    0xc08107000d0340c4241e2400c24082e0f80c0d0f011608240418010250610103600c1081150700c00720850310f442c4010700300d40e400c224215400d1042c0345529901800d0103c0c0215003031141a010707910611041c18090714514016040031b480100400c24420a5001041030f250040345103903000395852424445440c01c100003400e03000c0e080c0340103410507001040f051411101c8d60307445101305010794109c07100000200d802d1340c01d0743c00a000d2041558003d5004000180308203500c00d45141c04c4400250401e03c0f0030281501c1d2406c2d4920320003802d40c4440309000c1a5806200d080000c00f4151528070040c1c2c28000e008021070b030000300c000e040181500710a40d100d4401d21003440c440f14440c083d00c1d075480d503d05190350190032298040e55680110250041c2c0d0b5242a000c4c0ca480d00e200c2d00c0c590506507006001880242402c5001d40d05001041281c3c0001603c0b141c01c440c07095504000050f00c2e401c0c164260b034090382d4142c20a16101c54603251200e80e5540d002d009120098225003441070b000107051202414944 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 897435908 1250 897434658 897434669
    0x330b0909071202190c0b090102040b0a030513240f180807020406170c0a0905070903020d0503070b010314210f0a0212070302072d1a09090405070603061e1e 68
    0x450000e0701c5085c0d0300400b680c0019020304203555064407410303081402c0344200d01c180728514504005444809000307410542d40034403110043c8182e042c3c55210b000d08100120705050b07003074444402d920002c4000303200b203041414446d44100003201014040144c0b005810307101801c1c2240100340c50003195541d80194000c1d044800c0c11203400042400c1703050340d0380c1608040a00c11b406004000c0348800040c0b144e01e1141d141030f51505a0703070f071130342e000e01ca06888908416a0180000c000180c0496040b290300342c000c0d8400d21200d00c1c01c000c8502c8550604503142284a0078100c884080c40501c2120710503150005540a0f807183d031440e00c52800d92414860803040c0010740c03030126000040c10340100304c0304200e460509401c0b0415100e0035601d00520031129101c94440143c3c034003031103207036103843c214098005001d031118606100e5500050318214115011500ca5108480034800c1c5175150080d6001000004019031002d9251030301d59021141d1800380e42038400d0100004402c14010880007801041c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 897437158 1250 897435908 897435937
    0x3020c190519150c050912010506030601030305090d08030910060602150a050a02091e1c0309060302070606051f0e040b2b02060d0b09011205060a0b0301330b0909071202 74
    0x1145483c024241d60042e0401b1341c0304038840c00020a5034107041c0215880f51030000c0180255a00b150b03015034030b64001d500060b4208000010740304c0000d80e42e200541c0680c00c1c0e503008080c10b1100a19050a6403640d4020408540005022003441da10501c421500140c50a0000c40d00d83c4d140c48908000b40107410f003040e80000f0540e40383ea602840400f070600511001d4409440c0c01500c07004400700e00502c108001e0004100c04070400440348217502030089188500d04c0850b185035030700c0c0064402c0e0403241c99503142889102c2110407803504500212a45072044c0c509021041c1d01c000095800800604042d00c41c100e504121612000ca0100712481164024091364413060800600b00061000508980c054a046030012490f04441e424000c1480d0340700b0000c4c04c1c1a500c0d180d502e07000e080c81903101030301903490b000301d070301215502d4804107020090580321540d0010b80c011040301604442d40250403042c41005443c655480319910507038090340320b040405940203e000401300038841d02100580c0407 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 897438408 1250 897437158 897437171
    0xf240e130c0504030b010e0705120603070906080309130c140f07122118020f04090b1602070b1e0c030f13050102060f0c270406030303020c19051915 65
    0x141c009020f401a00d014264900082c0c0e20b0317100559101c44151080d43c04500148401401c40002c25100c0750b124101406481000d540d0700c0f200c0058030740513045140c95401c0440d092040341000030310034030001d0900d001032081d0362f02d9a401404805403070520048502001820000341c000135400c554400b03600803501c20542e028207400500da030342d100f8040003c4241010642c240740200b4080c48214072b03100c1401541d1044540c1c200148a40d60b1a04c07a50080c0c3c84109410100e0500d40000c0d10440ca007034816400c480c001038009040c85d0040d00022440402030024507504001d4055902c0302d0b82911000f070380d50b2411440001d1541c0601a0b020500306030018052652220204083d421074000382c08440785178a1365094980c2c5420b085880700c42d161801c0c80000090020b00440188844800404142031403038580854240c409941007580866000952080c00d44400c220282100e600003141d00c000303107117170f941329902c8201c0500341050881100f02c1e19028010f240b00b0203010366000c00380c04c015a = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 897439658 1250 897438408 897438431
    0xd080301080706021b0105180d0b160e0d3503044e03060e13050606010c0506070e132f090307120302030c0312010f240e13 54
    0xa40d1040c0c010f0000500803440c10f13070750300d0a03640e4081d404607105856403810024455405e440100d030b111600b5074088400c0c0080c60220303003000b02e168003d00b0545280da02400100341d02800c00031450644070b000d000102e140c0c10100c1c0041090805080c4641003200800c022980c29201c1304074080342a00804c0300001c14002041028a15000c2a01e1803407007241c0010102891440312a505c03048440c84281000845000c41c401c0382600c1070861a1824001586d588500c4802c03001501111100c01130500c5158501c14400c1c03c000e00c40d4080001d10308104014000d80d980c64481d440a45500309001100300c1500d0a5601e2489245401e600804108005400300c540b0400302c0303040c6d0100c200f9080090702d149904842120841d485080003400414003685003500801d505405a001034003113010501000c90442814001001c0c41142910f1015881d410700e440228400e00c950301c0081e40982600c0507140c100030980f2160b0f0a410709003010f00c10b034032803038020800c051603d0511714071182c40c0c145030255 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 897440908 1250 897439658 897439663
    0x2030709050316050a0f05010206341709030703051207030605060a02010c081803070b15040204030c0f151b0f082712120706060e040b04060b010216060e0d08030108 72
    0x46400841d501200170356542e080c649520b005024550068100000245070404003541d4040401e03a0307446901e090300031180ba80e0b00c3c0d80800c2800040021146504680700c0c0c000f01090613088040311000e503103000d8141e90050500e100d0003114121520401c800224054007903070110b40180f2001c0d100603601d00031403100038020554030880368080f035007610100388650156188120003200c55001946003a40e10340703d601c0b0140008100105c204501c00c824074031602c40e400503000862107505144d0071541810814402050240c000703214500703018000308202a0f00c441310f11a010b80c0c003207004213000351034140110f040035480d40141101000294000215180c1d03080a940c44088894882c0d00f042d9002c10001c20380030b1100c0003001a44040f000c00e0070b91801c08002e00f50507205160008141e03a45d000c04681e074000482d8259640b030b0a600400090015a016100c0140c2d002d01c0030b400d15100c44641d00d000440c91b805264208401c3d620314410984070030400d405642d8000692039100c1da1b442c031800342e = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 897442158 1250 897440908 897440953
    0x30408070b0910020c22020f0f0a0914090a050711120d0b151b030c0f011a09040b04031110090c03020a060c08030606090103110d0c110708030409020307090503 70
    0x60003214007038400003d2070310108040c0c14100c0004e1009200c2e14541c840024003c60812091841030f80c00c01410b0603209203800100040b016100300c65803a143c54000c040c1614405074000141950120100202d691b2071121840e0300a0b8074501c009100c0e101c441007114000d8001c480346601c0c4c410919480fa04220040191907280710520050202d045000c003840b00d518950105c2403543c41060000d00300f0a03407078850740d510344405c00c4105d07424a00036211140c5400c40c010400a01030359986098140f08003203603800d00e1003c40030b641740652814299541d249500c001040038042040d103162440c5042d0040c40302c4110500c0359070052041e81e02d1400c25004016003071004030b01c00c140640e03001a029010721220401c1c03d41102406055a0352001802480d5201210300c90405649034602c0b107404401101034418450000c00c0003900d01c020b16809444005c0c0c81d407030044560301480b02040480c000004032019118600d9003d40c89459071075003a11890f903150001035150040440e110b242c41403001007007 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 897443408 1250 897442158 897442177
    0x2120a0314131101030207170903010b030304061805100c0b062206080d14031308070c1805220f11030f0d0e01051e07240b010311040b1605030408070b 66
    0xf01c0c2c40d00c0e0380360011740c101d11492500400c1d0b904d0241000240203491320182c40016000b4001040c008030b4030001a0640e4407c0d04030f0008100c00400040c207046540c1c540402600c0291000c003400c500d2214040d2a1040052004205c0300520f000503803140c0f200d490301101290541c1c1d180c2030380806212403c000e0714150150002c031381b0a2803109501240b0800164140c000700d00c034440c0c07840d00d560701d01443c000c01180060390024801c12095001490000071403000700784024601c0300c0048201401029614041d029004c04c2c0c002d101c15075951010b81007015403565011005060181640c0b40c44040c845007006801e50501500341c110380d1034000440c002240b481c44c0daa41440300110400152424080c8000c800d08566012403050840d08008008040b06405440480044000500e6211848540030b50703031640036885040ca4803455805028062980000708255070400b41090075504990140c2ea400c2c0032290641000402407043c2071088501500d03084080d02d0141c0e4862007025a16880801076 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 897444658 1250 897443408 897443423
    0x90f0f25050105090607032f160509070e03070504020f040e0f0108060612100e1f0203010803030628030503180609130507090824090d02120a031413 65
    0x203200d14040e600500740d8205031112820300d00054148403450700000340c104c060003140f402208411103030300c0046c94902642e4915070344103400400182c0c148614881a40d080890201080c800f0f07564070100340b68402d0007032418012101c00400001e107011103a038020340d00f00c0d00c00250b41039030b0000040100251403040c41e2048150701d900c00c00c074498010910800341c60b0b4100d0b0000c5029468085d15076046c814000040f07511001c0700001803070844031200310b100c07080c2d4001502030b43d4004000745100b2002110500450440d0b14142800751071f407000604c868030801c030702a01c665900300000d2412401004400b550f08490741c4a1070003a40e2680400346900c1c0d0700d64850250043ca160440450351500c030042c5c084009540146904805000054005028001d40010106107003c08004c0d0010f180c07000c41c0c0342c5508100d480020465001d02520f5141d403a0000b840c401c9020f5000111200702d200c080d6181c9584031400745d000c400511103080780807401020341c2c0030700880520046529a4a5014042 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 897445908 1250 897444658 897444703
    0xc0f0c091113030f15140609070e2b050a0602041a0702060d09020a09020a02060613020703021203060a03060f0e12030702100b041808030a0608160509090f0f 69
    0xc400703480c0d00a103036408000401031482400042c204250342c1c69004c0c400c10702c17050154181c0c50060152041c0703000c0444030103088401c00c91b5911f00169151b40081440c00d0030103620282002003035102c204034815440260a03545000c1141400135480307050350740c01409840d40d0411609d8500041e60151140d2150150a106034265034a0800101e032000366004240030b1a092405508102602c5080d1060b60b01140c4000c000920b001140014403004070740e540503203000d00e010340811603203550907804414018410300c5a040043d400044203000c81e20002013040d107a03a5000c001400142258000500e40d43c140000241101d202c0c0d0022240841050181c03640641d0519501d0841e0000700c44108c0103a0101046d80c07541c400e00da0001ca041c040150000c109540741d902c2c0d9484034003001c04216034164000081162040051103078401031300e0010043c3c140c081c01401200c1503110b19000b1b45201e503011070042041d244080001c010740d0f01c0808203449103418051201912400c500c40d10f510390a0780c0c5613 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 897447158 1250 897445908 897445931
    0x1507060b01020304051818011a15030105091b0c070909030f0c150b010302040308030c0a090801050906010b0c25061805060706090c0b07150c170f070c0f0c09 69
    0x3603034245c2d400500039246007541040c4800b11014040d0011032002c1201005400e040c200380511101c816030b20450300360001c098401d000400104d1205109042401d00040c0010f546401445030484413000001c20038820070001400c00b80315441c01011140314903071000a5602c0c0541090121074000e44498213003250a140681d4441c501c070701c0c01401f0460b01507060100f003900d40c1c0180001305061500608003a02c0790703101e0400740d04c180da6a01884101060000040781e000c060003000d8913600000340040c0c1080310007150b03510018090f40800c600045140d0b04410820040d0080084005942c4000d0542c080c20824903d0f01500a58002032441c425644007058031045041c01c460700604441e02d0030406855107001086040e908032075035803190b44009485a480c40281c00e041740241505140690740c598220200c43d00d04c2c01d4202803010307002c0803403c2d0340d41b130346641544003496030040011a5100d86003160303541a145801090030031075121001c10310420030030000a4485d03050f010801c850011 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 897448408 1250 897447158 897447163
    0x40f02090105010f02100e16080106050f0319230607080a0f060f1a040e1f090603050a23010f02031819060c1e0e24160f021507060b0102 60
    0x4683c0000542d110584206c0c180c8a1903020081c0181804181c1d50408200c080b0040024034030350100301305a440d500c0520032440c0010b005002d491007140107181d0040c5440ea000300401084101405014182c44500c200001e00d4001006281840042d55240d14206101418810b81500c5103003107945000280c08402c0742500c01c1e4000e1b5045800162200c80c5441d1011480070024003c0703408a0780d0900c80000c0010b0112000b0b4040c02c070185414083d01d11b01058122031609503031142040c641494010130101c1c401007000710300ea94021803002c0123014014001d501c02d8100480d14459586000b0542120041c5a4091405500c240030b6200c00ca500f8200390580e501c122807100c0c10800285070f0440001002c0350300408143d03005080000c01a4010700d03240300c03104a200e040780c0210304102c00480319443c200c2400716188112822100700700103182101e050b00e010b005138000704080710b02c0c1210140400c103040c044040343e00401c10340300340381402c140c0982d9402000c8115100c50610340d40c200c1c1980003 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 897449658 1250 897448408 897448427
    0xb0a0c0302031e150405011d0f151e1c03080f0603060106200d111c0f0e13150f060203180904020117010b03180304030c03081c0203040f0209010501 65
    0xf00081c030b203020341a10300c034031602c21020b4845070311084491004080c940b030754003400d4004c0070820001880c0c12446403e40c010100010103580c1d251b07568208018940e502546030a400c10f800b5209070000c00108110040f510711031044103580003805208440d42c000c3c4114104100300c0c03081c1e60710b0450340c880444c080b41201095450300d6140e040a00140440c0d4070895010351852000300a101036050f98504181c10885100802070006900b2511042100000c12800c0c89a058440800400403682c0700010001411402d020b01040004200007d290341c4840403034603547c0b0655010010500072060000003140107200c1c810101003022800262940003005440c40400b4030300300c003c1400108000c02010281c014400c905005201801e030741c00e008004e03101c9000e082000242a92070404221070b044504c0d800750140700c06e82c070070001030000422040e1152b08483d80464215181e00c1d02c50b9003a41203113048480248140e00c0402080248001054008801c0303000703980080450b600c601c01115800507 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 897450908 1250 897449658 897449671
    0x160302090604050717040503034201050f03101d010e070e0d060e1f0c0c060e19050304030614060607120212070326010f09020310120b0a0c030203 64
    0x4003040001d41e907050036000300b680600c0501d001c100002803010700d0005600c080e5410358442d4000710030070a00c003403681400144107680719400f80650030080d0070f207008515603038403019059412601048050340108250340303400d0500d0b040181c49180402118000250511601000c6400b000b101c04050b0b0407200210b060b0383c0500000b002681d600401511f400c146139109540141e105132481c0c000c17403140d1040101c1c2070584406003070310114030080e07403042203100c1d0082c408091424204142a030b400400c01c5040c503a015030041000c15142074617609140020101280500740c01041108001000c0028803c2d00e00c1210100042c491070317034600c20070000480c1d03180d030012800c00542000c00c42e0956000b11000b02481165045012913180b000c20b50000c040490128401c50700f0360000c142c004038143c901003e0140c04070031a6142c800480c1444c00d483c031900300c0007a40040400e00401c11740e99110090003010104054618407071602512a060840d29582850b00c1c018500d04018401d0007100d0103440c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 897452158 1250 897450908 897450919
    0xd05030c2a10051e070f080a140414120304080607020d02070801061512060308040605040f0909050a080c0111040e1609030804150e040e06040b0f0408040311190314160302 75
    0x50030321211300c25101140d00c60780c0141802258000342002415511540c4500481a25441c0400e0061701985601c1c48044012906100074400d01040c280c0c6280080030449038000c0b036825580c1c07071600714030942c0c2002c051b902892003003007003c0340c00003100501402d0590071030b5180342d9503100e00c600720740c17071409500011240c13180c0c1d100a043c40f8141c40140248903141c0003038146d80d0b0345d4403660240d1040d8400c0c40404c80c04141042089048041c2c5002071251180502c4224040ea03502a01c4507201d140041c02c4060115440700000001d50010601e01443c483c030607900d030f4450f21241211403040b80d42c010b00000484a003a10b1a111300400d400303c0381e2001005050a0520a00d0742c400880c0b00401d4041000d4442908078503036070340c02010707507940240c000341c0030a09107404d1444400c5d8006103d06070b481c203480248000111040d0032101108e410030001c108230000000003030030004040b005421404c04046001c014400b03012001070300e010200044682e00040c45100400c00085484043e612a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 897453408 1250 897452158 897452167
    0x2060a020301120f0828020706020109080306010825030b28090f0b130f060f0608060d080d0e0c040b0315160c050307080a080f0f060d05030c2a1005 65
    0xb07001103481350099108518803130a00003d44030300600c0000d803d02030324501e80702d00100700400760180206406008184000c1c8000000d5485180303052001a1260341001070510014800c41170100a00d01600038005e80907070713440c580340801800307800c510112a10a80ba110b100a0101c0e0800d544600c1c900000002c82d0705061400d007884004259508080d0040c6071287d400f0f030b22641e0348411034006000c051500040404040032440202c5100350084a4510006c24007440100c1d00411007660000d802c41d1032200b0000f00d4500348400d0301821440c5283c1d58101491600f840744003040460020800b40c804100400c8194101507540f0601802c6a4440301041c1c0030035154900760440d0084601c250421703441d0b070300555039098a0b48c0c0c84540d05403512000030a091094551140c2030f180c0120170301d80f01c60304c281802180000000c030040c0049124984c80d00182c41000418800e80b0b44104001c01940c0b0381c400c050001200c5809484111090341881002d01805407900c000035195001450b560103051 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 897454658 1250 897453408 897453413
    0x1e08030c15010b0c191110090810020c03030c0a0c02042a0e1305100308030910050c07020114070510020409140606070320030d020a0906030b0a031e030507150b0102060a02030112 78
    0x9466010804d03a4540c6440140f000782c4c7e102c2c001205400c4016560f01d24002d4035014084c0e0600a00030f9070f081caa140104805070480100100ba43e820841d000021541c61300049002d680a41c2c2c075a00003500141000e44a0721110340143d026101c100060300c106802d240e400d007049035002d03451100c843e4490016001d90701809401c1e40140c0e80054840500310030070b62039456480850f0800c0b62084d545502c01c14142030800c209009040e004a03082414909002007580060900049400c5040320414046001c0f800d000d010803080c2a02c1036142411950380391580100e6000d444032100c90004c04014402061550400c1c1c02200d92a9805a8aa000c01c40013000c0780d03403c051041c4c44800d2944001d105014225160f80b005000812068540c554400c0c60b00d18040d05036501d010b8803501c10500240c040020444920442c24024000070444001070b403e840d0036213440c0114100038100d2000d282003009241c210341d029869030b420903001c03500d16030f0b141c5150381c003640b02c00d018038002401c1c243d500800 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 897455908 1250 897454658 897454693
    0xe1009061103091c140a1e1104111305010e13020307051c0501030c0e04030801060f030e03040f030c0506041203080c0c16150c08041e08030c15010b0c 66
    0x401c007050a09403480e01910100082995501c40b201040c0c00c0e24200414040003140c04c800c04254490b44098181408181c840020084040840601c5003080030700321003c01c0340e54000300c800362030010001c00c44c1032941c41d00c46034541c00c2100c40a845415009000c1503640c00751200d0003002000518000803d1040d001100c0a900050b005400788842800394244040b007141d240380810111038000500303580f640c105103028400d15480028203107070000912020950002e0310724191009030400b01c4514501c3c1c1811402400c15824000d1540404107002c0381409481c0d00c0c040460313004014041c503540d01c9504010342031040d07201e4806020045150400024040c07524654400e814903405401c2c1442c00024900700711810090a031120072601b0107000c402c403680210314140c80316280c4644d20603080e07554881d01c0d01c1a4000c40715942e00c1e0b008161500103070000071001070068502038039214205403201d01e64440a4001500380d034440d600000c2a4001c0e1102582c1c2c0801c0028002c081d002074103000d101 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 897457158 1250 897455908 897455927
    0x506091e07150e060703052107080403181d092e0b0f0901120b07050306060703031109060a08090c100f0c2a0518010303090611030705010c080105010e100906 69
    0x300b407008140f1840100e5a4034000360003058000d4461035503d442c1c00e481e80441d640d40c141e1201030400340006000f00168810b84d09a40280d25051450044900854108040744150f004001c01052060440c03100c1480d440464003504801040314200914100d42d451000a04103089185a030500141e90344907580341c12254134110080d200e981600c039084042180118241c0044001c3c08203208250204510304609a03408182442c146086042010029170751b0300c103c0a02404240e1115924503100720380744101c3c0c2407808001c4c40c07207a4a1503008400380409504842d032980a005400002a80d424241c0d0186e0901d2820303034413001c480100b89816940c0e0405000107443c080b12040f60007690040f01045281465030141d8140d1040d864002009150110606a5001c04035100010000250804404000d84039203080c500c41d801c0c42ca21505113140540c842c040d100c0e43c00d12851007d40c0750001c01180c181c950030fa03211855014400306100b0b04410b0740740c25400103400b50108111042c4141e6011 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 897458408 1250 897457158 897457199
    0x8093c013522060b091501050d0209040e160302310203090a020a0e0a0605012604031412061f14090d0501060801230906070f110a0506091e07 62
    0x8000c042d0031884440c01c544020001156801d5640d0240c9015113401105140d001d0140100e00b8103041e81c5000083c80340c0103200b841d5200a070007150b00001665290840c1c0d5021504104803261a00c03144c660400744412880244c1c010015608803c0031000c401160103e182d07806416410204004441c0b103001f0b41c0020810411402041d89000050356000d005400802c85440c2e200d589007058965202121440c3d4801d9043c4048840031204064050340e1000100c201d10907074440d5951182000d54001c2040c1d44100f2800f01c000488940701c0942e1a00c89005400a0700c10340016200d44a40d051100c2515100c2d070040b84030703400210300004640d00140030b6404090b1610089022603a10242910183c1e00420303000c0c0d440701a4581082481030941900c1e803071016100300c2c181030100c145030316040c016014108101500c00401a000e005404900f54080018100d440880c4141002a00e91a007644c8008031030040e034400000c0c2080c202c0480c4514007120010703003011840c0c550003940c0c0c2c00311a00d16 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 897459658 1250 897458408 897458431
    0xb030307082a0312090d030606270f0305010f050705120f2703030f0a0903050a0503060406120515070e030d05090a0b04060801031a0408093c0135 64
    0x42c00c0d400d03005202400990311002d42485540c00e05079040b5007004036101881003018a09941005050b40c00317110510020140407032214540c2d0040d0200803612401d401c03040402e04440400010040b05610001c0b0521162004100c0d5440c0c400d402c0300e00344a030f040c1c410000d2081c04003280b0f90b04039100702286c00c040c0c60b00d09040b20001440426200c01680c8501c1c0c0c07a141c0001c000c00100029803010701740d100103400000c0000c0c40c412b68018042c0e02035a640305040000c0440000c0312a20782d40c0c0030001410b000c0b41020110550381c80c026503100c4d454440c2100044184001c20b61107801030760031260410b37006005c3c091400c100d0a007240c00d6005424240c0e0b000c1d01d00000040c50741a4000104098190303550341003c02d6046080c151003c40d0401d10280c03c82c0d010108100100c1d0902c004e4a003901c0003200c1d0000302201c0d20315004000d80c802d15040307074185071000e142d210800200724880c2490781c0a032121a00c03011b454403208429030b070034100081e0702c581d284422481d034801007060076840103d0803103 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 897460908 1250 897459658 897459727
    0x2120c03010e0f19240207051b1e091308120103060b0102070608090c011b05100f0b0a081902011e090e01170d030c0309020d0609060b03030708 63
    0x2402e4072511105800c00d90009021446400e034144000401e9940c0703800f52550500c0075581e510b030703110402281c1d1041c1d000d81000078450015582c0498901e541c02600f1501c0121001006110049a07a0301d01c030310030010400c1241e040c13142c003029108510b400800c800026503440042a1445500460884000c0c074100003805501c803040c00254083c40c025600054a1104e00740003900d464800c0d040032090000440c1000a4110000b070500105c0c0401c1c40d2160b590315460540f00402080c04030010b1070781c00341800340360090070f01d54004998052008818131074026000d0510042d4500c0d4001c441207038008481c5005d04000398641580824410300d000c0500f1221000c0b1009041145100d0000041c10050304002d00380c1542c4d080c1f0301400741d00d00c0c0041400782207882036642c1d424800c0c0d0441819182d41e140c0350441d0080c0d21040615070060080c854540d81407031b000d0010040120f0403158985450b5a8402a0500000340c42d0002e03407002c10300d8907210f90307001c0788240503042a60a800a800410 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 897462158 1250 897460908 897460933
    0x9020f13151712071e0f080c0d1b02010804020436061103160818070b090a08030c0615030c1e01090509100302040218040e07030c06020a0305070212 65
    0x688401008852240008201c8850056082001d900c0d06103c000c4000c3c400500420540704150341c1640c01d400001c4201c9040d450080c02d6800001d001074000350020a07080582c400208880d0900d4003295501e01d10304600802103620b40042900107400030f903402d0002001400d2035031100741c0000c1441c42034501c03615200010013210350450401400181c520030410201b10f00c40c0115103032140c61040702c904500d046902c0c41d80301100780c0024410004104045008030785200200c9407251081001c0e29401e13600c5003224151503000055180c021a400080003a240c3d80c040306850000c3ca160010b024a903c030402c4074040c82c4280714011340e040c0104021081d140d95000600c3d0107071280d03107143e83c000035555400503000d92030642c0b00358000d90f5102e00300868000040c00c1842525412500142c60750a1010000c0444840000c0c030f9070820315100d03548001c0200007442c00d00b07c3e482024207044840d00c4a8040362225480d01c0000c01140090180400501d011580074558414203400c846c480406407 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 897463408 1250 897462158 897462191
    0x5010f080d083414121314010e011a040218100525060b120309012a050a05160b0409020912010c111605060a050304050708030307050d0f09020f13 64
    0x81160305038144a008441e1908100c50001c1c5940340302980b4201408600c0072030609000034100800400c070305000d0f80030045503184401c0728104031f100810110300640999070003807980c61044110000301d04003148040c6002d00841e4000b28440300c500d00100c603400140242e5584d0b140d03c141c1032040c02d100c144241040c00380d8900841614442c0144060038605000d01220429032429004001c500e8140088681c000215102c1e0b500c00c1c42c10011803800481ca06c0c1c1640b1410380c9212410035901c0602c3c0910600040400025014070180d5142c940c000103071442c1e00c00c0780d01c0b401215006c20300003041610310607806082e100e4000b80111106070098600a421500084132590210b141c41c40045407109042011800460612803078161032810680020f02e24010900c6000c20040c00200107001c04c8400d000c1400280300543c21039482e402c3c105005001c6410241c10b503181246080582e503108099409001041d41d00648541c4102d480003040c05840c142072050361031240e413074108654114000303 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 897464658 1250 897463408 897463471
    0x81803030c01230109140130050f060708160e0604090e01091202071215020712080a27030f02070803041e05040b061605070b0a020307020405010f080d08 67
    0x19000c5075480d541040b00350480c03c16060f00301c420120700d0213401c03603409070444442c0c5043d40c0220341c4034803100806421258404d6050007500b085034400b040c000c01008400070700403840700100800c0e5005540ca4840858001c482115003514940c2c0b10404601400c0c0900442c400780381c2d020b0000c07031505850f04108801c1d2919040540b040c1d80d921808103050007900261981007a2091000d04141440c0058500ca014001c6c8000f8004000e07003170480ba00000103904a0700071951001200d0800d1460b108080c041d130404444c05180c42e421300c0d200c442082801d0700d103011085580303080f076980c1c5142e946048980a04000018007544600d210108402204001810050003260741c06003031110815801c035142005644468022401c1112541141da98102a104481304c00100e02a01301000d0601da0f05d807190650100111000024481c601c0a40c044010304406000741d4080c065641d03176080c8405485624411400c00d504003080b00d500062041411540041c0d60100d4181910305030040c0d58850041c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 897465908 1250 897464658 897464681
    0x203100e2b120509070f06080f0a060605031305070906080a140601080606150d020307030603120809030a0c03030b30010c02030f030606070b09060a0b0d081803030c01 73
    0x1001d102407116051000300c1c41905400422086800200355502402440070002425049500c0e500040c4031100d003005404000c00c1030010300142030360f5600001d4080d80040c0e950700044807104001460800d0140190002c545050399418910b40d608068080b203421034210031501c40c001c8200005401c0351501519015060f0003000d0305c0002c5035490290100d240c0c041090805821000042100c0440032821300d900000c151440e000c40f09086803204030a01c80c40750104d5090f8408803c2c000300ca949903000c1c10940c1e21a40400d18950000754007940d020400300c80003400fa42c4104482c3d4107039071117400900242c2e442410b002c508010141b0020300c0303800d042e111445000c185c100c2c1c2154900940c130b18010b01003014070300070008850070500007503da20900c4214108444000003088003515040200c804182e00190b01084d90b05047c0320b1030361500b0040e07907003802e068104410311a03280341009503c580e81380c1c000c1e0790920340954071855900e001e00c0c205240e60715020a200300641000c082c043da02c210403 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 897467158 1250 897465908 897465913
    0x901110f0601052b0b061302040e072705040e0115031a0f07020a031409100908250504090c17060609010f0503060403200a031d0117130203100e 63
    0x1030605090055100344035005400b44901000400c100d04015502190079139000040100103580710310100c0c47d02000e900c00c0200342440002d00142220401818500455980d036030800083c088003140400f2a81c000002181120040010010303450198032100070810918000b0035030311031a071406480c030300141e40162049011840d480382000c2c050070080da4080c0740445030190a082c0a5802581d80814110040c1400300d880c2003030098081030000d40340031100c014801c1c2070410074134000a000990f0381c803e00030944a404a090700b0074240043c034130141500345028420741450103040101524100d00140c44a221144000c6481681c50a00001d41c080721030050080d03040c81c0d01032100d0a94141c0c00403522140e506028441c2d5a004524580c2150b01490020301d1502c0c16001c503a111045684001d4003880788e2500202050703040402d10400101c14011a40f00c003040c6001900d0000410181a06070f00d50a00050000c0d0032114201c1115800601226821041c01c00d0714811680c4015201c3d41e540d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 897468408 1250 897467158 897467161
    0x2312040c0902070503180d0f1719051e031302012015040c12110111010618090c1e150216090b040e0f1c0c06020301090608070f080705060901110f06 65
    0x250540c80346d91611402950800c50381e15030303501c0e042900703042c1c0030300284168000080141101580780580e0f003500081c0315100640e02040d003000c0c0555100100034200c40ca00f81646050040d40c0c80c0a030303442146044d540035200c0d0519401140c2e1301000b10558070642201041501c2864010440d0b00c1150710070a045c102181401d092a451856080d8010b2403490301c1220b600001500410f541400740100f801c0c00441d00e07008024642c05060907400003a14690940000e40b0b203240310350045d0482c0b50046403544039141d00c03801401c440764401540c03041d60624140041101020401007021400424410b035003102c2c90480c003a14410006a211002d03580c0c550032842034501d0103100d001346501c40500140301c01601c0c0503400751182441c43c85003003039540340c03a424002e240c01070740c9080a06078010310455aa685941c81100104014061f6140910a41502060f880c6040244400b91348a01004015180c80c0c40100070041c2c1c000c400300b40c10000304407009442d041c82081207011207111600a000907 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 897469658 1250 897468408 897468427
    0xf230c0a080d0c1b020a06111e010f0605040902090112050f0a120801060807080103110d0215030708010f1a130512011a1806041d0a0f032312040c0902070503 69
    0xc00102d81c8a900e44ca9a0700100c0180d54510100701190124100440d0803401d803200c10781080000109040d54140c0c1c50203c244169041d4800001d80d521054208802e0382c4410501080b00c1c0c6246009405c5a00c0a00501403440c001e808010582d100310b049480c005941c0203450705090300d84100f2510955081141c20101d40c00800e09030140030b580c5495007203860040b100405c4010180700c00f03044200200e48159584e2111500c0002c450740103410340124044c04a014281c0350300031144078000810b090000700b228508100640c08445034031070451040c0c1d03040700310101c1c103a000c44090801003e00c041c002070240c50f0f0707040044026070581e00000d442c2c0714034600030714140d07441c10240e40b00d1a4041c0170085d0049045000c20380000007542c0008070101200d05c21146142c1d6085440414070a0b444840c040210b40c0c1d818850701c42c466540c0300682c40b8400081c1c01008110103001c40407e005011050003049804050355010303000d510300d458a40c0c2d9911051049034000d00041d5095013000441c0c144 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 897470908 1250 897469658 897469667
    0x30d08010302101b02010c0305160f0b010e040f0b1e0901150506030c0f0c0a060e0703060b09071b020112060b0a020f0d05040e040c03021009060f230c0a080d0c 70
    0x2d0b11103e09080304c501c80004c5452046001003900241031040340c40c000c0003030500c94015140801c0201d20fa0011400281c20048031182211500310358001141c800031850150001c011402141d014035900c561080580d241040000c1c001d0008142d01d6240280f81107812400c01c5c268003503002c160000458078440216500311451075003140c0c1c0508410014403400c1e580140c00c8a000114101142c1c0e2903420424559007072505401d40944214182206114503000c00b042401c1101d10681c410003480c4480710a0202c80c100c00c507180c80111712000d00c403d04403640380c00400e244134414980b221048249072014021103000360862040c003100481d048801e541c042043c500b4081c034000c010160b0360346105000b40036200d03071b02620080b100c985c000315080000c00d6041a000d580d00038105a9084803950004056845602c42c04000941c070403140c580c0d482c01041c0c074500880e08180050300711500043e40140c01d40c8420188041403282028000c08a0b0080b0060039800b03000352000f148050310f8072030050 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 897472158 1250 897470908 897470929
    0x41a011403010b010305010501050d0f0b192108070609050c10080a06120b010311060706142d2a04150e15120a0617010f1a010c060b0f030d08010302 65
    0x44c14540741c03400501960382c0010944040b209801c10208180c1c2d0080b031004081d10b010386007540c20440d030f06900600030b44503c2c00c420984200d2140240f1504409030b02c00e200300460200941071560400c2100040360840d01301c240380c98094002c9602d240b06450100c1d0744003841c07040040014910000780300031440f403030003100c1c01055a2207a81550b16151745031003039241010b200003481c0001c3c1c841030b404c0702d443d841c1c240d550142e0440802c2060811b0b00f11000903004048a040c405403207040c011754004440c01c00c5003c41e00c41059107015039541c9806840c0b80c2001c40380c444030040c540500380d504034070103000020005401900d428140300c0c3d904400140c40d0042c003180701441800d6015841003c0d20540c025100341c0000801c42c04a15210400100b000302241d820402100742ea01400803128001500204590540b00b0300401800014a01c5019541c4030310039400d00180000c40f000012648a40000c0c03100d42004101413600100b100029280c009036102c10f201045118004009600d4040c82c00c1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 897473408 1250 897472158 897472181
    0x71718090114030c061e0a02010515010c0f0f020123120a0b09070f050706060305030a1e0e0613080706020d02010510030201140a23090f04090812041a01140301 70
    0x7400c8100c50700207030301c44d00d0500745103029040206850400510101a400c00d4040c1e5140342a91208121f600038040c10341215000c0184040e2100c040595101ea01111081c035000010040b0421444d640c083c1d1084504070b099040029a14400b030158000318440000010720034038182e511071684003102240c40000303203c90506441e004c45c1da0155100d08080c0c42d032000b60303841c0060003003d507060151100d0091240c045e0056141c4800030007080f4001004001580141d2280740d5081850443e515940d012004d480000482d240f00b101010709028010f40300726078043c4c1840d0a8140c540b4a850325007011030f484940164011541c60070540e070284103413500300403070420a55405045800190010900e2408200002c00000780c40d00c06904c0340f501c6039804001d40a4601502d40c6900c40004c3e990090019079204207065400228a0320380b030311601040d2036100b8009410111402489003500c08010020f0310544007400312141400b0440200380e018040c24843c1901001942080c103003111110481c8 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 897474658 1250 897473408 897473429
    0xa090c05100804020607150c0914090106092714010617100303050904022802070b03370903020718230603030405030703080915040b030103080717180901 67
    0x600081580062282c0d4000d806845c2d00d0750b80c80c26858103150060340b02c0402c2c03503440d25001d006200c2c1a404140d0404035841c03c048448103400c003808003d5054020310801c0041692104200b01a24201c18050000000b540c1004c43d01e4040c00700744c10950b141803883c100100d100c08010310031143c111450010540702d203240314116140108200d100d008c1203010150030b004003c40e000030a6034481c1c0444010030028500e00002e039140d1405031004c00d21b4111800c4c003500a915021842041c00420343e881403440140c00046082c40c0315061160603411004007040a20160044c0248280780c0104e49101d48640e008103c036510305014201c8841891a810100341e00301100741c042d0180c402e5043c10141010200941c036a216100028618070460348215094090b26500009000144004d400c3c0100300b5600189581619042000b091080d1300038450070002c24030041c4081039008024062852080d5a55640f20079032400c2449075030001c07500c04241e100c070203240140c01d00f04070040318014205c0844 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 897475908 1250 897474658 897474679
    0x50106030c15140f09190603050a09050613020a03050f0303010603060611031903061d0405060603011512061413051209030304030201030209040605061c0b0a15030c02070803030a090c05 81
    0x10010501c001c14500300d96000c0f0041a086a0703044041c0880f000300300c000303004005040107810070101201c000d209080105e0301d4280010800e000b43e0007041c00d46903101024290700d41d84d100e4081e10302c500e00720040e40c110300c5029010000600400c9000c107003d44001c000c40d1030790f26024000f400d450664010501708190008811541c0c03d00100395003009644d00302c000103000400004500610321507102da0000c8441c81ea24104400004107440d018a01500071344405d5039950061500703849017212011002c0d01120300800c1812040f00c610b00b002486520b000c074041c070382e651105903840419959507c1c00300710440301401b08007040041e84030344150008003c0c1040a036400091b228051484040c0c18117400084e114000e560f5035200703a014000091080707403940004581c066088864594402c0501d142c80d00c181c4044ca001029902151480645142c492403041c07402c502030504150040d05602c038504011444103001d0010b18030400e814840050f5030300540c1800f01e4082ea03d0f912081c028200381c203 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 897477158 1250 897475908 897475949
    0x10905060406050924060d08040609030314040b030606030c0f120f1b041701141e010b04050a030602161202031c0515012102041e0905070c120e030a050106030c 70
    0x11095685c0d11449400380085a8441020400581c50310780014259840050003141c0d43d0380000b40c4800380d901035501e080c102c035a1180d132106944280d0040400c81c0360244000380d0680f81801c000d41e800320949141c2810701c804540444466008250a5102011740034100031608940d542c0d440e1b030098074643c0c1241900e000101608032071180340520f000d01d184140707541200480035013102d002c0b1421604441030524040705130000c1c000350000100205c1e07030070b2000003030301c402c0500c191400c1d03941c018041c4141600c0c50b92080002d5000520315102b400440103074030042800c04030444c090382616000b465032106044142c0b010007058145032041503250100b07000844802e00d800a44d586402c0c240002444401800000e854460f69182c040c15400080d0200d5030356020100500c0b00702109118800355500c4201940990300201e88802c002101e105002c80440d58400300f05040c03541600704601881d606a001c2800c3c492072034015261a07449a03810401c100315541220010425844520f182c4400178 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 897478408 1250 897477158 897477193
    0x7231b1615020a1a0a110a0e0f180f04051c02070e04020301062d05010509090415021c0b1201050f01030b040503040506041205060a151707080109050604060509 70
    0x1405080022121000410007a50003040030040b115005440058003411544121080e004115500e411039400c0009189038014040309480580c6103c1e03ca00d09684804020b00c045000da0103d403613400714007001c1200b03d45040d1a8418092110002c5214003841c00741441442c210903081840030584401480a44080d4045a69820340301a803580103580d0f220b0b030000074003401d219000794543d03054142220360844480740c00311265035564052544140d07950401585d0600030382c0000380d040540c00b0005000111044045092446100c20050406580700c0400004603c030b03814107a4138aa586500881d03500c0e2489070110408032940090246180071500e040b0003c0040c1300003082c440302d900100b020000140241c601402c000360881c0d40383d655440a07188070b6140d000c0103480354010030700411413400b094092030410038502c14550103032a140a802d604598015207200c200c42c020b803a00800d00b00403e000d10300030780b0300540060256003400d0606108440c0043c01036540c2e9445417521f9502e038001c2 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 897479658 1250 897478408 897478453
    0x6030108070b090d060c020601140d030e1003060b031e0a020f0906070503041e0302040c0f0e0f0607020301050a1b05070b0a0509010e0609010e0c03060105030c060307231b 75
    0x80900989682c0401d01080e0b5820444500401d10307400c001800d106d15038005119070480702c4030034109600600d0342c0c0034020120b105010140c0080c0014050840c641004240d400d402e00300b41c0780001c0c090765501444c81654100742da9000c9404140c2c6c01d40c1106c41c6d85075804075085103840c401103181a1a00c640b0610394480d0349180307400340d100400e0101c1400418000c0e10000c0441303040d400c54203203c0d40800c0340c0b00c6c525804128401c5103480f01034080240314401d8400003a2a544800360041110010048800200040254040300c100051b900684007801160f019030110030011030715601307410b000825903c5455000303003003040031b1111001051141e1505a0480b003d104001a10b80b10f49003020301410f40000308840d03030b20507a010300c00203807015070007840503440031001d403002d4919100400d03840760005e101d0107034507512a41241ca002e144c03400c01550489124101a96841050a150900d0700d9150f0300c9000142004662508040c02c0e5540c8010024a90f101410550800c24481d1a000705ca = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 897480908 1250 897479658 897479669
    0x180703120207090e1b0120070504050c0a0f1103070c080d0e030a1101080a0e0604030f0f0e0d02150c19021305040201080a0519140a0c0f0207170a14030304020f0603010807 75
    0x241d502810380d00072400d047c180c100385502c0c003010980e001d0b0142e80d541000c5c070495014510346000600c04495800a07541d414005a440312044ca404c11022525014811f130400c2060008012410000c1c021425080040110f9005010030000e07a0001410000742e0b154000d01a41040c018100050001c441130780e001c40090a204602c0e4031011242d400030007140d641690b0603c01d02c0c0c00d00c014160044044c0039008059031341e1180d00300d5565011100e040362491020381200c2d80e0b03047c56006140a104c0c1c614940c81004580341444d44544013140381c4542e9102c00c2801400401b0420b0550600603003418050266001c1030200c0c1c1060f500003405171a000b4020145250b54401040702c01f00100c001e10400c404541e028000301b807407078980c512200341c140c0740320380001c2c50300704003200741401303500ca40f5401c0400350050102c051a00300c0014546043d600552030030b018920b90340d800941600d0b0551280380b0340f07a0003541c581c58a881407020402d881e0411520806040c07004102201002405500f504d0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 897482014 1106 897480908 897480943
    0xf080702040b150412050f07030b0907080607120c02010b130609050105030d0c1209120f0308180c060703021501120b0c071a180703120207090e 63
    0x1058189a080f0b140300c140000c0107070f0301d13001c4505003410b030290050711214101f5004450402031240c00407241d40c903500c03081c4114000100a02000f9010690090040e418a000d000e0700610304546940c1503141c5840d4165030030ba100707400c04200000050041d00d413034402540b031000944041c1c001e00d80300c289003000014552400095143c0c040c0d509486d000d009205036220244414814a003840078450025400a0350000f0080c6620f8180e001d40c5115445140a18004100010181c030381c0944d03807a0756100191204000c109010f00c032004407644c5039603400e140f03000d034140b215001c000c4109195800000843c0c109603084000030314410722050009655812212081c3d0180c2000908004c80440743c1c92a41d050f004160b0740c101001b03640350b013010304500440d1803a00c04217800c02c40d850381c0020b001c01c2c240c98040000c00098120180c0502418104078031060b503550030000603c46c542d = true := by decide +kernel

theorem cover : BRFrame.Cov 897302158 897482014 := by
  have h0 := BRFrame.cov_init 897302158
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 897302158 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 897302158 ≤ n) (h2 : n < 897482014) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
